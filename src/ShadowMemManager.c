/*
****************************  Shadow Memory Manager ****************************
*
* The entire user-virtual space is virtually divided into slots of fixed size.
*
* A given slot could be in one of the five possible states:
* Application slot (A): these enclose at least one user mapped space (including
* stack and heap).
* Shadow slot (S): these contain the shadow map.
* Empty slot (E): these slots are not mapped by the process in question.
* Reserved slot (R): these slots are mmaped with no access protection.
* Blocked slot (B): these slots are mmaped with no acess protection to prevent
* application from using it.
*
* Shadow corresponding to an application address is given bythe following formula:
 	shadowAddr = (appAddr << shadowMemscale) + offset.
*
* Implementation inspired from EMS-64:
* http://groups.csail.mit.edu/commit/papers/2010/zhao-ismm10-ems64.pdf
*
* However, this implementation is different in that it has a customizable way
* of letting programmer decide whether page faults are to be handled or not
* to make sure that the shadow memory access has the least impact on performance
* as possible.
*
*/

#ifndef _GNU_SOURCE
	#define _GNU_SOURCE
#endif
#include <stdio.h>
#include <stdint.h>
#include <stdarg.h>
#include <stdlib.h>
#include <inttypes.h>
#include <math.h>
#include <string.h>
#include <sys/mman.h>
#include <sys/time.h>
#include <sys/resource.h>
#include <errno.h>
#include <unistd.h>
#include <sys/stat.h>
#include <fcntl.h>
#include <ctype.h>
#include <stdbool.h>
#include <inttypes.h>
#include <sys/types.h>
#include <sys/stat.h>
#include <fcntl.h>
#include <dlfcn.h>
#include <malloc.h>
#include <signal.h>
#include <setjmp.h>
#include "ShadowMemManager.h"
#include "Stringlib.h"
#include "HeapGuard.h"

#define DEBUG

#define DONT_THROW_EXECEPTION_ON_ERROR

/* There is a possiblity that the entire application using the shadow memory
 * library might be compiled as a shared library. So, we use a macro that can
 * be set or unset during compile time. By default, it is set.
 */
#ifndef COMPILED_AS_SHARED_OBJ
	#define COMPILED_AS_SHARED_OBJ
#endif

/* Block the heap by default */
#ifndef BLOCK_HEAP
	#define BLOCK_HEAP
#endif

/* Slot shift and shadow scale need to be obtained from command line */
#ifndef SLOT_SHIFT
	#define SLOT_SHIFT 32   /* 4 Gb is the default slot size */
#endif

#define SLOT_SIZE ((uint64_t)1 << (SLOT_SHIFT))

#ifndef SHADOW_SCALE
	#define SHADOW_SCALE 2 /* 1:4 mapping is set by default */
#endif

#define ASSERT(condition, errorMessage) 	__Assert(condition, errorMessage)
#define WARN(condition, errorMessage) 		__Warn(condition, errorMessage)
#define EXCEPTION(errorMessage) 			__Assert(false, errorMessage)
#define SAFE_STRSTR(haystack, needle)		__Safe_Strstr(haystack, needle)
#define SAFE_STRTOULL_BASE16(string, addr)	__Safe_Strtoull_Base16(string, addr)
#define SHADOW_MEMSET_ZERO(addr, numBytes)	__Safe_Memset_Zero(addr, numBytes)
#define SHADOW_MEMCPY(dest, src, numBytes)	__Safe_Memcpy(dest, src, numBytes)
#define DEBUG_PRINTF						__Debug_Printf
#define SAFE_SPRINTF						__Safe_Sprintf

/**** Pointers to the data structures comprised by the shadow memory library scratch space ****/
/* System, Scratch space, Heap and Stack Information */
static struct sysPageInfo *sysPageInfoPtr;
static struct scratchSpaceInfo *scratchSpaceInfoPtr;
static struct stack *stackInfoPtr;
static struct heap *heapInfoPtr;
static struct objInfo *objInfoPtr;

/* Pointer to memLayout table */
static struct unitInfo *memLayoutTablePtr;

/* Pointers to the appShadowInfo list */
static struct appShadowAddrsNode *app_shadowListPtr;
static struct appShadowAddrsNode *freeAppShadowListPtr;

/* Pointers to validOffsetsList */
static struct validOffset_struct *validOffsetsListPtr;
static struct validOffset_struct *freeValidOffsetsListPtr;

/* Pointers to invalidOffsets tables */
static struct invalidOffset_struct *posInvalidOffsetsTablePtr;
static struct invalidOffset_struct *negInvalidOffsetsTablePtr;

/* Pointers to the list that stores addresses of slots that need to be temporarily blocked */
//struct blockSlotAddrNode *blockSlotsListPtr;
//struct blockSlotAddrNode *free_blockSlotsListPtr;

/* Pointer to the app_mapping_info struct that can help deal with recursive mappings if needed */
static struct appMappingInfo *appMappingInfoPtr;

/*** Not the part of the scratch space ***/
/* Pointers to brk and sbrk buffers */
static uint64_t main_bufferPtr;
static uint64_t cur_bufferPtr;

/******** Varaibles to track the state of function calls in the library *********/
/* Tracks the states of initialization of shadow manager.
 * It has 3 states: SHADOW_INITIALIZED, SHADOW_INITIALIZING, SHADOW_UNINITIALIZED.
 */
static int8_t shadowManagerState = (int8_t)SHADOW_UNINITIALIZED;

/* We cache the previously used offsets. The first offset cached may be changed heuristic during
 * the page fault and the second offset is never changed. If it for access of shadow without saving
 * the context of program execution. The second one is typically for globals and heap if it is not
 * blocked.
 */
static int64_t shadowOffsets[2];

/* We would need to store the state of the context of the program when handling SIGVTALRM */
static sigjmp_buf alarm_context;

/* We keep track of whether the timer is on since we are implementing a recurive algorithm */
static bool timer_is_on = false;

/***** Pointers to commonly used functions *****/
/* The common pointers to the functions that are likely to be used often and the real
 * functions are wrapped and these global function pointers are pointers to real implementations.
 * Functions like calloc and free are specially handled since dlsym uses them. These can be used by
 * the tools running on the top of this library if it does not want to map shadow for some mapping.
 */
static int (*Sysbrk)(void *);
static void *(*Syssbrk)(intptr_t);
static void *(*Sysmalloc)(size_t);
static void *(*Syscalloc)(size_t, size_t);
static void *(*Sysrealloc)(void *, size_t);
static void (*Sysfree)(void *);
static void *(*Sysmmap)(void *, size_t, int, int, int, off_t);
static int (*Sysmunmap)(void *, size_t);
static int (*Sysmprotect)(void *, size_t, int);
static int (*Sysmadvise)(void *, size_t, int);
static int (*Sysmincore)(void *, size_t, unsigned char *);
static int (*Sysmlock)(const void *, size_t);
static int (*Sysmunlock)(const void *, size_t);
static int (*Sysmsync)(void *, size_t, int);
static int (*Sysgetrlimit)(int, struct rlimit *);
static int (*Syssetrlimit)(int, const struct rlimit *);
static int (*Sysprlimit)(pid_t, int, const struct rlimit *, struct rlimit *);

/* These structs are declared in 'malloc-internal.h'. We slightly modify the
 * definition as it was intended in glibc i.e. to use 8 byte members in the
 * struct. As for some size changes, they are accounted for by the pads.
 */
struct chunk_info {
	uint64_t mchunk_prev_size;  /* Size of previous chunk (if free).  */
	uint64_t mchunk_size;       /* Size in bytes, including overhead. */
	struct chunk_info* fd;      /* double links -- used only if free. */
	struct chunk_info* bk;

/* Only used for large blocks: pointer to next larger size.  */
	struct chunk_info* fd_nextsize; /* double links -- used only if free. */
	struct chunk_info* bk_nextsize;
};

/* This records the heap information at the top of every malloc arena mappings */
struct heap_info {
	struct arena_info *arena_ptr;
	struct heap_info *prev_heap;
	uint64_t size;
	uint64_t mprotect_size; /* Size in bytes that has been mprotected PROT_READ|PROT_WRITE.  */
};

/* Some modified definitions for macros as in glibc's 'malloc.c'. These indicate
 * if a given region is mmaped, used previouly and/or uses non-main arena.
 */
#define PREV_INUSE	   		(uint64_t)1 << 0 /* decimal value 1 */
#define IS_MMAPPED 				(uint64_t)1 << 1 /* decimal value 2 */
#define NON_MAIN_ARENA  	(uint64_t)1 << 2 /* decimal value 4 */

/* We keep track of the newly heap using malloc or calloc */
static uint64_t mmapped_heap_addr;
static uint64_t mmapped_heap_size;

/* We have to make sure if we want to handle page faults. If we are not
 * handling page faults, we are bound to use one shadow offset only.
 */
#ifdef COMPILED_AS_SHARED_OBJ
	#ifdef BLOCK_HEAP
		#undef HANDLE_PAGEFAULTS
	#else
		#define HANDLE_PAGEFAULTS
	#endif
#else
	#define HANDLE_PAGEFAULTS
#endif

#ifdef HANDLE_PAGEFAULTS
/* Keep track of shadow access context buffer and page faults */
static sigjmp_buf pageFault_context;
static bool handle_page_fault;

#define COUNT_SHADOW_PAGEFAULTS
#endif

#ifdef COUNT_SHADOW_PAGEFAULTS
/* Keep track of number of page faults to switch shadow offsets */
static uint64_t numPageFaults;
#endif

#ifdef HANDLE_PAGEFAULTS
/* Pointer to the list of page fault handlers used by tools using shadow memory */
static void(**pageFaultHandlersArrayPtr)(int, sigjmp_buf **);
#endif

#ifndef USE_GNU_MALLOC
/* This is used to map heap bags and heap blocks and use this shadow library
 * when heap bags are mapped and shadow needs to be mapped as well.
 */
static void *MapHeapBlock_and_Shadow(void *, size_t, int, int, int, off_t);
#endif


/********************* SHADOW MEMORY MANAGER CONSTRUCTOR **********************/

void Init_ShadowMapManager(void)
{
#ifdef DEBUG
	DEBUG_PRINTF("INIT SHADOW MAP MANAGER\n");
	Get_ShadowMemManager_State();
#endif

/* First, make sure that the constructor is called only once */
	if(shadowManagerState == (int8_t)SHADOW_INITIALIZED)
		return;

	DEBUG_PRINTF("INTIALIZING SHAODW MANAGER\n");
	shadowManagerState = (int8_t)SHADOW_INITIALIZING;
	Get_ShadowMemManager_State();
	int saved_errno = errno;

/* We keep track of the common pointers to the functions that are likely to be
 * used often and the real functions are wrapped and these global function pointers
 * are pointers to real implementations. We look them up in the symbol table now so
 * we do not have to do this again so this practice helps improving performance. Now,
 * since the dlsym calls that we are going to make are limited to just a few and the
 * worst case scenario that is highly unlikely is that a static structure of 32 bytes
 * will be calloced by the dlsym standard implementation. Since we have already
 * allocated some space statically in the data segment that is bound to be at least
 * 4kb, we shouldn't run out of buffer space.
 */
	Sysbrk = (int (*)(void *))dlsym(RTLD_NEXT, "brk");
	Syssbrk = (void *(*)(intptr_t))dlsym(RTLD_NEXT, "sbrk");
	Sysmalloc = (void *(*)(size_t))dlsym(RTLD_NEXT, "malloc");
	Syscalloc = (void *(*)(size_t, size_t))dlsym(RTLD_NEXT, "calloc");
	Sysrealloc = (void *(*)(void *, size_t))dlsym(RTLD_NEXT, "realloc");
	Sysfree = (void (*)(void *))dlsym(RTLD_NEXT, "free");
	Sysmmap = (void *(*)(void *, size_t, int, int, int, off_t))dlsym(RTLD_NEXT, "mmap");
	Sysmunmap = (int (*)(void *, size_t))dlsym(RTLD_NEXT, "munmap");
	Sysmprotect = (int (*)(void *, size_t, int)) dlsym(RTLD_NEXT, "mprotect");
	Sysmadvise = (int (*)(void *, size_t, int)) dlsym(RTLD_NEXT, "madvise");
	Sysmincore = (int (*)(void *, size_t, unsigned char *)) dlsym(RTLD_NEXT, "mincore");
	Sysmlock = (int (*)(const void *, size_t))dlsym(RTLD_NEXT, "mlock");
	Sysmunlock = (int (*)(const void *, size_t))dlsym(RTLD_NEXT, "munlock");
	Sysmsync = (int (*)(void *, size_t, int)) dlsym(RTLD_NEXT, "msync");
	Syssetrlimit = (int (*)(int, const struct rlimit *))dlsym(RTLD_NEXT, "setrlimit");
	Sysgetrlimit = (int (*)(int, struct rlimit *))dlsym(RTLD_NEXT, "getrlimit");
	Sysprlimit = (int (*)(pid_t, int, const struct rlimit *, struct rlimit *))dlsym(RTLD_NEXT, "prlimit");

/* Block the heap if necessary so the system heap cannot be used by heap allocators or the
 * application itself.
 */
#ifdef BLOCK_HEAP
	DEBUG_PRINTF("blocking heap\n");
	BlockHeap();
#endif

/* Map the scratch space for the shadow manager. Cannot use DEBUG_PRINTF and print any
 * infromation before mapping the scratch space.
 */
	MapScratchSpace();
	StoreSysPageInfo();
	InitMemLayoutTable();

#ifdef DEBUG
	//PrintProcLayout();
#endif

/* Open the /proc/<pid>/maps file. If we fail to do so due to some reason,
 * we end the process immediately.
 */
	char procInfoFile[1024] = {0};
	SAFE_SPRINTF(procInfoFile, 1024, "/proc/%d/maps", getpid());
	int procFile_fd = open(procInfoFile, O_RDONLY);
	ASSERT(procFile_fd != -1, "Error: Could not open proc maps file.\n");

#ifndef BLOCK_HEAP
	bool heapDetected_at_procStart = false;
#endif

/* We are going to have a state variable for detecting different segments of an object file */
	int8_t objSegState = (int8_t)EXEC_NOT_FOUND;

/* Heap has to be skipped when the table buffer is to be filled as we
 * interate through the proc file.
 */
	uint64_t progBreak = (uint64_t)Syssbrk(0);

/* Read the file and analyse the process memory layout */
	struct tableEntry_struct *cur_tablePtr = scratchSpaceInfoPtr->tablePtr;
	uint64_t prevEndAddr = 0;
	char buffer[1024] = {0};
	char readChar;
	uint64_t lineNum = 0;
	char *bufPtr = buffer;
	while(read(procFile_fd, (void *)&readChar, 1) > 0) {
		if(readChar == '\n') {
			*bufPtr = '\0';
			char *restBuf;

		/* Read the start addresses to convert the strings into hexadecimals as in proc file */
			char *invalidCharPtr;
			uint64_t startAddr = SAFE_STRTOULL_BASE16(buffer, &invalidCharPtr);
			ASSERT(startAddr != (uint64_t)-1 && invalidCharPtr,
					"Error in reading proc file. Possibly file is corrupt.\n");

		/* At this point, *invalidCharPtr == '-'. So we increment the pointer
		 * before reading the end address.
		 */
			uint64_t endAddr = SAFE_STRTOULL_BASE16(++invalidCharPtr, &invalidCharPtr);
			ASSERT(endAddr != (uint64_t)-1 && invalidCharPtr,
							"Error in reading proc file. Possibly file is corrupt.");

		/* Check if line being read has '/' since any executable is in a
		 * directory under the root and is most likely the first mapping to be found.
		 */
			if(objSegState != (int8_t)OBJ_FILE_SEG_ANALYSED && SAFE_STRSTR(invalidCharPtr, "/")) {
				if(objSegState == (int8_t)EXEC_NOT_FOUND) {
					objSegState = (int8_t)EXEC_FOUND;

				/* Now, we save the information about the executable */
					objInfoPtr->execBegAddr = startAddr;
					objInfoPtr->execSize = endAddr - startAddr;
					prevEndAddr = endAddr;
					bufPtr = buffer;
					continue;
				}
				if(objSegState == (int8_t)EXEC_FOUND) {
					objSegState = (int8_t)DATA_SEGMENT_FOUND;

				/* Now, we save the information about the data segment */
					objInfoPtr->dataSegBegAddr = startAddr;
					objInfoPtr->dataSegSize = endAddr - startAddr;
					prevEndAddr = endAddr;
					bufPtr = buffer;
					continue;
				}
				if(objSegState == (int8_t)DATA_SEGMENT_FOUND) {
					objSegState = (int8_t)OBJ_FILE_SEG_ANALYSED;

				/* Now, we save the information about thhe BSS segment */
					objInfoPtr->bssSegBegAddr = startAddr;
					objInfoPtr->bssSegSize = endAddr - startAddr;
					prevEndAddr = endAddr;
					bufPtr = buffer;
					continue;
				}
			}

		/* Look for the stack */
			if (SAFE_STRSTR(buffer, "stack")) {
			/* Get the limits of the stack. If we fal to do so, its a fatal error */
				struct rlimit stackLimitsInfo;
				ASSERT(Sysgetrlimit(RLIMIT_STACK, &stackLimitsInfo) != -1, "Error in getting stack limits.");

			/* If the soft limit happens to be 'unlimited', we explicitly set it.
			 * We have already got the hard limit from the function above and since
			 * we can't change it, we leave it unchanged.
			 */
				if(stackLimitsInfo.rlim_cur == RLIM_INFINITY) {
				/* Setting the stack soft limit explicitly to 8Mb */
					stackLimitsInfo.rlim_cur = (uint64_t)1 << 23;
					ASSERT(Syssetrlimit(RLIMIT_STACK, &stackLimitsInfo) != -1,
											"Failed to set a finite limit to stack growth.");
				} else {
					stackLimitsInfo.rlim_cur = (uint64_t)1 << 30;
					ASSERT(Syssetrlimit(RLIMIT_STACK, &stackLimitsInfo) != -1,
											"Failed to set a finite limit to stack growth.");
					stackInfoPtr->finite_stackSoftLimitSet = true;
				}
				stackInfoPtr->stackSoftLimit = (uint64_t)stackLimitsInfo.rlim_cur;
				stackInfoPtr->stackHardLimit = (uint64_t)stackLimitsInfo.rlim_max;
				stackInfoPtr->stackBase = endAddr;		 /* The stack base is the bottom of the stack */
				prevEndAddr = endAddr;
				bufPtr = buffer;
				continue;
			}

		/* Look for the heap */
			if (SAFE_STRSTR(buffer, "heap")) {
				heapInfoPtr->heapBase = startAddr; /* Heap base is the beginning address of the heap */
		#ifndef BLOCK_HEAP
				Get_Heap_Limits(); /* Get the limits for heap */
				heapDetected_at_procStart = true;
		#endif
				prevEndAddr = endAddr;
				bufPtr = buffer;
				continue;
			}
			if (SAFE_STRSTR(buffer, "vsyscall"))
				break;

		/* Skip the page that must have been mapped to block the heap */
			if(startAddr == progBreak) {
				prevEndAddr = endAddr;
				bufPtr = buffer;
				continue;
			}

		/* Store the start and end addresses in the scratch buffer table so
		 * these regions can be shadowed and could be used later, especially
		 * if the application has been mmaped as a shared library.
		 */
			cur_tablePtr->entry1 = startAddr;
			cur_tablePtr->entry2 = endAddr;
			cur_tablePtr++;

			prevEndAddr = endAddr;
			bufPtr = buffer;
			continue;
		}
		*bufPtr = readChar;
		bufPtr++;
	}
	ASSERT(!close(procFile_fd), "Error: Failed to close proc maps file,\n");

/* There is a possibility that heap might not be present in the beginning of a process */
#ifndef BLOCK_HEAP
	if(!heapDetected_at_procStart) {
		heapInfoPtr->heapBase = (uint64_t) Syssbrk(0);
		Get_Heap_Limits(); 		/* Get the limits for heap */
	}
#endif

/* Initialize the scratch space based on the information found  */
	InitScratchSpaceInfo();

/* Map shadow and reserved units for the stack */
#ifndef DO_NOT_SHADOW_STACK
	//DEBUG_PRINTF("SHADOWING STACK\n");
	Init_Stack_Mappings();
	//DEBUG_PRINTF("STACK SHADOWED\n");
#endif

/* Malloc alignement is 16 bytes. All the above heap and chunk structs are meant to be malloc
 * alignment so we adjust the pads for each of them. We asssume that whenever these structs
 * are allocated, they are malloc aligned but their end addresses depend on their sizes so
 * these paddings follow their corrsponding structs.
 */
	heapInfoPtr->alloc_chunkInfo_size = 16; /* 2 * sizeof(uint64_t) == 16 bytes */

/* We do not need to shadow the executable if the entire application is compiled a shared
 * library along with this shadow memory library and executable is not significant
 */
#ifndef COMPILED_AS_SHARED_OBJ
/* Map shadow and reserved units for the segments of the executable */
	Init_ObjSegs_Mappings();
#endif

/* Now this new offset used for the object file segment needs to be saved as the second offset */
	shadowOffsets[1] = shadowOffsets[0];

/* Map shadow and reserved units for the heap */
#ifndef BLOCK_HEAP
	Init_Heap_Mappings();
#endif

/* It is possible that the application is actually compiled as a shared library,
 * it would be difficult to know what shared library is loaded by the loader
 * invoked by the linker, without external support from the programmers. The
 * rest of the shared libraries are mmaped dynamically and we don't keep track
 * of them. It does not hurt to do this even though it seems unecessary because
 * the shared libraries are mmaped, and like most other mappings without any
 * specified mappings, would probably use the same shadow and offset. So it some
 * mappings may end up being "pre-shadowed".
 */
	Init_Mapped_Libraries();

/* Empty the scratch table buffer */
	SHADOW_MEMSET_ZERO((void *)scratchSpaceInfoPtr->tablePtr,
									scratchSpaceInfoPtr->tableBufferSize);

#ifndef USE_GNU_MALLOC
	//DEBUG_PRINTF("INITIALIZING DEBUG PRINTF\n");
/* Now, we set the function for mapping heap bags */
	Redefine_Heap_Mmap(MapHeapBlock_and_Shadow);
	Redefine_Heap_Shadow_Mmap(Sysmmap);
	Redefine_Heap_Munmap(Sysmunmap);
	Redefine_Heap_Shadow_Munmap(Sysmunmap);
	Redefine_Heap_Mprotect(Sysmprotect);
	Redefine_Heap_Shadow_Mprotect(Sysmprotect);

/* We can initialize HeapGuard now to get the heap bags ready */
	Init_HeapGuard();
	//DEBUG_PRINTF("HEAP GUARD INITIALIZED\n");
#endif

/* Register the signal to let the shadow memory manager handle page faults
 * with the kernel. This is only necessary if the application and the shadow
 * library are mapped as shared objects.
 */
#ifdef HANDLE_PAGEFAULTS
	struct sigaction signal_act;
	signal_act.sa_handler = Handle_PageFault;
	ASSERT(!sigemptyset(&signal_act.sa_mask), "Failed to set the page fault handler.\n");
	signal_act.sa_flags = 0;
	ASSERT(!sigaction (SIGSEGV, &signal_act, NULL), "Failed to set the page fault handler.\n");
#endif

	errno = saved_errno; /* Restore the value of errno to maintain transparency */
	shadowManagerState = (int8_t)SHADOW_INITIALIZED;
	Get_ShadowMemManager_State();

	DEBUG_PRINTF("SHADOW INITIALIZED\n");
	//PrintProcLayout();
#ifdef DEBUG
	//DEBUG_PRINTF("SHADOW INITIALIZED\n");
#endif
}

#ifndef BLOCK_HEAP
void Get_Heap_Limits(void)
{
/* Get the heap limits. If we fail, its a fatal error */
	struct rlimit heapLimitsInfo;
	ASSERT(Sysgetrlimit(RLIMIT_DATA, &heapLimitsInfo) != -1, "Failed to find heap limits.\n");

/* If the heap soft limit is 'unlimited', we save the soft limit as 500Mb.
 * Else we save it real soft limit.
 */
	if(heapLimitsInfo.rlim_cur != (uint64_t)RLIM_INFINITY)
		heapInfoPtr->heapSoftLimit = heapLimitsInfo.rlim_cur;
	else
		heapInfoPtr->heapSoftLimit = (uint64_t)1 << 29;
	heapInfoPtr->heapHardLimit = heapLimitsInfo.rlim_max;
}
#endif

#ifndef COMPILED_AS_SHARED_OBJ
/* This function will be optimized by the compiler */
void Init_ObjSegs_Mappings(void)
{
/* Here we shadow the segments separately */
#ifndef DO_NOT_SHADOW_EXEC
	Init_Exec_Mappings();
#endif

#ifndef DO_NOT_SHADOW_DATA_SEG
	Init_Data_Seg_Mappings();
#endif

#ifndef DO_NOT_SHADOW_DATA_SEG
	Init_BSS_Seg_Mappings();
#endif
}

#ifndef DO_NOT_SHADOW_EXEC
void Init_Exec_Mappings(void)
{
/* Map the shadows and reserved units for the executable */
	struct regSlotsInfo execSlotsInfo;
	Get_RegSlotsInfo(objInfoPtr->execBegAddr, objInfoPtr->execSize, &execSlotsInfo);
	MapAppRegion(execSlotsInfo.regSlotsBegAddr, execSlotsInfo.numRegSlots);
}
#endif

#ifndef DO_NOT_SHADOW_DATA_SEG
void Init_Data_Seg_Mappings(void)
{
/* Map the shadows and reserved units for the data segment*/
	struct regSlotsInfo dataSegSlotsInfo;
	Get_RegSlotsInfo(objInfoPtr->dataSegBegAddr, objInfoPtr->dataSegSize, &dataSegSlotsInfo);
	MapAppRegion(dataSegSlotsInfo.regSlotsBegAddr, dataSegSlotsInfo.numRegSlots);
}
#endif

#ifndef DO_NOT_SHADOW_BSS_SEG
void Init_BSS_Seg_Mappings(void)
{
/* Map the shadows and reserved units for the BSS segment*/
	struct regSlotsInfo bssSegSlotsInfo;
	Get_RegSlotsInfo(objInfoPtr->bssSegBegAddr, objInfoPtr->bssSegSize, &bssSegSlotsInfo);
	MapAppRegion(bssSegSlotsInfo.regSlotsBegAddr, bssSegSlotsInfo.numRegSlots);
}
#endif

void Fill_Gaps_in_ObjectFile_SegmentSlots(void)
{
	struct regSlotsInfo segSlotsInfo;

/* Fill the slots enclosing the executable */
	Get_RegSlotsInfo(objInfoPtr->execBegAddr, objInfoPtr->execSize, &segSlotsInfo);
	Fill_EmptySpaces_in_Slots(segSlotsInfo.regSlotsBegAddr, segSlotsInfo.numRegSlots);

/* Fill the slots enclosing the data segment */
	Get_RegSlotsInfo(objInfoPtr->dataSegBegAddr, objInfoPtr->dataSegSize, &segSlotsInfo);
	Fill_EmptySpaces_in_Slots(segSlotsInfo.regSlotsBegAddr, segSlotsInfo.numRegSlots);

/* Fill the slots enclosing the BSS segment */
	Get_RegSlotsInfo(objInfoPtr->bssSegBegAddr, objInfoPtr->bssSegSize, &segSlotsInfo);
	Fill_EmptySpaces_in_Slots(segSlotsInfo.regSlotsBegAddr, segSlotsInfo.numRegSlots);
}
#endif

#ifndef DO_NOT_SHADOW_STACK
void Init_Stack_Mappings(void)
{
/* Map the shadow units and reserved units for the stack */
	struct regSlotsInfo stackSlotsInfo;
	Get_RegSlotsInfo(stackInfoPtr->stackBase - stackInfoPtr->stackSoftLimit,
								stackInfoPtr->stackSoftLimit, &stackSlotsInfo);
	MapAppRegion(stackSlotsInfo.regSlotsBegAddr, stackSlotsInfo.numRegSlots);
}
#endif

#ifndef BLOCK_HEAP
void Init_Heap_Mappings(void)
{
/* Map the shadows and reserved units for the heap */
	struct regSlotsInfo heapSlotsInfo;
	Get_RegSlotsInfo(heapInfoPtr->heapBase, heapInfoPtr->heapSoftLimit, &heapSlotsInfo);
	MapAppRegion(heapSlotsInfo.regSlotsBegAddr, heapSlotsInfo.numRegSlots);
}
#endif

void Init_Mapped_Libraries(void)
{
/* Map all the library mappings in the table buffer in scratch space */
	struct tableEntry_struct *cur_tablePtr = scratchSpaceInfoPtr->tablePtr;
	while(cur_tablePtr->entry1 && cur_tablePtr->entry2) {
		struct regSlotsInfo libSlotsInfo;
		Get_RegSlotsInfo(cur_tablePtr->entry1,
				cur_tablePtr->entry2 - cur_tablePtr->entry1, &libSlotsInfo);
		MapAppRegion(libSlotsInfo.regSlotsBegAddr, libSlotsInfo.numRegSlots);
		cur_tablePtr++;
	}
}

#ifdef BLOCK_HEAP
void BlockHeap(void)
{
/* Map page at program break to block the heap */
	uint64_t curProgBreak = (uint64_t)Syssbrk(0);
	//DEBUG_PRINTF("current program break: %p\n", curProgBreak);
	uint64_t pageSize = (uint64_t)sysconf(_SC_PAGESIZE);
	uint64_t mmapPtr = (uint64_t)Sysmmap((void *)curProgBreak, pageSize, PROT_NONE,
									MAP_SHARED | MAP_ANONYMOUS | MAP_NORESERVE, 0, 0);
	//DEBUG_PRINTF("mmapPtr for blocking heap: %p\n", mmapPtr);
	//PrintProcLayout();
/* If the page could not be mapped, it is likely that the page is mapped.
 * So we just have to make sure that the application does not actually touch the page.
 *
 * Now, we just need to check if the page was mapped and if the page was aligned
 * to the program break. If not, we quit.
 */
	ASSERT(mmapPtr != (uint64_t)MAP_FAILED && mmapPtr == curProgBreak,
										"Error, could not block heap.\n");
}
#endif

void MapScratchSpace(void)
{
/* Sizes of different tool data structures to alloacte enough scratch space */
	uint64_t totalNumSlots = (uint64_t)1 << (47 - (uint64_t)SLOT_SHIFT);
	uint64_t memLayoutTableSize = totalNumSlots * sizeof(struct unitInfo);
	uint64_t infoListSize = totalNumSlots * sizeof(struct appShadowAddrsNode);
	uint64_t validOffsetsListSize = (totalNumSlots << 1) * sizeof(struct validOffset_struct);
	uint64_t infoStructsSize =
			sizeof(struct stack) + sizeof(struct heap) + sizeof(struct appMappingInfo)
			+ sizeof(struct sysPageInfo) + sizeof(struct scratchSpaceInfo) + sizeof(struct objInfo);
	uint64_t printfBufferSize = (uint64_t)1 << 12;
	uint64_t mallocBufferSize = (uint64_t)1 << 22;
	uint64_t tableBufferSize = (uint64_t)1 << 22;

#ifdef HANDLE_PAGEFAULTS
	uint64_t pageFaultHandlerListSize = (uint64_t)1 << 12;
#endif
	//uint64_t blockSlotsListSize = sizeof(struct blockSlotAddrNode) * totalNumSlots;

/* The invalidOffsets table consists of units equal to the number of slots
 * the user virtual space is divided into and those units constitute number
 * of sub-units equal to the number of shadow slots corresponding to each app slot.
 */
	uint64_t invalidOffsetsTableSize =
		totalNumSlots * (((uint64_t)1 << (uint64_t)SHADOW_SCALE) * sizeof(struct invalidOffset_struct));

/* Mapping the scratch space tables, lists and info structs contiguously */
#ifdef HANDLE_PAGEFAULTS
	uint64_t blockSize = memLayoutTableSize + (invalidOffsetsTableSize << 1) + infoListSize
						+ validOffsetsListSize + infoStructsSize + printfBufferSize
						+ mallocBufferSize + tableBufferSize + pageFaultHandlerListSize; //+ blockSlotsListSize;
#else
	uint64_t blockSize = memLayoutTableSize + (invalidOffsetsTableSize << 1) + infoListSize
							+ validOffsetsListSize + infoStructsSize + printfBufferSize
							+ mallocBufferSize + tableBufferSize; //+ blockSlotsListSize;
#endif

/* Page align the blockSize so we get the shift dispacement of the set bit of the pageSize */
	uint64_t size = (uint64_t)sysconf(_SC_PAGESIZE);
	uint64_t pageShift = 0;
	while(size >>= 1)
		pageShift++;

/* This page mask is used to get the page aligned addresses */
	uint64_t pageMask = ((uint64_t)(~0)) << pageShift;

/* Round the block size to the next page boundary */
	if(blockSize & (~pageMask))
		blockSize = ((blockSize & pageMask) + (uint64_t)sysconf(_SC_PAGESIZE));

	uint64_t mmapPtr = (uint64_t)Sysmmap(NULL, blockSize, PROT_READ | PROT_WRITE,
											MAP_SHARED | MAP_ANONYMOUS | MAP_NORESERVE, 0, 0);
	if(mmapPtr == (uint64_t)MAP_FAILED) {
	/* Most likely there is no space available to map the scratch space.
	 * Also, other functions like __Assert, DEBUG_PRINTF, etc. cannot be
	 * used since all are dependent on the scratch space buffer. So it is
	 * very difficult to print the error message to the programmer. So we
	 * simply quit since there is nothing much to do without scratch space.
	 */
		raise(SIGABRT);
	}

/* Setting the pointers to the data structures for the scratch space up */
	scratchSpaceInfoPtr = (struct scratchSpaceInfo *) mmapPtr;
	sysPageInfoPtr = (struct sysPageInfo *)(mmapPtr + sizeof(struct scratchSpaceInfo));
	objInfoPtr =
			(struct objInfo *)(mmapPtr +  sizeof(struct scratchSpaceInfo) + sizeof(struct sysPageInfo));
	stackInfoPtr = (struct stack *)(mmapPtr + sizeof(struct scratchSpaceInfo)
									+ sizeof(struct sysPageInfo) + sizeof(struct objInfo));
	heapInfoPtr = (struct heap *)(mmapPtr + sizeof(struct scratchSpaceInfo) + sizeof(struct stack)
								+ sizeof(struct sysPageInfo) + sizeof(struct objInfo));
	appMappingInfoPtr =
			(struct appMappingInfo *)(mmapPtr + infoStructsSize - sizeof(struct appMappingInfo));

	memLayoutTablePtr = (struct unitInfo *)(mmapPtr + infoStructsSize);
	posInvalidOffsetsTablePtr =
			(struct invalidOffset_struct *)(mmapPtr + memLayoutTableSize + infoStructsSize);
	negInvalidOffsetsTablePtr = (struct invalidOffset_struct *)(mmapPtr + memLayoutTableSize
												+ invalidOffsetsTableSize + infoStructsSize);

	app_shadowListPtr = (struct appShadowAddrsNode *)(mmapPtr + memLayoutTableSize
											+ (invalidOffsetsTableSize << 1) + infoStructsSize);
	validOffsetsListPtr = (struct validOffset_struct *)(mmapPtr + memLayoutTableSize
							+ (invalidOffsetsTableSize << 1) + infoStructsSize + infoListSize);

	scratchSpaceInfoPtr->printfPtr = mmapPtr + memLayoutTableSize + (invalidOffsetsTableSize << 1)
									+ infoStructsSize + infoListSize + validOffsetsListSize;
	scratchSpaceInfoPtr->mallocPtr = mmapPtr + memLayoutTableSize + (invalidOffsetsTableSize << 1)
							+ infoStructsSize + infoListSize + validOffsetsListSize + printfBufferSize;
	scratchSpaceInfoPtr->tablePtr = (struct tableEntry_struct *)(mmapPtr + memLayoutTableSize +
										(invalidOffsetsTableSize << 1) + infoStructsSize + infoListSize +
											validOffsetsListSize + printfBufferSize + mallocBufferSize);

	scratchSpaceInfoPtr->printfBufferSize = printfBufferSize;
	scratchSpaceInfoPtr->mallocBufferSize = mallocBufferSize;
	scratchSpaceInfoPtr->tableBufferSize = tableBufferSize;

#ifdef HANDLE_PAGEFAULTS
	pageFaultHandlersArrayPtr = (void(**)(int, sigjmp_buf **))(mmapPtr + memLayoutTableSize +
						(invalidOffsetsTableSize << 1) + infoStructsSize + infoListSize +
							validOffsetsListSize + printfBufferSize + mallocBufferSize + tableBufferSize);
#endif

	//blockSlotsListPtr = (uint64_t *)(mmapPtr + memLayoutTableSize + (invalidOffsetsTableSize << 1)
		//+ infoStructsSize + infoListSize + blockSlotsListSize);
}

void InitScratchSpaceInfo(void)
{
/* Sizes of different tool data structures allocated in the scratch space */
	uint64_t addrMask = ((uint64_t)(~0)) << (uint64_t)SLOT_SHIFT;
	uint64_t totalNumSlots = (uint64_t)1 << (47 - (uint64_t)SLOT_SHIFT);
	uint64_t memLayoutTableSize = totalNumSlots * sizeof(struct unitInfo);
	uint64_t invalidOffsetsTableSize =
			totalNumSlots * (((uint64_t)1 << (uint64_t)SHADOW_SCALE) * sizeof(struct invalidOffset_struct));
	uint64_t infoListSize = totalNumSlots * sizeof(struct appShadowAddrsNode);
	uint64_t validOffsetsListSize = (totalNumSlots << 1) * sizeof(struct validOffset_struct);
	uint64_t infoStructsSize =
			sizeof(struct stack) + sizeof(struct heap) + sizeof(struct scratchSpaceInfo)
			+ sizeof(struct sysPageInfo) + sizeof(struct appMappingInfo) + sizeof(struct objInfo);
	uint64_t printfBufferSize = scratchSpaceInfoPtr->printfBufferSize;
	uint64_t mallocBufferSize = scratchSpaceInfoPtr->mallocBufferSize;
	uint64_t tableBufferSize = scratchSpaceInfoPtr->tableBufferSize;

#ifdef HANDLE_PAGEFAULTS
	uint64_t pageFaultHandlerListSize = (uint64_t)1 << 12;
#endif

	//uint64_t blockSlotsListSize = sizeof(struct blockSlotAddrNode) * totalNumSlots;
#ifdef HANDLE_PAGEFAULTS
	uint64_t blockSize = memLayoutTableSize + (invalidOffsetsTableSize << 1) + infoListSize
							+ validOffsetsListSize + infoStructsSize + printfBufferSize
					+ mallocBufferSize + tableBufferSize + pageFaultHandlerListSize; //+ blockSlotsListSize;
#else
	uint64_t blockSize = memLayoutTableSize + (invalidOffsetsTableSize << 1) + infoListSize
						+ validOffsetsListSize + infoStructsSize + printfBufferSize
						+ mallocBufferSize + tableBufferSize; //+ blockSlotsListSize;
#endif

/* Updating info about the scratch space */
	uint64_t scratchEndAddr = (uint64_t)scratchSpaceInfoPtr + blockSize;
	uint64_t scratchSlotsBegAddr = (uint64_t)scratchSpaceInfoPtr & addrMask;
	uint64_t scratchSlotsEndAddr;
	if (scratchEndAddr & (~addrMask))
		scratchSlotsEndAddr = (scratchEndAddr & addrMask) + (uint64_t)SLOT_SIZE;
	else
		scratchSlotsEndAddr = scratchEndAddr;
	uint64_t numSlots =  (scratchSlotsEndAddr - scratchSlotsBegAddr) >> (uint64_t)SLOT_SHIFT;

/* Recording information about the scratch space structure */
	scratchSpaceInfoPtr->scratchSpaceAddr = (uint64_t)scratchSpaceInfoPtr;
	scratchSpaceInfoPtr->scratchSpaceSize = blockSize;
	scratchSpaceInfoPtr->scratchSlotsBegAddr = scratchSpaceInfoPtr->scratchSpaceAddr & addrMask;
	scratchSpaceInfoPtr->numScratchSlots = numSlots;

/* Initializing the memLayout table */
	struct appShadowAddrsNode *appShadowAddrsNodePtr = app_shadowListPtr;
	struct unitInfo *unitPtr = memLayoutTablePtr + (scratchSlotsBegAddr >> (uint64_t)SLOT_SHIFT);
	uint64_t countSlots = 0;
	while ((countSlots++) != numSlots) {
		unitPtr->offset = (int64_t) SCRATCH_UNIT_OFFSET;
		unitPtr->numReg = 1;
		uint64_t memLayoutTableOffset =
				((uint64_t)unitPtr - (uint64_t)memLayoutTablePtr) / sizeof(struct unitInfo);
		appShadowAddrsNodePtr->appUnitAddr = memLayoutTableOffset << (uint64_t)SLOT_SHIFT;
		appShadowAddrsNodePtr->nextNodePtr = appShadowAddrsNodePtr + sizeof(struct appShadowAddrsNode);
		appShadowAddrsNodePtr = appShadowAddrsNodePtr->nextNodePtr;
		unitPtr++;
	}
	(appShadowAddrsNodePtr - sizeof(struct appShadowAddrsNode))->nextNodePtr = NULL;

/* Initialize the mapped application region info. All the other fields are already intialized
 * to zero.
 */
	appMappingInfoPtr->mapping_type = (int8_t)NO_MAPPING_USED;

/* Initializing the blocked slots list *
	struct blockSlotAddrNode *blockSlotNodePtr = blockSlotsListPtr;
	countSlots = 0;
	while((countSlots++) != totalNumSlots) {
		blockSlotNodePtr->blockedSlotAddr = (uint64_t)MAX_VIRTUAL_ADDR;
		blockSlotNodePtr++;
	}
*/
}

void StoreSysPageInfo(void)
{
	sysPageInfoPtr->pageSize = (uint64_t)sysconf(_SC_PAGESIZE);

/* We get the shift dispacement of the set bit of the pageSize */
	uint64_t size = sysPageInfoPtr->pageSize;
	while(size >>= 1)
		(sysPageInfoPtr->pageShift)++;

/* This page mask is used to get the page aligned addresses */
	sysPageInfoPtr->pageMask = ((uint64_t)(~0)) << (sysPageInfoPtr->pageShift);
}

void InitMemLayoutTable(void)
{
/* We mark all the units in the memlayout table empty */
	struct unitInfo *unitPtr = memLayoutTablePtr;
	uint64_t totalNumSlots = (uint64_t)1 << (47 - (uint64_t)SLOT_SHIFT);
	uint64_t countSlots = totalNumSlots;
	while (countSlots--) {
		unitPtr->offset = (int64_t)EMPTY_SLOT_OFFSET;
		unitPtr->numReg = (uint64_t)NULL_NUM_SUB_REG;
		unitPtr++;
	}
}

uint64_t RoundUpSize_to_PageSizeMultiple(uint64_t size)
{
	if(size & (~sysPageInfoPtr->pageMask))
		return ((size & sysPageInfoPtr->pageMask) + sysPageInfoPtr->pageSize);
	return size;
}

void Get_RegSlotsInfo(uint64_t regBegAddr, uint64_t regSize, struct regSlotsInfo *regSlotsInfoPtr)
{
	uint64_t pageAligned_regBegAddr = regBegAddr & (sysPageInfoPtr->pageMask);

/* We find the slots info that enclose the given region */
	uint64_t pageAligned_regEndAddr =
			pageAligned_regBegAddr + RoundUpSize_to_PageSizeMultiple(regSize);
	uint64_t addrMask = ((uint64_t)(~0)) << (uint64_t)SLOT_SHIFT;
	uint64_t regSlotsBegAddr = pageAligned_regBegAddr & addrMask;
	uint64_t regSlotsEndAddr;
	if (pageAligned_regEndAddr & (~addrMask))
		regSlotsEndAddr = (pageAligned_regEndAddr & addrMask) + (uint64_t)SLOT_SIZE;
	else
		regSlotsEndAddr = pageAligned_regEndAddr;
	uint64_t numRegSlots =  (regSlotsEndAddr - regSlotsBegAddr) >> (uint64_t)SLOT_SHIFT;

/* Store the information in the given struct */
	regSlotsInfoPtr->regSlotsBegAddr = regSlotsBegAddr;
	regSlotsInfoPtr->numRegSlots = numRegSlots;
}


/************************************ MEMORY ALLOCATOR *************************************/

/*
 * Whenever an app region is mapped by the user application, the memory layout of the slots that
 would enclose the region, could be:
 1) <E>: <Empty>......<Empty> : All slots may be empty before mapping.
 2) <A>: <App> : The region might fit into the already-marked A unit (which enclosed at least
 one mapped region before this new mapping must have taken place).
 3) <AA>: <App><App> : The given mapping might taken place around and on the common boundary of
 two adjacent app units.
 4) <EA>: <Empty>.........<Empty><App> : The mapped region may occupy the empty slots and part of
 it could overlap with an existing app unit.
 5) <AE>: <App><Empty>.....<Empty> : Part of the mapped region may overlap with the existing app
 unit and the rest of it could occupy the empty slots following the app unit.
 6) <AEA>: <App1><Empty>.........<Empty><App2> : The lower addresses of the map region might be
 part of the App1 unit and the higher addresses might overlap with App2 unit and the rest of the
 part of the region occupy the empty slot(s).

 * Considering the slots in the vicinity of the aforementioned slots enlcosing the mapped region,
 we could have the folowing layouts corresonding to the above layouts:
 (NOTE: <Scratch> denotes slot occupied exclusively by the tool's scratch space and <?> denotes
 slot that we do not really care about; <EA> == <ES> and <AE> == <SE> when A unit is scratch unit.
 <AEA> == <SEA> and  <AEA> == <AES> when one of the A units is a scratch unit and only one of the
 app units can be scratch units since, scratch slots are contiguous).
 1) <App1>.<E>.<App2> , <App>.<E>.<Scratch>, <Scratch>.<E>.<App>, <Scratch>.<E>.<Empty>,
 <Empty>.<E>.<Scratch>, <App>.<E>.<Empty>, <Empty>.<E>.<App>, <Empty>.<E>.<Empty>
 2) <?>.<A>.<?>, <?>.<Scratch>.<?> (no need to look into the vicinity)
 3) <?>.<AA>.<?> (no need to look into the vicinity)
 4) <App>.<EA>.<?>, <Scratch>.<EA>.<?>, <App>.<ES>.<?>, <Empty>.<EA>.<?>, <Empty>.<ES>.<?>
 5) <?>.<AE>.<App>, <?>.<AE>.<Scratch>, <?>.<AE>.<Empty>, <?>.<SE>.<App>, <?>.<SE>.<Empty>
 6) <?>.<AEA>.<?>, <?>.<SEA>.<?>, <?>.<AES>.<?>
 */
void MapAppRegion(uint64_t appSlotsBegAddr, uint64_t numAppSlots)
{
/* Just a sanity check to see if number of app slots is equal to zero.
 * If yes, there is nothing to do.
 */
	if(!numAppSlots)
		return;

/* Most of the time, we would not need to map a new shadow everytime so we just check if the
 * given raange of clots have shadow(s) already.
 */
	struct unitInfo* unitPtr = memLayoutTablePtr + (appSlotsBegAddr >> (uint64_t)SLOT_SHIFT);
	uint64_t countSlots = 0;
	while(countSlots++ != numAppSlots) {
	/* Check if the given region already has a valid shadow */
		if (unitPtr->offset > (int64_t) MAX_VALID_OFFSET
		|| unitPtr->offset == (int64_t)SCRATCH_UNIT_OFFSET) {
			goto map_shadow;
		}
		unitPtr++;
	}

#ifdef DEBUG
	//Print_ShadowOffsets_Cache();
#endif
	return;

map_shadow:
	unitPtr = memLayoutTablePtr + (appSlotsBegAddr >> (uint64_t)SLOT_SHIFT);
	bool emptyUnitFirst = false;
	uint64_t memLayoutTableOffset;
	uint64_t appHighSlotAddr = 0;
	uint64_t appLowSlotAddr = 0;
	unitPtr = memLayoutTablePtr + (appSlotsBegAddr >> (uint64_t)SLOT_SHIFT);
	countSlots = 0;
	while (countSlots != numAppSlots) {
		if (unitPtr->offset == (int64_t) EMPTY_SLOT_OFFSET) {
			if (!countSlots)
				emptyUnitFirst = true;
		} else {
		/* If its not an empty slot, it has to be an app unit */
			memLayoutTableOffset =
					((uint64_t) unitPtr - (uint64_t) memLayoutTablePtr) / sizeof(struct unitInfo);
			if (!appLowSlotAddr)
				appLowSlotAddr = memLayoutTableOffset << (uint64_t)SLOT_SHIFT;
			else
				appHighSlotAddr = memLayoutTableOffset << (uint64_t)SLOT_SHIFT;
		}
		unitPtr++;
		countSlots++;
	}
	if (emptyUnitFirst) {
		if (appLowSlotAddr)
			Manage_EA_MemLayout(appSlotsBegAddr, numAppSlots);
		else
			Manage_E_MemLayout(appSlotsBegAddr, numAppSlots);
	} else {
		if (!appHighSlotAddr) {
			if (numAppSlots != 1)
				Manage_AE_MemLayout(appSlotsBegAddr, numAppSlots);
			else
				Manage_A_MemLayout(appSlotsBegAddr);
		} else {
			if (numAppSlots != 2)
				Manage_AEA_MemLayout(appSlotsBegAddr, numAppSlots);
			else
				Manage_AA_MemLayout(appSlotsBegAddr);
		}
	}

#ifndef HANDLE_PAGEFAULTS
/* If the application and the shadow memory library are mapped as shared objects and
 * the heap is intended to be blocked, then we have to make sure that both initliazed
 * offsets in the offsets cache are the same. If not, then there is no way we can handle
 * page faults because the application and the shadow memory library are mapped as shared
 * objects in the hope of effectively using single offset only.
 */
	if(shadowOffsets[1]) {
		ASSERT(shadowOffsets[0] == shadowOffsets[1],
				"Mappings using multiple shadow offsets when single offset is "\
				"supposed to be used. Abort.\n");
	}
#endif

#ifdef DEBUG
	//Print_ShadowOffsets_Cache();
#endif
}

/* Note: when counting the number of slots above the appBegSlotAddr and below the entire range of
 slots that that enclose the newly mapped region, we also count in the sratch units.
 Consider this case: If memory layout for the slots in that the region is enclosed by and the
 slots in the vicinity is .....<App><Scratch><Empty1><Empty2>... Now, if the newly mapped region
 happens to be completely enclosed by <Empty1>, then the memory layout will be like ..........
 <App><Scratch><App1><Empty2>... since the empty slot, after mapping of the app region, will be
 considered as an app unit, which in this case is say <App1>. Now, we could try map shadow for
 <App1> using the offset used for <App>. However, it might not work for <App1> so we would have
 to either find an offset that works for <App> as well as <App2> or we could simply get a new
 offset for <App1> and augment the valid offset list which would result in increase in the number
 of offsets which could potentially negatively impact the performance. So it seems imperative to
 count scratch units as app units and map shadow for it and change its protection to NO ACCESS.
 Also, this makes the algorithm simpler since for other kinds of aforementioned layouts, cases
 similar to this one are common and it seems to be a better idea considering the number of
 layouts possible. So the scratch space ends up having shadow region and reserved regions using
 existing valid offsets.
 */

uint64_t NumAppSlots_VicinityLowAppUnits(uint64_t begAppSlotAddr)
{
/* The slot might be the topmost slot of the virtual user address space */
	if(!begAppSlotAddr) {
	/* We check if the topmost slot is an app unit or not */
		struct unitInfo *unitPtr = memLayoutTablePtr + (begAppSlotAddr >> (uint64_t)SLOT_SHIFT);
		if (unitPtr->offset > (int64_t) MAX_VALID_OFFSET)
			return 0;
		return 1;
	}

/* We kind of roll back if the given slot is not the topmost slot and count the number of app units */
	uint64_t numLowAppSlots = 0;
	if (!((uint64_t)(begAppSlotAddr - (uint64_t)SLOT_SIZE) >> 47)) {
		struct unitInfo *unitPtr =
				memLayoutTablePtr + ((begAppSlotAddr - (uint64_t)SLOT_SIZE) >> (uint64_t)SLOT_SHIFT);
		while ((uint64_t)unitPtr >= (uint64_t)memLayoutTablePtr) {
			if (unitPtr->offset > (int64_t) MAX_VALID_OFFSET)
				break;
			unitPtr--;
			numLowAppSlots++;
		}
	}
	return numLowAppSlots;
}

uint64_t NumAppSlots_VicinityHighAppUnits(uint64_t endAppSlotAddr)
{
	uint64_t numHighAppSlots = 0;
	if (!(endAppSlotAddr >> 47)) {
		uint64_t totalNumSlots = (uint64_t)1 << (47 - (uint64_t)SLOT_SHIFT);
		uint64_t memLayoutTableEnd = (uint64_t)(memLayoutTablePtr + totalNumSlots - 1);
		struct unitInfo *unitPtr = memLayoutTablePtr + (endAppSlotAddr >> (uint64_t)SLOT_SHIFT);
		while ((uint64_t)unitPtr <= memLayoutTableEnd) {
			if (unitPtr->offset > (int64_t) MAX_VALID_OFFSET)
				break;
			unitPtr++;
			numHighAppSlots++;
		}
	}
	return numHighAppSlots;
}

void Convert_Shadow_to_Reserved(uint64_t appSlotBegAddr, uint64_t numAppSlots)
{
	struct unitInfo *appUnitPtr = memLayoutTablePtr + (appSlotBegAddr >> (uint64_t)SLOT_SHIFT);
	uint64_t shadowSlotAddr = (appSlotBegAddr << (uint64_t)SHADOW_SCALE) + appUnitPtr->offset;
	struct unitInfo *shadowUnitPtr = memLayoutTablePtr + (shadowSlotAddr >> (uint64_t)SLOT_SHIFT);
	uint64_t numShadowSlots = numAppSlots << (uint64_t)SLOT_SHIFT;

/* Here we convert all the shadow units to reserved units simply by changing their protection
* unmapping all the reserved units for the former shadow units.
*/
	uint64_t countSlots = 0;
	while ((countSlots++) != numShadowSlots) {
	/* Unmap the reserved units of the shadow */
		UnmapRegUnitReservedSlots(shadowSlotAddr);
		shadowUnitPtr->offset = (int64_t) RESERVED_SLOT_OFFSET;

	/* Reserved units have to have no access protection */
		Sysmprotect((void *) shadowSlotAddr, (uint64_t)SLOT_SIZE, PROT_NONE);
		shadowUnitPtr++;
		shadowSlotAddr += (uint64_t)SLOT_SIZE;
	}
}

uint64_t Safe_Get_ShadowData_TemCopy(uint64_t appSlotBegAddr, uint64_t numAppSlots)
{
/* We just do a sanity check here */
	if(!numAppSlots)
		return 0;

	struct unitInfo *appUnitPtr = memLayoutTablePtr + (appSlotBegAddr >> (uint64_t)SLOT_SHIFT);
	uint64_t shadowSlotsBegAddr = (appSlotBegAddr << (uint64_t)SHADOW_SCALE) + appUnitPtr->offset;
	uint64_t numShadowSlots = numAppSlots << (uint64_t)SHADOW_SCALE;
	struct validOffset_struct *validOffsetNodePtr = validOffsetsListPtr;
	uint64_t shadowData_copyPtr = (uint64_t) Sysmmap(NULL, numShadowSlots << (uint64_t)SLOT_SHIFT,
									PROT_READ | PROT_WRITE, MAP_SHARED | MAP_ANONYMOUS, 0, 0);
	ASSERT(shadowData_copyPtr != (uint64_t)MAP_FAILED, "Failed to make a copy for the shadow.");

/* Now we copy the shadow data to the copies of shadows we just mapped. In the process we skip the
 * scratch slots.
 */
	Safe_Copy_Read_Skip_ScratchShadow(shadowData_copyPtr, shadowSlotsBegAddr, numShadowSlots);

/* Getting to the valid offset list node that has the same offset as that for the specified app unit */
	while (validOffsetNodePtr->validOffset != appUnitPtr->offset)
		validOffsetNodePtr = validOffsetNodePtr->nextNodePtr;

/* The shadow slots for the app unit that has to be 'moved', either need to be unmapped or
 * it could serve as reserved units just in case some other app unit elsewhere is using the
 * same offset for its shadow as the app units in question. Now, this is because the given
 * application units are more likely to use a new offset rather than their old one, so the
 * this offset might be used to access data that is not at this offset, so we have to rely
 * on page faults. Therefore, these shadow slots might have to be converted to reserved units.
*/
	if(validOffsetNodePtr->numRegSameOffset == numAppSlots)
		MunmapShadowMemSlots(appSlotBegAddr, numAppSlots);
	else
		Convert_Shadow_to_Reserved(appSlotBegAddr, numAppSlots);

	return shadowData_copyPtr;
}

/* This is unsafe since its copying process does not look for scratch units in the
 * given range of slots This function is only to be used if we are aware of and
 * certain about the memory layout.
 */
uint64_t Unsafe_Get_ShadowData_TemCopy(uint64_t appSlotBegAddr, uint64_t numAppSlots)
{
/* We just do a sanity check here */
	if(!numAppSlots)
		return 0;

	struct unitInfo *appUnitPtr = memLayoutTablePtr + (appSlotBegAddr >> (uint64_t)SLOT_SHIFT);
	uint64_t shadowSlotsBegAddr = (appSlotBegAddr << (uint64_t)SHADOW_SCALE) + appUnitPtr->offset;
	uint64_t numShadowSlots = numAppSlots << (uint64_t)SHADOW_SCALE;
	struct validOffset_struct *validOffsetNodePtr = validOffsetsListPtr;
	uint64_t shadowData_copyPtr = (uint64_t) Sysmmap(NULL, numShadowSlots << (uint64_t)SLOT_SHIFT,
									PROT_READ | PROT_WRITE, MAP_SHARED | MAP_ANONYMOUS, 0, 0);
	ASSERT(shadowData_copyPtr != (uint64_t)MAP_FAILED, "Failed to make a copy for the shadow.");

/* Now we copy the shadow data to the copies of shadows we just mapped. In the process we skip the
 * scratch slots.
 */
	Unsafe_Copy_Read_Skip_ScratchShadow(shadowData_copyPtr, shadowSlotsBegAddr, numShadowSlots);

/* Getting to the valid offset list node that has the same offset as that for the specified app unit */
	while (validOffsetNodePtr->validOffset != appUnitPtr->offset)
		validOffsetNodePtr = validOffsetNodePtr->nextNodePtr;

/* The shadow slots for the app unit that has to be 'moved', either need to be unmapped
 * or it could serve as reserved units just in case some other app unit elsewhere is using
 * the same offset for its shadow as the app units in question. Now, this is because the
 * given application units are more likely to use a new offset rather than their old one,
 * so the this offset might be used to access data that is not at this offset, so we have
 * to rely on page faults. Therefore, these shadow slots might have to be converted to
 * reserved units.
*/
	if(validOffsetNodePtr->numRegSameOffset == numAppSlots)
		MunmapShadowMemSlots(appSlotBegAddr, numAppSlots);
	else
		Convert_Shadow_to_Reserved(appSlotBegAddr, numAppSlots);

	return shadowData_copyPtr;
}

/* Here we read from the main shadow and copy to the specified copy mapping */
void Safe_Copy_Read_Skip_ScratchShadow(uint64_t shadowData_copyPtr,
									uint64_t shadowSlotsBegAddr, uint64_t numShadowSlots)
{
	uint64_t scratchBegSlotsAddr = scratchSpaceInfoPtr->scratchSlotsBegAddr;
	uint64_t scratchEndSlotsAddr =
			scratchBegSlotsAddr + (scratchSpaceInfoPtr->numScratchSlots << (uint64_t)SLOT_SHIFT);
	uint64_t shadowSlotsEndAddr = shadowSlotsBegAddr + (numShadowSlots << (uint64_t)SLOT_SHIFT);

/* We get acess to the offset of the scratch space shadow for the memLayoutTable */
	struct unitInfo *scratchShadowUnitPtr =
			memLayoutTablePtr + (scratchBegSlotsAddr >> (uint64_t)SLOT_SHIFT);
	uint64_t scratchShadowBegAddr =
			(scratchBegSlotsAddr << (uint64_t)SHADOW_SCALE) + (scratchShadowUnitPtr->offset);
	uint64_t scratchShadowEndAddr =
			(scratchEndSlotsAddr << (uint64_t)SHADOW_SCALE) + (scratchShadowUnitPtr->offset);

/* We skip the  scratch shadow unita when copying. This is important because the
 * scratch space unit can be huge and memcpy can be pretty slow when unnecessarily
 * copying bytes of data.
 */
/* There is nothing to copy since the given range of slots is a subset of scratch shadow slots */
	if(scratchShadowBegAddr >= shadowSlotsBegAddr
	&& scratchShadowEndAddr <= shadowSlotsEndAddr) {
		return;
	}

/* Considering the case where the scratch space shadow is a subset of the given shadow egion */
	if(scratchShadowBegAddr > shadowSlotsBegAddr && scratchShadowEndAddr < shadowSlotsEndAddr) {
	/* Since scratch space is a proper subset, we skip it while copying data from shadows. So we
	 * begin with copying the lower segment first.
	 */
		SHADOW_MEMCPY((void *)shadowData_copyPtr, (void *)shadowSlotsBegAddr,
										scratchShadowBegAddr - shadowSlotsBegAddr);

		/* Now copy the high shadow segment */
		SHADOW_MEMCPY((void *)(shadowData_copyPtr + scratchShadowEndAddr - shadowSlotsBegAddr),
					(void *)scratchShadowEndAddr, shadowSlotsEndAddr - scratchShadowEndAddr);
		return;
	}

/* Considering the case where scratch unit(s) is(are) outside the domain
 * of the given region on the lower address side.
 */
	if(scratchShadowBegAddr < shadowSlotsBegAddr) {
		if(scratchShadowEndAddr > shadowSlotsBegAddr) {
		/* There is nothing to copy since the given range of slots is a
		 * subset of scratch shadow slots.
		 */
			if(scratchShadowEndAddr >= shadowSlotsEndAddr)
				return;

			if(scratchShadowEndAddr < shadowSlotsEndAddr) {
			/* Now copy the high shadow segment */
				SHADOW_MEMCPY((void *)(shadowData_copyPtr + scratchShadowEndAddr - shadowSlotsBegAddr),
							(void *)scratchShadowEndAddr, shadowSlotsEndAddr - scratchShadowEndAddr);
				return;
			}
		}
	}

/* Considering the case where scratch unit(s) is(are) outside the domain of the given region
* on the higher address side.
*/
	if(scratchShadowEndAddr > shadowSlotsEndAddr) {
		if(scratchShadowBegAddr < shadowSlotsEndAddr) {
		/* There is nothing to copy if the given range of slots is a subset of scratch shadow slots*/
			if(scratchShadowBegAddr <= shadowSlotsBegAddr)
				return;

			if(scratchShadowBegAddr > shadowSlotsBegAddr) {
			/* Just copy the higher shadow segment */
				SHADOW_MEMCPY((void *) shadowData_copyPtr, (void *)shadowSlotsBegAddr,
											scratchShadowBegAddr - shadowSlotsBegAddr);
				return;
			}
		}
	}

/* This means that the scratch shadow is NOT a subset of the given
 * shadow region, so we can simply copy the entire shadow data.
 */
	SHADOW_MEMCPY((void *)shadowData_copyPtr, (void *)shadowSlotsBegAddr,
									numShadowSlots << (uint64_t)SLOT_SHIFT);
}

/* This is an unsafe subroutine since it does not look for scratch shadow in the given
 * range of slots. This is only to be used when we are certain that it is safe to use it.
 */
void Unsafe_Copy_Read_Skip_ScratchShadow (uint64_t shadowData_copyPtr,
									uint64_t shadowSlotsBegAddr, uint64_t numShadowSlots)
{
	SHADOW_MEMCPY((void *)shadowData_copyPtr, (void *)shadowSlotsBegAddr,
										numShadowSlots << (uint64_t)SLOT_SHIFT);
}

/* Here we copy from the specified copy mapping and write to the main intended mapping */
void Safe_Copy_Write_Skip_ScratchShadow (uint64_t shadowCopyBegAddr,
								uint64_t shadowSlotsBegAddr, uint64_t numShadowSlots)
{
/* We just do a sanity check here */
	if(!numShadowSlots)
		return;

	uint64_t scratchBegSlotsAddr = scratchSpaceInfoPtr->scratchSlotsBegAddr;
	uint64_t scratchEndSlotsAddr =
			scratchBegSlotsAddr + (scratchSpaceInfoPtr->numScratchSlots << (uint64_t)SLOT_SHIFT);
	uint64_t shadowSlotsEndAddr = shadowSlotsBegAddr + (numShadowSlots << (uint64_t)SLOT_SHIFT);

/* We get acess to the offset of the scratch space shadow for the memLayoutTable */
	struct unitInfo *scratchShadowUnitPtr =
						memLayoutTablePtr + (scratchBegSlotsAddr >> (uint64_t)SLOT_SHIFT);
	uint64_t scratchShadowBegAddr =
			(scratchBegSlotsAddr << (uint64_t)SHADOW_SCALE) + (scratchShadowUnitPtr->offset);
	uint64_t scratchShadowEndAddr =
			(scratchEndSlotsAddr << (uint64_t)SHADOW_SCALE) + (scratchShadowUnitPtr->offset);

/* We skip the  scratch shadow unita when copying from the copy mapping to
 * the specified shadow map. This is important because the scratch space
 * unit can be huge and memcpy can be pretty slow when unnecessarily copying
 * bytes of data.
 */
/* If the given range of slots and shadow scratch coincide, we're done since
 * there is nothing to copy.
 */
	if(scratchShadowBegAddr == shadowSlotsBegAddr
	&& scratchShadowEndAddr == shadowSlotsEndAddr) {
		return;
	}

/* Considering the case where the scratch space shadow is a subset of the given shadow region */
	if(scratchShadowBegAddr > shadowSlotsBegAddr && scratchShadowEndAddr < shadowSlotsEndAddr) {
	/* Since scratch space is a proper subset, we skip it while copying data from shadows. So we
	 * begin with copying the lower segment first.
	 */
		SHADOW_MEMCPY((void *)shadowSlotsBegAddr, (void *)shadowCopyBegAddr,
													scratchShadowBegAddr - shadowSlotsBegAddr);

		/* Now copy the high shadow segment */
		SHADOW_MEMCPY((void *)scratchShadowEndAddr,
				(void *)(shadowCopyBegAddr + scratchShadowEndAddr - shadowSlotsBegAddr),
														shadowSlotsEndAddr - scratchShadowEndAddr);
		return;
	}

/* Considering the case where scratch unit(s) is(are) outside the domain of the given region
* on the lower address side.
*/
	if(scratchShadowBegAddr < shadowSlotsBegAddr) {
		if(scratchShadowEndAddr > shadowSlotsBegAddr) {
		/* There is nothing to copy if this given range of slots is a subset of scratch space  */
			if(scratchShadowEndAddr >= shadowSlotsEndAddr)
				return;

			if(scratchShadowEndAddr < shadowSlotsEndAddr) {
			/* Now copy the high shadow segment */
				SHADOW_MEMCPY((void *)scratchShadowEndAddr,
						(void *)(shadowCopyBegAddr + scratchShadowEndAddr - shadowSlotsBegAddr),
								shadowSlotsEndAddr - scratchShadowEndAddr);
				return;
			}
		}
	}

/* Considering the case where scratch unit(s) is(are) outside the domain of the given region
* on the higher address side.
*/
	if(scratchShadowEndAddr > shadowSlotsEndAddr) {
		if(scratchShadowBegAddr < shadowSlotsEndAddr) {
		/* There is nothing to copy if this given range of slots is a subset of scratch space  */
			if(scratchShadowBegAddr <= shadowSlotsBegAddr)
				return;

			if(scratchShadowBegAddr > shadowSlotsBegAddr) {
			/* Just copy the higher shadow segment */
				SHADOW_MEMCPY((void *)shadowSlotsBegAddr, (void *)shadowCopyBegAddr,
											scratchShadowBegAddr - shadowSlotsBegAddr);
				return;
			}
		}
	}

/* This means that the scratch shadow is NOT a subset of the given shadow
 * region, so we can simply copy the entire shadow data.
 */
	SHADOW_MEMCPY((void *)shadowSlotsBegAddr, (void *)shadowCopyBegAddr,
									numShadowSlots << (uint64_t)SLOT_SHIFT);
}

/* This subroutine is unsafe because it does not look for scratch shadow in
 * the given range of slots. We have this to avoid the unecessary slow down
 * due to branches above, especially when we are certain.
 */
void Unsafe_Copy_Write_Skip_ScratchShadow(uint64_t shadowCopyBegAddr,
							uint64_t shadowSlotsBegAddr, uint64_t numShadowSlots)
{
/* We just do a sanity check here */
	if(!numShadowSlots)
		return;

	SHADOW_MEMCPY((void *)shadowSlotsBegAddr, (void *)shadowCopyBegAddr,
										numShadowSlots << (uint64_t)SLOT_SHIFT);
}

void Unmap_ShadowData_TemCopy(uint64_t shadowDataCopyAddr, uint64_t numShadowCopySlots)
{
	Sysmunmap((void *) shadowDataCopyAddr, numShadowCopySlots << (uint64_t)SLOT_SHIFT);
}

void
Unmap_Scratch_ShadowReservedSlots(uint64_t scratchLowSlotAddr, uint64_t scratchHighSlotAddr,
																		int64_t shadowOffset)
{
	uint64_t numScratchShadowSlots = (uint64_t)1 << (uint64_t)SHADOW_SCALE;
	struct unitInfo *scratchUnitPtr =
			memLayoutTablePtr + (scratchLowSlotAddr >> (uint64_t)SLOT_SHIFT);
	uint64_t scratchAddr = scratchLowSlotAddr;
	uint64_t countScratchSlots = 0;
	while((countScratchSlots++) !=  scratchSpaceInfoPtr->numScratchSlots) {
		if(scratchUnitPtr->numReg == 1) {
			uint64_t scratchShadowAddr =  (scratchAddr << (uint64_t)SHADOW_SCALE) + shadowOffset;
			if(!(scratchShadowAddr >> 47)) {
				uint64_t countShadowSlots = 0;
				while((countShadowSlots++) !=  numScratchShadowSlots) {
					UnmapRegUnitReservedSlots(scratchShadowAddr);
					scratchShadowAddr += (uint64_t)SLOT_SIZE;
				}
			}
		}
		scratchAddr += (uint64_t)SLOT_SIZE;
		scratchUnitPtr++;
	}
}

void Reverse_changes_to_ValidOffsetSList_for_Scratch(uint64_t scratchLowSlotAddr,
											uint64_t scratchHighSlotAddr, int64_t shadowOffset)
{
	struct validOffset_struct *validOffsetNodePtr = validOffsetsListPtr;
	while(validOffsetNodePtr->validOffset != shadowOffset)   /* Walk the list */
		validOffsetNodePtr = validOffsetNodePtr->nextNodePtr;
	struct unitInfo *unitPtr = memLayoutTablePtr
									+ (scratchLowSlotAddr >> (uint64_t)SLOT_SHIFT);
	uint64_t numScratchSlots = (scratchHighSlotAddr - scratchLowSlotAddr) >> (uint64_t)SLOT_SHIFT;
	uint64_t countSlots = 0;
	while((countSlots++) != numScratchSlots) {
		if(unitPtr->numReg == 1)
			(validOffsetNodePtr->numRegSameOffset)--;
		unitPtr++;
	}
}

void Reverse_changes_to_AppShadowInfoList_for_Scratch(uint64_t scratchLowSlotAddr,
																								 		uint64_t scratchHighSlotAddr)
{
	struct appShadowAddrsNode *appShadowAddrsNodePtr = app_shadowListPtr;
	while(appShadowAddrsNodePtr) {
	/* Checking if the app slot from the list is a subset of the scratch space */
		if(appShadowAddrsNodePtr->appUnitAddr >= scratchLowSlotAddr
							&& appShadowAddrsNodePtr->appUnitAddr < scratchHighSlotAddr) {
			struct unitInfo *unitPtr = memLayoutTablePtr
									+ ((appShadowAddrsNodePtr->appUnitAddr) >> (uint64_t)SLOT_SHIFT);
			if(unitPtr->numReg == 1) {
				appShadowAddrsNodePtr->shadowUnitAddr = (uint64_t)NULL;
			}
		}
		appShadowAddrsNodePtr = appShadowAddrsNodePtr->nextNodePtr;
	}
}

void Mprotect_Scratch_Shadow(uint64_t scratchBegSlotsAddr, uint64_t scratchEndSlotsAddr,
													uint64_t shadowOffset, int64_t prot)
{
	uint64_t scratchShadowBegAddr = (scratchBegSlotsAddr << (uint64_t)SHADOW_SCALE) + shadowOffset;
	if(!(scratchShadowBegAddr >> 47)) {
		uint64_t scratchShadowSize = (scratchEndSlotsAddr - scratchBegSlotsAddr) << (uint64_t)SHADOW_SCALE;
		ASSERT (!Sysmprotect((void *) scratchShadowBegAddr, scratchShadowSize, prot),
							"Error in changing the scratch shadow mappings' protection.");
	}
}

void Safe_Reverse_Changes_on_ScratchUnits(uint64_t regSlotsBegAddr, uint64_t numRegSlots,
												uint64_t shadowOffset, int64_t prot)
{
/* We just do a sanity check here */
	if(!numRegSlots)
		return;

	uint64_t scratchBegSlotsAddr = scratchSpaceInfoPtr->scratchSlotsBegAddr;
	uint64_t scratchEndSlotsAddr =
			scratchBegSlotsAddr + (scratchSpaceInfoPtr->numScratchSlots << (uint64_t)SLOT_SHIFT);
	uint64_t regSlotsEndAddr = regSlotsBegAddr + (numRegSlots << (uint64_t)SLOT_SHIFT);

/* Considering the case where the scratch space is a subset of the given region */
	if(scratchBegSlotsAddr >= regSlotsBegAddr && scratchEndSlotsAddr <= regSlotsEndAddr) {
		Mprotect_Scratch_Shadow(scratchBegSlotsAddr, scratchEndSlotsAddr, shadowOffset, prot);
		Reverse_changes_to_AppShadowInfoList_for_Scratch(scratchBegSlotsAddr, scratchEndSlotsAddr);
		Unmap_Scratch_ShadowReservedSlots(scratchBegSlotsAddr, scratchEndSlotsAddr, shadowOffset);
		Reverse_changes_to_ValidOffsetSList_for_Scratch(scratchBegSlotsAddr,
													scratchEndSlotsAddr, shadowOffset);
	} else {
	/* Considering the case where scratch unit(s) is(are) outside the domain of the given region
	* on the lower address side.
	*/
		if(scratchBegSlotsAddr < regSlotsBegAddr) {
			if(scratchEndSlotsAddr > regSlotsBegAddr && scratchEndSlotsAddr <= regSlotsEndAddr) {
				Mprotect_Scratch_Shadow(regSlotsBegAddr, scratchEndSlotsAddr,shadowOffset, prot);
				Reverse_changes_to_AppShadowInfoList_for_Scratch(regSlotsBegAddr, scratchEndSlotsAddr);
				Unmap_Scratch_ShadowReservedSlots(regSlotsBegAddr, scratchEndSlotsAddr, shadowOffset);
				Reverse_changes_to_ValidOffsetSList_for_Scratch(regSlotsBegAddr,
															scratchEndSlotsAddr, shadowOffset);
			}
		} else {
		/* Considering the case where scratch unit(s) is(are) outside the domain of the given region
		* on the higher address side.
		*/
			if(scratchEndSlotsAddr > regSlotsEndAddr) {
				if(scratchBegSlotsAddr >= regSlotsBegAddr && scratchBegSlotsAddr < regSlotsEndAddr) {
					Mprotect_Scratch_Shadow(scratchBegSlotsAddr, regSlotsEndAddr, shadowOffset, prot);
					Reverse_changes_to_AppShadowInfoList_for_Scratch(scratchBegSlotsAddr, regSlotsEndAddr);
					Unmap_Scratch_ShadowReservedSlots(scratchBegSlotsAddr, regSlotsEndAddr, shadowOffset);
					Reverse_changes_to_ValidOffsetSList_for_Scratch(scratchBegSlotsAddr,
															regSlotsEndAddr, shadowOffset);
				}
			}
		}
	}
}

/* This is an unsafe function since it doesn't first check if the given  */
void Unsafe_Reverse_Changes_on_ScratchUnits(uint64_t scratchSlotsBegAddr, uint64_t numScratchSlots,
														uint64_t shadowOffset, int64_t prot)
{
/* We just do a sanity check here */
	if(!numScratchSlots)
		return;

	uint64_t scratchSlotsEndAddr = scratchSlotsBegAddr + (numScratchSlots << (uint64_t)SLOT_SHIFT);

	Mprotect_Scratch_Shadow(scratchSlotsBegAddr, scratchSlotsEndAddr, shadowOffset, prot);
	Reverse_changes_to_AppShadowInfoList_for_Scratch(scratchSlotsBegAddr, scratchSlotsEndAddr);
	Unmap_Scratch_ShadowReservedSlots(scratchSlotsBegAddr, scratchSlotsEndAddr, shadowOffset);
	Reverse_changes_to_ValidOffsetSList_for_Scratch(scratchSlotsBegAddr,scratchSlotsEndAddr, shadowOffset);
}

void Manage_App_EA__DifferentOffsetsCase(uint64_t appSlotsBegAddr, uint64_t numAppSlots)
{
/* Possibilities considered:  <App>.<EA>.<?> when the A and App unit offsets are different */
	uint64_t appSlotAddr = appSlotsBegAddr + ((numAppSlots - 1) << (uint64_t)SLOT_SHIFT);
	uint64_t numLowAppSlots = NumAppSlots_VicinityLowAppUnits(appSlotsBegAddr);
	uint64_t numHighAppSlots = NumAppSlots_VicinityHighAppUnits(appSlotAddr + (uint64_t)SLOT_SIZE);
	uint64_t lowAppSlotAddr = appSlotsBegAddr - (numLowAppSlots << (uint64_t)SLOT_SHIFT);

/* Get copies of the shadow data for low app units; and shared unit and high app units */
	uint64_t lowShadowCopyAddr = Safe_Get_ShadowData_TemCopy(lowAppSlotAddr, numLowAppSlots);
	uint64_t unitShadowCopyAddr = Safe_Get_ShadowData_TemCopy(appSlotAddr, numHighAppSlots + 1);
	uint64_t numLowShadowCopy = numLowAppSlots << (uint64_t)SHADOW_SCALE;
	uint64_t numUnitShadowCopy = (numHighAppSlots + 1) << (uint64_t)SHADOW_SCALE;
	uint64_t newUnitShadowAddr;
	uint64_t newLowShadowAddr;

/* Map the new shadow region for the entire range of addresses */
	int64_t offset = MmapShadowMemSlots(lowAppSlotAddr, numAppSlots + numLowAppSlots + numHighAppSlots);

/* In case the application mapping failed and we are in the process of stack unwinding because of
 * the possiblity of the application region being mapped recursively.
 */
	if(offset == (int64_t)APP_MAPPING_FAILED) {
	/* Now we need to attempt to remap the shadows for aplication units whose shadows were unmapped.
	 * We treat those units as FIXED MAPPINGS since we do not have their info and there must be app
	 * pointers pointing to them already.
	 */
		appMappingInfoPtr->mapping_type = (int8_t)FIXED_MAPPING_USED;

	/* Now, we are ready to map the shadows */
		int64_t lowShadowOffset = MmapShadowMemSlots(lowAppSlotAddr, numLowAppSlots);
		int64_t unitShadowOffset = MmapShadowMemSlots(appSlotAddr, numHighAppSlots + 1);

	/* Copy the shadow data from the temporary copies */
		newLowShadowAddr = (lowAppSlotAddr << (uint64_t)SHADOW_SCALE) + lowShadowOffset;
		newUnitShadowAddr = (appSlotAddr << (uint64_t)SHADOW_SCALE) + unitShadowOffset;

	/* Set the protection to no acess and unmap reserved units for the shadows of the scratch units
	 *  if any amongst the app units.
	 */
		Safe_Reverse_Changes_on_ScratchUnits(lowAppSlotAddr, numLowAppSlots, lowShadowOffset, PROT_NONE);
		Safe_Reverse_Changes_on_ScratchUnits(appSlotAddr + (uint64_t)SLOT_SIZE, numHighAppSlots,
																		unitShadowOffset, PROT_NONE);
	} else {
	/* Copy the shadow data from the copies to the newly mapped shadow region */
		newUnitShadowAddr = (appSlotAddr << (uint64_t)SHADOW_SCALE) + offset;
		newLowShadowAddr = (lowAppSlotAddr << (uint64_t)SHADOW_SCALE) + offset;

	/* Set the protection to no acess and unmap reserved units for the shadows of the scratch units
	 *  if any amongst the app units.
	 */
		Safe_Reverse_Changes_on_ScratchUnits(lowAppSlotAddr, numLowAppSlots, offset, PROT_NONE);
		Safe_Reverse_Changes_on_ScratchUnits(appSlotAddr + (uint64_t)SLOT_SIZE,
														numHighAppSlots, offset, PROT_NONE);
	}

	Safe_Copy_Write_Skip_ScratchShadow(lowShadowCopyAddr, newLowShadowAddr, numLowShadowCopy);
	Safe_Copy_Write_Skip_ScratchShadow(unitShadowCopyAddr, newUnitShadowAddr, numUnitShadowCopy);

/* Unmap the mapped copies pf shadow data */
	Unmap_ShadowData_TemCopy(lowShadowCopyAddr, numLowShadowCopy);
	Unmap_ShadowData_TemCopy(unitShadowCopyAddr, numUnitShadowCopy);
}

void Manage_Scratch_EA__Case(uint64_t appSlotsBegAddr, uint64_t numAppSlots)
{
/* Possibilities considered: <Scratch>.<EA>.<?> */
	uint64_t appSlotAddr = appSlotsBegAddr + ((numAppSlots - 1) << (uint64_t)SLOT_SHIFT);
	uint64_t numLowAppSlots = NumAppSlots_VicinityLowAppUnits(appSlotsBegAddr);
	uint64_t numHighAppSlots = NumAppSlots_VicinityHighAppUnits(appSlotAddr + (uint64_t)SLOT_SIZE);
	uint64_t lowAppSlotAddr = appSlotsBegAddr - (numLowAppSlots << (uint64_t)SLOT_SHIFT);

/* 	Try mapping shadow using the offset for shadow of A unit */
	struct unitInfo *unitPtr = memLayoutTablePtr + (appSlotAddr >> (uint64_t)SLOT_SHIFT);
	if (!AttemptMapShadow(appSlotsBegAddr, numLowAppSlots + numAppSlots - 1, unitPtr->offset)) {
	/* Get copies of the shadow data for unit and high app units */
		uint64_t unitShadowCopyAddr = Unsafe_Get_ShadowData_TemCopy(appSlotAddr, numHighAppSlots + 1);
		uint64_t numUnitShadowCopy = (numHighAppSlots + 1) << (uint64_t)SHADOW_SCALE;
		uint64_t newUnitShadowAddr;

	/* Map shadow slots for the given app slots */
		int64_t offset =
				MmapShadowMemSlots(lowAppSlotAddr, numLowAppSlots + numAppSlots + numHighAppSlots);

	/* In case the application mapping failed and we are in the process of stack unwinding because of
	 * the possiblity of the application region being mapped recursively.
	 */
		if(offset == (int64_t)APP_MAPPING_FAILED) {
		/* Now we need to attempt to remap the shadows for aplication units whose
		 * shadows were unmapped. We treat those units as FIXED MAPPINGS since we
		 * do not have their info and there must be app pointers pointing to them already.
		 */
			appMappingInfoPtr->mapping_type = (int8_t)FIXED_MAPPING_USED;

		/* Now, we are ready to map the shadows */
			int64_t unitShadowOffset = MmapShadowMemSlots(appSlotAddr, numHighAppSlots + 1);

		/* Copy the shadow data from the temporary copies */
			newUnitShadowAddr = (appSlotAddr << (uint64_t)SHADOW_SCALE) + unitShadowOffset;
		} else {
		/* Copy the shadow data from the copies to the newly mapped shadow region */
			newUnitShadowAddr = (appSlotAddr << (uint64_t)SHADOW_SCALE) + offset;

		/* Set the protection to no acess and unmap reserved units for the shadows
		 * of the scratch units if any amongst the app units.
	     */
			Unsafe_Reverse_Changes_on_ScratchUnits(lowAppSlotAddr,
										numLowAppSlots, offset, PROT_NONE);
		}

	/* Copying the data from the previous shadow slots to the new ones and
	 * unmapping the copy.
	 */
		Unsafe_Copy_Write_Skip_ScratchShadow(unitShadowCopyAddr,
								newUnitShadowAddr, numUnitShadowCopy);

		Unmap_ShadowData_TemCopy(unitShadowCopyAddr, numUnitShadowCopy);
	} else {
	/* Change protection for scratch's shadow */
		Unsafe_Reverse_Changes_on_ScratchUnits(lowAppSlotAddr,
							numLowAppSlots, unitPtr->offset, PROT_NONE);
	}
}

void Manage_App_ES__Case(uint64_t appSlotsBegAddr, uint64_t numAppSlots)
{
/* Possibilities considered: <App>.<ES>.<?> */
	uint64_t highAppSlotAddr = appSlotsBegAddr + (numAppSlots << (uint64_t)SLOT_SHIFT);
	uint64_t numLowAppSlots = NumAppSlots_VicinityLowAppUnits(appSlotsBegAddr);
	uint64_t numHighAppSlots = NumAppSlots_VicinityHighAppUnits(highAppSlotAddr);
	uint64_t lowAppSlotAddr = appSlotsBegAddr - (numLowAppSlots << (uint64_t)SLOT_SHIFT);

	struct unitInfo *lowAppUnitPtr =
			memLayoutTablePtr + ((appSlotsBegAddr - (uint64_t)SLOT_SIZE) >> (uint64_t)SLOT_SHIFT);
	if (!AttemptMapShadow(appSlotsBegAddr, numAppSlots + numHighAppSlots, lowAppUnitPtr->offset)) {
	/* Get copies of the shadow data for unit and high app units */
		uint64_t lowShadowCopyAddr = Unsafe_Get_ShadowData_TemCopy(lowAppSlotAddr, numLowAppSlots);
		uint64_t numLowShadowCopy = numLowAppSlots << (uint64_t)SHADOW_SCALE;
		uint64_t newLowShadowAddr;

	/* Map shadow for given app slots */
		int64_t offset =
			MmapShadowMemSlots(lowAppSlotAddr, numLowAppSlots + numAppSlots + numHighAppSlots);

	/* In case the application mapping failed and we are in the process of stack
	 * unwinding because of the possiblity of the application region being mapped
	 * recursively.
	 */
		if(offset == (int64_t)APP_MAPPING_FAILED) {
		/* Now we need to attempt to remap the shadows for aplication units whose
		 * shadows were unmapped. We treat those units as FIXED MAPPINGS since we
		 * do not have their info and there must be app pointers pointing to them already.
		 */
			appMappingInfoPtr->mapping_type = (int8_t)FIXED_MAPPING_USED;

		/* Now, we are ready to map the shadows */
			int64_t lowShadowOffset = MmapShadowMemSlots(lowAppSlotAddr, numLowAppSlots);

		/* Copy the shadow data from the temporary copies */
			newLowShadowAddr = (lowAppSlotAddr << (uint64_t)SHADOW_SCALE) + lowShadowOffset;
		} else {
		/* Copy the shadow data from the copies to the newly mapped shadow region */
			newLowShadowAddr = (lowAppSlotAddr << (uint64_t)SHADOW_SCALE) + offset;

		/* Set the protection to no acess and unmap reserved units for the
		 * shadows of the scratch units if any amongst the app units.
		 */
			Unsafe_Reverse_Changes_on_ScratchUnits(highAppSlotAddr,
									numHighAppSlots, offset, PROT_NONE);
		}

	/* Copying the data from the previous shadow slots to the new ones and unmapping the copy */
		Unsafe_Copy_Write_Skip_ScratchShadow(lowShadowCopyAddr,
									newLowShadowAddr, numLowShadowCopy);

		Unmap_ShadowData_TemCopy(lowShadowCopyAddr, numLowShadowCopy);
	} else {
	/* Change protection for scratch's shadow  except for the scratch slot that
	 * overlaps with the app region.
	 */
		Unsafe_Reverse_Changes_on_ScratchUnits(highAppSlotAddr, numHighAppSlots,
												 lowAppUnitPtr->offset, PROT_NONE);
	}
}

void Manage_App_EA__SameOffsetsCase(uint64_t appSlotsBegAddr, uint64_t numAppSlots)
{
/* Possibilities considered:  <App>.<EA>.<?> when the A and App unit offsets are same */
	uint64_t appSlotAddr = appSlotsBegAddr + ((numAppSlots - 1) << (uint64_t)SLOT_SHIFT);
	struct unitInfo *unitPtr = memLayoutTablePtr + (appSlotAddr >> (uint64_t)SLOT_SHIFT);

/* Try mapping shadow using the offset for shadow of A unit */
	if (!AttemptMapShadow(appSlotsBegAddr, numAppSlots - 1, unitPtr->offset)) {
/* Now, we can simply use the Manage_App_EA__DifferentOffsetsCase() function
 * since the same offsets didn't work and the subsequent implementation is
 * oblivious of the relation between the offsets od A-unit and low app units.
 */
		Manage_App_EA__DifferentOffsetsCase(appSlotsBegAddr, numAppSlots);
	}
}

void Manage_Empty_EA__Case(uint64_t appSlotsBegAddr, uint64_t numAppSlots)
{
/* Possibilities considered: <Empty>.<EA>.<?> */
	uint64_t appSlotAddr = appSlotsBegAddr + ((numAppSlots - 1) << (uint64_t)SLOT_SHIFT);
	uint64_t numHighAppSlots =
			NumAppSlots_VicinityHighAppUnits(appSlotAddr + (uint64_t)SLOT_SIZE);
	struct unitInfo *unitPtr = memLayoutTablePtr + (appSlotAddr >> (uint64_t)SLOT_SHIFT);

/* Try mapping using the offset for A-unit */
	if (!AttemptMapShadow(appSlotsBegAddr, numAppSlots - 1, unitPtr->offset)) {
	/* Get copies of the shadow data for unit and high app units */
		uint64_t highShadowCopyAddr = Safe_Get_ShadowData_TemCopy(appSlotAddr, numHighAppSlots);
		uint64_t numHighShadowCopy = (numHighAppSlots + 1) << (uint64_t)SHADOW_SCALE;
		uint64_t newUnitShadowAddr;

	/* Map shadow for given app slots */
		int64_t offset = MmapShadowMemSlots(appSlotsBegAddr, numAppSlots + numHighAppSlots);

	/* In case the application mapping failed and we are in the process of stack
	 * unwinding because of the possiblity of the application region being mapped
	 * recursively.
	 */
		if(offset == (int64_t)APP_MAPPING_FAILED) {
		/* Now we need to attempt to remap the shadows for aplication units whose
		 * shadows were unmapped. We treat those units as FIXED MAPPINGS since we
		 * do not have their info and there must be app pointers pointing to them already.
		 */
			appMappingInfoPtr->mapping_type = (int8_t)FIXED_MAPPING_USED;

		/* Now, we are ready to map the shadows */
			int64_t unitShadowOffset = MmapShadowMemSlots(appSlotAddr, numHighAppSlots + 1);

		/* Copy the shadow data from the temporary copies */
			newUnitShadowAddr = (appSlotAddr << (uint64_t)SHADOW_SCALE) + unitShadowOffset;

		/* Set the protection to no acess and unmap reserved units for the
		 * shadows of the scratch units if any amongst the app units.
		 */
			Safe_Reverse_Changes_on_ScratchUnits(appSlotAddr + (uint64_t)SLOT_SIZE,
										numHighAppSlots, unitShadowOffset, PROT_NONE);
		} else {
		/* Copy the shadow data from the copies to the newly mapped shadow region */
			newUnitShadowAddr = (appSlotAddr << (uint64_t)SHADOW_SCALE) + offset;

		/* Set the protection to no acess and unmap reserved units for the
		 * shadows of the scratch units if any amongst the app units.
		 */
			Safe_Reverse_Changes_on_ScratchUnits(appSlotAddr + (uint64_t)SLOT_SIZE,
												numHighAppSlots, offset, PROT_NONE);
		}

	/* Copying the data from the previous shadow slots to the new ones
	 * and unmapping the copy.
	 */
		Safe_Copy_Write_Skip_ScratchShadow(highShadowCopyAddr,
							newUnitShadowAddr, numHighShadowCopy);

		Unmap_ShadowData_TemCopy(highShadowCopyAddr, numHighShadowCopy);
	}
}

void Manage_Empty_ES__Case(uint64_t appSlotsBegAddr, uint64_t numAppSlots)
{
/* Possibilities considered: <Empty>.<ES>.<?> */
	uint64_t highAppSlotAddr = appSlotsBegAddr + (numAppSlots << (uint64_t)SLOT_SHIFT);
	uint64_t numHighAppSlots = NumAppSlots_VicinityHighAppUnits(highAppSlotAddr);

/* Map shadow for given app slots */
	int64_t offset = MmapShadowMemSlots(appSlotsBegAddr, numAppSlots + numHighAppSlots);

/* In case the application mapping failed and we are in the process of stack
 * unwinding because of the possiblity of the application region being mapped
 * recursively.
 */
	if(offset != (int64_t)APP_MAPPING_FAILED) {
	/* Reverse the changes made on the higher scratch units */
		Unsafe_Reverse_Changes_on_ScratchUnits(highAppSlotAddr,
								numHighAppSlots, offset, PROT_NONE);
	}
}

void Manage_EA_MemLayout(uint64_t appSlotsBegAddr, uint64_t numAppSlots)
{
	Add_AppInfo_to_AppShadowInfoList(appSlotsBegAddr, numAppSlots - 1);
	Add_AppInfo_to_MemLayoutTable(appSlotsBegAddr, numAppSlots); /* App unit inclusive */

/* We need to see if there is any conflict in the offsets due to the
 * mapping of the app region. If there is, it must have been resolved
 * using the recursive algorithm, so we need to do nothing but simply quit.
 */
	if(AddInvalidOffsets(appSlotsBegAddr,
			numAppSlots - 1, APP_MAP) == (int8_t)CONFLICT_RESOLVED) {
		return;
	}

	MapRegReservedSlots(appSlotsBegAddr, numAppSlots - 1);
	uint64_t numLowAppSlots = NumAppSlots_VicinityLowAppUnits(appSlotsBegAddr);
	uint64_t appSlotAddr = appSlotsBegAddr + ((numAppSlots - 1) << (uint64_t)SLOT_SHIFT);
	struct unitInfo *unitPtr = memLayoutTablePtr + (appSlotAddr >> (uint64_t)SLOT_SHIFT);
	struct unitInfo *lowAppUnitPtr = memLayoutTablePtr
								+ ((appSlotsBegAddr - (uint64_t)SLOT_SIZE) >> (uint64_t)SLOT_SHIFT);

/* All Posibilities: <App>.<EA>.<?>, <Scratch>.<EA>.<?>, <App>.<ES>.<?>,
 * <Empty>.<EA>.<?>, <Empty>.<ES>.<?>.
 */
	if (numLowAppSlots) {
	/* Possibilities considered: <App>.<EA>.<?>, <Scratch>.<EA>.<?>, <App>.<ES>.<?> */
		if (unitPtr->offset != lowAppUnitPtr->offset) {
		/* Possibilities considered: <App>.<EA>.<?>, <Scratch>.<EA>.<?>, <App>.<ES>.<?> */
			if (unitPtr->offset != (int64_t) SCRATCH_UNIT_OFFSET) {
			/* Possibilities considered: <App>.<EA>.<?>, <Scratch>.<EA>.<?> */
				//printf("E...EA high and low slots have different non-scratch offsets\n");
				if (lowAppUnitPtr->offset != (int64_t) SCRATCH_UNIT_OFFSET) {
				/* Possibilities considered:  <App>.<EA>.<?>  in which the offsets are different */
					Manage_App_EA__DifferentOffsetsCase(appSlotsBegAddr, numAppSlots);
				} else {
				/* Possibilities considered: <Scratch>.<EA>.<?> */
					Manage_Scratch_EA__Case(appSlotsBegAddr, numAppSlots);
				}
			} else {
			/* Possibilities considered: <App>.<ES>.<?> */
				Manage_App_ES__Case(appSlotsBegAddr, numAppSlots);
			}
		} else {
		/* Possibilities considered: <App>.<EA>.<?> in which the offsets are the same */
			Manage_App_EA__SameOffsetsCase(appSlotsBegAddr, numAppSlots);
		}
	} else {
	/* Possibilities considered: <Empty>.<EA>.<?>, <Empty>.<ES>.<?> */
		if (unitPtr->offset != (int64_t) SCRATCH_UNIT_OFFSET) {
		/* Possibilities considered: <Empty>.<EA>.<?> */
			Manage_Empty_EA__Case(appSlotsBegAddr, numAppSlots);
		} else {
		/* Possibilities considered: <Empty>.<ES>.<?> */
			Manage_Empty_ES__Case(appSlotsBegAddr, numAppSlots);
		}
	}
}

void Manage_App_E_App_DifferentOffsetsCase(uint64_t appSlotsBegAddr, uint64_t numAppSlots)
{
/* Possibilities considered: <App1>.<E>.<App2> with the app units having different offsets */
	uint64_t highAppSlotAddr = appSlotsBegAddr + (numAppSlots << (uint64_t)SLOT_SHIFT);
	uint64_t numLowAppSlots = NumAppSlots_VicinityLowAppUnits(appSlotsBegAddr);
	uint64_t numHighAppSlots = NumAppSlots_VicinityHighAppUnits(highAppSlotAddr);
	uint64_t lowAppSlotAddr = appSlotsBegAddr - (numLowAppSlots << (uint64_t)SLOT_SHIFT);

/* Get copies of the shadow data for low app units; and unit and high app units */
	uint64_t lowShadowCopyAddr = Safe_Get_ShadowData_TemCopy(lowAppSlotAddr, numLowAppSlots);
	uint64_t highShadowCopyAddr = Safe_Get_ShadowData_TemCopy(highAppSlotAddr, numHighAppSlots);
	uint64_t numLowShadowCopy = numLowAppSlots << (uint64_t)SHADOW_SCALE;
	uint64_t numHighShadowCopy = numHighAppSlots << (uint64_t)SHADOW_SCALE;
	uint64_t newLowShadowAddr;
	uint64_t newHighShadowAddr;

/* Map the new shadow region for the entire range of addresses */
	int64_t offset = MmapShadowMemSlots(lowAppSlotAddr,
								numAppSlots + numLowAppSlots + numHighAppSlots);

/* In case the application mapping failed and we are in the process of stack
 * unwinding because of the possiblity of the application region being mapped
 * recursively.
 */
	if(offset == (int64_t)APP_MAPPING_FAILED) {
	/* Now we need to attempt to remap the shadows for aplication units whose
	 * shadows were unmapped. We treat those units as FIXED MAPPINGS since we
	 * do not have their info and there must be app pointers pointing to them already.
	 */
		appMappingInfoPtr->mapping_type = (int8_t)FIXED_MAPPING_USED;

	/* Now, we are ready to map the shadows */
		int64_t lowShadowOffset = MmapShadowMemSlots(lowAppSlotAddr, numLowAppSlots);
		int64_t highShadowOffset = MmapShadowMemSlots(highAppSlotAddr, numHighAppSlots);

	/* Copy the shadow data from the temporary copies */
		newLowShadowAddr = (lowAppSlotAddr << (uint64_t)SHADOW_SCALE) + lowShadowOffset;
		newHighShadowAddr = (highAppSlotAddr << (uint64_t)SHADOW_SCALE) + highShadowOffset;

	/* Set the protection to no acess and unmap reserved units for the
	 * shadows of the scratch units if any amongst the app units.
	 */
		Safe_Reverse_Changes_on_ScratchUnits(lowAppSlotAddr,
							numLowAppSlots, lowShadowOffset, PROT_NONE);
		Safe_Reverse_Changes_on_ScratchUnits(highAppSlotAddr,
								numHighAppSlots, highShadowOffset, PROT_NONE);
	} else {
	/* Copy the shadow data from the copies to the newly mapped shadow region */
		newHighShadowAddr = (highAppSlotAddr << (uint64_t)SHADOW_SCALE) + offset;
		newLowShadowAddr = (lowAppSlotAddr << (uint64_t)SHADOW_SCALE) + offset;

	/* Set the protection to no acess and unmap reserved units for the
	 * shadows of the scratch units if any amongst the app units.
	 */
		Safe_Reverse_Changes_on_ScratchUnits(lowAppSlotAddr,
									numLowAppSlots, offset, PROT_NONE);
		Safe_Reverse_Changes_on_ScratchUnits(highAppSlotAddr,
									numHighAppSlots, offset, PROT_NONE);
	}

/* Copy the shadow data from the copies to the newly mapped shadow region */
	Safe_Copy_Write_Skip_ScratchShadow(lowShadowCopyAddr,
										newLowShadowAddr, numLowShadowCopy);
	Safe_Copy_Write_Skip_ScratchShadow(highShadowCopyAddr,
										newHighShadowAddr, numHighShadowCopy);

/* Unmap the mapped copies of shadow data */
	Unmap_ShadowData_TemCopy(lowShadowCopyAddr, numLowShadowCopy);
	Unmap_ShadowData_TemCopy(highShadowCopyAddr, numHighShadowCopy);
}

void Manage_App_E_Scratch_Case(uint64_t appSlotsBegAddr, uint64_t numAppSlots)
{
/* Possibilities considered: <App>.<E>.<Scratch> */
	uint64_t highSlotsAddr = appSlotsBegAddr + (numAppSlots << (uint64_t)SLOT_SHIFT);
	uint64_t numLowAppSlots = NumAppSlots_VicinityLowAppUnits(appSlotsBegAddr);
	uint64_t numHighAppSlots = NumAppSlots_VicinityHighAppUnits(highSlotsAddr);

/* Mapping using the low app unit's offset for its shadow */
	struct unitInfo *lowAppUnitPtr =
			memLayoutTablePtr + ((appSlotsBegAddr - (uint64_t)SLOT_SIZE) >> (uint64_t)SLOT_SHIFT);
	if (!AttemptMapShadow(appSlotsBegAddr, numAppSlots + numHighAppSlots, lowAppUnitPtr->offset)) {
	/* Get copies of the shadow data for unit and high app units */
		uint64_t lowAppSlotAddr = appSlotsBegAddr - (numLowAppSlots << (uint64_t)SLOT_SHIFT);
		uint64_t lowShadowCopyAddr = Unsafe_Get_ShadowData_TemCopy(lowAppSlotAddr, numLowAppSlots);
		uint64_t numLowShadowCopy = numLowAppSlots << (uint64_t)SHADOW_SCALE;
		uint64_t newLowShadowAddr;

	/* Map the new shadow region for the entire range of addresses */
		int64_t offset = MmapShadowMemSlots(appSlotsBegAddr - (numLowAppSlots << (uint64_t)SLOT_SHIFT),
												numAppSlots + numLowAppSlots + numHighAppSlots);
	/* In case the application mapping failed and we are in the process of
	 * stack unwinding because of the possiblity of the application region
	 * being mapped recursively.
	 */
		if(offset == (int64_t)APP_MAPPING_FAILED) {
		/* Now we need to attempt to remap the shadows for aplication units
		 * whose shadows were unmapped. We treat those units as FIXED MAPPINGS
		 * since we do not have their info and there must be app pointers pointing
		 * to them already.
		 */
			appMappingInfoPtr->mapping_type = (int8_t)FIXED_MAPPING_USED;

		/* Now, we are ready to map the shadows */
			int64_t lowShadowOffset = MmapShadowMemSlots(lowAppSlotAddr, numLowAppSlots);

		/* Copy the shadow data from the temporary copies */
			newLowShadowAddr = (lowAppSlotAddr << (uint64_t)SHADOW_SCALE) + lowShadowOffset;
		} else {
		/* Copy the shadow data from the copies to the newly mapped shadow region */
			uint64_t newHighShadowAddr = (highSlotsAddr << (uint64_t)SHADOW_SCALE) + offset;
			newLowShadowAddr = (lowAppSlotAddr << (uint64_t)SHADOW_SCALE) + offset;

		/* Set the protection to no acess and unmap reserved units for the shadows of the scratch units
		 *  if any amongst the app units.
		 */
			Unsafe_Reverse_Changes_on_ScratchUnits(highSlotsAddr, numHighAppSlots, offset, PROT_NONE);
		}

	/* Copy the shadow data from the copies to the newly mapped shadow region */
		Safe_Copy_Write_Skip_ScratchShadow(lowShadowCopyAddr, newLowShadowAddr, numLowShadowCopy);

	/* Unmap the mapped copies pf shadow data */
		Unmap_ShadowData_TemCopy(lowShadowCopyAddr, numLowShadowCopy);
	} else {
	/* Reverting changes on the scartch space */
		 Unsafe_Reverse_Changes_on_ScratchUnits(highSlotsAddr, numHighAppSlots,
				 	 	 	 	 	 	 	 	 	 	lowAppUnitPtr->offset, PROT_NONE);
	}
}

void Manage_Scratch_E_App_Case(uint64_t appSlotsBegAddr, uint64_t numAppSlots)
{
/* Possibilities considered: <Scratch>.<E>.<App> */
	uint64_t highAppSlotAddr = appSlotsBegAddr + (numAppSlots << (uint64_t)SLOT_SHIFT);
	uint64_t numLowAppSlots = NumAppSlots_VicinityLowAppUnits(appSlotsBegAddr);
	uint64_t numHighAppSlots = NumAppSlots_VicinityHighAppUnits(highAppSlotAddr);
	uint64_t lowAppSlotAddr = appSlotsBegAddr - (numLowAppSlots << (uint64_t)SLOT_SHIFT);

	/* Mapping using the high app unit's offset for its shadow */
	struct unitInfo *highAppUnitPtr =
			memLayoutTablePtr + (appSlotsBegAddr >> (uint64_t)SLOT_SHIFT) + numAppSlots;
	if (!AttemptMapShadow(lowAppSlotAddr,
				numAppSlots + numLowAppSlots, highAppUnitPtr->offset)) {
	/* Get copies of the shadow data for unit and high app units */
		uint64_t highShadowCopyAddr =
				Unsafe_Get_ShadowData_TemCopy(highAppSlotAddr, numHighAppSlots);
		uint64_t numHighShadowCopy = numHighAppSlots << (uint64_t)SHADOW_SCALE;
		uint64_t newHighShadowAddr;

	/* Map the new shadow region for the entire range of addresses */
		int64_t offset = MmapShadowMemSlots(lowAppSlotAddr,
							numAppSlots + numLowAppSlots + numHighAppSlots);

	/* In case the application mapping failed and we are in the process of
	 * stack unwinding because of the possiblity of the application region
	 * being mapped recursively.
	 */
		if(offset == (int64_t)APP_MAPPING_FAILED) {
		/* Now we need to attempt to remap the shadows for aplication units
		 * whose shadows were unmapped. We treat those units as FIXED MAPPINGS
		 * since we do not have their info and there must be app pointers pointing
		 * to them already.
		 */
			appMappingInfoPtr->mapping_type = (int8_t)FIXED_MAPPING_USED;

		/* Now, we are ready to map the shadows */
			int64_t highShadowOffset = MmapShadowMemSlots(highAppSlotAddr, numHighAppSlots);

		/* Copy the shadow data from the temporary copies */
			newHighShadowAddr = (highAppSlotAddr << (uint64_t)SHADOW_SCALE) + highShadowOffset;
		} else {
		/* Copy the shadow data from the copies to the newly mapped shadow region */
			newHighShadowAddr = (highAppSlotAddr << (uint64_t)SHADOW_SCALE) + offset;
			uint64_t newLowShadowAddr = (lowAppSlotAddr << (uint64_t)SHADOW_SCALE) + offset;

		/* Set the protection to no acess and unmap reserved units for the
		 * shadows of the scratch units if any amongst the app units.
		 */
			Unsafe_Reverse_Changes_on_ScratchUnits(lowAppSlotAddr,
										numLowAppSlots, offset, PROT_NONE);
		}

	/* Copy the shadow data from the copies to the newly mapped shadow region */
		Unsafe_Copy_Write_Skip_ScratchShadow(highShadowCopyAddr,
									newHighShadowAddr, numHighShadowCopy);

	/* Unmap the mapped copies pf shadow data */
		Unmap_ShadowData_TemCopy(highShadowCopyAddr, numHighShadowCopy);
	} else {
	/* Reversing changes on the scartch space */
		Unsafe_Reverse_Changes_on_ScratchUnits(lowAppSlotAddr, numLowAppSlots,
														highAppUnitPtr->offset, PROT_NONE);
	}
}

void Manage_App_E_App_SameOffsetsCase(uint64_t appSlotsBegAddr, uint64_t numAppSlots)
{
/* Possibilities considered: <App1>.<E>.<App2> with the app units having the same offset */
	struct unitInfo *lowAppUnitPtr =
			memLayoutTablePtr + ((appSlotsBegAddr - (uint64_t)SLOT_SIZE) >> (uint64_t)SLOT_SHIFT);

/* Try mapping using the existing same offsets of the app units */
	if (!AttemptMapShadow(appSlotsBegAddr, numAppSlots, lowAppUnitPtr->offset)) {
	/* Since the attemppt to use he app units's offset failed, we don't have to worry about
	 * the relation betweeen the offsets of the app units.
	 */
		Manage_App_E_App_DifferentOffsetsCase(appSlotsBegAddr, numAppSlots);
	}
}

void Manage_App_E_Empty_Case(uint64_t appSlotsBegAddr, uint64_t numAppSlots)
{
/* Possibilities considered: <App>.<E>.<Empty> */
	uint64_t numLowAppSlots = NumAppSlots_VicinityLowAppUnits(appSlotsBegAddr);
	struct unitInfo *lowAppUnitPtr =
			memLayoutTablePtr + ((appSlotsBegAddr - (uint64_t)SLOT_SIZE) >> (uint64_t)SLOT_SHIFT);

/* Try mapping using the offset for the app unit */
	if (!AttemptMapShadow(appSlotsBegAddr, numAppSlots, lowAppUnitPtr->offset)) {
	/* Get copies of the shadow data for unit and high app units */
		uint64_t lowShadowCopyAddr = Safe_Get_ShadowData_TemCopy(
				appSlotsBegAddr - (numLowAppSlots << (uint64_t)SLOT_SHIFT), numLowAppSlots);
		uint64_t numLowShadowCopy = numLowAppSlots << (uint64_t)SHADOW_SCALE;
		uint64_t lowAppSlotAddr = appSlotsBegAddr - (numLowAppSlots << (uint64_t)SLOT_SHIFT);
		uint64_t newLowShadowAddr;

	/* Map the entire address range */
		int64_t offset = MmapShadowMemSlots(lowAppSlotAddr, numAppSlots + numLowAppSlots);

	/* In case the application mapping failed and we are in the process of
	 * stack unwinding because of the possiblity of the application region
	 * being mapped recursively.
	 */
		if(offset == (int64_t)APP_MAPPING_FAILED) {
		/* Now we need to attempt to remap the shadows for aplication units
		 * whose shadows were unmapped. We treat those units as FIXED MAPPINGS
		 * since we do not have their info and there must be app pointers pointing
		 * to them already.
		 */
			appMappingInfoPtr->mapping_type = (int8_t)FIXED_MAPPING_USED;

		/* Now, we are ready to map the shadows */
			int64_t lowShadowOffset = MmapShadowMemSlots(lowAppSlotAddr, numLowAppSlots);

		/* Copy the shadow data from the temporary copies */
			newLowShadowAddr = (lowAppSlotAddr << (uint64_t)SHADOW_SCALE) + lowShadowOffset;

		/* Set the protection to no acess and unmap reserved units for
		 * the shadows of the scratch units if any amongst the app units.
		 */
			Safe_Reverse_Changes_on_ScratchUnits(lowAppSlotAddr,
							numLowAppSlots, lowShadowOffset, PROT_NONE);
		} else {
		/* Copy the shadow data from the copies to the newly mapped shadow region */
			newLowShadowAddr = (lowAppSlotAddr << (uint64_t)SHADOW_SCALE) + offset;

		/* Set the protection to no acess and unmap reserved units for the
		 * shadows of the scratch units if any amongst the app units.
		 */
			Safe_Reverse_Changes_on_ScratchUnits(lowAppSlotAddr,
										numLowAppSlots, offset, PROT_NONE);
		}

	/* Copy the shadow data from the copies to the newly mapped shadow region */
		Safe_Copy_Write_Skip_ScratchShadow(lowShadowCopyAddr,
										newLowShadowAddr, numLowShadowCopy);

	/* Unmap the mapped copies pf shadow data */
		Unmap_ShadowData_TemCopy(lowShadowCopyAddr, numLowShadowCopy);
	}
}

void Manage_Scratch_E_Empty_Case(uint64_t appSlotsBegAddr, uint64_t numAppSlots)
{
/* Possibilities considered: <Scratch>.<E>.<Empty> */
	uint64_t numLowAppSlots = NumAppSlots_VicinityLowAppUnits(appSlotsBegAddr);
	uint64_t lowAppSlotAddr = appSlotsBegAddr - (numLowAppSlots << (uint64_t)SLOT_SHIFT);

	int64_t offset = MmapShadowMemSlots(lowAppSlotAddr, numAppSlots + numLowAppSlots);

/* In case the application mapping failed and we are in the process of
 * stack unwinding because of the possiblity of the application region
 * being mapped recursively.
 */
	if(offset != (int64_t)APP_MAPPING_FAILED) {
	/* Copy the shadow data from the copies to the newly mapped shadow region */
		uint64_t newLowShadowAddr = (lowAppSlotAddr << (uint64_t)SHADOW_SCALE) + offset;

	/* Set the protection to no acess and unmap reserved units for
	 * the shadows of the scratch units if any amongst the app units.
	 */
		Safe_Reverse_Changes_on_ScratchUnits(lowAppSlotAddr,
								numLowAppSlots, offset, PROT_NONE);
	}
}

void Manage_Empty_E_App_Case(uint64_t appSlotsBegAddr, uint64_t numAppSlots)
{
/* Possibilities considered: <Empty>.<E>.<App> */
	uint64_t highAppSlotAddr = appSlotsBegAddr + (numAppSlots << (uint64_t)SLOT_SHIFT);
	uint64_t numHighAppSlots = NumAppSlots_VicinityHighAppUnits(highAppSlotAddr);

/* Try mapping using the offset for the app unit */
	struct unitInfo *highAppUnitPtr =
			memLayoutTablePtr + (appSlotsBegAddr >> (uint64_t)SLOT_SHIFT) + numAppSlots;
	if (!AttemptMapShadow(appSlotsBegAddr, numAppSlots, highAppUnitPtr->offset)) {
	/* Get copies of the shadow data for unit and high app units */
		uint64_t highShadowCopyAddr =
				Safe_Get_ShadowData_TemCopy(highAppSlotAddr, numHighAppSlots);
		uint64_t numHighShadowCopy = numHighAppSlots << (uint64_t)SHADOW_SCALE;
		uint64_t newHighShadowAddr;

	/* Map the entire address range */
		int64_t offset = MmapShadowMemSlots(appSlotsBegAddr, numAppSlots + numHighAppSlots);

	/* In case the application mapping failed and we are in the process of
	 * stack unwinding because of the possiblity of the application region
	 * being mapped recursively.
	 */
		if(offset == (int64_t)APP_MAPPING_FAILED) {
		/* Now we need to attempt to remap the shadows for aplication units
		 * whose shadows were unmapped. We treat those units as FIXED MAPPINGS
		 * since we do not have their info and there must be app pointers pointing
		 * to them already.
		 */
			appMappingInfoPtr->mapping_type = (int8_t)FIXED_MAPPING_USED;

		/* Now, we are ready to map the shadows */
			int64_t highShadowOffset = MmapShadowMemSlots(highAppSlotAddr, numHighAppSlots);

		/* Copy the shadow data from the temporary copies */
			newHighShadowAddr = (highAppSlotAddr << (uint64_t)SHADOW_SCALE) + highShadowOffset;

		/* Set the protection to no acess and unmap reserved units for the
		 * shadows of the scratch units if any amongst the app units.
		 */
			Safe_Reverse_Changes_on_ScratchUnits(highAppSlotAddr,
							numHighAppSlots, highShadowOffset, PROT_NONE);
		} else {
		/* Copy the shadow data from the copies to the newly mapped shadow region */
			newHighShadowAddr = (highAppSlotAddr << (uint64_t)SHADOW_SCALE) + offset;

		/* Set the protection to no acess and unmap reserved units for
		 * the shadows of the scratch units if any amongst the app units.
		 */
			Safe_Reverse_Changes_on_ScratchUnits(highAppSlotAddr,
									numHighAppSlots, offset, PROT_NONE);
		}

	/* Copy the shadow data from the copies to the newly mapped shadow region */
		Safe_Copy_Write_Skip_ScratchShadow(highShadowCopyAddr,
								newHighShadowAddr, numHighShadowCopy);

	/* Unmap the mapped copies pf shadow data */
		Unmap_ShadowData_TemCopy(highShadowCopyAddr, numHighShadowCopy);
	}
}

void Manage_Empty_E_Scratch_Case(uint64_t appSlotsBegAddr, uint64_t numAppSlots)
{
/* Possibilities considered: <Empty>.<E>.<Scratch> */
	uint64_t highAppSlotAddr = appSlotsBegAddr + (numAppSlots << (uint64_t)SLOT_SHIFT);
	uint64_t numHighAppSlots = NumAppSlots_VicinityHighAppUnits(highAppSlotAddr);

	int64_t offset = MmapShadowMemSlots(appSlotsBegAddr, numAppSlots + numHighAppSlots);

/* In case the application mapping failed and we are in the process of
 * stack unwinding because of the possiblity of the application region
 * being mapped recursively.
 */
	if(offset != (int64_t)APP_MAPPING_FAILED) {
	/* Copy the shadow data from the copies to the newly mapped shadow region */
		uint64_t newHighShadowAddr = (highAppSlotAddr << (uint64_t)SHADOW_SCALE) + offset;

	/* Set the protection to no acess and unmap reserved units for
	 * the shadows of the scratch units if any amongst the app units.
	 */
		Unsafe_Reverse_Changes_on_ScratchUnits(highAppSlotAddr,
								numHighAppSlots, offset, PROT_NONE);
	}
}

void Manage_Empty_E_Empty_Case(uint64_t appSlotsBegAddr, uint64_t numAppSlots)
{
/* Possibilities considered: <Empty>.<E>.<Empty> */
	MmapShadowMemSlots(appSlotsBegAddr, numAppSlots);
}

void Manage_E_MemLayout(uint64_t appSlotsBegAddr, uint64_t numAppSlots)
{
	Add_AppInfo_to_AppShadowInfoList(appSlotsBegAddr, numAppSlots);
	Add_AppInfo_to_MemLayoutTable(appSlotsBegAddr, numAppSlots); /* App unit inclusive */

/* We need to see if there is any conflict in the offsets due to the mapping of the
 * app region. If there is, it must have been resolved using the recursive algorithm,
 * so we need to do nothing but simply quit.
 */
	if(AddInvalidOffsets(appSlotsBegAddr,
			numAppSlots, APP_MAP) == (int8_t)CONFLICT_RESOLVED) {
		return;
	}

	MapRegReservedSlots(appSlotsBegAddr, numAppSlots);
	uint64_t numLowAppSlots = NumAppSlots_VicinityLowAppUnits(appSlotsBegAddr);
	uint64_t numHighAppSlots =
			NumAppSlots_VicinityHighAppUnits(appSlotsBegAddr + (numAppSlots << (uint64_t)SLOT_SHIFT));
	struct unitInfo *lowAppUnitPtr = memLayoutTablePtr
									+ ((appSlotsBegAddr - (uint64_t)SLOT_SIZE) >> (uint64_t)SLOT_SHIFT);
	struct unitInfo *highAppUnitPtr = memLayoutTablePtr
								+ (appSlotsBegAddr >> (uint64_t)SLOT_SHIFT) + numAppSlots;

/* Possibilities: <App1>.<E>.<App2> , <App>.<E>.<Scratch>, <Scratch>.<E>.<App>,
 *  <Scratch>.<E>.<Empty>, <App>.<E>.<Empty>, <Empty>.<E>.<Scratch>,
 *  <Empty>.<E>.<App>, <Empty>.<E>.<Empty>
*/
	if (numLowAppSlots) {
	/* Possibilities considered: <App1>.<E>.<App2> , <App>.<E>.<Scratch>, <Scratch>.<E>.<App>,
	 * <Scratch>.<E>.<Empty>, <App>.<E>.<Empty>
	 */
		if (numHighAppSlots) {
		/* Possibilities considered: <App1>.<E>.<App2> , <App>.<E>.<Scratch>, <Scratch>.<E>.<App> */
			if (lowAppUnitPtr->offset != highAppUnitPtr->offset) {
			/* Possibilities considered: <App1>.<E>.<App2> , <App>.<E>.<Scratch>, <Scratch>.<E>.<App> */
				if (lowAppUnitPtr->offset != (int64_t) SCRATCH_UNIT_OFFSET) {
				/* Possibilities considered: <App1>.<E>.<App2> , <App>.<E>.<Scratch> */
					if (highAppUnitPtr->offset != (int64_t) SCRATCH_UNIT_OFFSET) {
					/* Possibilities considered: <App1>.<E>.<App2> */
						Manage_App_E_App_DifferentOffsetsCase(appSlotsBegAddr,
								numAppSlots);
					} else {
					/* Possibilities considered: <App>.<E>.<Scratch> */
						Manage_App_E_Scratch_Case(appSlotsBegAddr, numAppSlots);
					}
				} else {
				/* Possibilities considered: <Scratch>.<E>.<App> */
					Manage_Scratch_E_App_Case(appSlotsBegAddr, numAppSlots);
				}
			} else {
			/* Possibilities considered: <App1>.<E>.<App2> */
				Manage_App_E_App_SameOffsetsCase(appSlotsBegAddr, numAppSlots);
			}
		} else {
		/* Possibilities considered:  <Scratch>.<E>.<Empty>, <App>.<E>.<Empty> */
			if (lowAppUnitPtr->offset != (int64_t) SCRATCH_UNIT_OFFSET) {
			/* Possibilities considered: <App>.<E>.<Empty> */
				Manage_App_E_Empty_Case(appSlotsBegAddr, numAppSlots);
			} else {
			/* Possibilities considered:  <Scratch>.<E>.<Empty> */
				Manage_Scratch_E_Empty_Case(appSlotsBegAddr, numAppSlots);
			}
		}
	} else {
		/* Possibilities considered: <Empty>.<E>.<Scratch>, <Empty>.<E>.<App>, <Empty>.<E>.<Empty> */
		if (numHighAppSlots) {
		/* 	Possibilities considered: <Empty>.<E>.<Scratch>, <Empty>.<E>.<App> */
			if (highAppUnitPtr->offset != (int64_t) SCRATCH_UNIT_OFFSET) {
			/* 	Possibilities considered: <Empty>.<E>.<App> */
				Manage_Empty_E_App_Case(appSlotsBegAddr, numAppSlots);
			} else {
			/* 	Possibilities considered: <Empty>.<E>.<Scratch> */
				Manage_Empty_E_Scratch_Case(appSlotsBegAddr, numAppSlots);
			}
		} else {
		/* Possibilities considered: <Empty>.<E>.<Empty> */
			Manage_Empty_E_Empty_Case(appSlotsBegAddr, numAppSlots);
		}
	}
}

void Manage__AE_App_DifferentOffsetsCase(uint64_t appSlotsBegAddr, uint64_t numAppSlots)
{
/* Possibilities considered: <?>.<AE>.<App> with different offsets */
	uint64_t highAppSlotAddr = appSlotsBegAddr + (numAppSlots << (uint64_t)SLOT_SHIFT);
	uint64_t numLowAppSlots = NumAppSlots_VicinityLowAppUnits(appSlotsBegAddr);
	uint64_t numHighAppSlots = NumAppSlots_VicinityHighAppUnits(highAppSlotAddr);
	uint64_t lowAppSlotAddr = appSlotsBegAddr - (numLowAppSlots << (uint64_t)SLOT_SHIFT);

/* Get copies of the shadow data for low app units; and unit and high app units */
	uint64_t lowShadowCopyAddr = Safe_Get_ShadowData_TemCopy(lowAppSlotAddr, numLowAppSlots + 1);
	uint64_t highShadowCopyAddr = Safe_Get_ShadowData_TemCopy(highAppSlotAddr, numHighAppSlots);
	uint64_t numLowShadowCopy = (numLowAppSlots + 1) << (uint64_t)SHADOW_SCALE;
	uint64_t numHighShadowCopy = numHighAppSlots << (uint64_t)SHADOW_SCALE;
	uint64_t newLowShadowAddr;
	uint64_t newHighShadowAddr;

/* Map the new shadow region for the entire range of addresses */
	int64_t offset = MmapShadowMemSlots(lowAppSlotAddr,
					numAppSlots + numLowAppSlots + numHighAppSlots);

/* In case the application mapping failed and we are in the process of
 * stack unwinding because of the possiblity of the application region
 * being mapped recursively.
 */
	if(offset == (int64_t)APP_MAPPING_FAILED) {
	/* Now we need to attempt to remap the shadows for aplication units
	 * whose shadows were unmapped. We treat those units as FIXED MAPPINGS
	 * since we do not have their info and there must be app pointers pointing
	 * to them already.
	 */
		appMappingInfoPtr->mapping_type = (int8_t)FIXED_MAPPING_USED;

	/* Now, we are ready to map the shadows */
		int64_t lowShadowOffset = MmapShadowMemSlots(lowAppSlotAddr, numLowAppSlots + 1);
		int64_t highShadowOffset = MmapShadowMemSlots(highAppSlotAddr, numHighAppSlots);

	/* Copy the shadow data from the temporary copies */
		newLowShadowAddr = (lowAppSlotAddr << (uint64_t)SHADOW_SCALE) + lowShadowOffset;
		newHighShadowAddr = (highAppSlotAddr << (uint64_t)SHADOW_SCALE) + highShadowOffset;

	/* Set the protection to no acess and unmap reserved units for
	 * the shadows of the scratch units if any amongst the app units.
	 */
		Safe_Reverse_Changes_on_ScratchUnits(lowAppSlotAddr,
					numLowAppSlots + 1, lowShadowOffset, PROT_NONE);
		Safe_Reverse_Changes_on_ScratchUnits(highAppSlotAddr,
					numHighAppSlots, highShadowOffset, PROT_NONE);
	} else {
	/* Copy the shadow data from the copies to the newly mapped shadow region */
		newHighShadowAddr = (highAppSlotAddr << (uint64_t)SHADOW_SCALE) + offset;
		newLowShadowAddr = (lowAppSlotAddr << (uint64_t)SHADOW_SCALE) + offset;

	/* Set the protection to no acess and unmap reserved units for the shadows of the scratch units
	 *  if any amongst the app units.
	 */
		Safe_Reverse_Changes_on_ScratchUnits(lowAppSlotAddr, numLowAppSlots, offset, PROT_NONE);
		Safe_Reverse_Changes_on_ScratchUnits(highAppSlotAddr, numHighAppSlots, offset, PROT_NONE);
	}

/* Copy the shadow data from the copies to the newly mapped shadow region */
	Safe_Copy_Write_Skip_ScratchShadow(lowShadowCopyAddr, newLowShadowAddr, numLowShadowCopy);
	Safe_Copy_Write_Skip_ScratchShadow(highShadowCopyAddr, newHighShadowAddr, numHighShadowCopy);

/* Unmap the mapped copies pf shadow data */
	Unmap_ShadowData_TemCopy(highShadowCopyAddr, numHighShadowCopy);
	Unmap_ShadowData_TemCopy(lowShadowCopyAddr, numLowShadowCopy);
}

void Manage__AE_Scratch_Case(uint64_t appSlotsBegAddr, uint64_t numAppSlots)
{
/* Possibilities considered: <?>.<AE>.<Scratch> */
	uint64_t highAppSlotAddr = appSlotsBegAddr + (numAppSlots << (uint64_t)SLOT_SHIFT);
	uint64_t numLowAppSlots = NumAppSlots_VicinityLowAppUnits(appSlotsBegAddr);
	uint64_t numHighAppSlots = NumAppSlots_VicinityHighAppUnits(highAppSlotAddr);
	uint64_t lowAppSlotAddr = appSlotsBegAddr - (numLowAppSlots << (uint64_t)SLOT_SHIFT);

/* Use the offset of the A unit to map the shadow */
	struct unitInfo *unitPtr = memLayoutTablePtr + (appSlotsBegAddr >> (uint64_t)SLOT_SHIFT);
	if (!AttemptMapShadow(appSlotsBegAddr + (uint64_t)SLOT_SIZE,
								numAppSlots + numHighAppSlots - 1, unitPtr->offset)) {
	/* Get copies of the shadow data for low app units */
		uint64_t lowShadowCopyAddr = Unsafe_Get_ShadowData_TemCopy(lowAppSlotAddr, numLowAppSlots + 1);
		uint64_t numLowShadowCopy = (numLowAppSlots + 1) << (uint64_t)SHADOW_SCALE;
		uint64_t newLowShadowAddr;

	/* Map the new shadow region for the entire range of addresses */
		int64_t offset = MmapShadowMemSlots(lowAppSlotAddr,
						numAppSlots + numLowAppSlots + numHighAppSlots);

	/* In case the application mapping failed and we are in the process of
	 * stack unwinding because of the possiblity of the application region
	 * being mapped recursively.
	 */
		if(offset == (int64_t)APP_MAPPING_FAILED) {
		/* Now we need to attempt to remap the shadows for aplication units
		 * whose shadows were unmapped. We treat those units as FIXED MAPPINGS
		 * since we do not have their info and there must be app pointers pointing
		 * to them already.
		 */
			appMappingInfoPtr->mapping_type = (int8_t)FIXED_MAPPING_USED;

		/* Now, we are ready to map the shadows */
			int64_t lowShadowOffset = MmapShadowMemSlots(lowAppSlotAddr, numLowAppSlots + 1);
			int64_t highShadowOffset = MmapShadowMemSlots(highAppSlotAddr, numHighAppSlots);

		/* Copy the shadow data from the temporary copies */
			newLowShadowAddr = (lowAppSlotAddr << (uint64_t)SHADOW_SCALE) + lowShadowOffset;
		} else {
		/* Copy the shadow data from the copies to the newly mapped shadow region */
			uint64_t newHighShadowAddr = (highAppSlotAddr << (uint64_t)SHADOW_SCALE) + offset;
			newLowShadowAddr = (lowAppSlotAddr << (uint64_t)SHADOW_SCALE) + offset;

		/* Set the protection to no acess and unmap reserved units for
		 * the shadows of the scratch units if any amongst the app units.
		 */
			Unsafe_Reverse_Changes_on_ScratchUnits(highAppSlotAddr,
										numHighAppSlots, offset, PROT_NONE);
		}

	/* Copy the shadow data from the copies to the newly mapped shadow region */
		Unsafe_Copy_Write_Skip_ScratchShadow(lowShadowCopyAddr,
										newLowShadowAddr, numLowShadowCopy);

	/* Unmap the mapped copies pf shadow data */
		Unmap_ShadowData_TemCopy(lowShadowCopyAddr, numLowShadowCopy);
	} else {
	/* Reversing changes on the scartch space */
		Unsafe_Reverse_Changes_on_ScratchUnits(highAppSlotAddr,
								numHighAppSlots, unitPtr->offset, PROT_NONE);
	}
}

void Manage__SE_App_Case(uint64_t appSlotsBegAddr, uint64_t numAppSlots)
{
/* Possibilities considered:  <?>.<SE>.<App> */
	uint64_t highAppSlotAddr = appSlotsBegAddr + (numAppSlots << (uint64_t)SLOT_SHIFT);
	uint64_t numLowAppSlots = NumAppSlots_VicinityLowAppUnits(appSlotsBegAddr);
	uint64_t numHighAppSlots = NumAppSlots_VicinityHighAppUnits(highAppSlotAddr);
	uint64_t lowAppSlotAddr = appSlotsBegAddr - (numLowAppSlots << (uint64_t)SLOT_SHIFT);

/* Attempt to map shadow using the App unit's offset */
	struct unitInfo *highAppUnitPtr =
			memLayoutTablePtr + (appSlotsBegAddr >> (uint64_t)SLOT_SHIFT) + numAppSlots;
	if (!AttemptMapShadow(lowAppSlotAddr,
						numAppSlots + numLowAppSlots - 1, highAppUnitPtr->offset)) {
	/* Get copies of the shadow data for low app units; and unit and high app units */
		uint64_t highShadowCopyAddr =
					Unsafe_Get_ShadowData_TemCopy(highAppSlotAddr, numHighAppSlots);
		uint64_t numHighShadowCopy = numHighAppSlots << (uint64_t)SHADOW_SCALE;
		uint64_t newHighShadowAddr;

	/* Map the new shadow region for the entire range of addresses */
		int64_t offset = MmapShadowMemSlots(lowAppSlotAddr,
							numAppSlots + numLowAppSlots + numHighAppSlots);

	/* In case the application mapping failed and we are in the process
	 * of stack unwinding because of the possiblity of the application
	 * region being mapped recursively.
	 */
		if(offset == (int64_t)APP_MAPPING_FAILED) {
		/* Now we need to attempt to remap the shadows for aplication units
		 * whose shadows were unmapped. We treat those units as FIXED MAPPINGS
		 * since we do not have their info and there must be app pointers pointing
		 * to them already.
		 */
			appMappingInfoPtr->mapping_type = (int8_t)FIXED_MAPPING_USED;

		/* Now, we are ready to map the shadows */
			int64_t lowShadowOffset = MmapShadowMemSlots(lowAppSlotAddr, numLowAppSlots + 1);
			int64_t highShadowOffset = MmapShadowMemSlots(highAppSlotAddr, numHighAppSlots);

		/* Copy the shadow data from the temporary copies */
			newHighShadowAddr = (highAppSlotAddr << (uint64_t)SHADOW_SCALE) + highShadowOffset;
		} else {
		/* Copy the shadow data from the copies to the newly mapped shadow region */
			newHighShadowAddr = (highAppSlotAddr << (uint64_t)SHADOW_SCALE) + offset;
			uint64_t newLowShadowAddr = (lowAppSlotAddr << (uint64_t)SHADOW_SCALE) + offset;

		/* Set the protection to no acess and unmap reserved units for
		 * the shadows of the scratch units if any amongst the app units.
		 */
			Unsafe_Reverse_Changes_on_ScratchUnits(lowAppSlotAddr,
										numLowAppSlots, offset, PROT_NONE);
		}

	/* Copy the shadow data from the copies to the newly mapped shadow region */
		Unsafe_Copy_Write_Skip_ScratchShadow(highShadowCopyAddr,
									newHighShadowAddr, numHighShadowCopy);

	/* Unmap the mapped copies pf shadow data */
		Unmap_ShadowData_TemCopy(highShadowCopyAddr, numHighShadowCopy);
	} else {
	/* Reversing changes on the scartch space */
		Unsafe_Reverse_Changes_on_ScratchUnits(lowAppSlotAddr,
						numLowAppSlots, highAppUnitPtr->offset, PROT_NONE);
	}
}

void Manage__AE_App_SameOffsetsCase(uint64_t appSlotsBegAddr, uint64_t numAppSlots)
{
/* Possibilities considered: <?>.<AE>.<App> when the A-unit and App unit offsets are same */
	struct unitInfo *unitPtr =
			memLayoutTablePtr + (appSlotsBegAddr >> (uint64_t)SLOT_SHIFT);

	/* Try to use the common offset to map shadow for the empty space between them */
	if (!AttemptMapShadow(appSlotsBegAddr + (uint64_t)SLOT_SIZE,
								numAppSlots - 1, unitPtr->offset)) {
	/* Since the mapping failed, we can use the following function and
	 * the relation between the offset for A unit and App unit are irelevant.
	 */
		Manage__AE_App_SameOffsetsCase(appSlotsBegAddr, numAppSlots);
	}
}

void Manage__AE_Empty_Case(uint64_t appSlotsBegAddr, uint64_t numAppSlots)
{
/* Possibilities considered: <?>.<AE>.<Empty> */
	uint64_t numLowAppSlots = NumAppSlots_VicinityLowAppUnits(appSlotsBegAddr);
	uint64_t lowAppSlotAddr = appSlotsBegAddr - (numLowAppSlots << (uint64_t)SLOT_SHIFT);

/* Try using the shadow offset for A-unit to map the empty slots */
	struct unitInfo *unitPtr = memLayoutTablePtr + (appSlotsBegAddr >> (uint64_t)SLOT_SHIFT);
	if (!AttemptMapShadow(appSlotsBegAddr + (uint64_t)SLOT_SIZE, numAppSlots - 1, unitPtr->offset)) {
	/* Get copies of the shadow data for low app units */
		uint64_t lowShadowCopyAddr = Safe_Get_ShadowData_TemCopy(lowAppSlotAddr, numLowAppSlots + 1);
		uint64_t numLowShadowCopy = (numLowAppSlots + 1) << (uint64_t)SHADOW_SCALE;
		uint64_t newLowShadowAddr;

	/* Map the new shadow region for the entire range of addresses */
		int64_t offset = MmapShadowMemSlots(lowAppSlotAddr, numAppSlots + numLowAppSlots);

	/* In case the application mapping failed and we are in the process of
	 * stack unwinding because of the possiblity of the application region
	 * being mapped recursively.
	 */
		if(offset == (int64_t)APP_MAPPING_FAILED) {
		/* Now we need to attempt to remap the shadows for aplication units
		 * whose shadows were unmapped. We treat those units as FIXED MAPPINGS
		 * since we do not have their info and there must be app pointers pointing
		 * to them already.
		 */
			appMappingInfoPtr->mapping_type = (int8_t)FIXED_MAPPING_USED;

		/* Now, we are ready to map the shadows */
			int64_t lowShadowOffset =
							MmapShadowMemSlots(lowAppSlotAddr, numLowAppSlots + 1);

		/* Copy the shadow data from the temporary copies */
			newLowShadowAddr = (lowAppSlotAddr << (uint64_t)SHADOW_SCALE) + lowShadowOffset;

		/* Set the protection to no acess and unmap reserved units for the
		 * shadows of the scratch units if any amongst the app units.
		 */
			Safe_Reverse_Changes_on_ScratchUnits(lowAppSlotAddr,
							numLowAppSlots + 1, lowShadowOffset, PROT_NONE);
		} else {
		/* Copy the shadow data from the copies to the newly mapped shadow region */
			newLowShadowAddr = (lowAppSlotAddr << (uint64_t)SHADOW_SCALE) + offset;

		/* Set the protection to no acess and unmap reserved units for the
		 * shadows of the scratch units if any amongst the app units.
		 */
			Safe_Reverse_Changes_on_ScratchUnits(lowAppSlotAddr,
										numLowAppSlots, offset, PROT_NONE);
		}

	/* Copy the shadow data from the copies to the newly mapped shadow region */
		Safe_Copy_Write_Skip_ScratchShadow(lowShadowCopyAddr,
										newLowShadowAddr, numLowShadowCopy);

	/* Unmap the mapped copies pf shadow data */
		Unmap_ShadowData_TemCopy(lowShadowCopyAddr, numLowShadowCopy);
	}
}

void Manage__SE_Empty_Case(uint64_t appSlotsBegAddr, uint64_t numAppSlots)
{
/* Possibilities considered: <?>.<SE>.<Empty> */
	uint64_t numLowAppSlots = NumAppSlots_VicinityLowAppUnits(appSlotsBegAddr);
	uint64_t lowAppSlotAddr = appSlotsBegAddr - (numLowAppSlots << (uint64_t)SLOT_SHIFT);

/* Map the entire range of addresses of the app region and its lower vicinity */
	int64_t offset = MmapShadowMemSlots(lowAppSlotAddr, numAppSlots + numLowAppSlots);

/* In case the application mapping failed and we are in the process of
 * stack unwinding because of the possiblity of the application region
 * being mapped recursively.
 */
	if(offset == (int64_t)APP_MAPPING_FAILED) {
	/* Reversing changes on the scartch space */
		Unsafe_Reverse_Changes_on_ScratchUnits(lowAppSlotAddr,
									numLowAppSlots, offset, PROT_NONE);
	}
}

void Manage_AE_MemLayout(uint64_t appSlotsBegAddr, uint64_t numAppSlots)
{
	Add_AppInfo_to_AppShadowInfoList(appSlotsBegAddr + (uint64_t)SLOT_SIZE, numAppSlots - 1);
	Add_AppInfo_to_MemLayoutTable(appSlotsBegAddr, numAppSlots);

/* We need to see if there is any conflict in the offsets due
 * to the mapping of the app region. If there is, it must have
 * been resolved using the recursive algorithm, so we need to do
 * nothing but simply quit.
 */
	if(AddInvalidOffsets(appSlotsBegAddr + (uint64_t)SLOT_SIZE,
				numAppSlots - 1, APP_MAP) == (int8_t)CONFLICT_RESOLVED) {
		return;
	}

	MapRegReservedSlots(appSlotsBegAddr + (uint64_t)SLOT_SIZE, numAppSlots - 1);
	uint64_t numLowAppSlots = NumAppSlots_VicinityLowAppUnits(appSlotsBegAddr);
	uint64_t numHighAppSlots =
			NumAppSlots_VicinityHighAppUnits(appSlotsBegAddr + (numAppSlots << (uint64_t)SLOT_SHIFT));
	struct unitInfo *unitPtr = memLayoutTablePtr + (appSlotsBegAddr >> (uint64_t)SLOT_SHIFT);
	struct unitInfo *highAppUnitPtr =
				memLayoutTablePtr + (appSlotsBegAddr >> (uint64_t)SLOT_SHIFT) + numAppSlots;
/* Possibilities: <?>.<AE>.<App>, <?>.<AE>.<Scratch>, <?>.<SE>.<App>,
 * <?>.<AE>.<Empty>, <?>.<SE>.<Empty>.
 */
	if (numHighAppSlots) {
	/* Possibilities considered: <?>.<AE>.<App>, <?>.<AE>.<Scratch>, <?> , <?>.<SE>.<App> */
		if (unitPtr->offset != highAppUnitPtr->offset) {
		/* Possibilities considered: <?>.<AE>.<App>, <?>.<AE>.<Scratch>, <?> , <?>.<SE>.<App> */
			if (unitPtr->offset != (int64_t) SCRATCH_UNIT_OFFSET) {
			/* Possibilities considered: <?>.<AE>.<App>, <?>.<AE>.<Scratch>, <?> */
				if (highAppUnitPtr->offset != (int64_t) SCRATCH_UNIT_OFFSET) {
				/* Possibilities considered: <?>.<AE>.<App> when the A-unit and App
				 * unit offsets are different.
				 */
					Manage__AE_App_DifferentOffsetsCase(appSlotsBegAddr,
							numAppSlots);
				} else {
				/* Possibilities considered: <?>.<AE>.<Scratch> */
					Manage__AE_Scratch_Case(appSlotsBegAddr, numAppSlots);
				}
			} else {
			/* Possibilities considered:  <?>.<SE>.<App> */
				Manage__SE_App_Case(appSlotsBegAddr, numAppSlots);
			}
		} else {
		/* Possibilities considered: <?>.<AE>.<App> when the A-unit and App
		 * unit offsets are same.
		 */
			Manage__AE_App_SameOffsetsCase(appSlotsBegAddr, numAppSlots);
		}
	} else {
	/* Possibilities: <?>. <AE>.<Empty>, <?>.<SE>.<Empty> */
		if (unitPtr->offset != (int64_t) SCRATCH_UNIT_OFFSET) {
		/* Possibilities: <?>.<AE>.<Empty> */
			Manage__AE_Empty_Case(appSlotsBegAddr, numAppSlots);
		} else {
		/* Possibilities: <?>.<SE>.<Empty> */
			Manage__SE_Empty_Case(appSlotsBegAddr, numAppSlots);
		}
	}
}

void Manage__AEA__DifferentOffsetsCase(uint64_t appSlotsBegAddr, uint64_t numAppSlots)
{
/* Possibilities considered: <?>.<AEA>.<?> with both A units having differeent offsets */
	uint64_t appSlotAddr = appSlotsBegAddr + ((numAppSlots - 1) << (uint64_t)SLOT_SHIFT);
	uint64_t numLowAppSlots = NumAppSlots_VicinityLowAppUnits(appSlotsBegAddr);
	uint64_t numHighAppSlots = NumAppSlots_VicinityHighAppUnits(appSlotAddr + (uint64_t)SLOT_SIZE);
	uint64_t lowAppSlotAddr = appSlotsBegAddr - (numLowAppSlots << (uint64_t)SLOT_SHIFT);

/* Get copies of the shadow data for low app units; and unit and high app units */
	uint64_t lowShadowCopyAddr = Safe_Get_ShadowData_TemCopy(lowAppSlotAddr, numLowAppSlots + 1);
	uint64_t highShadowCopyAddr = Safe_Get_ShadowData_TemCopy(appSlotAddr, numHighAppSlots + 1);
	uint64_t numLowShadowCopy = (numLowAppSlots + 1) << (uint64_t)SHADOW_SCALE;
	uint64_t numHighShadowCopy = (numHighAppSlots + 1) << (uint64_t)SHADOW_SCALE;
	uint64_t newLowShadowAddr;
	uint64_t newHighShadowAddr;

/* Map the new shadow region for the entire range of addresses */
	int64_t offset = MmapShadowMemSlots(lowAppSlotAddr,
							numAppSlots + numLowAppSlots + numHighAppSlots);

/* In case the application mapping failed and we are in the process of
 * stack unwinding because of the possiblity of the application region
 * being mapped recursively.
 */
	if(offset == (int64_t)APP_MAPPING_FAILED) {
	/* Now we need to attempt to remap the shadows for aplication units
	 * whose shadows were unmapped. We treat those units as FIXED MAPPINGS
	 * since we do not have their info and there must be app pointers pointing
	 * to them already.
	 */
		appMappingInfoPtr->mapping_type = (int8_t)FIXED_MAPPING_USED;

	/* Now, we are ready to map the shadows */
		int64_t lowShadowOffset = MmapShadowMemSlots(lowAppSlotAddr, numLowAppSlots + 1);
		int64_t highShadowOffset = MmapShadowMemSlots(appSlotAddr, numHighAppSlots + 1);

	/* Copy the shadow data from the temporary copies */
		newLowShadowAddr = (lowAppSlotAddr << (uint64_t)SHADOW_SCALE) + lowShadowOffset;
		newHighShadowAddr = (appSlotAddr << (uint64_t)SHADOW_SCALE) + highShadowOffset;

	/* Set the protection to no acess and unmap reserved units for
	 * the shadows of the scratch unit if any amongst the app units.
	 */
		Safe_Reverse_Changes_on_ScratchUnits(lowAppSlotAddr,
					numLowAppSlots + 1, lowShadowOffset, PROT_NONE);
		Safe_Reverse_Changes_on_ScratchUnits(appSlotAddr,
							numHighAppSlots + 1, highShadowOffset, PROT_NONE);
	} else {
	/* Copy the shadow data from the copies to the newly mapped shadow region */
		newHighShadowAddr = (appSlotAddr << (uint64_t)SHADOW_SCALE) + offset;
		newLowShadowAddr = (lowAppSlotAddr << (uint64_t)SHADOW_SCALE) + offset;

	/* Set the protection to no acess and unmap reserved units for the
	 * shadows of the scratch units if any amongst the app units.
	 */
		Safe_Reverse_Changes_on_ScratchUnits(lowAppSlotAddr,
										numLowAppSlots, offset, PROT_NONE);
		Safe_Reverse_Changes_on_ScratchUnits(appSlotAddr,
									numHighAppSlots, offset, PROT_NONE);
	}

/* Copy the shadow data from the copies to the newly mapped shadow region */
	Safe_Copy_Write_Skip_ScratchShadow(lowShadowCopyAddr,
									newLowShadowAddr, numLowShadowCopy);
	Safe_Copy_Write_Skip_ScratchShadow(highShadowCopyAddr,
									newHighShadowAddr, numHighShadowCopy);

/* Unmap the mapped copies pf shadow data */
	Unmap_ShadowData_TemCopy(highShadowCopyAddr, numHighShadowCopy);
	Unmap_ShadowData_TemCopy(lowShadowCopyAddr, numLowShadowCopy);
}

void Manage__AES__Case(uint64_t appSlotsBegAddr, uint64_t numAppSlots)
{
/* Possibilities considered: <?>.<AES>.<?> */
	uint64_t highAppSlotAddr = appSlotsBegAddr + (numAppSlots << (uint64_t)SLOT_SHIFT);
	uint64_t numLowAppSlots = NumAppSlots_VicinityLowAppUnits(appSlotsBegAddr);
	uint64_t numHighAppSlots = NumAppSlots_VicinityHighAppUnits(highAppSlotAddr);
	uint64_t lowAppSlotAddr = appSlotsBegAddr - (numLowAppSlots << (uint64_t)SLOT_SHIFT);

/* First we try to map shadow using the low app units */
	struct unitInfo* lowUnitPtr =
						memLayoutTablePtr + (appSlotsBegAddr >> (uint64_t)SLOT_SHIFT);
	if (!AttemptMapShadow(appSlotsBegAddr + (uint64_t)SLOT_SIZE,
						numAppSlots + numHighAppSlots - 1, lowUnitPtr->offset)) {
	/* Get copies of the shadow data for low app units; and unit and high app units */
		uint64_t lowShadowCopyAddr =
				Unsafe_Get_ShadowData_TemCopy(lowAppSlotAddr, numLowAppSlots + 1);
		uint64_t numLowShadowCopy = (numLowAppSlots + 1) << (uint64_t)SHADOW_SCALE;
		uint64_t newLowShadowAddr;

	/* Map the new shadow region for the entire range of addresses */
		int64_t offset = MmapShadowMemSlots(lowAppSlotAddr,
							numAppSlots + numLowAppSlots + numHighAppSlots);

	/* In case the application mapping failed and we are in the process of
	 * stack unwinding because of the possiblity of the application region
	 * being mapped recursively.
	 */
		if(offset == (int64_t)APP_MAPPING_FAILED) {
		/* Now we need to attempt to remap the shadows for aplication units
		 * whose shadows were unmapped. We treat those units as FIXED MAPPINGS
		 * since we do not have their info and there must be app pointers pointing
		 * to them already.
		 */
			appMappingInfoPtr->mapping_type = (int8_t)FIXED_MAPPING_USED;

		/* Now, we are ready to map the shadows */
			int64_t lowShadowOffset = MmapShadowMemSlots(lowAppSlotAddr, numLowAppSlots + 1);

		/* Copy the shadow data from the temporary copies */
			newLowShadowAddr = (lowAppSlotAddr << (uint64_t)SHADOW_SCALE) + lowShadowOffset;
		} else {
		/* Copy the shadow data from the copies to the newly mapped shadow region */
			uint64_t newHighShadowAddr = (highAppSlotAddr << (uint64_t)SHADOW_SCALE) + offset;
			newLowShadowAddr = (lowAppSlotAddr << (uint64_t)SHADOW_SCALE) + offset;

		/* Set the protection to no acess and unmap reserved units for the
		 * shadows of the scratch units if any amongst the app units.
		 */
			Unsafe_Reverse_Changes_on_ScratchUnits(highAppSlotAddr,
									numHighAppSlots, offset, PROT_NONE);
		}

	/* Copy the shadow data from the copies to the newly mapped shadow region */
		Unsafe_Copy_Write_Skip_ScratchShadow(lowShadowCopyAddr,
										newLowShadowAddr, numLowShadowCopy);

	/* Unmap the mapped copies pf shadow data */
		Unmap_ShadowData_TemCopy(lowShadowCopyAddr, numLowShadowCopy);
	} else {
	/* Reversing changes on the scartch space */
		Unsafe_Reverse_Changes_on_ScratchUnits(highAppSlotAddr,
										numHighAppSlots, lowUnitPtr->offset, PROT_NONE);
	}
}

void Manage__SEA__Case(uint64_t appSlotsBegAddr, uint64_t numAppSlots)
{
/* Possibilities considered: <?>.<SEA>.<?> */
	uint64_t appSlotAddr = appSlotsBegAddr + ((numAppSlots - 1) << (uint64_t)SLOT_SHIFT);
	uint64_t numLowAppSlots = NumAppSlots_VicinityLowAppUnits(appSlotsBegAddr);
	uint64_t numHighAppSlots = NumAppSlots_VicinityHighAppUnits(appSlotAddr + (uint64_t)SLOT_SIZE);
	uint64_t lowAppSlotAddr = appSlotsBegAddr - (numLowAppSlots << (uint64_t)SLOT_SHIFT);

/* Possibilities considered: <?>.<SEA>.<?> */
	struct unitInfo* highUnitPtr = memLayoutTablePtr + (appSlotAddr >> (uint64_t)SLOT_SHIFT);
	if (!AttemptMapShadow(lowAppSlotAddr, numAppSlots + numLowAppSlots - 1, highUnitPtr->offset)) {
	/* Get copies of the shadow data for low app units; and unit and high app units */
		uint64_t highShadowCopyAddr =
					Unsafe_Get_ShadowData_TemCopy(appSlotAddr, numHighAppSlots + 1);
		uint64_t numHighShadowCopy = (numHighAppSlots + 1) << (uint64_t)SHADOW_SCALE;
		uint64_t newHighShadowAddr;

	/* Map the new shadow region for the entire range of addresses */
		int64_t offset = MmapShadowMemSlots(lowAppSlotAddr,
							numAppSlots + numLowAppSlots + numHighAppSlots);

	/* In case the application mapping failed and we are in the process of
	 * stack unwinding because of the possiblity of the application region
	 * being mapped recursively.
	 */
		if(offset == (int64_t)APP_MAPPING_FAILED) {
		/* Now we need to attempt to remap the shadows for aplication units
		 * whose shadows were unmapped. We treat those units as FIXED MAPPINGS
		 * since we do not have their info and there must be app pointers pointing
		 * to them already.
		 */
			appMappingInfoPtr->mapping_type = (int8_t)FIXED_MAPPING_USED;

		/* Now, we are ready to map the shadows */
			int64_t lowShadowOffset = MmapShadowMemSlots(lowAppSlotAddr, numLowAppSlots + 1);
			int64_t highShadowOffset = MmapShadowMemSlots(appSlotAddr, numHighAppSlots + 1);

		/* Copy the shadow data from the temporary copies */
			newHighShadowAddr = (appSlotAddr << (uint64_t)SHADOW_SCALE) + highShadowOffset;
		} else {
		/* Copy the shadow data from the copies to the newly mapped shadow region */
			newHighShadowAddr = (appSlotAddr << (uint64_t)SHADOW_SCALE) + offset;
			uint64_t newLowShadowAddr = (lowAppSlotAddr << (uint64_t)SHADOW_SCALE) + offset;

		/* Set the protection to no acess and unmap reserved units for the
		 * shadows of the scratch units if any amongst the app units.
		 */
			Unsafe_Reverse_Changes_on_ScratchUnits(lowAppSlotAddr,
									numLowAppSlots, offset, PROT_NONE);
		}

	/* Copy the shadow data from the copies to the newly mapped shadow region */
		Unsafe_Copy_Write_Skip_ScratchShadow(highShadowCopyAddr,
								newHighShadowAddr, numHighShadowCopy);

		/* Unmap the mapped copies pf shadow data */
		Unmap_ShadowData_TemCopy(highShadowCopyAddr, numHighShadowCopy);
	} else {
	/* Reversing changes on the scartch space */
		Unsafe_Reverse_Changes_on_ScratchUnits(lowAppSlotAddr, numLowAppSlots,
														highUnitPtr->offset, PROT_NONE);
	}
}

void Manage__AEA__SameOffsetsCase(uint64_t appSlotsBegAddr, uint64_t numAppSlots)
{
/* Possibilities considered: <?>.<AEA>.<?> with both A units with same offset */
	struct unitInfo* lowUnitPtr = memLayoutTablePtr + (appSlotsBegAddr >> (uint64_t)SLOT_SHIFT);

/* Note: The existing pre-existing app units cannot be part of scatch space
 * since the scratch space is contiguous
 */
/* Attempt to map the shadow using the common offsets of A units */
	if (!AttemptMapShadow(appSlotsBegAddr + (uint64_t)SLOT_SIZE, numAppSlots - 2, lowUnitPtr->offset)) {
	/* Now we can proceed being oblivious to the relation between the offsets of A-units */
		Manage__AEA__DifferentOffsetsCase(appSlotsBegAddr, numAppSlots);
	}
}

void Manage_AEA_MemLayout(uint64_t appSlotsBegAddr, uint64_t numAppSlots)
{
	Add_AppInfo_to_MemLayoutTable(appSlotsBegAddr, numAppSlots);
	Add_AppInfo_to_AppShadowInfoList(appSlotsBegAddr + (uint64_t)SLOT_SIZE, numAppSlots - 2);

/* We need to see if there is any conflict in the offsets due to the mapping of the
 * app region. If there is, it must have been resolved using the recursive algorithm,
 * so we need to do nothing but simply quit.
 */
	if(AddInvalidOffsets(appSlotsBegAddr + (uint64_t)SLOT_SIZE,
			numAppSlots - 2, APP_MAP) == (int8_t)CONFLICT_RESOLVED) {
		return;
	}

	MapRegReservedSlots(appSlotsBegAddr + (uint64_t)SLOT_SIZE, numAppSlots - 2);
	uint64_t appLowSlotAddr = appSlotsBegAddr;
	uint64_t appHighSlotAddr = appSlotsBegAddr + ((numAppSlots - 1) << (uint64_t)SLOT_SHIFT);
	struct unitInfo* highUnitPtr = memLayoutTablePtr + (appHighSlotAddr >> (uint64_t)SLOT_SHIFT);
	struct unitInfo* lowUnitPtr = memLayoutTablePtr + (appLowSlotAddr >> (uint64_t)SLOT_SHIFT);

/* Possibilities considered: <?>.<AEA>.<?>, <?>.<SEA>.<?>, <?>.<AES>.<?> */
	if (lowUnitPtr->offset != highUnitPtr->offset) {
	/* Possibilities considered: <?>.<AEA>.<?>, <?>.<SEA>.<?>, <?>.<AES>.<?> */
		if (lowUnitPtr->offset != (int64_t) SCRATCH_UNIT_OFFSET) {
		/* Possibilities considered: <?>.<AEA>.<?>, <?>.<AES>.<?> */
			if (highUnitPtr->offset != (int64_t) SCRATCH_UNIT_OFFSET) {
			/* Possibilities considered: <?>.<AEA>.<?> */
				Manage__AEA__DifferentOffsetsCase(appSlotsBegAddr, numAppSlots);
			} else {
			/* Possibilities considered: <?>.<AES>.<?> */
				Manage__AES__Case(appSlotsBegAddr, numAppSlots);
			}
		} else {
		/* Possibilities considered: <?>.<SEA>.<?> */
			Manage__SEA__Case(appSlotsBegAddr, numAppSlots);
		}
	} else {
	/* Possibilities considered: <?>.<AEA>.<?> */
		Manage__AEA__SameOffsetsCase(appSlotsBegAddr, numAppSlots);
	}
}

void Manage_A_MemLayout(uint64_t appSlotsBegAddr)
{
	Add_AppInfo_to_MemLayoutTable(appSlotsBegAddr, 1); /* number of app slots mapped = 1 */
	struct unitInfo *unitPtr = memLayoutTablePtr + (appSlotsBegAddr >> (uint64_t)SLOT_SHIFT);
	if (unitPtr->offset == (int64_t) SCRATCH_UNIT_OFFSET)
		MmapShadowMemSlots(appSlotsBegAddr, 1); /* number of app slots mapped = 1 */
}

void Manage_AA_MemLayout(uint64_t appSlotsBegAddr)
{
	Add_AppInfo_to_MemLayoutTable(appSlotsBegAddr, 2); /* number of app slots mapped = 2 */
}

/* Fill the buffer table in the scratch space with the file addresses */
void Get_MappedRegions_within_Range(uint64_t slotsBegAddr, uint64_t numSlots)
{
	struct tableEntry_struct *cur_tablePtr = scratchSpaceInfoPtr->tablePtr;
	uint64_t slotsEndAddr = slotsBegAddr + (numSlots << (uint64_t)SLOT_SHIFT);

/* Open the /proc/<pid>/maps file. If we fail to do so due to some reason,
 * we end the process immediately.
 */
	char procInfoFile[1024] = {0};
	SAFE_SPRINTF(procInfoFile, 1024, "/proc/%d/maps", getpid());
	int procFile_fd = open(procInfoFile, O_RDONLY);
	ASSERT(procFile_fd != -1, "Error: Could not open proc maps file.\n");

/* Heap has to be skipped when the table buffer is to be filled as we
 * interate through the proc file.
 */
	uint64_t progBreak = (uint64_t)Syssbrk(0);

/* Read the file and analyse the process memory layout */
	uint64_t prevEndAddr = 0;
	char buffer[1024] = {0};
	char readChar;
	uint64_t lineNum = 0;
	char *bufPtr = buffer;
	while(read(procFile_fd, (void *)&readChar, 1) > 0) {
		if(readChar == '\n') {
			*bufPtr = '\0';
			char *restBuf;

		/* Read the start addresses to convert the strings into hexadecimals as in proc file */
			char *invalidCharPtr;
			uint64_t startAddr = SAFE_STRTOULL_BASE16(buffer, &invalidCharPtr);
			ASSERT(startAddr != (uint64_t)-1 && invalidCharPtr,
					"Error in reading proc file. Possibly file is corrupt.\n");

		/* At this point, *invalidCharPtr == '-'. So we increment the pointer
		 * before reading the end address.
		 */
			uint64_t endAddr = SAFE_STRTOULL_BASE16(++invalidCharPtr, &invalidCharPtr);
			ASSERT(endAddr != (uint64_t)-1 && invalidCharPtr,
							"Error in reading proc file. Possibly file is corrupt.");

		/* Put the addresses read from the proc file in the table buffer if it is the given range */
			if(endAddr <= slotsBegAddr) {
				bufPtr = buffer;
				continue;
			}
			if(startAddr >= slotsEndAddr)
				break;

			if(startAddr >= slotsBegAddr && endAddr <= slotsEndAddr) {
				cur_tablePtr->entry1 = startAddr;
				cur_tablePtr->entry2 = endAddr;
				cur_tablePtr++;
				bufPtr = buffer;
				continue;
			}
			if(startAddr <= slotsBegAddr && endAddr <= slotsEndAddr) {
				cur_tablePtr->entry1 = slotsBegAddr;
				cur_tablePtr->entry2 = endAddr;
				cur_tablePtr++;
				bufPtr = buffer;
				continue;
			}
			if(startAddr >= slotsBegAddr && startAddr < slotsEndAddr
			&& endAddr >= slotsEndAddr) {
				cur_tablePtr->entry1 = startAddr;
				cur_tablePtr->entry2 = slotsEndAddr;
				cur_tablePtr++;
				bufPtr = buffer;
				continue;
			}
			if(startAddr < slotsBegAddr && endAddr > slotsEndAddr) {
				cur_tablePtr->entry1 = slotsBegAddr;
				cur_tablePtr->entry2 = slotsEndAddr;
				cur_tablePtr++;
				bufPtr = buffer;
				continue;
			}
			bufPtr = buffer;
			continue;
		}
		*bufPtr = readChar;
		bufPtr++;
	}
	ASSERT(!close(procFile_fd), "Error: Failed to close proc maps file,\n");
}

/* In some situations when reserved units are to be mapped or blocked units
 * are to be mapped, they might be other mappings that might interfere with
 * the mapping of the whole slot(s) altogether, so we just map the empty
 * spaces in the in the slot(s).
 */
void Fill_EmptySpaces_in_Slots(uint64_t regSlotAddr, uint64_t numRegSlots)
{
/* Now we get the addresses that are mapped in the above range */
	Get_MappedRegions_within_Range(regSlotAddr, numRegSlots);

/* Now lets start filling up the space */
	struct tableEntry_struct *cur_tablePtr = scratchSpaceInfoPtr->tablePtr;
	uint64_t mapBegAddr = regSlotAddr;
	uint64_t mapEndAddr = regSlotAddr + (numRegSlots << (uint64_t)SLOT_SHIFT);
	while(mapBegAddr != mapEndAddr) {
	/* Check if there any mappings in the given range in question */
		if(!cur_tablePtr->entry1) {
			uint64_t mapSize = mapEndAddr - mapBegAddr;
			if(!mapSize)
				break;
			uint64_t mmapPtr = (uint64_t) Sysmmap((void *)mapBegAddr, mapSize, PROT_NONE,
														MAP_SHARED | MAP_ANONYMOUS, 0, 0);
			ASSERT(mmapPtr != (uint64_t)MAP_FAILED,
							"Error in mapping the space to fill up the slot.");
			ASSERT(mmapPtr == mapBegAddr,
							"Error in scaling the map to fill up the slot.");
			break;
		}

		if(mapBegAddr == cur_tablePtr->entry1) {
			mapBegAddr = cur_tablePtr->entry2;
			cur_tablePtr++;
			continue;
		}

	/* Map the region to fill up the region */
		uint64_t mapSize = (cur_tablePtr->entry1) - mapBegAddr;
		uint64_t mmapPtr = (uint64_t) Sysmmap((void *)mapBegAddr, mapSize, PROT_NONE,
													MAP_SHARED | MAP_ANONYMOUS, 0, 0);
		ASSERT(mmapPtr != (uint64_t)MAP_FAILED,
								"Error in mapping the space to fill up the slot.");
		ASSERT(mmapPtr == mapBegAddr, "Error in scaling the map to fill up the slot.");
		mapBegAddr = cur_tablePtr->entry2;
		cur_tablePtr++;
	}

/* Now we need to empty the buffer */
	SHADOW_MEMSET_ZERO((void *)scratchSpaceInfoPtr->tablePtr,
								scratchSpaceInfoPtr->tableBufferSize);
}

int8_t AppRegion_Overlaps_BlockedSlots(uint64_t appSlotsBegAddr, uint64_t numAppSlots)
{
	struct unitInfo *unitInfoPtr =
					memLayoutTablePtr + (appSlotsBegAddr >> (uint64_t)SLOT_SHIFT);
	uint64_t countSlots = 0;
	while(countSlots++ != numAppSlots) {
	/* If any slot is in fact a blocked slot, return 1 */
		if(unitInfoPtr->offset == (int64_t)BLOCK_SLOT_OFFSET)
			return 1;
		unitInfoPtr++;
	}
	return 0;
}

/* Here we try to map shadow using the existing offsets. If we fail in our
 * first attempt to do so, we would remap the application region, block the
 * empty slots that enclosed the given region and attempt to map shadow all
 * over again. This is a recursive operation and timed. These blocked slots
 * are put into a seperate list which is a part of the scratch space and there
 * are considered different kinds of slots namely Blocked App slots.
 */
int64_t Map_Shadow_with_ValidOffsets(uint64_t appSlotsBegAddr, uint64_t numAppSlots)
{
	volatile struct validOffset_struct *validOffsetNodePtr = validOffsetsListPtr;
	while (validOffsetNodePtr) {
		if (AttemptMapShadow(appSlotsBegAddr, numAppSlots, validOffsetNodePtr->validOffset)) {
		/* If the timer is on, that means the SIGALRM must be blocked.
		 * So we unblock it, handle it  if necessary and then we turn
		 * the timer off.
		 */
			if(timer_is_on) {
			/* Turn the timer off and let the kernel take control of SIGALRM */
				TurnTimerOff_and_RetSIGALRMControl();
				timer_is_on = false;
			}
			shadowOffsets[0] = validOffsetNodePtr->validOffset;
			return shadowOffsets[0];
		}
		validOffsetNodePtr = validOffsetNodePtr->nextNodePtr;
		}

/* If some region was extended, for instance, heap or stack, there is nothing we can do */
	if(appMappingInfoPtr->mapping_type == (int8_t)NO_MAPPING_USED)
		return 0;

/* If the mapping used is fixed or if we are trying to shadow previously
 * mapped app regions whose mapping info is not possible to know.
 * It also could be heap (if relevant) or the stack or executable.
 */
	if(appMappingInfoPtr->mapping_type == (int8_t)FIXED_MAPPING_USED)
		return 0;

/* We check is SIGVTALRM is a pending signal, if not, we continue. Else, we go random */
	sigset_t wait_mask;
	if(timer_is_on) {
		sigpending (&wait_mask);
		if (sigismember (&wait_mask, SIGVTALRM)) {
		/* Save the context of the program so after handler returns,
		 * the control returns here.
		 */
			if(sigsetjmp(alarm_context, 1)) {
			/* Turn the timer off and let the kernel take control of SIGALRM */
				TurnTimerOff_and_RetSIGALRMControl();
				timer_is_on = false;
				goto go_random;
			}

		/* Now we unblock SIGVTALRM so the signal can be caught and handled */
			Manage_SigAlarm_Signal(SIG_UNBLOCK,
						"Failed to unblock SIGVTALRM for it to be handled.");
		}
	}

/* We have to unmap the application region and block the slots that
 * were empty prior to its mapping.
 */
	if(appMappingInfoPtr->mapping_type == (int8_t)MMAP_MAPPING_USED) {
	/* If the mapping intended by the application was supposed to be
	 * at a non-null address, we can't really do anything about it
	 * so we just quit this function.
	 */
		if(appMappingInfoPtr->intended_addr)
			return 0;

	/* If the app region was mmaped directly, we unmap it */
		Sysmunmap((void *)appMappingInfoPtr->mmapped_addr, appMappingInfoPtr->size);
	} else {
	/* If the app region was mmaped through the malloc library,
	 * we let the malloc  library handle it.
	 */
		if(appMappingInfoPtr->mapping_type == (int8_t)MALLOC_MAPPING_USED
				|| appMappingInfoPtr->mapping_type == (int8_t)CALLOC_MAPPING_USED) {
			Sysfree((void *)appMappingInfoPtr->mmapped_addr);
		}
	}

	struct unitInfo *unitPtr = memLayoutTablePtr + (appSlotsBegAddr >> (uint64_t)SLOT_SHIFT);
	uint64_t countSlots = 0;
	while(countSlots != numAppSlots) {
		if(unitPtr->numReg == 1) {
		/* This means that the slot in question was an empty slot, so we block it */
			unitPtr->numReg = 0;
			unitPtr->offset = (int64_t)BLOCK_SLOT_OFFSET ;

		/* We also need to remove these slots from the app-shadow info list */
			uint64_t slotAddr = appSlotsBegAddr + (countSlots << (uint64_t)SLOT_SHIFT);
			Remove_AppInfo_from_AppShadowInfoList(slotAddr);

		/* Unmap the reserved slots corresponding to the app region slot
		 * that was recently unmapped.
		 */
			UnmapRegUnitReservedSlots(slotAddr);

		/* Block the slot and put the address in the blocked slots list */
			uint64_t mmapPtr = (uint64_t)Sysmmap((void *)slotAddr, (uint64_t)SLOT_SIZE, PROT_NONE,
																MAP_SHARED | MAP_ANONYMOUS, 0, 0);
			if(mmapPtr == (uint64_t)MAP_FAILED) {
			/* If mapping failed, fill the empty spaces */
				Fill_EmptySpaces_in_Slots(slotAddr, 1);
			} else {
				if(mmapPtr != slotAddr) {
				/* If the mapping could not be scaled properly, fill up the space */
					Sysmunmap((void *)mmapPtr, (uint64_t)SLOT_SIZE);
					Fill_EmptySpaces_in_Slots(slotAddr, 1);
				}
			}
			//Add_BlockSlotAddr_to_BlockSlotsList(slotAddr);
		}
		unitPtr++;
		countSlots++;
	}

/* We only turn the timer on only if the timer is off */
	if(!timer_is_on) {
	/* Now we start the block the SIGALRM signal */
		Manage_SigAlarm_Signal(SIG_BLOCK, "Failed to block SIGVTALRM");

	/* We let our signal handler catch and handle the signal */
		Manage_SigAlarm_SignalHandling(Handle_SigAlarm, "Failed to set the alarm handler.");

	/* Now we set the timer for 1 microsecond */
		Set_MicroTimer(5, "Failed to set the timer for large shadow mappings.");
	}

/* Now we remap the application region */
	if(appMappingInfoPtr->mapping_type == (int8_t)MMAP_MAPPING_USED) {
	/* If the app region was mmaped directly, we remap it using mmap */
		appMappingInfoPtr->mmapped_addr = (uint64_t)Sysmmap(NULL, appMappingInfoPtr->size,
				appMappingInfoPtr->prot, appMappingInfoPtr->flags, appMappingInfoPtr->fd,
																appMappingInfoPtr->offset);

	/* Possibly we are out of memory due to which the shadow mapping
	 * handled by the kernel failed, so instead of unwinding the stack
	 * and continuing, we could try to safely unwind the stack and let
	 * the application be aware that the mapping failed.
	 */
		if(appMappingInfoPtr->mmapped_addr == (uint64_t)MAP_FAILED) {
			if(timer_is_on) {
			/* Turn the timer off and let the kernel take control of SIGALRM */
				TurnTimerOff_and_RetSIGALRMControl();
				timer_is_on = false;
			}
			return APP_MAPPING_FAILED;
		}

	/* Now we try to map the shadow(s) */
		if(Map_Shadow_for_Mmaped_Region()) {
			if(timer_is_on) {
			/* Turn the timer off and let the kernel take control of SIGALRM */
				TurnTimerOff_and_RetSIGALRMControl();
				timer_is_on = false;
			}
			return shadowOffsets[0];
		}
	} else {
	/* If the app region was mmaped through the malloc library,
	 * we let the malloc  library handle it.
	 */
		if(appMappingInfoPtr->mapping_type == (int8_t)MALLOC_MAPPING_USED) {
			appMappingInfoPtr->mmapped_addr = (uint64_t)Sysmalloc(appMappingInfoPtr->size);

		/* It is possible that we are out of memory and we just quit gracefully
		 * and unwind the stack on our way out and let the appliaction know about
		 * this failure.
		 */
			if(!appMappingInfoPtr->mmapped_addr) {
				if(timer_is_on) {
				/* Turn the timer off and let the kernel take control of SIGALRM */
					TurnTimerOff_and_RetSIGALRMControl();
					timer_is_on = false;
				}
				return APP_MAPPING_FAILED;
			}

			if(Map_Shadow_for_Malloced_Region()) {
				if(timer_is_on) {
				/* Turn the timer off and let the kernel take control of SIGALRM */
					TurnTimerOff_and_RetSIGALRMControl();
					timer_is_on = false;
				}
				return shadowOffsets[0];
			}
		} else {
			if(appMappingInfoPtr->mapping_type == (int8_t)CALLOC_MAPPING_USED) {
				appMappingInfoPtr->mmapped_addr = (uint64_t)Syscalloc(1, appMappingInfoPtr->size);

			/* There is a possibility that we run  out of memory */
				if(!appMappingInfoPtr->mmapped_addr) {
					if(timer_is_on) {
					/* Turn the timer off and let the kernel take control of SIGALRM */
						TurnTimerOff_and_RetSIGALRMControl();
						timer_is_on = false;
					}
					return APP_MAPPING_FAILED;
				}
				if(Map_Shadow_for_Malloced_Region()) {
					if(timer_is_on) {
					/* Turn the timer off and let the kernel take control of SIGALRM */
						TurnTimerOff_and_RetSIGALRMControl();
						timer_is_on = false;
					}
					return shadowOffsets[0];
				}
			}
		}
	}
	return 0;

go_random:
/* Now, we try to map the application region at random loacations and try
 * to map shadows recursively. This is a timed operation as well.
 */
	return 0;
}

int64_t RemapAppRegion(void)
{
/* If some region was extended, for instance, heap or stack, there is nothing we can do */
	if(appMappingInfoPtr->mapping_type == (int8_t)NO_MAPPING_USED)
		return 0;

/* If the mapping used is fixed or if we are trying to shadow previously
 * mapped app regions whose mapping info is not possible to know. It also
 * could be heap (if relevant) or the stack or executable.
 */
	if(appMappingInfoPtr->mapping_type == (int8_t)FIXED_MAPPING_USED)
		return 0;

/* We check is SIGVTALRM is a pending signal, if not, we continue. Else, we go random */
	sigset_t wait_mask;
	if(timer_is_on) {
		sigpending (&wait_mask);
		if (sigismember (&wait_mask, SIGVTALRM)) {
		/* Save the context of the program so after handler returns, the control returns here */
			if(sigsetjmp(alarm_context, 1)) {
			/* Turn the timer off and let the kernel take control of SIGALRM */
				TurnTimerOff_and_RetSIGALRMControl();

				goto go_random;
			}

		/* Now we unblock SIGVTALRM so the signal can be caught and handled */
			Manage_SigAlarm_Signal(SIG_UNBLOCK,
						"Failed to unblock SIGVTALRM for it to be handled.");
		}
	}

/* We have to unmap the application region and block the slots that were
 * empty prior to its mapping.
 */
	if(appMappingInfoPtr->mapping_type == (int8_t)MMAP_MAPPING_USED) {
	/* If the mapping intended by the application was supposed to be
	 * at a non-null address, we can't really do anything about it so
	 * we just quit this function.
	 */
		if(appMappingInfoPtr->intended_addr)
			return 0;

	/* If the app region was mmaped directly, we unmap it */
		Sysmunmap((void *)appMappingInfoPtr->mmapped_addr, appMappingInfoPtr->size);
	} else {
	/* If the app region was mmaped through the malloc library,
	 * we let the malloc  library handle it.
	 */
		if(appMappingInfoPtr->mapping_type == (int8_t)MALLOC_MAPPING_USED
		|| appMappingInfoPtr->mapping_type == (int8_t)CALLOC_MAPPING_USED) {
			Sysfree((void *)appMappingInfoPtr->mmapped_addr);
		}
	}

	struct regSlotsInfo regSlotsInfoStruct;
	Get_RegSlotsInfo(appMappingInfoPtr->mmapped_addr,
									appMappingInfoPtr->size, &regSlotsInfoStruct);
	struct unitInfo *unitPtr =
			memLayoutTablePtr + ((regSlotsInfoStruct.regSlotsBegAddr) >> (uint64_t)SLOT_SHIFT);
	uint64_t countSlots = 0;
	while(countSlots != regSlotsInfoStruct.numRegSlots) {
		if(unitPtr->numReg == 1) {
		/* This means that the slot in question was an empty slot, so we block it */
			unitPtr->numReg = 0;
			unitPtr->offset = (int64_t)BLOCK_SLOT_OFFSET ;

		/* We also need to remove these slots from the app-shadow info list */
			uint64_t slotAddr =
					regSlotsInfoStruct.regSlotsBegAddr + (countSlots << (uint64_t)SLOT_SHIFT);
			Remove_AppInfo_from_AppShadowInfoList(slotAddr);

		/* Unmap the reserved slots corresponding to the app region slot that was recently unmapped */
			UnmapRegUnitReservedSlots(slotAddr);

		/* Block the slot and put the address in the blocked slots list */
			uint64_t mmapPtr = (uint64_t)Sysmmap((void *)slotAddr, (uint64_t)SLOT_SIZE, PROT_NONE,
															MAP_SHARED | MAP_ANONYMOUS, 0, 0);
			if(mmapPtr == (uint64_t)MAP_FAILED) {
			/* If mapping failed, fill the empty spaces */
				Fill_EmptySpaces_in_Slots(slotAddr, 1);
			} else {
				if(mmapPtr != slotAddr) {
				/* If the mapping could not be scaled properly, fill up the space */
					Sysmunmap((void *)mmapPtr, (uint64_t)SLOT_SIZE);
					Fill_EmptySpaces_in_Slots(slotAddr, 1);
				}
			}
			//Add_BlockSlotAddr_to_BlockSlotsList(slotAddr);
		}
		unitPtr++;
		countSlots++;
	}

/* We only turn the timer on only if the timer is off */
	if(!timer_is_on) {
	/* Now we start the block the SIGALRM signal */
		Manage_SigAlarm_Signal(SIG_BLOCK, "Failed to block SIGVTALRM");

	/* We let our signal handler catch and handle the signal */
		Manage_SigAlarm_SignalHandling(Handle_SigAlarm, "Failed to set the alarm handler.");

	/* Now we set the timer for 1 microsecond */
		Set_MicroTimer(5, "Failed to set the timer for large shadow mappings.");
	}

/* Now we remap the application region */
	if(appMappingInfoPtr->mapping_type == (int8_t)MMAP_MAPPING_USED) {
		if(!appMappingInfoPtr->mmapped_addr) {
		/* If the app region was mmaped directly, we remap it using mmap */
			appMappingInfoPtr->mmapped_addr = (uint64_t)Sysmmap(NULL, appMappingInfoPtr->size,
					appMappingInfoPtr->prot, appMappingInfoPtr->flags, appMappingInfoPtr->fd,
																	appMappingInfoPtr->offset);

		/* Possibly we are out of memory due to which the shadow mapping
		 * handled by the kernel failed, so instead of unwinding the stack
		 * and continuing, we could try to safely unwind the stack and let
		 * the application be aware that the mapping failed.
		 */
			if(appMappingInfoPtr->mmapped_addr == (uint64_t)MAP_FAILED) {
				if(timer_is_on) {
				/* Turn the timer off and let the kernel take control of SIGALRM */
					TurnTimerOff_and_RetSIGALRMControl();
					timer_is_on = false;
				}
				return 0;
			}

		/* Now we try to map the shadow(s) */
			if(Map_Shadow_for_Mmaped_Region()) {
				if(timer_is_on) {
				/* Turn the timer off and let the kernel take control of SIGALRM */
					TurnTimerOff_and_RetSIGALRMControl();
					timer_is_on = false;
				}
				return 1;
			}
		}
	} else {
	/* If the app region was mmaped through the malloc library,
	 * we let the malloc  library handle it.
	 */
		if(appMappingInfoPtr->mapping_type == (int8_t)MALLOC_MAPPING_USED) {
			appMappingInfoPtr->mmapped_addr = (uint64_t)Sysmalloc(appMappingInfoPtr->size);

		/* It is possible that we are out of memory and we just quit gracefully
		 * and unwind the stack on our way out and let the appliaction know about
		 * this failure.
		 */
			if(!appMappingInfoPtr->mmapped_addr) {
				if(timer_is_on) {
				/* Turn the timer off and let the kernel take control of SIGALRM */
					TurnTimerOff_and_RetSIGALRMControl();
					timer_is_on = false;
				}
				return 0;
			}

			if(Map_Shadow_for_Malloced_Region()) {
				if(timer_is_on) {
				/* Turn the timer off and let the kernel take control of SIGALRM */
					TurnTimerOff_and_RetSIGALRMControl();
					timer_is_on = false;
				}
				return 1;
			}
		} else {
			if(appMappingInfoPtr->mapping_type == (int8_t)CALLOC_MAPPING_USED) {
				appMappingInfoPtr->mmapped_addr = (uint64_t)Syscalloc(1, appMappingInfoPtr->size);

			/* There is a possibility that we run  out of memory */
				if(!appMappingInfoPtr->mmapped_addr) {
					if(timer_is_on) {
					/* Turn the timer off and let the kernel take control of SIGALRM */
						TurnTimerOff_and_RetSIGALRMControl();
						timer_is_on = false;
					}
					return 0;
				}
				if(Map_Shadow_for_Malloced_Region()) {
					if(timer_is_on) {
					/* Turn the timer off and let the kernel take control of SIGALRM */
						TurnTimerOff_and_RetSIGALRMControl();
						timer_is_on = false;
					}
					return 1;
				}
			}
		}
	}
	return 0;

go_random:
/* Now, we try to map the application region at random loacations and
 * try to map shadows recursively. This is a timed operation as well.
 */
	return 0;
}

inline void TurnTimerOff_and_RetSIGALRMControl (void)
{
/* We save the context if the program here so if the timer goes off while we
 * are turning the timer off and passing the control back on to the kernel to
 * handle SIGVTALRM, we can handle the signal and hopefully we'll have enough
 * to finish turning the timer off and let kernel pass SIGVTALRM.
 */
	sigsetjmp(alarm_context, 1);

/* We unset the timer to turn it off */
	Set_MicroTimer(0, "Failed to turn the timer off.");

/* Now we unblock SIGVTALRM so the signal can be caught and handled */
	Manage_SigAlarm_Signal(SIG_UNBLOCK,
							"Failed to unblock SIGVTALRM for it to be handled.");

/* We let the kernel catch and handle the signal */
	Manage_SigAlarm_SignalHandling(NULL,
			"Failed to pass the control of handling SIGVTALRM to the kernel.");
}

int8_t Map_Shadow_for_Malloced_Region(void)
{
	DEBUG_PRINTF("WARNING: RECURSIVE SHADOW MAPPING BEING USED FOR MALLOC\n");
#ifndef BLOCK_HEAP
	if(mallocPtr >= (uint64_t)Syssbrk(0)) {
#endif
	/* We get the pointer to the metadata for the malloced chunk
	 * and see how the allocation took place.
	 */
		struct chunk_info *ptr_to_metadata =
			(struct chunk_info *)(appMappingInfoPtr->mmapped_addr - heapInfoPtr->alloc_chunkInfo_size);

	/* One option is that either a new arena was mapped or an existing
	 * heap was expanded or non-contiguous main heap is mapped or reused
	 * so we just confirm by checking if the NON_MAIN_ARENA and PREV_INUSE
	 * bits are set just to be safe.
	 */
		if((ptr_to_metadata->mchunk_size) & PREV_INUSE) {
		/* We just check if the metadata for heap is not corrupt. If it is, we quit */
			ASSERT(!((ptr_to_metadata->mchunk_size & IS_MMAPPED)),
					"Heap metadata is corrupt. Both IS_MAPPED and PREV_INUSE bits cannot be set.");

		/* The chunk size has to be a multiple of 8 */
			uint64_t chunkSize = ptr_to_metadata->mchunk_size & ((uint64_t)(~0) << 3);
			if(ptr_to_metadata->mchunk_size & NON_MAIN_ARENA) {
			/* In order to improve performance, we depend on the fact the
			 * most of the time the application is likely to use the already-mapped
			 * heap rather than mmap new arena frequently. So we store some
			 * information about the previously mmaped and used non-main arena
			 * so we can quickly check if the given area has been allocated in
			 * the most recently used mmaped heap. If it is not, it must belong
			 * to some other mapped heap.
			 */
				if((uint64_t)ptr_to_metadata > mmapped_heap_addr) {
					if((uint64_t)ptr_to_metadata + chunkSize
							< mmapped_heap_addr + mmapped_heap_size) {
					/* We first check if the chunk is mapped */
						uint64_t pageAligned_ptr_to_metadata =
								(uint64_t)ptr_to_metadata & (sysPageInfoPtr->pageMask);
						uint64_t page_rounded_chunkSize = RoundUpSize_to_PageSizeMultiple(chunkSize);
						ASSERT(Sysmsync((void *)pageAligned_ptr_to_metadata,
								page_rounded_chunkSize, MS_ASYNC) != -1,
										"Error: Non-main arena chunk is not mmaped. "
												"Possibly the metadata is corrupt.");

					/* Once we know the allocation took place in an existing mapped heap, we're done */
						return 1;
					}
				}

			/* We need to figure out if a new arena was mapped or allocation
			 * took place within an existing arena. So we do a light-weight
			 * check to see if the app units enclosing the arena already have
			 * shadow and reserved units. We attempt to access the metadata for heap.
			 */
				uint64_t heap_addr = mmapped_heap_addr =
						(uint64_t)ptr_to_metadata & sysPageInfoPtr->pageMask;

				uint64_t page_rounded_heapSize = mmapped_heap_size =
						RoundUpSize_to_PageSizeMultiple(((struct heap_info *)heap_addr)->size);

			/* Now we check if the heap is really mapped */
				ASSERT(Sysmsync((void *)heap_addr, page_rounded_heapSize, MS_ASYNC) != -1,
								"Non-main heap not mmaped. Possibly the metadata is corrupt.");

			/* Now we can work on mapping the shadow that we have all the info we need */
				struct regSlotsInfo heapSlotsInfo;
				Get_RegSlotsInfo(heap_addr, ((struct heap_info *)heap_addr)->size, &heapSlotsInfo);
				MapAppRegion(heapSlotsInfo.regSlotsBegAddr, heapSlotsInfo.numRegSlots);
			} else {
			/* This means that the mmaped main arena (the non-contiguous extention of it) was used
			 * by real malloc. It is possible to allocate multiple chunks in the single mapping.
			 * It is most likely to be a non-contiguous main heap.
			 * First we check that the pages containing the non-main arena mapping are mapped.
			 */
				uint64_t pageAligned_ptr_to_metadata =
						(uint64_t)ptr_to_metadata & (sysPageInfoPtr->pageMask);
				uint64_t page_rounded_chunkSize = RoundUpSize_to_PageSizeMultiple(chunkSize);
				ASSERT(Sysmsync((void *)pageAligned_ptr_to_metadata,
						page_rounded_chunkSize, MS_ASYNC) != -1,
					"Error: Non-contiguous main arena chunk is not mmaped. "
										"Possibly the metadata is corrupt.");

			/* If chunk pointer is page aligned, possibly a new non-contiguous main heap.
			 *  Else an existing one is used.
			 */
				if(!((uint64_t)ptr_to_metadata & (~(sysPageInfoPtr->pageMask)))) {
					struct regSlotsInfo mainHeap_slotsInfo;
					Get_RegSlotsInfo((uint64_t)ptr_to_metadata,
										ptr_to_metadata->mchunk_size, &mainHeap_slotsInfo);
					MapAppRegion(mainHeap_slotsInfo.regSlotsBegAddr, mainHeap_slotsInfo.numRegSlots);
				}
			}
		} else {
		/* We just check if the metadata for heap is not corrupt. If it is, we quit */
			ASSERT(!((ptr_to_metadata->mchunk_size & NON_MAIN_ARENA)), "Heap metadata corrupt.\n");
			ASSERT(ptr_to_metadata->mchunk_size & IS_MMAPPED, "Heap metadata corrupt.\n");

		/* Just to be safe, we check if the metadata pointer corresponding to malloc
		 * pointer is page aligned.
		 */
			ASSERT(!((uint64_t)ptr_to_metadata & (~sysPageInfoPtr->pageMask)),
					 "Chunk metadata pointer not page aligned for mmaped chunk.");

			appMappingInfoPtr->mapping_type = (int8_t)MALLOC_MAPPING_USED;
			appMappingInfoPtr->mmapped_addr = appMappingInfoPtr->mmapped_addr;

		/* If it is mmaped, we try to get the starting address of the mmap
		 * by getting the page address the given pointer belongs to and use
		 * the size to shadow map it. We first get the size of th map from
		 * the metaData. This is not safe but this is the best choice
		 * we've got to get the size of the map.
		 */
			uint64_t mmaped_size = (ptr_to_metadata->mchunk_size) & ((uint64_t)(~0) << 3);

		/* We get the information about the slots that enclose the mmaped region,
		 * and then we map its shadow and reserved units.
		 */
			struct regSlotsInfo mmaped_regSlotsInfo;
			Get_RegSlotsInfo((uint64_t)ptr_to_metadata, mmaped_size, &mmaped_regSlotsInfo);
			MapAppRegion(mmaped_regSlotsInfo.regSlotsBegAddr, mmaped_regSlotsInfo.numRegSlots);
		}

#ifndef BLOCK_HEAP
	} else {
	/* This means that that the main arena was extended. If the the heap
	 * size exceeds the heap size for which the shadow has already been
	 * accounted for, we extend the heap limits kept track of by the
	 * scratch heap struct. We treat the heap extention as a new application region.
	 */
		if((uint64_t)Syssbrk(0) > heapInfoPtr->heapBase + heapInfoPtr->heapSoftLimit) {
			struct regSlotsInfo heapExtention_slotsInfo;
			uint64_t old_heapSoftLimit = heapInfoPtr->heapSoftLimit;
			uint64_t heapExtentionSize = (uint64_t)1 << 29;  /* extend the heap virtually by 500Mb */
			heapInfoPtr->heapSoftLimit += heapExtentionSize;  /* Now we update the saved heap soft limit */
			Get_RegSlotsInfo(heapInfoPtr->heapBase + old_heapSoftLimit,
					heapExtentionSize, &heapExtention_slotsInfo);
			MapAppRegion(heapExtention_slotsInfo.regSlotsBegAddr,
									heapExtention_slotsInfo.numRegSlots);
		}
	}
#endif
	return 1;
}

int8_t Map_Shadow_for_Mmaped_Region(void)
{
	DEBUG_PRINTF("+++++=WARNING: RECURSIVE SHADOW MAPPING BEING USED FOR MMAP\n");
#ifndef BLOCK_HEAP
/* If the mapping took place within the heap limits, we reduce the limit
 * to the begining of the newly mmaped region.
 */
	uint64_t old_heapCurLim = heapInfoPtr->heapBase + heapInfoPtr->heapSoftLimit;
	if(mmapPtr <= old_heapCurLim) {
	/* If the entire mmaped region fits within the former heap limits,
	 * we don't have to map a new shadow. Instead, we might have to
	 * truncate it accounting for the region beyond the newly mmaped region.
	 */
		heapInfoPtr->heapSoftLimit = (appMappingInfoPtr->mmaped_addr) - heapInfoPtr->heapBase;
		uint64_t mmapEndAddr = (appMappingInfoPtr->mmaped_addr) + (appMappingInfoPtr->size);
		if(mmapEndAddr > old_heapCurLim) {
		/* We treat the extra mmap region sticking out of the heap region as a new app region */
			struct regSlotsInfo regExtentionSlotsInfo;
			Get_RegSlotsInfo(old_heapCurLim,
					(uint64_t)(appMappingInfoPtr->size) -
								(old_heapCurLim - appMappingInfoPtr->mmaped_addr),
						&regExtentionSlotsInfo);
			MapAppRegion(regExtentionSlotsInfo.regSlotsBegAddr,
									regExtentionSlotsInfo.numRegSlots);
			return 1;
		} else {
			if(mmapEndAddr == old_heapCurLim) {
			/* mmaped region is at the end of the heap, so its shadow exits */
				return 1;
			} else {
			/* The mmaped region is inside the heap region, so the shadow exits but
			 * we need to truncate the shadow for region beyond the newly mmaped region.
			 */
				struct regSlotsInfo regTruncateSlotsInfo;
				Get_RegSlotsInfo(mmapEndAddr,
						old_heapCurLim - mmapEndAddr, &regTruncateSlotsInfo);
				UnmapAppRegion(regTruncateSlotsInfo.regSlotsBegAddr,
									regTruncateSlotsInfo.numRegSlots);
				return 1;
			}
		}
	}
#endif

/* Now, we get the information about the slots enclosing the mmapped
 * region and map shadows and reserved units.
 */
	struct regSlotsInfo mmaped_regSlotsInfo;
	Get_RegSlotsInfo(appMappingInfoPtr->mmapped_addr, appMappingInfoPtr->size, &mmaped_regSlotsInfo);
	MapAppRegion(mmaped_regSlotsInfo.regSlotsBegAddr, mmaped_regSlotsInfo.numRegSlots);
	return 1;
}

void *Mmap_FixedAddr_Shadow(uint64_t slotsBegAddr, uint64_t numSlots)
{
	uint64_t mmapAddr = slotsBegAddr;
	uint64_t mmapPtr;
	uint64_t countSlots = 0;
	while(countSlots != numSlots) {
try_mappingSlot_again:
		mmapPtr = (uint64_t) Sysmmap((void *)mmapAddr,
									(uint64_t)SLOT_SIZE, PROT_READ | PROT_WRITE,
									MAP_SHARED | MAP_ANONYMOUS | MAP_NORESERVE, 0, 0);

	/* We check if the mapping fails, we check if it is because mmapAddr is a blocked slot */
		if(mmapPtr == (uint64_t)MAP_FAILED) {
		/* If the slot in question is a blocked slot, we remove the slot
		 * from the blocked slot list and change the protection of the
		 * blocked slot to readable and writable.
		 */
			struct unitInfo *unitPtr = memLayoutTablePtr + (mmapPtr >> (uint64_t)SLOT_SHIFT);
			if(unitPtr->offset == (int64_t)BLOCK_SLOT_OFFSET) {
				Sysmprotect((void *)mmapAddr, (uint64_t)SLOT_SIZE, PROT_READ | PROT_WRITE);
				//Remove_BlockSlotAddr_from_BlockSlotsList(mmapAddr);
				goto try_mappingSlot_again;
			} else {
			/* We unmap the mappings that we just mapped */
				mmapAddr = slotsBegAddr;
				while(countSlots--) {
					Sysmunmap((void *)mmapAddr, (uint64_t)SLOT_SIZE);
					mmapAddr += (uint64_t)SLOT_SIZE;
				}
				return (void *)MAP_FAILED;
			}
		} else {
			if(mmapPtr != mmapAddr) {
			/* If the shadow mapping does not scale well, we unmap the shadow
			 * and unmap all the shadow slots we have mapped so far.
			 */
				Sysmunmap((void *)mmapPtr, (uint64_t)SLOT_SIZE);
				mmapAddr = slotsBegAddr;
				while(countSlots--) {
					Sysmunmap((void *)mmapAddr, (uint64_t)SLOT_SIZE);
					mmapAddr += (uint64_t)SLOT_SIZE;
				}
				return (void *)MAP_FAILED;
			}
		}
		mmapAddr += (uint64_t)SLOT_SIZE;
		countSlots++;
	}
	return (void *)slotsBegAddr;
}

void *Kernel_Mmap_Shadow(uint64_t numSlots)
{
/* First, we mmap the first slot of shadow */
	uint64_t firstSlotAddr =
			(uint64_t)Sysmmap(NULL, (uint64_t)SLOT_SIZE, PROT_READ | PROT_WRITE,
									MAP_SHARED | MAP_ANONYMOUS | MAP_NORESERVE, 0, 0);
	if(firstSlotAddr == (uint64_t)MAP_FAILED)
		return (void *)MAP_FAILED;

/* Now the above mapping can be extended (mmap algorithm on
 * linux and Mac OS) in either direction, so we keep track of
 * the direction of the mappings extention via say vma_merge()
 * in linux kernel for x86-64. The best way to do that is to
 * try mapping in one direction and if we fail we try the other
 * one. So we start mapping towards larger addresses.
 */
	uint64_t mmapPtr;
	uint64_t mmapAddr = firstSlotAddr + (uint64_t)SLOT_SIZE;
	uint64_t countSlots = 1;
	while(countSlots != numSlots) {
		mmapPtr = (uint64_t) Sysmmap((void *)mmapAddr,
						(uint64_t)SLOT_SIZE, PROT_READ | PROT_WRITE,
									MAP_SHARED | MAP_ANONYMOUS | MAP_NORESERVE, 0, 0);

	/* We check if the mapping fails, we check if it is because
	 * mmapAddr is a blocked slot.
	 */
		if(mmapPtr == (uint64_t)MAP_FAILED) {
		/* If the slot in question is a blocked slot, we remove the slot
		 * from the blocked slot list and change the protection of the
		 * blocked slot to readable and writable.
		 */
			struct unitInfo *unitPtr = memLayoutTablePtr + (mmapPtr >> (uint64_t)SLOT_SHIFT);
			if(unitPtr->offset == (int64_t)BLOCK_SLOT_OFFSET) {
				Sysmprotect((void *)mmapAddr, (uint64_t)SLOT_SIZE, PROT_READ | PROT_WRITE);
				//Remove_BlockSlotAddr_from_BlockSlotsList(mmapAddr);
				continue;
			} else {
			/* We unmap the mappings that we just mapped except the first one */
				mmapAddr = firstSlotAddr + (uint64_t)SLOT_SIZE;
				while((countSlots--) != 1) {
					Sysmunmap((void *)mmapAddr, (uint64_t)SLOT_SIZE);
					mmapAddr += (uint64_t)SLOT_SIZE;
				}
				goto try_lower_addrs;
			}
		} else {
			if(mmapPtr != mmapAddr) {
			/* If the shadow mapping does not scale well, we unmap the
			 * shadow and unmap all the shadow slots we have mapped so
			 * far except the first one.
			 */
				Sysmunmap((void *)mmapPtr, (uint64_t)SLOT_SIZE);
				mmapAddr = firstSlotAddr + (uint64_t)SLOT_SIZE;
				while((countSlots--) != 1) {
					Sysmunmap((void *)mmapAddr, (uint64_t)SLOT_SIZE);
					mmapAddr += (uint64_t)SLOT_SIZE;
				}
				goto try_lower_addrs;
			}
		}
		mmapAddr += (uint64_t)SLOT_SIZE;
		countSlots++;
	}
	return (void *) firstSlotAddr;

try_lower_addrs:
/* Now we let the mappings 'grow' towards the lower addresses */
	mmapAddr = firstSlotAddr - (uint64_t)SLOT_SIZE;
	countSlots = 1;
	while(countSlots != numSlots) {
		mmapPtr = (uint64_t) Sysmmap((void *)mmapAddr, (uint64_t)SLOT_SIZE, PROT_READ | PROT_WRITE,
												MAP_SHARED | MAP_ANONYMOUS | MAP_NORESERVE, 0, 0);

	/* We check if the mapping fails, we check if it is because mmapAddr is a blocked slot */
		if(mmapPtr == (uint64_t)MAP_FAILED) {
		/* If the slot in question is a blocked slot, we remove the
		 * slot from the blocked slot list and change the protection
		 * of the blocked slot to readable and writable.
		 */
			struct unitInfo *unitPtr = memLayoutTablePtr + (mmapPtr >> (uint64_t)SLOT_SHIFT);
			if(unitPtr->offset == (int64_t)BLOCK_SLOT_OFFSET) {
				Sysmprotect((void *)mmapAddr, (uint64_t)SLOT_SIZE, PROT_READ | PROT_WRITE);
				//Remove_BlockSlotAddr_from_BlockSlotsList(mmapAddr);
				continue;
			} else {
			/* We unmap the mappings that we just mapped */
				mmapAddr = firstSlotAddr + (uint64_t)SLOT_SIZE;
				while(countSlots--) {
					Sysmunmap((void *)mmapAddr, (uint64_t)SLOT_SIZE);
					mmapAddr -= (uint64_t)SLOT_SIZE;
				}
				return (void *)MAP_FAILED;
			}
		} else {
			if(mmapPtr != mmapAddr) {
			/* If the shadow mapping does not scale well, we unmap the shadow
			 * and unmap all the shadow slots we have mapped so far.
			 */
				Sysmunmap((void *)mmapPtr, (uint64_t)SLOT_SIZE);
				mmapAddr = firstSlotAddr + (uint64_t)SLOT_SIZE;
				while(countSlots--) {
					Sysmunmap((void *)mmapAddr, (uint64_t)SLOT_SIZE);
					mmapAddr -= (uint64_t)SLOT_SIZE;
				}
				return (void *)MAP_FAILED;
			}
		}
		mmapAddr -= (uint64_t)SLOT_SIZE;
		countSlots++;
	}
	return (void *) (firstSlotAddr - ((numSlots - 1) << (uint64_t)SLOT_SHIFT));
}

void Set_MicroTimer(uint64_t time, char *error_message)
{
	struct itimerval timer;
	struct timeval it_value;
	timer.it_value.tv_sec = 0;
	timer.it_value.tv_usec = (suseconds_t)time;
	timer.it_interval = timer.it_value;
	ASSERT(!setitimer (ITIMER_VIRTUAL , &timer, NULL), error_message);
}

 void Manage_SigAlarm_Signal(int manage_alarm_sig, char *error_message)
{
	sigset_t sig_mask;
	ASSERT(!sigemptyset (&sig_mask), "Failed to empty the signal mask.");
	ASSERT(!sigaddset (&sig_mask, SIGVTALRM), "Failed to add SIGVTALRM to mask.");
	ASSERT(!sigprocmask (manage_alarm_sig, &sig_mask, NULL), error_message);
}

void Manage_SigAlarm_SignalHandling(void (*signal_handler)(int sigNum), char *error_message)
{
	struct sigaction signal_act;
	signal_act.sa_handler = signal_handler;
	signal_act.sa_flags = 0;
	ASSERT(!sigemptyset(&signal_act.sa_mask), "Failed to set the empty signal mask.");
	ASSERT(!sigaction (SIGVTALRM, &signal_act, NULL), error_message);
}

int64_t Map_Shadow_with_NewOffset(uint64_t appSlotsBegAddr, uint64_t numAppSlots)
{
	volatile uint64_t numShadowSlots = numAppSlots << (uint64_t)SHADOW_SCALE;
	volatile uint64_t totalNumSlots = (uint64_t)1 << (47 - (uint64_t)SLOT_SHIFT);
	volatile uint64_t invalidOffsetsTablesMask =
			~((uint64_t)(~0) << (47 - (uint64_t)SLOT_SHIFT + (uint64_t)SHADOW_SCALE));
	volatile uint64_t mmapSize = numShadowSlots << (uint64_t)SLOT_SHIFT;
	volatile uint64_t mmapPtr;
	volatile int64_t offset;
	volatile uint64_t *stackBasePtr = NULL;
	volatile uint64_t *stackTopPtr;

/* We attempt to map the shadow. If the mapping is at invalid offset
 * from the application slot(s) it is shadow to, we push the address
 * of the truncated mapping onto the stack in the shadow scratch space
 * and we map again. We also set a timer to virtually time how much
 * time it took to execute and after 10 microseconds, we get SIGVTALRM
 * signal is thrown and handled.
 */
	Manage_SigAlarm_Signal(SIG_BLOCK, "Failed to block SIGVTALRM");

/* We let our signal handler catch and handle the signal */
	Manage_SigAlarm_SignalHandling(Handle_SigAlarm, "Failed to set the alarm handler.");

/* Now we set the timer for 1 microsecond */
	Set_MicroTimer(1, "Failed to set the timer for large shadow mappings.");

try_large_map:
/* Try mapping numShadowSlots + 1 and if it fails we proceed to go random.
 * If it succeeds, we try to align the mapping according to the units.
*/
	mmapPtr = (uint64_t)Kernel_Mmap_Shadow(
										(mmapSize + (uint64_t)SLOT_SIZE) >> (uint64_t)SLOT_SHIFT);
	if(mmapPtr != (uint64_t)MAP_FAILED) {
		uint64_t addrMask = ((uint64_t)(~0)) << (uint64_t)SLOT_SHIFT;
		uint64_t shadowBegAddr = mmapPtr;
		uint64_t mmapEndPtr = mmapPtr + mmapSize + (uint64_t)SLOT_SIZE;
		uint64_t shadowEndAddr = mmapEndPtr;
		if(mmapPtr & (~addrMask)) {
		/* If the beginning of the mapping is not aligned with the virtual
		 * units properly, we have to unmap the non-algning parts in the
		 * beginning and at the end of the mapping.
		 */
			mmapPtr = (shadowBegAddr & addrMask) + (uint64_t)SLOT_SIZE;
			mmapEndPtr = shadowEndAddr & addrMask;
			Sysmunmap((void *)shadowBegAddr, mmapPtr - shadowBegAddr);
		} else {
			mmapEndPtr = shadowEndAddr - (uint64_t)SLOT_SIZE;
		}
		Sysmunmap((void *)mmapEndPtr, shadowEndAddr - mmapEndPtr);

	/* Now we check if the shadow we have got is at the offset which has been deemed invalid already */
		struct invalidOffset_struct *invalidOffset_subUnitPtr;
		offset = mmapPtr - (appSlotsBegAddr << (uint64_t)SHADOW_SCALE);
		if (offset < 0) {
		/* Take the absolute value of the offset to hash and look up the hash table */
			uint64_t converted_offset = (uint64_t)((offset + (int64_t)(~0)) ^ ((int64_t)(~0)));
			uint64_t invalidOffsetsTablesOffset =
						(converted_offset >> (uint64_t)SLOT_SHIFT) & invalidOffsetsTablesMask;
			invalidOffset_subUnitPtr = negInvalidOffsetsTablePtr + invalidOffsetsTablesOffset;
		} else {
			uint64_t invalidOffsetsTablesOffset =
					(offset >> (uint64_t)SLOT_SHIFT) & invalidOffsetsTablesMask;
			invalidOffset_subUnitPtr = posInvalidOffsetsTablePtr + invalidOffsetsTablesOffset;
		}
		if(invalidOffset_subUnitPtr->numSubUnits) {
		/* We check if the stack data structure is mapped, if not we map it */
			if(!stackBasePtr) {
				stackBasePtr = (uint64_t *) Sysmmap(NULL,
						((uint64_t)1 << (47 - (uint64_t)SLOT_SHIFT)) * sizeof(uint64_t),
											PROT_READ | PROT_WRITE, MAP_SHARED | MAP_ANONYMOUS, 0, 0);
				stackTopPtr = stackBasePtr;
			}

		/* Now we put the addresses of the shadow slots on the stack */
			uint64_t numSlots = mmapSize >> (uint64_t)SLOT_SHIFT;
			uint64_t slotAddr = mmapPtr;
			while(numSlots--) {
				*(stackTopPtr++) = slotAddr;
				slotAddr += (uint64_t)SLOT_SIZE;
			}

		/* We check is SIGVTALRM is a pending signal, if not, we continue.
		 * Else, we unblock the signal and let the signal handler handle the signal.
		 */
			sigset_t wait_mask;
			sigpending (&wait_mask);
			if (sigismember (&wait_mask, SIGVTALRM)) {
			/* Save the context of the program so after handler returns, the control returns here */
				if(sigsetjmp(alarm_context, 1)) {
				/* Block the SIGVTALARM */
					Manage_SigAlarm_Signal(SIG_BLOCK,
								"Failed to block SIGVTALRM after signal handled.");

				/* By this point, the timer has expired so we just have to
				 * set it again and the blocked slot list still holds the
				 * pointers to blocked slots that we keep for now.
				 */
					goto go_random;
				}

			/* Unblock the SIGVTALARM */
				Manage_SigAlarm_Signal(SIG_UNBLOCK,
							"Failed to unblock SIGVTALRM for it to be handled.");
			}
			goto try_large_map;
		} else {
		/* Now, we have to check if the scratch space data structures are updated successfully */
			if(!Update_ScratchDataStructures_on_NewMap(appSlotsBegAddr, numAppSlots, offset)) {
			/* We check if the stack data structure is mapped, if not we map it */
				if(!stackBasePtr) {
					stackBasePtr = (uint64_t *) Sysmmap(NULL,
							(uint64_t)1 << (47 - (uint64_t)SLOT_SHIFT + 3),
											PROT_READ | PROT_WRITE, MAP_SHARED | MAP_ANONYMOUS, 0, 0);
					stackTopPtr = stackBasePtr;
				}

			/* Now we put the addresses of the shadow slots on the stack */
				uint64_t numSlots = mmapSize >> (uint64_t)SLOT_SHIFT;
				uint64_t slotAddr = mmapPtr;
				while(numSlots--) {
					*(stackTopPtr++) = slotAddr;
					slotAddr += (uint64_t)SLOT_SIZE;
				}

			/* We check is SIGVTALRM is a pending signal, if not, we continue.
			 * Else, we unblock the signal and let the signal handler handle
			 * the signal.
			 */
				sigset_t wait_mask;
				sigpending (&wait_mask);
				if (sigismember (&wait_mask, SIGVTALRM)) {
				/* Save the context of the program so after handler returns,
				 * the control returns here.
				 */
					if(sigsetjmp(alarm_context, 1)) {
					/* Block the SIGVTALARM */
						Manage_SigAlarm_Signal(SIG_BLOCK,
								"Failed to block SIGVTALRM after signal handled.");

					/* By this point, the timer has expired so we just have
					 * to set it again and the blocked slot list still holds
					 * the pointers to blocked slots that we keep for now.
					 */
						goto go_random;
					}

				/* Unblock the SIGVTALARM */
					Manage_SigAlarm_Signal(SIG_UNBLOCK,
							"Failed to unblock SIGVTALRM for it to be handled.");
				}
				goto try_large_map;
			}
		}
	} else {
go_random:
	/* We unset the timer first and then reset it to start afresh */
		Set_MicroTimer(0, "Failed to stop the timer to reset it.");

	/* At this point, the SIGVTALRM is still blocked, so we reset the timer */
		Set_MicroTimer(10, "Failed to set the timer for large shadow mappings.");

		volatile uint64_t memLayoutTableOffset;
try_random_map:
	/* Check if the offset computed for the prospective shadow slot
	 * is in the invalid offsets tables. If yes, continue to get
	 * another memLayoutOffset and repeat.
	 */
		memLayoutTableOffset = rand() % totalNumSlots;
		volatile uint64_t shadowSlotsBegAddr = memLayoutTableOffset << (uint64_t)SLOT_SHIFT;
		volatile struct invalidOffset_struct *invalidOffset_subUnitPtr;
		offset = shadowSlotsBegAddr - (appSlotsBegAddr << (uint64_t)SHADOW_SCALE);
		if (offset < 0) {
		/* Take the absolute value of the offset to hash and look up the hash table */
			uint64_t converted_offset = (uint64_t)((offset + (int64_t)(~0)) ^ ((int64_t)(~0)));
			uint64_t invalidOffsetsTablesOffset =
						(converted_offset >> (uint64_t)SLOT_SHIFT) & invalidOffsetsTablesMask;
			invalidOffset_subUnitPtr = negInvalidOffsetsTablePtr + invalidOffsetsTablesOffset;
		} else {
			volatile uint64_t invalidOffsetsTablesOffset =
					(offset >> (uint64_t)SLOT_SHIFT) & invalidOffsetsTablesMask;
			invalidOffset_subUnitPtr = posInvalidOffsetsTablePtr + invalidOffsetsTablesOffset;
		}
		if(invalidOffset_subUnitPtr->numSubUnits) {
		/* We check is SIGVTALRM is a pending signal, if not, we continue.
		 * Else, we unblock the signal and let the signal handler handle the signal.
		 */
			sigset_t wait_mask;
			sigpending (&wait_mask);
			if (sigismember (&wait_mask, SIGVTALRM)) {
			/* Save the context of the program so after handler returns,
			 * the control returns here.
			 */
				if(sigsetjmp(alarm_context, 1)) {
				/* We quit once time is up */
					EXCEPTION("Out of memory. Could not map the shadow.\n");
				}

			/* Now we unblock SIGVTALRM so the signal can be caught and handled */
				Manage_SigAlarm_Signal(SIG_UNBLOCK,
						"Failed to unblock SIGVTALRM for it to be handled.");
			}
			goto try_random_map;
		}

	/* Check if the required contiguous shadow slots are empty. If not find a new shadow slot */
		volatile struct unitInfo *shadowUnitPtr = memLayoutTablePtr + memLayoutTableOffset;
		volatile uint64_t countSlots = 0;
		while (countSlots != numShadowSlots) {
			if (shadowUnitPtr->offset != (int64_t) EMPTY_SLOT_OFFSET) {
			/* We check is SIGVTALRM is a pending signal, if not, we continue.
			 * Else, we unblock the signal and let the signal handler handle the signal.
			 */
				sigset_t wait_mask;
				sigpending (&wait_mask);
				if (sigismember (&wait_mask, SIGVTALRM)) {
				/* Save the context of the program so after handler
				 * returns, the control returns here.
				 */
					if(sigsetjmp(alarm_context, 1)) {
					/* We quit once time is up */
						ASSERT(false, "Out of memory. Could not map the shadow.\n");
					}
				/* Now we unblock SIGVTALRM so the signal can be caught and handled */
					Manage_SigAlarm_Signal(SIG_UNBLOCK,
							"Failed to unblock SIGVTALRM for it to be handled.");
				}
				goto try_random_map;
			}
			shadowUnitPtr++;
			countSlots++;
		}
		if (countSlots == numShadowSlots) {
			volatile uint64_t mmapAddr = memLayoutTableOffset << (uint64_t)SLOT_SHIFT;
			mmapPtr = (uint64_t)Mmap_FixedAddr_Shadow(mmapAddr, mmapSize >> (uint64_t)SLOT_SHIFT);
			if (mmapPtr != (uint64_t) MAP_FAILED) {
			/* Now, we have to check if the scratch space data structures are updated successfully */
				if(!Update_ScratchDataStructures_on_NewMap(appSlotsBegAddr, numAppSlots, offset)) {
				/* If there was an offset conflict, and continue if the SIGALRM
				 * signal is not pending.
				 */
					sigset_t wait_mask;
					sigpending (&wait_mask);
					if (sigismember (&wait_mask, SIGVTALRM)) {
					/* Save the context of the program so after handler returns,
					 * the control returns here.
					 */
						if(sigsetjmp(alarm_context, 1)) {
						/* We quit once time is up */
							ASSERT(false, "Out of memory. Could not map the shadow.\n");
						}

					/* Now we unblock SIGVTALRM so the signal can be caught and handled */
						Manage_SigAlarm_Signal(SIG_UNBLOCK,
								"Failed to unblock SIGVTALRM for it to be handled.");
					}
					goto try_random_map;
				}
			/* Now, we are almost done with the mapping so now we wrap up */
				goto shadow_mapping_done;
			} else {
			/* We check is SIGVTALRM is a pending signal, if not, we continue.
			 *  Else, we unblock the signal and let the signal handler handle the signal.
			 */
				sigset_t wait_mask;
				sigpending (&wait_mask);
				if (sigismember (&wait_mask, SIGVTALRM)) {
				/* Save the context of the program so after handler returns,
				 * the control returns here.
				 */
					if(sigsetjmp(alarm_context, 1)) {
					/* We quit once time is up */
						ASSERT(false, "Out of memory. Could not map the shadow.\n");
					}

				/* Now we unblock SIGVTALRM so the signal can be caught and handled */
					Manage_SigAlarm_Signal(SIG_UNBLOCK,
							"Failed to unblock SIGVTALRM for it to be handled.");
				}
				goto try_random_map;
			}
		}
	}

shadow_mapping_done:
/* Empty the stack if it exists */
	if(stackBasePtr) {
	/* unmap all the slots on the stack */
		while(stackTopPtr != stackBasePtr) {
			Sysmunmap((void *)*stackTopPtr, (uint64_t)SLOT_SIZE);
			stackTopPtr--;
		}

	/* Unmap the stack */
		Sysmunmap((void *)stackBasePtr, (uint64_t)1 << (47 - (uint64_t)SLOT_SHIFT));
	}

/* We save the context if the program here so if the timer goes off while we
 * are turning the timer off and passing the control back on to the kernel
 * to handle SIGVTALRM, we can handle the signal and hopefully we'll have enough
 * to finish turning the timer off and let kernel pass SIGVTALRM.
 */
	sigsetjmp(alarm_context, 1);
	TurnTimerOff_and_RetSIGALRMControl();

	shadowOffsets[0] = offset;
	MapNewOffsetBasedReservedSlots(appSlotsBegAddr, numAppSlots, offset);
	return shadowOffsets[0];
}

struct validOffset_struct *Get_Available_ValidOffsetNode(void)
{
	struct validOffset_struct* validOffsetNodePtr = validOffsetsListPtr;
	if (freeValidOffsetsListPtr) {
		struct validOffset_struct* freeValidOffsetsNodePtr = freeValidOffsetsListPtr;
		freeValidOffsetsListPtr = freeValidOffsetsNodePtr->nextNodePtr;
		if ((uint64_t) freeValidOffsetsNodePtr > (uint64_t) validOffsetsListPtr) {
			validOffsetNodePtr = validOffsetsListPtr;
			while (true) {
				if (!(validOffsetNodePtr->nextNodePtr)) { /* Reached the end of the validOffsets list */
					validOffsetNodePtr->nextNodePtr = freeValidOffsetsNodePtr;
					freeValidOffsetsNodePtr->nextNodePtr = NULL;
					validOffsetNodePtr = freeValidOffsetsNodePtr;
					break;
				}
				if ((uint64_t)(validOffsetNodePtr->nextNodePtr) > (uint64_t) freeValidOffsetsNodePtr) {
					freeValidOffsetsNodePtr->nextNodePtr = validOffsetNodePtr->nextNodePtr;
					validOffsetNodePtr->nextNodePtr = freeValidOffsetsNodePtr;
					validOffsetNodePtr = freeValidOffsetsNodePtr;
					break;
				}
				validOffsetNodePtr = validOffsetNodePtr->nextNodePtr;
			}
		} else {
			freeValidOffsetsNodePtr->nextNodePtr = validOffsetsListPtr;
			validOffsetsListPtr = freeValidOffsetsNodePtr;
		}
	} else {
		validOffsetNodePtr = validOffsetsListPtr;
		while (validOffsetNodePtr->nextNodePtr)
			validOffsetNodePtr = validOffsetNodePtr->nextNodePtr; /* Reaching end of list */
		if (validOffsetsListPtr->numRegSameOffset) {
			validOffsetNodePtr->nextNodePtr = validOffsetNodePtr + 1;
			validOffsetNodePtr = validOffsetNodePtr->nextNodePtr;
		}
	}
	return validOffsetNodePtr;
}

int64_t MmapShadowMemSlots(uint64_t appSlotsBegAddr, uint64_t numAppSlots)
{
	int64_t offset = Map_Shadow_with_ValidOffsets(appSlotsBegAddr, numAppSlots);
	if (offset || offset == (int64_t)APP_MAPPING_FAILED)
		return offset;
	return Map_Shadow_with_NewOffset(appSlotsBegAddr, numAppSlots);
}

int64_t AttemptMapShadow(uint64_t appSlotsBegAddr, uint64_t numAppSlots, int64_t existingOffset)
{
	uint64_t mmapAddr = (appSlotsBegAddr << (uint64_t)SHADOW_SCALE) + existingOffset;
	if (!(mmapAddr >> 47)) {
		struct unitInfo *shadowUnitPtr = memLayoutTablePtr + (mmapAddr >> (uint64_t)SLOT_SHIFT);
		uint64_t numShadowSlots = numAppSlots << (uint64_t)SHADOW_SCALE;
		uint64_t mmapSize = numShadowSlots << (uint64_t)SLOT_SHIFT;
		uint64_t countReservedSlots = 0;
		uint64_t countSlots = 0;
		while (countSlots != numShadowSlots) {
			if (shadowUnitPtr->offset != (int64_t)EMPTY_SLOT_OFFSET) {
				if(shadowUnitPtr->offset == (int64_t)RESERVED_SLOT_OFFSET) {
				/* Check whether the reserved slot is not shared by some other app units */
					if (shadowUnitPtr->numReg == 1)
						countReservedSlots++;
				}
			}
			shadowUnitPtr++;
			countSlots++;
		}

	/* Check if all the correspoding slots which are at the given existing offset are reserved units */
		if (countReservedSlots == numShadowSlots) {
			if(!Update_ScratchDataStructures_on_NewMap(appSlotsBegAddr, numAppSlots, existingOffset))
				return 0;
			shadowOffsets[0] = existingOffset;
			MapRegReservedSlots(mmapAddr, numShadowSlots);

		/* Change the protection for the reserved slots that are considered shadow slots now */
			Sysmprotect((void *) mmapAddr, numShadowSlots << (uint64_t)SLOT_SHIFT, PROT_READ | PROT_WRITE);
			return existingOffset;
		}

	/* Check if all the slots at the given offset to the application slots are empty */
		if (countSlots == numShadowSlots) {
			uint64_t mmapPtr = (uint64_t) Mmap_FixedAddr_Shadow(mmapAddr, mmapSize >> (uint64_t)SLOT_SHIFT);
			if (mmapPtr != (uint64_t) MAP_FAILED) {
			/* If there was an offset conflict, we need to unmap the above mapping and quit */
				if(!Update_ScratchDataStructures_on_NewMap(appSlotsBegAddr, numAppSlots, existingOffset)) {
					Sysmunmap((void *)mmapPtr, mmapSize >> (uint64_t)SLOT_SHIFT);
					return 0;
				}
				shadowOffsets[0] = existingOffset;
				MapRegReservedSlots(mmapPtr, numShadowSlots);
				return existingOffset;
			}
		}
	}
	return 0;
}

int8_t Update_ScratchDataStructures_on_NewMap(uint64_t appSlotsBegAddr,
								uint64_t numAppSlots, int64_t shadowOffset)
{
	uint64_t shadowMemAddr = (appSlotsBegAddr << (uint64_t)SHADOW_SCALE) + shadowOffset;
	uint64_t numShadowSlots = numAppSlots << (uint64_t)SHADOW_SCALE;

/* Update the shadow info in the  appShadowInfo list */
	uint64_t appSlotAddr = appSlotsBegAddr;
	uint64_t countSlots  = 0;
	while(countSlots++ != numAppSlots) {
		struct appShadowAddrsNode *addrsNodePtr = app_shadowListPtr;
		while (addrsNodePtr->appUnitAddr != appSlotAddr)
			addrsNodePtr = addrsNodePtr->nextNodePtr;
		addrsNodePtr->shadowUnitAddr =
			((addrsNodePtr->appUnitAddr) << (uint64_t)SHADOW_SCALE) + shadowOffset;
		appSlotAddr += (uint64_t)SLOT_SIZE;
	}

/* Updating the invalidoffsets tables */
	if(AddInvalidOffsets(shadowMemAddr, numShadowSlots, SHADOW_MAP)
			== (int8_t)OFFSET_CONFLICT) {
	/* If there is a conflict, we need to reverse the changes made to the appShadowList */
		appSlotAddr = appSlotsBegAddr;
		countSlots  = 0;
		while(countSlots++ != numAppSlots) {
			struct appShadowAddrsNode *addrsNodePtr = app_shadowListPtr;
			while (addrsNodePtr->appUnitAddr != appSlotAddr)
				addrsNodePtr = addrsNodePtr->nextNodePtr;
			addrsNodePtr->shadowUnitAddr = 0;
			appSlotAddr += (uint64_t)SLOT_SIZE;
		}

		return 0;
	}

/* Update the memLayout table with the shadow offset info */
	struct unitInfo *appUnitPtr = memLayoutTablePtr + (appSlotsBegAddr >> (uint64_t)SLOT_SHIFT);
	struct unitInfo *shadowUnitPtr = memLayoutTablePtr + (shadowMemAddr >> (uint64_t)SLOT_SHIFT);
	countSlots = 0;
	while(countSlots++ != numAppSlots) {
		appUnitPtr->offset = shadowOffset;
		appUnitPtr++;
	}

/* Mark the corresponding shadow slots as shadows in the memLayoutTable */
	countSlots = 0;
	while(countSlots++ != numShadowSlots) {
		shadowUnitPtr->offset = (int64_t) SHADOW_SLOT_OFFSET;
		shadowUnitPtr->numReg = 0;
		shadowUnitPtr++;
	}

/* Updating the valid offsets list by augmenting the number of app units with new shadows */
	struct validOffset_struct* validOffsetNodePtr = validOffsetsListPtr;
	while (validOffsetNodePtr) { /* Walk the list */
	/* This means that the offset we have here has already been used before */
		if(validOffsetNodePtr->validOffset == shadowOffset) {
			validOffsetNodePtr->numRegSameOffset += numAppSlots;
			return 1;
		}
		validOffsetNodePtr = validOffsetNodePtr->nextNodePtr;
	}

/* This means that the shadow offset here is a new one, so we add that to the list */
	validOffsetNodePtr = Get_Available_ValidOffsetNode();
	validOffsetNodePtr->validOffset = shadowOffset;
	validOffsetNodePtr->numRegSameOffset += numAppSlots;
	return 1;
}

/*
 void Add_BlockSlotAddr_to_BlockSlotsList(uint64_t blockedSlotAddr)
{
	struct blockSlotAddrNode *blockSlotsNodePtr;
	if (free_blockSlotsListPtr) {
	/* Using the available free blocked slot node *
		struct blockSlotAddrNode *free_blockSlotsNodePtr = free_blockSlotsListPtr;
		free_blockSlotsNodePtr->blockedSlotAddr = blockedSlotAddr;
		free_blockSlotsListPtr = free_blockSlotsListPtr->nextNodePtr;
		if ((uint64_t) free_blockSlotsNodePtr > (uint64_t)blockSlotsListPtr) {
			blockSlotsNodePtr = blockSlotsListPtr;
			while (1) {
			/* Check if the free node is at the end of the main list *
				if (!(blockSlotsNodePtr->nextNodePtr)) { /* Reached the end of the blocked slots list *
					blockSlotsNodePtr->nextNodePtr = free_blockSlotsNodePtr;
					free_blockSlotsNodePtr->nextNodePtr = NULL;
					return;
				}

			/* Check if the free node is between the nodes of the main list *
				if ((uint64_t)(blockSlotsNodePtr->nextNodePtr)
														  > (uint64_t)free_blockSlotsNodePtr) {
					free_blockSlotsNodePtr->nextNodePtr = blockSlotsNodePtr->nextNodePtr;
					blockSlotsNodePtr->nextNodePtr = free_blockSlotsNodePtr;
					return;
				}
				blockSlotsNodePtr = blockSlotsNodePtr->nextNodePtr;
			}
		} else {
		/* This means that the free node is in front of the main list's first node *
			free_blockSlotsNodePtr->nextNodePtr = blockSlotsListPtr;
			blockSlotsListPtr = free_blockSlotsNodePtr;
			return;
		}
	}

/* If there is no free list, we have to make use of the actual list *
	blockSlotsNodePtr = blockSlotsListPtr;
	while (blockSlotsNodePtr->nextNodePtr)
		blockSlotsNodePtr = blockSlotsNodePtr->nextNodePtr; /* Reach end of the list */

/* Access the node adjacent to the one to the last node of the list *
	blockSlotsNodePtr->nextNodePtr = blockSlotsNodePtr + 1;
	blockSlotsNodePtr = blockSlotsNodePtr->nextNodePtr;
	blockSlotsNodePtr->blockedSlotAddr = blockedSlotAddr;
}

 void Remove_BlockSlotAddr_from_BlockSlotsList(uint64_t blockedSlotAddr)
{
	if(blockSlotsListPtr->blockedSlotAddr != blockedSlotAddr) {
	/* We look for the node right before the one with the blockedSlotAddr *
		struct blockSlotAddrNode *prev_blockSlotNodePtr = blockSlotsListPtr;
		struct blockSlotAddrNode *next_blockSlotNodePtr = blockSlotsListPtr->nextNodePtr;
		while(next_blockSlotNodePtr->blockedSlotAddr != blockedSlotAddr) {
			prev_blockSlotNodePtr = next_blockSlotNodePtr;
			next_blockSlotNodePtr = prev_blockSlotNodePtr->nextNodePtr;
		}

	/* Now we link the node preceeding the node to be remove and the one succeeding it and then remove the node *
		prev_blockSlotNodePtr->nextNodePtr = next_blockSlotNodePtr->nextNodePtr;
		next_blockSlotNodePtr->blockedSlotAddr = (uint64_t)MAX_VIRTUAL_ADDR;
		next_blockSlotNodePtr->nextNodePtr = NULL;
	} else {
	/* Unmap the blocked slot *
		Sysmunmap((void *)blockSlotsListPtr->blockedSlotAddr, (uint64_t)SLOT_SIZE);

		if(blockSlotsListPtr->nextNodePtr) {
		/* Since we are supposed to remove the very first node, we have to copy the data up the list
		 * by one node and get rid of the very last node of the list.
		 *
			struct blockSlotAddrNode *prev_blockSlotNodePtr = blockSlotsListPtr;
			struct blockSlotAddrNode *next_blockSlotNodePtr;
			while(true) {
				next_blockSlotNodePtr = prev_blockSlotNodePtr->nextNodePtr;
				prev_blockSlotNodePtr->blockedSlotAddr = next_blockSlotNodePtr->blockedSlotAddr;
				if(!(next_blockSlotNodePtr->nextNodePtr)) {
				/* Now we get rid of the last node *
					next_blockSlotNodePtr->blockedSlotAddr = (uint64_t)MAX_VIRTUAL_ADDR;
					prev_blockSlotNodePtr->nextNodePtr = NULL;
					return;
				}
				prev_blockSlotNodePtr = next_blockSlotNodePtr;
				next_blockSlotNodePtr = prev_blockSlotNodePtr->nextNodePtr;
			}
		} else {
			blockSlotsListPtr->blockedSlotAddr = (uint64_t)MAX_VIRTUAL_ADDR;
		}
	}
}
*/

void Add_AppInfo_to_AppShadowInfoList(uint64_t appSlotsBegAddr, uint64_t numAppSlots)
{
	struct appShadowAddrsNode *appShadowAddrsNodePtr;
	uint64_t appSlotAddr = appSlotsBegAddr;
	uint64_t countSlots = 0;
	if (freeAppShadowListPtr) {
		while (countSlots != numAppSlots) {
		/* Using the available free app shadow info node */
			struct appShadowAddrsNode *freeAppShadowNodePtr = freeAppShadowListPtr;
			freeAppShadowNodePtr->appUnitAddr = appSlotAddr;
			freeAppShadowListPtr = freeAppShadowNodePtr->nextNodePtr;
			if ((uint64_t) freeAppShadowNodePtr > (uint64_t) app_shadowListPtr) {
				appShadowAddrsNodePtr = app_shadowListPtr;
				while (true) {
					if (!(appShadowAddrsNodePtr->nextNodePtr)) { /* Reached the end of the appShadowInfo list */
						appShadowAddrsNodePtr->nextNodePtr = freeAppShadowNodePtr;
						freeAppShadowNodePtr->nextNodePtr = NULL;
						break;
					}
					if ((uint64_t)(appShadowAddrsNodePtr->nextNodePtr)
															  > (uint64_t)freeAppShadowNodePtr) {
						freeAppShadowNodePtr->nextNodePtr = appShadowAddrsNodePtr->nextNodePtr;
						appShadowAddrsNodePtr->nextNodePtr = freeAppShadowNodePtr;
						break;
					}
					appShadowAddrsNodePtr = appShadowAddrsNodePtr->nextNodePtr;
				}
			} else {
				freeAppShadowNodePtr->nextNodePtr = app_shadowListPtr;
				app_shadowListPtr = freeAppShadowNodePtr;
			}
			appSlotAddr += (uint64_t)SLOT_SIZE;
			countSlots++;
			if (!freeAppShadowListPtr)
				break; /* free list exhausted */
		}
	}
	if (countSlots != numAppSlots) {
		appShadowAddrsNodePtr = app_shadowListPtr;
		while (appShadowAddrsNodePtr->nextNodePtr)
			appShadowAddrsNodePtr = appShadowAddrsNodePtr->nextNodePtr; /* Reach end of the list */
		while ((countSlots++) != numAppSlots) {
			appShadowAddrsNodePtr->nextNodePtr = appShadowAddrsNodePtr + 1;
			appShadowAddrsNodePtr = appShadowAddrsNodePtr->nextNodePtr;
			appShadowAddrsNodePtr->appUnitAddr = appSlotAddr;
			appSlotAddr += (uint64_t)SLOT_SIZE;
		}
	}
}

void Add_AppInfo_to_MemLayoutTable(uint64_t appSlotsBegAddr, uint64_t numAppSlots)
{
	struct unitInfo *appUnitPtr = memLayoutTablePtr + (appSlotsBegAddr >> (uint64_t)SLOT_SHIFT);
	uint64_t countSlots = 0;
	while ((countSlots++) != numAppSlots) {
		(appUnitPtr->numReg)++;
		appUnitPtr++;
	}
}

/* It is important to note that if every app unit is virtually divided
 * into subunits depending on (uint64_t)SHADOW_SCALE: i.e. number of
 * subunits = 2^(uint64_t)SHADOW_SCALE. Every subunit scales and offsets
 * to their respective shadow units. This concept can be extended to find
 * invalid offsets. Every subunit can be scaled and subtracted to another
 * app unit and different offsets can be obtained for each subunit. This
 * way, we can get 2^(uint64_t)SHADOW_SCALE number of invalid offsets for
 * every app unit from other app/shadow unit.
*/
int8_t AddInvalidOffsets(uint64_t slotBegAddr, uint64_t numSlots, int8_t action)
{
	uint64_t numAppShadowSlots = ((uint64_t)1 << (uint64_t)SHADOW_SCALE);
	uint64_t unitAddr = slotBegAddr;
	uint64_t countSlots = 0;
	while ((countSlots++) != numSlots) {
		struct appShadowAddrsNode *addrsNodePtr = app_shadowListPtr;
		while (addrsNodePtr) {
		/* To see if the addresses in the given range conflict with the ones in the list */
			bool addrConflictFound = false;

			if (unitAddr != addrsNodePtr->appUnitAddr) {
				if (addrsNodePtr->shadowUnitAddr) {
					uint64_t numShadowSlots = numAppShadowSlots;
					while (numShadowSlots--) {
						uint64_t curShadowSlotAddr = (addrsNodePtr->shadowUnitAddr)
																+ (numShadowSlots << (uint64_t)SLOT_SHIFT);
						if (unitAddr != curShadowSlotAddr) {
							int8_t conflictStatus = Add_UnitToUnit_2Way_InvalidOffsets(unitAddr,
																curShadowSlotAddr, action);
							if(conflictStatus == (int8_t)OFFSET_CONFLICT)
								return (int8_t)OFFSET_CONFLICT;
							if(conflictStatus == (int8_t)CONFLICT_RESOLVED)
								return (int8_t)CONFLICT_RESOLVED;
						} else {
							addrConflictFound = true;
						}
					}
				}
				int8_t conflictStatus = Add_UnitToUnit_1Way_InvalidOffset(unitAddr,
												addrsNodePtr->appUnitAddr, action);
				if(conflictStatus == (int8_t)OFFSET_CONFLICT)
					return (int8_t)OFFSET_CONFLICT;
				if(conflictStatus == (int8_t)CONFLICT_RESOLVED)
					return (int8_t)CONFLICT_RESOLVED;

			/*	Shadow address conflict is checked for since if there is a conflict the shadow address,
			 * the obtained offset is valid and should not be put in the invalid offset table
			 */
				if (!addrConflictFound) {
					conflictStatus = Add_UnitToUnit_1Way_InvalidOffset(addrsNodePtr->appUnitAddr,
												unitAddr, action);
					if(conflictStatus == (int8_t)OFFSET_CONFLICT)
						return (int8_t)OFFSET_CONFLICT;
					if(conflictStatus == (int8_t)CONFLICT_RESOLVED)
						return (int8_t)CONFLICT_RESOLVED;
				}
			}
			addrsNodePtr = addrsNodePtr->nextNodePtr;
		}
		unitAddr += (uint64_t)SLOT_SIZE;
	}

/* Now, we need to make sure that all the invalid offsets that we got are saved in the hash maps */
	Add_SubUnit_to_Unit_InvalidOffsets(0, 0, (int8_t)SAVE_INVALID_OFFSETS);
}

int8_t Add_UnitToUnit_2Way_InvalidOffsets(uint64_t unit1Addr, uint64_t unit2Addr, int8_t action)
{
	uint64_t numSubUnits = (uint64_t)1 << (uint64_t)SHADOW_SCALE;
	uint64_t subUnitSize = (uint64_t)SLOT_SIZE / numSubUnits;
	uint64_t countSubUnits = ((uint64_t)1 << (uint64_t)SHADOW_SCALE);
	while (countSubUnits--) {
	/* Getting the subUnitAddr for the first unit that is scaled and added to
	 * an offset to get to the second unit/
	 */
		uint64_t subUnitAddr = unit1Addr + (countSubUnits * subUnitSize);

	/* We need to keep track of the offset conflicts that might have
	 * taken place and conflicts that must have been resolved.
	 */
			int8_t conflictStatus =
					Add_SubUnit_to_Unit_InvalidOffsets(subUnitAddr, unit2Addr, action);
			if(conflictStatus == (int8_t)OFFSET_CONFLICT)
				return (int8_t)OFFSET_CONFLICT;
			if(conflictStatus == (int8_t)CONFLICT_RESOLVED)
				return (int8_t)CONFLICT_RESOLVED;

	/* Getting the subUnitAddr for second unit that is scaled and added to an
	 * offset to get to the first unit.
	 */
		subUnitAddr = unit2Addr + (countSubUnits * subUnitSize);

	/* We need to keep track of the offset conflicts that might have taken place
	 * and conflict that must have been resolved.
	 */
		conflictStatus = Add_SubUnit_to_Unit_InvalidOffsets(subUnitAddr, unit2Addr, action);
		if(conflictStatus == (int8_t)OFFSET_CONFLICT)
			return (int8_t)OFFSET_CONFLICT;
		if(conflictStatus == (int8_t)CONFLICT_RESOLVED)
			return (int8_t)CONFLICT_RESOLVED;
	}
	return 1;
}

int8_t Add_UnitToUnit_1Way_InvalidOffset(uint64_t from_unitAddr, uint64_t to_unitAddr, int8_t action)
{
	uint64_t subUnitAddr;
	uint64_t numSubUnits = (uint64_t)1 << (uint64_t)SHADOW_SCALE;
	uint64_t subUnitSize = (uint64_t)SLOT_SIZE / numSubUnits;
	uint64_t countSubUnits = ((uint64_t)1 << (uint64_t)SHADOW_SCALE);
	while (countSubUnits--) {
		subUnitAddr = from_unitAddr + (countSubUnits * subUnitSize);

	/* We need to keep track of the offset conflicts that might have taken
	 * place and conflicts that must have been resolved.
	 */
		int8_t conflictStatus =
				Add_SubUnit_to_Unit_InvalidOffsets(subUnitAddr, to_unitAddr, action);
		if(conflictStatus == (int8_t)OFFSET_CONFLICT)
			return (int8_t)OFFSET_CONFLICT;
		if(conflictStatus == (int8_t)CONFLICT_RESOLVED)
			return (int8_t)CONFLICT_RESOLVED;
	}
	return 1;
}

/* Here the subUnit1 is treated as the subUnit that is scaled and added to an
 * offset to get to unit2.
 */
int8_t Add_SubUnit_to_Unit_InvalidOffsets(uint64_t subUnit1Addr, uint64_t unit2Addr, int8_t action)
{
/* We keep track of a stack that we map so it acts like a buffer.
 * After we're sure that there are no conflicts with the computed offsets,
 * we can pop all the offsets off to into the hash tables in the scratch space.
 */
	static int64_t *stackBasePtr = NULL;
	static int64_t *stackTopPtr = NULL;

/* We rely on the action argument to decide whether we should stack the computed
 * invalid offsets or save them in the scratch space.
 */
	if(action != (int8_t)SAVE_INVALID_OFFSETS) {
	/* If no stack is mapped, map it */
		if(!stackBasePtr) {
		/* We map a fairly large stack trying to be safe and not run out of stack space */
			uint64_t stackSize =
					((uint64_t)1 << (47 - (uint64_t)SLOT_SHIFT + (uint64_t)SHADOW_SCALE)) * sizeof(uint64_t);
			stackBasePtr = (int64_t *)Sysmmap(NULL, stackSize, PROT_READ | PROT_WRITE,
											MAP_SHARED | MAP_ANONYMOUS, 0, 0);

		/* We abort if we can't map the stack */
			ASSERT(stackBasePtr != (int64_t *)MAP_FAILED,
					"Error: Couldn't map the buffer stack for the stacking invalid offsets.");

			stackTopPtr = stackBasePtr;
		}

	/* Now, we check if the offset we've got is one of the valid offsets */
		int64_t offset = unit2Addr - (subUnit1Addr << (uint64_t)SHADOW_SCALE);
		struct validOffset_struct *validOffsetNodePtr = validOffsetsListPtr;
		while(validOffsetNodePtr) {
			if(validOffsetNodePtr->validOffset == offset) {
			/* Since the offset matches what we need to do depends on what needs to
			 * be done. But first we need to 'empty' the stack.
			 */
				stackTopPtr = stackBasePtr;
				if(action == (int8_t)SHADOW_MAP) {
				/* We let the let the subroutine that maps shadow handle this conflict */
					return (int8_t)OFFSET_CONFLICT;
				}
				if(action == (int8_t) APP_MAP) {
				/* In this case we have to remap the app regions */
					if(!RemapAppRegion()) {
					/* If the application or its shadow mapping failes, we need to unmap
					 * the stack we already have in place.
					 */
						uint64_t stackSize =
							((uint64_t)1 << (47 - (uint64_t)SLOT_SHIFT + (uint64_t)SHADOW_SCALE))
															* sizeof(uint64_t);
						Sysmunmap((void *)stackBasePtr, stackSize);
						stackBasePtr = stackTopPtr = NULL;
					}

				/* If the application mapping was successful, it must have already been
				 * through the process of having all the invalid offsets added to the hash
				 * tablles and the shadow mapped. So all we need to do it exit since we are
				 * done.
				 */
					return (int8_t)CONFLICT_RESOLVED;
				}
			}
			validOffsetNodePtr = validOffsetNodePtr->nextNodePtr;
		}

	/* Now, we add the offset to the stack */
		*(stackTopPtr++) = offset;
	} else {
		uint64_t invalidOffsetsTablesMask =
				~((uint64_t)(~0) << (47 - (uint64_t)SLOT_SHIFT + (uint64_t)SHADOW_SCALE));
		struct invalidOffset_struct *invalidOffset_subUnitPtr;

	/* Now we save all stacked up invalid offsets in the scratch space hash tables */
		while(stackTopPtr != stackBasePtr) {
			if (*stackTopPtr < 0) {
			/* Take the absolute value of the negative offset to hash it into the table */
				uint64_t converted_offset =
						(uint64_t)((*stackTopPtr + (int64_t)(~0)) ^ ((int64_t)(~0)));
				uint64_t invalidOffsetsTablesOffset =
							(converted_offset >> (uint64_t)SLOT_SHIFT) & invalidOffsetsTablesMask;
				invalidOffset_subUnitPtr = negInvalidOffsetsTablePtr + invalidOffsetsTablesOffset;
			}
			else {
				uint64_t invalidOffsetsTablesOffset =
						(*stackTopPtr >> (uint64_t)SLOT_SHIFT) & invalidOffsetsTablesMask;
				invalidOffset_subUnitPtr = posInvalidOffsetsTablePtr + invalidOffsetsTablesOffset;
			}
			invalidOffset_subUnitPtr->invalidOffset = *stackTopPtr;
			(invalidOffset_subUnitPtr->numSubUnits)++;
			stackTopPtr--;
		}

	/* Then we unmap the stack */
		uint64_t stackSize =
				((uint64_t)1 << (47 - (uint64_t)SLOT_SHIFT + (uint64_t)SHADOW_SCALE)) * sizeof(uint64_t);
		Sysmunmap((void *)stackBasePtr, stackSize);
		stackBasePtr = stackTopPtr = NULL;
	}
	return 1;
}

void MapRegReservedSlots(uint64_t slotsBegAddr, uint64_t numSlots)
{
	if (validOffsetsListPtr->numRegSameOffset) {
		struct validOffset_struct *validOffsetNodePtr = validOffsetsListPtr;
		while (validOffsetNodePtr) {
			uint64_t countSlots = 0;
			uint64_t slotAddr = slotsBegAddr;
			while ((countSlots++) != numSlots) {
				MapRegSlotReservedUnits(slotAddr, validOffsetNodePtr->validOffset);
				slotAddr += (uint64_t)SLOT_SIZE;
			}
			validOffsetNodePtr = validOffsetNodePtr->nextNodePtr;
		}
	}
}

/* We map the reserved units for the all app and shadow units for the given
 * offset, except for the given range of app slots (since at the given offset,
 * the range has shadow. We also map the reserved units for the shadow(s) of
 * the given range of slots.
 */
void MapNewOffsetBasedReservedSlots(uint64_t avoidRegBegAddr,
																		uint64_t numAvoidRegSlots, int64_t newOffset)
{
	uint64_t numShadowSlots = (uint64_t) 1 << (uint64_t)SHADOW_SCALE;
	uint64_t avoidRegEndAddr = avoidRegBegAddr + (numAvoidRegSlots << (uint64_t)SLOT_SHIFT);
	struct appShadowAddrsNode* appShadowAddrsNodePtr = app_shadowListPtr;
	while (appShadowAddrsNodePtr) {
		if (!((appShadowAddrsNodePtr->appUnitAddr >= avoidRegBegAddr)
						&& (appShadowAddrsNodePtr->appUnitAddr < avoidRegEndAddr))) {
		/* Mapping the reserved slots for the application unit */
			MapRegSlotReservedUnits(appShadowAddrsNodePtr->appUnitAddr, newOffset);
			if (appShadowAddrsNodePtr->shadowUnitAddr) {
			/* Mapping the reserved slots for the corresponding shadow units */
				uint64_t shadowAddr = appShadowAddrsNodePtr->shadowUnitAddr;
				uint64_t countShadowSlots = 0;
				while ((countShadowSlots++) != numShadowSlots) {
					MapRegSlotReservedUnits(shadowAddr, newOffset);
					shadowAddr += (uint64_t)SLOT_SIZE;
				}
			}
		} else {
		/* For the given node, we map reserved units for the shadows for app address in this node */
			uint64_t shadowAddr = appShadowAddrsNodePtr->shadowUnitAddr;
			uint64_t countShadowSlots = 0;
			while ((countShadowSlots++) != numShadowSlots) {
				MapRegSlotReservedUnits(shadowAddr, newOffset);
				shadowAddr += (uint64_t)SLOT_SIZE;
			}
		}
		appShadowAddrsNodePtr = appShadowAddrsNodePtr->nextNodePtr;
	}
}

void MapRegSlotReservedUnits(uint64_t regSlotAddr, int64_t offset)
{
	uint64_t numReservedSlots = ((uint64_t) 1 << (uint64_t)SHADOW_SCALE);
	uint64_t reservedSlotAddr = (regSlotAddr << (uint64_t)SHADOW_SCALE) + offset;
	struct unitInfo *resUnitPtr = memLayoutTablePtr + (reservedSlotAddr >> (uint64_t)SLOT_SHIFT);
	uint64_t countReservedSlots = 0;
	while ((countReservedSlots++) != numReservedSlots) {
		if (!(reservedSlotAddr >> 47)) {
			if (!(resUnitPtr->offset == (int64_t) RESERVED_SLOT_OFFSET)) {
				uint64_t mmapPtr = (uint64_t)Sysmmap((void*) reservedSlotAddr, (uint64_t)SLOT_SIZE,
										PROT_NONE, MAP_SHARED | MAP_ANONYMOUS | MAP_NORESERVE, 0, 0);
				if(mmapPtr == (uint64_t)MAP_FAILED) {
				/* If the mapping failed, fill the empty space */
					Fill_EmptySpaces_in_Slots(reservedSlotAddr, 1);
				} else {
					if(mmapPtr != reservedSlotAddr) {
					/* If the mapping could not be scled, we fill the empty spaces */
						Sysmunmap((void *)mmapPtr, (uint64_t)SLOT_SIZE);
						Fill_EmptySpaces_in_Slots(reservedSlotAddr, 1);
					}
				}
				resUnitPtr->offset = (int64_t) RESERVED_SLOT_OFFSET;
			}
			(resUnitPtr->numReg)++;
			reservedSlotAddr += (uint64_t)SLOT_SIZE;
			resUnitPtr++;
		} else {
			break;
		}
	}
}


/*********************** MEMORY DEALLOCATOR **********************/

void UnmapAppRegion(uint64_t appSlotsBegAddr, uint64_t numAppSlots)
{
/* Just a sanity checkt to see oif number of app slots to free == zero. If yes,
 * there is noting to do.
 */
	if(!numAppSlots)
		return;

	struct unitInfo *appUnitPtr = memLayoutTablePtr + (appSlotsBegAddr >> (uint64_t)SLOT_SHIFT);
	uint64_t countAppSlots = 0;
	while (countAppSlots != numAppSlots) {
	/* Checking if the shadow map and its reserved slots need to be unmapped */
		if (!(--(appUnitPtr->numReg))) {
			struct appShadowAddrsNode *appShadowAddrsNodePtr;
			uint64_t appSlotAddr = appSlotsBegAddr + (countAppSlots << (uint64_t)SLOT_SHIFT);
			UnmapAppUnitMappedSlots(appSlotAddr);
			Remove_AppInfo_from_AppShadowInfoList(appSlotAddr);

		/* Setting the table info for an empty slot for free app unit */
			appUnitPtr->offset = (int64_t) EMPTY_SLOT_OFFSET;
			appUnitPtr->numReg = (uint64_t) NULL_NUM_SUB_REG;
		}
		countAppSlots++;
		appUnitPtr++;
	}
	Check_Vicinity_for_ScatchSpace(appSlotsBegAddr, numAppSlots);
	Subtract_InvalidOffsets(appSlotsBegAddr, numAppSlots);
}

void Remove_AppInfo_from_AppShadowInfoList(uint64_t appSlotAddr)
{
	struct appShadowAddrsNode *freeAppShadowEndPtr;
	struct appShadowAddrsNode *appShadowAddrsNodePtr;
	if (!freeAppShadowListPtr) {
		appShadowAddrsNodePtr = app_shadowListPtr;
		while (appShadowAddrsNodePtr->appUnitAddr != appSlotAddr) /* Walk the app shadow info list */
			appShadowAddrsNodePtr = appShadowAddrsNodePtr->nextNodePtr;
		freeAppShadowEndPtr = appShadowAddrsNodePtr;
		freeAppShadowListPtr = freeAppShadowEndPtr;
	} else {
	/* 	Reach the end of the free list */
		freeAppShadowEndPtr = freeAppShadowListPtr;
		while (freeAppShadowEndPtr->nextNodePtr)
			freeAppShadowEndPtr = freeAppShadowEndPtr->nextNodePtr;

	/* Walk the app shadow info list to look for the given slot address */
		appShadowAddrsNodePtr = app_shadowListPtr;
		while (appShadowAddrsNodePtr->appUnitAddr != appSlotAddr)
			appShadowAddrsNodePtr = appShadowAddrsNodePtr->nextNodePtr;

		freeAppShadowEndPtr->nextNodePtr = appShadowAddrsNodePtr;
		freeAppShadowEndPtr = freeAppShadowEndPtr->nextNodePtr;
	}
	if (freeAppShadowEndPtr != app_shadowListPtr) {
		appShadowAddrsNodePtr = app_shadowListPtr;
		while (appShadowAddrsNodePtr->nextNodePtr != freeAppShadowEndPtr)
			appShadowAddrsNodePtr = appShadowAddrsNodePtr->nextNodePtr;
		appShadowAddrsNodePtr->nextNodePtr = freeAppShadowEndPtr->nextNodePtr;
	} else {
		app_shadowListPtr = freeAppShadowEndPtr->nextNodePtr;
	}

/* Updating the information in the free node */
	freeAppShadowEndPtr->appUnitAddr = freeAppShadowEndPtr->shadowUnitAddr = 0;
	freeAppShadowEndPtr->nextNodePtr = NULL;
}

void Subtract_InvalidOffsets(uint64_t slotBegAddr, uint64_t numSlots)
{
	uint64_t numAppShadowSlots = ((uint64_t)1 << (uint64_t)SHADOW_SCALE);
	uint64_t countSlots = 0;
	while (countSlots != numSlots) {
		struct appShadowAddrsNode *addrsNodePtr = app_shadowListPtr;
		uint64_t unitAddr = slotBegAddr;
		while (addrsNodePtr) {
		/* To see if the addresses in the given range conflict with the ones in the list */
			bool addrConflictFound = false;
			if (unitAddr != addrsNodePtr->appUnitAddr) {
				if (addrsNodePtr->shadowUnitAddr) {
					uint64_t numShadowSlots = numAppShadowSlots;
					while (numShadowSlots--) {
						uint64_t curShadowSlotAddr = (addrsNodePtr->shadowUnitAddr)
																+ (numShadowSlots << (uint64_t)SLOT_SHIFT);
						if (unitAddr != curShadowSlotAddr)
							Subtract_UnitToUnit_2Way_InvalidOffsets(unitAddr, curShadowSlotAddr);
						else
							addrConflictFound = true;
					}
				}
				Subtract_UnitToUnit_1Way_InvalidOffset(unitAddr, addrsNodePtr->appUnitAddr);
			/*	Shadow address conflict is checked for since if there is a conflict
			 * the shadow address, the obtained offset is valid and should not be put
			 * in the invalid offset table.
			 */
				if (!addrConflictFound)
					Subtract_UnitToUnit_1Way_InvalidOffset(addrsNodePtr->appUnitAddr, unitAddr);
			}
			addrsNodePtr = addrsNodePtr->nextNodePtr;
			unitAddr += (uint64_t)SLOT_SIZE;
		}
		countSlots++;
	}
}

void Subtract_UnitToUnit_2Way_InvalidOffsets(uint64_t unit1Addr, uint64_t unit2Addr)
{
	uint64_t subUnitAddr;
	uint64_t numSubUnits = (uint64_t)1 << (uint64_t)SHADOW_SCALE;
	uint64_t subUnitSize = (uint64_t)SLOT_SIZE / numSubUnits;
	uint64_t countSubUnits =
			((uint64_t)1 << (uint64_t)SHADOW_SCALE); /* Equal to total number of subUnits in a unit */
	while (countSubUnits--) {
	/* Getting the subUnitAddr for the first unit that is scaled and added
	 * to an offset to get to the second unit.
	 */
		subUnitAddr = unit1Addr + (countSubUnits * subUnitSize);
		Subtract_SubUnit_to_Unit_InvalidOffsets(subUnitAddr, unit2Addr);

	/* Getting the subUnitAddr for second unit that is scaled and added to an
	 * offset to get to the first unit.
	 */
		subUnitAddr = unit2Addr + (countSubUnits * subUnitSize);
		Subtract_SubUnit_to_Unit_InvalidOffsets(subUnitAddr, unit1Addr);
	}
}

void Subtract_UnitToUnit_1Way_InvalidOffset(uint64_t from_unitAddr, uint64_t to_unitAddr)
{
	uint64_t subUnitAddr;
	uint64_t numSubUnits = (uint64_t)1 << (uint64_t)SHADOW_SCALE;
	uint64_t subUnitSize = (uint64_t)SLOT_SIZE / numSubUnits;
	uint64_t countSubUnits =
			((uint64_t)1 << (uint64_t)SHADOW_SCALE); /* Equal to total number of subUnits in a unit */
	while (countSubUnits--) {
		subUnitAddr = from_unitAddr + (countSubUnits * subUnitSize);
		Subtract_SubUnit_to_Unit_InvalidOffsets(subUnitAddr, to_unitAddr);
	}
}

/* Here the subUnit1 is treated as the subUnit that is scaled and added to an offset to get to unit2 */
void Subtract_SubUnit_to_Unit_InvalidOffsets(uint64_t subUnit1Addr, uint64_t unit2Addr)
{
	uint64_t invalidOffsetsTablesMask =
			~((uint64_t)(~0) << (47 - (uint64_t)SLOT_SHIFT + (uint64_t)SHADOW_SCALE));
	struct invalidOffset_struct *invalidOffset_subUnitPtr;
	int64_t offset = unit2Addr - (subUnit1Addr << (uint64_t)SHADOW_SCALE);
	if (offset < 0) {
	/* Take the absolute value of the negative offset to hash it into the table */
		uint64_t converted_offset = (uint64_t)((offset + (int64_t)(~0)) ^ ((int64_t)(~0)));
		uint64_t invalidOffsetsTablesOffset =
						(converted_offset >> (uint64_t)SLOT_SHIFT) & invalidOffsetsTablesMask;
		invalidOffset_subUnitPtr = negInvalidOffsetsTablePtr + invalidOffsetsTablesOffset;
	}
	else {
		uint64_t invalidOffsetsTablesOffset =
						(offset >> (uint64_t)SLOT_SHIFT) & invalidOffsetsTablesMask;
		invalidOffset_subUnitPtr = posInvalidOffsetsTablePtr + invalidOffsetsTablesOffset;
	}
	(invalidOffset_subUnitPtr->numSubUnits)--;
	if(!(invalidOffset_subUnitPtr->numSubUnits))
		invalidOffset_subUnitPtr->invalidOffset = 0;
}

void Reverse_changes_to_MemLayoutTable_for_Scratch(uint64_t scratchLowSlotAddr,
													uint64_t scratchHighSlotAddr)
{
	uint64_t numSlots = (scratchHighSlotAddr - scratchLowSlotAddr) >> (uint64_t)SLOT_SHIFT;
	struct unitInfo *unitPtr = memLayoutTablePtr + (scratchLowSlotAddr >> (uint64_t)SLOT_SHIFT);
	uint64_t countSlots = 0;
	while((countSlots++) != numSlots) {
		if(unitPtr->numReg == 1)
			unitPtr->offset = (int64_t)SCRATCH_UNIT_OFFSET;
		unitPtr++;
	}
}

int64_t Unmark_AppUnits_to_Scratch(uint64_t regSlotsBegAddr, uint64_t numRegSlots)
{
	uint64_t scratchBegSlotsAddr = scratchSpaceInfoPtr->scratchSlotsBegAddr;
	uint64_t scratchEndSlotsAddr = scratchBegSlotsAddr
						+ (scratchSpaceInfoPtr->numScratchSlots << (uint64_t)SLOT_SHIFT);
	uint64_t regSlotsEndAddr = regSlotsBegAddr + (numRegSlots << (uint64_t)SLOT_SHIFT);

/* Considering the case where the scratch space is a subset of the given region */
	if(scratchBegSlotsAddr >= regSlotsBegAddr && scratchEndSlotsAddr <= regSlotsEndAddr) {
		if(scratchSpaceInfoPtr->numScratchSlots == numRegSlots) {
			Reverse_changes_to_MemLayoutTable_for_Scratch(scratchBegSlotsAddr, scratchEndSlotsAddr);
			return (int64_t)SCRATCH_OUT_APP_REG;
		}
	} else {
	/* Considering the case where scratch unit(s) is(are) outside the domain of the given region
	* on the lower address side.
	*/
		if(scratchBegSlotsAddr < regSlotsBegAddr) {
			if(scratchEndSlotsAddr > regSlotsBegAddr && scratchEndSlotsAddr <= regSlotsEndAddr) {
				if(scratchSpaceInfoPtr->numScratchSlots == numRegSlots + 1) {
					Reverse_changes_to_MemLayoutTable_for_Scratch(regSlotsBegAddr, scratchEndSlotsAddr);
					return (int64_t)SCRATCH_IN_APP_REG;
				}
			}
		} else {
		/* Considering the case where scratch unit(s) is(are) outside the domain of the given region
		* on the higher address side.
		*/
			if(scratchEndSlotsAddr > regSlotsEndAddr) {
				if(scratchBegSlotsAddr >= regSlotsBegAddr
				&& scratchBegSlotsAddr < regSlotsEndAddr) {
					if(scratchSpaceInfoPtr->numScratchSlots == numRegSlots + 1) {
						Reverse_changes_to_MemLayoutTable_for_Scratch(scratchBegSlotsAddr, regSlotsEndAddr);
						return (int64_t)SCRATCH_IN_APP_REG;
					}
				}
			}
		}
	}
	return (int64_t)SCRATCH_IRRELEVANT;
}

void Check_Vicinity_for_ScatchSpace(uint64_t appSlotsBegAddr, uint64_t numAppSlots)
{
	uint64_t numLowAppSlots = NumAppSlots_VicinityLowAppUnits(appSlotsBegAddr);
	uint64_t numHighAppSlots =
		NumAppSlots_VicinityHighAppUnits(appSlotsBegAddr + (numAppSlots << (uint64_t)SLOT_SHIFT));

/*  Checking the slots in the vicinity Now, if the scratch units are not
 * immediately close to the app region slots, function simply returns.
 */
	int64_t scratchPos = Unmark_AppUnits_to_Scratch(appSlotsBegAddr
										- (numLowAppSlots << (uint64_t)SLOT_SHIFT), numLowAppSlots);
	if(scratchPos == (int64_t)SCRATCH_IRRELEVANT) {
		scratchPos = Unmark_AppUnits_to_Scratch(appSlotsBegAddr
									+ (numHighAppSlots << (uint64_t)SLOT_SHIFT), numHighAppSlots);
		if(scratchPos == (int64_t)SCRATCH_IRRELEVANT)
			return;
	}

/* If the scratch untit(s) is/are immediately outside the app region end slots,
 * we return after the called function returns
*/
	if(scratchPos == (int64_t)SCRATCH_OUT_APP_REG)
		return;

/* This code is executed when one of the  end slots of the app reg slots, is scratch unit */
	uint64_t scratchBegSlotsAddr = scratchSpaceInfoPtr->scratchSlotsBegAddr;
	uint64_t scratchEndSlotsAddr = scratchBegSlotsAddr
									+ (scratchSpaceInfoPtr->numScratchSlots << (uint64_t)SLOT_SHIFT);

/* Checks if the lower end is a scratch unit */
	uint64_t appLowEndSlotAddr = appSlotsBegAddr;
	if(appLowEndSlotAddr >= scratchBegSlotsAddr && appLowEndSlotAddr < scratchEndSlotsAddr) {
		struct unitInfo *unitPtr = memLayoutTablePtr + (appLowEndSlotAddr >> (uint64_t)SLOT_SHIFT);
		if(unitPtr->numReg == 1) {
			Safe_Reverse_Changes_on_ScratchUnits(appSlotsBegAddr, numAppSlots,
															unitPtr->offset, PROT_NONE);
			Reverse_changes_to_MemLayoutTable_for_Scratch(appLowEndSlotAddr,
														appLowEndSlotAddr + (uint64_t)SLOT_SIZE);
		}
	} else {
	/* Checks if the higher end is a scratch unit */
		uint64_t appHighEndSlotAddr = appSlotsBegAddr + ((numAppSlots - 1) << (uint64_t)SLOT_SHIFT);
		struct unitInfo *unitPtr = memLayoutTablePtr + (appHighEndSlotAddr >> (uint64_t)SLOT_SHIFT);
		if(unitPtr->numReg == 1) {
			Safe_Reverse_Changes_on_ScratchUnits(appSlotsBegAddr, numAppSlots,
															unitPtr->offset, PROT_NONE);
			Reverse_changes_to_MemLayoutTable_for_Scratch(appHighEndSlotAddr,
														appHighEndSlotAddr + (uint64_t)SLOT_SIZE);
		}
	}
}

void Unmap_OffsetSpecific_ReservedUnits(uint64_t regSlotAddr, int64_t offset)
{
	uint64_t numReservedSlots = ((uint64_t) 1 << (uint64_t)SHADOW_SCALE);
	uint64_t reservedSlotAddr = (regSlotAddr << (uint64_t)SHADOW_SCALE) + offset;
	struct unitInfo *resUnitPtr = memLayoutTablePtr + (reservedSlotAddr >> (uint64_t)SLOT_SHIFT);
	uint64_t countReservedSlots = 0;
	while ((countReservedSlots++) != numReservedSlots) {
		if (!(reservedSlotAddr >> 47)) {
			if (resUnitPtr->offset == (int64_t)RESERVED_SLOT_OFFSET) {
				if (!(--(resUnitPtr->numReg))) {
					Sysmunmap((void*) reservedSlotAddr, (uint64_t)SLOT_SIZE);
					resUnitPtr->offset = (int64_t)EMPTY_SLOT_OFFSET;
					resUnitPtr->numReg = (uint64_t)NULL_NUM_SUB_REG;
				}
			}
			reservedSlotAddr += (uint64_t)SLOT_SIZE;
			resUnitPtr++;
		} else {
			break;
		}
	}
}

void MunmapShadowMemSlots(uint64_t appSlotsBegAddr, uint64_t numAppSlots)
{
/* Freeing the valid offsets and reserved units */
	struct unitInfo* appUnitPtr = memLayoutTablePtr + (appSlotsBegAddr >> (uint64_t)SLOT_SHIFT);
	FreeValidOffset_and_ReservedSlots(appUnitPtr->offset, numAppSlots);

/* Getting rid of invalid offsets(if possible) */
	uint64_t shadowSlotAddr = (appSlotsBegAddr << (uint64_t)SHADOW_SCALE) + appUnitPtr->offset;
	struct unitInfo* shadowUnitPtr = memLayoutTablePtr + (shadowSlotAddr >> (uint64_t)SLOT_SHIFT);
	uint64_t numShadowSlots = (numAppSlots << (uint64_t)SHADOW_SCALE);
	Subtract_InvalidOffsets(shadowSlotAddr, numShadowSlots);

/* Unmapping the shadow regions and their associated reserved units */
	uint64_t countShadowSlots = 0;
	while ((countShadowSlots++) != numShadowSlots) {
		UnmapRegUnitReservedSlots(shadowSlotAddr);
		Sysmunmap((void*) shadowSlotAddr, (uint64_t)SLOT_SIZE);
		shadowUnitPtr->offset = (int64_t)EMPTY_SLOT_OFFSET;
		shadowUnitPtr->numReg = (uint64_t)NULL_NUM_SUB_REG;
		shadowUnitPtr++;
		shadowSlotAddr += (uint64_t)SLOT_SIZE;
	}
}

void FreeValidOffset_and_ReservedSlots(int64_t offset, uint64_t numAppSlots)
{
/* Managing the valid offsets list and its free list */
	struct validOffset_struct *validOffsetNodePtr = validOffsetsListPtr;
	while (validOffsetNodePtr->validOffset != offset) {
		validOffsetNodePtr = validOffsetNodePtr->nextNodePtr;
	}
	if (!(validOffsetNodePtr->numRegSameOffset -= numAppSlots)) {
	/* Unmap the reserved slots associated with this offset */
		Unmap_ValidOffset_Based_ReservedSlots(offset);
		struct validOffset_struct *freeValidOffsetsEndPtr = freeValidOffsetsListPtr;
		if (freeValidOffsetsListPtr) {
		/* 	Reach the end of the free list */
			while (freeValidOffsetsEndPtr->nextNodePtr)
				freeValidOffsetsEndPtr = freeValidOffsetsEndPtr->nextNodePtr;
		}
		if (!freeValidOffsetsListPtr) {
			freeValidOffsetsEndPtr = validOffsetNodePtr;
			freeValidOffsetsListPtr = freeValidOffsetsEndPtr;
		} else {
			freeValidOffsetsEndPtr->nextNodePtr = validOffsetNodePtr;
			freeValidOffsetsEndPtr = freeValidOffsetsEndPtr->nextNodePtr;
		}
		if (freeValidOffsetsEndPtr != validOffsetsListPtr) {
			validOffsetNodePtr = validOffsetsListPtr;
			while (validOffsetNodePtr->nextNodePtr != freeValidOffsetsEndPtr) /* Walk the list */
				validOffsetNodePtr = validOffsetNodePtr->nextNodePtr;
			validOffsetNodePtr->nextNodePtr = freeValidOffsetsEndPtr->nextNodePtr;
		} else {
			validOffsetsListPtr = freeValidOffsetsEndPtr->nextNodePtr;
		}

	/* Update freed valid offset node */
		freeValidOffsetsEndPtr->validOffset = 0;
		freeValidOffsetsEndPtr->numRegSameOffset = 0;
		freeValidOffsetsEndPtr->nextNodePtr = NULL;
	}
}

void Unmap_ValidOffset_Based_ReservedSlots(int64_t freedValidOffset)
{
	uint64_t numShadowSlots = ((uint64_t) 1 << (uint64_t)SHADOW_SCALE);
	struct appShadowAddrsNode* appShadowAddrsNodePtr = app_shadowListPtr;
	while (appShadowAddrsNodePtr) {
	/* Unmapping the reserved slots for the application unit */
		Unmap_OffsetSpecific_ReservedUnits(appShadowAddrsNodePtr->appUnitAddr,
																freedValidOffset);
		if (appShadowAddrsNodePtr->shadowUnitAddr) {
		/* Unmapping the reserved slots for the corresponding shadow units */
			uint64_t shadowAddr = appShadowAddrsNodePtr->shadowUnitAddr;
			uint64_t countShadowSlots = 0;
			while ((countShadowSlots++) != numShadowSlots) {
				Unmap_OffsetSpecific_ReservedUnits(shadowAddr, freedValidOffset);
				shadowAddr += (uint64_t)SLOT_SIZE;
			}
		}
		appShadowAddrsNodePtr = appShadowAddrsNodePtr->nextNodePtr;
	}
}

void UnmapAppUnitMappedSlots(uint64_t regSlotAddr)
{
	struct validOffset_struct *validOffsetNodePtr = validOffsetsListPtr;
	uint64_t numMappedSlots = ((uint64_t) 1 << (uint64_t)SHADOW_SCALE);
	while (validOffsetNodePtr) {
		uint64_t slotAddr =
				(regSlotAddr << (uint64_t)SHADOW_SCALE) + (validOffsetNodePtr->validOffset);
		if (!(slotAddr >> 47)) {
			struct unitInfo* unitPtr = memLayoutTablePtr + (slotAddr >> (uint64_t)SLOT_SHIFT);
			if (unitPtr->offset != (int64_t) SHADOW_SLOT_OFFSET) {
			/* Unmapping the reserved slots for app slot */
				uint64_t countSlots = 0;
				while ((countSlots++) != numMappedSlots) {
					if (!(--(unitPtr->numReg))) {
						Sysmunmap((void*) slotAddr, (uint64_t)SLOT_SIZE);
						unitPtr->offset = (int64_t) EMPTY_SLOT_OFFSET;
						unitPtr->numReg = (uint64_t) NULL_NUM_SUB_REG;
					} else
						(unitPtr->offset)--;
					unitPtr++;
					slotAddr += (uint64_t)SLOT_SIZE;
				}
			} else {
			/* Unmapping the shadow slots and their reserved slots */
				MunmapShadowMemSlots(regSlotAddr, 1);
			}
		}
		validOffsetNodePtr = validOffsetNodePtr->nextNodePtr;
	}
}

void UnmapRegUnitReservedSlots(uint64_t regSlotAddr)
{
	struct validOffset_struct* validOffsetNodePtr = validOffsetsListPtr;
	while (validOffsetNodePtr) {
		Unmap_OffsetSpecific_ReservedUnits(regSlotAddr, validOffsetNodePtr->validOffset);
		validOffsetNodePtr = validOffsetNodePtr->nextNodePtr;
	}
}


/********************* SHADOW MAP MANAGER DESTRUCTOR **************************/

void CleanUp_ShadowMap_and_Resources(void)
{
#ifdef COUNT_SHADOW_PAGEFAULTS
/* Print the total number of page faults handled to switch shadow offsets */
	DEBUG_PRINTF("Number of page shadows handled by shadow manager: %p  %d\n",
											numPageFaults, numPageFaults);
#endif

/* Unmap all the shadow and reserved units */
	struct appShadowAddrsNode *appShadowNodePtr = app_shadowListPtr;
	while (appShadowNodePtr) {
		UnmapAppUnitMappedSlots(appShadowNodePtr->appUnitAddr);
		appShadowNodePtr  = appShadowNodePtr->nextNodePtr;
	}

	DEBUG_PRINTF(">>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>\n");
/* Unmap the scratch space */
	uint64_t scratchSpaceBegAddr = scratchSpaceInfoPtr->scratchSpaceAddr;
	uint64_t scratchSpaceSize =
			RoundUpSize_to_PageSizeMultiple(scratchSpaceInfoPtr->scratchSpaceSize);

	DEBUG_PRINTF("intial scratch space size: %p\n", scratchSpaceInfoPtr->scratchSpaceSize);
	DEBUG_PRINTF("scratch space size: %p\n", scratchSpaceSize);
	DEBUG_PRINTF("SCRATCH SPACE ADDR: %p\n", scratchSpaceBegAddr);
	//PrintProcLayout();
	Sysmunmap((void *)scratchSpaceBegAddr, scratchSpaceSize);

#ifdef BLOCK_HEAP
/* Unmap the page that blocks the system heap */
	Sysmunmap((void *)Syssbrk(0), (uint64_t)sysconf(_SC_PAGESIZE));
#endif
}


/*********************************** WRAPPER FUNCTIONS *************************************/

#ifndef USE_GNU_MALLOC
void *MapHeapBlock_and_Shadow(void *appRegBegAddr, size_t appRegSize,
									int prot, int flags, int fd, off_t offset)
{
	//DEBUG_PRINTF("MAPPING HEAP BLOCK\n");

/* Map the region that needs to be mapped. This has to be used only for mapping
 * heap bags and that and also shadow for them. Since it is only to be used for
 * HeapGuard, this function does not have to do extra alignment checks.
 */
	uint64_t mmapPtr = (uint64_t)Sysmmap(appRegBegAddr, appRegSize, prot, flags, fd, offset);
	if(mmapPtr == (uint64_t)MAP_FAILED)
		return (void *)MAP_FAILED;
	if(mmapPtr == (uint64_t)appRegBegAddr)
		return (void *)mmapPtr;

/* Map shadow now that the block has been mapped properly */
	struct regSlotsInfo appSlotsInfo;
	Get_RegSlotsInfo(mmapPtr, appRegSize, &appSlotsInfo);
	MapAppRegion(appSlotsInfo.regSlotsBegAddr, appSlotsInfo.numRegSlots);

	//DEBUG_PRINTF("BAG ADDR: %p\n", mmapPtr);
	//DEBUG_PRINTF("SHADOW ADDRESS: %p\n", (mmapPtr << (uint64_t)SHADOW_SCALE) + shadowOffsets[0]);
	//DEBUG_PRINTF("SHADOW ADDRESS for 0x7fe7d0000000: %p\n", ((0x7fe7d0000000) << (uint64_t)SHADOW_SCALE) + shadowOffsets[0]);
	//PrintValidOffsetsList();
	//PrintProcLayout();
	return (void *)mmapPtr;
}
#endif

/* Wrapper function for malloc */
void *malloc(size_t size)
{
/* It is possible that the application can happen to use heap before shadow
 * memory library gets access to it.
 */
	if(shadowManagerState == (int8_t)SHADOW_UNINITIALIZED) {
		DEBUG_PRINTF("MALLOC: SHADOW UNINITIALIZED\n");
		Init_ShadowMapManager();
	}

#ifdef USE_GNU_MALLOC
	//DEBUG_PRINTF("GNU MALLOC\n");
/* Implement the real malloc */
	uint64_t mallocPtr = (uint64_t) Sysmalloc(size);
	if(!mallocPtr)
		return (void *)mallocPtr;

/* Malloc's glibc implementation uses __mmap function that uses INLINE_SYSCALL
 * which deals with the internal system call implementation due to which we do
 * not get the opportunity to wrap mmap. __mmap is a weak_alias of mmap. So we
 * put a couple of checks to see if mmap was internally implemented.
 */
	int saved_errno = errno;
#ifndef BLOCK_HEAP
	if(mallocPtr >= (uint64_t)Syssbrk(0)) {
#endif
	/* We get the pointer to the metadata for the malloced chunk and see
	 * how the allocation took place.
	 */
		struct chunk_info *ptr_to_metadata =
				(struct chunk_info *)(mallocPtr - heapInfoPtr->alloc_chunkInfo_size);

	/* One option is that either a new arena was mapped or an existing heap
	 * was expanded or non-contiguous main heap is mapped or reused so we just
	 * confirm by checking if the NON_MAIN_ARENA and PREV_INUSE bits are set
	 * just to be safe.
	 */
		if((ptr_to_metadata->mchunk_size) & PREV_INUSE) {
		/* We just check if the metadata for heap is not corrupt. If it is, we quit */
			ASSERT(!((ptr_to_metadata->mchunk_size & IS_MMAPPED)),
				"Heap metadata is corrupt. Both IS_MAPPED and PREV_INUSE bits cannot be set.");

		/* The chunk size has to be a multiple of 8 */
			uint64_t chunkSize = ptr_to_metadata->mchunk_size & ((uint64_t)(~0) << 3);
			if(ptr_to_metadata->mchunk_size & NON_MAIN_ARENA) {
			/* In order to improve performance, we depend on the fact the most of
			 * the time the application is likely to use the already-mapped heap
			 * rather than mmap new arena frequently. So we store some information
			 * about the previously mmaped and used non-main arena so we can quickly
			 * check if the given area has been allocated in the most recently used
			 * mmaped heap. If it is not, it must belong to some other mapped heap.
			 */
				if((uint64_t)ptr_to_metadata > mmapped_heap_addr
				&& ((uint64_t)ptr_to_metadata + chunkSize < mmapped_heap_addr + mmapped_heap_size)) {
				/* We first check if the chunk is mapped */
					uint64_t pageAligned_ptr_to_metadata =
							(uint64_t)ptr_to_metadata & (sysPageInfoPtr->pageMask);
					uint64_t page_rounded_chunkSize = RoundUpSize_to_PageSizeMultiple(chunkSize);
					ASSERT(Sysmsync((void *)pageAligned_ptr_to_metadata,
							page_rounded_chunkSize, MS_ASYNC) != -1,
								"Error: Non-main arena chunk is not mmaped. "
											"Possibly the metadata is corrupt.");

				/* Once we know the allocation took place in an existing mapped heap, we're done */
					errno = saved_errno; /* restoring the value of errno to retain transparency */
					return (void *)mallocPtr;
				}

			/* We need to figure out if a new arena was mapped or allocation
			 * took place within an existing arena. So we do a light-weight
			 * check to see if the app units enclosing the arena already have
			 * shadow and reserved units. We attempt to access the metadata for heap.
			 */
				uint64_t heap_addr = mmapped_heap_addr =
						(uint64_t)ptr_to_metadata & sysPageInfoPtr->pageMask;
				uint64_t page_rounded_heapSize = mmapped_heap_size =
						RoundUpSize_to_PageSizeMultiple(((struct heap_info *)heap_addr)->size);

			/* Now we check if the heap is really mapped */
				ASSERT(Sysmsync((void *)heap_addr, page_rounded_heapSize, MS_ASYNC) != -1,
								"Non-main heap not mmaped. Possibly the metadata is corrupt.");

				appMappingInfoPtr->mapping_type = (int8_t)MALLOC_MAPPING_USED;
				appMappingInfoPtr->mmapped_addr = mallocPtr;

			/* Now we can work on mapping the shadow that we have all the info we need */
				struct regSlotsInfo heapSlotsInfo;
				Get_RegSlotsInfo(heap_addr, ((struct heap_info *)heap_addr)->size, &heapSlotsInfo);
				MapAppRegion(heapSlotsInfo.regSlotsBegAddr, heapSlotsInfo.numRegSlots);

				mallocPtr = appMappingInfoPtr->mmapped_addr;
				appMappingInfoPtr->mmapped_addr = 0;
				appMappingInfoPtr->mapping_type = (int8_t)NO_MAPPING_USED;
			} else {
			/* This means that the mmaped main arena (the non-contiguous extention of it)
			 * was used by real malloc. It is possible to allocate multiple chunks in the
			 * single mapping. It is most likely to be a non-contiguous main heap.
			 * First we check that the pages containing the non-main arena mapping are mapped.
			 */
				uint64_t pageAligned_ptr_to_metadata =
						(uint64_t)ptr_to_metadata & (sysPageInfoPtr->pageMask);
				uint64_t page_rounded_chunkSize = RoundUpSize_to_PageSizeMultiple(chunkSize);
				ASSERT(Sysmsync((void *)pageAligned_ptr_to_metadata,
									page_rounded_chunkSize, MS_ASYNC) != -1,
							"Error: Non-contiguous main arena chunk is not mmaped. "
					"								Possibly the metadata is corrupt.");

			/* If chunk pointer is page aligned, possibly a new non-contiguous main heap.
			 * Else an existing one is used.
			 */
				if(!((uint64_t)ptr_to_metadata & (~(sysPageInfoPtr->pageMask)))) {
					appMappingInfoPtr->mapping_type = (int8_t)MALLOC_MAPPING_USED;
					appMappingInfoPtr->mmapped_addr = mallocPtr;

					struct regSlotsInfo mainHeap_slotsInfo;
					Get_RegSlotsInfo((uint64_t)ptr_to_metadata,
										ptr_to_metadata->mchunk_size, &mainHeap_slotsInfo);
					MapAppRegion(mainHeap_slotsInfo.regSlotsBegAddr, mainHeap_slotsInfo.numRegSlots);

					mallocPtr = appMappingInfoPtr->mmapped_addr;
					appMappingInfoPtr->mmapped_addr = 0;
					appMappingInfoPtr->mapping_type = (int8_t)NO_MAPPING_USED;
				}
			}
		} else {
		/* We just check if the metadata for heap is not corrupt. If it is, we quit */
			ASSERT(!((ptr_to_metadata->mchunk_size & NON_MAIN_ARENA)),
					"Heap metadata corrupt. Neither PREV_INUSE not set nor NON_MAIN_ARENA set.\n");
			ASSERT(ptr_to_metadata->mchunk_size & IS_MMAPPED,
					"Heap metadata corrupt. Neither PREV_INUSE not set nor IS_MMAPED set.\n");

		/* Just to be safe, we check if the metadata pointer corresponding to malloc
		 * pointer is page aligned.
		 */
			ASSERT(!((uint64_t)ptr_to_metadata & (~sysPageInfoPtr->pageMask)),
					 "Chunk metadata pointer not page aligned for mmaped chunk.");

			appMappingInfoPtr->mapping_type = (int8_t)MALLOC_MAPPING_USED;
			appMappingInfoPtr->mmapped_addr = mallocPtr;

		/* If it is mmaped, we try to get the starting address of the mmap by getting
		 * the page address the given pointer belongs to and use the size to shadow
		 * map it. We first get the size of th map from the metaData. This is not
		 * safe but this is the best choice we've got to get the size of the map.
		 */
			uint64_t mmaped_size = (ptr_to_metadata->mchunk_size) & ((uint64_t)(~0) << 3);

		/* We get the information about the slots that enclose the mmaped region,
		 * and then we map its shadow and reserved units.
		 */
			struct regSlotsInfo mmaped_regSlotsInfo;
			Get_RegSlotsInfo((uint64_t)ptr_to_metadata, mmaped_size, &mmaped_regSlotsInfo);
			MapAppRegion(mmaped_regSlotsInfo.regSlotsBegAddr, mmaped_regSlotsInfo.numRegSlots);

			mallocPtr = appMappingInfoPtr->mmapped_addr;
			appMappingInfoPtr->mmapped_addr = 0;
			appMappingInfoPtr->mapping_type = (int8_t)NO_MAPPING_USED;
		}

#ifndef BLOCK_HEAP
	} else {
	/* This means that that the main arena was extended. If the the heap size
	 * exceeds the heap size for which the shadow has already been accounted
	 * for, we extend the heap limits kept track of by the scratch heap struct.
	 * We treat the heap extention as a new application region.
	 */
		if((uint64_t)Syssbrk(0) > heapInfoPtr->heapBase + heapInfoPtr->heapSoftLimit) {
			struct regSlotsInfo heapExtention_slotsInfo;
			uint64_t old_heapSoftLimit = heapInfoPtr->heapSoftLimit;
			uint64_t heapExtentionSize = (uint64_t)1 << 29;  /* extend the heap virtually by 500Mb */
			heapInfoPtr->heapSoftLimit += heapExtentionSize;  /* Now we update the saved heap soft limit */
			Get_RegSlotsInfo(heapInfoPtr->heapBase + old_heapSoftLimit,
								heapExtentionSize, &heapExtention_slotsInfo);
			MapAppRegion(heapExtention_slotsInfo.regSlotsBegAddr,
								heapExtention_slotsInfo.numRegSlots);
		}
	}
#endif
	errno = saved_errno; /* restoring the value of errno to retain transparency */
	return (void *)mallocPtr;

#else
/* Allocate memory using Heap guard */
	return Heap_malloc(size);
#endif
}

/* Wrapper for calloc */
void *calloc(size_t nmem, size_t memsize)
{
	if(shadowManagerState == (int8_t)SHADOW_UNINITIALIZED) {
		Init_ShadowMapManager();
	} else {
		if(shadowManagerState == (int8_t)SHADOW_INITIALIZING) {
		/* A buffer that stores dlsym metadata. We just allocate at least 4Kb
		 * of space which should be good enough. This way, we do not have to
		 * extend the heap and not be able to wrap sbrk(). The metadata should
		 * actually take less than 400 bytes, but we just want to be safe.
		 */
			static uint8_t dlsym_buffer_space[(uint64_t)1 << 12];
			static uint64_t dlsymBufferPtr = (uint64_t)dlsym_buffer_space;
			uint64_t allocSize = nmem * memsize;

		/* Allocation sizes should be multiples of 8 for 64-bit architecture systems */
			if(allocSize % 8)
				allocSize = ((allocSize >> 3) + 1) << 3;
			uint64_t old_bufPtr = dlsymBufferPtr;
			dlsymBufferPtr += allocSize;
			return (void *)old_bufPtr;
		}
	}

#ifdef USE_GNU_MALLOC
/* This helps implementing real calloc */
	uint64_t callocPtr = (uint64_t) Syscalloc(nmem, memsize);

/* We are done if calloc return value is NULL */
	if(!callocPtr)
		return (void *)callocPtr;

/* calloc's glibc implementation uses __mmap function that uses
 * INLINE_SYSCALL which deals with the internal system call
 * implementation due to which we do not get the opportunity to wrap
 * mmap. __mmap is a weak_alias of mmap. So we put a couple of checks
 * to see if mmap was internally implemented.
*/
	int saved_errno = errno;
#ifndef BLOCK_HEAP
	if(callocPtr >= (uint64_t)Syssbrk(0)) {
#endif
	/* We get the pointer to the metadata to analyze how the allocation took place */
		struct chunk_info *ptr_to_metadata =
				(struct chunk_info *)(callocPtr - heapInfoPtr->alloc_chunkInfo_size);

	/* One option is that either a new arena was mapped or an existing heap
	 * was expanded or non-contiguous main heap is mapped or reused so we
	 * just confirm by checking if the NON_MAIN_ARENA and PREV_INUSE bits
	 * are set just to be safe.
	 */
		if((ptr_to_metadata->mchunk_size) & PREV_INUSE) {
		/* We just check if the metadata for heap is not corrupt. If it is, we quit */
			ASSERT(!((ptr_to_metadata->mchunk_size & IS_MMAPPED)),
					"Heap metadata is corrupt. Both IS_MAPPED and PREV_INUSE bits cannot be set.");

			uint64_t chunkSize = (ptr_to_metadata->mchunk_size) & ((uint64_t)(~0) << 3);
			if((ptr_to_metadata->mchunk_size) & NON_MAIN_ARENA) {
			/* In order to improve performance, we depend on the fact the
			 * most of the time the application is likely to use the already-mapped
			 * heap rather than mmap new arena frequently. So we store some information
			 * about the previously mmaped and used non-main arena so we can quickly
			 * check if the given area has been allocated in the most recently used
			 * mmaped heap. If it is not, it must belong to some other mapped heap.
			 */
				if((uint64_t)ptr_to_metadata > mmapped_heap_addr
						&& ((uint64_t)ptr_to_metadata + chunkSize
								< mmapped_heap_addr + mmapped_heap_size)) {
				/* We first check if the chunk is mapped */
					uint64_t pageAligned_ptr_to_metadata =
							(uint64_t)ptr_to_metadata & (sysPageInfoPtr->pageMask);
					uint64_t page_rounded_chunkSize = RoundUpSize_to_PageSizeMultiple(chunkSize);
					ASSERT(Sysmsync((void *)pageAligned_ptr_to_metadata,
											page_rounded_chunkSize, MS_ASYNC) != -1,
								"Error: Non-main arena chunk is not mmaped. "
												"Possibly the metadata is corrupt.");

				/* Once we know the allocation took place in an existing mapped heap, we're done */
					errno = saved_errno; /* restoring the value of errno to retain transparency */
					return (void *)callocPtr;
				}

			/* We need to figure out if a new arena was mapped or allocation
			 * took place within an existing arena. So we do a light-weight
			 * check to see if the app units enclosing the arena already have
			 * shadow and reserved units. We attempt to access the metadata for heap.
			 */
				uint64_t heap_addr = mmapped_heap_addr =
						(uint64_t)ptr_to_metadata & sysPageInfoPtr->pageMask;
				uint64_t page_rounded_heapSize = mmapped_heap_size =
						RoundUpSize_to_PageSizeMultiple(((struct heap_info *)heap_addr)->size);

			/* Now we check if the heap is really mapped */
				ASSERT(Sysmsync((void *)heap_addr, page_rounded_heapSize, MS_ASYNC) != -1,
							"Non-main heap not mmaped. Possibly the metadata is corrupt.");

				appMappingInfoPtr->mapping_type = (int8_t)CALLOC_MAPPING_USED;
				appMappingInfoPtr->mmapped_addr = callocPtr;

			/* Now we can work on mapping the shadow that we have all the info we need */
				struct regSlotsInfo heapSlotsInfo;
				Get_RegSlotsInfo(heap_addr, ((struct heap_info *)heap_addr)->size, &heapSlotsInfo);
				MapAppRegion(heapSlotsInfo.regSlotsBegAddr, heapSlotsInfo.numRegSlots);

				callocPtr = appMappingInfoPtr->mmapped_addr;
				appMappingInfoPtr->mmapped_addr = 0;
				appMappingInfoPtr->mapping_type = (int8_t)NO_MAPPING_USED;
			} else {
			/* This means that the mmaped main arena (the non-contiguous extention of it) was used
			 * by real_calloc. It is possible to allocate multiple chunks in the single mapping.
			 * It is most likely to be a non-contiguous main heap.
			 * First we check that the pages containing the non-main arena mapping are mapped.
			 */
				uint64_t pageAligned_ptr_to_metadata =
						(uint64_t)ptr_to_metadata & (sysPageInfoPtr->pageMask);
				uint64_t page_rounded_chunkSize = RoundUpSize_to_PageSizeMultiple(chunkSize);
				ASSERT(Sysmsync((void *)pageAligned_ptr_to_metadata,
								page_rounded_chunkSize, MS_ASYNC) != -1,
						"Error: Non-contiguous main arena chunk is not mmaped. "
												"Possibly the metadata is corrupt.");

			/* If the chunk pointer is page aligned, possibly a new
			 * non-contiguous main heap. Else an existing one is used.
			 */
				if((uint64_t)ptr_to_metadata & (~sysPageInfoPtr->pageMask)) {
					appMappingInfoPtr->mapping_type = (int8_t)CALLOC_MAPPING_USED;
					appMappingInfoPtr->mmapped_addr = callocPtr;

					struct regSlotsInfo mainHeap_slotsInfo;
					Get_RegSlotsInfo((uint64_t)ptr_to_metadata,
							ptr_to_metadata->mchunk_size, &mainHeap_slotsInfo);
					MapAppRegion(mainHeap_slotsInfo.regSlotsBegAddr, mainHeap_slotsInfo.numRegSlots);

					callocPtr = appMappingInfoPtr->mmapped_addr;
					appMappingInfoPtr->mapping_type = (int8_t)NO_MAPPING_USED;
					appMappingInfoPtr->mmapped_addr = 0;
				}
			}
		} else {
		/* We just check if the metadata for heap is not corrupt. If it is, we quit */
			ASSERT(!((ptr_to_metadata->mchunk_size & NON_MAIN_ARENA)),
								"Heap metadata corrupt. Neither PREV_INUSE not set "
										"nor NON_MAIN_ARENA set.\n");
			ASSERT(ptr_to_metadata->mchunk_size & IS_MMAPPED,
								"Heap metadata corrupt. Neither PREV_INUSE not set "
											"nor IS_MMAPED set.\n");

		/* Just to be safe, we check if the metadta pointer corresponding to
		 * calloc pointer is page aligned.
		 */
			ASSERT(!((uint64_t)ptr_to_metadata & (~sysPageInfoPtr->pageMask)),
					 	 "Chunk metadata pointer not page aligned for mmaped chunk.\n");

			appMappingInfoPtr->mapping_type = (int8_t)CALLOC_MAPPING_USED;
			appMappingInfoPtr->mmapped_addr = callocPtr;

		/* If it is mmaped, we try to get the starting address of the mmap by
		 * getting the page address the given pointer belongs to and use the
		 * size to shadow map it. We first get the size of th map from the
		 * metaData. This is not safe but this is the best choice we've got
		 * to get the size of the map.
		 */
			uint64_t mmaped_size = (ptr_to_metadata->mchunk_size) & ((uint64_t)(~0) << 3);

		/* We get the information about the slots that enclose the mmaped region,
		 * and then we map its shadow and reserved units.
		 */
			struct regSlotsInfo mmaped_regSlotsInfo;
			Get_RegSlotsInfo((uint64_t)ptr_to_metadata, mmaped_size, &mmaped_regSlotsInfo);
			MapAppRegion(mmaped_regSlotsInfo.regSlotsBegAddr, mmaped_regSlotsInfo.numRegSlots);

			callocPtr = appMappingInfoPtr->mmapped_addr;
			appMappingInfoPtr->mapping_type = (int8_t)NO_MAPPING_USED;
			appMappingInfoPtr->mmapped_addr = 0;
		}

#ifndef BLOCK_HEAP
	} else {
	/* This means that that the main arena was extended. If the the
	 * heap size exceeds the heap size for which the shadow has already
	 * been accounted for, we extend the heap limits kept track of by the
	 * scratch heap struct. We treat the heap extention as a new application region.
	 */
		if((uint64_t)Syssbrk(0) > heapInfoPtr->heapBase + heapInfoPtr->heapSoftLimit) {
			struct regSlotsInfo heapExtention_slotsInfo;
			uint64_t old_heapSoftLimit = heapInfoPtr->heapSoftLimit;
			uint64_t heapExtentionSize = (uint64_t)1 << 29;  /* extend the heap virtually by 500Mb */
			heapInfoPtr->heapSoftLimit += heapExtentionSize;  /* Now we update the saved heap soft limit */
			Get_RegSlotsInfo(heapInfoPtr->heapBase + old_heapSoftLimit,
								heapExtentionSize, &heapExtention_slotsInfo);
			MapAppRegion(heapExtention_slotsInfo.regSlotsBegAddr,
									heapExtention_slotsInfo.numRegSlots);
		}
	}
#endif
	errno = saved_errno; /* restoring the value of errno to retain transparency */
	return (void *)callocPtr;
#else
	return Heap_calloc(nmem, memsize);
#endif
}

/* Wrapper for realloc */
void *realloc(void *heapObjPtr, size_t objSize)
{
	if(shadowManagerState == (int8_t)SHADOW_UNINITIALIZED)
		Init_ShadowMapManager();

#ifdef USE_GNU_MALLOC
	Sysrealloc(heapObjPtr, objSize);
#else
/* Use HeapGuard's realloc */
	return Heap_realloc(heapObjPtr, objSize);
#endif
}

/* If the heap is blocked and when the application uses sbrk and brk,
 * we use a mapped 4Mb buffer and return the pointer to that space so
 * we do not break the application user space. This is similar to how Mac OS
 * emulates brk and sbrk calls, since the Mac OS does not use heap per se.
 */

/* Wrapper for brk */
int brk(void *addr)
{
	if(shadowManagerState == (int8_t)SHADOW_UNINITIALIZED)
		Init_ShadowMapManager();

#ifdef BLOCK_HEAP
	#ifndef DO_NOT_EMULATE_BREAK
		int saved_errno = errno;

	/* First, we map a 4Mb buffer, if it has not been mapped already */
		if(!main_bufferPtr) {
			main_bufferPtr = (uint64_t)Sysmmap(NULL, (uint64_t)1 << 22, PROT_NONE,
														MAP_SHARED | MAP_ANONYMOUS, 0, 0);
			ASSERT(main_bufferPtr != (uint64_t)MAP_FAILED,
					"Error: Could not map buffer to emulate program break.");

			appMappingInfoPtr->mapping_type = (int8_t)MMAP_MAPPING_USED;
			appMappingInfoPtr->intended_addr = 0;
			appMappingInfoPtr->mmapped_addr = main_bufferPtr;
			appMappingInfoPtr->size = (uint64_t)1 << 22;
			appMappingInfoPtr->prot = PROT_NONE;
			appMappingInfoPtr->flags = MAP_SHARED | MAP_ANONYMOUS;
			appMappingInfoPtr->fd = 0;
			appMappingInfoPtr->offset = 0;

		/* Map the shadow for this buffer */
			struct regSlotsInfo buffer_slotsInfo;
			Get_RegSlotsInfo(main_bufferPtr, (uint64_t)1 << 22, &buffer_slotsInfo);
			MapAppRegion(buffer_slotsInfo.regSlotsBegAddr, buffer_slotsInfo.numRegSlots);

			main_bufferPtr = appMappingInfoPtr->mmapped_addr;
			*appMappingInfoPtr = (struct appMappingInfo){0};
			appMappingInfoPtr->mapping_type = (int8_t)NO_MAPPING_USED;
		}

	/* If the given address is equal to the buffer pointer, we get rid of the buffer */
		if((uint64_t)addr == main_bufferPtr) {
			Sysmunmap((void *)main_bufferPtr, (uint64_t)1 << 22);
			main_bufferPtr = cur_bufferPtr = 0;

		/* Unmap the shadow for the buffer */
			struct regSlotsInfo buffer_slotsInfo;
			Get_RegSlotsInfo(main_bufferPtr, (uint64_t)1 << 22, &buffer_slotsInfo);
			UnmapAppRegion(buffer_slotsInfo.regSlotsBegAddr, buffer_slotsInfo.numRegSlots);

			errno = saved_errno; /* restore the value of errno to maintain transparency */
			return 0;
		}

	/* Round up to page-align the given address */
		uint64_t pageAligned_addr;
		if(!(pageAligned_addr = (uint64_t)addr & (sysPageInfoPtr->pageMask)))
			pageAligned_addr += sysPageInfoPtr->pageSize;

		if((pageAligned_addr >= main_bufferPtr)
				&& (pageAligned_addr < (main_bufferPtr + ((uint64_t)1 << 22)))) {
		/* If the page-aligned addr is within the buffer range, we check if
		 * the buffer was just mapped since all of its pages are inaccessible.
		 */
			if(cur_bufferPtr) {
				ASSERT(Sysmprotect((void *)main_bufferPtr,
						cur_bufferPtr - main_bufferPtr, PROT_NONE) != -1,
							"Error: Could not change protection of the buffer.");
			}

		/* We let make the current pointer to point to the page_aligned given
		 * address and let all the space above be readable and writable.
		 */
			ASSERT(Sysmprotect((void *)main_bufferPtr, pageAligned_addr - main_bufferPtr,
											PROT_READ|PROT_WRITE) != -1,
										"Error: Could not change protection of the buffer.");
			cur_bufferPtr = pageAligned_addr;
			errno = saved_errno; /* restore the value of errno to maintain transparency */
		} else {
		/* If the addr is not in the buffer range, we throw exception */
			EXCEPTION("Error: The page-aligned brk argument is out of buffer range.");
		}
		return 0;
	#else
	/* If the heap segment is not to be emulated, we let the system brk call fail gracefully */
		return Sysbrk(addr);
	#endif
#else
/* Let the heap to grow or shrink normally as the heap is not blocked */
	return Sysbrk(addr);
#endif
}

/* Wrapper for sbrk */
void *sbrk(intptr_t increment)
{
	if(shadowManagerState == (int8_t)SHADOW_UNINITIALIZED)
		Init_ShadowMapManager();

#ifdef BLOCK_HEAP
	#ifndef DO_NOT_EMULATE_BREAK
		int saved_errno = errno;
		uint64_t prev_cur_bufferPtr = cur_bufferPtr;

	/* First, we map a 4Mb buffer, if it has not been mapped already */
		if(!main_bufferPtr) {
			main_bufferPtr = (uint64_t)Sysmmap(NULL, (uint64_t)1 << 22, PROT_NONE,
													MAP_SHARED | MAP_ANONYMOUS, 0, 0);
			ASSERT(main_bufferPtr != (uint64_t)MAP_FAILED,
					"Error: Could not map buffer to emulate program break.");

			appMappingInfoPtr->mapping_type = (int8_t)MMAP_MAPPING_USED;
			appMappingInfoPtr->intended_addr = 0;
			appMappingInfoPtr->mmapped_addr = main_bufferPtr;
			appMappingInfoPtr->size = (uint64_t)1 << 22;
			appMappingInfoPtr->prot = PROT_NONE;
			appMappingInfoPtr->flags = MAP_SHARED | MAP_ANONYMOUS;
			appMappingInfoPtr->fd = 0;
			appMappingInfoPtr->offset = 0;

		/* Map the shadow for this buffer */
			struct regSlotsInfo buffer_slotsInfo;
			Get_RegSlotsInfo(main_bufferPtr, (uint64_t)1 << 22, &buffer_slotsInfo);
			MapAppRegion(buffer_slotsInfo.regSlotsBegAddr, buffer_slotsInfo.numRegSlots);

			main_bufferPtr = appMappingInfoPtr->mmapped_addr;
			*appMappingInfoPtr = (struct appMappingInfo){0};
			appMappingInfoPtr->mapping_type = (int8_t)NO_MAPPING_USED;
			cur_bufferPtr = main_bufferPtr;
		}

	/* If the resulting address after increment is equal to the buffer pointer,
	 * we get rid of the buffer.
	 */
		if(cur_bufferPtr + (int64_t)increment == main_bufferPtr) {
			Sysmunmap((void *)main_bufferPtr, (uint64_t)1 << 22);
			main_bufferPtr = cur_bufferPtr = 0;

		/* Unmap the shadow for the buffer */
			struct regSlotsInfo buffer_slotsInfo;
			Get_RegSlotsInfo(main_bufferPtr, (uint64_t)1 << 22, &buffer_slotsInfo);
			UnmapAppRegion(buffer_slotsInfo.regSlotsBegAddr, buffer_slotsInfo.numRegSlots);

			errno = saved_errno; /* restore the value of errno to maintain transparency */
			return (void *)prev_cur_bufferPtr;
		}

	/* Round up to page-align the given address */
		uint64_t pageAligned_addr;
		if(!(pageAligned_addr =
				(uint64_t)(cur_bufferPtr + (int64_t)increment) & (sysPageInfoPtr->pageMask)))
			pageAligned_addr += sysPageInfoPtr->pageSize;

		if((pageAligned_addr >= main_bufferPtr)
				&& (pageAligned_addr < (main_bufferPtr + ((uint64_t)1 << 22)))) {
		/* If the page-aligned addr is within the buffer range, we check if
		 * the buffer was just mapped since all of its pages are inaccessible.
		 */
			if(prev_cur_bufferPtr) {
				ASSERT(Sysmprotect((void *)main_bufferPtr,
						cur_bufferPtr - main_bufferPtr, PROT_NONE) != -1,
						"Error: Could not change protection of the buffer.");
			}

		/* We let make the current pointer to point to the page_aligned
		 * given address and let all the space above be readable and writable.
		 */
			ASSERT(Sysmprotect((void *)main_bufferPtr, pageAligned_addr - main_bufferPtr,
															PROT_READ|PROT_WRITE) != -1,
										"Error: Could not change protection of the buffer.");
			cur_bufferPtr = pageAligned_addr;
			errno = saved_errno; /* restore the value of errno to maintain transparency */
		} else {
		/* If the addr is not in the buffer range, we throw exception */
			EXCEPTION("Error: The incremented page-aligned address is out of buffer range.");
		}
		return (void *)prev_cur_bufferPtr;
	#else
	/* If the heap segment is not to be emulated, we let the system sbrk call
	 * fail gracefully.
	 */
		return Sysbrk(increment);
	#endif
#else
/* Let the heap to grow or shrink normally as the heap is not blocked */
	return Sysbrk(increment);
#endif
}

/* Wrapper for free */
void free(void *memPtr)
{
/* If dlsym/fclose uses free or internal implementation of malloc is followed
 * by use of free, we simply ignore those calls as buffers are used and buffers
 * are big enough and allocations do not need to be freed. Also, while the
 * handling error, we do not want to implement free.
 */
	if(shadowManagerState != (int8_t)SHADOW_INITIALIZING) {
	#ifdef USE_GNU_MALLOC
		Sysfree(memPtr);
	#else
		Heap_free(memPtr);
	#endif
	}
}

/* Wrapper function for mmap */
void *mmap(void *appRegBegAddr, size_t appRegSize, int prot, int flags, int fd, off_t offset)
{
/* Initialize shadow map manager if it has not been intialized */
	if(shadowManagerState == (int8_t)SHADOW_UNINITIALIZED)
		Init_ShadowMapManager();
	uint64_t mmapPtr;

map_again:
	if((uint64_t)appRegBegAddr)
		;
		//mmapPtr = Map_Application_Region(appSlotsBegAddr, numAppSlots);
	else
		mmapPtr = (uint64_t)Sysmmap(appRegBegAddr, appRegSize, prot, flags, fd, offset);

	if(mmapPtr == (uint64_t)MAP_FAILED)
		return (void *)MAP_FAILED;

#ifndef BLOCK_HEAP
/* If the mapping took place within the heap limits, we reduce the limit to the
 * begining of the newly mmaped region.
 */
	uint64_t old_heapCurLim = heapInfoPtr->heapBase + heapInfoPtr->heapSoftLimit;
	if(mmapPtr <= old_heapCurLim) {
	/* If the entire mmaped region fits within the former heap limits, we don't
	 * have to map a new shadow. Instead, we might have to truncate it accounting
	 * for the region beyond the newly mmaped region.
	 */
		heapInfoPtr->heapSoftLimit = mmapPtr - heapInfoPtr->heapBase;
		uint64_t mmapEndAddr = mmapPtr + appRegSize;
		if(mmapEndAddr > old_heapCurLim) {
		/* We treat the extra mmap region sticking out of the heap region as a new app region */
			struct regSlotsInfo regExtentionSlotsInfo;
			Get_RegSlotsInfo(old_heapCurLim, (uint64_t)appRegSize - (old_heapCurLim - mmapPtr),
																				&regExtentionSlotsInfo);

		/* Check if the application region ended up in the blocked slot(s), we have
		 * to unmap the region, block the slots again since the space is probably
		 * empty and remap the region.
		 */
			if (AppRegion_Overlaps_BlockedSlots(regExtentionSlotsInfo.regSlotsBegAddr,
												regExtentionSlotsInfo.numRegSlots)) {
				Sysmunmap((void *)mmapPtr, appRegSize);
				goto map_again;
			}

			int saved_errno = errno; /* We save the value of errno obtained from real mmap */
			appMappingInfoPtr->intended_addr = (uint64_t)appRegBegAddr;
			appMappingInfoPtr->mmapped_addr = mmapPtr;
			appMappingInfoPtr->size = appRegSize;
			appMappingInfoPtr->prot = prot;
			appMappingInfoPtr->fd = fd;
			appMappingInfoPtr->flags = flags;
			appMappingInfoPtr->offset = offset;

		/* The mapping type will be determined by the fact whether the mapping
		 * used is fixed or not. So we do not recursively map the applocation
		 * region if the shadow mapping does not work out.
		 */
			if(flags & MAP_FIXED)
				appMappingInfoPtr->mmap_type = (int8_t)FIXED_MAPPING_USED;
			else
				appMappingInfoPtr->mmap_type = (int8_t)MMAP_MAPPING_USED;

			MapAppRegion(regExtentionSlotsInfo.regSlotsBegAddr,
											regExtentionSlotsInfo.numRegSlots);

			mmapPtr = appMappingPtr->mmapped_addr;
			*appMappingInfoPtr = (struct appMappingInfo){0};
			appMappingInfoPtr->mmap_type = (int8_t)NO_MAPPING_USED;
			errno = saved_errno; /* restoring the value of errno to retain transparency */
			return (void *)mmapPtr;
		} else {
			if(mmapEndAddr == old_heapCurLim) {
			/* mmaped region is at the end of the heap, so its shadow exits */
				return (void *)mmapPtr;
			} else {
				int saved_errno = errno; /* We save the value of errno obtained from real mmap */

			/* The mmaped region is inside the heap region, so the shadow exits but
			 * we need to truncate the shadow for region beyond the newly mmaped region.
			 */
				struct regSlotsInfo regTruncateSlotsInfo;
				Get_RegSlotsInfo(mmapEndAddr, old_heapCurLim - mmapEndAddr, &regTruncateSlotsInfo);
				UnmapAppRegion(regTruncateSlotsInfo.regSlotsBegAddr,
										regTruncateSlotsInfo.numRegSlots);

				errno = saved_errno; /* restoring the value of errno to retain transparency */
				return (void *)mmapPtr;
			}
		}
	}
#endif

/* Now, we get the information about the slots enclosing the mmapped region
 * and map shadows and reserved units.
 */
	struct regSlotsInfo mmaped_regSlotsInfo;
	Get_RegSlotsInfo(mmapPtr, appRegSize, &mmaped_regSlotsInfo);

/* Check if the application region ended up in the blocked slot(s),
 * we have to unmap the region, block the slots again since the
 * space is probably empty and remap the region.
 */
	if (AppRegion_Overlaps_BlockedSlots(mmaped_regSlotsInfo.regSlotsBegAddr,
											mmaped_regSlotsInfo.numRegSlots)) {
		Sysmunmap((void *)mmapPtr, appRegSize);
		goto map_again;
	}

	int saved_errno = errno; /* We save the value of errno obtained from real mmap */
	appMappingInfoPtr->intended_addr = (uint64_t)appRegBegAddr;
	appMappingInfoPtr->mmapped_addr = mmapPtr;
	appMappingInfoPtr->size = appRegSize;
	appMappingInfoPtr->prot = prot;
	appMappingInfoPtr->fd = fd;
	appMappingInfoPtr->flags = flags;
	appMappingInfoPtr->offset = offset;

/* The mapping type will be determined by the fact whether the mapping used
 * is fixed or not. So we do not recursively map the applocation region if
 * the shadow mapping does not work out.
 */
	if(flags & MAP_FIXED)
		appMappingInfoPtr->mapping_type = (int8_t)FIXED_MAPPING_USED;
	else
		appMappingInfoPtr->mapping_type = (int8_t)MMAP_MAPPING_USED;

	MapAppRegion(mmaped_regSlotsInfo.regSlotsBegAddr, mmaped_regSlotsInfo.numRegSlots);

	mmapPtr = appMappingInfoPtr->mmapped_addr;
	*appMappingInfoPtr = (struct appMappingInfo){0};
	appMappingInfoPtr->mapping_type = (int8_t)NO_MAPPING_USED;
	errno = saved_errno; /* restoring the value of errno to retain transparency */
	return (void *)mmapPtr;
}

int8_t Region_in_ScratchSpace (uint64_t regBegAddr, uint64_t regSize)
{
	uint64_t scratchSpaceEndAddr =
			scratchSpaceInfoPtr->scratchSpaceAddr + scratchSpaceInfoPtr->scratchSpaceSize;

/* Check if the region beginning address in scratch space region */
	if(regBegAddr >= scratchSpaceInfoPtr->scratchSpaceAddr
	&& regBegAddr < scratchSpaceEndAddr) {
		return 1;
	}

/* Check if the region end address in scratch space region */
	uint64_t regEndAddr = regBegAddr + regSize;
	if(regEndAddr >= scratchSpaceInfoPtr->scratchSpaceAddr
	&& regEndAddr < scratchSpaceEndAddr) {
		return 1;
	}

/* Check if the region encloses the scratch space region */
	if(regBegAddr <= scratchSpaceInfoPtr->scratchSpaceAddr
	&& regEndAddr >= scratchSpaceEndAddr) {
		return 1;
	}

/* This means that the given region does not overlap with the scratch space */
	return 0;
}

#ifdef BLOCK_HEAP
int8_t Region_in_HeapBlockingPage (uint64_t regBegAddr, uint64_t regSize)
{
	uint64_t blockingPageBegAddr = (uint64_t)Syssbrk(0);
	uint64_t blockingPageEndAddr =
			blockingPageBegAddr + sysPageInfoPtr->pageSize;

/* Check if the region beginning address in heap blocking page */
	if(regBegAddr >= blockingPageBegAddr
	&& regBegAddr < blockingPageEndAddr) {
		return 1;
	}

/* Check if the region end address in heap blocking page */
	uint64_t regEndAddr = regBegAddr + regSize;
	if(regEndAddr >= blockingPageBegAddr
	&& regEndAddr < blockingPageEndAddr) {
		return 1;
	}

/* Check if the region encloses the heap blocking page */
	if(regBegAddr <= blockingPageBegAddr
	&& regEndAddr >= blockingPageEndAddr) {
		return 1;
	}

/* This means that the given region does not overlap with the heap blocking page */
	return 0;
}
#endif

/* Wrapper function for munmap */
int munmap(void *appRegBegAddr, size_t appRegSize)
{
/* Initialize shadow map manager if it has not been intialized */
	if(shadowManagerState == (int8_t)SHADOW_UNINITIALIZED)
		Init_ShadowMapManager();

/* Make sure that the application is not attempting to unmap any mapping used
 * by this shadow library.
 */
	struct regSlotsInfo appUnitsInfo;
	Get_RegSlotsInfo((uint64_t)appRegBegAddr, (uint64_t)appRegSize, &appUnitsInfo);
	struct unitInfo* unitPtr =
			memLayoutTablePtr + (appUnitsInfo.regSlotsBegAddr >> (uint64_t)SLOT_SHIFT);
	uint64_t countSlots = 0;
	while(countSlots++ != appUnitsInfo.numRegSlots) {
	/* Check if the given region is shadow, reserved or blocked slot(s) */
		if (unitPtr->offset > (int64_t) MAX_VALID_OFFSET) {
		/* Emulate munmap as if munmap was performed over an unmapped region.
		 * So check if the address is page aligned.
		 */
			if(((uint64_t)appRegBegAddr) & sysPageInfoPtr->pageMask)
				errno = EINVAL;
			else
				errno = ENOMEM;
			return -1;
		}
		unitPtr++;
	}

/* More specifically, we also need to check if the application is attempting to
 * unmap the scratch space or the heap blocking page because the slots/units
 * they end up in might happen to be treated as app units.
 */
	if(Region_in_ScratchSpace ((uint64_t)appRegBegAddr, appRegSize)
#ifdef BLOCK_HEAP
	|| Region_in_HeapBlockingPage ((uint64_t)appRegBegAddr, appRegSize)
#endif
	) {
	/* Emulate munmap as if munmap was performed over an unmapped region.
	 * So check if the address is page aligned.
	 */
		if(((uint64_t)appRegBegAddr) & sysPageInfoPtr->pageMask)
			errno = EINVAL;
		else
			errno = ENOMEM;
		return -1;
	}

	if(Sysmunmap(appRegBegAddr, appRegSize) == -1)
		return -1;

	int saved_errno = errno; /* We save the value of errno obtained from real mmap */

/* Now, we get information about the slots enclosing the munmapped region
 * and map shadows and reserved units.
 */
	UnmapAppRegion(appUnitsInfo.regSlotsBegAddr, appUnitsInfo.numRegSlots);

	errno = saved_errno; /* restoring the value of errno to retain transparency */
	return 0;
}

/* Wrapper for getrlimit */
int getrlimit (__rlimit_resource_t resource, struct rlimit *rlim)
{
/* Initialize shadow map manager if it has not been intialized */
	if(shadowManagerState == (int8_t)SHADOW_UNINITIALIZED)
		Init_ShadowMapManager();

	if(resource == RLIMIT_STACK && !(stackInfoPtr->finite_stackSoftLimitSet)) {
		int saved_errno  = errno; /* We save the value of errno obtained from real getrlimit */

	/* If we had explicitly set the stack soft limit, we need to return the soft limit as  */
		struct rlimit real_stackInfo;
		real_stackInfo.rlim_cur = RLIM_INFINITY;
		real_stackInfo.rlim_max = stackInfoPtr->stackHardLimit;
		ASSERT(Syssetrlimit(RLIMIT_STACK, &real_stackInfo) == -1,
					"Error in setting stack limit when creating illusion for application.");

	/* Now we get the stack limits and save them in the given structure and save the return value */
		int retVal = Sysgetrlimit(RLIMIT_STACK, rlim);

	/* We the set the stack limits as before */
		real_stackInfo.rlim_cur = stackInfoPtr->stackSoftLimit;
		ASSERT(Syssetrlimit(RLIMIT_STACK, &real_stackInfo) == -1,
					"Error in setting setting stack limit when back for library to operate on.");

		errno = saved_errno;	 /* restoring the value of errno to retain transparency */
		return retVal;
	}
	return Sysgetrlimit(resource, rlim);
}

/* Wrapper for setrlimit */
int setrlimit(__rlimit_resource_t resource, const struct rlimit *rlim)
{
/* Initialize shadow map manager if it has not been intialized */
	if(shadowManagerState == (int8_t)SHADOW_UNINITIALIZED)
		Init_ShadowMapManager();

	int setrlimit_retVal = Syssetrlimit(resource, rlim);
	if(setrlimit_retVal != -1) {
	/* We have to check the heap or stack limits have been changed */
		if(resource == RLIMIT_STACK) {
			if(rlim->rlim_cur > stackInfoPtr->stackSoftLimit) {
				int saved_errno  = errno; /* We save the value of errno obtained from real setrlimit */

			/* If the soft limit has been set to infinity, we increment the
			 * previous soft limit to 8Mb if the stack limit is set to less
			 * than 8Mb and if it is more than or equal to 8Mb, we're done.
			 */
				if(rlim->rlim_cur == RLIM_INFINITY) {
					uint64_t stackExtentionSize;
					if(stackInfoPtr->stackSoftLimit < ((uint64_t)1 << 23)) {
						stackExtentionSize = ((uint64_t)1 << 23) - stackInfoPtr->stackSoftLimit;
					} else {
						stackInfoPtr->stackHardLimit = rlim->rlim_max; /* updating the hard limit */
						errno = saved_errno;  /* restoring the value of errno to retain transparency */
						return setrlimit_retVal;
					}

					uint64_t old_stackSoftLimit = stackInfoPtr->stackSoftLimit;
					stackInfoPtr->stackSoftLimit += stackExtentionSize; /* update the sratch space struct for stack */

				/* We set the stack soft limit to 8Mb */
					struct rlimit stackLimInfo;
					stackLimInfo.rlim_cur =  stackInfoPtr->stackSoftLimit;
					stackLimInfo.rlim_max = rlim->rlim_max;
					ASSERT(Syssetrlimit(RLIMIT_STACK, &stackLimInfo) == -1,
							"Failed to set a finite stack limit when inifinite limit was explicitly set.");

				/* Now we treat the stack extention as a new application region and map its shadow */
					struct regSlotsInfo stackExtention_slotsInfo;
					uint64_t old_stackTop = stackInfoPtr->stackBase - old_stackSoftLimit;
					Get_RegSlotsInfo(old_stackTop, stackExtentionSize, &stackExtention_slotsInfo);
					MapAppRegion(stackExtention_slotsInfo.regSlotsBegAddr,
											stackExtention_slotsInfo.numRegSlots);

					stackInfoPtr->stackHardLimit = rlim->rlim_max; /* updating the hard limit */
					errno = saved_errno;  /* restoring the value of errno to retain transparency */
					return setrlimit_retVal;
				}

				stackInfoPtr->finite_stackSoftLimitSet = true;

			/* Now we augment the shadow existing shadow memory with the newly mmaped
			 * one. So the augmented stack section is treated as a new app region.
			 */
				struct regSlotsInfo stackExtention_slotsInfo;
				uint64_t stackExtentionSize = rlim->rlim_cur - stackInfoPtr->stackSoftLimit;
				uint64_t old_stackTop = stackInfoPtr->stackBase - stackInfoPtr->stackSoftLimit;
				Get_RegSlotsInfo(old_stackTop, stackExtentionSize, &stackExtention_slotsInfo);
				MapAppRegion(stackExtention_slotsInfo.regSlotsBegAddr,
														stackExtention_slotsInfo.numRegSlots);

			/* Update the stack info in the scratch space */
				stackInfoPtr->stackSoftLimit = rlim->rlim_cur;
				stackInfoPtr->stackHardLimit = rlim->rlim_max;

				errno = saved_errno; /* restoring the value of errno to retain transparency */
			} else {
				if(rlim->rlim_cur < stackInfoPtr->stackSoftLimit) {
					stackInfoPtr->finite_stackSoftLimitSet = true;
					int saved_errno  = errno; /* We save the value of errno obtained from real setrlimit */

				/* Now we truncate the shadow existing shadow memory with the newly mmaped one.
				 * So the truncated stack section is treated as a new app region.
				 */
					struct regSlotsInfo stackTruncate_slotsInfo;
					uint64_t stackTruncateSize = stackInfoPtr->stackSoftLimit - rlim->rlim_cur;
					uint64_t old_stackTop = stackInfoPtr->stackBase - stackInfoPtr->stackSoftLimit;
					Get_RegSlotsInfo(old_stackTop, stackTruncateSize, &stackTruncate_slotsInfo);
					UnmapAppRegion(stackTruncate_slotsInfo.regSlotsBegAddr,
												stackTruncate_slotsInfo.numRegSlots);

				/* Update the stack info in the scratch space */
					stackInfoPtr->stackSoftLimit = rlim->rlim_cur;
					stackInfoPtr->stackHardLimit = rlim->rlim_max;

					errno = saved_errno; /* restoring the value of errno to retain transparency */
				} else {
					stackInfoPtr->finite_stackSoftLimitSet = true;
					stackInfoPtr->stackHardLimit = rlim->rlim_max;
				}
			}
		}
	#ifndef BLOCK_HEAP
		else {
			if(resource == RLIMIT_DATA) {
				if(rlim->rlim_cur > heapInfoPtr->heapSoftLimit) {
					int saved_errno  = errno; /* We save the value of errno obtained from real setrlimit */

					if(rlim->rlim_cur == RLIM_INFINITY) {
					/* If the saved heap soft limit is less than 1Gb, we increment
					 * it to 1Gb, else we're done.
					 */
						uint64_t heapExtentionSize;
						if(heapInfoPtr->heapSoftLimit < (uint64_t)1 << 29) {
							heapExtentionSize = ((uint64_t)1 << 29) - heapInfoPtr->heapSoftLimit;
						} else {
							heapInfoPtr->heapHardLimit = rlim->rlim_max; /* updating the hard limit */
							errno = saved_errno;  /* restoring the value of errno to retain transparency */
							return setrlimit_retVal;
						}

						uint64_t old_heapSoftLimit = heapInfoPtr->heapSoftLimit;
						heapInfoPtr->heapSoftLimit += heapExtentionSize;
						heapInfoPtr->heapHardLimit = rlim->rlim_max;

					/* Now we augment the shadow existing shadow memory with the newly mmaped one.
					 * So the augmented heap section is treated as a new app region.
					 */
						struct regSlotsInfo heapExtention_slotsInfo;
						uint64_t old_heapLimBoundary = heapInfoPtr->heapBase + old_heapSoftLimit;
						Get_RegSlotsInfo(old_heapLimBoundary, heapExtentionSize, &heapExtention_slotsInfo);
						MapAppRegion(heapExtention_slotsInfo.regSlotsBegAddr,
												heapExtention_slotsInfo.numRegSlots);

						errno = saved_errno; /* restoring the value of errno to retain transparency */
						return setrlimit_retVal;
					}

				/* Now we augment the shadow existing shadow memory with the newly mmaped one.
				 * So the augmented heap section is treated as a new app region.
				 */
					struct regSlotsInfo heapExtention_slotsInfo;
					uint64_t heapExtentionSize = rlim->rlim_cur - heapInfoPtr->heapSoftLimit;
					uint64_t old_heapLimBoundary = heapInfoPtr->heapBase + heapInfoPtr->heapSoftLimit;
					Get_RegSlotsInfo(old_heapLimBoundary, heapExtentionSize, &heapExtention_slotsInfo);
					MapAppRegion(heapExtention_slotsInfo.regSlotsBegAddr,
												heapExtention_slotsInfo.numRegSlots);

				/* Update the heap info in the scratch space */
					heapInfoPtr->heapSoftLimit = rlim->rlim_cur;
					heapInfoPtr->heapHardLimit = rlim->rlim_max;

					errno = saved_errno; /* restoring the value of errno to retain transparency */
				} else {
					int saved_errno  = errno; /* We save the value of errno obtained from real setrlimit */

					if(rlim->rlim_cur < heapInfoPtr->heapSoftLimit) {
					/* Now we truncate the shadow existing shadow memory with the newly mmaped one.
					 * So the truncated stack section is treated as a new app region.
					 */
						struct regSlotsInfo heapTruncate_slotsInfo;
						uint64_t heapTruncateSize = heapInfoPtr->heapSoftLimit - rlim->rlim_cur;
						uint64_t old_heapLimBoundary = heapInfoPtr->heapBase + heapInfoPtr->heapSoftLimit;
						Get_RegSlotsInfo(old_heapLimBoundary, heapTruncateSize, &heapTruncate_slotsInfo);
						UnmapAppRegion(heapTruncate_slotsInfo.regSlotsBegAddr,
														heapTruncate_slotsInfo.numRegSlots);

					/* Update the stack info in the scratch space */
						heapInfoPtr->heapSoftLimit = rlim->rlim_cur;
						heapInfoPtr->heapHardLimit = rlim->rlim_max;

						errno = saved_errno; /* restoring the value of errno to retain transparency */
					} else {
					/* If the hard limit is changed alone, we have to update the scratch space info */
						if(rlim->rlim_max != heapInfoPtr->heapHardLimit)
							heapInfoPtr->heapHardLimit = rlim->rlim_max;
					}
				}
			}
		}
	#endif
	}
	return setrlimit_retVal;
}

/* Now, this is a security measure from preventing hackers from changing the protection
 * of shadow, reserved or blocked slot pages. So here is a wrapper for mprotect.
 */
int mprotect(void *addr, size_t len, int prot)
{
/* Initialize shadow map manager if it has not been intialized */
	if(shadowManagerState == (int8_t)SHADOW_UNINITIALIZED)
		Init_ShadowMapManager();

/* Make sure that the region in question to protect is an application region and not
 * shadow, reserved or blocked slot.
 */
	struct regSlotsInfo appUnitsInfo;
	Get_RegSlotsInfo((uint64_t)addr, (uint64_t)len, &appUnitsInfo);
	struct unitInfo* unitPtr =
			memLayoutTablePtr + (appUnitsInfo.regSlotsBegAddr >> (uint64_t)SLOT_SHIFT);
	uint64_t countSlots = 0;
	while(countSlots++ != appUnitsInfo.numRegSlots) {
	/* Check if the given region is shadow, reserved or blocked slot(s) */
		if (unitPtr->offset > (int64_t) MAX_VALID_OFFSET) {
		/* Emulate mprotect as if mprotect was performed over an unmapped region.
		 * So check if the address is page aligned.
		 */
			if(((uint64_t)addr) & sysPageInfoPtr->pageMask)
				errno = EINVAL;
			else
				errno = ENOMEM;
			return -1;
		}
		unitPtr++;
	}

/* More specifically, we also need to check if the application is attempting to
 * mprotect the scratch space or the heap blocking page because the slots/units
 * they end up in might happen to be treated as app units.
 */
	if(Region_in_ScratchSpace ((uint64_t)addr, len)
#ifdef BLOCK_HEAP
	|| Region_in_HeapBlockingPage ((uint64_t)addr, len)
#endif
	) {
	/* Emulate mprotect as if mprotect was performed over an unmapped region.
	 * So check if the address is page aligned.
	 */
		if(((uint64_t)addr) & sysPageInfoPtr->pageMask)
			errno = EINVAL;
		else
			errno = ENOMEM;
		return -1;
	}

	return Sysmprotect(addr, len, prot);
}

/* For security reasons, we also wrap madvise */
int madvise(void *addr, size_t length, int advice)
{
/* Initialize shadow map manager if it has not been intialized */
	if(shadowManagerState == (int8_t)SHADOW_UNINITIALIZED)
		Init_ShadowMapManager();

/* Make sure that the region in question to protect is an application region and not
 * shadow, reserved or blocked slot.
 */
	struct regSlotsInfo appUnitsInfo;
	Get_RegSlotsInfo((uint64_t)addr, (uint64_t)length, &appUnitsInfo);
	struct unitInfo* unitPtr =
			memLayoutTablePtr + (appUnitsInfo.regSlotsBegAddr >> (uint64_t)SLOT_SHIFT);
	uint64_t countSlots = 0;
	while(countSlots++ != appUnitsInfo.numRegSlots) {
	/* Check if the given region is shadow, reserved or blocked slot(s) */
		if (unitPtr->offset > (int64_t) MAX_VALID_OFFSET) {
		/* Emulate madvise as if madvise was performed over an unmapped region.
		 * So check if the address is page aligned.
		 */
			if(((uint64_t)addr) & sysPageInfoPtr->pageMask)
				errno = EINVAL;
			else
				errno = ENOMEM;
			return -1;
		}
		unitPtr++;
	}

/* More specifically, we also need to check if the application is attempting to
 * use mmadvise on the scratch space or the heap blocking page because the
 * slots/units they end up in might happen to be treated as app units.
 */
	if(Region_in_ScratchSpace ((uint64_t)addr, length)
#ifdef BLOCK_HEAP
	|| Region_in_HeapBlockingPage ((uint64_t)addr, length)
#endif
	) {
	/* Emulate madvise as if madvise was performed over an unmapped region.
	 * So check if the address is page aligned.
	 */
		if(((uint64_t)addr) & sysPageInfoPtr->pageMask)
			errno = EINVAL;
		else
			errno = ENOMEM;
		return -1;
	}

	return Sysmadvise(addr, length, advice);
}

/* For security reasons, wrap mlock */
int mlock(const void *addr, size_t len)
{
/* Initialize shadow map manager if it has not been intialized */
	if(shadowManagerState == (int8_t)SHADOW_UNINITIALIZED)
		Init_ShadowMapManager();

/* Make sure that the region in question to protect is an application region and not
 * shadow, reserved or blocked slot.
 */
	struct regSlotsInfo appUnitsInfo;
	Get_RegSlotsInfo((uint64_t)addr, (uint64_t)len, &appUnitsInfo);
	struct unitInfo* unitPtr =
			memLayoutTablePtr + (appUnitsInfo.regSlotsBegAddr >> (uint64_t)SLOT_SHIFT);
	uint64_t countSlots = 0;
	while(countSlots++ != appUnitsInfo.numRegSlots) {
	/* Check if the given region is shadow, reserved or blocked slot(s) */
		if (unitPtr->offset > (int64_t) MAX_VALID_OFFSET) {
		/* Emulate mlock as if mlock was performed over an unmapped region.
		 * So check if the address is page aligned.
		 */
			if(((uint64_t)addr) & sysPageInfoPtr->pageMask)
				errno = EINVAL;
			else
				errno = ENOMEM;
			return -1;
		}
		unitPtr++;
	}

/* More specifically, we also need to check if the application is attempting to
 * use mlock on the scratch space or the heap blocking page because the
 * slots/units they end up in might happen to be treated as app units.
 */
	if(Region_in_ScratchSpace ((uint64_t)addr, len)
#ifdef BLOCK_HEAP
	|| Region_in_HeapBlockingPage ((uint64_t)addr, len)
#endif
	) {
	/* Emulate mlock as if mlock was performed over an unmapped region.
	 * So check if the address is page aligned.
	 */
		if(((uint64_t)addr) & sysPageInfoPtr->pageMask)
			errno = EINVAL;
		else
			errno = ENOMEM;
		return -1;
	}

	return Sysmlock(addr, len);
}

/* For security reasons, wrap munlock */
int munlock(const void *addr, size_t len)
{
/* Initialize shadow map manager if it has not been intialized */
	if(shadowManagerState == (int8_t)SHADOW_UNINITIALIZED)
		Init_ShadowMapManager();

/* Make sure that the region in question to protect is an application region and not
 * shadow, reserved or blocked slot.
 */
	struct regSlotsInfo appUnitsInfo;
	Get_RegSlotsInfo((uint64_t)addr, (uint64_t)len, &appUnitsInfo);
	struct unitInfo* unitPtr =
			memLayoutTablePtr + (appUnitsInfo.regSlotsBegAddr >> (uint64_t)SLOT_SHIFT);
	uint64_t countSlots = 0;
	while(countSlots++ != appUnitsInfo.numRegSlots) {
	/* Check if the given region is shadow, reserved or blocked slot(s) */
		if (unitPtr->offset > (int64_t) MAX_VALID_OFFSET) {
		/* Emulate munlock as if munlock was performed over an unmapped region.
		 * So check if the address is page aligned.
		 */
			if(((uint64_t)addr) & sysPageInfoPtr->pageMask)
				errno = EINVAL;
			else
				errno = ENOMEM;
			return -1;
		}
		unitPtr++;
	}

/* More specifically, we also need to check if the application is attempting to
 * use munlock on the scratch space or the heap blocking page because the
 * slots/units they end up in might happen to be treated as app units.
 */
	if(Region_in_ScratchSpace ((uint64_t)addr, len)
#ifdef BLOCK_HEAP
	|| Region_in_HeapBlockingPage ((uint64_t)addr, len)
#endif
	) {
	/* Emulate munlock as if munlock was performed over an unmapped region.
	 * So check if the address is page aligned.
	 */
		if(((uint64_t)addr) & sysPageInfoPtr->pageMask)
			errno = EINVAL;
		else
			errno = ENOMEM;
		return -1;
	}

	return Sysmunlock(addr, len);
}

/* For security reasons, wrap mincore */
int mincore(void *addr, size_t length, unsigned char *vec)
{
/* Initialize shadow map manager if it has not been intialized */
	if(shadowManagerState == (int8_t)SHADOW_UNINITIALIZED)
		Init_ShadowMapManager();

/* Make sure that the region in question to protect is an application region and not
 * shadow, reserved or blocked slot.
 */
	struct regSlotsInfo appUnitsInfo;
	Get_RegSlotsInfo((uint64_t)addr, (uint64_t)length, &appUnitsInfo);
	struct unitInfo* unitPtr =
			memLayoutTablePtr + (appUnitsInfo.regSlotsBegAddr >> (uint64_t)SLOT_SHIFT);
	uint64_t countSlots = 0;
	while(countSlots++ != appUnitsInfo.numRegSlots) {
	/* Check if the given region is shadow, reserved or blocked slot(s) */
		if (unitPtr->offset > (int64_t) MAX_VALID_OFFSET) {
		/* Emulate mincore as if mincore was performed over an unmapped region.
		 * So check if the address is page aligned.
		 */
			if(((uint64_t)addr) & sysPageInfoPtr->pageMask)
				errno = EINVAL;
			else
				errno = ENOMEM;
			return -1;
		}
		unitPtr++;
	}

/* More specifically, we also need to check if the application is attempting to
 * use mincore on the scratch space or the heap blocking page because the
 * slots/units they end up in might happen to be treated as app units.
 */
	if(Region_in_ScratchSpace ((uint64_t)addr, length)
#ifdef BLOCK_HEAP
	|| Region_in_HeapBlockingPage ((uint64_t)addr, length)
#endif
	) {
	/* Emulate mincore as if mincore was performed over an unmapped region.
	 * So check if the address is page aligned.
	 */
		if(((uint64_t)addr) & sysPageInfoPtr->pageMask)
			errno = EINVAL;
		else
			errno = ENOMEM;
		return -1;
	}

	return Sysmincore(addr, length, vec);
}

/* For security reasons, wrap msync */
int msync(void *addr, size_t length, int flags)
{
/* Initialize shadow map manager if it has not been intialized */
	if(shadowManagerState == (int8_t)SHADOW_UNINITIALIZED)
		Init_ShadowMapManager();

/* Make sure that the region in question to protect is an application region
 * and not shadow, reserved or blocked slot.
 */
	struct regSlotsInfo appUnitsInfo;
	Get_RegSlotsInfo((uint64_t)addr, (uint64_t)length, &appUnitsInfo);
	struct unitInfo* unitPtr =
			memLayoutTablePtr + (appUnitsInfo.regSlotsBegAddr >> (uint64_t)SLOT_SHIFT);
	uint64_t countSlots = 0;
	while(countSlots++ != appUnitsInfo.numRegSlots) {
	/* Check if the given region is shadow, reserved or blocked slot(s) */
		if (unitPtr->offset > (int64_t) MAX_VALID_OFFSET) {
		/* Emulate msync as if msync was performed over an unmapped region.
		 * So check if the address is page aligned.
		 */
			if(((uint64_t)addr) & sysPageInfoPtr->pageMask)
				errno = EINVAL;
			else
				errno = ENOMEM;
			return -1;
		}
		unitPtr++;
	}

/* More specifically, we also need to check if the application is attempting
 * to use msync on the scratch space or the heap blocking page because the
 * slots/units they end up in might happen to be treated as app units.
 */
	if(Region_in_ScratchSpace ((uint64_t)addr, length)
#ifdef BLOCK_HEAP
	|| Region_in_HeapBlockingPage ((uint64_t)addr, length)
#endif
	) {
	/* Emulate msync as if msync was performed over an unmapped region.
	 * So check if the address is page aligned.
	 */
		if(((uint64_t)addr) & sysPageInfoPtr->pageMask)
			errno = EINVAL;
		else
			errno = ENOMEM;
		return -1;
	}

	return Sysmsync(addr, length, flags);
}


/********************************* INTERFACES FOR WRAPPED FUNCTIONS ******************************/

void Real_Brk(int (**real_brk)(void *))
{
/* Initialize shadow map manager if it has not been intialized */
	if(shadowManagerState == (int8_t)SHADOW_UNINITIALIZED)
		Init_ShadowMapManager();

	*real_brk = Sysbrk;
}

void Real_Sbrk(void *(**real_sbrk)(intptr_t))
{
/* Initialize shadow map manager if it has not been intialized */
	if(shadowManagerState == (int8_t)SHADOW_UNINITIALIZED)
		Init_ShadowMapManager();

	*real_sbrk = Syssbrk;
}

void Real_Malloc(void *(**real_malloc)(size_t))
{
/* Initialize shadow map manager if it has not been intialized */
	if(shadowManagerState == (int8_t)SHADOW_UNINITIALIZED)
		Init_ShadowMapManager();

	*real_malloc = Sysmalloc;
}

void Real_Calloc(void *(**real_calloc)(size_t, size_t))
{
/* Initialize shadow map manager if it has not been intialized */
	if(shadowManagerState == (int8_t)SHADOW_UNINITIALIZED)
		Init_ShadowMapManager();

	*real_calloc = Syscalloc;
}

void Real_Free(void (**real_free)(void *))
{
/* Initialize shadow map manager if it has not been intialized */
	if(shadowManagerState == (int8_t)SHADOW_UNINITIALIZED)
		Init_ShadowMapManager();

	*real_free = Sysfree;
}

void Real_Mmap(void *(**real_mmap)(void *, size_t, int, int, int, off_t))
{
/* Initialize shadow map manager if it has not been intialized */
	if(shadowManagerState == (int8_t)SHADOW_UNINITIALIZED)
		Init_ShadowMapManager();

	*real_mmap = Sysmmap;
}

void Real_Munmap(int (**real_munmap)(void *, size_t))
{
/* Initialize shadow map manager if it has not been intialized */
	if(shadowManagerState == (int8_t)SHADOW_UNINITIALIZED)
		Init_ShadowMapManager();

	*real_munmap = Sysmunmap;
}

void Real_Mprotect(int (**real_mprotect)(void *, size_t, int))
{
/* Initialize shadow map manager if it has not been intialized */
	if(shadowManagerState == (int8_t)SHADOW_UNINITIALIZED)
		Init_ShadowMapManager();

	*real_mprotect = Sysmprotect;
}

void Real_Madvise(int (**real_madvise)(void *, size_t, int))
{
/* Initialize shadow map manager if it has not been intialized */
	if(shadowManagerState == (int8_t)SHADOW_UNINITIALIZED)
		Init_ShadowMapManager();

	*real_madvise = Sysmadvise;
}

void Real_Mincore(int (**real_mincore)(void *, size_t, unsigned char *))
{
/* Initialize shadow map manager if it has not been intialized */
	if(shadowManagerState == (int8_t)SHADOW_UNINITIALIZED)
		Init_ShadowMapManager();

	*real_mincore = Sysmincore;
}

void Real_Mlock(int (**real_mlock)(const void *, size_t))
{
/* Initialize shadow map manager if it has not been intialized */
	if(shadowManagerState == (int8_t)SHADOW_UNINITIALIZED)
		Init_ShadowMapManager();

	*real_mlock = Sysmlock;
}

void Real_Munlock(int (**real_munlock)(const void *, size_t))
{
/* Initialize shadow map manager if it has not been intialized */
	if(shadowManagerState == (int8_t)SHADOW_UNINITIALIZED)
		Init_ShadowMapManager();

	*real_munlock = Sysmunlock;
}

void Real_Msync(int (**real_msync)(void *, size_t, int))
{
/* Initialize shadow map manager if it has not been intialized */
	if(shadowManagerState == (int8_t)SHADOW_UNINITIALIZED)
		Init_ShadowMapManager();

	*real_msync = Sysmsync;
}

void Real_Getrlimit(int (**real_getrlimit)(int, struct rlimit *))
{
/* Initialize shadow map manager if it has not been intialized */
	if(shadowManagerState == (int8_t)SHADOW_UNINITIALIZED)
		Init_ShadowMapManager();

	*real_getrlimit = Sysgetrlimit;
}

void Real_Setrlimit(int (**real_setrlimit)(int, const struct rlimit *))
{
/* Initialize shadow map manager if it has not been intialized */
	if(shadowManagerState == (int8_t)SHADOW_UNINITIALIZED)
		Init_ShadowMapManager();

	*real_setrlimit = Syssetrlimit;
}

void Real_Prlimit(int (**real_prlimit)(pid_t, int, const struct rlimit *, struct rlimit *))
{
/* Initialize shadow map manager if it has not been intialized */
	if(shadowManagerState == (int8_t)SHADOW_UNINITIALIZED)
		Init_ShadowMapManager();

	*real_prlimit = Sysprlimit;
}


/***************************** ERROR HANDLING *********************************/

/* We use this function to emulate assert() in the C library. We have
 * to handle exceptions based on conditions ourselves since all the
 * other functions use heap and functions assert().
 */
inline void ASSERT(bool condition, char *errorMessage)
{
/* If the condition is false, we handle the error, or else we're done */
	if(!condition) {
	/* Print the error message */
		DEBUG_PRINTF(errorMessage);

	/* Clean up the shadow resources */
		//CleanUp_ShadowMap_and_Resources();

	/* Now, we raise SIGABRT signal to the application */
		raise(SIGABRT);
	}
}

#ifdef USE_GNU_MALLOC
inline int8_t WARN(bool condition, char *errorMessage)
{
/* If the condition is false, we handle the error, or else we warn */
	if(!condition) {
		DEBUG_PRINTF(errorMessage);
		return 1;
	}
	return 0;
}
#endif

/***************************** API FOR SHADOW ACCESS **************************/

inline void *GetPtr_to_MetaData(void *appAddr)
{
	return (void *)(((uint64_t)appAddr) << (uint64_t)SHADOW_SCALE) + shadowOffsets[0];
}

/* API to write 8, 16, 32, 64 bits at a time */
inline void Write8_to_Shadow(void *appAddr, uint8_t value)
{
#ifdef HANDLE_PAGEFAULTS
	handle_page_fault = true;
	sigsetjmp(pageFault_context, 1);
#endif
	*((uint8_t *)((((uint64_t)appAddr) << (uint64_t)SHADOW_SCALE) + shadowOffsets[0])) = value;
#ifdef HANDLE_PAGEFAULTS
	handle_page_fault = false;
#endif
}

inline void Write16_to_Shadow(void *appAddr, uint16_t value)
{
#ifdef HANDLE_PAGEFAULTS
	handle_page_fault = true;
	sigsetjmp(pageFault_context, 1);
#endif
	*((uint16_t *)((((uint64_t)appAddr) << (uint64_t)SHADOW_SCALE) + shadowOffsets[0])) = value;
#ifdef HANDLE_PAGEFAULTS
	handle_page_fault = false;
#endif
}

inline void Write32_to_Shadow(void *appAddr, uint32_t value)
{
#ifdef DEBUG
	//DEBUG_PRINTF("appAddr: %p\n", appAddr);
#endif
#ifdef HANDLE_PAGEFAULTS
	handle_page_fault = true;
	sigsetjmp(pageFault_context, 1);
#endif
#ifdef DEBUG
	//DEBUG_PRINTF("ShadowAddr: %p\n", (uint64_t)(((uint64_t)appAddr) << (uint64_t)SHADOW_SCALE) + shadowOffsets[0]);
#endif
	//PrintProcLayout();
	uint64_t storeAddr = (((uint64_t)appAddr) << (uint64_t)SHADOW_SCALE) + shadowOffsets[0];
	//DEBUG_PRINTF("storeAddr: %p\n", storeAddr);
	*((uint32_t *)storeAddr) = value;
#ifdef HANDLE_PAGEFAULTS
	handle_page_fault = false;
#endif
}

inline void Write64_to_Shadow(void *appAddr, uint64_t value)
{
#ifdef HANDLE_PAGEFAULTS
	handle_page_fault = true;
	sigsetjmp(pageFault_context, 1);
#endif
	*((uint64_t *)((((uint64_t)appAddr) << (uint64_t)SHADOW_SCALE) + shadowOffsets[0])) = value;
#ifdef HANDLE_PAGEFAULTS
	handle_page_fault = false;
#endif
}

/* API to read 8, 16, 32, 64 bits at a time */
inline uint8_t Read8_from_Shadow(void *appAddr)
{
#ifdef HANDLE_PAGEFAULTS
	handle_page_fault = true;
	sigsetjmp(pageFault_context, 1);
#endif
	uint8_t shadowData =
			*((uint8_t *)((((uint64_t)appAddr) << (uint64_t)SHADOW_SCALE) + shadowOffsets[0]));
#ifdef HANDLE_PAGEFAULTS
	handle_page_fault = false;
#endif
	return shadowData;
}

inline uint16_t Read16_from_Shadow(void *appAddr)
{
#ifdef HANDLE_PAGEFAULTS
	handle_page_fault = true;
	sigsetjmp(pageFault_context, 1);
#endif
	uint16_t shadowData =
			*((uint16_t *)((((uint64_t)appAddr) << (uint64_t)SHADOW_SCALE) + shadowOffsets[0]));
#ifdef HANDLE_PAGEFAULTS
	handle_page_fault = false;
#endif
	return shadowData;
}

inline uint32_t Read32_from_Shadow(void *appAddr)
{
#ifdef DEBUG
	//DEBUG_PRINTF("appAddr: %p\n", appAddr);
#endif
#ifdef HANDLE_PAGEFAULTS
	handle_page_fault = true;
	sigsetjmp(pageFault_context, 1);
#endif
#ifdef DEBUG
	//DEBUG_PRINTF("ShadowAddr: %p\n",
		//	(uint32_t *)((((uint64_t)appAddr) << (uint64_t)SHADOW_SCALE) + shadowOffsets[0]));
#endif
	uint32_t shadowData =
				*((uint32_t *)((((uint64_t)appAddr) << (uint64_t)SHADOW_SCALE) + shadowOffsets[0]));
#ifdef HANDLE_PAGEFAULTS
	handle_page_fault = false;
#endif
	return shadowData;
}

inline uint64_t Read64_from_Shadow(void *appAddr)
{
#ifdef HANDLE_PAGEFAULTS
	handle_page_fault = true;
	sigsetjmp(pageFault_context, 1);
#endif
	uint64_t shadowData =
			*((uint64_t *)((((uint64_t)appAddr) << (uint64_t)SHADOW_SCALE) + shadowOffsets[0]));
#ifdef HANDLE_PAGEFAULTS
	handle_page_fault = false;
#endif
	return shadowData;
}

inline void *GetPtr_to_ConstOffset_MetaData(void *appAddr)
{
	return (void *)(((uint64_t)appAddr) << (uint64_t)SHADOW_SCALE) + shadowOffsets[1];
}

/* API to write 8, 16, 32, 64 bits at a time */
inline void Write8_to_ConstOffset_Shadow(void *appAddr, uint8_t value)
{
	*((uint8_t *)((((uint64_t)appAddr) << (uint64_t)SHADOW_SCALE) + shadowOffsets[1])) = value;
}

inline void Write16_to_ConstOffset_Shadow(void *appAddr, uint16_t value)
{
	*((uint16_t *)((((uint64_t)appAddr) << (uint64_t)SHADOW_SCALE) + shadowOffsets[1])) = value;
}

inline void Write32_to_ConstOffset_Shadow(void *appAddr, uint32_t value)
{
	*((uint32_t *)((((uint64_t)appAddr) << (uint64_t)SHADOW_SCALE) + shadowOffsets[1])) = value;
}

inline void Write64_to_ConstOffset_Shadow(void *appAddr, uint64_t value)
{
	*((uint64_t *)((((uint64_t)appAddr) << (uint64_t)SHADOW_SCALE) + shadowOffsets[1])) = value;
}

/* API to read 8, 16, 32, 64 bits at a time */
inline uint8_t Read8_from_ConstOffset_Shadow(void *appAddr)
{
	return *((uint8_t *)((((uint64_t)appAddr) << (uint64_t)SHADOW_SCALE) + shadowOffsets[1]));
}

inline uint16_t Read16_from_ConstOffset_Shadow(void *appAddr)
{
	return *((uint16_t *)((((uint64_t)appAddr) << (uint64_t)SHADOW_SCALE) + shadowOffsets[1]));
}

inline uint32_t Read32_from_ConstOffset_Shadow(void *appAddr)
{
	return *((uint32_t *)((((uint64_t)appAddr) << (uint64_t)SHADOW_SCALE) + shadowOffsets[1]));
}

inline uint64_t Read64_from_ConstOffset_Shadow(void *appAddr)
{
	return *((uint64_t *)((((uint64_t)appAddr) << (uint64_t)SHADOW_SCALE) + shadowOffsets[1]));
}

/* Non-temporal store to shadow */
#include <emmintrin.h>
inline void Write32_to_NonTemporal_Shadow(void *appAddr, uint32_t value)
{
	uint64_t shadowAddr = (((uint64_t)appAddr) << (uint64_t)SHADOW_SCALE) + shadowOffsets[0];
	_mm_stream_si32 ((uint32_t *)shadowAddr, value);
}


/*************************** PAGE FAULT HANDLER INTERFACE *********************/

/* This provides the interface to the application using shadow memory library
 * to indicate whether the application can handle page faults or not.
 */
inline int Can_Handle_PageFaults(void)
{
#ifdef HANDLE_PAGEFAULTS
	return 1;
#else
	return 0;
#endif
}

#ifdef HANDLE_PAGEFAULTS
/* Interface for the tools using shadow memory to handle page faults */
void Add_PageFaultHandler_to_ShadowHandler(void(*toolPageFaultHandlerPtr)(int, sigjmp_buf **))
{
/* Reach the end of the array */
	void(**pageFaultHandlersElemPtr)(int, sigjmp_buf **);
	pageFaultHandlersElemPtr = pageFaultHandlersArrayPtr;
	while(*pageFaultHandlersElemPtr)
		pageFaultHandlersElemPtr++;

	*pageFaultHandlersElemPtr = toolPageFaultHandlerPtr;
}
#endif


/****************************** SIGNAL HANDLERS *******************************/
#ifdef HANDLE_PAGEFAULTS

/* Signal handler for handling page faults */
void Handle_PageFault(int sigNum)
{
	if(handle_page_fault) {
		static struct validOffset_struct *cur_nodePtr;

	/* Check to see if the error was due to illegitimate memory access */
		if(!cur_nodePtr) {
			cur_nodePtr = validOffsetsListPtr;
		} else {
			cur_nodePtr = cur_nodePtr->nextNodePtr;
			if(!cur_nodePtr)
				cur_nodePtr = validOffsetsListPtr;
		}
		shadowOffsets[0] = cur_nodePtr->validOffset;

	#ifdef	COUNT_SHADOW_PAGEFAULTS
		++numPageFaults;
	#endif
		DEBUG_PRINTF("%d\n", numPageFaults);
	#ifdef DEBUG
		//DEBUG_PRINTF("Number of page faults so far: %d\n", numPageFaults);
		//PrintProcLayout();
	#endif
		siglongjmp(pageFault_context, 1);
	}

/* We try the external page fault handler if it is defined */
	void(**pageFaultHandlersElemPtr)(int, sigjmp_buf **);
	pageFaultHandlersElemPtr = pageFaultHandlersArrayPtr;
	while(*pageFaultHandlersElemPtr) {
		sigjmp_buf *context_buf_ptr;
		void(*handler)(int, sigjmp_buf **) = *pageFaultHandlersElemPtr;
		handler(sigNum, &context_buf_ptr);

	/* If the context_buf_ptr is not null,that means the tool using the shadow memory
	 * handled the fault and we need to return the control back to the tool. Else,
	 * there was a genuine major page fault and the kernel needs to handle it.
	 */
		if(context_buf_ptr)
			siglongjmp(*context_buf_ptr, 1);

		pageFaultHandlersElemPtr++;
	}

/* Since this is a page fault generated due to the application, we emulate the signal */
	struct sigaction signal_act;
	signal_act.sa_handler = NULL;
	ASSERT(!sigemptyset(&signal_act.sa_mask), "Failed to let the kernel handle page faults.");
	signal_act.sa_flags = 0;
	ASSERT(!sigaction (SIGSEGV, &signal_act, NULL), "Failed to let the kernel handle page faults.");
	raise(SIGSEGV);
}

#endif

/* Signal handler for handling execution  */
void Handle_SigAlarm(int sigNum)
{
/* The signal handler simlpl returns */
	siglongjmp(alarm_context, 1);
}

/****************************************** TEST FUNCTIONS ***************************************/

//#ifdef DEBUG
void PrintProcLayout(void)
{
	char command[1024] = {0};
	SAFE_SPRINTF(command, 1024, "cat /proc/%d/maps", getpid());
	system(command);
}

void PrintValidOffsetsList(void)
{
	struct validOffset_struct* validOffsetNodePtr = validOffsetsListPtr;
	int count = 1;
	while (validOffsetNodePtr) {
		DEBUG_PRINTF("validOffset: %p \n" , (void *)validOffsetNodePtr -> validOffset);
		DEBUG_PRINTF("NumReg: %p \n", validOffsetNodePtr->numRegSameOffset);
		validOffsetNodePtr = validOffsetNodePtr->nextNodePtr;
		count++;
	}
}

void Print_ShadowOffsets_Cache(void)
{
	DEBUG_PRINTF("shadowOffsets[0]: %p %d\n", shadowOffsets[0], shadowOffsets[0]);
	DEBUG_PRINTF("shadowOffsets[1]: %p %d\n", shadowOffsets[1], shadowOffsets[1]);
}

void PrintAppShadowInfoList(void)
{
	struct appShadowAddrsNode *appShadowNodePtr = app_shadowListPtr;
	uint64_t count = 1;
	while (appShadowNodePtr) {
		appShadowNodePtr = appShadowNodePtr->nextNodePtr;
		count++;
	}

	uint64_t numShadows = (uint64_t) 1 << (uint64_t)SHADOW_SCALE;
	uint64_t countShadows;
	uint64_t shadowAddr;
	int64_t offset;
	appShadowNodePtr = app_shadowListPtr;
	count = 1;
	while (appShadowNodePtr) {
		DEBUG_PRINTF("appAddr: %p\n", appShadowNodePtr->appUnitAddr);
		shadowAddr = appShadowNodePtr->shadowUnitAddr;
		if (shadowAddr) {
			offset = appShadowNodePtr->shadowUnitAddr
					- (appShadowNodePtr->appUnitAddr << (uint64_t)SHADOW_SCALE);
			DEBUG_PRINTF("offset: %"PRId64"\n", offset);
			countShadows = 0;
			while ((countShadows++) != numShadows) {
				DEBUG_PRINTF("ShadowAddr: %p\n", shadowAddr);
				shadowAddr += (uint64_t)SLOT_SIZE;
			}
		}
		appShadowNodePtr = appShadowNodePtr->nextNodePtr;
		count++;
	}
}

void Print_MemLayoutTable_Offsets(void)
{
	uint64_t totalNumSlots = (uint64_t)1 << (47 - (uint64_t)SLOT_SHIFT);
	struct unitInfo *unitPtr = memLayoutTablePtr;
	uint64_t countSlots = 0;
	while((countSlots)++ != totalNumSlots) {
		if(unitPtr->offset < (int64_t)MAX_VALID_OFFSET) {
			DEBUG_PRINTF("uniPtr->offset: %p\n", unitPtr->offset);
			DEBUG_PRINTF("Addr: %p\n",
				(((uint64_t)unitPtr - (uint64_t)memLayoutTablePtr) /sizeof(struct unitInfo))
										<< (uint64_t)SLOT_SHIFT);
		}
		unitPtr++;
	}
}

void PrintInvalidOffset(void)
{
	uint64_t totalNumSlots = (uint64_t)1 << (47 - (uint64_t)SLOT_SHIFT);
	uint64_t num_invalidOffsetsTable_SubUnits = (uint64_t)1 << (uint64_t)SHADOW_SCALE;
	uint64_t invalidOffsetsTableSize =
		totalNumSlots * (num_invalidOffsetsTable_SubUnits * sizeof(struct invalidOffset_struct));

	struct invalidOffset_struct *tablePtr = posInvalidOffsetsTablePtr;
	uint64_t numUnits = totalNumSlots * num_invalidOffsetsTable_SubUnits;
	while(numUnits--) {
		if(tablePtr->invalidOffset)
			DEBUG_PRINTF("Invalid Offset: %p  numSubUnits: %p\n",
								tablePtr->invalidOffset, tablePtr->numSubUnits);
		tablePtr++;
	}

	tablePtr = negInvalidOffsetsTablePtr;
	numUnits = totalNumSlots * num_invalidOffsetsTable_SubUnits;
	while(numUnits--) {
		if(tablePtr->invalidOffset)
			DEBUG_PRINTF("Invalid Offset: %p  numSubUnits: %p\n", tablePtr->invalidOffset, tablePtr->numSubUnits);
		tablePtr++;
	}
}

#ifdef USE_GNU_MALLOC
inline void Extract_Protection_Info(char *stringPtr, char *protArray)
{
/* Skip all the spaces */
	while(isspace(*stringPtr))
		stringPtr++;

/* Put the put characters in thr given array */
	protArray[0] = *(stringPtr++);
	protArray[1] = *(stringPtr++);
	protArray[2] = *(stringPtr++);
	protArray[3] = *stringPtr;
}

/* Printing mapping sizes from proc maps file */
void ReadProcMapsFile_PrintAddrDiff(uint64_t range_startAddr, uint64_t range_endAddr)
{
	char filepath[1024] = {0};
	SAFE_SPRINTF(filepath, 1024, "/proc/%d/maps", getpid());

/* Proc files should only be read */
	int fd = open(filepath, O_RDONLY);

#ifndef DONT_THROW_EXECEPTION_ON_ERROR
	ASSERT(fd != -1, "Error: Could not open proc file\n");
#else
	int8_t warning = WARN(fd != -1, "Warning: Could not open proc file\n");
	if(warning)
		return;
#endif

	DEBUG_PRINTF("Given Range: %p - %p\n", range_startAddr, range_endAddr);
	char buffer[1024] = {0};
	char readChar;
	uint64_t lineNum = 0;
	char *bufPtr = buffer;
	while(read(fd, (void *)&readChar, 1) > 0) {
		if(readChar == '\n') {
			*bufPtr = '\0';
			char *restBuf;
			uint64_t startAddr = SAFE_STRTOULL_BASE16(buffer, &restBuf);
			warning = WARN(startAddr  != (uint64_t)-1,
							"Warning: Failed to read start Address.\n");
			if(warning)
				return;

		/* Skip the '-' */
			uint64_t endAddr = SAFE_STRTOULL_BASE16(restBuf + 1, &restBuf);
			warning = WARN(endAddr  != (uint64_t)-1,
								"Warning: Failed to read end Address.\n");
			if(warning)
				return;

		/* Check if the start and end addresses is in range */
			if(range_startAddr) {
				if(range_startAddr > startAddr) {
					if(endAddr <= range_startAddr) {
					/* Nothing to do just yet */
						bufPtr = buffer;
						continue;
					}
					startAddr = range_startAddr;
				}
			}
			if(range_endAddr) {
				if(range_endAddr <= startAddr) {
				/* Nothing to do now. We are done */
					break;
				}
				if(endAddr > range_endAddr)
					endAddr = range_endAddr;
			}

		/* We try to get the protection bits */
			char prot[5] = {0};
			Extract_Protection_Info(restBuf, prot);

			uint64_t diff = endAddr - startAddr;
			lineNum++;
			DEBUG_PRINTF("Difference: %p,%d (%d) %p-%p %s\n",
							diff, diff, lineNum, startAddr, endAddr, prot);

			bufPtr = buffer;
			continue;
		}
		*bufPtr = readChar;
		bufPtr++;
	}

#ifndef DONT_THROW_EXECEPTION_ON_ERROR
	ASSERT(!close(fd), "Error: Failed to close proc file,\n");
#else
	WARN(!close(fd), "Warning: Failed to close proc file,\n");
#endif
}
#endif

inline void Get_ShadowMemManager_State(void)
{
	if(shadowManagerState == (int8_t)SHADOW_INITIALIZED) {
		DEBUG_PRINTF("SHADOW MANAGER STATE: INITIALIZED\n");
		return;
	}
	if(shadowManagerState == (int8_t)SHADOW_INITIALIZING) {
		DEBUG_PRINTF("SHADOW MANAGER STATE: INITIALIZING\n");
		return;
	}
	if(shadowManagerState == (int8_t)SHADOW_UNINITIALIZED) {
		DEBUG_PRINTF("SHADOW MANAGER STATE: UNINITIALIZED\n");
		return;
	}
}

//#endif

/**********************************************************************************************/
