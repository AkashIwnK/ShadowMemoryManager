/* HeapGuard library
 *
 * This Shadow-based heap allocator is based on the implementation of FreeGuard.
 *  Paper: https://arxiv.org/pdf/1709.02746.pdf
 *
 *  This implementation is slightly different as far as allocation techniques are
 *  concerned and security features provided.
 */

#include <stdint.h>
#include <stdlib.h>
#include <stdarg.h>
#include <inttypes.h>
#include <sys/mman.h>
#include <sys/time.h>
#include <sys/resource.h>
#include <errno.h>
#include <unistd.h>
#include <sys/types.h>
#include <sys/stat.h>
#include <fcntl.h>
#include <ctype.h>
#include <stdbool.h>
#include <dlfcn.h>
#include <malloc.h>
#include <pthread.h>
#include <signal.h>
#include "HeapGuard.h"
#include "Stringlib.h"

/* This heap allocator uses Big Bag of Heaps (BiBoH) of HEAP_BAG_SIZE with multiple
 * heaps of size 16Mb and each object class size is 1Mb, by default. This heap allocator
 * is exploits the mmap-features and ASLR. It does not use the heap provided by the
 * operating system.
 *
 * This heap allocator will have two major bags of pages mapped intially. First
 * for allocation sizes between 2^4 bytes and 2^19 bytes, second for sizes larger
 * than 2^19 bytes and less than 2^28 bytes. We map bags that are 2^32 bytes big
 * so there may not be any need to map anymore bags. Statiscally, the first bag
 * will be used more for allocation than the second one.
 *
 * THIS HEAP ALLOCATOR ASSUMES THAT THE PAGE SIZE IS 4kB.
 */

/* These macros determine if the following functions need to be wrapped by this library */
//#define WRAP_MALLOC
//#define WRAP_FREE
//#define WRAP_CALLOC
//#define WRAP_REALLOC

//#define DEBUG
#ifdef DEBUG
#define CATCH_PAGE_FAULTS
#define INSTRUMENT_LOADS_AND_STORES
#endif

//#define INSTRUMENT_LOADS_AND_STORES
//#define CATCH_PAGE_FAULTS

#define REDEFINE_HEAP_MMAP
#define REDEFINE_HEAP_MUNMAP
#define REDEFINE_HEAP_MPROTECT

#define REDEFINE_HEAP_SHADOW_MMAP
#define REDEFINE_HEAP_SHADOW_MUNMAP
#define REDEFINE_HEAP_SHADOW_MPROTECT


/* We let the user of this heap allocator library to decide whether they want
 * to use the specific security features this heap allocator offers.
 */
#define DO_NOT_GUARD_PAGES
//#define ALLOW_DOUBLE_FREES
//#define ALLOW_USE_AFTER_FREE

#define DONT_THROW_EXECEPTION_ON_ERROR

#define ASSERT 	__Safe_Assert
#define ERROR	__Error
#define WARN	__Warn
#define DEBUG_PRINTF __Debug_Printf

/* Pointers to mmap and munmap if mmap and/or munmap are to be redefined */
#ifdef REDEFINE_HEAP_MMAP
void *(*heap_mmap)(void *, size_t, int, int, int, off_t);
#endif

#ifdef REDEFINE_HEAP_MUNMAP
int (*heap_munmap)(void *, size_t);
#endif

#ifdef REDEFINE_HEAP_MPROTECT
int (*heap_mprotect)(void *, size_t, int);
#endif

#ifdef REDEFINE_HEAP_SHADOW_MMAP
void *(*heap_shadow_mmap)(void *, size_t, int, int, int, off_t);
#endif

#ifdef REDEFINE_HEAP_SHADOW_MUNMAP
int (*heap_shadow_munmap)(void *, size_t);
#endif

#ifdef REDEFINE_HEAP_SHADOW_MPROTECT
int (*heap_shadow_mprotect)(void *, size_t, int);
#endif

/* A hash table that holds all the information about heaps for live threads */
static struct perThreadInfo **threadInfo;

/* The pointer to the map storing thread info */
static struct perThreadInfo *threadInfoSpacePtr;
static struct perThreadInfo *threadInfoNextNodePtr;

/* Lock for managing thread space pointers */
static pthread_mutex_t lock;


#ifdef INSTRUMENT_LOADS_AND_STORES
#define NO_FAULT (uint64_t)(~0)

uint64_t lastLoadAddr = (uint64_t)NO_FAULT;
uint64_t lastStoreAddr = (uint64_t)NO_FAULT;
#endif

#ifdef DEBUG
#define MALLOC_USED 	(int8_t)(~0)
#define FREE_USED 		((int8_t)(~0) << 1)
#define REALLOC_USED	((int8_t)(~0) << 2)
#define DONE        	((int8_t)(~0) << 3)

int8_t state;
#endif

int8_t heapGuardState = (int8_t)HEAPGUARD_UNINITIALIZED;

/************************************* HEAP ALLOCATOR INITIALIZER *********************************/

void Init_HeapGuard(void)
{
	if(heapGuardState == (int8_t)HEAPGUARD_INITIALIZED)
		return;

/* We use a lock here to avoid false sharing */
	pthread_mutex_lock(&lock);

/* Map the thread info array to store pointers  */
	if(!threadInfo)
		Map_ThreadInfoArray();

/* Map the thread info map */
	if(!threadInfoSpacePtr)
		Map_ThreadInfoSpace();

/* Look up the thread info */
	uint64_t threadId = (uint64_t)pthread_self();
	DEBUG_PRINTF("ThreadInfo index: %p\n", ((uint64_t)threadId & (uint64_t)THREAD_INFO_NUM_ELEM) >> 12);
	struct perThreadInfo **threadInfoPtr =
			&threadInfo[((uint64_t)threadId & (uint64_t)THREAD_INFO_NUM_ELEM) >> 12];
	DEBUG_PRINTF("threadInfoPtr: %p\n", threadInfoPtr);
	*threadInfoPtr = threadInfoNextNodePtr++;
	pthread_mutex_unlock(&lock);

/* Store the threadId */
	(*threadInfoPtr)->threadId = (uint64_t)threadId;
	DEBUG_PRINTF("Thread Id: %d %p\n", threadId, threadId);

/* Map a hash table to keep track the heap bag type */
	(*threadInfoPtr)->heapBagType_hashPtr = Map_HeapBagType_HashTable();
	DEBUG_PRINTF("(*threadInfoPtr)->heapBagType_hashPtr: %p\n", (*threadInfoPtr)->heapBagType_hashPtr);

/* Map the heap bags. There shouldn't be much need to change the contents of this cache */
	(*threadInfoPtr)->primaryHeap[0] = Map_HeapBag((uint64_t)HEAP_BAG_SIZE);
	(*threadInfoPtr)->primaryHeap[1] = Map_HeapBag((uint64_t)HEAP_BAG_SIZE);

#ifndef DO_NOT_GUARD_PAGES
/* Now we have to map guard pages. For allocation sizes less than 1 page, every alternate page
 * is made inaccesssible for security purposes.
 */
	PlantGuardPages((*threadInfoPtr)->primaryHeap[0], (uint64_t)HEAP_BAG_SIZE, (int8_t)SMALL_HEAP_BAG);
	PlantGuardPages((*threadInfoPtr)->primaryHeap[1], (uint64_t)HEAP_BAG_SIZE, (int8_t)LARGE_HEAP_BAG);
#endif

/* Shadow metadata is going to be a small fraction of the total shadow size so to make better
 * use of memory, we use rest of the space as a free list space. The shadow data for both bags
 * is adajact to each other and it is followed by the free list space.
 */
	uint64_t shadowPtr = Map_BagShadow();
	(*threadInfoPtr)->shadowOffset[0] =
			shadowPtr - (((*threadInfoPtr)->primaryHeap[0]) >> (uint64_t)SHADOW_MAP_SCALE);
	(*threadInfoPtr)->shadowOffset[1] =
			shadowPtr + (uint64_t)TOTAL_METADATA_SIZE -
				(((*threadInfoPtr)->primaryHeap[1]) >> (uint64_t)LARGE_SHADOW_MAP_SCALE);

/* The free list space is adjacent to the shadow metadata for each primary bags */
	(*threadInfoPtr)->freeListsEmptyNode =
					(struct freeObjNode *)(shadowPtr + (uint64_t)SHADOW_METADATA_SIZE);
	(*threadInfoPtr)->freeListsSpace_freeList = NULL;

/* Initialize the shadow data */
	Initialize_BagShadow((*threadInfoPtr)->primaryHeap[0], (uint64_t)HEAP_BAG_SIZE,
									(*threadInfoPtr)->shadowOffset[0], (int8_t)SMALL_HEAP_BAG);
	Initialize_BagShadow((*threadInfoPtr)->primaryHeap[1], (uint64_t)HEAP_BAG_SIZE,
									(*threadInfoPtr)->shadowOffset[1], (int8_t)LARGE_HEAP_BAG);

/* Intialization of hash table */
	Initialize_HeapBagType_HashTable((*threadInfoPtr)->heapBagType_hashPtr,
								(*threadInfoPtr)->primaryHeap[0], (int8_t)SMALL_HEAP_BAG);
	Initialize_HeapBagType_HashTable((*threadInfoPtr)->heapBagType_hashPtr,
								(*threadInfoPtr)->primaryHeap[1], (int8_t)LARGE_HEAP_BAG);

#ifdef CATCH_PAGE_FAULTS
	struct sigaction signal_act;
	signal_act.sa_handler = Handle_PageFault;
	ASSERT(!sigemptyset(&signal_act.sa_mask), "Failed to set the page fault handler.");
	signal_act.sa_flags = 0;
	ASSERT(!sigaction (SIGSEGV, &signal_act, NULL), "Failed to set the page fault handler.");
#endif

	DEBUG_PRINTF("HEAP ALLOCATION MANAGER INTIALIZED\n");
	//Print_Process_Layout();
	DEBUG_PRINTF("*threadInfoPtr: %p\n", *threadInfoPtr);
	DEBUG_PRINTF("(*threadInfoPtr)->heapBagType_hashPtr: %p\n", (*threadInfoPtr)->heapBagType_hashPtr);
	heapGuardState = (int8_t)HEAPGUARD_INITIALIZED;
}

void Map_ThreadInfoArray(void)
{
/* Map the thread info array */
	uint64_t threadInfoArraySize =
			RoundUp_to_PageSize((uint64_t)THREAD_INFO_NUM_ELEM * sizeof(struct perThreadInfo *))
											+ ((uint64_t)DEFAULT_PAGE_SIZE << 1);
	threadInfo = (struct perThreadInfo **)ShadowHeapMmap(0, threadInfoArraySize,
								PROT_READ | PROT_WRITE, MAP_SHARED | MAP_ANONYMOUS, 0, 0);
	if(threadInfo == (struct perThreadInfo **)MAP_FAILED) {
	/* Use the recursive fragmentation algorithm */
		threadInfo =
				(struct perThreadInfo **)MapHugeBlocks(ShadowHeapMmap, ShadowHeapMunmap, 
												ShadowHeapMprotect, threadInfoArraySize);
	}

/* Now, that we have mapped the info array, we need to surround it with guard
 * pages for protection.
 */
	uint64_t blockPagePtr = (uint64_t)threadInfo;
	ASSERT(ShadowHeapMprotect(blockPagePtr, (uint64_t)DEFAULT_PAGE_SIZE, PROT_NONE) != -1,
				"Error: Could not plant a guardpage in the beginning of thread info array.\n");

/* Place the second guard page */
	threadInfo = blockPagePtr + (uint64_t)DEFAULT_PAGE_SIZE;
	blockPagePtr += (threadInfoArraySize - (uint64_t)DEFAULT_PAGE_SIZE);
	ASSERT(ShadowHeapMprotect(blockPagePtr, (uint64_t)DEFAULT_PAGE_SIZE, PROT_NONE) != -1,
					"Error: Could not plant a guardpage in the end of thread info array.\n");
	DEBUG_PRINTF("THREADINFO: %p\n", threadInfo);
	Print_Process_Layout();
}

void Map_ThreadInfoSpace(void)
{
/* Map the thread info space */
	uint64_t threadInfoSpaceSize =
			RoundUp_to_PageSize((uint64_t)MAX_NUM_THREADS * sizeof(struct perThreadInfo));
													+ ((uint64_t)DEFAULT_PAGE_SIZE << 1);
	threadInfoSpacePtr = (struct perThreadInfo *)ShadowHeapMmap(0, threadInfoSpaceSize,
								PROT_READ | PROT_WRITE, MAP_SHARED | MAP_ANONYMOUS, 0, 0);
	if(threadInfoSpacePtr == (struct perThreadInfo *)MAP_FAILED) {
	/* Use the recursive fragmentation algorithm */
		threadInfoSpacePtr =
				(struct perThreadInfo *)MapHugeBlocks(ShadowHeapMmap, ShadowHeapMunmap, 
													ShadowHeapMprotect, threadInfoSpaceSize);
	}

/* Now, that we have mapped the info array, we need to surround it with guard
 * pages for protection.
 */
	uint64_t blockPagePtr = (uint64_t)threadInfoSpacePtr;
	ASSERT(ShadowHeapMprotect(blockPagePtr, (uint64_t)DEFAULT_PAGE_SIZE, PROT_NONE) != -1,
				"Error: Could not plant a guardpage in the beginning of thread info space.\n");

/* Place the second guard page */
	threadInfoSpacePtr = blockPagePtr + (uint64_t)DEFAULT_PAGE_SIZE;
	blockPagePtr += (threadInfoSpaceSize - (uint64_t)DEFAULT_PAGE_SIZE);
	ASSERT(ShadowHeapMprotect(blockPagePtr, (uint64_t)DEFAULT_PAGE_SIZE, PROT_NONE) != -1,
					"Error: Could not plant a guardpage in the end of thread info space.\n");
	DEBUG_PRINTF("THREADINFOSPACE: %p\n", threadInfoSpacePtr);
	Print_Process_Layout();

	threadInfoNextNodePtr = threadInfoSpacePtr;
}

int8_t *Map_HeapBagType_HashTable(void)
{
/* Map the heap bag type hash table */
	uint64_t hashTableSize = RoundUp_to_PageSize((uint64_t)BAG_TYPE_HASH_TABLE_SIZE)
													+ ((uint64_t)DEFAULT_PAGE_SIZE << 1);
	DEBUG_PRINTF("hash table size: %p %d\n", hashTableSize, hashTableSize);
	uint64_t hashTablePtr = (uint64_t)ShadowHeapMmap(0, hashTableSize,
							PROT_READ | PROT_WRITE, MAP_SHARED | MAP_ANONYMOUS, 0, 0);
	if(hashTablePtr == (uint64_t)MAP_FAILED) {
	/* Use the recursive fragmentation algorithm */
		hashTablePtr = MapHugeBlocks(ShadowHeapMmap, ShadowHeapMunmap, 
											ShadowHeapMprotect, hashTableSize);
	}

/* Now, that we have mapped the info array, we need to surround it with guard
 * pages for protection.
 */
	uint64_t blockPagePtr = hashTablePtr;
	ASSERT(ShadowHeapMprotect(blockPagePtr, (uint64_t)DEFAULT_PAGE_SIZE, PROT_NONE) != -1,
		"Error: Could not plant a guardpage in the beginning of heap bag type hash table.\n");

/* Place the second guard page */
	hashTablePtr = blockPagePtr + (uint64_t)DEFAULT_PAGE_SIZE;
	blockPagePtr += (hashTableSize - (uint64_t)DEFAULT_PAGE_SIZE);
	ASSERT(ShadowHeapMprotect(blockPagePtr, (uint64_t)DEFAULT_PAGE_SIZE, PROT_NONE) != -1,
			"Error: Could not plant a guardpage in the end of heap bag type hash table.\n");

	DEBUG_PRINTF("hash table ptr: %p\n", hashTablePtr);
	Print_Process_Layout();
	return (int8_t *)hashTablePtr;
}

inline uint64_t Map_BagShadow(void)
{
/* Map the thread info space */
	uint64_t shadowSize = RoundUp_to_PageSize((uint64_t)BAG_SHADOW_SIZE)
												+ ((uint64_t)DEFAULT_PAGE_SIZE << 1);
	uint64_t shadowPtr = (uint64_t)ShadowHeapMmap(0, shadowSize,
								PROT_READ | PROT_WRITE, MAP_SHARED | MAP_ANONYMOUS, 0, 0);
	if(shadowPtr == (uint64_t)MAP_FAILED) {
	/* Use the recursive fragmentation algorithm */
		shadowPtr = MapHugeBlocks(ShadowHeapMmap, ShadowHeapMunmap, 
											ShadowHeapMprotect, shadowSize);
	}
	
/* Now, that we have mapped the info array, we need to surround it with guard
 * pages for protection.
 */
	uint64_t blockPagePtr = shadowPtr;
	ASSERT(ShadowHeapMprotect(blockPagePtr, (uint64_t)DEFAULT_PAGE_SIZE, PROT_NONE) != -1,
		"Error: Could not plant a guardpage in the beginning of heap bag type hash table.\n");

/* Place the second guard page */
	shadowPtr = blockPagePtr + (uint64_t)DEFAULT_PAGE_SIZE;
	blockPagePtr += (shadowSize - (uint64_t)DEFAULT_PAGE_SIZE);
	ASSERT(ShadowHeapMprotect(blockPagePtr, (uint64_t)DEFAULT_PAGE_SIZE, PROT_NONE) != -1,
			"Error: Could not plant a guardpage in the end of heap bag type hash table.\n");

	return shadowPtr;
}

/* Algorithm used here relies on the fact that the 64-bit user address
 * space is humungous and we never run out of virtual memory space. We 
 * also specify which mmap, munmap and mprotect api we want this function 
 * to use.
 */
uint64_t MapHugeBlocks(void *(*mmap_func)(void *, size_t, int, int, int, off_t), 
						int (*munmap_func)(void *, size_t), 
						int (*mprotect_func)(void *, size_t, int),
						uint64_t size)
{
/* The block to be mapped is continued to be  fragmanted and an attempt
 * to map the fragment. If we fail, we fragment again and try again.
 */
	uint64_t blockPtr;
	uint64_t lastFragmentPtr;
	uint64_t fragmentSize = size >> 1;
	uint64_t numFragments_to_be_mapped = (uint64_t)1 << 1;

try_mapping_block_again:
/* First mapping is not at a fixed address */
	blockPtr = (uint64_t)mmap_func(0, fragmentSize,
					PROT_READ | PROT_WRITE, MAP_SHARED | MAP_ANONYMOUS, 0, 0);
	if(blockPtr == (uint64_t)MAP_FAILED) {
		numFragments_to_be_mapped <<= 1;
		fragmentSize <<= 1;
		goto try_mapping_block_again;
	}

/* Now, the fragments to be mapped will be mapped either at the lower adddress
 * or higher address than the block address. We try to map at a higher address
 * first. We have to keep in mind that this algorithm might fail if the the block
 * is being mapped between other mappings that might prevent this block from
 * extending on either side, in this case we have to "block" (make the mappings
 * inaccessible), and try mapping the block all over again.
 */
	numFragments_to_be_mapped--;
	lastFragmentPtr = blockPtr;
	bool higher_addr_mapping_failed = false;
	bool lower_addr_mapping_failed = false;
	uint64_t fragmentPtr;
	uint64_t nextAddr = lastFragmentPtr + fragmentSize;

	while(numFragments_to_be_mapped--) {
	try_higher_addresses:
	/* Try mapping at a higher address */
		fragmentPtr = (uint64_t)mmap_func(nextAddr, fragmentSize,
				PROT_READ | PROT_WRITE, MAP_SHARED | MAP_ANONYMOUS, 0, 0);
		if(fragmentPtr == (uint64_t)MAP_FAILED) {
		/* Check if we failed to map in the lower addresses */
			if(lower_addr_mapping_failed)
				goto block_all_mappings;

		/* Try using lower address */
			nextAddr = blockPtr - fragmentSize;
			higher_addr_mapping_failed = true;
			goto try_lower_addresses;
		}
		if(fragmentPtr != nextAddr) {
		/* These means that probably the there is not enough space where
		 * we intended to map the heap. So we unmap this mapping and try
		 * lower addresses instead if conditions are right.
		 */
			munmap_func(fragmentPtr, fragmentSize);

		/* Check if we failed to map in the lower addresses */
			if(lower_addr_mapping_failed)
				goto block_all_mappings;

			nextAddr = blockPtr - fragmentSize;
			higher_addr_mapping_failed = true;
			goto try_lower_addresses;
		}

	/* This means that the mapping was sucessful, so we continue in the
	 * same direction.
	 */
		higher_addr_mapping_failed = false;
		lastFragmentPtr = fragmentPtr;
		nextAddr = fragmentPtr + fragmentSize;
	}

	while(numFragments_to_be_mapped--) {
	try_lower_addresses:
	/* Try mapping at a higher address */
		fragmentPtr = (uint64_t)mmap_func(nextAddr, fragmentSize,
				PROT_READ | PROT_WRITE, MAP_SHARED | MAP_ANONYMOUS, 0, 0);
		if(fragmentPtr == (uint64_t)MAP_FAILED) {
		/* Check if we failed to map in the higher addresses */
			if(higher_addr_mapping_failed)
				goto block_all_mappings;

		/* Try using higher address */
			nextAddr = lastFragmentPtr + fragmentSize;
			lower_addr_mapping_failed = true;
			goto try_higher_addresses;
		}
		if(fragmentPtr != nextAddr) {
		/* These means that probably the there is not enough space where
		 * we intended to map the heap. So we unmap this mapping and try
		 * higher addresses instead if conditions are right.
		 */
			munmap_func(fragmentPtr, fragmentSize);

		/* Check if we failed to map in the higher addresses */
			if(higher_addr_mapping_failed)
				goto block_all_mappings;

			nextAddr = lastFragmentPtr + fragmentSize;
			lower_addr_mapping_failed = true;
			goto try_higher_addresses;
		}

	/* This means that the mapping was sucessful, so we continue in the
	 * same direction.
	 */
		lower_addr_mapping_failed = false;
		blockPtr = fragmentPtr;
		nextAddr = fragmentPtr - fragmentSize;
	}

/* Keep compiler happy so do not return just here */
	goto end;

block_all_mappings:
/* Now, we make all the mappings of the above block inaccessible */
	while(blockPtr <= lastFragmentPtr) {
		ASSERT(mprotect_func(blockPtr, fragmentSize, PROT_NONE) != -1,
							"Error: Could not block the big bags of heap\n");
		blockPtr += fragmentSize;
	}

/* Now we try to map the block all over again */
	goto try_mapping_block_again;

end:
	return blockPtr;
}

uint64_t Map_HeapBag(uint64_t size)
{
	//DEBUG_PRINTF("BAG SIZE TO BE MAPPED: %d\n", size);

/* The size of the bag should be a multiple of HEAP_BAG_SIZE */
	ASSERT(!(size & (uint64_t)HEAP_BAG_SIZE_MASK),
						"Error: Given bag size is not multiple of HEAP_BAG_SIZE\n");

/* Mapping a bag with guard pages on either sides may not be easy and may incur
 * a lot of overhead if not done properly.
 * So we map size + heap_bag. We divide the entire user address space into heap
 * bags and we have to make sure that the address of the mapping is not aligned
 * to the bag unit since the bag itself needs to be aligned but not the guard
 * pages themselves. A block is defined as two guard pages + heap bag.
 *
 */
	uint64_t blockPtr;

try_mapping_block:
	//DEBUG_PRINTF("TRY MAPPING SIZE + HEAP_BAG_SIZE\n");
	blockPtr = (uint64_t)HeapMmap(0, size + (uint64_t)HEAP_BAG_SIZE,
							PROT_READ | PROT_WRITE, MAP_SHARED | MAP_ANONYMOUS, 0, 0);
	if(blockPtr == (uint64_t)MAP_FAILED) {
	/* This mapping should never fail, if it does, a segmentation fault will be thrown? */
		blockPtr = MapHugeBlocks(HeapMmap, HeapMunmap, 
							HeapMprotect, size + (uint64_t)HEAP_BAG_SIZE);
	}

/* Now if the block is aligned to the bag slot, we "block" a page by
 * making it inaccessible.
 */
	if(!(blockPtr & (uint64_t)HEAP_BAG_ALIGN_MASK)) {
		//DEBUG_PRINTF("MAPPED BLOCK HEAP BAG ALIGNED\n");
	/* Now we unmap the entire block except leaving one page only */
		uint64_t unmapSize = size + (uint64_t)HEAP_BAG_SIZE - (uint64_t)DEFAULT_PAGE_SIZE;
		if(HeapMunmap(blockPtr, unmapSize) == -1) {
		/* If unmapping failed, "block" the entire block */
			ASSERT(ShadowHeapMprotect(blockPtr, size + (uint64_t)HEAP_BAG_SIZE, PROT_NONE) != -1,
												"Error: Could not block the big bags of heap\n");
		} else {
		/* Block one page. This is done in an effort to not to terribly fragment the virtual space */
			ASSERT(ShadowHeapMprotect(blockPtr + unmapSize, (uint64_t)DEFAULT_PAGE_SIZE, PROT_NONE) != -1,
													"Error: Could not block the big bags of heap\n");
		}
		goto try_mapping_block;
	}

#ifndef	DO_NOT_GUARD_PAGES
/* Truncate the mappings to have one extraneous page on either side of a bag of heaps.
 * First we find the first address aligned with bag slot minus one page.
 */
	uint64_t bagPtr = (blockPtr & (uint64_t)HEAP_BAG_ALIGN_MASK) +
								(uint64_t)HEAP_BAG_SIZE - (uint64_t)DEFAULT_PAGE_SIZE;
	uint64_t unmapSize = bagPtr - blockPtr;
	HeapMunmap(blockPtr, unmapSize);
	unmapSize = (uint64_t)HEAP_BAG_SIZE - (unmapSize + ((uint64_t)DEFAULT_PAGE_SIZE << 1));
	blockPtr = bagPtr + (size + ((uint64_t)DEFAULT_PAGE_SIZE << 1));
	HeapMunmap(blockPtr, unmapSize);

/* First guard page is the first page of the bag of heaps This is because since 'mmap'
 * mappings are contiguous, it is possible that the data can be corrupted due to overflows
 * in other pages.
 */
	blockPtr = bagPtr;
	bagPtr += (uint64_t)DEFAULT_PAGE_SIZE;
	ASSERT(ShadowHeapMprotect(blockPtr, (uint64_t)DEFAULT_PAGE_SIZE, PROT_NONE) != -1,
						"Error: Could not plant a guardpage in the beginning of the bag of heaps.\n");

/* Plant another guard page in the end of the bag of heaps */
	blockPtr = bagPtr + size;
	ASSERT(ShadowHeapMprotect(blockPtr, (uint64_t)DEFAULT_PAGE_SIZE, PROT_NONE) != -1,
							"Error: Could not plant a guardpage in the end of the bag of heaps.\n");
#else
	uint64_t bagPtr = (blockPtr & (uint64_t)HEAP_BAG_ALIGN_MASK) + (uint64_t)HEAP_BAG_SIZE;
	uint64_t unmapSize = bagPtr - blockPtr;
	HeapMunmap(blockPtr, unmapSize);
	unmapSize = (uint64_t)HEAP_BAG_SIZE - unmapSize;
	blockPtr = bagPtr + size;
	HeapMunmap(blockPtr, unmapSize);
#endif

	return bagPtr;
}

#ifndef DO_NOT_GUARD_PAGES
void PlantGuardPages(uint64_t bagPtr, uint64_t bagSize, int8_t heapBagType)
{
/*  Now if the class size is less than a page, every alternate page is made inaccessible */
	if(heapBagType == (int8_t)SMALL_HEAP_BAG) {
		uint64_t numGuardPages = (SUBHEAP_SIZE/((uint64_t)DEFAULT_PAGE_SIZE)) >> 1;
		uint64_t heapPtr = bagPtr;
		uint64_t heapIndex = 0;
		//DEBUG_PRINTF("NUM HEAPS: %d\n", NUM_HEAPS);
		while(heapIndex++ != NUM_HEAPS) {
			//DEBUG_PRINTF("HEAP INDEX; %d\n", heapIndex - 1);
			uint64_t subHeapPtr = heapPtr;
			uint64_t subHeapIndex = 0;
			while(subHeapIndex++ != 8) {
				//DEBUG_PRINTF("SUBHEAP INDEX: %d\n", subHeapIndex - 1);
				uint64_t guardPagePtr = subHeapPtr + ((uint64_t)DEFAULT_PAGE_SIZE);
				uint64_t numGuardPages_planted = 0;
				//DEBUG_PRINTF("GUARD PAGE ADDR: %p\n", guardPagePtr);
				while(numGuardPages_planted++ != numGuardPages) {
					ASSERT(ShadowHeapMprotect(guardPagePtr, (uint64_t)DEFAULT_PAGE_SIZE, PROT_NONE) != -1,
									"Error: Could not plant a guardpage in the bag of small heaps.\n");
					guardPagePtr += ((uint64_t)DEFAULT_PAGE_SIZE << 1);
				}
				//DEBUG_PRINTF("SUBHEAP PTR: %p\n", subHeapPtr);
				//ReadProcMapsFile_PrintAddrDiff(subHeapPtr, subHeapPtr + (uint64_t)SUBHEAP_SIZE);
				subHeapPtr += (uint64_t)SUBHEAP_SIZE;
			}
			//DEBUG_PRINTF("HEAP INDEX; %d\n", heapIndex - 1);
			//DEBUG_PRINTF("HEAP PTR: %p\n", heapPtr);
			//ReadProcMapsFile_PrintAddrDiff(heapPtr, heapPtr + (uint64_t)HEAP_SIZE);
			heapPtr += (uint64_t)HEAP_SIZE;
		}

		//DEBUG_PRINTF("\n\nDONE WITH SMALL SIZES\n");
		//DEBUG_PRINTF("BAG PTR: %p\n", bagPtr);

	/* Now, every object greater or equal to a page size have a guard page placed below and above it */
		heapPtr = bagPtr;
		heapIndex = 0;
		while(heapIndex++ != NUM_HEAPS) {
			//DEBUG_PRINTF("HEAP INDEX; %d\n", heapIndex - 1);
			uint64_t heapObjSize = (uint64_t)DEFAULT_PAGE_SIZE;
			uint64_t subHeapPtr = heapPtr + ((uint64_t)SUBHEAP_SIZE << 3);
			uint64_t subHeapIndex = 8;
			while(subHeapIndex++ != 16) {
				uint64_t guardPagePtr = subHeapPtr + heapObjSize;
				uint64_t numGuardPages = (SUBHEAP_SIZE/heapObjSize) >> 1;
				uint64_t numGuardPages_planted = 0;
				while(numGuardPages_planted++ != numGuardPages) {
					ASSERT(ShadowHeapMprotect(guardPagePtr, (uint64_t)DEFAULT_PAGE_SIZE, PROT_NONE) != -1,
									"Error: Could not plant a guardpage in the bag of medium heaps.\n");
					guardPagePtr += ((uint64_t)DEFAULT_PAGE_SIZE + heapObjSize);
				}
				//DEBUG_PRINTF("SUBHEAP PTR: %p\n", subHeapPtr);
				//DEBUG_PRINTF("HEAP OBJ SIZE: %p\n", heapObjSize);
				heapObjSize <<= 1;
				subHeapPtr += (uint64_t)SUBHEAP_SIZE;
			}
			//DEBUG_PRINTF("HEAP PTR: %p\n", heapPtr);
			heapPtr += (uint64_t)HEAP_SIZE;
		}

		//DEBUG_PRINTF("\n\nDONE WITH MEDIUM SIZES\n");
		return;
	}

/* Place guard pages for the larger heaps */
	if(heapBagType == (int8_t)LARGE_HEAP_BAG) {
		//ReadProcMapsFile_PrintAddrDiff(0, 0);
		uint64_t heapPtr = bagPtr;
		uint64_t heapIndex = 0;
		while(heapIndex++ != NUM_LARGE_HEAPS) {
			//DEBUG_PRINTF("HEAP INDEX; %d\n", heapIndex - 1);
			uint64_t heapObjSize = (uint64_t)MIN_LARGE_OBJ_SIZE;
			uint64_t subHeapPtr = heapPtr;
			uint64_t subHeapIndex = 0;
			while(subHeapIndex++ != 8) {
				//DEBUG_PRINTF("SUBHEAP INDEX; %d\n", subHeapIndex - 1);
				uint64_t guardPagePtr = subHeapPtr + heapObjSize;
				uint64_t numGuardPages = (LARGE_SUBHEAP_SIZE/heapObjSize) >> 1;
				uint64_t numGuardPages_planted = 0;
				while(numGuardPages_planted++ != numGuardPages) {
					ASSERT(ShadowHeapMprotect(guardPagePtr, (uint64_t)DEFAULT_PAGE_SIZE, PROT_NONE) != -1,
									"Error: Could not plant a guardpage in the bag of large heaps.\n");
					guardPagePtr += ((uint64_t)DEFAULT_PAGE_SIZE + heapObjSize);
				}
				//DEBUG_PRINTF("SUBHEAP PTR: %p\n", subHeapPtr);
				//DEBUG_PRINTF("HEAP OBJ SIZE: %p\n", heapObjSize);
				//ReadProcMapsFile_PrintAddrDiff(subHeapPtr, subHeapPtr + (uint64_t)LARGE_SUBHEAP_SIZE);
				heapObjSize <<= 1;
				subHeapPtr += (uint64_t)LARGE_SUBHEAP_SIZE;
			}
			heapPtr += (uint64_t)LARGE_HEAP_SIZE;
		}
		//DEBUG_PRINTF("\n\n\n\n");
		//Print_Process_Layout();
		return;
	}

/* Any other heap type is invalid because other heap types would have no types at all */
	ERROR("Error invalid heap type specified for the bag to have guard pages placed.\n");
}
#endif

void Initialize_BagShadow(uint64_t bagPtr, uint64_t bagSize, int64_t shadowOffset, int8_t heapBagType)
{
/* Initiaize the the shadow metadata by making the subheap metadata pointer to an unused object
 * point to the first object of the subheap.
 */
	if(heapBagType == (int8_t)SMALL_HEAP_BAG) {
		struct shadowMetadata *metadataPtr =
				(struct shadowMetadata *)((bagPtr >> (uint64_t)SHADOW_MAP_SCALE) + shadowOffset);

	/* Iterate over the first heap to intialize the shadow */
		uint64_t subHeapPtr = bagPtr;
		uint64_t subHeapIndex = 0;
		while(subHeapIndex++ != 16) {
			metadataPtr->nextObjPtr = subHeapPtr;
			metadataPtr++;
			subHeapPtr += (uint64_t)SUBHEAP_SIZE;
		}
		return;
	}

/* Initialize shadow for large subheap */
	if(heapBagType == (int8_t)LARGE_HEAP_BAG) {
		struct shadowMetadata *metadataPtr =
				(struct shadowMetadata *)((bagPtr >> (uint64_t)LARGE_SHADOW_MAP_SCALE) + shadowOffset);

	/* Iterate over the first heap to intialize the shadow */
		uint64_t subHeapPtr = bagPtr;
		uint64_t subHeapIndex = 0;
		while(subHeapIndex++ != 8) {
			metadataPtr->nextObjPtr = subHeapPtr;
			metadataPtr++;
			subHeapPtr += (uint64_t)LARGE_SUBHEAP_SIZE;
		}
		return;
	}

/* Any other heap type is invalid because other heap types would have no types at all */
	ERROR("Error invalid heap type specified for its shadow to be initialized.\n");
}

inline
void Initialize_HeapBagType_HashTable(int8_t *hashTablePtr, uint64_t bagPtr, int8_t heapBagType)
{
/* Initialize the heap bag type hash table */
	uint64_t index = (bagPtr & (uint64_t)HASH_TABLE_KEY_MASK) >> (uint64_t)HASH_TABLE_SHIFT;
	*(hashTablePtr + index) = heapBagType;
}

inline uint64_t RoundUp_to_PageSize(uint64_t size)
{
	if(size & (~DEFAULT_PAGE_MASK))
		return ((size & (uint64_t)DEFAULT_PAGE_MASK) + (uint64_t)DEFAULT_PAGE_SIZE);
	return size;
}


/**************************************** MANAGER FUNCTIONS ******************************/

/* It might be worth inlining if we allow use after free since
 * code size will be smaller in this case.
 */
#ifdef ALLOW_USE_AFTER_FREE
inline
#endif
void AddFreeNode(struct perThreadInfo *threadInfoPtr, struct freeObjNode **freeListPtr, uint64_t freeObjPtr)
{
#ifdef DEBUG
	DEBUG_PRINTF("ADD FREE NODE\n");
#endif

/* Add the a new free node to the list */
	if(*freeListPtr) {
	#ifndef ALLOW_USE_AFTER_FREE
	/* Free objects are added to the bottom of the free list to avoid use-after-free attacks */
		struct freeObjNode *nodePtr = *freeListPtr;
		while(nodePtr->nextNode) {
		/* Look for double frees (if the programmer has not disabled this feature) */
		#ifndef ALLOW_DOUBLE_FREES
		#ifndef DONT_THROW_EXECEPTION_ON_ERROR
		/* ASSERT not used for optimization purposes */
			if(nodePtr->objPtr == freeObjPtr) {

				char errorMessage[1024] = {0};
				__Safe_Sprintf(errorMessage, 1024,
						"Error: Object at %p double freed.\n", freeObjPtr);
				ERROR(errorMessage);
			}
		#else
			//if(nodePtr->objPtr == freeObjPtr)
				//return;
			if(WARN(nodePtr->objPtr == freeObjPtr, "Warning: Double free detected.\n"))
				return;
		#endif
		#endif
			nodePtr = nodePtr->nextNode;
		}

	/* Get a free node */
		struct freeObjNode *freeNodePtr;
		if(!(threadInfoPtr->freeListsSpace_freeList)) {
			freeNodePtr = threadInfoPtr->freeListsEmptyNode;
			(threadInfoPtr->freeListsEmptyNode)++;
		} else {
			freeNodePtr = threadInfoPtr->freeListsSpace_freeList;
			threadInfoPtr->freeListsSpace_freeList = freeNodePtr->nextNode;
		}

	/* Append a new free Node */
		nodePtr->nextNode = freeNodePtr;
	#else
	/* If the programmer chooses to not to enable HeapGuard to take measures to
	 * prevent use-after-free attacks, we try to optimize for performance by
	 * prepending the new free nodes instead of appending them.
	 */
		struct freeObjNode *freeNodePtr;
		if(!(threadInfoPtr->freeListsSpace_freeList)) {
			freeNodePtr = threadInfoPtr->freeListsEmptyNode;
			(threadInfoPtr->freeListsEmptyNode)++;
		} else {
			freeNodePtr = threadInfoPtr->freeListsSpace_freeList;
			threadInfoPtr->freeListsSpace_freeList = freeNodePtr->nextNode;
		}

		freeNodePtr->nextNode = *freeListPtr;
		freeNodePtr->objPtr = freeObjPtr;
		*freeListPtr = freeNodePtr;
	#endif
		freeNodePtr->objPtr = freeObjPtr;
		freeNodePtr->nextNode = NULL;
	}

/* If a free list for a subheap does not exist.. */
	struct freeObjNode *freeNodePtr;
	if(!(threadInfoPtr->freeListsSpace_freeList)) {
		freeNodePtr = threadInfoPtr->freeListsEmptyNode;
		(threadInfoPtr->freeListsEmptyNode)++;
	} else {
		freeNodePtr = threadInfoPtr->freeListsSpace_freeList;
		threadInfoPtr->freeListsSpace_freeList = freeNodePtr->nextNode;
	}
	*freeListPtr = freeNodePtr;
	freeNodePtr->objPtr = freeObjPtr;
	freeNodePtr->nextNode = NULL;
}

inline
uint64_t RemoveFreeNode(struct perThreadInfo *threadInfoPtr, struct freeObjNode **freeListPtrAddr)
{
#ifdef DEBUG
	DEBUG_PRINTF("REMOVING FREE NODE\n");
#endif
	struct freeObjNode *nodePtr = threadInfoPtr->freeListsSpace_freeList;
	threadInfoPtr->freeListsSpace_freeList = *freeListPtrAddr;
	*freeListPtrAddr = threadInfoPtr->freeListsSpace_freeList->nextNode;
	threadInfoPtr->freeListsSpace_freeList->nextNode = nodePtr;
	return threadInfoPtr->freeListsSpace_freeList->objPtr;
}

inline
uint64_t AllocateNewBag(struct perThreadInfo *threadInfoPtr, uint64_t size, int8_t heapBagType)
{
#ifdef DEBUG
	DEBUG_PRINTF("****************ALLOC NEW BAG**********************\n");
#endif

/* Map a new bag */
	uint64_t bagPtr = Map_HeapBag(size);

#ifndef DO_NOT_GUARD_PAGES
/* Place the guard pages */
	PlantGuardPages(bagPtr, size, heapBagType);
#endif

/* Save the heap bag type in the hash table */
	uint64_t index = bagPtr >> (uint64_t)HASH_TABLE_SHIFT;
	*((threadInfoPtr->heapBagType_hashPtr) + index) = heapBagType;
	DEBUG_PRINTF("****************ALLOC NEW BAG**********************\n");
	DEBUG_PRINTF("threadInfoPtr: %p\n", threadInfoPtr);
	DEBUG_PRINTF("threadInfoPtr->heapBagType_hashPtr: %p\n", threadInfoPtr->heapBagType_hashPtr);
	Print_Process_Layout();

	return bagPtr;
}

uint64_t Get_HeapObjSize(struct perThreadInfo *threadInfoPtr, uint64_t heapObjPtr)
{
/* Find the heap type in question */
	uint64_t realBagAddr = heapObjPtr & (uint64_t)HEAP_BAG_MASK;
	uint64_t hashIndex = (uint64_t)realBagAddr >> (uint64_t)HASH_TABLE_SHIFT;
	int8_t heapBagType = *((threadInfoPtr->heapBagType_hashPtr) + hashIndex);
	//DEBUG_PRINTF("GET HEAP OBJ SIZE\n");
	//DEBUG_PRINTF("threadInfoPtr: %p\n", threadInfoPtr);
	//DEBUG_PRINTF("threadInfoPtr->heapBagType_hashPtr: %p\n", threadInfoPtr->heapBagType_hashPtr);

/* We need to perform some sanity checks and compute heap object size */
	if(heapBagType == (int8_t)SMALL_HEAP_BAG) {
		//DEBUG_PRINTF("SMALL HEAP BAG TYPE\n");
	/* Now we try to find the equivalent pointer in the primary bag */
		uint64_t realSubHeapAddr = heapObjPtr & (uint64_t)SUBHEAP_MASK;
		uint64_t realHeapAddr = (uint64_t)heapObjPtr & (uint64_t)HEAP_MASK;
		uint64_t subHeapIndex = (realSubHeapAddr - realHeapAddr) >> (uint64_t)SUBHEAP_SHIFT;
		//DEBUG_PRINTF("---------subHeapIndex: %d\n", subHeapIndex);

	/* We need to check if the pointer is aligned properly to the object */
		if(subHeapIndex < 8) {
		/* Check if the given pointer is aligned to the object */
		#ifndef DONT_THROW_EXECEPTION_ON_ERROR
			ASSERT(!(heapObjPtr & (~(uint64_t)(~0) << (MIN_OBJ_SHIFT + subHeapIndex))),
				"Error: Pointer for given heap object is not properly aligned to object address.\n");
		#else
			int8_t warning =
				WARN(!(heapObjPtr & (~(uint64_t)(~0) << (MIN_OBJ_SHIFT + subHeapIndex))),
						"Warning: Pointer for given heap object is not properly aligned to object address.\n");
			if(warning)
				return (uint64_t)INVALID_HEAPOBJ_SIZE;
		#endif
		} else {
		/* The given pointer must be page-aligned */
		#ifndef DONT_THROW_EXECEPTION_ON_ERROR
			ASSERT(!(heapObjPtr & (~(uint64_t)DEFAULT_PAGE_MASK)),
				"Error: Pointer for given heap object is not properly aligned to object address.\n");
		#else
			int8_t warning =
				WARN(!(heapObjPtr & (~(uint64_t)DEFAULT_PAGE_MASK)),
						"Warning: Pointer for given heap object is not properly aligned to object address.\n");
			if(warning)
				return (uint64_t)INVALID_HEAPOBJ_SIZE;
		#endif
		}

	/* Compute the size of the heap object */
		return ((uint64_t)1 << (MIN_OBJ_SHIFT + subHeapIndex));
	}

	if(heapBagType == (int8_t)LARGE_HEAP_BAG) {
	/* The given pointer must be page-aligned */
	#ifndef DONT_THROW_EXECEPTION_ON_ERROR
		ASSERT(!(heapObjPtr & (~(uint64_t)DEFAULT_PAGE_MASK)),
					"Error: Pointer for given heap object is not properly aligned to object address.\n");
	#else
		int8_t warning = WARN(!(heapObjPtr & (~(uint64_t)DEFAULT_PAGE_MASK)),
					"Warning: Pointer for given heap object is not properly aligned to object address.\n");
		if(warning)
			return (uint64_t)INVALID_HEAPOBJ_SIZE;
	#endif

		uint64_t realSubHeapAddr = heapObjPtr & (uint64_t)LARGE_SUBHEAP_MASK;
		uint64_t realHeapAddr = (uint64_t)heapObjPtr & (uint64_t)LARGE_HEAP_MASK;
		uint64_t subHeapIndex = (realSubHeapAddr - realHeapAddr) >> (uint64_t)LARGE_SUBHEAP_SHIFT;

	/* Compute the size of the heap object */
		return ((uint64_t)1 << (MIN_LARGE_OBJ_SHIFT + subHeapIndex));
	}

#ifndef DONT_THROW_EXECEPTION_ON_ERROR
/* This means it must be a big block */
	ASSERT(heapBagType == (int8_t)BIG_BLOCK,
				"Error: Error in heap type hash table found. HeapGuard metadata corrupt "
					"or an attempt made to point to an unallocated object.\n");

/* The given pointer must be page-aligned */
	ASSERT(!(heapObjPtr & (~(uint64_t)DEFAULT_PAGE_MASK)),
				"Error: Pointer for given heap object is not properly aligned to object address.\n");
#else
/* This means it must be a big block */
	int8_t warning = WARN(heapBagType == (int8_t)BIG_BLOCK,
				"Warning: Error in heap type hash table found. HeapGuard metadata corrupt "
								"or the given pointer pointing to an unallocated object.\n");
	if(warning)
		return (uint64_t)INVALID_HEAPOBJ_SIZE;

/* The given pointer must be page-aligned */
	warning  = WARN(!(heapObjPtr & (~(uint64_t)DEFAULT_PAGE_MASK)),
				"Warning: Pointer for given heap object is not properly aligned to object address.\n");
	if(warning)
		return (uint64_t)INVALID_HEAPOBJ_SIZE;
#endif

/* We consider the size of the given oject in this to be equal to the size of a heap bag */
	return (uint64_t)HEAP_BAG_SIZE;
}


/***************************************** HEAP ALLOCATOR API *****************************/

/* This malloc should not return NULL unless the size is zero */
#ifdef WRAP_MALLOC
inline
#endif
void *Heap_malloc(uint64_t objSize)
{
/* Heap_malloc returns NULL if the size if zero */
	if(WARN(objSize, "Warning: Object size is zero\n"))
		return NULL;
	
/* Default attribute constructor might not work for c++ compilers */
//#ifdef __cplusplus
	if(heapGuardState == (int8_t)HEAPGUARD_UNINITIALIZED)
		Init_HeapGuard();
//#endif

#ifdef DEBUG
	state = (int8_t)MALLOC_USED;
	DEBUG_PRINTF("**** MALLOC ****\n");
	DEBUG_PRINTF("OBJ SIZE: %p %d\n", objSize, objSize);
#endif

	//DEBUG_PRINTF("***** MALLOC *****\n");
/* Look up the thread info */
	//DEBUG_PRINTF("(pthread_self() & (uint64_t)THREAD_INFO_NUM_ELEM) >> 12: %d\n",
	//						(pthread_self() & (uint64_t)THREAD_INFO_NUM_ELEM) >> 12);
	struct perThreadInfo *threadInfoPtr =
			threadInfo[(pthread_self() & (uint64_t)THREAD_INFO_NUM_ELEM) >> 12];
	//DEBUG_PRINTF("**** MALLOC ****\n");
	//DEBUG_PRINTF("threadInfoPtr: %p\n", threadInfoPtr);
	//DEBUG_PRINTF("threadInfoPtr->heapBagType_hashPtr: %p\n", threadInfoPtr->heapBagType_hashPtr);

	if(objSize <= (uint64_t)MAX_SMALL_OBJ_SIZE) {
	/* Get the subheap of the heap. Here the size is going to be less than 4Gb
	 * anyways so we cast the size to get the number of bytes following the most
	 * significant 1-bit.
	 */
		uint64_t minSizeExp = 31 - (uint64_t)__builtin_clz((uint32_t)objSize);
		int64_t subHeapIndex = minSizeExp - (uint64_t)MIN_OBJ_SHIFT;

	/* If the object size is not aligned well with the standard sizes, then go to
	 * the next subheap.
	 */
		if(subHeapIndex < 0) {
			subHeapIndex = 0;
			minSizeExp = MIN_OBJ_SHIFT;
		} else {
			if(((uint64_t)1 << minSizeExp) < objSize) {
				minSizeExp++;
				subHeapIndex++;
			}
		}

	/* Get the address to the metadata */
		uint64_t subHeapAddr =
				(threadInfoPtr->primaryHeap[0]) + (subHeapIndex << (uint64_t)SUBHEAP_SHIFT);
		struct shadowMetadata *metadataPtr =
				(struct shadowMetadata *)((subHeapAddr >> (uint64_t)SHADOW_MAP_SCALE)
														+ (threadInfoPtr->shadowOffset[0]));
	#ifdef DEBUG
		DEBUG_PRINTF("MALLOC: minSizeExp: %d\n", minSizeExp);
		DEBUG_PRINTF("MALLOC: subHeapIndex: %d\n", subHeapIndex);
		DEBUG_PRINTF("MALLOC: subheapAddr: %p\n", subHeapAddr);
		DEBUG_PRINTF("MALLOC: metadata: %p\n", metadataPtr);
	#endif

	/* Check if the free list exists */
		if(metadataPtr->freeListPtr) {
			uint64_t mallocPtr = RemoveFreeNode(threadInfoPtr,
								(struct freeObjNode **)(&(metadataPtr->freeListPtr)));
		#ifdef DEBUG
			DEBUG_PRINTF("USE FREE NODE\n");
			DEBUG_PRINTF("MALLOC POINTER: %p\n", mallocPtr);
			//Print_SubHeap_Layout(realSubHeapAddr);
			state = (int8_t)DONE;
		#endif
			return (void *)mallocPtr;
		}

	/* Since the free list does not exist, we allocate the space directly */
		uint64_t mallocPtr = metadataPtr->nextObjPtr;
		uint64_t supersetSize = (uint64_t)1 << minSizeExp;
		metadataPtr->nextObjPtr += supersetSize;

	/* We have to check if the next object pointer becomes page aligned because
	 * every other page for small allocations is a guard page. This check is
	 * mainly for small allocations less than a page big.
	 */
		if((metadataPtr->nextObjPtr) & (~(uint64_t)DEFAULT_PAGE_MASK)) {
		#ifdef DEBUG
			DEBUG_PRINTF("MALLOC POINTER: %p\n", mallocPtr);
			DEBUG_PRINTF("void *MALLOC POINTER: %p\n", (void *)mallocPtr);
			//Print_SubHeap_Layout(mallocPtr & (uint64_t)SUBHEAP_MASK);
			state = (int8_t)DONE;
		#endif
			return (void *)mallocPtr;
		}

	/* Skip the guard page*/
		uint64_t realSubHeapAddr = (metadataPtr->nextObjPtr) & (uint64_t)SUBHEAP_MASK;

	#ifndef DO_NOT_GUARD_PAGES
		metadataPtr->nextObjPtr += (uint64_t)DEFAULT_PAGE_SIZE;
	#endif

	/* Now we have to check if the pointer is pointing to the next subHeap
	 * i.e. this object's subHeap is full (since the next object pointer is
	 * page aligned.
	 */
		int64_t leftoverSize = realSubHeapAddr + (uint64_t)SUBHEAP_SIZE -
								(metadataPtr->nextObjPtr) - (uint64_t)DEFAULT_PAGE_SIZE;
		if(leftoverSize < supersetSize) {
		/* Allocate a new heap. But we need to check if we need tp map a new bag */
			uint64_t realBagAddr = (metadataPtr->nextObjPtr) & (uint64_t)HEAP_BAG_MASK;

		/* Check if the end of the bag has been hit */
			if(metadataPtr->nextObjPtr == realBagAddr)
				realBagAddr -= (uint64_t)HEAP_BAG_SIZE;

		/* Check if the last subheap is full */
			if(realSubHeapAddr + (uint64_t)HEAP_SIZE
					> realBagAddr + (uint64_t)HEAP_BAG_SIZE) {
			/* Map a new bag */
				//DEBUG_PRINTF("size: %d\n", objSize);
				uint64_t bagPtr = AllocateNewBag(threadInfoPtr, (uint64_t)HEAP_BAG_SIZE,
																		(int8_t)SMALL_HEAP_BAG);
				metadataPtr->nextObjPtr = bagPtr + (subHeapIndex << (uint64_t)SUBHEAP_SHIFT);
			} else {
			/* Use the next adjacent heap */
				metadataPtr->nextObjPtr = realSubHeapAddr + (uint64_t)HEAP_SIZE;
			}
		}

	#ifdef DEBUG
		DEBUG_PRINTF("MALLOC POINTER: %p\n", mallocPtr);
		Print_SubHeap_Layout(realSubHeapAddr);
		state = (int8_t)DONE;
	#endif
		return (void *)mallocPtr;
	}

/* Check if we really need to use the largest heap */
	if(objSize <= (uint64_t)LARGEST_PREALLOCATED_SIZE) {
		//DEBUG_PRINTF("LARGE ALLOCATION\n");
	/* Get the subheap of the heap. Here the size is going to be less than 4Gb
	 * anyways so we cast the size to get the number of bites following the most
	 * significant 1-bit.
	 */
		uint64_t minSizeExp = 31 - (uint64_t)__builtin_clz((uint32_t)objSize);
		uint64_t subHeapIndex = minSizeExp - (uint64_t)MIN_LARGE_OBJ_SHIFT;

	/* If the object size is not aligned well with the standard sizes, then go to
	 * the next subheap.
	 */
		if(((uint64_t)1 << minSizeExp) < objSize) {
			minSizeExp++;
			subHeapIndex++;
		}

	/* Get the address to the metadata */
		uint64_t subHeapAddr =
				(threadInfoPtr->primaryHeap[1]) + (subHeapIndex << (uint64_t)LARGE_SUBHEAP_SHIFT);
		struct shadowMetadata *metadataPtr =
				(struct shadowMetadata *)((subHeapAddr >> (uint64_t)LARGE_SHADOW_MAP_SCALE)
															+ (threadInfoPtr->shadowOffset[1]));
	#ifdef DEBUG
		DEBUG_PRINTF("MALLOC: minSizeExp: %d\n", minSizeExp);
		DEBUG_PRINTF("MALLOC: subHeapIndex: %d\n", subHeapIndex);
		DEBUG_PRINTF("MALLOC: subheapAddr: %p\n", subHeapAddr);
		DEBUG_PRINTF("MALLOC: metadata: %p\n", metadataPtr);
	#endif

	/* Check if the free list exists */
		if(metadataPtr->freeListPtr) {
			uint64_t mallocPtr = RemoveFreeNode(threadInfoPtr,
											(struct freeObjNode **)(&(metadataPtr->freeListPtr)));
		#ifdef DEBUG
			DEBUG_PRINTF("FROM FREELIST\n");
			DEBUG_PRINTF("MALLOC POINTER: %p\n", mallocPtr);
			//Print_SubHeap_Layout(realSubHeapAddr);
			state = (int8_t)DONE;
		#endif
			return (void *)mallocPtr;
		}
		//DEBUG_PRINTF("LAYOUT BEFORE ALLOCATION\n");
		//Print_SubHeap_Layout(realSubHeapAddr);

	/* Since the free list does not exist, we allocate the space directly */
		uint64_t mallocPtr = metadataPtr->nextObjPtr;
		//DEBUG_PRINTF("MALLOC: matadataPtr->nextObjPtr: %p\n", metadataPtr->nextObjPtr);
		//DEBUG_PRINTF("MALLOCPTR: %p\n", mallocPtr);
		uint64_t supersetSize = (uint64_t)1 << minSizeExp;
		metadataPtr->nextObjPtr += supersetSize;

	/* Skip the guard page*/
		uint64_t realSubHeapAddr = (metadataPtr->nextObjPtr) & (uint64_t)LARGE_SUBHEAP_MASK;

	#ifndef DO_NOT_GUARD_PAGES
		metadataPtr->nextObjPtr += (uint64_t)DEFAULT_PAGE_SIZE;
	#endif

	/* Now we have to check if the pointer is pointing to the next subHeap
	 * i.e. this object's subHeap is full (since the next object pointer is
	 * page aligned.
	 */
		int64_t leftoverSize = realSubHeapAddr + (uint64_t)LARGE_SUBHEAP_SIZE -
								(metadataPtr->nextObjPtr) - (uint64_t)DEFAULT_PAGE_SIZE;
		if(leftoverSize < supersetSize) {
		/* Allocate a new heap. But we need to check if we need tp map a new bag */
			uint64_t realBagAddr = (metadataPtr->nextObjPtr) & (uint64_t)HEAP_BAG_MASK;

		/* Check if the end of the bag has been hit */
			if(metadataPtr->nextObjPtr == realBagAddr)
				realBagAddr -= (uint64_t)HEAP_BAG_SIZE;

		/* Check if the last subheap is full */
			if(realSubHeapAddr + (uint64_t)LARGE_HEAP_SIZE
							> realBagAddr + (uint64_t)HEAP_BAG_SIZE) {
			/* Map a new bag */
				uint64_t bagPtr = AllocateNewBag(threadInfoPtr, (uint64_t)HEAP_BAG_SIZE,
																		(int8_t)LARGE_HEAP_BAG);
				metadataPtr->nextObjPtr = bagPtr + (subHeapIndex << (uint64_t)LARGE_SUBHEAP_SHIFT);
			} else {
			/* Use the next adjacent heap */
				metadataPtr->nextObjPtr = realSubHeapAddr + (uint64_t)LARGE_HEAP_SIZE;
			}
		}

	#ifdef DEBUG
		DEBUG_PRINTF("MALLOC POINTER: %p\n", mallocPtr);
		Print_SubHeap_Layout(realSubHeapAddr);
		state = (int8_t)DONE;
	#endif
		return (void *)mallocPtr;
	}

/* Now, simply map the object as a bag. But before that, we need to make
 * sure that the size is a multiple of bag size. If not,make it a multiple
 * of heap bag size.
 */
	if(objSize & (uint64_t)HEAP_BAG_SIZE_MASK)
		objSize = (objSize & (uint64_t)HEAP_BAG_ALIGN_MASK) + (uint64_t)HEAP_BAG_SIZE;

	uint64_t mallocPtr = (uint64_t)Map_HeapBag(objSize);
	//DEBUG_PRINTF("******************OBJSIZE: %d\n", objSize);
/* This means that the allocation size is too huge */
	uint64_t index = (mallocPtr & (uint64_t)HASH_TABLE_KEY_MASK) >> (uint64_t)HASH_TABLE_SHIFT;
	*((threadInfoPtr->heapBagType_hashPtr) + index) = (int8_t)BIG_BLOCK;
	//DEBUG_PRINTF("threadInfoPtr: %p\n", threadInfoPtr);
	//DEBUG_PRINTF("threadInfoPtr->heapBagType_hashPtr: %p\n", threadInfoPtr->heapBagType_hashPtr);

#ifdef DEBUG
	DEBUG_PRINTF("MALLOC POINTER: %p\n", mallocPtr);
	Print_SubHeap_Layout(mallocPtr);
	state = (int8_t)DONE;
#endif
	return (void *)mallocPtr;
}

#ifdef WRAP_FREE
inline
#endif
void Heap_free(void *heapObjPtr)
{
#ifndef DONT_THROW_EXECEPTION_ON_ERROR
	ASSERT(heapObjPtr, "Error: NULL pointer freed.\n");
#else
	//if(WARN(heapObjPtr, "Warning: NULL pointer freed.\n")) {
	if(!heapObjPtr) {
	#ifdef DEBUG
		state = (int8_t)DONE;
	#endif
		return;
	}
#endif

	#ifdef DEBUG
		state = (int8_t)FREE_USED;
		DEBUG_PRINTF("***FREE***\n");
		DEBUG_PRINTF("POINTER TO BE FREED: %p\n", heapObjPtr);
	#endif

/* Look up the thread info */
	struct perThreadInfo *threadInfoPtr =
				threadInfo[(pthread_self() & (uint64_t)THREAD_INFO_NUM_ELEM) >> 12];
	//DEBUG_PRINTF("***FREE***\n");
	//DEBUG_PRINTF("threadInfoPtr: %p\n", threadInfoPtr);
	//DEBUG_PRINTF("threadInfoPtr->heapBagType_hashPtr: %p\n", threadInfoPtr->heapBagType_hashPtr);
	//DEBUG_PRINTF("POINTER TO BE FREED: %p\n", heapObjPtr);
	uint64_t hashIndex = (uint64_t)heapObjPtr >> (uint64_t)HASH_TABLE_SHIFT;
	//DEBUG_PRINTF("hash index: %d %p\n", hashIndex, hashIndex);
	//DEBUG_PRINTF("threadInfoPtr->heapBagType_hashPtr: %p\n", threadInfoPtr->heapBagType_hashPtr);
	//DEBUG_PRINTF("Dereference address: %p\n", (threadInfoPtr->heapBagType_hashPtr) + hashIndex);
	int8_t heapBagType = *((threadInfoPtr->heapBagType_hashPtr) + hashIndex);

	if(heapBagType == (int8_t)SMALL_HEAP_BAG) {
	/* Now we try to find the equivalent pointer in the primary bag */
		uint64_t realSubHeapAddr = (uint64_t)heapObjPtr & (uint64_t)SUBHEAP_MASK;
		uint64_t realHeapAddr = (uint64_t)heapObjPtr & (uint64_t)HEAP_MASK;
		uint64_t subHeapIndex = (realSubHeapAddr - realHeapAddr) >> (uint64_t)SUBHEAP_SHIFT;

	/* We need to check if the pointer is aligned properly to the object */
		if(subHeapIndex < 8) {
		/* Check if the given pointer is aligned to the object */
		#ifndef DONT_THROW_EXECEPTION_ON_ERROR
			ASSERT(!((uint64_t)heapObjPtr & (~(uint64_t)(~0) << (MIN_OBJ_SHIFT + subHeapIndex))),
				"Error: Pointer being freed is not properly aligned to object address.\n");
		#else
			int8_t warning =
				WARN(!((uint64_t)heapObjPtr & (~(uint64_t)(~0) << (MIN_OBJ_SHIFT + subHeapIndex))),
						"Warning: Pointer being freed is not properly aligned to object address.\n");
			if(warning) {
			#ifdef DEBUG
				state = (int8_t)DONE;
			#endif
				return;
			}
		#endif
		} else {
		/* The given pointer must be page-aligned */
		#ifndef DONT_THROW_EXECEPTION_ON_ERROR
			ASSERT(!((uint64_t)heapObjPtr & (~(uint64_t)DEFAULT_PAGE_MASK)),
				"Error: Pointer being freed is not properly aligned to object address.\n");
		#else
			int8_t warning =
				WARN(!((uint64_t)heapObjPtr & (~(uint64_t)DEFAULT_PAGE_MASK)),
						"Warning: Pointer being freed is not properly aligned to object address.\n");
			if(warning) {
			#ifdef DEBUG
				state = (int8_t)DONE;
			#endif
				return;
			}
		#endif
		}

		//DEBUG_PRINTF("FREE: SUBHEAP INDEX: %d\n", subHeapIndex);
		uint64_t subHeapAddr =
				(threadInfoPtr->primaryHeap[0]) + (subHeapIndex << (uint64_t)SUBHEAP_SHIFT);
		//DEBUG_PRINTF("FREE: subheapAddr: %p\n", subHeapAddr);

	/* Get the address to the metadata */
		struct shadowMetadata *metadataPtr =
				(struct shadowMetadata *)((subHeapAddr >> SHADOW_MAP_SCALE)
														+ (threadInfoPtr->shadowOffset[0]));
		//DEBUG_PRINTF("FREE: shadow offset: %p\n", threadInfoPtr->shadowOffset[0]);
		//DEBUG_PRINTF("FREE: metadataPtr: %p\n", metadataPtr);

	/* Add the pointer to the free list */
		AddFreeNode(threadInfoPtr, (struct freeObjNode **)&(metadataPtr->freeListPtr),
																			(uint64_t)heapObjPtr);
	#ifdef DEBUG
		state = (int8_t)DONE;
	#endif
		return;
	}

	if(heapBagType == (int8_t)LARGE_HEAP_BAG) {
	/* The given pointer must be page-aligned */
	#ifndef DONT_THROW_EXECEPTION_ON_ERROR
		ASSERT(!((uint64_t)heapObjPtr & (~(uint64_t)DEFAULT_PAGE_MASK)),
					"Error: Pointer being freed is not properly aligned to object address.\n");
	#else
		int8_t warning = WARN(!((uint64_t)heapObjPtr & (~(uint64_t)DEFAULT_PAGE_MASK)),
					"Warning: Pointer being freed is not properly aligned to object address.\n");
		if(warning) {
		#ifdef DEBUG
			state = (int8_t)DONE;
		#endif
			return;
		}
	#endif

	/* Now we try to find the equivalent pointer in the primary bag */
		uint64_t realSubHeapAddr = (uint64_t)heapObjPtr & (uint64_t)LARGE_SUBHEAP_MASK;
		uint64_t realHeapAddr = (uint64_t)heapObjPtr & (uint64_t)LARGE_HEAP_MASK;
		uint64_t subHeapIndex = (realSubHeapAddr - realHeapAddr) >> (uint64_t)LARGE_SUBHEAP_SHIFT;
		uint64_t subHeapAddr =
				(threadInfoPtr->primaryHeap[1]) + (subHeapIndex << (uint64_t)LARGE_SUBHEAP_SHIFT);

	/* Get the address to the metadata */
		struct shadowMetadata *metadataPtr =
				(struct shadowMetadata *)((subHeapAddr >> LARGE_SHADOW_MAP_SCALE)
														+ (threadInfoPtr->shadowOffset[1]));

	/* Add the pointer to the free list */
		AddFreeNode(threadInfoPtr, (struct freeObjNode **)&(metadataPtr->freeListPtr),
																	(uint64_t)heapObjPtr);
	#ifdef DEBUG
		state = (int8_t)DONE;
	#endif
		return;
	}

#ifndef DONT_THROW_EXECEPTION_ON_ERROR
/* This means it must be a big block */
	ASSERT(heapBagType == (int8_t)BIG_BLOCK,
				"Error: Error in heap type hash table found. HeapGuard metadata corrupt "
					"or an attempt made to free an unallocated object.\n");

/* The given pointer must be page-aligned */
	ASSERT(!((uint64_t)heapObjPtr & (~(uint64_t)DEFAULT_PAGE_MASK)),
				"Error: Pointer being freed is not properly aligned to object address.\n");
#else
/* This means it must be a big block */
	int8_t warning = WARN(heapBagType == (int8_t)BIG_BLOCK,
				"Warning: Error in heap type hash table found. HeapGuard metadata corrupt "
								"or an attempt made to free an unallocated object.\n");
	if(warning) {
	#ifdef DEBUG
		state = (int8_t)DONE;
	#endif
		return;
	}

/* The given pointer must be page-aligned */
	warning  = WARN(!((uint64_t)heapObjPtr & (~(uint64_t)DEFAULT_PAGE_MASK)),
				"Warning: Pointer being freed is not properly aligned to object address.\n");
	if(warning) {
	#ifdef DEBUG
		state = (int8_t)DONE;
	#endif
		return;
	}
#endif

/* We simply unmap a heap bag. If we the size of the block is larger than
 * the heap bag, we cannot unmap it since we cannot keep track of it. Heap
 * bag is large enough that the chances of mapping a block larger than heap
 * bag are very, very low indeed. Blocks are guaranteed to be at least bag size.
 */
	HeapMunmap((uint64_t)heapObjPtr, (uint64_t)HEAP_BAG_SIZE);
	*((threadInfoPtr->heapBagType_hashPtr) + hashIndex) = 0;
	DEBUG_PRINTF("threadInfoPtr: %p\n", threadInfoPtr);
	DEBUG_PRINTF("threadInfoPtr->heapBagType_hashPtr: %p\n", threadInfoPtr->heapBagType_hashPtr);
#ifdef DEBUG
	state = (int8_t)DONE;
#endif
}

#ifdef WRAP_FREE
inline
#endif
void *Heap_calloc(uint64_t nmemb, uint64_t size)
{
#ifdef DEBUG
	DEBUG_PRINTF("*****CALLOC*****\n");
#endif
	//DEBUG_PRINTF("*****CALLOC*****\n");
/* Allocate the object first */
	uint64_t objSize = nmemb * size;
	uint64_t mallocPtr = (uint64_t)Heap_malloc(objSize);

/* Set the object bytes to zero */
	return __Safe_Memset_Zero((void *)mallocPtr, objSize);
}

#ifdef WRAP_REALLOC
inline
#endif
void *Heap_realloc(void *heapObjPtr, uint64_t objSize)
{
/* Heap_realloc returns NULL if the size if zero */
	if(WARN(objSize, "Warning: Object size is zero\n"))
		return NULL;	
	
/* First we need to check if the given pointer is NULL */
	if(!heapObjPtr)
		return Heap_malloc(objSize);

#ifdef DEBUG
	state = (int8_t)REALLOC_USED;
	//DEBUG_PRINTF("*****REALLOC*****\n");
#endif
	//DEBUG_PRINTF("*****REALLOC*****\n");
	struct perThreadInfo *threadInfoPtr =
					threadInfo[(pthread_self() & (uint64_t)THREAD_INFO_NUM_ELEM) >> 12];
	//DEBUG_PRINTF("threadInfoPtr: %p\n", threadInfoPtr);
	//DEBUG_PRINTF("threadInfoPtr->heapBagType_hashPtr: %p\n", threadInfoPtr->heapBagType_hashPtr);

	uint64_t heapObjSize = Get_HeapObjSize(threadInfoPtr, (uint64_t)heapObjPtr);
	//DEBUG_PRINTF("HEAP OBJ SIZE: %p %d\n", heapObjSize, heapObjSize);
	if(heapObjSize == (uint64_t)INVALID_HEAPOBJ_SIZE) {
	#ifdef DEBUG
		DEBUG_PRINTF("INVALID SIZE !!!!\n");
		DEBUG_PRINTF("REALLOC: HEAP OBJ PTR: %p\n", heapObjPtr);
		DEBUG_PRINTF("REALLOC: OBJ SIZE: %d %p\n", objSize, objSize);
		state = (int8_t)DONE;
	#endif
		return NULL;
	}

/* Now we need to find the size of the object ptr is pointing
 * to. If the objsize is less than the computed object size, we
 * reallocate. If the size of the object is equal to the one being
 * pointed at, we do not make any changes. If the object size is
 * more than the current size, reallocate.
 */
	//DEBUG_PRINTF("REALLOC: HEAP OBJ PTR: %p\n", heapObjPtr);
	//DEBUG_PRINTF("HEAP OBJ SIZE: %p %d\n", heapObjSize, heapObjSize);
	//DEBUG_PRINTF("REALLOC: OBJ SIZE: %d %p\n", objSize, objSize);
#ifdef DEBUG
	DEBUG_PRINTF("HEAP OBJ SIZE: %p %d\n", heapObjSize, heapObjSize);
	DEBUG_PRINTF("REALLOC: HEAP OBJ PTR: %p\n", heapObjPtr);
	DEBUG_PRINTF("REALLOC: OBJ SIZE: %d %p\n", objSize, objSize);
#endif
	uint64_t givenSupersetSize;
	uint64_t mallocPtr;
	if(objSize <= (uint64_t)MAX_SMALL_OBJ_SIZE) {
	/* Get the subheap of the heap. Here the size is going to be less than 4Gb
	 * anyways so we cast the size to get the number of bytes following the most
	 * significant 1-bit.
	 */
		uint64_t minSizeExp = 31 - (uint64_t)__builtin_clz((uint32_t)objSize);
		int64_t subHeapIndex = minSizeExp - (uint64_t)MIN_OBJ_SHIFT;

	/* If the object size is not aligned well with the standard sizes, then go to
	 * the next subheap.
	 */
		if(subHeapIndex < 0) {
			subHeapIndex = 0;
			minSizeExp = MIN_OBJ_SHIFT;
		} else {
			if(((uint64_t)1 << minSizeExp) < objSize) {
				minSizeExp++;
				subHeapIndex++;
			}
		}
		//DEBUG_PRINTF("REALLOC: minSizeExp: %d\n", minSizeExp);
		//DEBUG_PRINTF("REALLOC: subHeapIndex: %d\n", subHeapIndex);

	/* Compute the real object size */
		givenSupersetSize = (uint64_t)1 << minSizeExp;
		//DEBUG_PRINTF("GIVEN SUPERSET SIZE: %p %d\n", givenSupersetSize, givenSupersetSize);

	/* Now, we need to see how the sizes compare */
		if(givenSupersetSize == heapObjSize) {
		#ifdef DEBUG
			DEBUG_PRINTF("SMALL HEAP MATCH\n");
			state = (int8_t)DONE;
		#endif
			//DEBUG_PRINTF("REALLOC PTR: %p\n", heapObjPtr);
			return heapObjPtr;
		}

	/* Now, this means the sizes differ and we need to allocate a separate object */
		uint64_t subHeapAddr =
				(threadInfoPtr->primaryHeap[0]) + (subHeapIndex << (uint64_t)SUBHEAP_SHIFT);
		//DEBUG_PRINTF("REALLOC: subheapAddr: %p\n", subHeapAddr);

	/* Get the metadata */
		struct shadowMetadata *metadataPtr =
				(struct shadowMetadata *)((subHeapAddr >> (uint64_t)SHADOW_MAP_SCALE)
														+ (threadInfoPtr->shadowOffset[0]));
		//DEBUG_PRINTF("REALLOC: metadata: %p\n", metadataPtr);

	/* Check if the free list exists */
		if(metadataPtr->freeListPtr) {
			mallocPtr = RemoveFreeNode(threadInfoPtr,
							(struct freeObjNode **)(&(metadataPtr->freeListPtr)));
			//DEBUG_PRINTF("USE FREE NODE\n");
			//DEBUG_PRINTF("REALLOC POINTER: %p\n", mallocPtr);
			//Print_SubHeap_Layout(mallocPtr & (uint64_t)SUBHEAP_MASK);
			goto copy_data;
		}

	/* Since the free list does not exist, we allocate the space directly */
		mallocPtr = metadataPtr->nextObjPtr;
		uint64_t supersetSize = (uint64_t)1 << minSizeExp;
		metadataPtr->nextObjPtr += supersetSize;

	/* We have to check if the next object pointer becomes page aligned because
	 * every other page for small allocations is a guard page. This check is
	 * mainly for small allocations less than a page big.
	 */
		if((metadataPtr->nextObjPtr) & (~(uint64_t)DEFAULT_PAGE_MASK)) {
			//DEBUG_PRINTF("--MALLOC POINTER: %p\n", mallocPtr);
			//Print_SubHeap_Layout(mallocPtr & (uint64_t)SUBHEAP_MASK);
			goto copy_data;
		}

	/* Skip the guard page*/
		uint64_t realSubHeapAddr = (metadataPtr->nextObjPtr) & (uint64_t)SUBHEAP_MASK;

	#ifndef DO_NOT_GUARD_PAGES
		metadataPtr->nextObjPtr += (uint64_t)DEFAULT_PAGE_SIZE;
	#endif

	/* Now we have to check if the pointer is pointing to the next subHeap
	 * i.e. this object's subHeap is full (since the next object pointer is
	 * page aligned.
	 */
		int64_t leftoverSize = realSubHeapAddr + (uint64_t)SUBHEAP_SIZE -
								(metadataPtr->nextObjPtr) - (uint64_t)DEFAULT_PAGE_SIZE;
		if(leftoverSize < supersetSize) {
		/* Allocate a new heap. But we need to check if we need tp map a new bag */
			uint64_t realBagAddr = (metadataPtr->nextObjPtr) & (uint64_t)HEAP_BAG_MASK;

		/* Check if the end of the bag has been hit */
			if(metadataPtr->nextObjPtr == realBagAddr)
				realBagAddr -= (uint64_t)HEAP_BAG_SIZE;

		/* Check if the last subheap is full */
			if(realSubHeapAddr + (uint64_t)HEAP_SIZE
					> realBagAddr + (uint64_t)HEAP_BAG_SIZE) {
			/* Map a new bag */
				//DEBUG_PRINTF("size: %d\n", objSize);
				uint64_t bagPtr = AllocateNewBag(threadInfoPtr, (uint64_t)HEAP_BAG_SIZE,
																		(int8_t)SMALL_HEAP_BAG);
				metadataPtr->nextObjPtr = bagPtr + (subHeapIndex << (uint64_t)SUBHEAP_SHIFT);
			} else {
			/* Use the next adjacent heap */
				metadataPtr->nextObjPtr = realSubHeapAddr + (uint64_t)HEAP_SIZE;
			}
		}

	#ifdef DEBUG
		DEBUG_PRINTF("MALLOC POINTER: %p\n", mallocPtr);
		Print_SubHeap_Layout(realSubHeapAddr);
	#endif
		goto copy_data;
	}

/* Realloc for larger heaps */
	if(objSize <= (uint64_t)LARGEST_PREALLOCATED_SIZE) {
		//DEBUG_PRINTF("LARGE OBJ SIZE\n");
	/* Get the subheap of the heap. Here the size is going to be less than 4Gb
	 * anyways so we cast the size to get the number of bites following the most
	 * significant 1-bit.
	 */
		uint64_t minSizeExp = 31 - (uint64_t)__builtin_clz((uint32_t)objSize);
		uint64_t subHeapIndex = minSizeExp - (uint64_t)MIN_LARGE_OBJ_SHIFT;

	/* If the object size is not aligned well with the standard sizes, then go to
	 * the next subheap.
	 */
		if(((uint64_t)1 << minSizeExp) < objSize) {
			minSizeExp++;
			subHeapIndex++;
		}
		//DEBUG_PRINTF("REALLOC: minSizeExp: %d\n", minSizeExp);
		//DEBUG_PRINTF("REALLOC: subHeapIndex: %d\n", subHeapIndex);

	/* Compute the real object size */
		givenSupersetSize = (uint64_t)1 << minSizeExp;
		//DEBUG_PRINTF("GIVEN SUPERSET SIZE: %p %d\n", givenSupersetSize, givenSupersetSize);

	/* Now, we need to see how the sizes compare */
		if(givenSupersetSize == heapObjSize) {
			//DEBUG_PRINTF("LARGE HEAP MATCH\n");
		#ifdef DEBUG
			state = (int8_t)DONE;
		#endif
			//DEBUG_PRINTF("REALLOC PTR: %p\n", heapObjPtr);
			return heapObjPtr;
		}

	/* Now, this means the sizes differ and we need to allocate a separate object */
		uint64_t subHeapAddr =
				(threadInfoPtr->primaryHeap[1]) + (subHeapIndex << (uint64_t)LARGE_SUBHEAP_SHIFT);
		//DEBUG_PRINTF("REALLOC: subheapAddr: %p\n", subHeapAddr);
		struct shadowMetadata *metadataPtr =
				(struct shadowMetadata *)((subHeapAddr >> (uint64_t)LARGE_SHADOW_MAP_SCALE)
															+ (threadInfoPtr->shadowOffset[1]));
		//DEBUG_PRINTF("MALLOC: matadataPtr: %p\n", metadataPtr);
		//DEBUG_PRINTF("MALLOC: shadow offset: %p\n", threadInfoPtr->shadowOffset[1]);

	/* Check if the free list exists */
		if(metadataPtr->freeListPtr) {
			mallocPtr = RemoveFreeNode(threadInfoPtr,
											(struct freeObjNode **)(&(metadataPtr->freeListPtr)));
			//DEBUG_PRINTF("FROM FREELIST\n");
			//DEBUG_PRINTF("REALLOC POINTER: %p\n", mallocPtr);
			//Print_SubHeap_Layout(mallocPtr & (uint64_t)LARGE_SUBHEAP_MASK);
			goto copy_data;
		}
		//DEBUG_PRINTF("LAYOUT BEFORE ALLOCATION\n");
		//Print_SubHeap_Layout(realSubHeapAddr);

	/* Since the free list does not exist, we allocate the space directly */
		mallocPtr = metadataPtr->nextObjPtr;
		//DEBUG_PRINTF("MALLOC: matadataPtr->nextObjPtr: %p\n", metadataPtr->nextObjPtr);
		//DEBUG_PRINTF("MALLOCPTR: %p\n", mallocPtr);
		uint64_t supersetSize = (uint64_t)1 << minSizeExp;
		metadataPtr->nextObjPtr += supersetSize;

	/* Skip the guard page*/
		uint64_t realSubHeapAddr = (metadataPtr->nextObjPtr) & (uint64_t)LARGE_SUBHEAP_MASK;

	#ifndef DO_NOT_GUARD_PAGES
		metadataPtr->nextObjPtr += (uint64_t)DEFAULT_PAGE_SIZE;
	#endif

	/* Now we have to check if the pointer is pointing to the next subHeap
	 * i.e. this object's subHeap is full (since the next object pointer is
	 * page aligned.
	 */
		int64_t leftoverSize = realSubHeapAddr + (uint64_t)LARGE_SUBHEAP_SIZE -
								(metadataPtr->nextObjPtr) - (uint64_t)DEFAULT_PAGE_SIZE;
		if(leftoverSize < supersetSize) {
		/* Allocate a new heap. But we need to check if we need tp map a new bag */
			uint64_t realBagAddr = (metadataPtr->nextObjPtr) & (uint64_t)HEAP_BAG_MASK;

		/* Check if the end of the bag has been hit */
			if(metadataPtr->nextObjPtr == realBagAddr)
				realBagAddr -= (uint64_t)HEAP_BAG_SIZE;

		/* Check if the last subheap is full */
			if(realSubHeapAddr + (uint64_t)LARGE_HEAP_SIZE
							> realBagAddr + (uint64_t)HEAP_BAG_SIZE) {
			/* Map a new bag */
				uint64_t bagPtr = AllocateNewBag(threadInfoPtr, (uint64_t)HEAP_BAG_SIZE,
																		(int8_t)LARGE_HEAP_BAG);
				metadataPtr->nextObjPtr = bagPtr + (subHeapIndex << (uint64_t)LARGE_SUBHEAP_SHIFT);
			} else {
			/* Use the next adjacent heap */
				metadataPtr->nextObjPtr = realSubHeapAddr + (uint64_t)LARGE_HEAP_SIZE;
			}
		}
	#ifdef DEBUG
		DEBUG_PRINTF("-REALLOC POINTER: %p\n", mallocPtr);
		Print_SubHeap_Layout(realSubHeapAddr);
	#endif
		goto copy_data;
	}

	//DEBUG_PRINTF("REALLOC: BIG BLOCK\n");
/* This means that the object size is that of a big block */
	givenSupersetSize = objSize;
	if(givenSupersetSize & (uint64_t)HEAP_BAG_SIZE_MASK) {
		givenSupersetSize =
			(givenSupersetSize & (uint64_t)HEAP_BAG_ALIGN_MASK) + (uint64_t)HEAP_BAG_SIZE;
	}

/* Now, we need to see how the sizes compare */
	if(givenSupersetSize == heapObjSize) {
	#ifdef DEBUG
		DEBUG_PRINTF("BIG BLOCK MATCH\n");
		state = (int8_t)DONE;
	#endif
		return heapObjPtr;
	}

/* This bit of code should rarely be executed */
	mallocPtr = (uint64_t)Map_HeapBag(objSize);

/* This means that the allocation size is huge */
	uint64_t index = (mallocPtr & (uint64_t)HASH_TABLE_KEY_MASK) >> (uint64_t)HASH_TABLE_SHIFT;
	*((threadInfoPtr->heapBagType_hashPtr) + index) = (int8_t)BIG_BLOCK;
	//DEBUG_PRINTF("threadInfoPtr: %p\n", threadInfoPtr);
	//DEBUG_PRINTF("threadInfoPtr->heapBagType_hashPtr: %p\n", threadInfoPtr->heapBagType_hashPtr);

#ifdef DEBUG
	DEBUG_PRINTF("REALLOC POINTER: %p\n", mallocPtr);
	Print_SubHeap_Layout(mallocPtr);
#endif

copy_data:
/* Now, we copy the heap object data to the newly allocated one */
	if(givenSupersetSize > heapObjSize)
		mallocPtr = __Safe_Memcpy((void *)mallocPtr, heapObjPtr, heapObjSize);
	else
		mallocPtr = __Safe_Memcpy((void *)mallocPtr, heapObjPtr, givenSupersetSize);

	//DEBUG_PRINTF("OBJECT DATA COPIED\n");

/* Add the given pointer to the free list */
	if(heapObjSize <= (uint64_t)MAX_SMALL_OBJ_SIZE) {
	/* Get the subheap of the heap. Here the size is going to be less than 4Gb
	 * anyways so we cast the size to get the number of bytes following the most
	 * significant 1-bit.
	 */
		uint64_t minSizeExp = 31 - (uint64_t)__builtin_clz((uint32_t)heapObjSize);
		int64_t subHeapIndex = minSizeExp - (uint64_t)MIN_OBJ_SHIFT;

	/* If the object size is not aligned well with the standard sizes, then go to
	 * the next subheap.
	 */
		if(subHeapIndex < 0) {
			subHeapIndex = 0;
			minSizeExp = MIN_OBJ_SHIFT;
		} else {
			if(((uint64_t)1 << minSizeExp) < heapObjSize) {
				minSizeExp++;
				subHeapIndex++;
			}
		}
		uint64_t subHeapAddr =
				(threadInfoPtr->primaryHeap[0]) + (subHeapIndex << (uint64_t)SUBHEAP_SHIFT);
		//DEBUG_PRINTF("HEAP OBJ: subheapAddr: %p\n", subHeapAddr);

	/* Get the metadata */
		struct shadowMetadata *metadataPtr =
				(struct shadowMetadata *)((subHeapAddr >> (uint64_t)SHADOW_MAP_SCALE)
														+ (threadInfoPtr->shadowOffset[0]));

	/* Add the object to the free list */
		AddFreeNode(threadInfoPtr, (struct freeObjNode **)&(metadataPtr->freeListPtr),
																			(uint64_t)heapObjPtr);
	#ifdef DEBUG
		DEBUG_PRINTF("GIVEN HEAP OBJECT FREED\n");
		state = (int8_t)DONE;
	#endif
		return (void *)mallocPtr;
	}

/* This means we have to free an object from a large heap */
	if(heapObjSize <= (uint64_t)LARGEST_PREALLOCATED_SIZE) {
		//DEBUG_PRINTF("LARGE OBJ SIZE\n");
	/* Get the subheap of the heap. Here the size is going to be less than 4Gb
	 * anyways so we cast the size to get the number of bites following the most
	 * significant 1-bit.
	 */
		uint64_t minSizeExp = 31 - (uint64_t)__builtin_clz((uint32_t)heapObjSize);
		uint64_t subHeapIndex = minSizeExp - (uint64_t)MIN_LARGE_OBJ_SHIFT;

	/* If the object size is not aligned well with the standard sizes, then go to
	 * the next subheap.
	 */
		if(((uint64_t)1 << minSizeExp) < heapObjSize) {
			minSizeExp++;
			subHeapIndex++;
		}
		//DEBUG_PRINTF("HEAPOBJPTR: minSizeExp: %d\n", minSizeExp);
		//DEBUG_PRINTF("HEAPOBJPTR: subHeapIndex: %d\n", subHeapIndex);

	/* Now, this means the sizes differ and we need to allocate a separate object */
		uint64_t subHeapAddr =
				(threadInfoPtr->primaryHeap[1]) + (subHeapIndex << (uint64_t)LARGE_SUBHEAP_SHIFT);
		//DEBUG_PRINTF("REALLOC: subheapAddr: %p\n", subHeapAddr);
		struct shadowMetadata *metadataPtr =
				(struct shadowMetadata *)((subHeapAddr >> (uint64_t)LARGE_SHADOW_MAP_SCALE)
															+ (threadInfoPtr->shadowOffset[1]));

	/* Add the object to the free list */
		AddFreeNode(threadInfoPtr, (struct freeObjNode **)&(metadataPtr->freeListPtr),
																			(uint64_t)heapObjPtr);
	#ifdef DEBUG
		DEBUG_PRINTF("GIVEN HEAP OBJECT FREED\n");
		state = (int8_t)DONE;
	#endif
		return (void *)mallocPtr;
	}

	//DEBUG_PRINTF("BIG BLOCK TO BE FREED\n");
/* Free the old big block */
	HeapMunmap((uint64_t)heapObjPtr, heapObjSize);

/* Update the hash table */
	uint64_t realBagAddr = (uint64_t)heapObjPtr & (uint64_t)HEAP_BAG_MASK;
	uint64_t hashIndex =
		((uint64_t)realBagAddr & (uint64_t)HASH_TABLE_KEY_MASK) >> (uint64_t)HASH_TABLE_SHIFT;
	*((threadInfoPtr->heapBagType_hashPtr) + hashIndex) = 0;
	//DEBUG_PRINTF("threadInfoPtr: %p\n", threadInfoPtr);
	//DEBUG_PRINTF("threadInfoPtr->heapBagType_hashPtr: %p\n", threadInfoPtr->heapBagType_hashPtr);
#ifdef DEBUG
	DEBUG_PRINTF("GIVEN HEAP OBJECT FREED\n");
	state = (int8_t)DONE;
#endif
	return (void *)mallocPtr;
}

#ifdef WRAP_MALLOC
inline void *malloc(uint64_t objSize)
{
	return Heap_malloc(objSize);
}
#endif

#ifdef WRAP_FREE
inline void free(void *heapObjPtr)
{
	return Heap_free(heapObjPtr);
}
#endif

#ifdef WRAP_CALLOC
void *calloc(size_t numObj, size_t objSize)
{
	return Heap_calloc(numObj, objSize);
}
#endif

#ifdef WRAP_REALLOC
void *realloc(void *ptr, size_t size)
{
	return Heap_realloc(ptr, size);
}
#endif


/*********************************** FUNCTION WRAPPERS ***********************************/

/* Just in case programmer wants to use a different 'mmap' and/or 'munmap', they can */
#ifdef REDEFINE_HEAP_MMAP
void Redefine_Heap_Mmap(void *(*new_mmap)(void *, size_t, int, int, int, off_t))
{
	heap_mmap = new_mmap;
}
#endif

#ifdef REDEFINE_HEAP_MUNMAP
void Redefine_Heap_Munmap(int (*new_munmap)(void *, size_t))
{
	heap_munmap = new_munmap;
}
#endif

#ifdef REDEFINE_HEAP_MPROTECT
void Redefine_Heap_Mprotect(int (*new_mprotect)(void *, size_t, int))
{
	heap_mprotect = new_mprotect;
}
#endif

#ifdef REDEFINE_HEAP_SHADOW_MMAP
void Redefine_Heap_Shadow_Mmap(void *(*new_mmap)(void *, size_t, int, int, int, off_t))
{
	heap_shadow_mmap = new_mmap;
}
#endif

#ifdef REDEFINE_HEAP_SHADOW_MUNMAP
void Redefine_Heap_Shadow_Munmap(int (*new_munmap)(void *, size_t))
{
	heap_shadow_munmap = new_munmap;
}
#endif

#ifdef REDEFINE_HEAP_SHADOW_MPROTECT
void Redefine_Heap_Shadow_Mprotect(int (*new_mprotect)(void *, size_t, int))
{
	heap_shadow_mprotect = new_mprotect;
}
#endif

/* API used by the heap allocator, given the programmer preferences */
inline void *HeapMmap(uint64_t addr, uint64_t length, int prot, int flags, int fd, off_t offset)
{
#ifdef REDEFINE_HEAP_MMAP
	return heap_mmap((void *)addr, (size_t)length, prot, flags, fd, offset);
#else
	return mmap((void *)addr, (size_t)length, prot, flags, fd, offset);
#endif
}

inline int HeapMunmap(uint64_t addr, uint64_t length)
{
#ifdef REDEFINE_HEAP_MUNMAP
	return heap_munmap((void *)addr, (size_t)length);
#else
	return munmap((void *)addr, (size_t)length);
#endif
}

inline int HeapMprotect(uint64_t addr, uint64_t length, int prot)
{
#ifdef REDEFINE_HEAP_MPROTECT
	return heap_mprotect((void *)addr, (size_t)length, prot);
#else
	return mprotect((void *)addr, (size_t)length, prot);
#endif
}

inline void *ShadowHeapMmap(uint64_t addr, uint64_t length, int prot, int flags, int fd, off_t offset)
{
#ifdef REDEFINE_HEAP_SHADOW_MMAP
	return heap_shadow_mmap((void *)addr, (size_t)length, prot, flags, fd, offset);
#else
	return mmap((void *)addr, (size_t)length, prot, flags, fd, offset);
#endif
}

inline int ShadowHeapMunmap(uint64_t addr, uint64_t length)
{
#ifdef REDEFINE_HEAP_SHADOW_MUNMAP
	return heap_shadow_munmap((void *)addr, (size_t)length);
#else
	return munmap((void *)addr, (size_t)length);
#endif
}

inline int ShadowHeapMprotect(uint64_t addr, uint64_t length, int prot)
{
#ifdef REDEFINE_HEAP_SHADOW_MPROTECT
	return heap_shadow_mprotect((void *)addr, (size_t)length, prot);
#else
	return mprotect((void *)addr, (size_t)length, prot);
#endif
}


/********************************** ERROR HANDLING ***************************************/

/* We use this function to emulate assert() in the C library. We have to handle exceptions based on
 * conditions ourselves since all the other functions use heap and functions assert().
 */
inline void __Safe_Assert(bool condition, char *errorMessage)
{
/* If the condition is false, we handle the error, or else we're done */
	if(!condition)
		__Error(errorMessage);
}

/* This is just to print the error message to the console and abort */
inline void __Error(char *errorMessage)
{
/* Print the error message */
	DEBUG_PRINTF(errorMessage);

	Print_Process_Layout();

/* Now, we raise SIGABRT signal to the application */
	raise(SIGABRT);
}

inline int8_t __Warn(bool condition, char *errorMessage)
{
/* If the condition is false, we handle the error, or else we warn */
	if(!condition) {
		DEBUG_PRINTF(errorMessage);
		return 1;
	}
	return 0;
}


/*********************************** DEBUGGING FUNCTIONS ***********************************/

void Print_Process_Layout(void)
{
	char command[1024] = {0};
	__Safe_Sprintf(command, 1024, "cat /proc/%d/maps", getpid());
	system(command);
}

void PrintHeapType(struct perThreadInfo *threadInfoPtr, uint64_t bagPtr)
{
	uint64_t hashIndex =
			((uint64_t)bagPtr & (uint64_t)HASH_TABLE_KEY_MASK) >> (uint64_t)HASH_TABLE_SHIFT;
	int8_t heapBagType = *((threadInfoPtr->heapBagType_hashPtr) + hashIndex);

	if(heapBagType == (int8_t)SMALL_HEAP_BAG) {
		DEBUG_PRINTF("HeapBagType for bag: %p is SMALL_HEAP_BAG\n", bagPtr);
		return;
	}
	if(heapBagType == (int8_t)LARGE_HEAP_BAG) {
		DEBUG_PRINTF("HeapBagType for bag: %p is LARGE_HEAP_BAG\n", bagPtr);
		return;
	}
	if(heapBagType == (int8_t)BIG_BLOCK) {
		DEBUG_PRINTF("HeapBagType for bag: %p is BIG_BLOCK\n", bagPtr);
		return;
	}
	if(heapBagType == 0) {
		DEBUG_PRINTF("HeapBagType for bag: %p is NONE/EMPTY\n", bagPtr);
		return;
	}
	DEBUG_PRINTF("HeapBagType for bag: %p is UNKNOWN\n", bagPtr);
}

void Identify_HeapBagType(int8_t heapBagType)
{
	if(heapBagType == (int8_t)SMALL_HEAP_BAG) {
		DEBUG_PRINTF("HeapBagType is SMALL_HEAP_BAG\n");
		return;
	}
	if(heapBagType == (int8_t)LARGE_HEAP_BAG) {
		DEBUG_PRINTF("HeapBagType is LARGE_HEAP_BAG\n");
		return;
	}
	if(heapBagType == (int8_t)BIG_BLOCK) {
		DEBUG_PRINTF("HeapBagType is BIG_BLOCK\n");
		return;
	}
	if(heapBagType == 0) {
		DEBUG_PRINTF("HeapBagType is EMPTY\n");
		return;
	}
	DEBUG_PRINTF("HeapBagType is UNKNOWN\n");
}

#ifdef CATCH_PAGE_FAULTS
void Handle_PageFault(int sigNum)
{
#ifdef INSTRUMENT_LOADS_AND_STORES
	if(lastStoreAddr == (uint64_t)NO_FAULT) {
		DEBUG_PRINTF("LAST LOAD ADDR: %p\n", lastLoadAddr);
		Print_Process_Layout();
		DEBUG_PRINTF("LAST LOAD ADDR: %p\n", lastLoadAddr);
		ReadProcMapsFile_PrintAddrDiff(lastLoadAddr - (uint64_t)DEFAULT_PAGE_SIZE,
										lastLoadAddr + (uint64_t)DEFAULT_PAGE_SIZE);
	} else {
		if(lastLoadAddr == (uint64_t)NO_FAULT) {
			DEBUG_PRINTF("LAST STORE ADDR: %p\n", lastStoreAddr);
			Print_Process_Layout();
			DEBUG_PRINTF("LAST STORE ADDR: %p\n", lastStoreAddr);
			ReadProcMapsFile_PrintAddrDiff(lastStoreAddr + (uint64_t)DEFAULT_PAGE_SIZE,
											lastStoreAddr - (uint64_t)DEFAULT_PAGE_SIZE);
		}
#endif
	#ifdef DEBUG
		else {
			if(state != (int8_t)DONE) {
				if(state = (int8_t)MALLOC_USED) {
					DEBUG_PRINTF("ERROR IN MALLOC\n");
				} else {
					if(state = (int8_t)FREE_USED)
						DEBUG_PRINTF("ERROR IN MALLOC\n");
					else
						DEBUG_PRINTF("REASON FOR PAGE FAULT UNKNOWN\n");
				}
			} else {
				DEBUG_PRINTF("NOT AN ERROR IN HEAPGUARD LIB\n");
			}
		}
	#endif
	}

	//Print_Process_Layout();

/* Since this is a page fault generated due to the application, we emulate the signal */
	struct sigaction signal_act;
	signal_act.sa_handler = NULL;
	ASSERT(!sigemptyset(&signal_act.sa_mask), "Failed to let the kernel handle page faults.");
	signal_act.sa_flags = 0;
	ASSERT(!sigaction (SIGSEGV, &signal_act, NULL), "Failed to let the kernel handle page faults.");
	raise(SIGSEGV);
}
#endif

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
	__Safe_Sprintf(filepath, 1024, "/proc/%d/maps", getpid());

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
			uint64_t startAddr = __Safe_Strtoull_Base16(buffer, &restBuf);
			warning = WARN(startAddr  != (uint64_t)-1,
							"Warning: Failed to read start Address.\n");
			if(warning)
				return;

		/* Skip the '-' */
			uint64_t endAddr = __Safe_Strtoull_Base16(restBuf + 1, &restBuf);
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

/* These functions reduce the scope of printing the process layout which is
 * convinient for debugging.
 *  */

void Print_Heap_Layout(uint64_t heapAddr)
{
/* Make sure that the heap address and threadInfoPtr are not NULL */
#ifndef DONT_THROW_EXECEPTION_ON_ERROR
	ASSERT(heapAddr, "Error: Heap address specified for printing layout is NULL.\n");
#else
	if(WARN(heapAddr, "Warning: Heap address specified for printing layout is NULL.\n")) {
		return;
	}
#endif

	struct perThreadInfo *threadInfoPtr =
					threadInfo[(pthread_self() & (uint64_t)THREAD_INFO_NUM_ELEM) >> 12];
	uint64_t bagAddr = (uint64_t)heapAddr & (uint64_t)HEAP_BAG_MASK;
	uint64_t hashIndex =
			((uint64_t)bagAddr & (uint64_t)HASH_TABLE_KEY_MASK) >> (uint64_t)HASH_TABLE_SHIFT;
	int8_t heapBagType = *((threadInfoPtr->heapBagType_hashPtr) + hashIndex);

	if(heapBagType == (int8_t)SMALL_HEAP_BAG) {
	/* We make sure that the heap address appropriately aligned */
	#ifndef DONT_THROW_EXECEPTION_ON_ERROR
		ASSERT(!((heapAddr - bagAddr) % (uint64_t)HEAP_SIZE),
					"Error: heap address specified for printing layout is not "
					"aligned appropriately.\n");
	#else
		int8_t warning = WARN(!((heapAddr - bagAddr) % (uint64_t)HEAP_SIZE),
				"Warning: heap address specified for printing layout is not "
				"aligned appropriately.\n");
		if(warning)
			return;
	#endif
		ReadProcMapsFile_PrintAddrDiff(heapAddr, heapAddr + (uint64_t)HEAP_SIZE);
		return;
	}
	if(heapBagType == (int8_t)LARGE_HEAP_BAG) {
	/* We make sure that the heap address appropriately aligned */
	#ifndef DONT_THROW_EXECEPTION_ON_ERROR
		ASSERT(!((heapAddr - bagAddr) % (uint64_t)LARGE_HEAP_SIZE),
					"Error: heap address specified for printing layout is not "
					"aligned appropriately.\n");
	#else
		int8_t warning = WARN(!((heapAddr - bagAddr) % (uint64_t)LARGE_HEAP_SIZE),
				"Warning: heap address specified for printing layout is not "
				"aligned appropriately.\n");
		if(warning)
			return;
	#endif
		ReadProcMapsFile_PrintAddrDiff(heapAddr, heapAddr + (uint64_t)LARGE_HEAP_SIZE);
		return;
	}
	if(heapBagType == (int8_t)BIG_BLOCK) {
	/* Make sure that the the address is bag slot aligned */
	#ifndef DONT_THROW_EXECEPTION_ON_ERROR
		ASSERT(!(heapAddr & (~(uint64_t)HEAP_BAG_ALIGN_MASK)),
				"Error: Heap address specified for big block for printing layout is not "
				"aligned to bag slot.\n");
	#else
		int8_t warning = WARN(!(heapAddr & (~(uint64_t)HEAP_BAG_ALIGN_MASK)),
				"Warning: Heap address specified for big block for printing layout is not "
				"aligned to bag slot.\n");
		if(warning)
			return;
	#endif
		ReadProcMapsFile_PrintAddrDiff(heapAddr, heapAddr + (uint64_t)HEAP_BAG_SIZE);
		return;
	}

#ifndef DONT_THROW_EXECEPTION_ON_ERROR
	ERROR("Error: Invalid heap type specified or heap does not exist.\n");
#else
	WARN(0, "Warning: Invalid heap type specified or heap does not exist.\n");
#endif
}

void Print_SubHeap_Layout(uint64_t subHeapAddr)
{
/* Make sure that the heap address and threadInfoPtr are not NULL */
#ifndef DONT_THROW_EXECEPTION_ON_ERROR
	ASSERT(heapAddr, "Error: Heap address specified for printing layout is NULL.\n");
#else
	if(WARN(subHeapAddr, "Warning: Heap address specified for printing layout is NULL.\n")) {
		return;
	}
#endif

	struct perThreadInfo *threadInfoPtr =
					threadInfo[(pthread_self() & (uint64_t)THREAD_INFO_NUM_ELEM) >> 12];
	uint64_t bagAddr = (uint64_t)subHeapAddr & (uint64_t)HEAP_BAG_MASK;
	uint64_t hashIndex =
			((uint64_t)bagAddr & (uint64_t)HASH_TABLE_KEY_MASK) >> (uint64_t)HASH_TABLE_SHIFT;
	int8_t heapBagType = *((threadInfoPtr->heapBagType_hashPtr) + hashIndex);

	if(heapBagType == (int8_t)SMALL_HEAP_BAG) {
	/* We make sure that the heap address appropriately aligned */
	#ifndef DONT_THROW_EXECEPTION_ON_ERROR
		ASSERT(!(subHeapAddr & (~(uint64_t)SUBHEAP_MASK)),
					"Error: heap address specified for printing layout is not "
					"aligned appropriately.\n");
	#else
		int8_t warning = WARN(!(subHeapAddr & (~(uint64_t)SUBHEAP_MASK)),
				"Warning: heap address specified for printing layout is not"
				"aligned appropriately.\n");
		if(warning)
			return;
	#endif
		ReadProcMapsFile_PrintAddrDiff(subHeapAddr, subHeapAddr + (uint64_t)SUBHEAP_SIZE);
		return;
	}
	if(heapBagType == (int8_t)LARGE_HEAP_BAG) {
	/* We make sure that the heap address appropriately aligned */
	#ifndef DONT_THROW_EXECEPTION_ON_ERROR
		ASSERT(!(subHeapAddr & (~(uint64_t)LARGE_SUBHEAP_MASK)),
					"Error: heap address specified for printing layout is not "
					"aligned appropriately.\n");
	#else
		int8_t warning = WARN(!(subHeapAddr & (~(uint64_t)LARGE_SUBHEAP_MASK)),
				"Warning: heap address specified for printing layout is not "
				"aligned appropriately.\n");
		if(warning)
			return;
	#endif
		ReadProcMapsFile_PrintAddrDiff(subHeapAddr, subHeapAddr + (uint64_t)LARGE_SUBHEAP_SIZE);
		return;
	}
	if(heapBagType == (int8_t)BIG_BLOCK) {
	/* Make sure that the the address is bag slot aligned */
	#ifndef DONT_THROW_EXECEPTION_ON_ERROR
		ASSERT(!(subHeapAddr & (~(uint64_t)HEAP_BAG_ALIGN_MASK)),
				"Error: Heap address specified for big block for printing layout is not "
				"aligned to bag slot.\n");
	#else
		int8_t warning = WARN(!(subHeapAddr & (~(uint64_t)HEAP_BAG_ALIGN_MASK)),
				"Warning: Heap address specified for big block for printing layout is not"
				"aligned to bag slot.\n");
		if(warning)
			return;
	#endif
		ReadProcMapsFile_PrintAddrDiff(subHeapAddr, subHeapAddr + (uint64_t)HEAP_BAG_SIZE);
		return;
	}

#ifndef DONT_THROW_EXECEPTION_ON_ERROR
	ERROR("Error: Invalid heap type specified or heap does not exist.\n");
#else
	WARN(0, "Warning: Invalid heap type specified or heap does not exist.\n");
#endif
}

int8_t RegionisEmpty(uint64_t addr, uint64_t size)
{
/* We iterate through the heap bag and see if there is any non-zero value */
	uint64_t *ptr = (uint64_t *)addr;
	uint64_t elemSize = size >> 3;
	while(elemSize--)  {
		if(*ptr)
			return 0;
		ptr++;
	}
	return 1;
}

#ifdef INSTRUMENT_LOADS_AND_STORES
void TrackLoads(uint64_t loadAddr)
{
	lastStoreAddr = (uint64_t)NO_FAULT;
	lastLoadAddr = loadAddr;
	//DEBUG_PRINTF(">>>>>>LAST LOAD ADDR: %p\n", lastLoadAddr);
}

void TrackStores(uint64_t storeAddr)
{
	lastLoadAddr = (uint64_t)NO_FAULT;
	lastStoreAddr = storeAddr;
	//DEBUG_PRINTF(">>>>>>LAST STORE ADDR: %p\n", lastStoreAddr);
}
#endif


/********************************************************************************************/



