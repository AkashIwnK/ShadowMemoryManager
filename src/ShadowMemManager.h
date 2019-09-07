/********** Shadow memory manager Header ********/

#ifndef SHADOW_MAP_MANAGER_HEADER_H_
#define SHADOW_MAP_MANAGER_HEADER_H_

#define MAX_VIRTUAL_ADDR       ~((uint64_t)(~0) << 47)
#define EMPTY_SLOT_OFFSET      (uint64_t)1 << 50
#define RESERVED_SLOT_OFFSET   (uint64_t)1 << 51
#define SHADOW_SLOT_OFFSET     (uint64_t)1 << 52
#define BLOCK_SLOT_OFFSET      (uint64_t)1 << 55
#define MAX_VALID_OFFSET       ~((uint64_t)(~0) << 47)
#define SCRATCH_UNIT_OFFSET    MAX_VALID_OFFSET
#define RET_INVALID_OFFSET     MAX_VALID_OFFSET
#define NULL_NUM_SUB_REG        0
#define SCRATCH_IN_APP_REG		1
#define SCRATCH_OUT_APP_REG		2	
#define SCRATCH_IRRELEVANT		3

#define SHADOW_INITIALIZED      4
#define SHADOW_INITIALIZING		5
#define SHADOW_UNINITIALIZED	6

#define EXEC_NOT_FOUND          8
#define EXEC_FOUND              9
#define DATA_SEGMENT_FOUND 		10
#define OBJ_FILE_SEG_ANALYSED	11

#define NO_MAPPING_USED          0
#define FIXED_MAPPING_USED      -5
#define MALLOC_MAPPING_USED 	-1
#define CALLOC_MAPPING_USED     -2
#define MMAP_MAPPING_USED       -3

#define APP_MAPPING_FAILED       (uint64_t)1 << 57

#ifndef BLOCK_HEAP
#define MAIN_HEAP_USED          -4
#endif

#define OFFSET_CONFLICT         -6
#define CONFLICT_RESOLVED       -7
#define SAVE_INVALID_OFFSETS    -8

/* These are the actions */
#define SHADOW_MAP              -9
#define APP_MAP                 -10

/******************************* SCRATCH SPACE STRUCTURES **************************/

/* Structures that store information about specific memory units */
struct stack {
	uint64_t stackBase;
	uint64_t stackSoftLimit;
	uint64_t stackHardLimit;
	bool finite_stackSoftLimitSet; /* track whether application explicitly set the stack limit */
};

/* It may seem that this struct is big but it stores vital info so its worth it */
struct heap {
	uint64_t heapBase;   			/* starting address of heap */
	uint64_t heapSoftLimit;         /* Heap soft limit used by the shadow memory library */
	uint64_t heapHardLimit;			/* Heap hard limit used by the shadow memory library */
	uint64_t alloc_chunkInfo_size;
	uint64_t padded_chunkInfo_size;
};

/* We need to map shadow for the executable so we need to save some information about the executable */
struct objInfo {
/* Info about the executable */
	uint64_t execBegAddr;
	uint64_t execSize;

/* Info on data segment */
	uint64_t dataSegBegAddr;
	uint64_t dataSegSize;

/* Info on BSS segment */
	uint64_t bssSegBegAddr;
	uint64_t bssSegSize;
};

struct tableEntry_struct {
	uint64_t entry1;
	uint64_t entry2;
};

struct scratchSpaceInfo {
/* Information about scratch space */
	uint64_t scratchSpaceAddr;
	uint64_t scratchSpaceSize;
	uint64_t scratchSlotsBegAddr;
	uint64_t numScratchSlots;

/* Store information about different buffers */
	uint64_t printfPtr;
	uint64_t printfBufferSize;
	uint64_t mallocPtr;
	uint64_t mallocBufferSize;

/* Information about a table */
	struct tableEntry_struct *tablePtr;
	uint64_t tableBufferSize;
};

/* Storing some system won't hurt */
struct sysPageInfo {
	uint64_t pageSize;
	uint64_t pageShift;
	uint64_t pageMask;  /* Used to get page aligned addresses */
};

/* Node structures used for the lists that constitute the scratch space 
 * for the shadow map manager.
*/ 
struct validOffset_struct {
	int64_t validOffset;
	uint64_t numRegSameOffset;
	struct validOffset_struct *nextNodePtr;
};

struct appShadowAddrsNode {
	uint64_t appUnitAddr;
	uint64_t shadowUnitAddr;
	struct appShadowAddrsNode *nextNodePtr;
};

/* Unit struct for arrays in the invalid offsets hash tables */
struct invalidOffset_struct {
	int64_t invalidOffset;
	uint64_t numSubUnits;
};

/* Units for the memory layout table to indicate the type of unit i.e. each table unit
* representing each virtual unit/slot of the user address space. 
*/
struct unitInfo {
	int64_t offset; 
	uint64_t numReg;
};

struct blockSlotAddrNode {
	uint64_t blockedSlotAddr;
	struct blockSlotAddrNode *nextNodePtr;
};

struct appMappingInfo {
	int8_t mapping_type;
	uint64_t intended_addr;
	uint64_t mmapped_addr;
	uint64_t size;
	int prot;
	int flags;
	int fd;
	off_t offset;
};

/* This struct is meant to store information about the slots beginning address and number of slots that
 * enclose a particular application region */
struct regSlotsInfo {
	uint64_t regSlotsBegAddr;
	uint64_t numRegSlots;
};

/******************************** MANAGER CONSTRUCTOR ************************************/

/* Functions for initialization of the shadow map manager: maps scratch space, reserved
* and shadow units for the stack and heap.
*/
void Init_ShadowMapManager(void);
void Adjust_HeapSoftLimit(void);
void MapScratchSpace(void);
void Mmap_Temp_Malloc_Buffer(void);
void Fill_Gaps_in_ObjectFile_SegmentSlots(void);
void Init_Stack_Mappings(void);
void Init_Heap_Mappings(void);
void Init_Mapped_Libraries(void);
void InitScratchSpaceInfo(void);
void StoreSysPageInfo(void);
void Get_Heap_Limits(void);
void BlockHeap(void);
void InitMemLayoutTable(void);
void Init_ObjSegs_Mappings(void);
void Init_Exec_Mappings(void);
void Init_Data_Seg_Mappings(void);
void Init_BSS_Seg_Mappings(void);
void Get_RegSlotsInfo(uint64_t, uint64_t, struct regSlotsInfo *);
uint64_t RoundUpSize_to_PageSizeMultiple(uint64_t size);


/************************************* ALLOCATOR ************************************/

/**** Functions used to map shadows and reserved units ****/
void MapAppRegion(uint64_t, uint64_t);

/* Functions listed according to the memory layout they manage */
/* 1 */ void Manage_EA_MemLayout(uint64_t, uint64_t);
	/*1.a.*/ void Manage_App_EA__DifferentOffsetsCase(uint64_t, uint64_t);
	/*1.b.*/ void Manage_Scratch_EA__Case(uint64_t, uint64_t);
	/*1.c.*/ void Manage_App_ES__Case(uint64_t, uint64_t);
	/*1.d.*/ void Manage_App_EA__SameOffsetsCase(uint64_t, uint64_t);
	/*1.e.*/ void Manage_Empty_EA__Case(uint64_t, uint64_t);
	/*1.f.*/ void Manage_Empty_ES__Case(uint64_t, uint64_t);

/* 2 */ void Manage_E_MemLayout(uint64_t, uint64_t);
	/*2.a.*/ void Manage_App_E_App_DifferentOffsetsCase(uint64_t, uint64_t);
	/*2.b.*/ void Manage_App_E_Scratch_Case(uint64_t, uint64_t);
	/*2.c.*/ void Manage_Scratch_E_App_Case(uint64_t, uint64_t);
	/*2.d.*/ void Manage_App_E_App_SameOffsetsCase(uint64_t, uint64_t);
	/*2.e.*/ void Manage_App_E_Empty_Case(uint64_t, uint64_t);
	/*2.f.*/ void Manage_Scratch_E_Empty_Case(uint64_t, uint64_t);
	/*2.g.*/ void Manage_Empty_E_App_Case(uint64_t, uint64_t);
	/*2.h.*/ void Manage_Empty_E_Scratch_Case(uint64_t, uint64_t);
	/*2.i.*/ void Manage_Empty_E_Empty_Case(uint64_t, uint64_t);

/* 3 */ void Manage_AE_MemLayout(uint64_t, uint64_t);
	/*3.a.*/ void Manage__AE_App_DifferentOffsetsCase(uint64_t, uint64_t);
	/*3.b.*/ void Manage__AE_Scratch_Case(uint64_t, uint64_t);
	/*3.c.*/ void Manage__SE_App_Case(uint64_t, uint64_t);
	/*3.d.*/ void Manage__AE_App_SameOffsetsCase(uint64_t, uint64_t);
	/*3.e.*/ void Manage__AE_Empty_Case(uint64_t, uint64_t);
	/*3.f.*/ void Manage__SE_Empty_Case(uint64_t, uint64_t);

/* 4 */ void Manage_AEA_MemLayout(uint64_t, uint64_t);
	/*4.a.*/ void Manage__AEA__DifferentOffsetsCase(uint64_t, uint64_t);
	/*4.b.*/ void Manage__AES__Case(uint64_t, uint64_t);
	/*4.c.*/ void Manage__SEA__Case(uint64_t, uint64_t);
	/*4.d.*/ void Manage__AEA__SameOffsetsCase(uint64_t, uint64_t);

/* 5 */ void Manage_A_MemLayout(uint64_t);

/* 6 */ void Manage_AA_MemLayout(uint64_t);

/* Functions used by the above allocator functions */
void Fill_EmptySpaces_in_Slots(uint64_t regSlotAddr, uint64_t numregSlots);
void Fill_EmptySpaces_in_a_Slot(uint64_t slotAddr);
void TurnTimerOff_and_RetSIGALRMControl(void);
void Reverse_Changes_on_ScratchUnits(uint64_t regSlotsBegAddr, uint64_t numRegSlots,
												uint64_t shadowOffset, int64_t prot);
void
Reverse_changes_to_AppShadowInfoList_for_Scratch(uint64_t scratchLowSlotAddr, uint64_t scratchHighSlotAddr);
void Reverse_changes_to_ValidOffsetSList_for_Scratch(uint64_t scratchLowSlotAddr,
											uint64_t scratchHighSlotAddr, int64_t shadowOffset);
int64_t RemapAppRegion(void);
int8_t Map_Shadow_for_Malloced_Region(void);
int8_t Map_Shadow_for_Mmaped_Region(void);
void *Mmap_FixedAddr_Shadow(uint64_t slotsBegAddr, uint64_t numSlots);
void *Kernel_Mmap_Shadow(uint64_t numSlots);
void Add_AppInfo_to_AppShadowInfoList(uint64_t, uint64_t);
void Add_AppInfo_to_MemLayoutTable(uint64_t, uint64_t);
uint64_t NumAppSlots_VicinityLowAppUnits(uint64_t);
uint64_t NumAppSlots_VicinityHighAppUnits(uint64_t);
void Mprotect_Scratch_Shadow(uint64_t scratchBegSlotsAddr, uint64_t scratchEndSlotsAddr,
													uint64_t shadowOffset, int64_t prot);
void Unmap_Scratch_ShadowReservedSlots(uint64_t, uint64_t, int64_t);
int64_t MmapShadowMemSlots(uint64_t, uint64_t);
int8_t AddInvalidOffsets(uint64_t, uint64_t, int8_t);
int8_t Add_UnitToUnit_2Way_InvalidOffsets(uint64_t unit1Addr, uint64_t unit2Addr, int8_t);
int8_t Add_UnitToUnit_1Way_InvalidOffset(uint64_t from_unitAddr, uint64_t to_unitAddr, int8_t);
int8_t Add_SubUnit_to_Unit_InvalidOffsets(uint64_t subUnit1Addr, uint64_t unit2Addr, int8_t);
void Remove_AppInfo_to_AppShadowInfoList(uint64_t appSlotAddr);
void Add_InvalidOffsetsTable(uint64_t*, uint64_t);
void Add_Slots_to_Stack(uint64_t, uint64_t);
void MapRegSlotReservedUnits(uint64_t, int64_t);
void MapRegReservedSlots(uint64_t, uint64_t);
void MapNewOffsetBasedReservedSlots(uint64_t, uint64_t, int64_t);
int64_t Map_Shadow_with_ValidOffsets(uint64_t, uint64_t);
int64_t Map_Shadow_with_NewOffset(uint64_t, uint64_t);
int8_t Update_ScratchDataStructures_on_NewMap(uint64_t, uint64_t, int64_t);
int64_t AttemptMapShadow(uint64_t, uint64_t, int64_t);
void Add_AppInfo_to_AppShadowInfoList(uint64_t, uint64_t);
struct validOffset_struct *Get_Available_ValidOffsetNode(void);
void Add_AppInfo_to_MemLayoutTable(uint64_t, uint64_t);
int64_t MmapShadowMemSlots(uint64_t appSlotsBegAddr, uint64_t numAppSlots);
//void Add_Slots_to_BlockSlotsList(uint64_t slotsBegAddr, uint64_t numSlots);
//void Add_BlockSlotAddr_to_BlockSlotsList(uint64_t blockedSlotAddr);
//void Remove_BlockSlotAddr_from_BlockSlotsList(uint64_t blockedSlotAddr);
//void Empty_BlockSlotsList_from_Node(struct blockSlotAddrNode *emptyBegBlockSlotsNode);
void Set_MicroTimer(uint64_t time, char *error_message);


/************************************* DEALLOCATOR ******************************/

void UnmapAppRegion(uint64_t, uint64_t);
void Subtract_InvalidOffsets(uint64_t slotBegAddr, uint64_t numSlots) ;
void Subtract_UnitToUnit_2Way_InvalidOffsets(uint64_t unit1Addr, uint64_t unit2Addr);
void Subtract_UnitToUnit_1Way_InvalidOffset(uint64_t from_unitAddr, uint64_t to_unitAddr);
void Subtract_SubUnit_to_Unit_InvalidOffsets(uint64_t subUnit1Addr, uint64_t unit2Addr);
void Check_Vicinity_for_ScatchSpace(uint64_t, uint64_t);
void MunmapShadowMemSlots(uint64_t, uint64_t);
void UnmapRegSlotReservedUnits(uint64_t, int64_t);
void FreeValidOffset_and_ReservedSlots(int64_t, uint64_t);
void Unmap_ValidOffset_Based_ReservedSlots(int64_t);
void Remove_AppInfo_from_AppShadowInfoList(uint64_t appSlotAddr);
void UnmapAppUnitMappedSlots(uint64_t);
void Check_Vicinity_for_ScatchSpace(uint64_t, uint64_t);
void UnmapShadowUnitReservedSlots(uint64_t);
void Convert_Shadow_to_Reserved(uint64_t, uint64_t);
uint64_t Unsafe_Get_ShadowData_TemCopy(uint64_t appSlotBegAddr, uint64_t numAppSlots);
uint64_t Safe_Get_ShadowData_TemCopy(uint64_t appSlotBegAddr, uint64_t numAppSlots);
void Safe_Copy_Read_Skip_ScratchShadow(uint64_t shadowData_copyPtr,
									uint64_t shadowSlotsBegAddr, uint64_t numShadowSlots);
void Unsafe_Copy_Read_Skip_ScratchShadow(uint64_t shadowData_copyPtr,
									uint64_t shadowSlotsBegAddr, uint64_t numShadowSlots);

void Unmap_ShadowData_TemCopy(uint64_t, uint64_t);
void UnmapRegUnitReservedSlots(uint64_t);
void Manage_SigAlarm_Signal(int manage_alarm_sig, char *error_message);
void Manage_SigAlarm_SignalHandling(void (*signal_handler)(int sigNum), char *error_message);




/*********************************** REALLOCATOR *************************************/

/********************************** MANAGER DESTRUCTOR *****************************/

/* This function unmaps all shadow and reserved units and the scratch space */
void CleanUp_ShadowMap_and_Resources(void);

/************************************ API ****************************************/
void *GetPtr_to_MetaData(void *appAddr) __attribute__((always_inline));
void *GetPtr_to_ConstOffset_MetaData(void *appAddr) __attribute__((always_inline));

void Write8_to_Shadow (void *appAddr,  uint8_t value);
void Write16_to_Shadow(void *appAddr, uint16_t value);
void Write32_to_Shadow(void *appAddr, uint32_t value);
void Write64_to_Shadow(void *appAddr, uint64_t value);
void Write8_to_ConstOffset_Shadow (void *appAddr,  uint8_t value);
void Write16_to_ConstOffset_Shadow(void *appAddr, uint16_t value);
void Write32_to_ConstOffset_Shadow(void *appAddr, uint32_t value);
void Write64_to_ConstOffset_Shadow(void *appAddr, uint64_t value);

uint8_t  Read8_from_Shadow(void *appAddr);
uint16_t Read16_from_Shadow(void *appAddr);
uint32_t Read32_from_Shadow(void *appAddr);
uint64_t Read64_from_Shadow(void *appAddr);
uint8_t  Read8_from_ConstOffset_Shadow(void *appAddr);
uint16_t Read16_from_ConstOffset_Shadow(void *appAddr);
uint32_t Read32_from_ConstOffset_Shadow(void *appAddr);
uint64_t Read64_from_ConstOffset_Shadow(void *appAddr);

/************************ INTERFACES FOR WRAPPED FUNCTIONS ********************/
void Real_Brk(int (**real_brk)(void *));
void Real_Sbrk(void *(**real_sbrk)(intptr_t));
void Real_Malloc(void *(**real_malloc)(size_t));
void Real_Calloc(void *(**real_calloc)(size_t, size_t));
void Real_Free(void (**real_free)(void *));
void Real_Mmap(void *(**real_mmap)(void *, size_t, int, int, int, off_t));
void Real_Munmap(int (**real_munmap)(void *, size_t));
void Real_Mprotect(int (**real_mprotect)(void *, size_t, int));
void Real_Madvise(int (**real_madvise)(void *, size_t, int));
void Real_Mincore(int (**real_mincore)(void *, size_t, unsigned char *));
void Real_Mlock(int (**real_mlock)(const void *, size_t));
void Real_Munlock(int (**real_munlock)(const void *, size_t));
void Real_Msync(int (**real_msync)(void *, size_t, int));
void Real_Getrlimit(int (**real_getrlimit)(int, struct rlimit *));
void Real_Setrlimit(int (**real_setrlimit)(int, const struct rlimit *));
void Real_Prlimit(int (**real_prlimit)(pid_t, int, const struct rlimit *, struct rlimit *));

/******************************** MANAGER TEST FUNCTIONS **************************/
void PrintValidOffsetsList(void);
void Print_ShadowOffsets_Cache(void);
void PrintAppShadowInfoList(void);
void PrintProcLayout(void);
void Print_MemLayoutTable_Offsets(void);

/********************************** ERROR HANDLER *********************************/
void __Assert(bool condition, char *errorMessage);

/********************************* STRING LIBRARY FUNCTIONS ********************************/
void *SHADOW_MEMCPY(void *dest, const void *src, uint64_t numBytes);
void *SHADOW_MEMSET_ZERO(void *memPtr, uint64_t numBytes);
char *SAFE_STRSTR(char *hay, char *needle);
void SAFE_SPRINTF(char *string, uint64_t stringSize, char *insertString, ...);
uint64_t SAFE_STRTOULL_BASE16(char *hexString, char **firstInvalidStringAddr);
void DEBUG_PRINTF(char *message, ...);

/************************************* PAGE FAULT HANDLER INTERFACE ********************************/

int Can_Handle_PageFaults(void) __attribute__((always_inline));
void Add_PageFaultHandler_to_ShadowHandler(void(*)(int, sigjmp_buf **));

/******************************* SIGNAL HANDLERS **********************************/
void Handle_PageFault(int);
void Handle_SigAlarm(int);

#endif  /* SHADOW_MAP_MANAGER_HEADER_H_ */
