/* Header for the HeapGuard */

#ifndef _HEAPGUARD_H_
#define _HEAPGUARD_H_

#include <stdbool.h>

#define HEAPGUARD_INITIALIZED 		(int8_t)(~0)
#define HEAPGUARD_UNINITIALIZED 	(int8_t)(0x1f)

/* This is the primary parameter that can control other paramters.
 * More is the value of this parameter more time it takes for
 * HeapGuard to intialize.
 */
#define HEAP_BAG_SHIFT 31

/* We use a fixed page size for performance purposes */
#define DEFAULT_PAGE_SIZE ((uint64_t)1 << 12)
#define DEFAULT_PAGE_MASK ((uint64_t)(~0) << 12)
#define DEFAULT_PAGE_SHIFT 12

#define SUBHEAP_SHIFT 20
#define LARGE_SUBHEAP_SHIFT 28
#define NUM_SUBHEAPS_SHIFT 4
#define NUM_LARGE_SUBHEAPS_SHIFT 3

#define NUM_SUBHEAPS 		((uint64_t)1 << NUM_SUBHEAPS_SHIFT)
#define NUM_LARGE_SUBHEAPS 	((uint64_t)1 << NUM_LARGE_SUBHEAPS_SHIFT)
#define HEAP_BAG_SIZE  		((uint64_t)1 << HEAP_BAG_SHIFT)
#define SUBHEAP_SIZE   		((uint64_t)1 << SUBHEAP_SHIFT)
#define LARGE_SUBHEAP_SIZE  ((uint64_t)1 << LARGE_SUBHEAP_SHIFT)
#define HEAP_SIZE      		((uint64_t)1 << (NUM_SUBHEAPS_SHIFT + SUBHEAP_SHIFT))
#define LARGE_HEAP_SIZE     ((uint64_t)1 << (NUM_LARGE_SUBHEAPS_SHIFT + LARGE_SUBHEAP_SHIFT))

#define HEAP_BAG_ALIGN_MASK		 ((uint64_t)(~0) << HEAP_BAG_SHIFT)
#define HEAP_BAG_SIZE_MASK       (~HEAP_BAG_ALIGN_MASK)
#define HEAP_ALIGN_MASK			 ((uint64_t)(~0) << HEAP_SHIFT)
#define LARGE_HEAP_ALIGN_MASK	 ((uint64_t)(~0) << LARGE_HEAP_SHIFT)
#define SUBHEAP_ALIGN_MASK 		 ((uint64_t)(~0) << SUBHEAP_SHIFT)
#define LARGE_SUBHEAP_ALIGN_MASK ((uint64_t)(~0) << LARGE_SUBHEAP_SHIFT)
#define HEAP_ALIGN_MASK			 ((uint64_t)(~0) << (NUM_SUBHEAPS_SHIFT + SUBHEAP_SHIFT))
#define LARGE_HEAP_ALIGN_MASK	 ((uint64_t)(~0) << (NUM_LARGE_SUBHEAPS_SHIFT + LARGE_SUBHEAP_SHIFT))

#define HEAP_BAG_MASK       ((uint64_t)(~0) << HEAP_BAG_SHIFT)
#define SUBHEAP_MASK 		((uint64_t)(~0) << SUBHEAP_SHIFT)
#define LARGE_SUBHEAP_MASK  ((uint64_t)(~0) << LARGE_SUBHEAP_SHIFT)
#define HEAP_MASK			((uint64_t)(~0) << (NUM_SUBHEAPS_SHIFT + SUBHEAP_SHIFT))
#define LARGE_HEAP_MASK	 	((uint64_t)(~0) << (NUM_LARGE_SUBHEAPS_SHIFT + LARGE_SUBHEAP_SHIFT))

#define NUM_HEAPS 			(HEAP_BAG_SIZE/HEAP_SIZE)
#define NUM_LARGE_HEAPS		(HEAP_BAG_SIZE/LARGE_HEAP_SIZE)

#define MIN_OBJ_SHIFT 		4
#define MIN_LARGE_OBJ_SHIFT 20

#define MIN_OBJ_SIZE 		((uint64_t)1 << MIN_OBJ_SHIFT)
#define MIN_LARGE_OBJ_SIZE 	((uint64_t)1 << MIN_LARGE_OBJ_SHIFT)
#define MAX_SMALL_OBJ_SIZE  (MIN_LARGE_OBJ_SIZE >> 1)

#define LARGEST_PREALLOCATED_SIZE ((uint64_t)1 << 27)

#define INVALID_HEAPOBJ_SIZE  (uint64_t)(~0)

#define HASH_BAG_SHIFT 			MIN_OBJ_SHIFT
#define HASH_LARGE_BAG_SHIFT	MIN_LARGE_OBJ_SHIFT

/* Heap Bag types */
#define SMALL_HEAP_BAG 	1
#define LARGE_HEAP_BAG 	2
#define BIG_BLOCK       3

/* Metadata comprises of pointer to free list and the pointer to the adjacent
 * unused heap object.
 */
#define METADATA_SIZE 16

#define SHADOW_MAP_SCALE		(SUBHEAP_SHIFT - 4)
#define LARGE_SHADOW_MAP_SCALE  (LARGE_SUBHEAP_SHIFT - 4)

#define TOTAL_METADATA_SIZE 		(NUM_SUBHEAPS * METADATA_SIZE)
#define TOTAL_LARGE_METADATA_SIZE 	(NUM_LARGE_SUBHEAPS * METADATA_SIZE)

#define SHADOW_METADATA_SIZE (TOTAL_METADATA_SIZE + TOTAL_LARGE_METADATA_SIZE)

#define BAG_SHADOW_SIZE      	HEAP_BAG_SIZE

#define MAX_NUM_THREADS			((uint64_t)1 << 20)
#define THREAD_INFO_NUM_ELEM 	((uint64_t)1 << 28) /* This should be good enough */
#define THREAD_ID_MASK			0x00000fffffff0000

#define BAG_TYPE_HASH_TABLE_SIZE ((uint64_t)1 << 47) >> ((uint64_t)HEAP_BAG_SHIFT)
#define HASH_TABLE_KEY_MASK     HEAP_BAG_ALIGN_MASK
#define HASH_TABLE_SHIFT        HEAP_BAG_SHIFT


/* This is the node struct for the list of pointers to freed objects */
struct freeObjNode {
	uint64_t objPtr;
	struct freeObjNode *nextNode;
};

/* Shadow metadata for the sub-heap */
struct shadowMetadata {
	uint64_t nextObjPtr;
	struct freeObjNode *freeListPtr;
};

/* Structure for each thread */
struct perThreadInfo {
/* Store the thread id */
	uint64_t threadId;

/* A hash table pointer to track the heap bag type for pointers as keys */
	int8_t *heapBagType_hashPtr;

/* Array of pointers to the two heaps. The very first heaps of the
 * very first bags mapped are primary heaps.
*/
	uint64_t primaryHeap[2];

/* Shadow Offsets for different primary bags */
	int64_t shadowOffset[2];

/* Pointers to free lists space */
	struct freeObjNode *freeListsEmptyNode;
	struct freeObjNode *freeListsSpace_freeList;
};


/************** INITIALIZER *************/

void Init_HeapGuard(void);// __attribute__((constructor(101)));
void Map_ThreadInfoArray(void);
void Map_ThreadInfoSpace(void);
int8_t *Map_HeapBagType_HashTable(void);
uint64_t Map_BagShadow(void);
uint64_t MapHugeBlocks(void *(*mmap_func)(void *, size_t, int, int, int, off_t), 
						int (*munmap_func)(void *, size_t), 
						int (*mprotect_func)(void *, size_t, int),
						uint64_t size);
uint64_t Map_HeapBag(uint64_t size);
void PlantGuardPages(uint64_t bagPtr, uint64_t bagSize, int8_t heapBagType);
void Initialize_BagShadow(uint64_t bagPtr, uint64_t bagSize, int64_t shadowOffset, int8_t heapBagType);
void Initialize_HeapBagType_HashTable(int8_t *hashTablePtr, uint64_t bagPtr, int8_t heapBagType);
uint64_t RoundUp_to_PageSize(uint64_t size);


/************* MANAGER FUNCTIONS *************/

void AddFreeNode(struct perThreadInfo *threadInfoPtr, struct freeObjNode **freeListPtr, uint64_t freeObjPtr);
uint64_t RemoveFreeNode(struct perThreadInfo *threadInfoPtr, struct freeObjNode **freeListPtrAddr);
uint64_t AllocateNewBag(struct perThreadInfo *threadInfoPtr, uint64_t size, int8_t heapBagType);
uint64_t Get_HeapObjSize(struct perThreadInfo *threadInfoPtr, uint64_t heapObjPtr);


/************* HEAP MANAGER API **************/

void *Heap_malloc(uint64_t objSize);
void Heap_free(void *heapObjPtr);
void *Heap_calloc(uint64_t numObj, uint64_t objSize);
void *Heap_realloc(void *heapObjPtr, uint64_t objSize);


/************* FUNTION WRAPPERS ************/

void Redefine_Heap_Mmap(void *(*new_mmap)(void *, size_t, int, int, int, off_t));
void Redefine_Heap_Shadow_Mmap(void *(*new_mmap)(void *, size_t, int, int, int, off_t));
void Redefine_Heap_Munmap(int (*new_munmap)(void *, size_t));
void Redefine_Heap_Shadow_Munmap(int (*new_munmap)(void *, size_t));
void Redefine_Heap_Mprotect(int (*new_mprotect)(void *, size_t, int));
void Redefine_Heap_Shadow_Mprotect(int (*new_mprotect)(void *, size_t, int));
void *HeapMmap(uint64_t addr, uint64_t length, int prot, int flags, int fd, off_t offset);
int HeapMunmap(uint64_t addr, uint64_t length);
int HeapMprotect(uint64_t addr, uint64_t length, int prot);
void *ShadowHeapMmap(uint64_t addr, uint64_t length, int prot, int flags, int fd, off_t offset);
int ShadowHeapMunmap(uint64_t addr, uint64_t length);
int ShadowHeapMprotect(uint64_t addr, uint64_t length, int prot);


/************* ERROR HANDLING **************/

void __Safe_Assert(bool condition, char *errorMessage);
void __Error(char *errorMessage);
int8_t __Warn(bool condition, char *errorMessage);


/************** DEBUGING FUNCTIONS *********/

void Handle_PageFault(int);
void Print_Process_Layout(void);
void PrintHeapType(struct perThreadInfo *threadInfoPtr, uint64_t bagPtr);
void Identify_HeapBagType(int8_t heapBagType);
void Extract_Protection_Info(char *stringPtr, char *protArray);
void ReadProcMapsFile_PrintAddrDiff(uint64_t range_startAddr, uint64_t range_endAddr);
void Print_Heap_Layout(uint64_t heapAddr);
void Print_SubHeap_Layout(uint64_t subHeapAddr);
int8_t RegionisEmpty(uint64_t addr, uint64_t size);
void TrackLoads(uint64_t loadAddr);
void TrackStores(uint64_t storeAddr);

#endif /* _HEAPGUARD_H_ */
