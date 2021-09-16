/*
 * mm.c - malloc using segregated list
 * KAIST
 * Tony Kim
 * 
 * In this approach, 
 * Every block has a header and a footer 
 * in which header contains reallocation information, size, and allocation info
 * and footer contains size and allocation info.
 * Free list are tagged to the segregated list.
 * Therefore all free block contains pointer to the predecessor and successor.
 * The segregated list headers are organized by 2^k size.
 * 
 */
#include <stdio.h>
#include <stdlib.h>
#include <assert.h>
#include <unistd.h>
#include <string.h>

#include "mm.h"
#include "memlib.h"

/* single word (4) or double word (8) alignment */
#define ALIGNMENT 8
/* rounds up to the nearest multiple of ALIGNMENT */
#define ALIGN(size) (((size) + (ALIGNMENT - 1)) & ~0x7)

// My additional Macros
#define WSIZE 4 // word and header/footer size (bytes)
#define DSIZE 8 // double word size (bytes)
#define INITCHUNKSIZE (1 << 6)
#define CHUNKSIZE (1 << 12) //+(1<<7)

#define LISTLIMIT 20
#define REALLOC_BUFFER (1 << 7) //이거 크기 딱히 상관없음

#define MAX(x, y) ((x) > (y) ? (x) : (y))
#define MIN(x, y) ((x) < (y) ? (x) : (y))

// Pack a size and allocated bit into a word
#define PACK(size, alloc) ((size) | (alloc))

// Read and write a word at address p
#define GET(p) (*(unsigned int *)(p))
#define PUT(p, val) (*(unsigned int *)(p) = (val) | GET_TAG(p))
#define PUT_NOTAG(p, val) (*(unsigned int *)(p) = (val))

// Store predecessor or successor pointer for free blocks
//위에꺼랑 합쳐쓰기 싫으니까 그냥 여기서 나눠줌
#define SET_PTR(p, ptr) (*(unsigned int *)(p) = (unsigned int)(ptr))

// Read the size and allocation bit from address p
#define GET_SIZE(p) (GET(p) & ~0x7)
#define GET_ALLOC(p) (GET(p) & 0x1)
#define GET_TAG(p) (GET(p) & 0x2)
#define SET_RATAG(p) (GET(p) |= 0x2)
#define REMOVE_RATAG(p) (GET(p) &= ~0x2)

// Address of block's header and footer
#define HDRP(ptr) ((char *)(ptr)-WSIZE)
#define FTRP(ptr) ((char *)(ptr) + GET_SIZE(HDRP(ptr)) - DSIZE)

// Address of (physically) next and previous blocks
#define NEXT_BLKP(ptr) ((char *)(ptr) + GET_SIZE((char *)(ptr)-WSIZE))
#define PREV_BLKP(ptr) ((char *)(ptr)-GET_SIZE((char *)(ptr)-DSIZE))

// Address of free block's predecessor and successor entries
#define PRED_PTR(ptr) ((char *)(ptr))
#define SUCC_PTR(ptr) ((char *)(ptr) + WSIZE)

// Address of free block's predecessor and successor on the segregated list
#define PRED(ptr) (*(char **)(ptr))
#define SUCC(ptr) (*(char **)(SUCC_PTR(ptr)))

team_t team = {
    /* Team name */
    "ateam",
    /* First member's full name */
    "Harry Bovik",
    /* First member's email address */
    "bovik@cs.cmu.edu",
    /* Second member's full name (leave blank if none) */
    "",
    /* Second member's email address (leave blank if none) */
    ""};
// Global var
void *segregated_free_lists[LISTLIMIT];

// Functions
static void *extend_heap(size_t size);
static void *coalesce(void *ptr);
static void *place(void *ptr, size_t asize);
static void insert_node(void *ptr, size_t size);
static void delete_node(void *ptr);

//static void checkheap(int verbose);

///////////////////////////////// Block information /////////////////////////////////////////////////////////
/*
 
A   : Allocated? (1: true, 0:false)
RA  : Reallocation tag (1: true, 0:false)
 
 < Allocated Block >
 
 
             31 30 29 28 27 26 25 24 23 22 21 20 19 18 17 16 15 14 13 12 11 10  9  8  7  6  5  4  3  2  1  0
            +--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+
 Header :   |                              size of the block                                       |  |  | A|
    bp ---> +--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+
            |                                                                                               |
            |                                                                                               |
            .                              Payload and padding                                              .
            .                                                                                               .
            .                                                                                               .
            +--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+
 Footer :   |                              size of the block                                       |     | A|
            +--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+
 
 
 < Free block >
 
             31 30 29 28 27 26 25 24 23 22 21 20 19 18 17 16 15 14 13 12 11 10  9  8  7  6  5  4  3  2  1  0
            +--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+
 Header :   |                              size of the block                                       |  |RA| A|
    bp ---> +--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+
            |                        pointer to its predecessor in Segregated list                          |
bp+WSIZE--> +--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+
            |                        pointer to its successor in Segregated list                            |
            +--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+
            .                                                                                               .
            .                                                                                               .
            .                                                                                               .
            +--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+
 Footer :   |                              size of the block                                       |     | A|
            +--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+
 
 
*/
///////////////////////////////// End of Block information /////////////////////////////////////////////////////////

//////////////////////////////////////// Helper functions //////////////////////////////////////////////////////////
static void *extend_heap(size_t size)
{
    void *ptr;
    size_t asize; // Adjusted size

    asize = ALIGN(size);

    if ((ptr = mem_sbrk(asize)) == (void *)-1)
        return NULL;

    // Set headers and footer
    PUT_NOTAG(HDRP(ptr), PACK(asize, 0));
    PUT_NOTAG(FTRP(ptr), PACK(asize, 0));
    PUT_NOTAG(HDRP(NEXT_BLKP(ptr)), PACK(0, 1));
    insert_node(ptr, asize);

    return coalesce(ptr);
}

static void insert_node(void *ptr, size_t size)
{
    int list = 0;
    void *search_ptr = ptr;
    void *insert_ptr = NULL;

    // Select segregated list
    while ((list < LISTLIMIT - 1) && (size > 1))
    {
        size >>= 1;
        list++;
    }

    // Keep size ascending order and search
    search_ptr = segregated_free_lists[list];
    while ((search_ptr != NULL) && (size > GET_SIZE(HDRP(search_ptr))))
    {
        insert_ptr = search_ptr;
        search_ptr = PRED(search_ptr);
    }
    //prev쪽이 뒷쪽으로 가는 거고 succ이 리스트의 앞쪽임
    // Set predecessor and successor
    if (search_ptr != NULL)
    {
        if (insert_ptr != NULL)
        { //이건 사이에 들어감
            SET_PTR(PRED_PTR(ptr), search_ptr);
            SET_PTR(SUCC_PTR(search_ptr), ptr);
            SET_PTR(SUCC_PTR(ptr), insert_ptr);
            SET_PTR(PRED_PTR(insert_ptr), ptr);
        }
        else // ptr이 맨 앞에 들어감
        {
            SET_PTR(PRED_PTR(ptr), search_ptr);
            SET_PTR(SUCC_PTR(search_ptr), ptr);
            SET_PTR(SUCC_PTR(ptr), NULL);
            segregated_free_lists[list] = ptr;
        }
    }
    else
    {
        if (insert_ptr != NULL) //ptr이 맨끝에들어감
        {
            SET_PTR(PRED_PTR(ptr), NULL);
            SET_PTR(SUCC_PTR(ptr), insert_ptr);
            SET_PTR(PRED_PTR(insert_ptr), ptr);
        }
        else
        { //이건 둘다 없으니 내가 포인터 처음이 됨
            SET_PTR(PRED_PTR(ptr), NULL);
            SET_PTR(SUCC_PTR(ptr), NULL);
            segregated_free_lists[list] = ptr;
        }
    }

    return;
}

static void delete_node(void *ptr)
{
    int list = 0;
    size_t size = GET_SIZE(HDRP(ptr));

    // Select segregated list
    while ((list < LISTLIMIT - 1) && (size > 1))
    {
        size >>= 1;
        list++;
    }

    if (PRED(ptr) != NULL) //다음꺼 그러니까 리스트 순회할때는 다음임
    {
        if (SUCC(ptr) != NULL) // 여기는 전이랑 후가 있는거임
        {
            //둘다 있으니까 둘사이를 연결 해줌
            SET_PTR(SUCC_PTR(PRED(ptr)), SUCC(ptr));
            SET_PTR(PRED_PTR(SUCC(ptr)), PRED(ptr));
        }
        else //SUCC이 NULL 이고 pred로 현재 포인터 바꿔줌
        {    //이건 ptr입장에서 전꺼가 없으니까 ptr이 없어지면 앞에것의 전을 null로
            SET_PTR(SUCC_PTR(PRED(ptr)), NULL);
            segregated_free_lists[list] = PRED(ptr); // 그리고 처음 값 바꿔줌 맨앞이니까
        }
    }
    else
    {
        if (SUCC(ptr) != NULL) //이거는 ptr 다음도이없고 전꺼는 있을때 즉 맨 뒤임
            SET_PTR(PRED_PTR(SUCC(ptr)), NULL);

        else //둘다 없으니까 ptr 지우면 그냥 NULL됨
        {
            segregated_free_lists[list] = NULL;
        }
    }

    return;
}

static void *coalesce(void *ptr)
{
    size_t prev_alloc = GET_ALLOC(HDRP(PREV_BLKP(ptr)));
    size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(ptr)));
    size_t size = GET_SIZE(HDRP(ptr));

    // Do not coalesce with previous block if the previous block is tagged with Reallocation tag
    //전에꺼 헤드에서 RA태그 가져옴  만약 태그가 있으면 prev를 1로 바꿔줌 즉 비어있는게 아니게됨
    if (GET_TAG(HDRP(PREV_BLKP(ptr))))
        prev_alloc = 1;
    //기존 경우와 같이 나눠줌
    if (prev_alloc && next_alloc)
    { // Case 1
        return ptr;
    }
    else if (prev_alloc && !next_alloc)
    { // Case 2
        delete_node(ptr);
        delete_node(NEXT_BLKP(ptr));
        size += GET_SIZE(HDRP(NEXT_BLKP(ptr)));
        PUT(HDRP(ptr), PACK(size, 0));
        PUT(FTRP(ptr), PACK(size, 0));
    }
    else if (!prev_alloc && next_alloc)
    { // Case 3
        delete_node(ptr);
        delete_node(PREV_BLKP(ptr));
        size += GET_SIZE(HDRP(PREV_BLKP(ptr)));
        PUT(FTRP(ptr), PACK(size, 0));
        PUT(HDRP(PREV_BLKP(ptr)), PACK(size, 0));
        ptr = PREV_BLKP(ptr);
    }
    else
    { // Case 4
        delete_node(ptr);
        delete_node(PREV_BLKP(ptr));
        delete_node(NEXT_BLKP(ptr));
        size += GET_SIZE(HDRP(PREV_BLKP(ptr))) + GET_SIZE(HDRP(NEXT_BLKP(ptr)));
        PUT(HDRP(PREV_BLKP(ptr)), PACK(size, 0));
        PUT(FTRP(NEXT_BLKP(ptr)), PACK(size, 0));
        ptr = PREV_BLKP(ptr);
    }

    insert_node(ptr, size);

    return ptr;
}

static void *place(void *ptr, size_t asize)
{
    size_t ptr_size = GET_SIZE(HDRP(ptr));
    size_t remainder = ptr_size - asize;

    delete_node(ptr);

    if (remainder <= DSIZE * 2)
    {
        // Do not split block
        PUT(HDRP(ptr), PACK(ptr_size, 1));
        PUT(FTRP(ptr), PACK(ptr_size, 1));
    }

    else if (asize >= 100) //일정 크기를 넘어가면 빈공간을 앞으로 해줌
    {
        // Split block
        PUT(HDRP(ptr), PACK(remainder, 0));
        PUT(FTRP(ptr), PACK(remainder, 0));
        PUT_NOTAG(HDRP(NEXT_BLKP(ptr)), PACK(asize, 1)); //큰사이즈를 두고 태그가 없음
        PUT_NOTAG(FTRP(NEXT_BLKP(ptr)), PACK(asize, 1));
        insert_node(ptr, remainder);
        return NEXT_BLKP(ptr);
    }

    else //기존 조건과 같이 나눠줌
    {
        // Split block
        PUT(HDRP(ptr), PACK(asize, 1));
        PUT(FTRP(ptr), PACK(asize, 1));
        PUT_NOTAG(HDRP(NEXT_BLKP(ptr)), PACK(remainder, 0));
        PUT_NOTAG(FTRP(NEXT_BLKP(ptr)), PACK(remainder, 0));
        insert_node(NEXT_BLKP(ptr), remainder);
    }
    return ptr;
}

//////////////////////////////////////// End of Helper functions ////////////////////////////////////////

/*
 * mm_init - initialize the malloc package.
 * Before calling mm_malloc, mm_realloc, or mm_free, 
 * the application program calls mm_init to perform any necessary initializations,
 * such as allocating the initial heap area.
 *
 * Return value : -1 if there was a problem, 0 otherwise.
 */
int mm_init(void)
{
    int list;
    char *heap_start; // Pointer to beginning of heap

    // Initialize segregated free lists
    for (list = 0; list < LISTLIMIT; list++)
    {
        segregated_free_lists[list] = NULL;
    }

    // Allocate memory for the initial empty heap
    if ((long)(heap_start = mem_sbrk(4 * WSIZE)) == -1)
        return -1;

    PUT_NOTAG(heap_start, 0);                            /* Alignment padding */
    PUT_NOTAG(heap_start + (1 * WSIZE), PACK(DSIZE, 1)); /* Prologue header */
    PUT_NOTAG(heap_start + (2 * WSIZE), PACK(DSIZE, 1)); /* Prologue footer */
    PUT_NOTAG(heap_start + (3 * WSIZE), PACK(0, 1));     /* Epilogue header */

    if (extend_heap(INITCHUNKSIZE) == NULL)
        return -1;

    return 0;
}

/*
 * mm_malloc - Allocate a block by incrementing the brk pointer.
 *     Always allocate a block whose size is a multiple of the alignment.
 *
 * Role : 
 * 1. The mm_malloc routine returns a pointer to an allocated block payload.
 * 2. The entire allocated block should lie within the heap region.
 * 3. The entire allocated block should overlap with any other chunk.
 * 
 * Return value : Always return the payload pointers that are alligned to 8 bytes.
 */
void *mm_malloc(size_t size)
{
    size_t asize;      /* Adjusted block size */
    size_t extendsize; /* Amount to extend heap if no fit */
    void *ptr = NULL;  /* Pointer */

    // Ignore size 0 cases
    if (size == 0)
        return NULL;

    // Align block size
    if (size <= DSIZE)
    {
        asize = 2 * DSIZE;
    }
    else
    {
        asize = ALIGN(size + DSIZE);
    }

    int list = 0;
    size_t searchsize = asize;
    // Search for free block in segregated list
    while (list < LISTLIMIT)
    {
        if ((list == LISTLIMIT - 1) || ((searchsize <= 1) && (segregated_free_lists[list] != NULL)))
        {
            ptr = segregated_free_lists[list];
            // Ignore blocks that are too small or marked with the reallocation bit
            while ((ptr != NULL) && ((asize > GET_SIZE(HDRP(ptr))) || (GET_TAG(HDRP(ptr)))))
            {
                ptr = PRED(ptr);
            }
            if (ptr != NULL)
                break;
        }

        searchsize >>= 1;
        list++;
    }

    // if free block is not found, extend the heap
    if (ptr == NULL)
    {
        extendsize = MAX(asize, CHUNKSIZE);

        if ((ptr = extend_heap(extendsize)) == NULL)
            return NULL;
    }

    // Place and divide block
    ptr = place(ptr, asize);

    // Return pointer to newly allocated block
    return ptr;
}

/*
 * mm_free - Freeing a block does nothing.
 *
 * Role : The mm_free routine frees the block pointed to by ptr
 *
 * Return value : returns nothing
 */
void mm_free(void *ptr)
{
    size_t size = GET_SIZE(HDRP(ptr));

    REMOVE_RATAG(HDRP(NEXT_BLKP(ptr))); // RA태그를 reallocation 할때 오른쪽을 주니까 오른쪽을 체크해서 있으면 지워줌
    PUT(HDRP(ptr), PACK(size, 0));
    PUT(FTRP(ptr), PACK(size, 0));

    insert_node(ptr, size);
    coalesce(ptr);

    return;
}

/*
 * mm_realloc - Implemented simply in terms of mm_malloc and mm_free
 *
 * Role : The mm_realloc routine returns a pointer to an allocated 
 *        region of at least size bytes with constraints.
 *
 *  I used https://github.com/htian/malloc-lab/blob/master/mm.c source idea to maximize utilization
 *  by using reallocation tags
 *  in reallocation cases (realloc-bal.rep, realloc2-bal.rep)
 */
void *mm_realloc(void *ptr, size_t size)
{
    void *new_ptr = ptr;    /* Pointer to be returned */
    size_t new_size = size; /* Size of new block */
    int remainder;          /* Adequacy of block sizes */
    int extendsize;         /* Size of heap extension */
    int block_buffer;       /* Size of block buffer */

    // Ignore size 0 cases
    if (size == 0)
        return NULL;

    // Align block size
    if (new_size <= DSIZE)
    {
        new_size = 2 * DSIZE;
    }
    else
    {
        new_size = ALIGN(size + DSIZE);
    }

    /* Add overhead requirements to block size */
    new_size += REALLOC_BUFFER; //이거 그냥 버퍼 크기 주는 것 같음

    /* Calculate block buffer */
    block_buffer = GET_SIZE(HDRP(ptr)) - new_size; //이렇게 크기 구해서 만약 0보다 작으면 더 할당 해줘야됨

    /* Allocate more space if overhead falls below the minimum */
    if (block_buffer < 0)
    {
        /* Check if next block is a free block or the epilogue block */
        //다음 노드가  비어있거나 , 에필로그일때
        if (!GET_ALLOC(HDRP(NEXT_BLKP(ptr))) || !GET_SIZE(HDRP(NEXT_BLKP(ptr))))
        {
            remainder = GET_SIZE(HDRP(ptr)) + GET_SIZE(HDRP(NEXT_BLKP(ptr))) - new_size;
            if (remainder < 0) //에필로그인 경우
            {
                extendsize = MAX(-remainder, CHUNKSIZE);
                if (extend_heap(extendsize) == NULL)
                    return NULL;
                remainder += extendsize;
            }
            //아니면 다음 블록을 가용노드로 합침
            delete_node(NEXT_BLKP(ptr));

            // Do not split block
            PUT_NOTAG(HDRP(ptr), PACK(new_size + remainder, 1));
            PUT_NOTAG(FTRP(ptr), PACK(new_size + remainder, 1));
        }
        else //블럭이 없다면 새로 할당해줌
        {
            new_ptr = mm_malloc(new_size - DSIZE);
            memcpy(new_ptr, ptr, MIN(size, new_size));
            mm_free(ptr);
        }

        block_buffer = GET_SIZE(HDRP(new_ptr)) - new_size;
    }

    // Tag the next block if block overhead drops below twice the overhead
    //일정 기준보다 작다면 RA태그를 해줌 근데 엄청 크면 굳이 해줄 필요가 없음
    if (block_buffer < 2 * REALLOC_BUFFER)
        SET_RATAG(HDRP(NEXT_BLKP(new_ptr)));

    // Return the reallocated block
    return new_ptr;
}