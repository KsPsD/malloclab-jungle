#include <stdio.h>
#include <stdlib.h>
#include <assert.h>
#include <unistd.h>
#include <string.h>
#include <sys/mman.h>
#include <errno.h>
#include "mm.h"
#include "memlib.h"

#define WSIZE 4
#define DSIZE 8
#define CHUNKSIZE (1 << 12)
#define MAX(x, y) ((x) > (y) ? (x) : (y))
#define PACK(size, alloc) ((size) | (alloc))
#define GET(p) (*(unsigned int *)(p))
#define PUT(p, val) (*(unsigned int *)(p) = (val))
#define GET_SIZE(p) (GET(p) & ~0x7)
#define GET_ALLOC(p) (GET(p) & 0x1)
#define HDRP(bp) ((char *)(bp)-WSIZE)
#define FTRP(bp) ((char *)(bp) + GET_SIZE(HDRP(bp)) - DSIZE)
#define NEXT_BLKP(bp) ((char *)(bp) + GET_SIZE(HDRP(bp)))
#define PREV_BLKP(bp) ((char *)(bp)-GET_SIZE(HDRP(bp) - WSIZE))
#define PREC_FREEP(bp) (*(void **)(bp))         // *(GET(PREC_FREEP(bp))) == 다음 가용리스트의 bp //Predecessor
#define SUCC_FREEP(bp) (*(void **)(bp + WSIZE)) // *(GET(SUCC_FREEP(bp))) == 다음 가용리스트의 bp //successor

static void *extend_heap(size_t words);
static void *coalesce(void *bp);
static void *find_fit(size_t asize);
static void place(void *bp, size_t asize);
void removeBlock(void *bp);
void putFreeBlock(void *bp);
static char *heap_listp = NULL;
static char *free_listp = NULL; // 가용리스트의 첫번째 블록을 가리키는 포인터

int mm_init(void)
{
    heap_listp = mem_sbrk(24);
    if (heap_listp == (void *)-1)
    {
        return -1;
    }
    PUT(heap_listp, 0);                       //패딩
    PUT(heap_listp + WSIZE, PACK(16, 1));     //프롤로그 헤더
    PUT(heap_listp + 2 * WSIZE, NULL);        //프롤로그 PREC 포인터 NULL로 초기화
    PUT(heap_listp + 3 * WSIZE, NULL);        //프롤로그 SUCC 포인터 NULL로 초기화
    PUT(heap_listp + 4 * WSIZE, PACK(16, 1)); //프롤로그 풋터
    PUT(heap_listp + 5 * WSIZE, PACK(0, 1));  //에필로그 헤더

    free_listp = heap_listp + DSIZE; // free_listp 초기화
    //가용리스트에 블록이 추가될 때 마다 항상 리스트의 제일 앞에 추가될 것이므로 지금 생성한 프롤로그 블록은 항상 가용리스트의 끝에 위치하게 된다.

    if (extend_heap(CHUNKSIZE / DSIZE) == NULL)
    {
        return -1;
    }
    return 0;
}

static void *extend_heap(size_t words)
{
    size_t size;
    char *bp;
    size = words * DSIZE;
    if ((bp = mem_sbrk(size)) == (void *)-1)
        return NULL;

    PUT(HDRP(bp), PACK(size, 0));
    PUT(FTRP(bp), PACK(size, 0));
    PUT(HDRP(NEXT_BLKP(bp)), PACK(0, 1));
    return coalesce(bp);
}

void *mm_malloc(size_t size)
{
    void *bp;
    size_t extend_size;
    size_t asize;

    if (size == 0)
        return NULL;

    if (size <= DSIZE)
    {
        asize = 2 * DSIZE;
    }
    else
    {
        asize = DSIZE * ((size + (DSIZE) + (DSIZE - 1)) / DSIZE);
    }

    if ((bp = find_fit(asize)) != NULL)
    {
        place(bp, asize);
        return bp;
    }
    extend_size = MAX(asize, CHUNKSIZE);
    bp = extend_heap(extend_size / DSIZE);
    if (bp == NULL)
        return NULL;
    place(bp, asize);
    return bp;
}

static void *find_fit(size_t asize)
{
    // first fit
    void *bp;
    bp = free_listp;
    //가용리스트 내부의 유일한 할당 블록은 맨 뒤의 프롤로그 블록이므로 할당 블록을 만나면 for문을 종료한다.
    for (bp; GET_ALLOC(HDRP(bp)) != 1; bp = SUCC_FREEP(bp))
    {
        if (GET_SIZE(HDRP(bp)) >= asize)
        {
            return bp;
        }
    }
    return NULL;
}

static void place(void *bp, size_t asize)
{
    size_t csize;
    csize = GET_SIZE(HDRP(bp));
    // 할당될 블록이니 가용리스트 내부에서 제거해준다.
    removeBlock(bp);
    if (csize - asize >= 16)
    {
        PUT(HDRP(bp), PACK(asize, 1));
        PUT(FTRP(bp), PACK(asize, 1));
        bp = NEXT_BLKP(bp);
        PUT(HDRP(bp), PACK(csize - asize, 0));
        PUT(FTRP(bp), PACK(csize - asize, 0));
        // 가용리스트 첫번째에 분할된 블럭을 넣는다.
        putFreeBlock(bp);
    }
    else
    {
        PUT(HDRP(bp), PACK(csize, 1));
        PUT(FTRP(bp), PACK(csize, 1));
    }
}

//새로 반환되거나 생성된 가용 블록을 가용리스트 맨 앞에 추가한다.
void putFreeBlock(void *bp)
{
    SUCC_FREEP(bp) = free_listp;
    PREC_FREEP(bp) = NULL;
    PREC_FREEP(free_listp) = bp;
    free_listp = bp;
}

//항상 가용리스트 맨 뒤에 프롤로그 블록이 존재하고 있기 때문에 조건을 간소화할 수 있다.
void removeBlock(void *bp)
{
    // 첫번째 블럭을 없앨 때
    if (bp == free_listp)
    {
        PREC_FREEP(SUCC_FREEP(bp)) = NULL;
        free_listp = SUCC_FREEP(bp);
        // 앞 뒤 모두 있을 때
    }
    else
    {
        SUCC_FREEP(PREC_FREEP(bp)) = SUCC_FREEP(bp);
        PREC_FREEP(SUCC_FREEP(bp)) = PREC_FREEP(bp);
    }
}

void mm_free(void *bp)
{
    size_t size = GET_SIZE(HDRP(bp));
    PUT(HDRP(bp), PACK(size, 0));
    PUT(FTRP(bp), PACK(size, 0));
    coalesce(bp);
}

static void *coalesce(void *bp)
{
    size_t prev_alloc = GET_ALLOC(HDRP(PREV_BLKP(bp)));
    size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp)));
    size_t size = GET_SIZE(HDRP(bp));

    //이미 가용리스트에 존재하던 블록은 연결하기 이전에 가용리스트에서 제거해준다.
    if (prev_alloc && !next_alloc)
    {
        removeBlock(NEXT_BLKP(bp));
        size += GET_SIZE(HDRP(NEXT_BLKP(bp)));
        PUT(HDRP(bp), PACK(size, 0));
        PUT(FTRP(bp), PACK(size, 0));
    }
    else if (!prev_alloc && next_alloc)
    {
        removeBlock(PREV_BLKP(bp));
        size += GET_SIZE(HDRP(PREV_BLKP(bp)));
        bp = PREV_BLKP(bp);
        PUT(HDRP(bp), PACK(size, 0));
        PUT(FTRP(bp), PACK(size, 0));
    }
    else if (!prev_alloc && !next_alloc)
    {
        removeBlock(PREV_BLKP(bp));
        removeBlock(NEXT_BLKP(bp));
        size += GET_SIZE(HDRP(NEXT_BLKP(bp))) + GET_SIZE(HDRP(PREV_BLKP(bp)));
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
        PUT(FTRP(NEXT_BLKP(bp)), PACK(size, 0));
        bp = PREV_BLKP(bp);
    }
    //연결된 블록을 가용리스트에 추가
    putFreeBlock(bp);
    return bp;
}

void *mm_realloc(void *bp, size_t size)
{
    if (size <= 0)
    {
        mm_free(bp);
        return 0;
    }
    if (bp == NULL)
    {
        return mm_malloc(size);
    }
    void *newp = mm_malloc(size);
    if (newp == NULL)
    {
        return 0;
    }
    size_t oldsize = GET_SIZE(HDRP(bp));
    if (size < oldsize)
    {
        oldsize = size;
    }
    memcpy(newp, bp, oldsize);
    mm_free(bp);
    return newp;
}