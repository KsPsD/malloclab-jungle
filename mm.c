/*
 * mm-naive.c - The fastest, least memory-efficient malloc package.
 * i
 * In this naive approach, a block is allocated by simply incrementing
 * the brk pointer.  A block is pure payload. There are no headers or
 * footers.  Blocks are never coalesced or reused. Realloc is
 * implemented directly using mm_malloc and mm_free.
 *
 * NOTE TO STUDENTS: Replace this header comment with your own header
 * comment that gives a high level description of your solution.
 */

#include <stdio.h>
#include <stdlib.h>
#include <assert.h>
#include <unistd.h>
#include <string.h>

#include "mm.h"
#include "memlib.h"

/*********************************************************
 * NOTE TO STUDENTS: Before you do anything else, please
 * provide your team information in the following struct.
 ********************************************************/
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

#define WSIZE 4
#define DSIZE 8
#define CHUNKSIZE (1 << 12)

#define MAX(x, y) ((x) > (y) ? (x) : (y))
#define PACK(size, alloc) ((size) | (alloc))

//p 주소에 사이즈 저장하거나 가져오기
#define GET(p) (*(unsigned int *)(p))
#define PUT(p, val) (*(unsigned int *)(p) = (val))

//p주소에 해당하는 사이즈와 현재 할당 되었는지 여부를 가져옴
#define GET_SIZE(p) (GET(p) & ~0x7)
#define GET_ALLOC(p) (GET(p) & 0x1)

//현재 블록의 헤더와 풋터를 찾음
#define HDRP(bp) ((char *)(bp)-WSIZE)
#define FTRP(bp) ((char *)(bp) + GET_SIZE(HDRP(bp)) - DSIZE)

//다음 블록 ,이전 블록을 찾음
#define NEXT_BLKP(bp) ((char *)(bp) + GET_SIZE(((char *)(bp)-WSIZE)))
#define PREV_BLKP(bp) ((char *)(bp)-GET_SIZE(((char *)(bp)-DSIZE)))

static char *heap_listp;
static char *cur_bp;
static char *ex_bp;
void mm_free(void *ptr);
static void *coalesce(void *bp);
static void *extend_heap(size_t words);
int mm_init(void);
static void *find_fit(size_t size);
static void *place(void *bp, size_t asize);

//////implicit 가용 리스트 방법이고  next fit으로 구현했습니다.

static void *coalesce(void *bp) //가용 블록들을 연결시켜주는 함수
{
    size_t prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(bp))); //
    size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp)));
    size_t size = GET_SIZE(HDRP(bp));

    if (prev_alloc && next_alloc)
        return bp;
    else if (prev_alloc && !next_alloc) // 앞 쪽이 가용 상태
    {
        size += GET_SIZE(HDRP(NEXT_BLKP(bp)));
        PUT(HDRP(bp), PACK(size, 0));
        PUT(FTRP(bp), PACK(size, 0));
    }
    else if (!prev_alloc && next_alloc) //뒷쪽이 가용 상태
    {
        size += GET_SIZE(HDRP(PREV_BLKP(bp)));
        PUT(FTRP(bp), PACK(size, 0));
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
        bp = PREV_BLKP(bp);
    }
    else //앞 뒤 둘다
    {
        size += GET_SIZE(HDRP(PREV_BLKP(bp))) + GET_SIZE(FTRP(NEXT_BLKP(bp)));
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
        PUT(FTRP(NEXT_BLKP(bp)), PACK(size, 0));
        bp = PREV_BLKP(bp);
    }
    cur_bp = bp;
    return bp;
}
static void *extend_heap(size_t words)
{
    char *bp;
    size_t size;
    size = (words % 2) ? (words + 1) * WSIZE : words * WSIZE;

    if ((long)(bp = mem_sbrk(size)) == -1)
        return NULL;

    PUT(HDRP(bp), PACK(size, 0)); //그전 init에서 바꿔준 brk에서 헤더랑 풋터에 사이즈 담고
    PUT(FTRP(bp), PACK(size, 0));
    PUT(HDRP(NEXT_BLKP(bp)), PACK(0, 1)); // 바뀐 헤더에서 다음 칸 찾아서 거기에 에필로그 넣어줌

    return coalesce(bp);
}

int mm_init(void)
{
    if ((heap_listp = mem_sbrk(4 * WSIZE)) == (void *)-1) //4워드 가져워서 빈 가용 리스트를 만듬
        return -1;

    PUT(heap_listp, 0);
    PUT(heap_listp + (1 * WSIZE), PACK(DSIZE, 1)); //header
    PUT(heap_listp + (2 * WSIZE), PACK(DSIZE, 1)); //footer
    PUT(heap_listp + (3 * WSIZE), PACK(0, 1));     //epilogue
    heap_listp += (2 * WSIZE);

    if (extend_heap(CHUNKSIZE / WSIZE) == NULL) //첫 시작 힙크기 늘려줌
        return -1;

    cur_bp = heap_listp; //next fit이기 때문에 현재 가용블록의 위치를 가리킴
    return 0;
}

static void *find_fit(size_t asize)
{
    void *start_bp = cur_bp; //현재 가용 블록 부터 시작
    while (GET_SIZE(HDRP(start_bp)) > 0)
    {
        if (!GET_ALLOC(HDRP(start_bp)) && (asize <= GET_SIZE(HDRP(start_bp)))) //할당 되어 있지 않고 사이즈가 맞다면 리턴해줌
        {
            cur_bp = start_bp;
            return start_bp;
        }

        start_bp = NEXT_BLKP(start_bp);
    }
    //찾지 못하면 처음 부터 다시 찾음
    start_bp = heap_listp;
    while (GET_SIZE(HDRP(start_bp)) > 0)
    {
        if (!GET_ALLOC(HDRP(start_bp)) && (asize <= GET_SIZE(HDRP(start_bp))))
            return start_bp;
        start_bp = NEXT_BLKP(start_bp);
    }
    return NULL;
}
//
//가용 블록들에 할당 된 뒤 분할 하는 과정
static void *place(void *bp, size_t asize)
{
    size_t size = GET_SIZE(HDRP(bp));
    if (size - asize >= DSIZE * 2)
    {
        PUT(HDRP(bp), PACK(asize, 1));
        PUT(FTRP(bp), PACK(asize, 1));
        bp = NEXT_BLKP(bp);
        PUT(HDRP(bp), PACK(size - asize, 0));
        PUT(FTRP(bp), PACK(size - asize, 0));
    }
    else
    {
        PUT(HDRP(bp), PACK(size, 1));
        PUT(FTRP(bp), PACK(size, 1));
    }
}
//블록 할당 해주는 부분
void *mm_malloc(size_t size)
{

    size_t asize;
    size_t extendsize;
    char *bp;

    if (size == 0)
        return NULL;
    if (size <= DSIZE) //최소 공간 만큼은 할당 해줌
        asize = 2 * DSIZE;
    else //최소 공간의 배수 형태로 만들어줌
        asize = DSIZE * ((size + (DSIZE) + (DSIZE - 1)) / DSIZE);

    //할당 가능한 블록 찾는다면 분할 해주고 위치 바꿔줌
    if ((bp = find_fit(asize)) != NULL)
    {
        place(bp, asize);
        return bp;
    }
    //맞는 블록이 없다면 힙의 크기를 늘려줌
    extendsize = MAX(asize, CHUNKSIZE);
    if ((bp = extend_heap(extendsize / WSIZE)) == NULL)
        return NULL;
    //맞게 분할해 준다
    place(bp, asize);
    return bp;
}

//할당된 블록을 반환하는 함수
void mm_free(void *ptr)
{
    size_t size = GET_SIZE(HDRP(ptr));
    PUT(HDRP(ptr), PACK(size, 0));
    PUT(FTRP(ptr), PACK(size, 0));
    //반환 한뒤 연결 할 수 있는지 확인해줌
    coalesce(ptr);
}

//재할당 하는 과정
void *mm_realloc(void *ptr, size_t size)
{
    void *oldptr = ptr;
    void *newptr;
    size_t copySize;

    newptr = mm_malloc(size); //할당할 만큼 사이즈를 받아 줌
    if (newptr == NULL)
        return NULL;
    copySize = GET_SIZE(HDRP(oldptr)); //기존 블록 위치 사이즈 가져옴
    if (size < copySize)               // 기존 블록사이즈가 더 크다면 새로 할당한 사이즈 만큼만 받음
        copySize = size;
    memcpy(newptr, oldptr, copySize); // 사이즈 바꿔줌
    mm_free(oldptr);                  //기존 블록 해제 해줌
    return newptr;
}
