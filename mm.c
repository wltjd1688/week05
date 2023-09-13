/*
 * mm-naive.c - The fastest, least memory-efficient malloc package.
 * 
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
    "week05-5조",
    /* First member's full name */
    "Kim Jisung",
    /* First member's email address */
    "wltjd1688@gmail.com",
    "",
    "",
};

/* single word (4) or double word (8) alignment */
#define ALIGNMENT 8

/* rounds up to the nearest multiple of ALIGNMENT */
#define ALIGN(size) (((size) + (ALIGNMENT-1)) & ~0x7)

// 기본 size 상수
#define WSIZE 4
#define DSIZE 8
// #define MINIMUM 16
#define CHUNKSIZE (1<<13)                           // 초기불럭과 힙확장을 위한 기본크기
#define SEGREGATED_SIZE (16)

#define MAX(x,y) (((x) > (y) ? (x): (y)))

// 케스팅과 포인터 연산
#define PACK(size, alloc) ((size) | (alloc))        // 크기와 할당 비트를 통합하여 헤더와 폴더에 저장할 수 있는 값을 리턴한다.

// 인자 p가 참조하는 워드를 읽거나 val에 저장하고 return 한다.
#define GET(p) (*(unsigned int *)(p))
#define PUT(p,val) (*(unsigned int *)(p) = (unsigned)(val))

// 각각의 주소 p에 있는 헤더 또는 폴더의 size와 할당비트를 return
#define GET_SIZE(p) (GET(p) & ~0x7)
#define GET_ALLOC(p) (GET(p) & 0x1)
#define GET_ROOT(class) (*(void **)((char *)(heap_listp) + (WSIZE * class)))
#define PREV(bp) (*(void **)(bp))
#define SUSS(bp) (*(void **)((char *)(bp) + WSIZE))

// 각각 블록 헤더와 풋터를 가리키는 포인터를 리턴한다.
#define HDRP(bp) ((char *)(bp) - WSIZE)
#define FTRP(bp) ((char *)(bp) + GET_SIZE(HDRP(bp)) - DSIZE)

// 다음과 이전 블록의 포인터를 각각 리턴한다.
#define NEXT_BLKP(bp) ((char *)(bp) + GET_SIZE(((char *)(bp) - WSIZE)))
#define PREV_BLKP(bp) ((char *)(bp) - GET_SIZE(((char *)(bp) - DSIZE)))

#define NUM_LISTS 32

static void* heap_listp;
// static char* free_array;
// static void* pointp;
// static char* free_listp;
static void* extend_heap(size_t);
static void* coalesce(void *);
static void* find_fit(size_t);
// static void* next_fit(size_t asize);
static void place(void *, size_t);
static int get_class(size_t size);
static void insert_node(void *bp);
static void delete_node(void *bp);

/* 
 * mm_init - initialize the malloc package.
 */
int mm_init(void)
{
    // heap_listp를 생성할 수 있는지 확인
    if ((heap_listp = mem_sbrk((SEGREGATED_SIZE + 4) * WSIZE)) == (void *)-1) // 메모리 시스템에서 4word 추출
        return -1;
    // 초기화 작업
    PUT(heap_listp, 0);                                                                         // 패딩
    PUT(heap_listp + (1*WSIZE), PACK((SEGREGATED_SIZE+2) * WSIZE, 1));                          // 프롤로그 헤더
    for (int i = 0; i < SEGREGATED_SIZE; i++)                                                   // 세그리게이트 사이즈에 맞게 root역할을 할 블럭을 생성해준다.
        PUT(heap_listp + ((2 + i) * WSIZE), NULL);
    PUT(heap_listp + ((SEGREGATED_SIZE + 2) * WSIZE), PACK((SEGREGATED_SIZE + 2) * WSIZE, 1));  // 프롤로그 풋터
    PUT(heap_listp + ((SEGREGATED_SIZE + 3) * WSIZE), PACK(0, 1));                              // 에필로그 헤더
    heap_listp += (2*WSIZE);                                                                    // 세그리게이트의 첫번째로 포인터를 옮겨준다.
    // pointp = heap_listp;                                                                     // next_fit에서 사용하는 pointp 
    // free_listp = heap_listp + 2*WSIZE;                                                       // explicit free list에서 포인터로 사용
    if (extend_heap(4) == NULL)                                                                 // ---------- 이걸 왜 하는지 모르겠음... 근데 하면 점수 더 준다고해서 일단 넣어둠
        return -1;
    if (extend_heap(CHUNKSIZE / WSIZE) == NULL)
        return -1;                                                                              // ----------
    return 0;
}

//  * mm_malloc - Allocate a block by incrementing the brk pointer.
//  *     Always allocate a block whose size is a multiple of the alignment.
//  */
void *mm_malloc(size_t size)
{
    size_t asize;                           // 조정된 블록 사이즈
    size_t extendsize;                      // 확장할 사이즈
    char * bp;

    if (size == 0)                          // 잘못된 요청 분기
        return NULL;
    // 8바이트 이하일때 최소블록크기 할당
    if (size <= DSIZE)
        asize = 2*DSIZE;
    else
        // 8바이트 이상일 때 오버헤드 바이트를 추가하고, 인접의 8의 배수로 반올림한다.
        asize = ALIGN(size+DSIZE);
    // 가용리스트 검색
    if ((bp = find_fit(asize)) != NULL){
        // 요청한 블록을 배치하고, 옵션으로 초과부분을 분할하고, 새롭게 할당한 불록을 리턴한다.
        place(bp, asize);                   // 할당
        return bp;                          // 새로 할당된 블록의 포인터 리턴
    }

    // 새로운 가용불럭 힙 확장
    extendsize = MAX(asize, CHUNKSIZE); // PAGE_REQUEST_SIZE 배수만큼 추가 메모리 요청
    if ((bp = extend_heap(extendsize/WSIZE)) == NULL)
        return NULL;
    place(bp, asize);
    return bp;
    // int newsize = ALIGN(size + SIZE_T_SIZE);
    // void *p = mem_sbrk(newsize);
    // if (p == (void *)-1)
	// return NULL;
    // else {
    //     *(size_t *)p = size;
    //     return (void *)((char *)p + SIZE_T_SIZE);
    // }
}

// explicit list LIFO의 삭제노드
// void delete_node(void *bp){
//     if(bp == free_listp) {
//         PREV(SUSS(bp))=NULL;
//         free_listp=SUSS(bp);
//     } else {
//         SUSS(PREV(bp)) = SUSS(bp);
//         PREV(SUSS(bp)) = PREV(bp);
//     }
// }

// explicit list LIFO의 삽입노드
// void insert_list(void *bp){
//     SUSS(bp) = free_listp;
//     PREV(bp) = NULL;
//     PREV(free_listp) = bp;
//     free_listp = bp;
// }

/*
 * mm_free - Freeing a block does nothing.
 */
void mm_free(void *bp)
{
    size_t size = GET_SIZE(HDRP(bp));
    PUT(HDRP(bp), PACK(size, 0));           // 헤더를 가용블럭으로 만들어주기
    PUT(FTRP(bp), PACK(size, 0));           // 풋터를 가용블럭으로 만들어주기
    coalesce(bp);
    // insert_node(bp);
}

/*
 * mm_realloc - Implemented simply in terms of mm_malloc and mm_free
 */
void *mm_realloc(void *ptr, size_t size) {
    // ptr이 null이면 malloc을 해준다.
    if (ptr == NULL)
        return mm_malloc(size);
    
    // size가 0 이면 가용블럭으로 만들어준다.
    if (size <= 0)
    {
        mm_free(ptr);
        return 0;
    }

    // 복사할 새로운 size를 할당한다.
    void* newptr = mm_malloc(size);
    if (newptr == NULL)
        return NULL;

    // 기존 ptr의 size를 가져온다.
    size_t copySize = GET_SIZE(HDRP(ptr)) - DSIZE;
    // size가 copysize보다 작을때 기존 copysize를 size로 줄여서 옮긴다.
    if (size < copySize)
        copySize = size;
    // 새로운ptr에 copySize만큼 넣어준다.
    memcpy(newptr, ptr, copySize);
    // ptr을 free해준다.
    mm_free(ptr);
    return newptr;
    // void *oldptr = ptr;
    // void *newptr;
    // size_t copySize;

    // if (size <= (GET_SIZE(HDRP(ptr))-DSIZE)){
    //     return ptr;
    // }
    // if (GET_ALLOC(HDRP(NEXT_BLKP(ptr))) == 0 && GET_SIZE(HDRP(NEXT_BLKP(ptr))) > (size - GET_SIZE(HDRP(ptr))-DSIZE)){

    //     delete_node(NEXT_BLKP(ptr));
    //     size_t sum = GET_SIZE(HDRP(ptr)) + GET_SIZE(HDRP(NEXT_BLKP(ptr)));
    //     PUT(HDRP(ptr), PACK(sum,1));
    //     PUT(FTRP(ptr), PACK(sum,1));
    //     return ptr;
    // }

    // newptr = mm_malloc(size);
    // if (newptr == NULL)
    //   return NULL;
    // copySize = GET_SIZE(HDRP(oldptr));
    // memcpy(newptr, oldptr, copySize);
    // mm_free(oldptr);
    // return newptr;
}

static void* extend_heap(size_t words) {
    char* bp;
    // 힙 확장
    if ((long)(bp = mem_sbrk(words * WSIZE)) == -1)
        return NULL;

    PUT(HDRP(bp), PACK(words * WSIZE, 0));              // 새 빈 블록 헤더 초기화
    PUT(HDRP(NEXT_BLKP(bp)), PACK(0,1));                // 에필로그 블록 헤더 초기화
    return coalesce(bp);                                // 병합 후 리턴 블록 포인터 변환
}

static void* coalesce(void *bp)
{
    insert_node(bp);                                            // 현재 블록을 free list에 추가
    size_t csize = GET_SIZE(HDRP(bp));                          // 변환할 사이즈
    void *root = heap_listp + (SEGREGATED_SIZE + 2) * WSIZE;    // 실제 메모리 블록들이 시작하는 위치
    void *left_buddyp;                                          // 왼쪽 버디의 bp
    void *right_buddyp;                                         // 오른쪽 버디의 bp

    while(1)
    {
        // 좌우 버디의 bp 파악
        if ((bp-root) & csize)     // 현재 블록에서 힙까지의 메모리 합(bp - root)과 csize가 중복되는 비트가 있다면 현재 블록은 오른쪽 버디에 해당
        {
            left_buddyp = bp-csize;
            right_buddyp = bp;
        }
        else
        {
            right_buddyp = bp + csize;
            left_buddyp = bp;
        }
        // 양쪽 버디가 모두 가용 상태이고, 각 사이즈가 동일하면 (각 버디가 분할되어있지 않으면)
        if (!GET_ALLOC(HDRP(left_buddyp)) && !GET_ALLOC(HDRP(right_buddyp)) && GET_SIZE(HDRP(left_buddyp))==GET_SIZE(right_buddyp))
        {
            delete_node(left_buddyp);               // 양쪽 버디를 모두 가용 리스트에서 제거
            delete_node(right_buddyp);
            csize <<= 1;                            // size를 2배로 변경
            PUT(HDRP(left_buddyp), PACK(csize,0));  // 왼쪽 버디부터 size만큼 가용 블록으로 변경
            insert_node(left_buddyp);               // 가용 블록으로 변경된 블록을 free list에 추가
            bp = left_buddyp;
        } else{
            break;
        }
    }
        return bp;
}
    // size_t prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(bp)));
    // size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp)));
    // size_t size = GET_SIZE(HDRP(bp));

    // if (prev_alloc && !next_alloc){                                        // case 2
    //     delete_node(NEXT_BLKP(bp));
    //     size += GET_SIZE(HDRP(NEXT_BLKP(bp)));
    //     PUT(HDRP(bp), PACK(size, 0));
    //     PUT(FTRP(bp), PACK(size, 0));

    // } else if (!prev_alloc && next_alloc) { 
    //     delete_node(PREV_BLKP(bp));                                      // case 3
    //     size += GET_SIZE(HDRP(PREV_BLKP(bp)));
    //     bp = PREV_BLKP(bp);
    //     PUT(HDRP(bp), PACK(size, 0));
    //     PUT(FTRP(bp), PACK(size, 0));
    
    // } else if (!prev_alloc && !next_alloc) { 
    //     delete_node(PREV_BLKP(bp));                                             // case 4
    //     delete_node(NEXT_BLKP(bp));
    //     size += GET_SIZE(HDRP(PREV_BLKP(bp))) + GET_SIZE(FTRP(NEXT_BLKP(bp)));
    //     bp = PREV_BLKP(bp);
    //     PUT(HDRP(bp), PACK(size, 0));
    //     PUT(FTRP(bp), PACK(size, 0));
    // }
    // insert_node(bp);
    // // insert_list(bp);
    // // pointp = bp;
    // return bp;

// segregate list find_fit
static void *find_fit(size_t asize)
{
    int class = get_class(asize);
    void *bp = GET_ROOT(class);
    while (class < SEGREGATED_SIZE) // 현재 탐색하는 클래스가 범위 안에 있는 동안 반복
    {
        bp = GET_ROOT(class);
        while (bp != NULL)
        {
            if ((asize <= GET_SIZE(HDRP(bp)))) // 적합한 사이즈의 블록을 찾으면 반환
                return bp;
            bp = SUSS(bp); // 다음 가용 블록으로 이동
        }
        class += 1;
    }
    return NULL;
}

// explicit list find_fit
// static void * find_fit(size_t asize) {
//     void * bp;

//     for (bp=free_listp; GET_ALLOC(HDRP(bp)) != 1; bp = SUSS(bp)){
//         if (asize <= GET_SIZE(HDRP(bp))){ 
//             return bp;
//         }
//         // bp = NEXT_BLKP(bp);
//     }
//     return NULL;
// }

// static void * next_fit(size_t asize){
//     void * bp;
//     // if (bp == NULL) bp = heap_listp;
//     for(bp = pointp; GET_SIZE(HDRP(bp))>0;bp = NEXT_BLKP(bp)){
//         if(!GET_ALLOC(HDRP(bp)) && (asize <= GET_SIZE(HDRP(bp)))){
//             pointp = bp;
//             return bp;
//         }
//     }
//     for(bp = heap_listp; bp != pointp; bp = NEXT_BLKP(bp)){
//         if(!GET_ALLOC(HDRP(bp)) && (asize <= GET_SIZE(HDRP(bp)))){
//             pointp = bp;
//             return bp;
//         }
//     }
//     return NULL;
// }

// segregated list
// static void insert_node(void *bp){
//     int class = get_class(GET_SIZE(HDRP(bp)));
//     SUSS(bp) = GET_ROOT(class);         // bp의 해당 가용 리스트의 루트가 가리키던 블록
//     if (GET_ROOT(class) != NULL)        // list에 블록이 존재했을 경우만
//         PREV(GET_ROOT(class)) = bp;     // 루트였던 블록의 PRED를 추가된 블록으로 연결
//     GET_ROOT(class) = bp;
// }

// static void delete_node(void* bp){

//     int class = get_class(GET_SIZE(HDRP(bp)));
//     if (bp == GET_ROOT(class)) // 분리하려는 블록이 free_list 맨 앞에 있는 블록이면 (이전 블록이 없음)
//     {
//         GET_ROOT(class) = SUSS(GET_ROOT(class)); // 다음 블록을 루트로 변경
//         return;
//     }
//     // 이전 블록의 SUCC을 다음 가용 블록으로 연결
//     SUSS(PREV(bp)) = SUSS(bp);
//     // 다음 블록의 PRED를 이전 블록으로 변경
//     if (SUSS(bp) != NULL) // 다음 가용 블록이 있을 경우만
//         PREV(SUSS(bp)) = PREV(bp);
// }

// 
// int get_class(size_t size)
// {
//     int temp = 31 - __builtin_clz(size);
//     if (temp > SEGREGATED_SIZE-1){
//         return SEGREGATED_SIZE - 1;
//     } else {
//         return temp;
//     }
// }

// explicit list
static void place(void *bp, size_t asize){      // 할당할 위치의 bp, 사용할 양
    delete_node(bp);                            // free_list에서 해당 블록 제거
    size_t csize = GET_SIZE(bp);                // 사용하려는 블록의 크기

    while (asize != csize){                     // 사용하려는 asize와 블록의 크기 csize가 다르면
        csize >>= 1;                            // 블록의 크기를 반으로 나눔
        PUT(HDRP(bp + csize), PACK(csize,0));   // 뒷부분을 가용 블록으로 변경
        insert_node(bp + csize);                // 뒷부분을 가용 블록 리스트에 추가
    }
    PUT(HDRP(bp), PACK(csize,1));               // 크기가 같아지면 해당 블록 사용 처리
    // size_t csize = GET_SIZE(HDRP(bp));
    // delete_node(bp);

    // if ((csize - asize) >= (2*DSIZE)) {
    //     PUT(HDRP(bp), PACK(asize, 1));
    //     PUT(FTRP(bp), PACK(asize, 1));
    //     bp = NEXT_BLKP(bp);
    //     PUT(HDRP(bp), PACK((csize-asize), 0));
    //     PUT(FTRP(bp), PACK((csize-asize), 0));
    //     coalesce(bp);
    // }
    // else{
    //     PUT(HDRP(bp), PACK(csize, 1));
    //     PUT(FTRP(bp), PACK(csize, 1));
    // }
}