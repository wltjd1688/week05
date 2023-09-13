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
// #define SEGREGATED_SIZE (16)                        // segregated list에서 size를 정해줘야함

#define MAX(x,y) (((x) > (y) ? (x): (y)))

// 케스팅과 포인터 연산
#define PACK(size, alloc) ((size) | (alloc))        // 크기와 할당 비트를 통합하여 헤더와 폴더에 저장할 수 있는 값을 리턴한다.

// 인자 p가 참조하는 워드를 읽거나 val에 저장하고 return 한다.
#define GET(p) (*(unsigned int *)(p))
#define PUT(p,val) (*(unsigned int *)(p) = (unsigned)(val))

// 각각의 주소 p에 있는 헤더 또는 폴더의 size와 할당비트를 return
#define GET_SIZE(p) (GET(p) & ~0x7)
#define GET_ALLOC(p) (GET(p) & 0x1)
// #define GET_ROOT(class) (*(void **)((char *)(heap_listp) + (WSIZE * class)))
#define PREV(bp) (*(void **)(bp))
#define SUSS(bp) (*(void **)((char *)(bp) + WSIZE))

// 각각 블록 헤더와 풋터를 가리키는 포인터를 리턴한다.
#define HDRP(bp) ((char *)(bp) - WSIZE)
#define FTRP(bp) ((char *)(bp) + GET_SIZE(HDRP(bp)) - DSIZE)

// 다음과 이전 블록의 포인터를 각각 리턴한다.
#define NEXT_BLKP(bp) ((char *)(bp) + GET_SIZE(((char *)(bp) - WSIZE)))
#define PREV_BLKP(bp) ((char *)(bp) - GET_SIZE(((char *)(bp) - DSIZE)))

// #define NUM_LISTS 32

static void* heap_listp;
// static void* pointp;                     // next_fit - 할당한 불럭의 포인터를 저장해줌
static char* free_listp;                // explicit list - 가용불럭 포인터 표시용
static void* extend_heap(size_t);
static void* coalesce(void *);
static void* find_fit(size_t);
// static void* next_fit(size_t asize);     // next_fit
static void place(void *, size_t);
// static int get_class(size_t size);          // segregate list에서 class 찾을때 사용
// explicit, segregated, buddy system에서 사용
static void delete_node(void *bp);
static void insert_node(void *bp);


/* 
 * mm_init - initialize the malloc package.
 */
int mm_init(void)
{
    /* // segregated list & buddy system
    if ((heap_listp = mem_sbrk((SEGREGATED_SIZE + 4) * WSIZE)) == (void *)-1)                   // segregated list & buddy system 메모리 시스템에서 (SEGREGATED_SIZE + 4)word 추출
        return -1;
    // 초기화 작업
    PUT(heap_listp, 0);                                                                         // 패딩
    PUT(heap_listp + (1*WSIZE), PACK((SEGREGATED_SIZE+2) * WSIZE, 1));                          // 프롤로그 헤더
    for (int i = 0; i < SEGREGATED_SIZE; i++)                                                   // 세그리게이트 사이즈에 맞게 root역할을 할 블럭을 생성해준다.
        PUT(heap_listp + ((2 + i) * WSIZE), NULL);
    PUT(heap_listp + ((SEGREGATED_SIZE + 2) * WSIZE), PACK((SEGREGATED_SIZE + 2) * WSIZE, 1));  // 프롤로그 풋터
    PUT(heap_listp + ((SEGREGATED_SIZE + 3) * WSIZE), PACK(0, 1));                              // 에필로그 헤더
    heap_listp += (2*WSIZE);                                                                    // 세그리게이트의 첫번째로 포인터를 옮겨준다.
    */

    /* // implicit
    if ((heap_listp = mem_sbrk(4 * WSIZE)) == (void *)-1)                                       // implicit 메모리 시스템에서 4word 추출
        return -1;
    // 초기화 작업
    PUT(heap_listp, 0);                                                                         // 패딩
    PUT(heap_listp + (1*WSIZE), PACK(DSIZE, 1));                                                // 프롤로그 헤더
    PUT(heap_listp + (2* WSIZE), PACK(DSIZE * WSIZE, 1));                                       // 프롤로그 풋터
    PUT(heap_listp + (3* WSIZE), PACK(0, 1));                                                   // 에필로그 헤더
    heap_listp += (2*WSIZE);                                                                    // payload 시작부분으로 포인터를 옮겨준다.
    // pointp = heap_listp;                                                                     // next_fit에서 사용하는 pointp 
    free_listp = heap_listp + 2*WSIZE;                                                          // explicit free list에서 포인터로 사용
    */

   // explicit
   if ((heap_listp = mem_sbrk(6 * WSIZE)) == (void *)-1)                                        //Explicit 메모리 시스템에서 4word 추출
        return -1;
    // 초기화 작업
    PUT(heap_listp, 0);                                                                         // 패딩
    PUT(heap_listp + (1* WSIZE), PACK(2*DSIZE, 1));                                               // 프롤로그 헤더
    PUT(heap_listp + (2* WSIZE), NULL);                                                         // 이전 가용 불럭의 주소(PREV)
    PUT(heap_listp + (3* WSIZE), NULL);                                                         // 다음 가용 불럭의 주소(SUCC)
    PUT(heap_listp + (4* WSIZE), PACK(2*DSIZE, 1));                                       // 프롤로그 풋터
    PUT(heap_listp + (5* WSIZE), PACK(0, 1));                                                   // 에필로그 헤더
    free_listp = heap_listp + DSIZE;                                                            // explicit free list에서 포인터로 사용

    if (extend_heap(4) == NULL)                                                                 // 이걸 넣어서 왜 2점이나 오른거지...?
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

    if (size <= 0)                          // 잘못된 요청 분기
        return NULL;
    // 8바이트 이하일때 최소블록크기 할당
    if (size <= DSIZE)
        asize = 2*DSIZE;
    else
        // 8바이트 이상일 때 오버헤드 바이트를 추가하고, 인접의 8의 배수로 반올림한다.
        asize = DSIZE * ((size + DSIZE + (DSIZE-1))/DSIZE);
        // asize = ALIGN(size + DSIZE);
    // 가용리스트 검색
    if ((bp = find_fit(asize)) != NULL){
        // 요청한 블록을 배치하고, 옵션으로 초과부분을 분할하고, 새롭게 할당한 불록을 리턴한다.
        place(bp, asize);                   // 할당
        return bp;                          // 새로 할당된 블록의 포인터 리턴
    }

    // 새로운 가용불럭 힙 확장
    extendsize = MAX(asize, CHUNKSIZE);                 // asize와 CHUNKSIZE중 더 큰값을 extendsize로 지정하고 늘려줌
    if ((bp = extend_heap(extendsize/WSIZE)) == NULL)   // 늘려줄 수 있는지 아닌지
        return NULL;
    place(bp, asize);
    return bp;
}

/*
 * mm_free - Freeing a block does nothing.
 */
void mm_free(void *bp)
{
    size_t size = GET_SIZE(HDRP(bp));
    PUT(HDRP(bp), PACK(size, 0));           // 헤더를 가용블럭으로 만들어주기
    PUT(FTRP(bp), PACK(size, 0));           // 풋터를 가용블럭으로 만들어주기 + buddy system에서는 필요없음
    coalesce(bp);
}

/*
 * mm_realloc - Implemented simply in terms of mm_malloc and mm_free
 */
void *mm_realloc(void *ptr, size_t size) {
    /* //기초에 if문 추가한 realloc
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
    */

    void *oldptr = ptr;
    void *newptr;
    size_t copySize;

    if (size <= (GET_SIZE(HDRP(ptr))-DSIZE)){                                                                           // size가 기존보다 작으면 그대로 
        return ptr;
    }
    if (GET_ALLOC(HDRP(NEXT_BLKP(ptr))) == 0 && GET_SIZE(HDRP(NEXT_BLKP(ptr))) > (size - GET_SIZE(HDRP(ptr))-DSIZE)){   // ptr불럭의 다음블럭이 가용이고 ptr불럭 사이즈보다 size가 더 클때

        delete_node(NEXT_BLKP(ptr));                                                                                    // 다음불럭 삭제해주기
        size_t sum = GET_SIZE(HDRP(ptr)) + GET_SIZE(HDRP(NEXT_BLKP(ptr)));                                              // 사이즈 늘려주기 후 할당표시해주기
        PUT(HDRP(ptr), PACK(sum,1));
        PUT(FTRP(ptr), PACK(sum,1));
        return ptr;
    }
    // 그외
    newptr = mm_malloc(size);
    if (newptr == NULL)
      return NULL;
    copySize = GET_SIZE(HDRP(oldptr));
    memcpy(newptr, oldptr, copySize);
    mm_free(oldptr);
    return newptr;
}

static void* extend_heap(size_t words) {
    char* bp;
    /*
    // buddy system 구현할려고 바꾼 코드
    // 힙 확장
    if ((long)(bp = mem_sbrk(words * WSIZE)) == -1)
        return NULL;

    PUT(HDRP(bp), PACK(words * WSIZE, 0));              // 새 빈 블록 헤더 초기화
    PUT(FTRP(bp), PACK(words * WSIZE, 0));              // 새 빈 블록 헤더 초기화
    PUT(HDRP(NEXT_BLKP(bp)), PACK(0,1));                // 에필로그 블록 헤더 초기화
    return coalesce(bp);                                // 병합 후 리턴 블록 포인터 변환
    */

    // size: 확장할 크기
    size_t size = (words % 2) ? (words + 1) * WSIZE : words * WSIZE;// 2워드의 가장 가까운 배수로 반올림 (홀수면 1 더해서 곱함)

    if ((bp = mem_sbrk(size)) == (void*)-1)                          // 힙 확장
        return NULL;

    PUT(HDRP(bp), PACK(size, 0));                                   // 새 빈 블록 헤더 초기화
    PUT(FTRP(bp), PACK(size, 0));                                   // 새 빈 블록 푸터 초기화
    PUT(HDRP(NEXT_BLKP(bp)), PACK(0, 1));                           // 에필로그 블록 헤더 초기화

    return coalesce(bp);                                            // 병합 후 coalesce 함수에서 리턴된 블록 포인터 반환
}

static void* coalesce(void *bp)
{
    /* buddy system 구현할려고 따온 코드
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
    */
    // bp의 이전, 이후 불럭의 할당 여부 확인
    size_t prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(bp)));
    size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp)));
    size_t size = GET_SIZE(HDRP(bp));                                           // 현재 불럭의 사이느

    if (prev_alloc && !next_alloc){                                             // case 2 - 오른쪽만 가용불럭일 때
        delete_node(NEXT_BLKP(bp));                                             // 합치기 전에 오른쪾 불럭 삭제
        size += GET_SIZE(HDRP(NEXT_BLKP(bp)));                                  // size 병합
        PUT(HDRP(bp), PACK(size, 0));                                           // head에 size넣기
        PUT(FTRP(bp), PACK(size, 0));                                           // head에 size를 넣었기 때문에 bp의 풋터로 바로 이동하여 size를 넣는다.

    } else if (!prev_alloc && next_alloc) {                                     // case 3 - 왼쪽만 가용불럭일 때
        delete_node(PREV_BLKP(bp));                                             // 합치기 전에 왼쪽 불럭 삭제
        size += GET_SIZE(HDRP(PREV_BLKP(bp)));                                  // size 병합
        bp = PREV_BLKP(bp);                                                     // bp를 이전블록으로 옮긴 후 뒤와같이 size넣기
        PUT(HDRP(bp), PACK(size, 0));
        PUT(FTRP(bp), PACK(size, 0));
    
    } else if (!prev_alloc && !next_alloc) {                                    // case 4 - 둘다 가용불럭일 때
        delete_node(PREV_BLKP(bp));                                             // 이전 가용 불럭 삭제
        delete_node(NEXT_BLKP(bp));                                             // 다음 가용 불럭 삭제 
        size += GET_SIZE(HDRP(PREV_BLKP(bp))) + GET_SIZE(FTRP(NEXT_BLKP(bp)));  // size 병합하기
        bp = PREV_BLKP(bp);                                                     // head는 이전불럭이 가지고 있으므로 bp를 이전불럭의 payload첫번째로 이동
        PUT(HDRP(bp), PACK(size, 0));                                           // 위와 같이 size넣기
        PUT(FTRP(bp), PACK(size, 0));
    }
    insert_node(bp);                                                            // case1 + 이후 가용불럭 넣기
    // pointp = bp;                                                             // next_fit 에서 사용되는 표인터
    return bp;
}

// // segregate list find_fit
// static void *find_fit(size_t asize)
// {
//     int class = get_class(asize);
//     void *bp = GET_ROOT(class);
//     while (class < SEGREGATED_SIZE) // 현재 탐색하는 클래스가 범위 안에 있는 동안 반복
//     {
//         bp = GET_ROOT(class);
//         while (bp != NULL)
//         {
//             if ((asize <= GET_SIZE(HDRP(bp)))) // 적합한 사이즈의 블록을 찾으면 반환
//                 return bp;
//             bp = SUSS(bp); // 다음 가용 블록으로 이동
//         }
//         class += 1;
//     }
//     return NULL;
// }

// explicit list find_fit
static void * find_fit(size_t asize) {
    void * bp;

    for (bp=free_listp; GET_ALLOC(HDRP(bp)) != 1; bp = SUSS(bp)){
        if (asize <= GET_SIZE(HDRP(bp))){ 
            return bp;
        }
    }
    return NULL;
}

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

// explicit list LIFO의 삭제노드
static void delete_node(void *bp){
    if(bp == free_listp) {          // bp가 free list의 가장 첫번째 요소라면
        PREV(SUSS(bp))=NULL;        // 삭제할 노드의 다음 불럭의 전주소를 NULL로
        free_listp=SUSS(bp);        // root의 다음을 삭제할 노드의 다음 주소로 연결해준다.
    } else {
        SUSS(PREV(bp)) = SUSS(bp);  // 이전 노드의 다음 불럭 주소를 다음 노드와 연결
        PREV(SUSS(bp)) = PREV(bp);  // 다음 노드의 이전 불럭 주소를 이전 불럭가 연결
    }
}

// explicit list LIFO의 삽입노드
static void insert_node(void *bp){  // LIFO방식이므로 root 다음에 가용불럭을 연결
    SUSS(bp) = free_listp;          // root의 다음 불럭 주소를 삽입할 가용불럭의 다음 주소에 추가
    PREV(bp) = NULL;                // 현재 불럭의 이전 불럭은 root 이므로 NULL을 추가함
    PREV(free_listp) = bp;          // 다음불럭의 이전 불럭 주소를 넣는 자리에 bp주소를 넣음
    free_listp = bp;                // root의 다음불럭을 bp로 만들어줌
}

/* // segregated list & buddy system -insert_node, delete_node, get_class
static void insert_node(void *bp){
    int class = get_class(GET_SIZE(HDRP(bp)));
    SUSS(bp) = GET_ROOT(class);         // bp의 해당 가용 리스트의 루트가 가리키던 블록
    if (GET_ROOT(class) != NULL)        // list에 블록이 존재했을 경우만
        PREV(GET_ROOT(class)) = bp;     // 루트였던 블록의 PRED를 추가된 블록으로 연결
    GET_ROOT(class) = bp;
}

static void delete_node(void* bp){

    int class = get_class(GET_SIZE(HDRP(bp)));
    if (bp == GET_ROOT(class)) // 분리하려는 블록이 free_list 맨 앞에 있는 블록이면 (이전 블록이 없음)
    {
        GET_ROOT(class) = SUSS(GET_ROOT(class)); // 다음 블록을 루트로 변경
        return;
    }
    // 이전 블록의 SUCC을 다음 가용 블록으로 연결
    SUSS(PREV(bp)) = SUSS(bp);
    // 다음 블록의 PRED를 이전 블록으로 변경
    if (SUSS(bp) != NULL) // 다음 가용 블록이 있을 경우만
        PREV(SUSS(bp)) = PREV(bp);
}


int get_class(size_t size)
{
    int temp = 31 - __builtin_clz(size);
    if (temp > SEGREGATED_SIZE-1){
        return SEGREGATED_SIZE - 1;
    } else {
        return temp;
    }
}
*/

static void place(void *bp, size_t asize){      // 할당할 위치의 bp, 사용할 양
    /* // explicit list
    delete_node(bp);                            // free_list에서 해당 블록 제거
    size_t csize = GET_SIZE(bp);                // 사용하려는 블록의 크기

    while (asize != csize){                     // 사용하려는 asize와 블록의 크기 csize가 다르면
        csize >>= 1;                            // 블록의 크기를 반으로 나눔
        PUT(HDRP(bp + csize), PACK(csize,0));   // 뒷부분을 가용 블록으로 변경
        insert_node(bp + csize);                // 뒷부분을 가용 블록 리스트에 추가
    }
    PUT(HDRP(bp), PACK(csize,1));               // 크기가 같아지면 해당 블록 사용 처리
    */

    // implict, explicit
    size_t csize = GET_SIZE(HDRP(bp));          // find_fit으로 찾은 가용불럭의 크기
    delete_node(bp);                            // 이제 할당할거니까 가용 리스트에서 삭제

    if ((csize - asize) >= (2*DSIZE)) {         // 할당하고도 남은 부분이 최소불럭 단위보다 크다면
        PUT(HDRP(bp), PACK(asize, 1));          // 헤더랑 풋터를 이용해 asize 만큼 할당하고 
        PUT(FTRP(bp), PACK(asize, 1));
        bp = NEXT_BLKP(bp);                     // 남은 영역을 가용불럭으로 만들어준다
        PUT(HDRP(bp), PACK((csize-asize), 0));
        PUT(FTRP(bp), PACK((csize-asize), 0));
        insert_node(bp);                        // 그리고 가용불럭을 가용리스트에 추가해준다.
    }
    else{
        PUT(HDRP(bp), PACK(csize, 1));          // 할당받은 불럭의 남은부분이 최소불럭보다 작거나 딱맞다면 그냥 할당해주면된다
        PUT(FTRP(bp), PACK(csize, 1));
    }
}

/*
Results for mm malloc:
trace  valid  util     ops      secs  Kops
 0       yes   89%    5694  0.001071  5318
 1       yes   92%    5848  0.000360 16222
 2       yes   94%    6648  0.000628 10581
 3       yes   96%    5380  0.000443 12153
 4       yes   99%   14400  0.001610  8942
 5       yes   89%    4800  0.000961  4994
 6       yes   85%    4800  0.001053  4557
 7       yes   55%   12000  0.002868  4183
 8       yes   51%   24000  0.002939  8165
 9       yes   53%   14401  0.000793 18153
10       yes   27%   14401  0.002915  4940
Total          75%  112372  0.015643  7183

Perf index = 45 (util) + 40 (thru) = 85/100
*/