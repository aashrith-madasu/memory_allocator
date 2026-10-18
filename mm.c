/*
 * mm.c
 *
 * Name: AASHRITH SAI MADASU
 *
 * APPROACH: This malloc implementation uses a segregated list, 
 * best-fit strategy, splitting-coalescing, footer optimization.
 * 
 * 
 * ********************************* OPTIMIZATIONS ************************************************
 *
 * Segregated list: Using 14 bins with pre-determined boundaries to segregate blocks of different
 *                  sizes to make the search faster and improve utilization.
 * 
 * Splitting-coalescing: If the found block is bigger than enough, the block is split and the 
 *                       remaining space is initialized as a free block and added to the seg-list.
 *                       When a block is freed, it is coalesced with previous and next blocks if 
 *                       they are free.
 * 
 * Footer optimization: Footer is only initialized for free blocks and allocated blocks contain 
 *                      only a header. To enable this, an extra bit in meta-data called "prev_alloc" 
 *                      is maintained. This way when coalescing, one can check if the previous block
 *                      is free without using it's footer.
 * 
 * Storing 16-byte blocks: To improve utilization further, the MIN_BLOCK_SIZE is reduced from 32 to 16.
 *                         For 16-byte blocks, we cannot have all header, footer, next and prev
 *                         pointers, hence, only a header and next pointer is used. To enable this a 
 *                         singly-linked list is used. To enable, coalescing 16-byte blocks, an extra 
 *                         meta-data bit called "prev_16" is maintained. Using this, one could check 
 *                         if the previous block is 16-byte sized and merge accordingly.
 * 
 * Best-fit seach: For a requested size, first the corresponding bin is determined. And the search is 
 *                 performed in the bin (doubly linked-list). Best-fit strategy is used but with a 
 *                 search limit to ensure the balance of utilization and throughput. If a suitable 
 *                 block is not found within the limit, sub-sequent bins are searched and if the bin 
 *                 is non-empty the first block is returned.
 * 
 * Extending heap: If a suitable block is not found, the heap is extended by the requested size or 
 *                 by a minimum size whichever is lower. This is done to ensure that we avoid 
 *                 calling "sbrk" too many times and use the remaning space for further requests.
 *                 
 * 
 */
#include <assert.h>
#include <stdlib.h>
#include <stdio.h>
#include <string.h>
#include <unistd.h>
#include <stdint.h>
#include <stdbool.h>

#include "mm.h"
#include "memlib.h"

/*
 * If you want to enable your debugging output and heap checker code,
 * uncomment the following line. Be sure not to have debugging enabled
 * in your final submission.
 */
// #define DEBUG

#ifdef DEBUG
// When debugging is enabled, the underlying functions get called
#define dbg_printf(...) printf(__VA_ARGS__)
#define dbg_assert(...) assert(__VA_ARGS__)
#else
// When debugging is disabled, no code gets generated
#define dbg_printf(...)
#define dbg_assert(...)
#endif // DEBUG

// do not change the following!
#ifdef DRIVER
// create aliases for driver tests
#define malloc mm_malloc
#define free mm_free
#define realloc mm_realloc
#define calloc mm_calloc
#define memset mm_memset
#define memcpy mm_memcpy
#endif // DRIVER

#define ALIGNMENT 16
#define HEAP_OFFSET 8
#define HEADER_SIZE 8
#define MIN_BLOCK_SIZE 16
#define EXTEND_SIZE 4096
#define SEG_LIST_SIZE 14
#define SEARCH_LIMIT 32


// rounds up to the nearest multiple of ALIGNMENT
static size_t align(size_t x)
{
    return ALIGNMENT * ((x+ALIGNMENT-1)/ALIGNMENT);
}

// global vars 
void* seg_list[SEG_LIST_SIZE];


// >>>>>>>>>> Helper Functions >>>>>>>>>>

static size_t get_size(void* blk)
{
    size_t* header = (size_t*) blk;
    return (*header & ~15);
}

static size_t get_alloc(void* blk)
{
    size_t* header = (size_t*) blk;
    return (*header & 1);  
}

static size_t get_prev_alloc(void* blk)
{
    size_t* header = (size_t*) blk;
    return (*header & 2); 
}

static size_t is_prev_16(void* blk)
{
    size_t* header = (size_t*) blk;
    return (*header & 4); 
}

static size_t get_meta(void* blk)
{
    size_t* header = (size_t*) blk;
    return (*header & 15);
}

static void set_header(void* blk, size_t data)
{
    size_t* header = (size_t*) blk;
    *header = data;
}

static void* get_footer_ref(void* blk)
{
    return (void*)(
        (char*)blk + get_size(blk) - HEADER_SIZE
    );
}

static size_t get_footer(void* blk)
{
    size_t* footer = (size_t*) get_footer_ref(blk);
    return *footer;
}

static void set_footer(void* blk, size_t data)
{
    size_t* footer = (size_t*) get_footer_ref(blk);
    *footer = data;
}

static void* get_payload(void* blk)
{
    return (void*)(
        (char*)blk + HEADER_SIZE
    );
}

static void* get_block(void* payload)
{
    return (void*)(
        (char*)payload - HEADER_SIZE
    );
}

static void* first_block()
{
    return (void*)(
        (char*)mm_heap_lo() + HEAP_OFFSET + 2*HEADER_SIZE
    );
}

static void* prev_block(void* blk)
{
    size_t prev_bksize = is_prev_16(blk) ? 16 : get_size((char*)blk - HEADER_SIZE);

    // reached prologue
    if (prev_bksize == 0) return NULL;

    return (void*)(
        (char*)blk - prev_bksize
    );
}

static void* next_block(void* blk, bool strict)
{
    void* next_blk = (void*)(
        (char*)blk + get_size(blk)
    );

    if (!strict) return next_blk;

    size_t next_bksize = get_size(next_blk);

    // reached epilogue
    if (next_bksize == 0) return NULL;

    return next_blk;
}

// ***** free-list utils *****

static int get_seg_index(size_t size){

    size_t bins[SEG_LIST_SIZE-1] = {32, 64, 128, 256, 512, 1024, 2048,
                                4096, 8192, 16384, 32768, 65536, 131072};

    for (int i=0; i<SEG_LIST_SIZE; i++) {
        if (size < bins[i]) return i;
    }
    return SEG_LIST_SIZE-1;
}


static void* fl_next(void* blk)
{
    // blk MUST be a freelist block
    return (void*)*(uintptr_t*)get_payload(blk);
}

static void fl_set_next(void* blk, void* n)
{
    *(uintptr_t*)get_payload(blk) = (uintptr_t) n;
}

static void* fl_prev(void* blk)
{
    // blk MUST be a freelist block
    if (get_size(blk) == MIN_BLOCK_SIZE) return NULL;

    return (void*)*(uintptr_t*)(
        (char*)get_payload(blk) + 8
    );
}

static void fl_set_prev(void* blk, void* p)
{
    *(uintptr_t*)(
        (char*)get_payload(blk) + 8
    ) = (uintptr_t) p;
}

static void fl_add_block(void* blk)
{
    int seg_index = get_seg_index(get_size(blk));
    
    void* HEAD = seg_list[seg_index];
    
    if (HEAD != NULL) {
        
        fl_set_next(blk, HEAD);
        
        if (seg_index > 0) {
            fl_set_prev(HEAD, blk);
            fl_set_prev(blk, NULL);
        }
    } else {
        fl_set_next(blk, NULL);
        if (seg_index > 0) {
            fl_set_prev(blk, NULL);
        }
    }
    
    seg_list[seg_index] = blk; 
}

static void fl_remove_block(void* blk)
{
    int seg_index = get_seg_index(get_size(blk));

    if (seg_index == 0) {

        void* cur = seg_list[seg_index];
        void* p = NULL;

        while (cur && cur != blk) {
            p = cur;
            cur = fl_next(cur);
        }

        if (cur) {

            if (p) fl_set_next(p, fl_next(cur));
            else seg_list[seg_index] = fl_next(cur);
        }
    } 
    else {

        void* p = fl_prev(blk);
        void* n = fl_next(blk);
        
        if (p) fl_set_next(p, n);
        if (n) fl_set_prev(n, p);
        
        if (!p) seg_list[seg_index] = n;
    }
}



// <<<<<<<<<< Helper Functions <<<<<<<<<<

/*
 * mm_init: returns false on error, true on success.
 */
bool mm_init(void)
{
    /*
        initialize: 
            offset of 8-bytes at the start
            prologue header, 
            prologue footer, 
            epilogue header
    */
    void* lo = mm_sbrk(32);

    // prologue
    *(size_t*)((char*)lo + HEAP_OFFSET) = 0|1;
    *(size_t*)((char*)lo + HEAP_OFFSET + HEADER_SIZE) = 0|1;

    /*
        epilogue
        initial meta-data:
            size = 0
            prev_16 = true
            prev_alloc = true
            alloc = true
    */
    *(size_t*)((char*)lo + HEAP_OFFSET + 2*HEADER_SIZE) = 0|4|2|1;

    // set all bins to NULL 
    for (int i=0; i<SEG_LIST_SIZE; i++) {
        seg_list[i] = NULL;
    }

    return true;
}

/*
 * searchs through the heap to find a free block that
 * best-fits (smallest but big enough) the given size 
 */
void* find_best_fit(size_t size){

    // "blk" should always point a free-list block

    void* best_block = NULL;
    size_t best_size = ~0; // max possible an unsigned int can store

    int seg_index = get_seg_index(size);

    if (seg_index == 0) {

        best_block = seg_list[seg_index];
    } 
    else {

        void* blk = seg_list[seg_index];
        
        for (int i=0; i<SEARCH_LIMIT; i++) {
            
            if(!blk) break;
            
            size_t bksize = get_size(blk);
            
            // best fit
            if (bksize >= size && bksize < best_size) {
                best_block = blk;
                best_size = bksize;
            }
            // move to next block
            blk = fl_next(blk);
        }
    }
    
    seg_index++;
    
    while (!best_block && seg_index < SEG_LIST_SIZE) {
        best_block = seg_list[seg_index];
        seg_index++;
    }

    return best_block;
}

/*
 * malloc
 */
void* malloc(size_t size)
{
    /*
        align the size
        find total chunk space needed including header + footer
        extend the heap
        go back to old epilogue start
        init header
        init new epilogue at the end
        return payload start address
    */

    if (size <= 0) return NULL;

    size_t reqsize = align(size + HEADER_SIZE);

    void* blk = find_best_fit(reqsize);

    size_t bksize, meta;

    if (blk == NULL) { 
        // EXTEND

        size_t extend_size = ((reqsize < EXTEND_SIZE) ? EXTEND_SIZE : reqsize);

        void* oldbrk = mm_sbrk(extend_size);

        blk = get_block(oldbrk); // also old epilogue pointer
        bksize = extend_size;
        meta = get_meta(blk);
        
        // new epilogue
        set_header(blk + extend_size, 0|1);

    } else { 
        // REUSE

        fl_remove_block(blk);

        bksize = get_size(blk);
        meta = get_meta(blk);
    }

    size_t remsize = bksize - reqsize;

    if (remsize >= MIN_BLOCK_SIZE){
        // SPLIT

        // new blk
        set_header(blk, reqsize|meta|1);

        // next blk
        void* n = next_block(blk, false);
        size_t prev_16 = (reqsize==16)<<2;

        set_header(n, remsize|prev_16|2);
        if (remsize > MIN_BLOCK_SIZE){
            set_footer(n, remsize);
        }

        // add next blk to free-list
        fl_add_block(n);


        // Set the prev_16 bit of the next to next block
        void* nn = next_block(n, false);
        prev_16 = (remsize==16)<<2;
        set_header(nn, get_size(nn)|get_meta(nn)|prev_16);

        return get_payload(blk);

    } else {
        // NO SPLIT

        set_header(blk, bksize|meta|1);

        // set prev_alloc of next block to true
        void* n = next_block(blk, false);
        set_header(n, get_size(n)|get_meta(n)|2);

        return get_payload(blk);
    }

}

/*
 * Coalesce 
 * 
 * blk - will have correct header and footer set
 * return a new blk with correct header and footer set - total size and alloc = 0
 * 
 */
static void* coalesce(void* blk){

    if (!get_prev_alloc(blk)) {

        void* p = prev_block(blk);

        if (p) {

            fl_remove_block(p);
            size_t meta = get_meta(p);

            // Merge
            size_t comb_size = get_size(p) + get_size(blk);
            set_header(p, comb_size|meta);
            if (comb_size > MIN_BLOCK_SIZE) 
                set_footer(p, comb_size);
            blk = p;
        }
    }

    void* n = next_block(blk, true);

    if (n && !get_alloc(n)) {
        
        fl_remove_block(n);

        size_t meta = get_meta(blk);

        // Merge
        size_t comb_size = get_size(blk) + get_size(n);
        
        set_header(blk, comb_size|meta);
        if (comb_size > MIN_BLOCK_SIZE)
            set_footer(blk, comb_size);
    }

    return blk;
}

/*
 * free
 */
void free(void* ptr)
{
    /*
        set allocation status in hedaer to 0
        init a footer mirroring the header
    */

    if (ptr == NULL) return;

    // if invalid address
    if (!in_heap(ptr)) return;

    // if address is not aligned
    if (((uintptr_t)ptr & 15) > 0) return;

    
    void* blk = get_block(ptr);
    size_t bksize = get_size(blk);

    size_t meta = get_meta(blk);

    // mark unallocated
    set_header(blk, bksize| (meta & ~1));
    if (bksize > MIN_BLOCK_SIZE)
        set_footer(blk, bksize);

    // coalesce
    blk = coalesce(blk);

    // add to free-list
    fl_add_block(blk);

    // update prev metadata in n
    void* n = next_block(blk, false);

    size_t prev_16 = (get_size(blk)==16) << 2;
    
    set_header(n, get_size(n) | (get_meta(n) & ~6) | prev_16);

    return;
}

/*
 * realloc
 */
void* realloc(void* oldptr, size_t size)
{
    /*
        allocate a new chunk of new size
        copy content from old payload to new payload
        free old chunk
    */

    if (oldptr == NULL) {
        void* newptr = malloc(size);
        return newptr;
    }

    if (size == 0) {
        free(oldptr);
        return NULL;
    }

    size_t oldsize = get_size(get_block(oldptr)) - HEADER_SIZE;

    if (oldsize == size) return oldptr;
    
    void* newptr = malloc(size);

    // copy the data from old block to new block
    mem_memcpy(newptr, oldptr, ((oldsize <= size) ? oldsize : size));

    // de-allocate the old block
    free(oldptr);

    return newptr;
}

/*
 * calloc
 * This function is not tested by mdriver, and has been implemented for you.
 */
void* calloc(size_t nmemb, size_t size)
{
    void* ptr;
    size *= nmemb;
    ptr = malloc(size);
    if (ptr) {
        memset(ptr, 0, size);
    }
    return ptr;
}

/*
 * Returns whether the pointer is in the heap.
 * May be useful for debugging.
 */
static bool in_heap(const void* p)
{
    return p <= mm_heap_hi() && p >= mm_heap_lo();
}

/*
 * Returns whether the pointer is aligned.
 * May be useful for debugging.
 */
static bool aligned(const void* p)
{
    size_t ip = (size_t) p;
    return align(ip) == ip;
}

/*
 * mm_checkheap
 * You call the function via mm_checkheap(__LINE__)
 * The line number can be used to print the line number of the calling
 * function where there was an invalid heap.
 */
bool mm_checkheap(int line_number)
{
// #ifdef DEBUG
    // Write code to check heap invariants here

    // Epilogue should al`ways stay the same to mark the end of the heap

    size_t* epilogue = (size_t*)((char*)mm_heap_hi() - 7);

    bool ok = ((*epilogue & ~15) == 0)
              && ((*epilogue & 1) == 1);

    if (!ok) {
        printf("Line %d : heap is bad \n", line_number);
        printf("epilogue: (%lu | %lu) \n", (*epilogue & ~15), (*epilogue & 1));
        return false;
    }

    void* blk = first_block();

    printf("Heap:");

    while (blk) {
        size_t bksize = get_size(blk);
        if (bksize == 0) break;
        size_t alloc = get_alloc(blk);

        printf("  (%lu,%lu,%lu)", bksize, alloc, get_prev_alloc(blk));

        if (!alloc) {

            printf("<->(%lu)", get_footer(blk) & ~15);
        }
        blk = next_block(blk, true);
    }

    if (blk) {
        printf("\n\nError: bksize is 0 but not epilogue \n");
        return false;
    }

    printf("\nHeap is fine \n");


// #endif // DEBUG
    return true;
}
