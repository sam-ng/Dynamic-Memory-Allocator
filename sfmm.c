/**
 * All functions you make for the assignment must be implemented in this file.
 * Do not submit your assignment with a main function in this file.
 * If you submit with a main function in this file, you will get a zero.
 */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include "debug.h"
#include "sfmm.h"

#include "sfmm_func_proto.h"
#include <errno.h>


void *sf_malloc(size_t size) {
    // if request size equals 0, return NULL without setting sf_errno
    if (size == 0) {
        return NULL;
    }
    size_t block_size = size + BLOCK_HEADER_SIZE; //BLOCK_HEADER_SIZE = 8
    size_t padding = 0;
    if (block_size < MINIMUM_BLOCK_SIZE) {
        padding = MINIMUM_BLOCK_SIZE - block_size; // block_size must be a multiple of 64
        block_size += padding;
    }
    else {
        while (block_size % MINIMUM_BLOCK_SIZE != 0) {
            block_size++;
        }
    }
    if (sf_mem_start() == sf_mem_end()) { // if start and end point to the same address, heap is empty
        sf_malloc_free_list_init();
        sf_malloc_heap_init();
        if (sf_errno == ENOMEM) {
            return NULL;
        }
    }
    sf_block* target_block = traverse_free_list_heads(block_size); // target_block points to a block large enough to hold the requested payload
    while (target_block == NULL) {
        sf_block* new_page = expand_heap();
        if (new_page == NULL) {
            sf_errno = ENOMEM;
            return NULL;
        }
        target_block = traverse_free_list_heads(block_size);
    }
    // target_block has been found
    if ((target_block->header&BLOCK_SIZE_MASK) > block_size) { // if target_block size is larger than block_size, target_block must be split
        target_block = split(target_block, block_size);
    }
    else {
        allocate_block(target_block);
    }
    return target_block->body.payload; // malloc returns pointer to the payload
}

void sf_free(void *pp) {
    // CHECK FOR INVALID POINTER
    // Case 1: null pointer
    if (pp == NULL) {
        abort();
    }
    // Case 2: not 64-byte aligned
    size_t pp_addr = (size_t) pp;
    if (pp_addr % 64 != 0) {
        abort();
    }
    // Case 3: not allocated
    char* pp_addr_cast = (char*) pp;
    pp_addr_cast -= 16; // account for prev_footer and header, as pp points to payload
    sf_block* pp_block_ptr = (sf_block*) pp_addr_cast;
    if ((pp_block_ptr->header & THIS_BLOCK_ALLOCATED) == 0) {
        abort();
    }
    // Case 4: header of block before end of prologue or footer of block after beginning of epilogue
    char* start_addr = (char*) sf_mem_start();
    start_addr += /*unused*/ 48 + /*prev_footer*/ 8 + /*prologue_block*/ 56;
    sf_block* prologue_end_ptr = (sf_block*) start_addr;
    if (pp_block_ptr < prologue_end_ptr) {
        abort();
    }
    char* end_addr = (char*) sf_mem_end();
    end_addr -= 16; // accounts for prev footer and epilogue header
    sf_block* epilogue_ptr = (sf_block*) end_addr;

    size_t pp_size = pp_block_ptr->header & BLOCK_SIZE_MASK;
    pp_addr_cast += pp_size;
    sf_block* pp_footer_ptr = (sf_block*) pp_addr_cast;
    if (pp_footer_ptr > epilogue_ptr) {
        abort();
    }
    // Case 5: prev_alloc field = 0, but alloc field of previous block != 0
    int prev_alloc = pp_block_ptr->header & PREV_BLOCK_ALLOCATED;
    size_t prev_size = pp_block_ptr->prev_footer & BLOCK_SIZE_MASK;
    pp_addr_cast = (char*) pp_block_ptr;
    pp_addr_cast -= prev_size;
    sf_block* prev_block_ptr = (sf_block*) pp_addr_cast;
    if (prev_alloc == 0) {
        if ((prev_block_ptr->header & THIS_BLOCK_ALLOCATED) != 0) {
            abort();
        }
    }
    // VALID POINTER WAS GIVEN
    pp_addr_cast = (char*) pp_block_ptr;
    pp_addr_cast += pp_size;
    sf_block* next_block_ptr = (sf_block*) pp_addr_cast;
    // FREE CURRENT BLOCK FIRST
    pp_block_ptr->header &= (~THIS_BLOCK_ALLOCATED); // zero out THIS_BLOCK_ALLOCATED
    next_block_ptr->prev_footer = pp_block_ptr->header; // set next block's prev_footer
    next_block_ptr->header &= (~PREV_BLOCK_ALLOCATED);
    int index = get_Fibonacci_index(pp_block_ptr->header & BLOCK_SIZE_MASK);
    sf_block* sentinel = &sf_free_list_heads[index];
    insert_free_block_into_list(sentinel, pp_block_ptr);
    sf_block* coalesced_block = pp_block_ptr; // pointer to block to be inserted into free list
    if ((prev_block_ptr->header & THIS_BLOCK_ALLOCATED) == 0) { // PREVIOUS BLOCK IS FREE, COALESCING REQUIRED
        coalesced_block = coalesce(prev_block_ptr, pp_block_ptr);
        if ((next_block_ptr->header & THIS_BLOCK_ALLOCATED) == 0) { // NEXT BLOCK IS FREE, COALESCING REQUIRED
            coalesced_block = coalesce(coalesced_block, next_block_ptr);
        }
    }
    else {
        if ((next_block_ptr->header & THIS_BLOCK_ALLOCATED) == 0) { // PREVIOUS BLOCK IS ALLOCATED, BUT NEXT BLOCK IS FREE, COALESCING REQUIRED
            coalesced_block = coalesce(pp_block_ptr, next_block_ptr);
        }
    }
    return;
}

void *sf_realloc(void *pp, size_t rsize) {
    // CHECK FOR INVALID POINTER
    // Case 1: null pointer
    if (pp == NULL) {
        sf_errno = EINVAL;
        return NULL;
    }
    // Case 2: not 64-byte aligned
    size_t pp_addr = (size_t) pp;
    if (pp_addr % 64 != 0) {
        sf_errno = EINVAL;
        return NULL;
    }
    // Case 3: not allocated
    char* pp_addr_cast = (char*) pp;
    pp_addr_cast -= 16; // account for prev_footer and header, as pp points to payload
    sf_block* pp_block_ptr = (sf_block*) pp_addr_cast;
    if ((pp_block_ptr->header & THIS_BLOCK_ALLOCATED) == 0) {
        sf_errno = EINVAL;
        return NULL;
    }
    // Case 4: header of block before end of prologue or footer of block after beginning of epilogue
    char* start_addr = (char*) sf_mem_start();
    start_addr += /*unused*/ 48 + /*prev_footer*/ 8 + /*prologue_block*/ 56;
    sf_block* prologue_end_ptr = (sf_block*) start_addr;
    if (pp_block_ptr < prologue_end_ptr) {
        sf_errno = EINVAL;
        return NULL;
    }
    char* end_addr = (char*) sf_mem_end();
    end_addr -= 16; // accounts for prev footer and epilogue header
    sf_block* epilogue_ptr = (sf_block*) end_addr;

    size_t pp_size = pp_block_ptr->header & BLOCK_SIZE_MASK;
    pp_addr_cast += pp_size;
    sf_block* pp_footer_ptr = (sf_block*) pp_addr_cast;
    if (pp_footer_ptr > epilogue_ptr) {
        sf_errno = EINVAL;
        return NULL;
    }
    // Case 5: prev_alloc field = 0, but alloc field of previous block != 0
    int prev_alloc = pp_block_ptr->header & PREV_BLOCK_ALLOCATED;
    size_t prev_size = pp_block_ptr->prev_footer & BLOCK_SIZE_MASK;
    pp_addr_cast = (char*) pp_block_ptr;
    pp_addr_cast -= prev_size;
    sf_block* prev_block_ptr = (sf_block*) pp_addr_cast;
    if (prev_alloc == 0) {
        if ((prev_block_ptr->header & THIS_BLOCK_ALLOCATED) != 0) {
            sf_errno = EINVAL;
            return NULL;
        }
    }
    // VALID POINTER WAS GIVEN
    if (rsize == 0) { // if rsize == 0, free allocated block and return NULL
        sf_free(pp);
        return NULL;
    }
    // 2 cases
    pp_addr_cast = (char*) pp;
    pp_addr_cast -= 16; // account for prev_footer and header
    pp_block_ptr = (sf_block*) pp_addr_cast;
    pp_size = pp_block_ptr->header & BLOCK_SIZE_MASK;
    // Case 1: Reallocating to a larger size (pp_size < rsize)
    if (pp_size < rsize) {
        void *larger_block_payload_ptr = sf_malloc(rsize);
        if (larger_block_payload_ptr == NULL) { // if sf_malloc() returns NULL, sf_errno = ENOMEM
            return NULL;
        }
        size_t pp_payload_size = pp_size - BLOCK_HEADER_SIZE;
        // void* memcpy(void* dest, const void* src, size_t size)
        void *dest = memcpy(larger_block_payload_ptr, pp, pp_payload_size);
        sf_free(pp); // free old memory
        return dest;
    } // Case 2: Reallocating to a smaller size (pp_size > rsize)
    else if (pp_size > rsize) {
        size_t block_size = rsize + 8; // size of header if split
        if (block_size < MINIMUM_BLOCK_SIZE) {
            block_size = MINIMUM_BLOCK_SIZE;
        }
        else {
            while(block_size % MINIMUM_BLOCK_SIZE != 0) {
                block_size++;
            }
        }
        if ((pp_size - block_size) > 0 && ((pp_size - block_size) % MINIMUM_BLOCK_SIZE) == 0) {
            pp_addr_cast = (char*) pp_block_ptr;
            pp_addr_cast += pp_size;
            sf_block* next_block_ptr = (sf_block*) pp_addr_cast;
            pp_addr_cast = (char*) pp_block_ptr;
            pp_addr_cast += block_size;
            sf_block* remainder_block_ptr = (sf_block*) pp_addr_cast;
            sf_block* allocated_block = split(pp_block_ptr, block_size);
            if ((next_block_ptr->header & THIS_BLOCK_ALLOCATED) == 0) {
                coalesce(remainder_block_ptr, next_block_ptr);
            }
            return allocated_block->body.payload;
        }

    }
    // Trivial case: pp_size = rsize, sf_realloc() does nothing
    return pp;
}

void *sf_memalign(size_t size, size_t align) {
    // Check if alignment is at least greater than minimum block size
    if (align < MINIMUM_BLOCK_SIZE) {
        sf_errno = EINVAL;
        return NULL;
    }
    // Check if alignment is a power of two
    size_t power_of_two = 1;
    while (1) {
        if (align == power_of_two) {
            break;
        }
        if (align < power_of_two) {
            sf_errno = EINVAL;
            return NULL;
        }
        power_of_two *= 2;
    }
    // Check if size is 0
    if (size == 0) {
        return NULL;
    }
    size_t large_size = /*requested size*/ size + /*alignment size*/ align + MINIMUM_BLOCK_SIZE; // header_size added in sf_malloc()
    void* large_payload_ptr = sf_malloc(large_size);
    if (large_payload_ptr == NULL) {
        return NULL;
    }
    char* large_block_addr = (char*) large_payload_ptr;
    large_block_addr -= 16;
    sf_block* large_block = (sf_block*) large_block_addr; // points to beginning of large_block

    char* payload_end_addr = (char*) large_payload_ptr;
    payload_end_addr += size; // points to end of large_block payload
    char* minimum_block_end_addr = large_block_addr;
    while (minimum_block_end_addr < payload_end_addr) {
        minimum_block_end_addr += MINIMUM_BLOCK_SIZE; // points to possible end of large_block
    }
    char* next_block_addr = large_block_addr;
    next_block_addr += large_block->header & BLOCK_SIZE_MASK; // points to start of next_block
    // if the payload is aligned
    if ((size_t)large_payload_ptr % align == 0) {
        if ((next_block_addr-minimum_block_end_addr) >= MINIMUM_BLOCK_SIZE) { // if there is enough extra space for a block, split
            split(large_block, (size_t)(minimum_block_end_addr-large_block_addr));
            char* free1_addr = (char*) large_block;
            sf_block* free1 = (sf_block*)(free1_addr+(large_block->header&BLOCK_SIZE_MASK));
            char* free2_addr = (char*) free1;
            sf_block* free2 = (sf_block*)(free2_addr+(free1->header&BLOCK_SIZE_MASK));
            coalesce(free1, free2);
        }
        return large_payload_ptr;
    }
    // if the payload isn't aligned
    large_block_addr = (char*) large_payload_ptr;
    int count = 0;
    while ((size_t)large_block_addr % align != 0) {
        large_block_addr++;
        count++;
    }
    if (count < MINIMUM_BLOCK_SIZE) {
        large_block_addr++;
        count++;
        while ((size_t)large_block_addr % align != 0) {
        large_block_addr++;
        count++;
        }
    }
    sf_block* target_block_ptr = (sf_block*)(large_block_addr-16);
    size_t free_size = (count/MINIMUM_BLOCK_SIZE) * MINIMUM_BLOCK_SIZE; // round down to nearest multiple of minimum_block_size
    target_block_ptr = split_alt(large_block, free_size);
    // free block in back
    char* target_block_addr = (char*) target_block_ptr;
    minimum_block_end_addr = target_block_addr;
    payload_end_addr = (char*) target_block_ptr->body.payload;
    payload_end_addr += size; // points to end of large_block payload
    while (minimum_block_end_addr < payload_end_addr) {
        minimum_block_end_addr += MINIMUM_BLOCK_SIZE; // points to possible end of large_block
    }
    if ((next_block_addr-minimum_block_end_addr) >= MINIMUM_BLOCK_SIZE) { // if there is enough extra space for a block, split
        split(target_block_ptr, (size_t)(minimum_block_end_addr-target_block_addr));
        char* free1_addr = (char*) target_block_ptr;
        sf_block* free1 = (sf_block*)(free1_addr+(target_block_ptr->header&BLOCK_SIZE_MASK));
        char* free2_addr = (char*) free1;
        sf_block* free2 = (sf_block*)(free2_addr+(free1->header&BLOCK_SIZE_MASK));
        coalesce(free1, free2);
    }
    return target_block_ptr->body.payload;
}


// Helper Functions

// Called if heap is empty
void sf_malloc_heap_init() {
    if (sf_mem_grow() == NULL) {
        sf_errno = ENOMEM;
        return;
    }

    // starting at 48 bytes in heap, insert prologue block into heap
    char* start_addr = (char*) sf_mem_start();
    start_addr += 48;
    sf_block* prologue_ptr = (sf_block*) start_addr;
    prologue_ptr->header = 64; // block_size of prologue header = 64
    prologue_ptr->header |= THIS_BLOCK_ALLOCATED; // set allocated bit of prologue header to 1
    prologue_ptr->header |= PREV_BLOCK_ALLOCATED; // set prev allocated bit of prologue header to 1

    // starting at address right after prologue payload, insert wilderness
    start_addr = (char*) sf_mem_start();
    start_addr += 48 + /* prologue prev footer*/ 8 + /* prologue block */ 56;
    sf_block* wilderness_ptr = (sf_block*) start_addr;
    wilderness_ptr->header = PAGE_SZ - 128;
    wilderness_ptr->prev_footer = prologue_ptr->header; // set prev_footer of wilderness block to prologue header
    wilderness_ptr->header |= PREV_BLOCK_ALLOCATED; // set prev allocated bit of wilderness header to 1

    // starting at end of heap - 2 rows, insert epilogue block into heap
    char* end_addr = (char*) sf_mem_end();
    end_addr -= 16; // accounts for prev footer and epilogue header
    sf_block* epilogue_ptr = (sf_block*) end_addr;
    epilogue_ptr->header = 0; // block_size of epilogue header = 0
    epilogue_ptr->prev_footer = wilderness_ptr->header;
    epilogue_ptr->header |= THIS_BLOCK_ALLOCATED; // set allocated bit of epilogue header to 1

    sf_free_list_heads[NUM_FREE_LISTS-1].body.links.next = wilderness_ptr; // the last size class points to wilderness block
    sf_free_list_heads[NUM_FREE_LISTS-1].body.links.prev = wilderness_ptr;
    wilderness_ptr->body.links.next = &sf_free_list_heads[NUM_FREE_LISTS-1];
    wilderness_ptr->body.links.prev = &sf_free_list_heads[NUM_FREE_LISTS-1];
}

// Initializes the free lists links
void sf_malloc_free_list_init() {
    // free_list is empty, so next and prev pointers point to the sentinel
    for (int i = 0; i < NUM_FREE_LISTS; i++) {
        sf_free_list_heads[i].body.links.next = &sf_free_list_heads[i];
        sf_free_list_heads[i].body.links.prev = &sf_free_list_heads[i];
    }
}

// @returns index in Fibonacci sequence
int get_Fibonacci_index(size_t size) {
    int a = 0;
    int b = 1;
    int index = -1;
    int sum;
    do {
        sum = a + b;
        a = b;
        b = sum;
        index++;
    } while (sum < (size/MINIMUM_BLOCK_SIZE));
    if (index > NUM_FREE_LISTS-2) { // second to last size class case
        index = NUM_FREE_LISTS-2;
    }
    return index;
}

sf_block* traverse_free_list_heads(size_t size) {
    int index = get_Fibonacci_index(size);
    sf_block* current_head;
    sf_block* target_block;
    for (int i = index; i < NUM_FREE_LISTS; i++) { // loop through each head of free_list starting at the minimum size class
        current_head = &sf_free_list_heads[i];
        target_block = search_free_list(current_head, size);
        if (target_block != NULL) {
            return target_block;
        }
    }
    return NULL;
}

// @returns pointer to free block big enough for allocation
sf_block* search_free_list(sf_block* free_list_ptr, size_t size) {
    sf_block* head = free_list_ptr;
    if (head->body.links.next == head) { // list is empty
        return NULL;
    }
    sf_block* target_block = head;
    int block_size = 0;
    do {
        target_block = target_block->body.links.next; // iterate through free_list
        block_size = target_block->header & BLOCK_SIZE_MASK;
        if (block_size >= size) {
            return target_block;
        }
    }
    while (target_block != head);
    return NULL;
}

// @returns pointer to new wilderness block or coalesced wilderness block from expanded heap
sf_block* expand_heap() {
    char* end_addr = (char*) sf_mem_end();
    end_addr -= 16;
    sf_block* old_epilogue_ptr = (sf_block*) end_addr;
    size_t last_block_size = old_epilogue_ptr->prev_footer & BLOCK_SIZE_MASK;
    end_addr -= last_block_size; // end_addr = address of last block before epilogue
    sf_block* last_block_ptr = (sf_block*) end_addr;
    sf_block* new_page = sf_mem_grow(); // new_page points to new wilderness block
    if (new_page == NULL) {
        sf_errno = ENOMEM;
        return NULL;
    }
    // CODE TO MOVE EPILOGUE BLOCK
    // old epilogue header becomes header to new wilderness block
    old_epilogue_ptr->header = PAGE_SZ; // size of new wilderness block includes 8 bytes from current page but excludes epilogue at next page
    sf_block* coalesced_block = old_epilogue_ptr;
    sf_block* wilderness_sentinel = &sf_free_list_heads[NUM_FREE_LISTS-1];
    if ((old_epilogue_ptr->prev_footer & THIS_BLOCK_ALLOCATED) == 1) { // preexisting wilderness block was allocated
        old_epilogue_ptr->header |= PREV_BLOCK_ALLOCATED;
        insert_free_block_into_list(wilderness_sentinel, old_epilogue_ptr);
    }
    else {
        insert_free_block_into_list(wilderness_sentinel, old_epilogue_ptr);
        coalesced_block = coalesce(last_block_ptr, old_epilogue_ptr);
    }
    new_page->header = PAGE_SZ - 16;
    // starting at new end of heap - 2 rows, insert epilogue block into heap
    end_addr = (char*) sf_mem_end();
    end_addr -= 16;
    sf_block* new_epilogue_ptr = (sf_block*) end_addr;
    new_epilogue_ptr->header = 0; // block_size of epilogue header = 0
    new_epilogue_ptr->prev_footer = coalesced_block->header;
    new_epilogue_ptr->header |= THIS_BLOCK_ALLOCATED; // set allocated bit of epilogue header to 1
    return coalesced_block;
}

// @returns pointer to allocated block
sf_block* split(sf_block* target_block, size_t size) {
    int is_wilderness = 0;
    sf_block* sentinel = &sf_free_list_heads[NUM_FREE_LISTS-1];
    if (target_block->body.links.next == sentinel) { // check if target_block is wilderness
        is_wilderness = 1;
    }
    size_t upper_half_size = (target_block->header&BLOCK_SIZE_MASK) - size; // keep this value for use later
    if (upper_half_size == 0) {
        return target_block;
    }
    int this_alloc = target_block->header & THIS_BLOCK_ALLOCATED;
    target_block->header = size; // allocated block header = size
    target_block->header |= THIS_BLOCK_ALLOCATED; // allocated block header's allocated bit must be set
    if ((target_block->prev_footer & THIS_BLOCK_ALLOCATED) == 1) { // previous block was allocated
        target_block->header |= PREV_BLOCK_ALLOCATED;
    }
    if (this_alloc == 0) {
        remove_free_block_from_list(target_block);
    }
    char* target_block_addr = (char*) target_block; // casting to char* for pointer arithmetic
    target_block_addr += size;
    sf_block* upper_half = (sf_block*) target_block_addr; // upper_half = remainder free block
    upper_half->prev_footer = target_block->header;
    upper_half->header = upper_half_size;
    upper_half->header |= PREV_BLOCK_ALLOCATED; // previous block is allocated
    if (is_wilderness == 0) {
        int index = get_Fibonacci_index(upper_half_size);
        sentinel = &sf_free_list_heads[index];
    }
    insert_free_block_into_list(sentinel, upper_half);
    // CODE FOR SETTING PREV FOOTER OF NEXT BLOCK
    char* upper_half_addr = (char*) upper_half;
    upper_half_addr += upper_half_size;
    sf_block* next_block = (sf_block*) upper_half_addr;
    next_block->prev_footer = upper_half->header;
    return target_block;
}

// @returns pointer to allocated block
sf_block* allocate_block(sf_block* target_block) {
    remove_free_block_from_list(target_block);
    target_block->header |= THIS_BLOCK_ALLOCATED; // target_block is allocated
    size_t target_block_size = target_block->header & BLOCK_SIZE_MASK;
    char* target_block_addr = (char*) target_block;
    target_block_addr += target_block_size;
    sf_block* next_block = (sf_block*) target_block_addr;
    next_block->prev_footer = target_block->header;
    return target_block;
}


// @params 2 adjacent free blocks
// @returns pointer to coalesced block
sf_block* coalesce(sf_block* free1, sf_block* free2) {
    // check if either free block belongs in wilderness size class
    int is_wilderness = 0;
    sf_block* sentinel = &sf_free_list_heads[NUM_FREE_LISTS-1];
    if (free1->body.links.next == sentinel) {
        is_wilderness = 1;
    }
    if (free2->body.links.next == sentinel) {
        is_wilderness = 1;
    }
    // remove blocks from free list
    remove_free_block_from_list(free1);
    remove_free_block_from_list(free2);
    size_t size1 = free1->header & BLOCK_SIZE_MASK;
    size_t size2 = free2->header & BLOCK_SIZE_MASK;
    size_t new_size = size1 + size2;
    int prev_alloc = free1->header & PREV_BLOCK_ALLOCATED;
    free1->header = new_size; // free1 now points to the coalesced block
    if (prev_alloc == 2) { // if block before free1 was allocated, free1's new header's allocated bit is set
        free1->header |= PREV_BLOCK_ALLOCATED;
    }
    char* free2_addr = (char*) free2;
    free2_addr += size2; // free2_addr = address of block after free2
    sf_block* block3 = (sf_block*) free2_addr;
    block3->prev_footer = free1->header;
    // insert coalesced block into free list
    if (is_wilderness == 0) {
        int index = get_Fibonacci_index(new_size);
        sentinel = &sf_free_list_heads[index];
    }
    insert_free_block_into_list(sentinel, free1);
    return free1;
}

// @params pointer to free block to be removed from free list
void remove_free_block_from_list(sf_block* free_block_ptr) {
    sf_block* prev = free_block_ptr->body.links.prev;
    sf_block* next = free_block_ptr->body.links.next;
    prev->body.links.next = next; // prev->xxblockxx->next
    next->body.links.prev = prev; // prev-<xxblockxx<-next
    free_block_ptr->body.links.prev = NULL;
    free_block_ptr->body.links.next = NULL;
}

// @params sentinel node, free block to be inserted after sentinel
void insert_free_block_into_list(sf_block* sentinel, sf_block* free_block_ptr) {
    sf_block* first_block = sentinel->body.links.next;
    sentinel->body.links.next = free_block_ptr; // sentinel->free_block_ptr->first_block
    first_block->body.links.prev = free_block_ptr; // sentinel->free_block_ptr->first_block
    free_block_ptr->body.links.prev = sentinel;
    free_block_ptr->body.links.next = first_block;
}

// @returns pointer to allocated block [SIMILAR TO split(), but frees lower_half and allocates upper_half]
sf_block* split_alt(sf_block* target_block, size_t size) {
    int is_wilderness = 0;
    sf_block* sentinel = &sf_free_list_heads[NUM_FREE_LISTS-1];
    if (target_block->body.links.next == sentinel) { // check if target_block is wilderness
        is_wilderness = 1;
    }
    size_t upper_half_size = (target_block->header&BLOCK_SIZE_MASK) - size; // keep this value for use later
    if (upper_half_size == 0) {
        return target_block;
    }
    target_block->header = size; // free block header = size
    if ((target_block->prev_footer & THIS_BLOCK_ALLOCATED) == 1) { // previous block was allocated
        target_block->header |= PREV_BLOCK_ALLOCATED;
    }
    if (is_wilderness == 0) {
        int index = get_Fibonacci_index(size);
        sentinel = &sf_free_list_heads[index];
    }
    insert_free_block_into_list(sentinel, target_block);
    char* target_block_addr = (char*) target_block; // casting to char* for pointer arithmetic
    target_block_addr += size;
    sf_block* upper_half = (sf_block*) target_block_addr; // upper_half = remainder allocated block
    upper_half->prev_footer = target_block->header;
    upper_half->header = upper_half_size;
    upper_half->header |= THIS_BLOCK_ALLOCATED; // this block is allocated
    return upper_half;
}