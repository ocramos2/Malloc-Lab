/* 
 * mm-implicit.c -  Simple allocator based on implicit free SEG_LISTS, 
 *                  first fit placement, and boundary tag coalescing. 
 *
 * Each block has header and footer of the form:
 * 
 *      31                     3  2  1  0 
 *      -----------------------------------
 *     | s  s  s  s  ... s  s  s  0  0  a/f
 *      ----------------------------------- 
 * 
 * where s are the meaningful size bits and a/f is set 
 * iff the block is allocated. The list has the following form:
 *
 * begin                                                          end
 * heap                                                           heap  
 *  -----------------------------------------------------------------   
 * |  pad   | hdr(8:a) | ftr(8:a) | zero or more usr blks | hdr(8:a) |
 *  -----------------------------------------------------------------
 *          |       prologue      |                       | epilogue |
 *          |         block       |                       | block    |
 *
 * The allocated prologue and epilogue blocks are overhead that
 * eliminate edge conditions during coalescing.
 */
#include <stdio.h>	
#include <stdlib.h>	
#include <unistd.h>	
#include <memory.h>	
#include "mm.h"	
#include "memlib.h"

/*********************************************************
 * NOTE TO STUDENTS: Before you do anything else, please
 * provide your team information in the following struct.
 ********************************************************/
team_t team = {
  /* Team name */
  "Change Name",
  /* First member's full name */
  "Change Name",
  /* First member's email address */
  "Change Name",
  /* Second member's full name (leave blank if none) */
  "",
  /* Second member's email address (leave blank if none) */
  ""
};

/*
 * Sources: References to various pages on Github and StackOverflow, and the course textbook.
 */

/////////////////////////////////////////////////////////////////////////////
// Constants and macros
//
// These correspond to the material in Figure 9.43 of the text
// The macros have been turned into C++ inline functions to
// make debugging code easier.
//
/////////////////////////////////////////////////////////////////////////////
#define WSIZE     4       /* word size (bytes) */  
#define DSIZE     8       /* doubleword size (bytes) */
#define CHUNKSIZE (1<<12) /* initial heap size (bytes) */
#define OVERHEAD  16      /* overhead of header and footer (bytes) */

#define SEG_LISTS     20      /* Number of segregated SEG_LISTS */
#define REALLOC_BUFFER  (1<<7)    /* Reallocation REALLOC_BUFFER */

#define MAX(x, y) ((x) > (y) ? (x) : (y)) /* Maximum of two numbers */
#define MIN(x, y) ((x) < (y) ? (x) : (y)) /* Minimum of two numbers */

/* Pack size and allocation bit into a word */
#define PACK(size, alloc) ((size) | (alloc))

/* Read and write a word at address p */
#define GET(p) (*(unsigned int *)(p))

/* Preserve reallocation bit */
#define PUT(p, val) (*(unsigned int *)(p) = (val) | GET_TAG(p))

/* Clear reallocation bit */
#define CLEAR_PUT(p, val) (*(unsigned int *)(p) = (val))

/* Store preceding or succeeding pointer for free blocks */
#define SET_PTR(p, ptr) (*(unsigned int *)(p) = (unsigned int)(ptr))

/* Adjust the reallocation tag */
#define SET_TAG(p) (*(unsigned int *)(p) = GET(p) | 0x2)
#define UNSET_TAG(p) (*(unsigned int *)(p) = GET(p) & ~0x2)

/* Read the size and allocation bit from address p */
#define GET_SIZE(p) (GET(p) & ~0x7)
#define GET_ALLOC(p) (GET(p) & 0x1)
#define GET_TAG(p) (GET(p) & 0x2)

/* Address of block's header and footer */
#define HEAD(ptr) ((char *)(ptr) - WSIZE)
#define FOOT(ptr) ((char *)(ptr) + GET_SIZE(HEAD(ptr)) - DSIZE)

/* Address of next and previous blocks */
#define NEXT(ptr) ((char *)(ptr) + GET_SIZE((char *)(ptr) - WSIZE))
#define PREV(ptr) ((char *)(ptr) - GET_SIZE((char *)(ptr) - DSIZE))

/* Address of free block's preceding and succeeding entries */
#define PRECEDE_PTR(ptr) ((char *)(ptr))
#define SUCCEED_PTR(ptr) ((char *)(ptr) + WSIZE)

/* Address of free block's preceding and succeeding on segregated list */
#define PRECEDE(ptr) (*(char **)(ptr))
#define SUCCEED(ptr) (*(char **)(SUCCEED_PTR(ptr)))

/* Check for alignment */
#define ALIGN(p) (((u_int32_t)(p) + 7) & ~(0x7))

/* Settings for mm_check */
#define CHECK         0 
#define CHECK_MALLOC  1 
#define CHECK_FREE    1 
#define CHECK_REALLOC 1 
#define DISPLAY_BLOCK 1 
#define DISPLAY_LIST  1 
#define PAUSE         1 

/* Line offset for referencing trace files */
#define LINE_OFFSET   4

/* Global variables */
void *FREE_SEG_LISTS[SEG_LISTS]; /* Array of pointers to segregated free SEG_LISTS */
char *prologue_block;    /* Pointer to prologue block */

/* Function prototypes */
static void *incr_heap(u_int32_t size);
static void *merge(void *ptr);
static void place(void *ptr, u_int32_t size_x);
static void insert_node(void *ptr, u_int32_t size);
static void remove_node(void *ptr);

/* Initialize the malloc package, and construct prologue and epilogue blocks */
int mm_init(void)
{
  int list;         /* List counter */
  char *heap_begin; /* Pointer to beginning of heap */

  /* Initialize array of pointers to segregated free SEG_LISTS */
  for (list = 0; list < SEG_LISTS; list++) {
    FREE_SEG_LISTS[list] = NULL;
  }

  /* Allocate memory for the initial empty heap */
  if ((long)(heap_begin = mem_sbrk(4 * WSIZE)) == -1)
    return -1;
  
  CLEAR_PUT(heap_begin, 0);                            
  CLEAR_PUT(heap_begin + (1 * WSIZE), PACK(DSIZE, 1)); 
  CLEAR_PUT(heap_begin + (2 * WSIZE), PACK(DSIZE, 1)); 
  CLEAR_PUT(heap_begin + (3 * WSIZE), PACK(0, 1));     
  prologue_block = heap_begin + DSIZE;
  
  /* Extend empty heap */
  if (incr_heap(CHUNKSIZE) == NULL)
    return -1;
  
  return 0;
}

/* Place new block in a free block, but may need to extend heap. 
Pad blocks with boundary tags, and change lengths as needed. */
void *mm_malloc(u_int32_t size)
{
  u_int32_t size_x;      
  u_int32_t incr_size; 
  void *ptr = NULL; 
  int list = 0;      
  
  /* Filter invalid block size */
  if (size == 0)
    return NULL;
  
  /* Adjust block size for boundary tags and alignment */
  if (size <= DSIZE) {
    size_x = 2 * DSIZE;
  } else {
    size_x = DSIZE * ((size + (DSIZE) + (DSIZE - 1)) / DSIZE);
  }
  
  /* Select a free block of sufficient size from the segregated list */
  size = size_x;
  while (list < SEG_LISTS) {
    if ((list == SEG_LISTS - 1) || ((size <= 1) && (FREE_SEG_LISTS[list] != NULL))) {
      ptr = FREE_SEG_LISTS[list];

      while ((ptr != NULL)
        && ((size_x > GET_SIZE(HEAD(ptr))) || (GET_TAG(HEAD(ptr)))))
      {
        ptr = PRECEDE(ptr);
      }
        
      if (ptr != NULL)
        break;
    }
    
    size >>= 1;
    list++;
  }
  
  /* Extend the heap if free blocks are not large enough */
  if (ptr == NULL) {
    incr_size = MAX(size_x, CHUNKSIZE);
    if ((ptr = incr_heap(incr_size)) == NULL)
      return NULL;
  }
  
  /* Place block */
  place(ptr, size_x);
  
  /* Return pointer to new block */
  return ptr;
}

/* Free block by adding it to the appropriate list and coalescing it */
void mm_free(void *ptr)
{
  /* Size of block */
  u_int32_t size = GET_SIZE(HEAD(ptr));
  
  /* Adjust the reallocation tag on the next block */
  UNSET_TAG(HEAD(NEXT(ptr)));
  
  /* Adjust the allocation status in boundary tags */
  PUT(HEAD(ptr), PACK(size, 0));
  PUT(FOOT(ptr), PACK(size, 0));
  
  /* Insert new block into appropriate list */
  insert_node(ptr, size);
  
  /* Merge free block */
  merge(ptr);
  
  return;
}

/* Reallocate block in place and extend heap if needed. */
void *mm_realloc(void *ptr, u_int32_t size)
{
  void *new_ptr = ptr;    /* Pointer returned */
  u_int32_t new_size = size; /* Size of new block */
  int remainder;          /* Size of block needed */
  int incr_size;         /* Size of heap extension */
  int block_realloc_buffer;       /* Size of block REALLOC_BUFFER */
	
  /* Account for invalid block size */
  if (size == 0)
    return NULL;
  
  /* Block size should include boundary tag and alignment requirements */
  if (new_size <= DSIZE) {
    new_size = 2 * DSIZE;
  } else {
    new_size = DSIZE * ((new_size + (DSIZE) + (DSIZE - 1)) / DSIZE);
  }
  
  /* Add REALLOC_BUFFER to new size */
  new_size += REALLOC_BUFFER;
  
  /* Size of block REALLOC_BUFFER */
  block_realloc_buffer = GET_SIZE(HEAD(ptr)) - new_size;
  
  /* Allocate more space if REALLOC_BUFFER block is less than zero */
  if (block_realloc_buffer < 0) {
      
    /* Check if next block is free or if it is the last block */
    if (!GET_ALLOC(HEAD(NEXT(ptr))) || !GET_SIZE(HEAD(NEXT(ptr)))) {
      remainder = GET_SIZE(HEAD(ptr)) + GET_SIZE(HEAD(NEXT(ptr))) - new_size;
      if (remainder < 0) {
        incr_size = MAX(-remainder, CHUNKSIZE);
        if (incr_heap(incr_size) == NULL)
          return NULL;
        remainder += incr_size;
      }
      
      remove_node(NEXT(ptr));
      
      /* Do not split block */
      CLEAR_PUT(HEAD(ptr), PACK(new_size + remainder, 1)); /* Block header */
      CLEAR_PUT(FOOT(ptr), PACK(new_size + remainder, 1)); /* Block footer */
    } 
      else {
      new_ptr = mm_malloc(new_size - DSIZE);
      memmove(new_ptr, ptr, MIN(size, new_size));
      mm_free(ptr);
    }
    block_realloc_buffer = GET_SIZE(HEAD(new_ptr)) - new_size;
  }  

  /* Tag the next block if block overhead is less than two times the REALLOC_BUFFER */
  if (block_realloc_buffer < 2 * REALLOC_BUFFER)
    SET_TAG(HEAD(NEXT(new_ptr)));
  
  /* Return reallocated block */
  return new_ptr;
}

/* Use system call to extend heap, and insert the new free block into correct list */
static void *incr_heap(u_int32_t size)
{
  void *ptr;                   /* Pointer to newly allocated memory */
  u_int32_t words = size / WSIZE; /* Size of extension in words */
  u_int32_t size_x;                /* Adjusted size */
  
  /* Allocate even number of words for alignment purposes */
  size_x = (words % 2) ? (words + 1) * WSIZE : words * WSIZE;
  
  /* Increase heap size */
  if ((long)(ptr = mem_sbrk(size_x)) == -1)
    return NULL;
  
  /* Set header and footer */
  CLEAR_PUT(HEAD(ptr), PACK(size_x, 0));   /* Free block header */
  CLEAR_PUT(FOOT(ptr), PACK(size_x, 0));   /* Free block footer */
  CLEAR_PUT(HEAD(NEXT(ptr)), PACK(0, 1)); /* Last header */
  
  /* Insert new block into correct list */
  insert_node(ptr, size_x);
  
  /* merge if the previous block is free */
  return merge(ptr);
}

/* Insert a block pointer into a segregated list, sorted by pointer address in 
ascending order from 2^n to 2^(n+1)-1 */
static void insert_node(void *ptr, u_int32_t size) {
  int list = 0;
  void *search_ptr = ptr;
  void *insert_ptr = NULL;
  
  /* Select segregated list */
  while ((list < SEG_LISTS - 1) && (size > 1)) {
    size >>= 1;
    list++;
  }
  
  /* Select location on list to insert pointer */
  search_ptr = FREE_SEG_LISTS[list];
  while ((search_ptr != NULL) && (size > GET_SIZE(HEAD(search_ptr)))) {
    insert_ptr = search_ptr;
    search_ptr = PRECEDE(search_ptr);
  }
  
  /* Set preceding and succeeding */
  if (search_ptr != NULL) {
    if (insert_ptr != NULL) {
      SET_PTR(PRECEDE_PTR(ptr), search_ptr); 
      SET_PTR(SUCCEED_PTR(search_ptr), ptr);
      SET_PTR(SUCCEED_PTR(ptr), insert_ptr);
      SET_PTR(PRECEDE_PTR(insert_ptr), ptr);
    } else {
      SET_PTR(PRECEDE_PTR(ptr), search_ptr); 
      SET_PTR(SUCCEED_PTR(search_ptr), ptr);
      SET_PTR(SUCCEED_PTR(ptr), NULL);
      
      /* Add block to correct list */
      FREE_SEG_LISTS[list] = ptr;
    }
  } else {
    if (insert_ptr != NULL) {
      SET_PTR(PRECEDE_PTR(ptr), NULL);
      SET_PTR(SUCCEED_PTR(ptr), insert_ptr);
      SET_PTR(PRECEDE_PTR(insert_ptr), ptr);
    } else {
      SET_PTR(PRECEDE_PTR(ptr), NULL);
      SET_PTR(SUCCEED_PTR(ptr), NULL);
      
      /* Add block to correct list */
      FREE_SEG_LISTS[list] = ptr;
    }
  }

  return;
}

/* Remove free block pointer from a segregated list and reset the list head */
static void remove_node(void *ptr) {
  int list = 0;
  u_int32_t size = GET_SIZE(HEAD(ptr));
  
  /* Select segregated list */
  while ((list < SEG_LISTS - 1) && (size > 1)) {
    size >>= 1;
    list++;
  }
  
  if (PRECEDE(ptr) != NULL) {
    if (SUCCEED(ptr) != NULL) {
      SET_PTR(SUCCEED_PTR(PRECEDE(ptr)), SUCCEED(ptr));
      SET_PTR(PRECEDE_PTR(SUCCEED(ptr)), PRECEDE(ptr));
    } else {
      SET_PTR(SUCCEED_PTR(PRECEDE(ptr)), NULL);
      FREE_SEG_LISTS[list] = PRECEDE(ptr);
    }
  } else {
    if (SUCCEED(ptr) != NULL) {
      SET_PTR(PRECEDE_PTR(SUCCEED(ptr)), NULL);
    } else {
      FREE_SEG_LISTS[list] = NULL;
    }
  }
  
  return;
}

/* merge adjacent free blocks and sort new ones in correct list. */
static void *merge(void *ptr)
{
  u_int32_t prev_alloc = GET_ALLOC(HEAD(PREV(ptr)));
  u_int32_t next_alloc = GET_ALLOC(HEAD(NEXT(ptr)));
  u_int32_t size = GET_SIZE(HEAD(ptr));
  
  /* Return if previous and next blocks are allocated */
  if (prev_alloc && next_alloc) {
    return ptr;
  }
  
  /* Do not merge with previous block if tagged */
  if (GET_TAG(HEAD(PREV(ptr))))
    prev_alloc = 1;
  
  /* remove old blocks from list */
  remove_node(ptr);
  
  /* Find free blocks and merge */
  if (prev_alloc && !next_alloc) {
    remove_node(NEXT(ptr));
    size += GET_SIZE(HEAD(NEXT(ptr)));
    PUT(HEAD(ptr), PACK(size, 0));
    PUT(FOOT(ptr), PACK(size, 0));
  } else if (!prev_alloc && next_alloc) {
    remove_node(PREV(ptr));
    size += GET_SIZE(HEAD(PREV(ptr)));
    PUT(FOOT(ptr), PACK(size, 0));
    PUT(HEAD(PREV(ptr)), PACK(size, 0));
    ptr = PREV(ptr);
  } else {
    remove_node(PREV(ptr));
    remove_node(NEXT(ptr));
    size += GET_SIZE(HEAD(PREV(ptr))) + GET_SIZE(HEAD(NEXT(ptr)));
    PUT(HEAD(PREV(ptr)), PACK(size, 0));
    PUT(FOOT(NEXT(ptr)), PACK(size, 0));
    ptr = PREV(ptr);
  }
  
  /* Adjust segregated linked SEG_LISTS */
  insert_node(ptr, size);
  
  return ptr;
}

/* Set headers and footers for new blocks, split if space allows */
static void place(void *ptr, u_int32_t size_x)
{
  u_int32_t ptr_size = GET_SIZE(HEAD(ptr));
  u_int32_t remainder = ptr_size - size_x;
  
  /* remove block from list */
  remove_node(ptr);
  
  if (remainder >= OVERHEAD) {
    /* Split block */
    PUT(HEAD(ptr), PACK(size_x, 1)); /* Block header */
    PUT(FOOT(ptr), PACK(size_x, 1)); /* Block footer */
    CLEAR_PUT(HEAD(NEXT(ptr)), PACK(remainder, 0)); /* Next header */
    CLEAR_PUT(FOOT(NEXT(ptr)), PACK(remainder, 0)); /* Next footer */  
    insert_node(NEXT(ptr), remainder);
  } else {
    /* Do not split */
    PUT(HEAD(ptr), PACK(ptr_size, 1)); /* Block header */
    PUT(FOOT(ptr), PACK(ptr_size, 1)); /* Block footer */
  }
  return;
}
