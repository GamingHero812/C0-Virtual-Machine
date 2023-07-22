/**************************************************************************/
/*              COPYRIGHT Carnegie Mellon University 2022                 */
/* Do not post this file or any derivative on a public site or repository */
/**************************************************************************/
#include <assert.h>
#include <stdio.h>
#include <limits.h>
#include <stdlib.h>

#include "lib/xalloc.h"
#include "lib/stack.h"
#include "lib/contracts.h"
#include "lib/c0v_stack.h"
#include "lib/c0vm.h"
#include "lib/c0vm_c0ffi.h"
#include "lib/c0vm_abort.h"

/* call stack frames */
typedef struct frame_info frame;
struct frame_info {
  c0v_stack_t S;  /* Operand stack of C0 values */
  ubyte *P;        /* Function body */
  size_t pc;       /* Program counter */
  c0_value *V;     /* The local variables */
};

int execute(struct bc0_file *bc0) {
  REQUIRES(bc0 != NULL);

  /* Variables */
  c0v_stack_t S = c0v_stack_new(); /* Operand stack of C0 values */
  ubyte *P = bc0->function_pool[0].code;      /* Array of bytes that make up the current function */
  size_t pc = 0;     /* Current location within the current byte array P */
  c0_value *V = xcalloc((bc0->function_pool[0].num_vars), sizeof(c0_value));   /* Local variables (you won't need this till Task 2) */
  (void) V;      // silences compilation errors about V being currently unused

  /* The call stack, a generic stack that should contain pointers to frames */
  /* You won't need this until you implement functions. */
  gstack_t callStack = stack_new();
  // (void) callStack; // silences compilation errors about callStack being currently unused

  while (true) {

#ifdef DEBUG
    /* You can add extra debugging information here */
    fprintf(stderr, "Opcode %x -- Stack size: %zu -- PC: %zu\n",
            P[pc], c0v_stack_size(S), pc);
#endif

    switch (P[pc]) {

    /* Additional stack operation: */

    case POP: {
      pc++;
      c0v_pop(S);
      break;
    }

    case DUP: {
      pc++;
      c0_value v = c0v_pop(S);
      c0v_push(S,v);
      c0v_push(S,v);
      break;
    }

    case SWAP: {
      pc++;
      c0_value y = c0v_pop(S);
      c0_value x = c0v_pop(S);
      c0v_push(S, y);
      c0v_push(S, x);
      break;
    }


    /* Returning from a function.
     * This currently has a memory leak! You will need to make a slight
     * change for the initial tasks to avoid leaking memory.  You will
     * need to revise it further when you write INVOKESTATIC. */

    case RETURN: {
      c0_value retval = c0v_pop(S);
      assert(c0v_stack_empty(S));
// Another way to print only in DEBUG mode
//IF_DEBUG(fprintf(stderr, "Returning %d from execute()\n", val2int(retval)));
      // Free everything before returning from the execute function!
      c0v_stack_free(S); 
      free(V); 
      if (stack_empty(callStack))
      {
        stack_free(callStack, NULL);
        return val2int(retval);
      }
      else
      {
        frame *f = (frame*)pop(callStack);
        S = f->S;
        P = f->P;
        V = f->V;
        pc = f->pc;
        c0v_push(S, retval);
        free(f);
        break; 
      }
    }


    /* Arithmetic and Logical operations */

    case IADD: {
      pc++;
      int y = val2int(c0v_pop(S));
      int x = val2int(c0v_pop(S));
      c0v_push(S, int2val(x+y));
      break;
    }

    case ISUB: {
      pc++;
      int y = val2int(c0v_pop(S));
      int x = val2int(c0v_pop(S));
      c0v_push(S, int2val(x-y));
      break;
    }

    case IMUL: {
      pc++;
      int y = val2int(c0v_pop(S));
      int x = val2int(c0v_pop(S));
      c0v_push(S, int2val(x*y));
      break;
    }

    case IDIV: {
      pc++;
      int y = val2int(c0v_pop(S));
      if (y == 0)
        c0_arith_error("Division by 0");
      else{
        int x = val2int(c0v_pop(S));
        if (x == INT_MIN && y == -1)
        {
          c0_arith_error("Division overflow");
        }
        else
          c0v_push(S, int2val(x/y));
      }
      break;
    }

    case IREM: {
      pc++;
      int y = val2int(c0v_pop(S));
      if (y == 0)
        c0_arith_error("Mod by 0");
      else{
        int x = val2int(c0v_pop(S));
        if (x == INT_MIN && y == -1)
        {
          c0_arith_error("Modular overflow");
        }
        else
          c0v_push(S, int2val(x%y));
      }
      break;
    }

    case IAND: {
      pc++;
      int y = val2int(c0v_pop(S));
      int x = val2int(c0v_pop(S));
      c0v_push(S, int2val(x&y));
      break;
    }

    case IOR: {
      pc++;
      int y = val2int(c0v_pop(S));
      int x = val2int(c0v_pop(S));
      c0v_push(S, int2val(x|y));
      break;
    }

    case IXOR: {
      pc++;
      int y = val2int(c0v_pop(S));
      int x = val2int(c0v_pop(S));
      c0v_push(S, int2val(x^y));
      break;
    }

    case ISHR: {
      pc++;
      int y = val2int(c0v_pop(S));
      int x = val2int(c0v_pop(S));
      if (!(y>=32 || y<0))
        c0v_push(S, int2val(x>>y));
      else  
        c0_arith_error("shifting by an invalid amount");
      break;
    }

    case ISHL: {
      pc++;
      int y = val2int(c0v_pop(S));
      int x = val2int(c0v_pop(S));
      if (!(y>=32 || y<0))
        c0v_push(S, int2val(x<<y));
      else  
        c0_arith_error("shifting by an invalid amount");
      break;
    }


    /* Pushing constants */

    case BIPUSH: {
      pc++;
      c0v_push(S, int2val((byte)P[pc]));
      pc++;
      break;
    }

    case ILDC: {
      pc++;
      uint32_t c1 = (uint32_t) P[pc];
      pc++;
      uint32_t c2 = (uint32_t) P[pc];
      pc++;
      int x = (int)(bc0->int_pool[c1<<8 | c2]);
      c0v_push(S, int2val(x));
      break;
    }

    case ALDC: {
      pc++;
	    uint32_t c1 = (uint32_t)P[pc];
      pc++;
      uint32_t c2 = (uint32_t)P[pc];
      pc++;
	    void* a = &((bc0->string_pool)[(c1<<8) | c2]);
	    c0v_push(S,ptr2val(a));	
	    break;
    }

    case ACONST_NULL: {
      pc++;
      c0v_push(S, ptr2val(NULL));
      break;
    }


    /* Operations on local variables */

    case VLOAD: {
      pc++;
      c0_value v = V[P[pc]];
      c0v_push(S, v);
      pc++;
      break;
    }

    case VSTORE: {
      pc++;
      c0_value v = c0v_pop(S);
      V[P[pc]] = v;
      pc++;
      break;
    }


    /* Assertions and errors */

    case ATHROW: {
      pc++;
      void *a = val2ptr(c0v_pop(S));
      c0_user_error((char*)a);
      break;
    }

    case ASSERT: {
      pc++;
      void *a = val2ptr(c0v_pop(S));
      int x = val2int(c0v_pop(S));
      if (x == 0)
      {
        c0_assertion_failure((char *)a);
      }
      break;
    }


    /* Control flow operations */

    case NOP:{
      pc++;
      break;
    }

    case IF_CMPEQ:{
      c0_value v2 = c0v_pop(S);
      c0_value v1 = c0v_pop(S);
      if (val_equal(v1, v2))
      {
        int o1 = (int)P[pc+1];
        int o2 = (int)P[pc+2];
        pc = pc + (int16_t)(o1<<8 | o2);
      } 
      else  
        pc += 3;
      break;
    }

    case IF_CMPNE: {
      c0_value v2 = c0v_pop(S);
      c0_value v1 = c0v_pop(S);
      if (!val_equal(v1, v2))
      {
        int o1 = (int)P[pc+1];
        int o2 = (int)P[pc+2];
        pc = pc + (int16_t)(o1<<8 | o2);
      } 
      else  
        pc += 3;
      break;
    }

    case IF_ICMPLT: {
      int y = val2int(c0v_pop(S));
      int x = val2int(c0v_pop(S));
      if (x<y)
      {
        int o1 = (int)P[pc+1];
        int o2 = (int)P[pc+2];
        pc = pc + (int16_t)(o1<<8 | o2);
      }
      else  
        pc += 3;
      break;
    }

    case IF_ICMPGE: {
      int y = val2int(c0v_pop(S));
      int x = val2int(c0v_pop(S));
      if (x>=y)
      {
        int o1 = (int)P[pc+1];
        int o2 = (int)P[pc+2];
        pc = pc + (int16_t)(o1<<8 | o2);
      }
      else  
        pc += 3;
      break;
    }

    case IF_ICMPGT: {
      int y = val2int(c0v_pop(S));
      int x = val2int(c0v_pop(S));
      if (x>y)
      {
        int o1 = (int)P[pc+1];
        int o2 = (int)P[pc+2];
        pc = pc + (int16_t)(o1<<8 | o2);
      }
      else  
        pc += 3;
      break;
    }

    case IF_ICMPLE: {
      int y = val2int(c0v_pop(S));
      int x = val2int(c0v_pop(S));
      if (x<=y)
      {
        int o1 = (int)P[pc+1];
        int o2 = (int)P[pc+2];
        pc = pc + (int16_t)(o1<<8 | o2);
      }
      else  
        pc += 3;
      break;
    }

    case GOTO: {
      int o1 = (int)P[pc+1];
      int o2 = (int)P[pc+2];
      pc = pc + (int16_t)(o1<<8 | o2);
      break;
    }


    /* Function call operations: */

    case INVOKESTATIC: {
      frame *f = xmalloc(sizeof(frame));
      f->S = S;
      f->P = P;
      f->V = V;
      push(callStack, (void*)f);
      pc++;
      uint16_t c1 = (uint16_t) P[pc];
      pc++;
      uint16_t c2 = (uint16_t) P[pc];
      uint16_t index = (c1<<8) | c2;
      f->pc = pc + 1;
      struct function_info g = bc0->function_pool[index];
      V = xmalloc(sizeof(c0_value)*g.num_vars);
      uint16_t num_args = g.num_args;
      while (num_args > 0)
      {
       c0_value v = c0v_pop(S);
       V[num_args-1] = v;
       num_args -= 1;
      }
      S = c0v_stack_new();
      P = g.code;
      pc = 0;
      break;
    }

    case INVOKENATIVE: {
      pc++;
      uint16_t c1 = (uint16_t) P[pc];
      pc++;
      uint16_t c2 = (uint16_t) P[pc];
      uint16_t index = (c1<<8) | c2;
      struct native_info n = bc0->native_pool[index];
      uint16_t args = n.num_args;
      c0_value *x = xmalloc(sizeof(c0_value)*n.num_args);
      while (args>0)
      {
        c0_value v = c0v_pop(S);
        x[args-1] = v;
        args -= 1;
      }
      native_fn *nat = native_function_table[n.function_table_index];
      c0_value final = (*nat)(x);
      c0v_push(S, final);
      free(x);
      pc++;
      break;
    }


    /* Memory allocation and access operations: */

    case NEW: 
    {
      pc++;
      uint8_t s = P[pc];
      char* new_arr = xcalloc(sizeof(char), s);
      pc++;
      c0v_push(S, ptr2val((void*)new_arr));
      break;
    }

    case IMLOAD:
    {
      pc++;
      void* check = (void*) val2ptr(c0v_pop(S));
      if (check == NULL)
        c0_memory_error("NULL pointer");
      int jawn = *(int*)check;
      c0v_push(S, int2val(jawn));
      break;
    }

    case IMSTORE:
    {
      pc++;
      int w = val2int(c0v_pop(S));
      void* a = (void*)val2ptr(c0v_pop(S));
      if (a == NULL)
        c0_memory_error("NULL pointer");
      *((int*)a) = w;
      break;
    }

    case AMLOAD:
    {
      pc++;
      void** a = val2ptr(c0v_pop(S));
      if (a == NULL)
        c0_memory_error("NULL pointer");
      c0v_push(S, ptr2val(*a));
      break;
    }

    case AMSTORE:
    {
      pc++;
      void* b = val2ptr(c0v_pop(S));
      void** a = val2ptr(c0v_pop(S));
      if (a == NULL)
        c0_memory_error("NULL pointer");
      *a = b;
      break;
    }

    case CMLOAD:
    {
      pc++;
      void* a = val2ptr(c0v_pop(S));
      if (a == NULL)
        c0_memory_error("NULL pointer");
      int w = *(int*)a;
      c0v_push(S, int2val(w));
      break;
    }

    case CMSTORE:
    {
      pc++;
      int x = val2int(c0v_pop(S));
      void* a = val2ptr(c0v_pop(S));
      if (a == NULL)
        c0_memory_error("NULL pointer");
      *((char*) a) = x & 0x7F;
      break;
    }

    case AADDF:
    {
      pc++;
      uint8_t f = P[pc];
      pc++;
      void* a = val2ptr(c0v_pop(S));
      if (a == NULL)
        c0_memory_error("NULL pointer");
      void* new = (void*)((char*)a + f);
      c0v_push(S, ptr2val(new));
      break;
    }


    /* Array operations: */

    case NEWARRAY:
    {
      pc++;
      uint8_t s = P[pc];
      int n = val2int(c0v_pop(S));
      if (n < 0)
        c0_memory_error("n is negative");
      c0_array* new = xcalloc(sizeof(c0_array), 1);
      new->count = n+1; //changed from n+1
      new->elt_size = s;
      char* arr = xcalloc((int)P[pc]*(n+1), sizeof(char));
      new->elems = (void*)arr;
      c0v_push(S, ptr2val((void*)new));
      pc++;
      break;
    }

    case ARRAYLENGTH:
    {
      pc++;
      void* a = val2ptr(c0v_pop(S));
      int count = ((c0_array*)a)->count;
      c0v_push(S, int2val(count));
      break;
    }

    case AADDS:
    {
      pc++;
      int x = val2int(c0v_pop(S));
      void* a = (void*)val2ptr(c0v_pop(S));
      c0_array* arr = (c0_array*)a;
      if (a == NULL)
        c0_memory_error("NULL pointer");
      int count = arr->count;
      if (x<0 || x>=count)
        c0_memory_error("out of bounds");
      int s = x*arr->elt_size;
      c0v_push(S, ptr2val((void*)((char*)arr->elems + s)));
      break;
    }


    /* BONUS -- C1 operations */

    case CHECKTAG:

    case HASTAG:

    case ADDTAG:

    case ADDROF_STATIC:

    case ADDROF_NATIVE:

    case INVOKEDYNAMIC:

    default:
      fprintf(stderr, "invalid opcode: 0x%02x\n", P[pc]);
      abort();
    }
  }

  /* cannot get here from infinite loop */
  assert(false);
}
