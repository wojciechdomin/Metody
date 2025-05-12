(* # -*- mode: c; -*- *)

let with_runtime p =
  Printf.sprintf
  {|
#define STACK_SIZE 10000
#define HEAP_SIZE  1000000

#include <stdio.h>

int stack[STACK_SIZE];
int stack_ptr = -1; // top-most element on the stack

int heap[HEAP_SIZE];
int heap_ptr = 0; // first free cell

// heap objects
#define INT  0
#define BOOL 1
#define UNIT 2
#define PAIR 3

int compare(int ptr1, int ptr2){
	int tag1 = heap[ptr1-1];
	int tag2 = heap[ptr2-1];
	if(tag1 != tag2) return 0;
	switch(tag1){
		case INT:
		case BOOL:
		case UNIT:
		return (heap[ptr1] == heap[ptr2]);
		break;
		case PAIR:
			return compare(heap[ptr1], heap[ptr2]) && compare(heap[ptr1+1], heap[ptr2+1]);
		break;
	}
}

void print_heap_obj(int ptr)
{
  switch (heap[ptr-1])
  {
    case INT:
      printf("%%d", heap[ptr]);
      break;
    case BOOL:
      if (heap[ptr])
        printf("true");
      else
        printf("false");
      break;
    case UNIT:
      printf("()");
      break;
    case PAIR:
      printf("(");
      print_heap_obj(heap[ptr]);
      printf(",");
      print_heap_obj(heap[ptr+1]);
      printf(")");
  }
}

int main()
{
%s
  print_heap_obj(stack[0]);
  printf("\n");
  return 0;
}
  |}
  p
