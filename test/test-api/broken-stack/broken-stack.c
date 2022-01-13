#include <stdlib.h>
#include <stdio.h>

#define LIMIT 32

/**
 * @brief To represent C struct in Haskell
 */
typedef struct stack_t {
    int array[LIMIT];
    int top;
} stack_t;

stack_t *create_stack() {
    stack_t *stack = (stack_t *)malloc(sizeof(stack_t));
    stack->top = 0;
    return stack;
}

void push_stack(stack_t *stack, int elem) {
    stack->array[stack->top++] = elem;
}

void pop_stack(stack_t *stack) {
    stack->top--;
}

int peek_stack(stack_t *stack) {
    return stack->array[stack->top - 1];
}

int get_stack_size(stack_t *stack) {
    return stack->top;
}
