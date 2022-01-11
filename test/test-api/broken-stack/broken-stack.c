static const int LIMIT = 1024;

typedef struct stack_t {
    int top;
    int array[LIMIT];
} stack_t;

stack_t *create_stack() {
    stack_t *stack = malloc(sizeof(stack_t));
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

void get_stack_size(stack_t *stack) {
    return stack->top;
}
