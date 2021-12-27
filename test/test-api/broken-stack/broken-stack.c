typedef struct stack_t {
    int top;
    int array[4096];
} stack_t;

static const int LIMIT = 1024;

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

void get_stack_size(stack_t *stack) {
    return stack->top;
}
