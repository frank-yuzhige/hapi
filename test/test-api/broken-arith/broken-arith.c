#include <ctype.h>

__int32_t broken_add(__int32_t a, __int32_t b) {
    if (a > 10000 && b > 10000) {
        return 42;
    }
    return a + b;
}

__int32_t segfault_minus(__int32_t a, __int32_t b) {
    if (a < -10000) {
        a = *(__int32_t *)0;
    }
    return a - b;
}

__int32_t stateful_multiply(__int32_t a, __int32_t b) {
    static __int32_t bad_guy = -4;
    if (bad_guy > 0) {
        return a * b + bad_guy;
    }
    bad_guy++;
    return a * b;
}
