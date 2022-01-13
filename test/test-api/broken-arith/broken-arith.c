#include <ctype.h>
#include <stdlib.h>
#include <stdio.h>


/*
 * No crash, yet return value is wrong under certain inputs.
 */
__int32_t broken_add(__int32_t a, __int32_t b) {
    if (a + b > 10000) {
        return 42;
    }
    return a + b;
}

/*
 * Crash under certain inputs.
 */
__int32_t segfault_minus(__int32_t a, __int32_t b) {
    if (a < -10000) {
        *(int *)0 = 1;   // Segfault
    }
    return (__int32_t) (a - b);
}

/*
 * Good on first 4 calls, then it corrupts.
 * Might be a challenge to tackle, as the lib's state will not recover.
 */
__int32_t stateful_multiply(__int32_t a, __int32_t b) {
    static __int32_t bad_guy = -4;
    bad_guy++;
    if (bad_guy > 0) {
        return a * b + bad_guy;
    }
    return a * b;
}

/*
 * Limited input domain results exit failure, but does not imply bug.
 * Meanwhile contains a bug on certain input.
 * - LibSpec needs to describe input domain as well.
 */
__int32_t limited_input_range_negate(__int32_t a) {
    if (a > 65535 || a < -42) {
        fprintf(stderr, "My negate function only allows input domain to be [-42, 65535], sad!\n");
        exit(EXIT_FAILURE);
    }
    if (a == 6666) {
        *(int *)NULL = 1;   // Segfault
    }
    return -a;
}
