#include <ctype.h>
#include <stdlib.h>
#include <stdio.h>

char *broken_str(__int32_t a) {
    char *buf = (char *)malloc(sizeof(char) * 6); // Not enough, cause buffer overflow
    sprintf(buf, "%d", a);
    return buf;
}
