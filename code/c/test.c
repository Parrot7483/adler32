#include "adler32.h"
#include <stdint.h>
#include <stdio.h>
#include <string.h>
#include <assert.h>

const char *GREEN = "\033[32m";
const char *RESET = "\033[0m";

int32_t main(void)
{
    char *input1 = "Wikipedia";
    assert(adler32(input1, strlen(input1)) == 300286872);

    char *input2 = "Algorithms";
    assert(adler32(input2, strlen(input2)) == 363791387);

    char *input3 = "Hello, World!";
    assert(adler32(input3, strlen(input3)) == 530449514);

    char input4[] = {4, 1, 6, 3, 10};
    assert(adler32(input4, 5) == 4128793);

    char input5[] = {};
    assert(adler32(input5, 0) == 1);

    char input6[] = {1};
    assert(adler32(input6, 1) == 131074);

    printf("%sAll tests passed!\n%s", GREEN, RESET);
    return 0;
}