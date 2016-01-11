#include "ops.h"
#include <stdio.h>

int main()
{
    int64_t a = INT64_MIN;
    int64_t b = -1;
    int64_t ans = narith_i64sdiv(a,b);

    printf("a is %ld\n", a);
    printf("b is %ld\n", b);
    printf("answer is %ld\n", ans);
    return 0;
}

