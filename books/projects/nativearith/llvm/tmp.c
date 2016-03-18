#include <stdio.h>
#include <stdlib.h>
#include <inttypes.h>

extern void foo(int64_t* in, int64_t* out);

int main()
{
    int64_t in [5];
    int64_t out [5];

    in[0] = 3;
    in[1] = 4;
    in[2] = 5;
    foo(in, out);

    printf("out[0] = %" PRId64 "\n", out[0]);
    printf("out[1] = %" PRId64 "\n", out[1]);
    return 0;
}
