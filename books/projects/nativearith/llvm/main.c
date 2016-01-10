#include <stdio.h>
#include <stdint.h>

extern int64_t i64eql(int64_t a, int64_t b);
extern int64_t i64neq(int64_t a, int64_t b);
extern int64_t i64sle(int64_t a, int64_t b);
extern int64_t i64slt(int64_t a, int64_t b);
extern int64_t i64sge(int64_t a, int64_t b);
extern int64_t i64sgt(int64_t a, int64_t b);
extern int64_t i64bitand(int64_t a, int64_t b);
extern int64_t i64bitor(int64_t a, int64_t b);
extern int64_t i64bitxor(int64_t a, int64_t b);
extern int64_t i64plus(int64_t a, int64_t b);
extern int64_t i64minus(int64_t a, int64_t b);
extern int64_t i64times(int64_t a, int64_t b);
extern int64_t i64sdiv(int64_t a, int64_t b);


int main()
{
    int64_t a = INT64_MIN;
    int64_t b = -1;
    int64_t ans = i64sdiv(a,b);

    printf("a is %ld\n", a);
    printf("b is %ld\n", b);
    printf("answer is %ld\n", ans);
    return 0;
}
