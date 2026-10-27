#include "generated.h"

#include <inttypes.h>
#include <stdint.h>
#include <stdio.h>

int main(void)
{
    /* L1 is exponential; native acceptance executes only inputs 0..30. */
    for (uint64_t input = UINT64_C(0); input <= UINT64_C(30); ++input) {
        if (printf("%" PRIu64 " %" PRIu64 "\n", input, fib_l1(input)) < 0) {
            return 1;
        }
    }
    return 0;
}
