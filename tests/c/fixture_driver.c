#include "generated.h"

#include <inttypes.h>
#include <stdint.h>
#include <stdio.h>

int main(void)
{
    for (uint64_t input = UINT64_C(0); input <= UINT64_C(91); ++input) {
        if (printf("%" PRIu64 " %" PRIu64 " %" PRIu64 " %" PRIu64
                   " %" PRIu64 " %" PRIu64 " %" PRIu64 "\n",
                   input, stateSwapFixture(input), directArithmeticFixture(input),
                   sequencingFixture(input), conditionalFixture(input),
                   branchInitializationFixture(input), recursiveCountdownFixture(input)) < 0) {
            return 1;
        }
    }
    return 0;
}
