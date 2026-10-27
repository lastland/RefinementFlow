#include "generated.h"

#include <inttypes.h>
#include <stdint.h>
#include <stdio.h>

/* Deliberate unsigned underflow belongs only in the ordinary build. */
int main(void)
{
    const uint64_t inputs[] = {UINT64_C(0), UINT64_C(1), UINT64_C(2), UINT64_MAX};
    for (size_t index = 0; index < sizeof inputs / sizeof inputs[0]; ++index) {
        const uint64_t input = inputs[index];
        if (printf("%" PRIu64 " %" PRIu64 " %" PRIu64 "\n",
                   input, costSubFixture(input), pureSubFixture(input)) < 0) {
            return 1;
        }
    }
    return 0;
}
