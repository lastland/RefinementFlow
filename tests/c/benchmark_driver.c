#define _POSIX_C_SOURCE 200809L
#if defined(__APPLE__)
#define _DARWIN_C_SOURCE
#endif

#include "generated.h"
#include <errno.h>
#include <inttypes.h>
#include <stdbool.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

#if defined(CLOCK_MONOTONIC_RAW)
#define BENCHMARK_CLOCK CLOCK_MONOTONIC_RAW
#define BENCHMARK_CLOCK_NAME "CLOCK_MONOTONIC_RAW"
#else
#define BENCHMARK_CLOCK CLOCK_MONOTONIC
#define BENCHMARK_CLOCK_NAME "CLOCK_MONOTONIC"
#endif

enum { CONFIG_COUNT = 297, REPEATS = 11, FAST_WARMUP = 10000 };
#define MIN_BATCH_NS UINT64_C(12000000)
#define L1_SINGLE_CALL_CAP_NS UINT64_C(1000000000)

typedef uint64_t (*BenchmarkFunction)(uint64_t);
typedef struct {
    const char *target;
    BenchmarkFunction function;
    uint64_t input;
    uint64_t iterations;
    bool is_l1;
} Configuration;
typedef struct {
    uint64_t elapsed_ns;
    uint64_t checksum;
} Batch;

uint64_t benchmark_identity(uint64_t input);
static volatile uint64_t checksum_sink;

static void fail(const char *message)
{
    fprintf(stderr, "%s\n", message);
    exit(EXIT_FAILURE);
}

static uint64_t now_ns(void)
{
    struct timespec time;
    if (clock_gettime(BENCHMARK_CLOCK, &time) != 0) {
        perror("clock_gettime");
        exit(EXIT_FAILURE);
    }
    return (uint64_t)time.tv_sec * UINT64_C(1000000000)
           + (uint64_t)time.tv_nsec;
}

/* Keep one common indirect-call loop, including for the identity baseline.
 * Only this measurement boundary is noinline; generated targets are untouched.
 */
__attribute__((noinline))
static Batch benchmark_batch(BenchmarkFunction function, uint64_t input,
                             uint64_t iterations)
{
    uint64_t checksum = 0;
    const uint64_t start = now_ns();
    for (uint64_t i = 0; i < iterations; ++i) {
        checksum += function(input);
    }
    const uint64_t end = now_ns();
    checksum_sink ^= checksum;
    if (end < start) {
        fail("benchmark clock moved backwards");
    }
    return (Batch){end - start, checksum};
}

static void record(FILE *file, const Configuration *configuration, int round,
                   uint64_t iterations, Batch batch, const char *phase)
{
    if (fprintf(file, "%s,%" PRIu64 ",%d,%" PRIu64 ",%" PRIu64 ",%" PRIu64,
                configuration->target, configuration->input, round, iterations,
                batch.elapsed_ns, batch.checksum) < 0
        || (phase != NULL && fprintf(file, ",%s", phase) < 0)
        || fputc('\n', file) == EOF) {
        perror("write benchmark CSV");
        exit(EXIT_FAILURE);
    }
}

static uint64_t random_next(uint64_t *state)
{
    *state ^= *state >> 12;
    *state ^= *state << 25;
    *state ^= *state >> 27;
    return *state * UINT64_C(2685821657736338717);
}

static uint64_t parse_seed(const char *text)
{
    char *end = NULL;
    errno = 0;
    if (text[0] < '0' || text[0] > '9') {
        fail("seed must be a nonzero uint64 integer (decimal or 0x hexadecimal)");
    }
    const uintmax_t value = strtoumax(text, &end, 0);
    if (errno != 0 || end == text || *end != '\0' || value == 0
        || value > UINT64_MAX) {
        fail("seed must be a nonzero uint64 integer (decimal or 0x hexadecimal)");
    }
    return (uint64_t)value;
}

int main(int argc, char **argv)
{
    if (argc != 4 || argv[1][0] == '\0' || argv[2][0] == '\0'
        || strcmp(argv[1], argv[2]) == 0) {
        fprintf(stderr, "usage: %s raw.csv calibration.csv nonzero-seed\n", argv[0]);
        return EXIT_FAILURE;
    }
    const uint64_t seed = parse_seed(argv[3]);
    FILE *samples = fopen(argv[1], "w");
    FILE *calibration = fopen(argv[2], "w");
    if (samples == NULL || calibration == NULL) {
        perror("open benchmark CSV");
        return EXIT_FAILURE;
    }
    if (fputs("target,input,round,iterations,elapsed_ns,checksum\n", samples) == EOF
        || fputs("target,input,round,iterations,elapsed_ns,checksum,phase\n",
                 calibration) == EOF) {
        fail("cannot write CSV headers");
    }

    Configuration configurations[CONFIG_COUNT];
    size_t count = 0;
    const uint64_t l1_inputs[] = {
        0, 1, 2, 3, 4, 5, 8, 10, 12, 15, 18, 20, 22, 25, 28, 30, 32, 35, 38, 40
    };
    for (size_t i = 0; i < sizeof(l1_inputs) / sizeof(l1_inputs[0]); ++i) {
        configurations[count++] = (Configuration){
            "fib_l1", fib_l1, l1_inputs[i], 0, true};
    }
    const BenchmarkFunction fast_functions[] = {fib_l2, fib_l3, fib_l4};
    const char *fast_names[] = {"fib_l2", "fib_l3", "fib_l4"};
    for (size_t target = 0; target < 3; ++target) {
        for (uint64_t input = 0; input <= 91; ++input) {
            configurations[count++] = (Configuration){
                fast_names[target], fast_functions[target], input, 0, false};
        }
    }
    configurations[count++] = (Configuration){
        "identity", benchmark_identity, 17, 0, false};
    if (count != CONFIG_COUNT) {
        fail("internal configuration count mismatch");
    }

    bool l1_capped = false;
    uint64_t cap_input = 0;
    uint64_t cap_elapsed_ns = 0;
    const char *cap_phase = "none";
    size_t active_count = 0;
    for (size_t i = 0; i < count; ++i) {
        Configuration *configuration = &configurations[i];
        if (configuration->is_l1 && l1_capped) {
            continue;
        }
        const uint64_t warmup_calls = configuration->is_l1 ? 1 : FAST_WARMUP;
        Batch batch = benchmark_batch(configuration->function,
                                      configuration->input, warmup_calls);
        record(calibration, configuration, -1, warmup_calls, batch, "warmup");
        uint64_t iterations = configuration->is_l1 ? 1 : UINT64_C(1024);
        if (configuration->is_l1 && batch.elapsed_ns > L1_SINGLE_CALL_CAP_NS) {
            l1_capped = true;
            cap_phase = "warmup";
        } else {
            for (;;) {
                batch = benchmark_batch(configuration->function,
                                        configuration->input, iterations);
                record(calibration, configuration, -1, iterations, batch,
                       "calibration");
                if (configuration->is_l1 && iterations == 1
                    && batch.elapsed_ns > L1_SINGLE_CALL_CAP_NS) {
                    l1_capped = true;
                    cap_phase = "calibration";
                    break;
                }
                if (batch.elapsed_ns >= MIN_BATCH_NS) {
                    configuration->iterations = iterations;
                    ++active_count;
                    break;
                }
                if (iterations > UINT64_MAX / 2) {
                    fail("calibration iteration count overflow");
                }
                iterations *= 2;
            }
        }
        if (configuration->is_l1 && l1_capped) {
            cap_input = configuration->input;
            cap_elapsed_ns = batch.elapsed_ns;
            fprintf(stderr, "L1 single-call cap: n=%" PRIu64 " took %" PRIu64
                    " ns during %s; skipping repeated timing at this and larger inputs\n",
                    cap_input, cap_elapsed_ns, cap_phase);
        }
    }
    if (fclose(calibration) != 0) {
        perror("close calibration CSV");
        return EXIT_FAILURE;
    }

    uint64_t random_state = seed;
    for (int round = 0; round < REPEATS; ++round) {
        size_t order[CONFIG_COUNT];
        size_t length = 0;
        for (size_t i = 0; i < count; ++i) {
            if (configurations[i].iterations != 0) {
                order[length++] = i;
            }
        }
        for (size_t i = length - 1; i > 0; --i) {
            const size_t j = (size_t)(random_next(&random_state) % (i + 1));
            const size_t temporary = order[i];
            order[i] = order[j];
            order[j] = temporary;
        }
        for (size_t i = 0; i < length; ++i) {
            const Configuration *configuration = &configurations[order[i]];
            Batch batch = benchmark_batch(configuration->function,
                                          configuration->input,
                                          configuration->iterations);
            if (batch.elapsed_ns == 0) {
                fail("benchmark sample clock did not advance");
            }
            record(samples, configuration, round, configuration->iterations,
                   batch, NULL);
        }
        if (fflush(samples) != 0) {
            perror("flush sample CSV");
            return EXIT_FAILURE;
        }
    }
    if (fclose(samples) != 0) {
        perror("close sample CSV");
        return EXIT_FAILURE;
    }
    struct timespec resolution;
    if (clock_getres(BENCHMARK_CLOCK, &resolution) != 0) {
        perror("clock_getres");
        return EXIT_FAILURE;
    }
    printf("seed=0x%016" PRIx64 "\nrepeats=%d\nconfiguration_count=%zu\n"
           "clock=%s\nclock_resolution_ns=%" PRIu64 "\nchecksum_sink=%" PRIu64 "\n",
           seed, REPEATS, active_count, BENCHMARK_CLOCK_NAME,
           (uint64_t)resolution.tv_sec * UINT64_C(1000000000)
           + (uint64_t)resolution.tv_nsec, checksum_sink);
    if (l1_capped) {
        printf("l1_first_skipped_input=%" PRIu64 "\nl1_cap_elapsed_ns=%" PRIu64
               "\nl1_cap_phase=%s\n", cap_input, cap_elapsed_ns, cap_phase);
    } else {
        puts("l1_first_skipped_input=none\nl1_cap_elapsed_ns=0\nl1_cap_phase=none");
    }
    return EXIT_SUCCESS;
}
