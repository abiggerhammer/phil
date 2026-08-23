#ifndef PHIL_RUNTIME_PHASE0_BEGIN_POLICY_CHOICE_V1_SMOKE_FIXTURE_H
#define PHIL_RUNTIME_PHASE0_BEGIN_POLICY_CHOICE_V1_SMOKE_FIXTURE_H

#include <stddef.h>
#include <stdint.h>

#define PHIL_TEST_BEGIN_POLICY_WIRE_CAPACITY 8u

struct phil_test_policy_context {
    uint64_t max_length;
};

struct phil_test_begin_record {
    uint64_t length;
};

struct phil_test_begin_policy_transport {
    uint8_t input[PHIL_TEST_BEGIN_POLICY_WIRE_CAPACITY];
    size_t input_length;
    size_t input_offset;
    uint8_t output[PHIL_TEST_BEGIN_POLICY_WIRE_CAPACITY];
    size_t output_capacity;
    size_t output_length;
};

#endif
