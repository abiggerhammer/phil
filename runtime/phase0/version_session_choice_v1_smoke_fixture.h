#ifndef PHIL_RUNTIME_PHASE0_VERSION_SESSION_CHOICE_V1_SMOKE_FIXTURE_H
#define PHIL_RUNTIME_PHASE0_VERSION_SESSION_CHOICE_V1_SMOKE_FIXTURE_H

#include <stddef.h>
#include <stdint.h>

#define PHIL_TEST_VERSION_CAPACITY 8
#define PHIL_TEST_WIRE_CAPACITY 16

struct phil_test_version_set {
    uint16_t values[PHIL_TEST_VERSION_CAPACITY];
    size_t length;
};

struct phil_test_hello_record {
    struct phil_test_version_set versions;
};

struct phil_test_choice_transport {
    uint8_t input[PHIL_TEST_WIRE_CAPACITY];
    size_t input_length;
    size_t input_offset;
    uint8_t output[PHIL_TEST_WIRE_CAPACITY];
    size_t output_length;
    size_t output_capacity;
};

#endif
