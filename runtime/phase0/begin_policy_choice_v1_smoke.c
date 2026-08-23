#include "begin_policy_choice_v1.h"
#include "begin_policy_choice_v1_smoke_fixture.h"

#include <stdlib.h>

static struct phil_test_policy_context *as_policy_context(void *value) {
    if (value == NULL) {
        abort();
    }
    return (struct phil_test_policy_context *) value;
}

static struct phil_test_begin_record *as_begin_record(void *value) {
    if (value == NULL) {
        abort();
    }
    return (struct phil_test_begin_record *) value;
}

static struct phil_test_begin_policy_transport *as_transport(void *value) {
    if (value == NULL) {
        abort();
    }
    return (struct phil_test_begin_policy_transport *) value;
}

static void write_octet(
    struct phil_test_begin_policy_transport *transport,
    uint8_t value) {
    if (transport->output_length >= transport->output_capacity
        || transport->output_length >= PHIL_TEST_BEGIN_POLICY_WIRE_CAPACITY) {
        abort();
    }
    transport->output[transport->output_length++] = value;
}

static uint8_t read_octet(struct phil_test_begin_policy_transport *transport) {
    if (transport->input_offset >= transport->input_length
        || transport->input_offset >= PHIL_TEST_BEGIN_POLICY_WIRE_CAPACITY) {
        abort();
    }
    return transport->input[transport->input_offset++];
}

bool phil_runtime_validate_begin_policy(
    void *policy_context_value,
    void *begin_record_value,
    uint8_t *rejection_reason_out) {
    struct phil_test_policy_context *policy_context =
        as_policy_context(policy_context_value);
    struct phil_test_begin_record *begin_record =
        as_begin_record(begin_record_value);

    if (rejection_reason_out == NULL) {
        abort();
    }
    if (begin_record->length <= policy_context->max_length) {
        return true;
    }
    *rejection_reason_out = 0x01u;
    return false;
}

void phil_runtime_select_begin_policy_reject(
    void *transport_value,
    uint8_t rejection_reason) {
    struct phil_test_begin_policy_transport *transport = as_transport(transport_value);
    if (rejection_reason != 0x01u) {
        abort();
    }
    write_octet(transport, 0x00u);
    write_octet(transport, rejection_reason);
}

void phil_runtime_select_begin_policy_proceed(void *transport_value) {
    struct phil_test_begin_policy_transport *transport = as_transport(transport_value);
    write_octet(transport, 0x01u);
}

bool phil_runtime_receive_begin_policy_choice(
    void *transport_value,
    uint8_t *rejection_reason_out) {
    struct phil_test_begin_policy_transport *transport = as_transport(transport_value);
    uint8_t tag = read_octet(transport);

    if (tag == 0x01u) {
        return true;
    }
    if (tag == 0x00u) {
        uint8_t reason = read_octet(transport);
        if (rejection_reason_out == NULL || reason != 0x01u) {
            abort();
        }
        *rejection_reason_out = reason;
        return false;
    }
    abort();
}
