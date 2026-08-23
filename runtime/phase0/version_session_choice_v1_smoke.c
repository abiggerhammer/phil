#include "version_session_choice_v1.h"
#include "version_session_choice_v1_smoke_fixture.h"

#include <stdlib.h>

static struct phil_test_version_set *as_set(void *value) {
    if (value == NULL) {
        abort();
    }
    return (struct phil_test_version_set *) value;
}

static struct phil_test_choice_transport *as_transport(void *value) {
    if (value == NULL) {
        abort();
    }
    return (struct phil_test_choice_transport *) value;
}

static void write_octet(struct phil_test_choice_transport *transport, uint8_t value) {
    if (transport->output_length >= transport->output_capacity
        || transport->output_length >= PHIL_TEST_WIRE_CAPACITY) {
        abort();
    }
    transport->output[transport->output_length++] = value;
}

static uint8_t read_octet(struct phil_test_choice_transport *transport) {
    if (transport->input_offset >= transport->input_length
        || transport->input_offset >= PHIL_TEST_WIRE_CAPACITY) {
        abort();
    }
    return transport->input[transport->input_offset++];
}

void *phil_record_Hello_get_versions(void *hello_record) {
    if (hello_record == NULL) {
        abort();
    }
    return &((struct phil_test_hello_record *) hello_record)->versions;
}

bool phil_runtime_choose_supported(
    void *server_supported,
    void *offered_versions,
    uint16_t *selected_version_out) {
    struct phil_test_version_set *supported = as_set(server_supported);
    struct phil_test_version_set *offered = as_set(offered_versions);
    size_t i;
    size_t j;

    if (selected_version_out == NULL) {
        abort();
    }
    if (supported->length > PHIL_TEST_VERSION_CAPACITY
        || offered->length > PHIL_TEST_VERSION_CAPACITY) {
        abort();
    }

    for (i = 0; i < supported->length; ++i) {
        for (j = 0; j < offered->length; ++j) {
            if (supported->values[i] == offered->values[j]) {
                *selected_version_out = supported->values[i];
                return true;
            }
        }
    }
    return false;
}

void phil_runtime_select_unsupported(void *transport_value) {
    struct phil_test_choice_transport *transport = as_transport(transport_value);
    write_octet(transport, 0x00u);
}

void phil_runtime_select_version(void *transport_value, uint16_t selected_version) {
    struct phil_test_choice_transport *transport = as_transport(transport_value);
    write_octet(transport, 0x01u);
    write_octet(transport, (uint8_t) (selected_version >> 8));
    write_octet(transport, (uint8_t) (selected_version & 0xffu));
}

bool phil_runtime_refine_selected_version(
    void *transport_value,
    uint16_t selected_version) {
    struct phil_test_choice_transport *transport = as_transport(transport_value);
    size_t i;
    if (transport->offered_versions == NULL
        || transport->offered_versions->length > PHIL_TEST_VERSION_CAPACITY) {
        abort();
    }
    for (i = 0; i < transport->offered_versions->length; ++i) {
        if (transport->offered_versions->values[i] == selected_version) {
  return true;
        }
    }
    return false;
}

bool phil_runtime_receive_version_choice(
    void *transport_value,
    uint16_t *selected_version_out) {
    struct phil_test_choice_transport *transport = as_transport(transport_value);
    uint8_t tag = read_octet(transport);

    if (tag == 0x00u) {
        return false;
    }
    if (tag == 0x01u) {
        uint16_t high;
        uint16_t low;
        if (selected_version_out == NULL) {
            abort();
        }
        high = read_octet(transport);
        low = read_octet(transport);
        *selected_version_out = (uint16_t) ((high << 8) | low);
        return true;
    }
    abort();
}
