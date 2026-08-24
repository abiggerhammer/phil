#include "client_control_send_v1.h"

#include <stddef.h>

static int versions_token;
static int payload_token;
static int kind_token;
static int digest_token;
static int transport_token;

static void *expected_payload;
static void *expected_transport;
static void *expected_versions;
static void *expected_kind;
static void *expected_digest;
static uint64_t expected_length;
static unsigned hello_calls;
static unsigned begin_calls;
static unsigned refine_calls;

void *phil_runtime_supported_versions(void) {
    return &versions_token;
}

uint64_t phil_runtime_payload_length(void *payload_owner) {
    return payload_owner == expected_payload ? expected_length : 0;
}

void *phil_runtime_payload_kind(void *payload_owner) {
    return payload_owner == expected_payload ? &kind_token : NULL;
}

void *phil_runtime_sha256(void *payload_owner) {
    return payload_owner == expected_payload ? &digest_token : NULL;
}

void phil_runtime_send_hello(void *transport, void *versions) {
    if (transport == expected_transport && versions == expected_versions) {
        ++hello_calls;
    }
}

void phil_runtime_send_begin_sha256(
    void *transport,
    uint64_t length,
    void *kind,
    void *digest) {
    if (transport == expected_transport
        && length == expected_length
        && kind == expected_kind
        && digest == expected_digest) {
        ++begin_calls;
    }
}

bool phil_runtime_refine_selected_version_with_set(
    void *transport,
    void *versions,
    uint16_t selected) {
    if (transport == expected_transport
        && versions == expected_versions
        && selected == UINT16_C(7)) {
        ++refine_calls;
        return true;
    }
    return false;
}

int phil_client_control_send_v1_smoke(void) {
    expected_payload = &payload_token;
    expected_transport = &transport_token;
    expected_versions = &versions_token;
    expected_kind = &kind_token;
    expected_digest = &digest_token;
    expected_length = UINT64_C(4096);
    hello_calls = 0;
    begin_calls = 0;
    refine_calls = 0;

    void *versions = phil_runtime_supported_versions();
    if (versions != expected_versions) {
        return 1;
    }

    phil_runtime_send_hello(expected_transport, versions);
    if (hello_calls != 1) {
        return 2;
    }

    uint64_t length = phil_runtime_payload_length(expected_payload);
    void *kind = phil_runtime_payload_kind(expected_payload);
    void *digest = phil_runtime_sha256(expected_payload);
    if (length != expected_length || kind != expected_kind || digest != expected_digest) {
        return 3;
    }

    phil_runtime_send_begin_sha256(expected_transport, length, kind, digest);
    if (begin_calls != 1) {
        return 4;
    }

    if (!phil_runtime_refine_selected_version_with_set(
            expected_transport, versions, UINT16_C(7))) {
        return 5;
    }
    if (refine_calls != 1) {
        return 6;
    }

    return 0;
}
