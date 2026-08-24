#include <stdbool.h>
#include <stdint.h>

static void *current_transport;
static void *current_versions;
static uint64_t current_length;
static void *current_kind;
static void *current_digest;

void *phil_runtime_supported_versions(void) {
    return current_versions;
}

uint64_t phil_runtime_payload_length(void) {
    return current_length;
}

void *phil_runtime_payload_kind(void) {
    return current_kind;
}

void *phil_runtime_sha256(void) {
    return current_digest;
}

void phil_runtime_send_hello(void) {
    (void)current_transport;
}

void phil_runtime_send_begin_sha256(void) {
    (void)current_transport;
}

bool phil_runtime_refine_selected_version_with_set(uint16_t selected) {
    return selected != 0;
}
