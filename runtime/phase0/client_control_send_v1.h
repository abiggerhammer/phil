#ifndef PHIL_PHASE0_CLIENT_CONTROL_SEND_V1_H
#define PHIL_PHASE0_CLIENT_CONTROL_SEND_V1_H

#include <stdbool.h>
#include <stdint.h>

void *phil_runtime_supported_versions(void);
uint64_t phil_runtime_payload_length(void *payload_owner);
void *phil_runtime_payload_kind(void *payload_owner);
void *phil_runtime_sha256(void *payload_owner);
void phil_runtime_send_hello(void *transport, void *versions);
void phil_runtime_send_begin_sha256(
    void *transport,
    uint64_t length,
    void *kind,
    void *digest);
bool phil_runtime_refine_selected_version_with_set(
    void *transport,
    void *versions,
    uint16_t selected);

int phil_client_control_send_v1_smoke(void);

#endif
