#ifndef PHIL_RUNTIME_PHASE0_VERSION_SESSION_CHOICE_V1_H
#define PHIL_RUNTIME_PHASE0_VERSION_SESSION_CHOICE_V1_H

#include <stdbool.h>
#include <stdint.h>

void *phil_record_Hello_get_versions(void *hello_record);
bool phil_runtime_choose_supported(
    void *server_supported,
    void *offered_versions,
    uint16_t *selected_version_out);
void phil_runtime_select_unsupported(void *transport);
void phil_runtime_select_version(void *transport, uint16_t selected_version);
bool phil_runtime_receive_version_choice(
    void *transport,
    uint16_t *selected_version_out);

#endif
