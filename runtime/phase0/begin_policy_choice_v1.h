#ifndef PHIL_RUNTIME_PHASE0_BEGIN_POLICY_CHOICE_V1_H
#define PHIL_RUNTIME_PHASE0_BEGIN_POLICY_CHOICE_V1_H

#include <stdbool.h>
#include <stdint.h>

bool phil_runtime_validate_begin_policy(
    void *policy_context,
    void *begin_record,
    uint8_t *rejection_reason_out);
void phil_runtime_select_begin_policy_reject(
    void *transport,
    uint8_t rejection_reason);
void phil_runtime_select_begin_policy_proceed(void *transport);
bool phil_runtime_receive_begin_policy_choice(
    void *transport,
    uint8_t *rejection_reason_out);

#endif
