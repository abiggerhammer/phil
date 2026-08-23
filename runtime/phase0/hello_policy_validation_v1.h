#ifndef PHIL_RUNTIME_PHASE0_HELLO_POLICY_VALIDATION_V1_H
#define PHIL_RUNTIME_PHASE0_HELLO_POLICY_VALIDATION_V1_H

#include <stdbool.h>

bool phil_runtime_validate_hello_policy(
    void *policy_context,
    void *hello_record,
    void **rejection_reason_out);
void phil_runtime_fail_hello_policy(
    void *transport,
    void *rejection_reason);

#endif
