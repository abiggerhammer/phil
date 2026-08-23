#include <stdbool.h>
#include <stdint.h>

bool phil_runtime_validate_begin_policy(void) {
    return true;
}

void phil_runtime_select_begin_policy_reject(void) {
}

void phil_runtime_select_begin_policy_proceed(void) {
}

bool phil_runtime_receive_begin_policy_choice(void) {
    return true;
}
