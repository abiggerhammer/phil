#include "hello_policy_validation_v1.h"

#include <stdbool.h>

struct phil_test_policy_context {
  bool accept;
  void *reason;
};

static void *last_failure_transport;
static void *last_failure_reason;

bool phil_runtime_validate_hello_policy(
    void *policy_context,
    void *hello_record,
    void **rejection_reason_out) {
  struct phil_test_policy_context *context = policy_context;
  if (context == 0 || hello_record == 0 || rejection_reason_out == 0) {
    return false;
  }
  if (context->accept) {
    return true;
  }
  *rejection_reason_out = context->reason;
  return false;
}

void phil_runtime_fail_hello_policy(
    void *transport,
    void *rejection_reason) {
  last_failure_transport = transport;
  last_failure_reason = rejection_reason;
}

int phil_hello_policy_validation_v1_smoke(void) {
  int hello_record = 1;
  int transport = 2;
  int rejection_reason = 3;
  int untouched = 4;
  void *reason_slot = &untouched;
  struct phil_test_policy_context accepted = { true, &rejection_reason };
  struct phil_test_policy_context rejected = { false, &rejection_reason };

  if (!phil_runtime_validate_hello_policy(
        &accepted, &hello_record, &reason_slot)) {
    return 1;
  }
  if (reason_slot != &untouched) {
    return 2;
  }

  reason_slot = 0;
  if (phil_runtime_validate_hello_policy(
        &rejected, &hello_record, &reason_slot)) {
    return 3;
  }
  if (reason_slot != &rejection_reason) {
    return 4;
  }

  last_failure_transport = 0;
  last_failure_reason = 0;
  phil_runtime_fail_hello_policy(&transport, reason_slot);
  if (last_failure_transport != &transport) {
    return 5;
  }
  if (last_failure_reason != &rejection_reason) {
    return 6;
  }

  return 0;
}
