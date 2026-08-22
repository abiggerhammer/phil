#include "recognized_record_v1.h"

#include <stddef.h>

struct phil_begin_record_impl {
  uint64_t length;
};

struct phil_smoke_state {
  uint8_t begin_status;
  struct phil_begin_record_impl begin_record;
  unsigned begin_recognize_calls;
  unsigned begin_accessor_calls;
  unsigned exact_receive_calls;
  unsigned cleanup_calls;
  unsigned accepted_calls;
  unsigned invalid_record_calls;
  uint64_t observed_receive_length;
};

static struct phil_smoke_state smoke_state;

void phil_smoke_configure(uint8_t begin_status, uint64_t begin_length) {
  smoke_state.begin_status = begin_status;
  smoke_state.begin_record.length = begin_length;
  smoke_state.begin_recognize_calls = 0;
  smoke_state.begin_accessor_calls = 0;
  smoke_state.exact_receive_calls = 0;
  smoke_state.cleanup_calls = 0;
  smoke_state.accepted_calls = 0;
  smoke_state.invalid_record_calls = 0;
  smoke_state.observed_receive_length = 0;
}

bool phil_smoke_success_observed(uint64_t expected_length) {
  return smoke_state.begin_recognize_calls == 1
      && smoke_state.begin_accessor_calls == 1
      && smoke_state.exact_receive_calls == 1
      && smoke_state.cleanup_calls == 0
      && smoke_state.accepted_calls == 1
      && smoke_state.invalid_record_calls == 0
      && smoke_state.observed_receive_length == expected_length;
}

bool phil_smoke_fail_closed_observed(void) {
  return smoke_state.begin_recognize_calls == 1
      && smoke_state.begin_accessor_calls == 0
      && smoke_state.exact_receive_calls == 0
      && smoke_state.cleanup_calls == 1
      && smoke_state.accepted_calls == 0
      && smoke_state.invalid_record_calls == 0;
}

bool phil_runtime_recognize_Hello(void) {
  return true;
}

struct phil_recognized_record_result phil_runtime_recognize_Begin(void) {
  struct phil_recognized_record_result result;
  smoke_state.begin_recognize_calls += 1;
  result.status = smoke_state.begin_status;
  result.record = &smoke_state.begin_record;
  return result;
}

bool phil_runtime_validate_HelloPolicy(void) {
  return true;
}

bool phil_runtime_validate_BeginPolicy(void) {
  return true;
}

bool phil_runtime_refine_selected_version(void) {
  return true;
}

uint64_t phil_record_Begin_get_length(void *record) {
  smoke_state.begin_accessor_calls += 1;
  if (record != &smoke_state.begin_record) {
    smoke_state.invalid_record_calls += 1;
    return 0;
  }
  return smoke_state.begin_record.length;
}

bool phil_runtime_receive_exact_u64(uint64_t length) {
  smoke_state.exact_receive_calls += 1;
  smoke_state.observed_receive_length = length;
  return true;
}

bool phil_runtime_send_exact(void) {
  return true;
}

bool phil_runtime_digest_validate(void) {
  return true;
}

bool phil_runtime_store(void) {
  return true;
}

bool phil_branch_condition(void) {
  return true;
}

void phil_cleanup(void) {
  smoke_state.cleanup_calls += 1;
}

void phil_call_select_accepted(void) {
  smoke_state.accepted_calls += 1;
}

#define PHIL_NOOP_CALL(name) \
  void name(void) {}

PHIL_NOOP_CALL(phil_call_receive_frame_Hello)
PHIL_NOOP_CALL(phil_call_choose_supported)
PHIL_NOOP_CALL(phil_call_select_unsupported)
PHIL_NOOP_CALL(phil_call_select_version)
PHIL_NOOP_CALL(phil_call_receive_frame_Begin)
PHIL_NOOP_CALL(phil_call_select_reject)
PHIL_NOOP_CALL(phil_call_select_proceed)
PHIL_NOOP_CALL(phil_call_receive_payload_cancel_label)
PHIL_NOOP_CALL(phil_call_select_rejected)
PHIL_NOOP_CALL(phil_call_send_Hello)
PHIL_NOOP_CALL(phil_call_receive_version_unsupported_label)
PHIL_NOOP_CALL(phil_call_send_Begin)
PHIL_NOOP_CALL(phil_call_receive_proceed_reject_label)
PHIL_NOOP_CALL(phil_call_should_cancel_upload)
PHIL_NOOP_CALL(phil_call_select_cancel)
PHIL_NOOP_CALL(phil_call_select_payload)
PHIL_NOOP_CALL(phil_call_receive_accepted_rejected_label)
