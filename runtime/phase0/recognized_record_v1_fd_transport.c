#include "recognized_record_v1.h"

#include <errno.h>
#include <stddef.h>
#include <unistd.h>

struct phil_begin_record_impl {
  uint64_t length;
};

struct phil_transport_state {
  int input_fd;
  uint8_t begin_status;
  struct phil_begin_record_impl begin_record;
  unsigned begin_recognize_calls;
  unsigned begin_accessor_calls;
  unsigned exact_receive_calls;
  unsigned cleanup_calls;
  unsigned accepted_calls;
  unsigned invalid_record_calls;
  uint64_t requested_receive_length;
  uint64_t bytes_read;
  bool last_receive_succeeded;
};

static struct phil_transport_state transport_state;

void phil_transport_configure(int input_fd, uint8_t begin_status, uint64_t begin_length) {
  transport_state.input_fd = input_fd;
  transport_state.begin_status = begin_status;
  transport_state.begin_record.length = begin_length;
  transport_state.begin_recognize_calls = 0;
  transport_state.begin_accessor_calls = 0;
  transport_state.exact_receive_calls = 0;
  transport_state.cleanup_calls = 0;
  transport_state.accepted_calls = 0;
  transport_state.invalid_record_calls = 0;
  transport_state.requested_receive_length = 0;
  transport_state.bytes_read = 0;
  transport_state.last_receive_succeeded = false;
}

bool phil_transport_success_observed(uint64_t expected_length) {
  return transport_state.begin_recognize_calls == 1
      && transport_state.begin_accessor_calls == 1
      && transport_state.exact_receive_calls == 1
      && transport_state.cleanup_calls == 0
      && transport_state.accepted_calls == 1
      && transport_state.invalid_record_calls == 0
      && transport_state.requested_receive_length == expected_length
      && transport_state.bytes_read == expected_length
      && transport_state.last_receive_succeeded;
}

bool phil_transport_short_read_observed(
    uint64_t expected_length,
    uint64_t expected_bytes_read) {
  return transport_state.begin_recognize_calls == 1
      && transport_state.begin_accessor_calls == 1
      && transport_state.exact_receive_calls == 1
      && transport_state.cleanup_calls == 1
      && transport_state.accepted_calls == 0
      && transport_state.invalid_record_calls == 0
      && transport_state.requested_receive_length == expected_length
      && transport_state.bytes_read == expected_bytes_read
      && !transport_state.last_receive_succeeded;
}

bool phil_runtime_recognize_Hello(void) {
  return true;
}

struct phil_recognized_record_result phil_runtime_recognize_Begin(void) {
  struct phil_recognized_record_result result;
  transport_state.begin_recognize_calls += 1;
  result.status = transport_state.begin_status;
  result.record = &transport_state.begin_record;
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
  transport_state.begin_accessor_calls += 1;
  if (record != &transport_state.begin_record) {
    transport_state.invalid_record_calls += 1;
    return 0;
  }
  return transport_state.begin_record.length;
}

bool phil_runtime_receive_exact_u64(uint64_t length) {
  unsigned char buffer[4096];
  uint64_t remaining = length;

  transport_state.exact_receive_calls += 1;
  transport_state.requested_receive_length = length;
  transport_state.last_receive_succeeded = false;

  if (transport_state.input_fd < 0) {
    return false;
  }

  while (remaining > 0) {
    size_t requested = remaining > (uint64_t) sizeof(buffer)
      ? sizeof(buffer)
      : (size_t) remaining;
    ssize_t received;

    do {
      received = read(transport_state.input_fd, buffer, requested);
    } while (received < 0 && errno == EINTR);

    if (received <= 0) {
      return false;
    }

    transport_state.bytes_read += (uint64_t) received;
    remaining -= (uint64_t) received;
  }

  transport_state.last_receive_succeeded = true;
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
  transport_state.cleanup_calls += 1;
}

void phil_call_select_accepted(void) {
  transport_state.accepted_calls += 1;
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
