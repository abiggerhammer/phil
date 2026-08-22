#include "rejected_response_v1.h"

#include <openssl/crypto.h>
#include <openssl/sha.h>
#include <stdlib.h>
#include <string.h>

#define PHIL_SMOKE_CAPACITY 4096u
#define PHIL_SHA256_BYTES 32u
#define PHIL_REJECTED_RESPONSE_BYTES 2u
#define PHIL_REJECTED_TAG 0x00u
#define PHIL_REASON_DIGEST_MISMATCH 0x01u

struct phil_transport_impl {
  uint8_t bytes[PHIL_SMOKE_CAPACITY];
  size_t available;
  size_t cursor;
  uint8_t output[64];
  size_t output_length;
};

struct phil_begin_record_impl {
  uint64_t length;
  uint8_t digest[PHIL_SHA256_BYTES];
};

struct phil_payload_impl {
  size_t length;
  uint8_t bytes[];
};

struct phil_smoke_state {
  struct phil_transport_impl transport;
  struct phil_begin_record_impl begin_record;
  struct phil_payload_impl *last_payload;
  size_t last_payload_length;
  unsigned exact_receive_calls;
  unsigned digest_calls;
  unsigned store_calls;
  unsigned release_calls;
  unsigned accepted_calls;
  unsigned rejected_calls;
  unsigned invalid_transport_calls;
  unsigned invalid_digest_subject_calls;
  unsigned invalid_release_calls;
  unsigned invalid_rejected_transport_calls;
  unsigned invalid_rejected_reason_calls;
  unsigned rejected_before_release_calls;
  bool last_payload_matches_input;
  bool last_digest_result;
};

static struct phil_smoke_state smoke_state;

static struct phil_payload_impl *allocate_payload(size_t length) {
  struct phil_payload_impl *payload = malloc(sizeof(*payload) + length);
  if (payload == NULL) {
    abort();
  }
  payload->length = length;
  return payload;
}

void *phil_smoke_configure_rejected_response(
    const uint8_t *bytes,
    size_t available,
    uint64_t requested_length,
    const uint8_t expected_digest[32]) {
  if (available > PHIL_SMOKE_CAPACITY) {
    abort();
  }
  if (smoke_state.last_payload != NULL) {
    free(smoke_state.last_payload);
  }
  memset(&smoke_state, 0, sizeof(smoke_state));
  if (available != 0) {
    memcpy(smoke_state.transport.bytes, bytes, available);
  }
  smoke_state.transport.available = available;
  smoke_state.begin_record.length = requested_length;
  memcpy(smoke_state.begin_record.digest, expected_digest, PHIL_SHA256_BYTES);
  return &smoke_state.transport;
}

bool phil_smoke_rejected_response_observed(
    size_t payload_length,
    const uint8_t *expected_response,
    size_t response_length) {
  return smoke_state.exact_receive_calls == 1
      && smoke_state.digest_calls == 1
      && smoke_state.store_calls == 0
      && smoke_state.release_calls == 1
      && smoke_state.accepted_calls == 0
      && smoke_state.rejected_calls == 1
      && smoke_state.invalid_transport_calls == 0
      && smoke_state.invalid_digest_subject_calls == 0
      && smoke_state.invalid_release_calls == 0
      && smoke_state.invalid_rejected_transport_calls == 0
      && smoke_state.invalid_rejected_reason_calls == 0
      && smoke_state.rejected_before_release_calls == 0
      && smoke_state.last_payload == NULL
      && smoke_state.last_payload_length == payload_length
      && smoke_state.last_payload_matches_input
      && !smoke_state.last_digest_result
      && response_length == PHIL_REJECTED_RESPONSE_BYTES
      && smoke_state.transport.output_length == response_length
      && memcmp(smoke_state.transport.output, expected_response, response_length) == 0;
}

bool phil_runtime_recognize_Hello(void) {
  return true;
}

struct phil_recognized_record_result phil_runtime_recognize_Begin(void) {
  struct phil_recognized_record_result result = {
    .status = 1,
    .record = &smoke_state.begin_record,
  };
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
  if (record != &smoke_state.begin_record) {
    return 0;
  }
  return smoke_state.begin_record.length;
}

struct phil_exact_receive_result phil_runtime_receive_exact_u64(
    void *transport,
    uint64_t length) {
  struct phil_exact_receive_result result;
  struct phil_transport_impl *source = transport;
  size_t requested;
  size_t remaining;
  size_t copied;
  const uint8_t *source_start;
  struct phil_payload_impl *payload;

  smoke_state.exact_receive_calls += 1;
  if (source != &smoke_state.transport) {
    smoke_state.invalid_transport_calls += 1;
    payload = allocate_payload(0);
    smoke_state.last_payload = payload;
    smoke_state.last_payload_length = 0;
    smoke_state.last_payload_matches_input = false;
    result.status = 0;
    result.payload = payload;
    return result;
  }

  requested = length > PHIL_SMOKE_CAPACITY
    ? PHIL_SMOKE_CAPACITY + 1u
    : (size_t) length;
  remaining = source->available - source->cursor;
  copied = requested <= remaining ? requested : remaining;
  source_start = source->bytes + source->cursor;
  payload = allocate_payload(copied);
  if (copied != 0) {
    memcpy(payload->bytes, source_start, copied);
  }
  source->cursor += copied;

  smoke_state.last_payload = payload;
  smoke_state.last_payload_length = copied;
  smoke_state.last_payload_matches_input =
    copied == 0 || memcmp(payload->bytes, source_start, copied) == 0;

  result.status = requested <= remaining ? 1 : 0;
  result.payload = payload;
  return result;
}

bool phil_runtime_digest_validate(void *begin_record, void *payload_handle) {
  uint8_t actual[PHIL_SHA256_BYTES];
  struct phil_begin_record_impl *begin = begin_record;
  struct phil_payload_impl *payload = payload_handle;

  smoke_state.digest_calls += 1;
  if (begin != &smoke_state.begin_record
      || payload != smoke_state.last_payload
      || payload == NULL) {
    smoke_state.invalid_digest_subject_calls += 1;
    smoke_state.last_digest_result = false;
    return false;
  }
  if (SHA256(payload->bytes, payload->length, actual) == NULL) {
    abort();
  }
  smoke_state.last_digest_result =
    CRYPTO_memcmp(actual, begin->digest, PHIL_SHA256_BYTES) == 0;
  return smoke_state.last_digest_result;
}

struct phil_store_result phil_runtime_store(void *payload_handle) {
  struct phil_store_result result = { .status = 0, .upload_id = NULL };
  struct phil_payload_impl *payload = payload_handle;

  smoke_state.store_calls += 1;
  if (payload == smoke_state.last_payload && payload != NULL) {
    free(payload);
    smoke_state.last_payload = NULL;
  }
  return result;
}

void phil_runtime_select_accepted(void *transport, void *upload_id) {
  (void) transport;
  (void) upload_id;
  smoke_state.accepted_calls += 1;
}

void phil_runtime_select_rejected(void *transport, uint8_t reason_code) {
  struct phil_transport_impl *destination = transport;

  if (destination != &smoke_state.transport) {
    smoke_state.invalid_rejected_transport_calls += 1;
    return;
  }
  if (reason_code != PHIL_REASON_DIGEST_MISMATCH) {
    smoke_state.invalid_rejected_reason_calls += 1;
    return;
  }
  if (smoke_state.last_payload != NULL || smoke_state.release_calls != 1) {
    smoke_state.rejected_before_release_calls += 1;
    return;
  }

  destination->output[0] = PHIL_REJECTED_TAG;
  destination->output[1] = reason_code;
  destination->output_length = PHIL_REJECTED_RESPONSE_BYTES;
  smoke_state.rejected_calls += 1;
}

void phil_buffer_release(void *payload) {
  smoke_state.release_calls += 1;
  if (payload != smoke_state.last_payload || payload == NULL) {
    smoke_state.invalid_release_calls += 1;
    return;
  }
  free(payload);
  smoke_state.last_payload = NULL;
}

bool phil_runtime_send_exact(void) {
  return true;
}

bool phil_branch_condition(void) {
  return true;
}

void phil_cleanup(void) {}

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
PHIL_NOOP_CALL(phil_call_send_Hello)
PHIL_NOOP_CALL(phil_call_receive_version_unsupported_label)
PHIL_NOOP_CALL(phil_call_send_Begin)
PHIL_NOOP_CALL(phil_call_receive_proceed_reject_label)
PHIL_NOOP_CALL(phil_call_should_cancel_upload)
PHIL_NOOP_CALL(phil_call_select_cancel)
PHIL_NOOP_CALL(phil_call_select_payload)
PHIL_NOOP_CALL(phil_call_receive_accepted_rejected_label)
