#include "storage_v1.h"

#include <openssl/crypto.h>
#include <openssl/sha.h>
#include <stdlib.h>
#include <string.h>

#define PHIL_SMOKE_CAPACITY 4096u
#define PHIL_SHA256_BYTES 32u

struct phil_transport_impl {
  uint8_t bytes[PHIL_SMOKE_CAPACITY];
  size_t available;
  size_t cursor;
};

struct phil_begin_record_impl {
  uint64_t length;
  uint8_t digest[PHIL_SHA256_BYTES];
};

struct phil_payload_impl {
  size_t length;
  uint8_t bytes[];
};

struct phil_upload_id_impl {
  uint8_t opaque_tag[16];
};

struct phil_smoke_state {
  struct phil_transport_impl transport;
  struct phil_begin_record_impl begin_record;
  struct phil_upload_id_impl upload_id;
  struct phil_payload_impl *last_payload;
  uint8_t stored_bytes[PHIL_SMOKE_CAPACITY];
  size_t stored_length;
  size_t last_payload_length;
  uint8_t configured_store_status;
  unsigned exact_receive_calls;
  unsigned digest_calls;
  unsigned store_calls;
  unsigned release_calls;
  unsigned accepted_calls;
  unsigned invalid_transport_calls;
  unsigned invalid_digest_subject_calls;
  unsigned invalid_store_owner_calls;
  unsigned invalid_release_calls;
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

void *phil_smoke_configure_storage(
    const uint8_t *bytes,
    size_t available,
    uint64_t requested_length,
    const uint8_t expected_digest[32],
    uint8_t store_status) {
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
  smoke_state.configured_store_status = store_status;
  memset(smoke_state.upload_id.opaque_tag, 0x5a, sizeof(smoke_state.upload_id.opaque_tag));
  return &smoke_state.transport;
}

static bool common_store_observation(size_t expected_length) {
  return smoke_state.exact_receive_calls == 1
      && smoke_state.digest_calls == 1
      && smoke_state.store_calls == 1
      && smoke_state.release_calls == 0
      && smoke_state.invalid_transport_calls == 0
      && smoke_state.invalid_digest_subject_calls == 0
      && smoke_state.invalid_store_owner_calls == 0
      && smoke_state.invalid_release_calls == 0
      && smoke_state.last_payload == NULL
      && smoke_state.last_payload_length == expected_length
      && smoke_state.last_payload_matches_input
      && smoke_state.last_digest_result;
}

bool phil_smoke_storage_success_observed(const uint8_t *expected, size_t length) {
  return common_store_observation(length)
      && smoke_state.accepted_calls == 1
      && smoke_state.stored_length == length
      && (length == 0 || memcmp(smoke_state.stored_bytes, expected, length) == 0);
}

bool phil_smoke_storage_failure_observed(size_t length) {
  return common_store_observation(length)
      && smoke_state.accepted_calls == 0
      && smoke_state.stored_length == 0;
}

bool phil_smoke_storage_reserved_status_observed(size_t length) {
  return common_store_observation(length)
      && smoke_state.accepted_calls == 0
      && smoke_state.stored_length == 0;
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

  if (length > PHIL_SMOKE_CAPACITY) {
    requested = PHIL_SMOKE_CAPACITY + 1u;
  } else {
    requested = (size_t) length;
  }

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
  struct phil_store_result result;
  struct phil_payload_impl *payload = payload_handle;

  smoke_state.store_calls += 1;
  if (payload != smoke_state.last_payload || payload == NULL) {
    smoke_state.invalid_store_owner_calls += 1;
    result.status = 0;
    result.upload_id = NULL;
    return result;
  }

  if (smoke_state.configured_store_status == 1) {
    if (payload->length > PHIL_SMOKE_CAPACITY) {
      abort();
    }
    if (payload->length != 0) {
      memcpy(smoke_state.stored_bytes, payload->bytes, payload->length);
    }
    smoke_state.stored_length = payload->length;
  }

  free(payload);
  smoke_state.last_payload = NULL;

  result.status = smoke_state.configured_store_status;
  if (result.status == 1) {
    result.upload_id = &smoke_state.upload_id;
  } else if (result.status == 2) {
    /* Fault injection: consumer must still reject a reserved status even if a
       non-null ID is supplied. This is intentionally not a conforming result. */
    result.upload_id = &smoke_state.upload_id;
  } else {
    result.upload_id = NULL;
  }
  return result;
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
PHIL_NOOP_CALL(phil_call_select_rejected)
PHIL_NOOP_CALL(phil_call_send_Hello)
PHIL_NOOP_CALL(phil_call_receive_version_unsupported_label)
PHIL_NOOP_CALL(phil_call_send_Begin)
PHIL_NOOP_CALL(phil_call_receive_proceed_reject_label)
PHIL_NOOP_CALL(phil_call_should_cancel_upload)
PHIL_NOOP_CALL(phil_call_select_cancel)
PHIL_NOOP_CALL(phil_call_select_payload)
PHIL_NOOP_CALL(phil_call_receive_accepted_rejected_label)

void phil_call_select_accepted(void) {
  smoke_state.accepted_calls += 1;
}
