#include "final_response_receive_v1.h"

#include <stdlib.h>
#include <string.h>

#define PHIL_ACCEPTED_BYTES 17u
#define PHIL_REJECTED_BYTES 2u
#define PHIL_UPLOAD_ID_BYTES 16u

struct phil_transport_impl {
  uint8_t bytes[32];
  size_t length;
};

struct phil_upload_id_impl {
  uint8_t token[PHIL_UPLOAD_ID_BYTES];
};

struct phil_smoke_state {
  struct phil_transport_impl transport;
  struct phil_upload_id_impl upload_id;
  uint8_t recorded_token[PHIL_UPLOAD_ID_BYTES];
  unsigned branch_calls;
  unsigned receive_calls;
  unsigned record_calls;
  unsigned accepted_decodes;
  unsigned rejected_decodes;
};

static struct phil_smoke_state smoke_state;

void *phil_smoke_configure_final_response(const uint8_t *bytes, size_t length) {
  if (length > sizeof(smoke_state.transport.bytes)) abort();
  memset(&smoke_state, 0, sizeof(smoke_state));
  if (length != 0) memcpy(smoke_state.transport.bytes, bytes, length);
  smoke_state.transport.length = length;
  return &smoke_state.transport;
}

bool phil_smoke_accepted_observed(const uint8_t token[16]) {
  return smoke_state.branch_calls == 3
      && smoke_state.receive_calls == 1
      && smoke_state.record_calls == 1
      && smoke_state.accepted_decodes == 1
      && smoke_state.rejected_decodes == 0
      && memcmp(smoke_state.recorded_token, token, PHIL_UPLOAD_ID_BYTES) == 0;
}

bool phil_smoke_rejected_observed(void) {
  return smoke_state.branch_calls == 3
      && smoke_state.receive_calls == 1
      && smoke_state.record_calls == 0
      && smoke_state.accepted_decodes == 0
      && smoke_state.rejected_decodes == 1;
}

bool phil_runtime_receive_final_response(void *transport, void *upload_id_out) {
  struct phil_transport_impl *source = transport;
  void **out = upload_id_out;
  smoke_state.receive_calls += 1;
  if (source != &smoke_state.transport || out == NULL) abort();
  if (source->length == PHIL_ACCEPTED_BYTES && source->bytes[0] == 0x01u) {
    memcpy(smoke_state.upload_id.token, source->bytes + 1, PHIL_UPLOAD_ID_BYTES);
    *out = &smoke_state.upload_id;
    smoke_state.accepted_decodes += 1;
    return true;
  }
  if (source->length == PHIL_REJECTED_BYTES
      && source->bytes[0] == 0x00u
      && source->bytes[1] == 0x01u) {
    smoke_state.rejected_decodes += 1;
    return false;
  }
  abort();
}

void phil_runtime_record_upload_id(void *upload_id) {
  struct phil_upload_id_impl *value = upload_id;
  if (value != &smoke_state.upload_id) abort();
  memcpy(smoke_state.recorded_token, value->token, PHIL_UPLOAD_ID_BYTES);
  smoke_state.record_calls += 1;
}

bool phil_branch_condition(void) {
  static const bool decisions[3] = { true, true, false };
  unsigned index = smoke_state.branch_calls;
  smoke_state.branch_calls += 1;
  if (index >= 3) abort();
  return decisions[index];
}

bool phil_runtime_recognize_Hello(void) { return true; }
struct phil_recognized_record_result phil_runtime_recognize_Begin(void) {
  struct phil_recognized_record_result result = { 1u, NULL };
  return result;
}
bool phil_runtime_validate_HelloPolicy(void) { return true; }
bool phil_runtime_validate_BeginPolicy(void) { return true; }
bool phil_runtime_refine_selected_version(void) { return true; }
struct phil_exact_receive_result phil_runtime_receive_exact_u64(void *transport, uint64_t length) {
  (void) transport; (void) length;
  { struct phil_exact_receive_result result = { 0u, NULL }; return result; }
}
bool phil_runtime_send_exact(void) { return true; }
bool phil_runtime_digest_validate(void *begin_record, void *payload) {
  (void) begin_record; (void) payload; return true;
}
struct phil_store_result phil_runtime_store(void *payload) {
  (void) payload;
  { struct phil_store_result result = { 0u, NULL }; return result; }
}
void phil_runtime_select_accepted(void *transport, void *upload_id) { (void) transport; (void) upload_id; }
void phil_runtime_select_rejected(void *transport, uint8_t reason) { (void) transport; (void) reason; }
uint64_t phil_record_Begin_get_length(void *record) { (void) record; return 0; }
void phil_buffer_release(void *payload) { (void) payload; }
void phil_cleanup(void) {}

#define PHIL_NOOP_CALL(name) void name(void) {}
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
