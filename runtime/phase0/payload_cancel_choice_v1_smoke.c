#include "payload_cancel_choice_v1.h"

#include <stdlib.h>
#include <string.h>

#define PHIL_FINAL_BYTES_MAX 32u
#define PHIL_UPLOAD_ID_BYTES 16u

struct phil_transport_impl {
  bool has_choice;
  uint8_t incoming_choice;
  bool selected;
  uint8_t selected_choice;
  uint8_t final_bytes[PHIL_FINAL_BYTES_MAX];
  size_t final_length;
};

struct phil_upload_id_impl {
  uint8_t token[PHIL_UPLOAD_ID_BYTES];
};

enum phil_smoke_mode {
  PHIL_SMOKE_NONE = 0,
  PHIL_SMOKE_CLIENT = 1,
  PHIL_SMOKE_SERVER = 2
};

struct phil_smoke_state {
  enum phil_smoke_mode mode;
  bool client_cancel;
  struct phil_transport_impl client_transport;
  struct phil_transport_impl server_transport;
  struct phil_upload_id_impl upload_id;
  uint8_t payload_storage;
  unsigned branch_calls;
  unsigned select_choice_calls;
  unsigned receive_choice_calls;
  unsigned final_receive_calls;
  unsigned record_calls;
};

static struct phil_smoke_state smoke_state;

static void reset_state(void) {
  memset(&smoke_state, 0, sizeof(smoke_state));
}

void *phil_smoke_configure_client(
    bool cancel_upload,
    const uint8_t *final_bytes,
    size_t final_length) {
  reset_state();
  smoke_state.mode = PHIL_SMOKE_CLIENT;
  smoke_state.client_cancel = cancel_upload;
  if (final_length > PHIL_FINAL_BYTES_MAX) abort();
  if (final_length != 0u) memcpy(smoke_state.client_transport.final_bytes, final_bytes, final_length);
  smoke_state.client_transport.final_length = final_length;
  return &smoke_state.client_transport;
}

void *phil_smoke_configure_server(uint8_t incoming_choice) {
  reset_state();
  smoke_state.mode = PHIL_SMOKE_SERVER;
  smoke_state.server_transport.has_choice = true;
  smoke_state.server_transport.incoming_choice = incoming_choice;
  return &smoke_state.server_transport;
}

void *phil_smoke_configure_server_empty(void) {
  reset_state();
  smoke_state.mode = PHIL_SMOKE_SERVER;
  smoke_state.server_transport.has_choice = false;
  return &smoke_state.server_transport;
}

bool phil_smoke_client_choice_observed(uint8_t expected_choice) {
  return smoke_state.mode == PHIL_SMOKE_CLIENT
      && smoke_state.select_choice_calls == 1u
      && smoke_state.client_transport.selected
      && smoke_state.client_transport.selected_choice == expected_choice;
}

bool phil_smoke_server_choice_observed(uint8_t expected_choice) {
  return smoke_state.mode == PHIL_SMOKE_SERVER
      && smoke_state.receive_choice_calls == 1u
      && smoke_state.server_transport.has_choice
      && smoke_state.server_transport.incoming_choice == expected_choice;
}

void phil_runtime_select_payload_cancel(void *transport, uint8_t choice) {
  struct phil_transport_impl *target = transport;
  if (target != &smoke_state.client_transport) abort();
  if (choice != 0x00u && choice != 0x01u) abort();
  target->selected = true;
  target->selected_choice = choice;
  smoke_state.select_choice_calls += 1u;
}

bool phil_runtime_receive_payload_cancel(void *transport) {
  struct phil_transport_impl *source = transport;
  if (source != &smoke_state.server_transport) abort();
  smoke_state.receive_choice_calls += 1u;
  if (!source->has_choice) abort();
  if (source->incoming_choice == 0x01u) return true;
  if (source->incoming_choice == 0x00u) return false;
  abort();
}

bool phil_runtime_receive_final_response(void *transport, void *upload_id_out) {
  struct phil_transport_impl *source = transport;
  void **out = upload_id_out;
  smoke_state.final_receive_calls += 1u;
  if (source != &smoke_state.client_transport || out == NULL) abort();
  if (source->final_length == 17u && source->final_bytes[0] == 0x01u) {
    memcpy(smoke_state.upload_id.token, source->final_bytes + 1, PHIL_UPLOAD_ID_BYTES);
    *out = &smoke_state.upload_id;
    return true;
  }
  if (source->final_length == 2u
      && source->final_bytes[0] == 0x00u
      && source->final_bytes[1] == 0x01u) {
    return false;
  }
  abort();
}

void phil_runtime_record_upload_id(void *upload_id) {
  if (upload_id != &smoke_state.upload_id) abort();
  smoke_state.record_calls += 1u;
}

bool phil_branch_condition(void) {
  unsigned index = smoke_state.branch_calls++;
  if (smoke_state.mode == PHIL_SMOKE_CLIENT) {
    if (index < 2u) return true;
    if (index == 2u) return smoke_state.client_cancel;
    abort();
  }
  if (smoke_state.mode == PHIL_SMOKE_SERVER) {
    if (index == 0u) return true;
    abort();
  }
  abort();
}

bool phil_runtime_recognize_Hello(void) { return true; }
struct phil_recognized_record_result phil_runtime_recognize_Begin(void) {
  struct phil_recognized_record_result result = { 1u, &smoke_state.payload_storage };
  return result;
}
bool phil_runtime_validate_HelloPolicy(void) { return true; }
bool phil_runtime_validate_BeginPolicy(void) { return true; }
bool phil_runtime_refine_selected_version(void) { return true; }
struct phil_exact_receive_result phil_runtime_receive_exact_u64(void *transport, uint64_t length) {
  struct phil_exact_receive_result result;
  (void) length;
  if (transport != &smoke_state.server_transport) abort();
  result.status = 1u;
  result.payload = &smoke_state.payload_storage;
  return result;
}
bool phil_runtime_send_exact(void) { return true; }
bool phil_runtime_digest_validate(void *begin_record, void *payload) {
  (void) begin_record;
  return payload == &smoke_state.payload_storage;
}
struct phil_store_result phil_runtime_store(void *payload) {
  struct phil_store_result result;
  if (payload != &smoke_state.payload_storage) abort();
  result.status = 1u;
  result.upload_id = &smoke_state.upload_id;
  return result;
}
void phil_runtime_select_accepted(void *transport, void *upload_id) {
  if (transport != &smoke_state.server_transport || upload_id != &smoke_state.upload_id) abort();
}
void phil_runtime_select_rejected(void *transport, uint8_t reason) {
  (void) reason;
  if (transport != &smoke_state.server_transport) abort();
}
uint64_t phil_record_Begin_get_length(void *record) {
  if (record != &smoke_state.payload_storage) abort();
  return 0u;
}
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
PHIL_NOOP_CALL(phil_call_send_Hello)
PHIL_NOOP_CALL(phil_call_receive_version_unsupported_label)
PHIL_NOOP_CALL(phil_call_send_Begin)
PHIL_NOOP_CALL(phil_call_receive_proceed_reject_label)
PHIL_NOOP_CALL(phil_call_should_cancel_upload)
