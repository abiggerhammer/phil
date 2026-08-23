#ifndef PHIL_PHASE0_FINAL_RESPONSE_RECEIVE_V1_H
#define PHIL_PHASE0_FINAL_RESPONSE_RECEIVE_V1_H

#include <stdbool.h>
#include <stddef.h>
#include <stdint.h>

struct phil_recognized_record_result { uint8_t status; void *record; };
struct phil_exact_receive_result { uint8_t status; void *payload; };
struct phil_store_result { uint8_t status; void *upload_id; };

bool phil_runtime_recognize_Hello(void);
struct phil_recognized_record_result phil_runtime_recognize_Begin(void);
bool phil_runtime_validate_HelloPolicy(void);
bool phil_runtime_validate_BeginPolicy(void);
bool phil_runtime_refine_selected_version(void);
struct phil_exact_receive_result phil_runtime_receive_exact_u64(void *transport, uint64_t length);
bool phil_runtime_send_exact(void);
bool phil_runtime_digest_validate(void *begin_record, void *payload);
struct phil_store_result phil_runtime_store(void *payload);
void phil_runtime_select_accepted(void *transport, void *upload_id);
void phil_runtime_select_rejected(void *transport, uint8_t reason);
uint64_t phil_record_Begin_get_length(void *record);
void phil_buffer_release(void *payload);

bool phil_runtime_receive_final_response(void *transport, void *upload_id_out);
void phil_runtime_record_upload_id(void *upload_id);

bool phil_branch_condition(void);
void phil_cleanup(void);
void phil_call_receive_frame_Hello(void);
void phil_call_choose_supported(void);
void phil_call_select_unsupported(void);
void phil_call_select_version(void);
void phil_call_receive_frame_Begin(void);
void phil_call_select_reject(void);
void phil_call_select_proceed(void);
void phil_call_receive_payload_cancel_label(void);
void phil_call_send_Hello(void);
void phil_call_receive_version_unsupported_label(void);
void phil_call_send_Begin(void);
void phil_call_receive_proceed_reject_label(void);
void phil_call_should_cancel_upload(void);
void phil_call_select_cancel(void);
void phil_call_select_payload(void);

void *phil_smoke_configure_final_response(const uint8_t *bytes, size_t length);
bool phil_smoke_accepted_observed(const uint8_t token[16]);
bool phil_smoke_rejected_observed(void);

#endif
