#ifndef PHIL_PHASE0_INTEGRATED_UPLOAD_V1_H
#define PHIL_PHASE0_INTEGRATED_UPLOAD_V1_H

#include "control_codec_v1.h"

#include <stdbool.h>
#include <stddef.h>
#include <stdint.h>

struct phil_exact_receive_result {
  uint8_t status;
  void *payload;
};

/* Remaining compiler-visible runtime ABI used by control-codec-v1 LLVM. */
void *phil_record_Hello_get_versions(void *hello_record);
uint64_t phil_record_Begin_get_length(void *begin_record);

bool phil_runtime_choose_supported(
    void *server_supported,
    void *offered_versions,
    uint16_t *selected_version_out);
void phil_runtime_select_unsupported(void *transport);
void phil_runtime_select_version(void *transport, uint16_t selected_version);
bool phil_runtime_receive_version_choice(
    void *transport,
    uint16_t *selected_version_out);

bool phil_runtime_validate_hello_policy(
    void *policy_context,
    void *hello_record,
    void **rejection_reason_out);
void phil_runtime_fail_hello_policy(void *transport, void *rejection_reason);

bool phil_runtime_validate_begin_policy(
    void *policy_context,
    void *begin_record,
    uint8_t *rejection_reason_out);
void phil_runtime_select_begin_policy_reject(
    void *transport,
    uint8_t rejection_reason);
void phil_runtime_select_begin_policy_proceed(void *transport);
bool phil_runtime_receive_begin_policy_choice(
    void *transport,
    uint8_t *rejection_reason_out);

void phil_runtime_select_payload_cancel(void *transport, uint8_t choice);
bool phil_runtime_receive_payload_cancel(void *transport);

void phil_runtime_send_exact(void *transport, void *payload_owner);
struct phil_exact_receive_result phil_runtime_receive_exact_u64(
    void *transport,
    uint64_t length);
bool phil_runtime_digest_validate(void *begin_record, void *payload);
void phil_buffer_release(void *payload);

uint8_t phil_runtime_store_with_error(
    void *payload,
    void **upload_id_out,
    void **storage_error_out);
void phil_runtime_fail_storage(void *transport, void *storage_error);

void phil_runtime_select_accepted(void *transport, void *upload_id);
void phil_runtime_select_rejected(void *transport, uint8_t reason);
bool phil_runtime_receive_final_response(void *transport, void **upload_id_out);
void phil_runtime_record_upload_id(void *upload_id);

void phil_call_should_cancel_upload(void);
bool phil_branch_condition(void);
void phil_cleanup(void);

/* Native demonstrator controls. These are fixture APIs, not Phil runtime ABI. */
enum phil_integrated_v1_scenario {
  PHIL_INTEGRATED_V1_ACCEPT = 1,
  PHIL_INTEGRATED_V1_DIGEST_REJECT = 2,
  PHIL_INTEGRATED_V1_CANCEL = 3
};

int phil_integrated_v1_prepare(
    enum phil_integrated_v1_scenario scenario,
    const uint8_t *payload_bytes,
    size_t payload_length);
void phil_integrated_v1_destroy(void);
void *phil_integrated_v1_transport(void);
void *phil_integrated_v1_client_payload(void);
void *phil_integrated_v1_policy_context(void);
void *phil_integrated_v1_server_supported_versions(void);
void phil_integrated_v1_enter_client(void);
void phil_integrated_v1_enter_server(void);
void phil_integrated_v1_wait_client_version_receive(void);
bool phil_integrated_v1_observed(enum phil_integrated_v1_scenario scenario);

#endif
