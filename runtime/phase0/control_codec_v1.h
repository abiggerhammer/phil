#ifndef PHIL_PHASE0_CONTROL_CODEC_V1_H
#define PHIL_PHASE0_CONTROL_CODEC_V1_H

#include <stdbool.h>
#include <stddef.h>
#include <stdint.h>

#define PHIL_CODEC_V1_HEADER_SIZE 8u
#define PHIL_CODEC_V1_TAG_HELLO 0x01u
#define PHIL_CODEC_V1_TAG_BEGIN 0x02u
#define PHIL_CODEC_V1_DIGEST_SHA256 0x01u

/* Compiler-visible runtime ABI inherited by control-codec-v1. */
void *phil_runtime_supported_versions(void);
uint64_t phil_runtime_payload_length(void *payload_owner);
void *phil_runtime_payload_kind(void *payload_owner);
void *phil_runtime_sha256(void *payload_owner);
void phil_runtime_send_hello(void *transport, void *versions);
void phil_runtime_send_begin_sha256(
    void *transport,
    uint64_t length,
    void *kind,
    void *digest);
bool phil_runtime_refine_selected_version_with_set(
    void *transport,
    void *versions,
    uint16_t selected);

void phil_runtime_receive_frame_Hello(
    void *transport,
    void **pending_out,
    void **frame_out);
void phil_runtime_receive_frame_Begin(
    void *transport,
    void **pending_out,
    void **frame_out);
void *phil_runtime_frame_borrow_view_Hello(void *frame);
void *phil_runtime_frame_borrow_view_Begin(void *frame);
uint8_t phil_runtime_recognize_Hello(
    void *pending,
    void *raw_view,
    void **record_out,
    void **reason_out);
uint8_t phil_runtime_recognize_Begin(
    void *pending,
    void *raw_view,
    void **record_out,
    void **reason_out);
void phil_runtime_commit_ingress_Hello(void *transport, void *pending);
void phil_runtime_commit_ingress_Begin(void *transport, void *pending);
void phil_runtime_fail_recognition_Hello(void *pending, void *reason);
void phil_runtime_fail_recognition_Begin(void *pending, void *reason);
void phil_runtime_destroy_pending_Hello(void *pending, void *frame);
void phil_runtime_destroy_pending_Begin(void *pending, void *frame);

/* Native fixture/support API. These helpers are not compiler ABI primitives. */
void *phil_codec_v1_transport_new(void);
void phil_codec_v1_transport_free(void *transport);
size_t phil_codec_v1_transport_size(void *transport);
size_t phil_codec_v1_transport_read_offset(void *transport);
const uint8_t *phil_codec_v1_transport_bytes(void *transport);
int phil_codec_v1_transport_append(void *transport, const uint8_t *bytes, size_t length);

void *phil_codec_v1_version_set_new(const uint16_t *versions, size_t count);
void phil_codec_v1_version_set_free(void *versions);
void *phil_codec_v1_kind_new(const uint8_t *bytes, size_t length);
void phil_codec_v1_kind_free(void *kind);
void *phil_codec_v1_digest_new(const uint8_t bytes[32]);
void phil_codec_v1_digest_free(void *digest);
void *phil_codec_v1_payload_new(uint64_t length, void *kind, void *digest);
void phil_codec_v1_payload_free(void *payload);

int phil_codec_v1_validate_frame_bytes(
    const uint8_t *bytes,
    size_t available,
    uint8_t expected_tag,
    size_t *frame_size_out);

size_t phil_codec_v1_hello_version_count(void *record);
uint16_t phil_codec_v1_hello_version_at(void *record, size_t index);
uint64_t phil_codec_v1_begin_length(void *record);
size_t phil_codec_v1_begin_kind_length(void *record);
const uint8_t *phil_codec_v1_begin_kind_bytes(void *record);
const uint8_t *phil_codec_v1_begin_digest_bytes(void *record);
uint8_t phil_codec_v1_recognition_reason_code(void *reason);
void phil_codec_v1_record_free(void *record);
void phil_codec_v1_reason_free(void *reason);

int phil_control_codec_v1_smoke(void);

#endif
