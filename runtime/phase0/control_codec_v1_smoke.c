#include "control_codec_v1.h"

#include <string.h>

static const uint8_t hello_fixture[] = {
  0x50u, 0x48u, 0x49u, 0x4cu, 0x01u, 0x01u, 0x00u, 0x08u,
  0x00u, 0x03u, 0x00u, 0x01u, 0x00u, 0x03u, 0x12u, 0x34u
};

static const uint8_t begin_fixture[] = {
  0x50u, 0x48u, 0x49u, 0x4cu, 0x01u, 0x02u, 0x00u, 0x2du,
  0x01u, 0x02u, 0x03u, 0x04u, 0x05u, 0x06u, 0x07u, 0x08u,
  0x03u, 0x62u, 0x69u, 0x6eu, 0x01u,
  0x00u, 0x01u, 0x02u, 0x03u, 0x04u, 0x05u, 0x06u, 0x07u,
  0x08u, 0x09u, 0x0au, 0x0bu, 0x0cu, 0x0du, 0x0eu, 0x0fu,
  0x10u, 0x11u, 0x12u, 0x13u, 0x14u, 0x15u, 0x16u, 0x17u,
  0x18u, 0x19u, 0x1au, 0x1bu, 0x1cu, 0x1du, 0x1eu, 0x1fu
};

static int bytes_equal(const uint8_t *actual, const uint8_t *expected, size_t length) {
  return actual != NULL && memcmp(actual, expected, length) == 0;
}

static int test_hello_fixture(void) {
  const uint16_t version_items[] = {1u, 3u, 0x1234u};
  void *transport = phil_codec_v1_transport_new();
  void *versions = phil_codec_v1_version_set_new(version_items, 3u);
  void *pending = NULL;
  void *frame = NULL;
  void *record = NULL;
  void *reason = NULL;
  void *raw;
  uint8_t status;
  int ok;

  if (transport == NULL || versions == NULL) {
    return 0;
  }
  phil_runtime_send_hello(transport, versions);
  ok = phil_codec_v1_transport_size(transport) == sizeof(hello_fixture)
      && bytes_equal(
          phil_codec_v1_transport_bytes(transport),
          hello_fixture,
          sizeof(hello_fixture));
  if (!ok) {
    phil_codec_v1_version_set_free(versions);
    phil_codec_v1_transport_free(transport);
    return 0;
  }

  phil_runtime_receive_frame_Hello(transport, &pending, &frame);
  raw = phil_runtime_frame_borrow_view_Hello(frame);
  status = phil_runtime_recognize_Hello(pending, raw, &record, &reason);
  ok = status == 1u
      && record != NULL
      && reason == NULL
      && phil_codec_v1_hello_version_count(record) == 3u
      && phil_codec_v1_hello_version_at(record, 0u) == 1u
      && phil_codec_v1_hello_version_at(record, 1u) == 3u
      && phil_codec_v1_hello_version_at(record, 2u) == 0x1234u;
  if (ok) {
    phil_runtime_commit_ingress_Hello(transport, pending);
    ok = phil_codec_v1_transport_read_offset(transport) == sizeof(hello_fixture);
  } else {
    if (pending != NULL && frame != NULL) {
      phil_runtime_destroy_pending_Hello(pending, frame);
    }
  }

  phil_codec_v1_record_free(record);
  phil_codec_v1_reason_free(reason);
  phil_codec_v1_version_set_free(versions);
  phil_codec_v1_transport_free(transport);
  return ok;
}

static int test_begin_fixture(void) {
  const uint8_t kind_bytes[] = {0x62u, 0x69u, 0x6eu};
  uint8_t digest_bytes[32];
  void *transport = phil_codec_v1_transport_new();
  void *kind;
  void *digest;
  void *pending = NULL;
  void *frame = NULL;
  void *record = NULL;
  void *reason = NULL;
  void *raw;
  uint8_t status;
  size_t index;
  int ok;

  for (index = 0u; index < sizeof(digest_bytes); ++index) {
    digest_bytes[index] = (uint8_t)index;
  }
  kind = phil_codec_v1_kind_new(kind_bytes, sizeof(kind_bytes));
  digest = phil_codec_v1_digest_new(digest_bytes);
  if (transport == NULL || kind == NULL || digest == NULL) {
    return 0;
  }

  phil_runtime_send_begin_sha256(
      transport,
      UINT64_C(0x0102030405060708),
      kind,
      digest);
  ok = phil_codec_v1_transport_size(transport) == sizeof(begin_fixture)
      && bytes_equal(
          phil_codec_v1_transport_bytes(transport),
          begin_fixture,
          sizeof(begin_fixture));
  if (!ok) {
    phil_codec_v1_kind_free(kind);
    phil_codec_v1_digest_free(digest);
    phil_codec_v1_transport_free(transport);
    return 0;
  }

  phil_runtime_receive_frame_Begin(transport, &pending, &frame);
  raw = phil_runtime_frame_borrow_view_Begin(frame);
  status = phil_runtime_recognize_Begin(pending, raw, &record, &reason);
  ok = status == 1u
      && record != NULL
      && reason == NULL
      && phil_codec_v1_begin_length(record) == UINT64_C(0x0102030405060708)
      && phil_codec_v1_begin_kind_length(record) == sizeof(kind_bytes)
      && bytes_equal(
          phil_codec_v1_begin_kind_bytes(record),
          kind_bytes,
          sizeof(kind_bytes))
      && bytes_equal(
          phil_codec_v1_begin_digest_bytes(record),
          digest_bytes,
          sizeof(digest_bytes));
  if (ok) {
    phil_runtime_commit_ingress_Begin(transport, pending);
    ok = phil_codec_v1_transport_read_offset(transport) == sizeof(begin_fixture);
  } else {
    if (pending != NULL && frame != NULL) {
      phil_runtime_destroy_pending_Begin(pending, frame);
    }
  }

  phil_codec_v1_record_free(record);
  phil_codec_v1_reason_free(reason);
  phil_codec_v1_kind_free(kind);
  phil_codec_v1_digest_free(digest);
  phil_codec_v1_transport_free(transport);
  return ok;
}

static int test_concatenated_commit_boundaries(void) {
  const uint16_t version_items[] = {1u};
  const uint8_t kind_bytes[] = {0x78u};
  uint8_t digest_bytes[32] = {0u};
  void *transport = phil_codec_v1_transport_new();
  void *versions = phil_codec_v1_version_set_new(version_items, 1u);
  void *kind = phil_codec_v1_kind_new(kind_bytes, sizeof(kind_bytes));
  void *digest = phil_codec_v1_digest_new(digest_bytes);
  void *pending = NULL;
  void *frame = NULL;
  void *record = NULL;
  void *reason = NULL;
  size_t first_size = 0u;
  size_t total_size;
  int ok;

  if (transport == NULL || versions == NULL || kind == NULL || digest == NULL) {
    return 0;
  }
  phil_runtime_send_hello(transport, versions);
  if (phil_codec_v1_validate_frame_bytes(
        phil_codec_v1_transport_bytes(transport),
        phil_codec_v1_transport_size(transport),
        PHIL_CODEC_V1_TAG_HELLO,
        &first_size) != 0) {
    return 0;
  }
  phil_runtime_send_begin_sha256(transport, 9u, kind, digest);
  total_size = phil_codec_v1_transport_size(transport);

  phil_runtime_receive_frame_Hello(transport, &pending, &frame);
  if (phil_runtime_recognize_Hello(
        pending,
        phil_runtime_frame_borrow_view_Hello(frame),
        &record,
        &reason) != 1u) {
    return 0;
  }
  phil_codec_v1_record_free(record);
  record = NULL;
  phil_runtime_commit_ingress_Hello(transport, pending);
  ok = phil_codec_v1_transport_read_offset(transport) == first_size;
  if (!ok) {
    return 0;
  }

  pending = NULL;
  frame = NULL;
  phil_runtime_receive_frame_Begin(transport, &pending, &frame);
  if (phil_runtime_recognize_Begin(
        pending,
        phil_runtime_frame_borrow_view_Begin(frame),
        &record,
        &reason) != 1u) {
    return 0;
  }
  phil_codec_v1_record_free(record);
  phil_runtime_commit_ingress_Begin(transport, pending);
  ok = phil_codec_v1_transport_read_offset(transport) == total_size;

  phil_codec_v1_reason_free(reason);
  phil_codec_v1_version_set_free(versions);
  phil_codec_v1_kind_free(kind);
  phil_codec_v1_digest_free(digest);
  phil_codec_v1_transport_free(transport);
  return ok;
}

static int test_frame_rejection(void) {
  uint8_t mutated[sizeof(hello_fixture)];
  size_t frame_size = 0u;

  memcpy(mutated, hello_fixture, sizeof(mutated));
  mutated[0] ^= 0x01u;
  if (phil_codec_v1_validate_frame_bytes(
        mutated,
        sizeof(mutated),
        PHIL_CODEC_V1_TAG_HELLO,
        &frame_size) == 0) {
    return 0;
  }

  memcpy(mutated, hello_fixture, sizeof(mutated));
  mutated[4] = 0x02u;
  if (phil_codec_v1_validate_frame_bytes(
        mutated,
        sizeof(mutated),
        PHIL_CODEC_V1_TAG_HELLO,
        &frame_size) == 0) {
    return 0;
  }

  if (phil_codec_v1_validate_frame_bytes(
        hello_fixture,
        sizeof(hello_fixture),
        PHIL_CODEC_V1_TAG_BEGIN,
        &frame_size) == 0) {
    return 0;
  }

  return phil_codec_v1_validate_frame_bytes(
      hello_fixture,
      sizeof(hello_fixture) - 1u,
      PHIL_CODEC_V1_TAG_HELLO,
      &frame_size) != 0;
}

static int test_hello_recognition_failure(void) {
  const uint8_t bad_hello[] = {
    0x50u, 0x48u, 0x49u, 0x4cu, 0x01u, 0x01u, 0x00u, 0x06u,
    0x00u, 0x02u, 0x00u, 0x01u, 0x00u, 0x01u
  };
  void *transport = phil_codec_v1_transport_new();
  void *pending = NULL;
  void *frame = NULL;
  void *record = NULL;
  void *reason = NULL;
  uint8_t status;
  int ok;

  if (transport == NULL
      || phil_codec_v1_transport_append(transport, bad_hello, sizeof(bad_hello)) != 0) {
    return 0;
  }
  phil_runtime_receive_frame_Hello(transport, &pending, &frame);
  status = phil_runtime_recognize_Hello(
      pending,
      phil_runtime_frame_borrow_view_Hello(frame),
      &record,
      &reason);
  ok = status == 0u
      && record == NULL
      && reason != NULL
      && phil_codec_v1_recognition_reason_code(reason) == 3u
      && phil_codec_v1_transport_read_offset(transport) == 0u;
  if (ok) {
    phil_runtime_fail_recognition_Hello(pending, reason);
  }
  phil_runtime_destroy_pending_Hello(pending, frame);
  phil_codec_v1_reason_free(reason);
  phil_codec_v1_transport_free(transport);
  return ok;
}

static int test_begin_recognition_failure(void) {
  uint8_t bad_begin[sizeof(begin_fixture)];
  void *transport = phil_codec_v1_transport_new();
  void *pending = NULL;
  void *frame = NULL;
  void *record = NULL;
  void *reason = NULL;
  uint8_t status;
  int ok;

  memcpy(bad_begin, begin_fixture, sizeof(bad_begin));
  bad_begin[20] = 0x02u;
  if (transport == NULL
      || phil_codec_v1_transport_append(transport, bad_begin, sizeof(bad_begin)) != 0) {
    return 0;
  }
  phil_runtime_receive_frame_Begin(transport, &pending, &frame);
  status = phil_runtime_recognize_Begin(
      pending,
      phil_runtime_frame_borrow_view_Begin(frame),
      &record,
      &reason);
  ok = status == 0u
      && record == NULL
      && reason != NULL
      && phil_codec_v1_recognition_reason_code(reason) == 3u
      && phil_codec_v1_transport_read_offset(transport) == 0u;
  if (ok) {
    phil_runtime_fail_recognition_Begin(pending, reason);
  }
  phil_runtime_destroy_pending_Begin(pending, frame);
  phil_codec_v1_reason_free(reason);
  phil_codec_v1_transport_free(transport);
  return ok;
}

static int test_existing_operand_identity_helpers(void) {
  const uint8_t kind_bytes[] = {0xa5u, 0x5au};
  uint8_t digest_bytes[32] = {0u};
  void *transport = phil_codec_v1_transport_new();
  void *kind = phil_codec_v1_kind_new(kind_bytes, sizeof(kind_bytes));
  void *digest = phil_codec_v1_digest_new(digest_bytes);
  void *payload = phil_codec_v1_payload_new(1234u, kind, digest);
  void *versions = phil_runtime_supported_versions();
  int ok = transport != NULL
      && kind != NULL
      && digest != NULL
      && payload != NULL
      && phil_runtime_payload_length(payload) == 1234u
      && phil_runtime_payload_kind(payload) == kind
      && phil_runtime_sha256(payload) == digest
      && phil_runtime_refine_selected_version_with_set(transport, versions, 1u)
      && !phil_runtime_refine_selected_version_with_set(transport, versions, 2u);

  phil_codec_v1_payload_free(payload);
  phil_codec_v1_kind_free(kind);
  phil_codec_v1_digest_free(digest);
  phil_codec_v1_transport_free(transport);
  return ok;
}

int phil_control_codec_v1_smoke(void) {
  return test_hello_fixture()
      && test_begin_fixture()
      && test_concatenated_commit_boundaries()
      && test_frame_rejection()
      && test_hello_recognition_failure()
      && test_begin_recognition_failure()
      && test_existing_operand_identity_helpers()
    ? 0
    : 1;
}
