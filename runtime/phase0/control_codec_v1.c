#include "control_codec_v1.h"

#include <stdlib.h>
#include <string.h>

#define PHIL_CODEC_V1_MAGIC_0 0x50u
#define PHIL_CODEC_V1_MAGIC_1 0x48u
#define PHIL_CODEC_V1_MAGIC_2 0x49u
#define PHIL_CODEC_V1_MAGIC_3 0x4cu
#define PHIL_CODEC_V1_VERSION 0x01u
#define PHIL_CODEC_V1_MAX_HELLO_VERSIONS 32766u

#define PHIL_CODEC_FRAME_OK 0
#define PHIL_CODEC_FRAME_NULL 1
#define PHIL_CODEC_FRAME_SHORT_HEADER 2
#define PHIL_CODEC_FRAME_MAGIC 3
#define PHIL_CODEC_FRAME_VERSION 4
#define PHIL_CODEC_FRAME_TAG 5
#define PHIL_CODEC_FRAME_TRUNCATED 6

#define PHIL_CODEC_HELLO_REASON_EMPTY 1u
#define PHIL_CODEC_HELLO_REASON_LENGTH 2u
#define PHIL_CODEC_HELLO_REASON_ORDER 3u
#define PHIL_CODEC_BEGIN_REASON_LENGTH 1u
#define PHIL_CODEC_BEGIN_REASON_KIND 2u
#define PHIL_CODEC_BEGIN_REASON_DIGEST_ALG 3u

struct PhilCodecVersionSet {
  size_t count;
  uint16_t *versions;
  int is_static;
};

struct PhilCodecKind {
  size_t length;
  uint8_t *bytes;
};

struct PhilCodecDigest {
  uint8_t bytes[32];
};

struct PhilCodecPayload {
  uint64_t length;
  struct PhilCodecKind *kind;
  struct PhilCodecDigest *digest;
};

struct PhilCodecTransport {
  uint8_t *bytes;
  size_t length;
  size_t capacity;
  size_t read_offset;
};

struct PhilCodecFrame {
  uint8_t tag;
  size_t length;
  uint8_t *bytes;
};

struct PhilCodecPending {
  uint8_t tag;
  struct PhilCodecTransport *transport;
  size_t start;
  size_t end;
  struct PhilCodecFrame *frame;
};

struct PhilCodecHelloRecord {
  uint8_t tag;
  size_t count;
  uint16_t *versions;
};

struct PhilCodecBeginRecord {
  uint8_t tag;
  uint64_t length;
  size_t kind_length;
  uint8_t *kind_bytes;
  uint8_t digest[32];
};

struct PhilCodecReason {
  uint8_t tag;
  uint8_t code;
};

static uint16_t default_version_items[] = {1u};
static struct PhilCodecVersionSet default_versions = {
  1u,
  default_version_items,
  1
};

static void codec_abort(void) {
  abort();
}

static void *checked_malloc(size_t size) {
  void *result = malloc(size);
  if (result == NULL) {
    codec_abort();
  }
  return result;
}

static uint16_t read_u16be(const uint8_t *bytes) {
  return (uint16_t)(((uint16_t)bytes[0] << 8) | (uint16_t)bytes[1]);
}

static uint64_t read_u64be(const uint8_t *bytes) {
  uint64_t result = 0u;
  size_t index;
  for (index = 0u; index < 8u; ++index) {
    result = (result << 8) | (uint64_t)bytes[index];
  }
  return result;
}

static void write_u16be(uint8_t *bytes, uint16_t value) {
  bytes[0] = (uint8_t)(value >> 8);
  bytes[1] = (uint8_t)(value & 0xffu);
}

static void write_u64be(uint8_t *bytes, uint64_t value) {
  size_t index;
  for (index = 0u; index < 8u; ++index) {
    bytes[7u - index] = (uint8_t)(value & 0xffu);
    value >>= 8;
  }
}

static void transport_reserve(struct PhilCodecTransport *transport, size_t additional) {
  size_t needed;
  size_t capacity;
  uint8_t *new_bytes;

  if (transport == NULL || additional > SIZE_MAX - transport->length) {
    codec_abort();
  }
  needed = transport->length + additional;
  if (needed <= transport->capacity) {
    return;
  }
  capacity = transport->capacity == 0u ? 64u : transport->capacity;
  while (capacity < needed) {
    if (capacity > SIZE_MAX / 2u) {
      capacity = needed;
      break;
    }
    capacity *= 2u;
  }
  new_bytes = realloc(transport->bytes, capacity);
  if (new_bytes == NULL) {
    codec_abort();
  }
  transport->bytes = new_bytes;
  transport->capacity = capacity;
}

static void transport_append_or_abort(
    struct PhilCodecTransport *transport,
    const uint8_t *bytes,
    size_t length) {
  if (transport == NULL || (length != 0u && bytes == NULL)) {
    codec_abort();
  }
  transport_reserve(transport, length);
  if (length != 0u) {
    memcpy(transport->bytes + transport->length, bytes, length);
  }
  transport->length += length;
}

static void append_header(
    struct PhilCodecTransport *transport,
    uint8_t tag,
    uint16_t payload_length) {
  uint8_t header[PHIL_CODEC_V1_HEADER_SIZE];
  header[0] = PHIL_CODEC_V1_MAGIC_0;
  header[1] = PHIL_CODEC_V1_MAGIC_1;
  header[2] = PHIL_CODEC_V1_MAGIC_2;
  header[3] = PHIL_CODEC_V1_MAGIC_3;
  header[4] = PHIL_CODEC_V1_VERSION;
  header[5] = tag;
  write_u16be(header + 6u, payload_length);
  transport_append_or_abort(transport, header, sizeof(header));
}

static int version_set_is_canonical(const struct PhilCodecVersionSet *set) {
  size_t index;
  if (set == NULL || set->count == 0u || set->count > PHIL_CODEC_V1_MAX_HELLO_VERSIONS) {
    return 0;
  }
  for (index = 1u; index < set->count; ++index) {
    if (set->versions[index - 1u] >= set->versions[index]) {
      return 0;
    }
  }
  return 1;
}

static struct PhilCodecReason *reason_new(uint8_t tag, uint8_t code) {
  struct PhilCodecReason *reason = checked_malloc(sizeof(*reason));
  reason->tag = tag;
  reason->code = code;
  return reason;
}

int phil_codec_v1_validate_frame_bytes(
    const uint8_t *bytes,
    size_t available,
    uint8_t expected_tag,
    size_t *frame_size_out) {
  size_t total;
  uint16_t payload_length;

  if (frame_size_out != NULL) {
    *frame_size_out = 0u;
  }
  if (bytes == NULL) {
    return PHIL_CODEC_FRAME_NULL;
  }
  if (available < PHIL_CODEC_V1_HEADER_SIZE) {
    return PHIL_CODEC_FRAME_SHORT_HEADER;
  }
  if (bytes[0] != PHIL_CODEC_V1_MAGIC_0
      || bytes[1] != PHIL_CODEC_V1_MAGIC_1
      || bytes[2] != PHIL_CODEC_V1_MAGIC_2
      || bytes[3] != PHIL_CODEC_V1_MAGIC_3) {
    return PHIL_CODEC_FRAME_MAGIC;
  }
  if (bytes[4] != PHIL_CODEC_V1_VERSION) {
    return PHIL_CODEC_FRAME_VERSION;
  }
  if (bytes[5] != expected_tag) {
    return PHIL_CODEC_FRAME_TAG;
  }
  payload_length = read_u16be(bytes + 6u);
  total = PHIL_CODEC_V1_HEADER_SIZE + (size_t)payload_length;
  if (available < total) {
    return PHIL_CODEC_FRAME_TRUNCATED;
  }
  if (frame_size_out != NULL) {
    *frame_size_out = total;
  }
  return PHIL_CODEC_FRAME_OK;
}

void *phil_codec_v1_transport_new(void) {
  struct PhilCodecTransport *transport = checked_malloc(sizeof(*transport));
  transport->bytes = NULL;
  transport->length = 0u;
  transport->capacity = 0u;
  transport->read_offset = 0u;
  return transport;
}

void phil_codec_v1_transport_free(void *transport_value) {
  struct PhilCodecTransport *transport = transport_value;
  if (transport == NULL) {
    return;
  }
  free(transport->bytes);
  free(transport);
}

size_t phil_codec_v1_transport_size(void *transport_value) {
  struct PhilCodecTransport *transport = transport_value;
  return transport == NULL ? 0u : transport->length;
}

size_t phil_codec_v1_transport_read_offset(void *transport_value) {
  struct PhilCodecTransport *transport = transport_value;
  return transport == NULL ? 0u : transport->read_offset;
}

const uint8_t *phil_codec_v1_transport_bytes(void *transport_value) {
  struct PhilCodecTransport *transport = transport_value;
  return transport == NULL ? NULL : transport->bytes;
}

int phil_codec_v1_transport_append(void *transport_value, const uint8_t *bytes, size_t length) {
  struct PhilCodecTransport *transport = transport_value;
  if (transport == NULL || (length != 0u && bytes == NULL)) {
    return 1;
  }
  transport_append_or_abort(transport, bytes, length);
  return 0;
}

void *phil_codec_v1_version_set_new(const uint16_t *versions, size_t count) {
  struct PhilCodecVersionSet *set;
  if (versions == NULL || count == 0u || count > PHIL_CODEC_V1_MAX_HELLO_VERSIONS) {
    return NULL;
  }
  set = checked_malloc(sizeof(*set));
  set->versions = checked_malloc(count * sizeof(*set->versions));
  memcpy(set->versions, versions, count * sizeof(*set->versions));
  set->count = count;
  set->is_static = 0;
  if (!version_set_is_canonical(set)) {
    phil_codec_v1_version_set_free(set);
    return NULL;
  }
  return set;
}

void phil_codec_v1_version_set_free(void *versions_value) {
  struct PhilCodecVersionSet *set = versions_value;
  if (set == NULL || set->is_static) {
    return;
  }
  free(set->versions);
  free(set);
}

void *phil_codec_v1_kind_new(const uint8_t *bytes, size_t length) {
  struct PhilCodecKind *kind;
  if (bytes == NULL || length == 0u || length > 255u) {
    return NULL;
  }
  kind = checked_malloc(sizeof(*kind));
  kind->bytes = checked_malloc(length);
  memcpy(kind->bytes, bytes, length);
  kind->length = length;
  return kind;
}

void phil_codec_v1_kind_free(void *kind_value) {
  struct PhilCodecKind *kind = kind_value;
  if (kind == NULL) {
    return;
  }
  free(kind->bytes);
  free(kind);
}

void *phil_codec_v1_digest_new(const uint8_t bytes[32]) {
  struct PhilCodecDigest *digest;
  if (bytes == NULL) {
    return NULL;
  }
  digest = checked_malloc(sizeof(*digest));
  memcpy(digest->bytes, bytes, sizeof(digest->bytes));
  return digest;
}

void phil_codec_v1_digest_free(void *digest_value) {
  free(digest_value);
}

void *phil_codec_v1_payload_new(uint64_t length, void *kind, void *digest) {
  struct PhilCodecPayload *payload;
  if (kind == NULL || digest == NULL) {
    return NULL;
  }
  payload = checked_malloc(sizeof(*payload));
  payload->length = length;
  payload->kind = kind;
  payload->digest = digest;
  return payload;
}

void phil_codec_v1_payload_free(void *payload) {
  free(payload);
}

void *phil_runtime_supported_versions(void) {
  return &default_versions;
}

uint64_t phil_runtime_payload_length(void *payload_owner) {
  struct PhilCodecPayload *payload = payload_owner;
  if (payload == NULL) {
    codec_abort();
  }
  return payload->length;
}

void *phil_runtime_payload_kind(void *payload_owner) {
  struct PhilCodecPayload *payload = payload_owner;
  if (payload == NULL || payload->kind == NULL) {
    codec_abort();
  }
  return payload->kind;
}

void *phil_runtime_sha256(void *payload_owner) {
  struct PhilCodecPayload *payload = payload_owner;
  if (payload == NULL || payload->digest == NULL) {
    codec_abort();
  }
  return payload->digest;
}

bool phil_runtime_refine_selected_version_with_set(
    void *transport,
    void *versions_value,
    uint16_t selected) {
  struct PhilCodecVersionSet *set = versions_value;
  size_t index;
  if (transport == NULL || !version_set_is_canonical(set)) {
    return false;
  }
  for (index = 0u; index < set->count; ++index) {
    if (set->versions[index] == selected) {
      return true;
    }
  }
  return false;
}

void phil_runtime_send_hello(void *transport_value, void *versions_value) {
  struct PhilCodecTransport *transport = transport_value;
  struct PhilCodecVersionSet *set = versions_value;
  size_t index;
  size_t payload_size;
  uint8_t count_bytes[2];
  uint8_t version_bytes[2];

  if (transport == NULL || !version_set_is_canonical(set)) {
    codec_abort();
  }
  payload_size = 2u + 2u * set->count;
  if (payload_size > UINT16_MAX) {
    codec_abort();
  }
  append_header(transport, PHIL_CODEC_V1_TAG_HELLO, (uint16_t)payload_size);
  write_u16be(count_bytes, (uint16_t)set->count);
  transport_append_or_abort(transport, count_bytes, sizeof(count_bytes));
  for (index = 0u; index < set->count; ++index) {
    write_u16be(version_bytes, set->versions[index]);
    transport_append_or_abort(transport, version_bytes, sizeof(version_bytes));
  }
}

void phil_runtime_send_begin_sha256(
    void *transport_value,
    uint64_t length,
    void *kind_value,
    void *digest_value) {
  struct PhilCodecTransport *transport = transport_value;
  struct PhilCodecKind *kind = kind_value;
  struct PhilCodecDigest *digest = digest_value;
  size_t payload_size;
  uint8_t length_bytes[8];
  uint8_t kind_length;
  uint8_t digest_alg = PHIL_CODEC_V1_DIGEST_SHA256;

  if (transport == NULL || kind == NULL || digest == NULL
      || kind->length == 0u || kind->length > 255u) {
    codec_abort();
  }
  payload_size = 42u + kind->length;
  if (payload_size > UINT16_MAX) {
    codec_abort();
  }
  append_header(transport, PHIL_CODEC_V1_TAG_BEGIN, (uint16_t)payload_size);
  write_u64be(length_bytes, length);
  transport_append_or_abort(transport, length_bytes, sizeof(length_bytes));
  kind_length = (uint8_t)kind->length;
  transport_append_or_abort(transport, &kind_length, 1u);
  transport_append_or_abort(transport, kind->bytes, kind->length);
  transport_append_or_abort(transport, &digest_alg, 1u);
  transport_append_or_abort(transport, digest->bytes, sizeof(digest->bytes));
}

static void receive_frame(
    void *transport_value,
    uint8_t expected_tag,
    void **pending_out,
    void **frame_out) {
  struct PhilCodecTransport *transport = transport_value;
  struct PhilCodecFrame *frame;
  struct PhilCodecPending *pending;
  size_t frame_size = 0u;
  size_t available;
  int status;

  if (transport == NULL || pending_out == NULL || frame_out == NULL
      || transport->read_offset > transport->length) {
    codec_abort();
  }
  available = transport->length - transport->read_offset;
  if (transport->bytes == NULL || available < PHIL_CODEC_V1_HEADER_SIZE) {
    codec_abort();
  }
  status = phil_codec_v1_validate_frame_bytes(
      transport->bytes + transport->read_offset,
      available,
      expected_tag,
      &frame_size);
  if (status != PHIL_CODEC_FRAME_OK) {
    codec_abort();
  }

  frame = checked_malloc(sizeof(*frame));
  frame->bytes = checked_malloc(frame_size);
  memcpy(frame->bytes, transport->bytes + transport->read_offset, frame_size);
  frame->length = frame_size;
  frame->tag = expected_tag;

  pending = checked_malloc(sizeof(*pending));
  pending->tag = expected_tag;
  pending->transport = transport;
  pending->start = transport->read_offset;
  pending->end = transport->read_offset + frame_size;
  pending->frame = frame;

  *pending_out = pending;
  *frame_out = frame;
}

void phil_runtime_receive_frame_Hello(void *transport, void **pending_out, void **frame_out) {
  receive_frame(transport, PHIL_CODEC_V1_TAG_HELLO, pending_out, frame_out);
}

void phil_runtime_receive_frame_Begin(void *transport, void **pending_out, void **frame_out) {
  receive_frame(transport, PHIL_CODEC_V1_TAG_BEGIN, pending_out, frame_out);
}

static void *borrow_frame(void *frame_value, uint8_t expected_tag) {
  struct PhilCodecFrame *frame = frame_value;
  if (frame == NULL || frame->tag != expected_tag) {
    codec_abort();
  }
  return frame;
}

void *phil_runtime_frame_borrow_view_Hello(void *frame) {
  return borrow_frame(frame, PHIL_CODEC_V1_TAG_HELLO);
}

void *phil_runtime_frame_borrow_view_Begin(void *frame) {
  return borrow_frame(frame, PHIL_CODEC_V1_TAG_BEGIN);
}

static uint8_t recognize_hello(
    struct PhilCodecPending *pending,
    struct PhilCodecFrame *frame,
    void **record_out,
    void **reason_out) {
  const uint8_t *payload;
  size_t payload_length;
  uint16_t count;
  size_t expected_length;
  size_t index;
  struct PhilCodecHelloRecord *record;

  payload = frame->bytes + PHIL_CODEC_V1_HEADER_SIZE;
  payload_length = frame->length - PHIL_CODEC_V1_HEADER_SIZE;
  if (payload_length < 2u) {
    *reason_out = reason_new(PHIL_CODEC_V1_TAG_HELLO, PHIL_CODEC_HELLO_REASON_LENGTH);
    return 0u;
  }
  count = read_u16be(payload);
  if (count == 0u) {
    *reason_out = reason_new(PHIL_CODEC_V1_TAG_HELLO, PHIL_CODEC_HELLO_REASON_EMPTY);
    return 0u;
  }
  expected_length = 2u + 2u * (size_t)count;
  if (expected_length != payload_length) {
    *reason_out = reason_new(PHIL_CODEC_V1_TAG_HELLO, PHIL_CODEC_HELLO_REASON_LENGTH);
    return 0u;
  }
  for (index = 1u; index < (size_t)count; ++index) {
    uint16_t previous = read_u16be(payload + 2u + 2u * (index - 1u));
    uint16_t current = read_u16be(payload + 2u + 2u * index);
    if (previous >= current) {
      *reason_out = reason_new(PHIL_CODEC_V1_TAG_HELLO, PHIL_CODEC_HELLO_REASON_ORDER);
      return 0u;
    }
  }

  record = checked_malloc(sizeof(*record));
  record->tag = PHIL_CODEC_V1_TAG_HELLO;
  record->count = (size_t)count;
  record->versions = checked_malloc(record->count * sizeof(*record->versions));
  for (index = 0u; index < record->count; ++index) {
    record->versions[index] = read_u16be(payload + 2u + 2u * index);
  }
  (void)pending;
  *record_out = record;
  return 1u;
}

static uint8_t recognize_begin(
    struct PhilCodecPending *pending,
    struct PhilCodecFrame *frame,
    void **record_out,
    void **reason_out) {
  const uint8_t *payload;
  size_t payload_length;
  size_t kind_length;
  size_t expected_length;
  size_t digest_alg_offset;
  struct PhilCodecBeginRecord *record;

  payload = frame->bytes + PHIL_CODEC_V1_HEADER_SIZE;
  payload_length = frame->length - PHIL_CODEC_V1_HEADER_SIZE;
  if (payload_length < 42u) {
    *reason_out = reason_new(PHIL_CODEC_V1_TAG_BEGIN, PHIL_CODEC_BEGIN_REASON_LENGTH);
    return 0u;
  }
  kind_length = (size_t)payload[8];
  if (kind_length == 0u) {
    *reason_out = reason_new(PHIL_CODEC_V1_TAG_BEGIN, PHIL_CODEC_BEGIN_REASON_KIND);
    return 0u;
  }
  expected_length = 42u + kind_length;
  if (expected_length != payload_length) {
    *reason_out = reason_new(PHIL_CODEC_V1_TAG_BEGIN, PHIL_CODEC_BEGIN_REASON_LENGTH);
    return 0u;
  }
  digest_alg_offset = 9u + kind_length;
  if (payload[digest_alg_offset] != PHIL_CODEC_V1_DIGEST_SHA256) {
    *reason_out = reason_new(PHIL_CODEC_V1_TAG_BEGIN, PHIL_CODEC_BEGIN_REASON_DIGEST_ALG);
    return 0u;
  }

  record = checked_malloc(sizeof(*record));
  record->tag = PHIL_CODEC_V1_TAG_BEGIN;
  record->length = read_u64be(payload);
  record->kind_length = kind_length;
  record->kind_bytes = checked_malloc(kind_length);
  memcpy(record->kind_bytes, payload + 9u, kind_length);
  memcpy(record->digest, payload + digest_alg_offset + 1u, sizeof(record->digest));
  (void)pending;
  *record_out = record;
  return 1u;
}

static uint8_t recognize(
    void *pending_value,
    void *raw_view,
    uint8_t expected_tag,
    void **record_out,
    void **reason_out) {
  struct PhilCodecPending *pending = pending_value;
  struct PhilCodecFrame *frame = raw_view;

  if (pending == NULL || frame == NULL || record_out == NULL || reason_out == NULL
      || pending->tag != expected_tag || frame->tag != expected_tag
      || pending->frame != frame) {
    codec_abort();
  }
  *record_out = NULL;
  *reason_out = NULL;
  if (expected_tag == PHIL_CODEC_V1_TAG_HELLO) {
    return recognize_hello(pending, frame, record_out, reason_out);
  }
  return recognize_begin(pending, frame, record_out, reason_out);
}

uint8_t phil_runtime_recognize_Hello(
    void *pending,
    void *raw_view,
    void **record_out,
    void **reason_out) {
  return recognize(
      pending,
      raw_view,
      PHIL_CODEC_V1_TAG_HELLO,
      record_out,
      reason_out);
}

uint8_t phil_runtime_recognize_Begin(
    void *pending,
    void *raw_view,
    void **record_out,
    void **reason_out) {
  return recognize(
      pending,
      raw_view,
      PHIL_CODEC_V1_TAG_BEGIN,
      record_out,
      reason_out);
}

static void free_frame(struct PhilCodecFrame *frame) {
  if (frame != NULL) {
    free(frame->bytes);
    free(frame);
  }
}

static void commit_ingress(void *transport_value, void *pending_value, uint8_t expected_tag) {
  struct PhilCodecTransport *transport = transport_value;
  struct PhilCodecPending *pending = pending_value;
  if (transport == NULL || pending == NULL || pending->transport != transport
      || pending->tag != expected_tag || transport->read_offset != pending->start
      || pending->end > transport->length) {
    codec_abort();
  }
  transport->read_offset = pending->end;
  free_frame(pending->frame);
  pending->frame = NULL;
  free(pending);
}

void phil_runtime_commit_ingress_Hello(void *transport, void *pending) {
  commit_ingress(transport, pending, PHIL_CODEC_V1_TAG_HELLO);
}

void phil_runtime_commit_ingress_Begin(void *transport, void *pending) {
  commit_ingress(transport, pending, PHIL_CODEC_V1_TAG_BEGIN);
}

static void fail_recognition(void *pending_value, void *reason_value, uint8_t expected_tag) {
  struct PhilCodecPending *pending = pending_value;
  struct PhilCodecReason *reason = reason_value;
  if (pending == NULL || reason == NULL || pending->tag != expected_tag
      || reason->tag != expected_tag) {
    codec_abort();
  }
}

void phil_runtime_fail_recognition_Hello(void *pending, void *reason) {
  fail_recognition(pending, reason, PHIL_CODEC_V1_TAG_HELLO);
}

void phil_runtime_fail_recognition_Begin(void *pending, void *reason) {
  fail_recognition(pending, reason, PHIL_CODEC_V1_TAG_BEGIN);
}

static void destroy_pending(void *pending_value, void *frame_value, uint8_t expected_tag) {
  struct PhilCodecPending *pending = pending_value;
  struct PhilCodecFrame *frame = frame_value;
  if (pending == NULL || frame == NULL || pending->tag != expected_tag
      || frame->tag != expected_tag || pending->frame != frame) {
    codec_abort();
  }
  free_frame(frame);
  pending->frame = NULL;
  free(pending);
}

void phil_runtime_destroy_pending_Hello(void *pending, void *frame) {
  destroy_pending(pending, frame, PHIL_CODEC_V1_TAG_HELLO);
}

void phil_runtime_destroy_pending_Begin(void *pending, void *frame) {
  destroy_pending(pending, frame, PHIL_CODEC_V1_TAG_BEGIN);
}

size_t phil_codec_v1_hello_version_count(void *record_value) {
  struct PhilCodecHelloRecord *record = record_value;
  if (record == NULL || record->tag != PHIL_CODEC_V1_TAG_HELLO) {
    return 0u;
  }
  return record->count;
}

uint16_t phil_codec_v1_hello_version_at(void *record_value, size_t index) {
  struct PhilCodecHelloRecord *record = record_value;
  if (record == NULL || record->tag != PHIL_CODEC_V1_TAG_HELLO || index >= record->count) {
    codec_abort();
  }
  return record->versions[index];
}

uint64_t phil_codec_v1_begin_length(void *record_value) {
  struct PhilCodecBeginRecord *record = record_value;
  if (record == NULL || record->tag != PHIL_CODEC_V1_TAG_BEGIN) {
    codec_abort();
  }
  return record->length;
}

size_t phil_codec_v1_begin_kind_length(void *record_value) {
  struct PhilCodecBeginRecord *record = record_value;
  if (record == NULL || record->tag != PHIL_CODEC_V1_TAG_BEGIN) {
    return 0u;
  }
  return record->kind_length;
}

const uint8_t *phil_codec_v1_begin_kind_bytes(void *record_value) {
  struct PhilCodecBeginRecord *record = record_value;
  if (record == NULL || record->tag != PHIL_CODEC_V1_TAG_BEGIN) {
    return NULL;
  }
  return record->kind_bytes;
}

const uint8_t *phil_codec_v1_begin_digest_bytes(void *record_value) {
  struct PhilCodecBeginRecord *record = record_value;
  if (record == NULL || record->tag != PHIL_CODEC_V1_TAG_BEGIN) {
    return NULL;
  }
  return record->digest;
}

uint8_t phil_codec_v1_recognition_reason_code(void *reason_value) {
  struct PhilCodecReason *reason = reason_value;
  return reason == NULL ? 0u : reason->code;
}

void phil_codec_v1_record_free(void *record_value) {
  uint8_t tag;
  if (record_value == NULL) {
    return;
  }
  tag = *(const uint8_t *)record_value;
  if (tag == PHIL_CODEC_V1_TAG_HELLO) {
    struct PhilCodecHelloRecord *record = record_value;
    free(record->versions);
    free(record);
    return;
  }
  if (tag == PHIL_CODEC_V1_TAG_BEGIN) {
    struct PhilCodecBeginRecord *record = record_value;
    free(record->kind_bytes);
    free(record);
    return;
  }
  codec_abort();
}

void phil_codec_v1_reason_free(void *reason) {
  free(reason);
}
