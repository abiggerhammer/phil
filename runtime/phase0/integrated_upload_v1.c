#include "integrated_upload_v1.h"

#include <openssl/crypto.h>
#include <openssl/sha.h>
#include <pthread.h>
#include <stdlib.h>
#include <string.h>

#define PHIL_INTEGRATED_MAX_PAYLOAD (1024u * 1024u)
#define PHIL_INTEGRATED_VERSION_NONE 0
#define PHIL_INTEGRATED_VERSION_UNSUPPORTED 1
#define PHIL_INTEGRATED_VERSION_SELECTED 2
#define PHIL_INTEGRATED_BEGIN_NONE 0
#define PHIL_INTEGRATED_BEGIN_REJECT 1
#define PHIL_INTEGRATED_BEGIN_PROCEED 2
#define PHIL_INTEGRATED_PAYLOAD_NONE (-1)
#define PHIL_INTEGRATED_FINAL_NONE 0
#define PHIL_INTEGRATED_FINAL_REJECTED 1
#define PHIL_INTEGRATED_FINAL_ACCEPTED 2
#define PHIL_INTEGRATED_ROLE_NONE 0
#define PHIL_INTEGRATED_ROLE_CLIENT 1
#define PHIL_INTEGRATED_ROLE_SERVER 2

struct PhilIntegratedVersionSet {
  size_t count;
  uint16_t *versions;
};

struct PhilIntegratedPolicyContext {
  uint32_t marker;
};

struct PhilIntegratedPayload {
  size_t length;
  uint8_t *bytes;
};

struct PhilIntegratedUploadId {
  uint8_t token[16];
};

struct PhilIntegratedStorageError {
  uint8_t code;
};

struct PhilIntegratedSession {
  pthread_mutex_t mutex;
  pthread_cond_t condition;
  enum phil_integrated_v1_scenario scenario;

  void *transport;
  void *client_payload;
  void *client_kind;
  void *client_digest;
  bool client_payload_alive;
  uint8_t *client_bytes;
  size_t client_length;

  struct PhilIntegratedPolicyContext policy_context;
  struct PhilIntegratedVersionSet server_supported;
  struct PhilIntegratedVersionSet *hello_versions;
  void *hello_record;
  void *begin_record;

  bool client_waiting_version;
  bool client_waiting_begin;
  int version_choice;
  uint16_t selected_version;
  int begin_choice;
  uint8_t begin_rejection_reason;
  int payload_choice;
  int final_choice;
  uint8_t final_rejection_reason;
  void *final_upload_id;

  uint8_t *exact_bytes;
  size_t exact_length;
  bool exact_sent;
  struct PhilIntegratedPayload *server_payload;
  struct PhilIntegratedUploadId *upload_id;
  struct PhilIntegratedStorageError storage_error;

  unsigned exact_send_calls;
  unsigned exact_receive_calls;
  unsigned digest_calls;
  unsigned store_calls;
  unsigned release_calls;
  bool last_digest_result;
  bool upload_recorded;
  uint8_t recorded_upload_id[16];
  bool fatal_effect;
};

static struct PhilIntegratedSession integrated_session;
static bool integrated_session_initialized;
static int hello_policy_reason_token;
static _Thread_local int integrated_thread_role;
static _Thread_local bool integrated_branch_condition;

static void integrated_abort(void) {
  abort();
}

static struct PhilIntegratedSession *require_session(void) {
  if (!integrated_session_initialized) {
    integrated_abort();
  }
  return &integrated_session;
}

static void lock_session(struct PhilIntegratedSession *session) {
  if (pthread_mutex_lock(&session->mutex) != 0) {
    integrated_abort();
  }
}

static void unlock_session(struct PhilIntegratedSession *session) {
  if (pthread_mutex_unlock(&session->mutex) != 0) {
    integrated_abort();
  }
}

static void broadcast_session(struct PhilIntegratedSession *session) {
  if (pthread_cond_broadcast(&session->condition) != 0) {
    integrated_abort();
  }
}

static void wait_session(struct PhilIntegratedSession *session) {
  if (pthread_cond_wait(&session->condition, &session->mutex) != 0) {
    integrated_abort();
  }
}

static void *checked_malloc(size_t size) {
  void *result = malloc(size == 0u ? 1u : size);
  if (result == NULL) {
    integrated_abort();
  }
  return result;
}

static void require_transport(struct PhilIntegratedSession *session, void *transport) {
  if (transport == NULL || transport != session->transport) {
    integrated_abort();
  }
}

static bool version_set_contains(
    const struct PhilIntegratedVersionSet *set,
    uint16_t version) {
  size_t index;
  if (set == NULL || set->versions == NULL) {
    return false;
  }
  for (index = 0u; index < set->count; ++index) {
    if (set->versions[index] == version) {
      return true;
    }
  }
  return false;
}

static void free_server_payload(struct PhilIntegratedSession *session) {
  if (session->server_payload != NULL) {
    free(session->server_payload->bytes);
    free(session->server_payload);
    session->server_payload = NULL;
  }
}

static void consume_client_payload_metadata(void) {
  struct PhilIntegratedSession *session = require_session();
  void *payload = NULL;
  lock_session(session);
  if (session->client_payload_alive) {
    payload = session->client_payload;
    session->client_payload_alive = false;
  }
  unlock_session(session);
  if (payload != NULL) {
    phil_codec_v1_payload_free(payload);
  }
}

int phil_integrated_v1_prepare(
    enum phil_integrated_v1_scenario scenario,
    const uint8_t *payload_bytes,
    size_t payload_length) {
  static const uint8_t kind_bytes[] = {0x62u, 0x69u, 0x6eu};
  struct PhilIntegratedSession *session = &integrated_session;
  uint8_t digest_bytes[32];

  if (integrated_session_initialized
      || payload_bytes == NULL
      || payload_length == 0u
      || payload_length > PHIL_INTEGRATED_MAX_PAYLOAD
      || (scenario != PHIL_INTEGRATED_V1_ACCEPT
        && scenario != PHIL_INTEGRATED_V1_DIGEST_REJECT
        && scenario != PHIL_INTEGRATED_V1_CANCEL)) {
    return 1;
  }

  memset(session, 0, sizeof(*session));
  if (pthread_mutex_init(&session->mutex, NULL) != 0) {
    return 1;
  }
  if (pthread_cond_init(&session->condition, NULL) != 0) {
    (void)pthread_mutex_destroy(&session->mutex);
    return 1;
  }
  integrated_session_initialized = true;
  session->scenario = scenario;
  session->payload_choice = PHIL_INTEGRATED_PAYLOAD_NONE;
  session->policy_context.marker = UINT32_C(0x5048494c);

  session->client_bytes = checked_malloc(payload_length);
  memcpy(session->client_bytes, payload_bytes, payload_length);
  session->client_length = payload_length;

  session->server_supported.count = 1u;
  session->server_supported.versions = checked_malloc(sizeof(uint16_t));
  session->server_supported.versions[0] = 1u;

  session->transport = phil_codec_v1_transport_new();
  session->client_kind = phil_codec_v1_kind_new(kind_bytes, sizeof(kind_bytes));
  if (SHA256(payload_bytes, payload_length, digest_bytes) == NULL) {
    integrated_abort();
  }
  if (scenario == PHIL_INTEGRATED_V1_DIGEST_REJECT) {
    digest_bytes[0] ^= 0xffu;
  }
  session->client_digest = phil_codec_v1_digest_new(digest_bytes);
  session->client_payload = phil_codec_v1_payload_new(
      (uint64_t)payload_length,
      session->client_kind,
      session->client_digest);
  session->client_payload_alive = true;

  if (session->transport == NULL
      || session->client_kind == NULL
      || session->client_digest == NULL
      || session->client_payload == NULL) {
    integrated_abort();
  }
  return 0;
}

void phil_integrated_v1_destroy(void) {
  struct PhilIntegratedSession *session;
  if (!integrated_session_initialized) {
    return;
  }
  session = &integrated_session;

  if (session->client_payload_alive) {
    phil_codec_v1_payload_free(session->client_payload);
  }
  phil_codec_v1_kind_free(session->client_kind);
  phil_codec_v1_digest_free(session->client_digest);
  phil_codec_v1_transport_free(session->transport);
  phil_codec_v1_record_free(session->hello_record);
  phil_codec_v1_record_free(session->begin_record);
  free(session->hello_versions == NULL ? NULL : session->hello_versions->versions);
  free(session->hello_versions);
  free(session->server_supported.versions);
  free(session->client_bytes);
  free(session->exact_bytes);
  free_server_payload(session);
  free(session->upload_id);

  if (pthread_cond_destroy(&session->condition) != 0) {
    integrated_abort();
  }
  if (pthread_mutex_destroy(&session->mutex) != 0) {
    integrated_abort();
  }
  memset(session, 0, sizeof(*session));
  integrated_session_initialized = false;
  integrated_thread_role = PHIL_INTEGRATED_ROLE_NONE;
  integrated_branch_condition = false;
}

void *phil_integrated_v1_transport(void) {
  return require_session()->transport;
}

void *phil_integrated_v1_client_payload(void) {
  return require_session()->client_payload;
}

void *phil_integrated_v1_policy_context(void) {
  return &require_session()->policy_context;
}

void *phil_integrated_v1_server_supported_versions(void) {
  return &require_session()->server_supported;
}

void phil_integrated_v1_enter_client(void) {
  (void)require_session();
  integrated_thread_role = PHIL_INTEGRATED_ROLE_CLIENT;
  integrated_branch_condition = false;
}

void phil_integrated_v1_enter_server(void) {
  (void)require_session();
  integrated_thread_role = PHIL_INTEGRATED_ROLE_SERVER;
  integrated_branch_condition = false;
}

void phil_integrated_v1_wait_client_version_receive(void) {
  struct PhilIntegratedSession *session = require_session();
  lock_session(session);
  while (!session->client_waiting_version) {
    wait_session(session);
  }
  unlock_session(session);
}

void *phil_record_Hello_get_versions(void *hello_record) {
  struct PhilIntegratedSession *session = require_session();
  struct PhilIntegratedVersionSet *set;
  size_t count;
  size_t index;

  if (hello_record == NULL) {
    integrated_abort();
  }
  count = phil_codec_v1_hello_version_count(hello_record);
  if (count == 0u) {
    integrated_abort();
  }
  set = checked_malloc(sizeof(*set));
  set->count = count;
  set->versions = checked_malloc(count * sizeof(*set->versions));
  for (index = 0u; index < count; ++index) {
    set->versions[index] = phil_codec_v1_hello_version_at(hello_record, index);
  }

  lock_session(session);
  if (session->hello_versions != NULL) {
    unlock_session(session);
    free(set->versions);
    free(set);
    integrated_abort();
  }
  session->hello_versions = set;
  unlock_session(session);
  return set;
}

uint64_t phil_record_Begin_get_length(void *begin_record) {
  return phil_codec_v1_begin_length(begin_record);
}

bool phil_runtime_choose_supported(
    void *server_supported,
    void *offered_versions,
    uint16_t *selected_version_out) {
  struct PhilIntegratedSession *session = require_session();
  struct PhilIntegratedVersionSet *server = server_supported;
  struct PhilIntegratedVersionSet *offered = offered_versions;
  size_t index;

  if (server != &session->server_supported
      || offered != session->hello_versions
      || selected_version_out == NULL) {
    integrated_abort();
  }
  for (index = 0u; index < offered->count; ++index) {
    if (version_set_contains(server, offered->versions[index])) {
      *selected_version_out = offered->versions[index];
      return true;
    }
  }
  return false;
}

void phil_runtime_select_unsupported(void *transport) {
  struct PhilIntegratedSession *session = require_session();
  lock_session(session);
  require_transport(session, transport);
  session->version_choice = PHIL_INTEGRATED_VERSION_UNSUPPORTED;
  broadcast_session(session);
  unlock_session(session);
}

void phil_runtime_select_version(void *transport, uint16_t selected_version) {
  struct PhilIntegratedSession *session = require_session();
  lock_session(session);
  require_transport(session, transport);
  session->selected_version = selected_version;
  session->version_choice = PHIL_INTEGRATED_VERSION_SELECTED;
  broadcast_session(session);
  while (!session->client_waiting_begin && !session->fatal_effect) {
    wait_session(session);
  }
  if (session->fatal_effect) {
    unlock_session(session);
    integrated_abort();
  }
  unlock_session(session);
}

bool phil_runtime_receive_version_choice(
    void *transport,
    uint16_t *selected_version_out) {
  struct PhilIntegratedSession *session = require_session();
  bool selected;
  lock_session(session);
  require_transport(session, transport);
  session->client_waiting_version = true;
  broadcast_session(session);
  while (session->version_choice == PHIL_INTEGRATED_VERSION_NONE
      && !session->fatal_effect) {
    wait_session(session);
  }
  if (session->fatal_effect) {
    unlock_session(session);
    integrated_abort();
  }
  selected = session->version_choice == PHIL_INTEGRATED_VERSION_SELECTED;
  if (selected) {
    if (selected_version_out == NULL) {
      unlock_session(session);
      integrated_abort();
    }
    *selected_version_out = session->selected_version;
  }
  unlock_session(session);
  return selected;
}

bool phil_runtime_validate_hello_policy(
    void *policy_context,
    void *hello_record,
    void **rejection_reason_out) {
  struct PhilIntegratedSession *session = require_session();
  bool accepted = policy_context == &session->policy_context
      && session->policy_context.marker == UINT32_C(0x5048494c)
      && hello_record != NULL
      && phil_codec_v1_hello_version_count(hello_record) != 0u;

  lock_session(session);
  session->hello_record = hello_record;
  unlock_session(session);
  if (accepted) {
    if (rejection_reason_out != NULL) {
      *rejection_reason_out = NULL;
    }
    return true;
  }
  if (rejection_reason_out == NULL) {
    integrated_abort();
  }
  *rejection_reason_out = &hello_policy_reason_token;
  return false;
}

void phil_runtime_fail_hello_policy(void *transport, void *rejection_reason) {
  struct PhilIntegratedSession *session = require_session();
  lock_session(session);
  require_transport(session, transport);
  if (rejection_reason != &hello_policy_reason_token) {
    unlock_session(session);
    integrated_abort();
  }
  session->fatal_effect = true;
  broadcast_session(session);
  unlock_session(session);
}

bool phil_runtime_validate_begin_policy(
    void *policy_context,
    void *begin_record,
    uint8_t *rejection_reason_out) {
  static const uint8_t expected_kind[] = {0x62u, 0x69u, 0x6eu};
  struct PhilIntegratedSession *session = require_session();
  const uint8_t *kind_bytes;
  size_t kind_length;
  bool accepted;

  if (begin_record == NULL) {
    integrated_abort();
  }
  kind_length = phil_codec_v1_begin_kind_length(begin_record);
  kind_bytes = phil_codec_v1_begin_kind_bytes(begin_record);
  accepted = policy_context == &session->policy_context
      && phil_codec_v1_begin_length(begin_record) == (uint64_t)session->client_length
      && kind_length == sizeof(expected_kind)
      && kind_bytes != NULL
      && memcmp(kind_bytes, expected_kind, sizeof(expected_kind)) == 0;

  lock_session(session);
  session->begin_record = begin_record;
  unlock_session(session);
  if (!accepted) {
    if (rejection_reason_out == NULL) {
      integrated_abort();
    }
    *rejection_reason_out = 1u;
  }
  return accepted;
}

void phil_runtime_select_begin_policy_reject(
    void *transport,
    uint8_t rejection_reason) {
  struct PhilIntegratedSession *session = require_session();
  lock_session(session);
  require_transport(session, transport);
  session->begin_choice = PHIL_INTEGRATED_BEGIN_REJECT;
  session->begin_rejection_reason = rejection_reason;
  broadcast_session(session);
  unlock_session(session);
}

void phil_runtime_select_begin_policy_proceed(void *transport) {
  struct PhilIntegratedSession *session = require_session();
  lock_session(session);
  require_transport(session, transport);
  session->begin_choice = PHIL_INTEGRATED_BEGIN_PROCEED;
  broadcast_session(session);
  unlock_session(session);
}

bool phil_runtime_receive_begin_policy_choice(
    void *transport,
    uint8_t *rejection_reason_out) {
  struct PhilIntegratedSession *session = require_session();
  bool proceed;
  lock_session(session);
  require_transport(session, transport);
  session->client_waiting_begin = true;
  broadcast_session(session);
  while (session->begin_choice == PHIL_INTEGRATED_BEGIN_NONE
      && !session->fatal_effect) {
    wait_session(session);
  }
  if (session->fatal_effect) {
    unlock_session(session);
    integrated_abort();
  }
  proceed = session->begin_choice == PHIL_INTEGRATED_BEGIN_PROCEED;
  if (!proceed) {
    if (rejection_reason_out == NULL) {
      unlock_session(session);
      integrated_abort();
    }
    *rejection_reason_out = session->begin_rejection_reason;
  }
  unlock_session(session);
  return proceed;
}

void phil_runtime_select_payload_cancel(void *transport, uint8_t choice) {
  struct PhilIntegratedSession *session = require_session();
  if (choice > 1u) {
    integrated_abort();
  }
  lock_session(session);
  require_transport(session, transport);
  session->payload_choice = (int)choice;
  broadcast_session(session);
  unlock_session(session);
}

bool phil_runtime_receive_payload_cancel(void *transport) {
  struct PhilIntegratedSession *session = require_session();
  bool payload;
  lock_session(session);
  require_transport(session, transport);
  while (session->payload_choice == PHIL_INTEGRATED_PAYLOAD_NONE
      && !session->fatal_effect) {
    wait_session(session);
  }
  if (session->fatal_effect) {
    unlock_session(session);
    integrated_abort();
  }
  payload = session->payload_choice == 1;
  unlock_session(session);
  return payload;
}

void phil_runtime_send_exact(void *transport, void *payload_owner) {
  struct PhilIntegratedSession *session = require_session();
  void *consumed_payload;
  lock_session(session);
  require_transport(session, transport);
  if (!session->client_payload_alive
      || payload_owner != session->client_payload
      || session->exact_sent) {
    unlock_session(session);
    integrated_abort();
  }
  session->exact_bytes = checked_malloc(session->client_length);
  memcpy(session->exact_bytes, session->client_bytes, session->client_length);
  session->exact_length = session->client_length;
  session->exact_sent = true;
  session->exact_send_calls += 1u;
  consumed_payload = session->client_payload;
  session->client_payload_alive = false;
  broadcast_session(session);
  unlock_session(session);
  phil_codec_v1_payload_free(consumed_payload);
}

struct phil_exact_receive_result phil_runtime_receive_exact_u64(
    void *transport,
    uint64_t length) {
  struct PhilIntegratedSession *session = require_session();
  struct phil_exact_receive_result result;
  struct PhilIntegratedPayload *payload;
  size_t requested;
  size_t copied;

  lock_session(session);
  require_transport(session, transport);
  while (!session->exact_sent && !session->fatal_effect) {
    wait_session(session);
  }
  if (session->fatal_effect || session->server_payload != NULL) {
    unlock_session(session);
    integrated_abort();
  }
  requested = length > SIZE_MAX ? SIZE_MAX : (size_t)length;
  copied = requested < session->exact_length ? requested : session->exact_length;
  payload = checked_malloc(sizeof(*payload));
  payload->length = copied;
  payload->bytes = checked_malloc(copied);
  if (copied != 0u) {
    memcpy(payload->bytes, session->exact_bytes, copied);
  }
  session->server_payload = payload;
  session->exact_receive_calls += 1u;
  result.status = requested == session->exact_length ? 1u : 0u;
  result.payload = payload;
  unlock_session(session);
  return result;
}

bool phil_runtime_digest_validate(void *begin_record, void *payload_value) {
  struct PhilIntegratedSession *session = require_session();
  struct PhilIntegratedPayload *payload = payload_value;
  const uint8_t *expected;
  uint8_t actual[32];
  bool matches;

  lock_session(session);
  if (begin_record != session->begin_record
      || payload == NULL
      || payload != session->server_payload) {
    unlock_session(session);
    integrated_abort();
  }
  expected = phil_codec_v1_begin_digest_bytes(begin_record);
  if (expected == NULL || SHA256(payload->bytes, payload->length, actual) == NULL) {
    unlock_session(session);
    integrated_abort();
  }
  matches = CRYPTO_memcmp(actual, expected, sizeof(actual)) == 0;
  session->digest_calls += 1u;
  session->last_digest_result = matches;
  unlock_session(session);
  return matches;
}

void phil_buffer_release(void *payload) {
  struct PhilIntegratedSession *session = require_session();
  lock_session(session);
  if (payload == NULL || payload != session->server_payload) {
    unlock_session(session);
    integrated_abort();
  }
  free_server_payload(session);
  session->release_calls += 1u;
  unlock_session(session);
}

uint8_t phil_runtime_store_with_error(
    void *payload,
    void **upload_id_out,
    void **storage_error_out) {
  struct PhilIntegratedSession *session = require_session();
  struct PhilIntegratedUploadId *upload_id;
  size_t index;

  lock_session(session);
  if (payload == NULL
      || payload != session->server_payload
      || upload_id_out == NULL
      || storage_error_out == NULL) {
    unlock_session(session);
    integrated_abort();
  }
  session->store_calls += 1u;
  upload_id = checked_malloc(sizeof(*upload_id));
  for (index = 0u; index < sizeof(upload_id->token); ++index) {
    upload_id->token[index] = (uint8_t)(0xa0u + index);
  }
  free_server_payload(session);
  session->upload_id = upload_id;
  *upload_id_out = upload_id;
  *storage_error_out = NULL;
  unlock_session(session);
  return 1u;
}

void phil_runtime_fail_storage(void *transport, void *storage_error) {
  struct PhilIntegratedSession *session = require_session();
  lock_session(session);
  require_transport(session, transport);
  if (storage_error != &session->storage_error) {
    unlock_session(session);
    integrated_abort();
  }
  session->fatal_effect = true;
  broadcast_session(session);
  unlock_session(session);
}

void phil_runtime_select_accepted(void *transport, void *upload_id) {
  struct PhilIntegratedSession *session = require_session();
  lock_session(session);
  require_transport(session, transport);
  if (upload_id == NULL || upload_id != session->upload_id) {
    unlock_session(session);
    integrated_abort();
  }
  session->final_choice = PHIL_INTEGRATED_FINAL_ACCEPTED;
  session->final_upload_id = upload_id;
  broadcast_session(session);
  unlock_session(session);
}

void phil_runtime_select_rejected(void *transport, uint8_t reason) {
  struct PhilIntegratedSession *session = require_session();
  lock_session(session);
  require_transport(session, transport);
  session->final_choice = PHIL_INTEGRATED_FINAL_REJECTED;
  session->final_rejection_reason = reason;
  broadcast_session(session);
  unlock_session(session);
}

bool phil_runtime_receive_final_response(void *transport, void **upload_id_out) {
  struct PhilIntegratedSession *session = require_session();
  bool accepted;
  lock_session(session);
  require_transport(session, transport);
  while (session->final_choice == PHIL_INTEGRATED_FINAL_NONE
      && !session->fatal_effect) {
    wait_session(session);
  }
  if (session->fatal_effect) {
    unlock_session(session);
    integrated_abort();
  }
  accepted = session->final_choice == PHIL_INTEGRATED_FINAL_ACCEPTED;
  if (accepted) {
    if (upload_id_out == NULL) {
      unlock_session(session);
      integrated_abort();
    }
    *upload_id_out = session->final_upload_id;
  }
  unlock_session(session);
  return accepted;
}

void phil_runtime_record_upload_id(void *upload_id) {
  struct PhilIntegratedSession *session = require_session();
  struct PhilIntegratedUploadId *value = upload_id;
  lock_session(session);
  if (value == NULL || value != session->upload_id) {
    unlock_session(session);
    integrated_abort();
  }
  memcpy(session->recorded_upload_id, value->token, sizeof(value->token));
  session->upload_recorded = true;
  unlock_session(session);
}

void phil_call_should_cancel_upload(void) {
  struct PhilIntegratedSession *session = require_session();
  if (integrated_thread_role != PHIL_INTEGRATED_ROLE_CLIENT) {
    integrated_abort();
  }
  integrated_branch_condition = session->scenario == PHIL_INTEGRATED_V1_CANCEL;
}

bool phil_branch_condition(void) {
  if (integrated_thread_role == PHIL_INTEGRATED_ROLE_NONE) {
    integrated_abort();
  }
  return integrated_branch_condition;
}

void phil_cleanup(void) {
  if (integrated_thread_role == PHIL_INTEGRATED_ROLE_CLIENT) {
    consume_client_payload_metadata();
  }
}

bool phil_integrated_v1_observed(enum phil_integrated_v1_scenario scenario) {
  struct PhilIntegratedSession *session = require_session();
  bool observed = false;
  lock_session(session);
  if (scenario == PHIL_INTEGRATED_V1_ACCEPT) {
    observed = session->scenario == scenario
        && session->payload_choice == 1
        && session->exact_send_calls == 1u
        && session->exact_receive_calls == 1u
        && session->digest_calls == 1u
        && session->last_digest_result
        && session->store_calls == 1u
        && session->release_calls == 0u
        && session->final_choice == PHIL_INTEGRATED_FINAL_ACCEPTED
        && session->upload_recorded
        && session->upload_id != NULL
        && CRYPTO_memcmp(
          session->recorded_upload_id,
          session->upload_id->token,
          sizeof(session->recorded_upload_id)) == 0
        && !session->client_payload_alive
        && !session->fatal_effect;
  } else if (scenario == PHIL_INTEGRATED_V1_DIGEST_REJECT) {
    observed = session->scenario == scenario
        && session->payload_choice == 1
        && session->exact_send_calls == 1u
        && session->exact_receive_calls == 1u
        && session->digest_calls == 1u
        && !session->last_digest_result
        && session->store_calls == 0u
        && session->release_calls == 1u
        && session->final_choice == PHIL_INTEGRATED_FINAL_REJECTED
        && session->final_rejection_reason == 1u
        && !session->upload_recorded
        && !session->client_payload_alive
        && !session->fatal_effect;
  } else if (scenario == PHIL_INTEGRATED_V1_CANCEL) {
    observed = session->scenario == scenario
        && session->payload_choice == 0
        && session->exact_send_calls == 0u
        && session->exact_receive_calls == 0u
        && session->digest_calls == 0u
        && session->store_calls == 0u
        && session->release_calls == 0u
        && session->final_choice == PHIL_INTEGRATED_FINAL_NONE
        && !session->upload_recorded
        && !session->client_payload_alive
        && !session->fatal_effect;
  }
  unlock_session(session);
  return observed;
}
