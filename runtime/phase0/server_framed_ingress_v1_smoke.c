#include "server_framed_ingress_v1.h"

#include <stddef.h>

static int transport_token;
static int hello_pending_token;
static int hello_frame_token;
static int hello_raw_token;
static int hello_record_token;
static int hello_reason_token;
static int begin_pending_token;
static int begin_frame_token;
static int begin_raw_token;
static int begin_record_token;
static int begin_reason_token;

static void *expected_transport;
static unsigned hello_receive_calls;
static unsigned hello_borrow_calls;
static unsigned hello_recognize_calls;
static unsigned hello_commit_calls;
static unsigned hello_fail_calls;
static unsigned hello_destroy_calls;
static unsigned begin_receive_calls;
static unsigned begin_borrow_calls;
static unsigned begin_recognize_calls;
static unsigned begin_commit_calls;
static unsigned begin_fail_calls;
static unsigned begin_destroy_calls;
static uint8_t hello_status;
static uint8_t begin_status;

static void reset_state(void) {
    expected_transport = &transport_token;
    hello_receive_calls = 0;
    hello_borrow_calls = 0;
    hello_recognize_calls = 0;
    hello_commit_calls = 0;
    hello_fail_calls = 0;
    hello_destroy_calls = 0;
    begin_receive_calls = 0;
    begin_borrow_calls = 0;
    begin_recognize_calls = 0;
    begin_commit_calls = 0;
    begin_fail_calls = 0;
    begin_destroy_calls = 0;
    hello_status = 1;
    begin_status = 0;
}

void phil_runtime_receive_frame_Hello(void *transport, void **pending_out, void **frame_out) {
    if (transport == expected_transport && pending_out != NULL && frame_out != NULL) {
        *pending_out = &hello_pending_token;
        *frame_out = &hello_frame_token;
        hello_receive_calls += 1;
    }
}

void phil_runtime_receive_frame_Begin(void *transport, void **pending_out, void **frame_out) {
    if (transport == expected_transport && pending_out != NULL && frame_out != NULL) {
        *pending_out = &begin_pending_token;
        *frame_out = &begin_frame_token;
        begin_receive_calls += 1;
    }
}

void *phil_runtime_frame_borrow_view_Hello(void *frame) {
    if (frame == &hello_frame_token) {
        hello_borrow_calls += 1;
        return &hello_raw_token;
    }
    return NULL;
}

void *phil_runtime_frame_borrow_view_Begin(void *frame) {
    if (frame == &begin_frame_token) {
        begin_borrow_calls += 1;
        return &begin_raw_token;
    }
    return NULL;
}

uint8_t phil_runtime_recognize_Hello(
    void *pending,
    void *raw_view,
    void **record_out,
    void **reason_out) {
    if (pending != &hello_pending_token || raw_view != &hello_raw_token
        || record_out == NULL || reason_out == NULL) {
        return 0;
    }
    hello_recognize_calls += 1;
    if (hello_status == 1) {
        *record_out = &hello_record_token;
        *reason_out = NULL;
    } else {
        *record_out = NULL;
        *reason_out = &hello_reason_token;
    }
    return hello_status;
}

uint8_t phil_runtime_recognize_Begin(
    void *pending,
    void *raw_view,
    void **record_out,
    void **reason_out) {
    if (pending != &begin_pending_token || raw_view != &begin_raw_token
        || record_out == NULL || reason_out == NULL) {
        return 0;
    }
    begin_recognize_calls += 1;
    if (begin_status == 1) {
        *record_out = &begin_record_token;
        *reason_out = NULL;
    } else {
        *record_out = NULL;
        *reason_out = &begin_reason_token;
    }
    return begin_status;
}

void phil_runtime_commit_ingress_Hello(void *transport, void *pending) {
    if (transport == expected_transport && pending == &hello_pending_token) {
        hello_commit_calls += 1;
    }
}

void phil_runtime_commit_ingress_Begin(void *transport, void *pending) {
    if (transport == expected_transport && pending == &begin_pending_token) {
        begin_commit_calls += 1;
    }
}

void phil_runtime_fail_recognition_Hello(void *pending, void *reason) {
    if (pending == &hello_pending_token && reason == &hello_reason_token) {
        hello_fail_calls += 1;
    }
}

void phil_runtime_fail_recognition_Begin(void *pending, void *reason) {
    if (pending == &begin_pending_token && reason == &begin_reason_token) {
        begin_fail_calls += 1;
    }
}

void phil_runtime_destroy_pending_Hello(void *pending, void *frame) {
    if (pending == &hello_pending_token && frame == &hello_frame_token) {
        hello_destroy_calls += 1;
    }
}

void phil_runtime_destroy_pending_Begin(void *pending, void *frame) {
    if (pending == &begin_pending_token && frame == &begin_frame_token) {
        begin_destroy_calls += 1;
    }
}

int phil_server_framed_ingress_v1_smoke(void) {
    void *pending = NULL;
    void *frame = NULL;
    void *raw = NULL;
    void *record = NULL;
    void *reason = NULL;

    reset_state();

    phil_runtime_receive_frame_Hello(expected_transport, &pending, &frame);
    raw = phil_runtime_frame_borrow_view_Hello(frame);
    if (phil_runtime_recognize_Hello(pending, raw, &record, &reason) != 1) {
        return 1;
    }
    if (record != &hello_record_token || reason != NULL) {
        return 2;
    }
    phil_runtime_commit_ingress_Hello(expected_transport, pending);

    pending = NULL;
    frame = NULL;
    raw = NULL;
    record = NULL;
    reason = NULL;
    phil_runtime_receive_frame_Begin(expected_transport, &pending, &frame);
    raw = phil_runtime_frame_borrow_view_Begin(frame);
    if (phil_runtime_recognize_Begin(pending, raw, &record, &reason) == 1) {
        return 3;
    }
    if (record != NULL || reason != &begin_reason_token) {
        return 4;
    }
    phil_runtime_fail_recognition_Begin(pending, reason);
    phil_runtime_destroy_pending_Begin(pending, frame);

    if (hello_receive_calls != 1 || hello_borrow_calls != 1
        || hello_recognize_calls != 1 || hello_commit_calls != 1
        || hello_fail_calls != 0 || hello_destroy_calls != 0) {
        return 5;
    }
    if (begin_receive_calls != 1 || begin_borrow_calls != 1
        || begin_recognize_calls != 1 || begin_commit_calls != 0
        || begin_fail_calls != 1 || begin_destroy_calls != 1) {
        return 6;
    }

    hello_status = 0;
    pending = NULL;
    frame = NULL;
    raw = NULL;
    record = NULL;
    reason = NULL;
    phil_runtime_receive_frame_Hello(expected_transport, &pending, &frame);
    raw = phil_runtime_frame_borrow_view_Hello(frame);
    if (phil_runtime_recognize_Hello(pending, raw, &record, &reason) == 1) {
        return 7;
    }
    phil_runtime_fail_recognition_Hello(pending, reason);
    phil_runtime_destroy_pending_Hello(pending, frame);
    if (hello_fail_calls != 1 || hello_destroy_calls != 1) {
        return 8;
    }

    return 0;
}
