#include <stdint.h>

static void *current_transport;
static void *current_pending;
static void *current_frame;
static void *current_raw;
static void *current_reason;

void phil_runtime_receive_frame_Hello(void) {
    (void)current_transport;
}

void phil_runtime_receive_frame_Begin(void) {
    (void)current_transport;
}

void *phil_runtime_frame_borrow_view_Hello(void) {
    return current_raw;
}

void *phil_runtime_frame_borrow_view_Begin(void) {
    return current_raw;
}

uint8_t phil_runtime_recognize_Hello(void) {
    (void)current_pending;
    (void)current_reason;
    return 0;
}

uint8_t phil_runtime_recognize_Begin(void) {
    (void)current_pending;
    (void)current_reason;
    return 0;
}

void phil_runtime_commit_ingress_Hello(void) {
    (void)current_pending;
}

void phil_runtime_commit_ingress_Begin(void) {
    (void)current_pending;
}

void phil_runtime_fail_recognition_Hello(void) {
    (void)current_reason;
}

void phil_runtime_fail_recognition_Begin(void) {
    (void)current_reason;
}

void phil_runtime_destroy_pending_Hello(void) {
    (void)current_frame;
}

void phil_runtime_destroy_pending_Begin(void) {
    (void)current_frame;
}
