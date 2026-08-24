#ifndef PHIL_PHASE0_SERVER_FRAMED_INGRESS_V1_H
#define PHIL_PHASE0_SERVER_FRAMED_INGRESS_V1_H

#include <stdint.h>

void phil_runtime_receive_frame_Hello(void *transport, void **pending_out, void **frame_out);
void phil_runtime_receive_frame_Begin(void *transport, void **pending_out, void **frame_out);

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

int phil_server_framed_ingress_v1_smoke(void);

#endif
