#ifndef PHIL_PHASE0_STORAGE_FAILURE_DETAIL_V1_H
#define PHIL_PHASE0_STORAGE_FAILURE_DETAIL_V1_H

#include <stdint.h>

uint8_t phil_runtime_store_with_error(
    void *payload,
    void **upload_id_out,
    void **storage_error_out);

void phil_runtime_fail_storage(
    void *transport,
    void *storage_error);

int phil_storage_failure_detail_v1_smoke(void);

#endif
