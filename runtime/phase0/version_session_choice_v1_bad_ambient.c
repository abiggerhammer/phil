#include <stdbool.h>
#include <stdint.h>

void *phil_record_Hello_get_versions(void) { return 0; }
bool phil_runtime_choose_supported(uint16_t *selected_version_out) {
    (void) selected_version_out;
    return false;
}
void phil_runtime_select_unsupported(void) {}
void phil_runtime_select_version(uint16_t selected_version) { (void) selected_version; }
bool phil_runtime_receive_version_choice(uint16_t *selected_version_out) {
    (void) selected_version_out;
    return false;
}
bool phil_runtime_refine_selected_version(uint16_t selected_version) {
    (void) selected_version;
    return false;
}
