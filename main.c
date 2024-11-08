// main.c
#include <stdio.h>
#include <lean/lean.h>
#include <stdint.h>

// Declare the external Lean function
void lean_initialize_runtime_module();
extern uint32_t helper2_c(uint32_t n);
lean_object *initialize_Coins_FFI(uint8_t, lean_object*);

int main() {

    lean_initialize_runtime_module();
    initialize_Coins_FFI(1, lean_io_mk_world());
    lean_io_mark_end_initialization();
    uint32_t input = 520;
    uint32_t result = helper2_c(input);
    printf("helper2(%u) = %u\n", input, result);
    return 0;
}