// main.c
#include <stdio.h>
#include <lean/lean.h>
#include <stdint.h>

// Declare the external Lean function
void lean_initialize_runtime_module();
extern uint32_t l_helper2__c(uint32_t n);
lean_object *initialize_Coins_CoinSolution(uint8_t, lean_object*);

int main() {

    lean_initialize_runtime_module();
    initialize_Coins_CoinSolution(1, lean_io_mk_world());
    lean_io_mark_end_initialization();
    uint32_t input = 999999999;
    uint32_t result = l_helper2__c(input);
    printf("helper2(%u) = %u\n", input, result);
    return 0;
}
