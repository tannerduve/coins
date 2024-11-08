// main.c
#include <stdio.h>
#include <stdint.h>

// Declare the external Lean function
extern uint32_t helper2_c(uint32_t n);

int main() {
    uint32_t input = 10;
    uint32_t result = helper2_c(input);
    printf("helper2(%u) = %u\n", input, result);
    return 0;
}
