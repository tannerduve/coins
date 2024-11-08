#!/usr/bin/env sh

# Set Lean toolchain directories
TOOLCHAIN_DIR="$(lean --print-prefix)"
INCLUDE_DIR="$TOOLCHAIN_DIR/include"
# INCLUDE_DIR="/Users/tannerduve/.elan/toolchains/stable/include"
LIB_DIR="$TOOLCHAIN_DIR/lib"
LEAN_LIB_DIR="$LIB_DIR/lean"

# Step 1: Build the Lean code
lake build
lake build Coins.FFI:c

# Verify if Coins.c file was generated
if [ ! -f ".lake/build/ir/Coins/FFI.c" ]; then
    echo "Error: FFI.c not found. Please check your Lean code."
    exit 1
fi

# Step 2: Compile the C code and link with Lean runtime libraries
clang -O3 main.c .lake/build/ir/Coins/FFI.c -o main \
  -I"$INCLUDE_DIR" -L"$LEAN_LIB_DIR" -L"$LIB_DIR" \
  -lleancpp -lLean -lInit -lleanrt -lLake -lc++ -lc++abi -lm -ldl \
  -flto -ffunction-sections -lgmp -luv -fdata-sections -Wl,-dead_strip

# Step 3: Run the executable
./main
