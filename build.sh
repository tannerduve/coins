#!/usr/bin/env sh

# Set Lean toolchain directories
TOOLCHAIN_DIR="$(lean --print-prefix)"
INCLUDE_DIR="$TOOLCHAIN_DIR/include"
LIB_DIR="$TOOLCHAIN_DIR/lib"
LEAN_LIB_DIR="$LIB_DIR/lean"

# Step 1: Build the Lean code
lake build Batteries:static Coins:static

# Step 2: Compile the C code and link with Lean runtime libraries
clang -O3 main.c -o main \
  .lake/packages/batteries/.lake/build/lib/libBatteries.a \
  .lake/build/lib/libCoins.a \
  -I"$INCLUDE_DIR" -L"$LEAN_LIB_DIR" -L"$LIB_DIR" \
  -lleancpp -lLean -lStd -lInit -lleanrt -lLake -lc++ -lc++abi -lm -ldl \
  -flto -ffunction-sections -lgmp -luv -fdata-sections -Wl,-dead_strip

# Step 3: Run the executable
./main
