#!/bin/bash
set -e
set -o pipefail

TEST_RUNS=(
    '--no-default-features --features serde'
    '--no-default-features --features alloc,serde'
    '--features serde'
    '--target sparc-unknown-linux-gnu --features serde'
    '--target mips64-unknown-linux-gnuabi64 --features serde'
)

for FLAGS in "${TEST_RUNS[@]}"
do
    cargo +nightly miri test $FLAGS
done
