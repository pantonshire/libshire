#!/bin/bash
set -e
set -o pipefail

cargo +nightly miri test --no-default-features --features serde

cargo +nightly miri test --no-default-features --features alloc,serde

cargo +nightly miri test

# 32-bit target
cargo +nightly miri test --target sparc-unknown-linux-gnu

# Big-endian target
cargo +nightly miri test --target mips64-unknown-linux-gnuabi64
