#!/bin/bash
set -e
set -o pipefail

# no_std and no alloc
cargo +nightly miri test --no-default-features --features serde

# no_std with alloc
cargo +nightly miri test --no-default-features --features alloc,serde

# std
cargo +nightly miri test --features serde

# 32-bit target
cargo +nightly miri test --target sparc-unknown-linux-gnu --features serde

# Big-endian target
cargo +nightly miri test --target mips64-unknown-linux-gnuabi64 --features serde
