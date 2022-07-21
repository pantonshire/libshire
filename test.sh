#!/bin/bash

cargo miri test

# 32-bit target
cargo miri test --target sparc-unknown-linux-gnu

# Big-endian target
cargo miri test --target mips64-unknown-linux-gnuabi64
