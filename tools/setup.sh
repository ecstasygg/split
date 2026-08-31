#!/bin/sh
set -eu
cache="${SPLIT_CACHE:-$HOME/.cache/split}"
mkdir -p "$cache"
if [ ! -f "$cache/sdk.tar.gz" ]; then
  curl -fL --retry 2 https://github.com/seL4/microkit/releases/download/2.3.1/microkit-sdk-2.3.1-linux-x86-64.tar.gz -o "$cache/sdk.tar.gz"
fi
if [ ! -f "$cache/source.tar.gz" ]; then
  curl -fL --retry 2 https://codeload.github.com/seL4/microkit/tar.gz/refs/tags/2.3.1 -o "$cache/source.tar.gz"
fi
printf '%s  %s\n' b1b285b8785db7557eba6d0665dd4fbf2f265ea5c0b39d6f91ae3dcc43d2c424 "$cache/sdk.tar.gz" 67ae034628465c35169c398dd7d9ea61dbe8bd93c7a9adb05b9bb31bae25c22f "$cache/source.tar.gz" | sha256sum -c -
if [ ! -d "$cache/microkit-sdk-2.3.1" ]; then
  tar -xzf "$cache/sdk.tar.gz" -C "$cache"
fi
tar -xzf "$cache/source.tar.gz" -C "$cache"
patch -s -p1 -d "$cache/microkit-2.3.1" < "$(dirname "$0")/microkit.patch"
cargo build --release --locked -p microkit-tool --manifest-path "$cache/microkit-2.3.1/Cargo.toml"
