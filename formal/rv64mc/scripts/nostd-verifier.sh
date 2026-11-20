#!/usr/bin/env bash
# Writes a `no_std` + `alloc` copy of crates/verifier to $1 (default: formal/rv64mc/guest/verifier-nostd), for the RV64IM
# guest. The rewrite is mechanical: `std::` becomes `core::` (`alloc::` for collections), every module imports the
# alloc items the std prelude gave it, and every function is `#[inline(always)]` or `#[inline(never)]` as
# ../boundaries.txt says (inline-attrs.py). crates/verifier itself is not touched.
set -euo pipefail
here=$(cd "$(dirname "$0")" && pwd)
root=$(cd "$here/../../.." && pwd)
src=${VERIFIER_SRC:-$root/crates/verifier}
out=${1:-$here/../guest/verifier-nostd}
rm -rf "$out"
mkdir -p "$out/src"
cp "$src"/src/*.rs "$out/src/"
cat > "$out/Cargo.toml" <<'EOF'
[package]
name = "verifier"
version = "0.0.0"
edition = "2024"
publish = false
EOF
for f in "$out"/src/*.rs; do
  sed -i -e 's/\bstd::collections::/alloc::collections::/g' -e 's/\bstd::/core::/g' "$f"
  if [ "$(basename "$f")" = lib.rs ]; then
    # After the inner attributes and the crate docs, before the first item.
    awk 'BEGIN{done=0} /^#!\[/ && !done {print; print "#![no_std]"; print "extern crate alloc;"; print "#[allow(unused_imports)]"; print "mod prelude {"; print "    pub use alloc::borrow::ToOwned;"; print "    pub use alloc::boxed::Box;"; print "    pub use alloc::string::{String, ToString};"; print "    pub use alloc::vec::Vec;"; print "    pub use alloc::{format, vec};"; print "}"; print "#[allow(unused_imports)]"; print "use prelude::*;"; done=1; next} {print}' "$f" > "$f.tmp"
    mv "$f.tmp" "$f"
  else
    awk 'BEGIN{done=0} !done && !/^\/\/!/ {print "#[allow(unused_imports)]"; print "use crate::prelude::*;"; done=1} {print}' "$f" > "$f.tmp"
    mv "$f.tmp" "$f"
  fi
done
python3 -I "$here/inline-attrs.py" "$here/../boundaries.txt" "$out/src"
echo "$out"
