# recverify: the leanVM verifier as a leanVM guest

`guest/` is `leanvm_core::cpu::Program::verify` (mode 0, the full verifier) or `Program::verify_core` (mode 1, everything but the deferred claims) compiled for rv64im and run on the leanVM interpreter. `host/` proves an inner run natively, verifies it natively, lays the inner program, its output and the proof out in the guest's advice, runs the guest, and checks that the guest commits exactly the statement the native verifier accepted: the inner program's digest and output, and in mode 1 the hash of the deferred claims (`cpu::DeferredClaims`). It then reports the guest's steps, rows per table, table heights with the fill, and the committed size a proof of that run would have.

This is a research harness, not a checked-in fixture: no ELF is committed, `programs/build.sh` and `programs/clippy.sh` skip it, and no test runs it. The host is a root workspace member, so it is built, linted and formatted with the rest.

## Building

The guest builds `std` for a custom target, `riscv64im-leanvm-zkvm.json` (`os = "zkvm"`, so `build-std` takes std's single-threaded zkvm platform layer and the verifier's crates build unchanged), with its own `link.ld` (a larger RAM with a heap, and a larger advice) and a pinned nightly (`rust-toolchain.toml`, with `rust-src`). The platform layer's `sys_*` functions, a bump allocator and the `__sync_*` atomics are in `guest/src/main.rs`.

```bash
(cd programs/recverify/guest && cargo build --release)
cargo build --release -p recverify-host
ELF=programs/recverify/guest/target/riscv64im-leanvm-zkvm/release/recverify
```

On the guest target the library takes these paths, all gated on `target_arch = "riscv64"` and `target_os = "zkvm"`, so native builds are unchanged:

- `primitives::field::gf2_64x3`: every product is the machine's extension-field instruction (#397, `ext`, inline `.insn` on elements in memory): `extmul` for a product, an in-place product (`*=`) and a square (every operand the same element), `extmulk` for a product by an `F64`, `extmack` per term of `dot_base`. The products come reduced, so `F192Unreduced` holds the reduced sum (the reduction is linear, so the result is the same).
- `primitives::field::gf2_64`: the `F64` product and square are `extmulk` on the element `(a, 0, 0)`, cheaper than the software kernels in cycles and in committed words. The carry-less 64x64 product (`mul_wide`) stays software, by integer multiplies (`software::clmul_by_holes`), and the verifier no longer calls it.
- `primitives::hash`: `compress` is the machine's `blake2s` instruction, and the batched hash runs one input at a time through it.
- `zk_alloc`: no address space to reserve, so the arena stays disengaged.

## Running

From the workspace root:

```bash
target/release/recverify-host $ELF fib 1000          # Fibonacci 1,000, full verifier
target/release/recverify-host $ELF fib 1000 core     # the same, verify_core only
target/release/recverify-host $ELF fib 2000000 [core]
target/release/recverify-host $ELF xmss 400 [core]   # leanXMSS over 400 signatures
```

`RATE=<n>` sets the inner proof's log inverse rate (1 by default). The `inner:` lines describe the inner proof, the `outer:` lines the guest's run: its RAM use, the committed statement (asserted equal to the native verifier's), the steps and rows per table with each table's height after the fill, the committed words and whether they fit one proof (`pcs::MAX_MU`), and the committed words one more row costs in each table.

Two more subcommands:

- `prim <op> <n>` runs `n` of one primitive in the guest instead of a verifier (the guest's `primitive`: 0 `F64` product, 1 `F192` product, 2 `F192` square, 3 `F192` times `F64`, 4 `F192` inverse, 5 the carry-less 64x64 product, 6 a BLAKE2s compression, 7 `F64` square, 8 `F192` product accumulated unreduced, 9 `F192` product in place, 10 `F192` times `F64` accumulated unreduced, 11 an eight-term `dot_base`, anything else below 100 the loop alone). The cost of one is the difference of two runs over the difference of their `n`. `prim <100 + op> <n>` instead checks operation `op` (0 to 4 and 7 to 11) on `n` random inputs against the software kernels the guest used before it had the extension-field instructions, and the host asserts there is no mismatch.
- `words <log_ram> <log_advice> <rows of ALU LOAD STORE LD SD SHIFT MUL MULH DIV HASH EXT>` is the committed size a run of this guest with those executed rows would have, with RAM and the advice resized.

## Memory

The guest's run is billions of steps' worth of trace, so **the host never records it**. It streams the run through `rv::Machine::step`, counting the steps at each pc, and derives the rows per table, the fill (`cpu::filler::Plan`) and the committed size (`Program::stack_sizes`) from those counts exactly. It never calls `cpu::Program::execute`, `measure` or `prove` on the guest: those keep every row of the trace, and an earlier version of this host that called `measure` on a run of billions of cycles took tens of GiB and killed the session. `MEASURE=1` cross-checks the streamed numbers against `cpu::Program::measure`, and the host refuses it with an error, before recording anything, when the run is longer than `MAX_TRACED_STEPS` (a few million steps; `prim` runs fit). Keep it that way when changing the host.

What the host does hold is the inner proof's prover, which for leanXMSS 400 is the largest allocation of a run; run it under a memory cap (`systemd-run --user --scope -p MemoryMax=12G -p MemorySwapMax=0 ...`).

## Profiling and counting

`profile.py` folds the host's profiles with the guest's symbols (needs binutils' `addr2line` and `nm`). Build each variant into its own target directory:

```bash
cd programs/recverify/guest
CARGO_PROFILE_RELEASE_DEBUG=true cargo build --release --target-dir target/debuginfo
RUSTFLAGS="-C link-arg=-Tlink.ld --cfg recguest_count" cargo build --release --target-dir target/count
cd ../../..
DEBUG=programs/recverify/guest/target/debuginfo/riscv64im-leanvm-zkvm/release/recverify
COUNT=programs/recverify/guest/target/count/riscv64im-leanvm-zkvm/release/recverify
```

- `PROFILE=/tmp/steps.txt target/release/recverify-host $DEBUG xmss 400 core` writes the steps and table per pc; then `python3 programs/recverify/profile.py $DEBUG /tmp/steps.txt inner|outer [top]` charges them to the innermost inlined function or to the symbol, and `... classes` splits them into field arithmetic, soft float and plumbing, with the rows per table of each.
- `PROFILE_CALLS=/tmp/calls.txt target/release/recverify-host <elf> ...` keeps a shadow call stack; `python3 programs/recverify/profile.py <elf> /tmp/calls.txt calls [depth] [min_percent]` prints the dynamic call tree, steps inclusive of callees (use the same ELF for both).
- The counting build (`--cfg recguest_count`, declared in the workspace's `check-cfg`) keeps every field operation and compression a call (`inline(never)`), so `PROFILE_CALLS` with `$COUNT` and `python3 programs/recverify/profile.py $COUNT /tmp/calls.txt ops` counts them per verifier stage. Its step counts are not the release build's.

`model.py` models the cycles and committed words per inner proof under field-multiply options (the software kernels, a carry-less multiply pair, and the extension-field instructions the guest uses) from `measured.json`, which holds this branch's measured runs (rows, operation counts, the plumbing split) of Fibonacci 1,000, Fibonacci 2M and leanXMSS 400 in both modes: `python3 programs/recverify/model.py programs/recverify/measured.json` from the workspace root, with the host and the guest built. Regenerate `measured.json` after a change that moves the guest's costs.

## Experiments on top

The harness keeps upstream's protocol. It uses `verify_core` and `check_deferred` (#393), the WHIR configuration as a table (#396, which removes the guest's soft float) and the skip domain's Lagrange forms in linear time (#391). Changes that move the verifier's cost can be measured by merging them into a scratch branch and rerunning the host: jagged tables (#389) or one batched zerocheck and lincheck (#392). A change made before the `cpu` module was rebuilt around its domain types (#381) needs porting first: the free `cpu::verify*` functions are `Program` methods now, the bytecode tuple and table are `Lookup::Bytecode`'s, and `cpu/trace.rs` is part of `cpu/execute.rs`. With batched flock reductions `DeferredClaims` holds one batched circuit claim, so `claim_words` in the guest and the host changes with it.
