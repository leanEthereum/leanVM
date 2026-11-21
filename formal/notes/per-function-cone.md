# Per-function cones for the guest's proofs

Goal: an edit of one function of `guests/lean_ethereum.py` rebuilds that function's generated data and proofs plus a small glue layer, not the whole guest. This is the plan; what is done and what remains are at the end.

## Firewalls

Lake (`ModuleImportInfo.addImport`) puts into a module's trace each import's public olean and those of its public imports, transitively; a `meta import` brings in everything below, `import all` the private parts; a file outside the module system sees everything. So a proof-only edit rebuilds that module alone, a changed declaration or import list rebuilds the modules that see it, and a private `import` stops the rebuild at the first module whose olean is unchanged. `tools/deps.py` follows this rule, and `tools/firewall-canary.py` (run by `check-all.sh` and CI) checks it against Lake on `tests/LeanVMTests/Firewall/`.

## What stays global

The statement keeps its meaning. Global by nature: the bytecode and its layout (`Statement/Data/`), facts about the bytecode as a whole (`deployedSeed`, the decoder tables), the jump table, `main`'s entry and the halting pc. Only late glue modules import them; every per-function and generic module is data-free (checked in the build, like `Guest/Fast/Firewall.lean`), and the glue imports per-function modules privately. One statement change is for the user to decide: moving `guestProgram` and its import of `Statement.Data.Bytecode` out of `Statement/LeanVmGuest.lean`, with no definition changed.

## The layout

**Packs.** A function's generated data sits under `Guest/Pack/`, keyed by its stable name (`Data/Names.lean`: its name, a loop's `{caller}_loop{k}`), never by index: in the hash pack `Pack/P{k}/` with `k = packOf 64 key` (`PackHash.lean`, FNV-1a of the key, so an added or removed function moves no other one), or, when it is too large for one module, in `Pack/<key>/`. Each function's definitions live in its namespace `LeanVM.Guest.Fn.«key»`. A pack holds the core IR (`Core.lean`, a long function's `Core{n}.lean`).

**Glue**, late: the aggregates as lists of references to the packs (`Data/Core.lean`'s `coreFunctions`, each `Fn.«key».core`, so a link is `rfl`), and what is about the whole program (`End*`, `Budget`, the decoder tables).

## Migration, each step green

Done:

1. **Tools.** `deps.py` follows Lake's rule and reports by family; the firewall canary is in the gate.
2. **Stable names.** The hand-written proofs name functions by stable name (`fn% «s»`, `idx% «s»`, `name% «s»`, `Guest/CoreRef.lean`), so a renumbering changes no proof; `scripts/guest-changes` and the walk generators read the same keys.
3. **Core IR in packs.** `guest-core` writes each function's core IR into its pack (`Pack/P{k}/Core.lean`, `Pack/<key>/Core*.lean`), and `Data/Core.lean` lists references to them.

Remaining:

4. **Untaint.** Data imports cut out of the generic modules (`B1.Common.Basic`, `Pow`, `LimitsNZ`, ...); with the user's go, `guestProgram` moves in the statement.
5. **Memory and Count local.** The Memory and Count data in the packs, one family check per pack with callee summaries, `RangeOk` and the roots' bounds assembled in the glue; a certificate holds its own cost and the sums move to the glue, so a cheaper function does not rebuild its callers.
6. **B1 parametric**, directory by directory, old names kept as glue instantiations: `Finds P name fn` replaces `coreProgram_find?_at (j := …)`; specs become `f_SpecP P`, the old `f_Spec := f_SpecP coreProgram`; a proof takes `[Finds P "f" Fn.«f».core]` and its callees' `g_SpecP P`.

## For the user

- Moving `guestProgram` in the statement (step 4).
- Loop names in the compiler (`<fn>__loop<k>`): the generators' stable keys (`{caller}_loop{k}`) serve the proofs meanwhile.
