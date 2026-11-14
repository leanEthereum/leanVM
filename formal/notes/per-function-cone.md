# Per-function cones for the guest's proofs

Goal: an edit of one function of `crates/rec_aggregation/guests/lean_ethereum.py` rebuilds that function's generated data, certificates and proofs plus a small glue layer, not the whole guest. This is the plan; what is done and what remains are at the end.

## Why an edit rebuilds nearly everything

1. **Data at the root.** Every check is stated over a global index (`WinOk j i` unfolds `glob`, `fnOf j`, `coreOf j`, `certOf j`; `cplWin` also `plumbOf`, `fsN`, `sigT`, a trie of every signature; the Memory families walk ranges of `coreProgram`), so every check module imports the aggregated data through `Glob`, and B1 through `CoreData`.
2. **Generic modules carry data.** `Exec` imports `Guest.Bytecode`, `ExecC` imports `Glob`, and `Statement/LeanVmGuest.lean` holds both the generic node statement and `guestProgram`, so whatever needs a claim or a child imports the bytecode.
3. **Absolute positions.** Branch and call targets are `SET`s of `g^pc` (decoded through `Data.powTree`, which lists every pc), return addresses `DEREF .pc`, the jump table holds pcs, `Sig.entry` is compared with call targets. A length change moves every later function, so import isolation alone leaves most of the cone of a typical edit.
4. **Unstable keys.** The generated data names functions by global index (`Data.core{j}`, `certOf j`, `Cert.callees`) and the compiler names loops by a global counter (`__loop{id}`).
5. **Totals in certificates.** Count and Memory certificates hold call-tree totals, so a cheaper function changes its ancestors'.

## Firewalls

Lake (`ModuleImportInfo.addImport`) puts into a module's trace each import's public olean and those of its public imports, transitively; a `meta import` brings in everything below, `import all` the private parts; a file outside the module system sees everything. So a proof-only edit rebuilds that module alone, a changed declaration or import list rebuilds the modules that see it, and a private `import` stops the rebuild at the first module whose olean is unchanged. `tools/deps.py` follows this rule, and `tools/firewall-canary.py` (run by `check-all.sh` and CI) checks it against Lake on `tests/LeanVMTests/Firewall/`.

## What stays global

The statement keeps its meaning. Global by nature: the bytecode and its layout (`Statement/Data/`), facts about the bytecode as a whole (`deployedSeed`, the decoder tables), the jump table, `main`'s entry, the halting pc, and the table of `g^pc` for the pcs used. Only late glue modules import them; every per-function and generic module is data-free (checked in the build, like `B2C/CertFirewall.lean`), and the glue imports per-function modules privately. One statement change is for the user to decide: moving `guestProgram` and its import of `Statement.Data.Bytecode` out of `Statement/LeanVmGuest.lean`, with no definition changed.

## The layout

**Packs.** A function's generated data sits under `Guest/Pack/`, keyed by its stable name (`Data/Names.lean`: its name, a loop's `{caller}_loop{k}`), never by index: in the hash pack `Pack/P{k}/` with `k = packOf 64 key` (`PackHash.lean`, FNV-1a of the key, so an added or removed function moves no other one), or, when it is too large for one module, in `Pack/<key>/`. Each function's definitions live in its namespace `LeanVM.Guest.Fn.«key»`. Today a pack holds the core IR only (`Core.lean`, a long function's `Core{n}.lean`); the plan adds `Code` (relative code, below), `Sig` (what a caller reads: name, `nargs`, `nret`, `env`, `pre`, `post`, `mem`, `sem`, frame size, family summaries; its own module, so that a body edit keeping the interface rebuilds no caller), `Cert` (certificate, plumbing, snapshots, parts, arms, callee table, jump-table view, constant powers of `g`), and the kernel checks `Checked`, `Cplw`, `Shared`, `Mem`, `Cnt` over these and the callees' `Sig`.

**Glue**, late: the aggregates as lists of references to the packs (`Data/Core.lean`'s `coreFunctions`, each `Fn.«key».core`, so a link is `rfl`), link modules importing the packs privately and stating `WinOk j i`, `CplOk j`, the specs about `coreProgram`, the assemblies (`Checked.all_ok`, `CplAll`, `RangeOk`), and what is about the whole program (`SoundFacts`, `Sound`, `End*`, `Budget`, the decoder tables).

**Projection rule.** A check reads `Glob` only through `calleeAt`, the call and tail-call cases and `armsOk`/`tableCallsOk`. So `WinOk j i` becomes `checkWin (globOf j) ...` over a per-function view (callee table, jump-table view; `Glob.jt` becomes `ℕ → Option ℕ`), `Sound.b2_step` gets a transfer lemma (the view agrees with `glob` on the callees; `Pre` of a non-callee is false), and the pack's check is a closed `decide +kernel`. Likewise `cplWin j` becomes `cplWinD (cview j)`, `shareWin j` becomes `shareWinD (sview j)`, and the Memory range walks per-function checks with callee summaries, each with its old form by `rfl`.

## Position independence

Not a relocation lemma about today's checker, which treats a pc as an ordinary `Sym.gp e` with arithmetic on exponents. Instead the checker never sees an absolute pc:

- **Relative code.** A code-pointer `SET` in a pack is tagged in its high limb, which real code never uses: `.set o t TSELF` (offset `t`), `.set o k TCALL` (callee slot `k`). `link ρ` (entry, callee entries, `g^pc` table) maps them to the real `SET`s; the glue proves `fnOf j = link ρ_j code` and checks the `g^pc` table once.
- **Symbolic pointers.** `Sym` gains `.code t` and `.ent k`, and `Sym.val` takes `ρ`: `symOf` reads the tags, `jumpKind` compares offsets, `DEREF .pc` gives `.code (i + 2)`, `calleeAt` reads the slot, a tail call to the own entry is `.code 0`, table jumps read the pack's jump-table view (checked against `Data.jtTrie` in the glue). Untagged code reads as before, so families move one at a time.
- **Soundness once for every layout.** `Exec`, `CheckSound`, `Cpl*` read `ρ.entry`, `ρ.callee k` where they read `entry` and `Sig.entry` today.
- Positions inside a function are already offsets, but an early edit moves the later windows, so `main_loop2` stays costly to edit until its windows are relative or it is split.

## The families

- **B1**: parametric in the program. `Finds P name fn` replaces `coreProgram_find?_at (j := …)`; specs become `f_SpecP P`, the old `f_Spec := f_SpecP coreProgram`; a proof takes `[Finds P "f" Fn.«f».core]` and its callees' `g_SpecP P`. The glue gives the instances and chains the specs.
- **Checked**, **Cplw**, **Shared**, **Chained**: per-function modules over views; `sigT` becomes callee tables; `FrameSizes`, `Plumb`, `Snaps`, `CplParts`, `CplArms` move into the packs.
- **Memory**, **Count**: one family check per pack with callee summaries, `RangeOk` and the roots' bounds assembled in the glue; a certificate holds its own cost and the sums move to the glue, so a cheaper function does not rebuild its callers.
- **Glue**: the decoder tables, `SoundFacts` (on the critical path: split its per-function facts into the packs), `Walk*Ok`, `Budget`, `End*`.

## Risks

- More, smaller modules: their startup adds to a cold build. Merge tiny groups, as the packs do.
- The firewall rests on Lake's rule and on every guest file being a `module`; the canary fails the gate if either breaks.
- The relocation refactor (`ExecCore`, `Exec`, `Check`, `CheckSound`, `ExecC`, `Cpl*`, `Sound`, the generators) is the step with real proof work.
- Everything importing `guestProgram` rebuilds on every edit.
- A changed `Sig` or summary rebuilds the callers' checks.
- Every step touching `Glob`, `Check` or `Exec` rebuilds everything once.

## Migration, each step green

Done:

1. **Tools.** `deps.py` follows Lake's rule and reports by family; the firewall canary is in the gate.
2. **Stable names.** The hand-written proofs name functions by stable name (`fn% «s»`, `idx% «s»`, `name% «s»`, `Guest/CoreRef.lean`), so a renumbering changes no proof; `scripts/guest-changes` and the walk generators read the same keys.
3. **Core IR in packs.** `guest-core` writes each function's core IR into its pack (`Pack/P{k}/Core.lean`, `Pack/<key>/Core*.lean`), and `Data/Core.lean` lists references to them.
- **Steps 5, 6 and 8 for Checked and B2C.** The packs hold each function's code, certificate, signature, completeness and sharing data (`Bundle.lean`, `Sig.lean`) and its checks over its own data and view (`Checked*`, `Cplw*`, `Shared*`: `Check.checkWinCF`, `B2C.cplWinD`, `B2C.shareWinD`, defined in the data-free `CheckView`, `B2C/CplCheck`, `ShareCheck`, `ChainCheck`, guarded by `ViewFirewall.lean`); the completeness walk finds a callee among the function's callees (`calleeS`), the context restricted to them (`Glob.restrict`). The glue (`Checked/Link*`, `Checked/Fn*`, `B2C/Cplw/Fn*`, `B2C/Shared/Fn*`) links them to `WinOk`, `CplOk`, `ShareOk` (`Check.Link`, `cplOk_of_link`, `shareOk_of_link`). Still global: `main_loop2`'s split windows and chained `match`es (`Checked/X*`, `G*`, `B2C/Cplw/D*`, `B2C/Shared/H*`, `B2C/Chained/`).

Remaining:

4. **Untaint.** Data imports cut out of the generic modules (`Exec`, `ExecC`, `B1.Common.Basic`, `Pow`, `LimitsNZ`, ...); with the user's go, `guestProgram` moves in the statement.
5. **The rest of the packs.** The Memory and Count data in the packs (Checked's and B2C's are).
6. **`main_loop2`'s split windows local**, the rest of Checked and B2C: the group checks over the pack's data (`win_lit` on terms), the assemblies as glue.
7. **Relocation.** Tagged pointers, `Sym.code`/`.ent`, soundness for every `ρ`, `link` and the `g^pc` table in the glue.
9. **Memory and Count local.**
10. **B1 parametric**, directory by directory, old names kept as glue instantiations; can run beside 6 to 9 after 5.
11. **Glue diet.** `SoundFacts` split, generators recomputing only changed functions, relative windows for `main_loop2`.

## For the user

- Moving `guestProgram` in the statement (step 4).
- Loop names in the compiler (`<fn>__loop<k>`): the generators' stable keys (`{caller}_loop{k}`) serve the proofs meanwhile.
- Splitting `main_loop2` in the compiler instead of relativizing its windows.
