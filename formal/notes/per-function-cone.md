# Per-function cones for the guest's proofs

Goal: an edit of one function of `crates/rec_aggregation/guests/lean_ethereum.py` rebuilds that function's generated data, certificates and proofs plus a small glue layer, not the whole guest. This is the plan the migration follows; the steps are at the end.

## Today

An edit of one function's core IR (`Guest/Data/Core05`) rebuilds 2,847 modules, 8.8 CPU-h, at least 10 min on unlimited cores (about 25 min on h3). By family: B2C 3.8 CPU-h, Checked 2.6, B1 1.8, Memory 0.2, Count 0.1, the rest 0.6. `__loop2` (114,219 instructions) is about half of Checked and B2C. The causes:

1. **Data at the root.** Every check is stated over a global index (`WinOk j i` unfolds `glob`, `fnOf j`, `coreOf j`, `certOf j`; `cplWin` also `plumbOf`, `fsN`, `sigT`, a trie of every signature; the Memory families walk ranges of `coreProgram`), so every check module imports the aggregated data through `Glob`, and B1 through `CoreData`.
2. **Generic modules carry data.** `Exec` imports `Guest.Bytecode`; `ExecC` imports `Glob`; `Statement/LeanVmGuest.lean` holds both the generic node statement and `guestProgram := assemble Data.functions 19`, so whatever needs a claim or a child imports the bytecode.
3. **Absolute positions.** Branch and call targets are `SET`s of `g^pc` (decoded through `Data.powTree`, which lists every pc), return addresses `DEREF .pc`, the jump table holds pcs, `Sig.entry` is compared with call targets. A length change moves every later function, so import isolation alone leaves most of the cone of a typical edit.
4. **Unstable keys.** Functions are named by global index (`Data.core18`, `coreProgram_find?_at (j := 2)`, `Cert.callees`), loops by a global counter (`__loop{id}`, `lower.rs`), `Data.Source` by line numbers.
5. **Totals in certificates.** Count and Memory certificates hold call-tree totals, so a cheaper function changes its ancestors'.

## (a) What stays global

The statement is unchanged in meaning. Global by nature: the bytecode list and its layout (`Statement/Data/`, 0.18 CPU-h, the floor), facts about the bytecode as a whole (`deployedSeed`, the decoder tables), the jump table, `main`'s entry, the halting pc, and the table of `g^pc` for the pcs used. Only late glue modules import them, every per-function and generic module is data-free (checked in the build, like `CertFirewall.lean`), and glue imports per-function modules with a private `import`. One statement change is for the user to decide: moving `guestProgram` and its import of `Statement.Data.Bytecode` out of `Statement/LeanVmGuest.lean` into a later or an eighteenth file, with no definition changed.

## Firewalls

Lake (v4.35, `ModuleImportInfo.addImport`) puts into a module's trace each import's public olean and those of its public imports, transitively; a `meta import` brings in everything below, `import all` the private parts; a file outside the module system sees everything. So, measured: a proof-only edit rebuilds that module alone; a changed declaration or import list rebuilds the modules that see it; a private `import` stops the rebuild at the first module whose olean is unchanged. `tools/deps.py` follows this rule, and `tools/firewall-canary.py` (run by `check-all.sh`) checks it against Lake on `tests/LeanVMTests/Firewall/`.

## The layout

**Per-function bundle**, generated, keyed by a stable name, never by index, one group per source function with its specializations (646 groups), the largest split by windows as now. Under `Guest/Fn/<key>/`: `Core` (core IR), `Code` (relative code, below), `Sig` (what a caller reads: name, `nargs`, `nret`, `env`, `pre`, `post`, `mem`, `sem`, frame size, family summaries; its own module so that a body edit keeping the interface rebuilds no caller), `Cert` (certificate, plumbing, snapshots, parts, arms, callee table, jump-table view, constant powers of `g`), the kernel checks `Checked`, `Cplw`, `Shared`, `Mem`, `Cnt` over these constants and the callees' `Sig`, and the B1 proof over any program that finds the function, importing callees' spec statements, never their proofs.

**Glue**, late: the aggregates as lists of references to the bundles (`Data.core2 := Fn.g_power_of_word.core`, so a link is `rfl`), link modules importing the bundles privately and stating `WinOk j i`, `CplOk j`, the specs about `coreProgram`, the assemblies (`Checked.all_ok`, `CplAll`, `RangeOk`), and what is about the whole program (`SoundFacts`, `Sound`, `End*`, `Budget`, decoder tables).

**Projection rule.** A check reads `Glob` only through `calleeAt`, the call and tail-call cases and `armsOk`/`tableCallsOk`. So `WinOk j i` is redefined as `checkWin (globOf j) ...` over a per-function view (callee table, jump-table view; `Glob.jt` becomes `ℕ → Option ℕ`), `Sound.b2_step` gets a transfer lemma (the view agrees with `glob` on the callees; `Pre` of a non-callee is false), and the bundle's check is a closed `decide +kernel`. Likewise `cplWin j` becomes `cplWinD (cview j)`, `shareWin j` becomes `shareWinD (sview j)`, the Memory range walks per-function checks with callee summaries, each with its old form by `rfl`. (The prototype instead stated a leaf's check for every context, `∀ G, checkWin G ... = true`, and a caller's for every context patched with its callees' signatures, checked by the kernel through `addDecl`; the closed form needs no such command.)

## (b) Position independence

Not a relocation lemma about today's checker, which treats a pc as an ordinary `Sym.gp e` with arithmetic on exponents. Instead the checker never sees an absolute pc:

- **Relative code.** A code-pointer `SET` in a bundle is tagged in its high limb, which real code never uses: `.set o t TSELF` (offset `t`), `.set o k TCALL` (callee slot `k`). `link ρ` (entry, callee entries, `g^pc` table) maps them to the real `SET`s; the glue proves `fnOf j = link ρ_j code`, linear (comparing `__loop2`'s code with a copy takes 1.3 s) and checks the `g^pc` table once.
- **Symbolic pointers.** `Sym` gains `.code t` and `.ent k`, `Sym.val` takes `ρ`: `symOf` reads the tags, `jumpKind` compares offsets, `DEREF .pc` gives `.code (i + 2)`, `calleeAt` reads the slot, a tail call to the own entry is `.code 0`, table jumps read the bundle's jump-table view (checked against `Data.jtTrie` in the glue). Untagged code reads as before, so families move one at a time.
- **Soundness once for every layout.** `Exec`, `CheckSound`, `Cpl*` read `ρ.entry`, `ρ.callee k` where they read `entry` and `Sig.entry` today.
- Positions inside a function are already offsets, but an early edit moves the later windows, so `__loop2` stays costly to edit until its windows are relative or it is split.

## (c) The families

- **B1**: parametric in the program. `Finds P name fn` replaces `coreProgram_find?_at (j := …)`; specs become `f_SpecP P`, the old `f_Spec := f_SpecP coreProgram`; a proof takes `[Finds P "f" Fn.f.core]` and its callees' `g_SpecP P`. The glue gives the instances and chains the specs.
- **Checked**, **Cplw**, **Shared**, **Chained**: per-function modules over views; `sigT` becomes callee tables; `FrameSizes`, `Plumb`, `Snaps`, `CplParts`, `CplArms` move into the bundles.
- **Memory**, **Count**: one family check per bundle with callee summaries, `RangeOk` and the roots' bounds assembled in the glue; to stop a cheaper function from rebuilding its callers, a certificate holds its own cost and the sums move to the glue.
- **Glue**: decoder tables, `SoundFacts` (122 s, 15 GB, on the critical path: split its per-function facts into the bundles), `Walk*Ok`, `Budget`, `End*`.

## Expected result

A body edit of a small function: `Statement/Data/` 0.18 CPU-h, its bundle (seconds; minutes for `sp_wots`; 3 to 4 CPU-h for `__loop2`), aggregates, links and assemblies 0.1 to 0.15, the `g^pc` table 0.1, what follows the assemblies 0.16 (critical path 4.6 min). About 0.6 CPU-h and 6 min wall, 0.4 CPU-h and 4 min once `SoundFacts` is split, against 8.2 CPU-h and 25 min. The prototype (three functions on h4, absolute pcs kept) measured an interface edit of a bundle's data rebuilding that bundle's data, check, B1 and link only, 7.5 CPU-s; a callee's `Sig` edit its caller's check and link only; plus 20 s of Lake checking traces per build.

## Risks

- About 4,000 more modules at about 1.3 s of startup each: a cold build gains 1 to 2 CPU-h. Merge tiny groups.
- The firewall rests on Lake's rule and on every guest file being a `module`; the canary fails the gate if either breaks.
- The relocation refactor (`ExecCore`, `Exec`, `Check`, `CheckSound`, `ExecC`, `Cpl*`, `Sound`, the generators) is the step with real proof work.
- Everything importing `guestProgram` rebuilds on every edit.
- A new loop renames every later `__loop{id}`; callers name callees in their core IR.
- A changed `Sig` or summary rebuilds the callers' checks.
- Every step touching `Glob`, `Check` or `Exec` rebuilds everything once.

## Migration, each step green

Cones are for a length-changing body edit of a small function.

1. **Tools.** `deps.py` follows Lake's rule and reports by family; the firewall canary in the gate. 8.8 CPU-h.
2. **Untaint.** Generic files are `module`s; data imports cut out of generic modules (`Exec`, `ExecC`, `B1.Common.Basic`, `Pow`, `LimitsNZ`, ...); with the user's go, `guestProgram` moves in the statement. 8.8 CPU-h.
3. **Bundles.** The generators write `Guest/Fn/<key>/{Core,Code,Cert,Sig}.lean`; the aggregates become references. 8.8 CPU-h.
4. **Checked local.** `WinOk` over views, the transfer lemma, per-function checks, links. 6.3 CPU-h for an edit that keeps the length, 8.8 otherwise.
5. **Relocation.** Tagged pointers, `Sym.code`/`.ent`, soundness for every `ρ`, `link` and the `g^pc` table in the glue. 6.3 CPU-h.
6. **B2C local.** `cplWinD`, `shareWinD`, callee tables, the B2C data in the bundles. 2.4 CPU-h.
7. **Memory and Count local.** 2.1 CPU-h, nearly all B1.
8. **B1 parametric**, directory by directory, old names kept as glue instantiations; can run beside 4 to 7 after 3. 0.6 CPU-h, 6 min.
9. **Glue diet.** `SoundFacts` split, generators recomputing only changed functions, relative windows for `__loop2`. 0.4 CPU-h, 4 min.

## For the user

- Moving `guestProgram` in the statement (step 2).
- Loop names in the compiler (`<fn>__loop<k>`) or stable keys in the generators.
- Splitting `__loop2` in the compiler instead of relativizing its windows.
