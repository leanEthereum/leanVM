# Campaign backlog (carry into wave 3 briefs)

- [done, wave 3a] memset total contract stating the bytes written (SetPost), then strengthen TryAllocSpecT to give TryAllocPost's zeroed bytes (wave 2a R1-4; callers counting_sort, column_kappas, stack, stack_offsets rely on zeros).
- RawVecT: buffer disjoint from a header that lives in the heap (wave 2a R1-5; first hit: group_by_word's Vec<u16> header inside a Vec<(K, Vec<u16>)> element).
- [69, 72 done, wave 3a; 71, 70 in wave 3b's list] Drops 69, 72 (then 71, 70): rv_symT over the loop body ran >10 min at 3 GB (wave 2a); diagnose (likely the element-read terms), cut with stops.
- Input::digest (5): wave 1a draft runW1a/InputDigestT.draft.lean, 4M heartbeats, six goals (WordPreT rebuilt across calls; return address read back).
- memmove (225): MemmoveSpecT stated, not proved (wave 2b may take it).
- Pass-through reserve callers (SpecExtend VecE, VecForm, ExtendTrustedMap BusBlock): their callers carry RawVecT.
- Partial-side fix of MemcpySpec merged (ed65561cfb): defect witnessed, specs corrected.
- Partial MemcpySpec/MemmoveSpec (corrected by the fix-copy merge ed65561cfb) are still open class-C hypotheses of the partial Table instances: discharging them needs a partial port of MemcpyT (864 lines, without Windows/WinOk) and a memmove proof. Lower priority than MainSpecT; TContract.contract/HoldsT.holds bridge exists but needs Windows in the partial pre.

- Wave 3a R1-2 (deferred): CloneT/ColumnClaimT posts omit the copied bytes; needs a slot-apart-from-source conjunct (true at all 8 sites). Only for functional proofs.
- Wave 3c (after 2b frees leanVM-t-symt): WHIR and ring-switch (75, 77, 79, 82, 83, 103, 116, 126, 132, 133, 134, 140, 212, 119), Input::digest (5).
- Wave 3c finding: the partial `Dot.Pre` (#822, class A) asks `Live` (heap), unsatisfiable at 4 image sites passing stack slices (closure#2 of verify_bus_balance steps 47/80/99, verify_keccak 578). Wave 4b adds a second total contract; the partial spec should get the same widening when 158/60 get partial proofs. Same reading owed for eq_eval, poly_eval, index_mle, padding_weight, ring_psi Live pres.
- Workflow: lifecycle.workflow.js now takes implementPasses (fresh implementers continue the list).
- Executor bug: `TryMapT.fin` prints `PANIC at Lean.Expr.appArg! ... application expected` (info level, build succeeds, axioms standard). Comes from Tactic/ (rv_symT or a closer) calling appArg! on a non-application. Find and guard it before the PR leaves draft (CI greps may flag it).
- PlacementNextT: IterT does not force sret/r apart from the shunt's end word; build_layout's proof must supply the offsets (notes say which).
- rv_autoT's `through` had no effect in wave 4a (D4, R2): possible parse bug in Tactic/Sym.lean elabArgs (rvThrough node layout). Check alongside the PANIC.
