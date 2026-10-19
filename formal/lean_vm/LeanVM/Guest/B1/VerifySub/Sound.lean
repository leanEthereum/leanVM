/-
  LeanVM.Guest.B1.VerifySub.Sound

  `verify_sub`'s soundness: its relation, over the callees' soundness, implies its meaning.
-/

module

public import LeanVM.Guest.B1.VerifySub.Tail
public import LeanVM.Guest.B1.VerifySub.Layout

/-!
# `verify_sub` is sound (TRIAGE #44)

`verify_sub_sound`: on a memory of `2^κ` words, `6 ≤ κ ≤ 32`, over the exponent tables, for a
bytecode of `2^22` words, and given the callees' soundness (`SoundGkr`, `SoundTables`,
`SoundFlock`, `SoundPlace`, `HypKappa`, `SoundOpen`, `SoundTerm`, from groups 4 and 5),
`verify_sub`'s relation implies `MeaningVerifySub`: the deferring verifier accepts the proof
made of the words the guest read and the openings `open_stacked` read, for the statement `pi`
under `seed`, with the claims on the fixed polynomials, of the guest's shape, at `defer_out`.

The proof reads each phase off the body (`Front`, `Challenges`, `Ring`, `Loops`, `Tail`), turns
each callee's relation into its outcome, ties the chain states phase to phase by
`digestScalars_injective`, and hands the phases' runs to `verifyDeferred_true`. The sizes are
tied together by the layout's lemmas: the bus depth `verify_sub` computes from `block_kappa` is
`pushDepth`, and the stack's log from `certify_placement`'s total is `stackLog`.
-/

namespace LeanVM.Guest.B1.VerifySub

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.Blake2sHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

variable {rd : Reader} {σ : Val}

theorem readsAt_unique {p : E} {xs ys : List E} (hl : xs.length = ys.length) (hx : ReadsAt rd p xs)
    (hy : ReadsAt rd p ys) : xs = ys :=
  List.ext_getElem hl fun k h1 h2 => loadHolds_unique (hx k h1) (hy k h2)

theorem prod_map_gen_pow (l : List ℕ) (f : ℕ → ℕ) :
    (l.map fun x ↦ gen ^ f x).prod = gen ^ (l.map f).sum := by
  induction l with
  | nil => simp
  | cons x l ih => rw [List.map_cons, List.prod_cons, ih, List.map_cons, List.sum_cons, pow_add]

theorem kappaBase_getD (m : ℕ) (hs : List ℕ) (hl : hs.length = 6) :
    ∀ i < 8, (kappaBase (gen ^ m) (hs.map (gen ^ ·))).getD i 0 = gen ^ (0 :: m :: hs).getD i 0
  | 0, _ => by simp [kappaBase]
  | 1, _ => by simp [kappaBase]
  | i + 2, hi => by
    simp only [kappaBase, List.getD_cons_succ]
    rw [List.getD_eq_getElem _ _ (by simp [hl]; omega), List.getD_eq_getElem _ _ (by omega),
      List.getElem_map]

/-- The block kappas over a certified base are g-powers. -/
theorem blockKappas_pow (m : ℕ) (hs : List ℕ) (hl : hs.length = 6) (b : ℕ) (hb : b < 37) :
    (blockKappas (gen ^ m) (hs.map (gen ^ ·))).getD b 0 =
      gen ^ (pushKappas m hs).getD b 0 := by
  rw [pushKappas_eq m hs hl, List.getD_eq_getElem _ _ (by simp [blockKappas]; omega),
    List.getD_eq_getElem _ _ (by simp; omega)]
  simp only [blockKappas, List.getElem_map, List.getElem_range]
  have hsrc := blockKappaSrc_lt b (by omega)
  rw [pow_add]
  congr 1
  exact kappaBase_getD m hs hl _ hsrc

theorem pushKappas_length (m : ℕ) (hs : List ℕ) (hl : hs.length = 6) :
    (pushKappas m hs).length = 37 := by
  rw [pushKappas_eq m hs hl]; simp

theorem pushKappas_le (m : ℕ) (hs : List ℕ) (hl : hs.length = 6) (hm : m ≤ 32)
    (hh : ∀ h ∈ hs, h < 29) : ∀ b < 37, (pushKappas m hs).getD b 0 ≤ 32 := by
  intro b hb
  rw [pushKappas_eq m hs hl, List.getD_eq_getElem _ _ (by simp; omega)]
  simp only [List.getElem_map, List.getElem_range]
  rw [blockKappaAdj_eq b (by omega)]
  have hsrc := blockKappaSrc_lt b (by omega)
  have hg : ∀ i, (0 :: m :: hs).getD i 0 ≤ 32 := fun i => by
    match i with
    | 0 => simp
    | 1 => simpa using hm
    | i + 2 =>
      simp only [List.getD_cons_succ]
      rw [List.getD_eq_getElem?_getD]
      cases e : hs[i]? with
      | none => simp
      | some v => have := hh v (List.mem_of_getElem? e); simp; omega
  by_cases hadj : b = 2 ∨ b = 39
  · rcases hadj with rfl | rfl <;> simp [blockKappaSrc]
  · simp only [hadj, ↓reduceIte, add_zero]
    exact hg _

/-- **The bus depth is the push side's** (G:2124-2128 against V:1474). -/
theorem vs_depth (h : VsHolds rd σ) (ht : ExpTables rd (σ (.n 4)) (σ (.n 5))) {m : ℕ}
    (hm : m ≤ 32) {hs : List ℕ} (hl : hs.length = 6) (hh : ∀ h ∈ hs, h < 29)
    (h144 : σ (.n 144) = gen ^ m) (hdw : dimsWords σ = hs.map (gen ^ ·)) :
    σ (.n 416) = gen ^ ((pushKappas m hs).map (2 ^ ·)).sum := by
  obtain ⟨-, -, hbk⟩ := vs_kappas (h.to 2136) (by decide)
  obtain ⟨hp, hprod⟩ := vs_push h
  rw [h144, hdw] at hbk
  have hq : ∀ b < 37, σ (.n (pushK b + 2)) = gen ^ 2 ^ (pushKappas m hs).getD b 0 := by
    intro b hb
    obtain ⟨l1, l2⟩ := hp b hb
    have hk : σ (.n (pushK b)) = gen ^ (pushKappas m hs).getD b 0 := by
      rw [← blockKappas_pow m hs hl b hb, List.getD_eq_getElem _ _ (by simp [blockKappas]; omega)]
      exact loadHolds_unique l1 (hbk b (by simp [blockKappas]; omega))
    rw [hk, loadHolds_mul_gen_pow, Nat.add_zero] at l2
    exact loadHolds_unique l2 (ht _ (by have := pushKappas_le m hs hl hm hh b hb; show _ < 34; omega)).2
  rw [hprod, List.map_congr_left (fun b hb => hq b (List.mem_range.mp hb))]
  have hlen := pushKappas_length m hs hl
  rw [← map_getD_range (pushKappas m hs) (2 ^ ·), hlen, prod_map_gen_pow]

theorem layoutOf_logMemory (bytecode : List K) (m : ℕ) (rows : List ℕ) :
    (layoutOf bytecode m rows).logMemory = m := rfl

theorem layoutOf_logBytecode {bytecode : List K} (hb : bytecode.length = 2 ^ 22) (m : ℕ)
    (rows : List ℕ) : (layoutOf bytecode m rows).logBytecode = 18 := by
  show Nat.log2 bytecode.length - busBits = 18
  rw [hb, Nat.log2_two_pow]; rfl

theorem layoutOf_heights (bytecode : List K) (m : ℕ) (rows : List ℕ) :
    (layoutOf bytecode m rows).tableLogHeights = rows.map log2Ceil := rfl

theorem readWords_eq (σ : Val) {m r : ℕ} {rows : List ℕ} (hl : rows.length = 6)
    (h15 : σ (.n 15) = eOfNat m) (h121 : σ (.n 121) = eOfNat r)
    (hr : ∀ t < 6, σ (.n (rdB (t + 1))) = eOfNat (rows.getD t 0)) :
    readWords σ 8 = announce m rows r := by
  obtain ⟨a, b, c, d, e, f, rfl⟩ : ∃ a b c d e f, rows = [a, b, c, d, e, f] := by
    match rows, hl with
    | [a, b, c, d, e, f], _ => exact ⟨a, b, c, d, e, f, rfl⟩
  have h0 := hr 0 (by omega); have h1 := hr 1 (by omega); have h2 := hr 2 (by omega)
  have h3 := hr 3 (by omega); have h4 := hr 4 (by omega); have h5 := hr 5 (by omega)
  simp only [rdB, List.getD_cons_zero, List.getD_cons_succ] at h0 h1 h2 h3 h4 h5
  simp only [readWords, announce, List.range_succ, List.range_zero, List.nil_append,
    List.map_cons, List.map_nil, rdB, List.cons_append]
  rw [h15, h0, h1, h2, h3, h4, h5, h121]

/-! ## Results a program always returns -/

/-- Every run of `p` returns a value satisfying `Q`. -/
def Rets {α : Type} (Q : α → Prop) (p : Prog α) : Prop :=
  ∀ s a s', runId p s = some (a, s') → Q a

theorem rets_ret {α : Type} {Q : α → Prop} {a : α} (h : Q a) : Rets Q (Prog.ret a) :=
  fun s b s' hr => by
    have hr' : some (a, s) = some (b, s') := hr
    simp only [Option.some.injEq, Prod.mk.injEq] at hr'
    exact hr'.1 ▸ h

theorem rets_bind {α β : Type} {Q : α → Prop} {R : β → Prop} {p : Prog α} {f : α → Prog β}
    (hp : Rets Q p) (hf : ∀ x, Q x → Rets R (f x)) : Rets R (p >>= f) := fun s b s' hr => by
  rw [prog_bind_eq, run_bind] at hr
  cases h : runId p s with
  | none => rw [h] at hr; exact absurd hr (by simp)
  | some r =>
    rw [h] at hr
    exact hf r.1 (hp s r.1 r.2 h) _ _ _ hr

theorem rets_true {α : Type} (p : Prog α) : Rets (fun _ => True) p := fun _ _ _ _ => trivial

/-- The bus result's point is GKR's. -/
theorem busRest_point (ev : Evaluations) (layout : Layout) (alphas : List E) (beta : E)
    (point treeValues : List E) :
    Rets (fun b => b.point = point) (busRest ev layout alphas beta point treeValues) := by
  unfold busRest
  exact rets_bind (rets_true _) fun _ _ => rets_bind (rets_true _) fun _ _ =>
    rets_bind (rets_true _) fun _ _ => rets_bind (rets_true _) fun _ _ => rets_ret rfl

theorem tablesSeg_point {ev : Evaluations} {layout : Layout} {pi : Digest} {alphas : List E}
    {beta : E} {point treeValues : List E} {cv cv' : Digest} {xs : List E} {bus : BusResult}
    {claims : List ColumnClaim}
    (h : RunsTo (tablesSeg ev layout pi alphas beta point treeValues) cv xs (bus, claims) cv') :
    bus.point = point := by
  have hr : Rets (fun r : BusResult × List ColumnClaim => r.1.point = point)
      (tablesSeg ev layout pi alphas beta point treeValues) := by
    unfold tablesSeg
    exact rets_bind (busRest_point ev layout alphas beta point treeValues) fun b hb =>
      rets_bind (rets_true _) fun _ _ => rets_bind (rets_true _) fun _ _ => rets_ret hb
  exact hr _ _ _ (h [] [] [])

theorem sum_le_of_le (l : List ℕ) (B : ℕ) (h : ∀ x ∈ l, x ≤ B) : l.sum ≤ l.length * B := by
  have := List.sum_le_length_nsmul l B h
  simpa using this

/-- **`verify_sub` is sound** (TRIAGE #44). -/
theorem verify_sub_sound {κ : ℕ} (hκ : κ ≤ 32) (hκ6 : 6 ≤ κ) (Lm : MemImage κ) {bytecode : List K}
    (hb : bytecode.length = 2 ^ 22)
    {TCtx : Reader → Layout → BusResult → List ColumnClaim → List E → Prop}
    {PCtx : Reader → List ℕ → E → E → Prop}
    (hgkr : SoundGkr Lm.read) (htab : SoundTables bytecode TCtx Lm.read) (hfl : SoundFlock Lm.read)
    (hpl : SoundPlace PCtx Lm.read) (hkap : HypKappa PCtx Lm.read) (hop : SoundOpen Lm.read)
    (hterm : SoundTerm TCtx PCtx Lm.read) {args : List E}
    (ht : ExpTables Lm.read (args.getD 4 0) (args.getD 5 0))
    (h : coreProgram.Rel Lm.read "verify_sub" args []) :
    MeaningVerifySub bytecode Lm.read args [] := by
  obtain ⟨σ, rfl, hv⟩ := verify_sub_holds h
  simp only [List.getD_cons_succ, List.getD_cons_zero] at ht
  -- the seed, the sizes, the root
  obtain ⟨seed, pi, hseed, hpi, h12⟩ := vs_seed (hv.to 2136) (by decide)
  obtain ⟨hrd, hst, hrows⟩ := vs_reads hv h12
  obtain ⟨r, hr1, hr2, h121, h138⟩ := vs_rate hκ hκ6 Lm hv ht
  obtain ⟨m, hm1, hm2, h15, h144⟩ := vs_logMem hκ hκ6 Lm (hv.to 2136) (by decide) ht
  obtain ⟨-, -, h447, root, hroot⟩ := vs_root hv (hst 8 le_rfl)
  obtain ⟨hdims, hbase, hbk⟩ := vs_kappas (hv.to 2136) (by decide)
  -- the bus challenges
  obtain ⟨har, h499⟩ := vs_alphas hv h447
  have hal : (sqAll 4 (obsAll (obsAll (blake2sBytes (digestBytes seed ++ digestBytes pi))
      (readWords σ 8)) [σ (.n 419), σ (.n 434)])).1.length = 4 := by simp [sqAll_eq]
  have hfpw := vs_fpw (hv.to 2136) (by decide) hal har
  obtain ⟨h690, h698, h700⟩ := vs_beta hv h499
  -- GKR
  have cG := hv.call 806 "verify_bus_gkr" [.n 690, .n 691, .n 700, .n 417, .n 418]
    [.n 701, .n 702, .n 703, .n 704, .n 705, .n 706] (by decide +kernel)
  simp only [List.map_cons, List.map_nil] at cG
  obtain ⟨cvG0, depth, xsG, gr, cvG, hcvG0, h417, hdepth, hxsG, hrunG, hptl, hvl, hzeta, hretsG⟩ :=
    hgkr _ _ _ _ _ _ cG
  rw [h690] at hcvG0
  have ecvG0 := digestScalars_injective hcvG0
  subst ecvG0
  simp only [List.cons_append, List.nil_append, List.cons.injEq] at hretsG
  obtain ⟨r701, r702, r703, hgr⟩ := hretsG
  have e707 := hv.atom 807 (.copy (.n 707) (.n 701)) (by decide +kernel)
  have e708 := hv.atom 808 (.copy (.n 708) (.n 702)) (by decide +kernel)
  simp only [Atom.Holds] at e707 e708
  -- the tables
  have cT := hv.call 810 "verify_tables" [.n 707, .n 708, .n 703, .n 0, .n 1, .n 418, .n 417,
    .n 143, .n 30, .n 163, .n 5, .n 508, .n 698, .n 7, .n 8, .n 709, .n 704, .n 705, .n 706]
    [.n 710, .n 711, .n 712, .n 713, .n 714, .n 715] (by decide +kernel)
  simp only [List.map_cons, List.map_nil] at cT
  rw [h144] at hdims hbk hbase
  have hpre : TablesPre Lm.read (σ (.n 4)) pi m
      (sqAll 4 (obsAll (obsAll (blake2sBytes (digestBytes seed ++ digestBytes pi))
        (readWords σ 8)) [σ (.n 419), σ (.n 434)])).1 gr.2.1 gr.2.2
      [σ (.n 707), σ (.n 708), σ (.n 703), σ (.n 0), σ (.n 1), σ (.n 418), σ (.n 417),
        σ (.n 143), σ (.n 30), σ (.n 163), σ (.n 5), σ (.n 508), σ (.n 698), σ (.n 7), σ (.n 8),
        σ (.n 709), σ (.n 704), σ (.n 705), σ (.n 706)] :=
    ⟨hpi, hzeta, by rw [h417, hptl], by omega, hm1, hm2,
      ⟨dimsWords σ, by simp [dimsWords], hdims, hbk⟩, ht, hal, hfpw, hgr.symm⟩
  obtain ⟨cvT0, xsT, cvT, rowsN, bus, claims, hcvT0, hrl, hrowsR, hdimsR, hlogs, hxsT, hrunT,
    hcl, hpool, hctx, hfsT, hcurT⟩ := htab _ _ _ _ _ _ _ _ hpre cT
  rw [e707, e708, r701, r702] at hcvT0
  have ecvT0 := digestScalars_injective hcvT0
  subst ecvT0
  -- the rows and their heights
  have hrowsW : ∀ t < 6, σ (.n (rdB (t + 1))) = eOfNat (rowsN.getD t 0) := fun t ht' => by
    rw [List.getD_eq_getElem _ _ (by omega)]
    have := hrowsR t (by simp [hrl]; omega)
    rw [List.getElem_map] at this
    exact loadHolds_unique (hrows t ht') this
  have hann := readWords_eq σ hrl h15 h121 hrowsW
  rw [hann] at h447 har hal hfpw hpre hrunT
  have hdw : dimsWords σ = (rowsN.map log2Ceil).map (gen ^ ·) := by
    have := readsAt_unique (by simp [dimsWords, hrl]) hdims hdimsR
    rw [List.cons.injEq] at this
    rw [this.2, List.map_map]
    rfl
  have hhs : ∀ h ∈ rowsN.map log2Ceil, h < 29 := by
    intro x hx; obtain ⟨n, hn, rfl⟩ := List.mem_map.mp hx; exact hlogs n hn
  have hhl : (rowsN.map log2Ceil).length = 6 := by simp [hrl]
  -- the bus depth
  obtain ⟨N, hN, h416, hlN, h417'⟩ := vs_busMu hκ hκ6 Lm hv ht
  have hS := vs_depth hv ht hm2 hhl hhs h144 hdw
  have hSlt : ((pushKappas m (rowsN.map log2Ceil)).map (2 ^ ·)).sum ≤ 37 * 2 ^ 32 := by
    have := sum_le_of_le ((pushKappas m (rowsN.map log2Ceil)).map (2 ^ ·)) (2 ^ 32) (by
      intro x hx
      obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hx
      obtain ⟨b, hb', rfl⟩ := List.getElem_of_mem hk
      have := pushKappas_le m _ hhl hm2 hhs b (by rw [pushKappas_length m _ hhl] at hb'; exact hb')
      rw [List.getD_eq_getElem _ _ hb'] at this
      exact Nat.pow_le_pow_right (by decide) this)
    rwa [List.length_map, pushKappas_length m _ hhl] at this
  rw [h416] at hS
  have eN := gen_pow_inj (by omega) (by omega) hS
  rw [h417'] at h417
  have edepth := gen_pow_inj (by omega) (by omega) h417
  have hpd := pushDepth_eq hb m rowsN hrl
  rw [← eN] at hpd
  rw [← hpd] at edepth
  have hd18 : 18 ≤ depth := by
    rw [← edepth, hpd, eN]
    have : 2 ^ 17 < ((pushKappas m (rowsN.map log2Ceil)).map (2 ^ ·)).sum := by
      simp only [pushKappas, List.map_append, List.sum_append, List.map_cons, List.sum_cons]
      have := Nat.one_le_two_pow (n := m)
      omega
    exact log2Ceil_ge this
  -- Flock
  have e710 := hv.atom 811 (.copy (.n 716) (.n 710)) (by decide +kernel)
  have e711 := hv.atom 812 (.copy (.n 717) (.n 711)) (by decide +kernel)
  have l718 := hv.atom 813 (.load (.n 718) (.n 143) 6) (by decide +kernel)
  simp only [Atom.Holds] at e710 e711 l718
  have h718 : σ (.n 718) = gen ^ (rowsN.map log2Ceil).getD 5 0 := by
    have := hdimsR 6 (by simp [hrl])
    rw [loadHolds_unique l718 this]
    simp only [List.getElem_cons_succ, List.getElem_map]
    rw [List.getD_eq_getElem _ _ (by simp [hrl]), List.getElem_map]
  have hτ : (rowsN.map log2Ceil).getD 5 0 < 29 := by
    rw [List.getD_eq_getElem _ _ (by simp [hrl])]
    exact hhs _ (List.getElem_mem _)
  have cF := hv.call 819 "verify_flock" [.n 716, .n 717, .n 712, .n 718, .n 721, .n 722, .n 723]
    [.n 724, .n 725, .n 726, .n 727, .n 728, .n 729] (by decide +kernel)
  simp only [List.map_cons, List.map_nil] at cF
  rw [h718] at cF
  obtain ⟨cvF0, xsF, cvF, zSkip, alpha, mv, chi, rcs, sl, hcvF0, hxsF, hchil, hrcsl, hsll, hchi,
    hrcs, hsr, hrunF, hretsF⟩ := hfl _ _ _ _ _ _ _ _ hτ cF
  rw [e710, e711, hfsT] at hcvF0
  have ecvF0 := digestScalars_injective hcvF0
  subst ecvF0
  simp only [List.cons.injEq] at hretsF
  obtain ⟨r724, r725, r726, r727, r728, r729, -⟩ := hretsF
  -- the ring switch
  have e724 := hv.atom 820 (.copy (.n 730) (.n 724)) (by decide +kernel)
  have e725 := hv.atom 821 (.copy (.n 731) (.n 725)) (by decide +kernel)
  simp only [Atom.Holds] at e724 e725
  have h730 : (σ (.n 730), σ (.n 731)) = digestScalars cvF := by rw [e724, e725, r724, r725]
  obtain ⟨hmc, h810⟩ := vs_mapChallenges hv h730
  have hmcl : (sqAll 6 cvF).1.length = 6 := by simp [sqAll_eq]
  have hct := vs_ctable hv hmcl hmc
  have htr := vs_transposed hv hsll hsr hmcl hmc
  have hzv := vs_zvals hv hτ h718 hchil hrcsl hchi hrcs
  -- the batching
  obtain ⟨h1171, h1179, hlp, h1627⟩ := vs_lam hv h810 (by rw [List.length_map, hcl]) hpool
  rw [htr, List.length_map] at h1627
  -- the placement and the stack's size
  have cP := hv.call 1913 "certify_placement" [.n 155, .n 5] [.n 1629, .n 1630, .n 1631]
    (by decide +kernel)
  simp only [List.map_cons, List.map_nil] at cP
  rw [hdw] at hbase
  obtain ⟨off, kap, hretsP, hpctx⟩ := hpl _ _ _ m _ _ ht hm2 hhl hhs hbase cP
  simp only [List.cons.injEq] at hretsP
  obtain ⟨r1629, r1630, r1631, -⟩ := hretsP
  obtain ⟨N2, hN2, h1629, hμ1, hμ2, hopen⟩ := vs_stackSel hκ hκ6 Lm hv ht hr1 hr2 h138
  have hST := stackTotal_lt m (rowsN.map log2Ceil) hm2 hhs
  rw [r1629] at h1629
  have eST := gen_pow_inj (by omega) (by omega) h1629
  rw [← eST] at hμ1 hμ2 hopen
  have hsl : (layoutOf bytecode m rowsN).stackLog =
      max 15 (log2Ceil (stackTotal (columnKappas m 18 (rowsN.map log2Ceil)))) :=
    stackLog_eq hb m rowsN
  rw [← hsl] at hμ1 hμ2 hopen
  -- the opening
  obtain ⟨cvW0, xsW, os, w, cvW, roots', hcvW0, hxsW, hrunW, pt, hretsW, hpt, hwl⟩ :=
    hop _ _ hμ1 hμ2 hr1 hr2 root _ _ _ _ _ _ _ hroot hopen
  rw [h1171] at hcvW0
  have ecvW0 := digestScalars_injective hcvW0
  subst ecvW0
  simp only [List.cons.injEq] at hretsW
  obtain ⟨r1648, r1649, r1650, r1651, -⟩ := hretsW
  -- the terminal
  have hkb := hkap _ _ _ hpctx (by rw [hsl] at hμ2; omega)
  have hbusp : bus.point.length < 33 := by
    have hT0 := hrunT (.claimed ⟨gr.2.1.take (layoutOf bytecode m rowsN).logBytecode ++
      (sqAll 4 (obsAll (obsAll (blake2sBytes (digestBytes seed ++ digestBytes pi))
        (announce m rowsN r)) [σ (.n 419), σ (.n 434)])).1, σ (.n 714), 0, 0, [], [], [], 0⟩)
      (bytecodeAt_claimed _ bytecode)
    rw [tablesSeg_point hT0, hptl]; exact hdepth
  have cE := hv.call 1927 "check_opening_terminal" [.n 418, .n 709, .n 715, .n 417, .n 713,
    .n 144, .n 718, .n 8, .n 1180, .n 1630, .n 1631, .n 734, .n 733, .n 1649, .n 1650, .n 1651,
    .n 1648] [] (by decide +kernel)
  simp only [List.map_cons, List.map_nil] at cE
  have hacc := hterm (layoutOf bytecode m rowsN) bus claims (σ (.n 1179))
    (rcs.reverse ++ chi.drop 8) (ringCoefficients (sqAll 6 cvF).1) w
    [σ (.n 418), σ (.n 709), σ (.n 715), σ (.n 417), σ (.n 713), σ (.n 144), σ (.n 718), σ (.n 8),
      σ (.n 1180), σ (.n 1630), σ (.n 1631), σ (.n 734), σ (.n 733), σ (.n 1649), σ (.n 1650),
      σ (.n 1651), σ (.n 1648)]
    ⟨hctx, (by rw [r1630, r1631, layoutOf_logMemory, layoutOf_logBytecode hb,
        layoutOf_heights]; exact hpctx), (by rw [r1631]; exact hkb), (by rw [h144, layoutOf_logMemory]),
      (by rw [h718, layoutOf_heights]; rfl), (by rw [hcl]; exact hlp), hzv,
      (readsAt_of_getD fun k hk => hct k (by simpa [ringCoefficients, kBits] using hk)),
      (by rw [r1649]; exact hpt), r1650, r1651, r1648, (by simp only [layoutOf]),
      (by simp only [layoutOf]), (by omega), (by rw [layoutOf_logMemory]; omega), hbusp,
      (by rw [hwl]), (by rw [layoutOf_heights]; simp [hrcsl, hchil, opBlake2s]; omega),
      (by simp [ringCoefficients, kBits])⟩ cE
  -- the deferring verifier accepts
  rw [← r727, ← r728, ← r729] at hrunF
  have hrows32 : ∀ n ∈ rowsN, n ≤ 2 ^ 32 := fun n hn =>
    le_trans (le_two_pow_log2Ceil n) (Nat.pow_le_pow_right (by decide) (by have := hlogs n hn; omega))
  set cc : FixedClaims := ⟨gr.2.1.take 18 ++ (sqAll 4 (obsAll (obsAll
      (blake2sBytes (digestBytes seed ++ digestBytes pi)) (announce m rowsN r))
      [σ (.n 419), σ (.n 434)])).1, σ (.n 714), σ (.n 728), σ (.n 727), chi.take 8, rcs.reverse, sl,
      σ (.n 729)⟩ with hcc
  refine ⟨seed, pi, cc, ⟨announce m rowsN r ++ σ (.n 419) :: σ (.n 434) ::
      (xsG ++ (xsT ++ (xsF ++ xsW))), os⟩, hseed, hpi, ?_, ?_, ?_⟩
  · rw [← edepth, hann] at hrunG
    rw [h1627, h1179] at hrunW
    rw [h1179] at hacc
    rw [h698] at hrunT
    have hT := hrunT (.claimed cc) (by rw [layoutOf_logBytecode hb]; exact bytecodeAt_claimed cc bytecode)
    have hF : RunsTo (verifyFlock (.claimed cc) (blake2sR1csLogSize +
        (layoutOf bytecode m rowsN).tableLogHeights.getD opBlake2s 0)) cvT xsF
        (rcs.reverse ++ chi.drop 8, sl) cvF := by
      rw [layoutOf_heights]; exact hrunF (.claimed cc) (matricesAt_claimed cc)
    refine verifyDeferred_true hb seed pi cc hm1 hm2 hr1 hr2 hrl hrows32 hμ1 hμ2 hroot
      (cv10 := obsAll (obsAll (blake2sBytes (digestBytes seed ++ digestBytes pi)) (announce m rowsN r))
        [σ (.n 419), σ (.n 434)]) (gr := gr) (bus := bus) (claims := claims)
      (fp := rcs.reverse ++ chi.drop 8) (s := sl) (w := w) (roots' := roots') (cvG := cvG)
      (cvT := cvT) (cvF := cvF) (cvW := cvW) (xsG := xsG) (xsT := xsT) (xsF := xsF) (xsW := xsW)
      (os := os) rfl ?_ ?_ ?_ ?_ ?_
    · convert hrunG using 2
    · convert hT using 2
      rw [hann]
    · convert hF using 2
    · convert hrunW using 2
    · convert hacc using 2
  · refine ⟨?_, ?_, by simp [hcc, hrcsl], by simp [hcc, hsll]⟩
    · simp only [hcc, List.length_append, List.length_take, hptl, hal]; omega
    · simp only [hcc, List.length_take, hchil]; omega
  · exact vs_defer hv (by omega) hzeta hal har (by omega) hchi hrcsl hrcs hsll hsr

end
end LeanVM.Guest.B1.VerifySub
