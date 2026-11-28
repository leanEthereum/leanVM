/-
  LeanVM.Guest.B1.VsC.CstOk

  `check_stack_terminal`'s statements before its assertion hold under what its callees give, and
  its assertion holds where the native terminal check does.
-/

module

public import LeanVM.Guest.B1.VsC.CstAtoms
public import LeanVM.Guest.B1.VsC.CstVal
public import LeanVM.Guest.B1.VsC.CertifyW
public import LeanVM.Guest.B1.VsC.RsRunA
public import LeanVM.Guest.B1.VsC.RingRowsA

/-!
# `check_stack_terminal`'s statements

`CstHyp.allOk`: on a memory where `CstHyp` holds, with `q_keccak`'s ring row the last of
`rs_eq_run`'s rows (`RsOut`) and each `ring_cols` return its table's sum (`rcSum`), every statement
before the final assertion holds under `CstC`: the atoms by `CstHyp.holds`, the dispatch at arm
`stackLog - 16` on the selectors' words, `rs_eq_run` on the row, `ring_rows` on the rows in
`rchi`, each `ring_cols` on a row of `rchi` and the scales and masks in `rq`, `pmask`, each
`eq_prefix_chain` on its chain's own words. `CstHyp.assert`: then `cst_value` and the native check
give the assertion.
-/

namespace LeanVM.Guest.B1.VsC

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest LeanVM.Guest.B1
open LeanVM.Guest.Memory LeanVM.Guest.Complete LeanVM.Guest.B1.Stack LeanVM.Guest.B1.Fwd LeanVM.Guest.B1.Link
open LeanVM.Guest.B1.Whir LeanVM.Guest.Value LeanVM.Guest.B1.VerifySub LeanVM.Protocol LeanVM.Protocol.Verifier

@[expose] public section

/-! ## The callees' words -/

/-- Row `h` of `rchi`: the table's coefficients times the products over the row point's first `h`. -/
def rcRow (cs chi x : List E) (h : ℕ) : List E := (List.range 64).map (rgRow cs chi ((padX1 x).take chi.length) h)

/-- The scales `ring_cols` reads from pointer `q0`. -/
def rcScl (rho : E) (qPoint : List E) (q0 nt : ℕ) : List E := ((cstRqW rho qPoint).drop q0).take nt

/-- The masks `ring_cols` reads from pointer `q0`. -/
def rcMsk (layout : Layout) (x : List E) (q0 nt : ℕ) : List E := ((cstMaskW layout x).drop q0).take nt

/-- **`ring_cols`' return on table `t`**, its pointers from `q0`, `nt` of them. -/
def rcSum (layout : Layout) (chi x f g qPoint : List E) (rho : E) (t q0 nt : ℕ) : E :=
  ∑ q ∈ Finset.range nt, (rcMsk layout x q0 nt).getD q 0 *
    frobSum (rcRow (ringCoefficients f g) chi x (hgt layout t)) ((rcScl rho qPoint q0 nt).getD q 0)

/-- The tables' `ring_cols` calls: table, first pointer, pointers, return value. -/
def rcTab : List (ℕ × ℕ × ℕ × ℕ) :=
  [(0, 0, 5, 471), (1, 5, 5, 488), (2, 10, 3, 504), (3, 13, 5, 522), (4, 18, 5, 540), (5, 23, 10, 569)]

/-- Atoms whose equations give the calls' arguments. -/
def cstNeed : List Atom :=
  [.const (.n 41) (word 8198521646651277316 0), .mul (.n 42) (.n 4) (.n 41), .const (.n 55) (word 549755813888 0),
    .mul (.n 56) (.n 10) (.n 55), .const (.n 57) (word 64 0), .mul (.n 58) (.n 51) (.n 57),
    .const (.n 572) (word 1 0), .const (.n 609) (word 1 0), .const (.n 612) (word 1 0), .const (.n 613) (word 64 0),
    .mul (.n 614) (.n 51) (.n 613), .const (.n 615) (word 1 0), .const (.n 616) (word 1 0)]

set_option maxRecDepth 100000 in
theorem cstNeed_ok : cstNeed.all (fun a => decide (a ∈ cstAtomsB)) = true := by decide +kernel

theorem readsAt_take' {rd : Reader} {p : E} {l : List E} (h : ReadsAt rd p l) (n : ℕ) : ReadsAt rd p (l.take n) :=
  fun k hk => by
    have hk' : k < l.length := by rw [List.length_take] at hk; omega
    rw [List.getElem_take]; exact h k hk'

theorem readsAt_dropTake {rd : Reader} {p : E} {l : List E} (h : ReadsAt rd p l) {q0 nt : ℕ} (hle : q0 + nt ≤ l.length) :
    ReadsAt rd (p * gen ^ q0) ((l.drop q0).take nt) := fun k hk => by
  have hk' : k < nt := by rw [List.length_take, List.length_drop] at hk; omega
  rw [loadHolds_mul_gen_pow, List.getElem_take, List.getElem_drop]
  exact h (q0 + k) (by omega)

theorem memRest_ring {s : Stmt} (h : s ∈ cstRing) : s ∈ cstRest := by
  unfold cstRest
  exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ h)))

/-- The relation that always holds. -/
def trivC : CallRel := fun _ _ _ => True

theorem allOk_of_aoc {C : CallRel} {rd : Reader} {σ : Val} {ss : List Stmt} (haoc : ∀ s ∈ ss, atomOrCall s = true)
    (hat : ∀ a, Stmt.atom a ∈ ss → a.Holds rd σ)
    (hc : ∀ f args rets, Stmt.call f args rets ∈ ss → C f (args.map σ) (rets.map σ)) : AllOk C rd σ ss := by
  intro s hs
  cases s with
  | atom a => exact hat a hs
  | call f args rets => exact hc f args rets hs
  | _ => exact absurd (haoc _ hs) (by simp [atomOrCall])

/-- A later table's `ring_cols` arguments. -/
theorem tab_args {C : CallRel} {rd : Reader} {σ : Val} {v0 q0 kb rq pm acc : ℕ} {ks : List ℕ} {W : E}
    {name : String} (hA : AllOk C rd σ (cstTab v0 q0 ks kb W rq pm acc name)) :
    σ (.n (v0 + masksVals ks + 6)) = σ (.n 31) * σ (.n kb) ^ 64 ∧
      σ (.n (v0 + masksVals ks + 8)) = σ (.n rq) * W ∧ σ (.n (v0 + masksVals ks + 10)) = σ (.n pm) * W := by
  unfold cstTab at hA
  simp only [allOk_append, allOk_cons, allOk_nil, and_true] at hA
  obtain ⟨⟨-, hs⟩, h6, h7, h8, h9, h10, -, -⟩ := hA
  simp only [StmtOk, Atom.Holds] at h6 h7 h8 h9 h10
  rw [h7] at h8
  rw [h9] at h10
  exact ⟨by rw [h6, sq_facts hs], h8, h10⟩

/-- Table `0`'s `ring_cols` row. -/
theorem tab0_args {C : CallRel} {rd : Reader} {σ : Val} (hA : AllOk C rd σ cstTab0) :
    σ (.n 470) = σ (.n 31) * σ (.n 46) ^ 64 := by
  unfold cstTab0 at hA
  simp only [allOk_append, allOk_cons, allOk_nil, and_true] at hA
  obtain ⟨⟨-, hs⟩, h6, -⟩ := hA
  simp only [StmtOk, Atom.Holds] at h6
  have h5 : σ (.n 469) = σ (.n 46) ^ 64 := sq_facts hs
  rw [h6, h5]

/-! ## `CstC` per callee -/

section
variable {rd : Reader} {layout : Layout} {x : List E}

theorem cstArms_ne : ∀ f ∈ cstArms, f ≠ "rs_eq_run" ∧ f ≠ "ring_rows" ∧ f ≠ "eq_prefix_chain" ∧
    ∀ p ∈ ringColsNames, f ≠ p.2 := by decide

theorem cstC_arm {f : String} (hf : f ∈ cstArms) {args : List E} {sel : E}
    (h : ∀ b < 52, LoadHolds rd sel b (selW layout x b)) : CstC rd layout x f args [sel] := by
  obtain ⟨h1, h2, h3, h4⟩ := cstArms_ne f hf
  exact ⟨fun _ => ⟨sel, rfl, h⟩, fun he => absurd he h1, fun he => absurd he h2, fun p hp he => absurd he (h4 p hp),
    fun he => absurd he h3⟩

theorem cstC_rs {args rets : List E} (h : RsRunC rd args rets) : CstC rd layout x "rs_eq_run" args rets := by
  refine ⟨fun hm => absurd hm (by decide), fun _ => h, fun he => absurd he (by decide), fun p hp he => ?_,
    fun he => absurd he (by decide)⟩
  simp only [ringColsNames, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl <;> exact absurd he (by decide)

theorem cstC_rows {args rets : List E} (h : MeaningRingRows rd args rets) : CstC rd layout x "ring_rows" args rets := by
  refine ⟨fun hm => absurd hm (by decide), fun he => absurd he (by decide), fun _ => h, fun p hp he => ?_,
    fun he => absurd he (by decide)⟩
  simp only [ringColsNames, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl <;> exact absurd he (by decide)

theorem cstC_epc {args rets : List E} (h : EpcC rd args rets) : CstC rd layout x "eq_prefix_chain" args rets := by
  refine ⟨fun hm => absurd hm (by decide), fun he => absurd he (by decide), fun he => absurd he (by decide),
    fun p hp he => ?_, fun _ => h⟩
  simp only [ringColsNames, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl <;> exact absurd he (by decide)

theorem ringColsNames_inj : ∀ p ∈ ringColsNames, ∀ q ∈ ringColsNames, p.2 = q.2 → p = q := by decide

theorem cstC_cols {n : ℕ} {name : String} (hp : (n, name) ∈ ringColsNames) {args rets : List E}
    (h : MeaningRingCols n rd args rets) : CstC rd layout x name args rets := by
  have hn : name ∉ cstArms ∧ name ≠ "rs_eq_run" ∧ name ≠ "ring_rows" ∧ name ≠ "eq_prefix_chain" := by
    have : ∀ p ∈ ringColsNames, p.2 ∉ cstArms ∧ p.2 ≠ "rs_eq_run" ∧ p.2 ≠ "ring_rows" ∧ p.2 ≠ "eq_prefix_chain" := by
      decide
    exact this _ hp
  refine ⟨fun hm => absurd hm hn.1, fun he => absurd he hn.2.1, fun he => absurd he hn.2.2.1, fun p hp' he => ?_,
    fun he => absurd he hn.2.2.2⟩
  rw [ringColsNames_inj p hp' (n, name) hp he.symm]
  exact h

/-- A prefix chain from `1` of the words `as` against the point, its `len + 1` entries in memory. -/
theorem epc_ok {chain a b1 : E} {as : List E} {len : ℕ} (hlen : len ≤ as.length) (hn : len ≤ 30)
    (hx : x.length ≤ 40) (hch : ReadsAt rd chain (chainW as x len)) (ha : ReadsAt rd a as)
    (hb : ReadsAt rd b1 (padX1 x)) : EpcC rd [chain, 1, a, b1, gen ^ len] [] := by
  refine ⟨rfl, len, by omega, rfl, as.take len, (padX1 x).take len, by simp; omega,
    by rw [List.length_take, padX1_length x hx]; omega, readsAt_take' ha len, readsAt_take' hb len, fun j hj => ?_⟩
  have hv := hch j (by rw [chainW, List.length_map, List.length_range]; omega)
  have e : (chainW as x len)[j]'(by rw [chainW, List.length_map, List.length_range]; omega) =
      prefixProd 1 (as.take len) ((padX1 x).take len) j := by
    simp only [chainW, List.getElem_map, List.getElem_range]
    unfold prefixProd
    rw [List.take_take, List.take_take, min_eq_left hj]
  rw [e] at hv
  exact hv

end

/-! ## On a memory -/

section
variable {rd : Reader} {w : ℕ → E} {σ : Val} {layout : Layout} {link : LinkEnd}
  {chi r qPoint kOut kIn f g x z : List E} {rho lam rm : E} {outputs : List ColumnClaim} {c csel crow fp : ℕ}
variable (h : CstHyp rd w σ layout link chi r qPoint kOut kIn f g x z rho lam rm outputs c csel crow fp)
include h

theorem CstHyp.w0 : ReadsAt rd (ptrAtV (cstBase chi.length c 0))
    (rgRows (ringCoefficients f g) chi ((padX1 x).take chi.length) chi.length) :=
  h.words (cstBase chi.length c 0, rgRows (ringCoefficients f g) chi ((padX1 x).take chi.length) chi.length)
    (by simp only [cstWords]; exact List.mem_cons_self)

theorem CstHyp.need : ∀ a ∈ cstNeed, a.Holds rd σ := fun a ha =>
  h.holds a (by simpa using List.all_eq_true.mp cstNeed_ok a ha)

/-- A table's `ring_cols` on a row of `rchi` and the scales and masks from pointer `q0`. -/
theorem CstHyp.rcOk {t q0 nt : ℕ} (ht : t < 6) (hq : q0 + nt ≤ 33) {row scl msk : E}
    (hrow : row = ptrAtV (cstBase chi.length c 0) * gen ^ (64 * hgt layout t))
    (hscl : scl = ptrAtV (cstBase chi.length c 2) * gen ^ q0) (hmsk : msk = ptrAtV (cstBase chi.length c 1) * gen ^ q0) :
    MeaningRingCols nt rd [row, scl, msk] [rcSum layout chi x f g qPoint rho t q0 nt] := by
  obtain ⟨-, -, -, -, -, -, -, hheights, -⟩ := h.ctx
  refine ⟨rcRow (ringCoefficients f g) chi x (hgt layout t), rcScl rho qPoint q0 nt, rcMsk layout x q0 nt,
    by simp [rcRow, kBits], by simp [rcScl, cstRqW]; omega, by simp [rcMsk, cstMaskW]; omega, ?_,
    ?_, ?_, rfl⟩
  · rw [hrow]
    intro k hk
    have hk' : k < 64 := by simpa [rcRow] using hk
    rw [loadHolds_mul_gen_pow]
    simp only [rcRow, List.getElem_map, List.getElem_range]
    exact rgRows_at h.w0 (hheights t (by simpa [nTables] using ht)) hk'
  · rw [hscl]; exact readsAt_dropTake h.w2 (by simp [cstRqW]; omega)
  · rw [hmsk]; exact readsAt_dropTake h.w1 (by simp [cstMaskW]; omega)

set_option maxHeartbeats 2000000 in
/-- **Every statement before the assertion holds under what the callees give.** -/
theorem CstHyp.allOk
    (hrow : RsOut (ringCoefficients f g) kIn ((padX1 x).take (hgt layout 5 + 6)) (ptrAtV crow) rd)
    (hrc : ∀ p ∈ rcTab, σ (.n p.2.2.2) = rcSum layout chi x f g qPoint rho p.1 p.2.1 p.2.2.1) :
    AllOk (CstC rd layout x) rd σ cstBodyB ∧ AllOk (CstC rd layout x) rd σ cstTail0 := by
  obtain ⟨⟨bytecode, rows, hbl⟩, hexp, hkb, hplaced, hchiR, hgn, hchi24, hheights, hpieces, hcols, hqlen, heqq,
    hrR, hlmr, hglm, hmp, hgm1, hgm2, hrm, hzv, hkin, hout, hkoutl, hkinl, hf, hg, hct, hrho, hlam, hxl, hpt, hpt1,
    hzl, hoodz⟩ := h.ctx
  have hL := h.hL
  set n := chi.length with hn
  have hn24 : n ≤ 24 := hchi24
  have h5n : hgt layout 5 ≤ n := hheights 5 (by decide)
  have hq6 : hgt layout 5 + 6 ≤ layout.stackLog := by
    have := (block_placed hbl (b := 2) (by decide)).2.2.2
    rwa [(block_placed hbl (b := 2) (by decide)).2.1, (blockKap_eq layout).2.2] at this
  have hlmL : layout.logMemory ≤ layout.stackLog := by
    have := (block_placed hbl (b := 0) (by decide)).2.2.2
    rwa [(block_placed hbl (b := 0) (by decide)).2.1, (blockKap_eq layout).1] at this
  have h16 : 16 ≤ layout.stackLog := by rw [(cs_layout hbl hL).2.1]; exact le_max_left _ _
  have hx40 : x.length ≤ 40 := by omega
  have hko : kOut.length = hgt layout 5 + 6 := by rw [hkoutl]; rfl
  have hkin6 : kIn.length = hgt layout 5 + 6 := by rw [hkinl, hko]
  have hcs : (ringCoefficients f g).length = 64 := ringCoefficients_length f g hf hg
  have hN := h.need
  simp only [cstNeed, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, Atom.Holds, forall_eq] at hN
  obtain ⟨e41, e42, e55, e56, e57, e58, e572, e609, e612, e613, e614, e615, e616⟩ := hN
  have k46 : σ (.n 46) = gen ^ hgt layout 0 := h.kbv 0 (by norm_num)
  have k47 : σ (.n 47) = gen ^ hgt layout 1 := h.kbv 1 (by norm_num)
  have k48 : σ (.n 48) = gen ^ hgt layout 2 := h.kbv 2 (by norm_num)
  have k49 : σ (.n 49) = gen ^ hgt layout 3 := h.kbv 3 (by norm_num)
  have k50 : σ (.n 50) = gen ^ hgt layout 4 := h.kbv 4 (by norm_num)
  have k51 : σ (.n 51) = gen ^ hgt layout 5 := h.kbv 5 (by norm_num)
  have b31 : σ (.n 31) = ptrAtV (cstBase n c 0) := h.buf 0 (by norm_num)
  have b32 : σ (.n 32) = ptrAtV (cstBase n c 1) := h.buf 1 (by norm_num)
  have b33 : σ (.n 33) = ptrAtV (cstBase n c 2) := h.buf 2 (by norm_num)
  have b34 : σ (.n 34) = ptrAtV (cstBase n c 3) := h.buf 3 (by norm_num)
  have b35 : σ (.n 35) = ptrAtV (cstBase n c 4) := h.buf 4 (by norm_num)
  have b36 : σ (.n 36) = ptrAtV (cstBase n c 5) := h.buf 5 (by norm_num)
  have b37 : σ (.n 37) = ptrAtV (cstBase n c 6) := h.buf 6 (by norm_num)
  have b38 : σ (.n 38) = ptrAtV (cstBase n c 7) := h.buf 7 (by norm_num)
  have b40 : σ (.n 40) = ptrAtV (cstBase n c 9) := h.buf 9 (by norm_num)
  obtain ⟨hok0, hok1⟩ : cstH0.all atomOrCall = true ∧ cstRest.all atomOrCall = true := by
    have := cstNodeOk_ok
    simp only [cstNodeOk, Bool.and_eq_true] at this
    obtain ⟨⟨⟨⟨⟨⟨h1, h2⟩, -⟩, -⟩, -⟩, -⟩, -⟩ := this
    exact ⟨h1, h2⟩
  -- the tables' arguments, from the ring segment's atoms
  have hRingT : AllOk trivC rd σ cstRing :=
    allOk_of_aoc (fun s hs => List.all_eq_true.mp hok1 s (memRest_ring hs))
      (fun a ha => h.holds a (mem_atomsB (memB_ring ha))) (fun _ _ _ _ => trivial)
  obtain ⟨-, -, -, ht0, ht1, ht2, ht3, ht4, ht5, -⟩ := ring_facts hRingT
  have a0 : σ (.n 470) = σ (.n 31) * σ (.n 46) ^ 64 := tab0_args ht0
  have a1 : σ (.n 483) = σ (.n 31) * σ (.n 47) ^ 64 ∧ σ (.n 485) = σ (.n 33) * word 32 0 ∧
      σ (.n 487) = σ (.n 32) * word 32 0 := tab_args ht1
  have a2 : σ (.n 499) = σ (.n 31) * σ (.n 48) ^ 64 ∧ σ (.n 501) = σ (.n 485) * word 32 0 ∧
      σ (.n 503) = σ (.n 487) * word 32 0 := tab_args ht2
  have a3 : σ (.n 517) = σ (.n 31) * σ (.n 49) ^ 64 ∧ σ (.n 519) = σ (.n 33) * word 8192 0 ∧
      σ (.n 521) = σ (.n 32) * word 8192 0 := tab_args ht3
  have a4 : σ (.n 535) = σ (.n 31) * σ (.n 50) ^ 64 ∧ σ (.n 537) = σ (.n 519) * word 32 0 ∧
      σ (.n 539) = σ (.n 521) * word 32 0 := tab_args ht4
  have a5 : σ (.n 564) = σ (.n 31) * σ (.n 51) ^ 64 ∧ σ (.n 566) = σ (.n 537) * word 32 0 ∧
      σ (.n 568) = σ (.n 539) * word 32 0 := tab_args ht5
  have rowE : ∀ t (kb : ℕ), σ (.n kb) = gen ^ hgt layout t →
      σ (.n 31) * σ (.n kb) ^ 64 = ptrAtV (cstBase n c 0) * gen ^ (64 * hgt layout t) := fun t kb hk => by
    rw [hk, b31, ← pow_mul, Nat.mul_comm]
  have rq : ∀ q0 : ℕ, σ (.n 33) * gen ^ q0 = ptrAtV (cstBase n c 2) * gen ^ q0 := fun q0 => by rw [b33]
  have pm : ∀ q0 : ℕ, σ (.n 32) * gen ^ q0 = ptrAtV (cstBase n c 1) * gen ^ q0 := fun q0 => by rw [b32]
  have rcs : ∀ t q0 nt ret, (t, q0, nt, ret) ∈ rcTab → σ (.n ret) = rcSum layout chi x f g qPoint rho t q0 nt :=
    fun t q0 nt ret hm => hrc _ hm
  have w5 : word 32 0 = gen ^ 5 := word_g5
  have w13 : word 8192 0 = gen ^ 13 := word_g13
  -- each statement of the body but the dispatch
  have stmt : ∀ s, (s ∈ cstH0 ∨ s ∈ cstRest) → s ∈ cstBodyB → StmtOk (CstC rd layout x) rd σ s := by
    intro s hs hsB
    have haoc : atomOrCall s = true := by
      rcases hs with hs | hs
      · exact List.all_eq_true.mp hok0 s hs
      · exact List.all_eq_true.mp hok1 s hs
    cases s with
    | atom a => exact h.holds a (mem_atomsB (List.mem_append_left _ hsB))
    | call fn args rets =>
      have hcall : (⟨fn, args, rets, true⟩ : Call) ∈ cstRestCalls := by
        rcases hs with hs | hs
        · have hm : (⟨fn, args, rets, true⟩ : Call) ∈ callsOfB cstH0 := List.mem_filterMap.mpr ⟨_, hs, rfl⟩
          rw [cstH0_calls] at hm
          exact absurd hm List.not_mem_nil
        · rw [← cstRest_calls]
          exact List.mem_filterMap.mpr ⟨_, hs, rfl⟩
      simp only [cstRestCalls, List.mem_cons, List.not_mem_nil, or_false, Call.mk.injEq, and_true] at hcall
      simp only [StmtOk]
      rcases hcall with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ |
        ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ |
        ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;> simp only [List.map_cons, List.map_nil]
      · -- `rs_eq_run`
        refine cstC_rs ⟨hgt layout 5 + 6, by omega, by rw [e58, e57, k51, word_g6, ← pow_add], kIn,
          (padX1 x).take (hgt layout 5 + 6), ringCoefficients f g, hkin6, by simp; omega, hcs, ?_,
          readsAt_take' hpt1 _, hct, σ (.n 59), rfl, fun k hk => h.row ▸ hrow k hk⟩
        rw [e56, e55, word_g39]
        exact hkin
      · -- `ring_rows`
        refine cstC_rows ⟨n, by omega, hgn, chi, (padX1 x).take n, ringCoefficients f g, rfl, by simp; omega, hcs,
          hchiR, readsAt_take' hpt1 _, hct, fun k hk => ?_, fun m _ hm k hk => ?_, rfl⟩
        · rw [b31]
          have hk' : k < 64 := by rw [hcs] at hk; exact hk
          have hv := rgRows_at h.w0 (m := 0) (Nat.zero_le _) hk'
          simp only [rgRow, ringRow, List.take_zero, List.zipWith_nil_left, List.foldl_nil, Nat.mul_zero,
            Nat.zero_add] at hv
          rwa [List.getD_eq_getElem _ _ hk] at hv
        · rw [b31]; exact rgRows_at h.w0 hm hk
      · rw [rcs 0 0 5 471 (by simp [rcTab])]
        exact cstC_cols (by decide) (h.rcOk (by norm_num) (by norm_num) (by rw [a0, rowE 0 46 k46])
          (by rw [b33, pow_zero, mul_one]) (by rw [b32, pow_zero, mul_one]))
      · rw [rcs 1 5 5 488 (by simp [rcTab])]
        exact cstC_cols (by decide) (h.rcOk (by norm_num) (by norm_num) (by rw [a1.1, rowE 1 47 k47])
          (by rw [a1.2.1, w5, b33]) (by rw [a1.2.2, w5, b32]))
      · rw [rcs 2 10 3 504 (by simp [rcTab])]
        exact cstC_cols (by decide) (h.rcOk (by norm_num) (by norm_num) (by rw [a2.1, rowE 2 48 k48])
          (by rw [a2.2.1, a1.2.1, w5, b33, mul_assoc, ← pow_add])
          (by rw [a2.2.2, a1.2.2, w5, b32, mul_assoc, ← pow_add]))
      · rw [rcs 3 13 5 522 (by simp [rcTab])]
        exact cstC_cols (by decide) (h.rcOk (by norm_num) (by norm_num) (by rw [a3.1, rowE 3 49 k49])
          (by rw [a3.2.1, w13, b33]) (by rw [a3.2.2, w13, b32]))
      · rw [rcs 4 18 5 540 (by simp [rcTab])]
        exact cstC_cols (by decide) (h.rcOk (by norm_num) (by norm_num) (by rw [a4.1, rowE 4 50 k50])
          (by rw [a4.2.1, a3.2.1, w5, w13, b33, mul_assoc, ← pow_add])
          (by rw [a4.2.2, a3.2.2, w5, w13, b32, mul_assoc, ← pow_add]))
      · rw [rcs 5 23 10 569 (by simp [rcTab])]
        exact cstC_cols (by decide) (h.rcOk (by norm_num) (by norm_num) (by rw [a5.1, rowE 5 51 k51])
          (by rw [a5.2.1, a4.2.1, a3.2.1, w5, w13, b33, mul_assoc, mul_assoc, ← pow_add, ← pow_add])
          (by rw [a5.2.2, a4.2.2, a3.2.2, w5, w13, b32, mul_assoc, mul_assoc, ← pow_add, ← pow_add]))
      · rw [b36, e572, word_one, hglm]
        exact cstC_epc (epc_ok hlmr (by omega) hx40 h.w5 hrR hpt1)
      · rw [b37, b38, e609, word_one, hglm]
        exact cstC_epc (epc_ok (by simp [piW]; omega) (by omega) hx40 h.w6 h.w7 hpt1)
      · rw [b35, e612, word_one, e614, e613, k51, word_g6, ← pow_add, ← hko]
        exact cstC_epc (epc_ok le_rfl (by omega) hx40 h.w4 hzv hpt1)
      · rw [b40, e615, word_one, hplaced.1, ← hzl]
        exact cstC_epc (epc_ok le_rfl (by omega) hx40 h.w9 hoodz hpt1)
      · rw [b34, e616, word_one, hgn]
        exact cstC_epc (epc_ok le_rfl (by omega) hx40 h.w3 hchiR hpt1)
    | _ => simp [atomOrCall] at haoc
  refine ⟨fun s hs => ?_, allOk_of_aoc (fun s hs => ?_)
    (fun a ha => h.holds a (mem_atomsB (List.mem_append_right _ ha))) (fun _ _ _ hc => ?_)⟩
  · have hA : s ∈ cstH0 ∨ s = .dispatch (.n 42) cstArms cstArgsV [.n 43] ∨ s ∈ cstRest := by
      have : s ∈ cstBodyA := by rw [cstBodyA_eq]; exact List.mem_append_left _ (List.mem_append_left _ hs)
      rw [cstBodyA_split] at this
      simpa using this
    rcases hA with hs0 | rfl | hs1
    · exact stmt s (Or.inl hs0) hs
    · simp only [StmtOk, List.map_cons, List.map_nil]
      refine ⟨layout.stackLog - 16, by simp [cstArms]; omega, ?_, ?_⟩
      · rw [e42, e41, hplaced.1, ← gen_pow_eq_ofK]
        calc gen ^ layout.stackLog * word 8198521646651277316 0 =
            gen ^ (layout.stackLog - 16) * (gen ^ 16 * word 8198521646651277316 0) := by
              rw [← mul_assoc, ← pow_add, Nat.sub_add_cancel h16]
          _ = gen ^ (layout.stackLog - 16) := by rw [gen16_inv, mul_one]
      · exact cstC_arm (List.getElem_mem _) fun b hb => h.sel ▸ h.selOut b hb
    · exact stmt s (Or.inr hs1) hs
  · simp only [cstTail0, List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
  · simp [cstTail0] at hc

/-- **The assertion holds** where the native terminal check does. -/
theorem CstHyp.assert
    (hrow : RsOut (ringCoefficients f g) kIn ((padX1 x).take (hgt layout 5 + 6)) (ptrAtV crow) rd)
    (hrc : ∀ p ∈ rcTab, σ (.n p.2.2.2) = rcSum layout chi x f g qPoint rho p.1 p.2.1 p.2.2.1)
    {keccakSlices : List E} {oodValue v0 v1 : E} {claims : List StackClaim}
    (hcl : stackedClaims layout link (publicClaimsPure layout rm v0 v1) outputs kIn keccakSlices f g rho
        (fun y ↦ eqEval z y, oodValue) = some claims)
    (hnat : (σ (.n 19) + stackedBasis claims lam x) * σ (.n 20) = σ (.n 21)) :
    (Atom.assertEq (.n 924) (.n 21)).Holds rd σ := by
  obtain ⟨hB, hT⟩ := h.allOk hrow hrc
  obtain ⟨claims', hcl', hv⟩ := cst_value (keccakSlices := keccakSlices) (oodValue := oodValue) (v0 := v0) (v1 := v1)
    hB hT h.ctx
  rw [hcl] at hcl'
  cases hcl'
  show σ (.n 924) + σ (.n 21) = 0
  rw [hv, hnat]
  exact add_self_E _

end

end
end LeanVM.Guest.B1.VsC
