/-
  LeanVM.Guest.B1.VsC.CstLoads

  `check_stack_terminal`'s loads on an honest memory: each reads a defined word, where.
-/

module

public import LeanVM.Guest.B1.VsC.CstChecks
public import LeanVM.Guest.B1.VsC.CstWordsIn
public import LeanVM.Guest.B1.VsC.Vsc8CalleesA

/-!
# `check_stack_terminal`'s loads

`CstHyp`: a valuation satisfying the body's equations (`Good`), its buffers at the cursor `c`, the
selectors at `csel` and `q_keccak`'s ring row at `crow` (its callees' returns), on a memory where
`StackCtxAt` holds of its parameters, holding its own words (`cstWords`) and the selectors' and
the row's words, the caller's arrays below the frame.

`cst_load`: every load before the final assertion reads a word of its buffers, of the caller's
arrays, of the selectors or of the row (`CstLoc`); every load but `eqtree`'s stores holds, by the
kind the kernel gave it (`cstAtomsOk`): a fresh load reads a defined word, a store's word is its
buffer's honest word.
-/

namespace LeanVM.Guest.B1.VsC

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest LeanVM.Guest.B1
open LeanVM.Guest.Memory LeanVM.Guest.Complete LeanVM.Guest.B1.Stack LeanVM.Guest.B1.Fwd LeanVM.Guest.B1.Link
open LeanVM.Guest.B1.Whir LeanVM.Guest.Value LeanVM.Protocol LeanVM.Protocol.Verifier

@[expose] public section

/-- Where `check_stack_terminal`'s loads read: its buffers from `c`, the caller's arrays `arrs`, the
selectors at `csel`, `q_keccak`'s ring row at `crow`. -/
def CstLoc (n c csel crow : ℕ) (arrs : List (E × ℕ)) (i : ℕ) : Prop :=
  (c ≤ i ∧ i < c + (64 * (n + 1) + 422)) ∨ ptrRegion arrs i ∨ (csel ≤ i ∧ i < csel + 52) ∨
    (crow ≤ i ∧ i < crow + 64)

/-- **What `check_stack_terminal`'s loads need on a memory.** -/
structure CstHyp (rd : Reader) (w : ℕ → E) (σ : Val) (layout : Layout) (link : LinkEnd)
    (chi r qPoint kOut kIn f g x z : List E) (rho lam rm : E) (outputs : List ColumnClaim)
    (c csel crow fp : ℕ) : Prop where
  good : ∀ a, Stmt.atom a ∈ cstBody → Good rd cstS w σ a
  buf : ∀ i < 10, σ (.n (31 + i)) = ptrAtV (cstBase chi.length c i)
  sel : σ (.n 43) = ptrAtV csel
  row : σ (.n 59) = ptrAtV crow
  ctx : StackCtxAt rd (cstValArgs σ) layout link chi r qPoint kOut kIn f g x z rho lam rm outputs
  hL : layout.stackLog ≤ 30
  below : PtrsBelow (cstArrays (cstValArgs σ) chi r kOut kIn f g z) fp
  words : HoldsWords rd (cstWords c layout chi r qPoint kOut x z f g rho rm)
  selOut : ∀ b < 52, LoadHolds rd (ptrAtV csel) b (selW layout x b)
  rowOut : ∀ j < 64, ∃ v, LoadHolds rd (ptrAtV crow) j v

/-! ## Addresses -/

theorem addr_mul_gen (p : E) (e o : ℕ) :
    (p * gen ^ e).limb 0 * addressOfIndex o = p.limb 0 * addressOfIndex (e + o) := by
  rw [gen_pow_eq_ofK, limb0_mul_ofK, mul_assoc]
  simp only [Parameters.addressOfIndex, ← pow_add]

theorem addr_ptr (b o : ℕ) : (ptrAtV b).limb 0 * addressOfIndex o = addressOfIndex (b + o) := by
  simp [ptrAtV, addressOfIndex, pow_add]

theorem region_of {arrs : List (E × ℕ)} {fp : ℕ} (hb : PtrsBelow arrs fp) {q : E × ℕ} (hq : q ∈ arrs) {t : ℕ}
    (ht : t < q.2) : ∃ i, q.1.limb 0 * addressOfIndex t = addressOfIndex i ∧ ptrRegion arrs i := by
  obtain ⟨i, -, hi⟩ := hb q hq t ht
  exact ⟨i, hi, q, hq, t, ht, hi⟩

/-! ## Membership -/

theorem memB_head {s : Stmt} (h : s ∈ cstHead) : s ∈ cstBodyB ++ cstTail0 := by
  simp only [cstBodyB, List.mem_append]; tauto

theorem memB_ring {s : Stmt} (h : s ∈ cstRing) : s ∈ cstBodyB ++ cstTail0 := by
  simp only [cstBodyB, List.mem_append]; tauto

theorem mem_atomsB {a : Atom} (h : Stmt.atom a ∈ cstBodyB ++ cstTail0) : a ∈ cstAtomsB := mem_atomsOf' h

theorem cst_atomB {a : Atom} (ha : a ∈ cstAtomsB) : cstAtomB cstS cstAtomsB a = true := by
  have := cstAtomsOk_ok
  simp only [cstAtomsOk, Bool.and_eq_true, List.all_eq_true] at this
  exact this.1 a ha

/-- A store's pointer is one of the four buffers stored into. -/
theorem cst_storePtr {d p : V} {off : ℕ} (ha : Atom.load d p off ∈ cstAtomsB) (hS : Atom.load d p off ∈ cstS) :
    p = .n 33 ∨ p = .n 32 ∨ p = .n 38 ∨ p = .n 39 := by
  by_contra hne
  simp only [not_or] at hne
  obtain ⟨h1, h2, h3, h4⟩ := hne
  have h := cst_atomB ha
  simp [cstAtomB, hS, h1, h2, h3, h4] at h

theorem cst_fresh_of {d : V} {m off : ℕ} (ha : Atom.load d (.n m) off ∈ cstAtomsB) (hm : m ≠ 33 ∧ m ≠ 32 ∧ m ≠ 38 ∧ m ≠ 39) :
    Atom.load d (.n m) off ∉ cstS := fun hS => by
  rcases cst_storePtr ha hS with h | h | h | h <;> simp only [V.mk.injEq] at h <;> omega

theorem eqStores_off : (eqStoresAt (.n 39) 0 255 6).all
    (fun a => match a with | .load _ p off => decide (p = .n 39) && decide (off < 126) | _ => false) = true := by
  decide +kernel

theorem eqStore_off {d p : V} {off : ℕ} (h : Atom.load d p off ∈ eqStoresAt (.n 39) 0 255 6) : p = .n 39 ∧ off < 126 := by
  have := List.all_eq_true.mp eqStores_off _ h
  simpa using this

/-! ## The memory's words -/

section
variable {rd : Reader} {w : ℕ → E} {σ : Val} {layout : Layout} {link : LinkEnd}
  {chi r qPoint kOut kIn f g x z : List E} {rho lam rm : E} {outputs : List ColumnClaim} {c csel crow fp : ℕ}

theorem CstHyp.gB (h : CstHyp rd w σ layout link chi r qPoint kOut kIn f g x z rho lam rm outputs c csel crow fp)
    {a : Atom} (ha : a ∈ cstAtomsB) : Good rd cstS w σ a :=
  h.good a (mem_cstBody_of_B (mem_of_mem_atomsOf ha))

section words
variable (h : CstHyp rd w σ layout link chi r qPoint kOut kIn f g x z rho lam rm outputs c csel crow fp)
include h

theorem CstHyp.w1 : ReadsAt rd (ptrAtV (cstBase chi.length c 1)) (cstMaskW layout x) :=
  h.words (cstBase chi.length c 1, cstMaskW layout x) (by simp only [cstWords]; exact List.mem_cons_of_mem _ List.mem_cons_self)

theorem CstHyp.w2 : ReadsAt rd (ptrAtV (cstBase chi.length c 2)) (cstRqW rho qPoint) :=
  h.words (cstBase chi.length c 2, cstRqW rho qPoint) (by simp only [cstWords]; exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))

theorem CstHyp.w3 : ReadsAt rd (ptrAtV (cstBase chi.length c 3)) (chainW chi x chi.length) :=
  h.words (cstBase chi.length c 3, chainW chi x chi.length) (by simp only [cstWords]; exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _
    (List.mem_cons_of_mem _ List.mem_cons_self)))

theorem CstHyp.w4 : ReadsAt rd (ptrAtV (cstBase chi.length c 4)) (chainW kOut x kOut.length) :=
  h.words (cstBase chi.length c 4, chainW kOut x kOut.length) (by simp only [cstWords]; exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _
    (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))))

theorem CstHyp.w5 : ReadsAt rd (ptrAtV (cstBase chi.length c 5)) (chainW r x layout.logMemory) :=
  h.words (cstBase chi.length c 5, chainW r x layout.logMemory) (by simp only [cstWords]; exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _
    (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)))))

theorem CstHyp.w6 : ReadsAt rd (ptrAtV (cstBase chi.length c 6)) (chainW (piW rm) x layout.logMemory) :=
  h.words (cstBase chi.length c 6, chainW (piW rm) x layout.logMemory) (by simp only [cstWords]; exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _
    (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
      List.mem_cons_self))))))

theorem CstHyp.w7 : ReadsAt rd (ptrAtV (cstBase chi.length c 7)) (piW rm) :=
  h.words (cstBase chi.length c 7, piW rm) (by simp only [cstWords]; exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _
    (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
      (List.mem_cons_of_mem _ List.mem_cons_self)))))))

theorem CstHyp.w8 : ReadsAt rd (ptrAtV (cstBase chi.length c 8)) (tqW layout x) :=
  h.words (cstBase chi.length c 8, tqW layout x) (by simp only [cstWords]; exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _
    (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
      (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))))))))

theorem CstHyp.w9 : ReadsAt rd (ptrAtV (cstBase chi.length c 9)) (chainW z x z.length) :=
  h.words (cstBase chi.length c 9, chainW z x z.length) (by simp only [cstWords]; exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _
    (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
      (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)))))))))

/-- The tables' heights `kappa_base` gives. -/
theorem CstHyp.kbv : ∀ t < 6, σ (.n (46 + t)) = gen ^ hgt layout t := by
  obtain ⟨-, -, hkb, -⟩ := h.ctx
  intro t ht
  have hm : Atom.load (.n (46 + t)) (.n 1) (2 + t) ∈ cstAtomsB := by
    apply mem_atomsB; apply memB_head; interval_cases t <;> simp [cstHead]
  have hS := cst_fresh_of hm (by omega)
  have hv := kappaSources_get hkb (2 + t) (by omega)
  rw [good_load_eq hv (h.gB hm) hS]
  have h1 : 2 + t ≠ 1 := by omega
  simp [kvOf, hgt, h1]

/-- The point's slots' pointer. -/
theorem CstHyp.v254 : σ (.n 254) = σ (.n 17) * gen ^ hgt layout 5 := by
  have hm : Atom.mul (.n 254) (.n 17) (.n 51) ∈ cstAtomsB := by
    apply mem_atomsB; apply memB_ring; simp [cstRing]
  rw [good_mul_eq (h.gB hm) (by decide) (by decide)]
  exact congrArg _ (h.kbv 5 (by norm_num))

end words

theorem ptrKinds_lt : ∀ q < 33, ptrKinds.getD q 0 < 116 := by decide

/-- `tq`'s words past the root levels: the slots' weights. -/
theorem tqEntry_kern (layout : Layout) (x : List E) {k : ℕ} (h1 : 52 ≤ k) (h2 : k < 116) :
    tqEntry layout x (k + 10) = kernW layout x (k - 52) := by
  have hlog : Nat.log 2 (k + 10 + 2) = 6 :=
    Nat.log_eq_of_pow_le_of_lt_pow (by norm_num; omega) (by norm_num; omega)
  rw [tqEntry, kernW, hlog, List.take_take, min_self, show k + 10 + 2 - 2 ^ 6 = k - 52 by norm_num]

theorem chainW_get {as x : List E} {n j : ℕ} (hj : j ≤ n) : (chainW as x n).getD j 0 = prefixProd 1 as (padX1 x) j := by
  simp [chainW, List.getD_eq_getElem?_getD, show j < n + 1 by omega]

section load
variable (h : CstHyp rd w σ layout link chi r qPoint kOut kIn f g x z rho lam rm outputs c csel crow fp)
include h

/-- The selector `q_keccak`'s mask scales. -/
theorem CstHyp.v52 : σ (.n 52) = selW layout x 2 := by
  have hm : Atom.load (.n 52) (.n 43) 2 ∈ cstAtomsB := by
    apply mem_atomsB; apply memB_head; simp [cstHead]
  rw [good_load_eq (h.sel ▸ h.selOut 2 (by norm_num)) (h.gB hm) (cst_fresh_of hm (by omega))]

/-- **Every load of `check_stack_terminal` before its assertion reads where it may**, and holds
unless it is one of `eqtree`'s stores. -/
theorem CstHyp.load {d p : V} {off : ℕ} (ha : Atom.load d p off ∈ cstAtomsB) :
    (∃ i, (σ p).limb 0 * addressOfIndex off = addressOfIndex i ∧
        CstLoc chi.length c csel crow (cstArrays (cstValArgs σ) chi r kOut kIn f g z) i) ∧
      (Atom.load d p off ∉ cstS ∨ Atom.load d p off ∉ eqStoresAt (.n 39) 0 255 6 → LoadHolds rd (σ p) off (σ d)) := by
  obtain ⟨⟨bytecode, rows, hbl⟩, hexp, hkb, hplaced, hchiR, hgn, hchi24, hheights, hpieces, hcols, hqlen, heqq,
    hrR, hlmr, hglm, hmp, hgm1, hgm2, hrm, hzv, hkin, hout, hkoutl, hkinl, hf, hg, hct, hrho, hlam, hxl, hpt, hpt1,
    hzl, hoodz⟩ := h.ctx
  set n := chi.length with hn
  set arrs := cstArrays (cstValArgs σ) chi r kOut kIn f g z with harrs
  have hL := h.hL
  have hn24 : n ≤ 24 := hchi24
  have h5n : hgt layout 5 ≤ n := hheights 5 (by decide)
  have hq6 : hgt layout 5 + 6 ≤ layout.stackLog := by
    have := (block_placed hbl (b := 2) (by decide)).2.2.2
    rwa [(block_placed hbl (b := 2) (by decide)).2.1, (blockKap_eq layout).2.2] at this
  have hlmL : layout.logMemory ≤ layout.stackLog := by
    have := (block_placed hbl (b := 0) (by decide)).2.2.2
    rwa [(block_placed hbl (b := 0) (by decide)).2.1, (blockKap_eq layout).1] at this
  have hko : kOut.length = hgt layout 5 + 6 := by rw [hkoutl]; rfl
  have own : ∀ i o, i < 10 → o < (cstSizes n).getD i 0 → ∃ i', (ptrAtV (cstBase n c i)).limb 0 * addressOfIndex o =
      addressOfIndex i' ∧ CstLoc n c csel crow arrs i' := by
    intro i o hi ho
    refine ⟨_, addr_ptr _ _, Or.inl ?_⟩
    interval_cases i <;> simp [cstBase, cstSizes] at ho ⊢ <;> omega
  have ownM : ∀ i e o, i < 10 → e + o < (cstSizes n).getD i 0 → ∃ i', (ptrAtV (cstBase n c i) * gen ^ e).limb 0 *
      addressOfIndex o = addressOfIndex i' ∧ CstLoc n c csel crow arrs i' := by
    intro i e o hi ho
    rw [addr_mul_gen]
    exact own i (e + o) hi ho
  have reg : ∀ q ∈ arrs, ∀ t < q.2, ∃ i, q.1.limb 0 * addressOfIndex t = addressOfIndex i ∧ CstLoc n c csel crow arrs i :=
    fun q hq t ht => by
      obtain ⟨i, hi, hr⟩ := region_of h.below hq ht
      exact ⟨i, hi, Or.inr (Or.inl hr)⟩
  have hG := h.gB ha
  by_cases hS : Atom.load d p off ∈ cstS
  · have hA := cst_atomB ha
    simp only [cstAtomB, hS, decide_true, ↓reduceIte, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at hA
    rcases hA with ((⟨rfl, hq⟩ | ⟨rfl, hq⟩) | ⟨rfl, hq⟩) | ⟨rfl, hq⟩
    · -- `rq`: `rho` times `eq_q`'s word
      simp only [cstRqB, Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true', decide_eq_false_iff_not] at hq
      obtain ⟨⟨⟨⟨⟨hd, h13⟩, hq33⟩, hmul⟩, hld⟩, hfr⟩ := hq
      have b2 : σ (.n 33) = ptrAtV (cstBase n c 2) := h.buf 2 (by norm_num)
      refine ⟨by rw [b2]; exact own 2 off (by norm_num) (by simp [cstSizes]; omega), fun _ => ?_⟩
      obtain ⟨m, rfl⟩ : ∃ m, d = .n m := ⟨d.idx, hd⟩
      dsimp only at h13 hmul hld hfr
      have hek : (eqKernel qPoint).length = 64 := by rw [length_eqKernel_eq, hqlen]; rfl
      have hv := readsAt_getD' heqq (i := off) (by rw [List.length_take, hek]; show off < min 33 64; omega)
      rw [loadHolds_mul_gen_pow] at hv
      have e1 := good_load_eq hv (h.gB hld) hfr
      have e2 := good_mul_eq (h.gB hmul) (by show 13 < m; omega) (by show m - 1 < m; omega)
      have hw := readsAt_getD' h.w2 (i := off) (by rw [cstRqW, List.length_map, List.length_range]; exact hq33)
      have hl : ((eqKernel qPoint).take (guest_const% N_POINTERS)).getD off 0 = (eqKernel qPoint).getD off 0 := by
        simp only [List.getD_eq_getElem?_getD, List.getElem?_take, show off < guest_const% N_POINTERS from hq33,
          ↓reduceIte]
      have hr : (cstRqW rho qPoint).getD off 0 = rho * (eqKernel qPoint).getD off 0 := by
        rw [cstRqW, List.getD_eq_getElem _ _ (by rw [List.length_map, List.length_range]; exact hq33)]
        simp only [List.getElem_map, List.getElem_range]
      rw [b2, e2, e1, hrho, hl, ← hr]
      exact hw
    · -- `pmask`: the pointer's mask
      simp only [cstMaskB, Bool.and_eq_true, decide_eq_true_eq] at hq
      obtain ⟨hq33, hq⟩ := hq
      have b1 : σ (.n 32) = ptrAtV (cstBase n c 1) := h.buf 1 (by norm_num)
      refine ⟨by rw [b1]; exact own 1 off (by norm_num) (by simp [cstSizes]; omega), fun _ => ?_⟩
      have hw := readsAt_getD' h.w1 (i := off) (by rw [cstMaskW, List.length_map, List.length_range]; exact hq33)
      have hmw : (cstMaskW layout x).getD off 0 = maskW layout x (ptrKinds.getD off 0) := by
        rw [cstMaskW, List.getD_eq_getElem _ _ (by rw [List.length_map, List.length_range]; exact hq33)]
        simp only [List.getElem_map, List.getElem_range]
      rw [hmw] at hw
      rw [b1]
      convert hw using 1
      have hk116 := ptrKinds_lt off hq33
      by_cases hk : ptrKinds.getD off 0 < 52
      · simp only [hk, ↓reduceIte, Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true',
          decide_eq_false_iff_not] at hq
        obtain ⟨hld, hfr⟩ := hq
        rw [good_load_eq (h.sel ▸ h.selOut _ hk) (h.gB hld) hfr]
        simp only [maskW, hk, ↓reduceIte]
      · simp only [hk, ↓reduceIte, Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true',
          decide_eq_false_iff_not] at hq
        obtain ⟨⟨⟨⟨hd, h52⟩, hmul⟩, hld⟩, hfr⟩ := hq
        obtain ⟨m, rfl⟩ : ∃ m, d = .n m := ⟨d.idx, hd⟩
        dsimp only at h52 hmul hld hfr
        have b8 : σ (.n 39) = ptrAtV (cstBase n c 8) := h.buf 8 (by norm_num)
        have hl : ptrKinds.getD off 0 + 10 < (tqW layout x).length := by
          rw [tqW, List.length_map, List.length_range]; omega
        have hv := readsAt_getD' h.w8 (i := ptrKinds.getD off 0 + 10) hl
        rw [← b8] at hv
        have e1 := good_load_eq hv (h.gB hld) hfr
        have e2 := good_mul_eq (h.gB hmul) (by show m - 1 < m; omega) (by show 52 < m; omega)
        have hget : (tqW layout x).getD (ptrKinds.getD off 0 + 10) 0 = tqEntry layout x (ptrKinds.getD off 0 + 10) := by
          rw [tqW, List.getD_eq_getElem _ _ (by rw [List.length_map, List.length_range]; omega)]
          simp only [List.getElem_map, List.getElem_range]
        rw [e2, e1, h.v52, hget, tqEntry_kern layout x (by omega : 52 ≤ ptrKinds.getD off 0) hk116]
        simp only [maskW, hk, ↓reduceIte]
    · -- `pi_pt`: `rm`, then zeros
      simp only [cstPiB, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at hq
      have b7 : σ (.n 38) = ptrAtV (cstBase n c 7) := h.buf 7 (by norm_num)
      have hoff : off < 31 := by rcases hq with ⟨-, rfl⟩ | ⟨⟨-, h2⟩, -⟩ <;> omega
      refine ⟨by rw [b7]; exact own 7 off (by norm_num) (by simp [cstSizes]; omega), fun _ => ?_⟩
      have hw := readsAt_getD' h.w7 (i := off) (by rw [piW, List.length_cons, List.length_replicate]; omega)
      rw [b7]
      convert hw using 1
      rcases hq with ⟨rfl, rfl⟩ | ⟨⟨h1, -⟩, hc⟩
      · rw [hrm, piW, List.getD_cons_zero]
      · have e : σ d = word 0 0 := h.gB hc
        rw [e, B1.word_zero]
        obtain ⟨o, rfl⟩ : ∃ o, off = o + 1 := ⟨off - 1, by omega⟩
        rw [piW, List.getD_cons_succ, List.getD_eq_getElem _ _ (by rw [List.length_replicate]; omega),
          List.getElem_replicate]
    · -- `eqtree`'s stores into `tq`
      obtain ⟨-, hoff⟩ := eqStore_off hq
      have b8 : σ (.n 39) = ptrAtV (cstBase n c 8) := h.buf 8 (by norm_num)
      exact ⟨by rw [b8]; exact own 8 off (by norm_num) (by simp [cstSizes]; omega), fun h' => h'.elim (fun h1 => absurd hS h1) (fun h2 => absurd hq h2)⟩
  · have hA := cst_atomB ha
    simp only [cstAtomB, hS, decide_false, Bool.false_eq_true, ↓reduceIte] at hA
    have fin : ∀ v, LoadHolds rd (σ p) off v → LoadHolds rd (σ p) off (σ d) := fun v hv => by
      rw [good_load_eq hv hG hS]; exact hv
    simp only [cstFreshB, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at hA
    rcases hA with ((((((⟨rfl, ho⟩ | ⟨rfl, ho⟩) | ⟨⟨rfl, ho1⟩, ho2⟩) | ⟨rfl, ho⟩) | ⟨rfl, ho⟩) | ⟨rfl, ho⟩) |
      ⟨rfl, ho⟩) | hD
    · -- `kappa_base`
      refine ⟨reg (σ (.n 1), 2 + nTables) (by simp [harrs, cstArrays, cstValArgs]) off (by simp [nTables]; omega),
        fun _ => ?_⟩
      exact fin _ (kappaSources_get hkb off ho)
    · -- `kaps`
      have hb : off < nStkBlocks := by simpa [nStkBlocks, stackBlocks_length] using ho
      refine ⟨reg (σ (.n 3), nStkBlocks) (by simp [harrs, cstArrays, cstValArgs]) off hb, fun _ => ?_⟩
      obtain ⟨pl, -, -, hkap⟩ := hplaced.2 off hb
      exact fin _ hkap
    · -- `eq_q`
      have hq : (σ (.n 11) * gen ^ guest_const% EQ_Q_AT, guest_const% N_POINTERS) ∈ arrs := by
        simp [harrs, cstArrays, cstValArgs]
      obtain ⟨i, hi, hr⟩ := reg _ hq (off - 62) (by show off - 62 < 33; omega)
      refine ⟨⟨i, ?_, hr⟩, fun _ => ?_⟩
      · rw [← hi, addr_mul_gen]
        congr 2
        show off = 62 + (off - 62)
        omega
      · have hek : (eqKernel qPoint).length = 64 := by rw [length_eqKernel_eq, hqlen]; rfl
        have hv := readsAt_getD' heqq (i := off - 62) (by rw [List.length_take, hek]; show off - 62 < min 33 64; omega)
        rw [loadHolds_mul_gen_pow, show guest_const% EQ_Q_AT + (off - 62) = off by show 62 + (off - 62) = off; omega] at hv
        exact fin _ hv
    · -- the selectors
      refine ⟨⟨csel + off, by rw [h.sel, addr_ptr], Or.inr (Or.inr (Or.inl ⟨by omega, by omega⟩))⟩, fun _ => ?_⟩
      exact fin _ (h.sel ▸ h.selOut off ho)
    · -- `q_keccak`'s ring row
      refine ⟨⟨crow + off, by rw [h.row, addr_ptr], Or.inr (Or.inr (Or.inr ⟨by omega, by omega⟩))⟩, fun _ => ?_⟩
      obtain ⟨v, hv⟩ := h.rowOut off ho
      exact fin _ (h.row ▸ hv)
    · -- `tq`
      have b8 : σ (.n 39) = ptrAtV (cstBase n c 8) := h.buf 8 (by norm_num)
      refine ⟨by rw [b8]; exact own 8 off (by norm_num) (by simp [cstSizes]; omega), fun _ => ?_⟩
      exact fin _ (b8 ▸ h.w8 off (by rw [tqW, List.length_map, List.length_range]; exact ho))
    · -- the point's slots' coordinates
      have hq : (σ (.n 17), 40) ∈ arrs := by simp [harrs, cstArrays, cstValArgs]
      obtain ⟨i, hi, hr⟩ := reg _ hq (hgt layout 5 + off) (by show hgt layout 5 + off < 40; omega)
      refine ⟨⟨i, by rw [h.v254, addr_mul_gen]; exact hi, hr⟩, fun _ => ?_⟩
      have hv := hpt (hgt layout 5 + off) (by rw [List.length_append, List.length_replicate]; omega)
      rw [← loadHolds_mul_gen_pow, ← h.v254] at hv
      exact fin _ hv
    · -- a prefix chain times the word fixing its index
      simp only [cstDerivB, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at hD
      obtain ⟨⟨hp, h52⟩, hD⟩ := hD
      obtain ⟨m, rfl⟩ : ∃ m, p = .n m := ⟨p.idx, hp⟩
      dsimp only at h52 hD
      have mulv : ∀ a b, Atom.mul (.n m) (.n a) (.n b) ∈ cstAtomsB → a < m → b < m →
          σ (.n m) = σ (.n a) * σ (.n b) := fun a b hm ha hb =>
        good_mul_eq (h.gB hm) ha hb
      have chain : ∀ (i : ℕ) (as : List E) (len e o : ℕ), i < 10 → (cstSizes n).getD i 0 = 42 ∨ (cstSizes n).getD i 0 = 31 →
          ReadsAt rd (ptrAtV (cstBase n c i)) (chainW as x len) → e + o ≤ len → len < (cstSizes n).getD i 0 →
          σ (.n m) = ptrAtV (cstBase n c i) * gen ^ e → off = o →
          (∃ i', (σ (.n m)).limb 0 * addressOfIndex off = addressOfIndex i' ∧ CstLoc n c csel crow arrs i') ∧
            (Atom.load d (.n m) off ∉ cstS ∨ Atom.load d (.n m) off ∉ eqStoresAt (.n 39) 0 255 6 →
              LoadHolds rd (σ (.n m)) off (σ d)) := by
        intro i as len e o hi _ hw hle hlt hσ hoff
        subst hoff
        refine ⟨by rw [hσ]; exact ownM i e off hi (by omega), fun _ => ?_⟩
        have hv := hw (e + off) (by rw [chainW, List.length_map, List.length_range]; omega)
        rw [← loadHolds_mul_gen_pow, ← hσ] at hv
        exact fin _ hv
      have b3 : σ (.n 34) = ptrAtV (cstBase n c 3) := h.buf 3 (by norm_num)
      rcases hD with ((((⟨rfl, hm⟩ | ⟨rfl, hm⟩) | ⟨rfl, hm⟩) | ⟨rfl, hm⟩) | ⟨rfl, hm⟩) | ⟨⟨rfl, hm⟩, hk⟩
      · exact chain 5 r layout.logMemory layout.logMemory 0 (by norm_num) (by simp [cstSizes]) h.w5 (by omega)
          (by simp [cstSizes]; omega) (by rw [mulv 36 8 hm (by omega) (by omega), h.buf 5 (by norm_num), hglm]) rfl
      · exact chain 6 (piW rm) layout.logMemory layout.logMemory 0 (by norm_num) (by simp [cstSizes]) h.w6 (by omega)
          (by simp [cstSizes]; omega) (by rw [mulv 37 8 hm (by omega) (by omega), h.buf 6 (by norm_num), hglm]) rfl
      · exact chain 9 z z.length layout.stackLog 0 (by norm_num) (by simp [cstSizes]) h.w9 (by omega)
          (by simp [cstSizes]; omega) (by rw [mulv 40 4 hm (by omega) (by omega), h.buf 9 (by norm_num), hplaced.1]) rfl
      · exact chain 4 kOut kOut.length (hgt layout 5) 6 (by norm_num) (by simp [cstSizes]) h.w4 (by omega)
          (by simp [cstSizes]; omega)
          (by rw [mulv 35 51 hm (by omega) (by omega), h.buf 4 (by norm_num), h.kbv 5 (by norm_num)]) rfl
      · exact chain 3 chi n (hgt layout 5) 0 (by norm_num) (by simp [cstSizes]) h.w3 (by omega)
          (by simp [cstSizes]; omega) (by rw [mulv 34 51 hm (by omega) (by omega), b3, h.kbv 5 (by norm_num)]) rfl
      · simp only [cstSentKB, List.any_eq_true, Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true',
          decide_eq_false_iff_not] at hk
        obtain ⟨k, hks, ⟨hk52, hld⟩, hfr⟩ := hk
        obtain ⟨t, ht, hsrc, hcl⟩ := (sentList_facts k hks).2 hk52
        have hb : k < nStkBlocks := by simpa [nStkBlocks, stackBlocks_length] using hk52
        obtain ⟨pl, hpl, -, hkap⟩ := hplaced.2 k hb
        have hP : blockP layout k = pl := by rw [blockP, hpl]; rfl
        have hvc : pl.variableCount = hgt layout t := by
          rw [← hP, (block_placed hbl hk52).2.1, blockKap, layout_kappa _ _ hcl hsrc]; rfl
        have hvn : pl.variableCount ≤ n := by rw [hvc]; exact hheights t (by simpa [nTables] using ht)
        have e1 := good_load_eq hkap (h.gB hld) hfr
        exact chain 3 chi n pl.variableCount 0 (by norm_num) (by simp [cstSizes]) h.w3 (by omega)
          (by simp [cstSizes]; omega) (by rw [mulv 34 (m - 1) hm (by omega) (by omega), b3, e1]) rfl

end load

end

end
end LeanVM.Guest.B1.VsC
