/-
  LeanVM.Guest.B1.Exact.VtOwn

  `verify_tables`' own computed hints exact at its honest valuation, on a memory holding its caller's buffers and its
  own: the heap digits and bits are its offsets' at their tables' heights, the limbs its evaluation's.
-/

module

public import LeanVM.Guest.B1.Tables.VtC.AWeight
public import LeanVM.Guest.Exact.Ok

/-!
# `verify_tables`' own computed hints, exact

`vtSites`: its computed hints not pinned by the next atom, its three framework blocks' offset bits (`vtBitA`), its 96
table blocks' offset digits (`vtDigA`), the start shift of a block of table `t` its `kappa_base` word `27 + t`, and its
two limbs; every other is an `inverse` followed by its `assertNe` (`vt_sites_ok`, by the kernel). On the honest
valuation `vtσ` of a memory holding the caller's buffers and the own buffers, the offsets are `g^offP`, `g^offC` and
the start words `g^τ_t` (`vtS_sort`), the buffers hold `offBits`, `offDigits off τ_t` (`ownW`), which are the executor's
formula of them (`digits_exact`, `bitsExp_exact`), and the evaluation writes the limbs (`vt_limbs_exact`).
`vt_own_exact`: so every valid node of `verify_tables` at its honest valuation is exact.
-/

namespace LeanVM.Guest.B1.Tables

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Memory
open LeanVM.Guest.B1.Fwd
open LeanVM.Protocol.Verifier (gen)
open LeanVM.Guest.B1.Main (MemL)

@[expose] public section

attribute [local instance high] LeanVM.Guest.Core.instDecidableEqAtom

/-- A table block's digits hint: block `b`, buffer `w`, table `t`. -/
def vtDigA (b w t : ℕ) : Atom :=
  .hint (.digitsExp (.n (vtBoffV b)) 34 9 4 0 (some (.n (27 + t))) (.heap (.n w) 0 9))

/-- A framework block's bits hint. -/
def vtBitA (b : ℕ) : Atom := .hint (.bitsExp (.n (vtBoffV b)) 34 (.heap (.n (vtFwW b + 6)) 0 34))

/-- The two limbs hints. -/
def vtLimbA : List Atom := [.hint (.limbs (.n 6) [.n 5962]), .hint (.limbs (.n 7) [.n 5967])]

/-- `verify_tables`' computed hints not pinned by the next atom. -/
def vtSites : List Atom :=
  (List.range 3).map vtBitA ++
    (List.range 51).map (fun i ↦ vtDigA (vtPushSel.getD i default).1 (vtPushSel.getD i default).2.2.1
      (vtPushSel.getD i default).2.2.2.1) ++
    (List.range 45).map (fun i ↦ vtDigA (vtCountSel.getD i default).1 (vtCountSel.getD i default).2.2.1
      (vtCountSel.getD i default).2.2.2.1) ++ vtLimbA

theorem vt_sites_ok : Stmt.blockNextOk (fun a => isComputed a && !decide (a ∈ vtSites)) pinsInverse
    (core% «verify_tables» body) = true := by
  decide +kernel

theorem vt_sel_data : (∀ i < 51, (vtPushSel.getD i default).1 = 3 + i ∧ (vtPushSel.getD i default).2.2.2.1 < 6 ∧
      (vtPushSel.getD i default).2.2.1 ∈ vtAllocVars) ∧
    (∀ i < 45, (vtCountSel.getD i default).1 = 108 + i ∧ (vtCountSel.getD i default).2.2.2.1 < 6 ∧
      (vtCountSel.getD i default).2.2.1 ∈ vtAllocVars) ∧ ∀ b < 3, vtFwW b + 6 ∈ vtAllocVars := by
  decide

/-- A heap hint's words where the memory holds them. -/
theorem words_heap_reads {rd : Reader} {σ : Val} {p : V} {P : E} {ws : List E} (hp : σ p = P)
    (hr : TbReadsAt rd P ws) : Dest.words rd σ (.heap p 0 ws.length) = ws :=
  List.ext_getElem (by simp [Dest.words]) fun k _ h2 => by simp [Dest.words, hp, (hr k h2).2]

/-- `offDigits` is the executor's digits of an offset from a shift below `96`. -/
theorem offDigits_eq {off τ : ℕ} (hτ : τ < 96) :
    offDigits off τ = (List.range 9).map fun j ↦ ofK (g ^
      (if 128 ≤ τ + 4 * j then 0 else (off >>> (τ + 4 * j)) % 2 ^ 4)) := by
  apply List.ext_getElem (by rw [offDigits_length]; simp)
  intro j h1 _
  rw [offDigits_length] at h1
  simp only [offDigits, nibDigits, selBitsOf_length, List.getElem_map, List.getElem_range]
  simp only [show ¬ 128 ≤ τ + 4 * j by omega, ↓reduceIte]
  rw [gen_pow_eq_ofK]
  congr 2
  rw [← bitsVal_testBit (Nat.mod_lt _ (by norm_num : 0 < 2 ^ 4))]
  refine bitsVal_congr fun t ht ↦ ?_
  rw [Nat.testBit_mod_two_pow, decide_eq_true ht, Bool.true_and, Nat.testBit_shiftRight, selBitsOf,
    List.getD_eq_getElem _ _ (by simp; omega)]
  simp only [List.getElem_map, List.getElem_range]
  congr 1
  omega

/-- **A table block's digits hint is exact** where its offset is `g^off`, its shift word `g^τ` and its buffer holds
`offDigits off τ`. -/
theorem digits_exact {rd : Reader} {σ : Val} {v c p : V} {off τ : ℕ} {P : E} (hoff : off < 2 ^ 34) (hτ : τ < 96)
    (hv : σ v = gen ^ off) (hc : σ c = gen ^ τ) (hp : σ p = P) (hr : TbReadsAt rd P (offDigits off τ)) :
    (Hint.digitsExp v 34 9 4 0 (some c) (.heap p 0 9)).Exact rd σ := by
  refine ⟨off, τ, hoff, by rw [hv, gen_pow_eq_ofK], ⟨by omega, by rw [hc, gen_pow_eq_ofK]⟩, ?_⟩
  have e := words_heap_reads hp hr
  rw [offDigits_length] at e
  rw [e, offDigits_eq hτ]

/-- **A framework block's bits hint is exact** where its offset is `g^off` and its buffer holds `offBits off`. -/
theorem bitsExp_exact {rd : Reader} {σ : Val} {v p : V} {off : ℕ} {P : E} (hoff : off < 2 ^ 34)
    (hv : σ v = gen ^ off) (hp : σ p = P) (hr : TbReadsAt rd P (offBits off)) :
    (Hint.bitsExp v 34 (.heap p 0 34)).Exact rd σ := by
  refine ⟨off, hoff, by rw [hv, gen_pow_eq_ofK], ?_⟩
  have e := words_heap_reads hp hr
  rw [offBits_length] at e
  rw [e, offBits]
  exact List.map_congr_left fun j _ ↦ bitE_eq_bitWord _

section
variable {rd : Reader} {w : ℕ → E} {args : List E}

/-- **The limbs hints are exact** on the honest valuation: it evaluates them. -/
theorem vt_limbs_exact (hl : args.length = 20) : ∀ a ∈ vtLimbA, a.Exact rd (vtσ rd w args) := by
  have g1 := vt_goodL (rd := rd) (w := w) hl 5527 [.atom (.hint (.limbs (.n 6) [.n 5962]))] (by decide +kernel)
  have g2 := vt_goodL (rd := rd) (w := w) hl 5533 [.atom (.hint (.limbs (.n 7) [.n 5967]))] (by decide +kernel)
  generalize vtσ rd w args = σ at g1 g2 ⊢
  simp only [GoodL, GoodS, fixNe, Good, and_true] at g1 g2
  intro a ha
  simp only [vtLimbA, List.mem_cons, List.not_mem_nil, or_false] at ha
  rcases ha with rfl | rfl
  · have := g1 0 (by simp)
    simp only [List.getElem_cons_zero, limbAt] at this
    simp [Atom.Exact, Hint.Exact, this]
  · have := g2 0 (by simp)
    simp only [List.getElem_cons_zero, limbAt] at this
    simp [Atom.Exact, Hint.Exact, this]

end

/-- **Every site is exact** on the honest valuation of a memory holding the caller's buffers and the own buffers at
`o`. -/
theorem vt_sites_exact {H : VtHonest} (hs : VtShape H) (B : VtBases) {o : ℕ} {rd : Reader} (hlow : LowDef 14 rd)
    (hlin : MemL rd (H.linL B)) (hown : MemL rd (bufL o H.sizes (H.ownW B))) :
    ∀ a ∈ vtSites, a.Exact rd (vtσ rd (vtW H (B.at o)) (H.args B)) := by
  set B' := B.at o
  have hm : MemLay rd (H.linL B' ++ H.ownL B') := fun q hq ↦ by
    rcases List.mem_append.mp hq with hq | hq
    · exact hlin q hq
    · exact hown q hq
  have hw := vtW_ok H B'
  have hl : (H.args B').length = 20 := rfl
  have p : ∀ i < 20, (vtσ rd (vtW H B') (H.args B')) (.n i) = (H.args B').getD i 0 := fun i hi ↦ vt_param hl hi
  have mDims : TbReadsAt rd (ofK (addressOfIndex B'.dims)) H.dimsW :=
    vt_lin_reads (q := (B'.dims, H.dimsW)) hm (by simp [VtHonest.linL])
  have mSq : TbReadsAt rd (ofK (addressOfIndex B'.sq)) expTableWordsW :=
    vt_lin_reads (q := (B'.sq, expTableWordsW)) hm (by simp [VtHonest.linL])
  have hd := fun j (hj : j < 9) ↦ ownW_getD_head H B' hj
  have o33 : TbReadsAt rd (vtW H B' 33) (vtGKeyW H.lm H.τ) :=
    vt_own_reads' hm hw (j := 0) (by norm_num) rfl (hd 0 (by norm_num))
  have o34 : TbReadsAt rd (vtW H B' 34) (vtGSizeW H.lm H.τ) :=
    vt_own_reads' hm hw (j := 1) (by norm_num) rfl (hd 1 (by norm_num))
  have o35 : TbReadsAt rd (vtW H B' 35) (vtGBaseW H.lm H.τ) :=
    vt_own_reads' hm hw (j := 2) (by norm_num) rfl (hd 2 (by norm_num))
  have o36 : TbReadsAt rd (vtW H B' 36) (vtGOrdW H.lm H.τ) :=
    vt_own_reads' hm hw (j := 3) (by norm_num) rfl (hd 3 (by norm_num))
  obtain ⟨-, -, hkb, -, hP, hC⟩ :=
    vtS_sort (rd := rd) (w := vtW H B') (args := H.args B') hl hlow hs.hlm hs.hτ33
      (by rw [p 10 (by norm_num)]; exact mDims) (by rw [p 12 (by norm_num)]; exact vt_expTablesAt mSq) o33 o34 o35 o36
  rw [vt_sizesP_eq] at hP
  rw [vt_sizesC_eq] at hC
  have hμ := hs.hμ33
  have hfP : ∀ x < 54, H.offP.getD x 0 < 2 ^ 34 := fun x hx ↦
    lt_of_lt_of_le (vtB_stack_lt _ (by rw [vtSizesP_length]; exact hx) hs.hfitP)
      (Nat.pow_le_pow_right (by norm_num) (by omega))
  have hfC : ∀ x < 45, H.offC.getD x 0 < 2 ^ 34 := fun x hx ↦
    lt_of_lt_of_le (vtB_stack_lt _ (by rw [vtSizesC_length]; exact hx) hs.hfitC)
      (Nat.pow_le_pow_right (by norm_num) (by omega))
  have hP' : ∀ x < 54, vtσ rd (vtW H B') (H.args B') (.n (vtBoffV x)) = gen ^ H.offP.getD x 0 := hP
  have hC' : ∀ x < 45, vtσ rd (vtW H B') (H.args B') (.n (vtBoffV (108 + x))) = gen ^ H.offC.getD x 0 := hC
  have hkbt : ∀ t < 6, vtσ rd (vtW H B') (H.args B') (.n (27 + t)) = gen ^ H.τ t := fun t ht ↦ by
    have := hkb (2 + t) (by omega)
    rw [show 25 + (2 + t) = 27 + t by omega, Nat.add_comm 2 t, vt_tau_getD H.lm (vtHt H.rows) ht] at this
    exact this
  have hτ : ∀ t < 6, H.τ t < 96 := fun t ht ↦ by have := hs.hτ31 t ht; simp only [VtHonest.τ]; omega
  obtain ⟨dP, dC, dF⟩ := vt_sel_data
  intro a ha
  simp only [vtSites, List.mem_append, List.mem_map, List.mem_range] at ha
  rcases ha with ((⟨b, hb, rfl⟩ | ⟨i, hi, rfl⟩) | ⟨i, hi, rfl⟩) | ha
  · have hr := vt_own_reads' hm hw (j := 9 + b) (by omega) (vtAllocVars_F b hb) (ownW_getD_F H B' hb)
    exact bitsExp_exact (hfP b (by omega)) (hP' b (by omega)) (vt_alloc_var hl (dF b hb)) hr
  · obtain ⟨e1, ht, hav⟩ := dP i hi
    have hr := vt_own_reads' hm hw (j := 12 + i) (by omega) (vtAllocVars_P i hi) (ownW_getD_P H B' hi)
    have hv : vtσ rd (vtW H B') (H.args B') (.n (vtBoffV (vtPushSel.getD i default).1)) =
        gen ^ H.offP.getD (3 + i) 0 := by rw [e1]; exact hP' _ (by omega)
    exact digits_exact (hfP (3 + i) (by omega)) (hτ _ ht) hv (hkbt _ ht) (vt_alloc_var hl hav) hr
  · obtain ⟨e1, ht, hav⟩ := dC i hi
    have hr := vt_own_reads' hm hw (j := 63 + i) (by omega) (vtAllocVars_C i hi) (ownW_getD_C H B' hi)
    have hv : vtσ rd (vtW H B') (H.args B') (.n (vtBoffV (vtCountSel.getD i default).1)) =
        gen ^ H.offC.getD i 0 := by rw [e1]; exact hC' _ hi
    exact digits_exact (hfC i hi) (hτ _ ht) hv (hkbt _ ht) (vt_alloc_var hl hav) hr
  · exact vt_limbs_exact hl a ha

/-- **`verify_tables`' own computed hints are exact at its honest valuation**, on a memory holding its caller's
buffers. -/
theorem vt_own_exact {H : VtHonest} (hs : VtShape H) (B : VtBases) {rd : Reader} {σ : Val} {bufs : List ℕ}
    {ks : List Tree} {args rets : List E} (hq : vtQn H B rd σ) (hlow : LowDef 14 rd) (hlin : MemL rd (H.linL B))
    (hv : (Memory.Tree.node "verify_tables" σ bufs ks).Valid coreProgram rd args rets) :
    ExactAt coreProgram rd "verify_tables" σ := by
  obtain ⟨o, rfl, hown, -, -⟩ := hq
  obtain ⟨fn, hf, -, es, vs, hw, -, hes, -⟩ := hv
  obtain ⟨fn', hf', -, hb⟩ := vtFound
  have e : fn = fn' := Option.some.inj (hf.symm.trans hf')
  subst e
  have hpin : Stmt.blockNextOk (fun a => isComputed a && !decide (a ∈ vtSites)) pinsInverse fn.body = true := by
    rw [hb, ← verify_tables_body]; exact vt_sites_ok
  exact exactAt_of_walk hf hw (exact_of_sites hpin hw hes fun a ha _ ↦ vt_sites_exact hs B hlow hlin hown a ha)

end
end LeanVM.Guest.B1.Tables
