/-
  LeanVM.Guest.B1.Tables.VerifyTablesC0

  `verify_tables`' completeness: the bytecode share's hint and the six tables' padding weights.
-/

module

public import LeanVM.Guest.B1.Tables.VerifyTablesFwdI
public import LeanVM.Guest.B1.Tables.VerifyTablesPad
public import LeanVM.Guest.B1.Tables.VtCPad
public import LeanVM.Guest.B1.Uniform

/-!
# The padding weights, forward (G:1534-1542)

`vtPre`'s statements `1438 ..< 1505` as items (`vtIt0`): the hinted bytecode share, then per
table its log-height `τ` read from `dims`, range-checked, the padding weight dispatched on it
(`padding_weight__Lτ` on the row count and `zeta`), its `lead` asserted `1` and its `rest`
nonzero. `vt_c0`: on the honest dispatch results (`vtHv0`), the window completes.
-/

namespace LeanVM.Guest.B1.VerifySub

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.Verifier
open LeanVM.Guest.B1.Sig

@[expose] public section

/-- Table `t`'s padding weight, as items. -/
def vtPadI (t : ℕ) : List FItem :=
  [.atom (.load (.n (1733 + 14 * t)) (.n 7) (t + 1)),
    .atom (.const (.n (1733 + 14 * t + 1)) (word 268435456 0 0)),
    .atom (.rangeCheck (.n (1733 + 14 * t)) (.n (1733 + 14 * t + 2)) (.n (1733 + 14 * t + 3))
      (.n (1733 + 14 * t + 4)) (.n (1733 + 14 * t + 1))),
    .atom (.load (.n (1733 + 14 * t + 5)) (.n 8) t),
    .disp (.n (1733 + 14 * t)) pwNames [.n (1733 + 14 * t + 5), .n 5]
      [.n (1733 + 14 * t + 6), .n (1733 + 14 * t + 7), .n (1733 + 14 * t + 8)],
    .atom (.const (.n (1733 + 14 * t + 9)) (word 1 0 0)),
    .atom (.assertEq (.n (1733 + 14 * t + 7)) (.n (1733 + 14 * t + 9))),
    .atom (.const (.n (1733 + 14 * t + 10)) (word 0 0 0)),
    .atom (.add (.n (1733 + 14 * t + 11)) (.n (1733 + 14 * t + 8)) (.n (1733 + 14 * t + 10))),
    .hint (.inverse (.n (1733 + 14 * t + 11)) (.n (1733 + 14 * t + 12))),
    .atom (.assertNe (.n (1733 + 14 * t + 11)) (.n (1733 + 14 * t + 12)) (.n (1733 + 14 * t + 13)))]

/-- The window's items. -/
def vtIt0 : List FItem := .hint (.witness "bytecode_val" (.stack [.n 1732])) :: (List.range 6).flatMap vtPadI

set_option maxRecDepth 100000 in
theorem vtIt0_eq : vtIt0.flatMap FItem.stmts = (vtPre.drop 1438).take 67 :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem vtIt0_ok : fOkI 1732 1817 [] vtIt0 = true := by decide +kernel

/-- Table `t`'s obligations. -/
def vtPadOb (t : ℕ) : List IOb :=
  [.ob (.ld (.n 7) (t + 1)), .ob (.rc (.n (1733 + 14 * t)) (.n (1733 + 14 * t + 2))), .ob (.ld (.n 8) t),
    .disp (.n (1733 + 14 * t)) pwNames [.n (1733 + 14 * t + 5), .n 5]
      [.n (1733 + 14 * t + 6), .n (1733 + 14 * t + 7), .n (1733 + 14 * t + 8)],
    .ob (.holds (.assertEq (.n (1733 + 14 * t + 7)) (.n (1733 + 14 * t + 9)))),
    .ob (.unit (.n (1733 + 14 * t + 11)) (.n (1733 + 14 * t + 12)))]

set_option maxRecDepth 100000 in
theorem vtIt0_obs : iObs 1732 [] vtIt0 = (List.range 6).flatMap vtPadOb :=
  listEqb_sound iobEqb_sound (by decide +kernel)

/-- Table `t`'s definitions. -/
def vtPadEq (t : ℕ) : List FEq :=
  [.ld (.n (1733 + 14 * t)) (.n 7) (t + 1), .def (.const (.n (1733 + 14 * t + 1)) (word 268435456 0 0)),
    .rc (.n (1733 + 14 * t)) (.n (1733 + 14 * t + 2)) (.n (1733 + 14 * t + 3)) (.n (1733 + 14 * t + 4))
      (.n (1733 + 14 * t + 1)),
    .ld (.n (1733 + 14 * t + 5)) (.n 8) t,
    .item (.disp (.n (1733 + 14 * t)) pwNames [.n (1733 + 14 * t + 5), .n 5]
      [.n (1733 + 14 * t + 6), .n (1733 + 14 * t + 7), .n (1733 + 14 * t + 8)]),
    .def (.const (.n (1733 + 14 * t + 9)) (word 1 0 0)), .def (.const (.n (1733 + 14 * t + 10)) (word 0 0 0)),
    .def (.add (.n (1733 + 14 * t + 11)) (.n (1733 + 14 * t + 8)) (.n (1733 + 14 * t + 10))),
    .item (.hint (.inverse (.n (1733 + 14 * t + 11)) (.n (1733 + 14 * t + 12))))]

set_option maxRecDepth 100000 in
theorem vtIt0_eqsB : ∀ t < 6, (vtPadEq t).all fun e => (fEqs 1732 [] vtIt0).any (feqEqb e) := by
  decide +kernel

theorem vtIt0_eqs : ∀ t < 6, ∀ e ∈ vtPadEq t, e ∈ fEqs 1732 [] vtIt0 := fun t ht e he =>
  mem_of_any feqEqb_sound (List.all_eq_true.mp (vtIt0_eqsB t ht) e he)

set_option maxRecDepth 100000 in
theorem vtIt0_bv : FEq.item (.hint (.witness "bytecode_val" (.stack [.n 1732]))) ∈ fEqs 1732 [] vtIt0 :=
  mem_of_any feqEqb_sound (by decide +kernel)

/-- The window's hints and dispatch results: the bytecode share, and per table its padding
weight, `lead`, `rest` and `rest⁻¹`. -/
noncomputable def vtHv0 (bv : E) (pw lead rest : ℕ → E) (k : ℕ) : E :=
  if k = 1732 then bv
  else if (k - 1733) % 14 = 6 then pw ((k - 1733) / 14)
  else if (k - 1733) % 14 = 7 then lead ((k - 1733) / 14)
  else if (k - 1733) % 14 = 8 then rest ((k - 1733) / 14)
  else if (k - 1733) % 14 = 12 then (rest ((k - 1733) / 14))⁻¹
  else 0

theorem memAt_of_loadHolds {rd : Reader} {p w : E} {off : ℕ} (h : LoadHolds rd p off w) :
    memAt rd p off = w := by
  rw [memAt, h.2]; rfl

theorem isSome_of_loadHolds {rd : Reader} {p w : E} {off : ℕ} (h : LoadHolds rd p off w) :
    (rd (p.limb 0 * Parameters.gpow off)).isSome := by
  rw [h.2]; rfl

theorem low_gen_pow {κ : ℕ} {rd : Reader} (hl : LowDef κ rd) {i : ℕ} (hi : i < 2 ^ κ) :
    IsInK (gen ^ i) ∧ (rd ((gen ^ i).limb 0 * Parameters.gpow 0)).isSome := by
  have := loadHolds_low hl hi
  rw [← gen_pow_eq_ofK] at this
  exact ⟨this.1, isSome_of_loadHolds this⟩

theorem gen_pow_div {a b : ℕ} (h : a ≤ b) : gen ^ b * (gen ^ a)⁻¹ = gen ^ (b - a) := by
  rw [show b = (b - a) + a by omega, pow_add, mul_assoc, mul_inv_cancel₀ (gen_pow_ne_zero a), mul_one,
    Nat.add_sub_cancel]

section
variable {rd : Reader} {σ : Val} {dims rowsP zeta bv : E} {logMem : ℕ} {rowsN : List ℕ} {point : List E}

/-- The window's oracle on the run's data. -/
noncomputable def vtHvP (bv : E) (rowsN : List ℕ) (point : List E) : ℕ → E :=
  vtHv0 bv (fun t => paddingWeight (point.take (log2Ceil (rowsN.getD t 0))) (rowsN.getD t 0))
    (fun t => pwLead (log2Ceil (rowsN.getD t 0)) (rowsN.getD t 0))
    (fun t => pwRest (log2Ceil (rowsN.getD t 0)) (rowsN.getD t 0))

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
/-- **The padding weights complete** (G:1534-1542): the bytecode share hinted, and each table's
weight at its log-height. -/
theorem vt_c0 {κ : ℕ} (hκ : 5 ≤ κ) (hlow : LowDef κ rd) (h7 : σ (.n 7) = dims) (h8 : σ (.n 8) = rowsP)
    (h5 : σ (.n 5) = zeta)
    (hdims : ReadsAt rd dims (gen ^ logMem :: rowsN.map fun n ↦ gen ^ log2Ceil n))
    (hrows : ReadsAt rd rowsP (rowsN.map eOfNat)) (hz : ReadsAt rd zeta point) (hrl : rowsN.length = 6)
    (hτ : ∀ t < 6, log2Ceil (rowsN.getD t 0) < 29)
    (hτp : ∀ t < 6, log2Ceil (rowsN.getD t 0) ≤ point.length) :
    Completes (coreProgram.Rel rd) rd 1732 1817 ((vtPre.drop 1438).take 67) σ (fun σ' =>
      σ' (.n 1732) = bv ∧ ∀ t < 6, σ' (.n (1733 + 14 * t)) = gen ^ log2Ceil (rowsN.getD t 0) ∧
        σ' (.n (1739 + 14 * t)) =
          paddingWeight (point.take (log2Ceil (rowsN.getD t 0))) (rowsN.getD t 0)) := by
  rw [← vtIt0_eq]
  set hv := vtHvP bv rowsN point
  have Cm := completes_items (C := coreProgram.Rel rd) (rd := rd) hv vtIt0 vtIt0_ok σ
  generalize hσf : fRunI rd 1732 hv [] σ vtIt0 = σf at Cm
  have hf : ∀ v, fRunI rd 1732 hv [] σ vtIt0 v = σf v := fun v => by rw [hσf]
  have E := fRunI_eqs rd hv σf vtIt0 [] σ vtIt0_ok hf
  have FR : ∀ k < 1732, σf (.n k) = σ (.n k) := fun k hk =>
    fRunI_eq_of_def rd hv vtIt0_ok hf (by simp [fDef, vNum, hk])
  have h2k : 29 ≤ 2 ^ κ := le_trans (by norm_num) (Nat.pow_le_pow_right (by norm_num) hκ)
  have hdd : ∀ t < 6, LoadHolds rd dims (t + 1) (gen ^ log2Ceil (rowsN.getD t 0)) := fun t ht => by
    have := hdims (t + 1) (by simp; omega)
    simp only [List.getElem_cons_succ, List.getElem_map] at this
    rwa [List.getD_eq_getElem _ _ (by omega)]
  have hrr : ∀ t < 6, LoadHolds rd rowsP t (eOfNat (rowsN.getD t 0)) := fun t ht => by
    have := hrows t (by simp; omega)
    simp only [List.getElem_map] at this
    rwa [List.getD_eq_getElem _ _ (by omega)]
  -- each table's facts
  have key : ∀ t < 6, σf (.n (1733 + 14 * t)) = gen ^ log2Ceil (rowsN.getD t 0) ∧
      σf (.n (1733 + 14 * t + 1)) = word 268435456 0 0 ∧
      σf (.n (1733 + 14 * t + 2)) = gen ^ (28 - log2Ceil (rowsN.getD t 0)) ∧
      σf (.n (1733 + 14 * t + 5)) = eOfNat (rowsN.getD t 0) ∧
      σf (.n (1733 + 14 * t + 6)) =
        paddingWeight (point.take (log2Ceil (rowsN.getD t 0))) (rowsN.getD t 0) ∧
      σf (.n (1733 + 14 * t + 7)) = pwLead (log2Ceil (rowsN.getD t 0)) (rowsN.getD t 0) ∧
      σf (.n (1733 + 14 * t + 8)) = pwRest (log2Ceil (rowsN.getD t 0)) (rowsN.getD t 0) ∧
      σf (.n (1733 + 14 * t + 9)) = word 1 0 0 ∧
      σf (.n (1733 + 14 * t + 11)) = pwRest (log2Ceil (rowsN.getD t 0)) (rowsN.getD t 0) + word 0 0 0 ∧
      σf (.n (1733 + 14 * t + 12)) = (pwRest (log2Ceil (rowsN.getD t 0)) (rowsN.getD t 0))⁻¹ := by
    intro t ht
    have Et := fun e he => E e (vtIt0_eqs t ht e he)
    simp only [vtPadEq, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at Et
    obtain ⟨e0, e1, e2, e5, e6, e9, e10, e11, e12⟩ := Et
    have hτt := hτ t ht
    have hd := hdd t ht
    have hr := hrr t ht
    have v0 : σf (.n (1733 + 14 * t)) = gen ^ log2Ceil (rowsN.getD t 0) := by
      rw [show σf (.n (1733 + 14 * t)) = memAt rd (σf (.n 7)) (t + 1) from e0, FR 7 (by omega), h7,
        memAt_of_loadHolds hd]
    have v1 : σf (.n (1733 + 14 * t + 1)) = word 268435456 0 0 := e1
    have hv6 := e6 0 (by show 0 < 3; omega) (by show 0 < 3; omega)
    have hv7 := e6 1 (by show 1 < 3; omega) (by show 1 < 3; omega)
    have hv8 := e6 2 (by show 2 < 3; omega) (by show 2 < 3; omega)
    have hv12 := e12 0 (by show 0 < 1; omega) (by show 0 < 1; omega)
    simp only [FItem.sets, FItem.vals, hintCells, List.getElem_cons_zero, List.getElem_cons_succ,
      List.map_cons, List.map_nil] at hv6 hv7 hv8 hv12
    have i6 : (1733 + 14 * t + 6 - 1733) % 14 = 6 ∧ (1733 + 14 * t + 6 - 1733) / 14 = t := by omega
    have i7 : (1733 + 14 * t + 7 - 1733) % 14 = 7 ∧ (1733 + 14 * t + 7 - 1733) / 14 = t := by omega
    have i8 : (1733 + 14 * t + 8 - 1733) % 14 = 8 ∧ (1733 + 14 * t + 8 - 1733) / 14 = t := by omega
    have i12 : (1733 + 14 * t + 12 - 1733) % 14 = 12 ∧ (1733 + 14 * t + 12 - 1733) / 14 = t := by omega
    refine ⟨v0, v1, ?_, ?_, ?_, ?_, ?_, e9, ?_, ?_⟩
    · obtain ⟨y, -, -⟩ := e2
      rw [y, v1, v0, show (268435456 : ℕ) = 2 ^ 28 by norm_num, word_two_pow (by norm_num)]
      exact gen_pow_div (by omega)
    · rw [show σf (.n (1733 + 14 * t + 5)) = memAt rd (σf (.n 8)) t from e5, FR 8 (by omega), h8,
        memAt_of_loadHolds hr]
    · rw [hv6]; simp only [hv, vtHvP, vtHv0, i6]; simp; omega
    · rw [hv7]; simp only [hv, vtHvP, vtHv0, i7]; simp; omega
    · rw [hv8]; simp only [hv, vtHvP, vtHv0, i8]; simp; omega
    · rw [show σf (.n (1733 + 14 * t + 11)) = σf (.n (1733 + 14 * t + 8)) + σf (.n (1733 + 14 * t + 10))
        from e11, show σf (.n (1733 + 14 * t + 10)) = word 0 0 0 from e10, hv8]
      simp only [hv, vtHvP, vtHv0, i8]; simp; omega
    · rw [hv12]; simp only [hv, vtHvP, vtHv0, i12]; simp; omega
  refine (Cm (IObls_of_obs _ _ ?_)).mono le_rfl le_rfl ?_
  · rw [vtIt0_obs]
    intro o ho
    obtain ⟨t, ht, ho⟩ := List.mem_flatMap.mp ho
    have ht' := List.mem_range.mp ht
    obtain ⟨k0, k1, k2, k5, k6, k7, k8, k9, k11, k12⟩ := key t ht'
    have hτt := hτ t ht'
    have hd := hdd t ht'
    have hr := hrr t ht'
    obtain ⟨hl1, hl2⟩ := pw_lead_rest hτt (rfl : log2Ceil (rowsN.getD t 0) = _)
    simp only [vtPadOb, List.mem_cons, List.not_mem_nil, or_false] at ho
    rcases ho with rfl | rfl | rfl | rfl | rfl | rfl
    · show IsInK (σf (.n 7)) ∧ _
      rw [FR 7 (by omega), h7]; exact ⟨hd.1, isSome_of_loadHolds hd⟩
    · show σf (.n (1733 + 14 * t)) ≠ 0 ∧ IsInK (σf (.n (1733 + 14 * t))) ∧ _ ∧ IsInK (σf (.n (1733 + 14 * t + 2))) ∧ _
      rw [k0, k2]
      have a := low_gen_pow hlow (i := log2Ceil (rowsN.getD t 0)) (by omega)
      have b := low_gen_pow hlow (i := 28 - log2Ceil (rowsN.getD t 0)) (by omega)
      exact ⟨gen_pow_ne_zero _, a.1, a.2, b.1, b.2⟩
    · show IsInK (σf (.n 8)) ∧ _
      rw [FR 8 (by omega), h8]; exact ⟨hr.1, isSome_of_loadHolds hr⟩
    · refine ⟨log2Ceil (rowsN.getD t 0), by rw [show pwNames.length = 29 from rfl]; omega,
        by rw [k0, gen_pow_eq_ofK], ?_⟩
      simp only [List.map_cons, List.map_nil]
      rw [k5, FR 5 (by omega), h5, k6, k7, k8]
      refine pw_dispatch_complete _ _ ⟨rowsN.getD t 0, point.take (log2Ceil (rowsN.getD t 0)),
        log2Ceil_le_iff.mp le_rfl, rfl, by simp only [List.length_take]; have := hτp t ht'; omega,
        fun k hk => ?_, rfl⟩
      simp only [List.length_take] at hk
      have := hz k (by omega)
      simpa [List.getElem_take] using this
    · show σf (.n (1733 + 14 * t + 7)) + σf (.n (1733 + 14 * t + 9)) = 0
      rw [k7, k9, hl1, word_one]; exact e_add_self 1
    · show σf (.n (1733 + 14 * t + 11)) * σf (.n (1733 + 14 * t + 12)) = 1
      rw [k11, k12, word_zero, add_zero]; exact mul_inv_cancel₀ hl2
  · rintro σ' rfl
    refine ⟨?_, fun t ht => ⟨(key t ht).1, ?_⟩⟩
    · have := E _ vtIt0_bv 0 (by show 0 < 1; omega) (by show 0 < 1; omega)
      simp only [FItem.sets, FItem.vals, hintCells, List.getElem_cons_zero, List.map_cons, List.map_nil] at this
      rw [this]; simp [hv, vtHvP, vtHv0]
    · rw [show 1739 + 14 * t = 1733 + 14 * t + 6 by ring]; exact (key t ht).2.2.2.2.1

end

end
end LeanVM.Guest.B1.VerifySub
