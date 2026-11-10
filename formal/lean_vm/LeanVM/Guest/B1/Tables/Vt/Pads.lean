/-
  LeanVM.Guest.B1.Tables.Vt.Pads

  `verify_tables`' table heights: each table's hinted log-height is `max (log2Ceil rows) floor`, its
  row count an integer word, and its padding weight `paddingWeight` at the bus point's prefix.
-/

module

public import LeanVM.Guest.B1.Tables.Vt.Sort
public import LeanVM.Guest.B1.Tables.Padding

/-!
# The tables' heights (G:2195-2209)

Table `t`'s statements (`vtPadT`, `vtPad5T` for the `KECCAK` table, whose floor is `9`): its
`τ_g = kb[2 + t]` below `g^33`, its row count, the `padding_weight` arm `τ` on `(rows, zeta)`,
and `lead = 1 ∧ rest ≠ 0` (at the `KECCAK` table only when `τ ≠ 9`). `vt_pads`: every table's
`τ` is `max (log2Ceil n) floor` for its row count `n`, and its padding weight is `paddingWeight`
at the first `τ` words at `zeta`.
-/

namespace LeanVM.Guest.B1.Tables

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Protocol LeanVM.Protocol.Verifier

@[expose] public section

/-- `padding_weight`'s 33 arms. -/
def vtPadNames : List String := (List.range 33).map (lName "padding_weight")

/-- `g^32`, as the data writes it. -/
abbrev vtW32 : E := word 4294967296 0 0

/-- Table `t`'s height statements, `t < 5`, values from `v`: `τ_g = kb[2 + t]` (variable
`30 + t`) below `g^33`. -/
def vtPadT (v t : ℕ) : List Stmt :=
  [.atom (.const (.n v) vtW32),
    .atom (.rangeCheck (.n (30 + t)) (.n (v + 1)) (.n (v + 2)) (.n (v + 3)) (.n v)),
    .atom (.load (.n (v + 4)) (.n 11) t),
    .dispatch (.n (30 + t)) vtPadNames [.n (v + 4), .n 8] [.n (v + 5), .n (v + 6), .n (v + 7)],
    .atom (.const (.n (v + 8)) (word 1 0 0)), .atom (.assertEq (.n (v + 6)) (.n (v + 8))),
    .atom (.const (.n (v + 9)) (word 0 0 0)), .atom (.add (.n (v + 10)) (.n (v + 7)) (.n (v + 9))),
    .atom (.hint (.inverse (.n (v + 10)) (.n (v + 11)))),
    .atom (.assertNe (.n (v + 10)) (.n (v + 11)) (.n (v + 12)))]

/-- The `KECCAK` table's height statements, values from `v`. -/
def vtPad5T (v : ℕ) : List Stmt :=
  [.atom (.const (.n v) vtW32),
    .atom (.rangeCheck (.n 35) (.n (v + 1)) (.n (v + 2)) (.n (v + 3)) (.n v)),
    .atom (.load (.n (v + 4)) (.n 11) 5),
    .dispatch (.n 35) vtPadNames [.n (v + 4), .n 8] [.n (v + 5), .n (v + 6), .n (v + 7)],
    .atom (.const (.n (v + 8)) vtW32), .atom (.const (.n (v + 9)) (word 512 0 0)),
    .atom (.mul (.n 35) (.n (v + 10)) (.n (v + 9))),
    .atom (.rangeCheck (.n (v + 10)) (.n (v + 11)) (.n (v + 12)) (.n (v + 13)) (.n (v + 8))),
    .atom (.const (.n (v + 14)) (word 512 0 0)), .atom (.add (.n (v + 15)) (.n 35) (.n (v + 14))),
    .ite (.n (v + 15)) [] [.atom (.const (.n (v + 16)) (word 1 0 0)),
      .atom (.assertEq (.n (v + 6)) (.n (v + 16))), .atom (.const (.n (v + 17)) (word 0 0 0)),
      .atom (.add (.n (v + 18)) (.n (v + 7)) (.n (v + 17))),
      .atom (.hint (.inverse (.n (v + 18)) (.n (v + 19)))),
      .atom (.assertNe (.n (v + 18)) (.n (v + 19)) (.n (v + 20)))]]

theorem vtPad_check : ∀ t < 5,
    tbStmtsEqb (vtPadT (582 + 13 * t) t)
      ((vtAt (567 + 10 * t)).take (vtPadT (582 + 13 * t) t).length) = true := by
  decide +kernel

theorem vtPad5_check :
    tbStmtsEqb (vtPad5T 647) ((vtAt 617).take (vtPad5T 647).length) = true := by
  decide +kernel

/-- `kappa_base` in the frame (G:2130-2133): `kb[0] = 1`, `kb[1 + t] = dims_g[t]`. -/
theorem vt_kb {rd : Reader} {σ : Val} (h : VtH rd σ) :
    σ (.n 28) = 1 ∧ ∀ i < 7, LoadHolds rd (σ (.n 10)) i (σ (.n (29 + i))) := by
  have c := h.atomAt 8 (.const (.n 28) (word 1 0 0)) (by decide +kernel)
  have hl : ∀ i < 7, Atom.Holds rd σ (.load (.n (29 + i)) (.n 10) i) := by
    intro i hi
    exact h.atomAt (9 + i) _ (by revert i; decide +kernel)
  refine ⟨by simpa [Atom.Holds, tb_word_one] using c, fun i hi => ?_⟩
  simpa [Atom.Holds] using hl i hi

theorem vtW32_eq : vtW32 = ofK (Parameters.addressOfIndex 32) := by
  rw [vtW32, show (4294967296 : ℕ) = 2 ^ 32 by norm_num, tb_word_two_pow (by norm_num),
    gen_pow_eq_ofK]

/-- Table `t`'s padding weight's value. -/
def vtPadV (t : ℕ) : ℕ := 587 + 13 * t

/-- What table `t`'s height statements give. -/
def VtPadOk (rd : Reader) (σ : Val) (t : ℕ) : Prop :=
  ∃ (τ n : ℕ) (zs : List E), τ < 33 ∧ LoadHolds rd (σ (.n 10)) (t + 1) (gen ^ τ) ∧
    LoadHolds rd (σ (.n 11)) t (eOfNat n) ∧ n ≤ 2 ^ τ ∧ zs.length = τ ∧
    TbReadsAt rd (σ (.n 8)) zs ∧ σ (.n (vtPadV t)) = paddingWeight zs n ∧
    τ = max (log2Ceil n) (tableLogFloors.getD t 0)

/-- The dispatch on `τ_g = g^τ` runs arm `τ`. -/
theorem vt_pad_arm {rd : Reader} {σ : Val} {v : ℕ} {τ : ℕ} (hτ : τ < 33) (hv : σ (.n v) = gen ^ τ)
    {args rets : List V}
    (hd : ∃ (j : ℕ) (h : j < vtPadNames.length), σ (.n v) = ofK (Parameters.addressOfIndex j) ∧
      coreProgram.Rel rd vtPadNames[j] (args.map σ) (rets.map σ)) :
    PadWeightOut τ rd (args.map σ) (rets.map σ) := by
  obtain ⟨j, hj, hjv, hrel⟩ := hd
  have hj33 : j < 33 := by simpa [vtPadNames] using hj
  rw [hv, ← gen_pow_eq_ofK] at hjv
  obtain rfl := gen_pow_inj (by omega) (by omega) hjv
  simp only [vtPadNames, List.getElem_map, List.getElem_range] at hrel
  exact padding_weight_holds τ hτ _ _ _ hrel

section
variable {μ : ℕ} (hμ : μ ≤ 32) (Lm : MemoryImage μ)
include hμ

theorem vt_pad (σ : Val) (h : VtH Lm.read σ) {t : ℕ} (ht : t < 5) : VtPadOk Lm.read σ t := by
  obtain ⟨k, hs⟩ := h.sliceAt _ _ (vtPad_check t ht)
  simp only [vtPadT, Stmt.HoldsList, Stmt.Holds, and_true] at hs
  obtain ⟨c1, rc, l5, hd, c9, q, c10, a11, -, n13⟩ := hs
  simp only [Atom.Holds] at c1 l5 c9 q c10 a11 n13
  have l0 : LoadHolds Lm.read (σ (.n 10)) (t + 1) (σ (.n (30 + t))) := by
    have := (vt_kb h).2 (t + 1) (by omega); rwa [show 29 + (t + 1) = 30 + t by omega] at this
  obtain ⟨τ, hτ, hv⟩ := vt_rc hμ Lm (K := 33) (by omega) (by norm_num) (by rw [c1, vtW32_eq]) rc
  have hp := vt_pad_arm hτ hv hd
  simp only [List.map_cons, List.map_nil, PadWeightOut] at hp
  obtain ⟨n, zs, hn, hrows, hzl, hzs, hpad, hlead, hrest⟩ := hp
  have hlr : pwLead τ n = 1 ∧ pwRest τ n ≠ 0 := by
    refine ⟨?_, fun h0 => ?_⟩
    · rw [pwLead, ← hlead, e_add_eq_zero_iff.mp q, c9, tb_word_one]
    · obtain ⟨e1, e2⟩ := n13
      rw [a11, c10, tb_word_zero, add_zero, hrest, show PadRest τ n = 0 from h0, zero_mul] at e1
      rw [e1] at e2
      exact zero_ne_one e2
  have hlog := (lead_rest_iff (by omega) hn).mp hlr
  refine ⟨τ, n, zs, hτ, by rw [← hv]; exact l0, by rw [← hrows]; exact l5, hn, hzl, hzs,
    by rw [show vtPadV t = 582 + 13 * t + 5 by unfold vtPadV; ring]; exact hpad, ?_⟩
  have hf : tableLogFloors.getD t 0 = 0 := by interval_cases t <;> rfl
  rw [hf, hlog]
  simp

theorem vt_pad5 (σ : Val) (h : VtH Lm.read σ) : VtPadOk Lm.read σ 5 := by
  obtain ⟨k, hs⟩ := h.sliceAt _ _ vtPad5_check
  simp only [vtPad5T, Stmt.HoldsList] at hs
  rw [tb_holds_ite_noRet _ _ _ rfl rfl] at hs
  simp only [Stmt.HoldsList, Stmt.Holds, and_true] at hs
  obtain ⟨c1, rc, l5, hd, c9, c10, m11, rc11, c15, a16, ⟨-, -, hne⟩⟩ := hs
  simp only [Atom.Holds] at c1 l5 c9 c10 m11 c15 a16
  have l0 : LoadHolds Lm.read (σ (.n 10)) 6 (σ (.n 35)) := (vt_kb h).2 6 (by omega)
  obtain ⟨τ, hτ, hv⟩ := vt_rc hμ Lm (K := 33) (by omega) (by norm_num) (by rw [c1, vtW32_eq]) rc
  obtain ⟨d, hd33, hdv⟩ := vt_rc hμ Lm (K := 33) (by omega) (by norm_num) (by rw [c9, vtW32_eq])
    rc11
  have hp := vt_pad_arm hτ hv hd
  simp only [List.map_cons, List.map_nil, PadWeightOut] at hp
  obtain ⟨n, zs, hn, hrows, hzl, hzs, hpad, hlead, hrest⟩ := hp
  rw [show (512 : ℕ) = 2 ^ 9 by norm_num, tb_word_two_pow (by norm_num)] at c10 c15
  have hτ9 : τ = d + 9 := by
    rw [hv, hdv, c10, ← pow_add] at m11
    exact gen_pow_inj (by omega) (by omega) m11
  refine ⟨τ, n, zs, hτ, by rw [← hv]; exact l0, by rw [← hrows]; exact l5, hn, hzl, hzs,
    by rw [show vtPadV 5 = 647 + 5 from rfl]; exact hpad, ?_⟩
  show τ = max (log2Ceil n) 9
  rcases Nat.eq_or_lt_of_le (show 9 ≤ τ by omega) with h9 | h9
  · rw [← h9]
    have := log2Ceil_le_iff.mpr (show n ≤ 2 ^ 9 by rw [h9]; exact hn)
    omega
  · have hne' : σ (.n (647 + 15)) ≠ 0 := by
      rw [a16, hv, c15]
      intro h0
      have := gen_pow_inj (by omega) (by omega) (e_add_eq_zero_iff.mp h0)
      omega
    obtain ⟨c17, q, c18, a19, -, n21⟩ := hne hne'
    simp only [Atom.Holds] at c17 q c18 a19 n21
    have hlr : pwLead τ n = 1 ∧ pwRest τ n ≠ 0 := by
      refine ⟨?_, fun h0 => ?_⟩
      · rw [pwLead, ← hlead, e_add_eq_zero_iff.mp q, c17, tb_word_one]
      · obtain ⟨e1, e2⟩ := n21
        rw [a19, c18, tb_word_zero, add_zero, hrest, show PadRest τ n = 0 from h0, zero_mul] at e1
        rw [e1] at e2
        exact zero_ne_one e2
    have hlog := (lead_rest_iff (by omega) hn).mp hlr
    omega

/-- **The tables' heights** (G:2195-2209). -/
theorem vt_pads (σ : Val) (h : VtH Lm.read σ) : ∀ t < 6, VtPadOk Lm.read σ t := by
  intro t ht
  rcases Nat.lt_or_ge t 5 with h5 | h5
  · exact vt_pad hμ Lm σ h h5
  · obtain rfl : t = 5 := by omega
    exact vt_pad5 hμ Lm σ h

end

end
end LeanVM.Guest.B1.Tables
