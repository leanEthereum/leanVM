/-
  LeanVM.Guest.B1.Tables.VerifyTablesPad

  `verify_tables`'s padding weights: each table's log-height is range-checked, certified the
  least holding its rows, and its padding weight dispatched on it.
-/

module

public import LeanVM.Guest.B1.Tables.VerifyTablesSort

/-!
# The tables' padding weights (G:1546-1557)

For each table `t`, `verify_tables` range-checks `dims_g[t + 1] = g^τ`, `τ < 29`, dispatches
`padding_weight__L{τ}` on `table_rows[t]`, and asserts `lead = 1`, `rest ≠ 0`: the rows are some
`n ≤ 2^τ` with `log2Ceil n = τ` (`lead_rest_iff`), and the weight is `paddingWeight` over the
point's first `τ` coordinates (`vt_pads`).
-/

namespace LeanVM.Guest.B1.VerifySub

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.Blake2sHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

/-- `padding_weight`'s 29 specializations, in dispatch order. -/
def pwNames : List String :=
  ["padding_weight__L0", "padding_weight__L1", "padding_weight__L2", "padding_weight__L3", "padding_weight__L4", "padding_weight__L5", "padding_weight__L6", "padding_weight__L7", "padding_weight__L8", "padding_weight__L9", "padding_weight__L10", "padding_weight__L11", "padding_weight__L12", "padding_weight__L13", "padding_weight__L14", "padding_weight__L15", "padding_weight__L16", "padding_weight__L17", "padding_weight__L18", "padding_weight__L19", "padding_weight__L20", "padding_weight__L21", "padding_weight__L22", "padding_weight__L23", "padding_weight__L24", "padding_weight__L25", "padding_weight__L26", "padding_weight__L27", "padding_weight__L28"]

/-- A dispatched `padding_weight` arm is sound. -/
theorem pw_dispatch {rd : Reader} {rows zeta : E} {rets : List E} :
    ∀ (j : ℕ) (hj : j < pwNames.length),
      coreProgram.Rel rd (pwNames[j]'hj) [rows, zeta] rets →
        MeaningPaddingWeight j rd [rows, zeta] rets
  | 0, _, h => (padding_weight_L0_iff rd rows zeta rets).mp h
  | 1, _, h => (padding_weight_L1_iff rd rows zeta rets).mp h
  | 2, _, h => (padding_weight_L2_iff rd rows zeta rets).mp h
  | 3, _, h => (padding_weight_L3_iff rd rows zeta rets).mp h
  | 4, _, h => (padding_weight_L4_iff rd rows zeta rets).mp h
  | 5, _, h => (padding_weight_L5_iff rd rows zeta rets).mp h
  | 6, _, h => (padding_weight_L6_iff rd rows zeta rets).mp h
  | 7, _, h => (padding_weight_L7_iff rd rows zeta rets).mp h
  | 8, _, h => (padding_weight_L8_iff rd rows zeta rets).mp h
  | 9, _, h => (padding_weight_L9_iff rd rows zeta rets).mp h
  | 10, _, h => (padding_weight_L10_iff rd rows zeta rets).mp h
  | 11, _, h => (padding_weight_L11_iff rd rows zeta rets).mp h
  | 12, _, h => (padding_weight_L12_iff rd rows zeta rets).mp h
  | 13, _, h => (padding_weight_L13_iff rd rows zeta rets).mp h
  | 14, _, h => (padding_weight_L14_iff rd rows zeta rets).mp h
  | 15, _, h => (padding_weight_L15_iff rd rows zeta rets).mp h
  | 16, _, h => (padding_weight_L16_iff rd rows zeta rets).mp h
  | 17, _, h => (padding_weight_L17_iff rd rows zeta rets).mp h
  | 18, _, h => (padding_weight_L18_iff rd rows zeta rets).mp h
  | 19, _, h => (padding_weight_L19_iff rd rows zeta rets).mp h
  | 20, _, h => (padding_weight_L20_iff rd rows zeta rets).mp h
  | 21, _, h => (padding_weight_L21_iff rd rows zeta rets).mp h
  | 22, _, h => (padding_weight_L22_iff rd rows zeta rets).mp h
  | 23, _, h => (padding_weight_L23_iff rd rows zeta rets).mp h
  | 24, _, h => (padding_weight_L24_iff rd rows zeta rets).mp h
  | 25, _, h => (padding_weight_L25_iff rd rows zeta rets).mp h
  | 26, _, h => (padding_weight_L26_iff rd rows zeta rets).mp h
  | 27, _, h => (padding_weight_L27_iff rd rows zeta rets).mp h
  | 28, _, h => (padding_weight_L28_iff rd rows zeta rets).mp h
  | _ + 29, hj, _ => absurd hj (by simp [pwNames])

/-- `g^28`, the range check `log(tau_g) < N_COLUMN_LOGS`. -/
theorem word_g28 : word 268435456 0 0 = ofK (Parameters.gpow 28) := by
  rw [show (268435456 : ℕ) = 2 ^ 28 by norm_num, word_two_pow (by decide), gen_pow_eq_ofK]

/-- Table `t`'s padding weight, from value `1733 + 14·t` (G:1550-1557). -/
def vtPad (t : ℕ) : List Stmt :=
  let v := 1733 + 14 * t
  [.atom (.load (.n v) (.n 7) (t + 1)), .atom (.const (.n (v + 1)) (word 268435456 0 0)),
    .atom (.rangeCheck (.n v) (.n (v + 2)) (.n (v + 3)) (.n (v + 4)) (.n (v + 1))),
    .atom (.load (.n (v + 5)) (.n 8) t),
    .dispatch (.n v) pwNames [.n (v + 5), .n 5] [.n (v + 6), .n (v + 7), .n (v + 8)],
    .atom (.const (.n (v + 9)) (word 1 0 0)), .atom (.assertEq (.n (v + 7)) (.n (v + 9))),
    .atom (.const (.n (v + 10)) (word 0 0 0)), .atom (.add (.n (v + 11)) (.n (v + 8)) (.n (v + 10))),
    .atom (.hint (.inverse (.n (v + 11)) (.n (v + 12)))),
    .atom (.assertNe (.n (v + 11)) (.n (v + 12)) (.n (v + 13)))]

theorem vt_pad_blocks : ∀ t < 6, stmtsEqb (vtPad t) ((vtPre.drop (1439 + 11 * t)).take 11) = true := by
  decide +kernel

/-- **The tables' heights and padding weights** (G:1546-1557): table `t`'s rows are `n ≤ 2^τ`
with `log2Ceil n = τ < 29`, `dims_g[t + 1] = g^τ`, and, once the point has `τ` coordinates, its
padding weight is `paddingWeight` over them. -/
theorem vt_pads {κ : ℕ} (hκ : κ ≤ 32) (Lm : MemImage κ) {σ : Val} (h : VtHolds Lm.read σ)
    {point : List E} (hz : ReadsAt Lm.read (σ (.n 5)) point) :
    ∀ t < 6, ∃ τ n : ℕ, τ < 29 ∧ n ≤ 2 ^ τ ∧ log2Ceil n = τ ∧ σ (.n (1733 + 14 * t)) = gen ^ τ ∧
      LoadHolds Lm.read (σ (.n 7)) (t + 1) (gen ^ τ) ∧
      LoadHolds Lm.read (σ (.n 8)) t (eOfNat n) ∧
      (τ ≤ point.length → σ (.n (1739 + 14 * t)) = paddingWeight (point.take τ) n) := by
  intro t ht
  obtain ⟨k, hb⟩ := h.slice _ _ (vt_pad_blocks t ht)
  simp only [vtPad, Stmt.HoldsList, Stmt.Holds, Atom.Holds, and_true, true_and, word_one,
    word_zero, List.map_cons, List.map_nil] at hb
  obtain ⟨l0, c1, ⟨r0, r1, r2⟩, l5, ⟨j, hj, hjx, hrel⟩, c9, ae, c10, a11, ⟨m13, e13⟩⟩ := hb
  obtain ⟨τ, hτ, hgτ⟩ := rc_sound' hκ Lm (K := 29) (by omega) (by decide)
    (by rw [c1]; exact word_g28) r0 r1 r2
  have hj29 : j < 29 := by simpa [pwNames] using hj
  have hjτ : j = τ := by
    rw [hgτ, gen_pow_eq_ofK] at hjx
    exact (gpow_injOn (by simp only [Set.mem_Iio]; omega)
      (by simp only [Set.mem_Iio]; omega) (ofK_injective hjx)).symm
  subst hjτ
  obtain ⟨n, zs, hn, hrows, hzl, hzs, hret⟩ := pw_dispatch j hj hrel
  simp only [List.cons.injEq, and_true] at hret
  obtain ⟨e6, e7, e8⟩ := hret
  have hlead : pwLead j n = 1 := by rw [← e7, ← c9]; exact e_add_eq_zero_iff.mp ae
  have hrest : pwRest j n ≠ 0 := by
    intro h0
    rw [a11, c10, add_zero, e8, h0, zero_mul] at m13
    exact zero_ne_one (m13.symm.trans e13)
  refine ⟨j, n, hτ, hn, (lead_rest_iff (by omega) hn).mp ⟨hlead, hrest⟩, hgτ,
    by rw [← hgτ]; exact l0, by rw [← hrows]; exact l5, fun hle => ?_⟩
  have hzs' : zs = point.take j := by
    apply List.ext_getElem (by simp [hzl]; omega)
    intro k h1 h2
    have hk : k < point.length := by simp at h2; omega
    rw [List.getElem_take]
    exact loadHolds_unique (hzs k h1) (hz k hk)
  rw [show 1739 + 14 * t = 1733 + 14 * t + 6 by ring, e6, hzs']

end
end LeanVM.Guest.B1.VerifySub
