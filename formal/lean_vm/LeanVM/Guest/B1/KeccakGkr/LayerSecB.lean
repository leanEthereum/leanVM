/-
  LeanVM.Guest.B1.KeccakGkr.LayerSecB

  `keccak_layer`'s middle sections: the product at `s` (Horner) and the pack rounds' two
  dispatches.
-/

module

public import LeanVM.Guest.B1.KeccakGkr.LayerT
import LeanVM.Guest.ValRef
import LeanVM.Guest.Data.ValNames.«keccak_layer__L»

/-!
# The pack rounds' dispatches

`hornerT_holds`: the Horner chain is `polyEval` of the product at `s`. `packT_holds`: the pack
rounds' two dispatches to `layer_rounds` (`LayerW.hr1`, `hr2`), from the capacity after `s`, the
cursor past the product and the nonce, and the product at `s`, then on `prev_point·step_g^16`,
`point·step_g^16`; the second's capacity copied.
-/

namespace LeanVM.Guest.B1.VerifySub

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

variable {C : CallRel} {rd : Reader} {σ : Val}

/-! ## Horner -/

/-- The value after `j` steps of the chain. -/
def hornerV (a : ℕ → ℕ) (b j : ℕ) : ℕ := if j = 0 then a 46 else b + 2 * j - 1

/-- **Horner**: the chain's last value is the product at `s`. -/
theorem hornerT_holds {a : ℕ → ℕ} {s b : ℕ} {cs : List E} (hl : cs.length = 47)
    (hc : ∀ k < 47, σ (.n (a k)) = cs.getD k 0) {next : Prop} {kret : List E → Prop}
    (h : Stmt.HoldsList C rd σ (hornerT a s b) next kret) :
    σ (.n (b + 91)) = polyEval cs (σ (.n s)) ∧ next := by
  rw [hornerT, holdsList_range_flatten _ _ (fun _ ↦ rfl)] at h
  obtain ⟨hall, hn⟩ := h
  have step : ∀ j ≤ 46, σ (.n (hornerV a b j)) = polyEval (cs.drop (46 - j)) (σ (.n s)) := by
    intro j
    induction j with
    | zero =>
      intro _
      simp only [hornerV, ↓reduceIte]
      rw [hc 46 (by omega), List.drop_eq_getElem_cons (by omega),
        show 46 + 1 = cs.length by omega, List.drop_length]
      simp [polyEval, List.getElem?_eq_getElem (show 46 < cs.length by omega)]
    | succ j ih =>
      intro hj
      have hj' := hall j (by omega)
      simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds, and_true] at hj'
      obtain ⟨e1, e2⟩ := hj'
      have hv : hornerV a b (j + 1) = b + 2 * j + 1 := by simp [hornerV]; omega
      have hp : (if j = 0 then a 46 else b + 2 * j - 1) = hornerV a b j := rfl
      rw [hv, e2, e1, hp, ih (by omega), hc (45 - j) (by omega),
        show 46 - (j + 1) = 45 - j by omega, show 46 - j = 45 - j + 1 by omega,
        List.drop_eq_getElem_cons (i := 45 - j) (show 45 - j < cs.length by omega)]
      simp only [polyEval, List.foldr_cons, List.getD_eq_getElem?_getD,
        List.getElem?_eq_getElem (show 45 - j < cs.length by omega), Option.getD_some]
  have := step 46 le_rfl
  rw [show hornerV a b 46 = b + 91 by simp [hornerV]] at this
  exact ⟨by simpa using this, hn⟩

/-! ## The pack rounds -/

theorem gen48 : word 281474976710656 0 = gen ^ 48 := by
  rw [show (281474976710656 : ℕ) = 2 ^ 48 from rfl]; exact word_two_pow (by decide)

theorem dispatch_getD {fs : List String} {j : ℕ} (h : j < fs.length) : fs[j] = fs.getD j "" := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h, Option.getD_some]

/-- **The pack rounds**: `prev_point` (value `o + 781`), the dispatch on `step_g` from the
capacity after `s` (`o + 539`), the cursor past the product and the nonce and the product at `s`
(`o + 780`), returning from `o + 785`; the dispatch on `rem_g` on those returns, returning from
`o + 798`; the capacity copied from there to `o + 805`. -/
theorem packT_holds {o : ℕ} {next : Prop} {kret : List E → Prop}
    (h : Stmt.HoldsList C rd σ (packT o) next kret) :
    LoadHolds rd (σ (.n (valf% «keccak_layer» "claim"))) 2 (σ (.n (o + 781))) ∧
      (∃ j1 < 2, σ (.n (valf% «keccak_layer» "step_g")) = gen ^ j1 ∧
        C (stepNames.getD j1 "") ((cap5 (o + 539)).map σ ++
          [σ (.n (valf% «keccak_layer» "cursor@1")) * gen ^ 48, σ (.n (o + 780)), σ (.n (o + 781)),
            σ (.n (o + 782)), σ (.n (valf% «keccak_layer» "tabs"))])
          ((List.range 7).map fun k ↦ σ (.n (o + 785 + k)))) ∧
      (∃ j2 < 16, σ (.n (valf% «keccak_layer» "rem_g")) = gen ^ j2 ∧
        C (remNames.getD j2 "") (((List.range 7).map fun k ↦ σ (.n (o + 785 + k))) ++
          [σ (.n (o + 781)) * σ (.n (valf% «keccak_layer» "step_g")) ^ krStep,
            σ (.n (o + 782)) * σ (.n (valf% «keccak_layer» "step_g")) ^ krStep,
            σ (.n (valf% «keccak_layer» "tabs"))])
          ((List.range 7).map fun k ↦ σ (.n (o + 798 + k)))) ∧
      (∀ j < 5, σ (.n (o + 805 + j)) = σ (.n (o + 798 + j))) ∧ next := by
  rw [packT, holdsList_append, holdsList_append, holdsList_map_atoms] at h
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds, List.map_append, List.map_cons,
    List.map_nil, List.map_map] at h
  obtain ⟨lpp, -, e783, e784, ⟨j1, hj1, hx1, hc1⟩, e792, e793, e794, e795, e796, e797,
    ⟨j2, hj2, hx2, hc2⟩, hcopy, -, hn⟩ := h
  have h16 : σ (.n (o + 795)) = σ (.n (valf% «keccak_layer» "step_g")) ^ krStep := by
    rw [e795, e794, e793, e792]; simp only [krStep]; ring
  refine ⟨lpp, ⟨j1, hj1, by rw [gen_pow_eq_ofK]; exact hx1, ?_⟩,
    ⟨j2, hj2, by rw [gen_pow_eq_ofK]; exact hx2, ?_⟩, hcopy, hn⟩
  · rw [← dispatch_getD hj1, ← gen48, ← e783, ← e784]
    exact hc1
  · rw [← dispatch_getD hj2, ← h16, ← e796, ← e797]
    exact hc2

end
end LeanVM.Guest.B1.VerifySub
