/-
  LeanVM.Guest.B1.KeccakGkr.LayerSecB

  `keccak_layer`'s middle sections (G:2695-2762): the product at `s` (Horner), the pack rounds'
  first record and their two loops, and the last record read.
-/

module

public import LeanVM.Guest.B1.KeccakGkr.LayerT

/-!
# The pack rounds' records

`hornerT_holds`: the Horner chain is `polyEval` of the product at `s` (V:1998). `packSetupT_holds`:
the first record (`RoundRec`, the capacity after `s`, the cursor past the product and the nonce, the product at
`s`, the scale `1`), the two loops' calls (`LayerW.h0`, `hloop`, `hrem`). `lastT_holds`: the
record `rounds·step_g·rem_g` read.
-/

namespace LeanVM.Guest.B1.VerifySub

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

variable {C : CallRel} {rd : Reader} {σ : Val}

/-! ## Horner -/

/-- The value after `j` steps of the chain. -/
def hornerV (a : ℕ → ℕ) (b j : ℕ) : ℕ := if j = 0 then a 46 else b + 2 * j - 1

/-- **Horner** (G:2695-2697): the chain's last value is the product at `s`. -/
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

/-! ## The pack rounds' setup -/

theorem gen48 : word 281474976710656 0 = gen ^ 48 := by
  rw [show (281474976710656 : ℕ) = 2 ^ 48 from rfl]; exact word_two_pow (by decide)

/-- **The pack rounds' setup** (G:2699-2739): the first record at `rounds` (value `o + 720`), the
eight-round loop's call, and the remainder loop's on `rounds·step_g`, `prev_point·step_g⁸`,
`point·step_g⁸`, both passed `tabs`. -/
theorem packSetupT_holds {o first : ℕ} {next : Prop} {kret : List E → Prop}
    (h : Stmt.HoldsList C rd σ (packSetupT o first) next kret) :
    LoadHolds rd (σ (.n 11)) 2 (σ (.n (o + 718))) ∧
      RoundRec rd (σ (.n (o + 720))) 0 ((cap5 (o + 539)).map σ) (σ (.n 7) * gen ^ 48)
        (σ (.n (o + 717))) 1 ∧
      IsInK (1 + σ (.n 9)) ∧
      (1 + σ (.n 9) ≠ 0 → C (packLoopName first)
        [1, σ (.n 9), σ (.n (o + 720)), σ (.n (o + 718)), σ (.n (o + 719)), σ (.n 14)] []) ∧
      σ (.n (o + 727)) = σ (.n (o + 720)) * σ (.n 9) ∧ IsInK (1 + σ (.n 10)) ∧
      (1 + σ (.n 10) ≠ 0 →
        C (remLoopName first) [1, σ (.n 10), σ (.n (o + 720)) * σ (.n 9),
          σ (.n (o + 718)) * σ (.n 9) ^ 8, σ (.n 14), σ (.n (o + 719)) * σ (.n 9) ^ 8] []) ∧
      next := by
  simp only [packSetupT, Stmt.HoldsList, Stmt.Holds, Atom.Holds, List.map_cons, List.map_nil] at h
  obtain ⟨lpp, -, -, c0, c1, c2, c3, c4, e21, e22, lcur, lclaim, e23, lsc, e24, e25, e26,
    hik, hcall, e27, e28, e29, e30, e31, e32, e33, e34, e35, e36, e37, e38, hik', hcall', hn⟩ := h
  have e25' : σ (.n (o + 725)) = 1 + σ (.n 9) := by rw [e25, e24, word_one]
  have e37' : σ (.n (o + 737)) = 1 + σ (.n 10) := by rw [e37, e36, word_one]
  have hrec : RoundRec rd (σ (.n (o + 720))) 0 ((cap5 (o + 539)).map σ) (σ (.n 7) * gen ^ 48)
      (σ (.n (o + 717))) 1 := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · simp only [cap5, List.map_cons, List.map_nil]
      exact capAt_five c0 c1 c2 c3 c4
    · rw [e22, e21, gen48] at lcur
      exact lcur
    · exact lclaim
    · rw [e23, word_one] at lsc
      exact lsc
  have h8 : σ (.n (o + 730)) = σ (.n 9) ^ 8 := by rw [e30, e29, e28]; ring
  have h8' : σ (.n (o + 734)) = σ (.n 9) ^ 8 := by rw [e34, e33, e32]; ring
  refine ⟨lpp, hrec, e25' ▸ hik, fun hne ↦ ?_, e27, e37' ▸ hik', fun hne ↦ ?_, hn⟩
  · have := hcall (by rw [e25']; exact hne)
    rwa [e26, word_one] at this
  · have := hcall' (by rw [e37']; exact hne)
    rwa [e38, word_one, e27, e31, h8, e35, h8'] at this

/-- **The last record** (G:2758-2762): `rounds·step_g·rem_g` (value `o + 739`) and its capacity,
cursor, claim and scale. -/
theorem lastT_holds {o : ℕ} {next : Prop} {kret : List E → Prop}
    (h : Stmt.HoldsList C rd σ (lastT o) next kret) :
    σ (.n (o + 739)) = σ (.n (o + 727)) * σ (.n 10) ∧
      RoundRec rd (σ (.n (o + 739))) 0 ((cap5 (o + 740)).map σ) (σ (.n (o + 745)))
        (σ (.n (o + 746))) (σ (.n (o + 747))) ∧ next := by
  rw [lastT, holdsList_append, holdsList_append, holdsList_map_atoms] at h
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at h
  obtain ⟨e, ⟨hc, -, hn⟩⟩ := h
  refine ⟨e, ⟨?_, hc 5 (by omega), hc 6 (by omega), hc 7 (by omega)⟩, hn⟩
  simp only [cap5, List.map_cons, List.map_nil]
  exact capAt_five (hc 0 (by omega)) (hc 1 (by omega)) (hc 2 (by omega)) (hc 3 (by omega))
    (hc 4 (by omega))

end
end LeanVM.Guest.B1.VerifySub
