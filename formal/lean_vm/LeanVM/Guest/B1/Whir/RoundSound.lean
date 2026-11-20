/-
  LeanVM.Guest.B1.Whir.RoundSound

  `opening_round`'s core IR is `roundBody`, and gives its meaning in every program that finds it.
-/

module

public import LeanVM.Guest.B1.Whir.Round
public import LeanVM.Guest.Pack.P0.Core
import LeanVM.Guest.B1.Common.Vc

namespace LeanVM.Guest.B1.Whir

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

set_option maxRecDepth 100000 in
theorem opening_round_body : (Fn.«opening_round».core).body = roundBody :=
  stmtsEqb_sound (by decide +kernel)

theorem opening_round_params : (Fn.«opening_round».core).params = (List.range 10).map V.n := rfl

/-- **`opening_round`'s core IR gives its meaning**, in every program that finds it, on a memory
image of `2^κ` words, `11 ≤ κ ≤ 32`, whose `tabs` holds the bit windows. -/
theorem opening_round_soundP (P : Program) [Finds P "opening_round" Fn.«opening_round».core]
    (hg : grind_check_SpecP P 7) {κ : ℕ} (hκ : κ ≤ 32) (hw : winTabBits ≤ κ)
    (L : MemoryImage κ) (args rets : List E) (ht : WinTabs L.read (args.getD 7 0))
    (h : P.Rel L.read "opening_round" args rets) : MeaningOpeningRound L.read args rets := by
  revert ht h
  rw [rel_iff_fnSem (Finds.find (P := P) (fn := Fn.«opening_round».core))]
  vc [keccakF_cells, word_zero, word_one, word_dsObserve]
  rintro ht ⟨f0, f1, f2, f3, f4, cur, claim, tabs, gp, cp, rfl, u0, l0, w, l1, c0, l2, c1, l3, n2, l4, hgc, lg,
    lc0, lc1, rfl⟩
  have hs2 : rdS2 [f0, f1, f2, f3, f4] [u0, w, c0, c1] =
      ⟨[f0, f1, f2, f3, f4], [(u0, dsObserve), (w, dsObserve), (c0, dsObserve), (c1, dsObserve)]⟩ := by
    rw [rdS2, absorbAll_four]
  set S1 := permOf [u0, word 0 1, w, word 0 1, c0, word 0 1, c1, word 0 1, f0, f1, f2, f3, f4]
  have hN : (rdS2 [f0, f1, f2, f3, f4] [u0, w, c0, c1]).nonceState n2 =
      permOf [n2, word 0 4, 0, 0, 0, 0, 0, 0, cellsOfState S1 false 8, cellsOfState S1 false 9,
        cellsOfState S1 false 10, cellsOfState S1 false 11, cellsOfState S1 false 12] := by
    rw [hs2]
    simp [Fs.nonceState, Fs.absorb, rateScalars, perm_eq_cells, pendCells, capOf, scalarCells_eq]
    rfl
  have hb : _root_.LeanVM.Parameters.Whir.foldGrindingBits ≠ 0 := by decide
  have G := (hg hκ hw L _ tabs ht []).mp (grindCheckName_seven ▸ hgc)
  obtain ⟨gok, hα, hs3⟩ := grindSqueeze_cells hb n2 _ _ (by rw [hN]) (by rw [hN]) G.2
  refine ⟨u0, w, c0, c1, n2, ?_, ?_⟩
  · intro k hk
    simp only [List.length_cons, List.length_nil] at hk
    interval_cases k
    · exact l0
    · exact l1
    · exact l2
    · exact l3
    · exact l4
  · simp only [rdG2, hα, hs3, hN, Fs.squeeze, capOf, Keccak.challengeOf_cells]
    refine ⟨gok, lg, lc0, lc1, ?_⟩
    simp only [roundClaim, List.cons_append, List.nil_append, Fs.perm, rateOf]
    rw [show (32 : ℕ) = 2 ^ 5 by rfl, word_two_pow (by decide)]
    rfl

end
end LeanVM.Guest.B1.Whir
