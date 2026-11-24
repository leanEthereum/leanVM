/-
  LeanVM.Guest.B1.Whir.RoundComplete

  A fold round's honest sponge values, for the inline round's completeness.
-/

module

public import LeanVM.Guest.B1.Whir.RoundSound

/-!
# A fold round, honestly

The honest values of a fold round on its arguments and the five words at the cursor, value by
value (the sponge's three permutations `rdS1`, `rdS3`, `rdS4`).
-/

namespace LeanVM.Guest.B1.Whir

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

/-! ## The honest values -/

/-- Cell `i` of a state. -/
def rdCell (S : KeccakState) (i : ℕ) : E := cellsOfState S false ⟨i % 13, Nat.mod_lt _ (by omega)⟩

/-- The four scalars' permutation. -/
def rdS1 (as xs : List E) : KeccakState :=
  (⟨as.take 5, [(xs.getD 0 0, dsObserve), (xs.getD 1 0, dsObserve), (xs.getD 2 0, dsObserve),
    (xs.getD 3 0, dsObserve)]⟩ : Fs).perm

/-- The nonce's permutation. -/
def rdS3 (as xs : List E) : KeccakState :=
  (⟨capOf (rdS1 as xs), [(xs.getD 4 0, dsPowNonce)]⟩ : Fs).perm

/-- `β`'s permutation. -/
def rdS4 (as xs : List E) : KeccakState := (⟨capOf (rdS3 as xs), []⟩ : Fs).perm

/-- The arithmetic tail's values, from `74`. -/
def rdTail (as xs : List E) : List E :=
  let al := rdCell (rdS3 as xs) 0
  let be := rdCell (rdS4 as xs) 0
  let u0 := xs.getD 0 0
  let w := xs.getD 1 0
  let c0 := xs.getD 2 0
  let c1 := xs.getD 3 0
  let claim := as.getD 6 0
  let a := u0 + claim + al * w + be * (c0 + c1)
  [be * c0, u0 + be * c0, u0 + claim, al * w, u0 + claim + al * w, c0 + c1, be * (c0 + c1), a,
    al * a, u0 + be * c0 + al * a,
    rdCell (rdS4 as xs) 8, rdCell (rdS4 as xs) 9, rdCell (rdS4 as xs) 10, rdCell (rdS4 as xs) 11,
    rdCell (rdS4 as xs) 12, word 32 0, as.getD 5 0 * word 32 0, as.getD 5 0 * word 32 0,
    u0 + be * c0 + al * a]

/-! ## The meaning's sponges -/

theorem rdCell_eq (S : KeccakState) (c : Fin 13) : rdCell S c.val = cellsOfState S false c := by
  unfold rdCell
  congr 1
  exact Fin.ext (Nat.mod_eq_of_lt c.isLt)

/-- The meaning's sponges are the honest permutations. -/
theorem rd_sponges (f0 f1 f2 f3 f4 cur claim tabs gp cp u0 w c0 c1 n2 : E) :
    let as := [f0, f1, f2, f3, f4, cur, claim, tabs, gp, cp]
    let xs := [u0, w, c0, c1, n2]
    let fs := [f0, f1, f2, f3, f4]
    let m := [u0, w, c0, c1]
    (rdS2 fs m).nonceState n2 = rdS3 as xs ∧
      rdG2 fs m n2 = (challengeOf (rdS3 as xs), ⟨capOf (rdS3 as xs), []⟩) ∧
      (rdG2 fs m n2).2.squeeze = (challengeOf (rdS4 as xs), ⟨capOf (rdS4 as xs), []⟩) := by
  intro as xs fs m
  have hb : _root_.LeanVM.Parameters.Whir.foldGrindingBits ≠ 0 := by decide
  have es : rdS2 fs m = ⟨fs, [(u0, dsObserve), (w, dsObserve), (c0, dsObserve), (c1, dsObserve)]⟩ := by
    rw [rdS2, absorbAll_four]
  have en : (rdS2 fs m).nonceState n2 = rdS3 as xs := by
    rw [es]; simp [Fs.nonceState, Fs.absorb, rateScalars, rdS3, rdS1, xs, as, fs]
  have e2 : rdG2 fs m n2 = (challengeOf (rdS3 as xs), ⟨capOf (rdS3 as xs), []⟩) := by
    rw [rdG2, Fs.grindSqueeze_pos _ hb, en]
  refine ⟨en, e2, ?_⟩
  rw [e2]; rfl

end
end LeanVM.Guest.B1.Whir
