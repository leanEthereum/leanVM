/-
  LeanVM.Guest.B1.Opening.QueriesPlaced6

  What an iteration of `opening_queries`' loop needs.
-/

module

public import LeanVM.Guest.B1.Opening.QueriesPlaced5
import LeanVM.Guest.Value.FieldBits

/-!
# An iteration's data

`OqIt1Ok`, `OqIt0Ok`: what iteration `j` of the loop needs: its queries' `QD.Ok` (their windows,
cap leaves and flags), their points and window pointers, the chain's words, the region it reads.
`gen_pow_guard`: the loop's guard `g^(j+1) + g^N` is in `K`, nonzero exactly before the last
iteration.
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Memory
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

/-- **What a level-0 iteration at `g^j` needs**: its two queries honest with their windows, their
points and window pointers, the chain's step (non-final levels), and where it reads the caller's
words. -/
structure OqIt1Ok (rd : Reader) (R : ℕ → Prop) (s : Oq) (cd j : ℕ)
    (positions qptrs cap flags coefs hsp ch mu : E) (rounds : List FoldRound) (hsv : List E)
    (w1 w2 : QW) (bp1 bp2 v : E) : Prop where
  ok1 : (oqQD s cd 15 true 0 bp1 cap flags rounds hsv w1).Ok rd coefs hsp
  ok2 : (oqQD s cd (oqE1 s + 2) false (oqK1 s 15) bp2 cap flags rounds hsv w2).Ok rd coefs hsp
  x1 : LoadHolds rd positions (2 * j) (eOfNat w1.1)
  x2 : LoadHolds rd positions (2 * j + 1) (eOfNat w2.1)
  b1 : LoadHolds rd qptrs (2 * j) bp1
  b2 : LoadHolds rd qptrs (2 * j + 1) bp2
  chv : s.final ≠ 1 → LoadHolds rd ch j v ∧
    LoadHolds rd ch (j + 1) (((v + oqResV s rounds w1) * mu + oqResV s rounds w2) * mu)
  rp : ∀ e < 2, OqIn R ((positions * gen ^ (2 * j)).limb 0 * Parameters.addressOfIndex e)
  rq : ∀ e < 2, OqIn R ((qptrs * gen ^ (2 * j)).limb 0 * Parameters.addressOfIndex e)
  reg1 : OqQReg R s cap flags coefs hsp bp1 w1.1
  reg2 : OqQReg R s cap flags coefs hsp bp2 w2.1
  rc : s.final ≠ 1 → ∀ e < 2, OqIn R ((ch * gen ^ j).limb 0 * Parameters.addressOfIndex e)

/-- **What a deeper iteration at `g^j` needs.** -/
structure OqIt0Ok (rd : Reader) (R : ℕ → Prop) (s : Oq) (cd j : ℕ)
    (positions qptrs cap flags coefs hsp ch mu : E) (rounds : List FoldRound) (hsv : List E)
    (w : QW) (bp v : E) : Prop where
  ok : (oqQD s cd 14 true 0 bp cap flags rounds hsv w).Ok rd coefs hsp
  x : LoadHolds rd positions j (eOfNat w.1)
  b : LoadHolds rd qptrs j bp
  chv : s.final ≠ 1 → LoadHolds rd ch j v ∧ LoadHolds rd ch (j + 1) ((v + oqResV s rounds w) * mu)
  rp : OqIn R ((positions * gen ^ j).limb 0 * Parameters.addressOfIndex 0)
  rq : OqIn R ((qptrs * gen ^ j).limb 0 * Parameters.addressOfIndex 0)
  reg : OqQReg R s cap flags coefs hsp bp w.1
  rc : s.final ≠ 1 → ∀ e < 2, OqIn R ((ch * gen ^ j).limb 0 * Parameters.addressOfIndex e)

theorem gen_pow_guard {j N : ℕ} (hN : N < ordG) (hj : j + 1 ≤ N) :
    IsInK (gen ^ j * gen + gen ^ N) ∧ (gen ^ j * gen + gen ^ N ≠ 0 ↔ j + 1 < N) := by
  rw [← pow_succ]
  refine ⟨isInK_add (by rw [gen_pow_eq_ofK]; exact ofK_isInK _)
    (by rw [gen_pow_eq_ofK]; exact ofK_isInK _), ⟨fun h ↦ ?_, fun h he ↦ ?_⟩⟩
  · rcases Nat.lt_or_ge (j + 1) N with h' | h'
    · exact h'
    · exact absurd (by rw [show j + 1 = N by omega]; exact e_add_self _) h
  · have := gen_pow_inj (lt_of_lt_of_le (by omega) (le_of_lt hN)) hN (e_add_eq_zero_iff.mp he)
    omega

end
end LeanVM.Guest.B1
