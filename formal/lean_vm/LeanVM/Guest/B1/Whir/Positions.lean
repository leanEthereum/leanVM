/-
  LeanVM.Guest.B1.Whir.Positions

  The Spec's query positions (`sampleQueries`) from the challenges of the squeezes they take.
-/

module

public import LeanVM.Guest.B1.Whir.Run

/-!
# Query positions (V:1670-1682)

`sampleQueriesAux depth fuel count` squeezes a challenge, takes up to `per = 192 / depth`
positions of `depth` bits from it, low bits first, and recurs on the rest. `queriesOf per d ws q`
is the `q` positions the challenges `ws` give, position `k` from challenge `k / per` at bit
`(k % per)·d`; `sampleQueriesAux_run`: from a sponge with nothing waiting, `sampleQueriesAux`
squeezes `ceilDiv count per` challenges and returns `queriesOf` of them, when the fuel is at least
that.
-/

namespace LeanVM.Guest.B1.Whir

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

/-- `⌈a / b⌉`. -/
def ceilDiv (a b : ℕ) : ℕ := (a + b - 1) / b

/-- The `q` positions of `d` bits the challenges `ws` give, `per` from each. -/
def queriesOf (per d : ℕ) (ws : List E) (q : ℕ) : List ℕ :=
  (List.range q).map fun k ↦ (eToNat (ws.getD (k / per) 0) >>> ((k % per) * d)) % 2 ^ d

theorem ceilDiv_zero (b : ℕ) : ceilDiv 0 b = 0 := by
  unfold ceilDiv; rcases b with _ | b <;> simp

theorem ceilDiv_step {a b : ℕ} (hb : 1 ≤ b) (ha : 0 < a) :
    ceilDiv a b = ceilDiv (a - min b a) b + 1 := by
  unfold ceilDiv
  rcases Nat.lt_or_ge b a with h | h
  · rw [min_eq_left h.le]
    have e : a + b - 1 = (a - b + b - 1) + b := by omega
    rw [e, Nat.add_div_right _ (by omega : 0 < b)]
  · rw [min_eq_right h, Nat.sub_self, Nat.zero_add]
    have e1 : (a + b - 1) / b = 1 := Nat.div_eq_of_lt_le (by omega) (by omega)
    have e2 : (b - 1) / b = 0 := Nat.div_eq_of_lt (by omega)
    rw [e1, e2]

theorem queriesOf_cons (per d : ℕ) (hper : 1 ≤ per) (w : E) (ws : List E) (q : ℕ) :
    ((List.range (min per q)).map fun c ↦ (eToNat w >>> (c * d)) % 2 ^ d) ++
        queriesOf per d ws (q - min per q) = queriesOf per d (w :: ws) q := by
  unfold queriesOf
  apply List.ext_getElem
  · simp only [List.length_append, List.length_map, List.length_range]; omega
  · intro k h1 h2
    simp only [List.length_map, List.length_range] at h2
    rw [List.getElem_map, List.getElem_range]
    rcases Nat.lt_or_ge k (min per q) with hk | hk
    · rw [List.getElem_append_left (by simpa using hk), List.getElem_map, List.getElem_range]
      have h1 : k / per = 0 := Nat.div_eq_of_lt (by omega)
      have h2 : k % per = k := Nat.mod_eq_of_lt (by omega)
      rw [h1, h2]
      rfl
    · rw [List.getElem_append_right (by simpa using hk), List.getElem_map, List.getElem_range]
      simp only [List.length_map, List.length_range]
      have hmin : min per q = per := by
        rcases Nat.lt_or_ge per q with h | h
        · exact min_eq_left h.le
        · omega
      rw [hmin] at hk ⊢
      obtain ⟨j, rfl⟩ : ∃ j, k = per + j := ⟨k - per, by omega⟩
      rw [Nat.add_sub_cancel_left, Nat.add_div_left _ (by omega), Nat.add_mod_left]
      rfl

/-- **The query positions** from a sponge with nothing waiting. -/
theorem sampleQueriesAux_run (d : ℕ) (hd : 1 ≤ 192 / d) :
    ∀ (fuel rem : ℕ) (F : Fs), ceilDiv rem (192 / d) ≤ fuel →
      RunsTo (sampleQueriesAux d fuel rem) F []
        (queriesOf (192 / d) d (F.squeezeN (ceilDiv rem (192 / d))).1 rem)
        (F.squeezeN (ceilDiv rem (192 / d))).2
  | fuel, 0, F, _ => by
    rw [ceilDiv_zero]
    rcases fuel with _ | fuel <;> exact runsTo_ret _ _
  | 0, rem + 1, F, h => by
    have := ceilDiv_step (a := rem + 1) hd (Nat.succ_pos rem); omega
  | fuel + 1, rem + 1, F, h => by
    have hs := ceilDiv_step (a := rem + 1) hd (Nat.succ_pos rem)
    have ih := sampleQueriesAux_run d hd fuel (rem + 1 - min (192 / d) (rem + 1)) F.squeeze.2
      (by omega)
    have h1 := runsTo_sampleE F
    have := h1.bind (f := fun w ↦ do
        let rest ← sampleQueriesAux d fuel (rem + 1 - min (192 / d) (rem + 1))
        return ((List.range (min (192 / d) (rem + 1))).map fun c ↦
          (eToNat w >>> (c * d)) % 2 ^ d) ++ rest)
      (ih.bind (f := fun rest ↦ (pure (((List.range (min (192 / d) (rem + 1))).map fun c ↦
          (eToNat F.squeeze.1 >>> (c * d)) % 2 ^ d) ++ rest) : VerifierProgram (List ℕ)))
        (runsTo_ret _ _))
    have hp : sampleQueriesAux d (fuel + 1) (rem + 1) = (do
        let w ← VerifierProgram.sampleChallenge
        let rest ← sampleQueriesAux d fuel (rem + 1 - min (192 / d) (rem + 1))
        return ((List.range (min (192 / d) (rem + 1))).map fun c ↦
          (eToNat w >>> (c * d)) % 2 ^ d) ++ rest) := by
      simp only [sampleQueriesAux, Nat.add_one_ne_zero, ↓reduceIte]
    rw [hp, hs]
    refine RunsTo.of_eq this rfl rfl ?_ rfl
    exact queriesOf_cons _ _ hd _ _ _

end
end LeanVM.Guest.B1.Whir
