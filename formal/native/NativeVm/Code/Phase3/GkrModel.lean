module

public import NativeVm.Code.Refine
public import NativeVm.Code.Gadgets
public import NativeVm.Equiv.Field
public import NativeVm.Model.Gkr
public import NativeVm.Field.Arrays

/-!
# The GKR walk's model, as the code runs it

Pure facts about `Model.gkrStep`, `Model.gkrLayers` and the equality-mode `sumcheck` for the code
of `NativeVm.Code.Phase3.Gkr`: every grind of the walk is of `0` bits (`grindingBits_le`); the walk's
next step from a remaining depth `rem > 0` is of `gkrStepOf rem` coordinates (`gkrLayers_pos`); a
step is `gkrStepM`, its grinds dropped, in parts (`childM`, `gkrStep_eq`); a sumcheck round's runs
(`roundF_run`); the walk's runs from its first two reads (`verifyGkr_run`); the sum and the product
as the field kernels compute them, against ones (`dot_ones`, `eqEval_ones`).
-/

@[expose] public section

namespace NativeVm.Code.P3

open Native NativeVm.Model NativeVm.Code LeanVM.Parameters

/-! ## Grinds -/

theorem grindingBits_le {k : Nat} (hk : k ≤ 8) : grindingBits k = 0 := by
  unfold grindingBits LeanVM.Protocol.Compile.grindingBits
  split
  · rfl
  · have : Nat.log2 (k - 1) < 3 := (Nat.log2_lt (by omega)).mpr (by
      show k - 1 < 8
      omega)
    unfold LeanVM.Protocol.Compile.securityBits
    omega

theorem grind_le_run {k : Nat} (hk : k ≤ 8) (t : TState) : (Model.grind (grindingBits k)).run t = some ((), t) := by
  rw [grindingBits_le hk]
  rfl

/-! ## The walk's steps -/

/-- The coordinates of the walk's next step from the remaining depth `rem`. -/
def gkrStepOf (rem : Nat) : Nat := if rem % 2 = 1 then 1 else 2

theorem gkrStepOf_le {rem : Nat} (h : 0 < rem) : gkrStepOf rem ≤ rem := by
  unfold gkrStepOf
  split <;> omega

theorem gkrStepOf_cases (rem : Nat) : gkrStepOf rem = 1 ∨ gkrStepOf rem = 2 := by
  unfold gkrStepOf
  split <;> simp

theorem gkrLayers_pos {rem : Nat} (h : 0 < rem) (st : GkrStateW) :
    gkrLayers rem st = gkrStep (gkrStepOf rem) (decide (rem = gkrStepOf rem)) st >>=
      gkrLayers (rem - gkrStepOf rem) := by
  match rem, h with
  | 1, _ => rw [gkrLayers]; rfl
  | n + 2, _ =>
    rw [gkrLayers]
    unfold gkrStepOf
    by_cases hn : n % 2 = 1
    · have h1 : (n + 2) % 2 = 1 := by omega
      have h2 : decide (n + 2 = 1) = false := by simp
      simp only [hn, h1, h2, ↓reduceIte]
      rfl
    · have h1 : ¬ (n + 2) % 2 = 1 := by omega
      have h2 : decide (n + 2 = 2) = decide (n = 0) := by simp
      simp only [hn, h1, h2, ↓reduceIte]
      rfl

/-! ## A sumcheck round -/

/-- The step of the equality-mode `sumcheck`'s fold. -/
def roundF (count : Nat) (acc : Array EW × EW) (equality : Option EW) : VM (Array EW × EW) := do
  let message ← sumcheckRoundPoly count acc.2 equality
  let challenge ← sampleChallenge
  pure (acc.1.push challenge, polyEval message challenge)

theorem sumcheck_eq (claim : EW) (count : Nat) (eqs : Array (Option EW)) :
    sumcheck claim count eqs = eqs.toList.foldlM (roundF count) (#[], claim) := by
  rw [sumcheck, Array.foldlM_toList]
  rfl

variable {t t₁ t₂ : TState}

theorem roundF_run {n : Nat} (hn : n ≤ 7) {acc : Array EW × EW} {e : EW} {xs : Array EW} {c : EW}
    (h1 : (readScalars n).run t = some (xs, t₁)) (h2 : Model.sampleChallenge.run t₁ = some (c, t₂)) :
    (roundF (n + 1) acc (some e)).run t =
      some ((acc.1.push c, polyEval (#[acc.2 + e * sumE xs] ++ xs) c), t₂) := by
  unfold roundF sumcheckRoundPoly
  simp only [Nat.add_sub_cancel, bind_assoc]
  rw [Refines.run_bind_some h1, Refines.run_bind_some (grind_le_run (by omega) t₁), pure_bind,
    Refines.run_bind_some h2]
  rfl

theorem roundF_none {n : Nat} {acc : Array EW × EW} {e : EW}
    (h1 : (readScalars n).run t = none) : (roundF (n + 1) acc (some e)).run t = none := by
  unfold roundF sumcheckRoundPoly
  simp only [Nat.add_sub_cancel, bind_assoc]
  rw [Refines.run_bind_none h1]

/-! ## A step in parts -/

/-- The children's part of a step: three children read, their products checked. -/
def childM (n : Nat) (claim comb : EW) : VM (Array EW × Array EW × Array EW) := do
  let c0 ← readScalars n
  let c1 ← readScalars n
  let c2 ← readScalars n
  require (claim == polyEval #[prodE c0, prodE c1, prodE c2] comb)
  pure (c0, c1, c2)

/-- `gkrStep` with its grinds of `0` bits dropped. -/
def gkrStepM (step : Nat) (st : GkrStateW) : VM GkrStateW := do
  let comb ← sampleChallenge
  let r ← sumcheck (polyEval st.values comb) (2 ^ step + 1) (st.point.map some)
  let c ← childM (2 ^ step) r.2 comb
  let y ← sampleChallenges step
  pure ⟨#[multilinearEval c.1 y, multilinearEval c.2.1 y, multilinearEval c.2.2 y], y ++ r.1⟩

theorem grind_le_eq {k : Nat} (hk : k ≤ 8) : Model.grind (grindingBits k) = pure () := by
  rw [grindingBits_le hk]
  rfl

theorem gkrStep_eq {step : Nat} (hs : step ≤ 2) (last : Bool) (st : GkrStateW) :
    gkrStep step last st = gkrStepM step st := by
  have hg : (if last then 2 * step else step) ≤ 8 := by split <;> omega
  unfold gkrStep gkrStepM childM
  rw [grind_le_eq (by decide), grind_le_eq hg]
  simp only [pure_bind, bind_assoc, List.map_toArray, List.map_cons, List.map_nil]

/-! ## The walk's runs -/

theorem verifyGkr_run {depth : Nat} {shared count : EW}
    (h1 : Model.readScalar.run t = some (shared, t₁)) (h2 : Model.readScalar.run t₁ = some (count, t₂)) :
    (verifyGkrGrandProducts depth).run t =
      ((gkrLayers depth ⟨#[shared, shared, count], #[]⟩).run t₂).map
        fun p ↦ ((count, p.1.point, p.1.values), p.2) := by
  unfold verifyGkrGrandProducts
  rw [Refines.run_bind_some h1, Refines.run_bind_some h2, StateT.run_bind]
  cases (gkrLayers depth ⟨#[shared, shared, count], #[]⟩).run t₂ <;> rfl

theorem verifyGkr_none1 {depth : Nat} (h1 : Model.readScalar.run t = none) :
    (verifyGkrGrandProducts depth).run t = none := by
  unfold verifyGkrGrandProducts
  rw [Refines.run_bind_none h1]

theorem verifyGkr_none2 {depth : Nat} {shared : EW}
    (h1 : Model.readScalar.run t = some (shared, t₁)) (h2 : Model.readScalar.run t₁ = none) :
    (verifyGkrGrandProducts depth).run t = none := by
  unfold verifyGkrGrandProducts
  rw [Refines.run_bind_some h1, Refines.run_bind_none h2]

/-! ## Sums and products against ones -/

open LeanVM.Protocol in
theorem one_add_add_one (x : E) : 1 + x + 1 = x := by
  have h : (1 : E) + 1 = 0 := by
    rw [← Field.eOf_one, ← Field.eOf_add, UInt64.xor_self, UInt64.xor_self, Field.eOf_zero]
  rw [add_comm (1 : E) x, add_assoc, h, add_zero]

open LeanVM.Protocol in
theorem dot_ones : ∀ (xs : List E) (m : Nat), xs.length ≤ m →
    Verifier.dot xs (List.replicate m 1) = Verifier.sumE xs
  | [], m, _ => by cases m <;> rfl
  | x :: xs, m + 1, h => by
    rw [List.replicate_succ, Field.dot_cons, dot_ones xs m (by simp at h; omega), mul_one]
    unfold Verifier.sumE
    rw [List.foldl_cons, zero_add, Field.foldl_add xs x]

open LeanVM.Protocol in
theorem eqEval_ones : ∀ (xs : List E) (m : Nat), xs.length ≤ m →
    Verifier.eqEval xs (List.replicate m 1) = Verifier.prodE xs
  | [], m, _ => by cases m <;> rfl
  | x :: xs, m + 1, h => by
    rw [List.replicate_succ, Field.eqEval_cons, eqEval_ones xs m (by simp at h; omega),
      one_add_add_one]
    unfold Verifier.prodE
    rw [List.foldl_cons, one_mul, Field.foldl_mul xs x]

end NativeVm.Code.P3
