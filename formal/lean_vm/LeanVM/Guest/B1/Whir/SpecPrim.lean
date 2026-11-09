/-
  LeanVM.Guest.B1.Whir.SpecPrim

  The Spec's primitive steps, run on the carried sponge (`runF`), read backwards: what an
  accepting run of a step followed by a continuation tells.
-/

module

public import LeanVM.Guest.B1.Whir.RunF
public import LeanVM.Guest.B1.Whir.Positions
public import LeanVM.Protocol.WithHash

/-!
# Primitive steps, backwards

For each primitive (`readE`, `readN`, `sampleE`, `sampleN`, `grindP`, `commitP`, `queryP`,
`require`, `sampleQueries`) followed by a continuation `k`, an accepting `runF` splits into the
step's effect on the state (`FSt`) and an accepting run of `k`. `readN`, `sampleN` and
`sampleQueries` are solved in closed form (`absorbAll`, `squeezeN`, `queriesOf`).
-/

namespace LeanVM.Guest.B1.Whir

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

variable {α β : Type}

theorem runF_ret_some {a : α} {st : FSt} {r : α × FSt} (h : runF (VerifierProgram.ret a) st =
    some r) :
    r = (a, st) := (Option.some.inj h).symm

theorem runF_readE_bind {k : E → VerifierProgram β} {F : Fs} {xs : List E} {os : List (List Opening)}
    {R : List (Digest × ℕ × ℕ)} {r : β × FSt} (h : runF (VerifierProgram.readScalar.bind k) ⟨F, xs, os, R⟩ = some r) :
    ∃ x xs', xs = x :: xs' ∧ runF (k x) ⟨F.absorb x dsObserve, xs', os, R⟩ = some r := by
  cases xs with
  | nil => simp [VerifierProgram.readScalar, VerifierProgram.bind, runF] at h
  | cons x xs => exact ⟨x, xs, rfl, h⟩

theorem runF_sampleE_bind (k : E → VerifierProgram β) (F : Fs) (xs : List E) (os : List (List Opening))
    (R : List (Digest × ℕ × ℕ)) :
    runF (VerifierProgram.sampleChallenge.bind k) ⟨F, xs, os, R⟩ = runF (k F.squeeze.1) ⟨F.squeeze.2, xs, os, R⟩ := rfl

theorem runF_grindP_bind {bits : ℕ} {k : Unit → VerifierProgram β} {F : Fs} {xs : List E} {os : List (List Opening)}
    {R : List (Digest × ℕ × ℕ)} {r : β × FSt}
    (h : runF ((VerifierProgram.grindProofOfWork bits).bind k) ⟨F, xs, os, R⟩ = some r) :
    ∃ n xs', xs = n :: xs' ∧ powOk bits n (F.absorb n dsPowNonce).squeeze.1 = true ∧
      runF (k ()) ⟨(F.absorb n dsPowNonce).squeeze.2, xs', os, R⟩ = some r := by
  cases xs with
  | nil => simp [VerifierProgram.grindProofOfWork, VerifierProgram.bind, runF] at h
  | cons n xs =>
    simp only [VerifierProgram.grindProofOfWork, VerifierProgram.bind, runF] at h
    split at h
    · rename_i hp
      exact ⟨n, xs, rfl, hp, h⟩
    · simp at h

theorem runF_commitP_bind {hh ww : ℕ} {k : Unit → VerifierProgram β} {F : Fs} {xs : List E}
    {os : List (List Opening)} {R : List (Digest × ℕ × ℕ)} {r : β × FSt}
    (h : runF ((VerifierProgram.readCommitment hh ww).bind k) ⟨F, xs, os, R⟩ = some r) :
    ∃ x0 x1 xs' d, xs = x0 :: x1 :: xs' ∧ digestFromHalves (x0, x1) = some d ∧
      runF (k ()) ⟨(F.absorb x0 dsObserve).absorb x1 dsObserve, xs', os, R ++ [(d, hh, ww)]⟩ =
        some r := by
  match xs with
  | [] => simp [VerifierProgram.readCommitment, VerifierProgram.bind, runF] at h
  | [_] => simp [VerifierProgram.readCommitment, VerifierProgram.bind, runF] at h
  | x0 :: x1 :: xs =>
    simp only [VerifierProgram.readCommitment, VerifierProgram.bind, runF] at h
    split at h
    · rename_i d hd
      exact ⟨x0, x1, xs, d, rfl, hd, h⟩
    · simp at h

theorem runF_queryP_bind {i : ℕ} {ps : List ℕ} {k : List (List K) → VerifierProgram β} {F : Fs}
    {xs : List E} {os : List (List Opening)} {R : List (Digest × ℕ × ℕ)} {r : β × FSt}
    (h : runF ((VerifierProgram.queryOpenings i ps).bind k) ⟨F, xs, os, R⟩ = some r) :
    ∃ (root : Digest) (height width : ℕ) (rows : List (List K)) (phase : List Opening)
      (rest : List (List Opening)),
      R[i]? = some (root, height, width) ∧ os = phase :: rest ∧
      Id.run (Compile.openPhaseWithHash (m := Id) keccak256 root height width ps phase) =
        some rows ∧
      runF (k rows) ⟨F, xs, rest, R⟩ = some r := by
  cases hR : R[i]? with
  | none => simp [VerifierProgram.queryOpenings, VerifierProgram.bind, runF, hR] at h
  | some v =>
    obtain ⟨root, height, width⟩ := v
    cases os with
    | nil => simp [VerifierProgram.queryOpenings, VerifierProgram.bind, runF, hR] at h
    | cons phase rest =>
      simp only [VerifierProgram.queryOpenings, VerifierProgram.bind, runF, hR] at h
      cases ho : Id.run (Compile.openPhaseWithHash (m := Id) keccak256 root height width ps
          phase) with
      | none => simp [ho] at h
      | some rows =>
        simp only [ho] at h
        exact ⟨root, height, width, rows, phase, rest, rfl, rfl, ho, h⟩

theorem runF_require_bind {c : Prop} [Decidable c] {k : Unit → VerifierProgram β} {st : FSt} {r :
    β × FSt}
    (h : runF ((VerifierProgram.require c).bind k) st = some r) : c ∧ runF (k ()) st = some r := by
  by_cases hc : c
  · simp only [VerifierProgram.require, hc, ↓reduceIte, VerifierProgram.ret_bind] at h
    exact ⟨hc, h⟩
  · simp [VerifierProgram.require, hc, VerifierProgram.bind, runF] at h

/-- **`readN n`, backwards**: the next `n` words, absorbed. -/
theorem runF_readN_bind : ∀ (n : ℕ) {k : List E → VerifierProgram β} {F : Fs} {xs : List E}
    {os : List (List Opening)} {R : List (Digest × ℕ × ℕ)} {r : β × FSt},
    runF ((VerifierProgram.readScalars n).bind k) ⟨F, xs, os, R⟩ = some r →
      n ≤ xs.length ∧
      runF (k (xs.take n)) ⟨F.absorbAll (xs.take n) dsObserve, xs.drop n, os, R⟩ = some r
  | 0, k, F, xs, os, R, r, h => by
    refine ⟨Nat.zero_le _, ?_⟩
    simpa [VerifierProgram.readScalars, Fs.absorbAll] using h
  | n + 1, k, F, xs, os, R, r, h => by
    have e : (VerifierProgram.readScalars (n + 1)).bind k =
        VerifierProgram.readScalar.bind fun x ↦ (VerifierProgram.readScalars n).bind fun xs ↦ k (x
            :: xs) := by
      simp only [VerifierProgram.readScalars, VerifierProgram.bind_eq, VerifierProgram.pure_eq,
          VerifierProgram.bind_assoc, VerifierProgram.ret_bind]
    rw [e] at h
    obtain ⟨x, xs', hs, h1⟩ := runF_readE_bind h
    obtain ⟨hl, h2⟩ := runF_readN_bind n h1
    subst hs
    refine ⟨by simp; omega, ?_⟩
    simpa [Fs.absorbAll, List.take_succ_cons, List.drop_succ_cons] using h2

/-- **`sampleN n`**: the next `n` challenges. -/
theorem runF_sampleN_bind : ∀ (n : ℕ) (k : List E → VerifierProgram β) (F : Fs) (xs : List E)
    (os : List (List Opening)) (R : List (Digest × ℕ × ℕ)),
    runF ((VerifierProgram.sampleChallenges n).bind k) ⟨F, xs, os, R⟩ =
      runF (k (F.squeezeN n).1) ⟨(F.squeezeN n).2, xs, os, R⟩
  | 0, k, F, xs, os, R => by simp [VerifierProgram.sampleChallenges, Fs.squeezeN]
  | n + 1, k, F, xs, os, R => by
    have e : (VerifierProgram.sampleChallenges (n + 1)).bind k =
        VerifierProgram.sampleChallenge.bind fun x ↦ (VerifierProgram.sampleChallenges n).bind
            fun xs ↦ k (x :: xs) := by
      simp only [VerifierProgram.sampleChallenges, VerifierProgram.bind_eq, VerifierProgram.pure_eq,
          VerifierProgram.bind_assoc, VerifierProgram.ret_bind]
    rw [e, runF_sampleE_bind, runF_sampleN_bind n]
    rfl

/-- **The query positions**: `ceilDiv rem (192/d)` challenges, cut into positions. -/
theorem runF_sampleQueriesAux_bind (d : ℕ) (hd : 1 ≤ 192 / d) :
    ∀ (fuel rem : ℕ) (k : List ℕ → VerifierProgram β) (F : Fs) (xs : List E) (os : List (List Opening))
      (R : List (Digest × ℕ × ℕ)), ceilDiv rem (192 / d) ≤ fuel →
      runF ((sampleQueriesAux d fuel rem).bind k) ⟨F, xs, os, R⟩ =
        runF (k (queriesOf (192 / d) d (F.squeezeN (ceilDiv rem (192 / d))).1 rem))
          ⟨(F.squeezeN (ceilDiv rem (192 / d))).2, xs, os, R⟩
  | fuel, 0, k, F, xs, os, R, _ => by
    rw [ceilDiv_zero]
    rcases fuel with _ | fuel <;> simp [sampleQueriesAux, queriesOf, Fs.squeezeN]
  | 0, rem + 1, k, F, xs, os, R, h => by
    have := ceilDiv_step (a := rem + 1) hd (Nat.succ_pos rem); omega
  | fuel + 1, rem + 1, k, F, xs, os, R, h => by
    have hs := ceilDiv_step (a := rem + 1) hd (Nat.succ_pos rem)
    have hp : (sampleQueriesAux d (fuel + 1) (rem + 1)).bind k =
        VerifierProgram.sampleChallenge.bind fun w ↦
        (sampleQueriesAux d fuel (rem + 1 - min (192 / d) (rem + 1))).bind fun rest ↦
          k (((List.range (min (192 / d) (rem + 1))).map fun c ↦
            (eToNat w >>> (c * d)) % 2 ^ d) ++ rest) := by
      simp only [sampleQueriesAux, Nat.add_one_ne_zero, ↓reduceIte, VerifierProgram.bind_eq,
          VerifierProgram.pure_eq,
        VerifierProgram.bind_assoc, VerifierProgram.ret_bind]
    rw [hp, runF_sampleE_bind, runF_sampleQueriesAux_bind d hd fuel _ _ _ _ _ _ (by omega), hs,
      queriesOf_cons _ _ hd]
    rfl

theorem ceilDiv_le_self {a b : ℕ} (hb : 1 ≤ b) : ceilDiv a b ≤ a := by
  unfold ceilDiv
  rcases Nat.eq_zero_or_pos a with rfl | ha
  · simp only [Nat.zero_add]; exact (Nat.div_eq_of_lt (by omega)).le
  · obtain ⟨a', rfl⟩ : ∃ a', a = a' + 1 := ⟨a - 1, by omega⟩
    obtain ⟨b', rfl⟩ : ∃ b', b = b' + 1 := ⟨b - 1, by omega⟩
    apply Nat.div_le_of_le_mul
    have e : a' + 1 + (b' + 1) - 1 = a' + b' + 1 := by omega
    rw [e]
    nlinarith [Nat.zero_le (a' * b')]

theorem runF_sampleQueries_bind {d q : ℕ} (hd : 1 ≤ 192 / d) (k : List ℕ → VerifierProgram β)
    (F : Fs)
    (xs : List E) (os : List (List Opening)) (R : List (Digest × ℕ × ℕ)) :
    runF ((sampleQueries d q).bind k) ⟨F, xs, os, R⟩ =
      runF (k (queriesOf (192 / d) d (F.squeezeN (ceilDiv q (192 / d))).1 q))
        ⟨(F.squeezeN (ceilDiv q (192 / d))).2, xs, os, R⟩ :=
  runF_sampleQueriesAux_bind d hd q q k F xs os R (ceilDiv_le_self hd)

end
end LeanVM.Guest.B1.Whir
