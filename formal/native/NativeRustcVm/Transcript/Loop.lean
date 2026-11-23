module

public import NativeVm.Model.Transcript
public import NativeRustcVm.Transcript.Frame

/-!
# The model's loops of reads and samples

`readScalars n` and `sampleChallenges n` are `pushes m n`: `n` results of the step `m`, in order.
One more step (`pushes_succ`), a rejecting step rejecting every longer loop (`pushes_none`), and the
results' count (`pushes_size`). The elements a loop writes: one more (`ewsAt_push`), kept where
nothing changed (`ewsAt_keep`); the end of the output reached (`off_eq_iff`).
-/

namespace NativeRustcVm.Transcript

open NativeVm.Model

@[expose] public section

/-- `n` results of `m`, in order. -/
def pushes (m : VM EW) (n : Nat) : VM (Array EW) :=
  (List.range n).foldlM (fun (acc : Array EW) _ ↦ do pure (acc.push (← m))) #[]

end

public section

theorem readScalars_eq (n : Nat) : readScalars n = pushes readScalar n := rfl

theorem sampleChallenges_eq (n : Nat) : sampleChallenges n = pushes sampleChallenge n := rfl

theorem pushes_zero (m : VM EW) (s : TState) : (pushes m 0).run s = some (#[], s) := rfl

theorem pushes_succ (m : VM EW) (n : Nat) (s : TState) :
    (pushes m (n + 1)).run s = ((pushes m n).run s).bind fun p ↦
      (m.run p.2).map fun q ↦ (p.1.push q.1, q.2) := by
  unfold pushes
  rw [List.range_succ, List.foldlM_append, StateT.run_bind]
  show Option.bind _ _ = Option.bind _ _
  congr 1
  funext p
  rcases hm : m.run p.2 with _ | ⟨x, s''⟩ <;>
    simp [List.foldlM_cons, List.foldlM_nil, hm]

theorem pushes_none {m : VM EW} {n : Nat} {s : TState} (h : (pushes m n).run s = none) :
    (pushes m (n + 1)).run s = none := by
  rw [pushes_succ, h]; rfl

/-- A step rejecting after `i` results rejects every longer loop. -/
theorem pushes_none_of {m : VM EW} {i : Nat} {s s' : TState} {xs : Array EW}
    (h : (pushes m i).run s = some (xs, s')) (hm : m.run s' = none) :
    ∀ n, i < n → (pushes m n).run s = none := by
  intro n hn
  induction n with
  | zero => omega
  | succ n ih =>
    rcases Nat.lt_succ_iff_lt_or_eq.mp hn with hlt | heq
    · exact pushes_none (ih hlt)
    · subst heq
      rw [pushes_succ, h]
      show (m.run s').map _ = none
      rw [hm]; rfl

theorem pushes_size {m : VM EW} {n : Nat} {s s' : TState} {xs : Array EW}
    (h : (pushes m n).run s = some (xs, s')) : xs.size = n := by
  induction n generalizing xs s' with
  | zero => cases h; rfl
  | succ n ih =>
    rw [pushes_succ] at h
    rcases hp : (pushes m n).run s with _ | ⟨ys, t⟩
    · rw [hp] at h; cases h
    · rw [hp] at h
      rcases hq : m.run t with _ | ⟨y, t'⟩
      · simp [hq] at h
      · simp only [Option.bind_some, hq, Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        rw [Array.size_push, ih hp]

theorem length_flatMap_ewBytes (xs : List EW) : (xs.flatMap ewBytes).length = 16 * xs.length := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    rw [List.flatMap_cons, List.length_append, ih]
    simp only [ewBytes, List.length_append, length_wordBytes, List.length_cons]
    omega

theorem ewsAt_push {d : Mem 64} {p : BitVec 64} {xs : Array EW} {c : EW} :
    EWsAt d p (xs.push c).toList ↔ EWsAt d p xs.toList ∧ EWAt d (off p (16 * xs.size)) c := by
  unfold EWsAt EWAt
  rw [Array.toList_push, List.flatMap_append, bytesAt_append, length_flatMap_ewBytes,
    Array.length_toList]
  simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]

theorem ewsAt_keep {d d' : Mem 64} {p : BitVec 64} {xs : List EW} {R : BitVec 64 → Prop}
    (hs : SameOutside d d' R) (hnw : 16 * xs.length ≤ 2 ^ 64)
    (hR : ∀ q, InRange p (16 * xs.length) q → ¬ R q) (h : EWsAt d p xs) : EWsAt d' p xs :=
  bytesAt_congr h fun i hi ↦ hs _ (hR _ (by
    rw [length_flatMap_ewBytes] at hi
    exact inRange_off_self hi hnw))

theorem off_eq_iff {o : BitVec 64} {i n : Nat} (hn : o.toNat + 16 * n ≤ 2 ^ 64) (hi : i < n) :
    off o (16 * (i + 1)) = off o (16 * n) ↔ i + 1 = n := by
  constructor
  · intro h
    have := congrArg BitVec.toNat h
    simp only [off, BitVec.toNat_add, BitVec.toNat_ofNat] at this
    omega
  · rintro rfl; rfl

end

end NativeRustcVm.Transcript
