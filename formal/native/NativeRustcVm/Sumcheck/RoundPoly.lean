module

public import NativeVm.Model.Transcript

/-!
# `sumcheck_round_poly` as `transcript.rs` runs it

The model's `sumcheckRoundPoly count claim eq` step by step, as the Rust's two branches run it
(`roundPoly_some_run`, `roundPoly_none_run`); the round polynomial has `count` coefficients
(`roundPoly_size`, from `readScalars_size`); the grind's bits are the bit length of `count - 1`
(`grindingBits_succ`, `bit_length` of `count - 2` and `count - 1` less `3`, saturating).
-/

namespace NativeRustcVm.Sumcheck

open NativeVm.Model

@[expose] public section

/-- The bit length of `v`: `0` at `0`, else `log2 v + 1`. -/
def bitLenNat (v : Nat) : Nat := if v = 0 then 0 else v.log2 + 1

end

public section

/-- `grindingBits (v + 1)` is the bit length of `v` less `3`, saturating. -/
theorem grindingBits_succ (v : Nat) : grindingBits (v + 1) = bitLenNat v - 3 := by
  show LeanVM.Protocol.Compile.grindingBits (v + 1) = _
  unfold LeanVM.Protocol.Compile.grindingBits LeanVM.Protocol.Compile.securityBits bitLenNat
  by_cases h : v = 0
  · simp [h]
  · rw [ite_eq_right (show ¬(v + 1 ≤ 1) by omega), ite_eq_right h, Nat.add_sub_cancel]

/-- `readScalars n` returns `n` elements. -/
theorem readScalars_size {n : Nat} {s s' : TState} {xs : Array EW}
    (h : (readScalars n).run s = some (xs, s')) : xs.size = n := by
  have key : ∀ (l : List Nat) (acc : Array EW) (s s' : TState) (xs : Array EW),
      (l.foldlM (fun acc _ ↦ do pure (acc.push (← readScalar))) acc : VM (Array EW)).run s =
        some (xs, s') → xs.size = acc.size + l.length := by
    intro l
    induction l with
    | nil =>
      intro acc s s' xs h
      simp only [List.foldlM_nil, StateT.run_pure, Option.pure_def, Option.some.injEq,
        Prod.mk.injEq] at h
      rw [← h.1]; simp
    | cons x l ih =>
      intro acc s s' xs h
      simp only [List.foldlM_cons, StateT.run_bind] at h
      cases hr : (readScalar.run s) with
      | none =>
        simp only [bind, StateT.run] at h hr
        simp [hr] at h
      | some p =>
        obtain ⟨x, s1⟩ := p
        simp only [bind, StateT.run] at h hr
        simp only [hr, pure, StateT.pure, Option.bind_some] at h
        have := ih _ _ _ _ h
        simp at this
        simp; omega
  have := key (List.range n) #[] s s' xs h
  simpa using this

/-- **The equality mode's round**: the tail read, the grind, the derived coefficient first. -/
theorem roundPoly_some_run (count : Nat) (claim e : EW) (s : TState) :
    (sumcheckRoundPoly count claim (some e)).run s =
      ((readScalars (count - 1)).run s).bind fun p ↦
        ((grind (grindingBits (count - 1 + 1))).run p.2).bind fun q ↦
          some (#[claim + e * sumE p.1] ++ p.1, q.2) := by
  simp only [sumcheckRoundPoly, StateT.run, bind, StateT.bind, pure, StateT.pure]

/-- **The plain round**: the constant, the tail, the grind, the derived coefficient second. -/
theorem roundPoly_none_run (count : Nat) (claim : EW) (s : TState) :
    (sumcheckRoundPoly count claim none).run s =
      (readScalar.run s).bind fun p0 ↦
        ((readScalars (count - 2)).run p0.2).bind fun p ↦
          ((grind (grindingBits (count - 1))).run p.2).bind fun q ↦
            some (#[p0.1, claim + sumE p.1] ++ p.1, q.2) := by
  simp only [sumcheckRoundPoly, StateT.run, bind, StateT.bind, pure, StateT.pure]

/-- **The round polynomial has `count` coefficients** (`2 ≤ count`). -/
theorem roundPoly_size {count : Nat} (hc : 2 ≤ count) {claim : EW} {e : Option EW}
    {s s' : TState} {msg : Array EW}
    (h : (sumcheckRoundPoly count claim e).run s = some (msg, s')) : msg.size = count := by
  cases e with
  | none =>
    rw [roundPoly_none_run] at h
    cases h0 : readScalar.run s with
    | none => simp [h0] at h
    | some p0 =>
      rw [h0, Option.bind_some] at h
      cases h1 : (readScalars (count - 2)).run p0.2 with
      | none => simp [h1] at h
      | some p =>
        rw [h1, Option.bind_some] at h
        cases h2 : (grind (grindingBits (count - 1))).run p.2 with
        | none => simp [h2] at h
        | some q =>
          rw [h2, Option.bind_some, Option.some.injEq, Prod.mk.injEq] at h
          rw [← h.1, Array.size_append, readScalars_size h1]
          simp
          omega
  | some e =>
    rw [roundPoly_some_run] at h
    cases h1 : (readScalars (count - 1)).run s with
    | none => simp [h1] at h
    | some p =>
      rw [h1, Option.bind_some] at h
      cases h2 : (grind (grindingBits (count - 1 + 1))).run p.2 with
      | none => simp [h2] at h
      | some q =>
        rw [h2, Option.bind_some, Option.some.injEq, Prod.mk.injEq] at h
        rw [← h.1, Array.size_append, readScalars_size h1]
        simp
        omega

end

end NativeRustcVm.Sumcheck
