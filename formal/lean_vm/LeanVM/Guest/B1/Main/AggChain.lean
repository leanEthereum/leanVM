/-
  LeanVM.Guest.B1.Main.AggChain

  The Fiat-Shamir blocks of the batching loops read forward: one absorb, a chain of absorbs, one
  squeeze.
-/

module

public import LeanVM.Guest.B1.Main.AggLoops
public import LeanVM.Guest.B1.Main.BatchSpec

/-!
# Absorb chains and squeezes, forward

`fsNext_out`: an `fs_next` block from the state of `cv` leaves the state of `obsCv cv x`, `x` the
word it read. `obsChain_sound`: a chain of `n` of them reads `n` words `xs` at the cursor and
leaves the state of `obsAll cv xs`. `squeeze_out`: a `squeeze` block from the state of `cv`
leaves the state of `sqCv cv` and the challenge `challengeOf (sqCv cv)`.
-/

namespace LeanVM.Guest.B1.Main

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Protocol LeanVM.Protocol.Blake2sHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

variable {C : CallRel} {rd : Reader} {σ : Val}

theorem fsNext_out {s0 s1 cur : V} {j b : ℕ} {cv : Digest}
    (h : LoadHolds rd (σ cur) j (σ (.n b)) ∧ ∃ cv, (σ s0, σ s1) = digestScalars cv ∧
      ∀ k, 2 ≤ k → k < 14 → σ (.n (b + 1 + k)) = fsVals (σ (.n b)) cv 1 k)
    (hcv : (σ s0, σ s1) = digestScalars cv) :
    LoadHolds rd (σ cur) j (σ (.n b)) ∧
      (σ (.n (b + 13)), σ (.n (b + 14))) = digestScalars (obsCv cv (σ (.n b))) := by
  obtain ⟨hl, cv', hcv', e⟩ := h
  have := digestScalars_injective (hcv'.symm.trans hcv)
  subst this
  refine ⟨hl, ?_⟩
  rw [show b + 13 = b + 1 + 12 by omega, show b + 14 = b + 1 + 13 by omega,
    e 12 (by omega) (by omega), e 13 (by omega) (by omega)]
  rfl

theorem squeeze_out {s0 s1 : V} {b : ℕ} {cv : Digest}
    (h : ∃ cv, (σ s0, σ s1) = digestScalars cv ∧ ∀ k, k < 14 → σ (.n (b + k)) = sqVals cv k)
    (hcv : (σ s0, σ s1) = digestScalars cv) :
    (σ (.n (b + 5)), σ (.n (b + 6))) = digestScalars (sqCv cv) ∧
      σ (.n (b + 13)) = challengeOf (sqCv cv) := by
  obtain ⟨cv', hcv', e⟩ := h
  have := digestScalars_injective (hcv'.symm.trans hcv)
  subst this
  refine ⟨?_, e 13 (by omega)⟩
  rw [e 5 (by omega), e 6 (by omega)]
  rfl

theorem obsAll_take_succ (cv : Digest) (xs : List E) (k : ℕ) (hk : k < xs.length) :
    obsAll cv (xs.take (k + 1)) = obsCv (obsAll cv (xs.take k)) (xs.getD k 0) := by
  rw [List.take_add_one, List.getElem?_eq_getElem hk, List.getD_eq_getElem _ _ hk, obsAll,
    obsAll, Option.toList_some, List.foldl_append]
  rfl

/-- **An absorb chain, forward**: from the state of `cv`, the `n` words at the cursor are read and
absorbed. -/
theorem obsChain_sound (s0 s1 cur : V) (B n : ℕ) (kret : List E → Prop) {cv : Digest}
    (h : Stmt.HoldsList C rd σ (obsChainT s0 s1 cur B n) True kret)
    (hcv : (σ s0, σ s1) = digestScalars cv) :
    ∃ xs : List E, xs.length = n ∧ ReadsAt rd (σ cur) xs ∧
      (σ (chainS0 s0 B n), σ (chainS1 s1 B n)) = digestScalars (obsAll cv xs) := by
  rw [obsChainT, holdsList_range_flatten _ _ (fun _ => rfl)] at h
  simp only [holds_fsNextT, and_true] at h
  let xs := (List.range n).map fun k => σ (.n (B + 15 * k))
  have hlen : xs.length = n := by simp [xs]
  have hx : ∀ k < n, xs.getD k 0 = σ (.n (B + 15 * k)) := fun k hk => by
    simp [xs, List.getD_eq_getElem?_getD, hk]
  have key : ∀ m ≤ n, (σ (chainS0 s0 B m), σ (chainS1 s1 B m)) =
      digestScalars (obsAll cv (xs.take m)) := by
    intro m hm
    induction m with
    | zero => simpa [chainS0, chainS1, obsAll] using hcv
    | succ m ih =>
      have := (fsNext_out (h m (by omega)) (ih (by omega))).2
      rw [obsAll_take_succ _ _ _ (by omega), hx m (by omega)]
      exact this
  refine ⟨xs, hlen, fun k hk => ?_, ?_⟩
  · have := (h k (by omega)).1
    rwa [← hx k (by omega), List.getD_eq_getElem _ _ hk] at this
  · rw [key n le_rfl, ← hlen, List.take_length]

end
end LeanVM.Guest.B1.Main
