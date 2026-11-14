/-
  LeanVM.Guest.B1.Exact.Padding

  `padding_weight__L{τ}` is exact on every valid tree, at its 31 specializations: its `τ + 1` bits are Boolean and
  rebuild its word.
-/

module

public import LeanVM.Guest.Exact.Ok
public import LeanVM.Guest.B1.Tables.Padding

/-!
# `padding_weight`, exact

`padding_weight__L{τ}` hints the `τ + 1` bits of `W = rows + (2^τ - 1)`, pins each by booleanity and rebuilds `W` from
them (`Padding.lean`). So on every path that holds, the bits rebuild their word (`bits_exact_of_sum`): its one computed
hint is exact (`pw_pathExact`; the template's conditions `pw_holds_iff` at `τ ≥ 2`, `__L0` and `__L1` by their bodies),
and `padding_weight__L{τ}`, calling nothing, is in `ExactOk` (`pw_exactOk`).
-/

namespace LeanVM.Guest.B1.Tables

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Memory
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

/-- `padding_weight__L{τ}`'s computed hint: the bits of its word. -/
def pwHintA (τ : ℕ) : Atom :=
  if τ = 0 then .hint (.bits (.n 0) 0 1 (.stack [.n 2]))
  else .hint (.bits (.n 3) 0 (τ + 1) (.stack ((List.range (τ + 1)).map fun k => .n (4 + k))))

theorem pw_sites_all : (List.range 31).all (fun τ => Stmt.blockNextOk
    (fun a => isComputed a && !decide (a ∈ [pwHintA τ])) pinsInverse (pwBodyOf τ)) = true := by
  decide +kernel

theorem pw_callees_all : (List.range 31).all (fun τ => Stmt.blockCallees (pwBodyOf τ) == []) = true := by
  decide +kernel

/-- The template's conditions, at a valuation. -/
theorem pw_holds_iff {C : CallRel} {rd : Reader} {σ : Val} (τ : ℕ) (rets : List E) :
    Stmt.HoldsList C rd σ (pwBody τ) False (fun rs => rs = rets) ↔
      σ (.n 2) = word (2 ^ τ - 1) 0 ∧ σ (.n 3) = σ (.n 0) + σ (.n 2) ∧
      σ (.n 4) = σ (.n 4) * σ (.n 4) ∧ LoadHolds rd (σ (.n 1)) 0 (σ (.n (τ + 5))) ∧
      σ (.n (τ + 6)) = σ (.n 4) * σ (.n (τ + 5)) ∧ σ (.n (τ + 7)) = σ (.n 4) + σ (.n (τ + 5)) ∧
      σ (.n (τ + 8)) = σ (.n (τ + 6)) + σ (.n (τ + 7)) ∧
      (∀ i < τ - 1, PwStepOk rd σ τ (i + 1)) ∧
      σ (.n (4 + τ)) = σ (.n (4 + τ)) * σ (.n (4 + τ)) ∧
      (∀ j < τ - 2, PwHornOk σ τ j) ∧ PwTailOk σ τ rets := by
  rw [pwBody]
  simp only [holdsList_append, tb_holdsList_range_flatten (τ - 1) (fun i => pwStep τ (i + 1))
    (fun _ => rfl), tb_holdsList_range_flatten (τ - 2) (pwHorner τ) (fun _ => rfl), holds_pwStep,
    holds_pwHorner, holds_pwTail, pwHead, pwStep0, Stmt.HoldsList, Stmt.Holds, Atom.Holds, true_and]

/-- **At `τ ≥ 2`, the template's bits rebuild its word.** -/
theorem pw_bits_rebuild {rd : Reader} {σ : Val} {τ : ℕ} (h2 : 2 ≤ τ) (h32 : τ ≤ 32) {rets : List E}
    (h : Stmt.HoldsList (fun _ _ _ => True) rd σ (pwBody τ) False (fun rs => rs = rets)) :
    (∀ k < τ + 1, σ (.n (4 + k)) * σ (.n (4 + k)) = σ (.n (4 + k))) ∧
      σ (.n 3) = ∑ k ∈ Finset.range (τ + 1), σ (.n (4 + k)) * gen ^ k := by
  obtain ⟨e2, e3, s0b, -, -, -, -, hsteps, htop, hhorn, ht⟩ := (pw_holds_iff τ rets).mp h
  obtain ⟨t0, t1, t2, -, -, -, -, -, -, t9, t10, t11, a11, -⟩ := ht
  set b : ℕ → E := fun k => σ (.n (4 + k))
  have hb : ∀ k < τ + 1, b k * b k = b k := fun k hk => by
    rcases Nat.eq_zero_or_pos k with rfl | hk0
    · exact s0b.symm
    rcases Nat.lt_or_ge k τ with hkτ | hkτ
    · obtain ⟨e, -⟩ := hsteps (k - 1) (by omega)
      rw [show k - 1 + 1 = k by omega] at e
      exact e.symm
    · rw [show k = τ by omega]; exact htop.symm
  have hbl : ∀ j ≤ τ - 2, σ (.n (pwBelow τ j)) = pwBl b τ j := fun j hj => by
    induction j with
    | zero => simp only [pwBelow, ↓reduceIte, pwBl, b]; congr 2; omega
    | succ j ih =>
      obtain ⟨c, m, a⟩ := hhorn j (by omega)
      rw [pwBl, ← ih (by omega), show pwBelow τ (j + 1) = 6 * τ + 6 + 3 * j by
        simp only [pwBelow, Nat.succ_ne_zero, ↓reduceIte]; ring, a, m, c, tb_word_gen]
      simp only [b]; congr 3; omega
  have hlow : pwS σ τ 2 = ∑ k ∈ Finset.range τ, b k * gen ^ k := by
    rw [t2, t1, t0, hbl _ le_rfl, pwBl_top b h2, tb_word_two_pow (by omega),
      show τ = τ - 1 + 1 by omega, Finset.sum_range_succ, show τ - 1 + 1 - 1 = τ - 1 by omega]
    simp only [b]; rw [show 3 + (τ - 1 + 1) = 4 + (τ - 1) by omega]
  refine ⟨hb, ?_⟩
  rw [Finset.sum_range_succ, ← hlow, ← e_add_eq_zero_iff.mp a11, t11, t10, t9, tb_word_two_pow (by omega)]

/-- **Every path of `padding_weight__L{τ}` that holds is exact.** -/
theorem pw_pathExact {τ : ℕ} (hτ : τ < 31) {fn : Fn} (hb : fn.body = pwBodyOf τ) : PathExactFn fn := by
  have hs := List.all_eq_true.mp pw_sites_all τ (List.mem_range.mpr hτ)
  rw [← hb] at hs
  refine pathExact_of_sites (sites := [pwHintA τ]) hs fun rd σ es vs hw hes a ha _ => ?_
  rw [List.mem_singleton.mp ha]
  have h : Stmt.HoldsList (fun _ _ _ => True) rd σ fn.body False (fun rs => rs = vs.map σ) :=
    holdsList_of_walk _ (by rw [hw]; exact ⟨fun e he => ⟨hes e he, fun _ _ _ _ => trivial⟩, rfl⟩)
  rw [hb, pwBodyOf] at h
  by_cases h0 : τ = 0
  · subst h0
    simp only [↓reduceIte, pwBody0, Stmt.HoldsList, Stmt.Holds, Atom.Holds, true_and] at h
    obtain ⟨b0, a0, -⟩ := h
    simp only [pwHintA, ↓reduceIte]
    exact bits_exact_of_sum (fun _ => σ (.n 2)) (by norm_num) rfl (fun _ _ => b0.symm)
      (by simp [(e_add_eq_zero_iff.mp a0).symm])
  by_cases h1 : τ = 1
  · subst h1
    simp only [show (1 : ℕ) ≠ 0 from by decide, ↓reduceIte, pwBody1, Stmt.HoldsList, Stmt.Holds, Atom.Holds,
      true_and] at h
    obtain ⟨-, -, b4, -, -, -, -, b5, -, -, -, c13, m14, a15, e15, -⟩ := h
    simp only [pwHintA, show (1 : ℕ) ≠ 0 from by decide, ↓reduceIte]
    refine bits_exact_of_sum (fun k => σ (.n (4 + k))) (by norm_num) rfl (fun k hk => ?_) ?_
    · interval_cases k
      exacts [b4.symm, b5.symm]
    · rw [← e_add_eq_zero_iff.mp e15, a15, m14, c13, word_gen]
      simp [Finset.sum_range_succ]
  · simp only [h0, h1, ↓reduceIte] at h
    obtain ⟨hbb, hv⟩ := pw_bits_rebuild (by omega) (by omega) h
    simp only [pwHintA, h0, ↓reduceIte]
    exact bits_exact_of_sum (fun k => σ (.n (4 + k))) (by omega) (by rw [List.map_map]; rfl) hbb hv

/-- **`padding_weight__L{τ}` is exact on every valid tree.** -/
theorem pw_exactOk {τ : ℕ} (hτ : τ < 31) : ExactOk (lName "padding_weight" τ) := by
  obtain ⟨fn, hf, -, hb⟩ := pwFound hτ
  refine .node hf (pw_pathExact hτ hb) fun g hg _ => absurd hg ?_
  have := List.all_eq_true.mp pw_callees_all τ (List.mem_range.mpr hτ)
  rw [hb, beq_iff_eq.mp this]
  exact List.not_mem_nil

end
end LeanVM.Guest.B1.Tables
