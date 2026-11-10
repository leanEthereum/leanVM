/-
  LeanVM.Guest.B1.KeccakGkr.PlainCompleteIn

  `keccak_plain_rounds`, completely and with its loads placed: its relation by a tree loading only
  the stream words at the cursor and the challenges' slots at the point.
-/

module

public import LeanVM.Guest.B1.KeccakGkr.PlainComplete41
public import LeanVM.Guest.B1.KeccakGkr.RecIn

/-!
# `keccak_plain_rounds`' loads

Both specializations are leaf bodies whose loads (by the kernel: `plain_leafOk`) read the cursor
(argument `7`) below `2n` and the point (argument `9`) below `n`; so with those words in a region
`R`, the relation loads from `R` (`keccak_plain_rounds_relIn`).
-/

namespace LeanVM.Guest.B1.VerifySub

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Guest.Memory LeanVM.Guest.Lift
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

/-- A load through the cursor below `2n` or through the point below `n`; no other load. -/
def plainLoad (n : ℕ) : Atom → Bool
  | .load _ p off => (decide (p = .n 7) && decide (off < 2 * n)) || (decide (p = .n 9) && decide (off < n))
  | _ => true

set_option maxRecDepth 100000 in
theorem plain60_leafOk : Stmt.leafOkList (plainLoad 6) Data.core266.body = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem plain41_leafOk : Stmt.leafOkList (plainLoad 4) Data.core268.body = true := by
  decide +kernel

theorem plain_loads {n : ℕ} {σ : Val} {es : List Ev} (h : ∀ e ∈ es, EvLeafOk (plainLoad n) e) :
    ∀ A ∈ loadAddrs σ es, (∃ off < 2 * n, A = (σ (.n 7)).limb 0 * Parameters.addressOfIndex off) ∨
      (∃ off < n, A = (σ (.n 9)).limb 0 * Parameters.addressOfIndex off) := by
  intro A hA
  obtain ⟨e, he, hea⟩ := List.mem_filterMap.mp hA
  have hok := h e he
  cases e with
  | atom a =>
    cases a with
    | load d p off =>
      simp only [Ev.loadAddr?, Option.some.injEq] at hea
      simp only [EvLeafOk, plainLoad, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at hok
      rcases hok with ⟨rfl, ho⟩ | ⟨rfl, ho⟩
      · exact Or.inl ⟨off, ho, hea.symm⟩
      · exact Or.inr ⟨off, ho, hea.symm⟩
    | _ => simp [Ev.loadAddr?] at hea
  | _ => simp [Ev.loadAddr?] at hea

theorem plain_relIn_of {n : ℕ} {f : String} {fn : Fn} (hf : coreProgram.find? f = some fn)
    (hparams : fn.params = [.n 0, .n 1, .n 2, .n 3, .n 4, .n 5, .n 6, .n 7, .n 8, .n 9, .n 10])
    (hleaf : Stmt.leafOkList (plainLoad n) fn.body = true) {rd : Reader} {R : ℕ → Prop}
    {args rets : List E} (hcur : ∀ k < 2 * n, InR R (args.getD 7 0) k)
    (hpt : ∀ k < n, InR R (args.getD 9 0) k) (h : coreProgram.Rel rd f args rets) :
    coreProgram.RelIn rd R f args rets :=
  relIn_of_leaf hf hleaf (fun σ es vs hp hw A hA ↦ by
    have hall : (Out.ret es vs).All (EvLeafOk (plainLoad n)) := by
      have := walk_leafOk (σ := σ) fn.body hleaf
      rwa [hw] at this
    rw [hparams] at hp
    have h7 : σ (.n 7) = args.getD 7 0 := by rw [← hp]; rfl
    have h9 : σ (.n 9) = args.getD 9 0 := by rw [← hp]; rfl
    rcases plain_loads hall A hA with ⟨off, ho, rfl⟩ | ⟨off, ho, rfl⟩
    · rw [h7]; exact hcur off ho
    · rw [h9]; exact hpt off ho) h

/-- **`keccak_plain_rounds` is complete, loading the stream words and the challenges' slots.** -/
theorem keccak_plain_rounds_relIn {k0 : ℕ} (hk : k0 < 2) {rd : Reader} {R : ℕ → Prop}
    {args rets : List E} (hpc : PlainCellsOk k0 args)
    (hm : MeaningPlainRounds (plainCount k0) k0 rd args rets)
    (hcur : ∀ k < 2 * plainCount k0, InR R (args.getD 7 0) k)
    (hpt : ∀ k < plainCount k0, InR R (args.getD 9 0) k) :
    coreProgram.RelIn rd R (plainName k0) args rets := by
  interval_cases k0
  · exact plain_relIn_of find_plain60 rfl plain60_leafOk hcur hpt (plain60_complete rd args rets hm)
  · exact plain_relIn_of find_plain41 rfl plain41_leafOk hcur hpt
      (plain41_complete rd args rets hpc hm)

end
end LeanVM.Guest.B1.VerifySub
