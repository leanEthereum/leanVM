/-
  LeanVM.Protocol.EndToEnd.Complete.Sizes

  The honest prover of the verifier program's first two steps: it announces the sizes and the
  rate, which pass every check of `readSizes` and give the verifier's layout, and commits the
  stack's word.
-/

module

public import LeanVM.Protocol.EndToEnd.Front.LayoutSizes
public import LeanVM.Protocol.Whir.Complete.Opening

/-!
# The announced sizes and the commitment

Steps 1 and 2 of `verify_execution` (`readSizes`, `commitStack`; `python-verifier/verifier.py:
1384-1395` at leanVM `3a37fb6e1c7423e36b67d1cac4eda70c3ad4dd45`). The honest prover sends the
eight scalars `announce s ρ` (`Front.announce`: the memory's log-size, the six tables' row counts,
then the WHIR rate, each the Python's `E(n)`), then the stack's level-0 word.

* `follows_readSizes`: for sizes admissible for the program and a valid rate, every `require` of
  `readSizes` passes, and it returns `(verifierLayout prog s, ρ)`: the converse of
  `Front.readSizes_ret_sizes`.
* `whirAdmissible`: the stack's size and the rate are in WHIR's window, so the opening's
  completeness (`Whir.Complete.follows_commitStack`, `follows_verifyStackedOpening`) applies at
  the verifier's layout.
-/

namespace LeanVM.Protocol.EndToEnd.Complete

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Protocol.LeanIsa LeanVM.Protocol.EndToEnd.Front LeanVM.Protocol.Whir.Complete

@[expose] public section

/-! ## The announced scalars -/

/-- The Python's `E(n)` has zero upper limbs. -/
theorem eOfNat_limb_one (n : ℕ) : (eOfNat n).limb 1 = 0 := by simp [eOfNat]

theorem eOfNat_limb_two (n : ℕ) : (eOfNat n).limb 2 = 0 := by simp [eOfNat]

/-- The Python's `int(E(n))` of a word-sized `n` is `n`. -/
theorem kToNat_eOfNat {n : ℕ} (h : n < 2 ^ 64) : kToNat ((eOfNat n).limb 0) = n := by
  simp only [eOfNat, limb_ofK, Fin.isValue, Fin.val_zero, ↓reduceIte, kToNat, K.ofBits]
  show (BitVec.ofNat 64 n).toNat = n
  rw [BitVec.toNat_ofNat]
  exact Nat.mod_eq_of_lt h

/-- **The honest announcement passes `readSizes`.** For sizes admissible for the program and a
valid rate, the honest prover's eight scalars pass every check, and `readSizes` returns the
verifier's layout at the sizes, and the rate. -/
theorem follows_readSizes (prog : Program) {s : Sizes} (hs : s.Admissible prog) {ρ : ℕ}
    (hρ : validRate ρ) (cs : Commits) :
    Follows (fun cs' _ b ↦ cs' = cs ∧ b = (verifierLayout prog s, ρ))
      (Script.sendList (announce s ρ)) (readSizes (bytecodeWords prog)) cs := by
  obtain ⟨h1, h2, h3, h5⟩ := hs
  have hlen : (announce s ρ).length = 2 + tables.length := by
    simp [announce, tables]
  unfold readSizes
  simp only [Prog.bind_eq]
  rw [← hlen, ← Script.bind_ret (Script.sendList (announce s ρ))]
  refine Follows.bind (fun cs' _ b hb ↦ ?_) _ _ _ (Follows.sendList_readN cs _)
  obtain ⟨rfl, rfl⟩ := hb
  have hlimbs : ((announce s ρ).all fun value ↦ decide (value.limb 1 = 0 ∧ value.limb 2 = 0)) =
      true := by
    simp [announce, eOfNat_limb_one, eOfNat_limb_two]
  have hmem : s.logMem < 2 ^ 64 := by
    have : s.logMem ≤ 32 := h2
    omega
  have hhead : kToNat (((announce s ρ).headD 0).limb 0) = s.logMem := by
    simp only [announce, List.cons_append, List.map_cons, List.headD_cons]
    exact kToNat_eOfNat hmem
  have hlast : kToNat (((announce s ρ).getLastD 0).limb 0) = ρ := by
    simp only [announce, List.map_cons, List.map_append, List.map_nil, List.cons_append]
    rw [List.getLastD_eq_getLast?, List.getLast?_cons, List.getLast?_append]
    simp only [List.getLast?_singleton, Option.some_or, Option.getD_some]
    exact kToNat_eOfNat (by have := hρ.2; omega)
  have htab : (((announce s ρ).drop 1).take tables.length).map (fun value ↦ kToNat (value.limb 0))
      = tableRows s := by
    have ht : tables.length = 6 := rfl
    simp only [announce, ht, List.cons_append, List.map_cons, List.drop_succ_cons, List.drop_zero,
      List.map_append, List.map_nil, tableRows, List.ofFn_succ, List.ofFn_zero]
    simp only [List.nil_append, List.take_succ_cons, List.take_zero,
      List.map_cons, List.map_nil, List.cons.injEq, and_true]
    have hτ : ∀ j, kToNat ((eOfNat (s.rows j)).limb 0) = s.rows j := fun j ↦
      kToNat_eOfNat (lt_of_le_of_lt (h3 j) (by decide))
    exact ⟨hτ 0, hτ 1, hτ 2, hτ 3, hτ 4, hτ 5⟩
  have hok : LayoutOk s := ⟨h1, h2, h3⟩
  have hb := buildLayout_eq prog s
  simp only [hok, ↓reduceIte] at hb
  have hwin : minStackedLog ≤ (verifierLayout prog s).stackLog ∧
      (verifierLayout prog s).stackLog ≤ maxStackedLog := by
    rw [stackLog_verifierLayout]
    exact ⟨le_max_right _ _, h5⟩
  simp only [Prog.require, hlimbs, ↓reduceIte, Prog.ret_bind, hlast, hhead, htab, hb,
    Verifier.liftOption, hwin, and_self, Prog.pure_eq]
  simp only [show 1 ≤ ρ ∧ ρ ≤ 4 from hρ, and_self, ↓reduceIte, Prog.ret_bind]
  exact ⟨rfl, rfl⟩

/-- The stack's size and an admissible rate are in WHIR's window. -/
theorem whirAdmissible (prog : Program) {s : Sizes} (hs : s.Admissible prog) {ρ : ℕ}
    (hρ : validRate ρ) : Whir.Admissible (leanIsaμ prog s) ρ :=
  ⟨le_max_right _ _, hs.2.2.2, hρ.1, hρ.2⟩

end
end LeanVM.Protocol.EndToEnd.Complete
