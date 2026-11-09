/-
  LeanVM.Guest.B1.Terminal.PiChain

  The public input's chain of `check_opening_terminal` (G:3245-3250): `__loop14` and the products
  it writes.
-/

module

public import LeanVM.Guest.B1.KeccakGkr.Lib
public import LeanVM.Guest.B1.Terminal.Template

/-!
# The public input's chain

`check_opening_terminal` writes `pi_chain[0] = 1`, `pi_chain[1] = rm + point1[0]` and runs
`__loop14` (`mul_range(GEN, g_log_mem)`), whose body at `x = g^k` writes
`pi_chain[k + 1] = pi_chain[k]·point1[k]`. `piChain_value`: for `1 ≤ k ≤ m`, `pi_chain[k]` is
`(rm + point1[0])·Π_{0 < i < k} point1[i]`.
-/

namespace LeanVM.Guest.B1.VerifySub

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.Verifier Finset

@[expose] public section

variable {rd : Reader}

/-- `__loop14`'s body. -/
def loop15T : List Stmt :=
  [.atom (.mul (.n 4) (.n 2) (.n 0)), .atom (.load (.n 5) (.n 4) 0),
    .atom (.mul (.n 6) (.n 3) (.n 0)), .atom (.load (.n 7) (.n 6) 0),
    .atom (.mul (.n 8) (.n 5) (.n 7)), .atom (.mul (.n 9) (.n 2) (.n 0)),
    .atom (.load (.n 8) (.n 9) 1), .atom (.const (.n 10) (word 2 0 0)),
    .atom (.mul (.n 11) (.n 0) (.n 10)), .atom (.add (.n 12) (.n 11) (.n 1)),
    .atom (.const (.n 13) (word 2 0 0)), .atom (.mul (.n 14) (.n 0) (.n 13)),
    .callIf (.n 12) "__loop14" [.n 14, .n 1, .n 2, .n 3], .ret []]

/-- `__loop14`, found by name, has four parameters and the body `loop15T`. -/
noncomputable def loop15Check : Bool :=
  match coreProgram.find? "__loop14" with
  | some fn => decide (fn.params = [.n 0, .n 1, .n 2, .n 3]) && stmtsEqb fn.body loop15T
  | none => false

theorem loop15Check_eq : loop15Check = true := by decide +kernel

theorem loop15Found : ∃ fn : Fn, coreProgram.find? "__loop14" = some fn ∧
    fn.params = [.n 0, .n 1, .n 2, .n 3] ∧ fn.body = loop15T := by
  have h := loop15Check_eq
  unfold loop15Check at h
  split at h
  · rename_i fn hf
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    exact ⟨fn, hf, h.1, stmtsEqb_sound h.2⟩
  · exact absurd h (by simp)

/-- One step of the chain at `x`: `chain[x·g] = chain[x]·p1[x]`. -/
def PiStep (rd : Reader) (chain p1 x : E) : Prop :=
  ∃ a b : E, LoadHolds rd (chain * x) 0 a ∧ LoadHolds rd (p1 * x) 0 b ∧
    LoadHolds rd (chain * x) 1 (a * b)

/-- **`__loop14`'s step.** -/
theorem loop15_step (d : ℕ) (x N chain p1 : E)
    (h : coreProgram.relN rd (d + 1) "__loop14" [x, N, chain, p1] []) :
    PiStep rd chain p1 x ∧
      (x * gen + N ≠ 0 → coreProgram.relN rd d "__loop14" [x * gen, N, chain, p1] []) := by
  obtain ⟨fn, hf, σ, hpar, hb⟩ := h
  obtain ⟨fn', hf', hp', hb'⟩ := loop15Found
  rw [hf'] at hf
  cases hf
  rw [hp'] at hpar
  rw [hb'] at hb
  simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true] at hpar
  obtain ⟨rfl, rfl, rfl, rfl⟩ := hpar
  simp only [loop15T, Stmt.HoldsList, Stmt.Holds, Atom.Holds, List.map_cons, List.map_nil] at hb
  obtain ⟨e4, l5, e6, l7, e8, e9, l8, e10, e11, e12, e13, e14, ⟨-, hcall, -⟩⟩ := hb
  refine ⟨⟨σ (.n 5), σ (.n 7), by rw [← e4]; exact l5, by rw [← e6]; exact l7, ?_⟩, fun hne ↦ ?_⟩
  · rw [← e8, ← e9]; exact l8
  · have e : σ (.n 12) = σ (.n 0) * gen + σ (.n 1) := by rw [e12, e11, e10, word_gen]
    have := hcall (by rw [e]; exact hne)
    rw [e14, e13, word_gen] at this
    exact this

/-- **The public input's chain**: from `chain[0] = 1`, `chain[1] = rm + p1[0]` and the steps at
`g^k`, `1 ≤ k < m`, every `chain[k]`, `1 ≤ k ≤ m`, is `(rm + p1[0])·Π_{0 < i < k} p1[i]`. -/
theorem piChain_value {chain p1 rm : E} {ps : List E} (hps : ReadsAt rd p1 ps) {m : ℕ}
    (hm : m ≤ ps.length) (h1 : LoadHolds rd chain 1 (rm + ps.getD 0 0))
    (hstep : ∀ k, 1 ≤ k → k < m → PiStep rd chain p1 (gen ^ k)) :
    ∀ k, 1 ≤ k → k ≤ m →
      LoadHolds rd chain k ((rm + ps.getD 0 0) * ∏ i ∈ Ico 1 k, ps.getD i 0) := by
  intro k hk1 hkm
  induction k with
  | zero => omega
  | succ k ih =>
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · simpa using h1
    · have ihk := ih hk (by omega)
      obtain ⟨a, b, la, lb, lab⟩ := hstep k hk (by omega)
      rw [loadHolds_mul_gen_pow, Nat.add_zero] at la lb
      rw [loadHolds_mul_gen_pow] at lab
      have ea := loadHolds_unique la ihk
      have hpk : LoadHolds rd p1 k (ps.getD k 0) := by
        rw [List.getD_eq_getElem _ _ (by omega)]; exact hps k (by omega)
      have eb := loadHolds_unique lb hpk
      rw [ea, eb] at lab
      rw [prod_Ico_succ_top (by omega), ← mul_assoc]
      exact lab

end
end LeanVM.Guest.B1.VerifySub
