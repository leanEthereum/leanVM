/-
  LeanVM.Guest.B1.KeccakGkr.CopyLoop

  The copy loops of `verify_keccak` (`__loop10`, `__loop11`, `__loop12`, G:2755-2756, 2824-2825,
  2919-2920): `dst[x] = src[x]` for `x` over `g^0 .. g^(m-1)`.
-/

module

public import LeanVM.Guest.B1.KeccakGkr.PackChain

namespace LeanVM.Guest.B1.VerifySub

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.Verifier

@[expose] public section

variable {rd : Reader}

/-- A copy loop's body, named `name`: at `x`, `dst·x` gets `src·x`'s word. -/
def copyLoopT (name : String) : List Stmt :=
  [.atom (.mul (.n 4) (.n 3) (.n 0)), .atom (.load (.n 5) (.n 4) 0), .atom (.mul (.n 6) (.n 2) (.n 0)),
    .atom (.load (.n 5) (.n 6) 0), .atom (.const (.n 7) (word 2 0)),
    .atom (.mul (.n 8) (.n 0) (.n 7)), .atom (.add (.n 9) (.n 8) (.n 1)),
    .atom (.const (.n 10) (word 2 0)), .atom (.mul (.n 11) (.n 0) (.n 10)),
    .callIf (.n 9) name [.n 11, .n 1, .n 2, .n 3], .ret []]

theorem copyLoop_body11 : Data.core265.body = copyLoopT "__loop10" := stmtsEqb_sound (by decide +kernel)
theorem copyLoop_body12 : Data.core269.body = copyLoopT "__loop11" := stmtsEqb_sound (by decide +kernel)
theorem copyLoop_body13 : Data.core271.body = copyLoopT "__loop12" := stmtsEqb_sound (by decide +kernel)

theorem find_copyLoop11 : coreProgram.find? "__loop10" = some Data.core265 :=
  Program.find?_of_indexOf? (j := 265) (by decide +kernel) rfl
theorem find_copyLoop12 : coreProgram.find? "__loop11" = some Data.core269 :=
  Program.find?_of_indexOf? (j := 269) (by decide +kernel) rfl
theorem find_copyLoop13 : coreProgram.find? "__loop12" = some Data.core271 :=
  Program.find?_of_indexOf? (j := 271) (by decide +kernel) rfl

/-- **A copy loop's step.** -/
theorem copyLoop_step {name : String} {fn : Fn} (hf : coreProgram.find? name = some fn)
    (hb : fn.body = copyLoopT name) (hp : fn.params = [V.n 0, .n 1, .n 2, .n 3]) (d : ℕ)
    (x N dst src : E) (h : coreProgram.relN rd (d + 1) name [x, N, dst, src] []) :
    (∃ v, LoadHolds rd (src * x) 0 v ∧ LoadHolds rd (dst * x) 0 v) ∧
      (x * gen + N ≠ 0 → coreProgram.relN rd d name [x * gen, N, dst, src] []) := by
  obtain ⟨fn', hf', σ, hpar, hbody⟩ := h
  rw [hf] at hf'
  cases hf'
  rw [hp] at hpar
  simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true] at hpar
  obtain ⟨rfl, rfl, rfl, rfl⟩ := hpar
  rw [hb] at hbody
  simp only [copyLoopT, Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hbody
  obtain ⟨e4, l5, e6, s5, e7, e8, e9, e10, e11, -, hcall, -⟩ := hbody
  refine ⟨⟨σ (.n 5), by rw [← e4]; exact l5, by rw [← e6]; exact s5⟩, fun hne ↦ ?_⟩
  have h9 : σ (.n 9) = σ (.n 0) * gen + σ (.n 1) := by rw [e9, e8, e7, word_gen]
  have h11 : σ (.n 11) = σ (.n 0) * gen := by rw [e11, e10, word_gen]
  have := hcall (by rw [h9]; exact hne)
  simpa [h11] using this

/-- **A copy loop** from `x = 1` with `N = g^m`, `0 < m < ordG`: `dst[j] = src[j]`, `j < m`. -/
theorem copyLoop_sound {name : String} {fn : Fn} (hf : coreProgram.find? name = some fn)
    (hb : fn.body = copyLoopT name) (hp : fn.params = [V.n 0, .n 1, .n 2, .n 3]) {N dst src : E}
    {m : ℕ} (hN : N = gen ^ m) (hm : m < ordG)
    (h : coreProgram.Rel rd name [1, N, dst, src] []) :
    ∀ j < m, ∃ v, LoadHolds rd src j v ∧ LoadHolds rd dst j v := by
  intro j hj
  have := loop_sound (P := coreProgram) (f := name) (ps := [N, dst, src]) (N := N)
    (B := fun x ↦ ∃ v, LoadHolds rd (src * x) 0 v ∧ LoadHolds rd (dst * x) 0 v)
    (fun d x hx ↦ copyLoop_step hf hb hp d x N dst src hx) hN hm 0 (by simpa using h) j
    (Nat.zero_le _) hj
  obtain ⟨v, h1, h2⟩ := this
  refine ⟨v, ?_, ?_⟩
  · have := (loadHolds_mul_gen_pow rd src j 0 v).1 h1
    simpa using this
  · have := (loadHolds_mul_gen_pow rd dst j 0 v).1 h2
    simpa using this

end
end LeanVM.Guest.B1.VerifySub
