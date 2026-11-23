/-
  LeanVM.Guest.B1.KeccakGkr.CopyLoop

  The copy loops of `verify_keccak` (`verify_keccak_loop0`, `verify_keccak_loop1`,
  `verify_keccak_loop2`): `dst[x] = src[x]` for `x` over `g^0 ..
  g^(m-1)`.
-/

module

public import LeanVM.Guest.B1.KeccakGkr.PackChain
public import LeanVM.Guest.Data.NameStrings
import LeanVM.Guest.ValRef
import LeanVM.Guest.Data.ValNames.«verify_keccak_loop0»
import LeanVM.Guest.Data.ValNames.«verify_keccak_loop1»
import LeanVM.Guest.Data.ValNames.«verify_keccak_loop2»

namespace LeanVM.Guest.B1.VerifySub

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.Verifier

@[expose] public section

variable {rd : Reader}

/-- A copy loop's body, named `name`: at `x`, `dst·x` gets `src·x`'s word. -/
def copyLoopT (name : String) : List Stmt :=
  [.atom (.mul (.n (val% «verify_keccak_loop0» «verify_keccak_loop1» «verify_keccak_loop2» "s0#0")) (.n 3) (.n (val% «verify_keccak_loop0» «verify_keccak_loop1» «verify_keccak_loop2» "xt"))), .atom (.load (.n (val% «verify_keccak_loop0» «verify_keccak_loop1» «verify_keccak_loop2» "s0#1")) (.n (val% «verify_keccak_loop0» «verify_keccak_loop1» «verify_keccak_loop2» "s0#0")) 0), .atom (.mul (.n (val% «verify_keccak_loop0» «verify_keccak_loop1» «verify_keccak_loop2» "s0#2")) (.n 2) (.n (val% «verify_keccak_loop0» «verify_keccak_loop1» «verify_keccak_loop2» "xt"))),
    .atom (.load (.n (val% «verify_keccak_loop0» «verify_keccak_loop1» «verify_keccak_loop2» "s0#1")) (.n (val% «verify_keccak_loop0» «verify_keccak_loop1» «verify_keccak_loop2» "s0#2")) 0), .atom (.const (.n (val% «verify_keccak_loop0» «verify_keccak_loop1» «verify_keccak_loop2» "s2#0")) (word 2 0)),
    .atom (.mul (.n (val% «verify_keccak_loop0» «verify_keccak_loop1» «verify_keccak_loop2» "s2#1")) (.n (val% «verify_keccak_loop0» «verify_keccak_loop1» «verify_keccak_loop2» "xt")) (.n (val% «verify_keccak_loop0» «verify_keccak_loop1» «verify_keccak_loop2» "s2#0"))), .atom (.add (.n (val% «verify_keccak_loop0» «verify_keccak_loop1» «verify_keccak_loop2» "s2#2")) (.n (val% «verify_keccak_loop0» «verify_keccak_loop1» «verify_keccak_loop2» "s2#1")) (.n (val% «verify_keccak_loop0» «verify_keccak_loop1» «verify_keccak_loop2» "bound"))),
    .atom (.const (.n (val% «verify_keccak_loop0» «verify_keccak_loop1» «verify_keccak_loop2» "s2#3")) (word 2 0)), .atom (.mul (.n (val% «verify_keccak_loop0» «verify_keccak_loop1» «verify_keccak_loop2» "s2#4")) (.n (val% «verify_keccak_loop0» «verify_keccak_loop1» «verify_keccak_loop2» "xt")) (.n (val% «verify_keccak_loop0» «verify_keccak_loop1» «verify_keccak_loop2» "s2#3"))),
    .callIf (.n (val% «verify_keccak_loop0» «verify_keccak_loop1» «verify_keccak_loop2» "s2#2")) name [.n (val% «verify_keccak_loop0» «verify_keccak_loop1» «verify_keccak_loop2» "s2#4"), .n (val% «verify_keccak_loop0» «verify_keccak_loop1» «verify_keccak_loop2» "bound"), .n 2, .n 3], .ret []]

theorem copyLoop_body11 : (fn% «verify_keccak_loop0»).body = copyLoopT name% «verify_keccak_loop0»
    := stmtsEqb_sound (by decide +kernel)
theorem copyLoop_body12 : (fn% «verify_keccak_loop1»).body = copyLoopT name% «verify_keccak_loop1»
    := stmtsEqb_sound (by decide +kernel)
theorem copyLoop_body13 : (fn% «verify_keccak_loop2»).body = copyLoopT name% «verify_keccak_loop2»
    := stmtsEqb_sound (by decide +kernel)

theorem find_copyLoop11 : coreProgram.find? name% «verify_keccak_loop0» = some
    fn% «verify_keccak_loop0» :=
  coreProgram_find?_at (j := idx% «verify_keccak_loop0») rfl
theorem find_copyLoop12 : coreProgram.find? name% «verify_keccak_loop1» = some
    fn% «verify_keccak_loop1» :=
  coreProgram_find?_at (j := idx% «verify_keccak_loop1») rfl
theorem find_copyLoop13 : coreProgram.find? name% «verify_keccak_loop2» = some
    fn% «verify_keccak_loop2» :=
  coreProgram_find?_at (j := idx% «verify_keccak_loop2») rfl

/-- **A copy loop's step.** -/
theorem copyLoop_step {name : String} {fn : Fn} (hf : coreProgram.find? name = some fn)
    (hb : fn.body = copyLoopT name) (hp : fn.params = [V.n (val% «verify_keccak_loop0» «verify_keccak_loop1» «verify_keccak_loop2» "xt"), .n (val% «verify_keccak_loop0» «verify_keccak_loop1» «verify_keccak_loop2» "bound"), .n 2, .n 3]) (d : ℕ)
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
  refine ⟨⟨σ (.n (val% «verify_keccak_loop0» «verify_keccak_loop1» «verify_keccak_loop2» "s0#1")), by rw [← e4]; exact l5, by rw [← e6]; exact s5⟩, fun hne ↦ ?_⟩
  have h9 : σ (.n (val% «verify_keccak_loop0» «verify_keccak_loop1» «verify_keccak_loop2» "s2#2")) = σ (.n (val% «verify_keccak_loop0» «verify_keccak_loop1» «verify_keccak_loop2» "xt")) * gen + σ (.n (val% «verify_keccak_loop0» «verify_keccak_loop1» «verify_keccak_loop2» "bound")) := by rw [e9, e8, e7, word_gen]
  have h11 : σ (.n (val% «verify_keccak_loop0» «verify_keccak_loop1» «verify_keccak_loop2» "s2#4")) = σ (.n (val% «verify_keccak_loop0» «verify_keccak_loop1» «verify_keccak_loop2» "xt")) * gen := by rw [e11, e10, word_gen]
  have := hcall (by rw [h9]; exact hne)
  simpa [h11] using this

/-- **A copy loop** from `x = 1` with `N = g^m`, `0 < m < ordG`: `dst[j] = src[j]`, `j < m`. -/
theorem copyLoop_sound {name : String} {fn : Fn} (hf : coreProgram.find? name = some fn)
    (hb : fn.body = copyLoopT name) (hp : fn.params = [V.n (val% «verify_keccak_loop0» «verify_keccak_loop1» «verify_keccak_loop2» "xt"), .n (val% «verify_keccak_loop0» «verify_keccak_loop1» «verify_keccak_loop2» "bound"), .n 2, .n 3]) {N dst src : E}
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
