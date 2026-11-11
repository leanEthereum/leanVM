/-
  LeanVM.Guest.B1.Gkr.Loop8Complete

  `__loop7`, completely: the point at `row` and at `zeta` gives its relation from `1` below
  `g^m`.
-/

module

public import LeanVM.Guest.B1.Gkr.Loop8
public import LeanVM.Guest.B1.Common.Loops

/-!
# `__loop7`, completely (G:1913-1914)

`l8_complete`: when the memory holds the same `m ≥ 1` words at `row` and at `zeta`, `__loop7`
holds from `1` below `g^m` (`loop_iff`, each iteration's atoms on the evident valuation).
-/

namespace LeanVM.Guest.B1.Tables

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Protocol LeanVM.Protocol.Verifier LeanVM.Guest.B1

@[expose] public section

/-- `__loop7`'s atoms. -/
def l8A : List Stmt := l8Body.take 9

theorem l8Body_eq : l8Body = l8A ++ [.callIf (.n 9) "__loop7" [.n 11, .n 1, .n 2, .n 3], .ret []] :=
  rfl

theorem l8A_atoms : AllAtoms l8A := by
  intro s hs
  simp only [l8A, l8Body, List.take, List.mem_cons, List.not_mem_nil, or_false] at hs
  rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact ⟨_, rfl⟩

set_option maxRecDepth 10000 in
/-- **`__loop7`, completely.** -/
theorem l8_complete {rd : Reader} {zeta row : E} {m : ℕ} (hm : 0 < m) (hmb : m < 2 ^ 62)
    {pt : List E} (hl : pt.length = m) (hr : TbReadsAt rd row pt) (hz : TbReadsAt rd zeta pt) :
    coreProgram.Rel rd "__loop7" [1, gen ^ m, zeta, row] [] := by
  obtain ⟨fn, hf, hp, hb⟩ := l8Found
  rw [l8Body_eq] at hb
  have hstep : ∀ d x, coreProgram.relN rd (d + 1) "__loop7" (x :: [gen ^ m, zeta, row]) [] ↔
      AtomsBody rd fn.params l8A (x :: [gen ^ m, zeta, row]) ∧ IsInK (x * gen + gen ^ m) ∧
        (x * gen + gen ^ m ≠ 0 →
          coreProgram.relN rd d "__loop7" (x * gen :: [gen ^ m, zeta, row]) []) := by
    intro d x
    refine loop_step_atoms hf hb l8A_atoms (fun σ hpar hall => ?_) d
    rw [hp] at hpar
    simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true] at hpar
    obtain ⟨h0, h1, h2, h3⟩ := hpar
    have g := fun a ha => hall a ha
    simp only [l8A, l8Body, List.take, List.mem_cons, List.not_mem_nil, or_false,
      Stmt.atom.injEq, forall_eq_or_imp, forall_eq, Atom.Holds] at g
    obtain ⟨-, -, -, -, c7, m8, a9, c10, m11⟩ := g
    rw [tb_word_gen] at c7 c10
    refine ⟨by rw [a9, m8, c7, h0, h1], ?_⟩
    simp only [List.map_cons, List.map_nil, m11, c10, h0, h1, h2, h3]
  rw [← pow_zero gen]
  refine (loop_iff hstep 0).mpr ⟨m, hm, rfl, first_hit_of_lt (by unfold ordG; omega) rfl,
    fun j _ hj => ?_⟩
  -- the iteration at `g^j`
  have hjl : j < pt.length := by omega
  refine ⟨B1.Val.ofArgs [gen ^ j, gen ^ m, zeta, row, row * gen ^ j, pt[j], zeta * gen ^ j,
    gen, gen ^ j * gen, gen ^ j * gen + gen ^ m, gen, gen ^ j * gen], ?_, ?_⟩
  · rw [hp]; rfl
  · intro a ha
    simp only [l8A, l8Body, List.take, List.mem_cons, List.not_mem_nil, or_false,
      Stmt.atom.injEq] at ha
    have lr : LoadHolds rd (row * gen ^ j) 0 pt[j] := by
      rw [tb_loadHolds_mul_gen_pow, Nat.add_zero]; exact hr j hjl
    have lz : LoadHolds rd (zeta * gen ^ j) 0 pt[j] := by
      rw [tb_loadHolds_mul_gen_pow, Nat.add_zero]; exact hz j hjl
    rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · rfl
    · exact lr
    · rfl
    · exact lz
    · exact tb_word_gen.symm
    · rfl
    · rfl
    · exact tb_word_gen.symm
    · rfl

end
end LeanVM.Guest.B1.Tables
