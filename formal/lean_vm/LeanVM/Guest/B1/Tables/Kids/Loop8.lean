/-
  LeanVM.Guest.B1.Tables.Kids.Loop8

  `__loop7` (`verify_bus_gkr`'s copy of the point) loads from any region holding its two runs.
-/

module

public import LeanVM.Guest.B1.Tables.Kids.Loop9
public import LeanVM.Guest.B1.Gkr.Loop8

/-!
# `__loop7`, loading from a region

Iteration `k < K` of `__loop7` (`x = g^k`, the end `g^K`) reads `row·x` and writes `zeta·x`.
`loop8_relIn`: by induction on the derivation's depth, every iteration loads from `R` when the
runs `zeta` and `row` (`K` words each) lie in `R`.
-/

namespace LeanVM.Guest.B1.Tables

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Memory
open LeanVM.Protocol.Verifier (gen)

@[expose] public section

/-- `__loop7`'s statements before its `ret`. -/
def l8Pre : List Stmt := l8Body.dropLast

theorem l8Body_pre_eq : l8Body = l8Pre ++ [.ret []] := by simp [l8Pre, l8Body]

theorem l8_flat : l8Pre.all Stmt.flat = true := by decide +kernel

theorem l8_noDisp : l8Pre.all noDispB = true := by decide +kernel

theorem l8_loads : l8Pre.all (loadsViaB [(4, 1), (6, 1)]) = true := by decide +kernel

theorem l8_calls : l8Pre.filterMap Main.Stmt.callS =
    [(some (.n 9), "__loop7", [.n 11, .n 1, .n 2, .n 3], [])] := by decide +kernel

/-- **`__loop7` loads from `R`**, every iteration `k < K`. -/
theorem loop8_relIn {rd : Reader} {R : ℕ → Prop} {K : ℕ} {zeta row : E}
    (hz : PtrIn R zeta K) (hr : PtrIn R row K) :
    ∀ d k, k < K → coreProgram.relN rd d "__loop7" [gen ^ k, gen ^ K, zeta, row] [] →
      coreProgram.RelIn rd R "__loop7" [gen ^ k, gen ^ K, zeta, row] [] := by
  intro d
  induction d with
  | zero => intro k _ h; exact h.elim
  | succ d ih =>
    intro k hk h
    obtain ⟨fn, hf, hsem⟩ := h
    obtain ⟨fn', hf', hp, hb⟩ := l8Found
    rw [hf] at hf'
    obtain rfl := Option.some.inj hf'
    refine relIn_of_flat hf (by rw [hb, l8Body_pre_eq]) l8_flat hsem fun σ hpar hh ↦ ?_
    rw [hp] at hpar
    simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true] at hpar
    obtain ⟨p0, p1, p2, p3⟩ := hpar
    rw [hb] at hh
    simp only [l8Body, Stmt.HoldsList, Stmt.Holds, Atom.Holds, List.map_cons, List.map_nil] at hh
    obtain ⟨m4, -, m6, -, c7, m8, a9, c10, m11, ⟨-, hc, -⟩⟩ := hh
    rw [tb_word_gen] at c7 c10
    refine ⟨fun s hs ↦ dispOk_of_noDisp (List.all_eq_true.mp l8_noDisp s hs),
      loads_via l8_loads fun pb hpb ↦ ?_, fun c hcm ht ↦ ?_⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hpb
      rcases hpb with rfl | rfl
      · rw [m4, p3, p0]; exact ptrIn_mul (ptrIn_mono hr (by omega))
      · rw [m6, p2, p0]; exact ptrIn_mul (ptrIn_mono hz (by omega))
    · rw [filterMap_callSF l8_noDisp, l8_calls] at hcm
      simp only [List.map_cons, List.map_nil, List.mem_singleton] at hcm
      subst hcm
      simp only [Main.mkCall, decide_eq_true_eq] at ht ⊢
      have e11 : σ (.n 11) = gen ^ (k + 1) := by rw [m11, c10, p0, pow_succ]
      have e9 : σ (.n 9) = gen ^ (k + 1) + gen ^ K := by rw [a9, m8, c7, p0, p1, pow_succ]
      have hk1 : k + 1 < K := by
        rcases Nat.lt_or_ge (k + 1) K with h' | h'
        · exact h'
        · exfalso
          apply ht
          rw [e9, show k + 1 = K by omega, e_add_eq_zero_iff]
      have hrel := hc ht
      simp only [List.map_cons, List.map_nil, e11, p1, p2, p3] at hrel ⊢
      exact ih (k + 1) hk1 hrel

end
end LeanVM.Guest.B1.Tables
