/-
  LeanVM.Guest.B1.Gkr.GlCInZeta

  `verify_bus_gkr_loop0` (`verify_bus_gkr`'s copy of the point) loads from any region holding its
  two runs.
-/

module

public import LeanVM.Guest.B1.Tables.Kids.Loop9
public import LeanVM.Guest.B1.Gkr.Loop8
public import LeanVM.Guest.Data.NameStrings
import LeanVM.Guest.ValRef
import LeanVM.Guest.Data.ValNames.«verify_bus_gkr_loop0»

/-!
# `verify_bus_gkr_loop0`, loading from a region

Iteration `k < K` of `verify_bus_gkr_loop0` (`x = g^k`, the end `g^K`) reads `row·x` and writes
`zeta·x`. `vbz_relIn`: by induction on the derivation's depth, every iteration loads from `R` when
the runs `zeta` and `row` (`K` words each) lie in `R`.
-/

namespace LeanVM.Guest.B1.Tables

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Memory
open LeanVM.Protocol.Verifier (gen)

@[expose] public section

/-- `verify_bus_gkr_loop0`'s statements before its `ret`. -/
def vbzPre : List Stmt := l8Body.dropLast

theorem vbzBody_pre_eq : l8Body = vbzPre ++ [.ret []] := by simp [vbzPre, l8Body]

theorem vbz_flat : vbzPre.all Stmt.flat = true := by decide +kernel

theorem vbz_noDisp : vbzPre.all noDispB = true := by decide +kernel

theorem vbz_loads : vbzPre.all (loadsViaB [(4, 1), (6, 1)]) = true := by decide +kernel

theorem vbz_calls : vbzPre.filterMap Main.Stmt.callS =
    [(some (.n (val% «verify_bus_gkr_loop0» "s2#2")), name% «verify_bus_gkr_loop0», [.n (val% «verify_bus_gkr_loop0» "s2#4"), .n (val% «verify_bus_gkr_loop0» "bound"), .n (val% «verify_bus_gkr_loop0» "zeta"), .n (val% «verify_bus_gkr_loop0» "final_point_row")],
        [])] := by decide +kernel

/-- **`verify_bus_gkr_loop0` loads from `R`**, every iteration `k < K`. -/
theorem vbz_relIn {rd : Reader} {R : ℕ → Prop} {K : ℕ} {zeta row : E}
    (hz : PtrIn R zeta K) (hr : PtrIn R row K) :
    ∀ d k, k < K → coreProgram.relN rd d name% «verify_bus_gkr_loop0» [gen ^ k, gen ^ K, zeta,
        row] [] →
      coreProgram.RelIn rd R name% «verify_bus_gkr_loop0» [gen ^ k, gen ^ K, zeta, row] [] := by
  intro d
  induction d with
  | zero => intro k _ h; exact h.elim
  | succ d ih =>
    intro k hk h
    obtain ⟨fn, hf, hsem⟩ := h
    obtain ⟨fn', hf', hp, hb⟩ := l8Found
    rw [hf] at hf'
    obtain rfl := Option.some.inj hf'
    refine relIn_of_flat hf (by rw [hb, vbzBody_pre_eq]) vbz_flat hsem fun σ hpar hh ↦ ?_
    rw [hp] at hpar
    simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true] at hpar
    obtain ⟨p0, p1, p2, p3⟩ := hpar
    rw [hb] at hh
    simp only [l8Body, Stmt.HoldsList, Stmt.Holds, Atom.Holds, List.map_cons, List.map_nil] at hh
    obtain ⟨m4, -, m6, -, c7, m8, a9, c10, m11, ⟨-, hc, -⟩⟩ := hh
    rw [tb_word_gen] at c7 c10
    refine ⟨fun s hs ↦ dispOk_of_noDisp (List.all_eq_true.mp vbz_noDisp s hs),
      loads_via vbz_loads fun pb hpb ↦ ?_, fun c hcm ht ↦ ?_⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hpb
      rcases hpb with rfl | rfl
      · rw [m4, p3, p0]; exact ptrIn_mul (ptrIn_mono hr (by omega))
      · rw [m6, p2, p0]; exact ptrIn_mul (ptrIn_mono hz (by omega))
    · rw [filterMap_callSF vbz_noDisp, vbz_calls] at hcm
      simp only [List.map_cons, List.map_nil, List.mem_singleton] at hcm
      subst hcm
      simp only [Main.mkCall, decide_eq_true_eq] at ht ⊢
      have e11 : σ (.n (val% «verify_bus_gkr_loop0» "s2#4")) = gen ^ (k + 1) := by rw [m11, c10, p0, pow_succ]
      have e9 : σ (.n (val% «verify_bus_gkr_loop0» "s2#2")) = gen ^ (k + 1) + gen ^ K := by rw [a9, m8, c7, p0, p1, pow_succ]
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
