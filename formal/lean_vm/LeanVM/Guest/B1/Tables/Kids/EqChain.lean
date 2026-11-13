/-
  LeanVM.Guest.B1.Tables.Kids.EqChain

  `eq_prefix_chain` loads from any region holding the runs it reads and writes.
-/

module

public import LeanVM.Guest.B1.Tables.Kids.Walk
public import LeanVM.Guest.B1.Tables.Kids.Families
public import LeanVM.Guest.B1.Eq.EqPrefix

/-!
# `eq_prefix_chain`, loading from a region

`eq_prefix_chain_relIn`: on `count_g = g^n`, `n ≤ 40`, it dispatches to `eq_prefix_run__L{n}`,
which loads from `R` when the chain's `n + 1` words and `a`'s and `b1`'s `n` lie in `R`
(`eq_prefix_run_relIn`); it loads nothing itself.
-/

namespace LeanVM.Guest.B1.Tables

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Memory
open LeanVM.Protocol.Verifier (gen)

@[expose] public section

/-- `eq_prefix_chain`'s statements before its `ret`. -/
def epcPre : List Stmt :=
  [.atom (.const (.n 5) (word (2 ^ 40) 0)),
    .atom (.rangeCheck (.n 4) (.n 6) (.n 7) (.n 8) (.n 5)),
    .dispatch (.n 4) eqPrefixRunNames [.n 0, .n 1, .n 2, .n 3] [.n 9]]

theorem epc_body : Fn.body fn% «eq_prefix_chain» = epcPre ++ [.ret []] := by
  rw [B1.eq_prefix_chain_body]; rfl

theorem epc_flat : epcPre.all Stmt.flat = true := by decide +kernel

/-- **`eq_prefix_chain` loads from `R`.** -/
theorem eq_prefix_chain_relIn {rd : Reader} {R : ℕ → Prop} {chain seed a b1 : E} {n : ℕ}
    (hn : n ≤ 40) {rets : List E} (hc : PtrIn R chain (n + 1)) (ha : PtrIn R a n)
    (hb : PtrIn R b1 n)
    (h : coreProgram.Rel rd "eq_prefix_chain" [chain, seed, a, b1, gen ^ n] rets) :
    coreProgram.RelIn rd R "eq_prefix_chain" [chain, seed, a, b1, gen ^ n] rets := by
  refine relIn_of_flatRel B1.find_eq_prefix_chain epc_body epc_flat h fun σ hpar hh ↦ ?_
  rw [show Fn.params fn% «eq_prefix_chain» = [.n 0, .n 1, .n 2, .n 3, .n 4] from rfl] at hpar
  simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true] at hpar
  obtain ⟨p0, p1, p2, p3, p4⟩ := hpar
  rw [epc_body] at hh
  simp only [epcPre, List.cons_append, List.nil_append, Stmt.HoldsList, Stmt.Holds, Atom.Holds,
    List.map_cons, List.map_nil] at hh
  obtain ⟨-, -, ⟨j, hj, hx, hcall⟩, -⟩ := hh
  have hlen : eqPrefixRunNames.length = 41 := rfl
  have hjn : j = n := by
    rw [p4, gen_pow_eq_ofK] at hx
    exact gpow_injOn (by simp only [Set.mem_Iio]; omega) (by simp only [Set.mem_Iio]; omega)
      (ofK_injective hx).symm
  subst hjn
  refine ⟨fun s hs ↦ ?_, by simp [epcPre, Stmt.loadS], fun c hc ht ↦ ?_⟩
  · simp only [epcPre, List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl | rfl
    · trivial
    · trivial
    · exact ⟨j, hj, by omega, hx⟩
  · simp only [epcPre, Stmt.callSF, List.filterMap_cons, List.filterMap_nil, Main.Stmt.callS,
      List.map_cons, List.map_nil, List.mem_singleton] at hc
    subst hc
    have hlog : logG (σ (.n 4)) = j := by rw [hx]; exact logG_spec (by omega)
    simp only [Main.mkCall, hlog, List.map_cons, List.map_nil, p0, p1, p2, p3]
    have hname : eqPrefixRunNames[j] = eqPrefixRunNames.getD j "" := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj, Option.getD_some]
    rw [hname] at hcall
    simp only [p0, p1, p2, p3] at hcall
    exact eq_prefix_run_relIn (by omega) hc ha hb hcall

end
end LeanVM.Guest.B1.Tables
