/-
  LeanVM.Guest.B1.Eq.EqPrefixRevIn

  `eq_prefix_run_rev` and `eq_prefix_chain_rev` load from any region holding the runs they read
  and write.
-/

module

public import LeanVM.Guest.B1.Tables.Kids.Walk
public import LeanVM.Guest.B1.Tables.Kids.Families
public import LeanVM.Guest.B1.Eq.EqPrefixRev
import LeanVM.Guest.ValRef
import LeanVM.Guest.Data.ValNames.«eq_prefix_chain_rev»
import LeanVM.Guest.StmtsAppend

/-!
# `eq_prefix_chain_rev`, loading from a region

`eq_prefix_run_rev_relIn`: `eq_prefix_run_rev__L{n}` (`n ≤ 32`, `[chain, out, src, b1]`) loads the
chain's `n + 1` words and `out`'s, `src`'s and `b1`'s `n` (`dloadCheck`, the kernel).
`eq_prefix_chain_rev_relIn`: on `count_g = g^n` it dispatches to it and loads nothing itself.
-/

namespace LeanVM.Guest.B1.Tables

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Memory
open LeanVM.Protocol.Verifier (gen)

@[expose] public section

theorem eprr_dload : ∀ n < 33, dloadCheck (eqPrefixRunRevNames.getD n "") [n + 1, n, n, n] = true := by
  decide +kernel

section
variable {rd : Reader} {R : ℕ → Prop}

theorem eq_prefix_run_rev_relIn {n : ℕ} (hn : n ≤ 32) {chain out src b1 : E} {rets : List E}
    (hc : PtrIn R chain (n + 1)) (ho : PtrIn R out n) (hs : PtrIn R src n) (hb : PtrIn R b1 n)
    (h : coreProgram.Rel rd (eqPrefixRunRevNames.getD n "") [chain, out, src, b1] rets) :
    coreProgram.RelIn rd R (eqPrefixRunRevNames.getD n "") [chain, out, src, b1] rets :=
  relIn_of_dload (eprr_dload n (by omega)) (fun p hp ↦ by
    simp only [List.length_cons, List.length_nil] at hp
    interval_cases p
    · exact fun _ ↦ hc
    · exact fun _ ↦ ho
    · exact fun _ ↦ hs
    · exact fun _ ↦ hb) h

end

/-- `eq_prefix_chain_rev`'s statements before its `ret`. -/
def epcrPre : List Stmt :=
  [.atom (.const (.n (val% «eq_prefix_chain_rev» "s0#0")) (word (2 ^ 32) 0)),
    .atom (.rangeCheck (.n (val% «eq_prefix_chain_rev» "count_g")) (.n (val% «eq_prefix_chain_rev» "s0#1")) (.n (val% «eq_prefix_chain_rev» "s0#2")) (.n (val% «eq_prefix_chain_rev» "s0#3")) (.n (val% «eq_prefix_chain_rev» "s0#0"))),
    .dispatch (.n (val% «eq_prefix_chain_rev» "count_g")) eqPrefixRunRevNames [.n (val% «eq_prefix_chain_rev» "chain"), .n (val% «eq_prefix_chain_rev» "out"), .n (val% «eq_prefix_chain_rev» "src"), .n (val% «eq_prefix_chain_rev» "b1")] [.n (val% «eq_prefix_chain_rev» "done")]]

theorem epcr_body : Fn.body fn% «eq_prefix_chain_rev» = epcrPre ⧺ [.ret []] := by
  rw [B1.eq_prefix_chain_rev_body]; rfl

theorem epcr_flat : epcrPre.all Stmt.flat = true := by decide +kernel

/-- **`eq_prefix_chain_rev` loads from `R`.** -/
theorem eq_prefix_chain_rev_relIn {rd : Reader} {R : ℕ → Prop} {chain out src b1 : E} {n : ℕ}
    (hn : n ≤ 32) {rets : List E} (hc : PtrIn R chain (n + 1)) (ho : PtrIn R out n)
    (hs : PtrIn R src n) (hb : PtrIn R b1 n)
    (h : coreProgram.Rel rd "eq_prefix_chain_rev" [chain, out, src, b1, gen ^ n] rets) :
    coreProgram.RelIn rd R "eq_prefix_chain_rev" [chain, out, src, b1, gen ^ n] rets := by
  refine relIn_of_flatRel B1.find_eq_prefix_chain_rev epcr_body epcr_flat h fun σ hpar hh ↦ ?_
  rw [show Fn.params fn% «eq_prefix_chain_rev» = [.n (val% «eq_prefix_chain_rev» "chain"), .n (val% «eq_prefix_chain_rev» "out"), .n (val% «eq_prefix_chain_rev» "src"), .n (val% «eq_prefix_chain_rev» "b1"), .n (val% «eq_prefix_chain_rev» "count_g")] from rfl] at hpar
  simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true] at hpar
  obtain ⟨p0, p1, p2, p3, p4⟩ := hpar
  rw [epcr_body] at hh
  simp only [epcrPre, List.cons_append, List.nil_append, Stmt.HoldsList, Stmt.Holds, Atom.Holds,
    List.map_cons, List.map_nil] at hh
  obtain ⟨-, -, ⟨j, hj, hx, hcall⟩, -⟩ := hh
  have hlen : eqPrefixRunRevNames.length = 33 := rfl
  have hjn : j = n := by
    rw [p4, gen_pow_eq_ofK] at hx
    exact gpow_injOn (by simp only [Set.mem_Iio]; omega) (by simp only [Set.mem_Iio]; omega)
      (ofK_injective hx).symm
  subst hjn
  refine ⟨fun s hs ↦ ?_, by simp [epcrPre, Stmt.loadS], fun c hc' ht ↦ ?_⟩
  · simp only [epcrPre, List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl | rfl
    · trivial
    · trivial
    · exact ⟨j, hj, by omega, hx⟩
  · simp only [epcrPre, Stmt.callSF, List.filterMap_cons, List.filterMap_nil, Main.Stmt.callS,
      List.map_cons, List.map_nil, List.mem_singleton] at hc'
    subst hc'
    have hlog : logG (σ (.n (val% «eq_prefix_chain_rev» "count_g"))) = j := by rw [hx]; exact logG_spec (by omega)
    simp only [Main.mkCall, hlog, List.map_cons, List.map_nil, p0, p1, p2, p3]
    have hname : eqPrefixRunRevNames[j] = eqPrefixRunRevNames.getD j "" := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj, Option.getD_some]
    rw [hname] at hcall
    simp only [p0, p1, p2, p3] at hcall
    exact eq_prefix_run_rev_relIn (by omega) hc ho hs hb hcall

end
end LeanVM.Guest.B1.Tables
