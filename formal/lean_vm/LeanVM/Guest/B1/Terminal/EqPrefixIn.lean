/-
  LeanVM.Guest.B1.Terminal.EqPrefixIn

  `eq_prefix_run` and `eq_prefix_chain` load only their chain and their two runs: their relations
  by trees loading from those regions (`Program.RelIn`).
-/

module

public import LeanVM.Guest.B1.Eq.EqPrefix
public import LeanVM.Guest.B1.Tables.FlatAt
public import LeanVM.Guest.Memory.LiftPure

/-!
# The prefix chains, loading their regions

`ep_relIn`: a relation of `eq_prefix_run__L{n}` (a leaf: its loads read the chain at `g^bc`,
offsets `0 .. n`, and the runs at `g^ba`, `g^bb`, offsets below `n`, `epLok`, kernel-checked) is
one loading only those regions. `eqc_relIn`: the same for `eq_prefix_chain`, whose only loads are
its callee's (a constant, a range check, a dispatch on `g^n`).
-/

namespace LeanVM.Guest.B1.VerifySub

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Protocol.Verifier hiding gpow
open LeanVM.Guest.Memory
open LeanVM.Guest.B1.Main (Layout MemL RegionL)

@[expose] public section

/-- The loads `eq_prefix_run__L{n}` makes: the chain (`0`) at offsets `0 .. n`, the runs (`2`,
`3`) below `n`. -/
def epLok (n : ℕ) : Atom → Bool
  | .load _ p off => (decide (p = .n 0) && decide (off ≤ n)) ||
      (decide (p = .n 2) && decide (off < n)) || (decide (p = .n 3) && decide (off < n))
  | _ => true

/-- A specialization of `eq_prefix_run`, found, its parameters `0 .. 3`, a leaf of `epLok n`. -/
noncomputable def epChk (n : ℕ) : Bool :=
  match coreProgram.find? (eqPrefixRunNames.getD n "") with
  | some fn => decide (fn.params = [.n 0, .n 1, .n 2, .n 3]) &&
      Lift.Stmt.leafOkList (epLok n) fn.body
  | none => false

theorem ep_chk : (List.range 41).all epChk = true := by decide +kernel

theorem ep_found {n : ℕ} (hn : n ≤ 40) : ∃ fn, coreProgram.find? (eqPrefixRunNames.getD n "") = some fn ∧
    fn.params = [.n 0, .n 1, .n 2, .n 3] ∧ Lift.Stmt.leafOkList (epLok n) fn.body = true := by
  have h := List.all_eq_true.mp ep_chk n (List.mem_range.2 (by omega))
  unfold epChk at h
  split at h
  · rename_i fn hf
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    exact ⟨fn, hf, h.1, h.2⟩
  · exact absurd h (by simp)

/-- **`eq_prefix_run__L{n}` loads its regions only.** -/
theorem ep_relIn {n : ℕ} (hn : n ≤ 40) {rd : Reader} {bc ba bb : ℕ} {seed : E} {rets : List E}
    {R : ℕ → Prop}
    (hR : ∀ i, (bc ≤ i ∧ i ≤ bc + n) ∨ (ba ≤ i ∧ i < ba + n) ∨ (bb ≤ i ∧ i < bb + n) → R i)
    (h : coreProgram.Rel rd (eqPrefixRunNames.getD n "")
      [ofK (addressOfIndex bc), seed, ofK (addressOfIndex ba), ofK (addressOfIndex bb)] rets) :
    coreProgram.RelIn rd R (eqPrefixRunNames.getD n "")
      [ofK (addressOfIndex bc), seed, ofK (addressOfIndex ba), ofK (addressOfIndex bb)] rets := by
  obtain ⟨fn, hf, hp, hleaf⟩ := ep_found hn
  refine Lift.relIn_of_leaf hf hleaf (fun σ es vs hpar hw A hA => ?_) h
  have hall := Lift.walk_leafOk (σ := σ) _ hleaf
  rw [hw] at hall
  rw [hp] at hpar
  simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true] at hpar
  obtain ⟨e0, -, e2, e3⟩ := hpar
  obtain ⟨e, he, hea⟩ := List.mem_filterMap.mp hA
  have hok := hall e he
  cases e with
  | atom a =>
    cases a with
    | load d p off =>
      simp only [Ev.loadAddr?, Option.some.injEq] at hea
      subst hea
      simp only [Lift.EvLeafOk, epLok, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at hok
      rcases hok with (⟨rfl, ho⟩ | ⟨rfl, ho⟩) | ⟨rfl, ho⟩
      · rw [e0, Main.addr_ofK]; exact ⟨_, rfl, hR _ (Or.inl ⟨by omega, by omega⟩)⟩
      · rw [e2, Main.addr_ofK]; exact ⟨_, rfl, hR _ (Or.inr (Or.inl ⟨by omega, by omega⟩))⟩
      · rw [e3, Main.addr_ofK]; exact ⟨_, rfl, hR _ (Or.inr (Or.inr ⟨by omega, by omega⟩))⟩
    | _ => simp [Ev.loadAddr?] at hea
  | _ => simp [Ev.loadAddr?] at hea

/-- `eq_prefix_chain`'s statements before its `ret`. -/
def eqcPre : List Stmt :=
  [.atom (.const (.n 5) (word (2 ^ 40) 0)),
    .atom (.rangeCheck (.n 4) (.n 6) (.n 7) (.n 8) (.n 5)),
    .dispatch (.n 4) eqPrefixRunNames [.n 0, .n 1, .n 2, .n 3] [.n 9]]

theorem eqPrefixRunNames_getElem {j : ℕ} (hj : j < eqPrefixRunNames.length) :
    eqPrefixRunNames[j] = eqPrefixRunNames.getD j "" := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj, Option.getD_some]

/-- **`eq_prefix_chain` loads its regions only**: its callee's. -/
theorem eqc_relIn {rd : Reader} {bc ba bb n : ℕ} (hn : n ≤ 40) {seed : E} {R : ℕ → Prop}
    (hR : ∀ i, (bc ≤ i ∧ i ≤ bc + n) ∨ (ba ≤ i ∧ i < ba + n) ∨ (bb ≤ i ∧ i < bb + n) → R i)
    (h : coreProgram.Rel rd "eq_prefix_chain"
      [ofK (addressOfIndex bc), seed, ofK (addressOfIndex ba), ofK (addressOfIndex bb), gen ^
          n] []) :
    coreProgram.RelIn rd R "eq_prefix_chain"
      [ofK (addressOfIndex bc), seed, ofK (addressOfIndex ba), ofK (addressOfIndex bb), gen ^ n]
          [] := by
  obtain ⟨σ, hp, hb⟩ := (rel_iff_sem find_eq_prefix_chain _ _).mp h
  have hbody : Fn.body fn% «eq_prefix_chain» = eqcPre ++ [.ret []] := core4_body
  rw [hbody] at hb
  rw [show Fn.params fn% «eq_prefix_chain» = [.n 0, .n 1, .n 2, .n 3, .n 4] from rfl] at hp
  simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true] at hp
  obtain ⟨e0, e1, e2, e3, e4⟩ := hp
  simp only [eqcPre, List.cons_append, List.nil_append, Stmt.HoldsList, Stmt.Holds,
    List.map_cons, List.map_nil] at hb
  obtain ⟨h5, hrc, ⟨j, hj, hx, hcall⟩, -⟩ := hb
  have hlen : eqPrefixRunNames.length = 41 := rfl
  have hjn : j = n := by
    rw [e4, gen_pow_eq_ofK] at hx
    exact gpow_injOn (by simp; omega) (by simp; omega) (ofK_injective hx).symm
  subst hjn
  have hlog : logG (σ (.n 4)) = j := by rw [hx]; exact logG_spec (by omega)
  have hw := walk_flat σ [] eqcPre (by decide) (fun s hs => by
    simp only [eqcPre, List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl | rfl
    · trivial
    · trivial
    · exact ⟨j, hj, by omega, hx⟩)
  rw [← hbody] at hw
  have hev : eqcPre.flatMap (flEvs σ) = [.atom (.const (.n 5) (word (2 ^ 40) 0)),
      .atom (.rangeCheck (.n 4) (.n 6) (.n 7) (.n 8) (.n 5)),
      .call (eqPrefixRunNames.getD j "") [.n 0, .n 1, .n 2, .n 3] [.n 9]] := by
    simp [eqcPre, flEvs, Main.slEvs, hlog]
  rw [hev] at hw
  refine relIn_of_walk coreProgram_wf find_eq_prefix_chain ?_ hw rfl ?_ ?_ ?_
  · show [Core.V.n 0, .n 1, .n 2, .n 3, .n 4].map σ = _
    simp only [List.map_cons, List.map_nil, e0, e1, e2, e3, e4]
  · intro e he
    simp only [List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl | rfl
    · exact h5
    · exact hrc
    · trivial
  · intro A hA
    simp [loadAddrs, Ev.loadAddr?] at hA
  · intro c hc _
    simp only [calls, List.filterMap_cons, Ev.call?, List.filterMap_nil, List.mem_singleton] at hc
    subst hc
    simp only [List.map_cons, List.map_nil, e0, e1, e2, e3]
    rw [eqPrefixRunNames_getElem hj] at hcall
    simp only [e0, e1, e2, e3] at hcall
    exact ep_relIn (by omega) hR hcall

end
end LeanVM.Guest.B1.VerifySub
