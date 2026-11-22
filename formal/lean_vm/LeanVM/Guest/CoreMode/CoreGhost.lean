/-
  LeanVM.Guest.CoreMode.CoreGhost

  An honest valuation with ghost words: a function naming no ghost value keeps every fact of
  `HonB` (`HonF` but its residuals and linked cells) when its ghost values are set (`setG`).
-/

module

public import LeanVM.Guest.CoreMode.Core
public import LeanVM.Guest.CoreMode.HeapCTree

/-!
# Ghost words on the core route

A heap signature's ghost slot `j` is the value `V.n (GB + j)` of the function's own pass, a value its
body never names (`ngB`). So the valuation of an honest instance can be given any ghost words `gw`
(`setG σ gw`): its path, its events, its cells and its jumps are the same (`honB_setG`), and only its
residuals (which may name ghosts) and its linked cells (`GlF`, which pin the ghost words to the caller's
cells) are to be shown at the new valuation.
-/

namespace LeanVM.Guest.CoreMode

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Memory
open LeanVM.Guest.Bridge (stmtsOf)

@[expose] public section

variable {κ : ℕ}

/-- **The function names no ghost value**: fewer than `GB` parameters, every value and temporary of its
body, and every value of each of its statements, below `GB`. -/
def ngB (fn : Fn) : Bool :=
  Nat.blt fn.params.length GB && (Stmt.usesList fn.body ++ Stmt.tmpsList fn.body).all (fun v ↦ Nat.blt v.idx GB) &&
    (stmtsOf fn.body).all fun s ↦ (Stmt.uses s).all fun v ↦ Nat.blt v.idx GB

theorem calls_uses {es : List Ev} {i : ℕ} {c : Call} (h : (calls es)[i]? = some c) :
    ∃ e ∈ es, ∀ v ∈ c.args ++ c.rets, v ∈ e.uses := by
  have hm : c ∈ calls es := List.mem_of_getElem? h
  obtain ⟨e, he, hc⟩ := List.mem_filterMap.mp hm
  refine ⟨e, he, fun v hv ↦ ?_⟩
  cases e with
  | call f a r =>
    simp only [Ev.call?, Option.some.injEq] at hc
    subst hc
    simpa [Ev.uses] using hv
  | skip f a =>
    simp only [Ev.call?, Option.some.injEq] at hc
    subst hc
    simpa [Ev.uses] using hv
  | atom _ => simp [Ev.call?] at hc
  | inK _ => simp [Ev.call?] at hc

/-- **An honest valuation with ghost words**: its path, cells and jumps the same. -/
theorem honB_setG {img : MemoryImage κ} {Cf : CFun} {fp : ℕ} {σ : Val} {gw : List E} (h : HonB img Cf fp σ)
    (hng : ngB Cf.fn = true) : HonB img Cf fp (setG σ gw) := by
  simp only [ngB, Bool.and_eq_true, List.all_eq_true, Nat.blt_eq] at hng
  obtain ⟨⟨hnp, hu⟩, hs⟩ := hng
  have hU : ∀ v ∈ Stmt.usesList Cf.fn.body, setG σ gw v = σ v := fun v hv ↦
    setG_eq (hu v (List.mem_append_left _ hv))
  have hT : ∀ v ∈ Stmt.tmpsList Cf.fn.body, setG σ gw v = σ v := fun v hv ↦
    setG_eq (hu v (List.mem_append_right _ hv))
  have hW : walk (setG σ gw) Cf.fn.body = walk σ Cf.fn.body := walk_congr _ hU
  have hin : ∀ {es vs}, walk σ Cf.fn.body = .ret es vs → (∀ e ∈ es, ∀ v ∈ e.uses, v ∈ Stmt.usesList Cf.fn.body) ∧
      (es.flatMap Ev.tmps).Sublist (Stmt.tmpsList Cf.fn.body) ∧ ∀ v ∈ vs, v ∈ Stmt.usesList Cf.fn.body := by
    intro es vs hw
    have := walk_within (σ := σ) Cf.fn.body
    rw [hw] at this
    exact this
  have hev : ∀ {es vs}, walk σ Cf.fn.body = .ret es vs → ∀ e ∈ es, ∀ v ∈ e.uses ++ e.tmps, setG σ gw v = σ v := by
    intro es vs hw e he v hv
    obtain ⟨h1, h2, -⟩ := hin hw
    rcases List.mem_append.mp hv with hv | hv
    · exact hU v (h1 e he v hv)
    · exact hT v (h2.subset (List.mem_flatMap.mpr ⟨e, he, hv⟩))
  have hcl : ∀ {es vs}, walk σ Cf.fn.body = .ret es vs → ∀ {i : ℕ} {c : Call}, (calls es)[i]? = some c →
      ∀ v ∈ c.args ++ c.rets, setG σ gw v = σ v := by
    intro es vs hw i c hc v hv
    obtain ⟨e, he, hu'⟩ := calls_uses hc
    exact hev hw e he v (List.mem_append_left _ (hu' v hv))
  have hms : ∀ x arms, Stmt.match_ x arms ∈ stmtsOf Cf.fn.body → setG σ gw x = σ x := fun x arms hm ↦
    setG_eq (hs _ hm x (by simp [Stmt.uses]))
  have hds : ∀ x fs args rets, Stmt.dispatch x fs args rets ∈ stmtsOf Cf.fn.body → setG σ gw x = σ x :=
    fun x fs args rets hm ↦ setG_eq (hs _ hm x (by simp [Stmt.uses]))
  have hrw : ∀ {es vs}, walk (setG σ gw) Cf.fn.body = .ret es vs → walk σ Cf.fn.body = .ret es vs := fun hw ↦ by
    rw [← hW]; exact hw
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, h.main⟩
  · obtain ⟨es, vs, rd, hw, hh⟩ := h.path
    exact ⟨es, vs, rd, by rw [hW]; exact hw, fun e he ↦ (holds_congr (hev hw e he)).mpr (hh e he)⟩
  · intro es vs hw a p ha hp
    have hw' := hrw hw
    have hpu : p ∈ (Ev.atom a).uses := by
      cases a with
      | load d p' off =>
        simp only [ptrOf, Option.some.injEq] at hp
        subst hp
        simp [Ev.uses, atomUses]
      | hint hn =>
        simp only [ptrOf, Option.map_eq_some_iff] at hp
        obtain ⟨⟨p', off, len⟩, hh, rfl⟩ := hp
        simpa [Ev.uses, atomUses] using hintHeap_uses hh
      | _ => simp [ptrOf] at hp
    rw [hev hw' _ ha p (List.mem_append_left _ hpu)]
    exact h.ptr es vs hw' a p ha hp
  · intro hn es vs hw p r rs ha
    have hw' := hrw hw
    rw [hev hw' _ ha p (List.mem_append_left _ (by simp [Ev.uses, atomUses]))]
    exact h.fa hn es vs hw' p r rs ha
  · intro k hk
    rw [setG_eq (show (V.n k).idx < GB by show k < GB; omega)]
    exact h.par k hk
  · intro es vs hw v hv
    have hw' := hrw hw
    rw [hU v ((hin hw').2.2 v hv)]
    exact h.rets es vs hw' v hv
  · intro es vs hw k hk
    have hw' := hrw hw
    rw [hU _ ((hin hw').2.2 _ (List.getElem_mem hk))]
    exact h.retc es vs hw' k hk
  · intro es vs hw i c q s hc htk hs'
    have hw' := hrw hw
    obtain ⟨kfp, h1, h2, h3, h4, h5⟩ := h.kid es vs hw' i c q s hc htk hs'
    refine ⟨kfp, h1, h2, h3, fun k hk ↦ ?_, fun k hk ↦ ?_⟩
    · rw [hcl hw' hc _ (List.mem_append_left _ (List.getElem_mem hk))]; exact h4 k hk
    · rw [hcl hw' hc _ (List.mem_append_right _ (List.getElem_mem hk))]; exact h5 k hk
  · intro es vs hw
    exact h.tgt es vs (hrw hw)
  · obtain ⟨hz, hnz, hself, hpc, hcond, harm, hsel, hdsel⟩ := h.jc
    refine ⟨hz, hnz, hself, hpc, fun es vs hw c hc ↦ ?_, fun x arms hm od a ha hax k t hk ht ↦ ?_,
      fun es vs hw x arms hm ↦ ?_, fun es vs hw x fs args rets hm ↦ ?_⟩
    · have hw' := hrw hw
      rw [hev hw' _ hc c (by simp [Ev.uses])]
      exact hcond es vs hw' c hc
    · rw [hms x arms hm] at hk
      exact harm x arms hm od a ha hax k t hk ht
    · rw [hms x arms hm]
      exact hsel es vs (hrw hw) x arms hm
    · rw [hds x fs args rets hm]
      exact hdsel es vs (hrw hw) x fs args rets hm
  · intro es vs hw e he
    have hw' := hrw hw
    exact (holds_congr (hev hw' e he)).mpr (h.holds es vs hw' e he)
  · intro es vs hw i c hc hl off oc od q S hoff hoc hod hq hf hso hS
    have hw' := hrw hw
    obtain ⟨h1, h2, h3, h4⟩ := h.tail es vs hw' i c hc hl off oc od q S hoff hoc hod hq hf hso hS
    refine ⟨h1, h2, h3, fun k hk ↦ ?_⟩
    rw [hcl hw' hc _ (List.mem_append_left _ (List.getElem_mem hk))]
    exact h4 k hk

end

end LeanVM.Guest.CoreMode
