/-
  LeanVM.Guest.B1.Tables.VtC.ABound

  What `verify_tables`' bound (`AWeight`) reads of its calls and its rounds loop.
-/

module

public import LeanVM.Guest.B1.Tables.VtC.AComplete
public import LeanVM.Guest.B1.Tables.VtC.Calls
public import LeanVM.Guest.B1.Tables.FlatLiftT
public import LeanVM.Guest.Memory.LoopPre
public import LeanVM.Guest.Data.NameStrings
import LeanVM.Guest.ValRef
import LeanVM.Guest.Data.ValNames.«verify_tables»

/-!
# `verify_tables`, placed, within its bound

The callees' words come as hypotheses in G7's forms: every statically bounded callee `g` of
`vtKidS` within a constant `Kf g` (`TotalLe`), `shared_selector_tables` within `Ksh` on a run
length `g^n`, `n < 64` (`TotalLeOn`), `verify_tables_loop0`'s run within `K10` words an iteration
and its one phantom frame (`TotalLeOn … LoopPre`). Call by call (`vtCallBnd`): a call's callee's
constant (`Ksh` for the shared tables), a dispatch's largest arm's, the rounds loop's run `vtRunB` at
the honest round count `n`. Here: a call of the body by its statement (`flatCalls_getElem`), and
the honest values around the rounds loop's call (`vt_loopVals`); `AWeight` proves the bound,
`fs "verify_tables" + Σ sizes + Σ vtBs + ifFrames`.
-/

namespace LeanVM.Guest.B1.Tables

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Memory
open LeanVM.Guest.B1.Fwd
open LeanVM.Guest.B1.Main (Layout MemL RegionL)
open LeanVM.Protocol.Verifier (gen)

@[expose] public section

/-- A call's frame under `σ`, by its statement among the body's calls. -/
theorem flatCalls_getElem {σ : Val} : ∀ (pre : List Stmt) (i : ℕ) (c : Call),
    (flatCalls pre σ)[i]? = some c → ∃ s, (pre.filter callB)[i]? = some s ∧
      ∃ tup, Stmt.callSF σ s = some tup ∧ c = mkCall σ tup
  | [], _, _, h => by simp [flatCalls] at h
  | s :: ss, i, c, h => by
    cases hs : callB s
    · have hn : Stmt.callSF σ s = none := by
        cases s <;> simp_all [callB, Stmt.callSF, Main.Stmt.callS]
      have h' : (flatCalls ss σ)[i]? = some c := by
        simpa [flatCalls, List.filterMap_cons, hn] using h
      obtain ⟨s', h1, h2⟩ := flatCalls_getElem ss i c h'
      exact ⟨s', by simpa [List.filter_cons, hs] using h1, h2⟩
    · obtain ⟨tup, ht⟩ : ∃ tup, Stmt.callSF σ s = some tup := by
        cases s <;> simp_all [callB, Stmt.callSF, Main.Stmt.callS]
      rcases i with _ | i
      · simp only [flatCalls, List.filterMap_cons, ht, List.map_cons, List.getElem?_cons_zero,
          Option.some.injEq] at h
        exact ⟨s, by simp [hs], tup, ht, h.symm⟩
      · have h' : (flatCalls ss σ)[i]? = some c := by
          simpa [flatCalls, List.filterMap_cons, ht] using h
        obtain ⟨s', h1, h2⟩ := flatCalls_getElem ss i c h'
        exact ⟨s', by simpa [List.filter_cons, hs] using h1, h2⟩

theorem le_foldr_max {l : List ℕ} {a : ℕ} (h : a ∈ l) : a ≤ l.foldr max 0 := by
  induction l with
  | nil => simp at h
  | cons b l ih =>
    rcases List.mem_cons.mp h with rfl | h
    · exact le_max_left _ _
    · exact (ih h).trans (le_max_right _ _)

theorem getElem?_filter_mem {l : List Stmt} {p : Stmt → Bool} {i : ℕ} {s : Stmt}
    (h : (l.filter p)[i]? = some s) : s ∈ l ∧ p s = true := by
  have hm := List.mem_of_getElem? h
  exact ⟨List.mem_of_mem_filter hm, (List.mem_filter.mp hm).2⟩

/-- **The honest values around the rounds loop's call**: the round count `g^n`, the call's
condition `1 + g^n` and its counter's start `1`. -/
theorem vt_loopVals (H : VtHonest) (B B' : VtBases) (rd : Reader) :
    vtσ rd (vtW H B') (H.args B) (.n (val% «verify_tables» "g_zc_n")) = gen ^ H.n ∧
      vtσ rd (vtW H B') (H.args B) (.n (val% «verify_tables» "s73#1")) = 1 + gen ^ H.n ∧
      vtσ rd (vtW H B') (H.args B) (.n (val% «verify_tables» "s73#2")) = 1 := by
  have hl : (H.args B).length = 21 := rfl
  have g1 := vt_goodL (rd := rd) (w := vtW H B') hl 2286
    [.atom (.hint (.witness "zc_tau_max" (.stack [.n (val% «verify_tables» "g_zc_n")])))] (by decide +kernel)
  have g2 := vt_goodL (rd := rd) (w := vtW H B') hl 2351
    [.atom (.const (.n (val% «verify_tables» "s73#0")) (word 1 0)), .atom (.add (.n (val% «verify_tables» "s73#1")) (.n (val% «verify_tables» "s73#0")) (.n (val% «verify_tables» "g_zc_n"))),
      .atom (.const (.n (val% «verify_tables» "s73#2")) (word 1 0))] (by decide +kernel)
  generalize vtσ rd (vtW H B') (H.args B) = σ' at g1 g2 ⊢
  simp only [GoodL, GoodS, fixNe, Good, List.mem_cons, List.not_mem_nil, or_false,
    forall_eq, and_true] at g1 g2
  obtain ⟨c0, a0, c1⟩ := g2
  have w : σ' (.n (val% «verify_tables» "g_zc_n")) = gen ^ H.n := by rw [g1]; exact (vtW_ok H B').w2544
  exact ⟨w, by rw [a0, c0, w, tb_word_one], by rw [c1, tb_word_one]⟩

end
end LeanVM.Guest.B1.Tables
