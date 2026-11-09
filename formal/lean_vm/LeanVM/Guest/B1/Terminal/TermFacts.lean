/-
  LeanVM.Guest.B1.Terminal.TermFacts

  `check_opening_terminal`'s body, checked by the kernel for its completeness: its evaluation
  pattern, its stores, its buffers, its calls.
-/

module

public import LeanVM.Guest.B1.Terminal.Holds
public import LeanVM.Guest.B1.Fwd.Canon
public import LeanVM.Guest.B1.Tables.FlatAt

/-!
# `check_opening_terminal`'s body, for completeness

`termPre`, the body before its `ret` (`term_body'`): the head, the selectors, the claims' blocks
(`termClaims.1`) and the tail before its `ret`. By kernel evaluation: it defines its values in
order (`term_chk`, `1782` values), its only stores are the public input's chain's first two words
(`term_stores`), it is flat, takes no address, allocates its four buffers (`term_allocs`: the
prefix chains at `zeta` and `chi`, the public input's chain, the outputs' chain) and makes its 107
calls in order (`term_callSF`).
-/

namespace LeanVM.Guest.B1.VerifySub

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Guest.Memory LeanVM.Guest.B1.Fwd

@[expose] public section

/-- The tail before its `ret`. -/
def termTailPre : List Stmt := (termTailT 1766 1764 1765).dropLast

/-- **`check_opening_terminal`'s statements before its `ret`.** -/
def termPre : List Stmt := termHeadT ++ selsT ++ termClaims.1 ++ termTailPre

theorem termTail_split : termTailT 1766 1764 1765 = termTailPre ++ [.ret []] := by
  simp only [termTailPre, termTailT]; rfl

theorem termT_split : termT = termPre ++ [.ret []] := by
  rw [termT, termClaims_end, termTail_split, termPre]
  simp only [List.append_assoc]

theorem find_term : coreProgram.find? "check_opening_terminal" = some Data.core17 :=
  Program.find?_of_indexOf? (j := 17) (by decide +kernel) rfl

theorem term_body' : Data.core17.body = termPre ++ [.ret []] := by
  obtain ⟨fn, hf, -, hb⟩ := termFound
  rw [find_term, Option.some.injEq] at hf
  subst hf
  exact hb.trans termT_split

theorem term_params : Data.core17.params = (List.range 18).map Core.V.n := by
  obtain ⟨fn, hf, hp, -⟩ := termFound
  rw [find_term, Option.some.injEq] at hf
  subst hf
  exact hp

theorem term_chk : chk 18 termT = some 1782 := by decide +kernel

theorem term_stores : storesOf 18 termT =
    [.load (.n 25) (.n 24) 0, .load (.n 27) (.n 24) 1] := by decide +kernel

theorem term_flat : termPre.all Stmt.flat = true := by decide +kernel

theorem term_addrs : termPre.filterMap Main.Stmt.addrS = [] := by decide +kernel

theorem term_allocs : termPre.filterMap Main.Stmt.allocSz =
    [(.n 18, .inl 35), (.n 20, .inl 35), (.n 24, .inl 35), (.n 1766, .inl 41)] := by decide +kernel

theorem term_not_loop : coreProgram.loop "check_opening_terminal" = false := by decide +kernel

/-! ## The calls -/

/-- No dispatch. -/
def noDispB : Stmt → Bool
  | .dispatch .. => false
  | _ => true

theorem callSF_of_noDisp (σ : Val) {l : List Stmt} (h : l.all noDispB = true) :
    l.filterMap (Stmt.callSF σ) = l.filterMap Main.Stmt.callS :=
  List.filterMap_congr fun s hs => by
    have := List.all_eq_true.mp h s hs
    cases s <;> simp_all [Stmt.callSF, noDispB]

theorem head_noDisp : termHeadT.all noDispB = true := by decide +kernel

theorem claims_noDisp : termClaims.1.all noDispB = true := by decide +kernel

theorem tail_noDisp : termTailPre.all noDispB = true := by decide +kernel

theorem head_callS : termHeadT.filterMap Main.Stmt.callS =
    [(none, "eq_prefix_chain", [.n 18, .n 19, .n 1, .n 14, .n 4], []),
      (none, "eq_prefix_chain", [.n 20, .n 21, .n 2, .n 14, .n 5], []),
      (some (.n 29), "__loop14", [.n 30, .n 6, .n 24, .n 14], []),
      (none, "selector_tables", [.n 13, .n 14], [.n 41])] := by decide +kernel

theorem claims_callS : termClaims.1.filterMap Main.Stmt.callS = [] := by decide +kernel

theorem tail_callS : termTailPre.filterMap Main.Stmt.callS =
    [(none, "eq_prefix_chain", [.n 1766, .n 1767, .n 11, .n 14, .n 1769], []),
      (none, "ring_switch_weight", [.n 1771, .n 14, .n 12, .n 1773], [.n 1774])] := by
  decide +kernel

/-- Committed column `c`'s selector's call. -/
noncomputable def selCall (σ : Val) (c : ℕ) : Option V × String × List V × List V :=
  (none, colSelNames.getD (logG (σ (.n (selKap c).2.1))) "",
    [.n (selStart c), .n 41, .n ((selKap c).2.2 + 1)], [.n (selV c)])

theorem kapT_callSF (σ : Val) (src adj r : ℕ) : (kapT src adj r).1.filterMap (Stmt.callSF σ) = [] := by
  unfold kapT; split <;> rfl

theorem selBlock_callSF (σ : Val) (c : ℕ) : (selBlockT c).filterMap (Stmt.callSF σ) = [selCall σ c] := by
  rw [selBlockT, List.filterMap_append, List.filterMap_append, selKap, kapT_callSF]
  rfl

theorem sels_callSF (σ : Val) :
    selsT.filterMap (Stmt.callSF σ) = (List.range Tables.nCommittedCols).map (selCall σ) := by
  rw [selsT, List.filterMap_flatMap,
    show (fun c => (selBlockT c).filterMap (Stmt.callSF σ)) = fun c => [selCall σ c] from
      funext fun c => selBlock_callSF σ c]
  generalize List.range Tables.nCommittedCols = l
  induction l with
  | nil => rfl
  | cons c l ih => simp only [List.flatMap_cons, List.map_cons, ih, List.singleton_append]

/-- **The calls, in order.** -/
theorem term_callSF (σ : Val) : termPre.filterMap (Stmt.callSF σ) =
    [(none, "eq_prefix_chain", [.n 18, .n 19, .n 1, .n 14, .n 4], []),
      (none, "eq_prefix_chain", [.n 20, .n 21, .n 2, .n 14, .n 5], []),
      (some (.n 29), "__loop14", [.n 30, .n 6, .n 24, .n 14], []),
      (none, "selector_tables", [.n 13, .n 14], [.n 41])] ++
    (List.range Tables.nCommittedCols).map (selCall σ) ++
    [(none, "eq_prefix_chain", [.n 1766, .n 1767, .n 11, .n 14, .n 1769], []),
      (none, "ring_switch_weight", [.n 1771, .n 14, .n 12, .n 1773], [.n 1774])] := by
  rw [termPre, List.filterMap_append, List.filterMap_append, List.filterMap_append,
    callSF_of_noDisp σ head_noDisp, head_callS, sels_callSF, callSF_of_noDisp σ claims_noDisp,
    claims_callS, callSF_of_noDisp σ tail_noDisp, tail_callS, List.append_nil]

end
end LeanVM.Guest.B1.VerifySub
