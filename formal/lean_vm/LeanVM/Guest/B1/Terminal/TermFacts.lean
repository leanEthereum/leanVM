/-
  LeanVM.Guest.B1.Terminal.TermFacts

  `check_opening_terminal`'s body, checked by the kernel for its completeness: its evaluation
  pattern, its stores, its buffers, its calls.
-/

module

public import LeanVM.Guest.B1.Terminal.Holds
public import LeanVM.Guest.B1.Fwd.Canon
public import LeanVM.Guest.B1.Tables.FlatAt
public import LeanVM.Guest.Data.NameStrings

/-!
# `check_opening_terminal`'s body, for completeness

`termPre`, the body before its `ret` (`term_body'`): the head, the selectors, the claims' blocks
(`termClaims.1`) and the tail before its `ret`. By kernel evaluation: it defines its values in
order (`term_chk`, `1715` values), its only stores are the public input's chain's first two words
(`term_stores`), it is flat, takes no address, allocates its five buffers (`term_allocs`: the
prefix chains at `zeta` and `chi`, the public input's chain, the outputs' chain, the out-of-domain
claim's chain) and makes its 101 calls in order (`term_callSF`).
-/

namespace LeanVM.Guest.B1.VerifySub

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Guest.Memory LeanVM.Guest.B1.Fwd

@[expose] public section

/-- The tail before its `ret`. -/
def termTailPre : List Stmt := (termTailT 1694 1692 1693).dropLast

/-- **`check_opening_terminal`'s statements before its `ret`.** -/
def termPre : List Stmt := termHeadT ++ selsT ++ termClaims.1 ++ termTailPre

theorem termTail_split : termTailT 1694 1692 1693 = termTailPre ++ [.ret []] := by
  simp only [termTailPre, termTailT]; rfl

theorem termT_split : termT = termPre ++ [.ret []] := by
  rw [termT, termClaims_end, termTail_split, termPre]
  simp only [List.append_assoc]

theorem find_term : coreProgram.find? "check_opening_terminal" = some fn% «check_opening_terminal»
    :=
  coreProgram_find?_at (j := idx% «check_opening_terminal») rfl

theorem term_body' : (fn% «check_opening_terminal»).body = termPre ++ [.ret []] := by
  obtain ⟨fn, hf, -, hb⟩ := termFound
  rw [find_term, Option.some.injEq] at hf
  subst hf
  exact hb.trans termT_split

theorem term_params : (fn% «check_opening_terminal»).params = (List.range 20).map Core.V.n := by
  obtain ⟨fn, hf, hp, -⟩ := termFound
  rw [find_term, Option.some.injEq] at hf
  subst hf
  rw [hp]; rfl

theorem term_chk : chk 20 termT = some 1715 := by decide +kernel

theorem term_stores : storesOf 20 termT =
    [.load (.n 27) (.n 26) 0, .load (.n 29) (.n 26) 1] := by decide +kernel

theorem term_flat : termPre.all Stmt.flat = true := by decide +kernel

theorem term_addrs : termPre.filterMap Main.Stmt.addrS = [] := by decide +kernel

theorem term_allocs : termPre.filterMap Main.Stmt.allocSz =
    [(.n 20, .inl 35), (.n 22, .inl 35), (.n 26, .inl 35), (.n 1694, .inl 41), (.n 1709, .inl 31)] := by
  decide +kernel

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
    [(none, "eq_prefix_chain", [.n 20, .n 21, .n 1, .n 14, .n 4], []),
      (none, "eq_prefix_chain", [.n 22, .n 23, .n 2, .n 14, .n 5], []),
      (some (.n 31), name% «check_opening_terminal_loop0», [.n 32, .n 6, .n 26, .n 14], []),
      (none, "selector_tables", [.n 13, .n 14], [.n 43])] := by decide +kernel

theorem claims_callS : termClaims.1.filterMap Main.Stmt.callS = [] := by decide +kernel

theorem tail_callS : termTailPre.filterMap Main.Stmt.callS =
    [(none, "eq_prefix_chain", [.n 1694, .n 1695, .n 11, .n 14, .n 1697], []),
      (none, "ring_switch_weight", [.n 1699, .n 14, .n 12, .n 1701], [.n 1702]),
      (none, "eq_prefix_chain", [.n 1709, .n 1710, .n 18, .n 14, .n 19], [])] := by
  decide +kernel

/-- Committed column `c`'s selector's call. -/
noncomputable def selCall (σ : Val) (c : ℕ) : Option V × String × List V × List V :=
  (none, colSelNames.getD (logG (σ (.n (selKap c).2.1))) "",
    [.n (selStart c), .n 43, .n ((selKap c).2.2 + 1)], [.n (selV c)])

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
    [(none, "eq_prefix_chain", [.n 20, .n 21, .n 1, .n 14, .n 4], []),
      (none, "eq_prefix_chain", [.n 22, .n 23, .n 2, .n 14, .n 5], []),
      (some (.n 31), name% «check_opening_terminal_loop0», [.n 32, .n 6, .n 26, .n 14], []),
      (none, "selector_tables", [.n 13, .n 14], [.n 43])] ++
    (List.range Tables.nCommittedCols).map (selCall σ) ++
    [(none, "eq_prefix_chain", [.n 1694, .n 1695, .n 11, .n 14, .n 1697], []),
      (none, "ring_switch_weight", [.n 1699, .n 14, .n 12, .n 1701], [.n 1702]),
      (none, "eq_prefix_chain", [.n 1709, .n 1710, .n 18, .n 14, .n 19], [])] := by
  rw [termPre, List.filterMap_append, List.filterMap_append, List.filterMap_append,
    callSF_of_noDisp σ head_noDisp, head_callS, sels_callSF, callSF_of_noDisp σ claims_noDisp,
    claims_callS, callSF_of_noDisp σ tail_noDisp, tail_callS, List.append_nil]

end
end LeanVM.Guest.B1.VerifySub
