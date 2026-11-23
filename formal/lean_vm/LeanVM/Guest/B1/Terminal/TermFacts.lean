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
import LeanVM.Guest.ValRef
import LeanVM.Guest.Data.ValNames.«check_opening_terminal»

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
    [.load (.n (val% «check_opening_terminal» "s7#0")) (.n (val% «check_opening_terminal» "pi_chain")) 0, .load (.n (val% «check_opening_terminal» "s8#1")) (.n (val% «check_opening_terminal» "pi_chain")) 1] := by decide +kernel

theorem term_flat : termPre.all Stmt.flat = true := by decide +kernel

theorem term_addrs : termPre.filterMap Main.Stmt.addrS = [] := by decide +kernel

theorem term_allocs : termPre.filterMap Main.Stmt.allocSz =
    [(.n (val% «check_opening_terminal» "zeta_eq_chain"), .inl 35), (.n (val% «check_opening_terminal» "chi_eq_chain"), .inl 35), (.n (val% «check_opening_terminal» "pi_chain"), .inl 35), (.n (val% «check_opening_terminal» "out_eq_chain"), .inl 41), (.n (val% «check_opening_terminal» "ood_chain"), .inl 31)] := by
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
    [(none, "eq_prefix_chain", [.n (val% «check_opening_terminal» "zeta_eq_chain"), .n (val% «check_opening_terminal» "s1#0"), .n (val% «check_opening_terminal» "zeta"), .n (val% «check_opening_terminal» "point1"), .n (val% «check_opening_terminal» "g_bus_mu")], []),
      (none, "eq_prefix_chain", [.n (val% «check_opening_terminal» "chi_eq_chain"), .n (val% «check_opening_terminal» "s3#0"), .n (val% «check_opening_terminal» "chi"), .n (val% «check_opening_terminal» "point1"), .n (val% «check_opening_terminal» "g_zc_n")], []),
      (some (.n (val% «check_opening_terminal» "s9#1")), name% «check_opening_terminal_loop0», [.n (val% «check_opening_terminal» "s9#2"), .n (val% «check_opening_terminal» "g_log_mem"), .n (val% «check_opening_terminal» "pi_chain"), .n (val% «check_opening_terminal» "point1")], []),
      (none, "selector_tables", [.n (val% «check_opening_terminal» "point"), .n (val% «check_opening_terminal» "point1")], [.n (val% «check_opening_terminal» "sel_eq")])] := by decide +kernel

theorem claims_callS : termClaims.1.filterMap Main.Stmt.callS = [] := by decide +kernel

theorem tail_callS : termTailPre.filterMap Main.Stmt.callS =
    [(none, "eq_prefix_chain", [.n (val% «check_opening_terminal» "out_eq_chain"), .n (val% «check_opening_terminal» "s24#0"), .n (val% «check_opening_terminal» "z_vals"), .n (val% «check_opening_terminal» "point1"), .n (val% «check_opening_terminal» "s24#2")], []),
      (none, "ring_switch_weight", [.n (val% «check_opening_terminal» "rs_weight~2"), .n (val% «check_opening_terminal» "point1"), .n (val% «check_opening_terminal» "c_table"), .n (val% «check_opening_terminal» "rs_weight~4")], [.n (val% «check_opening_terminal» "rs_weight")]),
      (none, "eq_prefix_chain", [.n (val% «check_opening_terminal» "ood_chain"), .n (val% «check_opening_terminal» "s28#0"), .n (val% «check_opening_terminal» "ood_z"), .n (val% «check_opening_terminal» "point1"), .n (val% «check_opening_terminal» "gmv")], [])] := by
  decide +kernel

/-- Committed column `c`'s selector's call. -/
noncomputable def selCall (σ : Val) (c : ℕ) : Option V × String × List V × List V :=
  (none, colSelNames.getD (logG (σ (.n (selKap c).2.1))) "",
    [.n (selStart c), .n (val% «check_opening_terminal» "sel_eq"), .n ((selKap c).2.2 + 1)], [.n (selV c)])

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
    [(none, "eq_prefix_chain", [.n (val% «check_opening_terminal» "zeta_eq_chain"), .n (val% «check_opening_terminal» "s1#0"), .n (val% «check_opening_terminal» "zeta"), .n (val% «check_opening_terminal» "point1"), .n (val% «check_opening_terminal» "g_bus_mu")], []),
      (none, "eq_prefix_chain", [.n (val% «check_opening_terminal» "chi_eq_chain"), .n (val% «check_opening_terminal» "s3#0"), .n (val% «check_opening_terminal» "chi"), .n (val% «check_opening_terminal» "point1"), .n (val% «check_opening_terminal» "g_zc_n")], []),
      (some (.n (val% «check_opening_terminal» "s9#1")), name% «check_opening_terminal_loop0», [.n (val% «check_opening_terminal» "s9#2"), .n (val% «check_opening_terminal» "g_log_mem"), .n (val% «check_opening_terminal» "pi_chain"), .n (val% «check_opening_terminal» "point1")], []),
      (none, "selector_tables", [.n (val% «check_opening_terminal» "point"), .n (val% «check_opening_terminal» "point1")], [.n (val% «check_opening_terminal» "sel_eq")])] ++
    (List.range Tables.nCommittedCols).map (selCall σ) ++
    [(none, "eq_prefix_chain", [.n (val% «check_opening_terminal» "out_eq_chain"), .n (val% «check_opening_terminal» "s24#0"), .n (val% «check_opening_terminal» "z_vals"), .n (val% «check_opening_terminal» "point1"), .n (val% «check_opening_terminal» "s24#2")], []),
      (none, "ring_switch_weight", [.n (val% «check_opening_terminal» "rs_weight~2"), .n (val% «check_opening_terminal» "point1"), .n (val% «check_opening_terminal» "c_table"), .n (val% «check_opening_terminal» "rs_weight~4")], [.n (val% «check_opening_terminal» "rs_weight")]),
      (none, "eq_prefix_chain", [.n (val% «check_opening_terminal» "ood_chain"), .n (val% «check_opening_terminal» "s28#0"), .n (val% «check_opening_terminal» "ood_z"), .n (val% «check_opening_terminal» "point1"), .n (val% «check_opening_terminal» "gmv")], [])] := by
  rw [termPre, List.filterMap_append, List.filterMap_append, List.filterMap_append,
    callSF_of_noDisp σ head_noDisp, head_callS, sels_callSF, callSF_of_noDisp σ claims_noDisp,
    claims_callS, callSF_of_noDisp σ tail_noDisp, tail_callS, List.append_nil]

end
end LeanVM.Guest.B1.VerifySub
