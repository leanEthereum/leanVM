/-
  LeanVM.Guest.B1.Tables.Vt.BcShare

  `verify_tables`' bytecode share: the slot sumcheck's four rounds, its point in `bc_point`, the
  bytecode's value read after it, and the closing check against the slot weights' fold.
-/

module

public import LeanVM.Guest.B1.Tables.Vt.Fresh
public import LeanVM.Guest.B1.Fs.TailRound
public import LeanVM.Guest.B1.Gkr.Spec
public import LeanVM.Protocol.EndToEnd.Complete.BusShare
import LeanVM.Guest.ValRef
import LeanVM.Guest.Data.ValNames.«verify_tables»

/-!
# The bytecode share

After the framework's four words, the share `S` and the first round's `c0`, `c2` ride the stream
(`vt_fresh`); the first round's challenge is squeezed after them, its claim
`c0 + r (S + (1 + r) c2)` computed in place, and the three other rounds are `opening_tail_round`
calls. Each challenge is stored in `bc_point`. The bytecode's value is then read, and the last
claim checked against `fp_w` folded at the four challenges (`multilinearEval`) times the value.

`vt_bc`: from the sponge after the framework's words, `bytecodeShare` reads `S`, `c0`, `c2`, the
three rounds' six words and the value, and returns the share, the point and the value, leaving the
value waiting on the last round's capacity.
-/

namespace LeanVM.Guest.B1.Tables

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Protocol.EndToEnd.Complete (multilinearEval_eq_dot)

@[expose] public section

/-- A plain round of `sumcheck _ 3` on the carried capacity, then the rounds after it. -/
theorem vt_tail_cons (cap : List E) (c0 c2 claim : E) {rest : List (Option E)} {ys pt : List E}
    {fin : E} {s2 : Fs}
    (h2 : RunsTo (sumcheck (c0 + ((⟨cap, []⟩ : Fs).absorbAll [c0, c2] dsObserve).squeeze.1 *
        (claim + (1 + ((⟨cap, []⟩ : Fs).absorbAll [c0, c2] dsObserve).squeeze.1) * c2)) 3 rest)
      ((⟨cap, []⟩ : Fs).absorbAll [c0, c2] dsObserve).squeeze.2 ys (pt, fin) s2) :
    RunsTo (sumcheck claim 3 (none :: rest)) ⟨cap, []⟩ ([c0, c2] ++ ys)
      (((⟨cap, []⟩ : Fs).absorbAll [c0, c2] dsObserve).squeeze.1 :: pt, fin) s2 := by
  rw [tail_eval] at h2
  exact runsTo_sumcheck_cons (runsTo_roundPolyNone ⟨cap, []⟩ claim c0 [c2] 3 rfl (by decide)) h2

/-- `opening_tail_round`'s returns, by its meaning. -/
theorem vt_otr {rd : Reader} {f0 f1 f2 f3 f4 cur claim tabs : E} {rets : List E}
    (h : coreProgram.Rel rd "opening_tail_round" [f0, f1, f2, f3, f4, cur, claim, tabs] rets) :
    ∃ c0 c2 : E, ReadsAt rd cur [c0, c2] ∧
      rets = ((⟨[f0, f1, f2, f3, f4], []⟩ : Fs).absorbAll [c0, c2] dsObserve).squeeze.2.cap ++
        [cur * gen ^ 2, c0 + ((⟨[f0, f1, f2, f3, f4], []⟩ : Fs).absorbAll [c0, c2]
          dsObserve).squeeze.1 * (claim + (1 + ((⟨[f0, f1, f2, f3, f4], []⟩ : Fs).absorbAll
          [c0, c2] dsObserve).squeeze.1) * c2),
          ((⟨[f0, f1, f2, f3, f4], []⟩ : Fs).absorbAll [c0, c2] dsObserve).squeeze.1] :=
  (opening_tail_round_holds rd _ _).mp h

/-- An eight-word return split as five capacity cells and three words. -/
theorem vt_split8 {a0 a1 a2 a3 a4 a5 a6 a7 p q r : E} {C : List E} (hC : C.length = 5)
    (h : [a0, a1, a2, a3, a4, a5, a6, a7] = C ++ [p, q, r]) :
    [a0, a1, a2, a3, a4] = C ∧ a5 = p ∧ a6 = q ∧ a7 = r := by
  match C, hC with
  | [c0, c1, c2, c3, c4], _ =>
    simp only [List.cons_append, List.nil_append, List.cons.injEq] at h
    obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, -⟩ := h
    subst h0 h1 h2 h3 h4
    exact ⟨rfl, h5, h6, h7⟩

/-- A list of length `16` is its sixteen entries. -/
theorem vt_list16 (w : List E) (hw : w.length = 16) :
    w = (List.range 16).map fun i ↦ w.getD i 0 := by
  apply List.ext_getElem (by simp [hw])
  intro i h1 h2
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h1]

set_option maxRecDepth 10000 in
/-- **The bytecode share.** -/
theorem vt_bc {rd : Reader} {σ : Val} (h : VtH rd σ) {weights : List E}
    (hwl : weights.length = 16) (hW : TbReadsAt rd (σ (.n (val% «verify_tables» "fp_w"))) weights) (low : List E) :
    ∃ ys : List E, ys.length = 6 ∧ TbReadsAt rd (σ (.n (val% «verify_tables» "cursor@1")) * gen ^ 7) (ys ++ [σ (.n (val% «verify_tables» "x@8"))]) ∧
      TbReadsAt rd (σ (.n (val% «verify_tables» "bc_point"))) [σ (.n (val% «verify_tables» "nxt[0]@2")), σ (.n (val% «verify_tables» "bc_r@1")), σ (.n (val% «verify_tables» "bc_r@2")), σ (.n (val% «verify_tables» "bc_r@3"))] ∧
      σ (.n (val% «verify_tables» "cursor@4")) = σ (.n (val% «verify_tables» "cursor@1")) * gen ^ 7 * gen ^ 6 ∧
      [σ (.n (val% «verify_tables» "sp[0]@2")), σ (.n (val% «verify_tables» "sp[1]@2")), σ (.n (val% «verify_tables» "sp[2]@2")), σ (.n (val% «verify_tables» "sp[3]@2")), σ (.n (val% «verify_tables» "sp[4]@2"))] =
        [σ (.n (val% «verify_tables» "bfs0@3")), σ (.n (val% «verify_tables» "bfs1@3")), σ (.n (val% «verify_tables» "bfs2@3")), σ (.n (val% «verify_tables» "bfs3@3")), σ (.n (val% «verify_tables» "bfs4@3"))] ∧
      σ (.n (val% «verify_tables» "rate[0]@3")) = σ (.n (val% «verify_tables» "x@8")) ∧
      RunsTo (bytecodeShare weights low)
        ((⟨[σ (.n (val% «verify_tables» "fs0")), σ (.n (val% «verify_tables» "fs1")), σ (.n (val% «verify_tables» "fs2")), σ (.n (val% «verify_tables» "fs3")), σ (.n (val% «verify_tables» "fs4"))], []⟩ : Fs).absorbAll
          [σ (.n (val% «verify_tables» "x@1")), σ (.n (val% «verify_tables» "x@2")), σ (.n (val% «verify_tables» "x@3")), σ (.n (val% «verify_tables» "x@4"))] dsObserve)
        ([σ (.n (val% «verify_tables» "x@5")), σ (.n (val% «verify_tables» "x@6")), σ (.n (val% «verify_tables» "x@7"))] ++ ys ++ [σ (.n (val% «verify_tables» "x@8"))])
        (σ (.n (val% «verify_tables» "x@5")), low ++ [σ (.n (val% «verify_tables» "nxt[0]@2")), σ (.n (val% «verify_tables» "bc_r@1")), σ (.n (val% «verify_tables» "bc_r@2")), σ (.n (val% «verify_tables» "bc_r@3"))], σ (.n (val% «verify_tables» "x@8")))
        ((⟨[σ (.n (val% «verify_tables» "bfs0@3")), σ (.n (val% «verify_tables» "bfs1@3")), σ (.n (val% «verify_tables» "bfs2@3")), σ (.n (val% «verify_tables» "bfs3@3")), σ (.n (val% «verify_tables» "bfs4@3"))], []⟩ : Fs).absorb
          (σ (.n (val% «verify_tables» "x@8"))) dsObserve) := by
  obtain ⟨-, hr0, hcap0, d43, d47, d51⟩ := vt_fresh h
  have s0 := h.atomAt 1626 (.load (.n (val% «verify_tables» "nxt[0]@2")) (.n (val% «verify_tables» "bc_point")) 0) (by decide +kernel)
  have a1932 := h.atomAt 1627 (.const (.n (val% «verify_tables» "bc_claim@1~0")) (word 1 0)) (by decide +kernel)
  have a1933 := h.atomAt 1628 (.add (.n (val% «verify_tables» "bc_claim@1~1")) (.n (val% «verify_tables» "bc_claim@1~0")) (.n (val% «verify_tables» "nxt[0]@2"))) (by decide +kernel)
  have a1934 := h.atomAt 1629 (.mul (.n (val% «verify_tables» "bc_claim@1~2")) (.n (val% «verify_tables» "bc_claim@1~1")) (.n (val% «verify_tables» "bc_msg[2]"))) (by decide +kernel)
  have a1935 := h.atomAt 1630 (.add (.n (val% «verify_tables» "bc_claim@1~3")) (.n (val% «verify_tables» "bc_msg[0]")) (.n (val% «verify_tables» "bc_claim@1~2"))) (by decide +kernel)
  have a1936 := h.atomAt 1631 (.mul (.n (val% «verify_tables» "bc_claim@1~4")) (.n (val% «verify_tables» "nxt[0]@2")) (.n (val% «verify_tables» "bc_claim@1~3"))) (by decide +kernel)
  have a1937 := h.atomAt 1632 (.add (.n (val% «verify_tables» "bc_claim@1")) (.n (val% «verify_tables» "bc_msg[1]")) (.n (val% «verify_tables» "bc_claim@1~4"))) (by decide +kernel)
  have a1938 := h.atomAt 1633 (.const (.n (val% «verify_tables» "bfs0@1~8")) (word 128 0)) (by decide +kernel)
  have a1939 := h.atomAt 1634 (.mul (.n (val% «verify_tables» "bfs0@1~9")) (.n (val% «verify_tables» "cursor@1")) (.n (val% «verify_tables» "bfs0@1~8"))) (by decide +kernel)
  have k1 := h.callAt 1635 "opening_tail_round" [.n (val% «verify_tables» "nxt[8]@2"), .n (val% «verify_tables» "nxt[9]@2"), .n (val% «verify_tables» "nxt[10]@2"), .n (val% «verify_tables» "nxt[11]@2"), .n (val% «verify_tables» "nxt[12]@2"),
    .n (val% «verify_tables» "bfs0@1~9"), .n (val% «verify_tables» "bc_claim@1"), .n (val% «verify_tables» "tabs")] [.n (val% «verify_tables» "bfs0@1"), .n (val% «verify_tables» "bfs1@1"), .n (val% «verify_tables» "bfs2@1"), .n (val% «verify_tables» "bfs3@1"), .n (val% «verify_tables» "bfs4@1"), .n (val% «verify_tables» "cursor@2"), .n (val% «verify_tables» "bc_claim@2"),
    .n (val% «verify_tables» "bc_r@1")] (by decide +kernel)
  have s1 := h.atomAt 1636 (.load (.n (val% «verify_tables» "bc_r@1")) (.n (val% «verify_tables» "bc_point")) 1) (by decide +kernel)
  have k2 := h.callAt 1637 "opening_tail_round" [.n (val% «verify_tables» "bfs0@1"), .n (val% «verify_tables» "bfs1@1"), .n (val% «verify_tables» "bfs2@1"), .n (val% «verify_tables» "bfs3@1"), .n (val% «verify_tables» "bfs4@1"),
    .n (val% «verify_tables» "cursor@2"), .n (val% «verify_tables» "bc_claim@2"), .n (val% «verify_tables» "tabs")] [.n (val% «verify_tables» "bfs0@2"), .n (val% «verify_tables» "bfs1@2"), .n (val% «verify_tables» "bfs2@2"), .n (val% «verify_tables» "bfs3@2"), .n (val% «verify_tables» "bfs4@2"), .n (val% «verify_tables» "cursor@3"), .n (val% «verify_tables» "bc_claim@3"),
    .n (val% «verify_tables» "bc_r@2")] (by decide +kernel)
  have s2 := h.atomAt 1638 (.load (.n (val% «verify_tables» "bc_r@2")) (.n (val% «verify_tables» "bc_point")) 2) (by decide +kernel)
  have k3 := h.callAt 1639 "opening_tail_round" [.n (val% «verify_tables» "bfs0@2"), .n (val% «verify_tables» "bfs1@2"), .n (val% «verify_tables» "bfs2@2"), .n (val% «verify_tables» "bfs3@2"), .n (val% «verify_tables» "bfs4@2"),
    .n (val% «verify_tables» "cursor@3"), .n (val% «verify_tables» "bc_claim@3"), .n (val% «verify_tables» "tabs")] [.n (val% «verify_tables» "bfs0@3"), .n (val% «verify_tables» "bfs1@3"), .n (val% «verify_tables» "bfs2@3"), .n (val% «verify_tables» "bfs3@3"), .n (val% «verify_tables» "bfs4@3"), .n (val% «verify_tables» "cursor@4"), .n (val% «verify_tables» "bc_claim@4"),
    .n (val% «verify_tables» "bc_r@3")] (by decide +kernel)
  have s3 := h.atomAt 1640 (.load (.n (val% «verify_tables» "bc_r@3")) (.n (val% «verify_tables» "bc_point")) 3) (by decide +kernel)
  have c0 := h.atomAt 1641 (.copy (.n (val% «verify_tables» "sp[0]@2")) (.n (val% «verify_tables» "bfs0@3"))) (by decide +kernel)
  have c1 := h.atomAt 1642 (.copy (.n (val% «verify_tables» "sp[1]@2")) (.n (val% «verify_tables» "bfs1@3"))) (by decide +kernel)
  have c2 := h.atomAt 1643 (.copy (.n (val% «verify_tables» "sp[2]@2")) (.n (val% «verify_tables» "bfs2@3"))) (by decide +kernel)
  have c3 := h.atomAt 1644 (.copy (.n (val% «verify_tables» "sp[3]@2")) (.n (val% «verify_tables» "bfs3@3"))) (by decide +kernel)
  have c4 := h.atomAt 1645 (.copy (.n (val% «verify_tables» "sp[4]@2")) (.n (val% «verify_tables» "bfs4@3"))) (by decide +kernel)
  have lv := h.atomAt 1646 (.load (.n (val% «verify_tables» "x@8")) (.n (val% «verify_tables» "cursor@4")) 0) (by decide +kernel)
  have cv := h.atomAt 1647 (.copy (.n (val% «verify_tables» "rate[0]@3")) (.n (val% «verify_tables» "x@8"))) (by decide +kernel)
  -- the fold of `fp_w`
  have l0 := h.atomAt 1649 (.load (.n (val% «verify_tables» "r0")) (.n (val% «verify_tables» "bc_point")) 0) (by decide +kernel)
  have w0 := h.atomAt 1650 (.load (.n (val% «verify_tables» "w_lo@1")) (.n (val% «verify_tables» "fp_w")) 0) (by decide +kernel)
  have w1 := h.atomAt 1651 (.load (.n (val% «verify_tables» "s48.u0.s1#0")) (.n (val% «verify_tables» "fp_w")) 1) (by decide +kernel)
  have a1957 := h.atomAt 1652 (.add (.n (val% «verify_tables» "s48.u0.s1#1")) (.n (val% «verify_tables» "w_lo@1")) (.n (val% «verify_tables» "s48.u0.s1#0"))) (by decide +kernel)
  have a1958 := h.atomAt 1653 (.mul (.n (val% «verify_tables» "s48.u0.s1#2")) (.n (val% «verify_tables» "r0")) (.n (val% «verify_tables» "s48.u0.s1#1"))) (by decide +kernel)
  have a1959 := h.atomAt 1654 (.add (.n (val% «verify_tables» "w_fold[0]")) (.n (val% «verify_tables» "w_lo@1")) (.n (val% «verify_tables» "s48.u0.s1#2"))) (by decide +kernel)
  have w2 := h.atomAt 1655 (.load (.n (val% «verify_tables» "w_lo@2")) (.n (val% «verify_tables» "fp_w")) 2) (by decide +kernel)
  have w3 := h.atomAt 1656 (.load (.n (val% «verify_tables» "s48.u1.s1#0")) (.n (val% «verify_tables» "fp_w")) 3) (by decide +kernel)
  have a1962 := h.atomAt 1657 (.add (.n (val% «verify_tables» "s48.u1.s1#1")) (.n (val% «verify_tables» "w_lo@2")) (.n (val% «verify_tables» "s48.u1.s1#0"))) (by decide +kernel)
  have a1963 := h.atomAt 1658 (.mul (.n (val% «verify_tables» "s48.u1.s1#2")) (.n (val% «verify_tables» "r0")) (.n (val% «verify_tables» "s48.u1.s1#1"))) (by decide +kernel)
  have a1964 := h.atomAt 1659 (.add (.n (val% «verify_tables» "w_fold[1]")) (.n (val% «verify_tables» "w_lo@2")) (.n (val% «verify_tables» "s48.u1.s1#2"))) (by decide +kernel)
  have w4 := h.atomAt 1660 (.load (.n (val% «verify_tables» "w_lo@3")) (.n (val% «verify_tables» "fp_w")) 4) (by decide +kernel)
  have w5 := h.atomAt 1661 (.load (.n (val% «verify_tables» "s48.u2.s1#0")) (.n (val% «verify_tables» "fp_w")) 5) (by decide +kernel)
  have a1967 := h.atomAt 1662 (.add (.n (val% «verify_tables» "s48.u2.s1#1")) (.n (val% «verify_tables» "w_lo@3")) (.n (val% «verify_tables» "s48.u2.s1#0"))) (by decide +kernel)
  have a1968 := h.atomAt 1663 (.mul (.n (val% «verify_tables» "s48.u2.s1#2")) (.n (val% «verify_tables» "r0")) (.n (val% «verify_tables» "s48.u2.s1#1"))) (by decide +kernel)
  have a1969 := h.atomAt 1664 (.add (.n (val% «verify_tables» "w_fold[2]")) (.n (val% «verify_tables» "w_lo@3")) (.n (val% «verify_tables» "s48.u2.s1#2"))) (by decide +kernel)
  have w6 := h.atomAt 1665 (.load (.n (val% «verify_tables» "w_lo@4")) (.n (val% «verify_tables» "fp_w")) 6) (by decide +kernel)
  have w7 := h.atomAt 1666 (.load (.n (val% «verify_tables» "s48.u3.s1#0")) (.n (val% «verify_tables» "fp_w")) 7) (by decide +kernel)
  have a1972 := h.atomAt 1667 (.add (.n (val% «verify_tables» "s48.u3.s1#1")) (.n (val% «verify_tables» "w_lo@4")) (.n (val% «verify_tables» "s48.u3.s1#0"))) (by decide +kernel)
  have a1973 := h.atomAt 1668 (.mul (.n (val% «verify_tables» "s48.u3.s1#2")) (.n (val% «verify_tables» "r0")) (.n (val% «verify_tables» "s48.u3.s1#1"))) (by decide +kernel)
  have a1974 := h.atomAt 1669 (.add (.n (val% «verify_tables» "w_fold[3]")) (.n (val% «verify_tables» "w_lo@4")) (.n (val% «verify_tables» "s48.u3.s1#2"))) (by decide +kernel)
  have w8 := h.atomAt 1670 (.load (.n (val% «verify_tables» "w_lo@5")) (.n (val% «verify_tables» "fp_w")) 8) (by decide +kernel)
  have w9 := h.atomAt 1671 (.load (.n (val% «verify_tables» "s48.u4.s1#0")) (.n (val% «verify_tables» "fp_w")) 9) (by decide +kernel)
  have a1977 := h.atomAt 1672 (.add (.n (val% «verify_tables» "s48.u4.s1#1")) (.n (val% «verify_tables» "w_lo@5")) (.n (val% «verify_tables» "s48.u4.s1#0"))) (by decide +kernel)
  have a1978 := h.atomAt 1673 (.mul (.n (val% «verify_tables» "s48.u4.s1#2")) (.n (val% «verify_tables» "r0")) (.n (val% «verify_tables» "s48.u4.s1#1"))) (by decide +kernel)
  have a1979 := h.atomAt 1674 (.add (.n (val% «verify_tables» "w_fold[4]")) (.n (val% «verify_tables» "w_lo@5")) (.n (val% «verify_tables» "s48.u4.s1#2"))) (by decide +kernel)
  have w10 := h.atomAt 1675 (.load (.n (val% «verify_tables» "w_lo@6")) (.n (val% «verify_tables» "fp_w")) 10) (by decide +kernel)
  have w11 := h.atomAt 1676 (.load (.n (val% «verify_tables» "s48.u5.s1#0")) (.n (val% «verify_tables» "fp_w")) 11) (by decide +kernel)
  have a1982 := h.atomAt 1677 (.add (.n (val% «verify_tables» "s48.u5.s1#1")) (.n (val% «verify_tables» "w_lo@6")) (.n (val% «verify_tables» "s48.u5.s1#0"))) (by decide +kernel)
  have a1983 := h.atomAt 1678 (.mul (.n (val% «verify_tables» "s48.u5.s1#2")) (.n (val% «verify_tables» "r0")) (.n (val% «verify_tables» "s48.u5.s1#1"))) (by decide +kernel)
  have a1984 := h.atomAt 1679 (.add (.n (val% «verify_tables» "w_fold[5]")) (.n (val% «verify_tables» "w_lo@6")) (.n (val% «verify_tables» "s48.u5.s1#2"))) (by decide +kernel)
  have w12 := h.atomAt 1680 (.load (.n (val% «verify_tables» "w_lo@7")) (.n (val% «verify_tables» "fp_w")) 12) (by decide +kernel)
  have w13 := h.atomAt 1681 (.load (.n (val% «verify_tables» "s48.u6.s1#0")) (.n (val% «verify_tables» "fp_w")) 13) (by decide +kernel)
  have a1987 := h.atomAt 1682 (.add (.n (val% «verify_tables» "s48.u6.s1#1")) (.n (val% «verify_tables» "w_lo@7")) (.n (val% «verify_tables» "s48.u6.s1#0"))) (by decide +kernel)
  have a1988 := h.atomAt 1683 (.mul (.n (val% «verify_tables» "s48.u6.s1#2")) (.n (val% «verify_tables» "r0")) (.n (val% «verify_tables» "s48.u6.s1#1"))) (by decide +kernel)
  have a1989 := h.atomAt 1684 (.add (.n (val% «verify_tables» "w_fold[6]")) (.n (val% «verify_tables» "w_lo@7")) (.n (val% «verify_tables» "s48.u6.s1#2"))) (by decide +kernel)
  have w14 := h.atomAt 1685 (.load (.n (val% «verify_tables» "w_lo@8")) (.n (val% «verify_tables» "fp_w")) 14) (by decide +kernel)
  have w15 := h.atomAt 1686 (.load (.n (val% «verify_tables» "s48.u7.s1#0")) (.n (val% «verify_tables» "fp_w")) 15) (by decide +kernel)
  have a1992 := h.atomAt 1687 (.add (.n (val% «verify_tables» "s48.u7.s1#1")) (.n (val% «verify_tables» "w_lo@8")) (.n (val% «verify_tables» "s48.u7.s1#0"))) (by decide +kernel)
  have a1993 := h.atomAt 1688 (.mul (.n (val% «verify_tables» "s48.u7.s1#2")) (.n (val% «verify_tables» "r0")) (.n (val% «verify_tables» "s48.u7.s1#1"))) (by decide +kernel)
  have a1994 := h.atomAt 1689 (.add (.n (val% «verify_tables» "w_fold[7]")) (.n (val% «verify_tables» "w_lo@8")) (.n (val% «verify_tables» "s48.u7.s1#2"))) (by decide +kernel)
  have l1 := h.atomAt 1690 (.load (.n (val% «verify_tables» "rj@1")) (.n (val% «verify_tables» "bc_point")) 1) (by decide +kernel)
  have a1996 := h.atomAt 1691 (.add (.n (val% «verify_tables» "s49.u1.s1.u0.s2#0")) (.n (val% «verify_tables» "w_fold[0]")) (.n (val% «verify_tables» "w_fold[1]"))) (by decide +kernel)
  have a1997 := h.atomAt 1692 (.mul (.n (val% «verify_tables» "s49.u1.s1.u0.s2#1")) (.n (val% «verify_tables» "rj@1")) (.n (val% «verify_tables» "s49.u1.s1.u0.s2#0"))) (by decide +kernel)
  have a1998 := h.atomAt 1693 (.add (.n (val% «verify_tables» "w_fold[8]")) (.n (val% «verify_tables» "w_fold[0]")) (.n (val% «verify_tables» "s49.u1.s1.u0.s2#1"))) (by decide +kernel)
  have a1999 := h.atomAt 1694 (.add (.n (val% «verify_tables» "s49.u1.s1.u1.s2#0")) (.n (val% «verify_tables» "w_fold[2]")) (.n (val% «verify_tables» "w_fold[3]"))) (by decide +kernel)
  have a2000 := h.atomAt 1695 (.mul (.n (val% «verify_tables» "s49.u1.s1.u1.s2#1")) (.n (val% «verify_tables» "rj@1")) (.n (val% «verify_tables» "s49.u1.s1.u1.s2#0"))) (by decide +kernel)
  have a2001 := h.atomAt 1696 (.add (.n (val% «verify_tables» "w_fold[9]")) (.n (val% «verify_tables» "w_fold[2]")) (.n (val% «verify_tables» "s49.u1.s1.u1.s2#1"))) (by decide +kernel)
  have a2002 := h.atomAt 1697 (.add (.n (val% «verify_tables» "s49.u1.s1.u2.s2#0")) (.n (val% «verify_tables» "w_fold[4]")) (.n (val% «verify_tables» "w_fold[5]"))) (by decide +kernel)
  have a2003 := h.atomAt 1698 (.mul (.n (val% «verify_tables» "s49.u1.s1.u2.s2#1")) (.n (val% «verify_tables» "rj@1")) (.n (val% «verify_tables» "s49.u1.s1.u2.s2#0"))) (by decide +kernel)
  have a2004 := h.atomAt 1699 (.add (.n (val% «verify_tables» "w_fold[10]")) (.n (val% «verify_tables» "w_fold[4]")) (.n (val% «verify_tables» "s49.u1.s1.u2.s2#1"))) (by decide +kernel)
  have a2005 := h.atomAt 1700 (.add (.n (val% «verify_tables» "s49.u1.s1.u3.s2#0")) (.n (val% «verify_tables» "w_fold[6]")) (.n (val% «verify_tables» "w_fold[7]"))) (by decide +kernel)
  have a2006 := h.atomAt 1701 (.mul (.n (val% «verify_tables» "s49.u1.s1.u3.s2#1")) (.n (val% «verify_tables» "rj@1")) (.n (val% «verify_tables» "s49.u1.s1.u3.s2#0"))) (by decide +kernel)
  have a2007 := h.atomAt 1702 (.add (.n (val% «verify_tables» "w_fold[11]")) (.n (val% «verify_tables» "w_fold[6]")) (.n (val% «verify_tables» "s49.u1.s1.u3.s2#1"))) (by decide +kernel)
  have l2 := h.atomAt 1703 (.load (.n (val% «verify_tables» "rj@2")) (.n (val% «verify_tables» "bc_point")) 2) (by decide +kernel)
  have a2009 := h.atomAt 1704 (.add (.n (val% «verify_tables» "s49.u2.s1.u0.s2#0")) (.n (val% «verify_tables» "w_fold[8]")) (.n (val% «verify_tables» "w_fold[9]"))) (by decide +kernel)
  have a2010 := h.atomAt 1705 (.mul (.n (val% «verify_tables» "s49.u2.s1.u0.s2#1")) (.n (val% «verify_tables» "rj@2")) (.n (val% «verify_tables» "s49.u2.s1.u0.s2#0"))) (by decide +kernel)
  have a2011 := h.atomAt 1706 (.add (.n (val% «verify_tables» "w_fold[12]")) (.n (val% «verify_tables» "w_fold[8]")) (.n (val% «verify_tables» "s49.u2.s1.u0.s2#1"))) (by decide +kernel)
  have a2012 := h.atomAt 1707 (.add (.n (val% «verify_tables» "s49.u2.s1.u1.s2#0")) (.n (val% «verify_tables» "w_fold[10]")) (.n (val% «verify_tables» "w_fold[11]"))) (by decide +kernel)
  have a2013 := h.atomAt 1708 (.mul (.n (val% «verify_tables» "s49.u2.s1.u1.s2#1")) (.n (val% «verify_tables» "rj@2")) (.n (val% «verify_tables» "s49.u2.s1.u1.s2#0"))) (by decide +kernel)
  have a2014 := h.atomAt 1709 (.add (.n (val% «verify_tables» "w_fold[13]")) (.n (val% «verify_tables» "w_fold[10]")) (.n (val% «verify_tables» "s49.u2.s1.u1.s2#1"))) (by decide +kernel)
  have l3 := h.atomAt 1710 (.load (.n (val% «verify_tables» "rj@3")) (.n (val% «verify_tables» "bc_point")) 3) (by decide +kernel)
  have a2016 := h.atomAt 1711 (.add (.n (val% «verify_tables» "s49.u3.s1.u0.s2#0")) (.n (val% «verify_tables» "w_fold[12]")) (.n (val% «verify_tables» "w_fold[13]"))) (by decide +kernel)
  have a2017 := h.atomAt 1712 (.mul (.n (val% «verify_tables» "s49.u3.s1.u0.s2#1")) (.n (val% «verify_tables» "rj@3")) (.n (val% «verify_tables» "s49.u3.s1.u0.s2#0"))) (by decide +kernel)
  have a2018 := h.atomAt 1713 (.add (.n (val% «verify_tables» "w_fold[14]")) (.n (val% «verify_tables» "w_fold[12]")) (.n (val% «verify_tables» "s49.u3.s1.u0.s2#1"))) (by decide +kernel)
  have a2019 := h.atomAt 1714 (.mul (.n (val% «verify_tables» "s50#0")) (.n (val% «verify_tables» "w_fold[14]")) (.n (val% «verify_tables» "x@8"))) (by decide +kernel)
  have a2020 := h.atomAt 1715 (.assertEq (.n (val% «verify_tables» "bc_claim@4")) (.n (val% «verify_tables» "s50#0"))) (by decide +kernel)
  simp only [Atom.Holds] at s0 a1932 a1933 a1934 a1935 a1936 a1937 a1938 a1939 s1 s2 s3
  simp only [Atom.Holds] at c0 c1 c2 c3 c4 lv cv l0 w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12
  simp only [Atom.Holds] at w13 w14 w15 l1 l2 l3 a2020
  simp only [Atom.Holds] at a1957 a1958 a1959 a1962 a1963 a1964 a1967 a1968 a1969 a1972 a1973
  simp only [Atom.Holds] at a1974 a1977 a1978 a1979 a1982 a1983 a1984 a1987 a1988 a1989 a1992
  simp only [Atom.Holds] at a1993 a1994 a1996 a1997 a1998 a1999 a2000 a2001 a2002 a2003 a2004
  simp only [Atom.Holds] at a2005 a2006 a2007 a2009 a2010 a2011 a2012 a2013 a2014 a2016 a2017
  simp only [Atom.Holds] at a2018 a2019
  simp only [List.map_cons, List.map_nil] at k1 k2 k3
  -- the three tail rounds
  obtain ⟨x0, x1, hx01, e1⟩ := vt_otr k1
  obtain ⟨x2, x3, hx23, e2⟩ := vt_otr k2
  obtain ⟨x4, x5, hx45, e3⟩ := vt_otr k3
  obtain ⟨q1, u1, v1, r1⟩ := vt_split8 (by rfl) e1
  obtain ⟨q2, u2, v2, r2⟩ := vt_split8 (by rfl) e2
  obtain ⟨q3, u3, v3, r3⟩ := vt_split8 (by rfl) e3
  -- the sponge before the share, and after its first round
  set F0 : Fs := (⟨[σ (.n (val% «verify_tables» "fs0")), σ (.n (val% «verify_tables» "fs1")), σ (.n (val% «verify_tables» "fs2")), σ (.n (val% «verify_tables» "fs3")), σ (.n (val% «verify_tables» "fs4"))], []⟩ : Fs).absorbAll
    [σ (.n (val% «verify_tables» "x@1")), σ (.n (val% «verify_tables» "x@2")), σ (.n (val% «verify_tables» "x@3")), σ (.n (val% «verify_tables» "x@4"))] dsObserve with hF0
  have hF : ((F0.absorb (σ (.n (val% «verify_tables» "x@5"))) dsObserve).absorb (σ (.n (val% «verify_tables» "x@6"))) dsObserve).absorbAll
      [σ (.n (val% «verify_tables» "x@7"))] dsObserve = vtFreshFs σ := by
    simp only [hF0, vtFreshFs, vtFreshWords, Fs.absorbAll, List.foldl_cons, List.foldl_nil]
  have hF2 : (vtFreshFs σ).squeeze.2 =
      ⟨[σ (.n (val% «verify_tables» "nxt[8]@2")), σ (.n (val% «verify_tables» "nxt[9]@2")), σ (.n (val% «verify_tables» "nxt[10]@2")), σ (.n (val% «verify_tables» "nxt[11]@2")), σ (.n (val% «verify_tables» "nxt[12]@2"))], []⟩ := by
    rw [show (vtFreshFs σ).squeeze.2 = ⟨(vtFreshFs σ).squeeze.2.cap, []⟩ from rfl, ← hcap0]
    rfl
  -- the claims
  have hw128 : σ (.n (val% «verify_tables» "bfs0@1~8")) = gen ^ 7 := by
    rw [a1938, show (128 : ℕ) = 2 ^ 7 by norm_num, tb_word_two_pow (by norm_num)]
  have hc1 : σ (.n (val% «verify_tables» "bc_claim@1")) = σ (.n (val% «verify_tables» "x@6")) + σ (.n (val% «verify_tables» "nxt[0]@2")) * (σ (.n (val% «verify_tables» "x@5")) + (1 + σ (.n (val% «verify_tables» "nxt[0]@2"))) *
      σ (.n (val% «verify_tables» "x@7"))) := by
    rw [a1937, a1936, a1935, a1934, a1933, a1932, tb_word_one, d43, d47, d51]
  have hfin : σ (.n (val% «verify_tables» "bc_claim@4")) = dot (eqKernel [σ (.n (val% «verify_tables» "nxt[0]@2")), σ (.n (val% «verify_tables» "bc_r@1")), σ (.n (val% «verify_tables» "bc_r@2")), σ (.n (val% «verify_tables» "bc_r@3"))])
      weights * σ (.n (val% «verify_tables» "x@8")) := by
    have hl0 := tb_loadHolds_unique l0 s0
    have hl1 := tb_loadHolds_unique l1 s1
    have hl2 := tb_loadHolds_unique l2 s2
    have hl3 := tb_loadHolds_unique l3 s3
    have hw : ∀ i (hi : i < 16), LoadHolds rd (σ (.n (val% «verify_tables» "fp_w"))) i (weights.getD i 0) := fun i hi ↦ by
      rw [List.getD_eq_getElem _ _ (by omega)]; exact hW i (by omega)
    have ew := fun {i : ℕ} {v : E} (hi : i < 16) (hv : LoadHolds rd (σ (.n (val% «verify_tables» "fp_w"))) i v) ↦
      tb_loadHolds_unique hv (hw i hi)
    have e1972 : σ (.n (val% «verify_tables» "w_fold[14]")) = multilinearEval ((List.range 16).map fun i ↦ weights.getD i 0)
        [σ (.n (val% «verify_tables» "nxt[0]@2")), σ (.n (val% «verify_tables» "bc_r@1")), σ (.n (val% «verify_tables» "bc_r@2")), σ (.n (val% «verify_tables» "bc_r@3"))] := by
      rw [a2018, a2017, a2016, a2011, a2010, a2009, a2014, a2013, a2012, a1998, a1997, a1996,
        a2001, a2000, a1999, a2004, a2003, a2002, a2007, a2006, a2005, a1959, a1958, a1957,
        a1964, a1963, a1962, a1969, a1968, a1967, a1974, a1973, a1972, a1979, a1978, a1977,
        a1984, a1983, a1982, a1989, a1988, a1987, a1994, a1993, a1992, hl0, hl1, hl2, hl3,
        ew (by norm_num) w0, ew (by norm_num) w1, ew (by norm_num) w2, ew (by norm_num) w3,
        ew (by norm_num) w4, ew (by norm_num) w5, ew (by norm_num) w6, ew (by norm_num) w7,
        ew (by norm_num) w8, ew (by norm_num) w9, ew (by norm_num) w10, ew (by norm_num) w11,
        ew (by norm_num) w12, ew (by norm_num) w13, ew (by norm_num) w14, ew (by norm_num) w15]
      simp only [multilinearEval, List.range_succ, List.range_zero,
        List.map_cons, List.map_nil, List.nil_append, List.cons_append, List.foldl_cons,
        List.foldl_nil, foldPairs, List.headD_cons]
      ring
    rw [e_add_eq_zero_iff.mp a2020, a2019, e1972, ← vt_list16 weights hwl,
      multilinearEval_eq_dot weights _ hwl rfl]
  -- the run
  have sq : ∀ s : Fs, s.squeeze.2 = ⟨s.squeeze.2.cap, []⟩ := fun s ↦ rfl
  have hR4 := runsTo_sumcheck_nil
    (⟨[σ (.n (val% «verify_tables» "bfs0@3")), σ (.n (val% «verify_tables» "bfs1@3")), σ (.n (val% «verify_tables» "bfs2@3")), σ (.n (val% «verify_tables» "bfs3@3")), σ (.n (val% «verify_tables» "bfs4@3"))], []⟩ : Fs)
    (σ (.n (val% «verify_tables» "bc_claim@4"))) 3
  have hR3 := vt_tail_cons [σ (.n (val% «verify_tables» "bfs0@2")), σ (.n (val% «verify_tables» "bfs1@2")), σ (.n (val% «verify_tables» "bfs2@2")), σ (.n (val% «verify_tables» "bfs3@2")), σ (.n (val% «verify_tables» "bfs4@2"))]
    x4 x5 (σ (.n (val% «verify_tables» "bc_claim@3"))) (rest := []) (ys := []) (pt := []) (fin := σ (.n (val% «verify_tables» "bc_claim@4")))
    (s2 := ⟨[σ (.n (val% «verify_tables» "bfs0@3")), σ (.n (val% «verify_tables» "bfs1@3")), σ (.n (val% «verify_tables» "bfs2@3")), σ (.n (val% «verify_tables» "bfs3@3")), σ (.n (val% «verify_tables» "bfs4@3"))], []⟩)
    (by rw [← v3, sq, ← q3]; exact hR4)
  have hR2 := vt_tail_cons [σ (.n (val% «verify_tables» "bfs0@1")), σ (.n (val% «verify_tables» "bfs1@1")), σ (.n (val% «verify_tables» "bfs2@1")), σ (.n (val% «verify_tables» "bfs3@1")), σ (.n (val% «verify_tables» "bfs4@1"))]
    x2 x3 (σ (.n (val% «verify_tables» "bc_claim@2"))) (by rw [← v2, sq, ← q2]; exact hR3)
  have hR1 := vt_tail_cons [σ (.n (val% «verify_tables» "nxt[8]@2")), σ (.n (val% «verify_tables» "nxt[9]@2")), σ (.n (val% «verify_tables» "nxt[10]@2")), σ (.n (val% «verify_tables» "nxt[11]@2")), σ (.n (val% «verify_tables» "nxt[12]@2"))]
    x0 x1 (σ (.n (val% «verify_tables» "bc_claim@1"))) (by rw [← v1, sq, ← q1]; exact hR2)
  rw [← r1, ← r2, ← r3] at hR1
  have hR0 := runsTo_sumcheck_cons
    (runsTo_roundPolyNone (F0.absorb (σ (.n (val% «verify_tables» "x@5"))) dsObserve) (σ (.n (val% «verify_tables» "x@5"))) (σ (.n (val% «verify_tables» "x@6")))
      [σ (.n (val% «verify_tables» "x@7"))] 3 rfl (by decide))
    (by rw [hF, hF2, ← tail_eval, ← hr0, ← hc1]; exact hR1)
  rw [hF, ← hr0] at hR0
  have hS := runsTo_readE F0 (σ (.n (val% «verify_tables» "x@5")))
  have hv := runsTo_readE
    (⟨[σ (.n (val% «verify_tables» "bfs0@3")), σ (.n (val% «verify_tables» "bfs1@3")), σ (.n (val% «verify_tables» "bfs2@3")), σ (.n (val% «verify_tables» "bfs3@3")), σ (.n (val% «verify_tables» "bfs4@3"))], []⟩ : Fs) (σ (.n (val% «verify_tables» "x@8")))
  have hq := tb_runsTo_require hfin
    ((⟨[σ (.n (val% «verify_tables» "bfs0@3")), σ (.n (val% «verify_tables» "bfs1@3")), σ (.n (val% «verify_tables» "bfs2@3")), σ (.n (val% «verify_tables» "bfs3@3")), σ (.n (val% «verify_tables» "bfs4@3"))], []⟩ : Fs).absorb
      (σ (.n (val% «verify_tables» "x@8"))) dsObserve)
  -- the reads
  have hp1 : σ (.n (val% «verify_tables» "bfs0@1~9")) = σ (.n (val% «verify_tables» "cursor@1")) * gen ^ 7 := by rw [a1939, hw128]
  have hrd : TbReadsAt rd (σ (.n (val% «verify_tables» "cursor@1")) * gen ^ 7) ([x0, x1] ++ ([x2, x3] ++ ([x4, x5] ++
      [σ (.n (val% «verify_tables» "x@8"))]))) := by
    have r01 : TbReadsAt rd (σ (.n (val% «verify_tables» "cursor@1")) * gen ^ 7) [x0, x1] := fun k hk ↦ by
      have := hx01 k hk; rwa [hp1] at this
    have r23 : TbReadsAt rd (σ (.n (val% «verify_tables» "cursor@1")) * gen ^ 7 * gen ^ 2) [x2, x3] := fun k hk ↦ by
      have := hx23 k hk; rwa [u1, hp1] at this
    have r45 : TbReadsAt rd (σ (.n (val% «verify_tables» "cursor@1")) * gen ^ 7 * gen ^ 2 * gen ^ 2) [x4, x5] := fun k hk ↦ by
      have := hx45 k hk; rwa [u2, u1, hp1] at this
    have rv : TbReadsAt rd (σ (.n (val% «verify_tables» "cursor@1")) * gen ^ 7 * gen ^ 2 * gen ^ 2 * gen ^ 2) [σ (.n (val% «verify_tables» "x@8"))] := by
      rw [tbReadsAt_singleton, ← hp1, ← u1, ← u2, ← u3]; exact lv
    exact tbReadsAt_append.mpr ⟨r01, tbReadsAt_append.mpr ⟨r23, tbReadsAt_append.mpr ⟨r45, rv⟩⟩⟩
  refine ⟨[x0, x1, x2, x3, x4, x5], rfl, by simpa using hrd, ?_, ?_, ?_, cv, ?_⟩
  · intro k hk
    simp only [List.length_cons, List.length_nil] at hk
    interval_cases k
    · exact s0
    · exact s1
    · exact s2
    · exact s3
  · rw [u3, u2, u1, hp1, mul_assoc, mul_assoc, ← pow_add, ← pow_add]
  · rw [c0, c1, c2, c3, c4]
  · rw [show [σ (.n (val% «verify_tables» "x@5")), σ (.n (val% «verify_tables» "x@6")), σ (.n (val% «verify_tables» "x@7"))] ++ [x0, x1, x2, x3, x4, x5] ++ [σ (.n (val% «verify_tables» "x@8"))] =
        [σ (.n (val% «verify_tables» "x@5"))] ++ (([σ (.n (val% «verify_tables» "x@6")), σ (.n (val% «verify_tables» "x@7"))] ++ ([x0, x1] ++ ([x2, x3] ++ ([x4, x5] ++
          [])))) ++ ([σ (.n (val% «verify_tables» "x@8"))] ++ ([] ++ []))) by simp]
    unfold bytecodeShare
    exact hS.bind (hR0.bind (hv.bind (hq.bind (runsTo_ret _ _))))

end
end LeanVM.Guest.B1.Tables
