/-
  LeanVM.Guest.B1.Whir.FinishSplit

  The body after the closing rounds split at its return.
-/

module

public import LeanVM.Guest.B1.Whir.Template

/-!
# The finish, split

`osFinishA c st tch`: the statements of `osFinish` before its return and the returned values;
`osFinish_eq`: `osFinish` is them, then the return.
-/

namespace LeanVM.Guest.B1.Whir

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest LeanVM.Protocol

@[expose] public section

/-- The body after the closing rounds, before its return, and the returned values. -/
def osFinishA (c : OsCfg) (st : OsSt) (tch : ℕ) : List Stmt × List V :=
  let n := c.levels.length
  let mid := c.levels.take c.yrLevel
  let yat := st.k
  let pt := yat + 1
  let pts := osPtBlks c pt (pt + 1) tch 0 pointCap (pt + 2)
  let bd := pts.2 + 1
  let ls := pts.2 + 3
  let la := pts.2 + 5
  let bs := osBases c tch bd ls la 0 mid (pts.2 + 6)
  let ich := bs.2 + 1
  let rs := osResiduals c ich bd ls la 0 mid st.mats (bs.2 + 3)
  let od := osOodWeights c tch ((c.levels.headD default).logCols) 1 c.levels.tail none rs.2
  let k := od.2.2
  ([.call ("fold_final_msg__L" ++ natStr c.yrLog) [.n osFmsg, .n tch] [.n yat],
    .atom (.hint (.alloc (.n pt) pointCap)), .atom (.hint (.alloc (.n (pt + 1)) pointCap))] ++
    pts.1 ++ osHeap (n * ligColsCap) pts.2 ++ osHeap n (pts.2 + 2) ++ osHeap n (pts.2 + 4) ++ bs.1 ++
    osHeap (2 * n) bs.2 ++ [osCst (bs.2 + 2) (word 0 0), osLd (bs.2 + 2) ich 0, osLd st.claim ich 1] ++
    rs.1 ++ od.1 ++
    [osLd k ich (2 * c.yrLevel + 1), osCp (k + 1) pt, osCp (k + 2) (pt + 1), osLd (k + 3) ich (2 * c.yrLevel),
      osAdd (k + 4) (k + 3) (od.2.1.getD 0), osCp (k + 5) yat],
   [.n k, .n (k + 1), .n (k + 2), .n (k + 4), .n (k + 5)])

theorem osFinish_eq (c : OsCfg) (st : OsSt) (tch : ℕ) :
    osFinish c st tch = (osFinishA c st tch).1 ++ [.ret (osFinishA c st tch).2] := by
  simp only [osFinish, osFinishA, List.append_assoc, List.cons_append, List.nil_append]

/-- The body of `open_stacked` before its return. -/
def osBodyA (c : OsCfg) : List Stmt :=
  let h := osHead c
  let lv := osLevels c 0 c.levels h.2
  let tl := osTail c lv.2
  h.1 ++ lv.1 ++ tl.1 ++ (osFinishA c tl.2.1 tl.2.2).1

/-- The values `open_stacked` returns. -/
def osBodyRet (c : OsCfg) : List V :=
  (osFinishA c (osTail c (osLevels c 0 c.levels (osHead c).2).2).2.1
    (osTail c (osLevels c 0 c.levels (osHead c).2).2).2.2).2

theorem osBody_eq (c : OsCfg) : osBody c = osBodyA c ++ [.ret (osBodyRet c)] := by
  simp only [osBody, osBodyA, osBodyRet, osFinish_eq, List.append_assoc]

end
end LeanVM.Guest.B1.Whir
