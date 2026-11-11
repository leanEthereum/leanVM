/-
  LeanVM.Guest.B1.Place.OsCallV

  The calls of f128's `open_stacked` template, level by level: what the placed lift sequences,
  and the special calls whose honest argument values the body's completeness names.
-/

module

public import LeanVM.Guest.B1.Whir.FinishSplit
public import LeanVM.Guest.Memory.Straight

/-!
# The template's calls

A level of `osBody c` (`Whir.osLevel`) splits at its squeezes (`osLevel_callSplit`): before them
its fold rounds, its message and the query grind (`lvA`); the squeezes (`lvS`: the first
squeeze's `decode_query_windows`, `osDecCall`, then the squeeze loop's guarded call, `osSqCall`);
after them `λ`'s grind, the cap, the high part, `opening_queries` (`osQCall`) and the glue
(`lvB`). After the levels, the closing rounds' `opening_tail_round` calls and the finish's
`fold_final_msg` and each non-final level's residual loop (`osResCall`).

`osStAt c l`: the state before level `l`; `osSqSt c l`, `osQSt c l`: before its squeezes and
before its queries. The special calls are named at those states, so the body's completeness can
state their argument values (`osDecCall c l`, `osSqCall c l`, `osQCall c l`, `osResCall c l`).
`osBody_calls`: the body's calls, the levels' (`osLvKs`, as `OsLvKP`) then the rest's.
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Memory
open LeanVM.Guest.B1.Whir

@[expose] public section

/-- Level `l`'s row. -/
abbrev osLvAt (c : OsCfg) (l : ℕ) : OsLv := c.levels.getD l default

/-! ## A level, split at its squeezes -/

/-- A level's fold rounds. -/
def lvF (c : OsCfg) (lv : OsLv) (s : OsSt) : List Stmt × OsSt :=
  osRounds c.plan lv.foldsOff lv.folds s

/-- A level's message: the final lane, or the next commitment. -/
def lvM (c : OsCfg) (lvl : ℕ) (lv : OsLv) (s : OsSt) : List Stmt × OsSt :=
  if lvl = c.yrLevel then osFinalMsg c lv (lvF c lv s).2 else osCommit c lvl lv (lvF c lv s).2

/-- A level before its squeezes. -/
def lvA (c : OsCfg) (lvl : ℕ) (lv : OsLv) (s : OsSt) : List Stmt :=
  (lvF c lv s).1 ++ (lvM c lvl lv s).1 ++
    [.call ("grind_check__L" ++ natStr queryGrind) [.n (lvM c lvl lv s).2.pow0, .n osTabs] []]

/-- A level's squeezes. -/
def lvS (c : OsCfg) (lvl : ℕ) (lv : OsLv) (s : OsSt) : List Stmt × OsSt :=
  osSqueezes c lvl lv (lvM c lvl lv s).2

/-- A level's batching challenge, cap and high part: the state before its queries. -/
def lvH (c : OsCfg) (lvl : ℕ) (lv : OsLv) (s : OsSt) : List Stmt × OsSt :=
  let la := if lvl = c.yrLevel then (([] : List Stmt), (lvS c lvl lv s).2) else osLam (lvS c lvl lv s).2
  let cp := osCap c lvl lv la.2
  let h := if lvl = c.yrLevel then osHsFinal c lv cp.2 else osHsMid lvl lv cp.2
  (la.1 ++ cp.1 ++ h.1, h.2)

/-- A level after its squeezes. -/
def lvB (c : OsCfg) (lvl : ℕ) (lv : OsLv) (s : OsSt) : List Stmt :=
  let q := osQueries c lvl lv (lvH c lvl lv s).2
  let g := if lvl = c.yrLevel then (([] : List Stmt), q.2) else osGlue lvl lv q.2
  (lvH c lvl lv s).1 ++ q.1 ++ g.1

theorem osLevel_callSplit (c : OsCfg) (lvl : ℕ) (lv : OsLv) (s : OsSt) :
    (osLevel c lvl lv s).1 = lvA c lvl lv s ++ ((lvS c lvl lv s).1 ++ lvB c lvl lv s) := by
  simp only [osLevel, lvA, lvB, lvH, lvS, lvM, lvF, List.append_assoc]

/-! ## Calls of atom runs -/

theorem osCallS_atoms {l : List Stmt} (h : ∀ s ∈ l, ∃ a, s = .atom a) :
    l.filterMap Stmt.callS = [] :=
  List.filterMap_eq_nil_iff.mpr fun s hs ↦ by obtain ⟨a, rfl⟩ := h s hs; rfl

theorem osMatS_callS (P : List (ℕ × ℕ × ℕ)) (b o : ℕ) (s : OsSt) :
    (osMatS P b o s).1.filterMap Stmt.callS = [] := by
  unfold osMatS osMatP; split <;> rfl

theorem osHeap_callS (e k : ℕ) : (osHeap e k).filterMap Stmt.callS = [] := rfl

/-! ## The squeezes' calls -/

/-- The first squeeze's decoder call at the squeezes' state `s`. -/
def osDecCallAt (c : OsCfg) (lv : OsLv) (s : OsSt) : Option V × String × List V × List V :=
  let qp := osMatS c.plan osQpos lv.posOff { s with k := s.k + 2 }
  let wp := osMatS c.plan osQbp lv.posOff qp.2.2
  (none, "decode_query_windows__L" ++ natStr lv.depth ++ "_L" ++ natStr lv.capDepth,
    [s.word0, qp.2.1, wp.2.1, osTabs].map V.n, [])

/-- The squeeze loop's guarded call at the squeezes' state `s`. -/
def osSqCallAt (c : OsCfg) (lvl : ℕ) (lv : OsLv) (s : OsSt) : Option V × String × List V × List V :=
  let qp := osMatS c.plan osQpos lv.posOff { s with k := s.k + 2 }
  let wp := osMatS c.plan osQbp lv.posOff qp.2.2
  let l := wp.2.2.k
  (some (.n (l + 2)), c.sqLoop lvl,
    .n (l + 3) :: .n (l + 4) :: [s.k + 1, osQpos, osQbp, osTabs].map V.n, [])

theorem osSqueezes_callS (c : OsCfg) (lvl : ℕ) (lv : OsLv) (s : OsSt) :
    (osSqueezes c lvl lv s).1.filterMap Stmt.callS =
      [osDecCallAt c lv s, osSqCallAt c lvl lv s] := by
  simp only [osSqueezes, List.filterMap_append, osHeap_callS, osMatS_callS, osLoopCall,
    List.filterMap_cons, List.filterMap_nil, Stmt.callS, List.nil_append]
  rw [osCallS_atoms (by simp; intro _ _ _ _ h; exact ⟨_, h.symm⟩), osCallS_atoms (by simp)]
  simp [osDecCallAt, osSqCallAt]

/-! ## The levels' states and special calls -/

/-- The state before level `j` of the levels from `lvl` at `s`. -/
def osStFrom (c : OsCfg) (lvl : ℕ) (lvs : List OsLv) (s : OsSt) (j : ℕ) : OsSt :=
  (osLevels c lvl (lvs.take j) s).2

/-- The state before level `l`. -/
def osStAt (c : OsCfg) (l : ℕ) : OsSt := osStFrom c 0 c.levels (osHead c).2 l

/-- The state before level `l`'s squeezes. -/
def osSqSt (c : OsCfg) (l : ℕ) : OsSt := (lvM c l (osLvAt c l) (osStAt c l)).2

/-- Level `l`'s first decoder call. -/
def osDecCall (c : OsCfg) (l : ℕ) : Option V × String × List V × List V :=
  osDecCallAt c (osLvAt c l) (osSqSt c l)

/-- Level `l`'s squeeze loop call. -/
def osSqCall (c : OsCfg) (l : ℕ) : Option V × String × List V × List V :=
  osSqCallAt c l (osLvAt c l) (osSqSt c l)

/-- The state before level `l`'s queries. -/
def osQSt (c : OsCfg) (l : ℕ) : OsSt := (lvH c l (osLvAt c l) (osStAt c l)).2

/-! ## The queries' call -/

/-- A level's `opening_queries` call at the queries' state `s`. -/
def osQCallAt (c : OsCfg) (lvl : ℕ) (lv : OsLv) (s : OsSt) : Option V × String × List V × List V :=
  let fin := lvl = c.yrLevel
  let cp := osMatS c.plan osCaps (4 * lv.capOff) s
  let fl := osMatS c.plan osFlags lv.capOff cp.2.2
  let li : List Stmt × ℕ × OsSt :=
    if fin then ([osCst fl.2.2.k (word 0 0)], fl.2.2.k, { fl.2.2 with k := fl.2.2.k + 1 })
    else ([], s.lamInv, fl.2.2)
  let cf := osMatS c.plan osCoefs (2 * lv.foldsOff) li.2.2
  let hp : List Stmt × ℕ × OsSt :=
    if fin then ([], s.hs, cf.2.2) else osMatS c.plan osHs (lvl * hsStride) cf.2.2
  let qp := osMatS c.plan osQpos lv.posOff hp.2.2
  let wp := osMatS c.plan osQbp lv.posOff qp.2.2
  let g := wp.2.2.k
  (none, osQueriesName c lvl lv, [cp.2.1, fl.2.1, li.2.1, cf.2.1, hp.2.1, qp.2.1, wp.2.1, g].map V.n,
    [.n (g + 1)])

/-- Level `l`'s `opening_queries` call. -/
def osQCall (c : OsCfg) (l : ℕ) : Option V × String × List V × List V :=
  osQCallAt c l (osLvAt c l) (osQSt c l)

theorem osQueries_callS (c : OsCfg) (lvl : ℕ) (lv : OsLv) (s : OsSt) :
    (osQueries c lvl lv s).1.filterMap Stmt.callS = [osQCallAt c lvl lv s] := by
  simp only [osQueries, List.filterMap_append, osMatS_callS, List.filterMap_cons,
    List.filterMap_nil, Stmt.callS, List.nil_append]
  split_ifs <;> simp [osMatS_callS, osQCallAt, Stmt.callS, *]

theorem osPowSteps_callS (x : ℕ) : ∀ (ds : List Bool) (acc k : ℕ),
    (osPowSteps x ds acc k).1.filterMap Stmt.callS = []
  | [], _, _ => rfl
  | true :: ds, acc, k => by
    simp only [osPowSteps, ↓reduceIte, List.filterMap_cons, osPowSteps_callS x ds]; rfl
  | false :: ds, acc, k => by
    simp only [osPowSteps, Bool.false_eq_true, ↓reduceIte, List.filterMap_cons, osPowSteps_callS x ds]
    rfl

theorem osGlue_callS (lvl : ℕ) (lv : OsLv) (s : OsSt) :
    (osGlue lvl lv s).1.filterMap Stmt.callS = [] := by
  simp only [osGlue, List.filterMap_append, osPowSteps_callS]
  rfl

theorem lvB_callS (c : OsCfg) (lvl : ℕ) (lv : OsLv) (s : OsSt) :
    (lvB c lvl lv s).filterMap Stmt.callS =
      (lvH c lvl lv s).1.filterMap Stmt.callS ++ [osQCallAt c lvl lv (lvH c lvl lv s).2] := by
  simp only [lvB, List.filterMap_append, osQueries_callS]
  split_ifs <;> simp [osGlue_callS]

/-! ## After the levels -/

/-- The levels' state. -/
def osLvsEnd (c : OsCfg) : OsSt := (osLevels c 0 c.levels (osHead c).2).2

/-- The statements after the levels before the return: the closing rounds and the finish. -/
def osRest (c : OsCfg) : List Stmt :=
  (osTail c (osLvsEnd c)).1 ++ (osFinishA c (osTail c (osLvsEnd c)).2.1 (osTail c (osLvsEnd c)).2.2).1

theorem osBodyA_eq_rest (c : OsCfg) :
    osBodyA c = (osHead c).1 ++ (osLevels c 0 c.levels (osHead c).2).1 ++ osRest c := by
  simp only [osBodyA, osRest, osLvsEnd, List.append_assoc]

/-- The finish's residual base values: `inner_chain`, `basis_d`, the scales, the products, the
first free value. -/
def osResBase (c : OsCfg) : ℕ × ℕ × ℕ × ℕ × ℕ :=
  let st := (osTail c (osLvsEnd c)).2.1
  let tch := (osTail c (osLvsEnd c)).2.2
  let pt := st.k + 1
  let pts := osPtBlks c pt (pt + 1) tch 0 pointCap (pt + 2)
  let bd := pts.2 + 1
  let ls := pts.2 + 3
  let la := pts.2 + 5
  let bs := osBases c tch bd ls la 0 (c.levels.take c.yrLevel) (pts.2 + 6)
  (bs.2 + 1, bd, ls, la, bs.2 + 3)

/-- The first free value of non-final level `l`'s residual chain. -/
def osResK (c : OsCfg) (l : ℕ) : ℕ :=
  let b := osResBase c
  (osResiduals c b.1 b.2.1 b.2.2.1 b.2.2.2.1 0 ((c.levels.take c.yrLevel).take l) b.2.2.2.2).2

/-- Non-final level `l`'s residual loop call. -/
def osResCall (c : OsCfg) (l : ℕ) : Option V × String × List V × List V :=
  let k := osResK c l
  (some (.n (k + 7)), c.resLoop l,
    .n (k + 8) :: .n (k + 9) :: [osQpos, (osResBase c).2.1, osHs, k + 2, k].map V.n, [])

end
end LeanVM.Guest.B1
