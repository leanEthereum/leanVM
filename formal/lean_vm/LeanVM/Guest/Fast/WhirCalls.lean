module

public import LeanVM.Guest.Fast.WhirTables
public import LeanVM.Guest.Fast.WhirTemplate
public import LeanVM.Guest.Fast.FunctionNames
public import LeanVM.Guest.B1.Whir.Witness
public import LeanVM.Guest.Memory.GuestCalleesOk
public import LeanVM.Guest.CoreNames

/-!
# `open_stacked`'s tables, checked

* `osQCalls c` (`Fast/WhirTemplate.lean`): each level's `level_queries` dispatch of the template at
  the configuration `c`, the states threaded as `osLevelsW` threads them (`osLevelsW_eq`);
* `callMatch c r q`: the `OsCall` `r` is the dispatch `q` in numbers: its `opening_queries`
  callee's shape, the indices of `level_queries`' specialization, of its `opening_queries`
  callee, of that callee's loop and of its queries' `walk_path` (`decoderFunctionName`,
  `Fast/FunctionNames.lean`), the loop's iterations, the level's depth and cap depth, the
  dispatch's arguments' and returns' cells (cells all);
* `osWordsTab_eq`, `CallsOKN`: the literal tables of `Fast/WhirTables.lean` are the template's at
  every size and rate (`osCfgAt j`: size `j % ligNSizes`, rate index `j / ligNSizes`), by kernel
  evaluation, a configuration at a time (`callsOK_j`, `Fast/WhirCalls/R*.lean`, a module per rate,
  joined in `Fast/WhirTablesCheck.lean`), the names read off `Data.nameT` (`nameIs`, `callMatchN`)
  and the `opening_queries` specialization found by its entry in the table (`oqAt`), not by its
  name, the table's names being distinct (`oqNames_nodup`).
-/

namespace LeanVM.Guest.Fast

open LeanVM.Guest.Core LeanVM.Guest.B1 LeanVM.Guest.B1.Whir

@[expose] public section

/-- A cell's number. -/
def vIdx (v : V) : ℕ := v.idx

/-- Whether a value is the cell of its number. -/
def isN (v : V) : Bool := v == .n v.idx

/-- Two shapes, field by field. -/
def shapeBEq (a b : OqShape) : Bool :=
  a.odd == b.odd && a.base == b.base && a.folds == b.folds && a.leafCells == b.leafCells &&
    a.depth == b.depth && a.cd == b.cd && a.mu == b.mu && a.vanish == b.vanish &&
    a.nHs == b.nHs && a.hsBits == b.hsBits && a.final == b.final && a.vs == b.vs

theorem eq_of_shapeBEq {a b : OqShape} (h : shapeBEq a b = true) : a = b := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _⟩ := a
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _⟩ := b
  simp only [shapeBEq, Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩, h10⟩, h11⟩, h12⟩ := h
  subst h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12
  rfl

theorem osLevelsW_eq (rd : Reader) (V : FrameMap) (σ : Val) (c : OsCfg) :
    ∀ lvl lvs s, osLevelsW rd V σ c lvl lvs s =
      (osQCallsFrom c lvl lvs s).map fun q ↦ osLevelW rd V c q.1 q.2.1 (q.2.2.1.map σ) (q.2.2.2.map σ)
  | _, [], _ => rfl
  | lvl, lv :: rest, s => by
    rw [osLevelsW, osQCallsFrom, List.map_cons, osLevelsW_eq rd V σ c (lvl + 1) rest]

/-- **The table's call `r` is the dispatch `q`** of the configuration `c`. -/
noncomputable def callMatch (c : OsCfg) (r : OsCall) : ℕ × OsLv × List V × List V → Bool
  | (lvl, lv, args, rets) =>
    shapeBEq (oqShapeAt r.sh) (oqShapeOf (osOqName c lvl lv)) &&
      decoderFunctionName r.lq == osQueriesName c lvl lv &&
      decoderFunctionName r.fn == osOqName c lvl lv &&
      decoderFunctionName r.loop == oqLoopOf (osOqName c lvl lv) &&
      decoderFunctionName r.walk == oqWalkOf (oqShapeOf (osOqName c lvl lv)).oq &&
      r.N == lv.queries / (1 + lvBase lvl) && r.depth == lv.depth && r.cd == lv.capDepth &&
      r.args == args.map vIdx && r.rets == rets.map vIdx && args.all isN && rets.all isN

/-- `decoderFunctionName j = f`, read off `Data.nameT`. -/
def nameIs (j : ℕ) (f : String) : Bool := isFunctionIndex j && decide (Data.nameT.find (j - 1) = some f)

theorem nameIs_spec {j : ℕ} {f : String} (h : nameIs j f = true) : decoderFunctionName j = f := by
  simp only [nameIs, Bool.and_eq_true, decide_eq_true_eq] at h
  have hj := h.1
  simp only [isFunctionIndex, Bool.and_eq_true, decide_eq_true_eq] at hj
  have hl : j - 1 < coreProgram.length := by rw [coreProgram_length]; omega
  have hn := Data.nameT_spec hl h.2
  unfold decoderFunctionName
  simp only [h.1, ↓reduceIte, List.getD_eq_getElem _ _ hl]
  rw [List.getElem?_eq_getElem hl, Option.map_some, Option.some.injEq] at hn
  exact hn

/-- Entry `i` of the specializations' table. -/
def oqAt (i : ℕ) : Option (String × String × OqShape) := openingQueriesLoops[i]?

/-- The loop helper of entry `i`. -/
def oqLoopAt (i : ℕ) : String := ((oqAt i).map (·.2.1)).getD ""

/-- **The specializations' names are distinct**, by their codes. -/
theorem oqNames_nodup : (openingQueriesLoops.map (·.1)).Nodup := by
  have h : ((openingQueriesLoops.map (·.1)).map encS).Nodup := by decide +kernel
  exact h.of_map _

theorem find_fst_of_nodup {β : Type} : ∀ {l : List (String × β)} {i : ℕ} {p : String × β},
    (l.map (·.1)).Nodup → l[i]? = some p → l.find? (·.1 == p.1) = some p
  | [], _, _, _, h => by simp at h
  | q :: l, 0, p, _, h => by simp only [List.getElem?_cons_zero, Option.some.injEq] at h; subst h; simp
  | q :: l, i + 1, p, hn, h => by
      rw [List.map_cons, List.nodup_cons] at hn
      simp only [List.getElem?_cons_succ] at h
      have hne : (q.1 == p.1) = false := by
        simp only [beq_eq_false_iff_ne]
        rintro he
        exact hn.1 (he ▸ List.mem_map_of_mem (List.mem_of_getElem? h))
      rw [List.find?_cons, hne]
      exact find_fst_of_nodup hn.2 h

/-- An entry found by its name is entry `i`. -/
theorem oqEntry_of_at {i : ℕ} {n : String} (h : ((oqAt i).map (·.1)) = some n) : oqEntry n = oqAt i := by
  rcases hp : oqAt i with _ | p
  · rw [hp] at h; cases h
  rw [hp, Option.map_some, Option.some.injEq] at h
  subst h
  exact find_fst_of_nodup oqNames_nodup hp

/-- `callMatch`, the names read off `Data.nameT`, the specialization by its entry in the table. -/
noncomputable def callMatchN (c : OsCfg) (r : OsCall) : ℕ × OsLv × List V × List V → Bool
  | (lvl, lv, args, rets) =>
    decide (((oqAt r.sh).map (·.1)) = some (osOqName c lvl lv)) &&
      nameIs r.lq (osQueriesName c lvl lv) &&
      nameIs r.fn (osOqName c lvl lv) &&
      nameIs r.loop (oqLoopAt r.sh) &&
      nameIs r.walk (oqWalkOf (oqShapeAt r.sh).oq) &&
      r.N == lv.queries / (1 + lvBase lvl) && r.depth == lv.depth && r.cd == lv.capDepth &&
      r.args == args.map vIdx && r.rets == rets.map vIdx && args.all isN && rets.all isN

theorem callMatch_of_N {c : OsCfg} {r : OsCall} {q : ℕ × OsLv × List V × List V}
    (h : callMatchN c r q = true) : callMatch c r q = true := by
  obtain ⟨lvl, lv, args, rets⟩ := q
  simp only [callMatchN, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩, h10⟩, h11⟩, h12⟩ := h
  have he := oqEntry_of_at h1
  have hl : oqLoopOf (osOqName c lvl lv) = oqLoopAt r.sh := by rw [oqLoopOf, oqLoopAt, he]
  have hs : oqShapeOf (osOqName c lvl lv) = oqShapeAt r.sh := by rw [oqShapeOf, oqShapeAt, he, oqAt]
  simp only [callMatch, Bool.and_eq_true, beq_iff_eq, nameIs_spec h2, nameIs_spec h3, nameIs_spec h4,
    nameIs_spec h5, hl, hs]
  simp_all [shapeBEq]

theorem osWordsTab_eq :
    osWordsTab = (List.range (ligNSizes * ligNRates)).map fun j ↦ osWordsLen (osCfgAt j) := by
  decide +kernel

/-- Configuration `j`'s dispatches are the table's. -/
def CallsOK (j : ℕ) : Prop :=
  (osCallsTab.getD j []).length = (osQCalls (osCfgAt j)).length ∧
    ((osCallsTab.getD j []).zip (osQCalls (osCfgAt j))).all
      (fun p ↦ callMatch (osCfgAt j) p.1 p.2) = true

/-- `CallsOK`, the names read off `Data.nameT`. -/
def CallsOKN (j : ℕ) : Prop :=
  (osCallsTab.getD j []).length = (osQCalls (osCfgAt j)).length ∧
    ((osCallsTab.getD j []).zip (osQCalls (osCfgAt j))).all
      (fun p ↦ callMatchN (osCfgAt j) p.1 p.2) = true

theorem CallsOKN.ok {j : ℕ} (h : CallsOKN j) : CallsOK j :=
  ⟨h.1, List.all_eq_true.mpr fun p hp => callMatch_of_N (List.all_eq_true.mp h.2 p hp)⟩

end
end LeanVM.Guest.Fast
