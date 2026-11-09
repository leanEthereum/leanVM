/-
  LeanVM.Guest.B1.Place.OsCand

  A candidate's decided facts for open_stacked's placed lift.
-/

module

public import LeanVM.Guest.B1.Place.OsFinal

/-!
# A candidate's placed facts, decided

`PlacedP c`: the facts of `OsCfgPlaced` that do not depend on the frame certificates, as one
decidable proposition (no `frameAddr` in the body, the callee names' kinds, the buffers' sizes,
the row weights' and positions' bounds). `placedP_sound` reads them back. `sqLoop_isLoop`,
`osBody_notLoop`: the loop flags, from the bodies. `OsFitsAt fs cert c`: the certificate facts of
`opening_queries`' frames, per level, left a hypothesis. `cfgPlaced_of`: the configuration's
`OsCfgPlaced` from them.
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Memory
open LeanVM.Guest.B1.Whir
open LeanVM.Protocol LeanVM.Protocol.Compile LeanVM.Protocol.KeccakHash
open LeanVM.Protocol.Verifier hiding Layout

@[expose] public section

/-- **A configuration's placed facts but the certificates'**, one decidable proposition. -/
def PlacedP (c : OsCfg) : Prop :=
  (osBodyA c).filterMap Main.Stmt.addrS = [] ∧
  (∀ i < c.levels.length, i ≠ c.yrLevel →
    osKindOf ("opening_ood_point__L" ++ natStr (lvAt c i).logCols) = some (.ood (lvAt c i).logCols)) ∧
  (∀ i < c.levels.length,
    osKindOf ("grind_check__L" ++ natStr (lvAt c i).grind) = some (.grind Whir.queryGrindingBits)) ∧
  osKindOf ("opening_final_message__L" ++ natStr c.yrLen) = some (.fm c.yrLen) ∧
  (∀ i < c.levels.length,
    osKindOf ("opening_row_weights__L" ++ natStr (lvAt c i).folds ++ "_L" ++
      natStr (if i = 0 then 1 else 0)) = some (.rw (lvAt c i).folds (if i = 0 then 1 else 0))) ∧
  (∀ i < c.levels.length,
    osKindOf ("verify_merkle_cap__L" ++ natStr (lvAt c i).capDepth) = some (.cap (lvAt c i).capDepth)) ∧
  osKindOf ("fold_final_msg__L" ++ natStr c.yrLog) = some (.ffm c.yrLog) ∧
  (∀ i < c.levels.length, osKindOf (c.sqLoop i) = none) ∧
  (∀ i < c.levels.length, osKindOf (osQueriesName i (lvAt c i)) = none) ∧
  (∀ i < c.levels.length, osKindOf (c.resLoop i) = none) ∧
  (∀ i < c.levels.length,
    2 ^ rwLo (lvAt c i).folds + 2 ^ ((lvAt c i).folds - rwLo (lvAt c i).folds) ≤ c.maxIl) ∧
  (∀ i < c.levels.length, (lvAt c i).capDepth ≤ (lvAt c i).depth) ∧
  (∀ i < c.levels.length, ∀ j < c.levels.length, c.sqLoop i ≠ c.resLoop j) ∧
  (∀ i < c.levels.length, (lvAt c i).squeezes ≤ c.maxSq) ∧
  (∀ i < c.levels.length, (lvAt c i).logCols ≤ ligColsCap) ∧
  c.yrLog ≤ yrLogCap ∧
  (∀ i < c.levels.length, (lvAt c i).posOff + (lvAt c i).squeezes * (192 / (lvAt c i).depth) ≤
    if i + 1 < c.levels.length then (lvAt c (i + 1)).posOff else c.posLen) ∧
  (∀ i < c.levels.length, 4 * (lvAt c i).capOff + 2 ^ ((lvAt c i).capDepth + 2) ≤
    if i + 1 < c.levels.length then 4 * (lvAt c (i + 1)).capOff else 4 * c.capLen) ∧
  (∀ i < c.levels.length, (lvAt c i).capOff + 2 ^ (lvAt c i).capDepth ≤
    if i + 1 < c.levels.length then (lvAt c (i + 1)).capOff else c.capLen) ∧
  (∀ e ∈ osSizesL c, e < 2 ^ 64 - 1) ∧
  (∀ x ∈ osSizesL c, 0 < x) ∧
  (osSizesL c).sum < 2 ^ 64 - 1 ∧
  (∀ l < c.levels.length,
    rowLo (lvAt c l).interleave + (lvAt c l).interleave / rowLo (lvAt c l).interleave ≤ c.maxIl) ∧
  (∀ l < c.levels.length, (lvAt c l).queries + 1 < ordG) ∧
  (∀ l < c.levels.length, resBatch ≤ (lvAt c l).queries)

instance (c : OsCfg) : Decidable (PlacedP c) := by
  unfold PlacedP; infer_instance

/-- **The decided facts, read back.** -/
theorem placedP_sound {c : OsCfg} (h : PlacedP c) :
    OsBodyFacts c ∧ OsNames c ∧ OsSizes c ∧ (∀ e ∈ osSizesL c, e < 2 ^ 64 - 1) ∧
      (∀ x ∈ osSizesL c, 0 < x) ∧ (osSizesL c).sum < 2 ^ 64 - 1 ∧
      (∀ l < c.levels.length,
        rowLo (lvAt c l).interleave + (lvAt c l).interleave / rowLo (lvAt c l).interleave ≤ c.maxIl) ∧
      (∀ l < c.levels.length, (lvAt c l).queries + 1 < ordG) ∧
      (∀ l < c.levels.length, resBatch ≤ (lvAt c l).queries) := by
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h11', h13, h14, h15, h16, h17, h18,
    h19, h20, h21, h22, h23, h24⟩ := h
  exact ⟨⟨h0⟩, ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h11'⟩,
    ⟨h13, h14, h15, h16, h17, h18⟩, h19, h20, h21, h22, h23, h24⟩

/-- **A squeeze loop's body ends with its tail call**: it is a loop helper. -/
theorem sqLoop_isLoop {name : String} {fn : Fn} {lv : OsLv} (hf : coreProgram.find? name = some fn)
    (hb : fn.body = sqLoopBody lv name) : coreProgram.loop name = true := by
  have hn : fn.name = name := by simpa using List.find?_some hf
  rw [Program.loop_of_find? hf, Fn.loop, hb, hn]
  simp [sqLoopBody, osLoopTail, List.reverse_append]

/-- **`open_stacked`'s body ends with its returns**: it is no loop helper. -/
theorem osBody_notLoop {c : OsCfg} {name : String} {fn : Fn} (hf : coreProgram.find? name = some fn)
    (hb : fn.body = osBody c) : coreProgram.loop name = false := by
  rw [Program.loop_of_find? hf, Fn.loop, hb, osBody_split]
  simp [List.reverse_append, osFinishRet]

/-- **The certificate facts of a configuration's `opening_queries` frames.** -/
def OsFitsAt (fs : String → ℕ) (cert : String → V → ℕ) (c : OsCfg) : Prop :=
  ∀ l < c.levels.length, OqFits fs cert (osQueriesName l (lvAt c l))
    (oqLoopOf (osQueriesName l (lvAt c l))) (osQShape c l)
    ((lvAt c l).queries % 2 * (if l = 0 then 1 else 0))

/-- **A configuration's placed facts**, from its decided ones, its names, its loop helpers and
its certificates. -/
theorem cfgPlaced_of {fs : String → ℕ} {cert : String → V → ℕ} {c : OsCfg} (hP : PlacedP c)
    (hq : ∀ l < c.levels.length, NamesOk c l (lvAt c l))
    (hsq : ∀ l < c.levels.length, ∃ fn, coreProgram.find? (c.sqLoop l) = some fn ∧
      fn.params = osParams 6 ∧ fn.body = sqLoopBody (lvAt c l) (c.sqLoop l))
    (hres : ∀ l < c.levels.length, ∃ fn, coreProgram.find? (c.resLoop l) = some fn ∧
      fn.params = osParams 6 ∧ fn.body = resLoopBody l (lvAt c l) (c.resLoop l))
    (hfits : OsFitsAt fs cert c) : OsCfgPlaced fs cert c := by
  obtain ⟨hb, hn, hs, hsz, hpos, htot, hil, hqo, hq8⟩ := placedP_sound hP
  refine ⟨hb, hn, hs, hsz, hpos, htot, hq, hfits, hil, hqo, hq8, fun l hl ↦ ?_, hres,
    fun l hl ↦ ?_⟩
  · obtain ⟨fn, h1, h2, h3⟩ := hsq l hl
    exact ⟨fn, h1, h2, h3, sqLoop_isLoop h1 h3⟩
  · exact (hq l hl).2.2.2.1

end
end LeanVM.Guest.B1
