/-
  LeanVM.Guest.B1.Place.LpProof

  `level_positions` complete placed at every specialization: `level_positions_completeAt`.
-/

module

public import LeanVM.Guest.B1.Place.LpTotal
public import LeanVM.Guest.B1.Bits.QueryWindowsAtAll

/-!
# `level_positions`, placed, every specialization

`level_positions_completeAt` proves `level_positions_completeAt_Spec`: each entry of `lpTable` is
`lp_placed` at its body (`lpTable_ok`), its decoder's placed completeness (`qwDecodeAtD_holds`)
and its constants (`lpTable_facts`, by `decide`), its decoders at `lpDfp`; the words bound by
`lp_bound`, from a valid tree on a memory built for it.
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Memory
open LeanVM.Guest.B1.Main (Layout MemL RegionL)
open LeanVM.Guest.B1.Whir

@[expose] public section

set_option maxRecDepth 100000 in
/-- The constants of `lpTable`'s entries the proof uses. -/
theorem lpTable_facts : ∀ e ∈ lpTable, 0 < e.2.1 ∧ e.2.1 ≤ 64 ∧
    digitsVal (osPowDigits (192 / e.2.2.2.1)) 1 = 192 / e.2.2.2.1 ∧
    e.2.2.1 ≠ qwDecName e.2.2.2.1 e.2.2.2.2 ∧
    (qwDecName e.2.2.2.1 e.2.2.2.2, e.2.2.2.1, e.2.2.2.2) ∈ queryWindowsShapes := by
  decide +kernel

/-- **`level_positions`' loop ends with its tail call**: it is a loop helper. -/
theorem lpLoop_isLoop {d cd : ℕ} {loop : String} {fn : Fn} (hf : coreProgram.find? loop = some fn)
    (hb : fn.body = lpLoopBody d cd loop) : coreProgram.loop loop = true := by
  have hn : fn.name = loop := by simpa using List.find?_some hf
  rw [Program.loop_of_find? hf, Fn.loop, hb, hn]
  simp [lpLoopBody, osLoopTail, List.reverse_append]

/-- **`level_positions` ends with its returns**: it is no loop helper. -/
theorem lp_notLoop {sq : ℕ} {name loop : String} {fn : Fn} (hf : coreProgram.find? name = some fn)
    (hb : fn.body = lpBody sq loop) : coreProgram.loop name = false := by
  rw [Program.loop_of_find? hf, Fn.loop, hb]
  simp [lpBody, List.reverse_append]

/-- **`level_positions` is complete placed at every specialization.** -/
theorem level_positions_completeAt : level_positions_completeAt_Spec := by
  intro fs cert κ hfit hcons hκ e he
  obtain ⟨hlp, hl⟩ := lpTable_ok e he
  obtain ⟨hsq, hsqB, hpw, hne, hmem⟩ := lpTable_facts e he
  have hdec := qwDecodeAtD_holds hfit hcons hκ _ hmem
  have hs := qwShape_all _ hmem
  have hq := queryWindows_data _ hmem
  have hnl : coreProgram.loop e.1 = false :=
    let ⟨_, hf, _, hb⟩ := hlp; lp_notLoop hf hb
  have hll : coreProgram.loop e.2.2.1 = true :=
    let ⟨_, hf, _, hb⟩ := hl; lpLoop_isLoop hf hb
  refine ⟨fun fp j ↦ lpDfp fs e.1 e.2.2.1 e.2.2.2.1 e.2.2.2.2 e.2.1 fp j, fun Bd ↦ ?_⟩
  intro cap pos wp tabs Lin hcl hcan hreg hmemL hBd fp
  obtain ⟨Lown, hW, hD, hR⟩ := lp_placed fs cert κ hlp hl hnl hll hne hsq (by omega) hpw hdec
    hcl hcan fp (hreg fp) (fun rd hlow hm ↦ hmemL fp rd hlow hm)
  exact ⟨lpN fs e.1 e.2.2.1 e.2.2.2.1 e.2.2.2.2 e.2.1, Lown, hW, hD,
    fun B hB ↦ lp_bound hlp hl hsq hsqB hpw hs hq hcl hcan (hBd B hB), hR⟩

end
end LeanVM.Guest.B1
