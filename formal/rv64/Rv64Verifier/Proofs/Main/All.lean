import Rv64Verifier.Proofs.Main.Return
import Rv64Verifier.Proofs.Main.Iv
import Rv64Verifier.Proofs.Main.ParseHead
import Rv64Verifier.Proofs.Main.ParseEnd
import Rv64Verifier.Proofs.Main.NewHead

/-!
# `main`, and soundness from `walk`'s contract

`main_spec`: the stages (`Proofs/Main/Stages.lean`) and `walk`'s contract give `main`'s, on every
input that fits below the heap (`inputWords`). `IvStage` (`iv_stage`) and `ParseStage`
(`parse_head`, `parse_rest`) are proved; `NewStage` is a hypothesis.
`sound_of_walk`: as `sound_of_main`, for those inputs (`SoundFits`).
-/

namespace Rv64Verifier.Proofs.Main
open RiscvZkvm.Rv64 LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.Compile
  Rv64Verifier.Proofs.End

/-- **`main` meets its contract**, given its stages and `walk`'s. -/
theorem main_spec (hIv : IvStage) (hNew : NewStage) (hParse : ParseStage) (hW : WalkCallSpec)
    (words : List Word) (hfit : words.length ≤ inputWords) :
    FunSpec Image.code mainEntry (MainPre words) (MainPost words) := by
  intro s hpc hpre
  obtain ⟨v, hsv, hv | hd⟩ := hIv s words hpc hpre hfit
  · obtain ⟨t, hvt, ht⟩ :=
      ((hNew s words).trans ((hParse s words).trans (walk_return hW hpre.1))) v hv
    exact ⟨t, hsv.trans hvt, ht⟩
  · exact ⟨v, hsv, Or.inr hd⟩

/-- `Sound`, for the inputs that fit below the heap. -/
def SoundFits (image : LoadImage) : Prop :=
  ∀ words s n, words.length ≤ inputWords → Loaded image words s → HaltsWith image.code s n 1 →
    ∃ bytecode publicInput proof, decodeInput words = some (bytecode, publicInput, proof) ∧
      verify bytecode publicInput proof = true

/-- `sound_of_main`, for the inputs that fit. -/
theorem sound_of_main_fits
    (hmain : ∀ words, words.length ≤ inputWords →
      FunSpec Image.code mainEntry (MainPre words) (MainPost words)) :
    SoundFits image := by
  intro words s n hfit hload hhalts
  obtain ⟨hpc, hdata, hinput, ha0⟩ := hload
  obtain ⟨u, hu, hhalt, hu1⟩ := hhalts
  have hustop := Halting.step_none hhalt
  obtain ⟨s₁, hs₁, hx⟩ := start_spec.reaches hpc trivial
  have hfr : ∀ a, s₁.getMem a = s.getMem a := fun a ↦ hx.frame a (by simp [startExpect])
  have hreg : ∀ r v, (r, v) ∈ startExpect.regs → s₁.getReg r = v.eval s :=
    fun r v h ↦ hx.2.1 (r, v) h
  have hpre : MainPre words s₁ := by
    refine ⟨hreg .x2 (.c stackTop) (by simp [startExpect]),
      hreg .x3 (.c globalPointer) (by simp [startExpect]), ?_, ?_, ?_⟩
    · rw [hreg .x10 (.reg .x10) (by simp [startExpect])]; exact ha0
    · intro p hp; rw [hfr]; exact hdata p hp
    · intro i h; rw [hfr]; exact hinput i h
  obtain ⟨t, hst, hout⟩ := hmain words hfit s₁ hx.pc hpre
  rcases hout with ⟨htpc, -, hpost⟩ | hdead
  · have hret : t.pc = returnPoint := by
      rw [htpc, returnAddress, hreg .x1 (.c returnPoint) (by simp [startExpect])]
      show returnPoint &&& ~~~1#64 = returnPoint
      decide +kernel
    obtain ⟨t₂, ht₂, hy⟩ := halt_spec.reaches hret trivial
    have hfetch : Image.code.fetch t₂.pc = some (.base .ECALL) := by rw [hy.pc]; exact halt_fetch
    have hx5 : t₂.getReg .x5 = 0 := hy.2.1 (.x5, .c 0) (by simp [haltExpect])
    have ha0' : t₂.getReg .x10 = t.getReg .x10 := hy.2.1 (.x10, .reg .x10) (by simp [haltExpect])
    have hsame : t₂ = u :=
      stop_unique hu hustop (hs₁.trans (hst.trans ht₂)) (Halting.step_none ⟨hfetch, hx5⟩)
    apply hpost
    rw [← ha0', hsame, hu1]
  · have hsame : t = u := stop_unique hu hustop (hs₁.trans hst) hdead.1
    subst hsame
    exact absurd hu1 (hdead.2 hhalt)

/-- `main`'s contract, given `walk`'s and the stage not yet proved. -/
theorem main_spec_of (hNew : NewStage) (hW : WalkCallSpec) (words : List Word)
    (hfit : words.length ≤ inputWords) :
    FunSpec Image.code mainEntry (MainPre words) (MainPost words) :=
  main_spec iv_stage hNew (parse_stage_of parse_head parse_rest) hW words hfit

/-- **Soundness, from `walk`'s contract**, for the inputs that fit, given `Bytecode::new`'s grouping
(`NewStage`). -/
theorem sound_of_walk (hNew : NewStage) (hW : WalkCallSpec) : SoundFits image :=
  sound_of_main_fits fun words hfit ↦ main_spec_of hNew hW words hfit

end Rv64Verifier.Proofs.Main

/-! Lean's three axioms, nothing native. -/

/-- info: 'Rv64Verifier.Proofs.Main.sound_of_walk' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Rv64Verifier.Proofs.Main.sound_of_walk

/-- info: 'Rv64Verifier.Proofs.Main.iv_stage' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Rv64Verifier.Proofs.Main.iv_stage

/-- info: 'Rv64Verifier.Proofs.Main.parse_head' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Rv64Verifier.Proofs.Main.parse_head

/-- info: 'Rv64Verifier.Proofs.Main.parse_rest' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Rv64Verifier.Proofs.Main.parse_rest

/-- info: 'Rv64Verifier.Proofs.Main.new_head' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Rv64Verifier.Proofs.Main.new_head
