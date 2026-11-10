import Rv64Verifier.Proofs.Final.All
import Rv64Verifier.Proofs.Walk.AllE
import Rv64Verifier.Proofs.Walk.Front
import Rv64Verifier.Proofs.Walk.Dr12
import Rv64Verifier.Proofs.Pcs.All
import Rv64Verifier.Proofs.Walk.R19M
import Rv64Verifier.Proofs.Walk.R20I

/-!
# `walk`'s contract, assembled

`walkSpec`: `WalkSpecO OI` (`walk`'s contract, the proof's openings in place: `OpenPre`) from the
front (`front`, DEREF to R9 by `derefToR10`) and the tail (`tail_of`), given what is still open:
`verify_bus_balance`'s contract and its reading of the `Bytecode` (`BusBalanceSpec`, `BcWalk`),
`verify_keccak`'s as `walk` calls it (`VerifyKeccakSpecE`, for R20; R19 and R20 are `r1920`),
`extend_desugared`'s strengthened contract (`ExtendSpecE`) and `verify_stacked_opening`'s
(`VsoSpec`). `openBridge` gives `verify_stacked_opening` the openings
`OI` places. `walkCall_of_walkO`: `main`'s view of it, given that the doublewords the openings read
miss what `walk` writes (`OpenRO`).
-/

namespace Rv64Verifier.Proofs.Final
open RiscvZkvm.Rv64 LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.Compile Rv64Verifier.Model
  Rv64Verifier.Runtime

section
variable {s : MachineState}

/-- `OI.openingsAt`, of the `Proof` at `a`. -/
theorem OI.openingsAtA {a : Word} {ops : List (List Opening)} (h : OI s a ops) :
    Walk.OpeningsAtA s a ops := by
  have key : ∀ L, L = (Main.readProof s a).openings → ∀ k (hk : k < L.length),
      Transcript.PhaseAt s (vecPtr s (a + 24) + BitVec.ofNat 64 (24 * k)) L[k] := by
    intro L hL k hk
    subst hL
    simp only [Main.readProof, List.getElem_map, List.getElem_range]
    exact phaseAt_self _
  refine ⟨?_, fun k hk ↦ key _ h.1 k hk⟩
  rw [h.1]
  simp [Main.readProof]

/-- `OI.openMapped`, of the `Proof` at `a`. -/
theorem openMappedA_of {out a : Word} (hm : Main.ProofMem s out a) : Walk.OpenMappedA s a :=
  ⟨zero_or_region (by decide) hm.openings, fun k hk ↦
    ⟨zero_or_region (by decide) (hm.phases k hk).buf, fun j hj ↦
      ⟨zero_or_region (by decide) ((hm.phases k hk).paths j hj).leaf,
        mapped_of_part (by decide) ((hm.phases k hk).paths j hj).siblings⟩⟩⟩

end

/-- The openings `OI` places at `walk`'s entry are those `verify_stacked_opening` reads. -/
theorem openBridge : Walk.OpenBridge OI Transcript.OpeningsAt := by
  intro s v T hpre hO I hptr _ _ hOI
  have hA := (Walk.openKeep hpre hO I).1 _ (OI.openingsAtA hOI)
  have hp : Transcript.proofAt v (Walk.tp s) = s.getReg .x13 := hptr
  rw [← hp] at hA
  exact Walk.OpeningsAtA.toP hA

/-- `walk`'s contract gives the one `main` uses, the doublewords the openings read missing what
`walk` writes. -/
theorem walkCall_of_walkO (hW : Walk.WalkSpecO OI)
    (hO : ∀ s, Main.WalkCallPre s → Walk.OpenRO s (s.getReg .x13)) : Main.WalkCallSpec := by
  intro s hpc hpre
  obtain ⟨t, hr, h⟩ := hW s hpc ⟨walkPre_of hpre, openMappedA_of hpre.proof, hO s hpre⟩
  exact ⟨t, hr, h.imp_left fun ⟨hpc', hpres, hpost⟩ ↦ ⟨hpc', hpres, walkCallPost_of hpre hpost⟩⟩

/-- DEREF, JUMP and R9, from the proved callees. -/
theorem derefJump : ∀ s u A k R Q B Bb, Walk.WalkPre s → Walk.AtDeref OI s u A k R Q B Bb →
    ∃ t, Reaches Image.code u t ∧ ((∃ A k R Q B, Walk.AtR10 OI s t A k R Q B) ∨ Walk.Done OI s t ∨
      Dead Image.code t) := by
  intro s u A k R Q B Bb hpre h
  obtain ⟨t, hr, ht | hd⟩ := Walk.derefToR10 Layout.col_proved Layout.prod_proved
    Layout.add_scaled_proved Layout.state_step_proved Layout.state_derived_proved Runtime.alloc_spec
    Layout.term_proved Layout.bytecode_proved Layout.memory_cols_proved Layout.memory_proved
    Multilinear.fromElem Runtime.memcpy hpre h
  · exact ⟨t, hr, Or.inl ⟨_, _, _, _, _, ht⟩⟩
  · exact ⟨t, hr, Or.inr (Or.inr hd)⟩

/-- R19 and R20, from R18's exit to `AtR21`, given `verify_keccak`'s contract as `walk` calls it. -/
theorem r1920 (hVK : Walk.VerifyKeccakSpecE) : Walk.R19R20 OI := by
  intro s u₀ w t u layout rows lir bus evs P C L hpre h X
  obtain ⟨v, hr, ⟨P', C', L', pub, A⟩ | hd⟩ := Walk.r19 Transcript.duplex Multilinear.fromElem cloneE
    Runtime.alloc_spec Rv64Verifier.Runtime.reserveFast_80008a10 Multilinear.scalerNew Field.mul
    Rv64Verifier.Runtime.growOneFresh_8000c0a4 hpre h X
  · obtain ⟨x, hr', ⟨P'', C'', L'', cl, pt, sl, ks, ke, H⟩ | hx | hx⟩ := Walk.r20 hVK
      Rv64Verifier.Runtime.growOneFresh_8000c0a4 Runtime.Drop.drop_nop_spec Runtime.dropLayout
      hpre h A
    · exact ⟨x, hr.trans hr', Or.inl ⟨w, t, evs, P'', C'', L'', cl, pt, sl, ks, ke, H⟩⟩
    · exact ⟨x, hr.trans hr', Or.inr (Or.inl hx)⟩
    · exact ⟨x, hr.trans hr', Or.inr (Or.inr hx)⟩
  · exact ⟨v, hr, Or.inr (Or.inr hd)⟩

/-- **`walk`'s contract**, given `verify_bus_balance`'s and its reading of the `Bytecode`,
`verify_keccak`'s, `extend_desugared`'s and `verify_stacked_opening`'s. -/
theorem walkSpec {BcOk : MachineState → Nat → Word → Prop}
    {bev : MachineState → Word → List E → Option E} (hBB : Bus.BusBalanceSpec BcOk bev)
    (hBW : Walk.BcWalk BcOk bev) (hVK : Walk.VerifyKeccakSpecE) (hE : Walk.ExtendSpecE)
    (hV : PcsContracts.VsoSpec Transcript.OpeningsAt) : Walk.WalkSpecO OI :=
  Walk.walk_spec_of' (Walk.front derefJump hBB hBW)
    (Walk.tail_of Transcript.duplex Multilinear.powers Multilinear.dot tableSumcheckClosed
      Runtime.Drop.drop_nop_spec Runtime.dropLayout cloneE Runtime.growAmortized Pcs.ringSwitch
      Runtime.alloc_spec hE hV openBridge (r1920 hVK))

end Rv64Verifier.Proofs.Final

/-! Lean's three axioms, nothing native. -/

/-- info: 'Rv64Verifier.Proofs.Final.openBridge' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Rv64Verifier.Proofs.Final.openBridge

/-- info: 'Rv64Verifier.Proofs.Final.walkCall_of_walkO' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Rv64Verifier.Proofs.Final.walkCall_of_walkO

/-- info: 'Rv64Verifier.Proofs.Final.derefJump' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Rv64Verifier.Proofs.Final.derefJump

/-- info: 'Rv64Verifier.Proofs.Final.r1920' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Rv64Verifier.Proofs.Final.r1920

/-- info: 'Rv64Verifier.Proofs.Final.walkSpec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Rv64Verifier.Proofs.Final.walkSpec
