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
`OI` places. `walkCall_of_walkO`: `main`'s view of it; the doublewords the openings read miss what
`walk` writes (`openRO_of`): any of them shares a doubleword with a byte `main` gives apart from
it, and `NEXT` is aligned once there are openings (`WalkCallPre.aligned`).
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

/-! ## The openings' doublewords miss what `walk` writes -/

section
variable {s : MachineState}

/-- A byte sharing a doubleword with a byte of a part `main` gives misses what `walk` writes, `NEXT`
aligned. -/
theorem dword_ro (hpre : Main.WalkCallPre s) (h8 : heapNext s % 8 = 0) {b y z : Word} {n al : Nat}
    (h : Main.Part s (s.getReg .x10) b n al) (hz : Within z b n) (hyz : y.toNat / 8 = z.toNat / 8) :
    ¬ (Within y (s.getReg .x10) 80 ∨ Within y (stackLo s Walk.walkStack) Walk.walkStack ∨
      Within y nextAddr 8 ∨ (heapNext s ≤ y.toNat ∧ y.toNat < heapEnd) ∨ y.toNat < 8) := by
  simp only [Within] at hz
  rcases h.2 with ⟨h0, -⟩ | ⟨hm, ⟨ho, hn⟩, hst, hres, -⟩
  · omega
  obtain ⟨e1, e2, e3⟩ := stack_nat hpre.stack
  have hsp := hpre.stack.aligned
  have hx := hpre.out.2.1
  have hle := walkStack_le
  have hN : nextAddr.toNat = 0xa0000f30 := rfl
  have hE : heapEnd = 0x78000000 := rfl
  have hMS : Main.walkStack = 0x1000000 := rfl
  simp only [Apart, Main.walkOutSize] at hres hst hn
  simp only [Runtime.Mapped] at hm
  rw [e1] at hst
  simp only [Within]
  rw [e2]
  rintro (hw | hw | hw | hw | hw) <;> omega

/-- A byte of the doublewords holding `h` digests from `b`, which `main` gives, shares a
doubleword with one of their bytes. -/
theorem sib_dword {b y : Word} {h : Nat} (hb : b.toNat + 32 * h ≤ 2 ^ 64)
    (hy : Within y (b &&& ~~~7#64) (Transcript.sibSpan b h)) :
    ∃ z, Within z b (32 * h) ∧ y.toNat / 8 = z.toNat / 8 := by
  have hal := Sym.alignToDword_toNat b
  simp only [alignToDword] at hal
  simp only [Within, Transcript.sibSpan, hal] at hy ⊢
  have hh : 0 < h := by
    rcases Nat.eq_zero_or_pos h with h0 | h0
    · subst h0; omega
    · exact h0
  by_cases h1 : y.toNat < b.toNat
  · exact ⟨b, ⟨by omega, by omega⟩, by omega⟩
  by_cases h2 : b.toNat + 32 * h ≤ y.toNat
  · refine ⟨BitVec.ofNat 64 (b.toNat + 32 * h - 1), ?_⟩
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show b.toNat + 32 * h - 1 < 2 ^ 64 by omega)]
    exact ⟨⟨by omega, by omega⟩, by omega⟩
  · exact ⟨y, ⟨by omega, by omega⟩, rfl⟩

/-- **What the openings `main` gives read misses what `walk` writes.** -/
theorem openRO_of (hpre : Main.WalkCallPre s) : Walk.OpenRO s (s.getReg .x13) := by
  intro y hy
  have hm := hpre.proof
  have hlen : (vecLen s (s.getReg .x13 + 24)).toNat ≠ 0 := by
    rcases hy with hy | ⟨k, hk, -⟩
    · simp only [Within] at hy; omega
    · omega
  have h8 := hpre.aligned (Or.inr hlen)
  rcases hy with hy | ⟨k, hk, hy⟩
  · exact dword_ro hpre h8 hm.openings hy rfl
  have hph := hm.phases k hk
  rcases hy with hy | ⟨j, hj, hy⟩
  · exact dword_ro hpre h8 hph.buf hy rfl
  have hpa := hph.paths j hj
  rcases hy with hy | hy
  · exact dword_ro hpre h8 hpa.leaf hy rfl
  · have hfit : (vecPtr s (vecPtr s (vecPtr s (s.getReg .x13 + 24) + BitVec.ofNat 64 (24 * k)) +
        BitVec.ofNat 64 (56 * j) + 24)).toNat + 32 * (vecLen s (vecPtr s (vecPtr s
          (s.getReg .x13 + 24) + BitVec.ofNat 64 (24 * k)) + BitVec.ofNat 64 (56 * j) + 24)).toNat ≤
          2 ^ 64 := by
      rcases hpa.siblings.2 with ⟨h0, -⟩ | ⟨hmp, -⟩
      · have := (vecPtr s (vecPtr s (vecPtr s (s.getReg .x13 + 24) + BitVec.ofNat 64 (24 * k)) +
          BitVec.ofNat 64 (56 * j) + 24)).isLt
        omega
      · simp only [Runtime.Mapped] at hmp; omega
    obtain ⟨z, hz, hyz⟩ := sib_dword hfit hy
    exact dword_ro hpre h8 hpa.siblings hz hyz

end

/-- The openings `OI` places at `walk`'s entry are those `verify_stacked_opening` reads. -/
theorem openBridge : Walk.OpenBridge OI Transcript.OpeningsAt := by
  intro s v T hpre hO I hptr _ _ hOI
  have hA := (Walk.openKeep hpre hO I).1 _ (OI.openingsAtA hOI)
  have hp : Transcript.proofAt v (Walk.tp s) = s.getReg .x13 := hptr
  rw [← hp] at hA
  exact Walk.OpeningsAtA.toP hA

/-- **`walk`'s contract gives the one `main` uses.** -/
theorem walkCall_of_walkO (hW : Walk.WalkSpecO OI) : Main.WalkCallSpec := by
  intro s hpc hpre
  obtain ⟨t, hr, h⟩ := hW s hpc ⟨walkPre_of hpre, openMappedA_of hpre.proof, openRO_of hpre⟩
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

/-- info: 'Rv64Verifier.Proofs.Final.openRO_of' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Rv64Verifier.Proofs.Final.openRO_of

/-- info: 'Rv64Verifier.Proofs.Final.walkCall_of_walkO' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Rv64Verifier.Proofs.Final.walkCall_of_walkO

/-- info: 'Rv64Verifier.Proofs.Final.derefJump' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Rv64Verifier.Proofs.Final.derefJump

/-- info: 'Rv64Verifier.Proofs.Final.r1920' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Rv64Verifier.Proofs.Final.r1920

/-- info: 'Rv64Verifier.Proofs.Final.walkSpec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Rv64Verifier.Proofs.Final.walkSpec
