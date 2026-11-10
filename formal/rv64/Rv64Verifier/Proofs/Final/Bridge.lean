import Rv64Verifier.Proofs.Walk.Contracts
import Rv64Verifier.Proofs.Main.Contracts
import Rv64Verifier.Proofs.Transcript.Openings

/-!
# `walk`'s contract gives `main`'s view of it

`walkCall_of_walk`: `WalkSpec OI` gives `WalkCallSpec`, for `OI` the openings `main` reads
(`readProof`) with every buffer in place (`ProofMem`). From `OI`, `OI.openingsAt`,
`OI.openMapped` and `OI.openFits` give `verify_stacked_opening`'s `OpeningsAt`, `OpenMapped` and
`OpenFits` of a transcript whose proof it is.
-/

namespace Rv64Verifier.Proofs.Final
open RiscvZkvm.Rv64 LeanVM.Protocol LeanVM.Protocol.Compile Rv64Verifier.Runtime

/-- The openings `walk` is given: those `main` reads, their buffers in place. -/
def OI (s : MachineState) (a : Word) (ops : List (List Opening)) : Prop :=
  ops = (Main.readProof s a).openings ∧ Main.ProofMem s (s.getReg .x10) a

section
variable {s : MachineState}

theorem walkStack_le : Walk.walkStack ≤ Main.walkStack := by decide

theorem walk_stack (h : RtStack s Main.walkStack) : RtStack s Walk.walkStack :=
  h.inner (t := s) (k := 0) (by simp) (by simpa using walkStack_le) (by decide) (by decide)
    (by decide) (by decide)

theorem stack_nat (h : RtStack s Main.walkStack) :
    (stackLo s Main.walkStack).toNat = (s.getReg .x2).toNat - Main.walkStack ∧
      (stackLo s Walk.walkStack).toNat = (s.getReg .x2).toNat - Walk.walkStack ∧
      Main.walkStack ≤ (s.getReg .x2).toNat := by
  have b1 := h.bounds (by decide) (by decide)
  have b2 := (walk_stack h).bounds (by decide) (by decide)
  exact ⟨b1.2.2.2, b2.2.2.2, by omega⟩

theorem apart_small (h : RtStack s Main.walkStack) {a : Word} {n : Nat}
    (ha : Apart a n (stackLo s Main.walkStack) Main.walkStack) :
    Apart a n (stackLo s Walk.walkStack) Walk.walkStack := by
  obtain ⟨e1, e2, e3⟩ := stack_nat h
  have := walkStack_le
  simp only [Apart] at ha ⊢
  rw [e1] at ha
  rw [e2]
  omega

theorem within_big (h : RtStack s Main.walkStack) {a : Word}
    (ha : Within a (stackLo s Walk.walkStack) Walk.walkStack) :
    Within a (stackLo s Main.walkStack) Main.walkStack := by
  obtain ⟨e1, e2, e3⟩ := stack_nat h
  have := walkStack_le
  simp only [Within] at ha ⊢
  rw [e1]
  rw [e2] at ha
  omega

/-- A part `main` gives is only read by `walk`; an empty one's pointer lies below `NEXT`. -/
theorem readOnly_of_part (hpre : Main.WalkCallPre s) {a : Word} {n al : Nat}
    (h : Main.Part s (s.getReg .x10) a n al) : Walk.ReadOnly s a n := by
  rcases h.2 with ⟨h0, hle⟩ | ⟨-, hout, hst, hres, hro⟩
  · exact ⟨⟨Or.inl (by omega), Or.inl h0⟩, Or.inl h0, Or.inl h0, Or.inl h0⟩
  · exact ⟨hout, apart_small hpre.stack hst, hres, hro⟩

theorem region_of_part {out a : Word} {n : Nat} (h : Main.Part s out a n 8) (hn : n ≠ 0) :
    Transcript.Region a n :=
  ⟨(h.2.resolve_left fun h' ↦ hn h'.1).1, h.1⟩

theorem mapped_of_part {out a : Word} {n m al : Nat} (hm : 0 < m)
    (h : Main.Part s out a (m * n) al) : n = 0 ∨ Mapped a (m * n) := by
  rcases h.2 with h' | h'
  · left
    rcases Nat.mul_eq_zero.mp h'.1 with h0 | h0
    · omega
    · exact h0
  · exact Or.inr h'.1

theorem bytecodeMem {out p : Word} (h : Main.BcMem s out p) : Bytecode.BytecodeMem s p where
  self := (h.self.2.resolve_left fun h' ↦ absurd h'.1 (by decide)).1
  align := h.self.1
  blocks := mapped_of_part (by decide) h.blocks
  blocksAlign := h.blocks.1
  words := mapped_of_part (by decide) h.words
  wordsAlign := h.words.1
  positions := mapped_of_part (by decide) h.positions
  positionsAlign := h.positions.1
  bytes := mapped_of_part (by decide) h.bytes
  bytesAlign := h.bytes.1

theorem walkPre_of (hpre : Main.WalkCallPre s) : Walk.WalkPre s where
  heap := hpre.heap
  stack := walk_stack hpre.stack
  rodata := hpre.rodata
  out := ⟨hpre.out.1, hpre.out.2.1⟩
  outFree := hpre.out.2.2.1
  outStack := apart_small hpre.stack hpre.out.2.2.2
  outRodata := hpre.outRodata
  bytecode := ⟨bytecodeMem hpre.bc, readOnly_of_part hpre hpre.bc.self,
    readOnly_of_part hpre hpre.bc.blocks, readOnly_of_part hpre hpre.bc.words,
    readOnly_of_part hpre hpre.bc.positions, readOnly_of_part hpre hpre.bc.bytes⟩
  input := region_of_part hpre.publicInput (by decide)
  inputRO := readOnly_of_part hpre hpre.publicInput
  proof := region_of_part hpre.proof.self (by decide)
  proofRO := readOnly_of_part hpre hpre.proof.self
  stream := (mapped_of_part (by decide) hpre.proof.stream).imp_right fun h ↦ ⟨h, hpre.proof.stream.1⟩
  streamRO := readOnly_of_part hpre hpre.proof.stream
  aligned := fun h ↦ hpre.aligned (Or.inl h)

theorem proofIn (hpre : Main.WalkCallPre s) :
    Walk.ProofIn OI s (s.getReg .x13) (Main.readProof s (s.getReg .x13)) where
  stream := rfl
  openingsLen := by simp [Main.readProof]
  openings := ⟨rfl, hpre.proof⟩

theorem walkCallPost_of (hpre : Main.WalkCallPre s) {t : MachineState} (h : Walk.WalkPost OI s t) :
    Main.WalkCallPost s t where
  heap := h.heap
  ok := fun hne ↦ h.ok hne _ (proofIn hpre)
  frame := h.frame.mono fun a ha ↦ by
    unfold Walk.WalkW at ha
    rcases ha with ha | ha | ha | ha
    · exact Or.inl ha
    · exact Or.inr (Or.inl (within_big hpre.stack ha))
    · exact Or.inr (Or.inr (Or.inl ha))
    · exact Or.inr (Or.inr (Or.inr ha))

end

/-- **`walk`'s contract gives the one `main` uses.** -/
theorem walkCall_of_walk (hW : Walk.WalkSpec OI) : Main.WalkCallSpec := by
  intro s hpc hpre
  obtain ⟨t, hr, h⟩ := hW s hpc (walkPre_of hpre)
  exact ⟨t, hr, h.imp_left fun ⟨hpc', hpres, hpost⟩ ↦ ⟨hpc', hpres, walkCallPost_of hpre hpost⟩⟩

/-! ## What `OI` gives `verify_stacked_opening` -/

section
variable {s : MachineState}

theorem laneOfBytes_eq (x : Nat → BitVec 8) :
    Transcript.laneOfBytes ((List.range 8).map x) =
      UInt64.ofBitVec (Model.fromLeBytes ((List.range 8).map x)) := by
  simp only [Transcript.laneOfBytes, Model.fromLeBytes,
    show List.range 8 = [0, 1, 2, 3, 4, 5, 6, 7] from rfl, List.map_cons, List.map_nil,
    List.foldr_cons, List.foldr_nil, List.foldl_cons, List.foldl_nil, List.getD_cons_zero,
    List.getD_cons_succ, BitVec.shiftLeft_or_distrib, ← BitVec.shiftLeft_add, Nat.reduceAdd,
    Nat.reduceMul, BitVec.shiftLeft_zero]
  have h0 : (0 : BitVec 64) <<< 64 = 0 := by decide
  rw [h0]
  generalize BitVec.setWidth 64 (x 0) = y0
  generalize BitVec.setWidth 64 (x 1) <<< 8 = y1
  generalize BitVec.setWidth 64 (x 2) <<< 16 = y2
  generalize BitVec.setWidth 64 (x 3) <<< 24 = y3
  generalize BitVec.setWidth 64 (x 4) <<< 32 = y4
  generalize BitVec.setWidth 64 (x 5) <<< 40 = y5
  generalize BitVec.setWidth 64 (x 6) <<< 48 = y6
  generalize BitVec.setWidth 64 (x 7) <<< 56 = y7
  exact congrArg UInt64.ofBitVec (by ac_rfl)

theorem digestBytesAt_eq (a : Word) :
    Transcript.digestBytesAt s a = Main.digestOfBytes (bytesAt s a 32) := by
  unfold Transcript.digestBytesAt Main.digestOfBytes
  congr 1
  funext i
  have hi := i.isLt
  have hb : Contracts.bytesAt s (a + BitVec.ofNat 64 (8 * i.val)) 8 =
      (List.range 8).map fun j ↦ s.getByte (a + BitVec.ofNat 64 (8 * i.val + j)) := by
    simp only [Contracts.bytesAt]
    refine List.map_congr_left fun j _ ↦ ?_
    rw [BitVec.ofNat_add, BitVec.add_assoc]
  have hw : (Model.digestWordsRust (bytesAt s a 32)).getD i.val 0 =
      Model.fromLeBytes ((List.range 8).map fun j ↦ s.getByte (a + BitVec.ofNat 64 (8 * i.val + j))) := by
    simp only [Model.digestWordsRust]
    rw [List.getD_eq_getElem _ _ (by simp only [List.length_map, List.length_range]; omega), List.getElem_map, List.getElem_range]
    congr 1
    apply List.ext_getElem (by simp [bytesAt_length]; omega)
    intro j h1 h2
    simp only [List.length_map, List.length_range] at h2
    simp only [List.getElem_take, List.getElem_drop, bytesAt, byteAt, List.getElem_map,
      List.getElem_range]
  rw [hb, laneOfBytes_eq, hw]

theorem pathAt_self (b : Word) : Transcript.PathAt s b (Main.pathAt s b) where
  leaf := by
    simp only [Transcript.kListAt, Main.pathAt, vecWords, readWords_eq_map, List.map_map]
    rfl
  path := by
    simp only [Main.pathAt]
    exact List.map_congr_left fun k _ ↦ digestBytesAt_eq _
  leafIndex := rfl

theorem phaseAt_self (q : Word) : Transcript.PhaseAt s q (Main.phaseAt s q) where
  len := by simp [Main.phaseAt]
  paths j hj := by
    simp only [Main.phaseAt, List.getElem_map, List.getElem_range]
    exact pathAt_self _

/-- The openings `OI` gives are those of a transcript whose proof it is. -/
theorem OI.openingsAt {a : Word} {ops : List (List Opening)} (h : OI s a ops) {p : Word}
    (hp : Transcript.proofAt s p = a) {T : Model.TState} (hT : T.proof.openings = ops) :
    Transcript.OpeningsAt s p T := by
  have key : ∀ L, L = (Main.readProof s a).openings → ∀ k (hk : k < L.length),
      Transcript.PhaseAt s (vecPtr s (a + 24) + BitVec.ofNat 64 (24 * k)) L[k] := by
    intro L hL k hk
    subst hL
    simp only [Main.readProof, List.getElem_map, List.getElem_range]
    exact phaseAt_self _
  have hv : Transcript.openingsVec s p = a + 24 := by simp only [Transcript.openingsVec, hp]
  refine ⟨?_, fun k hk ↦ ?_⟩
  · rw [hv, hT, h.1]
    simp [Main.readProof]
  · rw [hv]
    exact key _ (hT.trans h.1) k hk

theorem zero_or_region {out a : Word} {n m : Nat} (hm : 0 < m) (h : Main.Part s out a (m * n) 8) :
    n = 0 ∨ Transcript.Region a (m * n) :=
  (mapped_of_part hm h).imp_right fun h' ↦ ⟨h', h.1⟩

/-- The buffers the openings `OI` gives read are mapped and aligned as their types ask. -/
theorem OI.openMapped {a : Word} {ops : List (List Opening)} (h : OI s a ops) {p : Word}
    (hp : Transcript.proofAt s p = a) : Transcript.OpenMapped s p := by
  have hv : Transcript.openingsVec s p = a + 24 := by simp only [Transcript.openingsVec, hp]
  have hm := h.2
  refine ⟨by rw [hv]; exact zero_or_region (by decide) hm.openings, fun k hk ↦ ?_⟩
  rw [hv] at hk ⊢
  have hph := hm.phases k hk
  refine ⟨zero_or_region (by decide) hph.buf, fun j hj ↦ ?_⟩
  have hpa := hph.paths j hj
  exact ⟨zero_or_region (by decide) hpa.leaf, mapped_of_part (by decide) hpa.siblings⟩

/-- The buffers the openings `OI` gives read do not wrap. -/
theorem OI.openFits {a : Word} {ops : List (List Opening)} (h : OI s a ops) {p : Word}
    (hp : Transcript.proofAt s p = a) : Transcript.OpenFits s p :=
  (h.openMapped hp).fits

end

end Rv64Verifier.Proofs.Final
