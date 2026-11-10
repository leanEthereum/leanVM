import Rv64Verifier.Proofs.Pcs.VsoCalls
import Rv64Verifier.Proofs.Pcs.VsoSibCopy
import Rv64Verifier.Proofs.Hash.Bytes
import Rv64Verifier.Proofs.Transcript.Keccak
import Rv64Verifier.Proofs.Pcs.VsoMerkle

/-!
# `verify_stacked_opening`'s Merkle checks: a path's climb

`MerklePath::root`'s loop over the siblings, at `0x8000af10`, `S` the entry's `sp`: the node's 32
bytes at `S - 160`, the leaf index at `S - 784`, `s2` the next sibling, `s5` the level, `s11` the
siblings' count. Each level puts the node and the sibling, in the order the index's bit says, in a
64-byte buffer at `S - 384` (`0x8000abfc` or `0x8000af20`, then `memcpy` at `0x8000ad78`), hashes it
to `S - 464` (`keccak_hash` at `0x8000ad80`) and copies the digest back to the node
(`0x8000ad94`). After the last level it goes on at `0x8000ab04` (`Climbed`), the node
`climbBytes` of the siblings.
-/

namespace Rv64Verifier.Proofs.Pcs.Vso
open RiscvZkvm.Rv64 LeanVM.Parameters Rv64Verifier.Contracts Rv64Verifier.Runtime
  Rv64Verifier.Transcript Rv64Verifier.Pcs Rv64Verifier.PcsContracts Rv64Verifier.Blocks.F38
open Rv64Verifier.Sym (reduceReg reducePc reduceMem reduceWrites reduceObl)

/-! ## Bytes -/

theorem bytesAt_rt (s : MachineState) (a : Word) (n : ℕ) :
    Runtime.bytesAt s a n = Contracts.bytesAt s a n := rfl

theorem bytesAt_64 (s : MachineState) (a : Word) :
    Contracts.bytesAt s a 64 = Contracts.bytesAt s a 32 ++ Contracts.bytesAt s (a + 32) 32 := by
  simp only [Contracts.bytesAt, show (64 : ℕ) = 32 + 32 from rfl, List.range_add, List.map_append,
    List.map_map]
  congr 1
  apply List.map_congr_left
  intro i _
  simp only [Function.comp, BitVec.add_assoc, BitVec.ofNat_add]
  rfl

/-- Four doublewords that `t` holds as `s` held four others. -/
theorem bytesAt_of_four {s t : MachineState} {a b : Word} (ha : a.toNat % 8 = 0)
    (hb : b.toNat % 8 = 0) (h0 : t.getMem a = s.getMem b) (h1 : t.getMem (a + 8) = s.getMem (b + 8))
    (h2 : t.getMem (a + 16) = s.getMem (b + 16)) (h3 : t.getMem (a + 24) = s.getMem (b + 24)) :
    Contracts.bytesAt t a 32 = Contracts.bytesAt s b 32 := by
  refine bytesAt_of_dwords ha hb fun m hm ↦ ?_
  interval_cases m
  · simpa using h0
  · exact h1
  · exact h2
  · exact h3

/-- 32 aligned bytes that a frame misses are kept. -/
theorem DFrame.bytes32 {u v : MachineState} {X : Word → Prop} (hX : DFrame u v X) {a : Word}
    (ha : a.toNat % 8 = 0) (hw : a.toNat + 32 ≤ 2 ^ 64) (hm : ∀ y, Within y a 32 → ¬ X y) :
    Contracts.bytesAt v a 32 = Contracts.bytesAt u a 32 := by
  refine bytesAt_of_dwords ha ha fun m hm4 ↦ hX _ fun i hi hx ↦ hm _ ?_ hx
  addr_omega [hw, hi, hm4]

/-! ## The blocks' copies -/

theorem af20_bytes {s t : MachineState} (h : b8000af20.Holds s t) (h8 : (s.getReg .x2).toNat % 8 = 0)
    (hw : (s.getReg .x2).toNat + 912 ≤ 2 ^ 64) :
    Contracts.bytesAt t (s.getReg .x2 + 656) 32 = Contracts.bytesAt s (s.getReg .x2 + 880) 32 := by
  refine bytesAt_of_four (by addr_omega [h8, hw]) (by addr_omega [h8, hw]) ?_ ?_ ?_ ?_
  · exact h.mem_eq 3 (by decide) (by rv_eval []) (by
      simp only [reduceMem, List.getElem_cons_succ, List.getElem_cons_zero, Sym.E.eval,
        Sym.BinOp.eval, Sym.UnOp.eval, Sym.LoadKind.fromWord]
      rw [show s.getReg .x2 + 880 = s.getReg .x2 + 880#64 from rfl]; exact reassemble _)
  · exact h.mem_eq 2 (by decide) (by rv_eval []) (by
      simp only [reduceMem, List.getElem_cons_succ, List.getElem_cons_zero, Sym.E.eval,
        Sym.BinOp.eval, Sym.UnOp.eval, Sym.LoadKind.fromWord]
      rw [show s.getReg .x2 + 880 + 8 = s.getReg .x2 + 888#64 by rv_eval []]; exact reassemble _)
  · exact h.mem_eq 1 (by decide) (by rv_eval []) (by
      simp only [reduceMem, List.getElem_cons_succ, List.getElem_cons_zero, Sym.E.eval,
        Sym.BinOp.eval, Sym.UnOp.eval, Sym.LoadKind.fromWord]
      rw [show s.getReg .x2 + 880 + 16 = s.getReg .x2 + 896#64 by rv_eval []]; exact reassemble _)
  · exact h.mem_eq 0 (by decide) (by rv_eval []) (by
      simp only [reduceMem, List.getElem_cons_zero, Sym.E.eval,
        Sym.BinOp.eval, Sym.UnOp.eval, Sym.LoadKind.fromWord]
      rw [show s.getReg .x2 + 880 + 24 = s.getReg .x2 + 904#64 by rv_eval []]; exact reassemble _)

theorem ad94_bytes {s t : MachineState} (h : b8000ad94.Holds s t) (h8 : (s.getReg .x2).toNat % 8 = 0)
    (hw : (s.getReg .x2).toNat + 912 ≤ 2 ^ 64) :
    Contracts.bytesAt t (s.getReg .x2 + 880) 32 = Contracts.bytesAt s (s.getReg .x2 + 576) 32 := by
  refine bytesAt_of_four (by addr_omega [h8, hw]) (by addr_omega [h8, hw]) ?_ ?_ ?_ ?_
  · exact h.mem_eq 3 (by decide) (by rv_eval []) (by
      simp only [reduceMem, List.getElem_cons_succ, List.getElem_cons_zero, Sym.E.eval,
        Sym.BinOp.eval, Sym.UnOp.eval, Sym.LoadKind.fromWord]
      rw [show s.getReg .x2 + 576 = s.getReg .x2 + 576#64 from rfl]; exact reassemble _)
  · exact h.mem_eq 2 (by decide) (by rv_eval []) (by
      simp only [reduceMem, List.getElem_cons_succ, List.getElem_cons_zero, Sym.E.eval,
        Sym.BinOp.eval, Sym.UnOp.eval, Sym.LoadKind.fromWord]
      rw [show s.getReg .x2 + 576 + 8 = s.getReg .x2 + 584#64 by rv_eval []]; exact reassemble _)
  · exact h.mem_eq 1 (by decide) (by rv_eval []) (by
      simp only [reduceMem, List.getElem_cons_succ, List.getElem_cons_zero, Sym.E.eval,
        Sym.BinOp.eval, Sym.UnOp.eval, Sym.LoadKind.fromWord]
      rw [show s.getReg .x2 + 576 + 16 = s.getReg .x2 + 592#64 by rv_eval []]; exact reassemble _)
  · exact h.mem_eq 0 (by decide) (by rv_eval []) (by
      simp only [reduceMem, List.getElem_cons_zero, Sym.E.eval,
        Sym.BinOp.eval, Sym.UnOp.eval, Sym.LoadKind.fromWord]
      rw [show s.getReg .x2 + 576 + 24 = s.getReg .x2 + 600#64 by rv_eval []]; exact reassemble _)

/-! ## The callees -/

theorem stack_mapped {s : MachineState} (hpre : VsoPre s) :
    0xa0000000 ≤ (s.getReg .x2 - 2464).toNat ∧ (s.getReg .x2).toNat ≤ 0xc0000008 ∧
      (s.getReg .x2).toNat % 16 = 0 ∧ 2464 ≤ (s.getReg .x2).toNat := by
  have hm := hpre.stack.mapped (by decide) (by decide)
  have hb := bounds hpre
  rw [stackLo_vso, vso_stack] at hm
  refine ⟨hm.1, hb.2.1, hb.2.2, by omega⟩

/-- `memcpy` of 32 bytes to `S - 352`. -/
theorem callMemcpy (hM : Runtime.MemcpySpec 0x800126e4) {s t : MachineState} (hpre : VsoPre s)
    (hpc : t.pc = 0x800126e4) (hsp : t.getReg .x2 = s.getReg .x2 - 1040)
    (hx10 : t.getReg .x10 = s.getReg .x2 - 352) (hx12 : t.getReg .x12 = 32)
    (hsrc : Mapped (t.getReg .x11) 32) (hsa : Apart (t.getReg .x11) 32 (s.getReg .x2 - 2464) 2464 ∨
      t.getReg .x11 = s.getReg .x2 - 160) :
    ∃ v, Reaches Image.code t v ∧ (Dead Image.code v ∨ (v.pc = returnAddress t ∧ Preserves t v ∧
      Contracts.bytesAt v (s.getReg .x2 - 352) 32 = Contracts.bytesAt t (t.getReg .x11) 32 ∧
      DFrame t v fun a ↦ Within a (s.getReg .x2 - 352) 32 ∨ Within a (s.getReg .x2 - 1056) 16)) := by
  have hm := stack_mapped hpre
  have hsl : stackLo t memcpyStack = s.getReg .x2 - 1056 := by
    simp only [stackLo, memcpyStack, hsp]; rv_eval []
  have h32 : (t.getReg .x12).toNat = 32 := by rw [hx12]; rfl
  have hpreM : Runtime.MemcpyPre t := {
    dst := by rw [hx10, h32]; addr_omega [hm]
    src := by rw [h32]; exact hsrc
    apart := by
      rw [hx10, h32]
      rcases hsa with h | h
      · addr_omega [h, hm]
      · rw [h]; addr_omega [hm]
    stack := (hpre.stack.sub 1040 hsp (by decide) (by decide) (by decide) (by decide)
      (by decide)).toStackOk
    dstStack := by rw [hx10, h32, hsl]; addr_omega [hm]
    srcStack := by
      rw [h32, hsl]
      rcases hsa with h | h
      · addr_omega [h, hm]
      · rw [h]; addr_omega [hm] }
  obtain ⟨v, hr, ⟨hpc', hpres, hpost⟩ | hdead⟩ := hM.call (Reaches.refl t) hpc hpreM
  · have hb := hpost.bytes
    have hf := DFrame.of_byteFrame hpost.frame
    rw [hx10, h32, bytesAt_rt, bytesAt_rt] at hb
    rw [hx10, h32, hsl] at hf
    exact ⟨v, hr, Or.inr ⟨hpc', hpres, hb, hf⟩⟩
  · exact ⟨v, hr, Or.inl hdead⟩

/-- `keccak_hash` of the 64 bytes at `S - 384` into `S - 464`. -/
theorem callKeccak (hK : KeccakHashSpec) {s t : MachineState} (hpre : VsoPre s)
    (hpc : t.pc = 0x8000c8e0) (hsp : t.getReg .x2 = s.getReg .x2 - 1040)
    (hx10 : t.getReg .x10 = s.getReg .x2 - 464) (hx11 : t.getReg .x11 = s.getReg .x2 - 384)
    (hx12 : t.getReg .x12 = 64) (hrod : RodataOk t) :
    ∃ v, Reaches Image.code t v ∧ (Dead Image.code v ∨ (v.pc = returnAddress t ∧ Preserves t v ∧
      Contracts.bytesAt v (s.getReg .x2 - 464) 32 =
        Model.keccakHashRust (Contracts.bytesAt t (s.getReg .x2 - 384) 64) ∧
      DFrame t v fun a ↦ Within a (s.getReg .x2 - 464) 32 ∨ Within a (s.getReg .x2 - 2144) 1104)) := by
  have hm := stack_mapped hpre
  have hro := hpre.stack.rodata
  rw [stackLo_vso, vso_stack] at hro
  have hsl : stackLo t keccakHashStack = s.getReg .x2 - 2144 := by
    simp only [stackLo, keccakHashStack, keccakFStack, memStack, hsp, Nat.reduceAdd]; rv_eval []
  have h64 : (t.getReg .x12).toNat = 64 := by rw [hx12]; rfl
  have hpreK : KeccakHashPre t := {
    out := by rw [hx10]; exact bytesValid_ram (by addr_omega [hm]) (by addr_omega [hm])
    outAligned := by rw [hx10]; addr_omega [hm]
    data := by rw [hx11, h64]; addr_omega [hm]
    stack := (hpre.stack.sub 1040 hsp (by decide) (by decide) (by decide) (by decide)
      (by decide)).toStackOk
    outStack := by rw [hx10, hsl]; addr_omega [hm]
    dataStack := by rw [hx11, h64, hsl]; addr_omega [hm]
    tables := keccakTables_of_rodata hrod
    tablesStack := by rw [hsl]; addr_omega [hro, hm] }
  obtain ⟨v, hr, ⟨hpc', hpres, hpost⟩ | hdead⟩ := hK.call (Reaches.refl t) hpc hpreK
  · have hb := hpost.value
    have hf := DFrame.of_two hpost.frame
    rw [hx10, hx11, h64] at hb
    rw [hx10, hsl] at hf
    exact ⟨v, hr, Or.inr ⟨hpc', hpres, hb, hf⟩⟩
  · exact ⟨v, hr, Or.inl hdead⟩

/-! ## A level of the climb -/

/-- What the climb writes: the callees' stacks, the digest, the buffer, the node. -/
def CW (s : MachineState) (a : Word) : Prop :=
  Within a (s.getReg .x2 - 2464) 1424 ∨ Within a (s.getReg .x2 - 464) 32 ∨
    Within a (s.getReg .x2 - 384) 64 ∨ Within a (s.getReg .x2 - 160) 32

/-- From `0x8000ad78`, the buffer's first half `B1` and the source `B2` of its second: `memcpy`,
`keccak_hash`, the digest copied to the node, the level counted. -/
theorem climb_tail (hM : Runtime.MemcpySpec 0x800126e4) (hK : KeccakHashSpec) {s t : MachineState}
    {sib : Word} {j n : ℕ} {B1 B2 : List (BitVec 8)} (hpre : VsoPre s) (hreg : Mapped sib (32 * n))
    (hap : Apart sib (32 * n) (s.getReg .x2 - 2464) 2464) (hjn : j < n)
    (hpc : t.pc = 0x8000ad78) (hsp : t.getReg .x2 = s.getReg .x2 - 1040)
    (hx10 : t.getReg .x10 = s.getReg .x2 - 352) (hx12 : t.getReg .x12 = 32)
    (hx18 : t.getReg .x18 = sib + BitVec.ofNat 64 (32 * j)) (hx21 : t.getReg .x21 = BitVec.ofNat 64 j)
    (hx27 : t.getReg .x27 = BitVec.ofNat 64 n)
    (hsrc : t.getReg .x11 = sib + BitVec.ofNat 64 (32 * j) ∨ t.getReg .x11 = s.getReg .x2 - 160)
    (hB1 : Contracts.bytesAt t (s.getReg .x2 - 384) 32 = B1)
    (hB2 : Contracts.bytesAt t (t.getReg .x11) 32 = B2) (hrod : RodataOk t) :
    ∃ v, Reaches Image.code t v ∧ (Dead Image.code v ∨ (DFrame t v (CW s) ∧
      v.getReg .x2 = s.getReg .x2 - 1040 ∧ (∀ r ∈ [Reg.x9, .x24, .x25, .x26], v.getReg r = t.getReg r) ∧
      v.getReg .x18 = sib + BitVec.ofNat 64 (32 * (j + 1)) ∧ v.getReg .x21 = BitVec.ofNat 64 (j + 1) ∧
      v.getReg .x27 = BitVec.ofNat 64 n ∧
      Contracts.bytesAt v (s.getReg .x2 - 160) 32 = Model.keccakHashRust (B1 ++ B2) ∧
      ((j + 1 < n ∧ v.pc = 0x8000af10) ∨ (j + 1 = n ∧ v.pc = 0x8000ab04)))) := by
  have hm := stack_mapped hpre
  have hR := hreg
  simp only [Mapped] at hR
  -- `memcpy`
  obtain ⟨t1, r1, h1⟩ := Sym.BlockSpec.reaches b8000ad78_spec hpc trivial
  have k1 := b8000ad78_keeps h1
  have m1 := b8000ad78_mem_same h1
  have sp1 : t1.getReg .x2 = s.getReg .x2 - 1040 := (k1 .x2 (by decide)).trans hsp
  have ra1 : t1.getReg .x1 = 0x8000ad80 := b8000ad78_x1 h1
  have src1 : t1.getReg .x11 = t.getReg .x11 := k1 .x11 (by decide)
  obtain ⟨t2, r2, hv2⟩ := callMemcpy hM hpre (b8000ad78_pc h1) sp1
    (by rw [k1 .x10 (by decide), hx10]) (by rw [k1 .x12 (by decide), hx12])
    (by rw [src1]; rcases hsrc with h | h <;> rw [h] <;> addr_omega [hR, hjn, hm])
    (by rw [src1]; rcases hsrc with h | h
        · exact Or.inl (by rw [h]; addr_omega [hap, hR, hjn, hm])
        · exact Or.inr h)
  rcases hv2 with hd | ⟨pc2, pr2, by2, fr2⟩
  · exact ⟨t2, r1.trans r2, Or.inl hd⟩
  have sp2 : t2.getReg .x2 = s.getReg .x2 - 1040 := (pr2.reg .x2).trans sp1
  -- `keccak_hash`
  have fr12 : DFrame t t2 (CW s) := (DFrame.of_same m1 (CW s)).trans (fr2.mono fun a ha ↦ by
    rcases ha with ha | ha
    · exact Or.inr (Or.inr (Or.inl (by addr_omega [ha, hm])))
    · exact Or.inl (by addr_omega [ha, hm])) fun _ h ↦ h
  have hro := hpre.stack.rodata
  rw [stackLo_vso, vso_stack] at hro
  have rod2 : RodataOk t2 := hrod.dframe fr12 fun a ha hw ↦ by
    rcases hw with hw | hw | hw | hw <;> addr_omega [ha, hw, hro, hm]
  obtain ⟨t3, r3, h3⟩ := Sym.BlockSpec.reaches b8000ad80_spec
    (by rw [pc2, returnAddress_eq, ra1]; rfl) trivial
  have k3 := b8000ad80_keeps h3
  have m3 := b8000ad80_mem_same h3
  have sp3 : t3.getReg .x2 = s.getReg .x2 - 1040 := (k3 .x2 (by decide)).trans sp2
  obtain ⟨t4, r4, hv4⟩ := callKeccak hK hpre (b8000ad80_pc h3) sp3
    (by rw [b8000ad80_x10 h3, sp2]; rv_eval []) (by rw [b8000ad80_x11 h3, sp2]; rv_eval [])
    (b8000ad80_x12 h3) (rod2.dframe (DFrame.of_same m3 fun _ ↦ False) fun _ _ h ↦ h)
  rcases hv4 with hd | ⟨pc4, pr4, by4, fr4⟩
  · exact ⟨t4, r1.trans (r2.trans (r3.trans r4)), Or.inl hd⟩
  have sp4 : t4.getReg .x2 = s.getReg .x2 - 1040 := (pr4.reg .x2).trans sp3
  -- the input's bytes
  have hin : Contracts.bytesAt t3 (s.getReg .x2 - 384) 64 = B1 ++ B2 := by
    rw [bytesAt_64, show s.getReg .x2 - 384 + 32 = s.getReg .x2 - 352 by rv_eval []]
    have e3 : ∀ a n, Contracts.bytesAt t3 a n = Contracts.bytesAt t2 a n := fun a n ↦ by
      simp only [Contracts.bytesAt, MachineState.getByte, m3]
    rw [e3, e3, by2, src1, ← hB1, ← hB2]
    congr 1
    · rw [DFrame.bytes32 fr2 (by addr_omega [hm]) (by addr_omega [hm]) fun y hy hw ↦ by
        rcases hw with hw | hw <;> addr_omega [hy, hw, hm]]
      simp only [Contracts.bytesAt, MachineState.getByte, m1]
    · simp only [Contracts.bytesAt, MachineState.getByte, m1]
  -- the digest to the node
  have ra3 : t3.getReg .x1 = 0x8000ad94 := b8000ad80_x1 h3
  have hj64 : j + 1 < 2 ^ 64 := by omega
  obtain ⟨t5, r5, h5⟩ := Sym.BlockSpec.reaches b8000ad94_spec
    (by rw [pc4, returnAddress_eq, ra3]; rfl) (by
      rv_eval [sp4]
      and_intros <;> first
        | exact validAccess_one (by addr_omega [hm])
        | valid_access hpre.stack.valid [hm]
        | addr_omega [hm])
  have k5 := b8000ad94_keeps h5
  have sp5 : t5.getReg .x2 = s.getReg .x2 - 1040 := (k5 .x2 (by decide)).trans sp4
  have x21₄ : t4.getReg .x21 = BitVec.ofNat 64 j := by
    rw [pr4.reg .x21, k3 .x21 (by decide), pr2.reg .x21, k1 .x21 (by decide), hx21]
  have x27₄ : t4.getReg .x27 = BitVec.ofNat 64 n := by
    rw [pr4.reg .x27, k3 .x27 (by decide), pr2.reg .x27, k1 .x27 (by decide), hx27]
  have x18₄ : t4.getReg .x18 = sib + BitVec.ofNat 64 (32 * j) := by
    rw [pr4.reg .x18, k3 .x18 (by decide), pr2.reg .x18, k1 .x18 (by decide), hx18]
  have fr5 : DFrame t4 t5 (CW s) := (DFrame.of_memFrame (b8000ad94_frame h5 (by
    rw [sp4]; addr_omega [hm]))).mono fun a ha ↦ by
      rw [sp4] at ha; exact Or.inr (Or.inr (Or.inr (by addr_omega [ha, hm])))
  have fr : DFrame t t5 (CW s) := (fr12.trans ((DFrame.of_same m3 (CW s)).trans (fr4.mono fun a ha ↦ by
    rcases ha with ha | ha
    · exact Or.inr (Or.inl ha)
    · exact Or.inl (by addr_omega [ha, hm])) fun _ h ↦ h) fun _ h ↦ h).trans fr5 fun _ h ↦ h
  have node : Contracts.bytesAt t5 (s.getReg .x2 - 160) 32 = Model.keccakHashRust (B1 ++ B2) := by
    have := ad94_bytes h5 (by rw [sp4]; addr_omega [hm]) (by rw [sp4]; addr_omega [hm])
    rw [sp4, show s.getReg .x2 - 1040 + 880 = s.getReg .x2 - 160 by rv_eval [],
      show s.getReg .x2 - 1040 + 576 = s.getReg .x2 - 464 by rv_eval [], by4, hin] at this
    exact this
  refine ⟨t5, r1.trans (r2.trans (r3.trans (r4.trans r5))), Or.inr ⟨fr, sp5, fun r hr ↦ ?_,
    by rw [b8000ad94_x18 h5, x18₄]; addr_omega [hR, hjn],
    by rw [b8000ad94_x21 h5, x21₄]; addr_omega [hj64],
    by rw [k5 .x27 (by decide), x27₄], node, ?_⟩⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · rw [k5 .x9 (by decide), pr4.reg .x9, k3 .x9 (by decide), pr2.reg .x9, k1 .x9 (by decide)]
    · rw [k5 .x24 (by decide), pr4.reg .x24, k3 .x24 (by decide), pr2.reg .x24, k1 .x24 (by decide)]
    · rw [k5 .x25 (by decide), pr4.reg .x25, k3 .x25 (by decide), pr2.reg .x25, k1 .x25 (by decide)]
    · rw [k5 .x26 (by decide), pr4.reg .x26, k3 .x26 (by decide), pr2.reg .x26, k1 .x26 (by decide)]
  · by_cases he : j + 1 = n
    · exact Or.inr ⟨he, b8000ad94_pc_taken h5 (by rw [x21₄, x27₄, ← he]; addr_omega [hj64])⟩
    · exact Or.inl ⟨by omega, b8000ad94_pc_not_taken h5 (by
        rw [x21₄, x27₄]; intro h; exact he (by addr_omega [h, hj64, hR]))⟩

/-- At `0x8000af10`, before level `j` of the climb: the siblings' bytes `sibs` from `sib`, the leaf
index `idx`, the node climbed from `leaf` through the first `j` siblings. -/
structure Climb (s : MachineState) (sib idx : Word) (leaf : List (BitVec 8))
    (sibs : List (List (BitVec 8))) (u : MachineState) (j : ℕ) : Prop where
  pc : u.pc = 0x8000af10
  sp : u.getReg .x2 = s.getReg .x2 - 1040
  x18 : u.getReg .x18 = sib + BitVec.ofNat 64 (32 * j)
  x21 : u.getReg .x21 = BitVec.ofNat 64 j
  x27 : u.getReg .x27 = BitVec.ofNat 64 sibs.length
  jlt : j < sibs.length
  index : u.getMem (s.getReg .x2 - 784) = idx
  node : Contracts.bytesAt u (s.getReg .x2 - 160) 32 = Model.Pcs.climbBytes idx 0 leaf (sibs.take j)
  sibs : ∀ i (h : i < sibs.length), Contracts.bytesAt u (sib + BitVec.ofNat 64 (32 * i)) 32 = sibs[i]
  rodata : RodataOk u

theorem climbBytes_take {idx : Word} {leaf : List (BitVec 8)} {sibs : List (List (BitVec 8))} {j : ℕ}
    (hj : j < sibs.length) :
    Model.Pcs.climbBytes idx 0 leaf (sibs.take (j + 1)) =
      Model.Pcs.climbStep idx j (Model.Pcs.climbBytes idx 0 leaf (sibs.take j)) sibs[j] := by
  rw [List.take_add_one, List.getElem?_eq_getElem hj, Option.toList_some, Model.Pcs.climbBytes_snoc,
    List.length_take, Nat.min_eq_left hj.le, Nat.zero_add]

/-- **A level of the climb.** -/
theorem climb_step (hM : Runtime.MemcpySpec 0x800126e4) (hK : KeccakHashSpec) {s u : MachineState}
    {sib idx : Word} {leaf : List (BitVec 8)} {sibs : List (List (BitVec 8))} {j : ℕ}
    (hpre : VsoPre s) (hreg : Mapped sib (32 * sibs.length))
    (hap : Apart sib (32 * sibs.length) (s.getReg .x2 - 2464) 2464)
    (hc : Climb s sib idx leaf sibs u j) :
    ∃ v, Reaches Image.code u v ∧ (Dead Image.code v ∨ (DFrame u v (CW s) ∧
      v.getReg .x2 = s.getReg .x2 - 1040 ∧ (∀ r ∈ [Reg.x9, .x24, .x25, .x26], v.getReg r = u.getReg r) ∧
      ((j + 1 < sibs.length ∧ Climb s sib idx leaf sibs v (j + 1)) ∨
        (j + 1 = sibs.length ∧ v.pc = 0x8000ab04 ∧
          Contracts.bytesAt v (s.getReg .x2 - 160) 32 = Model.Pcs.climbBytes idx 0 leaf sibs)))) := by
  have hm := stack_mapped hpre
  have hR := hreg
  simp only [Mapped] at hR
  have hjn := hc.jlt
  have hsp := hc.sp
  have hj64 : j < 2 ^ 64 := by omega
  obtain ⟨t1, r1, h1⟩ := Sym.BlockSpec.reaches b8000af10_spec hc.pc (by
    rv_eval [hsp]; valid_access hpre.stack.valid [hm])
  have k1 := b8000af10_keeps h1
  have m1 := b8000af10_mem_same h1
  have sp1 : t1.getReg .x2 = s.getReg .x2 - 1040 := (k1 .x2 (by decide)).trans hsp
  have x18₁ : t1.getReg .x18 = sib + BitVec.ofNat 64 (32 * j) := (k1 .x18 (by decide)).trans hc.x18
  have hpc1 : t1.pc = if ((u.getMem (u.getReg .x2 + 256) >>> ((u.getReg .x21).toNat % 64) &&& 1 !=
      0) = true) then 0x8000abfc else 0x8000af20 := h1.pc_eq (by rv_eval []; try rfl)
  have e256 : u.getMem (u.getReg .x2 + 256) = idx := by
    rw [hsp, show s.getReg .x2 - 1040 + 256 = s.getReg .x2 - 784 by rv_eval []]; exact hc.index
  have ej : (u.getReg .x21).toNat % 64 = j % 64 := by
    rw [hc.x21, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hj64]
  rw [e256, ej] at hpc1
  have e1 : ∀ a n, Contracts.bytesAt t1 a n = Contracts.bytesAt u a n := fun a n ↦ by
    simp only [Contracts.bytesAt, MachineState.getByte, m1]
  have hsib : Contracts.bytesAt t1 (sib + BitVec.ofNat 64 (32 * j)) 32 = sibs[j] := by
    rw [e1]; exact hc.sibs j hjn
  have hnode : Contracts.bytesAt t1 (s.getReg .x2 - 160) 32 =
      Model.Pcs.climbBytes idx 0 leaf (sibs.take j) := by rw [e1]; exact hc.node
  have rod1 : RodataOk t1 := hc.rodata.dframe (DFrame.of_same m1 fun _ ↦ False) fun _ _ h ↦ h
  -- the buffer's first half, the sibling or the node
  obtain ⟨t2, r2, x10₂, x12₂, src₂, B1₂, B2₂, fr₂, hst, k2⟩ : ∃ t2, Reaches Image.code t1 t2 ∧
      t2.getReg .x10 = s.getReg .x2 - 352 ∧ t2.getReg .x12 = 32 ∧
      (t2.getReg .x11 = sib + BitVec.ofNat 64 (32 * j) ∨ t2.getReg .x11 = s.getReg .x2 - 160) ∧
      Contracts.bytesAt t2 (s.getReg .x2 - 384) 32 =
        (if (idx >>> (j % 64)) &&& 1#64 = 0#64 then Model.Pcs.climbBytes idx 0 leaf (sibs.take j)
          else sibs[j]) ∧
      Contracts.bytesAt t2 (t2.getReg .x11) 32 =
        (if (idx >>> (j % 64)) &&& 1#64 = 0#64 then sibs[j]
          else Model.Pcs.climbBytes idx 0 leaf (sibs.take j)) ∧
      DFrame t1 t2 (Within · (s.getReg .x2 - 384) 32) ∧ t2.pc = 0x8000ad78 ∧
      ∀ r ∈ [Reg.x2, .x9, .x18, .x21, .x24, .x25, .x26, .x27], t2.getReg r = t1.getReg r := by
    by_cases hbit : (idx >>> (j % 64)) &&& 1#64 = 0#64
    · have hp : t1.pc = 0x8000af20 := by
        rw [hpc1]
        exact ite_eq_right_of_eq_false _ _ (eq_false (by rw [show (idx >>> (j % 64) &&& 1) = 0 from hbit]; decide))
      obtain ⟨t2, r2, h2⟩ := Sym.BlockSpec.reaches b8000af20_spec hp (by
        rv_eval [sp1]
        and_intros <;> first
          | exact validAccess_one (by addr_omega [hm])
          | valid_access hpre.stack.valid [hm]
          | addr_omega [hm])
      have k2 := b8000af20_keeps h2
      have fr := DFrame.of_memFrame (b8000af20_frame h2 (by rw [sp1]; addr_omega [hm]))
      have hb := af20_bytes h2 (by rw [sp1]; addr_omega [hm]) (by rw [sp1]; addr_omega [hm])
      rw [sp1, show s.getReg .x2 - 1040 + 656 = s.getReg .x2 - 384 by rv_eval [],
        show s.getReg .x2 - 1040 + 880 = s.getReg .x2 - 160 by rv_eval []] at hb
      rw [sp1, show s.getReg .x2 - 1040 + 656 = s.getReg .x2 - 384 by rv_eval []] at fr
      have x11₂ : t2.getReg .x11 = sib + BitVec.ofNat 64 (32 * j) := by
        rw [b8000af20_x11 h2, x18₁]
      refine ⟨t2, r2, by rw [b8000af20_x10 h2, sp1]; rv_eval [], b8000af20_x12 h2, Or.inl x11₂,
        by rw [hb, hnode]; simp only [hbit, ↓reduceIte], ?_, fr, b8000af20_pc h2, fun r hr ↦ k2 r (by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
          rcases hr with h | h | h | h | h | h | h | h <;> simp [h])⟩
      simp only [hbit, ↓reduceIte]
      rw [x11₂, ← hsib]
      have hal := Sym.alignToDword_toNat (sib + BitVec.ofNat 64 (32 * j))
      exact DFrame.bytesU fr (by addr_omega [hR, hjn, hal])
        fun y hy hw ↦ by addr_omega [hy, hw, hap, hR, hjn, hm, hal]
    · have hp : t1.pc = 0x8000abfc := by
        rw [hpc1]
        exact ite_eq_left_of_eq_true _ _ (eq_true (bne_iff_ne.mpr hbit))
      obtain ⟨t2, r2, h2⟩ := Sym.BlockSpec.reaches abfcA_spec hp (abfcA_obl
        (by rw [x18₁]; simp only [Mapped]; addr_omega [hR, hjn])
        (by rw [x18₁, sp1]; addr_omega [hR, hjn, hap, hm])
        (by rw [sp1]; refine ⟨?_, ?_, ?_, ?_⟩ <;> valid_access hpre.stack.valid [hm])
        (by rw [sp1]; addr_omega [hm]))
      have k2 := abfcA_keeps h2
      have fr := DFrame.of_memFrame (abfcA_frame h2 (by rw [sp1]; addr_omega [hm]))
      have hb := abfcA_bytes h2 (by rw [sp1]; addr_omega [hm]) (by rw [sp1]; addr_omega [hm])
      rw [sp1, show s.getReg .x2 - 1040 + 656 = s.getReg .x2 - 384 by rv_eval [], x18₁] at hb
      rw [sp1, show s.getReg .x2 - 1040 + 656 = s.getReg .x2 - 384 by rv_eval []] at fr
      have x11₂ : t2.getReg .x11 = s.getReg .x2 - 160 := by
        rw [abfcA_x11 h2, sp1]; rv_eval []
      refine ⟨t2, r2, by rw [abfcA_x10 h2, sp1]; rv_eval [], abfcA_x12 h2, Or.inr x11₂,
        by rw [hb, hsib]; simp only [hbit, ↓reduceIte], ?_, fr, abfcA_pc h2, fun r hr ↦ k2 r (by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
          rcases hr with h | h | h | h | h | h | h | h <;> simp [h])⟩
      simp only [hbit, ↓reduceIte]
      rw [x11₂, ← hnode]
      exact DFrame.bytes32 fr (by addr_omega [hm]) (by addr_omega [hm])
        fun y hy hw ↦ by addr_omega [hy, hw, hm]
  have sp2 : t2.getReg .x2 = s.getReg .x2 - 1040 := (k2 .x2 (by simp)).trans sp1
  have rod2 : RodataOk t2 := rod1.dframe fr₂ fun a ha hw ↦ by
    have hro := hpre.stack.rodata
    rw [stackLo_vso, vso_stack] at hro
    addr_omega [ha, hw, hro, hm]
  obtain ⟨v, r3, hv⟩ := climb_tail hM hK hpre hreg hap hjn hst sp2 x10₂ x12₂
    (by rw [k2 .x18 (by simp), x18₁]) (by rw [k2 .x21 (by simp), k1 .x21 (by decide), hc.x21])
    (by rw [k2 .x27 (by simp), k1 .x27 (by decide), hc.x27]) src₂ B1₂ B2₂ rod2
  rcases hv with hd | ⟨fr3, sp3, k3, x18₃, x21₃, x27₃, node₃, hpc₃⟩
  · exact ⟨v, r1.trans (r2.trans r3), Or.inl hd⟩
  have fr : DFrame u v (CW s) := ((DFrame.of_same m1 (CW s)).trans (fr₂.mono fun a ha ↦
    Or.inr (Or.inr (Or.inl (by addr_omega [ha, hm])))) fun _ h ↦ h).trans fr3 fun _ h ↦ h
  have hstep : Model.Pcs.climbBytes idx 0 leaf (sibs.take (j + 1)) =
      Model.keccakHashRust ((if (idx >>> (j % 64)) &&& 1#64 = 0#64 then
          Model.Pcs.climbBytes idx 0 leaf (sibs.take j) else sibs[j]) ++
        (if (idx >>> (j % 64)) &&& 1#64 = 0#64 then sibs[j]
          else Model.Pcs.climbBytes idx 0 leaf (sibs.take j))) := by
    rw [climbBytes_take hjn, Model.Pcs.climbStep]
    split <;> rfl
  rw [← hstep] at node₃
  have kr : ∀ r ∈ [Reg.x9, .x24, .x25, .x26], v.getReg r = u.getReg r := by
    intro r hr
    have hr' : r = .x9 ∨ r = .x24 ∨ r = .x25 ∨ r = .x26 := by simpa using hr
    rw [k3 r hr, k2 r (by rcases hr' with rfl | rfl | rfl | rfl <;> simp),
      k1 r (by rcases hr' with rfl | rfl | rfl | rfl <;> decide)]
  refine ⟨v, r1.trans (r2.trans r3), Or.inr ⟨fr, sp3, kr, ?_⟩⟩
  rcases hpc₃ with ⟨hlt, hp⟩ | ⟨he, hp⟩
  · refine Or.inl ⟨hlt, {
      pc := hp
      sp := sp3
      x18 := x18₃
      x21 := x21₃
      x27 := x27₃
      jlt := hlt
      index := by
        rw [fr _ fun i hi hw ↦ by
          rcases hw with hw | hw | hw | hw <;> addr_omega [hi, hw, hm]]
        exact hc.index
      node := node₃
      sibs := fun i hi ↦ by
        have hal := Sym.alignToDword_toNat (sib + BitVec.ofNat 64 (32 * i))
        rw [DFrame.bytesU fr (by addr_omega [hR, hi, hal])
          fun y hy hw ↦ by
            rcases hw with hw | hw | hw | hw <;> addr_omega [hy, hw, hap, hR, hi, hm, hal]]
        exact hc.sibs i hi
      rodata := hc.rodata.dframe fr fun a ha hw ↦ by
        have hro := hpre.stack.rodata
        rw [stackLo_vso, vso_stack] at hro
        rcases hw with hw | hw | hw | hw <;> addr_omega [ha, hw, hro, hm] }⟩
  · refine Or.inr ⟨he, hp, ?_⟩
    rw [node₃, he, List.take_length]

/-- After the climb, at `0x8000ab04`: the node is the path's root. -/
structure Climbed (s u v : MachineState) (idx : Word) (leaf : List (BitVec 8))
    (sibs : List (List (BitVec 8))) : Prop where
  fr : DFrame u v (CW s)
  sp : v.getReg .x2 = s.getReg .x2 - 1040
  regs : ∀ r ∈ [Reg.x9, .x24, .x25, .x26], v.getReg r = u.getReg r
  pc : v.pc = 0x8000ab04
  node : Contracts.bytesAt v (s.getReg .x2 - 160) 32 = Model.Pcs.climbBytes idx 0 leaf sibs

/-- **The climb**, from level `j` on. -/
theorem climb_loop (hM : Runtime.MemcpySpec 0x800126e4) (hK : KeccakHashSpec) {s : MachineState}
    {sib idx : Word} {leaf : List (BitVec 8)} {sibs : List (List (BitVec 8))} (hpre : VsoPre s)
    (hreg : Mapped sib (32 * sibs.length))
    (hap : Apart sib (32 * sibs.length) (s.getReg .x2 - 2464) 2464) :
    ∀ (k j : ℕ) (u : MachineState), sibs.length - j = k → Climb s sib idx leaf sibs u j →
      ∃ v, Reaches Image.code u v ∧ (Dead Image.code v ∨ Climbed s u v idx leaf sibs)
  | 0, j, _, hk, hc => absurd hc.jlt (by omega)
  | k + 1, j, u, hk, hc => by
    obtain ⟨t, r, ht⟩ := climb_step hM hK hpre hreg hap hc
    rcases ht with hd | ⟨fr, sp, kr, ⟨-, hn⟩ | ⟨-, pc, node⟩⟩
    · exact ⟨t, r, Or.inl hd⟩
    · obtain ⟨v, r', hv⟩ := climb_loop hM hK hpre hreg hap k (j + 1) t (by omega) hn
      rcases hv with hd | hv
      · exact ⟨v, r.trans r', Or.inl hd⟩
      · exact ⟨v, r.trans r', Or.inr ⟨fr.trans hv.fr fun _ h ↦ h, hv.sp,
          fun q hq ↦ (hv.regs q hq).trans (kr q hq), hv.pc, hv.node⟩⟩
    · exact ⟨t, r, Or.inr ⟨fr, sp, kr, pc, node⟩⟩

end Rv64Verifier.Proofs.Pcs.Vso
