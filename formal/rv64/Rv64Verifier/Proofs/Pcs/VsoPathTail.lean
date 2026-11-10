import Rv64Verifier.Proofs.Pcs.VsoPathCmp

/-!
# `verify_stacked_opening`'s Merkle checks: a path

`0x8000abcc` reads the siblings' count: none goes to the comparison at `0x8000b0a0`; otherwise
`0x8000abd4` puts the leaf index at `S - 784` and starts the climb (`Climb` at level `0`), after which
the comparison at `0x8000ab04`. `path_step` is a whole path, from `0x8000ab38` to the next one's
`0x8000ab2c` with the path's root checked (`PathRoot`), or to the `Err` at `0x8000b8d4`.
-/

namespace Rv64Verifier.Proofs.Pcs.Vso
open RiscvZkvm.Rv64 LeanVM.Parameters Rv64Verifier.Contracts Rv64Verifier.Runtime
  Rv64Verifier.Transcript Rv64Verifier.Pcs Rv64Verifier.PcsContracts Rv64Verifier.Blocks.F38
open Rv64Verifier.Sym (reduceReg reducePc reduceMem reduceWrites reduceObl)

/-- The root the paths climb to: its pointer at `S - 840`, its bytes safe. -/
structure RootOk (s u0 : MachineState) (R : Word) : Prop where
  slot : u0.getMem (s.getReg .x2 - 840) = R
  region : Region R 32
  safe : Safe s (heapNext u0) R 32

/-- Path `p`'s root is the root at `R`, as `merkleRust` checks it. -/
def PathRoot (u0 : MachineState) (p R : Word) : Prop :=
  Model.Pcs.pathRootBytes (BitVec.ofNat 64 (openingAt u0 p).leafIndex) (openingAt u0 p).leaf
    ((openingAt u0 p).path.map Model.Pcs.digestBits) = Model.Pcs.digestBits (digestAt u0 R)

/-- The siblings' bytes. -/
def sibsAt (u0 : MachineState) (p : Word) : List (List (BitVec 8)) :=
  (List.range (vecLen u0 (p + 24)).toNat).map fun i ↦
    Contracts.bytesAt u0 (vecPtr u0 (p + 24) + BitVec.ofNat 64 (32 * i)) 32

theorem pathRoot_of {s u0 : MachineState} {p R : Word} (hp : PathOk s u0 p) (hR : RootOk s u0 R)
    (h : Model.Pcs.climbBytes (u0.getMem (p + 48)) 0
      (Model.keccakHashRust (Contracts.bytesAt u0 (vecPtr u0 p) (8 * (vecLen u0 p).toNat)))
      (sibsAt u0 p) = Contracts.bytesAt u0 R 32) : PathRoot u0 p R := by
  have hL := Region.bounds hp.leaf
  have hRb := Region.bounds hR.region
  unfold PathRoot Model.Pcs.pathRootBytes
  rw [digestBits_at u0 hRb.2.2 (by omega), ← h]
  simp only [openingAt, BitVec.ofNat_toNat, BitVec.setWidth_eq, vecWords]
  rw [leaf_bytes u0 hL.2.2 _ (by omega)]
  congr 1
  simp only [sibsAt, List.map_map]
  apply List.map_congr_left
  intro i _
  exact digestBits_bytes u0 _

theorem sibCount {m : Word} (h0 : m ≠ 0) (hb : 32 * m.toNat < 2 ^ 64) :
    ((m * 32 - 32) >>> 5) + 1 = m := by
  apply BitVec.eq_of_toNat_eq
  have hm : 1 ≤ m.toNat := by
    rcases Nat.eq_zero_or_pos m.toNat with h | h
    · exact absurd (BitVec.eq_of_toNat_eq (by rw [h]; rfl)) h0
    · exact h
  simp only [BitVec.toNat_add, BitVec.toNat_ushiftRight, BitVec.toNat_sub, BitVec.toNat_mul,
    show (32 : Word).toNat = 32 from rfl, show (1 : Word).toNat = 1 from rfl,
    Nat.shiftRight_eq_div_pow]
  omega

/-- After a path: what it wrote, at `0x8000ab2c` with its root checked, or at the `Err`. -/
structure PathOut (s u0 : MachineState) (p E R : Word) (u v : MachineState) : Prop where
  sp : v.getReg .x2 = s.getReg .x2 - 1040
  fr : DFrame u v (PW s (heapNext u) (heapNext v))
  heap : HeapOk v
  mono : heapNext u ≤ heapNext v
  next : v.pc = 0x8000b8d4 ∨ (v.pc = 0x8000ab2c ∧ v.getReg .x22 = p ∧ v.getReg .x25 = E ∧
    (∀ r ∈ [Reg.x9, .x26], v.getReg r = u.getReg r) ∧ PathRoot u0 p R)

theorem pathTail (hM : Runtime.MemcpySpec 0x800126e4) (hK : KeccakHashSpec) (hC : MemcmpSpec)
    {s u0 u v : MachineState} {p E R : Word} (hpre : VsoPre s) (hp : PathOk s u0 p)
    (hR : RootOk s u0 R) (hin : PathIn s u0 p E u) (hh : Hashed s u0 p E u v) :
    ∃ w, Reaches Image.code v w ∧ (Dead Image.code w ∨ PathOut s u0 p E R u w) := by
  have hm := stack_mapped hpre
  have hb := bounds hpre
  have hP := Region.bounds hp.hdr
  have hRb := Region.bounds hR.region
  have hvhi := hh.heap.hi
  have hnx := hpre.stack.next
  rw [stackLo_vso, vso_stack] at hnx
  have fr0 : DFrame u0 v (PW s (heapNext u0) (heapNext v)) :=
    (hin.fr.mono fun a h ↦ h.mono (Nat.le_refl _) hh.mono).trans hh.fr
      fun a h ↦ h.mono hin.mono (Nat.le_refl _)
  have hw (x : Word) (h1 : p.toNat ≤ x.toNat) (h2 : x.toNat + 8 ≤ p.toNat + 56) :
      v.getMem x = u0.getMem x :=
    fr0 x fun i hi hw ↦ hp.hdrSafe.misses hpre hvhi _ (by addr_omega [h1, h2, hi, hP]) hw
  have hslot : v.getMem (s.getReg .x2 - 840) = R := by
    rw [fr0 _ fun i hi hw ↦ by
      rcases hw with (hw | hw | hw | hw) | hw | hw | ⟨hw1, hw2⟩
      all_goals first
        | addr_omega [hw, hi, hm]
        | addr_omega [hw, hi, hm, hnx]
        | addr_omega [hw2, hi, hm, hvhi]]
    exact hR.slot
  have hrod : RodataOk v := hin.rodata.dframe hh.fr (PW.rodata hpre hvhi)
  have hRv : Contracts.bytesAt v R 32 = Contracts.bytesAt u0 R 32 :=
    DFrame.bytes32 fr0 hRb.2.2 (by omega) (hR.safe.misses hpre hvhi)
  have hsp := hh.sp
  -- the siblings' count
  obtain ⟨t1, r1, h1⟩ := Sym.BlockSpec.reaches b8000abcc_spec hh.pc (by
    rv_eval [hh.x22]
    exact Region.valid hp.hdr (by addr_omega [hP]) (by addr_omega [hP]) (by addr_omega [hP]))
  have k1 := b8000abcc_keeps h1
  have m1 := b8000abcc_mem_same h1
  have e40 : v.getMem (p + 40) = vecLen u0 (p + 24) := by
    rw [hw _ (by addr_omega [hP]) (by addr_omega [hP])]; simp only [vecLen]; rv_eval []
  have e1 : ∀ a n, Contracts.bytesAt t1 a n = Contracts.bytesAt v a n := fun a n ↦ by
    simp only [Contracts.bytesAt, MachineState.getByte, m1]
  rcases eq_or_ne (vecLen u0 (p + 24)) 0 with hm0 | hm0
  · -- no siblings
    obtain ⟨t2, r2, hv2⟩ := cmpB hC hpre (R := R)
      (b8000abcc_pc_taken h1 (by rw [hh.x22, e40, hm0])) (by rw [k1 .x2 (by decide), hsp])
      (by rw [m1]; exact hslot) hR.region
    rcases hv2 with hd | ⟨m2, sp2, k2, x22₂, hnext⟩
    · exact ⟨t2, r1.trans r2, Or.inl hd⟩
    have hn2 : heapNext t2 = heapNext v := by simp only [heapNext, m2, m1]
    refine ⟨t2, r1.trans r2, Or.inr {
      sp := by rw [sp2, k1 .x2 (by decide), hsp]
      fr := by
        rw [hn2]
        exact hh.fr.trans (DFrame.of_same (fun a ↦ by rw [m2, m1]) _) fun _ h ↦ h
      heap := ⟨by rw [hn2]; exact hh.heap.lo, by rw [hn2]; exact hh.heap.hi⟩
      mono := by rw [hn2]; exact hh.mono
      next := ?_ }⟩
    rcases hnext with h | ⟨hpc, heq⟩
    · exact Or.inl h
    refine Or.inr ⟨hpc, by rw [x22₂, k1 .x22 (by decide), hh.x22],
      by rw [k2 .x25 (by simp), k1 .x25 (by decide), hh.x25], fun r hr ↦ ?_, ?_⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · rw [k2 .x9 (by simp), k1 .x9 (by decide), hh.regs .x9 (by simp)]
      · rw [k2 .x26 (by simp), k1 .x26 (by decide), hh.regs .x26 (by simp)]
    · refine pathRoot_of hp hR ?_
      rw [← hRv, ← e1, ← heq, e1, hh.node]
      simp only [sibsAt, hm0, show (0 : Word).toNat = 0 from rfl, List.range_zero, List.map_nil,
        Model.Pcs.climbBytes]
  -- the climb
  rcases hp.sibs with hz | ⟨hS, hSs⟩
  · exact absurd (BitVec.eq_of_toNat_eq (by rw [hz]; rfl)) hm0
  have hSb := Region.bounds hS
  have hal0 := Sym.alignToDword_toNat (vecPtr u0 (p + 24))
  obtain ⟨t2, r2, h2⟩ := Sym.BlockSpec.reaches b8000abd4_spec
    (b8000abcc_pc_not_taken h1 (by rw [hh.x22, e40]; exact hm0)) (by
      rv_eval [k1 .x2 (by decide), k1 .x22 (by decide), hsp, hh.x22]
      and_intros
      · valid_access hpre.stack.valid [hb]
      · exact Region.valid hp.hdr (by addr_omega [hP]) (by addr_omega [hP]) (by addr_omega [hP])
      · exact Region.valid hp.hdr (by addr_omega [hP]) (by addr_omega [hP]) (by addr_omega [hP]))
  have k2 := b8000abd4_keeps h2
  have sp1 : t1.getReg .x2 = s.getReg .x2 - 1040 := by rw [k1 .x2 (by decide), hsp]
  have x22₁ : t1.getReg .x22 = p := by rw [k1 .x22 (by decide), hh.x22]
  have fr2 : DFrame t1 t2 (Within · (s.getReg .x2 - 784) 8) := by
    have := DFrame.of_memFrame (b8000abd4_frame h2 (by rw [sp1]; addr_omega [hb]))
    rw [sp1, show s.getReg .x2 - 1040 + 256 = s.getReg .x2 - 784 by rv_eval []] at this
    exact this
  have frv2 : DFrame v t2 (PW s (heapNext v) (heapNext v)) :=
    (DFrame.of_same m1 _).trans fr2 fun a ha ↦ Or.inr (Or.inl ha)
  have fr02 : DFrame u0 t2 (PW s (heapNext u0) (heapNext v)) := fr0.trans frv2 fun a h ↦
    h.mono (hin.mono.trans hh.mono) (Nat.le_refl _)
  have hmN : (vecLen u0 (p + 24)).toNat ≠ 0 := fun h ↦ hm0 (BitVec.eq_of_toNat_eq (by rw [h]; rfl))
  have hlen : (sibsAt u0 p).length = (vecLen u0 (p + 24)).toNat := by simp [sibsAt]
  have e32 : t1.getMem (p + 32) = vecPtr u0 (p + 24) := by
    rw [m1, hw _ (by addr_omega [hP]) (by addr_omega [hP])]; simp only [vecPtr]; rv_eval []
  have e48 : t1.getMem (p + 48) = u0.getMem (p + 48) := by
    rw [m1, hw _ (by addr_omega [hP]) (by addr_omega [hP])]
  have hc : Climb s (vecPtr u0 (p + 24)) (u0.getMem (p + 48))
      (Model.keccakHashRust (Contracts.bytesAt u0 (vecPtr u0 p) (8 * (vecLen u0 p).toNat)))
      (sibsAt u0 p) t2 0 := {
    pc := b8000abd4_pc h2
    sp := by rw [k2 .x2 (by decide), sp1]
    x18 := by rw [b8000abd4_x18 h2, x22₁, e32]; simp
    x21 := b8000abd4_x21 h2
    x27 := by
      rw [b8000abd4_x27 h2, b8000abcc_x10 h1, hh.x22, e40, hlen, BitVec.ofNat_toNat,
        BitVec.setWidth_eq]
      exact sibCount hm0 (by have := mapped_of_wide hmN hS; simp only [Mapped] at this; omega)
    jlt := by rw [hlen]; omega
    index := by
      have := b8000abd4_m_x2_256 h2
      rw [sp1, x22₁, e48, show s.getReg .x2 - 1040 + 256 = s.getReg .x2 - 784 by rv_eval []] at this
      exact this
    node := by
      rw [List.take_zero, Model.Pcs.climbBytes, DFrame.bytes32 fr2 (by addr_omega [hm])
        (by addr_omega [hm]) fun y hy hw' ↦ by addr_omega [hy, hw', hm], e1, hh.node]
    sibs := fun i hi ↦ by
      rw [hlen] at hi
      have hal := Sym.alignToDword_toNat (vecPtr u0 (p + 24) + BitVec.ofNat 64 (32 * i))
      rw [DFrame.bytesU fr02 (by addr_omega [hSb, hi, hal, hal0])
        fun y hy ↦ hSs.misses hpre hvhi y (by addr_omega [hy, hSb, hi, hal, hal0])]
      simp [sibsAt]
    rodata := hrod.dframe frv2 (PW.rodata hpre hvhi) }
  obtain ⟨t3, r3, hv3⟩ := climb_loop hM hK hpre (by rw [hlen]; exact mapped_of_wide hmN hS)
    (by rw [hlen]; exact apart_of_wide hSs.2.1)
    _ 0 t2 rfl hc
  rcases hv3 with hd | hcl
  · exact ⟨t3, r1.trans (r2.trans r3), Or.inl hd⟩
  have fr03 : DFrame u0 t3 (PW s (heapNext u0) (heapNext v)) := fr02.trans hcl.fr fun a h ↦ Or.inl h
  obtain ⟨t4, r4, hv4⟩ := cmpA hC hpre (R := R) hcl.pc hcl.sp (by
    rw [fr03 _ fun i hi hw' ↦ by
      rcases hw' with (hw' | hw' | hw' | hw') | hw' | hw' | ⟨hw1, hw2⟩
      all_goals first
        | addr_omega [hw', hi, hm, hnx]
        | addr_omega [hw2, hi, hm, hvhi]]
    exact hR.slot) hR.region
  rcases hv4 with hd | ⟨m4, sp4, k4, x22₄, hnext⟩
  · exact ⟨t4, r1.trans (r2.trans (r3.trans r4)), Or.inl hd⟩
  have nx3 : t3.getMem nextAddr = t2.getMem nextAddr := hcl.fr _ fun i hi hw' ↦ by
    rcases hw' with hw' | hw' | hw' | hw' <;> addr_omega [hw', hi, hm, hnx]
  have nx2 : t2.getMem nextAddr = t1.getMem nextAddr := fr2 _ fun i hi hw' ↦ by
    addr_omega [hw', hi, hm, hnx]
  have hn4 : heapNext t4 = heapNext v := by simp only [heapNext, m4, nx3, nx2, m1]
  have kr (r : Reg) (hr : r ∈ [Reg.x9, .x25, .x26]) : t4.getReg r = v.getReg r := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;>
      rw [k4 _ (by simp), hcl.regs _ (by simp), k2 _ (by decide), k1 _ (by decide)]
  refine ⟨t4, r1.trans (r2.trans (r3.trans r4)), Or.inr {
    sp := by rw [sp4, hcl.sp]
    fr := by
      rw [hn4]
      have d : DFrame v t4 (PW s (heapNext v) (heapNext v)) :=
        (frv2.trans hcl.fr fun a h ↦ Or.inl h).trans (DFrame.of_same m4 _) fun _ h ↦ h
      exact hh.fr.trans d fun a h ↦ h.mono hh.mono (Nat.le_refl _)
    heap := ⟨by rw [hn4]; exact hh.heap.lo, by rw [hn4]; exact hh.heap.hi⟩
    mono := by rw [hn4]; exact hh.mono
    next := ?_ }⟩
  rcases hnext with h | ⟨hpc, heq⟩
  · exact Or.inl h
  refine Or.inr ⟨hpc, by rw [x22₄, hcl.regs .x24 (by simp), b8000abd4_x24 h2, x22₁],
    by rw [kr .x25 (by simp), hh.x25], fun r hr ↦ ?_, ?_⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · rw [kr .x9 (by simp), hh.regs .x9 (by simp)]
    · rw [kr .x26 (by simp), hh.regs .x26 (by simp)]
  · refine pathRoot_of hp hR ?_
    rw [← hcl.node, heq, DFrame.bytes32 fr03 hRb.2.2 (by omega) (hR.safe.misses hpre hvhi)]

end Rv64Verifier.Proofs.Pcs.Vso
