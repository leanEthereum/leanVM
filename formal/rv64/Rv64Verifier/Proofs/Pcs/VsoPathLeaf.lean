import Rv64Verifier.Proofs.Pcs.VsoPathCalls

/-!
# `verify_stacked_opening`'s Merkle checks: a path's leaf hashed

At `0x8000ab38` the path loop is at the `MerklePath` `p` (`s6`), `E` past the phase's last (`t0`).
`0x8000ab38` calls `try_allocate_in(S - 384, 8 n, 0, 1, 1)` for the leaf's `n` words, `0x8000ab64`
traps on `Err`, `0x8000ab70` makes the empty `Vec<u8>` and calls `reserve`, which has room
(`LeafAlloc`); `0x8000ab94` and `0x8000aba0` copy the words in with `memcpy`, `0x8000abb8` hashes them
into the node at `S - 160` (`Hashed`, at `0x8000abcc`).

The path's header and buffers are those of the Merkle block's state `u0` (`PathOk`), which the
path loop does not write (`Safe`); `PathIn` carries the frame from `u0`.
-/

namespace Rv64Verifier.Proofs.Pcs.Vso
open RiscvZkvm.Rv64 LeanVM.Parameters Rv64Verifier.Contracts Rv64Verifier.Runtime
  Rv64Verifier.Transcript Rv64Verifier.Pcs Rv64Verifier.PcsContracts Rv64Verifier.Blocks.F38
open Rv64Verifier.Sym (reduceReg reducePc reduceMem reduceWrites reduceObl)

/-- Path `p` at the Merkle block's state `u0`: its header and buffers mapped, aligned and safe, its
leaf not empty. -/
structure PathOk (s u0 : MachineState) (p : Word) : Prop where
  hdr : Region p 56
  hdrSafe : Safe s (heapNext u0) p 56
  leafNe : (vecLen u0 p).toNat ≠ 0
  leaf : Region (vecPtr u0 p) (8 * (vecLen u0 p).toNat)
  leafSafe : Safe s (heapNext u0) (vecPtr u0 p) (8 * (vecLen u0 p).toNat)
  sibs : (vecLen u0 (p + 24)).toNat = 0 ∨
    Region (vecPtr u0 (p + 24)) (32 * (vecLen u0 (p + 24)).toNat) ∧
      Safe s (heapNext u0) (vecPtr u0 (p + 24)) (32 * (vecLen u0 (p + 24)).toNat)

/-- At `0x8000ab38`, before path `p`, what the loop wrote since `u0`. -/
structure PathIn (s u0 : MachineState) (p E : Word) (u : MachineState) : Prop where
  pc : u.pc = 0x8000ab38
  sp : u.getReg .x2 = s.getReg .x2 - 1040
  x22 : u.getReg .x22 = p
  x5 : u.getReg .x5 = E
  fr : DFrame u0 u (PW s (heapNext u0) (heapNext u))
  heap : HeapOk u
  mono : heapNext u0 ≤ heapNext u
  rodata : RodataOk u

/-- A doubleword of the header is `u0`'s. -/
theorem PathIn.hdrWord {s u0 u : MachineState} {p E : Word} (hpre : VsoPre s)
    (h : PathIn s u0 p E u) (hp : PathOk s u0 p) {x : Word} (h1 : p.toNat ≤ x.toNat)
    (h2 : x.toNat + 8 ≤ p.toNat + 56) : u.getMem x = u0.getMem x := by
  have hP := Region.bounds hp.hdr
  exact h.fr x fun i hi hw ↦ hp.hdrSafe.misses hpre h.heap.hi _ (by addr_omega [h1, h2, hi, hP]) hw

theorem len8 {s u0 : MachineState} {p : Word} (hp : PathOk s u0 p) :
    (vecLen u0 p * 8).toNat = 8 * (vecLen u0 p).toNat := by
  have hL := Region.bounds hp.leaf
  rw [BitVec.toNat_mul, show (8 : Word).toNat = 8 from rfl, Nat.mod_eq_of_lt (by omega),
    Nat.mul_comm]

/-- At `0x8000ab94`: the empty `Vec<u8>` at `S - 384` with its buffer `B` for the leaf's bytes. -/
structure LeafAlloc (s u0 : MachineState) (p E : Word) (u w : MachineState) (B : Word) : Prop where
  pc : w.pc = 0x8000ab94
  sp : w.getReg .x2 = s.getReg .x2 - 1040
  x8 : w.getReg .x8 = vecLen u0 p
  x18 : w.getReg .x18 = vecPtr u0 p
  x21 : w.getReg .x21 = vecLen u0 p * 8
  x22 : w.getReg .x22 = p
  x25 : w.getReg .x25 = E
  regs : ∀ r ∈ [Reg.x9, .x26], w.getReg r = u.getReg r
  ptr : w.getMem (s.getReg .x2 - 376) = B
  len : w.getMem (s.getReg .x2 - 368) = 0
  buf : heapNext u ≤ B.toNat ∧ B.toNat + 8 * (vecLen u0 p).toNat ≤ heapNext w
  fr : DFrame u w (PW s (heapNext u) (heapNext w))
  heap : HeapOk w
  mono : heapNext u ≤ heapNext w

theorem allocLeaf (hT : TryAllocZeroedSpec) (hRF : ReserveFastSpec 0x8000c898)
    {s u0 u : MachineState} {p E : Word} (hpre : VsoPre s) (hp : PathOk s u0 p)
    (hin : PathIn s u0 p E u) :
    ∃ w, Reaches Image.code u w ∧ (Dead Image.code w ∨ ∃ B, LeafAlloc s u0 p E u w B) := by
  have hm := stack_mapped hpre
  have hb := bounds hpre
  have hP := Region.bounds hp.hdr
  have hsp := hin.sp
  have hnx := hpre.stack.next
  rw [stackLo_vso, vso_stack] at hnx
  have e8 : u.getMem (p + 8) = vecPtr u0 p :=
    hin.hdrWord hpre hp (by addr_omega [hP]) (by addr_omega [hP])
  have e16 : u.getMem (p + 16) = vecLen u0 p :=
    hin.hdrWord hpre hp (by addr_omega [hP]) (by addr_omega [hP])
  -- `try_allocate_in`
  obtain ⟨t1, r1, h1⟩ := Sym.BlockSpec.reaches b8000ab38_spec hin.pc (by
    rv_eval [hin.x22]
    and_intros <;> exact Region.valid hp.hdr (by addr_omega [hP]) (by addr_omega [hP])
      (by addr_omega [hP]))
  have k1 := b8000ab38_keeps h1
  have m1 := b8000ab38_mem_same h1
  have sp1 : t1.getReg .x2 = s.getReg .x2 - 1040 := (k1 .x2 (by decide)).trans hsp
  have x11₁ : t1.getReg .x11 = vecLen u0 p * 8 := by rw [b8000ab38_x11 h1, hin.x22, e16]
  have hn1 : heapNext t1 = heapNext u := by simp only [heapNext, m1]
  obtain ⟨t2, r2, hv2⟩ := callTryAlloc hT hpre (b8000ab38_pc h1) sp1
    (by rw [b8000ab38_x10 h1, hsp]; rv_eval []) (b8000ab38_x13 h1) (b8000ab38_x14 h1)
    ⟨hn1 ▸ hin.heap.lo, hn1 ▸ hin.heap.hi⟩
  rcases hv2 with hd | ⟨pc2, pr2, heap2, mono2, ok2, fr2⟩
  · exact ⟨t2, r1.trans r2, Or.inl hd⟩
  have sp2 : t2.getReg .x2 = s.getReg .x2 - 1040 := (pr2.reg .x2).trans sp1
  -- the tag
  obtain ⟨t3, r3, h3⟩ := Sym.BlockSpec.reaches b8000ab64_spec
    (by rw [pc2, returnAddress_eq, b8000ab38_x1 h1]; rfl) (by
      rv_eval [sp2]; valid_access hpre.stack.valid [hb])
  rcases eq_or_ne (t2.getMem (s.getReg .x2 - 384)) 0 with htag | htag
  swap
  · obtain ⟨t4, r4, h4⟩ := Sym.BlockSpec.reaches b8000ab6c_spec
      (b8000ab64_pc_not_taken h3 (by rv_eval [sp2]; exact htag)) trivial
    exact ⟨t4, r1.trans (r2.trans (r3.trans r4)),
      Or.inl (dead_of_fetch (by rw [b8000ab6c_pc h4]; exact trap))⟩
  obtain ⟨hcap, hbuf⟩ := ok2 htag
  rw [x11₁, len8 hp] at hbuf
  rw [x11₁] at hcap
  have k3 := b8000ab64_keeps h3
  have m3 := b8000ab64_mem_same h3
  have sp3 : t3.getReg .x2 = s.getReg .x2 - 1040 := (k3 .x2 (by decide)).trans sp2
  -- the `Vec`, and `reserve` with room
  obtain ⟨t4, r4, h4⟩ := Sym.BlockSpec.reaches b8000ab70_spec
    (b8000ab64_pc_taken h3 (by rv_eval [sp2]; exact htag)) (by
      rv_eval [sp3]; and_intros <;> valid_access hpre.stack.valid [hb])
  have k4 := b8000ab70_keeps h4
  have fr4 := DFrame.of_memFrame (b8000ab70_frame h4 (by rw [sp3]; addr_omega [hb]))
  rw [sp3, show s.getReg .x2 - 1040 + 656 = s.getReg .x2 - 384 by rv_eval []] at fr4
  have v0 := b8000ab70_m_x2_656 h4
  have v1 := b8000ab70_m_x2_664 h4
  have v2 := b8000ab70_m_x2_672 h4
  rw [sp3] at v0 v1 v2
  rv_eval [m3] at v0 v1 v2
  have x21₃ : t3.getReg .x21 = vecLen u0 p * 8 := by
    rw [k3 .x21 (by decide), pr2.reg .x21, b8000ab38_x21 h1, hin.x22, e16]
  have x10₄ : t4.getReg .x10 = s.getReg .x2 - 384 := by rw [b8000ab70_x10 h4, sp3]; rv_eval []
  obtain ⟨t5, r5, ⟨pc5, pr5, -, m5⟩ | hd⟩ := hRF.call (Reaches.refl t4) (b8000ab70_pc h4)
    ⟨by rw [x10₄]; valid_sub hpre.stack.valid [hb], by
      rw [x10₄, b8000ab70_x11 h4, x21₃]
      simp only [vecLen, vecCap]
      rw [show s.getReg .x2 - 384 + 16 = s.getReg .x2 - 368 by rv_eval [], v2, v0, hcap]
      exact Nat.le_of_eq (by rw [show (0 : Word).toNat = 0 from rfl, Nat.zero_add]; rfl)⟩
  swap
  · exact ⟨t5, r1.trans (r2.trans (r3.trans (r4.trans r5))), Or.inl hd⟩
  -- `NEXT` and the frame
  have nx4 : t4.getMem nextAddr = t3.getMem nextAddr :=
    fr4 _ fun i hi hw ↦ by addr_omega [hw, hi, hb, hnx]
  have hn5 : heapNext t5 = heapNext t2 := by simp only [heapNext, m5, nx4, m3]
  have hnB := len8 hp
  have hL := Region.bounds hp.leaf
  have fr : DFrame u t5 (PW s (heapNext u) (heapNext t5)) := by
    have d2 : DFrame u t2 (PW s (heapNext u) (heapNext t5)) :=
      (DFrame.of_same m1 _).trans fr2 fun a ha ↦ by
        rcases ha with ha | ha | ha | ha
        · exact PW.of_cw (Or.inr (Or.inr (Or.inl (by addr_omega [ha, hm]))))
        · exact PW.of_stack (by addr_omega [ha, hm])
        · exact PW.of_next ha
        · simp only [Fresh] at ha
          exact PW.of_heap (by rw [← hn1]; exact ha.1) (by rw [hn5]; exact ha.2)
    have d4 : DFrame u t4 (PW s (heapNext u) (heapNext t5)) :=
      (d2.trans (DFrame.of_same m3 _) fun _ h ↦ h).trans fr4 fun a ha ↦
        PW.of_cw (Or.inr (Or.inr (Or.inl (by addr_omega [ha, hm]))))
    exact d4.trans (DFrame.of_same m5 _) fun _ h ↦ h
  have kk (r : Reg) (hr : r ∈ [Reg.x8, .x9, .x18, .x21, .x22, .x25, .x26]) :
      t5.getReg r = t1.getReg r := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      rw [pr5.reg _, k4 _ (by decide), k3 _ (by decide), pr2.reg _]
  refine ⟨t5, r1.trans (r2.trans (r3.trans (r4.trans r5))), Or.inr ⟨t2.getMem (s.getReg .x2 - 368), {
    pc := by rw [pc5, returnAddress_eq, b8000ab70_x1 h4]; rfl
    sp := by rw [pr5.reg .x2, k4 .x2 (by decide), sp3]
    x8 := by rw [kk .x8 (by simp), b8000ab38_x8 h1, hin.x22, e16]
    x18 := by rw [kk .x18 (by simp), b8000ab38_x18 h1, hin.x22, e8]
    x21 := by rw [kk .x21 (by simp), b8000ab38_x21 h1, hin.x22, e16]
    x22 := by rw [kk .x22 (by simp), k1 .x22 (by decide), hin.x22]
    x25 := by rw [kk .x25 (by simp), b8000ab38_x25 h1, hin.x5]
    regs := fun r hr ↦ by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · rw [kk .x9 (by simp), k1 .x9 (by decide)]
      · rw [kk .x26 (by simp), k1 .x26 (by decide)]
    ptr := by rw [m5, v1]
    len := by rw [m5, v2]
    buf := by
      rcases hbuf.2 with h0 | h0
      · exact absurd (by omega) hp.leafNe
      · exact ⟨by rw [← hn1]; exact h0.1, by rw [hn5]; exact h0.2⟩
    fr := fr
    heap := ⟨by rw [hn5]; exact heap2.lo, by rw [hn5]; exact heap2.hi⟩
    mono := by rw [hn5, ← hn1]; exact mono2 }⟩⟩

/-- At `0x8000abcc`: the leaf hashed into the node at `S - 160`. -/
structure Hashed (s u0 : MachineState) (p E : Word) (u v : MachineState) : Prop where
  pc : v.pc = 0x8000abcc
  sp : v.getReg .x2 = s.getReg .x2 - 1040
  x22 : v.getReg .x22 = p
  x25 : v.getReg .x25 = E
  regs : ∀ r ∈ [Reg.x9, .x26], v.getReg r = u.getReg r
  fr : DFrame u v (PW s (heapNext u) (heapNext v))
  heap : HeapOk v
  mono : heapNext u ≤ heapNext v
  node : Contracts.bytesAt v (s.getReg .x2 - 160) 32 =
    Model.keccakHashRust (Contracts.bytesAt u0 (vecPtr u0 p) (8 * (vecLen u0 p).toNat))

theorem copyHash (hM : Runtime.MemcpySpec 0x800126e4) (hK : KeccakHashSpec)
    {s u0 u w : MachineState} {p E B : Word} (hpre : VsoPre s) (hp : PathOk s u0 p)
    (hin : PathIn s u0 p E u) (ha : LeafAlloc s u0 p E u w B) :
    ∃ v, Reaches Image.code w v ∧ (Dead Image.code v ∨ Hashed s u0 p E u v) := by
  have hm := stack_mapped hpre
  have hb := bounds hpre
  have hnx := hpre.stack.next
  rw [stackLo_vso, vso_stack] at hnx
  have hab := hpre.stack.above
  simp only [vso_stack] at hab
  have hL := Region.bounds hp.leaf
  have hnB := len8 hp
  have hsp := ha.sp
  obtain ⟨hB1, hB2⟩ := ha.buf
  have hwhi := ha.heap.hi
  have hulo := hin.heap.lo
  have hu0u := hin.mono
  obtain ⟨hs1, hs2, -⟩ := hp.leafSafe
  have hmapB : Mapped B (8 * (vecLen u0 p).toNat) := by addr_omega [hB1, hB2, hulo, hwhi]
  have hapB : Apart B (8 * (vecLen u0 p).toNat) (s.getReg .x2 - 2464) 2464 := by
    addr_omega [hB2, hwhi, hab, hm]
  -- the copy
  obtain ⟨t1, r1, h1⟩ := Sym.BlockSpec.reaches b8000ab94_spec ha.pc (by
    rv_eval [hsp]; and_intros <;> valid_access hpre.stack.valid [hb])
  have k1 := b8000ab94_keeps h1
  have m1 := b8000ab94_mem_same h1
  have x20₁ : t1.getReg .x20 = B := by
    rw [b8000ab94_x20 h1, hsp, show s.getReg .x2 - 1040 + 664 = s.getReg .x2 - 376 by rv_eval []]
    exact ha.ptr
  have x27₁ : t1.getReg .x27 = 0 := by
    rw [b8000ab94_x27 h1, hsp, show s.getReg .x2 - 1040 + 672 = s.getReg .x2 - 368 by rv_eval []]
    exact ha.len
  have pc1 : t1.pc = 0x8000aba0 := b8000ab94_pc_not_taken h1 (by
    rw [ha.x8]; intro h0; exact hp.leafNe (by rw [h0]; rfl))
  obtain ⟨t2, r2, h2⟩ := Sym.BlockSpec.reaches b8000aba0_spec pc1 trivial
  have k2 := b8000aba0_keeps h2
  have m2 := b8000aba0_mem_same h2
  have sp2 : t2.getReg .x2 = s.getReg .x2 - 1040 := by
    rw [k2 .x2 (by decide), k1 .x2 (by decide), hsp]
  have x10₂ : t2.getReg .x10 = B := by rw [b8000aba0_x10 h2, x20₁, x27₁, add_zero]
  have x11₂ : t2.getReg .x11 = vecPtr u0 p := by
    rw [b8000aba0_x11 h2, k1 .x18 (by decide), ha.x18]
  have x12₂ : (t2.getReg .x12).toNat = 8 * (vecLen u0 p).toNat := by
    rw [b8000aba0_x12 h2, k1 .x21 (by decide), ha.x21, hnB]
  obtain ⟨t3, r3, hv3⟩ := callMemcpyG hM hpre (b8000aba0_pc h2) sp2
    (by rw [x10₂, x12₂]; exact hmapB) (by rw [x11₂, x12₂]; exact hp.leaf.1)
    (by rw [x10₂, x11₂, x12₂]; rcases hs1 with h | h <;> addr_omega [h, hB1, hB2, hu0u, hwhi, hL])
    (by rw [x10₂, x12₂]; exact hapB) (by rw [x11₂, x12₂]; exact hs2)
  rcases hv3 with hd | ⟨pc3, pr3, by3, fr3⟩
  · exact ⟨t3, r1.trans (r2.trans r3), Or.inl hd⟩
  rw [x10₂, x11₂, x12₂] at by3
  rw [x10₂, x12₂] at fr3
  -- `keccak_hash`
  obtain ⟨t4, r4, h4⟩ := Sym.BlockSpec.reaches b8000abb4_spec
    (by rw [pc3, returnAddress_eq, b8000aba0_x1 h2]; rfl) trivial
  have k4 := b8000abb4_keeps h4
  have m4 := b8000abb4_mem_same h4
  obtain ⟨t5, r5, h5⟩ := Sym.BlockSpec.reaches b8000abb8_spec (b8000abb4_pc h4) trivial
  have k5 := b8000abb8_keeps h5
  have m5 := b8000abb8_mem_same h5
  have sp5 : t5.getReg .x2 = s.getReg .x2 - 1040 := by
    rw [k5 .x2 (by decide), k4 .x2 (by decide), pr3.reg .x2, sp2]
  have x11₅ : t5.getReg .x11 = B := by
    rw [b8000abb8_x11 h5, k4 .x20 (by decide), pr3.reg .x20, k2 .x20 (by decide), x20₁]
  have x12₅ : (t5.getReg .x12).toNat = 8 * (vecLen u0 p).toNat := by
    rw [b8000abb8_x12 h5, b8000abb4_x27 h4, pr3.reg .x27, pr3.reg .x21, k2 .x27 (by decide),
      k2 .x21 (by decide), x27₁, k1 .x21 (by decide), ha.x21, zero_add, hnB]
  have nx3 : t3.getMem nextAddr = t2.getMem nextAddr := fr3 _ fun i hi hw ↦ by
    rcases hw with hw | hw
    · addr_omega [hw, hi, hB2, hwhi]
    · addr_omega [hw, hi, hm, hnx]
  have hn5 : heapNext t5 = heapNext w := by simp only [heapNext, m5, m4, nx3, m2, m1]
  have frA : DFrame u t5 (PW s (heapNext u) (heapNext t5)) := by
    rw [hn5]
    refine ((((ha.fr.trans (DFrame.of_same m1 _) fun _ h ↦ h).trans (DFrame.of_same m2 _)
      fun _ h ↦ h).trans fr3 fun a ha' ↦ ?_).trans (DFrame.of_same m4 _) fun _ h ↦ h).trans
      (DFrame.of_same m5 _) fun _ h ↦ h
    rcases ha' with ha' | ha'
    · exact PW.of_heap (by addr_omega [ha', hB1]) (by addr_omega [ha', hB2])
    · exact PW.of_stack (by addr_omega [ha', hm])
  have rod5 : RodataOk t5 := hin.rodata.dframe frA (PW.rodata hpre (by rw [hn5]; exact hwhi))
  obtain ⟨t6, r6, hv6⟩ := callKeccakG hK hpre (b8000abb8_pc h5) sp5
    (by rw [b8000abb8_x10 h5, k4 .x2 (by decide), pr3.reg .x2, sp2]; rv_eval [])
    (by rw [x11₅, x12₅]; exact hmapB) (by rw [x11₅, x12₅]; exact hapB) rod5
  rcases hv6 with hd | ⟨pc6, pr6, by6, fr6⟩
  · exact ⟨t6, r1.trans (r2.trans (r3.trans (r4.trans (r5.trans r6)))), Or.inl hd⟩
  rw [x11₅, x12₅] at by6
  have nx6 : t6.getMem nextAddr = t5.getMem nextAddr := fr6 _ fun i hi hw ↦ by
    rcases hw with hw | hw <;> addr_omega [hw, hi, hm, hnx]
  have hn6 : heapNext t6 = heapNext w := by simp only [heapNext, nx6]; exact hn5
  have frB : DFrame u t6 (PW s (heapNext u) (heapNext t6)) := by
    rw [hn6, ← hn5]
    exact frA.trans fr6 fun a ha' ↦ by
      rcases ha' with ha' | ha'
      · exact PW.of_cw (Or.inr (Or.inr (Or.inr ha')))
      · exact PW.of_stack (by addr_omega [ha', hm])
  -- the leaf's bytes
  have hleaf : Contracts.bytesAt t5 B (8 * (vecLen u0 p).toNat) =
      Contracts.bytesAt u0 (vecPtr u0 p) (8 * (vecLen u0 p).toNat) := by
    have e5 : Contracts.bytesAt t5 B (8 * (vecLen u0 p).toNat) =
        Contracts.bytesAt t3 B (8 * (vecLen u0 p).toNat) := by
      simp only [Contracts.bytesAt, MachineState.getByte, m5, m4]
    have e2 : Contracts.bytesAt t2 (vecPtr u0 p) (8 * (vecLen u0 p).toNat) =
        Contracts.bytesAt w (vecPtr u0 p) (8 * (vecLen u0 p).toNat) := by
      simp only [Contracts.bytesAt, MachineState.getByte, m2, m1]
    rw [e5, by3, e2, DFrame.bytesK ha.fr hL.2.2 _ (by omega)
        ((hp.leafSafe.mono hu0u).misses hpre hwhi),
      DFrame.bytesK hin.fr hL.2.2 _ (by omega) (hp.leafSafe.misses hpre hin.heap.hi)]
  have kk (r : Reg) (hr : r ∈ [Reg.x9, .x22, .x25, .x26]) : t6.getReg r = w.getReg r := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;>
      rw [pr6.reg _, k5 _ (by decide), k4 _ (by decide), pr3.reg _, k2 _ (by decide),
        k1 _ (by decide)]
  refine ⟨t6, r1.trans (r2.trans (r3.trans (r4.trans (r5.trans r6)))), Or.inr {
    pc := by rw [pc6, returnAddress_eq, b8000abb8_x1 h5]; rfl
    sp := by rw [pr6.reg .x2, sp5]
    x22 := by rw [kk .x22 (by simp), ha.x22]
    x25 := by rw [kk .x25 (by simp), ha.x25]
    regs := fun r hr ↦ by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · rw [kk .x9 (by simp), ha.regs .x9 (by simp)]
      · rw [kk .x26 (by simp), ha.regs .x26 (by simp)]
    fr := frB
    heap := ⟨by rw [hn6]; exact ha.heap.lo, by rw [hn6]; exact hwhi⟩
    mono := by rw [hn6]; exact ha.mono
    node := by rw [by6, hleaf] }⟩

end Rv64Verifier.Proofs.Pcs.Vso
