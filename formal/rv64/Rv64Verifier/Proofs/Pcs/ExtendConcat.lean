import Rv64Verifier.Proofs.Pcs.ExtendSel

/-!
# `Vec<StackClaim>::extend_desugared`: the push's `concat`

From `AfterSel` at `0x80009d08`: the slices `[point, selector]` at `F + 104`, `concat(F + 56,
slices, 2)`, to `Mid` at `0x80009d34`, the claim's stack point in the new `Vec` at `F + 56`.
-/

namespace Rv64Verifier.Proofs.Pcs.Extend
open RiscvZkvm.Rv64 Rv64Verifier.Runtime Rv64Verifier.Transcript Rv64Verifier.Pcs
  Rv64Verifier.PcsContracts Rv64Verifier.Model.Pcs Rv64Verifier.Blocks.F37 LeanVM.Parameters
open Rv64Verifier.Sym (reduceReg reducePc reduceMem reduceWrites reduceObl)

/-- Claim `k`'s point on the stack. -/
def stackPt (s : MachineState) (k : Nat) : List E :=
  (⟨varsAt s k, idxAt s k⟩ : Model.PlacementRust).stackPoint (columnClaimAt s (clAt s k)).point
    (stackLogAt s)

/-- At `0x80009d34`, `concat` returned. -/
structure Mid (s u v : MachineState) (k : Nat) : Prop where
  pc : v.pc = 0x80009d34
  sp : v.getReg .x2 = s.getReg .x2 - 240
  keep : ∀ r ∈ [Reg.x8, .x9, .x19, .x20, .x21, .x22, .x23, .x24], v.getReg r = u.getReg r
  x18 : v.getReg .x18 = clAt s k
  x25 : v.getReg .x25 = clAt s (k + 1)
  heap : HeapOk v
  mono : heapNext u ≤ heapNext v
  fr : DFrame u v (CallW s u (v.getMem nextAddr))
  pt : NewVecE u v (s.getReg .x2 - 184) (stackPt s k)

theorem CallW.mono {s u : MachineState} {nx nx' x : Word} (h : CallW s u nx x)
    (hle : nx.toNat ≤ nx'.toNat) : CallW s u nx' x := by
  rcases h with h | h | h | h
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr (Or.inl h))
  · exact Or.inr (Or.inr (Or.inr ⟨h.1, by omega⟩))

/-- From the entry on, through a pass's calls. -/
theorem Inv.callFrame {s u v : MachineState} {j : Nat} {nx : Word} (h : Inv s u j)
    (hf : DFrame u v (CallW s u nx)) (hle : (u.getMem nextAddr).toNat ≤ nx.toNat) :
    DFrame s v (Wr s extendStack (W s) nx) := by
  refine (h.p.mem.mono fun a ha ↦ ha.mono hle).trans hf fun a ha ↦ ?_
  have hm := h.p.mono
  rcases ha with ha | ha | ha | ha
  · exact Or.inl (Or.inr ha)
  · exact Or.inr (Or.inl (by addr_omega [ha]))
  · exact Or.inr (Or.inr (Or.inl ha))
  · exact Or.inr (Or.inr (Or.inr ⟨Nat.le_trans hm ha.1, ha.2⟩))

/-- A slice the function reads, kept from the entry on. -/
theorem src_eList {s v : MachineState} {nx : Word} (hd : DFrame s v (Wr s extendStack (W s) nx))
    (hnx : nx.toNat ≤ heapEnd) {a : Word} {m : Nat} (hs : Src s extendStack a (24 * m))
    (ho : ExtendOff s a (24 * m)) : eListAt v a m = eListAt s a m := by
  have hm := hs.miss (w := W s) (fun x hx hw ↦ by
    have hb := hs.bound
    rcases hw with hw | hw
    · rcases hb with hb | hb
      · simp only [Within] at hx; omega
      · addr_omega [hx, hw, ho.1, hb]
    · rcases hb with hb | hb
      · simp only [Within] at hx; omega
      · addr_omega [hx, hw, ho.2, hb]) hnx
  refine hd.eList hm ?_
  rcases hs.bound with h0 | h0
  · left; omega
  · right; omega

theorem concat_step (hC : MultilinearContracts.SliceConcatSpec) {s u t : MachineState} {k : Nat}
    (hpre : ExtendPre s) (hp : Push s u k) (ha : AfterSel s u t k) :
    ∃ v, Reaches Image.code t v ∧ (Dead Image.code v ∨ Mid s u v k) := by
  have hI := hp.inv
  have hk := hp.lt
  have hb := sbounds hpre
  have hst := hpre.stack
  have hv := hst.valid
  rw [hK] at hv
  obtain ⟨t₃, hr₃, h₃⟩ := Sym.BlockSpec.reaches b80009d08_spec ha.pc (by
    rv_eval [ha.sp]
    and_intros <;> valid_access hv [hb])
  have k₃ := b80009d08_keeps h₃
  have hf₃ := DFrame.of_memFrame (b80009d08_frame h₃ (by rw [ha.sp]; addr_omega [hb]))
  have hsp₃ : t₃.getReg .x2 = s.getReg .x2 - BitVec.ofNat 64 240 := (k₃ .x2 (by decide)).trans ha.sp
  have e104 : t.getReg .x2 + 104 = s.getReg .x2 - 136 := by rw [ha.sp]; addr_omega [hb]
  rw [e104] at hf₃
  have hm₃ (a : Word) (h1 : a.toNat + 8 ≤ (s.getReg .x2).toNat - 136 ∨
      (s.getReg .x2).toNat - 104 ≤ a.toNat) (h2 : a.toNat + 8 ≤ 2 ^ 64) : t₃.getMem a = t.getMem a :=
    hf₃ a fun i hi hw ↦ by addr_omega [hw, hi, h1, h2, hb]
  have p0 : t₃.getMem (s.getReg .x2 - 136) = s.getMem (clAt s k + 8) := by
    rw [← e104, b80009d08_m_x2_104 h₃, ha.x26]
  have l0 : t₃.getMem (s.getReg .x2 - 128) = s.getMem (clAt s k + 16) := by
    rw [show s.getReg .x2 - 128 = t.getReg .x2 + 112 by rw [ha.sp]; addr_omega [hb],
      b80009d08_m_x2_112 h₃, ha.x27]
  have p1 : t₃.getMem (s.getReg .x2 - 120) = vecPtr t (s.getReg .x2 - 160) := by
    rw [show s.getReg .x2 - 120 = t.getReg .x2 + 120 by rw [ha.sp]; addr_omega [hb],
      b80009d08_m_x2_120 h₃, ha.sp, vecPtr]
    congr 1; addr_omega [hb]
  have l1 : t₃.getMem (s.getReg .x2 - 112) = vecLen t (s.getReg .x2 - 160) := by
    rw [show s.getReg .x2 - 112 = t.getReg .x2 + 128 by rw [ha.sp]; addr_omega [hb],
      b80009d08_m_x2_128 h₃, ha.sp, vecLen]
    congr 1; addr_omega [hb]
  have hn₃ : t₃.getMem nextAddr = t.getMem nextAddr := hm₃ _ (by addr_omega [hb]) (by addr_omega [hb])
  have hnx₃ : heapNext t₃ = heapNext t := by simp only [heapNext, hn₃]
  have x11₃ := b80009d08_x11 h₃
  rw [ha.sp] at x11₃
  have x11₃' : t₃.getReg .x11 = s.getReg .x2 - 136 := by rw [x11₃]; addr_omega [hb]
  have x10₃ : t₃.getReg .x10 = s.getReg .x2 - 184 := by
    rw [b80009d08_x10 h₃, ha.sp]; addr_omega [hb]
  have x12₃ : (t₃.getReg .x12).toNat = 2 := by rw [b80009d08_x12 h₃]; rfl
  have hsl : stackLo t₃ MultilinearContracts.sliceConcatStack = s.getReg .x2 - 464 := by
    simp only [stackLo, hsp₃]; addr_omega [hb]
  -- the parts
  have q0 : MultilinearContracts.partPtr t₃ 0 = s.getMem (clAt s k + 8) := by
    simp only [MultilinearContracts.partPtr, x11₃', Nat.mul_zero, add_ofNat_zero, p0]
  have n0 : MultilinearContracts.partLen t₃ 0 = (s.getMem (clAt s k + 16)).toNat := by
    simp only [MultilinearContracts.partLen, x11₃', Nat.mul_zero, add_ofNat_zero]
    rw [show s.getReg .x2 - 136 + 8 = s.getReg .x2 - 128 by addr_omega [hb], l0]
  have q1 : MultilinearContracts.partPtr t₃ 1 = vecPtr t (s.getReg .x2 - 160) := by
    simp only [MultilinearContracts.partPtr, x11₃']
    rw [show s.getReg .x2 - 136 + BitVec.ofNat 64 (16 * 1) = s.getReg .x2 - 120 by addr_omega [hb], p1]
  have n1 : MultilinearContracts.partLen t₃ 1 = (vecLen t (s.getReg .x2 - 160)).toNat := by
    simp only [MultilinearContracts.partLen, x11₃']
    rw [show s.getReg .x2 - 136 + BitVec.ofNat 64 (16 * 1) + 8 = s.getReg .x2 - 112 by
      addr_omega [hb], l1]
  have hu' : heapNext s ≤ heapNext u := hI.p.mono
  have htm := ha.mono
  have hhi := ha.heap.hi
  have hlo' : heapStart ≤ heapNext u := le_trans hpre.heap.lo hu'
  simp only [heapStart] at hlo'
  have hheap₃ : HeapOk t₃ := ⟨by rw [hnx₃]; exact ha.heap.lo, by rw [hnx₃]; exact ha.heap.hi⟩
  have hPt : Src s extendStack (s.getMem (clAt s k + 8)) (24 * (s.getMem (clAt s k + 16)).toNat) :=
    hpre.points k hk
  have hPo : ExtendOff s (s.getMem (clAt s k + 8)) (24 * (s.getMem (clAt s k + 16)).toNat) :=
    hpre.pointsOff k hk
  have hfr3 : DFrame u t₃ (CallW s u (t₃.getMem nextAddr)) :=
    (ha.fr.mono fun a h ↦ h.mono (by rw [hn₃])).trans hf₃
      fun a h ↦ Or.inr (Or.inl (by rw [hK]; addr_omega [h, hb]))
  have hpreC : MultilinearContracts.SliceConcatPre t₃ := {
    heap := hheap₃
    out := by rw [x10₃]; simp only [Region, Mapped]; addr_omega [hb]
    count := by rw [x12₃]; decide
    slices := by rw [x11₃', x12₃]; simp only [Region, Mapped]; addr_omega [hb]
    stack := hst.sub 240 hsp₃ (by decide) (by decide) (by decide) (by decide) (by decide)
    outFree := by
      rw [x10₃]; simp only [Outside]; exact ⟨Or.inr (by addr_omega [hb]), by addr_omega [hb]⟩
    outStack := by rw [x10₃, hsl]; addr_omega [hb]
    slicesFree := by
      rw [x11₃', x12₃]; simp only [Outside]; exact ⟨Or.inr (by addr_omega [hb]), by addr_omega [hb]⟩
    slicesStack := by rw [x11₃', x12₃, hsl]; addr_omega [hb]
    slicesOut := by rw [x11₃', x12₃, x10₃]; addr_omega [hb]
    part := by
      intro i hi
      rw [x12₃] at hi
      rw [x10₃, hsl]
      match i, hi with
      | 0, _ =>
        rw [q0, n0]
        rcases hPt.region with h0 | hR
        · left; omega
        · right
          have hRb := Region.bounds hR
          have hfr := hPt.free
          simp only [Outside] at hfr
          have hsk := hPt.stack
          rw [hK] at hsk
          refine ⟨hR, ⟨?_, hfr.2⟩, by addr_omega [hsk, hb, hRb], by addr_omega [hsk, hb, hRb]⟩
          rcases hfr.1 with h | h
          · left; rw [hnx₃]; omega
          · right; exact h
      | 1, _ =>
        rw [q1, n1]
        obtain ⟨hal, hS0 | ⟨hS1, hS2⟩⟩ := ha.selBuf
        · left; omega
        · right
          refine ⟨heap_region (by omega) (by omega) hal,
            ⟨Or.inl (by rw [hnx₃]; omega), by addr_omega [hS2, hhi]⟩,
            by addr_omega [hS2, hhi, hb], by addr_omega [hS2, hhi, hb]⟩ }
  obtain ⟨t₄, hr₄, ⟨hpc₄, hpres₄, hpost₄⟩ | hdead⟩ := hC.call hr₃ (b80009d08_pc h₃) hpreC
  swap
  · exact ⟨t₄, hr₄, Or.inl hdead⟩
  have kp (r : Reg) (hr : r ∈ calleeSaved) : t₄.getReg r = t₃.getReg r := hpres₄ r hr
  have hnv := hpost₄.value
  rw [x10₃] at hnv
  have hfr₄ := hpost₄.frame
  rw [x10₃, hsl] at hfr₄
  have hm4 := hpost₄.mono
  have hhi4 := hpost₄.heap.hi
  have hpt : (MultilinearContracts.parts t₃).flatten = stackPt s k := by
    simp only [MultilinearContracts.parts, x12₃]
    rw [show List.range 2 = [0, 1] from rfl]
    simp only [List.map_cons, List.map_nil, List.flatten_cons, List.flatten_nil, List.append_nil, q0,
      n0, q1, n1]
    rw [src_eList (hI.callFrame hfr3 (by rw [hn₃]; exact htm)) (by rw [hn₃]; exact hhi) hPt hPo]
    have hsel : eListAt t₃ (vecPtr t (s.getReg .x2 - 160)) (vecLen t (s.getReg .x2 - 160)).toNat =
        vecEs t (s.getReg .x2 - 160) := by
      obtain ⟨hal, hS0 | ⟨hS1, hS2⟩⟩ := ha.selBuf
      · have h0 : (vecLen t (s.getReg .x2 - 160)).toNat = 0 := by omega
        simp only [vecEs, h0]
        rfl
      · exact hf₃.eList (fun x hx hw ↦ by addr_omega [hx, hw, hS2, hhi, hb])
          (Or.inr (by addr_omega [hS2, hhi]))
    rw [hsel, ha.sel]
    rfl
  refine ⟨t₄, hr₄, Or.inr ⟨?_, ?_, ?_, ?_, ?_, hpost₄.heap, ?_, ?_, ?_⟩⟩
  · rw [hpc₄, returnAddress_eq, b80009d08_x1 h₃]; decide
  · rw [kp .x2 (by decide), hsp₃]; rfl
  · intro r hr
    rw [kp r ((by decide : [Reg.x8, .x9, .x19, .x20, .x21, .x22, .x23, .x24] ⊆ calleeSaved) hr),
      keeps_sub k₃ (by decide) r hr]
    exact ha.keep r hr
  · rw [kp .x18 (by decide), k₃ .x18 (by decide), ha.x18]
  · rw [kp .x25 (by decide), k₃ .x25 (by decide), ha.x25]
  · have : heapNext t₃ = heapNext t := hnx₃
    omega
  · refine (hfr3.mono fun a h ↦ h.mono hm4).trans hfr₄
      fun a h ↦ ?_
    rcases h with h | h | h | h
    · exact Or.inr (Or.inl (by rw [hK]; addr_omega [h, hb]))
    · exact Or.inr (Or.inl (by rw [hK]; addr_omega [h, hb]))
    · exact Or.inr (Or.inr (Or.inl h))
    · simp only [Fresh] at h
      exact Or.inr (Or.inr (Or.inr ⟨by rw [hnx₃] at h; omega, h.2⟩))
  · rw [← hpt]
    exact ⟨hnv.vec, by
      have := hnv.buf; simp only [NewBuf] at this ⊢; rw [hnx₃] at this; omega, hnv.elems⟩

end Rv64Verifier.Proofs.Pcs.Extend
