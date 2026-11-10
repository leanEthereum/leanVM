import Rv64Verifier.Proofs.Layout.ExtendBase

/-!
# `extend_trusted`: through `reserve`

From the entry to `0x80006000`'s branch: the buffer `P` of capacity `C` has room for the new
blocks and keeps the old ones (`Res`).
-/

namespace Rv64Verifier.Layout.Extend
open RiscvZkvm.Rv64 Rv64Verifier.Runtime Rv64Verifier.Sym Rv64Verifier.Blocks.F22
  Rv64Verifier.Model.LayoutMirror
open Rv64Verifier.Sym (reduceReg reducePc reduceMem reduceWrites reduceObl)

/-- The `Vec`'s length at entry. -/
abbrev len (s : MachineState) : Nat := (vecLen s (s.getReg .x10)).toNat

/-- After `reserve`: `P`, `C` the buffer, `N2` the heap's end then. -/
structure Res (s : MachineState) (P C : Word) (N2 : Nat) : Prop where
  align : P.toNat % 8 = 0
  room : len s + itLen s ≤ C.toNat
  fit : C.toNat = 0 ∨ heapStart ≤ P.toNat ∧ P.toNat + 48 * C.toNat ≤ N2
  lo : heapNext s ≤ N2
  hi : N2 ≤ heapEnd
  same : (P = vecPtr s (s.getReg .x10) ∧ C = vecCap s (s.getReg .x10)) ∨
    C.toNat = 0 ∨ heapNext s ≤ P.toNat ∧ P.toNat + 48 * C.toNat ≤ N2

/-- The buffer is the old one, or new. -/
theorem Res.wr {s : MachineState} {P C : Word} {N2 : Nat} (h : Res s P C N2) {a : Word}
    (ha : Within a P (48 * C.toNat)) : W s a ∨ (heapNext s ≤ a.toNat ∧ a.toNat < N2) := by
  rcases h.same with ⟨rfl, rfl⟩ | h0 | h0
  · exact Or.inl (Or.inl (Or.inr ha))
  · simp only [Within] at ha; omega
  · exact Or.inr (by simp only [Within] at ha; omega)

/-- The registers and memory at `0x80006000`'s branch. -/
structure Mid (s u : MachineState) (P C : Word) : Prop where
  x8 : u.getReg .x8 = s.getReg .x10
  x9 : u.getReg .x9 = s.getReg .x11
  x18 : u.getReg .x18 = BitVec.ofNat 64 (itLen s)
  x19 : u.getReg .x19 = vecLen s (s.getReg .x10)
  x20 : u.getReg .x20 = itEnd s
  x22 : u.getReg .x22 = itStart s
  x23 : u.getReg .x23 = itEnd s - itStart s
  hdr : u.getMem (s.getReg .x10) = C ∧ u.getMem (s.getReg .x10 + 8) = P ∧
    u.getMem (s.getReg .x10 + 16) = vecLen s (s.getReg .x10)
  old : bytesAt u P (48 * len s) = bytesAt s (vecPtr s (s.getReg .x10)) (48 * len s)

theorem iter_facts {s : MachineState} (hpre : ExtendPre s) :
    Apart (s.getReg .x11) 40 (stackLo s extendStack) extendStack ∧
      (s.getReg .x11).toNat + 40 ≤ 0xc0000008 ∧ (s.getReg .x11).toNat % 8 = 0 := by
  have hb := ValidMemRange.bounds hpre.iter (by decide)
  exact ⟨apart_of fun x hx hs ↦ (hpre.kept x (Or.inl hx)).2.2.1 hs, by omega, hb.2.1⟩

theorem start (hR : ReserveFreshSpec 0x800060bc 48 8) {s : MachineState} (hpc : s.pc = 0x80005f94)
    (hpre : ExtendPre s) :
    ∃ u, Reaches Image.code s u ∧ ((∃ nx P C, Res s P C nx.toNat ∧ Inv s u nx ∧ Mid s u P C ∧
      u.pc = (if itEnd s = itStart s then 0x80006084 else 0x80006008)) ∨ Dead Image.code u) := by
  have hb := bounds hpre
  have hst := hpre.stack
  have hab := hst.above
  have hnx8 := hst.next
  have hheap := hpre.heap
  obtain ⟨hit, hit2, hit8⟩ := iter_facts hpre
  have hss := hpre.selfStack
  have hsf := hpre.selfFree
  simp only [Outside] at hsf
  have hbb := buf_bounds hpre
  have hsb := ValidMemRange.bounds hpre.self (by decide)
  obtain ⟨t₁, hr₁, h₁⟩ := BlockSpec.reaches b80005f94_spec hpc (by
    rv_eval []
    and_intros <;> first
      | valid_access hst.valid [hb]
      | valid_access hpre.iter [hit2, hit8]
      | addr_omega [hb, hit, hit2])
  have k₁ := b80005f94_keeps h₁
  have hm₁ := b80005f94_frame h₁ (by addr_omega [hb])
  have hdm₁ := hm₁.dframe
  have hsame₁ {a : Word} (ha : ∀ x, Within x a 8 → ¬ Within x (s.getReg .x2 - 88) 88)
      (hw : a.toNat + 8 ≤ 2 ^ 64) : t₁.getMem a = s.getMem a := hdm₁.getMem_of ha hw
  have inv₁ : Inv s t₁ (s.getMem nextAddr) := {
    sp := b80005f94_x2 h₁
    saved := by
      simp only [slots, List.forall_mem_cons, List.not_mem_nil, false_implies, implies_true,
        and_true]
      rv_eval []
      exact ⟨b80005f94_m_x2_n8 h₁, b80005f94_m_x2_n16 h₁, b80005f94_m_x2_n24 h₁,
        b80005f94_m_x2_n32 h₁, b80005f94_m_x2_n40 h₁, b80005f94_m_x2_n48 h₁, b80005f94_m_x2_n56 h₁,
        b80005f94_m_x2_n64 h₁, b80005f94_m_x2_n72 h₁, b80005f94_m_x2_n80 h₁, b80005f94_m_x2_n88 h₁⟩
    regs := fun r hr ↦ k₁ r (by revert hr; revert r; decide)
    mem := hdm₁.mono fun a ha ↦ Or.inr (Or.inl (by addr_omega [ha, hb]))
    next := hsame₁ (fun x hx h' ↦ by addr_omega [hx, h', hb, hnx8]) (by decide)
    mono := Nat.le_refl _
    fits := hheap.hi }
  have hsp₁ : t₁.getReg .x2 = s.getReg .x2 - 144 := b80005f94_x2 h₁
  have e0 : t₁.getMem (s.getReg .x10) = s.getMem (s.getReg .x10) :=
    hsame₁ (fun x hx h' ↦ by addr_omega [hx, h', hss, hb, hsb]) (by addr_omega [hss, hb, hsb])
  have e8 : t₁.getMem (s.getReg .x10 + 8) = s.getMem (s.getReg .x10 + 8) :=
    hsame₁ (fun x hx h' ↦ by addr_omega [hx, h', hss, hb, hsb]) (by addr_omega [hss, hb, hsb])
  have e16 : t₁.getMem (s.getReg .x10 + 16) = s.getMem (s.getReg .x10 + 16) :=
    hsame₁ (fun x hx h' ↦ by addr_omega [hx, h', hss, hb, hsb]) (by addr_omega [hss, hb, hsb])
  have hn₁ : heapNext t₁ = heapNext s := by simp only [heapNext, inv₁.next]
  have x10₁ : t₁.getReg .x10 = s.getReg .x10 := k₁ .x10 (by decide)
  -- `k`, from the slice's byte length
  have hd : ((s.getMem (s.getReg .x11 + 8) - s.getMem (s.getReg .x11)) >>> 3).toNat =
      ((itEnd s).toNat - (itStart s).toNat) / 8 := by
    rw [BitVec.toNat_ushiftRight, BitVec.toNat_sub, Nat.shiftRight_eq_div_pow]
    have := hpre.bounds
    have := (itEnd s).isLt
    have := (itStart s).isLt
    simp only [itEnd, itStart] at *
    omega
  have hK : t₁.getReg .x11 = BitVec.ofNat 64 (itLen s) := by
    have hw := hpre.whole
    rw [b80005f94_x11 h₁, div3 _ (by rw [hd]; omega), hd]
    simp only [itLen]
    congr 1
    omega
  have hsl : stackLo t₁ reserveStack = s.getReg .x2 - 304 := by
    simp only [stackLo, reserveStack, hsp₁]; rv_eval []
  have hvec₁ : VecOk t₁ (s.getReg .x10) 48 8 := by
    have hv := hpre.vec
    exact ⟨by simp only [RawVecOk, Buf, vecPtr, vecCap, hn₁, e0, e8]; exact hv.raw,
      by simp only [vecLen, vecCap, e0, e16]; exact hv.len⟩
  have hpre₁ : ReservePre 48 8 t₁ := {
    heap := ⟨hn₁ ▸ hheap.lo, hn₁ ▸ hheap.hi⟩
    self := x10₁ ▸ hpre.self
    vec := x10₁ ▸ hvec₁
    stack := hst.inner (k := 144) hsp₁ (by decide) (by decide) (by decide) (by decide) (by decide)
    selfFree := by rw [x10₁]; simp only [Outside, hn₁]; exact ⟨hsf.1, hsf.2⟩
    selfStack := by rw [x10₁, hsl]; addr_omega [hss, hb] }
  obtain ⟨t₂, hr₂, ⟨hpc₂, hpres₂, ⟨hp₂, hsame₂⟩⟩ | hdead⟩ := hR.call hr₁ (b80005f94_pc h₁) hpre₁
  swap
  · exact ⟨t₂, hr₂, Or.inr hdead⟩
  have hcap := hp₂.cap
  have hvec₂ := hp₂.vec
  have hlen₂ := hp₂.len
  have hbytes := hp₂.bytes
  have hfr₂ := hp₂.frame
  rw [x10₁] at hcap hvec₂ hlen₂ hbytes hsame₂
  rw [x10₁, hsl] at hfr₂
  rw [hK] at hcap
  have hbb₂ := vecBuf_bounds hvec₂ (by decide)
  have hmono₂ := hp₂.mono
  have hhi₂ := hp₂.heap.hi
  rw [hn₁] at hmono₂
  have inv₂ : Inv s t₂ (t₂.getMem nextAddr) := inv₁.step hpre hfr₂.dframe (fun a ha ↦ by
      rcases ha with ha | ha | ha | ha
      · exact Or.inl (Or.inl (Or.inl (by addr_omega [ha])))
      · exact Or.inl (Or.inr (by addr_omega [ha, hb]))
      · exact Or.inr (Or.inl ha)
      · simp only [Fresh, hn₁] at ha
        exact Or.inr (Or.inr ha))
    rfl hmono₂ hhi₂ fun r hr ↦ hpres₂ r (by unfold calleeSaved; revert hr; revert r; decide)
  have hsp₂ : t₂.getReg .x2 = s.getReg .x2 - 144 := (hpres₂.reg .x2).trans hsp₁
  have x8₂ : t₂.getReg .x8 = s.getReg .x10 := by rw [hpres₂.reg .x8, b80005f94_x8 h₁]
  obtain ⟨t₃, hr₃, h₃⟩ := BlockSpec.reaches b80006000_spec
    (by rw [hpc₂, returnAddress_eq, b80005f94_x1 h₁]; decide) (by
      rv_eval [x8₂]; valid_access hpre.self [hss, hb, hsb])
  have k₃ := b80006000_keeps h₃
  have hm₃ := b80006000_mem_same h₃
  obtain ⟨P, hP⟩ : ∃ P, P = vecPtr t₂ (s.getReg .x10) := ⟨_, rfl⟩
  obtain ⟨C, hC⟩ : ∃ C, C = vecCap t₂ (s.getReg .x10) := ⟨_, rfl⟩
  rw [← hP] at hbb₂ hsame₂ hbytes
  rw [← hC] at hbb₂ hcap hsame₂
  have hlen₁ : vecLen t₁ (s.getReg .x10) = vecLen s (s.getReg .x10) := e16
  rw [hlen₁] at hcap
  have hreg (r : Reg) (hr : r ∈ [Reg.x8, .x9, .x18, .x20, .x22, .x23]) : t₃.getReg r = t₁.getReg r := by
    rw [k₃ r (by revert hr; revert r; decide), hpres₂ r (by unfold calleeSaved; revert hr; revert r; decide)]
  refine ⟨t₃, hr₂.trans hr₃, Or.inl ⟨t₂.getMem nextAddr, P, C, {
      align := hbb₂.1
      room := by
        have h' : (BitVec.ofNat 64 (itLen s)).toNat = itLen s := by
          rw [BitVec.toNat_ofNat]
          exact Nat.mod_eq_of_lt (by simp only [itLen]; have := (itEnd s).isLt; omega)
        rw [h'] at hcap
        exact hcap
      fit := by
        rcases hbb₂.2 with h0 | h0
        · exact Or.inl h0
        · exact Or.inr ⟨h0.1, by simp only [heapNext] at h0; omega⟩
      lo := hmono₂
      hi := hhi₂
      same := by
        rcases hsame₂ with ⟨h0, h1⟩ | h0
        · left
          simp only [vecPtr, vecCap, e0, e8] at h0 h1
          exact ⟨h0, h1⟩
        · right
          simp only [NewBuf, hn₁] at h0
          rcases h0.2 with h2 | h2
          · exact Or.inl (by omega)
          · exact Or.inr ⟨h2.1, by simp only [heapNext] at h2; omega⟩ },
    inv₂.same hpre hm₃ k₃, {
      x8 := (hreg .x8 (by decide)).trans (b80005f94_x8 h₁)
      x9 := (hreg .x9 (by decide)).trans (b80005f94_x9 h₁)
      x18 := by rw [hreg .x18 (by decide), b80005f94_x18 h₁]; exact (b80005f94_x11 h₁).symm.trans hK
      x19 := by rw [b80006000_x19 h₃, x8₂]; exact hlen₂.trans hlen₁
      x20 := by rw [hreg .x20 (by decide), b80005f94_x20 h₁]; rfl
      x22 := by rw [hreg .x22 (by decide), b80005f94_x22 h₁]; rfl
      x23 := by rw [hreg .x23 (by decide), b80005f94_x23 h₁]; rfl
      hdr := ⟨(hm₃ _).trans hC.symm, (hm₃ _).trans hP.symm, (hm₃ _).trans (hlen₂.trans hlen₁)⟩
      old := by
        have hb3 : bytesAt t₃ P (48 * len s) = bytesAt t₂ P (48 * len s) :=
          bytesAt_eq_iff.mpr fun i _ ↦ by simp only [byteAt_eq, hm₃]
        have hc1 : (vecCap t₁ (s.getReg .x10)).toNat = (vecCap s (s.getReg .x10)).toNat := by
          simp only [vecCap, e0]
        have hl : len s ≤ (vecCap s (s.getReg .x10)).toNat := hpre.vec.len
        rw [hb3, bytesAt_prefix hbytes (n := 48 * len s) (by rw [hc1]; omega),
          show vecPtr t₁ (s.getReg .x10) = vecPtr s (s.getReg .x10) from e8]
        refine DFrame.bytesAt_al hdm₁ hbb.1 (by omega) (by
          rcases hbb.2 with h0 | h0
          · rw [show len s = 0 by omega]; have := (vecPtr s (s.getReg .x10)).isLt; omega
          · have := hheap.hi; simp only [heapEnd] at this; omega) fun x hx h' ↦ ?_
        rcases hbb.2 with h0 | h0
        · simp only [Within] at hx; omega
        · have := hheap.hi
          addr_omega [hx, h', h0, this, hl, hb, hab] }, ?_⟩⟩
  by_cases he : itEnd s = itStart s
  · simp only [he, ↓reduceIte]
    exact b80006000_pc_taken h₃ (by
      rw [hpres₂.reg .x20, hpres₂.reg .x22, b80005f94_x20 h₁, b80005f94_x22 h₁]; exact he)
  · simp only [he, ↓reduceIte]
    exact b80006000_pc_not_taken h₃ (by
      rw [hpres₂.reg .x20, hpres₂.reg .x22, b80005f94_x20 h₁, b80005f94_x22 h₁]; exact he)

end Rv64Verifier.Layout.Extend
