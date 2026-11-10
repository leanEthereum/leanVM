import Rv64Verifier.Proofs.Walk.R20F

/-!
# `walk` R20, the outputs' claim: room for it

`AtStore.of`: `AtStore` from `AtOut` at a later state that kept the frame but for the claims'
slots, and the heap. `r20some`: `0x80003f5c`, and `grow_one` when the `Vec` is full.
-/

namespace Rv64Verifier.Proofs.Walk
open RiscvZkvm.Rv64 LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.Compile
  LeanVM.Protocol.Verifier Rv64Verifier.Runtime Rv64Verifier.Model Rv64Verifier.Transcript
  Rv64Verifier.Bus Rv64Verifier.Gkr Rv64Verifier.Model.Gkr Rv64Verifier.Blocks.F4
open Rv64Verifier.Sym (reduceReg reducePc reduceMem reduceWrites reduceObl)

section Some
variable {OI : MachineState → Word → List (List Opening) → Prop} {s u₀ w t c x y : MachineState}
  {layout : LayoutMirror.LayoutRust} {rows : List (BitVec 64)} {lir : BitVec 64}
  {bus : BusResultRust} {evs : List (List E × List E)} {P C L P' C' : Word}
  {cl : List ColumnClaim} {o : KeccakOpenings} {ks ke : Nat} {p : List E} {wd : E}

theorem AtStore.of
    (A : AtOut OI s u₀ w t c x layout rows lir bus evs P C L cl o ks ke)
    (hs : o.outputs = Option.some (p, wd))
    (Hy : CoreT OI s u₀ w t y layout lir evs P' C' L.toNat cl
      (afterKeccak layout rows lir bus cl (o, ks, ke)))
    (pc : y.pc = 0x80003f84) (room : L.toNat < C'.toNat)
    (r12 : y.getReg .x12 = x.getReg .x12) (r13 : y.getReg .x13 = x.getReg .x13)
    (r19 : y.getReg .x19 = x.getReg .x19) (r20 : y.getReg .x20 = s.getReg .x2 - 1752)
    (rr : ∀ r ∈ ([.x22, .x23, .x24, .x25, .x26] : List Reg), y.getReg r = x.getReg r)
    (gy : ∀ k : Nat, 112 ≤ k ∧ k ≤ 2648 → (k ≤ 1616 ∨ 1640 ≤ k) →
      y.getMem (s.getReg .x2 - BitVec.ofNat 64 k) = x.getMem (s.getReg .x2 - BitVec.ofNat 64 k))
    (gH : ∀ z : Word, z.toNat + 8 ≤ heapNext x → y.getMem z = x.getMem z)
    (hmono : heapNext x ≤ heapNext y)
    (bufN : P'.toNat + 56 * C'.toNat ≤ heapNext c ∨ heapNext x ≤ P'.toNat) :
    AtStore OI s u₀ w t c y layout rows lir bus evs P' C' L cl o ks ke p wd (heapNext x) := by
  have gya (a : Word) (k : Nat) (ha : a = s.getReg .x2 - BitVec.ofNat 64 k)
      (hk : 112 ≤ k ∧ k ≤ 2648) (hw : k ≤ 1616 ∨ 1640 ≤ k) : y.getMem a = x.getMem a := by
    subst ha; exact gy k hk hw
  have outs := A.outs
  rw [hs] at outs
  obtain ⟨-, hv, hw⟩ := outs
  have bufx (a : Word) {xs : List E} (h : NewVecE c x a xs) : ∀ z : Word,
      (vecPtr x a).toNat ≤ z.toNat → z.toNat + 8 ≤ (vecPtr x a).toNat + 24 * xs.length →
      y.getMem z = x.getMem z := by
    intro z h1 h2
    obtain ⟨-, Il, If⟩ := newVecE_facts h
    rw [Il] at If
    rcases If with h0 | ⟨-, q2⟩
    · omega
    exact gH z (by omega)
  have mv (a : Word) (k : Nat) (ha : a = s.getReg .x2 - BitVec.ofNat 64 k)
      (hk : 112 + 16 ≤ k ∧ k ≤ 2648) (hw : k ≤ 1616 ∨ 1640 + 16 ≤ k) {xs : List E}
      (h : NewVecE c x a xs) : NewVecE c y a xs ∧ VecBy y c a (heapNext x) := by
    have e0 := gya a k ha (by omega) (by omega)
    have e8 := gya (a + 8) (k - 8) (by rw [ha]; apply BitVec.eq_of_toNat_eq; bv_omega)
      (by omega) (by omega)
    have e16 := gya (a + 16) (k - 16) (by rw [ha]; apply BitVec.eq_of_toNat_eq; bv_omega)
      (by omega) (by omega)
    refine ⟨NewVecE.move h e0 e8 e16 hmono (bufx a h), ?_⟩
    have := vecBy_of h
    simp only [VecBy, vecLen, vecPtr] at this ⊢
    rw [e8, e16]; exact this
  obtain ⟨i1, i1N⟩ := mv _ 1728 rfl (by omega) (by omega) A.in1
  obtain ⟨i2, i2N⟩ := mv _ 904 rfl (by omega) (by omega) A.in2
  obtain ⟨ov, oN⟩ := mv _ 880 rfl (by omega) (by omega) hv
  obtain ⟨c1, c2, c3, c4, c5⟩ := A.copy
  exact {
    core := Hy
    pc := pc
    room := room
    some := hs
    x12 := by
      rw [r12, A.x12]; simp only [vecPtr]
      rw [gya _ 896 (by bv_omega) (by omega) (by omega)]
    x13 := by
      rw [r13, A.x13]; simp only [vecLen]
      rw [gya _ 888 (by bv_omega) (by omega) (by omega)]
    x19 := by rw [r19, A.x19, gya (s.getReg .x2 - 880) 880 rfl (by omega) (by omega)]
    x20 := r20
    x22 := by rw [rr .x22 (by decide), A.x22]
    x23 := by rw [rr .x23 (by decide), A.x23]
    x24 := by rw [rr .x24 (by decide), A.x24]
    x25 := by rw [rr .x25 (by decide), A.x25]
    x26 := by rw [rr .x26 (by decide), A.x26]
    before := A.before.1
    bufN := bufN
    heapN := hmono
    in1 := i1
    in2 := i2
    outv := ov
    outw := by
      rw [← hw, show s.getReg .x2 - 880 + 24 = s.getReg .x2 - 856 by bv_omega]
      exact eAt_congr (gya _ 856 rfl (by omega) (by omega))
        (gya _ 848 (by bv_omega) (by omega) (by omega)) (gya _ 840 (by bv_omega) (by omega) (by omega))
    in1N := i1N
    in2N := i2N
    outN := oN
    copy := by
      rw [gya (s.getReg .x2 - 1768) 1768 rfl (by omega) (by omega),
        gya (s.getReg .x2 - 872) 872 rfl (by omega) (by omega),
        gya (s.getReg .x2 - 1760) 1760 rfl (by omega) (by omega),
        gya (s.getReg .x2 - 864) 864 rfl (by omega) (by omega),
        gya (s.getReg .x2 - 1752) 1752 rfl (by omega) (by omega),
        gya (s.getReg .x2 - 856) 856 rfl (by omega) (by omega),
        gya (s.getReg .x2 - 1744) 1744 rfl (by omega) (by omega),
        gya (s.getReg .x2 - 848) 848 rfl (by omega) (by omega),
        gya (s.getReg .x2 - 1736) 1736 rfl (by omega) (by omega),
        gya (s.getReg .x2 - 840) 840 rfl (by omega) (by omega)]
      exact ⟨c1, c2, c3, c4, c5⟩ }


set_option maxHeartbeats 1600000 in
set_option maxRecDepth 8192 in
/-- Room for the outputs' claim, `grow_one` if the `Vec` is full, or the run dies. -/
theorem r20some (hG : GrowOneFreshSpec 0x8000c0a4 56 8) (hpre : WalkPre s)
    (A : AtOut OI s u₀ w t c x layout rows lir bus evs P C L cl o ks ke)
    (hs : o.outputs = Option.some (p, wd)) :
    ∃ y, Reaches Image.code x y ∧ ((∃ P' C', AtStore OI s u₀ w t c y layout rows lir bus evs P' C'
      L cl o ks ke p wd (heapNext x)) ∨ Dead Image.code y) := by
  obtain ⟨hb1, hb2, hb3, -⟩ := bounds hpre
  have hval : ValidMemRange (s.getReg .x2 - 11392) 1424 := hpre.stack.valid
  have H := A.core
  have sp := H.rest.inv.sp
  have hpc : x.pc = 0x80003f5c := by
    rcases A.pcs with ⟨h, -⟩ | ⟨-, h⟩
    · rw [hs] at h; cases h
    · exact h
  obtain ⟨x₁, hr₁, h₁⟩ := Sym.BlockSpec.reaches b80003f5c_spec hpc (by
    rv_eval [sp]; valid_access hval [hb1])
  have m₁ := b80003f5c_mem_same h₁
  have k₁ := b80003f5c_keeps h₁
  have H₁ := H.same hpre m₁ (k₁ .x2 (by decide))
  have eC : x.getMem (x.getReg .x2 + 1024) = C := by
    rw [sp, show s.getReg .x2 - 2656 + 1024 = s.getReg .x2 - 1632 by bv_omega]; exact H.capSlot
  have x20₁ : x₁.getReg .x20 = s.getReg .x2 - 1752 := by rw [b80003f5c_x20 h₁, sp]; bv_omega
  have hLC := H.len
  by_cases hL : L = C
  swap
  · have pc₁ := b80003f5c_pc_taken h₁ (by rw [A.x25, eC]; exact hL)
    have room : L.toNat < C.toNat := by
      have : L.toNat ≠ C.toNat := fun e ↦ hL (BitVec.eq_of_toNat_eq e)
      omega
    refine ⟨x₁, hr₁, Or.inl ⟨P, C, AtStore.of A hs H₁ pc₁ room (k₁ .x12 (by decide))
      (k₁ .x13 (by decide)) (k₁ .x19 (by decide)) x20₁ (fun r hr ↦ k₁ r (by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl | rfl <;> decide))
      (fun k _ _ ↦ m₁ _) (fun z _ ↦ m₁ z) (by simp only [heapNext, m₁]; exact le_refl _)
      (Or.inl A.before.2)⟩⟩
  -- full: `grow_one`
  have pc₁ := b80003f5c_pc_not_taken h₁ (by rw [A.x25, eC]; exact hL)
  obtain ⟨x₂, hr₂, h₂⟩ := Sym.BlockSpec.reaches b80003f68_spec pc₁ (by rv_eval [])
  have m₂ := b80003f68_mem_same h₂
  have k₂ := b80003f68_keeps h₂
  have H₂ := H₁.same hpre m₂ (k₂ .x2 (by decide))
  have h10 : x₂.getReg .x10 = s.getReg .x2 - 1632 := by
    rw [b80003f68_x10 h₂, k₁ .x2 (by decide), sp]; bv_omega
  obtain ⟨v, hrv, ⟨hpcv, hp, st, P', C', Hv, hroom, hP'⟩ | hd⟩ :=
    H₂.growOneF hG hpre (by rw [hL]) (Reaches.refl x₂) (b80003f68_pc h₂) h10
  swap
  · exact ⟨v, hr₁.trans (hr₂.trans hrv), Or.inr hd⟩
  have pcv : v.pc = 0x80003f7c := by rw [hpcv, returnAddress, b80003f68_x1 h₂]; decide
  obtain ⟨y, hr₃, h₃⟩ := Sym.BlockSpec.reaches b80003f7c_spec pcv (by rv_eval [])
  have m₃ := b80003f7c_mem_same h₃
  have k₃ := b80003f7c_keeps h₃
  have Hy := Hv.same hpre m₃ (k₃ .x2 (by decide))
  have hn₂ : heapNext x₂ = heapNext x := by simp only [heapNext, m₂, m₁]
  have reg (r : Reg) (hr : r ∈ calleeSaved) (h3 : r ∈ ([.x1, .x2, .x3, .x4, .x5, .x6, .x7, .x8,
      .x9, .x10, .x11, .x14, .x15, .x16, .x17, .x18, .x19, .x20, .x21, .x22, .x23, .x24, .x25,
      .x26, .x27, .x28, .x29, .x30, .x31] : List Reg)) : y.getReg r = x₂.getReg r := by
    rw [k₃ r h3, hp r hr]
  refine ⟨y, hr₁.trans (hr₂.trans (hrv.trans hr₃)), Or.inl ⟨P', C', AtStore.of A hs Hy
    (b80003f7c_pc h₃) hroom ?_ ?_ ?_ ?_ (fun r hr ↦ ?_) (fun k hk hw ↦ ?_) (fun z hz ↦ ?_) ?_
    (Or.inr (by omega))⟩⟩
  · rw [b80003f7c_x12 h₃, hp .x18 (by decide), b80003f68_x18 h₂, k₁ .x12 (by decide)]
  · rw [b80003f7c_x13 h₃, hp .x21 (by decide), b80003f68_x21 h₂, k₁ .x13 (by decide)]
  · rw [reg .x19 (by decide) (by decide), k₂ .x19 (by decide), k₁ .x19 (by decide)]
  · rw [reg .x20 (by decide) (by decide), k₂ .x20 (by decide), x20₁]
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl <;>
      rw [reg _ (by decide) (by decide), k₂ _ (by decide), k₁ _ (by decide)]
  · rw [m₃, st.getF hpre (by addr_omega [hb1, hk]) (fun i hi hw' ↦ by
      simp only [Within] at hw'; rcases hw with hw | hw <;> addr_omega [hw', hw, hi, hb1, hk])
      (fun hf ↦ hf.elim), m₂, m₁]
  · rw [m₃, st.getH hpre (fun a ha ↦ (range_ok hpre H₂.rest (c := 1632) (k := 1632) (n := 16) rfl
      (by omega) (by omega) ha).1) (by omega), m₂, m₁]
  · have := st.mono; rw [hn₂] at this; simp only [heapNext, m₃] at this ⊢; exact this

end Some

end Rv64Verifier.Proofs.Walk
