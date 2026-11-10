import Rv64Verifier.Proofs.Bus.VbbTail18
import Rv64Verifier.Proofs.Multilinear.Contracts

/-!
# `verify_bus_balance` past the GKR loop: the index MLEs

A call of `index_mle` on a prefix of a `Vec<E>` held in registers, its result at `S - k`
(`indexCall`). From `Claims`, the two index MLEs at `S - 816` and `S - 792` and the slices
`[point[..log_bytecode], alphas]` at `S - 608`, to `concat`'s entry (`indexStage`, `Indexed`).
`restToConcat` composes the stages from `0x80006ca0` (`Scalars`) to there.
-/

namespace Rv64Verifier.Proofs.Bus.VerifyBusBalance
open RiscvZkvm.Rv64 LeanVM.Parameters LeanVM.Protocol.Verifier Rv64Verifier.Runtime
  Rv64Verifier.Model Rv64Verifier.Bus Rv64Verifier.Transcript Rv64Verifier.Blocks.F26
  Rv64Verifier.MultilinearContracts
open Rv64Verifier.Sym (reduceReg reducePc reduceMem reduceWrites reduceObl)

theorem indexCall (hI : IndexMleSpec) {s u₀ u : MachineState} (hpre : BusBalancePre s)
    (h : Inv s u) (hr : Reaches Image.code u₀ u) (hpc : u.pc = 0x80010cd4) {k : Nat}
    (h10 : u.getReg .x10 = s.getReg .x2 - BitVec.ofNat 64 k) (hk1 : 128 ≤ k) (hk2 : k ≤ 1344)
    (hk8 : k % 8 = 0) {cap ptr len n : Word} {xs : List E} (hp : NewVecR s u cap ptr len xs)
    (h11 : u.getReg .x11 = ptr) (h12 : u.getReg .x12 = n) (hn : n.toNat ≤ len.toNat) :
    ∃ v, Reaches Image.code u₀ v ∧ ((v.pc = returnAddress u ∧ Preserves u v ∧ Inv s v ∧
      StepS s u v (Within · (s.getReg .x2 - BitVec.ofNat 64 k) 24) ∧
      eAt v (s.getReg .x2 - BitVec.ofNat 64 k) = indexMleRust (xs.take n.toNat)) ∨
      Dead Image.code v) := by
  obtain ⟨hb1, -, hb3, -⟩ := bounds hpre
  obtain ⟨o1, -, o3⟩ := frameSlot (m := indexMleStack) hpre h (n := 24) (k := k) (by omega)
    hk2 hk8 (by decide)
  have hst : RtStack u indexMleStack :=
    hpre.stack.sub 1344 h.sp (by decide) (by decide) (by decide) (by decide) (by decide)
  have hsl : stackLo u indexMleStack = s.getReg .x2 - BitVec.ofNat 64 (1344 + 1184) := by
    simp only [stackLo, h.sp]; apply BitVec.eq_of_toNat_eq; addr_omega [hb1]
  have hle := hp.le
  have hb := hp.buf
  have hhi := h.heap.hi
  have hlo := hpre.heap.lo
  have hr4 := hpre.stack.rodata
  have hrb : rodataBase.toNat = 2684354560 := rfl
  rw [stackLo_eq] at hr4
  simp only [NewBuf, heapNext, heapEnd, heapStart] at hb hhi hlo
  have hpt : n.toNat = 0 ∨ (ptr.toNat % 8 = 0 ∧ 536870912 ≤ ptr.toNat ∧
      ptr.toNat + 24 * n.toNat ≤ 2013265920) := by
    rcases hb.2 with h0 | ⟨b1, b2⟩
    · exact Or.inl (by omega)
    · exact Or.inr ⟨hb.1, by omega, by omega⟩
  have pre : IndexMlePre u := {
    ret := by
      rw [h10]; exact regionRange o1 (Nat.le_refl _) (by omega) (by addr_omega [hb1, hb3, hk8, hk2])
    point := by
      rw [h11, h12]
      rcases hpt with h0 | ⟨p0, p1, p2⟩
      · rw [h0]; intro i hi; exact absurd hi (Nat.not_lt_zero _)
      · exact heapRange p0 (by simp only [heapStart]; omega) (by simp only [heapEnd]; omega)
    stack := hst.toStackOk
    retPoint := by
      rw [h10, h11, h12]
      rcases hpt with h0 | ⟨p0, p1, p2⟩
      · simp only [Apart]; exact Or.inr (Or.inl (by omega))
      · addr_omega [hb1, p1, p2, hk2]
    retStack := h10 ▸ o3
    pointStack := by
      rw [h11, h12, hsl]
      rcases hpt with h0 | ⟨p0, p1, p2⟩
      · simp only [Apart]; exact Or.inl (by omega)
      · addr_omega [hb1, p1, p2]
    rodata := h.rodata hpre
    stackRodata := by rw [hsl]; addr_omega [hr4, hrb, hb1] }
  obtain ⟨v, hrv, ⟨hpcv, hpv, post⟩ | hd⟩ := hI.call hr hpc pre
  swap
  · exact ⟨v, hrv, Or.inr hd⟩
  have hx := hpre.stack.next
  rw [stackLo_eq] at hx
  have fr : DFrame u v fun a ↦ Within a (s.getReg .x2 - BitVec.ofNat 64 k) 24 ∨
      Within a (s.getReg .x2 - 4544) 3200 := fun a ha ↦ by
    have h0 := ha 0 (by decide)
    rw [add_ofNat_zero] at h0
    refine post.frame a (fun hw ↦ h0 (Or.inl (by rw [← h10]; exact hw))) (fun hw ↦ h0 (Or.inr ?_))
    rw [hsl] at hw; addr_omega [hw, hb1]
  have hn' : heapNext v = heapNext u := by
    simp only [heapNext]
    exact congrArg BitVec.toNat (fr nextAddr fun i hi hw ↦ by
      rcases hw with hw | hw <;> addr_omega [hw, hi, hx, hb1, hk2])
  have st : StepS s u v (Within · (s.getReg .x2 - BitVec.ofNat 64 k) 24) :=
    ⟨fr.mono fun a ha ↦ by
      rcases ha with ha | ha
      · exact Or.inl ha
      · exact Or.inr (Or.inl ha),
      ⟨hn' ▸ h.heap.lo, hn' ▸ h.heap.hi⟩, hn'.ge, hpv .x2 (by decide)⟩
  have hval := post.value
  rw [h10, h11, h12, eListAt_take _ _ hn, hp.elems] at hval
  refine ⟨v, hrv, Or.inl ⟨hpcv, hpv, h.afterR hpre (frameW_slot hpre (by omega) hk2) st.toR, st,
    hval⟩⟩

/-- At `concat`'s entry (`0x8000cfc4`, its result at `S - 768`): the index MLEs of
`point[..log_memory]` and `point[..log_bytecode]` at `S - 816` and `S - 792`, the two slices at
`S - 608`. -/
structure Indexed (bev : MachineState → Word → List E → Option E) (s v : MachineState) (k : Start)
    (state : GkrState) (mem : List E) (mf bf : E) : Prop where
  inv : Inv s v
  kept : Kept s v k
  claims : ClaimsOk s v (v.getMem (s.getReg .x2 - 840)) (v.getMem (s.getReg .x2 - 832))
    (v.getMem (s.getReg .x2 - 824)) (allClaims s state mem mf bf)
  len : v.getMem (s.getReg .x2 - 824) = 5
  x1 : v.getReg .x1 = 0x800070b0
  x10 : v.getReg .x10 = s.getReg .x2 - 768
  x11 : v.getReg .x11 = s.getReg .x2 - 608
  x12 : v.getReg .x12 = 2
  x20 : v.getReg .x20 = s.getReg .x12
  x21 : v.getReg .x21 = s.getReg .x10
  x23 : v.getReg .x23 = logBc s
  x24 : v.getReg .x24 = logMem s
  x27 : v.getReg .x27 = v.getMem (s.getReg .x2 - 1256)
  x8 : v.getReg .x8 = v.getMem (s.getReg .x2 - 1128)
  memLen : 3 ≤ mem.length
  slice0 : v.getMem (s.getReg .x2 - 608) = v.getMem (s.getReg .x2 - 1256)
  slice0Len : v.getMem (s.getReg .x2 - 600) = logBc s
  slice1 : v.getMem (s.getReg .x2 - 592) = vecPtr v (s.getReg .x2 - 912)
  slice1Len : v.getMem (s.getReg .x2 - 584) = vecLen v (s.getReg .x2 - 912)
  memIndex : eAt v (s.getReg .x2 - 816) = indexMleRust (state.point.take (logMem s).toNat)
  bcIndex : eAt v (s.getReg .x2 - 792) = indexMleRust (state.point.take (logBc s).toNat)
  memory : NewVecE s v (s.getReg .x2 - 864) mem
  values : NewVecE s v (s.getReg .x2 - 176) state.values
  point : NewVecR s v (v.getMem (s.getReg .x2 - 1320)) (v.getMem (s.getReg .x2 - 1256))
    (v.getMem (s.getReg .x2 - 1144)) state.point
  valuesPtr : v.getMem (s.getReg .x2 - 1280) = vecPtr v (s.getReg .x2 - 176)
  pushPtr : v.getMem (s.getReg .x2 - 1272) = vecPtr s (s.getReg .x11 + 24)
  lm : (logMem s).toNat ≤ state.point.length
  lb : (logBc s).toNat ≤ state.point.length
  mfEq : mf = eOf3 (v.getReg .x25) (v.getReg .x22) (v.getMem (s.getReg .x2 - 1112))
  bfEq : bf = eOf3 (v.getReg .x26) (v.getMem (s.getReg .x2 - 1120))
    (v.getMem (s.getReg .x2 - 1128))
  tracks : Tracks (prog bev s) (s.getReg .x12) s v (rest bev s k state mem mf bf)

theorem indexStage (hI : IndexMleSpec) {bev : MachineState → Word → List E → Option E}
    {s t : MachineState} {k : Start} {state : GkrState} {mem : List E} {mf bf : E}
    (hpre : BusBalancePre s) (C : Claims bev s t k state mem mf bf) (hpc : t.pc = 0x80010cd4) :
    ∃ v, Reaches Image.code t v ∧ (Dead Image.code v ∨
      (v.pc = 0x8000cfc4 ∧ Indexed bev s v k state mem mf bf)) := by
  obtain ⟨hb1, -, -, -⟩ := bounds hpre
  have hval : ValidMemRange (s.getReg .x2 - 4544) 568 := hpre.stack.valid
  have hlen : state.point.length = (t.getMem (s.getReg .x2 - 1144)).toNat := by
    rw [← C.point.elems, eListAt_length]
  obtain ⟨v₁, hr₁, ⟨hpc₁, hp₁, I₁, st₁, mi⟩ | hd⟩ := indexCall hI hpre C.inv (Reaches.refl t) hpc
    (k := 816) C.x10 (by omega) (by omega) (by omega) C.point C.x11 C.x12
    (by rw [← hlen]; exact C.lm)
  swap
  · exact ⟨v₁, hr₁, Or.inl hd⟩
  have hpc₁' : v₁.pc = 0x80007070 := by rw [hpc₁, returnAddress_eq, C.x1]; decide
  obtain ⟨u₂, hr₂, h₂⟩ := Sym.BlockSpec.reaches b80007070_spec hpc₁' trivial
  have k₂ := b80007070_keeps h₂
  have m₂ := b80007070_mem_same h₂
  have I₂ := I₁.same m₂ (k₂ .x2 (by decide))
  have f816 : FrameW s (Within · (s.getReg .x2 - BitVec.ofNat 64 816) 24) :=
    frameW_slot hpre (by omega) (by omega)
  have st₁₂ : StepS s t u₂ (Within · (s.getReg .x2 - BitVec.ofNat 64 816) 24) :=
    (st₁.trans (StepS.same m₂ I₁.heap (k₂ .x2 (by decide)))).weaken fun a ha ↦ by
      rcases ha with ha | ha
      · exact ha
      · exact False.elim ha
  have r₁ (r : Reg) (hr : r ∈ calleeSaved) : v₁.getReg r = t.getReg r := hp₁ r hr
  obtain ⟨v₂, hr₃, ⟨hpc₂, hp₂, I₃, st₃, bi⟩ | hd⟩ := indexCall hI hpre I₂ (Reaches.refl u₂)
    (b80007070_pc h₂) (k := 792)
    (by rw [b80007070_x10 h₂, I₁.sp]; apply BitVec.eq_of_toNat_eq
        addr_omega [hb1])
    (by omega) (by omega) (by omega) (C.point.keepR hpre st₁₂.toR f816)
    (by rw [b80007070_x11 h₂, r₁ .x27 (by decide), C.x27])
    (by rw [b80007070_x12 h₂, r₁ .x23 (by decide), C.x23])
    (by rw [← hlen]; exact C.lb)
  swap
  · exact ⟨v₂, hr₁.trans (hr₂.trans hr₃), Or.inl hd⟩
  have hpc₂' : v₂.pc = 0x80007084 := by rw [hpc₂, returnAddress_eq, b80007070_x1 h₂]; decide
  have sp₂ : v₂.getReg .x2 = s.getReg .x2 - 1344 := I₃.sp
  obtain ⟨v, hr₄, h₄⟩ := Sym.BlockSpec.reaches b80007084_spec hpc₂' (by
    rv_eval [sp₂]
    and_intros <;> valid_access hval [hb1])
  have k₄ := b80007084_keeps h₄
  have fr₄ : DFrame v₂ v (Within · (s.getReg .x2 - 608) 32) :=
    (DFrame.of_memFrame (b80007084_frame h₄ (by rw [sp₂]; addr_omega [hb1]))).mono
      fun a ha ↦ by rw [sp₂] at ha; addr_omega [ha, hb1]
  have st₄ : StepS s v₂ v (Within · (s.getReg .x2 - 608) 32) :=
    StepS.ofDFrame I₃.heap fr₄ (fun _ h ↦ h) (fun i hi hw ↦ by addr_omega [hw, hi, hb1])
      (k₄ .x2 (by decide))
  have I₄ := I₃.afterR hpre (fun a ha ↦ by addr_omega [ha, hb1]) st₄.toR
  have st : StepS s t v fun a ↦ Within a (s.getReg .x2 - 816) 48 ∨
      Within a (s.getReg .x2 - 608) 32 :=
    ((st₁₂.trans st₃).trans st₄).weaken fun a ha ↦ by
      rcases ha with (ha | ha) | ha
      · exact Or.inl (by addr_omega [ha, hb1])
      · exact Or.inl (by addr_omega [ha, hb1])
      · exact Or.inr ha
  have fT : FrameW s fun a ↦ Within a (s.getReg .x2 - 816) 48 ∨
      Within a (s.getReg .x2 - 608) 32 := fun a ha ↦ by
    rcases ha with ha | ha <;> addr_omega [ha, hb1]
  have kT (x : Word) (hx : (s.getReg .x2 - 1344).toNat ≤ x.toNat ∧
      x.toNat + 8 ≤ (s.getReg .x2 - 816).toNat ∨ (s.getReg .x2 - 768).toNat ≤ x.toNat ∧
      x.toNat + 8 ≤ (s.getReg .x2 - 608).toNat ∨ (s.getReg .x2 - 576).toNat ≤ x.toNat ∧
      x.toNat + 8 ≤ (s.getReg .x2).toNat) : v.getMem x = t.getMem x :=
    st.slot hpre (fun z hz h' ↦ by
      rcases hx with hx | hx | hx <;> rcases h' with h' | h' <;> addr_omega [hz, h', hx, hb1])
      (by rcases hx with hx | hx | hx <;> constructor <;> addr_omega [hb1, hx])
  have K1 (x : Word) (hx : (s.getReg .x2 - 1344).toNat ≤ x.toNat ∧
      x.toNat + 8 ≤ (s.getReg .x2 - 816).toNat) : v.getMem x = t.getMem x := kT x (Or.inl hx)
  have rg (r : Reg) (hr : r ∈ ([.x8, .x20, .x21, .x22, .x23, .x24, .x25, .x26, .x27] : List Reg)) :
      v.getReg r = t.getReg r := by
    rw [k₄ r (mem_of_mem hr _), hp₂ r (by unfold calleeSaved; exact mem_of_mem hr _),
      k₂ r (mem_of_mem hr _), r₁ r (by unfold calleeSaved; exact mem_of_mem hr _)]
  have b736 := b80007084_m_x2_736 h₄
  have b744 := b80007084_m_x2_744 h₄
  have b752 := b80007084_m_x2_752 h₄
  have b760 := b80007084_m_x2_760 h₄
  rw [sp₂] at b736 b744 b752 b760
  have e (j : Nat) (hj : j ≤ 1344) : s.getReg .x2 - 1344 + BitVec.ofNat 64 j =
      s.getReg .x2 - BitVec.ofNat 64 (1344 - j) := by
    apply BitVec.eq_of_toNat_eq; addr_omega [hb1, hj]
  have w2 (x : Word) (hx : (s.getReg .x2 - 1344).toNat ≤ x.toNat ∧
      x.toNat + 8 ≤ (s.getReg .x2 - 608).toNat) : v.getMem x = v₂.getMem x :=
    st₄.slot hpre (fun z hz h' ↦ by addr_omega [hz, h', hx, hb1])
      (by constructor <;> addr_omega [hb1, hx])
  refine ⟨v, hr₁.trans (hr₂.trans (hr₃.trans hr₄)), Or.inr ⟨b80007084_pc h₄, {
    inv := I₄
    kept := C.kept.step hpre (st.toR.weaken fun a ha ↦ by
      rcases ha with ha | ha
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (by addr_omega [ha, hb1]))))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (by addr_omega [ha, hb1])))))))
    claims := by
      rw [K1 _ (by constructor <;> addr_omega [hb1]), K1 _ (by constructor <;> addr_omega [hb1]),
        K1 _ (by constructor <;> addr_omega [hb1])]
      exact C.claims.keepR hpre st.toR fT
    len := by rw [K1 _ (by constructor <;> addr_omega [hb1])]; exact C.len
    x1 := b80007084_x1 h₄
    x10 := by
      rw [b80007084_x10 h₄, sp₂]; apply BitVec.eq_of_toNat_eq; addr_omega [hb1]
    x11 := by
      rw [b80007084_x11 h₄, sp₂]; apply BitVec.eq_of_toNat_eq; addr_omega [hb1]
    x12 := b80007084_x12 h₄
    x20 := by rw [rg .x20 (by decide)]; exact C.x20
    x21 := by rw [rg .x21 (by decide)]; exact C.x21
    x23 := by rw [rg .x23 (by decide)]; exact C.x23
    x24 := by rw [rg .x24 (by decide)]; exact C.x24
    x27 := by rw [rg .x27 (by decide), K1 _ (by constructor <;> addr_omega [hb1])]; exact C.x27
    x8 := by rw [rg .x8 (by decide), K1 _ (by constructor <;> addr_omega [hb1])]; exact C.x8
    memLen := C.memLen
    slice0 := by
      rw [show s.getReg .x2 - 608 = s.getReg .x2 - 1344 + 736 by
        apply BitVec.eq_of_toNat_eq; addr_omega [hb1], b736, K1 _ (by constructor <;> addr_omega [hb1]),
        hp₂ .x27 (by decide), k₂ .x27 (by decide), r₁ .x27 (by decide)]
      exact C.x27
    slice0Len := by
      rw [show s.getReg .x2 - 600 = s.getReg .x2 - 1344 + 744 by
        apply BitVec.eq_of_toNat_eq; addr_omega [hb1], b744, hp₂ .x23 (by decide), k₂ .x23 (by decide),
        r₁ .x23 (by decide)]
      exact C.x23
    slice1 := by
      rw [show s.getReg .x2 - 592 = s.getReg .x2 - 1344 + 752 by
        apply BitVec.eq_of_toNat_eq; addr_omega [hb1], b752, vecPtr,
        w2 _ (by constructor <;> addr_omega [hb1])]
      exact congrArg v₂.getMem (by apply BitVec.eq_of_toNat_eq; addr_omega [hb1])
    slice1Len := by
      rw [show s.getReg .x2 - 584 = s.getReg .x2 - 1344 + 760 by
        apply BitVec.eq_of_toNat_eq; addr_omega [hb1], b760, vecLen,
        w2 _ (by constructor <;> addr_omega [hb1])]
      exact congrArg v₂.getMem (by apply BitVec.eq_of_toNat_eq; addr_omega [hb1])
    memIndex := by
      rw [st₄.eSlot hpre (x := s.getReg .x2 - 816) (fun z hz h' ↦ by addr_omega [hz, h', hb1])
          (by constructor <;> addr_omega [hb1]),
        st₃.eSlot hpre (x := s.getReg .x2 - 816) (fun z hz h' ↦ by addr_omega [hz, h', hb1])
          (by constructor <;> addr_omega [hb1])]
      show eAt u₂ (s.getReg .x2 - BitVec.ofNat 64 816) = _
      rw [← mi]
      unfold eAt
      simp only [m₂]
    bcIndex := by
      rw [← bi]
      exact st₄.eSlot hpre (fun z hz h' ↦ by addr_omega [hz, h', hb1])
        (by constructor <;> addr_omega [hb1])
    memory := C.memory.keepR hpre st.toR fT (by addr_omega [hb1]) fun z hz h' ↦ by
      rcases h' with h' | h' <;> addr_omega [hz, h', hb1]
    values := C.values.keepR hpre st.toR fT (by addr_omega [hb1]) fun z hz h' ↦ by
      rcases h' with h' | h' <;> addr_omega [hz, h', hb1]
    point := by
      rw [K1 _ (by constructor <;> addr_omega [hb1]), K1 _ (by constructor <;> addr_omega [hb1]),
        K1 _ (by constructor <;> addr_omega [hb1])]
      exact C.point.keepR hpre st.toR fT
    valuesPtr := by
      rw [K1 _ (by constructor <;> addr_omega [hb1]), C.valuesPtr, vecPtr, vecPtr,
        kT _ (Or.inr (Or.inr (by constructor <;> addr_omega [hb1])))]
    pushPtr := by rw [K1 _ (by constructor <;> addr_omega [hb1])]; exact C.pushPtr
    lm := C.lm
    lb := C.lb
    mfEq := by
      rw [rg .x25 (by decide), rg .x22 (by decide), K1 _ (by constructor <;> addr_omega [hb1])]
      exact C.mfEq
    bfEq := by
      rw [rg .x26 (by decide), K1 _ (by constructor <;> addr_omega [hb1]),
        K1 _ (by constructor <;> addr_omega [hb1])]
      exact C.bfEq
    tracks := C.tracks.keep fun T hT ↦ st.transcript hpre C.inv fT hT }⟩⟩

/-- From `0x80006ca0` to `concat`'s entry. -/
theorem restToConcat (hT : TryAllocZeroedSpec) (hM : MemcpySpec 0x800126e4) (hA : AllocSpec)
    (hG : GrowOneFreshSpec 0x8000c0a4 56 8) (hI : IndexMleSpec)
    {bev : MachineState → Word → List E → Option E} {s q : MachineState} {k : Start}
    {state : GkrState} {mem : List E} {mf bf : E} (hpre : BusBalancePre s)
    (Sc : Scalars bev s q k state mem mf bf) (hpc : q.pc = 0x80006ca0) :
    ∃ v, Reaches Image.code q v ∧ (Dead Image.code v ∨
      (v.pc = 0x8000cfc4 ∧ Indexed bev s v k state mem mf bf)) := by
  obtain ⟨y, hry, hd | ⟨hpcy, P⟩⟩ := pointsStage hT hM hpre Sc hpc
  · exact ⟨y, hry, Or.inl hd⟩
  obtain ⟨t, hrt, hd | ⟨hpct, C⟩⟩ := claimsStage hA hT hM hG hpre P hpcy
  · exact ⟨t, hry.trans hrt, Or.inl hd⟩
  obtain ⟨v, hrv, hd | ⟨hpcv, X⟩⟩ := indexStage hI hpre C hpct
  · exact ⟨v, hry.trans (hrt.trans hrv), Or.inl hd⟩
  exact ⟨v, hry.trans (hrt.trans hrv), Or.inr ⟨hpcv, X⟩⟩

end Rv64Verifier.Proofs.Bus.VerifyBusBalance
