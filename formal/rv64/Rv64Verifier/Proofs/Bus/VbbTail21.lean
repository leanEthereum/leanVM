import Rv64Verifier.Proofs.Bus.VbbTail20

/-!
# `verify_bus_balance` past the GKR loop: `final_pc` and the framework fingerprints

From `0x80007170` (`Evaluated`): the closure's captures at `S - 720`, `GEN` at `S - 248`,
`final_pc = GEN.pow(2^log_bytecode - 1)` into `S - 608` (`powStep`); the push side's
fingerprints `fingerprints(ONE, ONE, ONE)` into `S - 656` (`fps1Step`); `memory_final` and
`bytecode_final` at `S - 584` and `S - 560`, the pull side's `fingerprints(final_pc,
memory_final, bytecode_final)` into `S - 680` (`fps2Step`). Every write lies in `FpW`.
-/

namespace Rv64Verifier.Proofs.Bus.VerifyBusBalance
open RiscvZkvm.Rv64 LeanVM.Parameters LeanVM.Protocol.Verifier Rv64Verifier.Runtime
  Rv64Verifier.Model Rv64Verifier.Bus Rv64Verifier.Transcript Rv64Verifier.Blocks.F26
  Rv64Verifier.MultilinearContracts Rv64Verifier.FieldContracts
open Rv64Verifier.Sym (reduceReg reducePc reduceMem reduceWrites reduceObl)

/-! ## What a callee below the frame reads -/

/-- A frame slot, read by a callee with an `m`-byte stack below the frame. -/
theorem heldSlot {s v : MachineState} (hpre : BusBalancePre s) (h : Inv s v) {k n m : Nat}
    (hk1 : 104 + n ≤ k) (hk2 : k ≤ 1344) (hk8 : k % 8 = 0) (hn8 : n % 8 = 0)
    (hm : 1344 + m ≤ 4544) : Held v m (s.getReg .x2 - BitVec.ofNat 64 k) n := by
  obtain ⟨o1, o2, o3⟩ := frameSlot (m := m) hpre h (n := n) hk1 hk2 hk8 hm
  exact ⟨regionRange o1 (Nat.le_refl _) (by omega) o1.2, o2, o3⟩

/-- A nonempty `Vec<E>`'s elements, allocated since the entry, read by such a callee. -/
theorem heldVec {s v : MachineState} (hpre : BusBalancePre s) (h : Inv s v) {a : Word}
    {xs : List E} (hv : NewVecE s v a xs) (hl : 0 < xs.length) {m : Nat} (hm : 1344 + m ≤ 4544) :
    Held v m (vecPtr v a) (24 * (vecLen v a).toNat) := by
  have hlen := hv.length
  rcases bufPart hpre h hv.buf hv.vec.len (m := m) hm (k := 0) (l := 0) (by omega) with
    h0 | ⟨R, O, A1, -⟩
  · omega
  · exact ⟨regionRange R (Nat.le_refl _) (by omega) R.2, O, A1⟩

/-- `!(!0 << n) = (1 << n) - 1`. -/
theorem notShift_eq (n : Nat) (hn : n < 64) :
    (0xffffffffffffffff : Word) * BitVec.ofNat 64 (2 ^ n) ^^^ 0xffffffffffffffff =
      (1#64 <<< n) - 1#64 := by
  apply BitVec.eq_of_toNat_eq
  have hp : 2 ^ n ≤ 2 ^ 63 := Nat.pow_le_pow_right (by decide) (by omega)
  have hp1 : 1 ≤ 2 ^ n := Nat.one_le_two_pow
  simp only [show (0xffffffffffffffff : Word) = BitVec.allOnes 64 from rfl, BitVec.xor_allOnes,
    BitVec.toNat_not, BitVec.toNat_mul, BitVec.toNat_allOnes, BitVec.toNat_ofNat,
    BitVec.toNat_sub, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]
  generalize 2 ^ n = K at hp hp1 ⊢
  omega

/-! ## `final_pc` -/

/-- What the steps from `0x80007170` to `alloc`'s entry write in the frame. -/
def FpW (s : MachineState) (a : Word) : Prop :=
  Within a (s.getReg .x2 - 720) 496 ∨ Within a (s.getReg .x2 - 248) 72

theorem FpW.frameW {s : MachineState} (hpre : BusBalancePre s) : FrameW s (FpW s) := by
  obtain ⟨hb1, -, -, -⟩ := bounds hpre
  intro a ha
  rcases ha with ha | ha <;> addr_omega [ha, hb1]

theorem FpW.free {s : MachineState} (hpre : BusBalancePre s) {a : Word} (ha : FpW s a) :
    Free s a := by
  obtain ⟨hb1, -, -, -⟩ := bounds hpre
  refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ?_)))))
  rcases ha with ha | ha <;> addr_omega [ha, hb1]

/-- `fingerprints`' captures, at `S - 720`. -/
structure Env (s t : MachineState) : Prop where
  w0 : t.getMem (s.getReg .x2 - 720) = s.getReg .x2 - 888
  w1 : t.getMem (s.getReg .x2 - 712) = s.getReg .x2 - 816
  w2 : t.getMem (s.getReg .x2 - 704) = s.getReg .x2 - 864
  w3 : t.getMem (s.getReg .x2 - 696) = s.getReg .x2 - 792
  w4 : t.getMem (s.getReg .x2 - 688) = s.getReg .x2 - 744

theorem powStep (hP : PowSpec) {bev : MachineState → Word → List E → Option E}
    {s y : MachineState} {k : Start} {state : GkrState} {mem : List E} {mf bf bv : E}
    (hpre : BusBalancePre s) (E : Evaluated bev s y k state mem mf bf bv)
    (hpc : y.pc = 0x80007170) :
    ∃ t, Reaches Image.code y t ∧ (Dead Image.code t ∨ (t.pc = 0x800071c4 ∧ Inv s t ∧
      StepS s y t (FpW s) ∧ (∀ r ∈ calleeSaved, t.getReg r = y.getReg r) ∧
      eAt t (s.getReg .x2 - 608) = gpowRust ((1#64 <<< ((logBc s).toNat % 64)) - 1#64) ∧
      Env s t)) := by
  obtain ⟨hb1, -, -, -⟩ := bounds hpre
  have hval : ValidMemRange (s.getReg .x2 - 4544) 568 := hpre.stack.valid
  have sp := E.inv.sp
  obtain ⟨u, hr, h₁⟩ := Sym.BlockSpec.reaches b80007170_spec hpc (by
    rv_eval [sp]
    and_intros <;> valid_access hval [hb1])
  have k₁ := b80007170_keeps h₁
  have x12 : u.getReg .x12 = (0xffffffffffffffff : Word) *
      BitVec.ofNat 64 (2 ^ ((y.getReg .x23).toNat % 64)) ^^^ 0xffffffffffffffff :=
    h₁.reg_eq .x12 rfl (by rv_eval [])
  have fr₁ : DFrame y u (Within · (s.getReg .x2 - 720) 496) :=
    (DFrame.of_memFrame (b80007170_frame h₁ (by rw [sp]; addr_omega [hb1]))).mono
      fun a ha ↦ by rw [sp] at ha; addr_omega [ha, hb1]
  have st₁ : StepS s y u (FpW s) :=
    StepS.ofDFrame E.inv.heap fr₁ (fun a ha ↦ Or.inl ha) (fun i hi hw ↦ by addr_omega [hw, hi, hb1])
      (k₁ .x2 (by decide))
  have I₁ := E.inv.afterR hpre (FpW.frameW hpre) st₁.toR
  have sp₁ : u.getReg .x2 = s.getReg .x2 - 1344 := I₁.sp
  have hst : RtStack u powStack :=
    hpre.stack.sub 1344 sp₁ (by decide) (by decide) (by decide) (by decide) (by decide)
  have hsl : stackLo u powStack = s.getReg .x2 - BitVec.ofNat 64 (1344 + 1104) := by
    simp only [stackLo, sp₁]; apply BitVec.eq_of_toNat_eq; addr_omega [hb1]
  have hr4 := hst.rodata
  have hrb : rodataBase.toNat = 2684354560 := rfl
  have x10 : u.getReg .x10 = s.getReg .x2 - 608 := by
    rw [b80007170_x10 h₁, sp]; apply BitVec.eq_of_toNat_eq; addr_omega [hb1]
  have x11 : u.getReg .x11 = s.getReg .x2 - 248 := by
    rw [b80007170_x11 h₁, sp]; apply BitVec.eq_of_toNat_eq; addr_omega [hb1]
  have pre : PowPre u := {
    out := by rw [x10]; valid_sub hval [hb1]
    base := by rw [x11]; valid_sub hval [hb1]
    stack := hst.toStackOk
    pool := poolOk_of_rodata (I₁.rodata hpre) (by addr_omega [hr4, hrb])
    outBase := by rw [x10, x11]; addr_omega [hb1]
    outStack := by rw [x10, hsl]; addr_omega [hb1]
    baseStack := by rw [x11, hsl]; addr_omega [hb1]
    basePool := by rw [x11]; simp only [poolAddr]; addr_omega [hb1] }
  obtain ⟨t, hrt, ⟨hpct, hpt, post⟩ | hd⟩ := hP.call (Reaches.refl u) (b80007170_pc h₁) pre
  swap
  · exact ⟨t, hr.trans hrt, Or.inl hd⟩
  have hx := hpre.stack.next
  rw [stackLo_eq] at hx
  have frt : DFrame u t fun a ↦ Within a (s.getReg .x2 - 608) 24 ∨
      Within a (s.getReg .x2 - 248) 24 ∨ Within a (s.getReg .x2 - 4544) 3200 := fun a ha ↦ by
    have h0 := ha 0 (by decide)
    rw [add_ofNat_zero] at h0
    exact post.frame a (fun hw ↦ h0 (Or.inl (by rw [x10] at hw; exact hw)))
      (fun hw ↦ h0 (Or.inr (Or.inl (by rw [x11] at hw; exact hw))))
      (fun hw ↦ h0 (Or.inr (Or.inr (by rw [hsl] at hw; addr_omega [hw, hb1]))))
  have hn : heapNext t = heapNext u := by
    simp only [heapNext]
    exact congrArg BitVec.toNat (frt nextAddr fun i hi hw ↦ by
      rcases hw with hw | hw | hw <;> addr_omega [hw, hi, hx, hb1])
  have stt : StepS s u t (FpW s) :=
    ⟨frt.mono fun a ha ↦ by
      rcases ha with ha | ha | ha
      · exact Or.inl (Or.inl (by addr_omega [ha, hb1]))
      · exact Or.inl (Or.inr (by addr_omega [ha, hb1]))
      · exact Or.inr (Or.inl ha),
      ⟨hn ▸ I₁.heap.lo, hn ▸ I₁.heap.hi⟩, hn.ge, hpt .x2 (by decide)⟩
  have It := I₁.afterR hpre (FpW.frameW hpre) stt.toR
  have st := (st₁.trans stt).weaken fun a ha ↦ by rcases ha with ha | ha <;> exact ha
  have wt (j : Nat) (hj : 624 ≤ j) (hj2 : j + 8 ≤ 736) : t.getMem (s.getReg .x2 - 1344 +
      BitVec.ofNat 64 j) = u.getMem (s.getReg .x2 - 1344 + BitVec.ofNat 64 j) :=
    frt _ fun i hi hw ↦ by rcases hw with hw | hw | hw <;> addr_omega [hw, hi, hb1, hj, hj2]
  have env (j : Nat) (hj : 624 ≤ j) (hj2 : j + 8 ≤ 736) (c : Word) (hc : u.getMem
      (y.getReg .x2 + BitVec.ofNat 64 j) = c) : t.getMem (s.getReg .x2 - BitVec.ofNat 64 (1344 - j)) = c := by
    rw [show s.getReg .x2 - BitVec.ofNat 64 (1344 - j) = s.getReg .x2 - 1344 + BitVec.ofNat 64 j by
      apply BitVec.eq_of_toNat_eq; addr_omega [hb1, hj2], wt j hj hj2, ← sp]
    exact hc
  have e2 : eAt u (s.getReg .x2 - 248) = genRust := by
    have a0 := b80007170_m_x2_1096 h₁
    have a1 := b80007170_m_x2_1104 h₁
    have a2 := b80007170_m_x2_1112 h₁
    rw [sp] at a0 a1 a2
    refine eAt_const ?_ ?_ ?_
    · exact (congrArg u.getMem (by apply BitVec.eq_of_toNat_eq; addr_omega [hb1])).trans a0
    · exact (congrArg u.getMem (by apply BitVec.eq_of_toNat_eq; addr_omega [hb1])).trans a1
    · exact (congrArg u.getMem (by apply BitVec.eq_of_toNat_eq; addr_omega [hb1])).trans a2
  have hv := post.value
  rw [x10, x11, e2, x12, E.x23,
    notShift_eq _ (Nat.mod_lt _ (by decide))] at hv
  refine ⟨t, hr.trans hrt, Or.inr ⟨by rw [hpct, returnAddress_eq, b80007170_x1 h₁]; decide, It, st,
    fun r hr' ↦ by rw [hpt r hr', k₁ r (by unfold calleeSaved at hr'; exact mem_of_mem hr' _)],
    hv, ⟨?_, ?_, ?_, ?_, ?_⟩⟩⟩
  · refine (env 624 (by omega) (by omega) _ (b80007170_m_x2_624 h₁)).trans ?_
    rw [sp]; apply BitVec.eq_of_toNat_eq; addr_omega [hb1]
  · refine (env 632 (by omega) (by omega) _ (b80007170_m_x2_632 h₁)).trans ?_
    rw [sp]; apply BitVec.eq_of_toNat_eq; addr_omega [hb1]
  · refine (env 640 (by omega) (by omega) _ (b80007170_m_x2_640 h₁)).trans ?_
    rw [sp]; apply BitVec.eq_of_toNat_eq; addr_omega [hb1]
  · refine (env 648 (by omega) (by omega) _ (b80007170_m_x2_648 h₁)).trans ?_
    rw [sp]; apply BitVec.eq_of_toNat_eq; addr_omega [hb1]
  · refine (env 656 (by omega) (by omega) _ (b80007170_m_x2_656 h₁)).trans ?_
    rw [sp]; apply BitVec.eq_of_toNat_eq; addr_omega [hb1]

/-! ## `fingerprints` -/

theorem weightsLen (k : Start) : (eqKernelRust k.alphas).length = 16 := by
  rw [eqKernelRust_eq, eqKernel_length, k.alphasLen]; rfl

/-- A call of the `fingerprints` closure, its result at `S - ko`, its captures at `S - 720`, its
arguments at `S - kp`, `S - kc`, `S - kb`. -/
theorem fpsCall (hF : FingerprintsSpec) {s u₀ u : MachineState} {k : Start} {mem : List E}
    (hpre : BusBalancePre s) (h : Inv s u) (K : Kept s u k) (hr : Reaches Image.code u₀ u)
    (hpc : u.pc = 0x8001174c) {ko kp kc kb : Nat}
    (h10 : u.getReg .x10 = s.getReg .x2 - BitVec.ofNat 64 ko) (hko1 : 128 ≤ ko) (hko2 : ko ≤ 1344)
    (hko8 : ko % 8 = 0) (h11 : u.getReg .x11 = s.getReg .x2 - 720) (env : Env s u)
    (hmem : NewVecE s u (s.getReg .x2 - 864) mem) (hml : 3 ≤ mem.length)
    (h12 : u.getReg .x12 = s.getReg .x2 - BitVec.ofNat 64 kp) (hkp1 : 128 ≤ kp) (hkp2 : kp ≤ 1344)
    (hkp8 : kp % 8 = 0)
    (h13 : u.getReg .x13 = s.getReg .x2 - BitVec.ofNat 64 kc) (hkc1 : 128 ≤ kc) (hkc2 : kc ≤ 1344)
    (hkc8 : kc % 8 = 0)
    (h14 : u.getReg .x14 = s.getReg .x2 - BitVec.ofNat 64 kb) (hkb1 : 128 ≤ kb) (hkb2 : kb ≤ 1344)
    (hkb8 : kb % 8 = 0) :
    ∃ v, Reaches Image.code u₀ v ∧ ((v.pc = returnAddress u ∧ Preserves u v ∧ Inv s v ∧
      StepS s u v (Within · (s.getReg .x2 - BitVec.ofNat 64 ko) 24) ∧
      NewVecE s v (s.getReg .x2 - BitVec.ofNat 64 ko)
        (fingerprintsRust (eqKernelRust k.alphas) (eAt u (s.getReg .x2 - 816)) mem
          (eAt u (s.getReg .x2 - 792)) (eAt u (s.getReg .x2 - 744))
          (eAt u (s.getReg .x2 - BitVec.ofNat 64 kp)) (eAt u (s.getReg .x2 - BitVec.ofNat 64 kc))
          (eAt u (s.getReg .x2 - BitVec.ofNat 64 kb)))) ∨ Dead Image.code v) := by
  obtain ⟨hb1, -, -, -⟩ := bounds hpre
  obtain ⟨o1, o2, o3⟩ := frameSlot (m := fingerprintsStack) hpre h (n := 24) (k := ko)
    (by omega) hko2 hko8 (by decide)
  have hst : RtStack u fingerprintsStack :=
    hpre.stack.sub 1344 h.sp (by decide) (by decide) (by decide) (by decide) (by decide)
  have hsl : stackLo u fingerprintsStack = s.getReg .x2 - BitVec.ofNat 64 (1344 + 1552) := by
    simp only [stackLo, h.sp]; apply BitVec.eq_of_toNat_eq; addr_omega [hb1]
  have e720 (j : Nat) (hj : j ≤ 32) : u.getReg .x11 + BitVec.ofNat 64 j =
      s.getReg .x2 - BitVec.ofNat 64 (720 - j) := by
    rw [h11]; apply BitVec.eq_of_toNat_eq; addr_omega [hb1, hj]
  have cw : capWeights u = s.getReg .x2 - 888 := by
    simp only [capWeights]; rw [h11]; exact env.w0
  have cmi : capMemoryIndex u = s.getReg .x2 - 816 := by
    simp only [capMemoryIndex]; exact (congrArg u.getMem (e720 8 (by omega))).trans env.w1
  have cm : capMemory u = s.getReg .x2 - 864 := by
    simp only [capMemory]; exact (congrArg u.getMem (e720 16 (by omega))).trans env.w2
  have cbi : capBytecodeIndex u = s.getReg .x2 - 792 := by
    simp only [capBytecodeIndex]; exact (congrArg u.getMem (e720 24 (by omega))).trans env.w3
  have cbv : capBytecodeValue u = s.getReg .x2 - 744 := by
    simp only [capBytecodeValue]; exact (congrArg u.getMem (e720 32 (by omega))).trans env.w4
  have hws := K.weights
  have hwl : 0 < (eqKernelRust k.alphas).length := by rw [weightsLen]; decide
  have hs (kk : Nat) (h1 : 128 ≤ kk) (h2 : kk ≤ 1344) (h3 : kk % 8 = 0) :
      Held u fingerprintsStack (s.getReg .x2 - BitVec.ofNat 64 kk) 24 :=
    heldSlot hpre h (by omega) h2 h3 (by decide) (by decide)
  have henv : Held u fingerprintsStack (s.getReg .x2 - BitVec.ofNat 64 720) 40 :=
    heldSlot hpre h (k := 720) (n := 40) (by omega) (by omega) (by omega) (by omega) (by decide)
  have hwv : Held u fingerprintsStack (vecPtr u (s.getReg .x2 - 888))
      (24 * (vecLen u (s.getReg .x2 - 888)).toNat) := heldVec hpre h hws hwl (by decide)
  have hmv : Held u fingerprintsStack (vecPtr u (s.getReg .x2 - 864))
      (24 * (vecLen u (s.getReg .x2 - 864)).toNat) := heldVec hpre h hmem (by omega) (by decide)
  have pre : FingerprintsPre u := {
    heap := h.heap
    stack := hst
    rodata := h.rodata hpre
    out := by rw [h10]; exact regionRange o1 (Nat.le_refl _) (by omega) o1.2
    outFree := h10 ▸ o2
    outStack := h10 ▸ o3
    env := by rw [h11]; exact henv
    weights := by
      rw [cw]; exact ⟨hs 888 (by omega) (by omega) (by omega), hwv⟩
    memory := by
      rw [cm]
      exact ⟨hs 864 (by omega) (by omega) (by omega), hmv⟩
    memoryIndex := by rw [cmi]; exact hs 816 (by omega) (by omega) (by omega)
    bytecodeIndex := by rw [cbi]; exact hs 792 (by omega) (by omega) (by omega)
    bytecodeValue := by rw [cbv]; exact hs 744 (by omega) (by omega) (by omega)
    pc := by rw [h12]; exact hs kp hkp1 hkp2 hkp8
    memoryCount := by rw [h13]; exact hs kc hkc1 hkc2 hkc8
    bytecodeCount := by rw [h14]; exact hs kb hkb1 hkb2 hkb8 }
  obtain ⟨v, hrv, ⟨hpcv, hpv, post⟩ | hd⟩ := hF.call hr hpc pre
  swap
  · exact ⟨v, hrv, Or.inr hd⟩
  have st : StepS s u v (Within · (s.getReg .x2 - BitVec.ofNat 64 ko) 24) :=
    ⟨fun a ha ↦ post.frame a fun i hi hw ↦ ha i hi (by
      rcases hw with hw | hw | hw | hw
      · exact Or.inl (by rw [h10] at hw; exact hw)
      · rw [hsl] at hw; exact Or.inr (Or.inl (by addr_omega [hw, hb1]))
      · exact Or.inr (Or.inr (Or.inl hw))
      · exact Or.inr (Or.inr (Or.inr hw))), post.heap, post.mono, hpv .x2 (by decide)⟩
  have hel := post.elems
  rw [cw, cmi, cm, cbi, cbv, h12, h13, h14, hws.elems, hmem.elems] at hel
  have hv := post.vec
  have hfr := post.fresh
  have hcap := post.cap
  rw [h10] at hv hfr hel hcap
  refine ⟨v, hrv, Or.inl ⟨hpcv, hpv, h.afterR hpre (frameW_slot hpre (by omega) hko2) st.toR, st,
    ⟨hv, ?_, hel⟩⟩⟩
  have hm := h.mono
  simp only [NewBuf] at hfr ⊢
  rw [hcap]
  exact ⟨hfr.1, hfr.2.imp_right fun h' ↦ ⟨by omega, h'.2⟩⟩

/-! ## The framework fingerprints -/

/-- A doubleword a block wrote at `sp + j`, read from `S`. -/
theorem slotOf {s x t : MachineState} (hpre : BusBalancePre s)
    (sp : x.getReg .x2 = s.getReg .x2 - 1344) {j : Nat} (hj : j + 8 ≤ 1344) {c : Word}
    (h : t.getMem (x.getReg .x2 + BitVec.ofNat 64 j) = c) :
    t.getMem (s.getReg .x2 - BitVec.ofNat 64 (1344 - j)) = c := by
  obtain ⟨hb1, -, -, -⟩ := bounds hpre
  rw [← h, sp]
  exact congrArg t.getMem (by apply BitVec.eq_of_toNat_eq; addr_omega [hb1, hj])

/-- The `E` a block wrote at `sp + j`, its limbs `c`, `0`, `0`. -/
theorem eConstOf {s x t : MachineState} (hpre : BusBalancePre s)
    (sp : x.getReg .x2 = s.getReg .x2 - 1344) {j : Nat} (hj : j + 24 ≤ 1344) {c : Word}
    (h0 : t.getMem (x.getReg .x2 + BitVec.ofNat 64 j) = c)
    (h1 : t.getMem (x.getReg .x2 + BitVec.ofNat 64 (j + 8)) = 0)
    (h2 : t.getMem (x.getReg .x2 + BitVec.ofNat 64 (j + 16)) = 0) :
    eAt t (s.getReg .x2 - BitVec.ofNat 64 (1344 - j)) = eNew c := by
  obtain ⟨hb1, -, -, -⟩ := bounds hpre
  refine eAt_const ?_ ?_ ?_
  · exact slotOf hpre sp (by omega) h0
  · rw [← h1, sp]; exact congrArg t.getMem (by apply BitVec.eq_of_toNat_eq; addr_omega [hb1, hj])
  · rw [← h2, sp]; exact congrArg t.getMem (by apply BitVec.eq_of_toNat_eq; addr_omega [hb1, hj])

/-- The `E` a block wrote at `sp + j`, its limbs `a`, `b`, `c`. -/
theorem eOf3Of {s x t : MachineState} (hpre : BusBalancePre s)
    (sp : x.getReg .x2 = s.getReg .x2 - 1344) {j : Nat} (hj : j + 24 ≤ 1344) {a b c : Word}
    (h0 : t.getMem (x.getReg .x2 + BitVec.ofNat 64 j) = a)
    (h1 : t.getMem (x.getReg .x2 + BitVec.ofNat 64 (j + 8)) = b)
    (h2 : t.getMem (x.getReg .x2 + BitVec.ofNat 64 (j + 16)) = c) :
    eAt t (s.getReg .x2 - BitVec.ofNat 64 (1344 - j)) = eOf3 a b c := by
  obtain ⟨hb1, -, -, -⟩ := bounds hpre
  rw [eAt_eOf3]
  congr 1
  · exact slotOf hpre sp (by omega) h0
  · rw [← h1, sp]; exact congrArg t.getMem (by apply BitVec.eq_of_toNat_eq; addr_omega [hb1, hj])
  · rw [← h2, sp]; exact congrArg t.getMem (by apply BitVec.eq_of_toNat_eq; addr_omega [hb1, hj])

theorem one_eq_eNew : (1 : E) = eNew 1 := sepStateRust_eNew

/-- The push side's framework fingerprints. -/
def pushFps (s : MachineState) (k : Start) (state : GkrState) (mem : List E) (bv : E) : List E :=
  fingerprintsRust (eqKernelRust k.alphas) (indexMleRust (state.point.take (logMem s).toNat)) mem
    (indexMleRust (state.point.take (logBc s).toNat)) bv (gpowRust 0#64) 1 1

/-- The pull side's. -/
def pullFps (s : MachineState) (k : Start) (state : GkrState) (mem : List E) (mf bf bv : E) :
    List E :=
  fingerprintsRust (eqKernelRust k.alphas) (indexMleRust (state.point.take (logMem s).toNat)) mem
    (indexMleRust (state.point.take (logBc s).toNat)) bv
    (gpowRust ((1#64 <<< ((logBc s).toNat % 64)) - 1#64)) mf bf

/-- At `alloc`'s entry (`0x80000284`, for `vec![Form::default(); 3]`'s buffer): the two sides'
framework fingerprints at `S - 656` and `S - 680`, `totals` empty at `S - 632`, `weights`' buffer
and length in `s4`, `s5` and `s0`, `s6`. -/
structure Fps (bev : MachineState → Word → List E → Option E) (s z : MachineState) (k : Start)
    (state : GkrState) (mem : List E) (mf bf bv : E) : Prop where
  inv : Inv s z
  kept : Kept s z k
  claims : ClaimsOk s z (z.getMem (s.getReg .x2 - 840)) (z.getMem (s.getReg .x2 - 832))
    (z.getMem (s.getReg .x2 - 824)) (allClaims s state mem mf bf)
  len : z.getMem (s.getReg .x2 - 824) = 5
  bcPoint : NewVecE s z (s.getReg .x2 - 768) (state.point.take (logBc s).toNat ++ k.alphas)
  values : NewVecE s z (s.getReg .x2 - 176) state.values
  point : NewVecR s z (z.getMem (s.getReg .x2 - 1320)) (z.getMem (s.getReg .x2 - 1256))
    (z.getMem (s.getReg .x2 - 1144)) state.point
  valuesPtr : z.getMem (s.getReg .x2 - 1280) = vecPtr z (s.getReg .x2 - 176)
  pushPtr : z.getMem (s.getReg .x2 - 1272) = vecPtr s (s.getReg .x11 + 24)
  lm : (logMem s).toNat ≤ state.point.length
  lb : (logBc s).toNat ≤ state.point.length
  pushF : NewVecE s z (s.getReg .x2 - 656) (pushFps s k state mem bv)
  pullF : NewVecE s z (s.getReg .x2 - 680) (pullFps s k state mem mf bf bv)
  t0 : z.getMem (s.getReg .x2 - 632) = 0
  t1 : z.getMem (s.getReg .x2 - 624) = 8
  t2 : z.getMem (s.getReg .x2 - 616) = 0
  x1 : z.getReg .x1 = 0x80007274
  x9 : z.getReg .x9 = 8
  x10 : z.getReg .x10 = 8
  x11 : z.getReg .x11 = 72
  x8 : z.getReg .x8 = vecPtr z (s.getReg .x2 - 888)
  x22 : z.getReg .x22 = vecLen z (s.getReg .x2 - 888)
  x20 : z.getReg .x20 = vecPtr z (s.getReg .x2 - 888)
  x21 : z.getReg .x21 = vecLen z (s.getReg .x2 - 888)
  x27 : z.getReg .x27 = z.getMem (s.getReg .x2 - 1256)
  tracks : Tracks (prog bev s) (s.getReg .x12) s z (pure (restValue s k state mem mf bf bv))

theorem fpsPush (hP : PowSpec) (hF : FingerprintsSpec)
    {bev : MachineState → Word → List E → Option E} {s y : MachineState} {k : Start}
    {state : GkrState} {mem : List E} {mf bf bv : E} (hpre : BusBalancePre s)
    (E : Evaluated bev s y k state mem mf bf bv) (hpc : y.pc = 0x80007170) :
    ∃ t, Reaches Image.code y t ∧ (Dead Image.code t ∨ (t.pc = 0x80007208 ∧ Inv s t ∧
      StepS s y t (FpW s) ∧ (∀ r ∈ calleeSaved, t.getReg r = y.getReg r) ∧ Env s t ∧
      eAt t (s.getReg .x2 - 608) = gpowRust ((1#64 <<< ((logBc s).toNat % 64)) - 1#64) ∧
      NewVecE s t (s.getReg .x2 - 656) (pushFps s k state mem bv))) := by
  obtain ⟨hb1, -, -, -⟩ := bounds hpre
  have hval : ValidMemRange (s.getReg .x2 - 4544) 568 := hpre.stack.valid
  have fW := FpW.frameW hpre
  obtain ⟨t₁, hr₁, hd | ⟨hpc₁, I₁, st₁, rg₁, fp₁, env₁⟩⟩ := powStep hP hpre E hpc
  · exact ⟨t₁, hr₁, Or.inl hd⟩
  have sp₁ : t₁.getReg .x2 = s.getReg .x2 - 1344 := I₁.sp
  -- the push side's fingerprints
  obtain ⟨u₂, hr₂, h₂⟩ := Sym.BlockSpec.reaches b800071c4_spec hpc₁ (by
    rv_eval [sp₁]
    and_intros <;> valid_access hval [hb1])
  have k₂ := b800071c4_keeps h₂
  have fr₂ : DFrame t₁ u₂ (Within · (s.getReg .x2 - 248) 72) :=
    (DFrame.of_memFrame (b800071c4_frame h₂ (by rw [sp₁]; addr_omega [hb1]))).mono
      fun a ha ↦ by rw [sp₁] at ha; addr_omega [ha, hb1]
  have st₂ : StepS s t₁ u₂ (FpW s) :=
    StepS.ofDFrame I₁.heap fr₂ (fun a ha ↦ Or.inr ha) (fun i hi hw ↦ by addr_omega [hw, hi, hb1])
      (k₂ .x2 (by decide))
  have I₂ := I₁.afterR hpre fW st₂.toR
  have sp₂ : u₂.getReg .x2 = s.getReg .x2 - 1344 := I₂.sp
  have S₂ : StepS s y u₂ (FpW s) :=
    (st₁.trans st₂).weaken fun a ha ↦ by rcases ha with ha | ha <;> exact ha
  have K₂ : Kept s u₂ k := E.kept.step hpre (S₂.toR.weaken fun _ ha ↦ FpW.free hpre ha)
  have env₂ : Env s u₂ :=
    ⟨(fr₂ _ fun i hi hw ↦ by addr_omega [hw, hi, hb1]).trans env₁.w0,
      (fr₂ _ fun i hi hw ↦ by addr_omega [hw, hi, hb1]).trans env₁.w1,
      (fr₂ _ fun i hi hw ↦ by addr_omega [hw, hi, hb1]).trans env₁.w2,
      (fr₂ _ fun i hi hw ↦ by addr_omega [hw, hi, hb1]).trans env₁.w3,
      (fr₂ _ fun i hi hw ↦ by addr_omega [hw, hi, hb1]).trans env₁.w4⟩
  have miss (x : Word) (n : Nat) (hx : (s.getReg .x2 - 1344).toNat ≤ x.toNat ∧
      x.toNat + n ≤ (s.getReg .x2 - 720).toNat ∨ (s.getReg .x2 - 176).toNat ≤ x.toNat ∧
      x.toNat + n ≤ (s.getReg .x2).toNat) : ∀ z, Within z x n → ¬ FpW s z := fun z hz h' ↦ by
    rcases hx with hx | hx <;> rcases h' with h' | h' <;> addr_omega [hz, h', hx, hb1]
  have M₂ : NewVecE s u₂ (s.getReg .x2 - 864) mem :=
    E.memory.keepR hpre S₂.toR fW (by addr_omega [hb1])
      (miss _ 24 (Or.inl (by constructor <;> addr_omega [hb1])))
  have ex (w : MachineState) (stw : StepS s y w (FpW s)) (j : Nat) (hj1 : 720 + 24 ≤ j)
      (hj2 : j ≤ 1344) : eAt w (s.getReg .x2 - BitVec.ofNat 64 j) =
        eAt y (s.getReg .x2 - BitVec.ofNat 64 j) :=
    stw.eSlot hpre (miss _ 24 (Or.inl (by constructor <;> addr_omega [hb1, hj1, hj2])))
      (by constructor <;> addr_omega [hb1, hj1, hj2])
  have one₂ : eAt u₂ (s.getReg .x2 - BitVec.ofNat 64 248) = eNew 1 :=
    eConstOf hpre sp₁ (j := 1096) (by omega) (b800071c4_m_x2_1096 h₂) (b800071c4_m_x2_1104 h₂)
      (b800071c4_m_x2_1112 h₂)
  have one₂' : eAt u₂ (s.getReg .x2 - BitVec.ofNat 64 224) = eNew 1 :=
    eConstOf hpre sp₁ (j := 1120) (by omega) (b800071c4_m_x2_1120 h₂) (b800071c4_m_x2_1128 h₂)
      (b800071c4_m_x2_1136 h₂)
  have one₂'' : eAt u₂ (s.getReg .x2 - BitVec.ofNat 64 200) = eNew 1 :=
    eConstOf hpre sp₁ (j := 1144) (by omega) (b800071c4_m_x2_1144 h₂) (b800071c4_m_x2_1152 h₂)
      (b800071c4_m_x2_1160 h₂)
  have a2 (j : Nat) (hj : j ≤ 1344) : u₂.getReg .x2 + BitVec.ofNat 64 j =
      s.getReg .x2 - BitVec.ofNat 64 (1344 - j) := by
    rw [sp₂]; apply BitVec.eq_of_toNat_eq; addr_omega [hb1, hj]
  obtain ⟨t₂, hrt₂, ⟨hpct₂, hpt₂, It₂, stt₂, F₁⟩ | hd⟩ := fpsCall hF hpre I₂ K₂ (Reaches.refl u₂)
    (b800071c4_pc h₂) (ko := 656) (kp := 248) (kc := 224) (kb := 200)
    (by rw [b800071c4_x10 h₂, ← k₂ .x2 (by decide)]; exact a2 688 (by omega))
    (by omega) (by omega) (by omega)
    (by rw [b800071c4_x11 h₂, ← k₂ .x2 (by decide)]; exact a2 624 (by omega)) env₂ M₂ E.memLen
    (by rw [b800071c4_x12 h₂, ← k₂ .x2 (by decide)]; exact a2 1096 (by omega))
    (by omega) (by omega) (by omega)
    (by rw [b800071c4_x13 h₂, ← k₂ .x2 (by decide)]; exact a2 1120 (by omega))
    (by omega) (by omega) (by omega)
    (by rw [b800071c4_x14 h₂, ← k₂ .x2 (by decide)]; exact a2 1144 (by omega))
    (by omega) (by omega) (by omega)
  swap
  · exact ⟨t₂, hr₁.trans (hr₂.trans hrt₂), Or.inl hd⟩
  have hpc₂ : t₂.pc = 0x80007208 := by rw [hpct₂, returnAddress_eq, b800071c4_x1 h₂]; decide
  have e816₂ : eAt u₂ (s.getReg .x2 - 816) = eAt y (s.getReg .x2 - 816) :=
    ex u₂ S₂ 816 (by omega) (by omega)
  have e792₂ : eAt u₂ (s.getReg .x2 - 792) = eAt y (s.getReg .x2 - 792) :=
    ex u₂ S₂ 792 (by omega) (by omega)
  have e744₂ : eAt u₂ (s.getReg .x2 - 744) = eAt y (s.getReg .x2 - 744) :=
    ex u₂ S₂ 744 (by omega) (by omega)
  rw [one₂, one₂', one₂'', e816₂, e792₂, e744₂, E.memIndex, E.bcIndex, E.bcValue] at F₁
  have hpush : pushFps s k state mem bv = fingerprintsRust (eqKernelRust k.alphas)
      (indexMleRust (state.point.take (logMem s).toNat)) mem
      (indexMleRust (state.point.take (logBc s).toNat)) bv (eNew 1) (eNew 1) (eNew 1) := by
    rw [pushFps, gpowRust_zero, ← one_eq_eNew]
  have w2 (x : Word) (hx : ∀ z, Within z x 8 → ¬ (Within z (s.getReg .x2 - 656) 24 ∨
      Within z (s.getReg .x2 - 248) 72)) (hin : (s.getReg .x2 - 1344).toNat ≤ x.toNat ∧
      x.toNat + 8 ≤ (s.getReg .x2).toNat) : t₂.getMem x = t₁.getMem x := by
    rw [stt₂.slot hpre (fun z hz hw ↦ hx z hz (Or.inl (by addr_omega [hw, hb1]))) hin]
    exact fr₂ x fun i hi hw ↦ hx _ (by addr_omega [hi, hin, hb1]) (Or.inr hw)
  refine ⟨t₂, hr₁.trans (hr₂.trans hrt₂), Or.inr ⟨hpc₂, It₂,
    (S₂.trans stt₂).weaken fun a ha ↦ by
      rcases ha with ha | ha
      · exact ha
      · exact Or.inl (by addr_omega [ha, hb1]),
    fun r hr ↦ by rw [hpt₂ r hr, k₂ r (by unfold calleeSaved at hr; exact mem_of_mem hr _), rg₁ r hr],
    ⟨?_, ?_, ?_, ?_, ?_⟩, ?_, by rw [hpush]; exact F₁⟩⟩
  · rw [w2 _ (fun z hz hw ↦ by rcases hw with hw | hw <;> addr_omega [hz, hw, hb1])
      (by constructor <;> addr_omega [hb1])]; exact env₁.w0
  · rw [w2 _ (fun z hz hw ↦ by rcases hw with hw | hw <;> addr_omega [hz, hw, hb1])
      (by constructor <;> addr_omega [hb1])]; exact env₁.w1
  · rw [w2 _ (fun z hz hw ↦ by rcases hw with hw | hw <;> addr_omega [hz, hw, hb1])
      (by constructor <;> addr_omega [hb1])]; exact env₁.w2
  · rw [w2 _ (fun z hz hw ↦ by rcases hw with hw | hw <;> addr_omega [hz, hw, hb1])
      (by constructor <;> addr_omega [hb1])]; exact env₁.w3
  · rw [w2 _ (fun z hz hw ↦ by rcases hw with hw | hw <;> addr_omega [hz, hw, hb1])
      (by constructor <;> addr_omega [hb1])]; exact env₁.w4
  · rw [← fp₁]
    refine eAt_congr ?_ ?_ ?_ <;>
    · exact w2 _ (fun z hz hw ↦ by rcases hw with hw | hw <;> addr_omega [hz, hw, hb1])
        (by constructor <;> addr_omega [hb1])

theorem fpsStage (hP : PowSpec) (hF : FingerprintsSpec)
    {bev : MachineState → Word → List E → Option E} {s y : MachineState} {k : Start}
    {state : GkrState} {mem : List E} {mf bf bv : E} (hpre : BusBalancePre s)
    (E : Evaluated bev s y k state mem mf bf bv) (hpc : y.pc = 0x80007170) :
    ∃ z, Reaches Image.code y z ∧ (Dead Image.code z ∨
      (z.pc = 0x80000284 ∧ Fps bev s z k state mem mf bf bv)) := by
  obtain ⟨hb1, -, -, -⟩ := bounds hpre
  have hval : ValidMemRange (s.getReg .x2 - 4544) 568 := hpre.stack.valid
  have fW := FpW.frameW hpre
  obtain ⟨t₂, hr₂, hd | ⟨hpc₂, It₂, S₃, rg₂, env₂, fp₂, F₁⟩⟩ := fpsPush hP hF hpre E hpc
  · exact ⟨t₂, hr₂, Or.inl hd⟩
  have miss (x : Word) (n : Nat) (hx : (s.getReg .x2 - 1344).toNat ≤ x.toNat ∧
      x.toNat + n ≤ (s.getReg .x2 - 720).toNat ∨ (s.getReg .x2 - 176).toNat ≤ x.toNat ∧
      x.toNat + n ≤ (s.getReg .x2).toNat) : ∀ z, Within z x n → ¬ FpW s z := fun z hz h' ↦ by
    rcases hx with hx | hx <;> rcases h' with h' | h' <;> addr_omega [hz, h', hx, hb1]
  have ex (w : MachineState) (stw : StepS s y w (FpW s)) (j : Nat) (hj1 : 720 + 24 ≤ j)
      (hj2 : j ≤ 1344) : eAt w (s.getReg .x2 - BitVec.ofNat 64 j) =
        eAt y (s.getReg .x2 - BitVec.ofNat 64 j) :=
    stw.eSlot hpre (miss _ 24 (Or.inl (by constructor <;> addr_omega [hb1, hj1, hj2])))
      (by constructor <;> addr_omega [hb1, hj1, hj2])
  have sp₂' : t₂.getReg .x2 = s.getReg .x2 - 1344 := It₂.sp
  -- the pull side's arguments
  obtain ⟨u₃, hr₃, h₃⟩ := Sym.BlockSpec.reaches b80007208_spec hpc₂ (by
    rv_eval [sp₂']
    and_intros <;> valid_access hval [hb1])
  have k₃ := b80007208_keeps h₃
  have fr₃ : DFrame t₂ u₃ (Within · (s.getReg .x2 - 584) 48) :=
    (DFrame.of_memFrame (b80007208_frame h₃ (by rw [sp₂']; addr_omega [hb1]))).mono
      fun a ha ↦ by rw [sp₂'] at ha; addr_omega [ha, hb1]
  have st₃ : StepS s t₂ u₃ (FpW s) :=
    StepS.ofDFrame It₂.heap fr₃ (fun a ha ↦ Or.inl (by addr_omega [ha, hb1]))
      (fun i hi hw ↦ by addr_omega [hw, hi, hb1]) (k₃ .x2 (by decide))
  have I₃ := It₂.afterR hpre fW st₃.toR
  have S₄ : StepS s y u₃ (FpW s) :=
    (S₃.trans st₃).weaken fun a ha ↦ by rcases ha with ha | ha <;> exact ha
  have K₃ : Kept s u₃ k := E.kept.step hpre (S₄.toR.weaken fun _ ha ↦ FpW.free hpre ha)
  have w3 (x : Word) (hx : ∀ z, Within z x 8 → ¬ Within z (s.getReg .x2 - 584) 48)
      (hin : (s.getReg .x2 - 1344).toNat ≤ x.toNat ∧ x.toNat + 8 ≤ (s.getReg .x2).toNat) :
      u₃.getMem x = t₂.getMem x :=
    fr₃ x fun i hi hw ↦ hx _ (by addr_omega [hi, hin, hb1]) hw
  have env₃ : Env s u₃ :=
    ⟨(w3 _ (fun z hz hw ↦ by addr_omega [hz, hw, hb1]) (by constructor <;> addr_omega [hb1])).trans env₂.w0,
      (w3 _ (fun z hz hw ↦ by addr_omega [hz, hw, hb1]) (by constructor <;> addr_omega [hb1])).trans env₂.w1,
      (w3 _ (fun z hz hw ↦ by addr_omega [hz, hw, hb1]) (by constructor <;> addr_omega [hb1])).trans env₂.w2,
      (w3 _ (fun z hz hw ↦ by addr_omega [hz, hw, hb1]) (by constructor <;> addr_omega [hb1])).trans env₂.w3,
      (w3 _ (fun z hz hw ↦ by addr_omega [hz, hw, hb1]) (by constructor <;> addr_omega [hb1])).trans env₂.w4⟩
  have M₃ : NewVecE s u₃ (s.getReg .x2 - 864) mem :=
    E.memory.keepR hpre S₄.toR fW (by addr_omega [hb1])
      (miss _ 24 (Or.inl (by constructor <;> addr_omega [hb1])))
  have r₃ (r : Reg) (hr : r ∈ ([.x8, .x22, .x25, .x26] : List Reg)) : t₂.getReg r = y.getReg r :=
    rg₂ r (by unfold calleeSaved; exact mem_of_mem hr _)
  have y1112 : t₂.getMem (t₂.getReg .x2 + 232) = y.getMem (s.getReg .x2 - 1112) := by
    rw [sp₂', show s.getReg .x2 - 1344 + 232 = s.getReg .x2 - 1112 by
      apply BitVec.eq_of_toNat_eq; addr_omega [hb1]]
    exact S₃.slot hpre (miss _ 8 (Or.inl (by constructor <;> addr_omega [hb1])))
      (by constructor <;> addr_omega [hb1])
  have y1120 : t₂.getMem (t₂.getReg .x2 + 224) = y.getMem (s.getReg .x2 - 1120) := by
    rw [sp₂', show s.getReg .x2 - 1344 + 224 = s.getReg .x2 - 1120 by
      apply BitVec.eq_of_toNat_eq; addr_omega [hb1]]
    exact S₃.slot hpre (miss _ 8 (Or.inl (by constructor <;> addr_omega [hb1])))
      (by constructor <;> addr_omega [hb1])
  have mf₃ : eAt u₃ (s.getReg .x2 - BitVec.ofNat 64 584) = mf := by
    rw [E.mfEq]
    refine (eOf3Of hpre sp₂' (j := 760) (by omega) (b80007208_m_x2_760 h₃)
      (b80007208_m_x2_768 h₃) (b80007208_m_x2_776 h₃)).trans ?_
    rw [r₃ .x25 (by decide), r₃ .x22 (by decide), y1112]
  have bf₃ : eAt u₃ (s.getReg .x2 - BitVec.ofNat 64 560) = bf := by
    rw [E.bfEq]
    refine (eOf3Of hpre sp₂' (j := 784) (by omega) (b80007208_m_x2_784 h₃)
      (b80007208_m_x2_792 h₃) (b80007208_m_x2_800 h₃)).trans ?_
    rw [r₃ .x26 (by decide), r₃ .x8 (by decide), y1120, E.x8]
  have fp₃ : eAt u₃ (s.getReg .x2 - BitVec.ofNat 64 608) =
      gpowRust ((1#64 <<< ((logBc s).toNat % 64)) - 1#64) := by
    rw [← fp₂]
    refine eAt_congr ?_ ?_ ?_ <;>
      exact w3 _ (fun z hz hw ↦ by addr_omega [hz, hw, hb1]) (by constructor <;> addr_omega [hb1])
  have a3 (j : Nat) (hj : j ≤ 1344) : u₃.getReg .x2 + BitVec.ofNat 64 j =
      s.getReg .x2 - BitVec.ofNat 64 (1344 - j) := by
    rw [k₃ .x2 (by decide), sp₂']; apply BitVec.eq_of_toNat_eq; addr_omega [hb1, hj]
  obtain ⟨t₃, hrt₃, ⟨hpct₃, hpt₃, It₃, stt₃, F₂⟩ | hd⟩ := fpsCall hF hpre I₃ K₃ (Reaches.refl u₃)
    (b80007208_pc h₃) (ko := 680) (kp := 608) (kc := 584) (kb := 560)
    (by rw [b80007208_x10 h₃, ← k₃ .x2 (by decide)]; exact a3 664 (by omega))
    (by omega) (by omega) (by omega)
    (by rw [b80007208_x11 h₃, ← k₃ .x2 (by decide)]; exact a3 624 (by omega)) env₃ M₃ E.memLen
    (by rw [b80007208_x12 h₃, ← k₃ .x2 (by decide)]; exact a3 736 (by omega))
    (by omega) (by omega) (by omega)
    (by rw [b80007208_x13 h₃, ← k₃ .x2 (by decide)]; exact a3 760 (by omega))
    (by omega) (by omega) (by omega)
    (by rw [b80007208_x14 h₃, ← k₃ .x2 (by decide)]; exact a3 784 (by omega))
    (by omega) (by omega) (by omega)
  swap
  · exact ⟨t₃, hr₂.trans (hr₃.trans hrt₃), Or.inl hd⟩
  have hpc₃ : t₃.pc = 0x8000724c := by rw [hpct₃, returnAddress_eq, b80007208_x1 h₃]; decide
  have sp₃ : t₃.getReg .x2 = s.getReg .x2 - 1344 := It₃.sp
  -- `totals`, `weights` in `s0`, `s6`
  obtain ⟨z, hr₄, h₄⟩ := Sym.BlockSpec.reaches b8000724c_spec hpc₃ (by
    rv_eval [sp₃]
    and_intros <;> valid_access hval [hb1])
  have k₄ := b8000724c_keeps h₄
  have fr₄ : DFrame t₃ z (Within · (s.getReg .x2 - 632) 24) :=
    (DFrame.of_memFrame (b8000724c_frame h₄ (by rw [sp₃]; addr_omega [hb1]))).mono
      fun a ha ↦ by rw [sp₃] at ha; addr_omega [ha, hb1]
  have st₄ : StepS s t₃ z (Within · (s.getReg .x2 - 632) 24) :=
    StepS.ofDFrame It₃.heap fr₄ (fun _ h ↦ h) (fun i hi hw ↦ by addr_omega [hw, hi, hb1])
      (k₄ .x2 (by decide))
  have st₃' : StepS s t₂ u₃ (Within · (s.getReg .x2 - 584) 48) :=
    StepS.ofDFrame It₂.heap fr₃ (fun _ h ↦ h) (fun i hi hw ↦ by addr_omega [hw, hi, hb1])
      (k₃ .x2 (by decide))
  have Iz := It₃.afterR hpre (fun a ha ↦ by addr_omega [ha, hb1]) st₄.toR
  have Sz : StepS s y z (FpW s) :=
    (((S₄.trans stt₃).trans st₄).weaken fun a ha ↦ by
      rcases ha with ((ha | ha) | ha)
      · exact ha
      · exact Or.inl (by addr_omega [ha, hb1])
      · exact Or.inl (by addr_omega [ha, hb1]))
  have B : StepS s t₂ z fun a ↦ (Within a (s.getReg .x2 - 584) 48 ∨
      Within a (s.getReg .x2 - BitVec.ofNat 64 680) 24) ∨ Within a (s.getReg .x2 - 632) 24 :=
    (st₃'.trans stt₃).trans st₄
  have fB : FrameW s fun a ↦ (Within a (s.getReg .x2 - 584) 48 ∨
      Within a (s.getReg .x2 - BitVec.ofNat 64 680) 24) ∨ Within a (s.getReg .x2 - 632) 24 :=
    fun a ha ↦ by rcases ha with (ha | ha) | ha <;> addr_omega [ha, hb1]
  have K1 (x : Word) (hx : (s.getReg .x2 - 1344).toNat ≤ x.toNat ∧
      x.toNat + 8 ≤ (s.getReg .x2 - 720).toNat ∨ (s.getReg .x2 - 176).toNat ≤ x.toNat ∧
      x.toNat + 8 ≤ (s.getReg .x2).toNat) : z.getMem x = y.getMem x :=
    Sz.slot hpre (miss x 8 hx) (by rcases hx with hx | hx <;> constructor <;> addr_omega [hx, hb1])
  have e816₃ : eAt u₃ (s.getReg .x2 - 816) = eAt y (s.getReg .x2 - 816) :=
    ex u₃ S₄ 816 (by omega) (by omega)
  have e792₃ : eAt u₃ (s.getReg .x2 - 792) = eAt y (s.getReg .x2 - 792) :=
    ex u₃ S₄ 792 (by omega) (by omega)
  have e744₃ : eAt u₃ (s.getReg .x2 - 744) = eAt y (s.getReg .x2 - 744) :=
    ex u₃ S₄ 744 (by omega) (by omega)
  rw [fp₃, mf₃, bf₃, e816₃, e792₃, e744₃, E.memIndex, E.bcIndex, E.bcValue] at F₂
  have z880 : z.getMem (s.getReg .x2 - 880) = t₂.getMem (s.getReg .x2 - 880) :=
    B.slot hpre (fun z hz h' ↦ by rcases h' with (h' | h') | h' <;> addr_omega [hz, h', hb1])
      (by constructor <;> addr_omega [hb1])
  have z872 : z.getMem (s.getReg .x2 - 872) = t₂.getMem (s.getReg .x2 - 872) :=
    B.slot hpre (fun z hz h' ↦ by rcases h' with (h' | h') | h' <;> addr_omega [hz, h', hb1])
      (by constructor <;> addr_omega [hb1])
  have z880' : z.getMem (s.getReg .x2 - 880) = t₃.getMem (s.getReg .x2 - 880) :=
    st₄.slot hpre (fun z hz h' ↦ by addr_omega [hz, h', hb1]) (by constructor <;> addr_omega [hb1])
  have z872' : z.getMem (s.getReg .x2 - 872) = t₃.getMem (s.getReg .x2 - 872) :=
    st₄.slot hpre (fun z hz h' ↦ by addr_omega [hz, h', hb1]) (by constructor <;> addr_omega [hb1])
  have vp : vecPtr z (s.getReg .x2 - 888) = z.getMem (s.getReg .x2 - 880) :=
    congrArg z.getMem (by apply BitVec.eq_of_toNat_eq; addr_omega [hb1])
  have vl : vecLen z (s.getReg .x2 - 888) = z.getMem (s.getReg .x2 - 872) :=
    congrArg z.getMem (by apply BitVec.eq_of_toNat_eq; addr_omega [hb1])
  have t464 : t₂.getMem (t₂.getReg .x2 + 464) = t₂.getMem (s.getReg .x2 - 880) :=
    congrArg t₂.getMem (by rw [sp₂']; apply BitVec.eq_of_toNat_eq; addr_omega [hb1])
  have t472 : t₂.getMem (t₂.getReg .x2 + 472) = t₂.getMem (s.getReg .x2 - 872) :=
    congrArg t₂.getMem (by rw [sp₂']; apply BitVec.eq_of_toNat_eq; addr_omega [hb1])
  refine ⟨z, hr₂.trans (hr₃.trans (hrt₃.trans hr₄)),
    Or.inr ⟨b8000724c_pc h₄, {
    inv := Iz
    kept := E.kept.step hpre (Sz.toR.weaken fun _ ha ↦ FpW.free hpre ha)
    claims := by
      rw [K1 _ (Or.inl (by constructor <;> addr_omega [hb1])),
        K1 _ (Or.inl (by constructor <;> addr_omega [hb1])),
        K1 _ (Or.inl (by constructor <;> addr_omega [hb1]))]
      exact E.claims.keepR hpre Sz.toR fW
    len := by rw [K1 _ (Or.inl (by constructor <;> addr_omega [hb1]))]; exact E.len
    bcPoint := E.bcPoint.keepR hpre Sz.toR fW (by addr_omega [hb1])
      (miss _ 24 (Or.inl (by constructor <;> addr_omega [hb1])))
    values := E.values.keepR hpre Sz.toR fW (by addr_omega [hb1])
      (miss _ 24 (Or.inr (by constructor <;> addr_omega [hb1])))
    point := by
      rw [K1 _ (Or.inl (by constructor <;> addr_omega [hb1])),
        K1 _ (Or.inl (by constructor <;> addr_omega [hb1])),
        K1 _ (Or.inl (by constructor <;> addr_omega [hb1]))]
      exact E.point.keepR hpre Sz.toR fW
    valuesPtr := by
      rw [K1 _ (Or.inl (by constructor <;> addr_omega [hb1])), E.valuesPtr, vecPtr, vecPtr,
        K1 _ (Or.inr (by constructor <;> addr_omega [hb1]))]
    pushPtr := by rw [K1 _ (Or.inl (by constructor <;> addr_omega [hb1]))]; exact E.pushPtr
    lm := E.lm
    lb := E.lb
    pushF := by
      exact F₁.keepR hpre B.toR fB (by addr_omega [hb1]) fun z hz h' ↦ by
        rcases h' with (h' | h') | h' <;> addr_omega [hz, h', hb1]
    pullF := F₂.keepR hpre st₄.toR (fun a ha ↦ by addr_omega [ha, hb1]) (by addr_omega [hb1])
      fun z hz h' ↦ by addr_omega [hz, h', hb1]
    t0 := slotOf hpre sp₃ (j := 712) (by omega) (b8000724c_m_x2_712 h₄)
    t1 := slotOf hpre sp₃ (j := 720) (by omega) (b8000724c_m_x2_720 h₄)
    t2 := slotOf hpre sp₃ (j := 728) (by omega) (b8000724c_m_x2_728 h₄)
    x1 := b8000724c_x1 h₄
    x9 := b8000724c_x9 h₄
    x10 := b8000724c_x10 h₄
    x11 := b8000724c_x11 h₄
    x8 := by
      rw [b8000724c_x8 h₄, vp, z880', sp₃]
      exact congrArg t₃.getMem (by apply BitVec.eq_of_toNat_eq; addr_omega [hb1])
    x22 := by
      rw [b8000724c_x22 h₄, vl, z872', sp₃]
      exact congrArg t₃.getMem (by apply BitVec.eq_of_toNat_eq; addr_omega [hb1])
    x20 := by
      rw [k₄ .x20 (by decide), hpt₃ .x20 (by decide), b80007208_x20 h₃, t464, vp, z880]
    x21 := by
      rw [k₄ .x21 (by decide), hpt₃ .x21 (by decide), b80007208_x21 h₃, t472, vl, z872]
    x27 := by
      rw [k₄ .x27 (by decide), hpt₃ .x27 (by decide), k₃ .x27 (by decide), rg₂ .x27 (by decide),
        E.x27, K1 _ (Or.inl (by constructor <;> addr_omega [hb1]))]
    tracks := E.tracks.keep fun T hT ↦ Sz.transcript hpre E.inv fW hT }⟩⟩

end Rv64Verifier.Proofs.Bus.VerifyBusBalance
