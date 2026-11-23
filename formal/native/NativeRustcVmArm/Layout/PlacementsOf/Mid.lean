module

public import NativeRustcVmArm.Code.Vm.Memset.Names
public import NativeRustcVmArm.Code.Vm.StackOffsets.Names
public import NativeRustcVmArm.Layout.PlacementsOf.Entry

/-!
# `placements_of`: the stacked columns' offsets (`b8` to `b14`)

From `.L6` with the stacked columns and their sizes in `block_cols`, `block_sizes` (`I1 158 158`):
`b8` zeroes `block_offsets`, `b10` calls `stack_offsets` on the sizes (always `Some`: the sizes fit,
`fit`), `b12` keeps the total's log-size in X21 and zeroes `offsets`; `b14` starts the second loop
at `.L10` (`I2 0`).
-/

namespace NativeRustcVmArm.Layout.PlacementsOf

open NativeRustcArm NativeRustcArm.Sym NativeRustcVmArm.Vm.PlacementsOf
open NativeVm.Model NativeRustcVm.Layout LeanVM.Protocol.Verifier NativeVm.Math.Layout
open NativeRustcVm (WordAt WordsAt wordOf addr_add_add addr_add_zero toNat_add_ofNat)
open NativeRustcVmArm.Arrays (Body calleeRegs inSlots keepsAll restores)
open NativeRustcVmArm.Layout.BuildLayout (Body.of_call_stack stackOk_body natsOf_of_words
  wordsAt_natWords not_top_of_low sp_toNat_sub)

public section

section
variable [Labels]

/-- **The second loop** at `.L10`: the stacked columns before the `i`th have their offsets in
`offsets`. -/
structure I2 (m0 : MachineData) (i : Nat) (st : MachineData) : Prop where
  body : Bd m0 st
  le : i ≤ 94
  x8 : st.regs.X8.toBitVec = fb m0 + BitVec.ofNat 64 (2528 + 8 * i)
  x9 : st.regs.X9.toBitVec = fb m0 + BitVec.ofNat 64 (8 * i)
  x22 : st.regs.X22.toNat = 94 - i
  x19 : st.regs.X19 = m0.regs.X0
  x20 : st.regs.X20 = m0.regs.X1
  x21 : st.regs.X21.toNat = log2Ceil (sumF (κ m0) 0)
  x23 : st.regs.X23.toBitVec = rodataAddr .keccakSlot
  x24 : st.regs.X24.toBitVec = rodataAddr .keccakOutput
  x25 : st.regs.X25.toBitVec = fb m0 + BitVec.ofNat 64 3792
  cols : ∀ q (h : q < blockList.length),
    WordAt st.dmem (fb m0 + BitVec.ofNat 64 (8 * q)) (blockList[q]).toUInt64
  offs : ∀ q (h : q < blockList.length), WordAt st.dmem (fb m0 + BitVec.ofNat 64 (2528 + 8 * q))
    (sumF (κ m0) (keyF (κ m0) blockList[q])).toUInt64
  done : ∀ q (h : q < blockList.length), q < i →
    WordAt st.dmem (fb m0 + BitVec.ofNat 64 (3792 + 8 * blockList[q]))
      (sumF (κ m0) (keyF (κ m0) blockList[q])).toUInt64

/-- A word of the frame off the `n'` bytes from `o'` that a call changed. -/
theorem frame_keep {m0 : MachineData} (hF : Facts m0) {d d' : Mem 64} {o o' n' : Nat}
    (ho : o + 8 ≤ 5136) (ho' : o' + n' ≤ 5136) (hd : o + 8 ≤ o' ∨ o' + n' ≤ o)
    (hs : ∀ p, ¬InRange (fb m0 + BitVec.ofNat 64 o') n' p → d'.get? p = d.get? p) {v : UInt64}
    (h : WordAt d (fb m0 + BitVec.ofNat 64 o) v) : WordAt d' (fb m0 + BitVec.ofNat 64 o) v :=
  NativeRustcVm.Layout.WordAt.of_same h (n := 8) (fun j hj ↦ by
    rw [addr_add_add]
    exact hs _ (NativeRustcVm.not_inRange_sub (fb_noWrap hF) ho' (by omega) (by omega)))
    (Nat.le_refl _)

omit [Labels] in
/-- The callee's stack below the frame is off the stack's top `80` bytes. -/
theorem callee_not_top {m0 st : MachineData} {n' : Nat} (hsp1 : 5136 ≤ m0.regs.SP.toNat)
    (hn : 5136 + n' ≤ m0.regs.SP.toNat)
    (hsp : st.regs.SP.toBitVec = m0.regs.SP.toBitVec - BitVec.ofNat 64 5136) {p : BitVec 64}
    (h : InRange (stackBelow st n') n' p) :
    ¬InRange (m0.regs.SP.toBitVec - BitVec.ofNat 64 80) 80 p := by
  have e1 := sp_toNat_sub (m0 := m0) hsp1
  have e2 : (stackBelow st n').toNat = m0.regs.SP.toNat - 5136 - n' := by
    unfold stackBelow
    rw [hsp, Arrays.toNat_sub_ofNat (by rw [e1]; omega), e1]
  have hnw : NoWrap (stackBelow st n') n' := by
    unfold NoWrap; rw [e2]; have := m0.regs.SP.toNat_lt; omega
  exact not_top_of_low (by omega) hnw (by rw [e2]; omega) h

/-- A word of the frame off the `n'` bytes from `o'` and the callee's stack that a call
changed. -/
theorem frame_keep_call {m0 st st' : MachineData} (hF : Facts m0)
    (hsp : st.regs.SP.toBitVec = fb m0) {n'' : Nat} (hle : 5136 + n'' ≤ SS) {o o' n' : Nat}
    (ho : o + 8 ≤ 5136) (ho' : o' + n' ≤ 5136) (hd : o + 8 ≤ o' ∨ o' + n' ≤ o)
    (hs : Changes st st' n'' (fb m0 + BitVec.ofNat 64 o') n') {v : UInt64}
    (h : WordAt st.dmem (fb m0 + BitVec.ofNat 64 o) v) :
    WordAt st'.dmem (fb m0 + BitVec.ofNat 64 o) v :=
  NativeRustcVm.Layout.WordAt.of_same h (n := 8) (fun j hj ↦ by
    rw [addr_add_add]
    exact hs _ fun h' ↦ h'.elim
      (NativeRustcVm.not_inRange_sub (fb_noWrap hF) ho' (by omega) (by omega))
      (callee_below (F := 5136) hF.stack hsp hle (by omega)))
    (Nat.le_refl _)

/-- The registers the blocks keep. -/
structure Keep (m0 st : MachineData) : Prop where
  x19 : st.regs.X19 = m0.regs.X0
  x20 : st.regs.X20 = m0.regs.X1
  x23 : st.regs.X23.toBitVec = rodataAddr .keccakSlot
  x24 : st.regs.X24.toBitVec = rodataAddr .keccakOutput

theorem Keep.of {m0 st st' : MachineData} (h : Keep m0 st)
    (e19 : st'.regs.getXReg .X19 = st.regs.getXReg .X19)
    (e20 : st'.regs.getXReg .X20 = st.regs.getXReg .X20)
    (e23 : st'.regs.getXReg .X23 = st.regs.getXReg .X23)
    (e24 : st'.regs.getXReg .X24 = st.regs.getXReg .X24) : Keep m0 st' :=
  ⟨e19.trans h.x19, e20.trans h.x20, by rw [show st'.regs.X23 = _ from e23]; exact h.x23,
    by rw [show st'.regs.X24 = _ from e24]; exact h.x24⟩

theorem I1.keep {m0 st : MachineData} {c j : Nat} (h : I1 m0 c j st) : Keep m0 st :=
  ⟨h.x19, h.x20, h.x23, h.x24⟩

omit [Labels] in
/-- The offsets `stack_offsets` wrote, each the model's. -/
theorem ow_word {d : Mem 64} {a : BitVec 64} (κ : Nat → Nat)
    (h : WordsAt d a (natWords (stackOffsets (sizesOf κ)).1)) {q : Nat}
    (hq : q < blockList.length) :
    WordAt d (a + BitVec.ofNat 64 (8 * q)) (sumF κ (keyF κ blockList[q])).toUInt64 := by
  have hq' : q < (stackOffsets (sizesOf κ)).1.size := by rw [ow_size]; exact hq
  have := NativeRustcVm.wordsAt_iff.mp h q (by simp [natWords, hq'])
  have h1 := ow_getD κ hq
  simp only [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hq', Option.getD_some,
    List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hq] at h1
  simpa [natWords, h1] using this

end

variable [Host] {k : Nat}

/-- **`b8` to `b14`**: the offsets of the stacked columns; at `.L10`. -/
theorem mid (hp : Placed code k) (hms : Spec (Labels.label NativeRustcVmArm.Vm.Memset.entryLabel) MemsetPre MemsetPost)
    (hso : Spec (Labels.label NativeRustcVmArm.Vm.StackOffsets.entryLabel) StackOffsetsPre StackOffsetsPost)
    {m0 : MachineData} (hF : Facts m0) {st : MachineState} (hpc : st.pc = Host.addrOf (k + NativeRustcVmArm.Vm.PlacementsOf.b8Offset))
    (hI : I1 m0 158 158 st.data) :
    Eventually (step1 Host.exe) (fun s ↦ s.pc = Host.addrOf (k + NativeRustcVmArm.Vm.PlacementsOf.b15Offset) ∧ I2 m0 0 s.data) st := by
  have hS := hF.stack
  have hbl : below 158 = blockList := below_158
  have hn : blockList.length = 94 := blockList_length
  have hle : 5136 + stackOffsetsStack ≤ SS := SS_ge
  -- `b8`: `block_offsets` zeroed
  refine regs_step (infix_of b8_in_code (by simp [b8]) hp) run_b8 (rk run_b8) hI.body hpc
    fun st1 hm1 hpc1 hb1 hd1 hr1 ↦ ?_
  have K1 := hI.keep.of (hr1 .X19 rfl) (hr1 .X20 rfl) (hr1 .X23 rfl) (hr1 .X24 rfl)
  have g0 := hm1.regs .X0 _ rfl
  have g2 := hm1.regs .X2 _ rfl
  sym_simp at g0 g2
  have hsp0 : st.data.regs.SP.toBitVec = fb m0 := hI.body.sp
  refine memset_call hms hF hpc1 hb1 (o := 2528) (n := 1264) (by omega)
    (by
      rw [show st1.data.regs.X0 = st1.data.regs.getXReg .X0 from rfl, g0]
      show st.data.regs.SP.toBitVec + _ = _
      rw [hsp0])
    (by show (st1.data.regs.getXReg .X2).toBitVec.toNat = _; rw [g2]; rfl)
    fun st2 hpc2 hb2 hsv2 hs2 ↦ ?_
  have K2 := K1.of (hsv2 .X19 rfl) (hsv2 .X20 rfl) (hsv2 .X23 rfl) (hsv2 .X24 rfl)
  -- `b9`: room for the stacked columns
  refine regs_step (infix_of b9_in_code (by simp [b9]) hp) run_b9 (rk run_b9) hb2
    (pc_of hpc2 rfl) fun st3 hm3 hpc3 hb3 hd3 hr3 ↦ ?_
  have K3 := K2.of (hr3 .X19 rfl) (hr3 .X20 rfl) (hr3 .X23 rfl) (hr3 .X24 rfl)
  have e22 : (st2.data.regs.getXReg .X22).toBitVec = BitVec.ofNat 64 94 := by
    rw [hsv2 .X22 rfl, hr1 .X22 rfl]
    apply BitVec.eq_of_toNat_eq
    show st.data.regs.X22.toNat = _
    rw [hI.x22, hbl, hn]; rfl
  simp only [PcOk] at hpc3
  sym_simp at hpc3
  rw [show (Env.ofMachine st2.data []).regs .X22 = _ from e22, ofNat_ult' (by omega) (by decide)]
    at hpc3
  have hpc3' := pc_of ((Arrays.pc_cond hpc3).2 (by decide))
    (show k + NativeRustcVmArm.Vm.PlacementsOf.b9Offset + b9.length = k + NativeRustcVmArm.Vm.PlacementsOf.b10Offset from by rw [Nat.add_assoc, NativeRustcVmArm.Vm.PlacementsOf.b9_next])
  -- `b10`: `stack_offsets`
  refine regs_step (infix_of b10_in_code (by simp [b10]) hp) run_b10 (rk run_b10) hb3 hpc3'
    fun st4 hm4 hpc4 hb4 hd4 hr4 ↦ ?_
  have K4 := K3.of (hr4 .X19 rfl) (hr4 .X20 rfl) (hr4 .X23 rfl) (hr4 .X24 rfl)
  have g0 := hm4.regs .X0 _ rfl
  have g1 := hm4.regs .X1 _ rfl
  have g2 := hm4.regs .X2 _ rfl
  have g3 := hm4.regs .X3 _ rfl
  sym_simp at g0 g1 g2 g3
  have hsp3 : st3.data.regs.SP.toBitVec = fb m0 := hb3.sp
  have x0 : st4.data.regs.X0.toBitVec = fb m0 + BitVec.ofNat 64 1264 := by
    rw [show st4.data.regs.X0 = st4.data.regs.getXReg .X0 from rfl, g0]
    show st3.data.regs.SP.toBitVec + _ = _
    rw [hsp3]
  have x2 : st4.data.regs.X2.toBitVec = fb m0 + BitVec.ofNat 64 2528 := by
    rw [show st4.data.regs.X2 = st4.data.regs.getXReg .X2 from rfl, g2]
    show st3.data.regs.SP.toBitVec + _ = _
    rw [hsp3]
  have x1 : st4.data.regs.X1.toNat = 94 := by
    show (st4.data.regs.getXReg .X1).toBitVec.toNat = _
    rw [g1]
    show (st3.data.regs.getXReg .X22).toBitVec.toNat = _
    rw [hr3 .X22 rfl, e22]; rfl
  have x3 : st4.data.regs.X3.toNat = 158 := by
    show (st4.data.regs.getXReg .X3).toBitVec.toNat = _; rw [g3]; rfl
  have hsz4 : ∀ q (h : q < blockList.length), WordAt st4.data.dmem
      (fb m0 + BitVec.ofNat 64 (1264 + 8 * q)) (κ m0 blockList[q]).toUInt64 := fun q h ↦ by
    rw [hd4, hd3]
    refine frame_keep hF (o' := 2528) (n' := 1264) (by omega) (by omega) (by omega) hs2 ?_
    rw [hd1]
    have := hI.sizes q (by rw [hbl]; exact h)
    simpa only [hbl] using this
  have hsizes : natsOf st4.data st4.data.regs.X0 st4.data.regs.X1.toNat = sizesOf (κ m0) := by
    rw [x1]
    refine natsOf_of_words ?_ (fun x hx ↦ ?_) (by rw [sizesOf_size, hn])
    · rw [x0]
      refine wordsAt_natWords fun t ht ↦ ?_
      rw [sizesOf_size] at ht
      rw [addr_add_add]
      simpa [sizesOf] using hsz4 t ht
    · simp only [sizesOf, List.mem_toArray, List.mem_map] at hx
      obtain ⟨c, hc, rfl⟩ := hx
      have := hF.κ_le (lt_of_mem_blockList hc)
      omega
  have hpre : StackOffsetsPre st4.data := by
    refine ⟨stackOk_body hS hb4 (by decide) hle, by rw [x1]; decide, ?_, ?_, ?_, ?_, ?_⟩
    · rw [x0, x1]; exact frame_readable hF hb4 (by omega)
    · rw [x0, x1]; exact frame_apart_callee (F := 5136) hS hb4.sp hle (by omega)
    · rw [x2, x3]; exact frame_readable hF hb4 (by omega)
    · rw [x2, x3]; exact frame_apart_callee (F := 5136) hS hb4.sp hle (by omega)
    · rw [x0, x1, x2, x3]; exact frame_apart hF (by omega) (by omega) (by omega)
  refine call_then hpc4 hso hpre fun st5 hpc5 hpost ↦ ?_
  obtain ⟨hres, hch, hsv5⟩ := hpost
  have hcond : st4.data.regs.X1.toNat ≤ st4.data.regs.X3.toNat ∧
      OffsetsFit (natsOf st4.data st4.data.regs.X0 st4.data.regs.X1.toNat) := by
    rw [hsizes, x1, x3]; exact ⟨by decide, fit (κ m0) fun c hc ↦ hF.κ_le hc⟩
  rw [ite_eq_left hcond] at hres
  obtain ⟨r0, r1, rw5⟩ := hres
  rw [hsizes, ow_snd] at r1
  rw [hsizes, x2] at rw5
  rw [x2, x3] at hch
  have K5 := K4.of (hsv5.1 .X19 rfl) (hsv5.1 .X20 rfl) (hsv5.1 .X23 rfl) (hsv5.1 .X24 rfl)
  have hb5 : Bd m0 st5.data := Body.of_call_stack (G := 80) hb4 hch (fun p hp ↦ by
      rcases hp with hp | hp
      · obtain ⟨a1, a2⟩ := frame_low hF (o := 2528) (n := 8 * 158) (by omega) hp
        exact ⟨.inr a1, a2⟩
      · exact ⟨.inr (callee_stack (F := 5136) hS hb4.sp hle hp),
          callee_not_top hF.sp (by have := hS.2.1; omega) hb4.sp hp⟩)
    hsv5 slots_top (by decide) hF.sp
  -- `b11`: `Some`
  refine regs_step (infix_of b11_in_code (by simp [b11]) hp) run_b11 (rk run_b11) hb5
    (pc_of hpc5 rfl) fun st6 hm6 hpc6 hb6 hd6 hr6 ↦ ?_
  have K6 := K5.of (hr6 .X19 rfl) (hr6 .X20 rfl) (hr6 .X23 rfl) (hr6 .X24 rfl)
  simp only [PcOk] at hpc6
  sym_simp at hpc6
  have e0 : (Env.ofMachine st5.data []).regs .X0 = 1#64 := congrArg UInt64.toBitVec r0
  rw [e0] at hpc6
  have hpc6' := pc_of ((Arrays.pc_cond hpc6).2 (by decide))
    (show k + NativeRustcVmArm.Vm.PlacementsOf.b11Offset + b11.length = k + NativeRustcVmArm.Vm.PlacementsOf.b12Offset from by rw [Nat.add_assoc, NativeRustcVmArm.Vm.PlacementsOf.b11_next])
  -- `b12`: the total's log-size kept, `offsets` zeroed
  refine regs_step (infix_of b12_in_code (by simp [b12]) hp) run_b12 (rk run_b12) hb6 hpc6'
    fun st7 hm7 hpc7 hb7 hd7 hr7 ↦ ?_
  have K7 := K6.of (hr7 .X19 rfl) (hr7 .X20 rfl) (hr7 .X23 rfl) (hr7 .X24 rfl)
  have g0 := hm7.regs .X0 _ rfl
  have g2 := hm7.regs .X2 _ rfl
  have g21 := hm7.regs .X21 _ rfl
  have g25 := hm7.regs .X25 _ rfl
  sym_simp at g0 g2 g21 g25
  have hsp6 : st6.data.regs.SP.toBitVec = fb m0 := hb6.sp
  refine memset_call hms hF hpc7 hb7 (o := 3792) (n := 1264) (by omega)
    (by
      rw [show st7.data.regs.X0 = st7.data.regs.getXReg .X0 from rfl, g0]
      show st6.data.regs.SP.toBitVec + _ = _
      rw [hsp6])
    (by show (st7.data.regs.getXReg .X2).toBitVec.toNat = _; rw [g2]; rfl)
    fun st8 hpc8 hb8 hsv8 hs8 ↦ ?_
  have K8 := K7.of (hsv8 .X19 rfl) (hsv8 .X20 rfl) (hsv8 .X23 rfl) (hsv8 .X24 rfl)
  -- `b13`: some stacked columns
  refine regs_step (infix_of b13_in_code (by simp [b13]) hp) run_b13 (rk run_b13) hb8
    (pc_of hpc8 rfl) fun st9 hm9 hpc9 hb9 hd9 hr9 ↦ ?_
  have K9 := K8.of (hr9 .X19 rfl) (hr9 .X20 rfl) (hr9 .X23 rfl) (hr9 .X24 rfl)
  have e22' : (st8.data.regs.getXReg .X22).toBitVec = BitVec.ofNat 64 94 := by
    rw [hsv8 .X22 rfl, hr7 .X22 rfl, hr6 .X22 rfl, hsv5.1 .X22 rfl, hr4 .X22 rfl, hr3 .X22 rfl]
    exact e22
  simp only [PcOk] at hpc9
  sym_simp at hpc9
  rw [show (Env.ofMachine st8.data []).regs .X22 = _ from e22'] at hpc9
  have hpc9' := pc_of ((Arrays.pc_cond hpc9).2 (by decide))
    (show k + NativeRustcVmArm.Vm.PlacementsOf.b13Offset + b13.length = k + NativeRustcVmArm.Vm.PlacementsOf.b14Offset from by rw [Nat.add_assoc, NativeRustcVmArm.Vm.PlacementsOf.b13_next])
  -- `b14`: to `.L10`
  refine regs_step (infix_of b14_in_code (by simp [b14]) hp) run_b14 (rk run_b14) hb9 hpc9'
    fun st10 hm10 hpc10 hb10 hd10 hr10 ↦ ?_
  have K10 := K9.of (hr10 .X19 rfl) (hr10 .X20 rfl) (hr10 .X23 rfl) (hr10 .X24 rfl)
  have g8 := hm10.regs .X8 _ rfl
  have g9 := hm10.regs .X9 _ rfl
  sym_simp at g8 g9
  simp only [PcOk] at hpc10
  have hsp9 : st9.data.regs.SP.toBitVec = fb m0 := hb9.sp
  refine .done _ ⟨pc_of hpc10 rfl, hb10, by omega, ?_, ?_, ?_, K10.x19, K10.x20, ?_, K10.x23,
    K10.x24, ?_, fun q h ↦ ?_, fun q h ↦ ?_, fun q _ hq ↦ absurd hq (Nat.not_lt_zero _)⟩
  · show (st10.data.regs.getXReg .X8).toBitVec = _
    rw [g8]
    show st9.data.regs.SP.toBitVec + _ = _
    rw [hsp9]
  · show (st10.data.regs.getXReg .X9).toBitVec = _
    rw [g9]
    show st9.data.regs.SP.toBitVec = _
    rw [hsp9]; simp
  · show (st10.data.regs.getXReg .X22).toBitVec.toNat = _
    rw [hr10 .X22 rfl, hr9 .X22 rfl, e22']; rfl
  · show (st10.data.regs.getXReg .X21).toBitVec.toNat = _
    rw [hr10 .X21 rfl, hr9 .X21 rfl, hsv8 .X21 rfl, g21]
    show (st6.data.regs.getXReg .X1).toBitVec.toNat = _
    rw [hr6 .X1 rfl]
    exact r1
  · show (st10.data.regs.getXReg .X25).toBitVec = _
    rw [hr10 .X25 rfl, hr9 .X25 rfl, hsv8 .X25 rfl, g25]
    show st6.data.regs.SP.toBitVec + _ = _
    rw [hsp6]
  · rw [hd10, hd9]
    refine frame_keep hF (o' := 3792) (n' := 1264) (by omega) (by omega) (by omega) hs8 ?_
    rw [hd7, hd6]
    refine frame_keep_call hF hb4.sp hle (by omega) (o' := 2528) (n' := 8 * 158) (by omega)
      (by omega) hch ?_
    rw [hd4, hd3]
    refine frame_keep hF (o' := 2528) (n' := 1264) (by omega) (by omega) (by omega) hs2 ?_
    rw [hd1]
    have := hI.cols q (by rw [hbl]; exact h)
    simpa only [hbl] using this
  · rw [hd10, hd9]
    refine frame_keep hF (o' := 3792) (n' := 1264) (by omega) (by omega) (by omega) hs8 ?_
    rw [hd7, hd6, ← addr_add_add]
    exact ow_word (κ m0) rw5 h

end

end NativeRustcVmArm.Layout.PlacementsOf

