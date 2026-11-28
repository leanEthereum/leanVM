module

public import NativeRustcVmArm.Code.Vm.InstanceWeights.Names
public import NativeRustcVmArm.Code.Vm.Memcpy.Names
public import NativeRustcVmArm.Code.Vm.Powers.Names
public import NativeRustcVmArm.KeccakGkr.InstanceWeights.Exec
public import NativeRustcVmArm.KeccakGkr.InstanceWeights.Items
public import NativeRustcVmArm.Spec.Arrays

/-!
# `instance_weights` meets its contract

The prologue (`b0`) saves X19 to X30 in the 976-byte frame, keeps the result's address at `24`,
and calls `powers` into the frame's buffer at `232`. Then, in one environment, `b1`, the fourteen
turns of the loop and the tail (`b3`) sum the powers into the frame's `Buf` at `616`
(`buf_bytes`), which `memcpy` copies to the result; the epilogue (`b4`) returns
(`instanceWeights_spec`).
-/

namespace NativeRustcVmArm.KeccakGkr.InstanceWeights

open NativeRustcArm NativeRustcArm.Sym NativeVm.Model
open NativeRustcVmArm.Vm.InstanceWeights NativeRustcVmArm.Arrays NativeRustcVmArm.Sumcheck
open NativeRustcVm (Region)

@[expose] public section

/-- The prologue's slots. -/
def slots : List (Nat × XReg) :=
  [(968, .X19), (960, .X20), (952, .X21), (944, .X22), (936, .X23), (928, .X24), (920, .X25),
    (912, .X26), (904, .X27), (896, .X28), (880, .X29), (888, .X30)]

/-- The body: the 976-byte frame, the result written. -/
abbrev Body (m0 st : MachineData) : Prop :=
  Frame m0 976 instanceWeightsStack slots [⟨m0.regs.X0.toBitVec, 264⟩] st

end

public section

theorem slots_le : ∀ p ∈ slots, 880 ≤ p.1 ∧ p.1 + 8 ≤ 976 := by decide

theorem slots_le' : ∀ p ∈ slots, p.1 + 8 ≤ 976 := fun p hp ↦ (slots_le p hp).2

theorem all_slots : ∀ r, calleeSaved r = true → r ∉ slots.map (·.2) → r ∈ ([] : List XReg) := by
  intro r hr hn
  exfalso
  apply hn
  cases r <;> simp_all [calleeSaved, slots]

variable [NativeRustcArm.Host] {k : Nat}

/-- **`instance_weights` meets its contract**, given `powers`' and `memcpy`'s. -/
theorem instanceWeights_spec (hp : Placed code k)
    (hpow : Spec (Labels.label NativeRustcVmArm.Vm.Powers.entryLabel) PowersPre PowersPost)
    (hmemcpy : Spec (Labels.label NativeRustcVmArm.Vm.Memcpy.entryLabel) MemcpyPre MemcpyPost) :
    Spec (Labels.label NativeRustcVmArm.Vm.InstanceWeights.entryLabel) InstanceWeightsPre InstanceWeightsPost := by
  intro m0 hpre
  have hl : Labels.label NativeRustcVmArm.Vm.InstanceWeights.entryLabel = Host.addrOf (k + NativeRustcVmArm.Vm.InstanceWeights.b0Offset) := hp.label (j := NativeRustcVmArm.Vm.InstanceWeights.entryOffset) NativeRustcVmArm.Vm.InstanceWeights.entry_at
  rw [hl]
  obtain ⟨hS, hA⟩ := hpre
  have h976 : 976 ≤ instanceWeightsStack := by decide
  have hN : instanceWeightsStack ≤ m0.regs.SP.toBitVec.toNat := hS.2.1
  have hSP := m0.regs.SP.toBitVec.isLt
  obtain ⟨hmap, hnw, hfb⟩ := frame_ok hS h976
  generalize hfbd : m0.regs.SP.toBitVec - BitVec.ofNat 64 976 = fb at hmap hnw hfb
  have hfok : Region.Ok m0.dmem ⟨fb, 976⟩ := ⟨hmap, hnw⟩
  have hws := wsOff_of_areas hA hS
  set out := m0.regs.X0.toBitVec with hout
  set s : EW := ⟨m0.regs.X1, m0.regs.X2⟩ with hs
  have hook := Areas.ok hA (r := ⟨out, 264⟩) (Or.inl (by simp))
  -- the prologue
  have hmA : Match (Env.ofMachine m0 [(fb, 976)]) entryS m0 :=
    match_ofMachine ⟨rfl, fun _ ↦ hfbd ▸ frame_aligned hS h976 rfl, trivial⟩
      (by
        show _ = fb + BitVec.ofInt 64 976
        rw [show BitVec.ofInt 64 976 = BitVec.ofNat 64 976 from rfl, ← hfbd, BitVec.sub_add_cancel])
      trivial trivial trivial trivial
  refine exec_then (b0_in_code.trans hp.1 (by simp [b0])) e0 (wf_one hmap hnw) hmA
    fun s1 hm1 hpc1 ↦ ?_
  have hb1 : Body m0 s1.data :=
    Frame.of_entry hS h976 (hfbd ▸ hm1) rfl (by decide +kernel)
      (fun r hr hn ↦ absurd (all_slots r (by
        simp only [calleeRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with h | h | h | h | h | h | h | h | h | h | h <;> subst h <;> rfl) hn) (by simp))
      (by decide +kernel)
  have hsp1 : s1.data.regs.SP.toBitVec = fb := hb1.sp.trans hfbd
  have h0 := hm1.regs .X0 _ rfl
  have h1 := hm1.regs .X1 _ rfl
  have h2 := hm1.regs .X2 _ rfl
  have h3 := hm1.regs .X3 _ rfl
  have hx0 : s1.data.regs.X0 = m0.regs.X1 := UInt64.toBitVec_inj.mp h0
  have hx1 : s1.data.regs.X1 = m0.regs.X2 := UInt64.toBitVec_inj.mp h1
  have hx2 : s1.data.regs.X2.toBitVec = fb + BitVec.ofNat 64 232 := h2
  have hx3 : s1.data.regs.X3.toNat = 24 := by
    show (s1.data.regs.getXReg .X3).toBitVec.toNat = 24
    rw [h3]; rfl
  have hsave1 : NativeRustcVm.WordAt s1.data.dmem (fb + BitVec.ofNat 64 24) m0.regs.X0 := by
    have h := Sumcheck.Match.wordAt_write hm1 (r := 0) (o := 24) (v := .reg .X0) rfl (by decide)
      (by decide +kernel)
    rwa [show UInt64.ofBitVec (Sym.eval (Env.ofMachine m0 [(fb, 976)]) (.reg .X0)) = m0.regs.X0 from
      UInt64.ofBitVec_toBitVec _] at h
  -- `powers` into the frame's buffer
  have hbuf_ok := sub_ok hfok (o := 232) (n := 384) (by decide)
  refine call_then hpc1 hpow ⟨hb1.stackOk hS (by decide) (by decide), ?_, ?_⟩ fun s2 hpc2 hpost2 ↦ ?_
  · rw [hx2, hx3]
    exact ⟨Mapped.kept' hbuf_ok.1 hb1.kept, hbuf_ok.2⟩
  · show Apart s1.data.regs.X2.toBitVec (16 * s1.data.regs.X3.toNat)
      (s1.data.regs.SP.toBitVec - BitVec.ofNat 64 powersStack) powersStack
    rw [hx2, hx3, hsp1]
    have hP : 976 + powersStack ≤ instanceWeightsStack := by decide
    unfold Apart
    right
    rw [NativeRustcVm.toNat_add_ofNat (by omega), BitVec.toNat_sub_of_le (by
      rw [BitVec.le_def, BitVec.toNat_ofNat]; omega), BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (by decide)]
    omega
  obtain ⟨hpw, hch, hsv2⟩ := hpost2
  rw [hx2, hx3, hx0, hx1] at hpw
  rw [hx2, hx3] at hch
  have hb2 : Body m0 s2.data :=
    hb1.call_local (n := powersStack) (lo := 880) hS (by decide) slots_le (by decide) hws hch
      (fun p h ↦ by
        rcases h with h | h
        · exact Or.inr (Or.inr (hfbd ▸ inRange_mono h (by decide)))
        · exact Or.inl h) hsv2
  have hsave2 : NativeRustcVm.WordAt s2.data.dmem (fb + BitVec.ofNat 64 24) m0.regs.X0 :=
    NativeRustcVm.BytesAt.of_sameOutside hsave1 hch fun i hi hR ↦ by
      rw [NativeRustcVm.length_wordBytes] at hi
      rw [NativeRustcVm.addr_add_add] at hR
      rcases hR with hR | hR
      · unfold InRange at hR
        rw [show fb + BitVec.ofNat 64 (24 + i) - (fb + BitVec.ofNat 64 232) =
          BitVec.ofNat 64 (2 ^ 64 - 208 + i) by bv_omega, BitVec.toNat_ofNat] at hR
        omega
      · unfold stackBelow at hR
        rw [hsp1] at hR
        exact not_inRange_below (by simp only [powersStack, ewMulStack]; omega) hR
  -- `b1`, the loop and the tail
  have hfm2 : NativeRustcVm.Mapped s2.data.dmem fb 976 := Mapped.kept' hmap hb2.kept
  have hwfB : (Env.ofMachine s2.data [(fb, 976)]).WF := wf_one hfm2 hnw
  have hmB : Match (Env.ofMachine s2.data [(fb, 976)]) bodyS s2.data :=
    match_ofMachine ⟨rfl, fun _ ↦ hfbd ▸ frame_aligned hS h976 rfl, trivial⟩
      (by rw [hb2.sp, hfbd]; simp [Sym.eval]) trivial trivial trivial trivial
  refine exec_at (b1_in_code.trans hp.1 (by simp [b1])) e1 hwfB hpc2 hmB fun s3 hm3 hpc3 ↦ ?_
  have hm3' : Match (Env.ofMachine s2.data [(fb, 976)]) (it 0) s3.data := by
    rw [it_zero, after_eq e1]; exact hm3
  simp only [PcOk, NativeRustcVmArm.Vm.InstanceWeights.b1_length, NativeRustcVmArm.Vm.InstanceWeights.b1Length] at hpc3
  refine (Sym.loop (Q := fun s' ↦ s'.pc = Host.addrOf (k + NativeRustcVmArm.Vm.InstanceWeights.b3Offset) ∧
      Match (Env.ofMachine s2.data [(fb, 976)]) (it 14) s'.data)
    (fun n s ↦ ∃ j, n = 14 - j ∧ j < 14 ∧ s.pc = Host.addrOf (k + NativeRustcVmArm.Vm.InstanceWeights.b2Offset) ∧
      Match (Env.ofMachine s2.data [(fb, 976)]) (it j) s.data)
    (fun _ s ⟨j, hn, hj, hpc, hm⟩ ↦ exec_at (b2_in_code.trans hp.1 (by simp [b2])) (loop_exec hj)
      hwfB hpc hm fun s' hm' hpc' ↦ by
        simp only [PcOk, SBool.eval, NativeRustcVmArm.Vm.InstanceWeights.b2_length, NativeRustcVmArm.Vm.InstanceWeights.b2Length] at hpc'
        by_cases hlast : j = 13
        · subst hlast
          exact .done _ (Or.inl ⟨by simpa [b2Offset, b3Offset] using hpc', hm'⟩)
        · have hc : (j != 13) = true := by simpa using hlast
          simp only [hc, ite_true] at hpc'
          exact .done _ (Or.inr ⟨14 - (j + 1), by omega, j + 1, rfl, by omega,
            hpc'.trans (hp.label (j := NativeRustcVmArm.Vm.InstanceWeights.b2Offset) NativeRustcVmArm.Vm.InstanceWeights.label_1_at), hm'⟩))
    ⟨0, rfl, by decide, by simpa [b1Offset, b2Offset] using hpc3, hm3'⟩).bind fun s4 ⟨hpc4, hm4⟩ ↦ ?_
  refine exec_at (b3_in_code.trans hp.1 (by simp [b3])) e3 hwfB hpc4 hm4 fun s5 hm5 hpc5 ↦ ?_
  have hm5' : Match (Env.ofMachine s2.data [(fb, 976)]) (after b3 (it 14)) s5.data := by
    rw [after_eq e3]; exact hm5
  have hb5 : Body m0 s5.data :=
    hb2.write_local (lo := 880) hS h976 slots_le (by decide) hws hmB hm5' hwfB rfl all_slots
      (by rw [after_eq e3]; decide +kernel)
      fun p hw ↦ Or.inr (hfbd ▸ Written.inRange_le (r := 0) rfl hnw (by decide) tail_ok.2 hw)
  have hbuf : NativeRustcVm.BytesAt s5.data.dmem (fb + BitVec.ofNat 64 616) (bufBytes s) :=
    buf_bytes hm5' tail_ok.1 hpw
  have hr0 := hm5'.regs .X0 (.load 0 24 8) (by rw [after_eq e3]; rfl)
  have hr1 := hm5'.regs .X1 (.ptr 0 616) (by rw [after_eq e3]; rfl)
  have hr2 := hm5'.regs .X2 (.lit 264) (by rw [after_eq e3]; rfl)
  have hy0 : s5.data.regs.X0.toBitVec = out := by
    show (s5.data.regs.getXReg .X0).toBitVec = _
    rw [hr0]
    exact load_word (env := Env.ofMachine s2.data [(fb, 976)]) (r := 0) hsave2
  have hy1 : s5.data.regs.X1.toBitVec = fb + BitVec.ofNat 64 616 := hr1
  have hy2 : s5.data.regs.X2.toNat = 264 := by
    show (s5.data.regs.getXReg .X2).toBitVec.toNat = 264
    rw [hr2]; rfl
  -- `memcpy` to the result
  have hfr_ok := sub_ok hfok (o := 616) (n := 264) (by decide)
  have hap : Apart out 264 (fb + BitVec.ofNat 64 616) 264 := by
    have h := Areas.apart_stack hA (w := ⟨out, 264⟩) (by simp)
    have e : fb + BitVec.ofNat 64 616 =
        stackBelow m0 instanceWeightsStack + BitVec.ofNat 64 (instanceWeightsStack - 976 + 616) := by
      rw [← hfbd]; unfold stackBelow; bv_omega
    rw [e]
    have := Apart.sub (o := 0) (n := 264) (o' := instanceWeightsStack - 976 + 616) (n' := 264) h
      hook.2 (noWrap_stackBelow hS) (by show 0 + 264 ≤ 264; omega)
      (by simp only [instanceWeightsStack, powersStack, ewMulStack]; omega) (by decide) (by decide)
    rwa [NativeRustcVm.addr_add_zero] at this
  refine call_then hpc5 hmemcpy ⟨?_, ?_, ?_, ?_, ?_⟩ fun s6 hpc6 hpost6 ↦ ?_
  · rw [hy0, hy2]; exact Mapped.kept' hook.1 hb5.kept
  · rw [hy1, hy2]; exact Mapped.kept' hfr_ok.1 hb5.kept
  · rw [hy0, hy2]; exact hook.2
  · rw [hy1, hy2]; exact hfr_ok.2
  · rw [hy0, hy1, hy2]; exact hap
  obtain ⟨-, hcp, hsame6, hsv6⟩ := hpost6
  rw [hy0, hy1, hy2, ← bufBytes_length s, bytesOf_eq hbuf] at hcp
  rw [hy0, hy2] at hsame6
  have hb6 : Body m0 s6.data :=
    hb5.call (n := 0) hS (by decide) slots_le' hws hsame6
      (fun p h ↦ Or.inr ⟨⟨out, 264⟩, List.mem_singleton.mpr rfl, h⟩) hsv6
  -- the epilogue
  have hwfC : (Env.ofMachine s6.data [(fb, 976)]).WF := wf_one (Mapped.kept' hmap hb6.kept) hnw
  have hmC : Match (Env.ofMachine s6.data [(fb, 976)]) bodyS s6.data :=
    match_ofMachine ⟨rfl, fun _ ↦ hfbd ▸ frame_aligned hS h976 rfl, trivial⟩
      (by rw [hb6.sp, hfbd]; simp [Sym.eval]) trivial trivial trivial trivial
  refine exec_at (b4_in_code.trans hp.1 (by simp [b4])) e4 hwfC hpc6 hmC fun s7 hm7 hpc7 ↦
    .done _ ?_
  obtain ⟨hsaved, hx30, hdm⟩ := hb6.saved (hfbd ▸ hm7) (hfbd ▸ hwfC)
    (List.mem_map.mpr ⟨(888, .X30), by simp [slots], rfl⟩) (by decide +kernel) rfl
  refine ⟨?_, ⟨?_, ?_, ?_⟩, fun p hp' ↦ ?_, hsaved⟩
  · simp only [PcOk] at hpc7
    rw [hpc7]
    simp only [retOf, hx30]
  · rw [Array.length_toList, iw_size]
  · rw [hdm, Array.length_toList, iw_size]
    exact (NativeRustcVm.bytesAt_append_iff.mp hcp).1
  · rw [hdm]
    have := (NativeRustcVm.bytesAt_append_iff.mp hcp).2
    rwa [NativeRustcVm.length_wordBytes] at this
  · rw [hdm]; exact hb6.same p hp'

end

end NativeRustcVmArm.KeccakGkr.InstanceWeights
