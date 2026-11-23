module

public import NativeRustcVmX64.KeccakGkr.Common
public import NativeRustcVmX64.KeccakGkr.InstanceWeights.Exec
public import NativeRustcVmX64.KeccakGkr.InstanceWeights.Items
public import NativeRustcX64.Got
public import NativeRustcVmX64.Code.Vm.InstanceWeights.Names
public import NativeRustcVmX64.Code.Vm.Memcpy.Names
public import NativeRustcVmX64.Code.Vm.Powers.Names

/-!
# `instance_weights` on x86-64

**`instanceWeights_spec`**: the prologue (`b0`) pushes RBP to RBX, reserves 984 bytes, keeps the
result's address at `512` and calls `powers` into the frame's buffer at `112`. Then, in one
environment, `b1`, the fourteen turns of the loop and the tail (`b3`) sum the powers into the
frame's `Buf` at `736` (`buf_bytes`), which `memcpy` copies to the result; the epilogue (`b4`)
returns. Region 0 is the 1048 bytes below the entry's RSP and the return address: the body's RSP
at offset `16`, its calls' return address at `8`, and eight unused bytes at `0`.
-/

namespace NativeRustcVmX64.KeccakGkr.InstanceWeights

open NativeRustcX64 NativeRustcX64.Sym NativeVm.Model NativeRustcVmX64.Transcript
open NativeRustcVmX64.Vm.InstanceWeights
open NativeRustcVm.Transcript (off off_add off_off toNat_off inRange_off_iff inRange_off_self
  inRange_iff' not_inRange_of_apart Mapped.keeps bytesAt_congr)
open NativeRustcVm (Region)

public section

theorem slots_le : ∀ p ∈ slots, p.1 + 8 ≤ 1048 := by decide

theorem slots_ge : ∀ p ∈ slots, 1000 ≤ p.1 := by decide

variable [Host] {k : Nat}

/-- **`instance_weights` meets its contract**, given `powers`' and `memcpy`'s. -/
theorem instanceWeights_spec (hp : Placed code k)
    (hpow : Spec (Labels.label NativeRustcVmX64.Vm.Powers.entryLabel) PowersPre PowersPost)
    (hmemcpy : Spec (Labels.label NativeRustcVmX64.Vm.Memcpy.entryLabel) MemcpyPre MemcpyPost) :
    Spec (Labels.label NativeRustcVmX64.Vm.InstanceWeights.entryLabel) InstanceWeightsPre InstanceWeightsPost := by
  rintro m0 ⟨hst, hA, hgot⟩
  set out := reg m0 .rdi with hout
  set fb := stackBelow m0 1048 with hfb
  have hn : instanceWeightsStack ≤ (rspOf m0).toNat := hst.1
  have h8 : (rspOf m0).toNat + 8 ≤ 2 ^ 64 := hst.2.1
  have hN : 1048 ≤ instanceWeightsStack := by decide
  have hfnw : NativeRustcVm.NoWrap fb (1048 + 8) := frame_noWrap hst hN
  have hfnw' : fb.toNat + 1056 ≤ 2 ^ 64 := hfnw
  have hfnw1 : NativeRustcVm.NoWrap fb 1048 := by unfold NativeRustcVm.NoWrap; omega
  have hfmap := frame_mapped hst hN
  have hok : Region.Ok m0.dmem ⟨out, 264⟩ := Areas.ok hA (r := ⟨out, 264⟩) (by simp)
  have hoS : NativeRustcVm.Apart out 264 (stackBelow m0 instanceWeightsStack)
      (instanceWeightsStack + 8) := Areas.apart_stack hA (w := ⟨out, 264⟩) (by simp)
  have hoF : NativeRustcVm.Apart out 264 fb (1048 + 8) := apart_frame hoS hn hN
  have hoF' : out.toNat + 264 ≤ fb.toNat ∨ fb.toNat + 1056 ≤ out.toNat := hoF
  have hon : out.toNat + 264 ≤ 2 ^ 64 := hok.2
  have hfS : ∀ q, NativeRustcVm.InRange fb 1048 q →
      NativeRustcVm.InRange (stackBelow m0 instanceWeightsStack) instanceWeightsStack q :=
    fun q h ↦ inRange_frame_stack h8 hn hN h
  have hfo : ∀ j < 1056, ¬ NativeRustcVm.InRange out 264 (off fb j) := fun j hj ↦
    not_inRange_of_apart (Apart.symm' hoF) hfnw hok.2 (inRange_off_self hj (by omega))
  -- `b0`: the prologue, `call powers`.
  have hwf0 := frame_wf (m0 := m0) (d := m0) (F := 1048) (rest := []) (vars := fun _ ↦ 0)
    (ret := (Host.addrOf (k + NativeRustcVmX64.Vm.InstanceWeights.b0Offset + b0.length)).toBitVec) ⟨hfmap, hfnw⟩ (by simp)
    (List.pairwise_singleton _ _)
  unfold NativeRustcVmX64.Vm.InstanceWeights.entryLabel
  rw [hp.label NativeRustcVmX64.Vm.InstanceWeights.entry_at]
  refine exec_then (infix_of b0_in_code (by simp [b0]) hp) exit_b0 hwf0 (fun _ _ ↦ rfl)
    (match_ofMachine ⟨rfl, trivial⟩ ⟨match_rsp, trivial⟩ trivial trivial trivial)
    fun st1 hm1 hpc1 => ?_
  obtain ⟨hpro, hws1, hsave, hx7, hx6, hx2, hx1⟩ := ok_b0
  have hf1 : Frame m0 1048 slots 8 st1.data :=
    Frame.of_prologue Frame.entry hwf0 hm1 hpro slots_le (by decide)
  have hs1 : NativeRustcVm.SameOutside m0.dmem st1.data.dmem (NativeRustcVm.InRange fb 1048) :=
    sameOutside_low hwf0 hm1 (r := 0) rfl (by decide) hws1
  have hsp1 : rspOf st1.data = stackBelow m0 1040 := by
    rw [hf1.sp, off_stackBelow (by decide)]
  have hsv1 := wordAt_write hm1 (r := 0) (o := 512) rfl (by decide) hsave
  rw [show UInt64.ofBitVec ((Sym.reg .rdi).eval
    (frameEnv m0 m0 1048 [] (fun _ ↦ 0) (Host.addrOf (k + NativeRustcVmX64.Vm.InstanceWeights.b0Offset + b0.length)).toBitVec)) =
      UInt64.ofBitVec out from rfl] at hsv1
  have hX7 : reg st1.data .rdi = reg m0 .rsi := hm1.regs .rdi _ hx7
  have hX6 : reg st1.data .rsi = reg m0 .rdx := hm1.regs .rsi _ hx6
  have hX2 : reg st1.data .rdx = off fb 112 := (hm1.regs .rdx _ hx2).trans (eval_ptr0 112)
  have hX1 : reg st1.data .rcx = BitVec.ofNat 64 24 := hm1.regs .rcx _ hx1
  -- `powers` into the frame's buffer.
  have hcS : 1040 + powersStack ≤ instanceWeightsStack := by decide
  have hcal2 : ∀ q, NativeRustcVm.InRange (stackBelow st1.data powersStack) powersStack q →
      NativeRustcVm.InRange (stackBelow m0 instanceWeightsStack) instanceWeightsStack q ∧
        ¬ NativeRustcVm.InRange (stackBelow m0 1040) (1040 + 8) q :=
    fun q hq ↦ inRange_callee hsp1 h8 hn hcS hq
  have hfbn : fb.toNat = (rspOf m0).toNat - 1048 := stackBelow_toNat (by omega)
  have hpre1 : PowersPre st1.data := by
    unfold PowersPre SliceOk Readable OffStack
    rw [hX2, hX1, show (BitVec.ofNat 64 24).toNat = 24 from rfl]
    refine ⟨stackOk_callee hst hf1.kept hsp1 hcS,
      ⟨mapped_off (Mapped.keeps hfmap hf1.kept) (by decide), ?_⟩, ?_⟩
    · show (off fb 112).toNat + 384 ≤ 2 ^ 64
      rw [toNat_off (by omega)]; omega
    · show (off fb 112).toNat + 384 ≤ (stackBelow st1.data powersStack).toNat ∨
        (stackBelow st1.data powersStack).toNat + (powersStack + 8) ≤ (off fb 112).toNat
      have hiw : instanceWeightsStack = 1040 + powersStack := rfl
      rw [toNat_off (by omega), stackBelow_callee hsp1 (by omega),
        stackBelow_toNat (m := m0) (n := 1040 + powersStack) (by omega)]
      omega
  refine call_then hpc1 hpow hpre1 fun st2 hpc2 hrsp2 ⟨hpw, hch, hsv2⟩ => ?_
  rw [hX2, hX1, hX7, hX6, show (BitVec.ofNat 64 24).toNat = 24 from rfl] at hpw
  have hch' : NativeRustcVm.SameOutside st1.data.dmem st2.data.dmem (fun q ↦
      NativeRustcVm.InRange (off fb 112) 384 q ∨
        NativeRustcVm.InRange (stackBelow st1.data powersStack) powersStack q) := by
    have := hch
    unfold Changes at this
    rwa [hX2, hX1] at this
  have hslot : ∀ j, 496 ≤ j → j < 1056 → ¬ (NativeRustcVm.InRange (off fb 112) 384 (off fb j) ∨
      NativeRustcVm.InRange (stackBelow st1.data powersStack) powersStack (off fb j)) := by
    rintro j hj1 hj2 (h | h)
    · rw [inRange_off_iff (by omega) (by omega)] at h; omega
    · refine (hcal2 _ h).2 ?_
      rw [hfb, off_frame_sub (o := 8) (by decide) (by omega)]
      exact inRange_off_self (by omega) (by omega)
  have hf2 : Frame m0 1048 slots 16 st2.data :=
    Frame.call_at hf1 hsv2 hrsp2 hch'
      (fun p hp i hi ↦ hslot _ (by have := slots_ge p hp; omega)
        (by have := slots_le p hp; omega))
      (fun j hj ↦ hslot _ (by omega) (by omega))
  have hso2 : NativeRustcVm.SameOutside m0.dmem st2.data.dmem
      (NativeRustcVm.InRange (stackBelow m0 instanceWeightsStack) instanceWeightsStack) := by
    intro q hq
    rw [hch' q ?_]
    · exact hs1 q fun h ↦ hq (hfS q h)
    rintro (h | h)
    · exact hq (hfS q (inRange_of_off hfnw1 (by decide) h))
    · exact hq (hcal2 q h).1
  have hsv2' : NativeRustcVm.WordAt st2.data.dmem (off fb 512) (UInt64.ofBitVec out) :=
    bytesAt_congr hsv1 fun i hi ↦ by
      have hi' : i < 8 := by simpa [LeanVM.Protocol.KeccakHash.wordBytes] using hi
      rw [off_add]
      exact hch' _ (hslot _ (by omega) (by omega))
  -- `b1`, the loop and the tail, in one environment.
  have hg := hgot.1 "memcpy" (by simp)
  have hgF : NativeRustcVm.Apart (gotAddr "memcpy") 8 fb 1056 :=
    apart_frame hg.2.2.1 hn hN
  have hgot2 := hgot.unchanged hst
    (by
      intro a ha
      simp only [List.mem_singleton] at ha
      subst a
      exact hok.2)
    (hso2.mono fun _ h ↦ Or.inl h)
  have hwf2 := frame_wf (m0 := m0) (d := st2.data) (F := 1048)
    (rest := [(gotAddr "memcpy", 8)]) (vars := fun _ ↦ 0)
    (ret := (Host.addrOf (k + NativeRustcVmX64.Vm.InstanceWeights.b3Offset + b3.length)).toBitVec)
    ⟨Mapped.keeps hfmap hf2.kept, hfnw⟩
    (by
      intro r hr
      simp only [List.mem_singleton] at hr
      subst r
      exact ⟨Mapped.keeps (hgot.mapped (by simp)) hf2.kept, hg.2.1⟩)
    (List.pairwise_pair.mpr (Apart.symm' hgF))
  have hm2 : Match
      (frameEnv m0 st2.data 1048 [(gotAddr "memcpy", 8)] (fun _ ↦ 0)
        (Host.addrOf (k + NativeRustcVmX64.Vm.InstanceWeights.b3Offset + b3.length)).toBitVec)
      bodyS st2.data := by
    apply Match.withKnownBytes
    · exact match_ofMachine ⟨rfl, rfl, trivial⟩ ⟨hf2.rsp_eval, trivial⟩ trivial trivial
        ⟨by simp [Sym.eval, Env.base, gotAddr], trivial⟩
    · intro i hi
      simp only [Nat.zero_add, Sym.eval, Env.base_ofMachine_eq, Env.ofMachine_mem0]
      change st2.data.dmem.get? (gotAddr "memcpy" + BitVec.ofNat 64 i) = _
      rw [hgot2 "memcpy" (by simp) i hi]
      exact hgot.byte (by simp) hi
  refine exec_at (infix_of b1_in_code (by simp [b1]) hp) exit_b1 hwf2 nofun
    (hpc2.trans (by rw [Nat.add_assoc]; exact congrArg (fun j ↦ Host.addrOf (k + j)) NativeRustcVmX64.Vm.InstanceWeights.b0_next))
    hm2
    fun st3 hm3 hpc3 => ?_
  simp only [PcOk] at hpc3
  refine (loop (Q := fun s' ↦ s'.pc = Host.addrOf (k + NativeRustcVmX64.Vm.InstanceWeights.b3Offset) ∧
      Match (frameEnv m0 st2.data 1048 [(gotAddr "memcpy", 8)] (fun _ ↦ 0) (Host.addrOf (k + NativeRustcVmX64.Vm.InstanceWeights.b3Offset + b3.length)).toBitVec)
        (it 14) s'.data)
    (fun n s ↦ ∃ j, n = 14 - j ∧ j < 14 ∧ s.pc = Host.addrOf (k + NativeRustcVmX64.Vm.InstanceWeights.b2Offset) ∧
      Match (frameEnv m0 st2.data 1048 [(gotAddr "memcpy", 8)] (fun _ ↦ 0) (Host.addrOf (k + NativeRustcVmX64.Vm.InstanceWeights.b3Offset + b3.length)).toBitVec)
        (it j) s.data)
    (fun _ s ⟨j, hn, hj, hpc, hm⟩ ↦ exec_at (infix_of b2_in_code b2_ne hp) (loop_exec hj)
      hwf2 nofun hpc hm fun s' hm' hpc' ↦ by
        simp only [PcOk, SBool.eval] at hpc'
        by_cases hlast : j = 13
        · subst hlast
          exact .done _ (Or.inl ⟨by simpa [Nat.add_assoc, NativeRustcVmX64.Vm.InstanceWeights.b2_next] using hpc', hm'⟩)
        · have hc : (j != 13) = true := by simpa using hlast
          simp only [hc, ite_true] at hpc'
          exact .done _ (Or.inr ⟨14 - (j + 1), by omega, j + 1, rfl, by omega,
            hpc'.trans (label_of_infix hp b2_in_code rfl), hm'⟩))
    ⟨0, rfl, by decide, hpc3.trans (by rw [Nat.add_assoc]; exact congrArg (fun j ↦ Host.addrOf (k + j)) NativeRustcVmX64.Vm.InstanceWeights.b1_next), hm3⟩).bind
    fun s4 ⟨hpc4, hm4⟩ ↦ ?_
  refine exec_at (infix_of b3_in_code (by simp [b3]) hp) exit_b3 hwf2 (fun _ _ ↦ rfl) hpc4 hm4
    fun st5 hm5 hpc5 => ?_
  obtain ⟨hmid5, hitems, hws5, hx7₅, hx6₅, hx2₅⟩ := ok_b3
  have hf5 : Frame m0 1048 slots 8 st5.data := Frame.of_block hf2 hwf2 hm5 hmid5 slots_le
  have hs5 : NativeRustcVm.SameOutside st2.data.dmem st5.data.dmem (NativeRustcVm.InRange fb 1000) :=
    sameOutside_low hwf2 hm5 (r := 0) rfl (by decide) hws5
  have hbuf5 : NativeRustcVm.BytesAt st5.data.dmem (off fb 736) (bufBytes (ewArg (reg m0 .rsi)
      (reg m0 .rdx))) :=
    buf_bytes hm5 rfl (by decide) hitems hpw
  have hsp5 : rspOf st5.data = stackBelow m0 1040 := by
    rw [hf5.sp, off_stackBelow (by decide)]
  have hX7₅ : reg st5.data .rdi = out :=
    (hm5.regs .rdi _ hx7₅).trans (load_of_wordAt (r := 0) (o := 512)
      hsv2')
  have hX6₅ : reg st5.data .rsi = off fb 736 := (hm5.regs .rsi _ hx6₅).trans (eval_ptr0 736)
  have hX2₅ : reg st5.data .rdx = BitVec.ofNat 64 264 := hm5.regs .rdx _ hx2₅
  -- `memcpy` to the result.
  have hpre5 : MemcpyPre st5.data := by
    unfold MemcpyPre
    rw [hX7₅, hX6₅, hX2₅, show (BitVec.ofNat 64 264).toNat = 264 from rfl]
    refine ⟨stackOk_callee hst hf5.kept hsp5 (by decide), Mapped.keeps hok.1 hf5.kept,
      mapped_off (Mapped.keeps hfmap hf5.kept) (by decide), hok.2, ?_, ?_,
      ?_⟩
    · show (off fb 736).toNat + 264 ≤ 2 ^ 64
      rw [toNat_off (by omega)]; omega
    · show out.toNat + 264 ≤ (off fb 736).toNat ∨ (off fb 736).toNat + 264 ≤ out.toNat
      rw [toNat_off (by omega)]; omega
    · show out.toNat + 264 ≤ (rspOf st5.data).toNat ∨ (rspOf st5.data).toNat + 8 ≤ out.toNat
      rw [hsp5, stackBelow_toNat (by omega)]
      omega
  refine call_then hpc5 hmemcpy hpre5 fun st6 hpc6 hrsp6 ⟨_, hcp, hsame6, hsv6⟩ => ?_
  rw [hX7₅, hX6₅, hX2₅, show (BitVec.ofNat 64 264).toNat = 264 from rfl,
    ← bufBytes_length (ewArg (reg m0 .rsi) (reg m0 .rdx)), bytesOf_eq hbuf5] at hcp
  rw [hX7₅, hX2₅, show (BitVec.ofNat 64 264).toNat = 264 from rfl] at hsame6
  have hf6 : Frame m0 1048 slots 16 st6.data :=
    Frame.call_at hf5 hsv6 hrsp6 hsame6
      (fun p hp i hi ↦ hfo _ (by have := slots_le p hp; omega))
      (fun j hj ↦ hfo _ (by omega))
  -- `b4`: the epilogue.
  have hwf6 := frame_wf (m0 := m0) (d := st6.data) (F := 1048) (rest := []) (vars := fun _ ↦ 0)
    (ret := 0) ⟨Mapped.keeps hfmap hf6.kept, hfnw⟩ (by simp) (List.pairwise_singleton _ _)
  refine exec_at (infix_of b4_in_code (by simp [b4]) hp) exit_b4 hwf6 nofun
    (hpc6.trans (by rw [Nat.add_assoc]; exact congrArg (fun j ↦ Host.addrOf (k + j)) NativeRustcVmX64.Vm.InstanceWeights.b3_next))
    (match_ofMachine ⟨rfl, trivial⟩ ⟨hf6.rsp_eval, trivial⟩ trivial trivial trivial)
    fun st7 hm7 hpc7 => ?_
  obtain ⟨hepi, hmem7⟩ := ok_b4
  obtain ⟨hsv7, hrsp7⟩ := Frame.epilogue hf6 hwf6 hm7 hepi
  have hd7 : st7.data.dmem = st6.data.dmem := hm7.dmem_eq hwf6 hmem7
  simp only [PcOk] at hpc7
  refine .done _ ⟨by rw [hpc7]; exact hf6.load_ret hst hN, hrsp7, ?_, ?_, hsv7⟩
  · unfold bufBytes at hcp
    have hsplit := NativeRustcVm.bytesAt_append_iff.mp hcp
    rw [NativeRustcVm.length_wordBytes] at hsplit
    refine ⟨by rw [Array.length_toList, iw_size], ?_, ?_⟩
    · rw [hd7, Array.length_toList, iw_size]; exact hsplit.1
    · rw [hd7]; exact hsplit.2
  · intro q hq
    have hqS : ¬ NativeRustcVm.InRange (stackBelow m0 instanceWeightsStack) instanceWeightsStack q :=
      fun h ↦ hq ⟨_, List.mem_cons_self, h⟩
    have hqO : ¬ NativeRustcVm.InRange out 264 q :=
      fun h ↦ hq ⟨⟨out, 264⟩, List.mem_cons_of_mem _ List.mem_cons_self, h⟩
    rw [hd7, hsame6 q hqO,
      hs5 q fun h ↦ hqS (hfS q (inRange_mono h (by decide))),
      hso2 q hqS]

end

end NativeRustcVmX64.KeccakGkr.InstanceWeights
