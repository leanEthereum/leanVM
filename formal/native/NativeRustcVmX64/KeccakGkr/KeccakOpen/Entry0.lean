module

public import NativeRustcVmX64.KeccakGkr.KeccakOpen.Body
public import NativeRustcVmX64.KeccakGkr.KeccakOpen.ExecE
public import NativeRustcVmX64.Code.Vm.SumcheckOfSumcheckPlain.Names

/-!
# `keccak_open`: prologue and plain sumcheck

The seventh sumcheck argument is written in the caller frame. The sumcheck's output occupies
bytes 88 through 111; its transcript and six challenges are the external writable regions.
-/

namespace NativeRustcVmX64.KeccakGkr.KeccakOpen

open NativeRustcX64 NativeRustcX64.Sym NativeVm.Model NativeRustcVmX64.Transcript
open NativeRustcVmX64.Vm.KeccakOpen
open NativeRustcVm.Transcript (off off_zero off_off off_add toNat_off inRange_iff' Mapped.keeps
  bytesAt_congr DecArea tstateBytes TStateAt Touch)

@[expose] public section

def scRun (s : TState) (m0 : MachineData) : Option ((Array EW × EW) × TState) :=
  (sumcheckPlain (openValue m0) 3 LeanVM.Protocol.Verifier.qkeccakSlotBits).run s

structure Sc [Labels] (a : DecArea) (s : TState) (m0 d : MachineData) : Prop where
  body : Body m0 8 d
  bx : reg d .rbx = oA m0
  bp : reg d .rbp = reg m0 .rdx
  r12 : reg d .r12 = reg m0 .r8
  r13 : reg d .r13 = reg m0 .rcx
  r14 : reg d .r14 = reg m0 .r9
  out : SumcheckOut d.dmem (tA m0) a (off (fbA m0) 88) (slA m0) (scRun s m0)

end

public section

variable [Host] {k : Nat} {a : DecArea} {s : TState} {c : KeccakClaimW} {m0 : MachineData}

theorem sc_run (hp : Placed code k) (h : PreOk a s c m0)
    (hsc : ∀ a s, Spec (Labels.label NativeRustcVmX64.Vm.SumcheckOfSumcheckPlain.entryLabel) (SumcheckPlainPre a s)
      (SumcheckPlainPost a s)) :
    Eventually (step1 Host.exe) (fun st ↦ st.pc = Host.addrOf (k + NativeRustcVmX64.Vm.KeccakOpen.b1Offset) ∧ Sc a s m0 st.data)
      ⟨m0, Host.addrOf (k + NativeRustcVmX64.Vm.KeccakOpen.b0Offset)⟩ := by
  have hn := nums h
  have := hn.r1; have := hn.r2; have := hn.s; have := hn.t; have := hn.ss; have := hn.st
  have hfb := fbA_toNat h
  have hctx := context h
  have hle : 2208 + sumcheckPlainStack ≤ keccakOpenStack := by decide
  have hwf := wf_fold h (st := m0) (fun _ hx ↦ hx) (vars := fun _ ↦ 0)
    (ret := (Host.addrOf (k + NativeRustcVmX64.Vm.KeccakOpen.b0Offset + b0.length)).toBitVec)
  have hmatch : Match (E m0 m0 (fun _ ↦ 0) (Host.addrOf (k + NativeRustcVmX64.Vm.KeccakOpen.b0Offset + b0.length)).toBitVec) e0S m0 := by
    apply Match.withKnownBytes
    · refine match_ofMachine ⟨rfl, rfl, rfl, rfl, rfl, trivial⟩ ⟨match_rsp, trivial⟩ trivial trivial
        ⟨arg_alias 0, arg_alias 1, arg_alias 2, arg_alias 3, arg_alias 4, arg_alias 5, ?_,
          by simp [Sym.eval, RF, Env.base, gotAddr], trivial⟩
      show (E m0 m0 (fun _ ↦ 0) (Host.addrOf (k + NativeRustcVmX64.Vm.KeccakOpen.b0Offset + b0.length)).toBitVec).load 3 32 8 =
        slA m0 + BitVec.ofInt 64 0
      rw [show (32 : Nat) = 8 * 4 from rfl, load_arg h (fun _ _ ↦ rfl) (i := 4) (by decide), ofInt0,
        BitVec.add_zero]
      rfl
    · intro i hi
      simp only [Nat.zero_add]
      change m0.dmem.get? (gotAddr "memcpy" + BitVec.ofNat 64 i) =
        some (byteOf (Labels.label "memcpy").toBitVec i)
      exact h.got.byte (l := "memcpy") (by simp) hi
  refine exec_at (infix_of b0_in_code (by simp [b0]) hp) x0 hwf (fun _ _ ↦ rfl) rfl hmatch
    fun st1 hm1 hpc1 ↦ ?_
  obtain ⟨_, hf, hws, hw8, hdi, hsi, hdx, hcx, hr8, hr9, hbx, hbp, h12, h13, h14⟩ := f0
  have hf1 : Frame m0 2208 slots 0 st1.data :=
    Frame.of_prologue Frame.entry hwf hm1 hf slots_le' (by decide)
  have hs1 := sameOutside_touch hwf hm1 (r := 0) (b := fbA m0) (N := 2216)
    (lo := 0) (hi := 2208) rfl (by decide) (fun w hw ↦ by
      have := hws w hw; exact ⟨this.1, by omega⟩)
  have hb1 : Body m0 0 st1.data := ⟨hf1, fun q hq ↦ hs1 q fun ht ↦
    hq (touch_frame_out h (fun _ hj ↦ hj.2) ht)⟩
  have hat := hb1.at h
  have ydi : reg st1.data .rdi = off (fbA m0) 88 := (hm1.regs .rdi _ hdi).trans (eval_ptr0 88)
  have ysi : reg st1.data .rsi = tA m0 := hm1.regs .rsi _ hsi
  have ydx : reg st1.data .rdx = stackArg m0 2 :=
    (hm1.regs .rdx _ hdx).trans (load_arg h (fun _ _ ↦ rfl) (i := 2) (by decide))
  have ycx : reg st1.data .rcx = stackArg m0 3 :=
    (hm1.regs .rcx _ hcx).trans (load_arg h (fun _ _ ↦ rfl) (i := 3) (by decide))
  have y8 : reg st1.data .r8 = 3#64 := hm1.regs .r8 _ hr8
  have y9 : reg st1.data .r9 = slA m0 :=
    (hm1.regs .r9 _ hr9).trans (load_arg h (fun _ _ ↦ rfl) (i := 4) (by decide))
  have yw8 : NativeRustcVm.WordAt st1.data.dmem (off (fbA m0) 8) 6 :=
    wordAt_write hm1 (r := 0) (o := 8) (v := .lit 6) rfl (by decide) hw8
  have ya : stackArg st1.data 0 = 6#64 := by
    unfold stackArg
    rw [hat.sp, show stackBelow m0 2208 + BitVec.ofNat 64 (8 + 8 * 0) = off (fbA m0) 8 from rfl,
      NativeRustcVm.wordOf_of_wordAt yw8]
    rfl
  have yclaim : claimArg st1.data = openValue m0 := by
    unfold claimArg openValue ewArg
    rw [ydx, ycx]
  have hts : TStateAt st1.data.dmem (tA m0) a s :=
    h.ts.frame (hm1.kept hwf) (fun q hq ↦ hctx.stack_not_t (by
      obtain ⟨j, _, hj, rfl⟩ := hq
      exact hctx.inRange_frame (NativeRustcVm.Transcript.inRange_off_self hj.2
        (by have := hctx.noWrap_frame; unfold NativeRustcVm.NoWrap at this; omega)))) hs1
  have hpre : SumcheckPlainPre a s st1.data := by
    unfold SumcheckPlainPre SumcheckOk
    rw [ydi, ysi, y8, y9, ya]
    refine ⟨⟨?_, ?_⟩, hctx.stackOk hat hle, hctx.rcAt hat hle, hts, hctx.tstateOk hat hle,
      by decide, by decide, hctx.outOk_frame hat hle (by decide) (by decide),
      hctx.outOk hat hle (slot_out h), ?_, ?_⟩
    · rw [hat.sp]
      exact mapped_off (o := 8) (hctx.mapped_frame hat.kept) (by decide)
    · rw [hat.sp, hfb]; omega
    · exact Apart.symm' (hctx.apart_of_stack (slot_out h).2.2.2.2.1 (by decide))
    · apply h.got.transport
      · intro l hl i hi
        simp only [List.mem_singleton] at hl
        subst l
        exact (got_byte h hb1.same hi).trans (h.got.byte (by simp) hi).symm
      · intro l hl
        exact hctx.apart hat hle (h.got.1 l hl).2.2.1
      · intro l hl p hp
        have hg := (h.got.1 l hl).2.2.2
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
        rcases hp with rfl | rfl | rfl | rfl | rfl
        · exact hg _ (by simp)
        · exact hg (a.region.addr, a.region.size) (by simp)
        · have hs : Apart (gotAddr l) 8 (stackBelow m0 keccakOpenStack)
              (keccakOpenStack + 8) := (h.got.1 l hl).2.2.1
          have hb := stackBelow_toNat h.st.1
          have hf := fb_off h (j := 88) (by decide)
          have hN := h.st.1
          unfold Apart at hs ⊢
          rw [hb] at hs
          rw [hf]
          omega
        · exact hg _ (by simp)
        · exact hg _ (by simp)
  refine call_then hpc1 (hsc a s) hpre fun st2 hpc2 hrsp hpost ↦ ?_
  obtain ⟨hout, hso, hsv⟩ := hpost
  rw [ysi, ydi, y9, ya, y8, yclaim] at hout
  rw [ysi, ydi, y9, ya] at hso
  have hchange : ∀ q, (NativeRustcVm.InRange (off (fbA m0) 88) 24 q ∨
      NativeRustcVm.InRange (slA m0) 96 q ∨ NativeRustcVm.InRange (tA m0) tstateBytes q ∨
      NativeRustcVm.InRange (stackBelow st1.data sumcheckPlainStack) sumcheckPlainStack q) →
      Out m0 q ∧ ¬ NativeRustcVm.InRange (off (fbA m0) 2160) 56 q := by
    intro q hq
    have h2160 := fb_off h (j := 2160) (by decide)
    have h88 := fb_off h (j := 88) (by decide)
    have hout : NativeRustcVm.InRange (off (fbA m0) 88) 24 q → Out m0 q := fun hr ↦
      ⟨_, List.mem_cons_self, hctx.inRange_frame (inRange_of_off
        (by have := hctx.noWrap_frame; unfold NativeRustcVm.NoWrap at this ⊢; omega)
        (by decide) hr)⟩
    rcases hq with hq | hq | hq | hq
    · refine ⟨hout hq, ?_⟩
      rw [inRange_iff' (by unfold NativeRustcVm.NoWrap; omega), h88] at hq
      rw [inRange_iff' (by unfold NativeRustcVm.NoWrap; omega), h2160]
      omega
    · refine ⟨⟨_, .tail _ (.tail _ (.tail _ (.head _))), hq⟩, ?_⟩
      rw [inRange_iff' (by unfold NativeRustcVm.NoWrap; omega)] at hq
      rw [inRange_iff' (by unfold NativeRustcVm.NoWrap; omega), h2160]
      omega
    · refine ⟨⟨_, .tail _ (.tail _ (.head _)), hq⟩, ?_⟩
      rw [show tstateBytes = 760 from rfl, inRange_iff' (by unfold NativeRustcVm.NoWrap; omega)] at hq
      rw [inRange_iff' (by unfold NativeRustcVm.NoWrap; omega), h2160]
      omega
    · obtain ⟨hstack, hmiss⟩ := hctx.inRange_callee hat hle hq
      refine ⟨⟨_, .head _, hstack⟩, fun hr ↦ hmiss ?_⟩
      exact inRange_of_off hctx.noWrap_frame (by decide) hr
  have hf2 := hf1.call_slots hsv hrsp hso
    (fun p hp i hi hq ↦ (hchange _ hq).2 (by
      have hpl := slots_le p hp
      rw [← show 2160 + (p.1 + i - 2160) = p.1 + i by omega, ← off_off]
      exact NativeRustcVm.Transcript.inRange_off_self (by omega)
        (by decide)))
    (fun j hj hq ↦ (hchange _ hq).2 (by
      rw [show 2208 + j = 2160 + (48 + j) by omega, ← off_off]
      exact NativeRustcVm.Transcript.inRange_off_self (by omega)
        (by decide)))
  have hb2 : Body m0 8 st2.data := ⟨hf2, fun q hq ↦
    (hso q fun ht ↦ hq (hchange q ht).1).trans (hb1.same q hq)⟩
  refine .done _ ⟨hpc2.trans (by rw [Nat.add_assoc]; exact congrArg (fun j ↦ Host.addrOf (k + j)) NativeRustcVmX64.Vm.KeccakOpen.b0_next), hb2,
    (hsv.1 .rbx rfl).trans (hm1.regs .rbx _ hbx),
    (hsv.1 .rbp rfl).trans (hm1.regs .rbp _ hbp),
    (hsv.1 .r12 rfl).trans (hm1.regs .r12 _ h12),
    (hsv.1 .r13 rfl).trans (hm1.regs .r13 _ h13),
    (hsv.1 .r14 rfl).trans (hm1.regs .r14 _ h14), hout⟩

end

end NativeRustcVmX64.KeccakGkr.KeccakOpen
