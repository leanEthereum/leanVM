module

public import NativeRustcVmX64.Tables.TableSumcheck.Start
public import NativeRustcVmX64.Code.Vm.SumcheckOfSumcheckPlain.Names

/-!
# `table_sumcheck`: the plain sumcheck (x86-64)

`b1` saves the `TState`, pushes `n` below the frame and calls the sumcheck of `n` rounds from the
target, its claim at `592` of the frame (an `Option<EW>`), its challenges at `112`; `b2` leaves on
`None` (the model's run fails, `exit_fail`) and goes on otherwise (`plain`, to `Sc`).
-/

namespace NativeRustcVmX64.Tables.TableSumcheck

open NativeRustcX64 NativeRustcX64.Sym NativeRustcVmX64.Transcript NativeRustcVm.Transcript
open NativeVm.Model NativeRustcVm.Tables NativeRustcVm.Layout NativeRustcVm.Bus
open NativeRustcVmX64.Tables.Body NativeRustcVmX64.Sumcheck NativeRustcVmX64.Vm.TableSumcheck
open NativeRustcVmX64.Tables.TableTerms (at_pc addr_eq)
open NativeRustcVm (wordOf ewsOf)

@[expose] public section

/-- **After the sumcheck**: the body, the `TState` saved at `80`, the challenges at `112`, the
claim at `600`, the registers. -/
structure Sc [Labels] (a : DecArea) (s : TState) (heights : Array Nat) (m0 : MachineData)
    (xs : Array EW) (c : EW) (s1 : TState) (d : MachineData) : Prop where
  bd : Bd m0 736 N slots (outs m0) 40 d
  run : (sumcheckPlain (tgt m0) 4 (nR heights)).run s = some ((xs, c), s1)
  t80 : NativeRustcVm.WordAt d.dmem (off (fb m0) 80) (.ofBitVec (tA m0))
  ch : NativeRustcVm.EWsAt d.dmem (off (fb m0) 112) xs.toList
  cl : NativeRustcVm.EWAt d.dmem (off (fb m0) 600) c
  ts : TStateAt d.dmem (tA m0) a s1
  r13 : reg d .r13 = BitVec.ofNat 64 (nR heights)
  rbp : reg d .rbp = cpA m0
  r14 : reg d .r14 = bA m0
  rbx : reg d .rbx = hA m0
  r12 : reg d .r12 = fpA m0
  r15 : reg d .r15 = off (fb m0) 112

end

public section

theorem off_736_16 (m0 : MachineData) (o : Nat) :
    off (fb m0) (16 + o) = off (stackBelow m0 720) o := by
  rw [← off_off, off_frame_eq (by omega)]

variable [Host] {k : Nat} {a : DecArea} {s : TState} {heights : Array Nat} {bus : BusResultW}
  {m0 : MachineData}

/-- **A frame word kept by the sumcheck**: from `24`, apart from its claim and challenges. -/
theorem keep_sc (h : TableSumcheckPre a s heights bus m0) {d d' : MachineData}
    (hb : Bd m0 736 N slots (outs m0) 16 d) {n : Nat}
    (hso : NativeRustcVm.SameOutside d.dmem d'.dmem (fun q ↦
      NativeRustcVm.InRange (off (fb m0) 592) 24 q ∨ NativeRustcVm.InRange (off (fb m0) 112) (16 * n) q ∨
      NativeRustcVm.InRange (tA m0) tstateBytes q ∨
      NativeRustcVm.InRange (stackBelow d sumcheckPlainStack) sumcheckPlainStack q))
    (hn : n ≤ 30) {o : Nat} {w : UInt64} (h1 : 24 ≤ o) (h2 : o + 8 ≤ 592) (h3 : o + 8 ≤ 112 ∨ 112 + 16 * n ≤ o)
    (hw : NativeRustcVm.WordAt d.dmem (off (fb m0) o) w) :
    NativeRustcVm.WordAt d'.dmem (off (fb m0) o) w := by
  have hS := Pre.stack h
  have hnw : (fb m0).toNat + (736 + 8) ≤ 2 ^ 64 :=
    frame_noWrap (F := 736) hS (by unfold N tableSumcheckStack; omega)
  have hNle := N_ge
  have hso' : NativeRustcVm.SameOutside d.dmem d'.dmem (fun q ↦
      (NativeRustcVm.InRange (off (fb m0) 592) 24 q ∨ NativeRustcVm.InRange (off (fb m0) 112) (16 * n) q ∨
      NativeRustcVm.InRange (tA m0) tstateBytes q) ∨
      NativeRustcVm.InRange (stackBelow d sumcheckPlainStack) sumcheckPlainStack q) :=
    NativeRustcVm.SameOutside.mono hso fun q hq ↦ by
      rcases hq with hq | hq | hq | hq
      · exact .inl (.inl hq)
      · exact .inl (.inr (.inl hq))
      · exact .inl (.inr (.inr hq))
      · exact .inr hq
  refine keepW_call hb hS (by unfold N tableSumcheckStack; omega) (by omega) (by omega) hso'
    (j := o) (by omega) (by omega) (fun i hi hq ↦ ?_) hw
  rcases hq with hq | hq | hq
  · rw [inRange_off_iff (by omega) (by omega)] at hq; omega
  · rcases Nat.eq_zero_or_pos n with h0 | h0
    · rw [h0] at hq; unfold NativeRustcVm.InRange at hq; omega
    rw [inRange_off_iff (by omega) (by omega)] at hq; omega
  · exact outs_not_frame h (.inl hq) (inRange_off_self (by omega) (by omega))

omit [Host] in
/-- The model's run fails where the sumcheck does. -/
theorem res_none_sc (h : (sumcheckPlain (tgt m0) 4 (nR heights)).run s = none) :
    res s heights bus m0 = none := by
  unfold nR at h
  unfold res
  rw [tableSumcheck_run, h]
  rfl

/-- **The plain sumcheck.** -/
theorem plain (hp : Placed code k) (h : TableSumcheckPre a s heights bus m0)
    (hsc : ∀ a s, Spec (Labels.label NativeRustcVmX64.Vm.SumcheckOfSumcheckPlain.entryLabel) (SumcheckPlainPre a s)
      (SumcheckPlainPost a s))
    {d : MachineData} (hb : Bd m0 736 N slots (outs m0) 40 d) (H : St0 a s heights m0 d)
    (cont : ∀ xs c s1 d', Sc a s heights m0 xs c s1 d' →
      Eventually (step1 Host.exe) (Goal a s heights bus m0) ⟨d', Host.addrOf (k + NativeRustcVmX64.Vm.TableSumcheck.b3Offset)⟩) :
    Eventually (step1 Host.exe) (Goal a s heights bus m0) ⟨d, Host.addrOf (k + NativeRustcVmX64.Vm.TableSumcheck.b1Offset)⟩ := by
  have hS := Pre.stack h
  have hH := Pre.hts h
  have hn30 : nR heights ≤ 30 := foldl_max_le heights hH.1 hH.2.1
  have hNle := N_ge
  -- `b1`: the arguments, `n` pushed, the call.
  let ra := (Host.addrOf (k + NativeRustcVmX64.Vm.TableSumcheck.b1Offset + b1.length)).toBitVec
  have hwf : (E m0 d [(argA m0, 16)] ra).WF :=
    frame_wf' hS (by unfold N tableSumcheckStack; omega) hb.fr.kept (fun x hx ↦ by
      rw [List.mem_singleton] at hx; subst hx; exact ⟨(Pre.args h).1, args_noWrap h⟩)
      (List.pairwise_pair.mpr (frame_args h))
  have hm : Match (E m0 d [(argA m0, 16)] ra) argS d := by
    refine match_body hb ⟨rfl, rfl, trivial⟩ ⟨?_, ?_, trivial⟩
    · show stackBelow m0 736 + BitVec.ofInt 64 744 = argA m0 + BitVec.ofInt 64 0
      rw [show BitVec.ofInt 64 744 = BitVec.ofNat 64 (736 + 8) from rfl,
        show stackBelow m0 736 + BitVec.ofNat 64 (736 + 8) = off (stackBelow m0 736) (736 + 8)
          from rfl, frame_add, ofInt_zero64, BitVec.add_zero]
    · show stackBelow m0 736 + BitVec.ofInt 64 752 = argA m0 + BitVec.ofInt 64 8
      rw [show BitVec.ofInt 64 752 = BitVec.ofNat 64 (736 + 16) from rfl,
        show stackBelow m0 736 + BitVec.ofNat 64 (736 + 16) = off (stackBelow m0 736) (736 + 16)
          from rfl, frame_add, show BitVec.ofInt 64 8 = BitVec.ofNat 64 8 from rfl]
      unfold argA
      rw [NativeRustcVm.addr_add_add]
  refine exec_then (infix_of b1_in_code (by simp [b1]) hp) exit_b1 hwf (fun _ _ ↦ rfl) hm
    fun st1 hm1 hpc1 ↦ ?_
  obtain ⟨mid1, W1, ws1, w24, w80, rcx1, rdx1, rsi1, rdi1, r8_1, r9_1, r12_1, r15_1, k1⟩ := ok_b1
  have hb1 := hb.step hS (by unfold N tableSumcheckStack; omega) hwf hm1 mid1
    (fun p hp ↦ (slots_le p hp).2) W1 nofun
  have rg : ∀ {r : Reg64} {v : Sym}, (after b1 argS).reg r = some v →
      reg st1.data r = v.eval (E m0 d [(argA m0, 16)] ra) := fun hv ↦ hm1.regs _ _ hv
  have t80 : NativeRustcVm.WordAt st1.data.dmem (off (fb m0) 80) (.ofBitVec (tA m0)) :=
    wroteW hm1 (by omega) w80 H.r10
  have n24 : NativeRustcVm.WordAt st1.data.dmem (off (fb m0) 24)
      (.ofBitVec (BitVec.ofNat 64 (nR heights))) := wroteW hm1 (by omega) w24 H.r13
  have hts1 : TStateAt st1.data.dmem (tA m0) a s :=
    H.ts.frame (hm1.kept hwf) (fun q hq ↦ (ctx h).stack_not_t (fr_stack h (hq.elim id False.elim)))
      (NativeRustcVm.SameOutside.mono (same_block hwf hm1 (writesIn_of_mid mid1)
        (belowRet_of_mid mid1) W1 (X := fun _ ↦ False) nofun) fun q hq ↦ hq)
  -- `sumcheck`'s precondition.
  have hat : At m0 720 st1.data := Bd.atO h (by omega) hb1
  have c720 := ctxF h (F := 720) (by omega)
  have hle : 720 + sumcheckPlainStack ≤ N := by omega
  have e592 := off_736_16 m0 576
  have e112 := off_736_16 m0 96
  have hrsi : reg st1.data .rsi = tA m0 := by rw [rg rsi1]; exact H.r10
  have hrdi : reg st1.data .rdi = off (fb m0) 592 := by rw [rg rdi1]; exact eval_ptr0 592
  have hr9 : reg st1.data .r9 = off (fb m0) 112 := by rw [rg r9_1]; exact eval_ptr0 112
  have hr8 : (reg st1.data .r8).toNat = 4 := by rw [rg r8_1]; rfl
  have hsp1 : rspOf st1.data = off (fb m0) 16 := hb1.fr.sp
  have hstk : stackArg st1.data 0 = BitVec.ofNat 64 (nR heights) := by
    unfold stackArg
    rw [hsp1, off_add]
    exact congrArg UInt64.toBitVec (NativeRustcVm.wordOf_of_wordAt n24)
  have hnr : (BitVec.ofNat 64 (nR heights)).toNat = nR heights := toNat_ofNat_lt (by omega)
  have hpre : SumcheckPlainPre a s st1.data := by
    unfold SumcheckPlainPre SumcheckOk
    rw [hrsi, hrdi, hr9, hr8, hstk, hnr]
    refine ⟨⟨?_, ?_⟩, c720.stackOk hat hle, c720.rcAt hat hle, hts1, c720.tstateOk hat hle,
      by decide, by decide, ?_, ?_, ?_, ?_⟩
    · show NativeRustcVm.Mapped st1.data.dmem (rspOf st1.data + 8#64) (8 * 1)
      rw [hsp1, show (8#64 : BitVec 64) = BitVec.ofNat 64 8 from rfl, off_add]
      exact mapped_off (Mapped.keeps (frame_mapped hS (by omega)) hb1.fr.kept) (by omega)
    · rw [hsp1, toNat_off (by rw [fb_toNat h]; have := sp8 h; omega), fb_toNat h]
      have := spN h; have := sp8 h; omega
    · rw [show (592 : Nat) = 16 + 576 from rfl, e592]
      exact c720.outOk_frame hat hle (by omega) (by omega)
    · rw [show (112 : Nat) = 16 + 96 from rfl, e112]
      exact c720.outOk_frame hat hle (by omega) (by omega)
    · show NativeRustcVm.Apart _ _ _ _
      unfold NativeRustcVm.Apart
      have hf := fb_toNat h
      have := spN h; have := sp8 h
      rw [toNat_off (by omega), toNat_off (by omega)]
      omega
    · refine got_call h hb1 (by omega) hle ?_
      intro l hl b hb
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
      rcases hb with rfl | rfl | rfl | rfl | rfl
      · exact ((Pre.got h).1 l hl).2.2.2 (tA m0, tstateBytes) (by simp)
      · exact ((Pre.got h).1 l hl).2.2.2 (a.words, 8 * a.len) (by simp)
      · exact got_apart_frame (Pre.got h) hS hl (ob := 592) (len := 24) (by omega) (by decide)
      · exact got_apart_frame (Pre.got h) hS hl (ob := 112) (len := 16 * nR heights)
          (by omega) (by omega)
      · exact ((Pre.got h).1 l hl).2.2.2 (rcAddr, 192) (by simp)
  simp only [PcOk] at hpc1
  refine call_then (env := E m0 d [(argA m0, 16)] ra) hpc1 (hsc a s) hpre fun st2 hpc2 hrsp2 hq ↦ ?_
  have hclaim : claimArg st1.data = tgt m0 := by
    unfold claimArg tgt ewArg
    rw [rg rdx1, rg rcx1]
    show (⟨_, _⟩ : EW) = ⟨UInt64.ofBitVec (reg m0 .r9), _⟩
    rw [show (Sym.reg .r9).eval (E m0 d [(argA m0, 16)] ra) = reg d .r9 from rfl, H.r9]
    show (⟨_, UInt64.ofBitVec ((E m0 d [(argA m0, 16)] ra).load 1 0 8)⟩ : EW) = _
    rw [NativeRustcVmX64.Tables.TableTerms.load_eq_wordOf]
    have := arg_word h hb (j := 0) (by omega)
    rw [Nat.mul_zero, NativeRustcVm.addr_add_zero] at this
    rw [show (E m0 d [(argA m0, 16)] ra).base 1 = argA m0 from rfl, NativeRustcVm.addr_add_zero]
    rw [show (wordOf (E m0 d [(argA m0, 16)] ra).mem0 (argA m0)).toBitVec =
      (wordOf d.dmem (argA m0)).toBitVec from rfl, this]
  unfold SumcheckPlainPost SumcheckOut at hq
  simp only [hrsi, hrdi, hr9, hstk, hnr, hr8, hclaim] at hq
  generalize hR : (sumcheckPlain (tgt m0) 4 (nR heights)).run s = R at hq
  obtain ⟨⟨q0, q1, q2⟩, q3, q4⟩ := hq
  have hb2 := call_frame h hb1 (by omega) (by omega) q4 hrsp2 (Ro := fun q ↦
    NativeRustcVm.InRange (off (fb m0) 592) 24 q ∨
      NativeRustcVm.InRange (off (fb m0) 112) (16 * nR heights) q ∨
      NativeRustcVm.InRange (tA m0) tstateBytes q)
    (NativeRustcVm.SameOutside.mono q3 fun q hq ↦ by
      rcases hq with hq | hq | hq | hq
      · exact .inl (.inl hq)
      · exact .inl (.inr (.inl hq))
      · exact .inl (.inr (.inr hq))
      · exact .inr hq)
    fun q hq ↦ by
      rcases hq with hq | hq | hq
      · exact .inr ⟨592, 24, by omega, hq⟩
      · exact .inr ⟨112, 16 * nR heights, by omega, hq⟩
      · exact .inl (.inl hq)
  have hsf : ∀ q, (NativeRustcVm.InRange (off (fb m0) 592) 24 q ∨
      NativeRustcVm.InRange (off (fb m0) 112) (16 * nR heights) q ∨
      NativeRustcVm.InRange (tA m0) tstateBytes q ∨
      NativeRustcVm.InRange (stackBelow st1.data sumcheckPlainStack) sumcheckPlainStack q) →
      NativeRustcVm.InRange (stackBelow m0 N) N q ∨ NativeRustcVm.InRange (tA m0) tstateBytes q :=
    fun q hq ↦ by
      rcases hq with hq | hq | hq | hq
      · exact .inl (loc_stack h (by omega) hq)
      · exact .inl (loc_stack h (by omega) hq)
      · exact .inr hq
      · exact .inl (hb1.callee_in hS (by omega) (by omega) hq).1
  -- `b2`: the claim's tag.
  have hwf2 : (E m0 st2.data [] 0).WF := wf_nil h hb2.fr.kept
  have hm2 : Match (E m0 st2.data [] 0) retS st2.data := match_body hb2 ⟨rfl, trivial⟩ trivial
  refine at_pc (hpc2.trans (addr_eq (by rw [Nat.add_assoc]; exact congrArg (k + ·) NativeRustcVmX64.Vm.TableSumcheck.b1_next)))
    (exec_then (infix_of b2_in_code (by simp [b2]) hp) exit_b2 hwf2 nofun hm2
      fun st3 hm3 hpc3 ↦ ?_)
  obtain ⟨mid3, mem3, k3⟩ := ok_b2
  have hd3 : st3.data.dmem = st2.data.dmem := hm3.dmem_eq hwf2 mem3
  have hb3 := (blockB h hb2 hwf2 hm3 mid3 (by rw [WrOk, mem3]; rfl)).1
  have kr : ∀ r ∈ csR, reg st3.data r = reg st1.data r := fun r hr ↦ by
    rw [keeps_reg hm3 k3 hr]
    exact q4.1 r (by simp at hr; rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> rfl)
  have kd : ∀ r ∈ [Reg64.rbx, .rbp, .r13, .r14], reg st1.data r = reg d r :=
    fun r hr ↦ keeps_reg hm1 k1 hr
  cases R with
  | none =>
    have hr := hR
    have hc : c2.eval (E m0 st2.data [] 0) = true := by
      have := NativeRustcVmX64.Transcript.load4_of_tag (env := E m0 st2.data [] 0) (r := 0)
        (o := 592) (w := 0) (Or.inl rfl) q0
      unfold c2
      simp only [SBool.eval, Sym.eval, this, CmpOp.apply]
      decide
    simp only [PcOk, hc, ↓reduceIte] at hpc3
    exact at_pc (hpc3.trans (lbl_11 hp)) (exit_fail hp h hb3 (res_none_sc hr))
  | some p =>
    obtain ⟨⟨xs, c⟩, s1⟩ := p
    have hr := hR
    obtain ⟨tag, hc0⟩ := q0
    have hc : c2.eval (E m0 st2.data [] 0) = false := by
      have := NativeRustcVmX64.Transcript.load4_of_tag (env := E m0 st2.data [] 0) (r := 0)
        (o := 592) (w := 1) (Or.inr rfl) tag
      unfold c2
      simp only [SBool.eval, Sym.eval, this, CmpOp.apply]
      decide
    simp only [PcOk, hc, Bool.false_eq_true, ↓reduceIte] at hpc3
    have hk2 : ∀ (o : Nat) (w : UInt64), 24 ≤ o → o + 8 ≤ 592 →
        o + 8 ≤ 112 ∨ 112 + 16 * nR heights ≤ o →
        NativeRustcVm.WordAt st1.data.dmem (off (fb m0) o) w →
        NativeRustcVm.WordAt st3.data.dmem (off (fb m0) o) w := fun o w h1 h2 h3 hw ↦ by
      rw [hd3]
      exact keep_sc h hb1 q3 hn30 h1 h2 h3 hw
    refine at_pc (hpc3.trans (addr_eq (by rw [Nat.add_assoc]; exact congrArg (k + ·) NativeRustcVmX64.Vm.TableSumcheck.b2_next)))
      (cont xs c s1 st3.data ⟨hb3, hr, hk2 80 _ (by omega) (by omega) (by omega) t80, ?_, ?_, ?_,
        ?_, ?_, ?_, ?_, ?_, ?_⟩)
    · rw [hd3]; exact q1 xs c s1 rfl
    · rw [hd3]
      have := hc0
      rwa [off_off] at this
    · rw [hd3]
      exact q2 _ _ rfl
    · rw [kr .r13 (by simp), kd .r13 (by simp)]; exact H.r13
    · rw [kr .rbp (by simp), kd .rbp (by simp)]; exact H.rbp
    · rw [kr .r14 (by simp), kd .r14 (by simp)]; exact H.r14
    · rw [kr .rbx (by simp), kd .rbx (by simp)]; exact H.rbx
    · rw [kr .r12 (by simp), rg r12_1]; exact H.r8
    · rw [kr .r15 (by simp), rg r15_1]; exact eval_ptr0 112

end

end NativeRustcVmX64.Tables.TableSumcheck
