module

public import NativeRustcVmX64.KeccakGkr.VerifyLayer.Back.Check
public import NativeRustcVmX64.Code.Vm.BitLength.Names
public import NativeRustcVmX64.Code.Vm.SpongeWSqueeze.Names
public import NativeRustcVmX64.Code.Vm.TStateGrind.Names

/-! # The final grind and beta challenge in `verify_layer` -/

namespace NativeRustcVmX64.KeccakGkr.VerifyLayer

open NativeRustcX64 NativeRustcX64.Sym NativeVm.Model NativeRustcVmX64.Transcript
open NativeRustcVmX64.Vm.VerifyLayer
open NativeRustcVm.Transcript (tstateBytes DecArea TStateAt off)
open LeanVM.Parameters LeanVM.Protocol.Verifier

@[expose] public section

structure C6 (m0 : MachineData) (a : DecArea) (c : KeccakClaimW) (ch beta : EW)
    (pt lp t : Array EW) (s6 : TState) (d : MachineData) : Prop extends C5 m0 a c ch pt lp t s6 d where
  rax : reg d .rax = beta.c0.toBitVec
  rdx : reg d .rdx = beta.c1.toBitVec
  r13 : reg d .r13 = BitVec.ofNat 64 288230376151711742

end

public section

variable [Host] {a : DecArea} {s : TState} {c : KeccakClaimW} {m0 : MachineData} {k : Nat}

 theorem beta (hp : Placed code k) (hpre : VerifyLayerPre a s c m0)
    (hbl : Spec (Labels.label NativeRustcVmX64.Vm.BitLength.entryLabel) BitLengthPre BitLengthPost)
    (hgr : ∀ s, Spec (Labels.label NativeRustcVmX64.Vm.TStateGrind.entryLabel) (GrindPre a s) (GrindPost a s))
    (hsq : ∀ sp, Spec (Labels.label NativeRustcVmX64.Vm.SpongeWSqueeze.entryLabel) (SqueezePre sp) (SqueezePost sp))
    {ch : EW} {pt lp t : Array EW} {s5 : TState} {d : MachineData}
    (h : C5 m0 a c ch pt lp t s5 d) (hrun : runL s c m0 = rest6 ch pt lp t s5)
    (cont : ∀ b s6 d', C6 m0 a c ch b pt lp t s6 d' →
      runL s c m0 = some (newClaim ch pt lp t b, s6) →
      Eventually (step1 Host.exe) (Goal a s c m0) ⟨d', Host.addrOf (k + NativeRustcVmX64.Vm.VerifyLayer.b69Offset)⟩) :
    Eventually (step1 Host.exe) (Goal a s c m0) ⟨d, Host.addrOf (k + NativeRustcVmX64.Vm.VerifyLayer.b65Offset)⟩ := by
  have g := geo_of hpre
  have hWo := wFront_outs hpre
  have hS := pre_stack hpre
  have cx := ctx hpre (F := 2000) (by decide)
  rw [rest6, grindingBits_2] at hrun
  have hwf := wf0 hS h.body (vars := fun _ ↦ 0)
    (ret := (Host.addrOf (k + NativeRustcVmX64.Vm.VerifyLayer.b65Offset + b65.length)).toBitVec)
  have hm : Match (envB m0 d [] (fun _ ↦ 0) (Host.addrOf (k + NativeRustcVmX64.Vm.VerifyLayer.b65Offset + b65.length)).toBitVec)
      (fr 24) d :=
    match_ofMachine ⟨rfl, trivial⟩ ⟨h.body.rsp, trivial⟩ trivial trivial trivial
  refine Body.blk (o' := 16) g h.body hwf (blk hp b65_in_code (by simp [b65])) e65
    (fun _ _ ↦ rfl) hm (by decide +kernel) (hex0 (by decide +kernel)) fun st hm1 hpc1 hb1 _ ↦ ?_
  have hfr1 := frSame_blk (o := 24) (n := 2000) hwf hm1 (by decide +kernel) (by decide)
    (by decide +kernel)
  have hts1 := ts_blk0 hpre hwf hm1 (by decide +kernel) (by decide +kernel) h.ts
  have heq1 := scr_blk0E hpre hwf hm1 (by decide +kernel) (by decide +kernel)
    (by decide) (by rw [eqK_len h.lsz]; decide) h.eq
  have hrdi1 : reg st.data .rdi = 1#64 := hm1.regs .rdi _ rfl
  have h12_1 : reg st.data .r12 = tA m0 := (hm1.regs .r12 _ rfl).trans h.r12
  have h15_1 : reg st.data .r15 = sA m0 := (hm1.regs .r15 _ rfl).trans h.r15
  refine leafX hpre hWo (Sk := bitLengthStack) (by decide) hbl (fun _ _ hq ↦ ⟨hq.2.1, hq.2.2⟩)
    hpc1 hb1 (cx.stackOk (hb1.at_ hpre hWo (by decide)) (by decide))
    fun d2 hq2 hb2 hfr2 hts2 hcs2 hso2 ↦ ?_
  have h1 : reg d2 .rax = 1#64 := by
    apply BitVec.eq_of_toNat_eq
    rw [hq2.1, hrdi1]; rfl
  have h12_2 := (hcs2 .r12 rfl).trans h12_1
  have h15_2 := (hcs2 .r15 rfl).trans h15_1
  have heq2 := scr_call hpre hWo hb1 (Sk := bitLengthStack) (by decide)
    (NativeRustcVm.SameOutside.mono hso2 fun _ hq ↦ Or.inl hq) (X := fun _ ↦ False)
    (by decide) (by rw [eqK_len h.lsz]; decide) (fun _ hq ↦ hq.elim) heq1
  rw [show k + NativeRustcVmX64.Vm.VerifyLayer.b65Offset + b65.length = k + NativeRustcVmX64.Vm.VerifyLayer.b66Offset from by rw [Nat.add_assoc, NativeRustcVmX64.Vm.VerifyLayer.b65_next]]
  have hwf3 := wf0 hS hb2 (vars := fun _ ↦ 0)
    (ret := (Host.addrOf (k + NativeRustcVmX64.Vm.VerifyLayer.b66Offset + b66.length)).toBitVec)
  have hm3 : Match (envB m0 d2 [] (fun _ ↦ 0) (Host.addrOf (k + NativeRustcVmX64.Vm.VerifyLayer.b66Offset + b66.length)).toBitVec)
      (fr 24) d2 :=
    match_ofMachine ⟨rfl, trivial⟩ ⟨hb2.rsp, trivial⟩ trivial trivial trivial
  refine Body.blk (o' := 16) g hb2 hwf3 (blk hp b66_in_code (by simp [b66])) e66
    (fun _ _ ↦ rfl) hm3 (by decide +kernel) (hex0 (by decide +kernel)) fun st3 hm4 hpc4 hb4 _ ↦ ?_
  have hfr4 := frSame_blk (o := 24) (n := 2000) hwf3 hm4 (by decide +kernel) (by decide)
    (by decide +kernel)
  have hts4 := ts_blk0 hpre hwf3 hm4 (by decide +kernel) (by decide +kernel) (hts2 _ hts1)
  have heq4 := scr_blk0E hpre hwf3 hm4 (by decide +kernel) (by decide +kernel)
    (by decide) (by rw [eqK_len h.lsz]; decide) heq2
  have hrdi4 : reg st3.data .rdi = tA m0 := (hm4.regs .rdi _ rfl).trans h12_2
  have h12_4 : reg st3.data .r12 = tA m0 := (hm4.regs .r12 _ rfl).trans h12_2
  have h15_4 : reg st3.data .r15 = sA m0 := (hm4.regs .r15 _ rfl).trans h15_2
  have hgb : grindBits st3.data = 0 := by
    unfold grindBits
    rw [show reg st3.data .rsi = _ from hm4.regs .rsi _ rfl]
    simp only [Sym.eval, SBool.eval]
    change (if Bool.not (CmpOp.apply .ult .W32 (reg d2 .rax) 3#64) = true
      then BinOp.apply .sub .W32 (reg d2 .rax) 3#64 else 0#64).toNat % 2 ^ 32 = 0
    rw [h1]; decide
  have hat4 := hb4.at_ hpre hWo (by decide)
  have hgot4 : GotAt st3.data grindStack
      [(tA m0, tstateBytes), (a.words, 8 * a.len), (rcAddr, 192)] ["memcpy"] := by
    apply hb4.got hpre hWo (by decide) (by decide)
    simp only [NativeRustcVm.Transcript.DecArea.region]
    intro p hp
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl
    · exact ⟨(tA m0, tstateBytes), by simp, le_rfl, le_rfl⟩
    · exact ⟨(a.words, 8 * a.len), by simp, le_rfl, le_rfl⟩
    · exact ⟨(rcAddr, 192), by simp, le_rfl, le_rfl⟩
  refine call_then hpc4 (hgr s5) ⟨cx.stackOk hat4 (by decide), cx.rcAt hat4 (by decide),
    by rw [hrdi4]; exact hts4, by rw [hrdi4]; exact cx.tstateOk hat4 (by decide),
    by rw [hgb]; decide, by rw [hrdi4]; exact hgot4⟩ fun st5 hpc5 hrsp5 hq5 ↦ ?_
  obtain ⟨hok, hnext, hso, hsv⟩ := hq5
  rw [hgb] at hok hnext
  rw [hrdi4] at hnext hso
  have hso' : SameOutside st3.data.dmem st5.data.dmem (fun q ↦
      InRange (stackBelow st3.data grindStack) grindStack q ∨ InRange (tA m0) tstateBytes q) :=
    NativeRustcVm.SameOutside.mono hso fun _ hq ↦ hq.elim Or.inr Or.inl
  have hb5 := Body.callX hpre hWo hb4 hsv hrsp5 (Sk := grindStack) (by decide) hso'
    (fun _ hq ↦ Or.inl (Or.inl hq))
  have hfr5 := frSame_ts hpre hb4 (by decide) hso'
  have heq5 := scr_call hpre hWo hb4 (Sk := grindStack) (by decide) hso'
    (by decide) (by rw [eqK_len h.lsz]; decide)
    (fun _ hq hq' ↦ (scr_not_t hpre (by rw [eqK_len h.lsz]; decide) hq').1 hq) heq4
  have h12_5 := (hsv.1 .r12 rfl).trans h12_4
  have h15_5 := (hsv.1 .r15 rfl).trans h15_4
  obtain ⟨d5, pc5⟩ := st5
  simp only at hpc5 hb5 hfr5 heq5 h12_5 h15_5 hok hnext
  subst hpc5
  rw [show k + NativeRustcVmX64.Vm.VerifyLayer.b66Offset + b66.length = k + NativeRustcVmX64.Vm.VerifyLayer.b67Offset from by rw [Nat.add_assoc, NativeRustcVmX64.Vm.VerifyLayer.b66_next]]
  have hwf6 := wf0 hS hb5 (vars := fun _ ↦ 0) (ret := 0)
  have hm6 : Match (envB m0 d5 [] (fun _ ↦ 0) 0) (fr 24) d5 :=
    match_ofMachine ⟨rfl, trivial⟩ ⟨hb5.rsp, trivial⟩ trivial trivial trivial
  refine Body.blk (o' := 24) g hb5 hwf6 (blk hp b67_in_code (by simp [b67])) e67 nofun hm6
    (by decide +kernel) (hex0 (by decide +kernel)) fun st7 hm7 hpc7 hb7 _ ↦ ?_
  simp only [PcOk] at hpc7
  rw [show (SBool.cmp .eq .W8 (.bin .and .W8 (.reg .rax) (.reg .rax)) (.lit 0)).eval
      (envB m0 d5 [] (fun _ ↦ 0) 0) = !((grind 0).run s5).isSome from okAl_test hok] at hpc7
  have hd7 : st7.data.dmem = d5.dmem := hm7.dmem_eq hwf6 rfl
  have h12_7 := (hm7.regs .r12 _ rfl).trans h12_5
  have h15_7 := (hm7.regs .r15 _ rfl).trans h15_5
  obtain ⟨d7, pc7⟩ := st7
  simp only at hpc7 hb7 hd7 h12_7 h15_7
  cases hr : (grind 0).run s5 with
  | none =>
    rw [hr] at hpc7
    simp only [Option.isSome_none, Bool.not_false, ↓reduceIte] at hpc7
    rw [lbl hp b86_in_code rfl] at hpc7
    subst hpc7
    exact exit49 hp hpre hWo hb7 (by rw [hrun, hr]; rfl)
  | some q =>
    rw [hr] at hpc7 hnext
    simp only [Option.isSome_some, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hpc7
    subst hpc7
    have hts7 : TStateAt d7.dmem (tA m0) a q.2 := by rw [hd7]; exact hnext q.1 q.2 rfl
    have heq7 : NativeRustcVm.EWsAt d7.dmem (sA m0 + BitVec.ofNat 64 107520)
        (eqKernel lp).toList := by rw [hd7]; exact heq5
    rw [show k + NativeRustcVmX64.Vm.VerifyLayer.b67Offset + b67.length = k + NativeRustcVmX64.Vm.VerifyLayer.b68Offset from by rw [Nat.add_assoc, NativeRustcVmX64.Vm.VerifyLayer.b67_next]]
    have hwf8 := wf0 hS hb7 (vars := fun _ ↦ 0)
      (ret := (Host.addrOf (k + NativeRustcVmX64.Vm.VerifyLayer.b68Offset + b68.length)).toBitVec)
    have hm8 : Match (envB m0 d7 [] (fun _ ↦ 0) (Host.addrOf (k + NativeRustcVmX64.Vm.VerifyLayer.b68Offset + b68.length)).toBitVec)
        (fr 24) d7 :=
      match_ofMachine ⟨rfl, trivial⟩ ⟨hb7.rsp, trivial⟩ trivial trivial trivial
    refine Body.blk (o' := 16) g hb7 hwf8 (blk hp b68_in_code (by simp [b68])) e68
      (fun _ _ ↦ rfl) hm8 (by decide +kernel) (hex0 (by decide +kernel)) fun st9 hm9 hpc9 hb9 _ ↦ ?_
    have hfr9 := frSame_blk (o := 24) (n := 2000) hwf8 hm9 (by decide +kernel) (by decide)
      (by decide +kernel)
    have hts9 := ts_blk0 hpre hwf8 hm9 (by decide +kernel) (by decide +kernel) hts7
    have heq9 := scr_blk0E hpre hwf8 hm9 (by decide +kernel) (by decide +kernel)
      (by decide) (by rw [eqK_len h.lsz]; decide) heq7
    have hrdi9 : reg st9.data .rdi = tA m0 := (hm9.regs .rdi _ rfl).trans h12_7
    have h12_9 := (hm9.regs .r12 _ rfl).trans h12_7
    have h15_9 := (hm9.regs .r15 _ rfl).trans h15_7
    have h13_9 : reg st9.data .r13 = BitVec.ofNat 64 288230376151711742 := hm9.regs .r13 _ rfl
    refine call_then hpc9 (hsq q.2.sponge) (sqPre hpre hWo hb9 hts9 hrdi9)
      fun st10 hpc10 hrsp10 hq10 ↦ ?_
    obtain ⟨hb10, hfr10, h0, h1, hts10, hcs10⟩ := sqPost hpre hb9 hts9 hrdi9 hq10 hrsp10
    have heq10 := scr_call hpre hWo hb9 (Sk := squeezeStack) (by decide)
      (NativeRustcVm.SameOutside.mono hq10.2.2.2.1 fun _ hq ↦ hq.elim Or.inr Or.inl)
      (by decide) (by rw [eqK_len h.lsz]; decide)
      (fun _ hq hq' ↦ (scr_not_t hpre (by rw [eqK_len h.lsz]; decide) hq').1
        (by rw [hrdi9] at hq; exact inRange_mono hq (by decide))) heq9
    have hfrAll : FrSame m0 d.dmem st10.data.dmem 24 2000 := by
      have hf7 : FrSame m0 d.dmem d7.dmem 24 2000 := by
        rw [hd7]; exact ((hfr1.trans hfr2).trans hfr4).trans hfr5
      exact (hf7.trans hfr9).trans hfr10
    have hfinal : C6 m0 a c ch (sqS q.2).1 pt lp t (sqS q.2).2 st10.data :=
      ⟨⟨hb10, hts10,
        FWs.keepR (os := [32, 40, 48, 64, 80, 96, 120, 128, 224]) rfl hfrAll (by decide +kernel) h.fw,
        (hfrAll.sub (o' := 1704) (n' := 264) (by decide) (by decide)).buf h.mu,
        (hfrAll.sub (o' := 1224) (n' := 480) (by decide) (by decide)).ews h.hpt
          (by rw [Array.length_toList, h.psz]; have := (claimPt hpre (fun _ h ↦ h) h.body).1; omega),
        h.psz, h.lsz, heq10,
        (hfrAll.sub (o' := 56) (n' := 8) (by decide) (by decide)).word h.w56 (by decide),
        FWs.keepR (os := [72, 104, 112, 184, 192, 200]) rfl hfrAll (by decide +kernel) h.tw,
        (hcs10 .r12 rfl).trans h12_9, (hcs10 .r15 rfl).trans h15_9⟩,
        h0, h1, (hcs10 .r13 rfl).trans h13_9⟩
    exact at_pc hpc10 (cont _ _ st10.data hfinal (by rw [hrun, hr]; rfl))

end

end NativeRustcVmX64.KeccakGkr.VerifyLayer
