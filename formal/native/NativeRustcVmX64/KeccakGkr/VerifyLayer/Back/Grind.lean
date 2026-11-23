module

public import NativeRustcVmX64.KeccakGkr.VerifyLayer.Back.State
public import NativeRustcVmX64.Code.Vm.BitLength.Names
public import NativeRustcVmX64.Code.Vm.SpongeWSqueeze.Names
public import NativeRustcVmX64.Code.Vm.TStateGrind.Names

/-!
# `verify_layer` on x86-64: the first grind and `s`

From `AfterA` (`b44`, code index `370`): `bit_length(45)` (`b44`), `grind(t, 3)` (`b45`), its
`None` to the exit (`b46`), `squeeze` (`b47`): at `b48` (`383`) with `s` in RAX, RDX (`C1`):
`grindSq`. Tools: a `squeeze` from the frame's `16` (`sqPre`, `sqPost`).
-/

namespace NativeRustcVmX64.KeccakGkr.VerifyLayer

open NativeRustcX64 NativeRustcX64.Sym NativeVm.Model NativeRustcVmX64.Transcript
open NativeRustcVmX64.Vm.VerifyLayer
open NativeRustcVmX64.Sumcheck (Ctx At testAl_eq)
open NativeRustcVm.Transcript (tstateBytes spongeBytes DecArea TStateAt off)
open LeanVM.Parameters LeanVM.Protocol.Verifier

@[expose] public section

/-- **After `s`** (`b48`, code index `383`): `s` in RAX, RDX, the state `s2`. -/
structure C1 (m0 : MachineData) (a : DecArea) (c : KeccakClaimW) (p : Array EW) (ch : EW)
    (s2 : TState) (d : MachineData) : Prop where
  body : Body m0 (wFront m0) 24 d
  ts : TStateAt d.dmem (tA m0) a s2
  prod : NativeRustcVm.EWsAt d.dmem (off (stackBelow m0 2016) 472) p.toList
  psize : p.size = 47
  fw : FWs m0 d.dmem (backWords m0)
  rax : reg d .rax = ch.c0.toBitVec
  rdx : reg d .rdx = ch.c1.toBitVec
  r14 : reg d .r14 = tA m0

end

public section

variable {m0 : MachineData}

/-- The product kept with the frame's bytes from `24`. -/
theorem FrSame.prod {d d' : DataMem} (h : FrSame m0 d d' 24 2000) {p : Array EW}
    (hs : p.size = 47) (hp : NativeRustcVm.EWsAt d (off (stackBelow m0 2016) 472) p.toList) :
    NativeRustcVm.EWsAt d' (off (stackBelow m0 2016) 472) p.toList :=
  (h.sub (o' := 472) (n' := 752) (by decide) (by decide)).ews hp
    (by rw [Array.length_toList, hs])

/-- The back's words kept with the frame's bytes from `24`. -/
theorem FrSame.bw {d d' : DataMem} (h : FrSame m0 d d' 24 2000)
    (hw : FWs m0 d (backWords m0)) : FWs m0 d' (backWords m0) :=
  hw.keepIn h fun q hq ↦ by have := backWords_in q hq; omega

theorem okAl_test {d : MachineData} {b : Bool} (h : OkAl d b) :
    CmpOp.apply .eq .W8 (BinOp.apply .and .W8 (reg d .rax) (reg d .rax)) (BitVec.ofNat 64 0) =
      !b := by
  rw [testAl_eq]
  unfold OkAl boolRet at h
  rw [h]
  cases b <;> rfl

theorem grind3 (x : BitVec 64) (hx : x.toNat = 6) :
    (UnOp.apply .trunc .W32 (if CmpOp.apply .ult .W32 x (BitVec.ofNat 64 3) = true then
      BitVec.ofNat 64 0 else BinOp.apply .sub .W32 x (BitVec.ofNat 64 3))).toNat % 2 ^ 32 = 3 := by
  rw [show x = 6#64 from BitVec.eq_of_toNat_eq hx]
  decide

end

public section

variable [Labels] {a : DecArea} {s : TState} {c : KeccakClaimW} {m0 : MachineData}

/-- `squeeze`'s precondition from the frame's `16`, the `TState` `si` at RDI. -/
theorem sqPre (hpre : VerifyLayerPre a s c m0) {W : BitVec 64 → Prop}
    (hWo : ∀ q, W q → outs m0 q) {d : MachineData} (hb : Body m0 W 16 d) {si : TState}
    (hts : TStateAt d.dmem (tA m0) a si) (hrdi : reg d .rdi = tA m0) :
    SqueezePre si.sponge d := by
  have cx := ctx hpre (F := 2000) (by decide)
  have hat := hb.at_ hpre hWo (by decide)
  have hle : 2000 + squeezeStack ≤ 3232 := by decide
  have htok := cx.tstateOk hat hle
  have hfp := hts.footprint
  unfold SqueezePre
  rw [hrdi]
  have h1 : (tA m0).toNat + 760 ≤ (stackBelow d squeezeStack).toNat ∨
      (stackBelow d squeezeStack).toNat + (squeezeStack + 8) ≤ (tA m0).toNat := htok.1
  have h2 : (tA m0).toNat + 760 ≤ rcAddr.toNat ∨ rcAddr.toNat + 192 ≤ (tA m0).toNat := htok.2.2
  have hnw : (tA m0).toNat + 760 ≤ 2 ^ 64 := hfp.1.2
  refine ⟨cx.stackOk hat hle, cx.rcAt hat hle,
    ⟨fun j hj ↦ hfp.1.1 j (by simp only [spongeBytes] at hj; show j < 760; omega), ?_, ?_, ?_⟩,
    hts.sponge, ?_⟩
  · show (tA m0).toNat + 328 ≤ 2 ^ 64; omega
  · show (tA m0).toNat + 328 ≤ _ ∨ _ ≤ (tA m0).toNat; omega
  · show (tA m0).toNat + 328 ≤ _ ∨ _ ≤ (tA m0).toNat; omega
  · apply hb.got hpre hWo (by decide) (by decide)
    simp only [NativeRustcVm.Transcript.DecArea.region]
    intro p hp
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl
    · exact ⟨(tA m0, tstateBytes), by simp, le_rfl, by
        change (tA m0).toNat + 328 ≤ (tA m0).toNat + 760
        omega⟩
    · exact ⟨_, by simp, le_rfl, le_rfl⟩

/-- **After `squeeze`** from the frame's `16`: the body at `24`, the frame's bytes from `24`
kept, the challenge in RAX, RDX, the `TState` with the sponge squeezed. -/
theorem sqPost (hpre : VerifyLayerPre a s c m0) {d d' : MachineData}
    (hb : Body m0 (wFront m0) 16 d) {si : TState} (hts : TStateAt d.dmem (tA m0) a si)
    (hrdi : reg d .rdi = tA m0) (hpost : SqueezePost si.sponge d d')
    (hrsp : rspOf d' = rspOf d + 8#64) :
    Body m0 (wFront m0) 24 d' ∧ FrSame m0 d.dmem d'.dmem 24 2000 ∧
      reg d' .rax = (sqS si).1.c0.toBitVec ∧ reg d' .rdx = (sqS si).1.c1.toBitVec ∧
      TStateAt d'.dmem (tA m0) a (sqS si).2 ∧
      (∀ r, calleeSaved r = true → reg d' r = reg d r) := by
  have g := geo_of hpre
  have hWo := wFront_outs hpre
  obtain ⟨h0, h1, hsp, hs, hsv⟩ := hpost
  have cx := ctx hpre (F := 2000) (by decide)
  have hat := hb.at_ hpre hWo (by decide)
  have hle : 2000 + squeezeStack ≤ 3232 := by decide
  have hnwt : NativeRustcVm.NoWrap (tA m0) tstateBytes := hts.footprint.1.2
  rw [hrdi] at hsp hs
  have hs' : SameOutside d.dmem d'.dmem (fun q ↦
      InRange (stackBelow d squeezeStack) squeezeStack q ∨ InRange (tA m0) spongeBytes q) :=
    NativeRustcVm.SameOutside.mono hs fun q hq ↦ hq.elim Or.inr Or.inl
  refine ⟨Body.callX hpre hWo hb hsv hrsp (by decide) hs' fun q hq ↦
      .inl (.inl (inRange_mono hq (by decide))),
    frSame_call g hb (by decide) hs' (by decide) (by decide) fun q hq hq' ↦
      (frame_not_t hpre (fr_in g (by decide) hq')).1 (inRange_mono hq (by decide)),
    h0, h1, ?_, hsv.1⟩
  refine hts.with_sponge hsv.2 (R := InRange (stackBelow d squeezeStack) squeezeStack)
    (fun q hq ↦ cx.stack_not_t (cx.inRange_callee hat hle hq).1) (fun q hq ↦ hs q ?_) hsp
  rintro (h | h)
  · obtain ⟨j, hj, hw, hq'⟩ := NativeRustcVm.Transcript.touch_of_inRange (o := 0)
      (n := spongeBytes) hnwt (by decide) (by rwa [NativeRustcVm.Transcript.off_zero])
    exact hq (Or.inl ⟨j, hj, hw.2, hq'⟩)
  · exact hq (Or.inr h)

end

public section

variable [Host] {a : DecArea} {s : TState} {c : KeccakClaimW} {m0 : MachineData} {k : Nat}
  {p : Array EW} {s1 : TState}

/-- **The first grind and `s`**, from `b44` to `b48`. -/
theorem grindSq (hp : Placed code k) (hpre : VerifyLayerPre a s c m0)
    (hbl : Spec (Labels.label NativeRustcVmX64.Vm.BitLength.entryLabel) BitLengthPre BitLengthPost)
    (hgr : ∀ s, Spec (Labels.label NativeRustcVmX64.Vm.TStateGrind.entryLabel) (GrindPre a s) (GrindPost a s))
    (hsq : ∀ sp, Spec (Labels.label NativeRustcVmX64.Vm.SpongeWSqueeze.entryLabel) (SqueezePre sp) (SqueezePost sp))
    {d : MachineData} (h : AfterA m0 a c p s1 d)
    (hrun : runL s c m0 = ((grind (grindingBits (productBits - 1))).run s1).bind
      fun q ↦ rest2 c p q.2)
    (cont : ∀ ch s2 d', C1 m0 a c p ch s2 d' → runL s c m0 = rest3 c p ch s2 →
      Eventually (step1 Host.exe) (Goal a s c m0) ⟨d', Host.addrOf (k + NativeRustcVmX64.Vm.VerifyLayer.b48Offset)⟩) :
    Eventually (step1 Host.exe) (Goal a s c m0) ⟨d, Host.addrOf (k + NativeRustcVmX64.Vm.VerifyLayer.b44Offset)⟩ := by
  have g := geo_of hpre
  have hWo := wFront_outs hpre
  have hS := pre_stack hpre
  have cx := ctx hpre (F := 2000) (by decide)
  rw [grindingBits_46] at hrun
  -- `b44`: `bit_length(45)`.
  have hwf := wf0 hS h.body (vars := fun _ ↦ 0)
    (ret := (Host.addrOf (k + NativeRustcVmX64.Vm.VerifyLayer.b44Offset + b44.length)).toBitVec)
  have hm : Match (envB m0 d [] (fun _ ↦ 0) (Host.addrOf (k + NativeRustcVmX64.Vm.VerifyLayer.b44Offset + b44.length)).toBitVec)
      (fr 24) d :=
    match_ofMachine ⟨rfl, trivial⟩ ⟨h.body.rsp, trivial⟩ trivial trivial trivial
  refine Body.blk (o' := 16) g h.body hwf (blk hp b44_in_code (by simp [b44])) e44
    (fun _ _ ↦ rfl) hm (by decide +kernel) (hex0 (by decide +kernel)) fun st hm1 hpc1 hb1 _ ↦ ?_
  have hfr1 := frSame_blk (o := 24) (n := 2000) hwf hm1 (by decide +kernel) (by decide)
    (by decide +kernel)
  have hts1 := ts_blk0 hpre hwf hm1 (by decide +kernel) (by decide +kernel) h.ts
  have hrdi1 : reg st.data .rdi = 45#64 := hm1.regs .rdi _ rfl
  have hrbx1 : reg st.data .rbx = reg d .rbx := hm1.regs .rbx _ rfl
  have hat1 := hb1.at_ hpre hWo (by decide)
  refine leafX hpre hWo (Sk := bitLengthStack) (by decide) hbl (fun _ _ hq ↦ ⟨hq.2.1, hq.2.2⟩)
    hpc1 hb1 (cx.stackOk hat1 (by decide)) fun d2 hq2 hb2 hfr2 hts2 hcs2 _ ↦ ?_
  have h6 : (reg d2 .rax).toNat = 6 := by rw [hq2.1, hrdi1]; rfl
  have hfr2' := hfr1.trans hfr2
  have hts2' := hts2 _ hts1
  -- `b45`: `grind(t, 3)`.
  rw [show k + NativeRustcVmX64.Vm.VerifyLayer.b44Offset + b44.length = k + NativeRustcVmX64.Vm.VerifyLayer.b45Offset from by rw [Nat.add_assoc, NativeRustcVmX64.Vm.VerifyLayer.b44_next]]
  have hwf3 := wf0 hS hb2 (vars := fun _ ↦ 0)
    (ret := (Host.addrOf (k + NativeRustcVmX64.Vm.VerifyLayer.b45Offset + b45.length)).toBitVec)
  have hm3 : Match (envB m0 d2 [] (fun _ ↦ 0) (Host.addrOf (k + NativeRustcVmX64.Vm.VerifyLayer.b45Offset + b45.length)).toBitVec)
      (fr 24) d2 :=
    match_ofMachine ⟨rfl, trivial⟩ ⟨hb2.rsp, trivial⟩ trivial trivial trivial
  refine Body.blk (o' := 16) g hb2 hwf3 (blk hp b45_in_code (by simp [b45])) e45
    (fun _ _ ↦ rfl) hm3 (by decide +kernel) (hex0 (by decide +kernel)) fun st3 hm4 hpc4 hb4 _ ↦ ?_
  have e3 : ∀ r, (envB m0 d2 [] (fun _ ↦ 0)
      (Host.addrOf (k + NativeRustcVmX64.Vm.VerifyLayer.b45Offset + b45.length)).toBitVec).regs r = reg d2 r := fun _ ↦ rfl
  have hfr4 := frSame_blk (o := 24) (n := 2000) hwf3 hm4 (by decide +kernel) (by decide)
    (by decide +kernel)
  have hts4 := ts_blk0 hpre hwf3 hm4 (by decide +kernel) (by decide +kernel) hts2'
  have hfw4 := ((hfr2'.trans hfr4).bw h.fw)
  have hrdi4 : reg st3.data .rdi = tA m0 := by
    rw [show reg st3.data .rdi = _ from hm4.regs .rdi _ rfl]
    simp only [Sym.eval]
    rw [fload8 (bw40 (hfr2.bw (hfr1.bw h.fw)))]
  have hgb : grindBits st3.data = 3 := by
    unfold grindBits
    rw [show reg st3.data .rsi = _ from hm4.regs .rsi _ rfl]
    simp only [Sym.eval, SBool.eval, e3]
    exact grind3 _ h6
  have hrbx4 : reg st3.data .rbx = 0#64 := hm4.regs .rbx _ rfl
  have hat4 := hb4.at_ hpre hWo (by decide)
  have hgot4 : GotAt st3.data grindStack
      [(reg st3.data .rdi, tstateBytes), (a.words, 8 * a.len), (rcAddr, 192)] ["memcpy"] := by
    rw [hrdi4]
    apply hb4.got hpre hWo (by decide) (by decide)
    simp only [NativeRustcVm.Transcript.DecArea.region]
    intro p hp
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl <;> exact ⟨_, by simp, le_rfl, le_rfl⟩
  refine call_then hpc4 (hgr s1) ⟨cx.stackOk hat4 (by decide), cx.rcAt hat4 (by decide),
    by rw [hrdi4]; exact hts4, by rw [hrdi4]; exact cx.tstateOk hat4 (by decide),
    by rw [hgb]; decide, hgot4⟩ fun st5 hpc5 hrsp5 hq5 ↦ ?_
  obtain ⟨hok, hnext, hso, hsv⟩ := hq5
  rw [hgb] at hok hnext
  rw [hrdi4] at hnext hso
  have hso' : SameOutside st3.data.dmem st5.data.dmem (fun q ↦
      InRange (stackBelow st3.data grindStack) grindStack q ∨ InRange (tA m0) tstateBytes q) :=
    NativeRustcVm.SameOutside.mono hso fun q hq ↦ hq.elim Or.inr Or.inl
  have hb5 : Body m0 (wFront m0) 24 st5.data :=
    Body.callX hpre hWo hb4 hsv hrsp5 (by decide) hso' fun q hq ↦ .inl (.inl hq)
  have hfr5 := frSame_ts hpre hb4 (by decide) hso'
  have hrbx5 : reg st5.data .rbx = 0#64 := (hsv.1 .rbx rfl).trans hrbx4
  obtain ⟨d5, pc5⟩ := st5
  simp only at hpc5 hb5 hfr5 hrbx5 hok hnext hsv
  subst hpc5
  -- `b46`: `None` exits.
  have hwf6 := wf0 hS hb5 (vars := fun _ ↦ 0) (ret := 0)
  have hm6 : Match (envB m0 d5 [] (fun _ ↦ 0) 0) (fr 24) d5 :=
    match_ofMachine ⟨rfl, trivial⟩ ⟨hb5.rsp, trivial⟩ trivial trivial trivial
  rw [show k + NativeRustcVmX64.Vm.VerifyLayer.b45Offset + b45.length = k + NativeRustcVmX64.Vm.VerifyLayer.b46Offset from by rw [Nat.add_assoc, NativeRustcVmX64.Vm.VerifyLayer.b45_next]]
  refine Body.blk (o' := 24) g hb5 hwf6 (blk hp b46_in_code (by simp [b46])) e46 nofun hm6
    (by decide +kernel) (hex0 (by decide +kernel)) fun st7 hm7 hpc7 hb7 _ ↦ ?_
  simp only [PcOk] at hpc7
  rw [show (SBool.cmp .eq .W8 (.bin .and .W8 (.reg .rax) (.reg .rax)) (.lit 0)).eval
      (envB m0 d5 [] (fun _ ↦ 0) 0) = !((grind 3).run s1).isSome from okAl_test hok] at hpc7
  have hd7 : st7.data.dmem = d5.dmem := hm7.dmem_eq hwf6 rfl
  have hrbx7 : reg st7.data .rbx = 0#64 := (hm7.regs .rbx _ rfl).trans hrbx5
  have hk7 : ∀ r ∈ [Reg64.r14], reg st7.data r = reg d5 r :=
    keepR_regs hm7 (by decide +kernel) fun _ ↦ rfl
  obtain ⟨d7, pc7⟩ := st7
  simp only at hpc7 hb7 hd7 hrbx7 hk7
  cases hr : (grind 3).run s1 with
  | none =>
    rw [hr] at hpc7
    simp only [Option.isSome_none, Bool.not_false, ↓reduceIte] at hpc7
    subst hpc7
    have hnone : runL s c m0 = none := by rw [hrun, hr]; rfl
    rw [lbl hp b87_in_code rfl]
    exact exit50 hp hpre hWo hb7 (by rw [hrbx7, hnone]; rfl)
      (fun c' s' he ↦ by rw [hnone] at he; cases he)
  | some q =>
    rw [hr] at hpc7 hnext
    simp only [Option.isSome_some, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hpc7
    subst hpc7
    have hts7 : TStateAt d7.dmem (tA m0) a q.2 := by rw [hd7]; exact hnext q.1 q.2 rfl
    -- `b47`: `squeeze(t)`.
    rw [show k + NativeRustcVmX64.Vm.VerifyLayer.b46Offset + b46.length = k + NativeRustcVmX64.Vm.VerifyLayer.b47Offset from by rw [Nat.add_assoc, NativeRustcVmX64.Vm.VerifyLayer.b46_next]]
    have hwf8 := wf0 hS hb7 (vars := fun _ ↦ 0)
      (ret := (Host.addrOf (k + NativeRustcVmX64.Vm.VerifyLayer.b47Offset + b47.length)).toBitVec)
    have hm8 : Match (envB m0 d7 [] (fun _ ↦ 0) (Host.addrOf (k + NativeRustcVmX64.Vm.VerifyLayer.b47Offset + b47.length)).toBitVec)
        (fr 24) d7 :=
      match_ofMachine ⟨rfl, trivial⟩ ⟨hb7.rsp, trivial⟩ trivial trivial trivial
    have hfw7 : FWs m0 d7.dmem (backWords m0) := by rw [hd7]; exact hfr5.bw hfw4
    refine Body.blk (o' := 16) g hb7 hwf8 (blk hp b47_in_code (by simp [b47])) e47
      (fun _ _ ↦ rfl) hm8 (by decide +kernel) (hex0 (by decide +kernel))
      fun st9 hm9 hpc9 hb9 _ ↦ ?_
    have hfr9 := frSame_blk (o := 24) (n := 2000) hwf8 hm9 (by decide +kernel) (by decide)
      (by decide +kernel)
    have hts9 := ts_blk0 hpre hwf8 hm9 (by decide +kernel) (by decide +kernel) hts7
    have hrdi9 : reg st9.data .rdi = tA m0 := by
      rw [show reg st9.data .rdi = _ from hm9.regs .rdi _ rfl]
      simp only [Sym.eval]
      rw [fload8 (bw40 hfw7)]
    have hr14 : reg st9.data .r14 = tA m0 := by
      rw [show reg st9.data .r14 = _ from hm9.regs .r14 _ rfl]
      simp only [Sym.eval]
      rw [fload8 (bw40 hfw7)]
    refine call_then hpc9 (hsq q.2.sponge) (sqPre hpre hWo hb9 hts9 hrdi9)
      fun st10 hpc10 hrsp10 hq10 ↦ ?_
    obtain ⟨hb10, hfr10, h0, h1, hts10, hcs10⟩ := sqPost hpre hb9 hts9 hrdi9 hq10 hrsp10
    obtain ⟨d10, pc10⟩ := st10
    simp only at hpc10 hb10 hfr10 h0 h1 hts10 hcs10
    subst hpc10
    have hfrA := hfr2'.trans hfr4
    have hprod : NativeRustcVm.EWsAt d10.dmem (off (stackBelow m0 2016) 472) p.toList := by
      have hfrB : FrSame m0 d.dmem d7.dmem 24 2000 := by rw [hd7]; exact hfrA.trans hfr5
      exact ((hfrB.trans hfr9).trans hfr10).prod h.psize h.prod
    refine cont (sqS q.2).1 (sqS q.2).2 d10 ⟨hb10, hts10, hprod, h.psize,
      (hfr9.trans hfr10).bw hfw7, h0, h1, (hcs10 .r14 rfl).trans hr14⟩ ?_
    rw [hrun, hr]
    rfl

end

end NativeRustcVmX64.KeccakGkr.VerifyLayer
