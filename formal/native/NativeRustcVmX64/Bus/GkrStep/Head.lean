module

public import NativeRustcVmX64.Bus.GkrStep.Frame
public import NativeRustcVmX64.Code.Vm.BitLength.Names
public import NativeRustcVmX64.Code.Vm.PolyEval.Names
public import NativeRustcVmX64.Code.Vm.SpongeWSqueeze.Names
public import NativeRustcVmX64.Code.Vm.TStateGrind.Names

/-!
# `gkr_step` up to the combiner's evaluation (x86-64)

`b0` pushes the callee-saved registers (the `GkrStateW` in R14, `step` in RBX, the `TState` in
R15, `last` in R12) and calls `bit_length(1)`; `b1` grinds (`0` bits); `b2` checks it; `b3` keeps
`last` at `44` and squeezes the combiner; `b4` keeps its limb `0` at `104`, its limb `1` in RBP,
and evaluates the values there (`pre_spec`, to `AtPE`).
-/

namespace NativeRustcVmX64.Bus.GkrStep

open NativeRustcX64 NativeRustcX64.Sym NativeRustcVmX64.Vm.GkrStep
open NativeRustcVmX64.Transcript NativeRustcVmX64.Sumcheck NativeRustcVmX64.Bus.Gkr
open NativeVm.Model NativeRustcVm.Transcript NativeRustcVm.Bus

public section

theorem trunc_small (x : BitVec 64) (h : x.toNat ≤ 1) : UnOp.apply .trunc .W32 x = x := by
  have hx : x = 0#64 ∨ x = 1#64 := by
    rcases (show x.toNat = 0 ∨ x.toNat = 1 by omega) with h | h
    · exact .inl (BitVec.eq_of_toNat_eq h)
    · exact .inr (BitVec.eq_of_toNat_eq h)
  rcases hx with rfl | rfl <;> rfl

theorem W01_of_W0 {S : SState} {ivs : List (Nat × Nat)} (h : W0 S ivs = true) :
    W01 S ivs 0 0 = true := by
  unfold W0 W01 at *
  rw [List.all_eq_true] at *
  intro w hw
  simp [h w hw]

/-- Bytes of the frame a block kept (its writes in region 0 apart from them). -/
theorem keepB [Labels] {m0 d d' : MachineData} {rest : List (BitVec 64 × Nat)} {ret : BitVec 64}
    {S : SState} (hwf : (frameEnv m0 d 1408 rest (fun _ ↦ 0) ret).WF)
    (hm : Match (frameEnv m0 d 1408 rest (fun _ ↦ 0) ret) S d') (hmid : MidOk 1408 40 slots S = true ∨
      MidOk 1408 32 slots S = true ∨ MidOk 1408 0 slots S = true) {o : Nat} {bs : List UInt8}
    (hle : o + bs.length ≤ 1408) (hmiss : ∀ w ∈ S.mem, w.r = 0 → w.off + w.n ≤ o ∨ o + bs.length ≤ w.off)
    (h : NativeRustcVm.BytesAt d.dmem (off (fb m0) o) bs) :
    NativeRustcVm.BytesAt d'.dmem (off (fb m0) o) bs :=
  keep_frame hwf hm (by rcases hmid with h | h | h <;> exact writesIn_of_mid h) (by omega) hmiss h

variable [Host] {a : DecArea} {s0 : TState} {g0 : GkrStateW} {m0 : MachineData} {k : Nat}

/-- **`gkr_step` up to the combiner's evaluation**: the prologue, the first grind (of `0` bits),
the combiner, its evaluation of the values. -/
theorem pre_spec (hp : Placed code k) (h : GkrStepPre a s0 g0 m0)
    (hbl : Spec (Labels.label NativeRustcVmX64.Vm.BitLength.entryLabel) BitLengthPre BitLengthPost)
    (hgr : ∀ s, Spec (Labels.label NativeRustcVmX64.Vm.TStateGrind.entryLabel) (GrindPre a s) (GrindPost a s))
    (hsq : ∀ sp, Spec (Labels.label NativeRustcVmX64.Vm.SpongeWSqueeze.entryLabel) (SqueezePre sp) (SqueezePost sp))
    (hpe : Spec (Labels.label NativeRustcVmX64.Vm.PolyEval.entryLabel) PolyEvalPre PolyEvalPost)
    (cont : ∀ d, AtPE a s0 g0 m0 d →
      Eventually (step1 Host.exe) (Goal a s0 g0 m0) ⟨d, Host.addrOf (k + NativeRustcVmX64.Vm.GkrStep.b5Offset)⟩) :
    Eventually (step1 Host.exe) (Goal a s0 g0 m0) ⟨m0, Host.addrOf (k + NativeRustcVmX64.Vm.GkrStep.b0Offset)⟩ := by
  have hS := pre_stack h
  have hN := N_ge
  have cx := ctxF h 1408 N_ge
  have c32 := ctxF h (1408 - 32) (by omega)
  set t := reg m0 .rdi with ht
  set p := reg m0 .rcx with hpdef
  -- `b0`: the prologue, `bit_length(1)`.
  have hwf0 := wf0 h (d := m0) (fun _ h ↦ h) (Host.addrOf (k + NativeRustcVmX64.Vm.GkrStep.b0Offset + b0.length)).toBitVec
  obtain ⟨hpro, hw0, hdi0, h140, h120, hbx0, h150⟩ := ok_b0
  have hw0' := W0_spec hw0
  refine exec_then (infix_of b0_in_code (by simp [b0]) hp) exit_b0 hwf0 (fun _ _ ↦ rfl)
    (match_ofMachine ⟨rfl, trivial⟩ ⟨match_rsp, trivial⟩ trivial trivial trivial)
    fun st1 hm1 hpc1 ↦ ?_
  have fr1 : FR m0 32 st1.data :=
    Fr.of_prologue hS hN hwf0 hm1 hpro slots_le slots_cs fun w hw ↦ (hw0' w hw).1
  have hs1 : NativeRustcVm.SameOutside m0.dmem st1.data.dmem
      (NativeRustcVm.InRange (stackBelow m0 1408) 1408) :=
    fun q hq ↦ hm1.get?_mem0 hwf0 fun hw ↦ hq (written_fb hS hN (fun w hw ↦ ⟨(hw0' w hw).1,
      belowRet_spec (belowRet_of_pro hpro) w hw (hw0' w hw).1⟩) hw)
  have hts1 : TStateAt st1.data.dmem t a s0 :=
    tsKeep h (hm1.kept hwf0) hs1 (fun q hq ↦ .inl (fb_stack h hq)) (pre_ts h)
  have hgs1 : GkrStateWAt st1.data.dmem p g0 :=
    gsKeep h hs1 (fun q hq ↦ .inl (fb_stack h hq)) (pre_gs h)
  have e14 : reg st1.data .r14 = p := rv hm1 h140
  have e15 : reg st1.data .r15 = t := rv hm1 h150
  have ebx : reg st1.data .rbx = reg m0 .rsi := rv hm1 hbx0
  have e12 : reg st1.data .r12 = reg m0 .rdx := (rv hm1 h120).trans (trunc_small _ (pre_last h))
  have hat1 := atC h (by omega) fr1
  simp only [PcOk] at hpc1
  refine Fr.call (c := 32) (Nc := bitLengthStack) (lo := 40) (len := 0) (X := fun _ ↦ False) hS hN
    (by omega) (le32 (by simp)) (slots_call (by omega) (by omega)) (by omega) (outs_not_frame h)
    (fun _ h ↦ h.elim) hbl fr1 hpc1 (c32.stackOk hat1 (le32 (by simp)))
    (fun m' hq ↦ ⟨NativeRustcVm.SameOutside.mono hq.2.1 fun _ h ↦ .inl h, hq.2.2⟩)
    fun m2 fr2 hq2 hs2 hcs2 ↦ ?_
  have hax2 : reg m2 .rax = 1#64 := by
    apply BitVec.eq_of_toNat_eq
    rw [hq2.1, rv hm1 hdi0]
    rfl
  have hk2 : Kept st1.data.dmem m2.dmem := hq2.2.2.2
  have hts2 : TStateAt m2.dmem t a s0 :=
    tsKeep h hk2 hs2 (fun q hq ↦ hq.elim (fun hq ↦ .inl (calleeStack h (by omega) fr1
      (le32 (by simp)) hq)) False.elim) hts1
  have hgs2 : GkrStateWAt m2.dmem p g0 :=
    gsKeep h hs2 (fun q hq ↦ hq.elim (fun hq ↦ .inl (calleeStack h (by omega) fr1
      (le32 (by simp)) hq)) False.elim) hgs1
  -- `b1`: `grind(t, 0)`.
  have hwf1 := wf0 h fr2.frame.kept (Host.addrOf (k + NativeRustcVmX64.Vm.GkrStep.b1Offset + b1.length)).toBitVec
  obtain ⟨hmid1, hw1, hsi1, hdi1, hbp1, hk1⟩ := ok_b1
  refine exec_at (infix_of b1_in_code (by simp [b1]) hp) exit_b1 hwf1 (fun _ _ ↦ rfl)
    (show Host.addrOf (k + NativeRustcVmX64.Vm.GkrStep.b0Offset + b0.length) = _ by rw [Nat.add_assoc]; exact congrArg (fun j ↦ Host.addrOf (k + j)) NativeRustcVmX64.Vm.GkrStep.b0_next)
    (match_head fr2 _) fun st3 hm3 hpc3 ↦ ?_
  obtain ⟨fr3, hs3⟩ := FR.block h fr2 hwf1 hm3 hmid1 (.inl rfl) (W01_of_W0 hw1) (by decide)
    (by omega)
  have hs3' : NativeRustcVm.SameOutside m2.dmem st3.data.dmem (NativeRustcVm.InRange (fb m0) 1360) :=
    NativeRustcVm.SameOutside.mono hs3 fun q hq ↦ hq.elim id fun hq ↦
      absurd hq (by unfold NativeRustcVm.InRange; omega)
  have hts3 : TStateAt st3.data.dmem t a s0 :=
    tsKeep h (hm3.kept hwf1) hs3' (fun q hq ↦ .inl (fb_stack h (inRange_mono hq (by omega)))) hts2
  have hgs3 : GkrStateWAt st3.data.dmem p g0 :=
    gsKeep h hs3' (fun q hq ↦ .inl (fb_stack h (inRange_mono hq (by omega)))) hgs2
  have hbits : grindBits st3.data = 0 := by
    unfold grindBits
    rw [rv hm3 hsi1]
    show (UnOp.apply .trunc .W32 (if CmpOp.apply .ult .W32 (reg m2 .rax) (BitVec.ofNat 64 3) then
      BitVec.ofNat 64 0 else BinOp.apply .sub .W32 (reg m2 .rax) (BitVec.ofNat 64 3))).toNat %
        2 ^ 32 = 0
    rw [hax2]
    rfl
  have edi3 : reg st3.data .rdi = t := (rv hm3 hdi1).trans ((hcs2 .r15 rfl).trans e15)
  have hat3 := atC h (by omega) fr3
  simp only [PcOk] at hpc3
  refine Fr.call (c := 32) (Nc := grindStack) (lo := 40) (len := 0)
    (X := NativeRustcVm.InRange t tstateBytes) hS hN (by omega) (le32 (by simp))
    (slots_call (by omega) (by omega)) (by omega) (outs_not_frame h) (fun _ h ↦ .inl (.inl h))
    (hgr s0) fr3 hpc3 ⟨c32.stackOk hat3 (le32 (by simp)), c32.rcAt hat3 (le32 (by simp)),
      by rw [edi3]; exact hts3, by rw [edi3]; exact c32.tstateOk hat3 (le32 (by simp)),
      by rw [hbits]; decide, by
        rw [edi3]
        apply got_atC h (by omega) fr3 (le32 (by simp))
        intro l hl b hb
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
        rcases hb with rfl | rfl | rfl
        · rw [ht]
          exact ((pre_got h).1 l hl).2.2.2 (reg m0 .rdi, tstateBytes) (by simp)
        · exact ((pre_got h).1 l hl).2.2.2 (a.words, 8 * a.len) (by simp)
        · exact ((pre_got h).1 l hl).2.2.2 (rcAddr, 192) (by simp)⟩
    (fun m' hq ↦ ⟨NativeRustcVm.SameOutside.mono hq.2.2.1 fun q hq ↦ by
      rw [edi3] at hq; exact hq.elim .inr .inl, hq.2.2.2⟩)
    fun m4 fr4 hq4 hs4 hcs4 ↦ ?_
  obtain ⟨hal4, hnx4, -, hsv4⟩ := hq4
  rw [hbits, grind_zero_run] at hal4 hnx4
  rw [edi3] at hnx4
  have hts4 : TStateAt m4.dmem t a s0 := hnx4 () s0 rfl
  have hgs4 : GkrStateWAt m4.dmem p g0 :=
    gsKeep h hs4 (fun q hq ↦ hq.elim (fun hq ↦ .inl (calleeStack h (by omega) fr3
      (le32 (by simp)) hq)) .inr) hgs3
  have k4 : ∀ r ∈ [Reg64.rbx, .r12, .r14, .r15], reg m4 r = reg st1.data r := by
    intro r hr
    have hcs : calleeSaved r = true := by simp at hr; rcases hr with rfl | rfl | rfl | rfl <;> rfl
    exact (hcs4 r hcs).trans ((kr hm3 hk1 (by simp at hr ⊢; tauto)).trans (hcs2 r hcs))
  -- `b2`: the grind's result.
  have hwf5 := wf0 h fr4.frame.kept 0
  obtain ⟨hmid5, hmem5, hk5⟩ := ok_b2
  refine exec_at (infix_of b2_in_code (by simp [b2]) hp) exit_b2 hwf5 nofun
    (show Host.addrOf (k + NativeRustcVmX64.Vm.GkrStep.b1Offset + b1.length) = _ by rw [Nat.add_assoc]; exact congrArg (fun j ↦ Host.addrOf (k + j)) NativeRustcVmX64.Vm.GkrStep.b1_next)
    (match_head fr4 0) fun st5 hm5 hpc5 ↦ ?_
  obtain ⟨fr5, hd5⟩ := FR.block_nil h fr4 hwf5 hm5 hmid5 hmem5
  have hc5 : SBool.eval (frameEnv m0 m4 1408 [] (fun _ ↦ 0) 0) cAl = false := by
    have := testAl_okAl hal4
    exact this
  simp only [PcOk, hc5, Bool.false_eq_true, ↓reduceIte] at hpc5
  have hts5 : TStateAt st5.data.dmem t a s0 := by rw [hd5]; exact hts4
  have hgs5 : GkrStateWAt st5.data.dmem p g0 := by rw [hd5]; exact hgs4
  -- `b3`: `last` at `44`, `squeeze(t)`.
  have hwf6 := wf0 h fr5.frame.kept (Host.addrOf (k + NativeRustcVmX64.Vm.GkrStep.b3Offset + b3.length)).toBitVec
  obtain ⟨hmid6, hw6, h44, hdi6, hk6⟩ := ok_b3
  refine exec_at (infix_of b3_in_code (by simp [b3]) hp) exit_b3 hwf6 (fun _ _ ↦ rfl)
    (hpc5.trans (by rw [Nat.add_assoc]; exact congrArg (fun j ↦ Host.addrOf (k + j)) NativeRustcVmX64.Vm.GkrStep.b2_next)) (match_head fr5 _) fun st6 hm6 hpc6 ↦ ?_
  obtain ⟨fr6, hs6⟩ := FR.block h fr5 hwf6 hm6 hmid6 (.inl rfl) (W01_of_W0 hw6) (by decide)
    (by omega)
  have hs6' : NativeRustcVm.SameOutside st5.data.dmem st6.data.dmem
      (NativeRustcVm.InRange (fb m0) 1360) :=
    NativeRustcVm.SameOutside.mono hs6 fun q hq ↦ hq.elim id fun hq ↦
      absurd hq (by unfold NativeRustcVm.InRange; omega)
  have hts6 : TStateAt st6.data.dmem t a s0 :=
    tsKeep h (hm6.kept hwf6) hs6' (fun q hq ↦ .inl (fb_stack h (inRange_mono hq (by omega))))
      hts5
  have hgs6 : GkrStateWAt st6.data.dmem p g0 :=
    gsKeep h hs6' (fun q hq ↦ .inl (fb_stack h (inRange_mono hq (by omega))))
      hgs5
  have l44 : NativeRustcVm.BytesAt st6.data.dmem (off (fb m0) 44)
      ((List.range 4).map (byteOf (reg m0 .rdx))) := by
    have := hm6.bytesAt_write (r := 0) (o := 44) (n := 4) (b := stackBelow m0 1408)
      (sz := 1408 + 8) rfl (by omega) h44
    have e : (Sym.un .trunc .W32 (.reg .r12)).eval (frameEnv m0 st5.data 1408 [] (fun _ ↦ 0)
        (Host.addrOf (k + NativeRustcVmX64.Vm.GkrStep.b3Offset + b3.length)).toBitVec) = reg m0 .rdx := by
      show UnOp.apply .trunc .W32 (reg st5.data .r12) = _
      rw [kr hm5 hk5 (by simp), k4 .r12 (by simp), e12, trunc_small _ (pre_last h)]
    rwa [e] at this
  have edi6 : reg st6.data .rdi = t :=
    (rv hm6 hdi6).trans ((kr hm5 hk5 (by simp)).trans ((k4 .r15 (by simp)).trans e15))
  have hat6 := atC h (by omega) fr6
  have hle6 := le32 (X := squeezeStack) (by simp)
  have htok6 := c32.tstateOk hat6 hle6
  have hfp := hts6.footprint
  have hpre6 : SqueezePre s0.sponge st6.data := by
    unfold SqueezePre
    rw [edi6]
    have h1 : t.toNat + 760 ≤ (stackBelow st6.data squeezeStack).toNat ∨
        (stackBelow st6.data squeezeStack).toNat + (squeezeStack + 8) ≤ t.toNat := htok6.1
    have h2 : t.toNat + 760 ≤ rcAddr.toNat ∨ rcAddr.toNat + 192 ≤ t.toNat := htok6.2.2
    have hnw : t.toNat + 760 ≤ 2 ^ 64 := hfp.1.2
    refine ⟨c32.stackOk hat6 hle6, c32.rcAt hat6 hle6,
      ⟨fun j hj ↦ hfp.1.1 j (by simp only [spongeBytes] at hj; show j < 760; omega), ?_, ?_, ?_⟩,
      hts6.sponge, ?_⟩
    · show t.toNat + 328 ≤ 2 ^ 64; omega
    · show t.toNat + 328 ≤ _ ∨ _ ≤ t.toNat; omega
    · show t.toNat + 328 ≤ _ ∨ _ ≤ t.toNat; omega
    · apply got_atC h (by omega) fr6 hle6
      intro l hl b hb
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
      rcases hb with rfl | rfl
      · rw [ht]
        have hsep := ((pre_got h).1 l hl).2.2.2 (reg m0 .rdi, tstateBytes) (by simp)
        exact NativeRustcVm.Apart.mono_right hsep (Nat.le_refl _)
          (by dsimp only [Prod.fst, Prod.snd, spongeBytes, tstateBytes]; omega)
      · exact ((pre_got h).1 l hl).2.2.2 (rcAddr, 192) (by simp)
  simp only [PcOk] at hpc6
  have hR : ∀ q, NativeRustcVm.InRange t spongeBytes q → NativeRustcVm.InRange t tstateBytes q :=
    fun q hq ↦ inRange_mono hq (by decide)
  refine Fr.call (c := 32) (Nc := squeezeStack) (lo := 40) (len := 0)
    (X := NativeRustcVm.InRange t spongeBytes) hS hN (by omega) hle6
    (slots_call (by omega) (by omega)) (by omega) (outs_not_frame h)
    (fun q h ↦ .inl (.inl (hR q h))) (hsq s0.sponge) fr6 hpc6 hpre6
    (fun m' hq ↦ ⟨NativeRustcVm.SameOutside.mono hq.2.2.2.1 fun q hq ↦ by
      rw [edi6] at hq; exact hq.elim .inr .inl, hq.2.2.2.2⟩)
    fun m7 fr7 hq7 hs7 hcs7 ↦ ?_
  obtain ⟨hax7, hdx7, hsp7, -, hsv7⟩ := hq7
  rw [edi6] at hsp7
  have hcal7 : ∀ q, NativeRustcVm.InRange (stackBelow st6.data squeezeStack) squeezeStack q →
      NativeRustcVm.InRange (stackBelow m0 gkrStepStack) gkrStepStack q :=
    fun q hq ↦ calleeStack h (by omega) fr6 hle6 hq
  have hts7 : TStateAt m7.dmem t a { s0 with sponge := s0.sponge.squeeze.2 } := by
    refine hts6.with_sponge hsv7.2 (R := NativeRustcVm.InRange (stackBelow st6.data squeezeStack)
      squeezeStack) (fun q hq ↦ (ctxF h 1408 N_ge).stack_not_t (hcal7 q hq)) (fun q hq ↦ hs7 q ?_)
      hsp7
    rintro (h' | h')
    · exact hq (.inr h')
    · obtain ⟨j, hj, hw, hq'⟩ := touch_of_inRange (o := 0) (n := spongeBytes) hfp.1.2 (by show 0 + 328 ≤ 760; omega)
        (by rwa [off_zero])
      exact hq (.inl ⟨j, hj, hw.2, hq'⟩)
  have hgs7 : GkrStateWAt m7.dmem p g0 :=
    gsKeep h hs7 (fun q hq ↦ hq.elim (fun hq ↦ .inl (hcal7 q hq))
      fun hq ↦ .inr (hR q hq)) hgs6
  have l44' : NativeRustcVm.BytesAt m7.dmem (off (fb m0) 44)
      ((List.range 4).map (byteOf (reg m0 .rdx))) :=
    keepCall h fr6 hle6 hs7 (by omega) (by simp) (fun i hi hq ↦
      fb_not_outs h (j := 44 + i) (by simp at hi; omega) (.inl (hR _ hq))) l44
  have k7 : ∀ r ∈ [Reg64.rbx, .r12, .r14, .r15], reg m7 r = reg st1.data r := by
    intro r hr
    have hcs : calleeSaved r = true := by simp at hr; rcases hr with rfl | rfl | rfl | rfl <;> rfl
    exact (hcs7 r hcs).trans ((kr hm6 hk6 (by simp at hr ⊢; tauto)).trans
      ((kr hm5 hk5 (by simp at hr ⊢; tauto)).trans (k4 r hr)))
  -- `b4`: `c₀` at `104`, `c₁` in RBP, `poly_eval(s, 3, c)`.
  have hwf8 := wf0 h fr7.frame.kept (Host.addrOf (k + NativeRustcVmX64.Vm.GkrStep.b4Offset + b4.length)).toBitVec
  obtain ⟨hmid8, hw8, hw104, hbp8, hsi8, hdi8, hdx8, hcx8, hk8⟩ := ok_b4
  refine exec_at (infix_of b4_in_code (by simp [b4]) hp) exit_b4 hwf8 (fun _ _ ↦ rfl)
    (show Host.addrOf (k + NativeRustcVmX64.Vm.GkrStep.b3Offset + b3.length) = _ by rw [Nat.add_assoc]; exact congrArg (fun j ↦ Host.addrOf (k + j)) NativeRustcVmX64.Vm.GkrStep.b3_next)
    (match_head fr7 _) fun st8 hm8 hpc8 ↦ ?_
  obtain ⟨fr8, hs8⟩ := FR.block h fr7 hwf8 hm8 hmid8 (.inl rfl) (W01_of_W0 hw8) (by decide)
    (by omega)
  have hs8' : NativeRustcVm.SameOutside m7.dmem st8.data.dmem
      (NativeRustcVm.InRange (fb m0) 1360) :=
    NativeRustcVm.SameOutside.mono hs8 fun q hq ↦ hq.elim id fun hq ↦
      absurd hq (by unfold NativeRustcVm.InRange; omega)
  have hts8 : TStateAt st8.data.dmem t a { s0 with sponge := s0.sponge.squeeze.2 } :=
    tsKeep h (hm8.kept hwf8) hs8' (fun q hq ↦ .inl (fb_stack h (inRange_mono hq (by omega)))) hts7
  have hgs8 : GkrStateWAt st8.data.dmem p g0 :=
    gsKeep h hs8' (fun q hq ↦ .inl (fb_stack h (inRange_mono hq (by omega)))) hgs7
  have hw8' := W0_spec hw8
  have l448 : NativeRustcVm.BytesAt st8.data.dmem (off (fb m0) 44)
      ((List.range 4).map (byteOf (reg m0 .rdx))) :=
    keepB hwf8 hm8 (.inr (.inl hmid8)) (by simp) (fun w hw _ ↦ by
      obtain ⟨-, q, hq, h1, h2⟩ := hw8' w hw
      simp at hq ⊢; rcases hq with rfl | rfl <;> omega) l44'
  have c1048 : NativeRustcVm.WordAt st8.data.dmem (off (fb m0) 104) s0.sponge.squeeze.1.c0 := by
    have := wordAt_write hm8 (r := 0) (o := 104) (b := stackBelow m0 1408) (sz := 1408 + 8) rfl
      (by omega) hw104
    rwa [show (Sym.reg .rax).eval (frameEnv m0 m7 1408 [] (fun _ ↦ 0)
      (Host.addrOf (k + NativeRustcVmX64.Vm.GkrStep.b4Offset + b4.length)).toBitVec) = s0.sponge.squeeze.1.c0.toBitVec from hax7,
      UInt64.ofBitVec_toBitVec] at this
  have edi8 : reg st8.data .rdi = p := (rv hm8 hdi8).trans ((k7 .r14 (by simp)).trans e14)
  have esi8 : reg st8.data .rsi = BitVec.ofNat 64 3 := rv hm8 hsi8
  have edx8 : reg st8.data .rdx = s0.sponge.squeeze.1.c0.toBitVec := (rv hm8 hdx8).trans hax7
  have ecx8 : reg st8.data .rcx = s0.sponge.squeeze.1.c1.toBitVec := (rv hm8 hcx8).trans hdx7
  have hat8 := atC h (by omega) fr8
  have hle8 := le32 (X := polyEvalStack) (by simp)
  have hgo8 := c32.outOk hat8 hle8 (pre_gk h)
  have hgb : gkrStateBytes = 1064 := rfl
  simp only [PcOk] at hpc8
  refine Fr.call (c := 32) (Nc := polyEvalStack) (lo := 40) (len := 0) (X := fun _ ↦ False) hS hN
    (by omega) hle8 (slots_call (by omega) (by omega)) (by omega) (outs_not_frame h)
    (fun _ h ↦ h.elim) hpe fr8 hpc8 ?_
    (fun m' hq ↦ ⟨NativeRustcVm.SameOutside.mono hq.2.1 fun q hq ↦ hq.elim
      (fun h ↦ absurd h (by unfold NativeRustcX64.InRange; omega)) .inl, hq.2.2⟩)
    fun m9 fr9 hq9 hs9 hcs9 ↦ ?_
  · unfold PolyEvalPre SliceOk Readable OffStack
    rw [edi8, esi8]
    have hm := hgo8.1
    have hnw : p.toNat + 1064 ≤ 2 ^ 64 := hgo8.2.1
    have hap := hgo8.2.2.2.2.1
    rw [hgb] at hm hap
    rw [← hpdef] at hap
    refine ⟨c32.stackOk hat8 hle8, by decide, ⟨fun i hi ↦ hm i (by simp at hi; omega), ?_⟩, ?_⟩
    · show p.toNat + 16 * (BitVec.ofNat 64 3).toNat ≤ 2 ^ 64
      simp; omega
    · unfold NativeRustcX64.Apart at hap
      show p.toNat + 16 * (BitVec.ofNat 64 3).toNat ≤ _ ∨ _ ≤ p.toNat
      rw [show (BitVec.ofNat 64 3).toNat = 3 from rfl]; omega
  obtain ⟨hret9, -, hsv9⟩ := hq9
  have hval : (slice st8.data (reg st8.data .rdi) (reg st8.data .rsi)) = g0.values := by
    unfold slice
    rw [edi8, esi8, show (BitVec.ofNat 64 3).toNat = g0.values.toList.length by
      rw [Array.length_toList, hgs8.values_size]; rfl,
      NativeRustcVm.ewsOf_of_ewsAt hgs8.values, Array.toArray_toList]
  have harg : ewArg (reg st8.data .rdx) (reg st8.data .rcx) = s0.sponge.squeeze.1 := by
    rw [edx8, ecx8]; rfl
  rw [hval, harg] at hret9
  have hcal9 : ∀ q, NativeRustcVm.InRange (stackBelow st8.data polyEvalStack) polyEvalStack q →
      NativeRustcVm.InRange (stackBelow m0 gkrStepStack) gkrStepStack q :=
    fun q hq ↦ calleeStack h (by omega) fr8 hle8 hq
  refine cont m9 ⟨fr9, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact (hcs9 .rbx rfl).trans ((kr hm8 hk8 (by simp)).trans ((k7 .rbx (by simp)).trans ebx))
  · exact (hcs9 .r12 rfl).trans ((kr hm8 hk8 (by simp)).trans ((k7 .r12 (by simp)).trans e12))
  · exact (hcs9 .r14 rfl).trans ((kr hm8 hk8 (by simp)).trans ((k7 .r14 (by simp)).trans e14))
  · exact (hcs9 .r15 rfl).trans ((kr hm8 hk8 (by simp)).trans ((k7 .r15 (by simp)).trans e15))
  · exact (hcs9 .rbp rfl).trans ((rv hm8 hbp8).trans hdx7)
  · exact congrArg UInt64.toBitVec (congrArg EW.c0 hret9)
  · exact congrArg UInt64.toBitVec (congrArg EW.c1 hret9)
  · exact keepCall h fr8 hle8 hs9 (by omega) (by simp) (fun _ _ h ↦ h) l448
  · exact keepCallW h fr8 hle8 hs9 (by omega) (by omega) (fun _ _ h ↦ h) c1048
  · exact tsKeep h hsv9.2 hs9 (fun q hq ↦ hq.elim (fun hq ↦ .inl (hcal9 q hq)) False.elim) hts8
  · exact gsKeep h hs9 (fun q hq ↦ hq.elim (fun hq ↦ .inl (hcal9 q hq)) False.elim) hgs8

end

end NativeRustcVmX64.Bus.GkrStep
