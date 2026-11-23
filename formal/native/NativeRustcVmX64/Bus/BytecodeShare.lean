module

public import NativeRustcVmX64.Bus.BytecodeShare.Check
public import NativeRustcVmX64.Code.Vm.BytecodeShare.Names
public import NativeRustcVmX64.Code.Vm.Dot.Names
public import NativeRustcVmX64.Code.Vm.EWMul.Names
public import NativeRustcVmX64.Code.Vm.EqKernel.Names
public import NativeRustcVmX64.Code.Vm.SumcheckOfSumcheckPlain.Names
public import NativeRustcVmX64.Code.Vm.TStateReadScalar.Names

/-!
# `bytecode_share` on x86-64

`b0` pushes RBX, RBP, R12 to R15 into the 432-byte frame, keeps the output in RBX, the transcript
in R15, the weights in R14, `bytecode_low` in R13, RBP and the point in R12, and reads the share
into the `Option<EW>` at offset `128` (`b1`: none, the tag `0`). `b2` keeps the share at `120`,
`112`, zeroes the slot point (offset `32`) and runs the sumcheck over it (`b3`: none, the tag `0`);
`b4` keeps its claim at `104`, `96` and reads the value (`b5`); then the kernel, the check and the
copy (`BytecodeShare/Check.lean`, `Loop.lean`, `Copy.lean`). **`bytecodeShare_spec`**.
-/

namespace NativeRustcVmX64.Bus.BytecodeShare

open NativeRustcX64 NativeRustcX64.Sym NativeRustcVmX64.Vm.BytecodeShare NativeRustcVmX64.Transcript
open NativeRustcVmX64.Sumcheck NativeVm.Model NativeRustcVm.Transcript
open NativeRustcVm.Bus (busPointCap)

public section

section
variable [Labels] {a : DecArea} {s0 : TState} {m0 : MachineData}

/-- A byte of the `TState` is no byte of the frame. -/
theorem t_not_frame (h : BytecodeSharePre a s0 m0) {j : Nat} (hj : j < 440) :
    ¬ NativeRustcVm.InRange (tAt m0) tstateBytes (off (fa m0) j) := fun hq ↦ by
  have hfnw := (ctx_of h).noWrap_frame
  unfold NativeRustcVm.NoWrap at hfnw
  exact not_frame h (OT_OA _ hq) (inRange_off_self hj (by omega))

end

variable [Host] {a : DecArea} {s0 : TState} {m0 : MachineData} {k : Nat}

/-- **A `read_scalar` call** into the `Option<EW>` at offset `128`: its result there, the next
`TState`, the frame's bytes outside `128` to `152` kept. -/
theorem rs_call (h : BytecodeSharePre a s0 m0)
    (hrs : ∀ s, Spec (Labels.label NativeRustcVmX64.Vm.TStateReadScalar.entryLabel) (ReadScalarPre a s) (ReadScalarPost a s))
    {s : TState} {st : MachineState} {next : Int64} {R : MachineState → Prop}
    (hf : BF m0 (OT m0) 0 st.data)
    (hpc : st.pc = Labels.label NativeRustcVmX64.Vm.TStateReadScalar.entryLabel ∧ retOf st.data = next)
    (hdi : reg st.data .rdi = off (fa m0) 128) (hsi : reg st.data .rsi = tAt m0)
    (hts : TStateAt st.data.dmem (tAt m0) a s)
    (cont : ∀ m2 : MachineData, BF m0 (OT m0) 8 m2 →
      OptEWAt m2.dmem (off (fa m0) 128) ((readScalar.run s).map (·.1)) →
      NextAt m2.dmem (tAt m0) a (readScalar.run s) →
      (∀ {o : Nat} {bs : List UInt8}, 8 ≤ o → o + bs.length ≤ 128 →
        NativeRustcVm.BytesAt st.data.dmem (off (fa m0) o) bs →
        NativeRustcVm.BytesAt m2.dmem (off (fa m0) o) bs) →
      reg m2 .r15 = reg st.data .r15 →
      Eventually (step1 Host.exe) R ⟨m2, next⟩) :
    Eventually (step1 Host.exe) R st := by
  have c := ctx_of h
  have hat := hf.at h (fun q hq ↦ OT_OA q hq)
  have hfnw := c.noWrap_frame
  unfold NativeRustcVm.NoWrap at hfnw
  refine Eventually.bind (Spec.apply (hrs s) hpc.1 ?pre) fun st2 ⟨hpc2, hrsp2, hpost⟩ ↦ ?_
  case pre =>
    unfold ReadScalarPre
    rw [hsi, hdi]
    refine ⟨c.stackOk hat le_rs, c.rcAt hat le_rs, hts, c.tstateOk hat le_rs,
      c.outOk_frame hat le_rs (by omega) (by omega), hf.got_callee h OT_OA le_rs ?_⟩
    intro l hl b hb
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · exact ((pre_got h).1 l hl).2.2.2 _ (by simp)
    · exact ((pre_got h).1 l hl).2.2.2 _ (by simp)
    · exact got_apart_frame (pre_got h) h.1 hl N_ge (by omega)
    · exact ((pre_got h).1 l hl).2.2.2 _ (by simp)
  obtain ⟨hopt, hnext, hso, hsv⟩ := hpost
  rw [hdi] at hopt
  rw [hsi] at hnext
  rw [hsi, hdi] at hso
  obtain ⟨d2, pc2⟩ := st2
  simp only at hpc2 hrsp2 hopt hnext hso hsv
  rw [hpc2, hpc.2]
  have hso' : NativeRustcVm.SameOutside st.data.dmem d2.dmem (fun q ↦
      (NativeRustcVm.InRange (off (fa m0) 128) 24 q ∨ NativeRustcVm.InRange (tAt m0) tstateBytes q) ∨
        NativeRustcVm.InRange (stackBelow st.data readScalarStack) readScalarStack q) :=
    NativeRustcVm.SameOutside.mono hso fun q hq ↦ by
      rcases hq with hq | hq | hq
      · exact .inl (.inl hq)
      · exact .inl (.inr hq)
      · exact .inr hq
  refine cont d2 (hf.call h (fun q hq ↦ OT_OA q hq) le_rs hsv hrsp2 (fun q hq ↦ ?_) hso') hopt
    hnext (fun ho hon hb ↦ keep_call h hat le_rs hso' ho (by omega) (fun i hi hq ↦ ?_) hb)
    (hsv.1 .r15 rfl)
  · rcases hq with hq | hq
    · exact ⟨.inr (stk_local h (by omega) hq), notHigh_local h (by omega) hq⟩
    · exact ⟨.inl hq, notHigh_of_not_frame h (not_frame h (OT_OA q hq))⟩
  · rcases hq with hq | hq
    · exact not_local h (by omega) (by omega) (by omega) hq
    · exact t_not_frame h (by omega) hq

omit [Host] in
/-- A tag word `0` or `1` at offset `128`, as the tests read it. -/
theorem tag_load {d : MachineData} {ret : BitVec 64} {w : UInt64} (hw : w = 0 ∨ w = 1)
    (h : NativeRustcVm.WordAt d.dmem (off (fa m0) 128) w) :
    (envB m0 d ret).load 0 128 4 = BitVec.ofNat 64 w.toNat ∧
      (envB m0 d ret).load 0 128 1 = BitVec.ofNat 64 w.toNat :=
  ⟨load4_of_tag hw h, load1_of_tag hw h⟩

omit [Host] in
/-- An `Option<EW>` at offset `128`, `some`: the element at `136`, `144`. -/
theorem opt_some {d : Mem 64} {x : EW} (h : OptEWAt d (off (fa m0) 128) (some x)) :
    NativeRustcVm.WordAt d (off (fa m0) 128) 1 ∧ NativeRustcVm.WordAt d (off (fa m0) 136) x.c0 ∧
      NativeRustcVm.WordAt d (off (fa m0) 144) x.c1 := by
  obtain ⟨h1, h2⟩ := h
  rw [ewAt_iff, off_off, off_off] at h2
  exact ⟨h1, h2.1, h2.2⟩

/-- **After the sumcheck** (`b3` to `b5`): the value read; the check. -/
theorem after_sc (hp : Placed code k) (h : BytecodeSharePre a s0 m0)
    (hrs : ∀ s, Spec (Labels.label NativeRustcVmX64.Vm.TStateReadScalar.entryLabel) (ReadScalarPre a s) (ReadScalarPost a s))
    (hek : Spec (Labels.label NativeRustcVmX64.Vm.EqKernel.entryLabel) EqKernelPre EqKernelPost)
    (hdot : Spec (Labels.label NativeRustcVmX64.Vm.Dot.entryLabel) DotPre DotPost)
    (hmul : Spec (Labels.label NativeRustcVmX64.Vm.EWMul.entryLabel) EWMulPre EWMulPost)
    {sh : EW} {r : Option ((Array EW × EW) × TState)} {st : MachineData}
    (hf : BF m0 (OT m0) 8 st) (h15 : reg st .r15 = tAt m0)
    (w120 : NativeRustcVm.WordAt st.dmem (off (fa m0) 120) sh.c0)
    (w112 : NativeRustcVm.WordAt st.dmem (off (fa m0) 112) sh.c1)
    (hout : OptEWAt st.dmem (off (fa m0) 128) (r.map (·.1.2)))
    (hsl : ∀ xs c s', r = some ((xs, c), s') → NativeRustcVm.EWsAt st.dmem (off (fa m0) 32) xs.toList)
    (hnext : NextAt st.dmem (tAt m0) a r)
    (hsz : ∀ xs c s', r = some ((xs, c), s') → xs.size = 4)
    (hres : res s0 m0 = r.bind fun y ↦ (readScalar.run y.2).bind fun z ↦
      if (y.1.2 == dot (eqKernel y.1.1) (wts m0) * z.1) = true then
        some ((sh, slice m0 (bAt m0) (reg m0 .r8) ++ y.1.1, z.1), z.2) else none) :
    Eventually (step1 Host.exe) (Goal a s0 m0) ⟨st, Host.addrOf (k + NativeRustcVmX64.Vm.BytecodeShare.b3Offset)⟩ := by
  have c := ctx_of h
  have hwB : ∀ x : UInt64, (NativeRustcVm.wordBytes x).length = 8 := NativeRustcVm.length_wordBytes
  have hl14 : Labels.label NativeRustcVmX64.Vm.BytecodeShare.label_14 = Host.addrOf (k + NativeRustcVmX64.Vm.BytecodeShare.b15Offset) := hp.label NativeRustcVmX64.Vm.BytecodeShare.label_14_at
  have hwf3 := wf_envB h hf.frame.kept 0
  refine exec_then (infix_of b3_in_code (by simp [b3]) hp) exit_b3 hwf3 nofun (match_bodyS hf 0)
    fun st3 hm3 hpc3 ↦ ?_
  obtain ⟨-, -, -, hmid3, hmem3, hk3, -⟩ := ok_test
  obtain ⟨hf3, -⟩ := BF.block h hf hm3 hmid3 (KeepsB.mono hk3 (by simp [six]))
  have hd3 : st3.data.dmem = st.dmem := hm3.dmem_eq hwf3 hmem3
  simp only [PcOk] at hpc3
  cases hr : r with
  | none =>
    rw [hr] at hout
    have ht := (tag_load (ret := 0) (Or.inl rfl) hout).2
    have hc : c3.eval (envB m0 st 0) = true := by
      show CmpOp.apply .eq .W8 ((envB m0 st 0).load 0 128 1) (BitVec.ofNat 64 0) = true
      rw [ht]; decide
    simp only [hc, ↓reduceIte] at hpc3
    rw [hl14] at hpc3
    obtain ⟨d3, pc3⟩ := st3
    simp only at hpc3
    subst hpc3
    exact none15 hp h hf3 (fun q hq ↦ OT_OA q hq) (by rw [hres, hr]; rfl)
  | some y =>
    obtain ⟨⟨sp, cl⟩, s2⟩ := y
    rw [hr] at hout
    obtain ⟨ht1, hc0, hc1⟩ := opt_some hout
    have hsp := hsl sp cl s2 hr
    have hspz := hsz sp cl s2 hr
    have hts := hnext (sp, cl) s2 hr
    have ht := (tag_load (ret := 0) (Or.inr rfl) ht1).2
    have hc : c3.eval (envB m0 st 0) = false := by
      show CmpOp.apply .eq .W8 ((envB m0 st 0).load 0 128 1) (BitVec.ofNat 64 0) = false
      rw [ht]; decide
    simp only [hc, Bool.false_eq_true, ↓reduceIte] at hpc3
    rw [NativeRustcVmX64.Vm.BytecodeShare.b3_length] at hpc3
    -- `b4`: the claim kept, `read_scalar`.
    have hwf4 := wf_envB h hf3.frame.kept (Host.addrOf (k + NativeRustcVmX64.Vm.BytecodeShare.b4Offset + b4.length)).toBitVec
    refine exec_at (infix_of b4_in_code (by simp [b4]) hp) exit_b4 hwf4 (fun _ _ ↦ rfl) hpc3
      (match_bodyS hf3 _) fun st4 hm4 hpc4 ↦ ?_
    obtain ⟨hmid4, hrdi4, hrsi4, hk4, hW96, hW104, hws4⟩ := ok_b4
    obtain ⟨hf4, hs4⟩ := BF.block h hf3 hm4 hmid4 (KeepsB.mono hk4 (by simp [six]))
    have hin4 := writesIn_of_mid hmid4
    have kb4 : ∀ {o : Nat} {bs : List UInt8}, 8 ≤ o → o + bs.length ≤ 96 ∨ 112 ≤ o →
        o + bs.length ≤ 432 → NativeRustcVm.BytesAt st.dmem (off (fa m0) o) bs →
        NativeRustcVm.BytesAt st4.data.dmem (off (fa m0) o) bs := fun h1 h2 h3 hb ↦
      keep_frame hwf4 hm4 hin4 (by omega) (miss_of_writesF hws4 h1 h2) (by rw [hd3]; exact hb)
    have w96 : NativeRustcVm.WordAt st4.data.dmem (off (fa m0) 96) cl.c1 :=
      wordAt_written hm4 (r := 0) rfl (by omega) hW96 (load_ofMachine (o := 144) rfl
        (by rw [hd3]; exact hc1))
    have w104 : NativeRustcVm.WordAt st4.data.dmem (off (fa m0) 104) cl.c0 :=
      wordAt_written hm4 (r := 0) rfl (by omega) hW104 (load_ofMachine (o := 136) rfl
        (by rw [hd3]; exact hc0))
    have hts4 : TStateAt st4.data.dmem (tAt m0) a s2 :=
      tstate_keep h hs4 (hm4.kept hwf4) (fun q hq ↦ .inr (.inr (c.inRange_frame hq)))
        (by rw [hd3]; exact hts)
    have e15 : reg st3.data .r15 = tAt m0 :=
      (hm3.regs .r15 _ (KeepsB.reg hk3 (by simp [six]))).trans h15
    refine rs_call h hrs hf4 hpc4 ((hm4.regs .rdi _ hrdi4).trans (eval_ptr0 128))
      ((hm4.regs .rsi _ hrsi4).trans e15) hts4 fun m5 hf5 hopt5 hnext5 kc5 _ ↦ ?_
    have k45 : ∀ {o : Nat} {bs : List UInt8}, 8 ≤ o → o + bs.length ≤ 96 ∨ 112 ≤ o →
        o + bs.length ≤ 128 → NativeRustcVm.BytesAt st.dmem (off (fa m0) o) bs →
        NativeRustcVm.BytesAt m5.dmem (off (fa m0) o) bs := fun h1 h2 h3 hb ↦
      kc5 h1 h3 (kb4 h1 h2 (by omega) hb)
    have w120_5 := k45 (bs := NativeRustcVm.wordBytes _) (by omega) (by simp [hwB])
      (by simp [hwB]) w120
    have w112_5 := k45 (bs := NativeRustcVm.wordBytes _) (by omega) (by simp [hwB])
      (by simp [hwB]) w112
    have w104_5 := kc5 (bs := NativeRustcVm.wordBytes _) (by omega) (by simp [hwB]) w104
    have w96_5 := kc5 (bs := NativeRustcVm.wordBytes _) (by omega) (by simp [hwB]) w96
    have hspB : (sp.toList.flatMap NativeRustcVm.ewBytes).length = 64 := by
      rw [NativeRustcVm.length_ewsBytes, Array.length_toList, hspz]
    have hsp5 := k45 (bs := sp.toList.flatMap NativeRustcVm.ewBytes) (by omega)
      (by rw [hspB]; omega) (by rw [hspB]; omega) hsp
    -- `b5`: the value's tag.
    have hwf5 := wf_envB h hf5.frame.kept 0
    refine exec_at (infix_of b5_in_code (by simp [b5]) hp) exit_b5 hwf5 nofun rfl
      (match_bodyS hf5 0) fun st6 hm6 hpc6 ↦ ?_
    obtain ⟨-, -, -, -, -, -, hmid6, hmem6, hk6, -⟩ := ok_test
    obtain ⟨hf6, -⟩ := BF.block h hf5 hm6 hmid6 (KeepsB.mono hk6 (by simp [six]))
    have hd6 : st6.data.dmem = m5.dmem := hm6.dmem_eq hwf5 hmem6
    simp only [PcOk] at hpc6
    cases hr3 : readScalar.run s2 with
    | none =>
      rw [hr3] at hopt5
      have ht := (tag_load (ret := 0) (Or.inl rfl) hopt5).2
      have hc : c3.eval (envB m0 m5 0) = true := by
        show CmpOp.apply .eq .W8 ((envB m0 m5 0).load 0 128 1) (BitVec.ofNat 64 0) = true
        rw [ht]; decide
      simp only [hc, ↓reduceIte] at hpc6
      rw [hl14] at hpc6
      obtain ⟨d6, pc6⟩ := st6
      simp only at hpc6
      subst hpc6
      exact none15 hp h hf6 (fun q hq ↦ OT_OA q hq) (by rw [hres, hr]; simp [hr3])
    | some z =>
      obtain ⟨v, s3⟩ := z
      rw [hr3] at hopt5
      obtain ⟨ht1', hv0, hv1⟩ := opt_some hopt5
      have hts5 := hnext5 v s3 hr3
      have ht := (tag_load (ret := 0) (Or.inr rfl) ht1').2
      have hc : c3.eval (envB m0 m5 0) = false := by
        show CmpOp.apply .eq .W8 ((envB m0 m5 0).load 0 128 1) (BitVec.ofNat 64 0) = false
        rw [ht]; decide
      simp only [hc, Bool.false_eq_true, ↓reduceIte] at hpc6
      rw [NativeRustcVmX64.Vm.BytecodeShare.b5_length] at hpc6
      obtain ⟨d6, pc6⟩ := st6
      simp only at hpc6 hd6 hf6
      subst hpc6
      exact check hp h hek hdot hmul hf6 (by rw [hd6]; exact w120_5) (by rw [hd6]; exact w112_5)
        (by rw [hd6]; exact w104_5) (by rw [hd6]; exact w96_5) (by rw [hd6]; exact hv0)
        (by rw [hd6]; exact hv1) (by rw [hd6]; exact hsp5) hspz (by rw [hd6]; exact hts5)
        (by rw [hres, hr]; simp [hr3])
/-- **After the share** (`b1`, `b2`): the sumcheck over the slot point. -/
theorem after_share (hp : Placed code k) (h : BytecodeSharePre a s0 m0)
    (hrs : ∀ s, Spec (Labels.label NativeRustcVmX64.Vm.TStateReadScalar.entryLabel) (ReadScalarPre a s) (ReadScalarPost a s))
    (hsc : ∀ s, Spec (Labels.label NativeRustcVmX64.Vm.SumcheckOfSumcheckPlain.entryLabel) (SumcheckPlainPre a s)
      (SumcheckPlainPost a s))
    (hek : Spec (Labels.label NativeRustcVmX64.Vm.EqKernel.entryLabel) EqKernelPre EqKernelPost)
    (hdot : Spec (Labels.label NativeRustcVmX64.Vm.Dot.entryLabel) DotPre DotPost)
    (hmul : Spec (Labels.label NativeRustcVmX64.Vm.EWMul.entryLabel) EWMulPre EWMulPost)
    {st : MachineData} (hf : BF m0 (OT m0) 8 st) (h15 : reg st .r15 = tAt m0)
    (hout : OptEWAt st.dmem (off (fa m0) 128) ((readScalar.run s0).map (·.1)))
    (hnext : NextAt st.dmem (tAt m0) a (readScalar.run s0)) :
    Eventually (step1 Host.exe) (Goal a s0 m0) ⟨st, Host.addrOf (k + NativeRustcVmX64.Vm.BytecodeShare.b1Offset)⟩ := by
  have c := ctx_of h
  have hfnw := c.noWrap_frame
  unfold NativeRustcVm.NoWrap at hfnw
  have hfa : (fa m0).toNat = (stackBelow m0 432).toNat := rfl
  have hwB : ∀ x : UInt64, (NativeRustcVm.wordBytes x).length = 8 := NativeRustcVm.length_wordBytes
  have hl14 : Labels.label NativeRustcVmX64.Vm.BytecodeShare.label_14 = Host.addrOf (k + NativeRustcVmX64.Vm.BytecodeShare.b15Offset) := hp.label NativeRustcVmX64.Vm.BytecodeShare.label_14_at
  have hwf1 := wf_envB h hf.frame.kept 0
  refine exec_then (infix_of b1_in_code (by simp [b1]) hp) exit_b1 hwf1 nofun (match_bodyS hf 0)
    fun st1 hm1 hpc1 ↦ ?_
  obtain ⟨hmid1, hmem1, hk1, -⟩ := ok_test
  obtain ⟨hf1, -⟩ := BF.block h hf hm1 hmid1 (KeepsB.mono hk1 (by simp [six]))
  have hd1 : st1.data.dmem = st.dmem := hm1.dmem_eq hwf1 hmem1
  have e15 : reg st1.data .r15 = tAt m0 := (hm1.regs .r15 _ (KeepsB.reg hk1 (by simp [six]))).trans h15
  simp only [PcOk] at hpc1
  cases hr1 : readScalar.run s0 with
  | none =>
    rw [hr1] at hout
    have ht := (tag_load (ret := 0) (Or.inl rfl) hout).1
    have hc : c1.eval (envB m0 st 0) = true := by
      show (!(CmpOp.apply .eq .W32 ((envB m0 st 0).load 0 128 4) (BitVec.ofNat 64 1))) = true
      rw [ht]; decide
    simp only [hc, ↓reduceIte] at hpc1
    rw [hl14] at hpc1
    obtain ⟨d1, pc1⟩ := st1
    simp only at hpc1
    subst hpc1
    exact none15 hp h hf1 (fun q hq ↦ OT_OA q hq) (by rw [res, bytecodeShare_run, hr1]; rfl)
  | some x =>
  obtain ⟨sh, s1⟩ := x
  rw [hr1] at hout
  obtain ⟨ht1, hs0, hs1⟩ := opt_some hout
  simp only at hs0 hs1
  have hts := hnext sh s1 hr1
  have ht := (tag_load (ret := 0) (Or.inr rfl) ht1).1
  have hc : c1.eval (envB m0 st 0) = false := by
    show (!(CmpOp.apply .eq .W32 ((envB m0 st 0).load 0 128 4) (BitVec.ofNat 64 1))) = false
    rw [ht]; decide
  simp only [hc, Bool.false_eq_true, ↓reduceIte] at hpc1
  rw [NativeRustcVmX64.Vm.BytecodeShare.b1_length] at hpc1
  -- `b2`: the share kept, the slot point zeroed, the sumcheck.
  have hwf2 := wf_envB h hf1.frame.kept (Host.addrOf (k + NativeRustcVmX64.Vm.BytecodeShare.b2Offset + b2.length)).toBitVec
  refine exec_at (infix_of b2_in_code (by simp [b2]) hp) exit_b2 hwf2 (fun _ _ ↦ rfl) hpc1
    (match_bodyS hf1 _) fun st2 hm2 hpc2 ↦ ?_
  obtain ⟨hmid2, hrdi2, hrsi2, hrdx2, hrcx2, hr8_2, hr9_2, hk2, hW8, hW112, hW120, hws2⟩ := ok_b2
  obtain ⟨hf2, hs2⟩ := BF.block h hf1 hm2 hmid2 (KeepsB.mono hk2 (by simp [six]))
  rw [← hd1] at hs0 hs1
  have w8 : NativeRustcVm.WordAt st2.data.dmem (off (fa m0) 8) 4 :=
    wordAt_written hm2 (r := 0) rfl (by omega) hW8 rfl
  have w120 : NativeRustcVm.WordAt st2.data.dmem (off (fa m0) 120) sh.c0 :=
    wordAt_written hm2 (r := 0) rfl (by omega) hW120 (load_ofMachine (o := 136) rfl hs0)
  have w112 : NativeRustcVm.WordAt st2.data.dmem (off (fa m0) 112) sh.c1 :=
    wordAt_written hm2 (r := 0) rfl (by omega) hW112 (load_ofMachine (o := 144) rfl hs1)
  have hts2 : TStateAt st2.data.dmem (tAt m0) a s1 :=
    tstate_keep h hs2 (hm2.kept hwf2) (fun q hq ↦ .inr (.inr (c.inRange_frame hq)))
      (by rw [hd1]; exact hts)
  have hat2 := hf2.at h (fun q hq ↦ OT_OA q hq)
  have e2di : reg st2.data .rdi = off (fa m0) 128 := (hm2.regs .rdi _ hrdi2).trans (eval_ptr0 128)
  have e2si : reg st2.data .rsi = tAt m0 := (hm2.regs .rsi _ hrsi2).trans e15
  have e2r9 : reg st2.data .r9 = off (fa m0) 32 := (hm2.regs .r9 _ hr9_2).trans (eval_ptr0 32)
  have e2r8 : (reg st2.data .r8).toNat = 3 := by
    rw [show reg st2.data .r8 = _ from hm2.regs .r8 _ hr8_2]; rfl
  have e2cl : claimArg st2.data = sh := by
    unfold claimArg
    rw [show reg st2.data .rdx = _ from hm2.regs .rdx _ hrdx2,
      show reg st2.data .rcx = _ from hm2.regs .rcx _ hrcx2]
    simp only [Sym.eval]
    rw [load_ofMachine (o := 136) rfl hs0, load_ofMachine (o := 144) rfl hs1]
  have hsp2 : rspOf st2.data = fa m0 := by rw [hf2.frame.sp, off_zero]
  have hargA : rspOf st2.data + 8#64 = off (fa m0) 8 := by rw [hsp2]
  have e2n : (stackArg st2.data 0).toNat = 4 := by
    unfold stackArg
    rw [show rspOf st2.data + BitVec.ofNat 64 (8 + 8 * 0) = off (fa m0) 8 by rw [hsp2],
      NativeRustcVm.wordOf_of_wordAt w8]
    rfl
  have o128 := c.outOk_frame hat2 le_sc (o := 128) (n := 24) (by omega) (by omega)
  have o32 := c.outOk_frame hat2 le_sc (o := 32) (n := 64) (by omega) (by omega)
  refine call_then hpc2 (hsc s1) ?pre fun st3 hpc3 hrsp3 hpost3 ↦ ?_
  case pre =>
    unfold SumcheckPlainPre SumcheckOk
    rw [e2si, e2di, e2r9, e2r8, e2n]
    refine ⟨⟨by rw [hargA]; exact mapped_off (c.mapped_frame hf2.frame.kept) (by omega),
      by rw [hsp2]; omega⟩,
      c.stackOk hat2 le_sc, c.rcAt hat2 le_sc, hts2, c.tstateOk hat2 le_sc, by omega,
      by decide, o128, o32, ?_, hf2.got_callee h OT_OA le_sc ?_⟩
    · unfold NativeRustcX64.Apart
      rw [toNat_off (by omega), toNat_off (by omega)]
      omega
    · intro l hl b hb
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
      rcases hb with rfl | rfl | rfl | rfl | rfl
      · exact ((pre_got h).1 l hl).2.2.2 _ (by simp)
      · exact ((pre_got h).1 l hl).2.2.2 _ (by simp)
      · exact got_apart_frame (pre_got h) h.1 hl N_ge (by omega)
      · exact got_apart_frame (pre_got h) h.1 hl N_ge (by omega)
      · exact ((pre_got h).1 l hl).2.2.2 _ (by simp)
  obtain ⟨hout3, hso3, hsv3⟩ := hpost3
  rw [e2si, e2di, e2r9, e2r8, e2n, e2cl] at hout3
  rw [e2si, e2di, e2r9, e2n] at hso3
  obtain ⟨hopt3, hsl3, hnext3⟩ := hout3
  have hso3' : NativeRustcVm.SameOutside st2.data.dmem st3.data.dmem (fun q ↦
      (NativeRustcVm.InRange (off (fa m0) 128) 24 q ∨ NativeRustcVm.InRange (off (fa m0) 32) 64 q ∨
        NativeRustcVm.InRange (tAt m0) tstateBytes q) ∨
        NativeRustcVm.InRange (stackBelow st2.data sumcheckPlainStack) sumcheckPlainStack q) :=
    NativeRustcVm.SameOutside.mono hso3 fun q hq ↦ by
      rcases hq with hq | hq | hq | hq
      · exact .inl (.inl hq)
      · exact .inl (.inr (.inl hq))
      · exact .inl (.inr (.inr hq))
      · exact .inr hq
  have hf3 : BF m0 (OT m0) 8 st3.data :=
    hf2.call h (fun q hq ↦ OT_OA q hq) le_sc hsv3 hrsp3 (fun q hq ↦ by
      rcases hq with hq | hq | hq
      · exact ⟨.inr (stk_local h (by omega) hq), notHigh_local h (by omega) hq⟩
      · exact ⟨.inr (stk_local h (by omega) hq), notHigh_local h (by omega) hq⟩
      · exact ⟨.inl hq, notHigh_of_not_frame h (not_frame h (OT_OA q hq))⟩) hso3'
  have kc3 : ∀ {o : Nat} {bs : List UInt8}, 112 ≤ o → o + bs.length ≤ 128 →
      NativeRustcVm.BytesAt st2.data.dmem (off (fa m0) o) bs →
      NativeRustcVm.BytesAt st3.data.dmem (off (fa m0) o) bs := fun h1 h2 hb ↦
    keep_call h hat2 le_sc hso3' (by omega) (by omega) (fun i hi hq ↦ by
      rcases hq with hq | hq | hq
      · exact not_local h (by omega) (by omega) (by omega) hq
      · exact not_local h (by omega) (by omega) (by omega) hq
      · exact t_not_frame h (by omega) hq) hb
  rw [NativeRustcVmX64.Vm.BytecodeShare.b2_length] at hpc3
  obtain ⟨d3, pc3⟩ := st3
  simp only at hpc3 hf3 kc3 hopt3 hsl3 hnext3 hsv3
  subst hpc3
  refine after_sc hp h hrs hek hdot hmul hf3 ((hsv3.1 .r15 rfl).trans
      ((hm2.regs .r15 _ (KeepsB.reg hk2 (by simp [six]))).trans e15))
    (kc3 (by omega) (by simp [hwB]) w120) (kc3 (by omega) (by simp [hwB]) w112) hopt3 hsl3 hnext3
    (fun xs c s' hr ↦ sumcheckPlain_size hr) ?_
  rw [res, bytecodeShare_run, hr1]
  rfl

/-- **`bytecode_share`'s contract.** -/
theorem bytecodeShare_spec (hp : Placed code k)
    (hrs : ∀ s, Spec (Labels.label NativeRustcVmX64.Vm.TStateReadScalar.entryLabel) (ReadScalarPre a s) (ReadScalarPost a s))
    (hsc : ∀ s, Spec (Labels.label NativeRustcVmX64.Vm.SumcheckOfSumcheckPlain.entryLabel) (SumcheckPlainPre a s)
      (SumcheckPlainPost a s))
    (hek : Spec (Labels.label NativeRustcVmX64.Vm.EqKernel.entryLabel) EqKernelPre EqKernelPost)
    (hdot : Spec (Labels.label NativeRustcVmX64.Vm.Dot.entryLabel) DotPre DotPost)
    (hmul : Spec (Labels.label NativeRustcVmX64.Vm.EWMul.entryLabel) EWMulPre EWMulPost) :
    Spec (Labels.label NativeRustcVmX64.Vm.BytecodeShare.entryLabel) (BytecodeSharePre a s0) (BytecodeSharePost a s0) := by
  intro m0 h
  have c := ctx_of h
  rw [show Labels.label NativeRustcVmX64.Vm.BytecodeShare.entryLabel = Host.addrOf (k + NativeRustcVmX64.Vm.BytecodeShare.b0Offset) from hp.label NativeRustcVmX64.Vm.BytecodeShare.entry_at]
  let ret := (Host.addrOf (k + NativeRustcVmX64.Vm.BytecodeShare.b0Offset + b0.length)).toBitVec
  have hwf := wf_envB h (m0 := m0) (d := m0) (fun _ h ↦ h) ret
  have hm : Match (envB m0 m0 ret) entryS m0 :=
    match_ofMachine ⟨rfl, trivial⟩ ⟨match_rsp, trivial⟩ trivial trivial trivial
  refine exec_then (infix_of b0_in_code (by simp [b0]) hp) exit_b0 hwf (fun _ _ ↦ rfl) hm
    fun st hm1 hpc ↦ ?_
  obtain ⟨hpro, hrdi, hrsi, hrbx, hrbp, hr12, hr13, hr14, hr15, -⟩ := ok_b0
  have hs : NativeRustcVm.SameOutside m0.dmem st.data.dmem (NativeRustcVm.InRange (fa m0) 432) :=
    fun q hq ↦ hm1.get?_mem0 hwf fun hw ↦ hq (written_fr (belowRet_of_pro hpro) c.noWrap_frame hw)
  have hf : BF m0 (OT m0) 0 st.data :=
    ⟨Frame.of_prologue Frame.entry hwf hm1 hpro slots_le slots_cs,
      NativeRustcVm.SameOutside.mono hs fun q hq ↦ .inr (c.inRange_frame hq),
      hm1.regs .rbx _ hrbx, hm1.regs .rbp _ hrbp, hm1.regs .r12 _ hr12, hm1.regs .r13 _ hr13,
      hm1.regs .r14 _ hr14⟩
  have hts : TStateAt st.data.dmem (tAt m0) a s0 :=
    tstate_keep h hs (hm1.kept hwf) (fun q hq ↦ .inr (.inr (c.inRange_frame hq))) (pre_parts h).2.2.1
  simp only [PcOk] at hpc
  refine rs_call h hrs hf hpc ((hm1.regs .rdi _ hrdi).trans (eval_ptr0 128)) (hm1.regs .rsi _ hrsi)
    hts fun m2 hf2 hopt hnext _ h15 ↦ ?_
  rw [NativeRustcVmX64.Vm.BytecodeShare.b0_length]
  exact after_share hp h hrs hsc hek hdot hmul hf2 (h15.trans (hm1.regs .r15 _ hr15)) hopt hnext

end

end NativeRustcVmX64.Bus.BytecodeShare
