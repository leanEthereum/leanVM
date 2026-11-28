module

public import NativeRustcVmX64.Bus.GkrStep.Head
public import NativeRustcVmX64.Code.Vm.TStateReadScalars.Names

/-!
# `gkr_step`'s children (x86-64)

From `AtCh` (`b9`): the claim copied to `88`, `80`, the children's area `112` to `304` zeroed, then
three rounds (`rs_round`) of `read_scalars(t, frame + o, 2^step)` (`o` = `112`, `176`, `240`,
from `b9`, `b11`, `b13`) and the test of its result (`b10`, `b12`, `b14`) (`ch_spec`, to `AtPr`).
-/

namespace NativeRustcVmX64.Bus.GkrStep

open NativeRustcX64 NativeRustcX64.Sym NativeRustcVmX64.Vm.GkrStep
open NativeRustcVmX64.Transcript NativeRustcVmX64.Sumcheck NativeRustcVmX64.Bus.Gkr
open NativeVm.Model NativeRustcVm.Transcript NativeRustcVm.Bus
open NativeRustcVm.Sumcheck (readScalars_size)

public section
variable [Host] {a : DecArea} {s0 : TState} {g0 : GkrStateW} {m0 : MachineData} {k : Nat}

omit [Host] in
theorem cs_mem {r : Reg64} (h : calleeSaved r = true) : r ∈ cs6 := by
  cases r <;> first | exact absurd h (by decide) | simp [cs6]

theorem two_pow_le (h : GkrStepPre a s0 g0 m0) : 2 ^ (reg m0 .rsi).toNat ≤ 4 := by
  rcases pre_step h with e | e <;> rw [e] <;> decide

/-- **A round of the children**: `read_scalars(t, frame + o, 2^step)` from the call, then the test
of its result (`b10`, at `j`). -/
theorem rs_round (hp : Placed code k) (h : GkrStepPre a s0 g0 m0)
    (hrs : ∀ s, Spec (Labels.label NativeRustcVmX64.Vm.TStateReadScalars.entryLabel) (ReadScalarsPre a s) (ReadScalarsPost a s))
    {st : MachineState} {j : Nat} (hb : b10.IsInfixAt Host.prog (k + j))
    (fr : FR m0 32 st.data)
    (hpc : st.pc = Labels.label NativeRustcVmX64.Vm.TStateReadScalars.entryLabel ∧ retOf st.data = Host.addrOf (k + j))
    {o : Nat} (ho : 40 ≤ o) (ho' : o + 64 ≤ 1360)
    (hsi : reg st.data .rsi = off (fb m0) o) (hdi : reg st.data .rdi = reg m0 .rdi)
    (hdx : (reg st.data .rdx).toNat = 2 ^ (reg m0 .rsi).toNat) {s : TState}
    (hts : TStateAt st.data.dmem (reg m0 .rdi) a s)
    (hgs : GkrStateWAt st.data.dmem (reg m0 .rcx) g0)
    (hfail : (readScalars (2 ^ (reg m0 .rsi).toNat)).run s = none → run0 s0 g0 m0 = none)
    (cont : ∀ (d' : MachineData) (ys : Array EW) (s' : TState),
      (readScalars (2 ^ (reg m0 .rsi).toNat)).run s = some (ys, s') → FR m0 40 d' →
      (∀ r, calleeSaved r = true → reg d' r = reg st.data r) →
      NativeRustcVm.EWsAt d'.dmem (off (fb m0) o) ys.toList →
      TStateAt d'.dmem (reg m0 .rdi) a s' → GkrStateWAt d'.dmem (reg m0 .rcx) g0 →
      (∀ {o' : Nat} {bs : List UInt8}, 32 ≤ o' → o' + bs.length ≤ 1408 →
        (o' + bs.length ≤ o ∨ o + 64 ≤ o') →
        NativeRustcVm.BytesAt st.data.dmem (off (fb m0) o') bs →
        NativeRustcVm.BytesAt d'.dmem (off (fb m0) o') bs) →
      Eventually (step1 Host.exe) (Goal a s0 g0 m0) ⟨d', Host.addrOf (k + j + 2)⟩) :
    Eventually (step1 Host.exe) (Goal a s0 g0 m0) st := by
  have hS := pre_stack h
  have hN := N_ge
  have c32 := ctxF h (1408 - 32) (by omega)
  have hat := atC h (by omega) fr
  have hle := le32 (X := readScalarsStack) (by simp)
  have hn := two_pow_le h
  set n := 2 ^ (reg m0 .rsi).toNat with hndef
  have hX : ∀ q, (NativeRustcVm.InRange (off (fb m0) o) (16 * n) q ∨
      NativeRustcVm.InRange (reg m0 .rdi) tstateBytes q) →
      outs m0 q ∨ NativeRustcVm.InRange (off (fb m0) o) (16 * n) q :=
    fun q hq ↦ hq.elim .inr fun hq ↦ .inl (.inl hq)
  refine Fr.call (c := 32) (Nc := readScalarsStack) (lo := o) (len := 16 * n)
    (X := fun q ↦ NativeRustcVm.InRange (off (fb m0) o) (16 * n) q ∨
      NativeRustcVm.InRange (reg m0 .rdi) tstateBytes q)
    hS hN (by omega) hle (slots_call (by omega) (by omega)) (by omega) (outs_not_frame h) hX
    (hrs s) fr hpc ?_ (fun m' hq ↦ ⟨?_, hq.2.2.2.2⟩) fun m2 fr2 hq2 hs2 hcs2 ↦ ?_
  · unfold ReadScalarsPre
    rw [hdi, hsi, hdx]
    refine ⟨c32.stackOk hat hle, c32.rcAt hat hle, hts, c32.tstateOk hat hle,
      outFb h fr hle (by omega) (by omega), got_atC h (by omega) fr hle ?_⟩
    intro l hl b hb
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · exact ((pre_got h).1 l hl).2.2.2 _ (by simp)
    · exact ((pre_got h).1 l hl).2.2.2 _ (by simp)
    · exact got_apart_frame (pre_got h) h.1 hl N_ge (by omega)
    · exact ((pre_got h).1 l hl).2.2.2 _ (by simp)
  · have := hq.2.2.2.1
    rw [hdi, hsi, hdx] at this
    exact NativeRustcVm.SameOutside.mono this fun q hq ↦ by
      rcases hq with hq | hq | hq
      · exact .inr (.inl hq)
      · exact .inr (.inr hq)
      · exact .inl hq
  obtain ⟨hal, hok, hnext, -, hsv⟩ := hq2
  rw [hdx] at hal hok hnext
  rw [hsi] at hok
  rw [hdi] at hnext
  have hcal : ∀ q, NativeRustcVm.InRange (stackBelow st.data readScalarsStack) readScalarsStack q →
      NativeRustcVm.InRange (stackBelow m0 gkrStepStack) gkrStepStack q :=
    fun q hq ↦ calleeStack h (by omega) fr hle hq
  have hgs2 : GkrStateWAt m2.dmem (reg m0 .rcx) g0 := by
    refine gsKeep h hs2 (fun q hq ↦ ?_) hgs
    rcases hq with hq | hq | hq
    · exact .inl (hcal q hq)
    · exact .inl (fbo_stack h (by omega) hq)
    · exact .inr hq
  -- the test (`b10`)
  have hwf := wf0 h fr2.frame.kept 0
  obtain ⟨hmid, hmem, hk⟩ := ok_b10
  refine exec_then hb exit_b10 (wf0 h fr2.frame.kept 0) nofun (match_head fr2 0)
    fun st3 hm3 hpc3 ↦ ?_
  obtain ⟨fr3, hd3⟩ := FR.block_nil h fr2 hwf hm3 hmid hmem
  have hc : SBool.eval (frameEnv m0 m2 1408 [] (fun _ ↦ 0) 0) cAl =
      !((readScalars n).run s).isSome := testAl_okAl hal
  simp only [PcOk, hc] at hpc3
  cases hr : (readScalars n).run s with
  | none =>
    simp only [hr, Option.isSome_none, Bool.not_false, ↓reduceIte] at hpc3
    exact at_pc (hpc3.trans (hp.label NativeRustcVmX64.Vm.GkrStep.label_17_at)) (fail_spec hp h fr3 (hfail hr))
  | some r =>
    obtain ⟨ys, s'⟩ := r
    simp only [hr, Option.isSome_some, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hpc3
    -- This shared test executes at arbitrary j, not only at b10Offset.
    refine at_pc (hpc3.trans (by rw [NativeRustcVmX64.Vm.GkrStep.b10_length, NativeRustcVmX64.Vm.GkrStep.b10Length])) (cont st3.data ys s' hr fr3
      (fun r hr' ↦ (kr hm3 hk (cs_mem hr')).trans (hcs2 r hr'))
      (by rw [hd3]; exact hok ys s' hr) (by rw [hd3]; exact hnext ys s' hr)
      (by rw [hd3]; exact hgs2) fun {o'} {bs} ho1 ho2 hd hb ↦ ?_)
    rw [hd3]
    refine keepCall h fr hle hs2 ho1 ho2 (fun i hi hq ↦ ?_) hb
    rcases hq with hq | hq
    · exact fbo_apart h (o := o) (n := 16 * n) (o' := o' + i) (n' := 1) (by omega) (by omega)
        (by omega) hq (NativeRustcVm.inRange_self (by omega))
    · exact fb_not_outs h (by omega) (.inl hq)

/-- The `TState` and the `GkrStateW` kept by a block writing the frame only. -/
theorem tsgs_keep (h : GkrStepPre a s0 g0 m0) {d d' : Mem 64} (hk : Kept d d')
    (hs : NativeRustcVm.SameOutside d d' (fun q ↦ NativeRustcVm.InRange (fb m0) 1360 q ∨
      NativeRustcVm.InRange (off (reg m0 .rcx) 0) (0 - 0) q)) {s : TState}
    (hts : TStateAt d (reg m0 .rdi) a s) (hgs : GkrStateWAt d (reg m0 .rcx) g0) :
    TStateAt d' (reg m0 .rdi) a s ∧ GkrStateWAt d' (reg m0 .rcx) g0 := by
  have hR : ∀ q, (NativeRustcVm.InRange (fb m0) 1360 q ∨
      NativeRustcVm.InRange (off (reg m0 .rcx) 0) (0 - 0) q) →
      NativeRustcVm.InRange (stackBelow m0 gkrStepStack) gkrStepStack q := by
    intro q hq
    rcases hq with hq | hq
    · exact fb_stack h (inRange_mono hq (by omega))
    · exact absurd hq (by unfold NativeRustcVm.InRange; omega)
  exact ⟨tsKeep h hk hs (fun q hq ↦ .inl (hR q hq)) hts,
    gsKeep h hs (fun q hq ↦ .inl (hR q hq)) hgs⟩

/-- Frame bytes a block writing `[32, 40)` (and maybe more) kept. -/
theorem keep3240 {d d' : MachineData} {S : SState} {ret : BitVec 64}
    (hwf : (frameEnv m0 d 1408 [] (fun _ ↦ 0) ret).WF)
    (hm : Match (frameEnv m0 d 1408 [] (fun _ ↦ 0) ret) S d')
    (hmid : MidOk 1408 32 slots S = true) {ivs : List (Nat × Nat)} (hw : W0 S ivs = true)
    {o : Nat} {bs : List UInt8} (hle : o + bs.length ≤ 1408)
    (hd : ∀ p ∈ ivs, o + bs.length ≤ p.1 ∨ p.2 ≤ o)
    (hb : NativeRustcVm.BytesAt d.dmem (off (fb m0) o) bs) :
    NativeRustcVm.BytesAt d'.dmem (off (fb m0) o) bs :=
  keepB hwf hm (.inr (.inl hmid)) hle (fun w hw' _ ↦ by
    obtain ⟨-, q, hq, h1, h2⟩ := W0_spec hw w hw'
    rcases hd q hq with h3 | h3 <;> omega) hb

/-- **The children** (`b9` to `b14`), from `AtCh`. -/
theorem ch_spec (hp : Placed code k) (h : GkrStepPre a s0 g0 m0)
    (hrs : ∀ s, Spec (Labels.label NativeRustcVmX64.Vm.TStateReadScalars.entryLabel) (ReadScalarsPre a s) (ReadScalarsPost a s))
    (hpr : ∀ c cl xs h0 h1 h2 s3 d, AtPr a s0 g0 m0 c cl xs h0 h1 h2 s3 d →
      Eventually (step1 Host.exe) (Goal a s0 g0 m0) ⟨d, Host.addrOf (k + NativeRustcVmX64.Vm.GkrStep.b15Offset)⟩)
    {c cl : EW} {xs : Array EW} {s2 : TState} {d : MachineData}
    (at9 : AtCh a s0 g0 m0 c cl xs s2 d) :
    Eventually (step1 Host.exe) (Goal a s0 g0 m0) ⟨d, Host.addrOf (k + NativeRustcVmX64.Vm.GkrStep.b9Offset)⟩ := by
  set n := 2 ^ (reg m0 .rsi).toNat with hndef
  have hn := two_pow_le h
  have hn1 : 1 ≤ n := Nat.one_le_two_pow
  -- `b9`
  have hwf1 := wf0 h at9.fr.frame.kept (Host.addrOf (k + NativeRustcVmX64.Vm.GkrStep.b9Offset + b9.length)).toBitVec
  obtain ⟨hmid1, hw1, hw88, hw80, hsi1, hdi1, hdx1, hk1⟩ := ok_b9
  refine exec_then (infix_of b9_in_code (by simp [b9]) hp) exit_b9 hwf1 (fun _ _ ↦ rfl)
    (match_head at9.fr _) fun st1 hm1 hpc1 ↦ ?_
  obtain ⟨fr1, hs1⟩ := FR.block h at9.fr hwf1 hm1 hmid1 (.inl rfl) (W01_of_W0 hw1) (by decide)
    (by omega)
  obtain ⟨ts1, gs1⟩ := tsgs_keep h (hm1.kept hwf1) hs1 at9.ts at9.gs
  have kp1 : ∀ {o : Nat} {bs : List UInt8}, o + bs.length ≤ 1408 →
      (o + bs.length ≤ 32 ∨ (40 ≤ o ∧ o + bs.length ≤ 80) ∨ (96 ≤ o ∧ o + bs.length ≤ 112) ∨
        304 ≤ o) →
      NativeRustcVm.BytesAt d.dmem (off (fb m0) o) bs →
      NativeRustcVm.BytesAt st1.data.dmem (off (fb m0) o) bs := fun hle hd hb ↦
    keep3240 hwf1 hm1 hmid1 hw1 hle (fun p hp ↦ by
      simp at hp; rcases hp with rfl | rfl | rfl <;> simp <;> omega) hb
  obtain ⟨clw0, clw1⟩ := NativeRustcVm.Transcript.ewAt_iff.mp at9.clw
  rw [off_off] at clw1
  have cl88 : NativeRustcVm.WordAt st1.data.dmem (off (fb m0) 88) cl.c0 := by
    have := wordAt_write hm1 (r := 0) (o := 88) (b := stackBelow m0 1408) (sz := 1408 + 8) rfl
      (by omega) hw88
    rwa [show (Sym.load 0 120 8).eval (frameEnv m0 d 1408 [] (fun _ ↦ 0)
      (Host.addrOf (k + NativeRustcVmX64.Vm.GkrStep.b9Offset + b9.length)).toBitVec) = cl.c0.toBitVec from
      load_ofMachine (rs := [(stackBelow m0 1408, 1408 + 8)]) (r := 0) (o := 120) rfl clw0,
      UInt64.ofBitVec_toBitVec] at this
  have cl80 : NativeRustcVm.WordAt st1.data.dmem (off (fb m0) 80) cl.c1 := by
    have := wordAt_write hm1 (r := 0) (o := 80) (b := stackBelow m0 1408) (sz := 1408 + 8) rfl
      (by omega) hw80
    rwa [show (Sym.load 0 128 8).eval (frameEnv m0 d 1408 [] (fun _ ↦ 0)
      (Host.addrOf (k + NativeRustcVmX64.Vm.GkrStep.b9Offset + b9.length)).toBitVec) = cl.c1.toBitVec from
      load_ofMachine (rs := [(stackBelow m0 1408, 1408 + 8)]) (r := 0) (o := 128) rfl clw1,
      UInt64.ofBitVec_toBitVec] at this
  have k1 : ∀ r ∈ cs6, reg st1.data r = reg d r := fun r hr ↦ kr hm1 hk1 hr
  simp only [PcOk] at hpc1
  have hret1 : retOf st1.data = Host.addrOf (k + NativeRustcVmX64.Vm.GkrStep.b10Offset) := by
    rw [hpc1.2, Nat.add_assoc]; exact congrArg (fun j ↦ Host.addrOf (k + j)) NativeRustcVmX64.Vm.GkrStep.b9_next
  -- round 0
  refine rs_round hp h hrs (j := NativeRustcVmX64.Vm.GkrStep.b10Offset) (infix_of b10_in_code (by simp [b10]) hp) fr1
    ⟨hpc1.1, hret1⟩ (o := 112) (by omega) (by omega)
    ((rv hm1 hsi1).trans (eval_ptr0 112)) ((rv hm1 hdi1).trans at9.r15)
    (by rw [rv hm1 hdx1]; exact at9.r12) ts1 gs1
    (fun hr ↦ by rw [at9.run, gkrChildren, hr]; rfl)
    fun d2 y0 s3 hr0 fr2 hcs2 hy0 ts2 gs2 kp2 ↦ ?_
  have k2 : ∀ r ∈ cs6, reg d2 r = reg d r := fun r hr ↦
    (hcs2 r (by simp [cs6] at hr; rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> rfl)).trans
      (k1 r hr)
  -- `b11`
  have hwf3 := wf0 h fr2.frame.kept (Host.addrOf (k + NativeRustcVmX64.Vm.GkrStep.b11Offset + b11.length)).toBitVec
  obtain ⟨hmid3, hw3, hsi3, hdi3, hdx3, hk3⟩ := ok_b11
  refine exec_at (st := ⟨d2, _⟩) (infix_of b11_in_code (by simp [b11]) hp) exit_b11 hwf3
    (fun _ _ ↦ rfl) rfl (match_head fr2 _) fun st3 hm3 hpc3 ↦ ?_
  obtain ⟨fr3, hs3⟩ := FR.block h fr2 hwf3 hm3 hmid3 (.inl rfl) (W01_of_W0 hw3) (by decide)
    (by omega)
  obtain ⟨ts3, gs3⟩ := tsgs_keep h (hm3.kept hwf3) hs3 ts2 gs2
  have kp3 : ∀ {o : Nat} {bs : List UInt8}, o + bs.length ≤ 1408 → (o + bs.length ≤ 32 ∨ 40 ≤ o) →
      NativeRustcVm.BytesAt d2.dmem (off (fb m0) o) bs →
      NativeRustcVm.BytesAt st3.data.dmem (off (fb m0) o) bs := fun hle hd hb ↦
    keep3240 hwf3 hm3 hmid3 hw3 hle (fun p hp ↦ by simp at hp; subst hp; simp; omega) hb
  simp only [PcOk] at hpc3
  have hret3 : retOf st3.data = Host.addrOf (k + NativeRustcVmX64.Vm.GkrStep.b12Offset) := by
    rw [hpc3.2, Nat.add_assoc]; exact congrArg (fun j ↦ Host.addrOf (k + j)) NativeRustcVmX64.Vm.GkrStep.b11_next
  have h12 : (reg d .r12).toNat = n := at9.r12
  have hb12 : b12.IsInfixAt Host.prog (k + NativeRustcVmX64.Vm.GkrStep.b12Offset) := infix_of b12_in_code (by simp [b12]) hp
  refine rs_round hp h hrs (j := NativeRustcVmX64.Vm.GkrStep.b12Offset) (b12_eq ▸ hb12)
    fr3 ⟨hpc3.1, hret3⟩ (o := 176) (by omega) (by omega)
    ((rv hm3 hsi3).trans (eval_ptr0 176)) ((rv hm3 hdi3).trans ((k2 .r15 (by simp)).trans at9.r15))
    (by rw [rv hm3 hdx3]; show (reg d2 .r12).toNat = _; rw [k2 .r12 (by simp)]; exact h12) ts3 gs3
    (fun hr ↦ by rw [at9.run, gkrChildren, hr0]; simp only [Option.bind_some]; rw [hr]; rfl)
    fun d4 y1 s4 hr1 fr4 hcs4 hy1 ts4 gs4 kp4 ↦ ?_
  have k4 : ∀ r ∈ cs6, reg d4 r = reg d r := fun r hr ↦
    (hcs4 r (by simp [cs6] at hr; rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> rfl)).trans
      ((kr hm3 hk3 hr).trans (k2 r hr))
  -- `b13`
  have hwf5 := wf0 h fr4.frame.kept (Host.addrOf (k + NativeRustcVmX64.Vm.GkrStep.b13Offset + b13.length)).toBitVec
  obtain ⟨hmid5, hw5, hsi5, hdi5, hdx5, hk5⟩ := ok_b13
  refine exec_at (st := ⟨d4, _⟩) (infix_of b13_in_code (by simp [b13]) hp) exit_b13 hwf5
    (fun _ _ ↦ rfl) rfl (match_head fr4 _) fun st5 hm5 hpc5 ↦ ?_
  obtain ⟨fr5, hs5⟩ := FR.block h fr4 hwf5 hm5 hmid5 (.inl rfl) (W01_of_W0 hw5) (by decide)
    (by omega)
  obtain ⟨ts5, gs5⟩ := tsgs_keep h (hm5.kept hwf5) hs5 ts4 gs4
  have kp5 : ∀ {o : Nat} {bs : List UInt8}, o + bs.length ≤ 1408 → (o + bs.length ≤ 32 ∨ 40 ≤ o) →
      NativeRustcVm.BytesAt d4.dmem (off (fb m0) o) bs →
      NativeRustcVm.BytesAt st5.data.dmem (off (fb m0) o) bs := fun hle hd hb ↦
    keep3240 hwf5 hm5 hmid5 hw5 hle (fun p hp ↦ by simp at hp; subst hp; simp; omega) hb
  simp only [PcOk] at hpc5
  have hret5 : retOf st5.data = Host.addrOf (k + NativeRustcVmX64.Vm.GkrStep.b14Offset) := by
    rw [hpc5.2, Nat.add_assoc]; exact congrArg (fun j ↦ Host.addrOf (k + j)) NativeRustcVmX64.Vm.GkrStep.b13_next
  have hb14 : b14.IsInfixAt Host.prog (k + NativeRustcVmX64.Vm.GkrStep.b14Offset) := infix_of b14_in_code (by simp [b14]) hp
  refine rs_round hp h hrs (j := NativeRustcVmX64.Vm.GkrStep.b14Offset) (b14_eq ▸ hb14)
    fr5 ⟨hpc5.1, hret5⟩ (o := 240) (by omega) (by omega)
    ((rv hm5 hsi5).trans (eval_ptr0 240)) ((rv hm5 hdi5).trans ((k4 .r15 (by simp)).trans at9.r15))
    (by rw [rv hm5 hdx5]; show (reg d4 .r12).toNat = _; rw [k4 .r12 (by simp)]; exact h12) ts5 gs5
    (fun hr ↦ by
      rw [at9.run, gkrChildren, hr0]; simp only [Option.bind_some]; rw [hr1]
      simp only [Option.bind_some]; rw [hr]; rfl)
    fun d6 y2 s5 hr2 fr6 hcs6 hy2 ts6 gs6 kp6 ↦ ?_
  have k6 : ∀ r ∈ cs6, reg d6 r = reg d r := fun r hr ↦
    (hcs6 r (by simp [cs6] at hr; rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> rfl)).trans
      ((kr hm5 hk5 hr).trans (k4 r hr))
  have hz0 := readScalars_size hr0
  have hz1 := readScalars_size hr1
  have hz2 := readScalars_size hr2
  have L0 : 16 * y0.toList.length ≤ 64 := by rw [Array.length_toList, hz0]; omega
  have L1 : 16 * y1.toList.length ≤ 64 := by rw [Array.length_toList, hz1]; omega
  have L2 : 16 * y2.toList.length ≤ 64 := by rw [Array.length_toList, hz2]; omega
  -- a byte range through the three rounds
  have thru : ∀ {o : Nat} {bs : List UInt8}, o + bs.length ≤ 1408 →
      ((40 ≤ o ∧ o + bs.length ≤ 80) ∨ (96 ≤ o ∧ o + bs.length ≤ 112) ∨ 304 ≤ o) →
      NativeRustcVm.BytesAt d.dmem (off (fb m0) o) bs →
      NativeRustcVm.BytesAt d6.dmem (off (fb m0) o) bs := by
    intro o bs hle hd hb
    have hd' : o + bs.length ≤ 112 ∨ 304 ≤ o := by omega
    exact kp6 (by omega) hle (by omega) (kp5 hle (by omega) (kp4 (by omega) hle (by omega)
      (kp3 hle (by omega) (kp2 (by omega) hle (by omega) (kp1 hle (by omega) hb)))))
  have thru80 : ∀ {o : Nat} {bs : List UInt8}, o + bs.length ≤ 112 → 80 ≤ o →
      NativeRustcVm.BytesAt st1.data.dmem (off (fb m0) o) bs →
      NativeRustcVm.BytesAt d6.dmem (off (fb m0) o) bs := fun hle ho hb ↦
    kp6 (by omega) (by omega) (by omega) (kp5 (by omega) (by omega) (kp4 (by omega) (by omega)
      (by omega) (kp3 (by omega) (by omega) (kp2 (by omega) (by omega) (by omega) hb))))
  have hxl : xs.toList.length ≤ 63 := by
    rw [Array.length_toList]; have := at9.size; unfold busPointCap at this; omega
  have l4 : ((List.range 4).map (byteOf (reg m0 .rdx))).length = 4 := by simp
  have l8 : ∀ w : UInt64, (NativeRustcVm.wordBytes w).length = 8 := NativeRustcVm.length_wordBytes
  refine hpr c cl xs y0 y1 y2 s5 d6 ⟨fr6, ?_, ?_, ?_, ?_, ?_, ?_,
    thru (by rw [l4]; omega) (by rw [l4]; omega) at9.l44,
    thru (by rw [l8]; omega) (by rw [l8]; omega) at9.c104,
    thru80 (by rw [l8]; omega) (by omega) cl88,
    thru80 (by rw [l8]; omega) (by omega) cl80,
    kp6 (by omega) (by rw [l8]; omega) (by rw [l8]; omega) (kp5 (by rw [l8]; omega) (by rw [l8]; omega)
      (kp4 (by omega) (by rw [l8]; omega) (by rw [l8]; omega) (kp3 (by rw [l8]; omega) (by rw [l8]; omega)
        (kp2 (by omega) (by rw [l8]; omega) (by rw [l8]; omega)
          (kp1 (by rw [l8]; omega) (by rw [l8]; omega) at9.pa))))),
    thru (by rw [NativeRustcVm.length_ewsBytes]; omega)
      (by omega) at9.hxs, at9.size,
    kp6 (by omega) (by rw [NativeRustcVm.length_ewsBytes]; omega)
      (by rw [NativeRustcVm.length_ewsBytes]; omega) (kp5 (by rw [NativeRustcVm.length_ewsBytes]; omega)
      (by omega) (kp4 (by omega) (by rw [NativeRustcVm.length_ewsBytes]; omega)
        (by rw [NativeRustcVm.length_ewsBytes]; omega) (kp3 (by rw [NativeRustcVm.length_ewsBytes]; omega)
          (by omega) hy0))),
    kp6 (by omega) (by rw [NativeRustcVm.length_ewsBytes]; omega)
      (by rw [NativeRustcVm.length_ewsBytes]; omega) (kp5 (by rw [NativeRustcVm.length_ewsBytes]; omega)
      (by omega) hy1),
    hy2, hz0, hz1, hz2, ts6, gs6, ?_⟩
  · exact (k6 .rbx (by simp)).trans at9.rbx
  · rw [k6 .r12 (by simp)]; exact at9.r12
  · rw [k6 .r13 (by simp)]; exact at9.r13
  · exact (k6 .r14 (by simp)).trans at9.r14
  · exact (k6 .r15 (by simp)).trans at9.r15
  · exact (k6 .rbp (by simp)).trans at9.rbp
  · rw [at9.run, gkrChildren, hr0]; simp only [Option.bind_some]; rw [hr1]
    simp only [Option.bind_some]; rw [hr2]; rfl

end

end NativeRustcVmX64.Bus.GkrStep
