module

public import NativeRustcVmX64.KeccakGkr.VerifyKeccak.Copy
public import NativeRustcVmX64.KeccakGkr.VerifyKeccak.First
public import NativeRustcVmX64.Code.Vm.Memcpy.Names

/-!
# `verify_keccak`: the copies before the layers (x86-64)

`b9` to `b14`: the first claim (at frame offset `1000`) through the frame's `2536` (value, `mu`)
and `2816` (the point's elements) to the running claim at `992` and the first claim's copy at
`1768`, the point's size at `120`; `b15`: the first bit weights to the scratch's `weights`. At
`b16` (`t16`): `copiesStep`.
-/

namespace NativeRustcVmX64.KeccakGkr.VerifyKeccak

open NativeRustcX64 NativeRustcX64.Sym NativeRustcVmX64.Ring NativeRustcVmX64.KeccakGkr.SeqZ
open NativeRustcVmX64.Vm.VerifyKeccak NativeVm.Model
open NativeRustcVm.Transcript (DecArea TStateAt)
open NativeRustcVm.KeccakGkr (off ClaimAt WeightsAt)

@[expose] public section

/-- The values from the claim's copies on: the committed value, the first point's size `n`. -/
def V2 (cm : EW) (n : Nat) : Vs :=
  { c0 := cm.c0.toBitVec, c1 := cm.c1.toBitVec, fl := BitVec.ofNat 64 n }

end

public section

theorem addW (x y : BitVec 64) : BinOp.apply .add .W64 x y = x + y := by
  simp only [BinOp.apply, low_W64, ext_W64]

theorem koff_off (b : BitVec 64) (o i : Nat) : off (off b o) i = off b (o + i) :=
  NativeRustcVm.addr_add_add b o i

section
variable [Labels] {m0 : MachineData} {a : DecArea} {inst : Array EW}

/-- **Frame bytes a change misses**, as an image. -/
theorem imgF (c : Ctx a inst m0) {d d' : DataMem} {L : List (Nat × Nat)}
    {O : List (Nat × Nat × Nat)} (h : Chg m0 d d' L O) (hL : okL L = true) (hO : okO O = true)
    {o n : Nat} (hm : missL L o n = true) (hon : o + n ≤ 3368) :
    Img d (off (fb m0) o) d' (off (fb m0) o) n :=
  Img.of_same (Chg.frame c h hL hO hm hon)

/-- **Region bytes a change misses**, as an image. -/
theorem imgR (c : Ctx a inst m0) {d d' : DataMem} {L : List (Nat × Nat)}
    {O : List (Nat × Nat × Nat)} (h : Chg m0 d d' L O) (hL : okL L = true) (hO : okO O = true)
    {i o n : Nat} (h1 : 1 ≤ i) (h4 : i ≤ 4) (hm : missO O i o n = true) (hon : o + n ≤ rsz i) :
    Img d (off (ob m0 i) o) d' (off (ob m0 i) o) n :=
  Img.of_same (Chg.regS c h hL hO h1 h4 hm hon)

end

/-- **A claim from its parts**: the value and `mu` (`280` bytes), the point's size, the point's
elements (`480` bytes from `288`). -/
theorem claim_img {d d' : Mem 64} {p q : BitVec 64} {x : KeccakClaimW} (h : ClaimAt d p x)
    (hA : Img d p d' q 280) (hW : NativeRustcVm.WordAt d' (off q 280) x.point.toList.length.toUInt64)
    (hC : Img d (off p 288) d' (off q 288) 480) : ClaimAt d' q x := by
  obtain ⟨hv, hmu, hl, -, hpe⟩ := h
  refine ⟨hA.bytesAt0 hv (by rw [NativeRustcVm.length_ewBytes]; omega), hA.bufEWAt hmu (by decide),
    hl, hW, ?_⟩
  have hl' : x.point.toList.length ≤ 30 := hl
  have e : ∀ b : BitVec 64, off b NativeRustcVm.KeccakGkr.pointOff + 8#64 = off b 288 :=
    fun b ↦ NativeRustcVm.Transcript.off_add b 280 8
  rw [e] at hpe ⊢
  exact hC.ewsAt hpe (by omega)

variable [Host] {k : Nat} {m0 : MachineData} {a : DecArea} {s : TState}
  {cs : Array ColumnClaimW} {inst output : Array EW}

/-- **The copies** (`b9` to `b15`): at `b16` (`t16`), the first claim at `992` and `1768`, its
bit weights at the scratch's start and its `weights`. -/
theorem copiesStep (hp : Placed code k) (hpre : VerifyKeccakPre a s cs inst output m0)
    (hmemcpy : Spec (Labels.label NativeRustcVmX64.Vm.Memcpy.entryLabel) MemcpyPre MemcpyPost)
    {st : MachineState} {s4 : TState} {first : KeccakClaimW} {cm : EW}
    (hat : At m0 k NativeRustcVmX64.Vm.VerifyKeccak.b9Offset wrA t9 (vv m0 (V1 cm)) st)
    (hts : TStateAt st.data.dmem (reg m0 .rdi) a s4)
    (hcl : ClaimAt st.data.dmem (off (fb m0) 1000) first)
    (hw : WeightsAt st.data.dmem (off (reg m0 .r9) 0) first) {R : MachineState → Prop}
    (cont : ∀ st', At m0 k NativeRustcVmX64.Vm.VerifyKeccak.b16Offset wrA t16 (vv m0 (V2 cm first.point.size)) st' →
      TStateAt st'.data.dmem (reg m0 .rdi) a s4 →
      ClaimAt st'.data.dmem (off (fb m0) 992) first →
      ClaimAt st'.data.dmem (off (fb m0) 1768) first →
      WeightsAt st'.data.dmem (off (reg m0 .r9) 0) first →
      WeightsAt st'.data.dmem (off (reg m0 .r9) 25600) first →
      Eventually (step1 Host.exe) R st') :
    Eventually (step1 Host.exe) R st := by
  have c := ctx_of hpre
  have h := lay_of hpre
  have hw1280 : NativeRustcVm.WordAt st.data.dmem (off (fb m0) 1280)
      first.point.toList.length.toUInt64 := by
    have := hcl.2.2.2.1
    rwa [koff_off] at this
  have hg := c.got.1 "memcpy" (by simp)
  have hspan : Apart (gotAddr "memcpy") 8 (stackBelow m0 verifyKeccakStack)
      (verifyKeccakStack - 3344 + 3368) := by
    have hs : Apart (gotAddr "memcpy") 8 (stackBelow m0 verifyKeccakStack)
        (verifyKeccakStack + 8) := hg.2.2.1
    have ha := hg.2.2.2 (rspOf m0 + 8#64, 16) (by simp)
    have hK := c.K
    have har := c.ar
    have hN := c.sp
    unfold Apart at hs ha ⊢
    dsimp only [Prod.fst, Prod.snd] at ha
    rw [vk_eq] at *
    omega
  have hG := h.withGot (c.got.areas (areas' := rsOf m0) (by
    intro p hp
    simp only [rsOf, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl <;> simp)) hspan
  have hmG : ∀ ret, Match
      (envZ m0 st.data 3344 3368 (rsOf m0 ++ [(gotAddr "memcpy", 8)]) (vv m0 (V1 cm)) ret)
      t9G st.data := by
    intro ret
    apply Match.withKnownBytes
    · apply match_links
        (env' := envZ m0 st.data 3344 3368 (rsOf m0 ++ [(gotAddr "memcpy", 8)])
          (vv m0 (V1 cm)) ret) (T' := t9R) (hknown := rfl)
        (hat.2.mt ret) (by decide) rfl rfl
        (fun _ ↦ rfl) rfl rfl rfl (by vtacJ) rfl (regions_envZ rfl) rfl
        (fun _ _ hx ↦ by cases hx)
      intro x r o hx
      by_cases he : x = .gotSlot "memcpy"
      · subst x
        simp only [t9R, List.lookup, beq_self_eq_true,
          Option.some.injEq, Prod.mk.injEq] at hx
        obtain ⟨rfl, rfl⟩ := hx
        simp [Sym.eval, Env.base, rsOf, gotAddr]
      · have he' : (x == .gotSlot "memcpy") = false := by
          apply Bool.eq_false_iff.mpr
          intro hx
          exact he (eq_of_beq hx)
        simp [t9R, List.lookup, he'] at hx
    · intro i hi
      simp only [Nat.zero_add, Sym.eval, Env.base_ofMachine_eq, Env.ofMachine_mem0]
      change st.data.dmem.get? (gotAddr "memcpy" + BitVec.ofNat 64 i) = _
      rw [same_ro c hat.2.same hg.2.1 hg.2.2.1
        (fun _ ↦ hg.2.2.2 (reg m0 .rdi, 760) (by simp))
        (fun _ ↦ hg.2.2.2 (reg m0 .r9, 205824) (by simp))
        (fun _ ↦ hg.2.2.2 (keccakClaims m0, 97288) (by simp))
        (fun _ ↦ hg.2.2.2 (keccakOutArg m0, 1608) (by simp)) i hi]
      exact c.got.byte (by simp) hi
  -- `b9`: the value and `mu` to `2536`.
  refine cpStep (T' := t10) (vals' := vv m0 (V1 cm)) (hm := hmG)
    (hwfS := fun ret ↦ hG.wf hat.2.kept) hp hpre hmemcpy hat b9_in_code
    (by simp [b9]) run_b9 (by decide) rfl (D := off (fb m0) 2536) (Sr := off (fb m0) 1000)
    (n := 280) (fun mc hmc ↦ (hmc.regs .rdi _ rfl).trans (ev_frame 2536))
    (fun mc hmc ↦ (hmc.regs .rsi _ rfl).trans (ev_frame 1000)) rfl (by decide)
    (fun mc ca ↦ ⟨mapF h ca (by nd), nwF c (by nd), apF c ca (by nd) (by nd) (by nd)⟩)
    (fun mc ca ↦ ⟨mapF h ca (by nd), nwF c (by nd)⟩)
    (sepFF c (by nd) (by nd) (by nd) (by nd) (by nd)) (Lc := [(2536, 280)]) (Oc := [])
    (fun q hq ↦ chgR_frame List.mem_cons_self hq) (by decide) (by decide) (by decide)
    (by decide) (by decide) rfl rfl rfl (by vtacC) rfl rfl rfl rfl rfl rfl rfl
    fun st10 mc9 hat10 _ hi9 hb9 _ hc9 hk9 ↦ ?_
  rw [NativeRustcVmX64.Vm.VerifyKeccak.b9_next] at hat10
  have A10 : Img st.data.dmem (off (fb m0) 1000) st10.data.dmem (off (fb m0) 2536) 280 :=
    (imgF c hb9 (by decide) (by decide) (by decide) (by decide)).trans hi9
  have C10 : Img st.data.dmem (off (fb m0) 1288) st10.data.dmem (off (fb m0) 1288) 480 :=
    imgF c hc9 (by decide) (by decide) (by decide) (by decide)
  have w10 := Chg.wordF c hc9 (by decide) (by decide) (by decide) (by decide) hw1280
  have hl10 : ∀ ret, (envZ m0 st10.data 3344 3368 (rsOf m0) (vv m0 (V1 cm)) ret).load 0 1280 8 =
      first.point.toList.length.toUInt64.toBitVec := fun _ ↦ ld_frame w10
  -- `b10`: the point's elements to `2816`, its size into RBP.
  refine cpStep (hm := hat10.2.mt) (hwfS := fun _ ↦ h.wf hat10.2.kept)
    (T' := t11) (vals' := vv m0 (V2 cm first.point.size)) hp hpre hmemcpy hat10
    b10_in_code (by simp [b10]) run_b10 (by decide) rfl (D := off (fb m0) 2816)
    (Sr := off (fb m0) 1288) (n := 480)
    (fun mc hmc ↦ (hmc.regs .rdi _ rfl).trans (ev_frame 2816))
    (fun mc hmc ↦ (hmc.regs .rsi _ rfl).trans (ev_frame 1288)) rfl (by decide)
    (fun mc ca ↦ ⟨mapF h ca (by nd), nwF c (by nd), apF c ca (by nd) (by nd) (by nd)⟩)
    (fun mc ca ↦ ⟨mapF h ca (by nd), nwF c (by nd)⟩)
    (sepFF c (by nd) (by nd) (by nd) (by nd) (by nd)) (Lc := [(2816, 480)]) (Oc := [])
    (fun q hq ↦ chgR_frame List.mem_cons_self hq) (by decide) (by decide) (by decide)
    (by decide) (by decide) rfl rfl rfl ?_ rfl rfl rfl rfl rfl rfl rfl
    fun st11 mc10 hat11 _ hi10 hb10 _ hc10 hk10 ↦ ?_
  · intro ret
    simp only [List.cons_append, List.nil_append, List.forall_mem_cons, Sym.eval, hl10]
    and_intros <;> first | rfl | exact fun _ h ↦ nomatch h
  rw [NativeRustcVmX64.Vm.VerifyKeccak.b10_next] at hat11
  have A11 : Img st.data.dmem (off (fb m0) 1000) st11.data.dmem (off (fb m0) 2536) 280 :=
    A10.trans (imgF c hc10 (by decide) (by decide) (by decide) (by decide))
  have C11 : Img st.data.dmem (off (fb m0) 1288) st11.data.dmem (off (fb m0) 2816) 480 :=
    C10.trans ((imgF c hb10 (by decide) (by decide) (by decide) (by decide)).trans hi10)
  -- `b11`: the value and `mu` to `1768`.
  refine cpStep (hm := hat11.2.mt) (hwfS := fun _ ↦ h.wf hat11.2.kept)
    (T' := t11) (vals' := vv m0 (V2 cm first.point.size)) hp hpre hmemcpy hat11
    b11_in_code (by simp [b11]) run_b11 (by decide) rfl (D := off (fb m0) 1768)
    (Sr := off (fb m0) 2536) (n := 280)
    (fun mc hmc ↦ (hmc.regs .rdi _ rfl).trans (ev_frame 1768))
    (fun mc hmc ↦ (hmc.regs .rsi _ rfl).trans (ev_frame 2536)) rfl (by decide)
    (fun mc ca ↦ ⟨mapF h ca (by nd), nwF c (by nd), apF c ca (by nd) (by nd) (by nd)⟩)
    (fun mc ca ↦ ⟨mapF h ca (by nd), nwF c (by nd)⟩)
    (sepFF c (by nd) (by nd) (by nd) (by nd) (by nd)) (Lc := [(1768, 280)]) (Oc := [])
    (fun q hq ↦ chgR_frame List.mem_cons_self hq) (by decide) (by decide) (by decide)
    (by decide) (by decide) rfl rfl rfl (by vtacC) rfl rfl rfl rfl rfl rfl rfl
    fun st12 mc11 hat12 _ hi11 hb11 _ hc11 hk11 ↦ ?_
  rw [NativeRustcVmX64.Vm.VerifyKeccak.b11_next] at hat12
  have A12 : Img st.data.dmem (off (fb m0) 1000) st12.data.dmem (off (fb m0) 1768) 280 :=
    A11.trans ((imgF c hb11 (by decide) (by decide) (by decide) (by decide)).trans hi11)
  have B12 : Img st.data.dmem (off (fb m0) 1000) st12.data.dmem (off (fb m0) 2536) 280 :=
    A11.trans (imgF c hc11 (by decide) (by decide) (by decide) (by decide))
  have C12 : Img st.data.dmem (off (fb m0) 1288) st12.data.dmem (off (fb m0) 2816) 480 :=
    C11.trans (imgF c hc11 (by decide) (by decide) (by decide) (by decide))
  -- `b12`: the point's size at `2048`, its elements to `2056`.
  refine cpStep (hm := hat12.2.mt) (hwfS := fun _ ↦ h.wf hat12.2.kept)
    (T' := t11) (vals' := vv m0 (V2 cm first.point.size)) hp hpre hmemcpy hat12
    b12_in_code (by simp [b12]) run_b12 (by decide) rfl (D := off (fb m0) 2056)
    (Sr := off (fb m0) 2816) (n := 480)
    (fun mc hmc ↦ (hmc.regs .rdi _ rfl).trans (ev_frame 2056))
    (fun mc hmc ↦ (hmc.regs .rsi _ rfl).trans (ev_frame 2816)) rfl (by decide)
    (fun mc ca ↦ ⟨mapF h ca (by nd), nwF c (by nd), apF c ca (by nd) (by nd) (by nd)⟩)
    (fun mc ca ↦ ⟨mapF h ca (by nd), nwF c (by nd)⟩)
    (sepFF c (by nd) (by nd) (by nd) (by nd) (by nd)) (Lc := [(2056, 480)]) (Oc := [])
    (fun q hq ↦ chgR_frame List.mem_cons_self hq) (by decide) (by decide) (by decide)
    (by decide) (by decide) rfl rfl rfl (by vtacC) rfl rfl rfl rfl rfl rfl rfl
    fun st13 mc12 hat13 hm12 hi12 hb12 hl12 hc12 hk12 ↦ ?_
  rw [NativeRustcVmX64.Vm.VerifyKeccak.b12_next] at hat13
  have W13 : NativeRustcVm.WordAt st13.data.dmem (off (fb m0) 2048)
      first.point.toList.length.toUInt64 :=
    Chg.wordF c hl12 (by decide) (by decide) (by decide) (by decide)
      (NativeRustcVmX64.Transcript.wordAt_write hm12 (r := 0) (o := 2048) (b := fb m0)
        (sz := 3368) rfl (by decide) (v := .var 18) (by decide))
  have A13 : Img st.data.dmem (off (fb m0) 1000) st13.data.dmem (off (fb m0) 1768) 280 :=
    A12.trans (imgF c hc12 (by decide) (by decide) (by decide) (by decide))
  have B13 : Img st.data.dmem (off (fb m0) 1000) st13.data.dmem (off (fb m0) 2536) 280 :=
    B12.trans (imgF c hc12 (by decide) (by decide) (by decide) (by decide))
  have C13 : Img st.data.dmem (off (fb m0) 1288) st13.data.dmem (off (fb m0) 2056) 480 :=
    C12.trans ((imgF c hb12 (by decide) (by decide) (by decide) (by decide)).trans hi12)
  have D13 : Img st.data.dmem (off (fb m0) 1288) st13.data.dmem (off (fb m0) 2816) 480 :=
    C12.trans (imgF c hc12 (by decide) (by decide) (by decide) (by decide))
  -- `b13`: the value and `mu` to `992`.
  refine cpStep (hm := hat13.2.mt) (hwfS := fun _ ↦ h.wf hat13.2.kept)
    (T' := t11) (vals' := vv m0 (V2 cm first.point.size)) hp hpre hmemcpy hat13
    b13_in_code (by simp [b13]) run_b13 (by decide) rfl (D := off (fb m0) 992)
    (Sr := off (fb m0) 2536) (n := 280)
    (fun mc hmc ↦ (hmc.regs .rdi _ rfl).trans (ev_frame 992))
    (fun mc hmc ↦ (hmc.regs .rsi _ rfl).trans (ev_frame 2536)) rfl (by decide)
    (fun mc ca ↦ ⟨mapF h ca (by nd), nwF c (by nd), apF c ca (by nd) (by nd) (by nd)⟩)
    (fun mc ca ↦ ⟨mapF h ca (by nd), nwF c (by nd)⟩)
    (sepFF c (by nd) (by nd) (by nd) (by nd) (by nd)) (Lc := [(992, 280)]) (Oc := [])
    (fun q hq ↦ chgR_frame List.mem_cons_self hq) (by decide) (by decide) (by decide)
    (by decide) (by decide) rfl rfl rfl (by vtacC) rfl rfl rfl rfl rfl rfl rfl
    fun st14 mc13 hat14 _ hi13 hb13 _ hc13 hk13 ↦ ?_
  rw [NativeRustcVmX64.Vm.VerifyKeccak.b13_next] at hat14
  have A14 : Img st.data.dmem (off (fb m0) 1000) st14.data.dmem (off (fb m0) 1768) 280 :=
    A13.trans (imgF c hc13 (by decide) (by decide) (by decide) (by decide))
  have E14 : Img st.data.dmem (off (fb m0) 1000) st14.data.dmem (off (fb m0) 992) 280 :=
    B13.trans ((imgF c hb13 (by decide) (by decide) (by decide) (by decide)).trans hi13)
  have W14 := Chg.wordF c hc13 (by decide) (by decide) (by decide) (by decide) W13
  have C14 : Img st.data.dmem (off (fb m0) 1288) st14.data.dmem (off (fb m0) 2056) 480 :=
    C13.trans (imgF c hc13 (by decide) (by decide) (by decide) (by decide))
  have D14 : Img st.data.dmem (off (fb m0) 1288) st14.data.dmem (off (fb m0) 2816) 480 :=
    D13.trans (imgF c hc13 (by decide) (by decide) (by decide) (by decide))
  -- `b14`: the point's size at `120` and `1272`, its elements to `1280`.
  refine cpStep (hm := hat14.2.mt) (hwfS := fun _ ↦ h.wf hat14.2.kept)
    (T' := t15) (vals' := vv m0 (V2 cm first.point.size)) hp hpre hmemcpy hat14
    b14_in_code (by simp [b14]) run_b14 (by decide) rfl (D := off (fb m0) 1280)
    (Sr := off (fb m0) 2816) (n := 480)
    (fun mc hmc ↦ (hmc.regs .rdi _ rfl).trans (ev_frame 1280))
    (fun mc hmc ↦ (hmc.regs .rsi _ rfl).trans (ev_frame 2816)) rfl (by decide)
    (fun mc ca ↦ ⟨mapF h ca (by nd), nwF c (by nd), apF c ca (by nd) (by nd) (by nd)⟩)
    (fun mc ca ↦ ⟨mapF h ca (by nd), nwF c (by nd)⟩)
    (sepFF c (by nd) (by nd) (by nd) (by nd) (by nd)) (Lc := [(1280, 480)]) (Oc := [])
    (fun q hq ↦ chgR_frame List.mem_cons_self hq) (by decide) (by decide) (by decide)
    (by decide) (by decide) rfl rfl rfl (by vtacC) rfl rfl rfl rfl rfl rfl rfl
    fun st15 mc14 hat15 hm14 hi14 hb14 hl14 hc14 hk14 ↦ ?_
  rw [NativeRustcVmX64.Vm.VerifyKeccak.b14_next] at hat15
  have W15 : NativeRustcVm.WordAt st15.data.dmem (off (fb m0) 1272)
      first.point.toList.length.toUInt64 :=
    Chg.wordF c hl14 (by decide) (by decide) (by decide) (by decide)
      (NativeRustcVmX64.Transcript.wordAt_write hm14 (r := 0) (o := 1272) (b := fb m0)
        (sz := 3368) rfl (by decide) (v := .var 18) (by decide))
  have A15 := A14.trans (imgF c hc14 (o := 1768) (n := 280) (by decide) (by decide) (by decide)
    (by decide))
  have E15 := E14.trans (imgF c hc14 (o := 992) (n := 280) (by decide) (by decide) (by decide)
    (by decide))
  have W15' := Chg.wordF c hc14 (o := 2048) (by decide) (by decide) (by decide) (by decide) W14
  have C15 := C14.trans (imgF c hc14 (o := 2056) (n := 480) (by decide) (by decide) (by decide)
    (by decide))
  have F15 : Img st.data.dmem (off (fb m0) 1288) st15.data.dmem (off (fb m0) 1280) 480 :=
    D14.trans ((imgF c hb14 (by decide) (by decide) (by decide) (by decide)).trans hi14)
  -- The bit weights at the scratch's start before `b15`'s call.
  have hch := hc9.trans (hc10.trans (hc11.trans (hc12.trans (hc13.trans hc14))))
  have hk15 := NativeRustcVmX64.Transcript.kept_trans hk9 (NativeRustcVmX64.Transcript.kept_trans
    hk10 (NativeRustcVmX64.Transcript.kept_trans hk11 (NativeRustcVmX64.Transcript.kept_trans hk12
      (NativeRustcVmX64.Transcript.kept_trans hk13 hk14))))
  have hw15 := Chg.wtsR c hch (by decide) (by decide) (o := 0) (by decide) (by decide) hw
  refine cpStep (hm := hat15.2.mt) (hwfS := fun _ ↦ h.wf hat15.2.kept)
    (T' := t16) (vals' := vv m0 (V2 cm first.point.size)) hp hpre hmemcpy hat15
    b15_in_code (by simp [b15]) run_b15 (by decide) rfl (D := off (ob m0 2) 25600)
    (Sr := off (ob m0 2) 0) (n := 25600)
    (fun mc hmc ↦ (hmc.regs .rdi _ rfl).trans (addW (reg m0 .r9) (BitVec.ofNat 64 25600)))
    (fun mc hmc ↦ (hmc.regs .rsi _ rfl).trans (off0 (ob m0 2)).symm) rfl (by decide)
    (fun mc ca ↦ ⟨mapR h ca (by nd) (by nd) (by nd), nwR c (by nd) (by nd) (by nd),
      apR c ca (by nd) (by nd) (by nd) (by nd)⟩)
    (fun mc ca ↦ ⟨mapR h ca (by nd) (by nd) (by nd), nwR c (by nd) (by nd) (by nd)⟩)
    (by
      show _ ∨ _
      rw [offR c (i := 2) (o := 25600) (by nd) (by nd) (by nd),
        offR c (i := 2) (o := 0) (by nd) (by nd) (by nd)]
      omega)
    (Lc := []) (Oc := [(2, 25600, 25600)]) (fun q hq ↦ chgR_reg List.mem_cons_self hq)
    (by decide) (by decide) (by decide) (by decide) (by decide) rfl rfl rfl (by vtacC) rfl rfl rfl
    rfl rfl rfl rfl fun st16 _ hat16 _ hi15 hb15 _ hc15 hk15' ↦ ?_
  rw [NativeRustcVmX64.Vm.VerifyKeccak.b15_next] at hat16
  have hall := hch.trans hc15
  have hk := NativeRustcVmX64.Transcript.kept_trans hk15 hk15'
  have hwm := Chg.wtsR c hb15 (by decide) (by decide) (o := 0) (by decide) (by decide) hw15
  refine cont st16 hat16 (Chg.ts c hall (by decide) (by decide) (by decide) hk hts) ?_ ?_
    (Chg.wtsR c hc15 (by decide) (by decide) (o := 0) (by decide) (by decide) hw15)
    ⟨hw.1, hi15.ewsAt hwm.2 (by rw [Array.length_toList, hw.1]; decide)⟩
  · refine claim_img hcl
      (E15.trans (imgF c hc15 (o := 992) (n := 280) (by decide) (by decide) (by decide)
        (by decide))) ?_ ?_
    · rw [koff_off]
      exact Chg.wordF c hc15 (by decide) (by decide) (by decide) (by decide) W15
    · rw [koff_off, koff_off]
      exact F15.trans (imgF c hc15 (o := 1280) (n := 480) (by decide) (by decide) (by decide)
        (by decide))
  · refine claim_img hcl
      (A15.trans (imgF c hc15 (o := 1768) (n := 280) (by decide) (by decide) (by decide)
        (by decide))) ?_ ?_
    · rw [koff_off]
      exact Chg.wordF c hc15 (by decide) (by decide) (by decide) (by decide) W15'
    · rw [koff_off, koff_off]
      exact C15.trans (imgF c hc15 (o := 2056) (n := 480) (by decide) (by decide) (by decide)
        (by decide))

end

end NativeRustcVmX64.KeccakGkr.VerifyKeccak
