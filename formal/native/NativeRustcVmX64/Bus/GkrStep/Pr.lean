module

public import NativeRustcVmX64.Bus.GkrStep.Ch
public import NativeRustcVmX64.Code.Vm.PolyEval.Names
public import NativeRustcVmX64.Code.Vm.ProdE.Names

/-!
# `gkr_step`'s products and check (x86-64)

From `AtPr` (`b15`): the three children's products (`prod_e`, `b15` to `b17`, at `304`, `320`,
`336`), their evaluation at the combiner (`poly_eval`, `b18`), the check against the claim (`b19`,
`b20`) (`pr_spec`, to `AtTl`; else `NativeRustcVmX64.Vm.GkrStep.label_17`).
-/

namespace NativeRustcVmX64.Bus.GkrStep

open NativeRustcX64 NativeRustcX64.Sym NativeRustcVmX64.Vm.GkrStep
open NativeRustcVmX64.Transcript NativeRustcVmX64.Sumcheck NativeRustcVmX64.Bus.Gkr
open NativeVm.Model NativeRustcVm.Transcript NativeRustcVm.Bus

public section

/-- The derived `==` of elements: their limbs equal. -/
theorem ew_beq (x y : EW) : (x == y) = (x.c0 == y.c0 && x.c1 == y.c1) := by
  obtain ⟨a, b⟩ := x
  obtain ⟨c, d⟩ := y
  rfl

theorem cmp_w64 (x y : UInt64) : CmpOp.apply .eq .W64 x.toBitVec y.toBitVec = (x == y) := by
  simp only [CmpOp.apply, low_W64]
  by_cases h : x = y
  · simp [h]
  · simp [h, UInt64.toBitVec_inj]

/-- Three elements by their words. -/
theorem ews3' {d : Mem 64} {p : BitVec 64} {x y z : EW}
    (h0 : NativeRustcVm.WordAt d (off p 0) x.c0) (h1 : NativeRustcVm.WordAt d (off p 8) x.c1)
    (h2 : NativeRustcVm.WordAt d (off p 16) y.c0) (h3 : NativeRustcVm.WordAt d (off p 24) y.c1)
    (h4 : NativeRustcVm.WordAt d (off p 32) z.c0) (h5 : NativeRustcVm.WordAt d (off p 40) z.c1) :
    NativeRustcVm.EWsAt d p [x, y, z] := by
  rw [off_zero] at h0
  refine ewsAt_cons.mpr ⟨ewAt_iff.mpr ⟨h0, h1⟩, ewsAt_cons.mpr ⟨ewAt_iff.mpr ⟨?_, ?_⟩,
    ewsAt_cons.mpr ⟨ewAt_iff.mpr ⟨?_, ?_⟩, ewsAt_nil _ _⟩⟩⟩
  · exact h2
  · rw [off_off]; exact h3
  · rw [off_off]; exact h4
  · rw [off_off, off_off]; exact h5

variable [Host] {a : DecArea} {s0 : TState} {g0 : GkrStateW} {m0 : MachineData} {k : Nat}

/-- **A leaf call** from the frame at offset `32` (its changes in its stack only): the frame bytes
from `32`, the `TState` and the `GkrStateW` kept. -/
theorem leaf (h : GkrStepPre a s0 g0 m0) {X : Nat}
    (hX : X ∈ [bitLengthStack, grindStack, squeezeStack, polyEvalStack, readScalarsStack,
      prodEStack, sampleChallengesStack, mleStack]) {l : Label} {P : MachineData → Prop}
    {Q : MachineData → MachineData → Prop} (hspec : Spec (Labels.label l) P Q)
    (hQ : ∀ m m', Q m m' → NativeRustcVm.SameOutside m.dmem m'.dmem
      (fun q ↦ NativeRustcVm.InRange (stackBelow m X) X q) ∧ Saved m m')
    {st : MachineState} {next : Int64} {R : MachineState → Prop} (fr : FR m0 32 st.data)
    (hpc : st.pc = Labels.label l ∧ retOf st.data = next) (hP : P st.data)
    {s : TState} {g : GkrStateW} (hts : TStateAt st.data.dmem (reg m0 .rdi) a s)
    (hgs : GkrStateWAt st.data.dmem (reg m0 .rcx) g)
    (cont : ∀ m2 : MachineData, FR m0 40 m2 → Q st.data m2 →
      (∀ r, calleeSaved r = true → reg m2 r = reg st.data r) →
      (∀ {o : Nat} {bs : List UInt8}, 32 ≤ o → o + bs.length ≤ 1408 →
        NativeRustcVm.BytesAt st.data.dmem (off (fb m0) o) bs →
        NativeRustcVm.BytesAt m2.dmem (off (fb m0) o) bs) →
      TStateAt m2.dmem (reg m0 .rdi) a s → GkrStateWAt m2.dmem (reg m0 .rcx) g →
      Eventually (step1 Host.exe) R ⟨m2, next⟩) :
    Eventually (step1 Host.exe) R st := by
  have hle := le32 hX
  refine Fr.call (c := 32) (Nc := X) (lo := 40) (len := 0) (X := fun _ ↦ False)
    (pre_stack h) N_ge (by omega) hle (slots_call (by omega) (by omega)) (by omega)
    (outs_not_frame h) (fun _ h ↦ h.elim) hspec fr hpc hP
    (fun m' hq ↦ ⟨NativeRustcVm.SameOutside.mono (hQ _ _ hq).1 fun _ h ↦ .inl h, (hQ _ _ hq).2⟩)
    fun m2 fr2 hq hs hcs ↦ ?_
  have hcal : ∀ q, (NativeRustcVm.InRange (stackBelow st.data X) X q ∨ False) →
      NativeRustcVm.InRange (stackBelow m0 gkrStepStack) gkrStepStack q ∨
        NativeRustcVm.InRange (reg m0 .rcx) gkrStateBytes q :=
    fun q hq ↦ hq.elim (fun hq ↦ .inl (calleeStack h (by omega) fr hle hq)) False.elim
  exact cont m2 fr2 hq hcs (fun ho hob hb ↦ keepCall h fr hle hs ho hob (fun _ _ h ↦ h) hb)
    (tsKeep h (hQ _ _ hq).2.2 hs hcal hts)
    (gsKeep h hs (fun q hq ↦ hq.elim (fun hq ↦ .inl (calleeStack h (by omega) fr hle hq))
      False.elim) hgs)

omit [Host] in
/-- A frame slice's elements. -/
theorem slice_fb {d : MachineData} {o : Nat} {xs : Array EW}
    (hx : NativeRustcVm.EWsAt d.dmem (off (fb m0) o) xs.toList) {n : BitVec 64}
    (hn : n.toNat = xs.size) : slice d (off (fb m0) o) n = xs := by
  unfold slice
  rw [hn, ← Array.length_toList, NativeRustcVm.ewsOf_of_ewsAt hx, Array.toArray_toList]

/-- `prod_e`'s precondition, a child of `2^step` elements at `o` of the frame. -/
theorem prodPre (h : GkrStepPre a s0 g0 m0) {d : MachineData} (fr : FR m0 32 d) {o : Nat}
    (ho : 40 ≤ o) (ho' : o + 64 ≤ 1360) (hdi : reg d .rdi = off (fb m0) o)
    (hsi : (reg d .rsi).toNat = 2 ^ (reg m0 .rsi).toNat) : ProdEPre d := by
  have hle := le32 (X := prodEStack) (by simp)
  have c32 := ctxF h (1408 - 32) (by omega)
  have hn := two_pow_le h
  have hn1 : 2 ≤ 2 ^ (reg m0 .rsi).toNat := by
    rcases pre_step h with e | e <;> rw [e] <;> decide
  have hout := outFb h fr hle (o := o) (n := 16 * 2 ^ (reg m0 .rsi).toNat) (by omega) (by omega)
  unfold ProdEPre SliceOk Readable OffStack
  rw [hdi, hsi]
  exact ⟨c32.stackOk (atC h (by omega) fr) hle, hn1, hn, ⟨hout.1, hout.2.1⟩, hout.2.2.2.2.1⟩

omit [Host] in
theorem inRange0 {x q : BitVec 64} : ¬ NativeRustcVm.InRange x 0 q := Nat.not_lt_zero _

omit [Host] in
theorem changesQ {X : Nat} {m m' : MachineData} (hc : Changes m m' X 0 0) :
    NativeRustcVm.SameOutside m.dmem m'.dmem (fun q ↦ NativeRustcVm.InRange (stackBelow m X) X q) :=
  NativeRustcVm.SameOutside.mono hc fun _ hq ↦ hq.elim (fun h ↦ (inRange0 h).elim) id

/-- **The products and the check** (`b15` to `b20`), from `AtPr`. -/
theorem pr_spec (hp : Placed code k) (h : GkrStepPre a s0 g0 m0)
    (hpr : Spec (Labels.label NativeRustcVmX64.Vm.ProdE.entryLabel) ProdEPre ProdEPost)
    (hpe : Spec (Labels.label NativeRustcVmX64.Vm.PolyEval.entryLabel) PolyEvalPre PolyEvalPost)
    (htl : ∀ xs h0 h1 h2 s3 d, AtTl a s0 g0 m0 xs h0 h1 h2 s3 d →
      Eventually (step1 Host.exe) (Goal a s0 g0 m0) ⟨d, Host.addrOf (k + NativeRustcVmX64.Vm.GkrStep.b21Offset)⟩)
    {c cl : EW} {xs h0 h1 h2 : Array EW} {s3 : TState} {d : MachineData}
    (at0 : AtPr a s0 g0 m0 c cl xs h0 h1 h2 s3 d) :
    Eventually (step1 Host.exe) (Goal a s0 g0 m0) ⟨d, Host.addrOf (k + NativeRustcVmX64.Vm.GkrStep.b15Offset)⟩ := by
  have hn := two_pow_le h
  have hxl : xs.toList.length ≤ 63 := by
    rw [Array.length_toList]; have := at0.size; unfold busPointCap at this; omega
  have L0 : 16 * h0.toList.length ≤ 64 := by rw [Array.length_toList, at0.z0]; omega
  have L1 : 16 * h1.toList.length ≤ 64 := by rw [Array.length_toList, at0.z1]; omega
  have L2 : 16 * h2.toList.length ≤ 64 := by rw [Array.length_toList, at0.z2]; omega
  have l4 : ((List.range 4).map (byteOf (reg m0 .rdx))).length = 4 := by simp
  have l8 : ∀ w : UInt64, (NativeRustcVm.wordBytes w).length = 8 := NativeRustcVm.length_wordBytes
  have lE : ∀ xs : List EW, (xs.flatMap NativeRustcVm.ewBytes).length = 16 * xs.length :=
    NativeRustcVm.length_ewsBytes
  have E0 := lE h0.toList
  have E1 := lE h1.toList
  have E2 := lE h2.toList
  -- `b15`: `prod_e(frame + 112, 2^step)`.
  have hwf1 := wf0 h at0.fr.frame.kept (Host.addrOf (k + NativeRustcVmX64.Vm.GkrStep.b15Offset + b15.length)).toBitVec
  obtain ⟨hmid1, hw1, hdi1, hsi1, hk1⟩ := ok_b15
  refine exec_then (infix_of b15_in_code (by simp [b15]) hp) exit_b15 hwf1 (fun _ _ ↦ rfl)
    (match_head at0.fr _) fun st1 hm1 hpc1 ↦ ?_
  obtain ⟨fr1, hs1⟩ := FR.block h at0.fr hwf1 hm1 hmid1 (.inl rfl) (W01_of_W0 hw1) (by decide)
    (by omega)
  obtain ⟨ts1, gs1⟩ := tsgs_keep h (hm1.kept hwf1) hs1 at0.ts at0.gs
  have kp1 : ∀ {o : Nat} {bs : List UInt8}, o + bs.length ≤ 1408 → (o + bs.length ≤ 32 ∨ 40 ≤ o) →
      NativeRustcVm.BytesAt d.dmem (off (fb m0) o) bs →
      NativeRustcVm.BytesAt st1.data.dmem (off (fb m0) o) bs := fun hle hd hb ↦
    keep3240 hwf1 hm1 hmid1 hw1 hle (fun p hp ↦ by simp at hp; subst hp; simp; omega) hb
  have k1 : ∀ r ∈ cs6, reg st1.data r = reg d r := fun r hr ↦ kr hm1 hk1 hr
  have e12 : (reg st1.data .r12).toNat = 2 ^ (reg m0 .rsi).toNat := by
    rw [k1 .r12 (by simp)]; exact at0.r12
  have edi1 : reg st1.data .rdi = off (fb m0) 112 := (rv hm1 hdi1).trans (eval_ptr0 112)
  have esi1 : (reg st1.data .rsi).toNat = 2 ^ (reg m0 .rsi).toNat := by
    rw [rv hm1 hsi1]; exact at0.r12
  simp only [PcOk] at hpc1
  have k01 := kp1 (by rw [lE]; omega) (by omega) at0.k0
  refine leaf h (X := prodEStack) (by simp) hpr (fun _ _ hq ↦ ⟨changesQ hq.2.1, hq.2.2⟩) fr1 hpc1
    (prodPre h fr1 (by omega) (by omega) edi1 esi1) ts1 gs1 fun m2 fr2 hq2 hcs2 kp2 ts2 gs2 ↦ ?_
  have hP0 : ewRet m2 = prodE h0 := by
    rw [hq2.1, edi1, slice_fb k01 (by rw [esi1, at0.z0])]
  -- `b16`: the product at `304`; `prod_e(frame + 176, 2^step)`.
  have hwf3 := wf0 h fr2.frame.kept (Host.addrOf (k + NativeRustcVmX64.Vm.GkrStep.b16Offset + b16.length)).toBitVec
  obtain ⟨hmid3, hw3, w304, w312, hdi3, hsi3, hk3⟩ := ok_b16
  refine exec_at (st := ⟨m2, _⟩) (infix_of b16_in_code (by simp [b16]) hp) exit_b16 hwf3
    (fun _ _ ↦ rfl) (by show Host.addrOf (k + NativeRustcVmX64.Vm.GkrStep.b15Offset + b15.length) = _; rw [Nat.add_assoc]; exact congrArg (fun j ↦ Host.addrOf (k + j)) NativeRustcVmX64.Vm.GkrStep.b15_next)
    (match_head fr2 _) fun st3 hm3 hpc3 ↦ ?_
  obtain ⟨fr3, hs3⟩ := FR.block h fr2 hwf3 hm3 hmid3 (.inl rfl) (W01_of_W0 hw3) (by decide)
    (by omega)
  obtain ⟨ts3, gs3⟩ := tsgs_keep h (hm3.kept hwf3) hs3 ts2 gs2
  have kp3 : ∀ {o : Nat} {bs : List UInt8}, o + bs.length ≤ 1408 →
      (o + bs.length ≤ 32 ∨ (40 ≤ o ∧ o + bs.length ≤ 304) ∨ 320 ≤ o) →
      NativeRustcVm.BytesAt m2.dmem (off (fb m0) o) bs →
      NativeRustcVm.BytesAt st3.data.dmem (off (fb m0) o) bs := fun hle hd hb ↦
    keep3240 hwf3 hm3 hmid3 hw3 hle (fun p hp ↦ by
      simp at hp; rcases hp with rfl | rfl <;> simp <;> omega) hb
  have W304 := wordAt_write hm3 (r := 0) (o := 304) (b := stackBelow m0 1408) (sz := 1408 + 8) rfl
    (by omega) w304
  have W312 := wordAt_write hm3 (r := 0) (o := 312) (b := stackBelow m0 1408) (sz := 1408 + 8) rfl
    (by omega) w312
  have k3 : ∀ r ∈ cs6, reg st3.data r = reg d r := fun r hr ↦
    (kr hm3 hk3 hr).trans ((hcs2 r (by simp [cs6] at hr; rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> rfl)).trans (k1 r hr))
  simp only [PcOk] at hpc3
  have k13 := kp3 (by rw [lE]; omega) (by omega) (kp2 (by omega) (by rw [lE]; omega)
    (kp1 (by rw [lE]; omega) (by omega) at0.k1))
  have edi3 : reg st3.data .rdi = off (fb m0) 176 := (rv hm3 hdi3).trans (eval_ptr0 176)
  have esi3 : (reg st3.data .rsi).toNat = 2 ^ (reg m0 .rsi).toNat := by
    rw [rv hm3 hsi3]; show (reg m2 .r12).toNat = _; rw [hcs2 .r12 rfl]; exact e12
  refine leaf h (X := prodEStack) (by simp) hpr (fun _ _ hq ↦ ⟨changesQ hq.2.1, hq.2.2⟩) fr3 hpc3
    (prodPre h fr3 (by omega) (by omega) edi3 esi3) ts3 gs3 fun m4 fr4 hq4 hcs4 kp4 ts4 gs4 ↦ ?_
  have hP1 : ewRet m4 = prodE h1 := by
    rw [hq4.1, edi3, slice_fb k13 (by rw [esi3, at0.z1])]
  -- `b17`: the product at `320`; `prod_e(frame + 240, 2^step)`.
  have hwf5 := wf0 h fr4.frame.kept (Host.addrOf (k + NativeRustcVmX64.Vm.GkrStep.b17Offset + b17.length)).toBitVec
  obtain ⟨hmid5, hw5, w320, w328, hdi5, hsi5, hk5⟩ := ok_b17
  refine exec_at (st := ⟨m4, _⟩) (infix_of b17_in_code (by simp [b17]) hp) exit_b17 hwf5
    (fun _ _ ↦ rfl) (by show Host.addrOf (k + NativeRustcVmX64.Vm.GkrStep.b16Offset + b16.length) = _; rw [Nat.add_assoc]; exact congrArg (fun j ↦ Host.addrOf (k + j)) NativeRustcVmX64.Vm.GkrStep.b16_next)
    (match_head fr4 _) fun st5 hm5 hpc5 ↦ ?_
  obtain ⟨fr5, hs5⟩ := FR.block h fr4 hwf5 hm5 hmid5 (.inl rfl) (W01_of_W0 hw5) (by decide)
    (by omega)
  obtain ⟨ts5, gs5⟩ := tsgs_keep h (hm5.kept hwf5) hs5 ts4 gs4
  have kp5 : ∀ {o : Nat} {bs : List UInt8}, o + bs.length ≤ 1408 →
      (o + bs.length ≤ 32 ∨ (40 ≤ o ∧ o + bs.length ≤ 320) ∨ 336 ≤ o) →
      NativeRustcVm.BytesAt m4.dmem (off (fb m0) o) bs →
      NativeRustcVm.BytesAt st5.data.dmem (off (fb m0) o) bs := fun hle hd hb ↦
    keep3240 hwf5 hm5 hmid5 hw5 hle (fun p hp ↦ by
      simp at hp; rcases hp with rfl | rfl <;> simp <;> omega) hb
  have W320 := wordAt_write hm5 (r := 0) (o := 320) (b := stackBelow m0 1408) (sz := 1408 + 8) rfl
    (by omega) w320
  have W328 := wordAt_write hm5 (r := 0) (o := 328) (b := stackBelow m0 1408) (sz := 1408 + 8) rfl
    (by omega) w328
  have k5 : ∀ r ∈ cs6, reg st5.data r = reg d r := fun r hr ↦
    (kr hm5 hk5 hr).trans ((hcs4 r (by simp [cs6] at hr; rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> rfl)).trans (k3 r hr))
  simp only [PcOk] at hpc5
  have k25 := kp5 (by rw [lE]; omega) (by omega) (kp4 (by omega) (by rw [lE]; omega)
    (kp3 (by rw [lE]; omega) (by omega) (kp2 (by omega) (by rw [lE]; omega)
      (kp1 (by rw [lE]; omega) (by omega) at0.k2))))
  have edi5 : reg st5.data .rdi = off (fb m0) 240 := (rv hm5 hdi5).trans (eval_ptr0 240)
  have esi5 : (reg st5.data .rsi).toNat = 2 ^ (reg m0 .rsi).toNat := by
    rw [rv hm5 hsi5]; show (reg m4 .r12).toNat = _; rw [hcs4 .r12 rfl, k3 .r12 (by simp)]
    exact at0.r12
  refine leaf h (X := prodEStack) (by simp) hpr (fun _ _ hq ↦ ⟨changesQ hq.2.1, hq.2.2⟩) fr5 hpc5
    (prodPre h fr5 (by omega) (by omega) edi5 esi5) ts5 gs5 fun m6 fr6 hq6 hcs6 kp6 ts6 gs6 ↦ ?_
  have hP2 : ewRet m6 = prodE h2 := by
    rw [hq6.1, edi5, slice_fb k25 (by rw [esi5, at0.z2])]
  -- the products' words
  have e0 : UInt64.ofBitVec (reg m2 .rax) = (prodE h0).c0 := congrArg EW.c0 hP0
  have e0' : UInt64.ofBitVec (reg m2 .rdx) = (prodE h0).c1 := congrArg EW.c1 hP0
  have e1 : UInt64.ofBitVec (reg m4 .rax) = (prodE h1).c0 := congrArg EW.c0 hP1
  have e1' : UInt64.ofBitVec (reg m4 .rdx) = (prodE h1).c1 := congrArg EW.c1 hP1
  have e2 : UInt64.ofBitVec (reg m6 .rax) = (prodE h2).c0 := congrArg EW.c0 hP2
  have e2' : UInt64.ofBitVec (reg m6 .rdx) = (prodE h2).c1 := congrArg EW.c1 hP2
  have V304 : NativeRustcVm.WordAt st3.data.dmem (off (fb m0) 304) (prodE h0).c0 := by
    rw [← e0]; exact W304
  have V312 : NativeRustcVm.WordAt st3.data.dmem (off (fb m0) 312) (prodE h0).c1 := by
    rw [← e0']; exact W312
  have V320 : NativeRustcVm.WordAt st5.data.dmem (off (fb m0) 320) (prodE h1).c0 := by
    rw [← e1]; exact W320
  have V328 : NativeRustcVm.WordAt st5.data.dmem (off (fb m0) 328) (prodE h1).c1 := by
    rw [← e1']; exact W328
  -- `b18`: the third product at `336`; `poly_eval(frame + 304, 3, c)`.
  have hwf7 := wf0 h fr6.frame.kept (Host.addrOf (k + NativeRustcVmX64.Vm.GkrStep.b18Offset + b18.length)).toBitVec
  obtain ⟨hmid7, hw7, w336, w344, hdi7, hsi7, hdx7, hcx7, hk7⟩ := ok_b18
  refine exec_at (st := ⟨m6, _⟩) (infix_of b18_in_code (by simp [b18]) hp) exit_b18 hwf7
    (fun _ _ ↦ rfl) (by show Host.addrOf (k + NativeRustcVmX64.Vm.GkrStep.b17Offset + b17.length) = _; rw [Nat.add_assoc]; exact congrArg (fun j ↦ Host.addrOf (k + j)) NativeRustcVmX64.Vm.GkrStep.b17_next)
    (match_head fr6 _) fun st7 hm7 hpc7 ↦ ?_
  obtain ⟨fr7, hs7⟩ := FR.block h fr6 hwf7 hm7 hmid7 (.inl rfl) (W01_of_W0 hw7) (by decide)
    (by omega)
  obtain ⟨ts7, gs7⟩ := tsgs_keep h (hm7.kept hwf7) hs7 ts6 gs6
  have kp7 : ∀ {o : Nat} {bs : List UInt8}, o + bs.length ≤ 1408 →
      (o + bs.length ≤ 32 ∨ (40 ≤ o ∧ o + bs.length ≤ 336) ∨ 352 ≤ o) →
      NativeRustcVm.BytesAt m6.dmem (off (fb m0) o) bs →
      NativeRustcVm.BytesAt st7.data.dmem (off (fb m0) o) bs := fun hle hd hb ↦
    keep3240 hwf7 hm7 hmid7 hw7 hle (fun p hp ↦ by
      simp at hp; rcases hp with rfl | rfl <;> simp <;> omega) hb
  have W336 := wordAt_write hm7 (r := 0) (o := 336) (b := stackBelow m0 1408) (sz := 1408 + 8) rfl
    (by omega) w336
  have W344 := wordAt_write hm7 (r := 0) (o := 344) (b := stackBelow m0 1408) (sz := 1408 + 8) rfl
    (by omega) w344
  have V336 : NativeRustcVm.WordAt st7.data.dmem (off (fb m0) 336) (prodE h2).c0 := by
    rw [← e2]; exact W336
  have V344 : NativeRustcVm.WordAt st7.data.dmem (off (fb m0) 344) (prodE h2).c1 := by
    rw [← e2']; exact W344
  have W8 : ∀ w : UInt64, 8 = (NativeRustcVm.wordBytes w).length := fun w ↦ (l8 w).symm
  -- bytes from `m6` (after the third call) to `st7`, from `m4`, from `st3`...
  have t6 : ∀ {o : Nat} {w : UInt64}, 40 ≤ o → o + 8 ≤ 336 →
      NativeRustcVm.WordAt m6.dmem (off (fb m0) o) w → NativeRustcVm.WordAt st7.data.dmem (off (fb m0) o) w :=
    fun h1 h2 hb ↦ kp7 (by rw [l8]; omega) (by rw [l8]; omega) hb
  have t5 : ∀ {o : Nat} {w : UInt64}, 40 ≤ o → o + 8 ≤ 336 →
      NativeRustcVm.WordAt st5.data.dmem (off (fb m0) o) w →
      NativeRustcVm.WordAt st7.data.dmem (off (fb m0) o) w :=
    fun h1 h2 hb ↦ t6 h1 h2 (kp6 (by omega) (by rw [l8]; omega) hb)
  have t3 : ∀ {o : Nat} {w : UInt64}, 40 ≤ o → o + 8 ≤ 320 →
      NativeRustcVm.WordAt st3.data.dmem (off (fb m0) o) w →
      NativeRustcVm.WordAt st7.data.dmem (off (fb m0) o) w :=
    fun h1 h2 hb ↦ t5 h1 (by omega) (kp5 (by rw [l8]; omega) (by rw [l8]; omega)
      (kp4 (by omega) (by rw [l8]; omega) hb))
  have t1 : ∀ {o : Nat} {w : UInt64}, 40 ≤ o → o + 8 ≤ 304 →
      NativeRustcVm.WordAt st1.data.dmem (off (fb m0) o) w →
      NativeRustcVm.WordAt st7.data.dmem (off (fb m0) o) w :=
    fun h1 h2 hb ↦ t3 h1 (by omega) (kp3 (by rw [l8]; omega) (by rw [l8]; omega)
      (kp2 (by omega) (by rw [l8]; omega) hb))
  have hPs : NativeRustcVm.EWsAt st7.data.dmem (off (fb m0) 304)
      #[prodE h0, prodE h1, prodE h2].toList :=
    ews3' (by rw [off_off]; exact t3 (by omega) (by omega) V304)
      (by rw [off_off]; exact t3 (by omega) (by omega) V312)
      (by rw [off_off]; exact t5 (by omega) (by omega) V320)
      (by rw [off_off]; exact t5 (by omega) (by omega) V328)
      (by rw [off_off]; exact V336) (by rw [off_off]; exact V344)
  have k6 : ∀ r ∈ cs6, reg m6 r = reg d r := fun r hr ↦
    (hcs6 r (by simp [cs6] at hr; rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> rfl)).trans (k5 r hr)
  have c104 : NativeRustcVm.WordAt m6.dmem (off (fb m0) 104) c.c0 :=
    kp6 (by omega) (by rw [l8]; omega) (kp5 (by rw [l8]; omega) (by rw [l8]; omega)
      (kp4 (by omega) (by rw [l8]; omega) (kp3 (by rw [l8]; omega) (by rw [l8]; omega)
        (kp2 (by omega) (by rw [l8]; omega) (kp1 (by rw [l8]; omega) (by rw [l8]; omega) at0.c104)))))
  have edi7 : reg st7.data .rdi = off (fb m0) 304 := (rv hm7 hdi7).trans (eval_ptr0 304)
  have esi7 : reg st7.data .rsi = BitVec.ofNat 64 3 := rv hm7 hsi7
  have edx7 : reg st7.data .rdx = c.c0.toBitVec :=
    (rv hm7 hdx7).trans (load_ofMachine (rs := [(stackBelow m0 1408, 1408 + 8)]) (r := 0) (o := 104)
      rfl c104)
  have ecx7 : reg st7.data .rcx = c.c1.toBitVec :=
    (rv hm7 hcx7).trans ((k6 .rbp (by simp)).trans at0.rbp)
  have hle7 := le32 (X := polyEvalStack) (by simp)
  have c32 := ctxF h (1408 - 32) (by omega)
  simp only [PcOk] at hpc7
  refine leaf h (X := polyEvalStack) (by simp) hpe (fun _ _ hq ↦ ⟨changesQ hq.2.1, hq.2.2⟩) fr7
    hpc7 ?_ ts7 gs7 fun m8 fr8 hq8 hcs8 kp8 ts8 gs8 ↦ ?_
  · have hout := outFb h fr7 hle7 (o := 304) (n := 16 * 3) (by omega) (by omega)
    unfold PolyEvalPre SliceOk Readable OffStack
    rw [edi7, esi7, show (BitVec.ofNat 64 3).toNat = 3 from rfl]
    exact ⟨c32.stackOk (atC h (by omega) fr7) hle7, by omega, ⟨hout.1, hout.2.1⟩,
      hout.2.2.2.2.1⟩
  set PE := polyEval #[prodE h0, prodE h1, prodE h2] c with hPE
  have hPE8 : ewRet m8 = PE := by
    rw [hq8.1, edi7, esi7, slice_fb hPs (by rfl)]
    congr 1
    show (⟨_, _⟩ : EW) = c
    rw [edx7, ecx7]
  have p0 : UInt64.ofBitVec (reg m8 .rax) = PE.c0 := congrArg EW.c0 hPE8
  have p1 : UInt64.ofBitVec (reg m8 .rdx) = PE.c1 := congrArg EW.c1 hPE8
  have k8 : ∀ r ∈ cs6, reg m8 r = reg d r := fun r hr ↦
    (hcs8 r (by simp [cs6] at hr; rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> rfl)).trans
      ((kr hm7 hk7 hr).trans (k6 r hr))
  have t8 : ∀ {o : Nat} {bs : List UInt8}, 40 ≤ o → o + bs.length ≤ 1408 →
      (o + bs.length ≤ 304 ∨ 352 ≤ o) →
      NativeRustcVm.BytesAt d.dmem (off (fb m0) o) bs →
      NativeRustcVm.BytesAt m8.dmem (off (fb m0) o) bs := by
    intro o bs h1 h2 h3 hb
    exact kp8 (by omega) h2 (kp7 h2 (by omega) (kp6 (by omega) h2 (kp5 h2 (by omega)
      (kp4 (by omega) h2 (kp3 h2 (by omega) (kp2 (by omega) h2 (kp1 h2 (by omega) hb)))))))
  have cl88 := t8 (by omega) (by rw [l8]; omega) (by rw [l8]; omega) at0.cl88
  have cl80 := t8 (by omega) (by rw [l8]; omega) (by rw [l8]; omega) at0.cl80
  -- `b19`, `b20`: the check.
  have hfin : run0 s0 g0 m0 = if cl == PE then
      ((sampleChallenges (reg m0 .rsi).toNat).run s3).bind fun y ↦
        some (⟨#[multilinearEval h0 y.1, multilinearEval h1 y.1, multilinearEval h2 y.1],
          y.1 ++ xs⟩, y.2) else none := by
    rw [at0.run]; rfl
  have hwf9 := wf0 h fr8.frame.kept 0
  obtain ⟨hmid9, hmem9, hk9⟩ := ok_b19
  refine exec_at (st := ⟨m8, _⟩) (infix_of b19_in_code (by simp [b19]) hp) exit_b19 hwf9 nofun
    (by show Host.addrOf (k + NativeRustcVmX64.Vm.GkrStep.b18Offset + b18.length) = _; rw [Nat.add_assoc]; exact congrArg (fun j ↦ Host.addrOf (k + j)) NativeRustcVmX64.Vm.GkrStep.b18_next)
    (match_head fr8 0) fun st9 hm9 hpc9 ↦ ?_
  obtain ⟨fr9, hd9⟩ := FR.block_nil h fr8 hwf9 hm9 hmid9 hmem9
  have hc9 : SBool.eval (frameEnv m0 m8 1408 [] (fun _ ↦ 0) 0)
      (SBool.cmp .eq .W64 (.load 0 88 8) (.reg .rax)).not = !(cl.c0 == PE.c0) := by
    show (!CmpOp.apply .eq .W64 ((frameEnv m0 m8 1408 [] (fun _ ↦ 0) 0).load 0 88 8)
      (reg m8 .rax)) = _
    rw [load_ofMachine (rs := [(stackBelow m0 1408, 1408 + 8)]) (r := 0) (o := 88) rfl cl88,
      show reg m8 .rax = PE.c0.toBitVec by rw [← p0], cmp_w64]
  simp only [PcOk, hc9] at hpc9
  by_cases q0 : (cl.c0 == PE.c0) = true
  · simp only [q0, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hpc9
    have hwf10 := wf0 h fr9.frame.kept 0
    obtain ⟨hmid10, hmem10, hk10⟩ := ok_b20
    refine exec_at (infix_of b20_in_code (by simp [b20]) hp) exit_b20 hwf10 nofun
      (hpc9.trans (by rw [Nat.add_assoc]; exact congrArg (fun j ↦ Host.addrOf (k + j)) NativeRustcVmX64.Vm.GkrStep.b19_next)) (match_head fr9 0)
      fun st10 hm10 hpc10 ↦ ?_
    obtain ⟨fr10, hd10⟩ := FR.block_nil h fr9 hwf10 hm10 hmid10 hmem10
    have hc10 : SBool.eval (frameEnv m0 st9.data 1408 [] (fun _ ↦ 0) 0)
        (SBool.cmp .eq .W64 (.load 0 80 8) (.reg .rdx)).not = !(cl.c1 == PE.c1) := by
      show (!CmpOp.apply .eq .W64 ((frameEnv m0 st9.data 1408 [] (fun _ ↦ 0) 0).load 0 80 8)
        (reg st9.data .rdx)) = _
      rw [load_ofMachine (rs := [(stackBelow m0 1408, 1408 + 8)]) (r := 0) (o := 80) rfl
        (by rw [hd9]; exact cl80), kr hm9 hk9 (by simp),
        show reg m8 .rdx = PE.c1.toBitVec by rw [← p1], cmp_w64]
    simp only [PcOk, hc10] at hpc10
    by_cases q1 : (cl.c1 == PE.c1) = true
    · simp only [q1, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hpc10
      have hq : (cl == PE) = true := by rw [ew_beq, q0, q1]; rfl
      have k10 : ∀ r ∈ cs6, reg st10.data r = reg d r := fun r hr ↦
        (kr hm10 hk10 hr).trans ((kr hm9 hk9 (List.mem_cons_of_mem _ hr)).trans (k8 r hr))
      have hd : st10.data.dmem = m8.dmem := hd10.trans hd9
      refine at_pc (hpc10.trans (by rw [Nat.add_assoc]; exact congrArg (fun j ↦ Host.addrOf (k + j)) NativeRustcVmX64.Vm.GkrStep.b20_next)) (htl xs h0 h1 h2 s3 st10.data
        ⟨fr10, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, at0.size, ?_, ?_, ?_, at0.z0, at0.z1, at0.z2, ?_, ?_, ?_⟩)
      · exact (k10 .rbx (by simp)).trans at0.rbx
      · rw [k10 .r12 (by simp)]; exact at0.r12
      · rw [k10 .r13 (by simp)]; exact at0.r13
      · exact (k10 .r14 (by simp)).trans at0.r14
      · exact (k10 .r15 (by simp)).trans at0.r15
      · rw [hd]; exact t8 (by omega) (by rw [l4]; omega) (by rw [l4]; omega) at0.l44
      · rw [hd]; exact t8 (by omega) (by rw [l8]; omega) (by rw [l8]; omega) at0.pa
      · rw [hd]; exact t8 (by omega) (by rw [lE]; omega) (by omega) at0.hxs
      · rw [hd]; exact t8 (by omega) (by omega) (by omega) at0.k0
      · rw [hd]; exact t8 (by omega) (by omega) (by omega) at0.k1
      · rw [hd]; exact t8 (by omega) (by omega) (by omega) at0.k2
      · rw [hd]; exact ts8
      · rw [hd]; exact gs8
      · rw [hfin, hq]; rfl
    · simp only [q1, Bool.not_false, ↓reduceIte] at hpc10
      exact at_pc (hpc10.trans (hp.label NativeRustcVmX64.Vm.GkrStep.label_17_at)) (fail_spec hp h fr10 (by
        rw [hfin, show (cl == PE) = false by rw [ew_beq, q0]; simpa using q1]; rfl))
  · simp only [q0, Bool.not_false, ↓reduceIte] at hpc9
    exact at_pc (hpc9.trans (hp.label NativeRustcVmX64.Vm.GkrStep.label_17_at)) (fail_spec hp h fr9 (by
      rw [hfin, show (cl == PE) = false by rw [ew_beq]; simp [q0]]; rfl))

end

end NativeRustcVmX64.Bus.GkrStep
