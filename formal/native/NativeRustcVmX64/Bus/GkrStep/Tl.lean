module

public import NativeRustcVmX64.Bus.GkrStep.Pr
public import NativeRustcVmX64.Code.Vm.BitLength.Names
public import NativeRustcVmX64.Code.Vm.MultilinearEvalByOfMultilinearEval.Names
public import NativeRustcVmX64.Code.Vm.TStateGrind.Names
public import NativeRustcVmX64.Code.Vm.TStateSampleChallenges.Names

/-!
# `gkr_step`'s coordinates and new values (x86-64)

From `AtTl` (`b21`): the second grind (`b21` to `b23`, of `0` bits), the coordinates `y`
(`sample_challenges`, `b24`, at `48`), the children's evaluations at `y` (`multilinear_eval_by`,
`b25` to `b27`) written as the new values, the new point's length and `y` (`b28` to `b30`)
(`tl_spec`, to `AtCp`).
-/

namespace NativeRustcVmX64.Bus.GkrStep

open NativeRustcX64 NativeRustcX64.Sym NativeRustcVmX64.Vm.GkrStep
open NativeRustcVmX64.Transcript NativeRustcVmX64.Sumcheck NativeRustcVmX64.Bus.Gkr
open NativeVm.Model NativeRustcVm.Transcript NativeRustcVm.Bus

@[expose] public section
variable [Labels]

/-- **At the point's tail** (`NativeRustcVmX64.Vm.GkrStep.label_13`, `k + NativeRustcVmX64.Vm.GkrStep.b31Offset`): the new values, the point's length and
`y` written; the sumcheck's challenges `xs` (`|xs|` in R13) still to copy after `y`. -/
structure AtCp (a : DecArea) (s0 : TState) (g0 : GkrStateW) (m0 : MachineData) (xs y vs : Array EW)
    (s' : TState) (d : MachineData) : Prop where
  fr : FR m0 40 d
  rbx : reg d .rbx = reg m0 .rsi
  r13 : (reg d .r13).toNat = xs.size
  r14 : reg d .r14 = reg m0 .rcx
  pa : NativeRustcVm.WordAt d.dmem (off (fb m0) 96) (UInt64.ofBitVec (off (reg m0 .rcx) 56))
  hxs : NativeRustcVm.EWsAt d.dmem (off (fb m0) 352) xs.toList
  size : xs.size + (reg m0 .rsi).toNat ≤ busPointCap
  ysz : y.size = (reg m0 .rsi).toNat
  vsz : vs.size = 3
  vals : NativeRustcVm.EWsAt d.dmem (reg m0 .rcx) vs.toList
  len : NativeRustcVm.WordAt d.dmem (off (reg m0 .rcx) 48) (y.size + xs.size).toUInt64
  ys : NativeRustcVm.EWsAt d.dmem (off (reg m0 .rcx) 56) y.toList
  ts : TStateAt d.dmem (reg m0 .rdi) a s'
  run : run0 s0 g0 m0 = some (⟨vs, y ++ xs⟩, s')

/-- **After `sample_challenges`** (`k + NativeRustcVmX64.Vm.GkrStep.b25Offset`): the coordinates `y` at `48` of the frame. -/
structure AtY (a : DecArea) (s0 : TState) (g0 : GkrStateW) (m0 : MachineData)
    (xs h0 h1 h2 y : Array EW) (s' : TState) (d : MachineData) : Prop where
  fr : FR m0 40 d
  rbx : reg d .rbx = reg m0 .rsi
  r12 : (reg d .r12).toNat = 2 ^ (reg m0 .rsi).toNat
  r13 : (reg d .r13).toNat = xs.size
  r14 : reg d .r14 = reg m0 .rcx
  rbp : reg d .rbp = off (fb m0) 48
  pa : NativeRustcVm.WordAt d.dmem (off (fb m0) 96) (UInt64.ofBitVec (off (reg m0 .rcx) 56))
  hxs : NativeRustcVm.EWsAt d.dmem (off (fb m0) 352) xs.toList
  size : xs.size + (reg m0 .rsi).toNat ≤ busPointCap
  k0 : NativeRustcVm.EWsAt d.dmem (off (fb m0) 112) h0.toList
  k1 : NativeRustcVm.EWsAt d.dmem (off (fb m0) 176) h1.toList
  k2 : NativeRustcVm.EWsAt d.dmem (off (fb m0) 240) h2.toList
  z0 : h0.size = 2 ^ (reg m0 .rsi).toNat
  z1 : h1.size = 2 ^ (reg m0 .rsi).toNat
  z2 : h2.size = 2 ^ (reg m0 .rsi).toNat
  yw : NativeRustcVm.EWsAt d.dmem (off (fb m0) 48) y.toList
  ysz : y.size = (reg m0 .rsi).toNat
  ts : TStateAt d.dmem (reg m0 .rdi) a s'
  run : run0 s0 g0 m0 = some (⟨#[multilinearEval h0 y, multilinearEval h1 y,
    multilinearEval h2 y], y ++ xs⟩, s')

end

public section

variable [Labels] {a : DecArea} {s0 : TState} {g0 : GkrStateW} {m0 : MachineData}

/-- **Bytes of the `GkrStateW`** kept where the memory changed in the stack, the frame or `n`
bytes of it at `lo` apart from them. -/
theorem pKeep (h : GkrStepPre a s0 g0 m0) {d d' : Mem 64} {R : BitVec 64 → Prop}
    (hs : NativeRustcVm.SameOutside d d' R) {lo n : Nat} (hlo : lo + n ≤ 1064)
    (hR : ∀ q, R q → NativeRustcVm.InRange (stackBelow m0 gkrStepStack) gkrStepStack q ∨
      NativeRustcVm.InRange (fb m0) 1360 q ∨ NativeRustcVm.InRange (off (reg m0 .rcx) lo) n q)
    {o : Nat} {bs : List UInt8} (hob : o + bs.length ≤ 1064)
    (hd : o + bs.length ≤ lo ∨ lo + n ≤ o)
    (hb : NativeRustcVm.BytesAt d (off (reg m0 .rcx) o) bs) :
    NativeRustcVm.BytesAt d' (off (reg m0 .rcx) o) bs := by
  have hgo := pre_gk h
  have hnw : (reg m0 .rcx).toNat + 1064 ≤ 2 ^ 64 := hgo.2.1
  have cx := ctxF h 1408 N_ge
  refine NativeRustcVm.BytesAt.of_sameOutside hb hs fun i hi hq ↦ ?_
  rw [off_add] at hq
  have hin : NativeRustcVm.InRange (reg m0 .rcx) gkrStateBytes (off (reg m0 .rcx) (o + i)) :=
    inRange_off_self (by show o + i < 1064; omega) (by show 1064 ≤ 2 ^ 64; omega)
  rcases hR _ hq with hq | hq | hq
  · exact cx.out_not_stack hgo hin hq
  · exact cx.out_not_stack hgo hin (fb_stack h (inRange_mono hq (by omega)))
  · rcases Nat.eq_zero_or_pos n with h0 | h0
    · subst h0; exact absurd hq (by unfold NativeRustcVm.InRange; omega)
    rw [inRange_toNat (by rw [toNat_off (by omega)]; omega), toNat_off (by omega),
      toNat_off (by omega)] at hq
    omega

/-- Frame bytes from `40` kept from `d` to `d'`. -/
structure FK (m0 d d' : MachineData) : Prop where
  keep : ∀ {o : Nat} {bs : List UInt8}, 40 ≤ o → o + bs.length ≤ 1408 →
    NativeRustcVm.BytesAt d.dmem (off (fb m0) o) bs →
      NativeRustcVm.BytesAt d'.dmem (off (fb m0) o) bs

/-- The `GkrStateW`'s bytes below `lo` kept from `d` to `d'`. -/
structure PK (m0 d d' : MachineData) (lo : Nat) : Prop where
  keep : ∀ {o : Nat} {bs : List UInt8}, o + bs.length ≤ lo →
    NativeRustcVm.BytesAt d.dmem (off (reg m0 .rcx) o) bs →
      NativeRustcVm.BytesAt d'.dmem (off (reg m0 .rcx) o) bs

omit [Labels] in
theorem FK.trans {d1 d2 d3 : MachineData} (h1 : FK m0 d1 d2) (h2 : FK m0 d2 d3) : FK m0 d1 d3 :=
  ⟨fun ho hob hb ↦ h2.keep ho hob (h1.keep ho hob hb)⟩

omit [Labels] in
theorem PK.trans {d1 d2 d3 : MachineData} {l1 l2 : Nat} (h1 : PK m0 d1 d2 l1)
    (h2 : PK m0 d2 d3 l2) : PK m0 d1 d3 (min l1 l2) :=
  ⟨fun hob hb ↦ h2.keep (by omega) (h1.keep (by omega) hb)⟩

/-- The callee-saved registers `gkr_step`'s tail keeps. -/
abbrev k5 : List Reg64 := [.rbx, .rbp, .r12, .r13, .r15]

omit [Labels] in
theorem cs5 {r : Reg64} (hr : r ∈ k5) : calleeSaved r = true := by
  simp only [k5, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl <;> rfl

omit [Labels] in
theorem k5_6 {r : Reg64} (hr : r ∈ k5) : r ∈ cs6 := by
  simp only [k5, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl <;> simp

/-- A word written by a block, given its value. -/
theorem wordAt_eq {env : Env} {S : SState} {m : MachineData} (hm : Match env S m) {r o : Nat}
    {b : BitVec 64} {sz : Nat} (hb : env.regions[r]? = some (b, sz)) (hle : o + 8 ≤ sz) {v : Sym}
    (hw : ∀ i < 8, findWrite r (o + i) S.mem = some (v, i)) {w : UInt64}
    (hv : v.eval env = w.toBitVec) : NativeRustcVm.WordAt m.dmem (off b o) w := by
  have e : UInt64.ofBitVec (v.eval env) = w := by rw [hv]
  rw [← e]
  exact wordAt_write hm hb hle hw

/-- `n` bytes of the `GkrStateW` at `lo` within it. -/
theorem pSub (h : GkrStepPre a s0 g0 m0) {lo n : Nat} (hle : lo + n ≤ 1064) {q : BitVec 64}
    (hq : NativeRustcVm.InRange (off (reg m0 .rcx) lo) n q) :
    NativeRustcVm.InRange (reg m0 .rcx) gkrStateBytes q := by
  have hnw : (reg m0 .rcx).toNat + 1064 ≤ 2 ^ 64 := (pre_gk h).2.1
  rcases Nat.eq_zero_or_pos n with h0 | h0
  · subst h0; exact absurd hq (by unfold NativeRustcVm.InRange; omega)
  rw [inRange_toNat (by rw [toNat_off (by omega)]; omega), toNat_off (by omega)] at hq
  show NativeRustcVm.InRange _ 1064 _
  rw [inRange_toNat (by omega)]
  omega

/-- A block's frame bytes from `40`, the `GkrStateW`'s bytes below its writes, the `TState`. -/
theorem blk (h : GkrStepPre a s0 g0 m0) {d d' : MachineData} {rest : List (BitVec 64 × Nat)}
    {ret : BitVec 64} {S : SState} (hwf : (frameEnv m0 d 1408 rest (fun _ ↦ 0) ret).WF)
    (hm : Match (frameEnv m0 d 1408 rest (fun _ ↦ 0) ret) S d')
    (hmid : MidOk 1408 40 slots S = true ∨ MidOk 1408 32 slots S = true)
    {ivs : List (Nat × Nat)} {lo hi : Nat} (hw : W01 S ivs lo hi = true)
    (hivs : ∀ p ∈ ivs, p.2 ≤ 40) (hlo : lo ≤ hi) (hhi : hi ≤ 1064)
    (hs : NativeRustcVm.SameOutside d.dmem d'.dmem (fun q ↦ NativeRustcVm.InRange (fb m0) 1360 q ∨
      NativeRustcVm.InRange (off (reg m0 .rcx) lo) (hi - lo) q))
    {s : TState} (hts : TStateAt d.dmem (reg m0 .rdi) a s) :
    FK m0 d d' ∧ PK m0 d d' lo ∧ TStateAt d'.dmem (reg m0 .rdi) a s := by
  refine ⟨⟨fun {o} {bs} ho hob hb ↦ keepB hwf hm (hmid.elim .inl fun h ↦ .inr (.inl h)) hob
    (fun w hw' hr ↦ ?_) hb⟩, ⟨fun hob hb ↦ pKeep h hs (lo := lo) (n := hi - lo) (by omega)
    (fun q hq ↦ hq.elim (fun h ↦ .inr (.inl h)) fun h ↦ .inr (.inr h)) (by omega) (.inl hob) hb⟩,
    tsKeep h (hm.kept hwf) hs (fun q hq ↦ hq.elim
      (fun hq ↦ .inl (fb_stack h (inRange_mono hq (by omega))))
      fun hq ↦ .inr (pSub h (by omega) hq)) hts⟩
  rcases W01_spec hw w hw' with ⟨-, q, hq, h1, h2⟩ | ⟨h1, -⟩
  · have := hivs q hq; omega
  · omega

omit [Labels] in
theorem c28f (x y : BitVec 64) (h : x.toNat + y.toNat ≤ 63) :
    (!CmpOp.apply .ult .W64 (BinOp.apply .add .W64 x y) (BitVec.ofNat 64 63) &&
      !CmpOp.apply .eq .W64 (BinOp.apply .add .W64 x y) (BitVec.ofNat 64 63)) = false := by
  have hs : (BinOp.apply .add .W64 x y).toNat = x.toNat + y.toNat := by
    simp only [BinOp.apply, low_W64, ext_W64, BitVec.toNat_add]
    exact Nat.mod_eq_of_lt (by omega)
  generalize BinOp.apply .add .W64 x y = z at hs ⊢
  by_cases he : z.toNat = 63
  · obtain rfl : z = 63#64 := BitVec.eq_of_toNat_eq he
    decide
  · have hu : z.ult (BitVec.ofNat 64 63) = true := by
      simp only [BitVec.ult, BitVec.toNat_ofNat, decide_eq_true_eq]
      omega
    simp only [CmpOp.apply, low_W64, hu, Bool.not_true, Bool.false_and]

omit [Labels] in
theorem add_word (x y : BitVec 64) {n : Nat} (h : x.toNat + y.toNat = n) :
    BinOp.apply .add .W64 x y = BitVec.ofNat 64 n := by
  apply BitVec.eq_of_toNat_eq
  simp only [BinOp.apply, low_W64, ext_W64, BitVec.toNat_add, BitVec.toNat_ofNat]
  rw [h]

omit [Labels] in
theorem load44 (x : BitVec 64) (h : x.toNat ≤ 1) :
    BitVec.ofInt 64 (Int.ofBytes ((List.range 4).map (byteOf x))) = x := by
  rcases (show x.toNat = 0 ∨ x.toNat = 1 by omega) with e | e
  · obtain rfl : x = 0#64 := BitVec.eq_of_toNat_eq e
    decide
  · obtain rfl : x = 1#64 := BitVec.eq_of_toNat_eq e
    decide

omit [Labels] in
theorem rdi21 (x l : BitVec 64) (hx : x.toNat = 1 ∨ x.toNat = 2) (hl : l.toNat ≤ 1) :
    (BinOp.apply .sub .W64 (BinOp.apply .shl .W64 x l) (BitVec.ofNat 64 1)).toNat ≤ 3 := by
  rcases (show l.toNat = 0 ∨ l.toNat = 1 by omega) with e | e
  · obtain rfl : l = 0#64 := BitVec.eq_of_toNat_eq e
    rcases hx with e' | e'
    · obtain rfl : x = 1#64 := BitVec.eq_of_toNat_eq e'; decide
    · obtain rfl : x = 2#64 := BitVec.eq_of_toNat_eq e'; decide
  · obtain rfl : l = 1#64 := BitVec.eq_of_toNat_eq e
    rcases hx with e' | e'
    · obtain rfl : x = 1#64 := BitVec.eq_of_toNat_eq e'; decide
    · obtain rfl : x = 2#64 := BitVec.eq_of_toNat_eq e'; decide

omit [Labels] in
theorem bits2_zero (x : BitVec 64) (h : x.toNat ≤ 2) :
    (if (!CmpOp.apply .ult .W32 x (BitVec.ofNat 64 3)) = true then
      BinOp.apply .sub .W32 x (BitVec.ofNat 64 3) else BitVec.ofNat 64 0) = 0#64 := by
  rcases (show x.toNat = 0 ∨ x.toNat = 1 ∨ x.toNat = 2 by omega) with e | e | e
  · obtain rfl : x = 0#64 := BitVec.eq_of_toNat_eq e; decide
  · obtain rfl : x = 1#64 := BitVec.eq_of_toNat_eq e; decide
  · obtain rfl : x = 2#64 := BitVec.eq_of_toNat_eq e; decide

/-- `n'` bytes of the frame at `o'` within `n` bytes at `o`. -/
theorem fb_sub (h : GkrStepPre a s0 g0 m0) {o n o' n' : Nat} (h1 : o ≤ o') (h2 : o' + n' ≤ o + n)
    (h3 : o + n ≤ 1408) {q : BitVec 64} (hq : NativeRustcVm.InRange (off (fb m0) o') n' q) :
    NativeRustcVm.InRange (off (fb m0) o) n q := by
  have hS := pre_stack h
  have hN := N_ge
  rcases Nat.eq_zero_or_pos n' with h0 | h0
  · subst h0; exact absurd hq (by unfold NativeRustcVm.InRange; omega)
  have e1 := hS.1
  have e2 := hS.2.1
  rw [inRange_toNat (by rw [fb_off_toNat hS hN (by omega)]; omega),
    fb_off_toNat hS hN (by omega)] at hq
  rw [inRange_toNat (by rw [fb_off_toNat hS hN (by omega)]; omega),
    fb_off_toNat hS hN (by omega)]
  omega

end

public section
variable [Host] {a : DecArea} {s0 : TState} {g0 : GkrStateW} {m0 : MachineData} {k : Nat}

/-- **The second grind and the coordinates** (`b21` to `b24`), from `AtTl`. -/
theorem ya_spec (hp : Placed code k) (h : GkrStepPre a s0 g0 m0)
    (hbl : Spec (Labels.label NativeRustcVmX64.Vm.BitLength.entryLabel) BitLengthPre BitLengthPost)
    (hgr : ∀ s, Spec (Labels.label NativeRustcVmX64.Vm.TStateGrind.entryLabel) (GrindPre a s) (GrindPost a s))
    (hsm : ∀ s, Spec (Labels.label NativeRustcVmX64.Vm.TStateSampleChallenges.entryLabel) (SampleChallengesPre a s)
      (SampleChallengesPost a s))
    {xs h0 h1 h2 : Array EW} {s3 : TState}
    (hy : ∀ y s' d, AtY a s0 g0 m0 xs h0 h1 h2 y s' d →
      Eventually (step1 Host.exe) (Goal a s0 g0 m0) ⟨d, Host.addrOf (k + NativeRustcVmX64.Vm.GkrStep.b25Offset)⟩)
    {d : MachineData} (at0 : AtTl a s0 g0 m0 xs h0 h1 h2 s3 d) :
    Eventually (step1 Host.exe) (Goal a s0 g0 m0) ⟨d, Host.addrOf (k + NativeRustcVmX64.Vm.GkrStep.b21Offset)⟩ := by
  have hS := pre_stack h
  have hN := N_ge
  have c32 := ctxF h (1408 - 32) (by omega)
  have hstep := pre_step h
  set t := reg m0 .rdi with ht
  have hxl : xs.toList.length ≤ 63 := by
    rw [Array.length_toList]; have := at0.size; unfold busPointCap at this; omega
  have l8 : ∀ w : UInt64, (NativeRustcVm.wordBytes w).length = 8 := NativeRustcVm.length_wordBytes
  have lE : ∀ xs : List EW, (xs.flatMap NativeRustcVm.ewBytes).length = 16 * xs.length :=
    NativeRustcVm.length_ewsBytes
  have E0 := lE h0.toList
  have E1 := lE h1.toList
  have E2 := lE h2.toList
  have EX := lE xs.toList
  have L0 : h0.toList.length ≤ 4 := by rw [Array.length_toList, at0.z0]; exact two_pow_le h
  have L1 : h1.toList.length ≤ 4 := by rw [Array.length_toList, at0.z1]; exact two_pow_le h
  have L2 : h2.toList.length ≤ 4 := by rw [Array.length_toList, at0.z2]; exact two_pow_le h
  -- `b21`: `bit_length((step << last) - 1)`.
  have hwf1 := wf0 h at0.fr.frame.kept (Host.addrOf (k + NativeRustcVmX64.Vm.GkrStep.b21Offset + b21.length)).toBitVec
  obtain ⟨hmid1, hw1, hdi1, hk1⟩ := ok_b21
  refine exec_then (infix_of b21_in_code (by simp [b21]) hp) exit_b21 hwf1 (fun _ _ ↦ rfl)
    (match_head at0.fr _) fun st1 hm1 hpc1 ↦ ?_
  obtain ⟨fr1, hs1⟩ := FR.block h at0.fr hwf1 hm1 hmid1 (.inl rfl) (W01_of_W0 hw1) (by decide)
    (by omega)
  obtain ⟨ts1, gs1⟩ := tsgs_keep h (hm1.kept hwf1) hs1 at0.ts at0.gs
  have kp1 : ∀ {o : Nat} {bs : List UInt8}, o + bs.length ≤ 1408 → (o + bs.length ≤ 32 ∨ 40 ≤ o) →
      NativeRustcVm.BytesAt d.dmem (off (fb m0) o) bs →
      NativeRustcVm.BytesAt st1.data.dmem (off (fb m0) o) bs := fun hle hd hb ↦
    keep3240 hwf1 hm1 hmid1 hw1 hle (fun p hp ↦ by simp at hp; subst hp; simp; omega) hb
  have k1 : ∀ r ∈ cs6, reg st1.data r = reg d r := fun r hr ↦ kr hm1 hk1 hr
  have hld : (Sym.load 0 44 4).eval (frameEnv m0 d 1408 [] (fun _ ↦ 0)
      (Host.addrOf (k + NativeRustcVmX64.Vm.GkrStep.b21Offset + b21.length)).toBitVec) = reg m0 .rdx := by
    show (frameEnv m0 d 1408 [] (fun _ ↦ 0) (Host.addrOf (k + NativeRustcVmX64.Vm.GkrStep.b21Offset + b21.length)).toBitVec).load
      0 44 4 = _
    rw [Env.load_of_bytesAt (env := frameEnv m0 d 1408 [] (fun _ ↦ 0)
      (Host.addrOf (k + NativeRustcVmX64.Vm.GkrStep.b21Offset + b21.length)).toBitVec) (r := 0) (off := 44)
      (bs := (List.range 4).map (byteOf (reg m0 .rdx))) (by simp) at0.l44]
    exact load44 _ (pre_last h)
  have hdi1' : (reg st1.data .rdi).toNat ≤ 3 := by
    rw [rv hm1 hdi1]
    show (BinOp.apply .sub .W64 (BinOp.apply .shl .W64 (reg d .rbx) _) (BitVec.ofNat 64 1)).toNat ≤ 3
    rw [hld, at0.rbx]
    exact rdi21 _ _ hstep (pre_last h)
  simp only [PcOk] at hpc1
  refine leaf h (X := bitLengthStack) (by simp) hbl (fun _ _ hq ↦ ⟨hq.2.1, hq.2.2⟩) fr1 hpc1
    (c32.stackOk (atC h (by omega) fr1) (le32 (by simp))) ts1 gs1
    fun m2 fr2 hq2 hcs2 kp2 ts2 gs2 ↦ ?_
  have hax2 : (reg m2 .rax).toNat ≤ 2 := by
    rw [hq2.1]; exact bitLength_small hdi1'
  -- `b22`: `grind(t, 0)`.
  have hwf3 := wf0 h fr2.frame.kept (Host.addrOf (k + NativeRustcVmX64.Vm.GkrStep.b22Offset + b22.length)).toBitVec
  obtain ⟨hmid3, hw3, hsi3, hdi3, hk3⟩ := ok_b22
  refine exec_at (st := ⟨m2, _⟩) (infix_of b22_in_code (by simp [b22]) hp) exit_b22 hwf3
    (fun _ _ ↦ rfl) (by show Host.addrOf (k + NativeRustcVmX64.Vm.GkrStep.b21Offset + b21.length) = _; rw [Nat.add_assoc]; exact congrArg (fun j ↦ Host.addrOf (k + j)) NativeRustcVmX64.Vm.GkrStep.b21_next)
    (match_head fr2 _) fun st3 hm3 hpc3 ↦ ?_
  obtain ⟨fr3, hs3⟩ := FR.block h fr2 hwf3 hm3 hmid3 (.inl rfl) (W01_of_W0 hw3) (by decide)
    (by omega)
  obtain ⟨ts3, gs3⟩ := tsgs_keep h (hm3.kept hwf3) hs3 ts2 gs2
  have kp3 : ∀ {o : Nat} {bs : List UInt8}, o + bs.length ≤ 1408 → (o + bs.length ≤ 32 ∨ 40 ≤ o) →
      NativeRustcVm.BytesAt m2.dmem (off (fb m0) o) bs →
      NativeRustcVm.BytesAt st3.data.dmem (off (fb m0) o) bs := fun hle hd hb ↦
    keep3240 hwf3 hm3 hmid3 hw3 hle (fun p hp ↦ by simp at hp; subst hp; simp; omega) hb
  have k3 : ∀ r ∈ cs6, reg st3.data r = reg d r := fun r hr ↦
    (kr hm3 hk3 hr).trans ((hcs2 r (by simp [cs6] at hr; rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> rfl)).trans (k1 r hr))
  have hbits : grindBits st3.data = 0 := by
    unfold grindBits
    rw [rv hm3 hsi3]
    show (if (!CmpOp.apply .ult .W32 (reg m2 .rax) (BitVec.ofNat 64 3)) = true then
      BinOp.apply .sub .W32 (reg m2 .rax) (BitVec.ofNat 64 3) else BitVec.ofNat 64 0).toNat %
        2 ^ 32 = 0
    rw [bits2_zero _ hax2]
    rfl
  have edi3 : reg st3.data .rdi = t := (rv hm3 hdi3).trans ((hcs2 .r15 rfl).trans
    ((k1 .r15 (by simp)).trans at0.r15))
  have hat3 := atC h (by omega) fr3
  have hle3 := le32 (X := grindStack) (by simp)
  simp only [PcOk] at hpc3
  refine Fr.call (c := 32) (Nc := grindStack) (lo := 40) (len := 0)
    (X := NativeRustcVm.InRange t tstateBytes) hS hN (by omega) hle3
    (slots_call (by omega) (by omega)) (by omega) (outs_not_frame h) (fun _ h ↦ .inl (.inl h))
    (hgr s3) fr3 hpc3 ⟨c32.stackOk hat3 hle3, c32.rcAt hat3 hle3,
      by rw [edi3]; exact ts3, by rw [edi3]; exact c32.tstateOk hat3 hle3,
      by rw [hbits]; decide, by
        rw [edi3]
        apply got_atC h (by omega) fr3 hle3
        intro l hl b hb
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
        rcases hb with rfl | rfl | rfl
        · exact ((pre_got h).1 l hl).2.2.2 _ (by simp [t])
        · exact ((pre_got h).1 l hl).2.2.2 _ (by simp)
        · exact ((pre_got h).1 l hl).2.2.2 _ (by simp)⟩
    (fun m' hq ↦ ⟨NativeRustcVm.SameOutside.mono hq.2.2.1 fun q hq ↦ by
      rw [edi3] at hq; exact hq.elim .inr .inl, hq.2.2.2⟩)
    fun m4 fr4 hq4 hs4 hcs4 ↦ ?_
  obtain ⟨hal4, hnx4, -, hsv4⟩ := hq4
  rw [hbits, grind_zero_run] at hal4 hnx4
  rw [edi3] at hnx4
  have ts4 : TStateAt m4.dmem t a s3 := hnx4 () s3 rfl
  have kp4 : ∀ {o : Nat} {bs : List UInt8}, 32 ≤ o → o + bs.length ≤ 1408 →
      NativeRustcVm.BytesAt st3.data.dmem (off (fb m0) o) bs →
      NativeRustcVm.BytesAt m4.dmem (off (fb m0) o) bs := fun ho hob hb ↦
    keepCall h fr3 hle3 hs4 ho hob (fun i hi hq ↦ fb_not_outs h (by omega) (.inl hq)) hb
  have k4 : ∀ r ∈ cs6, reg m4 r = reg d r := fun r hr ↦
    (hcs4 r (by simp [cs6] at hr; rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> rfl)).trans (k3 r hr)
  -- `b23`: the grind's result.
  have hwf5 := wf0 h fr4.frame.kept 0
  obtain ⟨hmid5, hmem5, hk5⟩ := ok_b10
  have hb23 : b23.IsInfixAt Host.prog (k + NativeRustcVmX64.Vm.GkrStep.b23Offset) := infix_of b23_in_code (by simp [b23]) hp
  refine exec_at (st := ⟨m4, _⟩) (b23_eq ▸ hb23) exit_b10 hwf5 nofun
    (by show Host.addrOf (k + NativeRustcVmX64.Vm.GkrStep.b22Offset + b22.length) = _; rw [Nat.add_assoc]; exact congrArg (fun j ↦ Host.addrOf (k + j)) NativeRustcVmX64.Vm.GkrStep.b22_next)
    (match_head fr4 0) fun st5 hm5 hpc5 ↦ ?_
  obtain ⟨fr5, hd5⟩ := FR.block_nil h fr4 hwf5 hm5 hmid5 hmem5
  have hc5 : SBool.eval (frameEnv m0 m4 1408 [] (fun _ ↦ 0) 0) cAl = false := testAl_okAl hal4
  simp only [PcOk, hc5, Bool.false_eq_true, ↓reduceIte] at hpc5
  have k5 : ∀ r ∈ cs6, reg st5.data r = reg d r := fun r hr ↦ (kr hm5 hk5 hr).trans (k4 r hr)
  -- `b24`: `sample_challenges(t, frame + 48, step)`.
  have hwf6 := wf0 h fr5.frame.kept (Host.addrOf (k + NativeRustcVmX64.Vm.GkrStep.b24Offset + b24.length)).toBitVec
  obtain ⟨hmid6, hw6, hdi6, hsi6, hdx6, hbp6, hk6⟩ := ok_b24
  refine exec_at (infix_of b24_in_code (by simp [b24]) hp) exit_b24 hwf6 (fun _ _ ↦ rfl)
    (hpc5.trans (by rw [← b23_eq, Nat.add_assoc, NativeRustcVmX64.Vm.GkrStep.b23_next])) (match_head fr5 _) fun st6 hm6 hpc6 ↦ ?_
  obtain ⟨fr6, hs6⟩ := FR.block h fr5 hwf6 hm6 hmid6 (.inl rfl) (W01_of_W0 hw6) (by decide)
    (by omega)
  have ts6 : TStateAt st6.data.dmem t a s3 :=
    have gs4 := gsKeep h hs4 (fun q hq ↦ hq.elim (fun hq ↦ .inl (calleeStack h (by omega) fr3 hle3 hq))
      .inr) gs3
    (tsgs_keep h (hm6.kept hwf6) hs6 (show TStateAt st5.data.dmem _ _ _ by rw [hd5]; exact ts4)
      (show GkrStateWAt st5.data.dmem _ _ by rw [hd5]; exact gs4)).1
  have kp6 : ∀ {o : Nat} {bs : List UInt8}, o + bs.length ≤ 1408 →
      (o + bs.length ≤ 32 ∨ (40 ≤ o ∧ o + bs.length ≤ 48) ∨ 80 ≤ o) →
      NativeRustcVm.BytesAt st5.data.dmem (off (fb m0) o) bs →
      NativeRustcVm.BytesAt st6.data.dmem (off (fb m0) o) bs := fun hle hd hb ↦
    keep3240 hwf6 hm6 hmid6 hw6 hle (fun p hp ↦ by
      simp at hp; rcases hp with rfl | rfl <;> simp <;> omega) hb
  have edi6 : reg st6.data .rdi = t := (rv hm6 hdi6).trans ((k5 .r15 (by simp)).trans at0.r15)
  have esi6 : reg st6.data .rsi = off (fb m0) 48 := (rv hm6 hsi6).trans (eval_ptr0 48)
  have edx6 : reg st6.data .rdx = reg m0 .rsi := (rv hm6 hdx6).trans ((k5 .rbx (by simp)).trans at0.rbx)
  have hat6 := atC h (by omega) fr6
  have hle6 := le32 (X := sampleChallengesStack) (by simp)
  have hsn : (reg m0 .rsi).toNat ≤ 2 := by rcases hstep with e | e <;> omega
  simp only [PcOk] at hpc6
  refine Fr.call (c := 32) (Nc := sampleChallengesStack) (lo := 48) (len := 32)
    (X := fun q ↦ NativeRustcVm.InRange (off (fb m0) 48) (16 * (reg m0 .rsi).toNat) q ∨
      NativeRustcVm.InRange t tstateBytes q)
    hS hN (by omega) hle6 (slots_call (by omega) (by omega)) (by omega) (outs_not_frame h)
    (fun q hq ↦ hq.elim (fun hq ↦ .inr (fb_sub h (by omega) (by omega) (by omega) hq))
      fun hq ↦ .inl (.inl hq))
    (hsm s3) fr6 hpc6 ?_ (fun m' hq ↦ ⟨?_, hq.2.2⟩) fun m7 fr7 hq7 hs7 hcs7 ↦ ?_
  · unfold SampleChallengesPre
    rw [edi6, esi6, edx6]
    refine ⟨c32.stackOk hat6 hle6, c32.rcAt hat6 hle6, ts6, c32.tstateOk hat6 hle6,
      outFb h fr6 hle6 (by omega) (by omega), got_atC h (by omega) fr6 hle6 ?_⟩
    intro l hl b hb
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · exact ((pre_got h).1 l hl).2.2.2 _ (by simp [t])
    · exact ((pre_got h).1 l hl).2.2.2 _ (by simp)
    · exact got_apart_frame (pre_got h) h.1 hl N_ge (by omega)
    · exact ((pre_got h).1 l hl).2.2.2 _ (by simp)
  · have := hq.2.1
    rw [edi6, esi6, edx6] at this
    exact NativeRustcVm.SameOutside.mono this fun q hq ↦ by
      rcases hq with hq | hq | hq
      · exact .inr (.inl hq)
      · exact .inr (.inr hq)
      · exact .inl hq
  obtain ⟨⟨y, s', hrun', hyw, hts'⟩, -, hsv7⟩ := hq7
  rw [edx6] at hrun'
  rw [esi6] at hyw
  rw [edi6] at hts'
  have hysz : y.size = (reg m0 .rsi).toNat := Gkr.sampleChallenges_size hrun'
  have kp7 : ∀ {o : Nat} {bs : List UInt8}, 32 ≤ o → o + bs.length ≤ 1408 →
      (o + bs.length ≤ 48 ∨ 80 ≤ o) →
      NativeRustcVm.BytesAt st6.data.dmem (off (fb m0) o) bs →
      NativeRustcVm.BytesAt m7.dmem (off (fb m0) o) bs := fun {o} {_} ho hob hd hb ↦
    keepCall h fr6 hle6 hs7 ho hob (fun i hi hq ↦ by
      rcases hq with hq | hq
      · exact fbo_apart h (o := 48) (n := 16 * (reg m0 .rsi).toNat) (o' := o + i) (n' := 1)
          (by omega) (by omega) (by omega) hq (NativeRustcVm.inRange_self (by omega))
      · exact fb_not_outs h (by omega) (.inl hq)) hb
  have k7 : ∀ r ∈ [Reg64.rbx, .r12, .r13, .r14, .r15], reg m7 r = reg d r := fun r hr ↦
    (hcs7 r (by simp at hr; rcases hr with rfl | rfl | rfl | rfl | rfl <;> rfl)).trans
      ((kr hm6 hk6 hr).trans (k5 r (by simp at hr; rcases hr with rfl | rfl | rfl | rfl | rfl <;> simp)))
  have thr : ∀ {o : Nat} {bs : List UInt8}, 80 ≤ o → o + bs.length ≤ 1408 →
      NativeRustcVm.BytesAt d.dmem (off (fb m0) o) bs →
      NativeRustcVm.BytesAt m7.dmem (off (fb m0) o) bs := fun ho hob hb ↦
    have h4 := kp4 (by omega) hob (kp3 hob (by omega) (kp2 (by omega) hob (kp1 hob (by omega) hb)))
    kp7 (by omega) hob (by omega) (kp6 hob (by omega) (by rw [hd5]; exact h4))
  refine hy y s' m7 ⟨fr7, ?_, ?_, ?_, ?_, ?_, thr (by omega) (by rw [l8]; omega) at0.pa,
    thr (by omega) (by rw [EX]; omega) at0.hxs, at0.size,
    thr (by omega) (by rw [E0]; omega) at0.k0, thr (by omega) (by rw [E1]; omega) at0.k1,
    thr (by omega) (by rw [E2]; omega) at0.k2, at0.z0, at0.z1, at0.z2, hyw, hysz, hts', ?_⟩
  · exact (k7 .rbx (by simp)).trans at0.rbx
  · rw [k7 .r12 (by simp)]; exact at0.r12
  · rw [k7 .r13 (by simp)]; exact at0.r13
  · exact (k7 .r14 (by simp)).trans at0.r14
  · exact (hcs7 .rbp rfl).trans ((rv hm6 hbp6).trans (eval_ptr0 48))
  · rw [at0.run, hrun']; rfl

/-- **A leaf call** from the frame at offset `32` (its changes in its stack only): the frame bytes
from `40`, the `GkrStateW`'s bytes and the `TState` kept. -/
theorem leafP (h : GkrStepPre a s0 g0 m0) {X : Nat}
    (hX : X ∈ [bitLengthStack, grindStack, squeezeStack, polyEvalStack, readScalarsStack,
      prodEStack, sampleChallengesStack, mleStack]) {l : Label} {P : MachineData → Prop}
    {Q : MachineData → MachineData → Prop} (hspec : Spec (Labels.label l) P Q)
    (hQ : ∀ m m', Q m m' → NativeRustcVm.SameOutside m.dmem m'.dmem
      (fun q ↦ NativeRustcVm.InRange (stackBelow m X) X q) ∧ Saved m m')
    {st : MachineState} {next : Int64} {R : MachineState → Prop} (fr : FR m0 32 st.data)
    (hpc : st.pc = Labels.label l ∧ retOf st.data = next) (hP : P st.data)
    {s : TState} (hts : TStateAt st.data.dmem (reg m0 .rdi) a s)
    (cont : ∀ m2 : MachineData, FR m0 40 m2 → Q st.data m2 →
      (∀ r, calleeSaved r = true → reg m2 r = reg st.data r) → FK m0 st.data m2 →
      PK m0 st.data m2 1064 → TStateAt m2.dmem (reg m0 .rdi) a s →
      Eventually (step1 Host.exe) R ⟨m2, next⟩) :
    Eventually (step1 Host.exe) R st := by
  have hle := le32 hX
  refine Fr.call (c := 32) (Nc := X) (lo := 40) (len := 0) (X := fun _ ↦ False)
    (pre_stack h) N_ge (by omega) hle (slots_call (by omega) (by omega)) (by omega)
    (outs_not_frame h) (fun _ h ↦ h.elim) hspec fr hpc hP
    (fun m' hq ↦ ⟨NativeRustcVm.SameOutside.mono (hQ _ _ hq).1 fun _ h ↦ .inl h, (hQ _ _ hq).2⟩)
    fun m2 fr2 hq hs hcs ↦ ?_
  have hcal : ∀ q, (NativeRustcVm.InRange (stackBelow st.data X) X q ∨ False) →
      NativeRustcVm.InRange (stackBelow m0 gkrStepStack) gkrStepStack q :=
    fun q hq ↦ hq.elim (fun hq ↦ calleeStack h (by omega) fr hle hq) False.elim
  exact cont m2 fr2 hq hcs ⟨fun ho hob hb ↦ keepCall h fr hle hs (by omega) hob (fun _ _ h ↦ h) hb⟩
    ⟨fun hob hb ↦ pKeep h hs (lo := 0) (n := 0) (by omega) (fun q hq ↦ .inl (hcal q hq))
      (by omega) (.inr (by omega)) hb⟩
    (tsKeep h (hQ _ _ hq).2.2 hs (fun q hq ↦ .inl (hcal q hq)) hts)

/-- `multilinear_eval_by`'s precondition: a child of `2^step` elements at `o` of the frame, the
coordinates `y` (`step` of them) at `48`. -/
theorem mlePre (h : GkrStepPre a s0 g0 m0) {d : MachineData} (fr : FR m0 32 d) {o : Nat}
    (ho : 40 ≤ o) (ho' : o + 64 ≤ 1408) (hdi : (reg d .rdi).toNat = 2 ^ (reg m0 .rsi).toNat)
    (hdx : reg d .rdx = reg d .rdi) (hsi : reg d .rsi = off (fb m0) o)
    (hcx : reg d .rcx = off (fb m0) 48) (hr8 : reg d .r8 = reg m0 .rsi) :
    MleOfMultilinearEvalPre d := by
  have hle := le32 (X := mleStack) (by simp)
  have c32 := ctxF h (1408 - 32) (by omega)
  have hn := two_pow_le h
  have hst := pre_step h
  have hout := outFb h fr hle (o := o) (n := 16 * 2 ^ (reg m0 .rsi).toNat) (by omega) (by omega)
  have hout' := outFb h fr hle (o := 48) (n := 16 * (reg m0 .rsi).toNat) (by omega) (by omega)
  unfold MleOfMultilinearEvalPre SliceOk Readable OffStack
  rw [hsi, hcx, hr8, hdx, hdi]
  exact ⟨c32.stackOk (atC h (by omega) fr) hle, rfl, by omega, ⟨⟨hout.1, hout.2.1⟩,
    hout.2.2.2.2.1⟩, ⟨hout'.1, hout'.2.1⟩, hout'.2.2.2.2.1⟩

/-- **The new values and the point's start** (`b25` to `b30`), from `AtY`. -/
theorem mv_spec (hp : Placed code k) (h : GkrStepPre a s0 g0 m0)
    (hmle : Spec (Labels.label NativeRustcVmX64.Vm.MultilinearEvalByOfMultilinearEval.entryLabel) MleOfMultilinearEvalPre
      MleOfMultilinearEvalPost)
    {xs h0 h1 h2 y : Array EW} {s' : TState}
    (hcp : ∀ d, AtCp a s0 g0 m0 xs y #[multilinearEval h0 y, multilinearEval h1 y,
      multilinearEval h2 y] s' d →
      Eventually (step1 Host.exe) (Goal a s0 g0 m0) ⟨d, Host.addrOf (k + NativeRustcVmX64.Vm.GkrStep.b31Offset)⟩)
    {d : MachineData} (at0 : AtY a s0 g0 m0 xs h0 h1 h2 y s' d) :
    Eventually (step1 Host.exe) (Goal a s0 g0 m0) ⟨d, Host.addrOf (k + NativeRustcVmX64.Vm.GkrStep.b25Offset)⟩ := by
  have hstep := pre_step h
  have lE : ∀ xs : List EW, (xs.flatMap NativeRustcVm.ewBytes).length = 16 * xs.length :=
    NativeRustcVm.length_ewsBytes
  have E0 := lE h0.toList
  have E1 := lE h1.toList
  have E2 := lE h2.toList
  have EY := lE y.toList
  have L0 : h0.toList.length ≤ 4 := by rw [Array.length_toList, at0.z0]; exact two_pow_le h
  have L1 : h1.toList.length ≤ 4 := by rw [Array.length_toList, at0.z1]; exact two_pow_le h
  have L2 : h2.toList.length ≤ 4 := by rw [Array.length_toList, at0.z2]; exact two_pow_le h
  have LY : y.toList.length ≤ 2 := by rw [Array.length_toList, at0.ysz]; omega
  have ep : ∀ {dd : MachineData} {ret : BitVec 64},
      (Sym.ptr 1 0).eval (frameEnv m0 dd 1408 [(reg m0 .rcx, 1064)] (fun _ ↦ 0) ret) =
        reg m0 .rcx := eval_ptr rfl
  -- `b25`: the first child's evaluation at `y`.
  have hwf1 := wf0 h at0.fr.frame.kept (Host.addrOf (k + NativeRustcVmX64.Vm.GkrStep.b25Offset + b25.length)).toBitVec
  obtain ⟨hmid1, hw1, hdi1, hsi1, hdx1, hcx1, hr81, hk1⟩ := ok_b25
  refine exec_then (infix_of b25_in_code (by simp [b25]) hp) exit_b25 hwf1 (fun _ _ ↦ rfl)
    (match_head at0.fr _) fun st1 hm1 hpc1 ↦ ?_
  obtain ⟨fr1, hs1⟩ := FR.block h at0.fr hwf1 hm1 hmid1 (.inl rfl) (W01_of_W0 hw1) (by decide)
    (by omega)
  obtain ⟨F1, -, ts1⟩ := blk h hwf1 hm1 (.inr hmid1) (W01_of_W0 hw1) (by decide) (by omega)
    (by omega) hs1 at0.ts
  have R1 : ∀ r ∈ k5, reg st1.data r = reg d r := fun r hr ↦ kr hm1 hk1 (k5_6 hr)
  have edi1 : reg st1.data .rdi = reg d .r12 := rv hm1 hdi1
  have esi1 : reg st1.data .rsi = off (fb m0) 112 := (rv hm1 hsi1).trans (eval_ptr0 112)
  have edx1 : reg st1.data .rdx = reg d .r12 := rv hm1 hdx1
  have ecx1 : reg st1.data .rcx = off (fb m0) 48 := (rv hm1 hcx1).trans at0.rbp
  have er81 : reg st1.data .r8 = reg m0 .rsi := (rv hm1 hr81).trans at0.rbx
  simp only [PcOk] at hpc1
  refine leafP h (X := mleStack) (by simp) hmle (fun _ _ hq ↦ ⟨changesQ hq.2.1, hq.2.2⟩) fr1
    hpc1 (mlePre h fr1 (o := 112) (by omega) (by omega) (by rw [edi1]; exact at0.r12)
      (edx1.trans edi1.symm) esi1 ecx1 er81) ts1 fun m2 fr2 hq2 hcs2 F2 P2 ts2 ↦ ?_
  have hv0 : ewRet m2 = multilinearEval h0 y := by
    rw [hq2.1, esi1, ecx1, er81, edx1, slice_fb (F1.keep (by omega) (by rw [E0]; omega) at0.k0)
      (at0.r12.trans at0.z0.symm), slice_fb (F1.keep (by omega) (by rw [EY]; omega) at0.yw)
      at0.ysz.symm]
  have R2 : ∀ r ∈ k5, reg m2 r = reg d r := fun r hr ↦ (hcs2 r (cs5 hr)).trans (R1 r hr)
  have e14 : reg m2 .r14 = reg m0 .rcx :=
    (hcs2 .r14 rfl).trans ((kr hm1 hk1 (by simp)).trans at0.r14)
  -- `b26`: the first value; the second child's evaluation.
  have hwf3 := wfS h fr2.frame.kept (Host.addrOf (k + NativeRustcVmX64.Vm.GkrStep.b26Offset + b26.length)).toBitVec
  obtain ⟨hmid3, hw3, w0, w8, hdi3, hsi3, hdx3, hcx3, hr83, h143, hk3⟩ := ok_b26
  refine exec_at (st := ⟨m2, _⟩) (infix_of b26_in_code (by simp [b26]) hp) exit_b26 hwf3
    (fun _ _ ↦ rfl)
    (by show Host.addrOf (k + NativeRustcVmX64.Vm.GkrStep.b25Offset + b25.length) = _; rw [Nat.add_assoc]; exact congrArg (fun j ↦ Host.addrOf (k + j)) NativeRustcVmX64.Vm.GkrStep.b25_next)
    (match_sS fr2 e14 _) fun st3 hm3 hpc3 ↦ ?_
  obtain ⟨fr3, hs3⟩ := FR.block h fr2 hwf3 hm3 hmid3 (.inr rfl) hw3 (by decide) (by omega)
  obtain ⟨F3, P3, ts3⟩ := blk h hwf3 hm3 (.inr hmid3) hw3 (by decide) (by omega) (by omega) hs3 ts2
  have V0 : NativeRustcVm.WordAt st3.data.dmem (off (reg m0 .rcx) 0) (multilinearEval h0 y).c0 :=
    wordAt_eq hm3 (r := 1) (sz := 1064) rfl (by omega) w0 (by
      show reg m2 .rax = _; rw [← hv0]; rfl)
  have V8 : NativeRustcVm.WordAt st3.data.dmem (off (reg m0 .rcx) 8) (multilinearEval h0 y).c1 :=
    wordAt_eq hm3 (r := 1) (sz := 1064) rfl (by omega) w8 (by
      show reg m2 .rdx = _; rw [← hv0]; rfl)
  have R3 : ∀ r ∈ k5, reg st3.data r = reg d r := fun r hr ↦ (kr hm3 hk3 hr).trans (R2 r hr)
  have F13 := (F1.trans F2).trans F3
  have edi3 : reg st3.data .rdi = reg d .r12 := (rv hm3 hdi3).trans (R2 .r12 (by simp))
  have esi3 : reg st3.data .rsi = off (fb m0) 176 := (rv hm3 hsi3).trans (eval_ptr0 176)
  have edx3 : reg st3.data .rdx = reg d .r12 := (rv hm3 hdx3).trans (R2 .r12 (by simp))
  have ecx3 : reg st3.data .rcx = off (fb m0) 48 :=
    (rv hm3 hcx3).trans ((R2 .rbp (by simp)).trans at0.rbp)
  have er83 : reg st3.data .r8 = reg m0 .rsi :=
    (rv hm3 hr83).trans ((R2 .rbx (by simp)).trans at0.rbx)
  have e143 : reg st3.data .r14 = reg m0 .rcx := (rv hm3 h143).trans ep
  simp only [PcOk] at hpc3
  refine leafP h (X := mleStack) (by simp) hmle (fun _ _ hq ↦ ⟨changesQ hq.2.1, hq.2.2⟩) fr3
    hpc3 (mlePre h fr3 (o := 176) (by omega) (by omega) (by rw [edi3]; exact at0.r12)
      (edx3.trans edi3.symm) esi3 ecx3 er83) ts3 fun m4 fr4 hq4 hcs4 F4 P4 ts4 ↦ ?_
  have hv1 : ewRet m4 = multilinearEval h1 y := by
    rw [hq4.1, esi3, ecx3, er83, edx3, slice_fb (F13.keep (by omega) (by rw [E1]; omega) at0.k1)
      (at0.r12.trans at0.z1.symm), slice_fb (F13.keep (by omega) (by rw [EY]; omega) at0.yw)
      at0.ysz.symm]
  have R4 : ∀ r ∈ k5, reg m4 r = reg d r := fun r hr ↦ (hcs4 r (cs5 hr)).trans (R3 r hr)
  have e144 : reg m4 .r14 = reg m0 .rcx := (hcs4 .r14 rfl).trans e143
  -- `b27`: the second value; the third child's evaluation.
  have hwf5 := wfS h fr4.frame.kept (Host.addrOf (k + NativeRustcVmX64.Vm.GkrStep.b27Offset + b27.length)).toBitVec
  obtain ⟨hmid5, hw5, w16, w24, hdi5, hsi5, hdx5, hcx5, hr85, h145, hk5⟩ := ok_b27
  refine exec_at (st := ⟨m4, _⟩) (infix_of b27_in_code (by simp [b27]) hp) exit_b27 hwf5
    (fun _ _ ↦ rfl)
    (by show Host.addrOf (k + NativeRustcVmX64.Vm.GkrStep.b26Offset + b26.length) = _; rw [Nat.add_assoc]; exact congrArg (fun j ↦ Host.addrOf (k + j)) NativeRustcVmX64.Vm.GkrStep.b26_next)
    (match_sS fr4 e144 _) fun st5 hm5 hpc5 ↦ ?_
  obtain ⟨fr5, hs5⟩ := FR.block h fr4 hwf5 hm5 hmid5 (.inr rfl) hw5 (by decide) (by omega)
  obtain ⟨F5, P5, ts5⟩ := blk h hwf5 hm5 (.inr hmid5) hw5 (by decide) (by omega) (by omega) hs5 ts4
  have V16 : NativeRustcVm.WordAt st5.data.dmem (off (reg m0 .rcx) 16) (multilinearEval h1 y).c0 :=
    wordAt_eq hm5 (r := 1) (sz := 1064) rfl (by omega) w16 (by
      show reg m4 .rax = _; rw [← hv1]; rfl)
  have V24 : NativeRustcVm.WordAt st5.data.dmem (off (reg m0 .rcx) 24) (multilinearEval h1 y).c1 :=
    wordAt_eq hm5 (r := 1) (sz := 1064) rfl (by omega) w24 (by
      show reg m4 .rdx = _; rw [← hv1]; rfl)
  have R5 : ∀ r ∈ k5, reg st5.data r = reg d r := fun r hr ↦ (kr hm5 hk5 hr).trans (R4 r hr)
  have F15 := ((F13.trans F4).trans F5)
  have edi5 : reg st5.data .rdi = reg d .r12 := (rv hm5 hdi5).trans (R4 .r12 (by simp))
  have esi5 : reg st5.data .rsi = off (fb m0) 240 := (rv hm5 hsi5).trans (eval_ptr0 240)
  have edx5 : reg st5.data .rdx = reg d .r12 := (rv hm5 hdx5).trans (R4 .r12 (by simp))
  have ecx5 : reg st5.data .rcx = off (fb m0) 48 :=
    (rv hm5 hcx5).trans ((R4 .rbp (by simp)).trans at0.rbp)
  have er85 : reg st5.data .r8 = reg m0 .rsi :=
    (rv hm5 hr85).trans ((R4 .rbx (by simp)).trans at0.rbx)
  have e145 : reg st5.data .r14 = reg m0 .rcx := (rv hm5 h145).trans ep
  simp only [PcOk] at hpc5
  refine leafP h (X := mleStack) (by simp) hmle (fun _ _ hq ↦ ⟨changesQ hq.2.1, hq.2.2⟩) fr5
    hpc5 (mlePre h fr5 (o := 240) (by omega) (by omega) (by rw [edi5]; exact at0.r12)
      (edx5.trans edi5.symm) esi5 ecx5 er85) ts5 fun m6 fr6 hq6 hcs6 F6 P6 ts6 ↦ ?_
  have hv2 : ewRet m6 = multilinearEval h2 y := by
    rw [hq6.1, esi5, ecx5, er85, edx5, slice_fb (F15.keep (by omega) (by rw [E2]; omega) at0.k2)
      (at0.r12.trans at0.z2.symm), slice_fb (F15.keep (by omega) (by rw [EY]; omega) at0.yw)
      at0.ysz.symm]
  have R6 : ∀ r ∈ k5, reg m6 r = reg d r := fun r hr ↦ (hcs6 r (cs5 hr)).trans (R5 r hr)
  have e146 : reg m6 .r14 = reg m0 .rcx := (hcs6 .r14 rfl).trans e145
  -- `b28`: the third value; the point's room.
  have hwf7 := wfS h fr6.frame.kept 0
  obtain ⟨hmid7, hw7, w32, w40, hax7, h147, hk7⟩ := ok_b28
  refine exec_at (st := ⟨m6, _⟩) (infix_of b28_in_code (by simp [b28]) hp) exit_b28 hwf7 nofun
    (by show Host.addrOf (k + NativeRustcVmX64.Vm.GkrStep.b27Offset + b27.length) = _; rw [Nat.add_assoc]; exact congrArg (fun j ↦ Host.addrOf (k + j)) NativeRustcVmX64.Vm.GkrStep.b27_next)
    (match_sS fr6 e146 _) fun st7 hm7 hpc7 ↦ ?_
  obtain ⟨fr7, hs7⟩ := FR.block h fr6 hwf7 hm7 hmid7 (.inr rfl) hw7 (by decide) (by omega)
  obtain ⟨F7, P7, ts7⟩ := blk h hwf7 hm7 (.inl hmid7) hw7 (by decide) (by omega) (by omega) hs7 ts6
  have V32 : NativeRustcVm.WordAt st7.data.dmem (off (reg m0 .rcx) 32) (multilinearEval h2 y).c0 :=
    wordAt_eq hm7 (r := 1) (sz := 1064) rfl (by omega) w32 (by
      show reg m6 .rax = _; rw [← hv2]; rfl)
  have V40 : NativeRustcVm.WordAt st7.data.dmem (off (reg m0 .rcx) 40) (multilinearEval h2 y).c1 :=
    wordAt_eq hm7 (r := 1) (sz := 1064) rfl (by omega) w40 (by
      show reg m6 .rdx = _; rw [← hv2]; rfl)
  have R7 : ∀ r ∈ k5, reg st7.data r = reg d r := fun r hr ↦ (kr hm7 hk7 hr).trans (R6 r hr)
  have e147 : reg st7.data .r14 = reg m0 .rcx := (rv hm7 h147).trans ep
  have hsum : (reg m6 .rbx).toNat + (reg m6 .r13).toNat = y.size + xs.size := by
    rw [R6 .rbx (by simp), R6 .r13 (by simp), at0.rbx, at0.r13, at0.ysz]
  have hcap := at0.size
  have hysz := at0.ysz
  unfold busPointCap at hcap
  have hc7 : SBool.eval (frameEnv m0 m6 1408 [(reg m0 .rcx, 1064)] (fun _ ↦ 0) 0) c28 = false :=
    c28f (reg m6 .rbx) (reg m6 .r13) (by omega)
  simp only [PcOk, hc7, Bool.false_eq_true, ↓reduceIte] at hpc7
  have hax7' : reg st7.data .rax = BitVec.ofNat 64 (y.size + xs.size) :=
    (rv hm7 hax7).trans (add_word _ _ hsum)
  -- `b29`: the point's length and first coordinate.
  have yw7 := (((F15.trans F6).trans F7).keep (by omega) (by rw [EY]; omega) at0.yw)
  have hwf8 := wfS h fr7.frame.kept 0
  obtain ⟨hmid8, hw8, w48, w56, w64, h148, hk8⟩ := ok_b29
  refine exec_at (infix_of b29_in_code (by simp [b29]) hp) exit_b29 hwf8 nofun
    (hpc7.trans (by rw [Nat.add_assoc]; exact congrArg (fun j ↦ Host.addrOf (k + j)) NativeRustcVmX64.Vm.GkrStep.b28_next)) (match_sS fr7 e147 _)
    fun st8 hm8 hpc8 ↦ ?_
  obtain ⟨fr8, hs8⟩ := FR.block h fr7 hwf8 hm8 hmid8 (.inr rfl) hw8 (by decide) (by omega)
  obtain ⟨F8, P8, ts8⟩ := blk h hwf8 hm8 (.inl hmid8) hw8 (by decide) (by omega) (by omega) hs8 ts7
  have V48 : NativeRustcVm.WordAt st8.data.dmem (off (reg m0 .rcx) 48)
      (y.size + xs.size).toUInt64 :=
    wordAt_eq hm8 (r := 1) (sz := 1064) rfl (by omega) w48 hax7'
  have R8 : ∀ r ∈ k5, reg st8.data r = reg d r := fun r hr ↦ (kr hm8 hk8 hr).trans (R7 r hr)
  have e148 : reg st8.data .r14 = reg m0 .rcx := (rv hm8 h148).trans ep
  have hc8 : SBool.eval (frameEnv m0 st7.data 1408 [(reg m0 .rcx, 1064)] (fun _ ↦ 0) 0)
      (.cmp .eq .W64 (.reg .rbx) (.lit 1)) = decide ((reg m0 .rsi).toNat = 1) := by
    show CmpOp.apply .eq .W64 (reg st7.data .rbx) (BitVec.ofNat 64 1) = _
    rw [R7 .rbx (by simp), at0.rbx]
    simp only [CmpOp.apply, low_W64]
    by_cases e : (reg m0 .rsi).toNat = 1
    · rw [show reg m0 .rsi = 1#64 from BitVec.eq_of_toNat_eq e]
      decide
    · simp only [e, decide_false, beq_eq_false_iff_ne, ne_eq]
      exact fun h' ↦ e (by rw [h']; rfl)
  simp only [PcOk, hc8] at hpc8
  have hy : y.toList.length = (reg m0 .rsi).toNat := by rw [Array.length_toList, at0.ysz]
  -- the first coordinate's words, copied
  obtain ⟨y0, yr, hyl⟩ : ∃ y0 yr, y.toList = y0 :: yr := by
    rcases hq : y.toList with _ | ⟨y0, yr⟩
    · rw [hq] at hy; simp at hy; omega
    · exact ⟨y0, yr, rfl⟩
  rw [hyl] at yw7
  obtain ⟨hy0, hyr⟩ := ewsAt_cons.mp yw7
  obtain ⟨y00, y01⟩ := ewAt_iff.mp hy0
  rw [off_off] at y01
  have V56 : NativeRustcVm.WordAt st8.data.dmem (off (reg m0 .rcx) 56) y0.c0 :=
    wordAt_eq hm8 (r := 1) (sz := 1064) rfl (by omega) w56
      (load_ofMachine (rs := [(stackBelow m0 1408, 1408 + 8), (reg m0 .rcx, 1064)]) (r := 0)
        (o := 48) rfl y00)
  have V64 : NativeRustcVm.WordAt st8.data.dmem (off (reg m0 .rcx) 64) y0.c1 :=
    wordAt_eq hm8 (r := 1) (sz := 1064) rfl (by omega) w64
      (load_ofMachine (rs := [(stackBelow m0 1408, 1408 + 8), (reg m0 .rcx, 1064)]) (r := 0)
        (o := 56) rfl y01)
  have FA := ((F15.trans F6).trans F7).trans F8
  have PV0 := ((((P4.trans P5).trans P6).trans P7).trans P8)
  have PV16 := ((P6.trans P7).trans P8)
  have PV32 := P8
  have hvs : NativeRustcVm.EWsAt st8.data.dmem (reg m0 .rcx) [multilinearEval h0 y,
      multilinearEval h1 y, multilinearEval h2 y] :=
    ews3' (PV0.keep (by rw [NativeRustcVm.length_wordBytes]; omega) V0)
      (PV0.keep (by rw [NativeRustcVm.length_wordBytes]; omega) V8)
      (PV16.keep (by rw [NativeRustcVm.length_wordBytes]; omega) V16)
      (PV16.keep (by rw [NativeRustcVm.length_wordBytes]; omega) V24)
      (PV32.keep (by rw [NativeRustcVm.length_wordBytes]; omega) V32)
      (PV32.keep (by rw [NativeRustcVm.length_wordBytes]) V40)
  by_cases e1 : (reg m0 .rsi).toNat = 1
  · simp only [e1, decide_true, ↓reduceIte] at hpc8
    have hyr0 : yr = [] := by
      rw [hyl] at hy; simp only [List.length_cons] at hy
      exact List.eq_nil_of_length_eq_zero (by omega)
    subst hyr0
    refine at_pc (hpc8.trans (hp.label NativeRustcVmX64.Vm.GkrStep.label_13_at)) (hcp _ ⟨fr8, ?_, ?_, e148,
      FA.keep (by omega) (by rw [NativeRustcVm.length_wordBytes]; omega) at0.pa,
      FA.keep (by omega) (by rw [lE, Array.length_toList]; have := at0.size; unfold busPointCap at this; omega) at0.hxs,
      at0.size, at0.ysz, rfl, hvs, V48, ?_, ts8, at0.run⟩)
    · exact (R8 .rbx (by simp)).trans at0.rbx
    · rw [R8 .r13 (by simp)]; exact at0.r13
    · rw [hyl]
      exact ewsAt_cons.mpr ⟨ewAt_iff.mpr ⟨V56, by rw [off_off]; exact V64⟩, ewsAt_nil _ _⟩
  · simp only [e1, decide_false, Bool.false_eq_true, ↓reduceIte] at hpc8
    -- `b30`: the second coordinate.
    obtain ⟨y1, hyr1⟩ : ∃ y1, yr = [y1] := by
      rw [hyl] at hy
      rcases yr with _ | ⟨y1, _ | ⟨y2, yr⟩⟩
      · simp at hy; omega
      · exact ⟨y1, rfl⟩
      · simp at hy; omega
    subst hyr1
    obtain ⟨hy1, -⟩ := ewsAt_cons.mp hyr
    obtain ⟨y10, y11⟩ := ewAt_iff.mp hy1
    rw [off_off] at y10
    rw [off_off, off_off] at y11
    have hwf9 := wfS h fr8.frame.kept 0
    obtain ⟨hmid9, hw9, w72, w80, h149, hk9⟩ := ok_b30
    refine exec_at (infix_of b30_in_code (by simp [b30]) hp) exit_b30 hwf9 nofun
      (hpc8.trans (by rw [Nat.add_assoc]; exact congrArg (fun j ↦ Host.addrOf (k + j)) NativeRustcVmX64.Vm.GkrStep.b29_next)) (match_sS fr8 e148 _)
      fun st9 hm9 hpc9 ↦ ?_
    obtain ⟨fr9, hs9⟩ := FR.block h fr8 hwf9 hm9 hmid9 (.inr rfl) hw9 (by decide) (by omega)
    obtain ⟨F9, P9, ts9⟩ := blk h hwf9 hm9 (.inl hmid9) hw9 (by decide) (by omega) (by omega)
      hs9 ts8
    have V72 : NativeRustcVm.WordAt st9.data.dmem (off (reg m0 .rcx) 72) y1.c0 :=
      wordAt_eq hm9 (r := 1) (sz := 1064) rfl (by omega) w72
        (load_ofMachine (rs := [(stackBelow m0 1408, 1408 + 8), (reg m0 .rcx, 1064)]) (r := 0)
          (o := 64) rfl (F8.keep (by omega) (by rw [NativeRustcVm.length_wordBytes]; omega) y10))
    have V80 : NativeRustcVm.WordAt st9.data.dmem (off (reg m0 .rcx) 80) y1.c1 :=
      wordAt_eq hm9 (r := 1) (sz := 1064) rfl (by omega) w80
        (load_ofMachine (rs := [(stackBelow m0 1408, 1408 + 8), (reg m0 .rcx, 1064)]) (r := 0)
          (o := 72) rfl (F8.keep (by omega) (by rw [NativeRustcVm.length_wordBytes]; omega) y11))
    have kw : ∀ {o : Nat} {w : UInt64}, o + 8 ≤ 72 →
        NativeRustcVm.WordAt st8.data.dmem (off (reg m0 .rcx) o) w →
        NativeRustcVm.WordAt st9.data.dmem (off (reg m0 .rcx) o) w := fun ho hw ↦
      P9.keep (by rw [NativeRustcVm.length_wordBytes]; omega) hw
    refine at_pc (hpc9.trans (by rw [Nat.add_assoc]; exact congrArg (fun j ↦ Host.addrOf (k + j)) NativeRustcVmX64.Vm.GkrStep.b30_next)) (hcp _ ⟨fr9, ?_, ?_,
      (rv hm9 h149).trans ep,
      (FA.trans F9).keep (by omega) (by rw [NativeRustcVm.length_wordBytes]; omega) at0.pa,
      (FA.trans F9).keep (by omega) (by rw [lE, Array.length_toList]; have := at0.size; unfold busPointCap at this; omega) at0.hxs,
      at0.size, at0.ysz, rfl, ?_, kw (by omega) V48, ?_, ts9, at0.run⟩)
    · exact ((kr hm9 hk9 (by simp)).trans (R8 .rbx (by simp))).trans at0.rbx
    · rw [kr hm9 hk9 (by simp), R8 .r13 (by simp)]; exact at0.r13
    · have hvs0 : NativeRustcVm.EWsAt st8.data.dmem (off (reg m0 .rcx) 0) [multilinearEval h0 y,
          multilinearEval h1 y, multilinearEval h2 y] := by rw [off_zero]; exact hvs
      have := P9.keep (o := 0) (bs := [multilinearEval h0 y, multilinearEval h1 y,
        multilinearEval h2 y].flatMap NativeRustcVm.ewBytes) (by rw [lE]; simp) hvs0
      rwa [off_zero] at this
    · rw [hyl]
      exact ewsAt_cons.mpr ⟨ewAt_iff.mpr ⟨kw (by omega) V56, by rw [off_off]; exact kw (by omega) V64⟩,
        ewsAt_cons.mpr ⟨ewAt_iff.mpr ⟨by rw [off_off]; exact V72, by rw [off_off, off_off]; exact V80⟩,
          ewsAt_nil _ _⟩⟩

end

end NativeRustcVmX64.Bus.GkrStep
