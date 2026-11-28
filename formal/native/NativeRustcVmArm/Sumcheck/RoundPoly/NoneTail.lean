module

public import NativeRustcVmArm.Code.Vm.BitLength.Names
public import NativeRustcVmArm.Code.Vm.TStateGrind.Names
public import NativeRustcVmArm.Code.Vm.TStateSumcheckRoundPoly.Names
public import NativeRustcVmArm.Sumcheck.RoundPoly.SomeTail

/-!
# `sumcheck_round_poly` in plain mode, after the tail is read

The constant `p0` in `msg[0]`; from `.L` after `read_scalars` (`b12`, `none_b12`): a rejection,
or the tail's sum (`sum_e`, `b13`); from `b14` (`none_b14`): the grind's bits (`bit_length`), the
grind (`b15`), its test (`b16`), the derived coefficient into `msg[1]` (`b17`).
-/

namespace NativeRustcVmArm.Sumcheck.RoundPoly

open NativeRustcArm NativeRustcArm.Sym NativeRustcVmArm.Vm.TStateSumcheckRoundPoly
open NativeVm.Model NativeRustcVm.Transcript NativeRustcVm.Sumcheck

@[expose] public section

/-- The registers `sumcheck_round_poly` keeps in plain mode, after the constant. -/
structure NoneRegs (m0 : MachineData) (m : MachineData) : Prop where
  x19 : m.regs.getXReg .X19 = m0.regs.X5
  x20 : m.regs.getXReg .X20 = m0.regs.X3
  x21 : m.regs.getXReg .X21 = m0.regs.X2
  x22 : m.regs.getXReg .X22 = m0.regs.X0
  x23 : (m.regs.getXReg .X23).toNat = cnt m0 - 2

/-- The constant and the tail read, the state. -/
structure NTailAt [Labels] (m0 : MachineData) (a : DecArea) (p0 : EW) (tail : Array EW)
    (s1 : TState) (m : MachineData) : Prop where
  frame : RFrame m0 m
  head : NativeRustcVm.EWsAt m.dmem (msgAt m0 + BitVec.ofNat 64 0) [p0]
  tail : NativeRustcVm.EWsAt m.dmem (msgAt m0 + BitVec.ofNat 64 32) tail.toList
  ts : TStateAt m.dmem (tAt m0) a s1

end

public section

variable [Host] {a : DecArea} {s : TState} {e : Option EW} {m0 : MachineData} {k : Nat}

omit [Host] in
theorem NoneRegs.of_saved {m m' : MachineData} (h : NoneRegs m0 m) (hsv : Saved m m') :
    NoneRegs m0 m' :=
  ⟨(hsv.1 .X19 rfl).trans h.x19, (hsv.1 .X20 rfl).trans h.x20, (hsv.1 .X21 rfl).trans h.x21,
    (hsv.1 .X22 rfl).trans h.x22, by rw [hsv.1 .X23 rfl]; exact h.x23⟩

/-- The registers through a body block that keeps them. -/
theorem NoneRegs.of_block {m m' : MachineData} {S : SState} (h : NoneRegs m0 m)
    (hm : Match (envB m0 m) S m') (h19 : S.reg .X19 = some (.ptr 1 0))
    (h20 : S.reg .X20 = some (.reg .X20)) (h21 : S.reg .X21 = some (.reg .X21))
    (h22 : S.reg .X22 = some (.reg .X22)) (h23 : S.reg .X23 = some (.reg .X23)) :
    NoneRegs m0 m' :=
  ⟨x19_of_match hm h19, (reg_of_match hm h20).trans h.x20, (reg_of_match hm h21).trans h.x21,
    (reg_of_match hm h22).trans h.x22, by rw [reg_of_match hm h23]; exact h.x23⟩

/-- **The constant and the tail through a call** that changes `R` (in the `TState`) and its
stack. -/
theorem NTailAt.after (hpre : RoundPolyPre a s e m0) {p0 : EW} {tail : Array EW} {s1 : TState}
    {m m' : MachineData} (ht : NTailAt m0 a p0 tail s1 m) (hsz : tail.size + 2 ≤ maxCount)
    {Nc : Nat} (hle : 112 + Nc ≤ roundPolyStack) {R : BitVec 64 → Prop}
    (hR : ∀ p, R p → InRange (tAt m0) tstateBytes p)
    (hs : SameOutside m.dmem m'.dmem (fun p ↦ R p ∨ InRange (stackBelow m Nc) Nc p))
    (hsv : Saved m m') {s2 : TState} (hts : TStateAt m'.dmem (tAt m0) a s2) :
    NTailAt m0 a p0 tail s2 m' :=
  have hRm : ∀ p, (R p ∨ InRange (stackBelow m Nc) Nc p) → ¬ InRange (msgAt m0) (16 * maxCount) p :=
    fun p hp ↦ hp.elim (fun h ↦ t_not_msg hpre (hR p h))
      (fun h ↦ stack_not_msg hpre (callee_stack hpre ht.frame hle h))
  ⟨ht.frame.after_call hpre hle (fun p hp ↦ ⟨Or.inr (Or.inl (hR p hp)), t_not_fr hpre (hR p hp)⟩)
      hs hsv,
    msg_keep hpre hs hRm (by simp [maxCount]) ht.head,
    msg_keep hpre hs hRm (by simp only [Array.length_toList]; omega) ht.tail, hts⟩

/-- **The constant and the tail through a call** that changes only its stack. -/
theorem NTailAt.of_call (hpre : RoundPolyPre a s e m0) {p0 : EW} {tail : Array EW} {s1 : TState}
    {m m' : MachineData} (ht : NTailAt m0 a p0 tail s1 m) (hsz : tail.size + 2 ≤ maxCount)
    {Nc : Nat} (hle : 112 + Nc ≤ roundPolyStack)
    (hs : SameOutside m.dmem m'.dmem (InRange (stackBelow m Nc) Nc)) (hsv : Saved m m') :
    NTailAt m0 a p0 tail s1 m' :=
  ht.after hpre hsz hle (R := fun _ ↦ False) (fun _ h ↦ h.elim)
    (fun p hp ↦ hs p fun h ↦ hp (Or.inr h)) hsv
    (tstate_keep hpre hs hsv.2.2 (fun _ hp ↦ Or.inr (callee_stack hpre ht.frame hle hp)) ht.ts)

/-- The model's plain round from the constant on. -/
abbrev runN (m0 : MachineData) (p0 : EW) (s0 : TState) : Option (Array EW × TState) :=
  ((readScalars (cnt m0 - 2)).run s0).bind fun p ↦
    ((grind (grindingBits (cnt m0 - 1))).run p.2).bind fun q ↦
      some (#[p0, claimOf m0 + sumE p.1] ++ p.1, q.2)

/-- **After the tail's sum**, at `b14`: the grind's bits, the grind, the result. -/
theorem none_b14 (hp : Placed code k)
    (hbl : Spec (Labels.label NativeRustcVmArm.Vm.BitLength.entryLabel) BitLengthPre BitLengthPost)
    (hgr : ∀ a s, Spec (Labels.label NativeRustcVmArm.Vm.TStateGrind.entryLabel) (GrindPre a s) (GrindPost a s))
    (hpre : RoundPolyPre a s none m0) {p0 : EW} {s0 : TState}
    (hr0 : runR m0 s none = runN m0 p0 s0) {tail : Array EW} {s1 : TState}
    (hr1 : (readScalars (cnt m0 - 2)).run s0 = some (tail, s1)) {m : MachineData}
    (hg : NoneRegs m0 m) (ht : NTailAt m0 a p0 tail s1 m)
    (hx0 : m.regs.X0 = (sumE tail).c0) (hx1 : m.regs.X1 = (sumE tail).c1) :
    Eventually (step1 Host.exe)
      (fun st ↦ st.pc = retOf m0 ∧ RoundPolyPost a s none m0 st.data)
      ⟨m, Host.addrOf (k + NativeRustcVmArm.Vm.TStateSumcheckRoundPoly.b14Offset)⟩ := by
  have c := ctx_of hpre
  have hc2 : 2 ≤ cnt m0 := hpre.2.2.2.2.1
  have hc5 : cnt m0 ≤ maxCount := hpre.2.2.2.2.2.1
  have hmc : maxCount = 5 := rfl
  have htl : tail.size = cnt m0 - 2 := readScalars_size hr1
  have hsz : tail.size + 2 ≤ maxCount := by omega
  have hk14 : b14.IsInfixAt Host.prog (k + NativeRustcVmArm.Vm.TStateSumcheckRoundPoly.b14Offset) := b14_in_code.trans hp.1 (by simp [b14])
  have hk15 : b15.IsInfixAt Host.prog (k + NativeRustcVmArm.Vm.TStateSumcheckRoundPoly.b15Offset) := b15_in_code.trans hp.1 (by simp [b15])
  have hk16 : b16.IsInfixAt Host.prog (k + NativeRustcVmArm.Vm.TStateSumcheckRoundPoly.b16Offset) := b16_in_code.trans hp.1 (by simp [b16])
  have hk17 : b17.IsInfixAt Host.prog (k + NativeRustcVmArm.Vm.TStateSumcheckRoundPoly.b17Offset) := b17_in_code.trans hp.1 (by simp [b17])
  have hl9 : Labels.label NativeRustcVmArm.Vm.TStateSumcheckRoundPoly.label_9 = Host.addrOf (k + NativeRustcVmArm.Vm.TStateSumcheckRoundPoly.b19Offset) :=
    hp.label (j := NativeRustcVmArm.Vm.TStateSumcheckRoundPoly.b19Offset) NativeRustcVmArm.Vm.TStateSumcheckRoundPoly.label_9_at
  -- `b14`: `bit_length(count - 2)`.
  refine exec_then hk14 run_b14 (wf_envB hpre ht.frame) (match_bodyS hpre ht.frame hg.x19)
    fun st4 hm4 hpc4 ↦ ?_
  obtain ⟨hf4, hd4⟩ := RFrame.of_block hpre ht.frame hm4 rfl rfl rfl rfl
  have hg4 := hg.of_block hm4 rfl rfl rfl rfl rfl
  have h24 : st4.data.regs.getXReg .X24 = (sumE tail).c0 :=
    (reg_of_match' (r := .X24) (r' := .X0) hm4 rfl).trans hx0
  have h25 : st4.data.regs.getXReg .X25 = (sumE tail).c1 :=
    (reg_of_match' (r := .X25) (r' := .X1) hm4 rfl).trans hx1
  have h40 : st4.data.regs.X0.toNat = cnt m0 - 2 := by
    have := reg_of_match' (r := .X0) (r' := .X23) hm4 rfl
    rw [show st4.data.regs.X0 = st4.data.regs.getXReg .X0 from rfl, this]
    exact hg.x23
  have ht4 : NTailAt m0 a p0 tail s1 st4.data := ⟨hf4, hd4 ▸ ht.head, hd4 ▸ ht.tail, hd4 ▸ ht.ts⟩
  refine call_then hpc4 hbl trivial fun st5 hpc5 ⟨hbits, hs5, hsv5⟩ ↦ ?_
  have ht5 := ht4.of_call hpre hsz (Nc := bitLengthStack) (by decide) hs5 hsv5
  have hg5 := hg4.of_saved hsv5
  have h524 : st5.data.regs.getXReg .X24 = (sumE tail).c0 := (hsv5.1 .X24 rfl).trans h24
  have h525 : st5.data.regs.getXReg .X25 = (sumE tail).c1 := (hsv5.1 .X25 rfl).trans h25
  have hb5 : st5.data.regs.X0.toNat = bitLenNat (cnt m0 - 2) := by rw [hbits, h40]; rfl
  -- `b15`: `grind(bits)`.
  refine exec_at hk15 run_b15 (wf_envB hpre ht5.frame) hpc5 (match_bodyS hpre ht5.frame hg5.x19)
    fun st6 hm6 hpc6 ↦ ?_
  obtain ⟨hf6, hd6⟩ := RFrame.of_block hpre ht5.frame hm6 rfl rfl rfl rfl
  have hg6 := hg5.of_block hm6 rfl rfl rfl rfl rfl
  have h624 : st6.data.regs.getXReg .X24 = (sumE tail).c0 :=
    (reg_of_match (r := .X24) hm6 rfl).trans h524
  have h625 : st6.data.regs.getXReg .X25 = (sumE tail).c1 :=
    (reg_of_match (r := .X25) hm6 rfl).trans h525
  have ht6 : NTailAt m0 a p0 tail s1 st6.data :=
    ⟨hf6, hd6 ▸ ht5.head, hd6 ▸ ht5.tail, hd6 ▸ ht5.ts⟩
  have h60 : st6.data.regs.X0 = m0.regs.X0 :=
    (reg_of_match' (r := .X0) (r' := .X22) hm6 rfl).trans hg5.x22
  have hbl64 : bitLenNat (cnt m0 - 2) ≤ 64 := bitLenNat_le _ (by omega)
  have hbits6 : grindBits st6.data = grindingBits (cnt m0 - 1) := by
    have h1 := hm6.regs .X1 _ rfl
    have h2 := grind_bits (envB m0 st5.data) (by
      show st5.data.regs.X0.toNat ≤ 64
      rw [hb5]; exact hbl64)
    unfold grindBits
    rw [show cnt m0 - 1 = cnt m0 - 2 + 1 by omega, grindingBits_succ,
      show st6.data.regs.X1.toNat = (st6.data.regs.getXReg .X1).toBitVec.toNat from rfl, h1, h2]
    show (st5.data.regs.X0.toNat - 3) % 2 ^ 32 = _
    rw [hb5]
    omega
  refine call_then hpc6 (hgr a s1) ?pre fun st7 hpc7 hpost7 ↦ ?_
  case pre =>
    simp only [GrindPre, h60, hbits6]
    refine ⟨c.stackOk hf6.at_ (by decide), c.rcAt hf6.at_ (by decide), ht6.ts,
      c.tstateOk hf6.at_ (by decide), ?_⟩
    rw [show cnt m0 - 1 = cnt m0 - 2 + 1 by omega, grindingBits_succ]; omega
  simp only [GrindPost, h60, hbits6] at hpost7
  obtain ⟨hok7, hnext7, hs7, hsv7⟩ := hpost7
  have hf7 : RFrame m0 st7.data := hf6.after_call hpre (Nc := grindStack) (by decide)
    (R := InRange (tAt m0) tstateBytes) (fun p hp ↦ ⟨Or.inr (Or.inl hp), t_not_fr hpre hp⟩)
    hs7 hsv7
  have hg7 := hg6.of_saved hsv7
  -- `b16`: the grind's test.
  have hwf7 := wf_envB hpre hf7
  have hm7 := match_bodyS hpre hf7 hg7.x19
  refine exec_at hk16 run_b16 hwf7 hpc7 hm7 fun st8 hm8 hpc8 ↦ ?_
  obtain ⟨hf8, hd8⟩ := RFrame.of_block hpre hf7 hm8 rfl rfl rfl rfl
  have h80 : st8.data.regs.X0 = st7.data.regs.X0 := reg_of_match (r := .X0) hm8 rfl
  have hX0 : (envB m0 st7.data).regs .X0 = st7.data.regs.X0.toBitVec := rfl
  simp only [PcOk, SBool.eval, CmpOp.apply, Sym.eval, hX0] at hpc8
  cases hr2 : (grind (grindingBits (cnt m0 - 1))).run s1 with
  | none =>
    rw [hr2] at hok7
    have hpc : st8.pc = Host.addrOf (k + NativeRustcVmArm.Vm.TStateSumcheckRoundPoly.b19Offset) := by
      rw [hpc8, hok7, Option.isSome_none]
      have hc : (low .W32 (okWord false).toBitVec == low .W32 0#64) = true := by decide
      simp only [hc, ↓reduceIte, hl9]
    obtain ⟨d8, pc8⟩ := st8
    simp only at hpc
    subst hpc
    refine Eventually.mono (exit_spec hp hpre hf8) fun st ⟨h1, h2, h3, h4⟩ ↦ ⟨h1, ?_⟩
    refine post_none ?_ (h2.trans (h80.trans hok7)) (h3 ▸ hf8.same) h4
    rw [hr0]
    simp [runN, hr1, hr2]
  | some q =>
    obtain ⟨⟨⟩, s2⟩ := q
    rw [hr2] at hok7
    have hts2 : TStateAt st7.data.dmem (tAt m0) a s2 := hnext7 () s2 hr2
    have ht7 : NTailAt m0 a p0 tail s2 st7.data :=
      ht6.after hpre hsz (Nc := grindStack) (by decide) (R := InRange (tAt m0) tstateBytes)
        (fun _ h ↦ h) hs7 hsv7 hts2
    have hpc : st8.pc = Host.addrOf (k + NativeRustcVmArm.Vm.TStateSumcheckRoundPoly.b17Offset) := by
      rw [hpc8, hok7, Option.isSome_some]
      have hc : (low .W32 (okWord true).toBitVec == low .W32 0#64) = false := by decide
      simp only [hc, Bool.false_eq_true, ↓reduceIte]
      rfl
    -- `b17`: the derived coefficient into `msg[1]`, `Some`.
    have hm8' : Match (envB m0 st7.data) (after b16 bodyS) st8.data := by
      rw [after_eq run_b16]; exact hm8
    refine exec_at hk17 run_b17 hwf7 hpc hm8' fun st11 hm11 hpc11 ↦ ?_
    have hm11' : Match (envB m0 st7.data) (after b17 (after b16 bodyS)) st11.data := by
      rw [after_eq run_b17]; exact hm11
    have hno := (msgOk hpre).2.1
    unfold NoWrap at hno
    rw [hmc] at hno
    have hW : ∀ p, Written (envB m0 st7.data) (after b17 (after b16 bodyS)) p →
        (msgAt m0).toNat + 16 ≤ p.toNat ∧ p.toNat < (msgAt m0).toNat + 32 := fun p h ↦ by
      have := Written.toNat (r := 1) (lo := 16) (hi := 32) rfl
        (by rw [after_eq run_b17]; decide) h
      omega
    have hWr : ∀ p, Written (envB m0 st7.data) (after b17 (after b16 bodyS)) p →
        InRange (msgAt m0) (16 * maxCount) p := fun p h ↦ by
      have := hW p h
      rw [Sym.inRange_iff (by rw [hmc]; omega)]
      rw [hmc]; omega
    have hs11 := hm11'.sameOutside hwf7
    have hsv11 : Saved st7.data st11.data :=
      Match.saved hm7 hm11' hwf7 rfl (by rw [after_eq run_b17]; decide)
    have hf11 : RFrame m0 st11.data := hf7.after_call hpre (Nc := 0) (by decide)
      (R := Written (envB m0 st7.data) (after b17 (after b16 bodyS)))
      (fun p hp ↦ ⟨Or.inl (hWr p hp), msg_not_fr hpre (hWr p hp)⟩)
      (fun p hp ↦ hs11 p fun h ↦ hp (Or.inl h)) hsv11
    have hhead11 : NativeRustcVm.EWsAt st11.data.dmem (msgAt m0 + BitVec.ofNat 64 0) [p0] := by
      refine NativeRustcVm.BytesAt.of_sameOutside ht7.head hs11 fun i hi hw ↦ ?_
      have := hW _ hw
      rw [NativeRustcVm.length_ewsBytes] at hi
      simp only [List.length_singleton] at hi
      rw [NativeRustcVm.addr_add_add, NativeRustcVm.toNat_add_ofNat (by omega)] at this
      omega
    have htail11 : NativeRustcVm.EWsAt st11.data.dmem (msgAt m0 + BitVec.ofNat 64 32)
        tail.toList := by
      refine NativeRustcVm.BytesAt.of_sameOutside ht7.tail hs11 fun i hi hw ↦ ?_
      have := hW _ hw
      rw [NativeRustcVm.length_ewsBytes] at hi
      simp only [Array.length_toList] at hi
      rw [NativeRustcVm.addr_add_add, NativeRustcVm.toNat_add_ofNat (by omega)] at this
      omega
    have hts11 : TStateAt st11.data.dmem (tAt m0) a s2 :=
      tstate_keep hpre hs11 hsv11.2.2 (fun p hp ↦ Or.inl (hWr p hp)) ht7.ts
    have hg8 := hg7.of_block hm8 rfl rfl rfl rfl rfl
    have hx21 : (envB m0 st7.data).regs .X21 = m0.regs.X2.toBitVec := by
      show (st7.data.regs.getXReg .X21).toBitVec = _; rw [hg7.x21]
    have hx20 : (envB m0 st7.data).regs .X20 = m0.regs.X3.toBitVec := by
      show (st7.data.regs.getXReg .X20).toBitVec = _; rw [hg7.x20]
    have hx24 : (envB m0 st7.data).regs .X24 = (sumE tail).c0.toBitVec := by
      show (st7.data.regs.getXReg .X24).toBitVec = _; rw [hsv7.1 .X24 rfl, h624]
    have hx25 : (envB m0 st7.data).regs .X25 = (sumE tail).c1.toBitVec := by
      show (st7.data.regs.getXReg .X25).toBitVec = _; rw [hsv7.1 .X25 rfl, h625]
    have hmid : NativeRustcVm.EWAt st11.data.dmem (msgAt m0 + BitVec.ofNat 64 16)
        (claimOf m0 + sumE tail) := by
      have w0 := NativeRustcVmArm.Sumcheck.Match.wordAt_write hm11 (r := 1) (o := 16) rfl
        (by decide) (fun i hi ↦ by
          match i, hi with
          | 0, _ | 1, _ | 2, _ | 3, _ | 4, _ | 5, _ | 6, _ | 7, _ => rfl)
      have w1 := NativeRustcVmArm.Sumcheck.Match.wordAt_write hm11 (r := 1) (o := 24) rfl
        (by decide) (fun i hi ↦ by
          match i, hi with
          | 0, _ | 1, _ | 2, _ | 3, _ | 4, _ | 5, _ | 6, _ | 7, _ => rfl)
      rw [NativeRustcVm.ewAt_iff, NativeRustcVm.addr_add_add]
      refine ⟨?_, ?_⟩
      · convert w0 using 1
        simp only [Sym.eval, BinOp.apply, low_W64, ext_W64, hx21, hx24]
        show m0.regs.X2 ^^^ (sumE tail).c0 = _
        rw [UInt64.xor_comm]; rfl
      · convert w1 using 1
        simp only [Sym.eval, BinOp.apply, low_W64, ext_W64, hx20, hx25]
        show m0.regs.X3 ^^^ (sumE tail).c1 = _
        rw [UInt64.xor_comm]; rfl
    have h110 : st11.data.regs.X0 = 1 := UInt64.toBitVec_inj.mp (hm11.regs .X0 _ rfl)
    simp only [PcOk] at hpc11
    rw [hl9] at hpc11
    obtain ⟨d11, pc11⟩ := st11
    simp only at hpc11
    subst hpc11
    refine Eventually.mono (exit_spec hp hpre hf11) fun st ⟨h1, h2, h3, h4⟩ ↦ ⟨h1, ?_⟩
    refine post_some (msg := #[p0, claimOf m0 + sumE tail] ++ tail) (s' := s2) ?_
      (h2.trans h110) ?_ (h3 ▸ hts11) (h3 ▸ hf11.same) h4
    · rw [hr0]
      simp [runN, hr1, hr2]
    · rw [h3, Array.toList_append, NativeRustcVm.ewsAt_append]
      rw [NativeRustcVm.addr_add_zero] at hhead11
      refine ⟨?_, by simpa [NativeRustcVm.addr_add_add] using htail11⟩
      show NativeRustcVm.EWsAt _ _ ([p0] ++ [claimOf m0 + sumE tail])
      rw [NativeRustcVm.ewsAt_append]
      exact ⟨hhead11, by simpa using NativeRustcVm.ewsAt_singleton.2 hmid⟩

end

end NativeRustcVmArm.Sumcheck.RoundPoly
