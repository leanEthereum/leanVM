module

public import NativeRustcVmX64.Ring.Claim.Exec
public import NativeRustcVmX64.Ring.Stack
public import NativeRustcVmX64.Code.Vm.EWMul.Names
public import NativeRustcVmX64.Code.Vm.EqEvalFnOfEqAbove.Names
public import NativeRustcVmX64.Code.Vm.RingClaimWeight.Names
public import NativeRustcVmX64.Code.Vm.RingWeight.Names

/-!
# `ring_claim_weight` on x86-64

**`ringClaimWeight_spec`**: rustc's `ring_claim_weight(out, p, r, coefficients, x)`, placed
anywhere in the program, given the contracts of `eq_eval_fn` (`eq_above`'s closure),
`ring_weight` and `EW::mul`, stores `Some(eq_above(p, x) · ring_weight(r, x[..vc], c))`. `b0`
(the prologue, `eq_above`'s arguments: `eval_sat`, `eval_shr`, `eval_above`, `eval_min`; `call
eq_eval_fn`), `b1` (`call ring_weight` into the frame), `b2` (its tag, always `1`), `b3` (`call
EW::mul`), `b4`, `b6` (the product and the tag `1` stored, the epilogue).
-/

namespace NativeRustcVmX64.Ring.Claim

open NativeRustcX64 NativeRustcX64.Sym NativeRustcVmX64.Vm.RingClaimWeight NativeRustcVmX64.Transcript
open NativeRustcVm.Transcript NativeVm.Model NativeRustcVm.Ring

public section

/-! ## The values `b0` computes -/

section
variable [Labels] (env : Env)

theorem eval_sat : (satS.eval env).toNat = (env.load 1 8 8).toNat - (env.regs .rsi).toNat := by
  simp only [satS, Sym.eval, SBool.eval, CmpOp.apply, BinOp.apply, low_W64, ext_W64]
  split <;> rename_i hc <;> simp only [BitVec.ult, decide_eq_true_eq] at hc
  · simp; omega
  · rw [BitVec.toNat_sub_of_le (by simp [BitVec.le_def]; omega)]

theorem eval_min : (minS.eval env).toNat = min (env.regs .rsi).toNat (env.load 1 8 8).toNat := by
  simp only [minS, Sym.eval, SBool.eval, CmpOp.apply, low_W64]
  split <;> rename_i hc <;> simp only [BitVec.ult, decide_eq_true_eq] at hc <;> omega

theorem eval_shr :
    (shrS.eval env).toNat = (env.regs .rdx).toNat >>> (env.regs .rsi).toNat := by
  simp only [shrS, Sym.eval, SBool.eval, CmpOp.apply, BinOp.apply, low_W64, ext_W64]
  have hr := (env.regs .rdx).isLt
  split <;> rename_i hc <;> simp only [BitVec.ult, decide_eq_true_eq] at hc
  · have h64 : (BitVec.ofNat 64 64).toNat = 64 := rfl
    rw [h64] at hc
    have hs : shiftCount .W64 (env.regs .rsi) = (env.regs .rsi).toNat := by
      show ((env.regs .rsi).setWidth 8).toNat &&& 63 = _
      rw [BitVec.toNat_setWidth, show (63 : Nat) = 2 ^ 6 - 1 from rfl,
        Nat.and_two_pow_sub_one_eq_mod]
      omega
    rw [hs]
    exact BitVec.toNat_ushiftRight _ _
  · rw [show (BitVec.ofNat 64 64).toNat = 64 from rfl] at hc
    rw [Nat.shiftRight_eq_div_pow, Nat.div_eq_of_lt
      (Nat.lt_of_lt_of_le hr (Nat.pow_le_pow_right (by omega) (by omega)))]
    rfl

theorem eval_above :
    aboveS.eval env = if (env.load 1 8 8).toNat < (env.regs .rsi).toNat then 8#64
      else env.load 1 0 8 + BitVec.ofNat 64 (16 * (env.regs .rsi).toNat) := by
  simp only [aboveS, Sym.eval, SBool.eval, CmpOp.apply, BinOp.apply, low_W64, ext_W64]
  have h4 : shiftCount .W64 (BitVec.ofNat 64 4) = 4 := rfl
  split <;> rename_i hc
  · simp only [Bool.or_eq_true, BitVec.ult, decide_eq_true_eq, beq_iff_eq] at hc
    have : ¬ (env.load 1 8 8).toNat < (env.regs .rsi).toNat := by
      rcases hc with hc | hc
      · omega
      · rw [hc]; omega
    rw [ite_eq_right this, h4]
    congr 1
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.shiftLeft_eq,
      show (2 : Nat) ^ 4 = 16 from rfl, Nat.mul_comm]
  · simp only [Bool.or_eq_true, BitVec.ult, decide_eq_true_eq, beq_iff_eq, not_or] at hc
    have h1 : (env.regs .rsi).toNat ≠ (env.load 1 8 8).toNat := fun h ↦ hc.2 (BitVec.eq_of_toNat_eq h)
    rw [ite_eq_left (by omega)]

end

/-! ## Slices of `x` -/

theorem ewsOf_drop (d : DataMem) (b : BitVec 64) (n k : Nat) :
    (NativeRustcVm.ewsOf d b (k + n)).drop k =
      NativeRustcVm.ewsOf d (b + BitVec.ofNat 64 (16 * k)) n := by
  apply List.ext_getElem (by simp)
  intro i h1 h2
  simp only [List.getElem_drop, NativeRustcVm.getElem_ewsOf]
  rw [NativeRustcVm.addr_add_add, Nat.mul_add]

/-- The elements from `x + 16·vc`: `x`'s from `vc`. -/
theorem slice_above {m : MachineData} {a n : BitVec 64} {v : Nat} (hv : v ≤ n.toNat)
    {a' n' : BitVec 64} (ha' : a' = a + BitVec.ofNat 64 (16 * v))
    (hn' : n'.toNat = n.toNat - v) :
    slice m a' n' = (slice m a n).extract v (slice m a n).size := by
  unfold slice
  rw [ha', hn', ← ewsOf_drop m.dmem a (n.toNat - v) v, show v + (n.toNat - v) = n.toNat by omega]
  simp

/-- An empty rest when `vc > |x|`. -/
theorem slice_above_nil {m m' : MachineData} {a n : BitVec 64} {v : Nat} (hv : n.toNat < v)
    {a' n' : BitVec 64} (hn' : n'.toNat = 0) :
    slice m a' n' = (slice m' a n).extract v (slice m' a n).size := by
  unfold slice
  rw [hn']
  apply Array.ext (by simp; omega) fun i h1 h2 ↦ by simp at h1

/-- `x.get(..vc).unwrap_or(x)`: the first `min(vc, |x|)` elements. -/
theorem slice_low {m : MachineData} {a n : BitVec 64} {v : Nat} {n' : BitVec 64}
    (hn' : n'.toNat = min v n.toNat) : slice m a n' = (slice m a n).extract 0 v := by
  unfold slice
  rw [hn']
  apply Array.ext (by simp) fun i h1 h2 ↦ by simp

theorem slots_le : ∀ p ∈ slots, p.1 + 8 ≤ 96 := by decide

theorem slice_size (m : MachineData) (a n : BitVec 64) : (slice m a n).size = n.toNat := by
  simp [slice]

theorem stack_eq : ringClaimWeightStack = 912 := rfl

/-! ## The contract -/

variable [Host] {k : Nat}

/-- **`ring_claim_weight` meets its contract.** -/
theorem ringClaimWeight_spec (hp : Placed code k)
    (hee : Spec (Labels.label NativeRustcVmX64.Vm.EqEvalFnOfEqAbove.entryLabel) EqEvalFnOfEqAbovePre
      EqEvalFnOfEqAbovePost)
    (hrw : Spec (Labels.label NativeRustcVmX64.Vm.RingWeight.entryLabel) RingWeightPre RingWeightPost)
    (hmul : Spec (Labels.label NativeRustcVmX64.Vm.EWMul.entryLabel) EWMulPre EWMulPost) :
    Spec (Labels.label NativeRustcVmX64.Vm.RingClaimWeight.entryLabel) RingClaimWeightPre RingClaimWeightPost := by
  rintro m0 ⟨hst, hargs, hr36, hx64, hpt, hco, hx, ⟨⟨hom, hon⟩, hoS, hoA⟩⟩
  set o := reg m0 .rdi with hodef
  set xa := rspOf m0 + 8#64 with hxadef
  set fb := stackBelow m0 96 with hfb
  have hn : 912 ≤ (rspOf m0).toNat := hst.1
  have h8 : (rspOf m0).toNat + 8 ≤ 2 ^ 64 := hst.2.1
  have hfbN : fb.toNat = (rspOf m0).toNat - 96 := stackBelow_toNat (by omega)
  have hfnw : NativeRustcVm.NoWrap fb (96 + 8) := frame_noWrap hst (by decide)
  have hxN : xa.toNat = (rspOf m0).toNat + 8 := args_toNat hargs (by decide)
  have hA2 := hargs.2
  obtain ⟨hxm, hxn⟩ := args_readable hargs (by decide)
  have hxF : NativeRustcVm.Apart fb (96 + 8) xa (8 * 2) :=
    args_apart hst hargs (by decide) (by decide)
  have hoF : NativeRustcVm.Apart o 24 fb (96 + 8) := apart_frame hoS hst.1 (by decide)
  have hpw := pairwise3 (R := fun x y : BitVec 64 × Nat ↦ NativeRustcVm.Apart x.1 x.2 y.1 y.2)
    (x := (fb, 96 + 8)) (y := (xa, 16)) (z := (o, 24)) hxF (Apart.symm' hoF)
    (Apart.symm' hoA)
  have hstack : ∀ q, NativeRustcVm.InRange fb 96 q →
      NativeRustcVm.InRange (stackBelow m0 ringClaimWeightStack) ringClaimWeightStack q :=
    fun q h ↦ frame_in hst (by decide) h
  have hnil : ∀ q, ¬ NativeRustcVm.InRange 0 0 q := fun q h ↦ by unfold NativeRustcVm.InRange at h; omega
  -- The environments: the frame, `x`'s words, the output.
  have hwfE : ∀ (d : MachineData) (ret : BitVec 64), Kept m0.dmem d.dmem →
      (frameEnv m0 d 96 [(xa, 16), (o, 24)] (fun _ ↦ 0) ret).WF := fun d ret hk ↦
    frame_wf ⟨Mapped.keeps (frame_mapped hst (by decide)) hk, hfnw⟩
      (rest2_ok ⟨hxm, hxn⟩ ⟨hom, hon⟩ hk) hpw
  have hal : ∀ (d : MachineData) (ret : BitVec 64), ∀ j : Nat, j < 16 →
      (Sym.ptr 0 ((104 + j : Nat) : Int)).eval (frameEnv m0 d 96 [(xa, 16), (o, 24)] (fun _ ↦ 0) ret) =
        (frameEnv m0 d 96 [(xa, 16), (o, 24)] (fun _ ↦ 0) ret).base 1 + BitVec.ofInt 64 (j : Int) := by
    intro d ret j hj
    rw [eval_ptr0, ← hfb, BitVec.ofInt_natCast]
    show _ = xa + _
    apply BitVec.eq_of_toNat_eq
    rw [toNat_off (by omega), BitVec.toNat_add, BitVec.toNat_ofNat, hxN, hfbN]
    omega
  have hxs : ∀ (d : MachineData) (ret : BitVec 64),
      SameOutside m0.dmem d.dmem (InRange (stackBelow m0 ringClaimWeightStack) ringClaimWeightStack) →
      (frameEnv m0 d 96 [(xa, 16), (o, 24)] (fun _ ↦ 0) ret).load 1 0 8 = stackArg m0 0 ∧
        (frameEnv m0 d 96 [(xa, 16), (o, 24)] (fun _ ↦ 0) ret).load 1 8 8 = stackArg m0 1 :=
    fun d ret hs ↦ ⟨argWord hst hargs (by decide) hs rfl rfl (i := 0) (by decide),
      argWord hst hargs (by decide) hs rfl rfl (i := 1) (by decide)⟩
  -- `b0`: the prologue, `eq_above`'s arguments, `call eq_eval_fn`.
  have hwf0 := hwfE m0 (Host.addrOf (k + NativeRustcVmX64.Vm.RingClaimWeight.b0Offset + b0.length)).toBitVec fun _ h ↦ h
  have hm0 : Match (frameEnv m0 m0 96 [(xa, 16), (o, 24)] (fun _ ↦ 0)
      (Host.addrOf (k + NativeRustcVmX64.Vm.RingClaimWeight.b0Offset + b0.length)).toBitVec) entryS m0 :=
    match_ofMachine ⟨rfl, rfl, rfl, trivial⟩ ⟨match_rsp, known_ptr rfl rfl, trivial⟩ trivial
      trivial ⟨hal _ _ 0 (by decide), hal _ _ 8 (by decide), trivial⟩
  unfold NativeRustcVmX64.Vm.RingClaimWeight.entryLabel
  rw [hp.label NativeRustcVmX64.Vm.RingClaimWeight.entry_at]
  refine exec_then (infix_of b0_in_code (by simp [b0]) hp) run_b0 hwf0 (fun _ _ ↦ rfl) hm0
    fun st1 hm1 hpc1 ↦ ?_
  obtain ⟨hpro, hws1, hrdi, hrcx, hrsi, hrdx, hrbx, hrbp, hr12, hr15, hsp16⟩ :=
    after_eq run_b0 ▸ ok_b0
  have hf1 : Frame m0 96 slots 0 st1.data :=
    Frame.of_prologue Frame.entry hwf0 hm1 hpro slots_le (by decide)
  have hs1 : SameOutside m0.dmem st1.data.dmem
      (InRange (stackBelow m0 ringClaimWeightStack) ringClaimWeightStack) :=
    fun q hq ↦ sameOutside_low hwf0 hm1 (r := 0) rfl (by decide) hws1 q fun h ↦ hq (hstack q h)
  have hsp1 : rspOf st1.data = fb := by rw [hf1.sp, off_zero]
  obtain ⟨hx0, hx1⟩ := hxs m0 (Host.addrOf (k + NativeRustcVmX64.Vm.RingClaimWeight.b0Offset + b0.length)).toBitVec fun _ _ ↦ rfl
  have hrsi0 : (frameEnv m0 m0 96 [(xa, 16), (o, 24)] (fun _ ↦ 0)
      (Host.addrOf (k + NativeRustcVmX64.Vm.RingClaimWeight.b0Offset + b0.length)).toBitVec).regs .rsi = reg m0 .rsi := rfl
  have hrdx0 : (frameEnv m0 m0 96 [(xa, 16), (o, 24)] (fun _ ↦ 0)
      (Host.addrOf (k + NativeRustcVmX64.Vm.RingClaimWeight.b0Offset + b0.length)).toBitVec).regs .rdx = reg m0 .rdx := rfl
  have e1di : (reg st1.data .rdi).toNat = (stackArg m0 1).toNat - (reg m0 .rsi).toNat := by
    rw [show reg st1.data .rdi = _ from hm1.regs .rdi _ hrdi, eval_sat, hx1, hrsi0]
  have e1cx : (reg st1.data .rcx).toNat = (stackArg m0 1).toNat - (reg m0 .rsi).toNat := by
    rw [show reg st1.data .rcx = _ from hm1.regs .rcx _ hrcx, eval_sat, hx1, hrsi0]
  have e1si : (reg st1.data .rsi).toNat = (reg m0 .rdx).toNat >>> (reg m0 .rsi).toNat := by
    rw [show reg st1.data .rsi = _ from hm1.regs .rsi _ hrsi, eval_shr, hrsi0, hrdx0]
  have e1dx : reg st1.data .rdx = if (stackArg m0 1).toNat < (reg m0 .rsi).toNat then 8#64
      else stackArg m0 0 + BitVec.ofNat 64 (16 * (reg m0 .rsi).toNat) := by
    rw [show reg st1.data .rdx = _ from hm1.regs .rdx _ hrdx, eval_above, hx0, hx1, hrsi0]
  have e1bp : (reg st1.data .rbp).toNat = min (reg m0 .rsi).toNat (stackArg m0 1).toNat := by
    rw [show reg st1.data .rbp = _ from hm1.regs .rbp _ hrbp, eval_min, hx1, hrsi0]
  have e1b : reg st1.data .rbx = o := (hm1.regs .rbx _ hrbx).trans (eval_ptr rfl)
  have e112 : reg st1.data .r12 = reg m0 .rcx := hm1.regs .r12 _ hr12
  have e115 : reg st1.data .r15 = reg m0 .r8 := hm1.regs .r15 _ hr15
  have hw16 : NativeRustcVm.WordAt st1.data.dmem (off fb 16) (UInt64.ofBitVec (reg m0 .r9)) := by
    have h := wordAt_write hm1 (r := 0) (o := 16) (b := fb) (sz := 96 + 8) rfl (by decide) hsp16
    simp only [Sym.eval] at h
    exact h
  have hxl : slice st1.data (reg st1.data .rdx) (reg st1.data .rcx) = (slice m0 (stackArg m0 0) (stackArg m0 1)).extract (reg m0 .rsi).toNat (slice m0 (stackArg m0 0) (stackArg m0 1)).size := by
    by_cases hlt : (stackArg m0 1).toNat < (reg m0 .rsi).toNat
    · exact slice_above_nil hlt (by rw [e1cx]; omega)
    · rw [ite_eq_right hlt] at e1dx
      rw [← slice_keep hst hs1 hx]
      exact slice_above (by omega) e1dx (by rw [e1cx])
  have hpre1 : EqEvalFnOfEqAbovePre st1.data := by
    refine ⟨stackOk_callee hst hf1.kept hsp1 (by decide), by rw [e1di, e1cx]; omega, ?_⟩
    have hxs' : OffStack st1.data (stackArg m0 0) (16 * (stackArg m0 1).toNat) eqEvalFnStack :=
      apart_callee hx.2 hsp1 hst.1 (by decide)
    have hcb := stackBelow_callee (n' := eqEvalFnStack) hsp1 (by simp only [eqEvalFnStack, ewMulStack]; omega)
    have hcbN := stackBelow_toNat (m := m0) (n := 96 + eqEvalFnStack)
      (by simp only [eqEvalFnStack, ewMulStack]; omega)
    have hxw := hx.1.2
    unfold NoWrap at hxw
    unfold SliceOk Readable OffStack Apart
    by_cases hlt : (stackArg m0 1).toNat < (reg m0 .rsi).toNat
    · rw [ite_eq_left hlt] at e1dx
      rw [e1dx, e1cx, show (stackArg m0 1).toNat - (reg m0 .rsi).toNat = 0 by omega, Nat.mul_zero]
      refine ⟨⟨fun j hj ↦ absurd hj (by omega), by unfold NoWrap; simp⟩, ?_⟩
      rw [hcb, hcbN]
      left
      simp only [eqEvalFnStack, ewMulStack, show (8#64 : BitVec 64).toNat = 8 from rfl]
      omega
    · rw [ite_eq_right hlt] at e1dx
      rw [e1dx, e1cx, show 16 * ((stackArg m0 1).toNat - (reg m0 .rsi).toNat) =
        16 * (stackArg m0 1).toNat - 16 * (reg m0 .rsi).toNat by omega]
      obtain ⟨h1, h2, h3⟩ := range_rest (Mapped.keeps hx.1.1 hf1.kept) hx.1.2 hxs'
        (o := 16 * (reg m0 .rsi).toNat) (by omega)
      exact ⟨⟨h1, h2⟩, h3⟩
  refine call_then hpc1 hee hpre1 fun st2 hpc2 hrsp2 ⟨hv2, hs2, hsv2⟩ ↦ ?_
  rw [hxl, e1di, e1si] at hv2
  have hR2 : ∀ j, j < 96 + 8 → ¬ (InRange 0 0 (off fb j) ∨
      InRange (stackBelow st1.data eqEvalFnStack) eqEvalFnStack (off fb j)) := by
    rintro j hj (h | h)
    · exact hnil _ h
    · exact not_callee hst hsp1 (by decide) hj h
  have hf2 : Frame m0 96 slots 8 st2.data :=
    Frame.call_slots hf1 hsv2 hrsp2 hs2
      (fun p hp i hi ↦ hR2 _ (by have := slots_le p hp; omega)) (fun j hj ↦ hR2 _ (by omega))
  have hs2' : SameOutside m0.dmem st2.data.dmem
      (InRange (stackBelow m0 ringClaimWeightStack) ringClaimWeightStack) :=
    same_trans hs1 hs2 fun q h ↦ h.elim (fun h ↦ absurd h (hnil q))
      (fun h ↦ callee_in hst hsp1 (by decide) h)
  have hw16' : NativeRustcVm.WordAt st2.data.dmem (off fb 16) (UInt64.ofBitVec (reg m0 .r9)) :=
    bytesAt_congr hw16 fun i hi ↦ by
      have hi' : i < 8 := by simpa [LeanVM.Protocol.KeccakHash.wordBytes] using hi
      rw [off_add]
      exact hs2 _ (hR2 _ (by omega))
  have e2b : reg st2.data .rbx = o := (hsv2.1 .rbx rfl).trans e1b
  -- `b1`: `call ring_weight` into the frame.
  have hwf2 := hwfE st2.data (Host.addrOf (k + NativeRustcVmX64.Vm.RingClaimWeight.b1Offset + b1.length)).toBitVec hf2.kept
  have hm2 : Match (frameEnv m0 st2.data 96 [(xa, 16), (o, 24)] (fun _ ↦ 0)
      (Host.addrOf (k + NativeRustcVmX64.Vm.RingClaimWeight.b1Offset + b1.length)).toBitVec) midS st2.data :=
    match_ofMachine ⟨rfl, rfl, rfl, trivial⟩ ⟨hf2.rsp_eval, known_ptr rfl e2b, trivial⟩ trivial
      trivial ⟨hal _ _ 0 (by decide), hal _ _ 8 (by decide), trivial⟩
  refine exec_at (infix_of b1_in_code (by simp [b1]) hp) run_b1 hwf2 (fun _ _ ↦ rfl)
    (hpc2.trans (by rw [Nat.add_assoc]; exact congrArg (fun j ↦ Host.addrOf (k + j)) NativeRustcVmX64.Vm.RingClaimWeight.b0_next)) hm2 fun st3 hm3 hpc3 ↦ ?_
  obtain ⟨hmid3, hws3, h3di, h3si, h3dx, h3cx, h3r8, h3r9, h3r13, h3r14, h3bx⟩ :=
    after_eq run_b1 ▸ ok_b1
  have hf3 : Frame m0 96 slots 0 st3.data := Frame.of_block hf2 hwf2 hm3 hmid3 slots_le
  have hsp3 : rspOf st3.data = fb := by rw [hf3.sp, off_zero]
  have hs3 : SameOutside st2.data.dmem st3.data.dmem (InRange fb 8) :=
    sameOutside_low hwf2 hm3 (r := 0) rfl (by decide) hws3
  have hs3' : SameOutside m0.dmem st3.data.dmem
      (InRange (stackBelow m0 ringClaimWeightStack) ringClaimWeightStack) :=
    same_trans hs2' hs3 fun q h ↦ hstack q (inRange_le h (by decide))
  obtain ⟨hy0, -⟩ := hxs st2.data (Host.addrOf (k + NativeRustcVmX64.Vm.RingClaimWeight.b1Offset + b1.length)).toBitVec hs2'
  have f3di : reg st3.data .rdi = off fb 24 := (hm3.regs .rdi _ h3di).trans (eval_ptr0 24)
  have f3si : reg st3.data .rsi = reg m0 .rcx :=
    (hm3.regs .rsi _ h3si).trans ((hsv2.1 .r12 rfl).trans e112)
  have f3dx : reg st3.data .rdx = reg m0 .r8 :=
    (hm3.regs .rdx _ h3dx).trans ((hsv2.1 .r15 rfl).trans e115)
  have f3cx : reg st3.data .rcx = stackArg m0 0 := (hm3.regs .rcx _ h3cx).trans hy0
  have f3r8 : (reg st3.data .r8).toNat = min (reg m0 .rsi).toNat (stackArg m0 1).toNat := by
    rw [show reg st3.data .r8 = _ from hm3.regs .r8 _ h3r8]
    exact (congrArg BitVec.toNat (hsv2.1 .rbp rfl)).trans e1bp
  have f3r9 : reg st3.data .r9 = reg m0 .r9 :=
    (hm3.regs .r9 _ h3r9).trans (load_ofMachine (o := 16) rfl hw16')
  have f3r13 : reg st3.data .r13 = reg st2.data .rax := hm3.regs .r13 _ h3r13
  have f3r14 : reg st3.data .r14 = reg st2.data .rdx := hm3.regs .r14 _ h3r14
  have f3b : reg st3.data .rbx = o := (hm3.regs .rbx _ h3bx).trans (eval_ptr rfl)
  have hpre3 : RingWeightPre st3.data := by
    unfold RingWeightPre SliceOk ArrOk OptOutOk Readable OffStack
    rw [f3di, f3si, f3dx, f3cx, f3r9]
    have hcb := stackBelow_callee (n' := ringWeightStack) hsp3
      (by simp only [ringWeightStack, ewMulStack]; omega)
    have hcbN := stackBelow_toNat (m := m0) (n := 96 + ringWeightStack)
      (by simp only [ringWeightStack, ewMulStack]; omega)
    have hxs' := apart_callee hx.2 hsp3 hst.1 (n' := ringWeightStack) (by decide)
    unfold NativeRustcVm.Apart at hxs'
    have hxw := hx.1.2
    unfold NoWrap at hxw
    refine ⟨stackOk_callee hst hf3.kept hsp3 (by decide), hr36,
      ⟨⟨Mapped.keeps hpt.1.1 hf3.kept, hpt.1.2⟩, apart_callee hpt.2 hsp3 hst.1 (by decide)⟩,
      ⟨⟨fun j hj ↦ Mapped.keeps hx.1.1 hf3.kept _ (by rw [f3r8] at hj; omega),
        by unfold NoWrap; rw [f3r8]; omega⟩, by unfold Apart; rw [f3r8]; omega⟩,
      ⟨⟨Mapped.keeps hco.1.1 hf3.kept, hco.1.2⟩, apart_callee hco.2 hsp3 hst.1 (by decide)⟩,
      ⟨Mapped.keeps (mapped_off (o := 24) (k := 24) (frame_mapped (F := 96) hst (by decide))
        (by decide)) hf3.kept, ?_⟩, ?_, ?_⟩
    · show (off fb 24).toNat + 24 ≤ 2 ^ 64
      rw [toNat_off (by omega)]
      omega
    · rw [hcb]
      unfold Apart
      rw [toNat_off (by omega), hcbN]
      simp only [ringWeightStack, ewMulStack]
      omega
    · unfold Apart
      rw [toNat_off (by omega), hsp3, BitVec.toNat_add, show (8#64).toNat = 8 from rfl]
      omega
  refine call_then hpc3 hrw hpre3 fun st4 hpc4 hrsp4 ⟨hw4, hs4, hsv4⟩ ↦ ?_
  rw [f3di, f3si, f3dx, f3cx, f3r9, slice_keep hst hs3' hpt, arr_keep hst hs3' hco,
    slice_low (a := stackArg m0 0) (n := stackArg m0 1) f3r8, slice_keep hst hs3' hx] at hw4
  obtain ⟨W, hW⟩ : ∃ W, ringWeight (slice m0 (reg m0 .rcx) (reg m0 .r8))
      ((slice m0 (stackArg m0 0) (stackArg m0 1)).extract 0 (reg m0 .rsi).toNat)
      (arr m0 (reg m0 .r9) coeffCount) = W := ⟨_, rfl⟩
  rw [hW] at hw4
  rw [f3di] at hs4
  have hR4 : ∀ j, j < 24 ∨ 48 ≤ j → j < 96 + 8 → ¬ (NativeRustcVm.InRange (off fb 24) 24 (off fb j) ∨
      NativeRustcVm.InRange (stackBelow st3.data ringWeightStack) ringWeightStack (off fb j)) := by
    rintro j hj hj' (h | h)
    · rw [inRange_off_iff (by omega) (by omega)] at h
      omega
    · exact not_callee hst hsp3 (by decide) hj' h
  have hf4 : Frame m0 96 slots 8 st4.data :=
    Frame.call_slots hf3 hsv4 hrsp4 hs4
      (fun p hp i hi ↦ hR4 _ (by have := slots_le p hp; simp only [slots, List.mem_cons,
        List.not_mem_nil, or_false] at hp; rcases hp with rfl | rfl | rfl | rfl | rfl | rfl <;>
          simp <;> omega) (by have := slots_le p hp; omega))
      (fun j hj ↦ hR4 _ (by omega) (by omega))
  have hs4' : SameOutside m0.dmem st4.data.dmem
      (InRange (stackBelow m0 ringClaimWeightStack) ringClaimWeightStack) :=
    same_trans hs3' hs4 fun q h ↦ h.elim
      (fun h ↦ hstack q (inRange_of_off (N := 96) (by unfold NativeRustcVm.NoWrap; omega)
        (by decide) h))
      (fun h ↦ callee_in hst hsp3 (by decide) h)
  have e4b : reg st4.data .rbx = o := (hsv4.1 .rbx rfl).trans f3b
  have e413 : reg st4.data .r13 = reg st2.data .rax := (hsv4.1 .r13 rfl).trans f3r13
  have e414 : reg st4.data .r14 = reg st2.data .rdx := (hsv4.1 .r14 rfl).trans f3r14
  obtain ⟨hwt, hwe⟩ := hw4
  obtain ⟨hwc0, hwc1⟩ := ewAt_iff.mp hwe
  rw [off_off] at hwc0 hwc1
  rw [off_off] at hwc1
  -- `b2`: the tag, `1`.
  have hwf4 := hwfE st4.data (Host.addrOf (k + NativeRustcVmX64.Vm.RingClaimWeight.b3Offset + b3.length)).toBitVec hf4.kept
  have hm4 : Match (frameEnv m0 st4.data 96 [(xa, 16), (o, 24)] (fun _ ↦ 0)
      (Host.addrOf (k + NativeRustcVmX64.Vm.RingClaimWeight.b3Offset + b3.length)).toBitVec) midS st4.data :=
    match_ofMachine ⟨rfl, rfl, rfl, trivial⟩ ⟨hf4.rsp_eval, known_ptr rfl e4b, trivial⟩ trivial
      trivial ⟨hal _ _ 0 (by decide), hal _ _ 8 (by decide), trivial⟩
  refine exec_at (infix_of b2_in_code (by simp [b2]) hp) exit_b2 hwf4 nofun
    (hpc4.trans (by rw [Nat.add_assoc]; exact congrArg (fun j ↦ Host.addrOf (k + j)) NativeRustcVmX64.Vm.RingClaimWeight.b1_next)) hm4 fun st5 hm5 hpc5 ↦ ?_
  have htag : (frameEnv m0 st4.data 96 [(xa, 16), (o, 24)] (fun _ ↦ 0)
      (Host.addrOf (k + NativeRustcVmX64.Vm.RingClaimWeight.b3Offset + b3.length)).toBitVec).load 0 24 4 = BitVec.ofNat 64 1 :=
    load4_of_tag (Or.inr rfl) hwt
  simp only [PcOk] at hpc5
  sym_simp_at hpc5
  simp only [htag] at hpc5
  simp (config := { decide := true }) only [↓reduceIte] at hpc5
  -- `b3`: `call EW::mul`.
  refine exec_at (infix_of b3_in_code (by simp [b3]) hp) run_b3 hwf4 (fun _ _ ↦ rfl)
    (hpc5.trans (by rw [Nat.add_assoc]; exact congrArg (fun j ↦ Host.addrOf (k + j)) NativeRustcVmX64.Vm.RingClaimWeight.b2_next)) hm5 fun st6 hm6 hpc6 ↦ ?_
  obtain ⟨hmid6, hws6, h6di, h6si, h6dx, h6cx, h6bx⟩ := after_eq run_b3 ▸ ok_b3
  have hf6 : Frame m0 96 slots 0 st6.data := Frame.of_block hf4 hwf4 hm6 hmid6 slots_le
  have hsp6 : rspOf st6.data = fb := by rw [hf6.sp, off_zero]
  have hs6 : SameOutside st4.data.dmem st6.data.dmem (InRange fb 8) :=
    sameOutside_low hwf4 hm6 (r := 0) rfl (by decide) hws6
  have hs6' : SameOutside m0.dmem st6.data.dmem
      (InRange (stackBelow m0 ringClaimWeightStack) ringClaimWeightStack) :=
    same_trans hs4' hs6 fun q h ↦ hstack q (inRange_le h (by decide))
  have g6di : reg st6.data .rdi = reg st2.data .rax := (hm6.regs .rdi _ h6di).trans e413
  have g6si : reg st6.data .rsi = reg st2.data .rdx := (hm6.regs .rsi _ h6si).trans e414
  have g6dx : reg st6.data .rdx = W.c0.toBitVec :=
    (hm6.regs .rdx _ h6dx).trans (load_ofMachine (o := 32) rfl hwc0)
  have g6cx : reg st6.data .rcx = W.c1.toBitVec :=
    (hm6.regs .rcx _ h6cx).trans (load_ofMachine (o := 40) rfl hwc1)
  have g6b : reg st6.data .rbx = o := (hm6.regs .rbx _ h6bx).trans (eval_ptr rfl)
  refine call_then hpc6 hmul (stackOk_callee hst hf6.kept hsp6 (by decide))
    fun st7 hpc7 hrsp7 ⟨h7a, h7d, hs7, hsv7⟩ ↦ ?_
  rw [g6di, g6si, g6dx, g6cx] at h7a h7d
  have hval : ewRet st7.data = StackWeight.eval (.ring (placementArg m0)
      (slice m0 (reg m0 .rcx) (reg m0 .r8)) (arr m0 (reg m0 .r9) coeffCount))
      (slice m0 (stackArg m0 0) (stackArg m0 1)) := by
    have hA : ewArg (reg st2.data .rax) (reg st2.data .rdx) =
        eqAbove (placementArg m0) (slice m0 (stackArg m0 0) (stackArg m0 1)) := by
      rw [show ewArg (reg st2.data .rax) (reg st2.data .rdx) = ewRet st2.data from rfl, hv2]
      simp only [eqAbove, placementArg, slice_size]
    show ewArg (reg st7.data .rax) (reg st7.data .rdx) =
      eqAbove (placementArg m0) (slice m0 (stackArg m0 0) (stackArg m0 1)) *
        ringWeight (slice m0 (reg m0 .rcx) (reg m0 .r8))
          ((slice m0 (stackArg m0 0) (stackArg m0 1)).extract 0 (placementArg m0).variableCount)
          (arr m0 (reg m0 .r9) coeffCount)
    rw [← hA, show (placementArg m0).variableCount = (reg m0 .rsi).toNat from rfl, hW]
    unfold ewArg
    rw [h7a, h7d]
    rfl
  have hR7 : ∀ j, j < 96 + 8 → ¬ InRange (stackBelow st6.data ewMulStack) ewMulStack (off fb j) :=
    fun j hj h ↦ not_callee hst hsp6 (by decide) hj h
  have hf7 : Frame m0 96 slots 8 st7.data :=
    Frame.call_slots hf6 hsv7 hrsp7 hs7
      (fun p hp i hi ↦ hR7 _ (by have := slots_le p hp; omega)) (fun j hj ↦ hR7 _ (by omega))
  have hs7' : SameOutside m0.dmem st7.data.dmem
      (InRange (stackBelow m0 ringClaimWeightStack) ringClaimWeightStack) :=
    same_trans hs6' hs7 fun q h ↦ callee_in hst hsp6 (by decide) h
  have e7b : reg st7.data .rbx = o := (hsv7.1 .rbx rfl).trans g6b
  -- `b4`, `b6`: the product and the tag `1` stored, the epilogue.
  have hwf7 := hwfE st7.data 0 hf7.kept
  have hm7 : Match (frameEnv m0 st7.data 96 [(xa, 16), (o, 24)] (fun _ ↦ 0) 0) midS st7.data :=
    match_ofMachine ⟨rfl, rfl, rfl, trivial⟩ ⟨hf7.rsp_eval, known_ptr rfl e7b, trivial⟩ trivial
      trivial ⟨hal _ _ 0 (by decide), hal _ _ 8 (by decide), trivial⟩
  refine exec_at (infix_of b4_in_code (by simp [b4]) hp) run_b4 hwf7 nofun
    (hpc7.trans (by rw [Nat.add_assoc]; exact congrArg (fun j ↦ Host.addrOf (k + j)) NativeRustcVmX64.Vm.RingClaimWeight.b3_next)) hm7 fun st8 hm8 hpc8 ↦ ?_
  simp only [PcOk] at hpc8
  refine exec_at (infix_of b6_in_code (by simp [b6]) hp) (exec_after run_b4 run_b6) hwf7 nofun
    (hpc8.trans (hp.label NativeRustcVmX64.Vm.RingClaimWeight.label_3_at)) hm8 fun st9 hm9 hpc9 ↦ ?_
  obtain ⟨hepi, hw0, hw1, hw2, hws9⟩ := after_eq run_b6 ▸ ok_s
  obtain ⟨hsv9, hrsp9⟩ := Frame.epilogue hf7 hwf7 hm9 hepi
  have hs9 := sameOutside_region hwf7 hm9 (r := 2) rfl hws9
  have ht := wordAt_write hm9 (r := 2) (o := 0) rfl (by decide)
    (fun i hi ↦ by rw [Nat.zero_add]; exact hw0 i hi)
  rw [off_zero, show UInt64.ofBitVec ((Sym.lit 1).eval
    (frameEnv m0 st7.data 96 [(xa, 16), (o, 24)] (fun _ ↦ 0) 0)) = 1 from rfl] at ht
  have hc0 := wordAt_write hm9 (r := 2) (o := 8) rfl (by decide) hw1
  have hc1 := wordAt_write hm9 (r := 2) (o := 16) rfl (by decide) hw2
  simp only [PcOk] at hpc9
  refine .done _ ⟨by rw [hpc9]; exact hf7.load_ret hst (by decide), hrsp9, ?_, ?_, hsv9⟩
  · refine ⟨ht, ?_⟩
    rw [← hval]
    exact ewAt_iff.mpr ⟨hc0, by rw [off_off]; exact hc1⟩
  · intro q hq
    rw [hs9 q fun h ↦ hq (.inl h)]
    exact hs7' q fun h ↦ hq (.inr h)

end

end NativeRustcVmX64.Ring.Claim
