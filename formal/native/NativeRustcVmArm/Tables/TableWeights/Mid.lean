module

public import NativeRustcVmArm.Code.Vm.EWMul.Names
public import NativeRustcVmArm.Tables.TableWeights.Places

/-!
# `table_weights`: the multiplications of a coordinate

`b4` to `b8` each store the product of the previous multiplication in weight `j - 1`'s places and
multiply weight `j` by coordinate `c`'s factor or challenge (`mid_step`, from the block's literal
result: `MidBlock`). `b3` does the first multiplication (`first_step`).
-/

namespace NativeRustcVmArm.Tables.TableWeights

open NativeRustcArm NativeRustcArm.Sym NativeVm.Model NativeRustcVm.Tables
open NativeRustcVm (wordOf)

@[expose] public section

/-- The factor operand X2 of a multiplication by weight `j`, the challenge's low limb `x`. -/
def fac2 (j : Nat) (x : Sym) : Sym :=
  .bin .eor .W64 (.ite (.cmp .ult .W64 (.reg .X22) (.load 0 (hoff j) 8)) (.reg .X25) (.lit 0)) x

/-- The factor operand X3 of a multiplication by weight `j`. -/
def fac3 (j : Nat) : Sym :=
  .ite (.cmp .ult .W64 (.reg .X22) (.load 0 (hoff j) 8)) (.reg .X26) (.reg .X24)

/-- **What a block of the multiplications does** (`b4` to `b8`, the `j`th): the product in weight
`j - 1`'s places, weight `j` and the factor in X0 to X3, the other weights, the kept words and the
loop's registers untouched, only the frame written, SP the frame's base. -/
structure MidBlock (j : Nat) (S : SState) : Prop where
  sp : S.sp = .ptr 0 0
  writes : FrameWrites S 240
  x0 : S.reg .X0 = some (lo j).sym
  x1 : S.reg .X1 = some (hi j).sym
  x2 : S.reg .X2 = some (fac2 j (.reg .X29))
  x3 : S.reg .X3 = some (fac3 j)
  lo_prev : (lo (j - 1)).after S = some (.reg .X0)
  hi_prev : (hi (j - 1)).after S = some (.reg .X1)
  keep : ∀ i < 6, i ≠ j - 1 → (lo i).after S = some (lo i).sym ∧ (hi i).after S = some (hi i).sym
  regs : ∀ r ∈ [XReg.X22, .X23, .X24, .X25, .X26, .X27, .X29], S.reg r = some (.reg r)
  slots : ∀ p ∈ koffs, loadSym S.mem 0 p 8 = .load 0 p 8

end

public section

variable {m0 : MachineData}

theorem koffs_eq : (kslots m0).map Prod.fst = koffs := rfl

/-- The factor passed `EW::mul`. -/
theorem factor_of [Labels] {m : MachineData} {rs : List (BitVec 64 × Nat)} {c j : Nat} {x : Sym}
    (hc : c < 2 ^ 64) (hj : j < 6) (hf : Frm m0 m) (x22 : rg m .X22 = BitVec.ofNat 64 c)
    (x25 : rg m .X25 = ((fac m0 c).c0 ^^^ (ch m0 c).c0).toBitVec)
    (x26 : rg m .X26 = (fac m0 c).c1.toBitVec)
    (hx : x.eval (Env.ofMachine m ((fb m0, 240) :: rs)) = (ch m0 c).c0.toBitVec)
    (x24 : rg m .X24 = (ch m0 c).c1.toBitVec) :
    (⟨.ofBitVec ((fac2 j x).eval (Env.ofMachine m ((fb m0, 240) :: rs))),
      .ofBitVec ((fac3 j).eval (Env.ofMachine m ((fb m0, 240) :: rs)))⟩ : EW) =
      if c < (H m0).getD j 0 then fac m0 c else ch m0 c := by
  have hh : fw m0 m (hoff j) = hword m0 j := hf.slots (hoff j, hword m0 j) (hoff_mem hj)
  simp only [fac2, fac3, Sym.eval, SBool.eval, CmpOp.apply, BinOp.apply, low_W64, ext_W64,
    load_fw, hh, Env.ofMachine_regs]
  rw [show (m.regs.getXReg .X22).toBitVec = BitVec.ofNat 64 c from x22]
  exact factor_eq hc hj x25 x26 hx x24

variable [Host]

/-- **A multiplication of coordinate `c`** after the first: weight `j` updated. -/
theorem mid_step {j : Nat} (hj1 : 1 ≤ j) (hj5 : j ≤ 5) {ds : List Directive} {kk : Nat}
    (hk : ds.IsInfixAt Host.prog kk) {S' : SState}
    (hx : exec ds midS = some (S', .call NativeRustcVmArm.Vm.EWMul.entryLabel)) (hb : MidBlock j S')
    (hmul : Spec (label NativeRustcVmArm.Vm.EWMul.entryLabel) EWMulPre EWMulPost) (hg : Geo m0) {c : Nat}
    {m : MachineData} (hmid : Mid m0 c (j - 1) m) :
    Eventually (step1 Host.exe)
      (fun st => st.pc = Host.addrOf (kk + ds.length) ∧ Mid m0 c j st.data)
      ⟨m, Host.addrOf kk⟩ := by
  have hf := hmid.frm
  let env := Env.ofMachine m [(fb m0, 240)]
  have hwf : env.WF :=
    Env.wf_of ⟨⟨hf.frameOk hg |>.mapped, hg.hi⟩, trivial⟩ (List.pairwise_singleton _ _)
  have hm : Match env midS m := match_frame (rs := []) (srs := []) (known := []) (aliases := []) hg hf trivial trivial trivial
  have hc : c < 2 ^ 64 := Nat.lt_of_lt_of_le hmid.lt (UInt64.toNat_lt _).le
  refine exec_then hk hx hwf hm fun st hm' hpc => ?_
  refine call_mul hwf rfl (hf.frameOk hg) hm' hpc hb.sp hb.writes hb.x0 hb.x1 hb.x2 hb.x3 hmul
    fun st' hpc' hx0 hx1 hsv hsp hwd hsame hkept => .done _ ⟨hpc', ?_⟩
  have hreg : ∀ r ∈ [XReg.X22, .X23, .X24, .X25, .X26, .X27, .X29], rg st'.data r = rg m r :=
    fun r hr => hsv r _ (by simp at hr; rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      rfl) (hb.regs r hr)
  have hwj : WAt m0 m j ((W m0 c).getD j 0) := by
    have := hmid.w j (by omega) (by omega)
    simp only [show ¬(j < j - 1) by omega, ↓reduceIte] at this
    exact this
  have hprod : mulOf env (lo j).sym (hi j).sym (fac2 j (.reg .X29)) (fac3 j) =
      (W m0 (c + 1)).getD j 0 := by
    rw [mulOf, weight_of hwj, factor_of (rs := []) (x := .reg .X29) hc (by omega) hf hmid.x22
      hmid.x25 hmid.x26 hmid.x29 hmid.x24, W_succ hmid.lt (by omega)]
  refine ⟨hmid.lt, frm_after hf hsp hwd (by rw [koffs_eq]; exact hb.slots) hsame hkept,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun i hi hij => ?_⟩
  · rw [hreg .X22 (by simp)]; exact hmid.x22
  · rw [hreg .X23 (by simp)]; exact hmid.x23
  · rw [hreg .X27 (by simp)]; exact hmid.x27
  · rw [hreg .X29 (by simp)]; exact hmid.x29
  · rw [hreg .X24 (by simp)]; exact hmid.x24
  · rw [hreg .X25 (by simp)]; exact hmid.x25
  · rw [hreg .X26 (by simp)]; exact hmid.x26
  · show st'.data.regs.X0.toBitVec = _
    rw [hx0, hprod]
  · show st'.data.regs.X1.toBitVec = _
    rw [hx1, hprod]
  · by_cases hi1 : i = j - 1
    · subst hi1
      simp only [show j - 1 < j by omega, ↓reduceIte]
      refine ⟨?_, ?_⟩
      · rw [Pl.val_after hsv hwd lo_ok hb.lo_prev]; exact hmid.x0
      · rw [Pl.val_after hsv hwd hi_ok hb.hi_prev]; exact hmid.x1
    · obtain ⟨hl, hh⟩ := hb.keep i hi hi1
      have hw := hmid.w i hi hi1
      have e : (if i < j - 1 then c + 1 else c) = (if i < j then c + 1 else c) := by
        split_ifs <;> first | rfl | omega
      rw [e] at hw
      refine ⟨?_, ?_⟩
      · rw [Pl.val_after hsv hwd lo_ok hl, Pl.sym_eval]; exact hw.1
      · rw [Pl.val_after hsv hwd hi_ok hh, Pl.sym_eval]; exact hw.2

end

end NativeRustcVmArm.Tables.TableWeights
