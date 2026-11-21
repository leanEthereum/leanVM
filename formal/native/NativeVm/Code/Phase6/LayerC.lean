module

public import NativeVm.Code.Phase6.LayerB

/-!
# A layer's bit-position equality weights and its second check

`pure_eq`: `eqKernel` of the bit-position point at `eLp`, `2^keccakLocalBits` entries, at `eEq`;
`pure_dot`: their `dot` with the claim's weights; `chk2_refines`: the second check.
-/

@[expose] public section

namespace NativeVm.Code.P6

open Native NativeVm.Model NativeVm.Code LeanVM.Parameters Finset
open NativeVm.Transcript (wd wdisp Env rf_trans)
open NativeVm.Field (eOf eOf_inj emul emul_spec eRegs eadd eadd_spec eOf_zero)

variable {env : Env} {inp : Input} {s0 s : QState} {t : TState} {g : Nat → EW} {p : UInt64}

/-- The bit-position equality weights. -/
def eqC : List Stmt := [blk (setW eKn 11), blk (setW eKd 0),
  blk [I (.movi .r14 0), tab eEq (.imm (Int64.ofNat 2048)) (blk [I (.mov .r13 .r15), ekern eLp])]]

theorem pure_eq (hin : Inputs env inp s0.mem) {lp : Array EW} (hsz : lp.size = 11)
    (hlp : ∀ k < 11, g (eLp + k) = lp.getD k 0) :
    Pure6 env s0 (blk eqC) g (ovr (Function.update (Function.update g eKn
      (EW.ofK (11 : Nat).toUInt64)) eKd (EW.ofK (0 : Nat).toUInt64)) eEq 2048
      fun m ↦ (eqKernel lp).getD m 0) := by
  refine Pure6.cons (pure_setW hin (by p6_omega)) (Pure6.cons (pure_setW hin (by p6_omega))
    (Pure6.single (pure_tab hin (Lv := .r13 :: kernRegs) (by p6_omega) (by decide)
      fun m hm s hp hs h15 ↦ ?_)))
  refine NativeVm.Transcript.wp_reg (by rfl) ?_
  refine WP.mono (ekern_spec (o := eLp) (i := m) (n := 11) (d := 0) (by simpa using hp)
    (hs.congr fun _ _ ↦ rfl) (by rw [ovr_out (by p6_omega), Function.update_of_ne (by p6_ne),
      Function.update_self]) (by rw [ovr_out (by p6_omega), Function.update_self])
    (by simp [h15]) (by omega) (by omega) (by p6_omega))
    (fun s' ⟨h1, h2, h3⟩ ↦ ⟨?_, h2, rf_trans (l := [.r13]) (by rf_tac) h3⟩) (fun _ h ↦ h)
  rw [h1, eqKernel_getD lp (by rw [hsz]; omega), hsz]
  refine prod_congr rfl fun k hk ↦ ?_
  have := mem_range.1 hk
  rw [kfac, ovr_out (by p6_omega), Function.update_of_ne (by p6_omega),
    Function.update_of_ne (by p6_omega), Nat.add_zero, hlp k this]

/-- `dot` of the equality weights and the claim's weights. -/
def dotC : Stmt := ssum (.imm (Int64.ofNat 1600)) (dterm eEq eW)

theorem pure_dot (hin : Inputs env inp s0.mem) :
    Pure6 env s0 (blk (dotC :: stEl eVal)) g (Function.update g eVal
      (EW.ofE (∑ i ∈ range 1600, (g (eEq + i)).toE * (g (eW + i)).toE))) :=
  pure_el hin (L := sumRegs ++ dRegs) (by p6_omega) (by decide) fun s hp hs ↦
    WP.mono (ssum_spec (N := 1600) (Lt := dRegs) (T := fun i ↦ (g (eEq + i)).toE * (g (eW + i)).toE)
      (by decide) (by omega) (fun _ _ ↦ rfl) (fun i hi t ht h15 hm ↦ dterm_spec
        (by rw [sum_frame ht (by decide)]; exact hp) (hs.congr fun a _ ↦ by rw [hm])
        (by p6_omega) (by p6_omega) h15))
      (fun s' ⟨h1, h2, h3⟩ ↦ ⟨by rw [h1, NativeVm.Equiv.EW.toE_ofE], h2, h3⟩) (fun _ h ↦ h)

/-- `κ · t_0`. -/
def kt0C : List Stmt := ldA eKappa ++ ldB eT ++ [emul]

theorem pure_kt0 (hin : Inputs env inp s0.mem) :
    Pure6 env s0 (blk (blk kt0C :: stEl eMsg)) g (Function.update g eMsg
      (EW.ofE ((g eKappa).toE * (g eT).toE))) :=
  pure_el hin (L := eRegs ++ [.r11, .r12]) (by p6_omega) (by decide) fun s hp hs ↦ by
    unfold kt0C
    refine ldA_spec hp hs (by p6_omega) ?_
    refine ldB_spec (by simpa using hp) (hs.congr fun _ _ ↦ rfl) (by p6_omega) ?_
    refine WP.mono (emul_spec _) (fun s' ⟨h1, h2, h3⟩ ↦ ⟨?_, h2, ?_⟩) (fun _ h ↦ h)
    · rw [h1, NativeVm.Equiv.EW.toE_ofE]
      simp only [QState.setReg_reg, reduceCtorEq, ↓reduceIte, eOf_toE]
    · exact rf_trans (l := [.r9, .r10, .r11, .r12]) (by rf_tac) h3

/-- The second check: `dot · (κ t_0 + (κ + t_1) t_2)` against the sumcheck's claim. -/
def chk2C : List Stmt := ldA eKappa ++ ldB (eT + 1) ++ [eadd] ++ ldB (eT + 2) ++ [emul] ++
  ldB eMsg ++ [eadd] ++ ldB eVal ++ [emul] ++ chkEl eSC

theorem chk2_refines (hin : Inputs env inp s0.mem) {y : EW}
    (hy : y.toE = (g eVal).toE * ((g eMsg).toE + ((g eKappa).toE + (g (eT + 1)).toE) *
      (g (eT + 2)).toE)) :
    Refines (St env s0 g) (blk chk2C) (Model.require (y == g eSC)) (fun _ t s ↦ St env s0 g t s)
      (Kept env rs6 s0) := by
  intro t s h
  unfold chk2C
  simp only [List.append_assoc]
  refine ldA_spec h.2.2.1 h.2.2.2 (by p6_omega) ?_
  refine ldB_spec (by simpa using h.2.2.1) (h.2.2.2.congr fun _ _ ↦ rfl) (by p6_omega) ?_
  refine WP.blk_cons (WP.mono (eadd_spec _) (fun s1 ⟨e1, e2, e3⟩ ↦ ?_) (fun _ h ↦ h))
  have h1 : St env s0 g t s1 :=
    (((h.setReg (r := .r9) (by decide) (by decide) _).setReg (r := .r10) (by decide) (by decide) _).setReg
      (r := .r11) (by decide) (by decide) _ |>.setReg (r := .r12) (by decide) (by decide) _).frame hin
      e2 e3
  refine ldB_spec h1.2.2.1 h1.2.2.2 (by p6_omega) ?_
  refine WP.blk_cons (WP.mono (emul_spec _) (fun s2 ⟨f1, f2, f3⟩ ↦ ?_) (fun _ h ↦ h))
  have h2 : St env s0 g t s2 :=
    ((h1.setReg (r := .r11) (by decide) (by decide) _).setReg (r := .r12) (by decide) (by decide)
      _).frame hin f2 f3
  refine ldB_spec h2.2.2.1 h2.2.2.2 (by p6_omega) ?_
  refine WP.blk_cons (WP.mono (eadd_spec _) (fun s3 ⟨k1, k2, k3⟩ ↦ ?_) (fun _ h ↦ h))
  have h3 : St env s0 g t s3 :=
    ((h2.setReg (r := .r11) (by decide) (by decide) _).setReg (r := .r12) (by decide) (by decide)
      _).frame hin k2 k3
  refine ldB_spec h3.2.2.1 h3.2.2.2 (by p6_omega) ?_
  refine WP.blk_cons (WP.mono (emul_spec _) (fun s4 ⟨m1, m2, m3⟩ ↦ ?_) (fun _ h ↦ h))
  have h4 : St env s0 g t s4 :=
    ((h3.setReg (r := .r11) (by decide) (by decide) _).setReg (r := .r12) (by decide) (by decide)
      _).frame hin m2 m3
  refine chkEl_refines (by p6_omega) y t s4 ⟨h4, ?_⟩
  rw [m1, hy]
  simp only [QState.setReg_reg, reduceCtorEq, ↓reduceIte]
  rw [k1]
  simp only [QState.setReg_reg, reduceCtorEq, ↓reduceIte]
  rw [f1]
  simp only [QState.setReg_reg, reduceCtorEq, ↓reduceIte]
  rw [e1]
  simp only [QState.setReg_reg, reduceCtorEq, ↓reduceIte, eOf_toE]
  ring

end NativeVm.Code.P6
