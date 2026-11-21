module

public import NativeVm.Code.Phase6.LayerA3

/-!
# A layer's instance weights, `κ` and the sumcheck's claim

From the challenge `s` at `eS`: its powers (`pure_pow`), the instance weights
`keccakInstanceWeights s` (`pure_mu`), `κ` (`pure_kappa`), the claim `polyEval product s` of the
sumcheck over the point (`pure_pev`).
-/

@[expose] public section

namespace NativeVm.Code.P6

open Native NativeVm.Model NativeVm.Code LeanVM.Parameters Finset
open NativeVm.Transcript (wd wdisp Env rf_trans)
open NativeVm.Field (eOf eOf_inj emul emul_spec eRegs eadd eadd_spec eOf_zero epolyEval epolyEval_spec
  polyRegs)

variable {env : Env} {inp : Input} {s0 s : QState} {t : TState} {g : Nat → EW} {p : UInt64}

/-- Instance weight `e`, `e` in `r15`. -/
def muVal : Stmt := blk (idx16 ++ [I (.load .rbx (ix (2 * eEmbed))), msum ePow 24])

/-- The instance weights. -/
def muC : List Stmt := [blk [I (.movi .r14 0), tab eMu (.imm (Int64.ofNat 16)) muVal],
  blk (setW eMuN 16)]

theorem pure_mu (hin : Inputs env inp s0.mem) (hc : Cn g) {x : EW}
    (hpow : ∀ b < 24, (g (ePow + b)).toE = x.toE ^ b) :
    Pure6 env s0 (blk muC) g (Function.update (ovr g eMu 16 fun e ↦
      (keccakInstanceWeights x).getD e 0) eMuN (EW.ofK (16 : Nat).toUInt64)) := by
  refine Pure6.cons (pure_tab hin (Lv := mRegs) (by p6_omega) (by decide) fun m hm s hp hs h15 ↦ ?_)
    (Pure6.single (pure_setW hin (by p6_omega)))
  unfold muVal
  refine idx16_spec h15 ?_
  have hE : (ovr g eMu m (fun e ↦ (keccakInstanceWeights x).getD e 0) (eEmbed + m)).c0 =
      NativeVm.Equiv.rmfeEmbedWLit.getD m 0 := by
    rw [ovr_out (by p6_omega), hc.2.2.2.2.2.2.2.1 m (lt_of_lt_of_eq hm rfl)]
    exact tEmbed_spec m hm
  refine ldi0 (o := eEmbed) (i := m) (by simpa using hp) (by rax_tac) hs (by p6_omega) ?_
  rw [hE]
  refine WP.blk_cons (WP.mono (msum_spec (src := ePow) (n := 24) (p := sb env)
    (mask := NativeVm.Equiv.rmfeEmbedWLit.getD m 0) (by simpa using hp) hs (by p6_omega) (by omega)
    (by simp)) (fun s1 ⟨e1, e2, e3⟩ ↦ WP.blk_nil ⟨?_, ?_, ?_⟩) (fun _ h ↦ h))
  · rw [e1, instanceWeights_getD x hm]
    refine sum_congr rfl fun b hb ↦ ?_
    have := mem_range.1 hb
    rw [ovr_out (by p6_omega), hpow b this]
  · rw [e2]; rfl
  · exact rf_trans (l := [.rax, .rbx]) (l'' := mRegs) (by rf_tac) e3

/-- `polyEval` of the product's coefficients at `s`. -/
def pevC : Stmt :=
  blk ([I (.lea .r13 (at_ .rbp (wdisp (2 * eProd)))), I (.movi .r15 (Int64.ofNat 47))] ++ ldB eS ++
    [epolyEval])

theorem pure_pev (hin : Inputs env inp s0.mem) :
    Pure6 env s0 (blk (pevC :: stEl eSC)) g (Function.update g eSC
      (EW.ofE (LeanVM.Protocol.Verifier.polyEval (vals g eProd 47) (g eS).toE))) :=
  pure_el hin (L := [.r11, .r12] ++ polyRegs) (by p6_omega) (by decide) fun s hp hs ↦ by
    unfold pevC
    simp only [List.cons_append, List.nil_append]
    refine NativeVm.Transcript.wp_reg (by rfl) (NativeVm.Transcript.wp_reg (by rfl) ?_)
    rw [← List.singleton_append]
    refine ldB_spec (by simpa using hp) (hs.congr fun _ _ ↦ rfl) (by p6_omega) ?_
    have hE := hs.earr (o := eProd) (n := 47) (by p6_omega)
    refine WP.blk_cons (WP.mono (epolyEval_spec (cs := vals g eProd 47) ?_ ?_ (by simp [vals]))
      (fun s1 ⟨e1, e2, e3⟩ ↦ WP.blk_nil ⟨?_, e2, ?_⟩) (fun _ h ↦ h))
    · simp only [QState.setReg_reg, QState.setReg_mem, reduceCtorEq, ↓reduceIte, eval_el hp]
      exact hE
    · simp only [QState.setReg_reg, reduceCtorEq, ↓reduceIte, vals, List.length_map,
        List.length_range]
      rfl
    · rw [e1, NativeVm.Equiv.EW.toE_ofE]
      simp only [QState.setReg_reg, reduceCtorEq, ↓reduceIte, eOf_toE]
    · exact rf_trans (l := [.r13, .r15, .r11, .r12]) (by rf_tac) e3

end NativeVm.Code.P6
