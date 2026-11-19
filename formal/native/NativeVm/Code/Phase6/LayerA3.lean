module

public import NativeVm.Code.Phase6.LayerA2

/-!
# A layer's `iota`, the instance weights' sum, the first check

`pure_iota`: `Σ_seg segW_seg · Σ_z [bit z of RC[12 (seg + 1) - step - 1]] w_z`; `pure_sumMu`:
`Σ_i mu_i`; `chk1C`: `projected + iota · Σ mu` against the claim's value.
-/

@[expose] public section

namespace NativeVm.Code.P6

open Native NativeVm.Model NativeVm.Code LeanVM.Parameters Finset
open NativeVm.Transcript (wd wdisp Env rf_trans)
open NativeVm.Field (eOf eOf_inj emul emul_spec eRegs eadd eadd_spec eOf_zero)

variable {env : Env} {inp : Input} {s0 s : QState} {t : TState} {g : Nat → EW} {p : UInt64}

/-- Segment `seg`'s share of `iota`. -/
def iotaSeg (seg : Nat) : List Stmt := [I (.movi .rax (Int64.ofNat (12 * (seg + 1) - 1))),
  I (.load .rdx (at_ .rbp (wdisp (2 * eStep)))), I (.sub .rax .rdx), I (.shli .rax 4),
  I (.load .rbx (ix (2 * eRC))), msum eW 64, I (.mov .r11 .r9), I (.mov .r12 .r10)] ++
  ldA (eSegW + seg) ++ [emul]

/-- Segment `seg`'s share's value. -/
def iotaV (g : Nat → EW) (step seg : Nat) : LeanVM.Parameters.E :=
  (g (eSegW + seg)).toE * ∑ z ∈ range 64,
    if testBitW (keccakRCLit.getD (12 * (seg + 1) - step - 1) 0) z then (g (eW + z)).toE else 0

theorem iotaSeg_spec {step seg : Nat} (hp : s.reg .rbp = p) (hs : Scr s.mem p g) (hc : Cn g)
    (hst : g eStep = EW.ofK step.toUInt64) (hstep : step < 12) (hseg : seg < 2) {E : QState → Prop} :
    WP (blk (iotaSeg seg)) s (fun s' ↦ eOf (s'.reg .r9) (s'.reg .r10) = iotaV g step seg ∧
      s'.mem = s.mem ∧ RegsFrame pRegs s s') E := by
  have hidx : 12 * (seg + 1) - step - 1 < 24 := by omega
  have hrc : (g (eRC + (12 * (seg + 1) - step - 1))).c0 = keccakRCLit.getD (12 * (seg + 1) - step - 1) 0 := by
    rw [hc.1 _ (by rw [show tRC.length = 24 from rfl]; exact hidx)]
    exact tRC_spec _ hidx
  unfold iotaSeg
  simp only [List.cons_append, List.nil_append]
  fstep
  refine ld0 (by simpa using hp) (hs.congr fun _ _ ↦ rfl) (by p6_omega) ?_
  rw [hst]
  fstep; fstep
  have hsub : (Int64.ofNat (12 * (seg + 1) - 1)).toUInt64 - (EW.ofK step.toUInt64).c0 =
      (12 * (seg + 1) - step - 1).toUInt64 := by
    rw [show (EW.ofK step.toUInt64).c0 = step.toUInt64 from rfl,
      show (Int64.ofNat (12 * (seg + 1) - 1)).toUInt64 = (12 * (seg + 1) - 1).toUInt64 from rfl]
    apply UInt64.toNat_inj.mp
    rw [UInt64.toNat_sub_of_le _ _ ((NativeVm.Transcript.toUInt64_le (by omega) (by omega)).mpr
      (by omega)), toNat_toUInt64' (by omega), toNat_toUInt64' (by omega),
      toNat_toUInt64' (by omega)]
    omega
  refine ldi0 (o := eRC) (i := 12 * (seg + 1) - step - 1) (by simpa using hp)
    (by simp only [QState.setReg_reg, ↓reduceIte]; rw [hsub]; exact rax16 _)
    (hs.congr fun _ _ ↦ rfl) (by p6_omega) ?_
  rw [hrc]
  refine WP.blk_cons (WP.mono (msum_spec (src := eW) (n := 64) (f := g) (p := p)
    (mask := keccakRCLit.getD (12 * (seg + 1) - step - 1) 0)
    (by simpa using hp) (hs.congr fun _ _ ↦ rfl) (by p6_omega) (by omega) (by simp))
    (fun s1 ⟨e1, e2, e3⟩ ↦ ?_) (fun _ h ↦ h))
  have hp1 : s1.reg .rbp = p := by rw [e3 .rbp (by decide)]; simpa using hp
  fstep; fstep
  refine ldA_spec (by simpa using hp1) (hs.congr fun a _ ↦ by simp [e2]) (by p6_omega) ?_
  refine WP.blk_cons (WP.mono (emul_spec _) (fun s2 ⟨f1, f2, f3⟩ ↦ WP.blk_nil ⟨?_, ?_, ?_⟩)
    (fun _ h ↦ h))
  · rw [f1]; simp only [QState.setReg_reg, reduceCtorEq, ↓reduceIte]
    rw [e1, eOf_toE]; rfl
  · rw [f2]; simp [e2]
  · exact rf_trans (rf_trans (l := [.rax, .rdx, .rbx]) (l'' := pRegs) (by rf_tac) e3)
      (rf_trans (l := [.r11, .r12, .r9, .r10]) (l'' := pRegs) (by rf_tac) f3)

/-- `iota`. -/
def iotaC : List Stmt := [blk (blk (iotaSeg 0) :: stEl eVal),
  blk (blk (iotaSeg 1 ++ ldB eVal ++ [eadd]) :: stEl eIota)]

theorem pure_iota (hin : Inputs env inp s0.mem) {step : Nat} (hc : Cn g)
    (hst : g eStep = EW.ofK step.toUInt64) (hstep : step < 12) :
    ∃ g', Pure6 env s0 (blk iotaC) g g' ∧ (∀ i, i ≠ eVal → i ≠ eIota → g' i = g i) ∧
      (g' eIota).toE = iotaV g step 1 + iotaV g step 0 := by
  set g1 := Function.update g eVal (EW.ofE (iotaV g step 0))
  have hc1 : Cn g1 := hc.congr fun i h1 _ ↦ Function.update_of_ne (by p6_omega) _ _
  have hst1 : g1 eStep = EW.ofK step.toUInt64 := by
    simp only [g1]; rw [Function.update_of_ne (by p6_ne), hst]
  have hv1 : iotaV g1 step 1 = iotaV g step 1 := by
    simp only [iotaV, g1]
    rw [Function.update_of_ne (by p6_ne)]
    congr 1
  refine ⟨Function.update g1 eIota (EW.ofE (iotaV g step 1 + iotaV g step 0)),
    Pure6.cons (pure_el hin (by p6_omega) (L := pRegs) (by decide) fun s hp hs ↦
      WP.mono (iotaSeg_spec hp hs hc hst hstep (seg := 0) (by omega))
        (fun s' ⟨h1, h2, h3⟩ ↦ ⟨by rw [h1, NativeVm.Equiv.EW.toE_ofE], h2, h3⟩) (fun _ h ↦ h))
      (Pure6.single (pure_el hin (by p6_omega) (L := pRegs) (by decide) fun s hp hs ↦ ?_)),
    fun i h1 h2 ↦ by simp only [g1]; rw [Function.update_of_ne h2, Function.update_of_ne h1],
    by rw [Function.update_self, NativeVm.Equiv.EW.toE_ofE]⟩
  rw [List.append_assoc]
  refine Native.Keccak.Proof.wp_blk_append (WP.mono (iotaSeg_spec hp hs hc1 hst1 hstep (seg := 1)
    (by omega)) (fun s1 ⟨e1, e2, e3⟩ ↦ ?_) (fun _ h ↦ h))
  have hp1 : s1.reg .rbp = sb env := (e3 .rbp (by decide)).trans hp
  refine ldB_spec hp1 (hs.congr fun a _ ↦ by rw [e2]) (by p6_omega) ?_
  refine WP.blk_cons (WP.mono (eadd_spec _) (fun s2 ⟨f1, f2, f3⟩ ↦ WP.blk_nil ⟨?_, ?_, ?_⟩)
    (fun _ h ↦ h))
  · rw [f1]
    simp only [QState.setReg_reg, reduceCtorEq, ↓reduceIte]
    rw [e1, eOf_toE, hv1, NativeVm.Equiv.EW.toE_ofE]
    simp only [Function.update_self, NativeVm.Equiv.EW.toE_ofE]
  · rw [f2]; simp [e2]
  · exact rf_trans (l'' := pRegs) e3 (rf_trans (l := [.r11, .r12]) (l'' := pRegs) (by rf_tac) f3)

/-- The sum of the instance weights. -/
def sumMuC : Stmt := blk [I (.load .r14 (at_ .rbp (wdisp (2 * eMuN)))), ssum (.reg .r14) (lterm eMu)]

theorem pure_sumMu (hin : Inputs env inp s0.mem) {n o : Nat} (hn : g eMuN = EW.ofK n.toUInt64)
    (hn16 : n ≤ 16) (ho : o < scrN) :
    Pure6 env s0 (blk (sumMuC :: stEl o)) g
      (Function.update g o (EW.ofE (∑ i ∈ range n, (g (eMu + i)).toE))) :=
  pure_el hin (L := .r14 :: sumRegs ++ [.rax, .r9, .r10]) ho (by decide) fun s hp hs ↦ by
    unfold sumMuC
    refine ld0 hp hs (by p6_omega) ?_
    rw [hn]
    refine WP.blk_cons (WP.mono (ssum_spec (N := n) (Lt := [.rax, .r9, .r10])
      (T := fun i ↦ (g (eMu + i)).toE) (by decide) (by omega) (fun t ht ↦ ?_)
      (fun i hi t ht h15 hm ↦ lterm_spec (by rw [sum_frame ht (by decide)]; simpa using hp)
        (hs.congr fun a _ ↦ by rw [hm]; rfl) (by p6_omega) h15))
      (fun s1 ⟨e1, e2, e3⟩ ↦ WP.blk_nil ⟨by rw [e1, NativeVm.Equiv.EW.toE_ofE], e2, ?_⟩)
      (fun _ h ↦ h))
    · rw [Rhs.eval, sum_frame ht (by decide)]; simp [EW.ofK]
    · exact rf_trans (l := [.r14]) (by rf_tac) e3

/-- The first check: `projected + iota · Σ mu` against the claim's value. -/
def chk1C : List Stmt := ldA eIota ++ ldB eSumMu ++ [emul] ++ ldB eProj ++ [eadd] ++ chkEl eCV

theorem chk1_refines (hin : Inputs env inp s0.mem) {y : EW}
    (hy : y.toE = (g eProj).toE + (g eIota).toE * (g eSumMu).toE) :
    Refines (St env s0 g) (blk chk1C) (Model.require (y == g eCV)) (fun _ t s ↦ St env s0 g t s)
      (Kept env rs6 s0) := by
  intro t s h
  unfold chk1C
  simp only [List.append_assoc]
  refine ldA_spec h.2.2.1 h.2.2.2 (by p6_omega) ?_
  refine ldB_spec (by simpa using h.2.2.1) (h.2.2.2.congr fun _ _ ↦ rfl) (by p6_omega) ?_
  refine WP.blk_cons (WP.mono (emul_spec _) (fun s1 ⟨e1, e2, e3⟩ ↦ ?_) (fun _ h ↦ h))
  have h1 : St env s0 g t s1 :=
    (((h.setReg (r := .r9) (by decide) (by decide) _).setReg (r := .r10) (by decide) (by decide) _).setReg
      (r := .r11) (by decide) (by decide) _ |>.setReg (r := .r12) (by decide) (by decide) _).frame hin
      e2 e3
  refine ldB_spec h1.2.2.1 h1.2.2.2 (by p6_omega) ?_
  refine WP.blk_cons (WP.mono (eadd_spec _) (fun s2 ⟨f1, f2, f3⟩ ↦ ?_) (fun _ h ↦ h))
  have h2 : St env s0 g t s2 :=
    (((h1.setReg (r := .r11) (by decide) (by decide) _).setReg (r := .r12) (by decide) (by decide)
      _).frame hin f2 f3)
  refine chkEl_refines (by p6_omega) y t s2 ⟨h2, ?_⟩
  rw [f1, hy]
  simp only [QState.setReg_reg, reduceCtorEq, ↓reduceIte]
  rw [e1]
  simp only [QState.setReg_reg, reduceCtorEq, ↓reduceIte, eOf_toE]
  ring

end NativeVm.Code.P6
