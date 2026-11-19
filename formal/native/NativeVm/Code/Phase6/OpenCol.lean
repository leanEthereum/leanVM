module

public import NativeVm.Code.Phase6.OpenMle

/-!
# An opening's columns folded at the slot

The rows' table holds, column by column, `64` columns of `64` entries from `eRows`. `colC` folds
each column `z` at the slot point (`eSlot`, `6` coordinates) by `emle`, its work area at `eWk`,
and stores the value at `eOW + z`; the column's index is `r15`, kept across `emle` in the word at
`eKn` (`colC_spec`). It writes only `ColW`'s elements.
-/

@[expose] public section

namespace NativeVm.Code.P6

open Native NativeVm.Model NativeVm.Code LeanVM.Parameters LeanVM.Protocol
open NativeVm.Transcript (wd wdisp Env wd_inj rf_trans)
open NativeVm.Field (eOf emle arrRegs)

variable {env : Env} {inp : Input} {s0 s : QState} {t : TState} {g : Nat → EW}

/-- `emle`'s work area in an opening, `32` elements. -/
def eWk : Nat := eG + 128

/-- A pass of the columns' loop: column `z` (in `r15`, and the word at `eKn`) folded at the slot,
stored at `eOW + z`, then `z + 1` in `r15` and at `eKn`. -/
def colBody : Stmt := blk (I (.mov .rax .r15) :: I (.shli .rax 10) :: I (.lea .r13 (ix (2 * eRows))) ::
  I (.lea .r14 (at_ .rbp (wdisp (2 * eWk)))) :: I (.lea .rsi (at_ .rbp (wdisp (2 * eSlot)))) ::
  I (.movi .r15 64) :: emle :: (ldSb ++ I (.load .r15 (at_ .rbp (wdisp (2 * eKn)))) ::
  I (.movi .r14 0) :: blk (tabStore eOW) :: I (.mov .r9 .r15) :: I (.movi .r10 0) :: stEl eKn))

/-- Fold every column at the slot. -/
def colC : List Stmt :=
  [blk (setW eKn 0), I (.movi .r15 0), .loop (.cmp .ltu .r15 (.imm (Int64.ofNat 64))) colBody]

/-- The elements `colC` writes. -/
def ColW (i : Nat) : Prop := i = eKn ∨ (eWk ≤ i ∧ i < eWk + 32) ∨ (eOW ≤ i ∧ i < eOW + 64)

/-- Column `j` folded at the slot, from the scratch `g`. -/
def colV (g : Nat → EW) (j : Nat) : E :=
  Verifier.multilinearEval (vals g (eRows + 64 * j) 64) (vals g eSlot 6)

/-- The loop's invariant: `z` columns done. -/
def ColInv (env : Env) (s0 : QState) (g : Nat → EW) (t : TState) (s : QState) : Prop :=
  ∃ z ≤ 64, s.reg .r15 = z.toUInt64 ∧ ∃ g', St env s0 g' t s ∧ g' eKn = EW.ofK z.toUInt64 ∧
    (∀ i, ¬ ColW i → g' i = g i) ∧ ∀ j < z, (g' (eOW + j)).toE = colV g j

theorem vals_congr {g g' : Nat → EW} {o n : Nat} (h : ∀ i < n, g' (o + i) = g (o + i)) :
    vals g' o n = vals g o n :=
  List.map_congr_left fun i hi ↦ by rw [h i (List.mem_range.1 hi)]

theorem colBody_spec (hin : Inputs env inp s0.mem) {z : Nat} (hz : z < 64) {g' : Nat → EW}
    (h15 : s.reg .r15 = z.toUInt64) (h : St env s0 g' t s) (hkn : g' eKn = EW.ofK z.toUInt64)
    (hfr : ∀ i, ¬ ColW i → g' i = g i) (hres : ∀ j < z, (g' (eOW + j)).toE = colV g j) :
    WP colBody s (fun s' ↦ ColInv env s0 g t s' ∧
      64 - (s'.reg .r15).toNat < 64 - (s.reg .r15).toNat) fun _ ↦ False := by
  have hN := scrN_lt
  have hp := h.2.2.1
  unfold colBody
  refine NativeVm.Transcript.wp_reg (by rfl) (NativeVm.Transcript.wp_reg (by rfl) ?_)
  have hrax : (s.reg .r15 <<< (10 : Nat).toUInt64) = (8 * (2 * (64 * z))).toUInt64 := by
    rw [h15, NativeVm.Transcript.toUInt64_shl _ _ (by omega)]
    congr 1
    omega
  refine NativeVm.Transcript.wp_reg (by rfl) (NativeVm.Transcript.wp_reg (by rfl)
    (NativeVm.Transcript.wp_reg (by rfl) (NativeVm.Transcript.wp_reg (by rfl) ?_)))
  refine emle_st hin (a := eRows + 64 * z) (b := eWk) (c := eSlot) (m := 6)
    (((((((h.setReg (r := .rax) (by decide) (by decide) _).setReg (r := .rax) (by decide)
      (by decide) _).setReg (r := .r13) (by decide) (by decide) _).setReg (r := .r14) (by decide)
      (by decide) _).setReg (r := .rsi) (by decide) (by decide) _).setReg (r := .r15) (by decide)
      (by decide) _))
    ?_ ?_ ?_ (by rfl) (by omega) (by p6_omega) (by simp only [eWk]; p6_omega) (by p6_omega)
    (by simp only [eWk]; p6_omega) (by simp only [eWk]; p6_omega) fun s1 g1 h1 hag he _ ↦ ?_
  · simp only [QState.setReg_reg, reduceCtorEq, ↓reduceIte]
    rw [show 2 * (eRows + 64 * z) = 2 * (64 * z) + 2 * eRows by omega]
    exact eval_idx (by simpa using hp) (by simpa using hrax) _
  · simp only [QState.setReg_reg, reduceCtorEq, ↓reduceIte]
    exact eval_el (by simpa using hp) _
  · simp only [QState.setReg_reg, reduceCtorEq, ↓reduceIte]
    exact eval_el (by simpa using hp) _
  have hkn1 : g1 eKn = EW.ofK z.toUInt64 := by
    rw [hag _ (by simp only [eWk]; p6_omega), hkn]
  refine ld0 h1.2.2.1 h1.2.2.2 (by p6_omega) ?_
  rw [hkn1]
  refine NativeVm.Transcript.wp_reg (by rfl) ?_
  set x : EW := EW.ofE (colV g z) with hx
  have hxe : eOf (s1.reg .r9) (s1.reg .r10) = x.toE := by
    rw [he, hx, NativeVm.Equiv.EW.toE_ofE, colV]
    congr 1
    · exact vals_congr fun i hi ↦ hfr _ (by simp only [ColW, eWk]; p6_omega)
    · exact vals_congr fun i hi ↦ hfr _ (by simp only [ColW, eWk]; p6_omega)
  obtain ⟨v9, v10⟩ := regs_of_eOf hxe
  have hp1 := h1.2.2.1
  refine WP.blk_cons (WP.mono (tabStore_spec (o := eOW) (d := 0) (m := z) (f := g1) (p := sb env)
    (s := (s1.setReg .r15 (EW.ofK z.toUInt64).c0).setReg .r14 (Int64.toUInt64 0))
    (E := fun _ ↦ False) (by p6_omega) (by simpa using hp1) (by simp; rfl) (by simp; rfl)
    (h1.2.2.2.congr fun _ _ ↦ rfl) x (by simpa using v9) (by simpa using v10))
    (fun s3 ⟨e1, e2, e3, e4⟩ ↦ ?_) (fun _ h ↦ h))
  refine NativeVm.Transcript.wp_reg (by rfl) (NativeVm.Transcript.wp_reg (by rfl) ?_)
  rw [← List.append_nil (stEl eKn)]
  have hp3 : s3.reg .rbp = sb env := by rw [e3 .rbp (by decide)]; simpa using hp1
  refine stEl_spec (x := EW.ofK (z + 1).toUInt64) (by p6_omega) (by simpa using hp3)
    (e1.congr fun _ _ ↦ rfl) (by simp [e4]; rfl) (by simp; rfl) fun s4 h4 h5 h6 ↦ WP.blk_nil ?_
  have hst : St env s0 (Function.update (Function.update g1 (eOW + 0 + z) x) eKn
      (EW.ofK (z + 1).toUInt64)) t s4 := by
    refine St.mk' hin h1 h4 (fun a ha ↦ ?_) ?_ ?_
    · rw [h5 a ha]; simp only [QState.setReg_mem]; rw [e2 a ha]; rfl
    · rw [h6]; simp only [QState.setReg_reg, reduceCtorEq, ↓reduceIte]
      rw [e3 .rdi (by decide)]; simp
    · rw [h6]; simp only [QState.setReg_reg, reduceCtorEq, ↓reduceIte]
      rw [hp3, hp1]
  have h15' : s4.reg .r15 = (z + 1).toUInt64 := by
    rw [h6]; simp only [QState.setReg_reg, reduceCtorEq, ↓reduceIte]; exact e4
  refine ⟨⟨z + 1, by omega, h15', _, hst, Function.update_self .., fun i hi ↦ ?_, fun j hj ↦ ?_⟩, ?_⟩
  · have hi' := hi
    simp only [ColW, eWk, not_or] at hi'
    rw [Function.update_of_ne hi'.1, Function.update_of_ne (by p6_omega),
      hag _ (by simp only [eWk] at *; p6_omega), hfr i hi]
  · rw [Function.update_of_ne (by p6_omega)]
    by_cases hjz : j = z
    · subst hjz; rw [Nat.add_zero, Function.update_self, hx, NativeVm.Equiv.EW.toE_ofE]
    · rw [Function.update_of_ne (by omega), hag _ (by simp only [eWk]; p6_omega),
        hres j (by omega)]
  · rw [h15', h15, toNat_toUInt64' (by omega), toNat_toUInt64' (by omega)]
    omega

/-- **The columns folded at the slot**, the scratch the same outside `ColW`. -/
theorem colC_spec (hin : Inputs env inp s0.mem) (h : St env s0 g t s) :
    WP (blk colC) s (fun s' ↦ ∃ g', St env s0 g' t s' ∧ (∀ i, ¬ ColW i → g' i = g i) ∧
      ∀ z < 64, (g' (eOW + z)).toE = colV g z) fun _ ↦ False := by
  have hN := scrN_lt
  unfold colC
  refine WP.blk_cons (WP.mono (pure_setW (o := eKn) (w := 0) hin (by p6_omega) t s h)
    (fun s1 h1 ↦ ?_) (fun _ h ↦ h))
  refine NativeVm.Transcript.wp_reg (by rfl) (WP.blk_cons ?_)
  refine WP.mono (P := fun s' ↦ ∃ g', St env s0 g' t s' ∧ (∀ i, ¬ ColW i → g' i = g i) ∧
      ∀ z < 64, (g' (eOW + z)).toE = colV g z) ?_ (fun _ h ↦ WP.blk_nil h) (fun _ h ↦ h)
  refine WP.loop (ColInv env s0 g t) (fun s ↦ 64 - (s.reg .r15).toNat)
    ⟨0, by omega, by simp; rfl, _, h1.setReg (r := .r15) (by decide) (by decide) _,
      Function.update_self .., fun i hi ↦ Function.update_of_ne (fun e ↦ hi (Or.inl e)) _ _,
      fun j hj ↦ absurd hj (by omega)⟩ ?_ ?_
  · intro s2 ⟨z, _, h15, g', h2, hkn, hfr, hres⟩ hc
    have hz : z < 64 := (ltu_imm h15 (by omega) (by omega)).mp hc
    exact colBody_spec hin hz h15 h2 hkn hfr hres
  · intro s2 ⟨z, hz, h15, g', h2, _, hfr, hres⟩ hc
    have : ¬ z < 64 := fun h ↦ by
      rw [(ltu_imm h15 (by omega) (by omega)).mpr h] at hc; exact absurd hc (by decide)
    exact ⟨g', h2, hfr, fun j hj ↦ hres j (by omega)⟩

end NativeVm.Code.P6
