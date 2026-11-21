module

public import NativeVm.Code.Phase6.LayerA

/-!
# A layer's segment weights, `iota` and the instance weights' sum

`pure_segW`: the two entries of `eqKernel` of the claim's point from `packBits`; `pure_iota`: the
layer's `iota`; `pure_sumMu`: the sum of the claim's instance weights.
-/

@[expose] public section

namespace NativeVm.Code.P6

open Native NativeVm.Model NativeVm.Code LeanVM.Parameters Finset
open NativeVm.Transcript (wd wdisp Env rf_trans)
open NativeVm.Field (eOf eOf_inj emul emul_spec eRegs eadd eadd_spec eOf_zero)

variable {env : Env} {inp : Input} {s0 s : QState} {t : TState} {g : Nat → EW} {p : UInt64}

/-! ## Segment weights -/

/-- Entry `i` of `eqKernel` of `n` coordinates from `ePt + d`, `0` past its end. -/
def segV (g : Nat → EW) (d n i : Nat) : LeanVM.Parameters.E :=
  if i < 2 ^ n then ∏ k ∈ range n, kfac g ePt d i k else 0

/-- Entry `1`: `0` without coordinates. -/
def segOne : Stmt := blk [I (.load .rax (at_ .rbp (wdisp (2 * eSegN)))),
  .ite (.cmp .eq .rax (.imm 0)) (blk [I (.movi .r9 0), I (.movi .r10 0)])
    (blk [I (.movi .r13 1), ekern ePt])]

/-- The segment weights. -/
def segC : List Stmt := [blk (cpEl ePB eKd), blk (cpEl eSegN eKn),
  blk (blk [I (.movi .r13 0), ekern ePt] :: stEl eSegW), blk (segOne :: stEl (eSegW + 1))]

theorem pure_segW (hin : Inputs env inp s0.mem) {d n : Nat} (hd : g ePB = EW.ofK d.toUInt64)
    (hn : g eSegN = EW.ofK n.toUInt64) (hn64 : n < 32) (hdn : d + n ≤ 32) :
    ∃ g', Pure6 env s0 (blk segC) g g' ∧ (∀ i, ¬ (i = eKd ∨ i = eKn ∨ i = eSegW ∨ i = eSegW + 1) →
      g' i = g i) ∧ ∀ i < 2, (g' (eSegW + i)).toE = segV g d n i := by
  have hN := scrN_lt
  set g1 := Function.update g eKd (g ePB)
  set g2 := Function.update g1 eKn (g1 eSegN)
  have h2d : g2 eKd = EW.ofK d.toUInt64 := by
    simp only [g2, g1]; rw [Function.update_of_ne (by p6_ne), Function.update_self, hd]
  have h2n : g2 eKn = EW.ofK n.toUInt64 := by
    simp only [g2, g1]; rw [Function.update_self, Function.update_of_ne (by p6_ne), hn]
  have h2p : ∀ k, ePt ≤ k → k < ePt + 32 → g2 k = g k := fun k h1 h2 ↦ by
    simp only [g2, g1]; rw [Function.update_of_ne (by p6_omega), Function.update_of_ne (by p6_omega)]
  have hk : ∀ i, ∏ k ∈ range n, kfac g2 ePt d i k = ∏ k ∈ range n, kfac g ePt d i k :=
    fun i ↦ prod_congr rfl fun k hk ↦ by
      have := mem_range.1 hk
      simp only [kfac, h2p (ePt + d + k) (by omega) (by p6_omega)]
  have e0 : ∀ s, s.reg .rbp = sb env → Scr s.mem (sb env) g2 →
      WP (blk [I (.movi .r13 0), ekern ePt]) s (fun s' ↦ eOf (s'.reg .r9) (s'.reg .r10) =
        (EW.ofE (segV g d n 0)).toE ∧ s'.mem = s.mem ∧ RegsFrame (.r13 :: kernRegs) s s')
        fun _ ↦ False := fun s hp hs ↦ by
    refine NativeVm.Transcript.wp_reg (by rfl) ?_
    refine WP.mono (ekern_spec (i := 0) (by simpa using hp) (hs.congr fun _ _ ↦ rfl) h2n h2d
      (by simp; rfl) (by norm_num) (by omega) (by p6_omega)) (fun s' ⟨h1, h2, h3⟩ ↦ ⟨?_, h2, ?_⟩)
      (fun _ h ↦ h)
    · rw [h1, NativeVm.Equiv.EW.toE_ofE, segV, hk]
      simp
    · exact rf_trans (l := [.r13]) (by rf_tac) h3
  set g3 := Function.update g2 eSegW (EW.ofE (segV g d n 0))
  have h3d : g3 eKd = EW.ofK d.toUInt64 := by
    simp only [g3]; rw [Function.update_of_ne (by p6_ne), h2d]
  have h3n : g3 eKn = EW.ofK n.toUInt64 := by
    simp only [g3]; rw [Function.update_of_ne (by p6_ne), h2n]
  have h3s : g3 eSegN = EW.ofK n.toUInt64 := by
    simp only [g3, g2, g1]
    rw [Function.update_of_ne (by p6_ne), Function.update_of_ne (by p6_ne),
      Function.update_of_ne (by p6_ne), hn]
  have hk3 : ∀ i, ∏ k ∈ range n, kfac g3 ePt d i k = ∏ k ∈ range n, kfac g ePt d i k :=
    fun i ↦ (prod_congr rfl fun k hk ↦ by
      have := mem_range.1 hk
      simp only [kfac, g3, Function.update_of_ne (show ePt + d + k ≠ eSegW by p6_omega)]).trans
      (hk i)
  have e1 : ∀ s, s.reg .rbp = sb env → Scr s.mem (sb env) g3 →
      WP segOne s (fun s' ↦ eOf (s'.reg .r9) (s'.reg .r10) =
        (EW.ofE (segV g d n 1)).toE ∧ s'.mem = s.mem ∧ RegsFrame (.r13 :: kernRegs) s s')
        fun _ ↦ False := fun s hp hs ↦ by
    unfold segOne
    refine ld0 hp hs (by p6_omega) ?_
    rw [h3s]
    apply WP.blk_cons
    apply WP.ite
    by_cases h0 : n = 0
    · subst h0
      simp only [Cond.eval, Rhs.eval, QState.setReg_reg, ↓reduceIte]
      rw [show ((EW.ofK (Nat.toUInt64 0)).c0 == Int64.toUInt64 0) = true from rfl]
      simp only [↓reduceIte]
      fstep; fstep; fdone
      refine WP.blk_nil ⟨?_, rfl, by rf_tac⟩
      rw [NativeVm.Equiv.EW.toE_ofE, segV]
      simp only [pow_zero, lt_self_iff_false, ↓reduceIte]
      exact eOf_zero
    · have hc : ((EW.ofK n.toUInt64).c0 == (Int64.toUInt64 0)) = false := by
        simp only [EW.ofK, beq_eq_false_iff_ne]
        intro e
        exact h0 (NativeVm.Transcript.toUInt64_inj (by omega) (by norm_num) |>.mp e)
      simp only [Cond.eval, Rhs.eval, QState.setReg_reg, ↓reduceIte, hc, Bool.false_eq_true]
      refine NativeVm.Transcript.wp_reg (by rfl) ?_
      refine WP.mono (ekern_spec (i := 1) (by simpa using hp) (hs.congr fun _ _ ↦ rfl) h3n h3d
        (by simp; rfl) (by norm_num) (by omega) (by p6_omega))
        (fun s' ⟨h1, h2, h3⟩ ↦ WP.blk_nil ⟨?_, h2, ?_⟩) (fun _ h ↦ h)
      · rw [h1, NativeVm.Equiv.EW.toE_ofE, segV, hk3]
        have : 1 < 2 ^ n := Nat.one_lt_two_pow h0
        simp [this]
      · exact rf_trans (l := [.rax, .r13]) (by rf_tac) h3
  refine ⟨Function.update g3 (eSegW + 1) (EW.ofE (segV g d n 1)),
    Pure6.cons (pure_cp hin (by p6_omega) (by p6_omega))
      (Pure6.cons (pure_cp hin (by p6_omega) (by p6_omega))
        (Pure6.cons (pure_el hin (by p6_omega) (by decide) e0)
          (Pure6.single (pure_el hin (by p6_omega) (by decide) e1)))), fun i hi ↦ ?_, fun i hi ↦ ?_⟩
  · simp only [not_or] at hi
    simp only [g3, g2, g1]
    rw [Function.update_of_ne hi.2.2.2, Function.update_of_ne hi.2.2.1,
      Function.update_of_ne hi.2.1, Function.update_of_ne hi.1]
  · rcases i with _ | _ | i
    · simp only [g3]
      rw [Function.update_of_ne (by p6_ne), Nat.add_zero, Function.update_self,
        NativeVm.Equiv.EW.toE_ofE]
    · rw [Function.update_self, NativeVm.Equiv.EW.toE_ofE]
    · omega

end NativeVm.Code.P6
