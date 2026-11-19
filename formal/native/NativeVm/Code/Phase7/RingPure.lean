module

public import NativeVm.Code.Phase7.RingTargetK
public import NativeVm.Code.Phase7.RingWeight

/-!
# Ring switching's arithmetic, in the working area

`ringPure`: from the sixteen challenges at the scratch's start (`f` then `g`) and `q_keccak`'s 64
slices (`KeccakOutAt`'s), the coefficients (`coeffK`) and the target (`psiK`, `targetK`) into
`ringR` as `RingAt` lays them out, `rbp` the working area. Its scratch: the images and `z`
(`imgO`, `zO`). `ringPure_spec` states it on lists of `E`.
-/

@[expose] public section

namespace NativeVm.Code.Ring

open Native NativeVm.Field LeanVM.Parameters LeanVM.Protocol.Verifier
open NativeVm.Transcript (wdisp wdisp_toUInt64 wp_load wp_store wp_storei)

variable {s : QState} {F : QState → Prop}

/-- The challenges, `f` then `g`: the scratch's first 32 words. -/
abbrev chO : Nat := 52670
/-- The images (`128` words). -/
abbrev imgO : Nat := 52702
/-- `z` (two words). -/
abbrev zO : Nat := 52830
/-- The slices, `KeccakOutAt`'s. -/
abbrev slO : Nat := 27803
/-- The target, `RingAt`'s first two words. -/
abbrev tgO : Nat := 27931
/-- The coefficients, `RingAt`'s from word `2`. -/
abbrev cfO : Nat := 27933

/-- The offsets are the regions'. -/
theorem offs_eq : chO = scratchR.off ∧ imgO = scratchR.off + 32 ∧ zO = scratchR.off + 160 ∧
    slO = keccakR.off + vecWords pointCap ∧ tgO = ringR.off ∧ cfO = ringR.off + 2 := by decide

/-- **Ring switching's arithmetic.** -/
def ringPure : Stmt := blk [coeffK chO (chO + 16) cfO, psiK slO (chO + 16) imgO,
  targetK chO imgO zO tgO]

theorem ringPure_writes : ringPure.writes .rdi = false ∧ ringPure.writes .rsp = false := by
  decide

/-- **`ringPure` writes the target and the coefficients.** -/
theorem ringPure_spec {W : UInt64} {Fl Gl Sl : List E} (hbp : s.reg .rbp = W)
    (hF : EArr s.mem (ew W chO) Fl) (hFl : Fl.length = 8) (hG : EArr s.mem (ew W (chO + 16)) Gl)
    (hGl : Gl.length = 8) (hS : EArr s.mem (ew W slO) Sl) (hSl : Sl.length = 64)
    (hdomR : ∀ k < 130, (s.mem (ew W (tgO + k))).isSome)
    (hdomS : ∀ k < 130, (s.mem (ew W (imgO + k))).isSome) :
    WP ringPure s (fun s' ↦ s'.reg .rbp = W ∧ EW s'.mem (ew W tgO) 0 (ringTarget Sl Fl Gl) ∧
      EArr s'.mem (ew W cfO) (ringCoefficients Fl Gl) ∧
      ∀ a, (∀ k < 130, a ≠ ew W (tgO + k)) → (∀ k < 130, a ≠ ew W (imgO + k)) →
        s'.mem a = s.mem a) F := by
  have o : chO = 52670 ∧ imgO = 52702 ∧ zO = 52830 ∧ slO = 27803 ∧ tgO = 27931 ∧ cfO = 27933 :=
    ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
  obtain ⟨o1, o2, o3, o4, o5, o6⟩ := o
  have neq : ∀ {i j : Nat}, i < 2 ^ 60 → j < 2 ^ 60 → i ≠ j → ew W i ≠ ew W j :=
    fun hi hj h ↦ ew_ne W (by omega) (by omega) h
  unfold ringPure
  refine WP.then (coeffK_spec (F := F) (fO := chO) (gO := chO + 16) (cO := cfO) hbp hF hFl hG hGl
    (fun k hk ↦ by have := hdomR (k + 2) (by omega); rwa [show tgO + (k + 2) = cfO + k by omega]
      at this) (by omega) (by omega) (by omega)) fun s1 ⟨b1, c1, f1⟩ ↦ ?_
  have k1 : ∀ j, (j < cfO ∨ cfO + 128 ≤ j) → j < 2 ^ 60 → s1.mem (ew W j) = s.mem (ew W j) :=
    fun j hj hj' ↦ f1 _ fun k hk ↦ neq (by omega) (by omega) (by omega)
  refine WP.then (psiK_spec (F := F) (sO := slO) (gO := chO + 16) (iO := imgO) (Sl := Sl) (Gl := Gl)
    b1 (EArr_congr (fun j hj ↦ by rw [ew_ew, k1 _ (by omega) (by omega)]) hS) hSl
    (EArr_congr (fun j hj ↦ by rw [ew_ew, k1 _ (by omega) (by omega)]) hG) hGl
    (fun k hk ↦ by rw [k1 _ (by omega) (by omega)]; exact hdomS k (by omega))
    (by omega) (by omega) (by omega)) fun s2 ⟨b2, i2, f2⟩ ↦ ?_
  have k2 : ∀ j, (j < imgO ∨ imgO + 128 ≤ j) → j < 2 ^ 60 → s2.mem (ew W j) = s1.mem (ew W j) :=
    fun j hj hj' ↦ f2 _ fun k hk ↦ neq (by omega) (by omega) (by omega)
  refine WP.then (targetK_spec (F := F) (fO := chO) (iO := imgO) (zO := zO) (tO := tgO)
    (Fl := Fl) b2 (EArr_congr (fun j hj ↦ by
      rw [ew_ew, k2 _ (by omega) (by omega), k1 _ (by omega) (by omega)]) hF) hFl i2
    (by rw [List.length_map, hSl])
    (by rw [k2 _ (by omega) (by omega), k1 _ (by omega) (by omega)]
        have := hdomS 128 (by omega); rwa [show imgO + 128 = zO by omega] at this)
    (by rw [k2 _ (by omega) (by omega), k1 _ (by omega) (by omega)]
        have := hdomS 129 (by omega); rwa [show imgO + 129 = zO + 1 by omega] at this)
    (by rw [k2 _ (by omega) (by omega), k1 _ (by omega) (by omega)]
        have := hdomR 0 (by omega); rwa [show tgO + 0 = tgO by omega] at this)
    (by rw [k2 _ (by omega) (by omega), k1 _ (by omega) (by omega)]; exact hdomR 1 (by omega))
    (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)) fun s3 h3 ↦ ?_
  apply WP.blk_nil
  refine ⟨h3.rbp, by rw [ringTarget_eq]; exact h3.sum, ?_, fun a ha hb ↦ ?_⟩
  · refine EArr_congr (fun j hj ↦ ?_) c1
    rw [ringCoefficients_length, hFl, hGl] at hj
    rw [ew_ew, h3.frame _ (neq (by omega) (by omega) (by omega)) (neq (by omega) (by omega) (by omega))
      (neq (by omega) (by omega) (by omega)) (neq (by omega) (by omega) (by omega)),
      k2 _ (by omega) (by omega)]
  · rw [h3.frame _ (by have := hb 128 (by omega); rwa [show imgO + 128 = zO by omega] at this)
      (by have := hb 129 (by omega); rwa [show imgO + 129 = zO + 1 by omega] at this)
      (by have := ha 0 (by omega); rwa [show tgO + 0 = tgO by omega] at this) (ha 1 (by omega)),
      f2 a (fun k hk ↦ hb k (by omega)),
      f1 a (fun k hk ↦ by have := ha (k + 2) (by omega); rwa [show tgO + (k + 2) = cfO + k by omega]
        at this)]

end NativeVm.Code.Ring
