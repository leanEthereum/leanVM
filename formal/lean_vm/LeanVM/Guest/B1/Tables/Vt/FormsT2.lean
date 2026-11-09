/-
  LeanVM.Guest.B1.Tables.Vt.FormsT2

  Table 2's forms on the three sides, from the guest's statements: each block's value from its
  baked terms, the table's form the blocks' selectors times their values.
-/

module

public import LeanVM.Guest.B1.Tables.Vt.FormsDiff
public import LeanVM.Guest.B1.Tables.Vt.PullSels
public import LeanVM.Guest.B1.Tables.Vt.Pi

namespace LeanVM.Guest.B1.Tables

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Protocol LeanVM.Protocol.Verifier

@[expose] public section

set_option maxRecDepth 10000 in
theorem vtB02_0 {rd : Reader} {σ : Val} (h : VtH rd σ) {W ev : ℕ → E}
    (hw : ∀ i < 16, LoadHolds rd (σ (.n 13)) i (W i))
    (hev : ∀ c < 8, σ (.n (vtEvB (30 + c))) = ev c) :
    σ (.n 3533) = σ (.n 1034) * vtBlockVal (σ (.n 14)) W ev
      [[([], 1)], [([0], 2)], [([1], 1)]] := by
  obtain ⟨_, hs⟩ := h.sliceAt 3434 [
    .atom (.load (.n 3523) (.n 13) 0),
    .atom (.const (.n 3524) (word 2 0 0)),
    .atom (.mul (.n 3525) (.n 3524) (.n 3419)),
    .atom (.load (.n 3526) (.n 13) 1),
    .atom (.mul (.n 3527) (.n 3526) (.n 3525)),
    .atom (.add (.n 3528) (.n 3523) (.n 3527)),
    .atom (.load (.n 3529) (.n 13) 2),
    .atom (.mul (.n 3530) (.n 3529) (.n 3430)),
    .atom (.add (.n 3531) (.n 3528) (.n 3530)),
    .atom (.add (.n 3532) (.n 14) (.n 3531)),
    .atom (.mul (.n 3533) (.n 1034) (.n 3532))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs
  obtain ⟨a3434, a3435, a3436, a3437, a3438, a3439, a3440, a3441, a3442, a3443, a3444, -⟩ := hs
  have e3434 := tb_loadHolds_unique a3434 (hw 0 (by norm_num))
  have e3437 := tb_loadHolds_unique a3437 (hw 1 (by norm_num))
  have e3440 := tb_loadHolds_unique a3440 (hw 2 (by norm_num))
  have v3419 : σ (.n 3419) = ev 0 := by
    rw [← hev 0 (by norm_num)]; exact (vt_eval h (k := 30) (by norm_num)).2.2
  have v3430 : σ (.n 3430) = ev 1 := by
    rw [← hev 1 (by norm_num)]; exact (vt_eval h (k := 31) (by norm_num)).2.2
  have hB : σ (.n 3532) = vtBlockVal (σ (.n 14)) W ev [[([], 1)], [([0], 2)], [([1], 1)]] := by
    simp only [v3430, v3419, a3443, a3442, a3441, e3440, a3439, a3438, e3437, a3436, a3435, e3434]
    simp only [vtBlockVal_eq, vtSlots, vtCoordVal_cons, vtCoordVal_nil, List.map_cons,
      List.map_nil, List.prod_cons, List.prod_nil, vt_word_ofK, vt_ofK_ofBits_one]
    ring
  rw [a3444, hB]

set_option maxRecDepth 10000 in
theorem vtB02_1 {rd : Reader} {σ : Val} (h : VtH rd σ) {W ev : ℕ → E}
    (hw : ∀ i < 16, LoadHolds rd (σ (.n 13)) i (W i))
    (hev : ∀ c < 8, σ (.n (vtEvB (30 + c))) = ev c) :
    σ (.n 3567) = σ (.n 3533) + σ (.n 1043) * vtBlockVal (σ (.n 14)) W ev
      [[([], 4)], [([0], 1)], [([7], 2)], [([], 4)], [([2], 1)], [([3], 1)], [([4], 1)], [([5], 1)], [([], 0)]] := by
  obtain ⟨_, hs⟩ := h.sliceAt 3445 [
    .atom (.load (.n 3534) (.n 13) 0),
    .atom (.const (.n 3535) (word 4 0 0)),
    .atom (.mul (.n 3536) (.n 3534) (.n 3535)),
    .atom (.load (.n 3537) (.n 13) 1),
    .atom (.mul (.n 3538) (.n 3537) (.n 3419)),
    .atom (.add (.n 3539) (.n 3536) (.n 3538)),
    .atom (.const (.n 3540) (word 2 0 0)),
    .atom (.mul (.n 3541) (.n 3540) (.n 3522)),
    .atom (.load (.n 3542) (.n 13) 2),
    .atom (.mul (.n 3543) (.n 3542) (.n 3541)),
    .atom (.add (.n 3544) (.n 3539) (.n 3543)),
    .atom (.load (.n 3545) (.n 13) 3),
    .atom (.const (.n 3546) (word 4 0 0)),
    .atom (.mul (.n 3547) (.n 3545) (.n 3546)),
    .atom (.add (.n 3548) (.n 3544) (.n 3547)),
    .atom (.load (.n 3549) (.n 13) 4),
    .atom (.mul (.n 3550) (.n 3549) (.n 3454)),
    .atom (.add (.n 3551) (.n 3548) (.n 3550)),
    .atom (.load (.n 3552) (.n 13) 5),
    .atom (.mul (.n 3553) (.n 3552) (.n 3465)),
    .atom (.add (.n 3554) (.n 3551) (.n 3553)),
    .atom (.load (.n 3555) (.n 13) 6),
    .atom (.mul (.n 3556) (.n 3555) (.n 3476)),
    .atom (.add (.n 3557) (.n 3554) (.n 3556)),
    .atom (.load (.n 3558) (.n 13) 7),
    .atom (.mul (.n 3559) (.n 3558) (.n 3487)),
    .atom (.add (.n 3560) (.n 3557) (.n 3559)),
    .atom (.load (.n 3561) (.n 13) 8),
    .atom (.const (.n 3562) (word 0 0 0)),
    .atom (.mul (.n 3563) (.n 3561) (.n 3562)),
    .atom (.add (.n 3564) (.n 3560) (.n 3563)),
    .atom (.add (.n 3565) (.n 14) (.n 3564)),
    .atom (.mul (.n 3566) (.n 1043) (.n 3565)),
    .atom (.add (.n 3567) (.n 3533) (.n 3566))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs
  obtain ⟨a3445, a3446, a3447, a3448, a3449, a3450, a3451, a3452, a3453, a3454, a3455, a3456, a3457, a3458,
    a3459, a3460, a3461, a3462, a3463, a3464, a3465, a3466, a3467, a3468, a3469, a3470, a3471,
    a3472, a3473, a3474, a3475, a3476, a3477, a3478, -⟩ := hs
  have e3445 := tb_loadHolds_unique a3445 (hw 0 (by norm_num))
  have e3448 := tb_loadHolds_unique a3448 (hw 1 (by norm_num))
  have e3453 := tb_loadHolds_unique a3453 (hw 2 (by norm_num))
  have e3456 := tb_loadHolds_unique a3456 (hw 3 (by norm_num))
  have e3460 := tb_loadHolds_unique a3460 (hw 4 (by norm_num))
  have e3463 := tb_loadHolds_unique a3463 (hw 5 (by norm_num))
  have e3466 := tb_loadHolds_unique a3466 (hw 6 (by norm_num))
  have e3469 := tb_loadHolds_unique a3469 (hw 7 (by norm_num))
  have e3472 := tb_loadHolds_unique a3472 (hw 8 (by norm_num))
  have v3419 : σ (.n 3419) = ev 0 := by
    rw [← hev 0 (by norm_num)]; exact (vt_eval h (k := 30) (by norm_num)).2.2
  have v3454 : σ (.n 3454) = ev 2 := by
    rw [← hev 2 (by norm_num)]; exact (vt_eval h (k := 32) (by norm_num)).2.2
  have v3465 : σ (.n 3465) = ev 3 := by
    rw [← hev 3 (by norm_num)]; exact (vt_eval h (k := 33) (by norm_num)).2.2
  have v3476 : σ (.n 3476) = ev 4 := by
    rw [← hev 4 (by norm_num)]; exact (vt_eval h (k := 34) (by norm_num)).2.2
  have v3487 : σ (.n 3487) = ev 5 := by
    rw [← hev 5 (by norm_num)]; exact (vt_eval h (k := 35) (by norm_num)).2.2
  have v3522 : σ (.n 3522) = ev 7 := by
    rw [← hev 7 (by norm_num)]; exact (vt_eval h (k := 37) (by norm_num)).2.2
  have hB : σ (.n 3565) = vtBlockVal (σ (.n 14)) W ev [[([], 4)], [([0], 1)], [([7], 2)], [([], 4)], [([2], 1)], [([3], 1)], [([4], 1)], [([5], 1)], [([], 0)]] := by
    simp only [v3522, v3487, v3476, v3465, v3454, v3419, a3476, a3475, a3474, a3473, e3472, a3471, a3470,
      e3469, a3468, a3467, e3466, a3465, a3464, e3463, a3462, a3461, e3460, a3459, a3458,
      a3457, e3456, a3455, a3454, e3453, a3452, a3451, a3450, a3449, e3448, a3447, a3446,
      e3445]
    simp only [vtBlockVal_eq, vtSlots, vtCoordVal_cons, vtCoordVal_nil, List.map_cons,
      List.map_nil, List.prod_cons, List.prod_nil, vt_word_ofK, vt_ofK_ofBits_zero, vt_ofK_ofBits_one]
    ring
  rw [a3478, a3477, hB]

set_option maxRecDepth 10000 in
theorem vtB02_2 {rd : Reader} {σ : Val} (h : VtH rd σ) {W ev : ℕ → E}
    (hw : ∀ i < 16, LoadHolds rd (σ (.n 13)) i (W i))
    (hev : ∀ c < 8, σ (.n (vtEvB (30 + c))) = ev c) :
    σ (.n 3591) = σ (.n 3567) + σ (.n 1052) * vtBlockVal (σ (.n 14)) W ev
      [[([], 2)], [([1, 2], 1)], [([6], 2)], [([3], 1)], [([4], 1)], [([5], 1)]] := by
  obtain ⟨_, hs⟩ := h.sliceAt 3479 [
    .atom (.load (.n 3568) (.n 13) 0),
    .atom (.const (.n 3569) (word 2 0 0)),
    .atom (.mul (.n 3570) (.n 3568) (.n 3569)),
    .atom (.mul (.n 3571) (.n 3430) (.n 3454)),
    .atom (.load (.n 3572) (.n 13) 1),
    .atom (.mul (.n 3573) (.n 3572) (.n 3571)),
    .atom (.add (.n 3574) (.n 3570) (.n 3573)),
    .atom (.const (.n 3575) (word 2 0 0)),
    .atom (.mul (.n 3576) (.n 3575) (.n 3511)),
    .atom (.load (.n 3577) (.n 13) 2),
    .atom (.mul (.n 3578) (.n 3577) (.n 3576)),
    .atom (.add (.n 3579) (.n 3574) (.n 3578)),
    .atom (.load (.n 3580) (.n 13) 3),
    .atom (.mul (.n 3581) (.n 3580) (.n 3465)),
    .atom (.add (.n 3582) (.n 3579) (.n 3581)),
    .atom (.load (.n 3583) (.n 13) 4),
    .atom (.mul (.n 3584) (.n 3583) (.n 3476)),
    .atom (.add (.n 3585) (.n 3582) (.n 3584)),
    .atom (.load (.n 3586) (.n 13) 5),
    .atom (.mul (.n 3587) (.n 3586) (.n 3487)),
    .atom (.add (.n 3588) (.n 3585) (.n 3587)),
    .atom (.add (.n 3589) (.n 14) (.n 3588)),
    .atom (.mul (.n 3590) (.n 1052) (.n 3589)),
    .atom (.add (.n 3591) (.n 3567) (.n 3590))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs
  obtain ⟨a3479, a3480, a3481, a3482, a3483, a3484, a3485, a3486, a3487, a3488, a3489, a3490, a3491, a3492,
    a3493, a3494, a3495, a3496, a3497, a3498, a3499, a3500, a3501, a3502, -⟩ := hs
  have e3479 := tb_loadHolds_unique a3479 (hw 0 (by norm_num))
  have e3483 := tb_loadHolds_unique a3483 (hw 1 (by norm_num))
  have e3488 := tb_loadHolds_unique a3488 (hw 2 (by norm_num))
  have e3491 := tb_loadHolds_unique a3491 (hw 3 (by norm_num))
  have e3494 := tb_loadHolds_unique a3494 (hw 4 (by norm_num))
  have e3497 := tb_loadHolds_unique a3497 (hw 5 (by norm_num))
  have v3430 : σ (.n 3430) = ev 1 := by
    rw [← hev 1 (by norm_num)]; exact (vt_eval h (k := 31) (by norm_num)).2.2
  have v3454 : σ (.n 3454) = ev 2 := by
    rw [← hev 2 (by norm_num)]; exact (vt_eval h (k := 32) (by norm_num)).2.2
  have v3465 : σ (.n 3465) = ev 3 := by
    rw [← hev 3 (by norm_num)]; exact (vt_eval h (k := 33) (by norm_num)).2.2
  have v3476 : σ (.n 3476) = ev 4 := by
    rw [← hev 4 (by norm_num)]; exact (vt_eval h (k := 34) (by norm_num)).2.2
  have v3487 : σ (.n 3487) = ev 5 := by
    rw [← hev 5 (by norm_num)]; exact (vt_eval h (k := 35) (by norm_num)).2.2
  have v3511 : σ (.n 3511) = ev 6 := by
    rw [← hev 6 (by norm_num)]; exact (vt_eval h (k := 36) (by norm_num)).2.2
  have hB : σ (.n 3589) = vtBlockVal (σ (.n 14)) W ev [[([], 2)], [([1, 2], 1)], [([6], 2)], [([3], 1)], [([4], 1)], [([5], 1)]] := by
    simp only [v3511, v3487, v3476, v3465, v3454, v3430, a3500, a3499, a3498, e3497, a3496, a3495, e3494,
      a3493, a3492, e3491, a3490, a3489, e3488, a3487, a3486, a3485, a3484, e3483, a3482,
      a3481, a3480, e3479]
    simp only [vtBlockVal_eq, vtSlots, vtCoordVal_cons, vtCoordVal_nil, List.map_cons,
      List.map_nil, List.prod_cons, List.prod_nil, vt_word_ofK, vt_ofK_ofBits_one]
    ring
  rw [a3502, a3501, hB]

set_option maxRecDepth 10000 in
theorem vtSide02 {rd : Reader} {σ : Val} (h : VtH rd σ) {W ev : ℕ → E}
    (hw : ∀ i < 16, LoadHolds rd (σ (.n 13)) i (W i))
    (hev : ∀ c < 8, σ (.n (vtEvB (30 + c))) = ev c) :
    σ (.n 3591) =
      vtSideVal [σ (.n 1034), σ (.n 1043), σ (.n 1052)]
        (σ (.n 14)) W ev vtBTerms02 := by
  rw [vtB02_2 h hw hev, vtB02_1 h hw hev, vtB02_0 h hw hev]
  simp only [vtSideVal, vtBTerms02, List.zipWith_cons_cons, List.zipWith_nil_left,
    List.sum_cons, List.sum_nil, add_zero, add_assoc]

set_option maxRecDepth 10000 in
theorem vtD2_0 {rd : Reader} {σ : Val} (h : VtH rd σ) {W ev : ℕ → E}
    (hw : ∀ i < 16, LoadHolds rd (σ (.n 13)) i (W i))
    (hev : ∀ c < 8, σ (.n (vtEvB (30 + c))) = ev c) :
    σ (.n 3597) = σ (.n 1988) * vtSlots W ev 0
      [[], [([0], 3)], []] := by
  obtain ⟨_, hs⟩ := h.sliceAt 3504 [
    .atom (.const (.n 3593) (word 3 0 0)),
    .atom (.mul (.n 3594) (.n 3593) (.n 3419)),
    .atom (.load (.n 3595) (.n 13) 1),
    .atom (.mul (.n 3596) (.n 3595) (.n 3594)),
    .atom (.mul (.n 3597) (.n 1988) (.n 3596))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs
  obtain ⟨a3504, a3505, a3506, a3507, a3508, -⟩ := hs
  have e3506 := tb_loadHolds_unique a3506 (hw 1 (by norm_num))
  have v3419 : σ (.n 3419) = ev 0 := by
    rw [← hev 0 (by norm_num)]; exact (vt_eval h (k := 30) (by norm_num)).2.2
  have hB : σ (.n 3596) = vtSlots W ev 0 [[], [([0], 3)], []] := by
    simp only [v3419, a3507, e3506, a3505, a3504]
    simp only [vtSlots, vtCoordVal_cons, vtCoordVal_nil, List.map_cons,
      List.map_nil, List.prod_cons, List.prod_nil, vt_word_ofK]
    ring
  rw [a3508, hB]

set_option maxRecDepth 10000 in
theorem vtD2_1 {rd : Reader} {σ : Val} (h : VtH rd σ) {W ev : ℕ → E}
    (hw : ∀ i < 16, LoadHolds rd (σ (.n 13)) i (W i))
    (hev : ∀ c < 8, σ (.n (vtEvB (30 + c))) = ev c) :
    σ (.n 3603) = σ (.n 3597) + σ (.n 1990) * vtSlots W ev 0
      [[], [], [([7], 3)], [], [], [], [], [], []] := by
  obtain ⟨_, hs⟩ := h.sliceAt 3509 [
    .atom (.const (.n 3598) (word 3 0 0)),
    .atom (.mul (.n 3599) (.n 3598) (.n 3522)),
    .atom (.load (.n 3600) (.n 13) 2),
    .atom (.mul (.n 3601) (.n 3600) (.n 3599)),
    .atom (.mul (.n 3602) (.n 1990) (.n 3601)),
    .atom (.add (.n 3603) (.n 3597) (.n 3602))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs
  obtain ⟨a3509, a3510, a3511, a3512, a3513, a3514, -⟩ := hs
  have e3511 := tb_loadHolds_unique a3511 (hw 2 (by norm_num))
  have v3522 : σ (.n 3522) = ev 7 := by
    rw [← hev 7 (by norm_num)]; exact (vt_eval h (k := 37) (by norm_num)).2.2
  have hB : σ (.n 3601) = vtSlots W ev 0 [[], [], [([7], 3)], [], [], [], [], [], []] := by
    simp only [v3522, a3512, e3511, a3510, a3509]
    simp only [vtSlots, vtCoordVal_cons, vtCoordVal_nil, List.map_cons,
      List.map_nil, List.prod_cons, List.prod_nil, vt_word_ofK]
    ring
  rw [a3514, a3513, hB]

set_option maxRecDepth 10000 in
theorem vtD2_2 {rd : Reader} {σ : Val} (h : VtH rd σ) {W ev : ℕ → E}
    (hw : ∀ i < 16, LoadHolds rd (σ (.n 13)) i (W i))
    (hev : ∀ c < 8, σ (.n (vtEvB (30 + c))) = ev c) :
    σ (.n 3609) = σ (.n 3603) + σ (.n 1992) * vtSlots W ev 0
      [[], [], [([6], 3)], [], [], []] := by
  obtain ⟨_, hs⟩ := h.sliceAt 3515 [
    .atom (.const (.n 3604) (word 3 0 0)),
    .atom (.mul (.n 3605) (.n 3604) (.n 3511)),
    .atom (.load (.n 3606) (.n 13) 2),
    .atom (.mul (.n 3607) (.n 3606) (.n 3605)),
    .atom (.mul (.n 3608) (.n 1992) (.n 3607)),
    .atom (.add (.n 3609) (.n 3603) (.n 3608))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs
  obtain ⟨a3515, a3516, a3517, a3518, a3519, a3520, -⟩ := hs
  have e3517 := tb_loadHolds_unique a3517 (hw 2 (by norm_num))
  have v3511 : σ (.n 3511) = ev 6 := by
    rw [← hev 6 (by norm_num)]; exact (vt_eval h (k := 36) (by norm_num)).2.2
  have hB : σ (.n 3607) = vtSlots W ev 0 [[], [], [([6], 3)], [], [], []] := by
    simp only [v3511, a3518, e3517, a3516, a3515]
    simp only [vtSlots, vtCoordVal_cons, vtCoordVal_nil, List.map_cons,
      List.map_nil, List.prod_cons, List.prod_nil, vt_word_ofK]
    ring
  rw [a3520, a3519, hB]

set_option maxRecDepth 10000 in
theorem vtSide12 {rd : Reader} {σ : Val} (h : VtH rd σ) {W ev : ℕ → E}
    (hw : ∀ i < 16, LoadHolds rd (σ (.n 13)) i (W i))
    (hev : ∀ c < 8, σ (.n (vtEvB (30 + c))) = ev c) :
    σ (.n 3610) =
      vtSideVal [σ (.n 1988), σ (.n 1990), σ (.n 1992)]
        (σ (.n 14)) W ev vtBTerms12 := by
  have hF0 : σ (.n 3591) =
      vtSideVal [σ (.n 1988), σ (.n 1990), σ (.n 1992)]
        (σ (.n 14)) W ev vtBTerms02 := by
    rw [vtPullSels2 h]; exact vtSide02 h hw hev
  have a3521 := h.atomAt 3521 (.add (.n 3610) (.n 3591) (.n 3609)) (by decide +kernel)
  simp only [Atom.Holds] at a3521
  rw [vtSideVal_pull _ _ _ _ _ _ _ vtPull2, ← hF0, a3521, vtD2_2 h hw hev, vtD2_1 h hw hev, vtD2_0 h hw hev]
  simp only [vtDiffSum, vtDTerms2, List.zipWith_cons_cons, List.zipWith_nil_left,
    List.sum_cons, List.sum_nil, add_zero, add_assoc]

set_option maxRecDepth 10000 in
theorem vtSide22 {rd : Reader} {σ : Val} (h : VtH rd σ) {ev : ℕ → E}
    (hev : ∀ c < 8, σ (.n (vtEvB (30 + c))) = ev c) :
    σ (.n 3615) =
      vtSideVal [σ (.n 2137), σ (.n 2146)]
        (0) (fun _ ↦ 1) ev vtBTerms22 := by
  obtain ⟨_, hs⟩ := h.sliceAt 3524 [
    .atom (.mul (.n 3613) (.n 2137) (.n 3511)),
    .atom (.mul (.n 3614) (.n 2146) (.n 3522)),
    .atom (.add (.n 3615) (.n 3613) (.n 3614))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs
  obtain ⟨a3524, a3525, a3526, -⟩ := hs
  have v3511 : σ (.n 3511) = ev 6 := by
    rw [← hev 6 (by norm_num)]; exact (vt_eval h (k := 36) (by norm_num)).2.2
  have v3522 : σ (.n 3522) = ev 7 := by
    rw [← hev 7 (by norm_num)]; exact (vt_eval h (k := 37) (by norm_num)).2.2
  rw [a3526, a3524, a3525, v3511, v3522]
  simp only [vtSideVal, vtBTerms22, List.zipWith_cons_cons, List.zipWith_nil_left,
    List.sum_cons, List.sum_nil, vtBlockVal_eq, vtSlots, vtCoordVal_cons, vtCoordVal_nil,
    List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, vt_ofK_ofBits_one, zero_add,
    one_mul, mul_one, add_zero]

end
end LeanVM.Guest.B1.Tables
