/-
  LeanVM.Guest.CoreMode.Fn.verify_tables.ResVtG

  `verify_tables`' block groups at its honest instances: each side's ranks name every group of the
  side, the groups' keys are nonzero; the groups' bases read in group order (`Res.vtGrpB`) at the
  honest frames.
-/

module

public import LeanVM.Guest.CoreMode.Fn.verify_tables.ExpQv
public import LeanVM.Guest.CoreMode.Fn.verify_tables.ResVtSt
public import LeanVM.Guest.CoreMode.Fam.ResExp
public import LeanVM.Guest.B1.Tables.Vt.Sort
public import LeanVM.Guest.B1.Tables.Vt.Pads
public import LeanVM.Guest.CoreMode.Fn.verify_tables.SubVt
public import LeanVM.Guest.CoreMode.Fn.verify_tables.ResVtL
import LeanVM.Guest.ValRef
import LeanVM.Guest.Data.ValNames.«verify_tables»

/-!
# `verify_tables`' groups

`vtG_side`: a side's ranks each read a group of the side (the side table) and its key `g^KN`; the
keys strictly decrease along the ranks (the range-checked differences), so the ranks' groups are
distinct, and as many as the side's groups: every group is some rank's. `vt_groups`: both sides,
the keys `KN` from the groups' rank keys (`vt_grps`, the exponent tables), `kappa_base` from the
dims and the tables' heights (`vt_kb`, `vt_pads`); rank `1`'s keys, the divisors `133` and `430`,
are nonzero. `vt_groups_at`: at every honest instance, from its body (`vt_holds`) and precondition
(`vtPQ_all`). `nzVal_vt133`, `nzVal_vt430`: the divisors' `NzVal`.
-/

namespace LeanVM.Guest.EndExec

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Mode LeanVM.Guest.Core LeanVM.Guest.Memory
open LeanVM.Guest.B1 LeanVM.Guest.B1.Tables
open LeanVM.Guest.B2C (fsN cellJ namedOf)
open LeanVM.Guest.Bridge (FnAl)
open LeanVM.Guest.Res (Wit witOk holdsBase inFr vtGrpB vtGrpRes)
open LeanVM.Protocol LeanVM.Protocol.Verifier
open LeanVM.Prover.Exec

public section

/-! ## A side's ranks -/

/-- **A side's ranks name each of its groups**, given each group's key `g^KN`. -/
theorem vtG_side {rd : Reader} {σ : Core.Val} {v0 s G0 m : ℕ} (KN : ℕ → ℕ)
    (hfacts : ∀ r < m, VtRankFacts rd σ v0 s r)
    (hside : ∀ e < 24, LoadHolds rd (σ (.n (val% «verify_tables» "g_squares"))) (212 + e) (word (vtGroupSide e) 0))
    (hsideS : ∀ e < 24, vtGroupSide e = s → G0 ≤ e ∧ e < G0 + m) (hs : s < 3)
    (hkey : ∀ e, G0 ≤ e → e < G0 + m → KN e < 2 ^ 62 ∧
      ∃ key, LoadHolds rd (σ (.n (val% «verify_tables» "group_key"))) e key ∧ key * gen ^ 153 = gen ^ KN e) :
    (∀ r < m, ∃ e, G0 ≤ e ∧ e < G0 + m ∧ σ (.n (vtRv v0 r)) = gen ^ e ∧
      σ (.n (vtRv v0 r + 8)) * gen ^ 153 = gen ^ KN e) ∧
    ∀ g < m, ∃ r < m, σ (.n (vtRv v0 r)) = gen ^ (G0 + g) := by
  have hrank : ∀ r < m, ∃ e, G0 ≤ e ∧ e < G0 + m ∧ σ (.n (vtRv v0 r)) = gen ^ e ∧
      σ (.n (vtRv v0 r + 8)) * gen ^ 153 = gen ^ KN e := by
    intro r hr
    obtain ⟨e, he, hσe⟩ := (hfacts r hr).1
    have h3 := (hfacts r hr).2.1
    rw [hσe, tb_loadHolds_mul_gen_pow, Nat.add_comm] at h3
    have hw := tb_loadHolds_unique h3 (hside e he)
    have hse := hsideS e he
      (vt_word_small_inj hs (by unfold vtGroupSide; split_ifs <;> omega) hw).symm
    obtain ⟨-, key, hk1, hk2⟩ := hkey e hse.1 hse.2
    have h4 := (hfacts r hr).2.2.1
    rw [hσe, tb_loadHolds_mul_gen_pow, Nat.add_zero] at h4
    rw [tb_loadHolds_unique h4 hk1]
    exact ⟨e, hse.1, hse.2, hσe, hk2⟩
  refine ⟨hrank, ?_⟩
  obtain ⟨o, ho⟩ := tb_exists_fun_of_forall (α := ℕ) (n := m)
    (P := fun r e ↦ G0 ≤ e ∧ e < G0 + m ∧ σ (.n (vtRv v0 r)) = gen ^ e ∧
      σ (.n (vtRv v0 r + 8)) * gen ^ 153 = gen ^ KN e) hrank
  have hstep : ∀ r, r + 1 < m → KN (o (r + 1)) < KN (o r) := fun r hr ↦ by
    obtain ⟨d, hd, hdv⟩ := (hfacts (r + 1) hr).2.2.2.2.2.2.2 (by omega)
    rw [Nat.add_sub_cancel] at hdv
    have e1 : gen ^ KN (o r) = gen ^ (d + 1) * gen ^ KN (o (r + 1)) := by
      rw [← (ho r (by omega)).2.2.2, ← (ho (r + 1) hr).2.2.2, hdv, mul_assoc]
    have k1 := (hkey _ (ho r (by omega)).1 (ho r (by omega)).2.1).1
    have k2 := (hkey _ (ho (r + 1) hr).1 (ho (r + 1) hr).2.1).1
    have := tb_gen_pow_eq_mul k1 k2 (by omega) e1
    omega
  have hdec : ∀ a k, a + k + 1 < m → KN (o (a + k + 1)) < KN (o a) := by
    intro a k
    induction k with
    | zero => intro h; exact hstep a (by omega)
    | succ k ih =>
      intro h
      have h1 := hstep (a + k + 1) (by omega)
      have h2 := ih (by omega)
      rw [show a + (k + 1) + 1 = a + k + 1 + 1 by omega]
      omega
  have hinj : Set.InjOn o (Finset.range m : Set ℕ) := by
    intro a ha b hb hab
    simp only [Finset.coe_range, Set.mem_Iio] at ha hb
    by_contra hne
    rcases Nat.lt_or_gt_of_ne hne with hlt | hlt
    · have := hdec a (b - a - 1) (by omega)
      rw [show a + (b - a - 1) + 1 = b by omega, ← hab] at this
      omega
    · have := hdec b (a - b - 1) (by omega)
      rw [show b + (a - b - 1) + 1 = a by omega, hab] at this
      omega
  have himg : (Finset.range m).image o = Finset.Ico G0 (G0 + m) := by
    apply Finset.eq_of_subset_of_card_le
    · intro x hx
      obtain ⟨r, hr, rfl⟩ := Finset.mem_image.mp hx
      have := ho r (Finset.mem_range.mp hr)
      exact Finset.mem_Ico.mpr ⟨this.1, this.2.1⟩
    · rw [Finset.card_image_of_injOn hinj]; simp
  intro g hg
  have hmem : G0 + g ∈ (Finset.range m).image o := by
    rw [himg]; exact Finset.mem_Ico.mpr ⟨by omega, by omega⟩
  obtain ⟨r, hr, hre⟩ := Finset.mem_image.mp hmem
  exact ⟨r, Finset.mem_range.mp hr, by rw [← hre]; exact (ho r (Finset.mem_range.mp hr)).2.2.1⟩

section
variable {μ : ℕ} (hμ : μ ≤ 32) (Lm : MemoryImage μ)
include hμ

/-- **`verify_tables`' groups**: each side's ranks name every group of the side, and rank `1`'s
keys are nonzero. -/
theorem vt_groups {σ : Core.Val} (h : VtH Lm.read σ) {lm : ℕ} (hlm : lm ≤ 32) {ds : List E}
    (hds : TbReadsAt Lm.read (σ (.n (val% «verify_tables» "dims_g"))) (gen ^ lm :: ds)) (hE : ExpTablesAt Lm.read (σ (.n (val% «verify_tables» "g_squares")))) :
    (∀ g < 9, ∃ r < 9, σ (.n (vtRv 112 r)) = gen ^ g) ∧
      (∀ g < 6, ∃ r < 6, σ (.n (vtRv 409 r)) = gen ^ (18 + g)) ∧ σ (.n (val% «verify_tables» "key@2")) ≠ 0 ∧ σ (.n (val% «verify_tables» "key@11")) ≠ 0 ∧
      (∀ r < 9, ∃ e < 9, σ (.n (vtRv 112 r)) = gen ^ e) ∧
      (∀ r < 6, ∃ e, 18 ≤ e ∧ e < 24 ∧ σ (.n (vtRv 409 r)) = gen ^ e) := by
  obtain ⟨k0, kl⟩ := vt_kb h
  have hpads := vt_pads hμ Lm σ h
  obtain ⟨τ, hτ⟩ := tb_exists_fun_of_forall (α := ℕ) (n := 6)
    (P := fun t τ ↦ τ < 31 ∧ σ (.n (28 + t)) = gen ^ τ) (fun t ht ↦ by
      obtain ⟨τ, n, zs, h1, h2, -⟩ := hpads t ht
      refine ⟨τ, h1, ?_⟩
      have := kl (t + 1) (by omega)
      rw [show 27 + (t + 1) = 28 + t by omega] at this
      exact tb_loadHolds_unique this h2)
  have hkb : ∀ i < 8, σ (.n ((val% «verify_tables» "kb[0]") + i)) = gen ^ ([0, lm] ++ vtTauList τ).getD i 0 := by
    intro i hi
    match i, hi with
    | 0, _ => simpa using k0
    | 1, _ =>
      have := tb_loadHolds_unique (kl 0 (by omega)) (hds 0 (by simp))
      simpa using this
    | t + 2, hi =>
      have ht : t < 6 := by omega
      rw [show 26 + (t + 2) = 28 + t by omega, (hτ t ht).2]
      simp only [List.cons_append, List.nil_append, List.getD_cons_succ]
      rw [List.getD_eq_getElem _ _ (by simp [vtTauList]; omega)]
      simp [vtTauList]
  have hτ33 : ∀ t < 6, τ t < 33 := fun t ht ↦ by have := (hτ t ht).1; omega
  obtain ⟨hsq, hrk, hsd, -⟩ := hE
  have hsrc : ∀ k < 15, blockKappaSrc.getD (vtB0 k) 0 < 8 := by decide +kernel
  have hkx : ∀ k < 15, σ (.n (vtKv k)) * gen ^ vtAdj k = gen ^ vtKap lm τ (vtB0 k) := by
    intro k hk
    unfold vtKv
    rw [hkb _ (hsrc k hk), ← pow_add, vtKap, vtAdj]
  have hb153 : ∀ k < 15, vtB0 k < 153 := by decide +kernel
  have hκ34 : ∀ k < 15, vtKap lm τ (vtB0 k) < 34 := fun k hk ↦ vt_kap_lt lm τ hlm hτ33 (hb153 k hk)
  -- the groups' keys
  have hG : ∀ k < 15, ∃ key, LoadHolds Lm.read (σ (.n (val% «verify_tables» "group_key"))) (vtGi k) key ∧
      key * gen ^ vtB0 k = gen ^ (vtKap lm τ (vtB0 k) * 247) := by
    intro k hk
    obtain ⟨key, rk, sz, sq, hk1, hrk1, hke, -⟩ := vt_grps h k hk
    rw [hkx k hk, tb_loadHolds_mul_gen_pow] at hrk1
    have r1 := hrk _ (by simp [rankKeysList]; exact hκ34 k hk)
    rw [tb_loadHolds_mul_gen_pow] at r1
    have e1 := tb_loadHolds_unique hrk1 (by rw [Nat.add_comm]; exact r1)
    simp only [rankKeysList, List.getElem_map, List.getElem_range] at e1
    exact ⟨key, hk1, by rw [hke, e1]⟩
  have hsideT : ∀ e < 24, LoadHolds Lm.read (σ (.n (val% «verify_tables» "g_squares"))) (212 + e) (word (vtGroupSide e) 0) :=
    fun e he ↦ by
      have := hsd e (by simp [sideTabList]; exact he)
      rw [tb_loadHolds_mul_gen_pow] at this
      rw [← vt_sideTab_getD e he, List.getD_eq_getElem _ _ (by simp [sideTabList]; exact he)]
      exact this
  -- a group's key, past `g^153`
  have hkeyK : ∀ k < 15, vtKap lm τ (vtB0 k) * 247 + 153 - vtB0 k < 2 ^ 62 ∧
      ∃ key, LoadHolds Lm.read (σ (.n (val% «verify_tables» "group_key"))) (vtGi k) key ∧
        key * gen ^ 153 = gen ^ (vtKap lm τ (vtB0 k) * 247 + 153 - vtB0 k) := by
    intro k hk
    obtain ⟨key, h1, h2⟩ := hG k hk
    have hb := hb153 k hk
    refine ⟨by have := hκ34 k hk; omega, key, h1, ?_⟩
    rw [show key * gen ^ 153 = key * gen ^ vtB0 k * gen ^ (153 - vtB0 k) by
      rw [mul_assoc, ← pow_add, Nat.add_sub_cancel' hb.le], h2, ← pow_add]
    congr 1
    omega
  have hP : ∀ r < 9, VtRankFacts Lm.read σ 112 0 r := fun r hr ↦ by
    rcases Nat.eq_zero_or_pos r with rfl | hr0
    · obtain ⟨k, hs⟩ := h.sliceAt 110 _ vtPush0_check
      exact vt_rank0 hμ Lm hs
    · obtain ⟨k, hs⟩ := h.sliceAt _ _ (vtPush_check r hr hr0)
      exact vt_rank hμ Lm hr0 hs
  have hC : ∀ r < 6, VtRankFacts Lm.read σ 409 2 r := fun r hr ↦ by
    rcases Nat.eq_zero_or_pos r with rfl | hr0
    · obtain ⟨k, hs⟩ := h.sliceAt 403 _ vtCount0_check
      exact vt_rank0 hμ Lm hs
    · obtain ⟨k, hs⟩ := h.sliceAt _ _ (vtCount_check r hr hr0)
      exact vt_rank hμ Lm hr0 hs
  have hS0 : ∀ e < 24, vtGroupSide e = 0 → 0 ≤ e ∧ e < 0 + 9 := by decide
  have hS2 : ∀ e < 24, vtGroupSide e = 2 → 18 ≤ e ∧ e < 18 + 6 := by decide
  obtain ⟨hPr, hPs⟩ := vtG_side (fun e ↦ vtKap lm τ (vtB0 e) * 247 + 153 - vtB0 e) hP hsideT hS0
    (by norm_num) (fun e _ he ↦ by
      have := hkeyK e (by omega)
      simpa [vtGi, show e < 9 by omega] using this)
  obtain ⟨hCr, hCs⟩ := vtG_side (fun e ↦ vtKap lm τ (vtB0 (e - 9)) * 247 + 153 - vtB0 (e - 9)) hC
    hsideT hS2 (by norm_num) (fun e he1 he2 ↦ by
      have := hkeyK (e - 9) (by omega)
      simpa [vtGi, show ¬(e - 9 < 9) by omega, show e - 9 + 9 = e by omega] using this)
  refine ⟨fun g hg ↦ by simpa using hPs g hg, hCs, fun h0 ↦ ?_, fun h0 ↦ ?_,
    fun r hr ↦ ?_, fun r hr ↦ ?_⟩
  · obtain ⟨e, -, -, -, hk⟩ := hPr 1 (by norm_num)
    rw [show vtRv 112 1 + 8 = 133 from rfl, h0, zero_mul] at hk
    exact Value.gen_pow_ne_zero _ hk.symm
  · obtain ⟨e, -, -, -, hk⟩ := hCr 1 (by norm_num)
    rw [show vtRv 409 1 + 8 = 430 from rfl, h0, zero_mul] at hk
    exact Value.gen_pow_ne_zero _ hk.symm
  · obtain ⟨e, -, he, hσ, -⟩ := hPr r hr
    exact ⟨e, by omega, hσ⟩
  · obtain ⟨e, h1, h2, hσ, -⟩ := hCr r hr
    exact ⟨e, h1, h2, hσ⟩

end

/-! ## At the honest instances -/

variable {r : Ref}

/-- **`verify_tables`' body and precondition** at an honest instance. -/
theorem vt_inst (hr : r.Ok) {J : Inst} (hJ : J ∈ honestInsts coreProgram B2C.fs B2C.H r.hdr r.T) {σ : Core.Val}
    {bufs : List ℕ} {kids : List Tree} (hJt : J.t = .node "verify_tables" σ bufs kids) :
    VtH r.img.read σ ∧ ∃ pi lm weights point values,
      TablesPre pi lm weights point values r.img.read ((List.range 21).map fun k ↦ σ (.n k)) := by
  obtain ⟨args, rets, hv⟩ := inst_valid' hr hJ hJt
  obtain ⟨-, hb⟩ := Res.holds_of_valid Res.fs_pos hv VerifySub.find_vt
  obtain ⟨hH, -⟩ := vt_holds (fun _ _ _ h ↦ Res.KidRel.rel h) VerifySub.find_vt hb
  exact ⟨hH, vtPQ_all hr J hJ σ bufs kids hJt⟩

/-- **`verify_tables`' groups at an honest instance.** -/
theorem vt_groups_at (hr : r.Ok) {J : Inst} (hJ : J ∈ honestInsts coreProgram B2C.fs B2C.H r.hdr r.T)
    {σ : Core.Val} {bufs : List ℕ} {kids : List Tree} (hJt : J.t = .node "verify_tables" σ bufs kids) :
    (∀ g < 9, ∃ r < 9, σ (.n (vtRv 112 r)) = gen ^ g) ∧
      (∀ g < 6, ∃ r < 6, σ (.n (vtRv 409 r)) = gen ^ (18 + g)) ∧ σ (.n (val% «verify_tables» "key@2")) ≠ 0 ∧ σ (.n (val% «verify_tables» "key@11")) ≠ 0 ∧
      (∀ r < 9, ∃ e < 9, σ (.n (vtRv 112 r)) = gen ^ e) ∧
      (∀ r < 6, ∃ e, 18 ≤ e ∧ e < 24 ∧ σ (.n (vtRv 409 r)) = gen ^ e) := by
  obtain ⟨hH, pi, lm, w, pt, vals, hP⟩ := vt_inst hr hJ hJt
  rw [show (List.range 21).map (fun k ↦ σ (.n k)) = [σ (.n (val% «verify_tables» "fs0")), σ (.n (val% «verify_tables» "fs1")), σ (.n (val% «verify_tables» "fs2")), σ (.n (val% «verify_tables» "fs3")), σ (.n (val% «verify_tables» "fs4")),
    σ (.n (val% «verify_tables» "cursor@1")), σ (.n (val% «verify_tables» "pi_0")), σ (.n (val% «verify_tables» "pi_1")), σ (.n (val% «verify_tables» "zeta")), σ (.n (val% «verify_tables» "g_bus_mu")), σ (.n (val% «verify_tables» "dims_g")), σ (.n (val% «verify_tables» "table_rows")), σ (.n (val% «verify_tables» "g_squares")), σ (.n (val% «verify_tables» "fp_w")),
    σ (.n (val% «verify_tables» "beta")), σ (.n (val% «verify_tables» "claim_pool")), σ (.n (val% «verify_tables» "chi")), σ (.n (val% «verify_tables» "gkr_leaves")), σ (.n (val% «verify_tables» "tabs")), σ (.n (val% «verify_tables» "bc_point")), σ (.n (val% «verify_tables» "stream"))] from rfl] at hP
  obtain ⟨-, -, -, -, -, hlm, ⟨ds, -, hds⟩, hE, -⟩ := hP
  have hκ : r.κ ≤ 28 := logMemorySize_le_28 (e := r.exec) hr.size
  exact vt_groups (by omega) r.img hH hlm hds hE

/-- **Rank `1`'s push key is nonzero.** -/
theorem nzVal_vt133 : NzVal "verify_tables" (.n (val% «verify_tables» "key@2")) := fun _ hr _ hI _ _ _ hIt ↦
  (vt_groups_at hr hI hIt).2.2.1

/-- **Rank `1`'s count key is nonzero.** -/
theorem nzVal_vt430 : NzVal "verify_tables" (.n (val% «verify_tables» "key@11")) := fun _ hr _ hI _ _ _ hIt ↦
  (vt_groups_at hr hI hIt).2.2.2.1

/-! ## The families at the honest frames -/

section

variable {A : String → FnAl} {K : Mode.Cert} {i : ℕ} {e : Bridge.Ent} {j : ℕ}

end

end

end LeanVM.Guest.EndExec
