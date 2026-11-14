/-
  LeanVM.Guest.B1.Tables.Vt.SelsAll

  `verify_tables`' block selectors, all of them: the push side's framework and table blocks and
  the count side's blocks, each the specification's `blockSel` of its side's log-sizes, and the
  sides' selector sums.
-/

module

public import LeanVM.Guest.B1.Tables.Vt.Sels
public import LeanVM.Guest.B1.Tables.Vt.SelFw
public import LeanVM.Guest.B1.Tables.Vt.Shared

/-!
# All the block selectors (G:1940-2027, 2068-2078, 2263-2337)

`vt_sels`: when `kappa_base` (frame variables `28 .. 35`) holds `1`, `g^log_mem` and the tables'
heights `g^τ`, the point fits the memory and bytecode blocks, the push side's three framework selectors and
`51` table block selectors are `blockSel (vtSizesP log_mem τ)`, the count side's `45` are
`blockSel (vtSizesC τ)`, and `selector_sum` is each side's sum.
-/

namespace LeanVM.Guest.B1.Tables

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Protocol LeanVM.Protocol.Verifier
open LeanVM.Protocol.EndToEnd.Complete (blockSel)
open Finset

@[expose] public section

/-- A list's sum through its indices. -/
theorem vt_sum_map_range {α : Type} [Inhabited α] (g : α → E) :
    ∀ l : List α, (l.map g).sum = ∑ i ∈ range l.length, g (l.getD i default)
  | [] => by simp
  | a :: l => by
    rw [List.map_cons, List.sum_cons, vt_sum_map_range g l, List.length_cons,
      sum_range_succ']
    simp [add_comm]

theorem vtSizesP_length (lm : ℕ) (τ : ℕ → ℕ) : (vtSizesP lm τ).length = 54 := by
  simp [vtSizesP, vtPushPadData_length]

theorem vtSizesC_length (τ : ℕ → ℕ) : (vtSizesC τ).length = 45 := by
  simp [vtSizesC, vtCountPadData_length]

/-- The push side's sizes, block by block. -/
theorem vt_sizesP_eq (lm : ℕ) (τ : ℕ → ℕ) : (List.range 54).map (vtKap lm τ) = vtSizesP lm τ := by
  apply List.ext_getElem (by rw [List.length_map, List.length_range, vtSizesP_length])
  intro c h1 h2
  simp only [List.length_map, List.length_range] at h1
  rw [List.getElem_map, List.getElem_range, ← List.getD_eq_getElem _ 0 h2, vt_kapP lm τ h1]

/-- The count side's sizes, block by block. -/
theorem vt_sizesC_eq (lm : ℕ) (τ : ℕ → ℕ) :
    (List.range 45).map (fun c ↦ vtKap lm τ (108 + c)) = vtSizesC τ := by
  apply List.ext_getElem (by rw [List.length_map, List.length_range, vtSizesC_length])
  intro c h1 h2
  simp only [List.length_map, List.length_range] at h1
  rw [List.getElem_map, List.getElem_range, ← List.getD_eq_getElem _ 0 h2, vt_kapC lm τ h1]

theorem vtSizesP_le (lm : ℕ) (τ : ℕ → ℕ) (hlm : lm ≤ 32) (hτ : ∀ t < 6, τ t < 33) (b : ℕ) :
    (vtSizesP lm τ).getD b 0 ≤ 34 := by
  rcases Nat.lt_or_ge b 54 with hb | hb
  · rw [← vt_kapP lm τ hb]; have := vt_kap_lt lm τ hlm hτ (b := b) (by omega); omega
  · rw [List.getD_eq_default _ _ (by rw [vtSizesP_length]; exact hb)]; omega

theorem vtSizesC_le (lm : ℕ) (τ : ℕ → ℕ) (hlm : lm ≤ 32) (hτ : ∀ t < 6, τ t < 33) (b : ℕ) :
    (vtSizesC τ).getD b 0 ≤ 34 := by
  rcases Nat.lt_or_ge b 45 with hb | hb
  · rw [← vt_kapC lm τ hb]; have := vt_kap_lt lm τ hlm hτ (b := 108 + b) (by omega); omega
  · rw [List.getD_eq_default _ _ (by rw [vtSizesC_length]; exact hb)]; omega

/-- The push table blocks' data: block `3 + i`, its table, its copy, the running sum's chain, the
shared tables' pointers it steps from. -/
theorem vt_pushSel_data : ∀ i < 51,
    (vtPushSel.getD i default).1 = 3 + i ∧
    (vtPushSel.getD i default).2.2.2.1 = (vtPushPadData.getD i default).2.1 ∧
    (vtPushPadData.getD i default).2.1 < 6 ∧
    vtSelCopy (vtPushSel.getD i default).2.2.1 (vtPushSel.getD i default).2.2.2.1
      (vtPushSel.getD i default).2.2.2.2.1 = (vtPushPadData.getD i default).2.2.1 ∧
    (vtPushSel.getD i default).2.2.2.2.1 = some (if i = 0 then 834 else
      vtSelSum (vtPushSel.getD (i - 1) default).2.2.1 (vtPushSel.getD (i - 1) default).2.2.2.1
        (vtPushSel.getD (i - 1) default).2.2.2.2.1) ∧
    (0 < (vtPushSel.getD i default).2.2.2.1 →
      (vtPushSel.getD i default).2.2.2.2.2.1 = vtEqV ((vtPushSel.getD i default).2.2.2.1 - 1) ∧
      (((vtPushSel.getD i default).2.2.2.2.2.2.1 = vtGV ((vtPushSel.getD i default).2.2.2.1 - 1) ∧
        (vtPushSel.getD i default).2.2.2.2.2.2.2 = 21299200) ∨
       ((vtPushSel.getD i default).2.2.2.1 = 2 ∧ (vtPushSel.getD i default).2.2.2.2.2.2.1 = 702 ∧
        (vtPushSel.getD i default).2.2.2.2.2.2.2 = 299140177199104))) := by decide

/-- The count blocks' data. -/
theorem vt_countSel_data : ∀ i < 45,
    (vtCountSel.getD i default).1 = 108 + i ∧
    (vtCountSel.getD i default).2.2.2.1 = (vtCountPadData.getD i default).2.1 ∧
    (vtCountPadData.getD i default).2.1 < 6 ∧
    vtSelCopy (vtCountSel.getD i default).2.2.1 (vtCountSel.getD i default).2.2.2.1
      (vtCountSel.getD i default).2.2.2.2.1 = (vtCountPadData.getD i default).2.2.1 ∧
    (vtCountSel.getD i default).2.2.2.2.1 = (if i = 0 then none else
      some (vtSelSum (vtCountSel.getD (i - 1) default).2.2.1
        (vtCountSel.getD (i - 1) default).2.2.2.1 (vtCountSel.getD (i - 1) default).2.2.2.2.1)) ∧
    (0 < (vtCountSel.getD i default).2.2.2.1 →
      (vtCountSel.getD i default).2.2.2.2.2.1 = vtEqV ((vtCountSel.getD i default).2.2.2.1 - 1) ∧
      (((vtCountSel.getD i default).2.2.2.2.2.2.1 = vtGV ((vtCountSel.getD i default).2.2.2.1 - 1) ∧
        (vtCountSel.getD i default).2.2.2.2.2.2.2 = 21299200) ∨
       ((vtCountSel.getD i default).2.2.2.1 = 2 ∧ (vtCountSel.getD i default).2.2.2.2.2.2.1 = 702 ∧
        (vtCountSel.getD i default).2.2.2.2.2.2.2 = 299140177199104))) := by
  decide

theorem vt_pushSel_last : vtSelSum (vtPushSel.getD 50 default).2.2.1
    (vtPushSel.getD 50 default).2.2.2.1 (vtPushSel.getD 50 default).2.2.2.2.1 = 1290 := by decide

theorem vt_countSel_last : vtSelSum (vtCountSel.getD 44 default).2.2.1
    (vtCountSel.getD 44 default).2.2.2.1 (vtCountSel.getD 44 default).2.2.2.2.1 = 1823 := by
  decide

/-- A running sum: each step adds its term to the previous step's sum. -/
theorem vt_running_sum (S : ℕ → E) (prev : ℕ → E) (x : ℕ → E) (s0 : E) (n : ℕ)
    (hstep : ∀ i < n, S i = prev i + x i) (h0 : prev 0 = s0)
    (hchain : ∀ i, 0 < i → i < n → prev i = S (i - 1)) :
    ∀ k < n, S k = s0 + ∑ i ∈ range (k + 1), x i := by
  intro k hk
  induction k with
  | zero => rw [hstep 0 hk, h0]; simp
  | succ k ih =>
    rw [hstep (k + 1) hk, hchain (k + 1) (by omega) hk, Nat.add_sub_cancel, ih (by omega),
      sum_range_succ _ (k + 1)]
    ring

/-- The shared tables' pointers a table block `t > 0` steps from. -/
theorem vt_ptr_step {rd : Reader} {σ : Val} (h : VtH rd σ) {t : ℕ} (ht : t < 6) (ht0 : 0 < t) :
    σ (.n (vtEqV (t - 1))) * vtW288 = σ (.n 701) * gen ^ (288 * t) ∧
      σ (.n (vtGV (t - 1))) * word 21299200 0 = σ (.n 702) * gen ^ (144 * t) := by
  obtain ⟨e1, e2⟩ := vt_ptrs h (t - 1) (by omega)
  obtain ⟨s, rfl⟩ : ∃ s, t = s + 1 := ⟨t - 1, by omega⟩
  simp only [Nat.add_sub_cancel] at e1 e2 ⊢
  rw [e1, e2, show vtW288 = gen ^ 288 from vtW288_eq, vtW144_eq, mul_assoc, mul_assoc, ← pow_add,
    ← pow_add]
  constructor <;> ring_nf

section
variable {μ : ℕ} (hμ : μ ≤ 32) (Lm : MemoryImage μ)
include hμ

/-- **All the block selectors.** -/
theorem vt_sels {σ : Val} (h : VtH Lm.read σ) {point : List E}
    (hz : TbReadsAt Lm.read (σ (.n 8)) point) (hmu : σ (.n 9) = gen ^ point.length)
    (hml : point.length < 33) (hE : ExpTablesAt Lm.read (σ (.n 12))) {lm : ℕ}
    (hlm : lm ≤ 32) {τ : ℕ → ℕ} (hτ : ∀ t < 6, τ t < 33)
    (hkb : ∀ i < 8, σ (.n (25 + i)) = gen ^ ([0, lm] ++ vtTauList τ).getD i 0) :
    lm ≤ point.length ∧ 19 ≤ point.length ∧
      σ (.n 788) = blockSel (vtSizesP lm τ) point.length 0 point ∧
      σ (.n 804) = blockSel (vtSizesP lm τ) point.length 1 point ∧
      σ (.n 832) = blockSel (vtSizesP lm τ) point.length 2 point ∧
      σ (.n 790) = σ (.n 788) ∧ σ (.n 807) = σ (.n 804) ∧ σ (.n 835) = σ (.n 832) ∧
      (∀ i < 51, σ (.n (vtPushPadData.getD i default).2.2.1) =
        blockSel (vtSizesP lm τ) point.length (3 + i) point) ∧
      σ (.n 1290) = σ (.n 788) + σ (.n 804) + σ (.n 832) +
        (vtPushPadData.map fun x ↦ σ (.n x.2.2.1)).sum ∧
      (∀ i < 45, σ (.n (vtCountPadData.getD i default).2.2.1) =
        blockSel (vtSizesC τ) point.length i point) ∧
      σ (.n 1823) = (vtCountPadData.map fun x ↦ σ (.n x.2.2.1)).sum := by
  have hsq : TbReadsAt Lm.read (σ (.n 12)) gSquaresList := hE.1
  obtain ⟨hoP, hoC⟩ := vt_sort hμ Lm h hlm hτ hkb hE
  rw [vt_sizesP_eq] at hoP
  rw [vt_sizesC_eq] at hoC
  have hobP : ∀ b, (stackOffsets (vtSizesP lm τ)).1.getD b 0 < 2 ^ 62 :=
    vt_stackOffsets_lt _ (by rw [vtSizesP_length]; norm_num) (vtSizesP_le lm τ hlm hτ)
  have hobC : ∀ b, (stackOffsets (vtSizesC τ)).1.getD b 0 < 2 ^ 62 :=
    vt_stackOffsets_lt _ (by rw [vtSizesC_length]; norm_num) (vtSizesC_le lm τ hlm hτ)
  have hz1 := vt_zeta1 h hz hmu (by omega)
  have hidxc := vt_idxc h
  have hkbt : ∀ t < 6, σ (.n (27 + t)) = gen ^ τ t := fun t ht => by
    have := hkb (2 + t) (by omega)
    rwa [show 25 + (2 + t) = 27 + t by omega, Nat.add_comm 2 t, vt_tau_getD lm τ ht] at this
  -- the framework blocks
  have k0 : σ (.n 25) = gen ^ (vtSizesP lm τ).getD 0 0 := hkb 0 (by norm_num)
  have k1 : σ (.n 26) = gen ^ (vtSizesP lm τ).getD 1 0 := hkb 1 (by norm_num)
  have k2 : σ (.n 821) = gen ^ (vtSizesP lm τ).getD 2 0 := by
    have e0 : σ (.n 25) = 1 := by simpa using hkb 0 (by norm_num)
    rw [vt_fw2_kappa h, e0, one_mul]; rfl
  have f0 := vt_fwblock hμ Lm h vtFw0_check hmu hml hz1 hidxc k0 (by simp [vtSizesP])
    (hoP 0 (by norm_num)) (hobP 0)
  have f1 := vt_fwblock hμ Lm h vtFw1_check hmu hml hz1 hidxc k1 (by simp [vtSizesP]; omega)
    (hoP 1 (by norm_num)) (hobP 1)
  have f2 := vt_fwblock hμ Lm h vtFw2_check hmu hml hz1 hidxc k2 (by simp [vtSizesP])
    (hoP 2 (by norm_num)) (hobP 2)
  simp only [Option.isNone_none, Option.isNone_some, ↓reduceIte, Bool.false_eq_true,
    Nat.reduceAdd, vt_eqAbove_blockSel] at f0 f1 f2
  obtain ⟨-, s0, c0, -⟩ := f0
  obtain ⟨l1, s1, c1, u1⟩ := f1
  obtain ⟨l2, s2, c2, u2⟩ := f2
  simp only [vtSizesP, List.cons_append, List.getD_cons_succ, List.getD_cons_zero] at l1 l2
  -- the shared tables
  have hsh : ∀ t < 6, ∃ d, σ (.n (vtShLen t)) = gen ^ d ∧ point.length = d + τ t ∧
      RunTables Lm.read (σ (.n 701) * gen ^ (288 * t)) (σ (.n 702) * gen ^ (144 * t)) d
        (point.drop (τ t)) ((point.map (1 + ·)).drop (τ t)) ((gSquaresList.drop (τ t)).take d) :=
    fun t ht => vt_shared hμ Lm h hz hmu hml hz1 hsq ht (hτ t ht) (hkbt t ht)
  -- a table block's selector
  have hblk : ∀ {sizes : List ℕ} {b c w t : ℕ} {prev : Option ℕ} {pos es gs gw : ℕ},
      tbStmtsEqb (vtSelT w b t prev es gs gw)
        ((vtAt pos).take (vtSelT w b t prev es gs gw).length) = true →
      t < 6 → (0 < t → es = vtEqV (t - 1) ∧ ((gs = vtGV (t - 1) ∧ gw = 21299200) ∨
        (t = 2 ∧ gs = 702 ∧ gw = 299140177199104))) →
      sizes.getD c 0 = τ t → (∀ b, (stackOffsets sizes).1.getD b 0 < 2 ^ 62) →
      σ (.n (vtBoffV b)) = gen ^ (stackOffsets sizes).1.getD c 0 →
      σ (.n (vtSelE w t)) = blockSel sizes point.length c point ∧
        σ (.n (vtSelCopy w t prev)) = σ (.n (vtSelE w t)) ∧
        σ (.n (vtSelSum w t prev)) = (match prev with | none => 0 | some p => σ (.n p)) +
          σ (.n (vtSelE w t)) := by
    intro sizes b c w t prev pos es gs gw hc ht hd hsz hob hoff
    obtain ⟨d, hdv, hpl, hrun⟩ := hsh t ht
    have hptr : 0 < t → σ (.n es) * vtW288 = σ (.n 701) * gen ^ (288 * t) ∧
        σ (.n gs) * word gw 0 = σ (.n 702) * gen ^ (144 * t) := fun ht0 => by
      obtain ⟨rfl, hg⟩ := hd ht0
      refine ⟨(vt_ptr_step h ht ht0).1, ?_⟩
      rcases hg with ⟨rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
      · exact (vt_ptr_step h ht ht0).2
      · rw [vtW288_eq]
    obtain ⟨e1, e2, e3⟩ := vt_selblock hμ Lm h hc ht hptr hpl (by have := hτ t ht; omega) hdv
      hrun hoff (hob c)
    rw [← hsz, vt_eqAbove_blockSel] at e1
    exact ⟨e1, e2, e3⟩
  -- the push table blocks
  have hP : ∀ i < 51,
      σ (.n (vtSelE (vtPushSel.getD i default).2.2.1 (vtPushSel.getD i default).2.2.2.1)) =
        blockSel (vtSizesP lm τ) point.length (3 + i) point ∧
      σ (.n (vtPushPadData.getD i default).2.2.1) = σ (.n (vtSelE (vtPushSel.getD i default).2.2.1
        (vtPushSel.getD i default).2.2.2.1)) ∧
      σ (.n (vtSelSum (vtPushSel.getD i default).2.2.1 (vtPushSel.getD i default).2.2.2.1
        (vtPushSel.getD i default).2.2.2.2.1)) =
        σ (.n (if i = 0 then 834 else vtSelSum (vtPushSel.getD (i - 1) default).2.2.1
          (vtPushSel.getD (i - 1) default).2.2.2.1 (vtPushSel.getD (i - 1) default).2.2.2.2.1)) +
        σ (.n (vtSelE (vtPushSel.getD i default).2.2.1 (vtPushSel.getD i default).2.2.2.1)) := by
    intro i hi
    obtain ⟨d1, d2, d3, d4, d5, d6⟩ := vt_pushSel_data i hi
    have hsz : (vtSizesP lm τ).getD (vtPushSel.getD i default).1 0 =
        τ (vtPushSel.getD i default).2.2.2.1 := by
      rw [d1, d2, ← vt_kapP lm τ (by omega)]
      obtain ⟨e1, e2, e3⟩ := vt_srcP i hi
      rw [vtKap, e1, e2, vt_tau_getD lm τ e3, Nat.add_zero]
    obtain ⟨e1, e2, e3⟩ := hblk (c := (vtPushSel.getD i default).1)
      (vtPushSel_check i (by rw [show vtPushSel.length = 51 from rfl]; exact hi))
      (by rw [d2]; exact d3) d6 hsz hobP (by rw [d1]; exact hoP _ (by omega))
    rw [d1] at e1
    rw [d4] at e2
    refine ⟨e1, e2, ?_⟩
    rw [e3, d5]
  -- the count blocks
  have hC : ∀ i < 45,
      σ (.n (vtSelE (vtCountSel.getD i default).2.2.1 (vtCountSel.getD i default).2.2.2.1)) =
        blockSel (vtSizesC τ) point.length i point ∧
      σ (.n (vtCountPadData.getD i default).2.2.1) = σ (.n (vtSelE (vtCountSel.getD i default).2.2.1
        (vtCountSel.getD i default).2.2.2.1)) ∧
      σ (.n (vtSelSum (vtCountSel.getD i default).2.2.1 (vtCountSel.getD i default).2.2.2.1
        (vtCountSel.getD i default).2.2.2.2.1)) =
        (if i = 0 then 0 else σ (.n (vtSelSum (vtCountSel.getD (i - 1) default).2.2.1
          (vtCountSel.getD (i - 1) default).2.2.2.1
          (vtCountSel.getD (i - 1) default).2.2.2.2.1))) +
        σ (.n (vtSelE (vtCountSel.getD i default).2.2.1 (vtCountSel.getD i default).2.2.2.1)) := by
    intro i hi
    obtain ⟨d1, d2, d3, d4, d5, d6⟩ := vt_countSel_data i hi
    have hsz : (vtSizesC τ).getD i 0 = τ (vtCountSel.getD i default).2.2.2.1 := by
      rw [d2, ← vt_kapC lm τ hi]
      obtain ⟨e1, e2, e3⟩ := vt_srcC i hi
      rw [vtKap, e1, e2, vt_tau_getD lm τ e3, Nat.add_zero]
    obtain ⟨e1, e2, e3⟩ := hblk (c := i)
      (vtCountSel_check i (by rw [show vtCountSel.length = 45 from rfl]; exact hi))
      (by rw [d2]; exact d3) d6 hsz hobC (by rw [d1]; exact hoC i hi)
    rw [d4] at e2
    refine ⟨e1, e2, ?_⟩
    rw [e3, d5]
    split_ifs <;> rfl
  -- the sums
  have hsumP := vt_running_sum (fun i ↦ σ (.n (vtSelSum (vtPushSel.getD i default).2.2.1
      (vtPushSel.getD i default).2.2.2.1 (vtPushSel.getD i default).2.2.2.2.1)))
    (fun i ↦ σ (.n (if i = 0 then 834 else vtSelSum (vtPushSel.getD (i - 1) default).2.2.1
      (vtPushSel.getD (i - 1) default).2.2.2.1 (vtPushSel.getD (i - 1) default).2.2.2.2.1)))
    (fun i ↦ σ (.n (vtPushPadData.getD i default).2.2.1)) (σ (.n 834)) 51
    (fun i hi ↦ by rw [(hP i hi).2.2, (hP i hi).2.1]) (by simp)
    (fun i h0 _ ↦ by simp [show i ≠ 0 by omega]) 50 (by norm_num)
  have hsumC := vt_running_sum (fun i ↦ σ (.n (vtSelSum (vtCountSel.getD i default).2.2.1
      (vtCountSel.getD i default).2.2.2.1 (vtCountSel.getD i default).2.2.2.2.1)))
    (fun i ↦ if i = 0 then 0 else σ (.n (vtSelSum (vtCountSel.getD (i - 1) default).2.2.1
      (vtCountSel.getD (i - 1) default).2.2.2.1 (vtCountSel.getD (i - 1) default).2.2.2.2.1)))
    (fun i ↦ σ (.n (vtCountPadData.getD i default).2.2.1)) 0 45
    (fun i hi ↦ by rw [(hC i hi).2.2, (hC i hi).2.1]) (by simp)
    (fun i h0 _ ↦ by simp [show i ≠ 0 by omega]) 44 (by norm_num)
  simp only [vt_pushSel_last] at hsumP
  simp only [vt_countSel_last] at hsumC
  refine ⟨l1, l2, s0, s1, s2, c0, c1, c2,
    fun i hi ↦ (hP i hi).2.1.trans (hP i hi).1, ?_, fun i hi ↦ (hC i hi).2.1.trans (hC i hi).1, ?_⟩
  · rw [hsumP, u2, u1, vt_sum_map_range, vtPushPadData_length]
  · rw [hsumC, vt_sum_map_range, vtCountPadData_length, zero_add]

end

end
end LeanVM.Guest.B1.Tables
