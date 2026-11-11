/-
  LeanVM.Guest.B1.Tables.VtC.BSels

  All `verify_tables`' block selectors complete: the push side's three framework blocks and `51`
  table blocks, the count side's `45`, each on its honest offset, digits or bits and returns.
-/

module

public import LeanVM.Guest.B1.Tables.VtC.BSel
public import LeanVM.Guest.B1.Tables.VtC.BStack
public import LeanVM.Guest.B1.Tables.VtC.SShT
public import LeanVM.Guest.B1.Tables.Vt.SelsAll

/-!
# The block selectors, all (G:2206-2252)

`vtFwW b`: framework block `b`'s first value. `vtc_sels`: with `kappa_base` the memory's log-size
and the tables' heights, every push and count block's offset its side's `stackOffsets` offset
(`vtS_complete`), the sides fitting the bus cube, the shared tables in place, and the memory and the
oracle holding the honest bits, digits and returns, every selector's statements hold and the
selectors are `blockSel` (the soundness's `vt_sels`, from the honest valuation).
-/

namespace LeanVM.Guest.B1.Tables

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Guest.B1.Fwd LeanVM.Protocol LeanVM.Protocol.Verifier
open LeanVM.Protocol.EndToEnd.Complete (blockSel)
open Finset (range)

@[expose] public section

/-- Framework block `b`'s first value. -/
def vtFwW (b : ℕ) : ℕ := [778, 794, 822].getD b 0

theorem vtIdxcW_eq : vtIdxcW = vtIdxcList := rfl

section
variable {rd : Reader} {wo : ℕ → E} {args : List E}

local notation "σv" => vtσ rd wo args

/-- **All the block selectors, complete.** -/
theorem vtc_sels (hl : args.length = 20) (hlow : LowDefB 14 rd) {point : List E}
    (hmu : σv (.n 9) = gen ^ point.length) (hml : point.length < 33)
    (hz1 : TbReadsAt rd (σv (.n 699)) (point.map (1 + ·)))
    (hidxc : TbReadsAt rd (σv (.n 664)) vtIdxcW) {lm : ℕ} (hlmμ : lm ≤ point.length)
    (h19 : 19 ≤ point.length) {τ : ℕ → ℕ} (hτμ : ∀ t < 6, τ t ≤ point.length)
    (hkb : ∀ i < 8, σv (.n (25 + i)) = gen ^ ([0, lm] ++ vtTauList τ).getD i 0)
    (hfitP : ((vtSizesP lm τ).map (2 ^ ·)).sum ≤ 2 ^ point.length)
    (hfitC : ((vtSizesC τ).map (2 ^ ·)).sum ≤ 2 ^ point.length)
    (hoP : ∀ x < 54, σv (.n (vtBoffV x)) = gen ^ (stackOffsets (vtSizesP lm τ)).1.getD x 0)
    (hoC : ∀ x < 45, σv (.n (vtBoffV (108 + x))) = gen ^ (stackOffsets (vtSizesC τ)).1.getD x 0)
    (hsh : ∀ t < 6, σv (.n (vtShLen t)) = gen ^ (point.length - τ t))
    (hrun : ∀ t < 6, RunTables rd (σv (.n 701) * gen ^ (288 * t)) (σv (.n 702) * gen ^ (144 * t))
      (point.length - τ t) (point.drop (τ t)) ((point.map (1 + ·)).drop (τ t))
      ((gSquaresList.drop (τ t)).take (point.length - τ t)))
    (hbitsF : ∀ b < 3, TbReadsAt rd (wo (vtFwW b + 6))
      (offBits ((stackOffsets (vtSizesP lm τ)).1.getD b 0)))
    (hdigP : ∀ i < 51, TbReadsAt rd (wo (vtPushSel.getD i default).2.2.1)
      (offDigits ((stackOffsets (vtSizesP lm τ)).1.getD (3 + i) 0)
        (τ (vtPushSel.getD i default).2.2.2.1)))
    (hdigC : ∀ i < 45, TbReadsAt rd (wo (vtCountSel.getD i default).2.2.1)
      (offDigits ((stackOffsets (vtSizesC τ)).1.getD i 0) (τ (vtCountSel.getD i default).2.2.2.1)))
    (hwF : ∀ b < 3, wo (vtFwW b + 10) = blockSel (vtSizesP lm τ) point.length b point ∧
      wo (vtFwW b + 11) = gen ^ (stackOffsets (vtSizesP lm τ)).1.getD b 0)
    (hwP : ∀ i < 51, wo (vtSelE (vtPushSel.getD i default).2.2.1 (vtPushSel.getD i default).2.2.2.1) =
        blockSel (vtSizesP lm τ) point.length (3 + i) point ∧
      wo (vtSelE (vtPushSel.getD i default).2.2.1 (vtPushSel.getD i default).2.2.2.1 + 1) =
        gen ^ (stackOffsets (vtSizesP lm τ)).1.getD (3 + i) 0)
    (hwC : ∀ i < 45, wo (vtSelE (vtCountSel.getD i default).2.2.1
        (vtCountSel.getD i default).2.2.2.1) = blockSel (vtSizesC τ) point.length i point ∧
      wo (vtSelE (vtCountSel.getD i default).2.2.1 (vtCountSel.getD i default).2.2.2.1 + 1) =
        gen ^ (stackOffsets (vtSizesC τ)).1.getD i 0) :
    (∀ s ∈ vtFwSelT 778 0 25 none, VSH (coreProgram.Rel rd) rd σv s) ∧
      (∀ s ∈ vtFwSelT 794 1 26 (some 788), VSH (coreProgram.Rel rd) rd σv s) ∧
      (∀ s ∈ vtFwSelT 822 2 821 (some 806), VSH (coreProgram.Rel rd) rd σv s) ∧
      (∀ i < 51, ∀ s ∈ vtSelT (vtPushSel.getD i default).2.2.1 (vtPushSel.getD i default).1
        (vtPushSel.getD i default).2.2.2.1 (vtPushSel.getD i default).2.2.2.2.1
        (vtPushSel.getD i default).2.2.2.2.2.1 (vtPushSel.getD i default).2.2.2.2.2.2.1
        (vtPushSel.getD i default).2.2.2.2.2.2.2, VSH (coreProgram.Rel rd) rd σv s) ∧
      (∀ i < 45, ∀ s ∈ vtSelT (vtCountSel.getD i default).2.2.1 (vtCountSel.getD i default).1
        (vtCountSel.getD i default).2.2.2.1 (vtCountSel.getD i default).2.2.2.2.1
        (vtCountSel.getD i default).2.2.2.2.2.1 (vtCountSel.getD i default).2.2.2.2.2.2.1
        (vtCountSel.getD i default).2.2.2.2.2.2.2, VSH (coreProgram.Rel rd) rd σv s) ∧
      σv (.n 788) = blockSel (vtSizesP lm τ) point.length 0 point ∧
      σv (.n 804) = blockSel (vtSizesP lm τ) point.length 1 point ∧
      σv (.n 832) = blockSel (vtSizesP lm τ) point.length 2 point ∧
      σv (.n 790) = σv (.n 788) ∧ σv (.n 807) = σv (.n 804) ∧ σv (.n 835) = σv (.n 832) ∧
      (∀ i < 51, σv (.n (vtPushPadData.getD i default).2.2.1) =
        blockSel (vtSizesP lm τ) point.length (3 + i) point) ∧
      σv (.n 1290) = σv (.n 788) + σv (.n 804) + σv (.n 832) +
        (vtPushPadData.map fun x ↦ σv (.n x.2.2.1)).sum ∧
      (∀ i < 45, σv (.n (vtCountPadData.getD i default).2.2.1) =
        blockSel (vtSizesC τ) point.length i point) ∧
      σv (.n 1823) = (vtCountPadData.map fun x ↦ σv (.n x.2.2.1)).sum := by
  have hlow16 : ∀ i < 16, (rd (Parameters.addressOfIndex i)).isSome := fun i hi ↦
    hlow i (by norm_num; omega)
  have hkbt : ∀ t < 6, σv (.n (27 + t)) = gen ^ τ t := fun t ht => by
    have := hkb (2 + t) (by omega)
    rwa [show 25 + (2 + t) = 27 + t by omega, Nat.add_comm 2 t, vt_tau_getD lm τ ht] at this
  have hlenP := vtSizesP_length lm τ
  have hlenC := vtSizesC_length τ
  have halP : ∀ b < 54, 2 ^ (vtSizesP lm τ).getD b 0 ∣ (stackOffsets (vtSizesP lm τ)).1.getD b 0 :=
    fun b hb ↦ vtB_stack_aligned _ (by rw [hlenP]; exact hb)
  have halC : ∀ b < 45, 2 ^ (vtSizesC τ).getD b 0 ∣ (stackOffsets (vtSizesC τ)).1.getD b 0 :=
    fun b hb ↦ vtB_stack_aligned _ (by rw [hlenC]; exact hb)
  have hobP : ∀ b < 54, (stackOffsets (vtSizesP lm τ)).1.getD b 0 < 2 ^ point.length :=
    fun b hb ↦ vtB_stack_lt _ (by rw [hlenP]; exact hb) hfitP
  have hobC : ∀ b < 45, (stackOffsets (vtSizesC τ)).1.getD b 0 < 2 ^ point.length :=
    fun b hb ↦ vtB_stack_lt _ (by rw [hlenC]; exact hb) hfitC
  -- the framework blocks
  have k0 : σv (.n 25) = gen ^ (vtSizesP lm τ).getD 0 0 := hkb 0 (by norm_num)
  have k1 : σv (.n 26) = gen ^ (vtSizesP lm τ).getD 1 0 := hkb 1 (by norm_num)
  have k2 : σv (.n 821) = gen ^ (vtSizesP lm τ).getD 2 0 := by
    have e0 : σv (.n 25) = 1 := by simpa using hkb 0 (by norm_num)
    rw [vt_mulAt hl 810 (d := 821) (x := 25) (y := 820) (by norm_num) (by norm_num)
        (by decide +kernel), vt_constAt hl 809 (d := .n 820) (e := word 524288 0)
        (by decide +kernel), show (524288 : ℕ) = 2 ^ 19 by norm_num,
      tb_word_two_pow (by norm_num), e0, one_mul]
    rfl
  have f0 := vtc_fwblock (wo := wo) hl vtFw0_check (by norm_num) (by norm_num) hmu hml hz1
    hidxc k0 (by simp [vtSizesP]) (hoP 0 (by norm_num)) (halP 0 (by norm_num)) (hobP 0 (by norm_num))
    (hbitsF 0 (by norm_num)) (by rw [vt_eqAbove_blockSel]; exact (hwF 0 (by norm_num)).1)
    (hwF 0 (by norm_num)).2 hlow
  have f1 := vtc_fwblock (wo := wo) hl vtFw1_check (by norm_num) (by norm_num) hmu hml hz1
    hidxc k1 (by simp [vtSizesP]; omega) (hoP 1 (by norm_num)) (halP 1 (by norm_num))
    (hobP 1 (by norm_num)) (hbitsF 1 (by norm_num))
    (by rw [vt_eqAbove_blockSel]; exact (hwF 1 (by norm_num)).1) (hwF 1 (by norm_num)).2 hlow
  have f2 := vtc_fwblock (wo := wo) hl vtFw2_check (by norm_num) (by norm_num) hmu hml hz1
    hidxc k2 (by simp [vtSizesP]; omega) (hoP 2 (by norm_num)) (halP 2 (by norm_num))
    (hobP 2 (by norm_num)) (hbitsF 2 (by norm_num))
    (by rw [vt_eqAbove_blockSel]; exact (hwF 2 (by norm_num)).1) (hwF 2 (by norm_num)).2 hlow
  simp only [Option.isNone_none, Option.isNone_some, ↓reduceIte, Bool.false_eq_true,
    Nat.reduceAdd, vt_eqAbove_blockSel] at f0 f1 f2
  obtain ⟨a0, s0, c0, -⟩ := f0
  obtain ⟨a1, s1, c1, u1⟩ := f1
  obtain ⟨a2, s2, c2, u2⟩ := f2
  -- the pointers' steps
  have hstep : ∀ t < 6, 0 < t →
      σv (.n (vtEqV (t - 1))) * vtW288 = σv (.n 701) * gen ^ (288 * t) ∧
        σv (.n (vtGV (t - 1))) * word 21299200 0 = σv (.n 702) * gen ^ (144 * t) := by
    intro t ht ht0
    obtain ⟨e1, e2⟩ := vtc_shptr (rd := rd) (w := wo) hl (t - 1) (by omega)
    obtain ⟨s, rfl⟩ : ∃ s, t = s + 1 := ⟨t - 1, by omega⟩
    simp only [Nat.add_sub_cancel] at e1 e2 ⊢
    rw [e1, e2, show vtW288 = gen ^ 288 from vtW288_eq, vtW144_eq, mul_assoc, mul_assoc,
      ← pow_add, ← pow_add]
    constructor <;> ring_nf
  -- a table block's selector
  have hblk : ∀ {sizes : List ℕ} {b c w t : ℕ} {prev : Option ℕ} {pos es gs gw : ℕ},
      tbStmtsEqb (vtSelT w b t prev es gs gw)
        ((vtAt pos).take (vtSelT w b t prev es gs gw).length) = true →
      t < 6 → (0 < t → es = vtEqV (t - 1) ∧ ((gs = vtGV (t - 1) ∧ gw = 21299200) ∨
        (t = 2 ∧ gs = 702 ∧ gw = 299140177199104))) →
      es < w + 2 → gs < w + 4 →
      sizes.getD c 0 = τ t → 2 ^ τ t ∣ (stackOffsets sizes).1.getD c 0 →
      (stackOffsets sizes).1.getD c 0 < 2 ^ point.length →
      σv (.n (vtBoffV b)) = gen ^ (stackOffsets sizes).1.getD c 0 →
      TbReadsAt rd (wo w) (offDigits ((stackOffsets sizes).1.getD c 0) (τ t)) →
      wo (vtSelE w t) = blockSel sizes point.length c point →
      wo (vtSelE w t + 1) = gen ^ (stackOffsets sizes).1.getD c 0 →
      (∀ s ∈ vtSelT w b t prev es gs gw, VSH (coreProgram.Rel rd) rd σv s) ∧
        σv (.n (vtSelE w t)) = blockSel sizes point.length c point ∧
        σv (.n (vtSelCopy w t prev)) = σv (.n (vtSelE w t)) ∧
        σv (.n (vtSelSum w t prev)) = (match prev with | none => 0 | some p => σv (.n p)) +
          σv (.n (vtSelE w t)) := by
    intro sizes b c w t prev pos es gs gw hc ht hd hes hgs hsz hal hob hoff hdig hw0 hw1
    have hptr : 0 < t → σv (.n es) * vtW288 = σv (.n 701) * gen ^ (288 * t) ∧
        σv (.n gs) * word gw 0 = σv (.n 702) * gen ^ (144 * t) := fun ht0 => by
      obtain ⟨rfl, hg⟩ := hd ht0
      refine ⟨(hstep t ht ht0).1, ?_⟩
      rcases hg with ⟨rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
      · exact (hstep t ht ht0).2
      · rw [vtW288_eq]
    obtain ⟨e0, e1, e2, e3⟩ := vtc_selblock (wo := wo) hl hc ht hes hgs hptr
      (by have := hτμ t ht; omega : point.length = (point.length - τ t) + τ t) hml (hsh t ht)
      (hrun t ht) hoff hal hob hdig (by rw [hw0, ← hsz, vt_eqAbove_blockSel]) hw1 hlow16
    rw [← hsz, vt_eqAbove_blockSel] at e1
    exact ⟨e0, e1, e2, e3⟩
  -- the push table blocks
  have hrowP : ∀ i < 51, (vtPushSel.getD i default).2.2.2.2.2.1 <
      (vtPushSel.getD i default).2.2.1 + 2 ∧
      (vtPushSel.getD i default).2.2.2.2.2.2.1 < (vtPushSel.getD i default).2.2.1 + 4 := by
    decide +kernel
  have hrowC : ∀ i < 45, (vtCountSel.getD i default).2.2.2.2.2.1 <
      (vtCountSel.getD i default).2.2.1 + 2 ∧
      (vtCountSel.getD i default).2.2.2.2.2.2.1 < (vtCountSel.getD i default).2.2.1 + 4 := by
    decide +kernel
  have hP : ∀ i < 51, (∀ s ∈ vtSelT (vtPushSel.getD i default).2.2.1 (vtPushSel.getD i default).1
        (vtPushSel.getD i default).2.2.2.1 (vtPushSel.getD i default).2.2.2.2.1
        (vtPushSel.getD i default).2.2.2.2.2.1 (vtPushSel.getD i default).2.2.2.2.2.2.1
        (vtPushSel.getD i default).2.2.2.2.2.2.2, VSH (coreProgram.Rel rd) rd σv s) ∧
      σv (.n (vtSelE (vtPushSel.getD i default).2.2.1 (vtPushSel.getD i default).2.2.2.1)) =
        blockSel (vtSizesP lm τ) point.length (3 + i) point ∧
      σv (.n (vtPushPadData.getD i default).2.2.1) =
        σv (.n (vtSelE (vtPushSel.getD i default).2.2.1 (vtPushSel.getD i default).2.2.2.1)) ∧
      σv (.n (vtSelSum (vtPushSel.getD i default).2.2.1 (vtPushSel.getD i default).2.2.2.1
        (vtPushSel.getD i default).2.2.2.2.1)) =
        σv (.n (if i = 0 then 834 else vtSelSum (vtPushSel.getD (i - 1) default).2.2.1
          (vtPushSel.getD (i - 1) default).2.2.2.1 (vtPushSel.getD (i - 1) default).2.2.2.2.1)) +
        σv (.n (vtSelE (vtPushSel.getD i default).2.2.1 (vtPushSel.getD i default).2.2.2.1)) := by
    intro i hi
    obtain ⟨d1, d2, d3, d4, d5, d6⟩ := vt_pushSel_data i hi
    have hsz : (vtSizesP lm τ).getD (vtPushSel.getD i default).1 0 =
        τ (vtPushSel.getD i default).2.2.2.1 := by
      rw [d1, d2, ← vt_kapP lm τ (by omega)]
      obtain ⟨e1, e2, e3⟩ := vt_srcP i hi
      rw [vtKap, e1, e2, vt_tau_getD lm τ e3, Nat.add_zero]
    have hal := halP (vtPushSel.getD i default).1 (by rw [d1]; omega)
    rw [hsz] at hal
    obtain ⟨e0, e1, e2, e3⟩ := hblk (c := (vtPushSel.getD i default).1)
      (vtPushSel_check i (by rw [show vtPushSel.length = 51 from rfl]; exact hi))
      (by rw [d2]; exact d3) d6 (hrowP i hi).1 (hrowP i hi).2 hsz hal
      (hobP _ (by rw [d1]; omega)) (by rw [d1]; exact hoP _ (by omega))
      (by rw [d1]; exact hdigP i hi) (by rw [d1]; exact (hwP i hi).1)
      (by rw [d1]; exact (hwP i hi).2)
    rw [d1] at e1
    rw [d4] at e2
    refine ⟨e0, e1, e2, ?_⟩
    rw [e3, d5]
  -- the count blocks
  have hC : ∀ i < 45, (∀ s ∈ vtSelT (vtCountSel.getD i default).2.2.1 (vtCountSel.getD i default).1
        (vtCountSel.getD i default).2.2.2.1 (vtCountSel.getD i default).2.2.2.2.1
        (vtCountSel.getD i default).2.2.2.2.2.1 (vtCountSel.getD i default).2.2.2.2.2.2.1
        (vtCountSel.getD i default).2.2.2.2.2.2.2, VSH (coreProgram.Rel rd) rd σv s) ∧
      σv (.n (vtSelE (vtCountSel.getD i default).2.2.1 (vtCountSel.getD i default).2.2.2.1)) =
        blockSel (vtSizesC τ) point.length i point ∧
      σv (.n (vtCountPadData.getD i default).2.2.1) =
        σv (.n (vtSelE (vtCountSel.getD i default).2.2.1 (vtCountSel.getD i default).2.2.2.1)) ∧
      σv (.n (vtSelSum (vtCountSel.getD i default).2.2.1 (vtCountSel.getD i default).2.2.2.1
        (vtCountSel.getD i default).2.2.2.2.1)) =
        (if i = 0 then 0 else σv (.n (vtSelSum (vtCountSel.getD (i - 1) default).2.2.1
          (vtCountSel.getD (i - 1) default).2.2.2.1
          (vtCountSel.getD (i - 1) default).2.2.2.2.1))) +
        σv (.n (vtSelE (vtCountSel.getD i default).2.2.1 (vtCountSel.getD i default).2.2.2.1)) := by
    intro i hi
    obtain ⟨d1, d2, d3, d4, d5, d6⟩ := vt_countSel_data i hi
    have hsz : (vtSizesC τ).getD i 0 = τ (vtCountSel.getD i default).2.2.2.1 := by
      rw [d2, ← vt_kapC lm τ hi]
      obtain ⟨e1, e2, e3⟩ := vt_srcC i hi
      rw [vtKap, e1, e2, vt_tau_getD lm τ e3, Nat.add_zero]
    have hal := halC i hi
    rw [hsz] at hal
    obtain ⟨e0, e1, e2, e3⟩ := hblk (c := i)
      (vtCountSel_check i (by rw [show vtCountSel.length = 45 from rfl]; exact hi))
      (by rw [d2]; exact d3) d6 (hrowC i hi).1 (hrowC i hi).2 hsz hal (hobC i hi)
      (by rw [d1]; exact hoC i hi) (hdigC i hi) (hwC i hi).1 (hwC i hi).2
    rw [d4] at e2
    refine ⟨e0, e1, e2, ?_⟩
    rw [e3, d5]
    split_ifs <;> rfl
  -- the sums
  have hsumP := vt_running_sum (fun i ↦ σv (.n (vtSelSum (vtPushSel.getD i default).2.2.1
      (vtPushSel.getD i default).2.2.2.1 (vtPushSel.getD i default).2.2.2.2.1)))
    (fun i ↦ σv (.n (if i = 0 then 834 else vtSelSum (vtPushSel.getD (i - 1) default).2.2.1
      (vtPushSel.getD (i - 1) default).2.2.2.1 (vtPushSel.getD (i - 1) default).2.2.2.2.1)))
    (fun i ↦ σv (.n (vtPushPadData.getD i default).2.2.1)) (σv (.n 834)) 51
    (fun i hi ↦ by rw [(hP i hi).2.2.2, (hP i hi).2.2.1]) (by simp)
    (fun i h0 _ ↦ by simp [show i ≠ 0 by omega]) 50 (by norm_num)
  have hsumC := vt_running_sum (fun i ↦ σv (.n (vtSelSum (vtCountSel.getD i default).2.2.1
      (vtCountSel.getD i default).2.2.2.1 (vtCountSel.getD i default).2.2.2.2.1)))
    (fun i ↦ if i = 0 then 0 else σv (.n (vtSelSum (vtCountSel.getD (i - 1) default).2.2.1
      (vtCountSel.getD (i - 1) default).2.2.2.1 (vtCountSel.getD (i - 1) default).2.2.2.2.1)))
    (fun i ↦ σv (.n (vtCountPadData.getD i default).2.2.1)) 0 45
    (fun i hi ↦ by rw [(hC i hi).2.2.2, (hC i hi).2.2.1]) (by simp)
    (fun i h0 _ ↦ by simp [show i ≠ 0 by omega]) 44 (by norm_num)
  simp only [vt_pushSel_last] at hsumP
  simp only [vt_countSel_last] at hsumC
  refine ⟨a0, a1, a2, fun i hi ↦ (hP i hi).1, fun i hi ↦ (hC i hi).1, s0, s1, s2, c0, c1, c2,
    fun i hi ↦ (hP i hi).2.2.1.trans (hP i hi).2.1, ?_,
    fun i hi ↦ (hC i hi).2.2.1.trans (hC i hi).2.1, ?_⟩
  · rw [hsumP, u2, u1, vt_sum_map_range, vtPushPadData_length]
  · rw [hsumC, vt_sum_map_range, vtCountPadData_length, zero_add]

end

end
end LeanVM.Guest.B1.Tables
