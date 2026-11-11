/-
  LeanVM.Guest.B1.Tables.VtC.SSortAll

  `verify_tables`' statements `0 ..< 563` hold on the honest valuation: the capacity and claims
  copied, `kappa_base` read, the groups' keys and sizes stored, both sides' ranks certified, every
  push and count block's offset its side's `stackOffsets` offset.
-/

module

public import LeanVM.Guest.B1.Tables.VtC.SSort

/-!
# The block certification's statements, honestly (G:2244-2302)

`vtS_sort`: on a memory holding `dims_g`'s `g^log_mem` and heights, the exponent tables at
`g_squares` and the four group buffers' honest words (`vtGKeyW`, `vtGSizeW`, `vtGBaseW`, `vtGOrdW`),
defined below `2^14`, statements `0 ..< 563` hold; the copies and `kappa_base` are the arguments'
and `dims_g`'s, the group buffers the allocator's, and the blocks' offsets `g^stackOffsets`
(`vtc_side_offsets`: the soundness's side argument, from the ranks' facts).
-/

namespace LeanVM.Guest.B1.Tables

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Protocol LeanVM.Protocol.Verifier
open LeanVM.Guest.B1.Fwd
open Finset (range)

@[expose] public section

/-- **Consecutive slices hold**, so does the run they tile. -/
theorem forall_slices {P : Stmt → Prop} (A L : ℕ → ℕ) :
    ∀ n, (∀ k < n, k + 1 < n → A (k + 1) = A k + L k) →
      (∀ k < n, ∀ s ∈ (vtPre.drop (A k)).take (L k), P s) →
      ∀ s ∈ (vtPre.drop (A 0)).take (∑ k ∈ range n, L k), P s
  | 0, _, _ => by simp
  | n + 1, hA, h => by
    have hpos : ∀ k ≤ n, A k = A 0 + ∑ j ∈ range k, L j := by
      intro k hk
      induction k with
      | zero => simp
      | succ k ih =>
        rw [hA k (by omega) (by omega), ih (by omega), Finset.sum_range_succ, Nat.add_assoc]
    rw [Finset.sum_range_succ]
    refine forall_slice_join (forall_slices A L n (fun k _ hk ↦ hA k (by omega) (by omega))
      (fun k hk ↦ h k (by omega))) ?_
    rw [← hpos n le_rfl]
    exact h n (by omega)

/-- **A side's block offsets**, the soundness's `side` with the groups' facts as hypotheses: from
its ranks' facts, the groups' keys and sizes, the bases and steps, every block's offset is
`stackOffsets`'s. -/
theorem vtc_side_offsets {rd : Reader} {σ : Val} {lm : ℕ} {τ : ℕ → ℕ}
    (hκ34 : ∀ k < 15, vtKap lm τ (vtB0 k) < 34)
    (hG : ∀ k < 15, (∃ key, LoadHolds rd (σ (.n 33)) (vtGi k) key ∧
      key * gen ^ vtB0 k = gen ^ (vtKap lm τ (vtB0 k) * 247)) ∧
      LoadHolds rd (σ (.n 34)) (vtGi k) (gen ^ (vtLen k * 2 ^ vtKap lm τ (vtB0 k))))
    (hB : ∀ k < 15, LoadHolds rd (σ (.n 35)) (vtGi k)
        (σ (.n (vtBoffData.getD k default).2.2.2)) ∧
      σ (.n ((vtBoffData.getD k default).2.2.2 - 1)) = gen ^ 2 ^ vtKap lm τ (vtB0 k) ∧
      ∀ i < vtLen k - 1, σ (.n ((vtBoffData.getD k default).2.2.2 + 1 + i)) =
        σ (.n ((vtBoffData.getD k default).2.2.2 + i)) *
          σ (.n ((vtBoffData.getD k default).2.2.2 - 1)))
    (hsideT : ∀ e < 24, LoadHolds rd (σ (.n 12)) (212 + e) (word (vtGroupSide e) 0)) :
    ∀ (base G0 kOff m n v0 s : ℕ), base + n ≤ 153 → s < 3 →
    (∀ r < m, VtRankFacts rd σ v0 s r) →
    (∀ e < 24, vtGroupSide e = s → G0 ≤ e ∧ e < G0 + m) →
    (∀ j < m, kOff + j < 15 ∧ vtGi (kOff + j) = G0 + j ∧
      vtB0 (kOff + j) = base + (blockGroupStart.getD (G0 + j) 0 - base) ∧
      vtLen (kOff + j) = (blockGroupStart.getD (G0 + (j + 1)) 0 - base) -
        (blockGroupStart.getD (G0 + j) 0 - base) ∧
      blockGroupStart.getD (G0 + j) 0 - base < blockGroupStart.getD (G0 + (j + 1)) 0 - base ∧
      blockGroupStart.getD (G0 + (j + 1)) 0 - base ≤ n ∧
      vtBoffV (base + (blockGroupStart.getD (G0 + j) 0 - base)) =
        (vtBoffData.getD (kOff + j) default).2.2.2) →
    (∀ x < n, vtBk (base + x) - kOff < m ∧
      blockGroupStart.getD (G0 + (vtBk (base + x) - kOff)) 0 - base ≤ x ∧
      x < blockGroupStart.getD (G0 + (vtBk (base + x) - kOff + 1)) 0 - base ∧
      blockKappaSrc.getD (base + x) 0 = blockKappaSrc.getD (vtB0 (vtBk (base + x))) 0 ∧
      blockKappaAdj (base + x) = blockKappaAdj (vtB0 (vtBk (base + x))) ∧
      kOff + (vtBk (base + x) - kOff) = vtBk (base + x) ∧
      (blockGroupStart.getD (G0 + (vtBk (base + x) - kOff)) 0 - base < x →
        vtBoffV (base + x) = (vtBoffData.getD (vtBk (base + x)) default).2.2.2 + 1 +
          (x - 1 - (blockGroupStart.getD (G0 + (vtBk (base + x) - kOff)) 0 - base)) ∧
        vtBoffV (base + (x - 1)) = (vtBoffData.getD (vtBk (base + x)) default).2.2.2 +
          (x - 1 - (blockGroupStart.getD (G0 + (vtBk (base + x) - kOff)) 0 - base)) ∧
        x - 1 - (blockGroupStart.getD (G0 + (vtBk (base + x) - kOff)) 0 - base) <
          vtLen (vtBk (base + x)) - 1)) →
    (∀ j < m, ∀ x < n, blockGroupStart.getD (G0 + j) 0 - base ≤ x →
      x < blockGroupStart.getD (G0 + (j + 1)) 0 - base → vtBk (base + x) - kOff = j) →
    ∀ x < n, σ (.n (vtBoffV (base + x))) =
      gen ^ (stackOffsets ((List.range n).map fun c ↦ vtKap lm τ (base + c))).1.getD x 0 := by
  intro base G0 kOff m n v0 s hn hs hfacts hsideS D1 D2 D3
  have hκs : ∀ x < n, ((List.range n).map fun c ↦ vtKap lm τ (base + c)).getD x 0 =
      vtKap lm τ (base + x) := fun x hx => by
    rw [List.getD_eq_getElem _ _ (by simp; exact hx)]; simp
  refine vt_side_cert (G0 := G0) (base := base) _ (by simp)
    (fun j ↦ blockGroupStart.getD (G0 + j) 0 - base)
    (fun j ↦ vtKap lm τ (base + (blockGroupStart.getD (G0 + j) 0 - base)))
    (fun x ↦ vtBk (base + x) - kOff) (fun x ↦ vtBoffV (base + x)) hn hfacts hsideT hsideS hs
    (fun j hj ↦ ?_) (fun j hj ↦ ?_) (fun j hj ↦ ?_) (fun j hj ↦ (D1 j hj).2.2.2.2.1)
    (fun x hx ↦ ⟨(D2 x hx).1, (D2 x hx).2.1, (D2 x hx).2.2.1⟩)
    (fun j hj x h1 h2 ↦ ⟨by have := (D1 j hj).2.2.2.2.2.1; omega, D3 j hj x
      (by have := (D1 j hj).2.2.2.2.2.1; omega) h1 h2⟩)
    (fun x hx ↦ ?_) (fun j hj ↦ ?_) (fun x hx hlt ↦ ?_)
  · obtain ⟨hk, hgi, hb0, -⟩ := D1 j hj
    obtain ⟨⟨key, h1, h2⟩, -⟩ := hG _ hk
    exact ⟨key, by rw [← hgi]; exact h1, by rw [← hb0, h2]⟩
  · obtain ⟨hk, hgi, hb0, hl, -⟩ := D1 j hj
    have := (hG _ hk).2
    rwa [hgi, hl, hb0] at this
  · obtain ⟨hk, -, hb0, -⟩ := D1 j hj
    rw [← hb0]; exact hκ34 _ hk
  · obtain ⟨-, -, -, hsrc', hadj', hkk, -⟩ := D2 x hx
    have hj := (D2 x hx).1
    obtain ⟨-, -, hb0, -⟩ := D1 _ hj
    rw [hκs x hx, ← hb0, hkk, vtKap, vtKap, hsrc', hadj']
  · obtain ⟨hk, hgi, -, -, -, -, hbv⟩ := D1 j hj
    have := (hB _ hk).1
    rw [hgi, ← hbv] at this
    exact this
  · obtain ⟨-, -, -, -, -, hkk, hstep⟩ := D2 x hx
    have hj := (D2 x hx).1
    obtain ⟨hk, -, hb0, -⟩ := D1 _ hj
    obtain ⟨e1, e2, e3⟩ := hstep hlt
    obtain ⟨-, hst, hch⟩ := hB _ hk
    rw [hkk] at hst hch hb0
    rw [e1, e2, hch _ e3, hst, hb0]

theorem gpow_inv_step {A a B b d : ℕ} (h : A + b = d + 1 + B + a) :
    gen ^ A * (gen ^ a)⁻¹ = gen ^ (d + 1) * (gen ^ B * (gen ^ b)⁻¹) := by
  have e : gen ^ A * gen ^ b = gen ^ (d + 1) * gen ^ B * gen ^ a := by
    rw [← pow_add, h, pow_add, pow_add]
  have ha := gen_pow_ne_zero a
  have hb := gen_pow_ne_zero b
  field_simp
  linear_combination e

section
variable {rd : Reader} {w : ℕ → E} {args : List E}

local notation "σv" => vtσ rd w args

theorem vt_kbList_getD {lm : ℕ} {τ : ℕ → ℕ} {i : ℕ} (hi : i < 7) :
    (gen ^ lm :: (vtTauList τ).map (gen ^ ·)).getD i 0 = gen ^ ([lm] ++ vtTauList τ).getD i 0 := by
  rcases i with _ | i
  · rfl
  · simp only [List.getD_cons_succ, List.singleton_append, vtTauList]
    rw [List.getD_eq_getElem _ _ (by simp; omega), List.getD_eq_getElem _ _ (by simp; omega)]
    simp

set_option maxRecDepth 100000 in
/-- **`verify_tables`' statements `0 ..< 563`, honestly.** -/
theorem vtS_sort (hl : args.length = 20) (hlow : LowDefB 14 rd) {lm : ℕ} {τ : ℕ → ℕ}
    (hlm : lm ≤ 32) (hτ : ∀ t < 6, τ t < 29)
    (hdims : TbReadsAt rd (σv (.n 10)) (gen ^ lm :: (vtTauList τ).map (gen ^ ·)))
    (hE : ExpTablesAt rd (σv (.n 12)))
    (hkeyW : TbReadsAt rd (w 33) (vtGKeyW lm τ)) (hszW : TbReadsAt rd (w 34) (vtGSizeW lm τ))
    (hbaseW : TbReadsAt rd (w 35) (vtGBaseW lm τ)) (hordW : TbReadsAt rd (w 36) (vtGOrdW lm τ)) :
    (∀ s ∈ (vtPre.drop 0).take 563, VSH (coreProgram.Rel rd) rd σv s) ∧
      (∀ i < 5, σv (.n (20 + i)) = σv (.n i)) ∧
      (∀ i < 8, σv (.n (25 + i)) = gen ^ ([0, lm] ++ vtTauList τ).getD i 0) ∧
      (∀ i < 4, σv (.n (33 + i)) = w (33 + i)) ∧
      (∀ x < 54, σv (.n (vtBoffV x)) =
        gen ^ (stackOffsets ((List.range 54).map (vtKap lm τ))).1.getD x 0) ∧
      (∀ x < 45, σv (.n (vtBoffV (108 + x))) =
        gen ^ (stackOffsets ((List.range 45).map fun c ↦ vtKap lm τ (108 + c))).1.getD x 0) := by
  obtain ⟨hsq, hrk, hsd, -⟩ := hE
  -- the prologue
  have hgd : ∀ (n : ℕ) (s : Stmt), tbStmtsEqb [s] ((vtAt n).take 1) = true →
      GoodS rd vtSL w σv (fixNe s) := fun n s h ↦ vt_goodAt hl n s h
  have hcp : ∀ i < 5, σv (.n (20 + i)) = σv (.n i) := by
    intro i hi
    interval_cases i
    · exact vt_copyAt hl 0 (by decide +kernel)
    · exact vt_copyAt hl 1 (by decide +kernel)
    · exact vt_copyAt hl 2 (by decide +kernel)
    · exact vt_copyAt hl 3 (by decide +kernel)
    · exact vt_copyAt hl 4 (by decide +kernel)
  have hal : ∀ i < 4, σv (.n (33 + i)) = w (33 + i) := by
    intro i hi
    interval_cases i
    · exact vt_allocAt hl 13 (k := 24) (by decide +kernel)
    · exact vt_allocAt hl 14 (k := 24) (by decide +kernel)
    · exact vt_allocAt hl 15 (k := 24) (by decide +kernel)
    · exact vt_allocAt hl 16 (k := 24) (by decide +kernel)
  -- `kappa_base`
  have hdimsL : ∀ i < 7, LoadHolds rd (σv (.n 10)) i (gen ^ ([lm] ++ vtTauList τ).getD i 0) := by
    intro i hi
    have := hdims i (by simp [vtTauList]; omega)
    rwa [← List.getD_eq_getElem _ 0, vt_kbList_getD hi] at this
  have hkbR : ∀ i < 7, σv (.n (26 + i)) = gen ^ ([lm] ++ vtTauList τ).getD i 0 ∧
      VSH (coreProgram.Rel rd) rd σv (.atom (.load (.n (26 + i)) (.n 10) i)) := by
    intro i hi
    interval_cases i
    · exact vt_readAt hl 6 (by decide +kernel) (by decide +kernel) (hdimsL 0 (by norm_num))
    · exact vt_readAt hl 7 (by decide +kernel) (by decide +kernel) (hdimsL 1 (by norm_num))
    · exact vt_readAt hl 8 (by decide +kernel) (by decide +kernel) (hdimsL 2 (by norm_num))
    · exact vt_readAt hl 9 (by decide +kernel) (by decide +kernel) (hdimsL 3 (by norm_num))
    · exact vt_readAt hl 10 (by decide +kernel) (by decide +kernel) (hdimsL 4 (by norm_num))
    · exact vt_readAt hl 11 (by decide +kernel) (by decide +kernel) (hdimsL 5 (by norm_num))
    · exact vt_readAt hl 12 (by decide +kernel) (by decide +kernel) (hdimsL 6 (by norm_num))
  have hkb : ∀ i < 8, σv (.n (25 + i)) = gen ^ ([0, lm] ++ vtTauList τ).getD i 0 := by
    intro i hi
    rcases i with _ | i
    · rw [vt_constAt hl 5 (e := word 1 0) (by decide +kernel), tb_word_one]; simp
    · have := (hkbR i (by omega)).1
      rw [show 25 + (i + 1) = 26 + i by omega, this]
      rfl
  have hpro : ∀ s ∈ (vtPre.drop 0).take 18, VSH (coreProgram.Rel rd) rd σv s := by
    refine vt_blockR hl 0 18 [.atom (.load (.n 26) (.n 10) 0), .atom (.load (.n 27) (.n 10) 1),
      .atom (.load (.n 28) (.n 10) 2), .atom (.load (.n 29) (.n 10) 3),
      .atom (.load (.n 30) (.n 10) 4), .atom (.load (.n 31) (.n 10) 5),
      .atom (.load (.n 32) (.n 10) 6)] (by decide +kernel) ?_
    intro s hs _
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [(hkbR 0 (by norm_num)).2, (hkbR 1 (by norm_num)).2, (hkbR 2 (by norm_num)).2,
      (hkbR 3 (by norm_num)).2, (hkbR 4 (by norm_num)).2, (hkbR 5 (by norm_num)).2,
      (hkbR 6 (by norm_num)).2]
  -- the groups
  have hsrc : ∀ k < 15, blockKappaSrc.getD (vtB0 k) 0 < 8 := by decide +kernel
  have hkx : ∀ k < 15, σv (.n (vtKv k)) * gen ^ vtAdj k = gen ^ vtKap lm τ (vtB0 k) := by
    intro k hk
    rw [vtKv, hkb _ (hsrc k hk), ← pow_add, vtKap, vtAdj]
  have hb153 : ∀ k < 15, vtB0 k < 153 := by decide +kernel
  have hκ34 : ∀ k < 15, vtKap lm τ (vtB0 k) < 34 := fun k hk ↦ vt_kap_lt lm τ hlm hτ (hb153 k hk)
  have hrkK : ∀ κ < 34, LoadHolds rd (σv (.n 12) * gen ^ κ) 178 (gen ^ (κ * 247)) := by
    intro κ hκ
    have r1 := hrk κ (by simp [rankKeysList]; exact hκ)
    rw [tb_loadHolds_mul_gen_pow] at r1 ⊢
    rw [Nat.add_comm]
    simpa [rankKeysList] using r1
  have hsqK : ∀ κ < 34, LoadHolds rd (σv (.n 12) * gen ^ κ) 0 (gen ^ 2 ^ κ) := by
    intro κ hκ
    have s1 := hsq κ (by simp [gSquaresList]; exact hκ)
    rw [tb_loadHolds_mul_gen_pow, Nat.add_zero]
    simpa [gSquaresList] using s1
  have e36 : σv (.n 33) = w 33 := hal 0 (by norm_num)
  have e37 : σv (.n 34) = w 34 := hal 1 (by norm_num)
  have e38 : σv (.n 35) = w 35 := hal 2 (by norm_num)
  have e39 : σv (.n 36) = w 36 := hal 3 (by norm_num)
  rw [← e36] at hkeyW
  rw [← e37] at hszW
  rw [← e38] at hbaseW
  rw [← e39] at hordW
  have hgi24 : ∀ k < 15, vtGi k < 24 := by decide +kernel
  have hkeyG : ∀ k < 15, LoadHolds rd (σv (.n 33)) (vtGi k)
      (gen ^ (vtKap lm τ (vtB0 k) * 247) * (gen ^ vtB0 k)⁻¹) := by
    intro k hk
    have := hkeyW (vtGi k) (by simp [vtGKeyW]; exact hgi24 k hk)
    simp only [vtGKeyW, List.getElem_map, List.getElem_range] at this
    exact this
  have hszG : ∀ k < 15, LoadHolds rd (σv (.n 34)) (vtGi k)
      (gen ^ (vtLen k * 2 ^ vtKap lm τ (vtB0 k))) := by
    intro k hk
    have := hszW (vtGi k) (by simp [vtGSizeW]; exact hgi24 k hk)
    simp only [vtGSizeW, List.getElem_map, List.getElem_range] at this
    exact this
  have hgrp : ∀ k < 15, ∀ s ∈ (vtPre.drop (vtGrpA k)).take (vtGrpL k),
      VSH (coreProgram.Rel rd) rd σv s := fun k hk ↦
    vtc_grps hl hk (hkx k hk) (hrkK _ (hκ34 k hk)) (hsqK _ (hκ34 k hk)) (hkeyG k hk) (hszG k hk)
  have hgP : ∀ s ∈ (vtPre.drop 18).take 92, VSH (coreProgram.Rel rd) rd σv s := by
    have := forall_slices vtGrpA vtGrpL 9 (by decide) (fun k hk ↦ hgrp k (by omega))
    rwa [show vtGrpA 0 = 18 from rfl, show ∑ k ∈ range 9, vtGrpL k = 92 by decide] at this
  have hgC : ∀ s ∈ (vtPre.drop 339).take 64, VSH (coreProgram.Rel rd) rd σv s := by
    have := forall_slices (fun k ↦ vtGrpA (9 + k)) (fun k ↦ vtGrpL (9 + k)) 6 (by decide)
      (fun k hk ↦ hgrp (9 + k) (by omega))
    rwa [show vtGrpA (9 + 0) = 339 from rfl,
      show ∑ k ∈ range 6, vtGrpL (9 + k) = 64 by decide] at this
  -- the exponent tables' sides
  have hsideT : ∀ e < 24, LoadHolds rd (σv (.n 12)) (212 + e) (word (vtGroupSide e) 0) := by
    intro e he
    have := hsd e (by simp [sideTabList]; exact he)
    rw [tb_loadHolds_mul_gen_pow] at this
    rw [← vt_sideTab_getD e he, List.getD_eq_getElem _ _ (by simp [sideTabList]; exact he)]
    exact this
  -- one side's ranks
  have hside : ∀ s0 ∈ [0, 2], ∀ r < vtGm s0,
      LoadHolds rd (σv (.n 12) * gen ^ (vtG0 s0 + vtPi lm τ s0 r)) 212 (word s0 0) := by
    intro s0 hs0 r hr
    have hp := vtPi_lt (lm := lm) (τ := τ) hr
    rw [tb_loadHolds_mul_gen_pow, Nat.add_comm]
    have := hsideT (vtG0 s0 + vtPi lm τ s0 r) (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hs0
      rcases hs0 with rfl | rfl <;> simp [vtG0, vtGm] at hp ⊢ <;> omega)
    convert this using 2
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs0
    rcases hs0 with rfl | rfl <;> simp [vtG0, vtGm, vtGroupSide] at hp ⊢ <;> omega
  have hkeyR : ∀ s0 ∈ [0, 2], ∀ r < vtGm s0, LoadHolds rd
      (σv (.n 33) * gen ^ (vtG0 s0 + vtPi lm τ s0 r)) 0
      (gen ^ (vtKg lm τ (vtG0 s0 + vtPi lm τ s0 r) * 247) *
        (gen ^ blockGroupStart.getD (vtG0 s0 + vtPi lm τ s0 r) 0)⁻¹) := by
    intro s0 hs0 r hr
    have hp := vtPi_lt (lm := lm) (τ := τ) hr
    have hlt : vtG0 s0 + vtPi lm τ s0 r < 24 := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hs0
      rcases hs0 with rfl | rfl <;> simp [vtG0, vtGm] at hp ⊢ <;> omega
    rw [tb_loadHolds_mul_gen_pow, Nat.add_zero]
    have := hkeyW _ (by simp [vtGKeyW]; exact hlt)
    simp only [vtGKeyW, List.getElem_map, List.getElem_range] at this
    exact this
  have hszR : ∀ s0 ∈ [0, 2], ∀ r < vtGm s0, LoadHolds rd
      (σv (.n 34) * gen ^ (vtG0 s0 + vtPi lm τ s0 r)) 0
      (gen ^ vtGsz lm τ (vtG0 s0 + vtPi lm τ s0 r)) := by
    intro s0 hs0 r hr
    have hp := vtPi_lt (lm := lm) (τ := τ) hr
    have hlt : vtG0 s0 + vtPi lm τ s0 r < 24 := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hs0
      rcases hs0 with rfl | rfl <;> simp [vtG0, vtGm] at hp ⊢ <;> omega
    rw [tb_loadHolds_mul_gen_pow, Nat.add_zero]
    have := hszW _ (by simp [vtGSizeW]; exact hlt)
    simp only [vtGSizeW, List.getElem_map, List.getElem_range] at this
    exact this
  have hbaseR : ∀ s0 ∈ [0, 2], ∀ r < vtGm s0, LoadHolds rd
      (σv (.n 35) * gen ^ (vtG0 s0 + vtPi lm τ s0 r)) 0
      (gen ^ ∑ r' ∈ range r, vtGsz lm τ (vtG0 s0 + vtPi lm τ s0 r')) := by
    intro s0 hs0 r hr
    have hp := vtPi_lt (lm := lm) (τ := τ) hr
    have hrho := vtRho_pi (lm := lm) (τ := τ) hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs0
    rw [tb_loadHolds_mul_gen_pow, Nat.add_zero]
    rcases hs0 with rfl | rfl
    · have hlt : vtPi lm τ 0 r < 9 := by simpa [vtGm] using hp
      have := hbaseW (vtG0 0 + vtPi lm τ 0 r) (by simp [vtGBaseW, vtG0]; omega)
      simp only [vtGBaseW, List.getElem_map, List.getElem_range, vtG0, ↓reduceIte, Nat.zero_add,
        hlt] at this
      simp only [vtG0, ↓reduceIte, Nat.zero_add] at hrho ⊢
      rw [hrho, vtGP] at this
      simpa only [vtG0, ↓reduceIte, Nat.zero_add] using this
    · have hlt : vtPi lm τ 2 r < 6 := by simpa [vtGm] using hp
      have := hbaseW (vtG0 2 + vtPi lm τ 2 r) (by simp [vtGBaseW, vtG0]; omega)
      simp only [vtGBaseW, List.getElem_map, List.getElem_range, vtG0,
        show (2 : ℕ) ≠ 0 by norm_num, ↓reduceIte, show ¬ (18 + vtPi lm τ 2 r < 9) by omega,
        show ¬ (18 + vtPi lm τ 2 r < 18) by omega, Nat.add_sub_cancel_left] at this
      simp only [vtG0, show (2 : ℕ) ≠ 0 by norm_num, ↓reduceIte] at hrho ⊢
      rw [hrho, vtGP] at this
      simpa only [vtG0, show (2 : ℕ) ≠ 0 by norm_num, ↓reduceIte] using this
  have hstepR : ∀ s0 ∈ [0, 2], ∀ r, r + 1 < vtGm s0 → ∃ d ≤ 8397,
      gen ^ (vtKg lm τ (vtG0 s0 + vtPi lm τ s0 r) * 247) *
        (gen ^ blockGroupStart.getD (vtG0 s0 + vtPi lm τ s0 r) 0)⁻¹ =
      gen ^ (d + 1) * (gen ^ (vtKg lm τ (vtG0 s0 + vtPi lm τ s0 (r + 1)) * 247) *
        (gen ^ blockGroupStart.getD (vtG0 s0 + vtPi lm τ s0 (r + 1)) 0)⁻¹) := by
    intro s0 hs0 r hr
    have hp1 := vtPi_lt (lm := lm) (τ := τ) (s := s0) (r := r) (by omega)
    have hp2 := vtPi_lt (lm := lm) (τ := τ) (s := s0) hr
    obtain ⟨hle, htie⟩ := vtPi_adj (lm := lm) (τ := τ) (s := s0) hr
    have hmono : ∀ s1 ∈ [0, 2], ∀ i < vtGm s1, ∀ j < vtGm s1, i < j →
        blockGroupStart.getD (vtG0 s1 + i) 0 < blockGroupStart.getD (vtG0 s1 + j) 0 := by
      decide +kernel
    have hbg : ∀ s1 ∈ [0, 2], ∀ i < vtGm s1, blockGroupStart.getD (vtG0 s1 + i) 0 < 153 := by
      decide +kernel
    have hkg : ∀ i < 24, vtKg lm τ i < 34 := by
      intro i hi
      exact vt_kap_lt lm τ hlm hτ (by
        have : ∀ i < 24, blockGroupStart.getD i 0 < 153 := by decide +kernel
        exact this i hi)
    have hlt1 : vtG0 s0 + vtPi lm τ s0 r < 24 := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hs0
      rcases hs0 with rfl | rfl <;> simp [vtG0, vtGm] at hp1 ⊢ <;> omega
    have hk1 := hkg _ hlt1
    have hb1 := hbg s0 hs0 _ hp1
    have hb2 := hbg s0 hs0 _ hp2
    have hcase : blockGroupStart.getD (vtG0 s0 + vtPi lm τ s0 r) 0 <
          blockGroupStart.getD (vtG0 s0 + vtPi lm τ s0 (r + 1)) 0 ∨
        vtKg lm τ (vtG0 s0 + vtPi lm τ s0 (r + 1)) < vtKg lm τ (vtG0 s0 + vtPi lm τ s0 r) := by
      rcases Nat.lt_or_ge (vtKg lm τ (vtG0 s0 + vtPi lm τ s0 (r + 1)))
        (vtKg lm τ (vtG0 s0 + vtPi lm τ s0 r)) with h | h
      · exact Or.inr h
      · exact Or.inl (hmono s0 hs0 _ hp1 _ hp2 (htie (by omega)))
    generalize vtKg lm τ (vtG0 s0 + vtPi lm τ s0 r) = A at *
    generalize vtKg lm τ (vtG0 s0 + vtPi lm τ s0 (r + 1)) = B at *
    generalize blockGroupStart.getD (vtG0 s0 + vtPi lm τ s0 r) 0 = a at *
    generalize blockGroupStart.getD (vtG0 s0 + vtPi lm τ s0 (r + 1)) 0 = b at *
    refine ⟨A * 247 + b - (B * 247 + a) - 1, ?_, gpow_inv_step ?_⟩
    · rcases hcase with h | h
      · omega
      · have : (B + 1) * 247 ≤ A * 247 := Nat.mul_le_mul_right _ h
        omega
    · rcases hcase with h | h
      · omega
      · have : (B + 1) * 247 ≤ A * 247 := Nat.mul_le_mul_right _ h
        omega
  have hk0 : ∀ gi : ℕ, gen ^ (vtKg lm τ gi * 247) * (gen ^ blockGroupStart.getD gi 0)⁻¹ ≠ 0 :=
    fun gi ↦ mul_ne_zero (gen_pow_ne_zero _) (inv_ne_zero (gen_pow_ne_zero _))
  have hordP : ∀ r < 9, LoadHolds rd (σv (.n 36)) (0 + r) (gen ^ (vtG0 0 + vtPi lm τ 0 r)) := by
    intro r hr
    have := hordW r (by simp [vtGOrdW]; omega)
    simp only [vtGOrdW, List.getElem_map, List.getElem_range, hr, ↓reduceIte] at this
    simpa [vtG0] using this
  have hordC : ∀ r < 6, LoadHolds rd (σv (.n 36)) (18 + r) (gen ^ (vtG0 2 + vtPi lm τ 2 r)) := by
    intro r hr
    have := hordW (18 + r) (by simp [vtGOrdW]; omega)
    simp only [vtGOrdW, List.getElem_map, List.getElem_range,
      show ¬ (18 + r < 9) by omega, show ¬ (18 + r < 18) by omega, ↓reduceIte,
      Nat.add_sub_cancel_left] at this
    simpa [vtG0] using this
  have hgiR : ∀ s0 ∈ [0, 2], ∀ r < vtGm s0, vtG0 s0 + vtPi lm τ s0 r ≤ 23 := by
    intro s0 hs0 r hr
    have hp := vtPi_lt (lm := lm) (τ := τ) hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs0
    rcases hs0 with rfl | rfl <;> simp [vtG0, vtGm] at hp ⊢ <;> omega
  have m0 : (0 : ℕ) ∈ [0, 2] := by simp
  have m2 : (2 : ℕ) ∈ [0, 2] := by simp
  obtain ⟨rP, fP⟩ := side_ok (m := 9) hl hlow (by norm_num) (by norm_num) vtPush0_check
    vtPush_check (by decide +kernel) (by decide +kernel)
    (fun r ↦ vtG0 0 + vtPi lm τ 0 r)
    (fun r ↦ gen ^ (vtKg lm τ (vtG0 0 + vtPi lm τ 0 r) * 247) *
      (gen ^ blockGroupStart.getD (vtG0 0 + vtPi lm τ 0 r) 0)⁻¹)
    (fun r ↦ vtGsz lm τ (vtG0 0 + vtPi lm τ 0 r)) hordP (hgiR 0 m0) (hside 0 m0) (hkeyR 0 m0)
    (hszR 0 m0) (hbaseR 0 m0) (hstepR 0 m0) (fun _ _ ↦ hk0 _)
  obtain ⟨rC, fC⟩ := side_ok (m := 6) hl hlow (by norm_num) (by norm_num) vtCount0_check
    vtCount_check (by decide +kernel) (by decide +kernel)
    (fun r ↦ vtG0 2 + vtPi lm τ 2 r)
    (fun r ↦ gen ^ (vtKg lm τ (vtG0 2 + vtPi lm τ 2 r) * 247) *
      (gen ^ blockGroupStart.getD (vtG0 2 + vtPi lm τ 2 r) 0)⁻¹)
    (fun r ↦ vtGsz lm τ (vtG0 2 + vtPi lm τ 2 r)) hordC (hgiR 2 m2) (hside 2 m2) (hkeyR 2 m2)
    (hszR 2 m2) (hbaseR 2 m2) (hstepR 2 m2) (fun _ _ ↦ hk0 _)
  -- the groups' block offsets
  have hsS : ∀ k < 15, Atom.load (.n ((vtBoffData.getD k default).2.2.2 - 1))
      (.n ((vtBoffData.getD k default).2.2.2 - 2)) (vtBoffData.getD k default).2.2.1 ∉ vtSL ∧
      Atom.load (.n (vtBoffData.getD k default).2.2.2) (.n 35) (vtGi k) ∉ vtSL ∧
      (vtBoffData.getD k default).2.1 + 2 < (vtBoffData.getD k default).2.2.2 ∧
      14 < (vtBoffData.getD k default).2.2.2 := by decide +kernel
  have hbo : ∀ k < 15, (∀ st ∈ vtBoffT (vtBoffData.getD k default).2.1
        (vtBoffData.getD k default).2.2.1 (vtGi k) (vtBoffData.getD k default).2.2.2 (vtLen k),
        VSH (coreProgram.Rel rd) rd σv st) ∧
      LoadHolds rd (σv (.n 35)) (vtGi k) (σv (.n (vtBoffData.getD k default).2.2.2)) ∧
      σv (.n ((vtBoffData.getD k default).2.2.2 - 1)) = gen ^ 2 ^ vtKap lm τ (vtB0 k) ∧
      ∀ i < vtLen k - 1, σv (.n ((vtBoffData.getD k default).2.2.2 + 1 + i)) =
        σv (.n ((vtBoffData.getD k default).2.2.2 + i)) *
          σv (.n ((vtBoffData.getD k default).2.2.2 - 1)) := by
    intro k hk
    obtain ⟨hkv, hoff, -⟩ := vtBoffData_kv k hk
    obtain ⟨s1, s2, h1, h2⟩ := hsS k hk
    have hg := vt_goodL (rd := rd) (w := w) hl _ _ (vtPre_drop _ ▸ vtBoff_check k hk)
    have hst : LoadHolds rd (σv (.n 12) * σv (.n (vtBoffData.getD k default).2.1))
        (vtBoffData.getD k default).2.2.1 (gen ^ 2 ^ vtKap lm τ (vtB0 k)) := by
      rw [hkv, hoff, vtKv, hkb _ (hsrc k hk), tb_loadHolds_mul_gen_pow]
      have := hsq _ (by simp [gSquaresList]; exact hκ34 k hk)
      simpa [gSquaresList, vtKap, vtAdj] using this
    have hb := hbaseW (vtGi k) (by simp [vtGBaseW]; exact hgi24 k hk)
    obtain ⟨hall, e1, e2, hch⟩ := boff_ok (C := coreProgram.Rel rd) h1 h2 hg s1 s2 hst hb
    refine ⟨hall, by rw [e2]; exact hb, e1, fun i hi ↦ by rw [hch i hi, e1]⟩
  have hboS : ∀ k < 15, ∀ s ∈ (vtPre.drop (vtBoffData.getD k default).1).take (vtLen k + 2),
      VSH (coreProgram.Rel rd) rd σv s := by
    intro k hk s hs
    have e := tbStmtsEqb_sound (vtPre_drop _ ▸ vtBoff_check k hk)
    have hlen : (vtBoffT (vtBoffData.getD k default).2.1 (vtBoffData.getD k default).2.2.1
        (vtGi k) (vtBoffData.getD k default).2.2.2 (vtLen k)).length = vtLen k + 2 := by
      have : 1 ≤ vtLen k := by
        have : ∀ k < 15, 1 ≤ vtLen k := by decide +kernel
        exact this k hk
      simp [vtBoffT]; omega
    rw [hlen] at e
    exact (hbo k hk).1 s (by rw [e]; exact hs)
  have hbP : ∀ s ∈ (vtPre.drop 267).take 72, VSH (coreProgram.Rel rd) rd σv s := by
    have := forall_slices (fun k ↦ (vtBoffData.getD k default).1) (fun k ↦ vtLen k + 2) 9
      (by decide +kernel) (fun k hk ↦ hboS k (by omega))
    rwa [show (vtBoffData.getD 0 default).1 = 267 from rfl,
      show ∑ k ∈ range 9, (vtLen k + 2) = 72 by decide +kernel] at this
  have hbC : ∀ s ∈ (vtPre.drop 506).take 57, VSH (coreProgram.Rel rd) rd σv s := by
    have := forall_slices (fun k ↦ (vtBoffData.getD (9 + k) default).1) (fun k ↦ vtLen (9 + k) + 2) 6
      (by decide +kernel) (fun k hk ↦ hboS (9 + k) (by omega))
    rwa [show (vtBoffData.getD (9 + 0) default).1 = 506 from rfl,
      show ∑ k ∈ range 6, (vtLen (9 + k) + 2) = 57 by decide +kernel] at this
  -- the offsets
  have hG : ∀ k < 15, (∃ key, LoadHolds rd (σv (.n 33)) (vtGi k) key ∧
      key * gen ^ vtB0 k = gen ^ (vtKap lm τ (vtB0 k) * 247)) ∧
      LoadHolds rd (σv (.n 34)) (vtGi k) (gen ^ (vtLen k * 2 ^ vtKap lm τ (vtB0 k))) := fun k hk ↦
    ⟨⟨_, hkeyG k hk, by rw [mul_assoc, inv_mul_cancel₀ (gen_pow_ne_zero _), mul_one]⟩, hszG k hk⟩
  have hB : ∀ k < 15, LoadHolds rd (σv (.n 35)) (vtGi k)
        (σv (.n (vtBoffData.getD k default).2.2.2)) ∧
      σv (.n ((vtBoffData.getD k default).2.2.2 - 1)) = gen ^ 2 ^ vtKap lm τ (vtB0 k) ∧
      ∀ i < vtLen k - 1, σv (.n ((vtBoffData.getD k default).2.2.2 + 1 + i)) =
        σv (.n ((vtBoffData.getD k default).2.2.2 + i)) *
          σv (.n ((vtBoffData.getD k default).2.2.2 - 1)) := fun k hk ↦ (hbo k hk).2
  have hP := vtc_side_offsets hκ34 hG hB hsideT 0 0 0 9 54 111 0 (by norm_num) (by norm_num)
    (fun r hr ↦ (fP r hr).1) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel)
  have hC := vtc_side_offsets hκ34 hG hB hsideT 108 18 9 6 45 408 2 (by norm_num) (by norm_num)
    (fun r hr ↦ (fC r hr).1) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel)
  simp only [Nat.zero_add] at hP
  refine ⟨?_, hcp, hkb, hal, hP, hC⟩
  have j1 := forall_slice_join (a := 0) (l1 := 18) (l2 := 92) hpro hgP
  have j2 := forall_slice_join (a := 0) (l1 := 110) (l2 := 157) j1 rP
  have j3 := forall_slice_join (a := 0) (l1 := 267) (l2 := 72) j2 hbP
  have j4 := forall_slice_join (a := 0) (l1 := 339) (l2 := 64) j3 hgC
  have j5 := forall_slice_join (a := 0) (l1 := 403) (l2 := 103) j4 rC
  exact forall_slice_join (a := 0) (l1 := 506) (l2 := 57) j5 hbC

end

end
end LeanVM.Guest.B1.Tables
