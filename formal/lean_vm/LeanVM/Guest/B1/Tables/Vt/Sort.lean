/-
  LeanVM.Guest.B1.Tables.Vt.Sort

  `verify_tables`' block certification: on the push and the count side, every block's offset
  variable holds `g^` its `stackOffsets` offset over the side's log-sizes.
-/

module

public import LeanVM.Guest.B1.Tables.Vt.SortT
public import LeanVM.Guest.B1.Tables.GroupCert
public import LeanVM.Guest.B1.Tables.Interface

/-!
# A side's block offsets (G:2130-2171)

`vt_rank0`, `vt_rank`: what a rank's template gives (`VtRankFacts`). `vt_side_cert`: when every
group's key is `g^(254 κ - b0)` and its size `g^(len·2^κ)`, the ranks of a side certify its groups'
order strictly descending in the key (`tb_group_offsets`), so every block's offset is its
`stackOffsets` offset. `vt_sort`: the push side's `54` blocks and the count side's `45`, their
log-sizes `vtKap` of the memory's log-size and the tables' heights.
-/

namespace LeanVM.Guest.B1.Tables

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Protocol LeanVM.Protocol.Verifier
open Finset

@[expose] public section

/-! ## The sizes -/

/-- The tables' heights, in table order. -/
def vtTauList (τ : ℕ → ℕ) : List ℕ := (List.range 6).map τ

/-- Block `b`'s log-size: `kappa_base[BLOCK_KAPPA_SRC[b]]·g^BLOCK_KAPPA_ADJ[b]` in the exponent. -/
def vtKap (lm : ℕ) (τ : ℕ → ℕ) (b : ℕ) : ℕ :=
  ([0, lm] ++ vtTauList τ).getD (blockKappaSrc.getD b 0) 0 + blockKappaAdj b

/-! ## The ranks -/

/-- Choices below `n` as a function. -/
theorem vt_choose_fun {α : Type} [Inhabited α] {n : ℕ} {P : ℕ → α → Prop}
    (h : ∀ r < n, ∃ a, P r a) : ∃ f : ℕ → α, ∀ r < n, P r (f r) := by
  classical
  exact ⟨fun r => if hr : r < n then Classical.choose (h r hr) else default,
    fun r hr => by simp only [hr, ↓reduceDIte]; exact Classical.choose_spec (h r hr)⟩

theorem vt_word_small_inj {a b : ℕ} (ha : a < 3) (hb : b < 3) (h : word a 0 = word b 0) :
    a = b := by
  rw [tb_word_eOfNat, tb_word_eOfNat] at h
  exact eOfNat_inj (by omega) (by omega) h


theorem vtW23_eq : vtW23 = ofK (Parameters.addressOfIndex 23) := by
  rw [vtW23, show (8388608 : ℕ) = 2 ^ 23 by norm_num, tb_word_two_pow (by norm_num),
    gen_pow_eq_ofK]

theorem vtW8635_eq : vtW8635 = ofK (Parameters.addressOfIndex 8635) := by
  rw [vtW8635, tb_word_eOfNat]
  show ofK (K.ofBits 9287367476377611832) = ofK (Parameters.addressOfIndex 8635)
  rw [show K.ofBits 9287367476377611832 = Parameters.addressOfIndex 8635 by decide +kernel]

/-- Rank `r`'s group size read. -/
def vtSz (v0 r : ℕ) : ℕ := if r = 0 then v0 + 12 else vtRv v0 r + 18

/-- The running offset after rank `r`. -/
def vtGout (v0 r : ℕ) : ℕ := if r = 0 then v0 + 12 else vtRv v0 r + 19

theorem vt_gin_succ (v0 r : ℕ) : vtGin v0 (r + 1) = vtGout v0 r := by
  rcases Nat.eq_zero_or_pos r with rfl | hr
  · simp [vtGin, vtGout]
  · have h1 : r + 1 ≠ 0 := by omega
    have h2 : r + 1 ≠ 1 := by omega
    have h3 : r ≠ 0 := by omega
    simp only [vtGin, vtGout, h1, h2, h3, ↓reduceIte, Nat.add_sub_cancel]

/-- What rank `r` of a side gives: its group `g^e`, `e < 24`, of side `s`; the group's key, base
and size read; the running offset; and, past the first rank, the previous key `g^(d+1)` times
this one. -/
def VtRankFacts (rd : Reader) (σ : Val) (v0 s r : ℕ) : Prop :=
  (∃ e < 24, σ (.n (vtRv v0 r)) = gen ^ e) ∧
    LoadHolds rd (σ (.n 12) * σ (.n (vtRv v0 r))) 212 (word s 0) ∧
    LoadHolds rd (σ (.n 36) * σ (.n (vtRv v0 r))) 0 (σ (.n (vtRv v0 r + 8))) ∧
    LoadHolds rd (σ (.n 38) * σ (.n (vtRv v0 r))) 0 (σ (.n (vtGin v0 r))) ∧
    LoadHolds rd (σ (.n 37) * σ (.n (vtRv v0 r))) 0 (σ (.n (vtSz v0 r))) ∧
    σ (.n (vtGout v0 r)) = σ (.n (vtGin v0 r)) * σ (.n (vtSz v0 r)) ∧
    (r = 0 → σ (.n (vtGin v0 r)) = 1) ∧
    (1 ≤ r → ∃ d < 8636, σ (.n (vtRv v0 (r - 1) + 8)) = gen ^ (d + 1) * σ (.n (vtRv v0 r + 8)))

section
variable {μ : ℕ} (hμ : μ ≤ 32) (Lm : MemoryImage μ)
include hμ

theorem vt_rc {σ : Val} {x y t1 t2 k : V} {K : ℕ} (hK1 : 1 ≤ K) (hK : K ≤ 2 ^ 33)
    (hk : σ k = ofK (Parameters.addressOfIndex (K - 1)))
    (h : (Atom.rangeCheck x y t1 t2 k).Holds Lm.read σ) : ∃ e < K, σ x = gen ^ e :=
  tb_rc_sound' hμ Lm hK1 hK hk h.1 h.2.1 h.2.2

theorem vt_rank0 {σ : Val} {v0 R0 s : ℕ} {kret : List E → Prop}
    (h : Stmt.HoldsList (coreProgram.Rel Lm.read) Lm.read σ (vtRank0T v0 R0 s) True kret) :
    VtRankFacts Lm.read σ v0 s 0 := by
  simp only [vtRank0T, Stmt.HoldsList, Stmt.Holds, and_true] at h
  obtain ⟨-, c1, rc2, c5, m6, l5, m7, l8, c9, m10, l9, m11, l12⟩ := h
  simp only [Atom.Holds] at c1 c5 m6 l5 m7 l8 c9 m10 l9 m11 l12
  simp only [VtRankFacts, vtRv, vtGin, vtSz, vtGout, ↓reduceIte]
  refine ⟨vt_rc hμ Lm (K := 24) (by omega) (by norm_num) (by rw [c1, vtW23_eq]) rc2,
    by rw [← m6, ← c5]; exact l5, by rw [← m7]; exact l8, by rw [← m10]; exact l9,
    by rw [← m11]; exact l12, by rw [c9, tb_word_one, one_mul], fun _ => by rw [c9, tb_word_one],
    fun h => absurd h (by omega)⟩

theorem vt_rank {σ : Val} {v0 R0 s r : ℕ} (hr : 1 ≤ r) {kret : List E → Prop}
    (h : Stmt.HoldsList (coreProgram.Rel Lm.read) Lm.read σ (vtRankAt v0 R0 s r) True kret) :
    VtRankFacts Lm.read σ v0 s r := by
  simp only [vtRankAt, vtRankT, Stmt.HoldsList, Stmt.Holds, and_true] at h
  obtain ⟨-, c1, rc2, c5, m6, l5, m7, l8, c9, mpk, c11, m12, rc12, m16, lgin, m17, l18, m19⟩ := h
  simp only [Atom.Holds] at c1 c5 m6 l5 m7 l8 c9 mpk c11 m12 m16 lgin m17 l18 m19
  have hr0 : r ≠ 0 := by omega
  have hsz : vtSz v0 r = vtRv v0 r + 18 := by simp [vtSz, hr0]
  have hgo : vtGout v0 r = vtRv v0 r + 19 := by simp [vtGout, hr0]
  rw [VtRankFacts, hsz, hgo]
  refine ⟨vt_rc hμ Lm (K := 24) (by omega) (by norm_num) (by rw [c1, vtW23_eq]) rc2,
    by rw [← m6, ← c5]; exact l5, by rw [← m7]; exact l8, by rw [← m16]; exact lgin,
    by rw [← m17]; exact l18, m19, fun h => absurd h hr0, fun _ => ?_⟩
  obtain ⟨d, hd, hdv⟩ := vt_rc hμ Lm (K := 8636) (by omega) (by norm_num)
    (by rw [c9, vtW8635_eq]) rc12
  refine ⟨d, hd, ?_⟩
  have h10 : σ (.n (vtRv v0 r + 10)) = gen ^ (d + 1) := by
    calc σ (.n (vtRv v0 r + 10)) = σ (.n (vtRv v0 r + 10)) * (vtWInvGen * gen ^ 1) := by
          rw [vt_wInv (by decide +kernel), mul_one]
      _ = gen ^ (d + 1) := by rw [← mul_assoc, ← c11, ← m12, hdv, ← pow_add]
  rw [mpk, h10]

end

/-! ## A side -/

/-- Block group `gi`'s side, as `exponent_tables` writes it. -/
def vtGroupSide (gi : ℕ) : ℕ := if gi < 9 then 0 else if gi < 18 then 1 else 2

theorem vt_sideTab_getD : ∀ e < 24, sideTabList.getD e 0 = word (vtGroupSide e) 0 := by
  intro e he
  rw [tb_word_eOfNat, List.getD_eq_getElem _ _ (by simp [sideTabList]; exact he)]
  simp only [sideTabList, List.getElem_map, List.getElem_range]
  congr 1
  revert e; decide

/-- **A side's certified offsets.** The side's blocks `x < n` (global `base + x`) in `m` groups
`G0 + j` (`st`, `grp`, log-sizes `kg`), each group's key and size stored at `G0 + j`, its first
block's offset read from `group_base`, the others one step `g^(2^κ)` on: the ranks give every
block its `stackOffsets` offset. -/
theorem vt_side_cert {rd : Reader} {σ : Val} {n m G0 base v0 s : ℕ} (κs : List ℕ)
    (hlen : κs.length = n) (st kg grp bv : ℕ → ℕ) (hn : base + n ≤ 153)
    (hfacts : ∀ r < m, VtRankFacts rd σ v0 s r)
    (hside : ∀ e < 24, LoadHolds rd (σ (.n 12)) (212 + e) (word (vtGroupSide e) 0))
    (hsideS : ∀ e < 24, vtGroupSide e = s → G0 ≤ e ∧ e < G0 + m) (hs : s < 3)
    (hkey : ∀ j < m, ∃ key, LoadHolds rd (σ (.n 36)) (G0 + j) key ∧
      key * gen ^ (base + st j) = gen ^ (kg j * 254))
    (hsz : ∀ j < m, LoadHolds rd (σ (.n 37)) (G0 + j) (gen ^ ((st (j + 1) - st j) * 2 ^ kg j)))
    (hkg : ∀ j < m, kg j < 34) (hrun : ∀ j < m, st j < st (j + 1))
    (hgrp : ∀ x < n, grp x < m ∧ st (grp x) ≤ x ∧ x < st (grp x + 1))
    (hgrp' : ∀ j < m, ∀ x, st j ≤ x → x < st (j + 1) → x < n ∧ grp x = j)
    (hκ : ∀ x < n, κs.getD x 0 = kg (grp x))
    (hb0 : ∀ j < m, LoadHolds rd (σ (.n 38)) (G0 + j) (σ (.n (bv (st j)))))
    (hstep : ∀ x < n, st (grp x) < x →
      σ (.n (bv x)) = σ (.n (bv (x - 1))) * gen ^ 2 ^ kg (grp x)) :
    ∀ x < n, σ (.n (bv x)) = gen ^ (stackOffsets κs).1.getD x 0 := by
  have hstn : ∀ j < m, base + st j < 153 := fun j hj => by
    have := (hgrp' j hj (st j) le_rfl (hrun j hj)).1; omega
  -- the ranks' groups
  obtain ⟨e, he⟩ := vt_choose_fun (n := m) (fun r hr => (hfacts r hr).1)
  have hes : ∀ r < m, G0 ≤ e r ∧ e r < G0 + m := fun r hr => by
    have h3 := (hfacts r hr).2.1
    rw [(he r hr).2, tb_loadHolds_mul_gen_pow, Nat.add_comm] at h3
    have := tb_loadHolds_unique h3 (hside _ (he r hr).1)
    exact hsideS _ (he r hr).1
      (vt_word_small_inj hs (by unfold vtGroupSide; split_ifs <;> omega) this).symm
  set o : ℕ → ℕ := fun r => e r - G0 with ho_def
  have hoe : ∀ r < m, G0 + o r = e r := fun r hr => by have := hes r hr; simp only [ho_def]; omega
  have ho : ∀ r < m, o r < m := fun r hr => by have := hes r hr; simp only [ho_def]; omega
  -- the keys, in the exponent
  set keyN : ℕ → ℕ := fun j => kg j * 254 + 153 - (base + st j) with hkeyN
  have hkv : ∀ r < m, σ (.n (vtRv v0 r + 8)) * gen ^ 153 = gen ^ keyN (o r) := fun r hr => by
    obtain ⟨key, hk1, hk2⟩ := hkey (o r) (ho r hr)
    have h4 := (hfacts r hr).2.2.1
    rw [(he r hr).2, tb_loadHolds_mul_gen_pow, Nat.add_zero, ← hoe r hr] at h4
    rw [tb_loadHolds_unique h4 hk1]
    have hb := hstn (o r) (ho r hr)
    rw [show (153 : ℕ) = (base + st (o r)) + (153 - (base + st (o r))) by omega, pow_add,
      ← mul_assoc, hk2, ← pow_add, hkeyN]
    congr 1
    beta_reduce
    omega
  have hkN : ∀ j < m, keyN j < 2 ^ 62 := fun j hj => by
    have := hkg j hj; simp only [hkeyN]; omega
  have hdec : ∀ r, r + 1 < m → keyN (o (r + 1)) < keyN (o r) := fun r hr => by
    obtain ⟨d, hd, hdv⟩ := (hfacts (r + 1) hr).2.2.2.2.2.2.2 (by omega)
    rw [Nat.add_sub_cancel] at hdv
    have e1 : gen ^ keyN (o r) = gen ^ (d + 1) * gen ^ keyN (o (r + 1)) := by
      rw [← hkv r (by omega), ← hkv (r + 1) hr, hdv, mul_assoc]
    have := tb_gen_pow_eq_mul (hkN _ (ho r (by omega))) (hkN _ (ho (r + 1) hr)) (by omega) e1
    omega
  have hkeyO : ∀ a < m, ∀ b < m, keyN b < keyN a ↔
      (kg b < kg a ∨ (kg a = kg b ∧ st a < st b)) := by
    intro a ha b hb
    have := hstn a ha; have := hstn b hb
    simp only [hkeyN]
    omega
  -- the groups' bases
  have hgin : ∀ r < m, σ (.n (vtGin v0 r)) =
      gen ^ (∑ r' ∈ range r, (st (o r' + 1) - st (o r')) * 2 ^ kg (o r')) := by
    intro r hr
    induction r with
    | zero => rw [(hfacts 0 hr).2.2.2.2.2.2.1 rfl]; simp
    | succ r ih =>
      have hr' : r < m := by omega
      have h5 := (hfacts r hr').2.2.2.2.1
      rw [(he r hr').2, tb_loadHolds_mul_gen_pow, Nat.add_zero, ← hoe r hr'] at h5
      rw [vt_gin_succ, (hfacts r hr').2.2.2.2.2.1, ih hr',
        tb_loadHolds_unique h5 (hsz _ (ho r hr')), ← pow_add, Finset.sum_range_succ]
  have hbase : ∀ r < m, σ (.n (bv (st (o r)))) =
      gen ^ (∑ r' ∈ range r, (st (o r' + 1) - st (o r')) * 2 ^ kg (o r')) := fun r hr => by
    have h4 := (hfacts r hr).2.2.2.1
    rw [(he r hr).2, tb_loadHolds_mul_gen_pow, Nat.add_zero, ← hoe r hr, hgin r hr] at h4
    exact tb_loadHolds_unique (hb0 _ (ho r hr)) h4
  -- within a group
  have hwithin : ∀ k, ∀ x < n, x - st (grp x) = k →
      σ (.n (bv x)) = σ (.n (bv (st (grp x)))) * gen ^ (k * 2 ^ kg (grp x)) := by
    intro k
    induction k with
    | zero =>
      intro x hx hk
      have hx' : x = st (grp x) := by have := hgrp x hx; omega
      conv_lhs => rw [hx']
      simp
    | succ k ih =>
      intro x hx hk
      obtain ⟨hg, h1, h2⟩ := hgrp x hx
      have hlt : st (grp x) < x := by omega
      have hg1 : grp (x - 1) = grp x := (hgrp' (grp x) hg (x - 1) (by omega) (by omega)).2
      rw [hstep x hx hlt, ih (x - 1) (by omega) (by rw [hg1]; omega), hg1, mul_assoc, ← pow_add]
      congr 2
      ring
  intro x hx
  obtain ⟨r, hr, hor, hoff⟩ :=
    tb_group_offsets κs hlen st kg grp keyN o hgrp hgrp' hκ hkeyO ho hdec x hx
  rw [hwithin _ x hx rfl, hoff, ← hor, hbase r hr, pow_add]

/-! ## Both sides -/

/-- Global block `b`'s group index `k < 15` (`vtGi`). -/
def vtBk (b : ℕ) : ℕ := ((List.range 15).filter (fun k ↦ vtB0 k ≤ b)).length - 1

/-- Block `b`'s offset variable (`block_off[b]`). -/
def vtBoffV (b : ℕ) : ℕ := (vtBoffData.getD (vtBk b) default).2.2.2 + (b - vtB0 (vtBk b))

theorem vt_kap_lt (lm : ℕ) (τ : ℕ → ℕ) (hlm : lm ≤ 32) (hτ : ∀ t < 6, τ t < 29) {b : ℕ}
    (hb : b < 153) : vtKap lm τ b < 34 := by
  have hadj : ∀ b < 153, blockKappaAdj b = 0 ∨
      (blockKappaAdj b = 19 ∧ blockKappaSrc.getD b 0 = 0) := by decide
  have hle : ∀ i, ([0, lm] ++ vtTauList τ).getD i 0 ≤ 32 := by
    intro i
    match i with
    | 0 => simp
    | 1 => simpa using hlm
    | i + 2 =>
      simp only [List.cons_append, List.nil_append, List.getD_cons_succ, vtTauList]
      by_cases hi : i < 6
      · rw [List.getD_eq_getElem _ _ (by simp; exact hi)]
        simp only [List.getElem_map, List.getElem_range]
        have := hτ i hi; omega
      · rw [List.getD_eq_default _ _ (by simp; omega)]; omega
  rcases hadj b hb with h0 | ⟨h19, hs0⟩
  · rw [vtKap, h0]; have := hle (blockKappaSrc.getD b 0); omega
  · rw [vtKap, h19, hs0]; simp

section
variable {μ : ℕ} (hμ : μ ≤ 32) (Lm : MemoryImage μ)
include hμ

/-- **`verify_tables`' block certification** (G:2130-2171): with `kappa_base` the memory's log-size
and the tables' heights and the exponent tables in place, the push side's `54` blocks and the
count side's `45` hold `g^` the `stackOffsets` offsets of their side's log-sizes in `block_off`. -/
theorem vt_sort {σ : Val} (h : VtH Lm.read σ) {lm : ℕ} {τ : ℕ → ℕ} (hlm : lm ≤ 32)
    (hτ : ∀ t < 6, τ t < 29)
    (hkb : ∀ i < 8, σ (.n (28 + i)) = gen ^ ([0, lm] ++ vtTauList τ).getD i 0)
    (hE : ExpTablesAt Lm.read (σ (.n 12))) :
    (∀ x < 54, σ (.n (vtBoffV x)) =
      gen ^ (stackOffsets ((List.range 54).map (vtKap lm τ))).1.getD x 0) ∧
    (∀ x < 45, σ (.n (vtBoffV (108 + x))) =
      gen ^ (stackOffsets ((List.range 45).map fun c ↦ vtKap lm τ (108 + c))).1.getD x 0) := by
  obtain ⟨hsq, hrk, hsd⟩ := hE
  have hsrc : ∀ k < 15, blockKappaSrc.getD (vtB0 k) 0 < 8 := by decide +kernel
  have hkx : ∀ k < 15, σ (.n (vtKv k)) * gen ^ vtAdj k = gen ^ vtKap lm τ (vtB0 k) := by
    intro k hk
    rw [vtKv, hkb _ (hsrc k hk), ← pow_add, vtKap, vtAdj]
  have hκ34 : ∀ k < 15, vtKap lm τ (vtB0 k) < 34 := fun k hk =>
    vt_kap_lt lm τ hlm hτ (by have : ∀ k < 15, vtB0 k < 153 := by decide +kernel
                              exact this k hk)
  -- the groups' keys and sizes
  have hG : ∀ k < 15, (∃ key, LoadHolds Lm.read (σ (.n 36)) (vtGi k) key ∧
      key * gen ^ vtB0 k = gen ^ (vtKap lm τ (vtB0 k) * 254)) ∧
      LoadHolds Lm.read (σ (.n 37)) (vtGi k) (gen ^ (vtLen k * 2 ^ vtKap lm τ (vtB0 k))) := by
    intro k hk
    obtain ⟨key, rk, sz, sq, hk1, hrk1, hke, hsz1, hsq1, hszv⟩ := vt_grps h k hk
    rw [hkx k hk, tb_loadHolds_mul_gen_pow] at hrk1 hsq1
    have hκ := hκ34 k hk
    have r1 := hrk _ (by simp [rankKeysList]; exact hκ)
    rw [tb_loadHolds_mul_gen_pow] at r1
    have s1 := hsq _ (by simp [gSquaresList]; exact hκ)
    have e1 := tb_loadHolds_unique hrk1 (by rw [Nat.add_comm]; exact r1)
    have e2 := tb_loadHolds_unique hsq1 (by rw [Nat.add_zero]; exact s1)
    simp only [rankKeysList, List.getElem_map, List.getElem_range] at e1
    simp only [gSquaresList, List.getElem_map, List.getElem_range] at e2
    refine ⟨⟨key, hk1, by rw [hke, e1]⟩, ?_⟩
    rwa [hszv, e2, ← pow_mul, mul_comm] at hsz1
  -- the groups' block offsets
  have hB : ∀ k < 15, LoadHolds Lm.read (σ (.n 38)) (vtGi k)
        (σ (.n (vtBoffData.getD k default).2.2.2)) ∧
      σ (.n ((vtBoffData.getD k default).2.2.2 - 1)) = gen ^ 2 ^ vtKap lm τ (vtB0 k) ∧
      ∀ i < vtLen k - 1, σ (.n ((vtBoffData.getD k default).2.2.2 + 1 + i)) =
        σ (.n ((vtBoffData.getD k default).2.2.2 + i)) *
          σ (.n ((vtBoffData.getD k default).2.2.2 - 1)) := by
    intro k hk
    obtain ⟨hkv, hoff, h2⟩ := vtBoffData_kv k hk
    obtain ⟨kr, hs⟩ := h.sliceAt _ _ (vtBoff_check k hk)
    rw [vtBoffT, tb_holdsList_append_noRet rfl, tb_holdsList_mapAtoms] at hs
    obtain ⟨h1, hst⟩ := hs
    simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds, and_true] at h1
    obtain ⟨m0, l1, l2⟩ := h1
    refine ⟨l2, ?_, fun i hi => by simpa [Atom.Holds] using hst i hi⟩
    rw [m0, hkv, hoff] at l1
    have l1' : LoadHolds Lm.read (σ (.n 12) * (σ (.n (vtKv k)) * gen ^ vtAdj k)) 0
        (σ (.n ((vtBoffData.getD k default).2.2.2 - 1))) := by
      rw [← mul_assoc, tb_loadHolds_mul_gen_pow, Nat.add_zero]; exact l1
    rw [hkx k hk, tb_loadHolds_mul_gen_pow, Nat.add_zero] at l1'
    have s1 := hsq _ (by simp [gSquaresList]; exact hκ34 k hk)
    rw [tb_loadHolds_unique l1' s1]
    simp [gSquaresList]
  have hsideT : ∀ e < 24, LoadHolds Lm.read (σ (.n 12)) (212 + e) (word (vtGroupSide e) 0) :=
    fun e he => by
      have := hsd e (by simp [sideTabList]; exact he)
      rw [tb_loadHolds_mul_gen_pow] at this
      rw [← vt_sideTab_getD e he, List.getD_eq_getElem _ _ (by simp [sideTabList]; exact he)]
      exact this
  -- one side, from its group and block layout (all checked by evaluation)
  have side : ∀ (base G0 kOff m n v0 s : ℕ), base + n ≤ 153 → s < 3 →
      (∀ r < m, VtRankFacts Lm.read σ v0 s r) →
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
  have hP := side 0 0 0 9 54 114 0 (by norm_num) (by norm_num) (fun r hr => by
      rcases Nat.eq_zero_or_pos r with rfl | hr0
      · obtain ⟨k, hs⟩ := h.sliceAt 113 _ vtPush0_check
        exact vt_rank0 hμ Lm hs
      · obtain ⟨k, hs⟩ := h.sliceAt _ _ (vtPush_check r hr hr0)
        exact vt_rank hμ Lm hr0 hs)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  have hC := side 108 18 9 6 45 411 2 (by norm_num) (by norm_num) (fun r hr => by
      rcases Nat.eq_zero_or_pos r with rfl | hr0
      · obtain ⟨k, hs⟩ := h.sliceAt 406 _ vtCount0_check
        exact vt_rank0 hμ Lm hs
      · obtain ⟨k, hs⟩ := h.sliceAt _ _ (vtCount_check r hr hr0)
        exact vt_rank hμ Lm hr0 hs)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  simp only [Nat.zero_add] at hP
  exact ⟨hP, hC⟩

end

end
end LeanVM.Guest.B1.Tables
