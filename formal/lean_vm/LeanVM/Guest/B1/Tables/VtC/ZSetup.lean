/-
  LeanVM.Guest.B1.Tables.VtC.ZSetup

  `verify_tables`' statements `2590 ..< 2683`, completely: the table sumcheck's round count, its
  batching challenge and target, its rounds and its equality prefix.
-/

module

public import LeanVM.Guest.B1.Tables.VtC.ZBase
public import LeanVM.Guest.Data.NameStrings

/-!
# The table sumcheck's setup, completely

Helpers for the honest valuation: a read of a word the memory holds (`z_read`), a product read
as a quotient (`z_div`), a passing range check (`z_rc`, `z_rcd`), a `KECCAK` (`z_keccak`).
-/

namespace LeanVM.Guest.B1.Tables

open LeanVM.Parameters LeanVM.Semantics LeanVM.Core LeanVM.Core.Value
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Guest.B1.Fwd

@[expose] public section

section Helpers
variable {rd : Reader} {σ : Val}

/-- A read of a word the memory holds. -/
theorem z_read {d p : V} {off : ℕ} {v : E}
    (hg : Atom.load d p off ∈ vtSL ∨ σ d = rdAt rd (σ p) off) (hS : Atom.load d p off ∉ vtSL)
    (hm : LoadHolds rd (σ p) off v) : σ d = v ∧ (Atom.load d p off).Holds rd σ := by
  have e : σ d = v := by rw [hg.resolve_left hS, rdAt, hm.2]; rfl
  exact ⟨e, by show LoadHolds rd _ _ _; rw [e]; exact hm⟩

/-- A product read as a quotient. -/
theorem z_div {d x y : V} (hg : σ x = σ d * (σ y)⁻¹) (hy : σ y ≠ 0) :
    (Atom.mul d x y).Holds rd σ := by
  show σ d = σ x * σ y
  rw [hg, mul_assoc, inv_mul_cancel₀ hy, mul_one]

theorem z_gen_addr (a : ℕ) : (gen ^ a).limb 0 * Parameters.addressOfIndex 0 =
    Parameters.addressOfIndex a := by
  rw [gen_pow_eq_ofK]; simp [Parameters.addressOfIndex]

theorem z_low_load {a : ℕ} (h : (rd (Parameters.addressOfIndex a)).isSome) :
    LoadHolds rd (gen ^ a) 0 (rdAt rd (gen ^ a) 0) :=
  load_of_rdAt rfl (gen_pow_isInK a) (by rw [z_gen_addr]; exact h)

/-- **A passing range check**: `x = g^a`, `a ≤ K`, `k = g^K`, on a memory defined at `g^a` and
`g^(K - a)`. -/
theorem z_rc {x y t1 t2 k : V} {a K : ℕ} (haK : a ≤ K) (hx : σ x = gen ^ a) (hk : σ k = gen ^ K)
    (hg : σ t1 = rdAt rd (σ x) 0 ∧ σ t2 = rdAt rd (σ y) 0 ∧ σ y = σ k * (σ x)⁻¹)
    (h1 : (rd (Parameters.addressOfIndex a)).isSome) (h2 : (rd (Parameters.addressOfIndex (K -
        a))).isSome) :
    (Atom.rangeCheck x y t1 t2 k).Holds rd σ := by
  obtain ⟨e1, e2, ey⟩ := hg
  have ey' : σ y = gen ^ (K - a) := by rw [ey, hk, hx, ← pow_sub₀ _ gen_ne_zero haK]
  refine ⟨?_, ?_, ?_⟩
  · rw [e1, hx]; exact z_low_load h1
  · rw [hk, hx, ey', ← pow_add, Nat.add_sub_cancel' haK]
  · rw [e2, ey']; exact z_low_load h2

/-- A range check's facts, as `eq_prefix_chain` states them. -/
theorem z_rcd {a K : ℕ} (haK : a ≤ K) (h1 : (rd (Parameters.addressOfIndex a)).isSome)
    (h2 : (rd (Parameters.addressOfIndex (K - a))).isSome) : RangeChecked rd (gen ^ a) (gen ^ K) :=
  ⟨gen ^ (K - a), _, _, z_low_load h1, by rw [← pow_add, Nat.add_sub_cancel' haK],
    z_low_load h2⟩

/-- **A `KECCAK`** holds by its equations. -/
theorem z_keccak {S : List Atom} {w : ℕ → E} {ins outs : List V} {i o : Bool}
    (hg : Good rd S w σ (.keccak ins outs i o)) : (Atom.keccak ins outs i o).Holds rd σ :=
  holds_of_good hg trivial

theorem z_w32 : word 4294967296 0 = gen ^ 32 := by
  rw [show (4294967296 : ℕ) = 2 ^ 32 by norm_num, tb_word_two_pow (by norm_num)]

end Helpers

/-- The bus target: `ξ²·T_0 + ξ³·T_1 + ξ⁴·T_2` on the sides' totals. -/
def zTarget (σ : Val) (ξ : E) : E :=
  ξ ^ 2 * σ (.n 2441) + ξ ^ 3 * σ (.n 2487) + ξ ^ 4 * σ (.n 2542)

/-- What statements `2590 ..< 2683` give: `g^n`, `ξ` (the squeeze of `S`), the sponge after it,
the target, the buffers' sizes and pointers, and the last record (the sponge, the cursor `3n`
words on, the final claim). -/
def ZOut (σ : Val) (w : ℕ → E) (S : Fs) (xs : List E) (n : ℕ) : Prop :=
  σ (.n 2543) = gen ^ n ∧ σ (.n 2596) = S.squeeze.1 ∧
    [σ (.n 2604), σ (.n 2605), σ (.n 2606), σ (.n 2607), σ (.n 2608)] = S.squeeze.2.cap ∧
    σ (.n 2618) = zTarget σ S.squeeze.1 ∧ σ (.n 2624) = gen ^ (7 * (n + 1)) ∧
    σ (.n 2627) = gen ^ (n + 1) ∧ σ (.n 2648) = gen ^ (n + 1) ∧ σ (.n 2625) = w 2625 ∧
    σ (.n 2628) = w 2628 ∧ σ (.n 2649) = w 2649 ∧
    [σ (.n 2640), σ (.n 2641), σ (.n 2642), σ (.n 2643), σ (.n 2644)] =
      (zcRec S.squeeze.2.cap (zTarget σ S.squeeze.1) xs n).1 ∧
    σ (.n 2645) = σ (.n 1896) * gen * gen ^ (3 * n) ∧
    σ (.n 2646) = (zcRec S.squeeze.2.cap (zTarget σ S.squeeze.1) xs n).2

/-- The statements evaluation alone does not settle. -/
noncomputable def zRest : List Stmt := [
    .atom (.mul (.n 2543) (.n 2545) (.n 27)),
    .atom (.rangeCheck (.n 2545) (.n 2546) (.n 2547) (.n 2548) (.n 2544)),
    .atom (.mul (.n 2543) (.n 2551) (.n 28)),
    .atom (.rangeCheck (.n 2551) (.n 2552) (.n 2553) (.n 2554) (.n 2550)),
    .atom (.mul (.n 2543) (.n 2558) (.n 29)),
    .atom (.rangeCheck (.n 2558) (.n 2559) (.n 2560) (.n 2561) (.n 2557)),
    .atom (.mul (.n 2543) (.n 2565) (.n 30)),
    .atom (.rangeCheck (.n 2565) (.n 2566) (.n 2567) (.n 2568) (.n 2564)),
    .atom (.mul (.n 2543) (.n 2572) (.n 31)),
    .atom (.rangeCheck (.n 2572) (.n 2573) (.n 2574) (.n 2575) (.n 2571)),
    .atom (.mul (.n 2543) (.n 2579) (.n 32)),
    .atom (.rangeCheck (.n 2579) (.n 2580) (.n 2581) (.n 2582) (.n 2578)),
    .atom (.assertEq (.n 2584) (.n 2585)),
    .atom (.mul (.n 9) (.n 2587) (.n 2543)),
    .atom (.rangeCheck (.n 2587) (.n 2588) (.n 2589) (.n 2590) (.n 2586)),
    .atom (.keccak [.n 1905, .n 1906, .n 2592, .n 2592, .n 2592, .n 2593, .n 2594, .n 2595, .n 1899, .n 1900, .n 1901, .n 1902, .n 1903] [.n 2596, .n 2597, .n 2598, .n 2599, .n 2600, .n 2601, .n 2602, .n 2603, .n 2604, .n 2605, .n 2606, .n 2607, .n 2608] false false),
    .atom (.load (.n 2604) (.n 2625) 0),
    .atom (.load (.n 2605) (.n 2625) 1),
    .atom (.load (.n 2606) (.n 2625) 2),
    .atom (.load (.n 2607) (.n 2625) 3),
    .atom (.load (.n 2608) (.n 2625) 4),
    .atom (.load (.n 2630) (.n 2625) 5),
    .atom (.load (.n 2618) (.n 2625) 6),
    .atom (.load (.n 2631) (.n 2628) 0),
    .callIf (.n 2633) name% «verify_tables_loop0» [.n 2634, .n 2543, .n 2625, .n 18, .n 16,
        .n 2543, .n 2628],
    .atom (.load (.n 2640) (.n 2639) 0),
    .atom (.load (.n 2641) (.n 2639) 1),
    .atom (.load (.n 2642) (.n 2639) 2),
    .atom (.load (.n 2643) (.n 2639) 3),
    .atom (.load (.n 2644) (.n 2639) 4),
    .atom (.load (.n 2645) (.n 2639) 5),
    .atom (.load (.n 2646) (.n 2639) 6),
    .call "eq_prefix_chain" [.n 2649, .n 2650, .n 16, .n 699, .n 2543] []]

set_option maxRecDepth 100000 in
/-- **Statements `2590 ..< 2683`, completely**: the hinted `g^n` with `n` the
largest `τ_t` (at most `m = |point|`), the squeeze `ξ` (`XI_GRIND_BITS = 0`) of the sponge `S`
with the bytecode's value waiting, the target, the first record, `verify_tables_loop0`'s rounds on
the honest buffers (records, running products, `chi`) and words `xs` at the cursor one past the
bytecode's
value, the last record, `eq_prefix_chain` into the prefix weights of `chi` against `zeta1`. -/
theorem vtZ_complete {rd : Reader} {w : ℕ → E} {args : List E} (hl : args.length = 20)
    {m n : ℕ} {τ : ℕ → ℕ} (hτ : ∀ t < 6, τ t ≤ n) (hτn : ∃ t < 6, τ t = n) (hnm : n ≤ m)
    (hm : m ≤ 32) (h9 : vtσ rd w args (.n 9) = gen ^ m)
    (hkb : ∀ t < 6, vtσ rd w args (.n (27 + t)) = gen ^ τ t)
    (hlow : ∀ i < 64, (rd (Parameters.addressOfIndex i)).isSome) (hwn : w 2543 = gen ^ n) {S : Fs}
    (hSr : rateOf S.pend = [vtσ rd w args (.n 1905), vtσ rd w args (.n 1906), 0, 0, 0, 0, 0, 0])
    (hSc : S.cap = [vtσ rd w args (.n 1899), vtσ rd w args (.n 1900), vtσ rd w args (.n 1901),
      vtσ rd w args (.n 1902), vtσ rd w args (.n 1903)])
    {xs : List E} (hxl : xs.length = 3 * n)
    (hxs : TbReadsAt rd (vtσ rd w args (.n 1896) * gen) xs)
    (hR : TbReadsAt rd (w 2625) (zcRoundsW S.squeeze.2.cap (zTarget (vtσ rd w args) S.squeeze.1)
      (vtσ rd w args (.n 1896) * gen) xs n))
    (hC : TbReadsAt rd (w 2628)
      (zcCprodW S.squeeze.2.cap (zTarget (vtσ rd w args) S.squeeze.1) xs n))
    (hchi : TbReadsAt rd (vtσ rd w args (.n 16))
      (zcChis S.squeeze.2.cap (zTarget (vtσ rd w args) S.squeeze.1) xs n))
    {zs1 : List E} (hz1 : TbReadsAt rd (vtσ rd w args (.n 699)) zs1) (hz1l : n ≤ zs1.length)
    (hP : TbReadsAt rd (w 2649) ((List.range (n + 1)).map (prefixProd 1
      (zcChis S.squeeze.2.cap (zTarget (vtσ rd w args) S.squeeze.1) xs n) (zs1.take n)))) :
    (∀ s ∈ (vtPre.drop 2590).take 93, VSH (coreProgram.Rel rd) rd (vtσ rd w args) s) ∧
      ZOut (vtσ rd w args) w S xs n := by
  have g : GoodL rd w (vtσ rd w args) zBlk := vt_goodL hl 2590 zBlk zBlk_at
  have gk : Good rd vtSL w (vtσ rd w args) (.keccak [.n 1905, .n 1906, .n 2592, .n 2592, .n 2592, .n 2593, .n 2594, .n 2595, .n 1899,
      .n 1900, .n 1901, .n 1902, .n 1903] (lyOuts 2596) false false) :=
    (vt_goodL (rd := rd) (w := w) hl 2630 [.atom (.keccak [.n 1905, .n 1906, .n 2592, .n 2592, .n 2592, .n 2593, .n 2594, .n 2595, .n 1899,
      .n 1900, .n 1901, .n 1902, .n 1903]
      (lyOuts 2596) false false)] (by decide +kernel)).1
  have e := tbStmtsEqb_sound zBlk_at
  have hlen : zBlk.length = 93 := rfl
  suffices H : (∀ s ∈ zRest, VSH (coreProgram.Rel rd) rd (vtσ rd w args) s) ∧
      ZOut (vtσ rd w args) w S xs n by
    refine ⟨fun s hs => ?_, H.2⟩
    rw [← hlen, ← e] at hs
    exact vt_block hl 2590 zBlk zBlk_at zRest (by decide +kernel) H.1 s hs
  generalize vtσ rd w args = σ at *
  simp only [zBlk, GoodL, GoodS, Good, fixNe, List.forall_mem_cons, Nat.reduceLT, and_true,
    and_false, ↓reduceIte] at g
  obtain ⟨g2590, g2591, g2592, g2593, g2594, g2595, g2596, g2597, g2598, g2599, g2600, g2601, g2602,
    g2603, g2604, g2605, g2606, g2607, g2608, g2609, g2610, g2611, g2612, g2613, g2614, g2615,
    g2616, g2617, g2618, g2619, g2620, g2621, g2622, g2623, g2624, g2625, g2626, g2627, g2628,
    g2629, g2630, g2631, g2632, g2633, g2634, g2635, g2636, g2637, g2638, g2639, g2640, g2641,
    g2642, g2643, g2644, g2645, g2646, g2647, g2648, g2649, g2650, g2651, g2652, g2653, g2654,
    g2655, g2656, g2657, g2658, g2659, g2660, g2661, g2662, g2663, g2664, g2665, g2666, g2667,
    g2668, g2669, g2670, g2671, g2672, g2673, g2674, g2675, g2676, g2677, g2678, g2679, g2680,
    g2681, g2682⟩ := g
  have vn : σ (.n 2543) = gen ^ n := g2590.1.trans hwn
  -- n dominates every τ_t
  have hx : ∀ {t d : ℕ}, t < 6 → σ (.n d) = σ (.n 2543) * (σ (.n (27 + t)))⁻¹ →
      σ (.n d) = gen ^ (n - τ t) ∧ σ (.n (27 + t)) ≠ 0 := fun {t d} ht hg ↦ by
    rw [hkb t ht] at hg ⊢
    exact ⟨by rw [hg, vn, ← pow_sub₀ _ gen_ne_zero (hτ t ht)], pow_ne_zero _ gen_ne_zero⟩
  obtain ⟨x0, n0⟩ := hx (t := 0) (by norm_num) g2592
  obtain ⟨x1, n1⟩ := hx (t := 1) (by norm_num) g2596
  obtain ⟨x2, n2⟩ := hx (t := 2) (by norm_num) g2601
  obtain ⟨x3, n3⟩ := hx (t := 3) (by norm_num) g2606
  obtain ⟨x4, n4⟩ := hx (t := 4) (by norm_num) g2611
  obtain ⟨x5, n5⟩ := hx (t := 5) (by norm_num) g2616
  have rc2573 := z_rc (a := n - τ 0) (K := 32) (by omega) x0 (g2591.trans z_w32) g2593
    (hlow _ (by omega)) (hlow _ (by omega))
  have rc2577 := z_rc (a := n - τ 1) (K := 32) (by omega) x1 (g2595.trans z_w32) g2597
    (hlow _ (by omega)) (hlow _ (by omega))
  have rc2582 := z_rc (a := n - τ 2) (K := 32) (by omega) x2 (g2600.trans z_w32) g2602
    (hlow _ (by omega)) (hlow _ (by omega))
  have rc2587 := z_rc (a := n - τ 3) (K := 32) (by omega) x3 (g2605.trans z_w32) g2607
    (hlow _ (by omega)) (hlow _ (by omega))
  have rc2592 := z_rc (a := n - τ 4) (K := 32) (by omega) x4 (g2610.trans z_w32) g2612
    (hlow _ (by omega)) (hlow _ (by omega))
  have rc2597 := z_rc (a := n - τ 5) (K := 32) (by omega) x5 (g2615.trans z_w32) g2617
    (hlow _ (by omega)) (hlow _ (by omega))
  have m2572 := z_div (rd := rd) g2592 n0
  have m2576 := z_div (rd := rd) g2596 n1
  have m2581 := z_div (rd := rd) g2601 n2
  have m2586 := z_div (rd := rd) g2606 n3
  have m2591 := z_div (rd := rd) g2611 n4
  have m2596 := z_div (rd := rd) g2616 n5
  -- n ≤ m
  have x6 : σ (.n 2587) = gen ^ (m - n) := by
    rw [g2623, h9, vn, ← pow_sub₀ _ gen_ne_zero hnm]
  have rc2604 := z_rc (a := m - n) (K := 32) (by omega) x6 (g2622.trans z_w32) g2624
    (hlow _ (by omega)) (hlow _ (by omega))
  have m2603 := z_div (rd := rd) g2623 (by rw [vn]; exact pow_ne_zero _ gen_ne_zero)
  -- some τ_t is n
  have hz : σ (.n 2584) = 0 := by
    rw [g2619, g2614, g2609, g2604, g2599, g2594, g2598, g2603, g2608, g2613, g2618, vn,
      hkb 0 (by norm_num), hkb 1 (by norm_num), hkb 2 (by norm_num), hkb 3 (by norm_num),
      hkb 4 (by norm_num), hkb 5 (by norm_num)]
    obtain ⟨t, ht, hte⟩ := hτn
    interval_cases t <;> simp [hte, CharTwo.add_self_eq_zero]
  have a2601 : (Atom.assertEq (.n 2584) (.n 2585)).Holds rd σ := by
    show σ (.n 2584) + σ (.n 2585) = 0
    rw [hz, g2620, tb_word_zero, add_zero]
  -- the squeeze
  have hz0 : σ (.n 2592) = 0 := g2626.trans tb_word_zero
  have hz1' : σ (.n 2593) = 0 := g2627.trans tb_word_zero
  have hz2 : σ (.n 2594) = 0 := g2628.trans tb_word_zero
  have hz3 : σ (.n 2595) = 0 := g2629.trans tb_word_zero
  have hin : ([.n 1905, .n 1906, .n 2592, .n 2592, .n 2592, .n 2593, .n 2594, .n 2595, .n 1899,
      .n 1900, .n 1901, .n 1902, .n 1903] : List V).map σ = rateOf S.pend ++ S.cap := by
    rw [hSr, hSc]; simp [hz0, hz1', hz2, hz3]
  have k2630 : (Atom.keccak [.n 1905, .n 1906, .n 2592, .n 2592, .n 2592, .n 2593, .n 2594, .n 2595, .n 1899,
      .n 1900, .n 1901, .n 1902, .n 1903] (lyOuts 2596) false false).Holds rd σ := z_keccak gk
  obtain ⟨hPk, -⟩ := ly_keccak k2630
  rw [hin] at hPk
  have vξ : σ (.n 2596) = S.squeeze.1 := challengeT_value (s0 := .n 2596) (b := 2596) rfl (hPk 0 (by norm_num))
  have hcap0 : [σ (.n 2604), σ (.n 2605), σ (.n 2606), σ (.n 2607), σ (.n 2608)] =
      S.squeeze.2.cap := by
    rw [hPk 8 (by norm_num), hPk 9 (by norm_num), hPk 10 (by norm_num), hPk 11 (by norm_num),
      hPk 12 (by norm_num)]
    rfl
  have vT : σ (.n 2618) = zTarget σ S.squeeze.1 := by
    rw [g2640, g2638, g2636, g2637, g2639, g2635, g2634, g2633, g2632, g2631, tb_word_one, vξ,
      zTarget]
    ring
  -- the buffers
  set cap0 := S.squeeze.2.cap with hcap0d
  set cl0 := zTarget σ S.squeeze.1 with hcl0d
  have h5 : cap0.length = 5 := rfl
  have v2588 : σ (.n 2625) = w 2625 := g2647
  have v2591 : σ (.n 2628) = w 2628 := g2650
  have v2612 : σ (.n 2649) = w 2649 := g2680
  have r0 := zcRoundsW_reads h5 hR 0 (by omega)
  rw [Nat.mul_zero, pow_zero, mul_one, zcRecW, ← v2588] at r0
  simp only [zcRec, Nat.mul_zero, pow_zero, mul_one, ← hcap0, ← vT] at r0
  have v2593 : σ (.n 2630) = σ (.n 1896) * gen := by
    rw [g2657, g2656, tb_word_gen]
  have s2648 : (Atom.load (.n 2631) (.n 2628) 0).Holds rd σ := by
    show LoadHolds rd _ _ _
    rw [g2660, tb_word_one, v2591]
    simpa [zcCprodW] using hC 0 (by simp [zcCprodW])
  -- the rounds
  have v2596 : σ (.n 2633) = 1 + gen ^ n := by rw [g2663, g2662, tb_word_one, vn]
  have c2652 : VSH (coreProgram.Rel rd) rd σ
      (.callIf (.n 2633) name% «verify_tables_loop0» [.n 2634, .n 2543, .n 2625, .n 18, .n 16,
          .n 2543, .n 2628]) := by
    refine ⟨by rw [v2596]; exact isInK_add (by simpa using gen_pow_isInK 0) (gen_pow_isInK n),
      fun hne => ?_⟩
    have hn0 : 0 < n := by
      rcases Nat.eq_zero_or_pos n with rfl | h
      · exact absurd (by rw [v2596, pow_zero]; exact CharTwo.add_self_eq_zero 1) hne
      · exact h
    simp only [List.map_cons, List.map_nil]
    rw [g2664, tb_word_one, vn, v2588, v2591]
    exact l10_complete hn0 (zc_l10B h5 hR hC hchi hxs hxl)
  -- the last record
  have v2602 : σ (.n 2639) = w 2625 * gen ^ (7 * n) := by
    rw [g2670, g2669, g2668, g2667, g2666, vn, v2588]; ring
  have rn := zcRoundsW_reads h5 hR n le_rfl
  rw [zcRecW, ← v2602] at rn
  have hlen := zcRec_len (cl0 := cl0) (xs := xs) h5 n
  obtain ⟨e0, r2658⟩ := z_read g2671 (by decide +kernel) (rn 0 (by simp [hlen]))
  obtain ⟨e1, r2659⟩ := z_read g2672 (by decide +kernel) (rn 1 (by simp [hlen]))
  obtain ⟨e2, r2660⟩ := z_read g2673 (by decide +kernel) (rn 2 (by simp [hlen]))
  obtain ⟨e3, r2661⟩ := z_read g2674 (by decide +kernel) (rn 3 (by simp [hlen]))
  obtain ⟨e4, r2662⟩ := z_read g2675 (by decide +kernel) (rn 4 (by simp [hlen]))
  obtain ⟨e5, r2663⟩ := z_read g2676 (by decide +kernel) (rn 5 (by simp [hlen]))
  obtain ⟨e6, r2664⟩ := z_read g2677 (by decide +kernel) (rn 6 (by simp [hlen]))
  -- the equality prefix
  have c2669 : VSH (coreProgram.Rel rd) rd σ
      (.call "eq_prefix_chain" [.n 2649, .n 2650, .n 16, .n 699, .n 2543] []) := by
    show coreProgram.Rel rd _ _ _
    simp only [List.map_cons, List.map_nil]
    rw [g2681, tb_word_one, vn, v2612]
    refine (eq_prefix_chain_holds rd _ _).mpr ⟨rfl, z_rcd (by omega) (hlow _ (by omega))
      (hlow _ (by omega)), n, by omega, rfl, zcChis cap0 cl0 xs n, zs1.take n, by simp [zcChis],
      by simp; omega, hchi, fun k hk => by rw [List.getElem_take]; exact hz1 _ _, fun j hj => ?_⟩
    have := hP j (by simp; omega)
    simpa using this
  -- the statements
  have s2638 : (Atom.load (.n 2604) (.n 2625) 0).Holds rd σ := r0 0 (by simp)
  have s2639 : (Atom.load (.n 2605) (.n 2625) 1).Holds rd σ := r0 1 (by simp)
  have s2640 : (Atom.load (.n 2606) (.n 2625) 2).Holds rd σ := r0 2 (by simp)
  have s2641 : (Atom.load (.n 2607) (.n 2625) 3).Holds rd σ := r0 3 (by simp)
  have s2642 : (Atom.load (.n 2608) (.n 2625) 4).Holds rd σ := r0 4 (by simp)
  have s2645 : (Atom.load (.n 2630) (.n 2625) 5).Holds rd σ := by
    show LoadHolds rd _ _ _; rw [v2593]; exact r0 5 (by simp)
  have s2646 : (Atom.load (.n 2618) (.n 2625) 6).Holds rd σ := r0 6 (by simp)
  have hrest : ∀ s ∈ zRest, VSH (coreProgram.Rel rd) rd σ s := by
    intro s hs
    simp only [zRest, List.mem_cons, List.not_mem_nil, or_false] at hs
    obtain rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl := hs
    · exact m2572
    · exact rc2573
    · exact m2576
    · exact rc2577
    · exact m2581
    · exact rc2582
    · exact m2586
    · exact rc2587
    · exact m2591
    · exact rc2592
    · exact m2596
    · exact rc2597
    · exact a2601
    · exact m2603
    · exact rc2604
    · exact k2630
    · exact s2638
    · exact s2639
    · exact s2640
    · exact s2641
    · exact s2642
    · exact s2645
    · exact s2646
    · exact s2648
    · exact c2652
    · exact r2658
    · exact r2659
    · exact r2660
    · exact r2661
    · exact r2662
    · exact r2663
    · exact r2664
    · exact c2669
  refine ⟨hrest, vn, vξ, hcap0, vT, ?_, ?_, ?_, v2588, v2591, v2612, ?_, ?_, ?_⟩
  · rw [g2646, g2645, g2644, g2643, g2642, g2641, tb_word_gen, vn]; ring
  · rw [g2649, g2648, tb_word_gen, vn]; ring
  · rw [g2679, g2678, tb_word_gen, vn]; ring
  · change [σ (.n 2640), σ (.n 2641), σ (.n 2642), σ (.n 2643), σ (.n 2644)] =
      (zcRec cap0 cl0 xs n).1
    apply List.ext_getElem (by simp [hlen])
    intro k h1 h2
    simp only [List.length_cons, List.length_nil] at h1
    interval_cases k
    · rw [List.getElem_cons_zero, e0, List.getElem_append_left]
    · rw [List.getElem_cons_succ, List.getElem_cons_zero, e1, List.getElem_append_left]
    · rw [List.getElem_cons_succ, List.getElem_cons_succ, List.getElem_cons_zero, e2,
        List.getElem_append_left]
    · rw [List.getElem_cons_succ, List.getElem_cons_succ, List.getElem_cons_succ,
        List.getElem_cons_zero, e3, List.getElem_append_left]
    · rw [List.getElem_cons_succ, List.getElem_cons_succ, List.getElem_cons_succ,
        List.getElem_cons_succ, List.getElem_cons_zero, e4, List.getElem_append_left]
  · rw [e5, List.getElem_append_right (by omega)]; simp [hlen]
  · change σ (.n 2646) = (zcRec cap0 cl0 xs n).2
    rw [e6, List.getElem_append_right (by omega)]; simp [hlen]

end
end LeanVM.Guest.B1.Tables
