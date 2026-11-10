/-
  LeanVM.Guest.B1.Tables.VtC.ZSetup

  `verify_tables`' statements `2587 ..< 2688`, completely: the table sumcheck's round count, its
  batching challenge and target, its rounds and its equality prefix.
-/

module

public import LeanVM.Guest.B1.Tables.VtC.ZBase

/-!
# The table sumcheck's setup, completely (G:2369-2419)

Helpers for the honest valuation: a read of a word the memory holds (`z_read`), a product read
as a quotient (`z_div`), a passing range check (`z_rc`, `z_rcd`), a `KECCAK` of canonical cells
(`z_keccak`), `challenge_from_state` (`z_challenge`).
-/

namespace LeanVM.Guest.B1.Tables

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Guest.B1.Fwd

@[expose] public section

section Helpers
variable {rd : Reader} {σ : Val}

theorem z_canon_zero : IsCanonical128 (0 : E) := by
  rw [zero_eq_ofLimbs]; exact (isCanonical128_ofLimbs_iff _ _ _).mpr rfl

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

/-- **A `KECCAK` of canonical cells.** -/
theorem z_keccak {S : List Atom} {w : ℕ → E} {ins outs : List V} {i o : Bool}
    (hg : Good rd S w σ (.keccak ins outs i o)) (hc : AllCanonical (ins.map σ)) :
    (Atom.keccak ins outs i o).Holds rd σ := by
  refine holds_of_good hg fun c => ?_
  simp only [cells13, List.getD_eq_getElem?_getD]
  rcases h : (ins.map σ)[c.val]? with _ | x
  · exact z_canon_zero
  · exact hc x (List.mem_of_getElem? h)

theorem z_w32 : word 4294967296 0 = gen ^ 32 := by
  rw [show (4294967296 : ℕ) = 2 ^ 32 by norm_num, tb_word_two_pow (by norm_num)]

/-- **`challenge_from_state`'s atoms** on a canonical cell `s1`, by their equations. -/
theorem z_challenge {w : ℕ → E} {s0 s1 : V} {b : ℕ} (hg : GoodL rd w σ (challengeT s0 s1 b))
    (hc : IsCanonical128 (σ s1)) : ChallengeOk σ s0 s1 b := by
  simp only [challengeT, GoodL, GoodS, Good, fixNe] at hg
  obtain ⟨h0, h1, h2, h3, -, h5, h6, h7, -⟩ := hg
  rw [ite_pos' (by simp)] at h3 h6
  refine challengeOk_of_vals hc fun i hi => ?_
  have e0 : σ (.n b) = ofK ((σ s1).limb 0) := by
    have := h0 0 (by simp); simpa [limbAt] using this
  interval_cases i
  · exact e0
  · rw [h1, e0]; rfl
  · exact h2
  · rw [h3, h1, h2, e0]; rfl
  · exact h5
  · rw [h6, h5, e0]; rfl
  · rw [h7, h6, h5, e0]; rfl

end Helpers

/-- The bus target: `ξ²·T_0 + ξ³·T_1 + ξ⁴·T_2` on the sides' totals. -/
def zTarget (σ : Val) (ξ : E) : E :=
  ξ ^ 2 * σ (.n 1820) + ξ ^ 3 * σ (.n 2073) + ξ ^ 4 * σ (.n 2515)

/-- What statements `2587 ..< 2688` give: `g^n`, `ξ` (the squeeze of `S`), the sponge after it,
the target, the buffers' sizes and pointers, and the last record (the sponge, the cursor `3n`
words on, the final claim). -/
def ZOut (σ : Val) (w : ℕ → E) (S : Fs) (xs : List E) (n : ℕ) : Prop :=
  σ (.n 2516) = gen ^ n ∧ σ (.n 2588) = S.squeeze.1 ∧
    [σ (.n 2577), σ (.n 2578), σ (.n 2579), σ (.n 2580), σ (.n 2581)] = S.squeeze.2.cap ∧
    σ (.n 2598) = zTarget σ S.squeeze.1 ∧ σ (.n 2604) = gen ^ (7 * (n + 1)) ∧
    σ (.n 2607) = gen ^ (n + 1) ∧ σ (.n 2628) = gen ^ (n + 1) ∧ σ (.n 2605) = w 2605 ∧
    σ (.n 2608) = w 2608 ∧ σ (.n 2629) = w 2629 ∧
    [σ (.n 2620), σ (.n 2621), σ (.n 2622), σ (.n 2623), σ (.n 2624)] =
      (zcRec S.squeeze.2.cap (zTarget σ S.squeeze.1) xs n).1 ∧
    σ (.n 2625) = σ (.n 5) * gen ^ 5 * gen ^ (3 * n) ∧
    σ (.n 2626) = (zcRec S.squeeze.2.cap (zTarget σ S.squeeze.1) xs n).2

/-- The statements evaluation alone does not settle. -/
noncomputable def zRest : List Stmt := [
    .atom (.mul (.n 2516) (.n 2518) (.n 30)),
    .atom (.rangeCheck (.n 2518) (.n 2519) (.n 2520) (.n 2521) (.n 2517)),
    .atom (.mul (.n 2516) (.n 2524) (.n 31)),
    .atom (.rangeCheck (.n 2524) (.n 2525) (.n 2526) (.n 2527) (.n 2523)),
    .atom (.mul (.n 2516) (.n 2531) (.n 32)),
    .atom (.rangeCheck (.n 2531) (.n 2532) (.n 2533) (.n 2534) (.n 2530)),
    .atom (.mul (.n 2516) (.n 2538) (.n 33)),
    .atom (.rangeCheck (.n 2538) (.n 2539) (.n 2540) (.n 2541) (.n 2537)),
    .atom (.mul (.n 2516) (.n 2545) (.n 34)),
    .atom (.rangeCheck (.n 2545) (.n 2546) (.n 2547) (.n 2548) (.n 2544)),
    .atom (.mul (.n 2516) (.n 2552) (.n 35)),
    .atom (.rangeCheck (.n 2552) (.n 2553) (.n 2554) (.n 2555) (.n 2551)),
    .atom (.assertEq (.n 2557) (.n 2558)),
    .atom (.mul (.n 9) (.n 2560) (.n 2516)),
    .atom (.rangeCheck (.n 2560) (.n 2561) (.n 2562) (.n 2563) (.n 2559)),
    .atom (.keccak [.n 1905, .n 1907, .n 2565, .n 2565, .n 2565, .n 2566, .n 2567, .n 2568, .n 1893, .n 1894, .n 1895, .n 1896, .n 1897] [.n 2569, .n 2570, .n 2571, .n 2572, .n 2573, .n 2574, .n 2575, .n 2576, .n 2577, .n 2578, .n 2579, .n 2580, .n 2581] false false),
    .atom (.assertInK (.n 2582) (.n 2585)),
    .atom (.load (.n 2577) (.n 2605) 0),
    .atom (.load (.n 2578) (.n 2605) 1),
    .atom (.load (.n 2579) (.n 2605) 2),
    .atom (.load (.n 2580) (.n 2605) 3),
    .atom (.load (.n 2581) (.n 2605) 4),
    .atom (.load (.n 2610) (.n 2605) 5),
    .atom (.load (.n 2598) (.n 2605) 6),
    .atom (.load (.n 2611) (.n 2608) 0),
    .callIf (.n 2613) "__loop9" [.n 2614, .n 2516, .n 2605, .n 16, .n 2516, .n 2608],
    .atom (.load (.n 2620) (.n 2619) 0),
    .atom (.load (.n 2621) (.n 2619) 1),
    .atom (.load (.n 2622) (.n 2619) 2),
    .atom (.load (.n 2623) (.n 2619) 3),
    .atom (.load (.n 2624) (.n 2619) 4),
    .atom (.load (.n 2625) (.n 2619) 5),
    .atom (.load (.n 2626) (.n 2619) 6),
    .call "eq_prefix_chain" [.n 2629, .n 2630, .n 16, .n 703, .n 2516] []]

theorem z_slice_tail {P : Stmt → Prop} (h : ∀ s ∈ (vtPre.drop 2587).take 101, P s) :
    ∀ s ∈ (vtPre.drop 2589).take 99, P s := by
  intro s hs
  apply h
  rw [show (101 : ℕ) = 2 + 99 by rfl, List.take_add, List.drop_drop]
  exact List.mem_append_right _ hs

set_option maxRecDepth 100000 in
/-- **Statements `2587 ..< 2688`, completely** (G:2397-2447): the hinted `g^n` with `n` the
largest `τ_t` (at most `m = |point|`), the squeeze `ξ` of the sponge `S` after the bus words,
the target, the first record, `__loop9`'s rounds on the honest buffers (records, running
products, `chi`) and words `xs` at the cursor five on, the last record, `eq_prefix_chain` into
the prefix weights of `chi` against `zeta1`. -/
theorem vtZ_complete {rd : Reader} {w : ℕ → E} {args : List E} (hl : args.length = 20)
    {m n : ℕ} {τ : ℕ → ℕ} (hτ : ∀ t < 6, τ t ≤ n) (hτn : ∃ t < 6, τ t = n) (hnm : n ≤ m)
    (hm : m ≤ 32) (h9 : vtσ rd w args (.n 9) = gen ^ m)
    (hkb : ∀ t < 6, vtσ rd w args (.n (30 + t)) = gen ^ τ t)
    (hlow : ∀ i < 64, (rd (Parameters.addressOfIndex i)).isSome) (hwn : w 2516 = gen ^ n) {S : Fs}
    (hSr : rateOf S.pend = [vtσ rd w args (.n 1905), vtσ rd w args (.n 1907), 0, 0, 0, 0, 0, 0])
    (hSc : S.cap = [vtσ rd w args (.n 1893), vtσ rd w args (.n 1894), vtσ rd w args (.n 1895),
      vtσ rd w args (.n 1896), vtσ rd w args (.n 1897)])
    (hcan : AllCanonical (rateOf S.pend ++ S.cap)) {xs : List E} (hxl : xs.length = 3 * n)
    (hxs : TbReadsAt rd (vtσ rd w args (.n 5) * gen ^ 5) xs)
    (hR : TbReadsAt rd (w 2605) (zcRoundsW S.squeeze.2.cap (zTarget (vtσ rd w args) S.squeeze.1)
      (vtσ rd w args (.n 5) * gen ^ 5) xs n))
    (hC : TbReadsAt rd (w 2608)
      (zcCprodW S.squeeze.2.cap (zTarget (vtσ rd w args) S.squeeze.1) xs n))
    (hchi : TbReadsAt rd (vtσ rd w args (.n 16))
      (zcChis S.squeeze.2.cap (zTarget (vtσ rd w args) S.squeeze.1) xs n))
    {zs1 : List E} (hz1 : TbReadsAt rd (vtσ rd w args (.n 703)) zs1) (hz1l : n ≤ zs1.length)
    (hP : TbReadsAt rd (w 2629) ((List.range (n + 1)).map (prefixProd 1
      (zcChis S.squeeze.2.cap (zTarget (vtσ rd w args) S.squeeze.1) xs n) (zs1.take n)))) :
    (∀ s ∈ (vtPre.drop 2587).take 101, VSH (coreProgram.Rel rd) rd (vtσ rd w args) s) ∧
      ZOut (vtσ rd w args) w S xs n := by
  have g : GoodL rd w (vtσ rd w args) zBlk := vt_goodL hl 2587 zBlk zBlk_at
  have gk : Good rd vtSL w (vtσ rd w args) (.keccak [.n 1905, .n 1907, .n 2565, .n 2565, .n 2565,
      .n 2566, .n 2567, .n 2568, .n 1893, .n 1894, .n 1895, .n 1896, .n 1897] (lyOuts 2569) false
      false) := (vt_goodL (rd := rd) (w := w) hl 2627 [.atom (.keccak [.n 1905, .n 1907, .n 2565,
      .n 2565, .n 2565, .n 2566, .n 2567, .n 2568, .n 1893, .n 1894, .n 1895, .n 1896, .n 1897]
      (lyOuts 2569) false false)] (by decide +kernel)).1
  have gch : GoodL rd w (vtσ rd w args) (challengeT (.n 2569) (.n 2570) 2582) :=
    vt_goodL hl 2628 _ (by decide +kernel)
  have e := tbStmtsEqb_sound zBlk_at
  have hlen : zBlk.length = 101 := rfl
  suffices H : (∀ s ∈ zRest, VSH (coreProgram.Rel rd) rd (vtσ rd w args) s) ∧
      ZOut (vtσ rd w args) w S xs n by
    refine ⟨fun s hs => ?_, H.2⟩
    rw [← hlen, ← e] at hs
    exact vt_block hl 2587 zBlk zBlk_at zRest (by decide +kernel) H.1 s hs
  generalize vtσ rd w args = σ at *
  simp only [zBlk, GoodL, GoodS, Good, fixNe, List.forall_mem_cons, Nat.reduceLT, and_true,
    and_false, ↓reduceIte] at g
  obtain ⟨g2571, g2572, g2573, g2574, g2575, g2576, g2577, g2578, g2579, g2580, g2581, g2582,
    g2583, g2584, g2585, g2586, g2587, g2588, g2589, g2590, g2591, g2592, g2593, g2594, g2595,
    g2596, g2597, g2598, g2599, g2600, g2601, g2602, g2603, g2604, g2605, g2606, g2607, g2608,
    g2609, g2610, g2611, g2612, g2613, g2614, g2615, g2616, g2617, g2618, g2619, g2620, g2621,
    g2622, g2623, g2624, g2625, g2626, g2627, g2628, g2629, g2630, g2631, g2632, g2633, g2634,
    g2635, g2636, g2637, g2638, g2639, g2640, g2641, g2642, g2643, g2644, g2645, g2646, g2647,
    g2648, g2649, g2650, g2651, g2652, g2653, g2654, g2655, g2656, g2657, g2658, g2659, g2660,
    g2661, g2662, g2663, g2664, g2665, g2666, g2667, g2668, g2669, g2670, g2671⟩ := g
  have vn : σ (.n 2516) = gen ^ n := g2571.1.trans hwn
  -- n dominates every τ_t
  have hx : ∀ {t d : ℕ}, t < 6 → σ (.n d) = σ (.n 2516) * (σ (.n (30 + t)))⁻¹ →
      σ (.n d) = gen ^ (n - τ t) ∧ σ (.n (30 + t)) ≠ 0 := fun {t d} ht hg ↦ by
    rw [hkb t ht] at hg ⊢
    exact ⟨by rw [hg, vn, ← pow_sub₀ _ gen_ne_zero (hτ t ht)], pow_ne_zero _ gen_ne_zero⟩
  obtain ⟨x0, n0⟩ := hx (t := 0) (by norm_num) g2573
  obtain ⟨x1, n1⟩ := hx (t := 1) (by norm_num) g2577
  obtain ⟨x2, n2⟩ := hx (t := 2) (by norm_num) g2582
  obtain ⟨x3, n3⟩ := hx (t := 3) (by norm_num) g2587
  obtain ⟨x4, n4⟩ := hx (t := 4) (by norm_num) g2592
  obtain ⟨x5, n5⟩ := hx (t := 5) (by norm_num) g2597
  have rc2574 := z_rc (a := n - τ 0) (K := 32) (by omega) x0 (g2572.trans z_w32) g2574
    (hlow _ (by omega)) (hlow _ (by omega))
  have rc2578 := z_rc (a := n - τ 1) (K := 32) (by omega) x1 (g2576.trans z_w32) g2578
    (hlow _ (by omega)) (hlow _ (by omega))
  have rc2583 := z_rc (a := n - τ 2) (K := 32) (by omega) x2 (g2581.trans z_w32) g2583
    (hlow _ (by omega)) (hlow _ (by omega))
  have rc2588 := z_rc (a := n - τ 3) (K := 32) (by omega) x3 (g2586.trans z_w32) g2588
    (hlow _ (by omega)) (hlow _ (by omega))
  have rc2593 := z_rc (a := n - τ 4) (K := 32) (by omega) x4 (g2591.trans z_w32) g2593
    (hlow _ (by omega)) (hlow _ (by omega))
  have rc2598 := z_rc (a := n - τ 5) (K := 32) (by omega) x5 (g2596.trans z_w32) g2598
    (hlow _ (by omega)) (hlow _ (by omega))
  have m2573 := z_div (rd := rd) g2573 n0
  have m2577 := z_div (rd := rd) g2577 n1
  have m2582 := z_div (rd := rd) g2582 n2
  have m2587 := z_div (rd := rd) g2587 n3
  have m2592 := z_div (rd := rd) g2592 n4
  have m2597 := z_div (rd := rd) g2597 n5
  -- n ≤ m
  have x6 : σ (.n 2560) = gen ^ (m - n) := by
    rw [g2604, h9, vn, ← pow_sub₀ _ gen_ne_zero hnm]
  have rc2605 := z_rc (a := m - n) (K := 32) (by omega) x6 (g2603.trans z_w32) g2605
    (hlow _ (by omega)) (hlow _ (by omega))
  have m2604 := z_div (rd := rd) g2604 (by rw [vn]; exact pow_ne_zero _ gen_ne_zero)
  -- some τ_t is n
  have hz : σ (.n 2557) = 0 := by
    rw [g2600, g2595, g2590, g2585, g2580, g2575, g2579, g2584, g2589, g2594, g2599, vn,
      hkb 0 (by norm_num), hkb 1 (by norm_num), hkb 2 (by norm_num), hkb 3 (by norm_num),
      hkb 4 (by norm_num), hkb 5 (by norm_num)]
    obtain ⟨t, ht, hte⟩ := hτn
    interval_cases t <;> simp [hte, CharTwo.add_self_eq_zero]
  have a2602 : (Atom.assertEq (.n 2557) (.n 2558)).Holds rd σ := by
    show σ (.n 2557) + σ (.n 2558) = 0
    rw [hz, g2601, tb_word_zero, add_zero]
  -- the squeeze
  have hz0 : σ (.n 2565) = 0 := g2607.trans tb_word_zero
  have hz1' : σ (.n 2566) = 0 := g2608.trans tb_word_zero
  have hz2 : σ (.n 2567) = 0 := g2609.trans tb_word_zero
  have hz3 : σ (.n 2568) = 0 := g2610.trans tb_word_zero
  have hin : ([.n 1905, .n 1907, .n 2565, .n 2565, .n 2565, .n 2566, .n 2567, .n 2568, .n 1893,
      .n 1894, .n 1895, .n 1896, .n 1897] : List V).map σ = rateOf S.pend ++ S.cap := by
    rw [hSr, hSc]; simp [hz0, hz1', hz2, hz3]
  have k2611 : (Atom.keccak [.n 1905, .n 1907, .n 2565, .n 2565, .n 2565, .n 2566, .n 2567,
      .n 2568, .n 1893, .n 1894, .n 1895, .n 1896, .n 1897] (lyOuts 2569) false false).Holds rd σ :=
    z_keccak gk (by rw [hin]; exact hcan)
  obtain ⟨-, hPk, -⟩ := ly_keccak k2611
  rw [hin] at hPk
  have hch : ChallengeOk σ (.n 2569) (.n 2570) 2582 :=
    z_challenge gch
      (by rw [hPk 1 (by norm_num)]; exact cellsOfState_canonical _ _ _)
  have vξ : σ (.n 2588) = S.squeeze.1 :=
    challengeT_value hch (hPk 0 (by norm_num)) (hPk 1 (by norm_num))
  have hcap0 : [σ (.n 2577), σ (.n 2578), σ (.n 2579), σ (.n 2580), σ (.n 2581)] =
      S.squeeze.2.cap := by
    rw [hPk 8 (by norm_num), hPk 9 (by norm_num), hPk 10 (by norm_num), hPk 11 (by norm_num),
      hPk 12 (by norm_num)]
    rfl
  have vT : σ (.n 2598) = zTarget σ S.squeeze.1 := by
    rw [g2629, g2627, g2625, g2626, g2628, g2624, g2623, g2622, g2621, g2620, tb_word_one, vξ,
      zTarget]
    ring
  -- the buffers
  set cap0 := S.squeeze.2.cap with hcap0d
  set cl0 := zTarget σ S.squeeze.1 with hcl0d
  have h5 : cap0.length = 5 := rfl
  have hcan0 : AllCanonical cap0 := tb_capOf_canonical _
  have v2589 : σ (.n 2605) = w 2605 := g2636
  have v2592 : σ (.n 2608) = w 2608 := g2639
  have v2613 : σ (.n 2629) = w 2629 := g2669
  have r0 := zcRoundsW_reads h5 hR 0 (by omega)
  rw [Nat.mul_zero, pow_zero, mul_one, zcRecW, ← v2589] at r0
  simp only [zcRec, Nat.mul_zero, pow_zero, mul_one, ← hcap0, ← vT] at r0
  have v2594 : σ (.n 2610) = σ (.n 5) * gen ^ 5 := by
    rw [g2646, g2645, show (32 : ℕ) = 2 ^ 5 by norm_num, tb_word_two_pow (by norm_num)]
  have s2650 : (Atom.load (.n 2611) (.n 2608) 0).Holds rd σ := by
    show LoadHolds rd _ _ _
    rw [g2649, tb_word_one, v2592]
    simpa [zcCprodW] using hC 0 (by simp [zcCprodW])
  -- the rounds
  have v2597 : σ (.n 2613) = 1 + gen ^ n := by rw [g2652, g2651, tb_word_one, vn]
  have c2654 : VSH (coreProgram.Rel rd) rd σ
      (.callIf (.n 2613) "__loop9" [.n 2614, .n 2516, .n 2605, .n 16, .n 2516, .n 2608]) := by
    refine ⟨by rw [v2597]; exact isInK_add (by simpa using gen_pow_isInK 0) (gen_pow_isInK n),
      fun hne => ?_⟩
    have hn0 : 0 < n := by
      rcases Nat.eq_zero_or_pos n with rfl | h
      · exact absurd (by rw [v2597, pow_zero]; exact CharTwo.add_self_eq_zero 1) hne
      · exact h
    simp only [List.map_cons, List.map_nil]
    rw [g2653, tb_word_one, vn, v2589, v2592]
    exact l10_complete hn0 (zc_l10B h5 hcan0 hR hC hchi hxs hxl)
  -- the last record
  have v2603 : σ (.n 2619) = w 2605 * gen ^ (7 * n) := by
    rw [g2659, g2658, g2657, g2656, g2655, vn, v2589]; ring
  have rn := zcRoundsW_reads h5 hR n le_rfl
  rw [zcRecW, ← v2603] at rn
  have hlen := zcRec_len (cl0 := cl0) (xs := xs) h5 n
  obtain ⟨e0, r2660⟩ := z_read g2660 (by decide +kernel) (rn 0 (by simp [hlen]))
  obtain ⟨e1, r2661⟩ := z_read g2661 (by decide +kernel) (rn 1 (by simp [hlen]))
  obtain ⟨e2, r2662⟩ := z_read g2662 (by decide +kernel) (rn 2 (by simp [hlen]))
  obtain ⟨e3, r2663⟩ := z_read g2663 (by decide +kernel) (rn 3 (by simp [hlen]))
  obtain ⟨e4, r2664⟩ := z_read g2664 (by decide +kernel) (rn 4 (by simp [hlen]))
  obtain ⟨e5, r2665⟩ := z_read g2665 (by decide +kernel) (rn 5 (by simp [hlen]))
  obtain ⟨e6, r2666⟩ := z_read g2666 (by decide +kernel) (rn 6 (by simp [hlen]))
  -- the equality prefix
  have c2671 : VSH (coreProgram.Rel rd) rd σ
      (.call "eq_prefix_chain" [.n 2629, .n 2630, .n 16, .n 703, .n 2516] []) := by
    show coreProgram.Rel rd _ _ _
    simp only [List.map_cons, List.map_nil]
    rw [g2670, tb_word_one, vn, v2613]
    refine (eq_prefix_chain_holds rd _ _).mpr ⟨rfl, z_rcd (by omega) (hlow _ (by omega))
      (hlow _ (by omega)), n, by omega, rfl, zcChis cap0 cl0 xs n, zs1.take n, by simp [zcChis],
      by simp; omega, hchi, tbReadsAt_take hz1 n, fun j hj => ?_⟩
    have := hP j (by simp; omega)
    simpa using this
  -- the statements
  have i2616 : (Atom.assertInK (.n 2582) (.n 2585)).Holds rd σ := ⟨hch.2.2.2.1, hch.2.2.2.2.1⟩
  have s2640 : (Atom.load (.n 2577) (.n 2605) 0).Holds rd σ := r0 0 (by simp)
  have s2641 : (Atom.load (.n 2578) (.n 2605) 1).Holds rd σ := r0 1 (by simp)
  have s2642 : (Atom.load (.n 2579) (.n 2605) 2).Holds rd σ := r0 2 (by simp)
  have s2643 : (Atom.load (.n 2580) (.n 2605) 3).Holds rd σ := r0 3 (by simp)
  have s2644 : (Atom.load (.n 2581) (.n 2605) 4).Holds rd σ := r0 4 (by simp)
  have s2647 : (Atom.load (.n 2610) (.n 2605) 5).Holds rd σ := by
    show LoadHolds rd _ _ _; rw [v2594]; exact r0 5 (by simp)
  have s2648 : (Atom.load (.n 2598) (.n 2605) 6).Holds rd σ := r0 6 (by simp)
  have hrest : ∀ s ∈ zRest, VSH (coreProgram.Rel rd) rd σ s := by
    intro s hs
    simp only [zRest, List.mem_cons, List.not_mem_nil, or_false] at hs
    obtain rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl := hs
    · exact m2573
    · exact rc2574
    · exact m2577
    · exact rc2578
    · exact m2582
    · exact rc2583
    · exact m2587
    · exact rc2588
    · exact m2592
    · exact rc2593
    · exact m2597
    · exact rc2598
    · exact a2602
    · exact m2604
    · exact rc2605
    · exact k2611
    · exact i2616
    · exact s2640
    · exact s2641
    · exact s2642
    · exact s2643
    · exact s2644
    · exact s2647
    · exact s2648
    · exact s2650
    · exact c2654
    · exact r2660
    · exact r2661
    · exact r2662
    · exact r2663
    · exact r2664
    · exact r2665
    · exact r2666
    · exact c2671
  refine ⟨hrest, vn, vξ, hcap0, vT, ?_, ?_, ?_, v2589, v2592, v2613, ?_, ?_, ?_⟩
  · rw [g2635, g2634, g2633, g2632, g2631, g2630, tb_word_gen, vn]; ring
  · rw [g2638, g2637, tb_word_gen, vn]; ring
  · rw [g2668, g2667, tb_word_gen, vn]; ring
  · change [σ (.n 2620), σ (.n 2621), σ (.n 2622), σ (.n 2623), σ (.n 2624)] =
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
  · change σ (.n 2626) = (zcRec cap0 cl0 xs n).2
    rw [e6, List.getElem_append_right (by omega)]; simp [hlen]

end
end LeanVM.Guest.B1.Tables
