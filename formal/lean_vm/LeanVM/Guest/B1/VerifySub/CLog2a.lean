/-
  LeanVM.Guest.B1.VerifySub.CLog2a

  `verify_log2_ceil`'s honest valuation on a memory defined below `2^κ`, for its placed
  completeness.
-/

module

public import LeanVM.Guest.B1.VerifySub.CPlaced3

/-!
# `verify_log2_ceil`'s honest valuation, on any memory defined below `2^κ`

`vl_holds`: the body holds of a valuation iff its conditions do (`Log2.vl_unfold` for one
valuation). `vl_complete_low`: over the bits of `W` at `bits`, its prefix sums at `ps` and the
exponent tables, on a memory defined below `2^κ` (`κ ≥ 6`, where the two range checks read), the
honest valuation of `Log2.verify_log2_ceil_complete_aux` satisfies the body, returning
`g^max fl (log2Ceil W)` and `g^W`.
-/

namespace LeanVM.Guest.B1.VerifySub

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.Blake2sHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

theorem vl_holds {C : CallRel} {rd : Reader} (fl : ℕ) (σ : Val) (rets : List E) :
    Stmt.HoldsList C rd σ (vlBody fl) True (fun r => r = rets) ↔
      σ (.n 4) = 0 ∧ LoadHolds rd (σ (.n 3)) 0 (σ (.n 4)) ∧ (∀ j < 34, VlOk rd σ j) ∧
      σ (.n 410) = word (2 ^ 33) 0 0 ∧
      (LoadHolds rd (σ (.n 409)) 0 (σ (.n 412)) ∧ σ (.n 410) = σ (.n 409) * σ (.n 411) ∧
        LoadHolds rd (σ (.n 411)) 0 (σ (.n 413))) ∧
      σ (.n 414) = word (2 ^ 33) 0 0 ∧ σ (.n 415) = word (2 ^ fl) 0 0 ∧
      σ (.n 409) = σ (.n 416) * σ (.n 415) ∧
      (LoadHolds rd (σ (.n 416)) 0 (σ (.n 418)) ∧ σ (.n 414) = σ (.n 416) * σ (.n 417) ∧
        LoadHolds rd (σ (.n 417)) 0 (σ (.n 419))) ∧
      σ (.n 420) = σ (.n 3) * σ (.n 409) ∧ LoadHolds rd (σ (.n 420)) 0 (σ (.n 421)) ∧
      σ (.n 422) = σ (.n 421) + σ (.n 408) ∧ σ (.n 423) = σ (.n 422) * σ (.n 421) ∧
      σ (.n 424) = 0 ∧ σ (.n 423) + σ (.n 424) = 0 ∧
      σ (.n 425) = σ (.n 1) * σ (.n 409) ∧ LoadHolds rd (σ (.n 425)) 0 (σ (.n 426)) ∧
      σ (.n 427) = σ (.n 408) + σ (.n 426) ∧ σ (.n 428) = σ (.n 422) * σ (.n 427) ∧
      σ (.n 429) = 0 ∧ σ (.n 428) + σ (.n 429) = 0 ∧
      σ (.n 430) = word (2 ^ fl) 0 0 ∧ σ (.n 431) = σ (.n 409) + σ (.n 430) ∧
      (IsInK (σ (.n 431)) ∧ (σ (.n 431) ≠ 0 →
        σ (.n 432) = 1 ∧ σ (.n 433) = σ (.n 409) + σ (.n 432) ∧ IsInK (σ (.n 433)) ∧
        (σ (.n 433) ≠ 0 → σ (.n 434) = invGenWord ∧ σ (.n 435) = σ (.n 409) * σ (.n 434) ∧
          σ (.n 436) = σ (.n 3) * σ (.n 435) ∧ LoadHolds rd (σ (.n 436)) 0 (σ (.n 437)) ∧
          σ (.n 438) = invGenWord ∧ σ (.n 439) = σ (.n 409) * σ (.n 438) ∧
          σ (.n 440) = σ (.n 1) * σ (.n 439) ∧ LoadHolds rd (σ (.n 440)) 0 (σ (.n 441)) ∧
          σ (.n 442) = σ (.n 408) + σ (.n 441) ∧ σ (.n 443) = σ (.n 437) + σ (.n 408) ∧
          σ (.n 444) = σ (.n 443) * σ (.n 442) ∧ σ (.n 445) = 0 ∧
          σ (.n 446) = σ (.n 444) + σ (.n 445) ∧ σ (.n 448) = σ (.n 446) * σ (.n 447) ∧
          σ (.n 448) = 1))) ∧
      σ (.n 449) = σ (.n 409) ∧ σ (.n 450) = σ (.n 405) ∧ [σ (.n 449), σ (.n 450)] = rets := by
  rw [vlBody, vlTail]
  simp only [holdsList_append, Stmt.HoldsList]
  simp only [holds_ite_noRet (.n 431) [] vlMin rfl rfl]
  simp only [vlMin, Stmt.HoldsList]
  simp only [holds_ite_noRet (.n 433) [] vlMinIn rfl rfl]
  simp only [vlMinIn]
  simp only [holdsList_range_flatten 34 vlBlk (fun j => by cases j <;> rfl), holds_vlBlk,
    Stmt.HoldsList, Stmt.Holds, Atom.Holds, List.map_cons, List.map_nil, true_and, and_true,
    word_zero, word_one, implies_true]

theorem vl_complete_low {C : CallRel} (fl : ℕ) (hfl : fl < 34) {κ : ℕ} (hκ6 : 6 ≤ κ) {rd : Reader}
    (hlow : LowDef κ rd) {bits lp sq ps : E} (ht : ExpTables rd lp sq) {W : ℕ} (hW : W < 2 ^ 34)
    (hbits : ∀ j < 34, LoadHolds rd bits j (bitE (W.testBit j))) (hL : max fl (log2Ceil W) < 34)
    (hps : ∀ j ≤ 34, LoadHolds rd ps j (eOfNat (W % 2 ^ j))) :
    ∃ τ : Val, τ (.n 0) = bits ∧ τ (.n 1) = lp ∧ τ (.n 2) = sq ∧ τ (.n 3) = ps ∧
      τ (.n 409) = gen ^ max fl (log2Ceil W) ∧
      τ (.n 431) = gen ^ max fl (log2Ceil W) + word (2 ^ fl) 0 0 ∧
      τ (.n 433) = gen ^ max fl (log2Ceil W) + 1 ∧
      τ (.n 420) = ps * gen ^ max fl (log2Ceil W) ∧ τ (.n 425) = lp * gen ^ max fl (log2Ceil W) ∧
      τ (.n 436) = ps * (gen ^ max fl (log2Ceil W) * invGenWord) ∧
      τ (.n 440) = lp * (gen ^ max fl (log2Ceil W) * invGenWord) ∧
      Stmt.HoldsList C rd τ (vlBody fl) True
        (fun r => r = [gen ^ max fl (log2Ceil W), gen ^ W]) := by
  set L := max fl (log2Ceil W)
  have hW64 : W < 2 ^ 64 := lt_of_lt_of_le hW (by decide)
  obtain ⟨c1, c2, c3⟩ := verify_log2_ceil_complete (floor := fl) hW64 (by omega)
  have hK34 : 34 ≤ 2 ^ κ := le_trans (by decide) (Nat.pow_le_pow_right (by decide) hκ6)
  obtain ⟨r1a, r1b, r1c⟩ := rc_complete_low hlow (K := 34) (e := L) hK34 hL
  obtain ⟨r2a, r2b, r2c⟩ := rc_complete_low hlow (K := 34) (e := L - fl) hK34 (by omega)
  set y1 := (rcLow rd L 34).1
  set t1 := (rcLow rd L 34).2.1
  set t2 := (rcLow rd L 34).2.2
  set y2 := (rcLow rd (L - fl) 34).1
  set u1 := (rcLow rd (L - fl) 34).2.1
  set u2 := (rcLow rd (L - fl) 34).2.2
  set b := fun j => bitE (W.testBit j)
  set sv := fun j => (gen ^ 2 ^ j : E)
  set lo := eOfNat (W % 2 ^ L)
  set hi := lo + eOfNat W
  set lo' := eOfNat (W % 2 ^ (L - 1))
  set x := (lo' + eOfNat W) * (eOfNat W + eOfNat (2 ^ (L - 1)))
  set τ := setl (setv (setl (Val.ofArgs [bits, lp, sq]) 3 [ps, 0]) 5 404 (vlVals b sv 33)) 409
    [gen ^ L, word (2 ^ 33) 0 0, y1, t1, t2, word (2 ^ 33) 0 0, word (2 ^ fl) 0 0, gen ^ (L - fl),
      y2, u1, u2, ps * gen ^ L, lo, hi, hi * lo, 0, lp * gen ^ L, eOfNat (2 ^ L),
      eOfNat W + eOfNat (2 ^ L), hi * (eOfNat W + eOfNat (2 ^ L)), 0, word (2 ^ fl) 0 0,
      gen ^ L + word (2 ^ fl) 0 0, 1, gen ^ L + 1, invGenWord, gen ^ L * invGenWord,
      ps * (gen ^ L * invGenWord), lo', invGenWord, gen ^ L * invGenWord,
      lp * (gen ^ L * invGenWord), eOfNat (2 ^ (L - 1)), eOfNat W + eOfNat (2 ^ (L - 1)),
      lo' + eOfNat W, x, 0, x + 0, (x + 0)⁻¹, (x + 0) * (x + 0)⁻¹, gen ^ L, gen ^ W]
  have tv : ∀ i < 404, τ (.n (5 + i)) = vlVals b sv 33 i := fun i hi => by
    simp only [τ, setl, List.length_cons, List.length_nil]
    rw [set_n_lt (by omega), set_n_in (by omega) (by omega), Nat.add_sub_cancel_left]
  have t0 : ∀ i < 8, τ (.n (5 + i)) = [b 0, b 0 * b 0, 1, sv 0, 1, sv 0 + 1, b 0 * (sv 0 + 1),
      1 + b 0 * (sv 0 + 1)].getD i 0 := fun i hi => by rw [tv i (by omega), vlVals_zero _ _ _ _ hi]
  have ts : ∀ j c, j + 1 ≤ 33 → c < 12 → τ (.n (13 + 12 * j + c)) = [b (j + 1),
      b (j + 1) * b (j + 1), 1, sv (j + 1), 1, sv (j + 1) + 1, b (j + 1) * (sv (j + 1) + 1),
      1 + b (j + 1) * (sv (j + 1) + 1), gpwProd b sv (j + 2), word (2 ^ (j + 1)) 0 0,
      b (j + 1) * word (2 ^ (j + 1)) 0 0, ∑ t ∈ Finset.range (j + 2), b t * coordBasis t].getD c 0 :=
    fun j c hj hc => by
      rw [show 13 + 12 * j + c = 5 + (8 + 12 * j + c) by omega, tv _ (by omega),
        vlVals_succ _ _ _ _ _ hj hc]
  have tl : ∀ i < 42, τ (.n (409 + i)) = [gen ^ L, word (2 ^ 33) 0 0, y1, t1, t2, word (2 ^ 33) 0 0,
      word (2 ^ fl) 0 0, gen ^ (L - fl), y2, u1, u2, ps * gen ^ L, lo, hi, hi * lo, 0, lp * gen ^ L,
      eOfNat (2 ^ L), eOfNat W + eOfNat (2 ^ L), hi * (eOfNat W + eOfNat (2 ^ L)), 0,
      word (2 ^ fl) 0 0, gen ^ L + word (2 ^ fl) 0 0, 1, gen ^ L + 1, invGenWord,
      gen ^ L * invGenWord, ps * (gen ^ L * invGenWord), lo', invGenWord, gen ^ L * invGenWord,
      lp * (gen ^ L * invGenWord), eOfNat (2 ^ (L - 1)), eOfNat W + eOfNat (2 ^ (L - 1)),
      lo' + eOfNat W, x, 0, x + 0, (x + 0)⁻¹, (x + 0) * (x + 0)⁻¹, gen ^ L, gen ^ W].getD i 0 :=
    fun i hi => by
      simp only [τ, setl, List.length_cons, List.length_nil]
      rw [set_n_in (by omega) (by omega), Nat.add_sub_cancel_left]
  have hacc : ∀ j < 34, τ (.n (vlW j)) = ∑ t ∈ Finset.range (j + 1), b t * coordBasis t ∧
      τ (.n (vlE j)) = gpwProd b sv (j + 1) := fun j hj => by
    cases j with
    | zero =>
      refine ⟨?_, ?_⟩
      · have := t0 0 (by omega)
        rw [show (0 : ℕ) + 1 = 1 from rfl, Finset.sum_range_one, coordBasis, pow_zero,
          eOfNat192_of_lt (show (1 : ℕ) < 2 ^ 64 by decide), eOfNat_one, mul_one]
        exact this
      · have := t0 7 (by omega)
        rw [gpwProd, show (0 : ℕ) + 1 = 1 from rfl, Finset.prod_range_one]
        exact this
    | succ j =>
      rw [show vlW (j + 1) = 13 + 12 * j + 11 by simp only [vlW]; omega,
        show vlE (j + 1) = 13 + 12 * j + 8 by simp only [vlE]; omega]
      exact ⟨ts j 11 (by omega) (by omega), ts j 8 (by omega) (by omega)⟩
  have hbits' : ∀ j < 34, LoadHolds rd bits j (b j) := hbits
  have hsq : ∀ j < 34, LoadHolds rd sq j (sv j) := fun j hj => (ht j (by show j < 34; omega)).2
  have hX : τ (.n 408) = eOfNat W := by
    rw [show (408 : ℕ) = vlW 33 from rfl, (hacc 33 (by omega)).1, sum_bits_mod W 34 (by omega),
      Nat.mod_eq_of_lt hW]
  have hE : τ (.n 405) = gen ^ W := by
    rw [show (405 : ℕ) = vlE 33 from rfl, (hacc 33 (by omega)).2]
    exact gpwProd_pow (fun j _ => rfl) hW
  have e1 : τ (.n 1) = lp := by simp only [τ]; b1_look
  have e3 : τ (.n 3) = ps := by simp only [τ]; b1_look
  have x409 : τ (.n 409) = gen ^ L := tl 0 (by omega)
  have x410 : τ (.n 410) = word (2 ^ 33) 0 0 := tl 1 (by omega)
  have x411 : τ (.n 411) = y1 := tl 2 (by omega)
  have x412 : τ (.n 412) = t1 := tl 3 (by omega)
  have x413 : τ (.n 413) = t2 := tl 4 (by omega)
  have x414 : τ (.n 414) = word (2 ^ 33) 0 0 := tl 5 (by omega)
  have x415 : τ (.n 415) = word (2 ^ fl) 0 0 := tl 6 (by omega)
  have x416 : τ (.n 416) = gen ^ (L - fl) := tl 7 (by omega)
  have x417 : τ (.n 417) = y2 := tl 8 (by omega)
  have x418 : τ (.n 418) = u1 := tl 9 (by omega)
  have x419 : τ (.n 419) = u2 := tl 10 (by omega)
  have x420 : τ (.n 420) = ps * gen ^ L := tl 11 (by omega)
  have x421 : τ (.n 421) = lo := tl 12 (by omega)
  have x422 : τ (.n 422) = hi := tl 13 (by omega)
  have x423 : τ (.n 423) = hi * lo := tl 14 (by omega)
  have x424 : τ (.n 424) = 0 := tl 15 (by omega)
  have x425 : τ (.n 425) = lp * gen ^ L := tl 16 (by omega)
  have x426 : τ (.n 426) = eOfNat (2 ^ L) := tl 17 (by omega)
  have x427 : τ (.n 427) = eOfNat W + eOfNat (2 ^ L) := tl 18 (by omega)
  have x428 : τ (.n 428) = hi * (eOfNat W + eOfNat (2 ^ L)) := tl 19 (by omega)
  have x429 : τ (.n 429) = 0 := tl 20 (by omega)
  have x430 : τ (.n 430) = word (2 ^ fl) 0 0 := tl 21 (by omega)
  have x431 : τ (.n 431) = gen ^ L + word (2 ^ fl) 0 0 := tl 22 (by omega)
  have x432 : τ (.n 432) = 1 := tl 23 (by omega)
  have x433 : τ (.n 433) = gen ^ L + 1 := tl 24 (by omega)
  have x434 : τ (.n 434) = invGenWord := tl 25 (by omega)
  have x435 : τ (.n 435) = gen ^ L * invGenWord := tl 26 (by omega)
  have x436 : τ (.n 436) = ps * (gen ^ L * invGenWord) := tl 27 (by omega)
  have x437 : τ (.n 437) = lo' := tl 28 (by omega)
  have x438 : τ (.n 438) = invGenWord := tl 29 (by omega)
  have x439 : τ (.n 439) = gen ^ L * invGenWord := tl 30 (by omega)
  have x440 : τ (.n 440) = lp * (gen ^ L * invGenWord) := tl 31 (by omega)
  have x441 : τ (.n 441) = eOfNat (2 ^ (L - 1)) := tl 32 (by omega)
  have x442 : τ (.n 442) = eOfNat W + eOfNat (2 ^ (L - 1)) := tl 33 (by omega)
  have x443 : τ (.n 443) = lo' + eOfNat W := tl 34 (by omega)
  have x444 : τ (.n 444) = x := tl 35 (by omega)
  have x445 : τ (.n 445) = 0 := tl 36 (by omega)
  have x446 : τ (.n 446) = x + 0 := tl 37 (by omega)
  have x447 : τ (.n 447) = (x + 0)⁻¹ := tl 38 (by omega)
  have x448 : τ (.n 448) = (x + 0) * (x + 0)⁻¹ := tl 39 (by omega)
  have x449 : τ (.n 449) = gen ^ L := tl 40 (by omega)
  have x450 : τ (.n 450) = gen ^ W := tl 41 (by omega)
  have e0 : τ (.n 0) = bits := by simp only [τ]; b1_look
  have e2 : τ (.n 2) = sq := by simp only [τ]; b1_look
  have e4 : τ (.n 4) = 0 := by simp only [τ]; b1_look
  have x3 : τ (.n 3) = ps := e3
  refine ⟨τ, e0, e1, e2, x3, x409, x431, x433, x420, x425, x436, x440, (vl_holds fl τ _).mpr ⟨e4, by
      rw [e3, e4]; have := hps 0 (by omega); rwa [pow_zero, Nat.mod_one, eOfNat_zero] at this,
    fun j hj => ?_,
    x410, ⟨?_, ?_, ?_⟩, x414, x415, ?_, ⟨?_, ?_, ?_⟩, by rw [x420, e3, x409], ?_,
    by rw [x422, x421, hX], by rw [x423, x422, x421], x424, ?_, by rw [x425, e1, x409], ?_,
    by rw [x427, hX, x426], by rw [x428, x422, x427], x429, ?_, x430, by rw [x431, x409, x430],
    ⟨?_, fun h431 => ?_⟩, by rw [x449, x409], by rw [x450, hE], by rw [x449, x450]⟩⟩
  · cases j with
    | zero =>
      have f5 := t0 0 (by omega); have f6 := t0 1 (by omega); have f7 := t0 2 (by omega)
      have f8 := t0 3 (by omega); have f9 := t0 4 (by omega); have f10 := t0 5 (by omega)
      have f11 := t0 6 (by omega); have f12 := t0 7 (by omega)
      simp only [List.getD_cons_zero, List.getD_cons_succ, Nat.add_zero, Nat.reduceAdd]
        at f5 f6 f7 f8 f9 f10 f11 f12
      refine ⟨?_, by rw [f6, f5], ?_, f7, ?_, f9, by rw [f10, f8, f9], by rw [f11, f5, f10],
        by rw [f12, f7, f11], ?_⟩
      · rw [e0, f5]; exact hbits' 0 hj
      · rw [f6, f5]; simp only [b, bitE_mul_self]; exact e_add_self _
      · rw [e2, f8]; exact hsq 0 hj
      rw [e3, f5]
      have := hps 1 (by omega)
      rwa [show eOfNat (W % 2 ^ 1) = b 0 by
        rw [← sum_bits_mod W 1 (by omega), Finset.sum_range_one, coordBasis, pow_zero,
          eOfNat192_of_lt (show (1 : ℕ) < 2 ^ 64 by decide), eOfNat_one, mul_one]] at this
    | succ j =>
      have e := fun c (hc : c < 12) => ts j c (by omega) hc
      have f0 := e 0 (by omega); have f1 := e 1 (by omega); have f2 := e 2 (by omega)
      have f3 := e 3 (by omega); have f4 := e 4 (by omega); have f5 := e 5 (by omega)
      have f6 := e 6 (by omega); have f7 := e 7 (by omega); have f8 := e 8 (by omega)
      have f9 := e 9 (by omega); have f10 := e 10 (by omega); have f11 := e 11 (by omega)
      simp only [List.getD_cons_zero, List.getD_cons_succ,
        show ∀ k, 13 + 12 * j + k = k + 13 + 12 * j from fun k => by ring]
        at f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11
      obtain ⟨ha, hg⟩ := hacc j (by omega)
      refine ⟨?_, by rw [f1, f0], ?_, f2, ?_, f4, by rw [f5, f3, f4], by rw [f6, f0, f5],
        by rw [f7, f2, f6], ?_, f9, by rw [f10, f0, f9], ?_, ?_⟩
      · rw [e0, f0]; exact hbits' (j + 1) hj
      · rw [f1, f0]; simp only [b, bitE_mul_self]; exact e_add_self _
      · rw [e2, f3]; exact hsq (j + 1) hj
      · rw [f8, hg, f7, gpwProd, gpwProd, Finset.prod_range_succ (n := j + 1)]
      · rw [f11, ha, f10, Finset.sum_range_succ (n := j + 1), word_coordBasis (by omega)]
      · rw [e3, f11, sum_bits_mod W (j + 2) (by omega)]
        exact hps (j + 2) (by omega)
  · rw [x409, x412, gen_pow_eq_ofK]; exact r1a
  · rw [x410, x409, x411, word_two_pow_33, gen_pow_eq_ofK]; exact r1b
  · rw [x411, x413]; exact r1c
  · rw [x409, x416, x415, word_two_pow (by omega), ← pow_add, Nat.sub_add_cancel (le_max_left _ _)]
  · rw [x416, x418, gen_pow_eq_ofK]; exact r2a
  · rw [x414, x416, x417, word_two_pow_33, gen_pow_eq_ofK]; exact r2b
  · rw [x417, x419]; exact r2c
  · rw [x420, x421]
    rw [loadHolds_mul_gen_pow, Nat.add_zero]
    exact hps L (by omega)
  · rw [x423, x424, add_zero]; exact c1
  · rw [x425, x426, loadHolds_mul_gen_pow, Nat.add_zero]
    exact (ht L (by show L < 34; omega)).1
  · rw [x428, x429, add_zero]; exact c2
  · rw [x431, word_two_pow (by omega)]
    exact isInK_add (gen_pow_isInK _) (gen_pow_isInK _)
  · have hne : L ≠ fl := fun he => by
      rw [x431, he, word_two_pow (by omega)] at h431
      exact h431 (e_add_self _)
    refine ⟨x432, by rw [x433, x409, x432], ?_, fun h433 => ?_⟩
    · rw [x433]
      exact isInK_add (gen_pow_isInK _) (by rw [← pow_zero gen]; exact gen_pow_isInK 0)
    have h0 : L ≠ 0 := fun he => by
      rw [x433, he, pow_zero] at h433
      exact h433 (e_add_self _)
    obtain ⟨L', hL'⟩ : ∃ L', L = L' + 1 := ⟨L - 1, by omega⟩
    have hinv : gen ^ L * invGenWord = gen ^ L' := by rw [hL', gen_pow_mul_invGen]
    have hxne : x + 0 ≠ 0 := by rw [add_zero]; exact c3 hne h0
    have hm : (x + 0) * (x + 0)⁻¹ = 1 := e_mul_inv_cancel hxne
    refine ⟨x434, by rw [x435, x409, x434], by rw [x436, e3, x435], ?_, x438,
      by rw [x439, x409, x438], by rw [x440, e1, x439], ?_, by rw [x442, hX, x441],
      by rw [x443, x437, hX], by rw [x444, x443, x442], x445, by rw [x446, x444, x445],
      by rw [x448, x446, x447], by rw [x448]; exact hm⟩
    · rw [x436, x437, hinv, loadHolds_mul_gen_pow, Nat.add_zero]
      have := hps (L - 1) (by omega)
      rw [show L' = L - 1 by omega]
      exact this
    · rw [x440, x441, hinv, loadHolds_mul_gen_pow, Nat.add_zero, show L - 1 = L' by omega]
      exact (ht L' (by show L' < 34; omega)).1

end
end LeanVM.Guest.B1.VerifySub
