/-
  LeanVM.Guest.B1.Sig.SphincsBodyComplete

  The pieces of `verify_sig_lean_sphincs` around the forest are complete: the prologue, the
  codeword lanes and the digest's assertions, the counter and the encoding hash.
-/

module

public import LeanVM.Guest.B1.Sig.SphincsBody
public import LeanVM.Guest.B1.Sig.SphincsCoordComplete

namespace LeanVM.Guest.B1.Sig

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.Blake2sHash
open LeanVM.Protocol.Verifier LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Value

@[expose] public section

variable {C : CallRel} {rd : Reader}

/-! ## The prologue -/

theorem shifts_below_gen (bitBase n outBase : Nat) (hn : 0 < n) (hlt : bitBase + n ≤ outBase) :
    NumBelow (outBase + 3 * (n - 1) + 1) (Stmt.valsList (shifts bitBase n outBase)) := fun v hv => by
  rw [shifts_eq] at hv
  simp only [valsList_cons, Stmt.vals, Atom.vals, List.cons_append, List.nil_append, List.mem_cons] at hv
  rcases hv with rfl | rfl | hv
  · exact ⟨outBase, by omega, rfl⟩
  · exact ⟨bitBase + n - 1, by omega, rfl⟩
  · exact numBelow_valsList_flatMap _ _ (fun j hj => by
      simp only [List.mem_range] at hj
      simp only [shiftBlock, cst, addS, mulS, valsList_cons, valsList_nil, Stmt.vals, Atom.vals,
        List.cons_append, List.nil_append, List.append_nil]
      exact .cons ⟨_, by omega, rfl⟩ (.cons ⟨_, by omega, rfl⟩ (.cons ⟨_, by omega, rfl⟩
        (.cons ⟨_, by omega, rfl⟩ (.cons ⟨_, by omega, rfl⟩ (.cons ⟨_, by omega, rfl⟩
        (.cons ⟨_, by omega, rfl⟩ (.nil _)))))))) v hv

/-- The prologue's first statements, up to the index's bits. -/
def sPro1 : List Stmt :=
  [.atom (.load (.n 1) (.n 0) 1), cst 2 (mdw 48 true), cst 3 (mdw 64 true), cst 4 (word (tw 12) 0 0),
    .atom (.load (.n 5) (.n 0) 2), .atom (.load (.n 6) (.n 0) 3), cst 7 iv0, cst 8 iv1,
    cst 9 (mdw 64 false), b2s (.n 1) (.n 4) (.n 5) (.n 6) (.n 7) (.n 8) (.n 10) (.n 11) (.n 9),
    hintW "sp_rand" [.n 12], cst 13 (word 0 0 0), cst 14 (word 0 0 0), cst 15 (word 0 0 0),
    cst 16 (mdw 80 true), b2s (.n 12) (.n 13) (.n 14) (.n 15) (.n 10) (.n 11) (.n 17) (.n 18) (.n 16),
    .atom (.hint (.bits (.n 18) 0 26 (.stack ((List.range 26).map fun j => .n (19 + j)))))]

theorem sPro1_below : NumBelow 67 (Stmt.valsList sPro1) := by
  simp only [sPro1, hintW, cst, b2s, valsList_cons, valsList_nil, Stmt.vals, Atom.vals, Hint.vals, Dest.vals,
    List.append_nil, List.cons_append, List.nil_append, List.map_cons, List.map_nil, List.range_succ,
    List.range_zero]
  repeat (first | exact .nil _ | (refine .cons ⟨_, ?_, rfl⟩ ?_; omega))

/-- **The prologue's first statements are complete**, with the bits of `N` and `U` preset. -/
theorem sPro1_complete {σ : Val} {pp m0 m1 rho : E} (hl1 : LoadHolds rd (σ (.n 0)) 1 pp)
    (hl2 : LoadHolds rd (σ (.n 0)) 2 m0) (hl3 : LoadHolds rd (σ (.n 0)) 3 m1) (hpp : IsCanonical128 pp)
    (hm0 : IsCanonical128 m0) (hm1 : IsCanonical128 m1) (hrho : IsCanonical128 rho) (N U : Nat) :
    Completes C rd 1 67 sPro1 σ (fun σ' =>
      σ' (.n 1) = pp ∧ σ' (.n 2) = mdw 48 true ∧ σ' (.n 3) = mdw 64 true ∧ σ' (.n 5) = m0 ∧ σ' (.n 6) = m1 ∧
      σ' (.n 12) = rho ∧ (σ' (.n 17), σ' (.n 18)) = hcell [pp, word (tw 12) 0 0, m0, m1, rho] ∧
      (∀ j < 26, σ' (.n (19 + j)) = bitE (N.testBit j)) ∧ (∀ j < 22, σ' (.n (45 + j)) = bitE (U.testBit j)) ∧
      AgreeBelow 1 σ σ') := by
  set A := word (tw 12) 0 0
  set x := hmid ![pp, A, m0, m1]
  set o := hb (blockBytes ![pp, A, m0, m1] ++ [rho].flatMap cellBytes)
  set vs : List E := [pp, mdw 48 true, mdw 64 true, A, m0, m1, iv0, iv1, mdw 64 false, x.1, x.2, rho, 0, 0, 0,
    mdw 80 true, o.1, o.2]
  set g : Nat → E := fun k => if k < 18 then vs.getD k 0 else if k < 44 then bitE (N.testBit (k - 18))
    else bitE (U.testBit (k - 44))
  set σ' := upds σ ((List.range 66).map fun k => (1 + k, g k))
  have he : Ext 1 67 σ σ' := upds_ext σ _ (by simp; omega)
  have v : ∀ k < 66, σ' (.n (1 + k)) = g k := upds_range_at 1 _ 66 σ
  have v' : ∀ k, 1 ≤ k → k < 19 → σ' (.n k) = vs.getD (k - 1) 0 := fun k h1 h2 => by
    have := v (k - 1) (by omega); rw [show 1 + (k - 1) = k by omega] at this; rw [this]; simp [g, show k - 1 < 18 by omega]
  have h0 : σ' (.n 0) = σ (.n 0) := (he.agree 0 (by omega)).symm
  have hr : ([rho].flatMap cellBytes).length = 16 := by rw [length_flatMap_cellBytes']; rfl
  have hcmp := (compress_two_iff (b0 := ![pp, A, m0, m1]) (b1 := ![rho, 0, 0, 0]) (x0 := x.1) (x1 := x.2)
    (o0 := o.1) (o1 := o.2) (blockBytes_one rho) (by rw [hr]; omega) (by rw [hr]; omega)).mpr
    ⟨fin4_canonical.mpr ⟨hpp, isCanonical128_word _ _, hm0, hm1⟩,
      fin4_canonical.mpr ⟨hrho, isCanonical128_zero, isCanonical128_zero, isCanonical128_zero⟩, rfl, rfl⟩
  rw [hr] at hcmp
  refine ⟨σ', he, ⟨v' 1 le_rfl (by omega), v' 2 (by omega) (by omega), v' 3 (by omega) (by omega),
    v' 5 (by omega) (by omega), v' 6 (by omega) (by omega), v' 12 (by omega) (by omega), ?_, fun j hj => ?_,
    fun j hj => ?_, he.agree⟩, fun next kret hn => ?_⟩
  · rw [v' 17 (by omega) (by omega), v' 18 (by omega) (by omega)]
    show (o.1, o.2) = _
    simp only [o, blockBytes_four, hcell, ← List.flatMap_append]
    rfl
  · rw [show 19 + j = 1 + (18 + j) by omega, v _ (by omega)]
    simp [g, show ¬ (18 + j < 18) by omega, show 18 + j < 44 by omega]
  · rw [show 45 + j = 1 + (44 + j) by omega, v _ (by omega)]
    simp [g, show ¬ (44 + j < 18) by omega, show ¬ (44 + j < 44) by omega]
  · simp only [sPro1, hintW, cst, b2s, holdsList_cons_atom, holdsList_nil, Atom.Holds, true_and]
    rw [h0, v' 1 le_rfl (by omega), v' 2 (by omega) (by omega), v' 3 (by omega) (by omega),
      v' 4 (by omega) (by omega), v' 5 (by omega) (by omega), v' 6 (by omega) (by omega), v' 7 (by omega) (by omega),
      v' 8 (by omega) (by omega), v' 9 (by omega) (by omega), v' 10 (by omega) (by omega),
      v' 11 (by omega) (by omega), v' 12 (by omega) (by omega), v' 13 (by omega) (by omega),
      v' 14 (by omega) (by omega), v' 15 (by omega) (by omega), v' 16 (by omega) (by omega),
      v' 17 (by omega) (by omega), v' 18 (by omega) (by omega)]
    simp only [vs, List.getD_cons_succ, List.getD_cons_zero, Nat.sub_self, Nat.add_one_sub_one,
      show (3 : Nat) - 1 = 2 from rfl, word_zero]
    obtain ⟨hc1, hc2⟩ := hcmp
    refine ⟨hl1, ?_, ?_, ?_, hl2, hl3, ?_, ?_, ?_, hc1, ?_, ?_, ?_, ?_, hc2, hn⟩ <;> trivial

/-- **The prologue is complete**: from the claim's words, a randomizer, and the index and unused
bits `N`, `U` in range. -/
theorem sPrologue_complete {σ : Val} {pp m0 m1 rho : E} (hl1 : LoadHolds rd (σ (.n 0)) 1 pp)
    (hl2 : LoadHolds rd (σ (.n 0)) 2 m0) (hl3 : LoadHolds rd (σ (.n 0)) 3 m1) (hpp : IsCanonical128 pp)
    (hm0 : IsCanonical128 m0) (hm1 : IsCanonical128 m1) (hrho : IsCanonical128 rho) {N U : Nat} (hN : N < 2 ^ 26)
    (hU : U < 2 ^ 22) :
    Completes C rd 1 210 sPrologue σ (fun σ' =>
      SPre σ' N U ∧ σ' (.n 1) = pp ∧ σ' (.n 5) = m0 ∧ σ' (.n 6) = m1 ∧ σ' (.n 12) = rho ∧
      (σ' (.n 17), σ' (.n 18)) = hcell [pp, word (tw 12) 0 0, m0, m1, rho] ∧ AgreeBelow 1 σ σ') := by
  rw [sPrologue_eq, show [.atom (.load (.n 1) (.n 0) 1), cst 2 (mdw 48 true), cst 3 (mdw 64 true),
      cst 4 (word (tw 12) 0 0), .atom (.load (.n 5) (.n 0) 2), .atom (.load (.n 6) (.n 0) 3), cst 7 iv0, cst 8 iv1,
      cst 9 (mdw 64 false), b2s (.n 1) (.n 4) (.n 5) (.n 6) (.n 7) (.n 8) (.n 10) (.n 11) (.n 9),
      hintW "sp_rand" [.n 12], cst 13 (word 0 0 0), cst 14 (word 0 0 0), cst 15 (word 0 0 0),
      cst 16 (mdw 80 true), b2s (.n 12) (.n 13) (.n 14) (.n 15) (.n 10) (.n 11) (.n 17) (.n 18) (.n 16),
      .atom (.hint (.bits (.n 18) 0 26 (.stack ((List.range 26).map fun j => .n (19 + j)))))] = sPro1 from rfl]
  refine Completes.append (m := 67) (by omega) (by omega) sPro1_below
    (sPro1_complete hl1 hl2 hl3 hpp hm0 hm1 hrho N U) fun σ1 _ ⟨h1, h2, h3, h5, h6, h12, hd, hbN, hbU, hag1⟩ => ?_
  refine Completes.append_holds ((valsList_booleans 19 26).mono (by omega)) (fun next kret hn =>
    (booleans_iff 19 26).mpr ⟨fun j hj => by rw [hbN j hj]; exact bitE_mul_self _, hn⟩) ?_
  refine Completes.hint_cons _ ?_
  refine Completes.append_holds ((valsList_booleans 45 22).mono (by omega)) (fun next kret hn =>
    (booleans_iff 45 22).mpr ⟨fun j hj => by rw [hbU j hj]; exact bitE_mul_self _, hn⟩) ?_
  refine Completes.append (m := 143) (by omega) (by omega) (shifts_below_gen 19 26 67 (by omega) (by omega))
    (shifts_complete (C := C) (rd := rd) (by omega) (by omega) hN (by omega) hbN) fun σ2 _ ⟨hs2, hag2⟩ => ?_
  have hbU2 : ∀ j < 22, σ2 (.n (45 + j)) = bitE (U.testBit j) := fun j hj => by
    rw [← hag2 _ (by omega)]; exact hbU j hj
  refine Completes.append (m := 207) (by omega) (by omega) (shifts_below_gen 45 22 143 (by omega) (by omega))
    (shifts_complete (C := C) (rd := rd) (by omega) (by omega) hU (by omega) hbU2) fun σ3 _ ⟨hs3, hag3⟩ => ?_
  have hk3 : ∀ k < 67, σ3 (.n k) = σ1 (.n k) := fun k hk => ((hag2 k (by omega)).trans (hag3 k (by omega))).symm
  have h142 : σ3 (.n 142) = eOfNat N := by
    have := hs2 25 (by omega); rw [show 67 + 3 * 25 = 142 from rfl, show 26 - 1 - 25 = 0 from rfl, pow_zero,
      Nat.div_one] at this; rw [← hag3 _ (by omega)]; exact this
  have h206 : σ3 (.n 206) = eOfNat U := by
    have := hs3 21 (by omega); rwa [show 143 + 3 * 21 = 206 from rfl, show 22 - 1 - 21 = 0 from rfl, pow_zero,
      Nat.div_one] at this
  set σ4 := Function.update σ3 (.n 207) (word 0 (2 ^ 42) 0)
  set σ5 := Function.update σ4 (.n 208) (eOfNat U * word 0 (2 ^ 42) 0)
  set σ6 := Function.update σ5 (.n 209) (eOfNat N + lit (U * 2 ^ 106))
  have ne : ∀ a b : Nat, a ≠ b → (V.n a) ≠ V.n b := fun a b h e => h (by simp only [V.mk.injEq] at e; exact e.2.2)
  refine Completes.atom_cons (word 0 (2 ^ 42) 0) (by omega) (.cons ⟨207, by omega, rfl⟩ (.nil _))
    (Function.update_self _ _ _) ?_
  refine Completes.atom_cons (eOfNat U * word 0 (2 ^ 42) 0) (by omega)
    (.cons ⟨208, by omega, rfl⟩ (.cons ⟨206, by omega, rfl⟩ (.cons ⟨207, by omega, rfl⟩ (.nil _)))) ?_ ?_
  · show σ5 (.n 208) = σ5 (.n 206) * σ5 (.n 207)
    simp only [σ5, σ4, Function.update_self, Function.update_of_ne (ne _ _ (show 206 ≠ 208 by omega)),
      Function.update_of_ne (ne _ _ (show 206 ≠ 207 by omega)), Function.update_of_ne (ne _ _ (show 207 ≠ 208 by omega)),
      h206]
  refine Completes.atom_cons (eOfNat N + lit (U * 2 ^ 106)) (by omega)
    (.cons ⟨209, by omega, rfl⟩ (.cons ⟨142, by omega, rfl⟩ (.cons ⟨208, by omega, rfl⟩ (.nil _)))) ?_
    (Completes.nil _ _ _ ?_)
  · show σ6 (.n 209) = σ6 (.n 142) + σ6 (.n 208)
    simp only [σ6, σ5, σ4, Function.update_self, Function.update_of_ne (ne _ _ (show 142 ≠ 209 by omega)),
      Function.update_of_ne (ne _ _ (show 142 ≠ 208 by omega)), Function.update_of_ne (ne _ _ (show 142 ≠ 207 by omega)),
      Function.update_of_ne (ne _ _ (show 208 ≠ 209 by omega)), h142, eOfNat_mul_unused hU]
  · have hk6 : ∀ k < 207, ∀ e1 e2 e3 : E, Function.update (Function.update (Function.update σ3 (.n 207) e1)
        (.n (207 + 1)) e2) (.n (207 + 1 + 1)) e3 (.n k) = σ3 (.n k) := fun k hk e1 e2 e3 => by
      rw [Function.update_of_ne (ne _ _ (by omega)), Function.update_of_ne (ne _ _ (by omega)),
        Function.update_of_ne (ne _ _ (by omega))]
    refine ⟨⟨by rw [hk6 2 (by omega), hk3 2 (by omega), h2], by rw [hk6 3 (by omega), hk3 3 (by omega), h3], hN, hU,
      fun j hj => by rw [hk6 _ (by omega), hk3 _ (by omega), hbN j hj], fun l hl => ?_, ?_⟩,
      by rw [hk6 1 (by omega), hk3 1 (by omega), h1], by rw [hk6 5 (by omega), hk3 5 (by omega), h5],
      by rw [hk6 6 (by omega), hk3 6 (by omega), h6], by rw [hk6 12 (by omega), hk3 12 (by omega), h12],
      by rw [hk6 17 (by omega), hk6 18 (by omega), hk3 17 (by omega), hk3 18 (by omega), hd],
      fun k hk => (hag1 k hk).trans (by rw [hk6 k (by omega), hk3 k (by omega)])⟩
    · have := hs2 (25 - l) (by omega)
      rw [show 67 + 3 * (25 - l) = 142 - 3 * l by omega, show 26 - 1 - (25 - l) = l by omega] at this
      rw [hk6 _ (by omega), ← hag3 _ (by omega)]; exact this
    · simp

theorem sPrologue_below : NumBelow 210 (Stmt.valsList sPrologue) := by
  rw [sPrologue_eq, show [.atom (.load (.n 1) (.n 0) 1), cst 2 (mdw 48 true), cst 3 (mdw 64 true),
      cst 4 (word (tw 12) 0 0), .atom (.load (.n 5) (.n 0) 2), .atom (.load (.n 6) (.n 0) 3), cst 7 iv0, cst 8 iv1,
      cst 9 (mdw 64 false), b2s (.n 1) (.n 4) (.n 5) (.n 6) (.n 7) (.n 8) (.n 10) (.n 11) (.n 9),
      hintW "sp_rand" [.n 12], cst 13 (word 0 0 0), cst 14 (word 0 0 0), cst 15 (word 0 0 0),
      cst 16 (mdw 80 true), b2s (.n 12) (.n 13) (.n 14) (.n 15) (.n 10) (.n 11) (.n 17) (.n 18) (.n 16),
      .atom (.hint (.bits (.n 18) 0 26 (.stack ((List.range 26).map fun j => .n (19 + j)))))] = sPro1 from rfl]
  simp only [valsList_append, valsList_cons]
  refine (sPro1_below.mono (by omega)).append (((valsList_booleans 19 26).mono (by omega)).append ?_)
  refine NumBelow.append ?_ (((valsList_booleans 45 22).mono (by omega)).append
    (((shifts_below_gen 19 26 67 (by omega) (by omega)).mono (by omega)).append
      (((shifts_below_gen 45 22 143 (by omega) (by omega)).mono (by omega)).append ?_)))
  · simp only [Stmt.vals, Atom.vals, Hint.vals, Dest.vals, List.map_cons, List.map_nil, List.range_succ,
      List.range_zero, List.nil_append, List.cons_append]
    repeat (first | exact .nil _ | (refine .cons ⟨_, ?_, rfl⟩ ?_; omega))
  · simp only [cst, mulS, addS, valsList_nil, Stmt.vals, Atom.vals, List.append_nil, List.cons_append,
      List.nil_append]
    repeat (first | exact .nil _ | (refine .cons ⟨_, ?_, rfl⟩ ?_; omega))

/-! ## The lanes -/

/-- Lane value after `k` steps, over the bytes `t`. -/
def laneV (t : Nat → Nat) (k : Nat) : E := eOfNat ((∑ j ∈ Finset.range 8, t j * 2 ^ (8 * j)) / 2 ^ (8 * (7 - k)))

theorem laneV_zero {t : Nat → Nat} (ht : ∀ k < 8, t k < 2 ^ 8) : laneV t 0 = eOfNat (t 7) := by
  have hL := baseW_lt 8 8 ht
  have hd := baseW_digit 8 8 ht 7 (by omega)
  rw [Nat.mod_eq_of_lt (Nat.div_lt_of_lt_mul (by rw [← pow_add]; exact hL))] at hd
  rw [laneV, hd]

theorem laneV_succ {t : Nat → Nat} (ht : ∀ k < 8, t k < 2 ^ 8) {k : Nat} (hk : k < 7) :
    laneV t (k + 1) = eOfNat (t (6 - k)) + laneV t k * word 256 0 0 := by
  have hL := baseW_lt 8 8 ht
  have hq : (∑ j ∈ Finset.range 8, t j * 2 ^ (8 * j)) / 2 ^ (8 * (7 - k)) < 2 ^ 56 :=
    Nat.div_lt_of_lt_mul (lt_of_lt_of_le hL (by rw [← pow_add]; exact Nat.pow_le_pow_right (by norm_num) (by omega)))
  rw [laneV, laneV, lane_step hq (ht _ (by omega))]
  congr 1
  rw [div_pow_step 8 (∑ j ∈ Finset.range 8, t j * 2 ^ (8 * j)) (7 - (k + 1)),
    baseW_digit 8 8 ht (7 - (k + 1)) (by omega), show 7 - (k + 1) + 1 = 7 - k by omega,
    show 7 - (k + 1) = 6 - k by omega]

theorem laneV_seven (t : Nat → Nat) : laneV t 7 = eOfNat (∑ j ∈ Finset.range 8, t j * 2 ^ (8 * j)) := by
  simp [laneV]

/-- A block of the lanes. -/
def laneBlock (wd : Nat → V) (b k' : Nat) : List Stmt :=
  let lane0 : Nat → V := fun k => if k = 0 then wd 7 else .n (b + 6 * (k - 1) + 2)
  let lane1 : Nat → V := fun k => if k = 0 then wd 15 else .n (b + 6 * (k - 1) + 5)
  let e := b + 6 * k'
  [cst e (word 256 0 0), mulS (.n (e + 1)) (lane0 k') (.n e), addS (.n (e + 2)) (wd (7 - (k' + 1))) (.n (e + 1)),
    cst (e + 3) (word 256 0 0), mulS (.n (e + 4)) (lane1 k') (.n (e + 3)),
    addS (.n (e + 5)) (wd (15 - (k' + 1))) (.n (e + 4))]

theorem sLanes_split (wd : Nat → V) (bound : V) (b : Nat) :
    sLanes wd bound b = (List.range 7).flatMap (laneBlock wd b) ++
      [cst (b + 42) (word 0 1 0), mulS (.n (b + 42 + 1)) (.n (b + 6 * (7 - 1) + 5)) (.n (b + 42)),
        addS (.n (b + 42 + 2)) (.n (b + 6 * (7 - 1) + 2)) (.n (b + 42 + 1)),
        .atom (.assertEq (.n (b + 42 + 2)) (.n 17)), .atom (.assertEq bound (.n 18))] := rfl

theorem laneBlock_below {wd : Nat → V} {b k' : Nat} (hwd : ∀ k < 16, NB b (wd k)) (hk' : k' < 7) :
    NumBelow (b + 6 * (k' + 1)) (Stmt.valsList (laneBlock wd b k')) := by
  have w1 := (hwd (7 - (k' + 1)) (by omega)).mono (show b ≤ b + 6 * (k' + 1) by omega)
  have w2 := (hwd (15 - (k' + 1)) (by omega)).mono (show b ≤ b + 6 * (k' + 1) by omega)
  have w7 := (hwd 7 (by omega)).mono (show b ≤ b + 6 * (k' + 1) by omega)
  have w15 := (hwd 15 (by omega)).mono (show b ≤ b + 6 * (k' + 1) by omega)
  by_cases h0 : k' = 0
  · subst h0
    simp only [laneBlock, cst, mulS, addS, ↓reduceIte, valsList_cons, valsList_nil, Stmt.vals, Atom.vals,
      List.append_nil, List.cons_append, List.nil_append]
    exact .cons ⟨_, by omega, rfl⟩ (.cons ⟨_, by omega, rfl⟩ (.cons w7 (.cons ⟨_, by omega, rfl⟩
      (.cons ⟨_, by omega, rfl⟩ (.cons w1 (.cons ⟨_, by omega, rfl⟩ (.cons ⟨_, by omega, rfl⟩
      (.cons ⟨_, by omega, rfl⟩ (.cons w15 (.cons ⟨_, by omega, rfl⟩ (.cons ⟨_, by omega, rfl⟩ (.cons w2
      (.cons ⟨_, by omega, rfl⟩ (.nil _))))))))))))))
  · simp only [laneBlock, cst, mulS, addS, h0, ↓reduceIte, valsList_cons, valsList_nil, Stmt.vals, Atom.vals,
      List.append_nil, List.cons_append, List.nil_append]
    exact .cons ⟨_, by omega, rfl⟩ (.cons ⟨_, by omega, rfl⟩ (.cons ⟨_, by omega, rfl⟩ (.cons ⟨_, by omega, rfl⟩
      (.cons ⟨_, by omega, rfl⟩ (.cons w1 (.cons ⟨_, by omega, rfl⟩ (.cons ⟨_, by omega, rfl⟩
      (.cons ⟨_, by omega, rfl⟩ (.cons ⟨_, by omega, rfl⟩ (.cons ⟨_, by omega, rfl⟩ (.cons ⟨_, by omega, rfl⟩
      (.cons w2 (.cons ⟨_, by omega, rfl⟩ (.nil _))))))))))))))

theorem sLanes_below {wd : Nat → V} {bound : V} {b : Nat} (hwd : ∀ k < 16, NB b (wd k)) (hbB : NB b bound)
    (hb : 19 ≤ b) : NumBelow (b + 45) (Stmt.valsList (sLanes wd bound b)) := by
  rw [sLanes_split, valsList_append]
  refine (numBelow_valsList_flatMap _ _ fun k' hk' => ?_).append ?_
  · rw [List.mem_range] at hk'
    exact (laneBlock_below hwd hk').mono (by omega)
  · obtain ⟨kb, hkb, rfl⟩ := hbB
    simp only [cst, mulS, addS, valsList_cons, valsList_nil, Stmt.vals, Atom.vals, List.append_nil, List.cons_append,
      List.nil_append]
    repeat (first | exact .nil _ | (refine .cons ⟨_, ?_, rfl⟩ ?_; omega))

theorem lanes_lit {t : Nat → Nat} (ht : ∀ k < 16, t k < 2 ^ 8) :
    laneV t 7 + laneV (fun k => t (8 + k)) 7 * word 0 1 0 = lit (∑ k ∈ Finset.range 16, t k * 2 ^ (8 * k)) := by
  have hL0 := baseW_lt 8 8 (d := t) (fun k hk => ht k (by omega))
  have hL1 := baseW_lt 8 8 (d := fun k => t (8 + k)) (fun k hk => ht _ (by omega))
  have h64 : (2 : Nat) ^ (8 * 8) = 2 ^ 64 := rfl
  rw [h64] at hL0 hL1
  rw [laneV_seven, laneV_seven, word_y, mul_comm, eOfNat, eOfNat, ofK_add_y_mul_ofK, sum16_split, lit, word,
    Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hL0, Nat.add_mul_div_left _ _ (by positivity),
    Nat.div_eq_of_lt hL0, Nat.zero_add, Nat.mod_eq_of_lt hL1, ofBits_zero]

/-- **The lanes are complete**: over the codeword bytes `t`, when the digest's cells are the
bytes' literal and the bound. -/
theorem sLanes_complete {σ : Val} {wd : Nat → V} {bound : V} {b : Nat} (hb : 19 ≤ b) (hwd : ∀ k < 16, NB b (wd k))
    (hbB : NB b bound) {t : Nat → Nat} (ht : ∀ k < 16, t k < 2 ^ 8) (hwv : ∀ k < 16, σ (wd k) = eOfNat (t k))
    (h17 : σ (.n 17) = lit (∑ k ∈ Finset.range 16, t k * 2 ^ (8 * k))) (h18 : σ bound = σ (.n 18)) :
    Completes C rd b (b + 45) (sLanes wd bound b) σ (fun σ' => AgreeBelow b σ σ') := by
  have ht0 : ∀ k < 8, t k < 2 ^ 8 := fun k hk => ht k (by omega)
  have ht1 : ∀ k < 8, t (8 + k) < 2 ^ 8 := fun k hk => ht _ (by omega)
  set t' : Nat → Nat := fun k => t (8 + k)
  have hkeep : ∀ σ' : Val, AgreeBelow b σ σ' → ∀ v : V, NB b v → σ' v = σ v := fun σ' h v ⟨k, hk, e⟩ => by
    rw [e]; exact (h k hk).symm
  rw [sLanes_split]
  have hfm := Completes.flatMap_range (C := C) (rd := rd) (f := laneBlock wd b) (base := fun k => b + 6 * k)
    (Inv := fun k σ' => σ' (if k = 0 then wd 7 else .n (b + 6 * (k - 1) + 2)) = laneV t k ∧
      σ' (if k = 0 then wd 15 else .n (b + 6 * (k - 1) + 5)) = laneV t' k ∧ AgreeBelow b σ σ')
    (fun k => by omega) 7 (fun k hk => laneBlock_below hwd hk)
    (fun k hk σ' ⟨hl0, hl1, hag⟩ => by
      set e := b + 6 * k
      set vs : List E := [word 256 0 0, laneV t k * word 256 0 0, laneV t (k + 1), word 256 0 0,
        laneV t' k * word 256 0 0, laneV t' (k + 1)]
      set σ'' := upds σ' ((List.range 6).map fun j => (e + j, vs.getD j 0))
      have he : Ext e (e + 6) σ' σ'' := upds_ext σ' _ (by simp)
      have v : ∀ j < 6, σ'' (.n (e + j)) = vs.getD j 0 := upds_range_at e _ 6 σ'
      have hk' : ∀ v : V, NB e v → σ'' v = σ' v := fun v hv => he.out (out_of_lt hv)
      have hl0B : NB e (if k = 0 then wd 7 else .n (b + 6 * (k - 1) + 2)) := by
        split
        · exact (hwd 7 (by omega)).mono (by omega)
        · exact ⟨_, by omega, rfl⟩
      have hl1B : NB e (if k = 0 then wd 15 else .n (b + 6 * (k - 1) + 5)) := by
        split
        · exact (hwd 15 (by omega)).mono (by omega)
        · exact ⟨_, by omega, rfl⟩
      refine ⟨σ'', he, ⟨?_, ?_, fun j hj => (hag j hj).trans (he.agree j (by omega))⟩, fun next kret hn => ?_⟩
      · simp only [Nat.add_one_ne_zero, ↓reduceIte, Nat.add_sub_cancel]
        rw [show b + 6 * k + 2 = e + 2 from rfl, v 2 (by omega)]; rfl
      · simp only [Nat.add_one_ne_zero, ↓reduceIte, Nat.add_sub_cancel]
        rw [show b + 6 * k + 5 = e + 5 from rfl, v 5 (by omega)]; rfl
      · simp only [laneBlock, cst, mulS, addS, holdsList_cons_atom, holdsList_nil, Atom.Holds]
        have v0 := v 0 (by omega)
        rw [Nat.add_zero] at v0
        rw [v0, v 1 (by omega), v 2 (by omega), v 3 (by omega), v 4 (by omega), v 5 (by omega), hk' _ hl0B,
          hk' _ hl1B, hl0, hl1, hk' _ ((hwd (7 - (k + 1)) (by omega)).mono (by omega)),
          hk' _ ((hwd (15 - (k + 1)) (by omega)).mono (by omega)), hkeep σ' hag _ (hwd _ (by omega)),
          hkeep σ' hag _ (hwd _ (by omega)), hwv _ (by omega), hwv _ (by omega)]
        simp only [vs, List.getD_cons_succ, List.getD_cons_zero]
        refine ⟨trivial, trivial, ?_, trivial, trivial, ?_, hn⟩
        · rw [laneV_succ ht0 (by omega), show 7 - (k + 1) = 6 - k by omega]
        · rw [laneV_succ ht1 (by omega), show 15 - (k + 1) = 8 + (6 - k) by omega])
    σ ⟨by simp only [↓reduceIte]; rw [hwv 7 (by omega), laneV_zero ht0],
      by simp only [↓reduceIte]; rw [hwv 15 (by omega), laneV_zero ht1], fun _ _ => rfl⟩
  have hfb : NumBelow (b + 6 * 7) (Stmt.valsList ((List.range 7).flatMap (laneBlock wd b))) :=
    numBelow_valsList_flatMap _ _ fun k hk => (laneBlock_below hwd (List.mem_range.mp hk)).mono (by
      have := List.mem_range.mp hk; omega)
  refine Completes.append (m := b + 6 * 7) (by omega) (by omega) hfb hfm
    fun σ1 _ ⟨hl0, hl1, hag1⟩ => ?_
  simp only [OfNat.ofNat_ne_zero, ↓reduceIte, Nat.add_one_sub_one] at hl0 hl1
  set vs : List E := [word 0 1 0, laneV t' 7 * word 0 1 0, laneV t 7 + laneV t' 7 * word 0 1 0]
  set σ'' := upds σ1 ((List.range 3).map fun j => (b + 42 + j, vs.getD j 0))
  have he : Ext (b + 42) (b + 42 + 3) σ1 σ'' := upds_ext σ1 _ (by simp)
  have v : ∀ j < 3, σ'' (.n (b + 42 + j)) = vs.getD j 0 := upds_range_at (b + 42) _ 3 σ1
  have hk' : ∀ v : V, NB (b + 42) v → σ'' v = σ1 v := fun v hv => he.out (out_of_lt hv)
  refine ⟨σ'', he.mono le_rfl (by omega), fun j hj => (hag1 j hj).trans (he.agree j (by omega)), fun next kret hn => ?_⟩
  simp only [cst, mulS, addS, holdsList_cons_atom, holdsList_nil, Atom.Holds]
  have v0 := v 0 (by omega)
  rw [Nat.add_zero] at v0
  rw [v0, v 1 (by omega), v 2 (by omega), hk' (.n 17) ⟨17, by omega, rfl⟩, hk' (.n 18) ⟨18, by omega, rfl⟩,
    hk' _ (hbB.mono (by omega)), hk' (.n (b + 6 * (7 - 1) + 5)) ⟨_, by omega, rfl⟩,
    hk' (.n (b + 6 * (7 - 1) + 2)) ⟨_, by omega, rfl⟩, hkeep σ1 hag1 _ hbB, hkeep σ1 hag1 (.n 17) ⟨17, by omega, rfl⟩,
    hkeep σ1 hag1 (.n 18) ⟨18, by omega, rfl⟩, show b + 6 * (7 - 1) + 5 = b + 6 * 6 + 5 from rfl,
    show b + 6 * (7 - 1) + 2 = b + 6 * 6 + 2 from rfl, hl0, hl1, h17, h18]
  simp only [vs, List.getD_cons_succ, List.getD_cons_zero]
  refine ⟨trivial, trivial, trivial, ?_, e_add_eq_zero_iff.mpr rfl, hn⟩
  exact e_add_eq_zero_iff.mpr (lanes_lit ht)

/-! ## The counter -/

/-- A Horner step of the counter from base `b`. -/
def ctrBlock (b i' : Nat) : List Stmt :=
  [mulS (.n (b + 1 + (i' + 1))) (.n (b + 1 + (i' + 1))) (.n (b + 1 + (i' + 1))), cst (b + 33 + 3 * i') (word 2 0 0),
    mulS (.n (b + 33 + 3 * i' + 1)) (.n (b + 33 + 3 * i'))
      (if i' = 0 then .n (b + 32) else .n (b + 33 + 3 * i' - 1)),
    addS (.n (b + 33 + 3 * i' + 2)) (.n (b + 32 - (i' + 1))) (.n (b + 33 + 3 * i' + 1))]

/-- The counter's check and its encoding hash. -/
def ctrTail (fk : V) (b : Nat) : List Stmt :=
  [.atom (.assertEq (.n (b + 125)) (.n b)), cst (b + 126) (word (tw 4) 0 0), addS (.n (b + 126 + 1)) (.n 142) (.n (b + 126))] ++
  ivs (b + 126 + 2) ++ [cst (b + 126 + 4) (mdw 52 true),
    b2s (.n 1) (.n (b + 126 + 1)) fk (.n b) (.n (b + 126 + 2)) (.n (b + 126 + 3)) (.n (b + 126 + 5))
      (.n (b + 126 + 6)) (.n (b + 126 + 4))]

theorem sCounter_split (fk : V) (b : Nat) : sCounter fk b =
    hintW "sp_counter" [.n b] :: .atom (.hint (.bits (.n b) 0 32 (.stack ((List.range 32).map fun j => .n (b + 1 + j))))) ::
      ([mulS (.n (b + 1)) (.n (b + 1)) (.n (b + 1))] ++ ((List.range 31).flatMap (ctrBlock b) ++ ctrTail fk b)) := by
  simp only [sCounter, ctrTail, List.append_assoc, List.cons_append, List.nil_append]
  rfl

theorem ctrBlock_below {b i' : Nat} (hi : i' < 31) : NumBelow (b + 33 + 3 * (i' + 1)) (Stmt.valsList (ctrBlock b i')) := by
  have hp : NB (b + 33 + 3 * (i' + 1)) (if i' = 0 then .n (b + 32) else .n (b + 33 + 3 * i' - 1)) := by
    split
    · exact ⟨_, by omega, rfl⟩
    · exact ⟨_, by omega, rfl⟩
  simp only [ctrBlock, cst, mulS, addS, valsList_cons, valsList_nil, Stmt.vals, Atom.vals, List.append_nil,
    List.cons_append, List.nil_append]
  exact .cons ⟨_, by omega, rfl⟩ (.cons ⟨_, by omega, rfl⟩ (.cons ⟨_, by omega, rfl⟩ (.cons ⟨_, by omega, rfl⟩
    (.cons ⟨_, by omega, rfl⟩ (.cons ⟨_, by omega, rfl⟩ (.cons hp (.cons ⟨_, by omega, rfl⟩ (.cons ⟨_, by omega, rfl⟩
    (.cons ⟨_, by omega, rfl⟩ (.nil _))))))))))

theorem ctrTail_below {fk : V} {b : Nat} (hfk : NB b fk) (hb143 : 143 ≤ b) :
    NumBelow (b + 133) (Stmt.valsList (ctrTail fk b)) := by
  obtain ⟨kf, hkf, rfl⟩ := hfk
  simp only [ctrTail, ivs, cst, addS, b2s, valsList_cons, valsList_nil, Stmt.vals, Atom.vals,
    List.append_nil, List.cons_append, List.nil_append]
  repeat (first | exact .nil _ | (refine .cons ⟨_, ?_, rfl⟩ ?_; omega))

theorem sCounter_below {fk : V} {b : Nat} (hfk : NB b fk) (hb143 : 143 ≤ b) :
    NumBelow (b + 133) (Stmt.valsList (sCounter fk b)) := by
  rw [sCounter_split]
  simp only [hintW, mulS, valsList_cons, valsList_append, Stmt.vals, Atom.vals, Hint.vals, Dest.vals,
    List.cons_append, List.nil_append]
  refine .cons ⟨b, by omega, rfl⟩ (.cons ⟨b, by omega, rfl⟩ ?_)
  refine NumBelow.append (fun v hv => ?_) (.cons ⟨_, by omega, rfl⟩ (.cons ⟨_, by omega, rfl⟩
    (.cons ⟨_, by omega, rfl⟩ (NumBelow.append (numBelow_valsList_flatMap _ _ fun i hi =>
      (ctrBlock_below (List.mem_range.mp hi)).mono (by have := List.mem_range.mp hi; omega))
      (ctrTail_below hfk hb143)))))
  simp only [List.mem_map, List.mem_range] at hv
  obtain ⟨j, hj, rfl⟩ := hv
  exact ⟨_, by omega, rfl⟩

/-- **The counter is complete**: over any counter below `2^32`. -/
theorem sCounter_complete {σ : Val} {fk : V} {b : Nat} (hb143 : 143 ≤ b) (hfk : NB b fk) {Cn : Nat}
    (hCn : Cn < 2 ^ 32) (hp : IsCanonical128 (σ (.n 1))) (ha : IsCanonical128 (σ (.n 142) + word (tw 4) 0 0))
    (hf : IsCanonical128 (σ fk)) :
    Completes C rd b (b + 133) (sCounter fk b) σ (fun σ' => σ' (.n b) = eOfNat Cn ∧
      σ' (.n (b + 126 + 1)) = σ (.n 142) + word (tw 4) 0 0 ∧
      σ' (.n (b + 126 + 5)) = (hb (cellBytes (σ (.n 1)) ++ cellBytes (σ (.n 142) + word (tw 4) 0 0) ++
        cellBytes (σ fk) ++ leBytes Cn 4)).1 ∧ AgreeBelow b σ σ') := by
  rw [sCounter_split]
  refine Completes.hint_cons _ (Completes.hint_cons _ ?_)
  set cv : Nat → E := fun j => if j = 0 then eOfNat Cn else bitE (Cn.testBit (j - 1))
  set σ1 := upds σ ((List.range 33).map fun j => (b + j, cv j))
  have he1 : Ext b (b + 133) σ σ1 := upds_ext σ _ fun p hp => by
    simp only [List.mem_map, List.mem_range] at hp
    obtain ⟨j, hj, rfl⟩ := hp
    exact ⟨by omega, by omega⟩
  have hv1 : ∀ j < 33, σ1 (.n (b + j)) = cv j := upds_range_at b _ 33 σ
  have hbit : ∀ j < 32, σ1 (.n (b + 1 + j)) = bitE (Cn.testBit j) := fun j hj => by
    rw [add_assoc, hv1 _ (by omega)]
    simp only [cv, Nat.add_eq_zero_iff, one_ne_zero, false_and, ↓reduceIte, Nat.add_sub_cancel_left]
  have hc0 : σ1 (.n b) = eOfNat Cn := by
    have := hv1 0 (by omega)
    rwa [Nat.add_zero] at this
  have hag1 : AgreeBelow b σ σ1 := fun k hk => he1.agree k hk
  refine Completes.of_ext he1 (Completes.mono (lo := b + 33) ?_ (by omega) le_rfl fun σ' h => h)
  refine Completes.append_holds (.cons ⟨_, by omega, rfl⟩ (.cons ⟨_, by omega, rfl⟩ (.cons ⟨_, by omega, rfl⟩ (.nil _))))
    (fun next kret hn => ?_) ?_
  · simp only [mulS, holdsList_cons_atom, holdsList_nil, Atom.Holds]
    have h0 := hbit 0 (by omega)
    rw [Nat.add_zero] at h0
    rw [h0]
    exact ⟨(bitE_mul_self _).symm, hn⟩
  have hfm := Completes.flatMap_range (C := C) (rd := rd) (f := ctrBlock b) (base := fun i => b + 33 + 3 * i)
    (Inv := fun i σ' => AgreeBelow (b + 33) σ1 σ' ∧
      σ' (if i = 0 then .n (b + 32) else .n (b + 33 + 3 * i - 1)) = eOfNat (Cn / 2 ^ (31 - i)))
    (fun _ => by omega) 31 (fun i hi => ctrBlock_below hi)
    (fun i hi σ' ⟨hag, hpv⟩ => by
      set c := b + 33 + 3 * i
      set vs : List E := [word 2 0 0, word 2 0 0 * eOfNat (Cn / 2 ^ (31 - i)), eOfNat (Cn / 2 ^ (30 - i))]
      set σ'' := upds σ' ((List.range 3).map fun j => (c + j, vs.getD j 0))
      have he : Ext c (c + 3) σ' σ'' := upds_ext σ' _ (by simp)
      have v : ∀ j < 3, σ'' (.n (c + j)) = vs.getD j 0 := upds_range_at c _ 3 σ'
      have hk' : ∀ v : V, NB c v → σ'' v = σ' v := fun v hv => he.out (out_of_lt hv)
      have hpB : NB c (if i = 0 then .n (b + 32) else .n (b + 33 + 3 * i - 1)) := by
        split
        · exact ⟨_, by omega, rfl⟩
        · exact ⟨_, by omega, rfl⟩
      have hb1 : σ'' (.n (b + 1 + (i + 1))) = bitE (Cn.testBit (i + 1)) := by
        rw [hk' _ ⟨_, by omega, rfl⟩, ← hag _ (by omega), hbit _ (by omega)]
      have hb2 : σ'' (.n (b + 32 - (i + 1))) = bitE (Cn.testBit (30 - i)) := by
        rw [show b + 32 - (i + 1) = b + 1 + (30 - i) by omega, hk' _ ⟨_, by omega, rfl⟩, ← hag _ (by omega),
          hbit _ (by omega)]
      refine ⟨σ'', he, ⟨fun k hk => (hag k hk).trans (he.agree k (by omega)), ?_⟩, fun next kret hn => ?_⟩
      · simp only [Nat.add_one_ne_zero, ↓reduceIte]
        rw [show b + 33 + 3 * (i + 1) - 1 = c + 2 by omega, v 2 (by omega), show 31 - (i + 1) = 30 - i by omega]
        rfl
      · simp only [ctrBlock, cst, mulS, addS, holdsList_cons_atom, holdsList_nil, Atom.Holds]
        have v0 := v 0 (by omega)
        rw [Nat.add_zero] at v0
        rw [hb1, v0, v 1 (by omega), v 2 (by omega), hk' _ hpB, hpv, hb2]
        simp only [vs, List.getD_cons_succ, List.getD_cons_zero]
        refine ⟨(bitE_mul_self _).symm, trivial, trivial, ?_, hn⟩
        rw [word_two, add_comm, show 31 - i = 30 - i + 1 by omega, shift_step (by omega)])
    σ1 ⟨fun _ _ => rfl, by
      simp only [↓reduceIte]
      rw [show b + 32 = b + 1 + 31 by omega, hbit 31 (by omega), top_bit (show Cn < 2 ^ (31 + 1) from hCn)]⟩
  refine Completes.append (m := b + 33 + 3 * 31) (by omega) (by omega)
    (numBelow_valsList_flatMap _ _ fun i hi => (ctrBlock_below (List.mem_range.mp hi)).mono (by
      have := List.mem_range.mp hi; omega)) hfm fun σ2 _ ⟨hag2, hpv2⟩ => ?_
  have h125 : σ2 (.n (b + 125)) = eOfNat Cn := by
    rw [ite_neg' (by omega), show b + 33 + 3 * 31 - 1 = b + 125 by omega, Nat.sub_self, pow_zero,
      Nat.div_one] at hpv2
    exact hpv2
  have h2 : ∀ k < b + 33, σ2 (.n k) = σ1 (.n k) := fun k hk => (hag2 k hk).symm
  have hagB : AgreeBelow b σ σ2 := fun k hk => (hag1 k hk).trans (hag2 k (by omega))
  have hkB : ∀ v : V, NB b v → σ2 v = σ v := fun v ⟨k, hk, e⟩ => by rw [e]; exact (hagB k hk).symm
  set A := σ (.n 142) + word (tw 4) 0 0
  set r := cellBytes (σ (.n 1)) ++ cellBytes A ++ cellBytes (σ fk) ++ leBytes Cn 4
  set o := hb r
  have hr : r.length = 52 := by simp [r, length_cellBytes]
  set e := b + 126
  set vs : List E := [word (tw 4) 0 0, A, iv0, iv1, mdw 52 true, o.1, o.2]
  set σ3 := upds σ2 ((List.range 7).map fun j => (e + j, vs.getD j 0))
  have he3 : Ext e (e + 7) σ2 σ3 := upds_ext σ2 _ (by simp)
  have v : ∀ j < 7, σ3 (.n (e + j)) = vs.getD j 0 := upds_range_at e _ 7 σ2
  have hk3 : ∀ v : V, NB e v → σ3 v = σ2 v := fun v hv => he3.out (out_of_lt hv)
  have hcmp : CompressCells ![σ (.n 1), A, σ fk, eOfNat Cn] iv0 iv1 o.1 o.2 (mdw 52 true) := by
    rw [← hr]
    exact (compress_final_iff (by rw [blockBytes_four, hr]; simp [r, cellBytes_counter hCn]) (by rw [hr]; omega)).mpr
      ⟨fun i => by fin_cases i <;> simp [hp, ha, hf, isCanonical128_eOfNat], rfl⟩
  refine ⟨σ3, he3.mono (by omega) (by omega), ⟨?_, ?_, ?_, fun k hk => (hagB k hk).trans (he3.agree k (by omega))⟩,
    fun next kret hn => ?_⟩
  · rw [hk3 _ ⟨b, by omega, rfl⟩, h2 _ (by omega), hc0]
  · rw [v 1 (by omega)]; rfl
  · rw [v 5 (by omega)]; rfl
  · simp only [ctrTail, ivs, cst, addS, b2s, List.cons_append, List.nil_append, holdsList_cons_atom, holdsList_nil,
      Atom.Holds]
    have v0 := v 0 (by omega)
    rw [Nat.add_zero] at v0
    rw [v0, v 1 (by omega), v 2 (by omega), show e + 2 + 1 = e + 3 by omega, v 3 (by omega), v 4 (by omega),
      v 5 (by omega), v 6 (by omega), hk3 _ ⟨b + 125, by omega, rfl⟩, hk3 _ ⟨b, by omega, rfl⟩, h125,
      hk3 _ ⟨142, by omega, rfl⟩, hk3 _ ⟨1, by omega, rfl⟩, hk3 _ (hfk.mono (by omega)), h2 _ (by omega), hc0,
      hkB _ ⟨142, by omega, rfl⟩, hkB _ ⟨1, by omega, rfl⟩, hkB _ hfk]
    simp only [vs, List.getD_cons_succ, List.getD_cons_zero]
    exact ⟨e_add_eq_zero_iff.mpr rfl, trivial, rfl, trivial, trivial, trivial, hcmp, hn⟩

end
end LeanVM.Guest.B1.Sig
