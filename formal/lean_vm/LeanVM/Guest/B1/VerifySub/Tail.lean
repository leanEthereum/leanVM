/-
  LeanVM.Guest.B1.VerifySub.Tail

  `verify_sub`'s last phases as facts: the batching challenge and the opening's target, the
  stack's size and the candidate dispatched, the exported claims.
-/

module

public import LeanVM.Guest.B1.VerifySub.Loops

/-!
# The batching, the opening's dispatch and `defer_out` (G:2211-2280)

* `vs_lam`: `lam_cl`, `lam_pool = [lam, lam², …]` and the opening's target
  `transposed + Σ lam^(j+1)·pool[j]`, the specification's `dot (powers lam 113) …`;
* `vs_stackSel`: `g^m = g^max(15, log2Ceil total)` for the placement's total, `m ∈ [22, 28]`, and
  the dispatch selector `(m - 22) + 7·(r - 1)`;
* `vs_defer`: the cells stored at `defer_out`.
-/

namespace LeanVM.Guest.B1.VerifySub

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.Blake2sHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

variable {rd : Reader} {σ : Val}

/-! ## Sums -/

theorem foldl_add_eq (a : E) (l : List E) : l.foldl (· + ·) a = a + l.sum := by
  induction l generalizing a with
  | nil => simp
  | cons x l ih => rw [List.foldl_cons, ih, List.sum_cons, add_assoc]

theorem zipWith_powersFrom (acc b : E) :
    ∀ (vs : List E), (List.zipWith (· * ·) (powersFrom acc b vs.length) vs) =
      (List.range vs.length).map fun i ↦ acc * b ^ i * vs.getD i 0
  | [] => rfl
  | v :: vs => by
    rw [List.length_cons, powersFrom, List.zipWith_cons_cons, zipWith_powersFrom (acc * b) b vs,
      List.range_succ_eq_map]
    simp only [List.map_cons, List.map_map, Function.comp_def, pow_zero, mul_one,
      List.getD_cons_zero, List.getD_cons_succ, pow_succ]
    exact List.cons_eq_cons.mpr ⟨rfl, List.map_congr_left fun i _ => by ring⟩

theorem dot_powers_cons (lam x : E) (vs : List E) :
    dot (powers lam (vs.length + 1)) (x :: vs) =
      x + ((List.range vs.length).map fun i ↦ lam ^ (i + 1) * vs.getD i 0).sum := by
  rw [dot, powers, powersFrom, List.zipWith_cons_cons, one_mul, List.foldl_cons, zero_add,
    show 1 * lam = lam from one_mul lam, zipWith_powersFrom, foldl_add_eq]
  exact congrArg (x + ·) (congrArg List.sum (List.map_congr_left fun i _ => by ring))

theorem getD_powersFrom (acc b : E) : ∀ (n i : ℕ), i < n → (powersFrom acc b n).getD i 0 = acc * b ^ i
  | n + 1, 0, _ => by simp [powersFrom]
  | n + 1, i + 1, h => by
    rw [powersFrom, List.getD_cons_succ, getD_powersFrom (acc * b) b n i (by omega), pow_succ]
    ring

theorem length_powersFrom (acc b : E) : ∀ n, (powersFrom acc b n).length = n
  | 0 => rfl
  | n + 1 => by rw [powersFrom, List.length_cons, length_powersFrom]

theorem readsAt_of_getD {p : E} {xs : List E}
    (h : ∀ k < xs.length, LoadHolds rd p k (xs.getD k 0)) : ReadsAt rd p xs := fun k hk => by
  have := h k hk
  rwa [List.getD_eq_getElem _ _ hk] at this

/-! ## The batching -/

/-- The power `lam^(j+1)` in the batching loop. -/
def lpP (j : ℕ) : ℕ := if j = 0 then 1179 else 1184 + 4 * (j - 1)

/-- The running target after claim `j`. -/
def lpT (j : ℕ) : ℕ := if j = 0 then 1183 else lpP j + 3

theorem vs_lp_blocks : ∀ j < 111, stmtsEqb [.atom (.mul (.n (lpP (j + 1))) (.n (lpP j)) (.n 1179)),
    .atom (.load (.n (lpP (j + 1))) (.n 1180) (j + 1)),
    .atom (.load (.n (lpP (j + 1) + 1)) (.n 7) (j + 1)),
    .atom (.mul (.n (lpP (j + 1) + 2)) (.n (lpP (j + 1))) (.n (lpP (j + 1) + 1))),
    .atom (.add (.n (lpT (j + 1))) (.n (lpT j)) (.n (lpP (j + 1) + 2)))]
    ((vsPre.drop (1357 + 5 * j)).take 5) = true := by decide +kernel

/-- **The batching** (G:2219-2229): `lam_cl` from the ring map's final state, `lam_pool` its
powers from `lam` on, and the opening's target over the pool's values `vals`. -/
theorem vs_lam (h : VsHolds rd σ) {cv : Digest} (h0 : (σ (.n 810), σ (.n 811)) = digestScalars cv)
    {vals : List E} (hvl : vals.length = 112) (hv : ReadsAt rd (σ (.n 7)) vals) :
    (σ (.n 1171), σ (.n 1172)) = digestScalars (sqCv cv) ∧ σ (.n 1179) = challengeOf (sqCv cv) ∧
      ReadsAt rd (σ (.n 1180)) (powersFrom (σ (.n 1179)) (σ (.n 1179)) 112) ∧
      σ (.n 1627) = dot (powers (σ (.n 1179)) (vals.length + 1)) (σ (.n 1150) :: vals) := by
  obtain ⟨c, hc, h5, h13⟩ := h.squeeze 1338 (.n 810) (.n 811) 1166 (by decide +kernel)
  rw [h0] at hc
  rw [← digestScalars_injective hc] at h5 h13
  refine ⟨h5, h13, ?_⟩
  set lam := σ (.n 1179)
  have hb0 := h.slice 1353 [.atom (.load (.n 1179) (.n 1180) 0), .atom (.load (.n 1181) (.n 7) 0),
    .atom (.mul (.n 1182) (.n 1179) (.n 1181)), .atom (.add (.n 1183) (.n 1150) (.n 1182))]
    (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds, and_true] at hb0
  obtain ⟨p0, v0, m0, a0⟩ := hb0
  have hvv : ∀ j < 112, ∀ u, LoadHolds rd (σ (.n 7)) j u → u = vals.getD j 0 := fun j hj u hu => by
    rw [List.getD_eq_getElem _ _ (by omega)]; exact loadHolds_unique hu (hv j (by omega))
  have hP : ∀ j < 112, σ (.n (lpP j)) = lam ^ (j + 1) ∧ LoadHolds rd (σ (.n 1180)) j (lam ^ (j + 1)) ∧
      σ (.n (lpT j)) = σ (.n 1150) +
        ((List.range (j + 1)).map fun i ↦ lam ^ (i + 1) * vals.getD i 0).sum := by
    intro j hj
    induction j with
    | zero =>
      refine ⟨by simp [lpP, lam], by simpa [lam] using p0, ?_⟩
      simp only [lpT, ↓reduceIte, a0, m0, hvv 0 (by omega) _ v0, List.range_one, List.map_cons,
        List.map_nil, List.sum_cons, List.sum_nil, add_zero, zero_add, pow_one, lam]
    | succ j ih =>
      obtain ⟨ihP, -, ihT⟩ := ih (by omega)
      have hs := h.slice _ _ (vs_lp_blocks j (by omega))
      simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds, and_true] at hs
      obtain ⟨hm, lp, lv, hmv, ha⟩ := hs
      rw [ihP, ← pow_succ] at hm
      refine ⟨hm, by rw [← hm]; exact lp, ?_⟩
      rw [ha, ihT, hmv, hm, hvv (j + 1) hj _ lv, List.range_succ (n := j + 1), List.map_append,
        List.sum_append]
      simp [add_assoc]
  refine ⟨readsAt_of_getD fun k hk => ?_, ?_⟩
  · rw [length_powersFrom] at hk
    rw [getD_powersFrom _ _ _ _ hk, ← pow_succ']
    exact (hP k hk).2.1
  · rw [dot_powers_cons, hvl, ← (hP 111 (by omega)).2.2]
    rfl

/-! ## The stack's size and the dispatch -/

theorem minShiftInv : word 8198552432976855044 0 0 * gen ^ 22 = 1 := by
  rw [word_eOfNat, word_two_pow (a := 22) (by decide) |>.symm, word_eOfNat, eOfNat, eOfNat,
    ← ofK_mul, show K.ofBits 8198552432976855044 * K.ofBits (2 ^ 22) = 1 by decide +kernel, ofK_one]

/-- **The stack's size and the candidate** (G:2231-2250): `g^m = g^max(15, log2Ceil N)` for the
placement's total `g^N`, `22 ≤ m ≤ 28`, and the dispatch runs `open_stacked` at `(m, r)`. -/
theorem vs_stackSel {κ : ℕ} (hκ : κ ≤ 32) (hκ6 : 6 ≤ κ) (Lm : MemImage κ) (h : VsHolds Lm.read σ)
    (ht : ExpTables Lm.read (σ (.n 4)) (σ (.n 5))) {r : ℕ} (hr1 : 1 ≤ r) (hr2 : r ≤ 4)
    (h138 : σ (.n 138) = gen ^ (r - 1)) :
    ∃ N < 2 ^ 34, σ (.n 1629) = gen ^ N ∧ 22 ≤ max 15 (log2Ceil N) ∧ max 15 (log2Ceil N) ≤ 28 ∧
      coreProgram.Rel Lm.read (openName (max 15 (log2Ceil N)) r)
        [σ (.n 1171), σ (.n 1172), σ (.n 1627), σ (.n 419), σ (.n 434), σ (.n 726)]
        [σ (.n 1648), σ (.n 1649), σ (.n 1650), σ (.n 1651)] := by
  have hc := h.call 1914 "log2_ceil_in_the_exponent__L15_L34" [.n 1629, .n 4, .n 5] [.n 1632]
    (by decide +kernel)
  obtain ⟨N, hN, hg, hl, -, -, hr⟩ := (log2_ceil_in_the_exponent_L15_L34_iff hκ hκ6 Lm ht _).mp hc
  simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true] at hr
  have hs := h.slice 1915 [.atom (.const (.n 1633) (word 8198552432976855044 0 0)),
    .atom (.mul (.n 1634) (.n 1632) (.n 1633)), .atom (.const (.n 1635) (word 64 0 0)),
    .atom (.rangeCheck (.n 1634) (.n 1636) (.n 1637) (.n 1638) (.n 1635)),
    .atom (.mul (.n 1639) (.n 138) (.n 138)), .atom (.mul (.n 1640) (.n 1639) (.n 138)),
    .atom (.mul (.n 1641) (.n 1640) (.n 1640)), .atom (.mul (.n 1642) (.n 1641) (.n 138)),
    .atom (.mul (.n 1643) (.n 1634) (.n 1642)), .atom (.const (.n 1644) (word 134217728 0 0)),
    .atom (.rangeCheck (.n 1643) (.n 1645) (.n 1646) (.n 1647) (.n 1644)),
    .dispatch (.n 1643) openNames [.n 1171, .n 1172, .n 1627, .n 419, .n 434, .n 726]
      [.n 1648, .n 1649, .n 1650, .n 1651]] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds, and_true, List.map_cons, List.map_nil] at hs
  obtain ⟨e1633, e1634, e1635, ⟨r1, r2, r3⟩, e1639, e1640, e1641, e1642, e1643, -, -,
    ⟨j, hj, hx, hcall⟩⟩ := hs
  obtain ⟨e, he, hxe⟩ := rc_gen hκ hκ6 Lm (K := 7) (by decide) (by decide)
    (by rw [e1635]; exact word_two_pow (a := 6) (by decide)) r1 r2 r3
  have hμ : gen ^ max 15 (log2Ceil N) = gen ^ (e + 22) := by
    rw [← hr, pow_add, ← hxe, e1634, e1633, mul_assoc, minShiftInv, mul_one]
  have hμe := gen_pow_inj (by omega) (by omega) hμ
  have hsel : σ (.n 1643) = gen ^ (e + 7 * (r - 1)) := by
    rw [e1643, e1642, e1641, e1640, e1639, hxe, h138, pow_add]
    ring
  rw [hsel, ← gen_pow_eq_ofK] at hx
  have hjv : j = e + 7 * (r - 1) := gen_pow_inj (by simp [openNames] at hj; omega) (by omega) hx.symm
  have hname : openNames[j] = openName (max 15 (log2Ceil N)) r := by
    rw [openName, show max 15 (log2Ceil N) - 22 + 7 * (r - 1) = j by omega,
      List.getD_eq_getElem _ _ hj]
  rw [hname] at hcall
  exact ⟨N, hN, hg, by omega, by omega, hcall⟩

/-! ## `defer_out` -/

theorem readsAt_append {p : E} {a b : List E} (ha : ReadsAt rd p a)
    (hb : ∀ k (hk : k < b.length), LoadHolds rd p (a.length + k) b[k]) : ReadsAt rd p (a ++ b) := by
  intro k hk
  rw [List.length_append] at hk
  rcases Nat.lt_or_ge k a.length with h | h
  · rw [List.getElem_append_left h]; exact ha k h
  · rw [List.getElem_append_right h]
    have := hb (k - a.length) (by omega)
    rwa [show a.length + (k - a.length) = k by omega] at this

/-- A copy from `src[i]` to `defer_out[j]` through the value `v`, at statement `n`. -/
theorem VsHolds.copy (h : VsHolds rd σ) (n v : ℕ) (src : V) (i j : ℕ)
    (heq : stmtsEqb [.atom (.load (.n v) src i), .atom (.load (.n v) (.n 6) j)]
      ((vsPre.drop n).take 2) = true) {w : E} (hw : LoadHolds rd (σ src) i w) :
    LoadHolds rd (σ (.n 6)) j w := by
  have hs := h.slice n _ heq
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds, and_true] at hs
  rw [← loadHolds_unique hs.1 hw]; exact hs.2

/-- **`defer_out`** (G:2265-2279): the cells of the claims on the fixed polynomials, in
`Node.fixedCells` order. -/
theorem vs_defer (h : VsHolds rd σ) {P alphas chi rcs s : List E} (hP : 18 ≤ P.length)
    (hPr : ReadsAt rd (σ (.n 418)) P) (hal : alphas.length = 4) (har : ReadsAt rd (σ (.n 451)) alphas)
    (hcl : 8 ≤ chi.length) (hcr : ReadsAt rd (σ (.n 721)) chi) (hrl : rcs.length = 8)
    (hrr : ReadsAt rd (σ (.n 722)) rcs) (hsl : s.length = 64) (hsr : ReadsAt rd (σ (.n 723)) s) :
    ReadsAt rd (σ (.n 6)) (Node.fixedCells ⟨P.take 18 ++ alphas, σ (.n 714), σ (.n 728),
      σ (.n 727), chi.take 8, rcs.reverse, s, σ (.n 729)⟩) := by
  have hz : ∀ k < 18, stmtsEqb [.atom (.load (.n (1652 + k)) (.n 418) k),
      .atom (.load (.n (1652 + k)) (.n 6) k)] ((vsPre.drop (1928 + 2 * k)).take 2) = true := by
    decide +kernel
  have ha : ∀ k < 4, stmtsEqb [.atom (.load (.n (1670 + k)) (.n 451) k),
      .atom (.load (.n (1670 + k)) (.n 6) (18 + k))] ((vsPre.drop (1964 + 2 * k)).take 2) = true := by
    decide +kernel
  have hc : ∀ k < 8, stmtsEqb [.atom (.load (.n (1674 + 2 * k)) (.n 721) k),
      .atom (.load (.n (1674 + 2 * k)) (.n 6) (25 + k))] ((vsPre.drop (1975 + 4 * k)).take 2) = true := by
    decide +kernel
  have hr : ∀ k < 8, stmtsEqb [.atom (.load (.n (1675 + 2 * k)) (.n 722) k),
      .atom (.load (.n (1675 + 2 * k)) (.n 6) (33 + k))] ((vsPre.drop (1977 + 4 * k)).take 2) = true := by
    decide +kernel
  have hss : ∀ k < 64, stmtsEqb [.atom (.load (.n (1690 + k)) (.n 723) k),
      .atom (.load (.n (1690 + k)) (.n 6) (41 + k))] ((vsPre.drop (2007 + 2 * k)).take 2) = true := by
    decide +kernel
  have l22 := h.atom 1972 (.load (.n 714) (.n 6) 22) (by decide +kernel)
  have l23 := h.atom 1973 (.load (.n 728) (.n 6) 23) (by decide +kernel)
  have l24 := h.atom 1974 (.load (.n 727) (.n 6) 24) (by decide +kernel)
  have l105 := h.atom 2135 (.load (.n 729) (.n 6) 105) (by decide +kernel)
  have hbp : (P.take 18 ++ alphas).length = 22 := by simp [hal]; omega
  simp only [Node.fixedCells, List.reverse_reverse]
  refine readsAt_append (readsAt_append (readsAt_append (readsAt_append (readsAt_append ?_ ?_) ?_) ?_)
    ?_) ?_
  · refine readsAt_append (fun k hk => ?_) (fun k hk => ?_)
    · rw [List.length_take] at hk
      rw [List.getElem_take]
      exact h.copy _ _ _ _ _ (hz k (by omega)) (hPr k (by omega))
    · rw [List.length_take, show min 18 P.length = 18 by omega]
      exact h.copy _ _ _ _ _ (ha k (by omega)) (har k hk)
  · intro k hk
    rw [hbp]
    simp only [List.length_cons, List.length_nil] at hk
    match k, hk with
    | 0, _ => exact l22
    | 1, _ => exact l23
    | 2, _ => exact l24
  · intro k hk
    simp only [List.length_append, hbp, List.length_cons, List.length_nil, List.length_take] at hk ⊢
    rw [List.getElem_take]
    exact h.copy _ _ _ _ _ (hc k (by omega)) (hcr k (by omega))
  · intro k hk
    simp only [List.length_append, hbp, List.length_cons, List.length_nil, List.length_take,
      show min 8 chi.length = 8 by omega] at hk ⊢
    exact h.copy _ _ _ _ _ (hr k (by omega)) (hrr k hk)
  · intro k hk
    simp only [List.length_append, hbp, List.length_cons, List.length_nil, List.length_take,
      show min 8 chi.length = 8 by omega, hrl] at hk ⊢
    exact h.copy _ _ _ _ _ (hss k (by omega)) (hsr k hk)
  · intro k hk
    simp only [List.length_append, hbp, List.length_cons, List.length_nil, List.length_take,
      show min 8 chi.length = 8 by omega, hrl, hsl] at hk ⊢
    match k, hk with
    | 0, _ => exact l105

end
end LeanVM.Guest.B1.VerifySub
