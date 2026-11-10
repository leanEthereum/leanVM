/-
  LeanVM.Guest.B1.VerifySub.Lam

  `verify_sub`'s batching challenge and the stacked opening's target (G:3722-3737).
-/

module

public import LeanVM.Guest.B1.VerifySub.Lanes

/-!
# The batching

After `λ`'s squeeze, `vsLamT` walks the `134` pooled claims the opening batches (the pool's `159`
but the output lanes', slots `105 .. 129`; `vsKept`): claim `j`'s value is read where
`verify_tables` left it (`vsClaimAt`: `claim_pool` for the bus's and the public input's,
`col_eval_words` for the tables'), and the target accumulates `λ^(i+1)·value`; then `λ^135` times
the Keccak reduction's word and `λ^136` times the out-of-domain value. `vsLamT_holds`: the target
is `dot (powers λ 137)` of the ring switch's target, the kept claims' values, the Keccak word and
the out-of-domain value.
-/

namespace LeanVM.Guest.B1.VerifySub

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

variable {C : CallRel} {rd : Reader} {σ : Val} {next : Prop} {kret : List E → Prop}

/-! ## `dot` and `powers` -/

theorem lam_foldl_add (l : List E) (a : E) : l.foldl (· + ·) a = a + l.foldl (· + ·) 0 := by
  induction l generalizing a with
  | nil => simp
  | cons x l ih => rw [List.foldl_cons, List.foldl_cons, ih, ih (0 + x), zero_add, add_assoc]

theorem lam_dot_cons (a x : E) (as xs : List E) : dot (a :: as) (x :: xs) = a * x + dot as xs := by
  simp only [dot, List.zipWith_cons_cons, List.foldl_cons, zero_add]
  rw [lam_foldl_add]

theorem lam_dot_append {as xs : List E} (h : as.length = xs.length) (bs ys : List E) :
    dot (as ++ bs) (xs ++ ys) = dot as xs + dot bs ys := by
  simp only [dot, List.zipWith_append h, List.foldl_append]
  rw [lam_foldl_add]

theorem lam_powersFrom_add (b : E) : ∀ (n m : ℕ) (acc : E),
    powersFrom acc b (n + m) = powersFrom acc b n ++ powersFrom (acc * b ^ n) b m
  | 0, m, acc => by simp [powersFrom]
  | n + 1, m, acc => by
    rw [show n + 1 + m = (n + m) + 1 by omega, powersFrom, powersFrom, lam_powersFrom_add b n m,
      List.cons_append, pow_succ', mul_assoc]

theorem lam_powersFrom_length (b : E) : ∀ (n : ℕ) (acc : E), (powersFrom acc b n).length = n
  | 0, _ => rfl
  | n + 1, acc => by rw [powersFrom, List.length_cons, lam_powersFrom_length b n]

theorem lam_dot_range (lam : E) (W : ℕ → E) : ∀ (k j : ℕ),
    dot (powersFrom (lam ^ (j + 1)) lam k) ((List.range' j k).map W) =
      ((List.range' j k).map fun i ↦ lam ^ (i + 1) * W i).sum
  | 0, j => by simp [dot, powersFrom]
  | k + 1, j => by
    rw [powersFrom, List.range'_succ, List.map_cons, List.map_cons, List.sum_cons, lam_dot_cons,
      ← pow_succ, lam_dot_range lam W k (j + 1)]

/-! ## The claims' values -/

/-- **Claim `j`'s value where `vsClaimAt` reads it.** -/
theorem claim_load {claims : List ColumnClaim} (hcl : claims.length = 159)
    (hpool : ReadsAt rd (σ (.n 6)) ((claims.take 4).map (·.value)))
    (hcew : ReadsAt rd (σ (.n 582)) (((claims.drop 4).take 153).map (·.value)))
    (hpi : ReadsAt rd (σ (.n 6) * gen ^ 157) ((claims.drop 157).map (·.value))) :
    ∀ j < 159, LoadHolds rd (σ (.n (vsClaimAt j).1)) (vsClaimAt j).2
      ((claims.map (·.value)).getD j 0) := by
  intro j hj
  rw [List.getD_eq_getElem _ _ (by simp [hcl]; omega), List.getElem_map]
  unfold vsClaimAt
  split_ifs with h
  · have := hcew (j - 4) (by simp [hcl]; omega)
    simp only [List.getElem_map, List.getElem_take, List.getElem_drop,
      Nat.add_sub_of_le h.1] at this
    exact this
  · by_cases h4 : j < 4
    · have := hpool j (by simp [hcl]; omega)
      simp only [List.getElem_map, List.getElem_take] at this
      exact this
    · have := hpi (j - 157) (by simp [hcl]; omega)
      rw [loadHolds_mul_gen_pow] at this
      simp only [List.getElem_map, List.getElem_drop,
        Nat.add_sub_of_le (show 157 ≤ j by omega)] at this
      exact this

/-! ## The target -/

/-- The batching's steps from claim `j`. -/
theorem lam_chain {lam : E} {W : ℕ → E}
    (hW : ∀ i < 134, LoadHolds rd (σ (.n (vsClaimAt (vsKept i)).1)) (vsClaimAt (vsKept i)).2 (W i))
    (hl : σ (.n 1375) = lam) :
    ∀ (k j : ℕ) {nx : Prop} {T : E}, j + k ≤ 134 → σ (.n (vsTg j)) = T →
      σ (.n (vsPw j)) = lam ^ (j + 1) →
      Stmt.HoldsList C rd σ ((List.range' j k).flatMap vsLamStep) nx kret →
      σ (.n (vsTg (j + k))) = T + ((List.range' j k).map fun i ↦ lam ^ (i + 1) * W i).sum ∧
        σ (.n (vsPw (j + k))) = lam ^ (j + k + 1) ∧ nx
  | 0, j, _, _, _, hT, hP, h => ⟨by simp [hT], by simp [hP], h⟩
  | k + 1, j, _, T, hjk, hT, hP, h => by
    rw [List.range'_succ, List.flatMap_cons, holdsList_append] at h
    obtain ⟨l0, m1, a2, m3, h⟩ := h
    simp only [Atom.Holds] at l0 m1 a2 m3
    have hv := loadHolds_unique l0 (hW j (by omega))
    have hT' : σ (.n (vsTg (j + 1))) = T + lam ^ (j + 1) * W j := by
      rw [show vsTg (j + 1) = 1378 + 4 * j by simp only [vsTg, Nat.add_one_ne_zero, ↓reduceIte]; omega,
        a2, m1, hT, hP, hv]
    have hP' : σ (.n (vsPw (j + 1))) = lam ^ (j + 1 + 1) := by
      rw [show vsPw (j + 1) = 1379 + 4 * j by simp only [vsPw]; omega, m3, hP, hl, ← pow_succ]
    obtain ⟨e1, e2, hn⟩ := lam_chain hW hl k (j + 1) (by omega) hT' hP' h
    refine ⟨?_, ?_, hn⟩
    · rw [show j + (k + 1) = j + 1 + k by omega, e1, List.range'_succ, List.map_cons, List.sum_cons,
        add_assoc]
    · rw [show j + (k + 1) = j + 1 + k by omega, e2]

/-- **The batching challenge and the target** (G:3722-3737): `λ` squeezed, and the target
`dot (powers λ 137)` of the ring switch's target, the claims kept (not an output lane's), the
Keccak reduction's word and the out-of-domain value. -/
theorem vsLamT_holds (h8 : σ (.n 8) = 0) (h9 : σ (.n 9) = 0) (h10 : σ (.n 10) = 0)
    (h11 : σ (.n 11) = 0) {claims : List ColumnClaim} (hcl : claims.length = 159)
    (hcol : claims.map (·.column) = Tables.claimColumns)
    (hpool : ReadsAt rd (σ (.n 6)) ((claims.take 4).map (·.value)))
    (hcew : ReadsAt rd (σ (.n 582)) (((claims.drop 4).take 153).map (·.value)))
    (hpi : ReadsAt rd (σ (.n 6) * gen ^ 157) ((claims.drop 157).map (·.value)))
    {v : E} (hv : ReadsAt rd (σ (.n 310)) [v])
    (h : Stmt.HoldsList C rd σ vsLamT next kret) :
    (⟨[σ (.n 840), σ (.n 841), σ (.n 842), σ (.n 843), σ (.n 844)], []⟩ : Fs).squeeze =
        (σ (.n 1375), ⟨[σ (.n 1370), σ (.n 1371), σ (.n 1372), σ (.n 1373), σ (.n 1374)], []⟩) ∧
      σ (.n 1917) = dot (powers (σ (.n 1375)) 137)
        (σ (.n 1361) :: ((claims.filter (fun c ↦ c.column ∉ keccakOutputColumns)).map (·.value) ++
          [σ (.n 596), v])) ∧ next := by
  simp only [vsLamT, holdsList_append] at h
  obtain ⟨hsq, h⟩ := vsSqzT_holds h8 h9 h10 h11 h
  set lam := σ (.n 1375) with hlam
  set W : ℕ → E := fun i ↦ (claims.map (·.value)).getD (vsKept i) 0 with hWdef
  have hW : ∀ i < 134, LoadHolds rd (σ (.n (vsClaimAt (vsKept i)).1)) (vsClaimAt (vsKept i)).2
      (W i) := fun i hi ↦
    claim_load hcl hpool hcew hpi (vsKept i) (by simp only [vsKept]; split <;> omega)
  rw [List.range_eq_range'] at h
  obtain ⟨e1, e2, h⟩ := lam_chain hW rfl 134 0 (T := σ (.n 1361)) (by omega) rfl
    (by simp [vsPw]) h
  rw [show vsTg (0 + 134) = 1910 from rfl] at e1
  rw [show vsPw (0 + 134) = 1911 from rfl] at e2
  obtain ⟨m12, a13, m14, l15, m16, a17, hn⟩ := h
  simp only [Atom.Holds] at m12 a13 m14 l15 m16 a17
  have h15 := loadHolds_unique l15 (hv 0 (by simp))
  refine ⟨hsq, ?_, hn⟩
  -- the kept claims' values
  have hV : (claims.filter (fun c ↦ c.column ∉ keccakOutputColumns)).map (·.value) =
      (List.range' 0 134).map W := by
    rw [filter_notLanes_eq hcol]
    apply List.ext_getElem (by simp [hcl])
    intro i h1 h2
    simp only [List.length_range', List.length_map] at h2
    simp only [List.getElem_map, List.getElem_range', W, vsKept, zero_add, Nat.one_mul]
    rw [List.getD_eq_getElem _ _ (by simp [hcl]; split <;> omega), List.getElem_map]
    by_cases hi : i < 105
    · simp only [hi, ↓reduceIte]
      rw [List.getElem_append_left (by simp [hcl]; omega), List.getElem_take]
    · simp only [hi, ↓reduceIte]
      rw [List.getElem_append_right (by simp [hcl]; omega), List.getElem_drop]
      simp only [List.length_take, hcl, show min 105 159 = 105 from rfl,
        show 130 + (i - 105) = i + 25 by omega]
  -- the powers
  have hp : powers lam 137 =
      1 :: (powersFrom (lam ^ (0 + 1)) lam 134 ++ powersFrom (lam ^ (0 + 1) * lam ^ 134) lam 2) := by
    rw [← lam_powersFrom_add, powers, show (137 : ℕ) = 136 + 1 from rfl, powersFrom, one_mul,
      zero_add, pow_one]
  have hlen : (powersFrom (lam ^ (0 + 1)) lam 134).length = ((List.range' 0 134).map W).length := by
    rw [List.length_map, List.length_range', lam_powersFrom_length]
  rw [hV, hp, lam_dot_cons, lam_dot_append hlen, lam_dot_range]
  simp only [powersFrom, dot, List.zipWith_cons_cons, List.zipWith_nil_right, List.foldl_cons,
    List.foldl_nil]
  rw [a17, a13, m16, m12, m14, e1, e2, h15]
  simp only [hlam, List.getElem_cons_zero]
  ring

end
end LeanVM.Guest.B1.VerifySub
