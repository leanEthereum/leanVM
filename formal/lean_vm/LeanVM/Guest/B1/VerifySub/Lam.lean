/-
  LeanVM.Guest.B1.VerifySub.Lam

  `verify_sub`'s batching (G:3472-3485): the challenge `λ` and the batched target.
-/

module

public import LeanVM.Guest.B1.VerifySub.Front
public import LeanVM.Guest.B1.Tables.Interface
public import LeanVM.Protocol.Keccak.Multilinear
public import LeanVM.Protocol.Keccak.Rmfe

/-!
# The batching

After `λ`'s squeeze, `vsLamT` walks the `142` claims the opening batches (the pool's `167` but
the `25` output lanes', at `112 .. 136`; `vsKept`): claim `i`'s value is read where `verify_tables`
left it (`vsClaimAt`: `claim_pool` for the bus's and the public input's, `col_eval_words` for the
tables'), and the target accumulates `λ^(i+1)·value`; then `λ^143` times the output lanes' claim. `kept_eq`: the skipped slots are exactly the claims whose column is an output
lane, so the target is the specification's
`dot (powers λ (n + 2)) (ring target :: values ++ [outputs' value])`.
-/

namespace LeanVM.Guest.B1.VerifySub

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Protocol.KeccakGkr Finset

@[expose] public section

variable {C : CallRel} {rd : Reader} {σ : Val} {next : Prop} {kret : List E → Prop}

/-! ## The batched claims -/

/-- **The batched claims are the kept ones**: the pool's claims whose column is not an output
lane are `vsKept 0, …, vsKept 139`. -/
theorem kept_eq : (List.range Tables.nClaims).filter
    (fun j ↦ Tables.claimColumns.getD j 0 ∉ keccakOutputColumns) = (List.range 142).map vsKept := by
  decide +kernel

theorem vsKept_lt {i : ℕ} (hi : i < 142) : vsKept i < Tables.nClaims := by
  unfold vsKept; show _ < 167; split <;> omega

/-- The elements of a list that pass `p`, by index. -/
theorem filter_eq_map_idx {α : Type} [Inhabited α] (p : α → Bool) : ∀ l : List α,
    l.filter p = ((List.range l.length).filter (fun j ↦ p (l.getD j default))).map
      (l.getD · default)
  | [] => rfl
  | a :: l => by
    rw [List.length_cons, List.range_succ_eq_map, List.filter_cons, List.filter_cons,
      filter_eq_map_idx p l]
    simp only [List.getD_cons_zero, List.filter_map, Function.comp_def, List.getD_cons_succ]
    split <;> simp

/-- The batched claims' values: claim `vsKept i`'s, in order. -/
theorem kept_values {claims : List ColumnClaim} (hcol : claims.map (·.column) = Tables.claimColumns) :
    (claims.filter fun c ↦ c.column ∉ keccakOutputColumns).map (·.value) =
      (List.range 142).map fun i ↦ (claims.map (·.value)).getD (vsKept i) 0 := by
  have hl : claims.length = Tables.nClaims := by
    rw [← List.length_map (f := (·.column)), hcol]; decide +kernel
  have hc : ∀ j < claims.length, (claims.getD j default).column = Tables.claimColumns.getD j 0 := by
    intro j hj
    rw [← hcol, List.getD_eq_getElem _ _ hj, List.getD_eq_getElem _ _ (by simpa using hj),
      List.getElem_map]
  rw [filter_eq_map_idx, List.filter_congr (q := fun j ↦ Tables.claimColumns.getD j 0 ∉
      keccakOutputColumns) fun j hj ↦ by
    rw [hc j (List.mem_range.1 hj)], hl, kept_eq, List.map_map, List.map_map]
  refine List.map_congr_left fun i hi ↦ ?_
  have hk := vsKept_lt (List.mem_range.1 hi)
  simp only [Function.comp_apply]
  rw [List.getD_eq_getElem _ _ (by rw [hl]; exact hk), List.getD_eq_getElem _ _ (by simp [hl, hk]),
    List.getElem_map]

/-! ## The target -/

theorem lam_powersFrom_length (acc base : E) : ∀ n, (powersFrom acc base n).length = n
  | 0 => rfl
  | n + 1 => by rw [powersFrom, List.length_cons, lam_powersFrom_length _ base n]

/-- `dot (powers λ (m + 2)) (T :: f₀ … f_{m-1} ++ [x]) = T + Σ λ^(i+1) f_i + λ^(m+1) x`. -/
theorem dot_powers_batch (lam T x : E) (m : ℕ) (f : ℕ → E) :
    dot (powers lam (m + 2)) (T :: ((List.range m).map f ++ [x])) =
      T + ∑ i ∈ range m, lam ^ (i + 1) * f i + lam ^ (m + 1) * x := by
  have hlen : (powers lam (m + 2)).length = m + 2 := lam_powersFrom_length _ _ _
  rw [dot_eq _ _ (by simp [hlen]), hlen, Finset.sum_range_succ, Finset.sum_range_succ',
    powers_getD lam (by omega : 0 < m + 2), powers_getD lam (by omega : m + 1 < m + 2)]
  have hmid : ∀ i ∈ range m, (powers lam (m + 2)).getD (i + 1) 0 *
      (T :: ((List.range m).map f ++ [x])).getD (i + 1) 0 = lam ^ (i + 1) * f i := by
    intro i hi
    have hi' := List.mem_range.1 hi
    rw [powers_getD lam (by omega), List.getD_cons_succ,
      List.getD_eq_getElem _ _ (by simp; omega), List.getElem_append_left (by simpa using hi'),
      List.getElem_map, List.getElem_range]
  rw [Finset.sum_congr rfl hmid, List.getD_cons_succ, List.getD_cons_zero,
    List.getD_eq_getElem _ _ (by simp), List.getElem_append_right (by simp)]
  simp only [List.length_map, List.length_range, Nat.sub_self, List.getElem_cons_zero, pow_zero,
    one_mul]
  ring

/-! ## Where the batched values are -/

/-- **The pooled values where the batching reads them**: claim `j`'s at `vsClaimAt j`, from
`verify_tables`' three reads (the bus's in `claim_pool`, the tables' at `col_eval_words`, the
public input's at `claim_pool·g^164`). -/
theorem claimAt_reads {claims : List ColumnClaim} (hl : claims.length = Tables.nClaims)
    (hp : ReadsAt rd (σ (.n 6)) ((claims.take Tables.nBusClaims).map (·.value)))
    (hc : ReadsAt rd (σ (.n 645))
      (((claims.drop Tables.nBusClaims).take Tables.nColEvals).map (·.value)))
    (hq : ReadsAt rd (σ (.n 6) * gen ^ Tables.nPooled) ((claims.drop Tables.nPooled).map (·.value))) :
    ∀ j < Tables.nClaims, LoadHolds rd (σ (.n (vsClaimAt j).1)) (vsClaimAt j).2
      ((claims.map (·.value)).getD j 0) := by
  have e1 : Tables.nClaims = 167 := rfl
  have e2 : Tables.nBusClaims = 5 := rfl
  have e3 : Tables.nColEvals = 159 := rfl
  have e4 : Tables.nPooled = 164 := rfl
  rw [e1] at hl ⊢
  rw [e2, e3] at hc
  rw [e2] at hp
  rw [e4] at hq
  intro j hj
  have hj' : j < claims.length := by rw [hl]; exact hj
  rw [List.getD_eq_getElem _ _ (by simpa using hj'), List.getElem_map]
  unfold vsClaimAt
  split_ifs with h
  · have := hc (j - 5) (by simp only [List.length_map, List.length_take, List.length_drop, hl]; omega)
    simp only [List.getElem_map, List.getElem_take, List.getElem_drop] at this
    have e : claims[5 + (j - 5)]'(by omega) = claims[j] := by congr 1; omega
    rwa [e] at this
  · by_cases h5 : j < 5
    · have := hp j (by simp only [List.length_map, List.length_take, hl]; omega)
      simpa only [List.getElem_map, List.getElem_take] using this
    · obtain ⟨k, rfl⟩ : ∃ k, j = 164 + k := ⟨j - 164, by omega⟩
      have := hq k (by simp only [List.length_map, List.length_drop, hl]; omega)
      rw [loadHolds_mul_gen_pow] at this
      simpa only [List.getElem_map, List.getElem_drop, show 164 + k - 164 = k by omega] using this

/-! ## The walk -/

theorem vsPw_succ (n : ℕ) : vsPw (n + 1) = 1115 + 4 * n := by
  simp only [vsPw, Nat.add_one_ne_zero, ↓reduceIte]; omega

theorem vsTg_succ (n : ℕ) : vsTg (n + 1) = 1114 + 4 * n := by
  simp only [vsTg, Nat.add_one_ne_zero, ↓reduceIte]; omega

/-- The first `n` batched claims: the power `λ^(n+1)`, the target. -/
theorem lam_loop {lam T : E} {vals : List E} (hlam : σ (.n 1111) = lam) (hT : σ (.n 1091) = T)
    (hval : ∀ j < Tables.nClaims, LoadHolds rd (σ (.n (vsClaimAt j).1)) (vsClaimAt j).2
      (vals.getD j 0)) :
    ∀ n ≤ 142, ∀ {nx : Prop}, Stmt.HoldsList C rd σ ((List.range n).flatMap vsLamStep) nx kret →
      σ (.n (vsPw n)) = lam ^ (n + 1) ∧
      σ (.n (vsTg n)) = T + ∑ i ∈ range n, lam ^ (i + 1) * vals.getD (vsKept i) 0 ∧ nx
  | 0, _, nx, h => ⟨by simp [vsPw, hlam], by simp [vsTg, hT], h⟩
  | n + 1, hn, nx, h => by
    rw [List.range_succ, List.flatMap_append, holdsList_append] at h
    obtain ⟨hp, ht, h⟩ := lam_loop hlam hT hval n (by omega) h
    simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, vsLamStep, Stmt.HoldsList,
      Stmt.Holds, Atom.Holds, vsLd, vsMul, vsAdd] at h
    obtain ⟨ld, m1, a1, m2, h⟩ := h
    have hv : σ (.n (1112 + 4 * n)) = vals.getD (vsKept n) 0 :=
      loadHolds_unique ld (hval _ (vsKept_lt (by omega)))
    refine ⟨?_, ?_, h⟩
    · rw [vsPw_succ, m2, hp, hlam]; ring
    · rw [vsTg_succ, a1, ht, m1, hp, hv, Finset.sum_range_succ]; ring

/-- **The batching** (G:3472-3485), after `λ`'s squeeze (`hsq`, the squeeze's facts `SQ`):
`λ^143` at `1679`, and the batched target at `1681`. -/
theorem vsLamT_holds_of {SQ : Prop}
    (hsq : ∀ {nx : Prop}, Stmt.HoldsList C rd σ (vsSqzT 754 1092) nx kret → SQ ∧ nx)
    {claims : List ColumnClaim} (hcol : claims.map (·.column) = Tables.claimColumns)
    (hval : ∀ j < Tables.nClaims, LoadHolds rd (σ (.n (vsClaimAt j).1)) (vsClaimAt j).2
      ((claims.map (·.value)).getD j 0))
    (h : Stmt.HoldsList C rd σ vsLamT next kret) :
    SQ ∧ σ (.n 1679) = σ (.n 1111) ^ 143 ∧
    σ (.n 1681) = dot (powers (σ (.n 1111))
      ((claims.filter fun c ↦ c.column ∉ keccakOutputColumns).length + 2))
      (σ (.n 1091) :: ((claims.filter fun c ↦ c.column ∉ keccakOutputColumns).map (·.value) ++
        [σ (.n 657)])) ∧ next := by
  unfold vsLamT at h
  rw [holdsList_append, holdsList_append] at h
  obtain ⟨hS, h⟩ := hsq h
  obtain ⟨hp, ht, h⟩ := lam_loop rfl rfl hval 142 le_rfl h
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds, vsMul, vsAdd] at h
  obtain ⟨m, a, h⟩ := h
  have hv := kept_values hcol
  have hfl : (claims.filter fun c ↦ c.column ∉ keccakOutputColumns).length = 142 := by
    rw [← List.length_map (f := (·.value)), hv, List.length_map, List.length_range]
  rw [show vsTg 142 = 1678 from rfl] at ht
  rw [show vsPw 142 = 1679 from rfl] at hp
  refine ⟨hS, hp, ?_, h⟩
  rw [hv, hfl, dot_powers_batch, a, m, ht, hp]

/-- **The batching** (G:3472-3485): `λ`'s squeeze, `λ^143` at `1679`, and the batched target at
`1681`. -/
theorem vsLamT_holds (h10 : σ (.n 8) = 0) (h11 : σ (.n 9) = 0) (h12 : σ (.n 10) = 0)
    (h13 : σ (.n 11) = 0) {claims : List ColumnClaim}
    (hcol : claims.map (·.column) = Tables.claimColumns)
    (hval : ∀ j < Tables.nClaims, LoadHolds rd (σ (.n (vsClaimAt j).1)) (vsClaimAt j).2
      ((claims.map (·.value)).getD j 0))
    (h : Stmt.HoldsList C rd σ vsLamT next kret) :
    (⟨[σ (.n 754), σ (.n 755), σ (.n 756), σ (.n 757), σ (.n 758)], []⟩ : Fs).squeeze =
      (σ (.n 1111), ⟨[σ (.n 1100), σ (.n 1101), σ (.n 1102), σ (.n 1103), σ (.n 1104)], []⟩) ∧
    σ (.n 1679) = σ (.n 1111) ^ 143 ∧
    σ (.n 1681) = dot (powers (σ (.n 1111))
      ((claims.filter fun c ↦ c.column ∉ keccakOutputColumns).length + 2))
      (σ (.n 1091) :: ((claims.filter fun c ↦ c.column ∉ keccakOutputColumns).map (·.value) ++
        [σ (.n 657)])) ∧ next :=
  vsLamT_holds_of (fun hs ↦ vsSqzT_holds (capb := 754) (o := 1092) h10 h11 h12 h13 hs) hcol hval h

end
end LeanVM.Guest.B1.VerifySub
