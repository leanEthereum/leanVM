/-
  LeanVM.Guest.B1.Opening.QueriesComplete2

  The completeness of a query's leaf hash: its blocks hold at the honest values, and its digest
  is the row's.
-/

module

public import LeanVM.Guest.B1.Opening.QueriesComplete1

/-!
# A query's leaf hash, completeness

`oqLeaf_complete`: with `σ` honest on the query's range and the padding run `1, 0, 0, 0, 0`, every
`XOR` and `KECCAK` of the leaf hash holds (the blocks' inputs canonical, their outputs the
permutation's by the honest values' definition); `oqLeaf_digest`: its digest cells are then
`digestHalves (merkleLeafDigest row)` (`oqLeaf_sound`).
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Guest.Value.Keccak
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

theorem canonical_add {a b : E} (ha : IsCanonical128 a) (hb : IsCanonical128 b) :
    IsCanonical128 (a + b) := by
  unfold IsCanonical128 at *
  rw [limb_add, ha, hb, add_zero]

theorem canonical_ofLimbs (a b : K) : IsCanonical128 (E.ofLimbs a b 0) :=
  (isCanonical128_ofLimbs_iff _ _ _).mpr rfl

theorem canonical_word (a b : ℕ) : IsCanonical128 (word a b 0) := canonical_ofLimbs _ _

theorem canonical_zero : IsCanonical128 (0 : E) := by
  rw [zero_eq_ofLimbs]; exact canonical_ofLimbs _ _

theorem fin13_ofNat {c : ℕ} (hc : c < 13) : Fin.ofNat 13 c = ⟨c, hc⟩ :=
  Fin.ext (Nat.mod_eq_of_lt hc)

namespace QD

variable (d : QD) {rd : Reader} {σ : Val}

theorem pk_canonical (j : ℕ) : IsCanonical128 (d.pk j) := by rw [pk_eq]; exact canonical_ofLimbs _ _

theorem P_canonical (m : ℕ) : IsCanonical128 (d.P m) := by
  unfold P oqW80
  split
  · exact d.pk_canonical m
  · split
    · exact canonical_word _ _
    · split <;> exact canonical_word _ _

theorem leafO_canonical (k : ℕ) (c : Fin 13) : IsCanonical128 (d.leafO k c) := by
  cases k with
  | zero => exact canonical_zero
  | succ k => exact cellsOfState_canonical _ _ _

theorem leafI_canonical (k : ℕ) (c : Fin 13) : IsCanonical128 (d.leafI k c) := by
  unfold leafI
  split
  · split
    · exact d.P_canonical _
    · exact canonical_zero
  · split
    · exact canonical_add (d.leafO_canonical _ _) (d.P_canonical _)
    · exact d.leafO_canonical _ _

/-- The leaf's blocks, decoded. -/
theorem leafV_block (hs : d.s.RowShape) {k r : ℕ} (hk1 : 1 ≤ k) (hk : k < d.s.B)
    (hr : r < (if k + 1 = d.s.B then 23 else 22)) :
    d.leafV (13 + (k - 1) * 22 + r) =
      if k + 1 = d.s.B then
        (if r < 8 then d.leafI k (Fin.ofNat 13 r)
          else if r = 8 then oqW80 d.s
          else if r = 9 then d.leafI k 8
          else d.leafO (k + 1) (Fin.ofNat 13 (r - 10)))
      else (if r < 9 then d.leafI k (Fin.ofNat 13 r) else d.leafO (k + 1) (Fin.ofNat 13 (r - 9))) := by
  have hB : d.s.B = 4 ∨ d.s.B = 3 := by
    rcases shape_nums hs with h | h
    · exact Or.inl h.2.2.2.2.2.2.2.2.1
    · exact Or.inr h.2.2.2.2.2.2.2.2.1
  unfold leafV
  have hm : min ((13 + (k - 1) * 22 + r - 13) / 22 + 1) (d.s.B - 1) = k := by
    split at hr <;> omega
  simp only [show ¬ 13 + (k - 1) * 22 + r < 13 by omega, ↓reduceIte, hm,
    show 13 + (k - 1) * 22 + r - (13 + (k - 1) * 22) = r by omega]

theorem oqBs_eq {kL k : ℕ} (hk : 1 ≤ k) : oqBs kL k = kL + (13 + (k - 1) * 22) := by
  simp [oqBs, show k ≠ 0 by omega]; omega

/-- **The leaf hash holds at the honest values.** -/
theorem oqLeaf_complete (hs : d.s.RowShape)
    (hv : ∀ i, d.b ≤ i → i < d.e → σ (.n i) = d.val i)
    (hpad : σ (.n d.prV) = word 1 0) (hz : ∀ i < 4, σ (.n (d.prV + 1 + i)) = word 0 0) :
    ∀ a, Stmt.atom a ∈ oqLeafT d.s d.b d.prV d.kL → a.Holds rd σ := by
  obtain ⟨p1, p2, p3, p4, p5⟩ := d.places
  have hk := k1_eq d
  have hL := leafShape_of d.s hs
  have hnums : (d.s.ncells = 32 ∧ d.s.B = 4 ∧ d.s.chainLen = 69 ∧ d.s.R = 64) ∨
      (d.s.ncells = 24 ∧ d.s.B = 3 ∧ d.s.chainLen = 47 ∧ d.s.R = 48) := by
    rcases shape_nums hs with h | h
    · exact Or.inl ⟨h.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2.2, h.2.2.2.2.2.1⟩
    · exact Or.inr ⟨h.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2.2, h.2.2.2.2.2.1⟩
  have hncR : d.s.ncells = d.s.R / 2 := rfl
  -- σ on the packed cells, on the outputs, on the inputs
  have spk : ∀ m < d.s.ncells, σ (.n (oqPk d.b d.s.R m)) = d.pk m := fun m hm => by
    rw [show oqPk d.b d.s.R m = d.b + d.s.R + 3 * m + 2 by simp [oqPk],
      hv _ (by omega) (by omega), val_pack d (by omega) (by omega)]
    rfl
  have sP : ∀ m < d.s.ncells, σ (.n (oqPk d.b d.s.R m)) = d.P m := fun m hm => by
    rw [spk m hm, P]; simp [hm]
  have sleaf : ∀ i < d.s.chainLen, σ (.n (d.kL + i)) = d.leafV i := fun i hi => by
    rw [hv _ (by omega) (by omega), val_leaf d hi]
  have sout : ∀ k < d.s.B, ∀ c (hc : c < 13), (k + 1 < d.s.B ∨ c < 2) →
      σ (.n (oqOut d.s d.kL k c)) = d.leafO (k + 1) ⟨c, hc⟩ :=
    fun k hk c hc hc2 => by
      rcases Nat.eq_zero_or_pos k with rfl | hpos
      · rw [show oqOut d.s d.kL 0 c = d.kL + c by simp [oqOut], sleaf c (by omega)]
        unfold leafV
        simp only [hc, ↓reduceIte, fin13_ofNat hc]
      · by_cases hlast : k + 1 = d.s.B
        · rw [show oqOut d.s d.kL k c = d.kL + (13 + (k - 1) * 22 + (10 + c)) by
            simp only [oqOut, show k ≠ 0 by omega, hlast, ↓reduceIte]; rw [oqBs_eq (by omega)]; omega,
            sleaf _ (by rcases hnums with h | h <;> omega),
            leafV_block d hs (by omega) hk (by simp only [hlast, ↓reduceIte]; omega)]
          simp only [hlast, ↓reduceIte, show ¬ 10 + c < 8 by omega, show 10 + c ≠ 8 by omega,
            show 10 + c ≠ 9 by omega, show 10 + c - 10 = c by omega, fin13_ofNat hc]
        · rw [show oqOut d.s d.kL k c = d.kL + (13 + (k - 1) * 22 + (9 + c)) by
            simp only [oqOut, show k ≠ 0 by omega, hlast, ↓reduceIte]; rw [oqBs_eq (by omega)]; omega,
            sleaf _ (by rcases hnums with h | h <;> omega),
            leafV_block d hs (by omega) hk (by simp only [hlast, ↓reduceIte]; omega)]
          simp only [hlast, ↓reduceIte, show ¬ 9 + c < 9 by omega, show 9 + c - 9 = c by omega,
            fin13_ofNat hc]
  have sin : ∀ k, 1 ≤ k → k < d.s.B → ∀ c (hc : c < 9),
      σ (.n (oqIn d.s d.kL k c)) = d.leafI k ⟨c, by omega⟩ := fun k hk1 hk c hc => by
    by_cases hlast : k + 1 = d.s.B
    · by_cases h8 : c < 8
      · rw [show oqIn d.s d.kL k c = d.kL + (13 + (k - 1) * 22 + c) by
          simp only [oqIn, show 17 * k / 2 + c ≤ d.s.ncells by
            have := hL.last; have : k = d.s.B - 1 := by omega
            subst this; omega, ↓reduceIte]; rw [oqBs_eq hk1]; omega,
          sleaf _ (by rcases hnums with h | h <;> omega),
          leafV_block d hs hk1 hk (by simp only [hlast, ↓reduceIte]; omega)]
        simp only [hlast, h8, ↓reduceIte, fin13_ofNat (show c < 13 by omega)]
      · obtain rfl : c = 8 := by omega
        rw [show oqIn d.s d.kL k 8 = d.kL + (13 + (k - 1) * 22 + 9) by
          simp only [oqIn, show ¬ 17 * k / 2 + 8 ≤ d.s.ncells by
            have := hL.last; have : k = d.s.B - 1 := by omega
            subst this; omega, ↓reduceIte]; rw [oqBs_eq hk1]; omega,
          sleaf _ (by rcases hnums with h | h <;> omega),
          leafV_block d hs hk1 hk (by simp only [hlast, ↓reduceIte]; omega)]
        simp only [hlast, ↓reduceIte]; rfl
    · rw [show oqIn d.s d.kL k c = d.kL + (13 + (k - 1) * 22 + c) by
        simp only [oqIn, show 17 * k / 2 + c ≤ d.s.ncells by
          have := hL.mid k (by omega); omega, ↓reduceIte]; rw [oqBs_eq hk1]; omega,
        sleaf _ (by rcases hnums with h | h <;> omega),
        leafV_block d hs hk1 hk (by simp only [hlast, ↓reduceIte]; omega)]
      simp only [hlast, hc, ↓reduceIte, fin13_ofNat (show c < 13 by omega)]
  have hz' : ∀ i < 4, σ (.n (d.prV + 1 + i)) = 0 := fun i hi => by rw [hz i hi, word_zero]
  have hoN : ∀ k < d.s.B, ∀ c < oqOutN d.s k, k + 1 < d.s.B ∨ c < 2 := fun k hk c hc => by
    unfold oqOutN at hc; split_ifs at hc <;> omega
  intro a ha
  simp only [oqLeafT, List.mem_flatten, List.mem_map, List.mem_range] at ha
  obtain ⟨_, ⟨k, hk, rfl⟩, ha⟩ := ha
  unfold oqBlockT at ha
  split at ha
  · -- block 0
    rename_i hk0
    subst hk0
    simp only [List.mem_cons, List.not_mem_nil, or_false, Stmt.atom.injEq] at ha
    subst ha
    have eI : cells13 ((((List.range 9).map fun c ↦ V.n (oqPk d.b d.s.R c)) ++
        [V.n (d.prV + 1), V.n (d.prV + 2), V.n (d.prV + 3), V.n (d.prV + 4)]).map σ) = d.leafI 0 := by
      funext c
      rw [show ([.n (d.prV + 1), .n (d.prV + 2), .n (d.prV + 3), .n (d.prV + 4)] : List V) =
          (List.range 4).map fun c ↦ V.n (d.prV + 1 + c) by simp [List.range_succ],
        cells13_block]
      by_cases hc : c.val < 9
      · simp only [hc, ↓reduceIte, leafI]; rw [sP _ (by omega)]
      · simp only [hc, ↓reduceIte, leafI]; rw [hz' _ (by omega)]
    refine keccak_holds_of (O := d.leafO 1) (oc := if 0 + 1 = d.s.B then .two else .all) (by simp)
      ?_ ⟨?_, fun c _ => ?_⟩ fun c hc => ?_
    · simp only [List.length_map, List.length_range, oqOutN]; split <;> rfl
    · rw [eI]; exact d.leafI_canonical 0
    · rw [eI]; rfl
    · simp only [List.getElem_map, List.getElem_range]
      exact sout 0 (by omega) c.val c.isLt (hoN 0 (by omega) c.val (by simpa using hc))
  · rename_i hk0
    simp only [List.mem_append, List.mem_flatten, List.mem_map, List.mem_range] at ha
    rcases ha with ⟨_, ⟨c, hc, rfl⟩, ha⟩ | ha
    · -- the XORs
      have hsum := sin k (by omega) hk c hc
      unfold oqXorT at ha
      dsimp only at ha
      split at ha
      · rename_i hm
        simp only [List.mem_cons, List.not_mem_nil, or_false, Stmt.atom.injEq] at ha
        subst ha
        show σ _ = σ _ + σ _
        have e : oqBs d.kL k + c = oqIn d.s d.kL k c := by simp [oqIn, show 17 * k / 2 + c ≤ d.s.ncells by omega]
        rw [e, hsum, sout (k - 1) (by omega) c (by omega) (by omega), sP _ hm, leafI]
        simp [hk0, hc, show k - 1 + 1 = k by omega]
      · split at ha
        · rename_i hm hm'
          simp only [List.mem_cons, List.not_mem_nil, or_false, Stmt.atom.injEq] at ha
          subst ha
          show σ _ = σ _ + σ _
          have e : oqBs d.kL k + c = oqIn d.s d.kL k c := by simp [oqIn, show 17 * k / 2 + c ≤ d.s.ncells by omega]
          rw [e, hsum, sout (k - 1) (by omega) c (by omega) (by omega), hpad, leafI]
          simp [hk0, hc, show k - 1 + 1 = k by omega, P, hm']
        · rename_i hm hm'
          have hlast : k + 1 = d.s.B := by
            by_contra hne
            have := hL.mid k (by omega); omega
          have hc8 : c = 8 := by have := hL.last; omega
          subst hc8
          have hw : σ (.n (oqBs d.kL k + 8)) = oqW80 d.s := by
            rw [oqBs_eq (by omega), show d.kL + (13 + (k - 1) * 22) + 8 = d.kL + (13 + (k - 1) * 22 + 8) by
              omega, sleaf _ (by rcases hnums with h | h <;> omega),
              leafV_block d hs (by omega) hk (by simp only [hlast, ↓reduceIte]; omega)]
            simp [hlast]
          simp only [List.mem_cons, List.not_mem_nil, or_false, Stmt.atom.injEq] at ha
          rcases ha with rfl | rfl
          · exact hw
          · show σ _ = σ _ + σ _
            have e : oqBs d.kL k + 8 + 1 = oqIn d.s d.kL k 8 := by
              simp [oqIn, show ¬ 17 * k / 2 + 8 ≤ d.s.ncells by omega]
            rw [e, hsum, sout (k - 1) (by omega) 8 (by omega) (by omega), hw, leafI]
            simp [hk0, show k - 1 + 1 = k by omega, P, hm, hm']
    · -- the permutation
      simp only [List.mem_cons, List.not_mem_nil, or_false, Stmt.atom.injEq] at ha
      subst ha
      have eI : cells13 ((((List.range 9).map fun c ↦ V.n (oqIn d.s d.kL k c)) ++
          ((List.range 4).map fun c ↦ V.n (oqOut d.s d.kL (k - 1) (9 + c)))).map σ) = d.leafI k := by
        funext c
        rw [cells13_block]
        split
        · rename_i hc; exact sin k (by omega) hk c.val hc
        · rename_i hc
          rw [sout (k - 1) (by omega) _ (by omega) (by omega), show k - 1 + 1 = k by omega, leafI]
          simp only [hk0, hc, ↓reduceIte]
          congr 1; ext; simp; omega
      refine keccak_holds_of (O := d.leafO (k + 1)) (oc := if k + 1 = d.s.B then .two else .all)
        (by simp) ?_ ⟨?_, fun c _ => ?_⟩ fun c hc => ?_
      · simp only [List.length_map, List.length_range, oqOutN]; split <;> rfl
      · rw [eI]; exact d.leafI_canonical k
      · rw [eI]; rfl
      · simp only [List.getElem_map, List.getElem_range]
        exact sout k hk c.val c.isLt (hoN k hk c.val (by simpa using hc))

end QD

end
end LeanVM.Guest.B1
