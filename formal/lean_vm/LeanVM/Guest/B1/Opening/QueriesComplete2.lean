/-
  LeanVM.Guest.B1.Opening.QueriesComplete2

  The completeness of a query's leaf hash: its blocks hold at the honest values, and its digest
  is the row's.
-/

module

public import LeanVM.Guest.B1.Opening.QueriesHonest

/-!
# A query's leaf hash, completeness

`oqLeaf_complete`: with `σ` honest on the query's range and the padding run `1, 0, 0, 0, 0`, every
`XOR` and `KECCAK` of the leaf hash holds (the blocks' outputs the permutation's by the honest
values' definition); `oqLeaf_digest`: its digest cells are then `digestHalves (merkleLeafDigest
row)` (`oqLeaf_sound`).
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Guest.Value.Keccak
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

theorem fin13_ofNat {c : ℕ} (hc : c < 13) : Fin.ofNat 13 c = ⟨c, hc⟩ :=
  Fin.ext (Nat.mod_eq_of_lt hc)

/-- The row shapes' numbers. -/
theorem shape_nums {s : Oq} (hs : s.RowShape) :
    (s.base = 1 ∧ s.I = 64 ∧ s.ncells = 32 ∧ s.B = 4 ∧ s.chainLen = 69 ∧ s.lc = 33) ∨
    (s.base = 0 ∧ s.I = 16 ∧ s.ncells = 16 ∧ s.B = 2 ∧ s.chainLen = 25 ∧ s.lc = 16) := by
  rcases hs with ⟨hb, hI⟩ | ⟨hb, hI⟩
  · left; simp [Oq.ncells, Oq.B, Oq.chainLen, Oq.lc, Oq.I, rate, hb, hI]
  · right; simp [Oq.ncells, Oq.B, Oq.chainLen, Oq.lc, Oq.I, rate, hb, hI]

theorem oqTwo_iff (s : Oq) (k c : ℕ) :
    oqTwo s k c = true ↔ s.ncells < 17 * k / 2 + c ∨ (17 * k / 2 + c = s.ncells ∧ c = 8) := by
  simp [oqTwo]

theorem oqBs_eq {kL k : ℕ} (hk : 1 ≤ k) : oqBs kL k = kL + (13 + (k - 1) * 22) := by
  simp [oqBs, show k ≠ 0 by omega]; omega

/-- `novel_eval`'s levels end after they start. -/
theorem le_nvLevelsT {ws : ℕ → ℕ} (c i : ℕ) (ins : List ℕ) (k : ℕ) :
    k ≤ (nvLevelsT ws c i ins k).2.2 := by
  rw [QD.nvLevelsT_next (fun _ ↦ (0 : E)) c i ins (ins.map fun _ ↦ (0 : E)) k (by simp)]
  omega

namespace QD

variable (d : QD) {rd : Reader} {σ : Val}

/-- The fold starts before the query's end. -/
theorem ch_lt_e : d.ch < d.e := by
  have hv : d.ch ≤ oqVal d.s d.ch := by simp only [oqVal, oqAcc, oqRO, d.oqRK_eq]; omega
  have hr : oqVal d.s d.ch ≤ oqRes d.s d.b d.emit := by
    unfold oqRes
    split
    · exact Nat.le_trans (Nat.le_add_right _ (2 + 3 * d.s.mu + 4 * (d.s.nHs / 2)))
        (by rw [← Nat.add_assoc, ← Nat.add_assoc]; exact le_nvLevelsT _ _ _ _)
    · exact le_rfl
  show d.ch < oqRes d.s d.b d.emit + 1
  omega

/-- The leaf hash's values lie in the query. -/
theorem leaf_lt_e {i : ℕ} (hi : i < d.s.chainLen) : d.b ≤ d.kL + i ∧ d.kL + i < d.e := by
  have h1 := d.ch_lt_e
  have h2 := d.ch_eq
  have h3 := d.kL_eq
  have h4 := d.k1_eq
  rw [leafVals_length] at h2
  omega

/-- The leaf's cells: `σ` at `oqPk` is the leaf cell `pk`. -/
theorem pk_val (hs : d.s.RowShape) (hv : d.Hv σ) {m : ℕ} (hm : m < d.s.ncells) :
    σ (.n (oqPk d.s d.b m)) = d.pk m := by
  have h1 := d.ch_lt_e
  have h2 := d.ch_eq
  have h3 := d.kL_eq
  have h4 := d.k1_eq
  rw [leafVals_length] at h2
  rw [rowVals_length, packVals_length] at h4
  rcases shape_nums hs with ⟨hb, hI, hn, -⟩ | ⟨hb, hI, hn, -⟩
  · rw [show oqPk d.s d.b m = d.b + d.s.I + 3 * m + 2 by simp [oqPk, hb],
      hv _ (by omega) (by simp only [hb, ↓reduceIte] at h4; omega),
      val_pack d hb (by omega) (by omega)]
    rfl
  · rw [show oqPk d.s d.b m = d.b + m by simp [oqPk, hb],
      hv _ (by omega) (by simp only [hb] at h4; omega), val_row d (by omega)]
    simp [cell, pk, hb]

/-- The leaf's blocks, decoded. -/
theorem leafV_block (hs : d.s.RowShape) {k r : ℕ} (hk1 : 1 ≤ k) (hk : k < d.s.B)
    (hr : r < (if k + 1 = d.s.B then 23 else 22)) :
    d.leafV (13 + (k - 1) * 22 + r) =
      if k + 1 = d.s.B then
        (if r < 8 then d.leafI k (Fin.ofNat 13 r)
          else if r = 8 then d.P d.s.lc
          else if r = 9 then d.leafI k 8
          else d.leafO (k + 1) (Fin.ofNat 13 (r - 10)))
      else (if r < 9 then d.leafI k (Fin.ofNat 13 r) else d.leafO (k + 1) (Fin.ofNat 13 (r - 9))) := by
  have hB : d.s.B = 4 ∨ d.s.B = 2 := by
    rcases shape_nums hs with h | h
    · exact Or.inl h.2.2.2.1
    · exact Or.inr h.2.2.2.1
  unfold leafV
  have hm : min ((13 + (k - 1) * 22 + r - 13) / 22 + 1) (d.s.B - 1) = k := by
    split at hr <;> omega
  simp only [show ¬ 13 + (k - 1) * 22 + r < 13 by omega, ↓reduceIte, hm,
    show 13 + (k - 1) * 22 + r - (13 + (k - 1) * 22) = r by omega]

/-- **The leaf hash holds at the honest values.** -/
theorem oqLeaf_complete (hs : d.s.RowShape) (hv : d.Hv σ)
    (hpad : σ (.n d.prV) = word 1 0) (hz : ∀ i < 4, σ (.n (d.prV + 1 + i)) = word 0 0) :
    ∀ a, Stmt.atom a ∈ oqLeafT d.s d.b d.prV d.kL → a.Holds rd σ := by
  have hL := leafShape_of d.s hs
  have hnums : (d.s.ncells = 32 ∧ d.s.B = 4 ∧ d.s.chainLen = 69 ∧ d.s.lc = 33) ∨
      (d.s.ncells = 16 ∧ d.s.B = 2 ∧ d.s.chainLen = 25 ∧ d.s.lc = 16) := by
    rcases shape_nums hs with h | h
    · exact Or.inl ⟨h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2⟩
    · exact Or.inr ⟨h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2⟩
  have hlc : d.s.lc = 17 * (d.s.B - 1) / 2 + 8 := rfl
  -- σ on the leaf cells, on the outputs, on the inputs
  have sP : ∀ m < d.s.ncells, σ (.n (oqPk d.s d.b m)) = d.P m := fun m hm => by
    rw [d.pk_val hs hv hm, P]; simp [hm]
  have sleaf : ∀ i < d.s.chainLen, σ (.n (d.kL + i)) = d.leafV i := fun i hi => by
    obtain ⟨h1, h2⟩ := d.leaf_lt_e hi
    rw [hv _ h1 h2, val_leaf d hi]
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
  -- which input cells take two values: only the last block's cell `8`
  have two_iff : ∀ k, 1 ≤ k → k < d.s.B → ∀ c < 9,
      (oqTwo d.s k c = true ↔ (k + 1 = d.s.B ∧ c = 8)) := fun k hk1 hk c hc => by
    rw [oqTwo_iff]
    by_cases hlast : k + 1 = d.s.B
    · have : 17 * k / 2 + 8 = d.s.lc := by rw [hlc, show d.s.B - 1 = k by omega]
      have := hL.last
      constructor
      · intro h; refine ⟨hlast, ?_⟩; omega
      · intro h; omega
    · have := hL.mid k (by omega)
      constructor
      · intro h; omega
      · intro h; omega
  have sin : ∀ k, 1 ≤ k → k < d.s.B → ∀ c (hc : c < 9),
      σ (.n (oqIn d.s d.kL k c)) = d.leafI k ⟨c, by omega⟩ := fun k hk1 hk c hc => by
    by_cases hlast : k + 1 = d.s.B
    · by_cases h8 : c < 8
      · have ht : oqTwo d.s k c = false := by
          rw [← Bool.not_eq_true, two_iff k hk1 hk c hc]; omega
        rw [show oqIn d.s d.kL k c = d.kL + (13 + (k - 1) * 22 + c) by
            simp only [oqIn, ht, Bool.false_eq_true, ↓reduceIte]; rw [oqBs_eq hk1]; omega,
          sleaf _ (by rcases hnums with h | h <;> omega),
          leafV_block d hs hk1 hk (by simp only [hlast, ↓reduceIte]; omega)]
        simp only [hlast, h8, ↓reduceIte, fin13_ofNat (show c < 13 by omega)]
      · obtain rfl : c = 8 := by omega
        have ht : oqTwo d.s k 8 = true := (two_iff k hk1 hk 8 (by omega)).mpr ⟨hlast, rfl⟩
        rw [show oqIn d.s d.kL k 8 = d.kL + (13 + (k - 1) * 22 + 9) by
            simp only [oqIn, ht, ↓reduceIte]; rw [oqBs_eq hk1]; omega,
          sleaf _ (by rcases hnums with h | h <;> omega),
          leafV_block d hs hk1 hk (by simp only [hlast, ↓reduceIte]; omega)]
        simp only [hlast, ↓reduceIte]; rfl
    · have ht : oqTwo d.s k c = false := by
        rw [← Bool.not_eq_true, two_iff k hk1 hk c hc]; omega
      rw [show oqIn d.s d.kL k c = d.kL + (13 + (k - 1) * 22 + c) by
          simp only [oqIn, ht, Bool.false_eq_true, ↓reduceIte]; rw [oqBs_eq hk1]; omega,
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
    have eI : cells13 ((((List.range 9).map fun c ↦ V.n (oqPk d.s d.b c)) ++
        [V.n (d.prV + 1), V.n (d.prV + 2), V.n (d.prV + 3), V.n (d.prV + 4)]).map σ) = d.leafI 0 := by
      funext c
      rw [show ([.n (d.prV + 1), .n (d.prV + 2), .n (d.prV + 3), .n (d.prV + 4)] : List V) =
          (List.range 4).map fun c ↦ V.n (d.prV + 1 + c) by simp [List.range_succ],
        cells13_block]
      by_cases hc : c.val < 9
      · simp only [hc, ↓reduceIte, leafI]
        rw [sP _ (by rcases hnums with h | h <;> omega)]
      · simp only [hc, ↓reduceIte, leafI]; rw [hz' _ (by omega)]
    refine keccak_holds_of (O := d.leafO 1) (oc := if 0 + 1 = d.s.B then .two else .all) (by simp)
      ?_ (fun c _ => ?_) fun c hc => ?_
    · simp only [List.length_map, List.length_range, oqOutN]; split <;> rfl
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
        have ht : oqTwo d.s k c = false := by
          rw [← Bool.not_eq_true, oqTwo_iff]; omega
        have e : oqBs d.kL k + c = oqIn d.s d.kL k c := by
          simp only [oqIn, ht, Bool.false_eq_true, ↓reduceIte]
        rw [e, hsum, sout (k - 1) (by omega) c (by omega) (by omega), sP _ hm, leafI]
        simp [hk0, hc, show k - 1 + 1 = k by omega]
      · split at ha
        · rename_i hm ht
          obtain ⟨hlast, rfl⟩ := (two_iff k (by omega) hk c hc).mp ht
          have hm8 : 17 * k / 2 + 8 = d.s.lc := by rw [hlc, show d.s.B - 1 = k by omega]
          have hw : σ (.n (oqBs d.kL k + 8)) = d.P d.s.lc := by
            rw [oqBs_eq (by omega), show d.kL + (13 + (k - 1) * 22) + 8 = d.kL + (13 + (k - 1) * 22 + 8) by
              omega, sleaf _ (by rcases hnums with h | h <;> omega),
              leafV_block d hs (by omega) hk (by simp only [hlast, ↓reduceIte]; omega)]
            simp [hlast]
          have hPlc : d.P d.s.lc = (if 17 * k / 2 + 8 = d.s.ncells then oqW81 d.s else oqW80 d.s) := by
            have := hL.last
            rw [P, hm8]
            by_cases h : d.s.lc = d.s.ncells
            · simp [h]
            · simp [h, show ¬ d.s.lc < d.s.ncells by omega]
          simp only [List.mem_cons, List.not_mem_nil, or_false, Stmt.atom.injEq] at ha
          rcases ha with rfl | rfl
          · show σ _ = _
            rw [hw, hPlc]
          · show σ _ = σ _ + σ _
            have e : oqBs d.kL k + 8 + 1 = oqIn d.s d.kL k 8 := by
              simp only [oqIn, ht, ↓reduceIte]
            rw [e, hsum, sout (k - 1) (by omega) 8 (by omega) (by omega), hw, leafI]
            simp [hk0, show k - 1 + 1 = k by omega, hm8]
        · rename_i hm ht
          have hlast : k + 1 = d.s.B := by
            by_contra hne
            have := hL.mid k (by omega); omega
          have hc8 : c ≠ 8 := fun h ↦ ht ((two_iff k (by omega) hk c hc).mpr ⟨hlast, h⟩)
          have hmn : 17 * k / 2 + c = d.s.ncells := by
            have := (oqTwo_iff d.s k c).not.mp ht
            omega
          have hmlc : 17 * k / 2 + c ≠ d.s.lc := by
            rw [hlc, show d.s.B - 1 = k by omega]; omega
          simp only [List.mem_cons, List.not_mem_nil, or_false, Stmt.atom.injEq] at ha
          subst ha
          show σ _ = σ _ + σ _
          have e : oqBs d.kL k + c = oqIn d.s d.kL k c := by
            simp only [oqIn, Bool.not_eq_true] at ht ⊢
            simp only [ht, Bool.false_eq_true, ↓reduceIte]
          rw [e, hsum, sout (k - 1) (by omega) c (by omega) (by omega), hpad, leafI]
          have hnlc : d.s.ncells ≠ d.s.lc := by omega
          simp [hk0, hc, show k - 1 + 1 = k by omega, P, hmn, hnlc]
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
        (by simp) ?_ (fun c _ => ?_) fun c hc => ?_
      · simp only [List.length_map, List.length_range, oqOutN]; split <;> rfl
      · rw [eI]; rfl
      · simp only [List.getElem_map, List.getElem_range]
        exact sout k hk c.val c.isLt (hoN k hk c.val (by simpa using hc))

/-- The leaf's cells' bytes are the row's words' bytes. -/
theorem leaf_bytes (hrow : d.row.length = 2 * d.s.ncells) :
    cellsBytes ((List.range d.s.ncells).map d.pk) = d.row.flatMap K.toBytes :=
  cellsBytes_packed d.row d.s.ncells hrow

/-- **The leaf hash's digest** at the honest values: the digest of the row. -/
theorem oqLeaf_digest (hs : d.s.RowShape) (hrow : d.row.length = 2 * d.s.ncells) (hv : d.Hv σ)
    (hpad : σ (.n d.prV) = word 1 0) (hz : ∀ i < 4, σ (.n (d.prV + 1 + i)) = word 0 0) :
    (σ (.n (oqOut d.s d.kL (d.s.B - 1) 0)), σ (.n (oqOut d.s d.kL (d.s.B - 1) 1))) =
      digestHalves d.leaf :=
  oqLeaf_sound (rd := fun _ ↦ none) hs (d.oqLeaf_complete (rd := fun _ ↦ none) hs hv hpad hz) hpad
    (fun i hi ↦ by rw [hz i hi, word_zero]) (by simp)
    (fun j hj ↦ by rw [d.pk_val hs hv hj]; simp [List.getD_eq_getElem?_getD, hj])
    (d.leaf_bytes hrow)

end QD

end
end LeanVM.Guest.B1
