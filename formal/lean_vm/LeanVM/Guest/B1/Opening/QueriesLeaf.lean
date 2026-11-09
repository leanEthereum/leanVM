/-
  LeanVM.Guest.B1.Opening.QueriesLeaf

  One query's leaf hash: `keccak_cells` of the packed row is the Keccak-256 of the row's words.
-/

module

public import LeanVM.Guest.B1.Opening.QueriesRow
public import LeanVM.Guest.AcceptableChild

/-!
# A query's leaf hash (`opening_query`, G:1387-1388)

`keccak_cells(packed_row[0:leaf_cells], leaf_hash_state)` over the `n = R / 2` packed cells is
`B = 16n/136 + 1` chained `KECCAK`s (`oqLeafT`): block `k` reads the previous output plus the
cells from `17k / 2`, the padding `0x01` at cell `n` (the zero/padding run's first cell) and
`0x80` at cell `n + 1`. `oqLeaf_sound`: its digest cells are `digestHalves (merkleLeafDigest row)`
(G3's `keccak_final_digest`, the packed cells' bytes being the row's words' bytes).
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Guest.Value.Keccak
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

variable {rd : Reader} {σ : Val}

/-! ## The padded cells -/

theorem getD_xorByte_cell (cs : List E) (pos v m : ℕ) (hm : m < cs.length) :
    (xorByte cs pos v).getD m 0 = cs.getD m 0 + (if m = pos / 16 then byteCell pos v else 0) := by
  simp only [xorByte, List.getD_eq_getElem?_getD, List.getElem?_modify, List.getElem?_eq_getElem hm]
  by_cases h : pos / 16 = m
  · simp [h]
  · simp [h, Ne.symm h]

/-- The leaf shapes: `n` packed cells hashed in `B` blocks, the last reading cells
`17(B-1)/2 .. n + 1`, the middle ones row cells only. -/
structure LeafShape (s : Oq) : Prop where
  B2 : 2 ≤ s.B
  last : 17 * (s.B - 1) / 2 + 8 = s.ncells + 1
  mid : ∀ k, k + 1 < s.B → 17 * k / 2 + 8 < s.ncells
  read : padRead (16 * s.ncells) = s.ncells + 2
  w80 : (rate * (16 * s.ncells / rate + 1) - 1) / 16 = s.ncells + 1
  w80c : byteCell (rate * (16 * s.ncells / rate + 1) - 1) 0x80 = oqW80 s
  pad1 : byteCell (16 * s.ncells) 1 = word 1 0 0

theorem leafShape_of (s : Oq) (hs : s.RowShape) : LeafShape s := by
  have key : (s.ncells = 32 ∧ s.B = 4) ∨ (s.ncells = 24 ∧ s.B = 3) := by
    rcases hs with ⟨hb, hI⟩ | ⟨hb, hI⟩
    · left; simp [Oq.B, Oq.ncells, Oq.R, hb, hI, rate]
    · right; simp [Oq.B, Oq.ncells, Oq.R, hb, hI, rate]
  have hB : s.B = 16 * s.ncells / rate + 1 := rfl
  rcases key with ⟨hn, hB'⟩ | ⟨hn, hB'⟩
  all_goals
    refine ⟨by omega, by omega, fun k hk => by
      have hk' : k < 4 := by omega
      interval_cases k <;> omega, ?_, ?_,
      ?_, ?_⟩
    all_goals (simp only [hn, rate, oqW80, padRead, byteCell, hB']; try norm_num)

/-- The padded cells of the leaf: the row's cells, the padding `0x01`, then `0x80`. -/
theorem getD_padCells_leaf {s : Oq} (hL : LeafShape s) (cells : List E)
    (hc : cells.length = s.ncells) (m : ℕ) (hm : m < s.ncells + 2) :
    (padCells cells (16 * s.ncells)).getD m 0 =
      if m < s.ncells then cells.getD m 0 else if m = s.ncells then word 1 0 0 else oqW80 s := by
  have hl : (cells ++ List.replicate (padRead (16 * s.ncells) - cells.length) 0).length =
      s.ncells + 2 := by simp [hL.read, hc]
  have h16 : 16 * s.ncells / 16 = s.ncells := by omega
  unfold padCells
  rw [getD_xorByte_cell _ _ _ _ (by rw [length_xorByte, hl]; exact hm),
    getD_xorByte_cell _ _ _ _ (by rw [hl]; exact hm), hL.w80, h16]
  by_cases h1 : m < s.ncells
  · rw [List.getD_append _ _ _ _ (by omega)]
    simp [h1, show m ≠ s.ncells by omega, show m ≠ s.ncells + 1 by omega]
  · rw [List.getD_append_right _ _ _ _ (by omega)]
    have hz : (List.replicate (padRead (16 * s.ncells) - cells.length) (0 : E)).getD
        (m - cells.length) 0 = 0 := by
      simp [List.getD_eq_getElem?_getD, List.getElem?_replicate]
      split <;> rfl
    rw [hz]
    by_cases h2 : m = s.ncells
    · simp [h2, hL.pad1]
    · simp [show m = s.ncells + 1 by omega, hL.w80c]

/-! ## The chain -/

/-- The state the leaf's block `k` starts from: zero, then block `k - 1`'s outputs. -/
def oqLeafO (s : Oq) (kL : ℕ) (σ : Val) : ℕ → Fin 13 → E
  | 0, _ => 0
  | k + 1, c => σ (.n (oqOut s kL k c))

/-- The cells the leaf's block `k` reads. -/
def oqLeafI (s : Oq) (b pr kL : ℕ) (σ : Val) : ℕ → Fin 13 → E
  | 0, c => if c.val < 9 then σ (.n (oqPk b s.R c.val)) else σ (.n (pr + (c.val - 8)))
  | k + 1, c => if c.val < 9 then σ (.n (oqIn s kL (k + 1) c.val)) else σ (.n (oqOut s kL k c.val))

theorem cells13_block (f g : ℕ → V) (c : Fin 13) :
    cells13 ((((List.range 9).map f) ++ ((List.range 4).map g)).map σ) c =
      if c.val < 9 then σ (f c.val) else σ (g (c.val - 9)) := by
  fin_cases c <;> simp [cells13, List.range_succ]

theorem cells13_outs (f : ℕ → V) (c : Fin 13) :
    cells13 (((List.range 13).map f).map σ) c = σ (f c.val) := by
  fin_cases c <;> simp [cells13, List.range_succ]

theorem mem_oqLeafT {s : Oq} {b pr kL k : ℕ} (hk : k < s.B) {a : Atom}
    (ha : Stmt.atom a ∈ oqBlockT s b pr kL k) : Stmt.atom a ∈ oqLeafT s b pr kL :=
  List.mem_flatten.mpr ⟨_, List.mem_map.mpr ⟨k, List.mem_range.mpr hk, rfl⟩, ha⟩

/-- The packed cells' bytes are the row's words' bytes. -/
theorem cellsBytes_packed (row : List K) (n : ℕ) (hn : row.length = 2 * n) :
    cellsBytes ((List.range n).map fun j ↦ E.ofLimbs (row.getD (2 * j) 0) (row.getD (2 * j + 1) 0) 0) =
      row.flatMap K.toBytes := by
  induction n generalizing row with
  | zero => simp_all
  | succ n ih =>
    obtain ⟨front, x, y, rfl⟩ : ∃ front x y, row = front ++ [x, y] := by
      refine ⟨row.take (2 * n), row.getD (2 * n) 0, row.getD (2 * n + 1) 0, ?_⟩
      apply List.ext_getElem
      · simp; omega
      · intro i h1 h2
        simp only [List.getElem_append, List.length_take, List.getD_eq_getElem?_getD]
        split
        · simp
        · rename_i h
          have : i = 2 * n ∨ i = 2 * n + 1 := by simp at h1 h; omega
          rcases this with rfl | rfl <;> simp [List.getElem?_eq_getElem h1, hn]
    have hf : front.length = 2 * n := by simp at hn; omega
    have e : ∀ j, j < n → (front ++ [x, y]).getD (2 * j) 0 = front.getD (2 * j) 0 ∧
        (front ++ [x, y]).getD (2 * j + 1) 0 = front.getD (2 * j + 1) 0 := fun j hj => by
      simp [List.getD_eq_getElem?_getD, List.getElem?_append_left (show 2 * j < front.length by omega),
        List.getElem?_append_left (show 2 * j + 1 < front.length by omega)]
    have hmap : (List.range n).map (fun j ↦ E.ofLimbs ((front ++ [x, y]).getD (2 * j) 0)
        ((front ++ [x, y]).getD (2 * j + 1) 0) 0) =
        (List.range n).map (fun j ↦ E.ofLimbs (front.getD (2 * j) 0) (front.getD (2 * j + 1) 0) 0) :=
      List.map_congr_left (fun j hj => by
        rw [(e j (List.mem_range.mp hj)).1, (e j (List.mem_range.mp hj)).2])
    have h1 : (front ++ [x, y]).getD (2 * n) 0 = x := by
      simp [List.getD_eq_getElem?_getD, hf]
    have h2 : (front ++ [x, y]).getD (2 * n + 1) 0 = y := by
      simp [List.getD_eq_getElem?_getD, hf]
    rw [List.range_succ, List.map_append, cellsBytes_append, hmap, ih front hf, List.flatMap_append]
    simp only [List.map_cons, List.map_nil]
    rw [h1, h2]
    simp [cellsBytes, cellBytes]

/-- **The leaf hash** (G:1220-1222): with the padding run `1, 0, 0, 0, 0` at `pr` and the packed
cells those of the row's words, the last block's first two cells are the digest of the row,
`digestHalves (merkleLeafDigest row)` (the leaf of `openOne`, V:501). -/
theorem oqLeaf_sound {s : Oq} (hs : s.RowShape) {b pr kL : ℕ} {row : List K}
    (hA : ∀ a, Stmt.atom a ∈ oqLeafT s b pr kL → a.Holds rd σ)
    (hpad : σ (.n pr) = word 1 0 0) (hz : ∀ i < 4, σ (.n (pr + 1 + i)) = 0)
    (hrow : row.length = 2 * s.ncells)
    (hpk : ∀ j < s.ncells,
      σ (.n (oqPk b s.R j)) = E.ofLimbs (row.getD (2 * j) 0) (row.getD (2 * j + 1) 0) 0) :
    (σ (.n (oqOut s kL (s.B - 1) 0)), σ (.n (oqOut s kL (s.B - 1) 1))) =
      digestHalves (merkleLeafDigest row) := by
  have hL := leafShape_of s hs
  have hn9 : 9 ≤ s.ncells := by have := hL.mid 0 (by have := hL.B2; omega); omega
  set cells := (List.range s.ncells).map fun j ↦ σ (.n (oqPk b s.R j)) with hcells
  have hcl : cells.length = s.ncells := by simp [hcells]
  have hcg : ∀ m < s.ncells, cells.getD m 0 = σ (.n (oqPk b s.R m)) := fun m hm => by
    simp [hcells, List.getD_eq_getElem?_getD, hm]
  -- each block's permutation: canonical reads, its written cells the first of its Keccak-f
  have hblk : ∀ k < s.B, (∀ c, IsCanonical128 (oqLeafI s b pr kL σ k c)) ∧
      ∀ c : Fin 13, c.val < oqOutN s k → σ (.n (oqOut s kL k c)) = cellsOfState
        (keccakF1600 (stateOfCells (oqLeafI s b pr kL σ k) (Keccak.inLayout k)))
        (Keccak.outLayout s.B k) c := by
    intro k hk
    rcases k with _ | k
    · have h := hA _ (mem_oqLeafT hk (by simp [oqBlockT] : Stmt.atom (.keccak
        (((List.range 9).map fun c ↦ V.n (oqPk b s.R c)) ++
          [.n (pr + 1), .n (pr + 2), .n (pr + 3), .n (pr + 4)])
        ((List.range (oqOutN s 0)).map fun c ↦ V.n (oqOut s kL 0 c)) (Keccak.inLayout 0)
        (Keccak.outLayout s.B 0)) ∈ _))
      obtain ⟨-, -, O, hK, hw⟩ := keccak_holds_full h
      have eI : cells13 ((((List.range 9).map fun c ↦ V.n (oqPk b s.R c)) ++
          [V.n (pr + 1), V.n (pr + 2), V.n (pr + 3), V.n (pr + 4)]).map σ) = oqLeafI s b pr kL σ 0 := by
        funext c
        fin_cases c <;> simp [cells13, List.range_succ, oqLeafI]
      rw [eI] at hK
      refine ⟨hK.1, fun c hc => ?_⟩
      have := hw c (by simpa using hc)
      simp only [List.getElem_map, List.getElem_range] at this
      rw [this, hK.2 c c.isLt]
    · have h := hA _ (mem_oqLeafT hk (by simp [oqBlockT] : Stmt.atom (.keccak
        (((List.range 9).map fun c ↦ V.n (oqIn s kL (k + 1) c)) ++
          ((List.range 4).map fun c ↦ V.n (oqOut s kL k (9 + c))))
        ((List.range (oqOutN s (k + 1))).map fun c ↦ V.n (oqOut s kL (k + 1) c))
        (Keccak.inLayout (k + 1)) (Keccak.outLayout s.B (k + 1))) ∈ _))
      obtain ⟨-, -, O, hK, hw⟩ := keccak_holds_full h
      have eI : cells13 ((((List.range 9).map fun c ↦ V.n (oqIn s kL (k + 1) c)) ++
          ((List.range 4).map fun c ↦ V.n (oqOut s kL k (9 + c)))).map σ) =
            oqLeafI s b pr kL σ (k + 1) := by
        funext c; rw [cells13_block]
        simp only [oqLeafI]
        split
        · rfl
        · rename_i hc
          rw [show 9 + (c.val - 9) = c.val by omega]
      rw [eI] at hK
      refine ⟨hK.1, fun c hc => ?_⟩
      have := hw c (by simpa using hc)
      simp only [List.getElem_map, List.getElem_range] at this
      rw [this, hK.2 c c.isLt]
  -- the true states: block `k - 1`'s Keccak-f; before the last block, its written cells
  let O' : ℕ → Fin 13 → E := fun k c => if k = 0 then 0 else
    cellsOfState (keccakF1600 (stateOfCells (oqLeafI s b pr kL σ (k - 1)) (Keccak.inLayout (k - 1))))
      (Keccak.outLayout s.B (k - 1)) c
  have hOO : ∀ k < s.B, O' k = oqLeafO s kL σ k := by
    intro k hk
    funext c
    rcases k with _ | k
    · rfl
    · simp only [O', Nat.add_one_ne_zero, ↓reduceIte, Nat.add_sub_cancel, oqLeafO]
      exact ((hblk k (by omega)).2 c (by simp [oqOutN, show k + 1 ≠ s.B by omega])).symm
  have hB : 16 * s.ncells / rate + 1 = s.B := rfl
  have key := keccak_final_digest (cells := cells) (len := 16 * s.ncells) (pre := []) (n := 0)
    (I := oqLeafI s b pr kL σ) (O := O') (by rfl) (by rw [hcl])
    (getD_cellsBytes_of_le (by rw [hcl]))
    (by funext c; simp [O', absorbChunks, cellsOfState_zero])
    (by
      intro k hk c hc
      rw [hB] at hk
      rw [hOO k hk]
      rw [getD_padCells_leaf hL cells hcl _ (by
        rcases k with _ | k
        · omega
        · have := hL.last; have : 17 * (k + 1) / 2 ≤ 17 * (s.B - 1) / 2 :=
            Nat.div_le_div_right (by omega)
          omega)]
      rcases k with _ | k
      · simp only [oqLeafI, oqLeafO, hc, ↓reduceIte, zero_add, Nat.mul_zero, Nat.zero_div,
          show c.val < s.ncells by omega, hcg c.val (by omega)]
      · have hxor : ∀ a, Stmt.atom a ∈ oqXorT s b pr kL (k + 1) c.val → a.Holds rd σ :=
          fun a ha => hA a (mem_oqLeafT (k := k + 1) hk (by
            simp only [oqBlockT, Nat.succ_ne_zero, ↓reduceIte, List.mem_append]
            exact Or.inl (List.mem_flatten.mpr ⟨_, List.mem_map.mpr ⟨c.val, List.mem_range.mpr hc,
              rfl⟩, ha⟩)))
        simp only [oqLeafI, oqLeafO, hc, ↓reduceIte]
        by_cases h1 : 17 * (k + 1) / 2 + c.val < s.ncells
        · have := hxor _ (by simp [oqXorT, h1] : Stmt.atom (.add (.n (oqBs kL (k + 1) + c.val))
            (.n (oqOut s kL k c.val)) (.n (oqPk b s.R (17 * (k + 1) / 2 + c.val)))) ∈ _)
          simp only [Atom.Holds] at this
          simp only [h1, ↓reduceIte, hcg _ h1, oqIn, show 17 * (k + 1) / 2 + c.val ≤ s.ncells by omega]
          exact this
        · by_cases h2 : 17 * (k + 1) / 2 + c.val = s.ncells
          · have := hxor _ (by simp [oqXorT, h2] : Stmt.atom (.add (.n (oqBs kL (k + 1) + c.val))
              (.n (oqOut s kL k c.val)) (.n pr)) ∈ _)
            simp only [Atom.Holds] at this
            simp only [h2, ↓reduceIte, oqIn, le_refl, lt_self_iff_false]
            rw [← hpad]
            exact this
          · have h3 : 17 * (k + 1) / 2 + c.val = s.ncells + 1 := by
              have := hL.last; have : 17 * (k + 1) / 2 ≤ 17 * (s.B - 1) / 2 :=
                Nat.div_le_div_right (by omega)
              omega
            have e1 := hxor _ (by simp [oqXorT, h1, h2] :
              Stmt.atom (.const (.n (oqBs kL (k + 1) + c.val)) (oqW80 s)) ∈ _)
            have e2 := hxor _ (by simp [oqXorT, h1, h2] :
              Stmt.atom (.add (.n (oqBs kL (k + 1) + c.val + 1)) (.n (oqOut s kL k c.val))
                (.n (oqBs kL (k + 1) + c.val))) ∈ _)
            simp only [Atom.Holds] at e1 e2
            simp only [h1, h2, ↓reduceIte, oqIn, show ¬ 17 * (k + 1) / 2 + c.val ≤ s.ncells by omega]
            rw [e2, e1])
    (by
      intro k hk c hc
      rw [hOO k (by rw [hB] at hk; exact hk)]
      rcases k with _ | k
      · simp only [oqLeafI, oqLeafO, show ¬ c.val < 9 by omega, ↓reduceIte]
        have := hz (c.val - 9) (by omega)
        rwa [show pr + 1 + (c.val - 9) = pr + (c.val - 8) by omega] at this
      · simp [oqLeafI, oqLeafO, show ¬ c.val < 9 by omega])
    (by
      intro k hk
      rw [hB] at hk ⊢
      exact ⟨(hblk k hk).1, fun c _ => by simp [O']⟩)
  rw [hB, List.nil_append, List.take_of_length_le (by simp [hcl]), hcells] at key
  have hpk' : (List.range s.ncells).map (fun j ↦ σ (.n (oqPk b s.R j))) =
      (List.range s.ncells).map fun j ↦ E.ofLimbs (row.getD (2 * j) 0) (row.getD (2 * j + 1) 0) 0 :=
    List.map_congr_left fun j hj => hpk j (List.mem_range.mp hj)
  rw [hpk', cellsBytes_packed row s.ncells hrow] at key
  have hlast : ∀ c : Fin 13, c.val < 2 → O' s.B c = σ (.n (oqOut s kL (s.B - 1) c)) := fun c hc => by
    have := (hblk (s.B - 1) (by have := hL.B2; omega)).2 c
      (by simp [oqOutN, show s.B - 1 + 1 = s.B by have := hL.B2; omega]; omega)
    simp only [O', show s.B ≠ 0 by have := hL.B2; omega, ↓reduceIte]
    exact this.symm
  rw [hlast 0 (by decide), hlast 1 (by decide)] at key
  rw [merkleLeafDigest, ← key]
  rfl

end
end LeanVM.Guest.B1
