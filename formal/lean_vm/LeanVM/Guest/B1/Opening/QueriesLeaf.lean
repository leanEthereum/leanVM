/-
  LeanVM.Guest.B1.Opening.QueriesLeaf

  One query's leaf hash: `keccak_cells` of the packed row is the Keccak-256 of the row's words.
-/

module

public import LeanVM.Guest.B1.Opening.QueriesRow
public import LeanVM.Guest.AcceptableChild

/-!
# A query's leaf hash (`opening_query`, G:1384-1385)

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

/-- The last cell the last block reads: `17(B-1)/2 + 8`. -/
def Oq.lc (s : Oq) : ℕ := 17 * (s.B - 1) / 2 + 8

/-- The deployed row shapes: level 0 (`base = 1`, `folds = 6`) and deeper (`base = 0`,
`folds = 4`). -/
def Oq.RowShape (s : Oq) : Prop := (s.base = 1 ∧ s.folds = 6) ∨ (s.base = 0 ∧ s.folds = 4)

instance (s : Oq) : Decidable s.RowShape := by unfold Oq.RowShape; infer_instance

/-- The leaf shapes: `n` cells hashed in `B` blocks, the last reading cells `17(B-1)/2 .. lc`,
`lc` the cell after the row (its `0x01` and `0x80` share it) or the one after that, the middle
blocks row cells only. -/
structure LeafShape (s : Oq) : Prop where
  B2 : 2 ≤ s.B
  last : s.lc = s.ncells + 1 ∨ s.lc = s.ncells
  mid : ∀ k, k + 1 < s.B → 17 * k / 2 + 8 < s.ncells
  read : padRead (16 * s.ncells) = s.lc + 1
  w80 : (rate * (16 * s.ncells / rate + 1) - 1) / 16 = s.lc
  w80c : byteCell (rate * (16 * s.ncells / rate + 1) - 1) 0x80 = oqW80 s
  pad1 : byteCell (16 * s.ncells) 1 = word 1 0
  w81 : oqW81 s = word 1 0 + oqW80 s

theorem leafShape_of (s : Oq) (hs : s.RowShape) : LeafShape s := by
  have key : (s.ncells = 32 ∧ s.B = 4) ∨ (s.ncells = 16 ∧ s.B = 2) := by
    rcases hs with ⟨hb, hI⟩ | ⟨hb, hI⟩
    · left; simp [Oq.B, Oq.ncells, Oq.I, hb, hI, rate]
    · right; simp [Oq.B, Oq.ncells, Oq.I, hb, hI, rate]
  have hB : s.B = 16 * s.ncells / rate + 1 := rfl
  rcases key with ⟨hn, hB'⟩ | ⟨hn, hB'⟩
  all_goals
    refine ⟨by omega, by simp [Oq.lc, hB', hn], fun k hk => by
      have hk' : k < 4 := by omega
      interval_cases k <;> omega, ?_, ?_, ?_, ?_, ?_⟩
    all_goals (simp only [hn, rate, oqW80, oqW81, padRead, byteCell, hB', Oq.lc]; try norm_num)
  all_goals (rw [word, word, word, ofLimbs_add]; congr 1)

/-- The padded cells of the leaf: the row's cells, then the padding `0x01` and `0x80`, in one cell
or two. -/
theorem getD_padCells_leaf {s : Oq} (hL : LeafShape s) (cells : List E)
    (hc : cells.length = s.ncells) (m : ℕ) (hm : m ≤ s.lc) :
    (padCells cells (16 * s.ncells)).getD m 0 =
      if m < s.ncells then cells.getD m 0
      else if m = s.ncells then (if m = s.lc then oqW81 s else word 1 0) else oqW80 s := by
  have hl : (cells ++ List.replicate (padRead (16 * s.ncells) - cells.length) 0).length =
      s.lc + 1 := by have := hL.last; simp [hL.read, hc]; omega
  have h16 : 16 * s.ncells / 16 = s.ncells := by omega
  unfold padCells
  rw [getD_xorByte_cell _ _ _ _ (by rw [length_xorByte, hl]; omega),
    getD_xorByte_cell _ _ _ _ (by rw [hl]; omega), hL.w80, h16]
  have hz : m ≥ cells.length → (List.replicate (padRead (16 * s.ncells) - cells.length) (0 : E)).getD
      (m - cells.length) 0 = 0 := fun _ ↦ by
    simp [List.getD_eq_getElem?_getD, List.getElem?_replicate]
    split <;> rfl
  by_cases h1 : m < s.ncells
  · rw [List.getD_append _ _ _ _ (by omega)]
    have := hL.last
    simp [h1, show m ≠ s.ncells by omega, show m ≠ s.lc by omega]
  · rw [List.getD_append_right _ _ _ _ (by omega), hz (by omega)]
    by_cases h2 : m = s.ncells
    · by_cases h3 : m = s.lc
      · simp [h2, ← h3, hL.pad1, hL.w81, hL.w80c]
      · simp [h2, hL.pad1, show s.ncells ≠ s.lc by omega]
    · have h3 : m = s.lc := by have := hL.last; omega
      simp [h3, hL.w80c, show s.lc ≠ s.ncells by omega, show ¬ s.lc < s.ncells by omega]

/-! ## The chain -/

/-- The state the leaf's block `k` starts from: zero, then block `k - 1`'s outputs. -/
def oqLeafO (s : Oq) (kL : ℕ) (σ : Val) : ℕ → Fin 13 → E
  | 0, _ => 0
  | k + 1, c => σ (.n (oqOut s kL k c))

/-- The cells the leaf's block `k` reads. -/
def oqLeafI (s : Oq) (b pr kL : ℕ) (σ : Val) : ℕ → Fin 13 → E
  | 0, c => if c.val < 9 then σ (.n (oqPk s b c.val)) else σ (.n (pr + (c.val - 8)))
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
    cellsBytes ((List.range n).map fun j ↦ E.ofLimbs (row.getD (2 * j) 0) (row.getD (2 * j + 1) 0)) =
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
        ((front ++ [x, y]).getD (2 * j + 1) 0)) =
        (List.range n).map (fun j ↦ E.ofLimbs (front.getD (2 * j) 0) (front.getD (2 * j + 1) 0)) :=
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

/-- A deeper row's cells' bytes are its `K` words' bytes, both limbs of each cell. -/
theorem cellsBytes_limbs (cs : List E) :
    cellsBytes cs = (cs.flatMap fun c ↦ [c.limb 0, c.limb 1]).flatMap K.toBytes := by
  induction cs with
  | nil => rfl
  | cons c cs ih =>
    rw [cellsBytes_cons, ih, List.flatMap_cons, List.flatMap_append]
    simp [cellBytes]

/-- **The leaf hash** (`keccak_cells` of the leaf's cells): with the padding run `1, 0, 0, 0, 0` at
`pr` and the leaf's cells `cs` whose bytes are the row's words' bytes, the last block's first two
cells are the digest of the row, `digestHalves (merkleLeafDigest row)` (the leaf of `openOne`). -/
theorem oqLeaf_sound {s : Oq} (hs : s.RowShape) {b pr kL : ℕ} {row : List K} {cs : List E}
    (hA : ∀ a, Stmt.atom a ∈ oqLeafT s b pr kL → a.Holds rd σ)
    (hpad : σ (.n pr) = word 1 0) (hz : ∀ i < 4, σ (.n (pr + 1 + i)) = 0)
    (hcl : cs.length = s.ncells) (hpk : ∀ j < s.ncells, σ (.n (oqPk s b j)) = cs.getD j 0)
    (hbytes : cellsBytes cs = row.flatMap K.toBytes) :
    (σ (.n (oqOut s kL (s.B - 1) 0)), σ (.n (oqOut s kL (s.B - 1) 1))) =
      digestHalves (merkleLeafDigest row) := by
  have hL := leafShape_of s hs
  have hn9 : 9 ≤ s.ncells := by have := hL.mid 0 (by have := hL.B2; omega); omega
  -- each block's permutation: its written cells the first of its Keccak-f
  have hblk : ∀ k < s.B, ∀ c : Fin 13, c.val < oqOutN s k → σ (.n (oqOut s kL k c)) = cellsOfState
        (keccakF1600 (stateOfCells (oqLeafI s b pr kL σ k) (Keccak.inLayout k)))
        (Keccak.outLayout s.B k) c := by
    intro k hk
    rcases k with _ | k
    · have h := hA _ (mem_oqLeafT hk (by simp [oqBlockT] : Stmt.atom (.keccak
        (((List.range 9).map fun c ↦ V.n (oqPk s b c)) ++
          [.n (pr + 1), .n (pr + 2), .n (pr + 3), .n (pr + 4)])
        ((List.range (oqOutN s 0)).map fun c ↦ V.n (oqOut s kL 0 c)) (Keccak.inLayout 0)
        (Keccak.outLayout s.B 0)) ∈ _))
      obtain ⟨-, -, O, hK, hw⟩ := keccak_holds_full h
      have eI : cells13 ((((List.range 9).map fun c ↦ V.n (oqPk s b c)) ++
          [V.n (pr + 1), V.n (pr + 2), V.n (pr + 3), V.n (pr + 4)]).map σ) = oqLeafI s b pr kL σ 0 := by
        funext c
        fin_cases c <;> simp [cells13, List.range_succ, oqLeafI]
      rw [eI] at hK
      intro c hc
      have := hw c (by simpa using hc)
      simp only [List.getElem_map, List.getElem_range] at this
      rw [this, hK c c.isLt]
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
      intro c hc
      have := hw c (by simpa using hc)
      simp only [List.getElem_map, List.getElem_range] at this
      rw [this, hK c c.isLt]
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
      exact (hblk k (by omega) c (by simp [oqOutN, show k + 1 ≠ s.B by omega])).symm
  have hB : 16 * s.ncells / rate + 1 = s.B := rfl
  have hcg : ∀ m < s.ncells, cs.getD m 0 = σ (.n (oqPk s b m)) := fun m hm => (hpk m hm).symm
  -- the cell a block reads, by where it lies
  have hpos : ∀ k, k + 1 < s.B + 1 → ∀ c < 9, 17 * k / 2 + c < s.ncells ∨
      (17 * k / 2 + c = s.ncells ∧ c ≠ 8 ∧ 17 * k / 2 + c ≠ s.lc) ∨
      (17 * k / 2 + c = s.lc ∧ k + 1 = s.B ∧ c = 8 ∧ s.ncells ≤ s.lc) := by
    intro k hk c hc
    have hlast := hL.last
    have : k + 1 = s.B ∨ k + 1 < s.B := by omega
    rcases this with e | e
    · have : 17 * k / 2 + 8 = s.lc := by simp only [Oq.lc, ← e, Nat.add_sub_cancel]
      omega
    · have := hL.mid k e; omega
  have key := keccak_final_digest (cells := cs) (len := 16 * s.ncells) (pre := []) (n := 0)
    (I := oqLeafI s b pr kL σ) (O := O') (by rfl) (by rw [hcl])
    (getD_cellsBytes_of_le (by rw [hcl]))
    (by funext c; simp [O', absorbChunks, cellsOfState_zero])
    (by
      intro k hk c hc
      rw [hB] at hk
      rw [hOO k hk]
      have hp := hpos k (by omega) c.val hc
      have hlast : 17 * k / 2 + c.val ≤ s.lc := by have := hL.last; omega
      rw [getD_padCells_leaf hL cs hcl _ hlast]
      rcases k with _ | k
      · simp only [oqLeafI, oqLeafO, hc, ↓reduceIte, zero_add, Nat.mul_zero, Nat.zero_div,
          show c.val < s.ncells by omega, hcg c.val (by omega)]
      · have hxor : ∀ a, Stmt.atom a ∈ oqXorT s b pr kL (k + 1) c.val → a.Holds rd σ :=
          fun a ha => hA a (mem_oqLeafT (k := k + 1) hk (by
            simp only [oqBlockT, Nat.succ_ne_zero, ↓reduceIte, List.mem_append]
            exact Or.inl (List.mem_flatten.mpr ⟨_, List.mem_map.mpr ⟨c.val, List.mem_range.mpr hc,
              rfl⟩, ha⟩)))
        simp only [oqLeafI, oqLeafO, hc, ↓reduceIte]
        rcases hp with h1 | ⟨h2, h8, hl⟩ | ⟨hm, -, h8, hle⟩
        · have := hxor _ (by simp [oqXorT, h1] : Stmt.atom (.add (.n (oqBs kL (k + 1) + c.val))
            (.n (oqOut s kL k c.val)) (.n (oqPk s b (17 * (k + 1) / 2 + c.val)))) ∈ _)
          simp only [Atom.Holds] at this
          have h3 : oqTwo s (k + 1) c.val = false := by simp [oqTwo]; omega
          simp only [h1, ↓reduceIte, hcg _ h1, oqIn, h3, Bool.false_eq_true]
          exact this
        · have h3 : oqTwo s (k + 1) c.val = false := by simp [oqTwo]; omega
          have := hxor _ (by simp [oqXorT, h3, show ¬ 17 * (k + 1) / 2 + c.val < s.ncells by omega] :
            Stmt.atom (.add (.n (oqBs kL (k + 1) + c.val)) (.n (oqOut s kL k c.val)) (.n pr)) ∈ _)
          simp only [Atom.Holds] at this
          simp only [h2, lt_self_iff_false, ↓reduceIte, oqIn, h3, Bool.false_eq_true]
          have hne : ¬ s.ncells = s.lc := by omega
          simp only [hne, ↓reduceIte]
          rw [← hpad]
          exact this
        · have h1 : ¬ 17 * (k + 1) / 2 + c.val < s.ncells := by have := hL.last; omega
          have h3 : oqTwo s (k + 1) c.val = true := by
            simp only [oqTwo, Bool.or_eq_true, decide_eq_true_eq, Bool.and_eq_true]
            have := hL.last
            omega
          have e1 := hxor _ (by simp [oqXorT, h1, h3] :
            Stmt.atom (.const (.n (oqBs kL (k + 1) + c.val))
              (if 17 * (k + 1) / 2 + c.val = s.ncells then oqW81 s else oqW80 s)) ∈ _)
          have e2 := hxor _ (by simp [oqXorT, h1, h3] :
            Stmt.atom (.add (.n (oqBs kL (k + 1) + c.val + 1)) (.n (oqOut s kL k c.val))
              (.n (oqBs kL (k + 1) + c.val))) ∈ _)
          simp only [Atom.Holds] at e1 e2
          simp only [h1, ↓reduceIte, oqIn, h3]
          rw [e2, e1, hm]
          by_cases h5 : s.lc = s.ncells
          · simp [h5]
          · simp [h5])
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
      exact fun c _ => by simp [O'])
  rw [hB, List.nil_append, List.take_of_length_le (by simp [hcl]), hbytes] at key
  have hlast : ∀ c : Fin 13, c.val < 2 → O' s.B c = σ (.n (oqOut s kL (s.B - 1) c)) := fun c hc => by
    have := hblk (s.B - 1) (by have := hL.B2; omega) c
      (by simp [oqOutN, show s.B - 1 + 1 = s.B by have := hL.B2; omega]; omega)
    simp only [O', show s.B ≠ 0 by have := hL.B2; omega, ↓reduceIte]
    exact this.symm
  rw [hlast 0 (by decide), hlast 1 (by decide)] at key
  rw [merkleLeafDigest, ← key]
  rfl

end
end LeanVM.Guest.B1
