/-
  LeanVM.Guest.B1.Digest.Statement

  B1 for `statement_digest` (G:4058-4089; TRIAGE #86): the statement's digest, byte for byte.
-/

module

public import LeanVM.Guest.B1.Digest.Basic

/-!
# `statement_digest`

`statement_digest(seed_0, seed_1, xd_0, xd_1, sd_0, sd_1, da_0, da_1, defer)` hashes 44 cells: the
seed's two cells, the two claim lists' digests' two each, the DA digest's two, then the 24
deferred cells (read at `defer`) two at a time as three canonical cells each (`pack_pair`), `704`
bytes in six `KECCAK` blocks, the last holding bytes `680 … 703`, the padding's `0x01` (byte
`704`, cell `44`) and `0x80` (byte `815`, cell `50`). Its core IR (`Data.core21`) is the template
`sdAtoms` (`core20_body`, by kernel evaluation); `keccak_final_digest` makes the chain Keccak-256 of
the cells' bytes, which are the header cells' and the deferred cells' limbs (`pair_bytes`).
-/

namespace LeanVM.Guest.B1.Digest

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Value.Keccak
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

/-! ## The template -/

/-- The value of hashed cell `m < 44`: the eight header cells, then the three cells of each pair. -/
def sdCell (m : ℕ) : ℕ :=
  if m < 8 then 9 + m else 17 + 27 * ((m - 8) / 3) + (8 + 9 * ((m - 8) % 3))

/-- The value of output cell `c` of block `k < 6`. -/
def sdOut (k c : ℕ) : ℕ := if k < 5 then 346 + 22 * k + c else 452 + c

/-- The value of input cell `c` of block `k < 6`. -/
def sdIn (k c : ℕ) : ℕ :=
  if c < 9 then
    (if k = 0 then sdCell c else if k < 5 then 359 + 22 * (k - 1) + c
      else if c < 2 then 447 + c else if c = 2 then 449 else if c < 8 then sdOut 4 c else 451)
  else (if k = 0 then 342 + (c - 9) else sdOut (k - 1) c)

/-- The cells block `k` writes: the thirteen of the state, the last block the digest's two
(`out_cells`). -/
def sdOutN (k : ℕ) : ℕ := if k < 5 then 13 else 2

/-- The `KECCAK` of block `k`. -/
def sdKeccak (k : ℕ) : Atom :=
  .keccak ((List.range 13).map fun c => .n (sdIn k c))
    ((List.range (sdOutN k)).map fun c => .n (sdOut k c)) (inLayout k) (outLayout 6 k)

/-- The header cells. -/
def sdHdr : List Atom :=
  [.copy (.n 9) (.n 0), .copy (.n 10) (.n 1), .copy (.n 11) (.n 2), .copy (.n 12) (.n 3),
   .copy (.n 13) (.n 4), .copy (.n 14) (.n 5), .copy (.n 15) (.n 6), .copy (.n 16) (.n 7)]

/-- The constants: the padding's `0x01` cell and the zero capacity of the first block. -/
def sdConsts : List Atom :=
  [.const (.n 341) (word 1 0 0), .const (.n 342) (word 0 0 0), .const (.n 343) (word 0 0 0),
   .const (.n 344) (word 0 0 0), .const (.n 345) (word 0 0 0)]

/-- Block `k ∈ {1, …, 4}`: nine message cells XORed into the previous output, then its `KECCAK`. -/
def sdBlk (k : ℕ) : List Atom :=
  (List.range 9).map (fun c => .add (.n (359 + 22 * (k - 1) + c)) (.n (sdOut (k - 1) c))
    (.n (sdCell (17 * k / 2 + c)))) ++ [sdKeccak k]

/-- The padding's last cell (`0x80` at byte `815`, the last byte of the sixth block). -/
abbrev padWord : E := word 0 9223372036854775808 0

/-- The last block: the message's last two cells, the padding's two cells (the cells between are
zero, their outputs passed on), its `KECCAK`. -/
def sdBlk5 : List Atom :=
  [.add (.n 447) (.n (sdOut 4 0)) (.n (sdCell 42)), .add (.n 448) (.n (sdOut 4 1)) (.n (sdCell 43)),
   .add (.n 449) (.n (sdOut 4 2)) (.n 341), .const (.n 450) padWord,
   .add (.n 451) (.n (sdOut 4 8)) (.n 450), sdKeccak 5]

/-- `statement_digest`'s atoms. -/
def sdAtoms : List Atom :=
  sdHdr ++ (List.range 12).flatMap (fun p => pairAtoms (.n 8) (2 * p) (17 + 27 * p)) ++ sdConsts ++
    [sdKeccak 0] ++ (List.range 4).flatMap (fun j => sdBlk (j + 1)) ++ sdBlk5 ++
    [.copy (.n 454) (.n 452), .copy (.n 455) (.n 453)]

set_option maxRecDepth 100000 in
theorem core20_body : Fn.body Data.core21 = sdAtoms.map Stmt.atom ++ [.ret [.n 454, .n 455]] :=
  stmtsEqb_sound (by decide +kernel)

theorem core20_params : Fn.params Data.core21 =
    [.n 0, .n 1, .n 2, .n 3, .n 4, .n 5, .n 6, .n 7, .n 8] := rfl

/-! ## The cells -/

theorem sdCell_A (p : ℕ) : sdCell (8 + 3 * p) = 17 + 27 * p + 8 := by
  unfold sdCell
  rw [ite_neg' (by omega), show (8 + 3 * p - 8) / 3 = p by omega, show (8 + 3 * p - 8) % 3 = 0 by omega]

theorem sdCell_B (p : ℕ) : sdCell (8 + 3 * p + 1) = 17 + 27 * p + 17 := by
  unfold sdCell
  rw [ite_neg' (by omega), show (8 + 3 * p + 1 - 8) / 3 = p by omega,
    show (8 + 3 * p + 1 - 8) % 3 = 1 by omega]

theorem sdCell_C (p : ℕ) : sdCell (8 + 3 * p + 2) = 17 + 27 * p + 26 := by
  unfold sdCell
  rw [ite_neg' (by omega), show (8 + 3 * p + 2 - 8) / 3 = p by omega,
    show (8 + 3 * p + 2 - 8) % 3 = 2 by omega]

theorem range44_split (f : ℕ → E) :
    (List.range 44).map f = (List.range 8).map f ++
      (List.range 12).flatMap (fun p => [f (8 + 3 * p), f (8 + 3 * p + 1), f (8 + 3 * p + 2)]) :=
  rfl

theorem range24_split (g : ℕ → E) :
    (List.range 24).map g = (List.range 12).flatMap (fun p => [g (2 * p), g (2 * p + 1)]) := rfl

theorem cells13_map_range (σ : Val) (f : ℕ → ℕ) (c : Fin 13) :
    cells13 (((List.range 13).map fun c => V.n (f c)).map σ) c = σ (.n (f c)) := by
  simp [cells13, List.getD_eq_getElem?_getD, c.isLt]

/-- Block `k`'s `KECCAK`: canonical inputs, and its written cells the first of their Keccak-f. -/
theorem keccak_holds {rd : Reader} {σ : Val} {k : ℕ} (h : (sdKeccak k).Holds rd σ) :
    (∀ c : Fin 13, IsCanonical128 (σ (.n (sdIn k c)))) ∧ ∀ c : Fin 13, c.val < sdOutN k →
      σ (.n (sdOut k c)) = cellsOfState (keccakF1600 (stateOfCells
        (fun c : Fin 13 => σ (.n (sdIn k c))) (inLayout k))) (outLayout 6 k) c := by
  obtain ⟨-, -, O, hK, hw⟩ := keccak_holds_full h
  have e1 : cells13 (((List.range 13).map fun c => V.n (sdIn k c)).map σ) =
      fun c : Fin 13 => σ (.n (sdIn k c)) := funext (cells13_map_range σ _)
  rw [e1] at hK
  refine ⟨hK.1, fun c hc => ?_⟩
  have := hw c (by simpa using hc)
  simp only [List.getElem_map, List.getElem_range] at this
  rw [this, hK.2 c c.isLt]

/-- The padded 44-cell message past its cells: the `0x01` cell at `44`, the `0x80` cell at `50`,
zero between. -/
theorem padCells_44 (cells : List E) (hl : cells.length = 44) {i : ℕ} (h1 : 44 ≤ i) (h2 : i < 51) :
    (padCells cells 704).getD i 0 =
      if i = 44 then word 1 0 0 else if i = 50 then padWord else 0 := by
  have hr : padRead 704 - cells.length = 7 := by rw [hl]; rfl
  unfold padCells xorByte
  rw [show rate * (704 / rate + 1) - 1 = 815 from rfl, show (815 : ℕ) / 16 = 50 from rfl,
    show (704 : ℕ) / 16 = 44 from rfl, hr, List.getD_eq_getElem?_getD, List.getElem?_modify,
    List.getElem?_modify, List.getElem?_append_right (by omega), hl,
    List.getElem?_replicate_of_lt (by omega)]
  unfold byteCell
  simp only [show (704 : ℕ) % 16 = 0 from rfl, show (815 : ℕ) % 16 = 15 from rfl]
  rcases (show i = 44 ∨ (45 ≤ i ∧ i ≤ 49) ∨ i = 50 by omega) with rfl | ⟨h45, h49⟩ | rfl
  · simp [word_eOfNat]
  · simp [show i ≠ 44 by omega, show i ≠ 50 by omega, show (50 : ℕ) ≠ i by omega,
      show (44 : ℕ) ≠ i by omega]
  · simp [padWord]

/-! ## Soundness -/

set_option maxRecDepth 100000 in
/-- **`statement_digest` computes the statement's digest.** -/
theorem statement_digest_sound : statement_digest_sound_Spec := by
  intro rd args rets h
  obtain ⟨σ, hp, hb⟩ := (rel_iff_sem find_statement_digest args rets).mp h
  rw [core20_body, holdsList_atoms_ret] at hb
  obtain ⟨hat, hr⟩ := hb
  simp only [sdAtoms, List.forall_mem_append, List.forall_mem_cons, List.not_mem_nil,
    IsEmpty.forall_iff, implies_true, and_true] at hat
  obtain ⟨⟨⟨⟨⟨⟨hH, hP⟩, hC⟩, hK0⟩, hB⟩, hB5⟩, h454, h455⟩ := hat
  rw [forall_mem_flatMap_range] at hP hB
  -- the header
  simp only [sdHdr, List.forall_mem_cons, Atom.Holds, List.not_mem_nil, IsEmpty.forall_iff,
    implies_true, and_true] at hH
  obtain ⟨h9, h10, h11, h12, h13, h14, h15, h16⟩ := hH
  -- the constants
  simp only [sdConsts, List.forall_mem_cons, Atom.Holds, List.not_mem_nil, IsEmpty.forall_iff,
    implies_true, and_true] at hC
  obtain ⟨c341, c342, c343, c344, c345⟩ := hC
  -- the pairs
  have hpair := fun p hp => pair_fwd (hP p hp)
  -- the blocks
  have hadd : ∀ k, 1 ≤ k → k ≤ 4 → ∀ c < 9, σ (.n (359 + 22 * (k - 1) + c)) =
      σ (.n (sdOut (k - 1) c)) + σ (.n (sdCell (17 * k / 2 + c))) := by
    intro k hk1 hk4 c hc
    have := hB (k - 1) (by omega) _ (List.mem_append_left _ (List.mem_map.mpr ⟨c, List.mem_range.mpr hc, rfl⟩))
    rwa [show k - 1 + 1 = k by omega] at this
  have hkk : ∀ k, 1 ≤ k → k ≤ 4 → (sdKeccak k).Holds rd σ := by
    intro k hk1 hk4
    have := hB (k - 1) (by omega) (sdKeccak (k - 1 + 1)) (List.mem_append_right _ (List.mem_singleton_self _))
    rwa [show k - 1 + 1 = k by omega] at this
  simp only [sdBlk5, List.forall_mem_cons, List.not_mem_nil, IsEmpty.forall_iff, implies_true,
    and_true] at hB5
  obtain ⟨a447, a448, a449, c450, a451, hk5⟩ := hB5
  -- the chain
  let C44 : List E := (List.range 44).map fun m => σ (.n (sdCell m))
  have hC44 : C44.length = 44 := by simp [C44]
  have hC44get : ∀ m < 44, C44.getD m 0 = σ (.n (sdCell m)) := fun m hm => by
    simp [C44, List.getD_eq_getElem?_getD, hm]
  let I : ℕ → Fin 13 → E := fun k c => σ (.n (sdIn k c))
  let O : ℕ → Fin 13 → E := fun k c => if k = 0 then 0 else σ (.n (sdOut (k - 1) c))
  have hkk' : ∀ k ≤ 5, (sdKeccak k).Holds rd σ := fun k hk => by
    rcases (show k = 0 ∨ (1 ≤ k ∧ k ≤ 4) ∨ k = 5 by omega) with rfl | ⟨hk1, hk4⟩ | rfl
    · exact hK0
    · exact hkk k hk1 hk4
    · exact hk5
  -- the true outputs: the state after block `k - 1`, whose cells the written values are
  let O' : ℕ → Fin 13 → E := fun k c => if k = 0 then 0 else
    cellsOfState (keccakF1600 (stateOfCells (I (k - 1)) (inLayout (k - 1)))) (outLayout 6 (k - 1)) c
  have hOO : ∀ k ≤ 5, O' k = O k := fun k hk => by
    funext c
    rcases Nat.eq_zero_or_pos k with rfl | hk0
    · rfl
    · simp only [O', O, show k ≠ 0 by omega, ↓reduceIte]
      exact ((keccak_holds (hkk' (k - 1) (by omega))).2 c
        (by simp [sdOutN, show k - 1 < 5 by omega])).symm
  have hP44 : ∀ m < 44, (padCells C44 704).getD m 0 = σ (.n (sdCell m)) := fun m hm => by
    rw [padCells_getD_lt _ _ (by omega) (by rw [show (704 : ℕ) / 16 = 44 from rfl]; omega)
      (by rw [show rate * (704 / rate + 1) - 1 = 815 from rfl]; omega), hC44get m hm]
  have hB6 : 704 / rate + 1 = 6 := rfl
  have hrate : ∀ k < 704 / rate + 1, ∀ c : Fin 13, c.val < 9 →
      I k c = O k c + (padCells C44 704).getD (17 * k / 2 + c) 0 := by
    intro k hk c hc
    rw [hB6] at hk
    rcases (show k = 0 ∨ (1 ≤ k ∧ k ≤ 4) ∨ k = 5 by omega) with rfl | ⟨hk1, hk4⟩ | rfl
    · simp only [I, O, sdIn, hc, ↓reduceIte, Nat.mul_zero, Nat.zero_div, zero_add]
      rw [hP44 _ (by omega)]
    · simp only [I, O, sdIn, hc, ↓reduceIte, show k ≠ 0 by omega, show k < 5 by omega]
      rw [hadd k hk1 hk4 c hc, hP44 _ (by omega)]
    · rw [show 17 * 5 / 2 + c.val = 42 + c.val by omega]
      rcases (show c.val = 0 ∨ c.val = 1 ∨ c.val = 2 ∨ (3 ≤ c.val ∧ c.val < 8) ∨ c.val = 8 by omega)
        with h0 | h1 | h2 | ⟨h3, h8⟩ | h8
      · simp (config := {decide := true}) only [I, O, sdIn, h0, ↓reduceIte]
        rw [a447, hP44 _ (by omega)]
      · simp (config := {decide := true}) only [I, O, sdIn, h1, ↓reduceIte]
        rw [a448, hP44 _ (by omega)]
      · simp (config := {decide := true}) only [I, O, sdIn, h2, ↓reduceIte]
        rw [a449, c341, padCells_44 C44 hC44 (by omega) (by omega)]
        simp
      · simp (config := {decide := true}) only [I, O, sdIn, hc, ↓reduceIte,
          show ¬ c.val < 2 by omega, show c.val ≠ 2 by omega, h8]
        rw [padCells_44 C44 hC44 (by omega) (by omega)]
        simp [show 42 + c.val ≠ 44 by omega, show 42 + c.val ≠ 50 by omega]
      · simp (config := {decide := true}) only [I, O, sdIn, h8, ↓reduceIte]
        rw [a451, c450, padCells_44 C44 hC44 (by omega) (by omega)]
        simp
  have hcap : ∀ k < 704 / rate + 1, ∀ c : Fin 13, 9 ≤ c.val → I k c = O k c := by
    intro k hk c hc
    rw [hB6] at hk
    rcases Nat.eq_zero_or_pos k with rfl | hk0
    · simp only [I, O, sdIn, show ¬ c.val < 9 by omega, ↓reduceIte]
      rcases (show c.val - 9 = 0 ∨ c.val - 9 = 1 ∨ c.val - 9 = 2 ∨ c.val - 9 = 3 by omega) with
        h | h | h | h <;> simp only [h, Nat.reduceAdd] <;>
        first | rw [c342, word_zero] | rw [c343, word_zero] | rw [c344, word_zero] |
          rw [c345, word_zero]
    · simp only [I, O, sdIn, show ¬ c.val < 9 by omega, ↓reduceIte, show k ≠ 0 by omega]
  have hrate' : ∀ k < 704 / rate + 1, ∀ c : Fin 13, c.val < 9 →
      I k c = O' k c + (padCells C44 704).getD (17 * k / 2 + c) 0 := fun k hk c hc => by
    rw [hOO k (by rw [hB6] at hk; omega)]; exact hrate k hk c hc
  have hcap' : ∀ k < 704 / rate + 1, ∀ c : Fin 13, 9 ≤ c.val → I k c = O' k c := fun k hk c hc => by
    rw [hOO k (by rw [hB6] at hk; omega)]; exact hcap k hk c hc
  have hK : ∀ k < 704 / rate + 1,
      KeccakCellsRelation (I k) (inLayout k) (O' (k + 1)) (outLayout (704 / rate + 1) k) .all := by
    intro k hk
    rw [hB6] at hk ⊢
    exact ⟨(keccak_holds (hkk' k (by omega))).1, fun c _ => by simp [O']⟩
  have h0 : O' 0 = cellsOfState (absorbChunks 0 zeroState []) false := by
    funext c
    simp only [O', ↓reduceIte]
    exact (cellsOfState_zero false c).symm
  have hz : ∀ j, 704 ≤ j → (cellsBytes C44).getD j 0 = 0 := fun j hj =>
    getD_of_length_le (by rw [length_cellsBytes, hC44]; omega)
  have hdig := keccak_final_digest (pre := []) (n := 0) rfl (by rw [hC44]) hz h0 hrate' hcap' hK
  rw [hB6, List.nil_append, List.take_of_length_le (by rw [length_cellsBytes, hC44])] at hdig
  -- the canonical header
  have hcan := (hK 0 (by rw [hB6]; omega)).1
  have can : ∀ m < 8, IsCanonical128 (σ (.n (9 + m))) := fun m hm => by
    have := hcan ⟨m, by omega⟩
    simpa [I, sdIn, sdCell, show m < 9 by omega, hm] using this
  -- the deferred cells
  let cells : List E := (List.range 24).map fun q => σ (.n (17 + 27 * (q / 2) + q % 2))
  have hcells : cells = (List.range 12).flatMap
      (fun p => [σ (.n (17 + 27 * p)), σ (.n (17 + 27 * p + 1))]) := by
    simp only [cells, range24_split]
    refine List.flatMap_congr fun p _ => ?_
    rw [show 2 * p / 2 = p by omega, show 2 * p % 2 = 0 by omega,
      show (2 * p + 1) / 2 = p by omega, show (2 * p + 1) % 2 = 1 by omega, Nat.add_zero]
  have e1 : (List.range 8).map (fun m => σ (.n (sdCell m))) =
      [σ (.n 0), σ (.n 1), σ (.n 2), σ (.n 3), σ (.n 4), σ (.n 5), σ (.n 6), σ (.n 7)] := by
    rw [← h9, ← h10, ← h11, ← h12, ← h13, ← h14, ← h15, ← h16]; rfl
  have e2 : (List.range 12).flatMap (fun p => [σ (.n (sdCell (8 + 3 * p))),
      σ (.n (sdCell (8 + 3 * p + 1))), σ (.n (sdCell (8 + 3 * p + 2)))]) =
      (List.range 12).flatMap (fun p => pairCells (σ (.n (17 + 27 * p))) (σ (.n (17 + 27 * p + 1)))) := by
    refine List.flatMap_congr fun p hp => ?_
    obtain ⟨-, -, hc3⟩ := hpair p (List.mem_range.mp hp)
    rw [sdCell_A, sdCell_B, sdCell_C]
    exact hc3
  have hbytes : cellsBytes C44 =
      stmtBytes [σ (.n 0), σ (.n 1), σ (.n 2), σ (.n 3), σ (.n 4), σ (.n 5), σ (.n 6), σ (.n 7)]
        cells := by
    show cellsBytes ((List.range 44).map fun m => σ (.n (sdCell m))) = _
    rw [range44_split, e1, e2, cellsBytes_append, stmtBytes, hcells, List.flatMap_assoc]
    congr 1
  -- the meaning
  simp only [core20_params, List.map_cons, List.map_nil] at hp
  subst hp
  refine ⟨cells, by simp [cells], fun k hk => ?_, ?_, ?_⟩
  · have hk' : k < 24 := by simpa [cells] using hk
    obtain ⟨la, lb, -⟩ := hpair (k / 2) (by omega)
    simp only [cells, List.getElem_map, List.getElem_range]
    rcases Nat.mod_two_eq_zero_or_one k with h2 | h2
    · rw [h2, Nat.add_zero, show k = 2 * (k / 2) by omega]
      rw [show 2 * (k / 2) / 2 = k / 2 by omega]
      exact la
    · rw [h2, show k = 2 * (k / 2) + 1 by omega, show (2 * (k / 2) + 1) / 2 = k / 2 by omega]
      exact lb
  · intro c hc
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · rw [← h9]; exact can 0 (by omega)
    · rw [← h10]; exact can 1 (by omega)
    · rw [← h11]; exact can 2 (by omega)
    · rw [← h12]; exact can 3 (by omega)
    · rw [← h13]; exact can 4 (by omega)
    · rw [← h14]; exact can 5 (by omega)
    · rw [← h15]; exact can 6 (by omega)
    · rw [← h16]; exact can 7 (by omega)
  · simp only [Atom.Holds] at h454 h455
    have hO6 : ∀ c : Fin 13, c.val < 2 → O' 6 c = σ (.n (sdOut 5 c)) := fun c hc =>
      ((keccak_holds hk5).2 c (by simpa [sdOutN] using hc)).symm
    rw [hO6 0 (by decide), hO6 1 (by decide)] at hdig
    rw [← hbytes, digestCells, ← hdig, ← hr]
    simp only [List.map_cons, List.map_nil, h454, h455]
    rfl

end
end LeanVM.Guest.B1.Digest
