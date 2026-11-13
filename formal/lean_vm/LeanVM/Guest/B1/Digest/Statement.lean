/-
  LeanVM.Guest.B1.Digest.Statement

  B1 for `statement_digest` (G:4250-4274): the statement's digest, byte for byte.
-/

module

public import LeanVM.Guest.B1.Digest.Basic

/-!
# `statement_digest`

`statement_digest(seed_0, seed_1, xd_0, xd_1, sd_0, sd_1, da_0, da_1, defer)` hashes 32 cells: the
seed's two cells, the two claim lists' digests' two each, the DA digest's two, then the 24
deferred cells (read at `defer`), each cell its two limbs: `512` bytes in four `KECCAK` blocks,
the padding's `0x01` (byte `512`, cell `32`) and `0x80` (byte `543`, cell `33`) in the last. Its
core IR (`fn% «statement_digest»`) is the template `sdAtoms` (`sd_body`, by kernel evaluation);
`keccak_final_digest` makes the chain Keccak-256 of the cells' bytes.
-/

namespace LeanVM.Guest.B1.Digest

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Value.Keccak
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

/-! ## The template -/

/-- The value of hashed cell `m < 33`: the eight header cells, the 24 deferred cells, then the
padding's `0x01` cell. -/
def sdCell (m : ℕ) : ℕ := 9 + m

/-- The value of output cell `c` of block `k < 4`. -/
def sdOut (k c : ℕ) : ℕ := if k < 3 then 46 + 22 * k + c else 113 + c

/-- The value of input cell `c` of block `k < 4`. -/
def sdIn (k c : ℕ) : ℕ :=
  if c < 9 then
    (if k = 0 then sdCell c else if k < 3 then 59 + 22 * (k - 1) + c else if c < 8 then 103 + c
      else 112)
  else (if k = 0 then 42 + (c - 9) else sdOut (k - 1) c)

/-- The cells block `k` writes: the thirteen of the state, the last block the digest's two
(`out_cells`). -/
def sdOutN (k : ℕ) : ℕ := if k < 3 then 13 else 2

/-- The `KECCAK` of block `k`. -/
def sdKeccak (k : ℕ) : Atom :=
  .keccak ((List.range 13).map fun c => .n (sdIn k c))
    ((List.range (sdOutN k)).map fun c => .n (sdOut k c)) (inLayout k) (outLayout 4 k)

/-- The header cells. -/
def sdHdr : List Atom :=
  [.copy (.n 9) (.n 0), .copy (.n 10) (.n 1), .copy (.n 11) (.n 2), .copy (.n 12) (.n 3),
   .copy (.n 13) (.n 4), .copy (.n 14) (.n 5), .copy (.n 15) (.n 6), .copy (.n 16) (.n 7)]

/-- The deferred cells, read at `defer`. -/
def sdLoads : List Atom := (List.range 24).map fun i => .load (.n (17 + i)) (.n 8) i

/-- The constants: the padding's `0x01` cell and the zero capacity of the first block. -/
def sdConsts : List Atom :=
  [.const (.n 41) (word 1 0), .const (.n 42) (word 0 0), .const (.n 43) (word 0 0),
   .const (.n 44) (word 0 0), .const (.n 45) (word 0 0)]

/-- Block `k ∈ {1, 2}`: nine message cells XORed into the previous output, then its `KECCAK`. -/
def sdBlk (k : ℕ) : List Atom :=
  (List.range 9).map (fun c => .add (.n (59 + 22 * (k - 1) + c)) (.n (sdOut (k - 1) c))
    (.n (sdCell (17 * k / 2 + c)))) ++ [sdKeccak k]

/-- The padding's last cell (`0x80` at byte `543`, the last byte of the fourth block). -/
abbrev padWord : E := word 0 9223372036854775808

/-- The last block: the message's last seven cells and the padding's `0x01` cell, the padding's
`0x80` cell, its `KECCAK`. -/
def sdBlk3 : List Atom :=
  (List.range 8).map (fun c => .add (.n (103 + c)) (.n (sdOut 2 c)) (.n (sdCell (25 + c)))) ++
    [.const (.n 111) padWord, .add (.n 112) (.n (sdOut 2 8)) (.n 111), sdKeccak 3]

/-- `statement_digest`'s atoms. -/
def sdAtoms : List Atom :=
  sdHdr ++ sdLoads ++ sdConsts ++ [sdKeccak 0] ++ (List.range 2).flatMap (fun j => sdBlk (j + 1)) ++
    sdBlk3 ++ [.copy (.n 115) (.n 113), .copy (.n 116) (.n 114)]

set_option maxRecDepth 100000 in
theorem sd_body : Fn.body fn% «statement_digest» = sdAtoms.map Stmt.atom ++ [.ret [.n 115,
    .n 116]] :=
  stmtsEqb_sound (by decide +kernel)

theorem sd_params : Fn.params fn% «statement_digest» =
    [.n 0, .n 1, .n 2, .n 3, .n 4, .n 5, .n 6, .n 7, .n 8] := rfl

/-! ## The cells -/

theorem cells13_map_range (σ : Val) (f : ℕ → ℕ) (c : Fin 13) :
    cells13 (((List.range 13).map fun c => V.n (f c)).map σ) c = σ (.n (f c)) := by
  simp [cells13, List.getD_eq_getElem?_getD, c.isLt]

/-- Block `k`'s `KECCAK`: its written cells are the first of their Keccak-f. -/
theorem keccak_holds {rd : Reader} {σ : Val} {k : ℕ} (h : (sdKeccak k).Holds rd σ) :
    ∀ c : Fin 13, c.val < sdOutN k →
      σ (.n (sdOut k c)) = cellsOfState (keccakF1600 (stateOfCells
        (fun c : Fin 13 => σ (.n (sdIn k c))) (inLayout k))) (outLayout 4 k) c := by
  obtain ⟨-, -, O, hK, hw⟩ := keccak_holds_full h
  have e1 : cells13 (((List.range 13).map fun c => V.n (sdIn k c)).map σ) =
      fun c : Fin 13 => σ (.n (sdIn k c)) := funext (cells13_map_range σ _)
  rw [e1] at hK
  intro c hc
  have := hw c (by simpa using hc)
  simp only [List.getElem_map, List.getElem_range] at this
  rw [this, hK c c.isLt]

/-- The padded 32-cell message past its cells: the `0x01` cell at `32`, the `0x80` cell at
`33`. -/
theorem padCells_32 (cells : List E) (hl : cells.length = 32) {i : ℕ} (h1 : 32 ≤ i) (h2 : i < 34) :
    (padCells cells 512).getD i 0 = if i = 32 then word 1 0 else padWord := by
  have hr : padRead 512 - cells.length = 2 := by rw [hl]; rfl
  unfold padCells xorByte
  rw [show rate * (512 / rate + 1) - 1 = 543 from rfl, show (543 : ℕ) / 16 = 33 from rfl,
    show (512 : ℕ) / 16 = 32 from rfl, hr, List.getD_eq_getElem?_getD, List.getElem?_modify,
    List.getElem?_modify, List.getElem?_append_right (by omega), hl,
    List.getElem?_replicate_of_lt (by omega)]
  unfold byteCell
  simp only [show (512 : ℕ) % 16 = 0 from rfl, show (543 : ℕ) % 16 = 15 from rfl]
  rcases (show i = 32 ∨ i = 33 by omega) with rfl | rfl
  · simp [word_eOfNat]
  · simp [padWord]

/-! ## Soundness -/

set_option maxRecDepth 100000 in
/-- **`statement_digest` computes the statement's digest.** -/
theorem statement_digest_sound : statement_digest_sound_Spec := by
  intro rd args rets h
  obtain ⟨σ, hp, hb⟩ := (rel_iff_sem find_statement_digest args rets).mp h
  rw [sd_body, holdsList_atoms_ret] at hb
  obtain ⟨hat, hr⟩ := hb
  simp only [sdAtoms, List.forall_mem_append, List.forall_mem_cons, List.not_mem_nil,
    IsEmpty.forall_iff, implies_true, and_true] at hat
  obtain ⟨⟨⟨⟨⟨⟨hH, hL⟩, hC⟩, hK0⟩, hB⟩, hB3⟩, h115, h116⟩ := hat
  rw [forall_mem_flatMap_range] at hB
  -- the header
  simp only [sdHdr, List.forall_mem_cons, Atom.Holds, List.not_mem_nil, IsEmpty.forall_iff,
    implies_true, and_true] at hH
  obtain ⟨h9, h10, h11, h12, h13, h14, h15, h16⟩ := hH
  -- the constants
  simp only [sdConsts, List.forall_mem_cons, Atom.Holds, List.not_mem_nil, IsEmpty.forall_iff,
    implies_true, and_true] at hC
  obtain ⟨c41, c42, c43, c44, c45⟩ := hC
  -- the loads
  have hload : ∀ i < 24, LoadHolds rd (σ (.n 8)) i (σ (.n (17 + i))) := fun i hi =>
    hL _ (List.mem_map.mpr ⟨i, List.mem_range.mpr hi, rfl⟩)
  -- the blocks
  have hadd : ∀ k, 1 ≤ k → k ≤ 2 → ∀ c < 9, σ (.n (59 + 22 * (k - 1) + c)) =
      σ (.n (sdOut (k - 1) c)) + σ (.n (sdCell (17 * k / 2 + c))) := by
    intro k hk1 hk2 c hc
    have := hB (k - 1) (by omega) _
      (List.mem_append_left _ (List.mem_map.mpr ⟨c, List.mem_range.mpr hc, rfl⟩))
    rwa [show k - 1 + 1 = k by omega] at this
  have hkk : ∀ k, 1 ≤ k → k ≤ 2 → (sdKeccak k).Holds rd σ := by
    intro k hk1 hk2
    have := hB (k - 1) (by omega) (sdKeccak (k - 1 + 1))
      (List.mem_append_right _ (List.mem_singleton_self _))
    rwa [show k - 1 + 1 = k by omega] at this
  simp only [sdBlk3, List.forall_mem_append, List.forall_mem_cons, List.not_mem_nil,
    IsEmpty.forall_iff, implies_true, and_true] at hB3
  obtain ⟨hA3, c111, a112, hk3⟩ := hB3
  have hadd3 : ∀ c < 8, σ (.n (103 + c)) = σ (.n (sdOut 2 c)) + σ (.n (sdCell (25 + c))) :=
    fun c hc => hA3 _ (List.mem_map.mpr ⟨c, List.mem_range.mpr hc, rfl⟩)
  -- the chain
  let C32 : List E := (List.range 32).map fun m => σ (.n (sdCell m))
  have hC32 : C32.length = 32 := by simp [C32]
  have hC32get : ∀ m < 32, C32.getD m 0 = σ (.n (sdCell m)) := fun m hm => by
    simp [C32, List.getD_eq_getElem?_getD, hm]
  let I : ℕ → Fin 13 → E := fun k c => σ (.n (sdIn k c))
  let O : ℕ → Fin 13 → E := fun k c => if k = 0 then 0 else σ (.n (sdOut (k - 1) c))
  have hkk' : ∀ k ≤ 3, (sdKeccak k).Holds rd σ := fun k hk => by
    rcases (show k = 0 ∨ (1 ≤ k ∧ k ≤ 2) ∨ k = 3 by omega) with rfl | ⟨hk1, hk2⟩ | rfl
    · exact hK0
    · exact hkk k hk1 hk2
    · exact hk3
  -- the true outputs: the state after block `k - 1`, whose cells the written values are
  let O' : ℕ → Fin 13 → E := fun k c => if k = 0 then 0 else
    cellsOfState (keccakF1600 (stateOfCells (I (k - 1)) (inLayout (k - 1)))) (outLayout 4 (k - 1)) c
  have hOO : ∀ k ≤ 3, O' k = O k := fun k hk => by
    funext c
    rcases Nat.eq_zero_or_pos k with rfl | hk0
    · rfl
    · simp only [O', O, show k ≠ 0 by omega, ↓reduceIte]
      exact (keccak_holds (hkk' (k - 1) (by omega)) c
        (by simp [sdOutN, show k - 1 < 3 by omega])).symm
  have hP32 : ∀ m < 32, (padCells C32 512).getD m 0 = σ (.n (sdCell m)) := fun m hm => by
    rw [padCells_getD_lt _ _ (by omega) (by rw [show (512 : ℕ) / 16 = 32 from rfl]; omega)
      (by rw [show rate * (512 / rate + 1) - 1 = 543 from rfl]; omega), hC32get m hm]
  have hB4 : 512 / rate + 1 = 4 := rfl
  have hrate : ∀ k < 512 / rate + 1, ∀ c : Fin 13, c.val < 9 →
      I k c = O k c + (padCells C32 512).getD (17 * k / 2 + c) 0 := by
    intro k hk c hc
    rw [hB4] at hk
    rcases (show k = 0 ∨ (1 ≤ k ∧ k ≤ 2) ∨ k = 3 by omega) with rfl | ⟨hk1, hk2⟩ | rfl
    · simp only [I, O, sdIn, hc, ↓reduceIte, Nat.mul_zero, Nat.zero_div, zero_add]
      rw [hP32 _ (by omega)]
    · simp only [I, O, sdIn, hc, ↓reduceIte, show k ≠ 0 by omega, show k < 3 by omega]
      rw [hadd k hk1 hk2 c hc, hP32 _ (by omega)]
    · rw [show 17 * 3 / 2 + c.val = 25 + c.val by omega]
      rcases (show c.val < 7 ∨ c.val = 7 ∨ c.val = 8 by omega) with h7 | h7 | h8
      · simp (config := {decide := true}) only [I, O, sdIn, hc, ↓reduceIte,
          show c.val < 8 by omega]
        rw [hadd3 c (by omega), hP32 _ (by omega)]
      · simp (config := {decide := true}) only [I, O, sdIn, hc, ↓reduceIte,
          show c.val < 8 by omega]
        rw [hadd3 c (by omega), h7, padCells_32 C32 hC32 (by omega) (by omega)]
        simp only [sdCell, ↓reduceIte, Nat.reduceAdd, c41]
      · simp (config := {decide := true}) only [I, O, sdIn, h8, ↓reduceIte]
        rw [a112, c111, padCells_32 C32 hC32 (by omega) (by omega)]
        simp
  have hcap : ∀ k < 512 / rate + 1, ∀ c : Fin 13, 9 ≤ c.val → I k c = O k c := by
    intro k hk c hc
    rw [hB4] at hk
    rcases Nat.eq_zero_or_pos k with rfl | hk0
    · simp only [I, O, sdIn, show ¬ c.val < 9 by omega, ↓reduceIte]
      rcases (show c.val - 9 = 0 ∨ c.val - 9 = 1 ∨ c.val - 9 = 2 ∨ c.val - 9 = 3 by omega) with
        h | h | h | h <;> simp only [h, Nat.reduceAdd] <;>
        first | rw [c42, word_zero] | rw [c43, word_zero] | rw [c44, word_zero] |
          rw [c45, word_zero]
    · simp only [I, O, sdIn, show ¬ c.val < 9 by omega, ↓reduceIte, show k ≠ 0 by omega]
  have hrate' : ∀ k < 512 / rate + 1, ∀ c : Fin 13, c.val < 9 →
      I k c = O' k c + (padCells C32 512).getD (17 * k / 2 + c) 0 := fun k hk c hc => by
    rw [hOO k (by rw [hB4] at hk; omega)]; exact hrate k hk c hc
  have hcap' : ∀ k < 512 / rate + 1, ∀ c : Fin 13, 9 ≤ c.val → I k c = O' k c :=
    fun k hk c hc => by
      rw [hOO k (by rw [hB4] at hk; omega)]; exact hcap k hk c hc
  have hK : ∀ k < 512 / rate + 1,
      KeccakCellsRelation (I k) (inLayout k) (O' (k + 1)) (outLayout (512 / rate + 1) k) .all := by
    intro k hk
    rw [hB4] at hk ⊢
    exact fun c _ => by simp [O']
  have h0 : O' 0 = cellsOfState (absorbChunks 0 zeroState []) false := by
    funext c
    simp only [O', ↓reduceIte]
    exact (cellsOfState_zero false c).symm
  have hz : ∀ j, 512 ≤ j → (cellsBytes C32).getD j 0 = 0 := fun j hj =>
    getD_of_length_le (by rw [length_cellsBytes, hC32]; omega)
  have hdig := keccak_final_digest (pre := []) (n := 0) rfl (by rw [hC32]) hz h0 hrate' hcap' hK
  rw [hB4, List.nil_append, List.take_of_length_le (by rw [length_cellsBytes, hC32])] at hdig
  -- the deferred cells
  let cells : List E := (List.range 24).map fun q => σ (.n (17 + q))
  have e1 : (List.range 8).map (fun m => σ (.n (sdCell m))) =
      [σ (.n 0), σ (.n 1), σ (.n 2), σ (.n 3), σ (.n 4), σ (.n 5), σ (.n 6), σ (.n 7)] := by
    rw [← h9, ← h10, ← h11, ← h12, ← h13, ← h14, ← h15, ← h16]; rfl
  have hsplit : C32 = (List.range 8).map (fun m => σ (.n (sdCell m))) ++ cells := rfl
  have hbytes : cellsBytes C32 =
      stmtBytes [σ (.n 0), σ (.n 1), σ (.n 2), σ (.n 3), σ (.n 4), σ (.n 5), σ (.n 6), σ (.n 7)]
        cells := by
    rw [hsplit, e1, cellsBytes_append, stmtBytes]
    rfl
  -- the meaning
  simp only [sd_params, List.map_cons, List.map_nil] at hp
  subst hp
  refine ⟨cells, by simp [cells], fun k hk => ?_, ?_⟩
  · have hk' : k < 24 := by simpa [cells] using hk
    simp only [cells, List.getElem_map, List.getElem_range]
    exact hload k hk'
  · simp only [Atom.Holds] at h115 h116
    have hO4 : ∀ c : Fin 13, c.val < 2 → O' 4 c = σ (.n (sdOut 3 c)) := fun c hc =>
      ((keccak_holds hk3) c (by simpa [sdOutN] using hc)).symm
    rw [hO4 0 (by decide), hO4 1 (by decide)] at hdig
    rw [← hbytes, digestCells, ← hdig, ← hr]
    simp only [List.map_cons, List.map_nil, h115, h116]
    rfl

end
end LeanVM.Guest.B1.Digest
