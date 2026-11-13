/-
  LeanVM.Guest.B1.Main.Digests

  The digests of decoded statements: claim lists read off cells hash as the cells, and a
  statement's digest is the bytes `statement_digest` hashes.
-/

module

public import LeanVM.Guest.B1.Main.Decode

/-!
# Decoded digests

* `slotCells_of_loads`: a slot's four cells, from four loads;
* `xmss_digest`, `sphincs_digest`: a list of claims decoded at slots whose cells are `cells`, four
  a slot, hashes as `cells`;
* `daDigestAt_of_loads`: a DA digest slot of `da_digests` of two loads, its bytes theirs;
* `statementDigest_parts`: a statement's digest from the bytes of its header cells and deferred
  cells (`stmtBytes`);
* `deferOfCells_cells`, `fixedOfCells_cells`, `readCells_of_readsAt`: the deferred claims of
  `24` cells.
-/

namespace LeanVM.Guest.B1.Main

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Value.Keccak
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Guest.B1.Digest LeanVM.Node

@[expose] public section

variable {C : CallRel}

variable {rd : Reader}

/-! ## Slots -/

theorem slotCells_of_loads {p : E} {o : ℕ} {v : ℕ → E}
    (h : ∀ i < 4, LoadHolds rd p (4 * o + i) (v i)) :
    slotCells rd p o = [v 0, v 1, v 2, v 3] := by
  simp only [slotCells, readCells_eq_memRun, memRun, List.range_succ, List.range_zero,
    List.nil_append, List.map_cons, List.map_nil, List.cons_append]
  have hl : ∀ k < 4, memAt rd (p * gen ^ (4 * o)) k = v k := fun k hk =>
    memAt_of_load ((loadHolds_mul_gen_pow rd p _ _ _).mpr (h k hk))
  rw [hl 0 (by omega), hl 1 (by omega), hl 2 (by omega), hl 3 (by omega)]

/-- The slots `o j`, `j < n`, of the table at `p` hold `cells`, four a slot. -/
def SlotsHold (rd : Reader) (p : E) (o : ℕ → ℕ) (n : ℕ) (cells : List E) : Prop :=
  cells.length = 4 * n ∧ ∀ j < n, ∀ i < 4, LoadHolds rd p (4 * o j + i) (cells.getD (4 * j + i) 0)

theorem slotsHold_of_readsAt {p : E} {n : ℕ} {cells : List E} (h : ReadsAt rd p cells)
    (hl : cells.length = 4 * n) : SlotsHold rd p id n cells := by
  refine ⟨hl, fun j hj i hi => ?_⟩
  have := h (4 * j + i) (by omega)
  rwa [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega), Option.getD_some]

theorem slotCells_slots {p : E} {o : ℕ → ℕ} {n : ℕ} {cells : List E} (h : SlotsHold rd p o n cells)
    {j : ℕ} (hj : j < n) :
    slotCells rd p (o j) = [cells.getD (4 * j) 0, cells.getD (4 * j + 1) 0,
      cells.getD (4 * j + 2) 0, cells.getD (4 * j + 3) 0] :=
  slotCells_of_loads (v := fun i => cells.getD (4 * j + i) 0) (h.2 j hj)

/-- A list of claims decoded at the slots `o j` of a table hashes as the slots' cells. -/
theorem claims_digest {α : Type} (dec : E → E → E → E → α) (bytes : α → List UInt8)
    (hb : ∀ a b c d, bytes (dec a b c d) = cellsBytes [a, b, c, d]) {p : E} {o : ℕ → ℕ} {n : ℕ}
    {cells : List E} (h : SlotsHold rd p o n cells) :
    ((List.range n).map fun j => let c := slotCells rd p (o j)
      dec (c.getD 0 0) (c.getD 1 0) (c.getD 2 0) (c.getD 3 0)).flatMap bytes = cellsBytes cells := by
  rw [← flatMap_slots dec bytes hb cells n h.1]
  congr 1
  refine List.map_congr_left fun j hj => ?_
  rw [slotCells_slots h (List.mem_range.mp hj)]
  rfl

theorem xmss_digest {p : E} {o : ℕ → ℕ} {n : ℕ} {cells : List E} (h : SlotsHold rd p o n cells) :
    claimListDigest xmssPublicKeyBytes ((List.range n).map fun j => xmssAt rd p (o j)) = keccak256 (cellsBytes cells) := by
  unfold claimListDigest claimListPreimage
  rw [← claims_digest Sig.xmssClaimOf (fun c : LeanXmssClaim => claimBytesOf c.1.root c.1.parameter c.2)
    (fun a b c d => claimBytes_cells a b c d) h]
  rfl

theorem sphincs_digest {p : E} {o : ℕ → ℕ} {n : ℕ} {cells : List E} (h : SlotsHold rd p o n cells) :
    claimListDigest Sphincs.PublicKey.toBytes ((List.range n).map fun j => sphincsAt rd p (o j)) =
      keccak256 (cellsBytes cells) := by
  unfold claimListDigest claimListPreimage
  rw [← claims_digest Sig.sphincsClaimOf
    (fun c : LeanSphincsClaim => claimBytesOf c.1.publicSeed c.1.root c.2)
    (fun a b c d => claimBytes_cells a b c d) h]
  rfl

theorem xmss_digest_id {p : E} {n : ℕ} {cells : List E} (h : SlotsHold rd p id n cells) :
    claimListDigest xmssPublicKeyBytes ((List.range n).map (xmssAt rd p)) = keccak256 (cellsBytes cells) :=
  xmss_digest h

theorem sphincs_digest_id {p : E} {n : ℕ} {cells : List E} (h : SlotsHold rd p id n cells) :
    claimListDigest Sphincs.PublicKey.toBytes ((List.range n).map (sphincsAt rd p)) = keccak256 (cellsBytes cells) :=
  sphincs_digest h

/-! ## DA digests -/

/-- Two zero cells decode to the zero digest. -/
theorem digestOfCells_zero : digestOfCells 0 0 = zeroDigest := by
  simp only [digestOfCells, zeroDigest, limb_zero]
  rfl

/-- A DA digest slot of `da_digests` holding the cells `d0`, `d1` decodes to their digest, whose
bytes are theirs. -/
theorem daDigestAt_of_loads {σ : Val} {k : ℕ} {d0 d1 : E}
    (h0 : LoadHolds rd (σ (.n 364)) (2 * k) d0) (h1 : LoadHolds rd (σ (.n 364)) (2 * k + 1) d1) :
    daDigestAt rd σ k = digestOfCells d0 d1 ∧
      digestBytes (daDigestAt rd σ k) = cellsBytes [d0, d1] := by
  have e : daDigestAt rd σ k = digestOfCells d0 d1 := by
    unfold daDigestAt
    rw [cellAt_eq_memAt, memAt_of_load h0, memAt_of_load h1]
  exact ⟨e, by rw [e, digestBytes_ofCells]⟩

/-! ## The statement -/

theorem digestBytes_of_cells {d : Digest} {a b : E} (h : [a, b] = digestCells d) :
    digestBytes d = cellsBytes [a, b] := by
  rw [digestBytes_eq_cells]
  simp only [digestCells, List.cons.injEq, and_true] at h
  rw [h.1, h.2]

theorem cellsBytes_eight (a b c d e f g h : E) :
    cellsBytes [a, b, c, d, e, f, g, h] =
      cellsBytes [a, b] ++ cellsBytes [c, d] ++ cellsBytes [e, f] ++ cellsBytes [g, h] := by
  simp [cellsBytes]

/-- **A statement's digest from its parts**: the header cells' bytes and the 24 deferred cells. -/
theorem statementDigest_parts {seed : Digest} {s : NodeStatement} {s0 s1 x0 x1 y0 y1 d0 d1 : E}
    {defer : List E} (hseed : digestBytes seed = cellsBytes [s0, s1])
    (hx : digestBytes (claimListDigest xmssPublicKeyBytes s.claims.xmss) = cellsBytes [x0, x1])
    (hs : digestBytes (claimListDigest Sphincs.PublicKey.toBytes s.claims.sphincs) = cellsBytes [y0, y1])
    (hda : digestBytes s.claims.daDigest = cellsBytes [d0, d1])
    (hdef : s.deferredClaim.cells = defer) :
    statementDigest seed s = keccak256 (stmtBytes [s0, s1, x0, x1, y0, y1, d0, d1] defer) := by
  unfold statementDigest statementPreimage stmtBytes
  rw [hseed, hx, hs, hda, hdef, cellsBytes_eight]

/-! ## Deferred claims of 24 cells -/

theorem readCells_of_readsAt {p : E} {cells : List E} (h : ReadsAt rd p cells) (hl : cells.length = 24) :
    readCells rd p 24 = cells := by
  rw [readCells_eq_memRun, ← hl, ← readsAt_memRun h]

theorem deferOfCells_cells {cells : List E} (hl : cells.length = 24) :
    (deferOfCells cells).cells = cells := by
  have hb : bytecodeVars = 23 := rfl
  unfold deferOfCells DeferredClaim.cells
  rw [hb, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega), Option.getD_some]
  simp only
  rw [← List.take_succ_eq_append_getElem (by omega), List.take_of_length_le (by omega)]

theorem deferOfCells_point {cells : List E} (hl : cells.length = 24) :
    (deferOfCells cells).bytecodePoint.length = bytecodeVars := by
  simp [deferOfCells, hl, bytecodeVars]

theorem fixedOfCells_cells {f : BytecodeClaim} (hl : f.bytecodePoint.length = bytecodeVars) :
    fixedOfCells (DeferredClaim.cells f) = f := by
  have hb : bytecodeVars = 23 := rfl
  unfold fixedOfCells DeferredClaim.cells
  rw [List.take_append_of_le_length (by omega), List.take_of_length_le (by omega),
    List.getD_eq_getElem?_getD, List.getElem?_append_right (by omega), hl]
  simp

end
end LeanVM.Guest.B1.Main
