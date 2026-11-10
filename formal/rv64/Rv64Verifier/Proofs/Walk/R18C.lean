import Rv64Verifier.Proofs.Walk.R18B

/-!
# `walk` R18, the table claims: the mirror's steps and the inner loop's head

`tableClaimsRust` one table at a time (`tableClaims_take_succ`), and done when the six bases or the
evaluations run out (`tableClaims_take_done`). `InnerR18`: at the inner loop's head `0x80003894`,
`j` of table `k`'s values appended.
-/

namespace Rv64Verifier.Proofs.Walk
open RiscvZkvm.Rv64 LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.Compile
  LeanVM.Protocol.Verifier Rv64Verifier.Runtime Rv64Verifier.Model Rv64Verifier.Transcript
  Rv64Verifier.Bus

theorem zip_take_eq {α β : Type} (a : List α) (b : List β) (n : Nat) (h : n ≤ a.length) :
    a.zip (b.take n) = (a.zip b).take n := by
  induction a generalizing b n with
  | nil => simp
  | cons x a ih =>
    cases b with
    | nil => simp
    | cons y b =>
      cases n with
      | zero => simp
      | succ n => simp [ih b n (by simp at h; omega)]

/-- The claims of the first `k + 1` tables: the first `k`'s, then table `k`'s. -/
theorem tableClaims_take_succ (evs : List (List E × List E)) (k : Nat) (hk : k < 6)
    (hl : k < evs.length) :
    tableClaimsRust (evs.take (k + 1)) = tableClaimsRust (evs.take k) ++
      evs[k].2.zipIdx.map fun (value, column) ↦
        (⟨LayoutMirror.globalColumnBasesRust.getD k 0 + column, evs[k].1, value⟩ : ColumnClaim) := by
  have hb : LayoutMirror.globalColumnBasesRust.length = 6 := by rw [bases_val]; rfl
  simp only [tableClaimsRust]
  rw [zip_take_eq _ _ _ (by omega), zip_take_eq _ _ _ (by omega), List.take_add_one,
    List.flatMap_append, List.getElem?_eq_getElem (by simp; omega)]
  simp [List.getElem_zip, List.getElem?_eq_getElem (show k < LayoutMirror.globalColumnBasesRust.length by omega)]

/-- Six tables' claims are all of them. -/
theorem tableClaims_take_six (evs : List (List E × List E)) :
    tableClaimsRust (evs.take 6) = tableClaimsRust evs := by
  have hb : LayoutMirror.globalColumnBasesRust.length = 6 := by rw [bases_val]; rfl
  simp only [tableClaimsRust]
  rw [zip_take_eq _ _ _ (by omega), List.take_of_length_le (by simp; omega)]

theorem tableClaims_take_done (evs : List (List E × List E)) (k : Nat)
    (hk : k = evs.length ∨ k = 6) : tableClaimsRust (evs.take k) = tableClaimsRust evs := by
  rcases hk with rfl | rfl
  · rw [List.take_length]
  · exact tableClaims_take_six evs

/-- Table `k`'s claims: its values, each with its column and the table's point. -/
def tableClaimsOf (evs : List (List E × List E)) (k : Nat) : List ColumnClaim :=
  (evs.getD k ([], [])).2.zipIdx.map fun (value, column) ↦
    ⟨LayoutMirror.globalColumnBasesRust.getD k 0 + column, (evs.getD k ([], [])).1, value⟩

theorem tableClaims_succ (evs : List (List E × List E)) (k : Nat) (hk : k < 6)
    (hl : k < evs.length) :
    tableClaimsRust (evs.take (k + 1)) = tableClaimsRust (evs.take k) ++ tableClaimsOf evs k := by
  rw [tableClaims_take_succ evs k hk hl, tableClaimsOf, List.getD_eq_getElem _ _ hl]

/-- At `0x80003894`, `j` of table `k`'s `n` values appended (`n - j` left, none done twice), the
buffer having room for all `n`. -/
structure InnerR18 (OI : MachineState → Word → List (List Opening) → Prop)
    (s u₀ w t u : MachineState) (layout : LayoutMirror.LayoutRust) (rows : List (BitVec 64))
    (lir : BitVec 64) (bus : BusResultRust) (evs : List (List E × List E)) (k j : Nat)
    (P C L : Word) : Prop where
  pc : u.pc = 0x80003894
  rest : Rest s u₀ u
  wmono : heapNext u₀ ≤ heapNext w
  tmono : heapNext t ≤ heapNext u
  evKept : ∀ x : Word, heapNext w ≤ x.toNat → x.toNat + 8 ≤ heapNext t → u.getMem x = t.getMem x
  rowsAt : RowsAt w t (s.getReg .x2 - 928) evs
  hk : k < 6 ∧ k < evs.length
  hj : j < (evs.getD k ([], [])).2.length
  x8 : u.getReg .x8 = 6
  x9 : u.getReg .x9 = 0xffffffffffffffff
  x18 : u.getReg .x18 = BitVec.ofNat 64 k
  x19 : u.getReg .x19 = s.getReg .x2 - 896
  x21 : u.getReg .x21 = s.getReg .x2 - 1312
  x22 : u.getReg .x22 = vecPtr t (s.getReg .x2 - 928) + 48 * vecLen t (s.getReg .x2 - 928)
  x23 : u.getReg .x23 = vecPtr t (s.getReg .x2 - 928) + BitVec.ofNat 64 (48 * k)
  x20 : u.getReg .x20 = BitVec.ofNat 64 ((evs.getD k ([], [])).2.length - j)
  x24 : u.getReg .x24 = vecPtr t (vecPtr t (s.getReg .x2 - 928) + BitVec.ofNat 64 (48 * k + 24)) +
    BitVec.ofNat 64 (24 * j)
  x25 : u.getReg .x25 = L + BitVec.ofNat 64 (evs.getD k ([], [])).2.length
  x26 : u.getReg .x26 = BitVec.ofNat 64 (LayoutMirror.globalColumnBasesRust.getD k 0 + j)
  x27 : u.getReg .x27 = P + BitVec.ofNat 64 (56 * (L.toNat + j))
  bases : ∀ i < 6, u.getMem (s.getReg .x2 - 896 + BitVec.ofNat 64 (8 * i)) =
    BitVec.ofNat 64 (LayoutMirror.globalColumnBasesRust.getD i 0)
  capSlot : u.getMem (s.getReg .x2 - 1632) = C
  ptrSlot : u.getMem (s.getReg .x2 - 1624) = P
  lenSlot : u.getMem (s.getReg .x2 - 1616) = L
  ptr184 : u.getMem (s.getReg .x2 - 2472) = P
  len : L.toNat + (evs.getD k ([], [])).2.length ≤ C.toNat
  buf : P.toNat % 8 = 0 ∧ P.toNat + 56 * C.toNat ≤ heapNext u ∧
    ((P = vecPtr u₀ (s.getReg .x2 - 928) ∧ C = vecCap u₀ (s.getReg .x2 - 928)) ∨
      heapNext t ≤ P.toNat)
  claims : claimsIn u P (L.toNat + j) =
    bus.claims ++ tableClaimsRust (evs.take k) ++ (tableClaimsOf evs k).take j
  points : ∀ i < L.toNat + j, Old s u (vecPtr u (P + BitVec.ofNat 64 (56 * i)))
      (24 * (vecLen u (P + BitVec.ofNat 64 (56 * i))).toNat) ∧
    Apart (vecPtr u (P + BitVec.ofNat 64 (56 * i)))
      (24 * (vecLen u (P + BitVec.ofNat 64 (56 * i))).toNat) P (56 * C.toNat)
  tracks : TracksR OI s u
    (PcsContracts.digestAt u₀ (s.getReg .x2 - 1800), stackShape layout.stackLog lir.toNat)
    (afterTables (bytesAt s (s.getReg .x12) 32) layout rows lir bus evs)

end Rv64Verifier.Proofs.Walk
