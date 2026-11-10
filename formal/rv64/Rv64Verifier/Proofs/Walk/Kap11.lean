import Rv64Verifier.Proofs.Walk.Keep11

/-!
# `walk`: `kappas` (R11), its head

`kapPre A k i` is `kappasRust` over the first `i` tables (`kapPre_six`). At the loop's header
`0x800030c8` (`Kap11 .. i`), the `Vec<K>` at `sp + 1312` holds it (`KapVec`). `r11head` runs from
`0x80003038` (`AtR11`): the bound on `sp + 152`, `alloc(8, 48)` and the six framework kappas.
-/

namespace Rv64Verifier.Proofs.Walk
open RiscvZkvm.Rv64 LeanVM.Parameters LeanVM.Protocol.Compile Rv64Verifier.Runtime
  Rv64Verifier.Model Rv64Verifier.Transcript Rv64Verifier.Layout Rv64Verifier.Model.LayoutMirror
  Rv64Verifier.Blocks.F4
open Rv64Verifier.Sym (reduceReg reducePc reduceMem reduceWrites reduceObl)

/-- The heights. -/
abbrev hts (A : List E) : List Nat := tableLogHeightsRust (rowsOf A)

/-- The framework columns' and `q_keccak`'s kappas. -/
def kap0 (A : List E) (k : Nat) : List Nat :=
  [(lmOf A).toNat, (lmOf A).toNat, (lmOf A).toNat, (lmOf A).toNat, k - 4, (hts A).getD 5 0 + 6]

def kapStep (A : List E) (kappas : List Nat) (t : TableRust) : List Nat :=
  kappas ++ List.replicate t.width ((hts A).getD t.opcode 0)

/-- `kappas` after the first `i` tables. -/
def kapPre (A : List E) (k i : Nat) : List Nat := (tablesRust.take i).foldl (kapStep A) (kap0 A k)

/-- Its length. -/
def kapLen (i : Nat) : Nat := 6 + (tableWidthsRust.take i).sum

theorem kapPre_succ (A : List E) (k : Nat) {i : Nat} {t : TableRust} (h : tablesRust[i]? = some t) :
    kapPre A k (i + 1) =
      kapPre A k i ++ List.replicate (tableWidthsRust.getD i 0) ((hts A).getD i 0) := by
  have ho := tablesRust_opcode_eq h
  rw [kapPre, List.take_add_one, h, Option.toList_some, List.foldl_append, List.foldl_cons,
    List.foldl_nil, kapStep, TableRust.width, ho]
  rfl

theorem slotBits_eq : slotBitsRust keccakDepthRust = 6 := by decide

theorem kapPre_six (A : List E) (k : Nat) :
    kapPre A k 6 = kappasRust tablesRust (lmOf A).toNat (k - 4)
      ((hts A).getD opKeccakRust 0 + slotBitsRust keccakDepthRust) (hts A) := by
  have e : tablesRust.take 6 = tablesRust := List.take_of_length_le (le_of_eq rfl)
  rw [slotBits_eq, kapPre, e]
  rfl

theorem kapLen_succ {i : Nat} (hi : i < 6) : kapLen (i + 1) = kapLen i + tableWidthsRust.getD i 0 := by
  interval_cases i <;> rfl

theorem kapPre_length (A : List E) (k : Nat) : ∀ i, i ≤ 6 → (kapPre A k i).length = kapLen i
  | 0, _ => rfl
  | i + 1, hi => by
    have hl : i < tablesRust.length := lt_of_lt_of_le (Nat.lt_succ_self i) hi
    obtain ⟨t, ht⟩ : ∃ t, tablesRust[i]? = some t := ⟨_, List.getElem?_eq_getElem hl⟩
    rw [kapPre_succ A k ht, List.length_append, List.length_replicate,
      kapPre_length A k i (by omega), kapLen_succ (by omega)]

theorem kapLen_le {i : Nat} (hi : i ≤ 6) : kapLen i ≤ 165 := by interval_cases i <;> decide

theorem width_pos {i : Nat} (hi : i < 6) : 8 ≤ tableWidthsRust.getD i 0 ∧
    tableWidthsRust.getD i 0 ≤ 92 := by
  interval_cases i <;> decide

/-- `TABLE_WIDTHS` in `.rodata`. -/
theorem widthRod {u : MachineState} (ro : RodataOk u) {i : Nat} (hi : i < 6) :
    u.getMem (0xa0000460 + BitVec.ofNat 64 i * 8) = BitVec.ofNat 64 (tableWidthsRust.getD i 0) := by
  interval_cases i <;> exact ro.word

/-- The `Vec<K>` at `sp + 1312` holds `ks`, its buffer allocated from `lo2` on. -/
structure KapVec (s u : MachineState) (lo2 : Nat) (ks : List Nat) : Prop where
  ok : VecOk u (s.getReg .x2 - 1344) 8 8
  fresh : lo2 ≤ (vecPtr u (s.getReg .x2 - 1344)).toNat
  len : (vecLen u (s.getReg .x2 - 1344)).toNat = ks.length
  vals : ∀ j < ks.length, u.getMem (vecPtr u (s.getReg .x2 - 1344) + BitVec.ofNat 64 (8 * j)) =
    BitVec.ofNat 64 (ks.getD j 0)

/-- At `kappas`' loop header, `i` tables done. -/
structure Kap11 (OI : MachineState → Word → List (List Opening) → Prop) (s u : MachineState)
    (A : List E) (k : Nat) (R Q B : Word) (lo lo2 i : Nat) : Prop where
  keep : Keep11 OI s u A k R Q B lo lo2
  kv : KapVec s u lo2 (kapPre A k i)
  lt : i < 6
  x8 : u.getReg .x8 = BitVec.ofNat 64 (80 * i)
  x9 : u.getReg .x9 = 6
  x19 : u.getReg .x19 = 0xa0000460
  x20 : u.getReg .x20 = 480
  x22 : u.getReg .x22 = 6
  x27 : u.getReg .x27 = B

end Rv64Verifier.Proofs.Walk
