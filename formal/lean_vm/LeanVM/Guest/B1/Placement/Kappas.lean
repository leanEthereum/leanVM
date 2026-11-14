/-
  LeanVM.Guest.B1.Placement.Kappas

  The committed columns, their sizes over the guest's sources, and every committed column's log
  size below `33` once the stack is at most `2^32` (`HypKappa`).
-/

module

public import LeanVM.Guest.B1.Placement.InterfaceP
public import LeanVM.Guest.B1.Tables.Basic

/-!
# The committed columns' sizes

`committedCols 158` is every global column but `KECCAK`'s fifty value lanes and its columns with
a `q_keccak` slot (`committedCols_158`): the framework's five, then each table's columns, `KECCAK`'s
free column (global `80`) and its twenty-seven read counts (global `131 .. 157`). Over the base `[0, log_mem, τ_0, …, τ_5]`, the guest's sources
`colKappaSrc`, `colKappaAdj` give exactly `committedKappas (columnKappas log_mem 19 τ)`
(`committedKappas_columnKappas`).

`hypKappa`: every committed column's `κ` is at most `log2Ceil (stackTotal kappas)`, since `2^κ` is
one of its summands; so `≤ 30` once the stack is at most `2^30`.
-/

namespace LeanVM.Guest.B1.Tables

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

/-- The committed columns: all but `KECCAK`'s value lanes and the columns with a `q_keccak` slot,
global columns `66 .. 79` and `81 .. 130`. -/
theorem committedCols_158 :
    committedCols 158 = List.range 66 ++ [80] ++ (List.range 27).map (· + 131) := by
  decide +kernel

theorem committedCols_158_length : (committedCols 158).length = nCommittedCols := by
  rw [committedCols_158]; simp

theorem columnKappas_length (lm lb : ℕ) (hs : List ℕ) : (columnKappas lm lb hs).length = 158 := by
  simp only [columnKappas, List.length_append, List.length_cons, List.length_nil,
    List.length_flatMap, List.length_replicate]
  decide +kernel

theorem tables_shape :
    tables.map (fun t ↦ (t.width, t.opcode)) =
      [(13, 0), (13, 1), (7, 2), (14, 3), (14, 4), (92, 5)] := by
  decide +kernel

theorem qkeccakSlotBits_eq : qkeccakSlotBits = 6 := by decide +kernel

theorem columnKappas_eq (lm lb h0 h1 h2 h3 h4 h5 : ℕ) :
    columnKappas lm lb [h0, h1, h2, h3, h4, h5] = [lm, lm, lm, lb, h5 + 6] ++
      List.replicate 13 h0 ++ List.replicate 13 h1 ++ List.replicate 7 h2 ++
      List.replicate 14 h3 ++ List.replicate 14 h4 ++ List.replicate 92 h5 := by
  have e : ∀ hs : List ℕ, tables.flatMap (fun t ↦ List.replicate t.width (hs.getD t.opcode 0)) =
      (tables.map fun t ↦ (t.width, t.opcode)).flatMap
        (fun p ↦ List.replicate p.1 (hs.getD p.2 0)) := fun hs => by
    rw [List.flatMap_map]
  unfold columnKappas
  rw [e, tables_shape, qkeccakSlotBits_eq]
  simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, List.cons_append,
    List.nil_append, List.append_assoc]
  rfl

/-- **The guest's sizes are the specification's**: column `c`'s source and adjustment over the
base `[0, log_mem, τ_0, …, τ_5]` give `committedKappas (columnKappas log_mem 19 τ)`. -/
theorem committedKappas_columnKappas (lm : ℕ) (hs : List ℕ) (hl : hs.length = 6) :
    committedKappas (columnKappas lm guestLogBytecode hs) =
      (List.range nCommittedCols).map fun c ↦ (0 :: lm :: hs).getD (colKappaSrc c) 0 +
        colKappaAdj c := by
  obtain ⟨h0, h1, h2, h3, h4, h5, rfl⟩ : ∃ h0 h1 h2 h3 h4 h5, hs = [h0, h1, h2, h3, h4, h5] := by
    match hs, hl with
    | [h0, h1, h2, h3, h4, h5], _ => exact ⟨h0, h1, h2, h3, h4, h5, rfl⟩
  rw [committedKappas, columnKappas_length, committedCols_158, columnKappas_eq]
  rfl

theorem committedKappas_length (kappas : List ℕ) (h : kappas.length = 158) :
    (committedKappas kappas).length = nCommittedCols := by
  rw [committedKappas, List.length_map, h, committedCols_158_length]

theorem tb_le_log2Ceil_of_two_pow_le {k N : ℕ} (h : 2 ^ k ≤ N) : k ≤ log2Ceil N := by
  by_contra hlt
  have h1 := log2Ceil_le_iff.mp (show log2Ceil N ≤ k - 1 by omega)
  have : 2 ^ (k - 1) < 2 ^ k := Nat.pow_lt_pow_right (by decide) (by omega)
  omega

theorem tb_single_le_sum_map (l : List ℕ) (c : ℕ) (hc : c < l.length) :
    2 ^ l.getD c 0 ≤ (l.map (2 ^ ·)).sum := by
  rw [List.getD_eq_getElem _ _ hc]
  exact List.le_sum_of_mem (List.mem_map.mpr ⟨_, List.getElem_mem hc, rfl⟩)

/-- **Every committed column's `κ` is below 33** once the stack is at most `2^32`. -/
theorem hypKappa_holds : HypKappa := by
  intro kappas hl h30 c hc
  have hcl : c < (committedKappas kappas).length := by
    rw [committedKappas_length _ hl]; exact hc
  have := tb_le_log2Ceil_of_two_pow_le (tb_single_le_sum_map _ c hcl)
  rw [← stackTotal] at this
  omega

end
end LeanVM.Guest.B1.Tables
