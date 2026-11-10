/-
  LeanVM.Guest.B1.Whir.CAtoms

  Small blocks of the template at fixed values: a heap buffer, a permutation, a materialized
  pointer, a store.
-/

module

public import LeanVM.Guest.B1.Whir.CBlk
public import LeanVM.Guest.B1.Whir.RoundComplete
public import LeanVM.Guest.B1.Fs.Templates

/-!
# Small blocks at fixed values

* `heap_blk`: `HeapBuf(g^e)` at `k`: its size `g^e`, its pointer any given word.
* `keccak_blk`: a `KECCAK` reading the cells of a sponge: its outputs the sponge's permutation's
  cells (`rdCell`).
* `osMatS_blkA`: a fixed buffer's pointer materialized as the plan says.
* `stores_blk`: loads of values already fixed (stores into memory), holding where memory does.
-/

namespace LeanVM.Guest.B1.Whir

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest LeanVM.Guest.B1
open LeanVM.Guest.Value LeanVM.Protocol LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

variable {H : CallRel → Reader → Prop}

/-- **A heap buffer** `HeapBuf(g^e)` at `k`, its pointer `p`. -/
theorem heap_blk (σ : Val) (e k : ℕ) (p : E) :
    BlkA H σ k (k + 2) (osHeap e k) (fun σ' ↦ σ' (.n k) = gw e ∧ σ' (.n (k + 1)) = p) := by
  refine ⟨lstF k [gw e, p], fun C rd _ σ' _ hr ↦ ?_⟩
  have e0 := lstF_at hr (by simp) 0 (by simp)
  have e1 := lstF_at hr (by simp) 1 (by simp)
  simp only [List.getD_cons_zero, List.getD_cons_succ, Nat.add_zero] at e0 e1
  refine ⟨?_, e0, e1⟩
  simp only [osHeap, allOk_cons, allOk_nil, and_true, stmtOk_atom, holds_const, osCst]
  exact ⟨e0, trivial⟩

/-- **A permutation of a sponge's cells**: the inputs the sponge's waiting scalars' cells, zeros
and its capacity; the outputs its permutation's cells. -/
theorem keccak_blk {σ : Val} {ins : List ℕ} {out : ℕ} (s : Fs) (hs : s.pend.length ≤ 4)
    (hl : ins.length = 13) (hin : ∀ i ∈ ins, i < out)
    (hins : ∀ C rd, H C rd → ins.map (fun i ↦ σ (.n i)) =
      pendCells s.pend ++ List.replicate (8 - 2 * s.pend.length) 0 ++ s.cap) :
    BlkA H σ out (out + 13) [osKeccak ins out]
      (fun σ' ↦ ∀ j < 13, σ' (.n (out + j)) = rdCell s.perm j) := by
  refine ⟨fun i ↦ rdCell s.perm (i - out), fun C rd hH σ' ha hr ↦ ?_⟩
  have hv : ∀ j < 13, σ' (.n (out + j)) = rdCell s.perm j := fun j hj ↦ by
    rw [hr _ (by omega) (by omega)]; simp only [Nat.add_sub_cancel_left]
  refine ⟨?_, hv⟩
  simp only [osKeccak, allOk_cons, allOk_nil, and_true, stmtOk_atom]
  refine keccakA_of (by simp [hl]) (by simp [osRun]) ?_
  have e1 : (ins.map V.n).map σ' = ins.map (fun i ↦ σ (.n i)) := by
    simp only [List.map_map]
    exact List.map_congr_left fun i hi ↦ ha i (hin i hi)
  rw [e1, hins C rd hH, ← perm_eq_cells s hs]
  funext c
  simp only [cells13, osRun, List.map_map]
  rw [List.getD_eq_getElem _ _ (by simp), List.getElem_map, List.getElem_range]
  simp only [Function.comp]
  rw [hv c.val c.isLt, rdCell_eq]

/-- A fixed buffer's pointer, as a block at fixed values. -/
theorem osMatS_blkA {P : List (ℕ × ℕ × ℕ)} {base off : ℕ} {s : OsSt} (σ : Val)
    (hbase : base < s.k) (hmb : MatsBelow s.k s.mats) (hm : ∀ C rd, H C rd → MatsOk σ s.mats)
    (hoff : off < u128Bound) :
    BlkA H σ s.k (osMatS P base off s).2.2.k (osMatS P base off s).1
      (fun σ' ↦ σ' (.n (osMatS P base off s).2.1) = σ (.n base) * gen ^ off ∧
        MatsOk σ' (osMatS P base off s).2.2.mats ∧
        MatsBelow (osMatS P base off s).2.2.k (osMatS P base off s).2.2.mats) :=
  BlkA.ofF _ fun C rd hH ↦ osMatS_blk σ hbase hmb (hm C rd hH) hoff

/-- The materializations after a fixed buffer's pointer lie below the next free value. -/
theorem osMatS_below {P : List (ℕ × ℕ × ℕ)} {base off : ℕ} {s : OsSt} (hmb : MatsBelow s.k s.mats)
    (hbase : base < s.k) : MatsBelow (osMatS P base off s).2.2.k (osMatS P base off s).2.2.mats := by
  by_cases h0 : off = 0
  · simp only [osMatS, osMatsAfter, osMatP, h0, ↓reduceIte]; exact hmb
  · have hk : (osMatS P base off s).2.2.k = s.k + 2 := by
      simp only [osMatS, (osMatP_shape P s.mats base off s.k).2 h0]
    rw [hk]
    exact matsBelow_after hmb hbase (by omega) (by omega)

/-- **Stores**: loads of fixed values, holding where memory holds them. -/
theorem stores_blk {σ : Val} {k : ℕ} {ss : List Stmt}
    (h : ∀ C rd, H C rd → ∀ σ', AgreeBelow k σ σ' → AllOk C rd σ' ss) :
    BlkA H σ k k ss (fun _ ↦ True) :=
  ⟨fun _ ↦ 0, fun C rd hH σ' ha _ ↦ ⟨h C rd hH σ' ha, trivial⟩⟩

end
end LeanVM.Guest.B1.Whir
