/-
  LeanVM.Guest.B1.Main.MainHeapHonest

  `main`'s honest tree pops the honest pushes on `heap_sizes`, given each child's `verify_sub` tree
  pops its child's advised sizes.
-/

module

public import LeanVM.Guest.B1.Main.MainHeap
public import LeanVM.Guest.B1.Main.HeapPushes

/-!
# `main`'s advised sizes are the honest ones

`main_heap_honest`: a valid node of `main` at its honest valuation, its buffers `mSizes` of the honest
data, whose callees' trees satisfy `mainPredsH`'s predicates (within any bounds), pops the entries of
`Hints.honestPushes` on `heap_sizes`, given that every tree of `Pvs c` pops `vsHeapH … c`. The sizes
agree as words below `2^128` (`count_eq`).
-/

namespace LeanVM.Guest.B1.Main

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Memory
open LeanVM.Protocol LeanVM.Protocol.Verifier LeanVM.Node
open LeanVM.Guest (GuestLimits)

@[expose] public section

theorem count_eq {n : ℕ} (h : n < 2 ^ 128) : Hints.count n = ofK (addressOfIndex n) := by
  rw [Hints.count, gpowE, gpowK_eq h]

theorem advEntry_count {bufs : List ℕ} {k n : ℕ} (h : bufs[k]? = some n) (hn : n < 2 ^ 128) :
    advEntry bufs k = [Hints.count n] := by
  rw [advEntry, h, Option.map_some, Option.toList_some, count_eq hn]

variable {fs : String → ℕ} {fp : ℕ} {seed : Digest} {s : NodeStatement} {w : NodeWitness} {bytecode : List K}

/-- **`main`'s honest tree pops the honest pushes on `heap_sizes`**, given each child's `verify_sub` trees pop its
advised sizes. -/
theorem main_heap_honest (hl : GuestLimits s w) {Pvs : ℕ → Tree → Prop} {b : MainBs}
    (hvh : ∀ c t, Pvs c t → t.heapPops heapSlots = vsHeapH bytecode w c) {rd : Reader} {σ : Val}
    {ks : List Tree} (hval : (Memory.Tree.node "main" σ (mSizes (hData seed s w)) ks).Valid coreProgram rd [] [])
    (hv : MVals rd σ (hm fs fp seed s w))
    (hT : KidsT (mCalls σ (hm fs fp seed s w))
      ((fun _ => True) :: mTs (hm fs fp seed s w) ((mainPredsH s w (hDvNH w) Pvs).withTotal fs b)) ks)
    (hc : calls (mEvs σ) = mCalls σ (hm fs fp seed s w)) :
    (Memory.Tree.node "main" σ (mSizes (hData seed s w)) ks).heapPops heapSlots =
      ((Hints.honestPushes bytecode seed s w).filter (·.1 == Hints.heapSizeStream)).map (·.2) := by
  have hb := hData_bounds (seed := seed) hl fs fp
  have h16 := hb.nc
  have hlx := hb.lx
  have hxd := hb.xd
  have hls := hb.ls
  have hsd := hb.sd
  rw [main_tree_heap hb hval hv _ hT hc (Hx := [(Hints.listChainCells s.claims.xmss.length).map Hints.count |>.toList])
    (Hs := [(Hints.listChainCells s.claims.sphincs.length).map Hints.count |>.toList])
    (Hd := ((w.daMatrix.map fun c ↦ Hints.daHeapSizes c.2.rows.length).getD []).map fun n => [Hints.count n])
    (H5 := (List.range' 0 w.children.length).flatMap (vsHeapH bytecode w)), heapPushes_eq]
  · have hown : (heapSlots "main").map (advEntry (mSizes (hData seed s w))) =
        [4 * (s.claims.xmss.length + (xPlan s w).duplicates.length),
          4 * (s.claims.sphincs.length + (sPlan s w).duplicates.length), 2 * (w.children.length + 1),
          2 * w.children.length, 24 * w.children.length, 24 * w.children.length, w.children.length + 1].map
          fun k => [Hints.count k] := by
      have hX : (hData seed s w).X < 2 ^ 24 := by
        show (hData seed s w).nlx + (hData seed s w).nxd < _
        have : (hData seed s w).nlx < 2 ^ 23 := hlx
        have : (hData seed s w).nxd < 2 ^ 23 := hxd
        omega
      have hY : (hData seed s w).Y < 2 ^ 24 := by
        show (hData seed s w).nls + (hData seed s w).nsd < _
        have : (hData seed s w).nls < 2 ^ 23 := hls
        have : (hData seed s w).nsd < 2 ^ 23 := hsd
        omega
      have hn : (hData seed s w).nc ≤ 16 := h16
      show [0, 1, 4, 5, 6, 7, 8].map _ = _
      simp only [List.map_cons, List.map_nil]
      rw [advEntry_count rfl (by omega), advEntry_count rfl (by omega), advEntry_count rfl (by omega),
        advEntry_count rfl (by omega), advEntry_count rfl (by omega), advEntry_count rfl (by omega),
        advEntry_count rfl (by omega)]
      rfl
    have hnd : (hm fs fp seed s w).nd = (w.daMatrix.map fun _ => 1).getD 0 := rfl
    have hnc : (hm fs fp seed s w).nc = w.children.length := rfl
    rw [hown, hnd, hnc]
    unfold Hints.nodeHeapSizes
    by_cases h0 : w.children.length = 0
    · rcases hdm : w.daMatrix with _ | p <;> simp [h0]
    · rcases hdm : w.daMatrix with _ | p <;> simp [h0]
  · intro t a r htv ht
    rw [clHonest_heap (σ := σ) htv ht.1, B1.Digest.clBufs, Hints.listChainCells]
    by_cases h0 : s.claims.xmss.length = 0
    · simp [h0, advEntry]
    · have : s.claims.xmss.length < 2 ^ 23 := hlx
      simp only [h0, ↓reduceIte, Option.map_some, Option.toList_some]
      rw [advEntry_count rfl (by omega), Nat.mul_comm]
      rfl
  · intro t a r htv ht
    rw [clHonest_heap (σ := σ) htv ht.1, B1.Digest.clBufs, Hints.listChainCells]
    by_cases h0 : s.claims.sphincs.length = 0
    · simp [h0, advEntry]
    · have : s.claims.sphincs.length < 2 ^ 23 := hls
      simp only [h0, ↓reduceIte, Option.map_some, Option.toList_some]
      rw [advEntry_count rfl (by omega), Nat.mul_comm]
      rfl
  · intro hnd t a r htv ht
    rcases hdm : w.daMatrix with _ | p
    · simp [MainData.toIn, hData, hdm] at hnd
    · have hT := ht.1
      simp only [hDvNH, hdm, Option.map_some, Option.getD_some] at hT
      have hr : p.2.rows.length ≤ 32 := hl.atMost32Rows p (by simp [hdm])
      have hL : Da.wLog p.2 ≤ 5 := by
        rw [Da.wLog, LeanDa.logPaddedRowCount]
        exact (Nat.clog_mono_right 2 hr).trans (by decide)
      rw [dvNH_heap htv hT, advEntry_count rfl (by
          have := Nat.pow_le_pow_right (show 0 < 2 by decide) hL
          omega)]
      simp [Hints.daHeapSizes, Da.wLog, Nat.mul_comm]
  · intro t rest r hrest htv ht
    exact l5From_heap hvh (by omega) hrest w.children.length 0 t r (by simp [MainData.toIn, hData]) htv ht.1
end

end LeanVM.Guest.B1.Main
