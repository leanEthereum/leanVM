/-
  LeanVM.Guest.Complete.MainMidWins

  `mMid`'s first run at the honest oracle: the children's buffers and `written[0]`.
-/

module

public import LeanVM.Guest.Complete.MainMid
import LeanVM.Guest.Memory.Uniform

/-!
# `mMid`'s first run

`mMid_w0` allocates `child_pi`, `child_fresh`, `child_carried` and `written` at `mBase m 5 ..< 9` and
stores `written[0] = g^(nrx + nrs) = g^(kidBase w 0)`. `winsHypT_mid0`: its window keeps the invariant,
the cursor from `mBase m 5` to `mBase m 9`.
-/

namespace LeanVM.Guest.Complete

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Memory LeanVM.Guest.B1
open LeanVM.Guest.B1.Fwd LeanVM.Guest.B1.Main LeanVM.Guest.B1.VsC
open LeanVM.Node LeanVM.Protocol
open LeanVM.Protocol.Verifier

@[expose] public section

set_option maxRecDepth 200000 in
theorem mid0_shape : atomsOf ((mMid.drop 0).take 11) =
    [.hint (.allocDyn (.n 398) (.n 35)), .hint (.allocDyn (.n 399) (.n 44)), .hint (.allocDyn (.n 400) (.n 50)),
      .const (.n 401) (word 2 0), .mul (.n 402) (.n 6) (.n 401), .hint (.allocDyn (.n 403) (.n 402)),
      .mul (.n 404) (.n 2) (.n 5), .load (.n 404) (.n 403) 0, .const (.n 405) (word 1 0),
      .add (.n 406) (.n 405) (.n 6), .const (.n 407) (word 1 0)] := by
  decide +kernel

set_option maxRecDepth 200000 in
theorem mid0_mem : Atom.hint (.allocDyn (.n 403) (.n 402)) ∈ atomsOf mMid ∧
    Atom.mul (.n 404) (.n 2) (.n 5) ∈ atomsOf mMid := by
  decide +kernel

section
variable {al : String → Bool} {k : ℕ} {s : NodeStatement} {w : NodeWitness} {cover : List E} {rd0 : Reader}
  {R : ℕ → Prop} {es : List Ev}

set_option linter.unusedSimpArgs false in
/-- **`mMid`'s first run** keeps the invariant, from `mBase m 5` to `mBase m 9`. -/
theorem winsHypT_mid0 {ws : List W1} {st : St} {K : St → Prop} {Qs : List (Reader → Tree → Prop)}
    (hn : (mainCounts s w).nc ≤ 16)
    (hst : PreInv al s w cover (mBase (mainCounts s w) 5) Qs st)
    (hrest : ∀ st', PreInv al s w cover (mBase (mainCounts s w) 9) Qs st' →
      WinsHypT B2C.fs al B2C.cert k (mVal rd0 (mOrc al s w)) (mOrc al s w)
        (ownData B2C.cert 0 (B2C.fs "main") "main" (mainCounts s w).bufs es) R (mainPreR s) ws st' K) :
    WinsHypT B2C.fs al B2C.cert k (mVal rd0 (mOrc al s w)) (mOrc al s w)
      (ownData B2C.cert 0 (B2C.fs "main") "main" (mainCounts s w).bufs es) R (mainPreR s) (mMid_w0 :: ws) st K := by
  obtain ⟨-, -, c2, -, -, c5, -, -⟩ := mOrc_counts (al := al) (s := s) (w := w) (rd := rd0)
  obtain ⟨-, -, -, -, -, -, v35, v44, v50, v402⟩ := mOrc_sizes (al := al) (s := s) (w := w) (rd := rd0)
  have L : ∀ e, e < 2 ^ 19 * 64 → logG (gen ^ e) = e := fun e he => logG_gen_pow (by omega)
  have l1 := L (2 * (mainCounts s w).nc) (by omega)
  have l2 := L (55 * (mainCounts s w).nc) (by omega)
  have l3 := L (26 * (mainCounts s w).nc) (by omega)
  have l4 := L ((mainCounts s w).nc + 1) (by omega)
  have o398 : mOrc al s w 398 = mPtr (mainCounts s w) 5 0 := rfl
  have o399 : mOrc al s w 399 = mPtr (mainCounts s w) 6 0 := rfl
  have o400 : mOrc al s w 400 = mPtr (mainCounts s w) 7 0 := rfl
  have o403 : mOrc al s w 403 = mPtr (mainCounts s w) 8 0 := rfl
  have e6 : mBase (mainCounts s w) 6 = mBase (mainCounts s w) 5 + 2 * (mainCounts s w).nc := by
    simp [mBase, MainCounts.bufs, bases]
  have e7 : mBase (mainCounts s w) 7 = mBase (mainCounts s w) 6 + 55 * (mainCounts s w).nc := by
    simp [mBase, MainCounts.bufs, bases]
  have e8 : mBase (mainCounts s w) 8 = mBase (mainCounts s w) 7 + 26 * (mainCounts s w).nc := by
    simp [mBase, MainCounts.bufs, bases]
  have e9 : mBase (mainCounts s w) 9 = mBase (mainCounts s w) 8 + ((mainCounts s w).nc + 1) := by
    simp [mBase, MainCounts.bufs, bases]
  have htop : mTop (mainCounts s w) = mBase (mainCounts s w) 9 + 26 := by
    simp [mBase, mTop, MainCounts.bufs, bases]; omega
  have h4 := mBase_four_ge (mainCounts s w)
  have h5 := mBase_five (mainCounts s w)
  obtain ⟨m403, m404⟩ := mid0_mem
  have s403 : mVal rd0 (mOrc al s w) (.n 403) = ptrAt (mBase (mainCounts s w) 8) := by
    rw [show mVal rd0 (mOrc al s w) (.n 403) = mOrc al s w 403 from mMid_good m403, o403]; simp [mPtr]
  have s404 := pmul (good_mul (mMid_good (rd := rd0) (w := mOrc al s w) m404) (by norm_num) (by norm_num)) c2 c5
  unfold mMid_w0
  refine winsHypT_runI (a' := mBase (mainCounts s w) 9) hst ?_ ⟨?_, ?_, ?_, ?_, ?_⟩ hrest
  · rw [mid0_shape]
    simp only [allocs, List.map_cons, List.map_nil, List.filterMap_cons, List.filterMap_nil, Ev.alloc?, v35, v44,
      v50, v402, l1, l2, l3, l4, List.sum_cons, List.sum_nil]
    omega
  · rw [mid0_shape]
    simp only [allocDsts, allocs, List.map_cons, List.map_nil, List.filterMap_cons, List.filterMap_nil,
      Ev.allocDst?, Ev.alloc?, v35, v44, v50, v402, l1, l2, l3, l4, bases, V.idx, o398, o399, o400, o403, mPtr,
      Nat.add_zero, e6, e7, e8, Nat.add_assoc]
  · rw [mid0_shape]
    intro A hA
    simp only [loadAddrs, List.map_cons, List.map_nil, List.filterMap_cons, List.filterMap_nil, Ev.loadAddr?,
      List.mem_cons, List.not_mem_nil, or_false, s403] at hA
    rw [Main.addr_ofK] at hA
    exact ⟨_, hA, Or.inl (own_main (by omega) (by omega))⟩
  · rw [mid0_shape, heapHintAddrs_noHeap (by decide)]
    intro A hA; simp at hA
  · rw [mid0_shape]
    intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      first | exact pureT_triv rfl | trivial
  · rw [mid0_shape]
    intro rd _ _ hOr x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      try exact memT_triv rfl
    show LoadHolds rd _ 0 _
    rw [s403, s404]
    have hw := ((hst.hO rd hOr).1) (mBase (mainCounts s w) 8,
      (List.range ((mainCounts s w).nc + 1)).map fun c => gen ^ kidBase w c)
      (by simp only [mainWords]
          exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
            (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
              List.mem_cons_self))))))))
    have h0 := hw 0 (by simp)
    simpa [kidBase, mainCounts] using h0

end

end
end LeanVM.Guest.Complete
