/-
  LeanVM.Guest.B1.Digest.ChildWindow

  B1 for `child_claims_window` (G:2802-2824; TRIAGE #63): one window of a child's claim list,
  read from this node's table and marked.
-/

module

public import LeanVM.Guest.B1.Digest.ChildTail
public import LeanVM.Guest.B1.Digest.ScaledLog

namespace LeanVM.Guest.B1.Digest

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.Blake2sHash
open LeanVM.Protocol.Verifier LeanVM.Guest.Core LeanVM.Guest.Value

@[expose] public section

/-- **`child_claims_window`**: `x_q·g = g^N`, `N < 2^16`, `nxt = E(2^11·N)`, and 32 blocks read
and marked as `ChildReads`, chained from the state under `windowMd base nxt`. -/
def Meaning_child_claims_window (rd : Reader) (args rets : List E) : Prop :=
  ∃ s0 s1 base entries cover marks origin limit xq gsq o0 o1 nxt,
    args = [s0, s1, base, entries, cover, marks, origin, limit, xq, gsq] ∧ rets = [o0, o1, nxt] ∧
    ∃ N < 2 ^ 16, xq * gen = gen ^ N ∧ nxt = eOfNat (2 ^ 11 * N) ∧
    ∃ (off : ℕ → ℕ) (cs : List E), cs.length = 128 ∧
      ChildReads rd entries cover marks origin limit off cs 32 ∧
      ChainCells (s0, s1) (blocksOf cs) (windowMd base nxt) 32 (o0, o1)

/-- The last block, under `nxt`. -/
def ccwLast : List Atom :=
  cBlkHead 664 31 ++
  [.blake2s (.n 677) (.n 678) (.n 679) (.n 680) (.n 662) (.n 663) (.n 681) (.n 682) (.n 12)]

/-- `child_claims_window`'s body. -/
def ccwBody : List Stmt :=
  ([.const (.n 10) (word 2 0 0), .mul (.n 11) (.n 8) (.n 10)] : List Atom).map .atom ++
  [.call "scaled_log__L11" [.n 11, .n 9] [.n 12]] ++
  (([.copy (.n 13) (.n 0), .copy (.n 14) (.n 1)] : List Atom) ++ cBlk0 13 ++
    (List.range 30).flatMap (fun i => cBlk 13 (i + 1)) ++ ccwLast ++
    ([.copy (.n 683) (.n 681), .copy (.n 684) (.n 682), .copy (.n 685) (.n 12)] : List Atom)).map .atom ++
  [.ret [.n 683, .n 684, .n 685]]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
theorem find_child_claims_window : coreProgram.find? "child_claims_window" =
    some ⟨"child_claims_window", [.n 0, .n 1, .n 2, .n 3, .n 4, .n 5, .n 6, .n 7, .n 8, .n 9],
      ccwBody⟩ :=
  Program.find?_of_indexOf? (j := 21) (by decide +kernel) rfl

/-! ## Forward -/

theorem child_window_fwd {rd : Reader} (hm : MemOk rd) {gsq : E} (hT : SquaresAt rd gsq)
    {s0 s1 base entries cover marks origin limit xq : E} {rets : List E}
    (h : coreProgram.Rel rd "child_claims_window"
      [s0, s1, base, entries, cover, marks, origin, limit, xq, gsq] rets) :
    Meaning_child_claims_window rd [s0, s1, base, entries, cover, marks, origin, limit, xq, gsq]
      rets := by
  rw [rel_of_find find_child_claims_window] at h
  simp only [Fn.Sem, ccwBody, ccwLast, holdsList_atoms, List.cons_append, List.nil_append,
    Stmt.HoldsList, Stmt.Holds, Atom.Holds, List.forall_mem_append, forall_mem_flatMap_range,
    List.forall_mem_cons, forall_mem_nil_iff, and_true, List.map_cons, List.map_nil] at h
  obtain ⟨σ, hp, c10, m11, hcall, c13, c14, ⟨⟨⟨hb0, hblk⟩, hlh, hlc⟩, c683, c684, c685⟩, hr⟩ := h
  simp only [List.cons.injEq, and_true] at hp
  obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ := hp
  obtain ⟨v, hv, N, hN, hN11, hN12⟩ := (scaled_log_11_iff hT _ _).mp hcall
  simp only [List.cons.injEq, and_true] at hv
  have hB : ∀ j, ∃ e, j < 32 → ((∃ L ≤ 2 ^ 33, σ (.n 7) = gen ^ L ∧ e < L) ∧
      LoadHolds rd (σ (.n 4) * (σ (.n 6) * gen ^ e)) 0 (σ (.n 5) * gen ^ j) ∧
      CellsAt rd (σ (.n 3) * gen ^ (4 * e))
        [σ (.n (26 + 21 * j)), σ (.n (26 + 21 * j + 1)), σ (.n (26 + 21 * j + 2)),
          σ (.n (26 + 21 * j + 3))]) := by
    intro j
    by_cases hj : j < 32
    swap
    · exact ⟨0, fun h => absurd h hj⟩
    refine (?_ : ∃ e, _).imp fun e h _ => h
    rcases (show j = 0 ∨ (1 ≤ j ∧ j < 31) ∨ j = 31 by omega) with rfl | ⟨h1, h2⟩ | rfl
    · obtain ⟨e, hL, hs, hc, -⟩ := cBlk0_fwd hm hb0
      exact ⟨e, hL, hs, hc⟩
    · obtain ⟨e, hL, hs, hc, -⟩ := cBlk_fwd (o := 13) (j := j) hm (by omega)
        (by have := hblk (j - 1) (by omega); rwa [show j - 1 + 1 = j by omega] at this)
      rw [show 13 + 21 * j + 13 = 26 + 21 * j by ring, show 13 + 21 * j + 14 = 26 + 21 * j + 1 by ring,
        show 13 + 21 * j + 15 = 26 + 21 * j + 2 by ring,
        show 13 + 21 * j + 16 = 26 + 21 * j + 3 by ring] at hc
      exact ⟨e, hL, hs, hc⟩
    · exact cBlkHead_fwd hm (by omega) hlh
  choose off hoff using hB
  have hmd : ∀ j < 31, σ (.n (31 + 21 * j)) = baseMd (σ (.n 2)) j := by
    intro j hj
    rcases Nat.eq_zero_or_pos j with rfl | h1
    · exact (cBlk0_fwd hm hb0).choose_spec.2.2.2.1
    · have := (cBlk_fwd (o := 13) (j := j) hm (by omega)
        (by have := hblk (j - 1) (by omega); rwa [show j - 1 + 1 = j by omega] at this)).choose_spec.2.2.2.1
      rwa [show 13 + 21 * j + 18 = 31 + 21 * j by ring] at this
  have hch := chainCells_of_steps (n := 32)
    (blocks := fun j => ![σ (.n (26 + 21 * j)), σ (.n (26 + 21 * j + 1)), σ (.n (26 + 21 * j + 2)),
      σ (.n (26 + 21 * j + 3))]) (md := fun j => if j < 31 then σ (.n (31 + 21 * j)) else σ (.n 12))
    (st := fun j => if j = 0 then (σ (.n 13), σ (.n 14)) else if j = 32 then (σ (.n 681), σ (.n 682))
      else (σ (.n (11 + 21 * j)), σ (.n (12 + 21 * j))))
    (fun j hj => by
      rcases (show j = 0 ∨ (1 ≤ j ∧ j < 31) ∨ j = 31 by omega) with rfl | ⟨h1, h2⟩ | rfl
      · exact (cBlk0_fwd hm hb0).choose_spec.2.2.2.2
      · have := (cBlk_fwd (o := 13) (j := j) hm (by omega)
          (by have := hblk (j - 1) (by omega); rwa [show j - 1 + 1 = j by omega] at this)).choose_spec.2.2.2.2
        simp only [show j ≠ 0 by omega, show j ≠ 32 by omega, show j + 1 ≠ 0 by omega,
          show j + 1 ≠ 32 by omega, h2, ↓reduceIte]
        rw [show 13 + 21 * j + 13 = 26 + 21 * j by ring, show 13 + 21 * j + 14 = 26 + 21 * j + 1 by ring,
          show 13 + 21 * j + 15 = 26 + 21 * j + 2 by ring, show 13 + 21 * j + 16 = 26 + 21 * j + 3 by ring,
          show 13 + 21 * j - 2 = 11 + 21 * j by omega, show 13 + 21 * j - 1 = 12 + 21 * j by omega,
          show 13 + 21 * j + 19 = 11 + 21 * (j + 1) by ring,
          show 13 + 21 * j + 20 = 12 + 21 * (j + 1) by ring,
          show 13 + 21 * j + 18 = 31 + 21 * j by ring] at this
        exact this
      · simpa using hlc)
  simp only [↓reduceIte] at hch
  set cs := (List.range (4 * 32)).map (fun i => σ (.n (26 + 21 * (i / 4) + i % 4))) with hcs
  have hcsg : ∀ j r, j < 32 → r < 4 → cs.getD (4 * j + r) 0 = σ (.n (26 + 21 * j + r)) := by
    intro j r hj hr
    rw [hcs, List.getD_eq_getElem _ _ (by simp; omega)]
    simp only [List.getElem_map, List.getElem_range]
    congr 2
    omega
  refine ⟨_, _, _, _, _, _, _, _, _, _, σ (.n 683), σ (.n 684), σ (.n 685), rfl, hr.symm, N, hN,
    by rw [← hN11, m11, c10, word_gen], by rw [c685, hv, hN12], off, cs,
    by rw [hcs, List.length_map, List.length_range], ?_, ?_⟩
  · intro j hj
    obtain ⟨hL, hs, hc⟩ := hoff j hj
    refine ⟨hL, hs, ?_⟩
    have e0 := hcsg j 0 hj (by omega)
    rw [Nat.add_zero, Nat.add_zero] at e0
    rw [e0, hcsg j 1 hj (by omega), hcsg j 2 hj (by omega), hcsg j 3 hj (by omega)]
    exact hc
  · rw [chainCells_congr (b' := fun j => ![σ (.n (26 + 21 * j)), σ (.n (26 + 21 * j + 1)),
        σ (.n (26 + 21 * j + 2)), σ (.n (26 + 21 * j + 3))])
        (md' := fun j => if j < 31 then σ (.n (31 + 21 * j)) else σ (.n 12))
        (fun j hj => ?_) (fun j hj => ?_), ← c13, ← c14, c683, c684]
    · exact hch
    · have e0 := hcsg j 0 hj (by omega)
      rw [Nat.add_zero, Nat.add_zero] at e0
      simp only [blocksOf, e0, hcsg j 1 hj (by omega), hcsg j 2 hj (by omega),
        hcsg j 3 hj (by omega)]
    · unfold windowMd
      split_ifs with h1
      · exact (hmd j h1).symm
      · rw [c685]

/-! ## Backward -/

section
variable (P : Val) (off : ℕ → ℕ) (L : ℕ) (T1 T2 : ℕ → E) (cs : List E) (S : ℕ → E × E)
  (xq nxt : E)

/-- The honest values of `child_claims_window`. -/
def ccwVals (i : ℕ) : E :=
  if i < 10 then P (.n i) else if i = 10 then word 2 0 0 else if i = 11 then xq * word 2 0 0 else
  if i = 12 then nxt else
  if (i - 13) / 21 = 0 then
    (if (i - 13) % 21 = 0 then (S 0).1 else if (i - 13) % 21 = 1 then (S 0).2 else
      (cBlk0Vals P (off 0) L (T1 0) (T2 0) (cs.getD 0 0) (cs.getD 1 0) (cs.getD 2 0) (cs.getD 3 0)
        (S 1)).getD ((i - 13) % 21 - 2) 0) else
  if (i - 13) / 21 < 31 then (cBlkVals P off L T1 T2 cs S ((i - 13) / 21)).getD ((i - 13) % 21) 0 else
  if (i - 13) / 21 = 31 then
    (if (i - 13) % 21 < 17 then
      (cHeadVals P (off 31) L (T1 31) (T2 31) 31 (cs.getD 124 0) (cs.getD 125 0) (cs.getD 126 0)
        (cs.getD 127 0)).getD ((i - 13) % 21) 0 else
     if (i - 13) % 21 = 17 ∨ (i - 13) % 21 = 19 then (S 32).1 else (S 32).2) else nxt

theorem ccwVals_blk0 (r : ℕ) (hr : r < 19) :
    ccwVals P off L T1 T2 cs S xq nxt (13 + 2 + r) =
      (cBlk0Vals P (off 0) L (T1 0) (T2 0) (cs.getD 0 0) (cs.getD 1 0) (cs.getD 2 0) (cs.getD 3 0)
        (S 1)).getD r 0 := by
  simp only [ccwVals, show ¬(13 + 2 + r < 10) by omega, show (13 + 2 + r - 13) / 21 = 0 by omega,
    show (13 + 2 + r - 13) % 21 = r + 2 by omega, show r + 2 ≠ 0 by omega, show r + 2 ≠ 1 by omega,
    show 13 + 2 + r ≠ 10 by omega, show 13 + 2 + r ≠ 11 by omega, show 13 + 2 + r ≠ 12 by omega,
    ↓reduceIte, Nat.add_sub_cancel]

theorem ccwVals_blk (j r : ℕ) (hj1 : 1 ≤ j) (hj : j < 31) (hr : r < 21) :
    ccwVals P off L T1 T2 cs S xq nxt (13 + 21 * j + r) = (cBlkVals P off L T1 T2 cs S j).getD r 0 := by
  simp only [ccwVals, show ¬(13 + 21 * j + r < 10) by omega, show (13 + 21 * j + r - 13) / 21 = j by omega,
    show (13 + 21 * j + r - 13) % 21 = r by omega, show j ≠ 0 by omega, hj,
    show 13 + 21 * j + r ≠ 10 by omega, show 13 + 21 * j + r ≠ 11 by omega,
    show 13 + 21 * j + r ≠ 12 by omega, ↓reduceIte]

theorem ccwVals_last (r : ℕ) (hr : r < 17) :
    ccwVals P off L T1 T2 cs S xq nxt (664 + r) =
      (cHeadVals P (off 31) L (T1 31) (T2 31) 31 (cs.getD 124 0) (cs.getD 125 0) (cs.getD 126 0)
        (cs.getD 127 0)).getD r 0 := by
  simp only [ccwVals, show ¬(664 + r < 10) by omega, show (664 + r - 13) / 21 = 31 by omega,
    show (664 + r - 13) % 21 = r by omega, show 664 + r ≠ 10 by omega, show 664 + r ≠ 11 by omega,
    show 664 + r ≠ 12 by omega, hr, ↓reduceIte]
  simp

theorem ccwVals_end : ccwVals P off L T1 T2 cs S xq nxt 681 = (S 32).1 ∧
    ccwVals P off L T1 T2 cs S xq nxt 682 = (S 32).2 ∧
    ccwVals P off L T1 T2 cs S xq nxt 683 = (S 32).1 ∧
    ccwVals P off L T1 T2 cs S xq nxt 684 = (S 32).2 ∧ ccwVals P off L T1 T2 cs S xq nxt 685 = nxt := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> simp [ccwVals]

theorem ccwVals_out (j : ℕ) (hj1 : 1 ≤ j) (hj : j ≤ 31) :
    ccwVals P off L T1 T2 cs S xq nxt (11 + 21 * j) = (S j).1 ∧
      ccwVals P off L T1 T2 cs S xq nxt (12 + 21 * j) = (S j).2 := by
  rcases Nat.eq_or_lt_of_le hj1 with rfl | hj2
  · constructor <;> simp [ccwVals, cBlk0Vals]
  · constructor
    · rw [show 11 + 21 * j = 13 + 21 * (j - 1) + 19 by omega,
        ccwVals_blk P off L T1 T2 cs S xq nxt (j - 1) 19 (by omega) (by omega) (by omega)]
      simp [cBlkVals, cHeadVals, show j - 1 + 1 = j by omega]
    · rw [show 12 + 21 * j = 13 + 21 * (j - 1) + 20 by omega,
        ccwVals_blk P off L T1 T2 cs S xq nxt (j - 1) 20 (by omega) (by omega) (by omega)]
      simp [cBlkVals, cHeadVals, show j - 1 + 1 = j by omega]

end

theorem child_window_bwd {rd : Reader} (hm : MemOk rd) {gsq : E} (hT : SquaresAt rd gsq)
    {s0 s1 base entries cover marks origin limit xq : E} {rets : List E}
    (hL : ∃ L ≤ 2 ^ 16, limit = gen ^ L)
    (h : Meaning_child_claims_window rd [s0, s1, base, entries, cover, marks, origin, limit, xq, gsq]
      rets) :
    coreProgram.Rel rd "child_claims_window"
      [s0, s1, base, entries, cover, marks, origin, limit, xq, gsq] rets := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, o0, o1, nxt, hargs, rfl, N, hN, hxq, hnxt, off, cs, hlen, hR,
    hch⟩ := h
  simp only [List.cons.injEq, and_true] at hargs
  obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ := hargs
  rcases hch with ⟨h0, -⟩ | ⟨-, h, hst, hcan, hout⟩
  · omega
  obtain ⟨L, hL16, hlim⟩ := hL
  have hoff : ∀ j < 32, off j < L := fun j hj => by
    obtain ⟨⟨L', hL', hlim', ho⟩, -⟩ := hR j hj
    have := gen_pow_inj (a := L) (b := L') (by omega) (by omega) (hlim.symm.trans hlim')
    omega
  have hw : ∀ j, ∃ t1 t2, j < 32 → LoadHolds rd (gen ^ off j) 0 t1 ∧
      LoadHolds rd (gen ^ (L - 1 - off j)) 0 t2 := fun j => by
    by_cases hj : j < 32
    · obtain ⟨t1, t2, l1, -, l2⟩ := rangeCheck_complete hm (e := off j) (e' := L - 1 - off j)
        (lt_of_lt_of_le (hoff j hj) hL16) (by omega)
      exact ⟨t1, t2, fun _ => ⟨l1, l2⟩⟩
    · exact ⟨0, 0, fun h => absurd h hj⟩
  choose T1 T2 hT' using hw
  set P := listVal [s0, s1, base, entries, cover, marks, origin, limit, xq, gsq] with hP
  set S := fun j => digestScalars (chainRun h (blocksOf cs) (windowMd base nxt) j) with hS
  have hsteps := steps_of_chainCells (h := h) hcan
  have hS0 : S 0 = (s0, s1) := by rw [hS]; exact hst.symm
  rw [rel_of_find find_child_claims_window]
  simp only [Fn.Sem, ccwBody, ccwLast, holdsList_atoms, List.cons_append, List.nil_append,
    Stmt.HoldsList, Stmt.Holds, Atom.Holds, List.forall_mem_append, forall_mem_flatMap_range,
    List.forall_mem_cons, forall_mem_nil_iff, and_true, List.map_cons, List.map_nil]
  obtain ⟨e681, e682, e683, e684, e685⟩ := ccwVals_end P off L T1 T2 cs S xq nxt
  refine ⟨fun v => ccwVals P off L T1 T2 cs S xq nxt v.idx, rfl, rfl, rfl, ?_, ?_, ?_,
    ⟨⟨⟨?_, fun i hi => ?_⟩, ?_, ?_⟩, ?_, ?_, ?_⟩, ?_⟩
  · exact (scaled_log_11_iff hT _ _).mpr ⟨nxt, rfl, N, hN,
      by show xq * word 2 0 0 = gen ^ N; rw [word_gen]; exact hxq, hnxt⟩
  · show ccwVals P off L T1 T2 cs S xq nxt 13 = ccwVals P off L T1 T2 cs S xq nxt 0
    simp only [ccwVals]; simp [hS0, hP, listVal]
  · show ccwVals P off L T1 T2 cs S xq nxt 14 = ccwVals P off L T1 T2 cs S xq nxt 1
    simp only [ccwVals]; simp [hS0, hP, listVal]
  · obtain ⟨-, hs, hc⟩ := hR 0 (by omega)
    rw [pow_zero, mul_one] at hs
    have hcc := hsteps 0 (by omega)
    rw [blocksOf_getD] at hcc
    refine cBlk0_bwd (o := 13) (out := S 1) (hoff 0 (by omega)) hlim (hT' 0 (by omega)).1
      (hT' 0 (by omega)).2 hs hc ?_ (fun r hr => ccwVals_blk0 P off L T1 T2 cs S xq nxt r hr)
    show CompressCells _ (ccwVals P off L T1 T2 cs S xq nxt 13) (ccwVals P off L T1 T2 cs S xq nxt 14) _ _ _
    have e13 : ccwVals P off L T1 T2 cs S xq nxt 13 = (S 0).1 := by simp [ccwVals]
    have e14 : ccwVals P off L T1 T2 cs S xq nxt 14 = (S 0).2 := by simp [ccwVals]
    rw [e13, e14]
    have : windowMd base nxt 0 = baseMd base 0 := by simp [windowMd]
    rw [this] at hcc
    exact hcc
  · obtain ⟨-, hs, hc⟩ := hR (i + 1) (by omega)
    have hcc := hsteps (i + 1) (by omega)
    rw [blocksOf_getD, show windowMd base nxt (i + 1) = baseMd base (i + 1) by
      simp [windowMd]; omega] at hcc
    have eb := ccwVals_blk P off L T1 T2 cs S xq nxt (i + 1)
    refine cBlk_bwd (o := 13) (out := S (i + 1 + 1)) (by omega) (hoff _ (by omega)) hlim
      (hT' _ (by omega)).1 (hT' _ (by omega)).2 hs hc ?_ (fun r hr => ?_) ?_ ?_ ?_ ?_
    · obtain ⟨o1', o2'⟩ := ccwVals_out P off L T1 T2 cs S xq nxt (i + 1) (by omega) (by omega)
      show CompressCells _ (ccwVals P off L T1 T2 cs S xq nxt (13 + 21 * (i + 1) - 2))
        (ccwVals P off L T1 T2 cs S xq nxt (13 + 21 * (i + 1) - 1)) _ _ _
      rw [show 13 + 21 * (i + 1) - 2 = 11 + 21 * (i + 1) by omega,
        show 13 + 21 * (i + 1) - 1 = 12 + 21 * (i + 1) by omega, o1', o2']
      exact hcc
    · show ccwVals P off L T1 T2 cs S xq nxt (13 + 21 * (i + 1) + r) = _
      rw [eb r (by omega) (by omega) (by omega), cBlkVals,
        List.getD_append _ _ _ _ (by simp [cHeadVals]; omega)]
      rfl
    · show ccwVals P off L T1 T2 cs S xq nxt (13 + 21 * (i + 1) + 17) = _
      rw [eb 17 (by omega) (by omega) (by omega)]
      simp [cBlkVals, cHeadVals]
    · show ccwVals P off L T1 T2 cs S xq nxt (13 + 21 * (i + 1) + 18) = _
      rw [eb 18 (by omega) (by omega) (by omega)]
      simp [cBlkVals, cHeadVals]
      rfl
    · show ccwVals P off L T1 T2 cs S xq nxt (13 + 21 * (i + 1) + 19) = _
      rw [eb 19 (by omega) (by omega) (by omega)]
      simp [cBlkVals, cHeadVals]
    · show ccwVals P off L T1 T2 cs S xq nxt (13 + 21 * (i + 1) + 20) = _
      rw [eb 20 (by omega) (by omega) (by omega)]
      simp [cBlkVals, cHeadVals]
  · obtain ⟨-, hs, hc⟩ := hR 31 (by omega)
    exact cBlkHead_bwd (b := 664) (by omega) (hoff 31 (by omega)) hlim (hT' 31 (by omega)).1
      (hT' 31 (by omega)).2 hs hc (fun r hr => ccwVals_last P off L T1 T2 cs S xq nxt r hr)
  · have hcc := hsteps 31 (by omega)
    rw [blocksOf_getD, show windowMd base nxt 31 = nxt by simp [windowMd]] at hcc
    obtain ⟨o1', o2'⟩ := ccwVals_out P off L T1 T2 cs S xq nxt 31 (by omega) (by omega)
    have l0 := ccwVals_last P off L T1 T2 cs S xq nxt 13 (by omega)
    have l1 := ccwVals_last P off L T1 T2 cs S xq nxt 14 (by omega)
    have l2 := ccwVals_last P off L T1 T2 cs S xq nxt 15 (by omega)
    have l3 := ccwVals_last P off L T1 T2 cs S xq nxt 16 (by omega)
    simp only [cHeadVals, List.getD_cons_succ, List.getD_cons_zero] at l0 l1 l2 l3
    show CompressCells ![ccwVals P off L T1 T2 cs S xq nxt (664 + 13),
      ccwVals P off L T1 T2 cs S xq nxt (664 + 14), ccwVals P off L T1 T2 cs S xq nxt (664 + 15),
      ccwVals P off L T1 T2 cs S xq nxt (664 + 16)] (ccwVals P off L T1 T2 cs S xq nxt (11 + 21 * 31))
      (ccwVals P off L T1 T2 cs S xq nxt (12 + 21 * 31)) (ccwVals P off L T1 T2 cs S xq nxt 681)
      (ccwVals P off L T1 T2 cs S xq nxt 682) (ccwVals P off L T1 T2 cs S xq nxt 12)
    rw [l0, l1, l2, l3, o1', o2', e681, e682, show ccwVals P off L T1 T2 cs S xq nxt 12 = nxt by
      simp [ccwVals]]
    exact hcc
  · show ccwVals P off L T1 T2 cs S xq nxt 683 = ccwVals P off L T1 T2 cs S xq nxt 681
    rw [e683, e681]
  · show ccwVals P off L T1 T2 cs S xq nxt 684 = ccwVals P off L T1 T2 cs S xq nxt 682
    rw [e684, e682]
  · show ccwVals P off L T1 T2 cs S xq nxt 685 = ccwVals P off L T1 T2 cs S xq nxt 12
    rw [e685]; simp [ccwVals]
  · show [ccwVals P off L T1 T2 cs S xq nxt 683, ccwVals P off L T1 T2 cs S xq nxt 684,
      ccwVals P off L T1 T2 cs S xq nxt 685] = _
    rw [e683, e684, e685]
    show [(S 32).1, (S 32).2, nxt] = [o0, o1, nxt]
    rw [show S 32 = (o0, o1) from hout.symm]

/-- **`child_claims_window`**: sound, and complete for a table of at most `2^16` slots. -/
theorem child_claims_window_iff {rd : Reader} (hm : MemOk rd) {gsq : E} (hT : SquaresAt rd gsq)
    {s0 s1 base entries cover marks origin limit xq : E} (rets : List E)
    (hL : ∃ L ≤ 2 ^ 16, limit = gen ^ L) :
    coreProgram.Rel rd "child_claims_window"
        [s0, s1, base, entries, cover, marks, origin, limit, xq, gsq] rets ↔
      Meaning_child_claims_window rd [s0, s1, base, entries, cover, marks, origin, limit, xq, gsq]
        rets :=
  ⟨child_window_fwd hm hT, child_window_bwd hm hT hL⟩

end
end LeanVM.Guest.B1.Digest
