/-
  LeanVM.Guest.B1.Digest.ChildAt

  The child claim lists' callees on explicit runs: `child_claims_tail__L{k}` and
  `child_claims_window`, loading only the marks' slots and the claims' cells they read.
-/

module

public import LeanVM.Guest.B1.Digest.ChildList
public import LeanVM.Guest.B1.Digest.NodeAt

namespace LeanVM.Guest.B1.Digest

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.Blake2sHash
open LeanVM.Guest.Core LeanVM.Guest.Memory LeanVM.Guest.Value
open LeanVM.Protocol.Verifier (gen eOfNat)
open LeanVM.Guest.B1 (LowDef CompleteAt Within Returns)
open LeanVM.Guest.B1.Main (Layout MemL RegionL)

@[expose] public section

/-! ## Loads of the blocks -/

theorem cBlk0_loads (o : ℕ) : (cBlk0 o).filterMap atomLoad? =
    [(.n (o + 9), 0), (.n (o + 12), 0), (.n (o + 12), 1), (.n (o + 12), 2), (.n (o + 12), 3)] := rfl

theorem cBlkHead_loads (b j : ℕ) : (cBlkHead b j).filterMap atomLoad? =
    [(.n (b + 9), 0), (.n (b + 12), 0), (.n (b + 12), 1), (.n (b + 12), 2), (.n (b + 12), 3)] := rfl

theorem cBlk_loads (o j : ℕ) : (cBlk o j).filterMap atomLoad? =
    [(.n (o + 21 * j + 9), 0), (.n (o + 21 * j + 12), 0), (.n (o + 21 * j + 12), 1),
      (.n (o + 21 * j + 12), 2), (.n (o + 21 * j + 12), 3)] := by
  rw [cBlk, List.filterMap_append, cBlkHead_loads]; rfl

/-- A child list's reads: the marks' slots and the claims' cells at the indices `off j`, `j < k`. -/
def ChildLoad (entries cover origin : E) (off : ℕ → ℕ) (k : ℕ) (A : K) : Prop :=
  (∃ j < k, A = (cover * (origin * gen ^ off j)).limb 0 * gpow 0) ∨
    ∃ j < k, ∃ r < 4, A = (entries * gen ^ (4 * off j)).limb 0 * gpow r

/-! ## `child_claims_tail__L{k}` -/

def cctAtoms (k : ℕ) : List Atom :=
  ([.copy (.n 8) (.n 0), .copy (.n 9) (.n 1)] : List Atom) ++ cBlk0 8 ++
    (List.range (k - 1)).flatMap (fun i => cBlk 8 (i + 1)) ++
    ([.copy (.n (8 + 21 * k)) (.n (6 + 21 * k)), .copy (.n (9 + 21 * k)) (.n (7 + 21 * k))] : List Atom)

theorem cctBody_eq (k : ℕ) : cctBody k = (cctAtoms k).map .atom ++ [.ret [.n (8 + 21 * k), .n (9 + 21 * k)]] := rfl

/-- **`child_claims_tail__L{k}`'s honest run**, `k ≥ 1`, on a memory defined below `2^16`: a
valuation of its body loading only the marks' slots and the claims' cells of `ChildReads`. -/
theorem cct_run {rd : Reader} (hl : Low16 rd) (k : ℕ) (hk1 : 1 ≤ k) (hk : k < 32)
    {s0 s1 base entries cover marks origin limit o0 o1 : E} {L : ℕ} (hL16 : L ≤ 2 ^ 16)
    (hlim : limit = gen ^ L) {off : ℕ → ℕ} {cs : List E}
    (hR : ChildReads rd entries cover marks origin limit off cs k)
    (hch : ChainCells (s0, s1) (blocksOf cs) (baseMd base) k (o0, o1)) :
    ∃ σ : Val, [.n 0, .n 1, .n 2, .n 3, .n 4, .n 5, .n 6, .n 7].map σ =
        [s0, s1, base, entries, cover, marks, origin, limit] ∧
      (∀ a ∈ cctAtoms k, a.Holds rd σ) ∧ [σ (.n (8 + 21 * k)), σ (.n (9 + 21 * k))] = [o0, o1] ∧
      ∀ A ∈ loadAddrs σ ((cctAtoms k).map Ev.atom), ChildLoad entries cover origin off k A := by
  rcases hch with ⟨h0, -⟩ | ⟨-, h, hst, hcan, hout⟩
  · omega
  have hoff : ∀ j < k, off j < L := fun j hj => by
    obtain ⟨⟨L', hL', hlim', ho⟩, -⟩ := hR j hj
    have := gen_pow_inj (a := L) (b := L') (by omega) (by omega) (hlim.symm.trans hlim')
    omega
  have hw : ∀ j, ∃ t1 t2, j < k → LoadHolds rd (gen ^ off j) 0 t1 ∧
      LoadHolds rd (gen ^ (L - 1 - off j)) 0 t2 := fun j => by
    by_cases hj : j < k
    · obtain ⟨t1, t2, l1, -, l2⟩ := rangeCheck_complete_low hl (e := off j) (e' := L - 1 - off j)
        (by have := hoff j hj; omega) (by omega)
      exact ⟨t1, t2, fun _ => ⟨l1, l2⟩⟩
    · exact ⟨0, 0, fun h => absurd h hj⟩
  choose T1 T2 hT using hw
  set P := listVal [s0, s1, base, entries, cover, marks, origin, limit] with hP
  set S := fun j => digestScalars (chainRun h (blocksOf cs) (baseMd base) j) with hS
  have hsteps := steps_of_chainCells (h := h) hcan
  have hS0 : S 0 = (s0, s1) := by rw [hS]; exact hst.symm
  obtain ⟨e8, e8k, e6⟩ := cctVals_end k P off L T1 T2 cs S
  obtain ⟨t8, t9⟩ := cctVals_st0 k P off L T1 T2 cs S
  have hH : Stmt.HoldsList (coreProgram.Rel rd) rd (fun v => cctVals k P off L T1 T2 cs S v.idx) (cctBody k) False
      (fun rs => rs = [o0, o1]) := by
    simp only [cctBody, holdsList_atoms, holdsList_ret, List.forall_mem_append,
      forall_mem_flatMap_range, List.forall_mem_cons, Atom.Holds, forall_mem_nil_iff, and_true,
      List.map_cons, List.map_nil]
    refine ⟨⟨⟨⟨⟨?_, ?_⟩, ?_⟩, fun i hi => ?_⟩, ?_, ?_⟩, ?_⟩
    · show cctVals k P off L T1 T2 cs S 8 = cctVals k P off L T1 T2 cs S 0
      rw [t8, hS0]; rfl
    · show cctVals k P off L T1 T2 cs S 9 = cctVals k P off L T1 T2 cs S 1
      rw [t9, hS0]; rfl
    · obtain ⟨-, hs, hc⟩ := hR 0 hk1
      rw [pow_zero, mul_one] at hs
      have hcc := hsteps 0 hk1
      rw [blocksOf_getD] at hcc
      refine cBlk0_bwd (o := 8) (out := S 1) (hoff 0 hk1) hlim (hT 0 hk1).1 (hT 0 hk1).2 hs hc ?_
        (fun r hr => cctVals_blk0 k P off L T1 T2 cs S r hr)
      show CompressCells _ (cctVals k P off L T1 T2 cs S 8) (cctVals k P off L T1 T2 cs S 9) _ _ _
      rw [t8, t9]
      exact hcc
    · obtain ⟨-, hs, hc⟩ := hR (i + 1) (by omega)
      have hcc := hsteps (i + 1) (by omega)
      rw [blocksOf_getD] at hcc
      have eb := cctVals_blk k P off L T1 T2 cs S (i + 1)
      refine cBlk_bwd (o := 8) (out := S (i + 1 + 1)) (by omega) (hoff _ (by omega)) hlim
        (hT _ (by omega)).1 (hT _ (by omega)).2 hs hc ?_ (fun r hr => ?_) ?_ ?_ ?_ ?_
      · obtain ⟨o1', o2'⟩ := cctVals_out k P off L T1 T2 cs S (i + 1) (by omega) (by omega)
        show CompressCells _ (cctVals k P off L T1 T2 cs S (8 + 21 * (i + 1) - 2))
          (cctVals k P off L T1 T2 cs S (8 + 21 * (i + 1) - 1)) _ _ _
        rw [show 8 + 21 * (i + 1) - 2 = 6 + 21 * (i + 1) by omega,
          show 8 + 21 * (i + 1) - 1 = 7 + 21 * (i + 1) by omega, o1', o2']
        exact hcc
      · show cctVals k P off L T1 T2 cs S (8 + 21 * (i + 1) + r) = _
        rw [eb r (by omega) (by omega) (by omega), cBlkVals,
          List.getD_append _ _ _ _ (by simp [cHeadVals]; omega)]
        rfl
      · show cctVals k P off L T1 T2 cs S (8 + 21 * (i + 1) + 17) = _
        rw [eb 17 (by omega) (by omega) (by omega)]
        simp [cBlkVals, cHeadVals]
      · show cctVals k P off L T1 T2 cs S (8 + 21 * (i + 1) + 18) = _
        rw [eb 18 (by omega) (by omega) (by omega)]
        simp [cBlkVals, cHeadVals]
        rfl
      · show cctVals k P off L T1 T2 cs S (8 + 21 * (i + 1) + 19) = _
        rw [eb 19 (by omega) (by omega) (by omega)]
        simp [cBlkVals, cHeadVals]
      · show cctVals k P off L T1 T2 cs S (8 + 21 * (i + 1) + 20) = _
        rw [eb 20 (by omega) (by omega) (by omega)]
        simp [cBlkVals, cHeadVals]
    · show cctVals k P off L T1 T2 cs S (8 + 21 * k) = cctVals k P off L T1 T2 cs S (6 + 21 * k)
      rw [e8, (e6 hk1).1]
    · show cctVals k P off L T1 T2 cs S (9 + 21 * k) = cctVals k P off L T1 T2 cs S (7 + 21 * k)
      rw [e8k, (e6 hk1).2]
    · show [cctVals k P off L T1 T2 cs S (8 + 21 * k), cctVals k P off L T1 T2 cs S (9 + 21 * k)] = _
      rw [e8, e8k]
      show [(S k).1, (S k).2] = [o0, o1]
      rw [show S k = (o0, o1) from hout.symm]
  rw [cctBody_eq, holdsList_atoms, holdsList_ret] at hH
  refine ⟨fun v => cctVals k P off L T1 T2 cs S v.idx, rfl, hH.1, hH.2, fun A hA => ?_⟩
  rw [loadAddrs_atoms] at hA
  simp only [cctAtoms, List.filterMap_append, List.filterMap_flatMap, cBlk0_loads, cBlk_loads, List.map_append,
    List.mem_append, List.mem_map, List.mem_flatMap, List.mem_range, List.mem_cons, List.not_mem_nil, or_false,
    List.filterMap_cons, List.filterMap_nil, atomLoad?] at hA
  have h17 : cctVals k P off L T1 T2 cs S (8 + 9) = cover * (origin * gen ^ off 0) := by
    rw [show 8 + 9 = 8 + 2 + 7 from rfl, cctVals_blk0 k P off L T1 T2 cs S 7 (by omega)]; rfl
  have h20 : cctVals k P off L T1 T2 cs S (8 + 12) = entries * gen ^ (4 * off 0) := by
    rw [show 8 + 12 = 8 + 2 + 10 from rfl, cctVals_blk0 k P off L T1 T2 cs S 10 (by omega)]
    show P (.n 3) * (gen ^ off 0 * gen ^ off 0 * (gen ^ off 0 * gen ^ off 0)) = _
    rw [pow4_eq _ _ rfl]; rfl
  have hb9 : ∀ j, 1 ≤ j → j < k →
      cctVals k P off L T1 T2 cs S (8 + 21 * j + 9) = cover * (origin * gen ^ off j) := fun j h1 h2 => by
    rw [cctVals_blk k P off L T1 T2 cs S j 9 h1 h2 (by omega)]; rfl
  have hb12 : ∀ j, 1 ≤ j → j < k →
      cctVals k P off L T1 T2 cs S (8 + 21 * j + 12) = entries * gen ^ (4 * off j) := fun j h1 h2 => by
    rw [cctVals_blk k P off L T1 T2 cs S j 12 h1 h2 (by omega)]
    show P (.n 3) * (gen ^ off j * gen ^ off j * (gen ^ off j * gen ^ off j)) = _
    rw [pow4_eq _ _ rfl]; rfl
  rcases hA with ((⟨_, h, _⟩ | ⟨q, hq, rfl⟩) | ⟨q, ⟨i, hi, hq⟩, rfl⟩) | ⟨_, h, _⟩
  · exact h.elim
  · rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact Or.inl ⟨0, hk1, by show (cctVals k P off L T1 T2 cs S (8 + 9)).limb 0 * _ = _; rw [h17]⟩
    all_goals refine Or.inr ⟨0, hk1, ?_⟩
    · exact ⟨0, by omega, by show (cctVals k P off L T1 T2 cs S (8 + 12)).limb 0 * _ = _; rw [h20]⟩
    · exact ⟨1, by omega, by show (cctVals k P off L T1 T2 cs S (8 + 12)).limb 0 * _ = _; rw [h20]⟩
    · exact ⟨2, by omega, by show (cctVals k P off L T1 T2 cs S (8 + 12)).limb 0 * _ = _; rw [h20]⟩
    · exact ⟨3, by omega, by show (cctVals k P off L T1 T2 cs S (8 + 12)).limb 0 * _ = _; rw [h20]⟩
  · rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact Or.inl ⟨i + 1, by omega, by
        show (cctVals k P off L T1 T2 cs S (8 + 21 * (i + 1) + 9)).limb 0 * _ = _; rw [hb9 _ (by omega) (by omega)]⟩
    all_goals refine Or.inr ⟨i + 1, by omega, ?_⟩
    all_goals have e12 := hb12 (i + 1) (by omega) (by omega)
    · exact ⟨0, by omega, by show (cctVals k P off L T1 T2 cs S (8 + 21 * (i + 1) + 12)).limb 0 * _ = _; rw [e12]⟩
    · exact ⟨1, by omega, by show (cctVals k P off L T1 T2 cs S (8 + 21 * (i + 1) + 12)).limb 0 * _ = _; rw [e12]⟩
    · exact ⟨2, by omega, by show (cctVals k P off L T1 T2 cs S (8 + 21 * (i + 1) + 12)).limb 0 * _ = _; rw [e12]⟩
    · exact ⟨3, by omega, by show (cctVals k P off L T1 T2 cs S (8 + 21 * (i + 1) + 12)).limb 0 * _ = _; rw [e12]⟩
  · exact h.elim

end
end LeanVM.Guest.B1.Digest
