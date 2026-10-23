/-
  LeanVM.Guest.B1.Digest.ChildAt

  The child claim lists' callees on explicit runs: `child_claims_tail__L{k}` and
  `child_claims_window`, loading only the marks' slots and the claims' cells they read.
-/

module

public import LeanVM.Guest.Memory.Size
public import LeanVM.Guest.B1.Digest.ChildList
public import LeanVM.Guest.B1.Digest.NodeAt
public import LeanVM.Guest.B1.Digest.ClaimListAt

namespace LeanVM.Guest.B1.Digest

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.Blake2sHash
open LeanVM.Guest.Core LeanVM.Guest.Memory LeanVM.Guest.Value
open LeanVM.Protocol.Verifier (gen eOfNat)
open LeanVM.Guest.B1 (LowDef CompleteAt CompleteAtD CompleteAtB kidsBound DisjL disj_nil disj_append Within Returns)
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

theorem cBlk0_noAlloc (o : ℕ) : (cBlk0 o).all (fun a => !atomAllocB a) = true := rfl
theorem cBlk_noAlloc (o j : ℕ) : (cBlk o j).all (fun a => !atomAllocB a) = true := rfl
theorem cBlk0_noAddr (o : ℕ) : (cBlk0 o).filterMap atomAddr? = [] := rfl
theorem cBlk_noAddr (o j : ℕ) : (cBlk o j).filterMap atomAddr? = [] := rfl

theorem cctAtoms_noAlloc (k : ℕ) : (cctAtoms k).all (fun a => !atomAllocB a) = true := by
  simp only [cctAtoms, List.all_append, List.all_flatMap, cBlk0_noAlloc, cBlk_noAlloc]
  simp [atomAllocB]

theorem cctAtoms_noAddr (k : ℕ) : (cctAtoms k).filterMap atomAddr? = [] := by
  simp only [cctAtoms, List.filterMap_append, List.filterMap_flatMap, cBlk0_noAddr, cBlk_noAddr]
  simp [atomAddr?]

/-- **`child_claims_tail__L{k}` is complete, uniformly placed**, on reads every memory holding the
caller's words makes, at words of those. -/
theorem cct_completeAt (fs : String → ℕ) (cert : String → V → ℕ) {κ : ℕ} (hκ : 16 ≤ κ) (k : ℕ) (hk : k < 32)
    (Lin : Layout) {s0 s1 base entries cover marks origin limit o0 o1 : E} {L : ℕ} (hL16 : L ≤ 2 ^ 16)
    (hlim : limit = gen ^ L) {off : ℕ → ℕ} {cs : List E}
    (hR : ∀ rd, LowDef κ rd → MemL rd Lin → ChildReads rd entries cover marks origin limit off cs k)
    (hreg : ∀ A, ChildLoad entries cover origin off k A → ∃ i, A = gpow i ∧ RegionL Lin i)
    (hch : ChainCells (s0, s1) (blocksOf cs) (baseMd base) k (o0, o1)) :
    CompleteAt fs cert κ (cctNames.getD k "") Lin [s0, s1, base, entries, cover, marks, origin, limit]
      (Returns [o0, o1]) := by
  rcases Nat.eq_zero_or_pos k with rfl | hk1
  · obtain ⟨-, hout⟩ | ⟨h, -⟩ := hch
    swap; · omega
    simp only [Prod.mk.injEq] at hout
    refine LeanVM.Guest.B1.completeAt_leaf (find_child_claims_tail 0 hk) (by decide +kernel) κ Lin _ _ [] (fun _ => [])
      (fun _ => List.Forall₂.nil) fun fp rd _ _ _ => ?_
    refine ⟨listVal [s0, s1, base, entries, cover, marks, origin, limit, s0, s1, s0, s1], _, _, rfl,
      by show walk _ cctBody0 = _; exact walk_atoms _ _ _, by rw [hout.1, hout.2]; rfl, ?_, calls_atoms _,
      by rw [addrs_atoms]; rfl,
      allocs_atoms _ (by decide), by rw [allocDsts_atoms (by decide)]; rfl, ?_⟩
    · intro e he
      simp only [List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false] at he
      rcases he with rfl | rfl | rfl | rfl <;> rfl
    · intro A hA
      rw [loadAddrs_atoms] at hA
      simp [atomLoad?] at hA
  · refine LeanVM.Guest.B1.completeAt_leaf (find_child_claims_tail k hk) (by
      rw [Program.loop_of_find? (find_child_claims_tail k hk)]
      simp only [Fn.loop, show ¬k = 0 by omega, ↓reduceIte, cctBody_eq, List.reverse_append]
      rfl) κ Lin _ _ [] (fun _ => []) (fun _ => List.Forall₂.nil) fun fp rd hl _ hL => ?_
    obtain ⟨σ, hp, hh, hr, hld⟩ := cct_run (fun i hi => hl i (lt_of_lt_of_le hi (Nat.pow_le_pow_right (by norm_num) hκ)))
      k hk1 hk hL16 hlim (hR rd hl hL) hch
    refine ⟨σ, _, [.n (8 + 21 * k), .n (9 + 21 * k)], hp, by simp only [show ¬k = 0 by omega, ↓reduceIte, cctBody_eq]; exact walk_atoms _ _ _, hr,
      fun e he => ?_, calls_atoms _, by rw [addrs_atoms, cctAtoms_noAddr], allocs_atoms _ (cctAtoms_noAlloc k),
      by rw [allocDsts_atoms (cctAtoms_noAlloc k)]; rfl, fun A hA => ?_⟩
    · obtain ⟨a, ha, rfl⟩ := List.mem_map.mp he
      exact hh a ha
    · obtain ⟨i, hi, hRi⟩ := hreg A (hld A hA)
      exact ⟨i, hi, Or.inr hRi⟩

/-- **`child_claims_tail__L{k}` is complete, uniformly placed**, on reads every memory holding the
caller's words makes, at words of those. -/
theorem cct_completeAtD (fs : String → ℕ) (cert : String → V → ℕ) {κ : ℕ} (hκ : 16 ≤ κ) (k : ℕ) (hk : k < 32)
    (Lin : Layout) {s0 s1 base entries cover marks origin limit o0 o1 : E} {L : ℕ} (hL16 : L ≤ 2 ^ 16)
    (hlim : limit = gen ^ L) {off : ℕ → ℕ} {cs : List E}
    (hR : ∀ rd, LowDef κ rd → MemL rd Lin → ChildReads rd entries cover marks origin limit off cs k)
    (hreg : ∀ A, ChildLoad entries cover origin off k A → ∃ i, A = gpow i ∧ RegionL Lin i)
    (hch : ChainCells (s0, s1) (blocksOf cs) (baseMd base) k (o0, o1)) :
    CompleteAtD fs cert κ (cctNames.getD k "") Lin [s0, s1, base, entries, cover, marks, origin, limit]
      (Returns [o0, o1]) := by
  rcases Nat.eq_zero_or_pos k with rfl | hk1
  · obtain ⟨-, hout⟩ | ⟨h, -⟩ := hch
    swap; · omega
    simp only [Prod.mk.injEq] at hout
    refine LeanVM.Guest.B1.completeAt_leafD (find_child_claims_tail 0 hk) (by decide +kernel) κ Lin _ _ [] (fun _ => [])
      (fun _ => List.Forall₂.nil) fun fp rd _ _ _ => ?_
    refine ⟨listVal [s0, s1, base, entries, cover, marks, origin, limit, s0, s1, s0, s1], _, _, rfl,
      by show walk _ cctBody0 = _; exact walk_atoms _ _ _, by rw [hout.1, hout.2]; rfl, ?_, calls_atoms _,
      by rw [addrs_atoms]; rfl,
      allocs_atoms _ (by decide), by rw [allocDsts_atoms (by decide)]; rfl, ?_⟩
    · intro e he
      simp only [List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false] at he
      rcases he with rfl | rfl | rfl | rfl <;> rfl
    · intro A hA
      rw [loadAddrs_atoms] at hA
      simp [atomLoad?] at hA
  · refine LeanVM.Guest.B1.completeAt_leafD (find_child_claims_tail k hk) (by
      rw [Program.loop_of_find? (find_child_claims_tail k hk)]
      simp only [Fn.loop, show ¬k = 0 by omega, ↓reduceIte, cctBody_eq, List.reverse_append]
      rfl) κ Lin _ _ [] (fun _ => []) (fun _ => List.Forall₂.nil) fun fp rd hl _ hL => ?_
    obtain ⟨σ, hp, hh, hr, hld⟩ := cct_run (fun i hi => hl i (lt_of_lt_of_le hi (Nat.pow_le_pow_right (by norm_num) hκ)))
      k hk1 hk hL16 hlim (hR rd hl hL) hch
    refine ⟨σ, _, [.n (8 + 21 * k), .n (9 + 21 * k)], hp, by simp only [show ¬k = 0 by omega, ↓reduceIte, cctBody_eq]; exact walk_atoms _ _ _, hr,
      fun e he => ?_, calls_atoms _, by rw [addrs_atoms, cctAtoms_noAddr], allocs_atoms _ (cctAtoms_noAlloc k),
      by rw [allocDsts_atoms (cctAtoms_noAlloc k)]; rfl, fun A hA => ?_⟩
    · obtain ⟨a, ha, rfl⟩ := List.mem_map.mp he
      exact hh a ha
    · obtain ⟨i, hi, hRi⟩ := hreg A (hld A hA)
      exact ⟨i, hi, Or.inr hRi⟩

/-! ## `child_claims_window` -/

/-- **`child_claims_tail__L{k}` is complete, uniformly placed**, on reads every memory holding the
caller's words makes, at words of those. -/
theorem cct_completeAtB (fs : String → ℕ) (cert : String → V → ℕ) {κ : ℕ} (hκ : 16 ≤ κ) (k : ℕ) (hk : k < 32)
    (Lin : Layout) {s0 s1 base entries cover marks origin limit o0 o1 : E} {L : ℕ} (hL16 : L ≤ 2 ^ 16)
    (hlim : limit = gen ^ L) {off : ℕ → ℕ} {cs : List E}
    (hR : ∀ rd, LowDef κ rd → MemL rd Lin → ChildReads rd entries cover marks origin limit off cs k)
    (hreg : ∀ A, ChildLoad entries cover origin off k A → ∃ i, A = gpow i ∧ RegionL Lin i)
    (hch : ChainCells (s0, s1) (blocksOf cs) (baseMd base) k (o0, o1)) :
    CompleteAtB fs cert κ (cctNames.getD k "") Lin [s0, s1, base, entries, cover, marks, origin, limit]
      (Returns [o0, o1]) (fs (cctNames.getD k "")) := by
  rcases Nat.eq_zero_or_pos k with rfl | hk1
  · obtain ⟨-, hout⟩ | ⟨h, -⟩ := hch
    swap; · omega
    simp only [Prod.mk.injEq] at hout
    refine LeanVM.Guest.B1.completeAt_leafB (find_child_claims_tail 0 hk) (by decide +kernel) κ Lin _ _ [] (fun _ => [])
      (fun _ => List.Forall₂.nil) fun fp rd _ _ _ => ?_
    refine ⟨listVal [s0, s1, base, entries, cover, marks, origin, limit, s0, s1, s0, s1], _, _, rfl,
      by show walk _ cctBody0 = _; exact walk_atoms _ _ _, by rw [hout.1, hout.2]; rfl, ?_, calls_atoms _,
      by rw [addrs_atoms]; rfl,
      allocs_atoms _ (by decide), by rw [allocDsts_atoms (by decide)]; rfl, ?_⟩
    · intro e he
      simp only [List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false] at he
      rcases he with rfl | rfl | rfl | rfl <;> rfl
    · intro A hA
      rw [loadAddrs_atoms] at hA
      simp [atomLoad?] at hA
  · refine LeanVM.Guest.B1.completeAt_leafB (find_child_claims_tail k hk) (by
      rw [Program.loop_of_find? (find_child_claims_tail k hk)]
      simp only [Fn.loop, show ¬k = 0 by omega, ↓reduceIte, cctBody_eq, List.reverse_append]
      rfl) κ Lin _ _ [] (fun _ => []) (fun _ => List.Forall₂.nil) fun fp rd hl _ hL => ?_
    obtain ⟨σ, hp, hh, hr, hld⟩ := cct_run (fun i hi => hl i (lt_of_lt_of_le hi (Nat.pow_le_pow_right (by norm_num) hκ)))
      k hk1 hk hL16 hlim (hR rd hl hL) hch
    refine ⟨σ, _, [.n (8 + 21 * k), .n (9 + 21 * k)], hp, by simp only [show ¬k = 0 by omega, ↓reduceIte, cctBody_eq]; exact walk_atoms _ _ _, hr,
      fun e he => ?_, calls_atoms _, by rw [addrs_atoms, cctAtoms_noAddr], allocs_atoms _ (cctAtoms_noAlloc k),
      by rw [allocDsts_atoms (cctAtoms_noAlloc k)]; rfl, fun A hA => ?_⟩
    · obtain ⟨a, ha, rfl⟩ := List.mem_map.mp he
      exact hh a ha
    · obtain ⟨i, hi, hRi⟩ := hreg A (hld A hA)
      exact ⟨i, hi, Or.inr hRi⟩

/-! ## `child_claims_window` -/

def ccwRest : List Atom :=
  ([.copy (.n 13) (.n 0), .copy (.n 14) (.n 1)] : List Atom) ++ cBlk0 13 ++
    (List.range 30).flatMap (fun i => cBlk 13 (i + 1)) ++ ccwLast ++
    ([.copy (.n 683) (.n 681), .copy (.n 684) (.n 682), .copy (.n 685) (.n 12)] : List Atom)

def ccwPre : List Stmt :=
  ([.const (.n 10) (word 2 0 0), .mul (.n 11) (.n 8) (.n 10)] : List Atom).map .atom ++
    [.call "scaled_log__L11" [.n 11, .n 9] [.n 12]] ++ ccwRest.map .atom

theorem ccwBody_eq : ccwBody = ccwPre ++ [.ret [.n 683, .n 684, .n 685]] := by
  rw [ccwBody, ccwPre, ccwRest, List.append_assoc]

theorem ccwPre_straight : ccwPre.all Main.Stmt.straight = true := by
  simp [ccwPre, Main.Stmt.straight]

theorem stmtLoad_atoms (as : List Atom) : (as.map Stmt.atom).filterMap stmtLoad? = as.filterMap atomLoad? := by
  induction as with
  | nil => rfl
  | cons a as ih => cases a <;> simp only [List.map_cons, List.filterMap_cons, stmtLoad?, atomLoad?, ih]

/-- **`child_claims_window`'s honest run** on a memory defined below `2^16`. -/
theorem ccw_run {rd : Reader} (hl : Low16 rd) {gsq : E} (hT : SquaresAt rd gsq)
    {s0 s1 base entries cover marks origin limit xq o0 o1 nxt : E} {L : ℕ} (hL16 : L ≤ 2 ^ 16)
    (hlim : limit = gen ^ L) {N : ℕ} (hN : N < 2 ^ 16) (hxq : xq * gen = gen ^ N) (hnxt : nxt = eOfNat (2 ^ 11 * N))
    {off : ℕ → ℕ} {cs : List E} (hR : ChildReads rd entries cover marks origin limit off cs 32)
    (hch : ChainCells (s0, s1) (blocksOf cs) (windowMd base nxt) 32 (o0, o1)) :
    ∃ σ : Val, [.n 0, .n 1, .n 2, .n 3, .n 4, .n 5, .n 6, .n 7, .n 8, .n 9].map σ =
        [s0, s1, base, entries, cover, marks, origin, limit, xq, gsq] ∧
      Stmt.HoldsList (coreProgram.Rel rd) rd σ ccwBody False (fun rs => rs = [o0, o1, nxt]) ∧
      σ (.n 11) = xq * word 2 0 0 ∧ σ (.n 12) = nxt ∧ [σ (.n 683), σ (.n 684), σ (.n 685)] = [o0, o1, nxt] ∧
      ∀ A ∈ loadAddrs σ (ccwPre.flatMap (Main.slEvs σ)), ChildLoad entries cover origin off 32 A := by
  rcases hch with ⟨h0, -⟩ | ⟨-, h, hst, hcan, hout⟩
  · omega
  have hoff : ∀ j < 32, off j < L := fun j hj => by
    obtain ⟨⟨L', hL', hlim', ho⟩, -⟩ := hR j hj
    have := gen_pow_inj (a := L) (b := L') (by omega) (by omega) (hlim.symm.trans hlim')
    omega
  have hw : ∀ j, ∃ t1 t2, j < 32 → LoadHolds rd (gen ^ off j) 0 t1 ∧
      LoadHolds rd (gen ^ (L - 1 - off j)) 0 t2 := fun j => by
    by_cases hj : j < 32
    · obtain ⟨t1, t2, l1, -, l2⟩ := rangeCheck_complete_low hl (e := off j) (e' := L - 1 - off j)
        (lt_of_lt_of_le (hoff j hj) hL16) (by omega)
      exact ⟨t1, t2, fun _ => ⟨l1, l2⟩⟩
    · exact ⟨0, 0, fun h => absurd h hj⟩
  choose T1 T2 hT' using hw
  set P := listVal [s0, s1, base, entries, cover, marks, origin, limit, xq, gsq] with hP
  set S := fun j => digestScalars (chainRun h (blocksOf cs) (windowMd base nxt) j) with hS
  have hsteps := steps_of_chainCells (h := h) hcan
  have hS0 : S 0 = (s0, s1) := by rw [hS]; exact hst.symm
  obtain ⟨e681, e682, e683, e684, e685⟩ := ccwVals_end P off L T1 T2 cs S xq nxt
  have hH : Stmt.HoldsList (coreProgram.Rel rd) rd (fun v => ccwVals P off L T1 T2 cs S xq nxt v.idx) ccwBody False
      (fun rs => rs = [o0, o1, nxt]) := by
    simp only [ccwBody, ccwLast, holdsList_atoms, List.cons_append, List.nil_append,
      Stmt.HoldsList, Stmt.Holds, Atom.Holds, List.forall_mem_append, forall_mem_flatMap_range,
      List.forall_mem_cons, forall_mem_nil_iff, and_true, List.map_cons, List.map_nil]
    refine ⟨rfl, rfl, ?_, ?_, ?_, ⟨⟨⟨?_, fun i hi => ?_⟩, ?_, ?_⟩, ?_, ?_, ?_⟩, ?_⟩
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

  refine ⟨fun v => ccwVals P off L T1 T2 cs S xq nxt v.idx, rfl, hH, rfl, rfl, ?_, fun A hA => ?_⟩
  · show [ccwVals P off L T1 T2 cs S xq nxt 683, ccwVals P off L T1 T2 cs S xq nxt 684,
      ccwVals P off L T1 T2 cs S xq nxt 685] = _
    rw [e683, e684, e685, show S 32 = (o0, o1) from hout.symm]
  rw [loadAddrs_straight _ _ ccwPre_straight] at hA
  simp only [ccwPre, ccwRest, ccwLast, List.filterMap_append, stmtLoad_atoms, List.filterMap_flatMap, cBlk0_loads,
    cBlk_loads, cBlkHead_loads, List.map_append, List.mem_append, List.mem_map, List.mem_flatMap, List.mem_range,
    List.mem_cons, List.not_mem_nil, or_false, List.filterMap_cons, List.filterMap_nil, atomLoad?, stmtLoad?] at hA
  set V := ccwVals P off L T1 T2 cs S xq nxt with hV
  have h22 : V (13 + 9) = cover * (origin * gen ^ off 0) := by
    rw [hV, show 13 + 9 = 13 + 2 + 7 from rfl, ccwVals_blk0 P off L T1 T2 cs S xq nxt 7 (by omega)]; rfl
  have h25 : V (13 + 12) = entries * gen ^ (4 * off 0) := by
    rw [hV, show 13 + 12 = 13 + 2 + 10 from rfl, ccwVals_blk0 P off L T1 T2 cs S xq nxt 10 (by omega)]
    show P (.n 3) * (gen ^ off 0 * gen ^ off 0 * (gen ^ off 0 * gen ^ off 0)) = _
    rw [pow4_eq _ _ rfl]; rfl
  have hb9 : ∀ j, 1 ≤ j → j < 31 → V (13 + 21 * j + 9) = cover * (origin * gen ^ off j) := fun j h1 h2 => by
    rw [hV, ccwVals_blk P off L T1 T2 cs S xq nxt j 9 h1 h2 (by omega)]; rfl
  have hb12 : ∀ j, 1 ≤ j → j < 31 → V (13 + 21 * j + 12) = entries * gen ^ (4 * off j) := fun j h1 h2 => by
    rw [hV, ccwVals_blk P off L T1 T2 cs S xq nxt j 12 h1 h2 (by omega)]
    show P (.n 3) * (gen ^ off j * gen ^ off j * (gen ^ off j * gen ^ off j)) = _
    rw [pow4_eq _ _ rfl]; rfl
  have hl9 : V (664 + 9) = cover * (origin * gen ^ off 31) := by
    rw [hV, ccwVals_last P off L T1 T2 cs S xq nxt 9 (by omega)]; rfl
  have hl12 : V (664 + 12) = entries * gen ^ (4 * off 31) := by
    rw [hV, ccwVals_last P off L T1 T2 cs S xq nxt 12 (by omega)]
    show P (.n 3) * (gen ^ off 31 * gen ^ off 31 * (gen ^ off 31 * gen ^ off 31)) = _
    rw [pow4_eq _ _ rfl]; rfl
  rcases hA with (⟨_, h, _⟩ | ⟨_, h, _⟩) | ((((⟨_, h, _⟩ | ⟨q, hq, rfl⟩) | ⟨q, ⟨i, hi, hq⟩, rfl⟩) |
    (⟨q, hq, rfl⟩ | ⟨_, h, _⟩)) | ⟨_, h, _⟩)
  all_goals try exact h.elim
  · rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact Or.inl ⟨0, by omega, by show (V (13 + 9)).limb 0 * _ = _; rw [h22]⟩
    · exact Or.inr ⟨0, by omega, 0, by omega, by show (V (13 + 12)).limb 0 * _ = _; rw [h25]⟩
    · exact Or.inr ⟨0, by omega, 1, by omega, by show (V (13 + 12)).limb 0 * _ = _; rw [h25]⟩
    · exact Or.inr ⟨0, by omega, 2, by omega, by show (V (13 + 12)).limb 0 * _ = _; rw [h25]⟩
    · exact Or.inr ⟨0, by omega, 3, by omega, by show (V (13 + 12)).limb 0 * _ = _; rw [h25]⟩
  · have e9 := hb9 (i + 1) (by omega) (by omega)
    have e12 := hb12 (i + 1) (by omega) (by omega)
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact Or.inl ⟨i + 1, by omega, by show (V (13 + 21 * (i + 1) + 9)).limb 0 * _ = _; rw [e9]⟩
    · exact Or.inr ⟨i + 1, by omega, 0, by omega, by show (V (13 + 21 * (i + 1) + 12)).limb 0 * _ = _; rw [e12]⟩
    · exact Or.inr ⟨i + 1, by omega, 1, by omega, by show (V (13 + 21 * (i + 1) + 12)).limb 0 * _ = _; rw [e12]⟩
    · exact Or.inr ⟨i + 1, by omega, 2, by omega, by show (V (13 + 21 * (i + 1) + 12)).limb 0 * _ = _; rw [e12]⟩
    · exact Or.inr ⟨i + 1, by omega, 3, by omega, by show (V (13 + 21 * (i + 1) + 12)).limb 0 * _ = _; rw [e12]⟩
  · rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact Or.inl ⟨31, by omega, by show (V (664 + 9)).limb 0 * _ = _; rw [hl9]⟩
    · exact Or.inr ⟨31, by omega, 0, by omega, by show (V (664 + 12)).limb 0 * _ = _; rw [hl12]⟩
    · exact Or.inr ⟨31, by omega, 1, by omega, by show (V (664 + 12)).limb 0 * _ = _; rw [hl12]⟩
    · exact Or.inr ⟨31, by omega, 2, by omega, by show (V (664 + 12)).limb 0 * _ = _; rw [hl12]⟩
    · exact Or.inr ⟨31, by omega, 3, by omega, by show (V (664 + 12)).limb 0 * _ = _; rw [hl12]⟩

/-- **`child_claims_window` is complete, uniformly placed**, on reads every memory holding the
caller's words makes, at words of those. -/
theorem ccw_completeAt (fs : String → ℕ) (cert : String → V → ℕ) {κ : ℕ} (hκ : 16 ≤ κ) (Lin : Layout)
    {gsq s0 s1 base entries cover marks origin limit xq o0 o1 nxt : E} {L : ℕ} (hL16 : L ≤ 2 ^ 16)
    (hlim : limit = gen ^ L) {N : ℕ} (hN : N < 2 ^ 16) (hxq : xq * gen = gen ^ N) (hnxt : nxt = eOfNat (2 ^ 11 * N))
    {off : ℕ → ℕ} {cs : List E}
    (hR : ∀ rd, LowDef κ rd → MemL rd Lin → ChildReads rd entries cover marks origin limit off cs 32)
    (hsq : ∀ rd, MemL rd Lin → SquaresAt rd gsq)
    (hreg : ∀ A, ChildLoad entries cover origin off 32 A → ∃ i, A = gpow i ∧ RegionL Lin i)
    (hch : ChainCells (s0, s1) (blocksOf cs) (windowMd base nxt) 32 (o0, o1)) :
    CompleteAt fs cert κ "child_claims_window" Lin [s0, s1, base, entries, cover, marks, origin, limit, xq, gsq]
      (Returns [o0, o1, nxt]) := by
  refine completeAt_node find_child_claims_window (by
      rw [Program.loop_of_find? find_child_claims_window]
      simp only [Fn.loop, ccwBody_eq, List.reverse_append]
      rfl) κ Lin _ _ [] (fun _ => []) (fun _ _ h => by obtain ⟨q, hq, _⟩ := h; simp at hq)
    (fun _ q hq => by simp at hq)
    (fun _ => [⟨"scaled_log__L11", true, [xq * word 2 0 0, gsq], Lin, [nxt]⟩])
    (fun _ k hk _ => by
      simp only [List.mem_singleton] at hk
      subst hk
      exact LeanVM.Guest.B1.completeAt_of_rel_pure cldKid_pure (by simp [cldKidSet])
        (fun rd hL => (scaled_log_11_iff (hsq rd hL) _ _).mpr ⟨nxt, rfl, N, hN, by rw [word_gen]; exact hxq, hnxt⟩) κ)
    (fun _ k hk _ i hi => by
      simp only [List.mem_singleton] at hk
      subst hk
      exact Or.inr hi) fun fp rd hl _ hL => ?_
  refine ⟨fun k hk => by simp only [List.mem_singleton] at hk; subst hk; exact hL, ?_⟩
  obtain ⟨σ, hp, hH, h11, h12, hr, hld⟩ := ccw_run (fun i hi => hl i (lt_of_lt_of_le hi (Nat.pow_le_pow_right
    (by norm_num) hκ))) (hsq rd hL) hL16 hlim hN hxq hnxt (hR rd hl hL) hch
  have hw : walk σ ccwBody = .ret (ccwPre.flatMap (Main.slEvs σ)) [.n 683, .n 684, .n 685] := by
    rw [ccwBody_eq]; exact Main.walk_straight σ _ _ ccwPre_straight
  obtain ⟨e1, e2, e3, e4⟩ := Main.straight_parts σ _ ccwPre_straight
  have h9 : σ (.n 9) = gsq := by simp only [List.map_cons, List.map_nil, List.cons.injEq] at hp; exact hp.2.2.2.2.2.2.2.2.2.1
  refine ⟨σ, _, _, hp, hw, hr, holds_of_holdsList find_child_claims_window hH hw, ?_, ?_, ?_, ?_, fun A hA => ?_⟩
  · rw [e4, show ccwPre.filterMap Main.Stmt.callS = [(none, "scaled_log__L11", [.n 11, .n 9], [.n 12])] by
      decide +kernel]
    exact ⟨rfl, rfl, fun _ => ⟨show [σ (.n 11), σ (.n 9)] = _ by rw [h11, h9],
      show [σ (.n 12)] = _ by rw [h12]⟩, trivial⟩
  · rw [e3]; decide +kernel
  · rw [e2, show ccwPre.filterMap Main.Stmt.allocSz = [] by decide +kernel]; rfl
  · rw [e1, show ccwPre.filterMap Main.Stmt.allocSz = [] by decide +kernel]; rfl
  · obtain ⟨i, hi, hRi⟩ := hreg A (hld A hA)
    exact ⟨i, hi, Or.inr hRi⟩

/-- **`child_claims_window` is complete, uniformly placed**, on reads every memory holding the
caller's words makes, at words of those. -/
theorem ccw_completeAtD (fs : String → ℕ) (cert : String → V → ℕ) {κ : ℕ} (hκ : 16 ≤ κ) (Lin : Layout)
    {gsq s0 s1 base entries cover marks origin limit xq o0 o1 nxt : E} {L : ℕ} (hL16 : L ≤ 2 ^ 16)
    (hlim : limit = gen ^ L) {N : ℕ} (hN : N < 2 ^ 16) (hxq : xq * gen = gen ^ N) (hnxt : nxt = eOfNat (2 ^ 11 * N))
    {off : ℕ → ℕ} {cs : List E}
    (hR : ∀ rd, LowDef κ rd → MemL rd Lin → ChildReads rd entries cover marks origin limit off cs 32)
    (hsq : ∀ rd, MemL rd Lin → SquaresAt rd gsq)
    (hreg : ∀ A, ChildLoad entries cover origin off 32 A → ∃ i, A = gpow i ∧ RegionL Lin i)
    (hch : ChainCells (s0, s1) (blocksOf cs) (windowMd base nxt) 32 (o0, o1)) :
    CompleteAtD fs cert κ "child_claims_window" Lin [s0, s1, base, entries, cover, marks, origin, limit, xq, gsq]
      (Returns [o0, o1, nxt]) := by
  refine completeAt_nodeD find_child_claims_window (by
      rw [Program.loop_of_find? find_child_claims_window]
      simp only [Fn.loop, ccwBody_eq, List.reverse_append]
      rfl) κ Lin _ _ [] (fun _ => []) (fun _ _ h => by obtain ⟨q, hq, _⟩ := h; simp at hq)
    (fun _ q hq => by simp at hq) (fun _ => disj_nil)
    (fun _ => [⟨"scaled_log__L11", true, [xq * word 2 0 0, gsq], Lin, [nxt]⟩])
    (fun _ k hk _ => by
      simp only [List.mem_singleton] at hk
      subst hk
      exact LeanVM.Guest.B1.completeAt_of_rel_pureD cldKid_pure (by simp [cldKidSet])
        (fun rd hL => (scaled_log_11_iff (hsq rd hL) _ _).mpr ⟨nxt, rfl, N, hN, by rw [word_gen]; exact hxq, hnxt⟩) κ)
    (fun _ k hk _ i hi => by
      simp only [List.mem_singleton] at hk
      subst hk
      exact Or.inr hi) fun fp rd hl _ hL => ?_
  refine ⟨fun k hk => by simp only [List.mem_singleton] at hk; subst hk; exact hL, ?_⟩
  obtain ⟨σ, hp, hH, h11, h12, hr, hld⟩ := ccw_run (fun i hi => hl i (lt_of_lt_of_le hi (Nat.pow_le_pow_right
    (by norm_num) hκ))) (hsq rd hL) hL16 hlim hN hxq hnxt (hR rd hl hL) hch
  have hw : walk σ ccwBody = .ret (ccwPre.flatMap (Main.slEvs σ)) [.n 683, .n 684, .n 685] := by
    rw [ccwBody_eq]; exact Main.walk_straight σ _ _ ccwPre_straight
  obtain ⟨e1, e2, e3, e4⟩ := Main.straight_parts σ _ ccwPre_straight
  have h9 : σ (.n 9) = gsq := by simp only [List.map_cons, List.map_nil, List.cons.injEq] at hp; exact hp.2.2.2.2.2.2.2.2.2.1
  refine ⟨σ, _, _, hp, hw, hr, holds_of_holdsList find_child_claims_window hH hw, ?_, ?_, ?_, ?_, fun A hA => ?_⟩
  · rw [e4, show ccwPre.filterMap Main.Stmt.callS = [(none, "scaled_log__L11", [.n 11, .n 9], [.n 12])] by
      decide +kernel]
    exact ⟨rfl, rfl, fun _ => ⟨show [σ (.n 11), σ (.n 9)] = _ by rw [h11, h9],
      show [σ (.n 12)] = _ by rw [h12]⟩, trivial⟩
  · rw [e3]; decide +kernel
  · rw [e2, show ccwPre.filterMap Main.Stmt.allocSz = [] by decide +kernel]; rfl
  · rw [e1, show ccwPre.filterMap Main.Stmt.allocSz = [] by decide +kernel]; rfl
  · obtain ⟨i, hi, hRi⟩ := hreg A (hld A hA)
    exact ⟨i, hi, Or.inr hRi⟩


/-- **`child_claims_window` is complete, uniformly placed**, on reads every memory holding the
caller's words makes, at words of those. -/
theorem ccw_completeAtB (fs : String → ℕ) (cert : String → V → ℕ) {κ : ℕ} (hκ : 16 ≤ κ) (Lin : Layout)
    {gsq s0 s1 base entries cover marks origin limit xq o0 o1 nxt : E} {L : ℕ} (hL16 : L ≤ 2 ^ 16)
    (hlim : limit = gen ^ L) {N : ℕ} (hN : N < 2 ^ 16) (hxq : xq * gen = gen ^ N) (hnxt : nxt = eOfNat (2 ^ 11 * N))
    {off : ℕ → ℕ} {cs : List E}
    (hR : ∀ rd, LowDef κ rd → MemL rd Lin → ChildReads rd entries cover marks origin limit off cs 32)
    (hsq : ∀ rd, MemL rd Lin → SquaresAt rd gsq)
    (hreg : ∀ A, ChildLoad entries cover origin off 32 A → ∃ i, A = gpow i ∧ RegionL Lin i)
    (hch : ChainCells (s0, s1) (blocksOf cs) (windowMd base nxt) 32 (o0, o1)) (Bsl : ℕ)
    (hsl : TotalLe coreProgram fs "scaled_log__L11" fun _ => Bsl) :
    CompleteAtB fs cert κ "child_claims_window" Lin [s0, s1, base, entries, cover, marks, origin, limit, xq, gsq]
      (Returns [o0, o1, nxt]) (fs "child_claims_window" + Bsl) := by
  refine completeAt_nodeB find_child_claims_window (by
      rw [Program.loop_of_find? find_child_claims_window]
      simp only [Fn.loop, ccwBody_eq, List.reverse_append]
      rfl) κ Lin _ _ [] (fun _ => []) (fun _ _ h => by obtain ⟨q, hq, _⟩ := h; simp at hq)
    (fun _ q hq => by simp at hq) (fun _ => disj_nil)
    (fun _ => [⟨"scaled_log__L11", true, [xq * word 2 0 0, gsq], Lin, [nxt]⟩]) (fun _ => Bsl)
    (fun _ k hk _ => by
      simp only [List.mem_singleton] at hk
      subst hk
      exact LeanVM.Guest.B1.completeAt_of_rel_pureB cldKid_pure (by simp [cldKidSet])
        (fun rd hL => (scaled_log_11_iff (hsq rd hL) _ _).mpr ⟨nxt, rfl, N, hN, by rw [word_gen]; exact hxq, hnxt⟩) κ hsl)
    (fun _ k hk _ i hi => by
      simp only [List.mem_singleton] at hk
      subst hk
      exact Or.inr hi) _ (fun _ => by simp [kidsBound, KidR.kid]) fun fp rd hl _ hL => ?_
  refine ⟨fun k hk => by simp only [List.mem_singleton] at hk; subst hk; exact hL, ?_⟩
  obtain ⟨σ, hp, hH, h11, h12, hr, hld⟩ := ccw_run (fun i hi => hl i (lt_of_lt_of_le hi (Nat.pow_le_pow_right
    (by norm_num) hκ))) (hsq rd hL) hL16 hlim hN hxq hnxt (hR rd hl hL) hch
  have hw : walk σ ccwBody = .ret (ccwPre.flatMap (Main.slEvs σ)) [.n 683, .n 684, .n 685] := by
    rw [ccwBody_eq]; exact Main.walk_straight σ _ _ ccwPre_straight
  obtain ⟨e1, e2, e3, e4⟩ := Main.straight_parts σ _ ccwPre_straight
  have h9 : σ (.n 9) = gsq := by simp only [List.map_cons, List.map_nil, List.cons.injEq] at hp; exact hp.2.2.2.2.2.2.2.2.2.1
  refine ⟨σ, _, _, hp, hw, hr, holds_of_holdsList find_child_claims_window hH hw, ?_, ?_, ?_, ?_, fun A hA => ?_⟩
  · rw [e4, show ccwPre.filterMap Main.Stmt.callS = [(none, "scaled_log__L11", [.n 11, .n 9], [.n 12])] by
      decide +kernel]
    exact ⟨rfl, rfl, fun _ => ⟨show [σ (.n 11), σ (.n 9)] = _ by rw [h11, h9],
      show [σ (.n 12)] = _ by rw [h12]⟩, trivial⟩
  · rw [e3]; decide +kernel
  · rw [e2, show ccwPre.filterMap Main.Stmt.allocSz = [] by decide +kernel]; rfl
  · rw [e1, show ccwPre.filterMap Main.Stmt.allocSz = [] by decide +kernel]; rfl
  · obtain ⟨i, hi, hRi⟩ := hreg A (hld A hA)
    exact ⟨i, hi, Or.inr hRi⟩

end
end LeanVM.Guest.B1.Digest
