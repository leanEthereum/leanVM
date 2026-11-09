/-
  LeanVM.Guest.B1.Da.LevelsComplete

  `da_levels`, completely: a tree's levels in memory give each specialization's relation, its
  returns the root's cells (TRIAGE G #92).
-/

module

public import LeanVM.Guest.B1.Da.LevelsCChk0
public import LeanVM.Guest.B1.Da.LevelsCChk1
public import LeanVM.Guest.B1.Da.LevelsCChk2
public import LeanVM.Guest.B1.Da.LevelsCChk3
public import LeanVM.Guest.B1.Da.LevelsCChk4
public import LeanVM.Guest.B1.Da.LevelsCChk5
public import LeanVM.Guest.B1.Da.LevelsCChk6
public import LeanVM.Guest.B1.Da.LevelsSound
public import LeanVM.Guest.B1.Digest.LoopComplete
public import LeanVM.Guest.B1.Digest.PairComplete
public import LeanVM.Guest.B1.Digest.ListsComplete

/-!
# `da_levels`, completely

* the tree: `treeLvl_succ`, `length_treeLvl`, `cellRoot_treeLvl` (the root is the last level's
  node), the internal levels' cells canonical (digests);
* `lvl_block`: a level loop's block holds at every node of its level, on the evaluated valuation
  (`Fwd.ev`): its four loads read the level's cells, its pair hash is the next level's node
  (`chain_final`), which its two stores find in memory;
* `dl_complete`: a specialization holds, its guarded loops running to their ends
  (`guard_complete`), its returns the root's cells;
* `da_levels_complete : da_levels_complete_Spec`.
-/

namespace LeanVM.Guest.B1.Da

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Value.Keccak
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Guest.B1.Digest LeanVM.Guest.B1.Main LeanVM.Guest.B1.Fwd

@[expose] public section

variable {rd : Reader}

/-- `da_levels`' meaning, for a tree whose levels are in memory, gives its core IR. -/
def da_levels_complete_Spec : Prop :=
  ∀ k ≤ 10, ∀ (rd : Reader) (tree : E) (leaves : List (E × E)), leaves.length = 2 ^ k →
    (0 < k → AllCanonical (pairCells leaves)) → TreeMem rd tree k leaves →
      coreProgram.Rel rd (daLevelsName k) [tree] [(cellRoot k leaves).1, (cellRoot k leaves).2]

/-! ## The tree -/

theorem treeLvl_succ (leaves : List (E × E)) (l : ℕ) :
    treeLvl leaves (l + 1) = cellLevel (treeLvl leaves l) :=
  Function.iterate_succ_apply' _ _ _

theorem length_cellLevel (nodes : List (E × E)) : (cellLevel nodes).length = nodes.length / 2 := by
  simp [cellLevel]

theorem length_treeLvl {leaves : List (E × E)} {k : ℕ} (h : leaves.length = 2 ^ k) :
    ∀ l ≤ k, (treeLvl leaves l).length = 2 ^ (k - l)
  | 0, _ => by simp [treeLvl, h]
  | l + 1, hl => by
    rw [treeLvl_succ, length_cellLevel, length_treeLvl h l (by omega),
      show k - l = (k - (l + 1)) + 1 by omega, pow_succ, Nat.mul_div_cancel _ (by norm_num)]

theorem cellLevel_getD {nodes : List (E × E)} {p : ℕ} (hp : p < nodes.length / 2) :
    (cellLevel nodes).getD p 0 = nodeCells (nodes.getD (2 * p) 0) (nodes.getD (2 * p + 1) 0) := by
  simp [cellLevel, List.getD_eq_getElem?_getD, hp]

theorem cellRoot_treeLvl : ∀ (k : ℕ) (nodes : List (E × E)), cellRoot k nodes = (treeLvl nodes k).headD 0
  | 0, _ => rfl
  | k + 1, nodes => by
    rw [cellRoot, cellRoot_treeLvl k, treeLvl, treeLvl, Function.iterate_succ_apply]

theorem pairCells_getD' : ∀ (l : List (E × E)) (i : ℕ),
    (pairCells l).getD (2 * i) 0 = (l.getD i 0).1 ∧ (pairCells l).getD (2 * i + 1) 0 = (l.getD i 0).2
  | [], _ => by simp [pairCells]
  | p :: l, 0 => by simp [pairCells]
  | p :: l, i + 1 => by
    have ih := pairCells_getD' l i
    simp only [pairCells, List.flatMap_cons, List.cons_append, List.nil_append] at ih ⊢
    rw [show 2 * (i + 1) = 2 * i + 1 + 1 by ring, List.getD_cons_succ, List.getD_cons_succ,
      List.getD_cons_succ, List.getD_cons_succ, List.getD_cons_succ]
    exact ih

theorem length_pairCells (l : List (E × E)) : (pairCells l).length = 2 * l.length := by
  simp [pairCells, List.length_flatMap, mul_comm]

/-- The cells of an internal level are canonical: digests. -/
theorem canon_level_succ (leaves : List (E × E)) (l : ℕ) :
    AllCanonical (pairCells (treeLvl leaves (l + 1))) := by
  intro c hc
  rw [treeLvl_succ] at hc
  simp only [pairCells, cellLevel, List.mem_flatMap, List.mem_map, List.mem_range] at hc
  obtain ⟨_, ⟨i, -, rfl⟩, hc⟩ := hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl
  · exact (digestScalars_canonical _).1
  · exact (digestScalars_canonical _).2

theorem canon_level {leaves : List (E × E)} {k l : ℕ} (hk : 0 < k → AllCanonical (pairCells leaves))
    (hl : l < k) : AllCanonical (pairCells (treeLvl leaves l)) := by
  rcases l with _ | l
  · exact hk (by omega)
  · exact canon_level_succ leaves l

/-- A cell of a level, read from memory. -/
theorem treeMem_load {tree : E} {k : ℕ} {leaves : List (E × E)} (hlen : leaves.length = 2 ^ k)
    (h : TreeMem rd tree k leaves) {l : ℕ} (hl : l ≤ k) {i : ℕ} (hi : i < 2 * 2 ^ (k - l)) :
    LoadHolds rd (tree * gen ^ off k l) i ((pairCells (treeLvl leaves l)).getD i 0) := by
  have hL : (pairCells (treeLvl leaves l)).length = 2 * 2 ^ (k - l) := by
    rw [length_pairCells, length_treeLvl hlen l hl]
  have := h l hl i (by omega)
  rwa [List.getD_eq_getElem _ _ (by omega)]

theorem shiftC {p v : E} {a c j i : ℕ} :
    LoadHolds rd (p * gen ^ a * (gen ^ j) ^ c) i v ↔ LoadHolds rd (p * gen ^ a) (c * j + i) v := by
  rw [← pow_mul, loadHolds_mul_gen_pow, mul_comm j c]

/-! ## A level loop -/

theorem loopPre_mem {fn : Fn} {s : Stmt} (h : s ∈ loopPre fn) : s ∈ fn.body := by
  unfold loopPre at h
  cases hs : splitLoopF fn.body with
  | none => simp [hs] at h
  | some q =>
    obtain ⟨pre, c, g, args⟩ := q
    rw [hs] at h
    rw [(splitLoopF_eq hs).1]
    exact List.mem_append_left _ (by simpa using h)

theorem atom_mem_of_atomsIn {ss : List Stmt} {a : Atom} (h : a ∈ atomsIn ss) : Stmt.atom a ∈ ss := by
  obtain ⟨s, hs, hsa⟩ := List.mem_filterMap.mp h
  cases s <;> simp only [reduceCtorEq, Option.some.injEq] at hsa
  subst hsa
  exact hs

theorem mem_atomsIn {ss : List Stmt} {a : Atom} (h : Stmt.atom a ∈ ss) : a ∈ atomsIn ss :=
  List.mem_filterMap.mpr ⟨_, h, rfl⟩

/-- **A level loop's block holds** at node `p` of its level. -/
theorem lvl_block {f : String} {fn : Fn}
    {k lvl : ℕ} (hl : lvl < k) (hk : k ≤ 10) {pa pb c0 : ℕ} (hpab : pa ≠ pb)
    (hshape : loopShapeF fn f = true) (hplen : fn.params.length = 3)
    (hld : ∀ i < 4, (atomsIn (loopPre fn)).any (isLoadAt (.n (c0 + i)) (.n pa) i) = true)
    (hatoms : (loopPre fn).all (fun s => match s with | .atom _ => true | _ => false) = true)
    {c' : ℕ} (hchk : chk 3 fn.body = some c')
    (hcan : canonChk ((List.range 4).map (c0 + ·)) (lvlA' fn) = true)
    (hneeds : (atomsIn (loopPre fn)).all (fun a => !needsSide a ||
      decide (a ∈ storesOf 3 fn.body) || isLoadVia (.n pa) c0 a) = true)
    (hS : storesOf 3 fn.body = [.load ((lvlSp fn c0).outV ((lvlSp fn c0).nb - 1) 0) (.n pb) 0,
      .load ((lvlSp fn c0).outV ((lvlSp fn c0).nb - 1) 1) (.n pb) 1])
    (hpa : ptrOk ((atomsIn (loopPre fn)).filter pureB) (.n pa) (.n 2) (.n 0) (off k lvl) 4 = true)
    (hpb : ptrOk ((atomsIn (loopPre fn)).filter pureB) (.n pb) (.n 2) (.n 0) (off k (lvl + 1)) 2 =
      true)
    (hsp : (lvlSp fn c0).check (lvlA' fn) = true)
    {tree : E} {leaves : List (E × E)} (hlen : leaves.length = 2 ^ k)
    (hcl : 0 < k → AllCanonical (pairCells leaves)) (hmem : TreeMem rd tree k leaves)
    {p : ℕ} (hp : p < 2 ^ (k - lvl - 1)) :
    LoopBlock rd fn (gen ^ p) (gen ^ 2 ^ (k - lvl - 1)) [tree] := by
  set A := atomsIn (loopPre fn) with hAdef
  set S := storesOf 3 fn.body
  let args : List E := [gen ^ p, gen ^ 2 ^ (k - lvl - 1), tree]
  let σ : Val := B1.Val.ofArgs (ev rd (fun _ => 0) args fn.body)
  obtain ⟨-, -, hgs⟩ := ev_spec rd (fun _ => 0) fn.body args hchk
  have hg : ∀ a ∈ A, Good rd S (fun _ => 0) σ a := fun a ha =>
    hgs (.atom a) (loopPre_mem (atom_mem_of_atomsIn ha))
  have hpar : fn.params = [.n 0, .n 1, .n 2] := by
    have hs := hshape
    simp only [loopShapeF, Bool.and_eq_true, decide_eq_true_eq] at hs
    rw [hs.1.2, hplen]; rfl
  have e0 : σ (.n 0) = gen ^ p := ev_params rd _ (l := args) hchk (by simp [args])
  have e2 : σ (.n 2) = tree := ev_params rd _ (l := args) hchk (by simp [args])
  have hpure := pure_holds hg
  have hσa : σ (.n pa) = tree * gen ^ off k lvl * (gen ^ p) ^ 4 := by
    rw [ptr_sound hpa hpure (off_lt hk), e0, e2]
  have hσb : σ (.n pb) = tree * gen ^ off k (lvl + 1) * (gen ^ p) ^ 2 := by
    rw [ptr_sound hpb hpure (off_lt hk), e0, e2]
  -- the level's cells
  set L := treeLvl leaves lvl with hLdef
  have hLlen : L.length = 2 ^ (k - lvl) := length_treeLvl hlen lvl (by omega)
  have h2 : 2 ^ (k - lvl) = 2 * 2 ^ (k - lvl - 1) := by
    rw [← pow_succ']; congr 1; omega
  have hcell : ∀ i < 4, LoadHolds rd (σ (.n pa)) i ((pairCells L).getD (4 * p + i) 0) := by
    intro i hi
    rw [hσa, shiftC]
    exact treeMem_load hlen hmem (by omega) (by omega)
  -- the loads' values
  have hv : ∀ i < 4, σ (.n (c0 + i)) = (pairCells L).getD (4 * p + i) 0 := by
    intro i hi
    obtain ⟨a, ha, hp'⟩ := List.any_eq_true.mp (hld i hi)
    cases a <;> simp only [isLoadAt, Bool.false_eq_true, Bool.and_eq_true, decide_eq_true_eq,
      beq_iff_eq] at hp'
    obtain ⟨⟨rfl, rfl⟩, rfl⟩ := hp'
    rcases (hg _ ha : Good rd S _ σ (.load _ _ _)) with h | h
    · rw [hS] at h
      simp only [List.mem_cons, Atom.load.injEq, List.not_mem_nil, or_false] at h
      exfalso
      rcases h with ⟨-, h, -⟩ | ⟨-, h, -⟩ <;> exact hpab (by simpa using h)
    · rw [h, rdAt_of_load (hcell _ hi)]
  -- the non-store atoms, then the stores
  have hat : ∀ a ∈ A, a.Holds rd σ := by
    refine atoms_holds_stores (S := S) (w := fun _ => 0) (fun v => rfl) hcan hg ?_ ?_ ?_
    · intro i hi
      obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hi
      have hj' := List.mem_range.mp hj
      rw [hv j hj']
      have hcl' := canon_level hcl (k := k) (l := lvl) hl
      have hlt : 4 * p + j < (pairCells L).length := by
        rw [length_pairCells, hLlen, h2]; omega
      rw [List.getD_eq_getElem _ _ hlt]
      exact hcl' _ (List.getElem_mem _)
    · intro a ha hnS hns
      have := List.all_eq_true.mp hneeds a ha
      simp only [hns, Bool.not_true, Bool.false_or, Bool.or_eq_true, decide_eq_true_eq] at this
      rcases this with h | h
      · exact absurd h hnS
      · refine Or.inl ?_
        cases a <;> simp only [isLoadVia, Bool.false_eq_true, Bool.and_eq_true,
          decide_eq_true_eq] at h
        obtain ⟨⟨rfl, rfl⟩, hi⟩ := h
        show LoadHolds rd (σ (.n pa)) _ (σ (.n (c0 + _)))
        rw [hv _ hi]
        exact hcell _ hi
    · intro h1 a ha haS
      have hA' : ∀ b ∈ lvlA' fn, b.Holds rd σ := fun b hb =>
        h1 b (List.mem_filter.mp hb).1 (by simpa using (List.mem_filter.mp hb).2)
      obtain ⟨hd, -⟩ := chain_final hsp rfl hA' (pre := []) (n := 0) rfl
        (fun c => (cellsOfState_zero false c).symm)
      have hvals : ((lvlSp fn c0).vals σ).take ((lvlSp fn c0).len / 16) =
          [σ (.n c0), σ (.n (c0 + 1)), σ (.n (c0 + 2)), σ (.n (c0 + 3))] := by
        simp [lvlSp, pairSpec, ChainSpec.vals, srcVal]
      rw [hvals, List.nil_append] at hd
      have hv0 := hv 0 (by omega)
      rw [Nat.add_zero] at hv0
      rw [hv0, hv 1 (by omega), hv 2 (by omega), hv 3 (by omega)] at hd
      obtain ⟨q0, q1⟩ := pairCells_getD' L (2 * p)
      obtain ⟨q2, q3⟩ := pairCells_getD' L (2 * p + 1)
      rw [show 4 * p + 0 = 2 * (2 * p) by ring, show 4 * p + 1 = 2 * (2 * p) + 1 by ring,
        show 4 * p + 2 = 2 * (2 * p + 1) by ring, show 4 * p + 3 = 2 * (2 * p + 1) + 1 by ring,
        q0, q1, q2, q3] at hd
      -- the next level's node
      have hnext : (treeLvl leaves (lvl + 1)).getD p 0 =
          nodeCells (L.getD (2 * p) 0) (L.getD (2 * p + 1) 0) := by
        rw [treeLvl_succ, cellLevel_getD (by rw [hLlen, h2]; omega)]
      have hd' : (σ ((lvlSp fn c0).outV ((lvlSp fn c0).nb - 1) 0),
          σ ((lvlSp fn c0).outV ((lvlSp fn c0).nb - 1) 1)) = (treeLvl leaves (lvl + 1)).getD p 0 := by
        rw [hnext, hd]; rfl
      have hlen1 : 2 * p + 1 < 2 * 2 ^ (k - (lvl + 1)) := by
        rw [show k - (lvl + 1) = k - lvl - 1 by omega]; omega
      obtain ⟨r0, r1⟩ := pairCells_getD' (treeLvl leaves (lvl + 1)) p
      have o0 : σ ((lvlSp fn c0).outV ((lvlSp fn c0).nb - 1) 0) =
          ((treeLvl leaves (lvl + 1)).getD p 0).1 := congrArg Prod.fst hd'
      have o1 : σ ((lvlSp fn c0).outV ((lvlSp fn c0).nb - 1) 1) =
          ((treeLvl leaves (lvl + 1)).getD p 0).2 := congrArg Prod.snd hd'
      rw [hS] at haS
      simp only [List.mem_cons, List.not_mem_nil, or_false] at haS
      rcases haS with rfl | rfl
      · show LoadHolds rd (σ (.n pb)) 0 _
        rw [hσb, shiftC, Nat.add_zero, o0, ← r0]
        exact treeMem_load hlen hmem (by omega) (by omega)
      · show LoadHolds rd (σ (.n pb)) 1 _
        rw [hσb, shiftC, o1, ← r1]
        exact treeMem_load hlen hmem (by omega) hlen1
  refine ⟨σ, ?_, fun s hs => ?_⟩
  · rw [hpar]
    simp only [List.map_cons, List.map_nil]
    have e1 : σ (.n 1) = gen ^ 2 ^ (k - lvl - 1) := ev_params rd _ (l := args) hchk (by simp [args])
    rw [e0, e1, e2]
  · have := List.all_eq_true.mp hatoms s hs
    cases s <;> simp only [Bool.false_eq_true] at this
    rename_i a
    exact ⟨hat a (mem_atomsIn hs), trivial⟩

/-! ## A specialization -/

theorem headD_eq_getD (l : List (E × E)) : l.headD 0 = l.getD 0 0 := by cases l <;> rfl

/-- **A checked specialization is complete.** -/
theorem dl_complete {k : ℕ} (hk : k ≤ 10) (hok : dlEntryOk k = true) (hcok : dlCEntryOk k = true)
    (rd : Reader) (tree : E) (leaves : List (E × E)) (hlen : leaves.length = 2 ^ k)
    (hcl : 0 < k → AllCanonical (pairCells leaves)) (hmem : TreeMem rd tree k leaves) :
    coreProgram.Rel rd (daLevelsName k) [tree] [(cellRoot k leaves).1, (cellRoot k leaves).2] := by
  unfold dlEntryOk at hok
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range] at hok
  obtain ⟨⟨⟨⟨⟨-, hname⟩, hidx⟩, hlt⟩, hdl⟩, hloops⟩ := hok
  unfold dlCEntryOk at hcok
  simp only [Bool.and_eq_true, Option.isSome_iff_exists, List.isEmpty_iff, List.all_eq_true,
    List.mem_range] at hcok
  obtain ⟨⟨⟨⟨c', hchk⟩, hst⟩, hbody⟩, hcloops⟩ := hcok
  set e := dlTab.getD k (0, "", 0, [])
  set fn := coreProgram.getD e.2.2.1 default
  have hf := find_of_idx hidx hlt
  rw [← hname]
  unfold dlOk at hdl
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hdl
  obtain ⟨⟨hparams, -⟩, hdl⟩ := hdl
  split at hdl
  · rename_i P vs hsr
    rw [hsr] at hbody
    simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range,
      Bool.or_eq_true] at hdl hbody
    obtain ⟨⟨⟨⟨rfl, -⟩, hguards⟩, hr0⟩, hr1⟩ := hdl
    obtain ⟨⟨hcan, hneeds⟩, hcalls⟩ := hbody
    have hb := splitRet_eq hsr
    let σ : Val := B1.Val.ofArgs (ev rd (fun _ => 0) [tree] fn.body)
    obtain ⟨-, -, hgs⟩ := ev_spec rd (fun _ => 0) fn.body [tree] hchk
    rw [show [tree].length = 1 from rfl, hst] at hgs
    have hg : ∀ a ∈ atomsIn P, Good rd [] (fun _ => 0) σ a := fun a ha =>
      hgs (.atom a) (by rw [hb]; exact List.mem_append_left _ (atom_mem_of_atomsIn ha))
    have e0 : σ (.n 0) = tree := ev_params rd _ (l := [tree]) hchk (by simp)
    have h2k : 1 ≤ 2 ^ k := Nat.one_le_two_pow
    -- the root's cells
    have hroot : ∀ i < 2, LoadHolds rd tree (4 * 2 ^ k - 4 + i)
        ((pairCells (treeLvl leaves k)).getD i 0) := by
      intro i hi
      have := treeMem_load hlen hmem (l := k) le_rfl (i := i) (by simp; omega)
      rwa [off_self, loadHolds_mul_gen_pow] at this
    have hval : ∀ (x : V) (o i : ℕ), i < 2 → o = 4 * 2 ^ k - 4 + i →
        (atomsIn P).any (isLoadAt x (.n 0) o) = true → σ x = (pairCells (treeLvl leaves k)).getD i 0 := by
      intro x o i hi ho hx
      rw [good_load_of_any rfl hg hx, e0, ho, rdAt_of_load (hroot i hi)]
    have v0 := hval _ _ 0 (by omega) rfl hr0
    have v1 := hval _ _ 1 (by omega) (by omega) hr1
    have hat : ∀ a ∈ atomsIn P, a.Holds rd σ := by
      refine atoms_holds (fun v => rfl) hcan hg (fun i hi => absurd hi (by simp)) fun a ha hns => ?_
      refine Or.inl ?_
      rcases hneeds a ha with (h | h) | h
      · rw [hns] at h; exact absurd h (by simp)
      all_goals
        cases a <;> simp only [isLoadAt, Bool.false_eq_true, Bool.and_eq_true, decide_eq_true_eq,
          beq_iff_eq] at h
        obtain ⟨⟨rfl, rfl⟩, rfl⟩ := h
      · show LoadHolds rd (σ (.n 0)) _ (σ (.n (5 * k + 1)))
        rw [v0, e0]; exact hroot 0 (by omega)
      · show LoadHolds rd (σ (.n 0)) _ (σ (.n (5 * k + 2)))
        rw [v1, e0, show 4 * 2 ^ k - 3 = 4 * 2 ^ k - 4 + 1 by omega]; exact hroot 1 (by omega)
    -- the guarded loops
    have hcall : ∀ lvl < k, SHolds (coreProgram.Rel rd) rd σ (lvlCall lvl (e.2.2.2.getD lvl "")) := by
      intro lvl hl
      have hg' := hguards lvl hl
      have hlo := hloops lvl hl
      have hclo := hcloops lvl hl
      unfold loopOk at hlo
      unfold loopCOk at hclo
      split at hlo
      · rename_i j hj
        rw [hj] at hclo
        simp only [Bool.and_eq_true, decide_eq_true_eq] at hlo
        obtain ⟨hjl, hlok⟩ := hlo
        have hfl := find_of_idx hj hjl
        simp only [guardPowOk, Bool.and_eq_true] at hg'
        obtain ⟨⟨⟨-, ha⟩, h1⟩, hN⟩ := hg'
        split at ha
        · rename_i pp qq hpq
          simp only [Bool.and_eq_true] at ha
          have hm : 2 ^ (k - lvl - 1) < 2 ^ 64 := by
            have : 2 ^ (k - lvl - 1) ≤ 2 ^ 10 := Nat.pow_le_pow_right (by norm_num) (by omega)
            omega
          have hgc : σ (.n (5 * lvl + 3)) = 1 + gen ^ 2 ^ (k - lvl - 1) := by
            rw [addOf_sound hpq hat, const_sound ha.1 hat, word_one, constPow_sound ha.2 hat hm]
          have hone : σ (.n (5 * lvl + 4)) = 1 := by rw [const_sound h1 hat, word_one]
          have hNv : σ (.n (5 * lvl + 5)) = gen ^ 2 ^ (k - lvl - 1) := constPow_sound hN hat hm
          simp only [lvlOk, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true,
            List.mem_range] at hlok
          obtain ⟨⟨⟨⟨⟨hshape, hplen⟩, hld⟩, -⟩, -⟩, -⟩ := hlok
          simp only [lvlCOk, Bool.and_eq_true, Option.isSome_iff_exists, decide_eq_true_eq] at hclo
          obtain ⟨⟨⟨⟨⟨⟨⟨⟨c2, hchk2⟩, hatoms⟩, hcan2⟩, hneeds2⟩, hS2⟩, hpa⟩, hpb⟩, hsp⟩ := hclo
          have hgd := guard_complete hfl hshape (rest := [tree]) (m := 2 ^ (k - lvl - 1))
            (fun p hp => lvl_block hl hk (by split <;> decide) hshape hplen hld hatoms hchk2
              hcan2 hneeds2 hS2 hpa hpb hsp hlen hcl hmem hp)
          show IsInK (σ (.n (5 * lvl + 3))) ∧ (σ (.n (5 * lvl + 3)) ≠ 0 →
            coreProgram.Rel rd (e.2.2.2.getD lvl "") [σ (.n (5 * lvl + 4)), σ (.n (5 * lvl + 5)),
              σ (.n 0)] [])
          rw [hgc, hone, hNv, e0]
          exact hgd
        · exact absurd ha (by simp)
      · exact absurd hlo (by simp)
    refine (rel_iff_sem hf _ _).mpr ⟨σ, by rw [hparams]; simp [e0], ?_⟩
    rw [hb]
    refine holdsList_straight P _ _ _ (fun s hs => ?_) ?_
    · have := hcalls s hs
      cases s <;> simp only [Bool.false_eq_true] at this
      · exact hat _ (mem_atomsIn hs)
      · rename_i c g args
        obtain ⟨lvl, hl, heq⟩ := List.any_eq_true.mp this
        rw [stmtEqb_sound heq]
        exact hcall lvl (List.mem_range.mp hl)
    · show [σ (.n (5 * k + 1)), σ (.n (5 * k + 2))] = _
      rw [v0, v1, cellRoot_treeLvl, headD_eq_getD]
      obtain ⟨q0, q1⟩ := pairCells_getD' (treeLvl leaves k) 0
      simp only [Nat.mul_zero, Nat.zero_add] at q0 q1
      rw [q0, q1]
  · exact absurd hdl (by simp)

/-- **`da_levels` is complete.** -/
theorem da_levels_complete : da_levels_complete_Spec := by
  intro k hk
  interval_cases k
  · exact dl_complete (by omega) dl_ok0 dlc_ok0
  · exact dl_complete (by omega) dl_ok1 dlc_ok1
  · exact dl_complete (by omega) dl_ok2 dlc_ok2
  · exact dl_complete (by omega) dl_ok3 dlc_ok3
  · exact dl_complete (by omega) dl_ok4 dlc_ok4
  · exact dl_complete (by omega) dl_ok5 dlc_ok5
  · exact dl_complete (by omega) dl_ok6 dlc_ok6
  · exact dl_complete (by omega) dl_ok7 dlc_ok7
  · exact dl_complete (by omega) dl_ok8 dlc_ok8
  · exact dl_complete (by omega) dl_ok9 dlc_ok9
  · exact dl_complete (by omega) dl_ok10 dlc_ok10

end
end LeanVM.Guest.B1.Da
