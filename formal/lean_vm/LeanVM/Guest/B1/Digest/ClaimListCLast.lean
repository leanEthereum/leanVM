/-
  LeanVM.Guest.B1.Digest.ClaimListCLast

  `claim_list_last__L{k}` and a frame loop's block, completely.
-/

module

public import LeanVM.Guest.B1.Digest.ClaimListCChk
public import LeanVM.Guest.B1.Digest.ChainFilter
public import LeanVM.Guest.B1.Digest.PairComplete

/-!
# The last claims and a group of claims, completely

`claimLast_complete`: from a state at `sp` after whole blocks `pre` and `4k` canonical cells at
`blk`, `claim_list_last__L{k}` returns the digest of `pre ++` the cells: its evaluated valuation
(`Fwd.ev`) loads them, every atom holds (`Fwd.atoms_holds`), and soundness (`claimLast_sound`)
names the returns. `grp_block`: a frame loop's block (`m` claims) at the counter `x` holds when
the state after `pre` is at `chain · x^13`, the `4m` cells at `entries · x^(4m)`, and the state
after them at offset `13` (its stores, `chain_whole` on the block without them, `check_filter`).
-/

namespace LeanVM.Guest.B1.Digest

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Value.Keccak
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Guest.B1.Fwd

@[expose] public section

variable {rd : Reader}

theorem clc_all {k : ℕ} (hk : k < 17) : clcOk k (coreProgram.getD (361 + k) default) = true := by
  rcases Nat.lt_or_ge k 9 with h | h
  · exact clc_lo k h
  · have := clc_hi (k - 9) (by omega)
    rwa [show 9 + (k - 9) = k by omega, show 370 + (k - 9) = 361 + k by omega] at this

/-- A load found in the atoms, not a store, reads memory. -/
theorem load_val {S : List Atom} {w : ℕ → E} {σ : Val} {atoms : List Atom} {x p : V} {o : ℕ}
    (h : atoms.any (isLoadAt x p o) = true) (hg : ∀ a ∈ atoms, Good rd S w σ a)
    (hS : Atom.load x p o ∉ S) : σ x = rdAt rd (σ p) o := by
  obtain ⟨a, ha, hp⟩ := List.any_eq_true.mp h
  cases a <;> simp only [isLoadAt, Bool.false_eq_true, Bool.and_eq_true, decide_eq_true_eq,
    beq_iff_eq] at hp
  obtain ⟨⟨rfl, rfl⟩, rfl⟩ := hp
  rcases hg _ ha with h' | h'
  · exact absurd h' hS
  · exact h'

/-- A load, not a store, of a word in memory holds. -/
theorem load_holds_of {S : List Atom} {w : ℕ → E} {σ : Val} {d p : V} {o : ℕ} {v : E}
    (hS : Atom.load d p o ∉ S) (hg : Good rd S w σ (.load d p o)) (hv : LoadHolds rd (σ p) o v) :
    (Atom.load d p o).Holds rd σ := by
  rcases hg with h | h
  · exact absurd h hS
  · show LoadHolds rd (σ p) o (σ d)
    rw [h, rdAt_of_load hv]; exact hv

theorem cl_cells_unique {blk : E} {cells cells' : List E} (h : ReadsAt rd blk cells)
    (h' : ReadsAt rd blk cells') (hl : cells.length = cells'.length) : cells' = cells := by
  rw [readsAt_memRun h, readsAt_memRun h', hl]

set_option maxRecDepth 20000 in
/-- **`claim_list_last__L{k}` is complete**: from the state after whole blocks `pre` at `sp` and
`4k` cells at `blk`, it returns the digest of `pre ++` the cells. -/
theorem claimLast_complete {k : ℕ} (hk : k < 17) {sp blk : E} {n : ℕ} {pre : List UInt8}
    (hpre : pre.length = rate * n) (hS : StateAt rd sp 0 (absorbChunks n zeroState pre))
    {cells : List E} (hl : cells.length = 4 * k) (hr : ReadsAt rd blk cells) :
    coreProgram.Rel rd (clNames.getD k "") [sp, blk]
      (digestCells (keccak256 (pre ++ cellsBytes cells))) := by
  have hf := find_of_idx (cl_idx k hk) (by rw [coreProgram_length]; omega)
  have hok := cl_all k hk
  have hcok := clc_all hk
  set fn := coreProgram.getD (361 + k) default
  simp only [clOk, Bool.and_eq_true, decide_eq_true_eq] at hok
  obtain ⟨hpar, hok⟩ := hok
  simp only [clcOk, Bool.and_eq_true, Option.isSome_iff_exists, List.isEmpty_iff] at hcok
  obtain ⟨⟨⟨c', hchk⟩, hS0⟩, hcok⟩ := hcok
  split at hok
  · rename_i atoms r0 r1 hsb
    rw [hsb] at hcok
    simp only [Bool.and_eq_true, List.all_eq_true, Bool.or_eq_true, Bool.not_eq_true'] at hok hcok
    obtain ⟨⟨⟨-, -⟩, hl1⟩, hst⟩ := hok
    have hneeds := hcok
    let args : List E := [sp, blk]
    obtain ⟨σ, hσ⟩ : ∃ σ : Val, σ = B1.Val.ofArgs (ev rd (fun _ => 0) args fn.body) := ⟨_, rfl⟩
    obtain ⟨-, -, hgs⟩ := ev_spec rd (fun _ => 0) fn.body args hchk
    rw [show args.length = 2 from rfl, hS0, ← hσ] at hgs
    have hbody := splitBody_eq hsb
    have hg : ∀ a ∈ atoms, Good rd [] (fun _ => 0) σ a := fun a ha =>
      hgs (.atom a) (by rw [hbody]; exact List.mem_append_left _ (List.mem_map_of_mem ha))
    have e0 : σ (.n 0) = sp := by rw [hσ]; exact ev_params rd _ (l := args) hchk (by simp [args])
    have e1 : σ (.n 1) = blk := by rw [hσ]; exact ev_params rd _ (l := args) hchk (by simp [args])
    have vst : ∀ c : Fin 13, σ ((clSt k).getD c default) =
        cellsOfState (absorbChunks n zeroState pre) false c := by
      intro c
      simp only [stLoadsOk, Bool.and_eq_true, List.all_eq_true, List.mem_range] at hst
      rw [load_val (hst.2 c c.isLt) hg (by simp), e0, rdAt_of_load (hS c)]
    have vc : ∀ i < 4 * k, σ (.n (i + 2)) = cells.getD i 0 := by
      intro i hi
      simp only [loadsOk, List.all_eq_true, List.mem_range] at hl1
      have := hl1 i (by simp [clSpec]; omega)
      simp only [clSpec, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hi,
        Option.map_some, Option.getD_some] at this
      rw [load_val this hg (by simp), e1, rdAt_of_load (hr i (by omega)),
        List.getD_eq_getElem _ _ (by omega)]
    have hat : ∀ a ∈ atoms, a.Holds rd σ := by
      refine atoms_holds hg fun a ha hn => Or.inl ?_
      rcases hneeds a ha with (h | h) | h
      · rw [hn] at h; exact absurd h (by simp)
      · cases a <;> simp only [isLoadBelow, Bool.false_eq_true, Bool.and_eq_true,
          decide_eq_true_eq] at h
        rename_i d p o
        obtain ⟨rfl, ho⟩ := h
        have hv := hS ⟨o, ho⟩
        rw [Nat.zero_add, ← e0] at hv
        exact load_holds_of (by simp) (hg _ ha) hv
      · cases a <;> simp only [isLoadBelow, Bool.false_eq_true, Bool.and_eq_true,
          decide_eq_true_eq] at h
        rename_i d p o
        obtain ⟨rfl, ho⟩ := h
        have hv := hr o (by omega)
        rw [← e1] at hv
        exact load_holds_of (by simp) (hg _ ha) hv
    have hrel : coreProgram.Rel rd (clNames.getD k "") [sp, blk] [σ r0, σ r1] := by
      refine (rel_iff_sem hf _ _).mpr ⟨σ, ?_, ?_⟩
      · rw [hpar]
        simp only [List.map_cons, List.map_nil, e0, e1]
      · rw [hbody, holdsList_atoms_ret]
        exact ⟨hat, rfl⟩
    obtain ⟨sp', blk', hargs, hlast⟩ := claimLast_sound hk hrel
    simp only [List.cons.injEq, and_true] at hargs
    obtain ⟨rfl, rfl⟩ := hargs
    obtain ⟨cells', hl', hr', hd⟩ := hlast n pre hpre hS
    rw [cl_cells_unique hr hr' (by rw [hl, hl'])] at hd
    rw [← hd]
    exact hrel
  · exact absurd hok (by simp)

theorem cl_pre_mem {fn : Fn} {s : Stmt} (h : s ∈ loopPre fn) : s ∈ fn.body := by
  unfold loopPre at h
  cases hs : splitLoopF fn.body with
  | none => simp [hs] at h
  | some q =>
    obtain ⟨pre, c, g, args⟩ := q
    rw [hs] at h
    rw [(splitLoopF_eq hs).1]
    exact List.mem_append_left _ (by simpa using h)

theorem cl_atom_mem {ss : List Stmt} {a : Atom} (h : a ∈ atomsIn ss) : Stmt.atom a ∈ ss := by
  obtain ⟨s, hs, hsa⟩ := List.mem_filterMap.mp h
  cases s <;> simp only [reduceCtorEq, Option.some.injEq] at hsa
  subst hsa
  exact hs

theorem cl_mem_atoms {ss : List Stmt} {a : Atom} (h : Stmt.atom a ∈ ss) : a ∈ atomsIn ss :=
  List.mem_filterMap.mpr ⟨_, h, rfl⟩

set_option maxRecDepth 20000 in
/-- **A frame of `m` claims** (a frame loop's block at the counter `x`, `grpOk`, `grpcOk`): the
state after whole blocks `pre` at `chain · x^13`, the `4m` cells at `entries · x^(4m)`,
the state after them (`nb` blocks) at `chain · x^13` from offset `13`. -/
theorem grp_block {j : ℕ} {f : String} {m c0 st0 ep nb : ℕ}
    (hok : grpOk (coreProgram.getD j default) f m c0 st0 ep = true)
    (hcok : grpcOk (coreProgram.getD j default) f m c0 st0 ep = true)
    (hnb : (grpSpec m c0 st0 (loopAtoms (coreProgram.getD j default))).nb = nb) (hep : ep ≠ 9)
    {x N chain entries : E} {n : ℕ} {pre : List UInt8}
    (hpre : pre.length = rate * n) (hS : StateAt rd (chain * x ^ 13) 0 (absorbChunks n zeroState pre))
    {cells : List E} (hl : cells.length = 4 * m) (hr : ReadsAt rd (entries * x ^ (4 * m)) cells)
   
    (hS' : StateAt rd (chain * x ^ 13) 13
      (absorbChunks (n + nb) zeroState (pre ++ cellsBytes cells))) :
    LoopBlock rd (coreProgram.getD j default) x N [chain, entries] := by
  set fn := coreProgram.getD j default
  set A := loopAtoms fn with hAdef
  set S := storesOf 4 fn.body with hSdef
  simp only [grpOk, Bool.and_eq_true, decide_eq_true_eq] at hok
  obtain ⟨⟨⟨⟨⟨⟨⟨-, hlen4⟩, hck⟩, hst⟩, hl1⟩, -⟩, -⟩, -⟩ := hok
  simp only [grpcOk, Bool.and_eq_true, Option.isSome_iff_exists, List.all_eq_true,
    Bool.or_eq_true, Bool.not_eq_true', decide_eq_true_eq] at hcok
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨hshape, c', hchk⟩, hpreA⟩, heqA⟩, hSsh⟩, hneeds⟩, hstF⟩, hm9⟩, hmE⟩ :=
    hcok
  have heqA' := atomsEqbL_sound heqA
  let args : List E := [x, N, chain, entries]
  obtain ⟨σ, hσ⟩ : ∃ σ : Val, σ = B1.Val.ofArgs (ev rd (fun _ => 0) args fn.body) := ⟨_, rfl⟩
  obtain ⟨-, -, hgs⟩ := ev_spec rd (fun _ => 0) fn.body args hchk
  rw [show args.length = 4 from rfl, ← hσ] at hgs
  have hg : ∀ a ∈ A, Good rd S (fun _ => 0) σ a := fun a ha =>
    hgs (.atom a) (cl_pre_mem (cl_atom_mem (by rw [heqA']; exact ha)))
  have hpar : fn.params = [.n 0, .n 1, .n 2, .n 3] := by
    have hs2 := hshape
    simp only [loopShapeF, Bool.and_eq_true, decide_eq_true_eq] at hs2
    rw [hs2.1.2, hlen4]; rfl
  have par : ∀ i (hi : i < 4), σ (.n i) = args.getD i 0 := fun i hi => by
    rw [hσ]; exact ev_params rd _ (l := args) hchk (by simp [args]; omega)
  have e0 : σ (.n 0) = x := par 0 (by omega)
  have e2 : σ (.n 2) = chain := par 2 (by omega)
  have e3 : σ (.n 3) = entries := par 3 (by omega)
  have hP := pure_holds hg
  have v9 : σ (.n 9) = chain * x ^ 13 := by rw [monoIs_sound hm9 hP, e2, e0]
  have vE : σ (.n ep) = entries * x ^ (4 * m) := by rw [monoIs_sound hmE hP, e3, e0]
  have hSof : ∀ a ∈ S, ∃ c < 13,
      a = .load ((grpSpec m c0 st0 A).outV ((grpSpec m c0 st0 A).nb - 1) c) (.n 9) (13 + c) := by
    intro a ha
    obtain ⟨c, hc', he⟩ := List.any_eq_true.mp (hSsh a ha)
    exact ⟨c, List.mem_range.mp hc', atomEqb_sound he⟩
  have hnS9 : ∀ d o, o < 13 → Atom.load d (.n 9) o ∉ S := by
    intro d o ho h
    obtain ⟨c, -, he⟩ := hSof _ h
    simp only [Atom.load.injEq] at he
    omega
  have hnSE : ∀ d o, Atom.load d (.n ep) o ∉ S := by
    intro d o h
    obtain ⟨c, -, he⟩ := hSof _ h
    simp only [Atom.load.injEq] at he
    exact hep (congrArg V.idx he.2.1)
  have hq : ∀ a, isLoadB a = false → decide (a ∉ S) = true := by
    intro a ha
    simp only [decide_eq_true_eq]
    intro hm
    obtain ⟨c, -, rfl⟩ := hSof a hm
    simp [isLoadB] at ha
  have vst : ∀ c : Fin 13, σ ((grpSt st0).getD c default) =
      cellsOfState (absorbChunks n zeroState pre) false c := by
    intro c
    simp only [stLoadsOk, Bool.and_eq_true, List.all_eq_true, List.mem_range] at hst
    have hc13 := c.isLt
    rw [load_val (hst.2 c c.isLt) hg (hnS9 _ _ (by omega)), v9, rdAt_of_load (hS c)]
  have vc : ∀ i < 4 * m, σ (.n (i + c0)) = cells.getD i 0 := by
    intro i hi
    simp only [loadsOk, List.all_eq_true, List.mem_range] at hl1
    have := hl1 i (by simp [grpSpec]; omega)
    simp only [grpSpec, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hi,
      Option.map_some, Option.getD_some] at this
    rw [load_val this hg (hnSE _ _), vE, rdAt_of_load (hr i (by omega)),
      List.getD_eq_getElem _ _ (by omega)]
  have hat : ∀ a ∈ A, a.Holds rd σ := by
    refine atoms_holds_stores (S := S) (w := fun _ => 0) hg
      (fun a ha hnS' hns => Or.inl ?_) (fun h1 a ha haS => ?_)
    · rcases hneeds a ha with ((h | h) | h) | h
      · rw [hns] at h; exact absurd h (by simp)
      · exact absurd h hnS'
      · cases a <;> simp only [isLoadBelow, Bool.false_eq_true, Bool.and_eq_true,
          decide_eq_true_eq] at h
        rename_i d p o
        obtain ⟨rfl, ho⟩ := h
        have hv := hS ⟨o, ho⟩
        rw [Nat.zero_add, ← v9] at hv
        exact load_holds_of hnS' (hg _ ha) hv
      · cases a <;> simp only [isLoadBelow, Bool.false_eq_true, Bool.and_eq_true,
          decide_eq_true_eq] at h
        rename_i d p o
        obtain ⟨rfl, ho⟩ := h
        have hv := hr o (by omega)
        rw [← vE] at hv
        exact load_holds_of hnS' (hg _ ha) hv
    · have hF : ∀ b ∈ A.filter (fun a => decide (a ∉ S)), b.Holds rd σ :=
        fun b hb => h1 b (List.mem_filter.mp hb).1 (by simpa using (List.mem_filter.mp hb).2)
      have hchk' : (grpSpec m c0 st0 A).check (A.filter (fun a => decide (a ∉ S))) = true := by
        rw [check_filter hq]; exact hck
      have h0 := initCell_of_loads (s := grpSpec m c0 st0 A) rfl hstF hF
        (S := absorbChunks n zeroState pre) (by rw [v9]; exact hS)
      obtain ⟨hw, -⟩ := chain_whole hchk' rfl hF hpre h0
      have hv : (grpSpec m c0 st0 A).vals σ = cells := by
        refine List.ext_getElem (by simp [grpSpec, ChainSpec.vals, hl]) fun i h1 h2 => ?_
        have hi : i < 4 * m := by omega
        simp only [grpSpec, ChainSpec.vals, List.getElem_map, List.getElem_range, srcVal]
        rw [vc i hi, List.getD_eq_getElem _ _ h2]
      obtain ⟨c, hc13, rfl⟩ := hSof a haS
      show LoadHolds rd (σ (.n 9)) (13 + c) (σ ((grpSpec m c0 st0 A).outV ((grpSpec m c0 st0 A).nb - 1) c))
      have hwc := hw ⟨c, hc13⟩
      rw [hv, hnb, show ((⟨c, hc13⟩ : Fin 13) : ℕ) = c from rfl] at hwc
      rw [hnb, hwc, v9]
      exact hS' ⟨c, hc13⟩
  refine ⟨σ, ?_, fun s hs => ?_⟩
  · rw [hpar]
    simp only [List.map_cons, List.map_nil]
    rw [e0, par 1 (by omega), e2, e3]
    rfl
  · have := hpreA s hs
    cases s <;> simp only [isAtomS, Bool.false_eq_true] at this
    rename_i a
    exact ⟨hat a (by have := cl_mem_atoms hs; rwa [heqA'] at this), trivial⟩

end
end LeanVM.Guest.B1.Digest
