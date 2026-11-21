/-
  LeanVM.Guest.B1.Da.PadAt

  The roots' tree on its honest buffer, placed: the padding loop `da_pad_loop0`, `da_pad`, and the
  tree over the roots.

  `da_verify` checks Benedikt Wagner's LeanDA witnesses (`Da.MatrixWitness.Opens`), as ported here.
-/

module

public import LeanVM.Guest.CoreRef
public import LeanVM.Guest.B1.Da.DvHonest
public import LeanVM.Guest.B1.Da.LoopsComplete
public import LeanVM.Guest.B1.Da.AtTB
public import LeanVM.Guest.B1.Da.DvShape
public import LeanVM.Guest.B1.Da.FlatOut
public import LeanVM.Guest.B1.Digest.Steps
public import LeanVM.Guest.Data.NameStrings
public import LeanVM.Guest.GuestConst
-- Private: `guest_const%` inserts literals, so importers need not see the guest's source.
import LeanVM.Guest.Data.Consts
import LeanVM.Guest.ValRef
import LeanVM.Guest.Data.ValNames.«da_pad»

/-!
# The roots' tree, placed

On a memory holding the roots' tree at `g^bT` (`rootsCells r L syms`): `padL_rel` runs the padding
loop over the `2^L - r` padding blobs, `dl_rel` the levels, returning `daTree`'s cells.
`pad_completeAtB`: `da_pad` complete within `padB` by a tree of `padNH`.
-/

namespace LeanVM.Guest.B1.Da

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Memory
open LeanVM.Guest.Value.Keccak LeanVM.Protocol.KeccakHash
open LeanVM.Protocol.Verifier (gen eOfNat)
open LeanVM.Guest.B1.Fwd LeanVM.Guest.B1.Digest
open LeanVM.Guest.B1 (CompleteAtDTB Kid KidD kidsAt outsL KidsDepBP OutsOk RegionsOk CallsMatch
  Returns completeAt_flatDepRet flatCalls namedP)
open LeanVM.Guest.B1.Main (Layout MemL RegionL iterK)
open LeanVM.Guest.Budget (NodeHonest)

@[expose] public section

theorem one_add_gen_isInK (r : ℕ) : IsInK (1 + gen ^ r) := by
  rw [← pow_zero gen]; exact gen_pow_add_isInK _ _

theorem kidsT_mono : ∀ (cs : List Call) (Ts Ts' : List (Tree → Prop)) (ks : List Tree),
    List.Forall₂ (fun T T' => ∀ t, T t → T' t) Ts Ts' → KidsT cs Ts ks → KidsT cs Ts' ks
  | _ :: cs, _ :: Ts, _ :: Ts', k :: ks, .cons h hs, ⟨h1, h2⟩ =>
    ⟨fun ht => h k (h1 ht), kidsT_mono cs Ts Ts' ks hs h2⟩
  | [], _, _, _, _, _ => trivial
  | _ :: _, [], [], _, _, _ => trivial
  | _ :: _, _ :: _, _ :: _, [], _, _ => trivial

/-- An honest node under weaker predicates on its callees. -/
theorem nodeHonest_mono {P : Core.Program} {f : String} {Q : Val → Prop} {cs : Val → List Call}
    {bs : Val → List ℕ} {Ts Ts' : List (Tree → Prop)} {t : Tree} (h : NodeHonest P f Q cs bs Ts t)
    (hT : List.Forall₂ (fun T T' => ∀ t, T t → T' t) Ts Ts') : NodeHonest P f Q cs bs Ts' t := by
  obtain ⟨σ, ks, rfl, hQ, hw, hl, hk⟩ := h
  exact ⟨σ, ks, rfl, hQ, hw, by rw [← hT.length_eq]; exact hl, kidsT_mono _ _ _ _ hT hk⟩

theorem namedP_forall₂ {fs : String → ℕ} : ∀ (names : List String) (Bs : List ℕ) (Ps : List (Tree → Prop)),
    names.length = Ps.length → Bs.length = Ps.length →
    List.Forall₂ (fun T T' => ∀ t, T t → T' t) (namedP fs names Bs Ps) Ps
  | [], [], [], _, _ => .nil
  | _ :: ns, _ :: Bs, _ :: Ps, h1, h2 =>
    .cons (fun _ h => h.2) (namedP_forall₂ ns Bs Ps (by simpa using h1) (by simpa using h2))
  | [], _ :: _, _, h1, h2 => by simp at h1 h2; omega
  | _ :: _, [], _, h1, h2 => by simp at h1 h2; omega
  | [], [], _ :: _, h1, _ => by simp at h1
  | _ :: _, _ :: _, [], h1, _ => by simp at h1

variable {rd : Reader} {r L : ℕ} {syms : ℕ → ℕ → List E} {bT : ℕ}

/-- The roots' tree's leaf words. -/
theorem roots_leaf {i : ℕ} (hi : i < 2 ^ L) :
    (rootsCells r L syms).getD (2 * i) 0 = (digestHalves (blobLeaf r syms i)).1 ∧
      (rootsCells r L syms).getD (2 * i + 1) 0 = (digestHalves (blobLeaf r syms i)).2 := by
  have hl := length_treeCells (length_rootLeaves r L syms)
  have hp : (pairCells (rootLeaves r L syms)).length = 2 * 2 ^ L := by
    rw [length_pairCells, length_rootLeaves]
  have htree : treeCells (rootLeaves r L syms) L = pairCells (rootLeaves r L syms) ++
      (List.range L).flatMap fun l => pairCells (treeLvl (rootLeaves r L syms) (l + 1)) := by
    rw [treeCells, List.range_succ_eq_map, List.flatMap_cons, List.flatMap_map]
    rfl
  have hp1 := Nat.one_le_two_pow (n := L)
  have e : ∀ j < 2 * 2 ^ L, (rootsCells r L syms).getD j 0 =
      (pairCells (rootLeaves r L syms)).getD j 0 := by
    intro j hj
    rw [rootsCells, List.getD_append _ _ _ _ (by rw [hl]; omega), htree,
      List.getD_append _ _ _ _ (by rw [hp]; exact hj)]
  rw [e _ (by omega), e _ (by omega), (pairCells_getD _ i).1, (pairCells_getD _ i).2]
  simp [rootLeaves, hi]

/-- **The padding blobs' roots** (`da_pad_loop0`). -/
theorem padL_rel (hrL : r < 2 ^ L) (hT : ReadsAt rd (gen ^ bT) (rootsCells r L syms)) :
    coreProgram.Rel rd name% «da_pad_loop0» [1, gen ^ (2 ^ L - r), gen ^ bT, gen ^ r] [] := by
  have := loopF_complete (rd := rd) find_padL dv_loops_shape.2.1.1 (N := gen ^ (2 ^ L - r))
    (rest := [gen ^ bT, gen ^ r]) (m := 2 ^ L - r) rfl (fun d hd => ?_) 0 (by omega)
  · rwa [pow_zero] at this
  obtain ⟨hl1, hl2⟩ := roots_leaf (r := r) (L := L) (syms := syms) (i := r + d) (by omega)
  have hpad : blobLeaf r syms (r + d) = daPadBlobDigest := by rw [blobLeaf, ite_neg' (by omega)]
  rw [hpad] at hl1 hl2
  have hp : gen ^ bT * (gen ^ r * gen ^ r) * (gen ^ d * gen ^ d) = gen ^ bT * gen ^ (2 * (r + d)) := by
    simp only [← pow_add]
    ring_nf
  refine padL_block ?_ ?_
  · rw [hp, loadHolds_mul_gen_pow]
    exact loadHolds_of_reads hT (by rw [length_rootsCells]; omega) (by rw [Nat.add_zero, hl1])
  · rw [hp, loadHolds_mul_gen_pow]
    exact loadHolds_of_reads hT (by rw [length_rootsCells]; omega) hl2

/-- **The tree over the roots** returns `daTree`'s cells. -/
theorem dl_rel (hL : L = guest_const% DA_LOG_MAX_ROWS) (hT : ReadsAt rd (gen ^ bT) (rootsCells r L syms)) :
    coreProgram.Rel rd (daLevelsName L) [gen ^ bT] (digestCells (daTree r L syms)) := by
  rw [rootsCells, readsAt_append] at hT
  have hc := da_levels_complete L (Or.inl hL) rd (gen ^ bT) (rootLeaves r L syms) (length_rootLeaves r L syms)
    (treeMem_of_reads (length_rootLeaves r L syms) hT.1)
  rw [rootLeaves, cellRoot_mRoot] at hc
  exact hc

/-! ## `da_pad` -/

/-- `da_pad`'s body before its `ret`. -/
def padPre : List Stmt := dpadBody.dropLast

theorem pad_body : (fn% «da_pad»).body = padPre ++ [.ret []] := by
  have hok := dpad_ok
  unfold dpadOk at hok
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hok
  rw [stmtsEqb_sound hok.2]
  rfl

theorem pad_params : (fn% «da_pad»).params = [.n (val% «da_pad» "roots"), .n (val% «da_pad» "n_blob_g"), .n (val% «da_pad» "gap_g")] := by
  have hok := dpad_ok
  unfold dpadOk at hok
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hok
  exact hok.1

/-- `da_pad`'s callee: the padding loop, entered iff the gap `d` is nonzero. -/
noncomputable def padKids (r L : ℕ) (syms : ℕ → ℕ → List E) (bT : ℕ) : List KidD :=
  [fun _ => ⟨name% «da_pad_loop0», decide (2 ^ L - r ≠ 0), [1, gen ^ (2 ^ L - r), gen ^ bT, gen ^ r],
    [(bT, rootsCells r L syms)], Returns []⟩]

variable (fs : String → ℕ) (cert : String → V → ℕ)

/-- **`da_pad` is complete, placed, within `padB`**, on the roots' tree at `g^bT`. -/
theorem pad_completeAtB {SK : String → ℕ}
    (hpad : TotalLeOn coreProgram fs name% «da_pad_loop0» LoopPre
      (fun a => logG (a.getD 1 0) * iterK fs SK name% «da_pad_loop0» + fs name% «da_pad_loop0»))
    (hrL : r ≤ 2 ^ L) (hL : L ≤ 10) :
    CompleteAtDTB fs cert 16 "da_pad" [(bT, rootsCells r L syms)] [gen ^ bT, gen ^ r, gen ^ (2 ^ L - r)]
      (Returns []) (padNH (2 ^ L - r)) (padB fs SK (2 ^ L - r)) := by
  have hN : 2 ^ L ≤ 1024 := le_trans (Nat.pow_le_pow_right (by norm_num) hL) (by norm_num)
  have hd : 2 ^ L - r < ordG := by unfold ordG; omega
  refine ((completeAt_flatDepRet (fs := fs) (cert := cert) find_da_pad
    (by rw [Program.loop_of_find? find_da_pad]; decide +kernel) 16 [(bT, rootsCells r L syms)]
    [gen ^ bT, gen ^ r, gen ^ (2 ^ L - r)] (fun _ _ => []) [] pad_body (by decide) (by decide)
    (by decide) [] (fun _ => []) (fun _ => .nil) (fun _ => padKids r L syms bT)
    [name% «da_pad_loop0»]
    [if 2 ^ L - r ≠ 0 then (2 ^ L - r) * iterK fs SK name% «da_pad_loop0» + fs name% «da_pad_loop0»
      else fs name% «da_pad_loop0»] [fun _ => True] (padQ (2 ^ L - r))
    (fun _ => .cons (fun _ => rfl) .nil) (fun _ => ⟨fun _ => ⟨fun ht => ?_, fun ht => ?_⟩, trivial⟩)
    (fun _ _ _ _ => rfl) (fun fp outs ho => ?_) (fun fp outs ho rd _ _ hLin _ => ?_)
    (fun fp outs hlen ho rd _ _ _ _ => ?_)).mono ?_ (fun t ht => nodeHonest_mono ht
      (namedP_forall₂ _ _ _ rfl rfl)))
  · have h0 : 2 ^ L - r ≠ 0 := by simpa [padKids] using ht
    simp only [h0, ne_eq, not_false_eq_true, ↓reduceIte]
    exact pureB_loop daPure (by simp [daPureSet]) (fun rd hm => padL_rel (by omega)
      (reads_of_memL hm List.mem_cons_self)) hpad (by omega) (by omega)
  · have h0 : 2 ^ L - r = 0 := by simpa [padKids] using ht
    simp [h0]
  · match outs with
    | [] => trivial
    | o :: os => exact ⟨fun _ i hi => Or.inl (Or.inl hi), by cases os <;> trivial⟩
  · match outs with
    | [] => exact fun q hq => by simp [kidsAt, Kid.lins] at hq
    | o :: os => simpa [kidsAt, padKids, Kid.lins] using hLin
  · match outs, hlen with
    | [o], _ =>
    refine ⟨Val.ofArgs [gen ^ bT, gen ^ r, gen ^ (2 ^ L - r), word 1 0, word 1 0 + gen ^ (2 ^ L - r),
      word 1 0], by rw [pad_params]; rfl, fun s hs => ?_, ?_, rfl, rfl, ?_, fun q hq => ?_,
      ⟨rfl, by simp [ofArgs_n, word_one], by simp [ofArgs_n, word_one]⟩⟩
    · simp only [padPre, dpadBody, List.dropLast, List.mem_cons, List.not_mem_nil, or_false] at hs
      rcases hs with rfl | rfl | rfl | rfl <;> exact True.intro
    · rw [pad_body]
      refine holdsList_straight _ _ _ _ (fun s hs => ?_) rfl
      simp only [padPre, dpadBody, List.dropLast, List.mem_cons, List.not_mem_nil, or_false] at hs
      rcases hs with rfl | rfl | rfl | rfl
      all_goals simp only [SHolds, Atom.Holds, ofArgs_n, List.getD_cons_succ, List.getD_cons_zero]
      exact ⟨by rw [word_one]; exact one_add_gen_isInK _, fun _ => True.intro⟩
    · have ho1 : decide (2 ^ L - r ≠ 0) = true → o.1 = [] := fun h =>
        (show OutsOk [_] [o] from ho).1 h |>.1
      simp only [flatCalls, padPre, dpadBody, List.dropLast, List.filterMap, Stmt.callSF,
        Main.Stmt.callS, List.map, Main.mkCall, kidsAt, padKids, CallsMatch, ofArgs_n,
        List.getD_cons_succ, List.getD_cons_zero, word_one]
      exact ⟨trivial, by simp only [decide_eq_decide]; exact one_add_gen_ne_iff hd,
        fun ht => ⟨trivial, (ho1 ht).symm⟩, trivial⟩
    · simp [padPre, dpadBody, Stmt.loadS] at hq
  · simp only [List.sum_nil, List.sum_cons, padB]
    omega

end
end LeanVM.Guest.B1.Da
