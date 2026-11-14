/-
  LeanVM.Guest.B1.Main.MainPops

  `main`'s own entries: its node pops `meta`, `fs_seed`, its callees' entries in call order, `da_pick`, and a leaf's `leaf_defer`.
-/

module

public import LeanVM.Guest.B1.Main.MainAt
public import LeanVM.Guest.B1.Sig.PopsKit

/-!
# `main`'s own entries

* `Stmt.popS`, `spliceS`: a straight block's skeleton of entries, a witness hint's or a frame's callee's, and its entries with the callees' spliced in; `splice_straight`: a straight block's events splice as its skeleton;
* `mBlocks_popS`: `main`'s blocks' skeletons, by the kernel;
* `mainOwnPops m pe px ps p0 p1 p2 p3 pd p5 pa pst`: `main`'s entries, its callees' given; `main_pops`: a node of `main` at a valuation with `main`'s honest values pops them.
-/

namespace LeanVM.Guest.B1.Main

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Memory
open LeanVM.Protocol LeanVM.Protocol.Verifier LeanVM.Protocol.KeccakHash

@[expose] public section

/-- What a straight statement pops: a witness hint's stream and destination, or (`none`) its frame's callee's entries. -/
def Stmt.popS : Stmt → Option (Option (String × Dest))
  | .atom (.hint (.witness s d)) => some (some (s, d))
  | .call .. => some none
  | .callIf .. => some none
  | _ => none

/-- A skeleton's entries, each frame's callee's taken from `ks` in turn. -/
def spliceS (rd : Reader) (σ : Val) : List (Option (String × Dest)) → List (List Pop) → List Pop
  | [], _ => []
  | some (s, d) :: xs, ks => (s, d.words rd σ) :: spliceS rd σ xs ks
  | none :: xs, ks => ks.headD [] ++ spliceS rd σ xs ks.tail

variable {rd : Reader} {σ : Val}

/-- **A straight block's events splice as its skeleton.** -/
theorem splice_straight : ∀ (pre : List Stmt), pre.all Main.Stmt.straight = true → ∀ ks : List (List Pop),
    splice rd σ (pre.flatMap (Main.slEvs σ)) ks = spliceS rd σ (pre.filterMap Stmt.popS) ks
  | [], _, _ => rfl
  | s :: pre, h, ks => by
    simp only [List.all_cons, Bool.and_eq_true] at h
    rw [List.flatMap_cons]
    match s, h.1 with
    | .atom a, _ =>
      rw [show Main.slEvs σ (.atom a) = [.atom a] from rfl, List.singleton_append, splice,
        splice_straight pre h.2]
      cases a with
      | hint x =>
        cases x with
        | witness s d => rfl
        | _ => rfl
      | _ => rfl
    | .call f args rets, _ =>
      show ks.headD [] ++ splice rd σ (pre.flatMap (Main.slEvs σ)) ks.tail = _
      rw [splice_straight pre h.2]
      rfl
    | .callIf c f args, _ =>
      have e : ∀ es, splice rd σ ((if σ c = 0 then Ev.skip f args else .call f args []) :: es) ks =
          ks.headD [] ++ splice rd σ es ks.tail := fun es => by split <;> rfl
      show splice rd σ ((if σ c = 0 then Ev.skip f args else .call f args []) :: pre.flatMap (Main.slEvs σ)) ks = _
      rw [e, splice_straight pre h.2]
      rfl

theorem splice_inK_mid (c : V) : ∀ (xs ys : List Ev) (ks : List (List Pop)),
    splice rd σ (xs ++ .inK c :: ys) ks = splice rd σ (xs ++ ys) ks
  | [], _, _ => rfl
  | .atom a :: xs, ys, ks => by
    simp only [List.cons_append, splice]
    rw [splice_inK_mid c xs ys ks]
  | .inK _ :: xs, ys, ks => by
    simp only [List.cons_append, splice]
    exact splice_inK_mid c xs ys ks
  | .call .. :: xs, ys, ks => by
    simp only [List.cons_append, splice]
    rw [splice_inK_mid c xs ys ks.tail]
  | .skip .. :: xs, ys, ks => by
    simp only [List.cons_append, splice]
    rw [splice_inK_mid c xs ys ks.tail]

/-- `main`'s straight blocks on its path under `σ`. -/
noncomputable def mPath (σ : Val) : List Stmt :=
  mPre ++ (if σ (.n 368) = 0 then mDa else mDaZ) ++ mMid ++ (if σ (.n 418) = 0 then mLeaf else mAgg) ++ mPost

theorem splice_blocks (f : Stmt → List Ev) (c c' : V) (A B C D F : List Stmt) (ks : List (List Pop)) :
    splice rd σ (A.flatMap f ++ (.inK c :: B.flatMap f ++ (C.flatMap f ++ (.inK c' :: D.flatMap f ++
      F.flatMap f)))) ks = splice rd σ ((A ++ B ++ C ++ D ++ F).flatMap f) ks := by
  simp only [List.cons_append]
  rw [splice_inK_mid]
  simp only [← List.append_assoc]
  rw [splice_inK_mid]
  simp only [List.flatMap_append, List.append_assoc]

theorem splice_mEvs (ks : List (List Pop)) :
    splice rd σ (mEvs σ) ks = spliceS rd σ ((mPath σ).filterMap Stmt.popS) ks := by
  obtain ⟨s1, s2, s2', s3, s4, s5, s6⟩ := mBlocks_straight
  have hs : (mPath σ).all Main.Stmt.straight = true := by
    simp only [mPath, List.all_append, Bool.and_eq_true]
    exact ⟨⟨⟨⟨s1, by split; exacts [s2, s2']⟩, s3⟩, by split; exacts [s4, s5]⟩, s6⟩
  exact (splice_blocks (Main.slEvs σ) _ _ _ _ _ _ _ ks).trans (splice_straight _ hs ks)

/-- **`main`'s blocks' skeletons.** -/
theorem mBlocks_popS : mPre.filterMap Stmt.popS = [some ("meta", .stack ((List.range 8).map V.n)),
      some ("fs_seed", .stack [.n 26, .n 27]), none, none, none, none, none, none, none] ∧
    mDa.filterMap Stmt.popS = [none] ∧ mDaZ.filterMap Stmt.popS = [] ∧
    mMid.filterMap Stmt.popS = [none, some ("da_pick", .stack [.n 405])] ∧
    mLeaf.filterMap Stmt.popS = [some ("leaf_defer", .stack [.n 419])] ∧
    mAgg.filterMap Stmt.popS = [none] ∧ mPost.filterMap Stmt.popS = [none] := by
  decide +kernel

/-- **`main`'s entries**, its callees' given in call order: `exponent_tables`', the two claim lists' digests', the four signature loops', the direct DA check's when it runs, the children's loop's, the batching's when it runs, the statement digest's. -/
def mainOwnPops (m : MainIn) (pe px ps p0 p1 p2 p3 pd p5 pa pst : List Pop) : List Pop :=
  ("meta", m.cnt.map (gen ^ ·)) :: ("fs_seed", [(digestHalves m.seed).1, (digestHalves m.seed).2]) ::
    (pe ++ (px ++ (ps ++ (p0 ++ (p1 ++ (p2 ++ (p3 ++ ((if m.nd = 1 then pd else []) ++ (p5 ++
      (("da_pick", [gen ^ m.pick]) :: ((if m.nc = 0 then [("leaf_defer", [m.leaf])] else pa) ++ pst)))))))))))

/-- `main`'s callees' entries in call order, the conditional ones where they run. -/
def mainKidPops (m : MainIn) (pe px ps p0 p1 p2 p3 pd p5 pa pst : List Pop) : List (List Pop) :=
  [pe, px, ps, p0, p1, p2, p3] ++ (if m.nd = 1 then [pd] else []) ++ [p5] ++ (if m.nc = 0 then [] else [pa]) ++
    [pst]

theorem mPath_popS {m : MainIn} (hnd : m.nd ≤ 1) (hnc : m.nc ≤ 16) (hv : MVals rd σ m) :
    (mPath σ).filterMap Stmt.popS = [some ("meta", .stack ((List.range 8).map V.n)),
      some ("fs_seed", .stack [.n 26, .n 27]), none, none, none, none, none, none, none] ++
      (if m.nd = 1 then [none] else []) ++ [none, some ("da_pick", .stack [.n 405])] ++
      (if m.nc = 0 then [some ("leaf_defer", .stack [.n 419])] else [none]) ++ [none] := by
  have h368 : σ (.n 368) = 0 ↔ m.nd = 1 := by
    rw [hv.v389, e_add_eq_zero_iff]
    constructor
    · intro h
      exact Digest.gen_pow_inj' (a := m.nd) (b := 1) (by omega) (by norm_num) (by rw [h, pow_one])
    · intro h; rw [h, pow_one]
  have h418 : σ (.n 418) = 0 ↔ m.nc = 0 := by
    rw [hv.v451, add_comm, e_add_eq_zero_iff, eq_comm, gen_pow_eq_one_iff (by omega)]
  obtain ⟨b1, b2, b2', b3, b4, b5, b6⟩ := mBlocks_popS
  have e1 : (if σ (.n 368) = 0 then mDa else mDaZ).filterMap Stmt.popS = if m.nd = 1 then [none] else [] := by
    by_cases h : m.nd = 1
    · rw [ite_pos' (h368.mpr h), ite_pos' h, b2]
    · rw [ite_neg' (fun h' => h (h368.mp h')), ite_neg' h, b2']
  have e2 : (if σ (.n 418) = 0 then mLeaf else mAgg).filterMap Stmt.popS =
      if m.nc = 0 then [some ("leaf_defer", .stack [.n 419])] else [none] := by
    by_cases h : m.nc = 0
    · rw [ite_pos' (h418.mpr h), ite_pos' h, b4]
    · rw [ite_neg' (fun h' => h (h418.mp h')), ite_neg' h, b5]
  rw [mPath, List.filterMap_append, List.filterMap_append, List.filterMap_append, List.filterMap_append, b1, e1, b3,
    e2, b6]

/-- **`main`'s path splices its callees' entries into its own**, at a valuation with `main`'s honest values. -/
theorem main_spliceS {m : MainIn} (hnd : m.nd ≤ 1) (hnc : m.nc ≤ 16) (hv : MVals rd σ m)
    (pe px ps p0 p1 p2 p3 pd p5 pa pst : List Pop) :
    spliceS rd σ ((mPath σ).filterMap Stmt.popS) (mainKidPops m pe px ps p0 p1 p2 p3 pd p5 pa pst) =
      mainOwnPops m pe px ps p0 p1 p2 p3 pd p5 pa pst := by
  have hO : ∀ {j : ℕ}, j ∈ mOrcIdx → σ (.n j) = mOrc m j := fun hj => hv.orc _ hj
  have w1 : Dest.words rd σ (.stack ((List.range 8).map V.n)) = m.cnt.map (gen ^ ·) := by
    show [σ (.n 0), σ (.n 1), σ (.n 2), σ (.n 3), σ (.n 4), σ (.n 5), σ (.n 6), σ (.n 7)] = _
    rw [hO (by decide), hO (by decide), hO (by decide), hO (by decide), hO (by decide), hO (by decide),
      hO (by decide), hO (by decide)]
    rfl
  have w2 : Dest.words rd σ (.stack [.n 26, .n 27]) = [(digestHalves m.seed).1, (digestHalves m.seed).2] := by
    show [σ (.n 26), σ (.n 27)] = _
    rw [hO (by decide), hO (by decide)]
    rfl
  have w3 : Dest.words rd σ (.stack [.n 405]) = [gen ^ m.pick] := by
    show [σ (.n 405)] = _
    rw [hO (by decide)]
    rfl
  have w4 : Dest.words rd σ (.stack [.n 419]) = [m.leaf] := by
    show [σ (.n 419)] = _
    rw [hO (by decide)]
    rfl
  rw [mPath_popS hnd hnc hv, mainKidPops, mainOwnPops]
  by_cases a : m.nd = 1 <;> by_cases b : m.nc = 0 <;>
    simp only [a, b, ↓reduceIte, List.cons_append, List.nil_append, List.append_nil,
      spliceS, List.headD_cons, List.tail_cons, w1, w2, w3, w4]

/-- **`main`'s node pops its entries**, at a valuation with `main`'s honest values, its callees popping theirs. -/
theorem main_pops {m : MainIn} (hnd : m.nd ≤ 1) (hnc : m.nc ≤ 16) (hv : MVals rd σ m) {bufs : List ℕ}
    {ks : List Tree} {pe px ps p0 p1 p2 p3 pd p5 pa pst : List Pop}
    (hk : Tree.popsKids coreProgram rd ks = mainKidPops m pe px ps p0 p1 p2 p3 pd p5 pa pst) :
    (Memory.Tree.node "main" σ bufs ks).pops coreProgram rd = mainOwnPops m pe px ps p0 p1 p2 p3 pd p5 pa pst := by
  rw [Tree.pops_node find_main (walk_main σ), splice_mEvs, hk, main_spliceS hnd hnc hv]

end
end LeanVM.Guest.B1.Main
