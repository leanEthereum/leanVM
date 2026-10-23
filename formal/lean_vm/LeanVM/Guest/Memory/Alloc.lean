/-
  LeanVM.Guest.Memory.Alloc

  The bump allocator of an honest evaluation: every call instance's frame, `HeapBuf`s and callees
  in one contiguous region per subtree, its `HeapBuf`s placed from its own frame pointer and
  sizes, the regions of distinct instances disjoint, a loop's next iteration in the frame right
  after its own; and the frame writes, consistent by disjointness.
-/

module

public import LeanVM.Guest.Memory.Eval
public import LeanVM.Guest.Memory.Image

/-!
# Placing a call tree

Frame sizes are a parameter `fs` (the compiler's, from the certificate). A call instance of `f`
placed at word `fp` occupies, in order: its frame `[fp, fp + fs f)`, then its `HeapBuf`s one
after another, then its callees' regions in call order, each subtree contiguous. So a subtree
of `total` words occupies `[fp, fp + total)`, and an instance's `HeapBuf` pointers depend only
on its own `fp` and sizes (`bufBase`), never on its callees': a completeness proof fixes them
before it knows what its callees allocate.

A **loop helper** (`Program.loop`: its body ends with a `callIf` to itself and `ret []`) is the
exception: its tail call (its last callee, a phantom on the last iteration) is the frame its code
addresses as `fp · g^S`, so that callee's region comes first, at `fp + fs f`, then the
`HeapBuf`s, then the other callees in call order (`kidPos`, `Inst.Placed.kidFps_getLast?`). Of
the guest's loop helpers only `__loop5` (the loop over the children in `main`) allocates, two
`HeapBuf`s per iteration that its tail call's arguments do not depend on.

The Rust runner allocates in execution order instead (`cpu/execute.rs`, `next_free` from the
end of `main`'s frame): a callee frame when its call is set up, a loop's `n + 1` frames at once,
a dispatch's frame at the largest arm's size, a `HeapBuf` when its hint runs. Completeness needs
only disjointness, which this order gives by construction.

`Tree.insts fs lp H fp hdr t` lists the placed call instances (`Inst`), `lp` saying which
functions are loop helpers: the tree, its frame, its header words `fp[0]`, `fp[1]`, its callees'
frames and its `HeapBuf` bases; a callee's header is `H I i`, a function of the caller and the
call's index (the return registers, or the caller's own for a tail call). `insts_within` and
`insts_pairwise`: every instance owns words of its subtree's region only, and two instances own
no word in common. `frameWrites_consistent`: the headers and cells of all frames are consistent
writes.
-/

namespace LeanVM.Guest.Memory

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core

@[expose] public section

/-- A loop helper: its body ends with a `callIf` to itself, then `ret []`. -/
def _root_.LeanVM.Guest.Core.Fn.loop (fn : Fn) : Bool :=
  match fn.body.reverse with
  | .ret [] :: .callIf _ g _ :: _ => g == fn.name
  | _ => false

/-- The loop helpers of a program. -/
def _root_.LeanVM.Guest.Core.Program.loop (P : Core.Program) (f : String) : Bool :=
  match P.find? f with
  | some fn => fn.loop
  | none => false

theorem _root_.LeanVM.Guest.Core.Program.loop_of_find? {P : Core.Program} {f : String} {fn : Fn}
    (h : P.find? f = some fn) : P.loop f = fn.loop := by
  simp only [Program.loop, h]

/-- A placed call instance. -/
structure Inst where
  /-- The call instance. -/
  t : Tree
  /-- Its frame's first word. -/
  fp : ℕ
  /-- The words of `fp[0]`, `fp[1]`. -/
  hdr : E × E
  /-- Its callees' frames, in call order. -/
  kidFps : List ℕ
  /-- Its `HeapBuf`s' first words, in allocation order. -/
  bufBases : List ℕ

variable (fs : String → ℕ) (lp : String → Bool)

mutual
/-- The words a subtree allocates: frames and `HeapBuf`s. -/
def Tree.total : Tree → ℕ
  | .node f _ bufs kids => fs f + Tree.totalKids kids + bufs.sum
  | .phantom f _ => fs f

/-- The words a list of subtrees allocates. -/
def Tree.totalKids : List Tree → ℕ
  | [] => 0
  | k :: ks => k.total + Tree.totalKids ks
end

/-- Regions of the sizes `ss`, one after another from `b`. -/
def bases (b : ℕ) : List ℕ → List ℕ
  | [] => []
  | s :: ss => b :: bases (b + s) ss

/-- The first word of the `HeapBuf`s of an instance of `f` at `fp` whose callees' regions have
the sizes `ns`: right after its frame, or after its tail call's region for a loop helper. -/
def bufBase (fp : ℕ) (f : String) (ns : List ℕ) : ℕ :=
  fp + fs f + if lp f then ns.getLast?.getD 0 else 0

/-- The callees' frames of an instance of `f` at `fp` with `HeapBuf`s `bufs`, in call order, for
callee regions of sizes `ns`: one after another from the end of its `HeapBuf`s, a loop helper's
last callee at `fp + fs f`. -/
def kidPos (fp : ℕ) (f : String) (bufs ns : List ℕ) : List ℕ :=
  if lp f then
    bases (bufBase fs lp fp f ns + bufs.sum) ns.dropLast ++ ns.getLast?.toList.map fun _ => fp + fs f
  else bases (bufBase fs lp fp f ns + bufs.sum) ns

mutual
/-- **The bump allocator**: the call instances of a subtree whose frame is at `fp`. -/
def Tree.insts (H : Inst → ℕ → E × E) (fp : ℕ) (hdr : E × E) : Tree → List Inst
  | t@(.node f _ bufs kids) =>
      let I : Inst := ⟨t, fp, hdr, kidPos fs lp fp f bufs (kids.map (Tree.total fs)),
        bases (bufBase fs lp fp f (kids.map (Tree.total fs))) bufs⟩
      I :: Tree.instsKids H I 0 (kidPos fs lp fp f bufs (kids.map (Tree.total fs))) kids
  | t@(.phantom ..) => [⟨t, fp, hdr, [], []⟩]

/-- The call instances of the callees `ks` of `I` from its `i`-th, their frames at `ps`. -/
def Tree.instsKids (H : Inst → ℕ → E × E) (I : Inst) (i : ℕ) : List ℕ → List Tree → List Inst
  | _, [] => []
  | [], _ :: _ => []
  | p :: ps, k :: ks => k.insts H p (H I i) ++ Tree.instsKids H I (i + 1) ps ks
end

/-- Word `i` is in `I`'s frame. -/
def Inst.Frame (I : Inst) (i : ℕ) : Prop := I.fp ≤ i ∧ i < I.fp + fs I.t.name

/-- Word `i` is in one of `I`'s `HeapBuf`s. -/
def Inst.Buf (I : Inst) (i : ℕ) : Prop :=
  ∃ q ∈ I.t.bufs.zip I.bufBases, q.2 ≤ i ∧ i < q.2 + q.1

/-- Word `i` is `I`'s. -/
def Inst.Owns (I : Inst) (i : ℕ) : Prop := I.Frame fs i ∨ I.Buf i

/-- Two instances own no word in common. -/
def Inst.Apart (I J : Inst) : Prop := ∀ i, I.Owns fs i → ¬ J.Owns fs i

instance : Std.Symm (Inst.Apart fs) := ⟨fun _ _ h i hJ hI => h i hI hJ⟩

/-- Two regions `(size, base)` are disjoint. -/
def Disj (q q' : ℕ × ℕ) : Prop := q.2 + q.1 ≤ q'.2 ∨ q'.2 + q'.1 ≤ q.2

variable {fs lp}

/-! ## Regions -/

theorem bases_zip : ∀ {b : ℕ} {ss : List ℕ} {q : ℕ × ℕ}, q ∈ ss.zip (bases b ss) →
    b ≤ q.2 ∧ q.2 + q.1 ≤ b + ss.sum
  | _, [], _, h => (List.not_mem_nil h).elim
  | b, s :: ss, q, h => by
      simp only [bases, List.zip_cons_cons, List.mem_cons] at h
      rcases h with rfl | h
      · simp only [List.sum_cons]; omega
      · have := bases_zip h
        simp only [List.sum_cons]; omega

/-- The regions placed one after another are disjoint, in order. -/
theorem bases_pairwise : ∀ {b : ℕ} {ss : List ℕ},
    (ss.zip (bases b ss)).Pairwise fun q q' => q.2 + q.1 ≤ q'.2
  | _, [] => List.Pairwise.nil
  | b, s :: ss => by
      simp only [bases, List.zip_cons_cons, List.pairwise_cons]
      exact ⟨fun q hq => (bases_zip hq).1, bases_pairwise⟩

theorem length_bases : ∀ {b : ℕ} {ss : List ℕ}, (bases b ss).length = ss.length
  | _, [] => rfl
  | _, _ :: _ => by simp [bases, length_bases]

/-- The `i`-th region placed from `b` starts after the first `i`. -/
theorem getElem?_bases : ∀ {b : ℕ} {ss : List ℕ} {i : ℕ}, i < ss.length →
    (bases b ss)[i]? = some (b + (ss.take i).sum)
  | _, [], _, h => absurd h (by simp)
  | b, s :: ss, 0, _ => by simp [bases]
  | b, s :: ss, i + 1, h => by
      simp only [bases, List.getElem?_cons_succ, List.take_succ_cons, List.sum_cons]
      rw [getElem?_bases (by simpa using h)]
      congr 1
      omega

theorem totalKids_cons (k : Tree) (ks : List Tree) :
    Tree.totalKids fs (k :: ks) = k.total fs + Tree.totalKids fs ks := by
  rw [Tree.totalKids]

theorem totalKids_eq_sum : ∀ ks : List Tree, Tree.totalKids fs ks = (ks.map (Tree.total fs)).sum
  | [] => by rw [Tree.totalKids]; rfl
  | k :: ks => by rw [totalKids_cons, totalKids_eq_sum ks, List.map_cons, List.sum_cons]

theorem total_node (f : String) (σ : Val) (bufs : List ℕ) (kids : List Tree) :
    (Tree.node f σ bufs kids).total fs = fs f + Tree.totalKids fs kids + bufs.sum := by
  rw [Tree.total]

theorem le_total (t : Tree) : fs t.name ≤ t.total fs := by
  cases t with
  | node f σ bufs kids => rw [total_node]; simp only [Tree.name]; omega
  | phantom f σ => rw [Tree.total]; rfl

theorem getLast?_getD_le_sum : ∀ ns : List ℕ, ns.getLast?.getD 0 ≤ ns.sum := by
  intro ns
  rcases List.eq_nil_or_concat ns with rfl | ⟨l, b, rfl⟩
  · simp
  · simp [List.concat_eq_append, List.sum_append]

/-- The `HeapBuf`s lie past the frame, within the region. -/
theorem bufBase_le (fp : ℕ) (f : String) (bufs ns : List ℕ) :
    fp + fs f ≤ bufBase fs lp fp f ns ∧ bufBase fs lp fp f ns + bufs.sum ≤ fp + fs f + ns.sum + bufs.sum := by
  have := getLast?_getD_le_sum ns
  unfold bufBase
  split <;> omega

theorem length_kidPos (fp : ℕ) (f : String) (bufs ns : List ℕ) :
    (kidPos fs lp fp f bufs ns).length = ns.length := by
  unfold kidPos
  split
  · rcases List.eq_nil_or_concat ns with rfl | ⟨l, b, rfl⟩
    · simp [bases]
    · simp [List.concat_eq_append, length_bases]
  · exact length_bases

/-- **The callees' regions**: past the frame, within the region, apart from the `HeapBuf`s. -/
theorem kidPos_regions (fp : ℕ) (f : String) (bufs ns : List ℕ) :
    ∀ q ∈ ns.zip (kidPos fs lp fp f bufs ns), fp + fs f ≤ q.2 ∧
      q.2 + q.1 ≤ fp + fs f + ns.sum + bufs.sum ∧ Disj q (bufs.sum, bufBase fs lp fp f ns) := by
  intro q hq
  unfold kidPos at hq
  unfold Disj
  split at hq
  · rename_i hl
    rcases List.eq_nil_or_concat ns with rfl | ⟨l, b, rfl⟩
    · simp at hq
    · rw [List.concat_eq_append] at hq ⊢
      simp only [List.dropLast_concat, List.getLast?_concat, Option.toList_some, List.map_cons,
        List.map_nil] at hq
      rw [List.zip_append length_bases.symm, List.mem_append] at hq
      have hb : bufBase fs lp fp f (l ++ [b]) = fp + fs f + b := by simp [bufBase, hl]
      simp only [List.sum_append, List.sum_cons, List.sum_nil, hb] at hq ⊢
      rcases hq with hq | hq
      · have := bases_zip hq; omega
      · simp only [List.zip_cons_cons, List.zip_nil_right, List.mem_singleton] at hq
        subst hq; simp only; omega
  · rename_i hl
    have hb : bufBase fs lp fp f ns = fp + fs f := by simp [bufBase, hl]
    have := bases_zip hq
    rw [hb] at this ⊢
    omega

/-- The callees' regions are pairwise disjoint. -/
theorem kidPos_pairwise (fp : ℕ) (f : String) (bufs ns : List ℕ) :
    (ns.zip (kidPos fs lp fp f bufs ns)).Pairwise Disj := by
  unfold kidPos
  split
  · rename_i hl
    rcases List.eq_nil_or_concat ns with rfl | ⟨l, b, rfl⟩
    · simp
    · rw [List.concat_eq_append]
      simp only [List.dropLast_concat, List.getLast?_concat, Option.toList_some, List.map_cons,
        List.map_nil]
      rw [List.zip_append length_bases.symm, List.pairwise_append]
      have hb : bufBase fs lp fp f (l ++ [b]) = fp + fs f + b := by simp [bufBase, hl]
      refine ⟨bases_pairwise.imp fun h => Or.inl h, by simp, fun q hq q' hq' => ?_⟩
      simp only [List.zip_cons_cons, List.zip_nil_right, List.mem_singleton] at hq'
      subst hq'
      have := bases_zip hq
      rw [hb] at this
      exact Or.inr (by simp only; omega)
  · exact bases_pairwise.imp fun h => Or.inl h

/-! ## Placement -/

variable {H : Inst → ℕ → E × E}

theorem insts_node {f : String} {σ : Val} {bufs : List ℕ} {kids : List Tree} {fp : ℕ}
    {hdr : E × E} :
    (Tree.node f σ bufs kids).insts fs lp H fp hdr =
      let I : Inst := ⟨.node f σ bufs kids, fp, hdr, kidPos fs lp fp f bufs (kids.map (Tree.total fs)),
        bases (bufBase fs lp fp f (kids.map (Tree.total fs))) bufs⟩
      I :: Tree.instsKids fs lp H I 0 (kidPos fs lp fp f bufs (kids.map (Tree.total fs))) kids := by
  rw [Tree.insts]

theorem insts_phantom {f : String} {σ : Val} {fp : ℕ} {hdr : E × E} :
    (Tree.phantom f σ).insts fs lp H fp hdr = [⟨.phantom f σ, fp, hdr, [], []⟩] := by
  rw [Tree.insts]

theorem instsKids_cons {I : Inst} {i p : ℕ} {ps : List ℕ} {k : Tree} {ks : List Tree} :
    Tree.instsKids fs lp H I i (p :: ps) (k :: ks) =
      k.insts fs lp H p (H I i) ++ Tree.instsKids fs lp H I (i + 1) ps ks := by
  rw [Tree.instsKids]

theorem instsKids_nil {I : Inst} {i : ℕ} {ps : List ℕ} : Tree.instsKids fs lp H I i ps [] = [] := by
  rw [Tree.instsKids]

theorem instsKids_nil_left {I : Inst} {i : ℕ} {ks : List Tree} :
    Tree.instsKids fs lp H I i [] ks = [] := by
  cases ks <;> rw [Tree.instsKids]

/-- The head of a node's instances is the node. -/
theorem head_insts (t : Tree) (fp : ℕ) (hdr : E × E) :
    ∃ I rest, t.insts fs lp H fp hdr = I :: rest ∧ I.t = t ∧ I.fp = fp ∧ I.hdr = hdr := by
  cases t with
  | node f σ bufs kids => exact ⟨_, _, insts_node, rfl, rfl, rfl⟩
  | phantom f σ => exact ⟨_, _, insts_phantom, rfl, rfl, rfl⟩

mutual
/-- **Within its region**: every word an instance of a subtree at `fp` owns is in
`[fp, fp + total)`. -/
theorem insts_within : ∀ (t : Tree) (fp : ℕ) (hdr : E × E), ∀ I ∈ t.insts fs lp H fp hdr,
    ∀ i, I.Owns fs i → fp ≤ i ∧ i < fp + t.total fs
  | .node f σ bufs kids, fp, hdr, I, hI, i, hi => by
      rw [insts_node, List.mem_cons] at hI
      rw [total_node, totalKids_eq_sum]
      have hbb := bufBase_le (fs := fs) (lp := lp) fp f bufs (kids.map (Tree.total fs))
      rcases hI with rfl | hI
      · simp only [Inst.Owns, Inst.Frame, Inst.Buf, Tree.name, Tree.bufs] at hi
        rcases hi with ⟨h1, h2⟩ | ⟨q, hq, h1, h2⟩
        · omega
        · have := bases_zip hq; omega
      · obtain ⟨q, hq, h1, h2⟩ := instsKids_within kids _ _ _ I hI i hi
        have := kidPos_regions (fs := fs) (lp := lp) fp f bufs _ q hq
        omega
  | .phantom f σ, fp, hdr, I, hI, i, hi => by
      rw [insts_phantom, List.mem_singleton] at hI
      subst hI
      rw [Tree.total]
      rcases hi with ⟨h1, h2⟩ | ⟨q, hq, -⟩
      · exact ⟨h1, h2⟩
      · simp at hq

/-- `insts_within` for the callees at `ps`: every word one owns is in its callee's region. -/
theorem instsKids_within : ∀ (ks : List Tree) (ps : List ℕ) (I : Inst) (j : ℕ),
    ∀ J ∈ Tree.instsKids fs lp H I j ps ks, ∀ i, J.Owns fs i →
      ∃ q ∈ (ks.map (Tree.total fs)).zip ps, q.2 ≤ i ∧ i < q.2 + q.1
  | [], _, _, _, J, hJ, _, _ => by rw [instsKids_nil] at hJ; exact (List.not_mem_nil hJ).elim
  | _ :: _, [], _, _, J, hJ, _, _ => by
      rw [instsKids_nil_left] at hJ; exact (List.not_mem_nil hJ).elim
  | k :: ks, p :: ps, I, j, J, hJ, i, hi => by
      rw [instsKids_cons, List.mem_append] at hJ
      simp only [List.map_cons, List.zip_cons_cons, List.mem_cons, exists_eq_or_imp]
      rcases hJ with hJ | hJ
      · have := insts_within k _ _ J hJ i hi; exact Or.inl ⟨this.1, this.2⟩
      · exact Or.inr (instsKids_within ks ps I (j + 1) J hJ i hi)
end

mutual
/-- **Disjointness**: two instances of a subtree own no word in common. -/
theorem insts_pairwise : ∀ (t : Tree) (fp : ℕ) (hdr : E × E),
    (t.insts fs lp H fp hdr).Pairwise (Inst.Apart fs)
  | .node f σ bufs kids, fp, hdr => by
      rw [insts_node]
      refine List.Pairwise.cons (fun J hJ i hI hJi => ?_)
        (instsKids_pairwise kids _ _ 0 (kidPos_pairwise fp f bufs _))
      obtain ⟨q, hq, h1, h2⟩ := instsKids_within kids _ _ _ J hJ i hJi
      have := kidPos_regions (fs := fs) (lp := lp) fp f bufs _ q hq
      unfold Disj at this
      simp only [Inst.Owns, Inst.Frame, Inst.Buf, Tree.name, Tree.bufs] at hI
      rcases hI with ⟨-, h⟩ | ⟨q', hq', h1', h2'⟩
      · omega
      · have := bases_zip hq'; omega
  | .phantom f σ, fp, hdr => by
      rw [insts_phantom]
      exact List.pairwise_singleton _ _

/-- `insts_pairwise` for the callees at `ps`, their regions disjoint. -/
theorem instsKids_pairwise : ∀ (ks : List Tree) (ps : List ℕ) (I : Inst) (j : ℕ),
    ((ks.map (Tree.total fs)).zip ps).Pairwise Disj →
      (Tree.instsKids fs lp H I j ps ks).Pairwise (Inst.Apart fs)
  | [], _, _, _, _ => by rw [instsKids_nil]; exact List.Pairwise.nil
  | _ :: _, [], _, _, _ => by rw [instsKids_nil_left]; exact List.Pairwise.nil
  | k :: ks, p :: ps, I, j, hd => by
      simp only [List.map_cons, List.zip_cons_cons, List.pairwise_cons] at hd
      rw [instsKids_cons, List.pairwise_append]
      refine ⟨insts_pairwise k _ _, instsKids_pairwise ks ps I (j + 1) hd.2,
        fun J hJ J' hJ' i hi hi' => ?_⟩
      have h1 := insts_within k _ _ J hJ i hi
      obtain ⟨q, hq, h2, h3⟩ := instsKids_within ks ps I (j + 1) J' hJ' i hi'
      have := hd.1 q hq
      unfold Disj at this
      simp only at this
      omega
end

/-- An instance placed as the allocator places it: its callees' frames and its `HeapBuf`s where
`Tree.insts` puts them. -/
def Inst.Placed (fs : String → ℕ) (lp : String → Bool) (I : Inst) : Prop :=
  I.kidFps = kidPos fs lp I.fp I.t.name I.t.bufs (I.t.kids.map (Tree.total fs)) ∧
    I.bufBases = bases (bufBase fs lp I.fp I.t.name (I.t.kids.map (Tree.total fs))) I.t.bufs

mutual
/-- Every instance is placed. -/
theorem insts_placed : ∀ (t : Tree) (fp : ℕ) (hdr : E × E), ∀ I ∈ t.insts fs lp H fp hdr,
    I.Placed fs lp
  | .node f σ bufs kids, fp, hdr, I, hI => by
      rw [insts_node, List.mem_cons] at hI
      rcases hI with rfl | hI
      · exact ⟨rfl, rfl⟩
      · exact instsKids_placed kids _ _ 0 I hI
  | .phantom f σ, fp, hdr, I, hI => by
      rw [insts_phantom, List.mem_singleton] at hI
      subst hI
      refine ⟨?_, rfl⟩
      simp only [Tree.kids, List.map_nil, Tree.bufs, kidPos, bases, List.dropLast_nil,
        List.getLast?_nil, Option.toList_none, List.map_nil, List.append_nil, ite_self]

/-- `insts_placed` for the callees. -/
theorem instsKids_placed : ∀ (ks : List Tree) (ps : List ℕ) (I : Inst) (j : ℕ),
    ∀ J ∈ Tree.instsKids fs lp H I j ps ks, J.Placed fs lp
  | [], _, _, _, J, hJ => by rw [instsKids_nil] at hJ; exact (List.not_mem_nil hJ).elim
  | _ :: _, [], _, _, J, hJ => by rw [instsKids_nil_left] at hJ; exact (List.not_mem_nil hJ).elim
  | k :: ks, p :: ps, I, j, J, hJ => by
      rw [instsKids_cons, List.mem_append] at hJ
      rcases hJ with hJ | hJ
      · exact insts_placed k _ _ J hJ
      · exact instsKids_placed ks ps I (j + 1) J hJ
end

/-- The frame and the `HeapBuf`s of a placed instance are disjoint. -/
theorem Inst.Placed.frame_buf {I : Inst} (h : I.Placed fs lp) {i : ℕ} (hF : I.Frame fs i) :
    ¬ I.Buf i := by
  rintro ⟨q, hq, h1, -⟩
  rw [h.2] at hq
  have := bases_zip hq
  have := (bufBase_le (fs := fs) (lp := lp) I.fp I.t.name I.t.bufs
    (I.t.kids.map (Tree.total fs))).1
  exact absurd hF.2 (by omega)

/-- **A loop's next iteration follows its frame**: a loop helper's last callee, its tail call, is
at `fp · g^S`. -/
theorem Inst.Placed.kidFps_getLast? {I : Inst} (h : I.Placed fs lp) (hl : lp I.t.name = true)
    (hk : I.t.kids ≠ []) : I.kidFps.getLast? = some (I.fp + fs I.t.name) := by
  rw [h.1, kidPos, ite_eq_left hl]
  rcases List.eq_nil_or_concat (I.t.kids.map (Tree.total fs)) with he | ⟨l, b, he⟩
  · exact absurd (List.map_eq_nil_iff.mp he) hk
  · rw [he]
    simp [List.concat_eq_append]

/-- The `i`-th callee at `ps` is an instance at `ps[i]`, with header `H I (j + i)`. -/
theorem instsKids_kid : ∀ (ks : List Tree) (ps : List ℕ) (I : Inst) (j i : ℕ) {k : Tree} {p : ℕ},
    ks[i]? = some k → ps[i]? = some p →
    ∃ J ∈ Tree.instsKids fs lp H I j ps ks, J.t = k ∧ J.fp = p ∧ J.hdr = H I (j + i)
  | [], _, _, _, _, _, _, h, _ => by simp at h
  | _ :: _, [], _, _, _, _, _, _, h => by simp at h
  | k' :: ks, p' :: ps, I, j, 0, k, p, h, h' => by
      obtain rfl : k' = k := by simpa using h
      obtain rfl : p' = p := by simpa using h'
      obtain ⟨J, rest, he, ht, hfp, hh⟩ := head_insts (fs := fs) (lp := lp) (H := H) k' p' (H I j)
      refine ⟨J, ?_, ht, hfp, by rw [hh, Nat.add_zero]⟩
      rw [instsKids_cons, he]; exact List.mem_append_left _ List.mem_cons_self
  | k' :: ks, p' :: ps, I, j, i + 1, k, p, h, h' => by
      obtain ⟨J, hJ, ht, hfp, hh⟩ :=
        instsKids_kid ks ps I (j + 1) i (by simpa using h) (by simpa using h')
      refine ⟨J, ?_, ht, hfp, by rw [hh]; congr 1; omega⟩
      rw [instsKids_cons]
      exact List.mem_append_right _ hJ

mutual
/-- **Callees are instances**: the `i`-th callee of an instance is an instance at the `i`-th
callee frame, with header `H I i`. -/
theorem insts_kid : ∀ (t : Tree) (fp : ℕ) (hdr : E × E), ∀ I ∈ t.insts fs lp H fp hdr,
    ∀ (i : ℕ) (k : Tree), I.t.kids[i]? = some k →
      ∃ J ∈ t.insts fs lp H fp hdr, J.t = k ∧ I.kidFps[i]? = some J.fp ∧ J.hdr = H I i
  | .node f σ bufs kids, fp, hdr, I, hI, i, k, hk => by
      rw [insts_node, List.mem_cons] at hI
      rcases hI with rfl | hI
      · have hi : i < (kidPos fs lp fp f bufs (kids.map (Tree.total fs))).length := by
          rw [length_kidPos, List.length_map]
          exact (List.getElem?_eq_some_iff.mp hk).1
        obtain ⟨p, hp⟩ : ∃ p, (kidPos fs lp fp f bufs (kids.map (Tree.total fs)))[i]? = some p :=
          ⟨_, List.getElem?_eq_getElem hi⟩
        obtain ⟨J, hJ, ht, hfp, hh⟩ := instsKids_kid (fs := fs) (lp := lp) (H := H) kids _ _ 0 i hk hp
        refine ⟨J, ?_, ht, by rw [hfp]; exact hp, by simpa using hh⟩
        rw [insts_node]; exact List.mem_cons_of_mem _ hJ
      · obtain ⟨J, hJ, h⟩ := instsKids_kids_kid kids _ _ 0 I hI i k hk
        refine ⟨J, ?_, h⟩
        rw [insts_node]; exact List.mem_cons_of_mem _ hJ
  | .phantom f σ, fp, hdr, I, hI, i, k, hk => by
      rw [insts_phantom, List.mem_singleton] at hI
      subst hI
      simp [Tree.kids] at hk

/-- `insts_kid` for the callees. -/
theorem instsKids_kids_kid : ∀ (ks : List Tree) (ps : List ℕ) (I : Inst) (j : ℕ),
    ∀ J ∈ Tree.instsKids fs lp H I j ps ks, ∀ (i : ℕ) (k : Tree), J.t.kids[i]? = some k →
      ∃ J' ∈ Tree.instsKids fs lp H I j ps ks, J'.t = k ∧ J.kidFps[i]? = some J'.fp ∧
        J'.hdr = H J i
  | [], _, _, _, J, hJ, _, _, _ => by rw [instsKids_nil] at hJ; exact (List.not_mem_nil hJ).elim
  | _ :: _, [], _, _, J, hJ, _, _, _ => by
      rw [instsKids_nil_left] at hJ; exact (List.not_mem_nil hJ).elim
  | k' :: ks, p :: ps, I, j, J, hJ, i, k, hk => by
      rw [instsKids_cons, List.mem_append] at hJ
      rw [instsKids_cons]
      rcases hJ with hJ | hJ
      · obtain ⟨J', hJ', h⟩ := insts_kid k' _ _ J hJ i k hk
        exact ⟨J', List.mem_append_left _ hJ', h⟩
      · obtain ⟨J', hJ', h⟩ := instsKids_kids_kid ks ps I (j + 1) J hJ i k hk
        exact ⟨J', List.mem_append_right _ hJ', h⟩
end

/-! ## Size -/

mutual
/-- The call instances of a subtree, phantoms included. -/
def Tree.count : Tree → ℕ
  | .node _ _ _ kids => 1 + Tree.countKids kids
  | .phantom .. => 1

/-- `Tree.count` of a list of subtrees. -/
def Tree.countKids : List Tree → ℕ
  | [] => 0
  | k :: ks => k.count + Tree.countKids ks
end

mutual
/-- The `HeapBuf` words of a subtree. -/
def Tree.bufWords : Tree → ℕ
  | .node _ _ bufs kids => bufs.sum + Tree.bufWordsKids kids
  | .phantom .. => 0

/-- `Tree.bufWords` of a list of subtrees. -/
def Tree.bufWordsKids : List Tree → ℕ
  | [] => 0
  | k :: ks => k.bufWords + Tree.bufWordsKids ks
end

mutual
/-- **The words allocated**: at most the largest frame per instance, and the `HeapBuf`s. -/
theorem total_le {F : ℕ} (hF : ∀ f, fs f ≤ F) : ∀ t : Tree, t.total fs ≤ F * t.count + t.bufWords
  | .node f σ bufs kids => by
      rw [total_node, Tree.count, Tree.bufWords, Nat.mul_add]
      have := totalKids_le hF kids
      have := hF f
      omega
  | .phantom f σ => by
      rw [Tree.total, Tree.count, Tree.bufWords]
      have := hF f
      omega

/-- `total_le` for the callees. -/
theorem totalKids_le {F : ℕ} (hF : ∀ f, fs f ≤ F) :
    ∀ ks : List Tree, Tree.totalKids fs ks ≤ F * Tree.countKids ks + Tree.bufWordsKids ks
  | [] => by rw [Tree.totalKids, Tree.countKids, Tree.bufWordsKids]; omega
  | k :: ks => by
      rw [totalKids_cons, Tree.countKids, Tree.bufWordsKids, Nat.mul_add]
      have := total_le hF k
      have := totalKids_le hF ks
      omega
end

mutual
/-- The allocator places one instance per call instance. -/
theorem length_insts : ∀ (t : Tree) (fp : ℕ) (hdr : E × E), (t.insts fs lp H fp hdr).length = t.count
  | .node f σ bufs kids, fp, hdr => by
      rw [insts_node, Tree.count, List.length_cons,
        length_instsKids kids _ _ 0 (by rw [length_kidPos, List.length_map])]
      omega
  | .phantom f σ, fp, hdr => by rw [insts_phantom, Tree.count]; rfl

/-- `length_insts` for the callees. -/
theorem length_instsKids : ∀ (ks : List Tree) (ps : List ℕ) (I : Inst) (j : ℕ), ps.length = ks.length →
    (Tree.instsKids fs lp H I j ps ks).length = Tree.countKids ks
  | [], _, _, _, _ => by rw [instsKids_nil, Tree.countKids]; rfl
  | _ :: _, [], _, _, h => absurd h (by simp)
  | k :: ks, p :: ps, I, j, h => by
      rw [instsKids_cons, List.length_append, length_insts, Tree.countKids,
        length_instsKids ks ps I (j + 1) (by simpa using h)]
end

/-! ## Frame writes -/

/-- A frame's cells by offset: `fp[0]`, `fp[1]` its header, then `C I`. -/
def Inst.cells (C : Inst → List (ℕ × E)) (I : Inst) : List (ℕ × E) :=
  (0, I.hdr.1) :: (1, I.hdr.2) :: C I

/-- A frame's writes. -/
def Inst.writes (C : Inst → List (ℕ × E)) (I : Inst) : List Write :=
  (I.cells C).map fun q => (gpow (I.fp + q.1), q.2)

/-- The writes of the frames of the instances. -/
def frameWrites (C : Inst → List (ℕ × E)) (Is : List Inst) : List Write := Is.flatMap (Inst.writes C)

/-- What the cells of the frames must satisfy: the header fits the frame, every cell is past
the header and in the frame, and two cells at one offset hold one word. -/
structure CellsOk (fs : String → ℕ) (C : Inst → List (ℕ × E)) (Is : List Inst) : Prop where
  two_le : ∀ I ∈ Is, 2 ≤ fs I.t.name
  off : ∀ I ∈ Is, ∀ q ∈ C I, 2 ≤ q.1 ∧ q.1 < fs I.t.name
  agree : ∀ I ∈ Is, ∀ q ∈ C I, ∀ q' ∈ C I, q.1 = q'.1 → q.2 = q'.2

variable {C : Inst → List (ℕ × E)} {Is : List Inst}

theorem CellsOk.cell_lt (h : CellsOk fs C Is) {I : Inst} (hI : I ∈ Is) {q : ℕ × E}
    (hq : q ∈ I.cells C) : q.1 < fs I.t.name := by
  have := h.two_le I hI
  simp only [Inst.cells, List.mem_cons] at hq
  rcases hq with rfl | rfl | hq
  · simp only; omega
  · simp only; omega
  · exact (h.off I hI q hq).2

theorem CellsOk.cells_agree (h : CellsOk fs C Is) {I : Inst} (hI : I ∈ Is) {q q' : ℕ × E}
    (hq : q ∈ I.cells C) (hq' : q' ∈ I.cells C) (he : q.1 = q'.1) : q.2 = q'.2 := by
  simp only [Inst.cells, List.mem_cons] at hq hq'
  have hoff := h.off I hI
  rcases hq with rfl | rfl | hq <;> rcases hq' with rfl | rfl | hq'
  · rfl
  · exact absurd (he : (0 : ℕ) = 1) (by omega)
  · have := (hoff _ hq').1; have he : (0 : ℕ) = q'.1 := he; omega
  · exact absurd (he : (1 : ℕ) = 0) (by omega)
  · rfl
  · have := (hoff _ hq').1; have he : (1 : ℕ) = q'.1 := he; omega
  · have := (hoff _ hq).1; have he : q.1 = 0 := he; omega
  · have := (hoff _ hq).1; have he : q.1 = 1 := he; omega
  · exact h.agree I hI _ hq _ hq' he

theorem mem_frameWrites {a : Write} (ha : a ∈ frameWrites C Is) :
    ∃ I ∈ Is, ∃ q ∈ I.cells C, a = (gpow (I.fp + q.1), q.2) := by
  obtain ⟨I, hI, ha⟩ := List.mem_flatMap.mp ha
  obtain ⟨q, hq, rfl⟩ := List.mem_map.mp ha
  exact ⟨I, hI, q, hq, rfl⟩

/-- **The frames are write-once consistent**: instances apart, below the order of `g`. -/
theorem frameWrites_consistent (hp : Is.Pairwise (Inst.Apart fs)) (hok : CellsOk fs C Is)
    (hb : ∀ I ∈ Is, I.fp + fs I.t.name ≤ 2 ^ 64 - 1) : Consistent (frameWrites C Is) := by
  intro a ha b hb' hab
  obtain ⟨I, hI, q, hq, rfl⟩ := mem_frameWrites ha
  obtain ⟨J, hJ, q', hq', rfl⟩ := mem_frameWrites hb'
  have hlt := hok.cell_lt hI hq
  have hlt' := hok.cell_lt hJ hq'
  have hbI := hb I hI
  have hbJ := hb J hJ
  have he : I.fp + q.1 = J.fp + q'.1 :=
    gpow_injOn (by simp only [Set.mem_Iio]; omega) (by simp only [Set.mem_Iio]; omega) hab
  by_cases hIJ : I = J
  · subst hIJ
    exact hok.cells_agree hI hq hq' (by omega)
  · exact absurd (Or.inl ⟨by omega, by omega⟩ : J.Owns fs (J.fp + q'.1))
      (he ▸ hp.forall hI hJ hIJ (I.fp + q.1) (Or.inl ⟨by omega, by omega⟩))

end
end LeanVM.Guest.Memory
