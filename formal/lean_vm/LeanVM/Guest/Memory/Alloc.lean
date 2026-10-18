/-
  LeanVM.Guest.Memory.Alloc

  The bump allocator of an honest evaluation: every call instance's frame and `HeapBuf`s in one
  contiguous region per subtree, the regions of distinct instances disjoint, a loop's next
  iteration in the frame right after its own; and the frame writes, consistent by
  disjointness.
-/

module

public import LeanVM.Guest.Memory.Eval
public import LeanVM.Guest.Memory.Image

/-!
# Placing a call tree

Frame sizes are a parameter `fs` (the compiler's, from the certificate). A call instance placed
at word `fp` occupies, in order: its frame `[fp, fp + fs f)`, then its callees' regions, the
**last callee first**, each subtree contiguous, then its `HeapBuf`s one after another. So a
subtree of `total` words occupies `[fp, fp + total)`, and the last callee's frame is at
`fp + fs f`: a `mul_range` helper's tail call (`callIf`, its last call, a phantom on the last
iteration) is the frame its code addresses as `fp · g^S` (`Inst.Placed.kidFps_getLast?`).

The Rust runner allocates in execution order instead (`cpu/execute.rs`, `next_free` from the
end of `main`'s frame): a callee frame when its call is set up, a loop's `n + 1` frames at once,
a dispatch's frame at the largest arm's size, a `HeapBuf` when its hint runs. Completeness needs
only disjointness, which this order gives by construction.

`Tree.insts fs H fp hdr t` lists the placed call instances (`Inst`): the tree, its frame, its
header words `fp[0]`, `fp[1]`, its callees' frames and its `HeapBuf` bases; a callee's header is
`H I i`, a function of the caller and the call's index (the return registers, or the caller's
own for a tail call). `insts_within` and `insts_pairwise`: every instance owns words of its
subtree's region only, and two instances own no word in common. `frameWrites_consistent`: the
headers and cells of all frames are consistent writes.
-/

namespace LeanVM.Guest.Memory

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core

@[expose] public section

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

variable (fs : String → ℕ)

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

/-- The regions of callees placed from `b`, the last first. -/
def kidBases (b : ℕ) : List Tree → List ℕ
  | [] => []
  | _ :: ks => (b + Tree.totalKids fs ks) :: kidBases b ks

/-- Regions of the sizes `ss`, one after another from `b`. -/
def bases (b : ℕ) : List ℕ → List ℕ
  | [] => []
  | s :: ss => b :: bases (b + s) ss

mutual
/-- **The bump allocator**: the call instances of a subtree whose frame is at `fp`. -/
def Tree.insts (H : Inst → ℕ → E × E) (fp : ℕ) (hdr : E × E) : Tree → List Inst
  | t@(.node f _ bufs kids) =>
      let I : Inst := ⟨t, fp, hdr, kidBases fs (fp + fs f) kids,
        bases (fp + fs f + Tree.totalKids fs kids) bufs⟩
      I :: Tree.instsKids H I 0 (fp + fs f) kids
  | t@(.phantom ..) => [⟨t, fp, hdr, [], []⟩]

/-- The call instances of the callees `ks` of `I` from its `i`-th, placed from `b`. -/
def Tree.instsKids (H : Inst → ℕ → E × E) (I : Inst) (i b : ℕ) : List Tree → List Inst
  | [] => []
  | k :: ks => k.insts H (b + Tree.totalKids fs ks) (H I i) ++ Tree.instsKids H I (i + 1) b ks
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

variable {fs}

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

/-- The `HeapBuf`s of one instance are disjoint, in order. -/
theorem bases_pairwise : ∀ {b : ℕ} {ss : List ℕ},
    (ss.zip (bases b ss)).Pairwise fun q q' => q.2 + q.1 ≤ q'.2
  | _, [] => List.Pairwise.nil
  | b, s :: ss => by
      simp only [bases, List.zip_cons_cons, List.pairwise_cons]
      exact ⟨fun q hq => (bases_zip hq).1, bases_pairwise⟩

theorem length_bases : ∀ {b : ℕ} {ss : List ℕ}, (bases b ss).length = ss.length
  | _, [] => rfl
  | _, _ :: _ => by simp [bases, length_bases]

theorem length_kidBases : ∀ {b : ℕ} {ks : List Tree}, (kidBases fs b ks).length = ks.length
  | _, [] => rfl
  | _, _ :: _ => by simp [kidBases, length_kidBases]

theorem totalKids_cons (k : Tree) (ks : List Tree) :
    Tree.totalKids fs (k :: ks) = k.total fs + Tree.totalKids fs ks := by
  rw [Tree.totalKids]

theorem total_node (f : String) (σ : Val) (bufs : List ℕ) (kids : List Tree) :
    (Tree.node f σ bufs kids).total fs = fs f + Tree.totalKids fs kids + bufs.sum := by
  rw [Tree.total]

theorem le_total (t : Tree) : fs t.name ≤ t.total fs := by
  cases t with
  | node f σ bufs kids => rw [total_node]; simp only [Tree.name]; omega
  | phantom f σ => rw [Tree.total]; rfl

/-! ## Placement -/

variable {H : Inst → ℕ → E × E}

theorem insts_node {f : String} {σ : Val} {bufs : List ℕ} {kids : List Tree} {fp : ℕ}
    {hdr : E × E} :
    (Tree.node f σ bufs kids).insts fs H fp hdr =
      let I : Inst := ⟨.node f σ bufs kids, fp, hdr, kidBases fs (fp + fs f) kids,
        bases (fp + fs f + Tree.totalKids fs kids) bufs⟩
      I :: Tree.instsKids fs H I 0 (fp + fs f) kids := by
  rw [Tree.insts]

theorem insts_phantom {f : String} {σ : Val} {fp : ℕ} {hdr : E × E} :
    (Tree.phantom f σ).insts fs H fp hdr = [⟨.phantom f σ, fp, hdr, [], []⟩] := by
  rw [Tree.insts]

theorem instsKids_cons {I : Inst} {i b : ℕ} {k : Tree} {ks : List Tree} :
    Tree.instsKids fs H I i b (k :: ks) =
      k.insts fs H (b + Tree.totalKids fs ks) (H I i) ++ Tree.instsKids fs H I (i + 1) b ks := by
  rw [Tree.instsKids]

theorem instsKids_nil {I : Inst} {i b : ℕ} : Tree.instsKids fs H I i b [] = [] := by
  rw [Tree.instsKids]

/-- The head of a node's instances is the node. -/
theorem head_insts (t : Tree) (fp : ℕ) (hdr : E × E) :
    ∃ I rest, t.insts fs H fp hdr = I :: rest ∧ I.t = t ∧ I.fp = fp ∧ I.hdr = hdr := by
  cases t with
  | node f σ bufs kids => exact ⟨_, _, insts_node, rfl, rfl, rfl⟩
  | phantom f σ => exact ⟨_, _, insts_phantom, rfl, rfl, rfl⟩

mutual
/-- **Within its region**: every word an instance of a subtree at `fp` owns is in
`[fp, fp + total)`. -/
theorem insts_within : ∀ (t : Tree) (fp : ℕ) (hdr : E × E), ∀ I ∈ t.insts fs H fp hdr,
    ∀ i, I.Owns fs i → fp ≤ i ∧ i < fp + t.total fs
  | .node f σ bufs kids, fp, hdr, I, hI, i, hi => by
      rw [insts_node, List.mem_cons] at hI
      rw [total_node]
      rcases hI with rfl | hI
      · simp only [Inst.Owns, Inst.Frame, Inst.Buf, Tree.name, Tree.bufs] at hi
        rcases hi with ⟨h1, h2⟩ | ⟨q, hq, h1, h2⟩
        · omega
        · have := bases_zip hq; omega
      · have := instsKids_within kids (I := ⟨.node f σ bufs kids, fp, hdr,
          kidBases fs (fp + fs f) kids, bases (fp + fs f + Tree.totalKids fs kids) bufs⟩)
          0 (fp + fs f) I hI i hi
        omega
  | .phantom f σ, fp, hdr, I, hI, i, hi => by
      rw [insts_phantom, List.mem_singleton] at hI
      subst hI
      rw [Tree.total]
      rcases hi with ⟨h1, h2⟩ | ⟨q, hq, -⟩
      · exact ⟨h1, h2⟩
      · simp at hq

/-- `insts_within` for the callees placed from `b`. -/
theorem instsKids_within : ∀ (ks : List Tree) {I : Inst} (j b : ℕ), ∀ J ∈ Tree.instsKids fs H I j b ks,
    ∀ i, J.Owns fs i → b ≤ i ∧ i < b + Tree.totalKids fs ks
  | [], _, _, _, J, hJ, _, _ => by rw [instsKids_nil] at hJ; exact (List.not_mem_nil hJ).elim
  | k :: ks, I, j, b, J, hJ, i, hi => by
      rw [instsKids_cons, List.mem_append] at hJ
      rw [totalKids_cons]
      rcases hJ with hJ | hJ
      · have := insts_within k _ _ J hJ i hi; omega
      · have := instsKids_within ks (I := I) (j + 1) b J hJ i hi; omega
end

mutual
/-- **Disjointness**: two instances of a subtree own no word in common. -/
theorem insts_pairwise : ∀ (t : Tree) (fp : ℕ) (hdr : E × E),
    (t.insts fs H fp hdr).Pairwise (Inst.Apart fs)
  | .node f σ bufs kids, fp, hdr => by
      rw [insts_node]
      refine List.Pairwise.cons (fun J hJ i hI hJi => ?_) (instsKids_pairwise kids 0 (fp + fs f))
      have hJ' := instsKids_within kids 0 (fp + fs f) J hJ i hJi
      simp only [Inst.Owns, Inst.Frame, Inst.Buf, Tree.name, Tree.bufs] at hI
      rcases hI with ⟨-, h2⟩ | ⟨q, hq, h1, -⟩
      · omega
      · have := bases_zip hq; omega
  | .phantom f σ, fp, hdr => by
      rw [insts_phantom]
      exact List.pairwise_singleton _ _

/-- `insts_pairwise` for the callees placed from `b`. -/
theorem instsKids_pairwise : ∀ (ks : List Tree) {I : Inst} (j b : ℕ),
    (Tree.instsKids fs H I j b ks).Pairwise (Inst.Apart fs)
  | [], _, _, _ => by rw [instsKids_nil]; exact List.Pairwise.nil
  | k :: ks, I, j, b => by
      rw [instsKids_cons, List.pairwise_append]
      refine ⟨insts_pairwise k _ _, instsKids_pairwise ks (j + 1) b, fun J hJ J' hJ' i hi hi' => ?_⟩
      have h1 := insts_within k _ _ J hJ i hi
      have h2 := instsKids_within ks (I := I) (j + 1) b J' hJ' i hi'
      omega
end

/-- An instance placed as the allocator places it: its callees' frames and its `HeapBuf`s where
`Tree.insts` puts them. -/
def Inst.Placed (fs : String → ℕ) (I : Inst) : Prop :=
  I.kidFps = kidBases fs (I.fp + fs I.t.name) I.t.kids ∧
    I.bufBases = bases (I.fp + fs I.t.name + Tree.totalKids fs I.t.kids) I.t.bufs

mutual
/-- Every instance is placed. -/
theorem insts_placed : ∀ (t : Tree) (fp : ℕ) (hdr : E × E), ∀ I ∈ t.insts fs H fp hdr,
    I.Placed fs
  | .node f σ bufs kids, fp, hdr, I, hI => by
      rw [insts_node, List.mem_cons] at hI
      rcases hI with rfl | hI
      · exact ⟨rfl, rfl⟩
      · exact instsKids_placed kids 0 (fp + fs f) I hI
  | .phantom f σ, fp, hdr, I, hI => by
      rw [insts_phantom, List.mem_singleton] at hI
      subst hI
      exact ⟨rfl, rfl⟩

/-- `insts_placed` for the callees. -/
theorem instsKids_placed : ∀ (ks : List Tree) {I : Inst} (j b : ℕ), ∀ J ∈ Tree.instsKids fs H I j b ks,
    J.Placed fs
  | [], _, _, _, J, hJ => by rw [instsKids_nil] at hJ; exact (List.not_mem_nil hJ).elim
  | k :: ks, I, j, b, J, hJ => by
      rw [instsKids_cons, List.mem_append] at hJ
      rcases hJ with hJ | hJ
      · exact insts_placed k _ _ J hJ
      · exact instsKids_placed ks (I := I) (j + 1) b J hJ
end

/-- The frame and the `HeapBuf`s of a placed instance are disjoint. -/
theorem Inst.Placed.frame_buf {I : Inst} (h : I.Placed fs) {i : ℕ} (hF : I.Frame fs i) :
    ¬ I.Buf i := by
  rintro ⟨q, hq, h1, -⟩
  rw [h.2] at hq
  have := bases_zip hq
  exact absurd hF.2 (by omega)

/-- The callees placed from `b`, the last at `b`. -/
theorem kidBases_getLast? : ∀ {b : ℕ} {ks : List Tree}, ks ≠ [] → (kidBases fs b ks).getLast? = some b
  | _, [], h => absurd rfl h
  | b, [k], _ => by simp [kidBases, Tree.totalKids]
  | b, k :: k' :: ks, _ => by
      rw [kidBases, List.getLast?_cons, kidBases_getLast? (List.cons_ne_nil k' ks)]
      rfl

/-- **The last callee's frame follows the caller's**: a loop's tail call at `fp · g^S`. -/
theorem Inst.Placed.kidFps_getLast? {I : Inst} (h : I.Placed fs) (hk : I.t.kids ≠ []) :
    I.kidFps.getLast? = some (I.fp + fs I.t.name) := by
  rw [h.1, kidBases_getLast? hk]

/-- The `i`-th callee placed from `b` is an instance at the `i`-th region, with header
`H I (j + i)`. -/
theorem instsKids_kid : ∀ (ks : List Tree) {I : Inst} (j b i : ℕ) {k : Tree}, ks[i]? = some k →
    ∃ J ∈ Tree.instsKids fs H I j b ks, J.t = k ∧ (kidBases fs b ks)[i]? = some J.fp ∧
      J.hdr = H I (j + i)
  | [], _, _, _, _, _, h => by simp at h
  | k' :: ks, I, j, b, 0, k, h => by
      obtain rfl : k' = k := by simpa using h
      obtain ⟨J, rest, he, ht, hfp, hh⟩ := head_insts (H := H) k' (b + Tree.totalKids fs ks) (H I j)
      refine ⟨J, ?_, ht, ?_, by rw [hh, Nat.add_zero]⟩
      · rw [instsKids_cons, he]; exact List.mem_append_left _ List.mem_cons_self
      · rw [kidBases, hfp]; rfl
  | k' :: ks, I, j, b, i + 1, k, h => by
      obtain ⟨J, hJ, ht, hfp, hh⟩ := instsKids_kid ks (I := I) (j + 1) b i (by simpa using h)
      refine ⟨J, ?_, ht, by simpa [kidBases] using hfp, by rw [hh]; congr 1; omega⟩
      rw [instsKids_cons]
      exact List.mem_append_right _ hJ

mutual
/-- **Callees are instances**: the `i`-th callee of an instance is an instance at the `i`-th
callee frame, with header `H I i`. -/
theorem insts_kid : ∀ (t : Tree) (fp : ℕ) (hdr : E × E), ∀ I ∈ t.insts fs H fp hdr,
    ∀ (i : ℕ) (k : Tree), I.t.kids[i]? = some k →
      ∃ J ∈ t.insts fs H fp hdr, J.t = k ∧ I.kidFps[i]? = some J.fp ∧ J.hdr = H I i
  | .node f σ bufs kids, fp, hdr, I, hI, i, k, hk => by
      rw [insts_node, List.mem_cons] at hI
      rcases hI with rfl | hI
      · obtain ⟨J, hJ, h⟩ := instsKids_kid (H := H) kids 0 (fp + fs f) i hk
        refine ⟨J, ?_, by simpa using h⟩
        rw [insts_node]; exact List.mem_cons_of_mem _ hJ
      · obtain ⟨J, hJ, h⟩ := instsKids_kids_kid kids 0 (fp + fs f) I hI i k hk
        refine ⟨J, ?_, h⟩
        rw [insts_node]; exact List.mem_cons_of_mem _ hJ
  | .phantom f σ, fp, hdr, I, hI, i, k, hk => by
      rw [insts_phantom, List.mem_singleton] at hI
      subst hI
      simp [Tree.kids] at hk

/-- `insts_kid` for the callees. -/
theorem instsKids_kids_kid : ∀ (ks : List Tree) {I : Inst} (j b : ℕ), ∀ J ∈ Tree.instsKids fs H I j b ks,
    ∀ (i : ℕ) (k : Tree), J.t.kids[i]? = some k →
      ∃ J' ∈ Tree.instsKids fs H I j b ks, J'.t = k ∧ J.kidFps[i]? = some J'.fp ∧ J'.hdr = H J i
  | [], _, _, _, J, hJ, _, _, _ => by rw [instsKids_nil] at hJ; exact (List.not_mem_nil hJ).elim
  | k' :: ks, I, j, b, J, hJ, i, k, hk => by
      rw [instsKids_cons, List.mem_append] at hJ
      rw [instsKids_cons]
      rcases hJ with hJ | hJ
      · obtain ⟨J', hJ', h⟩ := insts_kid k' _ _ J hJ i k hk
        exact ⟨J', List.mem_append_left _ hJ', h⟩
      · obtain ⟨J', hJ', h⟩ := instsKids_kids_kid ks (I := I) (j + 1) b J hJ i k hk
        exact ⟨J', List.mem_append_right _ hJ', h⟩
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
