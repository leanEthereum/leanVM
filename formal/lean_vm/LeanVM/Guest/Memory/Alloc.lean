/-
  LeanVM.Guest.Memory.Alloc

  The bump allocator of an honest evaluation, in the Rust runner's order: every call instance's
  frame, a loop's frames together at its entry, then the `HeapBuf`s and callees in execution
  order, each callee's subtree contiguous; the regions of distinct instances disjoint; and the
  frame writes, consistent by disjointness.
-/

module

public import LeanVM.Guest.Memory.Eval
public import LeanVM.Guest.Memory.Image

/-!
# Placing a call tree

Frame sizes are a parameter `fs` (the compiler's, from the certificate). The allocator places a
subtree at a position `p = (fp, c)`: its frame at word `fp`, its `HeapBuf`s and its callees'
subtrees from word `c`, one after another in call order. A subtree's **block** is the frames
placed at its call: its own frame, and for a **loop helper** (`Program.loop`: its body ends with a
`callIf` to itself and `ret []`) its tail call's block too, the next iteration's frame right after
its own (`fp · g^S`), the last a phantom. A callee entered fresh at word `b` is at `(b, b +
block)`: its block, then the rest of its subtree; a loop iteration's tail call is at `(fp + fs f,
c')`, `c'` after the iteration's other callees. So a subtree of `total` words at `(b, b + block)`
occupies `[b, b + total)`, a loop entered at `b` has its frames at `b + i · fs f` and the
iterations' callees after them, iteration `0`'s first, and an instance's `HeapBuf` pointers
depend only on its own position and sizes, never on its callees': a completeness proof fixes
them before it knows what its callees allocate.

This is the Rust runner's order (`cpu/execute.rs`, `next_free` from the end of `main`'s frame): a
callee frame when its call is set up, a loop's frames at once at its entry (`Hint::AllocLoopFrames`,
the untaken call's a whole frame), a `HeapBuf` with its frame. Completeness needs only
disjointness, which this order gives by construction; soundness assumes nothing of where frames
lie.

`Tree.insts fs lp H p hdr t` lists the placed call instances (`Inst`), `lp` saying which
functions are loop helpers: the tree, its frame and cursor, its header words `fp[0]`, `fp[1]`,
its callees' frames and its `HeapBuf` bases; a callee's header is `H I i`, a function of the
caller and the call's index (the return registers, or the caller's own for a tail call).
`insts_within` and `insts_pairwise`: every instance owns words of its subtree's region only
(`InReg`), and two instances own no word in common. `frameWrites_consistent`: the headers and
cells of all frames are consistent writes.
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
  /-- The first word of its `HeapBuf`s and callees' regions. -/
  cur : ℕ
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

mutual
/-- **A subtree's block**: the words of the frames placed at its call, its own and, for a loop
helper, its tail call's block. -/
def Tree.block : Tree → ℕ
  | .node f _ _ kids => fs f + if lp f then Tree.blockLast kids else 0
  | .phantom f _ => fs f

/-- The block of the last of a list of subtrees. -/
def Tree.blockLast : List Tree → ℕ
  | [] => 0
  | [k] => k.block
  | _ :: ks@(_ :: _) => Tree.blockLast ks
end

/-- A subtree's words and block. -/
def Tree.sz (t : Tree) : ℕ × ℕ := (t.total fs, t.block fs lp)

/-- Regions of the sizes `ss`, one after another from `b`. -/
def bases (b : ℕ) : List ℕ → List ℕ
  | [] => []
  | s :: ss => b :: bases (b + s) ss

/-- Subtrees of the sizes `ss` (words, block), one after another from `b`, each its block first. -/
def basesC (b : ℕ) : List (ℕ × ℕ) → List (ℕ × ℕ)
  | [] => []
  | s :: ss => (b, b + s.2) :: basesC (b + s.1) ss

/-- The block of the last of subtrees of sizes `ns`. -/
def lastBlock (ns : List (ℕ × ℕ)) : ℕ := (ns.getLast?.map Prod.snd).getD 0

/-- The block of an instance of `f` whose callees' subtrees have the sizes `ns`. -/
def nodeBlock (f : String) (ns : List (ℕ × ℕ)) : ℕ := fs f + if lp f then lastBlock ns else 0

/-- The callees' positions of an instance of `f` at `p` with `HeapBuf`s `bufs`, in call order, for
callee subtrees of sizes `ns`: one after another from the end of its `HeapBuf`s, a loop helper's
last callee, its tail call, at the next frame `p.1 + fs f` and its callees after the others'. -/
def kidPos (p : ℕ × ℕ) (f : String) (bufs : List ℕ) (ns : List (ℕ × ℕ)) : List (ℕ × ℕ) :=
  if lp f then
    basesC (p.2 + bufs.sum) ns.dropLast ++ ns.getLast?.toList.map fun _ =>
      (p.1 + fs f, p.2 + bufs.sum + (ns.dropLast.map Prod.fst).sum)
  else basesC (p.2 + bufs.sum) ns

mutual
/-- **The bump allocator**: the call instances of a subtree at `p`. -/
def Tree.insts (H : Inst → ℕ → E × E) (p : ℕ × ℕ) (hdr : E × E) : Tree → List Inst
  | t@(.node f _ bufs kids) =>
      let I : Inst := ⟨t, p.1, p.2, hdr,
        (kidPos fs lp p f bufs (kids.map (Tree.sz fs lp))).map Prod.fst, bases p.2 bufs⟩
      I :: Tree.instsKids H I 0 (kidPos fs lp p f bufs (kids.map (Tree.sz fs lp))) kids
  | t@(.phantom ..) => [⟨t, p.1, p.2, hdr, [], []⟩]

/-- The call instances of the callees `ks` of `I` from its `i`-th, at `ps`. -/
def Tree.instsKids (H : Inst → ℕ → E × E) (I : Inst) (i : ℕ) :
    List (ℕ × ℕ) → List Tree → List Inst
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

/-- **The region of a subtree** of sizes `s` (words, block) at `p`: its block from `p.1`, its other
`s.1 - s.2` words from `p.2`. -/
def InReg (s p : ℕ × ℕ) (i : ℕ) : Prop :=
  (p.1 ≤ i ∧ i < p.1 + s.2) ∨ (p.2 ≤ i ∧ i + s.2 < p.2 + s.1)

/-- Subtrees at `q` and `q'` (sizes, position) own no word in common. -/
def DisjR (q q' : (ℕ × ℕ) × (ℕ × ℕ)) : Prop := ∀ i, InReg q.1 q.2 i → ¬ InReg q'.1 q'.2 i

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

theorem length_basesC : ∀ {b : ℕ} {ss : List (ℕ × ℕ)}, (basesC b ss).length = ss.length
  | _, [] => rfl
  | _, _ :: _ => by simp [basesC, length_basesC]

theorem basesC_zip : ∀ {b : ℕ} {ss : List (ℕ × ℕ)} {q : (ℕ × ℕ) × (ℕ × ℕ)},
    q ∈ ss.zip (basesC b ss) →
    q.2.2 = q.2.1 + q.1.2 ∧ b ≤ q.2.1 ∧ q.2.1 + q.1.1 ≤ b + (ss.map Prod.fst).sum
  | _, [], _, h => (List.not_mem_nil h).elim
  | b, s :: ss, q, h => by
      simp only [basesC, List.zip_cons_cons, List.mem_cons] at h
      rcases h with rfl | h
      · simp only [List.map_cons, List.sum_cons]
        exact ⟨trivial, le_rfl, by omega⟩
      · have := basesC_zip h
        simp only [List.map_cons, List.sum_cons]; omega

theorem basesC_pairwise : ∀ {b : ℕ} {ss : List (ℕ × ℕ)},
    (ss.zip (basesC b ss)).Pairwise fun q q' => q.2.1 + q.1.1 ≤ q'.2.1
  | _, [] => List.Pairwise.nil
  | b, s :: ss => by
      simp only [basesC, List.zip_cons_cons, List.pairwise_cons]
      exact ⟨fun q hq => (basesC_zip hq).2.1, basesC_pairwise⟩

theorem zip_cons_hps {k : Tree} {ks : List Tree} {p : ℕ × ℕ} {ps : List (ℕ × ℕ)}
    (h : ∀ q ∈ ((k :: ks).map (Tree.sz fs lp)).zip (p :: ps), q.2.1 + q.1.2 ≤ q.2.2) :
    p.1 + k.block fs lp ≤ p.2 ∧ ∀ q ∈ (ks.map (Tree.sz fs lp)).zip ps, q.2.1 + q.1.2 ≤ q.2.2 :=
  ⟨h (Tree.sz fs lp k, p) (by simp), fun q hq => h q (by simp [hq])⟩

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

theorem map_sz_fst (ks : List Tree) : (ks.map (Tree.sz fs lp)).map Prod.fst = ks.map (Tree.total fs) := by
  simp [Tree.sz]

theorem sum_map_sz (ks : List Tree) :
    ((ks.map (Tree.sz fs lp)).map Prod.fst).sum = Tree.totalKids fs ks := by
  rw [map_sz_fst, totalKids_eq_sum]

theorem blockLast_eq : ∀ ks : List Tree, Tree.blockLast fs lp ks = lastBlock (ks.map (Tree.sz fs lp))
  | [] => by rw [Tree.blockLast]; rfl
  | [k] => by rw [Tree.blockLast]; rfl
  | _ :: k :: ks => by
      rw [Tree.blockLast, blockLast_eq (k :: ks)]
      simp [lastBlock, List.getLast?_cons_cons]

theorem block_node (f : String) (σ : Val) (bufs : List ℕ) (kids : List Tree) :
    (Tree.node f σ bufs kids).block fs lp = nodeBlock fs lp f (kids.map (Tree.sz fs lp)) := by
  rw [Tree.block, blockLast_eq]; rfl

theorem block_phantom (f : String) (σ : Val) : (Tree.phantom f σ).block fs lp = fs f := by
  rw [Tree.block]

theorem le_block (t : Tree) : fs t.name ≤ t.block fs lp := by
  cases t with
  | node f σ bufs kids => rw [Tree.block]; simp only [Tree.name]; omega
  | phantom f σ => rw [Tree.block]; rfl

/-- A subtree's block is within its words. -/
theorem block_le_total : ∀ t : Tree, t.block fs lp ≤ t.total fs
  | .node f σ bufs kids => by
      rw [Tree.block, total_node]
      have : Tree.blockLast fs lp kids ≤ Tree.totalKids fs kids := blockLast_le kids
      split <;> omega
  | .phantom f σ => by rw [Tree.block, Tree.total]
where
  blockLast_le : ∀ ks : List Tree, Tree.blockLast fs lp ks ≤ Tree.totalKids fs ks
    | [] => by rw [Tree.blockLast, Tree.totalKids]
    | [k] => by
        rw [Tree.blockLast, totalKids_cons, Tree.totalKids]
        have := block_le_total k
        omega
    | k :: k' :: ks => by
        rw [Tree.blockLast, totalKids_cons]
        have := blockLast_le (k' :: ks)
        omega

theorem sz_le (ks : List Tree) : ∀ s ∈ ks.map (Tree.sz fs lp), s.2 ≤ s.1 := by
  intro s hs
  obtain ⟨k, -, rfl⟩ := List.mem_map.mp hs
  exact block_le_total k

theorem lastBlock_le_sum (ns : List (ℕ × ℕ)) (hns : ∀ s ∈ ns, s.2 ≤ s.1) :
    lastBlock ns ≤ (ns.map Prod.fst).sum := by
  rcases List.eq_nil_or_concat ns with rfl | ⟨l, b, rfl⟩
  · simp [lastBlock]
  · have := hns b (by simp)
    simp [lastBlock, List.concat_eq_append, List.sum_append]
    omega

theorem length_kidPos (p : ℕ × ℕ) (f : String) (bufs : List ℕ) (ns : List (ℕ × ℕ)) :
    (kidPos fs lp p f bufs ns).length = ns.length := by
  unfold kidPos
  split
  · rcases List.eq_nil_or_concat ns with rfl | ⟨l, b, rfl⟩
    · simp [basesC]
    · simp [List.concat_eq_append, length_basesC]
  · exact length_basesC

/-- A loop helper's callees: the others from the end of its `HeapBuf`s, its tail call at the next
frame. -/
theorem kidPos_loop {p : ℕ × ℕ} {f : String} {bufs : List ℕ} {l : List (ℕ × ℕ)} {b : ℕ × ℕ}
    (hl : lp f = true) :
    kidPos fs lp p f bufs (l ++ [b]) =
      basesC (p.2 + bufs.sum) l ++ [(p.1 + fs f, p.2 + bufs.sum + (l.map Prod.fst).sum)] := by
  simp [kidPos, hl]

theorem kidPos_not_loop' {p : ℕ × ℕ} {f : String} {bufs : List ℕ} {ns : List (ℕ × ℕ)}
    (hl : lp f = false ∨ ns = []) : kidPos fs lp p f bufs ns = basesC (p.2 + bufs.sum) ns := by
  rcases hl with hl | rfl
  · simp [kidPos, hl]
  · simp [kidPos, basesC]

/-- **The callees' regions**: within the instance's region, apart from its frame and its
`HeapBuf`s, each with its block before its cursor. -/
theorem kidPos_regions {p : ℕ × ℕ} {f : String} {bufs : List ℕ} {ns : List (ℕ × ℕ)}
    (hns : ∀ s ∈ ns, s.2 ≤ s.1) (hp : p.1 + nodeBlock fs lp f ns ≤ p.2) :
    ∀ q ∈ ns.zip (kidPos fs lp p f bufs ns), q.2.1 + q.1.2 ≤ q.2.2 ∧ ∀ i, InReg q.1 q.2 i →
      InReg (fs f + (ns.map Prod.fst).sum + bufs.sum, nodeBlock fs lp f ns) p i ∧
      ¬ (p.1 ≤ i ∧ i < p.1 + fs f) ∧ ¬ (p.2 ≤ i ∧ i < p.2 + bufs.sum) := by
  intro q hq
  unfold nodeBlock at hp ⊢
  by_cases hl : lp f = true ∧ ns ≠ []
  · obtain ⟨hl, hne⟩ := hl
    obtain ⟨l, b, rfl⟩ := (List.eq_nil_or_concat ns).resolve_left hne
    rw [List.concat_eq_append] at hq hns hp ⊢
    have hb := hns b (by simp)
    have hlb : lastBlock (l ++ [b]) = b.2 := by simp [lastBlock]
    rw [kidPos_loop hl, List.zip_append length_basesC.symm, List.mem_append] at hq
    simp only [hl, ↓reduceIte, hlb, List.map_append, List.map_cons, List.map_nil, List.sum_append,
      List.sum_cons, List.sum_nil] at hp ⊢
    rcases hq with hq | hq
    · obtain ⟨h1, h2, h3⟩ := basesC_zip hq
      have hq1 := hns q.1 (List.mem_append_left _ (List.of_mem_zip hq).1)
      refine ⟨by omega, fun i hi => ?_⟩
      unfold InReg at hi ⊢
      omega
    · simp only [List.zip_cons_cons, List.zip_nil_right, List.mem_singleton] at hq
      subst hq
      refine ⟨by simp only; omega, fun i hi => ?_⟩
      unfold InReg at hi ⊢
      simp only at hi ⊢
      omega
  · have hl' : lp f = false ∨ ns = [] := by
      by_cases h : lp f = true
      · exact Or.inr (by simpa using fun h' => hl ⟨h, h'⟩)
      · exact Or.inl (by simpa using h)
    have hb : (if lp f = true then lastBlock ns else 0) = 0 := by
      rcases hl' with h | rfl
      · simp [h]
      · simp [lastBlock]
    rw [kidPos_not_loop' hl'] at hq
    rw [hb] at hp ⊢
    obtain ⟨h1, h2, h3⟩ := basesC_zip hq
    have hq1 := hns q.1 (List.of_mem_zip hq).1
    refine ⟨by omega, fun i hi => ?_⟩
    unfold InReg at hi ⊢
    omega

/-- The callees' regions are pairwise disjoint. -/
theorem kidPos_pairwise {p : ℕ × ℕ} {f : String} {bufs : List ℕ} {ns : List (ℕ × ℕ)}
    (hns : ∀ s ∈ ns, s.2 ≤ s.1) (hp : p.1 + nodeBlock fs lp f ns ≤ p.2) :
    (ns.zip (kidPos fs lp p f bufs ns)).Pairwise DisjR := by
  have hfresh : ∀ {b : ℕ} {ss : List (ℕ × ℕ)}, (∀ s ∈ ss, s.2 ≤ s.1) →
      (ss.zip (basesC b ss)).Pairwise DisjR := by
    intro b ss hss
    refine (basesC_pairwise (b := b) (ss := ss)).imp_of_mem fun {q q'} hq hq' h i hi hi' => ?_
    obtain ⟨e1, -, -⟩ := basesC_zip hq
    obtain ⟨e1', -, -⟩ := basesC_zip hq'
    have := hss _ (List.of_mem_zip hq).1
    have := hss _ (List.of_mem_zip hq').1
    unfold InReg at hi hi'
    omega
  unfold nodeBlock at hp
  by_cases hl : lp f = true ∧ ns ≠ []
  · obtain ⟨hl, hne⟩ := hl
    obtain ⟨l, b, rfl⟩ := (List.eq_nil_or_concat ns).resolve_left hne
    rw [List.concat_eq_append] at hns hp ⊢
    have hlb : lastBlock (l ++ [b]) = b.2 := by simp [lastBlock]
    simp only [hl, ↓reduceIte, hlb] at hp
    rw [kidPos_loop hl, List.zip_append length_basesC.symm, List.pairwise_append]
    refine ⟨hfresh fun s hs => hns s (List.mem_append_left _ hs), by simp, fun q hq q' hq' i hi hi' => ?_⟩
    simp only [List.zip_cons_cons, List.zip_nil_right, List.mem_singleton] at hq'
    subst hq'
    obtain ⟨h1, h2, h3⟩ := basesC_zip hq
    have := hns _ (List.mem_append_left _ (List.of_mem_zip hq).1)
    unfold InReg at hi hi'
    simp only at hi'
    omega
  · have hl' : lp f = false ∨ ns = [] := by
      by_cases h : lp f = true
      · exact Or.inr (by simpa using fun h' => hl ⟨h, h'⟩)
      · exact Or.inl (by simpa using h)
    rw [kidPos_not_loop' hl']
    exact hfresh hns

/-! ## Placement -/

variable {H : Inst → ℕ → E × E}

theorem insts_node {f : String} {σ : Val} {bufs : List ℕ} {kids : List Tree} {p : ℕ × ℕ}
    {hdr : E × E} :
    (Tree.node f σ bufs kids).insts fs lp H p hdr =
      let I : Inst := ⟨.node f σ bufs kids, p.1, p.2, hdr,
        (kidPos fs lp p f bufs (kids.map (Tree.sz fs lp))).map Prod.fst, bases p.2 bufs⟩
      I :: Tree.instsKids fs lp H I 0 (kidPos fs lp p f bufs (kids.map (Tree.sz fs lp))) kids := by
  rw [Tree.insts]

theorem insts_phantom {f : String} {σ : Val} {p : ℕ × ℕ} {hdr : E × E} :
    (Tree.phantom f σ).insts fs lp H p hdr = [⟨.phantom f σ, p.1, p.2, hdr, [], []⟩] := by
  rw [Tree.insts]

theorem instsKids_cons {I : Inst} {i : ℕ} {p : ℕ × ℕ} {ps : List (ℕ × ℕ)} {k : Tree} {ks : List Tree} :
    Tree.instsKids fs lp H I i (p :: ps) (k :: ks) =
      k.insts fs lp H p (H I i) ++ Tree.instsKids fs lp H I (i + 1) ps ks := by
  rw [Tree.instsKids]

theorem instsKids_nil {I : Inst} {i : ℕ} {ps : List (ℕ × ℕ)} :
    Tree.instsKids fs lp H I i ps [] = [] := by
  rw [Tree.instsKids]

theorem instsKids_nil_left {I : Inst} {i : ℕ} {ks : List Tree} :
    Tree.instsKids fs lp H I i [] ks = [] := by
  cases ks <;> rw [Tree.instsKids]

/-- The head of a node's instances is the node. -/
theorem head_insts (t : Tree) (p : ℕ × ℕ) (hdr : E × E) :
    ∃ I rest, t.insts fs lp H p hdr = I :: rest ∧ I.t = t ∧ I.fp = p.1 ∧ I.cur = p.2 ∧
      I.hdr = hdr := by
  cases t with
  | node f σ bufs kids => exact ⟨_, _, insts_node, rfl, rfl, rfl, rfl⟩
  | phantom f σ => exact ⟨_, _, insts_phantom, rfl, rfl, rfl, rfl⟩

mutual
/-- **Within its region**: every word an instance of a subtree at `p` owns is in the subtree's
region. -/
theorem insts_within : ∀ (t : Tree) (p : ℕ × ℕ) (hdr : E × E), p.1 + t.block fs lp ≤ p.2 →
    ∀ I ∈ t.insts fs lp H p hdr, ∀ i, I.Owns fs i → InReg (t.sz fs lp) p i
  | .node f σ bufs kids, p, hdr, hp, I, hI, i, hi => by
      rw [insts_node, List.mem_cons] at hI
      rw [block_node] at hp
      have hsz : (Tree.node f σ bufs kids).sz fs lp =
          (fs f + ((kids.map (Tree.sz fs lp)).map Prod.fst).sum + bufs.sum,
            nodeBlock fs lp f (kids.map (Tree.sz fs lp))) := by
        rw [Tree.sz, total_node, block_node, sum_map_sz]
      rw [hsz]
      rcases hI with rfl | hI
      · have hlb := lastBlock_le_sum _ (sz_le (fs := fs) (lp := lp) kids)
        simp only [Inst.Owns, Inst.Frame, Inst.Buf, Tree.name, Tree.bufs] at hi
        unfold InReg nodeBlock
        unfold nodeBlock at hp
        rcases hi with ⟨h1, h2⟩ | ⟨q, hq, h1, h2⟩
        · split <;> omega
        · have := bases_zip hq; split <;> omega
      · obtain ⟨q, hq, hiq⟩ := instsKids_within kids _ _ _
          (fun q hq => (kidPos_regions (sz_le kids) hp q hq).1) I hI i hi
        exact ((kidPos_regions (sz_le kids) hp q hq).2 i hiq).1
  | .phantom f σ, p, hdr, _, I, hI, i, hi => by
      rw [insts_phantom, List.mem_singleton] at hI
      subst hI
      rcases hi with ⟨h1, h2⟩ | ⟨q, hq, -⟩
      · left; simp only [Tree.sz, block_phantom]; exact ⟨h1, h2⟩
      · simp at hq

/-- `insts_within` for the callees at `ps`: every word one owns is in its callee's region. -/
theorem instsKids_within : ∀ (ks : List Tree) (ps : List (ℕ × ℕ)) (I : Inst) (j : ℕ),
    (∀ q ∈ (ks.map (Tree.sz fs lp)).zip ps, q.2.1 + q.1.2 ≤ q.2.2) →
    ∀ J ∈ Tree.instsKids fs lp H I j ps ks, ∀ i, J.Owns fs i →
      ∃ q ∈ (ks.map (Tree.sz fs lp)).zip ps, InReg q.1 q.2 i
  | [], _, _, _, _, J, hJ, _, _ => by rw [instsKids_nil] at hJ; exact (List.not_mem_nil hJ).elim
  | _ :: _, [], _, _, _, J, hJ, _, _ => by
      rw [instsKids_nil_left] at hJ; exact (List.not_mem_nil hJ).elim
  | k :: ks, p :: ps, I, j, hps, J, hJ, i, hi => by
      rw [instsKids_cons, List.mem_append] at hJ
      have hps := zip_cons_hps hps
      simp only [List.map_cons, List.zip_cons_cons, List.mem_cons, exists_eq_or_imp]
      rcases hJ with hJ | hJ
      · exact Or.inl (insts_within k _ _ hps.1 J hJ i hi)
      · exact Or.inr (instsKids_within ks ps I (j + 1) hps.2 J hJ i hi)
end

mutual
/-- **Disjointness**: two instances of a subtree own no word in common. -/
theorem insts_pairwise : ∀ (t : Tree) (p : ℕ × ℕ) (hdr : E × E), p.1 + t.block fs lp ≤ p.2 →
    (t.insts fs lp H p hdr).Pairwise (Inst.Apart fs)
  | .node f σ bufs kids, p, hdr, hp => by
      rw [insts_node]
      rw [block_node] at hp
      have hreg := kidPos_regions (bufs := bufs) (sz_le (fs := fs) (lp := lp) kids) hp
      refine List.Pairwise.cons (fun J hJ i hI hJi => ?_)
        (instsKids_pairwise kids _ _ 0 (fun q hq => (hreg q hq).1)
          (kidPos_pairwise (sz_le kids) hp))
      obtain ⟨q, hq, hiq⟩ := instsKids_within kids _ _ _ (fun q hq => (hreg q hq).1) J hJ i hJi
      obtain ⟨-, hnf, hnb⟩ := (hreg q hq).2 i hiq
      simp only [Inst.Owns, Inst.Frame, Inst.Buf, Tree.name, Tree.bufs] at hI
      rcases hI with ⟨h1, h2⟩ | ⟨q', hq', h1', h2'⟩
      · exact hnf ⟨h1, h2⟩
      · have := bases_zip hq'; exact hnb ⟨by omega, by omega⟩
  | .phantom f σ, p, hdr, _ => by
      rw [insts_phantom]
      exact List.pairwise_singleton _ _

/-- `insts_pairwise` for the callees at `ps`, their regions disjoint. -/
theorem instsKids_pairwise : ∀ (ks : List Tree) (ps : List (ℕ × ℕ)) (I : Inst) (j : ℕ),
    (∀ q ∈ (ks.map (Tree.sz fs lp)).zip ps, q.2.1 + q.1.2 ≤ q.2.2) →
    ((ks.map (Tree.sz fs lp)).zip ps).Pairwise DisjR →
      (Tree.instsKids fs lp H I j ps ks).Pairwise (Inst.Apart fs)
  | [], _, _, _, _, _ => by rw [instsKids_nil]; exact List.Pairwise.nil
  | _ :: _, [], _, _, _, _ => by rw [instsKids_nil_left]; exact List.Pairwise.nil
  | k :: ks, p :: ps, I, j, hps, hd => by
      have hps := zip_cons_hps hps
      simp only [List.map_cons, List.zip_cons_cons, List.pairwise_cons] at hd
      rw [instsKids_cons, List.pairwise_append]
      refine ⟨insts_pairwise k _ _ hps.1, instsKids_pairwise ks ps I (j + 1) hps.2 hd.2,
        fun J hJ J' hJ' i hi hi' => ?_⟩
      have h1 := insts_within k _ _ hps.1 J hJ i hi
      obtain ⟨q, hq, h2⟩ := instsKids_within ks ps I (j + 1) hps.2 J' hJ' i hi'
      exact hd.1 q hq i h1 h2
end

/-- An instance placed as the allocator places it: its callees' frames and its `HeapBuf`s where
`Tree.insts` puts them, its block before its cursor. -/
def Inst.Placed (fs : String → ℕ) (lp : String → Bool) (I : Inst) : Prop :=
  I.kidFps = (kidPos fs lp (I.fp, I.cur) I.t.name I.t.bufs (I.t.kids.map (Tree.sz fs lp))).map
      Prod.fst ∧
    I.bufBases = bases I.cur I.t.bufs ∧ I.fp + I.t.block fs lp ≤ I.cur

mutual
/-- Every instance is placed. -/
theorem insts_placed : ∀ (t : Tree) (p : ℕ × ℕ) (hdr : E × E), p.1 + t.block fs lp ≤ p.2 →
    ∀ I ∈ t.insts fs lp H p hdr, I.Placed fs lp
  | .node f σ bufs kids, p, hdr, hp, I, hI => by
      rw [insts_node, List.mem_cons] at hI
      rcases hI with rfl | hI
      · exact ⟨rfl, rfl, hp⟩
      · rw [block_node] at hp
        exact instsKids_placed kids _ _ 0
          (fun q hq => (kidPos_regions (bufs := bufs) (sz_le kids) hp q hq).1) I hI
  | .phantom f σ, p, hdr, hp, I, hI => by
      rw [insts_phantom, List.mem_singleton] at hI
      subst hI
      refine ⟨?_, rfl, hp⟩
      simp only [Tree.kids, List.map_nil, kidPos, basesC, List.dropLast_nil,
        List.getLast?_nil, Option.toList_none, List.map_nil, List.append_nil, ite_self]

/-- `insts_placed` for the callees. -/
theorem instsKids_placed : ∀ (ks : List Tree) (ps : List (ℕ × ℕ)) (I : Inst) (j : ℕ),
    (∀ q ∈ (ks.map (Tree.sz fs lp)).zip ps, q.2.1 + q.1.2 ≤ q.2.2) →
    ∀ J ∈ Tree.instsKids fs lp H I j ps ks, J.Placed fs lp
  | [], _, _, _, _, J, hJ => by rw [instsKids_nil] at hJ; exact (List.not_mem_nil hJ).elim
  | _ :: _, [], _, _, _, J, hJ => by
      rw [instsKids_nil_left] at hJ; exact (List.not_mem_nil hJ).elim
  | k :: ks, p :: ps, I, j, hps, J, hJ => by
      have hps := zip_cons_hps hps
      rw [instsKids_cons, List.mem_append] at hJ
      rcases hJ with hJ | hJ
      · exact insts_placed k _ _ hps.1 J hJ
      · exact instsKids_placed ks ps I (j + 1) hps.2 J hJ
end

/-- The frame and the `HeapBuf`s of a placed instance are disjoint. -/
theorem Inst.Placed.frame_buf {I : Inst} (h : I.Placed fs lp) {i : ℕ} (hF : I.Frame fs i) :
    ¬ I.Buf i := by
  rintro ⟨q, hq, h1, -⟩
  rw [h.2.1] at hq
  have := bases_zip hq
  have := le_block (fs := fs) (lp := lp) I.t
  have := h.2.2
  exact absurd hF.2 (by omega)

/-- **A loop's next iteration follows its frame**: a loop helper's last callee, its tail call, is
at `fp · g^S`. -/
theorem Inst.Placed.kidFps_getLast? {I : Inst} (h : I.Placed fs lp) (hl : lp I.t.name = true)
    (hk : I.t.kids ≠ []) : I.kidFps.getLast? = some (I.fp + fs I.t.name) := by
  rw [h.1]
  rcases List.eq_nil_or_concat (I.t.kids.map (Tree.sz fs lp)) with he | ⟨l, b, he⟩
  · exact absurd (List.map_eq_nil_iff.mp he) hk
  · rw [he, List.concat_eq_append, kidPos_loop hl]
    simp

/-- The `i`-th callee at `ps` is an instance at `ps[i]`, with header `H I (j + i)`. -/
theorem instsKids_kid : ∀ (ks : List Tree) (ps : List (ℕ × ℕ)) (I : Inst) (j i : ℕ) {k : Tree}
    {p : ℕ × ℕ}, ks[i]? = some k → ps[i]? = some p →
    ∃ J ∈ Tree.instsKids fs lp H I j ps ks, J.t = k ∧ J.fp = p.1 ∧ J.hdr = H I (j + i)
  | [], _, _, _, _, _, _, h, _ => by simp at h
  | _ :: _, [], _, _, _, _, _, _, h => by simp at h
  | k' :: ks, p' :: ps, I, j, 0, k, p, h, h' => by
      obtain rfl : k' = k := by simpa using h
      obtain rfl : p' = p := by simpa using h'
      obtain ⟨J, rest, he, ht, hfp, -, hh⟩ := head_insts (fs := fs) (lp := lp) (H := H) k' p' (H I j)
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
theorem insts_kid : ∀ (t : Tree) (p : ℕ × ℕ) (hdr : E × E), ∀ I ∈ t.insts fs lp H p hdr,
    ∀ (i : ℕ) (k : Tree), I.t.kids[i]? = some k →
      ∃ J ∈ t.insts fs lp H p hdr, J.t = k ∧ I.kidFps[i]? = some J.fp ∧ J.hdr = H I i
  | .node f σ bufs kids, p, hdr, I, hI, i, k, hk => by
      rw [insts_node, List.mem_cons] at hI
      rcases hI with rfl | hI
      · have hi : i < (kidPos fs lp p f bufs (kids.map (Tree.sz fs lp))).length := by
          rw [length_kidPos, List.length_map]
          exact (List.getElem?_eq_some_iff.mp hk).1
        obtain ⟨q, hq⟩ : ∃ q, (kidPos fs lp p f bufs (kids.map (Tree.sz fs lp)))[i]? = some q :=
          ⟨_, List.getElem?_eq_getElem hi⟩
        obtain ⟨J, hJ, ht, hfp, hh⟩ := instsKids_kid (fs := fs) (lp := lp) (H := H) kids _ _ 0 i hk hq
        refine ⟨J, ?_, ht, by simp only [List.getElem?_map, hq, hfp]; rfl, by simpa using hh⟩
        rw [insts_node]; exact List.mem_cons_of_mem _ hJ
      · obtain ⟨J, hJ, h⟩ := instsKids_kids_kid kids _ _ 0 I hI i k hk
        refine ⟨J, ?_, h⟩
        rw [insts_node]; exact List.mem_cons_of_mem _ hJ
  | .phantom f σ, p, hdr, I, hI, i, k, hk => by
      rw [insts_phantom, List.mem_singleton] at hI
      subst hI
      simp [Tree.kids] at hk

/-- `insts_kid` for the callees. -/
theorem instsKids_kids_kid : ∀ (ks : List Tree) (ps : List (ℕ × ℕ)) (I : Inst) (j : ℕ),
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
theorem length_insts : ∀ (t : Tree) (p : ℕ × ℕ) (hdr : E × E), (t.insts fs lp H p hdr).length = t.count
  | .node f σ bufs kids, p, hdr => by
      rw [insts_node, Tree.count, List.length_cons,
        length_instsKids kids _ _ 0 (by rw [length_kidPos, List.length_map])]
      omega
  | .phantom f σ, p, hdr => by rw [insts_phantom, Tree.count]; rfl

/-- `length_insts` for the callees. -/
theorem length_instsKids : ∀ (ks : List Tree) (ps : List (ℕ × ℕ)) (I : Inst) (j : ℕ),
    ps.length = ks.length →
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
  (I.cells C).map fun q => (addressOfIndex (I.fp + q.1), q.2)

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
    ∃ I ∈ Is, ∃ q ∈ I.cells C, a = (addressOfIndex (I.fp + q.1), q.2) := by
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
