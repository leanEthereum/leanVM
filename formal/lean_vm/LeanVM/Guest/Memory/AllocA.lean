/-
  LeanVM.Guest.Memory.AllocA

  The executor's bump allocator, its aligned allocations included: a frame that holds `KECCAK`
  blocks starts at the next multiple of `keccakWindow` (`Prover.Exec.allocBase`). The call
  instances of a tree placed in its order (`Tree.instsA`), each owning words of its subtree's
  region only, two of them no word in common.
-/

module

public import LeanVM.Guest.Memory.Alloc
public import Statement.Prover.Execute

/-!
# Placing a call tree, aligned

`Memory/Alloc.lean`'s allocator (`Tree.insts`) is the bus era's: every region from the end of the
one before. Hotwire's executor (`Prover.Exec.allocate`) starts an *aligned* region at the next
multiple of `keccakWindow = 16` (`allocBase`): the compiler aligns the frames of a function that
holds `KECCAK` blocks, of a loop helper's frames together, and of a `dispatch`'s arms when one of
them holds blocks (`aligned` in `crates/zkdsl_compiler/src/lib.rs`). `al f` says which frames are
allocated aligned, a function of the callee (one flag per function: the guest's every frame of a
function is allocated with one flag, which the core route checks against the hints). `HeapBuf`s are
never aligned, and a function's `HeapBuf`s are allocated before its first call (the compiler's
`hoist_heap_bufs`), as at the tag.

Placed at `p = (fp, c)`, a subtree has its block at `fp` (its caller placed it) and its other words
from `c`: its `HeapBuf`s, then each callee entered fresh at `allocBase (al k) cur`, its block and
then its subtree, a loop helper's last callee (its tail call) at `fp + fs f`, its other words after
the other callees'. The cursor after the subtree is `Tree.endA c t`; it depends on `c` modulo
`16`, so where `Memory/Alloc.lean` reads a subtree's size this reads its end.

`Tree.instsA`: the placed call instances, as `Tree.insts` lists them. `instsA_within`: every
instance owns words of its subtree's region only (`RegA`: its block, and `[c, endA c t)`);
`instsA_pairwise`: two instances own no word in common; `instsA_placed`: each is placed where the
allocator puts it; `instsA_kid`: a callee is the instance at its caller's callee frame.
-/

namespace LeanVM.Guest.Memory

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core
open LeanVM.Prover.Exec (allocBase keccakWindow)

@[expose] public section

/-! ## The aligned base -/

theorem le_allocBase (a : Bool) (n : ℕ) : n ≤ allocBase a n := by
  unfold allocBase keccakWindow
  split <;> omega

theorem allocBase_le (a : Bool) (n : ℕ) : allocBase a n ≤ n + 15 := by
  unfold allocBase keccakWindow
  split <;> omega

theorem allocBase_aligned (n : ℕ) : allocBase true n % 16 = 0 := by
  unfold allocBase keccakWindow
  simp only [↓reduceIte]
  omega

variable (fs : String → ℕ) (lp al : String → Bool)

mutual
/-- **The cursor after a subtree's other words**, placed from `c`: its `HeapBuf`s, then its
callees' regions. -/
def Tree.endA (c : ℕ) : Tree → ℕ
  | .node f _ bufs kids => if lp f then Tree.endL (c + bufs.sum) kids else Tree.endF (c + bufs.sum) kids
  | .phantom .. => c

/-- The cursor after callees entered fresh from `c`. -/
def Tree.endF (c : ℕ) : List Tree → ℕ
  | [] => c
  | k :: ks => Tree.endF (Tree.endA (allocBase (al k.name) c + k.block fs lp) k) ks

/-- The cursor after a loop iteration's callees from `c`, the last its tail call, whose block its
caller's block holds. -/
def Tree.endL (c : ℕ) : List Tree → ℕ
  | [] => c
  | [k] => Tree.endA c k
  | k :: k' :: ks => Tree.endL (Tree.endA (allocBase (al k.name) c + k.block fs lp) k) (k' :: ks)
end

/-- Callees entered fresh from `c`: each its block at the aligned base and its cursor after it. -/
def posF (c : ℕ) : List Tree → List (ℕ × ℕ)
  | [] => []
  | k :: ks => (allocBase (al k.name) c, allocBase (al k.name) c + k.block fs lp) ::
      posF (Tree.endA fs lp al (allocBase (al k.name) c + k.block fs lp) k) ks

/-- A loop iteration's callees from `c`: fresh, but the last, the tail call, at `tl`, its cursor
after the others'. -/
def posL (tl c : ℕ) : List Tree → List (ℕ × ℕ)
  | [] => []
  | [_] => [(tl, c)]
  | k :: k' :: ks => (allocBase (al k.name) c, allocBase (al k.name) c + k.block fs lp) ::
      posL tl (Tree.endA fs lp al (allocBase (al k.name) c + k.block fs lp) k) (k' :: ks)

/-- **The callees' positions** of an instance of `f` at `p` with `HeapBuf`s `bufs`, in call order. -/
def kidPosA (p : ℕ × ℕ) (f : String) (bufs : List ℕ) (kids : List Tree) : List (ℕ × ℕ) :=
  if lp f then posL fs lp al (p.1 + fs f) (p.2 + bufs.sum) kids else posF fs lp al (p.2 + bufs.sum) kids

mutual
/-- **The aligned bump allocator**: the call instances of a subtree at `p`. -/
def Tree.instsA (H : Inst → ℕ → E × E) (p : ℕ × ℕ) (hdr : E × E) : Tree → List Inst
  | t@(.node f _ bufs kids) =>
      let I : Inst := ⟨t, p.1, p.2, hdr, (kidPosA fs lp al p f bufs kids).map Prod.fst, bases p.2 bufs⟩
      I :: Tree.instsKidsA H I 0 (kidPosA fs lp al p f bufs kids) kids
  | t@(.phantom ..) => [⟨t, p.1, p.2, hdr, [], []⟩]

/-- The call instances of the callees `ks` of `I` from its `i`-th, at `ps`. -/
def Tree.instsKidsA (H : Inst → ℕ → E × E) (I : Inst) (i : ℕ) :
    List (ℕ × ℕ) → List Tree → List Inst
  | _, [] => []
  | [], _ :: _ => []
  | p :: ps, k :: ks => k.instsA H p (H I i) ++ Tree.instsKidsA H I (i + 1) ps ks
end

/-- **The region of a subtree** at `p`: its block from `p.1`, its other words from `p.2` to its
end. -/
def RegA (t : Tree) (p : ℕ × ℕ) (i : ℕ) : Prop :=
  (p.1 ≤ i ∧ i < p.1 + t.block fs lp) ∨ (p.2 ≤ i ∧ i < t.endA fs lp al p.2)

/-- The words a tree placed at `(0, block)` uses: its root's frame `0` to its end. -/
def Tree.wordsA (t : Tree) : ℕ := t.endA fs lp al (t.block fs lp)

variable {fs lp al}

/-! ## The ends -/

theorem endA_node (c : ℕ) (f : String) (σ : Val) (bufs : List ℕ) (kids : List Tree) :
    (Tree.node f σ bufs kids).endA fs lp al c =
      if lp f then Tree.endL fs lp al (c + bufs.sum) kids else Tree.endF fs lp al (c + bufs.sum) kids := by
  rw [Tree.endA]

theorem endA_phantom (c : ℕ) (f : String) (σ : Val) : (Tree.phantom f σ).endA fs lp al c = c := by
  rw [Tree.endA]

theorem endF_nil (c : ℕ) : Tree.endF fs lp al c [] = c := by rw [Tree.endF]

theorem endF_cons (c : ℕ) (k : Tree) (ks : List Tree) :
    Tree.endF fs lp al c (k :: ks) =
      Tree.endF fs lp al (k.endA fs lp al (allocBase (al k.name) c + k.block fs lp)) ks := by
  rw [Tree.endF]

theorem endL_nil (c : ℕ) : Tree.endL fs lp al c [] = c := by rw [Tree.endL]

theorem endL_one (c : ℕ) (k : Tree) : Tree.endL fs lp al c [k] = k.endA fs lp al c := by rw [Tree.endL]

theorem endL_cons (c : ℕ) (k k' : Tree) (ks : List Tree) :
    Tree.endL fs lp al c (k :: k' :: ks) =
      Tree.endL fs lp al (k.endA fs lp al (allocBase (al k.name) c + k.block fs lp)) (k' :: ks) := by
  rw [Tree.endL]

mutual
/-- The cursor only advances. -/
theorem le_endA : ∀ (t : Tree) (c : ℕ), c ≤ t.endA fs lp al c
  | .node f σ bufs kids, c => by
      rw [endA_node]
      split
      · have := le_endL kids (c + bufs.sum); omega
      · have := le_endF kids (c + bufs.sum); omega
  | .phantom f σ, c => by rw [endA_phantom]

theorem le_endF : ∀ (ks : List Tree) (c : ℕ), c ≤ Tree.endF fs lp al c ks
  | [], c => by rw [endF_nil]
  | k :: ks, c => by
      rw [endF_cons]
      have h1 := le_allocBase (al k.name) c
      have h2 := le_endA k (allocBase (al k.name) c + k.block fs lp)
      have h3 := le_endF ks (k.endA fs lp al (allocBase (al k.name) c + k.block fs lp))
      omega

theorem le_endL : ∀ (ks : List Tree) (c : ℕ), c ≤ Tree.endL fs lp al c ks
  | [], c => by rw [endL_nil]
  | [k], c => by rw [endL_one]; exact le_endA k c
  | k :: k' :: ks, c => by
      rw [endL_cons]
      have h1 := le_allocBase (al k.name) c
      have h2 := le_endA k (allocBase (al k.name) c + k.block fs lp)
      have h3 := le_endL (k' :: ks) (k.endA fs lp al (allocBase (al k.name) c + k.block fs lp))
      omega
end

/-! ## The callees' positions -/

theorem length_posF : ∀ (c : ℕ) (ks : List Tree), (posF fs lp al c ks).length = ks.length
  | _, [] => rfl
  | c, k :: ks => by simp [posF, length_posF _ ks]

theorem length_posL : ∀ (tl c : ℕ) (ks : List Tree), (posL fs lp al tl c ks).length = ks.length
  | _, _, [] => rfl
  | _, _, [_] => rfl
  | tl, c, k :: k' :: ks => by
      rw [posL, List.length_cons, length_posL _ _ (k' :: ks)]
      rfl

theorem length_kidPosA (p : ℕ × ℕ) (f : String) (bufs : List ℕ) (kids : List Tree) :
    (kidPosA fs lp al p f bufs kids).length = kids.length := by
  unfold kidPosA
  split
  · exact length_posL _ _ _
  · exact length_posF _ _

/-- Fresh callees from `c`: each block at its cursor, after `c`, its region before the end, and
the earlier ones' regions before the later ones'. -/
theorem posF_zip : ∀ {c : ℕ} {ks : List Tree} {q : Tree × (ℕ × ℕ)}, q ∈ ks.zip (posF fs lp al c ks) →
    q.2.2 = q.2.1 + q.1.block fs lp ∧ c ≤ q.2.1 ∧ q.1.endA fs lp al q.2.2 ≤ Tree.endF fs lp al c ks
  | _, [], _, h => (List.not_mem_nil h).elim
  | c, k :: ks, q, h => by
      simp only [posF, List.zip_cons_cons, List.mem_cons] at h
      rw [endF_cons]
      rcases h with rfl | h
      · exact ⟨rfl, le_allocBase _ _, le_endF ks _⟩
      · obtain ⟨h1, h2, h3⟩ := posF_zip h
        have := le_allocBase (al k.name) c
        have := le_endA (fs := fs) (lp := lp) (al := al) k (allocBase (al k.name) c + k.block fs lp)
        exact ⟨h1, by omega, h3⟩

theorem posF_pairwise : ∀ {c : ℕ} {ks : List Tree},
    (ks.zip (posF fs lp al c ks)).Pairwise fun q q' => q.1.endA fs lp al q.2.2 ≤ q'.2.1
  | _, [] => List.Pairwise.nil
  | c, k :: ks => by
      simp only [posF, List.zip_cons_cons, List.pairwise_cons]
      exact ⟨fun q hq => (posF_zip hq).2.1, posF_pairwise⟩

/-- A loop iteration's callees from `c`: the fresh ones as `posF_zip`, before the last's cursor. -/
theorem posL_split : ∀ {tl c : ℕ} {l : List Tree} {b : Tree},
    posL fs lp al tl c (l ++ [b]) = posF fs lp al c l ++ [(tl, Tree.endF fs lp al c l)] ∧
      Tree.endL fs lp al c (l ++ [b]) = b.endA fs lp al (Tree.endF fs lp al c l)
  | tl, c, [], b => by simp [posL, posF, endL_one, endF_nil]
  | tl, c, k :: l, b => by
      obtain ⟨h1, h2⟩ := posL_split (tl := tl)
        (c := k.endA fs lp al (allocBase (al k.name) c + k.block fs lp)) (l := l) (b := b)
      obtain ⟨k', l', he⟩ : ∃ k' l', l ++ [b] = k' :: l' := by
        cases l with
        | nil => exact ⟨b, [], rfl⟩
        | cons x l => exact ⟨x, l ++ [b], rfl⟩
      refine ⟨?_, ?_⟩
      · rw [List.cons_append, he, posL, ← he, h1, posF, endF_cons]
        rfl
      · rw [List.cons_append, he, endL_cons, ← he, h2, endF_cons]

/-! ## The callees' regions -/

/-- **The callees' regions**: within the instance's region, apart from its frame and its
`HeapBuf`s, each with its block before its cursor. -/
theorem kidPosA_regions {p : ℕ × ℕ} {f : String} {σ : Val} {bufs : List ℕ} {kids : List Tree}
    (hp : p.1 + (Tree.node f σ bufs kids).block fs lp ≤ p.2) :
    ∀ q ∈ kids.zip (kidPosA fs lp al p f bufs kids), q.2.1 + q.1.block fs lp ≤ q.2.2 ∧ ∀ i, RegA fs lp al q.1 q.2 i →
      RegA fs lp al (.node f σ bufs kids) p i ∧
      ¬ (p.1 ≤ i ∧ i < p.1 + fs f) ∧ ¬ (p.2 ≤ i ∧ i < p.2 + bufs.sum) := by
  intro q hq
  unfold RegA
  rw [endA_node, block_node]
  rw [block_node] at hp
  unfold nodeBlock at hp ⊢
  by_cases hl : lp f = true ∧ kids ≠ []
  · obtain ⟨hl, hne⟩ := hl
    obtain ⟨l, b, rfl⟩ := (List.eq_nil_or_concat kids).resolve_left hne
    rw [List.concat_eq_append] at hq hp ⊢
    obtain ⟨hpos, hend⟩ := posL_split (fs := fs) (lp := lp) (al := al) (tl := p.1 + fs f)
      (c := p.2 + bufs.sum) (l := l) (b := b)
    have hlb : lastBlock ((l ++ [b]).map (Tree.sz fs lp)) = b.block fs lp := by simp [lastBlock, Tree.sz]
    simp only [hl, ↓reduceIte, hlb] at hp ⊢
    rw [hend]
    unfold kidPosA at hq
    rw [ite_eq_left_of_eq_true _ _ (eq_true hl), hpos, List.zip_append (by rw [length_posF]), List.mem_append] at hq
    have hF := le_endF (fs := fs) (lp := lp) (al := al) l (p.2 + bufs.sum)
    have hE := le_endA (fs := fs) (lp := lp) (al := al) b (Tree.endF fs lp al (p.2 + bufs.sum) l)
    rcases hq with hq | hq
    · obtain ⟨h1, h2, h3⟩ := posF_zip hq
      have := le_endA (fs := fs) (lp := lp) (al := al) q.1 q.2.2
      refine ⟨by omega, fun i hi => ?_⟩
      omega
    · simp only [List.zip_cons_cons, List.zip_nil_right, List.mem_singleton] at hq
      subst hq
      refine ⟨by simp only; omega, fun i hi => ?_⟩
      simp only at hi ⊢
      omega
  · have hl' : lp f = false ∨ kids = [] := by
      by_cases h : lp f = true
      · exact Or.inr (by simpa using fun h' => hl ⟨h, h'⟩)
      · exact Or.inl (by simpa using h)
    have hk : kidPosA fs lp al p f bufs kids = posF fs lp al (p.2 + bufs.sum) kids := by
      unfold kidPosA
      rcases hl' with h | rfl
      · simp [h]
      · split <;> rfl
    have he : (if lp f = true then Tree.endL fs lp al (p.2 + bufs.sum) kids
        else Tree.endF fs lp al (p.2 + bufs.sum) kids) = Tree.endF fs lp al (p.2 + bufs.sum) kids := by
      rcases hl' with h | rfl
      · simp [h]
      · split <;> simp only [endL_nil, endF_nil]
    have hb : (if lp f = true then lastBlock (kids.map (Tree.sz fs lp)) else 0) = 0 := by
      rcases hl' with h | rfl
      · simp [h]
      · simp [lastBlock]
    rw [he, hb]
    rw [hb] at hp
    rw [hk] at hq
    obtain ⟨h1, h2, h3⟩ := posF_zip hq
    have := le_endA (fs := fs) (lp := lp) (al := al) q.1 q.2.2
    refine ⟨by omega, fun i hi => ?_⟩
    omega

/-- The callees' regions are pairwise disjoint. -/
theorem kidPosA_pairwise {p : ℕ × ℕ} {f : String} {σ : Val} {bufs : List ℕ} {kids : List Tree}
    (hp : p.1 + (Tree.node f σ bufs kids).block fs lp ≤ p.2) :
    (kids.zip (kidPosA fs lp al p f bufs kids)).Pairwise
      fun q q' => ∀ i, RegA fs lp al q.1 q.2 i → ¬ RegA fs lp al q'.1 q'.2 i := by
  have hfresh : ∀ {c : ℕ} {ss : List Tree}, (ss.zip (posF fs lp al c ss)).Pairwise
      fun q q' => ∀ i, RegA fs lp al q.1 q.2 i → ¬ RegA fs lp al q'.1 q'.2 i := by
    intro c ss
    refine (posF_pairwise (c := c) (ks := ss)).imp_of_mem fun {q q'} hq hq' h i hi hi' => ?_
    obtain ⟨e1, -, -⟩ := posF_zip hq
    obtain ⟨e1', -, -⟩ := posF_zip hq'
    have := le_endA (fs := fs) (lp := lp) (al := al) q.1 q.2.2
    have := le_endA (fs := fs) (lp := lp) (al := al) q'.1 q'.2.2
    unfold RegA at hi hi'
    omega
  rw [block_node] at hp
  unfold nodeBlock at hp
  by_cases hl : lp f = true ∧ kids ≠ []
  · obtain ⟨hl, hne⟩ := hl
    obtain ⟨l, b, rfl⟩ := (List.eq_nil_or_concat kids).resolve_left hne
    rw [List.concat_eq_append] at hp ⊢
    obtain ⟨hpos, -⟩ := posL_split (fs := fs) (lp := lp) (al := al) (tl := p.1 + fs f)
      (c := p.2 + bufs.sum) (l := l) (b := b)
    have hlb : lastBlock ((l ++ [b]).map (Tree.sz fs lp)) = b.block fs lp := by simp [lastBlock, Tree.sz]
    simp only [hl, ↓reduceIte, hlb] at hp
    unfold kidPosA
    rw [ite_eq_left_of_eq_true _ _ (eq_true hl), hpos, List.zip_append (by rw [length_posF]), List.pairwise_append]
    refine ⟨hfresh, by simp, fun q hq q' hq' i hi hi' => ?_⟩
    simp only [List.zip_cons_cons, List.zip_nil_right, List.mem_singleton] at hq'
    subst hq'
    obtain ⟨h1, h2, h3⟩ := posF_zip hq
    have := le_endA (fs := fs) (lp := lp) (al := al) q.1 q.2.2
    unfold RegA at hi hi'
    simp only at hi'
    omega
  · have hl' : lp f = false ∨ kids = [] := by
      by_cases h : lp f = true
      · exact Or.inr (by simpa using fun h' => hl ⟨h, h'⟩)
      · exact Or.inl (by simpa using h)
    have hk : kidPosA fs lp al p f bufs kids = posF fs lp al (p.2 + bufs.sum) kids := by
      unfold kidPosA
      rcases hl' with h | rfl
      · simp [h]
      · split <;> rfl
    rw [hk]
    exact hfresh

/-! ## Placement -/

variable {H : Inst → ℕ → E × E}

theorem instsA_node {f : String} {σ : Val} {bufs : List ℕ} {kids : List Tree} {p : ℕ × ℕ}
    {hdr : E × E} :
    (Tree.node f σ bufs kids).instsA fs lp al H p hdr =
      let I : Inst := ⟨.node f σ bufs kids, p.1, p.2, hdr,
        (kidPosA fs lp al p f bufs kids).map Prod.fst, bases p.2 bufs⟩
      I :: Tree.instsKidsA fs lp al H I 0 (kidPosA fs lp al p f bufs kids) kids := by
  rw [Tree.instsA]

theorem instsA_phantom {f : String} {σ : Val} {p : ℕ × ℕ} {hdr : E × E} :
    (Tree.phantom f σ).instsA fs lp al H p hdr = [⟨.phantom f σ, p.1, p.2, hdr, [], []⟩] := by
  rw [Tree.instsA]

theorem instsKidsA_cons {I : Inst} {i : ℕ} {p : ℕ × ℕ} {ps : List (ℕ × ℕ)} {k : Tree} {ks : List Tree} :
    Tree.instsKidsA fs lp al H I i (p :: ps) (k :: ks) =
      k.instsA fs lp al H p (H I i) ++ Tree.instsKidsA fs lp al H I (i + 1) ps ks := by
  rw [Tree.instsKidsA]

theorem instsKidsA_nil {I : Inst} {i : ℕ} {ps : List (ℕ × ℕ)} :
    Tree.instsKidsA fs lp al H I i ps [] = [] := by
  rw [Tree.instsKidsA]

theorem instsKidsA_nil_left {I : Inst} {i : ℕ} {ks : List Tree} :
    Tree.instsKidsA fs lp al H I i [] ks = [] := by
  cases ks <;> rw [Tree.instsKidsA]

/-- The head of a node's instances is the node. -/
theorem head_instsA (t : Tree) (p : ℕ × ℕ) (hdr : E × E) :
    ∃ I rest, t.instsA fs lp al H p hdr = I :: rest ∧ I.t = t ∧ I.fp = p.1 ∧ I.cur = p.2 ∧
      I.hdr = hdr := by
  cases t with
  | node f σ bufs kids => exact ⟨_, _, instsA_node, rfl, rfl, rfl, rfl⟩
  | phantom f σ => exact ⟨_, _, instsA_phantom, rfl, rfl, rfl, rfl⟩

theorem zipA_cons_hps {k : Tree} {ks : List Tree} {p : ℕ × ℕ} {ps : List (ℕ × ℕ)}
    (h : ∀ q ∈ (k :: ks).zip (p :: ps), q.2.1 + q.1.block fs lp ≤ q.2.2) :
    p.1 + k.block fs lp ≤ p.2 ∧ ∀ q ∈ ks.zip ps, q.2.1 + q.1.block fs lp ≤ q.2.2 :=
  ⟨h (k, p) (by simp), fun q hq => h q (by simp [hq])⟩

mutual
/-- **Within its region**: every word an instance of a subtree at `p` owns is in the subtree's
region. -/
theorem instsA_within : ∀ (t : Tree) (p : ℕ × ℕ) (hdr : E × E), p.1 + t.block fs lp ≤ p.2 →
    ∀ I ∈ t.instsA fs lp al H p hdr, ∀ i, I.Owns fs i → RegA fs lp al t p i
  | .node f σ bufs kids, p, hdr, hp, I, hI, i, hi => by
      rw [instsA_node, List.mem_cons] at hI
      rcases hI with rfl | hI
      · have hb := le_block (fs := fs) (lp := lp) (.node f σ bufs kids)
        have he : p.2 + bufs.sum ≤ (Tree.node f σ bufs kids).endA fs lp al p.2 := by
          rw [endA_node]
          split
          · exact le_endL _ _
          · exact le_endF _ _
        simp only [Inst.Owns, Inst.Frame, Inst.Buf, Tree.fsz, Tree.bufs] at hi hb
        unfold RegA
        rcases hi with ⟨h1, h2⟩ | ⟨q, hq, h1, h2⟩
        · omega
        · have := bases_zip hq; omega
      · obtain ⟨q, hq, hiq⟩ := instsKidsA_within kids _ _ _
          (fun q hq => (kidPosA_regions hp q hq).1) I hI i hi
        exact ((kidPosA_regions hp q hq).2 i hiq).1
  | .phantom f σ, p, hdr, _, I, hI, i, hi => by
      rw [instsA_phantom, List.mem_singleton] at hI
      subst hI
      rcases hi with ⟨h1, h2⟩ | ⟨q, hq, -⟩
      · left; simp only [block_phantom]; exact ⟨h1, h2⟩
      · simp at hq

/-- `instsA_within` for the callees at `ps`: every word one owns is in its callee's region. -/
theorem instsKidsA_within : ∀ (ks : List Tree) (ps : List (ℕ × ℕ)) (I : Inst) (j : ℕ),
    (∀ q ∈ ks.zip ps, q.2.1 + q.1.block fs lp ≤ q.2.2) →
    ∀ J ∈ Tree.instsKidsA fs lp al H I j ps ks, ∀ i, J.Owns fs i →
      ∃ q ∈ ks.zip ps, RegA fs lp al q.1 q.2 i
  | [], _, _, _, _, J, hJ, _, _ => by rw [instsKidsA_nil] at hJ; exact (List.not_mem_nil hJ).elim
  | _ :: _, [], _, _, _, J, hJ, _, _ => by
      rw [instsKidsA_nil_left] at hJ; exact (List.not_mem_nil hJ).elim
  | k :: ks, p :: ps, I, j, hps, J, hJ, i, hi => by
      rw [instsKidsA_cons, List.mem_append] at hJ
      have hps := zipA_cons_hps hps
      simp only [List.zip_cons_cons, List.mem_cons, exists_eq_or_imp]
      rcases hJ with hJ | hJ
      · exact Or.inl (instsA_within k _ _ hps.1 J hJ i hi)
      · exact Or.inr (instsKidsA_within ks ps I (j + 1) hps.2 J hJ i hi)
end

mutual
/-- **Disjointness**: two instances of a subtree own no word in common. -/
theorem instsA_pairwise : ∀ (t : Tree) (p : ℕ × ℕ) (hdr : E × E), p.1 + t.block fs lp ≤ p.2 →
    (t.instsA fs lp al H p hdr).Pairwise (Inst.Apart fs)
  | .node f σ bufs kids, p, hdr, hp => by
      rw [instsA_node]
      have hreg := kidPosA_regions (al := al) hp
      refine List.Pairwise.cons (fun J hJ i hI hJi => ?_)
        (instsKidsA_pairwise kids _ _ 0 (fun q hq => (hreg q hq).1) (kidPosA_pairwise hp))
      obtain ⟨q, hq, hiq⟩ := instsKidsA_within kids _ _ _ (fun q hq => (hreg q hq).1) J hJ i hJi
      obtain ⟨-, hnf, hnb⟩ := (hreg q hq).2 i hiq
      simp only [Inst.Owns, Inst.Frame, Inst.Buf, Tree.fsz, Tree.bufs] at hI
      rcases hI with ⟨h1, h2⟩ | ⟨q', hq', h1', h2'⟩
      · exact hnf ⟨h1, h2⟩
      · have := bases_zip hq'; exact hnb ⟨by omega, by omega⟩
  | .phantom f σ, p, hdr, _ => by
      rw [instsA_phantom]
      exact List.pairwise_singleton _ _

/-- `instsA_pairwise` for the callees at `ps`, their regions disjoint. -/
theorem instsKidsA_pairwise : ∀ (ks : List Tree) (ps : List (ℕ × ℕ)) (I : Inst) (j : ℕ),
    (∀ q ∈ ks.zip ps, q.2.1 + q.1.block fs lp ≤ q.2.2) →
    (ks.zip ps).Pairwise (fun q q' => ∀ i, RegA fs lp al q.1 q.2 i → ¬ RegA fs lp al q'.1 q'.2 i) →
      (Tree.instsKidsA fs lp al H I j ps ks).Pairwise (Inst.Apart fs)
  | [], _, _, _, _, _ => by rw [instsKidsA_nil]; exact List.Pairwise.nil
  | _ :: _, [], _, _, _, _ => by rw [instsKidsA_nil_left]; exact List.Pairwise.nil
  | k :: ks, p :: ps, I, j, hps, hd => by
      have hps := zipA_cons_hps hps
      simp only [List.zip_cons_cons, List.pairwise_cons] at hd
      rw [instsKidsA_cons, List.pairwise_append]
      refine ⟨instsA_pairwise k _ _ hps.1, instsKidsA_pairwise ks ps I (j + 1) hps.2 hd.2,
        fun J hJ J' hJ' i hi hi' => ?_⟩
      have h1 := instsA_within k _ _ hps.1 J hJ i hi
      obtain ⟨q, hq, h2⟩ := instsKidsA_within ks ps I (j + 1) hps.2 J' hJ' i hi'
      exact hd.1 q hq i h1 h2
end

/-- An instance placed as the aligned allocator places it: its callees' frames and its `HeapBuf`s
where `Tree.instsA` puts them, its block before its cursor. -/
def Inst.PlacedA (fs : String → ℕ) (lp al : String → Bool) (I : Inst) : Prop :=
  I.kidFps = (kidPosA fs lp al (I.fp, I.cur) I.t.name I.t.bufs I.t.kids).map Prod.fst ∧
    I.bufBases = bases I.cur I.t.bufs ∧ I.fp + I.t.block fs lp ≤ I.cur

mutual
/-- Every instance is placed. -/
theorem instsA_placed : ∀ (t : Tree) (p : ℕ × ℕ) (hdr : E × E), p.1 + t.block fs lp ≤ p.2 →
    ∀ I ∈ t.instsA fs lp al H p hdr, I.PlacedA fs lp al
  | .node f σ bufs kids, p, hdr, hp, I, hI => by
      rw [instsA_node, List.mem_cons] at hI
      rcases hI with rfl | hI
      · exact ⟨rfl, rfl, hp⟩
      · exact instsKidsA_placed kids _ _ 0 (fun q hq => (kidPosA_regions hp q hq).1) I hI
  | .phantom f σ, p, hdr, hp, I, hI => by
      rw [instsA_phantom, List.mem_singleton] at hI
      subst hI
      refine ⟨?_, rfl, hp⟩
      simp only [Tree.kids, kidPosA, posL, posF, ite_self, List.map_nil]

/-- `instsA_placed` for the callees. -/
theorem instsKidsA_placed : ∀ (ks : List Tree) (ps : List (ℕ × ℕ)) (I : Inst) (j : ℕ),
    (∀ q ∈ ks.zip ps, q.2.1 + q.1.block fs lp ≤ q.2.2) →
    ∀ J ∈ Tree.instsKidsA fs lp al H I j ps ks, J.PlacedA fs lp al
  | [], _, _, _, _, J, hJ => by rw [instsKidsA_nil] at hJ; exact (List.not_mem_nil hJ).elim
  | _ :: _, [], _, _, _, J, hJ => by
      rw [instsKidsA_nil_left] at hJ; exact (List.not_mem_nil hJ).elim
  | k :: ks, p :: ps, I, j, hps, J, hJ => by
      have hps := zipA_cons_hps hps
      rw [instsKidsA_cons, List.mem_append] at hJ
      rcases hJ with hJ | hJ
      · exact instsA_placed k _ _ hps.1 J hJ
      · exact instsKidsA_placed ks ps I (j + 1) hps.2 J hJ
end

/-- The frame and the `HeapBuf`s of a placed instance are disjoint. -/
theorem Inst.PlacedA.frame_buf {I : Inst} (h : I.PlacedA fs lp al) {i : ℕ} (hF : I.Frame fs i) :
    ¬ I.Buf i := by
  rintro ⟨q, hq, h1, -⟩
  rw [h.2.1] at hq
  have := bases_zip hq
  have := le_block (fs := fs) (lp := lp) I.t
  have := h.2.2
  exact absurd hF.2 (by omega)

/-- **A loop's next iteration follows its frame**: a loop helper's last callee, its tail call, is
at `fp · g^S`. -/
theorem Inst.PlacedA.kidFps_getLast? {I : Inst} (h : I.PlacedA fs lp al) (hl : lp I.t.name = true)
    (hk : I.t.kids ≠ []) : I.kidFps.getLast? = some (I.fp + fs I.t.name) := by
  rw [h.1]
  obtain ⟨l, b, he⟩ := (List.eq_nil_or_concat I.t.kids).resolve_left hk
  unfold kidPosA
  rw [ite_eq_left_of_eq_true _ _ (eq_true hl), he, List.concat_eq_append, (posL_split (fs := fs) (lp := lp) (al := al)).1]
  simp

/-- The `i`-th callee at `ps` is an instance at `ps[i]`, with header `H I (j + i)`. -/
theorem instsKidsA_kid : ∀ (ks : List Tree) (ps : List (ℕ × ℕ)) (I : Inst) (j i : ℕ) {k : Tree}
    {p : ℕ × ℕ}, ks[i]? = some k → ps[i]? = some p →
    ∃ J ∈ Tree.instsKidsA fs lp al H I j ps ks, J.t = k ∧ J.fp = p.1 ∧ J.hdr = H I (j + i)
  | [], _, _, _, _, _, _, h, _ => by simp at h
  | _ :: _, [], _, _, _, _, _, _, h => by simp at h
  | k' :: ks, p' :: ps, I, j, 0, k, p, h, h' => by
      obtain rfl : k' = k := by simpa using h
      obtain rfl : p' = p := by simpa using h'
      obtain ⟨J, rest, he, ht, hfp, -, hh⟩ := head_instsA (fs := fs) (lp := lp) (al := al) (H := H) k' p' (H I j)
      refine ⟨J, ?_, ht, hfp, by rw [hh, Nat.add_zero]⟩
      rw [instsKidsA_cons, he]; exact List.mem_append_left _ List.mem_cons_self
  | k' :: ks, p' :: ps, I, j, i + 1, k, p, h, h' => by
      obtain ⟨J, hJ, ht, hfp, hh⟩ :=
        instsKidsA_kid ks ps I (j + 1) i (by simpa using h) (by simpa using h')
      refine ⟨J, ?_, ht, hfp, by rw [hh]; congr 1; omega⟩
      rw [instsKidsA_cons]
      exact List.mem_append_right _ hJ

mutual
/-- **Callees are instances**: the `i`-th callee of an instance is an instance at the `i`-th
callee frame, with header `H I i`. -/
theorem instsA_kid : ∀ (t : Tree) (p : ℕ × ℕ) (hdr : E × E), ∀ I ∈ t.instsA fs lp al H p hdr,
    ∀ (i : ℕ) (k : Tree), I.t.kids[i]? = some k →
      ∃ J ∈ t.instsA fs lp al H p hdr, J.t = k ∧ I.kidFps[i]? = some J.fp ∧ J.hdr = H I i
  | .node f σ bufs kids, p, hdr, I, hI, i, k, hk => by
      rw [instsA_node, List.mem_cons] at hI
      rcases hI with rfl | hI
      · have hi : i < (kidPosA fs lp al p f bufs kids).length := by
          rw [length_kidPosA]
          exact (List.getElem?_eq_some_iff.mp hk).1
        obtain ⟨q, hq⟩ : ∃ q, (kidPosA fs lp al p f bufs kids)[i]? = some q :=
          ⟨_, List.getElem?_eq_getElem hi⟩
        obtain ⟨J, hJ, ht, hfp, hh⟩ := instsKidsA_kid (fs := fs) (lp := lp) (al := al) (H := H) kids _ _ 0 i hk hq
        refine ⟨J, ?_, ht, by simp only [List.getElem?_map, hq, hfp]; rfl, by simpa using hh⟩
        rw [instsA_node]; exact List.mem_cons_of_mem _ hJ
      · obtain ⟨J, hJ, h⟩ := instsKidsA_kids_kid kids _ _ 0 I hI i k hk
        refine ⟨J, ?_, h⟩
        rw [instsA_node]; exact List.mem_cons_of_mem _ hJ
  | .phantom f σ, p, hdr, I, hI, i, k, hk => by
      rw [instsA_phantom, List.mem_singleton] at hI
      subst hI
      simp [Tree.kids] at hk

/-- `instsA_kid` for the callees. -/
theorem instsKidsA_kids_kid : ∀ (ks : List Tree) (ps : List (ℕ × ℕ)) (I : Inst) (j : ℕ),
    ∀ J ∈ Tree.instsKidsA fs lp al H I j ps ks, ∀ (i : ℕ) (k : Tree), J.t.kids[i]? = some k →
      ∃ J' ∈ Tree.instsKidsA fs lp al H I j ps ks, J'.t = k ∧ J.kidFps[i]? = some J'.fp ∧
        J'.hdr = H J i
  | [], _, _, _, J, hJ, _, _, _ => by rw [instsKidsA_nil] at hJ; exact (List.not_mem_nil hJ).elim
  | _ :: _, [], _, _, J, hJ, _, _, _ => by
      rw [instsKidsA_nil_left] at hJ; exact (List.not_mem_nil hJ).elim
  | k' :: ks, p :: ps, I, j, J, hJ, i, k, hk => by
      rw [instsKidsA_cons, List.mem_append] at hJ
      rw [instsKidsA_cons]
      rcases hJ with hJ | hJ
      · obtain ⟨J', hJ', h⟩ := instsA_kid k' _ _ J hJ i k hk
        exact ⟨J', List.mem_append_left _ hJ', h⟩
      · obtain ⟨J', hJ', h⟩ := instsKidsA_kids_kid ks ps I (j + 1) J hJ i k hk
        exact ⟨J', List.mem_append_right _ hJ', h⟩
end

/-- A subtree's frame is within the words it uses from its block. -/
theorem fsz_le_wordsA (t : Tree) : t.fsz fs ≤ t.wordsA fs lp al := by
  have := le_block (fs := fs) (lp := lp) t
  have := le_endA (fs := fs) (lp := lp) (al := al) t (t.block fs lp)
  unfold Tree.wordsA
  omega

end

end LeanVM.Guest.Memory
