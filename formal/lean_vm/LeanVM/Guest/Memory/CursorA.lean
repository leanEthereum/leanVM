/-
  LeanVM.Guest.Memory.CursorA

  The aligned bump allocator's cursor along an instance: past some of its `HeapBuf`s and calls,
  where its callees land, and where its subtree ends.
-/

module

public import LeanVM.Guest.Memory.AllocA

/-!
# The aligned cursor along an instance

The bus era's `Memory/Cursor.lean` on Hotwire's aligned allocator (`Tree.instsA`, `kidPosA`): a
callee entered fresh starts at `allocBase (al k) c`, so the cursor past a callee is not the cursor
plus its words but its end, `kidEnd c k`, and the cursor past callees is a fold (`curF`, which is
`Tree.endF`).

`Inst.curA I nb nc`: instance `I`'s cursor past its first `nb` `HeapBuf`s and its first `nc`
callees, a loop helper's tail call apart (`Tree.kidsC`: its frame is in the loop's block, its
region after the iteration's). `Inst.endCurA I`: where its subtree's words past its block end
(`Tree.endA`), the same for every iteration of a loop (`endCurA_tail`).

What the allocator's order gives (`instsA_kid_pos`, every callee instance at its `kidPosA`): a callee
not a tail call is at the aligned base of the cursor past every `HeapBuf` and the callees before it,
its own cursor after its block (`kid_posA`), and its subtree ends where the caller's cursor goes past
it (`endCurA_kid`); a loop's tail call starts its cursor where the iteration's ends and ends where the
iteration does (`tail_posA`, `endCurA_tail`); an instance whose last callee is not a loop's tail call
entered ends at its cursor past everything (`endCurA_ret`).
-/

namespace LeanVM.Guest.Memory

open LeanVM.Parameters LeanVM.Guest.Core
open LeanVM.Prover.Exec (allocBase keccakWindow)

@[expose] public section

variable (fs : String → ℕ) (lp al : String → Bool)

/-- The callees whose regions an instance's cursor passes: a loop helper's tail call apart. -/
def Tree.kidsC (t : Tree) : List Tree := if lp t.name then t.kids.dropLast else t.kids

/-- **The cursor past callee `k` entered fresh from `c`**: its block at the aligned base, then its
subtree's other words. -/
def kidEnd (c : ℕ) (k : Tree) : ℕ := k.endA fs lp al (allocBase (al k.name) c + k.block fs lp)

/-- The cursor past callees entered fresh from `c`, in turn. -/
def curF (c : ℕ) (ks : List Tree) : ℕ := ks.foldl (kidEnd fs lp al) c

/-- **An instance's cursor** past its first `nb` `HeapBuf`s and `nc` callees. -/
def Inst.curA (I : Inst) (nb nc : ℕ) : ℕ :=
  curF fs lp al (I.cur + (I.t.bufs.take nb).sum) ((I.t.kidsC lp).take nc)

/-- **Where an instance's subtree ends**: its cursor past its words beyond its block. -/
def Inst.endCurA (I : Inst) : ℕ := I.t.endA fs lp al I.cur

variable {fs lp al}

/-! ## The cursor past callees -/

theorem curF_nil (c : ℕ) : curF fs lp al c [] = c := rfl

theorem curF_cons (c : ℕ) (k : Tree) (ks : List Tree) :
    curF fs lp al c (k :: ks) = curF fs lp al (kidEnd fs lp al c k) ks := rfl

theorem curF_append (c : ℕ) (ks ks' : List Tree) :
    curF fs lp al c (ks ++ ks') = curF fs lp al (curF fs lp al c ks) ks' := by
  unfold curF; rw [List.foldl_append]

theorem endF_eq_curF : ∀ (c : ℕ) (ks : List Tree), Tree.endF fs lp al c ks = curF fs lp al c ks
  | c, [] => by rw [endF_nil]; rfl
  | c, k :: ks => by rw [endF_cons, curF_cons, endF_eq_curF _ ks]; rfl

theorem posF_getElem? : ∀ (c : ℕ) (ks : List Tree) (i : ℕ) (k : Tree), ks[i]? = some k →
    (posF fs lp al c ks)[i]? = some (allocBase (al k.name) (curF fs lp al c (ks.take i)),
      allocBase (al k.name) (curF fs lp al c (ks.take i)) + k.block fs lp)
  | _, [], _, _, h => by simp at h
  | c, k' :: ks, 0, k, h => by
      obtain rfl : k' = k := by simpa using h
      simp [posF, curF_nil]
  | c, k' :: ks, i + 1, k, h => by
      rw [posF, List.getElem?_cons_succ, posF_getElem? _ ks i k (by simpa using h), List.take_succ_cons,
        curF_cons]
      rfl

theorem kidsC_of_loop {t : Tree} (hl : lp t.name = true) : t.kidsC lp = t.kids.dropLast := by
  unfold Tree.kidsC; rw [ite_eq_left hl]

theorem kidsC_of_not_loop {t : Tree} (hl : ¬ lp t.name = true) : t.kidsC lp = t.kids := by
  unfold Tree.kidsC; rw [ite_eq_right hl]

theorem kidsC_getElem? {t : Tree} {i : ℕ} {k : Tree} (h : (t.kidsC lp)[i]? = some k) : t.kids[i]? = some k := by
  unfold Tree.kidsC at h
  split at h
  · rw [List.getElem?_dropLast] at h
    split at h
    · exact h
    · cases h
  · exact h

theorem kidsC_length_le (t : Tree) : (t.kidsC lp).length ≤ t.kids.length := by
  unfold Tree.kidsC; split <;> simp

/-- **A callee not a loop's tail call**: at the aligned base of the cursor past every `HeapBuf` and
the callees before it, its own cursor after its block. -/
theorem kid_posA {I : Inst} {i : ℕ} {k : Tree} (hk : (I.t.kidsC lp)[i]? = some k) :
    (kidPosA fs lp al (I.fp, I.cur) I.t.name I.t.bufs I.t.kids)[i]? =
      some (allocBase (al k.name) (I.curA fs lp al I.t.bufs.length i),
        allocBase (al k.name) (I.curA fs lp al I.t.bufs.length i) + k.block fs lp) := by
  unfold Inst.curA
  rw [List.take_length]
  unfold kidPosA
  by_cases hl : lp I.t.name = true
  · rw [ite_eq_left hl]
    rw [kidsC_of_loop hl] at hk ⊢
    have hne : I.t.kids ≠ [] := by
      intro h; rw [h] at hk; simp at hk
    obtain ⟨l, b, he⟩ := (List.eq_nil_or_concat I.t.kids).resolve_left hne
    rw [he, List.concat_eq_append] at hk ⊢
    rw [List.dropLast_concat] at hk ⊢
    have hi : i < l.length := (List.getElem?_eq_some_iff.mp hk).1
    rw [(posL_split (fs := fs) (lp := lp) (al := al) (tl := I.fp + fs I.t.name)
      (c := I.cur + I.t.bufs.sum) (l := l) (b := b)).1,
      List.getElem?_append_left (by rw [length_posF]; exact hi), posF_getElem? _ _ _ _ hk]
  · rw [ite_eq_right hl]
    rw [kidsC_of_not_loop hl] at hk ⊢
    exact posF_getElem? _ _ _ _ hk

/-- **A loop's tail call**: at the next frame, its cursor where the iteration's cursor is past every
`HeapBuf` and its other callees. -/
theorem tail_posA {I : Inst} (hl : lp I.t.name = true) (hk : I.t.kids ≠ []) :
    (kidPosA fs lp al (I.fp, I.cur) I.t.name I.t.bufs I.t.kids)[I.t.kids.length - 1]? =
      some (I.fp + fs I.t.name, I.curA fs lp al I.t.bufs.length (I.t.kidsC lp).length) := by
  unfold Inst.curA
  rw [List.take_length, List.take_length]
  unfold kidPosA
  rw [ite_eq_left hl, kidsC_of_loop hl]
  obtain ⟨l, b, he⟩ := (List.eq_nil_or_concat I.t.kids).resolve_left hk
  rw [he, List.concat_eq_append, List.dropLast_concat,
    (posL_split (fs := fs) (lp := lp) (al := al) (tl := I.fp + fs I.t.name)
      (c := I.cur + I.t.bufs.sum) (l := l) (b := b)).1, List.length_append, List.length_singleton,
    Nat.add_sub_cancel, List.getElem?_append_right (by rw [length_posF]), length_posF, Nat.sub_self,
    endF_eq_curF]
  rfl

/-! ## Where a subtree ends -/

theorem curA_succ {I : Inst} {nb nc : ℕ} {k : Tree} (hk : (I.t.kidsC lp)[nc]? = some k) :
    I.curA fs lp al nb (nc + 1) = kidEnd fs lp al (I.curA fs lp al nb nc) k := by
  unfold Inst.curA
  rw [List.take_add_one, hk, Option.toList_some, curF_append, curF_cons, curF_nil]

/-- **A callee not a loop's tail call ends where the caller's cursor goes past it.** -/
theorem endCurA_kid {I J : Inst} {i : ℕ} (hk : (I.t.kidsC lp)[i]? = some J.t)
    (hcur : J.cur = allocBase (al J.t.name) (I.curA fs lp al I.t.bufs.length i) + J.t.block fs lp) :
    J.endCurA fs lp al = I.curA fs lp al I.t.bufs.length (i + 1) := by
  rw [curA_succ hk, Inst.endCurA, hcur]
  rfl

/-- **A loop's tail call ends where the iteration does.** -/
theorem endCurA_tail {I J : Inst} (hl : lp I.t.name = true) (hk : I.t.kids ≠ [])
    (ht : J.t = I.t.kids.getLast hk)
    (hcur : J.cur = I.curA fs lp al I.t.bufs.length (I.t.kidsC lp).length)
    (hI : ∃ f σ bufs kids, I.t = .node f σ bufs kids) :
    J.endCurA fs lp al = I.endCurA fs lp al := by
  obtain ⟨f, σ, bufs, kids, hIt⟩ := hI
  have hl' : lp f = true := by rw [hIt] at hl; exact hl
  have hk' : kids ≠ [] := by rw [hIt] at hk; exact hk
  obtain ⟨l, b, he⟩ := (List.eq_nil_or_concat kids).resolve_left hk'
  rw [List.concat_eq_append] at he
  have hJt : J.t = b := by
    rw [ht]; simp only [hIt, Tree.kids, he, List.getLast_append_singleton]
  unfold Inst.curA at hcur
  rw [List.take_length, List.take_length, kidsC_of_loop hl] at hcur
  simp only [hIt, Tree.kids, Tree.bufs, he, List.dropLast_concat] at hcur
  rw [Inst.endCurA, Inst.endCurA, hIt, endA_node, ite_eq_left hl', he,
    (posL_split (fs := fs) (lp := lp) (al := al) (tl := 0) (c := I.cur + bufs.sum) (l := l) (b := b)).2,
    endF_eq_curF, ← hcur, hJt]

/-- **An instance whose callees left are none ends at its cursor past everything**, a loop
iteration whose last callee is a phantom (its tail call not taken) included. -/
theorem endCurA_ret {I : Inst} (hI : ∃ f σ bufs kids, I.t = .node f σ bufs kids)
    (hlast : lp I.t.name = true → ∀ hk : I.t.kids ≠ [], ∃ f σ, I.t.kids.getLast hk = .phantom f σ) :
    I.endCurA fs lp al = I.curA fs lp al I.t.bufs.length (I.t.kidsC lp).length := by
  obtain ⟨f, σ, bufs, kids, hIt⟩ := hI
  unfold Inst.curA
  rw [List.take_length, List.take_length, Inst.endCurA]
  by_cases hl : lp I.t.name = true
  · rw [kidsC_of_loop hl]
    have hl' : lp f = true := by rw [hIt] at hl; exact hl
    by_cases hk : I.t.kids = []
    · have hk' : kids = [] := by rw [hIt] at hk; exact hk
      subst hk'
      rw [hk, hIt, endA_node, ite_eq_left hl', endL_nil]
      rfl
    · obtain ⟨g, τ, hg⟩ := hlast hl hk
      simp only [hIt, Tree.kids, Tree.bufs] at hk hg ⊢
      obtain ⟨l, b, he⟩ := (List.eq_nil_or_concat kids).resolve_left hk
      rw [List.concat_eq_append] at he
      subst he
      rw [List.getLast_append_singleton] at hg
      subst hg
      rw [endA_node, ite_eq_left hl',
        (posL_split (fs := fs) (lp := lp) (al := al) (tl := 0) (c := I.cur + bufs.sum) (l := l)
          (b := .phantom g τ)).2, endA_phantom, endF_eq_curF, List.dropLast_concat]
  · rw [kidsC_of_not_loop hl]
    have hl' : ¬ lp f = true := by rw [hIt] at hl; exact hl
    rw [hIt, endA_node, ite_eq_right hl', endF_eq_curF]
    rfl

/-! ## Monotonicity -/

theorem allocBase_mono {a : Bool} {c c' : ℕ} (h : c ≤ c') : allocBase a c ≤ allocBase a c' := by
  unfold allocBase keccakWindow
  split
  · have := Nat.div_le_div_right (c := 16) (show c + 16 - 1 ≤ c' + 16 - 1 by omega)
    have := Nat.mul_le_mul_right 16 this
    omega
  · exact h

mutual
theorem endA_mono : ∀ (t : Tree) {c c' : ℕ}, c ≤ c' → t.endA fs lp al c ≤ t.endA fs lp al c'
  | .node f σ bufs kids, c, c', h => by
      rw [endA_node, endA_node]
      split
      · exact endL_mono kids (by omega)
      · exact endF_mono kids (by omega)
  | .phantom f σ, c, c', h => by rw [endA_phantom, endA_phantom]; exact h

theorem endF_mono : ∀ (ks : List Tree) {c c' : ℕ}, c ≤ c' → Tree.endF fs lp al c ks ≤ Tree.endF fs lp al c' ks
  | [], c, c', h => by rw [endF_nil, endF_nil]; exact h
  | k :: ks, c, c', h => by
      rw [endF_cons, endF_cons]
      exact endF_mono ks (endA_mono k (by have := allocBase_mono (a := al k.name) h; omega))

theorem endL_mono : ∀ (ks : List Tree) {c c' : ℕ}, c ≤ c' → Tree.endL fs lp al c ks ≤ Tree.endL fs lp al c' ks
  | [], c, c', h => by rw [endL_nil, endL_nil]; exact h
  | [k], c, c', h => by rw [endL_one, endL_one]; exact endA_mono k h
  | k :: k' :: ks, c, c', h => by
      rw [endL_cons, endL_cons]
      exact endL_mono (k' :: ks) (endA_mono k (by have := allocBase_mono (a := al k.name) h; omega))
end

theorem kidEnd_mono {c c' : ℕ} (h : c ≤ c') (k : Tree) : kidEnd fs lp al c k ≤ kidEnd fs lp al c' k :=
  endA_mono k (by have := allocBase_mono (a := al k.name) h; omega)

theorem le_kidEnd (c : ℕ) (k : Tree) : allocBase (al k.name) c + k.block fs lp ≤ kidEnd fs lp al c k :=
  le_endA k _

theorem curF_mono : ∀ (ks : List Tree) {c c' : ℕ}, c ≤ c' → curF fs lp al c ks ≤ curF fs lp al c' ks
  | [], _, _, h => h
  | k :: ks, _, _, h => curF_mono ks (kidEnd_mono h k)

theorem le_curF : ∀ (c : ℕ) (ks : List Tree), c ≤ curF fs lp al c ks
  | _, [] => le_rfl
  | c, k :: ks => by
      have h1 := le_kidEnd (fs := fs) (lp := lp) (al := al) c k
      have h2 := le_curF (kidEnd fs lp al c k) ks
      have := le_allocBase (al k.name) c
      rw [curF_cons]; omega

theorem curF_take_le (c : ℕ) (ks : List Tree) (n : ℕ) : curF fs lp al c (ks.take n) ≤ curF fs lp al c ks := by
  conv_rhs => rw [← List.take_append_drop n ks]
  rw [curF_append]
  exact le_curF _ _

/-- **The cursor stays within the subtree**: past at most every `HeapBuf` and callee. -/
theorem curA_le_endCurA {I : Inst} (hI : ∃ f σ bufs kids, I.t = .node f σ bufs kids) (nb nc : ℕ) :
    I.curA fs lp al nb nc ≤ I.endCurA fs lp al := by
  obtain ⟨f, σ, bufs, kids, hIt⟩ := hI
  have hb : (I.t.bufs.take nb).sum ≤ I.t.bufs.sum :=
    List.Sublist.sum_le_sum (List.take_sublist _ _) (fun _ _ ↦ Nat.zero_le _)
  have h1 : I.curA fs lp al nb nc ≤ curF fs lp al (I.cur + I.t.bufs.sum) (I.t.kidsC lp) :=
    (curF_mono _ (by omega)).trans (curF_take_le _ _ _)
  refine h1.trans ?_
  rw [Inst.endCurA]
  by_cases hl : lp I.t.name = true
  · rw [kidsC_of_loop hl]
    have hl' : lp f = true := by rw [hIt] at hl; exact hl
    simp only [hIt, Tree.kids, Tree.bufs]
    rw [endA_node, ite_eq_left hl']
    by_cases hk : kids = []
    · subst hk; simp [endL_nil, curF_nil]
    · obtain ⟨l, b, he⟩ := (List.eq_nil_or_concat kids).resolve_left hk
      rw [List.concat_eq_append] at he
      subst he
      rw [List.dropLast_concat, (posL_split (fs := fs) (lp := lp) (al := al) (tl := 0)
        (c := I.cur + bufs.sum) (l := l) (b := b)).2, endF_eq_curF]
      exact le_endA b _
  · rw [kidsC_of_not_loop hl]
    have hl' : ¬ lp f = true := by rw [hIt] at hl; exact hl
    simp only [hIt, Tree.kids, Tree.bufs]
    rw [endA_node, ite_eq_right hl', endF_eq_curF]

/-- A reserved callee's block stays within the subtree. -/
theorem curA_block_le {I : Inst} (hI : ∃ f σ bufs kids, I.t = .node f σ bufs kids) {nb nc : ℕ} {k : Tree}
    (hk : (I.t.kidsC lp)[nc]? = some k) :
    allocBase (al k.name) (I.curA fs lp al nb nc) + k.block fs lp ≤ I.endCurA fs lp al := by
  have h1 := le_kidEnd (fs := fs) (lp := lp) (al := al) (I.curA fs lp al nb nc) k
  rw [← curA_succ hk] at h1
  exact h1.trans (curA_le_endCurA hI _ _)

/-! ## The instances' positions -/

variable {H : Inst → ℕ → E × E}

theorem instsKidsA_kid_pos : ∀ (ks : List Tree) (ps : List (ℕ × ℕ)) (I : Inst) (j i : ℕ) {k : Tree}
    {p : ℕ × ℕ}, ks[i]? = some k → ps[i]? = some p →
    ∃ J ∈ Tree.instsKidsA fs lp al H I j ps ks, J.t = k ∧ J.fp = p.1 ∧ J.cur = p.2
  | [], _, _, _, _, _, _, h, _ => by simp at h
  | _ :: _, [], _, _, _, _, _, _, h => by simp at h
  | k' :: ks, p' :: ps, I, j, 0, k, p, h, h' => by
      obtain rfl : k' = k := by simpa using h
      obtain rfl : p' = p := by simpa using h'
      obtain ⟨J, rest, he, ht, hfp, hcur, -⟩ :=
        head_instsA (fs := fs) (lp := lp) (al := al) (H := H) k' p' (H I j)
      refine ⟨J, ?_, ht, hfp, hcur⟩
      rw [instsKidsA_cons, he]; exact List.mem_append_left _ List.mem_cons_self
  | k' :: ks, p' :: ps, I, j, i + 1, k, p, h, h' => by
      obtain ⟨J, hJ, h1⟩ := instsKidsA_kid_pos ks ps I (j + 1) i (by simpa using h) (by simpa using h')
      exact ⟨J, by rw [instsKidsA_cons]; exact List.mem_append_right _ hJ, h1⟩

mutual
/-- **Every callee instance at its position**: the `i`-th callee of an instance is an instance at
the `i`-th position `kidPosA` gives, frame and cursor. -/
theorem instsA_kid_pos : ∀ (t : Tree) (p : ℕ × ℕ) (hdr : E × E), ∀ I ∈ t.instsA fs lp al H p hdr,
    ∀ (i : ℕ) (k : Tree), I.t.kids[i]? = some k →
      ∃ J ∈ t.instsA fs lp al H p hdr, J.t = k ∧
        (kidPosA fs lp al (I.fp, I.cur) I.t.name I.t.bufs I.t.kids)[i]? = some (J.fp, J.cur)
  | .node f σ bufs kids, p, hdr, I, hI, i, k, hk => by
      rw [instsA_node, List.mem_cons] at hI
      rcases hI with rfl | hI
      · have hi : i < (kidPosA fs lp al p f bufs kids).length := by
          rw [length_kidPosA]
          exact (List.getElem?_eq_some_iff.mp hk).1
        obtain ⟨q, hq⟩ : ∃ q, (kidPosA fs lp al p f bufs kids)[i]? = some q :=
          ⟨_, List.getElem?_eq_getElem hi⟩
        obtain ⟨J, hJ, ht, hfp, hcur⟩ :=
          instsKidsA_kid_pos (fs := fs) (lp := lp) (al := al) (H := H) kids _ _ 0 i hk hq
        refine ⟨J, ?_, ht, ?_⟩
        · rw [instsA_node]; exact List.mem_cons_of_mem _ hJ
        · simp only [Tree.name, Tree.bufs, Tree.kids]; rw [hq, hfp, hcur]
      · obtain ⟨J, hJ, h⟩ := instsKidsA_kid_pos' kids _ _ 0 I hI i k hk
        refine ⟨J, ?_, h⟩
        rw [instsA_node]; exact List.mem_cons_of_mem _ hJ
  | .phantom f σ, p, hdr, I, hI, i, k, hk => by
      rw [instsA_phantom, List.mem_singleton] at hI
      subst hI
      simp [Tree.kids] at hk

/-- `instsA_kid_pos` for the callees. -/
theorem instsKidsA_kid_pos' : ∀ (ks : List Tree) (ps : List (ℕ × ℕ)) (I : Inst) (j : ℕ),
    ∀ J ∈ Tree.instsKidsA fs lp al H I j ps ks, ∀ (i : ℕ) (k : Tree), J.t.kids[i]? = some k →
      ∃ J' ∈ Tree.instsKidsA fs lp al H I j ps ks, J'.t = k ∧
        (kidPosA fs lp al (J.fp, J.cur) J.t.name J.t.bufs J.t.kids)[i]? = some (J'.fp, J'.cur)
  | [], _, _, _, J, hJ, _, _, _ => by rw [instsKidsA_nil] at hJ; exact (List.not_mem_nil hJ).elim
  | _ :: _, [], _, _, J, hJ, _, _, _ => by
      rw [instsKidsA_nil_left] at hJ; exact (List.not_mem_nil hJ).elim
  | k' :: ks, p :: ps, I, j, J, hJ, i, k, hk => by
      rw [instsKidsA_cons, List.mem_append] at hJ
      rw [instsKidsA_cons]
      rcases hJ with hJ | hJ
      · obtain ⟨J', hJ', h⟩ := instsA_kid_pos k' _ _ J hJ i k hk
        exact ⟨J', List.mem_append_left _ hJ', h⟩
      · obtain ⟨J', hJ', h⟩ := instsKidsA_kid_pos' ks ps I (j + 1) J hJ i k hk
        exact ⟨J', List.mem_append_right _ hJ', h⟩
end

end

end LeanVM.Guest.Memory
