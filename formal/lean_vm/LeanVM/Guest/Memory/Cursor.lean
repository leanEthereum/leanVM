/-
  LeanVM.Guest.Memory.Cursor

  The bump allocator's cursor along an instance: past some of its `HeapBuf`s and calls, where its
  callees land, and where its subtree ends.
-/

module

public import LeanVM.Guest.Memory.Alloc

/-!
# The cursor along an instance

`Inst.curAt I nb nc`: instance `I`'s cursor past its first `nb` `HeapBuf`s and the words of its first
`nc` callees, a loop helper's tail call apart (`Tree.kidsC`: its words are counted by the loop's
block, at the loop's entry). `Inst.endCur I`: where its subtree's words past its block end, the
same for every iteration of a loop (`endCur_tail`).

What the allocator's order gives (`insts_kid_pos`, every callee instance at its `kidPos`): a callee
not a tail call is at the cursor past every `HeapBuf` and the callees before it, its own cursor after
its block (`kid_pos`), and its subtree ends where the caller's cursor goes past it (`endCur_kid`);
a loop's tail call starts its cursor where the iteration's ends and ends where the iteration does
(`tail_pos`, `endCur_tail`); an instance whose last call is not a loop's tail call entered ends at
its cursor past everything (`endCur_ret`). `inst_eq_of_fp`: two honest instances at one frame are
one.
-/

namespace LeanVM.Guest.Memory

open LeanVM.Parameters LeanVM.Guest.Core

@[expose] public section

variable (fs : String → ℕ) (lp : String → Bool)

/-- The callees whose words an instance's cursor passes: a loop helper's tail call apart. -/
def Tree.kidsC (t : Tree) : List Tree := if lp t.name then t.kids.dropLast else t.kids

/-- **An instance's cursor** past its first `nb` `HeapBuf`s and `nc` callees. -/
def Inst.curAt (I : Inst) (nb nc : ℕ) : ℕ :=
  I.cur + (I.t.bufs.take nb).sum + (((I.t.kidsC lp).take nc).map (Tree.total fs)).sum

/-- **Where an instance's subtree ends**: its cursor past its words beyond its block. -/
def Inst.endCur (I : Inst) : ℕ := I.cur + (I.t.total fs - I.t.block fs lp)

variable {fs lp}

/-! ## Regions one after another -/

theorem basesC_getElem? : ∀ (b : ℕ) (ns : List (ℕ × ℕ)) (i : ℕ) (hi : i < ns.length),
    (basesC b ns)[i]? = some (b + ((ns.take i).map Prod.fst).sum, b + ((ns.take i).map Prod.fst).sum + ns[i].2)
  | _, [], _, hi => absurd hi (Nat.not_lt_zero _)
  | b, n :: ns, 0, _ => by simp [basesC]
  | b, n :: ns, i + 1, hi => by
    simp only [basesC, List.getElem?_cons_succ, List.take_succ_cons, List.map_cons, List.sum_cons,
      List.getElem_cons_succ]
    rw [basesC_getElem? (b + n.1) ns i (by simpa using hi)]
    simp only [Nat.add_assoc]

theorem kidsC_length_le (t : Tree) : (t.kidsC lp).length ≤ t.kids.length := by
  unfold Tree.kidsC; split <;> simp

theorem kidsC_getElem {t : Tree} {i : ℕ} (hi : i < (t.kidsC lp).length) :
    (t.kidsC lp)[i] = t.kids[i]'(lt_of_lt_of_le hi (kidsC_length_le t)) := by
  unfold Tree.kidsC at hi ⊢
  split
  · simp [List.getElem_dropLast]
  · rfl

theorem take_kidsC {t : Tree} {i : ℕ} (hi : i ≤ (t.kidsC lp).length) :
    (t.kidsC lp).take i = t.kids.take i := by
  unfold Tree.kidsC at hi ⊢
  split
  · rename_i h
    rw [ite_eq_left h] at hi
    rw [List.dropLast_eq_take, List.take_take, Nat.min_eq_left]
    simpa using hi
  · rfl

theorem take_dropLast' {α : Type} {l : List α} {i : ℕ} (h : i ≤ l.dropLast.length) :
    l.dropLast.take i = l.take i := by
  rw [List.dropLast_eq_take, List.take_take, Nat.min_eq_left (by simpa using h)]

theorem blockLast_getLast : ∀ (ks : List Tree) (hk : ks ≠ []),
    Tree.blockLast fs lp ks = (ks.getLast hk).block fs lp
  | [], hk => absurd rfl hk
  | [k], _ => by simp [Tree.blockLast]
  | k :: k' :: ks, _ => by
    rw [Tree.blockLast, blockLast_getLast (k' :: ks) (by simp), List.getLast_cons_cons]

theorem block_loop {t : Tree} (ht : ∃ f σ bufs kids, t = .node f σ bufs kids) (hl : lp t.name = true) :
    t.block fs lp = fs t.name + Tree.blockLast fs lp t.kids := by
  obtain ⟨f, σ, bufs, kids, rfl⟩ := ht
  simp only [Tree.name, Tree.kids] at hl ⊢
  rw [Tree.block, ite_eq_left hl]

theorem block_not_loop {t : Tree} (ht : ∃ f σ bufs kids, t = .node f σ bufs kids) (hl : ¬ lp t.name = true) :
    t.block fs lp = fs t.name := by
  obtain ⟨f, σ, bufs, kids, rfl⟩ := ht
  simp only [Tree.name] at hl ⊢
  rw [Tree.block, ite_eq_right hl, Nat.add_zero]

theorem total_eq {t : Tree} (ht : ∃ f σ bufs kids, t = .node f σ bufs kids) :
    t.total fs = fs t.name + (t.kids.map (Tree.total fs)).sum + t.bufs.sum := by
  obtain ⟨f, σ, bufs, kids, rfl⟩ := ht
  rw [total_node, totalKids_eq_sum]; rfl

/-- **A callee not a loop's tail call**: at the cursor past every `HeapBuf` and the callees before
it, its own cursor after its block. -/
theorem kid_pos {I : Inst} {i : ℕ} (hi : i < (I.t.kidsC lp).length) :
    (kidPos fs lp (I.fp, I.cur) I.t.name I.t.bufs (I.t.kids.map (Tree.sz fs lp)))[i]? =
      some (I.curAt fs lp I.t.bufs.length i,
        I.curAt fs lp I.t.bufs.length i + ((I.t.kidsC lp)[i]).block fs lp) := by
  have hik : i < I.t.kids.length := lt_of_lt_of_le hi (kidsC_length_le _)
  have hcur : I.curAt fs lp I.t.bufs.length i =
      I.cur + I.t.bufs.sum + (((I.t.kids.map (Tree.sz fs lp)).take i).map Prod.fst).sum := by
    rw [Inst.curAt, List.take_length, take_kidsC hi.le, ← List.map_take, map_sz_fst]
  rw [hcur, kidsC_getElem hi]
  unfold kidPos
  split
  · rename_i hl
    have hi' : i < ((I.t.kids.map (Tree.sz fs lp)).dropLast).length := by
      unfold Tree.kidsC at hi; rw [ite_eq_left hl] at hi; simpa using hi
    rw [List.getElem?_append_left (by rw [length_basesC]; exact hi'), basesC_getElem? _ _ _ hi',
      take_dropLast' hi'.le]
    simp [List.getElem_dropLast, Tree.sz]
  · rw [basesC_getElem? _ _ _ (by simpa using hik)]
    simp only [List.getElem_map, Option.some.injEq, Prod.mk.injEq, true_and]
    rfl

/-- **A loop's tail call**: at the next frame, its cursor where the iteration's cursor is past
every `HeapBuf` and its other callees. -/
theorem tail_pos {I : Inst} (hl : lp I.t.name = true) (hk : I.t.kids ≠ []) :
    (kidPos fs lp (I.fp, I.cur) I.t.name I.t.bufs (I.t.kids.map (Tree.sz fs lp)))[I.t.kids.length - 1]? =
      some (I.fp + fs I.t.name, I.curAt fs lp I.t.bufs.length (I.t.kidsC lp).length) := by
  obtain ⟨l, b, he⟩ := List.eq_nil_or_concat (I.t.kids.map (Tree.sz fs lp)) |>.resolve_left
    (by simpa using hk)
  have hlen : I.t.kids.length - 1 = l.length := by
    have := congrArg List.length he; simp at this; omega
  have hkc : I.t.kidsC lp = I.t.kids.dropLast := by unfold Tree.kidsC; rw [ite_eq_left hl]
  have hsum : ((I.t.kids.dropLast).map (Tree.total fs)).sum = (l.map Prod.fst).sum := by
    rw [← map_sz_fst (lp := lp), List.map_dropLast, he, List.concat_eq_append, List.dropLast_concat]
  rw [he, List.concat_eq_append, kidPos_loop hl, hlen,
    List.getElem?_append_right (by rw [length_basesC]), length_basesC, Nat.sub_self]
  simp only [List.getElem?_cons_zero, Option.some.injEq, Prod.mk.injEq, true_and]
  rw [Inst.curAt, List.take_length, hkc, List.take_length, hsum]

/-! ## Where a subtree ends -/

theorem curAt_succ {I : Inst} {nc : ℕ} (hnc : nc < (I.t.kidsC lp).length) :
    I.curAt fs lp I.t.bufs.length (nc + 1) =
      I.curAt fs lp I.t.bufs.length nc + ((I.t.kidsC lp)[nc]).total fs := by
  simp only [Inst.curAt, List.take_add_one, List.getElem?_eq_getElem hnc, Option.toList_some,
    List.map_append, List.sum_append, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
  omega

/-- **A callee not a loop's tail call ends where the caller's cursor goes past it.** -/
theorem endCur_kid {I J : Inst} {i : ℕ} (hi : i < (I.t.kidsC lp).length) (ht : J.t = (I.t.kidsC lp)[i])
    (hfp : J.fp = I.curAt fs lp I.t.bufs.length i) (hcur : J.cur = J.fp + J.t.block fs lp) :
    J.endCur fs lp = I.curAt fs lp I.t.bufs.length (i + 1) := by
  have := block_le_total (fs := fs) (lp := lp) J.t
  rw [Inst.endCur, curAt_succ hi, ← ht, hcur, hfp]
  omega

theorem sum_dropLast_add (l : List ℕ) (hl : l ≠ []) : l.dropLast.sum + l.getLast hl = l.sum := by
  conv_rhs => rw [← List.dropLast_append_getLast hl]
  rw [List.sum_append, List.sum_singleton]

/-- **A loop's tail call ends where the iteration does.** -/
theorem endCur_tail {I J : Inst} (hl : lp I.t.name = true) (hk : I.t.kids ≠ [])
    (ht : J.t = I.t.kids.getLast hk) (hcur : J.cur = I.curAt fs lp I.t.bufs.length (I.t.kidsC lp).length)
    (hI : ∃ f σ bufs kids, I.t = .node f σ bufs kids) :
    J.endCur fs lp = I.endCur fs lp := by
  have hkc : I.t.kidsC lp = I.t.kids.dropLast := by unfold Tree.kidsC; rw [ite_eq_left hl]
  have hJ := block_le_total (fs := fs) (lp := lp) J.t
  have hsum := sum_dropLast_add (I.t.kids.map (Tree.total fs)) (by simpa using hk)
  rw [← List.map_dropLast, List.getLast_map, ← ht] at hsum
  have hbl : Tree.blockLast fs lp I.t.kids = J.t.block fs lp := by rw [ht]; exact blockLast_getLast _ hk
  rw [Inst.endCur, Inst.endCur, hcur, Inst.curAt, List.take_length, hkc, List.take_length, total_eq hI,
    block_loop hI hl, hbl]
  omega

/-- **An instance whose callees left are none ends at its cursor past everything**, a loop
iteration whose last callee is a phantom (`total = block`) included. -/
theorem endCur_ret {I : Inst} (hI : ∃ f σ bufs kids, I.t = .node f σ bufs kids)
    (hlast : lp I.t.name = true → ∀ hk : I.t.kids ≠ [], (I.t.kids.getLast hk).total fs =
      (I.t.kids.getLast hk).block fs lp) :
    I.endCur fs lp = I.curAt fs lp I.t.bufs.length (I.t.kidsC lp).length := by
  rw [Inst.endCur, Inst.curAt, List.take_length, List.take_length, total_eq hI]
  by_cases hl : lp I.t.name = true
  · have hkc : I.t.kidsC lp = I.t.kids.dropLast := by unfold Tree.kidsC; rw [ite_eq_left hl]
    rw [block_loop hI hl, hkc]
    by_cases hk : I.t.kids = []
    · rw [hk]; simp [Tree.blockLast]
    · have hsum := sum_dropLast_add (I.t.kids.map (Tree.total fs)) (by simpa using hk)
      rw [← List.map_dropLast, List.getLast_map, hlast hl hk] at hsum
      rw [blockLast_getLast _ hk]
      omega
  · have hkc : I.t.kidsC lp = I.t.kids := by unfold Tree.kidsC; rw [ite_eq_right hl]
    rw [block_not_loop hI hl, hkc]
    omega

/-- **The cursor stays within the subtree**: past at most every `HeapBuf` and callee, then a
callee's block reserved. -/
theorem curAt_le_endCur {I : Inst} (hI : ∃ f σ bufs kids, I.t = .node f σ bufs kids) (nb nc : ℕ) :
    I.curAt fs lp nb nc ≤ I.endCur fs lp := by
  obtain ⟨f, σ, bufs, kids, hIt⟩ := hI
  have htot := total_eq (fs := fs) ⟨f, σ, bufs, kids, hIt⟩
  have hb : (I.t.bufs.take nb).sum ≤ I.t.bufs.sum := List.Sublist.sum_le_sum (List.take_sublist _ _)
    (fun _ _ ↦ Nat.zero_le _)
  have hk : (((I.t.kidsC lp).take nc).map (Tree.total fs)).sum ≤ ((I.t.kidsC lp).map (Tree.total fs)).sum :=
    List.Sublist.sum_le_sum ((List.take_sublist _ _).map _) (fun _ _ ↦ Nat.zero_le _)
  have hblk : I.t.block fs lp + ((I.t.kidsC lp).map (Tree.total fs)).sum ≤
      fs I.t.name + (I.t.kids.map (Tree.total fs)).sum := by
    by_cases hl : lp I.t.name = true
    · have hkc : I.t.kidsC lp = I.t.kids.dropLast := by unfold Tree.kidsC; rw [ite_eq_left hl]
      rw [block_loop ⟨f, σ, bufs, kids, hIt⟩ hl, hkc]
      by_cases hk : I.t.kids = []
      · rw [hk]; simp [Tree.blockLast]
      · have hsum := sum_dropLast_add (I.t.kids.map (Tree.total fs)) (by simpa using hk)
        rw [← List.map_dropLast, List.getLast_map] at hsum
        have := block_le_total (fs := fs) (lp := lp) (I.t.kids.getLast hk)
        rw [blockLast_getLast _ hk]
        omega
    · have hkc : I.t.kidsC lp = I.t.kids := by unfold Tree.kidsC; rw [ite_eq_right hl]
      rw [block_not_loop ⟨f, σ, bufs, kids, hIt⟩ hl, hkc]
  have hbt := block_le_total (fs := fs) (lp := lp) I.t
  rw [Inst.endCur, Inst.curAt, htot]
  omega

/-- A reserved callee's block stays within the subtree. -/
theorem curAt_block_le {I : Inst} (hI : ∃ f σ bufs kids, I.t = .node f σ bufs kids) {nb nc : ℕ}
    (hnc : nc < (I.t.kidsC lp).length) :
    I.curAt fs lp nb nc + ((I.t.kidsC lp)[nc]).block fs lp ≤ I.endCur fs lp := by
  have h1 : I.curAt fs lp nb nc ≤ I.curAt fs lp I.t.bufs.length nc := by
    have : (I.t.bufs.take nb).sum ≤ (I.t.bufs.take I.t.bufs.length).sum := by
      rw [List.take_length]
      exact List.Sublist.sum_le_sum (List.take_sublist _ _) (fun _ _ ↦ Nat.zero_le _)
    simp only [Inst.curAt]; omega
  calc I.curAt fs lp nb nc + ((I.t.kidsC lp)[nc]).block fs lp
      ≤ I.curAt fs lp I.t.bufs.length nc + ((I.t.kidsC lp)[nc]).total fs :=
        Nat.add_le_add h1 (block_le_total _)
    _ = I.curAt fs lp I.t.bufs.length (nc + 1) := (curAt_succ hnc).symm
    _ ≤ I.endCur fs lp := curAt_le_endCur hI _ _

/-! ## The instances' positions -/

variable {H : Inst → ℕ → E × E}

theorem instsKids_kid_pos : ∀ (ks : List Tree) (ps : List (ℕ × ℕ)) (I : Inst) (j i : ℕ) {k : Tree}
    {p : ℕ × ℕ}, ks[i]? = some k → ps[i]? = some p →
    ∃ J ∈ Tree.instsKids fs lp H I j ps ks, J.t = k ∧ J.fp = p.1 ∧ J.cur = p.2
  | [], _, _, _, _, _, _, h, _ => by simp at h
  | _ :: _, [], _, _, _, _, _, _, h => by simp at h
  | k' :: ks, p' :: ps, I, j, 0, k, p, h, h' => by
      obtain rfl : k' = k := by simpa using h
      obtain rfl : p' = p := by simpa using h'
      obtain ⟨J, rest, he, ht, hfp, hcur, -⟩ := head_insts (fs := fs) (lp := lp) (H := H) k' p' (H I j)
      refine ⟨J, ?_, ht, hfp, hcur⟩
      rw [instsKids_cons, he]; exact List.mem_append_left _ List.mem_cons_self
  | k' :: ks, p' :: ps, I, j, i + 1, k, p, h, h' => by
      obtain ⟨J, hJ, h1⟩ := instsKids_kid_pos ks ps I (j + 1) i (by simpa using h) (by simpa using h')
      exact ⟨J, by rw [instsKids_cons]; exact List.mem_append_right _ hJ, h1⟩

mutual
/-- **Every callee instance at its position**: the `i`-th callee of an instance is an instance at
the `i`-th position `kidPos` gives, frame and cursor. -/
theorem insts_kid_pos : ∀ (t : Tree) (p : ℕ × ℕ) (hdr : E × E), ∀ I ∈ t.insts fs lp H p hdr,
    ∀ (i : ℕ) (k : Tree), I.t.kids[i]? = some k →
      ∃ J ∈ t.insts fs lp H p hdr, J.t = k ∧
        (kidPos fs lp (I.fp, I.cur) I.t.name I.t.bufs (I.t.kids.map (Tree.sz fs lp)))[i]? = some (J.fp, J.cur)
  | .node f σ bufs kids, p, hdr, I, hI, i, k, hk => by
      rw [insts_node, List.mem_cons] at hI
      rcases hI with rfl | hI
      · have hi : i < (kidPos fs lp p f bufs (kids.map (Tree.sz fs lp))).length := by
          rw [length_kidPos, List.length_map]
          exact (List.getElem?_eq_some_iff.mp hk).1
        obtain ⟨q, hq⟩ : ∃ q, (kidPos fs lp p f bufs (kids.map (Tree.sz fs lp)))[i]? = some q :=
          ⟨_, List.getElem?_eq_getElem hi⟩
        obtain ⟨J, hJ, ht, hfp, hcur⟩ := instsKids_kid_pos (fs := fs) (lp := lp) (H := H) kids _ _ 0 i hk hq
        refine ⟨J, ?_, ht, ?_⟩
        · rw [insts_node]; exact List.mem_cons_of_mem _ hJ
        · simp only [Tree.name, Tree.bufs, Tree.kids]; rw [hq, hfp, hcur]
      · obtain ⟨J, hJ, h⟩ := instsKids_kid_pos' kids _ _ 0 I hI i k hk
        refine ⟨J, ?_, h⟩
        rw [insts_node]; exact List.mem_cons_of_mem _ hJ
  | .phantom f σ, p, hdr, I, hI, i, k, hk => by
      rw [insts_phantom, List.mem_singleton] at hI
      subst hI
      simp [Tree.kids] at hk

/-- `insts_kid_pos` for the callees. -/
theorem instsKids_kid_pos' : ∀ (ks : List Tree) (ps : List (ℕ × ℕ)) (I : Inst) (j : ℕ),
    ∀ J ∈ Tree.instsKids fs lp H I j ps ks, ∀ (i : ℕ) (k : Tree), J.t.kids[i]? = some k →
      ∃ J' ∈ Tree.instsKids fs lp H I j ps ks, J'.t = k ∧
        (kidPos fs lp (J.fp, J.cur) J.t.name J.t.bufs (J.t.kids.map (Tree.sz fs lp)))[i]? = some (J'.fp, J'.cur)
  | [], _, _, _, J, hJ, _, _, _ => by rw [instsKids_nil] at hJ; exact (List.not_mem_nil hJ).elim
  | _ :: _, [], _, _, J, hJ, _, _, _ => by
      rw [instsKids_nil_left] at hJ; exact (List.not_mem_nil hJ).elim
  | k' :: ks, p :: ps, I, j, J, hJ, i, k, hk => by
      rw [instsKids_cons, List.mem_append] at hJ
      rw [instsKids_cons]
      rcases hJ with hJ | hJ
      · obtain ⟨J', hJ', h⟩ := insts_kid_pos k' _ _ J hJ i k hk
        exact ⟨J', List.mem_append_left _ hJ', h⟩
      · obtain ⟨J', hJ', h⟩ := instsKids_kid_pos' ks ps I (j + 1) J hJ i k hk
        exact ⟨J', List.mem_append_right _ hJ', h⟩
end

/-- **Two instances at one frame are one**, among instances pairwise apart, frames nonempty. -/
theorem inst_eq_of_fp {Is : List Inst} (hp : Is.Pairwise (Inst.Apart fs)) {I J : Inst} (hI : I ∈ Is)
    (hJ : J ∈ Is) (hfp : I.fp = J.fp) (h1 : 0 < fs I.t.name) (h2 : 0 < fs J.t.name) : I = J := by
  by_contra hne
  have hA : Inst.Apart fs I J :=
    List.Pairwise.forall hp hI hJ hne
  exact hA I.fp (Or.inl ⟨le_rfl, by omega⟩) (Or.inl ⟨by omega, by omega⟩)

end

end LeanVM.Guest.Memory
