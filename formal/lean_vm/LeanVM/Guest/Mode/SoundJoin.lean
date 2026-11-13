module

public import LeanVM.Guest.Mode.SoundHint

/-!
# Joins, hint lists and residuals

`Holds.inter`: what two states both know holds where either holds. `stepHints_sound`: a pc's
hints, in order. `addRes_sound`: the residuals the walk assumes, given that they hold (`ResHolds`:
a value fact about the cells, which the reference's agreement with the memory gives from a fact
about the reference).
-/

namespace LeanVM.Guest.Mode

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest
open LeanVM.Prover.Exec

@[expose] public section

theorem Val.beq_eq {a b : Val} (h : a.beq b = true) : a = b := by
  cases a <;> cases b <;> simp only [Val.beq, Bool.and_eq_true, beq_iff_eq] at h <;>
    first
    | (rw [Mono.beq_eq h])
    | (obtain ⟨rfl, rfl⟩ := h; rfl)
    | (rw [Base.beq_eq h.1, h.2])
    | exact absurd h (by simp)

theorem Idx.beq_eq {a b : Idx} (h : a.beq b = true) : a = b := by
  cases a <;> cases b <;> simp only [Idx.beq, Bool.and_eq_true, beq_iff_eq] at h
  · rw [h]
  · simp at h
  · simp at h
  · rw [Base.beq_eq h.1, h.2]

theorem Rng.beq_eq {a b : Rng} (h : a.beq b = true) : a = b := by
  obtain ⟨q, lo, hi, S, d⟩ := a
  obtain ⟨q', lo', hi', S', d'⟩ := b
  simp only [Rng.beq, Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ := h
  rw [Mono.beq_eq h1, Idx.beq_eq h2, Idx.beq_eq h3, h4, h5]

theorem mem_interL {α : Type} {eq : α → α → Bool} {a b : List α} {x : α} (h : x ∈ interL eq a b) :
    x ∈ a :=
  (List.mem_filter.mp h).1

theorem mem_interT {α : Type} {eq : α → α → Bool} {a b : List α} {x : α} (h : x ∈ interT eq a b) :
    x ∈ a := by
  unfold interT at h
  rcases List.mem_append.mp h with h | h
  · exact List.mem_of_mem_take (mem_interL h)
  · exact List.mem_of_mem_drop h

theorem agree_forall₂ {α : Type} {eq : α → α → Bool} : ∀ {a b : List α},
    List.Forall₂ (fun x y ↦ eq x y = true) (a.take (agree eq a b)) (b.take (agree eq a b))
  | [], _ => by simp [agree]
  | _ :: _, [] => by simp [agree]
  | x :: xs, y :: ys => by
    unfold agree
    split_ifs with he
    · simp only [List.take_succ_cons]
      exact List.Forall₂.cons he agree_forall₂
    · simp

/-- **A join is sound**: what both know holds where the first holds. -/
theorem Holds.inter {s : St} {A B : Abs} (hA : Holds s A) : Holds s (A.inter B) where
  w o ho := hA.w o (Exec.Trie.get_inter (fun _ _ _ ↦ rfl) ho).1
  v o x ho := hA.v o x (Exec.Trie.get_inter (fun _ _ h ↦ Val.beq_eq h) ho).1
  nz o ho := hA.nz o (Exec.Trie.get_inter (fun _ _ _ ↦ rfl) ho).1
  hv p hp := hA.hv p (mem_interT hp)
  h k hk := hA.h k (mem_interT hk)
  r r hr := hA.r r (mem_interT hr)
  lt p hp := hA.lt p (mem_interT hp)
  pr _ hp := nomatch hp
  xs c a b ho := hA.xs c a b (Exec.Trie.get_inter (fun p q h ↦ by
    simp only [Bool.and_eq_true, beq_iff_eq] at h; exact Prod.ext h.1 h.2) ho).1
  p q hq := hA.p q (mem_interT hq)

theorem mem_interL_right {α : Type} {eq : α → α → Bool} (heq : ∀ x y, eq x y = true → x = y)
    {a b : List α} {x : α} (h : x ∈ interL eq a b) : x ∈ b := by
  obtain ⟨y, hy, he⟩ := List.any_eq_true.mp (List.mem_filter.mp h).2
  rwa [heq x y he]

theorem forall₂_mem {α : Type} {R : α → α → Prop} : ∀ {l₁ l₂ : List α}, List.Forall₂ R l₁ l₂ →
    ∀ {x}, x ∈ l₁ → ∃ y ∈ l₂, R x y
  | _, _, .nil, _, h => by cases h
  | _, _, .cons hr ht, x, h => by
    rcases List.mem_cons.mp h with rfl | h
    · exact ⟨_, List.mem_cons_self .., hr⟩
    · obtain ⟨y, hy, hxy⟩ := forall₂_mem ht h
      exact ⟨y, List.mem_cons_of_mem _ hy, hxy⟩

theorem mem_interT_right {α : Type} {eq : α → α → Bool} (heq : ∀ x y, eq x y = true → x = y)
    {a b : List α} {x : α} (h : x ∈ interT eq a b) : x ∈ b := by
  unfold interT at h
  rcases List.mem_append.mp h with h | h
  · exact mem_interL_right heq h
  · have hx : x ∈ a.reverse.take (agree eq a.reverse b.reverse) := by
      rw [List.take_reverse]; exact List.mem_reverse.mpr h
    obtain ⟨y, hy, he⟩ := forall₂_mem agree_forall₂ hx
    rw [heq _ _ he]
    exact List.mem_reverse.mp (List.mem_of_mem_take hy)

theorem pair_beq_eq {α β : Type} {ea : α → α → Bool} {eb : β → β → Bool}
    (ha : ∀ x y, ea x y = true → x = y) (hb : ∀ x y, eb x y = true → x = y) (p q : α × β)
    (h : (ea p.1 q.1 && eb p.2 q.2) = true) : p = q := by
  simp only [Bool.and_eq_true] at h
  exact Prod.ext (ha _ _ h.1) (hb _ _ h.2)

/-- **A join is sound**, from its second side. -/
theorem Holds.inter_right {s : St} {A B : Abs} (hB : Holds s B) : Holds s (A.inter B) where
  w o ho := hB.w o (Exec.Trie.get_inter (fun _ _ _ ↦ rfl) ho).2
  v o x ho := hB.v o x (Exec.Trie.get_inter (fun _ _ h ↦ Val.beq_eq h) ho).2
  nz o ho := hB.nz o (Exec.Trie.get_inter (fun _ _ _ ↦ rfl) ho).2
  hv p hp := hB.hv p (mem_interT_right
    (pair_beq_eq (fun _ _ h ↦ Mono.beq_eq h) (fun _ _ h ↦ Val.beq_eq h)) hp)
  h k hk := hB.h k (mem_interT_right (fun _ _ h ↦ Mono.beq_eq h) hk)
  r r hr := hB.r r (mem_interT_right (fun _ _ h ↦ Rng.beq_eq h) hr)
  lt p hp := hB.lt p (mem_interT_right
    (pair_beq_eq (fun _ _ h ↦ Idx.beq_eq h) (fun _ _ h ↦ Idx.beq_eq h)) hp)
  pr _ hp := nomatch hp
  xs c a b ho := hB.xs c a b (Exec.Trie.get_inter (fun p q h ↦ by
    simp only [Bool.and_eq_true, beq_iff_eq] at h; exact Prod.ext h.1 h.2) ho).2
  p q hq := hB.p q (mem_interT_right
    (pair_beq_eq (fun _ _ h ↦ Rng.beq_eq h) (fun _ _ h ↦ beq_iff_eq.mp h)) hq)

/-- Paths met: what all know holds where any holds. -/
theorem Holds.foldl_inter {s : St} : ∀ {A X : Abs} {l : List Abs}, X ∈ A :: l → Holds s X →
    Holds s (l.foldl Abs.inter A)
  | _, _, [], hm, hX => by rw [List.mem_singleton.mp hm] at hX; exact hX
  | A, X, B :: l, hm, hX => by
    rw [List.foldl_cons]
    rcases List.mem_cons.mp hm with rfl | hm
    · exact Holds.foldl_inter (List.mem_cons_self ..) hX.inter
    rcases List.mem_cons.mp hm with rfl | hm
    · exact Holds.foldl_inter (List.mem_cons_self ..) hX.inter_right
    · exact Holds.foldl_inter (List.mem_cons_of_mem _ hm) hX

/-- **Capping the paths is sound**: a path that holds leaves one that holds. -/
theorem Holds.cap {s : St} {As : List Abs} (h : ∃ A ∈ As, Holds s A) : ∃ A ∈ cap As, Holds s A := by
  obtain ⟨X, hm, hX⟩ := h
  match As, hm with
  | [_], hm => exact ⟨X, hm, hX⟩
  | [_, _], hm => exact ⟨X, hm, hX⟩
  | A :: B :: C :: Ds, hm => exact ⟨_, List.mem_singleton_self _, Holds.foldl_inter hm hX⟩

/-- **Meeting paths is sound**: a path that holds leaves one that holds. -/
theorem Holds.meetAll {s : St} {As : List Abs} (h : ∃ A ∈ As, Holds s A) :
    ∃ A ∈ meetAll As, Holds s A := by
  obtain ⟨X, hm, hX⟩ := h
  match As, hm with
  | A :: Bs, hm =>
    refine ⟨_, List.mem_singleton_self _, ?_⟩
    have e : Mode.foldlA Abs.interS A Bs = Bs.foldl Abs.inter A := by
      rw [foldlA_eq]
      exact congrArg (fun f ↦ Bs.foldl f A) (funext fun A ↦ funext fun B ↦ Abs.interS_eq A B)
    rw [e]
    exact Holds.foldl_inter hm hX

theorem mem_of_any_beq {α : Type} {eq : α → α → Bool} (heq : ∀ x y, eq x y = true → x = y) {l : List α}
    {x : α} (h : (l.any fun y ↦ eq x y) = true) : x ∈ l := by
  obtain ⟨y, hy, he⟩ := List.any_eq_true.mp h
  rwa [heq x y he]

/-- **A cut is sound**: a state weaker than one that holds holds. -/
theorem Holds.sub {s : St} {S A : Abs} (hA : Holds s A) (h : S.sub A = true) : Holds s S := by
  unfold Abs.sub at h
  simp only [Bool.and_eq_true, List.all_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨hw, hv⟩, hnz⟩, hhv⟩, hh⟩, hr⟩, hlt⟩, hpr⟩, hxs⟩, hp⟩ := h
  exact {
    w := fun o ho ↦ hA.w o (Exec.Trie.get_of_sub (fun _ _ _ ↦ rfl) hw ho)
    v := fun o x ho ↦ hA.v o x (Exec.Trie.get_of_sub (fun _ _ h ↦ Val.beq_eq h) hv ho)
    nz := fun o ho ↦ hA.nz o (Exec.Trie.get_of_sub (fun _ _ _ ↦ rfl) hnz ho)
    hv := fun p hp ↦ hA.hv p (mem_of_any_beq
      (pair_beq_eq (fun _ _ h ↦ Mono.beq_eq h) (fun _ _ h ↦ Val.beq_eq h)) (hhv p hp))
    h := fun k hk ↦ hA.h k (mem_of_any_beq (eq := fun x y ↦ y.beq x)
      (fun _ _ h ↦ (Mono.beq_eq h).symm) (hh k hk))
    r := fun r hr' ↦ hA.r r (mem_of_any_beq (eq := fun x y ↦ y.beq x)
      (fun _ _ h ↦ (Rng.beq_eq h).symm) (hr r hr'))
    lt := fun p hp ↦ hA.lt p (mem_of_any_beq
      (pair_beq_eq (fun _ _ h ↦ Idx.beq_eq h) (fun _ _ h ↦ Idx.beq_eq h)) (hlt p hp))
    pr := fun p hp ↦ hA.pr p (mem_of_any_beq
      (eq := fun p q ↦ p.1 == q.1 && p.2.1 == q.2.1 && p.2.2 == q.2.2) (fun x y h ↦ by
      simp only [Bool.and_eq_true, beq_iff_eq] at h
      exact Prod.ext h.1.1 (Prod.ext h.1.2 h.2)) (hpr p hp))
    xs := fun c a b ho ↦ hA.xs c a b (Exec.Trie.get_of_sub (fun p q h ↦ by
      simp only [Bool.and_eq_true, beq_iff_eq] at h; exact Prod.ext h.1 h.2) hxs ho)
    p := fun q hq ↦ hA.p q (mem_of_any_beq
      (pair_beq_eq (fun _ _ h ↦ Rng.beq_eq h) (fun _ _ h ↦ beq_iff_eq.mp h)) (hp q hq)) }

/-- **The fall-through of a `JUMP` on `[c]`** is sound, `[c]` being `0`. -/
theorem Holds.learn0 {s : St} {A : Abs} (hA : Holds s A) {c : ℕ}
    (hc : s.mem.get (s.fp + c) = some 0) : Holds s (A.learn0 c) := by
  unfold Abs.learn0
  split
  · rename_i a b hab
    obtain ⟨va, vb, ha, hb, hc'⟩ := hA.xs c a b hab
    rw [hc] at hc'
    obtain rfl : va = vb := by
      rw [← sub_eq_zero, CharTwo.sub_eq_add]; exact (Option.some.inj hc').symm
    have key : ∀ o, s.mem.get (s.fp + o) = some va →
        ValOk s ((A.v.get o).getD (.m (.root o))) va := by
      intro o ho
      cases hvo : A.v.get o with
      | none => exact MonoVal.root ho
      | some y =>
        obtain ⟨u, hu, hok⟩ := hA.v o y hvo
        rw [ho] at hu; cases hu; exact hok
    split
    · exact hA.addV ⟨va, hb, key a ha⟩
    · exact hA.addV ⟨va, ha, key b hb⟩
  · exact hA

/-- The hints at a pc, in order: each reads written cells, and the state after them holds the
walk's set. -/
theorem stepHints_sound {C : Ctx} :
    ∀ {s : St} {A A' : Abs} {hs : List Hint}, s.Good → s.fp < maxCells → s.mem.used ≤ maxCells →
      Holds s A → stepHints A hs = some A' →
      ∀ {s'}, hs.foldlM (runHint C) s = .ok s' → (∀ s1, St.Follows s s1 → s1.mem.used ≤ maxCells) →
        Holds s' A'
  | s, A, A', [], _, _, _, hH, h, s', e, _ => by
    cases h; cases e; exact hH
  | s, A, A', x :: xs, hgood, hfp, hu, hH, h, s', e, hU => by
    simp only [stepHints, Option.bind_eq_some_iff] at h
    obtain ⟨B, hB, h⟩ := h
    rw [List.foldlM_cons, bind_ok] at e
    obtain ⟨s1, e1, e⟩ := e
    have f1 := runHint_follows hgood e1
    have hu1 := hU s1 f1
    have hH1 := (stepHint_sound hgood hfp hu hH hB).2 e1 hu1
    exact stepHints_sound f1.good (by rw [f1.fp]; exact hfp) hu1 hH1 h e
      fun s2 f2 ↦ hU s2 (f1.trans f2)

/-- What a residual states, of the memory. -/
def ResHolds (s : St) : Res → Prop
  | .lt a b => LTF s a b
  | .nz o => NzAt s o

/-- **The residuals**, holding, keep the walk's set. -/
theorem addRes_sound {s : St} :
    ∀ {A A' : Abs} {rs : List Res}, Holds s A → (∀ r ∈ rs, ResHolds s r) → addRes A rs = some A' →
      Holds s A'
  | _, _, [], hH, _, h => by cases h; exact hH
  | A, A', .lt a b :: rs, hH, hr, h => by
    simp only [addRes] at h
    split_ifs at h
    exact addRes_sound (hH.addLt (hr _ (List.mem_cons_self ..))) (fun r hm ↦ hr r (List.mem_cons_of_mem _ hm)) h
  | A, A', .nz o :: rs, hH, hr, h => by
    simp only [addRes] at h
    split_ifs at h
    exact addRes_sound (hH.addNz (hr _ (List.mem_cons_self ..)))
      (fun r hm ↦ hr r (List.mem_cons_of_mem _ hm)) h

theorem Abs.hasIdx_sound {s : St} {A : Abs} (hA : Holds s A) {i : Idx} (h : A.hasIdx i = true) :
    ∃ x, IdxVal s i x := by
  cases i with
  | num n => exact ⟨n, rfl⟩
  | ex b c =>
    simp only [Abs.hasIdx] at h
    obtain ⟨⟨p, q⟩, hm, hh⟩ := List.any_eq_true.mp h
    obtain ⟨xp, xq, hp, hq, -⟩ := hA.lt _ hm
    have key : ∀ i : Idx, (match i.base? with | some x => x.beq b | none => false) = true →
        ∀ x, IdxVal s i x → ∃ x, IdxVal s (.ex b c) x := by
      intro i hi x hx
      cases i with
      | num => simp [Idx.base?] at hi
      | ex b' c' =>
        simp only [Idx.base?] at hi
        obtain rfl := Base.beq_eq hi
        obtain ⟨v, e, h1, h2, h3, -⟩ := hx
        exact ⟨e + c, v, e, h1, h2, h3, rfl⟩
    rcases Bool.or_eq_true_iff.mp hh with hh | hh
    · exact key p hh xp hp
    · exact key q hh xq hq

theorem BsVal.exists_fr {s : St} {A : Abs} (hA : Holds s A) :
    ∀ {bs : List (Base × ℕ)}, (bs.all fun p ↦ match p.1 with
      | .fr o => A.hasW o
      | .hp _ _ => false) = true → ∃ w, BsVal s bs w
  | [], _ => ⟨1, rfl⟩
  | (b, e) :: bs, h => by
    simp only [List.all_cons, Bool.and_eq_true] at h
    obtain ⟨w, hw⟩ := BsVal.exists_fr hA h.2
    cases b with
    | fr o =>
      obtain ⟨u, hu⟩ := Mem.get_of_written (hA.written h.1)
      exact ⟨u ^ e * w, u, w, hu, hw, rfl⟩
    | hp => simp at h

/-- **A run the walk knows written is.** -/
theorem Abs.coveredR_sound {s : St} {A : Abs} (hA : Holds s A) (hwf : s.mem.WF)
    (hu : s.mem.used ≤ maxCells) {r : Rng} (h : A.coveredR r = true) : RW s r := by
  unfold Abs.coveredR at h
  rcases Bool.or_eq_true_iff.mp h with h | h
  · obtain ⟨r', hm, hh⟩ := List.any_eq_true.mp h
    simp only [Bool.and_eq_true, beq_iff_eq] at hh
    obtain ⟨⟨⟨⟨⟨⟨hq, hS⟩, hd⟩, hlo⟩, hhi⟩, hklo⟩, hkhi⟩ := hh
    obtain ⟨vq, xlo', xhi', h1, h2, h3, h4⟩ := hA.r r' hm
    obtain ⟨xlo, hxlo⟩ := Abs.hasIdx_sound hA hklo
    obtain ⟨xhi, hxhi⟩ := Abs.hasIdx_sound hA hkhi
    obtain ⟨y, hy, hyle⟩ := Abs.le_sound hA hlo hxlo
    have hy' := hy.unique h2
    obtain ⟨z, hz, hzle⟩ := Abs.le_sound hA hhi h3
    have hz' := hz.unique hxhi
    rw [Mono.beq_eq hq] at h1
    exact ⟨vq, xlo, xhi, h1, hxlo, hxhi, fun j hj1 hj2 ↦ by
      rw [← hS, ← hd]; exact h4 j (by omega) (by omega)⟩
  · split at h
    · rename_i a b hlo hhi
      simp only [Bool.and_eq_true, decide_eq_true_eq] at h
      obtain ⟨⟨-, hbs⟩, hall⟩ := h
      obtain ⟨w, hw⟩ := BsVal.exists_fr hA hbs
      refine ⟨_, a, b, ⟨w, hw, rfl⟩, by rw [hlo]; rfl, by rw [hhi]; rfl, fun j hj1 hj2 ↦ ?_⟩
      have hc := List.all_eq_true.mp hall (j - a) (List.mem_range.mpr (by omega))
      have := Abs.covered_ex hA hwf hu hc (MonoVal.shift ⟨w, hw, rfl⟩ _)
      rwa [show r.S * (a + (j - a)) + r.d = r.S * j + r.d by congr 2; omega] at this
    · simp at h

/-- **One instruction the walk accepts**: its reads are written (`Reads`), and, unless it is a
`JUMP`, the walk's next set holds after it. -/
theorem stepOp_sound {En : Env} {C : Ctx} {s s' : St} {A A' : Abs} {ins : OffsetInstruction}
    (hs : s.Good) (hfp : s.fp < maxCells) (hpc : s.pc < C.ops.size) (hu : s.mem.used ≤ maxCells)
    (hE : EnvOk s En) (hH : Holds s A) (h : stepOp En s.pc A ins = some A') :
    Reads s (opOfOff ins) ∧
      ((∀ c d f, ins ≠ .jump c d f) → runOp C s (opOfOff ins) = .ok s' → Holds s' A') := by
  cases ins with
  | deref a o c mode =>
    obtain ⟨h1, h2⟩ := stepOp_sound_deref hs hfp hpc hu hE hH h
    exact ⟨h1, fun _ e ↦ h2 e⟩
  | jump c d f =>
    simp only [stepOp, Bool.and_eq_true] at h
    split_ifs at h with hc
    exact ⟨⟨hH.written hc.1.1, hH.written hc.1.2, hH.written hc.2⟩, fun hj ↦ absurd rfl (hj c d f)⟩
  | xor | mul | set | keccak =>
    obtain ⟨h1, h2⟩ := stepOp_sound_nj (s' := s') hs hfp hpc hE hH h (fun _ _ _ _ ↦ nofun)
      (fun _ _ _ ↦ nofun)
    exact ⟨h1, fun _ ↦ h2⟩

end

end LeanVM.Guest.Mode
