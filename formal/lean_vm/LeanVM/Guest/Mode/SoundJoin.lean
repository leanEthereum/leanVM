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

/-- **A join is sound**: what both know holds where the first holds. -/
theorem Holds.inter {s : St} {A B : Abs} (hA : Holds s A) : Holds s (A.inter B) where
  w o ho := hA.w o (Exec.Trie.get_inter (fun _ _ _ ↦ rfl) ho).1
  v o x ho := hA.v o x (Exec.Trie.get_inter (fun _ _ h ↦ Val.beq_eq h) ho).1
  nz o ho := hA.nz o (Exec.Trie.get_inter (fun _ _ _ ↦ rfl) ho).1
  hv p hp := hA.hv p (mem_interL hp)
  h k hk := hA.h k (mem_interL hk)
  r r hr := hA.r r (mem_interL hr)
  lt p hp := hA.lt p (mem_interL hp)
  pr _ hp := nomatch hp

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
    exact ⟨vq, xlo, xhi, h1, hxlo, hxhi, fun j hj1 hj2 x hx ↦
      h4 j (by omega) (by omega) x (by rw [hS, hd]; exact hx)⟩
  · split at h
    · rename_i a b hlo hhi
      simp only [Bool.and_eq_true, decide_eq_true_eq] at h
      obtain ⟨⟨-, hbs⟩, hall⟩ := h
      obtain ⟨w, hw⟩ := BsVal.exists_fr hA hbs
      refine ⟨_, a, b, ⟨w, hw, rfl⟩, by rw [hlo]; rfl, by rw [hhi]; rfl, fun j hj1 hj2 x hx ↦ ?_⟩
      have hc := List.all_eq_true.mp hall (j - a) (List.mem_range.mpr (by omega))
      refine Abs.covered_sound hA hwf hu hc (MonoVal.shift ⟨w, hw, rfl⟩ _) ?_
      rw [show r.S * (a + (j - a)) + r.d = r.S * j + r.d by congr 2; omega]
      exact hx
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
