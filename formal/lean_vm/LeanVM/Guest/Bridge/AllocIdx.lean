/-
  LeanVM.Guest.Bridge.AllocIdx

  Where a hint at an offset sits among a function's hints: the hints before its offset, its own
  offset's, and after; its index among the buffer hints, and what `bufsFirst` says around it.
-/

module

public import LeanVM.Guest.Bridge.AllocCur

/-!
# A hint among the function's hints

For a function's advice `d` with pcs increasing from its entry (`HintsUp`), the hints of offset
`off`, `hs`, split the function's hints (`hintsOff_split`): those before (offsets below `off`), `hs`
at `off`, those after (offsets above). So the `i`-th of `hs`, a buffer hint, is the buffer hint of
index `nbAt off` plus the buffer hints before it in `hs` (`bufsOf_idx`). `bufsFirst` is a pairwise
order (`bufsFirst_pairwise`): at a buffer hint, no frame hint before it, so none pending or reserved
before it at its offset (`buf_noFrame`); at a frame hint, every buffer hint before it (`frame_allBufs`).
-/

namespace LeanVM.Guest.Bridge

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Memory

public section

variable {X : AlignCtx} {d : ℕ × ℕ × List (ℕ × List Prover.Exec.Hint)}

theorem lookup_key {β : Type} : ∀ {l : List (ℕ × β)} {k : ℕ} {v : β}, l.lookup k = some v → ∃ q ∈ l, q.1 = k
  | [], _, _, h => by simp at h
  | ⟨a, b⟩ :: l, k, v, h => by
    rw [List.lookup_cons] at h
    by_cases he : k = a
    · exact ⟨⟨a, b⟩, List.mem_cons_self, he.symm⟩
    · rw [show (k == a) = false by simp [he]] at h
      obtain ⟨q, hq, hq'⟩ := lookup_key h
      exact ⟨q, List.mem_cons_of_mem _ hq, hq'⟩

theorem split_aux (entry off : ℕ) {hs : List Prover.Exec.Hint} :
    ∀ (l : List (ℕ × List Prover.Exec.Hint)), pcsUp l = true → (∀ q ∈ l, entry ≤ q.1) →
      l.lookup (entry + off) = some hs →
      ∃ P S : List (ℕ × Prover.Exec.Hint), (l.flatMap fun q ↦ q.2.map fun h ↦ (q.1 - entry, h)) = P ++ hs.map (fun h ↦ (off, h)) ++ S ∧
        (∀ q ∈ P, q.1 < off) ∧ ∀ q ∈ S, off < q.1
  | [], _, _, hl => by simp at hl
  | ⟨a1, a2⟩ :: l, hu, hge, hl => by
    have ha := hge _ List.mem_cons_self
    simp only at ha
    rw [List.lookup_cons] at hl
    have hlt : ∀ q ∈ l, a1 < q.1 := pcsUp_lt hu
    by_cases he : entry + off = a1
    · rw [show (entry + off == a1) = true by simp [he]] at hl
      obtain rfl := Option.some.inj hl
      refine ⟨[], l.flatMap fun q ↦ q.2.map fun h ↦ (q.1 - entry, h), ?_, by simp, fun q hq ↦ ?_⟩
      · rw [List.flatMap_cons]
        simp [show a1 - entry = off by omega]
      · obtain ⟨q', hq', hq⟩ := List.mem_flatMap.mp hq
        obtain ⟨h, -, rfl⟩ := List.mem_map.mp hq
        have := hlt q' hq'
        simp only
        omega
    · rw [show (entry + off == a1) = false by simp; omega] at hl
      obtain ⟨P, S, he', hP, hS⟩ := split_aux entry off l (pcsUp_tail hu)
        (fun q hq ↦ hge q (List.mem_cons_of_mem _ hq)) hl
      obtain ⟨q0, hq0, hq0e⟩ := lookup_key hl
      have := hlt q0 hq0
      refine ⟨a2.map (fun h ↦ (a1 - entry, h)) ++ P, S, ?_, fun q hq ↦ ?_, hS⟩
      · rw [List.flatMap_cons, he']; simp
      · rcases List.mem_append.mp hq with hq | hq
        · obtain ⟨h, -, rfl⟩ := List.mem_map.mp hq
          simp only
          omega
        · exact hP q hq

/-- **A function's hints split at an offset**: those before it, its own, those after. -/
theorem hintsOff_split {entry off : ℕ} (hU : HintsUp d entry) {hs : List Prover.Exec.Hint}
    (hl : d.2.2.lookup (entry + off) = some hs) :
    ∃ P S : List (ℕ × Prover.Exec.Hint), hintsOff d = P ++ hs.map (fun h ↦ (off, h)) ++ S ∧ (∀ q ∈ P, q.1 < off) ∧ ∀ q ∈ S, off < q.1 := by
  obtain ⟨h1, h2, h3⟩ := hU
  unfold hintsOff
  rw [h1]
  exact split_aux entry off d.2.2 h2 h3 hl

theorem bufsOf_eq : bufsOf X d = (hintsOff d).filter fun q ↦ isBuf X q.2 := by
  unfold bufsOf allocHints
  rw [List.filter_filter]
  apply List.filter_congr
  intro q _
  cases hb : isBuf X q.2
  · simp
  · simp [isBuf_ptr hb]

/-- `bufsFirst` as a pairwise order: no buffer hint after a frame hint. -/
theorem bufsFirst_pairwise : ∀ (seen : Bool) (l : List (ℕ × Prover.Exec.Hint)), bufsFirst X seen l = true →
    l.Pairwise (fun a b ↦ isFrame X a.2 = true → isBuf X b.2 = false) ∧ (seen = true → ∀ b ∈ l, isBuf X b.2 = false)
  | _, [], _ => ⟨List.Pairwise.nil, fun _ _ h ↦ by simp at h⟩
  | seen, q :: qs, h => by
    simp only [bufsFirst, Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true'] at h
    obtain ⟨h1, h2⟩ := h
    obtain ⟨ih1, ih2⟩ := bufsFirst_pairwise _ qs h2
    refine ⟨List.Pairwise.cons (fun b hb hf ↦ ih2 (by simp [hf]) b hb) ih1, fun hs b hb ↦ ?_⟩
    rcases List.mem_cons.mp hb with rfl | hb
    · rcases h1 with h | h
      · rw [hs] at h; cases h
      · exact h
    · exact ih2 (by simp [hs]) b hb

theorem filter_take_idx {α : Type} (p : α → Bool) : ∀ (l : List α) (i : ℕ) {x : α}, l[i]? = some x → p x = true →
    (l.filter p)[(l.take i).countP p]? = some x
  | [], _, _, h, _ => by simp at h
  | a :: l, 0, x, h, hp => by
    simp only [List.getElem?_cons_zero, Option.some.injEq] at h
    subst h
    simp [hp]
  | a :: l, i + 1, x, h, hp => by
    simp only [List.getElem?_cons_succ] at h
    rw [List.take_succ_cons, List.countP_cons, List.filter_cons]
    have := filter_take_idx p l i h hp
    cases ha : p a
    · simpa using this
    · simpa using this

/-- **The buffer hint at index `i` of an offset's hints** is the buffer hint of index `nbAt` plus the
buffer hints before it there. -/
theorem bufsOf_idx {entry off : ℕ} (hU : HintsUp d entry) {i : ℕ} {h : Prover.Exec.Hint}
    (hi : (hintsAtD d entry off)[i]? = some h) (hb : isBuf X h = true) :
    (bufsOf X d)[nbAt X d off + ((hintsAtD d entry off).take i).countP (isBuf X)]? = some (off, h) := by
  have hl : d.2.2.lookup (entry + off) = some (hintsAtD d entry off) := by
    unfold hintsAtD at hi ⊢
    cases hlk : d.2.2.lookup (entry + off) with
    | none => rw [hlk] at hi; simp at hi
    | some _ => rfl
  obtain ⟨P, S, he, hP, hS⟩ := hintsOff_split hU hl
  set hs := hintsAtD d entry off
  have hnb : nbAt X d off = (P.filter fun q ↦ isBuf X q.2).length := by
    rw [nbAt_eq, bufsOf_eq, he, List.filter_append, List.filter_append, List.countP_append, List.countP_append]
    have h1 : (P.filter fun q ↦ isBuf X q.2).countP (fun q ↦ decide (q.1 < off)) = (P.filter fun q ↦ isBuf X q.2).length :=
      List.countP_eq_length.mpr fun q hq ↦ by simpa using hP q (List.mem_filter.mp hq).1
    have h2 : ((hs.map fun h ↦ (off, h)).filter fun q ↦ isBuf X q.2).countP (fun q ↦ decide (q.1 < off)) = 0 :=
      List.countP_eq_zero.mpr fun q hq ↦ by
        obtain ⟨h', -, rfl⟩ := List.mem_map.mp (List.mem_filter.mp hq).1
        simp
    have h3 : (S.filter fun q ↦ isBuf X q.2).countP (fun q ↦ decide (q.1 < off)) = 0 :=
      List.countP_eq_zero.mpr fun q hq ↦ by
        have := hS q (List.mem_filter.mp hq).1
        simp only [decide_eq_true_eq]
        omega
    rw [h1, h2, h3]; rfl
  rw [hnb, bufsOf_eq, he, List.filter_append, List.filter_append, List.append_assoc,
    List.getElem?_append_right (by omega), Nat.add_sub_cancel_left]
  have hmi : (hs.map fun h ↦ (off, h))[i]? = some (off, h) := by rw [List.getElem?_map, hi]; rfl
  have := filter_take_idx (fun q : ℕ × Prover.Exec.Hint ↦ isBuf X q.2) _ i hmi hb
  have hc : ((hs.map fun h ↦ (off, h)).take i).countP (fun q ↦ isBuf X q.2) = (hs.take i).countP (isBuf X) := by
    rw [← List.map_take, List.countP_map]; rfl
  rw [hc] at this
  rw [List.getElem?_append_left]
  · exact this
  · exact (List.getElem?_eq_some_iff.mp this).1

/-- The hints split at an offset, by the function's allocation hints. -/
theorem allocHints_split {entry off : ℕ} (hU : HintsUp d entry) {i : ℕ} {h : Prover.Exec.Hint}
    (hi : (hintsAtD d entry off)[i]? = some h) :
    ∃ P S : List (ℕ × Prover.Exec.Hint), allocHints d = (P.filter fun q ↦ (allocPtr q.2).isSome) ++
        (((hintsAtD d entry off).take i).map (fun h ↦ (off, h))).filter (fun q ↦ (allocPtr q.2).isSome) ++
        ([(off, h)].filter fun q ↦ (allocPtr q.2).isSome) ++
        (((hintsAtD d entry off).drop (i + 1)).map (fun h ↦ (off, h))).filter (fun q ↦ (allocPtr q.2).isSome) ++
        (S.filter fun q ↦ (allocPtr q.2).isSome) ∧
      (∀ q ∈ P, q.1 < off) ∧ ∀ q ∈ S, off < q.1 := by
  have hl : d.2.2.lookup (entry + off) = some (hintsAtD d entry off) := by
    unfold hintsAtD at hi ⊢
    cases hlk : d.2.2.lookup (entry + off) with
    | none => rw [hlk] at hi; simp at hi
    | some _ => rfl
  obtain ⟨P, S, he, hP, hS⟩ := hintsOff_split hU hl
  refine ⟨P, S, ?_, hP, hS⟩
  have hsplit : hintsAtD d entry off = (hintsAtD d entry off).take i ++ [h] ++ (hintsAtD d entry off).drop (i + 1) := by
    conv_lhs => rw [← List.take_append_drop i (hintsAtD d entry off)]
    rw [List.append_assoc, List.drop_eq_getElem_cons (List.getElem?_eq_some_iff.mp hi).1]
    simp [(List.getElem?_eq_some_iff.mp hi).2]
  unfold allocHints
  rw [he]
  conv_lhs => rw [hsplit]
  simp only [List.map_append, List.filter_append, List.map_cons, List.map_nil, List.append_assoc]

theorem pw_cross {α : Type} {R : α → α → Prop} {l1 l2 : List α} (h : (l1 ++ l2).Pairwise R) :
    ∀ a ∈ l1, ∀ b ∈ l2, R a b := (List.pairwise_append.mp h).2.2

theorem countP_offs (p : Prover.Exec.Hint → Bool) {off : ℕ} (l : List Prover.Exec.Hint) :
    ((l.map fun h ↦ (off, h)).filter fun q ↦ (allocPtr q.2).isSome).countP (fun q ↦ p q.2) =
      l.countP (fun h ↦ (allocPtr h).isSome && p h) := by
  rw [List.countP_filter, List.countP_map]
  apply List.countP_congr
  intro x _
  simp [Function.comp, Bool.and_comm]

/-- **At a buffer hint, no frame hint before it**: none at an offset below its own, none before it
at its own. -/
theorem buf_noFrame {entry off : ℕ} (hU : HintsUp d entry) (hF : bufsFirst X false (allocHints d) = true) {i : ℕ}
    {h : Prover.Exec.Hint} (hi : (hintsAtD d entry off)[i]? = some h) (hb : isBuf X h = true) :
    (∀ q ∈ frames X d, off ≤ q.1) ∧ ((hintsAtD d entry off).take i).countP (isFrame X) = 0 := by
  obtain ⟨P, S, he, hP, hS⟩ := allocHints_split hU hi
  set Pf := P.filter fun q ↦ (allocPtr q.2).isSome
  set Tf := (((hintsAtD d entry off).take i).map (fun h ↦ (off, h))).filter (fun q ↦ (allocPtr q.2).isSome)
  set Hf := [(off, h)].filter fun q ↦ (allocPtr q.2).isSome
  set Df := (((hintsAtD d entry off).drop (i + 1)).map (fun h ↦ (off, h))).filter (fun q ↦ (allocPtr q.2).isSome)
  set Sf := S.filter fun q ↦ (allocPtr q.2).isSome
  have hpw := (bufsFirst_pairwise false _ hF).1
  rw [he] at hpw
  have h1 : ((Pf ++ Tf) ++ (Hf ++ Df ++ Sf)).Pairwise (fun a b ↦ isFrame X a.2 = true → isBuf X b.2 = false) := by
    simpa only [List.append_assoc] using hpw
  have hh : (off, h) ∈ Hf ++ Df ++ Sf :=
    List.mem_append_left _ (List.mem_append_left _ (by simp [Hf, isBuf_ptr hb]))
  refine ⟨fun q hq ↦ ?_, ?_⟩
  · unfold frames at hq
    have hf := (List.mem_filter.mp hq).2
    rw [he] at hq
    have hq' := (List.mem_filter.mp hq).1
    simp only [List.mem_append] at hq'
    rcases hq' with (((hq' | hq') | hq') | hq') | hq'
    · exfalso
      have := pw_cross h1 q (List.mem_append_left _ hq') (off, h) hh hf
      rw [hb] at this; cases this
    · obtain ⟨_, -, rfl⟩ := List.mem_map.mp (List.mem_filter.mp hq').1; exact le_rfl
    · have : q = (off, h) := by simpa [Hf] using (List.mem_filter.mp hq').1
      rw [this]
    · obtain ⟨_, -, rfl⟩ := List.mem_map.mp (List.mem_filter.mp hq').1; exact le_rfl
    · exact (hS q (List.mem_filter.mp hq').1).le
  · rw [List.countP_eq_zero]
    intro x hx hf
    have hm : (off, x) ∈ Tf := List.mem_filter.mpr ⟨List.mem_map.mpr ⟨x, hx, rfl⟩, isFrame_ptr hf⟩
    have := pw_cross h1 (off, x) (List.mem_append_right _ hm) (off, h) hh hf
    rw [hb] at this; cases this

/-- **At a frame hint, every buffer hint before it**: those at offsets below its own and those
before it at its own. -/
theorem frame_allBufs {entry off : ℕ} (hU : HintsUp d entry) (hF : bufsFirst X false (allocHints d) = true) {i : ℕ}
    {h : Prover.Exec.Hint} (hi : (hintsAtD d entry off)[i]? = some h) (hf : isFrame X h = true) :
    nbAt X d off + ((hintsAtD d entry off).take i).countP (isBuf X) = (bufsOf X d).length := by
  obtain ⟨P, S, he, hP, hS⟩ := allocHints_split hU hi
  set Pf := P.filter fun q ↦ (allocPtr q.2).isSome
  set Tf := (((hintsAtD d entry off).take i).map (fun h ↦ (off, h))).filter (fun q ↦ (allocPtr q.2).isSome)
  set Hf := [(off, h)].filter fun q ↦ (allocPtr q.2).isSome
  set Df := (((hintsAtD d entry off).drop (i + 1)).map (fun h ↦ (off, h))).filter (fun q ↦ (allocPtr q.2).isSome)
  set Sf := S.filter fun q ↦ (allocPtr q.2).isSome
  have hpw := (bufsFirst_pairwise false _ hF).1
  rw [he] at hpw
  have h2 : ((Pf ++ Tf ++ Hf) ++ (Df ++ Sf)).Pairwise (fun a b ↦ isFrame X a.2 = true → isBuf X b.2 = false) := by
    simpa only [List.append_assoc] using hpw
  have hh : (off, h) ∈ Pf ++ Tf ++ Hf := List.mem_append_right _ (by simp [Hf, isFrame_ptr hf])
  have hnb : ∀ q ∈ Df ++ Sf, isBuf X q.2 = false := fun q hq ↦ pw_cross h2 (off, h) hh q hq hf
  have hlen : (bufsOf X d).length = (allocHints d).countP (fun q ↦ isBuf X q.2) := by
    unfold bufsOf; rw [List.countP_eq_length_filter]
  have hnbAt : nbAt X d off = (allocHints d).countP (fun q ↦ decide (q.1 < off) && isBuf X q.2) := by
    unfold nbAt; rw [List.countP_eq_length_filter]
  have hP' : Pf.countP (fun q ↦ decide (q.1 < off) && isBuf X q.2) = Pf.countP (fun q ↦ isBuf X q.2) :=
    List.countP_congr fun q hq ↦ by simp [hP q (List.mem_filter.mp hq).1]
  have hz : ∀ L : List (ℕ × Prover.Exec.Hint), (∀ q ∈ L, off ≤ q.1) →
      L.countP (fun q ↦ decide (q.1 < off) && isBuf X q.2) = 0 :=
    fun L hL ↦ List.countP_eq_zero.mpr fun q hq ↦ by have := hL q hq; simp; omega
  have hTo : ∀ q ∈ Tf, off ≤ q.1 := fun q hq ↦ by
    obtain ⟨_, -, rfl⟩ := List.mem_map.mp (List.mem_filter.mp hq).1; exact le_rfl
  have hHo : ∀ q ∈ Hf, off ≤ q.1 := fun q hq ↦ by
    have : q = (off, h) := by simpa [Hf] using (List.mem_filter.mp hq).1
    rw [this]
  have hDo : ∀ q ∈ Df, off ≤ q.1 := fun q hq ↦ by
    obtain ⟨_, -, rfl⟩ := List.mem_map.mp (List.mem_filter.mp hq).1; exact le_rfl
  have hSo : ∀ q ∈ Sf, off ≤ q.1 := fun q hq ↦ (hS q (List.mem_filter.mp hq).1).le
  have hT : Tf.countP (fun q ↦ isBuf X q.2) = ((hintsAtD d entry off).take i).countP (isBuf X) := by
    rw [countP_offs]
    apply List.countP_congr
    intro x _
    cases hb : isBuf X x
    · simp
    · simp [isBuf_ptr hb]
  have hH : Hf.countP (fun q ↦ isBuf X q.2) = 0 := by
    have : isBuf X h = false := by unfold isBuf; simp [hf]
    simp [Hf, this]
  have hD : Df.countP (fun q ↦ isBuf X q.2) = 0 :=
    List.countP_eq_zero.mpr fun q hq hb ↦ by rw [hnb q (List.mem_append_left _ hq)] at hb; cases hb
  have hS0 : Sf.countP (fun q ↦ isBuf X q.2) = 0 :=
    List.countP_eq_zero.mpr fun q hq hb ↦ by rw [hnb q (List.mem_append_right _ hq)] at hb; cases hb
  rw [hlen, hnbAt, he]
  simp only [List.countP_append]
  rw [hP', hz _ hTo, hz _ hHo, hz _ hDo, hz _ hSo, hT, hH, hD, hS0]
  omega

end

end LeanVM.Guest.Bridge
