/-
  LeanVM.Guest.Backend.Complete.FrameFa

  No value a statement of a scoped body reads is the value of a later frame address.
-/

module

public import LeanVM.Guest.Backend.Complete.FrameAssemble

/-!
# Frame addresses after a statement

A value a statement reads is in scope at its start or made by an event its scope walk passes
(`scopeStmt_uses`). A frame address after it is of a value not in scope at its start
(`scopeBlock_fa`, from `badAddr`) and made by an event after it (`scopeBlock_made`); the trace makes
each value once (`scoped_allocs`). So `FaAfter` holds at every block of a scoped body
(`faAfter_scoped`, `faBody`), and its analogue for the arms of a `match` (`faArms_scoped`).
-/

namespace LeanVM.Guest.Backend.Complete

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Memory

@[expose] public section

/-! ## Values in scope or made -/

section Fa

theorem flushAt_made {rc : ℕ} {s s₀ : SSt} (h : flushAt rc s = .ok s₀) {v : V}
    (hv : s₀.live.contains v = true) :
    s.live.contains v = true ∨ ∃ pre, s.rest = pre ++ s₀.rest ∧ v ∈ allocsOf pre := by
  obtain ⟨hseg, hlive, -⟩ := flushS_seg rc s.rest s.live s.retDone s₀ h
  exact (hlive v hv).imp_right fun hm => ⟨_, hseg, hm⟩

theorem made_suf {v : V} {a b c : List Event} {live : VMap Unit}
    (h : live.contains v = true ∨ ∃ pre, a = pre ++ b ∧ v ∈ allocsOf pre) (hs : ∃ q, b = q ++ c) :
    live.contains v = true ∨ ∃ pre, a = pre ++ c ∧ v ∈ allocsOf pre :=
  h.imp_right fun hm => made_trans ⟨[], rfl⟩ hm hs

theorem made_twice {v : V} {a b c : List Event} (hnd : (allocsOf a).Nodup)
    (h₁ : ∃ pre, a = pre ++ b ∧ v ∈ allocsOf pre) (h₂ : ∃ pre, b = pre ++ c ∧ v ∈ allocsOf pre) :
    False := by
  obtain ⟨pre, rfl, hp⟩ := h₁
  obtain ⟨pre₂, rfl, hp₂⟩ := h₂
  rw [allocsOf_append, allocsOf_append] at hnd
  exact List.disjoint_of_nodup_append hnd hp (List.mem_append_left _ hp₂)

theorem nodup_suf {a b : List Event} (hnd : (allocsOf a).Nodup) (h : ∃ q, a = q ++ b) :
    (allocsOf b).Nodup := by
  obtain ⟨q, rfl⟩ := h
  rw [allocsOf_append] at hnd
  exact hnd.sublist (List.sublist_append_right _ _)

theorem scopeMatch_inv' {rc : ℕ} {x : V} {arms : List (List Stmt)} {s s' : SSt}
    (h : scopeStmt rc (.match_ x arms) s = .ok s') : ∃ s₀ s₁, flushEdge rc s = .ok s₀ ∧
      s₀.live.contains x = true ∧ scopeArms rc arms s₀ s₀.retDone = .ok s₁ ∧
      expectS isEmit "a match" s₁ = .ok s' := by
  simp only [scopeStmt] at h
  split at h
  · cases h
  next s₀ h₀ =>
  split at h
  · cases h
  next hn =>
  split at h
  · cases h
  next s₁ h₁ =>
  refine ⟨s₀, s₁, h₀, ?_, h₁, h⟩
  unfold needScope at hn
  split at hn
  · next hc => simpa [inScope] using hc
  · cases hn

theorem scopeFlat_made_live {rc : ℕ} {st : Stmt} {s s' : SSt} (h : scopeFlat rc st s = .ok s')
    {v : V} (hv : s'.live.contains v = true) :
    s.live.contains v = true ∨ ∃ pre, s.rest = pre ++ s'.rest ∧ v ∈ allocsOf pre := by
  obtain ⟨s₁, hfl, hr, hl, -, -⟩ := scopeFlat_inv h
  exact made_suf (flushAt_made hfl (hl ▸ hv)) ⟨[.emit], hr⟩

/-- **A value in scope after a statement** was in scope before it or is made by its walk. -/
theorem scopeStmt_made_live {rc : ℕ} {st : Stmt} {s s' : SSt} (h : scopeStmt rc st s = .ok s')
    {v : V} (hv : s'.live.contains v = true) :
    s.live.contains v = true ∨ ∃ pre, s.rest = pre ++ s'.rest ∧ v ∈ allocsOf pre := by
  cases st with
  | ite c z nz =>
    obtain ⟨s₀, s₁, h₀, -, h₁, ht⟩ := scopeIte_inv h
    have hl : s'.live = s₀.live := by
      rw [scopeIteTail_live (fun _ _ h' => scopeInner_live h') ht, scopeInner_live h₁]
    exact made_suf (flushAt_made (flushEdge_ok h₀).2 (hl ▸ hv))
      (Cons.suf ((scopeInner_cons (scopeBlock_cons rc z) h₁).trans
        (scopeIteTail_cons (fun _ _ h' => scopeInner_cons (scopeBlock_cons rc nz) h') ht)))
  | match_ x arms =>
    obtain ⟨s₀, s₁, h₀, -, h₁, hE⟩ := scopeMatch_inv' h
    obtain ⟨_, _, _, hlE, _⟩ := expectS_ok hE
    have hl : s'.live = s₀.live := by rw [hlE, scopeArms_live rc arms _ _ _ h₁]
    exact made_suf (flushAt_made (flushEdge_ok h₀).2 (hl ▸ hv))
      (Cons.suf ((scopeArms_cons rc arms _ _ _ h₁).trans (expectS_cons noAlloc_emit hE)))
  | atom a => exact scopeFlat_made_live h hv
  | call f args rets => exact scopeFlat_made_live h hv
  | callIf c f args => exact scopeFlat_made_live h hv
  | dispatch x fs args rets => exact scopeFlat_made_live h hv
  | ret vs => exact scopeFlat_made_live h hv

theorem scopeFlat_uses {rc : ℕ} {st : Stmt} {s s' : SSt} (h : scopeFlat rc st s = .ok s')
    {v : V} (hv : v ∈ ownUses st) :
    s.live.contains v = true ∨ ∃ pre, s.rest = pre ++ s'.rest ∧ v ∈ allocsOf pre := by
  obtain ⟨-, -, -, -, -, hown⟩ := scopeFlat_inv h
  exact scopeFlat_made_live h (hown v hv)

mutual
/-- **A value a block reads** is in scope at its start or made by an event its walk passes. -/
theorem scopeBlock_uses (rc : ℕ) : ∀ (ss : List Stmt) (s s' : SSt), scopeBlock rc ss s = .ok s' →
    ∀ v ∈ Stmt.usesList ss,
      s.live.contains v = true ∨ ∃ pre, s.rest = pre ++ s'.rest ∧ v ∈ allocsOf pre
  | [], _, _, _, _, hv => by simp [Stmt.usesList] at hv
  | st :: rest, s, s', h, v, hv => by
    simp only [scopeBlock] at h
    split at h
    · cases h
    · next s₁ h₁ =>
      rw [Stmt.usesList, List.mem_append] at hv
      rcases hv with hv | hv
      · exact made_suf (scopeStmt_uses rc st s s₁ h₁ v hv)
          (Cons.suf (scopeBlock_cons rc rest s₁ s' h))
      · rcases scopeBlock_uses rc rest s₁ s' h v hv with hl | hm
        · exact made_suf (scopeStmt_made_live h₁ hl) (Cons.suf (scopeBlock_cons rc rest s₁ s' h))
        · exact Or.inr (made_trans (Cons.suf (scopeStmt_cons rc st s s₁ h₁)) hm ⟨[], rfl⟩)

theorem scopeStmt_uses (rc : ℕ) : ∀ (st : Stmt) (s s' : SSt), scopeStmt rc st s = .ok s' →
    ∀ v ∈ Stmt.uses st,
      s.live.contains v = true ∨ ∃ pre, s.rest = pre ++ s'.rest ∧ v ∈ allocsOf pre
  | .ite c z nz, s, s', h, v, hv => by
    obtain ⟨s₀, s₁, h₀, hc, h₁, ht⟩ := scopeIte_inv h
    have c₀ := flushAt_cons (flushEdge_ok h₀).2
    have c₁ := scopeInner_cons (scopeBlock_cons rc z) h₁
    have cT := scopeIteTail_cons (fun _ _ h' => scopeInner_cons (scopeBlock_cons rc nz) h') ht
    have hl₀ : ∀ w, s₀.live.contains w = true →
        s.live.contains w = true ∨ ∃ pre, s.rest = pre ++ s'.rest ∧ w ∈ allocsOf pre :=
      fun w hw => made_suf (flushAt_made (flushEdge_ok h₀).2 hw) (Cons.suf (c₁.trans cT))
    simp only [Stmt.uses, List.mem_cons, List.mem_append] at hv
    rcases hv with rfl | hv | hv
    · exact hl₀ _ hc
    · obtain ⟨t₁, t₂, t₃, t₄, e₁, e₂, e₃, e₄, rfl⟩ := scopeInner_inv h₁
      obtain ⟨_, _, _, ht₁, _⟩ := expectS_ok e₁
      rcases scopeBlock_uses rc z t₁ t₂ e₂ v hv with hl | hm
      · exact hl₀ v (ht₁ ▸ hl)
      · exact Or.inr (made_trans (Cons.suf (c₀.trans (expectS_cons noAlloc_enter e₁))) hm
          (Cons.suf (((flushAt_cons (flushEdge_ok e₃).2).trans
            (expectS_cons (s' := t₄) noAlloc_leave e₄)).trans cT)))
    · rcases scopeIteTail_inv ht with ⟨r, s₂, -, h₂, hE⟩ | ⟨-, he, -⟩
      · obtain ⟨t₁, t₂, t₃, t₄, e₁, e₂, e₃, e₄, rfl⟩ := scopeInner_inv h₂
        obtain ⟨_, _, _, ht₁, _⟩ := expectS_ok e₁
        have hI := scopeInner_live h₁
        have hl₁ : t₁.live = s₀.live := ht₁.trans hI
        rcases scopeBlock_uses rc nz t₁ t₂ e₂ v hv with hl | hm
        · exact hl₀ v (hl₁ ▸ hl)
        · have cN := expectS_cons (rc := rc) noAlloc_enter e₁
          have cE := expectS_cons (rc := rc) noAlloc_emit hE
          exact Or.inr (made_trans (Cons.suf ((c₀.trans c₁).trans cN)) hm
            (Cons.suf (((flushAt_cons (flushEdge_ok e₃).2).trans
              (expectS_cons (s' := t₄) noAlloc_leave e₄)).trans cE)))
      · cases nz with
        | nil => simp [Stmt.usesList] at hv
        | cons _ _ => simp at he
  | .match_ x arms, s, s', h, v, hv => by
    obtain ⟨s₀, s₁, h₀, hx, h₁, hE⟩ := scopeMatch_inv' h
    have c₀ := flushAt_cons (flushEdge_ok h₀).2
    have cA := scopeArms_cons rc arms _ _ _ h₁
    have cE := expectS_cons (rc := rc) noAlloc_emit hE
    simp only [Stmt.uses, List.mem_cons] at hv
    rcases hv with rfl | hv
    · exact made_suf (flushAt_made (flushEdge_ok h₀).2 hx) (Cons.suf (cA.trans cE))
    · rcases scopeArms_uses rc arms s₀ _ s₁ h₁ v hv with hl | hm
      · exact made_suf (flushAt_made (flushEdge_ok h₀).2 hl) (Cons.suf (cA.trans cE))
      · exact Or.inr (made_trans (Cons.suf c₀) hm (Cons.suf cE))
  | .atom a, _, _, h, _, hv => scopeFlat_uses h (List.mem_append_left _ hv)
  | .call .., _, _, h, _, hv => scopeFlat_uses h hv
  | .callIf .., _, _, h, _, hv => scopeFlat_uses h hv
  | .dispatch .., _, _, h, _, hv => scopeFlat_uses h hv
  | .ret _, _, _, h, _, hv => scopeFlat_uses h hv

theorem scopeArms_uses (rc : ℕ) : ∀ (arms : List (List Stmt)) (s : SSt) (acc : Bool) (s' : SSt),
    scopeArms rc arms s acc = .ok s' → ∀ v ∈ Stmt.usesArms arms,
      s.live.contains v = true ∨ ∃ pre, s.rest = pre ++ s'.rest ∧ v ∈ allocsOf pre
  | [], _, _, _, _, _, hv => by simp [Stmt.usesArms] at hv
  | arm :: more, s, acc, s', h, v, hv => by
    simp only [scopeArms] at h
    split at h
    · cases h
    · next s₁ h₁ =>
      have cA := scopeArms_cons rc more _ _ s' h
      rw [Stmt.usesArms, List.mem_append] at hv
      rcases hv with hv | hv
      · obtain ⟨t₁, t₂, t₃, t₄, e₁, e₂, e₃, e₄, rfl⟩ := scopeInner_inv h₁
        obtain ⟨_, _, _, ht₁, _⟩ := expectS_ok e₁
        rcases scopeBlock_uses rc arm t₁ t₂ e₂ v hv with hl | hm
        · exact Or.inl (ht₁ ▸ hl)
        · exact Or.inr (made_trans (Cons.suf (rc := rc) (expectS_cons noAlloc_enter e₁)) hm
            (Cons.suf (((flushAt_cons (flushEdge_ok e₃).2).trans
              (expectS_cons (s' := t₄) noAlloc_leave e₄)).trans cA)))
      · rcases scopeArms_uses rc more _ _ s' h v hv with hl | hm
        · exact Or.inl (by rw [← scopeInner_live h₁]; exact hl)
        · exact Or.inr (made_trans (Cons.suf (scopeInner_cons (scopeBlock_cons rc arm) h₁)) hm
            ⟨[], rfl⟩)
end

/-! ## The blocks of a body on the scope walk -/

theorem scopeArms_mem (rc : ℕ) : ∀ (arms : List (List Stmt)) (s : SSt) (acc : Bool) (s' : SSt),
    scopeArms rc arms s acc = .ok s' → ∀ a ∈ arms,
      ∃ t t', scopeBlock rc a t = .ok t' ∧ ∃ q, s.rest = q ++ t.rest
  | [], _, _, _, _, _, ha => nomatch ha
  | arm :: more, s, acc, s', h, a, ha => by
    simp only [scopeArms] at h
    split at h
    · cases h
    · next s₁ h₁ =>
      rcases List.mem_cons.mp ha with rfl | ha
      · obtain ⟨t₁, t₂, -, -, e₁, e₂, -⟩ := scopeInner_inv h₁
        exact ⟨t₁, t₂, e₂, Cons.suf (rc := rc) (expectS_cons noAlloc_enter e₁)⟩
      · obtain ⟨t, t', ht, q, hq⟩ := scopeArms_mem rc more _ _ s' h a ha
        obtain ⟨q₁, hq₁⟩ := Cons.suf (scopeInner_cons (scopeBlock_cons rc arm) h₁)
        exact ⟨t, t', ht, q₁ ++ q, by rw [hq₁, List.append_assoc]; exact congrArg _ hq⟩

/-- **Every block of a body is walked** by the scope walk of the body, from a state whose trace
is left of the body's. -/
theorem inBody_scope {rc : ℕ} {body : List Stmt} {s₀ s₉ : SSt}
    (h : scopeBlock rc body s₀ = .ok s₉) {ss : List Stmt} (hb : InBody body ss) :
    ∃ s s', scopeBlock rc ss s = .ok s' ∧ ∃ q, s₀.rest = q ++ s.rest := by
  induction hb with
  | top => exact ⟨s₀, s₉, h, [], rfl⟩
  | tail _ ih =>
    obtain ⟨s, s', hs, q, hq⟩ := ih
    simp only [scopeBlock] at hs
    split at hs
    · cases hs
    · next s₁ h₁ =>
      obtain ⟨q₁, hq₁⟩ := Cons.suf (scopeStmt_cons rc _ s s₁ h₁)
      exact ⟨s₁, s', hs, q ++ q₁, by rw [hq, hq₁, List.append_assoc]⟩
  | iteZ _ ih =>
    obtain ⟨s, s', hs, q, hq⟩ := ih
    simp only [scopeBlock] at hs
    split at hs
    · cases hs
    · next s₁ h₁ =>
      obtain ⟨s₂, s₃, h₂, -, h₃, -⟩ := scopeIte_inv h₁
      obtain ⟨t₁, t₂, -, -, e₁, e₂, -⟩ := scopeInner_inv h₃
      obtain ⟨q₁, hq₁⟩ := Cons.suf ((flushAt_cons (flushEdge_ok h₂).2).trans
        (expectS_cons (rc := rc) noAlloc_enter e₁))
      exact ⟨t₁, t₂, e₂, q ++ q₁, by rw [hq, hq₁, List.append_assoc]⟩
  | @iteN c z nz rest _ ih =>
    obtain ⟨s, s', hs, q, hq⟩ := ih
    simp only [scopeBlock] at hs
    split at hs
    · cases hs
    · next s₁ h₁ =>
      obtain ⟨s₂, s₃, h₂, -, h₃, ht⟩ := scopeIte_inv h₁
      rcases scopeIteTail_inv ht with ⟨r, s₄, -, h₄, -⟩ | ⟨-, he, -⟩
      · obtain ⟨t₁, t₂, -, -, e₁, e₂, -⟩ := scopeInner_inv h₄
        have cN := expectS_cons (rc := rc) noAlloc_enter e₁
        obtain ⟨q₁, hq₁⟩ := Cons.suf (((flushAt_cons (flushEdge_ok h₂).2).trans
          (scopeInner_cons (scopeBlock_cons rc z) h₃)).trans cN)
        exact ⟨t₁, t₂, e₂, q ++ q₁, by rw [hq, hq₁, List.append_assoc]⟩
      · cases nz with
        | nil => exact ⟨s, s, by simp [scopeBlock], q, hq⟩
        | cons _ _ => simp at he
  | arm _ ha ih =>
    obtain ⟨s, s', hs, q, hq⟩ := ih
    simp only [scopeBlock] at hs
    split at hs
    · cases hs
    · next s₁ h₁ =>
      obtain ⟨s₂, s₃, h₂, -, h₃, -⟩ := scopeMatch_inv' h₁
      obtain ⟨t, t', ht, q₁, hq₁⟩ := scopeArms_mem rc _ _ _ _ h₃ _ ha
      obtain ⟨q₀, hq₀⟩ := Cons.suf (flushAt_cons (flushEdge_ok h₂).2)
      exact ⟨t, t', ht, q ++ q₀ ++ q₁, by rw [hq, hq₀, hq₁, List.append_assoc, List.append_assoc]⟩

/-! ## A path's values are uses -/

theorem pathVals_sub {σ : Val} {ss : List Stmt} {o : Out} {us ts : List V} (hw : o.Within us ts)
    (hs : ∀ v ∈ pathSels σ ss, v ∈ us) : ∀ v ∈ pathVals σ ss o, v ∈ us := by
  intro v hv
  simp only [pathVals, List.mem_append, List.mem_flatMap] at hv
  rcases hv with (⟨e, he, hv⟩ | hv) | hv
  · cases o with
    | fall es => exact hw.1 e he v hv
    | ret es vs => exact hw.1 e he v hv
    | stuck => simp [outEs] at he
  · cases o with
    | ret es vs => exact hw.2.2 v hv
    | fall es => simp [retVals] at hv
    | stuck => simp [retVals] at hv
  · exact hs v hv

theorem pathVals_uses {σ : Val} {s : Stmt} : ∀ v ∈ pathVals σ [s] (walk1 σ s), v ∈ Stmt.uses s :=
  pathVals_sub (walk1_within s) fun v hv => by simpa [Stmt.usesList] using pathSels_sub [s] v hv

theorem pathVals_usesList {σ : Val} {ss : List Stmt} :
    ∀ v ∈ pathVals σ ss (walk σ ss), v ∈ Stmt.usesList ss :=
  pathVals_sub (walk_within ss) (pathSels_sub ss)

/-! ## `FaAfter` -/

/-- **`FaAfter` at every block of a body** whose scope walk passes, from a trace making each value
once. -/
theorem faAfter_body {rc : ℕ} {body : List Stmt} {s₀ s₉ : SSt} (h : scopeBlock rc body s₀ = .ok s₉)
    (hnd : (allocsOf s₀.rest).Nodup) (σ : Val) :
    ∀ s rest, InBody body (s :: rest) → FaAfter σ s rest := by
  intro st rest hb v hv run hm
  obtain ⟨s, s', hs, hq⟩ := inBody_scope h hb
  simp only [scopeBlock] at hs
  split at hs
  · cases hs
  · next s₁ h₁ =>
    have hfa := scopeBlock_fa rc rest s₁ s' hs v run hm
    rcases scopeStmt_uses rc st s s₁ h₁ v (pathVals_uses v hv) with hl | hmd
    · rw [scopeStmt_live h₁ v hl] at hfa
      cases hfa
    · exact made_twice (nodup_suf hnd hq) hmd (scopeBlock_made rc rest s₁ s' hs v run hm)

/-- **The arms' analogue**: no value an arm's path reads is a frame address of a later arm. -/
theorem faArms_body {rc : ℕ} {body : List Stmt} {s₀ s₉ : SSt} (h : scopeBlock rc body s₀ = .ok s₉)
    (hnd : (allocsOf s₀.rest).Nodup) (σ : Val) :
    ∀ x arms rest, InBody body (.match_ x arms :: rest) → ∀ j (hj : j < arms.length),
      ∀ v ∈ pathVals σ arms[j] (walk σ arms[j]), ∀ run,
        Atom.frameAddr v run ∉ armsAtoms (arms.drop (j + 1)) := by
  intro x arms rest hb
  obtain ⟨s, s', hs, hq⟩ := inBody_scope h hb
  simp only [scopeBlock] at hs
  split at hs
  · cases hs
  · next s₁ h₁ =>
    obtain ⟨s₂, s₃, h₂, -, h₃, -⟩ := scopeMatch_inv' h₁
    have hnd₂ := nodup_suf (nodup_suf hnd hq) (Cons.suf (flushAt_cons (flushEdge_ok h₂).2))
    clear hs h₁ h₂ hq hnd hb
    generalize s₂.retDone = acc at h₃
    induction arms generalizing s₂ acc with
    | nil => intro j hj; simp at hj
    | cons arm more ih =>
      simp only [scopeArms] at h₃
      split at h₃
      · cases h₃
      · next t h₄ =>
        intro j hj v hv run hm
        cases j with
        | zero =>
          simp only [List.getElem_cons_zero, List.drop_succ_cons, List.drop_zero] at hv hm
          have hfa := scopeArms_fa rc more _ _ _ h₃ v run hm
          obtain ⟨pre₂, hpre₂, hp₂⟩ := scopeArms_made rc more _ _ _ h₃ v run hm
          obtain ⟨t₁, t₂, t₃, t₄, e₁, e₂, e₃, e₄, rfl⟩ := scopeInner_inv h₄
          obtain ⟨_, _, _, ht₁, _⟩ := expectS_ok e₁
          rcases scopeBlock_uses rc arm t₁ t₂ e₂ v (pathVals_usesList v hv) with hl | hmd
          · rw [ht₁] at hl
            simp only at hfa
            rw [hl] at hfa
            cases hfa
          · exact made_twice hnd₂
              (made_trans (Cons.suf (rc := rc) (expectS_cons noAlloc_enter e₁)) hmd
                (Cons.suf ((flushAt_cons (flushEdge_ok e₃).2).trans
                  (expectS_cons (s' := t₄) noAlloc_leave e₄))))
              ⟨pre₂, hpre₂, hp₂⟩
        | succ j =>
          simp only [List.getElem_cons_succ, List.drop_succ_cons] at hv hm
          have cI := scopeInner_cons (scopeBlock_cons rc arm) h₄
          exact ih { t with retDone := s₂.retDone } (nodup_suf hnd₂ (Cons.suf cI)) _
            h₃ j (by simpa using hj) v hv run hm

/-- **`FaAfter` at every block of a scoped function's body.** -/
theorem faAfter_scoped {tf : TracedFn} (h : Scoped tf) (σ : Val) :
    ∀ s rest, InBody tf.core.body (s :: rest) → FaAfter σ s rest :=
  let ⟨_, hs⟩ := scoped_body h
  faAfter_body hs (scoped_allocs h).1 σ

/-- **The arms' analogue at every `match` of a scoped function's body.** -/
theorem faArms_scoped {tf : TracedFn} (h : Scoped tf) (σ : Val) :
    ∀ x arms rest, InBody tf.core.body (.match_ x arms :: rest) → ∀ j (hj : j < arms.length),
      ∀ v ∈ pathVals σ arms[j] (walk σ arms[j]), ∀ run,
        Atom.frameAddr v run ∉ armsAtoms (arms.drop (j + 1)) :=
  let ⟨_, hs⟩ := scoped_body h
  faArms_body hs (scoped_allocs h).1 σ

/-- **`FaBody`.** -/
theorem faBody : FaBody := by
  intro _ _ _ tf _ hsc _ _ _ _ _ _ _ _ σ _ _ _ _ _
  exact faAfter_scoped hsc _

/-- **`AFaBody`.** -/
theorem aFaBody : AFaBody := by
  intro _ _ _ tf _ hsc _ _ _ _ _ _ _ _ σ _ _ _ _ _
  exact faArms_scoped hsc _

end Fa

/-- info: 'LeanVM.Guest.Backend.Complete.faBody' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms faBody

/-- info: 'LeanVM.Guest.Backend.Complete.aFaBody' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms aFaBody

end
end LeanVM.Guest.Backend.Complete
