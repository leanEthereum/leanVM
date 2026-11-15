/-
  LeanVM.Guest.Backend.Complete.FrameInner

  An inner block (`inBlock`) on the path from its block lemma, and off the path.
-/

module

public import LeanVM.Guest.Backend.Complete.FrameInduct
public import LeanVM.Guest.Backend.Complete.FrameNew
public import LeanVM.Guest.Backend.Complete.FrameLazy
public import LeanVM.Guest.Backend.Complete.FrameSegs
public import LeanVM.Guest.Backend.Complete.FrameOut
public import LeanVM.Guest.Backend.Complete.FrameFresh

/-!
# Inner blocks

`inBlockOf` proves `InBlockOf`: a block of its own on the path, from its block lemma, then its
flush, its `leave`, the anchor of a hint still waiting, the outer output and pools put back. The
scope walk's values in scope only grow through a block (`scopeBlock_live`), so the values in scope
at the block's start keep their words after it; by `flushEdge` no value made lazily waits at its
end (`flushLazy`). `InBlockOff` is the block off the path, the trace in lockstep with the scope
walk's (`inBlockOff_ok`). `scopeBlock_fa`: no frame address in a block is of a value in scope at its start
(`badAddr`).
-/

namespace LeanVM.Guest.Backend.Complete

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Memory

@[expose] public section

/-! ## The scope walk: values in scope grow, frame addresses are of values made after -/

section Live

theorem flushS_live (rc : ℕ) : ∀ (rs : List Event) (live : VMap Unit) (r : Bool) (s₁ : SSt),
    flushS rc rs live r = .ok s₁ → ∀ v, live.contains v = true → s₁.live.contains v = true
  | [], _, _, s₁, h, v, hv => by
    simp only [flushS, Except.ok.injEq] at h
    subst h
    exact hv
  | e :: es, live, r, s₁, h, v, hv => by
    have ih : ∀ l r', flushS rc es l r' = .ok s₁ → l.contains v = true →
        s₁.live.contains v = true := fun l r' h' hv' => flushS_live rc es l r' s₁ h' v hv'
    cases e <;> simp only [flushS] at h <;> (try split at h) <;> (try split at h) <;>
      (try split at h) <;>
      first
        | (cases h; done)
        | (cases h; exact hv)
        | exact ih _ _ h (addLive_of_contains _ _ _ hv)
        | exact ih _ _ h hv

theorem flushAt_live {rc : ℕ} {s s' : SSt} (h : flushAt rc s = .ok s') :
    ∀ v, s.live.contains v = true → s'.live.contains v = true :=
  flushS_live rc _ _ _ _ h

theorem scopeInner_live {rc : ℕ} {blk : SSt → Except String SSt} {s s' : SSt}
    (h : scopeInner rc blk s = .ok s') : s'.live = s.live := by
  obtain ⟨_, _, _, _, _, _, _, _, rfl⟩ := scopeInner_inv h
  rfl

theorem scopeIteTail_live {e : Bool} {nz : SSt → Except String SSt} {b : Bool}
    (hnz : ∀ s s', nz s = .ok s' → s'.live = s.live) {s s' : SSt}
    (h : scopeIteTail e nz b s = .ok s') : s'.live = s.live := by
  unfold scopeIteTail at h
  split at h
  · split at h
    · cases h
    · next s₂ h₂ =>
      obtain ⟨_, _, _, hl, _⟩ := expectS_ok h
      rw [hl]
      have h' := hnz _ _ h₂
      exact h'
  · split at h
    · cases h
    · obtain ⟨_, _, _, hl, _⟩ := expectS_ok h
      exact hl

theorem scopeArms_live (rc : ℕ) : ∀ (arms : List (List Stmt)) (s : SSt) (acc : Bool) (s' : SSt),
    scopeArms rc arms s acc = .ok s' → s'.live = s.live
  | [], s, acc, s', h => by
    simp only [scopeArms] at h
    cases h
    rfl
  | arm :: more, s, acc, s', h => by
    simp only [scopeArms] at h
    split at h
    · cases h
    · next s₁ h₁ =>
      rw [scopeArms_live rc more _ _ s' h]
      have h' := scopeInner_live h₁
      exact h'

theorem scopeStmt_live {rc : ℕ} {st : Stmt} {s s' : SSt} (h : scopeStmt rc st s = .ok s') :
    ∀ v, s.live.contains v = true → s'.live.contains v = true := by
  intro v hv
  cases st with
  | ite c z nz =>
    simp only [scopeStmt] at h
    split at h
    · cases h
    · next s₀ h₀ =>
      split at h
      · cases h
      · split at h
        · cases h
        · next s₁ h₁ =>
          rw [scopeIteTail_live (fun _ _ h' => scopeInner_live h') h, scopeInner_live h₁]
          exact flushAt_live (flushEdge_ok h₀).2 v hv
  | match_ x arms =>
    simp only [scopeStmt] at h
    split at h
    · cases h
    · next s₀ h₀ =>
      split at h
      · cases h
      · split at h
        · cases h
        · next s₁ h₁ =>
          obtain ⟨_, _, _, hl, _⟩ := expectS_ok h
          rw [hl]
          show s₁.live.contains v = true
          rw [scopeArms_live rc arms _ _ _ h₁]
          exact flushAt_live (flushEdge_ok h₀).2 v hv
  | atom a =>
    obtain ⟨s₁, hfl, -, hl₁, -, -⟩ := scopeFlat_inv h
    rw [hl₁]
    exact flushAt_live hfl v hv
  | call f args rets =>
    obtain ⟨s₁, hfl, -, hl₁, -, -⟩ := scopeFlat_inv h
    rw [hl₁]
    exact flushAt_live hfl v hv
  | callIf c f args =>
    obtain ⟨s₁, hfl, -, hl₁, -, -⟩ := scopeFlat_inv h
    rw [hl₁]
    exact flushAt_live hfl v hv
  | dispatch x fs args rets =>
    obtain ⟨s₁, hfl, -, hl₁, -, -⟩ := scopeFlat_inv h
    rw [hl₁]
    exact flushAt_live hfl v hv
  | ret vs =>
    obtain ⟨s₁, hfl, -, hl₁, -, -⟩ := scopeFlat_inv h
    rw [hl₁]
    exact flushAt_live hfl v hv

/-- **The values in scope only grow** through a block of the scope walk. -/
theorem scopeBlock_live (rc : ℕ) : ∀ (ss : List Stmt) (s s' : SSt), scopeBlock rc ss s = .ok s' →
    ∀ v, s.live.contains v = true → s'.live.contains v = true
  | [], s, s', h => by
    simp only [scopeBlock] at h
    cases h
    exact fun _ h => h
  | st :: rest, s, s', h => by
    simp only [scopeBlock] at h
    split at h
    · cases h
    · next s₁ h₁ => exact fun v hv => scopeBlock_live rc rest s₁ s' h v (scopeStmt_live h₁ v hv)

/-- A frame address statement of the scope walk is of a value not in scope before it. -/
theorem scopeFlat_addr {rc : ℕ} {p : V} {run : List V} {s s' : SSt}
    (h : scopeFlat rc (.atom (.frameAddr p run)) s = .ok s') : s.live.contains p = false := by
  unfold scopeFlat at h
  split at h
  · cases h
  split at h
  · cases h
  split at h
  · cases h
  split at h
  · cases h
  · next hb =>
    simp only [badAddr, Bool.or_eq_true, not_or] at hb
    simpa using hb.1.2

theorem not_live_of {rc : ℕ} {st : Stmt} {s s' : SSt} (h : scopeStmt rc st s = .ok s') {v : V}
    (hv : s'.live.contains v = false) : s.live.contains v = false := by
  cases hx : s.live.contains v with
  | false => rfl
  | true => rw [scopeStmt_live h v hx] at hv; cases hv

theorem not_live_inner {s s₁ : SSt}
    (h : expectS isEnter "a block" s = .ok s₁) {v : V}
    (hb : s₁.live.contains v = false) : s.live.contains v = false := by
  obtain ⟨_, _, _, hl, _⟩ := expectS_ok h
  rwa [hl] at hb

mutual
/-- **No frame address in a block is of a value in scope at its start** (`badAddr`). -/
theorem scopeBlock_fa (rc : ℕ) : ∀ (ss : List Stmt) (s s' : SSt), scopeBlock rc ss s = .ok s' →
    ∀ p run, Atom.frameAddr p run ∈ atomsIn ss → s.live.contains p = false
  | [], _, _, _, _, _, hm => by simp [atomsIn] at hm
  | st :: rest, s, s', h, p, run, hm => by
    simp only [scopeBlock] at h
    split at h
    · cases h
    · next s₁ h₁ =>
      rw [atomsIn, List.mem_append] at hm
      rcases hm with hm | hm
      · exact scopeStmt_fa rc st s s₁ h₁ p run hm
      · exact not_live_of h₁ (scopeBlock_fa rc rest s₁ s' h p run hm)

theorem scopeStmt_fa (rc : ℕ) : ∀ (st : Stmt) (s s' : SSt), scopeStmt rc st s = .ok s' →
    ∀ p run, Atom.frameAddr p run ∈ atomsOf st → s.live.contains p = false
  | .ite c z nz, s, s', h, p, run, hm => by
    simp only [scopeStmt] at h
    split at h
    · cases h
    · next s₀ h₀ =>
      have hpre : s₀.live.contains p = false → s.live.contains p = false := fun hb => by
        cases hx : s.live.contains p with
        | false => rfl
        | true => rw [flushAt_live (flushEdge_ok h₀).2 p hx] at hb; cases hb
      split at h
      · cases h
      · split at h
        · cases h
        · next s₁ h₁ =>
          rw [atomsOf, List.mem_append] at hm
          rcases hm with hm | hm
          · obtain ⟨t₁, t₂, -, -, e₁, e₂, -, -, -⟩ := scopeInner_inv h₁
            exact hpre (not_live_inner e₁ (scopeBlock_fa rc z t₁ t₂ e₂ p run hm))
          · unfold scopeIteTail at h
            split at h
            · split at h
              · cases h
              · next s₂ h₂ =>
                obtain ⟨t₁, t₂, -, -, e₁, e₂, -, -, -⟩ := scopeInner_inv h₂
                have := not_live_inner e₁ (scopeBlock_fa rc nz t₁ t₂ e₂ p run hm)
                exact hpre (by rw [← scopeInner_live h₁]; exact this)
            · split at h
              · cases h
              · next hne =>
                cases nz with
                | nil => simp [atomsIn] at hm
                | cons _ _ => simp at hne
  | .match_ x arms, s, s', h, p, run, hm => by
    simp only [scopeStmt] at h
    split at h
    · cases h
    · next s₀ h₀ =>
      split at h
      · cases h
      · split at h
        · cases h
        · next s₁ h₁ =>
          have hb := scopeArms_fa rc arms s₀ s₀.retDone s₁ h₁ p run hm
          cases hx : s.live.contains p with
          | false => rfl
          | true => rw [flushAt_live (flushEdge_ok h₀).2 p hx] at hb; cases hb
  | .atom a, s, s', h, p, run, hm => by
    simp only [atomsOf, List.mem_singleton] at hm
    subst hm
    exact scopeFlat_addr h
  | .call .., _, _, _, _, _, hm => by simp [atomsOf] at hm
  | .callIf .., _, _, _, _, _, hm => by simp [atomsOf] at hm
  | .dispatch .., _, _, _, _, _, hm => by simp [atomsOf] at hm
  | .ret _, _, _, _, _, _, hm => by simp [atomsOf] at hm

theorem scopeArms_fa (rc : ℕ) : ∀ (arms : List (List Stmt)) (s : SSt) (acc : Bool) (s' : SSt),
    scopeArms rc arms s acc = .ok s' →
    ∀ p run, Atom.frameAddr p run ∈ armsAtoms arms → s.live.contains p = false
  | [], _, _, _, _, _, _, hm => by simp [armsAtoms] at hm
  | arm :: more, s, acc, s', h, p, run, hm => by
    simp only [scopeArms] at h
    split at h
    · cases h
    · next s₁ h₁ =>
      rw [armsAtoms, List.mem_append] at hm
      rcases hm with hm | hm
      · obtain ⟨t₁, t₂, -, -, e₁, e₂, -, -, -⟩ := scopeInner_inv h₁
        exact not_live_inner e₁ (scopeBlock_fa rc arm t₁ t₂ e₂ p run hm)
      · have := scopeArms_fa rc more { s₁ with retDone := s.retDone } _ s' h p run hm
        rw [← scopeInner_live h₁]
        exact this
end

end Live

/-! ## Placement facts -/

section Place

variable {ctx : Ctx}

theorem expect_rest {e : Event → Bool} {what : String} {st : St} :
    wpP (expect e what) ctx st fun _ st' => st' = { st with rest := st.rest.tail } := by
  unfold expect
  refine wp_bind.mpr (wp_peek.mpr ?_)
  split
  · split
    · exact wp_modify.mpr rfl
    · exact wp_failP
  · exact wp_failP

theorem fresh_eq {st : St} :
    wpP fresh ctx st fun o st' => o = st.next ∧ st' = { st with next := st.next + 1 } :=
  wp_modifyGet.mpr ⟨rfl, rfl⟩

theorem emitOp_eq {o : LOp} {st : St} :
    wpP (emitOp o) ctx st fun _ st' =>
      st' = { st with pending := #[], out := st.out.push (.op st.pending.toList o) } := by
  unfold emitOp takeHints push
  exact wp_bind.mpr (wp_modifyGet.mpr (wp_modify.mpr rfl))

/-- `RR` with the trace passed forgotten. -/
theorem RR.old {S : V → Prop} {st st' : St} (h : RR S st st') :
    (∀ v, st'.locs[v]? ≠ none → st.locs[v]? ≠ none ∨ v ∈ allocsOf st.rest ∨
      (∃ k, st.lazy = some (v, k)) ∨ S v) ∧
    (∀ v ∈ allocsOf st'.rest, v ∈ allocsOf st.rest) ∧
    ∀ x ∈ st.tables.shared, x ∈ st'.tables.shared := by
  obtain ⟨pre, hpre, h1, -, h4⟩ := h
  refine ⟨fun v hv => ?_, fun v hv => by
    rw [hpre, allocsOf_append]
    exact List.mem_append_right _ hv, h4⟩
  rcases h1 v hv with h | h | h | h
  · exact Or.inl h
  · exact Or.inr (Or.inl (by rw [hpre, allocsOf_append]; exact List.mem_append_left _ h))
  · exact Or.inr (Or.inr (Or.inl h))
  · exact Or.inr (Or.inr (Or.inr h))

/-- A block's placement ends with no value waiting to be placed if none waited at its start. -/
theorem placeBlock_lazy : ∀ (ss : List Stmt) (st : St), st.lazy = none →
    wpP (placeBlock ss) ctx st fun _ st' => st'.lazy = none
  | [], st, h => by
    rw [placeBlock]
    exact wp_pure.mpr h
  | s :: rest, st, _ => by
    rw [placeBlock, ← bind_assoc]
    exact wp_bind.mpr (wp_mono (end_lazy (placeStmt s rest) st) fun _ st₁ h₁ =>
      placeBlock_lazy rest st₁ h₁)

end Place

/-! ## Words: straight-line instructions after a block that falls through -/

section Words

variable {κ₀ : ℕ} {Γ : Site κ₀}
  {Ag : Val → (ℕ → E) → (ℕ → E × E) → (κ : ℕ) → MemoryImage κ → Prop} {cl : List Call}
  {I : Inst} {bx : Ctx}

theorem BlkW.append_ops (hok : OpOK Γ I Ag cl) {C : (ℕ → E) → Prop} {blk ops : List PStmt}
    {ss tl : List Stmt} {es : List Ev} {i₀ pos : ℕ}
    (h : BlkW Γ I bx Ag cl C blk ss tl (.fall es) i₀ pos)
    (hW : ∀ s ∈ ops, ∃ h o, s = PStmt.op h o ∧ ∀ Ψ, C Ψ → OpW I Ψ o) :
    BlkW Γ I bx Ag cl C (blk ++ ops) ss tl (.fall es) i₀ pos := by
  cases ops with
  | nil => rwa [List.append_nil]
  | cons x xs =>
    obtain ⟨hs, hl, hh, h⟩ := h
    refine ⟨hs, hl, hh, fun hp Ψ hΨ σ' hσ kh cs ks next kj kret khalt hops hcs hks hk => ?_⟩
    rw [wLc_append _ _ _ _ _ _ _ blk (x :: xs) (List.cons_ne_nil _ _)]
    refine h hp Ψ hΨ σ' hσ kh cs ks _ _ kret khalt
      (fun o' ho => hops o' (by rw [bops_append]; exact List.mem_append_left _ ho)) hcs hks ?_
    intro cs' hcs'
    exact wLc_ops hok hΨ hσ kh (x :: xs) hW _
      (fun o' ho => hops o' (by rw [bops_append]; exact List.mem_append_right _ ho)) cs' _ next _
      kret khalt (hk cs' hcs')

end Words

/-! ## An inner block on the path -/

section Inner

variable {κ₀ : ℕ} {Γ : Site κ₀}
  {Ag : Val → (ℕ → E) → (ℕ → E × E) → (κ : ℕ) → MemoryImage κ → Prop} {cl : List Call}
  {ctx : Ctx} {I : Inst}

/-- **An inner block on the path from its block lemma.** -/
theorem inBlockOf (hok : OpOK Γ I Ag cl) (hI : I.Ok) : InBlockOf Γ Ag cl ctx I := by
  intro z hz C st sc sc' i₀ p₁ o hsc hw hns hes hcl hinv hc
  obtain ⟨s₁, s₂, s₃, s₄, h₁, h₂, h₃e, h₄, rfl⟩ := scopeInner_inv hsc
  obtain ⟨hlf, h₃⟩ := flushEdge_ok h₃e
  obtain ⟨hst, hinv₁⟩ := winv_enter hinv h₁
  obtain ⟨_, -, -, hlv₁, -⟩ := expectS_ok h₁
  obtain ⟨ev₄, hr₄, he₄, -, hrd₄⟩ := expectS_ok h₄
  have hsub₂ : ∀ v, sc.live.contains v = true → s₂.live.contains v = true := fun v hv =>
    scopeBlock_live _ z s₁ s₂ h₂ v (by rw [hlv₁]; exact hv)
  have ht : st.rest.tail = s₁.rest := by rw [hst]; rfl
  rw [← ht] at hinv₁
  have hB := hz [] C _ s₁ s₂ i₀ p₁ o h₂ hw hns hes hcl hinv₁ hc
  unfold inBlock
  refine wp_bind.mpr (wp_mono (expect_rest (st := st)) fun _ stA hA => ?_)
  subst hA
  refine wp_bind.mpr (wp_get.mpr (wp_bind.mpr (wp_set.mpr ?_)))
  refine wp_bind.mpr (wp_mono (wp_and hB (placeBlock_lazy z _ hinv.lazy))
    fun _ st₂ ⟨⟨C₂, hsat₂, hbl₂, hs₂, hn₂, hl₂, hW₂, hch₂, hb₂⟩, hlz₂⟩ => ?_)
  by_cases hP : (∃ es, o = .fall es) ∧ FinAt Γ I Ag p₁ st₂
  · obtain ⟨⟨es, rfl⟩, hF₂⟩ := hP
    have hinv₂ := hW₂ es rfl hF₂
    have hfl₃ : flushS ctx.retCells st₂.rest s₂.live s₂.retDone = .ok s₃ := by
      rw [← hinv₂.rest]
      exact h₃
    obtain ⟨hseg, -, huseS⟩ := flushS_seg _ _ _ _ _ hfl₃
    have hsegA : ∀ v ∈ allocsOf (flushSeg st₂.rest), st₂.locs[v]? = none := fun v hv =>
      (hinv₂.fresh v (by rw [hseg, allocsOf_append]; exact List.mem_append_left _ hv)).1
    have hall : allocsOf st₂.rest = allocsOf (flushSeg st₂.rest) ++ allocsOf s₄.rest := by
      conv_lhs => rw [hseg]
      rw [allocsOf_append, hr₄, allocsOf_other (e := ev₄) (fun vs k h => by
        subst h
        simp [isLeave] at he₄)]
    have hnd : (allocsOf (flushSeg st₂.rest) ++ allocsOf s₄.rest).Nodup := hall ▸ hinv₂.nodup
    have hFl := flushSeg_lock ctx I C₂ st₂ [] s₂.live s₂.retDone s₃
      (fun v => s₂.live.contains v = true ∨ st₂.locs[v]? = none) hI hfl₃ hinv₂.fuel
      (fun k _ _ _ hk => by simp at hk)
      (fun v _ _ hv _ => (huseS v hv).elim Or.inl fun h => Or.inr (hsegA v h))
      hinv₂.abi hinv₂.two
      (fun v l hv hl => hv.elim (fun h => hinv₂.vw v l h hl) fun h => by rw [h] at hl; cases hl)
      (fun hr k hk Ψ w hC => hinv₂.ret hr Ψ k w hk hC) hinv₂.cok
    refine wp_bind.mpr (wp_mono (wp_and hFl (wp_and (wp_and (flush_keep (st := st₂) (up := []))
      (flush_r (S := fun _ => False) (st := st₂) (up := [])))
      (flushLazy [] st₂ (by rw [← hinv₂.rest]; exact hlf))))
      fun _ st₃ ⟨⟨C₃, hc₃, hs₃, hn₃, hl₃, hE₃, hr₃, hFR₃, hrb₃, hnew₃⟩, ⟨hk₃, hR₃⟩, hz₃⟩ => ?_)
    have hr₃' : st₃.rest.tail = s₄.rest := by rw [hr₃, hr₄]; rfl
    refine wp_bind.mpr (wp_mono (expect_rest (st := st₃)) fun _ st₄ h₄' => ?_)
    subst h₄'
    refine wp_bind.mpr (wp_get.mpr ?_)
    have fin : ∀ (C₅ : (ℕ → E) → Prop) (st₅ : St), COk I C₅ st₅.next st₅.scope st₅.locs →
        Stronger C₅ C₃ → st₃.next ≤ st₅.next → st₅.locs = st₃.locs → st₅.rest = s₄.rest →
        st₅.lazy = st₃.lazy → st₅.chainIn = st₃.chainIn →
        (∀ c, c < st₃.next → BlindAt C₃ c → BlindAt C₅ c) → EmitsW I C₅ st₃ st₅ →
        ∃ C', (∃ Ψ, C' Ψ) ∧ Blind C' st₅.next ∧ Stronger C' C ∧ st.next ≤ st₅.next ∧
          LocsLe st.locs st₅.locs ∧
          ({ st₅ with out := st.out, scope := st.scope } : St).out = st.out ∧
          ({ st₅ with out := st.out, scope := st.scope } : St).scope = st.scope ∧
          ({ st₅ with out := st.out, scope := st.scope } : St).chainIn = none ∧
          (∀ es', Out.fall es = .fall es' → Fits I { st₅ with out := st.out, scope := st.scope } →
            OpsIn I p₁ (blockOps st₅.out.toList p₁) →
            TabsW Γ Ag { st₅ with out := st.out, scope := st.scope } →
            WInv ctx I C' { st₅ with out := st.out, scope := st.scope }
              { s₄ with live := sc.live }) ∧
          (Fits I { st₅ with out := st.out, scope := st.scope } →
            OpsIn I p₁ (blockOps st₅.out.toList p₁) →
            TabsW Γ Ag { st₅ with out := st.out, scope := st.scope } →
            BlkW Γ I ctx Ag cl C' st₅.out.toList z [] (.fall es) i₀ p₁ ∧
            RW I C' { st₅ with out := st.out, scope := st.scope } (pathVals I.σ z (.fall es))) := by
      intro C₅ st₅ hc₅ hs₅ hn₅ hl₅ hr₅ hz₅ hk₅ hbk₅ hE₅
      have hsC : Stronger C₅ C := (hs₂.trans hs₃).trans hs₅
      have hnT : st.next ≤ st₅.next := le_trans hn₂ (le_trans hn₃ hn₅)
      have hlT : LocsLe st.locs st₅.locs := fun v x h => by rw [hl₅]; exact hl₃ v x (hl₂ v x h)
      have hch₅ : st₅.chainIn = none := by rw [hk₅, hk₃]; exact hch₂
      have hE := hE₃.step hE₅ hs₅ hn₅ (by rw [hl₅]; exact LocsLe.refl _)
      refine ⟨C₅, hc₅.sat, hc₅.blind, hsC, hnT, hlT, rfl, rfl, hch₅, ?_, ?_⟩
      · intro _ _ _ _ _
        refine ⟨⟨hc₅.sat, hc₅.blind, fun Ψ hΨ => (hc.pools Ψ (hsC Ψ hΨ)).grow hlT,
          hc.cells.mono hnT⟩, hr₅.symm,
          VW.step ((hFR₃.2).anti fun v hv => Or.inl (Or.inl (hsub₂ v hv))) hs₅ hn₅ hl₅,
          le_trans hinv.two hnT, le_trans hinv.abi hnT, ?_, ?_, ?_, ?_, hch₅, hinv.pnt, ?_⟩
        · show st₅.rest.length ≤ ctx.fuel
          have h1 := hinv₂.fuel
          rw [hseg, hr₄, List.length_append, List.length_cons] at h1
          rw [hr₅]
          omega
        · intro hr Ψ k w hk hΨ
          have hab := hinv₂.abi
          refine hbk₅ _ (by simp only [Cell] at *; omega) (hrb₃ (by rw [← hrd₄]; exact hr) k hk)
            Ψ w hΨ
        · show (allocsOf st₅.rest).Nodup
          rw [hr₅]
          exact hnd.of_append_right
        · intro v hv
          have hv' : v ∈ allocsOf s₄.rest := by rw [← hr₅]; exact hv
          obtain ⟨hn0, hl0⟩ := hinv₂.fresh v (by rw [hall]; exact List.mem_append_right _ hv')
          have hns : v ∉ allocsOf (flushSeg st₂.rest) := fun h =>
            List.disjoint_of_nodup_append hnd h hv'
          refine ⟨?_, ?_⟩
          · show st₅.locs[v]? = none
            rw [hl₅]
            cases hx : st₃.locs[v]? with
            | none => rfl
            | some x =>
              rcases hnew₃ v (by rw [hx]; simp) with h | h
              · exact absurd hn0 h
              · exact absurd h hns
          · show sc.live.contains v = false
            cases hx : sc.live.contains v with
            | false => rfl
            | true => rw [hsub₂ v hx] at hl0; cases hl0
        · show st₅.lazy = none
          rw [hz₅, hz₃]
          exact hinv₂.lazy
      · intro hFt hOps _
        have hO₅ : OutOps I st₅ := fun _ _ hm => hOps.mem _ (op_mem_blockOps _ p₁ hm)
        obtain ⟨blk₂, hob₂, hbw₂, hrw₂⟩ := hb₂ hF₂
        have hob₂' : st₂.out.toList = blk₂ := hob₂
        have hbw₂' : BlkW Γ I ctx Ag cl C₂ blk₂ z [] (.fall es) i₀ p₁ := hbw₂
        obtain ⟨ops, hops, hopsW⟩ := hE
        refine ⟨?_, ?_⟩
        · rw [hops, hob₂']
          exact BlkW.append_ops hok (hbw₂'.mono (hs₃.trans hs₅)) (hopsW hFt hO₅)
        · refine hrw₂.grow (hs₃.trans hs₅) (le_trans hn₃ hn₅)
            (fun v x h => by rw [hl₅]; exact hl₃ v x h) ?_ ?_
          · intro v _ hv
            rcases hR₃.old.1 v (by rw [← hl₅]; exact hv) with h | h | ⟨k, h⟩ | h
            · exact Or.inl h
            · exact Or.inr h
            · rw [hlz₂] at h
              cases h
            · exact h.elim
          · intro v hv
            rw [hall]
            exact List.mem_append_right _ (by rw [← hr₅]; exact hv)
    dsimp only
    split
    · refine wp_bind.mpr (wp_mono (fresh_fat (C := C₃) (st := { st₃ with rest := st₃.rest.tail })
        (fun _ => I.kw (.const 0 0)) (wblind_const _ _) hc₃)
        fun o₅ st₅ ⟨C₅, hc₅, hs₅, hn₅, hl₅, hE₅, ho₅, hst₅, hC₅⟩ => ?_)
      subst ho₅ hC₅
      have h2 : 2 ≤ st₃.next := le_trans hinv₂.two hn₃
      refine wp_bind.mpr (wp_mono (emitOp_fat (.set st₃.next (.const 0 0))
        (fun _ _ Ψ hΨ => by
          show fw I Ψ st₃.next = I.kw (.const 0 0)
          rw [fw_of_two h2]
          exact hΨ.2) hc₅)
        fun _ st₆ ⟨C₆, hc₆, hs₆, hn₆, hl₆, hE₆, hC₆, hst₆⟩ => ?_)
      subst hC₆
      exact wp_bind.mpr (wp_get.mpr (wp_bind.mpr (wp_set.mpr (wp_pure.mpr
        (fin _ st₆ hc₆ hs₅ (by rw [hst₆, hst₅]; exact Nat.le_succ _) (by rw [hst₆, hst₅])
          (by rw [hst₆, hst₅]; exact hr₃') (by rw [hst₆, hst₅]) (by rw [hst₆, hst₅])
          (fun c hc' hb Ψ w hΨ => ⟨hb Ψ w hΨ.1,
            (Function.update_of_ne (Nat.ne_of_gt hc') w Ψ).trans hΨ.2⟩)
          (hE₅.step hE₆ (Stronger.refl _) hn₆ hl₆))))))
    · exact wp_bind.mpr (wp_get.mpr (wp_bind.mpr (wp_set.mpr (wp_pure.mpr
        (fin C₃ { st₃ with rest := st₃.rest.tail } hc₃ (Stronger.refl _) le_rfl rfl hr₃' rfl rfl
          (fun _ _ h => h) (EmitsW.refl _))))))
  · refine wp_bind.mpr (wp_mono (wp_and (wp_and (flush_mono (st := st₂) (up := []))
      (flush_app (st := st₂) (up := []))) (wp_and (flush_keep (st := st₂) (up := []))
      (flush_r (S := fun _ => False) (st := st₂) (up := []))))
      fun _ st₃ ⟨⟨⟨hn₃, hl₃⟩, hA₃⟩, hk₃, hR₃⟩ => ?_)
    refine wp_bind.mpr (wp_mono (expect_rest (st := st₃)) fun _ st₄ h₄' => ?_)
    subst h₄'
    refine wp_bind.mpr (wp_get.mpr ?_)
    have fin : ∀ (st₅ : St), st₃.next ≤ st₅.next → st₅.locs = st₃.locs →
        st₅.rest = st₃.rest.tail → st₅.chainIn = st₃.chainIn → st₅.tables = st₃.tables →
        (∃ blk, st₅.out.toList = st₃.out.toList ++ blk) →
        ∃ C', (∃ Ψ, C' Ψ) ∧ Blind C' st₅.next ∧ Stronger C' C ∧ st.next ≤ st₅.next ∧
          LocsLe st.locs st₅.locs ∧
          ({ st₅ with out := st.out, scope := st.scope } : St).out = st.out ∧
          ({ st₅ with out := st.out, scope := st.scope } : St).scope = st.scope ∧
          ({ st₅ with out := st.out, scope := st.scope } : St).chainIn = none ∧
          (∀ es', o = .fall es' → Fits I { st₅ with out := st.out, scope := st.scope } →
            OpsIn I p₁ (blockOps st₅.out.toList p₁) →
            TabsW Γ Ag { st₅ with out := st.out, scope := st.scope } →
            WInv ctx I C' { st₅ with out := st.out, scope := st.scope }
              { s₄ with live := sc.live }) ∧
          (Fits I { st₅ with out := st.out, scope := st.scope } →
            OpsIn I p₁ (blockOps st₅.out.toList p₁) →
            TabsW Γ Ag { st₅ with out := st.out, scope := st.scope } →
            BlkW Γ I ctx Ag cl C' st₅.out.toList z [] o i₀ p₁ ∧
            RW I C' { st₅ with out := st.out, scope := st.scope } (pathVals I.σ z o)) := by
      intro st₅ hn₅ hl₅ hr₅ hk₅ ht₅ hA₅
      have hnT : st₂.next ≤ st₅.next := le_trans hn₃ hn₅
      have hlT : LocsLe st₂.locs st₅.locs := fun v x h => by rw [hl₅]; exact hl₃ v x h
      obtain ⟨b₃, hb₃⟩ := hA₃
      obtain ⟨b₅, hb₅⟩ := hA₅
      have hob : st₅.out.toList = st₂.out.toList ++ (b₃ ++ b₅) := by
        rw [hb₅, hb₃, List.append_assoc]
      have hfin : Fits I { st₅ with out := st.out, scope := st.scope } →
          OpsIn I p₁ (blockOps st₅.out.toList p₁) →
          TabsW Γ Ag { st₅ with out := st.out, scope := st.scope } → FinAt Γ I Ag p₁ st₂ :=
        fun hFt hOps hT => FinAt.back (st' := st₅) ⟨hFt, hOps, hT⟩ hnT hlT hob
          fun x hx => by rw [ht₅]; exact hR₃.old.2.2 x hx
      refine ⟨C₂, hsat₂, hbl₂.mono hnT, hs₂, le_trans hn₂ hnT, hl₂.trans hlT, rfl, rfl,
        by rw [hk₅, hk₃]; exact hch₂, fun es' he hFt hOps hT => (hP ⟨⟨es', he⟩,
          hfin hFt hOps hT⟩).elim, fun hFt hOps hT => ?_⟩
      have hF₂ := hfin hFt hOps hT
      obtain ⟨blk₂, hob₂, hbw₂, hrw₂⟩ := hb₂ hF₂
      have hob₂' : st₂.out.toList = blk₂ := hob₂
      refine ⟨?_, ?_⟩
      · cases o with
        | fall es' => exact (hP ⟨⟨es', rfl⟩, hF₂⟩).elim
        | stuck => exact absurd rfl hns
        | ret es' vs =>
          have hbw₂' : BlkW Γ I ctx Ag cl C₂ blk₂ z ([] ++ []) (.ret es' vs) i₀ p₁ := hbw₂
          have := BlkW.append_ret (blk₂ := b₃ ++ b₅) hbw₂'
          rw [List.append_nil] at this
          rw [hob, hob₂']
          exact this
      · refine hrw₂.grow (Stronger.refl _) hnT hlT ?_ ?_
        · intro v _ hv
          rcases hR₃.old.1 v (by rw [← hl₅]; exact hv) with h | h | ⟨k, h⟩ | h
          · exact Or.inl h
          · exact Or.inr h
          · rw [hlz₂] at h
            cases h
          · exact h.elim
        · intro v hv
          exact hR₃.old.2.1 v (allocsOf_tail (by rw [← hr₅]; exact hv))
    dsimp only
    split
    · refine wp_bind.mpr (wp_mono fresh_eq fun o₅ st₅ ⟨_, hst₅⟩ => ?_)
      refine wp_bind.mpr (wp_mono (wp_and emitOp_eq emitOp_app) fun _ st₆ ⟨hst₆, hA₆⟩ => ?_)
      obtain ⟨b₆, hb₆⟩ := hA₆
      exact wp_bind.mpr (wp_get.mpr (wp_bind.mpr (wp_set.mpr (wp_pure.mpr
        (fin st₆ (by rw [hst₆, hst₅]; exact Nat.le_succ _) (by rw [hst₆, hst₅])
          (by rw [hst₆, hst₅]) (by rw [hst₆, hst₅]) (by rw [hst₆, hst₅])
          ⟨b₆, by rw [hb₆, hst₅]⟩)))))
    · exact wp_bind.mpr (wp_get.mpr (wp_bind.mpr (wp_set.mpr (wp_pure.mpr
        (fin { st₃ with rest := st₃.rest.tail } le_rfl rfl rfl rfl rfl ⟨[], by simp⟩)))))

end Inner

/-! ## An inner block off the path -/

/-- **Values the trace makes later stay unplaced** through a block in lockstep with the scope
walk (owed by the primitives' agent). -/
def BlockFresh : Prop :=
  ∀ (ctx : Ctx) (ss : List Stmt) (st : St) (s s' : SSt), scopeBlock ctx.retCells ss s = .ok s' →
    st.rest = s.rest → st.rest.length ≤ ctx.fuel → (allocsOf st.rest).Nodup → st.lazy = none →
    (∀ v run, Atom.frameAddr v run ∈ atomsIn ss → v ∉ allocsOf s'.rest) →
    wpP (placeBlock ss) ctx st fun _ st' =>
      ∀ v ∈ allocsOf st'.rest, st.locs[v]? = none → st'.locs[v]? = none

/-- `BlockFresh` for a block of its own (owed by the primitives' agent). -/
def InBlockFresh : Prop :=
  ∀ (ctx : Ctx) (z : List Stmt) (st : St) (sc sc' : SSt),
    scopeInner ctx.retCells (fun s' => scopeBlock ctx.retCells z s') sc = .ok sc' →
    st.rest = sc.rest → st.rest.length ≤ ctx.fuel → (allocsOf st.rest).Nodup → st.lazy = none →
    (∀ v run, Atom.frameAddr v run ∈ atomsIn z → v ∉ allocsOf sc'.rest) →
    wpP (inBlock (placeBlock z)) ctx st fun _ st' =>
      ∀ v ∈ allocsOf st'.rest, st.locs[v]? = none → st'.locs[v]? = none

/-- **An inner block off the path** (a branch or an arm not taken): its trace in lockstep with
the scope walk's, the outer output and pools given back, no `match` chaining out if none chained
in, the next free cell up, the places grown; from a state with no value waiting: none waiting
after it, the places it adds of values the trace left makes or frame addresses of its atoms, and
(the trace making each value once) the values made later still unplaced; the trace left shrinks
and the shared tables grow. -/
def InBlockOff (ctx : Ctx) (z : List Stmt) : Prop :=
  ∀ (st : St) (sc sc' : SSt),
    scopeInner ctx.retCells (fun s' => scopeBlock ctx.retCells z s') sc = .ok sc' →
    st.rest = sc.rest → st.rest.length ≤ ctx.fuel →
    wpP (inBlock (placeBlock z)) ctx st fun _ st' => st'.rest = sc'.rest ∧
      st'.scope = st.scope ∧ st'.out = st.out ∧ (st.chainIn = none → st'.chainIn = none) ∧
      st.next ≤ st'.next ∧ LocsLe st.locs st'.locs ∧
      (st.lazy = none → st'.lazy = none ∧
        (∀ v, st'.locs[v]? ≠ none → st.locs[v]? ≠ none ∨ v ∈ allocsOf st.rest ∨
          ∃ run, Atom.frameAddr v run ∈ atomsIn z) ∧
        ((allocsOf st.rest).Nodup →
          ∀ v ∈ allocsOf st'.rest, st.locs[v]? = none → st'.locs[v]? = none)) ∧
      (∀ v ∈ allocsOf st'.rest, v ∈ allocsOf st.rest) ∧
      ∀ x ∈ st.tables.shared, x ∈ st'.tables.shared

/-! ## The value of a frame address is made inside the block -/

section Made

theorem Cons.suf {rc : ℕ} {r r' : List Event} (h : Cons rc r r') : ∃ q, r = q ++ r' :=
  let ⟨q, hq, _⟩ := h
  ⟨q, hq⟩

theorem made_trans {p : V} {a b c d : List Event} (h₁ : ∃ q, a = q ++ b)
    (h₂ : ∃ pre, b = pre ++ c ∧ p ∈ allocsOf pre) (h₃ : ∃ q, c = q ++ d) :
    ∃ pre, a = pre ++ d ∧ p ∈ allocsOf pre := by
  obtain ⟨q₁, rfl⟩ := h₁
  obtain ⟨pre, rfl, hp⟩ := h₂
  obtain ⟨q₃, rfl⟩ := h₃
  exact ⟨q₁ ++ pre ++ q₃, by simp [List.append_assoc], by
    rw [allocsOf_append, allocsOf_append]
    exact List.mem_append_left _ (List.mem_append_right _ hp)⟩

/-- A frame address statement's value is made by the flush right before it (`badAddr`). -/
theorem scopeFlat_made {rc : ℕ} {p : V} {run : List V} {s s' : SSt}
    (h : scopeFlat rc (.atom (.frameAddr p run)) s = .ok s') :
    ∃ pre, s.rest = pre ++ s'.rest ∧ p ∈ allocsOf pre := by
  obtain ⟨s₁, hfl, hr₁, hl₁, -, -⟩ := scopeFlat_inv h
  have hb : s.live.contains p = false ∧ s'.live.contains p = true := by
    unfold scopeFlat at h
    split at h
    · cases h
    split at h
    · cases h
    split at h
    · cases h
    split at h
    · cases h
    · next hb =>
      cases h
      simp only [badAddr, Bool.or_eq_true, not_or] at hb
      exact ⟨by simpa using hb.1.2, by simpa using hb.2⟩
  obtain ⟨hseg, hlive, -⟩ := flushS_seg _ _ _ _ _ hfl
  have hp : p ∈ allocsOf (flushSeg s.rest) :=
    (hlive p (by rw [← hl₁]; exact hb.2)).resolve_left (by rw [hb.1]; simp)
  refine ⟨flushSeg s.rest ++ [.emit], ?_, by
    rw [allocsOf_append]
    exact List.mem_append_left _ hp⟩
  rw [List.append_assoc, List.singleton_append, ← hr₁]
  exact hseg

mutual
/-- **The value of a frame address of a block is made by an event the block's walk passes.** -/
theorem scopeBlock_made (rc : ℕ) : ∀ (ss : List Stmt) (s s' : SSt), scopeBlock rc ss s = .ok s' →
    ∀ p run, Atom.frameAddr p run ∈ atomsIn ss →
      ∃ pre, s.rest = pre ++ s'.rest ∧ p ∈ allocsOf pre
  | [], _, _, _, _, _, hm => by simp [atomsIn] at hm
  | st :: rest, s, s', h, p, run, hm => by
    simp only [scopeBlock] at h
    split at h
    · cases h
    · next s₁ h₁ =>
      rw [atomsIn, List.mem_append] at hm
      rcases hm with hm | hm
      · exact made_trans ⟨[], rfl⟩ (scopeStmt_made rc st s s₁ h₁ p run hm)
          (Cons.suf (scopeBlock_cons rc rest s₁ s' h))
      · exact made_trans (Cons.suf (scopeStmt_cons rc st s s₁ h₁))
          (scopeBlock_made rc rest s₁ s' h p run hm) ⟨[], rfl⟩

theorem scopeStmt_made (rc : ℕ) : ∀ (st : Stmt) (s s' : SSt), scopeStmt rc st s = .ok s' →
    ∀ p run, Atom.frameAddr p run ∈ atomsOf st →
      ∃ pre, s.rest = pre ++ s'.rest ∧ p ∈ allocsOf pre
  | .ite c z nz, s, s', h, p, run, hm => by
    simp only [scopeStmt] at h
    split at h
    · cases h
    · next s₀ h₀ =>
      split at h
      · cases h
      · split at h
        · cases h
        · next s₁ h₁ =>
          rw [atomsOf, List.mem_append] at hm
          rcases hm with hm | hm
          · obtain ⟨t₁, t₂, t₃, t₄, e₁, e₂, e₃, e₄, rfl⟩ := scopeInner_inv h₁
            have cT := scopeIteTail_cons
              (fun _ _ h' => scopeInner_cons (scopeBlock_cons rc nz) h') h
            exact made_trans
              (Cons.suf ((flushAt_cons (flushEdge_ok h₀).2).trans (expectS_cons noAlloc_enter e₁)))
              (scopeBlock_made rc z t₁ t₂ e₂ p run hm)
              (Cons.suf (((flushAt_cons (flushEdge_ok e₃).2).trans
                (expectS_cons (s' := t₄) noAlloc_leave e₄)).trans cT))
          · have c₁ := (flushAt_cons (flushEdge_ok h₀).2).trans
              (scopeInner_cons (scopeBlock_cons rc z) h₁)
            unfold scopeIteTail at h
            split at h
            · split at h
              · cases h
              · next s₂ h₂ =>
                obtain ⟨t₁, t₂, t₃, t₄, e₁, e₂, e₃, e₄, rfl⟩ := scopeInner_inv h₂
                have cE := expectS_cons (rc := rc) noAlloc_emit h
                have cN := expectS_cons (rc := rc) noAlloc_enter e₁
                exact made_trans (Cons.suf (c₁.trans cN))
                  (scopeBlock_made rc nz t₁ t₂ e₂ p run hm)
                  (Cons.suf (((flushAt_cons (flushEdge_ok e₃).2).trans
                    (expectS_cons (s' := t₄) noAlloc_leave e₄)).trans cE))
            · split at h
              · cases h
              · next hne =>
                cases nz with
                | nil => simp [atomsIn] at hm
                | cons _ _ => simp at hne
  | .match_ x arms, s, s', h, p, run, hm => by
    simp only [scopeStmt] at h
    split at h
    · cases h
    · next s₀ h₀ =>
      split at h
      · cases h
      · split at h
        · cases h
        · next s₁ h₁ =>
          exact made_trans (Cons.suf (flushAt_cons (flushEdge_ok h₀).2))
            (scopeArms_made rc arms s₀ s₀.retDone s₁ h₁ p run hm)
            (Cons.suf (rc := rc) (expectS_cons noAlloc_emit h))
  | .atom a, s, s', h, p, run, hm => by
    simp only [atomsOf, List.mem_singleton] at hm
    subst hm
    exact scopeFlat_made h
  | .call .., _, _, _, _, _, hm => by simp [atomsOf] at hm
  | .callIf .., _, _, _, _, _, hm => by simp [atomsOf] at hm
  | .dispatch .., _, _, _, _, _, hm => by simp [atomsOf] at hm
  | .ret _, _, _, _, _, _, hm => by simp [atomsOf] at hm

theorem scopeArms_made (rc : ℕ) : ∀ (arms : List (List Stmt)) (s : SSt) (acc : Bool) (s' : SSt),
    scopeArms rc arms s acc = .ok s' → ∀ p run, Atom.frameAddr p run ∈ armsAtoms arms →
      ∃ pre, s.rest = pre ++ s'.rest ∧ p ∈ allocsOf pre
  | [], _, _, _, _, _, _, hm => by simp [armsAtoms] at hm
  | arm :: more, s, acc, s', h, p, run, hm => by
    simp only [scopeArms] at h
    split at h
    · cases h
    · next s₁ h₁ =>
      rw [armsAtoms, List.mem_append] at hm
      rcases hm with hm | hm
      · obtain ⟨t₁, t₂, t₃, t₄, e₁, e₂, e₃, e₄, rfl⟩ := scopeInner_inv h₁
        have cA := scopeArms_cons rc more _ _ s' h
        exact made_trans (Cons.suf (rc := rc) (expectS_cons noAlloc_enter e₁))
          (scopeBlock_made rc arm t₁ t₂ e₂ p run hm)
          (Cons.suf (((flushAt_cons (flushEdge_ok e₃).2).trans
            (expectS_cons (s' := t₄) noAlloc_leave e₄)).trans cA))
      · exact made_trans (Cons.suf (scopeInner_cons (scopeBlock_cons rc arm) h₁))
          (scopeArms_made rc more _ _ s' h p run hm) ⟨[], rfl⟩
end

/-- **No frame address of a block is of a value the trace makes after it.** -/
theorem inner_fa_after {rc : ℕ} {z : List Stmt} {sc sc' : SSt}
    (h : scopeInner rc (fun s' => scopeBlock rc z s') sc = .ok sc')
    (hnd : (allocsOf sc.rest).Nodup) :
    ∀ v run, Atom.frameAddr v run ∈ atomsIn z → v ∉ allocsOf sc'.rest := by
  intro v run hm hv
  obtain ⟨t₁, t₂, t₃, t₄, e₁, e₂, e₃, e₄, rfl⟩ := scopeInner_inv h
  obtain ⟨pre, hpre, hp⟩ := made_trans (Cons.suf (rc := rc) (expectS_cons noAlloc_enter e₁))
    (scopeBlock_made rc z t₁ t₂ e₂ v run hm)
    (Cons.suf ((flushAt_cons (flushEdge_ok e₃).2).trans (expectS_cons (s' := t₄) noAlloc_leave e₄)))
  rw [hpre, allocsOf_append] at hnd
  exact List.disjoint_of_nodup_append hnd hp hv

end Made

/-! ## An inner block off the path, proved -/

section Off

variable {ctx : Ctx}

theorem inBlock_lazyOff (z : List Stmt) {st : St} {sc sc' : SSt}
    (hsc : scopeInner ctx.retCells (fun s' => scopeBlock ctx.retCells z s') sc = .ok sc')
    (hr : st.rest = sc.rest) (hf : st.rest.length ≤ ctx.fuel) (hz : st.lazy = none) :
    wpP (inBlock (placeBlock z)) ctx st fun _ st' => st'.lazy = none := by
  obtain ⟨s₁, s₂, s₃, s₄, h₁, h₂, h₃e, h₄, rfl⟩ := scopeInner_inv hsc
  obtain ⟨hlf, -⟩ := flushEdge_ok h₃e
  obtain ⟨ev, hst, -, -, -⟩ := expectS_ok h₁
  have ht : st.rest.tail = s₁.rest := by rw [hr, hst]; rfl
  unfold inBlock
  refine wp_bind.mpr (wp_mono (expect_rest (st := st)) fun _ stA hA => ?_)
  subst hA
  refine wp_bind.mpr (wp_get.mpr (wp_bind.mpr (wp_set.mpr ?_)))
  refine wp_bind.mpr (wp_mono (wp_and (blockRest z _ s₁ s₂ h₂ ht (by
      show st.rest.tail.length ≤ ctx.fuel
      rw [List.length_tail]
      omega)) (placeBlock_lazy z _ hz)) fun _ st₂ ⟨hr₂, hz₂⟩ => ?_)
  refine wp_bind.mpr (wp_mono (flushLazy [] st₂ (by rw [hr₂]; exact hlf)) fun _ st₃ hz₃ => ?_)
  refine wp_bind.mpr (wp_mono (expect_rest (st := st₃)) fun _ st₄ h₄' => ?_)
  subst h₄'
  refine wp_bind.mpr (wp_get.mpr ?_)
  dsimp only
  split
  · refine wp_bind.mpr (wp_mono fresh_eq fun _ st₅ ⟨_, hst₅⟩ => ?_)
    refine wp_bind.mpr (wp_mono emitOp_eq fun _ st₆ hst₆ => ?_)
    exact wp_bind.mpr (wp_get.mpr (wp_bind.mpr (wp_set.mpr (wp_pure.mpr (by
      rw [hst₆, hst₅]
      exact hz₃.trans hz₂)))))
  · exact wp_bind.mpr (wp_get.mpr (wp_bind.mpr (wp_set.mpr (wp_pure.mpr (hz₃.trans hz₂)))))

/-- **An inner block off the path**, from `InBlockFresh`. -/
theorem inBlockOff (hfr : InBlockFresh) (z : List Stmt) : InBlockOff ctx z := by
  intro st sc sc' hsc hr hf
  have hR : wpP (inBlock (placeBlock z)) ctx st fun _ st' => st'.rest = sc'.rest :=
    inBlock_rs (fun s₁ s₂ st h hl => placeBlock_rs z s₁ s₂ st h hl)
      (fun s₁ s₂ h => scopeBlock_cons _ z s₁ s₂ h) hsc (by rw [← hr]; exact hf) hr
  have hC : wpP (inBlock (placeBlock z)) ctx st fun _ st' =>
      st.chainIn = none → st'.chainIn = none := by
    by_cases h : st.chainIn = none
    · exact wp_mono (inBlock_chain (fun st h => wp_mono (placeMono z st) fun _ _ hq =>
        (hq.2.2 h).1) st h) fun _ _ h' _ => h'
    · exact fun _ _ _ h' => absurd h' h
  have hL : wpP (inBlock (placeBlock z)) ctx st fun _ st' => st.lazy = none →
      st'.lazy = none ∧ ((allocsOf st.rest).Nodup →
        ∀ v ∈ allocsOf st'.rest, st.locs[v]? = none → st'.locs[v]? = none) := by
    by_cases hz : st.lazy = none
    · refine wp_mono (wp_and (inBlock_lazyOff z hsc hr hf hz) ?_) fun _ _ ⟨h1, h2⟩ _ => ⟨h1, h2⟩
      by_cases hnd : (allocsOf st.rest).Nodup
      · exact wp_mono (hfr ctx z st sc sc' hsc hr hf hnd hz
          (inner_fa_after hsc (by rw [← hr]; exact hnd))) fun _ _ h _ => h
      · exact fun _ _ _ h => absurd h hnd
    · exact fun _ _ _ h => absurd h hz
  refine wp_mono (wp_and hR (wp_and (inBlock_mono (fun st => placeBlock_mono z st) st)
    (wp_and (inBlock_r (S := FA (atomsIn z)) (fun st => placeBlock_r z st) st) (wp_and hC hL))))
    fun _ st' ⟨h1, ⟨hm, ho, hs⟩, hRR, hc, hl⟩ => ⟨h1, hs, ho, hc, hm.1, hm.2,
      fun hz => ⟨(hl hz).1, fun v hv => ?_, (hl hz).2⟩, hRR.old.2.1, hRR.old.2.2⟩
  rcases hRR.old.1 v hv with h | h | ⟨k, h⟩ | h
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · rw [hz] at h
    cases h
  · exact Or.inr (Or.inr h)

theorem blockFresh_ok : BlockFresh := blockFresh

theorem inBlockFresh_ok : InBlockFresh := inBlockFresh

/-- **An inner block off the path.** -/
theorem inBlockOff_ok (z : List Stmt) : InBlockOff ctx z := inBlockOff inBlockFresh_ok z

end Off

end
end LeanVM.Guest.Backend.Complete
