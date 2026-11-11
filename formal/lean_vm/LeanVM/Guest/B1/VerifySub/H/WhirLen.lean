/-
  LeanVM.Guest.B1.VerifySub.H.WhirLen

  `open_stacked` on an honest child: the opening's terminal point has the stack's log of
  coordinates, and the callee is complete within its candidate's bound.
-/

module

public import LeanVM.Guest.B1.VerifySub.H.KidsB
public import LeanVM.Protocol.Verifier.DeferredShape
public import LeanVM.Protocol.Verifier.WhirTarget

/-!
# The opening

`always_whirOpen`: every end `whirOpen μ r target` returns has a point of `μ` coordinates: each
fold round draws one `α` (`always_foldRounds`), the levels glue without drawing any
(`glueLevel_alphas`), the final sumcheck draws the rest, and the ladder's folds leave the final
level a variable (`ladder_sum_lt`). `ChildSegs.w_point_length`: the honest opening's.
`ChildSegs.os_kidB`: `open_stacked`'s candidate, within `osBosAt`, from its placed completeness
(`open_stacked_completeAtB_Spec`).
-/

namespace LeanVM.Guest.B1.VerifySub

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Node LeanVM.Guest.Memory

@[expose] public section

/-- Every value a run of `p` may return satisfies `P`. -/
def AlwaysR {α : Type} (p : VerifierProgram α) (P : α → Prop) : Prop :=
  ∀ a, VerifierProgram.Returns p a → P a

theorem AlwaysR.bind {α β : Type} {p : VerifierProgram α} {f : α → VerifierProgram β}
    {Q : α → Prop} {P : β → Prop} (hf : ∀ a, Q a → AlwaysR (f a) P) (hp : AlwaysR p Q) :
    AlwaysR (p.bind f) P := fun b h ↦ by
  obtain ⟨a, ha, hb⟩ := VerifierProgram.returns_bind (f := f) h
  exact hf a (hp a ha) b hb

theorem alwaysR_true {α : Type} (p : VerifierProgram α) : AlwaysR p fun _ ↦ True :=
  fun _ _ ↦ trivial

theorem alwaysR_ret {α : Type} {a : α} {P : α → Prop} (h : P a) :
    AlwaysR (VerifierProgram.ret a) P := fun b hb ↦ by
  rw [VerifierProgram.returns_ret hb]; exact h

theorem alwaysR_fail {α : Type} {P : α → Prop} : AlwaysR (VerifierProgram.fail : VerifierProgram α) P :=
  fun _ h ↦ by cases h

theorem always_bind_all {α β : Type} {p : VerifierProgram α} {f : α → VerifierProgram β}
    {P : β → Prop} (h : ∀ a, AlwaysR (f a) P) : AlwaysR (p.bind f) P :=
  AlwaysR.bind (fun a _ ↦ h a) (alwaysR_true p)

theorem alwaysR_sumcheck (count : ℕ) : ∀ (eqs : List (Option E)) (claim : E),
    AlwaysR (sumcheck claim count eqs) fun r ↦ r.1.length = eqs.length
  | [], _ => alwaysR_ret rfl
  | e :: eqs, claim => by
    unfold sumcheck
    try simp only [VerifierProgram.bind_eq]
    refine always_bind_all fun msg ↦ always_bind_all fun ch ↦ ?_
    refine AlwaysR.bind (fun r hr ↦ ?_) (alwaysR_sumcheck count eqs _)
    obtain ⟨pt, fin⟩ := r
    exact alwaysR_ret (by simp only [List.length_cons] at hr ⊢; omega)

theorem always_foldRound (s : WhirState) :
    AlwaysR (foldRound s) fun r ↦ r.1.alphas.length = s.alphas.length + 1 := by
  unfold foldRound
  try simp only [VerifierProgram.bind_eq]
  repeat refine always_bind_all fun _ ↦ ?_
  exact alwaysR_ret (by simp)

theorem always_foldRounds : ∀ (n : ℕ) (s : WhirState),
    AlwaysR (foldRounds n s) fun r ↦ r.1.alphas.length = s.alphas.length + n
  | 0, s => alwaysR_ret rfl
  | n + 1, s => by
    unfold foldRounds
    try simp only [VerifierProgram.bind_eq]
    refine AlwaysR.bind (fun r hr ↦ ?_) (always_foldRound s)
    obtain ⟨s1, round⟩ := r
    refine AlwaysR.bind (fun r' hr' ↦ ?_) (always_foldRounds n s1)
    obtain ⟨s2, rounds⟩ := r'
    exact alwaysR_ret (by simp only at hr hr' ⊢; omega)

theorem foldl_alphas {X : Type} (f : WhirState → X → WhirState)
    (hf : ∀ s x, (f s x).alphas = s.alphas) :
    ∀ (l : List X) (s : WhirState), (l.foldl f s).alphas = s.alphas
  | [], _ => rfl
  | x :: l, s => (foldl_alphas f hf l (f s x)).trans (hf s x)

theorem glueLevel_alphas (s : WhirState) (lam : E) (mu : ℕ) (ps : List (List E)) (vs : List E)
    (qs : List ℕ) (ws : List E) (b : E) : (glueLevel s lam mu ps vs qs ws b).alphas = s.alphas := by
  unfold glueLevel
  dsimp only
  exact foldl_alphas _ (fun s x ↦ by obtain ⟨⟨_, _⟩, _⟩ := x; rfl) _ _

theorem length_rot (l : List E) (k : ℕ) : (l.drop k ++ l.take k).length = l.length := by
  simp only [List.length_append, List.length_drop, List.length_take]
  omega

/-- **The levels' end has a point of `logN` coordinates**, when the folds leave a variable. -/
theorem alwaysR_whirLevelsOpen (logN lf : ℕ) : ∀ (levels : List Whir.Level) (index : ℕ)
    (s : WhirState), s.alphas.length + (levels.map (·.fold)).sum ≤ logN →
      AlwaysR (B1.Whir.whirLevelsOpen logN lf index levels s) fun w ↦ w.point.length = logN
  | [], _, _, _ => alwaysR_fail
  | level :: rest, index, s, hle => by
    unfold B1.Whir.whirLevelsOpen
    try simp only [VerifierProgram.bind_eq]
    refine AlwaysR.bind (fun r hr ↦ ?_) (always_foldRounds level.fold s)
    obtain ⟨s1, rounds⟩ := r
    simp only at hr
    simp only [List.map_cons, List.sum_cons] at hle
    cases rest with
    | nil =>
      dsimp only
      refine always_bind_all fun _ ↦ always_bind_all fun _ ↦ always_bind_all fun _ ↦
        always_bind_all fun _ ↦ always_bind_all fun _ ↦ ?_
      refine AlwaysR.bind (fun t ht ↦ ?_) (alwaysR_sumcheck 3 _ s1.claim)
      obtain ⟨tail, claim⟩ := t
      simp only [List.length_replicate] at ht
      refine alwaysR_ret ?_
      show List.length (List.drop _ _ ++ List.take _ _) = logN
      rw [length_rot, List.length_append, ht]
      simp only [List.map_nil, List.sum_nil] at hle
      omega
    | cons next rest' =>
      dsimp only
      refine always_bind_all fun _ ↦ always_bind_all fun _ ↦ always_bind_all fun _ ↦
        always_bind_all fun _ ↦ always_bind_all fun _ ↦ always_bind_all fun _ ↦
        always_bind_all fun _ ↦ always_bind_all fun _ ↦ always_bind_all fun _ ↦ ?_
      refine alwaysR_whirLevelsOpen logN lf (next :: rest') _ _ ?_
      rw [glueLevel_alphas, hr]
      omega

/-- **Every end of `whirOpen μ r target` has a point of `μ` coordinates.** -/
theorem always_whirOpen (μ r : ℕ) (target : E) :
    AlwaysR (B1.Whir.whirOpen μ r target) fun w ↦ w.point.length = μ := by
  unfold B1.Whir.whirOpen
  try simp only [VerifierProgram.bind_eq]
  cases hl : Whir.ladder μ r with
  | none => exact alwaysR_fail
  | some levels =>
    exact alwaysR_whirLevelsOpen μ _ levels 0 _ (by
      have := ladder_sum_lt hl
      show 0 + _ ≤ μ
      omega)

/-- **A run with openings returns one of the values.** -/
theorem RunsWith.always {α : Type} {p : VerifierProgram α} {s s' : Fs} {xs : List E}
    {os : List (List Opening)} {roots roots' : List (Digest × ℕ × ℕ)} {a : α} {P : α → Prop}
    (h : B1.Whir.RunsWith p s xs os roots a s' roots') {sp : Sponge} (hs : s.Carries sp)
    (hp : AlwaysR p P) : P a := by
  obtain ⟨_, -, e⟩ := h sp hs [] []
  exact hp a (VerifierProgram.returns_of_run keccak256 keccakF1600 e)

namespace ChildSegs

variable {bytecode : List K} {seed : Digest} {c : Child} (S : ChildSegs bytecode seed c)

/-- **The honest opening's terminal point has the stack's log of coordinates.** -/
theorem w_point_length : S.w.point.length = S.μs :=
  RunsWith.always (P := fun w ↦ w.point.length = S.μs) S.runW (sp := ⟨S.s7.perm, [], none⟩) ⟨rfl, rfl, rfl⟩
    (always_whirOpen _ _ _)

variable {fs : String → ℕ} {cert : String → V → ℕ}

/-- **`open_stacked` on an honest child**, as `verify_sub` calls it, within its candidate's
bound. -/
theorem os_kidB (hos : open_stacked_completeAtB_Spec) {κ : ℕ} (hκ : 11 ≤ κ)
    (hrf : Lift.RunsFit fs cert) (hcons : RunsConsec cert) (W : VsWordsOs fs) (bs : List ℕ)
    (sqE : ℕ) :
    CompleteAtB fs cert κ (B1.Whir.openName S.μs S.rate) [(S.cW bs, S.xsW), (sqE, expTabAllWords)]
      (capOf S.s7.perm ++ [S.target, (digestHalves S.root).1, (digestHalves S.root).2,
        ptr (S.cW bs), ptr sqE * gen ^ winTabAt]) (vsOsOut S.μs S.w)
      (osBosAt fs W.Bnd W.Kr S.μs S.rate) :=
  hos S.μs S.rate S.hmu22 S.hmu28 S.hr1 S.hr4 fs cert κ W.Bnd W.Kr hrf hcons hκ W.hleaf
    (W.hloop _ _ S.hmu22 S.hmu28 S.hr1 S.hr4) S.s7.perm S.root S.target (ptr (S.cW bs))
    (ptr sqE * gen ^ winTabAt) S.xsW c.proof.openings S.w S.s' S.roots' S.runW S.nzW
    S.capsW _ fun _ _ hL ↦ ⟨hL _ List.mem_cons_self, winTabs_vsExp fun q hq ↦ hL q (by
      simp only [vsExpLin, List.mem_singleton] at hq
      simp [hq])⟩

end ChildSegs

end
end LeanVM.Guest.B1.VerifySub
