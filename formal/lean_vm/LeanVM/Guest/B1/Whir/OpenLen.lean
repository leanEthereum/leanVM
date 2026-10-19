/-
  LeanVM.Guest.B1.Whir.OpenLen

  The stacked opening's terminal point has one coordinate per variable of the stack.
-/

module

public import LeanVM.Guest.B1.Whir.StackedInv

/-!
# The length of the terminal point

`whirOpen_point_length`: a run of `whirOpen μ r target` at a deployed candidate ends at a point of
`μ` coordinates: every level's folds, then the tail's `logN - folds` rounds, rotated.
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Protocol LeanVM.Protocol.Blake2sHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Guest.B1.VerifySub

@[expose] public section

theorem os_foldRounds_len : ∀ (n : ℕ) (w : WhirState) (lf : List E) (s : St) (res : WhirState × List E) (s' : St),
    Runs (foldRounds n w lf) s res s' → res.1.folds.length = w.folds.length + n
  | 0, w, lf, s, res, s', h => by
    obtain ⟨rfl, -⟩ := os_inv_pure h
    rfl
  | n + 1, w, lf, s, res, s', h => by
    simp only [foldRounds] at h
    obtain ⟨ch, s1, -, h2⟩ := os_inv_bind h
    obtain ⟨q, s2, -, h4⟩ := os_inv_bind h2
    have := os_foldRounds_len n _ _ _ _ _ h4
    simp only [List.length_append, List.length_singleton] at this
    omega

theorem os_tailRounds_len : ∀ (n : ℕ) (t : E) (q : List E) (s : St) (res : List E × E) (s' : St),
    Runs (tailRounds n t q) s res s' → res.1.length = n
  | 0, t, q, s, res, s', h => by
    obtain ⟨rfl, -⟩ := os_inv_pure h
    rfl
  | n + 1, t, q, s, res, s', h => by
    simp only [tailRounds] at h
    obtain ⟨ch, s1, -, h2⟩ := os_inv_bind h
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp only [↓reduceIte] at h2
      obtain ⟨rfl, -⟩ := os_inv_pure h2
      rfl
    · rw [ite_neg' (by omega)] at h2
      obtain ⟨q', s2, -, h4⟩ := os_inv_bind h2
      obtain ⟨⟨rest, t'⟩, s3, h5, h6⟩ := os_inv_bind h4
      obtain ⟨rfl, -⟩ := os_inv_pure h6
      have := os_tailRounds_len n _ _ _ _ _ h5
      simp [this]

theorem os_foldl_inv {α β : Type} (f : β → α → β) (P : β → Prop) (hf : ∀ b a, P b → P (f b a)) :
    ∀ (l : List α) (b : β), P b → P (l.foldl f b)
  | [], _, h => h
  | a :: l, b, h => os_foldl_inv f P hf l (f b a) (hf b a h)

theorem os_glue_folds (lam : E) (s : WhirState) (pending : List (E × List E × (List E → E))) :
    (glue lam s pending).folds = s.folds := by
  unfold glue
  exact os_foldl_inv _ (fun b : WhirState × E => b.1.folds = s.folds) (fun b a hb => by
    obtain ⟨v, i, wa⟩ := a; exact hb) pending (s, 1) rfl

theorem os_levelQueries_folds {ml idx : ℕ} {L : Whir.Level} {lf : List E} {w : WhirState}
    {pending : List (E × List E × (List E → E))} {s s' : St} {w' : WhirState}
    (h : Runs (osLevelQueries ml idx L lf w pending) s w' s') : w'.folds = w.folds := by
  simp only [osLevelQueries] at h
  obtain ⟨_, _, -, h1⟩ := os_inv_bind h
  obtain ⟨_, _, -, h2⟩ := os_inv_bind h1
  obtain ⟨_, _, -, h3⟩ := os_inv_bind h2
  obtain ⟨_, _, -, h4⟩ := os_inv_bind h3
  obtain ⟨_, _, -, h5⟩ := os_inv_bind h4
  obtain ⟨rfl, -⟩ := os_inv_pure h5
  exact os_glue_folds _ _ _

theorem os_rotate_length (l : List E) (k : ℕ) : (l.drop k ++ l.take k).length = l.length := by
  simp only [List.length_append, List.length_drop, List.length_take]; omega

theorem os_whirLevelsOpen_len (logN lane : ℕ) : ∀ (levels : List Whir.Level) (idx : ℕ) (w : WhirState) (s : St)
    (e : WhirEnd) (s' : St), Runs (whirLevelsOpen logN lane idx levels w) s e s' →
    (levels.map (·.fold)).sum + w.folds.length ≤ logN → e.point.length = logN
  | [], _, _, _, _, _, h, _ => by cases h
  | L :: rest, idx, w, s, e, s', h, hle => by
    rw [os_whirLevelsOpen_cons] at h
    obtain ⟨⟨w1, lf⟩, s1, h1, h2⟩ := os_inv_bind h
    have hl1 := os_foldRounds_len _ _ _ _ _ _ h1
    simp only at hl1
    obtain ⟨⟨res, pending⟩, s2, -, h3⟩ := os_inv_bind h2
    obtain ⟨w2, s3, h4, h5⟩ := os_inv_bind h3
    have hf2 := os_levelQueries_folds h4
    simp only [List.map_cons, List.sum_cons] at hle
    match rest, h5 with
    | [], h5 =>
      simp only [osTailOpen] at h5
      obtain ⟨⟨tf, tgt⟩, s4, h6, h7⟩ := os_inv_bind h5
      obtain ⟨rfl, -⟩ := os_inv_pure h7
      have := os_tailRounds_len _ _ _ _ _ _ h6
      simp only at this
      rw [os_rotate_length, List.length_append, this, hf2, hl1]
      simp only [List.map_nil, List.sum_nil] at hle
      omega
    | _ :: _, h5 =>
      refine os_whirLevelsOpen_len logN lane _ _ _ _ _ _ h5 ?_
      rw [hf2, hl1]; omega

/-- The candidates' fold counts stay within the stack's variables. -/
def osFoldSumOk (μ r : ℕ) : Bool :=
  match deriveConfig μ r with
  | some c => decide ((c.map (·.fold)).sum ≤ μ)
  | none => true

theorem osFoldSumOk_window : ∀ μ < 29, 22 ≤ μ → ∀ r < 5, 1 ≤ r → osFoldSumOk μ r = true := by
  decide +kernel

/-- **The terminal point has `μ` coordinates**: a run of the stacked opening at a deployed
candidate ends at a point of length `μ`. -/
theorem whirOpen_point_length {μ r : ℕ} (hμ1 : 22 ≤ μ) (hμ2 : μ ≤ 28) (hr1 : 1 ≤ r) (hr2 : r ≤ 4)
    {target : E} {cv cv' : Digest} {xs : List E} {os : List Opening} {roots roots' : List (Digest × ℕ × ℕ)}
    {w : WhirEnd} (h : RunsWith (whirOpen μ r target) cv xs os roots w cv' roots') : w.point.length = μ := by
  have hr := h.runs [] []
  simp only [whirOpen] at hr
  obtain ⟨cfg, s1, h1, h2⟩ := os_inv_bind hr
  have hok := osFoldSumOk_window μ (by omega) hμ1 r (by omega) hr1
  unfold osFoldSumOk at hok
  revert h1
  cases hd : deriveConfig μ r with
  | none => intro h1; cases h1
  | some c =>
    intro h1
    rw [hd] at hok
    simp only [Verifier.liftOption] at h1
    obtain ⟨rfl, rfl⟩ := os_inv_ret h1
    obtain ⟨q, s2, -, h3⟩ := os_inv_bind h2
    exact os_whirLevelsOpen_len μ _ _ _ _ _ _ _ h3 (by simpa using hok)

end
end LeanVM.Guest.B1
