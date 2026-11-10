/-
  LeanVM.Prover.Corr

  Two scripts that make the same moves: the relation under which the executable prover's script
  and the specification's honest script give the same proof.
-/

module

public import Statement.Prover.Run
public import LeanVM.Protocol.Whir.Complete.Script
public import LeanVM.Protocol.EndToEnd.Complete.Sumcheck
public import LeanVM.Protocol.WithHash

/-!
# Scripts that make the same moves

`Corr R H₁ H₂`: the scripts `H₁` and `H₂` make the same moves (equal scalars sent, equal matrices
committed, at every position), each challenge and each answer to an opening given to both, and
end in results related by `R`. The run of a script against a program (`runFrom`) sees only the
moves, so two such scripts give the same proof (`runFrom_corr`), in every monad, for every hash
and permutation. `Corr.bind` composes the relation along `bind`, which is how the executable
prover is related to the specification phase by phase.
-/

namespace LeanVM.Prover

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.Compile

@[expose] public section

namespace Script

variable {α β γ : Type}

theorem bind_assoc' (p : Script α) (f : α → Script β) (g : β → Script γ) :
    (p.bind f).bind g = p.bind fun a ↦ (f a).bind g := by
  induction p with
  | ret a => rfl
  | send x k ih => simp only [bind, ih]
  | sample k ih => simp only [bind, ih]
  | grind k ih => simp only [bind, ih]
  | commit w k ih => simp only [bind, ih]
  | query k ih => simp only [bind, ih]

end Script

/-- The statement's round grind is the specification's, for a round of `count` coefficients. -/
theorem roundGrind_eq {count : ℕ} {c : List E} (hc : c.length = count) (mode : Option E) :
    roundGrind mode c = LeanVM.Protocol.EndToEnd.Complete.roundBits count mode := by
  subst hc; rfl

/-- **The scripts make the same moves**, and end in results related by `R`. -/
def Corr {α β : Type} (R : α → β → Prop) : Script α → Script β → Prop
  | .ret a, .ret b => R a b
  | .send x k, .send y k' => x = y ∧ Corr R k k'
  | .sample k, .sample k' => ∀ c, Corr R (k c) (k' c)
  | .grind k, .grind k' => Corr R k k'
  | .commit w k, .commit w' k' => w = w' ∧ Corr R k k'
  | .query k, .query k' => ∀ rows, Corr R (k rows) (k' rows)
  | _, _ => False

namespace Corr

variable {α β γ δ : Type}

/-- A script makes its own moves. -/
theorem refl : ∀ H : Script α, Corr (· = ·) H H
  | .ret _ => rfl
  | .send _ k => ⟨rfl, refl k⟩
  | .sample k => fun c ↦ refl (k c)
  | .grind k => refl k
  | .commit _ k => ⟨rfl, refl k⟩
  | .query k => fun rows ↦ refl (k rows)

/-- A weaker relation on the results. -/
theorem mono {R R' : α → β → Prop} (hR : ∀ a b, R a b → R' a b) :
    ∀ (H₁ : Script α) (H₂ : Script β), Corr R H₁ H₂ → Corr R' H₁ H₂
  | .ret _, .ret _, h => hR _ _ h
  | .send _ k, .send _ k', h => ⟨h.1, mono hR k k' h.2⟩
  | .sample k, .sample k', h => fun c ↦ mono hR (k c) (k' c) (h c)
  | .grind k, .grind k', h => mono hR k k' h
  | .commit _ k, .commit _ k', h => ⟨h.1, mono hR k k' h.2⟩
  | .query k, .query k', h => fun rows ↦ mono hR (k rows) (k' rows) (h rows)
  | .ret _, .send _ _, h | .ret _, .sample _, h | .ret _, .grind _, h | .ret _, .commit _ _, h
  | .ret _, .query _, h | .send _ _, .ret _, h | .send _ _, .sample _, h
  | .send _ _, .grind _, h | .send _ _, .commit _ _, h | .send _ _, .query _, h
  | .sample _, .ret _, h | .sample _, .send _ _, h | .sample _, .grind _, h
  | .sample _, .commit _ _, h | .sample _, .query _, h | .grind _, .ret _, h
  | .grind _, .send _ _, h | .grind _, .sample _, h | .grind _, .commit _ _, h
  | .grind _, .query _, h | .commit _ _, .ret _, h | .commit _ _, .send _ _, h
  | .commit _ _, .sample _, h | .commit _ _, .grind _, h | .commit _ _, .query _, h
  | .query _, .ret _, h | .query _, .send _ _, h | .query _, .sample _, h
  | .query _, .grind _, h | .query _, .commit _ _, h => h.elim

/-- **The relation composes along `bind`.** -/
theorem bind {R : α → β → Prop} {S : γ → δ → Prop} {f : α → Script γ} {g : β → Script δ}
    (hk : ∀ a b, R a b → Corr S (f a) (g b)) :
    ∀ (H₁ : Script α) (H₂ : Script β), Corr R H₁ H₂ → Corr S (H₁.bind f) (H₂.bind g)
  | .ret _, .ret _, h => hk _ _ h
  | .send _ k, .send _ k', h => ⟨h.1, bind hk k k' h.2⟩
  | .sample k, .sample k', h => fun c ↦ bind hk (k c) (k' c) (h c)
  | .grind k, .grind k', h => bind hk k k' h
  | .commit _ k, .commit _ k', h => ⟨h.1, bind hk k k' h.2⟩
  | .query k, .query k', h => fun rows ↦ bind hk (k rows) (k' rows) (h rows)
  | .ret _, .send _ _, h | .ret _, .sample _, h | .ret _, .grind _, h | .ret _, .commit _ _, h
  | .ret _, .query _, h | .send _ _, .ret _, h | .send _ _, .sample _, h
  | .send _ _, .grind _, h | .send _ _, .commit _ _, h | .send _ _, .query _, h
  | .sample _, .ret _, h | .sample _, .send _ _, h | .sample _, .grind _, h
  | .sample _, .commit _ _, h | .sample _, .query _, h | .grind _, .ret _, h
  | .grind _, .send _ _, h | .grind _, .sample _, h | .grind _, .commit _ _, h
  | .grind _, .query _, h | .commit _ _, .ret _, h | .commit _ _, .send _ _, h
  | .commit _ _, .sample _, h | .commit _ _, .grind _, h | .commit _ _, .query _, h
  | .query _, .ret _, h | .query _, .send _ _, h | .query _, .sample _, h
  | .query _, .grind _, h | .query _, .commit _ _, h => h.elim

/-- `bind` in `do` notation. -/
theorem bind' {R : α → β → Prop} {S : γ → δ → Prop} {f : α → Script γ} {g : β → Script δ}
    {H₁ : Script α} {H₂ : Script β} (h : Corr R H₁ H₂)
    (hk : ∀ a b, R a b → Corr S (f a) (g b)) : Corr S (H₁ >>= f) (H₂ >>= g) :=
  bind hk H₁ H₂ h

/-- The same moves, then a script related to the second's continuation. -/
theorem bind_same {S : γ → δ → Prop} {f : α → Script γ} {g : α → Script δ} (H : Script α)
    (hk : ∀ a, Corr S (f a) (g a)) : Corr S (H.bind f) (H.bind g) :=
  bind (R := (· = ·)) (fun a _ h ↦ h ▸ hk a) H H (refl H)

/-- Two results related. -/
theorem ret_ret {R : α → β → Prop} {a : α} {b : β} (h : R a b) :
    Corr R (Script.ret a) (Script.ret b) := h

/-- Equal sends. -/
theorem sendList (xs : List E) : Corr (fun _ _ ↦ True) (Script.sendList xs) (Script.sendList xs) :=
  mono (fun _ _ _ ↦ trivial) _ _ (refl _)

end Corr

/-! ## The run sees only the moves -/

/-- The relation on the run's script states: both absent, or both present and related. -/
def OCorr {α β : Type} (R : α → β → Prop) : Option (Script α) → Option (Script β) → Prop
  | none, none => True
  | some H₁, some H₂ => Corr R H₁ H₂
  | _, _ => False

section Run

variable {α β : Type} {R : α → β → Prop}

theorem OCorr.msgOf : ∀ {S₁ : Option (Script α)} {S₂ : Option (Script β)}, OCorr R S₁ S₂ →
    Script.msgOf S₁ = Script.msgOf S₂
  | none, none, _ => rfl
  | some (.send _ _), some (.send _ _), h => h.1
  | some (.ret _), some (.ret _), _ | some (.sample _), some (.sample _), _
  | some (.grind _), some (.grind _), _ | some (.commit _ _), some (.commit _ _), _
  | some (.query _), some (.query _), _ => rfl
  | some (.ret _), some (.send _ _), h | some (.ret _), some (.sample _), h
  | some (.ret _), some (.grind _), h | some (.ret _), some (.commit _ _), h
  | some (.ret _), some (.query _), h | some (.send _ _), some (.ret _), h
  | some (.send _ _), some (.sample _), h | some (.send _ _), some (.grind _), h
  | some (.send _ _), some (.commit _ _), h | some (.send _ _), some (.query _), h
  | some (.sample _), some (.ret _), h | some (.sample _), some (.send _ _), h
  | some (.sample _), some (.grind _), h | some (.sample _), some (.commit _ _), h
  | some (.sample _), some (.query _), h | some (.grind _), some (.ret _), h
  | some (.grind _), some (.send _ _), h | some (.grind _), some (.sample _), h
  | some (.grind _), some (.commit _ _), h | some (.grind _), some (.query _), h
  | some (.commit _ _), some (.ret _), h | some (.commit _ _), some (.send _ _), h
  | some (.commit _ _), some (.sample _), h | some (.commit _ _), some (.grind _), h
  | some (.commit _ _), some (.query _), h | some (.query _), some (.ret _), h
  | some (.query _), some (.send _ _), h | some (.query _), some (.sample _), h
  | some (.query _), some (.grind _), h | some (.query _), some (.commit _ _), h
  | none, some _, h | some _, none, h => h.elim

theorem OCorr.wordOf : ∀ {S₁ : Option (Script α)} {S₂ : Option (Script β)}, OCorr R S₁ S₂ →
    Script.wordOf S₁ = Script.wordOf S₂
  | none, none, _ => rfl
  | some (.commit _ _), some (.commit _ _), h => h.1
  | some (.ret _), some (.ret _), _ | some (.sample _), some (.sample _), _
  | some (.grind _), some (.grind _), _ | some (.send _ _), some (.send _ _), _
  | some (.query _), some (.query _), _ => rfl
  | some (.ret _), some (.send _ _), h | some (.ret _), some (.sample _), h
  | some (.ret _), some (.grind _), h | some (.ret _), some (.commit _ _), h
  | some (.ret _), some (.query _), h | some (.send _ _), some (.ret _), h
  | some (.send _ _), some (.sample _), h | some (.send _ _), some (.grind _), h
  | some (.send _ _), some (.commit _ _), h | some (.send _ _), some (.query _), h
  | some (.sample _), some (.ret _), h | some (.sample _), some (.send _ _), h
  | some (.sample _), some (.grind _), h | some (.sample _), some (.commit _ _), h
  | some (.sample _), some (.query _), h | some (.grind _), some (.ret _), h
  | some (.grind _), some (.send _ _), h | some (.grind _), some (.sample _), h
  | some (.grind _), some (.commit _ _), h | some (.grind _), some (.query _), h
  | some (.commit _ _), some (.ret _), h | some (.commit _ _), some (.send _ _), h
  | some (.commit _ _), some (.sample _), h | some (.commit _ _), some (.grind _), h
  | some (.commit _ _), some (.query _), h | some (.query _), some (.ret _), h
  | some (.query _), some (.send _ _), h | some (.query _), some (.sample _), h
  | some (.query _), some (.grind _), h | some (.query _), some (.commit _ _), h
  | none, some _, h | some _, none, h => h.elim

/-- The script states stay related after any move: a matching move steps both, a mismatched one
ends both. -/
theorem OCorr.after {S₁ : Option (Script α)} {S₂ : Option (Script β)} (h : OCorr R S₁ S₂) :
    OCorr R (Script.afterSend S₁) (Script.afterSend S₂) ∧
    (∀ c, OCorr R (Script.afterSample c S₁) (Script.afterSample c S₂)) ∧
    OCorr R (Script.afterGrind S₁) (Script.afterGrind S₂) ∧
    OCorr R (Script.afterCommit S₁) (Script.afterCommit S₂) ∧
    (∀ rows, OCorr R (Script.afterQuery rows S₁) (Script.afterQuery rows S₂)) := by
  rcases S₁ with _ | H₁ <;> rcases S₂ with _ | H₂
  · exact ⟨trivial, fun _ ↦ trivial, trivial, trivial, fun _ ↦ trivial⟩
  · exact h.elim
  · exact h.elim
  · cases H₁ <;> cases H₂ <;> simp only [OCorr, Corr] at h <;>
      first
      | simp only [Script.afterSend, Script.afterSample, Script.afterGrind, Script.afterCommit,
          Script.afterQuery, OCorr]
        first
        | exact ⟨h.2, fun _ ↦ trivial, trivial, trivial, fun _ ↦ trivial⟩
        | exact ⟨trivial, h, trivial, trivial, fun _ ↦ trivial⟩
        | exact ⟨trivial, fun _ ↦ trivial, h, trivial, fun _ ↦ trivial⟩
        | exact ⟨trivial, fun _ ↦ trivial, trivial, h.2, fun _ ↦ trivial⟩
        | exact ⟨trivial, fun _ ↦ trivial, trivial, trivial, h⟩
        | exact ⟨trivial, fun _ ↦ trivial, trivial, trivial, fun _ ↦ trivial⟩

variable {m : Type → Type} [Monad m] (H : Bytes → m Digest) (F : KeccakState → m KeccakState)

/-- **The run sees only the moves**: related script states give the same proof. -/
theorem runFrom_ocorr (fuel : ℕ) {γ : Type} :
    ∀ (P : VerifierProgram γ) (S₁ : Option (Script α)) (S₂ : Option (Script β)) (sp : Sponge)
      (cs : List Tree), OCorr R S₁ S₂ →
      runFromWithHash H F fuel P S₁ sp cs = runFromWithHash H F fuel P S₂ sp cs := by
  intro P
  induction P with
  | ret a => intros; rfl
  | fail => intros; rfl
  | read k ih =>
    intro S₁ S₂ sp cs h
    simp only [runFromWithHash, h.msgOf]
    congr 1; funext sp'; congr 1
    exact ih _ _ _ _ _ h.after.1
  | sample k ih =>
    intro S₁ S₂ sp cs h
    simp only [runFromWithHash]
    congr 1; funext r
    exact ih _ _ _ _ _ (h.after.2.1 r.1)
  | grind b k ih =>
    intro S₁ S₂ sp cs h
    simp only [runFromWithHash]
    congr 1; funext o
    rcases o with _ | n
    · rfl
    · simp only
      congr 1; funext r; congr 1
      exact ih _ _ _ _ h.after.2.2.1
  | commit ht w k ih =>
    intro S₁ S₂ sp cs h
    simp only [runFromWithHash, h.wordOf]
    congr 1; funext tree; congr 1; funext sp0; congr 1; funext sp1; congr 1
    exact ih _ _ _ _ h.after.2.2.2.1
  | query i ps k ih =>
    intro S₁ S₂ sp cs h
    simp only [runFromWithHash]
    split
    · rfl
    · congr 1
      exact ih _ _ _ _ _ (h.after.2.2.2.2 _)

/-- **Scripts that make the same moves give the same proof.** -/
theorem runFrom_corr (fuel : ℕ) {γ : Type} (P : VerifierProgram γ) {H₁ : Script α} {H₂ : Script β}
    (h : Corr R H₁ H₂) (sp : Sponge) (cs : List Tree) :
    runFromWithHash H F fuel P (some H₁) sp cs = runFromWithHash H F fuel P (some H₂) sp cs :=
  runFrom_ocorr H F fuel P _ _ sp cs h

/-- **Scripts that make the same moves give the same proof**, from a seed. -/
theorem runScript_corr (fuel : ℕ) (P : VerifierProgram Bool) {H₁ : Script α} {H₂ : Script β}
    (h : Corr R H₁ H₂) (seed : KeccakState) :
    runScriptWithHash H F P H₁ seed fuel = runScriptWithHash H F P H₂ seed fuel := by
  simp only [runScriptWithHash, runFrom_corr H F fuel P h]

end Run

end
end LeanVM.Prover
