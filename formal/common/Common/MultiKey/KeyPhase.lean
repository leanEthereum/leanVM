module

public import Common.MultiKey.Cost
public import VCVio.OracleComp.EvalDist.Sum

@[expose] public section

/-!
# Key generation in another order

In the random-oracle model, independent computations commute (`Common.run_bind_bind_comm`). So
the `k` keys of the multi-key game, their seeds sampled first and then generated in key order,
have (with the oracle's cache) the joint distribution of: key `i` first, from its own seed, then
the others, each from its own seed (`keyPhase`). The second order is the one of the game against
the reduction for key `i`.
-/

open OracleComp OracleSpec MeasureTheory
open scoped ENNReal
open HashSig.OverPermutation (sequenceFin)

namespace Common.SufCma.MultiKey

/-! ## Events through a bind -/

/-- Continuations with the same event probability on the support give the same event
probability. -/
theorem prEvent_bind_congr_support {α β γ : Type} (mx : ProbComp α) {f : α → ProbComp β}
    {g : α → ProbComp γ} {p : β → Prop} {q : γ → Prop}
    (h : ∀ a ∈ support mx, Pr{let y ← f a}[p y] = Pr{let y ← g a}[q y]) :
    Pr{let y ← mx >>= f}[p y] = Pr{let y ← mx >>= g}[q y] := by
  rw [prEvent_bind_eq_tsum, prEvent_bind_eq_tsum]
  refine tsum_congr fun a ↦ ?_
  by_cases ha : a ∈ support mx
  · rw [h a ha]
  · rw [prEvent_eq_zero_of_not_mem_support mx ha, zero_mul, zero_mul]

/-! ## Commuting in the random-oracle model -/

theorem romRun_bind_right {α β : Type} (x : OracleComp World α) {f g : α → OracleComp World β}
    (h : ∀ a c, romRun (f a) c =ᵈ romRun (g a) c) (c : SchemeHashSpec.QueryCache) :
    romRun (x >>= f) c =ᵈ romRun (x >>= g) c := by
  rw [romRun_bind, romRun_bind]
  exact EvalDistEq.bind_right _ fun z ↦ h z.1 z.2

theorem romRun_comm {α β δ : Type} (x : OracleComp World α) (y : OracleComp World β)
    (w : α → β → OracleComp World δ) (c : SchemeHashSpec.QueryCache) :
    romRun (x >>= fun a ↦ y >>= fun b ↦ w a b) c =ᵈ romRun (y >>= fun b ↦ x >>= fun a ↦ w a b) c :=
  run_bind_bind_comm (hs := SchemeHashSpec) x y w c

/-- Computations in sequence, mapped one by one, are the sequence mapped. -/
theorem sequenceFin_map {m : Type → Type} [Monad m] [LawfulMonad m] {α β : Type} :
    ∀ {n : ℕ} (f : Fin n → α → β) (c : Fin n → m α),
      sequenceFin (fun j ↦ f j <$> c j) = (fun v j ↦ f j (v j)) <$> sequenceFin c
  | 0, f, c => by
    simp only [sequenceFin, map_pure]
    congr 1
    funext j
    exact j.elim0
  | n + 1, f, c => by
    simp only [sequenceFin, map_bind, bind_map_left, map_pure]
    refine bind_congr fun h ↦ ?_
    rw [sequenceFin_map (fun j ↦ f j.succ) (fun j ↦ c j.succ), bind_map_left]
    refine bind_congr fun t ↦ ?_
    congr 1
    funext j
    refine Fin.cases ?_ (fun j ↦ ?_) j <;> rfl

/-- **Pull the computation at `i` to the front.** -/
theorem romRun_sequenceFin_pull {β δ : Type} :
    ∀ {n : ℕ} (c : Fin n → OracleComp World β) (i : Fin n)
      (W : (Fin n → β) → OracleComp World δ) (s : SchemeHashSpec.QueryCache),
      romRun (sequenceFin c >>= W) s =ᵈ
        romRun (c i >>= fun b ↦ sequenceFin (fun j ↦ if j = i then pure b else c j) >>= W) s
  | 0, _, i, _, _ => i.elim0
  | n + 1, c, i, W, s => by
    refine Fin.cases ?_ (fun i ↦ ?_) i
    · simp only [sequenceFin, bind_assoc, ↓reduceIte, pure_bind, Fin.succ_ne_zero]
      exact EvalDistEq.rfl
    · simp only [sequenceFin, bind_assoc, pure_bind]
      have hne : (0 : Fin (n + 1)) ≠ i.succ := (Fin.succ_ne_zero i).symm
      simp only [hne, ↓reduceIte, Fin.succ_inj]
      refine (romRun_bind_right _ (fun h c' ↦ romRun_sequenceFin_pull (fun j ↦ c j.succ) i
        (fun t ↦ pure (Fin.cases h t) >>= W) c') s).trans ?_
      simp only [pure_bind]
      exact romRun_comm (c 0) (c i.succ) _ s

/-- **Sample all, then generate all, is sample-and-generate one by one.** -/
theorem romRun_sequenceFin_interleave {α β δ : Type} :
    ∀ {n : ℕ} (a : Fin n → OracleComp World α) (b : Fin n → α → OracleComp World β)
      (W : (Fin n → α) → (Fin n → β) → OracleComp World δ) (s : SchemeHashSpec.QueryCache),
      romRun (sequenceFin a >>= fun xs ↦ sequenceFin (fun j ↦ b j (xs j)) >>= W xs) s =ᵈ
        romRun (sequenceFin (fun j ↦ a j >>= fun x ↦ (x, ·) <$> b j x) >>= fun ps ↦
          W (fun j ↦ (ps j).1) (fun j ↦ (ps j).2)) s
  | 0, a, b, W, s => by
    simp only [sequenceFin, pure_bind]
    have h1 : (fun j : Fin 0 ↦ (Fin.elim0 j : α × β).1) = Fin.elim0 := funext fun j ↦ j.elim0
    have h2 : (fun j : Fin 0 ↦ (Fin.elim0 j : α × β).2) = Fin.elim0 := funext fun j ↦ j.elim0
    rw [h1, h2]
  | n + 1, a, b, W, s => by
    simp only [sequenceFin, bind_assoc, pure_bind, bind_map_left]
    refine romRun_bind_right _ (fun x0 c' ↦ ?_) s
    simp only [Fin.cases_zero, Fin.cases_succ]
    have hc := romRun_comm (sequenceFin fun j ↦ a j.succ) (b 0 x0) (fun xs y0 ↦
      sequenceFin (fun j ↦ b j.succ (xs j)) >>= fun ys ↦
        W (Fin.cases x0 xs) (Fin.cases y0 ys)) c'
    refine EvalDistEq.trans hc ?_
    refine romRun_bind_right _ (fun y0 c'' ↦ ?_) c'
    have hi := romRun_sequenceFin_interleave (fun j ↦ a j.succ) (fun j ↦ b j.succ)
      (fun xs ys ↦ W (Fin.cases x0 xs) (Fin.cases y0 ys)) c''
    refine EvalDistEq.trans hi ?_
    have h1 : ∀ ps : Fin n → α × β, (Fin.cases x0 fun j ↦ (ps j).1 : Fin (n + 1) → α) =
        fun j ↦ (Fin.cases (motive := fun _ ↦ α × β) (x0, y0) ps j).1 :=
      fun ps ↦ funext fun j ↦ Fin.cases rfl (fun _ ↦ rfl) j
    have h2 : ∀ ps : Fin n → α × β, (Fin.cases y0 fun j ↦ (ps j).2 : Fin (n + 1) → β) =
        fun j ↦ (Fin.cases (motive := fun _ ↦ α × β) (x0, y0) ps j).2 :=
      fun ps ↦ funext fun j ↦ Fin.cases rfl (fun _ ↦ rfl) j
    simp only [h1, h2]
    exact EvalDistEq.rfl

end Common.SufCma.MultiKey
