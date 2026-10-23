/-
  LeanVM.Protocol.Compile.SpecRules.Bind

  The structural rules of the specification calculus: consequence, sequencing (`Spec.bind`),
  and case splits on values.
-/

module

public import LeanVM.Protocol.Compile.SpecRules.Basic

/-!
# Structural rules for specifications

* `Spec.mono`: strengthen the precondition, weaken the postcondition, raise `εmax` and the
  lead, lower the follower's allowance.
* `Spec.bind`: from `S : Spec p Pre Post εmax Lp Lf` and `F : ∀ a, Spec (f a) (Post a) Q εmax
  Lf T`, a specification `Spec (p.bind f) Pre Q εmax Lp T`. Its doom (`Spec.bindD`) and potential
  (`Spec.bindV`) are `p`'s strictly inside `p`; at a return of `p` at `l₁` the doom is `p`'s and
  `f a`'s start's, the potential `f a`'s start's in `p`'s doom and `1` outside it; after the
  return, `f a`'s. The potential at a return in doom is at most `Lf` (`f`'s lead) and so at most
  `p`'s (`retDoom` of `S`), which is what makes `p`'s supermartingale and bound carry over.
* `Spec.bind'`: the same for `p >>= f`; `Spec.ite`, `Spec.congr`: case splits; `Spec.dead`: any
  program from an unsatisfiable precondition.
-/

namespace LeanVM.Protocol.Compile

open LeanVM.Parameters Prog

@[expose] public section

variable {α β : Type}

/-- The average of a function into `[0, 1]` over the challenges is at most `1`. -/
theorem avg_le_one (g : E → ENNReal) (hg : ∀ c, g c ≤ 1) :
    (Fintype.card E : ENNReal)⁻¹ * ∑ c : E, g c ≤ 1 := by
  calc (Fintype.card E : ENNReal)⁻¹ * ∑ c : E, g c
      ≤ (Fintype.card E : ENNReal)⁻¹ * ∑ _c : E, (1 : ENNReal) := by gcongr with c; exact hg c
    _ = 1 := by
      rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
      exact ENNReal.inv_mul_cancel (by simp) (by simp)

namespace Prog

/-- A local run of `p.bind f` is strictly inside `p`, at `p`'s node followed by `f`, or at or
after a return of `p`, in a run of `f a`. -/
theorem reach_bind_pos {p : Prog α} {f : α → Prog β} {h₀ l : List Ev}
    (hl : (p.bind f).Reach h₀ l) :
    (p.retSplit l = none ∧ p.Reach h₀ l ∧ ∃ q, p.after l = some q ∧ (∀ a, q ≠ ret a) ∧
        (p.bind f).after l = some (q.bind f)) ∨
      ∃ a l₁ l₂, p.retSplit l = some (a, l₁, l₂) ∧ l = l₁ ++ l₂ ∧ p.Reach h₀ l₁ ∧
        p.after l₁ = some (ret a) ∧ (f a).Reach (h₀ ++ l₁) l₂ ∧
        (p.bind f).after l = (f a).after l₂ := by
  rcases hs : p.retSplit l with _ | ⟨a, l₁, l₂⟩
  · have hr := reach_of_reach_bind hl hs
    obtain ⟨q, hq⟩ := hr.after_isSome
    refine .inl ⟨rfl, hr, q, hq, fun a h ↦ after_ne_ret_of_retSplit_eq_none hs a (h ▸ hq), ?_⟩
    rw [after_bind_of_retSplit_eq_none f p l hs, hq]
    rfl
  · obtain ⟨h1, h2⟩ := reach_of_reach_bind_of_retSplit hl hs
    obtain ⟨he, ha⟩ := retSplit_eq_some_iff.1 hs
    exact .inr ⟨a, l₁, l₂, rfl, he, h1, ha, h2, after_bind_of_retSplit_eq_some f hs⟩

/-- `p` at a return is found by `retSplit` there. -/
theorem retSplit_self {p : Prog α} {l : List Ev} {a : α} (h : p.after l = some (ret a)) :
    p.retSplit l = some (a, l, []) := by
  simpa using retSplit_of_after p l [] h

end Prog

namespace Spec

variable {p : Prog α} {Pre Pre' : List Ev → Prop} {Post Post' : α → List Ev → Prop}
  {εmax εmax' L L' T T' : ENNReal}

/-! ## Consequence -/

/-- **Consequence**: a stronger precondition, a weaker postcondition, a larger `εmax` and lead,
a smaller follower's allowance. -/
def mono (S : Spec p Pre Post εmax L T) (hPre : ∀ h, Pre' h → Pre h)
    (hPost : ∀ a h, Post a h → Post' a h) (hε : εmax ≤ εmax') (hL : L ≤ L') (hT : T' ≤ T) :
    Spec p Pre' Post' εmax' L' T' where
  D := S.D
  V := S.V
  le_one := S.le_one
  start_D h hp := S.start_D h (hPre h hp)
  start_V h hp := (S.start_V h (hPre h hp)).trans hL
  read := S.read
  grind := S.grind
  commit := S.commit
  sample := S.sample
  query := S.query
  moveEnd := S.moveEnd
  retEnd := S.retEnd
  retDoom hl ha hD := le_trans (min_le_min_left 1 hT) (S.retDoom hl ha hD)
  post hl ha hD := hPost _ _ (S.post hl ha hD)
  bound hl hne hm hD := (S.bound hl hne hm hD).trans hε

@[simp] theorem mono_D (S : Spec p Pre Post εmax L T) (hPre : ∀ h, Pre' h → Pre h)
    (hPost : ∀ a h, Post a h → Post' a h) (hε : εmax ≤ εmax') (hL : L ≤ L') (hT : T' ≤ T) :
    (S.mono hPre hPost hε hL hT).D = S.D := rfl

@[simp] theorem mono_V (S : Spec p Pre Post εmax L T) (hPre : ∀ h, Pre' h → Pre h)
    (hPost : ∀ a h, Post a h → Post' a h) (hε : εmax ≤ εmax') (hL : L ≤ L') (hT : T' ≤ T) :
    (S.mono hPre hPost hε hL hT).V = S.V := rfl

/-- **A dead branch**: any program from an unsatisfiable precondition, with any lead (doom never
holds and the potential is `1`). -/
def dead : Spec p (fun _ ↦ False) Post εmax L T where
  D _ _ := False
  V _ _ := 1
  le_one _ _ := le_rfl
  start_D _ h := h
  start_V _ h := h.elim
  read := by intros; contradiction
  grind := by intros; contradiction
  commit := by intros; contradiction
  sample := by intros; exact avg_le_one _ fun _ ↦ le_rfl
  query := by intros; exact le_rfl
  moveEnd := by intros; exact le_rfl
  retEnd := by intros; exact le_rfl
  retDoom := by intros; contradiction
  post := by intros; contradiction
  bound := by intros; contradiction

/-- Transport along an equality of programs (for a `match` or a definitional unfolding). -/
def congr {p' : Prog α} (h : p = p') (S : Spec p Pre Post εmax L T) :
    Spec p' Pre Post εmax L T := h ▸ S

/-- **Case split** on a decidable proposition. -/
def ite {c : Prop} [Decidable c] {p₁ p₂ : Prog α} (S₁ : c → Spec p₁ Pre Post εmax L T)
    (S₂ : ¬ c → Spec p₂ Pre Post εmax L T) : Spec (if c then p₁ else p₂) Pre Post εmax L T :=
  if h : c then (S₁ h).congr (by simp [h]) else (S₂ h).congr (by simp [h])

/-! ## Sequencing -/

section Bind

variable {f : α → Prog β} {Q : β → List Ev → Prop} {Lp Lf : ENNReal}
  (S : Spec p Pre Post εmax Lp Lf) (F : ∀ a, Spec (f a) (Post a) Q εmax Lf T)

/-- Doom of `p.bind f`: `p`'s strictly inside `p`; at a return of `p`, `p`'s and the start doom
of `f a`; after it, `f a`'s. -/
def bindD (h₀ l : List Ev) : Prop :=
  match p.retSplit l with
  | none => S.D h₀ l
  | some (a, l₁, l₂) => (l₂ = [] → S.D h₀ l₁) ∧ (F a).D (h₀ ++ l₁) l₂

open Classical in
/-- The potential of `p.bind f`: `p`'s strictly inside `p`; at a return of `p`, the start
potential of `f a` in `p`'s doom and `1` outside it; after it, `f a`'s. -/
noncomputable def bindV (h₀ l : List Ev) : ENNReal :=
  match p.retSplit l with
  | none => S.V h₀ l
  | some (a, l₁, l₂) => if l₂ = [] ∧ ¬ S.D h₀ l₁ then 1 else (F a).V (h₀ ++ l₁) l₂

variable {S F}

theorem bindD_none {h₀ l : List Ev} (hs : p.retSplit l = none) :
    bindD S F h₀ l ↔ S.D h₀ l := by
  unfold bindD; rw [hs]

theorem bindD_some {h₀ l : List Ev} {a : α} {l₁ l₂ : List Ev}
    (hs : p.retSplit l = some (a, l₁, l₂)) :
    bindD S F h₀ l ↔ (l₂ = [] → S.D h₀ l₁) ∧ (F a).D (h₀ ++ l₁) l₂ := by
  unfold bindD; rw [hs]

theorem bindV_none {h₀ l : List Ev} (hs : p.retSplit l = none) :
    bindV S F h₀ l = S.V h₀ l := by
  unfold bindV; rw [hs]

open Classical in
theorem bindV_some {h₀ l : List Ev} {a : α} {l₁ l₂ : List Ev}
    (hs : p.retSplit l = some (a, l₁, l₂)) :
    bindV S F h₀ l = if l₂ = [] ∧ ¬ S.D h₀ l₁ then 1 else (F a).V (h₀ ++ l₁) l₂ := by
  unfold bindV; rw [hs]

theorem bindD_after {h₀ l : List Ev} {a : α} {l₁ l₂ : List Ev}
    (hs : p.retSplit l = some (a, l₁, l₂)) (hne : l₂ ≠ []) :
    bindD S F h₀ l ↔ (F a).D (h₀ ++ l₁) l₂ := by
  rw [bindD_some hs]; simp [hne]

theorem bindV_after {h₀ l : List Ev} {a : α} {l₁ l₂ : List Ev}
    (hs : p.retSplit l = some (a, l₁, l₂)) (hne : l₂ ≠ []) :
    bindV S F h₀ l = (F a).V (h₀ ++ l₁) l₂ := by
  rw [bindV_some hs]; simp [hne]

/-- At a return of `p` in doom, `f a` starts in doom with a potential at most `p`'s. -/
theorem ret_doom {h₀ l₁ : List Ev} {a : α} (hp : p.Reach h₀ l₁)
    (ha : p.after l₁ = some (ret a)) (hD : S.D h₀ l₁) :
    (F a).D (h₀ ++ l₁) [] ∧ (F a).V (h₀ ++ l₁) [] ≤ S.V h₀ l₁ := by
  have hpost := S.post hp ha hD
  exact ⟨(F a).start_D _ hpost,
    le_trans (le_min ((F a).le_one _ _) ((F a).start_V _ hpost)) (S.retDoom hp ha hD)⟩

/-- At a return of `p`, the potential of the composite is at most `p`'s. -/
theorem bindV_le_at_ret {h₀ l₁ : List Ev} {a : α} (hp : p.Reach h₀ l₁)
    (ha : p.after l₁ = some (ret a)) : bindV S F h₀ l₁ ≤ S.V h₀ l₁ := by
  rw [bindV_some (retSplit_self ha)]
  by_cases hD : S.D h₀ l₁
  · simpa [hD] using (ret_doom hp ha hD).2
  · simpa [hD] using S.retEnd hp ha hD

/-- At a return of `p` in doom, the composite is in doom. -/
theorem bindD_at_ret {h₀ l₁ : List Ev} {a : α} (hp : p.Reach h₀ l₁)
    (ha : p.after l₁ = some (ret a)) (hD : S.D h₀ l₁) : bindD S F h₀ l₁ :=
  (bindD_some (retSplit_self ha)).2 ⟨fun _ ↦ hD, (ret_doom hp ha hD).1⟩

/-- One event past a history strictly inside `p`: the composite's potential is at most `p`'s. -/
theorem bindV_le_child {h₀ l : List Ev} {e : Ev} (hs : p.retSplit l = none)
    (hp : p.Reach h₀ (l ++ [e])) : bindV S F h₀ (l ++ [e]) ≤ S.V h₀ (l ++ [e]) := by
  rcases hs' : p.retSplit (l ++ [e]) with _ | ⟨a, l₁, l₂⟩
  · rw [bindV_none hs']
  · obtain ⟨rfl, rfl⟩ := retSplit_concat hs hs'
    exact bindV_le_at_ret hp (by simpa using (retSplit_eq_some_iff.1 hs').2)

/-- One event past a history strictly inside `p`: `p`'s doom gives the composite's. -/
theorem bindD_child {h₀ l : List Ev} {e : Ev} (hs : p.retSplit l = none)
    (hp : p.Reach h₀ (l ++ [e])) (hD : S.D h₀ (l ++ [e])) : bindD S F h₀ (l ++ [e]) := by
  rcases hs' : p.retSplit (l ++ [e]) with _ | ⟨a, l₁, l₂⟩
  · exact (bindD_none hs').2 hD
  · obtain ⟨rfl, rfl⟩ := retSplit_concat hs hs'
    exact bindD_at_ret hp (by simpa using (retSplit_eq_some_iff.1 hs').2) hD

/-- A prover move keeps the composite's doom, given that it keeps `p`'s and `f a`'s. -/
theorem bindD_keep {h₀ l : List Ev} (e : Ev) (hl : (p.bind f).Reach h₀ l) (hD : bindD S F h₀ l)
    (hp : ∀ q, p.Reach h₀ l → p.after l = some q → (∀ a, q ≠ ret a) →
      (p.bind f).after l = some (q.bind f) → S.D h₀ l →
        p.Reach h₀ (l ++ [e]) ∧ S.D h₀ (l ++ [e]))
    (hf : ∀ a l₁ l₂, (f a).Reach (h₀ ++ l₁) l₂ → (f a).after l₂ = (p.bind f).after l →
      (F a).D (h₀ ++ l₁) l₂ → (F a).D (h₀ ++ l₁) (l₂ ++ [e])) :
    bindD S F h₀ (l ++ [e]) := by
  rcases reach_bind_pos hl with ⟨hs, hr, q, hq, hnr, hb⟩ | ⟨a, l₁, l₂, hs, -, -, -, h2, hb⟩
  · obtain ⟨hr', hD'⟩ := hp q hr hq hnr hb ((bindD_none hs).1 hD)
    exact bindD_child hs hr' hD'
  · rw [bindD_after (retSplit_append [e] hs) (by simp)]
    exact hf a l₁ l₂ h2 hb.symm ((bindD_some hs).1 hD).2

/-- Outside the composite's doom past a return of `p`: the potential is `1`, or `f a`'s outside
`f a`'s doom. -/
theorem bindV_of_not_bindD {h₀ l : List Ev} {a : α} {l₁ l₂ : List Ev}
    (hs : p.retSplit l = some (a, l₁, l₂)) (hD : ¬ bindD S F h₀ l) :
    1 ≤ bindV S F h₀ l ∨ (bindV S F h₀ l = (F a).V (h₀ ++ l₁) l₂ ∧ ¬ (F a).D (h₀ ++ l₁) l₂) := by
  rw [bindD_some hs] at hD
  rw [bindV_some hs]
  by_cases hc : l₂ = [] ∧ ¬ S.D h₀ l₁
  · exact .inl (by simp [hc])
  · refine .inr ⟨by simp [hc], fun hF ↦ hD ⟨fun h ↦ ?_, hF⟩⟩
    by_contra hn
    exact hc ⟨h, hn⟩

/-- In the composite's doom past a return of `p`, the potential is `f a`'s. -/
theorem bindV_of_bindD {h₀ l : List Ev} {a : α} {l₁ l₂ : List Ev}
    (hs : p.retSplit l = some (a, l₁, l₂)) (hD : bindD S F h₀ l) :
    bindV S F h₀ l = (F a).V (h₀ ++ l₁) l₂ ∧ (F a).D (h₀ ++ l₁) l₂ := by
  rw [bindD_some hs] at hD
  rw [bindV_some hs]
  refine ⟨?_, hD.2⟩
  have : ¬ (l₂ = [] ∧ ¬ S.D h₀ l₁) := fun ⟨h1, h2⟩ ↦ h2 (hD.1 h1)
  simp only [this, ite_false]

variable (S F)

/-- **Sequencing.** `p` specified with the follower's allowance `Lf`, `f a` from `Post a` with
lead `Lf`, give `p.bind f` from `Pre` with `p`'s lead. -/
noncomputable def bind : Spec (p.bind f) Pre Q εmax Lp T where
  D := bindD S F
  V := bindV S F
  le_one h₀ l := by
    unfold bindV
    split
    · exact S.le_one _ _
    · split_ifs
      · exact le_rfl
      · exact (F _).le_one _ _
  start_D h₀ hPre := by
    rcases hs : p.retSplit [] with _ | ⟨a, l₁, l₂⟩
    · exact (bindD_none hs).2 (S.start_D h₀ hPre)
    · obtain ⟨he, ha⟩ := retSplit_eq_some_iff.1 hs
      obtain ⟨rfl, rfl⟩ := List.append_eq_nil_iff.1 he.symm
      exact bindD_at_ret .nil ha (S.start_D h₀ hPre)
  start_V h₀ hPre := by
    rcases hs : p.retSplit [] with _ | ⟨a, l₁, l₂⟩
    · rw [bindV_none hs]; exact S.start_V h₀ hPre
    · obtain ⟨he, ha⟩ := retSplit_eq_some_iff.1 hs
      obtain ⟨rfl, rfl⟩ := List.append_eq_nil_iff.1 he.symm
      exact (bindV_le_at_ret .nil ha).trans (S.start_V h₀ hPre)
  read := by
    intro h₀ l k x hl ha hD
    refine bindD_keep _ hl hD (fun q hr hq hnr hb hD ↦ ?_)
      (fun a _ _ hr he hD ↦ (F a).read x hr (he.trans ha) hD)
    rw [ha] at hb
    cases q with
    | ret a => exact absurd rfl (hnr a)
    | read k' => exact ⟨.read x hr hq, S.read x hr hq hD⟩
    | _ => simp [Prog.bind] at hb
  grind := by
    intro h₀ l b k hl ha hD
    refine bindD_keep _ hl hD (fun q hr hq hnr hb hD ↦ ?_)
      (fun a _ _ hr he hD ↦ (F a).grind hr (he.trans ha) hD)
    rw [ha] at hb
    cases q with
    | ret a => exact absurd rfl (hnr a)
    | grind b' k' =>
      simp only [Prog.bind, Option.some.injEq, Prog.grind.injEq] at hb
      obtain ⟨rfl, -⟩ := hb
      exact ⟨.grind hr hq, S.grind hr hq hD⟩
    | _ => simp [Prog.bind] at hb
  commit := by
    intro h₀ l ht w k word hl ha hw hD
    refine bindD_keep _ hl hD (fun q hr hq hnr hb hD ↦ ?_)
      (fun a _ _ hr he hD ↦ (F a).commit word hr (he.trans ha) hw hD)
    rw [ha] at hb
    cases q with
    | ret a => exact absurd rfl (hnr a)
    | commit ht' w' k' =>
      simp only [Prog.bind, Option.some.injEq, Prog.commit.injEq] at hb
      obtain ⟨rfl, rfl, -⟩ := hb
      exact ⟨.commit word hr hq hw, S.commit word hr hq hw hD⟩
    | _ => simp [Prog.bind] at hb
  sample := by
    intro h₀ l k hl ha
    rcases reach_bind_pos hl with ⟨hs, hr, q, hq, hnr, hb⟩ | ⟨a, l₁, l₂, hs, -, -, -, h2, hb⟩
    · rw [ha] at hb
      cases q with
      | ret a => exact absurd rfl (hnr a)
      | sample k' =>
        rw [bindV_none hs]
        calc (Fintype.card E : ENNReal)⁻¹ * ∑ c : E, bindV S F h₀ (l ++ [Ev.sample c])
            ≤ (Fintype.card E : ENNReal)⁻¹ * ∑ c : E, S.V h₀ (l ++ [Ev.sample c]) := by
              gcongr with c
              exact bindV_le_child hs (.sample c hr hq)
          _ ≤ S.V h₀ l := S.sample hr hq
      | _ => simp [Prog.bind] at hb
    · have hfa : (f a).after l₂ = some (.sample k) := hb.symm.trans ha
      have hc : ∀ c, bindV S F h₀ (l ++ [Ev.sample c]) = (F a).V (h₀ ++ l₁) (l₂ ++ [Ev.sample c]) :=
        fun c ↦ bindV_after (retSplit_append [Ev.sample c] hs) (by simp)
      simp only [hc]
      rw [bindV_some hs]
      split_ifs
      · exact avg_le_one _ fun c ↦ (F a).le_one _ _
      · exact (F a).sample h2 hfa
  query := by
    intro h₀ l i ps k rows hl ha hans
    rcases reach_bind_pos hl with ⟨hs, hr, q, hq, hnr, hb⟩ | ⟨a, l₁, l₂, hs, he, -, -, h2, hb⟩
    · rw [ha] at hb
      cases q with
      | ret a => exact absurd rfl (hnr a)
      | query i' ps' k' =>
        simp only [Prog.bind, Option.some.injEq, Prog.query.injEq] at hb
        obtain ⟨rfl, rfl, -⟩ := hb
        rw [bindV_none hs]
        exact (bindV_le_child hs (.query hr hq hans)).trans (S.query hr hq hans)
      | _ => simp [Prog.bind] at hb
    · have hfa : (f a).after l₂ = some (.query i ps k) := hb.symm.trans ha
      rw [bindV_after (retSplit_append [Ev.query rows] hs) (by simp), bindV_some hs]
      split_ifs
      · exact (F a).le_one _ _
      · exact (F a).query h2 hfa (by rw [List.append_assoc, ← he]; exact hans)
  moveEnd := by
    intro h₀ l q' hl ha hm hD
    rcases reach_bind_pos hl with ⟨hs, hr, q, hq, hnr, hb⟩ | ⟨a, l₁, l₂, hs, -, -, -, h2, hb⟩
    · rw [ha, Option.some.injEq] at hb
      subst hb
      rw [bindV_none hs]
      exact S.moveEnd hr hq ((bind_isMove hnr).1 hm) (fun h ↦ hD ((bindD_none hs).2 h))
    · rcases bindV_of_not_bindD hs hD with h | ⟨h, hn⟩
      · exact h
      · rw [h]; exact (F a).moveEnd h2 (hb.symm.trans ha) hm hn
  retEnd := by
    intro h₀ l b hl ha hD
    rcases reach_bind_pos hl with ⟨hs, hr, q, hq, hnr, hb⟩ | ⟨a, l₁, l₂, hs, -, -, -, h2, hb⟩
    · rw [ha] at hb
      cases q with
      | ret a => exact absurd rfl (hnr a)
      | _ => simp [Prog.bind] at hb
    · rcases bindV_of_not_bindD hs hD with h | ⟨h, hn⟩
      · exact h
      · rw [h]; exact (F a).retEnd h2 (hb.symm.trans ha) hn
  retDoom := by
    intro h₀ l b hl ha hD
    rcases reach_bind_pos hl with ⟨hs, hr, q, hq, hnr, hb⟩ | ⟨a, l₁, l₂, hs, -, -, -, h2, hb⟩
    · rw [ha] at hb
      cases q with
      | ret a => exact absurd rfl (hnr a)
      | _ => simp [Prog.bind] at hb
    · obtain ⟨h, hF⟩ := bindV_of_bindD hs hD
      rw [h]; exact (F a).retDoom h2 (hb.symm.trans ha) hF
  post := by
    intro h₀ l b hl ha hD
    rcases reach_bind_pos hl with ⟨hs, hr, q, hq, hnr, hb⟩ | ⟨a, l₁, l₂, hs, he, -, -, h2, hb⟩
    · rw [ha] at hb
      cases q with
      | ret a => exact absurd rfl (hnr a)
      | _ => simp [Prog.bind] at hb
    · have := (F a).post h2 (hb.symm.trans ha) (bindV_of_bindD hs hD).2
      rwa [List.append_assoc, ← he] at this
  bound := by
    intro h₀ l hl hne hm hD
    rcases reach_bind_pos hl with ⟨hs, hr, -, -, -, -⟩ | ⟨a, l₁, l₂, hs, he, h1, ha1, h2, hb⟩
    · rw [bindV_none hs]
      exact S.bound hr hne hm ((bindD_none hs).1 hD)
    · obtain ⟨hV, hF⟩ := bindV_of_bindD hs hD
      rw [hV]
      by_cases h₂ : l₂ = []
      · subst h₂
        simp only [List.append_nil] at he
        subst he
        have hD₁ := ((bindD_some hs).1 hD).1 rfl
        exact le_trans (by gcongr; exact (ret_doom h1 ha1 hD₁).2) (S.bound h1 hne hm hD₁)
      · subst he
        rw [grindBits_append h₂]
        exact (F a).bound h2 h₂ ((endsMove_append h₂).1 hm) hF

/-- The doom of a sequence. -/
theorem bind_D : (S.bind F).D = bindD S F := rfl

/-- The potential of a sequence. -/
theorem bind_V : (S.bind F).V = bindV S F := rfl

/-- **Sequencing** in `do`-notation. -/
noncomputable def bind' : Spec (p >>= f) Pre Q εmax Lp T := S.bind F

end Bind

end Spec

end
end LeanVM.Protocol.Compile
