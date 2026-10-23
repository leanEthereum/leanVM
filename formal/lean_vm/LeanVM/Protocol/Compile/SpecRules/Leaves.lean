/-
  LeanVM.Protocol.Compile.SpecRules.Leaves

  The leaves of the specification calculus: a return, a rejection, a scalar read, a challenge,
  a proof of work, a commitment, an opening, a `require`, and a joint bound for a sub-program
  with no prover move.
-/

module

public import LeanVM.Protocol.Compile.SpecRules.Bind

/-!
# Leaf specifications

Each leaf is a specification `Spec p Pre Post εmax L T` whose lead `L` already contains the
follower's allowance `T` wherever `p` returns within the group:

| leaf | lead | side condition |
| --- | --- | --- |
| `Spec.ret a` | `T` | |
| `Spec.fail` | `0` | |
| `Spec.readE`, `Spec.commitP` | `0` | `T ≤ εmax` (the boundary after the move) |
| `Spec.grindP b` | `0` | `2⁻¹ ^ b * T ≤ εmax` (the proof of work discounts the follower) |
| `Spec.sampleE e` | `e + T` | at most a fraction `e` of the challenges break `Post` |
| `Spec.queryP` | `T` | `Post` holds of the rows the words give |
| `Spec.require` | `T` | |
| `Spec.ofNoMove` | `e + T` | no prover move, `escRet ≤ e < 1` |

`Prog.escRet Post h₀ l q` is the probability, over the remaining challenges, that the program
returns a value breaking `Post`; it is the expectation `Prog.retExp` of the indicator of a bad
return.
-/

namespace LeanVM.Protocol.Compile

open LeanVM.Parameters Prog

@[expose] public section

variable {α : Type}

/-! ## Expectations over the remaining challenges -/

namespace Prog

/-- The expectation of `g` at the return, over the challenges up to the first prover move:
`g a h` at a return of `a` after the whole history `h`, `0` at a rejection, a prover move, or an
opening of a missing commitment. -/
noncomputable def retExp (g : α → List Ev → ENNReal) (h₀ : List Ev) : List Ev → Prog α → ENNReal
  | l, sample k => (Fintype.card E : ENNReal)⁻¹ * ∑ c : E, retExp g h₀ (l ++ [Ev.sample c]) (k c)
  | l, query i ps k => match answer (h₀ ++ l) i ps with
    | some rows => retExp g h₀ (l ++ [Ev.query rows]) (k rows)
    | none => 0
  | l, ret a => g a (h₀ ++ l)
  | _, _ => 0

open Classical in
/-- The probability, over the remaining challenges, of a return breaking `Post`. -/
noncomputable def escRet (Post : α → List Ev → Prop) (h₀ : List Ev) (l : List Ev) (q : Prog α) :
    ENNReal :=
  retExp (fun a h ↦ if Post a h then 0 else 1) h₀ l q

/-- An expectation of a function into `[0, 1]` is at most `1`. -/
theorem retExp_le_one {g : α → List Ev → ENNReal} (hg : ∀ a h, g a h ≤ 1) (h₀ : List Ev) :
    ∀ (q : Prog α) (l : List Ev), retExp g h₀ l q ≤ 1
  | ret a, l => by simpa [retExp] using hg a _
  | fail, l => by simp [retExp]
  | read k, l => by simp [retExp]
  | grind b k, l => by simp [retExp]
  | commit ht w k, l => by simp [retExp]
  | sample k, l => by
    simp only [retExp]
    exact avg_le_one _ fun c ↦ retExp_le_one hg h₀ (k c) _
  | query i ps k, l => by
    simp only [retExp]
    split
    · exact retExp_le_one hg h₀ _ _
    · exact zero_le_one

/-- The average of a function plus a constant. -/
theorem avg_add_const (g : E → ENNReal) (T : ENNReal) :
    (Fintype.card E : ENNReal)⁻¹ * ∑ c : E, (g c + T) =
      (Fintype.card E : ENNReal)⁻¹ * ∑ c : E, g c + T := by
  rw [Finset.sum_add_distrib, mul_add, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
    ← mul_assoc, ENNReal.inv_mul_cancel (by simp) (by simp), one_mul]

/-- An expectation of `g ≤ g' + T` is at most that of `g'` plus `T`. -/
theorem retExp_le_add {g g' : α → List Ev → ENNReal} {T : ENNReal}
    (hg : ∀ a h, g a h ≤ g' a h + T) (h₀ : List Ev) :
    ∀ (q : Prog α) (l : List Ev), retExp g h₀ l q ≤ retExp g' h₀ l q + T
  | ret a, l => by simpa [retExp] using hg a _
  | fail, l => by simp [retExp]
  | read k, l => by simp [retExp]
  | grind b k, l => by simp [retExp]
  | commit ht w k, l => by simp [retExp]
  | sample k, l => by
    simp only [retExp]
    rw [← avg_add_const]
    gcongr with c
    exact retExp_le_add hg h₀ (k c) _
  | query i ps k, l => by
    simp only [retExp]
    split
    · exact retExp_le_add hg h₀ _ _
    · simp

end Prog

namespace Spec

variable {Pre : List Ev → Prop} {Post : α → List Ev → Prop} {εmax T : ENNReal}

/-! ## Return and rejection -/

private theorem reach_ret {a : α} {h₀ l : List Ev} (hl : (ret a).Reach h₀ l) : l = [] := by
  induction hl with
  | nil => rfl
  | read _ _ ha ih | sample _ _ ha ih | grind _ ha ih | commit _ _ ha _ ih | query _ ha _ ih =>
    subst ih; simp [after] at ha

private theorem reach_fail {h₀ l : List Ev} (hl : (fail : Prog α).Reach h₀ l) : l = [] := by
  induction hl with
  | nil => rfl
  | read _ _ ha ih | sample _ _ ha ih | grind _ ha ih | commit _ _ ha _ ih | query _ ha _ ih =>
    subst ih; simp [after] at ha

open Classical in
/-- **Return**: the postcondition must hold at the start; the lead is the follower's. -/
noncomputable def ret (a : α) : Spec (Prog.ret a) (Post a) Post εmax T T where
  D h₀ _ := Post a h₀
  V h₀ _ := if Post a h₀ then min 1 T else 1
  le_one _ _ := by split_ifs <;> simp
  start_D _ h := h
  start_V _ h := by simp [h]
  read := by intro _ _ _ _ hl ha; obtain rfl := reach_ret hl; simp [after] at ha
  grind := by intro _ _ _ _ hl ha; obtain rfl := reach_ret hl; simp [after] at ha
  commit := by intro _ _ _ _ _ _ hl ha; obtain rfl := reach_ret hl; simp [after] at ha
  sample := by intro _ _ _ hl ha; obtain rfl := reach_ret hl; simp [after] at ha
  query := by intro _ _ _ _ _ _ hl ha; obtain rfl := reach_ret hl; simp [after] at ha
  moveEnd := by
    intro _ _ _ hl ha hm; obtain rfl := reach_ret hl
    simp only [after, Option.some.injEq] at ha; subst ha; simp [IsMove] at hm
  retEnd := by intro _ _ _ _ _ hD; simp [hD]
  retDoom := by intro _ _ _ _ _ hD; simp [hD]
  post := by
    intro _ _ _ hl ha hD; obtain rfl := reach_ret hl
    simp only [after, Option.some.injEq, Prog.ret.injEq] at ha; subst ha; simpa using hD
  bound := by intro _ _ hl hne; exact absurd (reach_ret hl) hne

/-- **Rejection**: anything, with lead `0`. -/
def fail : Spec (Prog.fail : Prog α) Pre Post εmax 0 T where
  D _ _ := True
  V _ _ := 0
  le_one _ _ := zero_le_one
  start_D _ _ := trivial
  start_V _ _ := le_rfl
  read := by intros; trivial
  grind := by intros; trivial
  commit := by intros; trivial
  sample := by intro _ _ _ hl ha; obtain rfl := reach_fail hl; simp [after] at ha
  query := by intro _ _ _ _ _ _ hl ha; obtain rfl := reach_fail hl; simp [after] at ha
  moveEnd := by intro _ _ _ _ _ _ hD; exact absurd trivial hD
  retEnd := by intro _ _ _ _ _ hD; exact absurd trivial hD
  retDoom := by intro _ _ _ hl ha; obtain rfl := reach_fail hl; simp [after] at ha
  post := by intro _ _ _ hl ha; obtain rfl := reach_fail hl; simp [after] at ha
  bound := by intro _ _ hl hne; exact absurd (reach_fail hl) hne

/-! ## Prover moves -/

private theorem reach_readE {h₀ l : List Ev} (hl : readE.Reach h₀ l) :
    l = [] ∨ ∃ x, l = [Ev.read x] := by
  induction hl with
  | nil => exact .inl rfl
  | read x _ ha ih =>
    rcases ih with rfl | ⟨y, rfl⟩
    · exact .inr ⟨x, rfl⟩
    · simp [readE, after] at ha
  | sample _ _ ha ih | grind _ ha ih | commit _ _ ha _ ih | query _ ha _ ih =>
    rcases ih with rfl | ⟨y, rfl⟩ <;> simp [readE, after] at ha

open Classical in
/-- **Read** a scalar: `Post` after every scalar; the boundary after the read carries the
follower's lead. -/
noncomputable def readE {Post : E → List Ev → Prop}
    (h : ∀ h₀ x, Pre h₀ → Post x (h₀ ++ [Ev.read x])) (hT : T ≤ εmax) :
    Spec Prog.readE Pre Post εmax 0 T where
  D h₀ l := match l with
    | [] => Pre h₀
    | [Ev.read x] => Post x (h₀ ++ [Ev.read x])
    | _ => True
  V h₀ l := match l with
    | [] => if Pre h₀ then 0 else 1
    | [Ev.read x] => if Post x (h₀ ++ [Ev.read x]) then min 1 T else 1
    | _ => 1
  le_one h₀ l := by
    split
    · split_ifs <;> simp
    · split_ifs <;> simp
    · exact le_rfl
  start_D _ h := h
  start_V _ h := by simp [h]
  read := by
    intro h₀ l k x hl ha hD
    rcases reach_readE hl with rfl | ⟨y, rfl⟩
    · exact h h₀ x hD
    · simp [Prog.readE, after] at ha
  grind := by
    intro _ _ _ _ hl ha
    rcases reach_readE hl with rfl | ⟨y, rfl⟩ <;> simp [Prog.readE, after] at ha
  commit := by
    intro _ _ _ _ _ _ hl ha
    rcases reach_readE hl with rfl | ⟨y, rfl⟩ <;> simp [Prog.readE, after] at ha
  sample := by
    intro _ _ _ hl ha; rcases reach_readE hl with rfl | ⟨y, rfl⟩ <;> simp [Prog.readE, after] at ha
  query := by
    intro _ _ _ _ _ _ hl ha
    rcases reach_readE hl with rfl | ⟨y, rfl⟩ <;> simp [Prog.readE, after] at ha
  moveEnd := by
    intro h₀ l q hl ha hm hD
    rcases reach_readE hl with rfl | ⟨y, rfl⟩
    · simp [hD]
    · simp only [Prog.readE, after, Option.some.injEq] at ha; subst ha; simp [IsMove] at hm
  retEnd := by
    intro h₀ l a hl ha hD
    rcases reach_readE hl with rfl | ⟨y, rfl⟩
    · simp [Prog.readE, after] at ha
    · simp only at hD ⊢; simp [hD]
  retDoom := by
    intro h₀ l a hl ha hD
    rcases reach_readE hl with rfl | ⟨y, rfl⟩
    · simp [Prog.readE, after] at ha
    · simp only at hD ⊢; simp [hD]
  post := by
    intro h₀ l a hl ha hD
    rcases reach_readE hl with rfl | ⟨y, rfl⟩
    · simp [Prog.readE, after] at ha
    · simp only [Prog.readE, after, Option.some.injEq, Prog.ret.injEq] at ha; subst ha; exact hD
  bound := by
    intro h₀ l hl hne hm hD
    rcases reach_readE hl with rfl | ⟨y, rfl⟩
    · exact absurd rfl hne
    · simp only at hD ⊢
      simp only [hD, ite_true, grindBits, List.getLast?_singleton, pow_zero, one_mul]
      exact (min_le_right _ _).trans hT

private theorem reach_commitP {ht w : ℕ} {h₀ l : List Ev} (hl : (commitP ht w).Reach h₀ l) :
    l = [] ∨ ∃ word, WellShaped w word ∧ l = [Ev.commit ht w word] := by
  induction hl with
  | nil => exact .inl rfl
  | commit word _ ha hw ih =>
    rcases ih with rfl | ⟨y, -, rfl⟩
    · simp only [commitP, after, Option.some.injEq, Prog.commit.injEq] at ha
      obtain ⟨rfl, rfl, -⟩ := ha
      exact .inr ⟨word, hw, rfl⟩
    · simp [commitP, after] at ha
  | read _ _ ha ih | sample _ _ ha ih | grind _ ha ih | query _ ha _ ih =>
    rcases ih with rfl | ⟨y, -, rfl⟩ <;> simp [commitP, after] at ha

open Classical in
/-- **Commit** a matrix: `Post` after every well-shaped word; the boundary after the commitment
carries the follower's lead. -/
noncomputable def commitP {Post : Unit → List Ev → Prop} (ht w : ℕ)
    (h : ∀ h₀ word, Pre h₀ → WellShaped w word → Post () (h₀ ++ [Ev.commit ht w word]))
    (hT : T ≤ εmax) : Spec (Prog.commitP ht w) Pre Post εmax 0 T where
  D h₀ l := match l with
    | [] => Pre h₀
    | [e] => Post () (h₀ ++ [e])
    | _ => True
  V h₀ l := match l with
    | [] => if Pre h₀ then 0 else 1
    | [e] => if Post () (h₀ ++ [e]) then min 1 T else 1
    | _ => 1
  le_one h₀ l := by
    split
    · split_ifs <;> simp
    · split_ifs <;> simp
    · exact le_rfl
  start_D _ h := h
  start_V _ h := by simp [h]
  read := by
    intro _ _ _ _ hl ha
    rcases reach_commitP hl with rfl | ⟨y, -, rfl⟩ <;> simp [Prog.commitP, after] at ha
  grind := by
    intro _ _ _ _ hl ha
    rcases reach_commitP hl with rfl | ⟨y, -, rfl⟩ <;> simp [Prog.commitP, after] at ha
  commit := by
    intro h₀ l ht' w' k word hl ha hw hD
    rcases reach_commitP hl with rfl | ⟨y, -, rfl⟩
    · simp only [Prog.commitP, after, Option.some.injEq, Prog.commit.injEq] at ha
      obtain ⟨rfl, rfl, -⟩ := ha
      exact h h₀ word hD hw
    · simp [Prog.commitP, after] at ha
  sample := by
    intro _ _ _ hl ha
    rcases reach_commitP hl with rfl | ⟨y, -, rfl⟩ <;> simp [Prog.commitP, after] at ha
  query := by
    intro _ _ _ _ _ _ hl ha
    rcases reach_commitP hl with rfl | ⟨y, -, rfl⟩ <;> simp [Prog.commitP, after] at ha
  moveEnd := by
    intro h₀ l q hl ha hm hD
    rcases reach_commitP hl with rfl | ⟨y, -, rfl⟩
    · simp [hD]
    · simp [Prog.commitP, after] at ha; subst ha
      simp [IsMove] at hm
  retEnd := by
    intro h₀ l a hl ha hD
    rcases reach_commitP hl with rfl | ⟨y, -, rfl⟩
    · simp [Prog.commitP, after] at ha
    · simp only at hD ⊢; simp [hD]
  retDoom := by
    intro h₀ l a hl ha hD
    rcases reach_commitP hl with rfl | ⟨y, -, rfl⟩
    · simp [Prog.commitP, after] at ha
    · simp only at hD ⊢; simp [hD]
  post := by
    intro h₀ l a hl ha hD
    rcases reach_commitP hl with rfl | ⟨y, -, rfl⟩
    · simp [Prog.commitP, after] at ha
    · exact hD
  bound := by
    intro h₀ l hl hne hm hD
    rcases reach_commitP hl with rfl | ⟨y, -, rfl⟩
    · exact absurd rfl hne
    · simp only at hD ⊢
      simp only [hD, ite_true, grindBits, List.getLast?_singleton, pow_zero, one_mul]
      exact (min_le_right _ _).trans hT

private theorem reach_grindP {b : ℕ} {h₀ l : List Ev} (hl : (grindP b).Reach h₀ l) :
    l = [] ∨ l = [Ev.grind b] := by
  induction hl with
  | nil => exact .inl rfl
  | grind _ ha ih =>
    rcases ih with rfl | rfl
    · simp only [grindP, after, Option.some.injEq, Prog.grind.injEq] at ha
      obtain ⟨rfl, -⟩ := ha
      exact .inr rfl
    · simp [grindP, after] at ha
  | read _ _ ha ih | sample _ _ ha ih | commit _ _ ha _ ih | query _ ha _ ih =>
    rcases ih with rfl | rfl <;> simp [grindP, after] at ha

open Classical in
/-- **Proof of work** of `b` bits: `Post` after it; the boundary after it carries the follower's
lead discounted by `2⁻¹ ^ b`. -/
noncomputable def grindP {Post : Unit → List Ev → Prop} (b : ℕ)
    (h : ∀ h₀, Pre h₀ → Post () (h₀ ++ [Ev.grind b]))
    (hT : (2 : ENNReal)⁻¹ ^ b * T ≤ εmax) : Spec (Prog.grindP b) Pre Post εmax 0 T where
  D h₀ l := match l with
    | [] => Pre h₀
    | [e] => Post () (h₀ ++ [e])
    | _ => True
  V h₀ l := match l with
    | [] => if Pre h₀ then 0 else 1
    | [e] => if Post () (h₀ ++ [e]) then min 1 T else 1
    | _ => 1
  le_one h₀ l := by
    split
    · split_ifs <;> simp
    · split_ifs <;> simp
    · exact le_rfl
  start_D _ h := h
  start_V _ h := by simp [h]
  read := by
    intro _ _ _ _ hl ha; rcases reach_grindP hl with rfl | rfl <;> simp [Prog.grindP, after] at ha
  grind := by
    intro h₀ l b' k hl ha hD
    rcases reach_grindP hl with rfl | rfl
    · simp only [Prog.grindP, after, Option.some.injEq, Prog.grind.injEq] at ha
      obtain ⟨rfl, -⟩ := ha
      exact h h₀ hD
    · simp [Prog.grindP, after] at ha
  commit := by
    intro _ _ _ _ _ _ hl ha
    rcases reach_grindP hl with rfl | rfl <;> simp [Prog.grindP, after] at ha
  sample := by
    intro _ _ _ hl ha; rcases reach_grindP hl with rfl | rfl <;> simp [Prog.grindP, after] at ha
  query := by
    intro _ _ _ _ _ _ hl ha
    rcases reach_grindP hl with rfl | rfl <;> simp [Prog.grindP, after] at ha
  moveEnd := by
    intro h₀ l q hl ha hm hD
    rcases reach_grindP hl with rfl | rfl
    · simp [hD]
    · simp [Prog.grindP, after] at ha; subst ha; simp [IsMove] at hm
  retEnd := by
    intro h₀ l a hl ha hD
    rcases reach_grindP hl with rfl | rfl
    · simp [Prog.grindP, after] at ha
    · simp only at hD ⊢; simp [hD]
  retDoom := by
    intro h₀ l a hl ha hD
    rcases reach_grindP hl with rfl | rfl
    · simp [Prog.grindP, after] at ha
    · simp only at hD ⊢; simp [hD]
  post := by
    intro h₀ l a hl ha hD
    rcases reach_grindP hl with rfl | rfl
    · simp [Prog.grindP, after] at ha
    · exact hD
  bound := by
    intro h₀ l hl hne hm hD
    rcases reach_grindP hl with rfl | rfl
    · exact absurd rfl hne
    · simp only at hD ⊢
      simp only [hD, ite_true, grindBits, List.getLast?_singleton]
      exact le_trans (by gcongr; exact min_le_right _ _) hT

/-! ## Challenges and openings -/

private theorem reach_sampleE {h₀ l : List Ev} (hl : sampleE.Reach h₀ l) :
    l = [] ∨ ∃ c, l = [Ev.sample c] := by
  induction hl with
  | nil => exact .inl rfl
  | sample c _ ha ih =>
    rcases ih with rfl | ⟨y, rfl⟩
    · exact .inr ⟨c, rfl⟩
    · simp [sampleE, after] at ha
  | read _ _ ha ih | grind _ ha ih | commit _ _ ha _ ih | query _ ha _ ih =>
    rcases ih with rfl | ⟨y, rfl⟩ <;> simp [sampleE, after] at ha

/-- The doom of `Spec.sampleE`. -/
def sampleD (Pre : List Ev → Prop) (Post : E → List Ev → Prop) (h₀ l : List Ev) : Prop :=
  match l with
  | [] => Pre h₀
  | [Ev.sample c] => Post c (h₀ ++ [Ev.sample c])
  | _ => True

open Classical in
/-- The potential of `Spec.sampleE` after the challenge. -/
noncomputable def sampleG (Pre : List Ev → Prop) (Post : E → List Ev → Prop) (T : ENNReal)
    (h₀ l : List Ev) : ENNReal :=
  if sampleD Pre Post h₀ l then min 1 T else 1

theorem sampleG_le_one {Pre : List Ev → Prop} {Post : E → List Ev → Prop} {T : ENNReal}
    (h₀ l : List Ev) : sampleG Pre Post T h₀ l ≤ 1 := by
  unfold sampleG; split_ifs <;> simp

open Classical in
/-- **Sample** a challenge: at most a fraction `e` of the challenges break `Post`; the lead is
`e` plus the follower's. -/
noncomputable def sampleE {Post : E → List Ev → Prop} (e : ENNReal)
    (h : ∀ h₀, Pre h₀ → (Fintype.card E : ENNReal)⁻¹ *
      ((Finset.univ.filter fun c ↦ ¬ Post c (h₀ ++ [Ev.sample c])).card : ENNReal) ≤ e) :
    Spec Prog.sampleE Pre Post εmax (e + T) T where
  D := sampleD Pre Post
  V h₀ l := match l with
    | [] => (Fintype.card E : ENNReal)⁻¹ * ∑ c : E, sampleG Pre Post T h₀ [Ev.sample c]
    | _ => sampleG Pre Post T h₀ l
  le_one h₀ l := by
    split
    · exact avg_le_one _ fun c ↦ sampleG_le_one _ _
    · exact sampleG_le_one _ _
  start_D _ h := h
  start_V h₀ hPre := by
    simp only
    have hg : ∀ c, sampleG Pre Post T h₀ [Ev.sample c] ≤
        (if ¬ Post c (h₀ ++ [Ev.sample c]) then 1 else 0) + T := by
      intro c
      unfold sampleG sampleD
      by_cases hc : Post c (h₀ ++ [Ev.sample c])
      · simp [hc]
      · simp [hc]
    calc (Fintype.card E : ENNReal)⁻¹ * ∑ c : E, sampleG Pre Post T h₀ [Ev.sample c]
        ≤ (Fintype.card E : ENNReal)⁻¹ *
            ∑ c : E, ((if ¬ Post c (h₀ ++ [Ev.sample c]) then 1 else 0) + T) := by
          gcongr with c; exact hg c
      _ = (Fintype.card E : ENNReal)⁻¹ *
            ((Finset.univ.filter fun c ↦ ¬ Post c (h₀ ++ [Ev.sample c])).card : ENNReal) + T := by
          rw [avg_add_const, Finset.sum_boole]
      _ ≤ e + T := by gcongr; exact h h₀ hPre
  read := by
    intro _ _ _ _ hl ha
    rcases reach_sampleE hl with rfl | ⟨y, rfl⟩ <;> simp [Prog.sampleE, after] at ha
  grind := by
    intro _ _ _ _ hl ha
    rcases reach_sampleE hl with rfl | ⟨y, rfl⟩ <;> simp [Prog.sampleE, after] at ha
  commit := by
    intro _ _ _ _ _ _ hl ha
    rcases reach_sampleE hl with rfl | ⟨y, rfl⟩ <;> simp [Prog.sampleE, after] at ha
  sample := by
    intro h₀ l k hl ha
    rcases reach_sampleE hl with rfl | ⟨y, rfl⟩
    · simp
    · simp [Prog.sampleE, after] at ha
  query := by
    intro _ _ _ _ _ _ hl ha
    rcases reach_sampleE hl with rfl | ⟨y, rfl⟩ <;> simp [Prog.sampleE, after] at ha
  moveEnd := by
    intro h₀ l q hl ha hm
    rcases reach_sampleE hl with rfl | ⟨y, rfl⟩
    · simp only [Prog.sampleE, after, Option.some.injEq] at ha; subst ha; simp [IsMove] at hm
    · simp only [Prog.sampleE, after, Option.some.injEq] at ha; subst ha; simp [IsMove] at hm
  retEnd := by
    intro h₀ l a hl ha hD
    rcases reach_sampleE hl with rfl | ⟨y, rfl⟩
    · simp [Prog.sampleE, after] at ha
    · simp [sampleG, hD]
  retDoom := by
    intro h₀ l a hl ha hD
    rcases reach_sampleE hl with rfl | ⟨y, rfl⟩
    · simp [Prog.sampleE, after] at ha
    · simp [sampleG, hD]
  post := by
    intro h₀ l a hl ha hD
    rcases reach_sampleE hl with rfl | ⟨y, rfl⟩
    · simp [Prog.sampleE, after] at ha
    · simp only [Prog.sampleE, after, Option.some.injEq, Prog.ret.injEq] at ha; subst ha; exact hD
  bound := by
    intro h₀ l hl hne hm
    rcases reach_sampleE hl with rfl | ⟨y, rfl⟩
    · exact absurd rfl hne
    · simp [EndsMove] at hm

private theorem reach_queryP {i : ℕ} {ps : List ℕ} {h₀ l : List Ev}
    (hl : (queryP i ps).Reach h₀ l) :
    l = [] ∨ ∃ rows, answer h₀ i ps = some rows ∧ l = [Ev.query rows] := by
  induction hl with
  | nil => exact .inl rfl
  | @query l i' ps' k rows _ ha hans ih =>
    rcases ih with rfl | ⟨y, -, rfl⟩
    · simp only [queryP, after, Option.some.injEq, Prog.query.injEq] at ha
      obtain ⟨rfl, rfl, -⟩ := ha
      exact .inr ⟨rows, by simpa using hans, rfl⟩
    · simp [queryP, after] at ha
  | read _ _ ha ih | sample _ _ ha ih | grind _ ha ih | commit _ _ ha _ ih =>
    rcases ih with rfl | ⟨y, -, rfl⟩ <;> simp [queryP, after] at ha

/-- The doom of `Spec.queryP`. -/
def queryD (Pre : List Ev → Prop) (Post : List (List K) → List Ev → Prop) (h₀ l : List Ev) :
    Prop :=
  match l with
  | [] => Pre h₀
  | [Ev.query rows] => Post rows (h₀ ++ [Ev.query rows])
  | _ => True

open Classical in
/-- **Open** rows of the `i`-th commitment: `Post` of the rows the words give; the lead is the
follower's. -/
noncomputable def queryP {Post : List (List K) → List Ev → Prop} (i : ℕ) (ps : List ℕ)
    (h : ∀ h₀ rows, Pre h₀ → answer h₀ i ps = some rows → Post rows (h₀ ++ [Ev.query rows])) :
    Spec (Prog.queryP i ps) Pre Post εmax T T where
  D := queryD Pre Post
  V h₀ l := if queryD Pre Post h₀ l then min 1 T else 1
  le_one _ _ := by split_ifs <;> simp
  start_D _ h := h
  start_V _ h := by simp [queryD, h]
  read := by
    intro _ _ _ _ hl ha
    rcases reach_queryP hl with rfl | ⟨y, -, rfl⟩ <;> simp [Prog.queryP, after] at ha
  grind := by
    intro _ _ _ _ hl ha
    rcases reach_queryP hl with rfl | ⟨y, -, rfl⟩ <;> simp [Prog.queryP, after] at ha
  commit := by
    intro _ _ _ _ _ _ hl ha
    rcases reach_queryP hl with rfl | ⟨y, -, rfl⟩ <;> simp [Prog.queryP, after] at ha
  sample := by
    intro _ _ _ hl ha
    rcases reach_queryP hl with rfl | ⟨y, -, rfl⟩ <;> simp [Prog.queryP, after] at ha
  query := by
    intro h₀ l i' ps' k rows hl ha hans
    rcases reach_queryP hl with rfl | ⟨y, -, rfl⟩
    · simp only [Prog.queryP, after, Option.some.injEq, Prog.query.injEq] at ha
      obtain ⟨rfl, rfl, -⟩ := ha
      by_cases hP : Pre h₀
      · have := h h₀ rows hP (by simpa using hans)
        simp [queryD, hP, this]
      · simp only [queryD, hP, ite_false]
        split_ifs <;> simp
    · simp [Prog.queryP, after] at ha
  moveEnd := by
    intro h₀ l q hl ha hm
    rcases reach_queryP hl with rfl | ⟨y, -, rfl⟩
    · simp only [Prog.queryP, after, Option.some.injEq] at ha; subst ha; simp [IsMove] at hm
    · simp only [Prog.queryP, after, Option.some.injEq] at ha; subst ha; simp [IsMove] at hm
  retEnd := by intro _ _ _ _ _ hD; simp [hD]
  retDoom := by intro _ _ _ _ _ hD; simp [hD]
  post := by
    intro h₀ l a hl ha hD
    rcases reach_queryP hl with rfl | ⟨y, -, rfl⟩
    · simp [Prog.queryP, after] at ha
    · simp only [Prog.queryP, after, Option.some.injEq, Prog.ret.injEq] at ha; subst ha; exact hD
  bound := by
    intro h₀ l hl hne hm
    rcases reach_queryP hl with rfl | ⟨y, -, rfl⟩
    · exact absurd rfl hne
    · simp [EndsMove] at hm

/-- **Require** `c`: from a precondition under which `c` gives the postcondition; the lead is the
follower's. -/
noncomputable def require {c : Prop} [Decidable c] {Post : Unit → List Ev → Prop}
    (h : ∀ h₀, Pre h₀ → c → Post () h₀) : Spec (Prog.require c) Pre Post εmax T T :=
  Spec.ite (fun hc ↦ (Spec.ret ()).mono (fun h₀ hp ↦ h h₀ hp hc) (fun _ _ h ↦ h) le_rfl le_rfl
    le_rfl)
    (fun _ ↦ Spec.fail.mono (fun _ h ↦ h) (fun _ _ h ↦ h) le_rfl zero_le le_rfl)

/-! ## A sub-program with no prover move -/

open Classical in
/-- The potential of `Spec.ofNoMove`: the expectation of `1` at a return breaking `Post`, the
follower's lead (capped) at one keeping it. -/
noncomputable def noMoveV (p : Prog α) (Post : α → List Ev → Prop) (T : ENNReal) (h₀ l : List Ev) :
    ENNReal :=
  match p.after l with
  | some q => retExp (fun a h ↦ if Post a h then min 1 T else 1) h₀ l q
  | none => 1

/-- The doom of `Spec.ofNoMove`: `Post` at the returns. -/
def noMoveD (p : Prog α) (Post : α → List Ev → Prop) (h₀ l : List Ev) : Prop :=
  match p.after l with
  | some (Prog.ret a) => Post a (h₀ ++ l)
  | _ => True

open Classical in
/-- **A sub-program with no prover move**: a joint bound `e < 1` on the probability of a return
breaking `Post` gives the lead `e` plus the follower's. -/
noncomputable def ofNoMove {p : Prog α} {e : ENNReal}
    (hnm : ∀ {h₀ l q}, p.Reach h₀ l → p.after l = some q → ¬ q.IsMove)
    (he : e < 1) (h : ∀ h₀, Pre h₀ → escRet Post h₀ [] p ≤ e) :
    Spec p Pre Post εmax (e + T) T where
  D := noMoveD p Post
  V := noMoveV p Post T
  le_one h₀ l := by
    unfold noMoveV
    split
    · exact retExp_le_one (fun _ _ ↦ by split_ifs <;> simp) _ _ _
    · exact le_rfl
  start_D h₀ hPre := by
    unfold noMoveD
    split
    · rename_i a ha
      simp only [after, Option.some.injEq] at ha
      subst ha
      have := (h h₀ hPre).trans_lt he
      simp only [escRet, retExp, List.append_nil] at this ⊢
      split_ifs at this with hc
      · exact hc
      · exact absurd this (lt_irrefl _)
    · trivial
  start_V h₀ hPre := by
    have hp : p.after [] = some p := by simp [after]
    change noMoveV p Post T h₀ [] ≤ e + T
    rw [noMoveV, hp]
    refine le_trans (retExp_le_add (g' := fun a h ↦ if Post a h then 0 else 1) ?_ h₀ p [])
      (by gcongr; exact h h₀ hPre)
    intro a h'
    by_cases hc : Post a h' <;> simp [hc]
  read := by intro _ _ _ _ hl ha; exact absurd trivial (hnm hl ha)
  grind := by intro _ _ _ _ hl ha; exact absurd trivial (hnm hl ha)
  commit := by intro _ _ _ _ _ _ hl ha; exact absurd trivial (hnm hl ha)
  sample := by
    intro h₀ l k hl ha
    have hc : ∀ c, noMoveV p Post T h₀ (l ++ [Ev.sample c]) =
        retExp (fun a h ↦ if Post a h then min 1 T else 1) h₀ (l ++ [Ev.sample c]) (k c) := by
      intro c
      simp [noMoveV, after_snoc _ ha, after]
    simp only [hc]
    simp only [noMoveV, ha, retExp]
    exact le_rfl
  query := by
    intro h₀ l i ps k rows hl ha hans
    simp [noMoveV, after_snoc _ ha, after, ha, retExp, hans]
  moveEnd := by intro _ _ _ hl ha hm; exact absurd hm (hnm hl ha)
  retEnd := by
    intro h₀ l a hl ha hD
    simp only [noMoveD, ha] at hD
    simp [noMoveV, ha, retExp, hD]
  retDoom := by
    intro h₀ l a hl ha hD
    simp only [noMoveD, ha] at hD
    simp [noMoveV, ha, retExp, hD]
  post := by
    intro h₀ l a hl ha hD
    simpa only [noMoveD, ha] using hD
  bound := by
    intro h₀ l hl hne hm
    cases hl with
    | nil => exact absurd rfl hne
    | read _ hl' ha | grind hl' ha | commit _ hl' ha _ => exact absurd trivial (hnm hl' ha)
    | sample | query => simp [EndsMove] at hm

end Spec

end
end LeanVM.Protocol.Compile
