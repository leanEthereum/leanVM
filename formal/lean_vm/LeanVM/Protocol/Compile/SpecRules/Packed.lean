/-
  LeanVM.Protocol.Compile.SpecRules.Packed

  The leaves of the specification calculus for packed messages: a packed read, a packed draw with
  its bad set's average or count, a packed draw whose challenges a pure function slices, and a
  proof of work followed by a packed draw.
-/

module

public import LeanVM.Protocol.Compile.SpecRules.Leaves
public import LeanVM.Protocol.Compile.SpecRules.Grind

/-!
# Packed messages

| leaf | lead | side condition |
| --- | --- | --- |
| `Spec.readPackedE n` | `0` | `T ≤ εmax` (the boundary after the message) |
| `Spec.samplePackedE n e` | `e + T` | the bad lists of `n` challenges average at most `e` |
| `Spec.samplePackedCount n N` | `N/|E| + T` | at most `N·|E|^(n-1)` of the `|E|^n` lists are bad |
| `Spec.samplePackedMap f n N` | `N/|E| + T` | the count, on `f` of the challenges |
| `Spec.grindSamplePacked b n N` | `0` (`N/|E| + T` at `b = 0`) | the count, and `2^-b·(N/|E| + T) ≤ εmax` |

A packed draw of `n` challenges is one event (`Ev.samplePacked`), its challenges uniform and
independent in `E^n` (`avgPk`). The verifier slices the challenges into named vectors
(`drawn.take`, `drawn.drop`); `avgPk_slices` and `avgPk_ind_or_le` turn a bound on each named
slice into one on the draw, and `avgPk_le_card` a Schwartz-Zippel count into an average.
-/

namespace LeanVM.Protocol.Compile

open LeanVM.Parameters VerifierProgram

@[expose] public section

variable {α β : Type}

/-! ## Averages over slices -/

/-- **Averaging over two slices**: the first `a` challenges and the next `b`. -/
theorem avgPk_slices (a b : ℕ) (g : List E → List E → ENNReal) :
    avgPk (a + b) (fun l ↦ g (l.take a) (l.drop a)) = avgPk a fun x ↦ avgPk b fun y ↦ g x y := by
  rw [avgPk_append]
  refine avgPk_congr fun x hx ↦ avgPk_congr fun y _ ↦ ?_
  rw [List.take_append_of_le_length (by omega), List.take_of_length_le (by omega),
    List.drop_append_of_le_length (by omega), List.drop_of_length_le (by omega), List.nil_append]

open Classical in
/-- A union of bad sets averages at most the sum of their averages. -/
theorem avgPk_ind_or_le (n : ℕ) (A B : List E → Prop) :
    avgPk n (fun l ↦ if A l ∨ B l then 1 else 0) ≤
      avgPk n (fun l ↦ if A l then 1 else 0) + avgPk n (fun l ↦ if B l then 1 else 0) := by
  rw [← avgPk_add]
  refine avgPk_mono fun l _ ↦ ?_
  by_cases hA : A l <;> by_cases hB : B l <;> simp [hA, hB]

/-! ## A packed read -/

private theorem reach_readPackedE {n : ℕ} {h₀ l : List Ev}
    (hl : (readScalarsPacked n).Reach h₀ l) :
    l = [] ∨ ∃ xs, xs.length = n ∧ l = [Ev.readPacked xs] := by
  induction hl with
  | nil => exact .inl rfl
  | readPacked xs _ ha hn ih =>
    rcases ih with rfl | ⟨y, -, rfl⟩
    · simp only [readScalarsPacked, after, Option.some.injEq, VerifierProgram.readPacked.injEq]
        at ha
      obtain ⟨rfl, -⟩ := ha
      exact .inr ⟨xs, hn, rfl⟩
    · simp [readScalarsPacked, after] at ha
  | read _ _ ha ih | sample _ _ ha ih | grind _ ha ih | commit _ _ ha _ ih | query _ ha _ ih
  | samplePacked _ _ ha _ ih =>
    rcases ih with rfl | ⟨y, -, rfl⟩ <;> simp [readScalarsPacked, after] at ha

namespace Spec

variable {Pre : List Ev → Prop} {εmax T : ENNReal}

open Classical in
/-- **Read a packed message** of `n` scalars: `Post` after every message of `n` scalars; the
boundary after it carries the follower's lead. -/
noncomputable def readPackedE {Post : List E → List Ev → Prop} (n : ℕ)
    (h : ∀ h₀ xs, Pre h₀ → xs.length = n → Post xs (h₀ ++ [Ev.readPacked xs]))
    (hT : T ≤ εmax) : Spec (readScalarsPacked n) Pre Post εmax 0 T where
  D h₀ l := match l with
    | [] => Pre h₀
    | [Ev.readPacked xs] => xs.length = n → Post xs (h₀ ++ [Ev.readPacked xs])
    | _ => True
  V h₀ l := match l with
    | [] => if Pre h₀ then 0 else 1
    | [Ev.readPacked xs] =>
      if xs.length = n → Post xs (h₀ ++ [Ev.readPacked xs]) then min 1 T else 1
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
    rcases reach_readPackedE hl with rfl | ⟨y, -, rfl⟩ <;> simp [readScalarsPacked, after] at ha
  readPacked := by
    intro h₀ l n' k xs hl ha hn hD
    rcases reach_readPackedE hl with rfl | ⟨y, -, rfl⟩
    · simp only [readScalarsPacked, after, Option.some.injEq, VerifierProgram.readPacked.injEq]
        at ha
      obtain ⟨rfl, -⟩ := ha
      exact fun _ ↦ h h₀ xs hD hn
    · simp [readScalarsPacked, after] at ha
  samplePacked := by
    intro _ _ _ _ hl ha
    rcases reach_readPackedE hl with rfl | ⟨y, -, rfl⟩ <;> simp [readScalarsPacked, after] at ha
  grind := by
    intro _ _ _ _ hl ha
    rcases reach_readPackedE hl with rfl | ⟨y, -, rfl⟩ <;> simp [readScalarsPacked, after] at ha
  commit := by
    intro _ _ _ _ _ _ hl ha
    rcases reach_readPackedE hl with rfl | ⟨y, -, rfl⟩ <;> simp [readScalarsPacked, after] at ha
  sample := by
    intro _ _ _ hl ha
    rcases reach_readPackedE hl with rfl | ⟨y, -, rfl⟩ <;> simp [readScalarsPacked, after] at ha
  query := by
    intro _ _ _ _ _ _ hl ha
    rcases reach_readPackedE hl with rfl | ⟨y, -, rfl⟩ <;> simp [readScalarsPacked, after] at ha
  moveEnd := by
    intro h₀ l q hl ha hm hD
    rcases reach_readPackedE hl with rfl | ⟨y, hy, rfl⟩
    · simp [hD]
    · simp only [readScalarsPacked, after, hy, ↓reduceIte, Option.some.injEq] at ha
      subst ha; simp [IsMove] at hm
  retEnd := by
    intro h₀ l a hl ha hD
    rcases reach_readPackedE hl with rfl | ⟨y, -, rfl⟩
    · simp [readScalarsPacked, after] at ha
    · simp only at hD ⊢
      split_ifs
      exact le_rfl
  retDoom := by
    intro h₀ l a hl ha hD
    rcases reach_readPackedE hl with rfl | ⟨y, -, rfl⟩
    · simp [readScalarsPacked, after] at ha
    · simp only at hD ⊢
      split_ifs
      exact le_rfl
  post := by
    intro h₀ l a hl ha hD
    rcases reach_readPackedE hl with rfl | ⟨y, hy, rfl⟩
    · simp [readScalarsPacked, after] at ha
    · simp only [readScalarsPacked, after, hy, ↓reduceIte, Option.some.injEq,
        VerifierProgram.ret.injEq] at ha
      subst ha; exact hD hy
  bound := by
    intro h₀ l hl hne hm hD
    rcases reach_readPackedE hl with rfl | ⟨y, -, rfl⟩
    · exact absurd rfl hne
    · simp only at hD ⊢
      split_ifs
      simp only [grindBits, List.getLast?_singleton, pow_zero, one_mul]
      exact (min_le_right _ _).trans hT

end Spec

/-! ## A packed draw -/

private theorem reach_samplePackedE {n : ℕ} {h₀ l : List Ev}
    (hl : (sampleChallengesPacked n).Reach h₀ l) :
    l = [] ∨ ∃ cs, cs.length = n ∧ l = [Ev.samplePacked cs] := by
  induction hl with
  | nil => exact .inl rfl
  | samplePacked cs _ ha hn ih =>
    rcases ih with rfl | ⟨y, -, rfl⟩
    · simp only [sampleChallengesPacked, after, Option.some.injEq,
        VerifierProgram.samplePacked.injEq] at ha
      obtain ⟨rfl, -⟩ := ha
      exact .inr ⟨cs, hn, rfl⟩
    · simp [sampleChallengesPacked, after] at ha
  | read _ _ ha ih | sample _ _ ha ih | grind _ ha ih | commit _ _ ha _ ih | query _ ha _ ih
  | readPacked _ _ ha _ ih =>
    rcases ih with rfl | ⟨y, -, rfl⟩ <;> simp [sampleChallengesPacked, after] at ha

/-- The doom of `Spec.samplePackedE`. -/
def samplePackedD (Pre : List Ev → Prop) (Post : List E → List Ev → Prop) (n : ℕ)
    (h₀ l : List Ev) : Prop :=
  match l with
  | [] => Pre h₀
  | [Ev.samplePacked cs] => cs.length = n → Post cs (h₀ ++ [Ev.samplePacked cs])
  | _ => True

open Classical in
/-- The potential of `Spec.samplePackedE` after the draw. -/
noncomputable def samplePackedG (Pre : List Ev → Prop) (Post : List E → List Ev → Prop) (n : ℕ)
    (T : ENNReal) (h₀ l : List Ev) : ENNReal :=
  if samplePackedD Pre Post n h₀ l then min 1 T else 1

theorem samplePackedG_le_one {Pre : List Ev → Prop} {Post : List E → List Ev → Prop} {n : ℕ}
    {T : ENNReal} (h₀ l : List Ev) : samplePackedG Pre Post n T h₀ l ≤ 1 := by
  unfold samplePackedG; split_ifs <;> simp

namespace Spec

variable {Pre : List Ev → Prop} {εmax T : ENNReal}

open Classical in
/-- **A packed draw** of `n` challenges: the lists of `n` challenges that break `Post` average at
most `e`; the lead is `e` plus the follower's. -/
noncomputable def samplePackedE {Post : List E → List Ev → Prop} (n : ℕ) (e : ENNReal)
    (h : ∀ h₀, Pre h₀ →
      avgPk n (fun cs ↦ if Post cs (h₀ ++ [Ev.samplePacked cs]) then 0 else 1) ≤ e) :
    Spec (sampleChallengesPacked n) Pre Post εmax (e + T) T where
  D := samplePackedD Pre Post n
  V h₀ l := match l with
    | [] => avgPk n fun cs ↦ samplePackedG Pre Post n T h₀ [Ev.samplePacked cs]
    | _ => samplePackedG Pre Post n T h₀ l
  le_one h₀ l := by
    split
    · exact avgPk_le_of_le fun cs _ ↦ samplePackedG_le_one _ _
    · exact samplePackedG_le_one _ _
  start_D _ h := h
  start_V h₀ hPre := by
    simp only
    calc avgPk n (fun cs ↦ samplePackedG Pre Post n T h₀ [Ev.samplePacked cs])
        ≤ avgPk n (fun cs ↦ (if Post cs (h₀ ++ [Ev.samplePacked cs]) then 0 else 1) + T) := by
          refine avgPk_mono fun cs hcs ↦ ?_
          unfold samplePackedG samplePackedD
          by_cases hc : Post cs (h₀ ++ [Ev.samplePacked cs])
          · simp [hc, hcs]
          · simp [hc, hcs]
      _ = avgPk n (fun cs ↦ if Post cs (h₀ ++ [Ev.samplePacked cs]) then 0 else 1) + T := by
          rw [avgPk_add, avgPk_const]
      _ ≤ e + T := by gcongr; exact h h₀ hPre
  read := by
    intro _ _ _ _ hl ha
    rcases reach_samplePackedE hl with
      rfl | ⟨y, -, rfl⟩ <;> simp [sampleChallengesPacked, after] at ha
  readPacked := by
    intro _ _ _ _ _ hl ha
    rcases reach_samplePackedE hl with
      rfl | ⟨y, -, rfl⟩ <;> simp [sampleChallengesPacked, after] at ha
  samplePacked := by
    intro h₀ l n' k hl ha
    rcases reach_samplePackedE hl with rfl | ⟨y, -, rfl⟩
    · simp only [sampleChallengesPacked, after, Option.some.injEq,
        VerifierProgram.samplePacked.injEq] at ha
      obtain ⟨rfl, -⟩ := ha
      exact le_rfl
    · simp [sampleChallengesPacked, after] at ha
  grind := by
    intro _ _ _ _ hl ha
    rcases reach_samplePackedE hl with
      rfl | ⟨y, -, rfl⟩ <;> simp [sampleChallengesPacked, after] at ha
  commit := by
    intro _ _ _ _ _ _ hl ha
    rcases reach_samplePackedE hl with
      rfl | ⟨y, -, rfl⟩ <;> simp [sampleChallengesPacked, after] at ha
  sample := by
    intro _ _ _ hl ha
    rcases reach_samplePackedE hl with
      rfl | ⟨y, -, rfl⟩ <;> simp [sampleChallengesPacked, after] at ha
  query := by
    intro _ _ _ _ _ _ hl ha
    rcases reach_samplePackedE hl with
      rfl | ⟨y, -, rfl⟩ <;> simp [sampleChallengesPacked, after] at ha
  moveEnd := by
    intro h₀ l q hl ha hm
    rcases reach_samplePackedE hl with rfl | ⟨y, hy, rfl⟩
    · simp only [sampleChallengesPacked, after, Option.some.injEq] at ha
      subst ha; simp [IsMove] at hm
    · simp only [sampleChallengesPacked, after, hy, ↓reduceIte, Option.some.injEq] at ha
      subst ha; simp [IsMove] at hm
  retEnd := by
    intro h₀ l a hl ha hD
    rcases reach_samplePackedE hl with rfl | ⟨y, -, rfl⟩
    · simp [sampleChallengesPacked, after] at ha
    · simp [samplePackedG, hD]
  retDoom := by
    intro h₀ l a hl ha hD
    rcases reach_samplePackedE hl with rfl | ⟨y, -, rfl⟩
    · simp [sampleChallengesPacked, after] at ha
    · simp [samplePackedG, hD]
  post := by
    intro h₀ l a hl ha hD
    rcases reach_samplePackedE hl with rfl | ⟨y, hy, rfl⟩
    · simp [sampleChallengesPacked, after] at ha
    · simp only [sampleChallengesPacked, after, hy, ↓reduceIte, Option.some.injEq,
        VerifierProgram.ret.injEq] at ha
      subst ha; exact hD hy
  bound := by
    intro h₀ l hl hne hm
    rcases reach_samplePackedE hl with rfl | ⟨y, -, rfl⟩
    · exact absurd rfl hne
    · simp [EndsMove] at hm

open Classical in
/-- **A packed draw with a bad-set count**: if at most `N·|E|^(n-1)` of the `|E|^n` lists of `n`
challenges break `Post`, the lead is `N/|E|` plus the follower's. -/
noncomputable def samplePackedCount {Post : List E → List Ev → Prop} (n N : ℕ) (hn : 1 ≤ n)
    (h : ∀ h₀, Pre h₀ → (Finset.univ.filter fun v : Fin n → E ↦
      ¬ Post (List.ofFn v) (h₀ ++ [Ev.samplePacked (List.ofFn v)])).card ≤
        N * Fintype.card E ^ (n - 1)) :
    Spec (sampleChallengesPacked n) Pre Post εmax ((N : ENNReal) / Fintype.card E + T) T :=
  samplePackedE n _ fun h₀ hPre ↦ by
    have hc := avgPk_le_card (N := N) hn (fun cs ↦ ¬ Post cs (h₀ ++ [Ev.samplePacked cs]))
      (by convert h h₀ hPre)
    refine le_trans (le_of_eq (avgPk_congr fun cs _ ↦ ?_)) hc
    by_cases hp : Post cs (h₀ ++ [Ev.samplePacked cs]) <;> simp [hp]

open Classical in
/-- **A packed draw sliced by a pure function**: the program draws `n` challenges and returns
`f` of them (the verifier's named slices, `drawn.take`, `drawn.drop`); a count of the lists whose
image breaks `Post` gives the lead `N/|E|` plus the follower's. A phase `sampleChallengesPacked n
>>= fun cs ↦ k (f cs)` is this followed by `k` (`bind_assoc`). -/
noncomputable def samplePackedMap {Post : β → List Ev → Prop} (f : List E → β) (n N : ℕ)
    (hn : 1 ≤ n)
    (h : ∀ h₀, Pre h₀ → (Finset.univ.filter fun v : Fin n → E ↦
      ¬ Post (f (List.ofFn v)) (h₀ ++ [Ev.samplePacked (List.ofFn v)])).card ≤
        N * Fintype.card E ^ (n - 1)) :
    Spec (sampleChallengesPacked n >>= fun cs ↦ pure (f cs)) Pre Post εmax
      ((N : ENNReal) / Fintype.card E + T) T :=
  Spec.bind' (samplePackedCount (Post := fun cs h ↦ Post (f cs) h) n N hn h)
    fun cs ↦ (Spec.ret (Post := Post) (εmax := εmax) (T := T) (f cs)).congr (VerifierProgram.pure_eq _).symm

open Classical in
/-- **A proof of work, then a packed draw**: the grind's boundary discounts the draw's error and
the follower's lead by its bits, so with the count of `samplePackedCount` after the grind, the
side condition is `2^-b·(N/|E| + T) ≤ εmax` (with `grindingBits_discount` for the grind
`grindingBits N`). The lead is `0`, or `N/|E| + T` when `b = 0` and the verifier grinds
nothing. -/
noncomputable def grindSamplePacked {Post : List E → List Ev → Prop} (b n N : ℕ) (hn : 1 ≤ n)
    (h : ∀ h₀, Pre h₀ → (Finset.univ.filter fun v : Fin n → E ↦
      ¬ Post (List.ofFn v) (h₀ ++ grindEvs b ++ [Ev.samplePacked (List.ofFn v)])).card ≤
        N * Fintype.card E ^ (n - 1))
    (hT : (2 : ENNReal)⁻¹ ^ b * ((N : ENNReal) / Fintype.card E + T) ≤ εmax) :
    Spec (grindProofOfWork b >>= fun _ ↦ sampleChallengesPacked n) Pre Post εmax
      (if b = 0 then (N : ENNReal) / Fintype.card E + T else 0) T :=
  Spec.bind' (Post := fun _ h ↦ ∃ h₀, Pre h₀ ∧ h = h₀ ++ grindEvs b)
    (grindP b (fun h₀ hp ↦ ⟨h₀, hp, rfl⟩) hT)
    fun _ ↦ samplePackedCount n N hn fun _ ⟨h₀, hp, he⟩ ↦ by subst he; exact h h₀ hp

end Spec

end
end LeanVM.Protocol.Compile
