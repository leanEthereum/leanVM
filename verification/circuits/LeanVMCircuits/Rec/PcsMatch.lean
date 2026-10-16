module

public import LeanVMCircuits.Rec.Collision

@[expose] public section

/-!
#551's PCS bound in `PcsBound`'s terms.

#551 (`verification/whir` at `8198d0b2`, a separate Lean project on Lean 4.34 and its own mathlib; this project is on Lean 4.33 with no WHIR dependency, so the theorem cannot be imported) proves `Whir.SpongefishCurrentKnowledgeFinal.current_knowledge`: over a uniform primitive oracle `Node → Digest32` (`PrimitiveOracle`) and uniform attacker coins, the rational average (`FiatShamirGame.average`) of the indicator of `NativeAcceptedAnyFull` (for some binding shape `k : Fin 4`, a received record natively accepted while the public straight-line extractor fails) is at most `∑ k : Fin 4, finalBound Q_k`, `Q_k` the counted budget (`fullBudget`) of shape `k`.

`Pcs551` states that conclusion for one child in its own form, over finite types standing for `Node`, `Digest32` and the coins: `average` of the event's indicator at most the `Fin 4` sum of `finalBound` (both verbatim), with a map `φ` from the recursion's outcomes to #551's whose fibers all have one size (so it pushes the uniform outcome to the uniform one) and `pcsBad v` inside the preimage of #551's event. `Pcs551.frac`: `pcsBad v`'s fraction is at most #551's bound; `pcsBound_of_551` is `PcsBound` with `epsPCS v` that bound.

`restrict_fiber` and `pair_fiber` discharge the fiber premise for the map #551's oracle is read through: restricting the ideal compression oracle `H : X → Fin 4 → V` along an injective encoding `encode : Node → X` and a bijection `out : (Fin 4 → V) → Digest` of outputs, paired with the other coins (`(ω₀, H) ↦ (out ∘ H ∘ encode, ω₀)` from `Edges.crEvent`'s outcomes), has fibers of one size. #551's `Node` is 833 bits (a digest, a block, a tweak and a flag) and the circuit's compression input 14 words of 64 bits, so the encoding is a restriction, not an equivalence.

What stays premises: #551's theorem itself (`knowledge`, across the project boundary) and the inclusion `sub` of `pcsBad v` in its event, which needs the parent's rows to be #551's native acceptance of the child's opening (setup, record receive, binding, proof of work, Merkle authentication and equations) and its extractor's witness to be the child's committed witness.
-/

namespace LeanVMCircuits.Rec.Edges

open Finset

/-- #551's `SpongefishCurrentBCSKnowledge.finalBound`. -/
def finalBound (Q : ℚ) : ℚ :=
  Q * ((17 / 32 : ℚ) ^ 56 + 1 / 2 ^ 78) + min 1 ((2 * Q ^ 2 - Q) / 2 ^ 256) + (Q ^ 3 + 3 * Q ^ 2 - 2 * Q) / 2 ^ 256

theorem finalBound_nonneg (Q : ℕ) : 0 ≤ finalBound Q := by
  unfold finalBound
  have hQ : (Q : ℚ) = 0 ∨ 1 ≤ (Q : ℚ) := by
    rcases Nat.eq_zero_or_pos Q with h | h
    · exact Or.inl (by simp [h])
    · exact Or.inr (by exact_mod_cast h)
  have h1 : (0 : ℚ) ≤ (Q : ℚ) * ((17 / 32 : ℚ) ^ 56 + 1 / 2 ^ 78) := by positivity
  have h2 : (0 : ℚ) ≤ min 1 ((2 * (Q : ℚ) ^ 2 - Q) / 2 ^ 256) := by
    refine le_min zero_le_one (div_nonneg ?_ (by positivity))
    rcases hQ with h | h
    · simp [h]
    · nlinarith
  have h3 : (0 : ℚ) ≤ ((Q : ℚ) ^ 3 + 3 * Q ^ 2 - 2 * Q) / 2 ^ 256 := by
    refine div_nonneg ?_ (by positivity)
    rcases hQ with h | h
    · simp [h]
    · nlinarith
  linarith

/-- #551's `FiatShamirGame.average`: the uniform average over a finite type. -/
def average {C : Type} [Fintype C] (f : C → ℚ) : ℚ := (∑ c, f c) / Fintype.card C

/-- A map whose fibers all have `c` elements: the preimage of `S` is `|S| / |Y|` of the outcomes. -/
theorem card_preimage {Ω Y : Type} [Fintype Ω] [Fintype Y] [DecidableEq Y] (φ : Ω → Y) (c : ℕ) (hc : ∀ y, #{ω | φ ω = y} = c)
    (S : Finset Y) : #{ω | φ ω ∈ S} * Fintype.card Y = #S * Fintype.card Ω := by
  have hpre : #{ω | φ ω ∈ S} = ∑ y ∈ S, #{ω | φ ω = y} := by
    rw [card_eq_sum_card_fiberwise (f := φ) (t := S) fun ω hω => by simpa using hω]
    refine sum_congr rfl fun y hy => congrArg card ?_
    ext ω
    simp only [mem_filter, mem_univ, true_and]
    exact ⟨fun h => h.2, fun h => ⟨h ▸ hy, h⟩⟩
  have hall : Fintype.card Ω = ∑ y : Y, #{ω | φ ω = y} := by
    rw [← card_univ, card_eq_sum_card_fiberwise (f := φ) (t := univ) fun _ _ => mem_univ _]
  rw [hpre, hall, sum_congr rfl fun y _ => hc y, sum_congr rfl fun y _ => hc y, sum_const, sum_const, card_univ,
    smul_eq_mul, smul_eq_mul]
  ring

section Match

variable {ι Ω : Type} [Fintype Ω] {Node Digest Coins : Type} [Fintype Node] [DecidableEq Node] [Fintype Digest]
  [DecidableEq Digest] [Fintype Coins] [DecidableEq Coins]

open Classical in
/-- #551's `current_knowledge` for child `v`, matched to `pcsBad v`. `bad` is #551's event (`NativeAcceptedAnyFull` with the extraction failure) on its outcomes, a primitive oracle and the attacker's coins, `Q k` the budget of binding shape `k`, and `knowledge` the theorem's conclusion in its form. `φ` reads #551's outcome off the recursion's, with fibers of one size (`fiber`), and `pcsBad v` is inside the preimage of `bad` (`sub`). -/
structure Pcs551 (P : RecParts ι Ω) (v : ι) where
  bad : (Node → Digest) × Coins → Prop
  Q : Fin 4 → ℕ
  knowledge : average (fun x => if bad x then (1 : ℚ) else 0) ≤ ∑ k, finalBound (Q k)
  φ : Ω → (Node → Digest) × Coins
  fiber : ∃ c, ∀ y, #{ω | φ ω = y} = c
  sub : ∀ ω ∈ P.pcsBad v, bad (φ ω)

open Classical in
/-- `pcsBad v`'s fraction of the outcomes is at most #551's bound. -/
theorem Pcs551.frac {P : RecParts ι Ω} {v : ι} (m : Pcs551 (Node := Node) (Digest := Digest) (Coins := Coins) P v) :
    ((P.pcsBad v).card : ℚ) / Fintype.card Ω ≤ ∑ k, finalBound (m.Q k) := by
  obtain ⟨c, hc⟩ := m.fiber
  have hnn : 0 ≤ ∑ k, finalBound (m.Q k) := sum_nonneg fun k _ => finalBound_nonneg _
  rcases Nat.eq_zero_or_pos (Fintype.card Ω) with h0 | hpos
  · simp [h0, hnn]
  have hY : 0 < Fintype.card ((Node → Digest) × Coins) :=
    Fintype.card_pos_iff.mpr ⟨m.φ (Classical.choice (Fintype.card_pos_iff.mp hpos))⟩
  have hpre := card_preimage m.φ c hc {y | m.bad y}
  have hsub : (P.pcsBad v).card ≤ #{ω | m.φ ω ∈ ({y | m.bad y} : Finset _)} :=
    card_le_card fun ω hω => by simpa using m.sub ω hω
  have havg : average (fun x => if m.bad x then (1 : ℚ) else 0) =
      (#({y | m.bad y} : Finset ((Node → Digest) × Coins)) : ℚ) / Fintype.card ((Node → Digest) × Coins) := by
    rw [average, sum_boole]
  refine le_trans ?_ (havg ▸ m.knowledge)
  rw [div_le_div_iff₀ (by exact_mod_cast hpos) (by exact_mod_cast hY)]
  calc ((P.pcsBad v).card : ℚ) * Fintype.card ((Node → Digest) × Coins)
      ≤ (#{ω | m.φ ω ∈ ({y | m.bad y} : Finset _)} : ℚ) * Fintype.card ((Node → Digest) × Coins) := by
        gcongr
    _ = _ := by exact_mod_cast hpre

/-- `PcsBound` from #551 at every child: `epsPCS v` is #551's bound for child `v`. -/
theorem pcsBound_of_551 (P : RecParts ι Ω) (m : ∀ v, Pcs551 (Node := Node) (Digest := Digest) (Coins := Coins) P v) :
    PcsBound P fun v => (∑ k, finalBound ((m v).Q k)).toNNRat := by
  refine ⟨fun v => ?_⟩
  have hnn : 0 ≤ ∑ k, finalBound ((m v).Q k) := sum_nonneg fun k _ => finalBound_nonneg _
  rw [← NNRat.coe_le_coe, Rat.coe_toNNRat _ hnn]
  push_cast
  exact (m v).frac

end Match

/-- Restricting a function along an injective encoding `e` of inputs and a bijection `out` of outputs: any two fibers have as many elements. -/
theorem restrict_fiber_eq {A B Y Z : Type} [Fintype A] [Fintype B] [DecidableEq B] [Fintype Y] [DecidableEq Y]
    [DecidableEq Z] (e : A → B) (he : Function.Injective e) (out : Y → Z) (hout : Function.Bijective out)
    (g g' : A → Z) :
    #{H : B → Y | (fun a => out (H (e a))) = g} = #{H : B → Y | (fun a => out (H (e a))) = g'} := by
  classical
  let inv := Function.surjInv hout.2
  have hinv : ∀ z, out (inv z) = z := Function.surjInv_eq hout.2
  have hinv' : ∀ y, inv (out y) = y := Function.leftInverse_surjInv hout
  let put : (A → Z) → (B → Y) → (B → Y) := fun g H b => if h : ∃ a, e a = b then inv (g h.choose) else H b
  have hput : ∀ g H a, put g H (e a) = inv (g a) := fun g H a => by
    have hex : ∃ a', e a' = e a := ⟨a, rfl⟩
    simp only [put, dif_pos hex, he hex.choose_spec]
  have hoff : ∀ g H b, (¬ ∃ a, e a = b) → put g H b = H b := fun g H b h => by simp only [put, dif_neg h]
  have back : ∀ g H, (fun a => out (H (e a))) = g → put g H = H := fun g H hH => by
    funext b
    by_cases h : ∃ a, e a = b
    · obtain ⟨a, rfl⟩ := h
      rw [hput, ← hH, hinv']
    · exact hoff g H b h
  refine card_bij' (fun H _ => put g' H) (fun H _ => put g H) ?_ ?_ ?_ ?_
  · intro H _
    simp only [mem_filter, mem_univ, true_and]
    funext a
    rw [hput, hinv]
  · intro H _
    simp only [mem_filter, mem_univ, true_and]
    funext a
    rw [hput, hinv]
  · intro H hH
    simp only [mem_filter, mem_univ, true_and] at hH
    funext b
    by_cases h : ∃ a, e a = b
    · obtain ⟨a, rfl⟩ := h
      rw [hput, ← hH, hinv']
    · rw [hoff g _ b h, hoff g' H b h]
  · intro H hH
    simp only [mem_filter, mem_univ, true_and] at hH
    funext b
    by_cases h : ∃ a, e a = b
    · obtain ⟨a, rfl⟩ := h
      rw [hput, ← hH, hinv']
    · rw [hoff g' _ b h, hoff g H b h]

/-- The fibers of a restriction along an injective encoding and an output bijection all have one size. -/
theorem restrict_fiber {A B Y Z : Type} [Fintype A] [Fintype B] [DecidableEq B] [Fintype Y] [DecidableEq Y]
    [DecidableEq Z] (e : A → B) (he : Function.Injective e) (out : Y → Z) (hout : Function.Bijective out) :
    ∃ c, ∀ g : A → Z, #{H : B → Y | (fun a => out (H (e a))) = g} = c := by
  by_cases hn : Nonempty (A → Z)
  · obtain ⟨g₀⟩ := hn
    exact ⟨_, fun g => restrict_fiber_eq e he out hout g g₀⟩
  · exact ⟨0, fun g => absurd ⟨g⟩ hn⟩

open Classical in
/-- Pairing with the other coins keeps the fibers of one size: the map `(ω₀, H) ↦ (ψ H, ω₀)`. -/
theorem pair_fiber {Ω₀ F Y : Type} [Fintype Ω₀] [DecidableEq Ω₀] [Fintype F] [DecidableEq Y] (ψ : F → Y) (c : ℕ)
    (hc : ∀ y, #{H | ψ H = y} = c) : ∀ y : Y × Ω₀, #{ω : Ω₀ × F | (ψ ω.2, ω.1) = y} = c := by
  rintro ⟨y, w⟩
  rw [← hc y]
  refine card_bij' (fun ω _ => ω.2) (fun H _ => (w, H)) ?_ ?_ ?_ ?_
  · intro ω hω
    simp only [mem_filter, mem_univ, true_and, Prod.mk.injEq] at hω ⊢
    exact hω.1
  · intro H hH
    simpa only [mem_filter, mem_univ, true_and, Prod.mk.injEq, and_true] using hH
  · intro ω hω
    simp only [mem_filter, mem_univ, true_and, Prod.mk.injEq] at hω
    exact Prod.ext hω.2.symm rfl
  · intro H _
    rfl

open Classical in
/-- The map from the ideal compression model's outcomes `(ω₀, H)` to #551's, reading #551's primitive oracle through an injective input encoding and an output bijection, meets `Pcs551.fiber`. -/
theorem compress_fiber {Ω₀ X V Node Digest : Type} [Fintype Ω₀] [DecidableEq Ω₀] [Fintype X] [DecidableEq X] [Fintype V]
    [DecidableEq V] [Fintype Node] [DecidableEq Digest] (encode : Node → X) (he : Function.Injective encode)
    (out : (Fin 4 → V) → Digest) (hout : Function.Bijective out) :
    ∃ c, ∀ y : (Node → Digest) × Ω₀,
      #{ω : Ω₀ × (X → Fin 4 → V) | ((fun n => out (ω.2 (encode n))), ω.1) = y} = c := by
  obtain ⟨c, hc⟩ := restrict_fiber encode he out hout
  exact ⟨c, pair_fiber (fun (H : X → Fin 4 → V) n => out (H (encode n))) c hc⟩

open Classical in
/-- Non-vacuity of `Pcs551`: parts with no PCS event meet it with #551's event empty and a zero budget. -/
example {ι Ω : Type} [Fintype Ω] (P : RecParts ι Ω) (v : ι) (h : P.pcsBad v = ∅) :
    Nonempty (Pcs551 (Node := Unit) (Digest := Unit) (Coins := Unit) P v) :=
  ⟨{ bad := fun _ => False
     Q := fun _ => 0
     knowledge := by simp [average, finalBound]
     φ := fun _ => default
     fiber := ⟨Fintype.card Ω, fun y => by
       rw [show y = default from Subsingleton.elim _ _]
       simp⟩
     sub := fun ω hω => by simp [h] at hω }⟩

end LeanVMCircuits.Rec.Edges
