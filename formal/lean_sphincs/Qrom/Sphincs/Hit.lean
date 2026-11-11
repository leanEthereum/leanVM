module

public import Qrom.Sphincs.Invariant

@[expose] public section

/-!
# Hits on the honest values

An input is good for a value when the value's low bits are the honest value at the input's address:
the label of the position at that address, or the encoding target of the key at an encoding address
(`Qrom.Sphincs.good`). An input has one address, so at most `2^128` values are good for it
(`Qrom.Sphincs.card_good_le`). An input at a position's address whose payload is not the honest one
is no honest input, and both hashes answer it with `G` (`Qrom.Sphincs.ans_of_not_honest`).
-/

open OracleComp OracleSpec FORS FORS.Security FORS.Security.Graph FORS.Security.GraphCorrectness
  FORS.Security.GraphView Concrete

noncomputable section

set_option linter.unusedSectionVars false

namespace Qrom.Sphincs

variable [Params]

/-- The word of a key read from the data: its first valid encoding, or the dummy word. -/
def wordH (h : Key → HashOutput) (lay : Layer) (tree : TreeIndex) (leaf : LeafIndex) : Encoding :=
  ((encH h lay tree leaf encodingAttemptLimit 0).map Prod.snd).getD ReferenceChoice.dummyWord

/-- The honest value at an encoding address: the packed word. -/
def encTarget (d : Data) (lay : Layer) (tree : TreeIndex) (leaf : LeafIndex) : Digest :=
  Completeness.pack (wordH (hOf d) lay tree leaf)

/-- The value `y` hits the honest value at the address of `x`. -/
def good (d : Data) (x : Input) (y : HashOutput) : Prop :=
  (∃ (p : Position) (param : PublicParameter) (pl : HashInput),
    x.1 = tweakableHashInput param p.domain pl ∧ truncateHash y = truncateHash (hOf d (.pos p))) ∨
  ∃ (lay : Layer) (tree : TreeIndex) (leaf : LeafIndex) (param : PublicParameter) (pl : HashInput),
    x.1 = tweakableHashInput param (.encoding lay tree leaf) pl ∧ truncateHash y = encTarget d lay tree leaf

theorem position_domain_ne_encoding (p : Position) (lay : Layer) (tree : TreeIndex) (leaf : LeafIndex) :
    hashDomainFields p.domain ≠ hashDomainFields (.encoding lay tree leaf) := by
  intro h
  have := hashFields_injective (right := .encoding lay tree leaf) p.domain_inRange trivial h
  cases p <;> simp [Position.domain] at this

open Classical in
/-- The honest value an input's address points to. -/
def goodTarget (d : Data) (x : Input) : Digest :=
  if hp : ∃ (p : Position) (param : PublicParameter) (pl : HashInput),
      x.1 = tweakableHashInput param p.domain pl then
    truncateHash (hOf d (.pos (Classical.choose hp)))
  else if he : ∃ (lay : Layer) (tree : TreeIndex) (leaf : LeafIndex) (param : PublicParameter)
      (pl : HashInput), x.1 = tweakableHashInput param (.encoding lay tree leaf) pl then
    encTarget d (Classical.choose he) (Classical.choose (Classical.choose_spec he))
      (Classical.choose (Classical.choose_spec (Classical.choose_spec he)))
  else 0

open Classical in
theorem good_target {d : Data} {x : Input} {y : HashOutput} (hg : good d x y) :
    truncateHash y = goodTarget d x := by
  unfold goodTarget
  rcases hg with ⟨p, param, pl, hx, hy⟩ | ⟨lay, tree, leaf, param, pl, hx, hy⟩
  · have hp : ∃ (p : Position) (param : PublicParameter) (pl : HashInput),
        x.1 = tweakableHashInput param p.domain pl := ⟨p, param, pl, hx⟩
    rw [dite_eq_left hp]
    obtain ⟨param', pl', hx'⟩ := Classical.choose_spec hp
    have hf := (tweakableInput_injective (hx.symm.trans hx')).1
    rw [← Position.fields_injective hf]
    exact hy
  · have hp : ¬ ∃ (p : Position) (param : PublicParameter) (pl : HashInput),
        x.1 = tweakableHashInput param p.domain pl := by
      rintro ⟨p, param', pl', hx'⟩
      exact position_domain_ne_encoding p lay tree leaf
        (tweakableInput_injective (hx'.symm.trans hx)).1
    have he : ∃ (lay : Layer) (tree : TreeIndex) (leaf : LeafIndex) (param : PublicParameter)
        (pl : HashInput), x.1 = tweakableHashInput param (.encoding lay tree leaf) pl :=
      ⟨lay, tree, leaf, param, pl, hx⟩
    rw [dite_eq_right hp, dite_eq_left he]
    obtain ⟨param', pl', hx'⟩ := Classical.choose_spec (Classical.choose_spec
      (Classical.choose_spec he))
    have hf := hashFields_injective (left := .encoding lay tree leaf) (right := .encoding _ _ _)
      trivial trivial (tweakableInput_injective (hx.symm.trans hx')).1
    simp only [HashDomain.encoding.injEq] at hf
    obtain ⟨h1, h2, h3⟩ := hf
    refine hy.trans ?_
    rw [h1, h2, h3]

open Classical in
/-- **At most `2^128` values are good for an input.** -/
theorem card_good_le (d : Data) (x : Input) :
    (Finset.univ.filter fun y ↦ good d x y).card ≤ 2 ^ 128 := by
  have hsub : (Finset.univ.filter fun y ↦ good d x y) ⊆
      Finset.univ.filter fun z : HashOutput ↦ truncateHash z = goodTarget d x := by
    intro y hy
    rw [Finset.mem_filter] at hy ⊢
    exact ⟨hy.1, good_target hy.2⟩
  have hc := card_trunc_fiber (goodTarget d x)
  have := Finset.card_le_card hsub
  omega

/-- An input at a position's address, with a payload of whole digests, that is not the honest input
there is no honest input. -/
theorem not_honest_of_position (d : Data) (p : Position) (param : PublicParameter) (pl : HashInput)
    {l : HashInput} (hx : l = tweakableHashInput param p.domain pl) (hne : l ≠ inputD d (.pos p))
    (hpl : 16 ∣ pl.length) : ∀ k, inputD d k ≠ l := by
  have h45 : pl.length ≠ 45 := by omega
  have h36 : pl.length ≠ 36 := by omega
  intro k hk
  subst hx
  cases k with
  | pkSeed => exact keySeedInput_ne_tweakableHashInput _ _ _ _ _ hk
  | prf => exact keySeedInput_ne_tweakableHashInput _ _ _ _ _ hk
  | ots => exact keygenInput_ne_hashInput _ _ _ _ _ _ hk
  | fts => exact keygenInput_ne_hashInput _ _ _ _ _ _ hk
  | rnd => exact randomizerHashInput_ne_tweakableHashInput _ _ _ _ _ h45 hk
  | dig => exact messageDigestInput_ne_tweakableHashInput _ _ _ _ _ _ _ h36 hk
  | pos q =>
    have hf := (tweakableInput_injective hk).1
    rw [Position.fields_injective hf] at hk
    exact hne hk.symm
  | enc lay tree leaf c =>
    exact position_domain_ne_encoding p lay tree leaf (tweakableInput_injective hk).1.symm

/-- Both hashes answer an input that is no honest input with `G`. -/
theorem ans_of_not_honest (d : Data) (s : Log) (G : Input → HashOutput) (x : Input)
    (hx : ∀ k, inputD d k ≠ x.1) :
    ovFun (d none) (hOf d) G x.1 = G x ∧ hidFun d s G x.1 = G x := by
  have hpt : ∀ k, pt (hOf d) (d none) k ≠ x := fun k hk ↦ hx k (congrArg Subtype.val hk)
  constructor
  · show extend (override (proc (d none)) G (hOf d)) x.1 = G x
    rw [extend_val, override_of_not_mem]
    exact hpt
  · rw [hidFun, extend_val]
    simp only [OvGame.answer, hidGame]
    rw [dite_eq_right fun ⟨k, hk⟩ ↦ hpt k hk.2]
    rfl

end Qrom.Sphincs
