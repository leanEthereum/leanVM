import SphincsSecurity.Proof.Base.Prelude
import SphincsSecurity.Proof.Fts.FewTimeSignerView
import SphincsSecurity.Proof.Ots.SecretProbe
/-!
# Split random-oracle keys for hidden few-time leaves

Before an unrevealed few-time secret is guessed, its honest leaf-hash input is distinct from every
ordinary hash input available to the adversary. This file builds the lazy split-oracle side of that
argument. Ordinary inputs retain their exact keys, while an internal few-time leaf uses its secret
table coordinate as an opaque key. Both kinds receive lazy and consistent uniform answers.
-/

namespace SphincsSecurity.Concrete.FtsProbeSimulation

open OracleComp OracleSpec ENNReal

abbrev Coordinate := Index × FtsTree × FtsLeaf

noncomputable local instance instNonemptyCoordinate : Nonempty Coordinate :=
  ⟨(⟨0, by norm_num [totalHeight]⟩,
    ⟨0, by norm_num [ftsTrees]⟩,
    ⟨0, by norm_num [ftsTreeHeight]⟩)⟩

noncomputable def decodeProbe? (parameter : PublicParameter) (input : HashInput) :
    Option FtsSecretProbe := by
  classical
  exact if hexists : ∃ probe : FtsSecretProbe, probe.input parameter = input then
    some hexists.choose
  else none

theorem decodeProbe?_eq_some_iff (parameter : PublicParameter) (input : HashInput)
    (probe : FtsSecretProbe) :
    decodeProbe? parameter input = some probe ↔ probe.input parameter = input := by
  classical
  unfold decodeProbe?
  split
  · rename_i hexists
    constructor
    · intro heq
      have hprobe : hexists.choose = probe := Option.some.inj heq
      rw [← hprobe]
      exact hexists.choose_spec
    · intro hinput
      congr 1
      apply FtsSecretProbe.input_injective parameter
      exact hexists.choose_spec.trans hinput.symm
  · rename_i hnone
    constructor
    · simp
    · intro hinput
      exact (hnone ⟨probe, hinput⟩).elim

theorem decodeProbe?_eq_none_iff (parameter : PublicParameter) (input : HashInput) :
    decodeProbe? parameter input = none ↔
      ∀ probe : FtsSecretProbe, probe.input parameter ≠ input := by
  constructor
  · intro hnone probe hinput
    have hsome := (decodeProbe?_eq_some_iff parameter input probe).2 hinput
    rw [hnone] at hsome
    simp at hsome
  · intro hnone
    cases hdecode : decodeProbe? parameter input with
    | none => rfl
    | some probe =>
        exact (hnone probe ((decodeProbe?_eq_some_iff parameter input probe).1 hdecode)).elim
