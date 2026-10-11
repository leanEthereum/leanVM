import Whir.PublicCompressionCouplingStreamFacts

/-! The exact cache relation used by the source induction: stored cells, not
only sampled digests, correspond under consumed-coordinate relabeling. -/
namespace Whir.PublicCompressionCouplingRelabelCache
open FiatShamirGame TypedFiatShamirGame PublicCompressionCouplingJoint

variable {A B : Type} [DecidableEq A] [DecidableEq B]

structure Related (label : B → A) (pc : Cache A) (qc : Cache B) : Prop where
  forward : ∀ key answer, qc key=some answer → pc (label key)=some answer
  backward : ∀ node answer, pc node=some answer →
    ∃ key, qc key=some answer ∧ label key=node

def Extends (qc final : Cache B) : Prop :=
  ∀ key answer, qc key=some answer → final key=some answer

def InjectiveOn (label : B → A) (final : Cache B) : Prop :=
  ∀ left right d e, final left=some d → final right=some e → label left=label right → left=right

omit [DecidableEq A] [DecidableEq B] in
 theorem empty_related (label : B → A) : Related label (fun _ => none) (fun _ => none) := by
  constructor
  · intro key answer impossible; cases impossible
  · intro node answer impossible; cases impossible

omit [DecidableEq A] [DecidableEq B] in
 theorem Related.lookup {label : B → A} {pc : Cache A} {qc final : Cache B}
    (related : Related label pc qc) (extension : Extends qc final)
    (injective : InjectiveOn label final) {key : B} {answer : Digest32}
    (present : final key=some answer) : pc (label key)=qc key := by
  cases hit : qc key with
  | some digest => exact related.forward key digest hit
  | none =>
    cases stored : pc (label key) with
    | none => rfl
    | some digest =>
      obtain ⟨other,cached,same⟩ := related.backward _ _ stored
      have keys := injective other key digest answer (extension other digest cached) present same
      subst other
      rw [hit] at cached
      cases cached

 theorem Related.put {label : B → A} {pc : Cache A} {qc final : Cache B}
    (related : Related label pc qc) (extension : Extends qc final)
    (injective : InjectiveOn label final) {key : B} {answer : Digest32}
    (present : final key=some answer) :
    Related label (put pc (label key) answer) (put qc key answer) := by
  constructor
  · intro other digest stored
    by_cases same : other=key
    · subst other
      rw [put_self] at stored
      cases stored
      exact put_self _ _ _
    · rw [put_other _ _ _ _ same] at stored
      have unequal : label other ≠ label key := by
        intro nodes
        exact same (injective other key digest answer (extension other digest stored) present nodes)
      rw [put_other _ _ _ _ unequal]
      exact related.forward other digest stored
  · intro node digest stored
    by_cases same : node=label key
    · subst node
      rw [put_self] at stored
      cases stored
      exact ⟨key,put_self _ _ _,rfl⟩
    · rw [put_other _ _ _ _ same] at stored
      obtain ⟨other,cached,nodes⟩ := related.backward node digest stored
      have unequal : other ≠ key := by
        intro equal
        subst other
        exact same nodes.symm
      exact ⟨other,by rw [put_other _ _ _ _ unequal]; exact cached,nodes⟩

 theorem extends_put {qc final : Cache B} (extension : Extends qc final)
    {key : B} {answer : Digest32} (present : final key=some answer) :
    Extends (put qc key answer) final := by
  intro other digest stored
  by_cases same : other=key
  · subst other
    rw [put_self] at stored
    cases stored
    exact present
  · rw [put_other _ _ _ _ same] at stored
    exact extension other digest stored

#print axioms Related.lookup
#print axioms Related.put
end Whir.PublicCompressionCouplingRelabelCache
