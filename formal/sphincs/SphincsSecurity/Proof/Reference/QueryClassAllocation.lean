import SphincsSecurity.Proof.Reference.BoundaryChargePartition
import SphincsSecurity.Proof.Ots.OtsPrefixAllocation
namespace SphincsSecurity.Concrete.QueryClass

open _root_.OracleComp OracleSpec
set_option backward.isDefEq.respectTransparency false

def EncodingHash (parameter : PublicParameter) : OracleWorld.Domain → Prop
  | .inl _ => False
  | .inr input => ∃ position, AtEncodingPosition parameter input position

def OtherHash (parameter : PublicParameter) (words : OtsReferenceWords) (input : OracleWorld.Domain) : Prop :=
  CausalFrontierProgram.NonmessageHash parameter input ∧ ¬EncodingHash parameter input ∧
    ∀ address, ¬(OtsPrefix.atAddress parameter words address).Selects input

noncomputable instance (parameter : PublicParameter) : DecidablePred (EncodingHash parameter) := Classical.decPred _
noncomputable instance (parameter : PublicParameter) (words : OtsReferenceWords) : DecidablePred (OtherHash parameter words) :=
  Classical.decPred _

theorem encoding_nonmessage (parameter : PublicParameter) (input : OracleWorld.Domain) (hencoding : EncodingHash parameter input) :
    CausalFrontierProgram.NonmessageHash parameter input := by
  cases input with
  | inl input => exact False.elim hencoding
  | inr input =>
      obtain ⟨position, payload, hinput⟩ := hencoding
      rintro ⟨message, hmessage⟩
      have hdomain := (tweakableHashInput_injective parameter (by trivial) (by trivial) (hinput.symm.trans hmessage.symm)).1
      simp only [EncodingPosition.domain, reduceCtorEq] at hdomain

theorem prefix_nonmessage (segment : OtsPrefix) (input : OracleWorld.Domain) (hprefix : segment.Selects input) :
    CausalFrontierProgram.NonmessageHash segment.parameter input := by
  cases input with
  | inl input => exact False.elim hprefix
  | inr input =>
      obtain ⟨query, hquery⟩ := Option.ne_none_iff_exists'.mp hprefix
      have hinput := (segment.parse_some_iff input query).mp hquery
      rintro ⟨message, hmessage⟩
      have hdomain := (tweakableHashInput_injective segment.parameter (by trivial) (by trivial)
        (hinput.symm.trans hmessage.symm)).1
      simp only [reduceCtorEq] at hdomain

theorem prefix_not_encoding (segment : OtsPrefix) (input : OracleWorld.Domain) (hprefix : segment.Selects input) :
    ¬EncodingHash segment.parameter input := by
  cases input with
  | inl input => exact False.elim hprefix
  | inr input =>
      obtain ⟨query, hquery⟩ := Option.ne_none_iff_exists'.mp hprefix
      have hinput := (segment.parse_some_iff input query).mp hquery
      rintro ⟨position, hencoding⟩
      exact hencoding.not_atPosition (.chain segment.lay segment.tree segment.leaf segment.chainIdx (segment.step query.1))
        ⟨digestBytes query.2, hinput⟩

theorem allocation_step (parameter : PublicParameter) (words : OtsReferenceWords) (input : OracleWorld.Domain) :
    (∑ address : OtsPrefix.ChainAddress, if (OtsPrefix.atAddress parameter words address).Selects input then 1 else 0) +
        (if EncodingHash parameter input then 1 else 0) + (if OtherHash parameter words input then 1 else 0) =
      if CausalFrontierProgram.NonmessageHash parameter input then 1 else 0 := by
  classical
  by_cases hprefix : ∃ address, (OtsPrefix.atAddress parameter words address).Selects input
  · obtain ⟨address, haddress⟩ := hprefix
    have hsum : (∑ other : OtsPrefix.ChainAddress, if (OtsPrefix.atAddress parameter words other).Selects input then 1 else 0) = 1 := by
      rw [Finset.sum_eq_single address]
      · exact if_pos haddress
      · intro other _ hne
        exact if_neg (fun hother => hne (OtsPrefix.atAddress_selects_unique parameter words other address input hother haddress))
      · simp
    have hn := prefix_nonmessage _ input haddress
    have he := prefix_not_encoding _ input haddress
    have ho : ¬OtherHash parameter words input := fun h => h.2.2 address haddress
    simp only [hsum, if_neg he, if_neg ho, if_pos hn, Nat.add_zero]
  · have hnone : ∀ address, ¬(OtsPrefix.atAddress parameter words address).Selects input := by simpa using hprefix
    have hsum : (∑ address : OtsPrefix.ChainAddress, if (OtsPrefix.atAddress parameter words address).Selects input then 1 else 0) = 0 := by
      simp only [hnone, if_false, Finset.sum_const_zero]
    rw [hsum, Nat.zero_add]
    by_cases he : EncodingHash parameter input
    · have hn := encoding_nonmessage parameter input he
      simp only [he, hn, OtherHash, not_true_eq_false, and_false, false_and, if_true, if_false, Nat.add_zero]
    · by_cases hn : CausalFrontierProgram.NonmessageHash parameter input <;>
        simp [he, hn, OtherHash, hnone]

theorem allocation_calls (parameter : PublicParameter) (words : OtsReferenceWords) (inputs : List OracleWorld.Domain) :
    (∑ address : OtsPrefix.ChainAddress, QueryCap.calls (OtsPrefix.atAddress parameter words address).Selects inputs) +
        QueryCap.calls (EncodingHash parameter) inputs + QueryCap.calls (OtherHash parameter words) inputs =
      QueryCap.calls (CausalFrontierProgram.NonmessageHash parameter) inputs := by
  induction inputs with
  | nil => simp only [QueryCap.calls_nil, Finset.sum_const_zero, Nat.add_zero]
  | cons input inputs ih =>
      simp only [QueryCap.calls_cons, Finset.sum_add_distrib]
      have h := allocation_step parameter words input
      omega

end SphincsSecurity.Concrete.QueryClass
