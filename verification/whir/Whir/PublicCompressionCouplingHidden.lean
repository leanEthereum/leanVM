import Whir.PublicCompressionCouplingInspection
import Whir.PublicCompressionCouplingTargets

/-! The actual pinned simulator's hidden-forward-guess event. Public chosen
chaining values are retained, not excluded. Fresh hidden prefix answers are
sampled from the residual of the same seed table that served public requests. -/
namespace Whir.PublicCompressionCouplingMixed
open FiatShamirGame DuplexRefinement DuplexFraming DuplexModeGame TypedOracleCompiler
open TypedFiatShamirGame RawOracleCoupling

@[instance_reducible]
noncomputable def mixedKeyFintype (Q : Nat) : Fintype (Key Q) := by
  letI := rawKeyFintype Q
  infer_instance

noncomputable def publicCVTargets : List Observation → Finset Digest32
  | [] => ∅
  | observation :: rest => match observation.query with
    | .primitive _ node => insert node.cv (publicCVTargets rest)
    | .construction _ _ => publicCVTargets rest

 theorem publicCVTargets_card (observations : List Observation) :
    (publicCVTargets observations).card ≤
      (observations.map (fun observation => observation.query.cost)).sum := by
  classical
  induction observations with
  | nil => simp [publicCVTargets]
  | cons observation rest ih =>
    have ih' := ih
    simp only [Query.cost] at ih'
    cases query : observation.query with
    | primitive purpose node =>
      simp only [publicCVTargets,query,List.map_cons,List.sum_cons,Query.cost]
      have hc := Finset.card_insert_le node.cv (publicCVTargets rest)
      omega
    | construction coordinate valid =>
      simp only [publicCVTargets,query,List.map_cons,List.sum_cons,Query.cost]
      omega

def certifiedPublic {R : Type} (Q : Nat) (iv : Digest32) (p : Program R)
    (counted : Counts Q p) : Computation Q {view : View R // viewCost view ≤ Q} Q :=
  Computation.certify (compile Q iv [] p Q (by rfl) counted)
    (compile_every_viewCost Q iv [] p Q (by rfl) counted)

def privateInspection {R : Type} (Q : Nat) (iv : Digest32)
    (view : {view : View R // viewCost view ≤ Q}) :
    Computation Q (List InspectedConstruction) Q :=
  Sampling.pad (le_trans (inspectionCost_le view.val.observations) view.property)
    (inspect Q iv view.val.observations)

open Classical in
noncomputable def hiddenGuess {R : Type} (Q : Nat) (iv : Digest32) (p : Program R)
    (counted : Counts Q p) (table : Key Q → Digest32) : Bool :=
  let result := Sampling.eval table (memo (certifiedPublic Q iv p counted) (fun _ => none))
  PublicCompressionCouplingTargets.alarm table (publicCVTargets result.1.val.observations)
    (privateInspection Q iv result.1) result.2

open Classical in
/-- A derived bound from actual conditional uniform table sampling, not an
assumed missed-recognition certificate. Every adaptive continuation is covered. -/
theorem actual_hiddenGuess_probability {R : Type} (Q : Nat) (iv : Digest32)
    (p : Program R) (counted : Counts Q p) :
    letI := mixedKeyFintype Q
    average (fun table : Key Q → Digest32 =>
      if hiddenGuess Q iv p counted table then (1:ℚ) else 0) ≤
      min 1 ((Q:ℚ)*Q/2^256) := by
  let _ := mixedKeyFintype Q
  apply le_min
  · calc
      _ ≤ average (fun _ : Key Q → Digest32 => (1:ℚ)) := by
        apply average_mono
        intro table
        split <;> norm_num
      _ = 1 := average_const _
  · exact PublicCompressionCouplingTargets.adaptive_posthoc_bound
      (certifiedPublic Q iv p counted) (privateInspection Q iv)
      (fun view => publicCVTargets view.val.observations)
      (fun view => le_trans (publicCVTargets_card _) view.property)

#print axioms publicCVTargets_card
#print axioms actual_hiddenGuess_probability
end Whir.PublicCompressionCouplingMixed
