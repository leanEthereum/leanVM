/-
  LeanVM.Protocol.EndToEnd.Front.BusDoom

  Doom on a relation: no candidate oracle puts the statement in the relation. The escape of a
  challenge from it, bounded through a component's security and a union bound over the
  candidates, in the form the calculus of verifier programs takes it.
-/

module

public import LeanVM.Protocol.ToArkLib.Typed.SampleChallenge
public import LeanVM.Protocol.ToArkLib.Typed.SendChecked
public import VCVio.OracleComp.Constructions.SampleableType.Measure
public import LeanVM.Protocol.Field

/-!
# Doom on a relation

A front phase's security is appended from one-round components on ArkLib's typed framework, a
checked message (`Typed.sendChecked`) or a checked challenge (`Typed.sampleChallenge`), each
between two relations on `(statement, oracles)`. The verifier program carries the statement in
its variables (the GKR state, the sumcheck's claim and point), so its doom after a sub-program can
be stated on the component's relation: `RelDoom C R x`, no oracle `o` of the candidate set `C` has
`((x, o), ()) ∈ R`. A prover message that passes its check keeps it (`say_keep`, from any
security of the message by `Typed.sendChecked_reflect`), and a challenge escapes it, over the
candidates, with probability at most `|C|` times the component's error (`draw_escape_le`, from
any security of the challenge by `Typed.sample_escape`): the count of bad challenges that
`Spec.sampleE` asks for.
-/

namespace LeanVM.Protocol.EndToEnd.Front

open LeanVM.Parameters LeanVM.Protocol OracleComp OracleSpec
open scoped NNReal ENNReal

@[expose] public section

/-- **Doom on a relation**: no candidate oracle puts the statement in the relation. -/
def RelDoom {S : Type} {ι : Type} {O : ι → Type} (C : Set (∀ i, O i))
    (R : Set ((S × ∀ i, O i) × Unit)) (x : S) : Prop :=
  ∀ o ∈ C, ((x, o), ()) ∉ R

/-- A challenge event's probability is the fraction of the challenges in it. -/
theorem prEvent_uniform_E (p : E → Prop) [DecidablePred p] :
    Pr{let c ← $ᵗ E}[p c] =
      (Fintype.card E : ℝ≥0∞)⁻¹ * ((Finset.univ.filter p).card : ℝ≥0∞) := by
  rw [SampleableType.prEvent_uniformSample, div_eq_mul_inv, mul_comm]

open Classical in
/-- **The union bound over candidates**, counted: the challenges bad for some of at most `L₀`
candidates, each bad for at most a fraction `e` of the challenges, are at most a fraction
`L₀ · e`. -/
theorem card_exists_le {β : Type} {C : Set β} (hfin : C.Finite) {L₀ : ℕ} (hcard : C.ncard ≤ L₀)
    (P : β → E → Prop) {e : ℝ≥0∞}
    (h : ∀ q ∈ C, (Fintype.card E : ℝ≥0∞)⁻¹ *
      ((Finset.univ.filter fun c ↦ P q c).card : ℝ≥0∞) ≤ e) :
    (Fintype.card E : ℝ≥0∞)⁻¹ *
        ((Finset.univ.filter fun c ↦ ∃ q ∈ C, P q c).card : ℝ≥0∞) ≤ L₀ * e := by
  classical
  let s := hfin.toFinset
  have hsub : (Finset.univ.filter fun c ↦ ∃ q ∈ C, P q c) ⊆
      s.biUnion fun q ↦ Finset.univ.filter fun c ↦ P q c := by
    intro c hc
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hc
    obtain ⟨q, hq, hp⟩ := hc
    exact Finset.mem_biUnion.mpr ⟨q, hfin.mem_toFinset.mpr hq, by simpa using hp⟩
  calc (Fintype.card E : ℝ≥0∞)⁻¹ * ((Finset.univ.filter fun c ↦ ∃ q ∈ C, P q c).card : ℝ≥0∞)
      ≤ (Fintype.card E : ℝ≥0∞)⁻¹ *
          ∑ q ∈ s, ((Finset.univ.filter fun c ↦ P q c).card : ℝ≥0∞) := by
        gcongr
        exact_mod_cast (Finset.card_le_card hsub).trans Finset.card_biUnion_le
    _ = ∑ q ∈ s, (Fintype.card E : ℝ≥0∞)⁻¹ *
          ((Finset.univ.filter fun c ↦ P q c).card : ℝ≥0∞) := Finset.mul_sum _ _ _
    _ ≤ ∑ _q ∈ s, e := Finset.sum_le_sum fun q hq ↦ h q (hfin.mem_toFinset.mp hq)
    _ = s.card * e := by rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ L₀ * e := by
        gcongr
        rw [← Set.ncard_eq_toFinset_card C hfin]
        exact_mod_cast hcard

section Say

variable {S T : Type} {ι : Type} {O : ι → Type} {M : Type} {honest : (S × ∀ i, O i) × Unit → M}
  {chk : S → M → Bool} {f : S → M → T}
  {relIn : Set ((S × ∀ i, O i) × Unit)} {relOut : Set ((T × ∀ i, O i) × Unit)}
  {err : Typed.Errors (Typed.sayTree M) (Typed.sayRoles M)}

/-- **A checked message keeps doom**: a message that passes the check carries a doomed statement
to a doomed statement. -/
theorem say_keep (Sec : Typed.Security (Typed.sendChecked O M honest chk f) relIn relOut err)
    {C : Set (∀ i, O i)} {s : S} (hpre : RelDoom C relIn s) (m : M) (hchk : chk s m = true) :
    RelDoom C relOut (f s m) := fun o ho hout ↦ by
  obtain ⟨w, hw⟩ := Typed.sendChecked_reflect Sec s o m hchk () hout
  cases w
  exact hpre o ho hw

end Say

section Draw

variable {S T : Type} {ι : Type} {O : ι → Type} {chk : S → Bool} {f : S → E → T}
  {relIn : Set ((S × ∀ i, O i) × Unit)} {relOut : Set ((T × ∀ i, O i) × Unit)} {e : ℝ≥0}

open Classical in
/-- **A challenge escapes doom** with probability at most `L₀` times the component's error, over
at most `L₀` candidates: the challenges that pass the check and carry the statement into the
output relation for some candidate. -/
theorem draw_escape_le
    (Sec : Typed.Security (Typed.sampleChallenge O E chk f) relIn relOut (Typed.drawErrors E e))
    {C : Set (∀ i, O i)} (hfin : C.Finite) {L₀ : ℕ} (hcard : C.ncard ≤ L₀) {s : S}
    (hpre : RelDoom C relIn s) (hchk : chk s = true) :
    (Fintype.card E : ℝ≥0∞)⁻¹ *
        ((Finset.univ.filter fun c ↦ ¬ RelDoom C relOut (f s c)).card : ℝ≥0∞) ≤ L₀ * e := by
  classical
  have hev : (Finset.univ.filter fun c ↦ ¬ RelDoom C relOut (f s c)) =
      Finset.univ.filter fun c ↦ ∃ o ∈ C, ((f s c, o), ()) ∈ relOut := by
    ext c
    simp [RelDoom]
  rw [hev]
  refine card_exists_le hfin hcard (fun o c ↦ ((f s c, o), ()) ∈ relOut) fun o ho ↦ ?_
  have h := Typed.sample_escape Sec s o (fun w hw ↦ by cases w; exact hpre o ho hw) hchk
  rw [← prEvent_uniform_E]
  exact le_trans (prEvent_mono _ _ _ fun c hc ↦ ⟨(), hc⟩) h

end Draw

end
end LeanVM.Protocol.EndToEnd.Front
