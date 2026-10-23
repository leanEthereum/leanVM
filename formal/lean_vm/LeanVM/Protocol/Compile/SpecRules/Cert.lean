/-
  LeanVM.Protocol.Compile.SpecRules.Cert

  The doom certificate of a whole verifier program from a specification of it.
-/

module

public import LeanVM.Protocol.Compile.SpecRules.Bind

/-!
# From a specification to a doom certificate

A specification `S : Spec P (fun _ ↦ False) (fun b _ ↦ b = false) εmax L 0` of a whole verifier
program `P : Prog Bool` (no follower; the postcondition is rejection; the precondition is
discharged at the start by hand) is a doom certificate `S.toCert` with doom `S.D []` and the
escape bound of the group at `h` the potential `S.V [] h` (where `h` is a reachable boundary in
doom, `0` elsewhere). The certificate's escape bounds, discounted by the proof of work before
each group, are at most `εmax` (`Spec.toCert_bound`), given the start group's bound.
`Spec.toCertOfLead` takes instead a specification from the empty history with lead at most
`εmax`.

The core is `Spec.esc_le`: from a reachable history, the probability that the group escapes doom
is at most the potential, because the potential is a supermartingale over the challenges, does
not grow at openings, and is `1` wherever the group ends outside doom (`moveEnd`, `retEnd`); a
rejection, a `false` verdict, and an opening of a missing commitment escape nothing.
-/

namespace LeanVM.Protocol.Compile

open LeanVM.Parameters Prog

@[expose] public section

namespace Spec

variable {P : Prog Bool} {εmax L : ENNReal}

/-- The escape probability of a group is at most the potential. -/
theorem esc_le (S : Spec P (fun _ ↦ False) (fun b _ ↦ b = false) εmax L 0) :
    ∀ (q : Prog Bool) {l : List Ev}, P.Reachable l → P.after l = some q →
      esc (S.D []) l q ≤ S.V [] l
  | .ret true, l, hl, ha => by
    simp only [esc]
    split_ifs with hD
    · exact zero_le
    · exact S.retEnd (reach_nil_iff.2 hl) ha hD
  | .ret false, l, _, _ => by simp [esc]
  | .fail, l, _, _ => by simp [esc]
  | .read k, l, hl, ha => by
    simp only [esc]
    split_ifs with hD
    · exact zero_le
    · exact S.moveEnd (reach_nil_iff.2 hl) ha trivial hD
  | .grind b k, l, hl, ha => by
    simp only [esc]
    split_ifs with hD
    · exact zero_le
    · exact S.moveEnd (reach_nil_iff.2 hl) ha trivial hD
  | .commit ht w k, l, hl, ha => by
    simp only [esc]
    split_ifs with hD
    · exact zero_le
    · exact S.moveEnd (reach_nil_iff.2 hl) ha trivial hD
  | .sample k, l, hl, ha => by
    simp only [esc]
    calc (Fintype.card E : ENNReal)⁻¹ * ∑ c : E, esc (S.D []) (l ++ [Ev.sample c]) (k c)
        ≤ (Fintype.card E : ENNReal)⁻¹ * ∑ c : E, S.V [] (l ++ [Ev.sample c]) := by
          gcongr with c
          exact esc_le S (k c) (.sample c hl ha) (by rw [after_snoc _ ha]; simp [after])
      _ ≤ S.V [] l := S.sample (reach_nil_iff.2 hl) ha
  | .query i ps k, l, hl, ha => by
    simp only [esc]
    split
    · rename_i rows hans
      exact (esc_le S (k rows) (.query hl ha hans) (by rw [after_snoc _ ha]; simp [after])).trans
        (S.query (reach_nil_iff.2 hl) ha (by simpa using hans))
    · exact zero_le

open Classical in
/-- The escape bound of the certificate: the potential at a reachable boundary in doom. -/
noncomputable def certε (S : Spec P (fun _ ↦ False) (fun b _ ↦ b = false) εmax L 0)
    (h : List Ev) : ENNReal :=
  if P.Reachable h ∧ Boundary h ∧ S.D [] h then S.V [] h else 0

/-- **The doom certificate of a specification** of a whole program: doom `S.D []`, escape bound
the potential at reachable boundaries in doom. -/
noncomputable def toCert (S : Spec P (fun _ ↦ False) (fun b _ ↦ b = false) εmax L 0) :
    Cert P where
  D := S.D []
  ε := certε S
  read x hl ha hD := S.read x (reach_nil_iff.2 hl) ha hD
  grind hl ha hD := S.grind (reach_nil_iff.2 hl) ha hD
  commit word hl ha hw hD := S.commit word (reach_nil_iff.2 hl) ha hw hD
  group {h p} hl hb ha _ hD := by
    have hc : P.Reachable h ∧ Boundary h ∧ S.D [] h := ⟨hl, hb, hD⟩
    simp only [certε, hc]
    exact esc_le S p hl ha
  final hl ha hD := by simpa using S.post (reach_nil_iff.2 hl) ha hD

/-- The doom of the certificate is the specification's from the empty history. -/
theorem toCert_D (S : Spec P (fun _ ↦ False) (fun b _ ↦ b = false) εmax L 0) :
    S.toCert.D = S.D [] := rfl

open Classical in
/-- The escape bound of the certificate. -/
theorem toCert_ε (S : Spec P (fun _ ↦ False) (fun b _ ↦ b = false) εmax L 0) (h : List Ev) :
    S.toCert.ε h = if P.Reachable h ∧ Boundary h ∧ S.D [] h then S.V [] h else 0 := rfl

/-- **The certificate's bound**: every escape bound, discounted by the proof of work before its
group, is at most `εmax`, given the bound of the start group. -/
theorem toCert_bound (S : Spec P (fun _ ↦ False) (fun b _ ↦ b = false) εmax L 0)
    (hstart : S.D [] [] → S.V [] [] ≤ εmax) (h : List Ev) :
    (2 : ENNReal)⁻¹ ^ grindBits h * S.toCert.ε h ≤ εmax := by
  rw [toCert_ε]
  split_ifs with hc
  · obtain ⟨hl, hb, hD⟩ := hc
    rcases eq_or_ne h [] with rfl | hne
    · simpa [grindBits] using hstart hD
    · exact S.bound (reach_nil_iff.2 hl) hne ((endsMove_iff_boundary hne).2 hb) hD
  · simp

/-- The specification of a whole program from the empty history, as one from no history. -/
noncomputable def ofStart (S : Spec P (fun h ↦ h = []) (fun b _ ↦ b = false) εmax L 0) :
    Spec P (fun _ ↦ False) (fun b _ ↦ b = false) εmax L 0 :=
  S.mono (fun _ h ↦ h.elim) (fun _ _ h ↦ h) le_rfl le_rfl le_rfl

/-- **The doom certificate of a specification from the empty history**. -/
noncomputable def toCertOfLead (S : Spec P (fun h ↦ h = []) (fun b _ ↦ b = false) εmax L 0) :
    Cert P :=
  S.ofStart.toCert

/-- The doom of `toCertOfLead`. -/
theorem toCertOfLead_D (S : Spec P (fun h ↦ h = []) (fun b _ ↦ b = false) εmax L 0) :
    S.toCertOfLead.D = S.D [] := rfl

/-- **The certificate's bound** from a lead at most `εmax`. -/
theorem toCertOfLead_bound (S : Spec P (fun h ↦ h = []) (fun b _ ↦ b = false) εmax L 0)
    (hL : L ≤ εmax) (h : List Ev) :
    (2 : ENNReal)⁻¹ ^ grindBits h * S.toCertOfLead.ε h ≤ εmax :=
  S.ofStart.toCert_bound (fun _ ↦ (S.start_V [] rfl).trans hL) h

end Spec

end
end LeanVM.Protocol.Compile
