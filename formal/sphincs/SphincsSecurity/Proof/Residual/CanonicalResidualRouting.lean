import SphincsSecurity.Proof.Base.Prelude
import SphincsSecurity.Proof.Residual.CanonicalResidualQuery
namespace SphincsSecurity.Concrete.CanonicalProbeRouting

open _root_.OracleComp HiddenLabelObservation
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

noncomputable def tableReply (parameter : PublicParameter) (actual : Labels)
    (replies : CanonicalGraphLabels) (outside : QueryImpl HashSpec Id) (input : HashInput) : HashOutput :=
  (decodePosition parameter input).elim (outside input)
    (fun position => if input = inputOf parameter actual position then replies position else outside input)

theorem tableReply_programmed (parameter : PublicParameter)
    (otsSecret : Layer → TreeIndex → LeafIndex → ChainIndex → Digest)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (replies : CanonicalGraphLabels)
    (outside : QueryImpl HashSpec Id) (input : HashInput) :
    tableReply parameter (CanonicalCoordinate.value otsSecret ftsSecret replies) replies outside input =
      programmedHash parameter otsSecret ftsSecret replies outside input := by
  simp only [tableReply, programmedHash, inputOf_canonical]

noncomputable def stoppedTableReply (parameter : PublicParameter) (words : OtsReferenceWords)
    (disclosed : Index → FtsTree → FtsLeaf → Prop) (actual : Labels)
    (replies : CanonicalGraphLabels) (outside : QueryImpl HashSpec Id) (input : HashInput) : Option HashOutput :=
  let answer := tableReply parameter actual replies outside input
  if Bad parameter words disclosed actual input answer then none else some answer

noncomputable def routedTableReply (publicReplies : CanonicalGraphLabels) (actual : Labels)
    (outside : QueryImpl HashSpec Id) (input : HashInput) : Route → Option HashOutput
  | .outside => some (outside input)
  | .canonical position => some (publicReplies position)
  | .probe test => if test.keep actual (outside input) then some (outside input) else none

theorem stoppedTableReply_eq_routed (parameter : PublicParameter) (words : OtsReferenceWords)
    (disclosed : Index → FtsTree → FtsLeaf → Prop) (actual : Labels)
    (replies publicReplies : CanonicalGraphLabels)
    (hreplies : ∀ position, ¬CanonicalCoordinate.Hidden words disclosed (.graph position) →
      publicReplies position = replies position)
    (outside : QueryImpl HashSpec Id) (input : HashInput) (routing : Route)
    (hspec : RouteSpec parameter words disclosed actual input routing) :
    stoppedTableReply parameter words disclosed actual replies outside input =
      routedTableReply publicReplies actual outside input routing := by
  have hsafe := safe_iff_not_bad parameter words disclosed actual input routing hspec
  cases routing with
  | outside =>
      have hdecode := (decodePosition_none_iff parameter input).mpr hspec
      have hbad : ¬Bad parameter words disclosed actual input (outside input) :=
        (hsafe (outside input)).mp trivial
      simp only [stoppedTableReply, tableReply, hdecode, Option.elim_none, if_neg hbad, routedTableReply]
  | canonical position =>
      obtain ⟨hat, hinput, hpublic⟩ := hspec
      have hdecode := (decodePosition_some_iff parameter input position).mpr hat
      have hbad : ¬Bad parameter words disclosed actual input (replies position) :=
        (hsafe (replies position)).mp trivial
      have hreply := hreplies position (parent_public_of_no_hidden_child words disclosed position hpublic)
      simp only [stoppedTableReply, tableReply, hdecode, Option.elim_some, if_pos hinput,
        if_neg hbad, routedTableReply, hreply]
  | probe test =>
      cases test with
      | pair child parent hne candidate =>
          obtain ⟨position, hat, rfl, hslot, hhidden, hinput⟩ := hspec
          have hdecode := (decodePosition_some_iff parameter input position).mpr hat
          have heq : input = inputOf parameter actual position ↔ candidate = actual child := by
            rw [hinput, unary_eq_inputOf_iff parameter actual position child hslot candidate]
          by_cases hcanonical : input = inputOf parameter actual position
          · have hbad : Bad parameter words disclosed actual input (replies position) := by
              refine ⟨position, hat, Or.inl ⟨?_, hcanonical⟩⟩
              exact ⟨child, by rw [hslot]; exact List.mem_singleton_self _, hhidden⟩
            simp only [stoppedTableReply, tableReply, hdecode, Option.elim_some, if_pos hcanonical,
              if_pos hbad, routedTableReply, Probe.keep, heq.mp hcanonical, ne_eq, not_true_eq_false, false_and, if_false]
          · have hkeep := hsafe (outside input)
            change Probe.keep (.pair child (.graph position) hne candidate) actual (outside input) ↔
              ¬Bad parameter words disclosed actual input (outside input) at hkeep
            simp only [stoppedTableReply, tableReply, hdecode, Option.elim_some, if_neg hcanonical, routedTableReply]
            by_cases hk : Probe.keep (.pair child (.graph position) hne candidate) actual (outside input)
            · rw [if_pos hk, if_neg (hkeep.mp hk)]
            · rw [if_neg hk, if_pos (not_not.mp (fun hn => hk (hkeep.mpr hn)))]
      | output parent =>
          obtain ⟨position, hat, rfl, hinput⟩ := hspec
          have hdecode := (decodePosition_some_iff parameter input position).mpr hat
          have hkeep := hsafe (outside input)
          change Probe.keep (.output (.graph position)) actual (outside input) ↔
            ¬Bad parameter words disclosed actual input (outside input) at hkeep
          simp only [stoppedTableReply, tableReply, hdecode, Option.elim_some, if_neg hinput, routedTableReply]
          by_cases hk : Probe.keep (.output (.graph position)) actual (outside input)
          · rw [if_pos hk, if_neg (hkeep.mp hk)]
          · rw [if_neg hk, if_pos (not_not.mp (fun hn => hk (hkeep.mpr hn)))]

theorem stoppedTableReply_route (parameter : PublicParameter) (words : OtsReferenceWords)
    (disclosed : Index → FtsTree → FtsLeaf → Prop) (known actual : Labels)
    (hagrees : PublicAgreement words disclosed known actual)
    (replies publicReplies : CanonicalGraphLabels)
    (hreplies : ∀ position, ¬CanonicalCoordinate.Hidden words disclosed (.graph position) →
      publicReplies position = replies position)
    (outside : QueryImpl HashSpec Id) (input : HashInput) :
    stoppedTableReply parameter words disclosed actual replies outside input =
      routedTableReply publicReplies actual outside input (route parameter words disclosed known input) :=
  stoppedTableReply_eq_routed parameter words disclosed actual replies publicReplies hreplies outside input _
    (route_spec parameter words disclosed known actual hagrees input)

end SphincsSecurity.Concrete.CanonicalProbeRouting
