/-
  LeanVM.Guest.B1.Tables.VerifyTablesCTail

  `verify_tables`' completeness: the final check, `rm`, the public input's claims and the returns.
-/

module

public import LeanVM.Guest.B1.Tables.VerifyTablesFwdI
public import LeanVM.Guest.B1.Tables.VerifyTablesTail

/-!
# The tail, forward (G:1812-1824)

`vtPre`'s statements `7854 ..< 7899` as items (`vtItTail`), values `8140 ..< 8179`. `vt_c_tail`:
with the accumulated terms equal to the sumcheck's claim, the state of `cvR` at `(7569, 7570)`,
both public words canonical and the memory holding their lines at `rm` in the pool, the window
completes, returning the squeezed state, `g^n`'s cursor offset, the bytecode share and `rm`.
-/

namespace LeanVM.Guest.B1.VerifySub

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.Blake2sHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Guest.B1.Sig

@[expose] public section

/-- `vtPre`'s statements `7854 ..< 7899` as items. -/
def vtItTail : List FItem :=
  [.atom (.assertEq (.n 8139) (.n 4652)),
    .sq (.n 7569) (.n 7570) 8140,
    .hint (.limbs (.n 3) [.n 8154]),
    .atom (.add (.n 8155) (.n 3) (.n 8154)),
    .atom (.const (.n 8156) (word 1 0 1)),
    .atom (.mul (.n 8157) (.n 8155) (.n 8156)),
    .atom (.assertInK (.n 8154) (.n 8157)),
    .atom (.copy (.n 8158) (.n 8154)),
    .hint (.limbs (.n 4) [.n 8159]),
    .atom (.add (.n 8160) (.n 4) (.n 8159)),
    .atom (.const (.n 8161) (word 1 0 1)),
    .atom (.mul (.n 8162) (.n 8160) (.n 8161)),
    .atom (.assertInK (.n 8159) (.n 8162)),
    .atom (.copy (.n 8163) (.n 8159)),
    .atom (.add (.n 8164) (.n 8158) (.n 8163)),
    .atom (.mul (.n 8165) (.n 8153) (.n 8164)),
    .atom (.add (.n 8166) (.n 8158) (.n 8165)),
    .atom (.load (.n 8166) (.n 13) 109),
    .atom (.add (.n 8167) (.n 8157) (.n 8162)),
    .atom (.mul (.n 8168) (.n 8153) (.n 8167)),
    .atom (.add (.n 8169) (.n 8157) (.n 8168)),
    .atom (.load (.n 8169) (.n 13) 110),
    .atom (.const (.n 8170) (word 0 0 0)),
    .atom (.load (.n 8170) (.n 13) 111),
    .atom (.copy (.n 8171) (.n 8145)),
    .atom (.copy (.n 8172) (.n 8146)),
    .atom (.const (.n 8173) (word 29686813949952 0 0)),
    .atom (.mul (.n 8174) (.n 4651) (.n 8173)),
    .atom (.copy (.n 8175) (.n 8174)),
    .atom (.copy (.n 8176) (.n 4554)),
    .atom (.copy (.n 8177) (.n 1732)),
    .atom (.copy (.n 8178) (.n 8153))]

set_option maxRecDepth 100000 in
theorem vtItTail_eq : vtItTail.flatMap FItem.stmts = (vtPre.drop 7854).take 45 :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem vtItTail_ok : fOkI 8140 8179 [] vtItTail = true := by decide +kernel

/-- Its obligations. -/
def vtItTailOb : List IOb :=
  [.ob (.holds (.assertEq (.n 8139) (.n 4652))),
    .sq (.n 7569) (.n 7570),
    .ob (.holds (.assertInK (.n 8154) (.n 8157))),
    .ob (.holds (.assertInK (.n 8159) (.n 8162))),
    .ob (.holds (.load (.n 8166) (.n 13) 109)),
    .ob (.holds (.load (.n 8169) (.n 13) 110)),
    .ob (.holds (.load (.n 8170) (.n 13) 111))]

set_option maxRecDepth 100000 in
theorem vtItTail_obs : iObs 8140 [] vtItTail = vtItTailOb := listEqb_sound iobEqb_sound (by decide +kernel)

/-- Its definitions. -/
def vtItTailEq : List FEq :=
  [.item (.sq (.n 7569) (.n 7570) 8140),
    .item (.hint (.limbs (.n 3) [.n 8154])),
    .def (.add (.n 8155) (.n 3) (.n 8154)),
    .def (.const (.n 8156) (word 1 0 1)),
    .def (.mul (.n 8157) (.n 8155) (.n 8156)),
    .def (.copy (.n 8158) (.n 8154)),
    .item (.hint (.limbs (.n 4) [.n 8159])),
    .def (.add (.n 8160) (.n 4) (.n 8159)),
    .def (.const (.n 8161) (word 1 0 1)),
    .def (.mul (.n 8162) (.n 8160) (.n 8161)),
    .def (.copy (.n 8163) (.n 8159)),
    .def (.add (.n 8164) (.n 8158) (.n 8163)),
    .def (.mul (.n 8165) (.n 8153) (.n 8164)),
    .def (.add (.n 8166) (.n 8158) (.n 8165)),
    .def (.add (.n 8167) (.n 8157) (.n 8162)),
    .def (.mul (.n 8168) (.n 8153) (.n 8167)),
    .def (.add (.n 8169) (.n 8157) (.n 8168)),
    .def (.const (.n 8170) (word 0 0 0)),
    .def (.copy (.n 8171) (.n 8145)),
    .def (.copy (.n 8172) (.n 8146)),
    .def (.const (.n 8173) (word 29686813949952 0 0)),
    .def (.mul (.n 8174) (.n 4651) (.n 8173)),
    .def (.copy (.n 8175) (.n 8174)),
    .def (.copy (.n 8176) (.n 4554)),
    .def (.copy (.n 8177) (.n 1732)),
    .def (.copy (.n 8178) (.n 8153))]

set_option maxRecDepth 100000 in
theorem vtItTail_eqsB : vtItTailEq.all (fun e => (fEqs 8140 [] vtItTail).any (feqEqb e)) = true := by
  decide +kernel

/-- The tail's oracle: the two public words' low limbs. -/
noncomputable def vtHvTail (w3 w4 : E) (k : ℕ) : E :=
  if k = 8154 then ofK (w3.limb 0) else if k = 8159 then ofK (w4.limb 0) else 0

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
/-- **The tail completes.** -/
theorem vt_c_tail {rd : Reader} {σ : Val} {cvR : Digest}
    (hcv : (σ (.n 7569), σ (.n 7570)) = digestScalars cvR) (heq : σ (.n 8139) = σ (.n 4652))
    (hc3 : IsCanonical128 (σ (.n 3))) (hc4 : IsCanonical128 (σ (.n 4)))
    (h109 : LoadHolds rd (σ (.n 13)) 109 (ofK ((σ (.n 3)).limb 0) +
      challengeOf (sqCv cvR) * (ofK ((σ (.n 3)).limb 0) + ofK ((σ (.n 4)).limb 0))))
    (h110 : LoadHolds rd (σ (.n 13)) 110 (ofK ((σ (.n 3)).limb 1) +
      challengeOf (sqCv cvR) * (ofK ((σ (.n 3)).limb 1) + ofK ((σ (.n 4)).limb 1))))
    (h111 : LoadHolds rd (σ (.n 13)) 111 0) :
    Completes (coreProgram.Rel rd) rd 8140 8179 ((vtPre.drop 7854).take 45) σ (fun σ' =>
      σ' (.n 8171) = (digestScalars (sqCv cvR)).1 ∧ σ' (.n 8172) = (digestScalars (sqCv cvR)).2 ∧
        σ' (.n 8175) = σ (.n 4651) * gen ^ 104 ∧ σ' (.n 8176) = σ (.n 4554) ∧
        σ' (.n 8177) = σ (.n 1732) ∧ σ' (.n 8178) = challengeOf (sqCv cvR)) := by
  rw [← vtItTail_eq]
  set hv := vtHvTail (σ (.n 3)) (σ (.n 4))
  have Cm := completes_items (C := coreProgram.Rel rd) (rd := rd) hv vtItTail vtItTail_ok σ
  generalize hσf : fRunI rd 8140 hv [] σ vtItTail = σf at Cm
  have hf : ∀ v, fRunI rd 8140 hv [] σ vtItTail v = σf v := fun v => by rw [hσf]
  have E := fRunI_eqs rd hv σf vtItTail [] σ vtItTail_ok hf
  have FR : ∀ k < 8140, σf (.n k) = σ (.n k) := fun k hk =>
    fRunI_eq_of_def rd hv vtItTail_ok hf (by simp [fDef, vNum, hk])
  have hB := vtItTail_eqsB
  simp only [List.all_eq_true] at hB
  have F := fun e (he : e ∈ vtItTailEq) => E e (mem_of_any feqEqb_sound (hB e he))
  simp only [vtItTailEq, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at F
  obtain ⟨i7855, i7869, d8155, d8156, d8157, d8158, i7875, d8160, d8161, d8162, d8163, d8164, d8165,
    d8166, d8167, d8168, d8169, d8170, d8171, d8172, d8173, d8174, d8175, d8176, d8177, d8178⟩ := F
  simp only [FEq.Holds, Atom.Holds] at d8155 d8156 d8157 d8158 d8160 d8161 d8162 d8163 d8164 d8165
  simp only [FEq.Holds, Atom.Holds] at d8166 d8167 d8168 d8169 d8170 d8171 d8172 d8173 d8174 d8175
  simp only [FEq.Holds, Atom.Holds] at d8176 d8177 d8178
  have hdc : decodeCv (σf (.n 7569)) (σf (.n 7570)) = cvR := by
    rw [FR 7569 (by omega), FR 7570 (by omega)]
    have := decodeCv_spec ⟨cvR, hcv⟩
    rw [hcv] at this
    exact (digestScalars_injective this).symm
  have sq := fun k (hk : k < 14) => i7855 k (by simp [FItem.sets]; omega)
    (by simp [FItem.vals]; omega)
  simp only [FItem.sets, FItem.vals, List.getElem_map, List.getElem_range, hdc] at sq
  have s5 := sq 5 (by omega)
  have s6 := sq 6 (by omega)
  have s13 := sq 13 (by omega)
  simp only [sqVals, sqStateVals, absorbCv_sq] at s5 s6 s13
  have l54 := i7869 0 (by show 0 < 1; omega) (by show 0 < 1; omega)
  have l59 := i7875 0 (by show 0 < 1; omega) (by show 0 < 1; omega)
  simp only [FItem.sets, FItem.vals, hintCells, List.getElem_cons_zero, List.map_cons, List.map_nil] at l54 l59
  have e54 : σf (.n 8154) = ofK ((σ (.n 3)).limb 0) := by rw [l54]; simp [hv, vtHvTail]
  have e59 : σf (.n 8159) = ofK ((σ (.n 4)).limb 0) := by rw [l59]; simp [hv, vtHvTail]
  have e57 : σf (.n 8157) = ofK ((σ (.n 3)).limb 1) := by
    rw [d8157, d8155, d8156, FR 3 (by omega), e54, word_y_inv, split_hi hc3]
  have e62 : σf (.n 8162) = ofK ((σ (.n 4)).limb 1) := by
    rw [d8162, d8160, d8161, FR 4 (by omega), e59, word_y_inv, split_hi hc4]
  refine (Cm (IObls_of_obs _ _ ?_)).mono le_rfl le_rfl ?_
  · rw [vtItTail_obs]
    intro o ho
    simp only [vtItTailOb, List.mem_cons, List.not_mem_nil, or_false] at ho
    rcases ho with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · show σf (.n 8139) + σf (.n 4652) = 0
      rw [FR 8139 (by omega), FR 4652 (by omega), heq]; exact e_add_self _
    · exact ⟨cvR, by rw [FR 7569 (by omega), FR 7570 (by omega)]; exact hcv⟩
    · show IsInK (σf (.n 8154)) ∧ IsInK (σf (.n 8157))
      rw [e54, e57]; exact ⟨ofK_isInK _, ofK_isInK _⟩
    · show IsInK (σf (.n 8159)) ∧ IsInK (σf (.n 8162))
      rw [e59, e62]; exact ⟨ofK_isInK _, ofK_isInK _⟩
    · show LoadHolds rd (σf (.n 13)) 109 (σf (.n 8166))
      rw [d8166, d8165, d8164, d8158, d8163, e54, e59, s13, FR 13 (by omega)]; exact h109
    · show LoadHolds rd (σf (.n 13)) 110 (σf (.n 8169))
      rw [d8169, d8168, d8167, e57, e62, s13, FR 13 (by omega)]; exact h110
    · show LoadHolds rd (σf (.n 13)) 111 (σf (.n 8170))
      rw [d8170, word_zero, FR 13 (by omega)]; exact h111
  · intro σ' h; rw [h]
    refine ⟨by rw [d8171, s5], by rw [d8172, s6], ?_, by rw [d8176, FR 4554 (by omega)],
      by rw [d8177, FR 1732 (by omega)], by rw [d8178, s13]⟩
    rw [d8175, d8174, d8173, word_g104, FR 4651 (by omega)]

end
end LeanVM.Guest.B1.VerifySub
