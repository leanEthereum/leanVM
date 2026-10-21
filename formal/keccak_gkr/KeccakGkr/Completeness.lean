import KeccakGkr.Soundness

/-!
# Completeness

`protocol_complete`: if the first segment ends on the committed state after it (`Chain`), the
honest prover, which sends the true output values `v` and every other message as the protocol
computes it, ends every possible execution with the verifier accepting, both claims on the column
true, and the statement holding at the point the verifier drew.

The honest prover here computes in the field directly. The crate's prover computes in the basis
of the powers of `s` and aborts when `s` lies in a proper subfield (`§keccak:cost`, prover),
which this model does not include.
-/

open Polynomial OracleComp
open scoped ENNReal

namespace KeccakGkr

variable {E : Type} [Field E] [CharP E 2] [Fintype E] [DecidableEq E] [SampleableType E]
variable (P : Perm) (D : ℕ) {n : ℕ} (Q : Column n) (x : E)

/-- The data the layers carry is the honest one: the statement holds, `c_st` true. -/
def TruePx (c : Ctx E n) : Prop := Statement P D Q x c.rl c.rp c.v ∧ OutClaim Q x c

omit [CharP E 2] [Fintype E] [DecidableEq E] [SampleableType E] in
theorem pad_zero {k : ℕ} {T : Type} [Fintype T] (enc : T → Cube k) :
    pad enc (fun _ => (0 : E)) = 0 := by
  funext o; simp [pad]

omit [Fintype E] [DecidableEq E] [SampleableType E] in
theorem startTable_eq_zero (hc : Chain P D Q) (rl : Fin 4 → E) (rp : Fin n → E) (v : Lane → E)
    (hv : ∀ ℓ, v ℓ = outEval P D Q x ℓ rl rp) : startTable P D Q x rl rp v = 0 := by
  have hd : diffStep P D Q x rl rp = fun _ => 0 := by
    funext ℓ
    simp [diffStep, diffLow, segDiff_eq_zero P D Q x hc]
  have hb : (fun ℓ => outEval P D Q x ℓ rl rp - v ℓ) = fun _ => (0 : E) := by
    funext ℓ; rw [hv, sub_self]
  funext o
  simp only [startTable, hd, hb, pad_zero, Pi.zero_apply, ite_self]

omit [Fintype E] [DecidableEq E] in
theorem start_complete (hc : Chain P D Q) :
    (start P D Q x).Complete (fun _ => True) (ClaimGood P D Q D (TruePx P D Q x)) := by
  have c1 : (Phase.sample (Fin 4 → E) fun (_ : Unit) rl => rl).Complete (fun _ => True)
      (fun _ => True) := Phase.sample_complete fun _ _ _ => trivial
  have c2 : (Phase.sample (Fin n → E) fun (rl : Fin 4 → E) rp => (rl, rp)).Complete
      (fun _ => True) (fun _ => True) := Phase.sample_complete fun _ _ _ => trivial
  have c3 : (Phase.receive (Lane → E) (fun (a : (Fin 4 → E) × (Fin n → E)) v => (a, v))
      fun a ℓ => outEval P D Q x ℓ a.1 a.2).Complete (fun _ => True)
        (fun a => ∀ ℓ, a.2 ℓ = outEval P D Q x ℓ a.1.1 a.1.2) :=
    Phase.receive_complete fun _ _ _ => rfl
  have c4 : (Phase.sample (Fin 6 → E) fun (a : ((Fin 4 → E) × (Fin n → E)) × (Lane → E)) ρ =>
      (a, ρ)).Complete (fun a => ∀ ℓ, a.2 ℓ = outEval P D Q x ℓ a.1.1 a.1.2)
        (fun a => ∀ ℓ, a.1.2 ℓ = outEval P D Q x ℓ a.1.1.1 a.1.1.2) :=
    Phase.sample_complete fun _ h _ => h
  have c5 : (Phase.receive E (fun (a : Pre E n) cst => some (mkCtx a cst, firstClaim x (mkCtx a cst)))
      fun a => outTotal Q x a.1.1.1 a.1.1.2 a.2).Complete
        (fun a => ∀ ℓ, a.1.2 ℓ = outEval P D Q x ℓ a.1.1.1 a.1.1.2)
        (ClaimGood P D Q D (TruePx P D Q x)) := by
    refine Phase.receive_complete fun a hv => ?_
    refine ⟨⟨⟨hc, hv⟩, rfl⟩, ?_⟩
    have hid := firstClaim_identity P D Q x (mkCtx a (outTotal Q x a.1.1.1 a.1.1.2 a.2))
    have h0 := startTable_eq_zero P D Q x hc (mkCtx a (outTotal Q x a.1.1.1 a.1.1.2 a.2)).rl
      (mkCtx a (outTotal Q x a.1.1.1 a.1.1.2 a.2)).rp (mkCtx a (outTotal Q x a.1.1.1 a.1.1.2 a.2)).v hv
    rw [h0] at hid
    simp only [mle, Pi.zero_apply, mul_zero, Finset.sum_const_zero] at hid
    rw [show (mkCtx a (outTotal Q x a.1.1.1 a.1.1.2 a.2)).cst -
        outTotal Q x (mkCtx a (outTotal Q x a.1.1.1 a.1.1.2 a.2)).rl
          (mkCtx a (outTotal Q x a.1.1.1 a.1.1.2 a.2)).rp
          (mkCtx a (outTotal Q x a.1.1.1 a.1.1.2 a.2)).ρ = 0 from sub_self _, add_zero,
      sub_eq_zero] at hid
    exact hid.symm
  exact (c1.comp (c2.comp (c3.comp (c4.comp c5)))).mono (fun _ h => h) (fun _ h => h)

/-- After the opening of `c_st`, honestly: the statement holds, the last claim and the claim on
the column's words are true. -/
def OutAcc : Option (OutStage E n) → Prop
  | none => False
  | some s => Statement P D Q x s.1.rl s.1.rp s.1.v ∧ s.2.1.Holds P D Q 0 ∧
      colEval Q x s.1.rl s.1.rp s.2.2.1 = s.2.2.2

omit [Fintype E] in
theorem outOpen_complete :
    (outOpen Q x).Complete (ClaimGood P D Q 0 (TruePx P D Q x)) (OutAcc P D Q x) := by
  set Pout : Ctx E n × Claim E n → Prop :=
    fun cc => Statement P D Q x cc.1.rl cc.1.rp cc.1.v ∧ cc.2.Holds P D Q 0
  have o1 : (Phase.compute fun (st : Option (Ctx E n × Claim E n)) =>
      st.map fun cc => (cc, cc.1.cst)).Complete
        (ClaimGood P D Q 0 (TruePx P D Q x)) ((outSum Q x).True' Pout) := by
    refine Phase.compute_complete fun st h => ?_
    rcases st with _ | ⟨c, cl⟩
    · exact h
    · obtain ⟨⟨hst, hout⟩, hcl⟩ := h
      exact ⟨⟨hst, hcl⟩, hout.trans (total_outSum Q x _).symm⟩
  have o2 := sumcheck_complete 6 (outSum Q x) Pout
  have o3 : (Phase.receive E checkOut fun st =>
      match st with
      | some s => colEval Q x s.1.1.rl s.1.1.rp s.2.1
      | none => 0).Complete ((outSum Q x).Good Pout) (OutAcc P D Q x) := by
    refine Phase.receive_complete fun st h => ?_
    rcases st with _ | ⟨cc, fo, v⟩
    · exact h
    · obtain ⟨⟨hst, hcl⟩, hv⟩ := h
      simp only [checkOut, Option.bind_some]
      split_ifs with h'
      · exact ⟨hst, hcl, rfl⟩
      · exact absurd hv h'
  exact o1.comp (o2.comp o3)

/-- Before the opening of the last claim, honestly: the statement holds, the claim on the
column's words true. -/
def InTruePx (s : OutStage E n) : Prop :=
  Statement P D Q x s.1.rl s.1.rp s.1.v ∧ colEval Q x s.1.rl s.1.rp s.2.2.1 = s.2.2.2

omit [Fintype E] in
theorem inOpen_complete : (inOpen Q).Complete (OutAcc P D Q x) (Accepted P D Q x) := by
  have i1 : (Phase.compute fun (st : Option (OutStage E n)) => st.map fun s => (s, s.2.1.c)).Complete
      (OutAcc P D Q x) ((inSum₁ (E := E) Q).True' (InTruePx P D Q x)) := by
    refine Phase.compute_complete fun st h => ?_
    rcases st with _ | s
    · exact h
    · obtain ⟨hst, hcl, hcol⟩ := h
      exact ⟨⟨hst, hcol⟩, hcl.trans (total_inSum₁ P D Q s).symm⟩
  have i2 : ((sumcheck 4 (inSum₁ (E := E) Q)).map fun st =>
      st.map fun c => ((c.1, c.2.1), c.2.2)).Complete
        ((inSum₁ (E := E) Q).True' (InTruePx P D Q x))
        ((inSum₂ (E := E) Q).True' fun c => InTruePx P D Q x c.1) := by
    refine Phase.Complete.map ((sumcheck_complete 4 (inSum₁ (E := E) Q) (InTruePx P D Q x)).mono
      (fun _ h => h) fun st h => ?_)
    rcases st with _ | ⟨s, fl, v⟩
    · exact h
    · obtain ⟨hPx, hv⟩ := h
      exact ⟨hPx, hv.trans (total_inSum₂ Q (s, fl)).symm⟩
  have i3 := sumcheck_complete 6 (inSum₂ (E := E) Q) fun c => InTruePx P D Q x c.1
  have i4 : (Phase.receive (Slice → E) checkIn fun st =>
      match st with
      | some s => fun z => sliceEval Q z s.1.2 (Fin.init s.1.1.2.1.r) s.2.1
      | none => 0).Complete ((inSum₂ (E := E) Q).Good fun c => InTruePx P D Q x c.1)
        (Accepted P D Q x) := by
    refine Phase.receive_complete fun st h => ?_
    rcases st with _ | ⟨sf, fo, v⟩
    · exact h
    · obtain ⟨⟨hst, hcol⟩, hv⟩ := h
      simp only [checkIn, Option.bind_some]
      split_ifs with h'
      · exact ⟨hcol, fun _ => rfl, hst⟩
      · exact absurd hv h'
  exact i1.comp (i2.comp (i3.comp i4))

omit [Fintype E] in
/-- **Completeness.** If the first segment ends on the committed state after it, every possible
honest execution ends with the verifier accepting, the claims on the column true, and the
statement holding. -/
theorem protocol_complete (hc : Chain P D Q) :
    (protocol P D Q x).Complete (fun _ => True) (Accepted P D Q x) :=
  (start_complete P D Q x hc).comp ((layers_complete P D Q (TruePx P D Q x) D).comp
    ((outOpen_complete P D Q x).comp (inOpen_complete P D Q x)))

end KeccakGkr
