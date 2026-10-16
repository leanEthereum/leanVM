module

public import LeanVMCircuits.Rec.Edges
public import LeanVMCircuits.Rec.Run

@[expose] public section

/-!
The recursive verifier's soundness at a child, decomposed.

`Edges.tree_sound_certs_off` takes, for each child `v`, the recursive verifier's soundness off an event `badRec v`
(`hrec`): where its parent's circuit is satisfied, the child's circuit is satisfied at the statement the parent's
verifier reads. `RecParts` splits it. The parent's circuit holds a verifier of the child: `J v` certified checks
(sumchecks, GKR layers, WHIR sumchecks) on the child's transcript. At an outcome, check `j` reduces its input claims
(`inOk v j`) to its output claims (`outOk v j`). Where the parent's circuit is satisfied (`held v`) its test holds, and
it lets a false input through with true outputs only on `testBad v j`, which its round theorem bounds
(`Bind.sumcheck_part`, `Bind.whir_part`, `Bind.odd_part`, `Bind.top_part`: the events of `Bind.sumcheck_run_sound_at`
and the like, for a run of the parent's prover). Each check's outputs are
later checks' inputs or openings of the child's committed witness, true off `pcsBad v`, the event #551's `ε_PCS` bounds
(`RecParts.Ok.flow`). `RecParts.ins_ok`: off every check's `testBad` and off `pcsBad`, every check's inputs are true.

What remains is the AIR link (`air`, not proven here): where the parent's circuit is satisfied, every check's inputs
are true (the AIR's constraint and bus claims on the child's committed witness), no two compressions collide (off
`crBad v`, the ideal compression model's `ε_CR`) and the parent's verifier reads statement `st`, the child's circuit is
satisfied at `st`: the AIR tables and buses at the committed witness are the model's circuit, so that their claims give
`Model.Sat`. `RecParts.hrec` is then `hrec` off `badRec v`, the checks' `testBad` with `pcsBad` and `crBad`, and
`tree_sound_parts` bounds the outcomes at which some node's statement or input claims fail by the sum over the nodes of
their `bad`, their checks' `testBad`, `pcsBad` and `crBad` fractions.
-/

namespace LeanVMCircuits.Rec.Edges

open LeanVMCircuits.Rec Model Finset

section Parts

variable {ι Ω : Type}

/-- A child's verifier in its parent, as checks reducing claims: per child `v`, its `J v` checks' input and output
claims at each outcome, each check's event, and the PCS and collision events. -/
structure RecParts (ι Ω : Type) where
  J : ι → ℕ
  inOk : ι → ℕ → Ω → Prop
  outOk : ι → ℕ → Ω → Prop
  testBad : ι → ℕ → Finset Ω
  pcsBad : ι → Finset Ω
  crBad : ι → Finset Ω

/-- What the checks satisfy where the parent's circuit is satisfied (`held`): off the collision event `crBad`, each
check's test lets a false input through with true outputs only on its `testBad` (`test`; a round theorem's event is
counted off its run's collision event, `Bind.sumcheck_run_sound_at`), and each check's outputs are later checks' inputs
or openings true off `pcsBad` (`flow`). -/
structure RecParts.Ok (P : RecParts ι Ω) (held : ι → Ω → Prop) : Prop where
  test : ∀ v j ω, j < P.J v → held v ω → ω ∉ P.crBad v → ω ∉ P.testBad v j → P.outOk v j ω → P.inOk v j ω
  flow : ∀ v j ω, j < P.J v → ω ∉ P.pcsBad v → (∀ j', j < j' → j' < P.J v → P.inOk v j' ω) → P.outOk v j ω

open Classical in
/-- Child `v`'s event: some check's `testBad`, `pcsBad` or `crBad`. -/
noncomputable def RecParts.badRec (P : RecParts ι Ω) (v : ι) : Finset Ω :=
  (range (P.J v)).biUnion (P.testBad v) ∪ P.pcsBad v ∪ P.crBad v

open Classical in
/-- The parts' least events for given claims: check `j`'s event is where the parent's circuit is satisfied and the
check lets a false input through with true outputs, and the PCS event where some check's outputs are false though every
later check's inputs are true. -/
noncomputable def RecParts.least [Fintype Ω] (J : ι → ℕ) (inOk outOk : ι → ℕ → Ω → Prop) (held : ι → Ω → Prop)
    (crBad : ι → Finset Ω) : RecParts ι Ω where
  J := J
  inOk := inOk
  outOk := outOk
  testBad v j := {ω | held v ω ∧ outOk v j ω ∧ ¬ inOk v j ω}
  pcsBad v := {ω | ∃ j < J v, (∀ j', j < j' → j' < J v → inOk v j' ω) ∧ ¬ outOk v j ω}
  crBad := crBad

/-- Non-vacuity: for any claims, the least events satisfy `RecParts.Ok`. Bounding them is the round theorems' work for
`testBad` (`Bind.sumcheck_part`) and #551's for `pcsBad`. -/
theorem RecParts.least_ok [Fintype Ω] (J : ι → ℕ) (inOk outOk : ι → ℕ → Ω → Prop) (held : ι → Ω → Prop)
    (crBad : ι → Finset Ω) : (RecParts.least J inOk outOk held crBad).Ok held where
  test v j ω _ hh _ hb ho := by
    by_contra hn
    exact hb (by simp only [RecParts.least, mem_filter, mem_univ, true_and]; exact ⟨hh, ho, hn⟩)
  flow v j ω hj hp hin := by
    by_contra hn
    exact hp (by simp only [RecParts.least, mem_filter, mem_univ, true_and]; exact ⟨j, hj, hin, hn⟩)

/-- Off every check's `testBad`, `pcsBad` and `crBad`, where the parent's circuit is satisfied, every check's inputs
are true: by induction from the last check, whose outputs are openings. -/
theorem RecParts.ins_ok {P : RecParts ι Ω} {held : ι → Ω → Prop} (hP : P.Ok held) (v : ι) (ω : Ω) (hh : held v ω)
    (ht : ∀ j < P.J v, ω ∉ P.testBad v j) (hp : ω ∉ P.pcsBad v) (hc : ω ∉ P.crBad v) :
    ∀ j < P.J v, P.inOk v j ω := by
  suffices H : ∀ d j, P.J v - j = d → j < P.J v → P.inOk v j ω from fun j hj => H _ j rfl hj
  intro d
  induction d using Nat.strong_induction_on with
  | _ d ih =>
    intro j hd hj
    exact hP.test v j ω hj hh hc (ht j hj)
      (hP.flow v j ω hj hp fun j' hjj' hj' => ih (P.J v - j') (by omega) j' rfl hj')

open Classical in
theorem RecParts.not_mem_badRec {P : RecParts ι Ω} {v : ι} {ω : Ω} (h : ω ∉ P.badRec v) :
    (∀ j < P.J v, ω ∉ P.testBad v j) ∧ ω ∉ P.pcsBad v ∧ ω ∉ P.crBad v := by
  simp only [RecParts.badRec, mem_union, mem_biUnion, mem_range, not_or, not_exists, not_and] at h
  exact ⟨h.1.1, h.1.2, h.2⟩

/-- `hrec` from the parts: off `badRec v`, where the parent's circuit is satisfied and its verifier reads the child's
`treeStmt`, the AIR link (`hair`) gives the child's circuit satisfied there, every check's inputs being true. -/
theorem RecParts.hrec (T : TreeSound.Tree ι) (cert : ι → EdgeCert) (t : ι → State) (os : ι → Array (List ℕ))
    (L : Layout) (slot : ι → ℕ) (stRoot : Ω → ℕ → Fin 4 → K) (val : ι → Ω → Val) (P : RecParts ι Ω)
    (hP : P.Ok fun v ω => Sat (treeStmt T cert slot stRoot val (T.parent v) ω) (t (T.parent v))
      (val (T.parent v) ω))
    (hair : ∀ v ∈ T.nodes, v ≠ T.root → ∀ ω,
      Sat (treeStmt T cert slot stRoot val (T.parent v) ω) (t (T.parent v)) (val (T.parent v) ω) →
      (∀ j < P.J v, P.inOk v j ω) → ω ∉ P.crBad v →
      ((cert (T.parent v)).children.getD (slot v) default).inst.VerifiesAt (cert (T.parent v)).calls
        (os (T.parent v)) (val (T.parent v) ω) (treeStmt T cert slot stRoot val v ω) L.len →
      Sat (treeStmt T cert slot stRoot val v ω) (t v) (val v ω)) :
    ∀ v ∈ T.nodes, v ≠ T.root → ∀ ω, ω ∉ P.badRec v →
      Sat (treeStmt T cert slot stRoot val (T.parent v) ω) (t (T.parent v)) (val (T.parent v) ω) →
      ((cert (T.parent v)).children.getD (slot v) default).inst.VerifiesAt (cert (T.parent v)).calls
        (os (T.parent v)) (val (T.parent v) ω) (treeStmt T cert slot stRoot val v ω) L.len →
      Sat (treeStmt T cert slot stRoot val v ω) (t v) (val v ω) := by
  intro v hv hne ω hb hps hver
  obtain ⟨ht, hp, hc⟩ := RecParts.not_mem_badRec hb
  exact hair v hv hne ω hps (P.ins_ok hP v ω hps ht hp hc) hc hver

open Classical in
/-- The tree over its parts: the outcomes at which some node's statement or input claims are false are at most the sum
over the nodes of their reduction's `bad`, their checks' `testBad`, `pcsBad` and `crBad` fractions. Its premises are
the edges (`checkedges`), each reduction's test (`hstep`), each child's checks (`hP`, the round theorems) and the AIR
link (`hair`). -/
theorem tree_sound_parts [Fintype Ω] (T : TreeSound.Tree ι) (cert : ι → EdgeCert) (t : ι → State)
    (os : ι → Array (List ℕ)) (hr : ∀ v ∈ T.nodes, replayR (cert v).calls #[] 0 {} #[] = some (t v, os v))
    (hacc : ∀ v ∈ T.nodes, (cert v).accepts (os v) = true) (hver : ∀ v ∈ T.nodes, (cert v).verifies (os v) = true)
    (L : Layout) (hL : ∀ v ∈ T.nodes, (cert v).layout = L)
    (slot : ι → ℕ) (hslot : ∀ v ∈ T.nodes, v ≠ T.root → slot v < (cert (T.parent v)).children.length)
    (stRoot : Ω → ℕ → Fin 4 → K) (val : ι → Ω → Val)
    (hsroot : ∀ ω, Sat (stRoot ω) (t T.root) (val T.root ω)) (P : RecParts ι Ω)
    (hP : P.Ok fun v ω => Sat (treeStmt T cert slot stRoot val (T.parent v) ω) (t (T.parent v))
      (val (T.parent v) ω))
    (hair : ∀ v ∈ T.nodes, v ≠ T.root → ∀ ω,
      Sat (treeStmt T cert slot stRoot val (T.parent v) ω) (t (T.parent v)) (val (T.parent v) ω) →
      (∀ j < P.J v, P.inOk v j ω) → ω ∉ P.crBad v →
      ((cert (T.parent v)).children.getD (slot v) default).inst.VerifiesAt (cert (T.parent v)).calls
        (os (T.parent v)) (val (T.parent v) ω) (treeStmt T cert slot stRoot val v ω) L.len →
      Sat (treeStmt T cert slot stRoot val v ω) (t v) (val v ω))
    (tD : Dense E → Prop) (tM : Matrix E → Prop) (bad : ι → Finset Ω)
    (hstep : ∀ v ∈ T.nodes, ∀ ω, ω ∉ bad v →
      stmt T cert slot L (treeStmt T cert slot stRoot val) tD tM v ω → ins cert val tD tM v ω)
    (hroot : ∀ ω, stmt T cert slot L (treeStmt T cert slot stRoot val) tD tM T.root ω) :
    (Finset.card {ω | ∃ v ∈ T.nodes, ¬ (stmt T cert slot L (treeStmt T cert slot stRoot val) tD tM v ω ∧
        ins cert val tD tM v ω)} : ℚ≥0) / Fintype.card Ω ≤
      ∑ v ∈ T.nodes, ((bad v).card + ∑ j ∈ range (P.J v), (P.testBad v j).card + (P.pcsBad v).card +
        (P.crBad v).card : ℚ≥0) / Fintype.card Ω := by
  refine (tree_sound_certs_frac T cert t os hr hacc hver L hL slot hslot stRoot val hsroot P.badRec
    (P.hrec T cert t os L slot stRoot val hP hair) tD tM bad hstep hroot).trans ?_
  refine sum_le_sum fun v _ => div_le_div_of_nonneg_right ?_ (by positivity)
  have h1 : ((P.badRec v).card : ℚ≥0) ≤
      ∑ j ∈ range (P.J v), ((P.testBad v j).card : ℚ≥0) + (P.pcsBad v).card + (P.crBad v).card := by
    calc ((P.badRec v).card : ℚ≥0)
        ≤ (((range (P.J v)).biUnion (P.testBad v)).card + (P.pcsBad v).card + (P.crBad v).card : ℕ) := by
          refine Nat.cast_le.mpr ((card_union_le _ _).trans ?_)
          exact Nat.add_le_add_right (card_union_le _ _) _
      _ ≤ (∑ j ∈ range (P.J v), (P.testBad v j).card + (P.pcsBad v).card + (P.crBad v).card : ℕ) := by
          exact Nat.cast_le.mpr (Nat.add_le_add_right (Nat.add_le_add_right card_biUnion_le _) _)
      _ = _ := by push_cast; ring
  calc ((bad v).card : ℚ≥0) + (P.badRec v).card
      ≤ (bad v).card + (∑ j ∈ range (P.J v), ((P.testBad v j).card : ℚ≥0) + (P.pcsBad v).card +
        (P.crBad v).card) := by gcongr
    _ = _ := by push_cast; ring

end Parts

end LeanVMCircuits.Rec.Edges

namespace LeanVMCircuits.Rec.Bind

open LeanVMCircuits.Rec Model Finset

/-- A certified sumcheck is a check of `RecParts`: its input claim true (the claim is the instance's sum), its outputs
true (the hints are their true values, and the test's other side the instance's final value at the oracle's
challenges), and its event `sumcheckFalse`, `sumcheckEvent` with a false input claim, which `sumcheck_run_sound_at` bounds by
`n · d / |E|` of the oracles. Where the parent's circuit holds the test, a false input with true outputs is in the
event. -/
theorem sumcheck_part {c : Cert} {s : State} {sc : SumcheckCert} {I : Sumcheck.Inst E sc.rounds.length} {T' : ℕ → E}
    {val : (ℕ → K) → Val} (ρ : ℕ → K) (htest : ∀ a b, s.unions[sc.test]? = some (a, b) → val ρ a = val ρ b)
    (hout : (∀ w ∈ sc.hints, Model.ev (val ρ) w = T' w) ∧
      Model.ev (val ρ) sc.final + (sc.resid.map fun t => Model.ev (val ρ) t.1 * Model.ev (val ρ) t.2.1).sum =
        I.final (readR (chalWords c.outs sc.chals) ρ))
    (hnot : ¬ sumcheckFalse c s sc I T' val ρ) :
    Model.ev (val ρ) sc.claim0 = I.sum := by
  by_contra hne
  exact hnot ⟨⟨hout.1, htest, hout.2⟩, hne⟩

/-- A WHIR sumcheck is a check of `RecParts`: its event `whirFalse`, which `whir_run_sound_at` bounds by `n · d / |E|`
of the oracles. -/
theorem whir_part {c : Cert} {s : State} {wc : WhirCert} {I : Sumcheck.Inst E wc.rounds.length}
    {val : (ℕ → K) → Val} (ρ : ℕ → K) (htest : ∀ a b, s.unions[wc.test]? = some (a, b) → val ρ a = val ρ b)
    (hout : Model.ev (val ρ) wc.final = I.final (readR (chalWords c.outs wc.chals) ρ))
    (hnot : ¬ whirFalse c s wc I val ρ) : Model.ev (val ρ) wc.claim0 = I.sum := by
  by_contra hne
  exact hnot ⟨⟨htest, hout⟩, hne⟩

/-- A GKR odd layer is a check of `RecParts`: its input values are their true children's products where its test
holds and every next claim is its value's true line, off its event `oddFalse`, which `odd_run_sound_at` bounds by
`m / |E|` of the oracles. -/
theorem odd_part {c : Cert} {s : State} {oc : OddCert} {L R : ℕ → E} {val : (ℕ → K) → Val} (ρ : ℕ → K)
    (htest : ∀ a b, s.unions[oc.test]? = some (a, b) → val ρ a = val ρ b)
    (hout : ∀ k < oc.m, Model.ev (val ρ) (oc.out c.outs k) =
      L k + readR (chalWords c.outs oc.chals) ρ 1 * (L k + R k))
    (hnot : ¬ oddFalse c s oc L R val ρ) : ∀ k < oc.m, Model.ev (val ρ) (oc.values.getD k 0) = L k * R k := by
  intro k hk
  by_contra hne
  exact hnot ⟨⟨htest, hout⟩, k, hk, hne⟩

/-- A GKR radix-four top layer is a check of `RecParts`: its event `topFalse`, which `top_run_sound_at` bounds by
`(m + 1) / |E|` of the oracles. -/
theorem top_part {c : Cert} {s : State} {tc : TopCert} {T' : ℕ → ℕ → E} {val : (ℕ → K) → Val} (ρ : ℕ → K)
    (htest : ∀ a b, s.unions[tc.test]? = some (a, b) → val ρ a = val ρ b)
    (hout : ∀ k < tc.m, Model.ev (val ρ) (tc.out c.outs k) =
      lineE (lineE (T' k 0) (T' k 1) (readR (chalWords c.outs tc.chals) ρ 1))
        (lineE (T' k 2) (T' k 3) (readR (chalWords c.outs tc.chals) ρ 1)) (readR (chalWords c.outs tc.chals) ρ 2))
    (hnot : ¬ topFalse c s tc T' val ρ) :
    ∀ k < tc.m, Model.ev (val ρ) (tc.values.getD k 0) = T' k 0 * T' k 1 * T' k 2 * T' k 3 := by
  intro k hk
  by_contra hne
  exact hnot ⟨⟨htest, hout⟩, k, hk, hne⟩

end LeanVMCircuits.Rec.Bind
