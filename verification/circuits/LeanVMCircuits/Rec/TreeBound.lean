module

public import LeanVMCircuits.Rec.Collision
public import LeanVMCircuits.Rec.AirLink

@[expose] public section

/-!
The tree's soundness bound with every event's fraction replaced by its bound.

`AirLink.tree_sound_air` bounds the outcomes at which some node's statement or input claims are false by the sum over the nodes of their reduction's `bad`, their checks' `testBad`, `pcsBad`, `crBad`, the constraint batch's `batchBad` and the bus's `busBad` fractions. `tree_sound_bound` replaces the last four by bounds: `epsPCS v` (`Edges.PcsBound`, #551's WHIR bound), `epsCR v` (for the collision events, `Edges.crBad_frac`), `epsBus v` (`AirLink.busBad_frac`, `4 N_v / |E|`) and `epsBatch v` (the constraint batch's, left abstract).

`tree_sound_crEvent` instantiates `crBad` with the ideal compression model's collision event `Edges.crEvent` over outcomes pairing other coins with the oracle, its bound `Edges.epsCR V (Q v)` of child `v`'s number of compression queries. `tree_sound_ideal` further instantiates the bus's bound with `busBad_frac`'s `4 N_v / |E|`, the draw being uniform and made after the commitment.
-/

namespace LeanVMCircuits.Rec.AirLink

open LeanVMCircuits.Rec Model Finset Edges

section Bound

variable {ι Ω : Type}

/-- Every event is at most all the outcomes. -/
theorem frac_le_one [Fintype Ω] (s : Finset Ω) : (s.card : ℚ≥0) / Fintype.card Ω ≤ 1 :=
  div_le_one_of_le₀ (by exact_mod_cast card_le_univ _) (by positivity)

/-- The empty event is none of the outcomes. -/
theorem frac_empty [Fintype Ω] : ((∅ : Finset Ω).card : ℚ≥0) / Fintype.card Ω ≤ 0 := by
  simp

open Classical in
/-- The capstone: the outcomes at which some node's statement or input claims are false are at most the sum over the nodes of their reduction's `bad` and their checks' `testBad` fractions, the PCS bound `epsPCS v` (`PcsBound`, #551), the collision bound `epsCR v`, the bus's bound `epsBus v` (`busBad_frac`: `4 N_v / |E|`) and the constraint batch's bound `epsBatch v`. Its premises are `tree_sound_air`'s and the four bounds. -/
theorem tree_sound_bound [Fintype Ω] (T : TreeSound.Tree ι) (cert : ι → EdgeCert) (t : ι → State)
    (os : ι → Array (List ℕ)) (hr : ∀ v ∈ T.nodes, replayR (cert v).calls #[] 0 {} #[] = some (t v, os v))
    (hacc : ∀ v ∈ T.nodes, (cert v).accepts (os v) = true) (hver : ∀ v ∈ T.nodes, (cert v).verifies (os v) = true)
    (L : Layout) (hL : ∀ v ∈ T.nodes, (cert v).layout = L)
    (slot : ι → ℕ) (hslot : ∀ v ∈ T.nodes, v ≠ T.root → slot v < (cert (T.parent v)).children.length)
    (stRoot : Ω → ℕ → Fin 4 → K) (val : ι → Ω → Val)
    (hsroot : ∀ ω, Sat (stRoot ω) (t T.root) (val T.root ω)) (P : RecParts ι Ω)
    (hP : P.Ok fun v ω => Sat (treeStmt T cert slot stRoot val (T.parent v) ω) (t (T.parent v))
      (val (T.parent v) ω))
    (batchBad : ι → Finset Ω) (draw : ι → Ω → Fin 5 → E) (wit : ι → Ω → Witness)
    (hval : ∀ v ∈ T.nodes, v ≠ T.root → ∀ ω, val v ω = assign (stmtFirst (t v)) (wit v ω))
    (hlink : ChecksGiveRows T cert (fun v => stmtFirst (t v)) os L slot stRoot val P batchBad draw wit)
    (tD : Dense E → Prop) (tM : Matrix E → Prop) (bad : ι → Finset Ω)
    (hstep : ∀ v ∈ T.nodes, ∀ ω, ω ∉ bad v →
      stmt T cert slot L (treeStmt T cert slot stRoot val) tD tM v ω → ins cert val tD tM v ω)
    (hroot : ∀ ω, stmt T cert slot L (treeStmt T cert slot stRoot val) tD tM T.root ω)
    (epsPCS epsCR epsBus epsBatch : ι → ℚ≥0) (hpcs : PcsBound P epsPCS)
    (hcr : ∀ v ∈ T.nodes, ((P.crBad v).card : ℚ≥0) / Fintype.card Ω ≤ epsCR v)
    (hbus : ∀ v ∈ T.nodes, ((busBad (stmtFirst (t v)) (wit v) (draw v)).card : ℚ≥0) / Fintype.card Ω ≤ epsBus v)
    (hbatch : ∀ v ∈ T.nodes, ((batchBad v).card : ℚ≥0) / Fintype.card Ω ≤ epsBatch v) :
    (Finset.card {ω | ∃ v ∈ T.nodes, ¬ (stmt T cert slot L (treeStmt T cert slot stRoot val) tD tM v ω ∧
        ins cert val tD tM v ω)} : ℚ≥0) / Fintype.card Ω ≤
      ∑ v ∈ T.nodes, (((bad v).card + ∑ j ∈ range (P.J v), (P.testBad v j).card : ℚ≥0) / Fintype.card Ω +
        epsPCS v + epsCR v + epsBus v + epsBatch v) := by
  refine (tree_sound_air T cert t os hr hacc hver L hL slot hslot stRoot val hsroot P hP batchBad draw wit hval
    hlink tD tM bad hstep hroot).trans (sum_le_sum fun v hv => ?_)
  have key : ∀ (a p c b u N ep ec eu eb : ℚ≥0), p / N ≤ ep → c / N ≤ ec → u / N ≤ eu → b / N ≤ eb →
      (a + p + c + b + u) / N ≤ a / N + ep + ec + eu + eb := by
    intro a p c b u N ep ec eu eb hp hc hu hb
    calc (a + p + c + b + u) / N = a / N + p / N + c / N + u / N + b / N := by simp only [add_div]; ring
      _ ≤ a / N + ep + ec + eu + eb := add_le_add (add_le_add (add_le_add (add_le_add le_rfl hp) hc) hu) hb
  exact key _ _ _ _ _ _ _ _ _ _ (hpcs.le v) (hcr v hv) (hbus v hv) (hbatch v hv)

/-- Non-vacuity of the bounds' premises: every part, witness and draw meets them with every bound `1`, and an empty constraint batch event with `epsBatch = 0`. -/
example [Fintype Ω] (P : RecParts ι Ω) (t : ι → State) (wit : ι → Ω → Witness) (draw : ι → Ω → Fin 5 → E)
    (batchBad : ι → Finset Ω) :
    PcsBound P (fun _ => 1) ∧ (∀ v, ((P.crBad v).card : ℚ≥0) / Fintype.card Ω ≤ 1) ∧
      (∀ v, ((busBad (stmtFirst (t v)) (wit v) (draw v)).card : ℚ≥0) / Fintype.card Ω ≤ 1) ∧
      (∀ v, ((batchBad v).card : ℚ≥0) / Fintype.card Ω ≤ 1) ∧
      (∀ _v : ι, ((∅ : Finset Ω).card : ℚ≥0) / Fintype.card Ω ≤ 0) :=
  ⟨PcsBound.one P, fun _ => frac_le_one _, fun _ => frac_le_one _, fun _ => frac_le_one _, fun _ => frac_empty⟩

/-- Non-vacuity at the least parts with the collision events and no constraint batch event: `RecParts.Ok`, the PCS bound `1` and the batch bound `0` all hold. -/
example [Fintype Ω] (J : ι → ℕ) (inOk outOk : ι → ℕ → Ω → Prop) (held : ι → Ω → Prop) (crBad : ι → Finset Ω) :
    (RecParts.least J inOk outOk held crBad).Ok held ∧ PcsBound (RecParts.least J inOk outOk held crBad) (fun _ => 1) ∧
      ∀ _v : ι, ((∅ : Finset Ω).card : ℚ≥0) / Fintype.card Ω ≤ 0 :=
  ⟨RecParts.least_ok _ _ _ _ _, PcsBound.one _, fun _ => frac_empty⟩

end Bound

section Ideal

variable {ι Ω₀ X V C R : Type}

open Classical in
/-- The capstone with `crBad` the ideal compression model's collision event: over outcomes pairing other coins with a uniform oracle `X → (Fin 4 → V)`, child `v`'s `crBad` is `crEvent (σ v) (Q v)` (a collision or near hit among the first `Q v` compression queries of its prover `σ v`), bounded by `Edges.epsCR V (Q v)` (`crBad_frac`). -/
theorem tree_sound_crEvent [Fintype Ω₀] [Fintype X] [Fintype V] [Nonempty V] (T : TreeSound.Tree ι)
    (cert : ι → EdgeCert) (t : ι → State)
    (os : ι → Array (List ℕ)) (hr : ∀ v ∈ T.nodes, replayR (cert v).calls #[] 0 {} #[] = some (t v, os v))
    (hacc : ∀ v ∈ T.nodes, (cert v).accepts (os v) = true) (hver : ∀ v ∈ T.nodes, (cert v).verifies (os v) = true)
    (L : Layout) (hL : ∀ v ∈ T.nodes, (cert v).layout = L)
    (slot : ι → ℕ) (hslot : ∀ v ∈ T.nodes, v ≠ T.root → slot v < (cert (T.parent v)).children.length)
    (stRoot : Ω₀ × (X → Fin 4 → V) → ℕ → Fin 4 → K) (val : ι → Ω₀ × (X → Fin 4 → V) → Val)
    (hsroot : ∀ ω, Sat (stRoot ω) (t T.root) (val T.root ω)) (P : RecParts ι (Ω₀ × (X → Fin 4 → V)))
    (hP : P.Ok fun v ω => Sat (treeStmt T cert slot stRoot val (T.parent v) ω) (t (T.parent v))
      (val (T.parent v) ω))
    (batchBad : ι → Finset (Ω₀ × (X → Fin 4 → V))) (draw : ι → Ω₀ × (X → Fin 4 → V) → Fin 5 → E)
    (wit : ι → Ω₀ × (X → Fin 4 → V) → Witness)
    (hval : ∀ v ∈ T.nodes, v ≠ T.root → ∀ ω, val v ω = assign (stmtFirst (t v)) (wit v ω))
    (hlink : ChecksGiveRows T cert (fun v => stmtFirst (t v)) os L slot stRoot val P batchBad draw wit)
    (tD : Dense E → Prop) (tM : Matrix E → Prop) (bad : ι → Finset (Ω₀ × (X → Fin 4 → V)))
    (hstep : ∀ v ∈ T.nodes, ∀ ω, ω ∉ bad v →
      stmt T cert slot L (treeStmt T cert slot stRoot val) tD tM v ω → ins cert val tD tM v ω)
    (hroot : ∀ ω, stmt T cert slot L (treeStmt T cert slot stRoot val) tD tM T.root ω)
    (ch : X → C) (re : X → R) (hinj : ∀ x y, re x = re y → ch x = ch y → x = y)
    (σ : ι → Ω₀ → List (Fin 4 → V) → X) (Q : ι → ℕ) (hcrEq : ∀ v, P.crBad v = crEvent ch re (σ v) (Q v))
    (epsPCS epsBus epsBatch : ι → ℚ≥0) (hpcs : PcsBound P epsPCS)
    (hbus : ∀ v ∈ T.nodes, ((busBad (stmtFirst (t v)) (wit v) (draw v)).card : ℚ≥0) /
      Fintype.card (Ω₀ × (X → Fin 4 → V)) ≤ epsBus v)
    (hbatch : ∀ v ∈ T.nodes, ((batchBad v).card : ℚ≥0) / Fintype.card (Ω₀ × (X → Fin 4 → V)) ≤ epsBatch v) :
    (Finset.card {ω | ∃ v ∈ T.nodes, ¬ (stmt T cert slot L (treeStmt T cert slot stRoot val) tD tM v ω ∧
        ins cert val tD tM v ω)} : ℚ≥0) / Fintype.card (Ω₀ × (X → Fin 4 → V)) ≤
      ∑ v ∈ T.nodes, (((bad v).card + ∑ j ∈ range (P.J v), (P.testBad v j).card : ℚ≥0) /
        Fintype.card (Ω₀ × (X → Fin 4 → V)) + epsPCS v + Edges.epsCR V (Q v) + epsBus v + epsBatch v) :=
  tree_sound_bound T cert t os hr hacc hver L hL slot hslot stRoot val hsroot P hP batchBad draw wit hval hlink tD tM
    bad hstep hroot epsPCS (fun v => Edges.epsCR V (Q v)) epsBus epsBatch hpcs
    (fun v _ => crBad_frac ch re hinj P σ Q hcrEq v) hbus hbatch

open Classical in
/-- The capstone in the ideal model with the bus's bound instantiated: child `v`'s draw `draw v` is uniform and made after its commitment (a lens `put v`/`draw v` leaving `wit v` unchanged, as `busBad_frac` takes), its committed witnesses' buses having at most `N v` slots, so its bus bound is `4 N_v / |E|`. -/
theorem tree_sound_ideal [Fintype Ω₀] [Fintype X] [Fintype V] [Nonempty V] (T : TreeSound.Tree ι)
    (cert : ι → EdgeCert) (t : ι → State)
    (os : ι → Array (List ℕ)) (hr : ∀ v ∈ T.nodes, replayR (cert v).calls #[] 0 {} #[] = some (t v, os v))
    (hacc : ∀ v ∈ T.nodes, (cert v).accepts (os v) = true) (hver : ∀ v ∈ T.nodes, (cert v).verifies (os v) = true)
    (L : Layout) (hL : ∀ v ∈ T.nodes, (cert v).layout = L)
    (slot : ι → ℕ) (hslot : ∀ v ∈ T.nodes, v ≠ T.root → slot v < (cert (T.parent v)).children.length)
    (stRoot : Ω₀ × (X → Fin 4 → V) → ℕ → Fin 4 → K) (val : ι → Ω₀ × (X → Fin 4 → V) → Val)
    (hsroot : ∀ ω, Sat (stRoot ω) (t T.root) (val T.root ω)) (P : RecParts ι (Ω₀ × (X → Fin 4 → V)))
    (hP : P.Ok fun v ω => Sat (treeStmt T cert slot stRoot val (T.parent v) ω) (t (T.parent v))
      (val (T.parent v) ω))
    (batchBad : ι → Finset (Ω₀ × (X → Fin 4 → V))) (draw : ι → Ω₀ × (X → Fin 4 → V) → Fin 5 → E)
    (wit : ι → Ω₀ × (X → Fin 4 → V) → Witness)
    (hval : ∀ v ∈ T.nodes, v ≠ T.root → ∀ ω, val v ω = assign (stmtFirst (t v)) (wit v ω))
    (hlink : ChecksGiveRows T cert (fun v => stmtFirst (t v)) os L slot stRoot val P batchBad draw wit)
    (tD : Dense E → Prop) (tM : Matrix E → Prop) (bad : ι → Finset (Ω₀ × (X → Fin 4 → V)))
    (hstep : ∀ v ∈ T.nodes, ∀ ω, ω ∉ bad v →
      stmt T cert slot L (treeStmt T cert slot stRoot val) tD tM v ω → ins cert val tD tM v ω)
    (hroot : ∀ ω, stmt T cert slot L (treeStmt T cert slot stRoot val) tD tM T.root ω)
    (ch : X → C) (re : X → R) (hinj : ∀ x y, re x = re y → ch x = ch y → x = y)
    (σ : ι → Ω₀ → List (Fin 4 → V) → X) (Q : ι → ℕ) (hcrEq : ∀ v, P.crBad v = crEvent ch re (σ v) (Q v))
    (put : ι → Ω₀ × (X → Fin 4 → V) → (Fin 5 → E) → Ω₀ × (X → Fin 4 → V))
    (hgp : ∀ v ω x, draw v (put v ω x) = x) (hpg : ∀ v ω, put v ω (draw v ω) = ω)
    (hpp : ∀ v ω x y, put v (put v ω x) y = put v ω y) (hwit : ∀ v ω x, wit v (put v ω x) = wit v ω)
    (hfit : ∀ v ω T', (wit v ω).height T' ≤ 2 ^ 32) (N : ι → ℕ) (hN : ∀ v ω, (slots (wit v ω)).length ≤ N v)
    (epsPCS epsBatch : ι → ℚ≥0) (hpcs : PcsBound P epsPCS)
    (hbatch : ∀ v ∈ T.nodes, ((batchBad v).card : ℚ≥0) / Fintype.card (Ω₀ × (X → Fin 4 → V)) ≤ epsBatch v) :
    (Finset.card {ω | ∃ v ∈ T.nodes, ¬ (stmt T cert slot L (treeStmt T cert slot stRoot val) tD tM v ω ∧
        ins cert val tD tM v ω)} : ℚ≥0) / Fintype.card (Ω₀ × (X → Fin 4 → V)) ≤
      ∑ v ∈ T.nodes, (((bad v).card + ∑ j ∈ range (P.J v), (P.testBad v j).card : ℚ≥0) /
        Fintype.card (Ω₀ × (X → Fin 4 → V)) + epsPCS v + Edges.epsCR V (Q v) +
        ((4 * N v : ℕ) : ℚ≥0) / Fintype.card E + epsBatch v) :=
  tree_sound_crEvent T cert t os hr hacc hver L hL slot hslot stRoot val hsroot P hP batchBad draw wit hval hlink tD
    tM bad hstep hroot ch re hinj σ Q hcrEq epsPCS (fun v => ((4 * N v : ℕ) : ℚ≥0) / Fintype.card E) epsBatch hpcs
    (fun v _ => busBad_frac (stmtFirst (t v)) (wit v) (draw v) (put v) (hgp v) (hpg v) (hpp v) (hwit v) (hfit v) (N v) (hN v))
    hbatch

end Ideal

end LeanVMCircuits.Rec.AirLink
