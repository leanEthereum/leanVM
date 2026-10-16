module

public import LeanVMCircuits.Rec.TableSum
public import LeanVMCircuits.Rec.UnionCover

@[expose] public section

/-!
The AIR link's premise from the checks `checkbind` names.

`AirLink.ChecksGiveTable` asks, where every check's inputs are true, for the table sumcheck's input claim as the bus totals' `σ_0 + ξ σ_1`, the bus GKR's roots and the hash rows' packed witnesses on the committed witness. `checksGiveTable_of_named` gives it from the parts' inputs of three checks of child `v`'s parent: the table sumcheck `checkbind` names (`Bind.TableCert`, its input claim the sum of its honest instance `tableInst` on the committed witness), the bus GKR's first layer (its input claim, the named root, both trees' honest roots) and flock's reduction of the hash rows (`Flocked`). The totals and the root are the named wires' values in the parent's assignment and `ξ` the named `ξ`'s: where the parent's circuit is satisfied and its certificate accepted, `TableCert.claim_iff` reads the named sumcheck's input claim as the totals' `σ_0 + ξ σ_1`. What stays is that parts with these inputs meet `RecParts.Ok` with the round theorems' events (each check's output claims, the GKR's leaf claims through the bus forms `qforms` of `bus::verify_balance` and the sumcheck's column claims, being inputs of the checks after it down to the opening).
-/

namespace LeanVMCircuits.Rec.AirLink

open LeanVMCircuits.Rec Model Edges

variable {ι Ω : Type}

/-- `ChecksGiveTable` from the named checks' inputs: child `v`'s parent accepts its certificate `bc` and names the
table sumcheck `tc v`; check `jT v`'s input is that sumcheck's input claim being its honest instance's sum on the
committed witness at the named `ξ`, check `jG v`'s the named root being both trees' honest roots, and check `jF v`'s
the hash rows' packed witnesses. The totals and roots are the named wires' values. The root's premise may use the parent's calls holding (`Bind.Facts`, which its satisfied circuit gives). The certificates are checked on the parent's states `tb`, whose satisfaction `t`'s gives (`hsat`: `t` the circuits with their public rows reordered, `stmtFirst`). -/
theorem checksGiveTable_of_named [Fintype Ω] (T : TreeSound.Tree ι) (cert : ι → EdgeCert) (t : ι → State)
    (os : ι → Array (List ℕ)) (L : Layout) (slot : ι → ℕ) (stRoot : Ω → ℕ → Fin 4 → K) (val : ι → Ω → Val)
    (P : RecParts ι Ω) (n : ι → ℕ) (bdraw : (v : ι) → Ω → (Fin (n v) → E) × E)
    (qforms : (v : ι) → Ω → (Fin (n v) → E) → Fin 2 → Table → Quad) (draw : ι → Ω → Fin 5 → E)
    (taus : ι → Table → ℕ) (cols : ι → Ω → Table → ℕ → ℕ → K) (bc : ι → Bind.Cert) (tc : ι → Bind.TableCert)
    (jT jG jF : ι → ℕ) (tb : ι → State) (hsat : ∀ v st val', Sat st (t v) val' → Sat st (tb v) val')
    (hnamed : ∀ v ∈ T.nodes, v ≠ T.root → (bc (T.parent v)).accepts (tb (T.parent v)) = true ∧
      (tc v).ok (bc (T.parent v)) (bc (T.parent v)).outs = true ∧ jT v < P.J v ∧ jG v < P.J v ∧ jF v < P.J v)
    (hxi : ∀ v ω, (bdraw v ω).2 = Model.ev (val (T.parent v) ω) (tc v).xi)
    (hT : ∀ v ω sc, (bc (T.parent v)).sumchecks[(tc v).sc]? = some sc → P.inOk v (jT v) ω →
      Model.ev (val (T.parent v) ω) sc.claim0 =
        (tableInst (n v) (witAt T cert t slot stRoot val taus cols v ω) (bdraw v ω).1 (qforms v ω (bdraw v ω).1)
          (bdraw v ω).2).sum)
    (hG : ∀ v ω, Bind.Facts (bc (T.parent v)).calls (bc (T.parent v)).relax (bc (T.parent v)).outs
        (treeStmt T cert slot stRoot val (T.parent v) ω) (val (T.parent v) ω) → P.inOk v (jG v) ω →
      Model.ev (val (T.parent v) ω) (tc v).root = pullRoot (t v) (witAt T cert t slot stRoot val taus cols v ω) (draw v ω) ∧
      Model.ev (val (T.parent v) ω) (tc v).root = pushRoot (t v) (witAt T cert t slot stRoot val taus cols v ω) (draw v ω))
    (hF : ∀ v ω, P.inOk v (jF v) ω → Flocked (t v) (witAt T cert t slot stRoot val taus cols v ω)) :
    ChecksGiveTable T cert t os L slot stRoot val P n bdraw qforms
      (fun v ω _ i => Model.ev (val (T.parent v) ω) (if i = 0 then (tc v).tot0 else (tc v).tot1))
      (fun v ω _ => Model.ev (val (T.parent v) ω) (tc v).root) draw taus cols := by
  intro v hv hne ω hps hin _ _
  obtain ⟨hacc, hok, hjT, hjG, hjF⟩ := hnamed v hv hne
  have hFacts := (Bind.facts_of_holds (Bind.Cert.accepts_parts hacc).2.2.1
    (Bind.Sat.holds (hsat _ _ _ hps) (bc (T.parent v)).test)).1
  obtain ⟨sc, hsc, -⟩ := Bind.TableCert.sem hFacts hok
  obtain ⟨h0, h1⟩ := hG v ω hFacts (hin _ hjG)
  refine ⟨hF v ω (hin _ hjF), ?_, h0, h1, rfl⟩
  have h := (Bind.TableCert.claim_iff hFacts hok hsc _).mp (hT v ω sc hsc (hin _ hjT))
  rw [← hxi] at h
  simpa only [show ((1 : Fin 2) = 0) = False from by decide, if_true, if_false] using h

/-- Non-vacuity: parts whose three named checks' inputs are those claims meet `checksGiveTable_of_named`'s
hypotheses on the inputs. -/
theorem named_inputs [Fintype Ω] (T : TreeSound.Tree ι) (cert : ι → EdgeCert) (t : ι → State) (slot : ι → ℕ)
    (stRoot : Ω → ℕ → Fin 4 → K) (val : ι → Ω → Val) (n : ι → ℕ) (bdraw : (v : ι) → Ω → (Fin (n v) → E) × E)
    (qforms : (v : ι) → Ω → (Fin (n v) → E) → Fin 2 → Table → Quad) (draw : ι → Ω → Fin 5 → E)
    (taus : ι → Table → ℕ) (cols : ι → Ω → Table → ℕ → ℕ → K) (bc : ι → Bind.Cert) (tc : ι → Bind.TableCert)
    (outOk : ι → ℕ → Ω → Prop) (testBad : ι → ℕ → Finset Ω) (pcsBad crBad : ι → Finset Ω) :
    let w := witAt T cert t slot stRoot val taus cols
    let P : RecParts ι Ω := ⟨fun _ => 3, fun v j ω =>
      (j = 0 → ∀ sc, (bc (T.parent v)).sumchecks[(tc v).sc]? = some sc → Model.ev (val (T.parent v) ω) sc.claim0 =
        (tableInst (n v) (w v ω) (bdraw v ω).1 (qforms v ω (bdraw v ω).1) (bdraw v ω).2).sum) ∧
      (j = 1 → Model.ev (val (T.parent v) ω) (tc v).root = pullRoot (t v) (w v ω) (draw v ω) ∧
        Model.ev (val (T.parent v) ω) (tc v).root = pushRoot (t v) (w v ω) (draw v ω)) ∧
      (j = 2 → Flocked (t v) (w v ω)), outOk, testBad, pcsBad, crBad⟩
    (∀ v ω sc, (bc (T.parent v)).sumchecks[(tc v).sc]? = some sc → P.inOk v 0 ω →
      Model.ev (val (T.parent v) ω) sc.claim0 =
        (tableInst (n v) (w v ω) (bdraw v ω).1 (qforms v ω (bdraw v ω).1) (bdraw v ω).2).sum) ∧
    (∀ v ω, P.inOk v 1 ω → Model.ev (val (T.parent v) ω) (tc v).root = pullRoot (t v) (w v ω) (draw v ω) ∧
      Model.ev (val (T.parent v) ω) (tc v).root = pushRoot (t v) (w v ω) (draw v ω)) ∧
    (∀ v ω, P.inOk v 2 ω → Flocked (t v) (w v ω)) ∧ ∀ v, 0 < P.J v ∧ 1 < P.J v ∧ 2 < P.J v :=
  ⟨fun _ _ sc hsc h => h.1 rfl sc hsc, fun _ _ h => h.2.1 rfl, fun _ _ h => h.2.2 rfl,
    fun _ => ⟨by norm_num, by norm_num, by norm_num⟩⟩

end LeanVMCircuits.Rec.AirLink
