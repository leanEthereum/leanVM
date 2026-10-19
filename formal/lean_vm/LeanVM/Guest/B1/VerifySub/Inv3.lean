/-
  LeanVM.Guest.B1.VerifySub.Inv3

  GKR's and the tables' runs, backward.
-/

module

public import LeanVM.Guest.B1.VerifySub.Inv2

/-!
# GKR and the tables, backward

* `vs_gkr_inv`: a run of `gkrPhase depth` returns a nonzero count root, a point of `depth`
  coordinates and three values;
* `vs_tables_inv`: a run of `tablesSeg` at the claimed values reads the bytecode at the claimed point,
  and runs the same at every evaluation taking the claimed value there.
-/

namespace LeanVM.Guest.B1.VerifySub

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.Blake2sHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

theorem vs_gkrStep_inv {step : ℕ} {g g' : GkrState} {s s' : St} (h : Runs (gkrStep step g) s g' s') :
    g'.point.length = step + g.point.length ∧ g'.values.length = 3 := by
  unfold gkrStep at h
  obtain ⟨cb, s1, -, h⟩ := runs_bind_inv' h
  obtain ⟨⟨x, cl⟩, s2, hs, h⟩ := runs_bind_inv' h
  obtain ⟨c0, s3, -, h⟩ := runs_bind_inv' h
  obtain ⟨c1, s4, -, h⟩ := runs_bind_inv' h
  obtain ⟨c2, s5, -, h⟩ := runs_bind_inv' h
  obtain ⟨u, s6, -, h⟩ := runs_bind_inv' h
  obtain ⟨y, s7, hy, h⟩ := runs_bind_inv' h
  obtain ⟨rfl, -⟩ := runs_pure_inv h
  have h1 := runs_sumcheck_inv hs
  have h2 := runs_sampleN_inv hy
  simp only [List.length_map] at h1
  simp [h1, h2]

theorem vs_gkrLayers_inv : ∀ {n : ℕ} {g g' : GkrState} {s s' : St}, Runs (gkrLayers n g) s g' s' →
    g.values.length = 3 → g'.point.length = n + g.point.length ∧ g'.values.length = 3
  | 0, g, g', s, s', h, hv => by
    unfold gkrLayers at h
    obtain ⟨rfl, -⟩ := runs_pure_inv h
    exact ⟨by simp, hv⟩
  | 1, g, g', s, s', h, _ => by
    unfold gkrLayers at h
    obtain ⟨g1, s1, h1, h2⟩ := runs_bind_inv' h
    obtain ⟨a1, a2⟩ := vs_gkrStep_inv h1
    obtain ⟨b1, b2⟩ := vs_gkrLayers_inv h2 a2
    exact ⟨by omega, b2⟩
  | n + 2, g, g', s, s', h, _ => by
    unfold gkrLayers at h
    split at h
    · obtain ⟨g1, s1, h1, h2⟩ := runs_bind_inv' h
      obtain ⟨a1, a2⟩ := vs_gkrStep_inv h1
      obtain ⟨b1, b2⟩ := vs_gkrLayers_inv h2 a2
      exact ⟨by omega, b2⟩
    · obtain ⟨g1, s1, h1, h2⟩ := runs_bind_inv' h
      obtain ⟨a1, a2⟩ := vs_gkrStep_inv h1
      obtain ⟨b1, b2⟩ := vs_gkrLayers_inv h2 a2
      exact ⟨by omega, b2⟩

/-- **GKR's run, backward.** -/
theorem vs_gkr_inv {depth : ℕ} {r : E × List E × List E} {s s' : St} (h : Runs (gkrPhase depth) s r s') :
    r.1 ≠ 0 ∧ r.2.1.length = depth ∧ r.2.2.length = 3 := by
  unfold gkrPhase verifyGkrGrandProducts at h
  obtain ⟨r0, s0, h, hq⟩ := runs_bind_inv' h
  obtain ⟨u, s5, hreq, hr⟩ := runs_bind_inv' hq
  obtain ⟨hne, -⟩ := runs_require_inv hreq
  obtain ⟨rfl, -⟩ := runs_pure_inv hr
  obtain ⟨sh, s1, -, h⟩ := runs_bind_inv' h
  obtain ⟨cn, s2, -, h⟩ := runs_bind_inv' h
  obtain ⟨g, s3, hg, h⟩ := runs_bind_inv' h
  obtain ⟨rfl, -⟩ := runs_pure_inv h
  obtain ⟨a1, a2⟩ := vs_gkrLayers_inv hg rfl
  exact ⟨hne, by simpa using a1, a2⟩

theorem claimed_bytecode_inv {c : FixedClaims} {w : List K} {pt : List E} {v : E} {s s' : St}
    (h : Runs ((Evaluations.claimed c).bytecode w pt) s v s') :
    pt = c.bytecodePoint ∧ v = c.bytecodeValue ∧ s' = s := by
  by_cases hp : pt = c.bytecodePoint
  · have e : (Evaluations.claimed c).bytecode w pt = Prog.ret c.bytecodeValue := by
      simp [Evaluations.claimed, Prog.require, hp]
    rw [e] at h
    obtain ⟨rfl, rfl⟩ := runs_ret_inv h
    exact ⟨hp, rfl, rfl⟩
  · have e : (Evaluations.claimed c).bytecode w pt = Prog.fail := by
      simp [Evaluations.claimed, Prog.require, hp, Prog.bind]
    rw [e] at h
    cases h

/-- **The tables' run, backward**: at the claimed values, the bytecode is read at the claimed
point, and the run is the same at every evaluation taking the claimed value there. -/
theorem vs_tables_inv {c : FixedClaims} {layout : Layout} {pi : Digest} {alphas : List E} {beta : E}
    {point values : List E} {s s' : St} {out : BusResult × List ColumnClaim}
    (h : Runs (tablesSeg (.claimed c) layout pi alphas beta point values) s out s') :
    point.take layout.logBytecode ++ alphas = c.bytecodePoint ∧
      ∀ ev, BytecodeAt ev layout.bytecode c.bytecodePoint c.bytecodeValue →
        Runs (tablesSeg ev layout pi alphas beta point values) s out s' := by
  unfold tablesSeg at h
  obtain ⟨bus, s1, hb, h⟩ := runs_bind_inv' h
  unfold busRest at hb
  obtain ⟨m, t1, hm, hb⟩ := runs_bind_inv' hb
  obtain ⟨mf, t2, hmf, hb⟩ := runs_bind_inv' hb
  obtain ⟨bf, t3, hbf, hb⟩ := runs_bind_inv' hb
  dsimp only at hb
  obtain ⟨bv, t4, hbv, hb4⟩ := runs_bind_inv' hb
  obtain ⟨e, rfl, rfl⟩ := claimed_bytecode_inv hbv
  refine ⟨e, fun ev hev => ?_⟩
  unfold tablesSeg busRest
  refine Runs.bind_m (Runs.bind_m hm (Runs.bind_m hmf (Runs.bind_m hbf ?_))) h
  dsimp only
  exact Runs.bind_m (by rw [e]; exact hev _) hb4

end
end LeanVM.Guest.B1.VerifySub
