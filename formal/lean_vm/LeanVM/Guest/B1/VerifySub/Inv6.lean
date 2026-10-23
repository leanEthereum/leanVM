/-
  LeanVM.Guest.B1.VerifySub.Inv6

  An accepting deferred verifier, within the deployed limits, has a run `verify_sub` completes
  on (`VsData.Ok`, `VsData.TOk`).
-/

module

public import LeanVM.Guest.B1.VerifySub.Inv6a
public import LeanVM.Guest.B1.VerifySub.CPlaced0
public import LeanVM.Guest.B1.VerifySub.TablesLen
public import LeanVM.Guest.B1.Whir.OpenLen

/-!
# The inversion of `verifyDeferred`

`vs_inversion`: when the deferring verifier accepts `π` for `pi` under `seed` and the claims `c`,
with a stack log of at least 22 and at most 8192 stream words, its run is a `VsData` within the
deployed limits whose seed, public input, fixed claims and proof are those (`VsData.Ok`,
`VsData.TOk`); the opening's point length is group 4's `whirOpen_point_length`.
-/

namespace LeanVM.Guest.B1.VerifySub

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.Blake2sHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

theorem runs_unique {α : Type} {p : Prog α} {s s1 s2 : St} {a1 a2 : α} (h1 : Runs p s a1 s1)
    (h2 : Runs p s a2 s2) : a1 = a2 ∧ s1 = s2 := by
  unfold Runs at h1 h2
  rw [h1, Option.some.injEq, Prod.mk.injEq] at h2
  exact h2

/-- **The inversion**: an accepting deferred verifier within the deployed limits runs as a
`VsData` within them. -/
theorem vs_inversion {bytecode : List K} (hb : bytecode.length = 2 ^ 22)
    {seed pi : Digest} {c : FixedClaims} {π : Proof} (h : verifyDeferred bytecode seed pi c π = true)
    (hlo : ∀ layout r, announced bytecode π.stream = some (layout, r) → 22 ≤ layout.stackLog)
    (hst : π.stream.length ≤ 8192) :
    ∃ D : VsData, D.Ok bytecode ∧ D.TOk bytecode ∧ D.seed = seed ∧ D.pi = pi ∧ D.fresh = c ∧
      D.proof = π := by
  obtain ⟨sF, hrun, hsF, hoF⟩ := verifyDeferred_inv h
  unfold deferredProgram at hrun
  obtain ⟨u, sE, hE, hret⟩ := runs_bind_inv' hrun
  obtain ⟨-, rfl⟩ := runs_pure_inv hret
  rw [verifyExecution_split] at hE
  obtain ⟨lr, s1, h1, hE⟩ := runs_bind_inv' hE
  obtain ⟨u2, s2, h2, hE⟩ := runs_bind_inv' hE
  obtain ⟨alphas, s3, h3, hE⟩ := runs_bind_inv' hE
  obtain ⟨beta, s4, h4, hE⟩ := runs_bind_inv' hE
  obtain ⟨gr, s5, h5, hE⟩ := runs_bind_inv' hE
  obtain ⟨bc, s6, h6, hE⟩ := runs_bind_inv' hE
  obtain ⟨fl, s7, h7, hE⟩ := runs_bind_inv' hE
  obtain ⟨rs, s8, h8, h9⟩ := runs_bind_inv' hE
  have hann := announced_of_runs h1
  obtain ⟨logMem, rows, rate, rfl, e1s, e1c, e1o, e1r, hm1, hm2, hr1, hr2, hl, hrows, hs28⟩ :=
    vs_readSizes_inv hb h1
  have hs22 := hlo _ _ hann
  obtain ⟨x0, x1, root, hroot, e2s, e2c, e2o, e2r⟩ := vs_commitStack_inv h2
  have hx0 : x0 = (digestScalars root).1 := congrArg Prod.fst hroot
  have hx1 : x1 = (digestScalars root).2 := congrArg Prod.snd hroot
  subst hx0 hx1
  obtain ⟨rfl, rfl⟩ := runs_sampleN_det h3
  obtain ⟨rfl, rfl⟩ := runs_sampleE_det h4
  obtain ⟨xsG, e5s, e5o, e5r, hG⟩ := qfree_frame (qfree_gkrPhase _) _ _ _ _ _ _ h5
  obtain ⟨hg0, hgl, hgv⟩ := vs_gkr_inv h5
  obtain ⟨xsT, e6s, e6o, e6r, hT⟩ := qfree_frame (qfree_tablesSeg _ _ _ _ _ _ _) _ _ _ _ _ _ h6
  obtain ⟨hpt, -⟩ := vs_tables_inv h6
  obtain ⟨xsF, e7s, e7o, e7r, hF⟩ := qfree_frame (qfree_verifyFlock _ _) _ _ _ _ _ _ h7
  obtain ⟨zSkip, chi, rc, hfl, hchi, hrc, hsl, hz, hrow, hcol, -⟩ := vs_flock_inv h7
  obtain ⟨rfl, rfl⟩ := runs_unique h8 (runs_ringSwitch fl.1 fl.2 s7.cv s7.stream s7.openings s7.roots)
  unfold verifyStackedOpening at h9
  obtain ⟨lam, s9, h9a, h9⟩ := runs_bind_inv' h9
  obtain ⟨rfl, rfl⟩ := runs_sampleE_det h9a
  rw [verifyWhir_split] at h9
  obtain ⟨w, s10, hw, hreq⟩ := runs_bind_inv' h9
  obtain ⟨hacc, rfl⟩ := runs_require_inv hreq
  obtain ⟨xsW, osW, e10s, e10o, hW⟩ := runs_frame _ _ _ _ _ _ _ hw
  obtain ⟨chis, rm, hclen, hcl⟩ := vs_tablesSeg_claimsOk hb hm1 hl hgl hT
  simp only at e1s e1c e1o e1r e5s e5o e5r e10s e10o
  have h8l : flockNumLincheckRounds = 8 := by decide
  have h6k : flockKSkip = 6 := by decide
  rw [h8l] at hfl hrc hrow
  subst hfl
  -- the chain's states
  have c2 : s2.cv = obsAll (obsAll (blake2sBytes (digestBytes seed ++ digestBytes pi))
      (announce logMem rows rate)) [(digestScalars root).1, (digestScalars root).2] := by
    rw [e2c, e1c]
  rw [c2] at hG hT hpt
  -- the openings and the roots
  have o9 : π.openings = osW := by
    rw [← List.append_nil osW, ← hoF, ← e10o, e7o, e6o, e5o, e2o, e1o]
  have r9 : s7.roots = [(root, stackShape (layoutOf bytecode logMem rows).stackLog rate)] := by
    rw [e7r, e6r, e5r, e2r, e1r]; rfl
  rw [← o9] at hW
  simp only [r9] at hW
  -- the stream
  have hstream : π.stream = announce logMem rows rate ++ (digestScalars root).1 ::
      (digestScalars root).2 :: (xsG ++ (xsT ++ (xsF ++ xsW))) := by
    rw [e1s, e2s, e5s, e6s, e7s, e10s, hsF]
    simp
  have hpt' : (gr.2.1.take 18 ++ (sqAll 4 (obsAll (obsAll (blake2sBytes (digestBytes seed ++
      digestBytes pi)) (announce logMem rows rate)) [(digestScalars root).1,
      (digestScalars root).2])).1) = c.bytecodePoint := by
    rw [← layoutOf_logBytecode hb logMem rows]; exact hpt
  have hlb := layout_bounds hb hl hs28
  have hOpen : RunsWith (whirOpen (layoutOf bytecode logMem rows).stackLog rate
      (dot (powers (challengeOf (sqCv (sqAll 6 s7.cv).2)) (bc.2.length + 1))
        (ringTarget c.slices (sqAll 6 s7.cv).1 :: bc.2.map (·.value))))
      (sqCv (sqAll 6 s7.cv).2) xsW π.openings
      [(root, stackShape (layoutOf bytecode logMem rows).stackLog rate)] w sF.cv sF.roots := by
    convert hW using 3
    · simp
    · simp [ringSwitchClaim, ColumnClaim.onStack, Function.comp_def]
  refine ⟨⟨seed, pi, logMem, rows, rate, root, xsG, gr, s5.cv, xsT, bc.1, bc.2, s6.cv,
    gen ^ chis.length, c.bytecodeValue, rm, xsF, c.zSkip, c.alpha, c.matrixValue, chi, rc, c.slices,
    s7.cv, xsW, π.openings, w, sF.cv, sF.roots, chis⟩, ⟨hm1, hm2, hr1, hr2, hl, hlb.2, hs22, hs28,
    hlb.1, hG, hgl, hgv, ?_, ?_, ?_, ?_, hrc, hsl, ?_, ?_, ?_⟩, ?_, rfl, rfl, ?_, ?_⟩
  · intro ev hev rest os roots
    refine (vs_tables_inv (hT rest os roots)).2 ev ?_
    convert hev using 2
    all_goals first
      | rfl
      | (rw [← hpt']
         simp only [VsData.alphas, VsData.cv10, VsData.cv0, VsData.ann, VsData.x0, VsData.x1,
           layoutOf_logBytecode hb])
  · have := congrArg List.length hcl.2.1
    simpa [claimColumns_length] using this
  · intro ev hev rest os roots
    obtain ⟨-, -, -, -, -, -, -, -, -, -, hall⟩ := vs_flock_inv (hF rest os roots)
    exact hall ev (by rw [← hrow, ← hcol]; exact hev)
  · rw [hchi, h6k]
    simp only [VsData.tau, VsData.hs, blake2sR1csLogSize]
    simp [layoutOf, opBlake2s]
    omega
  · exact hOpen
  · exact whirOpen_point_length hs22 hs28 hr1 hr2 hOpen
  · convert hacc using 1
    funext x
    simp only [stackWeight, ringSwitchClaim, List.length_cons, List.map_cons]
    rfl
  · exact VsData.TOk.of_claims hcl rfl (by
      simp only [VsData.stream, VsData.ann, VsData.x0, VsData.x1, VsData.tail]
      rw [← hstream]; exact hst) hclen
  · cases c with
    | mk bp bvv al zs rp cp sl mv =>
      simp only at hpt' hrow hcol
      subst hpt' hrow hcol
      rfl
  · simp only [VsData.proof, VsData.stream, VsData.ann, VsData.x0, VsData.x1, VsData.tail]
    rw [← hstream]

end
end LeanVM.Guest.B1.VerifySub
