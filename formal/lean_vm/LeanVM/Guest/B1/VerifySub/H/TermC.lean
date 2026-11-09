/-
  LeanVM.Guest.B1.VerifySub.H.TermC

  `check_opening_terminal` on an honest child: its precondition on the honest memory, and its
  placed completeness as `verify_sub`'s thirteenth callee.
-/

module

public import LeanVM.Guest.B1.VerifySub.H.TermPre
public import LeanVM.Guest.B1.VerifySub.TermGlue
public import LeanVM.Guest.B1.Terminal.TermComplete

/-!
# The terminal, honestly

`vsTermB`: the terminal's buffers (the exponent table, `zeta`, `chi`, `kappa_base`,
`certify_placement`'s offsets, `z_vals`, `c_table`, `open_stacked`'s points).
`vsH_termPre`: on a memory holding `certify_placement`'s buffers, `open_stacked`'s points and the
terminal's words of `verify_sub`'s buffers, `TermPre` holds of the honest child.
`term_complete`: the terminal, entered on what `certify_placement` and `open_stacked` return, is
`CompleteAtD`.
-/

namespace LeanVM.Guest.B1.VerifySub

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Node

@[expose] public section

theorem readsAt_left {rd : Reader} {p : E} {xs ys : List E} (h : ReadsAt rd p (xs ++ ys)) :
    ReadsAt rd p xs := (Main.readsAt_append'.mp h).1

/-- The terminal's buffers. -/
def vsTermB (bs : List ℕ) (sqE eoff pb pb1 : ℕ) : TermBases :=
  ⟨sqE, vb bs 5, vb bs 8, vb bs 4, eoff, vb bs 9, vb bs 12, pb, pb1⟩

namespace ChildSegs

variable {bytecode : List K} {seed : Digest} {c : Child} (S : ChildSegs bytecode seed c)

/-- **`verify_tables`' honest data's shape facts the terminal's context takes.** -/
theorem H_ctxFacts (hbl : bytecode.length = 2 ^ 23) :
    S.H.rows.length = 6 ∧ S.H.bc.length = 2 ^ 23 ∧ S.H.lm ≤ S.H.point.length ∧
      19 ≤ S.H.point.length ∧ ∀ t < 6, Tables.vtHt S.H.rows t ≤ S.H.point.length := by
  have hb := S.μ_bounds hbl
  have hpl := (S.runG' hbl).2.2.1
  have hsl := S.hs_length
  refine ⟨S.hrowsL, hbl, ?_, ?_, fun t ht ↦ ?_⟩
  · rw [H_point, hpl, H_lm]; exact (height_le_depth S.logMem hsl (t := 0) (by norm_num)).2
  · rw [H_point, hpl]; omega
  · rw [H_rows, H_point, hpl, show Tables.vtHt S.rowsN t = S.hs.getD t 0 from rfl]
    exact (height_le_depth S.logMem hsl ht).1

end ChildSegs

/-- **The terminal's precondition on an honest child.** -/
theorem vsH_termPre {bytecode : List K} (hbl : bytecode.length = 2 ^ 23) {seed : Digest}
    {c : Child} (S : ChildSegs bytecode seed c) (bs : List ℕ) (sqE : ℕ) {rd : Reader}
    {e10 e11 e138 e139 e295 pb pb1 : ℕ} (hwl : S.w.point.length = S.μs)
    (hcpo : Main.MemL rd (Tables.cpOwn S.logMem S.hs e10 e11 e138 e139 e295))
    (hpt : ReadsAt rd (ofK (addressOfIndex pb)) (S.w.point ++ List.replicate (B1.Whir.pointCap -
        S.μs) 0))
    (hpt1 : ReadsAt rd (ofK (addressOfIndex pb1))
      (S.w.point.map (1 + ·) ++ List.replicate (B1.Whir.pointCap - S.μs) 1))
    (ht : Main.MemL rd (S.termLin bs sqE)) :
    TermPre rd S.layout S.bus S.claims ⟨qkeccak, S.op, S.word⟩ S.lam S.kpt (ringCoefficients S.rchs)
      S.w.point (termArgs (vsTermB bs sqE e295 pb pb1) S.H.rm (gen ^ S.μ) (gen ^ S.H.n)
        (gen ^ S.logMem) (gen ^ S.τ) S.lam S.w.inner S.w.residual S.w.target) := by
  obtain ⟨hok, -, -, -⟩ := S.H_run hbl
  obtain ⟨hr, hbc, hlmμ, h19, hτμ⟩ := S.H_ctxFacts hbl
  have hpl := (S.runG' hbl).2.2.1
  have hμ := S.μ_bounds hbl
  obtain ⟨-, hopl, hkpl, -, -⟩ := S.runK' hbl
  have hwl' : S.w.point.length = S.layout.stackLog := hwl
  -- the terminal's words
  have hm : ∀ q ∈ S.termLin bs sqE, ReadsAt rd (ofK (addressOfIndex q.1)) q.2 := ht
  have mZ : ReadsAt rd (ofK (addressOfIndex (vb bs 5))) S.point :=
    hm (vb bs 5, S.point) (by simp [ChildSegs.termLin])
  have mC : ReadsAt rd (ofK (addressOfIndex (vb bs 8))) S.chis :=
    hm (vb bs 8, S.chis) (by simp [ChildSegs.termLin])
  have mK : ReadsAt rd (ofK (addressOfIndex (vb bs 4))) (vsKbW S.logMem S.hs) :=
    hm (vb bs 4, vsKbW S.logMem S.hs) (by simp [ChildSegs.termLin])
  have mE : ReadsAt rd (ofK (addressOfIndex sqE)) expTableWords :=
    hm (sqE, expTableWords) (by simp [ChildSegs.termLin])
  have mV : ReadsAt rd (ofK (addressOfIndex (vb bs 9))) (zvW S.op S.kpt) :=
    hm (vb bs 9, zvW S.op S.kpt) (by simp [ChildSegs.termLin])
  have mT : ReadsAt rd (ofK (addressOfIndex (vb bs 12))) (ringCoefficients S.rchs) :=
    hm (vb bs 12, ringCoefficients S.rchs) (by simp [ChildSegs.termLin])
  -- `z_vals`
  have hopl39 : S.op.length ≤ 39 := by have := S.τ_bounds hbl; omega
  have mV' := Main.readsAt_append'.mp mV
  have mOp : ReadsAt rd (ofK (addressOfIndex (vb bs 9))) S.op := readsAt_left mV'.1
  have mKp : ReadsAt rd (ofK (addressOfIndex (vb bs 9)) * gen ^ qkeccakVarsCap) S.kpt := by
    have := mV'.2
    rwa [List.length_append, List.length_replicate, show S.op.length + (39 - S.op.length) = 39 by
      omega] at this
  -- the exponent table's nibble shares
  have hexp : ExpTables rd (ofK (addressOfIndex sqE)) :=
    (expTables_iff_words _ _).2 fun o ho ↦
      readsAt_getD' mE (by simpa [expTableWords, length_etWordsN] using ho)
  -- `kappa_base`
  have hcount : S.hs.map Hints.count = S.hs.map (gen ^ ·) :=
    List.map_congr_left fun x hx ↦ count_eq_gen (by have := S.hh29 hbl x hx; omega)
  -- `certify_placement`'s buffers
  have hcpOut : Tables.cpOut S.logMem S.hs
      [gen ^ Tables.stackTotal (columnKappas S.logMem Tables.guestLogBytecode S.hs),
        ofK (addressOfIndex e295)] (Tables.cpOwn S.logMem S.hs e10 e11 e138 e139 e295) :=
    ⟨e10, e11, e138, e139, e295, rfl, rfl⟩
  have hP := Tables.cp_out_ctx hcpOut hcpo
  have hK28 := committed_le28 hbl S.stack28
  -- the bus point
  have hbus : S.bus = S.H.busH := (Tables.vt_spec hok).2.1
  have hbp : S.bus.point = S.point := by rw [hbus]; rfl
  have hct := Tables.VtHonest.vtH_tctx hok hr hbc hlmμ h19 hτμ mZ mC
  rw [ChildSegs.H_point, hpl] at hct
  rw [S.hlayout] at hwl' ⊢
  simp only [TermPre, termArgs, vsTermB]
  refine ⟨termCtx_of_tctx hct, hP, fun c hc ↦ ?_, layoutOf_placements hbl _ _,
    layoutOf_stackLog hbl _ _, S.stack28, by show 1 ≤ S.logMem; have := S.h16; omega,
    S.h32, by rw [hbp, hpl]; omega, S.hs_length, S.hh29 hbl, rfl, rfl, ?_, gTabs_of_exp hexp, trivial,
    trivial, by rw [hopl, Tables.qkeccakSlotBits_eq]; rfl, mOp,
    by rw [hkpl, Tables.qkeccakSlotBits_eq]; rfl, mKp, by simp [ringCoefficients, kBits],
    mT, hwl', ?_, ?_⟩
  · have := hK28 c hc
    show (Tables.committedKappas (columnKappas S.logMem Tables.guestLogBytecode
      (Tables.tableHeightsOf S.rowsN))).getD c 0 < 29
    omega
  · show Tables.TbReadsAt rd _ (1 :: gen ^ S.logMem :: S.hs.map (gen ^ ·))
    rw [← hcount]; exact mK
  · unfold padPoint
    rw [hwl', show termPointCap = B1.Whir.pointCap from rfl]
    rw [← S.hlayout]; exact hpt
  · unfold padPoint
    rw [hwl', show termPointCap = B1.Whir.pointCap from rfl, List.map_append, List.map_replicate,
      add_zero]
    rw [← S.hlayout]; exact hpt1

theorem regionL_of {L : Main.Layout} {q : ℕ × List E} (hq : q ∈ L) {i : ℕ} (h1 : q.1 ≤ i)
    (h2 : i < q.1 + q.2.length) : Main.RegionL L i := ⟨q, hq, h1, h2⟩

variable {fs : String → ℕ} {cert : String → V → ℕ}

/-- The terminal's arguments on an honest child at the buffers `B`. -/
noncomputable def ChildSegs.termArgsH {bytecode : List K} {seed : Digest} {c : Child}
    (S : ChildSegs bytecode seed c) (B : TermBases) : List E :=
  termArgs B S.H.rm (gen ^ S.μ) (gen ^ S.H.n) (gen ^ S.logMem) (gen ^ S.τ) S.lam S.w.inner
    S.w.residual S.w.target

/-- **The terminal as `verify_sub`'s thirteenth callee**, entered on what `certify_placement` and
`open_stacked` return (`hwl`: the opening's terminal point has `μ` coordinates, `H/WhirLen`): any
property `Q` of a call of `check_opening_terminal` on its honest arguments at buffers `B`, words
`Lin` holding its precondition and its regions. -/
theorem term_via {bytecode : List K} (hbl : bytecode.length = 2 ^ 23) {seed : Digest}
    {c : Child} (S : ChildSegs bytecode seed c) {κ : ℕ} (bs : List ℕ) (sqE : ℕ)
    (hwl : S.w.point.length = S.μs) (pv : List (List E × Main.Layout))
    (ht : ((S.kids bs sqE).getD 12 noKid pv).taken = true)
    (Q : String → Main.Layout → List E → (List E → Main.Layout → Prop) → Prop)
    (hQ : ∀ (Lin : Main.Layout) (B : TermBases),
      (∀ rd, LowDef κ rd → Main.MemL rd Lin → TermPre rd S.layout S.bus S.claims
        ⟨qkeccak, S.op, S.word⟩ S.lam S.kpt (ringCoefficients S.rchs) S.w.point (S.termArgsH B)) →
      (∀ i, TermRegion B S.bus.point.length S.H.n (S.layout.tableLogHeights.getD opKeccak 0) i →
        Main.RegionL Lin i) →
      Q "check_opening_terminal" Lin (S.termArgsH B) (Returns [])) :
    Q ((S.kids bs sqE).getD 12 noKid pv).f ((S.kids bs sqE).getD 12 noKid pv).Lin
      ((S.kids bs sqE).getD 12 noKid pv).args ((S.kids bs sqE).getD 12 noKid pv).Out := by
  have hok : S.termOk pv := @of_decide_eq_true _ (Classical.propDecidable _) ht
  have hLin : ((S.kids bs sqE).getD 12 noKid pv).Lin =
      (ChildSegs.cpRes pv).2 ++ (ChildSegs.osRes pv).2 ++ S.termLin bs sqE := by
    show @ite _ _ (Classical.propDecidable _) _ _ = _
    rw [@ite_pos' _ _ (Classical.propDecidable _) _ _ hok]
  obtain ⟨⟨e10, e11, e138, e139, e295, hr9, hL9⟩, ⟨pb, pb1, hr11, hL11⟩⟩ := hok
  have hargs : ((S.kids bs sqE).getD 12 noKid pv).args =
      termArgs (vsTermB bs sqE e295 pb pb1) S.H.rm (gen ^ S.μ) (gen ^ S.H.n) (gen ^ S.logMem)
        (gen ^ S.τ) S.lam S.w.inner S.w.residual S.w.target := by
    show [_, _, _, _, _, _, _, _, _, _, (ChildSegs.cpRes pv).1.getD 1 0, _, _,
      (ChildSegs.osRes pv).1.getD 1 0, (ChildSegs.osRes pv).1.getD 2 0,
      (ChildSegs.osRes pv).1.getD 3 0, (ChildSegs.osRes pv).1.getD 4 0,
      (ChildSegs.osRes pv).1.getD 0 0] = _
    rw [hr9, hr11]
    rfl
  rw [hLin, hargs, hL9, hL11]
  show Q "check_opening_terminal" _ _ (Returns [])
  have hμ := S.μ_bounds hbl
  have hpl := (S.runG' hbl).2.2.1
  obtain ⟨hok', -, -, -⟩ := S.H_run hbl
  have hbus : S.bus = S.H.busH := (Tables.vt_spec hok').2.1
  have hbp : S.bus.point = S.point := by rw [hbus]; rfl
  have hτ := S.τ_bounds hbl
  obtain ⟨-, hopl, hkpl, -, -⟩ := S.runK' hbl
  have hμs : S.μs ≤ 28 := S.hmu28
  refine hQ _ (vsTermB bs sqE e295 pb pb1) (fun rd _ hm ↦ ?_) (fun i hi ↦ ?_)
  · obtain ⟨h12, hT⟩ := Main.memL_append.mp hm
    obtain ⟨hC, hO⟩ := Main.memL_append.mp h12
    exact vsH_termPre hbl S bs sqE hwl hC
      (hO (pb, S.w.point ++ List.replicate (B1.Whir.pointCap - S.μs) 0) (by simp))
      (hO (pb1, S.w.point.map (1 + ·) ++ List.replicate (B1.Whir.pointCap - S.μs) 1) (by simp)) hT
  · have hτl : S.layout.tableLogHeights.getD opKeccak 0 = S.τ := by rw [S.hlayout]; rfl
    simp only [TermRegion, vsTermB, hbp, hpl, hτl] at hi
    have hcl : S.chis.length = S.H.n := S.chis_length
    have hzl : (zvW S.op S.kpt).length = 39 + (S.τ + 6) := by
      simp [zvW, hopl, hkpl]; omega
    rcases hi with h | h | h | h | h | h | h | h | h | h
    · exact regionL_of (q := (vb bs 5, S.point)) (by simp [ChildSegs.termLin]) h.1 (by simp [hpl]; omega)
    · exact regionL_of (q := (vb bs 8, S.chis)) (by simp [ChildSegs.termLin]) h.1 (by simp [hcl]; omega)
    · exact regionL_of (q := (vb bs 4, vsKbW S.logMem S.hs)) (by simp [ChildSegs.termLin]) h.1
        (by simp [vsKbW, S.hs_length]; omega)
    · exact regionL_of (q := (e295, (stackOffsets (Tables.cpKs S.logMem S.hs)).1.map (gen ^ ·)))
        (by simp [Tables.cpOwn]) h.1
        (by simp [Tables.tb_stackOffsets_length, Tables.cpKs_length]; omega)
    · exact regionL_of (q := (sqE, expTableWords)) (by simp [ChildSegs.termLin]) (by omega)
        (by simp [expTableWords, length_etWordsN]; omega)
    · exact regionL_of (q := (vb bs 9, zvW S.op S.kpt)) (by simp [ChildSegs.termLin]) h.1
        (by rw [hzl]; omega)
    · exact regionL_of (q := (vb bs 9, zvW S.op S.kpt)) (by simp [ChildSegs.termLin]) (by omega)
        (by rw [hzl]; omega)
    · exact regionL_of (q := (vb bs 12, ringCoefficients S.rchs)) (by simp [ChildSegs.termLin]) h.1
        (by simp [ringCoefficients, kBits]; omega)
    · exact regionL_of (q := (pb, S.w.point ++ List.replicate (B1.Whir.pointCap - S.μs) 0))
        (by simp) h.1 (by simp [hwl, B1.Whir.pointCap]; omega)
    · exact regionL_of (q := (pb1, S.w.point.map (1 + ·) ++ List.replicate (B1.Whir.pointCap - S.μs) 1))
        (by simp) h.1 (by simp [hwl, B1.Whir.pointCap]; omega)

namespace ChildSegs

variable {bytecode : List K} {seed : Digest} {c : Child} (S : ChildSegs bytecode seed c)

/-- The batch's round count is at most `40`. -/
theorem H_n_le40 (hbl : bytecode.length = 2 ^ 23) : S.H.n ≤ 40 := by
  obtain ⟨t, ht, e⟩ := Tables.VtHonest.vtH_n_ex (H := S.H) S.hrowsL
  have := S.hh29 hbl (Tables.vtHt S.rowsN t) (by
    show Tables.vtHt S.rowsN t ∈ Tables.tableHeightsOf S.rowsN
    rw [Tables.vt_tableHeights_eq S.hrowsL]
    exact List.mem_map.mpr ⟨t, List.mem_range.mpr ht, rfl⟩)
  have e' : Tables.vtHt S.rowsN t = S.H.n := e
  omega

/-- The bus point has at most `34` coordinates. -/
theorem bus_point_le34 (hbl : bytecode.length = 2 ^ 23) : S.bus.point.length ≤ 34 := by
  have hμ := S.μ_bounds hbl
  have hpl := (S.runG' hbl).2.2.1
  obtain ⟨hok', -, -, -⟩ := S.H_run hbl
  have hbus : S.bus = S.H.busH := (Tables.vt_spec hok').2.1
  have hbp : S.bus.point = S.point := by rw [hbus]; rfl
  rw [hbp, hpl]; omega

end ChildSegs

/-- **The terminal is complete on an honest child**, entered on what `certify_placement` and
`open_stacked` return (`hwl`: the opening's terminal point has `μ` coordinates, `H/WhirLen`). -/
theorem term_complete {bytecode : List K} (hbl : bytecode.length = 2 ^ 23) {seed : Digest}
    {c : Child} (S : ChildSegs bytecode seed c) {κ : ℕ} (hκ : 16 ≤ κ) (bs : List ℕ) (sqE : ℕ)
    (hwl : S.w.point.length = S.μs) (pv : List (List E × Main.Layout))
    (ht : ((S.kids bs sqE).getD 12 noKid pv).taken = true) :
    CompleteAtD fs cert κ ((S.kids bs sqE).getD 12 noKid pv).f
      ((S.kids bs sqE).getD 12 noKid pv).Lin ((S.kids bs sqE).getD 12 noKid pv).args
      ((S.kids bs sqE).getD 12 noKid pv).Out :=
  term_via hbl S bs sqE hwl pv ht (CompleteAtD fs cert κ) fun _ B hpre hreg ↦
    check_opening_terminal_completeAt κ (by omega) B _ (nc := S.H.n) (S.H_n_le40 hbl) rfl hpre hreg
      (S.bus_point_le34 hbl) (S.fin hbl)

end
end LeanVM.Guest.B1.VerifySub
