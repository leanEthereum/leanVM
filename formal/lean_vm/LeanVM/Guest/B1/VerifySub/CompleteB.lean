/-
  LeanVM.Guest.B1.VerifySub.CompleteB

  `verify_sub` is complete on every honest child within `vsBound` words: its frame, its own
  buffers and its thirteen callees' bounds, the callees' words facts (`VsWords`) and
  `verify_keccak`'s bounded completeness (`VkCompleteAtB`) assumed.
-/

module

public import LeanVM.Guest.B1.VerifySub.Complete
public import LeanVM.Guest.B1.VerifySub.WordsB
public import LeanVM.Guest.B1.VerifySub.H.TermCB
public import LeanVM.Guest.B1.Terminal.KidsDepB
public import LeanVM.Guest.B1.Ring.CompleteB
public import LeanVM.Guest.B1.Gkr.VbgB
public import LeanVM.Guest.B1.Tables.VtC.ABound
public import LeanVM.Guest.B1.Place.OsCandB
public import LeanVM.Guest.Budget.Bounded
public import LeanVM.Guest.B1.Placement.CertifyAt
public import LeanVM.Guest.B1.Tables.VtC.AWeight
public import LeanVM.Guest.B1.VerifySub.H.TermCBW
public import LeanVM.Guest.B1.VerifySub.H.VtShape
public import LeanVM.Guest.B1.VerifySub.H.WhirLen

/-!
# `verify_sub` within a bound

The callees' words facts are `VerifySub/WordsB`'s (`VsWords`), with `open_stacked`'s here
(`VsWordsOs`). `vsBs W Bvk`: the sixteen callees' bounds, in call order (`Data.core18`): two
`g_power_of_word`s, `log2_ceil_in_the_exponent__L0_L34`, `certify_placement`,
`log2_ceil_in_the_exponent__L15_L34`, `grind_check__L15`, the `squeeze_point_from` dispatch,
`opening_message__L1_L1`, the `bus_grind_check` dispatch, `verify_bus_gkr`, `verify_tables`,
`verify_keccak`, `grind_check__L14`, `ring_switch_target`, the `open_stacked` dispatch and the
terminal; the maxima over the honest children's depths (`vbgMax`, `vtMax`, `osMax`) or a
dispatch's arms (`armMax`) where a callee's bound depends on them. `vsBound W Bvk =
fs "verify_sub" + 8706 + (vsBs W Bvk).sum`: the frame, the own buffers (`8677 + μ` words,
`μ ≤ 29`) and the callees. `vsNames μ r d`, `vsTs`: the callees' names (the squeeze's arm at the
stack log `μ`, the bus grind's at the depth `d`, `open_stacked`'s candidate) and trees, within
their bounds, `verify_tables`' and the terminal's within their weights (`vsPs`).

`verify_sub_completeB`: on every honest child, `verify_sub` is `CompleteAtDTB … (fun _ ↦ True)
(vsBound W Bvk)`, by `completeAt_flatDepRB` with `vs_obligations` and the callees' bounded
completeness (`vs_kidsDepB`).
-/

namespace LeanVM.Guest.B1.VerifySub

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Node LeanVM.Guest.Memory

@[expose] public section

/-! ## The bounds -/

/-- `verify_bus_gkr`'s bound over the depths below `30`. -/
@[irreducible] def vbgMax (fs : String → ℕ) (K29 R K8 : ℕ) : ℕ :=
  lmax ((List.range 30).map (Tables.vbgBound fs K29 R K8))

/-- `verify_tables`' bound at the bus depth `m` and the largest height `n`. -/
noncomputable def vtBnd (fs : String → ℕ) (Kf : String → ℕ) (Ksh K10 m n : ℕ) : ℕ :=
  fs "verify_tables" + (3841 + m + 9 * (n + 1)) +
    ((Tables.vtBs Kf Ksh (Tables.vtRunB fs K10 n)).sum + Tables.ifFrames fs Tables.vtPre)

/-- `verify_tables`' bound over the depths below `30` and the heights below `29`. -/
@[irreducible] noncomputable def vtMax (fs : String → ℕ) (Kf : String → ℕ) (Ksh K10 : ℕ) : ℕ :=
  lmax ((List.range 30).flatMap fun m ↦ (List.range 29).map (vtBnd fs Kf Ksh K10 m))

/-- `open_stacked`'s bound over the candidates (stack logs below `29`, rates below `5`). -/
@[irreducible] noncomputable def osMax (fs Bnd Kr : String → ℕ) : ℕ :=
  lmax ((List.range 29).flatMap fun μ ↦ (List.range 5).map (osBosAt fs Bnd Kr μ))

/-- **`verify_sub`'s callees' words facts with `open_stacked`'s**: its leaves' and residual loops'
(`Bnd`, `Kr`). -/
structure VsWordsOs (fs : String → ℕ) extends VsWords fs where
  Bnd : String → ℕ
  Kr : String → ℕ
  hleaf : OsLeafBounds fs Bnd
  hloop : ∀ μ r, 22 ≤ μ → μ ≤ 28 → 1 ≤ r → r ≤ 4 →
    OsLoopBounds fs Kr (B1.Whir.osCfg (B1.Whir.candidate μ r))

/-- **The callees' bounds**, in call order, `open_stacked`'s `os`. -/
noncomputable def vsBsWith {fs : String → ℕ} (W : VsWordsOs fs) (Bvk os : ℕ) : List ℕ :=
  [W.Bg, W.Bg, fs "log2_ceil_in_the_exponent__L0_L34" + 34 + 2 * fs "assert_small_g_power",
    fs "certify_placement" + Tables.cpSizes.sum,
    fs "log2_ceil_in_the_exponent__L15_L34" + 34 + 2 * fs "assert_small_g_power",
    W.Kst "grind_check__L15", armMax W.Kst squeezeNames, W.Kst "opening_message__L1_L1",
    armMax W.Kst busGrindNames, vbgMax fs W.K29 W.R W.K8, vtMax fs W.Kf W.Ksh W.K10, Bvk,
    W.Kst "grind_check__L14", fs "ring_switch_target" + 72 + W.B14, os,
    termBound fs W.Beqc W.K15 W.Bcs W.Brs]

/-- **The callees' bounds at one candidate**: `open_stacked`'s at the stack log `μ` and the
rate `r`. -/
noncomputable def vsBsAt {fs : String → ℕ} (W : VsWordsOs fs) (Bvk μ r : ℕ) : List ℕ :=
  vsBsWith W Bvk (osBosAt fs W.Bnd W.Kr μ r)

/-- **The callees' bounds**, `open_stacked`'s the largest over the candidates. -/
noncomputable def vsBs {fs : String → ℕ} (W : VsWordsOs fs) (Bvk : ℕ) : List ℕ :=
  vsBsWith W Bvk (osMax fs W.Bnd W.Kr)

/-- **`verify_sub`'s bound**: its frame, its own buffers (`8677 + μ`, `μ ≤ 29`), its callees. -/
noncomputable def vsBound {fs : String → ℕ} (W : VsWordsOs fs) (Bvk : ℕ) : ℕ :=
  fs "verify_sub" + 8706 + (vsBs W Bvk).sum

/-- **`verify_sub`'s bound at one candidate.** -/
noncomputable def vsBoundAt {fs : String → ℕ} (W : VsWordsOs fs) (Bvk μ r : ℕ) : ℕ :=
  fs "verify_sub" + 8706 + (vsBsAt W Bvk μ r).sum

/-! ## The callees' trees -/

/-- **`verify_sub`'s callees' names**, in call order: the squeeze's arm at the stack log `μ`, the
bus grind's at the depth `d`, `open_stacked`'s candidate `openName μ r`. -/
def vsNames (μ r d : ℕ) : List String :=
  ["g_power_of_word", "g_power_of_word", "log2_ceil_in_the_exponent__L0_L34", "certify_placement",
    "log2_ceil_in_the_exponent__L15_L34", "grind_check__L15", squeezeNames.getD (μ - 22) "",
    "opening_message__L1_L1", busGrindNames.getD d "", "verify_bus_gkr", "verify_tables",
    "verify_keccak", "grind_check__L14", "ring_switch_target", B1.Whir.openName μ r,
    "check_opening_terminal"]

/-- **`verify_sub`'s callees' predicates**: `verify_tables`' tree within `vtWB`, the terminal's
within `termWB`, at each opcode's weights. -/
noncomputable def vsPs {fs : String → ℕ} (W : VsWordsOs fs) : List (Tree → Prop) :=
  List.replicate 10 (fun _ ↦ True) ++
    [fun t ↦ ∀ op, Budget.WeighsLe coreProgram (W.ωv op) (vtWB W.toVsWords op) t] ++
    List.replicate 4 (fun _ ↦ True) ++
    [fun t ↦ ∀ op, Budget.WeighsLe coreProgram (W.ωv op) (termWB W.toVsWords op) t]

/-- **`verify_sub`'s callees' trees**: callee `j` a call of its name within its bound satisfying
its predicate. -/
noncomputable def vsTs (fs : String → ℕ) (W : VsWordsOs fs) (Bvk μ r d : ℕ) : List (Tree → Prop) :=
  namedP fs (vsNames μ r d) (vsBsAt W Bvk μ r) (vsPs W)

/-- **`verify_keccak`, placed, within `Bvk` words** (`VkCompleteAt` bounded). -/
def VkCompleteAtB (fs : String → ℕ) (cert : String → V → ℕ) (κ Bvk : ℕ) : Prop :=
  ∀ (τ : ℕ) (f chis outs xs op point slices cap' : List E) (word m0 : E)
    (curE chiE olE zvE slE : ℕ), 9 ≤ τ → τ ≤ 28 → τ ≤ chis.length → outs.length = 25 →
    f.length = 5 → AllCanonical f → (∃ sp, (⟨f, []⟩ : Fs).Carries sp) →
    RunsTo (keccakSeg τ (chis.take τ) outs) ⟨f, []⟩ xs
      (([⟨qkeccak, op, word⟩], point, slices), m0) ⟨cap', []⟩ →
    CompleteAtB fs cert κ "verify_keccak"
      [(curE, xs), (chiE, chis), (olE, outs), (zvE, op), (zvE + qkeccakVarsCap, point),
        (slE, slices)]
      (f ++ [ofK (addressOfIndex curE), gen ^ τ, ofK (addressOfIndex chiE), ofK (addressOfIndex
          olE), ofK (addressOfIndex zvE),
        ofK (addressOfIndex slE)])
      (Returns (cap' ++ [ofK (addressOfIndex curE) * gen ^ xs.length, word, m0])) Bvk

variable {fs : String → ℕ} {cert : String → V → ℕ}

/-! ## The callees within their bounds -/

/-- **`g_power_of_word`, placed, within its words.** -/
theorem gpw_completeAtB (κ : ℕ) (Lin : Main.Layout) {n : ℕ} (hn : n < 2 ^ 6) {Bg : ℕ}
    (hg : TotalLe coreProgram fs "g_power_of_word" fun _ ↦ Bg) :
    CompleteAtB fs cert κ "g_power_of_word" Lin [eOfNat n] (Returns [gen ^ n]) Bg :=
  completeAt_of_rel_pureB (B := fun _ ↦ Bg) gpw_pure (List.mem_singleton_self _)
    (fun rd _ ↦ (g_power_of_word_holds rd [eOfNat n] [gen ^ n]).2
      (show ∃ m < 2 ^ 6, eOfNat n = eOfNat m ∧ [gen ^ n] = [gen ^ m] from ⟨n, hn, rfl, rfl⟩)) κ hg

/-- **`assert_canonical`, placed, within its words.** -/
theorem ac_completeAtB (κ : ℕ) (Lin : Main.Layout) {w : E} (hw : IsCanonical128 w) {Ba : ℕ}
    (ha : TotalLe coreProgram fs "assert_canonical" fun _ ↦ Ba) :
    CompleteAtB fs cert κ "assert_canonical" Lin [w] (Returns [0]) Ba :=
  completeAt_of_rel_pureB (B := fun _ ↦ Ba) ac_pure (List.mem_singleton_self _)
    (fun rd _ ↦ (assert_canonical_holds rd [w] [0]).2
      (show IsCanonical128 w ∧ [(0 : E)] = [0] from ⟨hw, rfl⟩)) κ ha

/-- Callees by position, each within its bound. -/
theorem kidsDepB_of {κ : ℕ} : ∀ (ks : List KidD) (Bs : List ℕ), ks.length = Bs.length →
    (∀ j < ks.length, ∀ pv, ((ks.getD j noKid pv).taken = true →
        CompleteAtB fs cert κ (ks.getD j noKid pv).f (ks.getD j noKid pv).Lin
          (ks.getD j noKid pv).args (ks.getD j noKid pv).Out (Bs.getD j 0)) ∧
      ((ks.getD j noKid pv).taken = false → fs (ks.getD j noKid pv).f ≤ Bs.getD j 0)) →
    KidsDepB fs cert κ ks Bs
  | [], [], _, _ => trivial
  | [], _ :: _, h, _ => by simp at h
  | _ :: _, [], h, _ => by simp at h
  | _ :: ks, _ :: Bs, hl, h =>
    ⟨h 0 (by simp), kidsDepB_of ks Bs (by simpa using hl) fun j hj ↦ h (j + 1) (by simp; omega)⟩

/-- Callees within their bounds are within larger ones. -/
theorem KidsDepB.mono {κ : ℕ} {Bs Bs' : List ℕ} (hle : List.Forall₂ (· ≤ ·) Bs Bs') :
    ∀ {ks : List KidD}, KidsDepB fs cert κ ks Bs → KidsDepB fs cert κ ks Bs' := by
  induction hle with
  | nil => intro ks h; exact h
  | @cons b b' Bs Bs' hb _ ih =>
    intro ks h
    cases ks with
    | nil => exact h.elim
    | cons k ks =>
      exact ⟨fun pv ↦ ⟨fun ht ↦ ((h.1 pv).1 ht).mono le_rfl hb, fun ht ↦ ((h.1 pv).2 ht).trans hb⟩,
        ih h.2⟩

namespace ChildSegs

variable {bytecode : List K} {seed : Digest} {c : Child} (S : ChildSegs bytecode seed c)

/-- The largest height. -/
theorem n_le (hbl : bytecode.length = 2 ^ 23) : S.H.n ≤ 28 := by
  show (Tables.tableHeightsOf S.rowsN).foldl max 0 ≤ 28
  rcases Tables.VtHonest.vsFoldl_max_mem (Tables.tableHeightsOf S.rowsN) 0 with h | h
  · omega
  · have := S.hh29 hbl _ h
    omega

/-- `verify_tables`' own buffers. -/
theorem vt_sizes_sum : S.H.sizes.sum = 3841 + S.H.μ + 9 * (S.H.n + 1) := by
  simp only [Tables.VtHonest.sizes, List.sum_append, List.sum_cons, List.sum_nil,
    List.sum_replicate, smul_eq_mul]
  omega

/-- The stack's total is at most `2^28`. -/
theorem stackTotal_le (hbl : bytecode.length = 2 ^ 23) : Tables.stackTotal S.kappas ≤ 2 ^ 28 := by
  have h28 := S.stack28
  rw [stackLog_eq hbl] at h28
  exact log2Ceil_le_iff.mp (by
    show log2Ceil (Tables.stackTotal (columnKappas S.logMem 19 (Tables.tableHeightsOf S.rowsN)))
      ≤ 28
    omega)

end ChildSegs

/-- **`verify_sub`'s callees on an honest child, each within its bound**, `open_stacked` within its
candidate's. -/
theorem vs_kidsDepBAt {bytecode : List K} (hbl : bytecode.length = 2 ^ 23) {seed : Digest}
    {c : Child} (S : ChildSegs bytecode seed c) {κ : ℕ} (hκ : 16 ≤ κ) (hrf : Lift.RunsFit fs cert)
    (hcons : RunsConsec cert) (W : VsWords fs) {Bvk : ℕ} (hvk : VkCompleteAtB fs cert κ Bvk)
    (bs : List ℕ) (sqE : ℕ) :
    KidsDepB fs cert κ (S.kids bs sqE) (vsBsAt W Bvk S.μs S.rate) := by
  refine kidsDepB_of _ _ (by rw [ChildSegs.kids_length]; simp [vsBsAt]) fun j hj pv ↦ ?_
  have hj13 : j < 13 := by simpa [ChildSegs.kids_length] using hj
  have hμ := S.μ_bounds hbl
  have hτ := S.τ_bounds hbl
  interval_cases j
  · exact ⟨fun _ ↦ gpw_completeAtB κ [] (by have := S.hr4; omega) W.hg, fun h ↦ by cases h⟩
  · exact ⟨fun _ ↦ gpw_completeAtB κ [] (by have := S.h32; omega) W.hg, fun h ↦ by cases h⟩
  · refine ⟨fun _ ↦ log2_L0_completeAtB κ (by omega) _ sqE (S.pushTotal_lt hbl) ?_,
      fun h ↦ by cases h⟩
    show max 0 S.μ < 34; omega
  · exact ⟨fun _ ↦ ac_completeAtB κ [] (x_canonical S.hroot).1 W.ha, fun h ↦ by cases h⟩
  · exact ⟨fun _ ↦ ac_completeAtB κ [] (x_canonical S.hroot).2 W.ha, fun h ↦ by cases h⟩
  · obtain ⟨hrun, -, -, -⟩ := S.runG' hbl
    have hB : Tables.vbgBound fs W.K29 W.R W.K8 S.μ ≤ vbgMax fs W.K29 W.R W.K8 := by
      unfold vbgMax
      exact le_lmax (List.mem_map.2 ⟨S.μ, List.mem_range.2 (by omega), rfl⟩)
    exact ⟨fun _ ↦ (Tables.verify_bus_gkr_completeAtTB (by omega) (by omega) (by omega) hrun
      S.capS_carries (vcG bs) (vb bs 5) W.h29 W.hR W.h8).toCompleteAtB.mono le_rfl hB,
      fun h ↦ by cases h⟩
  · obtain ⟨hok, -, -, -⟩ := S.H_run hbl
    have hHμ : S.H.μ < 30 := by
      show S.point.length < 30
      rw [(S.runG' hbl).2.2.1]; omega
    have hn : S.H.n < 29 := by have := S.n_le hbl; omega
    have hB : fs "verify_tables" + S.H.sizes.sum + ((Tables.vtBs W.Kf W.Ksh (Tables.vtRunB fs W.K10 S.H.n)).sum +
        Tables.ifFrames fs Tables.vtPre) ≤ vtMax fs W.Kf W.Ksh W.K10 := by
      rw [S.vt_sizes_sum]
      unfold vtMax
      exact le_lmax2 (vtBnd fs W.Kf W.Ksh W.K10) hHμ hn
    exact ⟨fun _ ↦ (Tables.verify_tables_completeAtTB (by omega) hok (S.H_shape hbl) (S.vtB bs sqE)
      W.Kf W.Ksh W.K10 W.hKf W.hsh W.h10).toCompleteAtB.mono le_rfl hB, fun h ↦ by cases h⟩
  · obtain ⟨hrun, -, -, -, hc6⟩ := S.runK' hbl
    have hf : S.s6.cap = capOf S.H.s3.perm := S.s6_capOf hbl
    exact ⟨fun _ ↦ hvk S.τ S.s6.cap S.chis S.outs S.xsK S.op S.kpt S.slices S.s7.cap S.word S.m0
      (S.cK bs) (vb bs 8) (S.cL bs) (vb bs 9) (vb bs 10) hτ.1 (by omega)
      (by rw [S.chis_length]; exact hτ.2.2) (S.lanes hbl).2.2 (by rw [hf]; rfl)
      (by rw [hf]; exact Tables.tb_capOf_canonical _) hc6 hrun, fun h ↦ by cases h⟩
  · exact ⟨fun _ ↦ rst_completeAtB κ (S.runK' hbl).2.2.2.1 S.rchs_length W.hl14,
      fun h ↦ by cases h⟩
  · exact ⟨fun _ ↦ (Tables.certify_placement_completeAtB fs cert (by omega) S.hs_length S.h32
      (S.hh29 hbl) (by have := vsH_tau22 hbl S.hrowsL S.stack28; unfold ChildSegs.hs; omega) _
      _).toCompleteAtB, fun h ↦ by cases h⟩
  · have : log2Ceil (Tables.stackTotal S.kappas) ≤ 28 := log2Ceil_le_iff.mpr (S.stackTotal_le hbl)
    exact ⟨fun _ ↦ log2_L15_completeAtB κ (by omega) _ sqE (by have := S.stackTotal_le hbl; omega)
      (by omega), fun h ↦ by cases h⟩
  · exact ⟨fun _ ↦ open_stacked_completeAtB S.μs S.rate S.hmu22 S.hmu28 S.hr1 S.hr4 fs cert κ
      W.Bnd W.Kr hrf hcons (by omega) (fun _ _ ↦ trivial) W.hleaf
      (W.hloop _ _ S.hmu22 S.hmu28 S.hr1 S.hr4) S.s8.perm S.root S.target _ S.xsW c.proof.openings
      S.w S.s' S.roots' S.runW S.nzW S.capsW [(S.cW bs, S.xsW)]
      (fun _ _ hm ↦ hm _ List.mem_cons_self), fun h ↦ by cases h⟩
  · refine ⟨fun ht ↦ term_completeB hbl S hκ _ sqE S.w_point_length pv ht W.hEqc W.hL15 W.hCsF
      W.hrs, fun _ ↦ ?_⟩
    show fs "check_opening_terminal" ≤ termBound fs W.Beqc W.K15 W.Bcs W.Brs
    unfold termBound
    omega

/-- **`verify_sub`'s callees on an honest child, each within its bound.** -/
theorem vs_kidsDepB {bytecode : List K} (hbl : bytecode.length = 2 ^ 23) {seed : Digest}
    {c : Child} (S : ChildSegs bytecode seed c) {κ : ℕ} (hκ : 16 ≤ κ) (hrf : Lift.RunsFit fs cert)
    (hcons : RunsConsec cert) (W : VsWords fs) {Bvk : ℕ} (hvk : VkCompleteAtB fs cert κ Bvk)
    (bs : List ℕ) (sqE : ℕ) :
    KidsDepB fs cert κ (S.kids bs sqE) (vsBs W Bvk) := by
  have hB : osBosAt fs W.Bnd W.Kr S.μs S.rate ≤ osMax fs W.Bnd W.Kr := by
    unfold osMax
    exact le_lmax2 (osBosAt fs W.Bnd W.Kr) (by have : S.μs ≤ 28 := S.hmu28; omega)
      (by have := S.hr4; omega)
  refine KidsDepB.mono ?_ (vs_kidsDepBAt hbl S hκ hrf hcons W hvk bs sqE)
  exact .cons le_rfl (.cons le_rfl (.cons le_rfl (.cons le_rfl (.cons le_rfl (.cons le_rfl
    (.cons le_rfl (.cons le_rfl (.cons le_rfl (.cons le_rfl (.cons le_rfl (.cons hB
      (.cons le_rfl .nil))))))))))))

end
end LeanVM.Guest.B1.VerifySub
