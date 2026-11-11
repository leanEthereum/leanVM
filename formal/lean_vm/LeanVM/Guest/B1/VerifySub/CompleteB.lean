/-
  LeanVM.Guest.B1.VerifySub.CompleteB

  `verify_sub` is complete on every honest child within `vsBound` words: its frame, its own
  buffers and its thirteen callees' bounds, the callees' words facts (`VsWords`) and
  `verify_keccak`'s bounded completeness (`VkCompleteAtB`) assumed.
-/

module

public import LeanVM.Guest.B1.VerifySub.Complete
public import LeanVM.Guest.B1.VerifySub.H.TermCB
public import LeanVM.Guest.B1.Terminal.KidsDepB
public import LeanVM.Guest.B1.Ring.CompleteB
public import LeanVM.Guest.B1.Gkr.VbgB
public import LeanVM.Guest.B1.Tables.VtC.ABound
public import LeanVM.Guest.B1.Place.OsBos
public import LeanVM.Guest.B1.Place.OsPlaced
public import LeanVM.Guest.Budget.Bounded
public import LeanVM.Guest.B1.Tables.VtC.AWeight
public import LeanVM.Guest.B1.VerifySub.H.TermCBW
public import LeanVM.Guest.B1.VerifySub.H.VtShape
public import LeanVM.Guest.B1.VerifySub.H.WhirLen

/-!
# `verify_sub` within a bound

`VsWords fs`: the words facts of `verify_sub`'s callees' pure callees, at the frame sizes `fs`
(`TotalLe`, `TotalLeOn`), with their constants. `vsBs W Bvk`: the thirteen callees' bounds, in
call order — the maxima over the honest children's depths (`vbgMax`, `vtMax`, `osMax`) where a
callee's bound depends on them. `vsBound W Bvk = fs "verify_sub" + 8678 + (vsBs W Bvk).sum`: the
frame, the own buffers (at most `8644 + 32` words) and the callees.

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

/-- The largest of a list. -/
def lmax (l : List ℕ) : ℕ := l.foldl max 0

theorem le_lmax {l : List ℕ} {x : ℕ} (h : x ∈ l) : x ≤ lmax l := (Tables.foldl_max_ge l 0).2 x h

theorem le_lmax2 (f : ℕ → ℕ → ℕ) {A B a b : ℕ} (ha : a < A) (hb : b < B) :
    f a b ≤ lmax ((List.range A).flatMap fun a ↦ (List.range B).map (f a)) :=
  le_lmax (List.mem_flatMap.2 ⟨a, List.mem_range.2 ha, List.mem_map.2 ⟨b, List.mem_range.2 hb, rfl⟩⟩)

/-- `verify_bus_gkr`'s bound over the depths below `33`. -/
@[irreducible] def vbgMax (fs : String → ℕ) (K29 R K8 : ℕ) : ℕ :=
  lmax ((List.range 33).map (Tables.vbgBound fs K29 R K8))

/-- `verify_tables`' bound at the bus depth `m` and the largest height `n`. -/
noncomputable def vtBnd (fs : String → ℕ) (Kf : String → ℕ) (Ksh K10 m n : ℕ) : ℕ :=
  fs "verify_tables" + (3841 + m + 9 * (n + 1)) +
    ((Tables.vtBs Kf Ksh (Tables.vtRunB fs K10 n)).sum + Tables.ifFrames fs Tables.vtPre)

/-- `verify_tables`' bound over the depths below `33` and the heights below `33`. -/
@[irreducible] noncomputable def vtMax (fs : String → ℕ) (Kf : String → ℕ) (Ksh K10 : ℕ) : ℕ :=
  lmax ((List.range 33).flatMap fun m ↦ (List.range 33).map (vtBnd fs Kf Ksh K10 m))

/-- `open_stacked`'s bound over the stack logs below `33`. -/
@[irreducible] noncomputable def osMax (fs Bnd : String → ℕ) : ℕ :=
  lmax ((List.range 33).map (osBosAt fs Bnd))

/-- **`verify_sub`'s callees' words facts**, at the frame sizes `fs`: `g_power_of_word`'s and
`assert_canonical`'s (`Bg`, `Ba`), `verify_bus_gkr`'s loops and rounds (`K29`, `R`, `K8`),
`verify_tables`' callees (`Kf`, `Ksh`, `K10`), `ring_switch_target`'s loop (`B14`),
`open_stacked`'s callees (`Bnd`), the terminal's pure callees (`Beqc`,
`K15`, `Bcs`, `Brs`) — a loop's words per iteration, its run's one phantom frame charged once by the
`TotalLeOn … LoopPre` fact; and, at the weights `ωv op` (an opcode's instructions per frame), the weights
of `verify_tables`' callees (`Kvw`, `Wss`, `Kw10`) and of the terminal's (`Weqc`, `W15`, `Wst`,
`Wcs`, `Wrsw`), which bound those two callees' trees (`vtWB`, `termWB`). -/
structure VsWords (fs : String → ℕ) : Type where
  Bg : ℕ
  hg : TotalLe coreProgram fs "g_power_of_word" fun _ ↦ Bg
  Ba : ℕ
  ha : TotalLe coreProgram fs "assert_canonical" fun _ ↦ Ba
  K29 : ℕ
  R : ℕ
  K8 : ℕ
  h29 : TotalLeOn coreProgram fs "__loop36" LoopPre
    (fun a ↦ logG (a.getD 1 0) * K29 + fs "__loop36")
  hR : ∀ n ∈ Tables.grCounts, TotalLe coreProgram fs (Tables.lName "gkr_rounds" n) (fun _ ↦ R)
  h8 : TotalLeOn coreProgram fs "__loop7" LoopPre (fun a ↦ logG (a.getD 1 0) * K8 + fs "__loop7")
  Kf : String → ℕ
  Ksh : ℕ
  K10 : ℕ
  hKf : ∀ g ∈ Tables.vtKidS, g ≠ "__loop9" → g ≠ "__loop8" → g ≠ "shared_selector_tables" →
    TotalLe coreProgram fs g (fun _ ↦ Kf g)
  hsh : TotalLeOn coreProgram fs "shared_selector_tables"
    (fun a ↦ ∃ n < 64, a.getD 5 0 = gen ^ n) (fun _ ↦ Ksh)
  h10 : TotalLeOn coreProgram fs "__loop9" LoopPre (fun a ↦ logG (a.getD 1 0) * K10 + fs "__loop9")
  B14 : ℕ
  hl14 : TotalLeOn coreProgram fs "__loop13" (fun a ↦ a.getD 0 0 = 1) fun _ ↦ B14
  Bnd : String → ℕ
  hleaf : OsLeafBounds fs Bnd
  Beqc : ℕ
  K15 : ℕ
  Bcs : ℕ
  Brs : ℕ
  hEqc : TotalLe coreProgram fs "eq_prefix_chain" fun _ ↦ Beqc
  hL15 : TotalLeOn coreProgram fs "__loop14" LoopPre
    fun a ↦ logG (a.getD 1 0) * K15 + fs "__loop14"
  hCsF : ∀ κ' < 33, fs (Tables.lName "column_selector" κ') ≤ Bcs
  hrs : ∀ c ≤ 34, TotalLeOn coreProgram fs "rs_eq_run" (fun a ↦ a.getD 3 0 = gen ^ c)
    fun _ ↦ Brs
  ωv : Opcode → String → ℕ
  Kvw : Opcode → String → ℕ
  Wss : Opcode → ℕ
  Kw10 : Opcode → ℕ
  hKvw : ∀ op, ∀ g ∈ Tables.vtKidS, g ≠ "__loop9" → g ≠ "__loop8" → g ≠ "shared_selector_tables" →
    WeightLe coreProgram (ωv op) g (fun _ ↦ Kvw op g)
  hssw : ∀ op (rd : Reader) (t : Tree) (args rets : List E), t.name = "shared_selector_tables" →
    (∃ n < 64, args.getD 5 0 = gen ^ n) → t.Valid coreProgram rd args rets →
    t.BufsOk coreProgram → t.weight (ωv op) ≤ Wss op
  h10w : ∀ op, Budget.LoopW (ωv op) "__loop9" (Kw10 op)
  Weqc : Opcode → ℕ
  W15 : Opcode → ℕ
  Wst : Opcode → ℕ
  Wcs : Opcode → ℕ
  Wrsw : Opcode → ℕ
  hEqcW : ∀ op, WeightLe coreProgram (ωv op) "eq_prefix_chain" fun _ ↦ Weqc op
  hStW : ∀ op, WeightLe coreProgram (ωv op) "selector_tables" fun _ ↦ Wst op
  hCsW : ∀ op, ∀ κ' < 33, WeightLe coreProgram (ωv op) (Tables.lName "column_selector" κ')
    fun _ ↦ Wcs op
  h15W : ∀ op (rd : Reader) (t : Tree) (args rets : List E), t.name = "__loop14" →
    t.Valid coreProgram rd args rets → t.BufsOk coreProgram →
    t.total fs ≤ (32 * K15 + fs "__loop14") → t.weight (ωv op) ≤ W15 op
  hrswW : ∀ op (rd : Reader) (t : Tree) (args rets : List E), t.name = "ring_switch_weight" →
    t.Valid coreProgram rd args rets → t.BufsOk coreProgram →
    t.total fs ≤ fs "ring_switch_weight" + 2240 + Brs → t.weight (ωv op) ≤ Wrsw op

/-- **`verify_tables`' weight bound** at `W.ωv op`: its frame's and its calls' (`vtBs`). -/
noncomputable def vtWB {fs : String → ℕ} (W : VsWords fs) (op : Opcode) : ℕ :=
  W.ωv op "verify_tables" + (Tables.vtBs (W.Kvw op) (W.Wss op) (32 * W.Kw10 op)).sum

/-- **The terminal's weight bound** at `W.ωv op`: its frame's and its calls' (`termWs`). -/
noncomputable def termWB {fs : String → ℕ} (W : VsWords fs) (op : Opcode) : ℕ :=
  W.ωv op "check_opening_terminal" + (termWs W.Weqc W.W15 W.Wst W.Wcs W.Wrsw op).sum

/-- **The callees' bounds**, in call order (`vs_calls`). -/
noncomputable def vsBs {fs : String → ℕ} (W : VsWords fs) (Bvk : ℕ) : List ℕ :=
  [W.Bg, W.Bg, fs "log2_ceil_in_the_exponent__L0_L34" + 34 + 2 * fs "assert_small_g_power",
    W.Ba, W.Ba, vbgMax fs W.K29 W.R W.K8, vtMax fs W.Kf W.Ksh W.K10, Bvk,
    fs "ring_switch_target" + 18 + W.B14, fs "certify_placement" + Tables.cpSizes.sum,
    fs "log2_ceil_in_the_exponent__L16_L34" + 34 + 2 * fs "assert_small_g_power",
    osMax fs W.Bnd, termBound fs W.Beqc W.K15 W.Bcs W.Brs]

/-- **The callees' bounds at one stack log and rate**: `vsBs` with `open_stacked`'s bound at the stack log
`μ` (every rate of it within the same arm's bound). -/
noncomputable def vsBsAt {fs : String → ℕ} (W : VsWords fs) (Bvk μ _r : ℕ) : List ℕ :=
  [W.Bg, W.Bg, fs "log2_ceil_in_the_exponent__L0_L34" + 34 + 2 * fs "assert_small_g_power",
    W.Ba, W.Ba, vbgMax fs W.K29 W.R W.K8, vtMax fs W.Kf W.Ksh W.K10, Bvk,
    fs "ring_switch_target" + 18 + W.B14, fs "certify_placement" + Tables.cpSizes.sum,
    fs "log2_ceil_in_the_exponent__L16_L34" + 34 + 2 * fs "assert_small_g_power",
    osBosAt fs W.Bnd μ, termBound fs W.Beqc W.K15 W.Bcs W.Brs]

/-- **`verify_sub`'s bound**: its frame, its own buffers (`8644 + μ`, `μ ≤ 32`), its callees. -/
noncomputable def vsBound {fs : String → ℕ} (W : VsWords fs) (Bvk : ℕ) : ℕ :=
  fs "verify_sub" + 8678 + (vsBs W Bvk).sum

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
theorem n_le (hbl : bytecode.length = 2 ^ 23) : S.H.n ≤ 32 := by
  show (Tables.tableHeightsOf S.rowsN).foldl max 0 ≤ 32
  rcases Tables.VtHonest.vsFoldl_max_mem (Tables.tableHeightsOf S.rowsN) 0 with h | h
  · omega
  · have := S.hh33 hbl _ h
    omega

/-- `verify_tables`' own buffers. -/
theorem vt_sizes_sum : S.H.sizes.sum = 3841 + S.H.μ + 9 * (S.H.n + 1) := by
  simp only [Tables.VtHonest.sizes, List.sum_append, List.sum_cons, List.sum_nil,
    List.sum_replicate, smul_eq_mul]
  omega

/-- The stack's total is at most `2^32`. -/
theorem stackTotal_le (hbl : bytecode.length = 2 ^ 23) : Tables.stackTotal S.kappas ≤ 2 ^ 32 := by
  have h28 := S.stack32
  rw [stackLog_eq hbl] at h28
  exact log2Ceil_le_iff.mp (by
    show log2Ceil (Tables.stackTotal (columnKappas S.logMem 19 (Tables.tableHeightsOf S.rowsN)))
      ≤ 32
    omega)

end ChildSegs

/-- **`verify_sub`'s callees on an honest child, each within its bound**, `open_stacked` within its
stack log and rate's. -/
theorem vs_kidsDepBAt {bytecode : List K} (hbl : bytecode.length = 2 ^ 23) {seed : Digest}
    {c : Child} (S : ChildSegs bytecode seed c) {κ : ℕ} (hκ : 14 ≤ κ) (hrf : Lift.RunsFit fs cert)
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
    have hHμ : S.H.μ < 33 := by
      show S.point.length < 33
      rw [(S.runG' hbl).2.2.1]; omega
    have hn : S.H.n < 33 := by have := S.n_le hbl; omega
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
      (S.hh33 hbl) (by have := vsH_tau26 hbl S.hrowsL S.stack32; unfold ChildSegs.hs; omega) _
      _).toCompleteAtB, fun h ↦ by cases h⟩
  · have : log2Ceil (Tables.stackTotal S.kappas) ≤ 32 := log2Ceil_le_iff.mpr (S.stackTotal_le hbl)
    exact ⟨fun _ ↦ log2_L16_completeAtB κ (by omega) _ sqE (by have := S.stackTotal_le hbl; omega)
      (by omega), fun h ↦ by cases h⟩
  · exact ⟨fun _ ↦ open_stacked_completeAtB S.μs S.rate S.hmu20 S.hmu32 S.hr1 S.hr4 fs cert κ
      W.Bnd hrf hcons (by omega) W.hleaf S.s8.perm S.root S.target _ S.xsW c.proof.openings
      S.w S.s' S.roots' S.runW S.nzW S.capsW [(S.cW bs, S.xsW)]
      (fun _ _ hm ↦ hm _ List.mem_cons_self), fun h ↦ by cases h⟩
  · refine ⟨fun ht ↦ term_completeB hbl S hκ _ sqE S.w_point_length pv ht W.hEqc W.hL15 W.hCsF
      W.hrs, fun _ ↦ ?_⟩
    show fs "check_opening_terminal" ≤ termBound fs W.Beqc W.K15 W.Bcs W.Brs
    unfold termBound
    omega

/-- **`verify_sub`'s callees on an honest child, each within its bound.** -/
theorem vs_kidsDepB {bytecode : List K} (hbl : bytecode.length = 2 ^ 23) {seed : Digest}
    {c : Child} (S : ChildSegs bytecode seed c) {κ : ℕ} (hκ : 14 ≤ κ) (hrf : Lift.RunsFit fs cert)
    (hcons : RunsConsec cert) (W : VsWords fs) {Bvk : ℕ} (hvk : VkCompleteAtB fs cert κ Bvk)
    (bs : List ℕ) (sqE : ℕ) :
    KidsDepB fs cert κ (S.kids bs sqE) (vsBs W Bvk) := by
  have hB : osBosAt fs W.Bnd S.μs ≤ osMax fs W.Bnd := by
    unfold osMax
    exact le_lmax (List.mem_map.2 ⟨S.μs, List.mem_range.2 (by have : S.μs ≤ 32 := S.hmu32; omega),
      rfl⟩)
  refine KidsDepB.mono ?_ (vs_kidsDepBAt hbl S hκ hrf hcons W hvk bs sqE)
  exact .cons le_rfl (.cons le_rfl (.cons le_rfl (.cons le_rfl (.cons le_rfl (.cons le_rfl
    (.cons le_rfl (.cons le_rfl (.cons le_rfl (.cons le_rfl (.cons le_rfl (.cons hB
      (.cons le_rfl .nil))))))))))))

end
end LeanVM.Guest.B1.VerifySub
