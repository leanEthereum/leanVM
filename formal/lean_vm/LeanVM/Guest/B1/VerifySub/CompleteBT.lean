/-
  LeanVM.Guest.B1.VerifySub.CompleteBT

  `verify_sub` complete within its child's bound by a node whose callees are calls of their names
  within their bounds (`Budget.FlatShape`), `open_stacked` at the child's announced shape.
-/

module

public import LeanVM.Guest.B1.VerifySub.CMatch
public import LeanVM.Guest.B1.VerifySub.CompleteB
public import LeanVM.Guest.B1.Place.OsFinal
public import LeanVM.Guest.ChildShape
public import LeanVM.Guest.AcceptableChild

/-!
# `verify_sub` by its callees' trees

The callees' names, bounds and predicates are `VerifySub/BoundsB`'s (`vsNames`, `vsBsAt`, `vsPs`,
`vsTs`, `vsTsAny`, `vsBoundAt`). `vs_names`: the honest child's callees are calls of
`vsNames μ r (d - 20)`, the bus depth `d`.

`vsPsR`: `verify_sub`'s callees' predicates of the memory, `certify_placement`'s `Pcp`, `verify_tables`' `Pvt` beside its weights, `open_stacked`'s `Pos`. `vs_kidsDepBPR`: the callees within their bounds by trees of them, given `certify_placement`'s, `verify_tables`' and `open_stacked`'s. `verify_sub_completeBTG`: on an honest child, `verify_sub` is complete within the bound at its stack log and rate by a node of `vsTsAny` (`completeAt_flatDepRBPR` with `vs_obligations` and `vs_kidsDepBPR`), its valuation the honest one, its own buffers held (`vsQn`), its valid callees satisfying their predicates by name (`VsKidQ`, `kidsT_valid_mem`).

`verify_sub_completeBT`: on an honest child (`child_segments`), `verify_sub` is complete within
the bound at its announced stack log and rate (`childShape`), by a node of `vsTsAny`
(`verify_sub_completeBTG`, every predicate `True`), given `verify_keccak`'s bounded
completeness (`open_stacked`'s is `open_stacked_completeAtB`).
`verify_sub_completeBT_fs`: at `B2C.fs`, `verify_keccak` within `vkBound`.
-/

namespace LeanVM.Guest.B1.VerifySub

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Node LeanVM.Guest.Memory

@[expose] public section

theorem vs_names {bytecode : List K} {seed : Digest} {c : Child} (S : ChildSegs bytecode seed c)
    (bs : List ℕ) (sqE : ℕ) :
    List.Forall₂ (fun k n ↦ ∀ pv, (k pv).f = n) (S.kids bs sqE) (vsNames S.μs S.rate (S.d - 20)) :=
  .cons (fun _ ↦ rfl) (.cons (fun _ ↦ rfl) (.cons (fun _ ↦ rfl) (.cons (fun _ ↦ rfl)
    (.cons (fun _ ↦ rfl) (.cons (fun _ ↦ rfl) (.cons (fun _ ↦ rfl) (.cons (fun _ ↦ rfl)
      (.cons (fun _ ↦ rfl) (.cons (fun _ ↦ rfl) (.cons (fun _ ↦ rfl) (.cons (fun _ ↦ rfl)
        (.cons (fun _ ↦ rfl) (.cons (fun _ ↦ rfl) (.cons (fun _ ↦ rfl) (.cons (fun _ ↦ rfl)
          .nil)))))))))))))))

/-! ## Callees by name -/

theorem kidsT_valid_mem {P : Core.Program} {rd : Reader} {σ : Val} :
    ∀ (cs : List Call) (Ts : List (Tree → Prop)) (ks : List Tree), Tree.KidsValid P rd σ cs ks →
      KidsT cs Ts ks → cs.length ≤ Ts.length → ∀ t ∈ ks, (∃ a r, t.Valid P rd a r) → ∃ T ∈ Ts, T t
  | [], _, [], _, _, _, t, ht, _ => absurd ht List.not_mem_nil
  | c :: cs, T :: Ts, k :: ks, ⟨_, hc, hk⟩, ⟨h1, h2⟩, hl, t, ht, ⟨a, r, hv⟩ => by
    rcases List.mem_cons.mp ht with rfl | ht
    · by_cases htk : c.taken = true
      · exact ⟨T, List.mem_cons_self, h1 htk⟩
      · have htk' : c.taken = false := by simpa using htk
        simp only [htk', Bool.false_eq_true, ↓reduceIte] at hc
        obtain ⟨⟨f, σ', rfl⟩, -⟩ := hc
        exact hv.elim
    · obtain ⟨T', hT', h⟩ := kidsT_valid_mem cs Ts ks hk h2 (by simpa using hl) t ht ⟨a, r, hv⟩
      exact ⟨T', List.mem_cons_of_mem _ hT', h⟩
  | _ :: _, [], _, _, _, hl, _, _, _ => by simp at hl
  | [], _, _ :: _, h, _, _, _, _, _ => h.elim
  | _ :: _, _ :: _, [], h, _, _, _, _, _ => h.elim

theorem namedP_imp {fs : String → ℕ} {Q : Tree → Prop} : ∀ (ns : List String) (Bs : List ℕ) (Ps : List (Tree → Prop)),
    List.Forall₂ (fun n P => ∀ t, t.name = n → P t → Q t) ns Ps → ∀ T ∈ namedP fs ns Bs Ps, ∀ t, T t → Q t
  | n :: ns, b :: Bs, P :: Ps, .cons h hs, T, hT, t, hTt => by
    rcases List.mem_cons.mp hT with rfl | hT
    · exact h t hTt.1.1 hTt.2
    · exact namedP_imp ns Bs Ps hs T hT t hTt
  | [], _, _, _, _, hT, _, _ => by simp [namedP] at hT
  | _ :: _, [], _, _, _, hT, _, _ => by simp [namedP] at hT
  | _ :: _, _ :: _, [], _, _, hT, _, _ => by simp [namedP] at hT

theorem kidsT_mono' : ∀ (cs : List Call) (Ts Ts' : List (Tree → Prop)) (ks : List Tree),
    List.Forall₂ (fun T T' => ∀ t, T t → T' t) Ts Ts' → KidsT cs Ts ks → KidsT cs Ts' ks
  | _ :: cs, _ :: Ts, _ :: Ts', k :: ks, .cons h hs, ⟨h1, h2⟩ =>
    ⟨fun ht => h k (h1 ht), kidsT_mono' cs Ts Ts' ks hs h2⟩
  | [], _, _, _, _, _ => trivial
  | _ :: _, [], [], _, _, _ => trivial
  | _ :: _, _ :: _, _ :: _, [], _, _ => trivial

theorem flatShape_mono {f : String} {Ts Ts' : List (Tree → Prop)} {t : Tree}
    (h : Budget.FlatShape coreProgram f Ts t) (hT : List.Forall₂ (fun T T' => ∀ t, T t → T' t) Ts Ts') :
    Budget.FlatShape coreProgram f Ts' t := by
  obtain ⟨σ, bufs, ks, rfl, hw⟩ := h
  exact ⟨σ, bufs, ks, rfl, fun fn es vs hf hw' => ⟨by rw [← hT.length_eq]; exact (hw fn es vs hf hw').1,
    kidsT_mono' _ _ _ _ hT (hw fn es vs hf hw').2⟩⟩

theorem namedP_mono {fs : String → ℕ} : ∀ (ns : List String) (Bs : List ℕ) (Ps Ps' : List (Tree → Prop)),
    List.Forall₂ (fun P P' => ∀ t, P t → P' t) Ps Ps' →
    List.Forall₂ (fun T T' => ∀ t, T t → T' t) (namedP fs ns Bs Ps) (namedP fs ns Bs Ps')
  | n :: ns, b :: Bs, P :: Ps, P' :: Ps', .cons h hs =>
    .cons (fun t ht => ⟨ht.1, h t ht.2⟩) (namedP_mono ns Bs Ps Ps' hs)
  | [], _, _, _, _ => by simp [namedP]
  | _ :: _, [], _, _, _ => by simp [namedP]
  | _ :: _, _ :: _, [], [], _ => by simp [namedP]

variable {fs : String → ℕ} {cert : String → V → ℕ}

/-! ## The predicates -/

/-- **`verify_sub`'s callees' predicates of the memory**: `certify_placement`'s `Pcp`, `verify_tables`' weights
and `Pvt`, `open_stacked`'s `Pos`, the terminal's weights. -/
noncomputable def vsPsR (W : VsWordsOs fs) (Pcp Pvt Pos : Reader → Tree → Prop) : List (Reader → Tree → Prop) :=
  List.replicate 3 (fun _ _ ↦ True) ++ [Pcp] ++ List.replicate 6 (fun _ _ ↦ True) ++
    [fun rd t ↦ (∀ op, Budget.WeighsLe coreProgram (W.ωv op) (vtWB W.toVsWords op) t) ∧ Pvt rd t] ++
    List.replicate 3 (fun _ _ ↦ True) ++ [Pos] ++
    [fun _ t ↦ ∀ op, Budget.WeighsLe coreProgram (W.ωv op) (termWB W.toVsWords op) t]

theorem vsPsR_imp (W : VsWordsOs fs) (Pcp Pvt Pos : Reader → Tree → Prop) (rd : Reader) :
    List.Forall₂ (fun P P' => ∀ t, P t → P' t) ((vsPsR W Pcp Pvt Pos).map (· rd)) (vsPs W) := by
  simp only [vsPsR, vsPs, List.replicate_succ, List.replicate_zero, List.cons_append, List.nil_append,
    List.map_cons, List.map_nil, List.forall₂_cons, List.Forall₂.nil, and_true]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    first | exact fun _ _ => trivial | exact fun _ h => h.1 | exact fun _ h => h

/-- The certification's, the tables' and the opening's entries, by name. -/
def VsKidQ (Pcp Pvt Pos : Reader → Tree → Prop) (rd : Reader) (t : Tree) : Prop :=
  (t.name = "certify_placement" → Pcp rd t) ∧ (t.name = "verify_tables" → Pvt rd t) ∧
    (t.name ∈ vsOpenNames → Pos rd t)

theorem vsKidQ_of {Pcp Pvt Pos : Reader → Tree → Prop} {rd : Reader} {t : Tree} {n : String} (hn : t.name = n)
    (hb : n ∉ "certify_placement" :: "verify_tables" :: vsOpenNames) : VsKidQ Pcp Pvt Pos rd t := by
  refine ⟨fun h => ?_, fun h => ?_, fun h => ?_⟩
  · exact absurd (by rw [← hn, h]; exact List.mem_cons_self) hb
  · exact absurd (by rw [← hn, h]; exact List.mem_cons_of_mem _ List.mem_cons_self) hb
  · exact absurd (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (hn ▸ h))) hb

theorem getD_not_mem {l bad : List String} (h : ∀ s ∈ l, s ∉ bad) (h0 : "" ∉ bad) (i : ℕ) : l.getD i "" ∉ bad := by
  rw [List.getD_eq_getElem?_getD]
  rcases hi : l[i]? with _ | s
  · exact h0
  · exact h s (List.mem_of_getElem? hi)

theorem squeeze_not_mem (i : ℕ) : squeezeNames.getD i "" ∉ "certify_placement" :: "verify_tables" :: vsOpenNames :=
  getD_not_mem (by decide) (by decide) i

theorem busGrind_not_mem (i : ℕ) : busGrindNames.getD i "" ∉ "certify_placement" :: "verify_tables" :: vsOpenNames :=
  getD_not_mem (by decide) (by decide) i

theorem openName_ne (μ : ℕ) : Whir.openName μ ∉ ["certify_placement", "verify_tables"] :=
  getD_not_mem (by decide) (by decide) _

/-- **`verify_sub`'s callees' trees satisfy their entries by name.** -/
theorem vsNames_kidQ (W : VsWordsOs fs) (Bvk μ r d : ℕ) (Pcp Pvt Pos : Reader → Tree → Prop) (rd : Reader) :
    ∀ T ∈ namedP fs (vsNames μ r d) (vsBsAt W Bvk μ r) ((vsPsR W Pcp Pvt Pos).map (· rd)), ∀ t, T t →
      VsKidQ Pcp Pvt Pos rd t := by
  refine namedP_imp _ _ _ ?_
  simp only [vsNames, vsPsR, List.replicate_succ, List.replicate_zero, List.cons_append, List.nil_append,
    List.map_cons, List.map_nil, List.forall₂_cons, List.Forall₂.nil, and_true]
  refine ⟨fun t hn _ => vsKidQ_of hn (by decide), fun t hn _ => vsKidQ_of hn (by decide),
    fun t hn _ => vsKidQ_of hn (by decide), fun t hn hp => ⟨fun _ => hp, fun h => absurd (hn.symm.trans h)
      (by decide), fun h => absurd (hn ▸ h) (by decide)⟩, fun t hn _ => vsKidQ_of hn (by decide),
    fun t hn _ => vsKidQ_of hn (by decide), fun t hn _ => vsKidQ_of hn (squeeze_not_mem _),
    fun t hn _ => vsKidQ_of hn (by decide), fun t hn _ => vsKidQ_of hn (busGrind_not_mem _),
    fun t hn _ => vsKidQ_of hn (by decide), fun t hn hp => ⟨fun h => absurd (hn.symm.trans h) (by decide),
      fun _ => hp.2, fun h => absurd (hn ▸ h) (by decide)⟩, fun t hn _ => vsKidQ_of hn (by decide),
    fun t hn _ => vsKidQ_of hn (by decide), fun t hn _ => vsKidQ_of hn (by decide), fun t hn hp => ⟨fun h =>
      absurd (by rw [← hn, h]; exact List.mem_cons_self) (openName_ne μ), fun h =>
      absurd (by rw [← hn, h]; exact List.mem_cons_of_mem _ List.mem_cons_self) (openName_ne μ), fun _ => hp⟩,
    fun t hn _ => vsKidQ_of hn (by decide)⟩

/-! ## The callees -/

theorem kidsDepBP_getD {κ : ℕ} : ∀ {ks : List KidD} {Bs : List ℕ} {Ps : List (Tree → Prop)},
    KidsDepBP fs cert κ ks Bs Ps → ∀ (j : ℕ), j < ks.length → ∀ (pv : List (List E × Main.Layout)),
      ((ks.getD j noKid pv).taken = true →
        CompleteAtDTB fs cert κ (ks.getD j noKid pv).f (ks.getD j noKid pv).Lin
          (ks.getD j noKid pv).args (ks.getD j noKid pv).Out (Ps.getD j fun _ ↦ True) (Bs.getD j 0)) ∧
      ((ks.getD j noKid pv).taken = false → fs (ks.getD j noKid pv).f ≤ Bs.getD j 0)
  | [], _, _, _, _, hj, _ => absurd hj (by simp)
  | _ :: _, [], _, h, _, _, _ => h.elim
  | _ :: _, _ :: _, [], h, _, _, _ => h.elim
  | _ :: _, _ :: _, _ :: _, h, 0, _, pv => h.1 pv
  | _ :: _, _ :: _, _ :: _, h, j + 1, hj, pv => kidsDepBP_getD h.2 j (by simpa using hj) pv

theorem kidsDepBPR_of {κ : ℕ} : ∀ (ks : List KidD) (Bs : List ℕ) (Ps : List (Reader → Tree → Prop)),
    ks.length = Bs.length → ks.length = Ps.length →
    (∀ j < ks.length, ∀ pv, ((ks.getD j noKid pv).taken = true →
        CompleteAtDTBR fs cert κ (ks.getD j noKid pv).f (ks.getD j noKid pv).Lin
          (ks.getD j noKid pv).args (ks.getD j noKid pv).Out (Ps.getD j fun _ _ ↦ True) (Bs.getD j 0)) ∧
      ((ks.getD j noKid pv).taken = false → fs (ks.getD j noKid pv).f ≤ Bs.getD j 0)) →
    KidsDepBPR fs cert κ ks Bs Ps
  | [], [], [], _, _, _ => trivial
  | [], _ :: _, _, h, _, _ => by simp at h
  | [], [], _ :: _, _, h, _ => by simp at h
  | _ :: _, [], _, h, _, _ => by simp at h
  | _ :: _, _ :: _, [], _, h, _ => by simp at h
  | _ :: ks, _ :: Bs, _ :: Ps, hl, hl', h =>
    ⟨h 0 (by simp), kidsDepBPR_of ks Bs Ps (by simpa using hl) (by simpa using hl')
      fun j hj ↦ h (j + 1) (by simp; omega)⟩

/-- **`verify_sub`'s callees on an honest child, each within its bound by a tree of its predicate of the
memory**, given `certify_placement`'s, `verify_tables`' and `open_stacked`'s. -/
theorem vs_kidsDepBPR {bytecode : List K} (hbl : bytecode.length = 2 ^ 23) {seed : Digest}
    {c : Child} (S : ChildSegs bytecode seed c) {κ : ℕ} (hκ : 16 ≤ κ) (hrf : Lift.RunsFit fs cert)
    (hcons : RunsConsec cert) (W : VsWordsOs fs) {Bvk : ℕ} (hvk : VkCompleteAtBK fs cert κ Bvk)
    (bs : List ℕ) (sqE : ℕ) {Pcp Pvt Pos : Reader → Tree → Prop}
    (hcp : CompleteAtDTBR fs cert κ "certify_placement" (Tables.cpLin S.logMem S.hs (vb bs 4) sqE)
      [ptr (vb bs 4), ptr sqE] (Tables.cpOut S.logMem S.hs) Pcp (fs "certify_placement" + Tables.cpSizes.sum))
    (hvt : ∀ B, CompleteAtDTBR fs cert κ "verify_tables" (S.H.linL B) (S.H.args B) (Returns (S.H.retsH B))
      (fun rd t ↦ (∀ op, Budget.WeighsLe coreProgram (W.ωv op) (vtWB W.toVsWords op) t) ∧ Pvt rd t)
      (vtMax fs W.Kf W.Ksh W.K10))
    (hos : ∀ pv, CompleteAtDTBR fs cert κ (Whir.openName S.μs) ((S.kids bs sqE).getD 14 noKid pv).Lin
      ((S.kids bs sqE).getD 14 noKid pv).args ((S.kids bs sqE).getD 14 noKid pv).Out Pos
      (osBosAt fs W.Bnd S.μs)) :
    KidsDepBPR fs cert κ (S.kids bs sqE) (vsBsAt W Bvk S.μs S.rate) (vsPsR W Pcp Pvt Pos) := by
  have hO := vs_kidsDepBP hbl S hκ hrf hcons W hvk open_stacked_completeAtB bs sqE
  refine kidsDepBPR_of _ _ _ (by rw [ChildSegs.kids_length]; rfl) (by rw [ChildSegs.kids_length]; rfl)
    fun j hj pv ↦ ?_
  have hj16 : j < 16 := by simpa [ChildSegs.kids_length] using hj
  have hB := kidsDepBP_getD hO j hj pv
  interval_cases j
  · exact hB
  · exact hB
  · exact hB
  · exact ⟨fun _ ↦ hcp, hB.2⟩
  · exact hB
  · exact hB
  · exact hB
  · exact hB
  · exact hB
  · exact hB
  · exact ⟨fun _ ↦ hvt _, hB.2⟩
  · exact hB
  · exact hB
  · exact hB
  · exact ⟨fun _ ↦ hos pv, hB.2⟩
  · exact hB

/-! ## `verify_sub` -/

/-- The honest valuation, its own buffers held. -/
def vsQn {bytecode : List K} {seed : Digest} {c : Child} (S : ChildSegs bytecode seed c) (sqE outE : ℕ)
    (rd : Reader) (σ : Val) : Prop :=
  ∃ b outs, σ = vsσ rd (vsW (bases b (vsSizes S.d)) outs) (vsArgs seed c sqE outE) ∧
    Main.MemL rd (bufL b (vsSizes S.d) S.ownW)

/-- **`verify_sub` is complete on an honest child within its own bound, generic in what its `certify_placement`,
`verify_tables` and `open_stacked` callees' trees satisfy**: by a node of `vsTsAny` whose valuation is the honest one,
its own buffers held (`vsQn`), whose valid callees satisfy theirs by name (`VsKidQ`). -/
theorem verify_sub_completeBTG {bytecode : List K} (hbl : bytecode.length = 2 ^ 23)
    (hrf : Lift.RunsFit fs cert) (hcons : RunsConsec cert) (W : VsWordsOs fs) {Bvk κ : ℕ}
    (hκ : 16 ≤ κ) (hvk : VkCompleteAtBK fs cert κ Bvk) {seed : Digest} {c : Child}
    (S : ChildSegs bytecode seed c) (sqE outE : ℕ) (Lin : Main.Layout)
    (hst : c.proof.stream.length ≤ Coverage.childStreamCap)
    (hexp : ∀ q ∈ vsExpLin sqE, q ∈ Lin) (hout : (outE, DeferredClaim.cells c.freshClaim) ∈ Lin)
    {Pcp Pvt Pos : Reader → Tree → Prop}
    (hcp : ∀ e1 e2, CompleteAtDTBR fs cert κ "certify_placement" (Tables.cpLin S.logMem S.hs e1 e2)
      [ptr e1, ptr e2] (Tables.cpOut S.logMem S.hs) Pcp (fs "certify_placement" + Tables.cpSizes.sum))
    (hvt : ∀ B, CompleteAtDTBR fs cert κ "verify_tables" (S.H.linL B) (S.H.args B) (Returns (S.H.retsH B))
      (fun rd t ↦ (∀ op, Budget.WeighsLe coreProgram (W.ωv op) (vtWB W.toVsWords op) t) ∧ Pvt rd t)
      (vtMax fs W.Kf W.Ksh W.K10))
    (hos : ∀ bs pv, CompleteAtDTBR fs cert κ (Whir.openName S.μs) ((S.kids bs sqE).getD 14 noKid pv).Lin
      ((S.kids bs sqE).getD 14 noKid pv).args ((S.kids bs sqE).getD 14 noKid pv).Out Pos
      (osBosAt fs W.Bnd S.μs)) :
    CompleteAtDTBR fs cert κ "verify_sub" Lin (vsArgs seed c sqE outE) (Returns [])
      (fun rd t ↦ vsTsAny fs W Bvk S.μs S.rate t ∧ ∃ σ bufs ks, t = .node "verify_sub" σ bufs ks ∧
        vsQn S sqE outE rd σ ∧ ∀ k ∈ ks, (∃ a r, k.Valid coreProgram rd a r) → VsKidQ Pcp Pvt Pos rd k)
      (vsBoundAt W Bvk S.μs S.rate) := by
  have hd := S.d_bounds hbl
  obtain ⟨hkr, hkm, hσ⟩ := vs_obligations hbl S fs (κ := κ) (by omega) hexp hout (vs_callsMatch hbl S hexp)
  have h := completeAt_flatDepRBPR (fs := fs) (cert := cert) find_vs vs_not_loop κ Lin _ []
    (vs_body.trans vsT_splitPre) vs_cflat vs_caddrs vs_notIte (vsSizes S.d) (fun _ ↦ S.ownW)
    (fun _ ↦ S.ownW_fits hbl hst)
    (fun fp ↦ S.kids (bases (fp + fs "verify_sub") (vsSizes S.d)) sqE)
    (vsNames S.μs S.rate (S.d - 20)) (vsBsAt W Bvk S.μs S.rate) (vsPsR W Pcp Pvt Pos) (vsQn S sqE outE)
    (fun _ ↦ vs_names S _ sqE)
    (fun fp ↦ vs_kidsDepBPR hbl S hκ hrf hcons W hvk _ sqE (hcp _ _) hvt (hos _))
    hkr hkm fun fp outs hlen ho rd hlow hB hL hLo =>
      let ⟨σ, e, h⟩ := hσ fp outs hlen ho rd hlow hB hL hLo
      ⟨σ, ⟨_, outs, e, hB⟩, h⟩
  refine CompleteAtDTBR.monoV h (by simp only [vsSizes, List.sum_cons, List.sum_nil, vsBoundAt, ChildSegs.μs]; omega)
    fun rd t rets hv ⟨hF, hn⟩ ↦ ⟨⟨S.d - 20, by omega,
      flatShape_mono hF (namedP_mono _ _ _ _ (vsPsR_imp W _ _ _ rd))⟩, ?_⟩
  obtain ⟨σ, bufs, ks, rfl, hQn⟩ := hn
  refine ⟨σ, bufs, ks, rfl, hQn, fun k hk hkv ↦ ?_⟩
  obtain ⟨σ', bufs', ks', e, hw⟩ := hF
  cases e
  obtain ⟨fn, hf, -, es, vs, hwk, -, -, hkk⟩ := hv
  obtain ⟨hl, hkT⟩ := hw fn es vs hf hwk
  obtain ⟨T, hT, hTt⟩ := kidsT_valid_mem _ _ _ hkk hkT hl k hk hkv
  exact vsNames_kidQ W Bvk S.μs S.rate (S.d - 20) _ _ _ rd T hT k hTt

/-- **`verify_sub` is complete on every honest child within its own bound**, by a node whose
callees are calls of their names within their bounds, at the child's announced stack log and
rate. -/
theorem verify_sub_completeBT {bytecode : List K} (hbl : bytecode.length = 2 ^ 23)
    (hrf : Lift.RunsFit fs cert) (hcons : RunsConsec cert) (W : VsWordsOs fs) {Bvk κ : ℕ}
    (hκ : 16 ≤ κ) (hvk : VkCompleteAtBK fs cert κ Bvk) (seed : Digest)
    (c : Child) (sqE outE : ℕ) (Lin : Main.Layout)
    (hmu : ∀ layout r, Verifier.announcedLayoutAndRate bytecode c.proof.stream = some (layout, r) →
      Coverage.minChildStackLog ≤ layout.stackLog)
    (hst : c.proof.stream.length ≤ Coverage.childStreamCap)
    (hrz : Limits.verifyDeferredRefusingZero bytecode seed (statementDigest seed c.statement)
      c.freshClaim c.proof = true)
    (hcaps : ∀ b ∈ Limits.queryStepsOf (deferringVerifierProgram c.freshClaim bytecode
      (statementDigest seed c.statement)) (Coverage.childVerifierStart seed c),
      Limits.OpeningsAgree b.1 b.2)
    (hexp : ∀ q ∈ vsExpLin sqE, q ∈ Lin) (hout : (outE, DeferredClaim.cells c.freshClaim) ∈ Lin) :
    CompleteAtDTB fs cert κ "verify_sub" Lin (vsArgs seed c sqE outE) (Returns [])
      (vsTsAny fs W Bvk (childShape bytecode c).1 (childShape bytecode c).2)
      (vsBoundAt W Bvk (childShape bytecode c).1 (childShape bytecode c).2) := by
  obtain ⟨S⟩ := child_segments hbl seed c hmu hrz hcaps
  rw [childShape_of S.hann]
  have hd := S.d_bounds hbl
  obtain ⟨hhs, h5⟩ := S.hs_bounds hbl
  exact (verify_sub_completeBTG hbl hrf hcons W hκ hvk S sqE outE Lin hst hexp hout
    (Pcp := fun _ _ ↦ True) (Pvt := fun _ _ ↦ True) (Pos := fun _ _ ↦ True)
    (fun _ _ ↦ (Tables.certify_placement_completeAtB fs cert (by omega) (heights_length6 S.rowsN S.hrowsL)
      (S.h30.trans (by norm_num)) (S.hs_lt33 hbl) (show S.hs.getD 5 0 ≤ 27 by omega) _ _).toR)
    (fun B ↦ (S.vt_kidBW hbl (by omega) W B).toR.mono le_rfl fun _ _ h ↦ ⟨h, trivial⟩)
    (fun bs _ ↦ (S.os_kidB open_stacked_completeAtB (by omega) hrf hcons W bs sqE).toDTB.toR)).toDTB
    fun _ _ h ↦ h.1

/-- **`verify_sub` is complete within its own bound by its callees' trees** at the deployed frame
sizes, `verify_keccak` within `vkBound`. -/
theorem verify_sub_completeBT_fs {bytecode : List K} (hbl : bytecode.length = 2 ^ 23)
    {cert : String → V → ℕ} (hrf : Lift.RunsFit LeanVM.Guest.B2C.fs cert)
    (hcons : RunsConsec cert) (W : VsWordsOs LeanVM.Guest.B2C.fs) {κ : ℕ} (hκ : 16 ≤ κ)
    (seed : Digest) (c : Child) (sqE outE : ℕ) (Lin : Main.Layout)
    (hmu : ∀ layout r, Verifier.announcedLayoutAndRate bytecode c.proof.stream = some (layout, r) →
      Coverage.minChildStackLog ≤ layout.stackLog)
    (hst : c.proof.stream.length ≤ Coverage.childStreamCap)
    (hrz : Limits.verifyDeferredRefusingZero bytecode seed (statementDigest seed c.statement)
      c.freshClaim c.proof = true)
    (hcaps : ∀ b ∈ Limits.queryStepsOf (deferringVerifierProgram c.freshClaim bytecode
      (statementDigest seed c.statement)) (Coverage.childVerifierStart seed c),
      Limits.OpeningsAgree b.1 b.2)
    (hexp : ∀ q ∈ vsExpLin sqE, q ∈ Lin) (hout : (outE, DeferredClaim.cells c.freshClaim) ∈ Lin) :
    CompleteAtDTB LeanVM.Guest.B2C.fs cert κ "verify_sub" Lin (vsArgs seed c sqE outE) (Returns [])
      (vsTsAny LeanVM.Guest.B2C.fs W vkBound (childShape bytecode c).1 (childShape bytecode c).2)
      (vsBoundAt W vkBound (childShape bytecode c).1 (childShape bytecode c).2) :=
  verify_sub_completeBT hbl hrf hcons W hκ (verify_keccak_completeAtB_fs (by omega)) seed c sqE
    outE Lin hmu hst hrz hcaps hexp hout

end
end LeanVM.Guest.B1.VerifySub
