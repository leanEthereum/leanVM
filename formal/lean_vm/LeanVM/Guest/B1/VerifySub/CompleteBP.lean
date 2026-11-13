/-
  LeanVM.Guest.B1.VerifySub.CompleteBP

  `verify_sub` complete within its child's bound by a node popping `Hints.childHints` past its advised sizes, stream by stream, given its `certify_placement`, `verify_tables` and `open_stacked` callees complete by trees popping theirs.
-/

module

public import LeanVM.Guest.B1.VerifySub.CompleteBT
public import LeanVM.Guest.B1.VerifySub.ChildPopsHon
public import LeanVM.Guest.B1.VerifySub.GroupOrderBlock

/-!
# `verify_sub`'s pops

`vsPsR`: `verify_sub`'s callees' predicates of the memory, `certify_placement`'s `Pcp`, `verify_tables`' `Pvt` beside its weights, `open_stacked`'s `Pos`. `vs_kidsDepBPR`: the callees within their bounds by trees of them, given `certify_placement`'s, `verify_tables`' and `open_stacked`'s (`hcp`, `hvt`, `hos`). `verify_sub_completeBTP`: `completeAt_flatDepRBPR` with the honest valuation and its own buffers (`vsQn`); its tree pops `childHints.drop 4`, stream by stream (`vs_hon_child_pops`, its callees found among the node's by name, `kidsT_valid_mem`, their entries by the group orders' equalities `colGroupOrder_layoutOf`, `blockGroupOrder_eq`). `verify_sub_completeBT` is its corollary at `open_stacked_completeAtB`, every predicate `True`.
-/

namespace LeanVM.Guest.B1.VerifySub

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Node LeanVM.Guest.Memory

@[expose] public section

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

/-- **A node's valid trees satisfy the predicate**, from its validity. -/
theorem CompleteAtDTBR.monoV {fs : String → ℕ} {cert : String → V → ℕ} {k : ℕ} {f : String} {Lin : Main.Layout}
    {args : List E} {Out : List E → Main.Layout → Prop} {T T' : Reader → Tree → Prop} {B B' : ℕ}
    (h : CompleteAtDTBR fs cert k f Lin args Out T B) (hB : B ≤ B')
    (hT : ∀ rd t rets, t.Valid coreProgram rd args rets → T rd t → T' rd t) :
    CompleteAtDTBR fs cert k f Lin args Out T' B' := fun fp =>
  let ⟨n, Lown, rets, Lout, hn, ho, hw, hd, hr⟩ := h fp
  ⟨n, Lown, rets, Lout, hn.trans hB, ho, hw, hd, fun rd hl hm =>
    let ⟨t, ht, hT'⟩ := hr rd hl hm
    ⟨t, ht, hT rd t rets ht.2.1 hT'⟩⟩

/-! ## The predicates -/

variable {fs : String → ℕ} {cert : String → V → ℕ}

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
    (t.name ∈ vsOpen → Pos rd t)

theorem vsKidQ_of {Pcp Pvt Pos : Reader → Tree → Prop} {rd : Reader} {t : Tree} {n : String} (hn : t.name = n)
    (hb : n ∉ "certify_placement" :: "verify_tables" :: vsOpen) : VsKidQ Pcp Pvt Pos rd t := by
  refine ⟨fun h => ?_, fun h => ?_, fun h => ?_⟩
  · exact absurd (by rw [← hn, h]; exact List.mem_cons_self) hb
  · exact absurd (by rw [← hn, h]; exact List.mem_cons_of_mem _ List.mem_cons_self) hb
  · exact absurd (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (hn ▸ h))) hb

theorem getD_not_mem {l bad : List String} (h : ∀ s ∈ l, s ∉ bad) (h0 : "" ∉ bad) (i : ℕ) : l.getD i "" ∉ bad := by
  rw [List.getD_eq_getElem?_getD]
  rcases hi : l[i]? with _ | s
  · exact h0
  · exact h s (List.mem_of_getElem? hi)

theorem squeeze_not_mem (i : ℕ) : squeezeNames.getD i "" ∉ "certify_placement" :: "verify_tables" :: vsOpen :=
  getD_not_mem (by decide) (by decide) i

theorem busGrind_not_mem (i : ℕ) : busGrindNames.getD i "" ∉ "certify_placement" :: "verify_tables" :: vsOpen :=
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

/-- `certify_placement`'s entry: its group order. -/
def vsPcp (lm : ℕ) (hs : List ℕ) (rd : Reader) (t : Tree) : Prop :=
  t.pops coreProgram rd = [("col_group_order", (Tables.cpGOrd lm hs).map (gen ^ ·))]

/-- `verify_tables`' entries: its group order, its round count. -/
def vsPvt (lm : ℕ) (rows : List ℕ) (n : ℕ) (rd : Reader) (t : Tree) : Prop :=
  t.pops coreProgram rd = [("block_group_order", Tables.vtGOrdW lm (Tables.vtHt rows)), ("zc_tau_max", [gen ^ n])]

/-- `open_stacked`'s entries: the child's Merkle hints, stream by stream. -/
def vsPos (bytecode : List K) (seed : Digest) (c : Child) (rd : Reader) (t : Tree) : Prop :=
  SameStreams (t.pops coreProgram rd) (Hints.merkleHints true (Hints.childQueries bytecode seed c) c.proof.openings)

/-- **`verify_sub` is complete on an honest child within its own bound by a node popping `childHints` past its
advised sizes**, stream by stream, given its `certify_placement`, `verify_tables` and `open_stacked` callees
complete by trees popping theirs. -/
theorem verify_sub_completeBTP {bytecode : List K} (hbl : bytecode.length = 2 ^ 23)
    (hrf : Lift.RunsFit fs cert) (hcons : RunsConsec cert) (W : VsWordsOs fs) {Bvk κ : ℕ}
    (hκ : 16 ≤ κ) (hvk : VkCompleteAtBK fs cert κ Bvk) {seed : Digest} {c : Child}
    (S : ChildSegs bytecode seed c) (sqE outE : ℕ) (Lin : Main.Layout)
    (hst : c.proof.stream.length ≤ Coverage.childStreamCap)
    (hexp : ∀ q ∈ vsExpLin sqE, q ∈ Lin) (hout : (outE, DeferredClaim.cells c.freshClaim) ∈ Lin)
    (hcp : ∀ e1 e2, CompleteAtDTBR fs cert κ "certify_placement" (Tables.cpLin S.logMem S.hs e1 e2)
      [ptr e1, ptr e2] (Tables.cpOut S.logMem S.hs) (vsPcp S.logMem S.hs)
      (fs "certify_placement" + Tables.cpSizes.sum))
    (hvt : ∀ B, CompleteAtDTBR fs cert κ "verify_tables" (S.H.linL B) (S.H.args B) (Returns (S.H.retsH B))
      (fun rd t ↦ (∀ op, Budget.WeighsLe coreProgram (W.ωv op) (vtWB W.toVsWords op) t) ∧
        vsPvt S.logMem S.rowsN S.H.n rd t) (vtMax fs W.Kf W.Ksh W.K10))
    (hos : ∀ bs pv, CompleteAtDTBR fs cert κ (Whir.openName S.μs) ((S.kids bs sqE).getD 14 noKid pv).Lin
      ((S.kids bs sqE).getD 14 noKid pv).args ((S.kids bs sqE).getD 14 noKid pv).Out (vsPos bytecode seed c)
      (osBosAt fs W.Bnd S.μs)) :
    CompleteAtDTBR fs cert κ "verify_sub" Lin (vsArgs seed c sqE outE) (Returns [])
      (fun rd t ↦ vsTsAny fs W Bvk S.μs S.rate t ∧
        SameStreams (t.pops coreProgram rd) ((Hints.childHints bytecode seed c).drop 4))
      (vsBoundAt W Bvk S.μs S.rate) := by
  have hd := S.d_bounds hbl
  obtain ⟨hkr, hkm, hσ⟩ := vs_obligations hbl S fs (κ := κ) (by omega) hexp hout (vs_callsMatch hbl S hexp)
  have h := completeAt_flatDepRBPR (fs := fs) (cert := cert) find_vs vs_not_loop κ Lin _ []
    (vs_body.trans vsT_splitPre) vs_cflat vs_caddrs vs_notIte (vsSizes S.d) (fun _ ↦ S.ownW)
    (fun _ ↦ S.ownW_fits hbl hst)
    (fun fp ↦ S.kids (bases (fp + fs "verify_sub") (vsSizes S.d)) sqE)
    (vsNames S.μs S.rate (S.d - 20)) (vsBsAt W Bvk S.μs S.rate)
    (vsPsR W (vsPcp S.logMem S.hs) (vsPvt S.logMem S.rowsN S.H.n) (vsPos bytecode seed c)) (vsQn S sqE outE)
    (fun _ ↦ vs_names S _ sqE)
    (fun fp ↦ vs_kidsDepBPR hbl S hκ hrf hcons W hvk _ sqE (hcp _ _) hvt (hos _))
    hkr hkm fun fp outs hlen ho rd hlow hB hL hLo =>
      let ⟨σ, e, h⟩ := hσ fp outs hlen ho rd hlow hB hL hLo
      ⟨σ, ⟨_, outs, e, hB⟩, h⟩
  refine CompleteAtDTBR.monoV h (by simp only [vsSizes, List.sum_cons, List.sum_nil, vsBoundAt, ChildSegs.μs]; omega)
    fun rd t rets hv ⟨hF, hn⟩ ↦ ⟨⟨S.d - 20, by omega,
      flatShape_mono hF (namedP_mono _ _ _ _ (vsPsR_imp W _ _ _ rd))⟩, ?_⟩
  obtain ⟨σ, bufs, ks, rfl, hQn⟩ := hn
  obtain ⟨σ', bufs', ks', e, hw⟩ := hF
  cases e
  obtain ⟨b, outs, rfl, hB⟩ := hQn
  obtain ⟨tcp, tvt, tos, ncp, nvt, nos, hmem, himpl⟩ :=
    vs_hon_child_pops S (args := vsArgs seed c sqE outE) rfl b outs hB hst hv
  obtain ⟨fn, hf, -, es, vs, hwk, -, -, hk⟩ := hv
  obtain ⟨hl, hkT⟩ := hw fn es vs hf hwk
  have hQ : ∀ t ∈ [tcp, tvt, tos],
      VsKidQ (vsPcp S.logMem S.hs) (vsPvt S.logMem S.rowsN S.H.n) (vsPos bytecode seed c) rd t := by
    intro t ht
    obtain ⟨hm, a, r, hvt'⟩ := hmem t ht
    obtain ⟨T, hT, hTt⟩ := kidsT_valid_mem _ _ _ hk hkT hl t hm ⟨a, r, hvt'⟩
    exact vsNames_kidQ W Bvk S.μs S.rate (S.d - 20) _ _ _ rd T hT t hTt
  have hlay : S.layout = Tables.layoutOf bytecode S.logMem S.rowsN := S.hlayout
  refine himpl ?_ ?_ ((hQ tos (by simp)).2.2 nos)
  · rw [(hQ tcp (by simp)).1 ncp, hlay, colGroupOrder_layoutOf hbl S.logMem S.hrowsL]
    rfl
  · have hn : S.H.n < 2 ^ 64 := by
      have := S.nT_le hbl
      have e : S.H.n = S.nT := rfl
      omega
    rw [(hQ tvt (by simp)).2.1 nvt, hlay, blockGroupOrder_eq hbl S.logMem S.hrowsL, count_eq_gen (by
      show S.H.n < 2 ^ 64; exact hn)]
    rfl

end
end LeanVM.Guest.B1.VerifySub
