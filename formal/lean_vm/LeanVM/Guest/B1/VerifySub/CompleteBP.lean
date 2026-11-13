/-
  LeanVM.Guest.B1.VerifySub.CompleteBP

  `verify_sub` complete within its child's bound by a node popping `Hints.childHints` past its advised sizes, stream by stream, given its `open_stacked` callee complete by trees popping the child's Merkle hints.
-/

module

public import LeanVM.Guest.B1.VerifySub.CompleteBT
public import LeanVM.Guest.B1.VerifySub.ChildPopsHon
public import LeanVM.Guest.B1.VerifySub.GroupOrderBlock

/-!
# `verify_sub`'s pops

`cp_honest_pops`, `vt_honest_pops`: `certify_placement`'s and `verify_tables`' honest nodes (`Tables.cpQn`, `Tables.vtQn`: the honest valuation, its own buffers held) pop their group orders and `verify_tables` its round count; `cp_kidBP`, `vt_kidBWP`: so on the honest child, from `certify_placement_completeAtBR` and `verify_tables_completeAtTBWR'`. `verify_sub_completeBTP`: `verify_sub_completeBTG` with them; its tree pops `childHints.drop 4`, stream by stream (`vs_hon_child_pops`, its callees' entries by `VsKidQ` and the group orders' equalities `colGroupOrder_layoutOf`, `blockGroupOrder_eq`).
-/

namespace LeanVM.Guest.B1.VerifySub

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Node LeanVM.Guest.Memory

@[expose] public section

variable {fs : String → ℕ} {cert : String → V → ℕ}

/-! ## The callees' entries -/

/-- `certify_placement`'s entry: its group order. -/
def vsPcp (lm : ℕ) (hs : List ℕ) (rd : Reader) (t : Tree) : Prop :=
  t.pops coreProgram rd = [("col_group_order", (Tables.cpGOrd lm hs).map (gen ^ ·))]

/-- `verify_tables`' entries: its group order, its round count. -/
def vsPvt (lm : ℕ) (rows : List ℕ) (n : ℕ) (rd : Reader) (t : Tree) : Prop :=
  t.pops coreProgram rd = [("block_group_order", Tables.vtGOrdW lm (Tables.vtHt rows)), ("zc_tau_max", [gen ^ n])]

/-- `open_stacked`'s entries: the child's Merkle hints, stream by stream. -/
def vsPos (bytecode : List K) (seed : Digest) (c : Child) (rd : Reader) (t : Tree) : Prop :=
  SameStreams (t.pops coreProgram rd) (Hints.merkleHints true (Hints.childQueries bytecode seed c) c.proof.openings)

theorem cpσ_136 {lm : ℕ} {hs : List ℕ} {ekb esq e10 e11 e136 e137 e293 : ℕ} {rd : Reader} :
    Tables.cpσ lm hs ekb esq e10 e11 e136 e137 e293 rd (.n 136) = ofK (addressOfIndex e136) := by
  show Tables.cpF lm hs ekb esq e10 e11 e136 e137 e293 rd 136 = _
  unfold Tables.cpF
  rw [Tables.tb_ite_neg (by omega), Tables.tb_ite_neg (by omega), Tables.tb_ite_neg (by omega),
    Tables.tb_ite_neg (by omega), Tables.tb_ite_neg (by omega), Tables.tb_ite_neg (by omega), Tables.tb_ite_pos rfl]

/-- **`certify_placement`'s honest node pops its group order**, which its buffer holds. -/
theorem cp_honest_pops {lm : ℕ} {hs : List ℕ} {ekb esq : ℕ} {rd : Reader} {t : Tree} {args rets : List E}
    (ht : Budget.NodeHonest coreProgram "certify_placement" (Tables.cpQn lm hs ekb esq rd) (flatCalls Tables.cpPre)
      (fun _ ↦ Tables.cpSizes) [] t) (hv : t.Valid coreProgram rd args rets) : vsPcp lm hs rd t := by
  obtain ⟨σ, ks, rfl, ⟨b, rfl, hB⟩, -⟩ := ht
  have hm : (b + 9 + 9, (Tables.cpGOrd lm hs).map (gen ^ ·)) ∈ bufL b Tables.cpSizes (Tables.cpOwnL lm hs) :=
    List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)
  rw [vsPcp, cp_pops hv, cpPop_honest cpσ_136 (hB _ hm) (by rw [List.length_map, Tables.cpGOrd_length])]

/-- **`verify_tables`' honest node pops its group order and its round count**, which its buffer and valuation
hold. -/
theorem vt_honest_pops {H : Tables.VtHonest} {B : Tables.VtBases} {rd : Reader} {t : Tree} {σ : Val}
    {ks : List Tree} {args rets : List E} (e : t = .node "verify_tables" σ H.sizes ks) (hq : Tables.vtQn H B rd σ)
    (hv : t.Valid coreProgram rd args rets) :
    t.pops coreProgram rd = [("block_group_order", Tables.vtGOrdW H.lm H.τ), ("zc_tau_max", [gen ^ H.n])] := by
  subst e
  obtain ⟨o, -, hB, h36, h2544⟩ := hq
  have hm : (o + 24 + 24 + 24, Tables.vtGOrdW H.lm H.τ) ∈ bufL o H.sizes (H.ownW B) :=
    List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))
  have hl : (Tables.vtGOrdW H.lm H.τ).length = 24 := by rw [Tables.vtGOrdW, List.length_map, List.length_range]
  have hr : ReadsAt rd (ofK (addressOfIndex (o + 24 + 24 + 24))) (Tables.vtGOrdW H.lm H.τ) := hB _ hm
  have hw := heap_words (off := 0) (len := 24) h36 hr (by omega)
  rw [vt_pops hv]
  rw [vtPops, hw, List.drop_zero, List.take_of_length_le (by omega), h2544]

theorem vt_honest_vsPvt {H : Tables.VtHonest} {B : Tables.VtBases} {rd : Reader} {t : Tree} {σ : Val}
    {ks : List Tree} {args rets : List E} {lm : ℕ} {rows : List ℕ} (hlm : H.lm = lm) (hrows : H.rows = rows)
    (e : t = .node "verify_tables" σ H.sizes ks) (hq : Tables.vtQn H B rd σ) (hv : t.Valid coreProgram rd args rets) :
    vsPvt lm rows H.n rd t := by
  subst hlm hrows
  rw [vsPvt, vt_honest_pops e hq hv]
  rfl

namespace ChildSegs

variable {bytecode : List K} {seed : Digest} {c : Child} (S : ChildSegs bytecode seed c)

/-- **`certify_placement` on the honest child, by a tree popping its group order.** -/
theorem cp_kidBP (hbl : bytecode.length = 2 ^ 23) {κ : ℕ} (hκ : 14 ≤ κ) (e1 e2 : ℕ) :
    CompleteAtDTBR fs cert κ "certify_placement" (Tables.cpLin S.logMem S.hs e1 e2)
      [ptr e1, ptr e2] (Tables.cpOut S.logMem S.hs) (vsPcp S.logMem S.hs)
      (fs "certify_placement" + Tables.cpSizes.sum) := by
  have hd := S.d_bounds hbl
  obtain ⟨hhs, h5⟩ := S.hs_bounds hbl
  exact (Tables.certify_placement_completeAtBR fs cert hκ (heights_length6 S.rowsN S.hrowsL)
    (S.h30.trans (by norm_num)) (S.hs_lt33 hbl) (show S.hs.getD 5 0 ≤ 27 by omega) e1 e2).monoV le_rfl
    fun _ _ _ hv ht ↦ cp_honest_pops ht hv

/-- **`verify_tables` on the honest child, within `vtMax` by a tree within its weights popping its group order and
its round count.** -/
theorem vt_kidBWP (hbl : bytecode.length = 2 ^ 23) {κ : ℕ} (hκ : 14 ≤ κ) (W : VsWordsOs fs) (B : Tables.VtBases) :
    CompleteAtDTBR fs cert κ "verify_tables" (S.H.linL B) (S.H.args B) (Returns (S.H.retsH B))
      (fun rd t ↦ (∀ op, Budget.WeighsLe coreProgram (W.ωv op) (vtWB W.toVsWords op) t) ∧
        vsPvt S.logMem S.rowsN S.H.n rd t) (vtMax fs W.Kf W.Ksh W.K10) :=
  (Tables.verify_tables_completeAtTBWR' hκ (S.H_run hbl).1 (S.H_shape hbl) B W.Kf W.Ksh W.K10 W.hKf
    W.hsh W.h10 W.ωv W.Kvw W.Wss W.Kw10 W.hKvw W.hssw W.h10w).monoV (S.vt_bound_le hbl W)
    fun _ _ _ hv ⟨hw, _, _, e, hq⟩ ↦ ⟨hw, vt_honest_vsPvt rfl rfl e hq hv⟩

end ChildSegs

/-! ## `verify_sub` -/

/-- **`verify_sub` is complete on an honest child within its own bound by a node popping `childHints` past its
advised sizes**, stream by stream, given its `open_stacked` callee complete by trees popping the child's Merkle
hints. -/
theorem verify_sub_completeBTP {bytecode : List K} (hbl : bytecode.length = 2 ^ 23)
    (hrf : Lift.RunsFit fs cert) (hcons : RunsConsec cert) (W : VsWordsOs fs) {Bvk κ : ℕ}
    (hκ : 16 ≤ κ) (hvk : VkCompleteAtBK fs cert κ Bvk) {seed : Digest} {c : Child}
    (S : ChildSegs bytecode seed c) (sqE outE : ℕ) (Lin : Main.Layout)
    (hst : c.proof.stream.length ≤ Coverage.childStreamCap)
    (hexp : ∀ q ∈ vsExpLin sqE, q ∈ Lin) (hout : (outE, DeferredClaim.cells c.freshClaim) ∈ Lin)
    (hos : ∀ bs pv, CompleteAtDTBR fs cert κ (Whir.openName S.μs) ((S.kids bs sqE).getD 14 noKid pv).Lin
      ((S.kids bs sqE).getD 14 noKid pv).args ((S.kids bs sqE).getD 14 noKid pv).Out (vsPos bytecode seed c)
      (osBosAt fs W.Bnd S.μs)) :
    CompleteAtDTBR fs cert κ "verify_sub" Lin (vsArgs seed c sqE outE) (Returns [])
      (fun rd t ↦ vsTsAny fs W Bvk S.μs S.rate t ∧
        SameStreams (t.pops coreProgram rd) ((Hints.childHints bytecode seed c).drop 4))
      (vsBoundAt W Bvk S.μs S.rate) := by
  refine CompleteAtDTBR.monoV (verify_sub_completeBTG hbl hrf hcons W hκ hvk S sqE outE Lin hst hexp hout
    (fun _ _ ↦ S.cp_kidBP hbl (by omega) _ _) (fun B ↦ S.vt_kidBWP hbl (by omega) W B) hos) le_rfl
    fun rd t rets hv ⟨hT, σ, bufs, ks, e, hQn, hK⟩ ↦ ⟨hT, ?_⟩
  subst e
  obtain ⟨b, outs, rfl, hB⟩ := hQn
  obtain ⟨tcp, tvt, tos, ncp, nvt, nos, hmem, himpl⟩ :=
    vs_hon_child_pops S (args := vsArgs seed c sqE outE) rfl b outs hB hst hv
  have hQ : ∀ t ∈ [tcp, tvt, tos],
      VsKidQ (vsPcp S.logMem S.hs) (vsPvt S.logMem S.rowsN S.H.n) (vsPos bytecode seed c) rd t := by
    intro t ht
    obtain ⟨hm, a, r, hvt'⟩ := hmem t ht
    exact hK t hm ⟨a, r, hvt'⟩
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
