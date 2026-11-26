/-
  LeanVM.Guest.B1.VerifySub.CompleteBP

  `verify_sub` complete within its child's bound by a node popping `Hints.childHints`, stream by stream, given its `open_stacked` callee complete by trees popping the child's Merkle hints.
-/

module

public import LeanVM.Guest.B1.VerifySub.CompleteBT
public import LeanVM.Guest.B1.VerifySub.ChildPopsHon
public import LeanVM.Guest.B1.VerifySub.GroupOrderBlock
import LeanVM.Guest.ValRef
import LeanVM.Guest.Data.ValNames.«certify_placement»

/-!
# `verify_sub`'s pops

`cp_honest_pops`, `vt_honest_pops`: `certify_placement`'s and `verify_tables`' honest nodes (`Tables.cpQn`, `Tables.vtQn`: the honest valuation, its own buffers held) pop their group orders and `verify_tables` its round count; `cp_kidBP`: so on the honest child, from `certify_placement_completeAtBR`. `vsPcp`, `vsPvt`, `vsPos`: the callees' entries.
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
    Tables.cpσ lm hs ekb esq e10 e11 e136 e137 e293 rd (.n (val% «certify_placement» "group_order")) = ofK (addressOfIndex e136) := by
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

end ChildSegs

/-! ## `verify_sub` -/

end
end LeanVM.Guest.B1.VerifySub
