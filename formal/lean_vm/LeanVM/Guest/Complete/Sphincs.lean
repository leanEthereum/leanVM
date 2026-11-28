module

public import LeanVM.Guest.Complete.Call0
public import LeanVM.Guest.B1.Sig.SphincsSigPops
public import LeanVM.Guest.B1.Sig.SphincsExact
public import LeanVM.Guest.Exact.SpWotsFree
public import LeanVM.Guest.Memory.Straight
public import LeanVM.Guest.Memory.GuestWf
import LeanVM.Guest.ValRef
import LeanVM.Guest.Data.ValNames.«verify_sig_lean_sphincs»

/-!
# leanSPHINCS's check, complete

`verify_sig_lean_sphincs` and its three calls of `sp_wots` take no words of their own
(`CallCompletes0`): on a claim at `p` that a signature verifies and the byte table at `bb`, the
check's tree pops `Sig.spSegPops` (its hints, `Sig.spSegPops_sameStreams`), every node exact
(`verify_sig_lean_sphincs_completes`). Its valuation is `Sig.verify_sig_lean_sphincs_complete_vals`'
under the trivial call relation; the body is straight (`sStraight`), its calls the three layers'
honest calls of `sp_wots` (`sp_wots_completes`), whose computed hints are pinned
(`sp_wots_exactFree`), its own bit hints exact by `Sig.sNode_exact`.
-/

namespace LeanVM.Guest.Complete

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Memory LeanVM.Guest.B1

@[expose] public section

set_option linter.constructorNameAsVariable false

/-- `sp_wots`'s completeness: its entries for `digest` and `values`, every node exact. -/
def SpWotsPost (digest : HashSig.Digest) (values : Sphincs.ChainIndex → HashSig.Digest) (rd : Reader)
    (t : Tree) : Prop :=
  t.pops coreProgram rd = Sig.spWotsPops digest values ∧ t.Every (ExactAt coreProgram rd)

/-- **`sp_wots` completes**, on memories defined below `2^6`, popping its digest's digit words
and its chains' values. -/
theorem sp_wots_completes {k : ℕ} (hk : 6 ≤ k) (publicSeed : HashSig.PublicParameter)
    (layer : Sphincs.Layer) (tree : Sphincs.TreeIndex) (leaf : Sphincs.TreeLeafIndex) (digest : HashSig.Digest)
    (values : Sphincs.ChainIndex → HashSig.Digest)
    (hT : Sphincs.TargetSum.Valid (Sphincs.TargetSum.base2bDigits digest)) :
    CallCompletes0 k "sp_wots"
      [Sig.cellOf128 publicSeed, (Sig.keyAdrsCells layer.val tree.val leaf.val).1,
        (Sig.keyAdrsCells layer.val tree.val leaf.val).2, Sig.cellOf128 digest]
      [Sig.cellOf128 (Sig.wotsLeafOf publicSeed layer tree leaf digest values)] (fun _ => True)
      (SpWotsPost digest values) := by
  refine callCompletes0_node fun rd hl _ => ?_
  have hm : Sig.MemOK rd 64 := fun i hi => hl.mono hk i (by norm_num; omega)
  obtain ⟨σ, h0, h12, h3, hb, es, vs, hw, hc, hp⟩ :=
    Sig.sp_wots_complete_pops (fun _ _ _ => True) rd publicSeed layer tree leaf digest values hm hT
  have hsat := walk_sat (P := coreProgram) (fn% «sp_wots»).body
    (coreProgram_wf _ (List.mem_of_find?_eq_some Sig.find_sp_wots)) hb
  rw [hw] at hsat
  have hev : ∀ e ∈ es, e.Holds rd σ := fun e he => (hsat.1 e he).1
  have hpar : (fn% «sp_wots»).params.map σ = [Sig.cellOf128 publicSeed,
      (Sig.keyAdrsCells layer.val tree.val leaf.val).1, (Sig.keyAdrsCells layer.val tree.val leaf.val).2,
      Sig.cellOf128 digest] := by
    rw [Sig.sp_wots_params, ← h12, ← h0, ← h3]; rfl
  have hk' : Tree.KidsValid coreProgram rd σ (calls es) [] := by rw [hc]; exact kidsValid_nil
  refine ⟨σ, _, es, vs, [], Sig.find_sp_wots, hpar, hw, hsat.2, hev, hk', by rw [Tree.BufsOkKids]; trivial,
    ?_, ?_⟩
  · rw [pops_node Sig.find_sp_wots hw, Tree.popsKids, splice_nil_of_calls es hc, hp]
  · exact every_exact_of_free sp_wots_exactFree (t := .node "sp_wots" σ (allocs σ es) [])
      ⟨_, Sig.find_sp_wots, hpar, es, vs, hw, hsat.2, hev, hk'⟩ rfl rd

/-! ## The check -/

/-- `verify_sig_lean_sphincs`'s statements before its return. -/
def sPreR : List Stmt := Sig.sPre ++ [.atom (.assertEq Sig.sLayerT.2.2 Sig.sRoot)]

theorem sBody_straight : (fn% «verify_sig_lean_sphincs»).body = sPreR ++ [.ret []] := by
  rw [Sig.sBody_eq, Sig.sBody_splitC, sPreR, List.append_assoc]
  rfl

set_option maxRecDepth 100000 in
theorem sStraight : sPreR.all Stmt.straight = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem sCalls : sPreR.filterMap Stmt.callS = [(none, "sp_wots", Sig.sCallArgs 0, [Sig.sLeafOf 0]),
    (none, "sp_wots", Sig.sCallArgs 1, [Sig.sLeafOf 1]), (none, "sp_wots", Sig.sCallArgs 2, [Sig.sLeafOf 2])] := by
  decide +kernel

/-- **The three layers' encodings reach the target sum**, for a signature that verifies. -/
theorem sp_layers_valid {pk : Sphincs.PublicKey} {m : HashSig.Message} {sig : Sphincs.Signature}
    (hv : Sphincs.verifyWithKeccak pk m sig = true) :
    Sphincs.TargetSum.Valid (Sphincs.TargetSum.base2bDigits
        (Sig.cellVal (Sig.layerEnc pk (Sig.digestIdx pk m sig) sig ⟨0, by decide⟩ (Sig.forsKeyCell pk m sig)))) ∧
      Sphincs.TargetSum.Valid (Sphincs.TargetSum.base2bDigits
        (Sig.cellVal (Sig.layerEnc pk (Sig.digestIdx pk m sig) sig ⟨1, by decide⟩ (Sig.sRoot0 pk m sig)))) ∧
      Sphincs.TargetSum.Valid (Sphincs.TargetSum.base2bDigits
        (Sig.cellVal (Sig.layerEnc pk (Sig.digestIdx pk m sig) sig ⟨2, by decide⟩ (Sig.sRoot1 pk m sig)))) := by
  obtain ⟨r0, r1, h0, h1, h2⟩ := (Sig.verifyWithKeccak_iff_stages pk m sig).mp hv
  rw [Sig.sForsKeyOf_eq] at h0
  obtain ⟨hV0, hr0⟩ := Sig.layer_cells h0
  rw [hr0] at h1
  obtain ⟨hV1, hr1⟩ := Sig.layer_cells h1
  rw [hr1] at h2
  exact ⟨hV0, hV1, (Sig.layer_cells h2).1⟩

/-- **Layer `L`'s call of `sp_wots` completes**, when it is the honest one, popping `Sig.spKid`. -/
theorem layer_completes {k : ℕ} (hk : 6 ≤ k) {pk : Sphincs.PublicKey} {m : HashSig.Message}
    {sig : Sphincs.Signature} {σ : Val} {L : Sphincs.Layer} {S : E}
    (hT : Sphincs.TargetSum.Valid
      (Sphincs.TargetSum.base2bDigits (Sig.cellVal (Sig.layerEnc pk (Sig.digestIdx pk m sig) sig L S))))
    (h : Sig.LayerCallAt pk m sig σ L S) :
    CallCompletes0 k "sp_wots" ((Sig.sCallArgs L.val).map σ) ([Sig.sLeafOf L.val].map σ) (fun _ => True)
      (fun rd t => t.pops coreProgram rd = Sig.spKid pk m sig L S ∧ t.Every (ExactAt coreProgram rd)) := by
  have hr := sp_wots_completes hk pk.publicSeed L (Sphincs.treeOfIndex L (Sig.digestIdx pk m sig))
    (Sphincs.leafOfIndex L (Sig.digestIdx pk m sig)) (Sig.cellVal (Sig.layerEnc pk (Sig.digestIdx pk m sig) sig L S))
    (sig.layers L).chainValues hT
  rw [Sig.cellOf128_cellVal] at hr
  rw [h.1, List.map_cons, List.map_nil, h.2]
  exact hr

/-- What `verify_sig_lean_sphincs` reads: the byte table at `bb` and the claim at `p`. -/
def SphincsPre (p bb : E) (pk : Sphincs.PublicKey) (m : HashSig.Message) (rd : Reader) : Prop :=
  Sig.ByteBits rd bb ∧ Sig.ClaimAt rd p (Sig.cellOf128 pk.publicSeed) (Sig.cellOf128 pk.root)
    (Sig.cellOf128 (m.extractLsb' 0 128)) (Sig.cellOf128 (m.extractLsb' 128 128))

/-- `verify_sig_lean_sphincs`'s completeness: its entries, every node exact. -/
def SphincsPost (pk : Sphincs.PublicKey) (m : HashSig.Message) (sig : Sphincs.Signature) (rd : Reader)
    (t : Tree) : Prop :=
  t.pops coreProgram rd = Sig.spSegPops pk m sig ∧ t.Every (ExactAt coreProgram rd)

set_option maxRecDepth 100000 in
/-- **`verify_sig_lean_sphincs` completes**, on memories defined below `2^8`: on a claim at `p`
that `sig` verifies and the byte table at `bb`, its tree pops `Sig.spSegPops pk m sig`, every node
exact. -/
theorem verify_sig_lean_sphincs_completes {k : ℕ} (hk : 8 ≤ k) (p bb : E) (pk : Sphincs.PublicKey)
    (m : HashSig.Message) (sig : Sphincs.Signature) (hv : Sphincs.verifyWithKeccak pk m sig = true) :
    CallCompletes0 k "verify_sig_lean_sphincs" [p, bb] [] (SphincsPre p bb pk m) (SphincsPost pk m sig) := by
  refine callCompletes0_node fun rd hl ⟨hbb, hat⟩ => ?_
  have hm : Sig.MemOK rd 256 := fun i hi => hl.mono hk i (by norm_num; omega)
  obtain ⟨σ, h0, h1, hb, hwk, -, hcs, hS⟩ := Sig.verify_sig_lean_sphincs_complete_vals (fun _ _ _ => True)
    rd p bb pk m sig (fun _ _ _ _ _ _ _ => trivial) hm hbb hat hv
  have hwf := coreProgram_wf _ (List.mem_of_find?_eq_some Sig.find_verify_sig_lean_sphincs)
  have hw := walk_straight σ [] sPreR sStraight
  have hsat : (walk σ (sPreR ++ [Stmt.ret []])).Sat (fun _ _ _ => True) rd σ False (fun rs => rs = []) := by
    rw [sBody_straight] at hwf hb
    generalize hB : sPreR ++ [Stmt.ret []] = B at hwf hb ⊢
    exact walk_sat (P := coreProgram) _ hwf hb
  rw [hw] at hsat
  rw [← sBody_straight] at hw
  have hev : ∀ e ∈ sPreR.flatMap (slEvs σ), e.Holds rd σ := fun e he => (hsat.1 e he).1
  have hc : calls (sPreR.flatMap (slEvs σ)) = [⟨"sp_wots", Sig.sCallArgs 0, [Sig.sLeafOf 0], true⟩,
      ⟨"sp_wots", Sig.sCallArgs 1, [Sig.sLeafOf 1], true⟩, ⟨"sp_wots", Sig.sCallArgs 2, [Sig.sLeafOf 2], true⟩] := by
    rw [(straight_parts σ _ sStraight).2.2.2, sCalls]
    rfl
  obtain ⟨-, hps⟩ := hwk _ [] hw
  obtain ⟨hV0, hV1, hV2⟩ := sp_layers_valid hv
  obtain ⟨t0, hn0, hv0, hb0, hp0, hx0⟩ := layer_completes (k := k) (by omega) hV0 hcs.1 rd hl trivial
  obtain ⟨t1, hn1, hv1, hb1, hp1, hx1⟩ := layer_completes (k := k) (by omega) hV1 hcs.2.1 rd hl trivial
  obtain ⟨t2, hn2, hv2, hb2, hp2, hx2⟩ := layer_completes (k := k) (by omega) hV2 hcs.2.2 rd hl trivial
  refine ⟨σ, _, _, [], [t0, t1, t2], Sig.find_verify_sig_lean_sphincs, ?_, hw, rfl, hev, ?_, ?_, ?_, ?_⟩
  · rw [Sig.verify_sig_lean_sphincs_params]
    simp only [List.map_cons, List.map_nil, h0, h1]
  · rw [hc]
    exact kidsValid_cons_taken rfl hn0 hv0 (kidsValid_cons_taken rfl hn1 hv1
      (kidsValid_cons_taken rfl hn2 hv2 kidsValid_nil))
  · rw [Tree.BufsOkKids, Tree.BufsOkKids, Tree.BufsOkKids, Tree.BufsOkKids]
    exact ⟨hb0, hb1, hb2, trivial⟩
  · rw [pops_node Sig.find_verify_sig_lean_sphincs hw, Tree.popsKids, Tree.popsKids, Tree.popsKids,
      Tree.popsKids, hp0, hp1, hp2]
    exact hps
  · refine Tree.every_node.mpr ⟨exactAt_of_walk Sig.find_verify_sig_lean_sphincs hw
      (Sig.sNode_exact hw hev hS), ?_⟩
    rw [Tree.EveryKids, Tree.EveryKids, Tree.EveryKids, Tree.EveryKids]
    exact ⟨hx0, hx1, hx2, trivial⟩

end
end LeanVM.Guest.Complete
