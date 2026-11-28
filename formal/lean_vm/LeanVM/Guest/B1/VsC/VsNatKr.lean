/-
  LeanVM.Guest.B1.VsC.VsNatKr

  The Keccak reduction's run at the honest context, as `D3.Ok` asks it: the table's point and lanes the guest's
  buffers, the result one output claim.
-/

module

public import LeanVM.Guest.B1.VsC.VsNatVk
public import LeanVM.Guest.B1.VsC.VkInvOs
public import LeanVM.Guest.B1.VerifySub.PhLinkEnd

/-!
# `verify_keccak`'s run, `D3.Ok`'s fields

`natTail`'s Keccak run is on the link's `KECCAK` column: its point is the row point's first `τ` words
(`end_keccak_point`), which `.n 15`'s buffer holds (`bw 9`, the row side's challenges), and its lanes the packed
message's words `55 ..< 80` (`end_keccak`), the stream's from `natBm + 55`. Its result is one output claim, a point
and `64` slices (`vk_shape`). **`VsCtx.kec_nat`**: the run `D3.Ok.hrun` asks, at `bm = natBm`, `nx` the run's word
count, with `hpend`, the lengths and `τ`'s bounds; **`VsCtx.kec_bufs`**: `hrun`, `hop`, `hpt`, `hptl` at buffers
`.n 20` (`bw 14`: the claim's point padded to `qkeccakVarsCap`, then the point padded) and `.n 21` (`bw 15`: the
slices first).
-/

namespace LeanVM.Guest.B1.VsC

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Memory LeanVM.Guest.B1
open LeanVM.Guest.Complete LeanVM.Guest.B1.Fwd LeanVM.Guest.B1.Link LeanVM.Node LeanVM.Protocol
open LeanVM.Protocol.Verifier LeanVM.Protocol.Compile LeanVM.Protocol.KeccakHash LeanVM.Protocol.Link
open LeanVM.Guest.B1.VerifySub (qkeccakVarsCap keccakTauMin keccakTauMax)
open LeanVM.Guest.B1.Link.Arith (tailRowSide)

@[expose] public section

/-- Twenty-five words from `55` of a list whose first `144` are `m`. -/
theorem drop55_take25 {D m : List E} (h : D.take 144 = m) (hm : m.length = 144) :
    (D.drop 55).take 25 = (List.range 25).map fun i => m.getD (55 + i) 0 := by
  have hD : 144 ≤ D.length := by
    have := congrArg List.length h
    rw [List.length_take, hm] at this
    omega
  subst h
  apply List.ext_getElem
  · simp only [List.length_take, List.length_drop, List.length_map, List.length_range]
    omega
  · intro i h1 h2
    simp only [List.length_map, List.length_range] at h2
    rw [List.getElem_take, List.getElem_drop, List.getElem_map, List.getElem_range,
      List.getD_eq_getElem _ _ (by simp only [List.length_take]; omega), List.getElem_take]

section
variable {x : VsCtx} {L : LinkNat}

/-- The row point has the tallest table's log height of words. -/
theorem chi_length (lay : Layout) (F : Fs) : (L.chi lay F).length = linkRows lay := by
  unfold LinkNat.chi LinkNat.chainR
  rw [List.length_map, natChain_length]

/-- **`natTail`'s Keccak run at the honest context**, as `D3.Ok.hrun` asks it: on `.n 15`'s first `τ` words
and the packed message's lanes, from `packed_message`'s returns, on the stream's words past the packed message;
its result one output claim, a point and `64` slices, its end sponge's queue full. -/
theorem VsCtx.kec_nat {layout : Layout} {r : ℕ} {link : LinkEnd} {rest lanes xs rest' : List E} {n : E}
    {outs : List ColumnClaim} {kp ks : List E} {s' : Fs} (hret : CausalRule x.ret)
    (hann : announcedLayoutAndRate guestBytecode x.c.proof.stream = some (layout, r))
    (hN : FrontNum (chunksOf x.c.proof.stream.length) r layout.logMemory (hMax layout) (widthOf layout)
      (flagOf layout) (padStream x.c.proof.stream) (fun t => layout.tableLogHeights.getD t 0)
      (fun t => layout.tableRows.getD t 0))
    (hw : x.c.proof.stream.drop 12 = L.words layout ++ rest)
    (hL : L.Ok layout (natF3 x.seed x.c layout.stackLog) x.c.freshClaim link)
    (hln : kLanes link = some lanes) (hr : rest = xs ++ n :: rest')
    (hrun : RunsTo (verifyKeccak (layout.tableLogHeights.getD opKeccak 0) (link.columns.getD opKeccak ([], [])).1
      lanes) (L.F4 layout (natF3 x.seed x.c layout.stackLog)).squeeze.2 xs (outs, kp, ks) s')
    (hb18 : x.bw.getD 18 [] = padStream x.c.proof.stream)
    (r1287 : ∀ j < 6, ∀ σ, x.ret (1287 + j) σ = (x.natPm L).getD j 0)
    (h9 : (x.bw.getD 9 []).take x.nS = L.chi x.lay x.nF) :
    ∃ op kw, outs = [⟨qkeccak, op, kw⟩] ∧ ks.length = 64 ∧ s'.pend.length = rateScalars ∧
      op.length ≤ qkeccakVarsCap ∧ kp.length ≤ qkeccakVarsCap ∧ keccakTauMin ≤ x.hgS 5 ∧ x.hgS 5 ≤ keccakTauMax ∧
      RunsTo (verifyKeccak (x.hgS 5) ((x.bw.getD 9 []).take (x.hgS 5)) (x.sw (x.natBm L) 55 25))
        ⟨[x.w 1288, x.w 1289, x.w 1290, x.w 1291, x.w 1292], []⟩ (x.sw (x.natBm L) 144 xs.length)
        ([⟨qkeccak, op, kw⟩], kp, ks) s' := by
  have hlay : x.lay = layout := VsCtx.lay_of hann
  have htab : x.lay.tables = tables := by rw [hlay]; exact announced_tables hann
  rw [← hlay] at hw hL hrun
  have hF : natF3 x.seed x.c x.lay.stackLog = x.nF := rfl
  rw [hF] at hL hrun
  -- the heights
  have h9' : 9 ≤ x.hgS 5 := by rw [VsCtx.hgS, hlay]; exact hN.h9
  have h24 : x.hgS 5 ≤ 24 := by rw [VsCtx.hgS, hlay]; exact hN.h24 5 (by norm_num)
  have hnS : x.hgS 5 ≤ x.nS := by rw [VsCtx.hgS, VsCtx.nS, hlay]; exact hN.hht 5 (by norm_num)
  have hk5 : x.lay.tableLogHeights.getD opKeccak 0 = x.hgS 5 := rfl
  -- the `KECCAK` column
  have hcol : link.columns.getD opKeccak ([], []) = (tailRowSide x.lay L.chunks (L.theta0 x.lay x.nF)
      (L.drawn x.lay x.nF) (L.r x.lay x.nF) L.m1 (L.fresh x.lay x.nF) (Split.ofColumns tables x.c.freshClaim.values)
      (L.chi x.lay x.nF) (L.qPoint x.lay x.nF) L.msg).columns.getD opKeccak ([], []) := by
    rw [hL.link]; rfl
  have hpt : (link.columns.getD opKeccak ([], [])).1 = (x.bw.getD 9 []).take (x.hgS 5) := by
    rw [hcol, VerifySub.end_keccak_point htab _ _ _ _ _ _ _ _ _ hL.lenM, ← h9, List.take_take, hk5]
    congr 1
    omega
  have hpl : ((x.bw.getD 9 []).take (x.hgS 5)).length = x.hgS 5 := by
    have e : (x.bw.getD 9 []).take (x.hgS 5) = (L.chi x.lay x.nF).take (x.hgS 5) := by
      rw [← h9, List.take_take]
      congr 1
      omega
    rw [e, List.length_take, chi_length]
    have : linkRows x.lay = x.nS := rfl
    omega
  -- the lanes
  have hwd : L.chunks.width = x.wdS := by rw [VerifySub.chunks_width hL.chunks]; rfl
  have hbits : L.bits x.lay ≠ 0 := by
    have h19 : 19 ≤ x.wdS := by rw [VsCtx.wdS, hlay]; exact hN.hw19
    exact grindingBits_ne (le_max_of_le_right (by omega))
  have hlanes0 : lanes = (List.range 25).map fun lane ↦ L.msg.getD (55 + lane) 0 := by
    have e : kLanes link = some ((List.range 25).map fun lane ↦ L.msg.getD (55 + lane) 0) := by
      unfold kLanes
      rw [hcol]
      exact VerifySub.end_keccak htab _ _ _ _ _ _ _ _ _ hL.lenM
    rw [hln] at e
    exact Option.some.inj e
  have hlanes : lanes = x.sw (x.natBm L) 55 25 := by
    rw [hlanes0, VsCtx.sw, ← List.drop_drop]
    exact (drop55_take25 (x.sw_nat hbits hw hb18 hL.lenM).1 hL.lenM).symm
  -- the run
  have hq : linkQVars x.lay ≠ 0 := by rw [VerifySub.linkQVars_tables htab]; decide
  have hrun' := x.hrun_nat hret hbits hq hw hb18 hL.lenM r1287 hr hrun
  rw [hpt, hlanes] at hrun'
  have hll : (x.sw (x.natBm L) 55 25).length = keccakStateLanes := by
    rw [← hlanes, hlanes0, List.length_map, List.length_range]
    rfl
  have hshape : ((x.bw.getD 9 []).take (x.hgS 5)).length = x.hgS 5 ∧
      (x.sw (x.natBm L) 55 25).length = keccakStateLanes ∧ 4 ≤ x.hgS 5 := ⟨hpl, hll, by omega⟩
  rw [hpt, hlanes, hk5] at hrun
  obtain ⟨op, point, slices, word, hres, hsl, hpend, hopl, hptl⟩ :=
    VkOs.vk_shape (S := (L.F4 x.lay x.nF).perm) hshape hrun
  simp only [Prod.mk.injEq] at hres
  obtain ⟨rfl, rfl, rfl⟩ := hres
  refine ⟨op, word, rfl, hsl, hpend, ?_, ?_, by show 9 ≤ x.hgS 5; omega, by show x.hgS 5 ≤ 24; omega, hrun'⟩
  · show _ ≤ 39; omega
  · show _ ≤ 39; omega

/-- **`D3.Ok`'s Keccak fields at the buffers**: `.n 21`'s first `64` words the slices, `.n 20`'s the claim's point
padded to `qkeccakVarsCap`, then the input point padded. -/
theorem VsCtx.kec_bufs {op kp ks : List E} {kw : E} {s' : Fs} {bm nx : ℕ}
    (hb15 : (x.bw.getD 15 []).take 64 = ks)
    (hb14 : x.bw.getD 14 [] = op ++ List.replicate (qkeccakVarsCap - op.length) 0 ++
      (kp ++ List.replicate (qkeccakVarsCap - kp.length) 0))
    (hopl : op.length ≤ qkeccakVarsCap) (hptl : kp.length ≤ qkeccakVarsCap)
    (hrun : RunsTo (verifyKeccak (x.hgS 5) ((x.bw.getD 9 []).take (x.hgS 5)) (x.sw bm 55 25))
      ⟨[x.w 1288, x.w 1289, x.w 1290, x.w 1291, x.w 1292], []⟩ (x.sw bm 144 nx) ([⟨qkeccak, op, kw⟩], kp, ks) s') :
    RunsTo (verifyKeccak (x.hgS 5) ((x.bw.getD 9 []).take (x.hgS 5)) (x.sw bm 55 25))
        ⟨[x.w 1288, x.w 1289, x.w 1290, x.w 1291, x.w 1292], []⟩ (x.sw bm 144 nx)
        ([⟨qkeccak, op, kw⟩], kp, (x.bw.getD 15 []).take 64) s' ∧
      op = (x.bw.getD 14 []).take op.length ∧ kp = ((x.bw.getD 14 []).drop qkeccakVarsCap).take kp.length ∧
      qkeccakVarsCap + kp.length ≤ (vsAllocSz x.p).getD 14 0 := by
  have h78 : (vsAllocSz x.p).getD 14 0 = 78 := rfl
  have hl : (op ++ List.replicate (qkeccakVarsCap - op.length) 0).length = qkeccakVarsCap := by
    simp only [List.length_append, List.length_replicate]; omega
  refine ⟨by rw [hb15]; exact hrun, ?_, ?_, ?_⟩
  · rw [hb14, List.append_assoc, List.take_left' rfl]
  · rw [hb14, List.drop_left' hl, List.take_left' rfl]
  · have h39 : kp.length ≤ 39 := hptl
    rw [h78]; show 39 + kp.length ≤ 78; omega

end

end
end LeanVM.Guest.B1.VsC
