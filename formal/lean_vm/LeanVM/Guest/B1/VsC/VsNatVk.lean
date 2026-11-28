/-
  LeanVM.Guest.B1.VsC.VsNatVk

  The Keccak reduction's run at the honest context: the guest's start sponge and stream words are the native
  ones.
-/

module

public import LeanVM.Guest.B1.VsC.VsNatTail
public import LeanVM.Guest.B1.VsC.VsNatLk

/-!
# `verify_keccak`'s run at the honest context

`packed_message`'s returns `w 1288 … w 1292` (the honest rule `ret (1287 + j) = natPm[j]`) are the capacity of
the link's end sponge squeezed once (`vkStart_nat`), and the stream's words from the packed message's cursor
`natBm` are the native message, then the native words past it (`sw_nat`). So `natTail`'s Keccak run is the
run `D3.Ok.hrun` asks, at `bm = natBm`, `nx` the run's word count, on the native point and lanes
(`VsCtx.hrun_nat`).
-/

namespace LeanVM.Guest.B1.VsC

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Memory LeanVM.Guest.B1
open LeanVM.Guest.Complete LeanVM.Guest.B1.Fwd LeanVM.Guest.B1.Link LeanVM.Node LeanVM.Protocol
open LeanVM.Protocol.Verifier LeanVM.Protocol.Compile LeanVM.Protocol.KeccakHash LeanVM.Protocol.Link

@[expose] public section

section
variable {x : VsCtx} {L : LinkNat}

theorem capOf_len5 (S : KeccakState) : (capOf S).length = 5 := rfl

theorem list5_cons (a : E) : ∀ (l : List E), l.length = 5 →
    [(a :: l).getD 1 0, (a :: l).getD 2 0, (a :: l).getD 3 0, (a :: l).getD 4 0, (a :: l).getD 5 0] = l
  | [_, _, _, _, _], _ => rfl
  | [], h | [_], h | [_, _], h | [_, _, _], h | [_, _, _, _], h => by simp at h
  | _ :: _ :: _ :: _ :: _ :: _ :: _, h => by simp at h

/-- `padStream_drop13` with its tail: the native rest, then the padding. -/
theorem padStream_drop13' {s : List E} {lay : Layout} {rest : List E} (hb : L.bits lay ≠ 0)
    (hw : s.drop 12 = L.words lay ++ rest) : ∃ pad,
    (padStream s).drop 13 = L.wsI ++ L.m1 :: (L.wsR ++ (L.wsC ++ (L.msg ++ (rest ++ pad)))) := by
  have hw' : s.drop 12 = L.n0 :: (L.wsI ++ L.m1 :: (L.wsR ++ (L.wsC ++ (L.msg ++ rest)))) := by
    rw [hw]; simp [LinkNat.words, grindWords, hb]
  have hl : 13 ≤ s.length := by
    have := congrArg List.length hw'; simp at this; omega
  refine ⟨List.replicate (chunksOf s.length * 256 - s.length) 0, ?_⟩
  have e : s.drop 13 = (s.drop 12).drop 1 := by rw [List.drop_drop]
  unfold padStream
  rw [List.drop_append_of_le_length hl, e, hw']
  simp

/-- **The stream from the packed message's cursor**: the native message, then the native words past it. -/
theorem VsCtx.sw_nat {rest : List E} (hb : L.bits x.lay ≠ 0) (hw : x.c.proof.stream.drop 12 = L.words x.lay ++ rest)
    (hb18 : x.bw.getD 18 [] = padStream x.c.proof.stream) (hm : L.msg.length = 144) :
    ((x.bw.getD 18 []).drop (x.natBm L - x.base 18)).take 144 = L.msg ∧
      ∀ n ≤ rest.length, x.sw (x.natBm L) 144 n = rest.take n := by
  obtain ⟨pad, hd⟩ := padStream_drop13' hb hw
  have e : x.natBm L - x.base 18 = 13 + (L.wsI.length + 1 + L.wsR.length + L.wsC.length) := by
    simp only [VsCtx.natBm, VsCtx.natB772, VsCtx.sI]; omega
  have hD : (x.bw.getD 18 []).drop (x.natBm L - x.base 18) = L.msg ++ (rest ++ pad) := by
    rw [e, hb18, ← List.drop_drop, hd,
      show L.wsI ++ L.m1 :: (L.wsR ++ (L.wsC ++ (L.msg ++ (rest ++ pad)))) =
        (L.wsI ++ L.m1 :: (L.wsR ++ L.wsC)) ++ (L.msg ++ (rest ++ pad)) by simp,
      List.drop_left' (by simp; omega)]
  refine ⟨?_, fun n hn => ?_⟩
  · rw [hD]
    exact List.take_left' hm
  · simp only [VsCtx.sw]
    rw [← List.drop_drop, hD, List.drop_left' hm, List.take_append_of_le_length hn]

/-- **The pointer columns' last cells**: their first five are the link's end capacity. -/
theorem VsCtx.natLC_cap (hq : linkQVars x.lay ≠ 0) :
    (chainLast ⟨[], 0, 0⟩ (x.natLC L)).cells.take 5 = (L.endC x.lay x.nF).cap := by
  have hne : x.natLC L ≠ [] := natChain_ne hq _ _
  have e1 : chainLast ⟨[], 0, 0⟩ (x.natLC L) = chainLast ⟨(L.endR x.lay x.nF).cap,
      (chainLast ⟨[], 0, 0⟩ (x.natLR L)).cur, (chainLast ⟨[], 0, 0⟩ (x.natLR L)).cl⟩ (x.natLC L) :=
    chainLast_ne hne _ _
  have e2 := (natChain_fst_cap L.ntC (grindingBits (L.ntC + 1)) (linkQVars x.lay) (L.endR x.lay x.nF).cap
    (chainLast ⟨[], 0, 0⟩ (x.natLR L)).cur (chainLast ⟨[], 0, 0⟩ (x.natLR L)).cl 0 (L.endR x.lay x.nF).cl L.wsC).2
  have hcap : (chainLast ⟨[], 0, 0⟩ (x.natLC L)).cap = (L.endC x.lay x.nF).cap := by
    rw [e1]; exact e2
  have hl : (chainLast ⟨[], 0, 0⟩ (x.natLC L)).cap.length = 5 := natChain_last_cap hq _ _ _
  simp only [RSt.cells]
  rw [List.take_left' hl, hcap]

/-- **`verify_keccak`'s start sponge is the native one**: `packed_message`'s returns past its challenge are the
link's end sponge's capacity after one squeeze. -/
theorem VsCtx.vkStart_nat {rest : List E} (hret : CausalRule x.ret) (hb : L.bits x.lay ≠ 0)
    (hq : linkQVars x.lay ≠ 0) (hw : x.c.proof.stream.drop 12 = L.words x.lay ++ rest)
    (hb18 : x.bw.getD 18 [] = padStream x.c.proof.stream) (hm : L.msg.length = 144)
    (r1287 : ∀ j < 6, ∀ σ, x.ret (1287 + j) σ = (x.natPm L).getD j 0) :
    [x.w 1288, x.w 1289, x.w 1290, x.w 1291, x.w 1292] = (L.F4 x.lay x.nF).squeeze.2.cap := by
  have ha : x.args.length = 6 := rfl
  have e1 : x.w 1288 = _ := vsW_retC ha hret (i := 1287 + 1) (by decide) (r1287 1 (by norm_num))
  have e2 : x.w 1289 = _ := vsW_retC ha hret (i := 1287 + 2) (by decide) (r1287 2 (by norm_num))
  have e3 : x.w 1290 = _ := vsW_retC ha hret (i := 1287 + 3) (by decide) (r1287 3 (by norm_num))
  have e4 : x.w 1291 = _ := vsW_retC ha hret (i := 1287 + 4) (by decide) (r1287 4 (by norm_num))
  have e5 : x.w 1292 = _ := vsW_retC ha hret (i := 1287 + 5) (by decide) (r1287 5 (by norm_num))
  have hxm : ((x.bw.getD 18 []).drop (x.natBm L - x.base 18)).take 144 = L.msg := (x.sw_nat hb hw hb18 hm).1
  have hpm : x.natPm L = (L.F4 x.lay x.nF).squeeze.1 :: (L.F4 x.lay x.nF).squeeze.2.cap := by
    unfold VsCtx.natPm pmRets LinkNat.F4
    rw [hxm, x.natLC_cap hq]
  have hl : (L.F4 x.lay x.nF).squeeze.2.cap.length = 5 := capOf_len5 _
  rw [e1, e2, e3, e4, e5, hpm]
  exact list5_cons _ _ hl

/-- **`natTail`'s Keccak run at the honest context**: from `packed_message`'s returns, on the stream's words
past the packed message. -/
theorem VsCtx.hrun_nat {rest xs rest' : List E} {n : E} {inst lanes : List E}
    {res : List ColumnClaim × List E × List E} {s' : Fs} (hret : CausalRule x.ret) (hb : L.bits x.lay ≠ 0)
    (hq : linkQVars x.lay ≠ 0) (hw : x.c.proof.stream.drop 12 = L.words x.lay ++ rest)
    (hb18 : x.bw.getD 18 [] = padStream x.c.proof.stream) (hm : L.msg.length = 144)
    (r1287 : ∀ j < 6, ∀ σ, x.ret (1287 + j) σ = (x.natPm L).getD j 0) (hr : rest = xs ++ n :: rest')
    (hrun : RunsTo (verifyKeccak (x.lay.tableLogHeights.getD opKeccak 0) inst lanes) (L.F4 x.lay x.nF).squeeze.2
      xs res s') :
    RunsTo (verifyKeccak (x.hgS 5) inst lanes) ⟨[x.w 1288, x.w 1289, x.w 1290, x.w 1291, x.w 1292], []⟩
      (x.sw (x.natBm L) 144 xs.length) res s' := by
  have hs : x.sw (x.natBm L) 144 xs.length = xs := by
    rw [(x.sw_nat hb hw hb18 hm).2 _ (by rw [hr]; simp), hr, List.take_left' rfl]
  rw [x.vkStart_nat hret hb hq hw hb18 hm r1287, hs]
  exact hrun

end

end
end LeanVM.Guest.B1.VsC
