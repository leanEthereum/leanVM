/-
  LeanVM.Guest.B1.VsC.VsNatLk

  The link's honest data `Lk2` at the honest context, from the native link verifier's values.
-/

module

public import LeanVM.Guest.B1.VsC.VsNatLink
public import LeanVM.Guest.B1.VsC.VsOrcPh711
public import LeanVM.Guest.B1.VsC.VsOrcPh1
public import LeanVM.Guest.B1.VsC.KLBlock
public import LeanVM.Guest.B1.VsC.VsNatFs

/-!
# The link's honest data, natively

On an accepted child, `natChildLink` gives the native link's reads `L : LinkNat` past the stream's first `12`
words. The honest context's link data `Lk2` is built from it: the index side's chain `natLI` from the cursor
`ptrAt (base 18 + 13)` (the stream's word `13`, past the link grind's nonce) and the guest's claim `clI`, the
row side's `natLR` past `m1`, the pointer columns' `natLC`, the packed message at `natBm`.

**`lk2Ok_nat`**: `Lk2.Ok` from three guest-side equations, `g1` (`squeeze_packed`'s returns are the native
capacity after the packed draws), `g2` (the `KECCAK` of window `13` writes the native capacity after `m1`), `g3`
(`opening_message`'s cursor is the stream's word `13`), and the buffers' and returns' honest choices.
-/

namespace LeanVM.Guest.B1.VsC

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Memory LeanVM.Guest.B1
open LeanVM.Guest.Complete LeanVM.Guest.B1.Fwd LeanVM.Guest.B1.Link LeanVM.Node LeanVM.Protocol
open LeanVM.Protocol.Verifier LeanVM.Protocol.Compile LeanVM.Protocol.KeccakHash LeanVM.Protocol.Link

@[expose] public section

/-! ## Native chains -/

theorem natStep_cap (nt bits : ℕ) (st : RSt) (ws : List E) : (natStep nt bits st ws).2.cap.length = 5 := by
  show ((natRoundFs nt st ws).grindSqueeze bits (ws.getD (nt + 1) 0)).2.cap.length = 5
  unfold Fs.grindSqueeze Fs.squeeze
  split <;> simp [capOf]

theorem chainLast_cons' (a : RSt) (p : E × RSt) (l : List (E × RSt)) : chainLast a (p :: l) = chainLast p.2 l := rfl

/-- A nonempty chain's last capacity has five cells. -/
theorem natChain_last_cap0 (nt bits k : ℕ) : ∀ (a st : RSt) (ws : List E),
    (chainLast a (natChain nt bits (k + 1) st ws)).cap.length = 5 := by
  induction k with
  | zero => intro a st ws; simp only [natChain, chainLast]; exact natStep_cap nt bits st ws
  | succ k ih =>
    intro a st ws
    rw [show natChain nt bits (k + 1 + 1) st ws = natStep nt bits st ws ::
      natChain nt bits (k + 1) (natStep nt bits st ws).2 (ws.drop (natRoundLen nt bits)) from rfl, chainLast_cons']
    exact ih _ _ _

theorem natChain_last_cap {nt bits k : ℕ} (hk : k ≠ 0) (a st : RSt) (ws : List E) :
    (chainLast a (natChain nt bits k st ws)).cap.length = 5 := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk
  exact natChain_last_cap0 nt bits k a st ws

theorem natChain_ne {nt bits k : ℕ} (hk : k ≠ 0) (st : RSt) (ws : List E) : natChain nt bits k st ws ≠ [] := by
  intro h
  have := natChain_length nt bits k st ws
  rw [h] at this
  exact hk this.symm

/-- A list of five, by its entries. -/
theorem list5 {l : List E} (h : l.length = 5) : l = [l.getD 0 0, l.getD 1 0, l.getD 2 0, l.getD 3 0, l.getD 4 0] := by
  match l, h with
  | [a, b, c, d, e], _ => rfl

theorem cells_getD_cap {st : RSt} (h : st.cap.length = 5) {j : ℕ} (hj : j < 5) :
    st.cells.getD j 0 = st.cap.getD j 0 := by
  simp only [RSt.cells, List.getD_eq_getElem?_getD]
  rw [List.getElem?_append_left (by omega)]

theorem cells_getD_5 {st : RSt} (h : st.cap.length = 5) : st.cells.getD 5 0 = st.cur := by
  simp [RSt.cells, List.getD_eq_getElem?_getD, h]

theorem cells_getD_6 {st : RSt} (h : st.cap.length = 5) : st.cells.getD 6 0 = st.cl := by
  simp [RSt.cells, List.getD_eq_getElem?_getD, h]

theorem cells_length {st : RSt} (h : st.cap.length = 5) : st.cells.length = 7 := by
  simp [RSt.cells, h]

/-- The sponge after squeezes from an empty queue has an empty queue. -/
theorem squeezeN_emp : ∀ (n : ℕ) (c : List E), ((⟨c, []⟩ : Fs).squeezeN n).2 = ⟨((⟨c, []⟩ : Fs).squeezeN n).2.cap, []⟩
  | 0, _ => rfl
  | n + 1, c => squeezeN_emp n (capOf (Fs.perm ⟨c, []⟩))

theorem grindingBits_ne {n : ℕ} (h : 9 ≤ n) : grindingBits n ≠ 0 := by
  have : 3 ≤ Nat.log2 (n - 1) := (Nat.le_log2 (by omega)).2 (show 2 ^ 3 ≤ n - 1 by norm_num; omega)
  have e : (128 - securityBits) = 3 := rfl
  unfold grindingBits
  split <;> omega

theorem pmRets_length (xm f : List E) : (pmRets xm f).length = 6 := by
  simp [pmRets, Fs.squeeze, capOf]

/-! ## The native objects at the context -/

namespace VsCtx

variable (x : VsCtx) (L : LinkNat)

/-- The link's start sponge: `natF3` at the announced stack. -/
noncomputable def nF : Fs := natF3 x.seed x.c x.lay.stackLog

/-- The index side's first word: the stream's word `13`. -/
def sI : ℕ := x.base 18 + 13

/-- The index side's claim, from the guest's `state_ends` returns (`Ret2`'s `752`, `753`) and the opening's words
`6`, `7`. -/
noncomputable def clI : E := lrClaim (prodE (x.zsS.map (1 + ·))) (Link.endsProd ((x.bw.getD 2 []).take x.wdS) x.zsS)
  ((x.bw.getD 4 []).getD 6 0) ((x.bw.getD 4 []).getD 7 0)

/-- **The index side's honest chain.** -/
noncomputable def natLI : List (E × RSt) := L.chainI x.lay x.nF (ptrAt x.sI) x.clI

/-- The index side's end cursor: `m1`'s word. -/
def natB772 : ℕ := x.sI + L.wsI.length

/-- **The row side's honest chain**, past `m1`, from the index side's last claim. -/
noncomputable def natLR : List (E × RSt) :=
  L.chainR x.lay x.nF (ptrAt (x.natB772 L + 1)) (chainLast ⟨[], 0, 0⟩ (x.natLI L)).cl

/-- **The pointer columns' honest chain**, from the row side's last cursor and claim. -/
noncomputable def natLC : List (E × RSt) :=
  L.chainC x.lay x.nF (chainLast ⟨[], 0, 0⟩ (x.natLR L)).cur (chainLast ⟨[], 0, 0⟩ (x.natLR L)).cl

/-- The packed message's first word. -/
def natBm : ℕ := x.natB772 L + 1 + L.wsR.length + L.wsC.length

/-- `packed_message`'s honest returns. -/
noncomputable def natPm : List E :=
  pmRets (((x.bw.getD 18 []).drop (x.natBm L - x.base 18)).take 144) ((chainLast ⟨[], 0, 0⟩ (x.natLC L)).cells.take 5)

/-- **The link's honest data.** -/
noncomputable def natLk2 : Lk2 :=
  ⟨x.natLI L, x.sI, L.wsI.length, x.natB772 L, x.natLR L, x.natLC L, L.wsR.length, L.wsC.length, x.natBm L⟩

open LeanVM.Prover.Exec (allocBase) in
/-- **The link's two non-leaf calls at their pinned ends** (`Lk2.Ok`'s `crd`, `crs`, vspin's), on the link's data
`L'`: `VsHonEx` gives them where it chooses `x.ec 7` and `x.ec 9`. -/
def LkCalls (L' : Lk2) : Prop :=
  LrCall B2C.fs x.al B2C.cert 17 (x.w 680) (x.w 681) (x.w 682) (x.w 683) (x.w 684) (x.w 580)
      (lrClaim (x.w 752) (x.w 753) ((x.bw.getD 4 []).getD 6 0) ((x.bw.getD 4 []).getD 7 0)) (ptrAt (x.base 6))
      (ptrAt x.qt * word 365917469723852800 0) L'.l L'.nw (ph7Fp B2C.fs x.al x.wdS (x.ec 6)) (x.ec 7) ∧
    LrsCall B2C.fs x.al B2C.cert 17 (chunkCount x.wdS) (x.σ0 (.n 790)) (x.σ0 (.n 791)) (x.σ0 (.n 792))
      (x.σ0 (.n 793)) (x.σ0 (.n 794)) (ptrAt (L'.b772 + 1)) (x.w 773) (ptrAt (x.base 9)) (ptrAt (x.base 10))
      (ptrAt x.qt * word 365917469723852800 0) L'.l1 L'.l2 L'.nw1 L'.nw2
      (allocBase (x.al (lrsNames.getD (chunkCount x.wdS - 6) "")) (ph8End B2C.fs x.al x.wdS (x.ec 7))) (x.ec 9)

end VsCtx

/-! ## The bridge -/

section
variable {x : VsCtx} {L : LinkNat}

theorem VsCtx.lay_of {layout : Layout} {r : ℕ}
    (h : announcedLayoutAndRate guestBytecode x.c.proof.stream = some (layout, r)) : x.lay = layout := by
  simp [VsCtx.lay, h]

theorem widthOf_eq_linkWidth (layout : Layout) : widthOf layout = linkWidth layout := rfl

theorem hMax_eq_linkRows (layout : Layout) : hMax layout = linkRows layout := rfl

/-- The stream's words past the link grind's nonce, in the padded stream. -/
theorem padStream_drop13 {s : List E} {L : LinkNat} {lay : Layout} {rest : List E} (hb : L.bits lay ≠ 0)
    (hw : s.drop 12 = L.words lay ++ rest) :
    ∃ tl, (padStream s).drop 13 = L.wsI ++ L.m1 :: (L.wsR ++ (L.wsC ++ (L.msg ++ tl))) := by
  have hw' : s.drop 12 = L.n0 :: (L.wsI ++ L.m1 :: (L.wsR ++ (L.wsC ++ (L.msg ++ rest)))) := by
    rw [hw]; simp [LinkNat.words, grindWords, hb]
  have hl : 13 ≤ s.length := by
    have := congrArg List.length hw'; simp at this; omega
  refine ⟨rest ++ List.replicate (chunksOf s.length * 256 - s.length) 0, ?_⟩
  have e : s.drop 13 = (s.drop 12).drop 1 := by rw [List.drop_drop]
  unfold padStream
  rw [List.drop_append_of_le_length hl, e, hw']
  simp

/-- **The link's honest data is honest**, from the guest-side equations and the honest choices. -/
theorem lk2Ok_nat {layout : Layout} {r : ℕ} {link : LinkEnd} {rest : List E}
    (hann : announcedLayoutAndRate guestBytecode x.c.proof.stream = some (layout, r))
    (hN : FrontNum (chunksOf x.c.proof.stream.length) r layout.logMemory (hMax layout) (widthOf layout)
      (flagOf layout) (padStream x.c.proof.stream) (fun t => layout.tableLogHeights.getD t 0)
      (fun t => layout.tableRows.getD t 0))
    (hw : x.c.proof.stream.drop 12 = L.words x.lay ++ rest)
    (hL : L.Ok x.lay x.nF x.c.freshClaim link)
    (hb18 : x.bw.getD 18 [] = padStream x.c.proof.stream)
    (hrd : ∀ rd, HoldsWords rd x.Wo → ReadsAt rd (ptrAt (x.base 18)) (x.bw.getD 18 []))
    (g1 : [x.w 680, x.w 681, x.w 682, x.w 683, x.w 684] = L.cap2 x.lay x.nF)
    (g2 : [x.σ0 (.n 790), x.σ0 (.n 791), x.σ0 (.n 792), x.σ0 (.n 793), x.σ0 (.n 794)] = L.cap4 x.lay x.nF)
    (g3 : x.w 580 = ptrAt x.sI)
    (gcl : lrClaim (x.w 752) (x.w 753) ((x.bw.getD 4 []).getD 6 0) ((x.bw.getD 4 []).getD 7 0) = x.clI)
    (g773 : x.w 773 = (chainLast ⟨[], 0, 0⟩ (x.natLI L)).cl)
    (h6 : (x.bw.getD 6 []).take x.wdS = L.r x.lay x.nF)
    (h9 : (x.bw.getD 9 []).take x.nS = L.chi x.lay x.nF)
    (h10 : x.bw.getD 10 [] = L.qPoint x.lay x.nF)
    (r767 : ∀ j < 7, ∀ σ, x.ret (767 + j) σ = (chainLast ⟨[], 0, 0⟩ (x.natLI L)).cells.getD j 0)
    (r1071 : ∀ j < 7, ∀ σ, x.ret (1071 + j) σ = (chainLast ⟨[], 0, 0⟩ (x.natLC L)).cells.getD j 0)
    (r1287 : ∀ j < 6, ∀ σ, x.ret (1287 + j) σ = (x.natPm L).getD j 0)
    (hcalls : x.LkCalls (x.natLk2 L)) :
    (x.natLk2 L).Ok x := by
  have hlay : x.lay = layout := VsCtx.lay_of hann
  have htab : x.lay.tables = tables := by rw [hlay]; exact announced_tables hann
  have hw19 : 19 ≤ x.wdS := by rw [VsCtx.wdS, hlay]; exact hN.hw19
  have hw24 : x.wdS ≤ 24 := by rw [VsCtx.wdS, hlay]; exact hN.hw24
  have hwdE : linkWidth x.lay = x.wdS := rfl
  have hwd : L.chunks.width = x.wdS := by rw [VerifySub.chunks_width hL.chunks, hwdE]
  have hnS : linkRows x.lay = x.nS := rfl
  have hq6 : linkQVars x.lay = 6 := VerifySub.linkQVars_tables htab
  obtain ⟨hntR, hntC, hgR, hgC⟩ := natLink_counts hL.chunks (by rw [hwdE]; exact hw19) (by rw [hwdE]; exact hw24) rfl
  rw [hwdE] at hntR hntC hgR hgC
  have hbits : L.bits x.lay ≠ 0 := grindingBits_ne (le_max_of_le_right (by omega))
  -- the stream
  obtain ⟨tl, htl⟩ := padStream_drop13 hbits hw
  have hlen : (padStream x.c.proof.stream).length = 256 * x.p := hN.hws
  set T := L.wsI ++ L.m1 :: (L.wsR ++ (L.wsC ++ (L.msg ++ tl))) with hT
  have hlT : 13 + T.length = (padStream x.c.proof.stream).length := by
    have h1 := congrArg List.length htl
    rw [List.length_drop] at h1
    have h2 : 1 ≤ T.length := by rw [hT, List.length_append, List.length_cons]; omega
    omega
  have hrT : ∀ rd, HoldsWords rd x.Wo → ReadsAt rd (ptrAt x.sI) T := fun rd hW => by
    have := VsC.readsAt_drop (m := 13) (hrd rd hW)
    rwa [hb18, htl] at this
  have hlI : L.wsI.length = 2 * x.wdS := by rw [hL.lenI, hwd]; simp [natRoundLen]; ring
  have hTl : T.length = L.wsI.length + 1 + L.wsR.length + L.wsC.length + L.msg.length + tl.length := by
    simp [hT]; omega
  have hlM := hL.lenM
  have hb18e : x.base 18 = x.cur + 824 := VsCtx.base_c 18 824 (by norm_num) (by decide)
  have hsI : x.sI = x.base 18 + 13 := rfl
  have hb772 : x.natB772 L = x.sI + L.wsI.length := rfl
  have hbm : x.natBm L = x.natB772 L + 1 + L.wsR.length + L.wsC.length := rfl
  -- the pieces of the stream
  have rdI : ∀ rd, HoldsWords rd x.Wo → ReadsAt rd (ptrAt x.sI) L.wsI := fun rd hW => by
    have := readsAt_takeV (hrT rd hW) L.wsI.length
    rwa [hT, List.take_left' rfl] at this
  have rdR : ∀ rd, HoldsWords rd x.Wo → ReadsAt rd (ptrAt (x.natB772 L + 1)) L.wsR := fun rd hW => by
    have := readsAt_slice (hrT rd hW) (L.wsI.length + 1) L.wsR.length
    have e : (T.drop (L.wsI.length + 1)).take L.wsR.length = L.wsR := by
      rw [hT, show L.wsI ++ L.m1 :: (L.wsR ++ (L.wsC ++ (L.msg ++ tl))) =
        (L.wsI ++ [L.m1]) ++ (L.wsR ++ (L.wsC ++ (L.msg ++ tl))) by simp,
        List.drop_left' (by simp), List.take_left' rfl]
    rwa [e, ← Nat.add_assoc, ← hb772] at this
  have rdC : ∀ rd, HoldsWords rd x.Wo →
      ReadsAt rd (ptrAt (x.natB772 L + 1 + L.wsR.length)) L.wsC := fun rd hW => by
    have := readsAt_slice (hrT rd hW) (L.wsI.length + 1 + L.wsR.length) L.wsC.length
    have e : (T.drop (L.wsI.length + 1 + L.wsR.length)).take L.wsC.length = L.wsC := by
      rw [hT, show L.wsI ++ L.m1 :: (L.wsR ++ (L.wsC ++ (L.msg ++ tl))) =
        (L.wsI ++ [L.m1] ++ L.wsR) ++ (L.wsC ++ (L.msg ++ tl)) by simp,
        List.drop_left' (by simp; omega), List.take_left' rfl]
    rwa [e, ← Nat.add_assoc, ← Nat.add_assoc, ← hb772] at this
  -- the index side
  have hne1 : x.natLI L ≠ [] := natChain_ne (by omega) _ _
  have e7 : ph7St0 x.w (x.bw.getD 4 []) = ⟨L.cap2 x.lay x.nF, ptrAt x.sI, x.clI⟩ := by
    unfold ph7St0; rw [g1, g3, gcl]
  have hcI : (chainLast ⟨L.cap2 x.lay x.nF, ptrAt x.sI, x.clI⟩ (x.natLI L)).cur =
      ptrAt (x.natB772 L) := by
    rw [VsCtx.natLI, LinkNat.chainI, natChain_cur, ← hL.lenI, ptrAt_add]
    rfl
  have hcapI : (chainLast ⟨[], 0, 0⟩ (x.natLI L)).cap.length = 5 :=
    natChain_last_cap (by omega) _ _ _
  have eI0 : chainLast ⟨[], 0, 0⟩ (x.natLI L) = chainLast ⟨L.cap2 x.lay x.nF, ptrAt x.sI, x.clI⟩ (x.natLI L) :=
    chainLast_ne hne1 _ _
  -- the row side
  have hR0 : linkRows x.lay ≠ 0 := by
    have h5 : 9 ≤ layout.tableLogHeights.getD 5 0 := hN.h9
    have h55 : layout.tableLogHeights.getD 5 0 ≤ hMax layout := hN.hht 5 (by norm_num)
    rw [hlay, ← hMax_eq_linkRows]; omega
  have hne2 : x.natLR L ≠ [] := natChain_ne hR0 _ _
  have e9 : ph9St0 x.σ0 x.w (x.natB772 L) = ⟨L.cap4 x.lay x.nF, ptrAt (x.natB772 L + 1), (chainLast ⟨[], 0, 0⟩ (x.natLI L)).cl⟩ := by
    unfold ph9St0; rw [g2, g773]
  have hcR : (chainLast ⟨L.cap4 x.lay x.nF, ptrAt (x.natB772 L + 1), (chainLast ⟨[], 0, 0⟩ (x.natLI L)).cl⟩ (x.natLR L)).cur =
      ptrAt (x.natB772 L + 1 + L.wsR.length) := by
    rw [VsCtx.natLR, LinkNat.chainR, natChain_cur, ← hL.lenR, ptrAt_add]
  have eR0 : chainLast ⟨[], 0, 0⟩ (x.natLR L) =
      chainLast ⟨L.cap4 x.lay x.nF, ptrAt (x.natB772 L + 1), (chainLast ⟨[], 0, 0⟩ (x.natLI L)).cl⟩ (x.natLR L) := chainLast_ne hne2 _ _
  have hcapR : (chainLast ⟨L.cap4 x.lay x.nF, ptrAt (x.natB772 L + 1), (chainLast ⟨[], 0, 0⟩ (x.natLI L)).cl⟩ (x.natLR L)).cap =
      (L.endR x.lay x.nF).cap :=
    (natChain_fst_cap _ _ _ _ _ _ _ _ _).2
  have eRL : chainLast ⟨L.cap4 x.lay x.nF, ptrAt (x.natB772 L + 1), (chainLast ⟨[], 0, 0⟩ (x.natLI L)).cl⟩ (x.natLR L) =
      ⟨(L.endR x.lay x.nF).cap, (chainLast ⟨[], 0, 0⟩ (x.natLR L)).cur, (chainLast ⟨[], 0, 0⟩ (x.natLR L)).cl⟩ := by
    rw [eR0, ← hcapR]
  -- the pointer columns
  have hne3 : x.natLC L ≠ [] := natChain_ne (by omega) _ _
  have hcC : (chainLast ⟨[], 0, 0⟩ (x.natLC L)).cur = ptrAt (x.natBm L) := by
    rw [VsCtx.natLC, LinkNat.chainC, chainLast_ne (natChain_ne (by omega) _ _) _
      ⟨(L.endR x.lay x.nF).cap, (chainLast ⟨[], 0, 0⟩ (x.natLR L)).cur, (chainLast ⟨[], 0, 0⟩ (x.natLR L)).cl⟩,
      natChain_cur, ← hL.lenC]
    rw [eR0, hcR, ptrAt_add, hbm]
  have hcapC : (chainLast ⟨[], 0, 0⟩ (x.natLC L)).cap.length = 5 :=
    natChain_last_cap (by omega) _ _ _
  refine ⟨?hl, g3, ?hsIn, ?hcur, cells_length hcapI, ?hch, ?hc, r767, ?h772, ?hbIn, ?hl1, ?hl2, ?hcur1, ?hcur2,
    cells_length hcapC, ?hch1, ?hch2, ?hc12, r1071, ?hbm, ?hbmIn, pmRets_length _ _, r1287, hcalls.1, hcalls.2⟩
  · simp only [VsCtx.natLk2, VsCtx.natLI, LinkNat.chainI, natChain_length, hwd]
  · simp only [VsCtx.natLk2]; rw [hsI]; omega
  · simp only [VsCtx.natLk2]
    rw [e7, hcI, g3, ptrAt_add]
    rfl
  · simp only [VsCtx.natLk2, VsCtx.rsS, h6, VsCtx.natLI, LinkNat.r, LinkNat.chainI]
    exact (natChain_fst_cap _ _ _ _ _ _ _ _ _).1
  · intro rd hW _
    simp only [VsCtx.natLk2]
    rw [e7]
    exact hL.hI _ _ rd (rdI rd hW)
  · simp only [VsCtx.natLk2]
    rw [cells_getD_5 hcapI, eI0, hcI]
  · simp only [VsCtx.natLk2]; rw [hb772, hsI]; omega
  · simp only [VsCtx.natLk2, VsCtx.natLR, LinkNat.chainR, natChain_length]; rfl
  · simp only [VsCtx.natLk2, VsCtx.natLC, LinkNat.chainC, natChain_length, hq6]
  · simp only [VsCtx.natLk2]
    rw [e9, hcR, ptrAt_add]
  · simp only [VsCtx.natLk2]
    rw [chainLast_ne hne3 _ ⟨[], 0, 0⟩, hcC, e9, hcR, ptrAt_add, hbm]
  · simp only [VsCtx.natLk2, VsCtx.as15S, h9, VsCtx.natLR, LinkNat.chi, LinkNat.chainR]
    exact (natChain_fst_cap _ _ _ _ _ _ _ _ _).1
  · simp only [VsCtx.natLk2, h10, VsCtx.natLC, LinkNat.qPoint, LinkNat.chainC]
    exact (natChain_fst_cap _ _ _ _ _ _ _ _ _).1
  · intro rd hW _
    simp only [VsCtx.natLk2]
    refine ⟨?_, ?_⟩
    · rw [e9, ← hgR, ← hntR]
      exact hL.hR _ _ rd (rdR rd hW)
    · rw [e9, eRL, ← hgC, ← hntC]
      refine hL.hC _ _ rd ?_
      rw [eR0, hcR]
      exact rdC rd hW
  · simp only [VsCtx.natLk2]
    rw [cells_getD_5 hcapC, hcC]
  · simp only [VsCtx.natLk2]; rw [hbm, hb772, hsI]; omega

end

/-! ## A guest `KECCAK` atom is the native permutation -/

section
variable {rd0 : Reader} {w : ℕ → E} {args : List E}

/-- **A `KECCAK` of `vsC` on the forward valuation** writes the cells of `s.perm` when it reads `s`'s cells
(the waiting scalars' rate cells, zeros, the capacity). -/
theorem vsC_keccak_fs (ha : args.length = 6) {ins outs : List V} {s : Fs}
    (hm : Stmt.atom (.keccak ins outs false false) ∈ vsC) (hs : s.pend.length ≤ 4)
    (hins : ins.map (vsVal rd0 w args) = pendCells s.pend ++ List.replicate (8 - 2 * s.pend.length) 0 ++ s.cap)
    (ho : outs.length = 13) :
    cells13 (outs.map (vsVal rd0 w args)) = cellsOfState s.perm false := by
  have hg : Good rd0 (storesOf 482 vsC) w (vsVal rd0 w args) (.keccak ins outs false false) :=
    vsVal_goodC (rd := rd0) (w := w) ha _ hm
  exact keccakA_fs (VerifySub.KL.keccakA_complete hg) hs hins ho

/-- **A `KECCAK` of `vsA` on the forward valuation**, as `vsC_keccak_fs`. -/
theorem vsA_keccak_fs (ha : args.length = 6) {ins outs : List V} {s : Fs}
    (hm : Stmt.atom (.keccak ins outs false false) ∈ vsA) (hs : s.pend.length ≤ 4)
    (hins : ins.map (vsVal rd0 w args) = pendCells s.pend ++ List.replicate (8 - 2 * s.pend.length) 0 ++ s.cap)
    (ho : outs.length = 13) :
    cells13 (outs.map (vsVal rd0 w args)) = cellsOfState s.perm false :=
  keccakA_fs (rd := rd0) (VerifySub.KL.keccakA_complete (vsA_good (rd0 := rd0) (w := w) ha hm rfl)) hs hins ho

end

/-! ## The context's stream buffer, from the placement and the sizes -/

section
variable {x : VsCtx}

theorem VsCtx.p_le32 (hok : x.Ok) : x.p ≤ 32 := by
  obtain ⟨_, _, _, _, hN⟩ := frontNum_of_child hok.child
  exact hN.hp

theorem VsCtx.bwlen (hbw : x.bw.map List.length = vsAllocSz x.p) : x.bw.length = 24 := by
  have := congrArg List.length hbw
  simpa [vsAllocSz_lengthF] using this

theorem VsCtx.lenbw (hbw : x.bw.map List.length = vsAllocSz x.p) {j : ℕ} (hj : j < 24) :
    (x.bw.getD j []).length = (vsAllocSz x.p).getD j 0 := by
  have hl : j < x.bw.length := by rw [(VsCtx.bwlen (x := x)) hbw]; exact hj
  rw [List.getD_eq_getElem _ _ hl, List.getD_eq_getElem _ _ (by rw [vsAllocSz_lengthF]; exact hj)]
  have := List.getElem_of_eq hbw (by simpa using hl)
  simpa using this

/-- Buffer `j`'s run among the node's words, off `.n 19`. -/
theorem VsCtx.memWo (hbw : x.bw.map List.length = vsAllocSz x.p) {j : ℕ} (hj : j < 24) (h13 : j ≠ 13) :
    (x.base j, x.bw.getD j []) ∈ x.Wo := by
  have e : (x.bw.set 13 (x.cells19.map Prod.snd)).getD j [] = x.bw.getD j [] := by
    simp [List.getD_eq_getElem?_getD, List.getElem?_set_ne (Ne.symm h13)]
  unfold VsCtx.Wo
  rw [← e]
  exact mem_zip_getD (by rw [bases_lengthF, vsAllocSz_lengthF]; exact hj) (by simp [(VsCtx.bwlen (x := x)) hbw]; exact hj)

theorem VsCtx.holdsRd1 (hok : x.Ok) (hbw : x.bw.map List.length = vsAllocSz x.p) :
    HoldsWords x.rd1 (vsRuns x.cur x.bw) := by
  have hc := hok.hcur
  have hs : (x.bw.map List.length).sum ≤ 2 ^ 14 := by
    rw [hbw]
    have hp := (VsCtx.p_le32 (x := x)) hok
    simp only [vsAllocSz, vsSz0, List.cons_append, List.nil_append, List.sum_cons, List.sum_nil]
    omega
  have h := holdsWords_rdW (bases_zip_pairwise x.cur x.bw) fun q hq => by
    have := bases_zip_in x.cur x.bw q hq; omega
  show HoldsWords (vsRd1 x.rdP x.cur x.bw x.ex) _
  unfold vsRd1
  exact holdsWords_or (rd' := fun A => (exAt x.ex A).or (some ((x.rdP A).getD 0))) h

set_option maxHeartbeats 1000000 in
/-- **`rd0` reads the stream's buffer.** -/
theorem VsCtx.reads18 (hok : x.Ok) (hbw : x.bw.map List.length = vsAllocSz x.p) :
    ReadsAt x.rd0 (ptrAt (x.base 18)) (x.bw.getD 18 []) := by
  have hm : (x.base 18, x.bw.getD 18 []) ∈ vsRuns x.cur x.bw := by
    unfold vsRuns VsCtx.base
    rw [hbw]
    exact mem_zip_getD (by rw [bases_lengthF, vsAllocSz_lengthF]; norm_num) (by rw [(VsCtx.bwlen (x := x)) hbw]; norm_num)
  have h1 : ReadsAt x.rd1 (ptrAt (x.base 18)) (x.bw.getD 18 []) := (VsCtx.holdsRd1 (x := x)) hok hbw _ hm
  have hc := hok.hcur
  have hp := (VsCtx.p_le32 (x := x)) hok
  have h13 : x.base 13 = x.cur + 639 := VsCtx.base_c 13 639 (by norm_num) (by decide)
  have h18 : x.base 18 = x.cur + 824 := VsCtx.base_c 18 824 (by norm_num) (by decide)
  have hl := (VsCtx.lenbw (x := x)) hbw (j := 18) (by norm_num)
  have s18 : (vsAllocSz x.p).getD 18 0 = 256 * x.p := rfl
  rw [s18] at hl
  refine readsAt_rdSet (rd := x.rd1) (cells := x.cells19) h1 (by omega) ?_
  intro c hcm
  simp only [VsCtx.cells19, vsCells19, List.mem_map, List.mem_range] at hcm
  obtain ⟨i, hi, rfl⟩ := hcm
  dsimp only
  omega

end

/-! ## The three guest-side equations -/

section
variable {x : VsCtx} {L : LinkNat}

theorem omRets_eq (f0 f1 f2 f3 f4 cur : E) (xs : List E) (nn : E) :
    omRets f0 f1 f2 f3 f4 cur xs nn =
      [cellsOfState (omState [f0, f1, f2, f3, f4] xs (some nn)) false 0,
        cellsOfState (omState [f0, f1, f2, f3, f4] xs (some nn)) false 1,
        cellsOfState (omState [f0, f1, f2, f3, f4] xs (some nn)) false 8,
        cellsOfState (omState [f0, f1, f2, f3, f4] xs (some nn)) false 9,
        cellsOfState (omState [f0, f1, f2, f3, f4] xs (some nn)) false 10,
        cellsOfState (omState [f0, f1, f2, f3, f4] xs (some nn)) false 11,
        cellsOfState (omState [f0, f1, f2, f3, f4] xs (some nn)) false 12, cur * gen ^ (xs.length + 1)] := rfl

/-- **(G3)** `opening_message`'s cursor is the stream's word `13`. -/
theorem VsCtx.g3_of (hfs : VsFsChecks1 x) : x.w 580 = ptrAt x.sI := by
  have h := hfs.hom
  rw [omRets_eq] at h
  simp only [List.cons.injEq] at h
  obtain ⟨-, -, -, -, -, -, -, h580, -⟩ := h
  rw [h580, ptrAt_add]
  rfl

/-- **(G1)** `squeeze_packed`'s returns are the native capacity after the packed draws, once the front's
out-of-domain permutation is the native one (`hood`, the front's bridge). -/
theorem VsCtx.g1_of {rest : List E} (hw : x.c.proof.stream.drop 12 = L.words x.lay ++ rest)
    (htab : x.lay.tables = tables) (hch : Chunks.new (linkWidth x.lay) = some L.chunks) (hbits : L.bits x.lay ≠ 0)
    (hfs : VsFsChecks1 x) (hr1 : x.Ret1)
    (hood : [x.σ0 (.n 507), x.σ0 (.n 508), x.σ0 (.n 509), x.σ0 (.n 510), x.σ0 (.n 511)] =
      capOf (natOodS x.seed x.c)) :
    [x.w 680, x.w 681, x.w 682, x.w 683, x.w 684] = L.cap2 x.lay x.nF := by
  have hw' : x.c.proof.stream.drop 12 = L.n0 :: (L.wsI ++ L.m1 :: (L.wsR ++ (L.wsC ++ (L.msg ++ rest)))) := by
    rw [hw]; simp [LinkNat.words, grindWords, hbits]
  have hl : 13 ≤ x.c.proof.stream.length := by
    have := congrArg List.length hw'; simp at this; omega
  have h11 : (padStream x.c.proof.stream).getD 11 0 = x.c.proof.stream.getD 11 0 := padStream_getDF (by omega)
  have h12 : (padStream x.c.proof.stream).getD 12 0 = L.n0 := by
    rw [padStream_getDF (by omega), show x.c.proof.stream.getD 12 0 = (x.c.proof.stream.drop 12).getD 0 0 by
      simp [List.getD_eq_getElem?_getD], hw']
    rfl
  have hpk : x.pk = pkCount (L.nDrawn x.lay) := by
    unfold VsCtx.pk pkCount LinkNat.nDrawn linkDrawn
    rw [htab, VerifySub.chunks_width hch]
    rfl
  have e1 : (⟨[x.w 566, x.w 567, x.w 568, x.w 569, x.w 570], []⟩ : Fs) =
      ((⟨capOf (natOodS x.seed x.c), []⟩ : Fs).squeezeN (x.lay.stackLog - 1)).2 := by
    rw [hfs.hspf, VsCtx.spf, hood]
    exact (squeezeN_emp _ _).symm
  have hS : omState [x.w 566, x.w 567, x.w 568, x.w 569, x.w 570] [(padStream x.c.proof.stream).getD 11 0]
      (some ((padStream x.c.proof.stream).getD 12 0)) = x.nF.nonceState L.n0 := by
    show (((⟨[x.w 566, x.w 567, x.w 568, x.w 569, x.w 570], []⟩ : Fs).absorbAll _ dsObserve).nonceState _) = _
    rw [e1, h11, h12]
    rfl
  have h := hfs.hom
  rw [omRets_eq, hS] at h
  simp only [List.cons.injEq] at h
  obtain ⟨-, -, h575, h576, h577, h578, h579, -⟩ := h
  rw [hr1.r680, LinkNat.cap2, ← hpk, LinkNat.cap1, Fs.grindSqueeze_pos _ hbits, h575, h576, h577, h578, h579]
  rfl

set_option maxRecDepth 200000 in
theorem vsC13_kAtoms : ([.copy (.n 774) (.n 767), .copy (.n 775) (.n 768), .copy (.n 776) (.n 769),
    .copy (.n 777) (.n 770), .copy (.n 778) (.n 771), .load (.n 779) (.n 772) 0, .copy (.n 780) (.n 779),
    .const (.n 781) (word 0 1),
    .keccak [.n 780, .n 781, .n 25, .n 25, .n 25, .n 26, .n 27, .n 28, .n 774, .n 775, .n 776, .n 777, .n 778]
      [.n 782, .n 783, .n 784, .n 785, .n 786, .n 787, .n 788, .n 789, .n 790, .n 791, .n 792, .n 793, .n 794]
      false false] : List Atom).all (fun a => (atomsOf ((vsC.drop 259).take 11)).contains a) = true := by
  decide +kernel

set_option maxRecDepth 200000 in
theorem vsC13_fresh : vsSL.contains (.load (.n 779) (.n 772) 0) = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
/-- **(G2)** The `KECCAK` of window `13` writes the native capacity after `m1`. -/
theorem VsCtx.g2_of {rest : List E} (hw : x.c.proof.stream.drop 12 = L.words x.lay ++ rest)
    (hbits : L.bits x.lay ≠ 0) (hwd : L.chunks.width ≠ 0) (hlI : L.wsI.length = L.chunks.width * natRoundLen 1 0)
    (hret : CausalRule x.ret) (hb18 : x.bw.getD 18 [] = padStream x.c.proof.stream)
    (hrd0 : ReadsAt x.rd0 (ptrAt (x.base 18)) (x.bw.getD 18 []))
    (r767 : ∀ j < 7, ∀ σ, x.ret (767 + j) σ = (chainLast ⟨[], 0, 0⟩ (x.natLI L)).cells.getD j 0) :
    [x.σ0 (.n 790), x.σ0 (.n 791), x.σ0 (.n 792), x.σ0 (.n 793), x.σ0 (.n 794)] = L.cap4 x.lay x.nF := by
  have ha : x.args.length = 6 := rfl
  have hσ : x.σ0 = vsVal x.rd0 x.w x.args := rfl
  rw [hσ]
  have hg := vsC_atoms_good (rd0 := x.rd0) (w := x.w) ha 259 11
  have hm : ∀ a ∈ ([.copy (.n 774) (.n 767), .copy (.n 775) (.n 768), .copy (.n 776) (.n 769),
      .copy (.n 777) (.n 770), .copy (.n 778) (.n 771), .load (.n 779) (.n 772) 0, .copy (.n 780) (.n 779),
      .const (.n 781) (word 0 1),
      .keccak [.n 780, .n 781, .n 25, .n 25, .n 25, .n 26, .n 27, .n 28, .n 774, .n 775, .n 776, .n 777, .n 778]
        [.n 782, .n 783, .n 784, .n 785, .n 786, .n 787, .n 788, .n 789, .n 790, .n 791, .n 792, .n 793, .n 794]
        false false] : List Atom), Good x.rd0 vsSL x.w (vsVal x.rd0 x.w x.args) a := fun a h =>
    hg a (by simpa using List.all_eq_true.mp vsC13_kAtoms a h)
  set σ := vsVal x.rd0 x.w x.args with hσσ
  have i3 : σ (.n 774) = σ (.n 767) := hm (.copy (.n 774) (.n 767)) (by simp)
  have i4 : σ (.n 775) = σ (.n 768) := hm (.copy (.n 775) (.n 768)) (by simp)
  have i5 : σ (.n 776) = σ (.n 769) := hm (.copy (.n 776) (.n 769)) (by simp)
  have i6 : σ (.n 777) = σ (.n 770) := hm (.copy (.n 777) (.n 770)) (by simp)
  have i7 : σ (.n 778) = σ (.n 771) := hm (.copy (.n 778) (.n 771)) (by simp)
  have i9 : σ (.n 780) = σ (.n 779) := hm (.copy (.n 780) (.n 779)) (by simp)
  have i10 : σ (.n 781) = word 0 1 := hm (.const (.n 781) (word 0 1)) (by simp)
  have z25 : σ (.n 25) = word 0 0 := vsW0_good (a := .const (.n 25) (word 0 0)) ha (by simp [vsW0, vsW0a])
  have z26 : σ (.n 26) = word 0 0 := vsW0_good (a := .const (.n 26) (word 0 0)) ha (by simp [vsW0, vsW0a])
  have z27 : σ (.n 27) = word 0 0 := vsW0_good (a := .const (.n 27) (word 0 0)) ha (by simp [vsW0, vsW0a])
  have z28 : σ (.n 28) = word 0 0 := vsW0_good (a := .const (.n 28) (word 0 0)) ha (by simp [vsW0, vsW0a])
  -- the index side's last state
  have hne : x.natLI L ≠ [] := natChain_ne hwd _ _
  have hcap : (chainLast ⟨[], 0, 0⟩ (x.natLI L)).cap.length = 5 := natChain_last_cap hwd _ _ _
  have hr : ∀ j < 7, σ (.n (767 + j)) = (chainLast ⟨[], 0, 0⟩ (x.natLI L)).cells.getD j 0 := fun j hj => by
    have e1 : σ (.n (767 + j)) = x.w (767 + j) :=
      vsVal_retC (rd0 := x.rd0) (w := x.w) ha vsC12_eq (.n (767 + j)) (by interval_cases j <;> simp)
    rw [e1]
    exact vsW_retC ha hret (by interval_cases j <;> decide) (r767 j hj)
  have hcur : (chainLast ⟨[], 0, 0⟩ (x.natLI L)).cur = ptrAt (x.natB772 L) := by
    rw [chainLast_ne hne _ ⟨L.cap2 x.lay x.nF, ptrAt x.sI, x.clI⟩, VsCtx.natLI, LinkNat.chainI, natChain_cur, ← hlI,
      ptrAt_add]
    rfl
  have e772 : σ (.n 772) = ptrAt (x.natB772 L) := by
    rw [show (772 : ℕ) = 767 + 5 from rfl, hr 5 (by norm_num), cells_getD_5 hcap, hcur]
  -- `m1`
  obtain ⟨tl, htl⟩ := padStream_drop13 hbits hw
  have hT0 : ReadsAt x.rd0 (ptrAt x.sI) (L.wsI ++ L.m1 :: (L.wsR ++ (L.wsC ++ (L.msg ++ tl)))) := by
    have := VsC.readsAt_drop (m := 13) hrd0
    rwa [hb18, htl] at this
  have hm1 : ReadsAt x.rd0 (ptrAt (x.natB772 L)) [L.m1] := by
    have := readsAt_slice hT0 L.wsI.length 1
    rwa [List.drop_left' rfl, List.take_succ_cons, List.take_zero] at this
  have i8 : σ (.n 779) = L.m1 :=
    good_load_get? (by intro h; have fr := vsC13_fresh; rw [List.contains_iff_mem.mpr h] at fr; exact absurd fr (by decide))
      (hm (.load (.n 779) (.n 772) 0) (by simp)) e772 hm1 rfl
  -- the permutation
  clear_value σ
  set s1 : Fs := ⟨[σ (.n 767), σ (.n 768), σ (.n 769), σ (.n 770), σ (.n 771)], [(σ (.n 779), dsObserve)]⟩ with hs1
  have hK := keccakA_fs (s := s1) (VerifySub.KL.keccakA_complete (hm (.keccak [.n 780, .n 781, .n 25, .n 25, .n 25, .n 26, .n 27, .n 28, .n 774, .n 775,
      .n 776, .n 777, .n 778] [.n 782, .n 783, .n 784, .n 785, .n 786, .n 787, .n 788, .n 789, .n 790, .n 791, .n 792,
      .n 793, .n 794] false false) (by simp))) (by simp [s1]) (by
    simp only [List.map_cons, List.map_nil, s1, i3, i4, i5, i6, i7, i9, i10, z25, z26, z27, z28]
    rfl)
  have hc : ∀ k : Fin 13, ∀ hk : k.val < 13,
      σ ([.n 782, .n 783, .n 784, .n 785, .n 786, .n 787, .n 788, .n 789, .n 790, .n 791, .n 792,
        .n 793, .n 794] : List Core.V)[k.val] = cellsOfState s1.perm false k :=
    fun k hk ↦ outs_eq hK k (by simp)
  have e2 : capOf s1.perm = [σ (.n 790), σ (.n 791), σ (.n 792), σ (.n 793), σ (.n 794)] := by
    simp only [capOf]
    rw [← hc 8 (by decide), ← hc 9 (by decide), ← hc 10 (by decide), ← hc 11 (by decide),
      ← hc 12 (by decide)]
    rfl
  -- the native capacity
  have hendI : (L.endI x.lay x.nF).cap = [σ (.n 767), σ (.n 768), σ (.n 769), σ (.n 770), σ (.n 771)] := by
    have e : (L.endI x.lay x.nF).cap = (chainLast ⟨[], 0, 0⟩ (x.natLI L)).cap := by
      rw [chainLast_ne hne _ ⟨L.cap2 x.lay x.nF, ptrAt x.sI, x.clI⟩]
      exact (natChain_fst_cap _ _ _ _ _ _ _ _ _).2
    rw [e, list5 hcap, ← cells_getD_cap hcap (by norm_num), ← cells_getD_cap hcap (by norm_num),
      ← cells_getD_cap hcap (by norm_num), ← cells_getD_cap hcap (by norm_num), ← cells_getD_cap hcap (by norm_num),
      ← hr 0 (by norm_num), ← hr 1 (by norm_num), ← hr 2 (by norm_num), ← hr 3 (by norm_num), ← hr 4 (by norm_num)]
  have hF : L.freshFs x.lay x.nF = s1 := by
    rw [LinkNat.freshFs, hendI, hs1, i8]
    simp [Fs.absorb, rateScalars]
  rw [← e2, LinkNat.cap4, hF]

end

/-! ## `Bw2` at the honest context -/

/-- The announced layout of a child's stream (`default` off an announced one): `VsCtx.lay` of any context on it. -/
noncomputable def layOf (c : Child) : Layout :=
  ((announcedLayoutAndRate guestBytecode c.proof.stream).map Prod.fst).getD default

theorem VsCtx.lay_eq_layOf (x : VsCtx) : x.lay = layOf x.c := by
  rw [VsCtx.lay]; rfl

/-- **An accepted child's native link at its announced layout**: the honest choices of `bw` and `ret` are
built from this `L` (`VsCtx.natLI`, `natLR`, `natLC`, `natPm`, `L.r`, `L.chi`, `L.qPoint`). -/
theorem natLink_of {seed : Digest} {c : Child} (hc : VsChildOk guestBytecode seed c) :
    ∃ (L : LinkNat) (link : LinkEnd) (rest : List E), c.proof.stream.drop 12 = L.words (layOf c) ++ rest ∧
      L.Ok (layOf c) (natF3 seed c (layOf c).stackLog) c.freshClaim link := by
  obtain ⟨layout, r, hann, -, link, L, rest, hw, hL⟩ := natChildLink hc
  have e : layOf c = layout := by rw [layOf, hann]; rfl
  rw [e]
  exact ⟨L, link, rest, hw, hL⟩

set_option maxHeartbeats 2000000 in
/-- **`Bw2` at the honest context.** From the placement, the buffers' sizes, a causal return rule, the front's
facts (`VsFsChecks1`, `Bw1`, `Ret1`) and `Ret2`, the front's bridge `hood` (the out-of-domain permutation's
capacity the native one), the native link `L` (`natLink_of`), and the honest choices: buffers `5`, `11` the eq
tensors, `7`, `12` the `belowE` tables, `6`, `9`, `10` the native points, and the returns `767 + j`,
`1071 + j`, `1287 + j` the native chains' last cells and `packed_message`'s. -/
theorem VsCtx.bw2_of_nat {x : VsCtx} {L : LinkNat} {link : LinkEnd} {rest : List E}
    (hok : x.Ok) (hbw : x.bw.map List.length = vsAllocSz x.p) (hret : CausalRule x.ret)
    (hfs : VsFsChecks1 x) (hb1 : x.Bw1) (hr1 : x.Ret1) (hr2 : x.Ret2)
    (hood : [x.σ0 (.n 507), x.σ0 (.n 508), x.σ0 (.n 509), x.σ0 (.n 510), x.σ0 (.n 511)] =
      capOf (natOodS x.seed x.c))
    (hw : x.c.proof.stream.drop 12 = L.words x.lay ++ rest) (hL : L.Ok x.lay x.nF x.c.freshClaim link)
    (b11 : x.bw.getD 5 [] = eqLevels (ph7Rs (x.bw.getD 4 [])) 4)
    (b17 : x.bw.getD 11 [] = eqLevels ((x.bw.getD 10 []).take 6) 6)
    (b13 : (x.bw.getD 7 []).take (x.wdS + 1) = (List.range (x.wdS + 1)).map (Link.belowE x.rsS))
    (b18 : (x.bw.getD 12 []).take (x.nS + 1) = (List.range (x.nS + 1)).map (Link.belowE x.as15S))
    (h6 : (x.bw.getD 6 []).take x.wdS = L.r x.lay x.nF)
    (h9 : (x.bw.getD 9 []).take x.nS = L.chi x.lay x.nF)
    (h10 : x.bw.getD 10 [] = L.qPoint x.lay x.nF)
    (r767 : ∀ j < 7, ∀ σ, x.ret (767 + j) σ = (chainLast ⟨[], 0, 0⟩ (x.natLI L)).cells.getD j 0)
    (r1071 : ∀ j < 7, ∀ σ, x.ret (1071 + j) σ = (chainLast ⟨[], 0, 0⟩ (x.natLC L)).cells.getD j 0)
    (r1287 : ∀ j < 6, ∀ σ, x.ret (1287 + j) σ = (x.natPm L).getD j 0)
    (hcalls : x.LkCalls (x.natLk2 L)) (he12 : x.ec 12 = ph11End B2C.fs x.al x.nS x.h0S (x.ec 9)) :
    x.Bw2 := by
  obtain ⟨layout, r, hann, -, hN⟩ := frontNum_of_child hok.child
  have hlay : x.lay = layout := VsCtx.lay_of hann
  have htab : x.lay.tables = tables := by rw [hlay]; exact announced_tables hann
  have hwd : L.chunks.width = widthOf layout := by
    rw [VerifySub.chunks_width hL.chunks, ← widthOf_eq_linkWidth, hlay]
  have hw19 := hN.hw19
  have hbits : L.bits x.lay ≠ 0 := grindingBits_ne (le_max_of_le_right (by omega))
  have ha : x.args.length = 6 := rfl
  have hb18 := hb1.front.b18
  have gcl : lrClaim (x.w 752) (x.w 753) ((x.bw.getD 4 []).getD 6 0) ((x.bw.getD 4 []).getD 7 0) = x.clI := by
    have e1 : x.w 752 = _ := vsW_retC ha hret (i := 752) (by decide) hr2.r752
    have e2 : x.w 753 = _ := vsW_retC ha hret (i := 753) (by decide) hr2.r753
    rw [e1, e2]
    rfl
  have hcap : (chainLast ⟨[], 0, 0⟩ (x.natLI L)).cap.length = 5 := natChain_last_cap (by omega) _ _ _
  have g773 : x.w 773 = (chainLast ⟨[], 0, 0⟩ (x.natLI L)).cl := by
    have e : x.w (767 + 6) = _ := vsW_retC ha hret (i := 767 + 6) (by decide) (r767 6 (by norm_num))
    rw [e, cells_getD_6 hcap]
  have hrd : ∀ rd, HoldsWords rd x.Wo → ReadsAt rd (ptrAt (x.base 18)) (x.bw.getD 18 []) := fun rd hW =>
    hW _ (VsCtx.memWo (x := x) hbw (by norm_num) (by norm_num))
  exact ⟨b11, b17, b13, b18, ⟨_, lk2Ok_nat hann hN hw hL hb18 hrd
    (VsCtx.g1_of (x := x) hw htab hL.chunks hbits hfs hr1 hood)
    (VsCtx.g2_of (x := x) hw hbits (by omega) hL.lenI hret hb18 (VsCtx.reads18 (x := x) hok hbw) r767)
    (VsCtx.g3_of (x := x) hfs) gcl g773 h6 h9 h10 r767 r1071 r1287 hcalls⟩, he12⟩

/-! ## The honest buffers, chosen -/

/-- A list padded with zeros to `n` words. -/
def padTo (n : ℕ) (l : List E) : List E := l ++ List.replicate (n - l.length) 0

theorem padTo_length {n : ℕ} {l : List E} (h : l.length ≤ n) : (padTo n l).length = n := by
  simp [padTo]; omega

theorem padTo_take {n k : ℕ} {l : List E} (h : l.length = k) : (padTo n l).take k = l := by
  unfold padTo; exact List.take_left' h

/-- **The honest buffers `Bw2` names**, from the native link `L`, given the opening's `.n 10` (buffer `4`,
vsph1's): `.n 11` (buffer `5`) and `.n 17` (`11`) the eq tensors, `.n 12` (`6`) the index point, `.n 13` (`7`) its
`belowE` table, `.n 15` (`9`) the row point, `.n 16` (`10`) the pointer columns' point, `.n 18` (`12`) the row
point's `belowE` table. -/
structure BwNat (x : VsCtx) (L : LinkNat) : Prop where
  b5 : x.bw.getD 5 [] = eqLevels (ph7Rs (x.bw.getD 4 [])) 4
  b6 : x.bw.getD 6 [] = padTo 24 (L.r x.lay x.nF)
  b7 : x.bw.getD 7 [] = padTo 25 ((List.range (x.wdS + 1)).map (Link.belowE (L.r x.lay x.nF)))
  b9 : x.bw.getD 9 [] = padTo 24 (L.chi x.lay x.nF)
  b10 : x.bw.getD 10 [] = L.qPoint x.lay x.nF
  b11 : x.bw.getD 11 [] = eqLevels ((L.qPoint x.lay x.nF).take 6) 6
  b12 : x.bw.getD 12 [] = padTo 25 ((List.range (x.nS + 1)).map (Link.belowE (L.chi x.lay x.nF)))

section
variable {x : VsCtx} {L : LinkNat} {link : LinkEnd}

theorem natR_length (hL : L.Ok x.lay x.nF x.c.freshClaim link) : (L.r x.lay x.nF).length = x.wdS := by
  simp only [LinkNat.r, LinkNat.chainI, List.length_map, natChain_length]
  rw [VerifySub.chunks_width hL.chunks]; rfl

theorem natChi_length : (L.chi x.lay x.nF).length = x.nS := by
  simp only [LinkNat.chi, LinkNat.chainR, List.length_map, natChain_length]; rfl

theorem natQ_length (htab : x.lay.tables = tables) : (L.qPoint x.lay x.nF).length = 6 := by
  simp only [LinkNat.qPoint, LinkNat.chainC, List.length_map, natChain_length]
  exact VerifySub.linkQVars_tables htab

/-- **The honest buffers' sizes**: at a width and a row count at most `24`, an opening of at least `54` words. -/
theorem BwNat.lengths (hB : BwNat x L) (hL : L.Ok x.lay x.nF x.c.freshClaim link) (htab : x.lay.tables = tables)
    (hw : x.wdS ≤ 24) (hn : x.nS ≤ 24) (h4 : 54 ≤ (x.bw.getD 4 []).length) :
    (x.bw.getD 5 []).length = 30 ∧ (x.bw.getD 6 []).length = 24 ∧ (x.bw.getD 7 []).length = 25 ∧
      (x.bw.getD 9 []).length = 24 ∧ (x.bw.getD 10 []).length = 6 ∧ (x.bw.getD 11 []).length = 126 ∧
      (x.bw.getD 12 []).length = 25 := by
  have hq := natQ_length (L := L) htab
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have e : (ph7Rs (x.bw.getD 4 [])).length = 4 := by
      simp only [ph7Rs, List.length_take, List.length_drop]; omega
    rw [hB.b5, eqLevels_length (by omega)]; rfl
  · rw [hB.b6, padTo_length (by rw [natR_length hL]; exact hw)]
  · rw [hB.b7, padTo_length (by simp; omega)]
  · rw [hB.b9, padTo_length (by rw [natChi_length]; exact hn)]
  · rw [hB.b10, hq]
  · rw [hB.b11, eqLevels_length (by simp [hq])]; rfl
  · rw [hB.b12, padTo_length (by simp; omega)]

set_option maxHeartbeats 2000000 in
/-- **`Bw2` at the honest buffers** (`BwNat`), as `VsCtx.bw2_of_nat`. -/
theorem VsCtx.bw2_of_bwNat {rest : List E}
    (hok : x.Ok) (hbw : x.bw.map List.length = vsAllocSz x.p) (hret : CausalRule x.ret)
    (hfs : VsFsChecks1 x) (hb1 : x.Bw1) (hr1 : x.Ret1) (hr2 : x.Ret2)
    (hood : [x.σ0 (.n 507), x.σ0 (.n 508), x.σ0 (.n 509), x.σ0 (.n 510), x.σ0 (.n 511)] =
      capOf (natOodS x.seed x.c))
    (hw : x.c.proof.stream.drop 12 = L.words x.lay ++ rest) (hL : L.Ok x.lay x.nF x.c.freshClaim link)
    (hB : BwNat x L)
    (r767 : ∀ j < 7, ∀ σ, x.ret (767 + j) σ = (chainLast ⟨[], 0, 0⟩ (x.natLI L)).cells.getD j 0)
    (r1071 : ∀ j < 7, ∀ σ, x.ret (1071 + j) σ = (chainLast ⟨[], 0, 0⟩ (x.natLC L)).cells.getD j 0)
    (r1287 : ∀ j < 6, ∀ σ, x.ret (1287 + j) σ = (x.natPm L).getD j 0)
    (hcalls : x.LkCalls (x.natLk2 L)) (he12 : x.ec 12 = ph11End B2C.fs x.al x.nS x.h0S (x.ec 9)) :
    x.Bw2 := by
  have hr := natR_length hL
  have hc := natChi_length (x := x) (L := L)
  have h6 : (x.bw.getD 6 []).take x.wdS = L.r x.lay x.nF := by rw [hB.b6]; exact padTo_take hr
  have h9 : (x.bw.getD 9 []).take x.nS = L.chi x.lay x.nF := by rw [hB.b9]; exact padTo_take hc
  have b13 : (x.bw.getD 7 []).take (x.wdS + 1) = (List.range (x.wdS + 1)).map (Link.belowE x.rsS) := by
    rw [hB.b7, padTo_take (by simp), VsCtx.rsS, h6]
  have b18 : (x.bw.getD 12 []).take (x.nS + 1) = (List.range (x.nS + 1)).map (Link.belowE x.as15S) := by
    rw [hB.b12, padTo_take (by simp), VsCtx.as15S, h9]
  have b17 : x.bw.getD 11 [] = eqLevels ((x.bw.getD 10 []).take 6) 6 := by rw [hB.b11, hB.b10]
  exact VsCtx.bw2_of_nat hok hbw hret hfs hb1 hr1 hr2 hood hw hL hB.b5 b17 b13 b18 h6 h9 hB.b10 r767 r1071 r1287 hcalls he12

end

/-! ## The honest returns, chosen -/

/-- **The honest returns `Bw2` and `Ret2` name**, as constants: `state_ends`' (`752`, `753`), `link_rounds`'
(`767 ..< 774`), `index_side`'s (`797 ..= 799`), `link_row_side`'s (`1071 ..< 1078`), the zero hint `1286`,
`packed_message`'s (`1287 ..< 1293`), the first `table_point`'s (`1296 ..= 1298`); `none` elsewhere. -/
noncomputable def honRet (x : VsCtx) (L : LinkNat) (i : ℕ) : Option E :=
  if i = 752 then some (prodE (x.zsS.map (1 + ·)))
  else if i = 753 then some (Link.endsProd ((x.bw.getD 2 []).take x.wdS) x.zsS)
  else if 767 ≤ i ∧ i < 774 then some ((chainLast ⟨[], 0, 0⟩ (x.natLI L)).cells.getD (i - 767) 0)
  else if i = 797 then some (indexMle x.rsS)
  else if i = 798 then some (Link.sideFold x.zsS x.rsS).1
  else if i = 799 then some (Link.sideFold x.zsS x.rsS).2.1
  else if 1071 ≤ i ∧ i < 1078 then some ((chainLast ⟨[], 0, 0⟩ (x.natLC L)).cells.getD (i - 1071) 0)
  else if i = 1286 then some 0
  else if 1287 ≤ i ∧ i < 1293 then some ((x.natPm L).getD (i - 1287) 0)
  else if i = 1296 then some ((x.bw.getD 4 []).getD 0 0 * Link.tpTotalG (((x.bw.getD 4 []).drop 89).take x.h0S)
    ((x.bw.getD 9 []).take x.h0S) ((x.bw.getD 1 []).take x.h0S) ((x.bw.getD 1 []).getD x.h0S 0) x.h0S)
  else if i = 1297 then some (1 + (1 + (x.bw.getD 1 []).getD x.h0S 0) *
    Link.tpPad ((x.bw.getD 1 []).take x.h0S) ((x.bw.getD 9 []).take x.h0S))
  else if i = 1298 then some (Link.tpFullAt (((x.bw.getD 4 []).drop 89).take x.h0S) ((x.bw.getD 9 []).take x.h0S) x.h0S)
  else none

section
variable {x : VsCtx} {L : LinkNat} {link : LinkEnd}

/-- **A return rule agreeing with `honRet`** gives `Ret2` and the link's returns `Bw2` asks. -/
theorem ret_of_honRet (h : ∀ i v, honRet x L i = some v → ∀ σ, x.ret i σ = v) :
    x.Ret2 ∧ (∀ j < 7, ∀ σ, x.ret (767 + j) σ = (chainLast ⟨[], 0, 0⟩ (x.natLI L)).cells.getD j 0) ∧
      (∀ j < 7, ∀ σ, x.ret (1071 + j) σ = (chainLast ⟨[], 0, 0⟩ (x.natLC L)).cells.getD j 0) ∧
      (∀ j < 6, ∀ σ, x.ret (1287 + j) σ = (x.natPm L).getD j 0) := by
  refine ⟨⟨h _ _ (by simp [honRet]), h _ _ (by simp [honRet]), h _ _ (by simp [honRet]), h _ _ (by simp [honRet]),
    h _ _ (by simp [honRet]), h _ _ (by simp [honRet]), h _ _ (by simp [honRet]), h _ _ (by simp [honRet]),
    h _ _ (by simp [honRet])⟩, fun j hj => h _ _ ?_, fun j hj => h _ _ ?_, fun j hj => h _ _ ?_⟩
  · unfold honRet
    rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_left (by omega), Nat.add_sub_cancel_left]
  · unfold honRet
    rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega),
      ite_eq_right (by omega), ite_eq_left (by omega), Nat.add_sub_cancel_left]
  · unfold honRet
    rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega),
      ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_left (by omega), Nat.add_sub_cancel_left]

/-- **`Bw2` and `Ret2` at the honest context**: the honest buffers (`BwNat`) and returns (`honRet`) from the
native link `L` (`natLink_of`), given the placement, the sizes, a causal return rule, the front's facts and its
bridge `hood`. -/
theorem VsCtx.bw2Ret2_of_nat {rest : List E}
    (hok : x.Ok) (hbw : x.bw.map List.length = vsAllocSz x.p) (hret : CausalRule x.ret)
    (hfs : VsFsChecks1 x) (hb1 : x.Bw1) (hr1 : x.Ret1)
    (hood : [x.σ0 (.n 507), x.σ0 (.n 508), x.σ0 (.n 509), x.σ0 (.n 510), x.σ0 (.n 511)] =
      capOf (natOodS x.seed x.c))
    (hw : x.c.proof.stream.drop 12 = L.words x.lay ++ rest) (hL : L.Ok x.lay x.nF x.c.freshClaim link)
    (hB : BwNat x L) (hR : ∀ i v, honRet x L i = some v → ∀ σ, x.ret i σ = v)
    (hcalls : x.LkCalls (x.natLk2 L)) (he12 : x.ec 12 = ph11End B2C.fs x.al x.nS x.h0S (x.ec 9)) :
    x.Bw2 ∧ x.Ret2 := by
  obtain ⟨h2, r767, r1071, r1287⟩ := ret_of_honRet hR
  exact ⟨VsCtx.bw2_of_bwNat hok hbw hret hfs hb1 hr1 h2 hood hw hL hB r767 r1071 r1287 hcalls he12, h2⟩

end

/-! ## The front's bridge at the context, and the result -/

section
variable {x : VsCtx} {L : LinkNat} {link : LinkEnd}

/-- **The front's out-of-domain capacity is the native one** (vsnat3's `vsVal_oodS` at the context). -/
theorem VsCtx.hood_of (hok : x.Ok) (hbw : x.bw.map List.length = vsAllocSz x.p) (hret : CausalRule x.ret)
    (hb18 : x.bw.getD 18 [] = padStream x.c.proof.stream) :
    [x.σ0 (.n 507), x.σ0 (.n 508), x.σ0 (.n 509), x.σ0 (.n 510), x.σ0 (.n 511)] = capOf (natOodS x.seed x.c) := by
  have ha : x.args.length = 6 := rfl
  obtain ⟨layout, r, hann, S, hlen, -⟩ := natFront hok.child
  have hws : ∀ i < x.c.proof.stream.length,
      (padStream x.c.proof.stream).getD i 0 = x.c.proof.stream.getD i 0 := fun i hi => padStream_getDF hi
  have hwl : x.c.proof.stream.length ≤ (padStream x.c.proof.stream).length := by simp [padStream]
  have h0 : ReadsAt x.rd0 (ptrAt (x.base 18)) (padStream x.c.proof.stream) := by
    rw [← hb18]; exact VsCtx.reads18 hok hbw
  have hw55 : x.w 55 = ptrAt (x.base 18) := vsW_buf (rd1 := x.rd1) ha hret (j := 18) (by norm_num) rfl
  have hB13 := vsVal_oodS (rd0 := x.rd0) (args := x.args) (seed := x.seed) (c := x.c) (gsq := ptrAt x.qt)
    (out := ptrAt x.qo) rfl hw55 h0 (by omega) (fun i hi => hws i (by omega)) (by omega)
  have e8 : x.σ0 (.n 507) = cellsOfState (natOodS x.seed x.c) false 8 := outs_eq hB13 8 (by simp)
  have e9 : x.σ0 (.n 508) = cellsOfState (natOodS x.seed x.c) false 9 := outs_eq hB13 9 (by simp)
  have e10 : x.σ0 (.n 509) = cellsOfState (natOodS x.seed x.c) false 10 := outs_eq hB13 10 (by simp)
  have e11 : x.σ0 (.n 510) = cellsOfState (natOodS x.seed x.c) false 11 := outs_eq hB13 11 (by simp)
  have e12 : x.σ0 (.n 511) = cellsOfState (natOodS x.seed x.c) false 12 := outs_eq hB13 12 (by simp)
  rw [e8, e9, e10, e11, e12]
  rfl

/-- **`Bw2` and `Ret2` at the honest context**: the honest buffers (`BwNat`) and returns (`honRet`) from the
native link `L` (`natLink_of`), given the placement, the buffers' sizes, a causal return rule and the front's
facts (`VsFsChecks1`, vsnat3's `fsChecks1`; `Bw1`, `Ret1`, vsph1's). -/
theorem VsCtx.bw2Ret2_honest {rest : List E}
    (hok : x.Ok) (hbw : x.bw.map List.length = vsAllocSz x.p) (hret : CausalRule x.ret)
    (hfs : VsFsChecks1 x) (hb1 : x.Bw1) (hr1 : x.Ret1)
    (hw : x.c.proof.stream.drop 12 = L.words x.lay ++ rest) (hL : L.Ok x.lay x.nF x.c.freshClaim link)
    (hB : BwNat x L) (hR : ∀ i v, honRet x L i = some v → ∀ σ, x.ret i σ = v)
    (hcalls : x.LkCalls (x.natLk2 L)) (he12 : x.ec 12 = ph11End B2C.fs x.al x.nS x.h0S (x.ec 9)) :
    x.Bw2 ∧ x.Ret2 :=
  VsCtx.bw2Ret2_of_nat hok hbw hret hfs hb1 hr1 (VsCtx.hood_of hok hbw hret hb1.front.b18) hw hL hB hR hcalls he12

end

end
end LeanVM.Guest.B1.VsC
