/-
  LeanVM.Guest.B1.VsC.VsNatLink

  An accepted child's link, read backwards: the native link verifier's values as functions of what it read.
-/

module

public import LeanVM.Guest.B1.VsC.VsNatRun
public import LeanVM.Guest.B1.VerifySub.PhLinkSpine
public import LeanVM.Protocol.Link.Skeleton
public import LeanVM.Guest.B1.VsC.LinkShape
public import LeanVM.Guest.B1.VsC.LinkCallees
public import LeanVM.Guest.Complete.MainB1

/-!
# The link, natively

`LinkNat`: what the link reads, in order: the grind's nonce, the index side's rounds' words, the memory term
`m1`, the row side's and the pointer columns' rounds' words, the packed message. Every other value of the
native run is a function of it, the starting sponge and the layout: `θ_0`, the packed draws (`drawn`), the
index side's chain `chainI` from `cap2` (its point `r`, its end `endI`), the fresh coefficients `fresh` (cells
`0 .. 4` of the permutation absorbing `m1`), the row side's chain `chainR` from `cap4` (its point `chi`), the
pointer columns' chain `chainC` (its point `qPoint`, its end `endC`).

**`natLink_inv`**: an accepting deployed run of `verifyLink (freshSplit fc) layout`, from a sponge carried as
`F`, read `L.words` for some `L` with `L.Ok`: the chunks, the grind passing, the three chains `RoundChain`s at
every cursor and claim on every memory reading their words, the fresh claim's point the index point's first
`logBytecode` words, the terminal check (`tailLast … = endC.cl`), and the link's end `lkEnd`.
-/

namespace LeanVM.Guest.B1.VsC

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.B1 LeanVM.Guest.B1.Whir
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Protocol.Link LeanVM.Node LeanVM.Guest.Complete
open LeanVM.Guest.B1.Tables (TSt TCar fsOfT NoPacked noPacked_sumcheck noPacked_require)
open LeanVM.Guest.B1.VerifySub (tailLast lkEnd linkTailR_eq tailNValues_tables)

@[expose] public section

/-- **What the link reads**, in order. -/
structure LinkNat where
  chunks : Chunks
  n0 : E
  wsI : List E
  m1 : E
  wsR : List E
  wsC : List E
  msg : List E

namespace LinkNat

variable (L : LinkNat) (layout : Layout) (F : Fs)

/-- The link grind's bits. -/
def bits : ℕ := grindingBits (max (linkRows layout + 3 + bytecodeSlotBits) (L.chunks.width + 1))
/-- `θ_0`: the grind's challenge. -/
def theta0 : E := (F.grindSqueeze (L.bits layout) L.n0).1
/-- The capacity after `θ_0`. -/
def cap1 : List E := (F.grindSqueeze (L.bits layout) L.n0).2.cap
/-- The packed draw's size. -/
def nDrawn : ℕ := linkDrawn layout L.chunks
/-- The packed draws. -/
def drawn : List E := (Link.pkSqueeze (pkCount (L.nDrawn layout)) (L.cap1 layout F)).1.take (L.nDrawn layout)
/-- The capacity after the packed draws. -/
def cap2 : List E := (Link.pkSqueeze (pkCount (L.nDrawn layout)) (L.cap1 layout F)).2
/-- The index side's claim. -/
def claimI : E := indexClaim layout L.chunks (L.drawn layout F)
/-- The index side's chain from the cursor `cur` and the claim `cl`. -/
def chainI (cur cl : E) : List (E × Link.RSt) :=
  natChain 1 0 L.chunks.width ⟨L.cap2 layout F, cur, cl⟩ L.wsI
/-- The index side's end. -/
def endI : Link.RSt := Link.chainLast ⟨L.cap2 layout F, 0, L.claimI layout F⟩ (L.chainI layout F 0 (L.claimI layout F))
/-- The index point. -/
def r : List E := (L.chainI layout F 0 (L.claimI layout F)).map Prod.fst
/-- The sponge `m1` waits in. -/
def freshFs : Fs := (⟨(L.endI layout F).cap, []⟩ : Fs).absorb L.m1 dsObserve
/-- The fresh coefficients. -/
def fresh : List E := (List.range 5).map (Link.cellAt (L.freshFs layout F).perm)
/-- The capacity after them. -/
def cap4 : List E := capOf (L.freshFs layout F).perm
/-- The row rounds' tail coefficients. -/
def ntR : ℕ := (roundCoefficients L.chunks.d).1 - 2
/-- The pointer columns' rounds' tail coefficients. -/
def ntC : ℕ := (roundCoefficients L.chunks.d).2 - 2
/-- The row side's chain. -/
def chainR (cur cl : E) : List (E × Link.RSt) :=
  natChain L.ntR (grindingBits (L.ntR + 1)) (linkRows layout) ⟨L.cap4 layout F, cur, cl⟩ L.wsR
/-- The row side's end. -/
def endR : Link.RSt := Link.chainLast ⟨L.cap4 layout F, 0, (L.endI layout F).cl⟩
  (L.chainR layout F 0 (L.endI layout F).cl)
/-- The row point. -/
def chi : List E := (L.chainR layout F 0 (L.endI layout F).cl).map Prod.fst
/-- The pointer columns' chain. -/
def chainC (cur cl : E) : List (E × Link.RSt) :=
  natChain L.ntC (grindingBits (L.ntC + 1)) (linkQVars layout) ⟨(L.endR layout F).cap, cur, cl⟩ L.wsC
/-- The pointer columns' end. -/
def endC : Link.RSt := Link.chainLast ⟨(L.endR layout F).cap, 0, (L.endR layout F).cl⟩
  (L.chainC layout F 0 (L.endR layout F).cl)
/-- The pointer columns' point. -/
def qPoint : List E := (L.chainC layout F 0 (L.endR layout F).cl).map Prod.fst
/-- The words, in stream order. -/
def words : List E := grindWords (L.bits layout) L.n0 ++ (L.wsI ++ L.m1 :: (L.wsR ++ (L.wsC ++ L.msg)))

/-- **The native link's facts.** -/
structure Ok (fc : FreshClaim) (link : LinkEnd) : Prop where
  chunks : Chunks.new (linkWidth layout) = some L.chunks
  grind : F.GrindOk (L.bits layout) L.n0
  lenI : L.wsI.length = L.chunks.width * natRoundLen 1 0
  lenR : L.wsR.length = linkRows layout * natRoundLen L.ntR (grindingBits (L.ntR + 1))
  lenC : L.wsC.length = linkQVars layout * natRoundLen L.ntC (grindingBits (L.ntC + 1))
  lenM : L.msg.length = 144
  hI : ∀ (cur cl : E) rd, ReadsAt rd cur L.wsI → Link.RoundChain rd 1 0 ⟨L.cap2 layout F, cur, cl⟩ (L.chainI layout F cur cl)
  hR : ∀ (cur cl : E) rd, ReadsAt rd cur L.wsR →
    Link.RoundChain rd L.ntR (grindingBits (L.ntR + 1)) ⟨L.cap4 layout F, cur, cl⟩ (L.chainR layout F cur cl)
  hC : ∀ (cur cl : E) rd, ReadsAt rd cur L.wsC →
    Link.RoundChain rd L.ntC (grindingBits (L.ntC + 1)) ⟨(L.endR layout F).cap, cur, cl⟩ (L.chainC layout F cur cl)
  point : (L.r layout F).take layout.logBytecode = fc.point
  values : fc.values.length = (splitColumns tables).length
  terminal : tailLast layout L.chunks (L.theta0 layout F) (L.drawn layout F) (L.r layout F) L.m1 (L.fresh layout F)
    (Split.ofColumns tables fc.values) (L.chi layout F) (L.qPoint layout F) L.msg = (L.endC layout F).cl
  link : link = lkEnd layout L.chunks (L.theta0 layout F) (L.drawn layout F) (L.r layout F) L.m1 (L.fresh layout F)
    (Split.ofColumns tables fc.values) (L.chi layout F) (L.qPoint layout F) L.msg

end LinkNat

theorem linkDrawn_pos (layout : Layout) (chunks : Chunks) : 1 ≤ linkDrawn layout chunks := by
  unfold linkDrawn packedChallenges
  simp only
  omega

theorem noPacked_freshSplit (fc : FreshClaim) (bc : List K) (pt : List E) (pcs : List (ℕ × ℕ)) :
    NoPacked (freshSplit fc bc pt pcs) :=
  Tables.NoPacked.bind (noPacked_require _) fun _ => trivial

/-- **An accepted link, read backwards.** -/
theorem natLink_inv {fc : FreshClaim} {layout : Layout} (htab : layout.tables = tables) {F : Fs} {sp : Sponge}
    (hs : TCar F none sp) {xs : List E} {os : List (List Opening)} {R : List (Digest × ℕ × ℕ)} {link : LinkEnd}
    {st4 : VerifierProgramState}
    (h : runId (verifyLink (freshSplit fc) layout) ⟨sp, xs, os, R⟩ = some (link, st4)) :
    ∃ (L : LinkNat) (rest : List E), xs = L.words layout ++ rest ∧ L.Ok layout F fc link ∧
      ∃ sp', (⟨Link.pkAbsorb 18 L.msg (L.endC layout F).cap, []⟩ : Fs).Carries sp' ∧ st4 = ⟨sp', rest, os, R⟩ := by
  rw [verifyLink_eq_linkSkeleton] at h
  unfold linkSkeleton at h
  obtain ⟨chunks, hch, h⟩ := natLiftOption h
  obtain ⟨n0, xs1, hx1, hok, sp1, hc1, h⟩ := natGrindSample hs h
  obtain ⟨sp2, hc2, h⟩ := natSamplePacked (linkDrawn_pos layout chunks) hc1 h
  -- the index side
  obtain ⟨a, st1, t1, h⟩ := natBind_np (noPacked_sumcheck _ _ _) hc2 h
  obtain ⟨wsI, xs2, hlI, hx2, ea, est1, hchI⟩ := natChain_inv (nt := 1) (bits := 0) (by decide) chunks.width
    ⟨_, 0, _⟩ ⟨sp2, hc2⟩ t1
  obtain ⟨hc3, hst1⟩ := natEnd est1
  rw [ea, hst1] at h
  dsimp only at h
  unfold linkRowPhase at h
  -- the memory term, the fresh coefficients, the split
  obtain ⟨m1, xs3, hx3, sp3, hc4, h⟩ := natRead hc3 h
  obtain ⟨sp4, hc5, h⟩ := natSample5 hc4 h
  obtain ⟨spl, st5, t5, h⟩ := natBind_np (noPacked_freshSplit _ _ _ _) hc5 h
  unfold freshSplit at t5
  obtain ⟨hpt, t5⟩ := runTc_require t5
  have e5 := runTc_ret_inv t5
  simp only [Prod.mk.injEq] at e5
  obtain ⟨rfl, e5⟩ := e5
  obtain ⟨hc6, hst5⟩ := natEnd e5
  rw [hst5] at h
  -- the row side
  obtain ⟨b2, st6, t6, h⟩ := natBind_np (noPacked_sumcheck _ _ _) hc6 h
  have eR : (roundCoefficients chunks.d).1 = (roundCoefficients chunks.d).1 - 2 + 2 := by
    unfold roundCoefficients; omega
  rw [eR] at t6
  obtain ⟨wsR, xs4, hlR, hx4, eb, est6, hchR⟩ := natChain_inv rfl (linkRows layout) ⟨_, 0, _⟩ ⟨_, hc6⟩ t6
  obtain ⟨hc7, hst6⟩ := natEnd est6
  rw [eb, hst6] at h
  dsimp only at h
  -- the pointer columns
  obtain ⟨b3, st7, t7, h⟩ := natBind_np (noPacked_sumcheck _ _ _) hc7 h
  have eC : (roundCoefficients chunks.d).2 = (roundCoefficients chunks.d).2 - 2 + 2 := by
    unfold roundCoefficients; omega
  rw [eC] at t7
  obtain ⟨wsC, xs5, hlC, hx5, ec, est7, hchC⟩ := natChain_inv rfl (linkQVars layout) ⟨_, 0, _⟩ ⟨_, hc7⟩ t7
  obtain ⟨hc8, hst7⟩ := natEnd est7
  rw [ec, hst7] at h
  dsimp only at h
  -- the message, the terminal check, the end
  rw [Link.Arith.linkTailEq _ _ _ _ _ _ _ _ _ _ _, linkTailR_eq, tailNValues_tables htab,
    show 80 + kBits = 8 * 18 from rfl] at h
  obtain ⟨msg, rest, hlm, hx6, sp9, hc9, h⟩ := natReadPacked hc8 h
  obtain ⟨hterm, h⟩ := natRequire h
  have e9 := natRet h
  simp only [Prod.mk.injEq] at e9
  obtain ⟨rfl, rfl⟩ := e9
  refine ⟨⟨chunks, n0, wsI, m1, wsR, wsC, msg⟩, rest, ?_, ⟨hch, hok, hlI, hlR, hlC, hlm, hchI, hchR, hchC,
    hpt.1, hpt.2, hterm, rfl⟩, sp9, hc9, rfl⟩
  rw [hx1, hx2, hx3, hx4, hx5, hx6]
  simp [LinkNat.words, LinkNat.bits]

/-! ## At an accepted child -/

/-- A layout `buildLayout` gives has the deployed tables. -/
theorem buildLayout_tables {bytecode : List K} {logMemory : ℕ} {tableRows : List ℕ} {layout : Layout}
    (h : buildLayout bytecode logMemory tableRows = some layout) : layout.tables = tables := by
  unfold buildLayout at h
  split at h
  · cases h
  · split at h
    · simp only [Option.some.injEq] at h
      subst h
      rfl
    · cases h

/-- An announced layout has the deployed tables. -/
theorem announced_tables {bytecode : List K} {stream : List E} {layout : Layout} {r : ℕ}
    (h : announcedLayoutAndRate bytecode stream = some (layout, r)) : layout.tables = tables := by
  have hs := announced_eq_run (fun _ ↦ default) (fun _ ↦ default) bytecode
    (s := ⟨⟨default, [], none⟩, stream, [], []⟩) rfl
  have hsz : sizesOf bytecode (stream.take (2 + nTables)) = some (layout, r) := by
    have e := hs.symm.trans h
    rw [run_readSizes _ _ bytecode rfl] at e
    split at e
    · exact e
    · cases e
  obtain ⟨-, -, -, -, lm, rows, hb⟩ := sizesOf_facts hsz
  exact buildLayout_tables hb

/-- **An accepted child's link, natively**: past the stream's first `12` words, the link read `L.words`,
with `L.Ok` from the out-of-domain sample's sponge `natF3`. -/
theorem natChildLink {seed : Digest} {c : Child} (hc : VsChildOk guestBytecode seed c) :
    ∃ (layout : Layout) (r : ℕ), announcedLayoutAndRate guestBytecode c.proof.stream = some (layout, r) ∧
      VsShape guestBytecode layout r ∧
      ∃ (link : LinkEnd) (L : LinkNat) (rest : List E), c.proof.stream.drop 12 = L.words layout ++ rest ∧
        L.Ok layout (natF3 seed c layout.stackLog) c.freshClaim link := by
  obtain ⟨layout, r, hann, S, -, -, ood, link, st3, st4, -, -, hc3, hs3, ho3, hL⟩ := natFront hc
  obtain ⟨sp, xs, os, R⟩ := st3
  simp only at hs3 ho3 hc3
  subst hs3
  obtain ⟨L, rest, hx, hok, -⟩ := natLink_inv (announced_tables hann) hc3 hL
  exact ⟨layout, r, hann, S, link, L, rest, hx, hok⟩

/-- **The native counts are the guest's**: at a deployed width, the chunk count is `chunkCount`, the row
rounds take `chunkCount + 1` tail coefficients and the pointer columns' `chunkCount`, their grinds
`lrsGrind`'s. -/
theorem natLink_counts {w : ℕ} {ch : Chunks} (h : Chunks.new w = some ch) (h1 : 19 ≤ w) (h2 : w ≤ 24)
    {L : LinkNat} (hL : L.chunks = ch) :
    L.ntR = chunkCount w + 1 ∧ L.ntC = chunkCount w ∧
      grindingBits (L.ntR + 1) = (lrsGrind (chunkCount w)).1 ∧
      grindingBits (L.ntC + 1) = (lrsGrind (chunkCount w)).2 := by
  have hd : chunkCount w = ch.d := by simp [chunkCount, h]
  obtain ⟨-, r1, r2⟩ := chunkD_range w h1 h2
  rw [hd] at r1 r2
  have e1 : guest_const% LINK_D_MIN = 6 := rfl
  have e2 : guest_const% LINK_D_ARMS = 4 := rfl
  rw [e1] at r1
  rw [e1, e2] at r2
  have hR : L.ntR = ch.d + 1 := by unfold LinkNat.ntR roundCoefficients; rw [hL]; omega
  have hC : L.ntC = ch.d := by unfold LinkNat.ntC roundCoefficients; rw [hL]; omega
  rw [hd, hR, hC]
  refine ⟨rfl, rfl, ?_⟩
  rcases (by omega : ch.d = 6 ∨ ch.d = 7 ∨ ch.d = 8 ∨ ch.d = 9) with h | h | h | h <;> rw [h] <;> decide

end
end LeanVM.Guest.B1.VsC
