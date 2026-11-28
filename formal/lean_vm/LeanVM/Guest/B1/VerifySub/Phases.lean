/-
  LeanVM.Guest.B1.VerifySub.Phases

  `verify_sub`'s body against the deferring verifier, phase by phase: the objects a run's
  valuation holds (decoded), and what each phase of the body establishes of them.
-/

module

public import LeanVM.Guest.B1.VerifySub.Proof
public import LeanVM.Guest.B1.Main.SoundVX
public import LeanVM.Guest.B1.Stack.Interface
public import LeanVM.Guest.B1.Common.Run
import LeanVM.Guest.ValRef
import LeanVM.Guest.Data.ValNames.«verify_sub»
import LeanVM.Guest.GuestConst
-- Private: `guest_const%` inserts literals, so importers need not see the guest's data.
import LeanVM.Guest.Data.Consts

/-!
# `verify_sub`, phase by phase

A run of `verify_sub`'s body (`VsRun`) holds, in its valuation and the memory, every object the
deferring verifier (`deferringVerifierProgram`, `Statement/Verifier/Lib.lean`) computes on the child
proof `vsPiOf`: the seed and the public input (`vsSeed`, `vsPi`), the announced words and the
layout they give (`vsAnnounced`, `vsLayout`, `vsLir`), the fresh claim (`vsFresh`: the link point's
first `19` coordinates at `r_pt`, the hinted `split_values`), and the carried sponge between the
phases (`vsF0` after the seed, `vsF1` after the sizes, `vsF2` after the root, `vsF3` after the
out-of-domain value, `vsF5` after the public input's challenge, `vsF8` after the ring switch's
challenges).

Each phase's statement says what the body's run gives of them, the verifier's phase run on the
carried sponge (`RunsTo`, `B1/Common/Run.lean`) from the words in the stream:

* `PhSeed`: the seed's `KECCAK` writes the seed state's capacity;
* `PhSizes`: the eight announced words at `stream` run `readAnnouncedSizes`, the layout
  `buildLayout`'s, its stack's log in range, the dispatch selectors `size_sel` and `rate_sel`;
* `PhRoot`: the root's two words follow, absorbed;
* `PhOod`: the out-of-domain grind's nonce and value follow and run `readOod`;
* `PhLink`: the link's words follow and run `verifyLink` with the fresh claim's split
  (`freshSplit`), the public input's challenge `rm` after it, and what the later phases read of
  the link's end (`VsLinkFacts`);
* `PhKeccak`: the Keccak reduction's words run `keccakValidity` on that end (`VsKeccakFacts`);
* `PhRing`: the ring switch's nonce runs `ringSwitch` (`VsRingFacts`);
* `PhOpen`: `open_stacked`'s words and openings (`vsOsW`) run `verifyStackedOpening` on the
  verifier's claims;
* `PhExport`: the fresh claim's cells at `defer_out`, nothing returned.

`Chain.lean` chains them into `Main.SubSoundW bytecode vsPiOf`.
-/

namespace LeanVM.Guest.B1.VerifySub

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

/-! ## A run -/

/-- **A run of `verify_sub`'s body**: for a stacked program of `2^(19 + BYTECODE_SLOT_BITS)` words, on
a memory image of at most `2^32` words, under a call relation that unfolds at `V` and lies below
`coreProgram.Rel`, its body holds at `σ` returning `rets`, its arguments holding the exponent
tables. `Main.SubSoundW`'s hypotheses. -/
structure VsRun (bytecode : List K) {κ : ℕ} (L : MemoryImage κ) (C : CallRel) (V : FrameMap)
    (σ : Val) (rets : List E) : Prop where
  hbl : bytecode.length = 2 ^ (Main.bytecodeLog + bytecodeSlotBits)
  hκ : κ ≤ 32
  hU : UnfoldsV L.read C V
  hle : CallRel.Le C (coreProgram.Rel L.read)
  hb : Stmt.HoldsList C L.read σ (Fn.body fn% «verify_sub») False (fun rs ↦ rs = rets)
  hpre : VerifySubPre L.read ((fn% «verify_sub»).params.map σ)

/-! ## The objects a run holds -/

theorem wordsAt_length (rd : Reader) (p : E) (n : ℕ) : (wordsAt rd p n).length = n := by
  simp [wordsAt]

/-- The seed, from its halves `seed_0`, `seed_1`. -/
def vsSeed (σ : Val) : Digest :=
  digestFromHalves (σ (.n (val% «verify_sub» "seed_0")), σ (.n (val% «verify_sub» "seed_1")))

/-- The public input, from its halves `pi_0`, `pi_1`. -/
def vsPi (σ : Val) : Digest :=
  digestFromHalves (σ (.n (val% «verify_sub» "pi_0")), σ (.n (val% «verify_sub» "pi_1")))

/-- The stream's base. -/
def vsStream (σ : Val) : E := σ (.n (val% «verify_sub» "stream"))

/-- The fresh claim the child raises: the link point's `19` instruction coordinates at `r_pt`,
the `36` split columns' values at `splitv`. -/
def vsFresh (rd : Reader) (σ : Val) : FreshClaim :=
  ⟨wordsAt rd (σ (.n (val% «verify_sub» "r_pt"))) Main.bytecodeLog,
    wordsAt rd (σ (.n (val% «verify_sub» "splitv"))) (guest_const% N_SPLIT)⟩

/-- The eight announced words: the memory's log, the six tables' rows, the rate. -/
def vsAnnounced (σ : Val) : List E :=
  [σ (.n (val% «verify_sub» "x@1")), σ (.n (val% «verify_sub» "x@2")),
    σ (.n (val% «verify_sub» "x@3")), σ (.n (val% «verify_sub» "x@4")),
    σ (.n (val% «verify_sub» "x@5")), σ (.n (val% «verify_sub» "x@6")),
    σ (.n (val% «verify_sub» "x@7")), σ (.n (val% «verify_sub» "x@8"))]

/-- The announced memory log (`readAnnouncedSizes`' `logMemory`). -/
def vsLogMem (σ : Val) : ℕ := kToNat ((σ (.n (val% «verify_sub» "x@1"))).limb 0)

/-- The announced row counts (`readAnnouncedSizes`' `tableRows`). -/
def vsRows (σ : Val) : List ℕ := (((vsAnnounced σ).drop 1).take nTables).map fun v ↦ kToNat (v.limb 0)

/-- The announced rate exponent (`readAnnouncedSizes`' `logInverseRate`). -/
def vsLir (σ : Val) : ℕ := kToNat ((σ (.n (val% «verify_sub» "x@8"))).limb 0)

/-- The layout the announced sizes give (`buildLayout`'s). -/
def vsLayout (bytecode : List K) (σ : Val) : Layout :=
  (buildLayout bytecode (vsLogMem σ) (vsRows σ)).getD default

/-- The carried sponge after the seed: the seed permutation's capacity, nothing waiting. -/
def vsF0 (σ : Val) : Fs :=
  ⟨[σ (.n (val% «verify_sub» "sp[8]")), σ (.n (val% «verify_sub» "sp[9]")),
    σ (.n (val% «verify_sub» "sp[10]")), σ (.n (val% «verify_sub» "sp[11]")),
    σ (.n (val% «verify_sub» "sp[12]"))], []⟩

/-- The carried sponge after the announced sizes: the first four permuted in, the last four
waiting. -/
def vsF1 (σ : Val) : Fs :=
  ⟨[σ (.n (val% «verify_sub» "nxt[8]@1")), σ (.n (val% «verify_sub» "nxt[9]@1")),
    σ (.n (val% «verify_sub» "nxt[10]@1")), σ (.n (val% «verify_sub» "nxt[11]@1")),
    σ (.n (val% «verify_sub» "nxt[12]@1"))],
    [(σ (.n (val% «verify_sub» "x@5")), dsObserve), (σ (.n (val% «verify_sub» "x@6")), dsObserve),
      (σ (.n (val% «verify_sub» "x@7")), dsObserve), (σ (.n (val% «verify_sub» "x@8")), dsObserve)]⟩

/-- The carried sponge after the root: the last four sizes permuted in, the root's two words
waiting. -/
def vsF2 (σ : Val) : Fs :=
  ⟨[σ (.n (val% «verify_sub» "nxt[8]@2")), σ (.n (val% «verify_sub» "nxt[9]@2")),
    σ (.n (val% «verify_sub» "nxt[10]@2")), σ (.n (val% «verify_sub» "nxt[11]@2")),
    σ (.n (val% «verify_sub» "nxt[12]@2"))],
    [(σ (.n (val% «verify_sub» "x@9")), dsObserve), (σ (.n (val% «verify_sub» "x@10")), dsObserve)]⟩

/-- The out-of-domain grind's nonce. -/
def vsOodNonce (σ : Val) : E := σ (.n (val% «verify_sub» "rate[4]@3"))

/-- The out-of-domain value, at `ood_value`. -/
def vsOodValue (rd : Reader) (σ : Val) : E := (wordsAt rd (σ (.n (val% «verify_sub» "ood_value"))) 1).headD 0

/-- The out-of-domain point, the stack's `stackLog` coordinates at `ood_z`. -/
def vsOodZ (rd : Reader) (σ : Val) (stackLog : ℕ) : List E :=
  wordsAt rd (σ (.n (val% «verify_sub» "ood_z"))) stackLog

/-- The carried sponge after the out-of-domain value: the point's squeezes' capacity, the value
waiting. -/
def vsF3 (rd : Reader) (σ : Val) : Fs :=
  ⟨[σ (.n (val% «verify_sub» "fs0@1")), σ (.n (val% «verify_sub» "fs1@1")),
    σ (.n (val% «verify_sub» "fs2@1")), σ (.n (val% «verify_sub» "fs3@1")),
    σ (.n (val% «verify_sub» "fs4@1"))], [(vsOodValue rd σ, dsObserve)]⟩

/-- The public input's challenge, `packed_message`'s squeeze. -/
def vsRm (σ : Val) : E := σ (.n (val% «verify_sub» "rm"))

/-- The carried sponge after the public input's challenge. -/
def vsF5 (σ : Val) : Fs :=
  ⟨[σ (.n (val% «verify_sub» "fs0@6")), σ (.n (val% «verify_sub» "fs1@6")),
    σ (.n (val% «verify_sub» "fs2@6")), σ (.n (val% «verify_sub» "fs3@6")),
    σ (.n (val% «verify_sub» "fs4@6"))], []⟩

/-- The cursor past the link's words, `verify_keccak`'s. -/
def vsCurK (σ : Val) : E := σ (.n (val% «verify_sub» "fs0@7~8"))

/-- The cursor past the Keccak reduction's words. -/
def vsCurR (σ : Val) : E := σ (.n (val% «verify_sub» "cursor@4"))

/-- The capacity `verify_keccak` returns, the next permutation's. -/
def vsCapK (σ : Val) : List E :=
  [σ (.n (val% «verify_sub» "fs0@7")), σ (.n (val% «verify_sub» "fs1@7")),
    σ (.n (val% «verify_sub» "fs2@7")), σ (.n (val% «verify_sub» "fs3@7")),
    σ (.n (val% «verify_sub» "fs4@7"))]

/-- The ring switch's grind nonce. -/
def vsRingNonce (σ : Val) : E := σ (.n (val% «verify_sub» "rate[0]@5"))

/-- The carried sponge after the ring switch's challenges. -/
def vsF8 (σ : Val) : Fs :=
  ⟨[σ (.n (val% «verify_sub» "nxt[8]@7")), σ (.n (val% «verify_sub» "nxt[9]@7")),
    σ (.n (val% «verify_sub» "nxt[10]@7")), σ (.n (val% «verify_sub» "nxt[11]@7")),
    σ (.n (val% «verify_sub» "nxt[12]@7"))], []⟩

/-- The stack's root, from its halves. -/
def vsRoot (σ : Val) : Digest :=
  digestFromHalves (σ (.n (val% «verify_sub» "x@9")), σ (.n (val% «verify_sub» "x@10")))

/-! ## What the phases leave each other -/

/-- **What the later phases read of the link's end**: its memory term at `r`'s low coordinates
(`below_mem` its scale, `m1` its value), its pointer slices (the `64` words after the `80` sent
values at `cursor@3`), its pieces (`pointerPieces` at the row point at `chi` and the pointer
weights at `eq_q`), its columns (per table, the row point's low coordinates and the sent columns),
the fresh claim's point at `r_pt`, and the `KECCAK` table's point and output lanes (the sent
values at `fs0@7~10`, `cursor@3·g^SENT_OUT_LANES`). -/
def VsLinkFacts (bytecode : List K) (rd : Reader) (σ : Val) (link : LinkEnd) : Prop :=
  ∃ (r chis qPoint : List E),
    ReadsAt rd (σ (.n (val% «verify_sub» "r_pt"))) r ∧ Main.bytecodeLog ≤ r.length ∧
    (vsLayout bytecode σ).logMemory ≤ r.length ∧
    ReadsAt rd (σ (.n (val% «verify_sub» "chi"))) chis ∧
    σ (.n (val% «verify_sub» "g_n")) = gen ^ chis.length ∧
    (∀ t < nTables, (vsLayout bytecode σ).tableLogHeights.getD t 0 ≤ chis.length) ∧
    ReadsAt rd (σ (.n (val% «verify_sub» "eq_q")) * gen ^ guest_const% EQ_Q_AT)
      ((eqKernel qPoint).take (guest_const% N_POINTERS)) ∧
    qPoint.length = guest_const% LINK_Q_VARS ∧
    ReadsAt rd (σ (.n (val% «verify_sub» "cursor@3"))) (link.columns.flatMap fun c ↦ c.2.map (·.2)) ∧
    link.memoryPoint = r.take (vsLayout bytecode σ).logMemory ∧
    link.memoryScales = (σ (.n (val% «verify_sub» "below_mem")),
      eY * σ (.n (val% «verify_sub» "below_mem"))) ∧
    link.memoryValue = σ (.n (val% «verify_sub» "x@11")) ∧
    link.ring.pieces = Stack.pointerPieces (vsLayout bytecode σ) chis qPoint ∧
    ReadsAt rd (σ (.n (val% «verify_sub» "cursor@3")) * gen ^ guest_const% LINK_N_SENT)
      link.ring.slices ∧ link.ring.slices.length = kBits ∧
    link.columns.map (fun c ↦ (c.1, c.2.map (·.1))) =
      tables.zipIdx.map (fun (table, t) ↦
        (chis.take ((vsLayout bytecode σ).tableLogHeights.getD t 0), Stack.nonPointerColumns table)) ∧
    (link.columns.getD opKeccak ([], [])).1 =
      chis.take ((vsLayout bytecode σ).tableLogHeights.getD opKeccak 0) ∧
    ∃ outs : List E, ((List.range keccakStateLanes).mapM fun lane ↦
        ((link.columns.getD opKeccak ([], [])).2.find? fun value ↦ value.1 = keccakOut + lane).map
          (·.2)) = some outs ∧
      ReadsAt rd (σ (.n (val% «verify_sub» "fs0@7~10"))) outs ∧ outs.length = keccakStateLanes

/-- **What the later phases read of the Keccak reduction**: its output claim on `q_keccak` at the
point at `z_vals`, its input point at `z_vals·g^QKECCAK_VARS_CAP`, its `64` slices at `kslices`,
the claim's value `keccak_word`. -/
def VsKeccakFacts (rd : Reader) (σ : Val) (outs : List ColumnClaim) (kp ks : List E) : Prop :=
  ∃ op : List E, outs = [⟨qkeccak, op, σ (.n (val% «verify_sub» "keccak_word"))⟩] ∧
    ReadsAt rd (σ (.n (val% «verify_sub» "z_vals"))) op ∧
    ReadsAt rd (σ (.n (val% «verify_sub» "z_vals")) * gen ^ guest_const% QKECCAK_VARS_CAP) kp ∧
    ReadsAt rd (σ (.n (val% «verify_sub» "kslices"))) ks ∧ ks.length = kBits ∧
    σ (.n (val% «verify_sub» "kb[7]")) * gen ^ qkeccakSlotBits = gen ^ op.length ∧
    kp.length = op.length

/-- **What the opening reads of the ring switch**: the map's challenges `f`, `g` (their Frobenius
coefficients at `c_table`), `rho`, and the batching challenge `lam`. -/
def VsRingFacts (rd : Reader) (σ : Val) (f g : List E) (rho lam : E) : Prop :=
  f.length = 8 ∧ g.length = 8 ∧
    ReadsAt rd (σ (.n (val% «verify_sub» "map_challenges"))) (f ++ g) ∧
    ReadsAt rd (σ (.n (val% «verify_sub» "c_table"))) (ringCoefficients f g) ∧
    rho = σ (.n (val% «verify_sub» "nxt[1]@7")) ∧ lam = σ (.n (val% «verify_sub» "nxt[2]@7"))

/-- `bindPublicInput`'s claims, at the challenge `rm`: each memory limb's line through the public
input's halves. -/
def vsPublicClaims (layout : Layout) (pi : Digest) (rm : E) : List ColumnClaim :=
  let halves := digestHalves pi
  Stack.publicClaimsPure layout rm
    (multilinearEval [ofK (halves.1.limb 0), ofK (halves.2.limb 0)] [rm])
    (multilinearEval [ofK (halves.1.limb 1), ofK (halves.2.limb 1)] [rm])

/-! ## The phases -/

/-- **The seed**: the seed's `KECCAK` writes the capacity of `keccakF (seedInput seed pi)`. -/
def PhSeed : Prop :=
  ∀ (bytecode : List K) {κ : ℕ} (L : MemoryImage κ) (C : CallRel) (V : FrameMap) (σ : Val)
    (rets : List E), VsRun bytecode L C V σ rets →
      (vsF0 σ).Carries ⟨keccakF1600 (seedInput (vsSeed σ) (vsPi σ)), [], none⟩

/-- **The announced sizes**: the eight words at `stream` run `readAnnouncedSizes` to the layout
`buildLayout` gives and the rate; its stack's log is in range, and the dispatches' selectors are
`size_sel = g^(stackLog - 16)` and `rate_sel = rateSel lir`. -/
def PhSizes : Prop :=
  ∀ (bytecode : List K) {κ : ℕ} (L : MemoryImage κ) (C : CallRel) (V : FrameMap) (σ : Val)
    (rets : List E), VsRun bytecode L C V σ rets →
      ReadsAt L.read (vsStream σ) (vsAnnounced σ) ∧
      RunsTo (readAnnouncedSizes bytecode) (vsF0 σ) (vsAnnounced σ)
        (vsLayout bytecode σ, vsLir σ) (vsF1 σ) ∧
      buildLayout bytecode (vsLogMem σ) (vsRows σ) = some (vsLayout bytecode σ) ∧
      1 ≤ vsLir σ ∧ vsLir σ ≤ 4 ∧
      Whir.minOpenLog ≤ (vsLayout bytecode σ).stackLog ∧ (vsLayout bytecode σ).stackLog ≤ 30 ∧
      σ (.n (val% «verify_sub» "size_sel")) =
        ofK (addressOfIndex ((vsLayout bytecode σ).stackLog - Whir.minOpenLog)) ∧
      σ (.n (val% «verify_sub» "rate_sel")) = Whir.rateSel (vsLir σ)

/-- **The root**: its two words follow the sizes, absorbed after the last four sizes'
permutation. -/
def PhRoot : Prop :=
  ∀ (bytecode : List K) {κ : ℕ} (L : MemoryImage κ) (C : CallRel) (V : FrameMap) (σ : Val)
    (rets : List E), VsRun bytecode L C V σ rets →
      ReadsAt L.read (vsStream σ * gen ^ 8)
        [σ (.n (val% «verify_sub» "x@9")), σ (.n (val% «verify_sub» "x@10"))] ∧
      (((vsF1 σ).absorb (σ (.n (val% «verify_sub» "x@9"))) dsObserve).absorb
        (σ (.n (val% «verify_sub» "x@10"))) dsObserve) = vsF2 σ

/-- **The out-of-domain sample**: its grind's nonce and its value follow the root and run
`readOod` at the stack's log, the point at `ood_z`. -/
def PhOod : Prop :=
  ∀ (bytecode : List K) {κ : ℕ} (L : MemoryImage κ) (C : CallRel) (V : FrameMap) (σ : Val)
    (rets : List E), VsRun bytecode L C V σ rets →
      ReadsAt L.read (vsStream σ * gen ^ 10) [vsOodNonce σ, vsOodValue L.read σ] ∧
      RunsTo (readOod (vsLayout bytecode σ).stackLog) (vsF2 σ) [vsOodNonce σ, vsOodValue L.read σ]
        (fun x ↦ eqEval (vsOodZ L.read σ (vsLayout bytecode σ).stackLog) x, vsOodValue L.read σ)
        (vsF3 L.read σ) ∧
      ReadsAt L.read (σ (.n (val% «verify_sub» "ood_z")))
        (vsOodZ L.read σ (vsLayout bytecode σ).stackLog)

/-- **The link**: its words follow the out-of-domain value and run `verifyLink` with the fresh
claim's split; the public input's challenge `rm` is the next squeeze, and the link's end is as
`VsLinkFacts` says. -/
def PhLink : Prop :=
  ∀ (bytecode : List K) {κ : ℕ} (L : MemoryImage κ) (C : CallRel) (V : FrameMap) (σ : Val)
    (rets : List E), VsRun bytecode L C V σ rets →
      ∃ (xs : List E) (link : LinkEnd) (s : Fs),
        ReadsAt L.read (vsStream σ * gen ^ 12) xs ∧ vsCurK σ = vsStream σ * gen ^ (12 + xs.length) ∧
        RunsTo (verifyLink (freshSplit (vsFresh L.read σ)) (vsLayout bytecode σ)) (vsF3 L.read σ) xs
          link s ∧
        s.squeeze = (vsRm σ, vsF5 σ) ∧ VsLinkFacts bytecode L.read σ link

/-- **The Keccak reduction**: on the link's end, its words run `keccakValidity`, leaving a full
queue whose permutation's capacity `verify_keccak` returns. -/
def PhKeccak : Prop :=
  ∀ (bytecode : List K) {κ : ℕ} (L : MemoryImage κ) (C : CallRel) (V : FrameMap) (σ : Val)
    (rets : List E), VsRun bytecode L C V σ rets → ∀ link : LinkEnd,
      VsLinkFacts bytecode L.read σ link →
      ∃ (xs : List E) (outs : List ColumnClaim) (kp ks : List E) (s : Fs),
        ReadsAt L.read (vsCurK σ) xs ∧ vsCurR σ = vsCurK σ * gen ^ xs.length ∧
        RunsTo (keccakValidity (vsLayout bytecode σ) link) (vsF5 σ) xs (outs, kp, ks) s ∧
        s.pend.length = rateScalars ∧ capOf s.perm = vsCapK σ ∧ VsKeccakFacts L.read σ outs kp ks

/-- **The ring switch**: on the Keccak reduction's input slices and the link's pointer slices, its
grind's nonce runs `ringSwitch`, the batching challenge `lam` at `nxt[2]@7`. -/
def PhRing : Prop :=
  ∀ (bytecode : List K) {κ : ℕ} (L : MemoryImage κ) (C : CallRel) (V : FrameMap) (σ : Val)
    (rets : List E), VsRun bytecode L C V σ rets → ∀ (link : LinkEnd) (outs : List ColumnClaim)
      (kp ks : List E) (s : Fs) (qp : Placement),
      VsLinkFacts bytecode L.read σ link → VsKeccakFacts L.read σ outs kp ks →
      s.pend.length = rateScalars → capOf s.perm = vsCapK σ →
      (vsLayout bytecode σ).placements.getD qkeccak none = some qp →
      ∃ (f g : List E) (rho lam : E),
        LoadHolds L.read (vsCurR σ) 0 (vsRingNonce σ) ∧
        RunsTo (ringSwitch [keccakRingClaim qp kp ks, link.ring]) s [vsRingNonce σ]
          (ringMerge [keccakRingClaim qp kp ks, link.ring] f g rho, lam) (vsF8 σ) ∧
        VsRingFacts L.read σ f g rho lam

/-- **The stacked opening**: `open_stacked`'s words and openings, at the cursor past the ring
switch's nonce, run `verifyStackedOpening` on the verifier's claims (the merged ring claim, the
memory term, the column claims with a placement, the out-of-domain claim) from the root's
commitment. -/
def PhOpen : Prop :=
  ∀ (bytecode : List K) {κ : ℕ} (L : MemoryImage κ) (C : CallRel) (V : FrameMap) (σ : Val)
    (rets : List E), VsRun bytecode L C V σ rets → ∀ (link : LinkEnd) (outs : List ColumnClaim)
      (kp ks f g : List E) (rho lam : E) (qp : Placement) (memoryTerm : StackClaim),
      VsLinkFacts bytecode L.read σ link → VsKeccakFacts L.read σ outs kp ks →
      VsRingFacts L.read σ f g rho lam →
      (vsLayout bytecode σ).placements.getD qkeccak none = some qp →
      Stack.memoryTermPure (vsLayout bytecode σ) link = some memoryTerm →
      vsCursor σ = vsCurR σ * gen ∧
      ∃ (s : Fs) (roots : List (Digest × ℕ × ℕ)),
        Whir.RunsWith (verifyStackedOpening (vsLayout bytecode σ).stackLog (vsLir σ)
            (ringMerge [keccakRingClaim qp kp ks, link.ring] f g rho :: memoryTerm ::
              (linkColumnClaims link ++ vsPublicClaims (vsLayout bytecode σ) (vsPi σ) (vsRm σ) ++
                outs).filterMap (·.onStack (vsLayout bytecode σ)) ++
              [(fun x ↦ eqEval (vsOodZ L.read σ (vsLayout bytecode σ).stackLog) x,
                vsOodValue L.read σ)]) lam)
          (vsF8 σ)
          (vsOsW L.read V ((vsLayout bytecode σ).stackLog - Whir.minOpenLog) (vsLir σ) (vsOsArgs σ)
            (vsOsRets σ)).1
          (vsOsW L.read V ((vsLayout bytecode σ).stackLog - Whir.minOpenLog) (vsLir σ) (vsOsArgs σ)
            (vsOsRets σ)).2
          [(vsRoot σ, Whir.stackShape (vsLayout bytecode σ).stackLog (vsLir σ))] () s roots

/-- **The export**: nothing returned, the fresh claim's cells at `defer_out`. -/
def PhExport : Prop :=
  ∀ (bytecode : List K) {κ : ℕ} (L : MemoryImage κ) (C : CallRel) (V : FrameMap) (σ : Val)
    (rets : List E), VsRun bytecode L C V σ rets →
      rets = [] ∧ ReadsAt L.read (σ (.n (val% «verify_sub» "defer_out"))) (vsFresh L.read σ).cells

end
end LeanVM.Guest.B1.VerifySub
