/-
  LeanVM.Guest.B1.Sig.Interface

  What the signature verifiers of the aggregation guest establish, as named statements: the
  interface `main`'s proof composes, the proofs landing under the same names.
-/

module

public import LeanVM.Guest.CoreData
public import LeanVM.Guest.CoreLemmas
public import Statement.LeanVmGuest
public import LeanXmss.Scheme
public import Statement.LeanSphincs
public import Statement.Fast.Schemes
public import LeanDa.Scheme
public import Statement.Fast.Keccak
public import Statement.Fast.QuadExt
public import Statement.Fast.FieldWords
public import LeanVM.Facts.Verifier
public import LeanVM.Guest.B1.Main.Frames
public import LeanVM.Guest.B1.Sig.XmssSegT
public import LeanVM.Guest.B1.Sig.Frame

/-!
# The signature verifiers' interface

`verify_lean_xmss(signer, tags)` (`lean_ethereum.py:3655-3728`, inline in `main`'s raw-leanXMSS loop
`__loop2`, `Data.core36`, as its statements `xSeg`) and
`verify_sig_lean_sphincs(signer, byte_bits)` (`lean_ethereum.py:3951-4052` at leanVM main 40f877dc,
`Data.core20`) check one signature of the claim at `signer`: four cells, the key (leanXMSS: its root
and parameter; leanSPHINCS: `PK.seed` and `PK.root`), then the message's two halves, the low
first. `verify_lean_xmss` calls nothing (every helper is `@inline`
and every `match` arm runs in the frame), so its statements hold under any call relation; its chain
indices other than `0` and the powers of two are `__loop2`'s parameters `.n 5` to `.n 55`, which
`main` sets (`LxTagsHold`);
`verify_sig_lean_sphincs` calls `sp_wots` (`Data.core19`) once per layer, so its soundness is
stated under a call relation that unfolds at a frame map (`UnfoldsV`), the signature read off its
valuation and the frames of its calls.

**The decoding of a claim.** A cell `c` is the 128-bit value of its two low limbs, limb `0` the
low (`cellVal`; the `KECCAK` instructions that read the cells make them canonical); the message is
the two cells, the first low (`cellPairVal`). `xmssClaimOf a b c d`, `sphincsClaimOf a b c d` are
the claims of the four cells, as `Node.XmssClaim`, `Node.SphincsClaim`.

**What a call establishes for a signature** (`XmssOut rd p sig`, `SphincsOut rd p sig`): the four
words at `p` are a claim that `sig` verifies under Keccak-256 (`Node.xmssVerify`,
`Node.sphincsVerify`). `XmssSigned`, `SphincsSigned` are their existentials.

**The statements** (`…_Spec`, each a `Prop`; the proofs land as `…_holds`):

* `verify_lean_xmss_sound_Spec sigOf`: whenever the check holds of a valuation `σ` before `rest`,
  `rest` holds, and with the carried chain indices held `sigOf σ`, the signature read off the
  valuation, verifies the claim at the pointer `σ (.n 65)`. The decoder of the end theorem reads
  the signature this way, through the frame of the loop's iteration.
* `verify_sig_lean_sphincs_sound_Spec sigOf`: the same for leanSPHINCS, under a call relation that
  unfolds at a frame map `V`, the signature `sigOf σ V` read off the valuation and the frames of
  its `sp_wots` calls, on a memory image of at most `2^32` words (the range checks of
  `sp_from_bytes` are bounded discrete logarithms there, `rangeCheck_iff`), when its `byte_bits`
  argument holds the table `main` writes (`ByteBits`: `byte_bits[g^v] = v`): the counters are then
  32-bit integers, so the encodings' bytes are the scheme's.
* `verify_lean_xmss_complete_Spec`: for a claim held at the pointer in its canonical cells and a
  signature that verifies it, the carried chain indices held, on a memory of at least `256` words, so
  that every range check has its witnesses, the check holds of a valuation changing only its own
  values (`Completes`), under any call relation.
  leanSPHINCS's completeness statements are in `SphincsCompleteSpec`.

From them, the check gives the claim signed (`verify_lean_xmss_signed`) and the call relation
(`coreProgram.Rel`) gives it for leanSPHINCS (`verify_sig_lean_sphincs_signed`): proved here, from
the `Spec`s as hypotheses.
-/

namespace LeanVM.Guest.B1.Sig

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core

@[expose] public section

/-! ## Cells as the schemes' values -/

/-- A cell's 128-bit value: limb `0` the low 64 bits, limb `1` the high (limb `2` dropped). -/
def cellVal (c : E) : BitVec 128 := (c.limb 1).toBitVec ++ (c.limb 0).toBitVec

/-- The canonical cell of a 128-bit value. -/
def cellOf128 (v : BitVec 128) : E :=
  E.ofLimbs (BF64.ofBitVec (v.extractLsb' 0 64)) (BF64.ofBitVec (v.extractLsb' 64 64)) 0

/-- The 256-bit value of two cells, the first low. -/
def cellPairVal (lo hi : E) : BitVec 256 := cellVal hi ++ cellVal lo

/-- The leanXMSS claim of four cells: the key's root and parameter, the message's halves. -/
def xmssClaimOf (a b c d : E) : Node.LeanXmssClaim := (⟨cellVal a, cellVal b⟩, cellPairVal c d)

/-- The leanSPHINCS claim of four cells. -/
def sphincsClaimOf (a b c d : E) : Node.LeanSphincsClaim := (⟨cellVal a, cellVal b⟩, cellPairVal c d)

/-- The four words at `p`: `a`, `b`, `c`, `d` at offsets `0` to `3`. -/
def ClaimAt (rd : Reader) (p a b c d : E) : Prop :=
  LoadHolds rd p 0 a ∧ LoadHolds rd p 1 b ∧ LoadHolds rd p 2 c ∧ LoadHolds rd p 3 d

/-! ## What a call establishes -/

/-- **What `verify_lean_xmss(p)` establishes for the signature `sig`**: the four words at `p` are a
leanXMSS claim that `sig` verifies under Keccak-256. -/
def XmssOut (rd : Reader) (p : E) (sig : LeanXmss.Signature) : Prop :=
  ∃ a b c d, ClaimAt rd p a b c d ∧
    LeanXmss.verifyWithKeccak (xmssClaimOf a b c d).1 (xmssClaimOf a b c d).2 sig = true

/-- **What `verify_sig_lean_sphincs(p, _)` establishes for the signature `sig`**: the four words at
`p` are a leanSPHINCS claim that `sig` verifies under Keccak-256. -/
def SphincsOut (rd : Reader) (p : E) (sig : Sphincs.Signature) : Prop :=
  ∃ a b c d, ClaimAt rd p a b c d ∧
    Sphincs.verifyWithKeccak (sphincsClaimOf a b c d).1 (sphincsClaimOf a b c d).2 sig = true

/-- Some leanXMSS signature verifies the claim at `p`. -/
def XmssSigned (rd : Reader) (p : E) : Prop := ∃ sig, XmssOut rd p sig

/-- Some leanSPHINCS signature verifies the claim at `p`. -/
def SphincsSigned (rd : Reader) (p : E) : Prop := ∃ sig, SphincsOut rd p sig

/-! ## Preconditions -/

/-- **The byte table** `main` writes (`lean_ethereum.py:4573-4575`): `byte_bits[g^v] = v` for every
byte `v`, the word whose bits spell `v`. -/
def ByteBits (rd : Reader) (bb : E) : Prop := ∀ v < 256, LoadHolds rd bb v (word v 0 0)

/-- The memory holds a word at each of the first `n` addresses `g^i`: a range check below `n` has
its witnesses. -/
def MemOK (rd : Reader) (n : ℕ) : Prop := ∀ i < n, (rd (addressOfIndex i)).isSome

/-! ## The statements -/

/-- **`verify_lean_xmss` is sound, inline in `__loop2`, for the signature `sigOf` reads off the
loop's valuation**: whenever the check `xSeg` holds of `σ` before `rest` (under any call relation:
it calls nothing), `rest` holds, and when the carried chain indices (`.n 5` to `.n 55`) hold their
indices, `sigOf σ` verifies the claim at the pointer `σ (.n 65)`. -/
def verify_lean_xmss_sound_Spec (sigOf : Val → LeanXmss.Signature) : Prop :=
  ∀ (C : CallRel) (rd : Reader) (σ : Val) (rest : List Stmt) (next : Prop) (kret : List E → Prop),
    Stmt.HoldsList C rd σ (xSeg ++ rest) next kret →
      Stmt.HoldsList C rd σ rest next kret ∧
        (LxTagsHold (fun j => σ (sTagParam j)) → XmssOut rd (σ sSigner) (sigOf σ))

/-- **`verify_sig_lean_sphincs` is sound, for the signature `sigOf` reads off its valuation and the
frame map**: under a call relation `C` that unfolds at the frame map `V`, on a memory image of at
most `2^32` words, whenever its body holds of `σ`, it returns no words, and when its second
argument `σ (.n 1)` holds the byte table, `sigOf σ V` verifies the claim at its first argument
`σ (.n 0)`. -/
def verify_sig_lean_sphincs_sound_Spec (sigOf : Val → FrameMap → Sphincs.Signature) : Prop :=
  ∀ (C : CallRel) (V : FrameMap) {κ : ℕ} (L : MemoryImage κ), κ ≤ 32 → UnfoldsV L.read C V →
    ∀ (σ : Val) (rets : List E),
      Stmt.HoldsList C L.read σ Data.core20.body False (fun rs => rs = rets) →
        rets = [] ∧ (ByteBits L.read (σ (.n 1)) → SphincsOut L.read (σ (.n 0)) (sigOf σ V))

/-- **`verify_lean_xmss` is complete, inline in `__loop2`**: for a claim held at the pointer
`σ (.n 65)` in its canonical cells and a signature that verifies it, the carried chain indices
holding their indices, on a memory of at least `256` words (the windows and the digit words are
range-checked below `g^255`), the check `xSeg` holds of a valuation
changing `σ` only on its own values `66 ..< 120764`, under any call relation. -/
def verify_lean_xmss_complete_Spec : Prop :=
  ∀ (C : CallRel) (rd : Reader) (σ : Val) (pk : HashSig.PublicKey) (m : HashSig.Message)
    (sig : LeanXmss.Signature), MemOK rd 256 → LxTagsHold (fun j => σ (sTagParam j)) →
    ClaimAt rd (σ sSigner) (cellOf128 pk.root) (cellOf128 pk.parameter)
      (cellOf128 (m.extractLsb' 0 128)) (cellOf128 (m.extractLsb' 128 128)) →
    LeanXmss.verifyWithKeccak pk m sig = true →
      Completes C rd 66 120764 xSeg σ (fun _ => True)

/-! ## The functions, found -/

theorem core20_params : Data.core20.params = [.n 0, .n 1] := rfl

theorem find_verify_sig_lean_sphincs :
    coreProgram.find? "verify_sig_lean_sphincs" = some Data.core20 :=
  Program.find?_of_indexOf? (j := 20) (by decide +kernel) rfl

/-! ## The call relation, from the statements -/

variable {rd : Reader}

theorem rel_iff_body {name : String} {fn : Fn} (h : coreProgram.find? name = some fn)
    (args rets : List E) :
    coreProgram.Rel rd name args rets ↔
      ∃ σ : Val, fn.params.map σ = args ∧
        Stmt.HoldsList (coreProgram.Rel rd) rd σ fn.body False (fun rs => rs = rets) := by
  rw [rel_iff]
  simp only [h, Option.some.injEq, exists_eq_left', Fn.Sem]

/-- **The check in `__loop2`**: `rest` holds, and with the carried chain indices held the claim at
the pointer is signed. -/
theorem verify_lean_xmss_signed {sigOf : Val → LeanXmss.Signature}
    (hs : verify_lean_xmss_sound_Spec sigOf) {C : CallRel} {σ : Val} {rest : List Stmt}
    {next : Prop} {kret : List E → Prop} (h : Stmt.HoldsList C rd σ (xSeg ++ rest) next kret) :
    Stmt.HoldsList C rd σ rest next kret ∧
      (LxTagsHold (fun j => σ (sTagParam j)) → XmssSigned rd (σ sSigner)) :=
  let r := hs C rd σ rest next kret h
  ⟨r.1, fun ht => ⟨_, r.2 ht⟩⟩

/-- **A call of `verify_sig_lean_sphincs`** on a memory image of at most `2^32` words takes two
arguments, returns nothing, and when the second holds the byte table the claim at the first is
signed. -/
theorem verify_sig_lean_sphincs_signed {sigOf : Val → FrameMap → Sphincs.Signature}
    (hs : verify_sig_lean_sphincs_sound_Spec sigOf) {κ : ℕ} {L : MemoryImage κ} (hκ : κ ≤ 32)
    {args rets : List E} (h : coreProgram.Rel L.read "verify_sig_lean_sphincs" args rets) :
    ∃ p bb, args = [p, bb] ∧ rets = [] ∧ (ByteBits L.read bb → SphincsSigned L.read p) := by
  obtain ⟨σ, hp, hb⟩ := (rel_iff_body find_verify_sig_lean_sphincs args rets).mp h
  obtain ⟨hr, ho⟩ := hs _ (relV L.read) L hκ (unfoldsV_rel L.read) σ rets hb
  exact ⟨σ (.n 0), σ (.n 1), by rw [← hp]; rfl, hr, fun hbb => ⟨_, ho hbb⟩⟩

end
end LeanVM.Guest.B1.Sig
