/-
  LeanVM.Guest.B1.Sig.SphincsSig

  The leanSPHINCS signature `verify_sig_lean_sphincs` checks, read off its valuation and the frames
  of its three `sp_wots` calls.
-/

module

public import LeanVM.Guest.B1.Sig.SphincsT
public import LeanVM.Guest.B1.Sig.SphincsAdrs
public import LeanVM.Guest.B1.Sig.SpWotsLayout
public import LeanVM.Guest.B1.Sig.Codeword
public import LeanVM.Guest.B1.Sig.Bytes
public import LeanVM.Guest.B1.Main.FramesP

/-!
# The signature `verify_sig_lean_sphincs` checks

`sphincsSigOf σ V` reads the signature off `verify_sig_lean_sphincs`'s valuation `σ` and the
frame map `V`; it mentions no hash.

* the randomizer `R`, `n6` (`sRand`, `sp_rand`);
* FORS tree `c`'s opening (`sForsOpeningOf`): its secret at the tree's base (`sForsBase c`), and
  at each height `z` the hinted child that is not the node climbed (`siblingOf`, at
  `sForsKid c z`; `SphincsForsT`'s): `is_child`'s bit names the climbed one;
* layer `l`'s signature (`sLayerOf`): its counter, its four bytes (`sCtrOf l`, hinted most
  significant first and read lowest first, `sp_from_bytes`) reversed, `beWordAt 0`; its
  chain values, the chain starts of the frame `V "sp_wots" [PK.seed, a0, a1, enc] [leaf]` of the
  layer's call (`sChainValuesOf`); its path, the sibling of each level of `sp_path` (at
  `sPathKid l j`).

The positions are the template's (`sBody`, `SphincsT`, `SphincsForsT`).
-/

namespace LeanVM.Guest.B1.Sig

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core

@[expose] public section

/-! ## Positions -/

/-- **The hinted pair of FORS tree `c`'s level `z`** (`z < 10`, the children of the node at
height `z + 1`): after the tree's secret, its leaf's address and the leaf's hash (9 values), the
levels below, level `j` taking `forsLevelW c j` values (its parent's address `forsAtW c (j + 1)`,
which depends on the tree's place). -/
def sForsKid (c z : Nat) : Nat := sForsBase c + 9 + ((List.range z).map (forsLevelW c)).sum

/-- **The hinted pair of layer `l`'s path level `j`**, after the counter (37 values), `enc_at` (2),
the encoding (8) and the leaf: a level takes 13 values, the top layer's level `0` 16 (its parent's
index two bytes), the root's level 10. -/
def sPathKid (l j : Nat) : Nat :=
  sLayerBase l + 48 + 13 * j + (if l = 2 ∧ 0 < j then 3 else 0)

/-! ## Reading the values -/

/-- **The chain values `sp_wots`'s frame `σ` holds**: chain `i`'s start, hinted in the arm its
group's dispatch takes, the group's digit word the exponent of its selector (`spState`, `spN`,
`spStartAt`), in the guest's numbering (`spRen`). -/
noncomputable def sChainValuesOf (σ : Val) : Sphincs.ChainIndex → HashSig.Digest :=
  fun i => cellVal (σ (spRen (spStartAt (fun p => logG (σ (spRen (.n (spState p).2.2))) (4 ^ spN p))
    i.val)))

/-- **FORS tree `c`'s opening**: its secret, and the sibling at each height. -/
def sForsOpeningOf (σ : Val) (c : Nat) : Sphincs.ForsTreeOpening where
  secret := cellVal (σ (.n (sForsBase c)))
  path z := cellVal (siblingOf σ (sForsBit (10 * c + z.val)) (sForsKid c z.val))

/-- **Layer `l`'s one-time signature and path**, its chain values off the frame of its call. -/
noncomputable def sLayerOf (σ : Val) (V : FrameMap) (l : Sphincs.Layer) :
    Sphincs.LayerSignature l where
  counter := BitVec.ofNat 32 (beWordAt 0 (cellNat (σ (sCtrOf l.val))))
  chainValues := sChainValuesOf
    (V "sp_wots" [σ sPP, σ (sA0Of l.val), σ (sA1Of l.val), σ (sEncOf l.val)] [σ (sLeafOf l.val)])
  authenticationPath j :=
    cellVal (siblingOf σ (sLeafBit (sOffOf l.val + j.val)) (sPathKid l.val j.val))

/-- **The leanSPHINCS signature `verify_sig_lean_sphincs` checks**, read off its valuation `σ` and
the frame map `V`. -/
noncomputable def sphincsSigOf (σ : Val) (V : FrameMap) : Sphincs.Signature where
  randomizer := cellVal (σ sRand)
  forsOpening c := sForsOpeningOf σ c.val
  layers l := sLayerOf σ V l

end
end LeanVM.Guest.B1.Sig
