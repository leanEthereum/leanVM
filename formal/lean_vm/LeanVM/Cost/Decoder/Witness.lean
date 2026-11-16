module

public import LeanVM.Cost.Decoder.Frames
public import LeanVM.Guest.Located.Replay
public import LeanVM.Cost.Decoder.GuestPlaces
import all LeanVM.Guest.Located.Replay
import all LeanVM.Guest.PlaceCode

/-!
# The guest decoder's compiled chain: the witness and `main`'s valuation

* **`decWitN`, staged** (`decWitNStaged`, the logarithm's tables `D`, the readers' tables `R` and
  the leanSPHINCS reader given; `Equations.lean`: at `sphincsAtFrame readerTabs σ Vn` it is
  `Guest.Fast.decWitN`):
  `decWitStaged` (`Staged.lean`) with each callee's witness off its frame (`Frames.lean`), by
  partial application; `Guest.Fast.decWitN` is the deployed decoder's witness at the frame map
  keyed by index (`decWitN_eq`, `decode_eq_numbered`);
* **`main`'s valuation** off the reader (`mainVal`: `EndFinal.mainValWith`'s word, by the back
  end's places, read off the literal table `guestPlaces`).
-/

namespace LeanVM.Cost.Decoder

open LeanVM.Cost LeanVM.Parameters LeanVM.Guest.Core LeanVM.Guest.B1 LeanVM.Guest.B1.Main
open LeanVM.Protocol.Verifier LeanVM.Node

@[expose] public section

open LeanVM.Guest.Fast in
/-- **`decWitN`, staged**: `decWitStaged` with each callee's witness off its frame, by partial
application, the signatures' readers `wX`, `wS` given (the top's, `xmssAtFrameT`, `sphincsAtFrameT`,
look their frames up once; `xmssAtFrame`, `sphincsAtFrame` at the frame map). -/
noncomputable def decWitNStaged (D : LeanVM.Extraction.Fast.DiscreteLogTables) (R : ReaderTabs)
    (σ : Val) (rd : Reader) (Vn : NFrames) (wX : List E → LeanXmss.Signature)
    (wS : E → Sphincs.Signature) (cl : E → E → ℕ) : NodeWitness :=
  decWitStaged D σ rd wX wS (daAtFrame D Vn) (proofAtFrame R rd Vn cl)
    (hintsAtFrame rd Vn)

-- a frame cell's word, under a name of its own (the bounds name it, not an index)
cost_compile wordWithC := LeanVM.Guest.Located.wordWith
cost_compile decWitNC := decWitNStaged

/-! ## A place's word

`Guest.placeWith rd fp c`, the word place code `c` names at the frame `fp`, compiled as
`placeWord`: the cell's word read once, a shifted place's product by `g^e` limb by limb (`mulK`).
-/

open LeanVM.Guest.Located in
/-- **The word place code `c` names** at the frame `fp` (`Guest.placeWith`), as the decoder
computes it. -/
def placeWord (rd : Reader) (fp : K) (c : ℕ) : E :=
  if c = 0 then 0
  else if c < 2 ^ 20 then wordWith rd fp c
  else mulK (wordWith rd fp (c % 2 ^ 20)) (addressOfIndex (c / 2 ^ 20 - 1))

theorem placeWith_eq_placeWord (rd : Reader) (fp : K) (c : ℕ) :
    LeanVM.Guest.placeWith rd fp c = placeWord rd fp c := by
  unfold LeanVM.Guest.placeWith placeWord LeanVM.Guest.Located.wordWith mulK
  split_ifs
  · rfl
  · rfl
  · rw [LeanVM.Guest.Value.eq_ofLimbs ((rd (fp * addressOfIndex (c % 2 ^ 20))).getD 0),
      LeanVM.Guest.Value.ofLimbs_mul_ofK]
    simp only [LeanVM.Guest.Value.ofLimbs_limb0, LeanVM.Guest.Value.ofLimbs_limb1]

set_option maxRecDepth 100000 in
cost_compile placeWordC := placeWord
cost_rewrite placeWith_eq_placeWord

/-! ## The guest's table of places, held once -/

/-- **The guest's place codes**, a function of no argument whose body is the literal
(`guestPlacesLit`, `Rule.literalNatArrays`): every use of `guestPlaces` calls it
(`guestPlaces_eq_table`), so the program holds the table once, however many readers read it. -/
def guestPlacesTable : Array (Array ℕ) := guestPlacesLit

theorem guestPlaces_eq_table : guestPlaces = guestPlacesTable := rfl

set_option maxRecDepth 100000 in
cost_compile guestPlacesTableC := guestPlacesTable
cost_rewrite guestPlaces_eq_table

/-! ## `main`'s valuation -/

/-- The word of `main`'s value `v` at `fp = 1`, read with `rd`: its place read off `main`'s row of
the guest's table of places (`guestPlaces`, the literal held once, `guestPlacesTable`), in `O(1)`
whatever `v` (`Equations.lean`: `mainVal_eq`). -/
def mainVal (rd : Reader) (v : V) : E :=
  LeanVM.Guest.placeWith rd 1 ((guestPlaces.getD 1 #[]).getD v.idx 0)

cost_compile mainValC := mainVal

end

end LeanVM.Cost.Decoder
