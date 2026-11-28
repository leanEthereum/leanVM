/-
  LeanVM.Guest.B1.VsC.VkPH

  `verify_keccak` placed: its eighteen callees, one after the other (`KidsAtF`), on any valuation
  giving their honest words.
-/

module

public import LeanVM.Guest.B1.VsC.VkPG
public import LeanVM.Guest.B1.VsC.CopyLoopA
public import LeanVM.Guest.B1.VsC.PlainA
import LeanVM.Guest.ValRef
import LeanVM.Guest.Data.ValNames.«verify_keccak»

/-!
# The callees

From the cursor `c + τ + 412` past `verify_keccak`'s buffers: `verify_keccak_loop0` (`cl_placed`),
the twelve layers (`KeccakLayerCompleteA`, each at the aligned base past the previous one's end,
its end chosen, `posP`), the committed outputs' rounds (`plain60_placed`), `verify_keccak_loop1`,
the inputs' rounds (`plain41_placed`), their opening's (`plain60_placed`), `verify_keccak_loop2`.
`vk_kids`: on any valuation and calls carrying the honest words (`HonestCalls`), they complete one
after the other, loading from the caller's words, `verify_keccak`'s buffers and the earlier
layers' buffers; at the end the memory holds each layer's next claim.
-/

namespace LeanVM.Guest.B1.VerifySub

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Guest.Memory LeanVM.Guest.B1.Fwd LeanVM.Guest.Complete
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Protocol.KeccakGkr Finset LeanVM.Guest.B1.VerifySub.KL
open LeanVM.Prover.Exec (allocBase)

open LeanVM.Guest.B1.VsC (PostQuiet lpB clArgs plain60_placed plain41_placed)

@[expose] public section

namespace VkData

variable (D : VkData) (fs : String → ℕ) (al : String → Bool) (cert : String → V → ℕ) (k : ℕ)
variable (c curE chiE olE zvE slE tbE : ℕ)

/-- Layer `s`'s specialization. -/
def lname (s : ℕ) : String := layerName (firstOf s)

/-- The pointers of claim `s`'s record into its point, lanes, local point and flips, the previous
layer's buffers at `cbp` (the first claim's: `verify_keccak`'s point and lane tree, its two unused
pointers the claim records'). -/
def recPtrs (s cbp : ℕ) : E × E × E × E :=
  if s = 0 then (VsC.ptrAtV c, VsC.ptrAtV (c + D.o274 + 30), VsC.ptrAtV (c + D.o201), VsC.ptrAtV (c + D.o201))
  else (VsC.ptrAtV cbp, VsC.ptrAtV (cbp + (D.τ - 3) + 11), VsC.ptrAtV (cbp + (D.τ - 3)),
    VsC.ptrAtV (cbp + (D.τ - 3) + 36))

/-- Layer `s`'s arrays (`klArrays`). -/
def lArr (s cbp : ℕ) : List (E × ℕ) :=
  VsC.klArrays (VsC.ptrAtV (c + D.o201 + 22 * s)) (D.recPtrs c s cbp).1 (D.recPtrs c s cbp).2.1
    (D.recPtrs c s cbp).2.2.1 (D.recPtrs c s cbp).2.2.2 (VsC.ptrAtV (curE + D.lcur s))
    (VsC.ptrAtV (c + D.o201 + 22 * (s + 1))) (VsC.ptrAtV tbE) (D.τ - 3)
    (VsC.klXs (D.T s).1 (D.T s).2.1 (D.T s).2.2.1 (D.T s).2.2.2.1 (D.T s).2.2.2.2).length

/-- What layer `s` loads from: `verify_keccak`'s buffers, the stream, the window table, the previous
layer's buffers at `cbp`. -/
def lR (s cbp : ℕ) (i : ℕ) : Prop :=
  (c ≤ i ∧ i < c + D.τ + 412) ∨ (curE ≤ i ∧ i < curE + D.xs.length) ∨
    (tbE ≤ i ∧ i < tbE + 2 ^ winTabBits) ∨ (1 ≤ s ∧ cbp ≤ i ∧ i < cbp + (D.τ - 3) + 43)

/-- **Layer `s` completes at frame `fp`** (`KeccakLayerCompleteA`'s conclusion), ending at `e`. -/
def LP (s cbp fp e : ℕ) : Prop :=
  fp + fs (lname s) + (D.τ - 3) + 43 ≤ e ∧ ((∀ f, fs f < 2 ^ 16) → e ≤ fp + fs (lname s) + 2 ^ 18) ∧
  CallAtA fs al cert k (lname s)
    [(D.layer s).cap.getD 0 0, (D.layer s).cap.getD 1 0, (D.layer s).cap.getD 2 0,
      (D.layer s).cap.getD 3 0, (D.layer s).cap.getD 4 0, (D.cells s).1, (D.cells s).2,
      VsC.ptrAtV (curE + D.lcur s), gen ^ (D.τ - 3), gen ^ ((D.τ - 3) / krStep),
      gen ^ ((D.τ - 3) % krStep), VsC.ptrAtV (c + D.o201 + 22 * s),
      VsC.ptrAtV (c + D.o201 + 22 * (s + 1)), keccakIota D.τ s (D.layer s).c, VsC.ptrAtV tbE]
    ((layerBeta (D.layer s).c (plainStart (firstOf s) [(D.layer s).cap.getD 0 0, (D.layer s).cap.getD 1 0,
        (D.layer s).cap.getD 2 0, (D.layer s).cap.getD 3 0, (D.layer s).cap.getD 4 0] D.committed)
        (D.T s).1 (D.T s).2.1 (D.T s).2.2.1 (D.T s).2.2.2.1 (D.T s).2.2.2.2).2.cap ++
      [VsC.ptrAtV (curE + D.lcur s) *
        gen ^ (VsC.klXs (D.T s).1 (D.T s).2.1 (D.T s).2.2.1 (D.T s).2.2.2.1 (D.T s).2.2.2.2).length])
    (D.lR c curE tbE s cbp) (VsC.klOwn (fp + fs (lname s)) (D.τ - 3))
    (fun rd => ReadsAt rd (VsC.ptrAtV (c + D.o201 + 22 * (s + 1)))
        (VsC.klOutW ((D.layer s).next (firstOf s)) (fp + fs (lname s)) (D.τ - 3)) →
      ClaimRec rd false (VsC.ptrAtV (c + D.o201 + 22 * (s + 1))) ((D.layer s).next (firstOf s)) (D.τ - 3))
    (fun rd => WinTabs rd (VsC.ptrAtV tbE) ∧
      VsC.ClaimRecAt rd (firstOf s = 1) (VsC.ptrAtV (c + D.o201 + 22 * s)) (D.recPtrs c s cbp).1
        (D.recPtrs c s cbp).2.1 (D.recPtrs c s cbp).2.2.1 (D.recPtrs c s cbp).2.2.2 (D.layer s).c (D.τ - 3) ∧
      ReadsAt rd (VsC.ptrAtV (curE + D.lcur s))
        (VsC.klXs (D.T s).1 (D.T s).2.1 (D.T s).2.2.1 (D.T s).2.2.2.1 (D.T s).2.2.2.2) ∧
      ReadsAt rd (VsC.ptrAtV (c + D.o201 + 22 * (s + 1)))
        (VsC.klOutW ((D.layer s).next (firstOf s)) (fp + fs (lname s)) (D.τ - 3)))
    PostQuiet (fs (lname s)) fp (fp + fs (lname s)) e

/-- The first copy loop's frame and end. -/
def l0fp : ℕ := allocBase (al name% «verify_keccak_loop0») (c + D.τ + 412)
def l0end : ℕ := D.l0fp al c + lpB fs name% «verify_keccak_loop0» (D.τ - 4) 0

/-- **The layers' positions**: before layer `s`, its cursor and the previous layer's buffers;
each layer's end chosen among those it completes at. -/
noncomputable def posP : ℕ → ℕ × ℕ
  | 0 => (D.l0end fs al c, 0)
  | s + 1 =>
    let fp := allocBase (al (lname s)) (posP s).1
    (Classical.epsilon (D.LP fs al cert k c curE tbE s (posP s).2 fp), fp + fs (lname s))

/-- Layer `s`'s frame. -/
noncomputable def lfp (s : ℕ) : ℕ := allocBase (al (lname s)) (D.posP fs al cert k c curE tbE s).1

/-- Layer `s`'s buffers. -/
noncomputable def lsP (s : ℕ) : ℕ := D.lfp fs al cert k c curE tbE s + fs (lname s)

end VkData

end
end LeanVM.Guest.B1.VerifySub
