/-
  LeanVM.Guest.B1.VsC.VsOrcPhD

  The closed forms `Ph7` to `Ph11` name, before the context so its conditions can state them.
-/

module

public import LeanVM.Guest.B1.VsC.VsOrcTail
public import LeanVM.Guest.B1.VsC.VsOrcHonest
public import LeanVM.Guest.B1.VsC.RowSideA
public import LeanVM.Guest.B1.VsC.Vsc8CalleesA

/-!
# The closed forms of `Ph7` to `Ph11`

`eqLevels` (an `eqtree`'s buffer), `ph7Rs` (the packed point), `ph7St0` (the index side's start), `ph9St0`
(the row side's start), `pmRets` (`packed_message`'s returns); then `Ph12` to the end's: `tpD`, `ltIdx`, `LtIdentity`, `vkIdx`, `vkRets`,
`osRets`.
-/

namespace LeanVM.Guest.B1.VsC

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Memory LeanVM.Guest.B1
open LeanVM.Guest.Complete LeanVM.Guest.B1.Fwd LeanVM.Guest.B1.Link LeanVM.Protocol.Verifier
open LeanVM.Guest.B1.Whir LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile
open LeanVM.Guest.B1.Stack LeanVM.Guest.B1.VerifySub

@[expose] public section

/-- An `eqtree`'s buffer: the levels `eqKernel (rs.take t)`, `t = 1 ..= n`, one after the other. -/
def eqLevels (rs : List E) (n : ℕ) : List E := (List.range n).flatMap fun t => eqKernel (rs.take (t + 1))

/-- The packed point: the opening's words `50 ..< 54`. -/
def ph7Rs (xs10 : List E) : List E := (xs10.drop 50).take 4

/-- The index side's rounds' start: `squeeze_packed`'s capacity, the cursor `w 580`, the rounds' claim. -/
def ph7St0 (w : ℕ → E) (xs10 : List E) : RSt :=
  ⟨[w 680, w 681, w 682, w 683, w 684], w 580, lrClaim (w 752) (w 753) (xs10.getD 6 0) (xs10.getD 7 0)⟩

/-- The row side's start: the permutation's outputs, the cursor past the index side's word, the claim. -/
def ph9St0 (σ : Val) (w : ℕ → E) (b772 : ℕ) : RSt :=
  ⟨[σ (.n 790), σ (.n 791), σ (.n 792), σ (.n 793), σ (.n 794)], ptrAt (b772 + 1), w 773⟩

/-- `packed_message`'s returns: the squeeze after absorbing the message's packed words into the row side's
capacity. -/
noncomputable def pmRets (xm : List E) (f : List E) : List E :=
  (Fs.squeeze ⟨pkAbsorb 18 xm f, []⟩).1 :: (Fs.squeeze ⟨pkAbsorb 18 xm f, []⟩).2.cap

/-! ## The closed forms `Ph12` to the end name -/

/-- The table points' first return indices, `t = 1 … 5`. -/
def tpD (t : ℕ) : ℕ := [1403, 1524, 1607, 1734, 1880].getD (t - 1) 0

/-- The index arrays `link_terminal` reads: the point, the slices, the shifts, the chunks' `ν`. -/
def ltIdx (b12 b1076 b19 bnu nr nnu : ℕ) : List (ℕ × ℕ) :=
  [(b12, nr), (b1076 + 80, 64), (b19, 12), (bnu, nnu)]

/-- The link's terminal identity at `w32`'s values: the claim is the summand at the end point plus `rest`. -/
def LtIdentity (ch : Chunks) (σ : Val) (claim : E) (rs sl shs nus : List E) : Prop :=
  claim = (Functionals.new ch rs 12).summand (σ (.n 2846)) shs ((Functionals.new ch rs 12).values ch sl)
    (nus.map (σ (.n 2891) * ·)) + σ (.n 2890)

/-- The index arrays `verify_keccak` reads: the stream words past the packed message, the table point, the
outputs (the packed message's words `55 …`), the opening and the point at `.n 20`, the slices, the window tables. -/
def vkIdx (bm b15 b20 b21 qt nx nchi nop npt : ℕ) : List (ℕ × ℕ) :=
  [(bm + 144, nx), (b15, nchi), (bm + 55, 25), (b20, nop), (b20 + qkeccakVarsCap, npt), (b21, 64),
    (qt + 178, 2 ^ winTabBits)]

/-- `verify_keccak`'s returns: the capacity after the reduction, the cursor past its words, the claim's word. -/
def vkRets (s' : Fs) (cur : E) (n : ℕ) (kw : E) : List E := capOf s'.perm ++ [cur * gen ^ n, kw]

/-- `open_stacked`'s returns: the WHIR end's target, the point buffers, the inner and residual values, the
cursor past its words. -/
def osRets (wE : WhirEnd) (bp bp1 ie : ℕ) : List E :=
  [wE.target, ptrAt bp, ptrAt bp1, wE.inner, wE.residual, ptrAt ie]

/-! ## The callees' calls `Ph12` to the end pins -/

/-- `link_terminal__L{wd}`'s call as its completeness statement gives it, at the frame `fp` and the end `ec`. -/
def LtCall (fs : String → ℕ) (al : String → Bool) (cert : String → V → ℕ) (k wd : ℕ) (σ : Val) (claim : E)
    (b12 b1076 b19 bnu : ℕ) (rs sl shs nus : List E) (fp ec : ℕ) : Prop :=
  CallAtA fs al cert k (ltNames.getD (wd - 19) "")
    [ptrAt b12, ptrAt b1076, σ (.n 2846), ptrAt b19, σ (.n 2891), ptrAt bnu, σ (.n 2890), claim] [0]
    (ptrRegion (ltArrays (ptrAt b12) (ptrAt b1076) (ptrAt b19) (ptrAt bnu) rs.length nus.length)) (fun _ => False)
    (fun _ => True)
    (fun rd ↦ ReadsAt rd (ptrAt b12) rs ∧ (∀ k < 64, LoadHolds rd (ptrAt b1076) (80 + k) (sl.getD k 0)) ∧
      ReadsAt rd (ptrAt b19) shs ∧ ReadsAt rd (ptrAt bnu) nus)
    PostQuiet (fs (ltNames.getD (wd - 19) "")) fp (fp + fs (ltNames.getD (wd - 19) "")) ec

/-- `verify_keccak`'s call as its completeness statement gives it, at the frame `fp` and the end `ev`. -/
def VkCall (fs : String → ℕ) (al : String → Bool) (cert : String → V → ℕ) (k : ℕ) (w : ℕ → E)
    (b15 b20 b21 qt τ : ℕ) (chis outs xs op point slices : List E) (kw : E) (s' : Fs) (fp ev : ℕ) : Prop :=
  CallAtA fs al cert k "verify_keccak" [w 1288, w 1289, w 1290, w 1291, w 1292, w 1076 * word 21299200 0, gen ^ τ,
      ptrAt b15, w 1076 * word 36028797018963968 0, ptrAt b20, ptrAt b21, ptrAt qt * word 365917469723852800 0]
    (capOf s'.perm ++ [w 1076 * word 21299200 0 * gen ^ xs.length, kw])
    (ptrRegion (vkArrays (w 1076 * word 21299200 0) (ptrAt b15) (w 1076 * word 36028797018963968 0) (ptrAt b20)
      (ptrAt b21) (ptrAt qt * word 365917469723852800 0) xs chis op point)) (fun _ => False) (fun _ => True)
    (fun rd => WinTabs rd (ptrAt qt * word 365917469723852800 0) ∧ ReadsAt rd (ptrAt b15) chis ∧
      ReadsAt rd (w 1076 * word 36028797018963968 0) outs ∧ ReadsAt rd (w 1076 * word 21299200 0) xs ∧
      ReadsAt rd (ptrAt b20) op ∧ ReadsAt rd (ptrAt b20 * gen ^ qkeccakVarsCap) point ∧ ReadsAt rd (ptrAt b21) slices)
    PostQuiet (fs "verify_keccak") fp (fp + fs "verify_keccak") ev

/-- `ring_switch_target`'s call as its completeness statement gives it, on the ring buffers at `a`. -/
def RtCall (fs : String → ℕ) (al : String → Bool) (cert : String → V → ℕ) (k : ℕ) (a : ℕ) (s ch : List E)
    (fp er : ℕ) : Prop :=
  CallAtA fs al cert k "ring_switch_target" [ptrAt (a + 80), ptrAt a]
    [ringTarget s (ch.take ringMapWidth) (ch.drop ringMapWidth)]
    (ptrRegion [(ptrAt (a + 80), kBits), (ptrAt a, 2 * ringMapWidth)]) (fun _ => False) (fun _ => True)
    (fun rd => ReadsAt rd (ptrAt (a + 80)) s ∧ ReadsAt rd (ptrAt a) ch)
    PostQuiet (fs "ring_switch_target") fp (fp + fs "ring_switch_target") er

end
end LeanVM.Guest.B1.VsC
