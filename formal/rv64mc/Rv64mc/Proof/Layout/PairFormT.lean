/-
  Rv64mc.Proof.Layout.PairFormT

  A `Flushes` of `Form`s (`FlushesFormT`): its `push` and `pull` vectors of 24-byte `Vec<Form>` headers vectors'
  (`VecT`) with their buffers apart (`PairT.BufsApart`), and each element held (`HeldT`): a `Vec<Form>`
  (`FromElemVecFormT.VecFormT`) whose footprint (`ExtendTrustedT.InFoot`: its `Form`s' headers and their terms'
  blocks) avoids both of the `Flushes`' buffers. `PairT.FlushesT` carries the vectors but not their elements, which
  `tables`' and `build_layout`'s later reads and clones need; a footprint apart from both buffers is what lets a
  `Flushes::pair` call keep the elements pushed before it, since `pair` writes only the `Flushes`' header, each
  vector's next slot (`PairT.OutT`) and blocks it allocates.

  `Flushes::pair` keeps it (`SpecT`, from `PairT.SpecT` by `SpecT.of_pairT`): from `PairT.PreT`, the `Flushes`
  `FlushesFormT` and the two pushed `Vec<Form>`s held, it gives `PairT.PostT` and `FlushesFormT` again. The earlier
  elements move with a buffer that grew (`PairT.PushedT`'s `ElemsEq`) and the new ones are `push`'s and `pull`'s
  words (`VecFormT.move'`); their footprints are kept by the frame (`foot_kept`), lie below `NEXT` at entry, and so
  avoid a buffer that is the entry's (by the precondition) or allocated since (`PairT.KeptOrFresh`).

  ## Main definitions

  * `lo`, `hi`, `HeldT`, `ElemsHeldT`, `FlushesFormT`, `PreT`, `PostT`, `SpecT`

  ## Main results

  * `foot_kept`, `HeldT.move`, `keep`, `SpecT.of_pairT`
-/

import Rv64mc.Proof.Layout.PairT
import Rv64mc.Proof.Layout.ExtendTrustedT

namespace Rv64mc.Proof.Layout.PairFormT

open RiscvZkvm.Rv64 Lprog Lprog.RiscV Rv64mc.Spec.Runtime
open Rv64mc.Proof.Runtime.MemsetT (InWin)
open Rv64mc.Proof.Runtime.VecReprT (BufT VecT)
open Rv64mc.Proof.Runtime.GrowOne (rvCapAt_eq rvPtrAt_eq)
open Rv64mc.Proof.Runtime.VecHdrT (vecCap_eq vecPtr_eq vecLen_eq)
open Rv64mc.Proof.Layout.FromElemVecFormT (VecFormT)
open Rv64mc.Proof.Layout.ExtendTrustedT (InFoot FootApart VecFormT.foot_lt VecFormT.move')
open Rv64mc.Proof.Layout.PairT (BufsApart PushedT KeptOrFresh ElemsEq OutT SlotOut PostM)

variable {env : Env}

/-- The start of the buffer of the vector of 24-byte elements at `v`, as a number. -/
def lo (m : MachineState) (v : Word) : Nat := (vecPtr m v).toNat

/-- The end of the buffer of the vector of 24-byte elements at `v`, as a number. -/
def hi (m : MachineState) (v : Word) : Nat := (vecPtr m v).toNat + 24 * (vecCap m v).toNat

/-- **The `Vec<Form>` at `s` held by the `Flushes` at `a`**: a `Vec<Form>` whose footprint avoids both of the
    `Flushes`' buffers. -/
def HeldT (env : Env) (m : MachineState) (a s : Word) : Prop :=
  VecFormT env m s ∧ FootApart m s (lo m a) (hi m a) ∧ FootApart m s (lo m (a + 24#64)) (hi m (a + 24#64))

/-- **The elements of the vector at `v`**, each held by the `Flushes` at `a`. -/
def ElemsHeldT (env : Env) (m : MachineState) (a v : Word) : Prop :=
  ∀ i, i < (vecLen m v).toNat → HeldT env m a (vecPtr m v + BitVec.ofNat 64 (24 * i))

/-- **A `Flushes` of `Form`s at `a`**: its two vectors of 24-byte elements `VecT` with their buffers apart, each
    element held. -/
def FlushesFormT (env : Env) (m : MachineState) (a : Word) : Prop :=
  VecT env m a 24 ∧ VecT env m (a + 24#64) 24 ∧ BufsApart m a ∧ ElemsHeldT env m a a ∧
    ElemsHeldT env m a (a + 24#64)

/-- A vector's whole buffer, capacity and all. -/
theorem vecT_bufCap {m : MachineState} {a : Word} {s : Nat} (h : VecT env m a s) :
    BufT env m (vecCap m a) (vecPtr m a) s := by
  obtain ⟨-, ⟨-, -, h3, -⟩, -⟩ := h
  rwa [rvCapAt_eq, rvPtrAt_eq, ← vecCap_eq, ← vecPtr_eq] at h3

/-- **A held `Vec<Form>`'s footprint is kept by `pair`'s frame**: it lies below `NEXT`, so off the stack, and apart
    from both buffers, so off their next slots. -/
theorem foot_kept {m m' : MachineState} {top : Word} {regs : Reg → Word} {s : Word}
    (hpre : PairT.PreT env regs m) (h2 : regs .x2 = top) (hlim : env.stackLimit.toNat ≤ top.toNat)
    (hnx : (env.next m).toNat ≤ env.heapEnd.toNat) (hfr : env.Frame top (OutT regs m) m m')
    (hs : HeldT env m (regs .x10) s) : ∀ x, InFoot m s x → m'.getMem x = m.getMem x := by
  intro x hx
  have hxn := VecFormT.foot_lt hs.1 hx
  have hlay := env.layout
  have hso := hpre.1.2.2.1
  rw [h2] at hso
  unfold PlacementNextT.StackObj at hso
  refine hfr.2.2 x fun hw => ?_
  rcases hw with hw | hw | hw | hw
  · omega
  · omega
  · rw [hw] at hxn; omega
  · rcases hw with hw | hw | hw
    · unfold InRange at hw; omega
    · have := hs.2.1 x hx
      unfold SlotOut at hw; unfold lo hi at this; rw [vecPtr_eq, vecCap_eq] at this; omega
    · have := hs.2.2 x hx
      unfold SlotOut at hw; unfold lo hi at this; rw [vecPtr_eq, vecCap_eq] at this; omega

/-- **A held `Vec<Form>` whose header's words were copied** from `s` to `d`, its footprint kept: held at `d`, for
    buffers each the entry's or allocated since. -/
theorem HeldT.move {m m' : MachineState} {a s d : Word} (h : HeldT env m a s)
    (hn : (env.next m).toNat ≤ (env.next m').toNat) (hw : InWin env d 24) (hal : d.toNat % 8 = 0)
    (h0 : m'.getMem d = m.getMem s) (h8 : m'.getMem (d + 8#64) = m.getMem (s + 8#64))
    (h16 : m'.getMem (d + 16#64) = m.getMem (s + 16#64))
    (hf : ∀ x : Word, InFoot m s x → m'.getMem x = m.getMem x)
    (hA : KeptOrFresh env m m' a) (hB : KeptOrFresh env m m' (a + 24#64)) : HeldT env m' a d := by
  obtain ⟨hv, hsub⟩ := VecFormT.move' h.1 hn hw hal h0 h8 h16 hf
  have side : ∀ w, KeptOrFresh env m m' w → FootApart m s (lo m w) (hi m w) → FootApart m' d (lo m' w) (hi m' w) :=
    fun w hk ha x hx => by
      have hx' := hsub x hx
      have := VecFormT.foot_lt h.1 hx'
      rcases hk with ⟨hp, hc⟩ | hk
      · unfold lo hi; rw [hp, hc]; exact ha x hx'
      · exact .inl (by unfold lo; omega)
  exact ⟨hv, side a hA h.2.1, side _ hB h.2.2⟩

/-- `q + (k + c)` as two additions. -/
theorem add_split (q : Word) (k c : Nat) :
    q + BitVec.ofNat 64 (k + c) = q + BitVec.ofNat 64 k + BitVec.ofNat 64 c := by
  rw [BitVec.ofNat_add, BitVec.add_assoc]

/-- **One vector of the `Flushes` after `pair`**: its earlier elements moved and the pushed one, all held. -/
theorem elems_keep {m m' : MachineState} {a v src : Word}
    (hV : VecT env m' v 24) (hnx' : (env.next m').toNat ≤ env.heapEnd.toNat)
    (hn : (env.next m).toNat ≤ (env.next m').toNat) (hlen : (vecLen m' v).toNat = (vecLen m v).toNat + 1)
    (hP : PushedT m m' v src) (hold : ElemsHeldT env m a v) (hsrc : HeldT env m a src)
    (hf : ∀ s, HeldT env m a s → ∀ x, InFoot m s x → m'.getMem x = m.getMem x)
    (hA : KeptOrFresh env m m' a) (hB : KeptOrFresh env m m' (a + 24#64)) : ElemsHeldT env m' a v := by
  intro i hi
  rw [hlen] at hi
  have hb := vecT_bufCap hV
  have hlc := (Proof.Layout.FormReprT.vecT_buf hV).2.1
  have hP' : 0x10000000 ≤ (vecPtr m' v).toNat ∧ (vecPtr m' v).toNat + (vecCap m' v).toNat * 24 ≤
      (env.next m').toNat ∧ (vecPtr m' v).toNat % 8 = 0 := by
    rcases hb with h0 | ⟨h1, h2, h3⟩
    · omega
    · exact ⟨h1, h2, h3⟩
  have he : (vecPtr m' v + BitVec.ofNat 64 (24 * i)).toNat = (vecPtr m' v).toNat + 24 * i :=
    toNat_add_ofNat (by have := (env.next m').isLt; omega)
  have hw : InWin env (vecPtr m' v + BitVec.ofNat 64 (24 * i)) 24 := .inl ⟨by omega, by rw [he]; omega⟩
  have hal : (vecPtr m' v + BitVec.ofNat 64 (24 * i)).toNat % 8 = 0 := by rw [he]; omega
  by_cases hil : i < (vecLen m v).toNat
  · have hs := hold i hil
    have hE := hP.1
    have w : ∀ c, c < 3 → m'.getMem (vecPtr m' v + BitVec.ofNat 64 (24 * i) + BitVec.ofNat 64 (8 * c)) =
        m.getMem (vecPtr m v + BitVec.ofNat 64 (24 * i) + BitVec.ofNat 64 (8 * c)) := fun c hc => by
      rw [← add_split, ← add_split, show 24 * i + 8 * c = 8 * (3 * i + c) by omega]
      exact hE _ (by omega)
    refine hs.move hn hw hal ?_ ?_ ?_ (hf _ hs) hA hB
    · simpa using w 0 (by omega)
    · exact w 1 (by omega)
    · exact w 2 (by omega)
  · have hi' : i = (vecLen m v).toNat := by omega
    subst hi'
    have w : ∀ c, c < 3 → m'.getMem (vecPtr m' v + BitVec.ofNat 64 (24 * (vecLen m v).toNat) +
        BitVec.ofNat 64 (8 * c)) = m.getMem (src + BitVec.ofNat 64 (8 * c)) := fun c hc => by
      rw [← add_split]; exact hP.2 c hc
    refine hsrc.move hn hw hal ?_ ?_ ?_ (hf _ hsrc) hA hB
    · simpa using w 0 (by omega)
    · simpa using w 1 (by omega)
    · simpa using w 2 (by omega)

/-- **`pair` keeps a `Flushes` of `Form`s**, its two pushed `Vec<Form>`s held at entry. -/
theorem keep {m m' : MachineState} {top sp : Word} {regs : Reg → Word} (hpre : PairT.PreT env regs m)
    (h2 : regs .x2 = top) (hlim : env.stackLimit.toNat ≤ top.toNat) (hnx : (env.next m).toNat ≤ env.heapEnd.toNat)
    (hfr : env.Frame top (OutT regs m) m m') (hF : FlushesFormT env m (regs .x10))
    (hpush : HeldT env m (regs .x10) (regs .x11)) (hpull : HeldT env m (regs .x10) (regs .x12))
    (hpost : PostM env regs m sp m') : FlushesFormT env m' (regs .x10) := by
  obtain ⟨⟨hV1, hV2, -, hBA⟩, hl1, hl2, hP1, hP2, hK1, hK2⟩ := hpost
  have hf := fun s (hs : HeldT env m (regs .x10) s) => foot_kept hpre h2 hlim hnx hfr hs
  have hn := hfr.1
  have hnx' := hfr.2.1
  exact ⟨hV1, hV2, hBA, elems_keep hV1 hnx' hn hl1 hP1 hF.2.2.2.1 hpush hf hK1 hK2,
    elems_keep hV2 hnx' hn hl2 hP2 hF.2.2.2.2 hpull hf hK1 hK2⟩

/-- The precondition: `PairT.PreT`, `self` a `Flushes` of `Form`s, `push` and `pull` held by it. -/
def PreT (env : Env) (regs : Reg → Word) (m : MachineState) : Prop :=
  PairT.PreT env regs m ∧ FlushesFormT env m (regs .x10) ∧ HeldT env m (regs .x10) (regs .x11) ∧
    HeldT env m (regs .x10) (regs .x12)

/-- The postcondition: `PairT.PostT`, and `self` a `Flushes` of `Form`s again. -/
def PostT (env : Env) (regs : Reg → Word) (m : MachineState) (r' : Reg → Word) (m' : MachineState) : Prop :=
  PairT.PostT env regs m r' m' ∧ FlushesFormT env m' (regs .x10)

/-- **`Flushes::pair` over a `Flushes` of `Form`s**, or the guest's abort. -/
def SpecT (env : Env) (p : Lprog (Op Reg) Reg) (i need : Nat) : Prop :=
  HoldsT env p i need (PreT env) (PostT env) OutT AbortStop

/-- **`pair`'s total contract gives it.** -/
theorem SpecT.of_pairT {p : Lprog (Op Reg) Reg} {i need : Nat} (h : PairT.SpecT env p i need) :
    SpecT env p i need :=
  Isa.TContract.mono h (fun _ _ _ _ ⟨⟨he, hs, hst, hn, hP, hal⟩, hw⟩ => ⟨⟨he, hs, hst, hn, hP.1, hal⟩, hw⟩)
    (fun _ top regs m _ _ ⟨⟨he, hs, _, hn, hP, _⟩, _⟩ ⟨⟨ha, hfr, hst, hpost⟩, hc⟩ =>
      ⟨⟨ha, hfr, hst, hpost, keep hP.1 he.2 (by omega) hn hfr hP.2.1 hP.2.2.1 hP.2.2.2 hpost⟩, hc⟩)
    fun _ _ _ _ _ _ _ h => h

end Rv64mc.Proof.Layout.PairFormT

/-- info: 'Rv64mc.Proof.Layout.PairFormT.SpecT.of_pairT' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Rv64mc.Proof.Layout.PairFormT.SpecT.of_pairT
