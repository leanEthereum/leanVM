/-
  Rv64mc.Proof.Layout.StateDerivedT

  `Flushes::state_derived(&mut self, pc, fp, npc, nfp)` is total over a `Flushes` of `Form`s
  (`PairFormT.FlushesFormT`): it allocates two blocks of three `Form` headers (`alloc`, the abort where it fails),
  fills the first with `constant(SEP_STATE)` and the words of `npc` (`a1`) and `nfp` (`a2`), the second with
  `constant(SEP_STATE)`, `col(pc, 0)` and `col(fp, 0)` (the image passes `pc = 0`, `fp = 1`), and pushes the two
  `Vec<Form>`s with `Flushes::pair` (`PairFormT`). The `Flushes` stays a `Flushes` of `Form`s, each vector one
  longer, each buffer the entry's or allocated since (`PostT`); it writes what `pair` writes (`PairT.OutT`) besides
  its stack and fresh blocks.

  The precondition: `self` `PairT.FlushesT` and a `Flushes` of `Form`s; `npc` and `nfp` `Form`s (`FormReprT.FormT`)
  whose headers are caller's frame objects and whose terms' blocks avoid both of `self`'s buffers (`TermsApart`), so
  that the pushed `Vec<Form>`s are held (`PairFormT.HeldT`). The new `Form`s' blocks and the two blocks are allocated
  after the entry, above both buffers (`off_of_ge`).

  ## Main definitions

  * `Off`, `TermsApart`, `PreT`, `PostT`, `SpecT`

  ## Main results

  * `FormIn.terms`, `FormT.move`, `off_of_ge`, `held3`, `FlushesFormT.keep`, `self_kept`, `total`
-/

import Rv64mc.Proof.Layout.PairFormT
import Rv64mc.Proof.Layout.ConstantAlT
import Rv64mc.Proof.Layout.ColAlT
import Rv64mc.Gen.Tmpl.Verifier.Layout.Flushes.StateDerived

namespace Rv64mc.Proof.Layout.StateDerivedT

open RiscvZkvm.Rv64 Lprog Lprog.RiscV LeanVM.Parameters Rv64mc.Spec.Runtime Rv64mc.Spec.Layout
open Rv64mc.Proof.Runtime (Aborts)
open Rv64mc.Proof.Runtime.AllocT (AllocSpecT)
open Rv64mc.Proof.Runtime.MemsetT (InWin)
open Rv64mc.Proof.Runtime.VecReprT (BufT VecT)
open Rv64mc.Proof.Runtime.GrowOne (rvCapAt_eq rvPtrAt_eq)
open Rv64mc.Proof.Runtime.VecHdrT (vecCap_eq vecPtr_eq vecLen_eq)
open Rv64mc.Proof.Layout.FormReprT (FormT TermsT vecT_keep vecT_lt vecT_buf)
open Rv64mc.Proof.Layout.FromElemVecFormT (VecFormT)
open Rv64mc.Proof.Layout.ExtendTrustedT (InFoot FootApart VecFormT.foot_lt VecFormT.keep')
open Rv64mc.Proof.Layout.PairT (BufsApart KeptOrFresh FlushesT OutT Slots)
open Rv64mc.Proof.Layout.PairFormT (lo hi HeldT ElemsHeldT FlushesFormT vecT_bufCap)
open Rv64mc.Proof.Layout.PlacementNextT (StackObj)
open Rv64mc.Gen.Verifier.Layout.Flushes.StateDerived (Link tmpl)

variable {env : Env}

/-- **`x` avoids both buffers of the `Flushes` at `a`**. -/
def Off (m : MachineState) (a : Word) (x : Nat) : Prop :=
  (x < lo m a ∨ hi m a ≤ x) ∧ (x < lo m (a + 24#64) ∨ hi m (a + 24#64) ≤ x)

/-- **The terms' block of the `Form` at `f` avoids both buffers of the `Flushes` at `a`**. -/
def TermsApart (m : MachineState) (a f : Word) : Prop :=
  ∀ x : Word, (vecPtr m f).toNat ≤ x.toNat → x.toNat < (vecPtr m f).toNat + 40 * (vecLen m f).toNat →
    Off m a x.toNat

/-- The total precondition: `self` (`a0`) `PairT.FlushesT`, aligned, a `Flushes` of `Form`s; `npc` (`a1`) and `nfp`
    (`a2`) `Form`s, their headers caller's frame objects, their terms' blocks apart from `self`'s buffers. -/
def PreT (env : Env) (regs : Reg → Word) (m : MachineState) : Prop :=
  FlushesT env m (regs .x2) (regs .x10) ∧ (regs .x10).toNat % 8 = 0 ∧ FlushesFormT env m (regs .x10) ∧
    StackObj (regs .x2) (regs .x11) 24 ∧ StackObj (regs .x2) (regs .x12) 24 ∧ FormT env m (regs .x11) ∧
    FormT env m (regs .x12) ∧ TermsApart m (regs .x10) (regs .x11) ∧ TermsApart m (regs .x10) (regs .x12)

/-- The total postcondition: `self` a `Flushes` of `Form`s, each vector one longer, each buffer the entry's or
    allocated since. -/
def PostT (env : Env) (regs : Reg → Word) (m : MachineState) (_r' : Reg → Word) (m' : MachineState) : Prop :=
  FlushesFormT env m' (regs .x10) ∧
    (vecLen m' (regs .x10)).toNat = (vecLen m (regs .x10)).toNat + 1 ∧
    (vecLen m' (regs .x10 + 24#64)).toNat = (vecLen m (regs .x10 + 24#64)).toNat + 1 ∧
    KeptOrFresh env m m' (regs .x10) ∧ KeptOrFresh env m m' (regs .x10 + 24#64)

/-- **The total contract of `Flushes::state_derived`**, or the guest's abort. -/
def SpecT (env : Env) (p : Lprog (Op Reg) Reg) (i need : Nat) : Prop :=
  HoldsT env p i need (PreT env) (PostT env) OutT AbortStop

/-! ## The `Form`s and the `Flushes` across the body -/

/-- **A `Form` written by a call** between `lo` and `hi`: its terms' block, unless empty, in `[lo, hi)`. -/
theorem FormIn.terms {lo hi : Word} {m : MachineState} {a : Word} {f : LeanVM.Protocol.Verifier.Form}
    (h : FormIn lo hi m a f) : (vecLen m a).toNat = 0 ∨
      (lo.toNat ≤ (vecPtr m a).toNat ∧ (vecPtr m a).toNat + 40 * (vecLen m a).toNat ≤ hi.toNat) := by
  obtain ⟨q, cap, hv, hb⟩ := h
  have hp : vecPtr m a = q := hv.ptr_eq
  have hll : (vecLen m a).toNat = f.terms.length := by
    rw [hv.len_eq]; simp; have := hv.len_le; have := hv.cap_lt; omega
  have hreg : cap = 0 ∨ (lo.toNat ≤ q.toNat ∧ q.toNat + 40 * cap ≤ hi.toNat) := by
    simpa [BufIn, Region, Layouts.VecUsizeE.byteSize] using hb
  have := hv.len_le
  rw [hll, hp]
  rcases hreg with h0 | ⟨h1, h2⟩
  · exact .inl (by omega)
  · exact .inr ⟨h1, by
      have : 40 * f.terms.length ≤ 40 * cap := Nat.mul_le_mul_left _ this
      omega⟩

/-- **A `Form`'s header copied** from `s` to `d`, its terms' block kept: a `Form` at `d` with the same block. -/
theorem FormT.move {m M : MachineState} {s d : Word} (h : FormT env m s)
    (hn : (env.next m).toNat ≤ (env.next M).toNat) (hw : InWin env d 24) (hal : d.toNat % 8 = 0)
    (h0 : M.getMem d = m.getMem s) (h8 : M.getMem (d + 8#64) = m.getMem (s + 8#64))
    (h16 : M.getMem (d + 16#64) = m.getMem (s + 16#64))
    (hb : ∀ x : Word, (vecPtr m s).toNat ≤ x.toNat → x.toNat < (vecPtr m s).toNat + 40 * (vecLen m s).toNat →
      M.getMem x = m.getMem x) :
    FormT env M d ∧ vecPtr M d = vecPtr m s ∧ vecLen M d = vecLen m s := by
  have ep : vecPtr M d = vecPtr m s := by rw [vecPtr_eq, vecPtr_eq, h8]
  have el : vecLen M d = vecLen m s := by rw [vecLen_eq, vecLen_eq, h16]
  refine ⟨⟨CloneFormsT.vecT_copy h.1 hw hal hn h0 h8 h16, ?_⟩, ep, el⟩
  rw [ep, el]
  intro t ht
  have hT := h.2 t ht
  have hf := h.foot
  have := env.heapEnd.isLt
  have := env.layout
  rcases hf with h0 | ⟨-, h2, -⟩
  · omega
  have et : (vecPtr m s + BitVec.ofNat 64 (40 * t)).toNat = (vecPtr m s).toNat + 40 * t :=
    toNat_add_ofNat (by have := (env.next m).isLt; omega)
  refine vecT_keep hT hn fun b h1 h2 => hb b (by omega) ?_
  rw [et] at h2
  have : 40 * t + 40 ≤ 40 * (vecLen m s).toNat := by omega
  omega

/-- **What lies at or above `NEXT` avoids both buffers**, each a buffer of the entry's. -/
theorem off_of_ge {m : MachineState} {a : Word} {x : Nat} (h1 : VecT env m a 24) (h2 : VecT env m (a + 24#64) 24)
    (hx : (env.next m).toNat ≤ x) : Off m a x := by
  have b1 := vecT_bufCap h1
  have b2 := vecT_bufCap h2
  unfold Off lo hi
  constructor
  · rcases b1 with h | ⟨-, h, -⟩
    · rw [h]; omega
    · unfold Env.Live at h; omega
  · rcases b2 with h | ⟨-, h, -⟩
    · rw [h]; omega
    · unfold Env.Live at h; omega

/-- **A vector of three `Form`s held by a `Flushes`**: its header at `h` names three `Form`s in a block `B` below
    `NEXT`; the block and each `Form`'s terms avoid both buffers (as they were in `m`, whose header words `M` keeps). -/
theorem held3 {m M : MachineState} {a h B : Word} (hw : InWin env h 24) (hal : h.toNat % 8 = 0)
    (h0 : M.getMem h = 3#64) (h8 : M.getMem (h + 8#64) = B) (h16 : M.getMem (h + 16#64) = 3#64)
    (hB : 0x10000000 ≤ B.toNat) (hBal : B.toNat % 8 = 0) (hBn : B.toNat + 72 ≤ (env.next M).toNat)
    (hF : ∀ i, i < 3 → FormT env M (B + BitVec.ofNat 64 (24 * i)))
    (hblk : ∀ x : Word, B.toNat ≤ x.toNat → x.toNat < B.toNat + 72 → Off m a x.toNat)
    (hterm : ∀ i, i < 3 → TermsApart M a (B + BitVec.ofNat 64 (24 * i)))
    (hlo : Off M a = Off m a) : HeldT env M a h := by
  have ec : vecCap M h = 3#64 := by rw [vecCap_eq, h0]
  have ep : vecPtr M h = B := by rw [vecPtr_eq, h8]
  have el : vecLen M h = 3#64 := by rw [vecLen_eq, h16]
  have hV : VecFormT env M h := by
    refine ⟨⟨hw, ⟨InWin.sub hw (Nat.le_refl _) (by simp only [Layouts.RawVecInner.byteSize]; omega), hal, ?_, ?_⟩,
      ?_⟩, ?_⟩
    · rw [rvCapAt_eq, rvPtrAt_eq, h0, h8]
      exact .inr ⟨hB, by unfold Env.Live; simp; omega, hBal⟩
    · rw [rvCapAt_eq, h0]; simp
    · rw [el, ec]
    · rw [ep, el]; exact fun i hi => hF i (by simpa using hi)
  have side : ∀ x : Word, InFoot M h x → Off M a x.toNat := by
    intro x hx
    rw [hlo]
    rcases hx with ⟨h1, h2⟩ | ⟨i, hi, h1, h2⟩
    · rw [ep, el] at *; exact hblk x h1 (by simpa using h2)
    · rw [ep, el] at *
      have := hterm i (by simpa using hi) x h1 h2
      rwa [hlo] at this
  refine ⟨hV, fun x hx => (side x hx).1, fun x hx => (side x hx).2⟩

/-- **The elements of a `Flushes`' vector are kept** by a memory agreeing below `NEXT`, with the buffers' words
    and the vector's header kept. -/
theorem elemsHeld_keep {m M : MachineState} {a v : Word} (hV : VecT env m v 24) (h : ElemsHeldT env m a v)
    (hn : (env.next m).toNat ≤ (env.next M).toNat)
    (hk : ∀ b : Word, b.toNat < (env.next m).toNat → M.getMem b = m.getMem b)
    (ep : vecPtr M v = vecPtr m v) (el : vecLen M v = vecLen m v)
    (hlo : lo M a = lo m a ∧ hi M a = hi m a ∧ lo M (a + 24#64) = lo m (a + 24#64) ∧
      hi M (a + 24#64) = hi m (a + 24#64)) : ElemsHeldT env M a v := by
  intro i hi'
  rw [el] at hi'
  rw [ep]
  have hs := h i hi'
  have hbw := FromElemVecFormT.buf_word hV hi'
  have hkf := fun x hx => hk x (VecFormT.foot_lt hs.1 hx)
  obtain ⟨hv, hsub⟩ := VecFormT.keep' hs.1 hn (fun b h1 h2 => hk b (by omega)) hkf
  obtain ⟨l1, h1, l2, h2⟩ := hlo
  refine ⟨hv, fun x hx => ?_, fun x hx => ?_⟩
  · rw [l1, h1]; exact hs.2.1 x (hsub x hx)
  · rw [l2, h2]; exact hs.2.2 x (hsub x hx)

/-- `self`'s six words in a memory keeping its 48 bytes. -/
theorem kept48 {m M : MachineState} {a : Word} (hlt : a.toNat + 48 < 2 ^ 64)
    (hs : ∀ b : Word, a.toNat ≤ b.toNat → b.toNat < a.toNat + 48 → M.getMem b = m.getMem b) :
    M.getMem a = m.getMem a ∧ M.getMem (a + 8#64) = m.getMem (a + 8#64) ∧
      M.getMem (a + 16#64) = m.getMem (a + 16#64) ∧ M.getMem (a + 24#64) = m.getMem (a + 24#64) ∧
      M.getMem (a + 32#64) = m.getMem (a + 32#64) ∧ M.getMem (a + 40#64) = m.getMem (a + 40#64) := by
  have w : ∀ k, k ≤ 40 → M.getMem (a + BitVec.ofNat 64 k) = m.getMem (a + BitVec.ofNat 64 k) := fun k hk' => by
    have ek : (a + BitVec.ofNat 64 k).toNat = a.toNat + k := toNat_add_ofNat (by omega)
    exact hs _ (by omega) (by omega)
  exact ⟨by simpa using w 0 (by omega), w 8 (by omega), w 16 (by omega), w 24 (by omega), w 32 (by omega),
    w 40 (by omega)⟩

/-- `self`'s buffers in a memory keeping its 48 bytes. -/
theorem lohi_eq {m M : MachineState} {a : Word} (hlt : a.toNat + 48 < 2 ^ 64)
    (hs : ∀ b : Word, a.toNat ≤ b.toNat → b.toNat < a.toNat + 48 → M.getMem b = m.getMem b) :
    lo M a = lo m a ∧ hi M a = hi m a ∧ lo M (a + 24#64) = lo m (a + 24#64) ∧
      hi M (a + 24#64) = hi m (a + 24#64) := by
  obtain ⟨w0, w8, -, w24, w32, -⟩ := kept48 hlt hs
  have a8 : a + 24#64 + 8#64 = a + 32#64 := by rw [BitVec.add_assoc]; rfl
  unfold lo hi
  simp only [vecPtr_eq, vecCap_eq, a8, w0, w8, w24, w32]
  exact ⟨trivial, trivial, trivial, trivial⟩

/-- `self`'s buffers in a memory keeping its 48 bytes. -/
theorem off_eq {m M : MachineState} {a : Word} (hlt : a.toNat + 48 < 2 ^ 64)
    (hs : ∀ b : Word, a.toNat ≤ b.toNat → b.toNat < a.toNat + 48 → M.getMem b = m.getMem b) : Off M a = Off m a := by
  obtain ⟨l1, h1, l2, h2⟩ := lohi_eq hlt hs
  funext x
  unfold Off
  rw [l1, h1, l2, h2]

/-- **A `Flushes` of `Form`s is kept** by a memory agreeing below `NEXT` and on its 48 bytes. -/
theorem FlushesFormT.keep {m M : MachineState} {a : Word} (h : FlushesFormT env m a)
    (hn : (env.next m).toNat ≤ (env.next M).toNat)
    (hk : ∀ b : Word, b.toNat < (env.next m).toNat → M.getMem b = m.getMem b)
    (hs : ∀ b : Word, a.toNat ≤ b.toNat → b.toNat < a.toNat + 48 → M.getMem b = m.getMem b) :
    FlushesFormT env M a ∧ Off M a = Off m a := by
  obtain ⟨hV1, hV2, hBA, hE1, hE2⟩ := h
  have hlt := vecT_lt hV1
  have hlt2 := vecT_lt hV2
  have e24 : (a + 24#64).toNat = a.toNat + 24 := toNat_add_ofNat (by omega)
  obtain ⟨w0, w8, w16, w24, w32, w40⟩ := kept48 (by omega) hs
  have a8 : a + 24#64 + 8#64 = a + 32#64 := by rw [BitVec.add_assoc]; rfl
  have a16 : a + 24#64 + 16#64 = a + 40#64 := by rw [BitVec.add_assoc]; rfl
  have hlo := lohi_eq (by omega) hs
  refine ⟨⟨vecT_keep hV1 hn fun b h1 h2 => hs b h1 (by omega),
    vecT_keep hV2 hn fun b h1 h2 => hs b (by omega) (by omega), ?_,
    elemsHeld_keep hV1 hE1 hn hk (by rw [vecPtr_eq, vecPtr_eq, w8]) (by rw [vecLen_eq, vecLen_eq, w16]) hlo,
    elemsHeld_keep hV2 hE2 hn hk (by rw [vecPtr_eq, vecPtr_eq, a8, w32])
      (by rw [vecLen_eq, vecLen_eq, a16, w40]) hlo⟩, off_eq (by omega) hs⟩
  unfold BufsApart
  rw [w0, w8, w24, w32]
  exact hBA

/-! ## The body, cut after the first block's stores (instruction 34) and after the two `col`s (53) -/

/-- `pair`'s precondition, sealed so that the executor leaves it as one goal. -/
@[irreducible] def PPre (env : Env) (regs : Reg → Word) (m : MachineState) : Prop := PairFormT.PreT env regs m

/-- The registers past the first block: the stack pointer, `self` in `s0`, `3` in `s2`, the other saved ones the
    entry's. -/
def Regs (top : Word) (regs R : Reg → Word) : Prop :=
  R .x2 = top + 18446744073709551504#64 ∧ R .x8 = regs .x10 ∧ R .x18 = 3#64 ∧ R .x20 = regs .x20 ∧
    R .x21 = regs .x21 ∧ R .x22 = regs .x22 ∧ R .x23 = regs .x23 ∧ R .x24 = regs .x24 ∧ R .x25 = regs .x25 ∧
    R .x26 = regs .x26 ∧ R .x27 = regs .x27

/-- The `Form` at `f` has no terms, or its terms' block from `x` on. -/
def From (M : MachineState) (f : Word) (x : Nat) : Prop := (vecLen M f).toNat = 0 ∨ x ≤ (vecPtr M f).toNat

/-- The second block `b` at instruction 53, for the stack top `top`: allocated since the entry, its first `Form`
    written, the two `col`s' `Form`s in the frame at `top - 88` and `top - 64`, every terms' block after the block;
    the first vector's (at `top - 112`) footprint below the block. -/
def Blk2 (env : Env) (m M : MachineState) (b top : Word) : Prop :=
  (env.next m).toNat ≤ b.toNat ∧ b.toNat % 8 = 0 ∧ b.toNat + 72 ≤ (env.next M).toNat ∧ FormT env M b ∧
    FormT env M (top + 18446744073709551528#64) ∧ FormT env M (top + 18446744073709551552#64) ∧
    From M b (b.toNat + 72) ∧ From M (top + 18446744073709551528#64) (b.toNat + 72) ∧
    From M (top + 18446744073709551552#64) (b.toNat + 72) ∧
    ∀ x, InFoot M (top + 18446744073709551504#64) x → x.toNat < b.toNat

/-- A store elsewhere, by the addresses' numbers. -/
theorem get_ne {s : MachineState} {a b v : Word} (h : b.toNat ≠ a.toNat) : (s.setMem a v).getMem b = s.getMem b :=
  MachineState.getMem_setMem_ne fun e => h (by rw [e])

/-- `top - k` as a number. -/
theorem top_sub {top c : Word} {k : Nat} (hc : c.toNat + k = 2 ^ 64) (hk : k ≤ top.toNat) :
    (top + c).toNat = top.toNat - k :=
  Runtime.CloneT.toNat_add_neg hc hk

/-- The stores of instructions 59 to 67: the two `col`s' `Form`s at `top - 88` and `top - 64` copied to `B + 24` and
    `B + 48`, then the header `(3, B, 3)` at `top - 64`. -/
def chain2 (M : MachineState) (B top : Word) : MachineState :=
  ((((((((M.setMem (B + 24#64) (M.getMem (top + 18446744073709551528#64))).setMem (B + 32#64)
    (M.getMem (top + 18446744073709551536#64))).setMem (B + 40#64) (M.getMem (top + 18446744073709551544#64))).setMem
    (B + 48#64) (M.getMem (top + 18446744073709551552#64))).setMem (B + 56#64)
    (M.getMem (top + 18446744073709551560#64))).setMem (B + 64#64)
    (M.getMem (top + 18446744073709551568#64))).setMem (top + 18446744073709551552#64) 3#64).setMem
    (top + 18446744073709551560#64) B).setMem (top + 18446744073709551568#64) 3#64

/-- What `chain2` leaves and writes. -/
theorem chain2_get {M : MachineState} {B top : Word} (h112 : 112 ≤ top.toNat)
    (hB : B.toNat + 72 ≤ top.toNat - 112) :
    (∀ x : Word, (x.toNat < B.toNat + 24 ∨ B.toNat + 72 ≤ x.toNat) →
      (x.toNat < top.toNat - 64 ∨ top.toNat - 40 ≤ x.toNat) → (chain2 M B top).getMem x = M.getMem x) ∧
    (chain2 M B top).getMem (B + 24#64) = M.getMem (top + 18446744073709551528#64) ∧
    (chain2 M B top).getMem (B + 32#64) = M.getMem (top + 18446744073709551536#64) ∧
    (chain2 M B top).getMem (B + 40#64) = M.getMem (top + 18446744073709551544#64) ∧
    (chain2 M B top).getMem (B + 48#64) = M.getMem (top + 18446744073709551552#64) ∧
    (chain2 M B top).getMem (B + 56#64) = M.getMem (top + 18446744073709551560#64) ∧
    (chain2 M B top).getMem (B + 64#64) = M.getMem (top + 18446744073709551568#64) ∧
    (chain2 M B top).getMem (top + 18446744073709551552#64) = 3#64 ∧
    (chain2 M B top).getMem (top + 18446744073709551560#64) = B ∧
    (chain2 M B top).getMem (top + 18446744073709551568#64) = 3#64 := by
  have eB : ∀ k, k ≤ 64 → (B + BitVec.ofNat 64 k).toNat = B.toNat + k := fun k hk => toNat_add_ofNat (by omega)
  have b24 := eB 24 (by omega)
  have b32 := eB 32 (by omega)
  have b40 := eB 40 (by omega)
  have b48 := eB 48 (by omega)
  have b56 := eB 56 (by omega)
  have b64 := eB 64 (by omega)
  have t64 := top_sub (top := top) (c := 18446744073709551552#64) (k := 64) rfl (by omega)
  have t56 := top_sub (top := top) (c := 18446744073709551560#64) (k := 56) rfl (by omega)
  have t48 := top_sub (top := top) (c := 18446744073709551568#64) (k := 48) rfl (by omega)
  simp only [chain2]
  refine ⟨fun x h1 h2 => ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals
    repeat (first | rw [MachineState.getMem_setMem_eq] | rw [get_ne (by omega)])

/-- **A held `Vec<Form>` is kept** by a memory agreeing on its header and footprint, `self`'s buffers the same. -/
theorem HeldT.keep {M M' : MachineState} {a s : Word} (h : HeldT env M a s)
    (hn : (env.next M).toNat ≤ (env.next M').toNat)
    (hh : ∀ b : Word, s.toNat ≤ b.toNat → b.toNat < s.toNat + 24 → M'.getMem b = M.getMem b)
    (hf : ∀ x : Word, InFoot M s x → M'.getMem x = M.getMem x) (hlo : Off M' a = Off M a) : HeldT env M' a s := by
  obtain ⟨hv, hsub⟩ := VecFormT.keep' h.1 hn hh hf
  have key : ∀ x, InFoot M' s x → Off M' a x.toNat := fun x hx => by
    rw [hlo]; exact ⟨h.2.1 x (hsub x hx), h.2.2 x (hsub x hx)⟩
  exact ⟨hv, fun x hx => (key x hx).1, fun x hx => (key x hx).2⟩

/-- **Terms allocated after the entry avoid both buffers.** -/
theorem terms_off {m M : MachineState} {a f : Word} {x0 : Nat} (h1 : VecT env m a 24)
    (h2 : VecT env m (a + 24#64) 24) (hlo : Off M a = Off m a) (hfr : From M f x0) (hx0 : (env.next m).toNat ≤ x0) :
    TermsApart M a f := fun x l1 l2 => by
  rw [hlo]
  exact off_of_ge h1 h2 (by rcases hfr with h | h <;> [(rw [h] at l2; omega); omega])

/-- `t + c + k` as one offset. -/
theorem add_add {t c k d : Word} (h : c + k = d) : t + c + k = t + d := by rw [BitVec.add_assoc, h]

/-- **`self` kept from the entry `m` by `M`** (its 48 bytes, `NEXT` no lower): what `pair` writes from `M` it writes
    from `m`, each slot it writes besides `self` below `NEXT`, and `PostT` from `M` is `PostT` from `m`. -/
theorem self_kept {m M : MachineState} {regs R : Reg → Word} (hV1 : VecT env m (regs .x10) 24)
    (hV2 : VecT env m (regs .x10 + 24#64) 24) (hn : (env.next m).toNat ≤ (env.next M).toNat)
    (hs : ∀ b : Word, (regs .x10).toNat ≤ b.toNat → b.toNat < (regs .x10).toNat + 48 → M.getMem b = m.getMem b)
    (r10 : R .x10 = regs .x10) :
    (∀ b, OutT R M b → OutT regs m b) ∧
      (∀ b, OutT regs m b → b.toNat < (env.next m).toNat ∨ (regs .x10).toNat ≤ b.toNat) ∧
      ∀ r r' m1, PostT env R M r m1 → PostT env regs m r' m1 := by
  have hlt := vecT_lt hV1
  have hlt2 := vecT_lt hV2
  have e24 : (regs .x10 + 24#64).toNat = (regs .x10).toNat + 24 := toNat_add_ofNat (by omega)
  obtain ⟨w0, w8, w16, w24, w32, w40⟩ := kept48 (by omega) hs
  have a8 : regs .x10 + 24#64 + 8#64 = regs .x10 + 32#64 := add_add rfl
  have a16 : regs .x10 + 24#64 + 16#64 = regs .x10 + 40#64 := add_add rfl
  refine ⟨fun b hb => ?_, fun b hb => ?_, fun r r' m1 hP => ?_⟩
  · unfold OutT PairT.SlotOut at hb ⊢
    rw [r10, a8, a16, w0, w8, w16, w24, w32, w40] at hb
    rw [a8, a16]
    exact hb
  · have bv1 := vecT_bufCap hV1
    have bv2 := vecT_bufCap hV2
    unfold OutT PairT.SlotOut InRange at hb
    rw [vecPtr_eq, vecCap_eq] at bv1
    rw [vecPtr_eq, vecCap_eq, a8] at bv2
    rcases hb with hb | hb | hb
    · exact .inr hb.1
    · rcases bv1 with h | ⟨-, h, -⟩
      · omega
      · unfold Env.Live at h
        have : 24 * (m.getMem (regs .x10 + 16#64)).toNat + 24 ≤ (m.getMem (regs .x10)).toNat * 24 := by omega
        exact .inl (by omega)
    · rw [a8, a16] at hb
      rcases bv2 with h | ⟨-, h, -⟩
      · omega
      · unfold Env.Live at h
        have : 24 * (m.getMem (regs .x10 + 40#64)).toNat + 24 ≤ (m.getMem (regs .x10 + 24#64)).toNat * 24 := by
          omega
        exact .inl (by omega)
  · obtain ⟨hFF1, hl1, hl2, hK1, hK2⟩ := hP
    rw [r10] at hl1 hl2 hK1 hK2 hFF1
    refine ⟨hFF1, ?_, ?_, ?_, ?_⟩
    · rw [hl1, vecLen_eq, vecLen_eq, w16]
    · rw [hl2, vecLen_eq, vecLen_eq, a16, w40]
    · rcases hK1 with ⟨hp, hc⟩ | h
      · exact .inl ⟨by rw [hp, vecPtr_eq, vecPtr_eq, w8], by rw [hc, vecCap_eq, vecCap_eq, w0]⟩
      · exact .inr (by omega)
    · rcases hK2 with ⟨hp, hc⟩ | h
      · exact .inl ⟨by rw [hp, vecPtr_eq, vecPtr_eq, a8, w32], by rw [hc, vecCap_eq, vecCap_eq, w24]⟩
      · exact .inr (by omega)

/-- **`pair`'s precondition at instruction 72**, from the invariant at 53 and the stores between. -/
theorem pair_pre {m M : MachineState} {top B : Word} {regs R' : Reg → Word}
    (hpre : PreT env regs m) (h2 : regs .x2 = top) (hW : Windows env top m) (h16 : top.toNat % 16 = 0)
    (hstk : env.stackLimit.toNat + 112 ≤ top.toNat) (hF : env.Frame top Tactic.F m M)
    (hH : HeldT env M (regs .x10) (top + 18446744073709551504#64)) (hB : Blk2 env m M B top)
    (r2 : R' .x2 = top + 18446744073709551504#64) (r10 : R' .x10 = regs .x10)
    (r11 : R' .x11 = top + 18446744073709551504#64) (r12 : R' .x12 = top + 18446744073709551552#64) :
    PairFormT.PreT env R' (chain2 M B top) := by
  obtain ⟨⟨hV1, hV2, ⟨ha1, ha2⟩, -⟩, hal, hFF, -⟩ := hpre
  obtain ⟨b1, b2, b3, bF0, bF1, bF2, bf0, bf1, bf2, bft⟩ := hB
  rw [h2] at ha1
  have hlay := env.layout
  have hge := hW.next_ge
  have htl := hW.top_le
  have hnM := hF.2.1
  have hmM := hF.1
  have hB' : B.toNat + 72 ≤ top.toNat - 112 := by omega
  obtain ⟨cg, c24, c32, c40, c48, c56, c64, s0, s8, s16⟩ := chain2_get (M := M) (by omega) hB'
  have t112 := top_sub (top := top) (c := 18446744073709551504#64) (k := 112) rfl (by omega)
  have t88 := top_sub (top := top) (c := 18446744073709551528#64) (k := 88) rfl (by omega)
  have t64 := top_sub (top := top) (c := 18446744073709551552#64) (k := 64) rfl (by omega)
  have kM : ∀ x : Word, (x.toNat < (env.next m).toNat ∨ top.toNat ≤ x.toNat) → M.getMem x = m.getMem x :=
    fun x hx => hF.2.2 x fun hw => by
      rcases hw with hw | hw | hw | hw
      · omega
      · omega
      · rw [hw] at hx; omega
      · exact hw
  have kC : ∀ x : Word, (x.toNat < (env.next m).toNat ∨ top.toNat ≤ x.toNat) →
      (chain2 M B top).getMem x = m.getMem x := fun x hx => by
    rw [cg x (by omega) (by omega), kM x hx]
  have hnC : env.next (chain2 M B top) = env.next M := cg _ (by omega) (by omega)
  obtain ⟨hFC, hoC⟩ := FlushesFormT.keep hFF (by rw [hnC]; omega) (fun b hb => kC b (.inl hb))
    (fun b h1 h2 => kC b (.inr (by omega)))
  have hoM : Off M (regs .x10) = Off m (regs .x10) := off_eq (by omega) fun b h1 h2 => kM b (.inr (by omega))
  -- the `Form`s of the second block in the stored memory
  have kT : ∀ x : Word, B.toNat + 72 ≤ x.toNat → x.toNat < (env.next M).toNat →
      (chain2 M B top).getMem x = M.getMem x := fun x h1 h2 => cg x (by omega) (by omega)
  have termsK : ∀ f : Word, FormT env M f → From M f (B.toNat + 72) → ∀ x : Word,
      (vecPtr M f).toNat ≤ x.toNat → x.toNat < (vecPtr M f).toNat + 40 * (vecLen M f).toNat →
      (chain2 M B top).getMem x = M.getMem x := fun f hf hfr x l1 l2 => by
    have := hf.foot
    rcases hfr with h | h
    · rw [h] at l2; omega
    · exact kT x (by omega) (by omega)
  have G0 : FormT env (chain2 M B top) B := FormReprT.FormT.keep bF0 (by rw [hnC])
    (fun b l1 l2 => cg b (.inl (by omega)) (.inl (by omega))) (termsK B bF0 bf0)
  have eB : ∀ k, k ≤ 64 → (B + BitVec.ofNat 64 k).toNat = B.toNat + k := fun k hk => toNat_add_ofNat (by omega)
  have e24 := eB 24 (by omega)
  have e48 := eB 48 (by omega)
  obtain ⟨G1, p1, l1⟩ := FormT.move (d := B + 24#64) bF1 (by rw [hnC]) (.inl ⟨by omega, by omega⟩) (by omega) c24
    (by rw [add_add rfl, add_add rfl]; exact c32) (by rw [add_add rfl, add_add rfl]; exact c40)
    (termsK _ bF1 bf1)
  obtain ⟨G2, p2, l2⟩ := FormT.move (d := B + 48#64) bF2 (by rw [hnC]) (.inl ⟨by omega, by omega⟩) (by omega) c48
    (by rw [add_add rfl, add_add rfl]; exact c56) (by rw [add_add rfl, add_add rfl]; exact c64)
    (termsK _ bF2 bf2)
  have from1 : From (chain2 M B top) (B + 24#64) (B.toNat + 72) := by unfold From; rw [p1, l1]; exact bf1
  have from2 : From (chain2 M B top) (B + 48#64) (B.toNat + 72) := by unfold From; rw [p2, l2]; exact bf2
  have from0 : From (chain2 M B top) B (B.toNat + 72) := by
    have hk0 : ∀ k, k ≤ 16 → (chain2 M B top).getMem (B + BitVec.ofNat 64 k) = M.getMem (B + BitVec.ofNat 64 k) :=
      fun k hk => cg _ (.inl (by rw [eB k (by omega)]; omega)) (.inl (by rw [eB k (by omega)]; omega))
    unfold From; rw [vecPtr_eq, vecLen_eq, hk0 8 (by omega), hk0 16 (by omega)]; exact bf0
  have hoC' : Off (chain2 M B top) (regs .x10) = Off m (regs .x10) := hoC
  have sp8 : top + 18446744073709551504#64 + 8#64 = top + 18446744073709551512#64 := add_add rfl
  have sp16 : top + 18446744073709551504#64 + 16#64 = top + 18446744073709551520#64 := add_add rfl
  have hH' : HeldT env (chain2 M B top) (regs .x10) (top + 18446744073709551504#64) :=
    HeldT.keep hH (by rw [hnC]) (fun b l1 l2 => cg b (.inr (by omega)) (.inl (by omega)))
      (fun x hx => cg x (.inl (by have := bft x hx; omega)) (.inl (by have := bft x hx; omega)))
      (by rw [hoC', hoM])
  have hH2 : HeldT env (chain2 M B top) (regs .x10) (top + 18446744073709551552#64) := by
    refine held3 (m := m) (B := B) (.inr ⟨by omega, by omega⟩) (by omega) s0 (by rw [add_add rfl]; exact s8)
      (by rw [add_add rfl]; exact s16) (by omega) b2 (by rw [hnC]; exact b3) (fun i hi => ?_)
      (fun x l1 l2 => off_of_ge hV1 hV2 (by omega)) (fun i hi => ?_) hoC'
    · rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2) with rfl | rfl | rfl
      · simpa using G0
      · exact G1
      · exact G2
    · rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2) with rfl | rfl | rfl
      · simpa using terms_off hV1 hV2 hoC' from0 (by omega)
      · exact terms_off hV1 hV2 hoC' from1 (by omega)
      · exact terms_off hV1 hV2 hoC' from2 (by omega)
  unfold PairFormT.PreT PairT.PreT PairT.FlushesT
  rw [r2, r10, r11, r12]
  refine ⟨⟨⟨hFC.1, hFC.2.1, ⟨by rw [t112]; omega, by omega⟩, hFC.2.2.1⟩, hal, ⟨Nat.le_refl _, by rw [t112]; omega⟩,
    by rw [t112]; omega, ⟨by rw [t112, t64]; omega, by rw [t64]; omega⟩, by rw [t64]; omega,
    .inr (by rw [t112]; omega), .inr (by rw [t64]; omega)⟩, hFC, hH', hH2⟩

/-- `pair`'s postcondition, sealed so that the executor keeps it as one hypothesis. -/
@[irreducible] def PPost (env : Env) (regs : Reg → Word) (m : MachineState) (r' : Reg → Word) (m' : MachineState) :
    Prop :=
  PairFormT.PostT env regs m r' m'

/-- **The return, from `pair`'s**: the saved words kept, the frame, the postcondition. -/
theorem fin_post {m M m1 : MachineState} {top ret B : Word} {regs R' r1 : Reg → Word}
    (hpre : PreT env regs m) (h2 : regs .x2 = top) (hW : Windows env top m)
    (hstk : env.stackLimit.toNat + 112 ≤ top.toNat) (hF : env.Frame top Tactic.F m M) (hsl : Slots M top ret regs)
    (hB : Blk2 env m M B top)
    (hFp : env.Frame (top + 18446744073709551504#64) (PairT.OutT R' (chain2 M B top)) (chain2 M B top) m1)
    (hP : PPost env R' (chain2 M B top) r1 m1) (r10 : R' .x10 = regs .x10) :
    Slots m1 top ret regs ∧ env.Frame top (OutT regs m) m m1 ∧ ∀ r', PostT env regs m r' m1 := by
  obtain ⟨⟨hV1, hV2, ⟨ha1, ha2⟩, -⟩, -, -⟩ := hpre
  rw [h2] at ha1
  have b1 := hB.1
  have b3 := hB.2.2.1
  have hlay := env.layout
  have hge := hW.next_ge
  have htl := hW.top_le
  have hnM := hF.2.1
  have hmM := hF.1
  obtain ⟨cg, -⟩ := chain2_get (M := M) (B := B) (top := top) (by omega) (by omega)
  have t112 := top_sub (top := top) (c := 18446744073709551504#64) (k := 112) rfl (by omega)
  have kM : ∀ x : Word, ¬ env.MayWrite top Tactic.F m M x → M.getMem x = m.getMem x := hF.2.2
  have hnC : env.next (chain2 M B top) = env.next M := cg _ (by omega) (by omega)
  have kC : ∀ x : Word, (x.toNat < (env.next m).toNat ∨ top.toNat ≤ x.toNat) →
      (chain2 M B top).getMem x = m.getMem x := fun x hx => by
    rw [cg x (by omega) (by omega)]
    refine kM x fun hw => ?_
    rcases hw with hw | hw | hw | hw
    · omega
    · omega
    · rw [hw] at hx; omega
    · exact hw
  have nC : (env.next m).toNat ≤ (env.next (chain2 M B top)).toNat := by rw [hnC]; exact hmM
  obtain ⟨hout, slotLow, hpost⟩ := self_kept hV1 hV2 nC (fun x hx _ => kC x (.inr (by omega))) r10
  have k1 : ∀ x : Word, top.toNat - 40 ≤ x.toNat → x.toNat < top.toNat → m1.getMem x = M.getMem x := fun x l1 l2 => by
    rw [← cg x (.inr (by omega)) (.inr l1)]
    refine hFp.2.2 x fun hw => ?_
    rcases hw with hw | hw | hw | hw
    · omega
    · have := hFp.2.1; omega
    · rw [hw] at l1; omega
    · rcases slotLow x (hout x hw) with h | h <;> omega
  have F1 : env.Frame top Tactic.F m (chain2 M B top) := ⟨by rw [hnC]; exact hmM, by rw [hnC]; exact hnM,
    fun x hx => by
      have hx' : ¬ (env.stackLimit.toNat ≤ x.toNat ∧ x.toNat < top.toNat) := fun h => hx (.inl h)
      have hx'' : ¬ ((env.next m).toNat ≤ x.toNat ∧ x.toNat < (env.next (chain2 M B top)).toNat) :=
        fun h => hx (.inr (.inl h))
      rw [hnC] at hx''
      rw [cg x (by omega) (by omega)]
      refine kM x fun hw => hx ?_
      rcases hw with hw | hw | hw | hw
      · exact .inl hw
      · exact .inr (.inl (by rw [hnC]; exact hw))
      · exact .inr (.inr (.inl hw))
      · exact hw.elim⟩
  have F2 : env.Frame top (OutT regs m) m m1 :=
    (Tactic.frame_weaken F1).trans hFp (by omega) fun b hb => .inr (.inr (.inr (hout b hb)))
  obtain ⟨t1, t2, t3, t4, t5⟩ := hsl
  have g : ∀ c : Word, ∀ k, c.toNat + k = 2 ^ 64 → 0 < k → k ≤ 40 → m1.getMem (top + c) = M.getMem (top + c) :=
    fun c k hc h0 hk => by
      have := top_sub (top := top) hc (by omega)
      exact k1 _ (by omega) (by omega)
  refine ⟨⟨by rw [g _ 8 rfl (by omega) (by omega), t1], by rw [g _ 16 rfl (by omega) (by omega), t2],
    by rw [g _ 24 rfl (by omega) (by omega), t3], by rw [g _ 32 rfl (by omega) (by omega), t4],
    by rw [g _ 40 rfl (by omega) (by omega), t5]⟩, F2, fun r' => ?_⟩
  unfold PPost PairFormT.PostT PairT.PostT PairT.PostM at hP
  obtain ⟨⟨-, hl1, hl2, -, -, hK1, hK2⟩, hFF1⟩ := hP
  exact hpost r1 r' m1 ⟨hFF1, hl1, hl2, hK1, hK2⟩

set_option rv_sym.heap true in
/-- **From instruction 53 to the return**: the second block's last two `Form`s and both headers stored, `pair`. -/
theorem fin {env : Env} {p : Lprog (Op Reg) Reg} {i : Nat} {L : Link} (hp : p[i]? = some (tmpl L))
    (_hL : L.WF p) {needP : Nat}
    (hpair : HoldsT env p L.pair.idx needP (PPre env) (PPost env) PairT.OutT AbortStop)
    {Q : State rvIsa → Prop} {ret top : Word} {rest : List Frame} {regs : Reg → Word} {m : MachineState}
    (hk : ∀ r' m', HoldsT.post env (PostT env) OutT ret top regs m r' m' →
      rvIsa.Total p stmtCtx (WinOk p) Q ⟨rest, r', m'⟩)
    (hstop : ∀ fr st r' m', AbortStop regs m r' m' → rvIsa.accept p stmtCtx ⟨fr :: st, r', m'⟩ →
      Q ⟨fr :: st, r', m'⟩)
    (hstk : env.stackLimit.toNat + 112 + needP ≤ top.toNat) (hW : Windows env top m) (h16 : top.toNat % 16 = 0)
    (hpre : PreT env regs m) (h2 : regs .x2 = top) :
    ∀ R M, Regs top regs R → Slots M top ret regs → env.Frame top Tactic.F m M → env.Static M → M.code = m.code →
      HeldT env M (regs .x10) (top + 18446744073709551504#64) → Blk2 env m M (R .x9) top →
      rvIsa.Total p stmtCtx (WinOk p) Q ⟨⟨i, 106, ret, top⟩ :: rest, R, M⟩ := by
  intro R M hR hsl hF hS hcd hH hB
  have b1 := hB.1
  have b2 := hB.2.1
  have b3 := hB.2.2.1
  have hlay := env.layout
  have hnM := hF.2.1
  have hge := hW.next_ge
  have hE := hW.heapEnd_le
  rv_introT hR
  replace hpre : True → PreT env regs m := fun _ => hpre
  replace hH : True → HeldT env M (regs .x10) (top + 18446744073709551504#64) := fun _ => hH
  replace hB : True → Blk2 env m M (R .x9) top := fun _ => hB
  replace hsl : True → Slots M top ret regs := fun _ => hsl
  rv_symT hp with [_hL] using [hpair]
  · unfold PPre
    exact pair_pre (hpre trivial) h2 hW h16 (by omega) hF (hH trivial) (hB trivial) rfl rfl rfl rfl
  all_goals
    obtain ⟨⟨s1, s2, s3, s4, s5⟩, F2, hP⟩ :=
      fin_post (hpre trivial) h2 hW (by omega) hF (hsl trivial) (hB trivial) hret1_14 hret1_16 rfl
  · exact s1
  · exact ⟨⟨rfl, s2, s3, s4, s5, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, F2, hret1_15, hP _⟩


/-- A word a call may not write is kept. -/
theorem fkeep {t x : Word} {out : Word → Prop} {N N' : MachineState} (h : env.Frame t out N N')
    (hlo : x.toNat < env.stackLimit.toNat ∨ t.toNat ≤ x.toNat)
    (hn : x.toNat < (env.next N).toNat ∨ (env.next N').toNat ≤ x.toNat) (hna : x ≠ env.nextAddr) (ho : ¬ out x) :
    N'.getMem x = N.getMem x :=
  h.2.2 x fun hw => by
    rcases hw with hw | hw | hw | hw
    · omega
    · omega
    · exact hna hw
    · exact ho hw

/-- **The state at instruction 53 from the calls since 34**: `alloc`'s block `b`, `constant`'s `Form` in it, the two
    `col`s' `Form`s at `top - 88` and `top - 64`; the saved words, the frame and the first vector kept. -/
theorem blk2_of {m M m1 m3 m4 m5 : MachineState} {top ret b : Word} {regs R3 R4 R5 : Reg → Word}
    {f3 f4 f5 : LeanVM.Protocol.Verifier.Form}
    (hpre : PreT env regs m) (h2 : regs .x2 = top) (hW : Windows env top m) (h16 : top.toNat % 16 = 0)
    (hstk : env.stackLimit.toNat + 112 ≤ top.toNat) (hF : env.Frame top Tactic.F m M) (hsl : Slots M top ret regs)
    (hH : HeldT env M (regs .x10) (top + 18446744073709551504#64))
    (hft : ∀ x, InFoot M (top + 18446744073709551504#64) x → x.toNat < (env.next M).toNat)
    (a1 : env.Frame (top + 18446744073709551504#64) (fun _ => False) M m1) (a2 : (env.next M).toNat ≤ b.toNat)
    (a3 : b.toNat % 8 = 0) (a4 : b.toNat + (72#64).toNat = (env.next m1).toNat)
    (c1 : env.Frame (top + 18446744073709551504#64) (Term.Out R3 m1) m1 m3)
    (c2 : FormIn (env.next m1) (env.next m3) m3 b f3) (c3 : TermAlT.FormAl m3 b)
    (d1 : env.Frame (top + 18446744073709551504#64) (Term.Out R4 m3) m3 m4)
    (d2 : FormIn (env.next m3) (env.next m4) m4 (top + 18446744073709551528#64) f4)
    (d3 : TermAlT.FormAl m4 (top + 18446744073709551528#64))
    (e1 : env.Frame (top + 18446744073709551504#64) (Term.Out R5 m4) m4 m5)
    (e2 : FormIn (env.next m4) (env.next m5) m5 (top + 18446744073709551552#64) f5)
    (e3 : TermAlT.FormAl m5 (top + 18446744073709551552#64))
    (r3 : R3 .x10 = b) (r4 : R4 .x10 = top + 18446744073709551528#64)
    (r5 : R5 .x10 = top + 18446744073709551552#64) :
    Slots m5 top ret regs ∧ env.Frame top Tactic.F m m5 ∧ HeldT env m5 (regs .x10) (top + 18446744073709551504#64) ∧
      Blk2 env m m5 b top := by
  obtain ⟨⟨-, -, ⟨ha1, ha2⟩, -⟩, -, -⟩ := hpre
  rw [h2] at ha1
  have hlay := env.layout
  have hge := hW.next_ge
  have hE := hW.heapEnd_le
  have htl := hW.top_le
  have hnM := hF.2.1
  have hmM := hF.1
  have n1 := a1.1
  have n3 := c1.1
  have n4 := d1.1
  have n5 := e1.1
  have x5 := e1.2.1
  simp only [BitVec.toNat_ofNat] at a4
  have t112 := top_sub (top := top) (c := 18446744073709551504#64) (k := 112) rfl (by omega)
  have t88 := top_sub (top := top) (c := 18446744073709551528#64) (k := 88) rfl (by omega)
  have t64 := top_sub (top := top) (c := 18446744073709551552#64) (k := 64) rfl (by omega)
  have o3 : ∀ x : Word, Term.Out R3 m1 x → (env.next M).toNat ≤ x.toNat ∧ x.toNat < (env.next m1).toNat :=
    fun x hx => by unfold Term.Out InRange at hx; rw [r3] at hx; simp only [Layouts.Form.byteSize] at hx; omega
  have o4 : ∀ x : Word, Term.Out R4 m3 x → top.toNat - 88 ≤ x.toNat ∧ x.toNat < top.toNat - 64 :=
    fun x hx => by unfold Term.Out InRange at hx; rw [r4] at hx; simp only [Layouts.Form.byteSize] at hx; omega
  have o5 : ∀ x : Word, Term.Out R5 m4 x → top.toNat - 64 ≤ x.toNat ∧ x.toNat < top.toNat - 40 :=
    fun x hx => by unfold Term.Out InRange at hx; rw [r5] at hx; simp only [Layouts.Form.byteSize] at hx; omega
  -- a word below `NEXT` at `M` or of the frame from `top - 112` up, outside the `col`s' slots, is kept
  have kAll : ∀ x : Word, (x.toNat < (env.next M).toNat ∨
      (top.toNat - 112 ≤ x.toNat ∧ (x.toNat < top.toNat - 88 ∨ top.toNat - 40 ≤ x.toNat))) →
      m5.getMem x = M.getMem x := fun x hx => by
    have hna : x ≠ env.nextAddr := fun e => by rw [e] at hx; omega
    rw [fkeep e1 (by omega) (by omega) hna (fun h => by have := o5 x h; omega),
      fkeep d1 (by omega) (by omega) hna (fun h => by have := o4 x h; omega),
      fkeep c1 (by omega) (by omega) hna (fun h => by have := o3 x h; omega),
      fkeep a1 (by omega) (by omega) hna id]
  -- below `NEXT` at `m3` (or at `m4`), the `col`s keep
  have k35 : ∀ x : Word, x.toNat < (env.next m3).toNat → m5.getMem x = m3.getMem x := fun x hx => by
    have hna : x ≠ env.nextAddr := fun e => by rw [e] at hx; omega
    rw [fkeep e1 (by omega) (by omega) hna (fun h => by have := o5 x h; omega),
      fkeep d1 (by omega) (by omega) hna (fun h => by have := o4 x h; omega)]
  have k45 : ∀ x : Word, (x.toNat < (env.next m4).toNat ∨ (top.toNat - 112 ≤ x.toNat ∧ x.toNat < top.toNat - 64)) →
      m5.getMem x = m4.getMem x := fun x hx => by
    have hna : x ≠ env.nextAddr := fun e => by rw [e] at hx; omega
    exact fkeep e1 (by omega) (by omega) hna (fun h => by have := o5 x h; omega)
  -- the frame
  have F1 := hF.trans a1 (by omega) fun _ h => h.elim
  have F3 : env.Frame top Tactic.F m m3 := F1.trans c1 (by omega) fun x hx => .inr (.inl (by
    have := o3 x hx; omega))
  have F4 : env.Frame top Tactic.F m m4 := F3.trans d1 (by omega) fun x hx => .inl (by have := o4 x hx; omega)
  have F5 : env.Frame top Tactic.F m m5 := F4.trans e1 (by omega) fun x hx => .inl (by have := o5 x hx; omega)
  -- the saved words
  obtain ⟨t1, t2, t3, t4, t5⟩ := hsl
  have g : ∀ c : Word, ∀ k, c.toNat + k = 2 ^ 64 → 0 < k → k ≤ 40 → m5.getMem (top + c) = M.getMem (top + c) :=
    fun c k hc h0 hk => by
      have := top_sub (top := top) hc (by omega)
      exact kAll _ (.inr ⟨by omega, .inr (by omega)⟩)
  -- the first vector
  have hsp : ∀ x : Word, (top + 18446744073709551504#64).toNat ≤ x.toNat →
      x.toNat < (top + 18446744073709551504#64).toNat + 24 → m5.getMem x = M.getMem x :=
    fun x l1 l2 => kAll x (.inr ⟨by omega, .inl (by omega)⟩)
  have hfoot : ∀ x : Word, InFoot M (top + 18446744073709551504#64) x → m5.getMem x = M.getMem x :=
    fun x hx => kAll x (.inl (hft x hx))
  have ea : ∀ k, k ≤ 40 → (regs .x10 + BitVec.ofNat 64 k).toNat = (regs .x10).toNat + k :=
    fun k hk => toNat_add_ofNat (by omega)
  have hoff : Off m5 (regs .x10) = Off M (regs .x10) := off_eq (by omega) fun x l1 l2 =>
    kAll x (.inr ⟨by omega, .inr (by omega)⟩)
  obtain ⟨-, hsub⟩ := VecFormT.keep' hH.1 (by omega) hsp hfoot
  -- the second block's `Form`s
  have hF3 : FormT env m3 b := TermAlT.formT_of c2 c3 (by omega) (Nat.le_refl _) c1.2.1 hE
    (.inl ⟨by omega, by omega⟩) a3
  have hF4 : FormT env m4 (top + 18446744073709551528#64) := TermAlT.formT_of d2 d3 (by omega) (Nat.le_refl _)
    d1.2.1 hE (.inr ⟨by omega, by omega⟩) (by omega)
  have hF5 : FormT env m5 (top + 18446744073709551552#64) := TermAlT.formT_of e2 e3 (by omega) (Nat.le_refl _)
    x5 hE (.inr ⟨by omega, by omega⟩) (by omega)
  have eb : ∀ k, k ≤ 16 → (b + BitVec.ofNat 64 k).toNat = b.toNat + k := fun k hk => toNat_add_ofNat (by omega)
  have kb : ∀ k, k ≤ 16 → m5.getMem (b + BitVec.ofNat 64 k) = m3.getMem (b + BitVec.ofNat 64 k) :=
    fun k hk => k35 _ (by rw [eb k hk]; omega)
  have pb : vecPtr m5 b = vecPtr m3 b := by rw [vecPtr_eq, vecPtr_eq]; exact kb 8 (by omega)
  have lb : vecLen m5 b = vecLen m3 b := by rw [vecLen_eq, vecLen_eq]; exact kb 16 (by omega)
  have e88 : ∀ k, k ≤ 16 → (top + 18446744073709551528#64 + BitVec.ofNat 64 k).toNat = top.toNat - 88 + k :=
    fun k hk => by rw [toNat_add_ofNat (by omega), t88]
  have k88 : ∀ k, k ≤ 16 → m5.getMem (top + 18446744073709551528#64 + BitVec.ofNat 64 k) =
      m4.getMem (top + 18446744073709551528#64 + BitVec.ofNat 64 k) :=
    fun k hk => k45 _ (.inr ⟨by rw [e88 k hk]; omega, by rw [e88 k hk]; omega⟩)
  have p88 : vecPtr m5 (top + 18446744073709551528#64) = vecPtr m4 (top + 18446744073709551528#64) := by
    rw [vecPtr_eq, vecPtr_eq]; exact k88 8 (by omega)
  have l88 : vecLen m5 (top + 18446744073709551528#64) = vecLen m4 (top + 18446744073709551528#64) := by
    rw [vecLen_eq, vecLen_eq]; exact k88 16 (by omega)
  have fb := FormIn.terms c2
  have f88 := FormIn.terms d2
  have f64 := FormIn.terms e2
  have hb3 := hF3.foot
  have hb4 := hF4.foot
  refine ⟨⟨by rw [g _ 8 rfl (by omega) (by omega), t1], by rw [g _ 16 rfl (by omega) (by omega), t2],
    by rw [g _ 24 rfl (by omega) (by omega), t3], by rw [g _ 32 rfl (by omega) (by omega), t4],
    by rw [g _ 40 rfl (by omega) (by omega), t5]⟩, F5, HeldT.keep hH (by omega) hsp hfoot hoff,
    by omega, a3, by omega, ?_, ?_, hF5, ?_, ?_, ?_, fun x hx => by have := hft x (hsub x hx); omega⟩
  · refine FormReprT.FormT.keep hF3 (by omega) (fun x l1 l2 => k35 x (by omega)) fun x l1 l2 => k35 x ?_
    rcases hb3 with h | ⟨-, h, -⟩ <;> omega
  · refine FormReprT.FormT.keep hF4 (by omega) (fun x l1 l2 => k45 x (.inr ⟨by omega, by omega⟩))
      fun x l1 l2 => k45 x (.inl ?_)
    rcases hb4 with h | ⟨-, h, -⟩ <;> omega
  · unfold From; rw [pb, lb]; rcases fb with h | h <;> omega
  · unfold From; rw [p88, l88]; rcases f88 with h | h <;> omega
  · unfold From; rcases f64 with h | h <;> omega

set_option rv_sym.heap true in
/-- **From instruction 34 to 53**: the second block allocated and its first `Form` written, the two `col`s. -/
theorem mid {env : Env} {p : Lprog (Op Reg) Reg} {i : Nat} {L : Link} (hp : p[i]? = some (tmpl L))
    (hL : L.WF p) {needC needP : Nat}
    (hal : HoldsT env p L.alloc.idx 0 AllocPre (AllocPost env) (Stop := AbortStop))
    (hconst : ConstantAlT.specT env p L.constant.idx) (hcol : ColAlT.colSpecT env p L.col.idx needC)
    (hpanic : Aborts env p L.panicNounwindFmt.idx 0)
    (hpair : HoldsT env p L.pair.idx needP (PPre env) (PPost env) PairT.OutT AbortStop)
    {Q : State rvIsa → Prop} {ret top : Word} {rest : List Frame} {regs : Reg → Word} {m : MachineState}
    (hk : ∀ r' m', HoldsT.post env (PostT env) OutT ret top regs m r' m' →
      rvIsa.Total p stmtCtx (WinOk p) Q ⟨rest, r', m'⟩)
    (hstop : ∀ fr st r' m', AbortStop regs m r' m' → rvIsa.accept p stmtCtx ⟨fr :: st, r', m'⟩ →
      Q ⟨fr :: st, r', m'⟩)
    (hstk : env.stackLimit.toNat + 112 + needP ≤ top.toNat) (hstC : env.stackLimit.toNat + 112 + needC ≤ top.toNat)
    (hstK : env.stackLimit.toNat + 112 + Constant.need ≤ top.toNat)
    (hW : Windows env top m) (h16 : top.toNat % 16 = 0) (hpre : PreT env regs m) (h2 : regs .x2 = top) :
    ∀ R M, Regs top regs R → Slots M top ret regs → env.Frame top Tactic.F m M → env.Static M → M.code = m.code →
      HeldT env M (regs .x10) (top + 18446744073709551504#64) →
      (∀ x, InFoot M (top + 18446744073709551504#64) x → x.toNat < (env.next M).toNat) →
      rvIsa.Total p stmtCtx (WinOk p) Q ⟨⟨i, 68, ret, top⟩ :: rest, R, M⟩ := by
  intro R M hR hsl hF hS hcd hH hft
  have hlay := env.layout
  have hnM := hF.2.1
  have hmM := hF.1
  have hge := hW.next_ge
  have hE := hW.heapEnd_le
  rv_introT hR
  replace hpre : True → PreT env regs m := fun _ => hpre
  replace hH : True → HeldT env M (regs .x10) (top + 18446744073709551504#64) := fun _ => hH
  replace hsl : True → Slots M top ret regs := fun _ => hsl
  replace hft : True → ∀ x, InFoot M (top + 18446744073709551504#64) x → x.toNat < (env.next M).toNat :=
    fun _ => hft
  rv_symT hp stop [106] with [hL] using [hal, hconst 1, hcol, hpanic]
  obtain ⟨s5, F5, hH5, hB5⟩ := blk2_of (hpre trivial) h2 hW h16 (by omega) hF (hsl trivial) (hH trivial) (hft trivial)
    hret1_14 hret1_16 hret1_17 hret1_18 hret3_14 hret3_16 ⟨hret3_17, hret3_18⟩ hret4_14 hret4_16
    ⟨hret4_17, hret4_18⟩ hret5_14 hret5_16 ⟨hret5_17, hret5_18⟩ rfl rfl rfl
  exact fin hp hL hpair hk hstop hstk hW h16 (hpre trivial) h2 _ _
    ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ s5 F5 hret5_15
    (by rw [hret5_19, hret4_19, hret3_19, hret1_19, hcd]) hH5 hB5


/-- The stores of instructions 24 to 33: `npc`'s and `nfp`'s words (`v`, `w`) to `B + 24` and `B + 48`, then the
    header `(3, B, 3)` at `top - 112`. -/
def chain1 (M : MachineState) (B top v0 v8 v16 w0 w8 w16 : Word) : MachineState :=
  ((((((((M.setMem (B + 24#64) v0).setMem (B + 32#64) v8).setMem (B + 40#64) v16).setMem (B + 48#64) w0).setMem
    (B + 56#64) w8).setMem (B + 64#64) w16).setMem (top + 18446744073709551504#64) 3#64).setMem
    (top + 18446744073709551512#64) B).setMem (top + 18446744073709551520#64) 3#64

/-- What `chain1` leaves and writes. -/
theorem chain1_get {M : MachineState} {B top v0 v8 v16 w0 w8 w16 : Word} (h112 : 112 ≤ top.toNat)
    (hB : B.toNat + 72 ≤ top.toNat - 112) :
    (∀ x : Word, (x.toNat < B.toNat + 24 ∨ B.toNat + 72 ≤ x.toNat) →
      (x.toNat < top.toNat - 112 ∨ top.toNat - 88 ≤ x.toNat) →
      (chain1 M B top v0 v8 v16 w0 w8 w16).getMem x = M.getMem x) ∧
    (chain1 M B top v0 v8 v16 w0 w8 w16).getMem (B + 24#64) = v0 ∧
    (chain1 M B top v0 v8 v16 w0 w8 w16).getMem (B + 32#64) = v8 ∧
    (chain1 M B top v0 v8 v16 w0 w8 w16).getMem (B + 40#64) = v16 ∧
    (chain1 M B top v0 v8 v16 w0 w8 w16).getMem (B + 48#64) = w0 ∧
    (chain1 M B top v0 v8 v16 w0 w8 w16).getMem (B + 56#64) = w8 ∧
    (chain1 M B top v0 v8 v16 w0 w8 w16).getMem (B + 64#64) = w16 ∧
    (chain1 M B top v0 v8 v16 w0 w8 w16).getMem (top + 18446744073709551504#64) = 3#64 ∧
    (chain1 M B top v0 v8 v16 w0 w8 w16).getMem (top + 18446744073709551512#64) = B ∧
    (chain1 M B top v0 v8 v16 w0 w8 w16).getMem (top + 18446744073709551520#64) = 3#64 := by
  have eB : ∀ k, k ≤ 64 → (B + BitVec.ofNat 64 k).toNat = B.toNat + k := fun k hk => toNat_add_ofNat (by omega)
  have b24 := eB 24 (by omega)
  have b32 := eB 32 (by omega)
  have b40 := eB 40 (by omega)
  have b48 := eB 48 (by omega)
  have b56 := eB 56 (by omega)
  have b64 := eB 64 (by omega)
  have t112 := top_sub (top := top) (c := 18446744073709551504#64) (k := 112) rfl (by omega)
  have t104 := top_sub (top := top) (c := 18446744073709551512#64) (k := 104) rfl (by omega)
  have t96 := top_sub (top := top) (c := 18446744073709551520#64) (k := 96) rfl (by omega)
  simp only [chain1]
  refine ⟨fun x h1 h2 => ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals
    repeat (first | rw [MachineState.getMem_setMem_eq] | rw [get_ne (by omega)])

/-- **The state at instruction 34 from the entry**: the first block `b` from `alloc`, `constant`'s `Form` in it,
    `npc`'s and `nfp`'s words after it, its header at `top - 112`: the saved words, the frame, the vector held. -/
theorem blk1_of {m m1 m3 : MachineState} {top ret b : Word} {regs R3 : Reg → Word}
    {f3 : LeanVM.Protocol.Verifier.Form}
    (hpre : PreT env regs m) (h2 : regs .x2 = top) (hW : Windows env top m) (h16 : top.toNat % 16 = 0)
    (hstk : env.stackLimit.toNat + 112 ≤ top.toNat) (hnx : (env.next m).toNat ≤ env.heapEnd.toNat)
    (hS : env.Static m)
    (a1 : env.Frame (top + 18446744073709551504#64) (fun _ => False) (PairT.saved m top ret regs) m1)
    (a2 : (env.next m).toNat ≤ b.toNat) (a3 : b.toNat % 8 = 0) (a4 : b.toNat + (72#64).toNat = (env.next m1).toNat)
    (c1 : env.Frame (top + 18446744073709551504#64) (Term.Out R3 m1) m1 m3)
    (c2 : FormIn (env.next m1) (env.next m3) m3 b f3) (c3 : TermAlT.FormAl m3 b) (cS : env.Static m3)
    (r3 : R3 .x10 = b) :
    Slots (chain1 m3 b top (m3.getMem (regs .x11)) (m3.getMem (regs .x11 + 8#64)) (m3.getMem (regs .x11 + 16#64))
        (m3.getMem (regs .x12)) (m3.getMem (regs .x12 + 8#64)) (m3.getMem (regs .x12 + 16#64))) top ret regs ∧
      env.Frame top Tactic.F m (chain1 m3 b top (m3.getMem (regs .x11)) (m3.getMem (regs .x11 + 8#64))
        (m3.getMem (regs .x11 + 16#64)) (m3.getMem (regs .x12)) (m3.getMem (regs .x12 + 8#64))
        (m3.getMem (regs .x12 + 16#64))) ∧
      env.Static (chain1 m3 b top (m3.getMem (regs .x11)) (m3.getMem (regs .x11 + 8#64))
        (m3.getMem (regs .x11 + 16#64)) (m3.getMem (regs .x12)) (m3.getMem (regs .x12 + 8#64))
        (m3.getMem (regs .x12 + 16#64))) ∧
      HeldT env (chain1 m3 b top (m3.getMem (regs .x11)) (m3.getMem (regs .x11 + 8#64))
        (m3.getMem (regs .x11 + 16#64)) (m3.getMem (regs .x12)) (m3.getMem (regs .x12 + 8#64))
        (m3.getMem (regs .x12 + 16#64))) (regs .x10) (top + 18446744073709551504#64) := by
  generalize hC : chain1 m3 b top (m3.getMem (regs .x11)) (m3.getMem (regs .x11 + 8#64))
    (m3.getMem (regs .x11 + 16#64)) (m3.getMem (regs .x12)) (m3.getMem (regs .x12 + 8#64))
    (m3.getMem (regs .x12 + 16#64)) = C
  obtain ⟨⟨hV1, hV2, ⟨ha1, ha2⟩, -⟩, -, hFF, ⟨hn1, hn2⟩, ⟨hp1, hp2⟩, hN, hP, hTN, hTP⟩ := hpre
  rw [h2] at ha1 hn1 hp1
  have hlay := env.layout
  have hge := hW.next_ge
  have hE := hW.heapEnd_le
  have htl := hW.top_le
  have n1 := a1.1
  have n3 := c1.1
  have x3 := c1.2.1
  simp only [BitVec.toNat_ofNat] at a4
  obtain ⟨S1, S2, S3, S4⟩ := PairT.saved_ok (top := top) (ret := ret) (regs := regs) (out := Tactic.F) (by omega) hnx hS
  rw [S3] at n1
  obtain ⟨cg, c24, c32, c40, c48, c56, c64, s0, s8, s16⟩ := chain1_get (M := m3) (B := b) (top := top)
    (v0 := m3.getMem (regs .x11)) (v8 := m3.getMem (regs .x11 + 8#64)) (v16 := m3.getMem (regs .x11 + 16#64))
    (w0 := m3.getMem (regs .x12)) (w8 := m3.getMem (regs .x12 + 8#64)) (w16 := m3.getMem (regs .x12 + 16#64))
    (by omega) (by omega)
  rw [hC] at cg c24 c32 c40 c48 c56 c64 s0 s8 s16
  have o3 : ∀ x : Word, Term.Out R3 m1 x → (env.next m).toNat ≤ x.toNat ∧ x.toNat < (env.next m1).toNat :=
    fun x hx => by unfold Term.Out InRange at hx; rw [r3] at hx; simp only [Layouts.Form.byteSize] at hx; omega
  have F3 : env.Frame top Tactic.F m m3 := (S1.trans a1 (by
    rw [top_sub (top := top) (c := 18446744073709551504#64) (k := 112) rfl (by omega)]; omega) fun _ h => h.elim).trans
    c1 (by rw [top_sub (top := top) (c := 18446744073709551504#64) (k := 112) rfl (by omega)]; omega)
    fun x hx => .inr (.inl (by have := o3 x hx; rw [S3] at *; omega))
  have t112 := top_sub (top := top) (c := 18446744073709551504#64) (k := 112) rfl (by omega)
  have hnC : env.next C = env.next m3 := cg _ (by omega) (by omega)
  have F : env.Frame top Tactic.F m C := ⟨by rw [hnC]; exact F3.1, by rw [hnC]; exact x3, fun x hx => by
    have hx' : ¬ (env.stackLimit.toNat ≤ x.toNat ∧ x.toNat < top.toNat) := fun h => hx (.inl h)
    have hx'' : ¬ ((env.next m).toNat ≤ x.toNat ∧ x.toNat < (env.next C).toNat) := fun h => hx (.inr (.inl h))
    rw [hnC] at hx''
    rw [cg x (by omega) (by omega)]
    refine F3.2.2 x fun hw => hx ?_
    rcases hw with hw | hw | hw | hw
    · exact .inl hw
    · exact .inr (.inl (by rw [hnC]; exact hw))
    · exact .inr (.inr (.inl hw))
    · exact hw.elim⟩
  have xC := F.2.1
  have nC := F.1
  have kC : ∀ x : Word, (x.toNat < (env.next m).toNat ∨ top.toNat ≤ x.toNat) → C.getMem x = m.getMem x :=
    fun x hx => F.2.2 x fun hw => by
      rcases hw with hw | hw | hw | hw
      · omega
      · omega
      · rw [hw] at hx; omega
      · exact hw
  -- the saved words
  obtain ⟨t1, t2, t3, t4, t5⟩ := S4
  have g : ∀ c : Word, ∀ k, c.toNat + k = 2 ^ 64 → 0 < k → k ≤ 40 →
      C.getMem (top + c) = (PairT.saved m top ret regs).getMem (top + c) := fun c k hc h0 hk => by
    have := top_sub (top := top) hc (by omega)
    have hna : top + c ≠ env.nextAddr := fun e => by rw [e] at this; omega
    rw [cg _ (by omega) (by omega), fkeep c1 (by omega) (by omega) hna (fun h => by have := o3 _ h; omega),
      fkeep a1 (by omega) (by omega) hna id]
  -- the static data
  have hstat : env.Static C := by
    rw [← hC]; simp only [chain1]
    have eB : ∀ k, k ≤ 64 → (b + BitVec.ofNat 64 k).toNat = b.toNat + k := fun k hk => toNat_add_ofNat (by omega)
    have := eB 24 (by omega); have := eB 32 (by omega); have := eB 40 (by omega); have := eB 48 (by omega)
    have := eB 56 (by omega); have := eB 64 (by omega)
    have := top_sub (top := top) (c := 18446744073709551512#64) (k := 104) rfl (by omega)
    have := top_sub (top := top) (c := 18446744073709551520#64) (k := 96) rfl (by omega)
    repeat (first | exact cS | refine Tactic.static_store ?_ (by omega))
  -- the held vector
  have hoC : Off C (regs .x10) = Off m (regs .x10) := off_eq (by omega) fun x l1 l2 => kC x (.inr (by omega))
  have kT : ∀ x : Word, x.toNat < (env.next m).toNat → C.getMem x = m.getMem x := fun x hx => kC x (.inl hx)
  have hF0 : FormT env m3 b := TermAlT.formT_of c2 c3 (by omega) (Nat.le_refl _) x3 hE (.inl ⟨by omega, by omega⟩) a3
  have fb := FormIn.terms c2
  have hb0 := hF0.foot
  have eb : ∀ k, k ≤ 16 → (b + BitVec.ofNat 64 k).toNat = b.toNat + k := fun k hk => toNat_add_ofNat (by omega)
  have kb : ∀ x : Word, (b.toNat ≤ x.toNat ∧ x.toNat < b.toNat + 24) ∨ ((env.next m1).toNat ≤ x.toNat ∧
      x.toNat < (env.next m3).toNat) → C.getMem x = m3.getMem x := fun x hx => cg x (by omega) (by omega)
  have G0 : FormT env C b := FormReprT.FormT.keep hF0 (by rw [hnC]) (fun x l1 l2 => kb x (.inl ⟨l1, l2⟩))
    fun x l1 l2 => kb x (.inr (by rcases fb with h | h <;> omega))
  have p0 : vecPtr C b = vecPtr m3 b := by rw [vecPtr_eq, vecPtr_eq]; exact kb _ (.inl (by rw [eb 8 (by omega)]; omega))
  have l0 : vecLen C b = vecLen m3 b := by
    rw [vecLen_eq, vecLen_eq]; exact kb _ (.inl (by rw [eb 16 (by omega)]; omega))
  have hNf := hN.foot
  have hPf := hP.foot
  have e24 : (b + 24#64).toNat = b.toNat + 24 := toNat_add_ofNat (by omega)
  have e48 : (b + 48#64).toNat = b.toNat + 48 := toNat_add_ofNat (by omega)
  have k3 : ∀ x : Word, top.toNat ≤ x.toNat → m3.getMem x = m.getMem x := fun x hx => F3.2.2 x fun hw => by
    rcases hw with hw | hw | hw | hw
    · omega
    · have := F3.2.1; omega
    · rw [hw] at hx; omega
    · exact hw
  have en : ∀ x : Word, ∀ k, k ≤ 16 → top.toNat ≤ x.toNat → x.toNat + 24 ≤ 0xc0000000 →
      m3.getMem (x + BitVec.ofNat 64 k) = m.getMem (x + BitVec.ofNat 64 k) := fun x k hk h1 h2 =>
    k3 _ (by rw [toNat_add_ofNat (by omega)]; omega)
  obtain ⟨G1, p1, q1⟩ := FormT.move (d := b + 24#64) hN (by omega) (.inl ⟨by omega, by omega⟩) (by omega)
    (by rw [c24, k3 _ (by omega)])
    (by rw [add_add (d := 32#64) rfl, c32]; exact en _ 8 (by omega) (by omega) (by omega))
    (by rw [add_add (d := 40#64) rfl, c40]; exact en _ 16 (by omega) (by omega) (by omega))
    fun x l1 l2 => kT x (by rcases hNf with h | ⟨-, h, -⟩ <;> omega)
  obtain ⟨G2, p2, q2⟩ := FormT.move (d := b + 48#64) hP (by omega) (.inl ⟨by omega, by omega⟩) (by omega)
    (by rw [c48, k3 _ (by omega)])
    (by rw [add_add (d := 56#64) rfl, c56]; exact en _ 8 (by omega) (by omega) (by omega))
    (by rw [add_add (d := 64#64) rfl, c64]; exact en _ 16 (by omega) (by omega) (by omega))
    fun x l1 l2 => kT x (by rcases hPf with h | ⟨-, h, -⟩ <;> omega)
  have from0 : From C b (b.toNat + 72) := by unfold From; rw [p0, l0]; rcases fb with h | h <;> omega
  refine ⟨⟨by rw [g _ 8 rfl (by omega) (by omega), t1], by rw [g _ 16 rfl (by omega) (by omega), t2],
    by rw [g _ 24 rfl (by omega) (by omega), t3], by rw [g _ 32 rfl (by omega) (by omega), t4],
    by rw [g _ 40 rfl (by omega) (by omega), t5]⟩, F, hstat, ?_⟩
  refine held3 (m := m) (B := b) (.inr ⟨by omega, by omega⟩) (by omega) s0 (by rw [add_add rfl]; exact s8)
    (by rw [add_add rfl]; exact s16) (by omega) a3 (by rw [hnC]; omega) (fun i hi => ?_)
    (fun x l1 l2 => off_of_ge hV1 hV2 (by omega)) (fun i hi => ?_) hoC
  · rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2) with rfl | rfl | rfl
    · simpa using G0
    · exact G1
    · exact G2
  · rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2) with rfl | rfl | rfl
    · simpa using terms_off hV1 hV2 hoC from0 (by omega)
    · intro x l1 l2
      rw [hoC]
      simp only [p1, q1] at l1 l2
      exact hTN x l1 l2
    · intro x l1 l2
      rw [hoC]
      simp only [p2, q2] at l1 l2
      exact hTP x l1 l2

/-- The precondition, sealed so that the executor keeps it as one hypothesis. -/
@[irreducible] def PreS (env : Env) (regs : Reg → Word) (m : MachineState) : Prop := PreT env regs m

theorem preS_eq : PreS env = PreT env := by unfold PreS; rfl

set_option rv_sym.heap true in
theorem total (env : Env) (p : Lprog (Op Reg) Reg) (i : Nat) (L : Link) (hp : p[i]? = some (tmpl L)) (hL : L.WF p)
    {need needC needP : Nat} (hnC : 112 + needC ≤ need) (hnK : 112 + Constant.need ≤ need)
    (hnP : 112 + needP ≤ need)
    (halloc : AllocSpecT env p L.alloc.idx 0) (hconst : ConstantAlT.specT env p L.constant.idx)
    (hcol : ColAlT.colSpecT env p L.col.idx needC) (hpair : PairFormT.SpecT env p L.pair.idx needP)
    (hpanic : Aborts env p L.panicNounwindFmt.idx 0) : SpecT env p i need := by
  have hal' : HoldsT env p L.alloc.idx 0 AllocPre (AllocPost env) (Stop := AbortStop) :=
    halloc.mono_stop fun _ _ _ _ _ h => h.1
  have hpair' : HoldsT env p L.pair.idx needP (PPre env) (PPost env) PairT.OutT AbortStop := by
    unfold PPre PPost; exact hpair
  suffices h : HoldsT env p i need (PreS env) (PostT env) OutT AbortStop by rwa [preS_eq] at h
  rv_autoT hp stop [68] with [hL, hnC, hnK, hnP] using [hal', hconst 1, hpanic]
  all_goals
    have hP : PreT env regs m := by rw [← preS_eq]; exact hpre_6
    have hlay := env.layout
    have hA := hpre_8.nextAddr_ge
    have hE := hpre_8.heapEnd_le
    have hw1 : InWin env (regs .x11) 24 := hP.2.2.2.2.2.1.1.1
    have ha1 : (regs .x11).toNat % 8 = 0 := hP.2.2.2.2.2.1.1.2.1.2.1
    have hw2 : InWin env (regs .x12) 24 := hP.2.2.2.2.2.2.1.1.1
    have ha2 : (regs .x12).toNat % 8 = 0 := hP.2.2.2.2.2.2.1.1.2.1.2.1
    unfold InWin at hw1 hw2
    have e : ∀ x : Word, ∀ k, k ≤ 16 → x.toNat + 24 ≤ 0xc0000000 → (x + BitVec.ofNat 64 k).toNat = x.toNat + k :=
      fun x k hk hx => toNat_add_ofNat (by omega)
    have e18 := e (regs .x11) 8 (by omega) (by omega)
    have e116 := e (regs .x11) 16 (by omega) (by omega)
    have e28 := e (regs .x12) 8 (by omega) (by omega)
    have e216 := e (regs .x12) 16 (by omega) (by omega)
  all_goals try (apply inWindow_iff.2; first | (simp only [e18, e116, e28, e216]; omega) | omega)
  all_goals try (first | (simp only [e18, e116, e28, e216]; omega) | omega)
  obtain ⟨s1, F1, S1, H1⟩ := blk1_of hP hpre_2 hpre_8 hpre_7 (by omega) hpre_5 hpre_4 hret1_14 hret1_16 hret1_17
    hret1_18 hret3_14 hret3_16 ⟨hret3_17, hret3_18⟩ hret3_15 rfl
  refine mid hp hL hal' (hconst := hconst) hcol hpanic hpair' hk hstop (by omega) (by omega) (by omega) hpre_8
    hpre_7 hP hpre_2 _ _ ?_ s1 F1 S1 ?_ H1 fun x hx => VecFormT.foot_lt H1.1 hx
  · exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  · simp only [MachineState.code_setMem, hret3_19, hret1_19]

end Rv64mc.Proof.Layout.StateDerivedT

/-- info: 'Rv64mc.Proof.Layout.StateDerivedT.total' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Rv64mc.Proof.Layout.StateDerivedT.total
