/-
  Rv64mc.Proof.Layout.ConcatFormT

  `<[&[Form]] as Concat<Form>>::concat` is total: called with the result's slot (`a0`) and an array of exactly three
  slices of `Form`s (`a1`, each a pointer and a length, 16 bytes), it sums the lengths, checks the sum against
  `isize::MAX / 24` (a word of the static data; `handle_error` above), allocates the result's block (none when the sum
  is `0`; `handle_error` when `alloc` fails), builds the header `(sum, block, 0)` in its frame, extends it by each
  slice (`Vec<Form>::spec_extend`, `SpecExtendFormT`, which clones each `Form`) and copies the header to `sret`. The
  run ends with the guest's abort (`AbortStop`) where `alloc`, `spec_extend` or `handle_error` does. A safety-only
  contract (class D); it does not state the `Form`s' values.

  The precondition: the result's slot a caller's (`SretPre`), in a window and 8-byte aligned; the array a caller's
  (`Owned`), in a window and 8-byte aligned; each slice `SliceFT`: empty, or in a window, below `NEXT` or at or above
  the stack pointer, each element a `Form`. At its one caller, `Flushes::counted` (198, template steps 33 and 48),
  the array and `sret` are slots of its frame, the slices its arguments' `Form`s, a `Form` of its frame and the
  `col` it built.

  The postcondition: the result a `Vec<Form>` (`VecFormT`) of the lengths' sum, its buffer and every terms' block of
  its `Form`s allocated by the call (`PostT.foot`: its whole footprint lies between `NEXT` at entry and at exit), which
  is what `counted` needs to push it into a `Flushes` (`PairFormT.HeldT`).

  The body is cut at the join after `alloc` (instruction 74, `Inv74`), after each `spec_extend` (96, 112) and at the
  copy to `sret` (128); the vector at `sp + 8` is described at each cut by `Acc` (its length, its capacity the sum,
  its `Form`s and their terms' blocks above its buffer). Each part is its own declaration. `spec_extend`'s
  precondition and postcondition (`SEPre`, `SEPost`) and this function's postcondition (`PostS`) are sealed, so that
  the executor leaves each as one goal or hypothesis.

  ## Main definitions

  * `SliceFT`, `tot`, `PreT`, `PostT`, `SpecT`, `Above`, `Acc`, `hdr`, `Slots`, `Saved`, `saved`

  ## Main results

  * `PostT.foot`, `se_pre`, `acc_step`, `fin_post`, `total`
-/

import Rv64mc.Proof.Layout.SpecExtendFormT
import Rv64mc.Proof.Layout.PairFormT
import Rv64mc.Gen.Tmpl.Alloc.Slice.SliceRefSliceForm.AsConcatForm.Concat

namespace Rv64mc.Proof.Layout.ConcatFormT

open RiscvZkvm.Rv64 Lprog Lprog.RiscV Rv64mc.Spec.Runtime
open Rv64mc.Proof.Runtime (Aborts)
open Rv64mc.Proof.Runtime.MemsetT (InWin)
open Rv64mc.Proof.Runtime.VecReprT (BufT RawVecT VecT)
open Rv64mc.Proof.Runtime.AllocT (AllocSpecT)
open Rv64mc.Proof.Layout.FormReprT
open Rv64mc.Proof.Runtime.GrowOne (rvCapAt_eq rvPtrAt_eq)
open Rv64mc.Proof.Runtime.VecHdrT (vecCap_eq vecPtr_eq vecLen_eq)
open Rv64mc.Proof.Layout.FromElemVecFormT (VecFormT)
open Rv64mc.Proof.Layout.CloneFormsFreshT (FreshTermsT)
open Rv64mc.Proof.Layout.ExtendTrustedT (InFoot)
open Rv64mc.Gen.Alloc.Slice.SliceRefSliceForm.AsConcatForm.Concat (Link tmpl d_c8_d6dfd6bc_words)

variable {env : Env}

/-- **A slice of `n` `Form`s at `q`**: empty, or in a window, below `NEXT` or at or above `top` (a caller's frame),
    each element a `Form`. -/
def SliceFT (env : Env) (m : MachineState) (top q n : Word) : Prop :=
  n.toNat = 0 ∨ (InWin env q (24 * n.toNat) ∧
    (q.toNat + 24 * n.toNat ≤ (env.next m).toNat ∨ top.toNat ≤ q.toNat) ∧ FormsT env m q n.toNat)

/-- The three slices' lengths' sum, for the array at `a`. -/
def tot (m : MachineState) (a : Word) : Nat :=
  (m.getMem (a + 8#64)).toNat + (m.getMem (a + 24#64)).toNat + (m.getMem (a + 40#64)).toNat

/-- The total precondition: the result's slot a caller's, in a window and aligned; the array of three slices a
    caller's, in a window and aligned; each slice `SliceFT`. -/
def PreT (env : Env) (regs : Reg → Word) (m : MachineState) : Prop :=
  SretPre env regs m ∧ InWin env (regs .x10) 24 ∧ (regs .x10).toNat % 8 = 0 ∧
    env.Owned m (regs .x2) (regs .x11) 48 ∧ InWin env (regs .x11) 48 ∧ (regs .x11).toNat % 8 = 0 ∧
    SliceFT env m (regs .x2) (m.getMem (regs .x11)) (m.getMem (regs .x11 + 8#64)) ∧
    SliceFT env m (regs .x2) (m.getMem (regs .x11 + 16#64)) (m.getMem (regs .x11 + 24#64)) ∧
    SliceFT env m (regs .x2) (m.getMem (regs .x11 + 32#64)) (m.getMem (regs .x11 + 40#64))

/-- The total postcondition: the result a `Vec<Form>` of the lengths' sum, its buffer (unless empty) and its `Form`s'
    terms' blocks allocated since the entry. -/
def PostT (env : Env) (regs : Reg → Word) (m : MachineState) (_r' : Reg → Word) (m' : MachineState) : Prop :=
  VecFormT env m' (regs .x10) ∧ (vecLen m' (regs .x10)).toNat = tot m (regs .x11) ∧
    ((vecCap m' (regs .x10)).toNat = 0 ∨
      env.Fresh m m' (vecPtr m' (regs .x10)) (24 * (vecCap m' (regs .x10)).toNat)) ∧
    FreshTermsT env m m' (vecPtr m' (regs .x10)) (vecLen m' (regs .x10)).toNat

/-- **The total contract of `<[&[Form]] as Concat<Form>>::concat`.** -/
def SpecT (env : Env) (p : Lprog (Op Reg) Reg) (i need : Nat) : Prop :=
  HoldsT env p i need (PreT env) (PostT env) SretVecOut AbortStop

/-- **The result's footprint is fresh**: its buffer's `Form`s and their terms' blocks lie between `NEXT` at entry
    and at exit. -/
theorem PostT.foot {regs r' : Reg → Word} {m m' : MachineState} (h : PostT env regs m r' m') :
    ∀ b, InFoot m' (regs .x10) b → (env.next m).toNat ≤ b.toNat ∧ b.toNat < (env.next m').toNat := by
  obtain ⟨⟨hV, -⟩, -, hc, hT⟩ := h
  have hle := hV.2.2
  intro b hb
  rcases hb with ⟨h1, h2⟩ | ⟨i, hi, h1, h2⟩
  · rcases hc with h0 | ⟨f1, f2⟩
    · omega
    · have : 24 * (vecLen m' (regs .x10)).toNat ≤ 24 * (vecCap m' (regs .x10)).toNat := Nat.mul_le_mul_left _ hle
      omega
  · rcases hT i hi with h0 | ⟨f1, f2⟩
    · omega
    · omega

/-! ## The vector at `sp + 8` -/

/-- **Each of the `n` `Form`s from `q` has no terms or its terms' block in `[lo, NEXT)`.** -/
def Above (env : Env) (M : MachineState) (q : Word) (n lo : Nat) : Prop :=
  ∀ i, i < n → (vecLen M (q + BitVec.ofNat 64 (24 * i))).toNat = 0 ∨
    (lo ≤ (vecPtr M (q + BitVec.ofNat 64 (24 * i))).toNat ∧
      (vecPtr M (q + BitVec.ofNat 64 (24 * i))).toNat + 40 * (vecLen M (q + BitVec.ofNat 64 (24 * i))).toNat ≤
        (env.next M).toNat)

/-- **The vector at `H`** with `n` `Form`s and capacity `c`: its buffer none or allocated since the entry `m`, its
    `Form`s `FormsT`, their terms' blocks after the buffer. -/
def Acc (env : Env) (m M : MachineState) (H : Word) (n c : Nat) : Prop :=
  VecT env M H 24 ∧ (vecLen M H).toNat = n ∧ (vecCap M H).toNat = c ∧
    (c = 0 ∨ (env.next m).toNat ≤ (vecPtr M H).toNat) ∧ FormsT env M (vecPtr M H) n ∧
    Above env M (vecPtr M H) n ((vecPtr M H).toNat + 24 * c)

/-- A vector's buffer below `NEXT` and below `2 ^ 64`. -/
theorem buf_live {M : MachineState} {H : Word} (hV : VecT env M H 24) :
    (vecCap M H).toNat = 0 ∨ (0x10000000 ≤ (vecPtr M H).toNat ∧
      (vecPtr M H).toNat + 24 * (vecCap M H).toNat ≤ (env.next M).toNat) := by
  rcases PairFormT.vecT_bufCap hV with h | ⟨h1, h2, -⟩
  · exact .inl h
  · unfold Env.Live at h2; exact .inr ⟨h1, by omega⟩

/-- `q + 24 (n + j)` as `q + 24 n + 24 j`. -/
theorem add24 (q : Word) (n j : Nat) :
    q + BitVec.ofNat 64 (24 * (n + j)) = q + BitVec.ofNat 64 (24 * n) + BitVec.ofNat 64 (24 * j) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
  omega

/-- **`Form`s whose headers and terms' blocks lie in `[lo, NEXT)` are kept** by a memory agreeing there, `NEXT`
    no lower. -/
theorem forms_keep {M M' : MachineState} {q : Word} {n lo L : Nat} (hF : FormsT env M q n)
    (hA : Above env M q n L) (hq : n = 0 ∨ (lo ≤ q.toNat ∧ q.toNat + 24 * n ≤ (env.next M).toNat))
    (hL : lo ≤ L) (hn : (env.next M).toNat ≤ (env.next M').toNat)
    (hk : ∀ x : Word, lo ≤ x.toNat → x.toNat < (env.next M).toNat → M'.getMem x = M.getMem x) :
    FormsT env M' q n ∧ Above env M' q n L := by
  have hlay := env.layout
  have e : ∀ i, i < n → (q + BitVec.ofNat 64 (24 * i)).toNat = q.toNat + 24 * i := fun i hi =>
    toNat_add_ofNat (by have := env.heapEnd.isLt; have := (env.next M).isLt; omega)
  have hh : ∀ i, i < n → ∀ x : Word, (q + BitVec.ofNat 64 (24 * i)).toNat ≤ x.toNat →
      x.toNat < (q + BitVec.ofNat 64 (24 * i)).toNat + 24 → M'.getMem x = M.getMem x := fun i hi x h1 h2 => by
    rw [e i hi] at h1 h2
    exact hk x (by omega) (by omega)
  have hp : ∀ i, i < n → vecPtr M' (q + BitVec.ofNat 64 (24 * i)) = vecPtr M (q + BitVec.ofNat 64 (24 * i)) ∧
      vecLen M' (q + BitVec.ofNat 64 (24 * i)) = vecLen M (q + BitVec.ofNat 64 (24 * i)) := fun i hi => by
    have ei := e i hi
    have : (q + BitVec.ofNat 64 (24 * i)).toNat + 24 < 2 ^ 64 := by have := (env.next M).isLt; omega
    have e8 : (q + BitVec.ofNat 64 (24 * i) + 8#64).toNat = q.toNat + 24 * i + 8 := by
      rw [toNat_add_ofNat (a := q + BitVec.ofNat 64 (24 * i)) (k := 8) (by omega), ei]
    have e16 : (q + BitVec.ofNat 64 (24 * i) + 16#64).toNat = q.toNat + 24 * i + 16 := by
      rw [toNat_add_ofNat (a := q + BitVec.ofNat 64 (24 * i)) (k := 16) (by omega), ei]
    rw [vecPtr_eq, vecPtr_eq, vecLen_eq, vecLen_eq]
    exact ⟨hh i hi _ (by omega) (by omega), hh i hi _ (by omega) (by omega)⟩
  refine ⟨fun i hi => (hF i hi).keep hn (hh i hi) fun x h1 h2 => ?_, fun i hi => ?_⟩
  · rcases hA i hi with h0 | ⟨a1, a2⟩
    · omega
    · exact hk x (by omega) (by omega)
  · rw [(hp i hi).1, (hp i hi).2]
    exact (hA i hi).imp id fun ⟨a1, a2⟩ => ⟨a1, by omega⟩

/-- `Above` for a lower bound. -/
theorem Above.mono {M : MachineState} {q : Word} {n lo lo' : Nat} (h : Above env M q n lo) (hl : lo' ≤ lo) :
    Above env M q n lo' := fun i hi => (h i hi).imp id fun ⟨a1, a2⟩ => ⟨by omega, a2⟩

/-! ## The calls to `spec_extend` -/

/-- **A slice kept**: its `Form`s and their headers' words, from the entry `m` to `M`, when `M` agrees with `m`
    below `NEXT` at entry and at or above the stack top. -/
theorem src_keep {m M : MachineState} {top q l : Word} (hs : SliceFT env m top q l) (hl : l.toNat ≠ 0)
    (hkM : ∀ x : Word, (x.toNat < (env.next m).toNat ∨ top.toNat ≤ x.toNat) → M.getMem x = m.getMem x)
    (hnM : (env.next m).toNat ≤ (env.next M).toNat) :
    FormsT env M q l.toNat ∧ ∀ i, i < l.toNat →
      vecLen M (q + BitVec.ofNat 64 (24 * i)) = vecLen m (q + BitVec.ofNat 64 (24 * i)) ∧
      vecPtr M (q + BitVec.ofNat 64 (24 * i)) = vecPtr m (q + BitVec.ofNat 64 (24 * i)) := by
  rcases hs with h0 | ⟨hw, hq, hF⟩
  · exact absurd h0 hl
  have hw' := hw
  unfold InWin at hw'
  have e : ∀ i, i < l.toNat → (q + BitVec.ofNat 64 (24 * i)).toNat = q.toNat + 24 * i := fun i hi =>
    toNat_add_ofNat (by omega)
  have hh : ∀ i, i < l.toNat → ∀ x : Word, (q + BitVec.ofNat 64 (24 * i)).toNat ≤ x.toNat →
      x.toNat < (q + BitVec.ofNat 64 (24 * i)).toNat + 24 → M.getMem x = m.getMem x := fun i hi x h1 h2 => by
    rw [e i hi] at h1 h2
    exact hkM x (by omega)
  refine ⟨fun i hi => (hF i hi).keep hnM (hh i hi) fun x h1 h2 => ?_, fun i hi => ?_⟩
  · rcases (hF i hi).foot with h0 | ⟨-, a2, -⟩
    · omega
    · exact hkM x (.inl (by omega))
  · have ei := e i hi
    have e8 : (q + BitVec.ofNat 64 (24 * i) + 8#64).toNat = q.toNat + 24 * i + 8 := by
      rw [toNat_add_ofNat (a := q + BitVec.ofNat 64 (24 * i)) (k := 8) (by omega), ei]
    have e16 : (q + BitVec.ofNat 64 (24 * i) + 16#64).toNat = q.toNat + 24 * i + 16 := by
      rw [toNat_add_ofNat (a := q + BitVec.ofNat 64 (24 * i)) (k := 16) (by omega), ei]
    rw [vecPtr_eq, vecPtr_eq, vecLen_eq, vecLen_eq]
    exact ⟨hh i hi _ (by omega) (by omega), hh i hi _ (by omega) (by omega)⟩

/-- A slice's bytes as a number: `q + 24 l` does not wrap. -/
theorem slice_end {m : MachineState} {top q l : Word} (hs : SliceFT env m top q l)
    (hE : env.heapEnd.toNat ≤ 0x78000000) : q.toNat + 24 * l.toNat ≤ 0xc0000000 ∨ l.toNat = 0 := by
  have := env.layout
  rcases hs with h0 | ⟨hw, -, -⟩
  · exact .inr h0
  · unfold InWin at hw; exact .inl (by omega)

/-- **`spec_extend`'s precondition at a call**, from the vector at `H = sp + 8` and the slice. -/
theorem se_pre {m M : MachineState} {top H q l : Word} {n c : Nat} {R : Reg → Word}
    (hW : Windows env top m) (hlim : env.stackLimit.toNat + 96 ≤ top.toNat)
    (hA : Acc env m M H n c) (hH : H.toNat = top.toNat - 88)
    (hkM : ∀ x : Word, (x.toNat < (env.next m).toNat ∨ top.toNat ≤ x.toNat) → M.getMem x = m.getMem x)
    (hnM : (env.next m).toNat ≤ (env.next M).toNat) (hMx : (env.next M).toNat ≤ env.heapEnd.toNat)
    (hs : SliceFT env m top q l) (hroom : n + l.toNat ≤ c)
    (r2 : (R .x2).toNat = top.toNat - 96) (r10 : R .x10 = H) (r11 : R .x11 = q)
    (r12 : (R .x12).toNat = q.toNat + 24 * l.toNat) : SpecExtendFormT.PreT env R M := by
  obtain ⟨hV, hn, hc, hc0, hFs, hAb⟩ := hA
  have hlay := env.layout
  have := hW.top_le
  have hx := hW.next_ge
  have hbl := buf_live hV
  have hcnt : SpecExtendFormT.cnt R = l.toNat := by unfold SpecExtendFormT.cnt; rw [r12, r11]; omega
  have hle := slice_end hs hW.heapEnd_le
  unfold SpecExtendFormT.PreT SpecExtendFormT.spareLo SpecExtendFormT.spareHi
  rw [hcnt, r10, r11, r12, hn, hc]
  rw [hc] at hbl
  refine ⟨hV, ⟨by omega, by omega⟩, hFs, fun i hi => ?_, by omega, by omega, by omega, ?_, ?_, ?_⟩
  · rcases hAb i hi with h0 | ⟨a1, -⟩
    · exact .inl h0
    · exact .inr (.inr a1)
  · by_cases hl0 : l.toNat = 0
    · exact .inl hl0
    rcases hs with h0 | ⟨hw, hq, -⟩
    · exact absurd h0 hl0
    unfold InWin at hw
    refine .inr ⟨?_, ?_, ?_⟩
    · unfold OffStack; omega
    · rcases hq with h | h
      · exact .inl (by omega)
      · exact .inr (by omega)
    · rcases hc0 with h | h
      · omega
      rcases hq with h' | h'
      · exact .inl (by omega)
      · exact .inr (by rcases hbl with h0 | ⟨-, h2⟩ <;> have := hW.heapEnd_le <;> omega)
  · by_cases hl0 : l.toNat = 0
    · intro i hi; omega
    exact (src_keep hs hl0 hkM hnM).1
  · intro i hi
    have hl0 : l.toNat ≠ 0 := by omega
    obtain ⟨e1, e2⟩ := (src_keep hs hl0 hkM hnM).2 i hi
    rw [e1, e2]
    rcases hs with h0 | ⟨-, -, hF⟩
    · exact absurd h0 hl0
    rcases (hF i hi).foot with h0 | ⟨-, a2, -⟩
    · exact .inl h0
    · rcases hc0 with h | h
      · omega
      · exact .inr (.inl (by omega))

/-- What `spec_extend` writes besides its stack and fresh blocks, for the vector at `H = sp + 8`: `H`'s 24 bytes, or
    its new slots, in its buffer (so the capacity is not `0`). -/
theorem out_cases {m M : MachineState} {top H : Word} {n c : Nat} {R : Reg → Word} (hA : Acc env m M H n c)
    (h88 : 88 ≤ top.toNat) (hH : H.toNat = top.toNat - 88) (r10 : R .x10 = H) :
    ∀ b, SpecExtendFormT.OutT R M b → (top.toNat - 88 ≤ b.toNat ∧ b.toNat < top.toNat - 64) ∨
      ((vecPtr M H).toNat + 24 * n ≤ b.toNat ∧ b.toNat < (vecPtr M H).toNat + 24 * (n + SpecExtendFormT.cnt R)) := by
  obtain ⟨-, hn, -, -, -, -⟩ := hA
  intro b hb
  unfold SpecExtendFormT.OutT SpecExtendFormT.SlotOut SpecExtendFormT.spareLo at hb
  rw [r10, hn] at hb
  rcases hb with hb | hb
  · unfold InRange at hb; simp only [Layouts.Vec.byteSize] at hb; exact .inl ⟨by omega, by omega⟩
  · exact .inr ⟨hb.1, by omega⟩

/-- **After a `spec_extend`** on the vector at `H = sp + 8` with `l` more `Form`s: the vector `l` longer, the frame,
    and the words from `top - 64` (the saved registers) kept. -/
theorem acc_step {m M M' : MachineState} {top H : Word} {n c l : Nat} {R r' : Reg → Word}
    (hW : Windows env top m) (hlim : env.stackLimit.toNat + 96 ≤ top.toNat)
    (hA : Acc env m M H n c) (hH : H.toNat = top.toNat - 88) (r10 : R .x10 = H)
    (hcnt : SpecExtendFormT.cnt R = l) (hroom : n + l ≤ c) (hF : env.Frame top Tactic.F m M)
    (hFs : env.Frame (top + 18446744073709551520#64) (SpecExtendFormT.OutT R M) M M')
    (hP : SpecExtendFormT.PostT env R M r' M') :
    Acc env m M' H (n + l) c ∧ env.Frame top Tactic.F m M' ∧
      ∀ x : Word, top.toNat - 64 ≤ x.toNat → x.toNat < top.toNat → M'.getMem x = M.getMem x := by
  have hout := out_cases hA (by omega) hH r10
  rw [hcnt] at hout
  obtain ⟨hV, hn, hc, hc0, -, hAb⟩ := hA
  obtain ⟨hV', hl', hc', hp', hF', -, hFT⟩ := hP
  rw [r10] at hV' hl' hc' hp' hF' hFT
  rw [hn, hcnt] at hl' hF' hFT
  have hlay := env.layout
  have := hW.top_le
  have hx := hW.next_ge
  have e96 : (top + 18446744073709551520#64).toNat = top.toNat - 96 :=
    Runtime.CloneT.toNat_add_neg (k := 96) rfl (by omega)
  have hbl := buf_live hV
  rw [hc] at hbl
  have nM := hF.1
  have xM := hF.2.1
  have nM' := hFs.1
  have xM' := hFs.2.1
  have kS : ∀ x : Word, (x.toNat < (env.next M).toNat ∧ ((vecPtr M H).toNat ≤ x.toNat →
      x.toNat < (vecPtr M H).toNat + 24 * n)) ∨ top.toNat - 64 ≤ x.toNat → M'.getMem x = M.getMem x :=
    fun x hx' => hFs.2.2 x fun hw => by
      rcases hw with hw | hw | hw | hw
      · rw [e96] at hw; omega
      · omega
      · rw [hw] at hx'; omega
      · rcases hout x hw with h | ⟨h1, h2⟩
        · omega
        · rcases hbl with h' | ⟨h1', h2'⟩
          · omega
          · omega
  refine ⟨⟨hV', by rw [hl'], by rw [hc', hc], by rw [hp']; exact hc0, by rw [hp']; exact hF', ?_⟩,
    hF.trans hFs (by rw [e96]; omega) fun b hb => ?_, fun x h1 h2 => kS x (.inr h1)⟩
  · rw [hp']
    intro i hi
    have hc1 : c ≠ 0 := by omega
    rcases hbl with h0 | ⟨hb1, hb2⟩
    · exact absurd h0 hc1
    have ei : (vecPtr M H + BitVec.ofNat 64 (24 * i)).toNat = (vecPtr M H).toNat + 24 * i :=
      toNat_add_ofNat (by have := (env.next M).isLt; omega)
    by_cases hin : i < n
    · have e8 : (vecPtr M H + BitVec.ofNat 64 (24 * i) + 8#64).toNat = (vecPtr M H).toNat + 24 * i + 8 := by
        rw [toNat_add_ofNat (a := vecPtr M H + BitVec.ofNat 64 (24 * i)) (k := 8) (by have := (env.next M).isLt; omega),
          ei]
      have e16 : (vecPtr M H + BitVec.ofNat 64 (24 * i) + 16#64).toNat = (vecPtr M H).toNat + 24 * i + 16 := by
        rw [toNat_add_ofNat (a := vecPtr M H + BitVec.ofNat 64 (24 * i)) (k := 16)
          (by have := (env.next M).isLt; omega), ei]
      have kp : vecPtr M' (vecPtr M H + BitVec.ofNat 64 (24 * i)) = vecPtr M (vecPtr M H + BitVec.ofNat 64 (24 * i)) := by
        rw [vecPtr_eq M', vecPtr_eq M (vecPtr M H + _)]; exact kS _ (.inl ⟨by omega, fun _ => by omega⟩)
      have kl : vecLen M' (vecPtr M H + BitVec.ofNat 64 (24 * i)) = vecLen M (vecPtr M H + BitVec.ofNat 64 (24 * i)) := by
        rw [vecLen_eq M', vecLen_eq M (vecPtr M H + _)]; exact kS _ (.inl ⟨by omega, fun _ => by omega⟩)
      rw [kp, kl]
      exact (hAb i hin).imp id fun ⟨a1, a2⟩ => ⟨a1, by omega⟩
    · obtain ⟨j, rfl⟩ : ∃ j, i = n + j := ⟨i - n, by omega⟩
      rw [add24]
      rcases hFT j (by omega) with h0 | ⟨f1, f2⟩
      · exact .inl h0
      · exact .inr ⟨by omega, f2⟩
  · rcases hout b hb with h | ⟨h1, h2⟩
    · exact .inl ⟨by omega, by omega⟩
    · have h0 : c ≠ 0 := by omega
      rcases hbl with h' | ⟨h1', h2'⟩
      · exact absurd h' h0
      rcases hc0 with h'' | h''
      · exact absurd h'' h0
      exact .inr (.inl ⟨by omega, by omega⟩)

/-! ## The header and the copy to `sret` -/

/-- The header `(c, B, 0)` stored at `sp + 8 = top - 88`. -/
abbrev hdr (M : MachineState) (top c B : Word) : MachineState :=
  ((M.setMem (top + 18446744073709551528#64) c).setMem (top + 18446744073709551536#64) B).setMem
    (top + 18446744073709551544#64) 0#64

/-- **The header built**: a vector of no `Form`s over the block `B` of `c` (none when `c = 0`) allocated since the
    entry; the frame, the static data and the words from `top - 64` kept. -/
theorem hdr_ok {m M : MachineState} {top c B : Word} (hlim : env.stackLimit.toNat + 96 ≤ top.toNat)
    (h16 : top.toNat % 16 = 0) (hW : Windows env top m) (hF : env.Frame top Tactic.F m M) (hS : env.Static M)
    (hc : c.toNat * 24 < 2 ^ 63) (hB : c.toNat = 0 ∨ (env.Fresh m M B (c.toNat * 24) ∧ B.toNat % 8 = 0)) :
    Acc env m (hdr M top c B) (top + 18446744073709551528#64) 0 c.toNat ∧ env.Frame top Tactic.F m (hdr M top c B) ∧
      env.Static (hdr M top c B) ∧
      ∀ x : Word, top.toNat - 64 ≤ x.toNat → x.toNat < top.toNat → (hdr M top c B).getMem x = M.getMem x := by
  have hlay := env.layout
  have := hW.top_le
  have := hW.next_ge
  have hnM := hF.2.1
  have g : ∀ c : Word, ∀ k, c.toNat + k = 2 ^ 64 → k ≤ 96 → (top + c).toNat = top.toNat - k :=
    fun c k hc hk => Runtime.CloneT.toNat_add_neg hc (by omega)
  have e88 := g 18446744073709551528#64 88 rfl (by omega)
  have e80 := g 18446744073709551536#64 80 rfl (by omega)
  have e72 := g 18446744073709551544#64 72 rfl (by omega)
  have ne : ∀ a b : Word, a.toNat ≠ b.toNat → a ≠ b := fun a b hab e => hab (by rw [e])
  have r0 : (hdr M top c B).getMem (top + 18446744073709551528#64) = c := by
    simp only [hdr]
    rw [MachineState.getMem_setMem_ne (ne _ _ (by omega)), MachineState.getMem_setMem_ne (ne _ _ (by omega)),
      MachineState.getMem_setMem_eq]
  have r8 : (hdr M top c B).getMem (top + 18446744073709551528#64 + 8#64) = B := by
    have : top + 18446744073709551528#64 + 8#64 = top + 18446744073709551536#64 := by rw [BitVec.add_assoc]; rfl
    simp only [hdr]
    rw [this, MachineState.getMem_setMem_ne (ne _ _ (by omega)), MachineState.getMem_setMem_eq]
  have r16 : (hdr M top c B).getMem (top + 18446744073709551528#64 + 16#64) = 0#64 := by
    have : top + 18446744073709551528#64 + 16#64 = top + 18446744073709551544#64 := by rw [BitVec.add_assoc]; rfl
    simp only [hdr]
    rw [this, MachineState.getMem_setMem_eq]
  have hN : env.next (hdr M top c B) = env.next M := by
    simp only [hdr]
    rw [Env.next_setMem_stack (by omega), Env.next_setMem_stack (by omega), Env.next_setMem_stack (by omega)]
  have hcap : vecCap (hdr M top c B) (top + 18446744073709551528#64) = c := by rw [vecCap_eq, r0]
  have hptr : vecPtr (hdr M top c B) (top + 18446744073709551528#64) = B := by rw [vecPtr_eq, r8]
  have hlen : vecLen (hdr M top c B) (top + 18446744073709551528#64) = 0#64 := by rw [vecLen_eq, r16]
  have hw : InWin env (top + 18446744073709551528#64) 24 := .inr ⟨by omega, by omega⟩
  refine ⟨⟨⟨hw, ⟨.inr ⟨by omega, by simp only [Layouts.RawVecInner.byteSize]; omega⟩, by omega, ?_, ?_⟩, ?_⟩,
    by rw [hlen]; rfl, by rw [hcap], ?_, fun i hi => absurd hi (by omega), fun i hi => absurd hi (by omega)⟩,
    ?_, ?_, fun x h1 h2 => ?_⟩
  · rw [rvCapAt_eq, rvPtrAt_eq, ← vecCap_eq, ← vecPtr_eq, hcap, hptr]
    exact hB.imp_right fun ⟨⟨h1, h2⟩, h3⟩ => ⟨by omega, by unfold Env.Live; rw [hN]; omega, h3⟩
  · rw [rvCapAt_eq, ← vecCap_eq, hcap]; omega
  · rw [hlen, hcap]; simp
  · rw [hptr]; exact hB.imp_right fun ⟨⟨h1, _⟩, _⟩ => h1
  · exact Tactic.frame_slot (Tactic.frame_slot (Tactic.frame_slot hF (by omega) (by omega)) (by omega) (by omega))
      (by omega) (by omega)
  · exact Env.static_setMem_stack (Env.static_setMem_stack (Env.static_setMem_stack hS (by omega)) (by omega))
      (by omega)
  · simp only [hdr]
    rw [MachineState.getMem_setMem_ne (ne _ _ (by omega)), MachineState.getMem_setMem_ne (ne _ _ (by omega)),
      MachineState.getMem_setMem_ne (ne _ _ (by omega))]

/-- **The result's header copied** to `sret` from the vector at `sp + 8`: the postcondition, the frame, the static
    data, and the words from `top - 64` kept. -/
theorem fin_post {m M : MachineState} {top : Word} {regs : Reg → Word} (h2 : regs .x2 = top)
    (hpre : PreT env regs m) (hW : Windows env top m) (hlim : env.stackLimit.toNat + 96 ≤ top.toNat)
    (hF : env.Frame top Tactic.F m M) (hS : env.Static M)
    (hA : Acc env m M (top + 18446744073709551528#64) (tot m (regs .x11)) (tot m (regs .x11))) {r : Reg → Word} :
    let M3 := ((M.setMem (regs .x10) (M.getMem (top + 18446744073709551528#64))).setMem (regs .x10 + 8#64)
      (M.getMem (top + 18446744073709551536#64))).setMem (regs .x10 + 16#64) (M.getMem (top + 18446744073709551544#64))
    PostT env regs m r M3 ∧ env.Frame top (SretVecOut regs m) m M3 ∧ env.Static M3 ∧
      ∀ x : Word, top.toNat - 64 ≤ x.toNat → x.toNat < top.toNat → M3.getMem x = M.getMem x := by
  intro M3
  obtain ⟨hsret, hwin, hal, -⟩ := hpre
  obtain ⟨hV, hn, hc, hc0, hFs, hAb⟩ := hA
  have hlay := env.layout
  have := hW.nextAddr_ge
  have := hW.top_le
  have hx := hW.next_ge
  have nM := hF.1
  have xM := hF.2.1
  have hown' : env.Owned m top (regs .x10) 24 := by rw [← h2]; exact hsret
  have h24 := hown'.2
  have ho := hown'.1
  have e8 : (regs .x10 + 8#64).toNat = (regs .x10).toNat + 8 := toNat_add_ofNat (by omega)
  have e16 : (regs .x10 + 16#64).toNat = (regs .x10).toNat + 16 := toNat_add_ofNat (by omega)
  have ne : ∀ a b : Word, a.toNat ≠ b.toNat → a ≠ b := fun a b hab e => hab (by rw [e])
  have hwin' := hwin
  unfold InWin at hwin'
  have hnx : ∀ k, k ≤ 16 → ∀ b : Word, b.toNat = (regs .x10).toNat + k → b ≠ env.nextAddr := fun k hk b hb e => by
    rw [e] at hb; rcases hwin' with h | h <;> omega
  have hout : ∀ k, k ≤ 16 → ∀ b : Word, b.toNat = (regs .x10).toNat + k → SretVecOut regs m b := fun k hk b hb => by
    show InRange (regs .x10) Layouts.Vec.byteSize b; unfold InRange Layouts.Vec.byteSize; omega
  have hst : ∀ k, k ≤ 16 → ∀ b : Word, b.toNat = (regs .x10).toNat + k →
      b.toNat < env.staticLo.toNat ∨ env.staticHi.toNat ≤ b.toNat := fun k hk b hb => by
    rcases hwin' with h | h <;> omega
  have n1 := Tactic.next_setMem (N := M) (v := M.getMem (top + 18446744073709551528#64)) (hnx 0 (by omega) _ rfl)
  have n2 := Tactic.next_setMem (N := M.setMem (regs .x10) (M.getMem (top + 18446744073709551528#64)))
    (v := M.getMem (top + 18446744073709551536#64)) (hnx 8 (by omega) _ e8)
  have n3 := Tactic.next_setMem (N := (M.setMem (regs .x10) (M.getMem (top + 18446744073709551528#64))).setMem
    (regs .x10 + 8#64) (M.getMem (top + 18446744073709551536#64))) (v := M.getMem (top + 18446744073709551544#64))
    (hnx 16 (by omega) _ e16)
  have hN : env.next M3 = env.next M := by simp only [M3]; rw [n3, n2, n1]
  have hs8 : top + 18446744073709551528#64 + 8#64 = top + 18446744073709551536#64 := by rw [BitVec.add_assoc]; rfl
  have hs16 : top + 18446744073709551528#64 + 16#64 = top + 18446744073709551544#64 := by
    rw [BitVec.add_assoc]; rfl
  have r0 : M3.getMem (regs .x10) = M.getMem (top + 18446744073709551528#64) := by
    simp only [M3]
    rw [MachineState.getMem_setMem_ne (ne _ _ (by omega)), MachineState.getMem_setMem_ne (ne _ _ (by omega)),
      MachineState.getMem_setMem_eq]
  have r8 : M3.getMem (regs .x10 + 8#64) = M.getMem (top + 18446744073709551528#64 + 8#64) := by
    simp only [M3]
    rw [MachineState.getMem_setMem_ne (ne _ _ (by omega)), MachineState.getMem_setMem_eq, hs8]
  have r16 : M3.getMem (regs .x10 + 16#64) = M.getMem (top + 18446744073709551528#64 + 16#64) := by
    simp only [M3]; rw [MachineState.getMem_setMem_eq, hs16]
  have kx : ∀ x : Word, (x.toNat < (regs .x10).toNat ∨ (regs .x10).toNat + 24 ≤ x.toNat) →
      M3.getMem x = M.getMem x := fun x hx' => by
    simp only [M3]
    rw [MachineState.getMem_setMem_ne (ne _ _ (by omega)), MachineState.getMem_setMem_ne (ne _ _ (by omega)),
      MachineState.getMem_setMem_ne (ne _ _ (by omega))]
  have hv := Layout.CloneFormsT.vecT_copy hV hwin hal (by rw [hN]) r0 r8 r16
  have hl3 : vecLen M3 (regs .x10) = vecLen M (top + 18446744073709551528#64) := by rw [vecLen_eq, vecLen_eq, r16]
  have hp3 : vecPtr M3 (regs .x10) = vecPtr M (top + 18446744073709551528#64) := by rw [vecPtr_eq, vecPtr_eq, r8]
  have hc3 : vecCap M3 (regs .x10) = vecCap M (top + 18446744073709551528#64) := by rw [vecCap_eq, vecCap_eq, r0]
  have hbl := buf_live hV
  rw [hc] at hbl
  have hFA : FormsT env M3 (vecPtr M (top + 18446744073709551528#64)) (tot m (regs .x11)) ∧
      Above env M3 (vecPtr M (top + 18446744073709551528#64)) (tot m (regs .x11)) (env.next m).toNat := by
    by_cases ht : tot m (regs .x11) = 0
    · rw [ht]; exact ⟨fun i hi => absurd hi (by omega), fun i hi => absurd hi (by omega)⟩
    rcases hc0 with h | h
    · exact absurd h ht
    rcases hbl with h' | ⟨h1', h2'⟩
    · exact absurd h' ht
    refine forms_keep hFs (hAb.mono (by omega)) (.inr ⟨h, by omega⟩) (Nat.le_refl _) (by rw [hN]) fun x l1 l2 => kx x ?_
    rcases ho with ho | ho <;> omega
  refine ⟨⟨⟨hv, by rw [hp3, hl3, hn]; exact hFA.1⟩, by rw [hl3, hn], ?_, ?_⟩, ?_, ?_, fun x l1 l2 => kx x ?_⟩
  · rw [hc3, hp3, hc]
    rcases hc0 with h | h
    · exact .inl h
    · rcases hbl with h' | ⟨h1', h2'⟩
      · exact .inl h'
      · exact .inr ⟨h, by rw [hN]; omega⟩
  · rw [hp3, hl3, hn]
    have := hFA.2
    unfold Above at this
    rw [hN] at this
    unfold FreshTermsT
    rw [hN]
    exact this
  · simp only [M3]
    exact Tactic.frame_out (Tactic.frame_out (Tactic.frame_out (Tactic.frame_weaken hF) (hout 0 (by omega) _ rfl)
      (hnx 0 (by omega) _ rfl)) (hout 8 (by omega) _ e8) (hnx 8 (by omega) _ e8)) (hout 16 (by omega) _ e16)
      (hnx 16 (by omega) _ e16)
  · simp only [M3]
    exact Tactic.static_store (Tactic.static_store (Tactic.static_store hS (hst 0 (by omega) _ rfl))
      (hst 8 (by omega) _ e8)) (hst 16 (by omega) _ e16)
  · rcases ho with ho | ho <;> omega

/-! ## The parts -/

/-- The postcondition, sealed so that the executor keeps it as one goal at the return. -/
@[irreducible] def PostS (env : Env) (regs : Reg → Word) (m : MachineState) (r' : Reg → Word) (m' : MachineState) :
    Prop :=
  PostT env regs m r' m'

theorem postS_eq : PostS env = PostT env := by unfold PostS; rfl

/-- The prologue's eight saved words in `M`, at `top - 8` down to `top - 64`. -/
def Slots (M : MachineState) (top ret : Word) (regs : Reg → Word) : Prop :=
  M.getMem (top + 18446744073709551608#64) = ret ∧ M.getMem (top + 18446744073709551600#64) = regs .x8 ∧
    M.getMem (top + 18446744073709551592#64) = regs .x9 ∧ M.getMem (top + 18446744073709551584#64) = regs .x18 ∧
    M.getMem (top + 18446744073709551576#64) = regs .x19 ∧ M.getMem (top + 18446744073709551568#64) = regs .x20 ∧
    M.getMem (top + 18446744073709551560#64) = regs .x21 ∧ M.getMem (top + 18446744073709551552#64) = regs .x22

/-- The saved slots kept by a memory agreeing from `top - 64` to `top`. -/
theorem Slots.keep {M M' : MachineState} {top ret : Word} {regs : Reg → Word} (h : Slots M top ret regs)
    (h64 : 64 ≤ top.toNat)
    (hk : ∀ x : Word, top.toNat - 64 ≤ x.toNat → x.toNat < top.toNat → M'.getMem x = M.getMem x) :
    Slots M' top ret regs := by
  obtain ⟨t1, t2, t3, t4, t5, t6, t7, t8⟩ := h
  have g : ∀ c : Word, ∀ k, c.toNat + k = 2 ^ 64 → 0 < k → k ≤ 64 → M'.getMem (top + c) = M.getMem (top + c) :=
    fun c k hc h0 hk' => by
      have e := Runtime.CloneT.toNat_add_neg (t := top) hc (by omega)
      exact hk _ (by omega) (by omega)
  exact ⟨(g _ 8 rfl (by omega) (by omega)).trans t1, (g _ 16 rfl (by omega) (by omega)).trans t2,
    (g _ 24 rfl (by omega) (by omega)).trans t3, (g _ 32 rfl (by omega) (by omega)).trans t4,
    (g _ 40 rfl (by omega) (by omega)).trans t5, (g _ 48 rfl (by omega) (by omega)).trans t6,
    (g _ 56 rfl (by omega) (by omega)).trans t7, (g _ 64 rfl (by omega) (by omega)).trans t8⟩

/-- The five saved registers the function does not save, the entry's. -/
def Saved (regs R : Reg → Word) : Prop :=
  R .x23 = regs .x23 ∧ R .x24 = regs .x24 ∧ R .x25 = regs .x25 ∧ R .x26 = regs .x26 ∧ R .x27 = regs .x27

set_option rv_sym.heap true in
/-- **The return**, from instruction 128: the result's header copied to `sret`, the saved registers. -/
theorem fin {p : Lprog (Op Reg) Reg} {i : Nat} {L : Link} (hp : p[i]? = some (tmpl L))
    (_hL : L.WF p) {Q : State rvIsa → Prop} {ret top : Word} {rest : List Frame} {regs : Reg → Word}
    {m : MachineState}
    (hk : ∀ r' m', HoldsT.post env (PostT env) SretVecOut ret top regs m r' m' →
      rvIsa.Total p stmtCtx (WinOk p) Q ⟨rest, r', m'⟩)
    (hW : Windows env top m) (h2 : regs .x2 = top) (hpre : PreT env regs m)
    (hlim : env.stackLimit.toNat + 96 ≤ top.toNat) (h16 : top.toNat % 16 = 0) :
    ∀ R M, (R .x2 = top + 18446744073709551520#64 ∧ R .x8 = regs .x10 ∧ Saved regs R) → Slots M top ret regs →
      env.Frame top Tactic.F m M → env.Static M → M.code = m.code →
      Acc env m M (top + 18446744073709551528#64) (tot m (regs .x11)) (tot m (regs .x11)) →
      rvIsa.Total p stmtCtx (WinOk p) Q ⟨⟨i, 128, ret, top⟩ :: rest, R, M⟩ := by
  intro R M hR hsl hF hS hcd hA
  have hlay := env.layout
  have := hW.nextAddr_ge
  obtain ⟨hPost, hF', hS', hk3⟩ := fin_post (r := fun _ => 0#64) h2 hpre hW hlim hF hS hA
  obtain ⟨t1, t2, t3, t4, t5, t6, t7, t8⟩ := hsl
  obtain ⟨hsret, hwin, hal, -⟩ := hpre
  obtain ⟨-, -, -, -, -⟩ := hR.2.2
  have hwin' := hwin
  unfold InWin at hwin'
  have := hsret.2
  have hW1 := hW.heapEnd_le
  have w0 : inWindow (regs .x10) 8 = true := by rw [inWindow_iff]; omega
  have w8 : inWindow (regs .x10 + 8#64) 8 = true := by rw [inWindow_iff, toNat_add_ofNat (by omega)]; omega
  have w16 : inWindow (regs .x10 + 16#64) 8 = true := by rw [inWindow_iff, toNat_add_ofNat (by omega)]; omega
  clear hA hk3
  rw [← postS_eq] at hk
  have hPost' : True → PostT env regs m (fun _ => 0#64) _ := fun _ => hPost
  clear hPost
  rv_introT hR
  rv_symT hp with [_hL]
  rw [postS_eq]
  exact hPost' trivial

/-- `spec_extend`'s precondition, sealed so that the executor leaves it as one goal. -/
@[irreducible] def SEPre (env : Env) (regs : Reg → Word) (m : MachineState) : Prop :=
  SpecExtendFormT.PreT env regs m

/-- `spec_extend`'s postcondition, sealed so that the executor keeps it as one hypothesis. -/
@[irreducible] def SEPost (env : Env) (regs : Reg → Word) (m : MachineState) (r' : Reg → Word) (m' : MachineState) :
    Prop :=
  SpecExtendFormT.PostT env regs m r' m'

theorem se_spec {p : Lprog (Op Reg) Reg} {i need : Nat} (h : SpecExtendFormT.SpecT env p i need) :
    HoldsT env p i need (SEPre env) (SEPost env) SpecExtendFormT.OutT AbortStop := by
  unfold SEPre SEPost; exact h

/-- What the function's frame keeps: the heap below `NEXT` at entry and the caller's frame. -/
theorem keepM {m M : MachineState} {top : Word} (hlim : env.stackLimit.toNat ≤ top.toNat)
    (hF : env.Frame top Tactic.F m M) :
    ∀ x : Word, (x.toNat < (env.next m).toNat ∨ top.toNat ≤ x.toNat) → M.getMem x = m.getMem x :=
  fun x hx => hF.2.2 x fun hw => by
    have := env.layout
    have := hF.2.1
    have := hF.1
    rcases hw with hw | hw | hw | hw
    · omega
    · omega
    · rw [hw] at hx; omega
    · exact hw

/-- `q + 24 l`, as the code computes it. -/
theorem sh24 {q l : Word} (h : q.toNat + 24 * l.toNat < 2 ^ 64) :
    (q + (l <<< 4 + l <<< 3)).toNat = q.toNat + 24 * l.toNat := by
  simp only [BitVec.toNat_add, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]
  omega

/-- The array's words kept from the entry. -/
theorem arr_keep {m M : MachineState} {top : Word} {regs : Reg → Word} (hlim : env.stackLimit.toNat ≤ top.toNat) (h2 : regs .x2 = top) (hpre : PreT env regs m)
    (hF : env.Frame top Tactic.F m M) {k : Nat} (hk : k < 48) :
    M.getMem (regs .x11 + BitVec.ofNat 64 k) = m.getMem (regs .x11 + BitVec.ofNat 64 k) := by
  have hlay := env.layout
  obtain ⟨-, -, -, hown, hwa, -⟩ := hpre
  rw [h2] at hown
  unfold InWin at hwa
  have : (regs .x11 + BitVec.ofNat 64 k).toNat = (regs .x11).toNat + k := toNat_add_ofNat (by omega)
  exact keepM hlim hF _ (by rcases hown.1 with h | h <;> omega)

/-- **A slice's `spec_extend`**: its precondition, from the vector at `sp + 8` and the slice. -/
theorem call_pre {m M : MachineState} {top q l : Word} {n c : Nat} {R : Reg → Word}
    (hW : Windows env top m) (hlim : env.stackLimit.toNat + 96 ≤ top.toNat)
    (hF : env.Frame top Tactic.F m M) (hA : Acc env m M (top + 18446744073709551528#64) n c)
    (hs : SliceFT env m top q l) (hroom : n + l.toNat ≤ c)
    (r2 : R .x2 = top + 18446744073709551520#64) (r10 : R .x10 = top + 18446744073709551528#64)
    (r11 : R .x11 = q) (r12 : R .x12 = q + (l <<< 4 + l <<< 3)) : SEPre env R M := by
  have hlay := env.layout
  have := hW.top_le
  have e96 : (top + 18446744073709551520#64).toNat = top.toNat - 96 :=
    Runtime.CloneT.toNat_add_neg (k := 96) rfl (by omega)
  have e88 : (top + 18446744073709551528#64).toNat = top.toNat - 88 :=
    Runtime.CloneT.toNat_add_neg (k := 88) rfl (by omega)
  unfold SEPre
  refine se_pre hW hlim hA e88 (keepM (by omega) hF) hF.1 hF.2.1 hs hroom (by rw [r2, e96]) r10 r11 ?_
  rw [r12]
  rcases slice_end hs hW.heapEnd_le with h | h
  · exact sh24 (by omega)
  · have e0 : l = 0#64 := BitVec.eq_of_toNat_eq (by rw [h]; rfl)
    subst e0
    simp

/-- **After a slice's `spec_extend`**: the vector longer by the slice, the frame, the saved slots. -/
theorem call_post {m M m1 : MachineState} {top ret q l : Word} {n c : Nat} {regs R r1 : Reg → Word}
    (hW : Windows env top m) (hlim : env.stackLimit.toNat + 96 ≤ top.toNat) (hsl : Slots M top ret regs)
    (hF : env.Frame top Tactic.F m M) (hA : Acc env m M (top + 18446744073709551528#64) n c)
    (hroom : n + l.toNat ≤ c) (hb : q.toNat + 24 * l.toNat < 2 ^ 64)
    (hFs : env.Frame (top + 18446744073709551520#64) (SpecExtendFormT.OutT R M) M m1)
    (hP : SEPost env R M r1 m1) (r10 : R .x10 = top + 18446744073709551528#64) (r11 : R .x11 = q)
    (r12 : R .x12 = q + (l <<< 4 + l <<< 3)) :
    Acc env m m1 (top + 18446744073709551528#64) (n + l.toNat) c ∧ env.Frame top Tactic.F m m1 ∧
      Slots m1 top ret regs := by
  have := hW.top_le
  have e88 : (top + 18446744073709551528#64).toNat = top.toNat - 88 :=
    Runtime.CloneT.toNat_add_neg (k := 88) rfl (by omega)
  have hcnt : SpecExtendFormT.cnt R = l.toNat := by
    unfold SpecExtendFormT.cnt
    rw [r12, r11, sh24 hb]
    omega
  unfold SEPost at hP
  obtain ⟨hA1, hF1, hk⟩ := acc_step hW hlim hA e88 r10 hcnt hroom hF hFs hP
  exact ⟨hA1, hF1, hsl.keep (by omega) hk⟩

/-- A slice's end does not wrap. -/
theorem slice_lt {m : MachineState} {top q l : Word} (hs : SliceFT env m top q l)
    (hE : env.heapEnd.toNat ≤ 0x78000000) : q.toNat + 24 * l.toNat < 2 ^ 64 := by
  rcases slice_end hs hE with h | h
  · omega
  · rw [h]; have := q.isLt; omega

set_option rv_sym.heap true in
/-- **The third slice**, from instruction 112: its `spec_extend`, then the return. -/
theorem at112 {p : Lprog (Op Reg) Reg} {i : Nat} {L : Link} (hp : p[i]? = some (tmpl L))
    (hL : L.WF p) {need needS : Nat} (hnS : 96 + needS ≤ need)
    (hse : HoldsT env p L.specExtend.idx needS (SEPre env) (SEPost env) SpecExtendFormT.OutT AbortStop)
    {Q : State rvIsa → Prop} {ret top : Word} {rest : List Frame} {regs : Reg → Word} {m : MachineState}
    (hk : ∀ r' m', HoldsT.post env (PostT env) SretVecOut ret top regs m r' m' →
      rvIsa.Total p stmtCtx (WinOk p) Q ⟨rest, r', m'⟩)
    (hstop : ∀ fr st r' m', AbortStop regs m r' m' → rvIsa.accept p stmtCtx ⟨fr :: st, r', m'⟩ →
      Q ⟨fr :: st, r', m'⟩)
    (hneed : env.stackLimit.toNat + need ≤ top.toNat) (hW : Windows env top m) (h16 : top.toNat % 16 = 0)
    (h2 : regs .x2 = top) (hpre : PreT env regs m) :
    ∀ R M, (R .x2 = top + 18446744073709551520#64 ∧ R .x8 = regs .x10 ∧ R .x9 = regs .x11 ∧
        R .x18 = m.getMem (regs .x11 + 40#64) ∧ Saved regs R) → Slots M top ret regs →
      env.Frame top Tactic.F m M → env.Static M → M.code = m.code →
      Acc env m M (top + 18446744073709551528#64)
        ((m.getMem (regs .x11 + 8#64)).toNat + (m.getMem (regs .x11 + 24#64)).toNat) (tot m (regs .x11)) →
      rvIsa.Total p stmtCtx (WinOk p) Q ⟨⟨i, 112, ret, top⟩ :: rest, R, M⟩ := by
  have hfin := fin hp hL hk hW h2 hpre (by omega) h16
  intro R M hR hsl hF hS hcd hA
  have hlim : env.stackLimit.toNat + 96 ≤ top.toNat := by omega
  have hs : True → SliceFT env m top (M.getMem (regs .x11 + 32#64)) (m.getMem (regs .x11 + 40#64)) := fun _ => by
    have := hpre.2.2.2.2.2.2.2.2
    rwa [h2, ← arr_keep (by omega) h2 hpre hF (k := 32) (by omega)] at this
  have hroom : (m.getMem (regs .x11 + 8#64)).toNat + (m.getMem (regs .x11 + 24#64)).toNat +
      (m.getMem (regs .x11 + 40#64)).toNat ≤ tot m (regs .x11) := by unfold tot; omega
  rv_introT hR
  rv_symT hp stop [128] with [hL] using [hse]
  · exact call_pre hW hlim hF hA (hs trivial) hroom rfl rfl rfl rfl
  · obtain ⟨hA1, hF1, hsl1⟩ := call_post hW hlim hsl hF hA hroom (slice_lt (hs trivial) hW.heapEnd_le) hret1_14
      hret1_16 rfl rfl rfl
    exact hfin _ _ ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ hsl1 hF1 hret1_15 (hret1_17.trans hcd) hA1

set_option rv_sym.heap true in
/-- **The second slice**, from instruction 96: its `spec_extend`, then the third slice. -/
theorem at96 {p : Lprog (Op Reg) Reg} {i : Nat} {L : Link} (hp : p[i]? = some (tmpl L))
    (hL : L.WF p) {need needS : Nat} (hnS : 96 + needS ≤ need)
    (hse : HoldsT env p L.specExtend.idx needS (SEPre env) (SEPost env) SpecExtendFormT.OutT AbortStop)
    {Q : State rvIsa → Prop} {ret top : Word} {rest : List Frame} {regs : Reg → Word} {m : MachineState}
    (hk : ∀ r' m', HoldsT.post env (PostT env) SretVecOut ret top regs m r' m' →
      rvIsa.Total p stmtCtx (WinOk p) Q ⟨rest, r', m'⟩)
    (hstop : ∀ fr st r' m', AbortStop regs m r' m' → rvIsa.accept p stmtCtx ⟨fr :: st, r', m'⟩ →
      Q ⟨fr :: st, r', m'⟩)
    (hneed : env.stackLimit.toNat + need ≤ top.toNat) (hW : Windows env top m) (h16 : top.toNat % 16 = 0)
    (h2 : regs .x2 = top) (hpre : PreT env regs m) :
    ∀ R M, (R .x2 = top + 18446744073709551520#64 ∧ R .x8 = regs .x10 ∧ R .x9 = regs .x11 ∧
        R .x19 = m.getMem (regs .x11 + 24#64) ∧ R .x18 = m.getMem (regs .x11 + 40#64) ∧ Saved regs R) →
      Slots M top ret regs → env.Frame top Tactic.F m M → env.Static M → M.code = m.code →
      Acc env m M (top + 18446744073709551528#64) (m.getMem (regs .x11 + 8#64)).toNat (tot m (regs .x11)) →
      rvIsa.Total p stmtCtx (WinOk p) Q ⟨⟨i, 96, ret, top⟩ :: rest, R, M⟩ := by
  have h112 := at112 hp hL hnS hse hk hstop hneed hW h16 h2 hpre
  intro R M hR hsl hF hS hcd hA
  have hlim : env.stackLimit.toNat + 96 ≤ top.toNat := by omega
  have hs : True → SliceFT env m top (M.getMem (regs .x11 + 16#64)) (m.getMem (regs .x11 + 24#64)) := fun _ => by
    have := hpre.2.2.2.2.2.2.2.1
    rwa [h2, ← arr_keep (by omega) h2 hpre hF (k := 16) (by omega)] at this
  have hroom : (m.getMem (regs .x11 + 8#64)).toNat + (m.getMem (regs .x11 + 24#64)).toNat ≤ tot m (regs .x11) := by
    unfold tot; omega
  rv_introT hR
  rv_symT hp stop [112] with [hL] using [hse]
  · exact call_pre hW hlim hF hA (hs trivial) hroom rfl rfl rfl rfl
  · obtain ⟨hA1, hF1, hsl1⟩ := call_post hW hlim hsl hF hA hroom (slice_lt (hs trivial) hW.heapEnd_le) hret1_14
      hret1_16 rfl rfl rfl
    exact h112 _ _ ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ hsl1 hF1 hret1_15 (hret1_17.trans hcd) hA1

set_option rv_sym.heap true in
/-- **From the join after `alloc`** (instruction 74): the header `(c, B, 0)` at `sp + 8`, the first slice's
    `spec_extend`, then the second slice. -/
theorem at74 {p : Lprog (Op Reg) Reg} {i : Nat} {L : Link} (hp : p[i]? = some (tmpl L))
    (hL : L.WF p) {need needS : Nat} (hnS : 96 + needS ≤ need)
    (hse : HoldsT env p L.specExtend.idx needS (SEPre env) (SEPost env) SpecExtendFormT.OutT AbortStop)
    {Q : State rvIsa → Prop} {ret top : Word} {rest : List Frame} {regs : Reg → Word} {m : MachineState}
    (hk : ∀ r' m', HoldsT.post env (PostT env) SretVecOut ret top regs m r' m' →
      rvIsa.Total p stmtCtx (WinOk p) Q ⟨rest, r', m'⟩)
    (hstop : ∀ fr st r' m', AbortStop regs m r' m' → rvIsa.accept p stmtCtx ⟨fr :: st, r', m'⟩ →
      Q ⟨fr :: st, r', m'⟩)
    (hneed : env.stackLimit.toNat + need ≤ top.toNat) (hW : Windows env top m) (h16 : top.toNat % 16 = 0)
    (h2 : regs .x2 = top) (hpre : PreT env regs m) :
    ∀ R M, (R .x2 = top + 18446744073709551520#64 ∧ R .x8 = regs .x10 ∧ R .x9 = regs .x11 ∧
        R .x20 = m.getMem (regs .x11 + 8#64) ∧ R .x19 = m.getMem (regs .x11 + 24#64) ∧
        R .x18 = m.getMem (regs .x11 + 40#64) ∧ Saved regs R) →
      Slots M top ret regs → env.Frame top Tactic.F m M → env.Static M → M.code = m.code →
      (R .x21).toNat = tot m (regs .x11) → (R .x21).toNat * 24 < 2 ^ 63 →
      ((R .x21).toNat = 0 ∨ (env.Fresh m M (R .x10) ((R .x21).toNat * 24) ∧ (R .x10).toNat % 8 = 0)) →
      rvIsa.Total p stmtCtx (WinOk p) Q ⟨⟨i, 74, ret, top⟩ :: rest, R, M⟩ := by
  have h96 := at96 hp hL hnS hse hk hstop hneed hW h16 h2 hpre
  intro R M hR hsl hF hS hcd hc hc63 hB
  have hlim : env.stackLimit.toNat + 96 ≤ top.toNat := by omega
  obtain ⟨hA0, hF0, hS0, hk0⟩ := hdr_ok hlim h16 hW hF hS hc63 hB
  have hsl0 := hsl.keep (by omega) hk0
  rw [hc] at hA0
  have hs : True → SliceFT env m top (M.getMem (regs .x11)) (m.getMem (regs .x11 + 8#64)) := fun _ => by
    have := hpre.2.2.2.2.2.2.1
    have hk := arr_keep (by omega) h2 hpre hF (k := 0) (by omega)
    rw [BitVec.add_zero] at hk
    rwa [h2, ← hk] at this
  have hroom : 0 + (m.getMem (regs .x11 + 8#64)).toNat ≤ tot m (regs .x11) := by unfold tot; omega
  have hc0 : (hdr M top (R .x21) (R .x10)).code = m.code := by simp only [hdr, MachineState.code_setMem]; exact hcd
  clear hk0 hsl hB hc hc63
  rv_introT hR
  rv_symT hp stop [96] with [hL] using [hse]
  · exact call_pre hW hlim hF0 hA0 (hs trivial) hroom rfl rfl rfl rfl
  · obtain ⟨hA1, hF1, hsl1⟩ := call_post hW hlim hsl0 hF0 hA0 hroom (slice_lt (hs trivial) hW.heapEnd_le) hret1_14
      hret1_16 rfl rfl rfl
    rw [Nat.zero_add] at hA1
    exact h96 _ _ ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ hsl1 hF1 hret1_15 (hret1_17.trans hc0) hA1

/-- The prologue's eight saved words over `m`. -/
def saved (m : MachineState) (top ret : Word) (regs : Reg → Word) : MachineState :=
  (((((((m.setMem (top + 18446744073709551608#64) ret).setMem (top + 18446744073709551600#64) (regs .x8)).setMem
    (top + 18446744073709551592#64) (regs .x9)).setMem (top + 18446744073709551584#64) (regs .x18)).setMem
    (top + 18446744073709551576#64) (regs .x19)).setMem (top + 18446744073709551568#64) (regs .x20)).setMem
    (top + 18446744073709551560#64) (regs .x21)).setMem (top + 18446744073709551552#64) (regs .x22)

/-- The prologue's stores: the slots, the frame, the static data, `NEXT` and the code. -/
theorem saved_ok {m : MachineState} {top ret : Word} {regs : Reg → Word}
    (hlim : env.stackLimit.toNat + 96 ≤ top.toNat) (hnx : (env.next m).toNat ≤ env.heapEnd.toNat)
    (hS : env.Static m) :
    Slots (saved m top ret regs) top ret regs ∧ env.Frame top Tactic.F m (saved m top ret regs) ∧
      env.Static (saved m top ret regs) ∧ (saved m top ret regs).code = m.code ∧
      env.next (saved m top ret regs) = env.next m := by
  have g : ∀ c : Word, ∀ k, c.toNat + k = 2 ^ 64 → k ≤ 96 → (top + c).toNat = top.toNat - k :=
    fun c k hc hk => Runtime.CloneT.toNat_add_neg hc (by omega)
  have e1 := g 18446744073709551608#64 8 rfl (by omega)
  have e2 := g 18446744073709551600#64 16 rfl (by omega)
  have e3 := g 18446744073709551592#64 24 rfl (by omega)
  have e4 := g 18446744073709551584#64 32 rfl (by omega)
  have e5 := g 18446744073709551576#64 40 rfl (by omega)
  have e6 := g 18446744073709551568#64 48 rfl (by omega)
  have e7 := g 18446744073709551560#64 56 rfl (by omega)
  have e8 := g 18446744073709551552#64 64 rfl (by omega)
  refine ⟨?_, ?_, ?_, by simp only [saved, MachineState.code_setMem], ?_⟩
  · simp only [saved, Slots]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      repeat (first | rw [MachineState.getMem_setMem_eq] | rw [MachineState.getMem_setMem_ne (fun h => by
        have h' := congrArg BitVec.toNat h
        simp only [e1, e2, e3, e4, e5, e6, e7, e8] at h'; omega)])
  · simp only [saved]
    repeat (first | refine Tactic.frame_slot ?_ (by omega) (by omega) | exact Env.Frame.refl hnx)
  · simp only [saved]
    repeat (first | refine Env.static_setMem_stack ?_ (by omega) | exact hS)
  · simp only [saved]
    repeat (first | rw [Env.next_setMem_stack (by omega)])

/-- **The lengths' sum**, as the code computes it: below `2 ^ 30`, the sum of the three. -/
theorem sum_ok {m : MachineState} {regs : Reg → Word} (hpre : PreT env regs m)
    (hE : env.heapEnd.toNat ≤ 0x78000000) :
    (m.getMem (regs .x11 + 40#64) + (m.getMem (regs .x11 + 24#64) + m.getMem (regs .x11 + 8#64))).toNat =
      tot m (regs .x11) ∧ tot m (regs .x11) < 2 ^ 30 := by
  obtain ⟨-, -, -, -, -, -, s0, s1, s2⟩ := hpre
  have b0 := slice_end s0 hE
  have b1 := slice_end s1 hE
  have b2 := slice_end s2 hE
  unfold tot
  simp only [BitVec.toNat_add]
  omega

/-- The block's size, as the code computes it: `24` times the sum, below `2 ^ 63`. -/
theorem sz24 {S : Word} (h : S ≤ 384307168202282325#64) :
    (S <<< 4 + S <<< 3).toNat = 24 * S.toNat ∧ 24 * S.toNat < 2 ^ 63 := by
  rw [BitVec.le_def] at h
  have : (384307168202282325#64).toNat = 384307168202282325 := rfl
  simp only [BitVec.toNat_add, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]
  omega

set_option rv_sym.heap true in
/-- **`<[&[Form]] as Concat<Form>>::concat` is total**, with 96 bytes of stack beyond its callees', given its
    bound's word in the static data. -/
theorem total (env : Env) (p : Lprog (Op Reg) Reg) (i : Nat) (L : Link) (hp : p[i]? = some (tmpl L)) (hL : L.WF p)
    (hd : DataRef.InData env [(L.d_c8_d6dfd6bc, d_c8_d6dfd6bc_words)])
    {need needA needS needH : Nat} (hnA : 96 + needA ≤ need) (hnS : 96 + needS ≤ need) (hnH : 96 + needH ≤ need)
    (hal : AllocSpecT env p L.alloc.idx needA) (hse : SpecExtendFormT.SpecT env p L.specExtend.idx needS)
    (hhe : Aborts env p L.handleError.idx needH) : SpecT env p i need := by
  have hal' : HoldsT env p L.alloc.idx needA AllocPre (AllocPost env) (Stop := AbortStop) :=
    hal.mono_stop fun _ _ _ _ _ h => h.1
  have hse' := se_spec hse
  have hw1 := hd.words (List.mem_cons_self ..)
  rv_autoT hp stop [74] with [hL, hw1] using [hal', hhe]
  all_goals try exact (Layout.CloneFormsT.data_ok hpre_18 hd (List.mem_cons_self ..) (by decide)).1
  all_goals try exact (Layout.CloneFormsT.data_ok hpre_18 hd (List.mem_cons_self ..) (by decide)).2
  all_goals
    have hpre : PreT env regs m :=
      ⟨⟨hpre_6, hpre_7⟩, hpre_8, hpre_9, ⟨hpre_10, hpre_11⟩, hpre_12, hpre_13, hpre_14, hpre_15, hpre_16⟩
    have hlim : env.stackLimit.toNat + 96 ≤ top.toNat := by omega
    obtain ⟨hsum, hlt⟩ := sum_ok hpre hpre_18.heapEnd_le
    obtain ⟨h24, h63⟩ := sz24 hc_1
    obtain ⟨hsl0, hF0, hS0, hc0, hn0⟩ := saved_ok (ret := ret) (regs := regs) hlim hpre_5 hpre_4
    simp only [saved] at hsl0 hF0 hS0 hc0 hn0
    have h74 := at74 hp hL hnS hse' hk hstop hpre_3 hpre_18 hpre_17 hpre_2 hpre
  · have h0 : tot m (regs .x11) = 0 := by
      have := congrArg BitVec.toNat hc
      rw [h24, hsum, BitVec.toNat_ofNat] at this
      omega
    refine h74 _ _ ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ hsl0 hF0 hS0 hc0 ?_ ?_ (.inl ?_)
    · simp only [Tactic.rf]; rw [h0]; rfl
    · simp only [Tactic.rf]; simp
    · simp only [Tactic.rf]; rfl
  · show (_ : Word).toNat < 2 ^ 63
    rw [h24]; omega
  · have e96 : (top + 18446744073709551520#64).toNat = top.toNat - 96 :=
      Runtime.CloneT.toNat_add_neg (k := 96) rfl (by omega)
    have hk1 := fun (x : Word) (l1 : top.toNat - 64 ≤ x.toNat) (_ : x.toNat < top.toNat) =>
      keep1_1 x (by rw [BitVec.le_def, e96]; omega)
    rw [h24] at hret1_18
    refine h74 _ _ ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ (hsl0.keep (by omega) hk1)
      (hF0.trans hret1_14 (by rw [e96]; omega) fun b hb => hb.elim) hret1_15 (hret1_19.trans hc0) ?_ ?_
      (.inr ⟨⟨?_, ?_⟩, ?_⟩)
    · simp only [Tactic.rf]; exact hsum
    · simp only [Tactic.rf]; omega
    · simp only [Tactic.rf]; omega
    · simp only [Tactic.rf]; omega
    · simp only [Tactic.rf]; exact hret1_17

end Rv64mc.Proof.Layout.ConcatFormT

/-- info: 'Rv64mc.Proof.Layout.ConcatFormT.total' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Rv64mc.Proof.Layout.ConcatFormT.total
