/-
  Rv64mc.Proof.Runtime.SpecExtendT

  `<Vec<E> as SpecExtend<&E, slice::Iter<E>>>::spec_extend` (`extend_from_slice`) is total: called with the
  vector's header (`a0`) and the source slice `[begin, end)` (`a1`, `a2`), it reserves `(end - begin) / 16` more
  elements (`Vec::reserve`, `ReserveT`), copies the source past the length when it is not empty (`memcpy`) and
  stores the new length. Its result is still a vector's (`VecReprT.VecT`), its length grown by the source's, its
  buffer the one at entry or fresh; the run ends with the guest's abort (`AbortStop`) where `reserve` does. It does
  not state the bytes copied.

  The precondition: the vector a vector's and a caller's object (`Owned`), its header apart from its buffer
  (`HdrApart`, which `RawVecT` does not give: a header on the stack has it from the windows, one in the heap from
  its caller), and the source whole 16-byte elements in a window apart from the stack below the stack pointer, from
  the heap not yet allocated and from the vector's buffer (`SrcT`), which `memcpy`'s `CopyPreT` needs whether or
  not `reserve` moved the buffer. A slice of a caller's stack, of the heap below `NEXT` or of the static data meets
  it.

  The executor does not read the frame's slots through `reserve`'s and `memcpy`'s frames (`out` the header, the
  copy's doublewords): `hk1` and `hk2` give them, and `room` the buffer's place after `reserve`, so that the rest is
  arithmetic in small lemmas, away from the context's disjunctions.

  ## Main definitions

  * `HdrApart`, `SrcT`, `PreT`, `PostT`, `OutT`, `SpecT`

  ## Main results

  * `total`
  * `HdrApart.of_stack`: a header in the stack window has it
-/

import Rv64mc.Proof.Runtime.ReserveT
import Rv64mc.Proof.Runtime.MemcpyT
import Rv64mc.Proof.Runtime.CloneT
import Rv64mc.Gen.Tmpl.Alloc.Vec.SpecExtend.VecE.AsSpecExtendRefEIterE.SpecExtend
import Rv64mc.Tactic.SymT

namespace Rv64mc.Proof.Runtime.SpecExtendT

open RiscvZkvm.Rv64 Lprog Lprog.RiscV Rv64mc.Spec.Runtime
open Rv64mc.Proof.Runtime.MemsetT (InWin)
open Rv64mc.Proof.Runtime.VecReprT (BufT RawVecT VecT)
open Rv64mc.Proof.Runtime.MemcpyT (MemcpySpecT)
open Rv64mc.Proof.Runtime.ReserveT (ReserveSpecT)
open Rv64mc.Gen.Alloc.Vec.SpecExtend.VecE.AsSpecExtendRefEIterE.SpecExtend (Link tmpl)

/-- The vector's header at `a` apart from its buffer, unless the buffer is empty. -/
def HdrApart (m : MachineState) (a : Word) (size : Nat) : Prop :=
  (vecCap m a).toNat = 0 ∨ a.toNat + 24 ≤ (vecPtr m a).toNat ∨
    (vecPtr m a).toNat + (vecCap m a).toNat * size ≤ a.toNat

/-- A header in the stack window is apart from its buffer, which is empty or below `NEXT`. -/
theorem HdrApart.of_stack {env : Env} {m : MachineState} {a : Word} (h : RawVecT env m a 16)
    (hnx : (env.next m).toNat ≤ env.heapEnd.toNat) (ha : env.stackLimit.toNat ≤ a.toNat) : HdrApart m a 16 := by
  have hlay := env.layout
  obtain ⟨-, -, hb, -⟩ := h
  simp only [rvCapAt, rvPtrAt, Layouts.RawVecInner.cap, Layouts.RawVecInner.ptr] at hb
  unfold HdrApart vecCap vecPtr
  simp only [Layouts.Vec.cap, Layouts.Vec.ptr]
  rcases hb with hb | ⟨-, hb, -⟩
  · exact .inl hb
  · unfold Env.Live at hb
    exact .inr (.inr (by omega))

/-- The source `[b, e)` of `n` bytes: unless empty, in a window, apart from the stack below `sp`, from the heap not
    yet allocated and from the vector's buffer at `a`. -/
def SrcT (env : Env) (m : MachineState) (sp a b : Word) (n : Nat) : Prop :=
  n = 0 ∨ (inWindow b n = true ∧ OffStack env sp b n ∧
    (b.toNat + n ≤ (env.next m).toNat ∨ env.heapEnd.toNat ≤ b.toNat) ∧
    ((vecCap m a).toNat = 0 ∨ b.toNat + n ≤ (vecPtr m a).toNat ∨
      (vecPtr m a).toNat + (vecCap m a).toNat * 16 ≤ b.toNat))

/-- `spec_extend`'s total precondition: the vector a vector's, a caller's object, its header apart from its buffer;
    the source `[a1, a2)` whole elements, `SrcT`. -/
def PreT (env : Env) (regs : Reg → Word) (m : MachineState) : Prop :=
  VecT env m (regs .x10) 16 ∧ env.Owned m (regs .x2) (regs .x10) Layouts.Vec.byteSize ∧
    HdrApart m (regs .x10) 16 ∧ (regs .x11).toNat ≤ (regs .x12).toNat ∧
    ((regs .x12).toNat - (regs .x11).toNat) % 16 = 0 ∧
    SrcT env m (regs .x2) (regs .x10) (regs .x11) ((regs .x12).toNat - (regs .x11).toNat)

/-- `spec_extend`'s total postcondition: still a vector, its length grown by the source's elements, its buffer
    the one at entry or fresh. -/
def PostT (env : Env) (regs : Reg → Word) (m : MachineState) (_r' : Reg → Word) (m' : MachineState) : Prop :=
  VecT env m' (regs .x10) 16 ∧
    (vecLen m' (regs .x10)).toNat = (vecLen m (regs .x10)).toNat + ((regs .x12).toNat - (regs .x11).toNat) / 16 ∧
    ((vecCap m' (regs .x10) = vecCap m (regs .x10) ∧ vecPtr m' (regs .x10) = vecPtr m (regs .x10)) ∨
      env.Fresh m m' (vecPtr m' (regs .x10)) ((vecCap m' (regs .x10)).toNat * 16))

/-- What `spec_extend` writes besides its stack and what it allocates: the header and the buffer at entry. -/
def OutT (regs : Reg → Word) (m : MachineState) (b : Word) : Prop :=
  InRange (regs .x10) Layouts.Vec.byteSize b ∨
    InRange (vecPtr m (regs .x10)) ((vecCap m (regs .x10)).toNat * 16) b

/-- **The total contract of `Vec<E>::spec_extend` from a slice.** -/
def SpecT (env : Env) (p : Lprog (Op Reg) Reg) (i need : Nat) : Prop :=
  HoldsT env p i need (PreT env) (PostT env) OutT AbortStop

/-- The prologue's six saved words over `m`. -/
def saved (m : MachineState) (top ret : Word) (regs : Reg → Word) : MachineState :=
  (((((m.setMem (top + 18446744073709551608#64) ret).setMem (top + 18446744073709551600#64) (regs .x8)).setMem
    (top + 18446744073709551592#64) (regs .x9)).setMem (top + 18446744073709551584#64) (regs .x18)).setMem
    (top + 18446744073709551576#64) (regs .x19)).setMem (top + 18446744073709551568#64) (regs .x20)

/-- A word off the frame is the entry's after the prologue. -/
theorem saved_get {m : MachineState} {top ret b : Word} {regs : Reg → Word} (h48 : 48 ≤ top.toNat)
    (hb : b.toNat + 8 ≤ top.toNat - 48 ∨ top.toNat ≤ b.toNat) : (saved m top ret regs).getMem b = m.getMem b := by
  have hne : ∀ c : Word, ∀ k, c.toNat + k = 2 ^ 64 → k ≤ 48 → b ≠ top + c := fun c k hc hk he => by
    have := congrArg BitVec.toNat he
    rw [CloneT.toNat_add_neg hc (by omega)] at this
    omega
  simp only [saved]
  rw [MachineState.getMem_setMem_ne (hne _ 48 rfl le_rfl), MachineState.getMem_setMem_ne (hne _ 40 rfl (by omega)),
    MachineState.getMem_setMem_ne (hne _ 32 rfl (by omega)), MachineState.getMem_setMem_ne (hne _ 24 rfl (by omega)),
    MachineState.getMem_setMem_ne (hne _ 16 rfl (by omega)), MachineState.getMem_setMem_ne (hne _ 8 rfl (by omega))]

/-- `NEXT` after the prologue. -/
theorem saved_next {env : Env} {m : MachineState} {top ret : Word} {regs : Reg → Word}
    (hlim : env.stackLimit.toNat + 48 ≤ top.toNat) : env.next (saved m top ret regs) = env.next m := by
  have h : ∀ c : Word, ∀ k, c.toNat + k = 2 ^ 64 → k ≤ 48 → env.stackLimit.toNat ≤ (top + c).toNat :=
    fun c k hc hk => by rw [CloneT.toNat_add_neg hc (by omega)]; omega
  simp only [saved]
  rw [Env.next_setMem_stack (h _ 48 rfl le_rfl), Env.next_setMem_stack (h _ 40 rfl (by omega)),
    Env.next_setMem_stack (h _ 32 rfl (by omega)), Env.next_setMem_stack (h _ 24 rfl (by omega)),
    Env.next_setMem_stack (h _ 16 rfl (by omega)), Env.next_setMem_stack (h _ 8 rfl (by omega))]

/-- A slot of the frame, as a word and a number. -/
theorem slot_bounds {env : Env} {top c : Word} (hlim : env.stackLimit.toNat + 48 ≤ top.toNat)
    (hc : 0xffffffffffffffd0#64 ≤ c) :
    top + 0xffffffffffffffd0#64 ≤ top + c ∧ env.stackLimit.toNat ≤ (top + c).toNat ∧ (top + c).toNat < top.toNat := by
  have h48 : (0xffffffffffffffd0#64 : Word).toNat = 2 ^ 64 - 48 := rfl
  have hc' : 2 ^ 64 - 48 ≤ c.toNat := by rw [BitVec.le_def, h48] at hc; exact hc
  have hlt := c.isLt
  have e1 : (top + 0xffffffffffffffd0#64).toNat = top.toNat - 48 :=
    CloneT.toNat_add_neg (k := 48) (by rw [h48]; rfl) (by omega)
  have e2 : (top + c).toNat = top.toNat - (2 ^ 64 - c.toNat) := CloneT.toNat_add_neg (by omega) (by omega)
  rw [BitVec.le_def, e1, e2]
  omega

/-- The buffer after `reserve` with `k > 0` elements asked for: room for them past the length, in the input and
    heap window below `NEXT`, apart from the header and from the source. -/
theorem room {C0 P0 L0 C1 P1 L1 N0 N1 A S n k T H : Nat} (hk : 0 < k) (hl : L1 = L0)
    (hkeep : k ≤ C0 - L0 → C1 = C0 ∧ P1 = P0)
    (hgrow : ¬ k ≤ C0 - L0 → L0 + k ≤ C1 ∧ N0 ≤ P1 ∧ P1 + C1 * 16 ≤ N1)
    (hb1 : C1 = 0 ∨ (0x10000000 ≤ P1 ∧ P1 + C1 * 16 ≤ N1))
    (hhdr : C0 = 0 ∨ A + 24 ≤ P0 ∨ P0 + C0 * 16 ≤ A) (hown : A + 24 ≤ N0 ∨ T ≤ A)
    (hsrc : S + n ≤ N0 ∨ H ≤ S) (hsrc2 : C0 = 0 ∨ S + n ≤ P0 ∨ P0 + C0 * 16 ≤ S) (hN1 : N1 ≤ H) (hHT : H < T) :
    L1 + k ≤ C1 ∧ 0x10000000 ≤ P1 ∧ P1 + C1 * 16 ≤ N1 ∧ (A + 24 ≤ P1 ∨ P1 + C1 * 16 ≤ A) ∧
      (S + n ≤ P1 ∨ P1 + C1 * 16 ≤ S) ∧ (N0 ≤ P1 ∨ (C1 = C0 ∧ P1 = P0)) := by
  by_cases h : k ≤ C0 - L0
  · obtain ⟨h1, h2⟩ := hkeep h
    subst h1 h2 hl
    omega
  · have := hgrow h
    omega

/-- `reserve`'s `out` is in the header. -/
theorem grow_in {R : Reg → Word} {M : MachineState} {a b : Word} (hx : R .x10 = a) (hv : a.toNat + 24 < 2 ^ 64)
    (h : GrowOut R M b) : InRange a 24 b := by
  unfold GrowOut rvCapAt rvPtrAt at h
  simp only [Layouts.RawVecInner.cap, Layouts.RawVecInner.ptr] at h
  rw [hx] at h
  rcases h with h | h <;> subst h <;> unfold InRange <;> rw [toNat_add_ofNat (by omega)] <;> omega

/-- The prologue's stores stay in the frame. -/
theorem saved_frame {env : Env} {m : MachineState} {top ret : Word} {regs : Reg → Word}
    (hlim : env.stackLimit.toNat + 48 ≤ top.toNat) (hnx : (env.next m).toNat ≤ env.heapEnd.toNat) :
    env.Frame top Tactic.F m (saved m top ret regs) := by
  have h : ∀ c : Word, 0xffffffffffffffd0#64 ≤ c →
      env.stackLimit.toNat ≤ (top + c).toNat ∧ (top + c).toNat < top.toNat :=
    fun c hc => (slot_bounds hlim hc).2
  simp only [saved]
  refine Tactic.frame_store (Tactic.frame_store (Tactic.frame_store (Tactic.frame_store (Tactic.frame_store
    (Tactic.frame_store (Tactic.frame_refl hnx) ?_ ?_) ?_ ?_) ?_ ?_) ?_ ?_) ?_ ?_) ?_ ?_
  all_goals first | exact (h _ (by decide)).1 | exact (h _ (by decide)).2

/-- A slot of the frame is not in `reserve`'s `out`, the header of a caller's object. -/
theorem not_grow {env : Env} {R : Reg → Word} {M : MachineState} {a b top : Word} {N : Nat} (hx : R .x10 = a)
    (hv : a.toNat + 24 < 2 ^ 64) (hown : a.toNat + 24 ≤ N ∨ top.toNat ≤ a.toNat) (hN : N ≤ env.heapEnd.toNat)
    (hlo : env.stackLimit.toNat ≤ b.toNat) (hhi : b.toNat < top.toNat) : ¬ GrowOut R M b := by
  intro hg
  have hin := grow_in hx hv hg
  have := env.layout
  unfold InRange at hin
  omega

/-- The length stored into a vector whose header words are kept from one that was a vector's. -/
theorem vecT_setLen {env : Env} {m m' : MachineState} {a v : Word} (hw : InWin env a 24) (hr : RawVecT env m a 16)
    (hc : m'.getMem a = m.getMem a) (hp : m'.getMem (a + 8#64) = m.getMem (a + 8#64))
    (hn : (env.next m).toNat ≤ (env.next m').toNat) (hv : v.toNat ≤ (m.getMem a).toNat) :
    VecT env (m'.setMem (a + 16#64) v) a 16 ∧ vecLen (m'.setMem (a + 16#64) v) a = v ∧
      vecCap (m'.setMem (a + 16#64) v) a = m.getMem a ∧ vecPtr (m'.setMem (a + 16#64) v) a = m.getMem (a + 8#64) := by
  have hlt := hw.lt
  have h16 : (a + 16#64).toNat = a.toNat + 16 := toNat_add_ofNat (by omega)
  have h8 : (a + 8#64).toNat = a.toNat + 8 := toNat_add_ofNat (by omega)
  have ne0 : a ≠ a + 16#64 := fun he => by have := congrArg BitVec.toNat he; omega
  have ne8 : a + 8#64 ≠ a + 16#64 := fun he => by have := congrArg BitVec.toNat he; omega
  have hnx : env.next (m'.setMem (a + 16#64) v) = env.next m' :=
    Tactic.next_setMem (MemsetT.InWin.ne_next_add (o := 16) hw (by decide))
  have hcap : (m'.setMem (a + 16#64) v).getMem (rvCapAt a) = m.getMem (rvCapAt a) := by
    simp only [rvCapAt, Layouts.RawVecInner.cap, BitVec.add_zero]
    rw [MachineState.getMem_setMem_ne ne0, hc]
  have hptr : (m'.setMem (a + 16#64) v).getMem (rvPtrAt a) = m.getMem (rvPtrAt a) := by
    show (m'.setMem (a + 16#64) v).getMem (a + 8#64) = m.getMem (a + 8#64)
    rw [MachineState.getMem_setMem_ne ne8, hp]
  have hlen : vecLen (m'.setMem (a + 16#64) v) a = v := by
    rw [ReserveT.vecLen_eq, MachineState.getMem_setMem_eq]
  have hc0 : rvCapAt a = a := by simp [rvCapAt, Layouts.RawVecInner.cap]
  refine ⟨⟨hw, hr.keep hcap hptr (by rw [hnx]; exact hn), ?_⟩, hlen, ?_, hptr⟩
  · rw [hlen, ReserveT.vecCap_eq]
    rw [hc0] at hcap
    rw [hcap]
    exact hv
  · rw [hc0] at hcap
    rw [ReserveT.vecCap_eq, hcap]

/-- A word `memcpy` may write, into a destination at an aligned offset of a buffer. -/
theorem dwords_in {dst b : Word} {P L n : Nat} (hal : P % 8 = 0) (hD : dst.toNat = P + 16 * L)
    (hb : DwordsOf dst n b) : P + 16 * L ≤ b.toNat ∧ b.toNat < P + 16 * L + n := by
  unfold DwordsOf InRange at hb
  rw [toNat_alignToDword, hD] at hb
  omega

/-- The destination `dst = P + 16 L` of the copy, with `n = 16 k` bytes, inside the buffer. -/
theorem dst_ok {dst : Word} {P C L N H n k : Nat} (hD : dst.toNat = P + 16 * L) (h1 : L + k ≤ C)
    (h3 : P + C * 16 ≤ N) (hN : N ≤ H) (hk : k = n / 16) (hn : n % 16 = 0) :
    dst.toNat + n ≤ P + C * 16 ∧ dst.toNat + n ≤ H := by
  omega

/-- A word `memcpy` may write is in the buffer: fresh since `N0`, or the buffer at entry. -/
theorem copy_out_ok {b : Nat} {P C L n N0 N1 C0 P0 : Nat} (hb : P + 16 * L ≤ b ∧ b < P + 16 * L + n)
    (hroom : P + 16 * L + n ≤ P + C * 16) (h6 : N0 ≤ P ∨ (C = C0 ∧ P = P0)) (h3 : P + C * 16 ≤ N1) :
    (N0 ≤ b ∧ b < N1) ∨ (P0 ≤ b ∧ b < P0 + C0 * 16) := by
  omega

/-- The source's bytes do not wrap. -/
theorem src_nowrap {S : Word} {n : Nat} (h : inWindow S n = true) : S.toNat + n < 2 ^ 64 := by
  rcases inWindow_iff.1 h with h | h <;> omega

/-- The copy's ranges apart. -/
theorem disj {D S P C n b : Nat} (h1 : D ≤ b ∧ b < D + n) (h2 : S ≤ b ∧ b < S + n) (hP : P ≤ D)
    (hr : D + n ≤ P + C * 16) (h5 : S + n ≤ P ∨ P + C * 16 ≤ S) : False := by
  omega

/-- A word the copy may write is not a slot of the stack. -/
theorem not_slot {D n s H SL : Nat} (h : D ≤ s ∧ s < D + n) (hd : D + n ≤ H) (hHS : H ≤ SL) (hs : SL ≤ s) :
    False := by
  omega

/-- A word the copy may write is not one of the header's. -/
theorem not_hdr {A j D n P C : Nat} (h : D ≤ A + j ∧ A + j < D + n) (hP : P ≤ D) (hr : D + n ≤ P + C * 16)
    (h4 : A + 24 ≤ P ∨ P + C * 16 ≤ A) (hj : j < 24) : False := by
  omega

/-- A header word is below `NEXT` or in a caller's frame. -/
theorem hdr_word {A j N0 N1 T : Nat} (hown : A + 24 ≤ N0 ∨ T ≤ A) (hN : N0 ≤ N1) (hj : j < 24) :
    A + j < N1 ∨ T - 48 ≤ A + j := by
  omega

/-- A sum of two words below `2^64` as numbers. -/
theorem add_toNat {x y : Word} {C : Nat} (h : x.toNat + y.toNat ≤ C) (hC : C < 2 ^ 64) :
    (x + y).toNat = x.toNat + y.toNat := by
  rw [BitVec.toNat_add]; omega

/-- A vector's pointer, as the code reads it. -/
theorem vecPtr_eq (m : MachineState) (a : Word) : vecPtr m a = m.getMem (a + 8#64) := rfl

/-- A shift right by four, as a division. -/
theorem ushr4_toNat (w : Word) : (w >>> 4).toNat = w.toNat / 16 := by
  rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]

/-- A word below `NEXT` at entry, or at or above the stack top, is kept by a frame that writes nothing else. -/
theorem keep_of_frame {env : Env} {top : Word} {m M : MachineState} (hF : env.Frame top Tactic.F m M)
    (hlim : env.stackLimit.toNat ≤ top.toNat) :
    ∀ a : Word, (a.toNat + 8 ≤ (env.next m).toNat ∨ top.toNat ≤ a.toNat) → M.getMem a = m.getMem a :=
  fun a ha => hF.2.2 a fun hw => by
    have := env.layout
    have := hF.1
    have := hF.2.1
    rcases hw with hw | hw | hw | hw
    · omega
    · omega
    · rw [hw] at ha; omega
    · exact hw

/-- The header's `Owned` at the stack pointer, with the stack top for it. -/
theorem own_top {env : Env} {m : MachineState} {regs : Reg → Word} {top : Word} (h2 : regs .x2 = top)
    (h : env.Owned m (regs .x2) (regs .x10) Layouts.Vec.byteSize) :
    ((regs .x10).toNat + 24 ≤ (env.next m).toNat ∨ top.toNat ≤ (regs .x10).toNat) ∧
      (regs .x10).toNat + 24 < 2 ^ 64 := by
  subst h2; exact h

set_option maxHeartbeats 1000000 in
set_option rv_sym.heap true in
/-- **`spec_extend` is total**, with 48 bytes of stack beyond its callees'. -/
theorem total (env : Env) (p : Lprog (Op Reg) Reg) (i : Nat) (L : Link) (hp : p[i]? = some (tmpl L))
    (hL : L.WF p) {need needR needM : Nat} (hnR : 48 + needR ≤ need) (hnM : 48 + needM ≤ need)
    (hres : ReserveSpecT env 8 16 p L.reserve.idx needR) (hcp : MemcpySpecT env p L.memcpy.idx needM) :
    SpecT env p i need := by
  rv_autoT hp with [hL, own_top hpre_2 ⟨hpre_12, hpre_13⟩] using [hres, hcp]
  all_goals
    have hlay := env.layout
    have hlim : env.stackLimit.toNat + 48 ≤ top.toNat := by omega
    have hHS : env.heapEnd.toNat ≤ env.stackLimit.toNat := by omega
    have e48 : (top + 18446744073709551568#64).toNat = top.toNat - 48 := CloneT.toNat_add_neg rfl (by omega)
    have hnx0 := hpre_19.next_ge
    have hS : ∀ b : Word, (b.toNat + 8 ≤ top.toNat - 48 ∨ top.toNat ≤ b.toNat) →
        (saved m top ret regs).getMem b = m.getMem b := fun b hb => saved_get (by omega) hb
    have hSn : env.next (saved m top ret regs) = env.next m := saved_next hlim
    have hx0 : rvCapAt (regs .x10) = regs .x10 := by simp [rvCapAt, Layouts.RawVecInner.cap]
    have hx8 : (rvPtrAt (regs .x10)).toNat = (regs .x10).toNat + 8 := by
      simp only [rvPtrAt, Layouts.RawVecInner.ptr]; exact toNat_add_ofNat (by omega)
    have hx16 : (regs .x10 + 16#64).toNat = (regs .x10).toNat + 16 := toNat_add_ofNat (by omega)
    simp only [saved] at hS hSn
    have hcap := hS (rvCapAt (regs .x10)) (by rw [hx0]; omega)
    have hptr := hS (rvPtrAt (regs .x10)) (by rw [hx8]; omega)
  -- `reserve`'s precondition, read through the prologue's stores
  all_goals try
    try simp only [hcap, hptr, Env.Live, hSn]
    first
    | exact hpre_9
    | exact hpre_10
    | exact hpre_9.imp id fun h => h.2.1
    | (rwa [ReserveT.vecCap_eq, ReserveT.vecLen_eq] at hpre_11)
  -- after `reserve`: the frame's slots kept, the header's words as numbers
  all_goals
    have hown := hwith_1
    have hR10 : ∀ v : Word, (updReg (Tactic.rf (regs .x0) L.s0.hi (top + 18446744073709551568#64) (regs .x3)
        (regs .x4) (regs .x5) (regs .x6) (regs .x7) (regs .x10) ((regs .x12 - regs .x11) >>> 4) (regs .x10)
        ((regs .x12 - regs .x11) >>> 4) (regs .x12) (regs .x13) (regs .x14) (regs .x15) (regs .x16) (regs .x17)
        (regs .x12 - regs .x11) (regs .x12) (regs .x11) (regs .x21) (regs .x22) (regs .x23) (regs .x24) (regs .x25)
        (regs .x26) (regs .x27) (regs .x28) (regs .x29) (regs .x30) (regs .x31)) .x1 v) .x10 = regs .x10 :=
      fun _ => rfl
    have hk1 : ∀ c : Word, 0xffffffffffffffd0#64 ≤ c →
        m1.getMem (top + c) = (saved m top ret regs).getMem (top + c) := fun c hc => by
      obtain ⟨hle, hlo, hhi⟩ := slot_bounds hlim hc
      exact keep1_1 _ hle (not_grow (hR10 _) hwith_2 hown hpre_5 hlo hhi)
    simp only [saved] at hk1
    have hF1 : env.Frame top (OutT regs m) m m1 :=
      (Tactic.frame_weaken (saved_frame hlim hpre_5)).trans hret1_14 (slot_bounds hlim (BitVec.le_refl _)).2.2.le
        fun b hb => Or.inr (Or.inr (Or.inr (Or.inl (grow_in (hR10 _) hwith_2 hb))))
    have hr1 : RawVecT env m1 (regs .x10) 16 := ⟨hret1_20, hret1_21, hret1_22, hret1_23⟩
    have hA16 : InRange (regs .x10) 24 (regs .x10 + 16#64) := by unfold InRange; rw [hx16]; omega
    have hst16 := Env.Owned.not_static (m := m) (top := top) ⟨hwith_1, hwith_2⟩ hpre_5 (by omega) hA16
    have hnn16 : regs .x10 + 16#64 ≠ env.nextAddr :=
      Env.Owned.not_next (m := m) (top := top) ⟨hwith_1, hwith_2⟩ hpre_5 (by omega) hA16
    have hl0 : (saved m top ret regs).getMem (regs .x10 + 16#64) = m.getMem (regs .x10 + 16#64) :=
      saved_get (by omega) (by rw [hx16]; omega)
    simp only [saved] at hl0
    have hlen1 : (m1.getMem (regs .x10 + 16#64)).toNat = (m.getMem (regs .x10 + 16#64)).toNat := by
      rw [ReserveT.vecLen_eq, ReserveT.vecLen_eq, hl0] at hret1_16
      rw [hret1_16]
    have hle1 : (m1.getMem (regs .x10 + 16#64)).toNat ≤ (m1.getMem (regs .x10)).toNat := by
      rwa [ReserveT.vecLen_eq, ReserveT.vecCap_eq] at hret1_24
  -- `begin = end`: nothing to copy
  · show m1.getMem (top + 18446744073709551608#64) = ret
    rw [hk1 _ (by decide)]
    rv_closeT
  · have hz : (regs .x12 - regs .x11) >>> 4 = 0#64 := by rw [hc, BitVec.sub_self]; rfl
    rw [hz, BitVec.add_zero]
    obtain ⟨hv, hl, hvc, hvp⟩ := vecT_setLen hpre_6 hr1 rfl rfl (Nat.le_refl _) hle1
    have hsame := hret1_17 (by rw [hz]; exact Nat.zero_le _)
    rw [ReserveT.vecCap_eq, ReserveT.vecCap_eq, vecPtr_eq, vecPtr_eq] at hsame
    refine ⟨?_, hF1.trans (Env.Frame.setMem_out hret1_14.2.1 (Or.inl hA16) hnn16) (Nat.le_refl _)
      fun b h => Or.inr (Or.inr (Or.inr h)), Env.static_setMem hret1_15 hst16, hv, ?_, Or.inl ⟨?_, ?_⟩⟩
    · refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ <;>
        (show m1.getMem _ = _
         rw [hk1 _ (by decide)]
         rv_closeT)
    · rw [hl, hlen1, ReserveT.vecLen_eq, hc, Nat.sub_self, Nat.zero_div, Nat.add_zero]
    · rw [hvc, hsame.1, ReserveT.vecCap_eq, ← hx0, hcap]
    · rw [hvp, hsame.2, vecPtr_eq]
      exact hptr
  -- `begin < end`: the copy into the buffer's spare room
  all_goals
    have hn : (regs .x12 - regs .x11).toNat = (regs .x12).toNat - (regs .x11).toNat :=
      BitVec.toNat_sub_of_le (BitVec.le_def.2 hpre_15)
    have hn0 : (regs .x12).toNat - (regs .x11).toNat ≠ 0 := fun h => hc (BitVec.eq_of_toNat_eq (by omega))
    have hk : ((regs .x12 - regs .x11) >>> 4).toNat = ((regs .x12).toNat - (regs .x11).toNat) / 16 := by
      rw [ushr4_toNat, hn]
    obtain ⟨hsw, hsoff, hsrc, hsrc2⟩ := hpre_17.resolve_left hn0
    simp only [rvCapAt, rvPtrAt, Layouts.RawVecInner.cap, Layouts.RawVecInner.ptr, BitVec.add_zero, Grown,
      Env.Fresh] at hcap hptr hret1_18 hret1_22
    simp only [ReserveT.vecCap_eq, ReserveT.vecLen_eq, vecPtr_eq, hcap, hptr, hl0, hSn] at hret1_17 hret1_18
    simp only [ReserveT.vecCap_eq, vecPtr_eq] at hpre_14 hsrc2
    have hHT : env.heapEnd.toNat < top.toNat := by omega
    have hkpos : 0 < ((regs .x12 - regs .x11) >>> 4).toNat := by rw [hk]; omega
    have key := room (k := ((regs .x12 - regs .x11) >>> 4).toNat) (n := (regs .x12).toNat - (regs .x11).toNat)
      hkpos hlen1
      (fun h => ⟨congrArg BitVec.toNat (hret1_17 h).1, congrArg BitVec.toNat (hret1_17 h).2⟩)
      (fun h => ⟨(hret1_18 h).1, (hret1_18 h).2.1.1, (hret1_18 h).2.1.2⟩)
      (hret1_22.imp id fun h => ⟨h.1, h.2.1⟩) hpre_14 hwith_1 hsrc hsrc2 hret1_14.2.1 hHT
    obtain ⟨key1, key2, key3, key4, key5, key6⟩ := key
    have hHe := env.heapEnd.isLt
    have hP16 : (m1.getMem (regs .x10 + 8#64)).toNat + 2 ^ 4 * (m1.getMem (regs .x10 + 16#64)).toNat < 2 ^ 64 := by
      clear hpre_6 hpre_7 hpre_9 hpre_12 hpre_14 hpre_17 hret1_19 hret1_20 hret1_22 hsrc hsrc2 hwith_1 key4 key5 key6
      omega
    have hD : (m1.getMem (regs .x10 + 8#64) + m1.getMem (regs .x10 + 16#64) <<< 4).toNat =
        (m1.getMem (regs .x10 + 8#64)).toNat + 16 * (m1.getMem (regs .x10 + 16#64)).toNat :=
      WinT.elem_toNat hP16
    have hdst := dst_ok hD key1 key3 hret1_14.2.1 hk hpre_16
    have hal1 : (m1.getMem (regs .x10 + 8#64)).toNat % 8 = 0 :=
      (hret1_22.resolve_left fun h => by rw [h] at key1; exact absurd key1 (by omega)).2.2
    have hPD : (m1.getMem (regs .x10 + 8#64)).toNat ≤
        (m1.getMem (regs .x10 + 8#64) + m1.getMem (regs .x10 + 16#64) <<< 4).toNat := by
      rw [hD]; exact Nat.le_add_right _ _
  -- `memcpy(dst, begin, end - begin)`'s precondition
  · rw [hn]; exact Nat.lt_of_le_of_lt hdst.2 hHe
  · rw [hn]; exact src_nowrap hsw
  · intro _ b h1 h2
    rw [hn] at h1 h2
    exact disj h1 h2 hPD hdst.1 key5
  · refine Or.inr ⟨Or.inl ⟨Nat.le_trans key2 hPD, by rw [hn]; exact hdst.2⟩,
      Or.inl (by rw [hn]; exact Nat.le_trans hdst.2 hHS), by rw [hn]; exact hsw, ?_⟩
    unfold OffStack at hsoff ⊢
    rw [hpre_2] at hsoff
    rw [hn, e48]
    exact hsoff.imp id fun h => Nat.le_trans (Nat.sub_le _ _) h
  -- after `memcpy`: the frame's slots and the header kept
  all_goals
    have hdstD : (m1.getMem (regs .x10 + 8#64)).toNat + 16 * (m1.getMem (regs .x10 + 16#64)).toNat +
          (regs .x12 - regs .x11).toNat ≤
        (m1.getMem (regs .x10 + 8#64)).toNat + (m1.getMem (regs .x10)).toNat * 16 ∧
        (m1.getMem (regs .x10 + 8#64)).toNat + 16 * (m1.getMem (regs .x10 + 16#64)).toNat +
          (regs .x12 - regs .x11).toNat ≤ env.heapEnd.toNat := by
      rw [hn, ← hD]; exact hdst
    have hk2 : ∀ c : Word, 0xffffffffffffffd0#64 ≤ c → m2.getMem (top + c) = m1.getMem (top + c) := fun c hc => by
      obtain ⟨hle, hlo, hhi⟩ := slot_bounds hlim hc
      exact keep2_1 _ hle fun hb =>
        not_slot (dwords_in (n := (regs .x12 - regs .x11).toNat) hal1 hD hb) hdstD.2 hHS hlo
  · show m2.getMem (top + 18446744073709551608#64) = ret
    rw [hk2 _ (by decide), hk1 _ (by decide)]
    rv_closeT
  · have hN01 : (env.next m).toNat ≤ (env.next m1).toNat := by have := hret1_14.1; rwa [hSn] at this
    have hkeep : ∀ j : Nat, j < 24 → j % 8 = 0 →
        m2.getMem (regs .x10 + BitVec.ofNat 64 j) = m1.getMem (regs .x10 + BitVec.ofNat 64 j) := fun j hj _ => by
      have hj' : (regs .x10 + BitVec.ofNat 64 j).toNat = (regs .x10).toNat + j := toNat_add_ofNat (by omega)
      refine keep2_2 _ ?_ fun hb => ?_
      · rw [hj', e48]; exact hdr_word hwith_1 hN01 hj
      · have := dwords_in (n := (regs .x12 - regs .x11).toNat) hal1 hD hb
        rw [hj'] at this
        exact not_hdr this (by rw [← hD]; exact hPD) hdstD.1 key4 hj
    have hc2 : m2.getMem (regs .x10) = m1.getMem (regs .x10) := by
      simpa using hkeep 0 (by decide) rfl
    have hval : (m1.getMem (regs .x10 + 16#64) + (regs .x12 - regs .x11) >>> 4).toNat =
        (m1.getMem (regs .x10 + 16#64)).toNat + ((regs .x12 - regs .x11) >>> 4).toNat :=
      add_toNat key1 (BitVec.isLt _)
    obtain ⟨hv, hl, hvc, hvp⟩ :=
      vecT_setLen hpre_6 hr1 hc2 (hkeep 8 (by decide) rfl) hret2_14.1 (by rw [hval]; exact key1)
    refine ⟨?_, (hF1.trans hret2_14 (slot_bounds hlim (BitVec.le_refl _)).2.2.le fun b hb => ?_).trans
      (Env.Frame.setMem_out hret2_14.2.1 (Or.inl hA16) hnn16) (Nat.le_refl _)
      fun b h => Or.inr (Or.inr (Or.inr h)), Env.static_setMem hret2_15 hst16, hv, ?_, ?_⟩
    · refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ <;>
        (show m2.getMem _ = _
         rw [hk2 _ (by decide), hk1 _ (by decide)]
         rv_closeT)
    · have hin := dwords_in (n := (regs .x12 - regs .x11).toNat) hal1 hD hb
      rcases copy_out_ok hin hdstD.1 key6 key3 with h | h
      · exact Or.inr (Or.inl ⟨h.1, Nat.lt_of_lt_of_le h.2 hret2_14.1⟩)
      · refine Or.inr (Or.inr (Or.inr (Or.inr ?_)))
        unfold InRange
        rw [vecPtr_eq, ReserveT.vecCap_eq]
        exact h
    · rw [hl, hval, hlen1, hk, ReserveT.vecLen_eq]
    · rw [hvc, hvp, ReserveT.vecCap_eq, vecPtr_eq]
      by_cases hg : ((regs .x12 - regs .x11) >>> 4).toNat ≤
          (m.getMem (regs .x10)).toNat - (m.getMem (regs .x10 + 16#64)).toNat
      · exact Or.inl (hret1_17 hg)
      · refine Or.inr ⟨(hret1_18 hg).2.1.1, ?_⟩
        rw [Tactic.next_setMem hnn16]
        exact Nat.le_trans (hret1_18 hg).2.1.2 hret2_14.1

end Rv64mc.Proof.Runtime.SpecExtendT

/-- info: 'Rv64mc.Proof.Runtime.SpecExtendT.total' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Rv64mc.Proof.Runtime.SpecExtendT.total
