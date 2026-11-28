module

public import NativeRustcVmArm.KeccakGkr.KeccakOpen.Defs
public import NativeRustcVm.Transcript.Update

/-!
# `keccak_open`: the state around the fold

After `slot_weights` (`Mid`): the body, the frame's words (the value at `16`, the result's address
at `32`, the slot point's at `40`, the rows' at `48`), the slot point, the `TState`. Kept by a
change in `Safe` bytes (`Mid.keep`). The rows' contents (`ElemsAt` of `4096` elements) and the
two row buffers at the frame's `80` and `1104` are tracked beside it.
-/

namespace NativeRustcVmArm.KeccakGkr.KeccakOpen

open NativeRustcArm NativeRustcArm.Sym NativeVm.Model NativeRustcVmArm.Arrays
open LeanVM.Parameters LeanVM.Protocol.Verifier
open NativeRustcVm (Region InAny)
open NativeRustcVm.Transcript (DecArea tstateBytes TStateAt)
open NativeRustcVm.KeccakGkr (rowsBytes weightsBytes)

@[expose] public section

/-- What the fold works with: the decoded area, the `TState` after the sumcheck, the slot point,
the sumcheck's value. -/
structure Cx where
  a : DecArea
  s1 : TState
  sl : Array EW
  v : EW

/-- **The state around the fold.** -/
structure Mid [Labels] (c : Cx) (m0 st : MachineData) : Prop where
  body : Body m0 st
  v0 : NativeRustcVm.WordAt st.dmem (fbA m0 + BitVec.ofNat 64 16) c.v.c0
  v1 : NativeRustcVm.WordAt st.dmem (fbA m0 + BitVec.ofNat 64 24) c.v.c1
  out : NativeRustcVm.WordAt st.dmem (fbA m0 + BitVec.ofNat 64 32) m0.regs.X0
  sw : NativeRustcVm.WordAt st.dmem (fbA m0 + BitVec.ofNat 64 40) (UInt64.ofBitVec (slA m0))
  rw : NativeRustcVm.WordAt st.dmem (fbA m0 + BitVec.ofNat 64 48) (UInt64.ofBitVec (rwA m0))
  sl_size : c.sl.size = 6
  slot : NativeRustcVm.EWsAt st.dmem (slA m0) c.sl.toList
  ts : TStateAt st.dmem (tA m0) c.a c.s1

/-- The regions around the fold: the frame, the slot point, the rows. -/
def envR (m0 : MachineData) : List (BitVec 64 × Nat) :=
  [(fbA m0, 2224), (slA m0, 96), (rwA m0, 65536)]

/-- The variables of round `t` at row `i`: the challenge's limbs, `i`, `1024 i`. -/
def varsOf (sl : Array EW) (t i : Nat) : Nat → BitVec 64
  | 0 => (sl.getD t 0).c0.toBitVec
  | 1 => (sl.getD t 0).c1.toBitVec
  | 2 => BitVec.ofNat 64 i
  | 3 => BitVec.ofNat 64 (1024 * i)
  | _ => 0

/-- What the precondition gives every step: the numbers, the stack, the slot point and the rows
data memory. -/
structure Ok [Labels] (a : DecArea) (m0 : MachineData) : Prop where
  nums : Nums a m0
  stack : StackOk m0 keccakOpenStack
  slotM : Mapped m0.dmem (slA m0) 96
  rowsM : Mapped m0.dmem (rwA m0) 65536
  wsOff : WsOff m0 keccakOpenStack (wsOf m0)

end

public section

variable {c : Cx} {m0 st st' : MachineData}

/-- A byte of the frame's words is not `Safe`. -/
theorem not_safe_frame (hn : Nums c.a m0) {o : Nat} (h1 : 16 ≤ o) (h2 : o < 56) :
    ¬Safe m0 (fbA m0 + BitVec.ofNat 64 o) := by
  have := hn.hN
  rw [Safe, fb_add (by omega) (by omega)]
  have := hn.rS
  omega

/-- A `Safe` byte is in the function's stack or in the rows. -/
theorem safe_cases {q : BitVec 64} (h : Safe m0 q) :
    (spN m0 - 3104 ≤ q.toNat ∧ q.toNat < spN m0) ∨
      ((rwA m0).toNat ≤ q.toNat ∧ q.toNat < (rwA m0).toNat + 65536) := by
  unfold Safe at h
  omega

/-- A byte of the slot point is not `Safe`. -/
theorem not_safe_slot (hn : Nums c.a m0) {i : Nat} (hi : i < 96) :
    ¬Safe m0 (slA m0 + BitVec.ofNat 64 i) := fun h ↦ by
  have := hn.sW; have := hn.sS; have := hn.s_r
  have e := NativeRustcVm.toNat_add_ofNat (a := slA m0) (i := i) (by omega)
  have := safe_cases h
  rw [e] at this
  omega

variable [Labels]

/-- **The state around the fold kept** by a change in `Safe` bytes. -/
theorem Mid.keep (hm : Mid c m0 st) (hn : Nums c.a m0) (hb : Body m0 st')
    (hk : Kept st.dmem st'.dmem) {R : BitVec 64 → Prop}
    (hs : SameOutside st.dmem st'.dmem R) (hR : ∀ q, R q → Safe m0 q) :
    Mid c m0 st' := by
  have fw : ∀ {o : Nat} {w : UInt64}, 16 ≤ o → o + 8 ≤ 56 →
      NativeRustcVm.WordAt st.dmem (fbA m0 + BitVec.ofNat 64 o) w →
      NativeRustcVm.WordAt st'.dmem (fbA m0 + BitVec.ofNat 64 o) w := fun h1 h2 h ↦
    NativeRustcVm.BytesAt.of_sameOutside h hs fun i hi hR' ↦ by
      rw [NativeRustcVm.length_wordBytes] at hi
      rw [NativeRustcVm.addr_add_add] at hR'
      exact not_safe_frame hn (o := _ + i) (by omega) (by omega) (hR _ hR')
  refine ⟨hb, fw (by decide) (by decide) hm.v0, fw (by decide) (by decide) hm.v1,
    fw (by decide) (by decide) hm.out, fw (by decide) (by decide) hm.sw,
    fw (by decide) (by decide) hm.rw, hm.sl_size, ?_, ?_⟩
  · refine NativeRustcVm.BytesAt.of_sameOutside hm.slot hs fun i hi hR' ↦ ?_
    rw [NativeRustcVm.length_ewsBytes, Array.length_toList, hm.sl_size] at hi
    exact not_safe_slot hn hi (hR _ hR')
  · refine hm.ts.frame hk (fun q hq ↦ ?_) hs
    have hq' := safe_cases (hR q hq)
    have := hn.tW; have := hn.tS; have := hn.t_r; have := hn.wW; have := hn.wS; have := hn.r_w
    have et : tstateBytes = 760 := rfl
    refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
    · rw [NativeRustcVm.Transcript.inRange_iff' (show NativeRustcVm.NoWrap (tA m0) tstateBytes
        by unfold NativeRustcVm.NoWrap; rw [et]; omega), et] at h
      omega
    · rw [NativeRustcVm.Transcript.inRange_iff' (show NativeRustcVm.NoWrap c.a.words (8 * c.a.len)
        from hn.wW)] at h
      omega

end

end NativeRustcVmArm.KeccakGkr.KeccakOpen
