/-
  Rv64mc.Proof.Runtime.InputDigestT

  `Input::digest` is total (`InputDigestSpecT`): it reads four words through `Input::word` (`InputWordT`) and stores
  their 32 bytes at `sret`, writing of its caller's at most `DigestOut` (the result's doublewords and the reader), or
  the run ends with `a0 = 2` where the reader runs out (`Input::word`'s `WordStop`, weakened to `AbortStop`). Its
  postcondition is what a caller reads on with: the reader still satisfies `Input::word`'s total precondition
  (`ReaderT`). The precondition (`DigestPreT`) adds to the partial `DigestPre` the result in a window, the reader at
  or above the stack pointer (in a caller's frame, so apart from this one's) and `ReaderT`. A safety contract: the
  partial `DigestPost` (the bytes stored, the reader advanced by four words) is not proved here (class C, owed).

  The body is cut after the fourth call (instruction 24, `stores`): the calls part keeps `Mem` (`SavedT.MemOk`
  over the six saved registers' slots, with `DigestOut` as the frame's writes) and `ReaderT` across each call
  (`ReaderT.next`); the stores part steps the 32 byte stores and the epilogue.

  ## Main definitions

  * `ReaderT`, `DigestPreT`, `DigestPostT`, `InputDigestSpecT`, `Mem`

  ## Main results

  * `ReaderT.next`, `stores`, `total`
-/

import Rv64mc.Proof.Runtime.InputWordT
import Rv64mc.Proof.Runtime.WinT
import Rv64mc.Proof.Runtime.SavedT
import Rv64mc.Core.AbortStop
import Rv64mc.Gen.Tmpl.VerifierRv64.Input.Digest

namespace Rv64mc.Proof.Runtime.InputDigestT

open RiscvZkvm.Rv64 Lprog Lprog.RiscV Rv64mc.Spec.Runtime Rv64mc.Proof.Runtime
open Rv64mc.Proof.Runtime.InputWordT (WordPreT WordStop InputWordSpecT)
open Rv64mc.Proof.Runtime.MemsetT (InWin)
open Rv64mc.Proof.Runtime.SavedT (SlotsIn slots_le)
open Rv64mc.Gen.VerifierRv64.Input.Digest (Link tmpl)

/-- **The reader at `a` satisfies `Input::word`'s total precondition** in `m`. -/
def ReaderT (env : Env) (a : Word) (m : MachineState) : Prop := WordPreT env (fun _ => a) m

/-- `Input::digest`'s total precondition: `DigestPre`, the result in a window, the reader at or above the stack
    pointer and `ReaderT`. -/
def DigestPreT (env : Env) (regs : Reg → Word) (m : MachineState) : Prop :=
  DigestPre env regs m ∧ InWin env (regs .x10) Layouts.Digest.byteSize ∧ (regs .x2).toNat ≤ (regs .x11).toNat ∧
    ReaderT env (regs .x11) m

/-- `Input::digest`'s total postcondition: the reader still satisfies `ReaderT`. -/
def DigestPostT (env : Env) (regs : Reg → Word) (_m : MachineState) (_r' : Reg → Word) (m' : MachineState) :
    Prop :=
  ReaderT env (regs .x11) m'

/-- **The total contract of `Input::digest`**: from `DigestPreT`, the reader kept `ReaderT`, writing at most
    `DigestOut`, or `a0 = 2`. -/
def InputDigestSpecT (env : Env) (p : Lprog (Op Reg) Reg) (i need : Nat) : Prop :=
  HoldsT env p i need (DigestPreT env) (DigestPostT env) DigestOut AbortStop

variable {env : Env}

/-- **A word read keeps `ReaderT`**: the slice advanced by one word stays where it was. -/
theorem ReaderT.next {a : Word} {m m' : MachineState} {r' : Reg → Word} (h : ReaderT env a m)
    (hp : WordPost (fun _ => a) m r' m') : ReaderT env a m' := by
  obtain ⟨hw, hal, hhi, hs⟩ := h
  obtain ⟨hl, -, hq, hn⟩ := hp
  change m'.getMem (inputPtrAt a) = m.getMem (inputPtrAt a) + 8 at hq
  change m'.getMem (inputLenAt a) = m.getMem (inputLenAt a) - 1 at hn
  change m.getMem (inputLenAt a) ≠ 0 at hl
  have hl0 : (m.getMem (inputLenAt a)).toNat ≠ 0 := fun h0 => hl (BitVec.eq_of_toNat_eq h0)
  obtain ⟨h1, h2, h3⟩ := hs hl0
  dsimp only at h1 h2 h3
  have hhe := env.heapEnd.isLt
  have e1 : (m.getMem (inputPtrAt a) + 8).toNat = (m.getMem (inputPtrAt a)).toNat + 8 :=
    toNat_add_ofNat (k := 8) (by omega)
  have e2 : (m.getMem (inputLenAt a) - 1).toNat = (m.getMem (inputLenAt a)).toNat - 1 := by
    rw [BitVec.toNat_sub]; norm_num; omega
  refine ⟨hw, hal, hhi, fun hl' => ?_⟩
  change (m'.getMem (inputLenAt a)).toNat ≠ 0 at hl'
  change 0x10000000 ≤ (m'.getMem (inputPtrAt a)).toNat ∧ (m'.getMem (inputPtrAt a)).toNat % 8 = 0 ∧
    (m'.getMem (inputPtrAt a)).toNat + 8 * (m'.getMem (inputLenAt a)).toNat ≤ env.heapEnd.toNat
  rw [hn, e2] at hl'
  rw [hq, hn, e1, e2]
  exact ⟨by omega, by omega, by omega⟩

/-- `ReaderT` in a memory that agrees on the reader's two words. -/
theorem ReaderT.of_eq {a : Word} {m M : MachineState} (h : ReaderT env a m)
    (hp : M.getMem (inputPtrAt a) = m.getMem (inputPtrAt a)) (hl : M.getMem (inputLenAt a) = m.getMem (inputLenAt a)) :
    ReaderT env a M := by
  obtain ⟨hw, hal, hhi, hs⟩ := h
  exact ⟨hw, hal, hhi, fun h' => by
    change (M.getMem (inputLenAt a)).toNat ≠ 0 at h'
    change 0x10000000 ≤ (M.getMem (inputPtrAt a)).toNat ∧ (M.getMem (inputPtrAt a)).toNat % 8 = 0 ∧
      (M.getMem (inputPtrAt a)).toNat + 8 * (M.getMem (inputLenAt a)).toNat ≤ env.heapEnd.toNat
    rw [hp, hl] at *; exact hs h'⟩

/-- The callee-saved registers the function never saves (`s5` to `s11`), as at the entry. -/
def Keep (regs R : Reg → Word) : Prop :=
  R .x21 = regs .x21 ∧ R .x22 = regs .x22 ∧ R .x23 = regs .x23 ∧ R .x24 = regs .x24 ∧ R .x25 = regs .x25 ∧
    R .x26 = regs .x26 ∧ R .x27 = regs .x27

/-- What the parts keep of memory: `SavedT.MemOk` with the six saved registers' slots, from `top - 8` (the return
    address) down to `top - 48` (`s4`), writing of the caller's at most `DigestOut`. -/
abbrev Mem (env : Env) (ret top : Word) (regs : Reg → Word) (m M : MachineState) : Prop :=
  Runtime.SavedT.MemOk env top (DigestOut regs m)
    [18446744073709551608#64, 18446744073709551600#64, 18446744073709551592#64, 18446744073709551584#64,
      18446744073709551576#64, 18446744073709551568#64]
    [ret, regs .x8, regs .x9, regs .x18, regs .x19, regs .x20] m M

/-- The saved slots lie in the `48` bytes below `top`. -/
theorem slots : SlotsIn 48
    [18446744073709551608#64, 18446744073709551600#64, 18446744073709551592#64, 18446744073709551584#64,
      18446744073709551576#64, 18446744073709551568#64] :=
  slots_le

/-- **A byte store into the result keeps `Mem` and `ReaderT`**: its doubleword is the result's (`DigestOut`), in a
    window, apart from the saved slots (the result at or above `top`) and from the reader (`DigestPre`). -/
theorem byte_ok {ret top a : Word} {c : BitVec 8} {regs : Reg → Word} {m M : MachineState}
    (h : Mem env ret top regs m M ∧ ReaderT env (regs .x11) M) (hw : InWin env (regs .x10) 32)
    (hd3 : top.toNat ≤ (regs .x10).toNat)
    (hd5 : ∀ b, InRange (regs .x11) Layouts.Input.byteSize b →
      ¬ InRange (alignToDword (regs .x10)) (Layouts.Digest.byteSize + (regs .x10).toNat % 8) b)
    (h16 : top.toNat % 16 = 0) (hlim : env.stackLimit.toNat + 48 ≤ top.toNat) (ha : InRange (regs .x10) 32 a) :
    Mem env ret top regs m (M.setByte a c) ∧ ReaderT env (regs .x11) (M.setByte a c) := by
  obtain ⟨⟨hF, hc, hS, hsv⟩, hR⟩ := h
  have hal := toNat_alignToDword a
  have hal0 := toNat_alignToDword (regs .x10)
  have hwl := hw.lt
  unfold InRange at ha
  obtain ⟨hs, hn⟩ := hw.apart (b := alignToDword a) (by omega) (by omega)
  have hsb : Layouts.Digest.byteSize = 32 := rfl
  have hib : Layouts.Input.byteSize = 16 := rfl
  have keep : ∀ y : Word, (alignToDword a).toNat ≠ y.toNat → (M.setByte a c).getMem y = M.getMem y :=
    fun y hy => getMem_setByte_ne (fun he => hy (by rw [he]))
  have hrd : ∀ b, InRange (regs .x11) 16 b → (M.setByte a c).getMem b = M.getMem b := fun b hb =>
    keep b fun he => hd5 b hb (by unfold InRange; omega)
  have hx11 := (regs .x11).isLt
  refine ⟨⟨frame_byte_out hF (.inl (by unfold InRange; omega)) hn,
    by rw [setByte_def, MachineState.code_setMem]; exact hc,
    static_byte hS hs, hsv.keep (K := 48) (by omega) (fun y h1 h2 => keep y (by omega)) slots⟩,
    hR.of_eq (hrd _ ?_) (hrd _ ?_)⟩
  all_goals
    have := hR.1.2
    simp only [InRange, inputPtrAt, inputLenAt]
    rw [BitVec.toNat_add, BitVec.toNat_ofNat]
    simp only [Layouts.Input.f0, Layouts.SliceE.ptr, Layouts.SliceE.len] at this ⊢
    omega

/-- The facts every byte store reads. -/
structure Fx (env : Env) (top : Word) (regs : Reg → Word) : Prop where
  hw : InWin env (regs .x10) 32
  hd3 : top.toNat ≤ (regs .x10).toNat
  hd5 : ∀ b, InRange (regs .x11) Layouts.Input.byteSize b →
    ¬ InRange (alignToDword (regs .x10)) (Layouts.Digest.byteSize + (regs .x10).toNat % 8) b
  h16 : top.toNat % 16 = 0
  hlim : env.stackLimit.toNat + 48 ≤ top.toNat

/-- `byte_ok` at the result's byte `k`. -/
theorem byteK {ret top : Word} {c : BitVec 8} {regs : Reg → Word} {m M : MachineState} {k : Nat}
    (h : Mem env ret top regs m M ∧ ReaderT env (regs .x11) M) (F : Fx env top regs) (hk : k < 32) :
    Mem env ret top regs m (M.setByte (regs .x10 + BitVec.ofNat 64 k) c) ∧
      ReaderT env (regs .x11) (M.setByte (regs .x10 + BitVec.ofNat 64 k) c) :=
  byte_ok h F.hw F.hd3 F.hd5 F.h16 F.hlim (inRange_add hk F.hw.lt)

/-- `byte_ok` at the result's first byte. -/
theorem byte0 {ret top : Word} {c : BitVec 8} {regs : Reg → Word} {m M : MachineState}
    (h : Mem env ret top regs m M ∧ ReaderT env (regs .x11) M) (F : Fx env top regs) :
    Mem env ret top regs m (M.setByte (regs .x10) c) ∧ ReaderT env (regs .x11) (M.setByte (regs .x10) c) := by
  have := byteK (k := 0) (c := c) h F (by decide)
  rwa [show BitVec.ofNat 64 0 = 0#64 from rfl, BitVec.add_zero] at this

/-- `Mem` and `ReaderT` through the result's byte stores. -/
local macro "bytes_close " F:term:max h:term:max : tactic => `(tactic| (
  repeat (first
    | with_reducible refine byte0 ?_ $F
    | with_reducible refine byteK ?_ $F (by decide))
  exact $h))

set_option rv_sym.heap true in
/-- **The epilogue** (instruction 84): the saved registers restored, the return. -/
theorem epi (L : Link) (p : Lprog (Op Reg) Reg) (i : Nat) (hp : p[i]? = some (tmpl L))
    {Q : State rvIsa → Prop} {ret top : Word} {rest : List Frame} {regs : Reg → Word} {m : MachineState}
    (hk : ∀ r' m', HoldsT.post env (DigestPostT env) DigestOut ret top regs m r' m' →
      rvIsa.Total p stmtCtx (WinOk p) Q ⟨rest, r', m'⟩)
    (hlim : env.stackLimit.toNat + 48 ≤ top.toNat) (hal : top.toNat % 16 = 0) (hW : Windows env top m) :
    ∀ R M, R .x2 = top + 18446744073709551568#64 → Keep regs R →
      Mem env ret top regs m M ∧ ReaderT env (regs .x11) M →
      rvIsa.Total p stmtCtx (WinOk p) Q ⟨⟨i, 168, ret, top⟩ :: rest, R, M⟩ := by
  intro R M h2 hK ⟨hM, hR⟩
  have hI : R .x2 = top + 18446744073709551568#64 ∧ Keep regs R ∧ Mem env ret top regs m M := ⟨h2, hK, hM⟩
  have hpack := PLift.up hR
  clear hR
  rv_introT hI
  rv_symT hp with [hlim]
  all_goals
    obtain ⟨⟨a1, a2⟩, a3, a4, a5⟩ := hpack.down
    first | exact a1 | exact a2 | exact a3 | exact a4 | exact a5

set_option rv_sym.heap true in
/-- **The stores** (instruction 24): the four words' 32 bytes at `sret`, `Mem` and `ReaderT` kept by each
    (`bytes_close`), then the epilogue. -/
theorem stores (L : Link) (p : Lprog (Op Reg) Reg) (i : Nat) (hp : p[i]? = some (tmpl L))
    {Q : State rvIsa → Prop} {ret top : Word} {rest : List Frame} {regs : Reg → Word} {m : MachineState}
    (hk : ∀ r' m', HoldsT.post env (DigestPostT env) DigestOut ret top regs m r' m' →
      rvIsa.Total p stmtCtx (WinOk p) Q ⟨rest, r', m'⟩)
    (hW : Windows env top m) (F : Fx env top regs) :
    ∀ R M, R .x2 = top + 18446744073709551568#64 → R .x8 = regs .x10 → Keep regs R →
      Mem env ret top regs m M ∧ ReaderT env (regs .x11) M →
      rvIsa.Total p stmtCtx (WinOk p) Q ⟨⟨i, 48, ret, top⟩ :: rest, R, M⟩ := by
  intro R M h2 h8 hK hMR
  have hlim := F.hlim
  have hal := F.h16
  have hw := F.hw
  have hcode := hMR.1.2.1
  have hpack := PLift.up hMR
  clear hMR
  have hI : R .x2 = top + 18446744073709551568#64 ∧ R .x8 = regs .x10 ∧ Keep regs R := ⟨h2, h8, hK⟩
  rv_introT hI
  rv_symT hp stop [168] with [hlim]
  refine epi L p i hp hk hlim hal hW _ _ rfl ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ ?_
  bytes_close F hpack.down

/-- **`Mem` across `Input::word`** on the reader (`r .x10`, the entry's `x11`), from the stack pointer `top - 48`:
    what it writes is the reader's two words, `DigestOut`'s. -/
theorem call_ok {ret top : Word} {regs r : Reg → Word} {m M X : MachineState}
    (hM : Mem env ret top regs m M) (hlim : env.stackLimit.toNat + 48 ≤ top.toNat)
    (hx : top.toNat ≤ (regs .x11).toNat ∧ (regs .x11).toNat + 16 < 2 ^ 64) (hr : r .x10 = regs .x11)
    (hf : env.Frame (top + 18446744073709551568#64) (WordOut r M) M X)
    (hk : ∀ a : Word, top + 18446744073709551568#64 ≤ a → ¬ WordOut r M a → X.getMem a = M.getMem a)
    (hc : X.code = M.code) (hs : env.Static X) : Mem env ret top regs m X := by
  have e : (top + 18446744073709551568#64).toNat = top.toNat - 48 := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  refine hM.call slots (by omega) (by omega) hf hc hs (fun a ha => .inr (.inr (.inr (.inr ?_))))
    (fun a h1 h2 => hk a (Tactic.le_of_toNat (by omega)) fun hw => ?_)
  · unfold WordOut at ha; rw [hr] at ha; exact ha
  · unfold WordOut at hw; rw [hr] at hw
    simp only [inputPtrAt, inputLenAt, Layouts.Input.f0, Layouts.SliceE.ptr, Layouts.SliceE.len] at hw
    rcases hw with hw | hw <;> (have := congrArg BitVec.toNat hw; rw [toNat_add_ofNat (by omega)] at this; omega)

/-- A word of a caller's object (at or above `top`) read through the prologue's six stores. -/
theorem rd6 {M : MachineState} {top a v1 v2 v3 v4 v5 v6 : Word} {o : Nat} (ha : top.toNat ≤ a.toNat)
    (hw : a.toNat + 16 < 2 ^ 64) (htop : 48 ≤ top.toNat) (ho : o < 16) :
    ((((((M.setMem (top + 18446744073709551608#64) v1).setMem (top + 18446744073709551600#64) v2).setMem
      (top + 18446744073709551592#64) v3).setMem (top + 18446744073709551584#64) v4).setMem
      (top + 18446744073709551576#64) v5).setMem (top + 18446744073709551568#64) v6).getMem
      (a + BitVec.ofNat 64 o) = M.getMem (a + BitVec.ofNat 64 o) := by
  have e : (a + BitVec.ofNat 64 o).toNat = a.toNat + o := toNat_add_ofNat (by omega)
  have ne : ∀ c : Word, 2 ^ 64 - 48 ≤ c.toNat → a + BitVec.ofNat 64 o ≠ top + c := fun c hc => Tactic.ne_of_toNat (by
    rw [e, BitVec.toNat_add]; have := c.isLt; omega)
  rw [MachineState.getMem_setMem_ne (ne _ (by decide)), MachineState.getMem_setMem_ne (ne _ (by decide)),
    MachineState.getMem_setMem_ne (ne _ (by decide)), MachineState.getMem_setMem_ne (ne _ (by decide)),
    MachineState.getMem_setMem_ne (ne _ (by decide)), MachineState.getMem_setMem_ne (ne _ (by decide))]

set_option rv_sym.heap true in
/-- **`Input::digest` is total**: the prologue and the four calls, `ReaderT` carried across each by
    `ReaderT.next`, then the stores. -/
theorem total (L : Link) (p : Lprog (Op Reg) Reg) (i : Nat) (hp : p[i]? = some (tmpl L)) (hL : L.WF p)
    {need needW : Nat} (hnW : 48 + needW ≤ need) (hw : InputWordSpecT env p L.word.idx needW) :
    InputDigestSpecT env p i need := by
  have hw' : HoldsT env p L.word.idx needW (WordPreT env) WordPost WordOut (Stop := AbortStop) :=
    hw.mono_stop fun _ _ _ _ _ h => h.1
  rv_autoT hp stop [48] with [hL] using [hw']
  all_goals
    have hR : ReaderT env (regs .x11) m := ⟨⟨hpre_14, hpre_15⟩, hpre_16, hpre_17, hpre_18⟩
    have hlim : env.stackLimit.toNat + 48 ≤ top.toNat := by omega
    rw [hpre_2] at hpre_13
    have hib : Layouts.Input.byteSize = 16 := rfl
    have hP := fun (M' : MachineState) (v1 v2 v3 v4 v5 v6 : Word) =>
      rd6 (M := M') (v1 := v1) (v2 := v2) (v3 := v3) (v4 := v4) (v5 := v5) (v6 := v6)
        (o := Layouts.Input.f0 + Layouts.SliceE.ptr) hpre_13 (by omega) (by omega) (by decide)
    have hL' := fun (M' : MachineState) (v1 v2 v3 v4 v5 v6 : Word) =>
      rd6 (M := M') (v1 := v1) (v2 := v2) (v3 := v3) (v4 := v4) (v5 := v5) (v6 := v6)
        (o := Layouts.Input.f0 + Layouts.SliceE.len) hpre_13 (by omega) (by omega) (by decide)
  -- `Input::word`'s precondition at each call: the reader through the prologue, then through each call
  · exact (hR.of_eq (hP _ _ _ _ _ _ _) (hL' _ _ _ _ _ _ _)).2.2.2
  · exact (ReaderT.next (hR.of_eq (hP _ _ _ _ _ _ _) (hL' _ _ _ _ _ _ _)) hret1_16).2.2.2
  · exact (ReaderT.next (ReaderT.next (hR.of_eq (hP _ _ _ _ _ _ _) (hL' _ _ _ _ _ _ _)) hret1_16) hret2_16).2.2.2
  · exact (ReaderT.next (ReaderT.next (ReaderT.next (hR.of_eq (hP _ _ _ _ _ _ _) (hL' _ _ _ _ _ _ _)) hret1_16)
      hret2_16) hret3_16).2.2.2
  -- the stores
  · rw [hpre_2] at hpre_8
    have hx : top.toNat ≤ (regs .x11).toNat ∧ (regs .x11).toNat + 16 < 2 ^ 64 := ⟨hpre_13, by omega⟩
    refine stores L p i hp hk hpre_20 ⟨hpre_12, hpre_8, hpre_10, hpre_19, hlim⟩ _ _ rfl (by rv_closeT)
      ⟨by rv_closeT, by rv_closeT, by rv_closeT, by rv_closeT, by rv_closeT, by rv_closeT, by rv_closeT⟩
      ⟨call_ok (call_ok (call_ok (call_ok ?m0 hlim hx rfl hret1_14 keep1_1 hret1_17 hret1_15) hlim hx rfl hret2_14
        keep2_1 hret2_17 hret2_15) hlim hx rfl hret3_14 keep3_1 hret3_17 hret3_15) hlim hx rfl hret4_14 keep4_1
        hret4_17 hret4_15,
       ReaderT.next (ReaderT.next (ReaderT.next (ReaderT.next (hR.of_eq (hP _ _ _ _ _ _ _) (hL' _ _ _ _ _ _ _))
        hret1_16) hret2_16) hret3_16) hret4_16⟩
    case m0 => refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, trivial⟩ <;> rv_closeT

end Rv64mc.Proof.Runtime.InputDigestT

/-- info: 'Rv64mc.Proof.Runtime.InputDigestT.total' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Rv64mc.Proof.Runtime.InputDigestT.total
