module

public import NativeRustcVmX64.KeccakGkr.VerifyKeccak.Call
public import NativeRustcVmX64.KeccakGkr.VerifyKeccak.Frame
public import NativeRustcVmX64.Transcript.Glue

/-!
# `verify_keccak`: facts across steps (x86-64)

A frame pointer's and a frame word's value in a step's environment (`ev_frame`, `ld_frame`), a
callee's changes as `ChgR` (`chgQ`, `inR_frame`, `inR_reg`), elements, claims and bit weights in
the frame or the scratch kept across a change (`Chg.ewsF`, `Chg.claimF`, `Chg.wtsR`, `Chg.wordF`).
-/

namespace NativeRustcVmX64.KeccakGkr.VerifyKeccak

open NativeRustcX64 NativeRustcX64.Sym NativeRustcVmX64.KeccakGkr.SeqZ NativeVm.Model
open NativeRustcVm.Transcript (DecArea TStateAt)
open NativeRustcVm.KeccakGkr (off ClaimAt WeightsAt)

public section

variable [Labels] {m0 : MachineData} {a : DecArea} {inst : Array EW}

theorem ev_frame {d : MachineData} {rs : List (BitVec 64 × Nat)} {vals : Nat → BitVec 64}
    {ret : BitVec 64} (o : Nat) :
    (Sym.ptr 0 (o : Int)).eval (envZ m0 d 3344 3368 rs vals ret) = off (fb m0) o :=
  Fn.eval_ptr0' o

omit [Labels] in
theorem ld_frame {d : MachineData} {rs : List (BitVec 64 × Nat)} {vals : Nat → BitVec 64}
    {ret : BitVec 64} {o : Nat} {w : UInt64} (h : NativeRustcVm.WordAt d.dmem (off (fb m0) o) w) :
    (envZ m0 d 3344 3368 rs vals ret).load 0 o 8 = w.toBitVec :=
  NativeRustcVmX64.Transcript.load_ofMachine rfl h

/-- **A callee's changes** as `ChgR`. -/
theorem chgQ {mc m' : MachineData} {R : BitVec 64 → Prop} {Sk : Nat} {L : List (Nat × Nat)}
    {O : List (Nat × Nat × Nat)} (hs : SameOutside mc.dmem m'.dmem R)
    (hR : ∀ q, R q → InRange (stackBelow mc Sk) Sk q ∨ ChgR m0 L O q) (hsv : Saved mc m') :
    SameOutside mc.dmem m'.dmem (fun q ↦ InRange (stackBelow mc Sk) Sk q ∨ ChgR m0 L O q) ∧
      Saved mc m' :=
  ⟨fun q hq ↦ hs q fun h ↦ hq (hR q h), hsv⟩

/-- An output in the frame at offset `o` is a change. -/
theorem inR_frame {L : List (Nat × Nat)} {O : List (Nat × Nat × Nat)} {x : BitVec 64} {o n : Nat}
    (hx : x = off (fb m0) o) (hp : (o, n) ∈ L) {q : BitVec 64} (h : InRange x n q) :
    ChgR m0 L O q := by
  subst hx; exact chgR_frame hp h

/-- An output in region `i` at offset `o` is a change. -/
theorem inR_reg {L : List (Nat × Nat)} {O : List (Nat × Nat × Nat)} {x : BitVec 64} {i o n : Nat}
    (hx : x = off (ob m0 i) o) (hp : (i, o, n) ∈ O) {q : BitVec 64} (h : InRange x n q) :
    ChgR m0 L O q := by
  subst hx; exact chgR_reg hp h

/-- **Elements in the frame** kept across a change. -/
theorem Chg.ewsF (c : Ctx a inst m0) {d d' : DataMem} {L : List (Nat × Nat)}
    {O : List (Nat × Nat × Nat)} (h : Chg m0 d d' L O) (hL : okL L = true) (hO : okO O = true)
    {o : Nat} {xs : List EW} (hm : missL L o (16 * xs.length) = true)
    (hon : o + 16 * xs.length ≤ 3368) (he : NativeRustcVm.EWsAt d (off (fb m0) o) xs) :
    NativeRustcVm.EWsAt d' (off (fb m0) o) xs :=
  NativeRustcVm.Tables.EWsAt.of_same he (Chg.frame c h hL hO hm hon) le_rfl

/-- **A word in the frame** kept across a change. -/
theorem Chg.wordF (c : Ctx a inst m0) {d d' : DataMem} {L : List (Nat × Nat)}
    {O : List (Nat × Nat × Nat)} (h : Chg m0 d d' L O) (hL : okL L = true) (hO : okO O = true)
    {o : Nat} {w : UInt64} (hm : missL L o 8 = true) (hon : o + 8 ≤ 3368)
    (he : NativeRustcVm.WordAt d (off (fb m0) o) w) : NativeRustcVm.WordAt d' (off (fb m0) o) w :=
  NativeRustcVm.Layout.WordAt.of_same he (Chg.frame c h hL hO hm hon) le_rfl

/-- **A claim in the frame** kept across a change. -/
theorem Chg.claimF (c : Ctx a inst m0) {d d' : DataMem} {L : List (Nat × Nat)}
    {O : List (Nat × Nat × Nat)} (h : Chg m0 d d' L O) (hL : okL L = true) (hO : okO O = true)
    {o : Nat} {x : KeccakClaimW} (hm : missL L o 768 = true) (hon : o + 768 ≤ 3368)
    (he : ClaimAt d (off (fb m0) o) x) : ClaimAt d' (off (fb m0) o) x := by
  have hs := Chg.frame c h hL hO hm hon
  obtain ⟨h1, h2, h3⟩ := he
  refine ⟨NativeRustcVm.Layout.EWAt.of_same h1 hs (by omega),
    NativeRustcVm.Layout.BufEWAt.of_same h2 (hs.sub (o := 16) (k := 264) (by omega)) (by decide),
    NativeRustcVm.Layout.BufEWAt.of_same h3 (hs.sub (o := 280) (k := 488) (by omega)) (by decide)⟩

/-- **Bit weights in the scratch** at offset `o` kept across a change. -/
theorem Chg.wtsR (c : Ctx a inst m0) {d d' : DataMem} {L : List (Nat × Nat)}
    {O : List (Nat × Nat × Nat)} (h : Chg m0 d d' L O) (hL : okL L = true) (hO : okO O = true)
    {o : Nat} {x : KeccakClaimW} (hm : missO O 2 o 25600 = true) (hon : o + 25600 ≤ 205824)
    (he : WeightsAt d (off (reg m0 .r9) o) x) : WeightsAt d' (off (reg m0 .r9) o) x := by
  have hs := Chg.regS c h hL hO (i := 2) (by omega) (by omega) hm hon
  refine ⟨he.1, NativeRustcVm.Tables.EWsAt.of_same he.2 hs ?_⟩
  simp only [Array.length_toList, he.1]; decide

/-- **Elements in region `i`** kept across a change. -/
theorem Chg.ewsR (c : Ctx a inst m0) {d d' : DataMem} {L : List (Nat × Nat)}
    {O : List (Nat × Nat × Nat)} (h : Chg m0 d d' L O) (hL : okL L = true) (hO : okO O = true)
    {i o : Nat} (h1 : 1 ≤ i) (h4 : i ≤ 4) {xs : List EW} (hm : missO O i o (16 * xs.length) = true)
    (hon : o + 16 * xs.length ≤ rsz i) (he : NativeRustcVm.EWsAt d (off (ob m0 i) o) xs) :
    NativeRustcVm.EWsAt d' (off (ob m0 i) o) xs :=
  NativeRustcVm.Tables.EWsAt.of_same he (Chg.regS c h hL hO h1 h4 hm hon) le_rfl

omit [Labels] in
theorem off0 (x : BitVec 64) : off x 0 = x := by simp [off]

end

end NativeRustcVmX64.KeccakGkr.VerifyKeccak
