module

public import NativeRustcArm.Code.Sphincs.SphincsVerify.Names

public import NativeRustcArm.SphincsVerify.Calls
public import NativeRustcArm.SphincsVerify.Encode.Digits
public import NativeRustc.Sphincs.EncodeFacts
public import NativeRustcArm.Sym

/-!
# The codeword's loop `b110`

`b110` (`.LSphincsVerify_41`, directive 1392) runs 16 turns, turn `j` (X8 `8 j`, X11 the frame's
`26769 + 4 j`) writing the digits `4 j .. 4 j + 3` of the 128-bit digest `X9 · 2⁶⁴ + X10` to
`26768 + 4 j ..` (`loopWrites`, the digit at bit `s` as `digitSym s`). The executor's result for
each turn is checked by the kernel once (`loopOk_all`); `loop_step` reads one turn off it, `loop`
runs the turns: the 64 digits `digits V` at `26768`, the rest of the frame kept.
-/

namespace NativeRustcArm.SphincsVerifyProof

open NativeRustc NativeRustc.Sphincs NativeRustcArm.Sym

@[expose] public section

set_option Elab.async false

/-- The digit at bit `s` of `X9 · 2⁶⁴ + X10` as the loop computes it. -/
def digitSym (s : Nat) : Sym :=
  if 64 ≤ s then .bin .and .W32 (.bin .lsrv .W64 (.reg .X9) (.lit s)) (.lit 3)
  else .bin .and .W32 (.bin .orr .W64 (.bin .lslv .W64 (.un (.ubfm 63 62) .W64 (.reg .X9))
    (.lit (4294967295 - s))) (.bin .lsrv .W64 (.reg .X10) (.lit s))) (.lit 3)

/-- Turn `j`'s writes: the digits `4 j + 3`, `4 j + 2`, `4 j`, `4 j + 1`. -/
def loopWrites (j : Nat) : List Write :=
  [⟨0, 26768 + 4 * j + 3, 1, digitSym (126 - 8 * j - 6)⟩,
    ⟨0, 26768 + 4 * j + 2, 1, digitSym (126 - 8 * j - 4)⟩,
    ⟨0, 26768 + 4 * j, 1, digitSym (126 - 8 * j)⟩,
    ⟨0, 26768 + 4 * j + 1, 1, digitSym (126 - 8 * j - 2)⟩]

/-- Turn `j`'s symbolic state. -/
def loopInit (j : Nat) : SState :=
  init [(29376, true)] (.ptr 0 0)
    [(.X8, .lit (8 * j)), (.X11, .ptr 0 ((26769 + 4 * j : Nat) : Int)), (.X29, .ptr 0 29280)]

/-- Turn `j` as the executor runs it: back to the loop's head unless last, X8 and X11 on, X9, X10,
X29, SP and the callee-saved registers kept, the four digits written. -/
def loopOk (j : Nat) : Bool :=
  match exec Sphincs.SphincsVerify.b110 (loopInit j) with
  | some (S, x) => x == .cond (.lit (j + 1 != 16)) NativeRustcArm.Sphincs.SphincsVerify.label_41 &&
      S.reg .X8 == some (.lit (8 * j + 8)) &&
      S.reg .X11 == some (.ptr 0 ((26773 + 4 * j : Nat) : Int)) &&
      S.reg .X9 == some (.reg .X9) && S.reg .X10 == some (.reg .X10) &&
      S.reg .X29 == some (.ptr 0 29280) && S.sp == .ptr 0 0 && S.mem == loopWrites j &&
      keeps (loopInit j) S && Run.frameWrites S
  | none => false

theorem loopOk_all : ∀ j < 16, loopOk j = true := by decide +kernel

/-! ## The digits -/

/-- **A digit's value**: bits `s, s + 1` of `X9 · 2⁶⁴ + X10`. -/
theorem eval_digitSym [Labels] (env : Env) {s : Nat} (hs : s < 128) (hs' : s ≠ 63) :
    ((digitSym s).eval env).toNat =
      ((env.regs .X9).toNat * 2 ^ 64 + (env.regs .X10).toNat) >>> s % 4 := by
  unfold digitSym
  split
  · simp only [Sym.eval]
    exact digit_hi _ (env.regs .X10).isLt (by omega) hs
  · simp only [Sym.eval]
    exact digit_lo _ _ (by omega)

theorem findWrite_loopWrites (j t : Nat) (ht : t < 4) :
    findWrite 0 (26768 + 4 * j + t) (loopWrites j) = some (digitSym (126 - 8 * j - 2 * t), 0) := by
  interval_cases t <;> simp [findWrite, loopWrites]

/-! ## Frame facts -/

namespace Run

variable (r : Run) [Labels]

/-- The frame's bytes `a .. a + n` as addresses. -/
theorem inRange_off_iff (hpre : r.Pre) {a n : Nat} (h : a + n ≤ 29376) (p : BitVec 64) :
    InRange (r.off a) n p ↔ r.base.toNat + a ≤ p.toNat ∧ p.toNat < r.base.toNat + a + n := by
  have hb := r.base_toNat hpre
  have := r.m0.regs.SP.toNat_lt
  rw [Sym.inRange_iff (by rw [r.off_toNat hpre (by omega)]; omega), r.off_toNat hpre (by omega)]

/-- **A block's writes inside the frame's bytes `o .. o + n`** change only those. -/
theorem written_inRange (hpre : r.Pre) {m : MachineData} {vars : Nat → BitVec 64} {S : SState}
    {o n : Nat} (hon : o + n ≤ 29376)
    (hS : ∀ w ∈ S.mem, w.r = 0 ∧ o ≤ w.off ∧ w.off + w.n ≤ o + n) {p : BitVec 64}
    (hp : Written (r.env m vars) S p) : InRange (r.off o) n p := by
  obtain ⟨w, hw, b, sz, hb, h1, h2⟩ := hp
  obtain ⟨hr, ho, hn⟩ := hS w hw
  rw [hr] at hb
  cases hb
  rw [r.inRange_off_iff hpre hon]
  omega

end Run

/-! ## A turn -/

/-- The 128-bit digest the loop takes apart: `X9 · 2⁶⁴ + X10`. -/
def digest128 (m : MachineData) : Nat :=
  (m.regs.getXReg .X9).toBitVec.toNat * 2 ^ 64 + (m.regs.getXReg .X10).toBitVec.toNat

theorem label_41 [NativeRustcArm.Host] {k : Nat} (hp : Placed Sphincs.SphincsVerify.code k) :
    Labels.label NativeRustcArm.Sphincs.SphincsVerify.label_41 = NativeRustcArm.Host.addrOf (k + NativeRustcArm.Sphincs.SphincsVerify.b110Offset) :=
  hp.label NativeRustcArm.Sphincs.SphincsVerify.label_41_at


variable [NativeRustcArm.Host]

/-- **A turn of the loop**: turn `j` writes the digits `4 j .. 4 j + 3` at `26768 + 4 j`, and
goes back to the loop's head, or on to `b111` after the last. -/
theorem loop_step (r : Run) (hp : Placed Sphincs.SphincsVerify.code r.k) (hpre : r.Pre) {j : Nat}
    (hj : j < 16) (m : MachineData) (hF : r.Frame m)
    (h8 : Run.RegIs m .X8 (BitVec.ofNat 64 (8 * j)))
    (h11 : Run.RegIs m .X11 (r.off (26769 + 4 * j))) :
    Eventually (step1 NativeRustcArm.Host.exe) (fun st ↦
      st.pc = (if j + 1 = 16 then r.pc NativeRustcArm.Sphincs.SphincsVerify.b111Offset else r.pc NativeRustcArm.Sphincs.SphincsVerify.b110Offset) ∧ r.Frame st.data ∧
      Run.RegIs st.data .X8 (BitVec.ofNat 64 (8 * (j + 1))) ∧
      Run.RegIs st.data .X11 (r.off (26769 + 4 * (j + 1))) ∧ digest128 st.data = digest128 m ∧
      Saved m st.data ∧ SameOutside m.dmem st.data.dmem (InRange (r.off (26768 + 4 * j)) 4) ∧
      ∀ t < 4, st.data.dmem.get? (r.off (26768 + 4 * j + t)) =
        some (UInt8.ofNat (digest128 m >>> (126 - 2 * (4 * j + t)) % 4)))
      ⟨m, r.pc NativeRustcArm.Sphincs.SphincsVerify.b110Offset⟩ := by
  have hok := loopOk_all j hj
  rw [loopOk] at hok
  rcases hx : exec Sphincs.SphincsVerify.b110 (loopInit j) with _ | ⟨S, x⟩
  · rw [hx] at hok
    exact absurd hok Bool.false_ne_true
  · rw [hx] at hok
    simp only [Bool.and_eq_true, beq_iff_eq] at hok
    obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨hxe, hs8⟩, hs11⟩, hs9⟩, hs10⟩, hs29⟩, hssp⟩, hsmem⟩, hkeep⟩, hfw⟩ := hok
    subst hxe
    have hk := Sphincs.SphincsVerify.b110_in_code.trans hp.1 (List.cons_ne_nil _ _)
    have hwf := r.frame_wf hpre hF (fun _ ↦ 0)
    have h11' : (m.regs.getXReg .X11).toBitVec =
        (Sym.ptr 0 ((26769 + 4 * j : Nat) : Int)).eval (r.env m fun _ ↦ 0) := by
      show _ = r.base + BitVec.ofInt 64 ((26769 + 4 * j : Nat) : Int)
      rw [BitVec.ofInt_natCast]
      exact h11
    have hm := r.match_frame hpre hF (vars := fun _ ↦ 0)
      (known := [(.X8, .lit (8 * j)), (.X11, .ptr 0 ((26769 + 4 * j : Nat) : Int)),
        (.X29, .ptr 0 29280)]) (labels := []) (bounds := []) (aliases := [])
      ⟨h8, h11', hF.2.1, trivial⟩ trivial trivial trivial
    refine Sym.exec_then hk hx hwf hm fun st hm' hpc ↦ .done _ ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp only [Sym.PcOk, SBool.eval] at hpc
      rw [hpc]
      by_cases hj1 : j + 1 = 16
      · simp only [hj1, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte]
        simp only [Run.pc, Nat.add_assoc, NativeRustcArm.Sphincs.SphincsVerify.b110_next]
      · simp only [hj1, ↓reduceIte, bne_iff_ne, ne_eq, not_false_eq_true]
        exact label_41 hp
    · exact Run.Frame.of_match r hpre hF hm' hwf hssp hs29 hfw
    · rw [Run.RegIs, hm'.regs .X8 _ hs8, show 8 * (j + 1) = 8 * j + 8 by omega]
      rfl
    · rw [Run.RegIs, hm'.regs .X11 _ hs11]
      show r.base + BitVec.ofInt 64 ((26773 + 4 * j : Nat) : Int) = _
      rw [BitVec.ofInt_natCast, show 26769 + 4 * (j + 1) = 26773 + 4 * j by omega]
      rfl
    · unfold digest128
      rw [hm'.regs .X9 _ hs9, hm'.regs .X10 _ hs10]
      rfl
    · exact Sym.Match.saved hm hm' hwf rfl hkeep
    · refine SameOutside.mono (hm'.sameOutside hwf) fun p hp' ↦
        r.written_inRange hpre (by omega) (fun w hw ↦ ?_) hp'
      rw [hsmem] at hw
      simp only [loopWrites, List.mem_cons, List.not_mem_nil, or_false] at hw
      rcases hw with rfl | rfl | rfl | rfl <;> simp
    · intro t ht
      rw [show r.off (26768 + 4 * j + t) = r.base + BitVec.ofNat 64 (26768 + 4 * j + t) from rfl,
        hm'.mem 0 r.base 29376 rfl (26768 + 4 * j + t) (by omega)]
      simp only [Sym.memByte, hsmem, findWrite_loopWrites j t ht]
      apply congrArg some
      rw [byteOf, Nat.mul_zero, Nat.pow_zero, Nat.div_one,
        eval_digitSym _ (by omega) (by omega),
        show 126 - 8 * j - 2 * t = 126 - 2 * (4 * j + t) by omega]
      rfl

/-- **The loop**: from turn `j` with the digits below `4 j` stored, the machine reaches `b111`
with the 64 digits of `V` at `26768`, the frame's other bytes and the callee-saved registers
kept. -/
theorem loop_run (r : Run) (hp : Placed Sphincs.SphincsVerify.code r.k) (hpre : r.Pre) (V : Nat) :
    ∀ n j, j + n + 1 = 16 → ∀ m : MachineData, r.Frame m →
      Run.RegIs m .X8 (BitVec.ofNat 64 (8 * j)) → Run.RegIs m .X11 (r.off (26769 + 4 * j)) →
      digest128 m = V →
      (∀ t < 4 * j, m.dmem.get? (r.off (26768 + t)) = some (digitByte V t)) →
      Eventually (step1 NativeRustcArm.Host.exe) (fun st ↦ st.pc = r.pc NativeRustcArm.Sphincs.SphincsVerify.b111Offset ∧ r.Frame st.data ∧
        Saved m st.data ∧
        SameOutside m.dmem st.data.dmem (InRange (r.off (26768 + 4 * j)) (64 - 4 * j)) ∧
        ∀ t < 64, st.data.dmem.get? (r.off (26768 + t)) = some (digitByte V t))
      ⟨m, r.pc NativeRustcArm.Sphincs.SphincsVerify.b110Offset⟩ := by
  intro n
  induction n with
  | zero =>
    intro j hj m hF h8 h11 hV hd
    refine Eventually.mono (loop_step r hp hpre (by omega) m hF h8 h11) fun st ⟨hpc, hF', _, _, hV',
      hS, hout, hnew⟩ ↦
      ⟨by rw [hpc, NativeRustcArm.Sym.ite_pos (show j + 1 = 16 by omega)], hF', hS,
      SameOutside.mono hout fun p hp' ↦ by rwa [show 64 - 4 * j = 4 by omega], fun t ht ↦ ?_⟩
    by_cases htj : t < 4 * j
    · rw [hout _ (r.not_inRange_off hpre (by omega) (by omega) (.inl (by omega)))]
      exact hd t htj
    · have := hnew (t - 4 * j) (by omega)
      rwa [show 26768 + 4 * j + (t - 4 * j) = 26768 + t by omega, hV,
        show 4 * j + (t - 4 * j) = t by omega] at this
  | succ n ih =>
    intro j hj m hF h8 h11 hV hd
    refine Eventually.bind (loop_step r hp hpre (by omega) m hF h8 h11) fun st ⟨hpc, hF', h8', h11',
      hV', hS, hout, hnew⟩ ↦ ?_
    rw [NativeRustcArm.Sym.ite_neg (show ¬(j + 1 = 16) by omega)] at hpc
    obtain ⟨m', pc⟩ := st
    simp only at hpc
    subst hpc
    have hd' : ∀ t < 4 * (j + 1), m'.dmem.get? (r.off (26768 + t)) = some (digitByte V t) := by
      intro t ht
      by_cases htj : t < 4 * j
      · rw [hout _ (r.not_inRange_off hpre (by omega) (by omega) (.inl (by omega)))]
        exact hd t htj
      · have := hnew (t - 4 * j) (by omega)
        rwa [show 26768 + 4 * j + (t - 4 * j) = 26768 + t by omega, hV,
          show 4 * j + (t - 4 * j) = t by omega] at this
    refine Eventually.mono (ih (j + 1) (by omega) m' hF' h8' h11' (hV'.trans hV) hd')
      fun st ⟨h1, h2, h3, h4, h5⟩ ↦ ⟨h1, h2, Saved.trans hS h3, ?_, h5⟩
    intro p hp'
    rw [h4 p fun h ↦ hp' ?_, hout p fun h ↦ hp' ?_]
    · rw [r.inRange_off_iff hpre (by omega)] at h ⊢
      omega
    · rw [r.inRange_off_iff hpre (by omega)] at h ⊢
      omega

end

end NativeRustcArm.SphincsVerifyProof
