module

public import NativeRustcX64.Code.Sphincs.SphincsVerify.Names

public import NativeRustcX64.SphincsVerify.Encode.Hash
meta import NativeRustcX64.Code.Sphincs.SphincsVerify.Part2
meta import NativeRustcX64.SphincsVerify.Frame

/-!
# The codeword's loop `b104`

`b104` (`.LSphincsVerify_39`) runs 32 turns, turn `j` (RDI `4 j`, RSI the frame's
`561 + 2 j`) writing the digits `2 j`, `2 j + 1` of the 128-bit digest `rax · 2⁶⁴ + rdx` to
`560 + 2 j ..` (`loopWrites`, the digit at bit `s` as `byteS s`), over the digest. The executor's
result for each turn is checked by the kernel once (`loopOk_all`); `loop_step` reads one turn off
it, `loop_run` runs the turns: the 64 digits `digitByte V` at `560`, the rest of the frame kept.
-/

namespace NativeRustcX64.SphincsVerifyProof

open NativeRustc NativeRustc.Sphincs NativeRustcX64.Sym

@[expose] public section

set_option Elab.async false

/-- The word the loop takes the digit at bit `s` from: `rax >> s` or `shrd rdx, rax, s`. -/
def wordS (s : Nat) : Sym :=
  if 64 ≤ s then .bin .shr .W64 (.reg .rax) (.lit s)
  else .tern .shrd .W64 (.reg .rdx) (.reg .rax) (.lit s)

/-- The digit at bit `s`, as the loop stores it. -/
def byteS (s : Nat) : Sym :=
  .un .trunc .W8 (.bin .merge .W8 (wordS s) (.bin .and .W8 (wordS s) (.lit 3)))

/-- Turn `j`'s writes: the digits `2 j + 1`, `2 j`. -/
def loopWrites (j : Nat) : List Write :=
  [⟨0, 560 + 2 * j + 1, 1, byteS (124 - 4 * j)⟩, ⟨0, 560 + 2 * j, 1, byteS (126 - 4 * j)⟩]

/-- Turn `j`'s symbolic state. -/
def loopInit (j : Nat) : SState :=
  Run.frameState
    [(.rdi, .lit (4 * j)), (.rsi, .ptr 0 ((561 + 2 * j : Nat) : Int))]

/-- Turn `j` as the executor runs it: back to the loop's head unless last, RDI and RSI on, RAX,
RDX, RSP and the callee-saved registers kept, the two digits written. -/
def loopOk (j : Nat) : Bool :=
  match exec Sphincs.SphincsVerify.b104 (loopInit j) with
  | some (S, x) => x == .cond (.lit (j + 1 != 32)) NativeRustcX64.Sphincs.SphincsVerify.label_31 &&
      S.reg .rdi == some (.lit (4 * j + 4)) &&
      S.reg .rsi == some (.ptr 0 ((563 + 2 * j : Nat) : Int)) &&
      S.reg .rax == some (.reg .rax) && S.reg .rdx == some (.reg .rdx) &&
      S.reg .rsp == some (.ptr 0 0) && S.mem == loopWrites j && keeps (loopInit j) S &&
      Run.frameWrites S
  | none => false

theorem loopOk_all : ∀ j < 32, loopOk j = true := by decide +kernel

/-! ## The digits -/

/-- **A digit's value**: bits `s, s + 1` of `rax · 2⁶⁴ + rdx`. -/
theorem eval_byteS [Labels] (env : Env) {s : Nat} (hs : s < 128) :
    ((byteS s).eval env).toNat =
      ((env.regs .rax).toNat * 2 ^ 64 + (env.regs .rdx).toNat) >>> s % 4 := by
  unfold byteS
  simp only [Sym.eval]
  rw [byte3]
  unfold wordS
  split
  · simp only [Sym.eval]
    exact digit_hi _ (env.regs .rdx).isLt (by omega) hs
  · simp only [Sym.eval]
    by_cases h0 : s = 0
    · subst h0
      exact digit_zero _ _
    · exact digit_lo _ _ (by omega) (by omega)

theorem findWrite_loopWrites (j t : Nat) (ht : t < 2) :
    findWrite 0 (560 + 2 * j + t) (loopWrites j) = some (byteS (126 - 4 * j - 2 * t), 0) := by
  interval_cases t
  · simp [findWrite, loopWrites]
  · simp only [findWrite, loopWrites, Nat.mul_one]
    rw [show 126 - 4 * j - 2 = 124 - 4 * j by omega]
    simp

/-! ## Frame facts -/

namespace Run

variable (r : Run) [Labels]

/-- The frame's bytes `a .. a + n` as addresses. -/
theorem inRange_off_iff (hpre : r.Pre) {a n : Nat} (h : a + n ≤ 21624) (p : BitVec 64) :
    InRange (r.off a) n p ↔ r.base.toNat + a ≤ p.toNat ∧ p.toNat < r.base.toNat + a + n := by
  have hb := r.base_toNat hpre
  rw [Sym.inRange_iff (by rw [r.off_toNat hpre (by omega)]; omega), r.off_toNat hpre (by omega)]

/-- **A block's writes inside the frame's bytes `o .. o + n`** change only those. -/
theorem written_inRange (hpre : r.Pre) {m : MachineData} {vars : Nat → BitVec 64}
    {ret : BitVec 64} {S : SState} {o n : Nat} (hon : o + n ≤ 21624)
    (hS : ∀ w ∈ S.mem, w.r = 0 ∧ o ≤ w.off ∧ w.off + w.n ≤ o + n) {p : BitVec 64}
    (hp : Written (r.env m vars ret) S p) : InRange (r.off o) n p := by
  obtain ⟨w, hw, b, sz, hb, h1, h2⟩ := hp
  obtain ⟨hr, ho, hn⟩ := hS w hw
  rw [hr] at hb
  cases hb
  rw [r.inRange_off_iff hpre hon]
  omega

end Run

/-! ## A turn -/

theorem label_31 [ElfHost] {sec k : Nat} (hp : PlacedIn Sphincs.SphincsVerify.code sec k) :
    Labels.label NativeRustcX64.Sphincs.SphincsVerify.label_31 = ElfHost.addrOf sec (k + NativeRustcX64.Sphincs.SphincsVerify.b104Offset) :=
  hp.label NativeRustcX64.Sphincs.SphincsVerify.label_31_at


variable [ElfHost]

/-- **A turn of the loop**: turn `j` writes the digits `2 j`, `2 j + 1` at `560 + 2 j`, and goes
back to the loop's head, or on to `b105` after the last. -/
theorem loop_step (r : Run) (hp : PlacedIn Sphincs.SphincsVerify.code r.sec r.k) (hpre : r.Pre) {j : Nat}
    (hj : j < 32) (m : MachineData) (hF : r.Frame m)
    (h7 : Run.RegIs m .rdi (BitVec.ofNat 64 (4 * j)))
    (h6 : Run.RegIs m .rsi (r.off (561 + 2 * j))) :
    Eventually (elfStep1 ElfHost.exe) (fun st ↦
      st.pc = (if j + 1 = 32 then r.pc NativeRustcX64.Sphincs.SphincsVerify.b105Offset else r.pc NativeRustcX64.Sphincs.SphincsVerify.b104Offset) ∧ r.Frame st.data ∧
      Run.RegIs st.data .rdi (BitVec.ofNat 64 (4 * (j + 1))) ∧
      Run.RegIs st.data .rsi (r.off (561 + 2 * (j + 1))) ∧ digest128 st.data = digest128 m ∧
      Saved m st.data ∧ SameOutside m.dmem st.data.dmem (InRange (r.off (560 + 2 * j)) 2) ∧
      ∀ t < 2, st.data.dmem.get? (r.off (560 + 2 * j + t)) =
        some (UInt8.ofNat (digest128 m >>> (126 - 2 * (2 * j + t)) % 4)))
      ⟨m, r.pc NativeRustcX64.Sphincs.SphincsVerify.b104Offset⟩ := by
  have hok := loopOk_all j hj
  rw [loopOk] at hok
  rcases hx : exec Sphincs.SphincsVerify.b104 (loopInit j) with _ | ⟨S, x⟩
  · rw [hx] at hok
    exact absurd hok Bool.false_ne_true
  rw [hx] at hok
  simp only [Bool.and_eq_true, beq_iff_eq] at hok
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨hxe, hs7⟩, hs6⟩, hsax⟩, hsdx⟩, hssp⟩, hsmem⟩, hkeep⟩, hfw⟩ := hok
  subst hxe
  have hk := Sphincs.SphincsVerify.b104_in_code.trans hp.1 (List.cons_ne_nil _ _)
  have hwf := r.frame_wf hpre hF.2.2.2 (fun _ ↦ 0) 0
  have hm := r.match_frame hpre hF (vars := fun _ ↦ 0) (ret := 0)
    (known := [(.rdi, .lit (4 * j)), (.rsi, .ptr 0 ((561 + 2 * j : Nat) : Int))]) (labels := [])
    (bounds := []) (aliases := []) ⟨h7, h6.trans (r.ptr_eval m _ _ _).symm, trivial⟩ trivial
    trivial trivial
  refine Sym.exec_then_elf hk hx hwf (fun _ h ↦ by cases h) hm fun st hm' hpc ↦
    .done _ ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [Sym.PcOk, SBool.eval] at hpc
    rw [hpc]
    by_cases hj1 : j + 1 = 32
    · simp only [hj1, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte]
      simp only [Run.pc, Nat.add_assoc, NativeRustcX64.Sphincs.SphincsVerify.b104_next]
    · simp only [hj1, ↓reduceIte, bne_iff_ne, ne_eq, not_false_eq_true]
      exact label_31 hp
  · exact Run.Frame.of_match r hpre hF hm' hwf hssp hfw
  · rw [Run.RegIs, show reg st.data .rdi = _ from hm'.regs .rdi _ hs7,
      show 4 * (j + 1) = 4 * j + 4 by omega]
    rfl
  · rw [Run.RegIs, show reg st.data .rsi = _ from hm'.regs .rsi _ hs6,
      show 561 + 2 * (j + 1) = 563 + 2 * j by omega]
    exact r.ptr_eval _ _ _ _
  · unfold digest128
    rw [show reg st.data .rax = _ from hm'.regs .rax _ hsax,
      show reg st.data .rdx = _ from hm'.regs .rdx _ hsdx]
    rfl
  · exact Sym.Match.saved hm hm' hwf rfl hkeep
  · refine SameOutside.mono (hm'.sameOutside hwf) fun p hp' ↦
      r.written_inRange hpre (by omega) (fun w hw ↦ ?_) hp'
    rw [hsmem] at hw
    simp only [loopWrites, List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases hw with rfl | rfl <;> simp
  · intro t ht
    rw [show r.off (560 + 2 * j + t) = r.base + BitVec.ofNat 64 (560 + 2 * j + t) from rfl,
      hm'.mem 0 r.base frameRegion rfl (560 + 2 * j + t) (by rw [Run.frameRegion_eq]; omega)]
    simp only [Sym.memByte, hsmem, findWrite_loopWrites j t ht]
    apply congrArg some
    unfold byteOf
    rw [Nat.mul_zero, Nat.pow_zero, Nat.div_one, eval_byteS _ (by omega),
      show 126 - 4 * j - 2 * t = 126 - 2 * (2 * j + t) by omega]
    rfl

/-- **The loop**: from turn `j` with the digits below `2 j` stored, the machine reaches `b105`
with the 64 digits of `V` at `560`, the frame's other bytes and the callee-saved registers
kept. -/
theorem loop_run (r : Run) (hp : PlacedIn Sphincs.SphincsVerify.code r.sec r.k) (hpre : r.Pre) (V : Nat) :
    ∀ n j, j + n + 1 = 32 → ∀ m : MachineData, r.Frame m →
      Run.RegIs m .rdi (BitVec.ofNat 64 (4 * j)) → Run.RegIs m .rsi (r.off (561 + 2 * j)) →
      digest128 m = V →
      (∀ t < 2 * j, m.dmem.get? (r.off (560 + t)) = some (digitByte V t)) →
      Eventually (elfStep1 ElfHost.exe) (fun st ↦ st.pc = r.pc NativeRustcX64.Sphincs.SphincsVerify.b105Offset ∧ r.Frame st.data ∧
        Saved m st.data ∧
        SameOutside m.dmem st.data.dmem (InRange (r.off (560 + 2 * j)) (64 - 2 * j)) ∧
        ∀ t < 64, st.data.dmem.get? (r.off (560 + t)) = some (digitByte V t))
      ⟨m, r.pc NativeRustcX64.Sphincs.SphincsVerify.b104Offset⟩ := by
  intro n
  induction n with
  | zero =>
    intro j hj m hF h7 h6 hV hd
    refine Eventually.mono_elf (loop_step r hp hpre (by omega) m hF h7 h6) fun st ⟨hpc, hF', _, _, hV',
      hS, hout, hnew⟩ ↦ ⟨by rw [hpc, Sym.ite_pos (show j + 1 = 32 by omega)], hF', hS,
      SameOutside.mono hout fun p hp' ↦ by rwa [show 64 - 2 * j = 2 by omega], fun t ht ↦ ?_⟩
    by_cases htj : t < 2 * j
    · rw [hout _ (r.not_inRange_off hpre (by omega) (by omega) (.inl (by omega)))]
      exact hd t htj
    · have := hnew (t - 2 * j) (by omega)
      rwa [show 560 + 2 * j + (t - 2 * j) = 560 + t by omega, hV,
        show 2 * j + (t - 2 * j) = t by omega] at this
  | succ n ih =>
    intro j hj m hF h7 h6 hV hd
    refine Eventually.bind_elf (loop_step r hp hpre (by omega) m hF h7 h6) fun st ⟨hpc, hF', h7', h6',
      hV', hS, hout, hnew⟩ ↦ ?_
    rw [Sym.ite_neg (show ¬(j + 1 = 32) by omega)] at hpc
    obtain ⟨m', pc⟩ := st
    simp only at hpc
    subst hpc
    have hd' : ∀ t < 2 * (j + 1), m'.dmem.get? (r.off (560 + t)) = some (digitByte V t) := by
      intro t ht
      by_cases htj : t < 2 * j
      · rw [hout _ (r.not_inRange_off hpre (by omega) (by omega) (.inl (by omega)))]
        exact hd t htj
      · have := hnew (t - 2 * j) (by omega)
        rwa [show 560 + 2 * j + (t - 2 * j) = 560 + t by omega, hV,
          show 2 * j + (t - 2 * j) = t by omega] at this
    refine Eventually.mono_elf (ih (j + 1) (by omega) m' hF' h7' h6' (hV'.trans hV) hd')
      fun st ⟨h1, h2, h3, h4, h5⟩ ↦ ⟨h1, h2, Saved.trans hS h3, ?_, h5⟩
    intro p hp'
    rw [h4 p fun h ↦ hp' ?_, hout p fun h ↦ hp' ?_]
    · rw [r.inRange_off_iff hpre (by omega)] at h ⊢
      omega
    · rw [r.inRange_off_iff hpre (by omega)] at h ⊢
      omega

end

end NativeRustcX64.SphincsVerifyProof
