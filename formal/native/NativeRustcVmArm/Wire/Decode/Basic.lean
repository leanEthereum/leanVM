module

public import NativeRustcVmArm.Wire.Decode.Exec
public import NativeRustcVmArm.Wire.Common
public import NativeRustcVmArm.Ring.Frame
public import NativeRustcVmArm.Spec.Wire
public import NativeRustcVm.Wire.ReaderFacts
public import NativeRustcVm.Transcript.Update
public import NativeVm.Wire.Read

/-!
# `decode`'s places, states and model

The wire's bytes at `bpA` (X0, `Ln` of them), the decoded area at `decA` (X2, `lenW` words), the
working area at `wk` (X4); the frame (`Frm`, 96 bytes, X19 to X24 and X30 in slots, the reader at
its byte 8) in the 1280 bytes of stack the function uses. `Geo`: the places apart, from the
precondition (`geo_of`). What `decode` reaches (`Res`). The model as the code reads it
(`decodeM_eq'`, `phasesM_snoc`, `phasesM_none`), and the arithmetic of the checks.
-/

namespace NativeRustcVmArm.Wire.Decode

open NativeRustcArm NativeRustcArm.Sym NativeRustcVm.Wire NativeVm NativeVm.Wire
open NativeRustcVmArm.Ring (Fr base)
open NativeRustcVm (WordAt WordsAt InAny Region)
open NativeRustcVm.Transcript (DecArea DecodedAt PhaseAt)
open LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.Compile

@[expose] public section

/-- The prologue's slots. -/
def slots : List (Nat × XReg) :=
  [(32, .X30), (48, .X24), (56, .X23), (64, .X22), (72, .X21), (80, .X20), (88, .X19)]

/-- The callee-saved registers `decode` never writes. -/
def keep : List XReg := [.X25, .X26, .X27, .X28, .X29]

/-- The wire bytes' address. -/
abbrev bpA (m0 : MachineData) : BitVec 64 := m0.regs.X0.toBitVec
/-- The wire's byte count. -/
abbrev Ln (m0 : MachineData) : Nat := m0.regs.X1.toNat
/-- The decoded area's address. -/
abbrev decA (m0 : MachineData) : BitVec 64 := m0.regs.X2.toBitVec
/-- The decoded area's word count. -/
abbrev lenW (m0 : MachineData) : Nat := m0.regs.X3.toNat
/-- The working area's address. -/
abbrev wk (m0 : MachineData) : BitVec 64 := m0.regs.X4.toBitVec
/-- The reader's address: byte 8 of the frame. -/
abbrev rdr (m0 : MachineData) : BitVec 64 := base m0 96 + BitVec.ofNat 64 8
/-- Word `i` of the decoded area. -/
abbrev dw (m0 : MachineData) (i : Nat) : BitVec 64 := decA m0 + BitVec.ofNat 64 (8 * i)

/-- The outputs: the decoded area and the working area. -/
abbrev W (m0 : MachineData) (q : BitVec 64) : Prop :=
  InRange (decA m0) (8 * lenW m0) q ∨ InRange (wk m0) workBytes q

/-- The state between the prologue and the epilogue. -/
abbrev Frm (m0 m : MachineData) : Prop := Fr m0 96 1280 slots keep (W m0) m

/-- The environment of the frame. -/
abbrev frEnv (m0 m : MachineData) : Sym.Env := Env.ofMachine m [(base m0 96, 96)]

/-- The environment of the frame and the decoded area's word `i`. -/
abbrev dwEnv (m0 m : MachineData) (i : Nat) : Sym.Env :=
  Env.ofMachine m [(base m0 96, 96), (dw m0 i, 8)]

section
variable [Labels]

/-- The decoded area of the entry. -/
abbrev area (m0 : MachineData) : DecArea := ⟨decA m0, lenW m0, Ln m0⟩

/-- **What `decode` reaches** for the wire bytes `B`. -/
def Res (m0 : MachineData) (B : List UInt8) (st : MachineState) : Prop :=
  st.pc = retOf m0 ∧
    (match decodeM B with
      | some r => st.data.regs.X0 = 1 ∧
          DecodedAt st.data.dmem (area m0) (streamW r.1) (openingsW r.2)
      | none => st.data.regs.X0 = 0) ∧
    SameOutside m0.dmem st.data.dmem
      (InAny [⟨decA m0, 8 * lenW m0⟩, ⟨wk m0, workBytes⟩, stackR m0 decodeStack]) ∧
    Saved m0 st.data

/-- **The places**: the stack, the round constants, the wire's bytes `B`, the decoded area, the
working area, apart (the bytes when there are some). -/
structure Geo (m0 : MachineData) (B : List UInt8) : Prop where
  st : StackOk m0 1280
  rc : NativeRustcVmArm.RcAt m0 1280
  len : B.length = Ln m0
  bytes : BytesAt m0.dmem (bpA m0) B
  l32 : Ln m0 < 2 ^ 32
  dLe : decodedWords (Ln m0) ≤ lenW m0
  bNw : NoWrap (bpA m0) (Ln m0)
  dOk : Region.Ok m0.dmem ⟨decA m0, 8 * lenW m0⟩
  wOk : Region.Ok m0.dmem ⟨wk m0, workBytes⟩
  sC : NativeRustcVm.Apart (base m0 1280) 1280 rcAddr 192
  sD : NativeRustcVm.Apart (base m0 1280) 1280 (decA m0) (8 * lenW m0)
  sW : NativeRustcVm.Apart (base m0 1280) 1280 (wk m0) workBytes
  cD : NativeRustcVm.Apart rcAddr 192 (decA m0) (8 * lenW m0)
  cW : NativeRustcVm.Apart rcAddr 192 (wk m0) workBytes
  dW : NativeRustcVm.Apart (decA m0) (8 * lenW m0) (wk m0) workBytes
  sB : 0 < Ln m0 → NativeRustcVm.Apart (base m0 1280) 1280 (bpA m0) (Ln m0)
  cB : 0 < Ln m0 → NativeRustcVm.Apart rcAddr 192 (bpA m0) (Ln m0)
  bD : 0 < Ln m0 → NativeRustcVm.Apart (bpA m0) (Ln m0) (decA m0) (8 * lenW m0)
  bW : 0 < Ln m0 → NativeRustcVm.Apart (bpA m0) (Ln m0) (wk m0) workBytes

end

/-- The outcome of a read of four bytes at `c`. -/
def Read4 (r bp : BitVec 64) (B : List UInt8) (c : Nat) (m : MachineData) : Prop :=
  match rdU32 B c with
  | some (v, c') => m.regs.X0 = 1 ∧ m.regs.X1.toNat = v ∧ ReaderAt m.dmem r bp B c'
  | none => m.regs.X0 = 0

/-- The stream of `n` elements from the words `ws`. -/
def streamOf (n : Nat) (ws : List K) : List E :=
  (List.range n).map fun i ↦ E.ofLimbs (ws.getD (2 * i) 0) (ws.getD (2 * i + 1) 0)

end

public section

theorem after_eq {ds : List Directive} {S S₁ : SState} {x : Exit} (h : exec ds S = some (S₁, x)) :
    after ds S = S₁ := by
  rw [after, h]

theorem decodeStack_eq : decodeStack = 1280 := rfl
theorem phaseMStack_eq : phaseMStack = 1184 := rfl
theorem phaseBytes_eq : phaseBytes = 395288 := rfl
theorem workBytes_eq : workBytes = 483584 := rfl
theorem phaseWords_eq : phaseWords = 49411 := rfl

/-! ## The model -/

/-- **The model as the code reads it**: the stream's count and words, the phase count, the
phases, the check that no byte is left. -/
theorem decodeM_eq' (B : List UInt8) : decodeM B =
    match rdU32 B 0 with
    | none => none
    | some (n, c0) => match rdWords B (2 * n) c0 with
      | none => none
      | some (ws, c1) => match rdU32 B c1 with
        | none => none
        | some (p, cs) => if wireMaxPhases < p then none else
          match phasesM B p cs with
          | none => none
          | some (ps, c) => if c ≠ B.length then none else some (streamOf n ws, ps) := by
  unfold decodeM streamM streamOf
  cases h1 : rdU32 B 0 with
  | none => simp
  | some q =>
  obtain ⟨n, c0⟩ := q
  cases h2 : rdWords B (2 * n) c0 with
  | none => simp [h2]
  | some q =>
  obtain ⟨ws, c1⟩ := q
  cases h3 : rdU32 B c1 with
  | none => simp [h2, h3]
  | some q =>
  obtain ⟨p, cs⟩ := q
  by_cases hp : wireMaxPhases < p
  · simp [h2, h3, hp]
  cases h4 : phasesM B p cs with
  | none => simp [h2, h3, hp, h4]
  | some q =>
  obtain ⟨ps, c⟩ := q
  simp [h2, h3, hp, h4]

/-- One more phase after `k`. -/
theorem phasesM_snoc (B : List UInt8) (k : Nat) : ∀ {c c1 c2 : Nat} {ps : List PhaseOut}
    {p : PhaseOut}, phasesM B k c = some (ps, c1) → phaseM B c1 = some (p, c2) →
      phasesM B (k + 1) c = some (ps ++ [p], c2) := by
  induction k with
  | zero =>
    intro c c1 c2 ps p h hp
    simp only [phasesM, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    simp [phasesM, hp]
  | succ k ih =>
    intro c c1 c2 ps p h hp
    rw [phasesM.eq_2] at h ⊢
    simp only [Option.bind_eq_bind] at h ⊢
    cases h1 : phaseM B c with
    | none => simp [h1] at h
    | some q =>
      obtain ⟨a, c3⟩ := q
      simp only [h1, Option.bind_some] at h ⊢
      cases h2 : phasesM B k c3 with
      | none => simp [h2] at h
      | some q =>
        obtain ⟨ps', c4⟩ := q
        simp only [h2, Option.bind_some, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        rw [ih h2 hp]
        rfl

/-- A phase failing after `k` fails every longer run. -/
theorem phasesM_none (B : List UInt8) (k : Nat) : ∀ {c c1 m : Nat} {ps : List PhaseOut},
    phasesM B k c = some (ps, c1) → phaseM B c1 = none → phasesM B (k + m + 1) c = none := by
  induction k with
  | zero =>
    intro c c1 m ps h hp
    simp only [phasesM, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    rw [Nat.zero_add]
    simp [phasesM, hp]
  | succ k ih =>
    intro c c1 m ps h hp
    rw [show k + 1 + m + 1 = (k + m + 1) + 1 by omega, phasesM.eq_2]
    rw [phasesM.eq_2] at h
    simp only [Option.bind_eq_bind] at h ⊢
    cases h1 : phaseM B c with
    | none => simp
    | some q =>
      obtain ⟨a, c2⟩ := q
      simp only [h1, Option.bind_some] at h ⊢
      cases h2 : phasesM B k c2 with
      | none => simp [h2] at h
      | some q =>
        obtain ⟨ps', c3⟩ := q
        simp only [h2, Option.bind_some, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        rw [ih h2 hp]
        rfl

theorem phasesM_length (B : List UInt8) : ∀ (k c : Nat) {ps : List PhaseOut} {c' : Nat},
    phasesM B k c = some (ps, c') → ps.length = k
  | 0, c, ps, c', h => by
    simp only [phasesM, Option.some.injEq, Prod.mk.injEq] at h
    rw [← h.1]; rfl
  | k + 1, c, ps, c', h => by
    rw [phasesM.eq_2] at h
    simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at h
    obtain ⟨⟨a, c1⟩, -, ⟨ps', c2⟩, h2, he⟩ := h
    cases he
    simp [phasesM_length B k c1 h2]

/-- A 4-byte read of `Reader::le` is `rdU32`'s. -/
theorem rdLe_four (B : List UInt8) (c : Nat) :
    rdLe B c 4 = (rdU32 B c).map fun p ↦ (p.1.toUInt64, p.2) := by
  unfold rdLe rdU32
  split <;> rfl

theorem rdU32_c {B : List UInt8} {c v c' : Nat} (h : rdU32 B c = some (v, c')) :
    c' = c + 4 ∧ c + 4 ≤ B.length := by
  unfold rdU32 at h
  split at h
  · cases h; exact ⟨rfl, by assumption⟩
  · cases h

theorem rdWords_c {B : List UInt8} {n c : Nat} {ws : List K} {c' : Nat}
    (h : rdWords B n c = some (ws, c')) : c' = c + 8 * n ∧ c + 8 * n ≤ B.length ∧
      ws = (List.range n).map fun i ↦ K.ofLane (leAt B (c + 8 * i) 8) := by
  unfold rdWords at h
  split at h
  · cases h; exact ⟨rfl, by assumption, rfl⟩
  · cases h

/-! ## Bytes in memory -/

/-- Mapped memory holds bytes. -/
theorem exists_bytesAt {d : Mem 64} {a : BitVec 64} {n : Nat} (h : NativeRustcVm.Mapped d a n) :
    ∃ B : List UInt8, B.length = n ∧ BytesAt d a B := by
  refine ⟨(List.range n).map fun i ↦ (d.get? (a + BitVec.ofNat 64 i)).getD 0, by simp,
    fun i hi ↦ ?_⟩
  simp only [List.length_map, List.length_range] at hi
  simp only [List.getElem_map, List.getElem_range]
  have := h i hi
  rcases hd : d.get? (a + BitVec.ofNat 64 i) with _ | b
  · rw [hd] at this; cases this
  · rfl

/-! ## Arithmetic -/

theorem lor_one (y : Nat) : y ||| 1 = 2 * (y / 2) + 1 := by
  have h1 : 2 * (y / 2) ||| 1 = 2 * (y / 2) + 1 := by
    rw [Nat.or_comm, NativeRustc.lor_eq_add (n := 1) (by norm_num) (by simp)]
    omega
  rcases Nat.mod_two_eq_zero_or_one y with h | h
  · rw [show y = 2 * (y / 2) by omega] at ⊢
    rw [h1]
    omega
  · conv_lhs => rw [show y = 2 * (y / 2) + 1 by omega, ← h1, Nat.or_assoc, Nat.or_self]
    exact h1

theorem lsr_toNat (x : BitVec 64) {k : Nat} (hk : k < 64) :
    (UnOp.apply (.ubfm k 63) .W64 x).toNat = x.toNat / 2 ^ k := by
  have hb : RegWidth.W64.bits = 64 := rfl
  simp only [UnOp.apply, Sym.low_W64, Sym.ext_W64, evalUBFM, hb, Nat.mod_eq_of_lt hk,
    show 63 % 64 = 63 from rfl, show 63 ≥ k from by omega, ↓reduceIte, BitVec.toNat_setWidth,
    BitVec.take, BitVec.extractLsb'_toNat, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
  have := x.isLt
  have h1 : x.toNat / 2 ^ k < 2 ^ (63 - k + 1) := by
    rw [Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _), ← Nat.pow_add, show 63 - k + 1 + k = 64 by omega]
    exact x.isLt
  have h2 : 2 ^ (63 - k + 1) ≤ 2 ^ 64 := Nat.pow_le_pow_right (by omega) (by omega)
  simp only [Nat.pow_zero, Nat.div_one]
  rw [Nat.mod_eq_of_lt h1, Nat.mod_eq_of_lt (by omega)]

theorem lsl1_toNat (x : BitVec 64) :
    (UnOp.apply (.ubfm 63 62) .W64 x).toNat = 2 * x.toNat % 2 ^ 64 := by
  simp only [UnOp.apply, Sym.ext_W64, Sym.low_W64]
  simp [evalUBFM, toNat_take', BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]
  omega

theorem umulh_toNat (a b : BitVec 64) :
    (BinOp.apply .umulh .W64 a b).toNat = a.toNat * b.toNat / 2 ^ 64 := by
  have ha := a.isLt
  have hb := b.isLt
  simp only [BinOp.apply, Sym.low_W64, Sym.ext_W64, BitVec.extractLsb'_toNat, BitVec.toNat_ofInt,
    BitVec.unsigned]
  have hab : a.toNat * b.toNat < 2 ^ 128 := by
    have := Nat.mul_lt_mul'' ha hb
    simpa using this
  rw [show ((a.toNat : Int) * (b.toNat : Int)) = ((a.toNat * b.toNat : Nat) : Int) by
    push_cast; rfl]
  have hw : RegWidth.W64.bits = 64 := rfl
  rw [hw, Nat.shiftRight_eq_div_pow]
  omega

theorem toNat_add_lit {x : BitVec 64} {c : Nat} (h : x.toNat + c < 2 ^ 64) (hc : c < 2 ^ 64) :
    (BinOp.apply .add .W64 x (BitVec.ofNat 64 c)).toNat = x.toNat + c := by
  simp only [BinOp.apply, Sym.low_W64, Sym.ext_W64, BitVec.toNat_add, BitVec.toNat_ofNat]
  omega

theorem toNat_sub_lit {x : BitVec 64} {c : Nat} (h : c ≤ x.toNat) (hc : c < 2 ^ 64) :
    (BinOp.apply .sub .W64 x (BitVec.ofNat 64 c)).toNat = x.toNat - c := by
  simp only [BinOp.apply, Sym.low_W64, Sym.ext_W64, BitVec.toNat_sub, BitVec.toNat_ofNat]
  have := x.isLt
  omega

/-- The stream's end: `lsr #3` then `orr #1` of the byte count. -/
theorem streamEnd_eval (x : BitVec 64) :
    (BinOp.apply .orr .W64 (UnOp.apply (.ubfm 3 63) .W64 x) (BitVec.ofNat 64 1)).toNat =
      streamEnd x.toNat := by
  simp only [BinOp.apply, Sym.low_W64, Sym.ext_W64, BitVec.toNat_or, BitVec.toNat_ofNat]
  rw [lsr_toNat x (by omega), lor_one]
  unfold streamEnd maxStream
  omega

/-- `x ↦ x / 49411` as rustc computes it, at least `8` from `8 · 49411`. -/
theorem magic_ge (x y : Nat) (hx : 395288 ≤ x)
    (hy : x * 6019990451287497113 < (y + 1) * 18446744073709551616) :
    8 ≤ (y + (x - y) / 2) / 32768 := by
  omega

theorem umulh_magic (x : BitVec 64) :
    x.toNat * 6019990451287497113 < ((BinOp.apply .umulh .W64 x
      (BitVec.ofNat 64 6019990451287497113)).toNat + 1) * 18446744073709551616 := by
  rw [umulh_toNat, BitVec.toNat_ofNat]
  have h : 6019990451287497113 % 2 ^ 64 = 6019990451287497113 := by norm_num
  rw [h]
  omega

theorem lsr1_toNat (x : BitVec 64) : (UnOp.apply (.shift .LSR 1) .W64 x).toNat = x.toNat / 2 := by
  simp only [UnOp.apply, Sym.low_W64, Sym.ext_W64, shiftW]
  show (x >>> 1).toNat = _
  rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]

theorem add_toNat (x y : BitVec 64) :
    (BinOp.apply .add .W64 x y).toNat = (x.toNat + y.toNat) % 2 ^ 64 := by
  simp only [BinOp.apply, Sym.low_W64, Sym.ext_W64, BitVec.toNat_add]

theorem sub_toNat (x y : BitVec 64) :
    (BinOp.apply .sub .W64 x y).toNat = (2 ^ 64 - y.toNat + x.toNat) % 2 ^ 64 := by
  simp only [BinOp.apply, Sym.low_W64, Sym.ext_W64, BitVec.toNat_sub]

theorem add_orn_toNat (a b : BitVec 64) (h : b.toNat < a.toNat) :
    (BinOp.apply .add .W64 a (BinOp.apply .orn .W64 (BitVec.ofNat 64 0) b)).toNat =
      a.toNat - b.toNat - 1 := by
  have ha := a.isLt
  simp only [BinOp.apply, Sym.low_W64, Sym.ext_W64, BitVec.toNat_add, BitVec.toNat_or,
    BitVec.toNat_not, BitVec.toNat_ofNat, Nat.zero_mod, Nat.zero_or]
  omega

/-- The phases that fit after the stream's end `b` in `a` words: at least eight, plus one. -/
theorem slots_ge {a b : BitVec 64} (h : b.toNat + 1 + 8 * phaseWords ≤ a.toNat) :
    9 ≤ (BinOp.apply .add .W64 (UnOp.apply (.ubfm 15 63) .W64
      (BinOp.apply .add .W64
        (BinOp.apply .umulh .W64 (BinOp.apply .add .W64 a
          (BinOp.apply .orn .W64 (BitVec.ofNat 64 0) b)) (BitVec.ofNat 64 6019990451287497113))
        (UnOp.apply (.shift .LSR 1) .W64 (BinOp.apply .sub .W64
          (BinOp.apply .add .W64 a (BinOp.apply .orn .W64 (BitVec.ofNat 64 0) b))
          (BinOp.apply .umulh .W64 (BinOp.apply .add .W64 a
            (BinOp.apply .orn .W64 (BitVec.ofNat 64 0) b))
            (BitVec.ofNat 64 6019990451287497113))))))
      (BitVec.ofNat 64 1)).toNat := by
  rw [phaseWords_eq] at h
  have hx := add_orn_toNat a b (by omega)
  generalize BinOp.apply .add .W64 a (BinOp.apply .orn .W64 (BitVec.ofNat 64 0) b) = x at hx ⊢
  have hh := umulh_magic x
  have hh' := umulh_toNat x (BitVec.ofNat 64 6019990451287497113)
  generalize BinOp.apply .umulh .W64 x (BitVec.ofNat 64 6019990451287497113) = y at hh hh' ⊢
  have hxl := x.isLt
  have hyl := y.isLt
  have hyx : y.toNat ≤ x.toNat := by
    rw [hh', BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (show 6019990451287497113 < 2 ^ 64 by norm_num)]
    apply Nat.div_le_of_le_mul
    omega
  have hs := sub_toNat x y
  have hr := lsr1_toNat (BinOp.apply .sub .W64 x y)
  rw [hs, show (2 ^ 64 - y.toNat + x.toNat) % 2 ^ 64 = x.toNat - y.toNat by omega] at hr
  generalize UnOp.apply (.shift .LSR 1) .W64 (BinOp.apply .sub .W64 x y) = z at hr ⊢
  have hq := add_toNat y z
  rw [hr, Nat.mod_eq_of_lt (by omega)] at hq
  generalize BinOp.apply .add .W64 y z = u at hq ⊢
  have hm := magic_ge x.toNat y.toNat (by omega) hh
  rw [toNat_add_lit (by rw [lsr_toNat _ (by omega), hq]; omega) (by omega),
    lsr_toNat _ (by omega), hq]
  omega

end

end NativeRustcVmArm.Wire.Decode
