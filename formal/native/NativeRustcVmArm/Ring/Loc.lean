module

public import NativeRustcVmArm.Ring.Frame

/-!
# Values kept in registers and frame slots across blocks

A function that keeps values in callee-saved registers and in words of its frame (region 0 of
each block's environment) reads them as symbolic values `s` of a small fragment (`isLoc`: a
register, a word of region 0, a literal), evaluated in the frame's environment `envF b F m`
(`locVal`). After a block run from `m` to `m'` (a `Match` in an environment whose region 0 is
the frame), a location the block left alone keeps its value (`locKeep`, `locVal_keep`), one the
block stored `v` into holds `v`'s value (`locSet`, `locVal_set`); both are checked by `decide`
on the block's literal result.
-/

namespace NativeRustcVmArm.Ring

open NativeRustcArm NativeRustcArm.Sym

@[expose] public section

variable [Labels]

/-- The frame's environment: region 0 the `F` bytes from `b`. -/
abbrev envF (b : BitVec 64) (F : Nat) (m : MachineData) : Env := Env.ofMachine m [(b, F)]

/-- A location: a register, a word of region 0, or a literal. -/
def isLoc : Sym → Bool
  | .reg _ => true
  | .lit _ => true
  | .load 0 _ 8 => true
  | _ => false

/-- A location's value in `m`. -/
def locVal (b : BitVec 64) (F : Nat) (m : MachineData) (s : Sym) : UInt64 :=
  UInt64.ofBitVec (s.eval (envF b F m))

/-- The block left the location alone. -/
def locKeep (F : Nat) (S : SState) : Sym → Bool
  | .reg r => S.reg r == some (.reg r)
  | .lit _ => true
  | .load 0 off 8 => decide (off + 8 ≤ F) && (List.range 8).all fun i ↦ findWrite 0 (off + i) S.mem == none
  | _ => false

/-- The block stored `v` into the location. -/
def locSet (F : Nat) (S : SState) (v : Sym) : Sym → Bool
  | .reg r => S.reg r == some v
  | .load 0 off 8 => decide (off + 8 ≤ F) && (List.range 8).all fun i ↦ findWrite 0 (off + i) S.mem == some (v, i)
  | _ => false

/-- A location a call keeps: a callee-saved register, a word of the frame, a literal. -/
def locCS (F : Nat) : Sym → Bool
  | .reg r => calleeSaved r
  | .lit _ => true
  | .load 0 off 8 => decide (off + 8 ≤ F)
  | _ => false

end

public section

/-- No write of the block covers `a`. -/
theorem not_written {env : Env} {S : SState} {a : BitVec 64}
    (h : ∀ w ∈ S.mem, ∀ b sz, env.regions[w.r]? = some (b, sz) →
      b.toNat + w.off + w.n ≤ a.toNat ∨ a.toNat < b.toNat + w.off) : ¬Written env S a := by
  rintro ⟨w, hw, b, sz, hb, h1, h2⟩
  have := h w hw b sz hb
  omega

variable [Labels]

theorem eval_loc {s : Sym} (hs : isLoc s = true) (m : MachineData) (b : BitVec 64) (F : Nat)
    (rs : List (BitVec 64 × Nat)) (vars : Nat → BitVec 64) :
    s.eval (Env.ofMachine m ((b, F) :: rs) vars) = s.eval (envF b F m) := by
  match s, hs with
  | .reg _, _ => rfl
  | .lit _, _ => rfl
  | .load 0 _ 8, _ => rfl

/-- The value a location holds in a state that matches `S'`, in an environment of `m`. -/
theorem locVal_keep {m m' : MachineData} {b : BitVec 64} {F : Nat} {rs : List (BitVec 64 × Nat)}
    {vars : Nat → BitVec 64} {S' : SState}
    (hm : Match (Env.ofMachine m ((b, F) :: rs) vars) S' m')
    {s : Sym} (hk : locKeep F S' s = true) : locVal b F m' s = locVal b F m s := by
  unfold locVal
  congr 1
  match s, hk with
  | .reg r, hk =>
    simp only [locKeep, beq_iff_eq] at hk
    exact hm.regs r _ hk
  | .lit _, _ => rfl
  | .load 0 off 8, hk =>
    simp only [locKeep, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range,
      beq_iff_eq] at hk
    obtain ⟨hle, hw⟩ := hk
    simp only [Sym.eval, Env.load]
    congr 2
    apply List.map_congr_left
    intro i hi
    rw [List.mem_range] at hi
    rw [show (envF b F m').base 0 = b from rfl, show (envF b F m).base 0 = b from rfl,
      show (envF b F m').mem0 = m'.dmem from rfl, hm.mem 0 b F rfl (off + i) (by omega)]
    unfold memByte
    rw [hw i hi]
    rfl

/-- The value a location holds after the block stored `v` into it. -/
theorem locVal_set {m m' : MachineData} {b : BitVec 64} {F : Nat} {rs : List (BitVec 64 × Nat)}
    {vars : Nat → BitVec 64} {S' : SState}
    (hm : Match (Env.ofMachine m ((b, F) :: rs) vars) S' m') {v s : Sym}
    (hk : locSet F S' v s = true) :
    locVal b F m' s = UInt64.ofBitVec (v.eval (Env.ofMachine m ((b, F) :: rs) vars)) := by
  unfold locVal
  congr 1
  match s, hk with
  | .reg r, hk =>
    simp only [locSet, beq_iff_eq] at hk
    exact hm.regs r _ hk
  | .load 0 off 8, hk =>
    simp only [locSet, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range,
      beq_iff_eq] at hk
    obtain ⟨hle, hw⟩ := hk
    simp only [Sym.eval, Env.load]
    have hbytes : ((List.range 8).map fun i ↦
        ((envF b F m').mem0.get? ((envF b F m').base 0 + BitVec.ofNat 64 (off + i))).getD 0) =
        (List.range 8).map fun i ↦ byteOf (v.eval (Env.ofMachine m ((b, F) :: rs) vars)) (0 + i) := by
      apply List.map_congr_left
      intro i hi
      rw [List.mem_range] at hi
      rw [show (envF b F m').base 0 = b from rfl, show (envF b F m').mem0 = m'.dmem from rfl,
        hm.mem 0 b F rfl (off + i) (by omega)]
      unfold memByte
      rw [hw i hi, Nat.zero_add]
      rfl
    rw [hbytes, ofBytes_byteOf, BitVec.ofInt_natCast]
    apply BitVec.eq_of_toNat_eq
    simp only [Nat.mul_zero, Nat.pow_zero, Nat.div_one, BitVec.toNat_ofNat]
    have := (v.eval (Env.ofMachine m ((b, F) :: rs) vars)).isLt
    omega

/-- **A location across a call** that keeps the callee-saved registers and changes memory only
in its stack, below the frame. -/
theorem locVal_call {m0 m m2 : MachineData} {F N' : Nat}
    (hsp : m.regs.SP.toBitVec = base m0 F) (hN : F + N' ≤ m0.regs.SP.toNat)
    (hcs : ∀ r, calleeSaved r = true → m2.regs.getXReg r = m.regs.getXReg r)
    (hs : SameOutside m.dmem m2.dmem fun q ↦ InRange (stackBelow m N') N' q ∨ False)
    {s : Sym} (hl : locCS F s = true) : locVal (base m0 F) F m2 s = locVal (base m0 F) F m s := by
  unfold locVal
  congr 1
  match s, hl with
  | .reg r, hl =>
    simp only [locCS] at hl
    show (m2.regs.getXReg r).toBitVec = (m.regs.getXReg r).toBitVec
    rw [hcs r hl]
  | .lit _, _ => rfl
  | .load 0 off 8, hl =>
    simp only [locCS, decide_eq_true_eq] at hl
    simp only [Sym.eval, Env.load]
    congr 2
    apply List.map_congr_left
    intro i hi
    rw [List.mem_range] at hi
    show (m2.dmem.get? _).getD 0 = (m.dmem.get? _).getD 0
    rw [hs _ ?_]
    · rfl
    rintro (h | h)
    · rw [stackBelow_eq hsp hN] at h
      have hb := base_toNat (m0 := m0) (F := F) (by omega)
      have hb' := base_toNat (m0 := m0) (F := F + N') hN
      have hnw : NoWrap (base m0 (F + N')) N' := by
        unfold NoWrap; rw [hb']; have := m0.regs.SP.toNat_lt; omega
      rw [inRange_iff hnw, hb', show (envF (base m0 F) F m2).base 0 = base m0 F from rfl,
        NativeRustcVm.toNat_add_ofNat (by rw [hb]; have := m0.regs.SP.toNat_lt; omega), hb] at h
      omega
    · exact h

end

end NativeRustcVmArm.Ring
