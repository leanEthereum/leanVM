module

public import NativeRustcArm.Sym
public import NativeRustcArm.Hasher.Bytes
public import NativeRustcVm.MemLemmas
public import NativeRustcVm.Arrays.Read

/-!
# A function's frame between its calls

From the entry state `m0` of a function that keeps its frame in the `F` bytes below the entry's SP
(`base m0 F`) and uses `N` bytes of stack in all: what every state between its prologue and its
epilogue keeps (`Fr`): SP at the frame's base, the callee-saved registers `keep` the prologue did
not save, the registers `slots` saved at their offsets in the frame, memory as `m0`'s but in the
stack and the outputs `outs`, every mapped byte.

- `Fr.ofPrologue`: after a prologue block whose writes are the frame's (`slotsOk`).
- `Fr.step`: after a block or a call that keeps SP and `keep`, and writes neither the slots nor
  outside the stack and the outputs; `Fr.call` for a callee with `N'` bytes of stack.
- `Fr.stackOk`, `Fr.apart`: a callee's `StackOk`, an argument apart from its stack.
- `Fr.exit`: after the epilogue (`exitOk`): `retOf` and `Saved` of the entry's.
- `load_word`: a word in memory is what the environment loads.
-/

namespace NativeRustcVmArm.Ring

open NativeRustcArm NativeRustcArm.Sym

@[expose] public section

/-- The entry's SP minus `F`. -/
def base (m0 : MachineData) (F : Nat) : BitVec 64 := m0.regs.SP.toBitVec - BitVec.ofNat 64 F

/-- **Between the prologue and the epilogue.** -/
structure Fr (m0 : MachineData) (F N : Nat) (slots : List (Nat × XReg)) (keep : List XReg)
    (outs : BitVec 64 → Prop) (m : MachineData) : Prop where
  sp : m.regs.SP.toBitVec = base m0 F
  keep : ∀ r ∈ keep, m.regs.getXReg r = m0.regs.getXReg r
  slots : ∀ p ∈ slots,
    NativeRustcVm.WordAt m.dmem (base m0 F + BitVec.ofNat 64 p.1) (m0.regs.getXReg p.2)
  same : SameOutside m0.dmem m.dmem (fun q ↦ InRange (base m0 N) N q ∨ outs q)
  kept : Kept m0.dmem m.dmem

/-- The prologue's writes are the slots: register `r`'s eight bytes at offset `o` of region 0. -/
def slotsOk (S : SState) (slots : List (Nat × XReg)) : Bool :=
  slots.all fun p ↦ (List.range 8).all fun i ↦ findWrite 0 (p.1 + i) S.mem == some (.reg p.2, i)

/-- The epilogue restores SP (region 0's end, `F`) and each callee-saved register and X30: from
its slot, or kept. -/
def exitOk (S : SState) (F : Nat) (slots : List (Nat × XReg)) (keep : List XReg) : Bool :=
  allXRegs.all (fun r ↦ (!calleeSaved r && r != .X30) ||
      slots.any (fun p ↦ p.2 == r && S.reg r == some (.load 0 p.1 8)) ||
      (keep.contains r && S.reg r == some (.reg r))) &&
    S.sp == .ptr 0 F

end

public section

/-! ## Words -/

theorem ofInt_ofBytes_wordBytes (v : UInt64) :
    BitVec.ofInt 64 (Int.ofBytes (NativeRustcVm.wordBytes v)) = v.toBitVec := by
  have hw := Hasher.wordBytes_ofBitVec v.toBitVec
  have hb := Sym.ofBytes_byteOf v.toBitVec 0 8
  simp only [Nat.zero_add] at hb
  rw [show UInt64.ofBitVec v.toBitVec = v from rfl] at hw
  rw [show NativeRustcVm.wordBytes v = LeanVM.Protocol.KeccakHash.wordBytes v from rfl, hw, hb,
    BitVec.ofInt_natCast]
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ofNat]
  have := v.toBitVec.isLt
  simp only [Nat.mul_zero, Nat.pow_zero, Nat.div_one]
  omega

/-- **A word at a region's offset** is what the environment loads there. -/
theorem load_word {env : Env} {r off : Nat} {v : UInt64}
    (h : NativeRustcVm.WordAt env.mem0 (env.base r + BitVec.ofNat 64 off) v) :
    env.load r off 8 = v.toBitVec := by
  rw [Env.load_of_bytesAt (NativeRustcVm.length_wordBytes v) h, ofInt_ofBytes_wordBytes]

/-- A register's eight bytes, as the executor writes them, are its word. -/
theorem wordBytes_reg (x : BitVec 64) :
    (List.range 8).map (byteOf x) = NativeRustcVm.wordBytes (UInt64.ofBitVec x) :=
  (Hasher.wordBytes_ofBitVec x).symm

theorem ofBytes_eq_leNat : ∀ bs : List UInt8, Nat.ofBytes bs = NativeRustcVm.leNat bs
  | [] => rfl
  | b :: bs => by
    show Nat.ofBytes bs * 256 + b.toNat = b.toNat + 256 * NativeRustcVm.leNat bs
    rw [ofBytes_eq_leNat bs]
    omega

/-- **An environment's load of eight bytes** is the word `wordOf` reads there. -/
theorem load_eq_wordOf (env : Env) (r off : Nat) :
    env.load r off 8 = (NativeRustcVm.wordOf env.mem0 (env.base r + BitVec.ofNat 64 off)).toBitVec := by
  unfold Env.load NativeRustcVm.wordOf NativeRustcVm.bytesFrom
  rw [ofBytes_natCast, BitVec.ofInt_natCast, ofBytes_eq_leNat]
  show BitVec.ofNat 64 _ = BitVec.ofNat 64 _
  congr 2
  apply List.map_congr_left
  intro i _
  rw [NativeRustcVm.addr_add_add]

/-! ## Addresses -/

section
variable {m0 : MachineData} {F N : Nat}

theorem base_toNat (h : F ≤ m0.regs.SP.toNat) : (base m0 F).toNat = m0.regs.SP.toNat - F :=
  NativeRustcVm.toNat_sub_ofNat h

theorem base_add (hF : F ≤ N) (hN : N ≤ m0.regs.SP.toNat) :
    base m0 N + BitVec.ofNat 64 (N - F) = base m0 F := by
  apply BitVec.eq_of_toNat_eq
  have := m0.regs.SP.toNat_lt
  rw [NativeRustcVm.toNat_add_ofNat (by rw [base_toNat hN]; omega), base_toNat hN,
    base_toNat (by omega)]
  omega

theorem base_sub (hN : F + N ≤ m0.regs.SP.toNat) :
    base m0 F - BitVec.ofNat 64 N = base m0 (F + N) := by
  apply BitVec.eq_of_toNat_eq
  rw [NativeRustcVm.toNat_sub_ofNat (by rw [base_toNat (by omega)]; omega),
    base_toNat (by omega), base_toNat hN]
  omega

theorem base_add_eq : base m0 F + BitVec.ofNat 64 F = m0.regs.SP.toBitVec := by
  unfold base
  exact BitVec.sub_add_cancel _ _

theorem base_noWrap (hF : F ≤ m0.regs.SP.toNat) : NoWrap (base m0 F) F := by
  unfold NoWrap
  rw [base_toNat hF]
  have := m0.regs.SP.toNat_lt
  omega

theorem stackBelow_eq {m : MachineData} (hsp : m.regs.SP.toBitVec = base m0 F) {N' : Nat}
    (h : F + N' ≤ m0.regs.SP.toNat) : stackBelow m N' = base m0 (F + N') := by
  unfold stackBelow
  rw [hsp, base_sub h]

/-- The frame's bytes are mapped: the top `F` of the `N` bytes of stack. -/
theorem frame_mapped {N : Nat} (h0 : StackOk m0 N) (hF : F ≤ N) :
    Mapped m0.dmem (base m0 F) F := by
  obtain ⟨-, hN, hmap⟩ := h0
  intro i hi
  have := hmap (N - F + i) (by omega)
  rwa [show m0.regs.SP.toBitVec - BitVec.ofNat 64 N = base m0 N from rfl,
    ← NativeRustcVm.addr_add_add, base_add hF hN] at this

/-- The frame's base is 16-byte aligned. -/
theorem frame_aligned {N : Nat} (h0 : StackOk m0 N) (hF : F ≤ N) (h16 : F % 16 = 0) :
    (base m0 F).toNat % 16 = 0 := by
  obtain ⟨hal, hN, -⟩ := h0
  rw [base_toNat (by omega)]
  omega

/-- A range apart from the `N` bytes of stack is apart from the frame. -/
theorem apart_frame {N : Nat} (hN : N ≤ m0.regs.SP.toNat) (hF : F ≤ N) {a : BitVec 64} {n : Nat}
    (h : Apart a n (stackBelow m0 N) N) : Apart a n (base m0 F) F := by
  have h1 := base_toNat (m0 := m0) (F := F) (by omega)
  have h2 : (stackBelow m0 N).toNat = m0.regs.SP.toNat - N := base_toNat hN
  unfold Apart at *
  omega

end

/-! ## The frame -/

namespace Fr

variable {m0 : MachineData} {F N : Nat} {slots : List (Nat × XReg)} {keep : List XReg}
  {outs : BitVec 64 → Prop} {m : MachineData}

/-- The stack below the frame for a callee using `N'` bytes. -/
theorem stackOk (h : Fr m0 F N slots keep outs m) (h0 : StackOk m0 N) (hF : F % 16 = 0)
    {N' : Nat} (hle : F + N' ≤ N) : StackOk m N' := by
  obtain ⟨hal, hN, hmap⟩ := h0
  have hspN : m.regs.SP.toNat = m0.regs.SP.toNat - F := by
    show m.regs.SP.toBitVec.toNat = _
    rw [h.sp, base_toNat (by omega)]
  refine ⟨by omega, by omega, fun i hi ↦ ?_⟩
  have hb : m.regs.SP.toBitVec - BitVec.ofNat 64 N' + BitVec.ofNat 64 i =
      m0.regs.SP.toBitVec - BitVec.ofNat 64 N + BitVec.ofNat 64 (N - F - N' + i) := by
    rw [h.sp, base_sub (by omega), show m0.regs.SP.toBitVec - BitVec.ofNat 64 N = base m0 N from
      rfl, ← base_add (F := F + N') (by omega) hN, NativeRustcVm.addr_add_add]
    congr 2
    omega
  rw [hb]
  exact h.kept _ (hmap _ (by omega))

/-- An argument apart from the entry's stack is apart from a callee's. -/
theorem apart (h : Fr m0 F N slots keep outs m) (hN : N ≤ m0.regs.SP.toNat) {a : BitVec 64}
    {n N' : Nat} (ha : Apart a n (stackBelow m0 N) N) (hle : F + N' ≤ N) :
    Apart a n (stackBelow m N') N' := by
  rw [stackBelow_eq h.sp (by omega)]
  have h1 := base_toNat (m0 := m0) (F := F + N') (by omega)
  have h2 : (stackBelow m0 N).toNat = m0.regs.SP.toNat - N := base_toNat hN
  unfold Apart at *
  omega

/-- **A step**: a block or a call that keeps SP and the kept registers, unmaps nothing and writes
neither the slots nor outside the stack and the outputs. -/
theorem step (h : Fr m0 F N slots keep outs m) {m' : MachineData} {W : BitVec 64 → Prop}
    (hsp : m'.regs.SP = m.regs.SP) (hkeep : ∀ r ∈ keep, m'.regs.getXReg r = m.regs.getXReg r)
    (hk : Kept m.dmem m'.dmem) (hs : SameOutside m.dmem m'.dmem W)
    (hW : ∀ q, W q → InRange (base m0 N) N q ∨ outs q)
    (hsl : ∀ p ∈ slots, ∀ i < 8, ¬W (base m0 F + BitVec.ofNat 64 p.1 + BitVec.ofNat 64 i)) :
    Fr m0 F N slots keep outs m' where
  sp := by rw [hsp]; exact h.sp
  keep r hr := by rw [hkeep r hr]; exact h.keep r hr
  slots p hp := NativeRustcVm.BytesAt.of_sameOutside (h.slots p hp) hs fun i hi ↦
    hsl p hp i (by rw [NativeRustcVm.length_wordBytes] at hi; exact hi)
  same := (NativeRustcVm.SameOutside.trans h.same hs).mono fun q hq ↦ hq.elim id (hW q)
  kept p hp := hk p (h.kept p hp)

/-- **A call** to a function using `N'` bytes of stack and writing outputs `outs'` among `outs`,
apart from the frame. -/
theorem call (h : Fr m0 F N slots keep outs m) {m' : MachineData} {N' : Nat}
    {outs' : BitVec 64 → Prop} (hN : N ≤ m0.regs.SP.toNat) (hle : F + N' ≤ N)
    (hkeep : ∀ r ∈ keep, calleeSaved r = true) (hsl : ∀ p ∈ slots, p.1 + 8 ≤ F)
    (houts : ∀ q, outs' q → outs q) (hfr : ∀ q, outs q → ¬InRange (base m0 F) F q)
    (hS : Saved m m')
    (hs : SameOutside m.dmem m'.dmem fun q ↦ InRange (stackBelow m N') N' q ∨ outs' q) :
    Fr m0 F N slots keep outs m' := by
  have hsb := stackBelow_eq h.sp (N' := N') (by omega)
  have hnw : NoWrap (base m0 (F + N')) N' := by
    unfold NoWrap; rw [base_toNat (by omega)]; have := m0.regs.SP.toNat_lt; omega
  have hnwN := base_noWrap (m0 := m0) (F := N) hN
  refine h.step hS.2.1 (fun r hr ↦ hS.1 r (hkeep r hr)) hS.2.2 hs (fun q hq ↦ ?_) ?_
  · rcases hq with hq | hq
    · left
      rw [hsb, Sym.inRange_iff hnw] at hq
      rw [Sym.inRange_iff hnwN]
      rw [base_toNat (by omega)] at hq
      rw [base_toNat hN]
      omega
    · exact .inr (houts q hq)
  · intro p hp i hi hq
    have hp8 := hsl p hp
    have hq' : base m0 F + BitVec.ofNat 64 p.1 + BitVec.ofNat 64 i =
        base m0 F + BitVec.ofNat 64 (p.1 + i) := NativeRustcVm.addr_add_add _ _ _
    have hF := base_noWrap (m0 := m0) (F := F) (by omega)
    have hin : InRange (base m0 F) F (base m0 F + BitVec.ofNat 64 (p.1 + i)) :=
      NativeRustcVm.inRange_add (by omega) (by unfold NoWrap at hF; omega)
    rw [hq'] at hq
    rcases hq with hq | hq
    · rw [hsb, Sym.inRange_iff hnw] at hq
      rw [Sym.inRange_iff hF] at hin
      rw [base_toNat (by omega)] at hq
      rw [base_toNat (by omega)] at hin
      omega
    · exact hfr _ (houts _ hq) hin

end Fr
/-- **A block without writes** that keeps SP and the kept registers' symbolic values. -/
theorem Fr.ofBlock [Labels] {m0 : MachineData} {F N : Nat} {slots : List (Nat × XReg)}
    {keep : List XReg} {outs : BitVec 64 → Prop} {m m' : MachineData} {env : Env}
    {S S' : SState} (h : Fr m0 F N slots keep outs m) (hm : Match env S m) (hm' : Match env S' m')
    (hwf : env.WF) (hd : m.dmem = env.mem0) (hmem : S'.mem = []) (hsp : S'.sp = S.sp)
    (hkeep : ∀ r ∈ keep, ∃ v, S.reg r = some v ∧ S'.reg r = some v) :
    Fr m0 F N slots keep outs m' := by
  have hd' : m'.dmem = m.dmem := (hm'.dmem_eq hwf hmem).trans hd.symm
  refine h.step (W := fun _ ↦ False) (Match.sp_eq hm hm' hsp) (fun r hr ↦ ?_)
    (fun p hp ↦ by rw [hd']; exact hp) (fun p _ ↦ by rw [hd']) (fun _ h ↦ h.elim)
    (fun _ _ _ _ h ↦ h)
  obtain ⟨v, h0, h1⟩ := hkeep r hr
  exact Match.reg_eq hm hm' h0 h1

/-- The writes a block may make: in region 0 (the frame) apart from the slots, or in a region of
the outputs. -/
@[expose] def WriteOk (env : Env) (F : Nat) (slots : List (Nat × XReg)) (outs : BitVec 64 → Prop)
    (w : Write) : Prop :=
  (w.r = 0 ∧ w.off + w.n ≤ F ∧ ∀ p ∈ slots, w.off + w.n ≤ p.1 ∨ p.1 + 8 ≤ w.off) ∨
    (w.r ≠ 0 ∧ ∀ b sz, env.regions[w.r]? = some (b, sz) →
      w.off + w.n ≤ sz ∧ ∀ i < sz, outs (b + BitVec.ofNat 64 i))

/-- **A block with writes** in the frame (not the slots) and in the outputs, region 0 the
frame, keeping SP and the kept registers' symbolic values. -/
theorem Fr.ofBlockW [Labels] {m0 : MachineData} {F N : Nat} {slots : List (Nat × XReg)}
    {keep : List XReg} {outs : BitVec 64 → Prop} {m m' : MachineData} {env : Env}
    {S S' : SState} (h : Fr m0 F N slots keep outs m) (hm : Match env S m) (hm' : Match env S' m')
    (hwf : env.WF) (hd : m.dmem = env.mem0) (hsp : S'.sp = S.sp)
    (hkeep : ∀ r ∈ keep, ∃ v, S.reg r = some v ∧ S'.reg r = some v)
    (h0 : env.regions[0]? = some (base m0 F, F)) (hFN : F ≤ N) (hN : N ≤ m0.regs.SP.toNat)
    (hsl : ∀ p ∈ slots, p.1 + 8 ≤ F) (hW : ∀ w ∈ S'.mem, WriteOk env F slots outs w) :
    Fr m0 F N slots keep outs m' := by
  have hnwF := base_noWrap (m0 := m0) (F := F) (by omega)
  have hbF := base_toNat (m0 := m0) (F := F) (by omega)
  have hbN := base_toNat (m0 := m0) (F := N) hN
  have hnwN := base_noWrap (m0 := m0) (F := N) hN
  refine h.step (W := Written env S') (Match.sp_eq hm hm' hsp) (fun r hr ↦ ?_)
    (fun p hp ↦ hm'.kept hwf p (by rw [← hd]; exact hp))
    (fun p hp ↦ by rw [hm'.get?_mem0 hwf hp, hd]) (fun q hq ↦ ?_) ?_
  · obtain ⟨v, e0, e1⟩ := hkeep r hr
    exact Match.reg_eq hm hm' e0 e1
  · obtain ⟨w, hw, b, sz, hb, h1, h2⟩ := hq
    rcases hW w hw with ⟨hr, hle, -⟩ | ⟨-, hout⟩
    · left
      rw [hr, h0] at hb
      cases hb
      rw [inRange_iff hnwN]
      rw [hbF] at h1 h2
      omega
    · right
      obtain ⟨hle, hall⟩ := hout b sz hb
      have := Env.addr_in hwf hb (a := q) (by omega)
      rw [this]
      exact hall _ (by omega)
  · intro p hp i hi ⟨w, hw, b, sz, hb, h1, h2⟩
    have hp8 := hsl p hp
    have hq : (base m0 F + BitVec.ofNat 64 p.1 + BitVec.ofNat 64 i).toNat =
        (base m0 F).toNat + p.1 + i := by
      rw [NativeRustcVm.addr_add_add, NativeRustcVm.toNat_add_ofNat]
      all_goals unfold NoWrap at hnwF
      all_goals omega
    rw [hq] at h1 h2
    rcases hW w hw with ⟨hr, hle, hs⟩ | ⟨hr, hout⟩
    · rw [hr, h0] at hb
      cases hb
      have := hs p hp
      omega
    · obtain ⟨hle, -⟩ := hout b sz hb
      have := hwf.disjoint w.r 0 b (base m0 F) sz F hr hb h0
      omega

/-- **A call to a function** that uses `N'` bytes of stack and changes nothing else: the frame
kept, the callee-saved registers too. -/
theorem Fr.leaf [Host] {m0 : MachineData} {F N : Nat} {slots : List (Nat × XReg)}
    {keep : List XReg} {outs : BitVec 64 → Prop} {l : Label} {P : MachineData → Prop}
    {Q : MachineData → MachineData → Prop} {N' : Nat} {st : MachineState} {next : Int64}
    {R : MachineState → Prop} (h : Fr m0 F N slots keep outs st.data)
    (hN : N ≤ m0.regs.SP.toNat) (hle : F + N' ≤ N) (hkeep : ∀ r ∈ keep, calleeSaved r = true)
    (hsl : ∀ p ∈ slots, p.1 + 8 ≤ F) (hfr : ∀ q, outs q → ¬InRange (base m0 F) F q)
    (hspec : Spec (Labels.label l) P Q)
    (hQ : ∀ m m', Q m m' → SameOutside m.dmem m'.dmem (fun q ↦ InRange (stackBelow m N') N' q ∨
      outs q) ∧ Saved m m')
    (hpc : st.pc = Labels.label l ∧ retOf st.data = next) (hP : P st.data)
    (cont : ∀ m2, Fr m0 F N slots keep outs m2 → Q st.data m2 →
      (∀ r, calleeSaved r = true → m2.regs.getXReg r = st.data.regs.getXReg r) →
      Eventually (step1 Host.exe) R ⟨m2, next⟩) :
    Eventually (step1 Host.exe) R st :=
  Eventually.bind (Spec.apply hspec hpc.1 hP) fun ⟨m2, pc⟩ ⟨hpc', hq⟩ ↦ by
    simp only at hpc' hq
    rw [hpc', hpc.2]
    obtain ⟨hs, hS⟩ := hQ _ _ hq
    exact cont m2 (h.call hN hle hkeep hsl (fun _ h ↦ h) hfr hS hs) hq hS.1

/-- **A call writing into the frame**: a callee using `N'` bytes of stack, writing the `n` frame
bytes from offset `lo` (none of the slots) and outputs `outs'` among `outs`. -/
theorem Fr.callIn {m0 : MachineData} {F N : Nat} {slots : List (Nat × XReg)} {keep : List XReg}
    {outs : BitVec 64 → Prop} {m m' : MachineData} {N' lo n : Nat} {outs' : BitVec 64 → Prop}
    (h : Fr m0 F N slots keep outs m) (hN : N ≤ m0.regs.SP.toNat) (hle : F + N' ≤ N)
    (hlo : lo + n ≤ F) (hkeep : ∀ r ∈ keep, calleeSaved r = true)
    (hsl : ∀ p ∈ slots, p.1 + 8 ≤ F ∧ (p.1 + 8 ≤ lo ∨ lo + n ≤ p.1))
    (houts : ∀ q, outs' q → outs q) (hfr : ∀ q, outs q → ¬InRange (base m0 F) F q)
    (hS : Saved m m')
    (hs : SameOutside m.dmem m'.dmem fun q ↦ InRange (stackBelow m N') N' q ∨
      InRange (base m0 F + BitVec.ofNat 64 lo) n q ∨ outs' q) :
    Fr m0 F N slots keep outs m' := by
  have hsb := stackBelow_eq h.sp (N' := N') (by omega)
  have hnw : NoWrap (base m0 (F + N')) N' := by
    unfold NoWrap; rw [base_toNat (by omega)]; have := m0.regs.SP.toNat_lt; omega
  have hnwN := base_noWrap (m0 := m0) (F := N) hN
  have hF := base_noWrap (m0 := m0) (F := F) (by omega)
  have hbF := base_toNat (m0 := m0) (F := F) (by omega)
  have hSP := m0.regs.SP.toNat_lt
  have hlo' : (base m0 F + BitVec.ofNat 64 lo).toNat = (base m0 F).toNat + lo :=
    NativeRustcVm.toNat_add_ofNat (by unfold NoWrap at hF; omega)
  have hnwlo : NoWrap (base m0 F + BitVec.ofNat 64 lo) n := by
    unfold NoWrap at hF ⊢; rw [hlo']; omega
  refine h.step hS.2.1 (fun r hr ↦ hS.1 r (hkeep r hr)) hS.2.2 hs (fun q hq ↦ ?_) ?_
  · rcases hq with hq | hq | hq
    · left
      rw [hsb, Sym.inRange_iff hnw] at hq
      rw [Sym.inRange_iff hnwN]
      rw [base_toNat (by omega)] at hq
      rw [base_toNat hN]
      omega
    · left
      rw [Sym.inRange_iff hnwlo, hlo'] at hq
      rw [Sym.inRange_iff hnwN, base_toNat hN]
      omega
    · exact .inr (houts q hq)
  · intro p hp i hi hq
    obtain ⟨hp8, hpl⟩ := hsl p hp
    have hq' : base m0 F + BitVec.ofNat 64 p.1 + BitVec.ofNat 64 i =
        base m0 F + BitVec.ofNat 64 (p.1 + i) := NativeRustcVm.addr_add_add _ _ _
    have hin : InRange (base m0 F) F (base m0 F + BitVec.ofNat 64 (p.1 + i)) :=
      NativeRustcVm.inRange_add (by omega) (by unfold NoWrap at hF; omega)
    have hpi : (base m0 F + BitVec.ofNat 64 (p.1 + i)).toNat = (base m0 F).toNat + (p.1 + i) :=
      NativeRustcVm.toNat_add_ofNat (by unfold NoWrap at hF; omega)
    rw [hq'] at hq
    rcases hq with hq | hq | hq
    · rw [hsb, Sym.inRange_iff hnw] at hq
      rw [base_toNat (by omega), hpi] at hq
      omega
    · rw [Sym.inRange_iff hnwlo, hlo', hpi] at hq
      omega
    · exact hfr _ (houts _ hq) hin

/-- **A call** (as `Fr.leaf`), its postcondition's footprint needed at the call's state only. -/
theorem Fr.leafAt [Host] {m0 : MachineData} {F N : Nat} {slots : List (Nat × XReg)}
    {keep : List XReg} {outs : BitVec 64 → Prop} {l : Label} {P : MachineData → Prop}
    {Q : MachineData → MachineData → Prop} {N' : Nat} {st : MachineState} {next : Int64}
    {R : MachineState → Prop} (h : Fr m0 F N slots keep outs st.data)
    (hN : N ≤ m0.regs.SP.toNat) (hle : F + N' ≤ N) (hkeep : ∀ r ∈ keep, calleeSaved r = true)
    (hsl : ∀ p ∈ slots, p.1 + 8 ≤ F) (hfr : ∀ q, outs q → ¬InRange (base m0 F) F q)
    (hspec : Spec (Labels.label l) P Q)
    (hpc : st.pc = Labels.label l ∧ retOf st.data = next) (hP : P st.data)
    (hQ : ∀ m', Q st.data m' → SameOutside st.data.dmem m'.dmem (fun q ↦
      InRange (stackBelow st.data N') N' q ∨ outs q) ∧ Saved st.data m')
    (cont : ∀ m2, Fr m0 F N slots keep outs m2 → Q st.data m2 →
      (∀ r, calleeSaved r = true → m2.regs.getXReg r = st.data.regs.getXReg r) →
      Eventually (step1 Host.exe) R ⟨m2, next⟩) :
    Eventually (step1 Host.exe) R st :=
  Eventually.bind (Spec.apply hspec hpc.1 hP) fun ⟨m2, pc⟩ ⟨hpc', hq⟩ ↦ by
    simp only at hpc' hq
    rw [hpc', hpc.2]
    obtain ⟨hs, hS⟩ := hQ _ hq
    exact cont m2 (h.call hN hle hkeep hsl (fun _ h ↦ h) hfr hS hs) hq hS.1

/-- **A call writing into the frame** (`Fr.callIn`): the `n` frame bytes from `lo`. -/
theorem Fr.leafIn [Host] {m0 : MachineData} {F N : Nat} {slots : List (Nat × XReg)}
    {keep : List XReg} {outs : BitVec 64 → Prop} {l : Label} {P : MachineData → Prop}
    {Q : MachineData → MachineData → Prop} {N' lo n : Nat} {st : MachineState} {next : Int64}
    {R : MachineState → Prop} (h : Fr m0 F N slots keep outs st.data)
    (hN : N ≤ m0.regs.SP.toNat) (hle : F + N' ≤ N) (hlo : lo + n ≤ F)
    (hkeep : ∀ r ∈ keep, calleeSaved r = true)
    (hsl : ∀ p ∈ slots, p.1 + 8 ≤ F ∧ (p.1 + 8 ≤ lo ∨ lo + n ≤ p.1))
    (hfr : ∀ q, outs q → ¬InRange (base m0 F) F q) (hspec : Spec (Labels.label l) P Q)
    (hpc : st.pc = Labels.label l ∧ retOf st.data = next) (hP : P st.data)
    (hQ : ∀ m', Q st.data m' → SameOutside st.data.dmem m'.dmem (fun q ↦
      InRange (stackBelow st.data N') N' q ∨ InRange (base m0 F + BitVec.ofNat 64 lo) n q ∨
        outs q) ∧ Saved st.data m')
    (cont : ∀ m2, Fr m0 F N slots keep outs m2 → Q st.data m2 →
      (∀ r, calleeSaved r = true → m2.regs.getXReg r = st.data.regs.getXReg r) →
      Eventually (step1 Host.exe) R ⟨m2, next⟩) :
    Eventually (step1 Host.exe) R st :=
  Eventually.bind (Spec.apply hspec hpc.1 hP) fun ⟨m2, pc⟩ ⟨hpc', hq⟩ ↦ by
    simp only at hpc' hq
    rw [hpc', hpc.2]
    obtain ⟨hs, hS⟩ := hQ _ hq
    exact cont m2 (h.callIn hN hle hlo hkeep hsl (fun _ h ↦ h) hfr hS hs) hq hS.1

/-! ## Prologue and epilogue -/

theorem mem_of_contains {l : List XReg} {r : XReg} (h : l.contains r = true) : r ∈ l := by
  induction l with
  | nil => simp at h
  | cons a l ih =>
    simp only [List.contains_cons, Bool.or_eq_true] at h
    rcases h with h | h
    · rw [XReg.eq_of_beq h]; exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ (ih h)

theorem slotsOk_iff {S : SState} {slots : List (Nat × XReg)} (h : slotsOk S slots = true) :
    ∀ p ∈ slots, ∀ i < 8, findWrite 0 (p.1 + i) S.mem = some (.reg p.2, i) := by
  intro p hp i hi
  simp only [slotsOk, List.all_eq_true, List.mem_range, beq_iff_eq] at h
  exact h p hp i hi

section
variable [Labels]

/-- **After the prologue**: a block from the entry `m0`, region 0 the `F` bytes below SP, whose
writes are the slots' and in region 0 (`slotsOk`), keeping SP at region 0's base and the
registers `keep`. -/
theorem Fr.ofPrologue {m0 m : MachineData} {F N : Nat} {slots : List (Nat × XReg)}
    {keep : List XReg} {outs : BitVec 64 → Prop} {rs : List (BitVec 64 × Nat)}
    {vars : Nat → BitVec 64} {S : SState}
    (hN : N ≤ m0.regs.SP.toNat) (hFN : F ≤ N)
    (hm : Match (Env.ofMachine m0 ((base m0 F, F) :: rs) vars) S m)
    (hwf : (Env.ofMachine m0 ((base m0 F, F) :: rs) vars).WF)
    (hsp : S.sp = .ptr 0 0) (hok : slotsOk S slots = true) (hsl : ∀ p ∈ slots, p.1 + 8 ≤ F)
    (hmem : ∀ w ∈ S.mem, w.r = 0 ∧ w.off + w.n ≤ F)
    (hkeep : ∀ r ∈ keep, S.reg r = some (.reg r)) :
    Fr m0 F N slots keep outs m where
  sp := by rw [hm.sp, hsp]; simp [Sym.eval]
  keep r hr := by
    have := hm.regs r _ (hkeep r hr)
    exact UInt64.toBitVec_inj.mp this
  slots p hp := by
    have hw := hm.bytesAt_write (r := 0) (o := p.1) (n := 8) (b := base m0 F) (sz := F) rfl
      (hsl p hp) (v := .reg p.2) fun i hi ↦ slotsOk_iff hok p hp i hi
    rw [wordBytes_reg] at hw
    exact hw
  same q hq := by
    refine hm.get?_mem0 hwf fun ⟨w, hw, b, sz, hb, h1, h2⟩ ↦ hq (.inl ?_)
    obtain ⟨hr, hn⟩ := hmem w hw
    rw [hr] at hb
    cases hb
    rw [Sym.inRange_iff (base_noWrap hN), base_toNat hN]
    rw [base_toNat (by omega)] at h1 h2
    omega
  kept := hm.kept hwf

/-- **After the epilogue**: a block from a state of the frame, region 0 the frame, that restores
SP and the callee-saved registers and X30 (`exitOk`): the entry's return address, its
callee-saved registers and SP, every byte it mapped. -/
theorem Fr.exit {m0 m m' : MachineData} {F N : Nat} {slots : List (Nat × XReg)}
    {keep : List XReg} {outs : BitVec 64 → Prop} {rs : List (BitVec 64 × Nat)}
    {vars : Nat → BitVec 64} {S : SState} (h : Fr m0 F N slots keep outs m)
    (hm : Match (Env.ofMachine m ((base m0 F, F) :: rs) vars) S m')
    (hwf : (Env.ofMachine m ((base m0 F, F) :: rs) vars).WF)
    (hok : exitOk S F slots keep = true) :
    retOf m' = retOf m0 ∧ Saved m0 m' := by
  simp only [exitOk, Bool.and_eq_true, List.all_eq_true, beq_iff_eq] at hok
  obtain ⟨hregs, hsp⟩ := hok
  have hb : (Env.ofMachine m ((base m0 F, F) :: rs) vars).base 0 = base m0 F := rfl
  have hreg : ∀ r, (calleeSaved r = true ∨ r = .X30) → m'.regs.getXReg r = m0.regs.getXReg r := by
    intro r hr
    have := hregs r (mem_allXRegs r)
    simp only [Bool.or_eq_true, Bool.and_eq_true, Bool.not_eq_true', List.any_eq_true,
      beq_iff_eq] at this
    rcases this with (⟨hc, hx⟩ | ⟨p, hp, hpr, hS⟩) | ⟨hk, hS⟩
    · rcases hr with hr | hr
      · rw [hr] at hc; cases hc
      · rw [hr] at hx; exact absurd hx (by decide)
    · apply UInt64.toBitVec_inj.mp
      rw [hm.regs r _ hS]
      simp only [Sym.eval]
      rw [load_word (by rw [hb]; exact h.slots p hp), XReg.eq_of_beq hpr]
    · apply UInt64.toBitVec_inj.mp
      rw [hm.regs r _ hS, ← h.keep r (mem_of_contains hk)]
      rfl
  refine ⟨?_, fun r hr ↦ hreg r (.inl hr), ?_, fun p hp ↦ hm.kept hwf p (h.kept p hp)⟩
  · simp only [retOf]
    rw [show m'.regs.X30 = m'.regs.getXReg .X30 from rfl, hreg .X30 (.inr rfl)]
    rfl
  · apply UInt64.toBitVec_inj.mp
    rw [hm.sp, hsp]
    simp only [Sym.eval, hb]
    rw [BitVec.ofInt_natCast]
    exact base_add_eq

end

end

end NativeRustcVmArm.Ring
