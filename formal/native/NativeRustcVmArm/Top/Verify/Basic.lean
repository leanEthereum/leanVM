module

public import NativeRustcVmArm.Code.Vm.Verify.Names
public import NativeRustcVmArm.Spec.Top
public import NativeRustcVmArm.Rodata.Keccak
public import NativeRustcVmArm.Top.Verify.Exec

/-!
# `verify`: where things are

The facts `VerifyPre` gives as numbers (`Geo`, `geo_of`): the 832-byte frame at `frameOf m0`, the
`TState` at its byte 8 (`tOf m0`), the stack, the public input, the `Decoded`, the decoded area,
the working area and the bytecode. The bytecode's and the public input's words in memory
(`bcOf`, `pubOf`, `wordsAt_bcOf`, `wordsAt_pubOf`), the transcript's first state (`start`). The
read-only data kept where only the stack changed (`rodataAt_body`). What the states after `seed`
(`SA`) and after `verify_execution` (`SB`) hold. The blocks' places and the label.
-/

namespace NativeRustcVmArm.Top.Verify

open NativeRustcArm NativeRustcArm.Sym NativeRustcVmArm.Vm.Verify NativeVm.Model
open NativeRustcVm.Transcript
open NativeRustcVm (WordsAt Region wordsOf wordOf)
open NativeRustcVm.Top (workAreaBytes)

/-- The frame's address. -/
@[expose] public def frameOf (m0 : MachineData) : BitVec 64 :=
  m0.regs.SP.toBitVec - BitVec.ofNat 64 832

/-- The `TState`'s address. -/
@[expose] public def tOf (m0 : MachineData) : BitVec 64 := frameOf m0 + BitVec.ofNat 64 8

/-- The bytecode's words at the entry. -/
@[expose] public def bcOf (m0 : MachineData) : List UInt64 :=
  wordsOf m0.dmem m0.regs.X0.toBitVec m0.regs.X1.toNat

/-- The public input's words at the entry. -/
@[expose] public def pubOf (m0 : MachineData) : Vector UInt64 4 :=
  Vector.ofFn fun i ↦ wordOf m0.dmem (m0.regs.X2.toBitVec + BitVec.ofNat 64 (8 * i.val))

/-- The transcript's first state: the seed's sponge, the stream and the openings unread. -/
@[expose] public def start (bcw : List UInt64) (P : Vector UInt64 4) (stream : Array EW)
    (openings : Array (Array OpeningW)) : TState :=
  ⟨⟨seed bcw.toArray P, #[], none⟩, stream, 0, openings, 0, #[]⟩

/-- `VerifyPre`'s addresses as numbers. -/
public structure Geo [Labels] (a : DecArea) (m0 : MachineData) : Prop where
  s : 19216 ≤ m0.regs.SP.toBitVec.toNat
  al : m0.regs.SP.toBitVec.toNat % 16 = 0
  F : (frameOf m0).toNat = m0.regs.SP.toBitVec.toNat - 832
  T : (tOf m0).toNat = m0.regs.SP.toBitVec.toNat - 824
  sb : (m0.regs.SP.toBitVec - BitVec.ofNat 64 verifyStack).toNat =
    m0.regs.SP.toBitVec.toNat - 19216
  pub : m0.regs.X2.toBitVec.toNat + 32 ≤ m0.regs.SP.toBitVec.toNat - 19216 ∨
    m0.regs.SP.toBitVec.toNat ≤ m0.regs.X2.toBitVec.toNat
  pubN : m0.regs.X2.toBitVec.toNat + 32 ≤ 2 ^ 64
  dec : m0.regs.X3.toBitVec.toNat + 24 ≤ m0.regs.SP.toBitVec.toNat - 19216 ∨
    m0.regs.SP.toBitVec.toNat ≤ m0.regs.X3.toBitVec.toNat
  decN : m0.regs.X3.toBitVec.toNat + 24 ≤ 2 ^ 64
  area : a.words.toNat + 8 * a.len ≤ m0.regs.SP.toBitVec.toNat - 19216 ∨
    m0.regs.SP.toBitVec.toNat ≤ a.words.toNat
  areaN : a.words.toNat + 8 * a.len ≤ 2 ^ 64
  work : m0.regs.X4.toBitVec.toNat + workAreaBytes ≤ m0.regs.SP.toBitVec.toNat - 19216 ∨
    m0.regs.SP.toBitVec.toNat ≤ m0.regs.X4.toBitVec.toNat
  workN : m0.regs.X4.toBitVec.toNat + workAreaBytes ≤ 2 ^ 64
  pubDec : m0.regs.X2.toBitVec.toNat + 32 ≤ m0.regs.X3.toBitVec.toNat ∨
    m0.regs.X3.toBitVec.toNat + 24 ≤ m0.regs.X2.toBitVec.toNat
  decArea : m0.regs.X3.toBitVec.toNat + 24 ≤ a.words.toNat ∨
    a.words.toNat + 8 * a.len ≤ m0.regs.X3.toBitVec.toNat
  decWork : m0.regs.X3.toBitVec.toNat + 24 ≤ m0.regs.X4.toBitVec.toNat ∨
    m0.regs.X4.toBitVec.toNat + workAreaBytes ≤ m0.regs.X3.toBitVec.toNat
  bc : 0 < m0.regs.X1.toBitVec.toNat →
    m0.regs.X0.toBitVec.toNat + 8 * m0.regs.X1.toBitVec.toNat ≤
      m0.regs.SP.toBitVec.toNat - 19216 ∨ m0.regs.SP.toBitVec.toNat ≤ m0.regs.X0.toBitVec.toNat
  bcN : m0.regs.X0.toBitVec.toNat + 8 * m0.regs.X1.toBitVec.toNat ≤ 2 ^ 64
  n32 : 9 + 8 * m0.regs.X1.toBitVec.toNat < 2 ^ 32
  len : 0 < a.len

public section

theorem verifyStack_eq : verifyStack = 19216 := rfl

/-- The callee-saved registers outside the slots. -/
theorem nonslot {r : XReg} (hr : calleeSaved r = true) (hn : r ∉ slots.map (·.2)) :
    r ∈ [XReg.X24, .X25, .X26, .X27, .X28] := by
  cases r <;> simp_all [calleeSaved, slots]

theorem slotsIn : SlotsIn slots 768 832 := by
  intro p hp
  simp only [slots, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with h | h | h | h | h | h | h <;> rw [h] <;> decide

theorem geo_of [Labels] {a : DecArea} {stream : Array EW} {openings : Array (Array OpeningW)}
    {m0 : MachineData} (hpre : VerifyPre a stream openings m0) : Geo a m0 := by
  obtain ⟨⟨hal, hsN, -⟩, -, hn32, -, hdec, ⟨-, hbcN⟩, ⟨-, hpubN⟩, ⟨-, hdecN⟩, ⟨-, haN⟩,
    ⟨-, hwN⟩, hdis, -, hbcD⟩ := hpre
  have hS := verifyStack_eq
  have hsl := m0.regs.SP.toBitVec.isLt
  have hs : 19216 ≤ m0.regs.SP.toBitVec.toNat := by
    have : verifyStack ≤ m0.regs.SP.toBitVec.toNat := hsN
    rw [hS] at this; exact this
  have hal' : m0.regs.SP.toBitVec.toNat % 16 = 0 := hal
  have hF : (frameOf m0).toNat = m0.regs.SP.toBitVec.toNat - 832 := toNat_subAddr (by omega)
  have hsb : (m0.regs.SP.toBitVec - BitVec.ofNat 64 verifyStack).toNat =
      m0.regs.SP.toBitVec.toNat - 19216 := by rw [hS]; exact toNat_subAddr (by omega)
  have hsb' : (stackBelow m0 verifyStack).toNat = m0.regs.SP.toBitVec.toNat - 19216 := hsb
  simp only [NativeRustcVm.disjoint_cons_iff, List.forall_mem_cons, List.mem_nil_iff,
    false_implies, implies_true, NativeRustcVm.disjoint_nil, and_true, NativeRustcVm.Apart, stackR,
    DecArea.region] at hdis
  obtain ⟨⟨h01, h02, h03, h04⟩, ⟨h12, h13, h14⟩, ⟨h23, h24⟩, h34⟩ := hdis
  rw [hsb', hS] at h01 h02 h03 h04
  have hlen : 0 < a.len := by
    have := hdec.len
    unfold NativeVm.decodedWords NativeVm.phaseBase at this
    omega
  have e1 : m0.regs.X1.toNat = m0.regs.X1.toBitVec.toNat := rfl
  have hbcN' : m0.regs.X0.toBitVec.toNat + 8 * m0.regs.X1.toBitVec.toNat ≤ 2 ^ 64 := hbcN
  refine ⟨hs, hal', hF, ?_, hsb, by omega, hpubN, by omega, hdecN, by omega, haN, by omega, hwN,
    h12, h23, h24, fun hn ↦ ?_, hbcN', hn32, hlen⟩
  · unfold tOf; rw [toNat_addr (by omega), hF]; omega
  · obtain ⟨h, -⟩ := hbcD (by omega)
    simp only [NativeRustcVm.disjoint_cons_iff, List.forall_mem_cons, NativeRustcVm.Apart,
      stackR] at h
    obtain ⟨⟨h1, -⟩, -⟩ := h
    rw [hsb', hS] at h1
    omega

/-- The bytecode's words are at its address. -/
theorem wordsAt_bcOf {m0 : MachineData}
    (h : NativeRustcVm.Mapped m0.dmem m0.regs.X0.toBitVec (8 * m0.regs.X1.toNat)) :
    WordsAt m0.dmem m0.regs.X0.toBitVec (bcOf m0) :=
  wordsAt_wordsOf h

theorem length_bcOf (m0 : MachineData) : (bcOf m0).length = m0.regs.X1.toNat := by
  simp [bcOf, wordsOf]

/-- The public input's words are at its address. -/
theorem wordsAt_pubOf {m0 : MachineData}
    (h : NativeRustcVm.Mapped m0.dmem m0.regs.X2.toBitVec 32) :
    WordsAt m0.dmem m0.regs.X2.toBitVec (pubOf m0).toList := by
  refine NativeRustcVm.wordsAt_iff.mpr fun i hi ↦ ?_
  have hi4 : i < 4 := by simpa using hi
  simp only [pubOf, Vector.toList_ofFn, List.getElem_ofFn]
  exact wordAt_wordOf (NativeRustcVm.Mapped.sub h (by omega))

/-- The bytecode's words in memory are `bcOf`. -/
theorem bcOf_eq {m0 : MachineData} {bcw : List UInt64} (hl : bcw.length = m0.regs.X1.toNat)
    (h : WordsAt m0.dmem m0.regs.X0.toBitVec bcw) : bcw = bcOf m0 := by
  have := NativeRustcVm.wordsOf_of_wordsAt h
  rw [hl] at this
  exact this.symm

/-- The public input's words in memory are `pubOf`. -/
theorem pubOf_eq {m0 : MachineData} {P : Vector UInt64 4}
    (h : WordsAt m0.dmem m0.regs.X2.toBitVec P.toList) : P = pubOf m0 := by
  apply Vector.ext
  intro i hi
  have hw := NativeRustcVm.WordsAt.getElem h (i := i) (by simpa using hi)
  simp only [pubOf, Vector.getElem_ofFn]
  rw [NativeRustcVm.wordOf_of_wordAt hw]
  simp

/-- The read-only data stays at its labels where only the stack changed, apart from a stack range
inside the first. -/
theorem rodataAt_body [Labels] {m0 st : MachineData} {F N N' : Nat} {slots : List (Nat × XReg)}
    (h : RodataAt m0 N) (hb : Body m0 F slots (InStack m0 N) st) (hN : N ≤ m0.regs.SP.toBitVec.toNat)
    (hsp : st.regs.SP.toBitVec = m0.regs.SP.toBitVec - BitVec.ofNat 64 F)
    (hle : F + N' ≤ N) : RodataAt st N' := by
  have hs : NativeRustcVm.SameOutside m0.dmem st.dmem (InRange (stackBelow m0 N) N) :=
    fun p hp ↦ hb.same p fun h ↦ hp ((inRange_below hN).mpr h)
  have hsb : (stackBelow m0 N).toNat = m0.regs.SP.toBitVec.toNat - N := toNat_subAddr hN
  have hsb' : (stackBelow st N').toNat = m0.regs.SP.toBitVec.toNat - F - N' := by
    show (st.regs.SP.toBitVec - BitVec.ofNat 64 N').toNat = _
    rw [hsp, toNat_subAddr (by rw [toNat_subAddr (by omega)]; omega), toNat_subAddr (by omega)]
  have := m0.regs.SP.toBitVec.isLt
  exact RodataAt.mono h hs (by unfold NativeRustcVm.NoWrap; omega) (by omega) (by omega)

variable [Host] {k : Nat}

theorem hb0 (hp : Placed code k) : b0.IsInfixAt Host.prog (k + NativeRustcVmArm.Vm.Verify.b0Offset) :=
  b0_in_code.trans hp.1 (by simp [b0])
theorem hb1 (hp : Placed code k) : b1.IsInfixAt Host.prog (k + NativeRustcVmArm.Vm.Verify.b1Offset) :=
  b1_in_code.trans hp.1 (by simp [b1])
theorem hb2 (hp : Placed code k) : b2.IsInfixAt Host.prog (k + NativeRustcVmArm.Vm.Verify.b2Offset) :=
  b2_in_code.trans hp.1 (by simp [b2])
theorem hb3 (hp : Placed code k) : b3.IsInfixAt Host.prog (k + NativeRustcVmArm.Vm.Verify.b3Offset) :=
  b3_in_code.trans hp.1 (by simp [b3])
theorem hb4 (hp : Placed code k) : b4.IsInfixAt Host.prog (k + NativeRustcVmArm.Vm.Verify.b4Offset) :=
  b4_in_code.trans hp.1 (by simp [b4])
theorem hb5 (hp : Placed code k) : b5.IsInfixAt Host.prog (k + NativeRustcVmArm.Vm.Verify.b5Offset) :=
  b5_in_code.trans hp.1 (by simp [b5])
theorem hb6 (hp : Placed code k) : b6.IsInfixAt Host.prog (k + NativeRustcVmArm.Vm.Verify.b6Offset) :=
  b6_in_code.trans hp.1 (by simp [b6])
theorem hb7 (hp : Placed code k) : b7.IsInfixAt Host.prog (k + NativeRustcVmArm.Vm.Verify.b7Offset) :=
  b7_in_code.trans hp.1 (by simp [b7])
theorem hb8 (hp : Placed code k) : b8.IsInfixAt Host.prog (k + NativeRustcVmArm.Vm.Verify.b8Offset) :=
  b8_in_code.trans hp.1 (by simp [b8])
theorem hb9 (hp : Placed code k) : b9.IsInfixAt Host.prog (k + NativeRustcVmArm.Vm.Verify.b9Offset) :=
  b9_in_code.trans hp.1 (by simp [b9])

theorem lbl_entry (hp : Placed code k) : Labels.label NativeRustcVmArm.Vm.Verify.entryLabel = Host.addrOf (k + NativeRustcVmArm.Vm.Verify.b0Offset) :=
  hp.label (j := NativeRustcVmArm.Vm.Verify.entryOffset) NativeRustcVmArm.Vm.Verify.entry_at
theorem lbl_3 (hp : Placed code k) : Labels.label NativeRustcVmArm.Vm.Verify.label_3 = Host.addrOf (k + NativeRustcVmArm.Vm.Verify.b5Offset) :=
  hp.label (j := NativeRustcVmArm.Vm.Verify.b5Offset) NativeRustcVmArm.Vm.Verify.label_3_at
theorem lbl_5 (hp : Placed code k) : Labels.label NativeRustcVmArm.Vm.Verify.label_5 = Host.addrOf (k + NativeRustcVmArm.Vm.Verify.b8Offset) :=
  hp.label (j := NativeRustcVmArm.Vm.Verify.b8Offset) NativeRustcVmArm.Vm.Verify.label_5_at
theorem lbl_6 (hp : Placed code k) : Labels.label NativeRustcVmArm.Vm.Verify.label_6 = Host.addrOf (k + NativeRustcVmArm.Vm.Verify.b9Offset) :=
  hp.label (j := NativeRustcVmArm.Vm.Verify.b9Offset) NativeRustcVmArm.Vm.Verify.label_6_at

end

/-- After `seed`: the frame's body, the arguments in X19 to X23, the seed in the `TState`'s
lanes. -/
public structure SA (m0 m : MachineData) : Prop where
  body : Body m0 832 slots (InStack m0 verifyStack) m
  x19 : m.regs.X19 = m0.regs.X3
  x20 : m.regs.X20 = m0.regs.X4
  x21 : m.regs.X21 = m0.regs.X2
  x22 : m.regs.X22 = m0.regs.X1
  x23 : m.regs.X23 = m0.regs.X0
  seed : WordsAt m.dmem (tOf m0) (seed (bcOf m0).toArray (pubOf m0)).toList

/-- After `verify_execution`: the frame's body, the working area written, the `Decoded` in X19,
the walk's success in X0, the walk's last state in the `TState`. -/
public structure SB (a : DecArea) (stream : Array EW) (openings : Array (Array OpeningW))
    (m0 m : MachineData) : Prop where
  body : Body m0 832 slots
    (fun q ↦ InStack m0 verifyStack q ∨ InRange m0.regs.X4.toBitVec workAreaBytes q) m
  x19 : m.regs.X19 = m0.regs.X3
  x0 : m.regs.X0 = okWord ((verifyExecution (bcOf m0).toArray (pubOf m0)).run
    (start (bcOf m0) (pubOf m0) stream openings)).isSome
  next : NextAt m.dmem (tOf m0) a ((verifyExecution (bcOf m0).toArray (pubOf m0)).run
    (start (bcOf m0) (pubOf m0) stream openings))

end NativeRustcVmArm.Top.Verify
