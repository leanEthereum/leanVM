module

public import NativeRustcVmX64.Top.Verify.Exec
public import NativeRustcVmX64.Top.Basic
public import NativeRustcVm.Arrays.ReadLemmas
public import NativeRustcVmX64.Code.Vm.Verify.Names

/-!
# `verify`: where things are (x86-64)

The frame (`fb m0`, the 816 bytes below the entry's RSP and the return address), the `TState` at
its byte 8 (`tOf m0`). The facts `VerifyPre` gives as numbers (`Geo`, `geo_of`): the stack, the
public input, the `Decoded`, the decoded area, the working area and the bytecode, pairwise apart.
The bytecode's and the public input's words in memory (`bcOf`, `pubOf`), the transcript's first
state (`start`). What the states after `seed` (`SA`) and after `verify_execution` (`SB`) hold.
-/

namespace NativeRustcVmX64.Top.Verify

open NativeRustcX64 NativeRustcVmX64.Transcript NativeRustcVm.Transcript NativeVm.Model
open NativeRustcVm (wordsOf wordOf)
open NativeRustcVm.Top (workAreaBytes)

@[expose] public section

/-- The frame's base. -/
abbrev fb (m0 : MachineData) : BitVec 64 := stackBelow m0 816

/-- The `TState`'s address. -/
abbrev tOf (m0 : MachineData) : BitVec 64 := off (fb m0) 8

/-- The bytecode's words at the entry. -/
def bcOf (m0 : MachineData) : List UInt64 := wordsOf m0.dmem (reg m0 .rdi) (reg m0 .rsi).toNat

/-- The public input's words at the entry. -/
def pubOf (m0 : MachineData) : Vector UInt64 4 :=
  Vector.ofFn fun i ↦ wordOf m0.dmem (reg m0 .rdx + BitVec.ofNat 64 (8 * i.val))

/-- The transcript's first state: the seed's sponge, the stream and the openings unread. -/
def start (bcw : List UInt64) (P : Vector UInt64 4) (stream : Array EW)
    (openings : Array (Array OpeningW)) : TState :=
  ⟨⟨seed bcw.toArray P, #[], none⟩, stream, 0, openings, 0, #[]⟩

/-- The walk's run from the first state. -/
def run (m0 : MachineData) (stream : Array EW) (openings : Array (Array OpeningW)) :
    Option (Unit × TState) :=
  (verifyExecution (bcOf m0).toArray (pubOf m0)).run (start (bcOf m0) (pubOf m0) stream openings)

end

/-- The stack's bottom: the `18704` bytes below the entry's RSP start here. -/
@[expose] public def sb (m0 : MachineData) : Nat := (stackBelow m0 18704).toNat

public theorem sb_eq (m0 : MachineData) : (stackBelow m0 18704).toNat = sb m0 := rfl

/-- `VerifyPre`'s addresses as numbers, all relative to the stack's bottom `sb m0` and without
subtraction (`omega` then never splits on one). -/
public structure Geo (a : DecArea) (m0 : MachineData) : Prop where
  R : (rspOf m0).toNat = sb m0 + 18704
  e8 : sb m0 + 18712 ≤ 2 ^ 64
  F : (fb m0).toNat = sb m0 + 17888
  pub : (reg m0 .rdx).toNat + 32 ≤ sb m0 ∨ sb m0 + 18712 ≤ (reg m0 .rdx).toNat
  pubN : (reg m0 .rdx).toNat + 32 ≤ 2 ^ 64
  dec : (reg m0 .rcx).toNat + 24 ≤ sb m0 ∨ sb m0 + 18712 ≤ (reg m0 .rcx).toNat
  decN : (reg m0 .rcx).toNat + 24 ≤ 2 ^ 64
  area : a.words.toNat + 8 * a.len ≤ sb m0 ∨ sb m0 + 18712 ≤ a.words.toNat
  areaN : a.words.toNat + 8 * a.len ≤ 2 ^ 64
  work : (reg m0 .r8).toNat + workAreaBytes ≤ sb m0 ∨ sb m0 + 18712 ≤ (reg m0 .r8).toNat
  workN : (reg m0 .r8).toNat + workAreaBytes ≤ 2 ^ 64
  pubDec : (reg m0 .rdx).toNat + 32 ≤ (reg m0 .rcx).toNat ∨
    (reg m0 .rcx).toNat + 24 ≤ (reg m0 .rdx).toNat
  pubArea : (reg m0 .rdx).toNat + 32 ≤ a.words.toNat ∨ a.words.toNat + 8 * a.len ≤ (reg m0 .rdx).toNat
  pubWork : (reg m0 .rdx).toNat + 32 ≤ (reg m0 .r8).toNat ∨
    (reg m0 .r8).toNat + workAreaBytes ≤ (reg m0 .rdx).toNat
  decArea : (reg m0 .rcx).toNat + 24 ≤ a.words.toNat ∨ a.words.toNat + 8 * a.len ≤ (reg m0 .rcx).toNat
  decWork : (reg m0 .rcx).toNat + 24 ≤ (reg m0 .r8).toNat ∨
    (reg m0 .r8).toNat + workAreaBytes ≤ (reg m0 .rcx).toNat
  areaWork : a.words.toNat + 8 * a.len ≤ (reg m0 .r8).toNat ∨
    (reg m0 .r8).toNat + workAreaBytes ≤ a.words.toNat
  bc : 0 < (reg m0 .rsi).toNat →
    ((reg m0 .rdi).toNat + 8 * (reg m0 .rsi).toNat ≤ sb m0 ∨
      sb m0 + 18712 ≤ (reg m0 .rdi).toNat) ∧
    ((reg m0 .rdi).toNat + 8 * (reg m0 .rsi).toNat ≤ a.words.toNat ∨
      a.words.toNat + 8 * a.len ≤ (reg m0 .rdi).toNat) ∧
    ((reg m0 .rdi).toNat + 8 * (reg m0 .rsi).toNat ≤ (reg m0 .r8).toNat ∨
      (reg m0 .r8).toNat + workAreaBytes ≤ (reg m0 .rdi).toNat)
  bcN : (reg m0 .rdi).toNat + 8 * (reg m0 .rsi).toNat ≤ 2 ^ 64
  n32 : 9 + 8 * (reg m0 .rsi).toNat < 2 ^ 32
  len : 0 < a.len

public section

theorem verifyStack_eq : verifyStack = 18704 := rfl

theorem slots_le : ∀ p ∈ slots, p.1 + 8 ≤ 816 := by decide
theorem slots_ge : ∀ p ∈ slots, 768 ≤ p.1 := by decide
theorem slots_cs : ∀ p ∈ slots, calleeSaved p.2 = true := by decide

/-- `stackBelow m0 n` as the stack's bottom plus `18704 - n`. -/
theorem stackBelow_sb {m0 : MachineData} (h : 18704 ≤ (rspOf m0).toNat) {n c : Nat}
    (hc : c + n = 18704) : (stackBelow m0 n).toNat = sb m0 + c := by
  rw [stackBelow_toNat (by omega), sb, stackBelow_toNat h]
  omega

theorem geo_of [Labels] {a : DecArea} {stream : Array EW} {openings : Array (Array OpeningW)}
    {m0 : MachineData} (hpre : VerifyPre a stream openings m0) : Geo a m0 := by
  obtain ⟨hst, -, hn32, -, hdec, ⟨-, hbcN⟩, ⟨-, hpubN⟩, ⟨-, hdecN⟩, ⟨-, haN⟩,
    ⟨-, hwN⟩, hdis, -, hbcD, -⟩ := hpre
  have hS := verifyStack_eq
  have hs : 18704 ≤ (rspOf m0).toNat := by have := hst.1; omega
  have h8 := hst.2.1
  have hR : (rspOf m0).toNat = sb m0 + 18704 := by
    rw [sb, stackBelow_toNat hs]; omega
  have hF : (fb m0).toNat = sb m0 + 17888 := stackBelow_sb hs (by decide)
  simp only [NativeRustcVm.disjoint_cons_iff, List.forall_mem_cons, List.mem_nil_iff,
    false_implies, implies_true, NativeRustcVm.disjoint_nil, and_true, NativeRustcVm.Apart, stackR,
    DecArea.region, hS] at hdis
  obtain ⟨⟨h01, h02, h03, h04⟩, ⟨h12, h13, h14⟩, ⟨h23, h24⟩, h34⟩ := hdis
  have hlen : 0 < a.len := by
    have := hdec.len
    unfold NativeVm.decodedWords NativeVm.phaseBase at this
    omega
  have hbcN' : (reg m0 .rdi).toNat + 8 * (reg m0 .rsi).toNat ≤ 2 ^ 64 := hbcN
  refine ⟨hR, by omega, hF, by rw [← sb_eq]; omega, hpubN, by rw [← sb_eq]; omega, hdecN,
    by rw [← sb_eq]; omega, haN, by rw [← sb_eq]; omega, hwN,
    h12, h13, h14, h23, h24, h34, fun hn ↦ ?_, hbcN', hn32, hlen⟩
  obtain ⟨h, -⟩ := hbcD hn
  simp only [NativeRustcVm.disjoint_cons_iff, List.forall_mem_cons, List.mem_nil_iff,
    false_implies, implies_true, NativeRustcVm.disjoint_nil, and_true, NativeRustcVm.Apart, stackR,
    DecArea.region, hS] at h
  obtain ⟨⟨h1, -, -⟩, ⟨h2, h3⟩, -⟩ := h
  exact ⟨by rw [← sb_eq]; omega, h2, h3⟩

theorem wordsAt_bcOf {m0 : MachineData}
    (h : NativeRustcVm.Mapped m0.dmem (reg m0 .rdi) (8 * (reg m0 .rsi).toNat)) :
    NativeRustcVm.WordsAt m0.dmem (reg m0 .rdi) (bcOf m0) :=
  NativeRustcVm.wordsAt_of_mapped h

theorem length_bcOf (m0 : MachineData) : (bcOf m0).length = (reg m0 .rsi).toNat := by
  simp [bcOf, wordsOf]

theorem wordsAt_pubOf {m0 : MachineData} (h : NativeRustcVm.Mapped m0.dmem (reg m0 .rdx) 32) :
    NativeRustcVm.WordsAt m0.dmem (reg m0 .rdx) (pubOf m0).toList := by
  refine NativeRustcVm.wordsAt_iff.mpr fun i hi ↦ ?_
  have hi4 : i < 4 := by simpa using hi
  simp only [pubOf, Vector.toList_ofFn, List.getElem_ofFn]
  exact NativeRustcVm.wordAt_of_mapped (NativeRustcVm.Mapped.sub h (by omega))

theorem bcOf_eq {m0 : MachineData} {bcw : List UInt64} (hl : bcw.length = (reg m0 .rsi).toNat)
    (h : NativeRustcVm.WordsAt m0.dmem (reg m0 .rdi) bcw) : bcw = bcOf m0 := by
  have := NativeRustcVm.wordsOf_of_wordsAt h
  rw [hl] at this
  exact this.symm

theorem pubOf_eq {m0 : MachineData} {P : Vector UInt64 4}
    (h : NativeRustcVm.WordsAt m0.dmem (reg m0 .rdx) P.toList) : P = pubOf m0 := by
  apply Vector.ext
  intro i hi
  have hw := NativeRustcVm.WordsAt.getElem h (i := i) (by simpa using hi)
  simp only [pubOf, Vector.getElem_ofFn]
  rw [NativeRustcVm.wordOf_of_wordAt hw]
  simp

variable [Host] {k : Nat}

theorem lbl_entry (hp : Placed Vm.Verify.code k) : Labels.label NativeRustcVmX64.Vm.Verify.entryLabel = Host.addrOf (k + NativeRustcVmX64.Vm.Verify.b0Offset) :=
  hp.label NativeRustcVmX64.Vm.Verify.entry_at

end

/-- After `seed`: the frame, RSP at offset `8`, the memory changed only in the stack, the
arguments in RBX, R12 to R15, the seed's lanes at the `TState`. -/
public structure SA (m0 d : MachineData) : Prop where
  frame : Frame m0 816 Verify.slots 8 d
  same : NativeRustcVm.SameOutside m0.dmem d.dmem
    (NativeRustcVm.InRange (stackBelow m0 18704) 18704)
  rbx : reg d .rbx = reg m0 .rcx
  r12 : reg d .r12 = reg m0 .rsi
  r13 : reg d .r13 = reg m0 .rdi
  r14 : reg d .r14 = reg m0 .r8
  r15 : reg d .r15 = reg m0 .rdx
  rbp : reg d .rbp = tOf m0
  seed : NativeRustcVm.WordsAt d.dmem (tOf m0) (seed (bcOf m0).toArray (pubOf m0)).toList

/-- After `verify_execution`: the frame, the memory changed only in the stack and the working
area, the `Decoded` in RBX, the walk's success in AL, its last state in the `TState`. -/
public structure SB (a : DecArea) (stream : Array EW) (openings : Array (Array OpeningW))
    (m0 d : MachineData) : Prop where
  frame : Frame m0 816 Verify.slots 8 d
  same : NativeRustcVm.SameOutside m0.dmem d.dmem
    (fun q ↦ NativeRustcVm.InRange (stackBelow m0 18704) 18704 q ∨
      NativeRustcVm.InRange (reg m0 .r8) workAreaBytes q)
  rbx : reg d .rbx = reg m0 .rcx
  ok : OkAl d (run m0 stream openings).isSome
  next : NextAt d.dmem (tOf m0) a (run m0 stream openings)

end NativeRustcVmX64.Top.Verify
