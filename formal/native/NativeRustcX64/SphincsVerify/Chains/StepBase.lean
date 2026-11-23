module

public import NativeRustcX64.SphincsVerify.Chains.Keep
public import NativeRustcX64.SphincsVerify.InlineTh.Final

/-!
# A chain's step on x86-64: the frame's bytes a block writes

The frame's bytes a block writes in the frame's environment (`frame_write_load`,
`frame_write_val`, `frame_copy16`, `frame_write_word`), a frame word a block loads (`load_word`),
the step's registers (`Regs`), the length obligations (`len_tac`).
-/

namespace NativeRustcX64.SphincsVerifyProof.Chains

open NativeRustc NativeRustc.Sphincs NativeRustcX64.Sym LeanVM.Protocol.KeccakHash

@[expose] public section

/-- Raw call targets at a chain boundary, restored by the final block of each step. -/
def Funcs [Labels] (m : MachineData) : Prop :=
  Run.RegIs m .rbx (Labels.label "memset").toBitVec ∧
    Run.RegIs m .r14 (Labels.label "memcpy").toBitVec

/-- The position, hasher A, and the register-held call targets at a step's head. -/
def Regs [Labels] (r : Run) (m : MachineData) (pos : Nat) : Prop :=
  Run.RegIs m .rsi (BitVec.ofNat 64 pos) ∧ Run.RegIs m .r12 (r.off 4096) ∧ Funcs m

end

public section

variable [Labels] {r : Run}

theorem frame_write_load {m m' : MachineData} {vars : Nat → BitVec 64} {ret : BitVec 64}
    {S : SState} (hm : Match (r.env m vars ret) S m') {o o' n : Nat} (ho : o + n ≤ frameRegion)
    (hw : covers S.mem 0 o n (.load 0 o' n) = true) {bs : List UInt8} (hlen : bs.length = n)
    (hn : n ≤ 8) (h : BytesAt m.dmem (r.off o') bs) : BytesAt m'.dmem (r.off o) bs :=
  bytesAt_write_load hm (b := r.base) (sz := frameRegion) rfl ho hw hlen hn h

theorem frame_write_val {m m' : MachineData} {vars : Nat → BitVec 64} {ret : BitVec 64}
    {S : SState} (hm : Match (r.env m vars ret) S m') {o n : Nat} (ho : o + n ≤ frameRegion)
    {v : Sym} (hw : covers S.mem 0 o n v = true) :
    BytesAt m'.dmem (r.off o) ((List.range n).map (byteOf (v.eval (r.env m vars ret)))) :=
  bytesAt_write_val hm (b := r.base) (sz := frameRegion) rfl ho hw

/-- **A word written**: the bytes of its value. -/
theorem frame_write_word {m m' : MachineData} {vars : Nat → BitVec 64} {ret : BitVec 64}
    {S : SState} (hm : Match (r.env m vars ret) S m') {o : Nat} (ho : o + 8 ≤ frameRegion)
    {v : Sym} (hw : covers S.mem 0 o 8 v = true) {w : UInt64}
    (hv : v.eval (r.env m vars ret) = w.toBitVec) : BytesAt m'.dmem (r.off o) (wordBytes w) := by
  have := frame_write_val hm ho hw
  rwa [hv, ← Hasher.wordBytes_ofBitVec] at this

/-- **16 bytes copied** in the frame. -/
theorem frame_copy16 {m m' : MachineData} {vars : Nat → BitVec 64} {ret : BitVec 64}
    {S : SState} (hm : Match (r.env m vars ret) S m') {o o' : Nat} (ho : o + 16 ≤ frameRegion)
    (hw1 : covers S.mem 0 o 8 (.load 0 o' 8) = true)
    (hw2 : covers S.mem 0 (o + 8) 8 (.load 0 (o' + 8) 8) = true) {bs : List UInt8}
    (hlen : bs.length = 16) (h : BytesAt m.dmem (r.off o') bs) : BytesAt m'.dmem (r.off o) bs :=
  copy16 hm (b := r.base) (sz := frameRegion) rfl ho hw1 hw2 hlen h

/-- **A frame word loaded.** -/
theorem load_word {m : MachineData} {vars : Nat → BitVec 64} {ret : BitVec 64} {o : Nat}
    {w : UInt64} (h : BytesAt m.dmem (r.off o) (wordBytes w)) :
    (Sym.load 0 o 8).eval (r.env m vars ret) = w.toBitVec := by
  show Env.load _ 0 o 8 = _
  rw [Env.load_of_bytesAt (NativeRustc.length_wordBytes _) h, ofInt_ofBytes_wordBytes]

omit [Labels] in
theorem toBitVec_toUInt64 {n : Nat} : n.toUInt64.toBitVec = BitVec.ofNat 64 n := rfl

end

/-- Closes the frame's offset arithmetic with the lengths of literal byte lists. -/
macro "len_tac" : tactic =>
  `(tactic| ((try simp only [List.length_replicate, List.length_map, List.length_range,
    List.length_append]) <;> omega))

end NativeRustcX64.SphincsVerifyProof.Chains
