module

public import NativeRustcX64.SphincsVerify.Parse.Prologue

/-!
# The words' loops: a turn and a counter (x86-64)

`WS pre m`: the frame, the message at `2008`, the raw signature's first bytes `pre` at `11404`,
RBX the context, the key in registers. A word loop's turn (`turnS`) copies `q` input words from
`s` to the frame's `d` (`copy_turn`); a counter block (`ctxS`) stores an input word's low 4 bytes
big-endian (`low4_counter`).
-/

namespace NativeRustcX64.SphincsVerifyProof.Parse

open NativeRustc NativeRustc.Sphincs NativeRustcX64.Sym LeanVM.Protocol.KeccakHash

@[expose] public section

/-- **The words' loops' state**: the raw signature's first bytes `pre` at `11404`. -/
def WS (r : Run) (pre : List UInt8) (m : MachineData) : Prop :=
  r.Frame m ∧ BytesAt m.dmem (r.off 2008) r.msg ∧ BytesAt m.dmem (r.off 11404) pre ∧
    Run.RegIs m .rbx (ctx r) ∧ KeyRegs r m

/-- The registers the words' loops keep. -/
abbrev wsRegs : List Reg64 := [.rsp, .rbx, .r13, .r14, .r12, .rbp]

end

public section

theorem take4_low {x : UInt64} : Low4 x.toBitVec (be32 x.toUInt32).reverse := Low4.word

/-- **A word's low 4 bytes, loaded**. -/
theorem Low4.load4 [Labels] {env : Env} {r o : Nat} {x : UInt64}
    (h : BytesAt env.mem0 (env.base r + BitVec.ofNat 64 o) (wordBytes x)) :
    Low4 (env.load r o 4) (be32 x.toUInt32).reverse := by
  refine ⟨take4_low.1, fun t ht ↦ ?_⟩
  rw [byteOf_load ht (by decide), ← take4_low.2 t ht, ← load_word h, byteOf_load (by omega) le_rfl]

theorem wsRegs_keep {r : Run} {pre : List UInt8} {m m' : MachineData}
    (h : ∀ x ∈ wsRegs, m'.regs.get64 x = m.regs.get64 x) (hw : WS r pre m) :
    Run.RegIs m' .rbx (ctx r) ∧ KeyRegs r m' := by
  obtain ⟨-, -, -, hbx, h14, h15, h13, hbp⟩ := hw
  unfold Run.RegIs at *
  exact ⟨(h .rbx (by simp)).trans hbx, (h .r14 (by simp)).trans h14, (h .r12 (by simp)).trans h15,
    (h .r13 (by simp)).trans h13, (h .rbp (by simp)).trans hbp⟩

theorem rsp_keep {r : Run} {m m' : MachineData} (hF : r.Frame m)
    (h : ∀ x ∈ wsRegs, m'.regs.get64 x = m.regs.get64 x) : rspOf m' = r.base := by
  rw [rspOf, h .rsp (by simp)]
  exact hF.1

variable (r : Run) [Labels]

/-- **A word loop's turn**: the `8 q` bytes of the input words `s ..` copied to the frame's `d`,
the rest of the frame as it was, RSP and the words' registers kept. -/
theorem copy_turn (hpre : r.Pre) {pre : List UInt8} {m m' : MachineData} (hw : WS r pre m)
    {s q d : Nat} (hs : s + q ≤ 977) (hd : d + 8 * q ≤ 29352) {S₀ S' : SState}
    {vars : Nat → BitVec 64} {ret : BitVec 64}
    (hm : Match (Env.ofMachine m [(r.input + BitVec.ofNat 64 (8 * s), 8 * q), (r.off d, 8 * q)]
      vars ret) S₀ m)
    (hm' : Match (Env.ofMachine m [(r.input + BitVec.ofNat 64 (8 * s), 8 * q), (r.off d, 8 * q)]
      vars ret) S' m')
    (hwf : (Env.ofMachine m [(r.input + BitVec.ofNat 64 (8 * s), 8 * q), (r.off d, 8 * q)]
      vars ret).WF)
    (hc : copies S'.mem 1 0 0 0 (8 * q) = true) (hwr : writesIn S' 1 0 (8 * q) = true)
    (hk : keepsRegs wsRegs S₀ S' = true) :
    r.Frame m' ∧ BytesAt m'.dmem (r.off d) (wb r.w s q) ∧
      SameOutside m.dmem m'.dmem (InRange (r.off d) (8 * q)) ∧ Run.RegIs m' .rbx (ctx r) ∧
      KeyRegs r m' := by
  have hreg := keepsRegs_regs hm hm' hk
  obtain ⟨hF', hout⟩ := frame_of_hull r hpre hw.1 (ri := 1) (d := d) (lo := 0) (hi := 8 * q) rfl
    le_rfl (Nat.zero_le _) (by omega) hm' hwf hwr (rsp_keep hw.1 hreg)
  rw [Nat.add_zero, Nat.sub_zero] at hout
  refine ⟨hF', ?_, hout, wsRegs_keep hreg hw⟩
  have := copy hm' (r := 1) (o := 0) (r' := 0) (o' := 0) (n := 8 * q) rfl (by omega) hc
    (length_wb r.w s q)
    (by
      show BytesAt m.dmem (r.input + BitVec.ofNat 64 (8 * s) + BitVec.ofNat 64 0) _
      rw [show BitVec.ofNat 64 0 = 0#64 from rfl, BitVec.add_zero]
      exact input_words r hpre hw.1.2.2.1 hs)
  rwa [BitVec.add_zero] at this

/-- **A counter block**: the input word `k`'s low 4 bytes big-endian stored at the frame's `o`. -/
theorem low4_counter (hpre : r.Pre) {pre : List UInt8} {m m' : MachineData} (hw : WS r pre m)
    {k o : Nat} (hk : k < 977) (ho : o + 4 ≤ 29352)
    {S' : SState} {vars : Nat → BitVec 64} {ret : BitVec 64}
    (hm' : Match (Env.ofMachine m (regs3 r) vars ret) S' m')
    (hwf : (Env.ofMachine m (regs3 r) vars ret).WF)
    (hsp : S'.reg .rsp = some (.ptr 0 0)) (hfw : Run.frameWrites S' = true)
    (hwr : writesIn S' 0 o (o + 4) = true)
    (hl : holdsLow S'.mem 0 o (.un .trunc .W32 (.un .bswap .W32 (.load 2 (8 * k) 4))) = true) :
    r.Frame m' ∧ BytesAt m'.dmem (r.off o) (be32 (r.w k).toUInt32) ∧
      SameOutside m.dmem m'.dmem (InRange (r.off o) 4) := by
  have hF' := frame_of_block r hpre hw.1 rfl rfl hm' hwf hsp hfw
  have hout := sameOutside_hull hm' hwf (ri := 0) (B := r.base) (sz := 29408) (lo := o)
    (hi := o + 4) rfl (by omega) hwr
  rw [Nat.add_sub_cancel_left] at hout
  refine ⟨hF', ?_, hout⟩
  refine bytesAt_low hm' (B := r.base) (sz := 29408) rfl (by omega) hl ?_
  have hword := input_word r hpre hw.1.2.2.1 (k := k) (o := 8 * k) rfl hk
  have h4 := Low4.load4 (env := Env.ofMachine m (regs3 r) vars ret) (r := 2) (o := 8 * k) hword
  have := (h4.bswap).trunc
  rwa [List.reverse_reverse] at this

end

end NativeRustcX64.SphincsVerifyProof.Parse
