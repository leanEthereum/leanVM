module

public import NativeRustcArm.SphincsVerify.Chains.Glue
public import NativeRustcArm.SphincsVerify.Chains.Exec
public import NativeRustcArm.Hasher.Bytes

/-!
# A chain's step: the frame's symbolic states

A fresh symbolic state `frameS k` for a state of the chains (`match_frameS`), the frame's bytes a
block writes (`frame_write_load`, `frame_write_lit`, `frame_write_val`, `frame_copy16`).
-/

namespace NativeRustcArm.SphincsVerifyProof.Chains

open NativeRustc NativeRustc.Sphincs NativeRustcArm.Sym

public section

theorem allOf_append {α : Type} {P : α → Prop} :
    ∀ {a : List α} {b : List α}, AllOf P a → AllOf P b → AllOf P (a ++ b)
  | [], _, _, hb => hb
  | _ :: _, _, ha, hb => ⟨ha.1, allOf_append ha.2 hb⟩

variable [Labels] {r : Run}

/-- A known register that is the frame's byte `o`. -/
theorem known_ptr {m : MachineData} {y : XReg} {o : Nat} (h : Run.RegIs m y (r.off o)) :
    (m.regs.getXReg y).toBitVec = (Sym.ptr 0 o).eval (r.env m) := by
  rw [eval_ptr0]
  exact h

/-- A known register that is a literal. -/
theorem known_lit {m : MachineData} {y : XReg} {c : Nat} (h : Run.RegIs m y (BitVec.ofNat 64 c)) :
    (m.regs.getXReg y).toBitVec = (Sym.lit c).eval (r.env m) := h

/-- **A fresh symbolic state for a state of the chains**: the registers `k` and `keptK`. -/
theorem match_frameS (hpre : r.Pre) {l : Nat} {x E : List UInt8} {m : MachineData}
    (hK : Keep r l x E m) {k : List (XReg × Sym)}
    (hk : AllOf (fun p ↦ (m.regs.getXReg p.1).toBitVec = p.2.eval (r.env m)) k) :
    Match (r.env m) (frameS k) m :=
  r.match_frame hpre hK.1 (known := k ++ keptK) (allOf_append hk
    ⟨known_ptr hK.1.2.1, hK.2.2.2.1, known_ptr hK.2.2.2.2.1, known_ptr hK.2.2.2.2.2.1,
      known_ptr hK.2.2.2.2.2.2.1, trivial⟩) trivial trivial trivial

/-! ## Bytes a block writes in the frame -/

theorem frame_write_load {m m' : MachineData} {S : SState} (hm : Match (r.env m) S m')
    {o o' n : Nat} (ho : o + n ≤ 21616) (hw : covers S.mem 0 o n (.load 0 o' n) = true)
    {bs : List UInt8} (hlen : bs.length = n) (hn : n ≤ 8) (h : BytesAt m.dmem (r.off o') bs) :
    BytesAt m'.dmem (r.off o) bs :=
  bytesAt_write_load hm (b := r.base) (sz := 21616) rfl ho hw hlen hn h

theorem frame_write_val {m m' : MachineData} {S : SState} (hm : Match (r.env m) S m')
    {o n : Nat} (ho : o + n ≤ 21616) {v : Sym} (hw : covers S.mem 0 o n v = true) :
    BytesAt m'.dmem (r.off o) ((List.range n).map (byteOf (v.eval (r.env m)))) :=
  bytesAt_write_val hm (b := r.base) (sz := 21616) rfl ho hw

theorem frame_write_lit {m m' : MachineData} {S : SState} (hm : Match (r.env m) S m')
    {o n : Nat} (ho : o + n ≤ 21616) {c : Nat} (hw : covers S.mem 0 o n (.lit c) = true) :
    BytesAt m'.dmem (r.off o) ((List.range n).map (byteOf (BitVec.ofNat 64 c))) :=
  bytesAt_write_lit hm (b := r.base) (sz := 21616) rfl ho hw

omit [Labels] in
theorem BytesAt.off_zero {d : DataMem} {o : Nat} {bs : List UInt8}
    (h : BytesAt d (r.off o + BitVec.ofNat 64 0) bs) : BytesAt d (r.off o) bs := by
  simpa using h

/-- **16 bytes copied** by two 8-byte loads and stores. -/
theorem frame_copy16 {m m' : MachineData} {S : SState} (hm : Match (r.env m) S m')
    {o o' : Nat} (ho : o + 16 ≤ 21616) (hw1 : covers S.mem 0 o 8 (.load 0 o' 8) = true)
    (hw2 : covers S.mem 0 (o + 8) 8 (.load 0 (o' + 8) 8) = true) {bs : List UInt8}
    (hlen : bs.length = 16) (h : BytesAt m.dmem (r.off o') bs) : BytesAt m'.dmem (r.off o) bs := by
  rw [← List.take_append_drop 8 bs]
  have h1 := frame_write_load hm (by omega) hw1 (bs := bs.take 8) (by simp [hlen]) (by decide)
    (BytesAt.off_zero (by simpa using BytesAt.slice h 0 8))
  have h2 := frame_write_load hm (by omega) hw2 (bs := bs.drop 8) (by simp [hlen]) (by decide)
    (by
      have := BytesAt.slice h 8 8
      rwa [r.off_add, List.take_of_length_le (by simp [hlen])] at this)
  refine BytesAt.append h1 ?_
  rw [List.length_take, Nat.min_eq_left (by omega), r.off_add]
  exact h2

/-- Each of the `n` bytes at `o` in region `r` is a byte of a zero literal's newest write
(decided on a literal state). -/
@[expose] def zeroAt (ws : List Write) (r o n : Nat) : Bool :=
  (List.range n).all fun i ↦ match findWrite r (o + i) ws with
    | some (.lit 0, _) => true
    | _ => false

/-- **Zeros written** in the frame. -/
theorem frame_write_zero {m m' : MachineData} {S : SState} (hm : Match (r.env m) S m')
    {o n : Nat} (ho : o + n ≤ 21616) (hz : zeroAt S.mem 0 o n = true) :
    BytesAt m'.dmem (r.off o) (List.replicate n 0) := by
  intro i hi
  rw [List.length_replicate] at hi
  simp only [zeroAt, List.all_eq_true, List.mem_range] at hz
  have h := hz i hi
  rw [List.getElem_replicate]
  show m'.dmem.get? (r.base + BitVec.ofNat 64 o + BitVec.ofNat 64 i) = _
  rw [addr_add, hm.mem 0 r.base 21616 rfl (o + i) (by omega)]
  unfold memByte
  revert h
  cases findWrite 0 (o + i) S.mem with
  | none => simp
  | some vt =>
    obtain ⟨v, t⟩ := vt
    cases v <;> simp_all
    rename_i c
    rcases c with _ | c
    · simp [Sym.eval, byteOf]
    · simp at *

omit [Labels] in
/-- **Bytes side by side** in the frame. -/
theorem BytesAt.cat {d : DataMem} {o o' : Nat} {a b : List UInt8} (h1 : BytesAt d (r.off o) a)
    (h2 : BytesAt d (r.off o') b) (ho : o' = o + a.length) : BytesAt d (r.off o) (a ++ b) :=
  BytesAt.append h1 (by rw [r.off_add, ← ho]; exact h2)

omit [Labels] in
/-- **A slice of a copy**: bytes `c .. c + t` of a copy of the `n` bytes at `o'` are those at
`o' + c`. -/
theorem copy_slice {d d' : DataMem} {o o' n c : Nat} {bs : List UInt8}
    (hB : BytesAt d' (r.off o) (bytesOf d (r.off o') n)) (hc : c + bs.length ≤ n)
    (h : BytesAt d (r.off (o' + c)) bs) : BytesAt d' (r.off (o + c)) bs := by
  have := BytesAt.slice hB c bs.length
  rw [← Hasher.bytesOf_add _ _ hc, r.off_add, r.off_add, bytesOf_of_bytesAt h] at this
  exact this

end

/-- Closes the frame's offset arithmetic with the lengths of literal byte lists. -/
macro "len_tac" : tactic =>
  `(tactic| ((try simp only [List.length_replicate, List.length_map, List.length_range,
    List.length_append]) <;> omega))

end NativeRustcArm.SphincsVerifyProof.Chains
