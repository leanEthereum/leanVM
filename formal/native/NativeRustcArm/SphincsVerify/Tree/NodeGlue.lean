module

public import NativeRustcArm.SphincsVerify.Tree.NodeA

/-!
# The fold's node: what its stretches share

The node's registers every stretch keeps (`NRegs`: X19 the next height, X24 the layer's path, X27
the layer's word), through a block (`NRegs.of_match`) and a call (`NRegs.of_saved`); bytes inside
known bytes (`bytesAt_sub`); a word of known bytes as loaded (`load_sub`); the value at the end
of a block's branch (`pc_cond`).
-/

namespace NativeRustcArm.SphincsVerifyProof.Tree

open NativeRustc NativeRustc.Keccak NativeRustc.Sphincs NativeRustcArm.Sym NativeRustcArm
  LeanVM.Protocol.KeccakHash Native.Keccak
open NativeRustcArm.Sphincs.SphincsVerify

public section

variable (r : Run)

/-- **The node's registers**: X19 `z + 1`, X24 the layer's path, X27 the layer's word. -/
@[expose] def NRegs (l z : Nat) (m : MachineData) : Prop :=
  Run.RegIs m .X19 (BitVec.ofNat 64 (z + 1)) ∧ Run.RegIs m .X24 (r.off (12468 + 16 * pathStart l)) ∧
    Run.RegIs m .X27 (BitVec.ofNat 64 (l * 16777216))

variable {r}

theorem NRegs.of_match [Labels] {l z : Nat} {m m' : MachineData} {vars : Nat → BitVec 64}
    {S : SState} (h : NRegs r l z m) (hm : Match (r.env m vars) S m')
    (h19 : S.reg .X19 = some (.reg .X19)) (h24 : S.reg .X24 = some (.reg .X24))
    (h27 : S.reg .X27 = some (.reg .X27)) : NRegs r l z m' :=
  ⟨(hm.regs _ _ h19).trans h.1, (hm.regs _ _ h24).trans h.2.1, (hm.regs _ _ h27).trans h.2.2⟩

theorem NRegs.of_saved {l z : Nat} {m m' : MachineData} (h : NRegs r l z m) (hS : Saved m m') :
    NRegs r l z m' := by
  refine ⟨?_, ?_, ?_⟩ <;> unfold Run.RegIs <;> rw [hS.1 _ rfl]
  exacts [h.1, h.2.1, h.2.2]

theorem regIs_of_saved {x : XReg} (hx : calleeSaved x = true) {m m' : MachineData} {v : BitVec 64}
    (h : Run.RegIs m x v) (hS : Saved m m') : Run.RegIs m' x v := by
  unfold Run.RegIs; rw [hS.1 x hx]; exact h

/-- Bytes inside known bytes. -/
theorem bytesAt_sub {d : DataMem} {o : Nat} {bs : List UInt8} (h : BytesAt d (r.off o) bs)
    (i n : Nat) : BytesAt d (r.off (o + i)) ((bs.drop i).take n) := fun j hj ↦ by
  simp only [List.length_take, List.length_drop] at hj
  rw [Run.off_add, Nat.add_assoc, ← Run.off_add, h (i + j) (by omega)]
  simp [List.getElem_take, List.getElem_drop]

theorem rep_sub {n i k : Nat} {a : UInt8} (h : i + k ≤ n) :
    ((List.replicate n a).drop i).take k = List.replicate k a := by
  rw [List.drop_replicate, List.take_replicate, Nat.min_eq_left (by omega)]

/-- Zeros inside zeros. -/
theorem bytesAt_zero {d : DataMem} {o n : Nat} (h : BytesAt d (r.off o) (List.replicate n 0))
    {i k : Nat} (hik : i + k ≤ n) : BytesAt d (r.off (o + i)) (List.replicate k 0) := by
  have := bytesAt_sub h i k
  rwa [rep_sub hik] at this

/-- **The parts of a hasher's bytes** with a zero state, `T` buffered, `buf_len` `n`. -/
theorem hbytes_parts {d : DataMem} {o : Nat} {T : List UInt8} {n : Nat}
    (h : BytesAt d (r.off o) (List.replicate 200 0 ++ (T ++ (List.replicate (136 - T.length) 0 ++
      wordBytes n.toUInt64)))) (hT : T.length ≤ 136) :
    BytesAt d (r.off o) (List.replicate 200 0) ∧ BytesAt d (r.off (o + 200)) T ∧
      BytesAt d (r.off (o + 200 + T.length)) (List.replicate (136 - T.length) 0) ∧
      BytesAt d (r.off (o + 336)) (wordBytes n.toUInt64) := by
  have h1 := bytesAt_append_right h
  have h2 := bytesAt_append_right h1
  have h3 := bytesAt_append_right h2
  simp only [List.length_replicate, Run.off_add] at h1 h2 h3
  refine ⟨bytesAt_append_left h, bytesAt_append_left h1, bytesAt_append_left h2, ?_⟩
  rwa [show o + 200 + T.length + (136 - T.length) = o + 336 by omega] at h3

/-- **A hasher's bytes from its parts.** -/
theorem hbytes_of_parts {d : DataMem} {o : Nat} {T : List UInt8} {n : Nat} (hT : T.length ≤ 136)
    (h0 : BytesAt d (r.off o) (List.replicate 200 0)) (h1 : BytesAt d (r.off (o + 200)) T)
    (h2 : BytesAt d (r.off (o + 200 + T.length)) (List.replicate (136 - T.length) 0))
    (h3 : BytesAt d (r.off (o + 336)) (wordBytes n.toUInt64)) :
    BytesAt d (r.off o) (List.replicate 200 0 ++ (T ++ (List.replicate (136 - T.length) 0 ++
      wordBytes n.toUInt64))) := by
  refine bytesAt_cat (List.length_replicate ..) h0 (bytesAt_cat rfl h1 (bytesAt_cat
    (List.length_replicate ..) h2 ?_))
  rwa [show o + 200 + T.length + (136 - T.length) = o + 336 by omega]

/-- A word of known bytes, as loaded. -/
theorem load_sub {m : MachineData} {vars : Nat → BitVec 64} {o : Nat} {bs : List UInt8}
    (h : BytesAt m.dmem (r.off o) bs) {i : Nat} {v : UInt64}
    (hv : (bs.drop i).take 8 = wordBytes v) : (r.env m vars).load 0 (o + i) 8 = v.toBitVec := by
  apply load_word
  show BytesAt m.dmem (r.off (o + i)) (wordBytes v)
  rw [← hv]
  exact bytesAt_sub h i 8

theorem length_nodeAdrs (l z : Nat) : (r.nodeAdrs l z).length = 32 := by
  rw [Run.nodeAdrs, nodeAdrs_eq]; simp [be32, be64]

theorem length_children {l z : Nat} {cur : List UInt8} (hl : l < 3) (hz : z < heightOf l)
    (hc : cur.length = 16) : (r.children l cur z).length = 32 := by
  unfold Run.children; split <;> simp [hc, length_sibling r hl hz]

theorem length_seed : r.seed.length = 16 := by
  rw [Run.seed, Run.pk, PublicKey.fromBytes, List.length_take, length_pkBytes]
  rfl

theorem eval_ptr' [Labels] {m : MachineData} {vars : Nat → BitVec 64} (o : Nat) :
    (Sym.ptr 0 (o : Int)).eval (r.env m vars) = r.off o := eval_ptr o

/-- The pc after a conditional branch the block's condition decides. -/
theorem pc_cond [Labels] {env : Env} {c : SBool} {l : Label} {next : Int64} {st : MachineState}
    {b : Bool} (h : PcOk env (.cond c l) next st) (hc : c.eval env = b) :
    st.pc = if b then Labels.label l else next := by
  rw [← hc]; exact h

end

end NativeRustcArm.SphincsVerifyProof.Tree
