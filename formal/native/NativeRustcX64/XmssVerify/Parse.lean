module

public import NativeRustcX64.XmssVerify.Copy
public import NativeRustcX64.XmssVerify.Model

/-!
# `xmss_verify`: parsing the signature (x86-64)

Block 3 stores the key and a slice descriptor `(signature + 4, 2400)` in the frame, then calls
`LayerSignature::read` for the bottom layer. Block 4 reads the top layer from the updated slice.
The leaf index remains in RBP, the public parameter pointer in R15.
-/

namespace NativeRustcX64.Xmss.XmssVerify

open NativeRustcX64.Sym LeanVM.Protocol.KeccakHash NativeRustc.Xmss

set_option Elab.async false

@[expose] public section

/-- At block 5: the key, the message, the leaf index and the layers in the frame. -/
structure Parsed (w : Nat → UInt64) (m₀ m : MachineData) : Prop where
  common : Common m₀ m
  rsp : rspOf m = ad m₀ (fr + 24)
  r15 : reg m .r15 = ad m₀ (fr + 56)
  r12 : reg m .r12 = ad m₀ (fr + 3356)
  r13 : reg m .r13 = (w 8).toBitVec
  pk : BytesAt m.dmem (ad m₀ (fr + 40)) (pkB w)
  msg : BytesAt m.dmem (ad m₀ (fr + 152)) (msgB w)
  rbp : reg m .rbp = u32W (w 8)
  bottom : BytesAt m.dmem (ad m₀ (fr + 3356)) (bottomL w).memBytes
  top : BytesAt m.dmem (ad m₀ (fr + 4556)) (topL w).memBytes

end

public section

theorem st3_facts : (after b3 st3).reg .rdi = some (.ptr 0 3356) ∧
    (after b3 st3).reg .rsi = some (.ptr 0 184) ∧
    (after b3 st3).reg .rsp = some (.ptr 0 16) ∧ (after b3 st3).reg .rbx = some (.ptr 0 184) ∧
    (after b3 st3).reg .r15 = some (.ptr 0 56) ∧
    (after b3 st3).reg .rbp = some (.reg .rbp) ∧
    (after b3 st3).reg .r12 = some (.ptr 0 3356) ∧ (after b3 st3).reg .r13 = some (.reg .r13) ∧
    writesBelow (after b3 st3) [(0, 5760)] = true ∧
    firstOverlap 0 152 32 (after b3 st3).mem = none ∧
    firstOverlap 0 952 2404 (after b3 st3).mem = none := by decide +kernel

theorem st3_pk : ∀ j < 4, ∀ u < 8, findWrite 0 (40 + 8 * j + u) (after b3 st3).mem =
    some (.reg ([Reg64.rax, .rcx, .rdx, .rsi].getD j .rax), u) := by decide +kernel

theorem st3_cursor : ∀ u < 8,
    findWrite 0 (184 + u) (after b3 st3).mem = some (.ptr 0 956, u) := by decide +kernel
theorem st3_length : ∀ u < 8,
    findWrite 0 (192 + u) (after b3 st3).mem = some (.lit 2400, u) := by decide +kernel

theorem st4_facts : (after b4 st4).reg .rdi = some (.ptr 0 4556) ∧
    (after b4 st4).reg .rsi = some (.ptr 0 184) ∧
    (after b4 st4).reg .rsp = some (.ptr 0 16) ∧
    (∀ r ∈ [Reg64.rbp, .r12, .r13, .r15], (after b4 st4).reg r = some (.reg r)) ∧
    writesBelow (after b4 st4) [(0, 24)] = true := by decide +kernel

/-! ## Bytes -/

theorem wordsBytes_map (f : Nat → UInt64) (n : Nat) :
    Native.Keccak.wordsBytes ((List.range n).map f) = ((List.range n).map (wordBytes ∘ f)).flatten := by
  simp [Native.Keccak.wordsBytes, List.flatMap, List.map_map]

theorem length_sigB (w : Nat → UInt64) : (sigB w).length = 2404 := by
  rw [sigB, sigBytes, List.length_append, NativeRustc.length_u32Bytes,
    Native.Keccak.Proof.length_wordsBytes]
  simp

theorem length_msgB (w : Nat → UInt64) : (msgB w).length = 32 := by
  rw [msgB, messageBytes, Native.Keccak.Proof.length_wordsBytes]
  simp

theorem length_pkB (w : Nat → UInt64) : (pkB w).length = 32 := by
  rw [pkB, pkBytes, Native.Keccak.Proof.length_wordsBytes]
  simp

theorem length_slice {bs : List UInt8} {o : Nat} (h : o + 16 ≤ bs.length) :
    (NativeRustc.slice bs o 16).length = 16 := by
  simp [NativeRustc.slice]; omega

theorem length_memBytes {bs : List UInt8} {c : Nat} (h : c + 1200 ≤ bs.length) :
    (takeLayer bs c).1.memBytes.length = 1200 := by
  simp only [LayerSignature.memBytes, takeLayer, List.length_append, List.length_flatten,
    List.map_map]
  have hs : ∀ n o, n * 16 + o ≤ 1200 → ((List.range n).map
      (List.length ∘ fun i => NativeRustc.slice bs (c + o + 16 * i) 16)).sum = 16 * n := by
    intro n o hno
    induction n with
    | zero => rfl
    | succ n ih =>
      rw [List.range_succ, List.map_append, List.sum_append, ih (by omega)]
      simp [length_slice (show c + o + 16 * n + 16 ≤ bs.length by omega)]
      omega
  have h1 := hs 16 944 (by omega)
  have h2 := hs 58 16 (by omega)
  simp only [Function.comp_def] at h1 h2 ⊢
  rw [h1, h2, length_slice (by omega)]

theorem leNat_wordBytes (x : UInt64) : NativeRustc.leNat (wordBytes x) = x.toNat := by
  have h := regBytes_eq_wordBytes x.toBitVec
  rw [show UInt64.ofBitVec x.toBitVec = x from rfl] at h
  rw [← h, leNat_eq_ofBytes]
  have := Sym.ofBytes_byteOf x.toBitVec 0 8
  simp only [Nat.zero_add, Nat.mul_zero, Nat.pow_zero, Nat.div_one] at this
  rw [Sym.ofBytes_natCast] at this
  unfold regBytes
  rw [Int.ofNat.inj this, Nat.mod_eq_of_lt x.toBitVec.isLt]
  rfl

/-- Reading a layer from a bounded view gives the layer at the corresponding original offset. -/
theorem takeLayer_slice (bs : List UInt8) (c : Nat) :
    (takeLayer (NativeRustc.slice bs c 1200) 0).1 = (takeLayer bs c).1 := by
  have hs (o : Nat) (ho : o + 16 ≤ 1200) :
      NativeRustc.slice (NativeRustc.slice bs c 1200) o 16 =
        NativeRustc.slice bs (c + o) 16 := by
    simp only [NativeRustc.slice, List.drop_take, List.drop_drop, List.take_take]
    rw [Nat.min_eq_left (by omega)]
  simp only [takeLayer, Nat.zero_add]
  congr 1
  · simpa using hs 0 (by omega)
  · apply List.map_congr_left
    intro j hj
    have hj' := List.mem_range.mp hj
    simpa [Nat.add_assoc] using hs (16 + 16 * j) (by omega)
  · apply List.map_congr_left
    intro j hj
    have hj' := List.mem_range.mp hj
    simpa [Nat.add_assoc] using hs (944 + 16 * j) (by omega)

/-- A byte view of a mapped signature slice. -/
theorem bytesOf_slice {d : DataMem} {a : BitVec 64} {bs : List UInt8}
    (h : BytesAt d a bs) {c n : Nat} (hc : c + n ≤ bs.length) :
    bytesOf d (a + BitVec.ofNat 64 c) n = NativeRustc.slice bs c n := by
  have hb : BytesAt d (a + BitVec.ofNat 64 c) (NativeRustc.slice bs c n) := by
    intro i hi
    simp only [NativeRustc.slice, List.length_take, List.length_drop] at hi
    rw [addr_add_addr, h (c + i) (by omega)]
    simp [NativeRustc.slice]
  have hl : (NativeRustc.slice bs c n).length = n := by
    simp [NativeRustc.slice]
    omega
  simpa [hl] using hb.bytesOf

section
variable [Labels] {w : Nat → UInt64} {m₀ m : MachineData}

omit [Labels] in
/-- The signature's bytes after the copy. -/
theorem sig_of (h : LoopAt w m₀ m 50) : BytesAt m.dmem (ad m₀ (fr + 952)) (sigB w) := by
  unfold sigB sigBytes
  rw [u32Bytes_toUInt32, wordsBytes_map]
  refine BytesAt.append h.li ?_
  rw [List.length_take, NativeRustc.length_wordBytes, ad_add]
  exact bytesAt_flatten 300 (fun _ _ => NativeRustc.length_wordBytes _) fun k hk => by
    rw [ad_add, show fr + 952 + min 4 8 + 8 * k = fr + 956 + 8 * k by simp]
    exact h.sig k (by omega)

omit [Labels] in
/-- The message's bytes after the copy. -/
theorem msg_of (h : LoopAt w m₀ m 50) : BytesAt m.dmem (ad m₀ (fr + 152)) (msgB w) := by
  unfold msgB messageBytes
  rw [wordsBytes_map]
  exact bytesAt_flatten 4 (fun _ _ => NativeRustc.length_wordBytes _) fun k hk => by
    rw [ad_add]
    exact h.msg k hk

/-- A byte of the frame region from RSP on is outside a callee's stack. -/
theorem not_stack (P : Pre w m₀) {q n x : Nat} (h : rspOf m = ad m₀ (fr + q))
    (hn : n ≤ fr + q) (hq : q ≤ x) (hx : x < 5816) :
    ¬InRange (stackBelow m n) n (ad m₀ (fr + x)) := by
  rw [stackBelow_at h hn]
  exact P.not_inRange_ad (by fro) (by fro) (by omega)

end

end

end NativeRustcX64.Xmss.XmssVerify
