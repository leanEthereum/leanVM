module

public import NativeRustcArm.Code.Sphincs.SphincsVerify.Names

public import NativeRustcArm.SphincsVerify.Calls
public import NativeRustcArm.SphincsVerify.Rev
public import NativeRustcArm.SphincsVerify.Fors.Model
public import NativeRustcArm.SphincsVerify.Fors.Exec
public import NativeRustcArm.SphincsVerify.InlineTh.Final
public import NativeRustcArm.Hasher.Bytes
public import NativeRustcArm.SphincsVerify.Epilogue
public import NativeRustc.Sphincs.Digest

/-!
# The FORS region's glue

- the blocks' places in the program (`hb59`, ..., and `b67`'s and `b93`'s pieces) and the labels
  they branch to (`lbl_21`, ...);
- the frame's scratch (`Scr`: hashers A and B, the hash inputs and outputs) and what a block or
  a call writing only there keeps (`Keep`, `keep_of_match`, `keep_of_call`);
- what every state of the region keeps (`Base`: the frame, the inputs, the spills `384 .. 416`,
  the leaves, X20 `136`, X21 and X22 the hashers' buffers), and per tree (`TreeSt`: the spills
  `416`, `424`, the roots so far), through blocks and calls (`Base.of_match`, `Base.of_call`,
  `TreeSt.of_keep`);
- the words the region builds its addresses from (`kpW`, `treeW`) and their bytes;
- reading the frame's environment (`eval_ptr`, `bytes_load`, `write_bytes`, `match_lit`).
-/

namespace NativeRustcArm.SphincsVerifyProof.Fors

open NativeRustc NativeRustc.Keccak NativeRustc.Sphincs NativeRustcArm.Sym NativeRustcArm
  LeanVM.Protocol.KeccakHash Native.Keccak
open NativeRustcArm.Sphincs.SphincsVerify

/-! ## Definitions -/

@[expose] public section

/-- The frame's scratch: hasher A to the leaves' copy, hasher B to the roots. -/
def Scr (o : Nat) : Prop := (16400 ≤ o ∧ o < 25752) ∨ (26768 ≤ o ∧ o < 27808)

/-- A symbolic state's writes are in the scratch. -/
def scrW (S : SState) : Bool :=
  S.mem.all fun w ↦ w.r == 0 &&
    (decide (16400 ≤ w.off ∧ w.off + w.n ≤ 25752) || decide (26768 ≤ w.off ∧ w.off + w.n ≤ 27808))

/-- `m'` has `m`'s frame bytes outside the scratch. -/
def Keep (r : Run) (m m' : MachineData) : Prop :=
  ∀ o < 29376, ¬Scr o → m'.dmem.get? (r.off o) = m.dmem.get? (r.off o)

/-- The key pair's word: the index's low byte shifted to the word's top byte (`lsl w26, w20, #24`). -/
def kpW (r : Run) : BitVec 64 := UnOp.apply (.ubfm 8 7) .W32 (r.idx &&& 255).toBitVec

/-- The tree's word: the index's bytes reversed, shifted up a byte (`rev`, `lsl #8`). -/
def treeW (r : Run) : BitVec 64 := UnOp.apply (.ubfm 56 55) .W64 (UnOp.apply .rev .W64 r.idx.toBitVec)

/-- **What every state of the region keeps.** -/
structure Base (r : Run) (m : MachineData) : Prop where
  frame : r.Frame m
  inputs : r.Inputs m
  w384 : r.WordAt m 384 r.idx
  w392 : r.WordAt m 392 (r.addr 12900)
  w400 : r.WordAt m 400 (r.addr 25752)
  w408 : BytesAt m.dmem (r.off 408) (be64 (r.key 0).tree)
  leaves : BytesAt m.dmem (r.off 25752) (wordsBytes (r.leaves.map Nat.toUInt64))
  x20 : Run.RegIs m .X20 (BitVec.ofNat 64 136)
  x21 : Run.RegIs m .X21 (r.off 16600)
  x22 : Run.RegIs m .X22 (r.off 26968)

/-- **What a tree's states keep**: the spills `416` (its opening) and `424` (its leaf index), the
roots before it. -/
structure TreeSt (r : Run) (c : Nat) (m : MachineData) : Prop where
  base : Base r m
  hc : c < 24
  w416 : r.WordAt m 416 (r.addr (8244 + 176 * c))
  w424 : r.WordAt m 424 (r.leafOf c).toUInt64
  roots : BytesAt m.dmem (r.off 27808) ((List.range c).map r.forsRoot).flatten

end

/-! ## Places and labels -/

public section

theorem isInfixAt_sub {ds P : List Directive} {k : Nat} (h : ds.IsInfixAt P k) (a b : Nat)
    (hab : a + b ≤ ds.length) : ((ds.drop a).take b).IsInfixAt P (k + a) := by
  obtain ⟨t, ht⟩ := h
  refine ⟨(ds.drop a).drop b ++ t, ?_⟩
  rw [← List.append_assoc, List.take_append_drop, ← List.drop_append_of_le_length (by omega), ht,
    List.drop_drop]

variable [Host] {k : Nat}

theorem placed_infix {b : List Directive} {j : Nat} (hp : Placed code k) (hb : b.IsInfixAt code j)
    (hne : b ≠ []) : b.IsInfixAt Host.prog (k + j) :=
  hb.trans hp.1 hne

/-- A state at `a`, as the machine state of its data at `a`. -/
theorem ev_at {R : MachineState → Prop} {st : MachineState} {a : Int64} (h : st.pc = a)
    (k : Eventually (step1 Host.exe) R ⟨st.data, a⟩) : Eventually (step1 Host.exe) R st := by
  obtain ⟨d, p⟩ := st
  cases h
  exact k

theorem pc_true {env : Env} {l : Label} {next : Int64} {st : MachineState}
    (h : PcOk env (.cond (.lit true) l) next st) : st.pc = Labels.label l := by
  simpa [PcOk, SBool.eval] using h

theorem pc_false {env : Env} {l : Label} {next : Int64} {st : MachineState}
    (h : PcOk env (.cond (.lit false) l) next st) : st.pc = next := by
  simpa [PcOk, SBool.eval] using h

theorem pc_after {j j' : Nat} {ds : List Directive} (h : j + ds.length = j') :
    Host.addrOf (k + j + ds.length) = Host.addrOf (k + j') := by
  rw [Nat.add_assoc, h]

theorem hb59 (hp : Placed code k) : b59.IsInfixAt Host.prog (k + NativeRustcArm.Sphincs.SphincsVerify.b59Offset) :=
  placed_infix hp b59_in_code (by simp [b59])
theorem hb60 (hp : Placed code k) : b60.IsInfixAt Host.prog (k + NativeRustcArm.Sphincs.SphincsVerify.b60Offset) :=
  placed_infix hp b60_in_code (by simp [b60])
theorem hb61 (hp : Placed code k) : b61.IsInfixAt Host.prog (k + NativeRustcArm.Sphincs.SphincsVerify.b61Offset) :=
  placed_infix hp b61_in_code (by simp [b61])
theorem hb62 (hp : Placed code k) : b62.IsInfixAt Host.prog (k + NativeRustcArm.Sphincs.SphincsVerify.b62Offset) :=
  placed_infix hp b62_in_code (by simp [b62])
theorem hb63 (hp : Placed code k) : b63.IsInfixAt Host.prog (k + NativeRustcArm.Sphincs.SphincsVerify.b63Offset) :=
  placed_infix hp b63_in_code (by simp [b63])
theorem hb64 (hp : Placed code k) : b64.IsInfixAt Host.prog (k + NativeRustcArm.Sphincs.SphincsVerify.b64Offset) :=
  placed_infix hp b64_in_code (by simp [b64])
theorem hb65 (hp : Placed code k) : b65.IsInfixAt Host.prog (k + NativeRustcArm.Sphincs.SphincsVerify.b65Offset) :=
  placed_infix hp b65_in_code (by simp [b65])
theorem hb66 (hp : Placed code k) : b66.IsInfixAt Host.prog (k + NativeRustcArm.Sphincs.SphincsVerify.b66Offset) :=
  placed_infix hp b66_in_code (by simp [b66])
theorem hb67 (hp : Placed code k) : b67.IsInfixAt Host.prog (k + NativeRustcArm.Sphincs.SphincsVerify.b67Offset) :=
  placed_infix hp b67_in_code (by simp [b67])
theorem hb67a (hp : Placed code k) : b67a.IsInfixAt Host.prog (k + NativeRustcArm.Sphincs.SphincsVerify.b67Offset) := by
  have := isInfixAt_sub (hb67 hp) 0 18 (by decide)
  simp only [List.drop_zero, Nat.add_zero] at this
  exact this
theorem hb67b (hp : Placed code k) : b67b.IsInfixAt Host.prog (k + (NativeRustcArm.Sphincs.SphincsVerify.b67Offset + b67a.length)) :=
  isInfixAt_sub (hb67 hp) 18 1 (by decide)
theorem hb67c (hp : Placed code k) : b67c.IsInfixAt Host.prog (k + (NativeRustcArm.Sphincs.SphincsVerify.b67Offset + b67a.length + b67b.length)) :=
  isInfixAt_sub (hb67 hp) 19 5 (by decide)
theorem hb67d (hp : Placed code k) : b67d.IsInfixAt Host.prog (k + (NativeRustcArm.Sphincs.SphincsVerify.b67Offset + b67a.length + b67b.length + b67c.length)) :=
  isInfixAt_sub (hb67 hp) 24 1 (by decide)
theorem hb67e (hp : Placed code k) : b67e.IsInfixAt Host.prog (k + (NativeRustcArm.Sphincs.SphincsVerify.b67Offset + b67a.length + b67b.length + b67c.length + b67d.length)) := by
  have := isInfixAt_sub (hb67 hp) 25 15 (by decide)
  rwa [List.take_of_length_le (by decide)] at this
theorem hb68 (hp : Placed code k) : b68.IsInfixAt Host.prog (k + NativeRustcArm.Sphincs.SphincsVerify.b68Offset) :=
  placed_infix hp b68_in_code (by simp [b68])
theorem hb71 (hp : Placed code k) : b71.IsInfixAt Host.prog (k + NativeRustcArm.Sphincs.SphincsVerify.b71Offset) :=
  placed_infix hp b71_in_code (by simp [b71])
theorem hb72 (hp : Placed code k) : b72.IsInfixAt Host.prog (k + NativeRustcArm.Sphincs.SphincsVerify.b72Offset) :=
  placed_infix hp b72_in_code (by simp [b72])
theorem hb73 (hp : Placed code k) : b73.IsInfixAt Host.prog (k + NativeRustcArm.Sphincs.SphincsVerify.b73Offset) :=
  placed_infix hp b73_in_code (by simp [b73])
theorem hb74 (hp : Placed code k) : b74.IsInfixAt Host.prog (k + NativeRustcArm.Sphincs.SphincsVerify.b74Offset) :=
  placed_infix hp b74_in_code (by simp [b74])
theorem hb75 (hp : Placed code k) : b75.IsInfixAt Host.prog (k + NativeRustcArm.Sphincs.SphincsVerify.b75Offset) :=
  placed_infix hp b75_in_code (by simp [b75])
theorem hb76 (hp : Placed code k) : b76.IsInfixAt Host.prog (k + NativeRustcArm.Sphincs.SphincsVerify.b76Offset) :=
  placed_infix hp b76_in_code (by simp [b76])
theorem hb79 (hp : Placed code k) : b79.IsInfixAt Host.prog (k + NativeRustcArm.Sphincs.SphincsVerify.b79Offset) :=
  placed_infix hp b79_in_code (by simp [b79])
theorem hb80 (hp : Placed code k) : b80.IsInfixAt Host.prog (k + NativeRustcArm.Sphincs.SphincsVerify.b80Offset) :=
  placed_infix hp b80_in_code (by simp [b80])
theorem hb81 (hp : Placed code k) : b81.IsInfixAt Host.prog (k + NativeRustcArm.Sphincs.SphincsVerify.b81Offset) :=
  placed_infix hp b81_in_code (by simp [b81])
theorem hb82 (hp : Placed code k) : b82.IsInfixAt Host.prog (k + NativeRustcArm.Sphincs.SphincsVerify.b82Offset) :=
  placed_infix hp b82_in_code (by simp [b82])
theorem hb83 (hp : Placed code k) : b83.IsInfixAt Host.prog (k + NativeRustcArm.Sphincs.SphincsVerify.b83Offset) :=
  placed_infix hp b83_in_code (by simp [b83])
theorem hb84 (hp : Placed code k) : b84.IsInfixAt Host.prog (k + NativeRustcArm.Sphincs.SphincsVerify.b84Offset) :=
  placed_infix hp b84_in_code (by simp [b84])
theorem hb85 (hp : Placed code k) : b85.IsInfixAt Host.prog (k + NativeRustcArm.Sphincs.SphincsVerify.b85Offset) :=
  placed_infix hp b85_in_code (by simp [b85])
theorem hb88 (hp : Placed code k) : b88.IsInfixAt Host.prog (k + NativeRustcArm.Sphincs.SphincsVerify.b88Offset) :=
  placed_infix hp b88_in_code (by simp [b88])
theorem hb89 (hp : Placed code k) : b89.IsInfixAt Host.prog (k + NativeRustcArm.Sphincs.SphincsVerify.b89Offset) :=
  placed_infix hp b89_in_code (by simp [b89])
theorem hb90 (hp : Placed code k) : b90.IsInfixAt Host.prog (k + NativeRustcArm.Sphincs.SphincsVerify.b90Offset) :=
  placed_infix hp b90_in_code (by simp [b90])
theorem hb91 (hp : Placed code k) : b91.IsInfixAt Host.prog (k + NativeRustcArm.Sphincs.SphincsVerify.b91Offset) :=
  placed_infix hp b91_in_code (by simp [b91])
theorem hb92 (hp : Placed code k) : b92.IsInfixAt Host.prog (k + NativeRustcArm.Sphincs.SphincsVerify.b92Offset) :=
  placed_infix hp b92_in_code (by simp [b92])
theorem hb93 (hp : Placed code k) : b93.IsInfixAt Host.prog (k + NativeRustcArm.Sphincs.SphincsVerify.b93Offset) :=
  placed_infix hp b93_in_code (by simp [b93])
theorem hb93a (hp : Placed code k) : b93a.IsInfixAt Host.prog (k + NativeRustcArm.Sphincs.SphincsVerify.b93Offset) := by
  have := isInfixAt_sub (hb93 hp) 0 8 (by decide)
  simp only [List.drop_zero, Nat.add_zero] at this
  exact this
theorem hb93b (hp : Placed code k) : b93b.IsInfixAt Host.prog (k + (NativeRustcArm.Sphincs.SphincsVerify.b93Offset + b93a.length)) :=
  isInfixAt_sub (hb93 hp) 8 1 (by decide)
theorem hb93c (hp : Placed code k) : b93c.IsInfixAt Host.prog (k + (NativeRustcArm.Sphincs.SphincsVerify.b93Offset + b93a.length + b93b.length)) := by
  have := isInfixAt_sub (hb93 hp) 9 4 (by decide)
  rwa [List.take_of_length_le (by decide)] at this

theorem lbl_21 (hp : Placed code k) : Labels.label NativeRustcArm.Sphincs.SphincsVerify.label_21 = Host.addrOf (k + NativeRustcArm.Sphincs.SphincsVerify.b60Offset) :=
  hp.label NativeRustcArm.Sphincs.SphincsVerify.label_21_at
theorem lbl_22 (hp : Placed code k) : Labels.label NativeRustcArm.Sphincs.SphincsVerify.label_22 = Host.addrOf (k + NativeRustcArm.Sphincs.SphincsVerify.b67Offset) :=
  hp.label NativeRustcArm.Sphincs.SphincsVerify.label_22_at
theorem lbl_24 (hp : Placed code k) : Labels.label NativeRustcArm.Sphincs.SphincsVerify.label_24 = Host.addrOf (k + NativeRustcArm.Sphincs.SphincsVerify.b71Offset) :=
  hp.label NativeRustcArm.Sphincs.SphincsVerify.label_24_at
theorem lbl_25 (hp : Placed code k) : Labels.label NativeRustcArm.Sphincs.SphincsVerify.label_25 = Host.addrOf (k + NativeRustcArm.Sphincs.SphincsVerify.b72Offset) :=
  hp.label NativeRustcArm.Sphincs.SphincsVerify.label_25_at
theorem lbl_26 (hp : Placed code k) : Labels.label NativeRustcArm.Sphincs.SphincsVerify.label_26 = Host.addrOf (k + NativeRustcArm.Sphincs.SphincsVerify.b73Offset) :=
  hp.label NativeRustcArm.Sphincs.SphincsVerify.label_26_at
theorem lbl_30 (hp : Placed code k) : Labels.label NativeRustcArm.Sphincs.SphincsVerify.label_30 = Host.addrOf (k + NativeRustcArm.Sphincs.SphincsVerify.b79Offset) :=
  hp.label NativeRustcArm.Sphincs.SphincsVerify.label_30_at
theorem lbl_31 (hp : Placed code k) : Labels.label NativeRustcArm.Sphincs.SphincsVerify.label_31 = Host.addrOf (k + NativeRustcArm.Sphincs.SphincsVerify.b81Offset) :=
  hp.label NativeRustcArm.Sphincs.SphincsVerify.label_31_at
theorem lbl_32 (hp : Placed code k) : Labels.label NativeRustcArm.Sphincs.SphincsVerify.label_32 = Host.addrOf (k + NativeRustcArm.Sphincs.SphincsVerify.b82Offset) :=
  hp.label NativeRustcArm.Sphincs.SphincsVerify.label_32_at
theorem lbl_36 (hp : Placed code k) : Labels.label NativeRustcArm.Sphincs.SphincsVerify.label_36 = Host.addrOf (k + NativeRustcArm.Sphincs.SphincsVerify.b88Offset) :=
  hp.label NativeRustcArm.Sphincs.SphincsVerify.label_36_at

end

/-! ## Reading the frame's environment -/

public section

variable {r : Run}

theorem regIs_toNat {m : MachineData} {x : XReg} {n : Nat}
    (h : Run.RegIs m x (BitVec.ofNat 64 n)) (hn : n < 2 ^ 64) : (m.regs.getXReg x).toNat = n := by
  show (m.regs.getXReg x).toBitVec.toNat = n
  rw [h, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn]

theorem bytesAt_cat {d : DataMem} {o n : Nat} {p q : List UInt8} (hn : p.length = n)
    (hp : BytesAt d (r.off o) p) (hq : BytesAt d (r.off (o + n)) q) : BytesAt d (r.off o) (p ++ q) := by
  intro i hi
  by_cases h : i < p.length
  · rw [List.getElem_append_left h]
    exact hp i h
  · rw [List.getElem_append_right (by omega)]
    have := hq (i - p.length) (by simp at hi; omega)
    rwa [Run.off_add, show o + n + (i - p.length) = o + i by omega, ← Run.off_add] at this

theorem bytesAt_slice {d : DataMem} {o : Nat} {bs : List UInt8} (h : BytesAt d (r.off o) bs)
    (a n : Nat) : BytesAt d (r.off (o + a)) ((bs.drop a).take n) := by
  intro i hi
  simp only [List.length_take, List.length_drop] at hi
  rw [Run.off_add, show o + a + i = o + (a + i) by omega, ← Run.off_add, h (a + i) (by omega)]
  simp

theorem bytesAt_prefix {d : DataMem} {o : Nat} {p q : List UInt8} (h : BytesAt d (r.off o) (p ++ q)) :
    BytesAt d (r.off o) p := fun i hi ↦ by
  rw [h i (by simp; omega), List.getElem_append_left hi]

theorem bytesAt_suffix {d : DataMem} {o : Nat} {p q : List UInt8} (h : BytesAt d (r.off o) (p ++ q)) :
    BytesAt d (r.off (o + p.length)) q := fun i hi ↦ by
  rw [Run.off_add, show o + p.length + i = o + (p.length + i) by omega, ← Run.off_add,
    h (p.length + i) (by simp; omega), List.getElem_append_right (by omega)]
  simp

/-- **Bytes of a copy**: where `n` bytes from `b` were copied to `a`, the copy's bytes at `o` are
the source's. -/
theorem slice_copy {d d' : DataMem} {a b n o : Nat} {bs : List UInt8}
    (hcopy : BytesAt d' (r.off a) (bytesOf d (r.off b) n)) (hsrc : BytesAt d (r.off (b + o)) bs)
    (hl : o + bs.length ≤ n) : BytesAt d' (r.off (a + o)) bs := by
  have h := bytesAt_slice hcopy o bs.length
  rwa [← Hasher.bytesOf_add _ _ hl, Run.off_add, bytesOf_of_bytesAt hsrc] at h

/-- A literal word's bytes. -/
theorem lit_word (v : Nat) :
    (List.range 8).map (byteOf (BitVec.ofNat 64 v)) = wordBytes v.toUInt64 :=
  (Hasher.wordBytes_ofBitVec (BitVec.ofNat 64 v)).symm

theorem bytesOf_of_bytesAt' {d : DataMem} {a : BitVec 64} {bs : List UInt8} {n : Nat}
    (h : BytesAt d a bs) (hl : bs.length = n) : bytesOf d a n = bs := by
  subst hl
  exact bytesOf_of_bytesAt h

theorem bytesAt_eq_bytesOf {d : DataMem} {a : BitVec 64} {bs : List UInt8} (h : BytesAt d a bs) :
    bytesOf d a bs.length = bs := bytesOf_of_bytesAt h

/-- The bytes of a load of known bytes. -/
theorem bytes_load {m : MachineData} {vars : Nat → BitVec 64} {o n : Nat} {bs : List UInt8}
    (h : BytesAt m.dmem (r.off o) bs) (hl : bs.length = n) (hn : n ≤ 8) :
    (List.range n).map (byteOf ((r.env m vars).load 0 o n)) = bs := by
  subst hl
  apply List.ext_getElem (by simp)
  intro t h1 h2
  rw [List.getElem_map, List.getElem_range, byteOf_load h2 hn]
  show (m.dmem.get? (r.base + BitVec.ofNat 64 (o + t))).getD 0 = _
  rw [show r.base + BitVec.ofNat 64 (o + t) = r.off o + BitVec.ofNat 64 t by
    rw [Run.off_add]; rfl, h t h2]
  rfl

/-- A register's bytes, stored. -/
theorem bytes_reg (x : BitVec 64) : (List.range 8).map (byteOf x) = wordBytes (UInt64.ofBitVec x) :=
  (Hasher.wordBytes_ofBitVec x).symm

/-- A load of a word's bytes is the word. -/
theorem load_word {m : MachineData} {vars : Nat → BitVec 64} {o : Nat} {v : UInt64}
    (h : r.WordAt m o v) : (r.env m vars).load 0 o 8 = v.toBitVec := by
  rw [Env.load_of_bytesAt (bs := wordBytes v) (length_wordBytes v)
    (by show BytesAt m.dmem (r.base + BitVec.ofNat 64 o) _; exact h)]
  exact ofInt_ofBytes_wordBytes v

variable [Labels]

theorem eval_ptr {m : MachineData} {vars : Nat → BitVec 64} (o : Nat) :
    (Sym.ptr 0 (o : Int)).eval (r.env m vars) = r.off o := by
  show r.base + BitVec.ofInt 64 (o : Int) = r.base + BitVec.ofNat 64 o
  simp

/-- **A write's bytes** in the frame. -/
theorem write_bytes {m m' : MachineData} {vars : Nat → BitVec 64} {S : SState}
    (hm : Match (r.env m vars) S m') {o n : Nat} {v : Sym} (hle : o + n ≤ 29376)
    (hw : ∀ i < n, findWrite 0 (o + i) S.mem = some (v, i)) {bs : List UInt8}
    (hbs : (List.range n).map (byteOf (v.eval (r.env m vars))) = bs) :
    BytesAt m'.dmem (r.off o) bs :=
  hbs ▸ hm.bytesAt_write rfl hle hw

/-- A register a block leaves as its atom keeps its value. -/
theorem reg_of {m m' : MachineData} {rs : List (BitVec 64 × Nat)} {vars : Nat → BitVec 64}
    {S : SState} (hm : Match (Env.ofMachine m rs vars) S m') {x : XReg}
    (h : S.reg x = some (.reg x)) : m'.regs.getXReg x = m.regs.getXReg x :=
  UInt64.toBitVec_inj.mp (hm.regs x _ h)

/-- SP a block leaves as its atom keeps its value. -/
theorem sp_of {m m' : MachineData} {rs : List (BitVec 64 × Nat)} {vars : Nat → BitVec 64}
    {S : SState} (hm : Match (Env.ofMachine m rs vars) S m') (h : S.sp = .sp) :
    m'.regs.SP = m.regs.SP := by
  have := hm.sp
  rw [h] at this
  exact UInt64.toBitVec_inj.mp this

/-- **A value written**, the value read off the state's newest write at `o`. -/
theorem write_val {m m' : MachineData} {vars : Nat → BitVec 64} {S : SState}
    (hm : Match (r.env m vars) S m') {o n : Nat} {v : Sym}
    (_hv : (findWrite 0 o S.mem).map Prod.fst = some v) (hle : o + n ≤ 29376)
    (hw : ∀ i < n, findWrite 0 (o + i) S.mem = some (v, i)) {bs : List UInt8}
    (hbs : (List.range n).map (byteOf (v.eval (r.env m vars))) = bs) :
    BytesAt m'.dmem (r.off o) bs :=
  write_bytes hm hle hw hbs

/-- **A load written back**: the bytes it loaded. -/
theorem write_load {m m' : MachineData} {vars : Nat → BitVec 64} {S : SState}
    (hm : Match (r.env m vars) S m') {o o' n : Nat} (hle : o + n ≤ 29376) (hn : n ≤ 8)
    (hw : ∀ i < n, findWrite 0 (o + i) S.mem = some (.load 0 o' n, i)) {bs : List UInt8}
    (hl : bs.length = n) (h : BytesAt m.dmem (r.off o') bs) : BytesAt m'.dmem (r.off o) bs :=
  write_bytes hm hle hw (bytes_load h hl hn)

/-- **A register written**: its low bytes. -/
theorem write_reg {m m' : MachineData} {vars : Nat → BitVec 64} {S : SState}
    (hm : Match (r.env m vars) S m') {o n : Nat} (hle : o + n ≤ 29376) {x : XReg}
    (hw : ∀ i < n, findWrite 0 (o + i) S.mem = some (.reg x, i)) {bs : List UInt8}
    (hbs : (List.range n).map (byteOf (m.regs.getXReg x).toBitVec) = bs) :
    BytesAt m'.dmem (r.off o) bs :=
  write_bytes hm hle hw hbs

/-- The `n` bytes at `o` of region 0 are each the newest write of a literal zero (decided on a
literal state). -/
@[expose] def zeroW (ws : List Write) (o n : Nat) : Bool :=
  (List.range n).all fun i ↦ match findWrite 0 (o + i) ws with
    | some (.lit 0, _) => true
    | _ => false

/-- **Zeros written.** -/
theorem write_zeros {m m' : MachineData} {vars : Nat → BitVec 64} {S : SState}
    (hm : Match (r.env m vars) S m') {o n : Nat} (hle : o + n ≤ 29376) (hz : zeroW S.mem o n = true) :
    BytesAt m'.dmem (r.off o) (List.replicate n 0) := by
  intro i hi
  rw [List.length_replicate] at hi
  have h := List.all_eq_true.mp hz i (List.mem_range.mpr hi)
  rw [Run.off_add, show r.off (o + i) = r.base + BitVec.ofNat 64 (o + i) from rfl,
    hm.mem 0 r.base 29376 rfl (o + i) (by omega), List.getElem_replicate]
  unfold memByte
  split at h
  · rename_i t hf
    rw [hf]
    simp only [Sym.eval, Option.some.injEq]
    rw [byteOf_mod]
    simp
  · cases h

/-- **A state with a write the memory already holds**: where `S` has no write, the state with
`v`'s low `n` bytes at `o` in region `r` describes `m` too, when `m` has those bytes there. -/
theorem match_lit {env : Env} {S : SState} {m : MachineData} (hm : Match env S m)
    (hS : S.mem = []) {r o n : Nat} {v : Sym} {b : BitVec 64} {sz : Nat}
    (hb : env.regions[r]? = some (b, sz))
    (hv : ∀ i < n, m.dmem.get? (b + BitVec.ofNat 64 (o + i)) = some (byteOf (v.eval env) i)) :
    Match env { S with mem := [⟨r, o, n, v⟩] } m where
  regs := hm.regs
  sp := hm.sp
  flags := hm.flags
  regions := hm.regions
  labels := hm.labels
  bounds := hm.bounds
  aliases := hm.aliases
  outside := hm.outside
  mem r' b' n' hb' i hi := by
    rw [hm.mem r' b' n' hb' i hi, hS]
    show memByte env [] r' b' i = memByte env [⟨r, o, n, v⟩] r' b' i
    by_cases h : r = r' ∧ o ≤ i ∧ i < o + n
    · obtain ⟨rfl, h1, h2⟩ := h
      rw [hb] at hb'
      cases hb'
      have := hv (i - o) (by omega)
      rw [show o + (i - o) = i by omega, hm.mem r b _ hb i hi, hS] at this
      rw [this]
      simp [memByte, findWrite_cons, h1, h2]
    · simp only [memByte, findWrite_cons]
      rw [Hasher.ite_neg' h]

/-- A frame word whose bytes are a literal's, for `match_lit`. -/
theorem lit_bytes {m : MachineData} {vars : Nat → BitVec 64} {o v : Nat}
    (h : BytesAt m.dmem (r.off o) (wordBytes v.toUInt64)) :
    ∀ i < 8, m.dmem.get? (r.base + BitVec.ofNat 64 (o + i)) =
      some (byteOf ((Sym.lit v).eval (r.env m vars)) i) := by
  intro i hi
  have hb := h i (by rw [length_wordBytes]; exact hi)
  have this := bytes_reg (BitVec.ofNat 64 v)
  have hw : UInt64.ofBitVec (BitVec.ofNat 64 v) = v.toUInt64 := rfl
  rw [hw] at this
  have e : (wordBytes v.toUInt64)[i]'(by rw [length_wordBytes]; exact hi) =
      byteOf (BitVec.ofNat 64 v) i := by
    rw [List.getElem_of_eq this.symm]
    simp
  rw [show r.base + BitVec.ofNat 64 (o + i) = r.off o + BitVec.ofNat 64 i by rw [Run.off_add]; rfl,
    hb, e]
  rfl

end

/-! ## The scratch -/

public section

variable {r : Run}

theorem Keep.refl (m : MachineData) : Keep r m m := fun _ _ _ ↦ rfl

theorem Keep.trans {m₁ m₂ m₃ : MachineData} (h₁ : Keep r m₁ m₂) (h₂ : Keep r m₂ m₃) :
    Keep r m₁ m₃ := fun o ho hs ↦ (h₂ o ho hs).trans (h₁ o ho hs)

theorem Keep.of_eq {m m' : MachineData} (h : m'.dmem = m.dmem) : Keep r m m' :=
  fun _ _ _ ↦ by rw [h]

/-- **Bytes outside the scratch are kept.** -/
theorem Keep.bytesAt {m m' : MachineData} (hk : Keep r m m') {o : Nat} {bs : List UInt8}
    (h : BytesAt m.dmem (r.off o) bs) (ho : o + bs.length ≤ 29376)
    (hs : ∀ i < bs.length, ¬Scr (o + i)) : BytesAt m'.dmem (r.off o) bs := fun i hi ↦ by
  rw [Run.off_add, hk _ (by omega) (hs i hi), ← Run.off_add]
  exact h i hi

theorem frameWrites_of_scrW {S : SState} (h : scrW S = true) : Run.frameWrites S = true := by
  simp only [scrW, Run.frameWrites, List.all_eq_true, Bool.and_eq_true, beq_iff_eq,
    Bool.or_eq_true, decide_eq_true_eq] at h ⊢
  intro w hw
  obtain ⟨h0, h1⟩ := h w hw
  exact ⟨h0, by omega⟩

section
variable [Labels]

/-- **A block writing in the scratch** keeps the rest. -/
theorem keep_of_match (hpre : r.Pre) {m m' : MachineData} {vars : Nat → BitVec 64}
    {S : SState} (hm : Match (r.env m vars) S m') (hwf : (r.env m vars).WF)
    (hw : scrW S = true) : Keep r m m' := by
  intro o ho hs
  have hb := r.base_toNat hpre
  have := r.m0.regs.SP.toNat_lt
  have hoff := r.off_toNat hpre (a := o) (by omega)
  refine hm.get?_mem0 hwf fun ⟨w, hwm, b, sz, hr, h1, h2⟩ ↦ ?_
  simp only [scrW, List.all_eq_true, Bool.and_eq_true, beq_iff_eq, Bool.or_eq_true,
    decide_eq_true_eq] at hw
  obtain ⟨hr0, hwr⟩ := hw w hwm
  rw [hr0] at hr
  cases hr
  rw [hoff] at h1 h2
  unfold Scr at hs
  omega

/-- **A call writing in the scratch** keeps the rest. -/
theorem keep_of_call (hpre : r.Pre) {m m' : MachineData} (hF : r.Frame m) {a n N : Nat}
    (ha : a + n ≤ 29376) (hN : N ≤ finalizeStack)
    (hout : SameOutside m.dmem m'.dmem (r.CallOut m a n N)) (hs : ∀ o, a ≤ o → o < a + n → Scr o) :
    Keep r m m' := fun o ho hso ↦
  hout _ (r.not_callOut hpre hF ha hN ho (by
    by_contra h
    exact hso (hs o (by omega) (by omega))))

end

/-! ## `keccak_f` -/

/-- **`keccak_f(a)`**'s precondition, the state at the frame's `a`. -/
theorem keccakF_pre [Labels] (hpre : r.Pre) {m : MachineData} (hF : r.Frame m) {a : Nat}
    (h0 : Run.RegIs m .X0 (r.off a)) (ha : a + 200 ≤ 29376) : KeccakFPre m := by
  simp only [KeccakFPre]
  rw [← getXReg_X0, h0]
  have hN : keccakFStack ≤ finalizeStack := by decide
  obtain ⟨m1, w1⟩ := r.frame_mapped hpre hF ha
  exact ⟨r.stackOk hpre hF hN, r.rcAt hpre hF hN, m1, w1, r.apart_off_below hpre hF ha hN,
    r.apart_rc hpre ha⟩

/-- **After `keccak_f(a)`**: the permuted state, the rest kept. -/
theorem keccakF_out [Labels] {m m' : MachineData} {a : Nat} (h0 : Run.RegIs m .X0 (r.off a))
    (h : KeccakFPost m m') :
    BytesAt m'.dmem (r.off a) (Keccak.keccakF (bytesOf m.dmem (r.off a) 200)) ∧
      SameOutside m.dmem m'.dmem (r.CallOut m a 200 keccakFStack) ∧ Saved m m' := by
  simp only [KeccakFPost] at h
  rw [← getXReg_X0, h0] at h
  exact h

/-! ## What the region keeps -/

theorem length_pkBytes (w : Nat → UInt64) : (pkBytes w).length = 32 := by
  rw [pkBytes, Proof.length_wordsBytes]
  simp

theorem length_leavesMem : (wordsBytes (r.leaves.map Nat.toUInt64)).length = 192 := by
  rw [Proof.length_wordsBytes, List.length_map]
  have : r.leaves.length = 24 := by
    show (digestFields _).2.length = 24
    simp [digestFields]
  omega

theorem length_be64 (x : UInt64) : (be64 x).length = 8 := rfl
theorem length_be32 (x : UInt32) : (be32 x).length = 4 := rfl

/-- `m'` has `m`'s frame bytes below the scratch and those of the leaves. -/
@[expose] def Low (r : Run) (m m' : MachineData) : Prop :=
  ∀ o, (o < 416 ∨ (432 ≤ o ∧ o < 16400) ∨ (25752 ≤ o ∧ o < 25944)) →
    m'.dmem.get? (r.off o) = m.dmem.get? (r.off o)

theorem Keep.low {m m' : MachineData} (hk : Keep r m m') : Low r m m' :=
  fun o ho ↦ hk o (by omega) (by unfold Scr; omega)

theorem Low.trans {m₁ m₂ m₃ : MachineData} (h₁ : Low r m₁ m₂) (h₂ : Low r m₂ m₃) :
    Low r m₁ m₃ := fun o ho ↦ (h₂ o ho).trans (h₁ o ho)

theorem Low.bytesAt {m m' : MachineData} (hk : Low r m m') {o : Nat} {bs : List UInt8}
    (h : BytesAt m.dmem (r.off o) bs) (_ho : o + bs.length ≤ 29376)
    (hs : ∀ i < bs.length, o + i < 416 ∨ (432 ≤ o + i ∧ o + i < 16400) ∨
      (25752 ≤ o + i ∧ o + i < 25944)) :
    BytesAt m'.dmem (r.off o) bs := fun i hi ↦ by
  rw [Run.off_add, hk _ (hs i hi), ← Run.off_add]
  exact h i hi

/-- **`Base` across a change** below the scratch and the leaves' end, with X20, X21, X22 kept. -/
theorem Base.of_keep {m m' : MachineData} (hB : Base r m) (hk : Low r m m') (hF : r.Frame m')
    (h20 : m'.regs.getXReg .X20 = m.regs.getXReg .X20)
    (h21 : m'.regs.getXReg .X21 = m.regs.getXReg .X21)
    (h22 : m'.regs.getXReg .X22 = m.regs.getXReg .X22) : Base r m' where
  frame := hF
  inputs := ⟨hk.bytesAt hB.inputs.1 (by rw [length_pkBytes]; omega) (fun i hi ↦ by
      rw [length_pkBytes] at hi; omega),
    hk.bytesAt hB.inputs.2.1 (by rw [Run.length_sigMem]; omega) (fun i hi ↦ by
      rw [Run.length_sigMem] at hi; omega),
    hk.bytesAt hB.inputs.2.2 (by rw [length_wordBytes]; omega) (fun i hi ↦ by
      rw [length_wordBytes] at hi; omega)⟩
  w384 := hk.bytesAt hB.w384 (by rw [length_wordBytes]; omega) (fun i hi ↦ by
      rw [length_wordBytes] at hi; omega)
  w392 := hk.bytesAt hB.w392 (by rw [length_wordBytes]; omega) (fun i hi ↦ by
      rw [length_wordBytes] at hi; omega)
  w400 := hk.bytesAt hB.w400 (by rw [length_wordBytes]; omega) (fun i hi ↦ by
      rw [length_wordBytes] at hi; omega)
  w408 := hk.bytesAt hB.w408 (by rw [length_be64]; omega) (fun i hi ↦ by
      rw [length_be64] at hi; omega)
  leaves := hk.bytesAt hB.leaves (by rw [length_leavesMem]; omega) (fun i hi ↦ by
      rw [length_leavesMem] at hi; omega)
  x20 := by rw [Run.RegIs, h20]; exact hB.x20
  x21 := by rw [Run.RegIs, h21]; exact hB.x21
  x22 := by rw [Run.RegIs, h22]; exact hB.x22

theorem length_roots (c : Nat) (hc : ∀ i < c, (r.forsRoot i).length = 16) :
    ((List.range c).map r.forsRoot).flatten.length = 16 * c := by
  rw [length_flatten_uniform (n := 16) _ (by
    intro x hx
    rw [List.mem_map] at hx
    obtain ⟨i, hi, rfl⟩ := hx
    exact hc i (List.mem_range.mp hi)), List.length_map, List.length_range]

/-- `th`'s 16 bytes. -/
theorem length_th (seed adrs m : List UInt8) : (th seed adrs m).length = 16 := by
  rw [th, List.length_take, length_hashBytes]
  rfl

theorem length_forsUpTo (c z : Nat) : (r.forsUpTo c z).length = 16 := by
  induction z with
  | zero => exact length_th _ _ _
  | succ z _ => rw [Run.forsUpTo_succ]; exact length_th _ _ _

theorem length_forsRoot {c : Nat} (hc : c < 24) : (r.forsRoot c).length = 16 := by
  rw [Run.forsRoot_eq r hc]
  exact length_forsUpTo c 10

/-- **`TreeSt` across a change** outside the scratch. -/
theorem TreeSt.of_keep {c : Nat} {m m' : MachineData} (hT : TreeSt r c m) (hB : Base r m')
    (hk : Keep r m m') : TreeSt r c m' where
  base := hB
  hc := hT.hc
  w416 := hk.bytesAt hT.w416 (by rw [length_wordBytes]; omega) (fun i hi ↦ by
      rw [length_wordBytes] at hi; unfold Scr; omega)
  w424 := hk.bytesAt hT.w424 (by rw [length_wordBytes]; omega) (fun i hi ↦ by
      rw [length_wordBytes] at hi; unfold Scr; omega)
  roots := by
    have hl := length_roots (r := r) c fun i hi ↦ length_forsRoot (by have := hT.hc; omega)
    have := hT.hc
    exact hk.bytesAt hT.roots (by rw [hl]; omega) (fun i hi ↦ by rw [hl] at hi; unfold Scr; omega)

section
variable [Labels]

/-- **`Base` after a block** in the frame writing in the scratch and keeping X20, X21, X22. -/
theorem Base.of_match (hpre : r.Pre) {m m' : MachineData} (hB : Base r m) {vars : Nat → BitVec 64}
    {S : SState} (hm : Match (r.env m vars) S m') (hwf : (r.env m vars).WF)
    (hsp : S.sp = .ptr 0 0) (hx29 : S.reg .X29 = some (.ptr 0 29280)) (hw : scrW S = true)
    (h20 : S.reg .X20 = some (.lit 136)) (h21 : S.reg .X21 = some (.ptr 0 16600))
    (h22 : S.reg .X22 = some (.ptr 0 26968)) : Base r m' ∧ Keep r m m' := by
  have hk := keep_of_match hpre hm hwf hw
  refine ⟨hB.of_keep hk.low (Run.Frame.of_match r hpre hB.frame hm hwf hsp hx29 (frameWrites_of_scrW hw))
    ?_ ?_ ?_, hk⟩
  · apply UInt64.toBitVec_inj.mp
    rw [hm.regs .X20 _ h20, hB.x20]
    rfl
  · apply UInt64.toBitVec_inj.mp
    rw [hm.regs .X21 _ h21, hB.x21]
    exact eval_ptr 16600
  · apply UInt64.toBitVec_inj.mp
    rw [hm.regs .X22 _ h22, hB.x22]
    exact eval_ptr 26968

/-- **`Base` after a call** writing the frame's bytes `a .. a + n` in the scratch. -/
theorem Base.of_call (hpre : r.Pre) {m m' : MachineData} (hB : Base r m) (hS : Saved m m')
    {a n N : Nat} (ha : a + n ≤ 29280) (hN : N ≤ finalizeStack)
    (hout : SameOutside m.dmem m'.dmem (r.CallOut m a n N)) (hs : ∀ o, a ≤ o → o < a + n → Scr o) :
    Base r m' ∧ Keep r m m' := by
  have hk := keep_of_call hpre hB.frame (by omega) hN hout hs
  exact ⟨hB.of_keep hk.low (r.frame_of_call hpre hB.frame hS ha hN hout) (hS.1 .X20 rfl)
    (hS.1 .X21 rfl) (hS.1 .X22 rfl), hk⟩

/-- A symbolic state's writes are in the frame below the saved registers, off the bytes `Low`
keeps. -/
@[expose] def lowW (S : SState) : Bool :=
  S.mem.all fun w ↦ w.r == 0 &&
    (decide (416 ≤ w.off ∧ w.off + w.n ≤ 432) || decide (16400 ≤ w.off ∧ w.off + w.n ≤ 25752) ||
      decide (25944 ≤ w.off ∧ w.off + w.n ≤ 29280))

/-- **`Base` after a block** writing off the bytes `Low` keeps (`lowW`). -/
theorem Base.of_matchLow (hpre : r.Pre) {m m' : MachineData} (hB : Base r m)
    {vars : Nat → BitVec 64} {S : SState} (hm : Match (r.env m vars) S m') (hwf : (r.env m vars).WF)
    (hsp : S.sp = .ptr 0 0) (hx29 : S.reg .X29 = some (.ptr 0 29280)) (hw : lowW S = true)
    (h20 : S.reg .X20 = some (.lit 136)) (h21 : S.reg .X21 = some (.ptr 0 16600))
    (h22 : S.reg .X22 = some (.ptr 0 26968)) : Base r m' ∧ Low r m m' := by
  have hb := r.base_toNat hpre
  have := r.m0.regs.SP.toNat_lt
  simp only [lowW, List.all_eq_true, Bool.and_eq_true, beq_iff_eq, Bool.or_eq_true,
    decide_eq_true_eq] at hw
  have hk : Low r m m' := by
    intro o ho
    have hoff := r.off_toNat hpre (a := o) (by omega)
    refine hm.get?_mem0 hwf fun ⟨w, hwm, b, sz, hr, h1, h2⟩ ↦ ?_
    obtain ⟨hr0, hwr⟩ := hw w hwm
    rw [hr0] at hr
    cases hr
    rw [hoff] at h1 h2
    omega
  have hfw : Run.frameWrites S = true := by
    simp only [Run.frameWrites, List.all_eq_true, Bool.and_eq_true, beq_iff_eq,
      decide_eq_true_eq]
    intro w hwm
    obtain ⟨h0, h1⟩ := hw w hwm
    exact ⟨h0, by omega⟩
  refine ⟨hB.of_keep hk (Run.Frame.of_match r hpre hB.frame hm hwf hsp hx29 hfw) ?_ ?_ ?_, hk⟩
  · apply UInt64.toBitVec_inj.mp
    rw [hm.regs .X20 _ h20, hB.x20]
    rfl
  · apply UInt64.toBitVec_inj.mp
    rw [hm.regs .X21 _ h21, hB.x21]
    exact eval_ptr 16600
  · apply UInt64.toBitVec_inj.mp
    rw [hm.regs .X22 _ h22, hB.x22]
    exact eval_ptr 26968

/-- **A block in one region's environment** changes memory only in that region. -/
theorem same_of_one {m m' : MachineData} {a : BitVec 64} {n : Nat} {vars : Nat → BitVec 64}
    {S : SState} (hm : Match (Env.ofMachine m [(a, n)] vars) S m')
    (hwf : (Env.ofMachine m [(a, n)] vars).WF)
    (hall : S.mem.all (fun w ↦ decide (w.off + w.n ≤ n)) = true) :
    SameOutside m.dmem m'.dmem (InRange a n) := by
  have hnw := hwf.noWrap 0 a n rfl
  intro p hp
  refine hm.get?_mem0 hwf fun ⟨w, hwm, b, sz, hr, h1, h2⟩ ↦ hp ?_
  have hle := List.all_eq_true.mp hall w hwm
  simp only [decide_eq_true_eq] at hle
  have hr' : w.r = 0 := by
    rcases h : w.r with _ | k
    · rfl
    · rw [h] at hr; simp at hr
  rw [hr'] at hr
  simp only [Env.ofMachine_regions, List.getElem?_cons_zero, Option.some.injEq,
    Prod.mk.injEq] at hr
  obtain ⟨rfl, rfl⟩ := hr
  rw [inRange_iff (by omega)]
  omega

/-- **Bytes a block does not write** are kept, as `Run.bytesAt_kept` with the length given. -/
theorem keep_blk (hpre : r.Pre) {m m' : MachineData} {vars : Nat → BitVec 64} {S : SState}
    (hm : Match (r.env m vars) S m') (hwf : (r.env m vars).WF) {o n : Nat} {bs : List UInt8}
    (hl : bs.length = n) (ho : o + n ≤ 29376) (hn : Run.noWriteIn S o n = true)
    (h : BytesAt m.dmem (r.off o) bs) : BytesAt m'.dmem (r.off o) bs :=
  r.bytesAt_kept hpre hm hwf (by rw [hl]; exact ho) h (by rw [hl]; exact hn)

/-- **`bytesOf` of bytes a block does not write.** -/
theorem bytesOf_blk (hpre : r.Pre) {m m' : MachineData} (hF : r.Frame m) {vars : Nat → BitVec 64}
    {S : SState} (hm : Match (r.env m vars) S m') (hwf : (r.env m vars).WF) {o n : Nat}
    (ho : o + n ≤ 29376) (hn : Run.noWriteIn S o n = true) :
    bytesOf m'.dmem (r.off o) n = bytesOf m.dmem (r.off o) n :=
  bytesOf_of_bytesAt' (keep_blk hpre hm hwf (Hasher.length_bytesOf ..) ho hn
    (Hasher.bytesAt_bytesOf (r.frame_mapped hpre hF ho).1)) (Hasher.length_bytesOf ..)

end

end

/-! ## The words of the addresses -/

public section

variable (r : Run)

theorem kpW_eq : kpW r = UnOp.apply .rev .W32 (r.idx &&& 255).toBitVec := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [kpW, UnOp.apply, ext_W32, low_W32, evalUBFM, BitVec.take]
  interval_cases i <;> simp [revW]

/-- **The key pair's word**: its bytes are the key's leaf, big-endian, then zeros. -/
theorem wordBytes_kpW : wordBytes (UInt64.ofBitVec (kpW r)) = be32 (r.key 0).leaf ++ [0, 0, 0, 0] := by
  have hz : ∀ t, 4 ≤ t → t < 8 → byteOf (UnOp.apply .rev .W32 (r.idx &&& 255).toBitVec) t = 0 := by
    intro t h1 h2
    rw [byteOf_mod]
    have hl := lt32_of_ext (revW .W32 (low .W32 (r.idx &&& 255).toBitVec))
    simp only [UnOp.apply]
    have : (ext .W32 (revW .W32 (low .W32 (r.idx &&& 255).toBitVec))).toNat / 2 ^ (8 * t) = 0 :=
      Nat.div_eq_of_lt (lt_of_lt_of_le hl (Nat.pow_le_pow_right (by decide) (by omega)))
    rw [this]
    rfl
  have h4 : [4, 5, 6, 7].map (byteOf (UnOp.apply .rev .W32 (r.idx &&& 255).toBitVec)) =
      [0, 0, 0, 0] := by
    rw [List.map_cons, List.map_cons, List.map_cons, List.map_cons, List.map_nil,
      hz 4 (by decide) (by decide), hz 5 (by decide) (by decide), hz 6 (by decide) (by decide),
      hz 7 (by decide) (by decide)]
  rw [← bytes_reg, show List.range 8 = List.range 4 ++ [4, 5, 6, 7] from rfl, List.map_append,
    kpW_eq, bytes_rev32, Run.key0_leaf, h4]
  rfl

/-- The key pair's word's low four bytes. -/
theorem bytes_kpW : (List.range 4).map (byteOf (kpW r)) = be32 (r.key 0).leaf := by
  have := wordBytes_kpW r
  rw [← bytes_reg, show List.range 8 = List.range 4 ++ [4, 5, 6, 7] from rfl, List.map_append] at this
  exact List.append_inj_left this (by simp [be32])

theorem treeW_eq : treeW r = UnOp.apply .rev .W64 (r.idx >>> 8).toBitVec := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [treeW, UnOp.apply, low_W64, ext_W64, evalUBFM, BitVec.take, UInt64.toBitVec_shiftRight]
  interval_cases i <;> simp [revW]

/-- **The tree's word**: its bytes are the key's tree, big-endian. -/
theorem wordBytes_treeW : wordBytes (UInt64.ofBitVec (treeW r)) = be64 (r.key 0).tree := by
  rw [← bytes_reg, treeW_eq, bytes_rev64, Run.key0_tree]

end

/-! ## The region's symbolic states -/

public section

variable {r : Run} [Labels]

omit [Labels] in
theorem allOf_append {α : Type} {P : α → Prop} :
    ∀ {l l' : List α}, AllOf P l → AllOf P l' → AllOf P (l ++ l')
  | [], _, _, h' => h'
  | _ :: _, _, h, h' => ⟨h.1, allOf_append h.2 h'⟩

/-- The registers `kept` in a state of `Base`. -/
theorem known_kept {m : MachineData} (hB : Base r m) (vars : Nat → BitVec 64) :
    AllOf (fun p ↦ (m.regs.getXReg p.1).toBitVec = p.2.eval (r.env m vars)) kept :=
  ⟨hB.frame.2.1.trans (eval_ptr 29280).symm, hB.x21.trans (eval_ptr 16600).symm,
    hB.x22.trans (eval_ptr 26968).symm, hB.x20, trivial⟩

/-- **The frame's symbolic state** `frameS k bs` describes a state of `Base` where the registers
`k` and the bounds `bs` hold. -/
theorem match_frameS (hpre : r.Pre) {m : MachineData} (hB : Base r m) {vars : Nat → BitVec 64}
    {k : List (XReg × Sym)} {bs : List (Sym × Nat)}
    (hk : AllOf (fun p ↦ (m.regs.getXReg p.1).toBitVec = p.2.eval (r.env m vars)) k)
    (hbs : AllOf (fun p ↦ (p.1.eval (r.env m vars)).toNat < p.2) bs) :
    Match (r.env m vars) (frameS k bs) m :=
  r.match_frame hpre hB.frame (allOf_append hk (known_kept hB vars)) trivial hbs trivial

/-- `frameS k` with the frame's word at `o` known to be the literal `v`. -/
theorem match_frameS_lit (hpre : r.Pre) {m : MachineData} (hB : Base r m)
    {vars : Nat → BitVec 64} {k : List (XReg × Sym)}
    (hk : AllOf (fun p ↦ (m.regs.getXReg p.1).toBitVec = p.2.eval (r.env m vars)) k) {o v : Nat}
    (h : BytesAt m.dmem (r.off o) (wordBytes v.toUInt64)) :
    Match (r.env m vars) { frameS k with mem := [litW o v] } m :=
  match_lit (match_frameS (bs := []) hpre hB hk trivial) rfl (r := 0) (b := r.base) (sz := 29376) rfl
    (lit_bytes h)

/-- A register given by a frame pointer. -/
theorem known_ptr {m : MachineData} {vars : Nat → BitVec 64} {x : XReg} {o : Nat}
    (h : Run.RegIs m x (r.off o)) :
    (m.regs.getXReg x).toBitVec = (Sym.ptr 0 (o : Int)).eval (r.env m vars) :=
  h.trans (eval_ptr o).symm

end

end NativeRustcArm.SphincsVerifyProof.Fors
