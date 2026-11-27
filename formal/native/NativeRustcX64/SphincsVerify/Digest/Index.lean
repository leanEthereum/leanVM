module

public import NativeRustcX64.SphincsVerify.Digest.Loop
public import NativeRustcX64.SphincsVerify.Digest.ForsKey
import Mathlib.Tactic.IntervalCases

/-!
# `digest_fields`' index, the FORS loop's registers: `b56`, `b57` (x86-64)

`b56` (directive 653) reads bytes `30 .. 33` of `h_msg` (`2086 .. 2089`): RBX the index (the
tree's 18 bits then the leaf's byte, `idxSym`, `idxSym_eval`), RBP its low byte, stores it at
`10376` and copies the 24 leaves' words from `4104` to `10384` (`memcpy`). `b57` (directive 670)
stores the index at `552`, the address's tree word `bswap(idx) << 8` (R13, at `80`) and the key
pair's word `idx_low << 24` (EBP, at `68`), RSI `0`, R14 `PK.seed`: `AtFors` at `b58` (directive
680, `index_spec`).
-/

namespace NativeRustcX64.SphincsVerifyProof.Digest

open NativeRustc NativeRustc.Sphincs NativeRustcX64.Sym LeanVM.Protocol.KeccakHash Native.Keccak

@[expose] public section

/-- A byte of `h_msg`, zero-extended (`movzbl`). -/
abbrev zb (o : Nat) : Sym := .un (.zext .W8) .W32 (.load 0 o 1)

/-- RBX after `b47`: the index from `h_msg`'s bytes `30 .. 33`. -/
def idxSym : Sym :=
  .bin .or .W32 (.bin .and .W32 (.bin .shl .W32 (.bin .or .W32 (.bin .or .W32
    (.bin .shl .W32 (zb 2055) (.lit 8)) (.bin .shl .W32 (zb 2054) (.lit 16))) (zb 2056)) (.lit 8))
    (.lit 67108608)) (zb 2057)

end

public section

theorem setWidth64_toBitVec (a : UInt8) : BitVec.ofNat 64 a.toNat = BitVec.setWidth 64 a.toBitVec := by
  apply BitVec.eq_of_toNat_eq
  simp

/-- **The index's bits.** -/
theorem idxSym_eval [Labels] (env : Env) (a b c d : UInt8)
    (ha : env.load 0 2054 1 = BitVec.setWidth 64 a.toBitVec)
    (hb : env.load 0 2055 1 = BitVec.setWidth 64 b.toBitVec)
    (hc : env.load 0 2056 1 = BitVec.setWidth 64 c.toBitVec)
    (hd : env.load 0 2057 1 = BitVec.setWidth 64 d.toBitVec) :
    idxSym.eval env = (digestInt [a, b, c] 18 <<< 8 ||| digestInt [d] 8).toBitVec := by
  simp only [idxSym, zb]
  sym_simp
  rw [ha, hb, hc, hd]
  simp only [digestInt, List.foldl_cons, List.foldl_nil, UInt64.toBitVec_or,
    UInt64.toBitVec_and, UInt64.toBitVec_shiftLeft, UInt8.toBitVec_toUInt64, shiftCount, shiftMask,
    low, ext, Width.bits]
  generalize a.toBitVec = va
  generalize b.toBitVec = vb
  generalize c.toBitVec = vc
  generalize d.toBitVec = vd
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp
  interval_cases i <;> simp

/-- **The index's low byte** is its leaf's byte. -/
theorem idx_low (a b c d : UInt8) :
    BitVec.setWidth 64 d.toBitVec =
      ((digestInt [a, b, c] 18 <<< 8 ||| digestInt [d] 8) &&& 255).toBitVec := by
  simp only [digestInt, List.foldl_cons, List.foldl_nil, UInt64.toBitVec_or,
    UInt64.toBitVec_and, UInt64.toBitVec_shiftLeft, UInt8.toBitVec_toUInt64]
  generalize a.toBitVec = va
  generalize b.toBitVec = vb
  generalize c.toBitVec = vc
  generalize d.toBitVec = vd
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp
  interval_cases i <;> simp

/-- Three bytes of a list. -/
theorem slice_three (H : List UInt8) {k : Nat} (hk : k + 3 ≤ H.length) :
    slice H k 3 = [H.getD k 0, H.getD (k + 1) 0, H.getD (k + 2) 0] := by
  apply List.ext_getElem (by simp [slice]; omega)
  intro i h1 h2
  simp only [List.length_cons, List.length_nil] at h2
  interval_cases i <;> simp [slice, List.getD_eq_getElem?_getD] <;>
    rw [List.getElem?_eq_getElem (by omega), Option.getD_some]

/-- One byte of a list. -/
theorem slice_one (H : List UInt8) {k : Nat} (hk : k + 1 ≤ H.length) :
    slice H k 1 = [H.getD k 0] := by
  apply List.ext_getElem (by simp [slice]; omega)
  intro i h1 h2
  simp only [List.length_cons, List.length_nil] at h2
  interval_cases i
  simp [slice, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega : k < H.length)]

/-- **`digest_fields`' index** from bytes `30 .. 33`. -/
theorem digestFields_fst (H : List UInt8) (hH : H.length = 64) :
    (digestFields H).1 = digestInt [H.getD 30 0, H.getD 31 0, H.getD 32 0] 18 <<< 8 |||
      digestInt [H.getD 33 0] 8 := by
  rw [digestFields, slice_three H (by omega), slice_one H (by omega)]

theorem idx_eq (r : Run) : r.idx = (digestFields (hMsgBytes r)).1 := by
  rw [hMsgBytes_eq]
  rfl

theorem leaves_eq (r : Run) : r.leaves = (List.range 24).map (leafOf (hMsgBytes r)) := by
  rw [hMsgBytes_eq]
  rfl

theorem leaves_bytes (r : Run) :
    wordsBytes (r.leaves.map Nat.toUInt64) = leavesBytes (hMsgBytes r) 24 := by
  rw [leaves_eq, List.map_map]
  rfl

/-- A byte of the frame, loaded. -/
theorem frame_load_byte [Labels] {r : Run} {m : MachineData} {ret : BitVec 64} {o : Nat}
    {H : List UInt8} (h : BytesAt m.dmem (r.off o) H) {k o' : Nat} (hk : k < H.length)
    (ho : o + k = o') :
    (r.env m (fun _ ↦ 0) ret).load 0 o' 1 = BitVec.setWidth 64 (H.getD k 0).toBitVec := by
  subst ho
  rw [Env.load_of_bytesAt (n := 1) (bs := [H.getD k 0]) rfl ?_]
  · apply BitVec.eq_of_toNat_eq
    simp [Int.ofBytes]
  · intro i hi
    simp only [List.length_cons, List.length_nil, Nat.zero_add, Nat.lt_one_iff] at hi
    subst hi
    have := h k hk
    rw [Run.off_add] at this
    simpa [Run.off, List.getD_eq_getElem?_getD, hk] using this

/-! ## The FORS loop's words -/

/-- `bswapq` then `shlq $8`: the bytes reversed of the value shifted down a byte. -/
theorem bswap_shl8 (x : BitVec 64) :
    BinOp.apply .shl .W64 (UnOp.apply .bswap .W64 x) (BitVec.ofNat 64 8) =
      UnOp.apply .bswap .W64 (x >>> 8) := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BinOp.apply, UnOp.apply, bswapW, ext, low, shiftCount, shiftMask, Width.bits,
    BitVec.setWidth_eq]
  rw [show (BitVec.setWidth 8 8#64).toNat &&& 63 = 8 by decide, BitVec.getLsbD_shiftLeft,
    bswap64_getLsbD _ _ hi, BitVec.getLsbD_ushiftRight]
  by_cases h : i < 8
  · rw [BitVec.getLsbD_of_ge x _ (by omega)]
    simp [h]
  · rw [bswap64_getLsbD _ _ (by omega)]
    simp only [h, hi, decide_true, decide_false, Bool.not_false, Bool.true_and]
    congr 1
    omega

/-- The tree word's bytes. -/
theorem bytes_treeWord (x : BitVec 64) :
    wordBytes (UInt64.ofBitVec (BinOp.apply .shl .W64 (UnOp.apply .bswap .W64 x) (BitVec.ofNat 64 8))) =
      be64 (UInt64.ofBitVec x >>> 8) := by
  rw [← bytes_word, bswap_shl8, bytes_bswap64]
  rfl

/-- `shll $24` of a byte: its bytes. -/
theorem shl24_toNat (y : BitVec 64) (hy : y.toNat < 256) :
    (BinOp.apply .shl .W32 y (BitVec.ofNat 64 24)).toNat = y.toNat * 16777216 := by
  simp only [BinOp.apply, ext, low, shiftCount, shiftMask, Width.bits]
  simp only [BitVec.toNat_setWidth, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]
  rw [show ((24#64).toNat % 2 ^ 8 &&& 31) = 24 by decide]
  omega

/-- The key pair's word: a byte `b` shifted to the top of the low 32 bits. -/
theorem bytes_leafWord (y : BitVec 64) (v : UInt32) (hy : y.toNat < 256) (hv : v.toNat = y.toNat) :
    wordBytes (UInt64.ofBitVec (BinOp.apply .shl .W32 y (BitVec.ofNat 64 24))) =
      be32 v ++ [0, 0, 0, 0] := by
  have h := shl24_toNat y hy
  generalize BinOp.apply .shl .W32 y (BitVec.ofNat 64 24) = z at h
  simp only [wordBytes, be32, List.map_cons, List.map_nil, List.range_succ, List.range_zero,
    List.nil_append, List.cons_append]
  refine List.ext_getElem (by simp) fun i h1 h2 ↦ ?_
  simp only [List.length_cons, List.length_nil] at h1
  apply UInt8.toNat.inj
  interval_cases i <;> simp [UInt64.toNat_shiftRight, UInt32.toNat_shiftRight, h, hv] <;> omega

/-- The key pair's word stored (`movl`): its four bytes. -/
theorem bytes_leafWord4 (y : BitVec 64) (v : UInt32) (hy : y.toNat < 256) (hv : v.toNat = y.toNat) :
    (List.range 4).map (byteOf (BinOp.apply .shl .W32 y (BitVec.ofNat 64 24))) = be32 v := by
  have h := bytes_leafWord y v hy hv
  rw [← bytes_word] at h
  have := congrArg (List.take 4) h
  rw [← List.map_take, List.take_range] at this
  simpa [be32] using this

theorem key0_leaf' (idx : UInt64) : (OtsKey.ofIndex 0 idx).leaf = (idx &&& 255).toUInt32 := by
  simp only [OtsKey.ofIndex, layerHeights, List.take_zero, List.sum_nil, List.getD_cons_zero]
  rfl

theorem key0_leaf (idx : UInt64) : ((OtsKey.ofIndex 0 idx).leaf).toNat = (idx &&& 255).toNat := by
  rw [key0_leaf', UInt64.toNat_toUInt32]
  have : (idx &&& 255).toNat < 256 := by
    rw [UInt64.toNat_and]
    exact Nat.lt_of_le_of_lt Nat.and_le_right (by decide)
  omega

theorem key0_tree (idx : UInt64) : (OtsKey.ofIndex 0 idx).tree = idx >>> 8 := by
  simp only [OtsKey.ofIndex, layerHeights, List.take_zero, List.sum_nil, List.getD_cons_zero]
  rfl

variable [ElfHost]

/-- **The index, the leaves copied, the FORS loop's registers**: `b47`, `b48` to `b49`. -/
theorem index_spec (r : Run) (hp : PlacedIn Sphincs.SphincsVerify.code r.sec r.k) (hc : Callees)
    (hpre : r.Pre) {m : MachineData} (hA : AfterLoop r (hMsgBytes r) m) :
    Eventually (elfStep1 ElfHost.exe) (fun st ↦ st.pc = r.pc NativeRustcX64.Sphincs.SphincsVerify.b49Offset ∧ r.AtFors st.data)
      ⟨m, r.pc NativeRustcX64.Sphincs.SphincsVerify.b47Offset⟩ := by
  obtain ⟨hK, hH, hL⟩ := hA
  have hl := length_hMsgBytes r
  have hLl : (leavesBytes (hMsgBytes r) 24).length = 192 := length_leavesBytes _ _
  refine Run.memcpyCall r hp hpre hc Sphincs.SphincsVerify.b47_in_code rfl run_b47 rfl rfl
    (a := 10352) (b := 4072) (n := 192) hK (knownOK_nil m _) rfl rfl rfl
    (.inl ⟨by decide, by decide⟩) (by decide) (by decide) hLl fun m₁ hm₁ hkb₁ ↦
      ⟨hkb₁ 4072 _ (by omega) (by rw [hLl]; rfl) hL, fun m₂ hK₂ hS₂ hkc₂ hB₂ ↦ ?_⟩
  have l30 := frame_load_byte (r := r) (m := m) (ret := (r.pc (NativeRustcX64.Sphincs.SphincsVerify.b47Offset + Sphincs.SphincsVerify.b47.length)).toBitVec) hH (k := 30) (o' := 2054) (by omega) rfl
  have l31 := frame_load_byte (r := r) (m := m) (ret := (r.pc (NativeRustcX64.Sphincs.SphincsVerify.b47Offset + Sphincs.SphincsVerify.b47.length)).toBitVec) hH (k := 31) (o' := 2055) (by omega) rfl
  have l32 := frame_load_byte (r := r) (m := m) (ret := (r.pc (NativeRustcX64.Sphincs.SphincsVerify.b47Offset + Sphincs.SphincsVerify.b47.length)).toBitVec) hH (k := 32) (o' := 2056) (by omega) rfl
  have l33 := frame_load_byte (r := r) (m := m) (ret := (r.pc (NativeRustcX64.Sphincs.SphincsVerify.b47Offset + Sphincs.SphincsVerify.b47.length)).toBitVec) hH (k := 33) (o' := 2057) (by omega) rfl
  have hidx : reg m₁ .rbx = r.idx.toBitVec := by
    rw [show reg m₁ .rbx = idxSym.eval _ from hm₁.regs .rbx idxSym rfl,
      idxSym_eval _ _ _ _ _ l30 l31 l32 l33, idx_eq, digestFields_fst _ hl]
  have hlow : reg m₁ .rbp = (r.idx &&& 255).toBitVec := by
    rw [show reg m₁ .rbp = (zb 2057).eval _ from hm₁.regs .rbp _ rfl]
    show UnOp.apply (.zext .W8) .W32 ((r.env m (fun _ ↦ 0)
      (r.pc (NativeRustcX64.Sphincs.SphincsVerify.b47Offset + Sphincs.SphincsVerify.b47.length)).toBitVec).load 0 2057 1) = _
    rw [l33, idx_eq, digestFields_fst _ hl, ← idx_low]
    apply BitVec.eq_of_toNat_eq
    simp [UnOp.apply, ext, low]
  have g12 := regIs_of_saved hS₂ rfl (regIs_ptr hm₁ (y := .r12) (o := 4072) rfl)
  have gbx : reg m₂ .rbx = r.idx.toBitVec := (hS₂.1 .rbx rfl).trans hidx
  have gbp : reg m₂ .rbp = (r.idx &&& 255).toBitVec := (hS₂.1 .rbp rfl).trans hlow
  -- b48: the FORS loop's registers and spills
  refine Run.frameFall r hp hpre Sphincs.SphincsVerify.b48_in_code rfl (List.cons_ne_nil _ _)
    run_b48 rfl rfl hK₂ (knownOK_nil m₂ _) fun m₃ hm₃ hK₃ hkb₃ ↦ .done _ ⟨rfl, ?_⟩
  obtain ⟨hF₃, hI₃, h176⟩ := hK₃
  have hbp8 : (reg m₂ .rbp).toNat < 256 := by
    rw [gbp, UInt64.toNat_toBitVec, UInt64.toNat_and]
    exact Nat.lt_of_le_of_lt Nat.and_le_right (by decide)
  have hleaf : ((r.key 0).leaf).toNat = (reg m₂ .rbp).toNat := by
    rw [Run.key, key0_leaf, gbp, UInt64.toNat_toBitVec]
  have htree : UInt64.ofBitVec (reg m₂ .rbx) >>> 8 = (r.key 0).tree := by
    rw [gbx, Run.key, key0_tree, UInt64.ofBitVec_toBitVec]
  have hr15 : reg m₃ .r13 = BinOp.apply .shl .W64 (UnOp.apply .bswap .W64 (reg m₂ .rbx))
      (BitVec.ofNat 64 8) := by
    have h := hm₃.regs .r13 _ rfl
    simp only [Sym.eval, Env.ofMachine_regs] at h
    exact h
  have hrbp : reg m₃ .rbp = BinOp.apply .shl .W32 (reg m₂ .rbp) (BitVec.ofNat 64 24) := by
    have h := hm₃.regs .rbp _ rfl
    simp only [Sym.eval, Env.ofMachine_regs] at h
    exact h
  refine ⟨hF₃, hI₃, regIs_lit hm₃ (y := .rsi) (c := 0) rfl, ?_, ?_,
    regIs_keep hm₃ rfl g12, regIs_ptr hm₃ (y := .r14) (o := 112) rfl,
    ?_, ?_, ?_, ?_, h176, hm₃.regs .rbx _ rfl, regIs_ptr hm₃ (y := .r15) (o := 560) rfl⟩
  · rw [hr15, bytes_treeWord, htree]
  · rw [hrbp, bytes_leafWord _ _ hbp8 hleaf]
  · have := hm₃.bytesAt_write (r := 0) (o := 80) (n := 8) (b := r.base) (sz := 21632) rfl
      (by decide) (v := .bin .shl .W64 (.un .bswap .W64 (.reg .rbx)) (.lit 8)) (by decide)
    simp only [Sym.eval, Env.ofMachine_regs] at this
    rw [bytes_word] at this
    rw [← htree, ← bytes_treeWord]
    exact this
  · have := hm₃.bytesAt_write (r := 0) (o := 68) (n := 4) (b := r.base) (sz := 21632) rfl
      (by decide) (v := .bin .shl .W32 (.reg .rbp) (.lit 24)) (by decide)
    simp only [Sym.eval, Env.ofMachine_regs] at this
    rwa [bytes_leafWord4 _ _ hbp8 hleaf] at this
  · rw [leaves_bytes]
    exact hkb₃ 10352 _ (by rw [hLl]; omega) (by rw [hLl]; rfl) hB₂
  · have := hm₃.bytesAt_write (r := 0) (o := 552) (n := 8) (b := r.base) (sz := 21632) rfl
      (by decide) (v := .reg .rbx) (by decide)
    rw [bytes_word] at this
    rw [show r.idx = UInt64.ofBitVec (reg m₂ .rbx) by rw [gbx, UInt64.ofBitVec_toBitVec]]
    exact this

end

end NativeRustcX64.SphincsVerifyProof.Digest
