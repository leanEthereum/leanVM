module

public import NativeRustcArm.SphincsVerify.Digest.Hash
public import NativeRustcArm.SphincsVerify.Rev
public import NativeRustcArm.SphincsVerify.Epilogue

/-!
# Region 4, the FORS key: `ForsKeySpec`

`fors_key` (`th` of the 24 roots under the address of type `FORS_ROOTS`) with calls:
- `b94` (directive 1243) stores the address at `24720` (the tree's word X27, the type `4`, the
  key pair's word W26) and clears hasher A (`16400`); `b95`, `b96` update it with `PK.seed` and
  the address (`forsKey0_spec`);
- `b97` clones it to `26768`, `b98` updates the clone with the roots (`27824`), `b99` finalizes
  it to `16400` (`forsKey1_spec`);
- `b100` stores the digest's first 16 bytes, `signed`, at `27792` and sets the layer loop's
  registers and its spill at `0` (`forsKey2_spec`): `AtLayer 0 r.forsPk` at `b101` (directive
  1306).
-/

namespace NativeRustcArm.SphincsVerifyProof.Digest

open NativeRustc NativeRustc.Sphincs NativeRustc.Keccak NativeRustcArm.Sym
  LeanVM.Protocol.KeccakHash Native.Keccak

@[expose] public section

/-- The roots' bytes. -/
def rootsBytes (r : Run) : List UInt8 := ((List.range 24).map r.forsRoot).flatten

/-- The FORS key's address. -/
def fkAdrs (r : Run) : List UInt8 := forsAdrs r.idx 4

/-- **At `b97`**: hasher A at `16400` has absorbed `PK.seed | ADRS`; X22 `16`; the roots, the
index's spill. -/
def FK0 (r : Run) (m : MachineData) : Prop :=
  Keep r m ∧ Run.RegIs m .X22 16 ∧ BytesAt m.dmem (r.off 27824) (rootsBytes r) ∧
    r.WordAt m 384 r.idx ∧ HasherAt r m 16400 ([] ++ r.seed ++ fkAdrs r)

/-- **At `b100`**: the digest of `PK.seed | ADRS | roots` at `16400`; X19 and X20 the hashers. -/
def FK1 (r : Run) (m : MachineData) : Prop :=
  Keep r m ∧ Run.RegIs m .X22 16 ∧ Run.RegIs m .X19 (r.off 26768) ∧
    Run.RegIs m .X20 (r.off 16400) ∧ r.WordAt m 384 r.idx ∧
    BytesAt m.dmem (r.off 16400) (Keccak.hashBytes ([] ++ r.seed ++ fkAdrs r ++ rootsBytes r))

end

public section

theorem length_th' (seed adrs m : List UInt8) : (th seed adrs m).length = 16 := by
  rw [th, List.length_take, NativeRustc.Sphincs.length_hashBytes]
  rfl

theorem length_foldl16 {f : List UInt8 → Nat → List UInt8} (hf : ∀ c z, (f c z).length = 16) :
    ∀ (l : List Nat) (init : List UInt8), init.length = 16 → (l.foldl f init).length = 16
  | [], _, h => h
  | z :: l, _, _ => length_foldl16 hf l _ (hf _ z)

theorem length_forsRoot (r : Run) (c : Nat) : (r.forsRoot c).length = 16 := by
  unfold Run.forsRoot pathFold
  exact length_foldl16 (fun _ _ ↦ length_th' _ _ _) _ _ (length_th' _ _ _)

theorem length_rootsBytes (r : Run) : (rootsBytes r).length = 384 := by
  rw [rootsBytes, length_flatten_uniform (n := 16) _ (by
    intro x hx
    rw [List.mem_map] at hx
    obtain ⟨c, -, rfl⟩ := hx
    exact length_forsRoot r c), List.length_map, List.length_range]

theorem fkAdrs_eq (r : Run) : fkAdrs r = (be32 0 ++ be32 0) ++ (be64 (r.key 0).tree ++
    (be32 4 ++ (be32 (r.key 0).leaf ++ (be32 0 ++ be32 0)))) := by
  simp only [fkAdrs, forsAdrs, OtsKey.adrs_eq, adrsBytes, List.append_assoc]
  rfl

theorem length_fkAdrs (r : Run) : (fkAdrs r).length = 32 := by
  rw [fkAdrs_eq]
  simp [be32, be64]

theorem forsPk_eq (r : Run) :
    r.forsPk = (Keccak.hashBytes ([] ++ r.seed ++ fkAdrs r ++ rootsBytes r)).take 16 := by
  simp only [Run.forsPk, forsRecover, forsKey, th, List.nil_append, fkAdrs, rootsBytes]
  rfl

theorem length_forsPk (r : Run) : r.forsPk.length = 16 := by
  rw [Run.forsPk, forsRecover, forsKey]
  exact length_th' _ _ _

/-- The 4 low bytes of a word. -/
theorem bytes_low4 (x : BitVec 64) :
    (List.range 4).map (byteOf x) = (wordBytes (UInt64.ofBitVec x)).take 4 := by
  rw [← bytes_word, ← List.map_take, List.take_range]
  rfl

/-- A register's 8 bytes stored. -/
theorem bytesAt_reg8 [Labels] {r : Run} {m m₁ : MachineData} {S : SState}
    (hm : Match (r.env m) S m₁) {o : Nat} {y : XReg} (ho : o + 8 ≤ 29376)
    (hw : ∀ i < 8, findWrite 0 (o + i) S.mem = some (.reg y, i)) :
    BytesAt m₁.dmem (r.off o) (wordBytes (m.regs.getXReg y)) := by
  have := hm.bytesAt_write (r := 0) (o := o) (n := 8) (b := r.base) (sz := 29376) rfl ho hw
  rwa [bytes_word] at this

/-- A register's 4 low bytes stored. -/
theorem bytesAt_reg4 [Labels] {r : Run} {m m₁ : MachineData} {S : SState}
    (hm : Match (r.env m) S m₁) {o : Nat} {y : XReg} (ho : o + 4 ≤ 29376)
    (hw : ∀ i < 4, findWrite 0 (o + i) S.mem = some (.reg y, i)) :
    BytesAt m₁.dmem (r.off o) ((wordBytes (m.regs.getXReg y)).take 4) := by
  have := hm.bytesAt_write (r := 0) (o := o) (n := 4) (b := r.base) (sz := 29376) rfl ho hw
  rwa [bytes_low4] at this

/-- A literal's 8 bytes stored. -/
theorem bytesAt_lit8 [Labels] {r : Run} {m m₁ : MachineData} {S : SState}
    (hm : Match (r.env m) S m₁) {o v : Nat} (ho : o + 8 ≤ 29376)
    (hw : ∀ i < 8, findWrite 0 (o + i) S.mem = some (.lit v, i)) {bs : List UInt8}
    (hb : (List.range 8).map (byteOf (BitVec.ofNat 64 v)) = bs) : BytesAt m₁.dmem (r.off o) bs := by
  have := hm.bytesAt_write (r := 0) (o := o) (n := 8) (b := r.base) (sz := 29376) rfl ho hw
  rwa [show Sym.eval (r.env m) (.lit v) = BitVec.ofNat 64 v from rfl, hb] at this

/-- The frame's bytes `xs` at `o`, `ys` right after. -/
theorem bytesAt_cat {r : Run} {d : DataMem} {o k o' : Nat} {xs ys : List UInt8}
    (hx : BytesAt d (r.off o) xs) (hl : xs.length = k) (ho : o + k = o')
    (hy : BytesAt d (r.off o') ys) : BytesAt d (r.off o) (xs ++ ys) :=
  bytesAt_append hx (by rw [Run.off_add, hl, ho]; exact hy)

variable [NativeRustcArm.Host]

/-- **The FORS key's hasher absorbs `PK.seed | ADRS`** (`b94 .. b96`). -/
theorem forsKey0_spec (r : Run) (hp : Placed Sphincs.SphincsVerify.code r.k) (hc : Callees)
    (hpre : r.Pre) {m : MachineData} (hA : r.AtForsKey m) :
    Eventually (step1 NativeRustcArm.Host.exe) (fun st ↦ st.pc = r.pc NativeRustcArm.Sphincs.SphincsVerify.b97Offset ∧ FK0 r st.data)
      ⟨m, r.pc NativeRustcArm.Sphincs.SphincsVerify.b94Offset⟩ := by
  obtain ⟨hF, hI, h27, h26, h23, hR, h384, h392⟩ := hA
  have hK : Keep r m := ⟨hF, hI, h392⟩
  have hRl := length_rootsBytes r
  have hR : BytesAt m.dmem (r.off 27824) (rootsBytes r) := hR
  have hw := NativeRustc.length_wordBytes r.idx
  -- b94: the address, `memset` of hasher A
  refine Run.memsetCall r hp hpre hc Sphincs.SphincsVerify.b94_in_code rfl run_b94 rfl
    (a := 16400) (n := 344) hK (knownOK_ptr h23 (knownOK_nil m)) rfl rfl rfl
    ⟨by decide, by decide⟩ fun m₁ hm₁ hK₁ hkb₁ m₂ hK₂ hS₂ hkc₂ hB₂ ↦ ?_
  have gAd : BytesAt m₁.dmem (r.off 24720) (fkAdrs r) := by
    rw [fkAdrs_eq]
    refine bytesAt_cat (bytesAt_lit8 hm₁ (o := 24720) (v := 0) (by decide) (by decide) (by decide))
      rfl (rfl : 24720 + 8 = 24728) ?_
    refine bytesAt_cat (by rw [← h27]; exact bytesAt_reg8 hm₁ (o := 24728) (by decide) (by decide))
      rfl (rfl : 24728 + 8 = 24736) ?_
    refine bytesAt_cat (bytesAt_lit4 hm₁ (o := 24736) (v := 67108864) (by decide) (by decide)
      (by decide)) rfl (rfl : 24736 + 4 = 24740) ?_
    refine bytesAt_cat ?_ rfl (rfl : 24740 + 4 = 24744)
      (bytesAt_lit8 hm₁ (o := 24744) (v := 0) (by decide) (by decide) (by decide))
    have := bytesAt_reg4 hm₁ (o := 24740) (y := .X26) (by decide) (by decide)
    rwa [h26, show List.take 4 (be32 (r.key 0).leaf ++ [0, 0, 0, 0]) = be32 (r.key 0).leaf from
      List.take_left' rfl] at this
  have hAl := length_fkAdrs r
  have gAd := hkc₂ 24720 _ (by omega) (by omega) gAd
  have gR := hkc₂ 27824 _ (by omega) (by omega) (hkb₁ 27824 _ (by omega) (by rw [hRl]; rfl) hR)
  have g384 := hkc₂ 384 _ (by omega) (by omega) (hkb₁ 384 _ (by omega) (by rw [hw]; rfl) h384)
  have gH : HasherAt r m₂ 16400 [] := ⟨_, hB₂, Keccak.holds_new⟩
  -- b95: `PK.seed`
  refine Run.updateCall r hp hpre hc Sphincs.SphincsVerify.b95_in_code rfl run_b95 rfl
    (a := 16400) (b := 8208) (n := 16) hK₂ (knownOK_nil m₂) rfl rfl rfl ⟨by decide, by decide⟩
    (by decide) (by decide) (length_seed r) fun m₃ hm₃ hK₃ hkb₃ ↦
      ⟨gH.keepB hkb₃ (by decide) rfl, hK₃.seed, fun m₄ hK₄ hS₄ hkc₄ hH₄ ↦ ?_⟩
  have g22 := regIs_of_saved hS₄ rfl (regIs_lit hm₃ (y := .X22) (c := 16) rfl)
  have gAd := hkc₄ 24720 _ (by omega) (by omega) (hkb₃ 24720 _ (by omega) (by rw [hAl]; rfl) gAd)
  have gR := hkc₄ 27824 _ (by omega) (by omega) (hkb₃ 27824 _ (by omega) (by rw [hRl]; rfl) gR)
  have g384 := hkc₄ 384 _ (by omega) (by omega) (hkb₃ 384 _ (by omega) (by rw [hw]; rfl) g384)
  -- b96: the address
  refine Run.updateCall r hp hpre hc Sphincs.SphincsVerify.b96_in_code rfl run_b96 rfl
    (a := 16400) (b := 24720) (n := 32) hK₄ (knownOK_nil m₄) rfl rfl rfl ⟨by decide, by decide⟩
    (by decide) (by decide) hAl fun m₅ hm₅ hK₅ hkb₅ ↦
      ⟨hH₄.keepB hkb₅ (by decide) rfl, hkb₅ 24720 _ (by omega) (by rw [hAl]; rfl) gAd,
        fun m₆ hK₆ hS₆ hkc₆ hH₆ ↦ .done _ ⟨rfl, hK₆, ?_, ?_, ?_, hH₆⟩⟩
  · exact regIs_of_saved hS₆ rfl (regIs_keep hm₅ rfl g22)
  · exact hkc₆ 27824 _ (by omega) (by omega) (hkb₅ 27824 _ (by omega) (by rw [hRl]; rfl) gR)
  · exact hkc₆ 384 _ (by omega) (by omega) (hkb₅ 384 _ (by omega) (by rw [hw]; rfl) g384)

/-- **The roots absorbed, the FORS key's digest** (`b97 .. b99`). -/
theorem forsKey1_spec (r : Run) (hp : Placed Sphincs.SphincsVerify.code r.k) (hc : Callees)
    (hpre : r.Pre) {m : MachineData} (hA : FK0 r m) :
    Eventually (step1 NativeRustcArm.Host.exe) (fun st ↦ st.pc = r.pc NativeRustcArm.Sphincs.SphincsVerify.b100Offset ∧ FK1 r st.data)
      ⟨m, r.pc NativeRustcArm.Sphincs.SphincsVerify.b97Offset⟩ := by
  obtain ⟨hK, h22, hR, h384, hH⟩ := hA
  obtain ⟨hb, hbB, hbh⟩ := hH
  have hbl := Keccak.length_of_holds hbh
  have hRl := length_rootsBytes r
  have hw := NativeRustc.length_wordBytes r.idx
  -- b97: the clone
  refine Run.memcpyCall r hp hpre hc Sphincs.SphincsVerify.b97_in_code rfl run_b97 rfl
    (a := 26768) (b := 16400) (n := 344) hK (knownOK_nil m) rfl rfl rfl ⟨by decide, by decide⟩
    (by decide) (by decide) hbl fun m₁ hm₁ hK₁ hkb₁ ↦
      ⟨hkb₁ 16400 hb (by omega) (by rw [hbl]; rfl) hbB, fun m₂ hK₂ hS₂ hkc₂ hA₂ ↦ ?_⟩
  have g22 := regIs_of_saved hS₂ rfl (regIs_keep hm₁ rfl h22)
  have g19 := regIs_of_saved hS₂ rfl (regIs_ptr hm₁ (y := .X19) (o := 26768) rfl)
  have gR := hkc₂ 27824 _ (by omega) (by omega) (hkb₁ 27824 _ (by omega) (by rw [hRl]; rfl) hR)
  have g384 := hkc₂ 384 _ (by omega) (by omega) (hkb₁ 384 _ (by omega) (by rw [hw]; rfl) h384)
  have gB : HasherAt r m₂ 26768 ([] ++ r.seed ++ fkAdrs r) := ⟨hb, hA₂, hbh⟩
  -- b98: the roots
  refine Run.updateCall r hp hpre hc Sphincs.SphincsVerify.b98_in_code rfl run_b98 rfl
    (a := 26768) (b := 27824) (n := 384) hK₂ (knownOK_nil m₂) rfl rfl rfl ⟨by decide, by decide⟩
    (by decide) (by decide) hRl fun m₃ hm₃ hK₃ hkb₃ ↦
      ⟨gB.keepB hkb₃ (by decide) rfl, hkb₃ 27824 _ (by omega) (by rw [hRl]; rfl) gR,
        fun m₄ hK₄ hS₄ hkc₄ hH₄ ↦ ?_⟩
  have g22 := regIs_of_saved hS₄ rfl (regIs_keep hm₃ rfl g22)
  have g19 := regIs_of_saved hS₄ rfl (regIs_keep hm₃ rfl g19)
  have g384 := hkc₄ 384 _ (by omega) (by omega) (hkb₃ 384 _ (by omega) (by rw [hw]; rfl) g384)
  -- b99: the digest
  refine Run.finalizeCall r hp hpre hc Sphincs.SphincsVerify.b99_in_code rfl run_b99 rfl
    (o := 16400) (a := 26768) hK₄ (knownOK_nil m₄) rfl rfl ⟨by decide, by decide⟩ (by decide)
    (by decide) fun m₅ hm₅ hK₅ hkb₅ ↦
      ⟨hH₄.keepB hkb₅ (by decide) rfl, fun m₆ hK₆ hS₆ hkc₆ hD₆ ↦ .done _ ⟨rfl, hK₆, ?_, ?_, ?_, ?_, hD₆⟩⟩
  · exact regIs_of_saved hS₆ rfl (regIs_keep hm₅ rfl g22)
  · exact regIs_of_saved hS₆ rfl (regIs_keep hm₅ rfl g19)
  · exact regIs_of_saved hS₆ rfl (regIs_ptr hm₅ (y := .X20) (o := 16400) rfl)
  · exact hkc₆ 384 _ (by omega) (by omega) (hkb₅ 384 _ (by omega) (by rw [hw]; rfl) g384)

end

end NativeRustcArm.SphincsVerifyProof.Digest
