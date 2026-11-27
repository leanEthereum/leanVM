module

public import NativeRustcArm.SphincsVerify.Digest.Hash
public import NativeRustcArm.SphincsVerify.Rev
public import NativeRustcArm.SphincsVerify.Epilogue

/-!
# Region 4, the FORS key: `ForsKeySpec`

`fors_key` (`th` of the 24 roots under the address of type `FORS_ROOTS`) with calls:
- `b85` stores the address at `16960` (the tree's word X20, the type `4`, the
  key pair's word W25) and clears hasher A (`8640`); `b86`, `b87` update it with `PK.seed` and
  the address (`forsKey0_spec`);
- `b88` clones it to `19008`, `b89` updates the clone with the roots (`20064`), `b90` finalizes
  it to `8640` (`forsKey1_spec`);
- `b91` stores the digest's first 16 bytes, `signed`, at `20032` and sets the layer loop's
  registers and its spill at `8` (`forsKey2_spec`): `AtLayer 0 r.forsPk` at `b92`.
-/

namespace NativeRustcArm.SphincsVerifyProof.Digest

open NativeRustc NativeRustc.Sphincs NativeRustc.Keccak NativeRustcArm.Sym
  LeanVM.Protocol.KeccakHash Native.Keccak

@[expose] public section

/-- The roots' bytes. -/
def rootsBytes (r : Run) : List UInt8 := ((List.range 24).map r.forsRoot).flatten

/-- The FORS key's address. -/
def fkAdrs (r : Run) : List UInt8 := forsAdrs r.idx 4

/-- **At `b88`**: hasher A at `8640` has absorbed `PK.seed | ADRS`; X23 `16`, X27 `19008`;
the roots, the index's spill. -/
def FK0 (r : Run) (m : MachineData) : Prop :=
  Keep r m ∧ Run.RegIs m .X23 16 ∧ Run.RegIs m .X27 (r.off 19008) ∧
    BytesAt m.dmem (r.off 20064) (rootsBytes r) ∧
    r.WordAt m 400 r.idx ∧ HasherAt r m 8640 ([] ++ r.seed ++ fkAdrs r)

/-- **At `b91`**: the digest of `PK.seed | ADRS | roots` at `8640`; X19 and X20 the hashers,
X23 `16`, X27 `19008`. -/
def FK1 (r : Run) (m : MachineData) : Prop :=
  Keep r m ∧ Run.RegIs m .X23 16 ∧ Run.RegIs m .X19 (r.off 19008) ∧
    Run.RegIs m .X20 (r.off 8640) ∧ Run.RegIs m .X27 (r.off 19008) ∧ r.WordAt m 400 r.idx ∧
    BytesAt m.dmem (r.off 8640) (Keccak.hashBytes ([] ++ r.seed ++ fkAdrs r ++ rootsBytes r))

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
    (hm : Match (r.env m) S m₁) {o : Nat} {y : XReg} (ho : o + 8 ≤ 21616)
    (hw : ∀ i < 8, findWrite 0 (o + i) S.mem = some (.reg y, i)) :
    BytesAt m₁.dmem (r.off o) (wordBytes (m.regs.getXReg y)) := by
  have := hm.bytesAt_write (r := 0) (o := o) (n := 8) (b := r.base) (sz := 21616) rfl ho hw
  rwa [bytes_word] at this

/-- A register's 4 low bytes stored. -/
theorem bytesAt_reg4 [Labels] {r : Run} {m m₁ : MachineData} {S : SState}
    (hm : Match (r.env m) S m₁) {o : Nat} {y : XReg} (ho : o + 4 ≤ 21616)
    (hw : ∀ i < 4, findWrite 0 (o + i) S.mem = some (.reg y, i)) :
    BytesAt m₁.dmem (r.off o) ((wordBytes (m.regs.getXReg y)).take 4) := by
  have := hm.bytesAt_write (r := 0) (o := o) (n := 4) (b := r.base) (sz := 21616) rfl ho hw
  rwa [bytes_low4] at this

/-- A literal's 8 bytes stored. -/
theorem bytesAt_lit8 [Labels] {r : Run} {m m₁ : MachineData} {S : SState}
    (hm : Match (r.env m) S m₁) {o v : Nat} (ho : o + 8 ≤ 21616)
    (hw : ∀ i < 8, findWrite 0 (o + i) S.mem = some (.lit v, i)) {bs : List UInt8}
    (hb : (List.range 8).map (byteOf (BitVec.ofNat 64 v)) = bs) : BytesAt m₁.dmem (r.off o) bs := by
  have := hm.bytesAt_write (r := 0) (o := o) (n := 8) (b := r.base) (sz := 21616) rfl ho hw
  rwa [show Sym.eval (r.env m) (.lit v) = BitVec.ofNat 64 v from rfl, hb] at this

/-- The frame's bytes `xs` at `o`, `ys` right after. -/
theorem bytesAt_cat {r : Run} {d : DataMem} {o k o' : Nat} {xs ys : List UInt8}
    (hx : BytesAt d (r.off o) xs) (hl : xs.length = k) (ho : o + k = o')
    (hy : BytesAt d (r.off o') ys) : BytesAt d (r.off o) (xs ++ ys) :=
  bytesAt_append hx (by rw [Run.off_add, hl, ho]; exact hy)

variable [ElfHost]

/-- **The FORS key's hasher absorbs `PK.seed | ADRS`** (`b85 .. b87`). -/
theorem forsKey0_spec (r : Run) (hp : PlacedIn Sphincs.SphincsVerify.code r.sec r.k) (hc : Callees)
    (hpre : r.Pre) {m : MachineData} (hA : r.AtForsKey m) :
    Eventually (elfStep1 ElfHost.exe) (fun st ↦ st.pc = r.pc NativeRustcArm.Sphincs.SphincsVerify.b88Offset ∧ FK0 r st.data)
      ⟨m, r.pc NativeRustcArm.Sphincs.SphincsVerify.b85Offset⟩ := by
  obtain ⟨hF, hI, h20, h25, h23, h27, hR, h400, h408⟩ := hA
  have hK : Keep r m := ⟨hF, hI, h408⟩
  have hRl := length_rootsBytes r
  have hR : BytesAt m.dmem (r.off 20064) (rootsBytes r) := hR
  have hw := NativeRustc.length_wordBytes r.idx
  -- b85: the address, `memset` of hasher A
  refine Run.memsetCall r hp hpre hc Sphincs.SphincsVerify.b85_in_code rfl run_b85 rfl
    (a := 8640) (n := 344) hK (knownOK_ptr h23 (knownOK_nil m)) rfl rfl rfl
    ⟨by decide, by decide⟩ fun m₁ hm₁ hK₁ hkb₁ m₂ hK₂ hS₂ hkc₂ hB₂ ↦ ?_
  have g27 := regIs_of_saved hS₂ rfl (regIs_keep hm₁ rfl h27)
  have gAd : BytesAt m₁.dmem (r.off 16960) (fkAdrs r) := by
    rw [fkAdrs_eq]
    refine bytesAt_cat (bytesAt_lit8 hm₁ (o := 16960) (v := 0) (by decide) (by decide) (by decide))
      rfl (rfl : 16960 + 8 = 16968) ?_
    refine bytesAt_cat (by rw [← h20]; exact bytesAt_reg8 hm₁ (o := 16968) (by decide) (by decide))
      rfl (rfl : 16968 + 8 = 16976) ?_
    refine bytesAt_cat (bytesAt_lit4 hm₁ (o := 16976) (v := 67108864) (by decide) (by decide)
      (by decide)) rfl (rfl : 16976 + 4 = 16980) ?_
    refine bytesAt_cat ?_ rfl (rfl : 16980 + 4 = 16984)
      (bytesAt_lit8 hm₁ (o := 16984) (v := 0) (by decide) (by decide) (by decide))
    have := bytesAt_reg4 hm₁ (o := 16980) (y := .X25) (by decide) (by decide)
    rwa [h25, show List.take 4 (be32 (r.key 0).leaf ++ [0, 0, 0, 0]) = be32 (r.key 0).leaf from
      List.take_left' rfl] at this
  have hAl := length_fkAdrs r
  have gAd := hkc₂ 16960 _ (by omega) (by omega) gAd
  have gR := hkc₂ 20064 _ (by omega) (by omega) (hkb₁ 20064 _ (by omega) (by rw [hRl]; rfl) hR)
  have g400 := hkc₂ 400 _ (by omega) (by omega) (hkb₁ 400 _ (by omega) (by rw [hw]; rfl) h400)
  have gH : HasherAt r m₂ 8640 [] := ⟨_, hB₂, Keccak.holds_new⟩
  -- b86: `PK.seed`
  refine Run.updateCall r hp hpre hc Sphincs.SphincsVerify.b86_in_code rfl run_b86 rfl
    (a := 8640) (b := 448) (n := 16) hK₂ (knownOK_nil m₂) rfl rfl rfl ⟨by decide, by decide⟩
    (by decide) (by decide) (length_seed r) fun m₃ hm₃ hK₃ hkb₃ ↦
      ⟨gH.keepB hkb₃ (by decide) rfl, hK₃.seed, fun m₄ hK₄ hS₄ hkc₄ hH₄ ↦ ?_⟩
  have g23 := regIs_of_saved hS₄ rfl (regIs_lit hm₃ (y := .X23) (c := 16) rfl)
  have g27 := regIs_of_saved hS₄ rfl (regIs_keep hm₃ rfl g27)
  have gAd := hkc₄ 16960 _ (by omega) (by omega) (hkb₃ 16960 _ (by omega) (by rw [hAl]; rfl) gAd)
  have gR := hkc₄ 20064 _ (by omega) (by omega) (hkb₃ 20064 _ (by omega) (by rw [hRl]; rfl) gR)
  have g400 := hkc₄ 400 _ (by omega) (by omega) (hkb₃ 400 _ (by omega) (by rw [hw]; rfl) g400)
  -- b87: the address
  refine Run.updateCall r hp hpre hc Sphincs.SphincsVerify.b87_in_code rfl run_b87 rfl
    (a := 8640) (b := 16960) (n := 32) hK₄ (knownOK_nil m₄) rfl rfl rfl ⟨by decide, by decide⟩
    (by decide) (by decide) hAl fun m₅ hm₅ hK₅ hkb₅ ↦
      ⟨hH₄.keepB hkb₅ (by decide) rfl, hkb₅ 16960 _ (by omega) (by rw [hAl]; rfl) gAd,
        fun m₆ hK₆ hS₆ hkc₆ hH₆ ↦ .done _ ⟨rfl, hK₆, ?_, ?_, ?_, ?_, hH₆⟩⟩
  · exact regIs_of_saved hS₆ rfl (regIs_keep hm₅ rfl g23)
  · exact regIs_of_saved hS₆ rfl (regIs_keep hm₅ rfl g27)
  · exact hkc₆ 20064 _ (by omega) (by omega) (hkb₅ 20064 _ (by omega) (by rw [hRl]; rfl) gR)
  · exact hkc₆ 400 _ (by omega) (by omega) (hkb₅ 400 _ (by omega) (by rw [hw]; rfl) g400)

/-- **The roots absorbed, the FORS key's digest** (`b88 .. b90`). -/
theorem forsKey1_spec (r : Run) (hp : PlacedIn Sphincs.SphincsVerify.code r.sec r.k) (hc : Callees)
    (hpre : r.Pre) {m : MachineData} (hA : FK0 r m) :
    Eventually (elfStep1 ElfHost.exe) (fun st ↦ st.pc = r.pc NativeRustcArm.Sphincs.SphincsVerify.b91Offset ∧ FK1 r st.data)
      ⟨m, r.pc NativeRustcArm.Sphincs.SphincsVerify.b88Offset⟩ := by
  obtain ⟨hK, h23, h27, hR, h400, hH⟩ := hA
  obtain ⟨hb, hbB, hbh⟩ := hH
  have hbl := Keccak.length_of_holds hbh
  have hRl := length_rootsBytes r
  have hw := NativeRustc.length_wordBytes r.idx
  -- b88: the clone
  refine Run.memcpyCall r hp hpre hc Sphincs.SphincsVerify.b88_in_code rfl run_b88 rfl
    (a := 19008) (b := 8640) (n := 344) hK (knownOK_nil m) rfl rfl rfl ⟨by decide, by decide⟩
    (by decide) (by decide) hbl fun m₁ hm₁ hK₁ hkb₁ ↦
      ⟨hkb₁ 8640 hb (by omega) (by rw [hbl]; rfl) hbB, fun m₂ hK₂ hS₂ hkc₂ hA₂ ↦ ?_⟩
  have g23 := regIs_of_saved hS₂ rfl (regIs_keep hm₁ rfl h23)
  have g27 := regIs_of_saved hS₂ rfl (regIs_keep hm₁ rfl h27)
  have g19 := regIs_of_saved hS₂ rfl (regIs_ptr hm₁ (y := .X19) (o := 19008) rfl)
  have gR := hkc₂ 20064 _ (by omega) (by omega) (hkb₁ 20064 _ (by omega) (by rw [hRl]; rfl) hR)
  have g400 := hkc₂ 400 _ (by omega) (by omega) (hkb₁ 400 _ (by omega) (by rw [hw]; rfl) h400)
  have gB : HasherAt r m₂ 19008 ([] ++ r.seed ++ fkAdrs r) := ⟨hb, hA₂, hbh⟩
  -- b89: the roots
  refine Run.updateCall r hp hpre hc Sphincs.SphincsVerify.b89_in_code rfl run_b89 rfl
    (a := 19008) (b := 20064) (n := 384) hK₂ (knownOK_nil m₂) rfl rfl rfl ⟨by decide, by decide⟩
    (by decide) (by decide) hRl fun m₃ hm₃ hK₃ hkb₃ ↦
      ⟨gB.keepB hkb₃ (by decide) rfl, hkb₃ 20064 _ (by omega) (by rw [hRl]; rfl) gR,
        fun m₄ hK₄ hS₄ hkc₄ hH₄ ↦ ?_⟩
  have g23 := regIs_of_saved hS₄ rfl (regIs_keep hm₃ rfl g23)
  have g27 := regIs_of_saved hS₄ rfl (regIs_keep hm₃ rfl g27)
  have g19 := regIs_of_saved hS₄ rfl (regIs_keep hm₃ rfl g19)
  have g400 := hkc₄ 400 _ (by omega) (by omega) (hkb₃ 400 _ (by omega) (by rw [hw]; rfl) g400)
  -- b90: the digest
  refine Run.finalizeCall r hp hpre hc Sphincs.SphincsVerify.b90_in_code rfl run_b90 rfl
    (o := 8640) (a := 19008) hK₄ (knownOK_nil m₄) rfl rfl ⟨by decide, by decide⟩ (by decide)
    (by decide) fun m₅ hm₅ hK₅ hkb₅ ↦
      ⟨hH₄.keepB hkb₅ (by decide) rfl, fun m₆ hK₆ hS₆ hkc₆ hD₆ ↦ .done _ ⟨rfl, hK₆, ?_, ?_, ?_, ?_, ?_, hD₆⟩⟩
  · exact regIs_of_saved hS₆ rfl (regIs_keep hm₅ rfl g23)
  · exact regIs_of_saved hS₆ rfl (regIs_keep hm₅ rfl g19)
  · exact regIs_of_saved hS₆ rfl (regIs_ptr hm₅ (y := .X20) (o := 8640) rfl)
  · exact regIs_of_saved hS₆ rfl (regIs_keep hm₅ rfl g27)
  · exact hkc₆ 400 _ (by omega) (by omega) (hkb₅ 400 _ (by omega) (by rw [hw]; rfl) g400)

end

end NativeRustcArm.SphincsVerifyProof.Digest
