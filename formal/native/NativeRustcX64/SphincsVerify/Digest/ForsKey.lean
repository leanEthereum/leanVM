module

public import NativeRustcX64.SphincsVerify.Digest.Hash
public import NativeRustcX64.SphincsVerify.Bswap

/-!
# Region 4, the FORS key: `ForsKeySpec` (x86-64)

`fors_key` (`th` of the 24 roots under the address of type `FORS_ROOTS`) with calls:
- `b97` (directive 1088) stores the address at `2056` (the tree's word R13, the type `4`, the key
  pair's word EBP) and clears hasher A (`4104`); `b98`, `b99` update it with `PK.seed` and the
  address (`forsKey0_spec`);
- `b100` clones it to `560`, `b101` updates the clone with the roots (`20172`), `b102` finalizes
  it to `4104` (`forsKey1_spec`);
- `b103` stores the digest's first 16 bytes, `signed`, at `144` and sets the layer loop's
  registers (`forsKey2_spec`): `AtLayer 0 r.forsPk` at `b104` (directive 1129).
-/

namespace NativeRustcX64.SphincsVerifyProof.Digest

open NativeRustc NativeRustc.Sphincs NativeRustc.Keccak NativeRustcX64.Sym
  LeanVM.Protocol.KeccakHash Native.Keccak

@[expose] public section

/-- The roots' bytes. -/
def rootsBytes (r : Run) : List UInt8 := ((List.range 24).map r.forsRoot).flatten

/-- The FORS key's address. -/
def fkAdrs (r : Run) : List UInt8 := forsAdrs r.idx 4

/-- **At `b91`**: hasher A at `4072` has absorbed `PK.seed | ADRS`; R12 hasher A, RBX `0`, R13
the address; the roots, the index's spill. -/
def FK0 (r : Run) (m : MachineData) : Prop :=
  Keep r m ∧ Run.RegIs m .r12 (r.off 4072) ∧ Run.RegIs m .rbx 0 ∧ Run.RegIs m .r13 (r.off 2024) ∧
    BytesAt m.dmem (r.off 12396) (rootsBytes r) ∧ r.WordAt m 552 r.idx ∧
    HasherAt r m 4072 ([] ++ r.seed ++ fkAdrs r)

/-- **At `b94`**: the digest of `PK.seed | ADRS | roots` at `4072`; R12, RBX, R13, RBP. -/
def FK1 (r : Run) (m : MachineData) : Prop :=
  Keep r m ∧ Run.RegIs m .r12 (r.off 4072) ∧ Run.RegIs m .rbx 0 ∧ Run.RegIs m .r13 (r.off 2024) ∧
    Run.RegIs m .rbp (r.off 560) ∧ r.WordAt m 552 r.idx ∧
    BytesAt m.dmem (r.off 4072) (Keccak.hashBytes ([] ++ r.seed ++ fkAdrs r ++ rootsBytes r))

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

/-- The low 4 bytes of a 32-bit truncation are the value's. -/
theorem bytes_trunc32 (x : BitVec 64) :
    (List.range 4).map (byteOf (UnOp.apply .trunc .W32 x)) =
      (wordBytes (UInt64.ofBitVec x)).take 4 := by
  rw [← bytes_word, ← List.map_take, List.take_range, show min 4 8 = 4 from rfl]
  apply List.map_congr_left
  intro t ht
  rw [List.mem_range] at ht
  rw [byteOf_mod, byteOf_mod]
  congr 1
  simp only [UnOp.apply, toNat_ext, toNat_low]
  exact div_mod_256_of_mod (by simp [Width.bits]; omega)

section
variable [Labels]

/-- A register's 8 bytes stored. -/
theorem bytesAt_reg8 {r : Run} {m m₁ : MachineData} {ret : BitVec 64} {S : SState}
    (hm : Match (r.env m (fun _ ↦ 0) ret) S m₁) {o : Nat} {y : Reg64} (ho : o + 8 ≤ 21632)
    (hw : ∀ i < 8, findWrite 0 (o + i) S.mem = some (.reg y, i)) :
    BytesAt m₁.dmem (r.off o) (wordBytes (UInt64.ofBitVec (reg m y))) := by
  have := hm.bytesAt_write (r := 0) (o := o) (n := 8) (b := r.base) (sz := 21632) rfl ho hw
  rwa [bytes_word] at this

/-- A register's low 4 bytes stored (`movl`). -/
theorem bytesAt_trunc4 {r : Run} {m m₁ : MachineData} {ret : BitVec 64} {S : SState}
    (hm : Match (r.env m (fun _ ↦ 0) ret) S m₁) {o : Nat} {y : Reg64} (ho : o + 4 ≤ 21632)
    (hw : ∀ i < 4, findWrite 0 (o + i) S.mem = some (.un .trunc .W32 (.reg y), i)) :
    BytesAt m₁.dmem (r.off o) ((wordBytes (UInt64.ofBitVec (reg m y))).take 4) := by
  have := hm.bytesAt_write (r := 0) (o := o) (n := 4) (b := r.base) (sz := 21632) rfl ho hw
  rwa [show Sym.eval (r.env m (fun _ ↦ 0) ret) (.un .trunc .W32 (.reg y)) =
    UnOp.apply .trunc .W32 (reg m y) from rfl, bytes_trunc32] at this

/-- A literal's 8 bytes stored. -/
theorem bytesAt_lit8 {r : Run} {m m₁ : MachineData} {ret : BitVec 64} {S : SState}
    (hm : Match (r.env m (fun _ ↦ 0) ret) S m₁) {o v : Nat} (ho : o + 8 ≤ 21632)
    (hw : ∀ i < 8, findWrite 0 (o + i) S.mem = some (.lit v, i)) {bs : List UInt8}
    (hb : (List.range 8).map (byteOf (BitVec.ofNat 64 v)) = bs) : BytesAt m₁.dmem (r.off o) bs := by
  have := hm.bytesAt_write (r := 0) (o := o) (n := 8) (b := r.base) (sz := 21632) rfl ho hw
  rwa [show Sym.eval (r.env m (fun _ ↦ 0) ret) (.lit v) = BitVec.ofNat 64 v from rfl, hb] at this

end

variable [Host]

/-- **The FORS key's hasher absorbs `PK.seed | ADRS`** (`b88 .. b90`). -/
theorem forsKey0_spec (r : Run) (hp : Placed Sphincs.SphincsVerify.code r.k) (hc : Callees)
    (hpre : r.Pre) {m : MachineData} (hA : r.AtForsKey m) :
    Eventually (step1 Host.exe) (fun st ↦ st.pc = r.pc NativeRustcX64.Sphincs.SphincsVerify.b91Offset ∧ FK0 r st.data)
      ⟨m, r.pc NativeRustcX64.Sphincs.SphincsVerify.b88Offset⟩ := by
  obtain ⟨hF, hI, h15, hbp, hR, h568, h176⟩ := hA
  have hK : Keep r m := ⟨hF, hI, h176⟩
  have hRl := length_rootsBytes r
  have hR : BytesAt m.dmem (r.off 12396) (rootsBytes r) := hR
  have hw := NativeRustc.length_wordBytes r.idx
  have hAl := length_fkAdrs r
  -- b88: the address, `memset` of hasher A
  refine Run.memsetCall r hp hpre hc Sphincs.SphincsVerify.b88_in_code rfl run_b88 rfl rfl
    (a := 4072) (n := 344) hK (knownOK_nil m _) rfl rfl rfl (.inl ⟨by decide, by decide⟩)
    fun m₁ hm₁ hkb₁ m₂ hK₂ hS₂ hkc₂ hB₂ ↦ ?_
  have gAd : BytesAt m₁.dmem (r.off 2024) (fkAdrs r) := by
    rw [fkAdrs_eq]
    refine bytesAt_cat (bytesAt_lit8 hm₁ (o := 2024) (v := 0) (by decide) (by decide) (by decide))
      rfl (rfl : 2024 + 8 = 2032) ?_
    refine bytesAt_cat (by rw [← h15]; exact bytesAt_reg8 hm₁ (o := 2032) (by decide) (by decide))
      rfl (rfl : 2032 + 8 = 2040) ?_
    refine bytesAt_cat (bytesAt_lit4 hm₁ (o := 2040) (v := 67108864) (by decide) (by decide)
      (by decide)) rfl (rfl : 2040 + 4 = 2044) ?_
    refine bytesAt_cat ?_ rfl (rfl : 2044 + 4 = 2048)
      (bytesAt_lit8 hm₁ (o := 2048) (v := 0) (by decide) (by decide) (by decide))
    have := bytesAt_trunc4 hm₁ (o := 2044) (y := .rbp) (by decide) (by decide)
    rwa [hbp, show List.take 4 (be32 (r.key 0).leaf ++ [0, 0, 0, 0]) = be32 (r.key 0).leaf from
      List.take_left' rfl] at this
  have gAd := hkc₂ 2024 _ (by omega) (by omega) gAd
  have gR := hkc₂ 12396 _ (by omega) (by omega) (hkb₁ 12396 _ (by omega) (by rw [hRl]; rfl) hR)
  have g568 := hkc₂ 552 _ (by omega) (by omega) (hkb₁ 552 _ (by omega) (by rw [hw]; rfl) h568)
  have g12 := regIs_of_saved hS₂ rfl (regIs_ptr hm₁ (y := .r12) (o := 4072) rfl)
  have gbx := regIs_of_saved hS₂ rfl (regIs_lit hm₁ (y := .rbx) (c := 0) rfl)
  have gH : HasherAt r m₂ 4072 [] := ⟨_, hB₂, Keccak.holds_new⟩
  -- b89: `PK.seed`
  refine Run.updateCall r hp hpre hc Sphincs.SphincsVerify.b89_in_code rfl run_b89 rfl rfl
    (a := 4072) (b := 112) (n := 16) hK₂ (knownOK_ptr g12 (knownOK_nil m₂ _)) rfl rfl rfl
    (.inl ⟨by decide, by decide⟩) (by decide) (by decide) (length_seed r) fun m₃ hm₃ hkb₃ ↦
      ⟨gH.keepB hkb₃ (by decide) rfl,
        hkb₃ 112 _ (by rw [length_seed]; omega) (by rw [length_seed]; rfl) hK₂.seed,
        fun m₄ hK₄ hS₄ hkc₄ hH₄ ↦ ?_⟩
  have g12 := regIs_of_saved hS₄ rfl (regIs_ptr hm₃ (y := .r12) (o := 4072) rfl)
  have gbx := regIs_of_saved hS₄ rfl (regIs_keep hm₃ rfl gbx)
  have gAd := hkc₄ 2024 _ (by omega) (by omega) (hkb₃ 2024 _ (by omega) (by rw [hAl]; rfl) gAd)
  have gR := hkc₄ 12396 _ (by omega) (by omega) (hkb₃ 12396 _ (by omega) (by rw [hRl]; rfl) gR)
  have g568 := hkc₄ 552 _ (by omega) (by omega) (hkb₃ 552 _ (by omega) (by rw [hw]; rfl) g568)
  -- b90: the address
  refine Run.updateCall r hp hpre hc Sphincs.SphincsVerify.b90_in_code rfl run_b90 rfl rfl
    (a := 4072) (b := 2024) (n := 32) hK₄ (knownOK_ptr g12 (knownOK_nil m₄ _)) rfl rfl rfl
    (.inl ⟨by decide, by decide⟩) (by decide) (by decide) hAl fun m₅ hm₅ hkb₅ ↦
      ⟨hH₄.keepB hkb₅ (by decide) rfl, hkb₅ 2024 _ (by omega) (by rw [hAl]; rfl) gAd,
        fun m₆ hK₆ hS₆ hkc₆ hH₆ ↦ .done _ ⟨rfl, hK₆, ?_, ?_, ?_, ?_, ?_, hH₆⟩⟩
  · exact regIs_of_saved hS₆ rfl (regIs_ptr hm₅ (y := .r12) (o := 4072) rfl)
  · exact regIs_of_saved hS₆ rfl (regIs_keep hm₅ rfl gbx)
  · exact regIs_of_saved hS₆ rfl (regIs_ptr hm₅ (y := .r13) (o := 2024) rfl)
  · exact hkc₆ 12396 _ (by omega) (by omega) (hkb₅ 12396 _ (by omega) (by rw [hRl]; rfl) gR)
  · exact hkc₆ 552 _ (by omega) (by omega) (hkb₅ 552 _ (by omega) (by rw [hw]; rfl) g568)

/-- **The roots absorbed, the FORS key's digest** (`b91 .. b93`). -/
theorem forsKey1_spec (r : Run) (hp : Placed Sphincs.SphincsVerify.code r.k) (hc : Callees)
    (hpre : r.Pre) {m : MachineData} (hA : FK0 r m) :
    Eventually (step1 Host.exe) (fun st ↦ st.pc = r.pc NativeRustcX64.Sphincs.SphincsVerify.b94Offset ∧ FK1 r st.data)
      ⟨m, r.pc NativeRustcX64.Sphincs.SphincsVerify.b91Offset⟩ := by
  obtain ⟨hK, h12, hbx, h13, hR, h568, hH⟩ := hA
  obtain ⟨hb, hbB, hbh⟩ := hH
  have hbl := Keccak.length_of_holds hbh
  have hRl := length_rootsBytes r
  have hw := NativeRustc.length_wordBytes r.idx
  -- b91: the clone
  refine Run.memcpyCall r hp hpre hc Sphincs.SphincsVerify.b91_in_code rfl run_b91 rfl rfl
    (a := 560) (b := 4072) (n := 344) hK (knownOK_ptr h12 (knownOK_nil m _)) rfl rfl rfl
    (.inl ⟨by decide, by decide⟩) (by decide) (by decide) hbl fun m₁ hm₁ hkb₁ ↦
      ⟨hkb₁ 4072 hb (by omega) (by rw [hbl]; rfl) hbB, fun m₂ hK₂ hS₂ hkc₂ hA₂ ↦ ?_⟩
  have g12 := regIs_of_saved hS₂ rfl (regIs_ptr hm₁ (y := .r12) (o := 4072) rfl)
  have gbx := regIs_of_saved hS₂ rfl (regIs_keep hm₁ rfl hbx)
  have g13 := regIs_of_saved hS₂ rfl (regIs_keep hm₁ rfl h13)
  have gbp := regIs_of_saved hS₂ rfl (regIs_ptr hm₁ (y := .rbp) (o := 560) rfl)
  have gR := hkc₂ 12396 _ (by omega) (by omega) (hkb₁ 12396 _ (by omega) (by rw [hRl]; rfl) hR)
  have g568 := hkc₂ 552 _ (by omega) (by omega) (hkb₁ 552 _ (by omega) (by rw [hw]; rfl) h568)
  have gB : HasherAt r m₂ 560 ([] ++ r.seed ++ fkAdrs r) := ⟨hb, hA₂, hbh⟩
  -- b92: the roots
  refine Run.updateCall r hp hpre hc Sphincs.SphincsVerify.b92_in_code rfl run_b92 rfl rfl
    (a := 560) (b := 12396) (n := 384) hK₂ (knownOK_ptr gbp (knownOK_nil m₂ _)) rfl rfl rfl
    (.inl ⟨by decide, by decide⟩) (by decide) (by decide) hRl fun m₃ hm₃ hkb₃ ↦
      ⟨gB.keepB hkb₃ (by decide) rfl, hkb₃ 12396 _ (by omega) (by rw [hRl]; rfl) gR,
        fun m₄ hK₄ hS₄ hkc₄ hH₄ ↦ ?_⟩
  have g12 := regIs_of_saved hS₄ rfl (regIs_keep hm₃ rfl g12)
  have gbx := regIs_of_saved hS₄ rfl (regIs_keep hm₃ rfl gbx)
  have g13 := regIs_of_saved hS₄ rfl (regIs_keep hm₃ rfl g13)
  have gbp := regIs_of_saved hS₄ rfl (regIs_ptr hm₃ (y := .rbp) (o := 560) rfl)
  have g568 := hkc₄ 552 _ (by omega) (by omega) (hkb₃ 552 _ (by omega) (by rw [hw]; rfl) g568)
  -- b93: the digest
  refine Run.finalizeCall r hp hpre hc Sphincs.SphincsVerify.b93_in_code rfl run_b93 rfl rfl
    (o := 4072) (a := 560) hK₄ (knownOK_ptr gbp (knownOK_nil m₄ _)) rfl rfl
    (.inl ⟨by decide, by decide⟩) (by decide) (by decide) fun m₅ hm₅ hkb₅ ↦
      ⟨hH₄.keepB hkb₅ (by decide) rfl, fun m₆ hK₆ hS₆ hkc₆ hD₆ ↦
        .done _ ⟨rfl, hK₆, ?_, ?_, ?_, ?_, ?_, hD₆⟩⟩
  · exact regIs_of_saved hS₆ rfl (regIs_keep hm₅ rfl g12)
  · exact regIs_of_saved hS₆ rfl (regIs_keep hm₅ rfl gbx)
  · exact regIs_of_saved hS₆ rfl (regIs_keep hm₅ rfl g13)
  · exact regIs_of_saved hS₆ rfl (regIs_ptr hm₅ (y := .rbp) (o := 560) rfl)
  · exact hkc₆ 552 _ (by omega) (by omega) (hkb₅ 552 _ (by omega) (by rw [hw]; rfl) g568)

/-- **`signed`, the layer loop's registers** (`b94`). -/
theorem forsKey2_spec (r : Run) (hp : Placed Sphincs.SphincsVerify.code r.k) (hpre : r.Pre)
    {m : MachineData} (hA : FK1 r m) :
    Eventually (step1 Host.exe) (fun st ↦ st.pc = r.pc NativeRustcX64.Sphincs.SphincsVerify.b95Offset ∧ r.AtLayer 0 r.forsPk st.data)
      ⟨m, r.pc NativeRustcX64.Sphincs.SphincsVerify.b94Offset⟩ := by
  obtain ⟨hK, h12, hbx, h13, hbp, h568, hD⟩ := hA
  have hw := NativeRustc.length_wordBytes r.idx
  have hP : BytesAt m.dmem (r.off 4072) r.forsPk := by
    have := bytesAt_drop_take hD 0 16 (by rw [NativeRustc.Sphincs.length_hashBytes]; omega)
    rwa [Run.off_add, List.drop_zero, ← forsPk_eq] at this
  refine Run.frameFall r hp hpre Sphincs.SphincsVerify.b94_in_code rfl (List.cons_ne_nil _ _)
    run_b94 rfl rfl hK (knownOK_nil m _) fun m₁ hm₁ hK₁ hkb₁ ↦ .done _ ⟨rfl, ?_⟩
  obtain ⟨hF₁, hI₁, h176⟩ := hK₁
  have hP' : BytesAt (r.env m (fun _ ↦ 0) 0).mem0 ((r.env m (fun _ ↦ 0) 0).base 0 +
      BitVec.ofNat 64 4072) r.forsPk := hP
  exact ⟨by decide, length_forsPk r, hF₁, hI₁, regIs_lit hm₁ (y := .rcx) (c := 4656) rfl,
    regIs_lit hm₁ (y := .rsi) (c := 0) rfl, hm₁.regs .rdx _ rfl, regIs_keep hm₁ rfl hbx,
    regIs_keep hm₁ rfl h12, regIs_keep hm₁ rfl hbp, regIs_keep hm₁ rfl h13,
    regIs_ptr hm₁ (y := .r15) (o := 144) rfl,
    copy hm₁ (r := 0) (r' := 0) (sz := 21632) (o := 144) (o' := 4072) (n := 16) rfl (by decide)
      rfl (length_forsPk r) hP',
    h176, hkb₁ 552 _ (by omega) (by rw [hw]; rfl) h568, hm₁.regs .r14 _ rfl⟩

end

end NativeRustcX64.SphincsVerifyProof.Digest

namespace NativeRustcX64.SphincsVerifyProof

open Digest

public section

/-- **Region 4, the FORS key** (x86-64). -/
theorem forsKey_spec [Host] : ForsKeySpec := by
  intro r hp hc hpre m hA
  exact Run.stage r (forsKey0_spec r hp hc hpre hA) fun m₁ h₁ ↦
    Run.stage r (forsKey1_spec r hp hc hpre h₁) fun m₂ h₂ ↦ forsKey2_spec r hp hpre h₂

end

end NativeRustcX64.SphincsVerifyProof
