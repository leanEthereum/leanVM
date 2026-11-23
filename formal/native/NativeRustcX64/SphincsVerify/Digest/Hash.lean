module

public import NativeRustcX64.SphincsVerify.Digest.Call
public import NativeRustcX64.SphincsVerify.Digest.Exec

/-!
# `h_msg`: `b43 .. b54` (x86-64)

`b43` (directive 451) clears hasher B (`576`, `Hasher::new`), `b44 .. b47` update it with `R` (the
parsed signature's randomizer, `25180`), `PK.seed` (`112`), `PK.root` (`128`) and the message
(`1600`): it has absorbed `hInput r` (`absorb_spec`, at `b48`, directive 473). `b48 .. b50`
clone it to `4096`, update the clone with `BE32(0)` (stored at `9344`) and finalize it to `11392`
(`hash0_spec`); `b51 .. b53` copy the digest to `2048`, clone again, update with `BE32(1)` and
finalize (`hash1_spec`); `b54` copies the second digest to `2080`: `h_msg`'s 64 bytes at `2048`
(`hMsgBytes`), at the bit loop `b55` (directive 517, `hMsg_spec`).
-/

namespace NativeRustcX64.SphincsVerifyProof.Digest

open NativeRustc NativeRustc.Sphincs NativeRustcX64.Sym LeanVM.Protocol.KeccakHash Native.Keccak

@[expose] public section

/-- What `h_msg`'s hasher absorbs before the counter: `R | PK.seed | PK.root | M`. -/
def hInput (r : Run) : List UInt8 := r.sig.randomizer ++ r.seed ++ r.pk.root ++ r.msg

/-- `h_msg`'s call `i`'s digest. -/
def hCall (r : Run) (i : Nat) : List UInt8 := Keccak.hashBytes (hInput r ++ be32 i.toUInt32)

/-- `h_msg`'s 64 bytes. -/
def hMsgBytes (r : Run) : List UInt8 := hCall r 0 ++ hCall r 1

/-- **At `b48`**: what the digest keeps, R13 `0`, R14 hasher B (absorbed `hInput r`), R12 memcpy. -/
def Absorbed (r : Run) [Labels] (m : MachineData) : Prop :=
  Keep r m ∧ Run.RegIs m .r13 0 ∧ Run.RegIs m .r14 (r.off 576) ∧ HasherAt r m 576 (hInput r) ∧
    Run.RegIs m .r12 (Labels.label "memcpy").toBitVec

/-- **At `b51`**: the first digest at `11392`, hasher B, RBP the clone, RBX `BE32(i)`'s place, R15
the digests', and R12 the memcpy entry for the next clone. -/
def Hashed0 (r : Run) [Labels] (m : MachineData) : Prop :=
  Keep r m ∧ Run.RegIs m .r13 0 ∧ Run.RegIs m .r14 (r.off 576) ∧ Run.RegIs m .rbp (r.off 4096) ∧
    Run.RegIs m .rbx (r.off 9344) ∧ Run.RegIs m .r15 (r.off 11392) ∧
    HasherAt r m 576 (hInput r) ∧ BytesAt m.dmem (r.off 11392) (hCall r 0) ∧
    Run.RegIs m .r12 (Labels.label "memcpy").toBitVec

/-- **At `b54`**: the first digest at `2048`, the second at `11392`. -/
def Hashed1 (r : Run) (m : MachineData) : Prop :=
  Keep r m ∧ Run.RegIs m .r13 0 ∧ Run.RegIs m .rbp (r.off 4096) ∧
    BytesAt m.dmem (r.off 2048) (hCall r 0) ∧ BytesAt m.dmem (r.off 11392) (hCall r 1)

/-- Byte `i` of region `r` holds the byte at `o' + i` of region `r'` that a load read. -/
def copies (ws : List Write) (r o r' o' n : Nat) : Bool :=
  (List.range n).all fun i =>
    match findWrite r (o + i) ws with
    | some (.load r'' off k, u) => r'' == r' && off + u == o' + i && decide (u < k) && decide (k ≤ 8)
    | _ => false

end

public section

theorem length_hCall (r : Run) (i : Nat) : (hCall r i).length = 32 :=
  NativeRustc.Sphincs.length_hashBytes _

theorem length_hMsgBytes (r : Run) : (hMsgBytes r).length = 64 := by
  rw [hMsgBytes, List.length_append, length_hCall, length_hCall]

/-- `h_msg`'s bytes are the model's. -/
theorem hMsgBytes_eq (r : Run) : hMsgBytes r = hMsg r.sig.randomizer r.seed r.pk.root r.msg := by
  rw [hMsg, show List.range 2 = [0, 1] from rfl, List.flatMap_cons, List.flatMap_cons,
    List.flatMap_nil, List.append_nil]
  rfl

/-- **Bytes stored from loads**: where the newest write of each byte of `o .. o + n` in region
`r` is a load of the bytes `o' .. o' + n` of region `r'` (`copies`), they hold what those held. -/
theorem copy [Labels] {env : Env} {S : SState} {m : MachineData} (hm : Match env S m)
    {r o r' o' n : Nat} {B : BitVec 64} {sz : Nat}
    (hb : env.regions[r]? = some (B, sz)) (hle : o + n ≤ sz) (hc : copies S.mem r o r' o' n = true)
    {bs : List UInt8} (hl : bs.length = n)
    (h : BytesAt env.mem0 (env.base r' + BitVec.ofNat 64 o') bs) :
    BytesAt m.dmem (B + BitVec.ofNat 64 o) bs := by
  intro i hi
  have hc := List.all_eq_true.mp hc i (List.mem_range.mpr (hl ▸ hi))
  rw [addr_add, hm.mem r B sz hb (o + i) (by omega)]
  unfold memByte
  split at hc
  · rename_i r'' off k u hf
    simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hc
    obtain ⟨⟨⟨rfl, hoff⟩, hu⟩, hk⟩ := hc
    rw [hf]
    simp only [Sym.eval, Option.some.injEq]
    rw [byteOf_load hu hk, hoff, ← addr_add, h i hi]
    rfl
  · cases hc

/-- The frame's 32 bytes at `o'` copied to `o` by the block from `m` to `m₁`. -/
theorem copy32 [Labels] {r : Run} {m m₁ : MachineData} {ret : BitVec 64} {S : SState}
    (hm : Match (r.env m (fun _ ↦ 0) ret) S m₁) {o o' : Nat} (ho : o + 32 ≤ 29392)
    (hc : copies S.mem 0 o 0 o' 32 = true) {bs : List UInt8}
    (hl : bs.length = 32) (h : BytesAt m.dmem (r.off o') bs) : BytesAt m₁.dmem (r.off o) bs :=
  copy hm (sz := 29392) rfl ho hc hl h

/-- The 4 bytes of a literal word store. -/
theorem bytesAt_lit4 [Labels] {r : Run} {m m₁ : MachineData} {ret : BitVec 64} {S : SState}
    (hm : Match (r.env m (fun _ ↦ 0) ret) S m₁) {o v : Nat} (ho : o + 4 ≤ 29392)
    (hw : ∀ i < 4, findWrite 0 (o + i) S.mem = some (.lit v, i)) {bs : List UInt8}
    (hb : (List.range 4).map (byteOf (BitVec.ofNat 64 v)) = bs) : BytesAt m₁.dmem (r.off o) bs := by
  have := hm.bytesAt_write (r := 0) (o := o) (n := 4) (b := r.base) (sz := 29392) rfl ho hw
  rwa [show Sym.eval (r.env m (fun _ ↦ 0) ret) (.lit v) = BitVec.ofNat 64 v from rfl, hb] at this

/-- `n` bytes from byte `k` of bytes in memory. -/
theorem bytesAt_drop_take {d : DataMem} {a : BitVec 64} {bs : List UInt8} (h : BytesAt d a bs)
    (k n : Nat) (hk : k + n ≤ bs.length) :
    BytesAt d (a + BitVec.ofNat 64 k) ((bs.drop k).take n) := by
  intro i hi
  simp only [List.length_take, List.length_drop] at hi
  rw [Sym.addr_add, h (k + i) (by omega)]
  simp [List.getElem_take, List.getElem_drop]

theorem length_msg (r : Run) : r.msg.length = 32 := by
  simp [Run.msg, messageBytes, Native.Keccak.Proof.length_wordsBytes]

theorem length_seed (r : Run) : r.seed.length = 16 := by
  simp [Run.seed, Run.pk, PublicKey.fromBytes, length_pkBytes]

theorem length_root (r : Run) : r.pk.root.length = 16 := by
  simp [Run.pk, PublicKey.fromBytes, length_pkBytes]

/-- `R` in the frame. -/
theorem Keep.rand {r : Run} {m : MachineData} (hK : Keep r m) :
    BytesAt m.dmem (r.off 25180) r.sig.randomizer := by
  have := bytesAt_drop_take hK.2.1.2 4640 16 (by rw [length_sigMem']; omega)
  have e : ((sigMem r.sig).drop 4640).take 16 = r.sig.randomizer := SigMem.sigMem_randomizer r.w
  rwa [Run.off_add, e] at this

/-- `PK.seed` in the frame. -/
theorem Keep.seed {r : Run} {m : MachineData} (hK : Keep r m) :
    BytesAt m.dmem (r.off 112) r.seed := by
  have := bytesAt_drop_take hK.2.1.1 0 16 (by rw [length_pkBytes]; omega)
  rwa [Run.off_add, List.drop_zero] at this

/-- `PK.root` in the frame. -/
theorem Keep.root {r : Run} {m : MachineData} (hK : Keep r m) :
    BytesAt m.dmem (r.off 128) r.pk.root := by
  have := bytesAt_drop_take hK.2.1.1 16 16 (by rw [length_pkBytes])
  rwa [Run.off_add, List.take_of_length_le (by rw [List.length_drop, length_pkBytes])] at this

variable [Host]

/-- **`h_msg`'s hasher absorbs `R | PK.seed | PK.root | M`** (`b43 .. b47`). -/
theorem absorb_spec (r : Run) (hp : Placed Sphincs.SphincsVerify.code r.k) (hc : Callees)
    (hpre : r.Pre) {m : MachineData} (hA : r.AtHMsg m) :
    Eventually (step1 Host.exe) (fun st ↦ st.pc = r.pc NativeRustcX64.Sphincs.SphincsVerify.b48Offset ∧ Absorbed r st.data)
      ⟨m, r.pc NativeRustcX64.Sphincs.SphincsVerify.b43Offset⟩ := by
  obtain ⟨hF, hI, hbp, hmsg, h176, h12⟩ := hA
  have hK : Keep r m := ⟨hF, hI, h176⟩
  have hm32 := length_msg r
  -- b43: `memset` of hasher B
  refine Run.memsetCall r hp hpre hc Sphincs.SphincsVerify.b43_in_code rfl run_b43 rfl rfl
    (a := 576) (n := 344) hK (knownOK_nil m _) rfl rfl rfl (.inl ⟨by decide, by decide⟩)
    fun m₁ hm₁ hkb₁ m₂ hK₂ hS₂ hkc₂ hB₂ ↦ ?_
  have g13 := regIs_of_saved hS₂ rfl (regIs_lit hm₁ (y := .r13) (c := 0) rfl)
  have g14 := regIs_of_saved hS₂ rfl (regIs_ptr hm₁ (y := .r14) (o := 576) rfl)
  have gbp := regIs_of_saved hS₂ rfl (regIs_keep hm₁ rfl hbp)
  have g12 := regIs_of_saved hS₂ rfl (regIs_keep hm₁ rfl h12)
  have gmsg := hkc₂ 1600 _ (by omega) (by omega) (hkb₁ 1600 _ (by omega) (by rw [hm32]; rfl) hmsg)
  have gH : HasherAt r m₂ 576 [] := ⟨_, hB₂, Keccak.holds_new⟩
  -- b44: `R`
  have hrl : r.sig.randomizer.length = 16 := SigMem.length_randomizer r.w
  refine Run.updateCall r hp hpre hc Sphincs.SphincsVerify.b44_in_code rfl run_b44 rfl rfl
    (a := 576) (b := 25180) (n := 16) hK₂ (knownOK_ptr gbp (knownOK_ptr g14 (knownOK_nil m₂ _)))
    rfl rfl rfl (.inl ⟨by decide, by decide⟩) (by decide) (by decide) hrl
    fun m₃ hm₃ hkb₃ ↦ ⟨gH.keepB hkb₃ (by decide) rfl,
      hkb₃ 25180 _ (by rw [hrl]; omega) (by rw [hrl]; rfl)
        hK₂.rand, fun m₄ hK₄ hS₄ hkc₄ hH₄ ↦ ?_⟩
  have g13 := regIs_of_saved hS₄ rfl (regIs_keep hm₃ rfl g13)
  have g14 := regIs_of_saved hS₄ rfl (regIs_ptr hm₃ (y := .r14) (o := 576) rfl)
  have g12 := regIs_of_saved hS₄ rfl (regIs_keep hm₃ rfl g12)
  have gmsg := hkc₄ 1600 _ (by omega) (by omega) (hkb₃ 1600 _ (by omega) (by rw [hm32]; rfl) gmsg)
  -- b45: `PK.seed`
  refine Run.updateCall r hp hpre hc Sphincs.SphincsVerify.b45_in_code rfl run_b45 rfl rfl
    (a := 576) (b := 112) (n := 16) hK₄ (knownOK_ptr g14 (knownOK_nil m₄ _)) rfl rfl rfl
    (.inl ⟨by decide, by decide⟩) (by decide) (by decide) (length_seed r) fun m₅ hm₅ hkb₅ ↦
      ⟨hH₄.keepB hkb₅ (by decide) rfl, hkb₅ 112 _ (by rw [length_seed]; omega) (by rw [length_seed]; rfl) hK₄.seed, fun m₆ hK₆ hS₆ hkc₆ hH₆ ↦ ?_⟩
  have g13 := regIs_of_saved hS₆ rfl (regIs_keep hm₅ rfl g13)
  have g14 := regIs_of_saved hS₆ rfl (regIs_ptr hm₅ (y := .r14) (o := 576) rfl)
  have g12 := regIs_of_saved hS₆ rfl (regIs_keep hm₅ rfl g12)
  have gmsg := hkc₆ 1600 _ (by omega) (by omega) (hkb₅ 1600 _ (by omega) (by rw [hm32]; rfl) gmsg)
  -- b46: `PK.root`
  refine Run.updateCall r hp hpre hc Sphincs.SphincsVerify.b46_in_code rfl run_b46 rfl rfl
    (a := 576) (b := 128) (n := 16) hK₆ (knownOK_ptr g14 (knownOK_nil m₆ _)) rfl rfl rfl
    (.inl ⟨by decide, by decide⟩) (by decide) (by decide) (length_root r) fun m₇ hm₇ hkb₇ ↦
      ⟨hH₆.keepB hkb₇ (by decide) rfl, hkb₇ 128 _ (by rw [length_root]; omega) (by rw [length_root]; rfl) hK₆.root, fun m₈ hK₈ hS₈ hkc₈ hH₈ ↦ ?_⟩
  have g13 := regIs_of_saved hS₈ rfl (regIs_keep hm₇ rfl g13)
  have g14 := regIs_of_saved hS₈ rfl (regIs_ptr hm₇ (y := .r14) (o := 576) rfl)
  have g12 := regIs_of_saved hS₈ rfl (regIs_keep hm₇ rfl g12)
  have gmsg := hkc₈ 1600 _ (by omega) (by omega) (hkb₇ 1600 _ (by omega) (by rw [hm32]; rfl) gmsg)
  -- b47: the message
  refine Run.updateCall r hp hpre hc Sphincs.SphincsVerify.b47_in_code rfl run_b47 rfl rfl
    (a := 576) (b := 1600) (n := 32) hK₈ (knownOK_ptr g14 (knownOK_nil m₈ _)) rfl rfl rfl
    (.inl ⟨by decide, by decide⟩) (by decide) (by decide) hm32 fun m₉ hm₉ hkb₉ ↦
      ⟨hH₈.keepB hkb₉ (by decide) rfl, hkb₉ 1600 _ (by omega) (by rw [hm32]; rfl) gmsg,
        fun m₁₀ hK₁₀ hS₁₀ _ hH₁₀ ↦ .done _ ⟨rfl, hK₁₀, ?_, ?_, ?_,
          regIs_of_saved hS₁₀ rfl (regIs_keep hm₉ rfl g12)⟩⟩
  · exact regIs_of_saved hS₁₀ rfl (regIs_keep hm₉ rfl g13)
  · exact regIs_of_saved hS₁₀ rfl (regIs_ptr hm₉ (y := .r14) (o := 576) rfl)
  · simpa [hInput, List.append_assoc] using hH₁₀

/-- **`h_msg`'s first call** (`b48 .. b50`). -/
theorem hash0_spec (r : Run) (hp : Placed Sphincs.SphincsVerify.code r.k) (hc : Callees)
    (hpre : r.Pre) {m : MachineData} (hA : Absorbed r m) :
    Eventually (step1 Host.exe) (fun st ↦ st.pc = r.pc NativeRustcX64.Sphincs.SphincsVerify.b51Offset ∧ Hashed0 r st.data)
      ⟨m, r.pc NativeRustcX64.Sphincs.SphincsVerify.b48Offset⟩ := by
  obtain ⟨hK, h13, h14, hB, h12⟩ := hA
  obtain ⟨hb, hbB, hbh⟩ := hB
  have hbl := Keccak.length_of_holds hbh
  -- b48: the clone
  refine Run.memcpyCall r hp hpre hc Sphincs.SphincsVerify.b48_in_code rfl run_b48 rfl rfl
    (a := 4096) (b := 576) (n := 344) hK (knownOK_ptr h14 ⟨h12, trivial⟩) rfl rfl rfl
    (.inl ⟨by decide, by decide⟩) (by decide) (by decide) hbl fun m₁ hm₁ hkb₁ ↦
      ⟨hkb₁ 576 hb (by omega) (by rw [hbl]; rfl) hbB, fun m₂ hK₂ hS₂ hkc₂ hA₂ ↦ ?_⟩
  have g13 := regIs_of_saved hS₂ rfl (regIs_keep hm₁ rfl h13)
  have g14 := regIs_of_saved hS₂ rfl (regIs_ptr hm₁ (y := .r14) (o := 576) rfl)
  have gbp := regIs_of_saved hS₂ rfl (regIs_ptr hm₁ (y := .rbp) (o := 4096) rfl)
  have g12 := regIs_of_saved hS₂ rfl
    (hm₁.regs .r12 _ rfl : Run.RegIs m₁ .r12 (Labels.label "memcpy").toBitVec)
  have gB : HasherAt r m₂ 576 (hInput r) :=
    ⟨hb, hkc₂ 576 hb (by omega) (by omega) (hkb₁ 576 hb (by omega) (by rw [hbl]; rfl) hbB), hbh⟩
  have gA : HasherAt r m₂ 4096 (hInput r) := ⟨hb, hA₂, hbh⟩
  -- b49: `BE32(0)`
  refine Run.updateCall r hp hpre hc Sphincs.SphincsVerify.b49_in_code rfl run_b49 rfl rfl
    (a := 4096) (b := 9344) (n := 4) hK₂ (knownOK_ptr gbp (knownOK_nil m₂ _)) rfl rfl rfl
    (.inl ⟨by decide, by decide⟩) (by decide) (by decide) (bs := be32 (0 : Nat).toUInt32) rfl
    fun m₃ hm₃ hkb₃ ↦ ⟨gA.keepB hkb₃ (by decide) rfl, bytesAt_lit4 hm₃ (v := 0) (by decide)
      (by decide) (by decide), fun m₄ hK₄ hS₄ hkc₄ hH₄ ↦ ?_⟩
  have g13 := regIs_of_saved hS₄ rfl (regIs_keep hm₃ rfl g13)
  have g14 := regIs_of_saved hS₄ rfl (regIs_keep hm₃ rfl g14)
  have gbp := regIs_of_saved hS₄ rfl (regIs_ptr hm₃ (y := .rbp) (o := 4096) rfl)
  have gbx := regIs_of_saved hS₄ rfl (regIs_ptr hm₃ (y := .rbx) (o := 9344) rfl)
  have g12 := regIs_of_saved hS₄ rfl (regIs_keep hm₃ rfl g12)
  have gB := (gB.keepB hkb₃ (by decide) rfl).keepC hkc₄ (by decide) (by decide)
  -- b50: the first digest
  refine Run.finalizeCall r hp hpre hc Sphincs.SphincsVerify.b50_in_code rfl run_b50 rfl rfl
    (o := 11392) (a := 4096) hK₄ (knownOK_ptr gbp (knownOK_nil m₄ _)) rfl rfl
    (.inl ⟨by decide, by decide⟩) (by decide) (by decide) fun m₅ hm₅ hkb₅ ↦
      ⟨hH₄.keepB hkb₅ (by decide) rfl, fun m₆ hK₆ hS₆ hkc₆ hD₆ ↦
        .done _ ⟨rfl, hK₆, ?_, ?_, ?_, ?_, ?_, ?_, hD₆,
          regIs_of_saved hS₆ rfl (regIs_keep hm₅ rfl g12)⟩⟩
  · exact regIs_of_saved hS₆ rfl (regIs_keep hm₅ rfl g13)
  · exact regIs_of_saved hS₆ rfl (regIs_keep hm₅ rfl g14)
  · exact regIs_of_saved hS₆ rfl (regIs_ptr hm₅ (y := .rbp) (o := 4096) rfl)
  · exact regIs_of_saved hS₆ rfl (regIs_keep hm₅ rfl gbx)
  · exact regIs_of_saved hS₆ rfl (regIs_ptr hm₅ (y := .r15) (o := 11392) rfl)
  · exact (gB.keepB hkb₅ (by decide) rfl).keepC hkc₆ (by decide) (by decide)

/-- **`h_msg`'s second call** (`b51 .. b53`). -/
theorem hash1_spec (r : Run) (hp : Placed Sphincs.SphincsVerify.code r.k) (hc : Callees)
    (hpre : r.Pre) {m : MachineData} (hH : Hashed0 r m) :
    Eventually (step1 Host.exe) (fun st ↦ st.pc = r.pc NativeRustcX64.Sphincs.SphincsVerify.b54Offset ∧ Hashed1 r st.data)
      ⟨m, r.pc NativeRustcX64.Sphincs.SphincsVerify.b51Offset⟩ := by
  obtain ⟨hK, h13, h14, hbp, hbx, h15, hB, hD, h12⟩ := hH
  obtain ⟨hb, hbB, hbh⟩ := hB
  have hbl := Keccak.length_of_holds hbh
  have hcl := length_hCall r 0
  -- b51: the first digest copied, the clone again
  refine Run.memcpyCall r hp hpre hc Sphincs.SphincsVerify.b51_in_code rfl run_b51 rfl rfl
    (a := 4096) (b := 576) (n := 344) hK (knownOK_ptr hbp (knownOK_ptr h14 ⟨h12, trivial⟩))
    rfl rfl rfl (.inl ⟨by decide, by decide⟩) (by decide) (by decide) hbl fun m₁ hm₁ hkb₁ ↦
      ⟨hkb₁ 576 hb (by omega) (by rw [hbl]; rfl) hbB, fun m₂ hK₂ hS₂ hkc₂ hA₂ ↦ ?_⟩
  have g13 := regIs_of_saved hS₂ rfl (regIs_keep hm₁ rfl h13)
  have gbp := regIs_of_saved hS₂ rfl (regIs_ptr hm₁ (y := .rbp) (o := 4096) rfl)
  have gbx := regIs_of_saved hS₂ rfl (regIs_keep hm₁ rfl hbx)
  have g15 := regIs_of_saved hS₂ rfl (regIs_keep hm₁ rfl h15)
  have gD := hkc₂ 2048 _ (by omega) (by omega)
    (copy32 hm₁ (o := 2048) (o' := 11392) (by decide) rfl hcl hD)
  have gA : HasherAt r m₂ 4096 (hInput r) := ⟨hb, hA₂, hbh⟩
  -- b52: `BE32(1)`
  refine Run.updateCall r hp hpre hc Sphincs.SphincsVerify.b52_in_code rfl run_b52 rfl rfl
    (a := 4096) (b := 9344) (n := 4) hK₂ (knownOK_ptr gbp (knownOK_ptr gbx (knownOK_nil m₂ _)))
    rfl rfl rfl (.inl ⟨by decide, by decide⟩) (by decide) (by decide)
    (bs := be32 (1 : Nat).toUInt32) rfl fun m₃ hm₃ hkb₃ ↦
      ⟨gA.keepB hkb₃ (by decide) rfl, bytesAt_lit4 hm₃ (v := 16777216) (by decide)
        (by decide) (by decide), fun m₄ hK₄ hS₄ hkc₄ hH₄ ↦ ?_⟩
  have g13 := regIs_of_saved hS₄ rfl (regIs_keep hm₃ rfl g13)
  have gbp := regIs_of_saved hS₄ rfl (regIs_ptr hm₃ (y := .rbp) (o := 4096) rfl)
  have g15 := regIs_of_saved hS₄ rfl (regIs_keep hm₃ rfl g15)
  have gD := hkc₄ 2048 _ (by omega) (by omega) (hkb₃ 2048 _ (by omega) (by rw [hcl]; rfl) gD)
  -- b53: the second digest
  refine Run.finalizeCall r hp hpre hc Sphincs.SphincsVerify.b53_in_code rfl run_b53 rfl rfl
    (o := 11392) (a := 4096) hK₄ (knownOK_ptr gbp (knownOK_ptr g15 (knownOK_nil m₄ _))) rfl rfl
    (.inl ⟨by decide, by decide⟩) (by decide) (by decide) fun m₅ hm₅ hkb₅ ↦
      ⟨hH₄.keepB hkb₅ (by decide) rfl, fun m₆ hK₆ hS₆ hkc₆ hD₆ ↦
        .done _ ⟨rfl, hK₆, ?_, ?_, ?_, hD₆⟩⟩
  · exact regIs_of_saved hS₆ rfl (regIs_keep hm₅ rfl g13)
  · exact regIs_of_saved hS₆ rfl (regIs_ptr hm₅ (y := .rbp) (o := 4096) rfl)
  · exact hkc₆ 2048 _ (by omega) (by omega) (hkb₅ 2048 _ (by omega) (by rw [hcl]; rfl) gD)

end

end NativeRustcX64.SphincsVerifyProof.Digest
