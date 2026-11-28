module

public import NativeRustcArm.SphincsVerify.Digest.Absorb
public import NativeRustcArm.SphincsVerify.Digest.Loop

/-!
# `h_msg`'s two calls: `b50 .. b56`

The hasher at `26768` (`hInput r` absorbed) is cloned to `16400` (`memcpy`), the clone updated
with `BE32(0)` (stored at `23696`) and finalized to `25744` (`b50 .. b52`, `hash0_spec`); the
digest copied to `24720`, the clone made again, updated with `BE32(1)` and finalized
(`b53 .. b55`, `hash1_spec`); the second digest copied to `24752`, the loop's registers set
(`b56`, `hMsg_spec`): `h_msg`'s 64 bytes at `24720` (`hMsgBytes`), the loop's first turn.
-/

namespace NativeRustcArm.SphincsVerifyProof.Digest

open NativeRustc NativeRustc.Sphincs NativeRustcArm.Sym LeanVM.Protocol.KeccakHash Native.Keccak

@[expose] public section

/-- `h_msg`'s call `i`'s digest. -/
def hCall (r : Run) (i : Nat) : List UInt8 := Keccak.hashBytes (hInput r ++ be32 i.toUInt32)

/-- **At `b53`**: the first digest at `25744`, the hasher at `26768`, X23 `21648`. -/
def Hashed0 (r : Run) (m : MachineData) : Prop :=
  Keep r m ∧ Run.RegIs m .X21 (r.off 24720) ∧ Run.RegIs m .X23 (r.off 21648) ∧
    HasherAt r m 26768 (hInput r) ∧ BytesAt m.dmem (r.off 25744) (hCall r 0)

/-- **At `b56`**: the first digest at `24720`, the second at `25744`. -/
def Hashed1 (r : Run) (m : MachineData) : Prop :=
  Keep r m ∧ Run.RegIs m .X21 (r.off 24720) ∧ Run.RegIs m .X23 (r.off 21648) ∧
    BytesAt m.dmem (r.off 24720) (hCall r 0) ∧ BytesAt m.dmem (r.off 25744) (hCall r 1)

/-- `h_msg`'s 64 bytes. -/
def hMsgBytes (r : Run) : List UInt8 := hCall r 0 ++ hCall r 1

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

/-- Byte `i` of region `r` holds the byte at `o' + i` of region `r'` that a load read. -/
@[expose] def copies (ws : List Write) (r o r' o' n : Nat) : Bool :=
  (List.range n).all fun i =>
    match findWrite r (o + i) ws with
    | some (.load r'' off k, u) => r'' == r' && off + u == o' + i && decide (u < k) && decide (k ≤ 8)
    | _ => false

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
theorem copy32 [Labels] {r : Run} {m m₁ : MachineData} {S : SState} (hm : Match (r.env m) S m₁)
    {o o' : Nat} (ho : o + 32 ≤ 29376) (hc : copies S.mem 0 o 0 o' 32 = true) {bs : List UInt8}
    (hl : bs.length = 32) (h : BytesAt m.dmem (r.off o') bs) : BytesAt m₁.dmem (r.off o) bs :=
  copy hm (sz := 29376) rfl ho hc hl h

/-- The 4 bytes of a literal word store. -/
theorem bytesAt_lit4 [Labels] {r : Run} {m m₁ : MachineData} {S : SState}
    (hm : Match (r.env m) S m₁) {o v : Nat} (ho : o + 4 ≤ 29376)
    (hw : ∀ i < 4, findWrite 0 (o + i) S.mem = some (.lit v, i)) {bs : List UInt8}
    (hb : (List.range 4).map (byteOf (BitVec.ofNat 64 v)) = bs) : BytesAt m₁.dmem (r.off o) bs := by
  have := hm.bytesAt_write (r := 0) (o := o) (n := 4) (b := r.base) (sz := 29376) rfl ho hw
  rwa [show Sym.eval (r.env m) (.lit v) = BitVec.ofNat 64 v from rfl, hb] at this

variable [NativeRustcArm.Host]

/-- **`h_msg`'s first call** (`b50 .. b52`). -/
theorem hash0_spec (r : Run) (hp : Placed Sphincs.SphincsVerify.code r.k) (hc : Callees)
    (hpre : r.Pre) {m : MachineData} (hA : Absorbed r m) :
    Eventually (step1 NativeRustcArm.Host.exe) (fun st ↦ st.pc = r.pc NativeRustcArm.Sphincs.SphincsVerify.b53Offset ∧ Hashed0 r st.data)
      ⟨m, r.pc NativeRustcArm.Sphincs.SphincsVerify.b50Offset⟩ := by
  obtain ⟨hK, h21, hB⟩ := hA
  obtain ⟨hb, hbB, hbh⟩ := hB
  have hbl := Keccak.length_of_holds hbh
  -- b50: the clone
  refine Run.memcpyCall r hp hpre hc Sphincs.SphincsVerify.b50_in_code rfl run_b50 rfl
    (a := 16400) (b := 26768) (n := 344) hK (knownOK_nil m) rfl rfl rfl ⟨by decide, by decide⟩
    (by decide) (by decide) hbl fun m₁ hm₁ hK₁ hkb₁ ↦
      ⟨hkb₁ 26768 hb (by omega) (by rw [hbl]; rfl) hbB, fun m₂ hK₂ hS₂ hkc₂ hA₂ ↦ ?_⟩
  have g21 := regIs_of_saved hS₂ rfl (regIs_keep hm₁ rfl h21)
  have gB : HasherAt r m₂ 26768 (hInput r) :=
    ⟨hb, hkc₂ 26768 hb (by omega) (by omega) (hkb₁ 26768 hb (by omega) (by rw [hbl]; rfl) hbB), hbh⟩
  have gA : HasherAt r m₂ 16400 (hInput r) := ⟨hb, hA₂, hbh⟩
  -- b51: `BE32(0)`
  refine Run.updateCall r hp hpre hc Sphincs.SphincsVerify.b51_in_code rfl run_b51 rfl
    (a := 16400) (b := 23696) (n := 4) hK₂ (knownOK_nil m₂) rfl rfl rfl ⟨by decide, by decide⟩
    (by decide) (by decide) (bs := be32 (0 : Nat).toUInt32) rfl fun m₃ hm₃ hK₃ hkb₃ ↦
      ⟨gA.keepB hkb₃ (by decide) rfl, bytesAt_lit4 hm₃ (v := 0) (by decide)
        (fun i hi ↦ findWrite_head (ws := []) hi) (by decide), fun m₄ hK₄ hS₄ hkc₄ hH₄ ↦ ?_⟩
  have g21 := regIs_of_saved hS₄ rfl (regIs_keep hm₃ rfl g21)
  have g23 := regIs_of_saved hS₄ rfl (regIs_ptr hm₃ (y := .X23) (o := 21648) rfl)
  have gB := (gB.keepB hkb₃ (by decide) rfl).keepC hkc₄ (by decide) (by decide)
  -- b52: the first digest
  refine Run.finalizeCall r hp hpre hc Sphincs.SphincsVerify.b52_in_code rfl run_b52 rfl
    (o := 25744) (a := 16400) hK₄ (knownOK_nil m₄) rfl rfl ⟨by decide, by decide⟩ (by decide)
    (by decide) fun m₅ hm₅ hK₅ hkb₅ ↦
      ⟨hH₄.keepB hkb₅ (by decide) rfl, fun m₆ hK₆ hS₆ hkc₆ hD₆ ↦ .done _ ⟨rfl, hK₆, ?_, ?_, ?_, hD₆⟩⟩
  · exact regIs_of_saved hS₆ rfl (regIs_keep hm₅ rfl g21)
  · exact regIs_of_saved hS₆ rfl (regIs_keep hm₅ rfl g23)
  · exact (gB.keepB hkb₅ (by decide) rfl).keepC hkc₆ (by decide) (by decide)

/-- **`h_msg`'s second call** (`b53 .. b55`). -/
theorem hash1_spec (r : Run) (hp : Placed Sphincs.SphincsVerify.code r.k) (hc : Callees)
    (hpre : r.Pre) {m : MachineData} (hH : Hashed0 r m) :
    Eventually (step1 NativeRustcArm.Host.exe) (fun st ↦ st.pc = r.pc NativeRustcArm.Sphincs.SphincsVerify.b56Offset ∧ Hashed1 r st.data)
      ⟨m, r.pc NativeRustcArm.Sphincs.SphincsVerify.b53Offset⟩ := by
  obtain ⟨hK, h21, h23, hB, hD⟩ := hH
  obtain ⟨hb, hbB, hbh⟩ := hB
  have hbl := Keccak.length_of_holds hbh
  -- b53: the first digest copied, the clone again
  refine Run.memcpyCall r hp hpre hc Sphincs.SphincsVerify.b53_in_code rfl run_b53 rfl
    (a := 16400) (b := 26768) (n := 344) hK (knownOK_nil m) rfl rfl rfl ⟨by decide, by decide⟩
    (by decide) (by decide) hbl fun m₁ hm₁ hK₁ hkb₁ ↦
      ⟨hkb₁ 26768 hb (by omega) (by rw [hbl]; rfl) hbB, fun m₂ hK₂ hS₂ hkc₂ hA₂ ↦ ?_⟩
  have g21 := regIs_of_saved hS₂ rfl (regIs_keep hm₁ rfl h21)
  have g23 := regIs_of_saved hS₂ rfl (regIs_keep hm₁ rfl h23)
  have gD := hkc₂ 24720 _ (by rw [length_hCall]; omega) (by rw [length_hCall]; omega)
    (copy32 hm₁ (o := 24720) (o' := 25744) (by decide) rfl (length_hCall r 0) hD)
  have gA : HasherAt r m₂ 16400 (hInput r) := ⟨hb, hA₂, hbh⟩
  -- b54: `BE32(1)`
  refine Run.updateCall r hp hpre hc Sphincs.SphincsVerify.b54_in_code rfl run_b54 rfl
    (a := 16400) (b := 23696) (n := 4) hK₂ (knownOK_ptr g23 (knownOK_nil m₂)) rfl rfl rfl
    ⟨by decide, by decide⟩ (by decide) (by decide) (bs := be32 (1 : Nat).toUInt32) rfl
    fun m₃ hm₃ hK₃ hkb₃ ↦
      ⟨gA.keepB hkb₃ (by decide) rfl, bytesAt_lit4 hm₃ (v := 16777216) (by decide)
        (fun i hi ↦ findWrite_head (ws := []) hi) (by decide), fun m₄ hK₄ hS₄ hkc₄ hH₄ ↦ ?_⟩
  have g21 := regIs_of_saved hS₄ rfl (regIs_keep hm₃ rfl g21)
  have g23 := regIs_of_saved hS₄ rfl (regIs_ptr hm₃ (y := .X23) (o := 21648) rfl)
  have gD := hkc₄ 24720 _ (by rw [length_hCall]; omega) (by rw [length_hCall]; omega)
    (hkb₃ 24720 _ (by rw [length_hCall]; omega) (by rw [length_hCall]; rfl) gD)
  -- b55: the second digest
  refine Run.finalizeCall r hp hpre hc Sphincs.SphincsVerify.b55_in_code rfl run_b55 rfl
    (o := 25744) (a := 16400) hK₄ (knownOK_nil m₄) rfl rfl ⟨by decide, by decide⟩ (by decide)
    (by decide) fun m₅ hm₅ hK₅ hkb₅ ↦
      ⟨hH₄.keepB hkb₅ (by decide) rfl, fun m₆ hK₆ hS₆ hkc₆ hD₆ ↦ .done _ ⟨rfl, hK₆, ?_, ?_, ?_, hD₆⟩⟩
  · exact regIs_of_saved hS₆ rfl (regIs_keep hm₅ rfl g21)
  · exact regIs_of_saved hS₆ rfl (regIs_keep hm₅ rfl g23)
  · exact hkc₆ 24720 _ (by rw [length_hCall]; omega) (by rw [length_hCall]; omega)
      (hkb₅ 24720 _ (by rw [length_hCall]; omega) (by rw [length_hCall]; rfl) gD)

/-- **`h_msg` in place, the loop's first turn** (`b56`). -/
theorem hMsg_spec (r : Run) (hp : Placed Sphincs.SphincsVerify.code r.k) (hpre : r.Pre)
    {m : MachineData} (hH : Hashed1 r m) :
    Eventually (step1 NativeRustcArm.Host.exe)
      (fun st ↦ st.pc = r.pc NativeRustcArm.Sphincs.SphincsVerify.b57Offset ∧ LoopInv r (hMsgBytes r) 0 st.data) ⟨m, r.pc NativeRustcArm.Sphincs.SphincsVerify.b56Offset⟩ := by
  obtain ⟨hK, h21, h23, hD0, hD1⟩ := hH
  refine Run.frameFall r hp hpre Sphincs.SphincsVerify.b56_in_code rfl (List.cons_ne_nil _ _)
    run_b56 rfl hK (knownOK_nil m) fun m₁ hm₁ hK₁ hkb₁ ↦ .done _ ⟨rfl, by decide, hK₁,
      regIs_lit hm₁ rfl, regIs_ptr hm₁ rfl, regIs_lit hm₁ rfl, regIs_keep hm₁ rfl h21,
      regIs_keep hm₁ rfl h23, ?_, fun i hi ↦ absurd hi (by rw [length_leavesBytes]; omega)⟩
  refine bytesAt_append (hkb₁ 24720 _ (by rw [length_hCall]; omega) (by rw [length_hCall]; rfl) hD0) ?_
  rw [length_hCall, Run.off_add]
  exact copy32 hm₁ (o := 24752) (o' := 25744) (by decide) rfl (length_hCall r 1) hD1

end

end NativeRustcArm.SphincsVerifyProof.Digest
