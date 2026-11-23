module

public import NativeRustcX64.SphincsVerify.Chains.OuterBase

/-!
# A chain on x86-64: its end stored, its word, its last step's jump

`b116` stores chain `i`'s end at `28280 + 16 i` and goes on with chain `i + 1` or, after chain
63, to `b151` (`seg_b116`); `b118` stores the chain's word `BE32(i)` at `72` (`seg_b118`); `b150`
jumps back to `b116` after the steps (`seg_b150`).
-/

namespace NativeRustcX64.SphincsVerifyProof.Chains

open NativeRustc NativeRustc.Sphincs NativeRustcX64.Sym NativeRustcX64.Sphincs.SphincsVerify
open LeanVM.Protocol.KeccakHash

@[expose] public section

/-- Chain `i`'s end on layer `l` for the codeword `x`, as `wots_leaf` computes it. -/
def chainEnd (r : Run) (l : Nat) (x : List UInt8) (i : Nat) : List UInt8 :=
  chain r.seed (r.key l) i (x.getD i 0).toNat (3 - (x.getD i 0).toNat)
    ((r.layerSig l).wots.getD i [])

end

public section

theorem chainEnds_eq (r : Run) (l : Nat) (x : List UInt8) :
    r.chainEnds l x = (List.range 64).map (chainEnd r l x) := rfl

theorem bytes_word_of {x : BitVec 64} {w : UInt64} (hv : x = w.toBitVec) :
    (List.range 8).map (byteOf x) = wordBytes w := by
  rw [hv, ← Hasher.wordBytes_ofBitVec]

theorem beq_ofNat {a b : Nat} (ha : a < 2 ^ 64) (hb : b < 2 ^ 64) :
    (BitVec.ofNat 64 a == BitVec.ofNat 64 b) = decide (a = b) := by
  by_cases h : a = b
  · subst h
    simp
  · have : BitVec.ofNat 64 a ≠ BitVec.ofNat 64 b := fun he ↦ h (by
      have := congrArg BitVec.toNat he
      rwa [BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb]
        at this)
    simp [h, this]

/-- The ends so far, appended to. -/
theorem KeepRest.extend {r : Run} {l : Nat} {x E e : List UInt8} {m : MachineData}
    (hK : KeepRest r l x E m) (h : BytesAt m.dmem (r.off 28280) (E ++ e)) :
    KeepRest r l x (E ++ e) m :=
  ⟨hK.1, hK.2.1, hK.2.2.1, hK.2.2.2.1, hK.2.2.2.2.1, h⟩

/-- A frame word loaded in an environment whose region 0 starts at the frame's base. -/
theorem load0_word [Labels] {r : Run} {m : MachineData} {rest : List (BitVec 64 × Nat)}
    {n : Nat} {vars : Nat → BitVec 64} {ret : BitVec 64} {o : Nat} {w : UInt64}
    (h : BytesAt m.dmem (r.off o) (wordBytes w)) :
    (Env.ofMachine m ((r.off 0, n) :: rest) vars ret).load 0 o 8 = w.toBitVec := by
  have h' : BytesAt (Env.ofMachine m ((r.off 0, n) :: rest) vars ret).mem0
      ((Env.ofMachine m ((r.off 0, n) :: rest) vars ret).base 0 + BitVec.ofNat 64 o) (wordBytes w) := by
    show BytesAt m.dmem (r.off 0 + BitVec.ofNat 64 o) _
    rw [Run.off_add, Nat.zero_add]
    exact h
  rw [Env.load_of_bytesAt (NativeRustc.length_wordBytes _) h', ofInt_ofBytes_wordBytes]

variable [Host] {r : Run}

/-- **`b150`**: back to `b116`. -/
theorem seg_b150 (hp : Placed Sphincs.SphincsVerify.code r.k) (hpre : r.Pre) {l : Nat}
    {x E : List UInt8} (hx : x.length = 64) (hE : E.length ≤ 1024) {i : Nat} {e : List UInt8}
    (he : e.length = 16) {R : MachineState → Prop} {m : MachineData} (hK : Keep r l x E i m)
    (h12 : Run.RegIs m .r12 (r.off 4096)) (hcell : BytesAt m.dmem (r.off 184) e)
    (hf : Funcs m)
    (cont : ∀ m', Keep r l x E i m' → Run.RegIs m' .r12 (r.off 4096) →
      BytesAt m'.dmem (r.off 184) e → Funcs m' →
      Eventually (step1 Host.exe) R ⟨m', r.pc NativeRustcX64.Sphincs.SphincsVerify.b116Offset⟩) :
    Eventually (step1 Host.exe) R ⟨m, r.pc NativeRustcX64.Sphincs.SphincsVerify.b150Offset⟩ := by
  have hwf := r.frame_wf hpre hK.1.2.2.2 (fun _ ↦ 0) 0
  have hm := match_frameS hpre hK.1 hK.2.1 (ret := 0) (k := []) trivial
  refine blk r hp b150_in_code (List.cons_ne_nil _ _) run_b150 hwf (fun _ h ↦ nomatch h) hm
    fun st hm1 hpc ↦ ?_
  exact pc_at (hpc.trans (labelAt r hp b116_in_code rfl))
    (cont _ (Keep.of_block hpre hx hE hK hm1 hwf (by decide +kernel) rfl) (regIs_reg hm1 rfl h12)
      (r.bytesAt_kept hpre hm1 hwf (by omega) hcell (by rw [he]; decide +kernel))
      ⟨regIs_reg hm1 rfl hf.1, regIs_reg hm1 rfl hf.2⟩)

/-- **`b118`**: the chain's word `BE32(i)` at `72`; then the steps at `b119`. -/
theorem seg_b118 (hp : Placed Sphincs.SphincsVerify.code r.k) (hpre : r.Pre) {l : Nat}
    {x E : List UInt8} (hx : x.length = 64) (hE : E.length ≤ 1024) {i : Nat} (hi : i < 64)
    {d : Nat} {v : List UInt8} (hv : v.length = 16) {R : MachineState → Prop} {m : MachineData}
    (hF : r.Frame m) (hK : KeepRest r l x E m) (h80 : r.WordAt m 80 i.toUInt64)
    (h168 : r.WordAt m 168 (16 * i).toUInt64) (hsi : Run.RegIs m .rsi (BitVec.ofNat 64 d))
    (h12 : Run.RegIs m .r12 (r.off 4096)) (hcell : BytesAt m.dmem (r.off 184) v)
    (hf : Funcs m)
    (cont : ∀ m', Keep r l x E i m' → Regs r m' d → BytesAt m'.dmem (r.off 184) v →
      Eventually (step1 Host.exe) R ⟨m', r.pc NativeRustcX64.Sphincs.SphincsVerify.b119Offset⟩) :
    Eventually (step1 Host.exe) R ⟨m, r.pc NativeRustcX64.Sphincs.SphincsVerify.b118Offset⟩ := by
  have hwf := r.frame_wf hpre hF.2.2.2 (fun _ ↦ 0) 0
  have hm := match_frameS hpre hF hK (ret := 0) (k := []) trivial
  refine blk r hp b118_in_code (List.cons_ne_nil _ _) run_b118 hwf (fun _ h ↦ nomatch h) hm
    fun st hm1 hpc ↦ ?_
  have hw := frame_write_val hm1 (o := 72) (n := 4)
    (v := .bin .shl .W32 (.load 0 80 8) (.lit 24)) (by decide) (by decide +kernel)
  have hl : (r.env m (fun _ ↦ 0) 0).load 0 80 8 = BitVec.ofNat 64 i := load_word h80
  have e72 : (Sym.bin .shl .W32 (.load 0 80 8) (.lit 24)).eval (r.env m (fun _ ↦ 0) 0) =
      BinOp.apply .shl .W32 (BitVec.ofNat 64 i) (BitVec.ofNat 64 24) := by
    show BinOp.apply .shl .W32 ((r.env m (fun _ ↦ 0) 0).load 0 80 8) (BitVec.ofNat 64 24) = _
    rw [hl]
  rw [e72, bytes_chainWord hi] at hw
  have hK1 : Keep r l x E i st.data :=
    ⟨Run.Frame.of_match r hpre hF hm1 hwf rfl (by decide +kernel),
      hK.of_block hpre hx hE hm1 hwf (by decide +kernel),
      r.bytesAt_kept hpre hm1 hwf (by simp [NativeRustc.length_wordBytes]) h80
        (by rw [NativeRustc.length_wordBytes]; decide +kernel),
      r.bytesAt_kept hpre hm1 hwf (by simp [NativeRustc.length_wordBytes]) h168
        (by rw [NativeRustc.length_wordBytes]; decide +kernel), hw⟩
  exact pc_at (a := r.pc NativeRustcX64.Sphincs.SphincsVerify.b119Offset) (hpc.trans rfl) (cont _ hK1
    ⟨regIs_reg hm1 rfl hsi, regIs_reg hm1 rfl h12,
      regIs_reg hm1 rfl hf.1, regIs_reg hm1 rfl hf.2⟩
    (r.bytesAt_kept hpre hm1 hwf (by omega) hcell (by rw [hv]; decide +kernel)))

end

end NativeRustcX64.SphincsVerifyProof.Chains
