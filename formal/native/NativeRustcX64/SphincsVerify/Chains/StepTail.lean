module

public import NativeRustcX64.SphincsVerify.Chains.StepBase

/-!
# A chain's step on x86-64, its end: the final absorb and the new value

From the padded block's bytes at `2048` and the zero state of hasher A (`4096`): `b148` XORs the
padded block into the state and calls `keccak_f` (`seg_b148`), `b149` copies the first 16 bytes
to the chain's value at `184` and goes back to the step's head `b119` or on to `b150`
(`seg_b149`).
-/

namespace NativeRustcX64.SphincsVerifyProof.Chains

open NativeRustc NativeRustc.Sphincs NativeRustcX64.Sym NativeRustcX64.Sphincs.SphincsVerify
open NativeRustcX64.SphincsVerifyProof.InlineTh LeanVM.Protocol.KeccakHash

variable [Host] {r : Run}

@[expose] public section

/-- What follows a step that leaves the chain's value `th` of the padded `T`: from the frame's
state after `b149`, at `b119` for the next step or `b150` after position 2. -/
def StepCont (r : Run) (l : Nat) (x E : List UInt8) (i pos : Nat) (T : List UInt8)
    (R : MachineState → Prop) : Prop :=
  ∀ m', Keep r l x E i m' → Regs r m' (pos + 1) →
    BytesAt m'.dmem (r.off 184)
      ((Keccak.keccakF (Keccak.xorBlock (List.replicate 200 0) (Keccak.finalBlock T))).take 16) →
    Eventually (step1 Host.exe) R ⟨m', if pos + 1 = 3 then r.pc NativeRustcX64.Sphincs.SphincsVerify.b150Offset else r.pc NativeRustcX64.Sphincs.SphincsVerify.b119Offset⟩

end

public section

/-- **`b149`**: the first 16 bytes of hasher A become the chain's value; on to the next step or,
after position 2, to `b150`. -/
theorem seg_b149 (hp : Placed Sphincs.SphincsVerify.code r.k) (hpre : r.Pre) {l : Nat}
    {x E : List UInt8} (hx : x.length = 64) (hE : E.length ≤ 1024) {i pos : Nat} (hpos : pos ≤ 2)
    {A : List UInt8} (hA16 : 16 ≤ A.length) {R : MachineState → Prop} {m : MachineData}
    (hK : Keep r l x E i m) (h12 : Run.RegIs m .r12 (r.off 4096))
    (h64 : r.WordAt m 64 (pos + 1).toUInt64) (hA : BytesAt m.dmem (r.off 4096) A)
    (hcopy : Run.RegIs m .r15 (Labels.label "memcpy").toBitVec)
    (hset : Run.RegIs m .rbx (Labels.label "memset").toBitVec)
    (cont : ∀ m', Keep r l x E i m' → Regs r m' (pos + 1) → BytesAt m'.dmem (r.off 184) (A.take 16) →
      Eventually (step1 Host.exe) R ⟨m', if pos + 1 = 3 then r.pc NativeRustcX64.Sphincs.SphincsVerify.b150Offset else r.pc NativeRustcX64.Sphincs.SphincsVerify.b119Offset⟩) :
    Eventually (step1 Host.exe) R ⟨m, r.pc NativeRustcX64.Sphincs.SphincsVerify.b149Offset⟩ := by
  have hwf := r.frame_wf hpre hK.1.2.2.2 (fun _ ↦ 0) 0
  have hm := match_frameS hpre hK.1 hK.2.1 (ret := 0) (k := []) trivial
  refine blk r hp b149_in_code (List.cons_ne_nil _ _) run_b149 hwf (fun _ h ↦ nomatch h) hm
    fun st hm' hpc ↦ ?_
  have hK' := Keep.of_block hpre hx hE hK hm' hwf (by decide +kernel) rfl
  have hcell := frame_copy16 hm' (o := 184) (o' := 4096) (by decide) (by decide +kernel)
    (by decide +kernel) (bs := A.take 16) (by simp; omega) (take_of_bytesAt hA 16)
  have hsi : Run.RegIs st.data .rsi (BitVec.ofNat 64 (pos + 1)) := by
    unfold Run.RegIs reg
    rw [hm'.regs .rsi _ rfl, load_word h64]
    rfl
  refine pc_at ?_ (cont _ hK' ⟨hsi, regIs_reg hm' rfl h12, regIs_reg hm' rfl hset,
    (hm'.regs .r14 _ rfl).trans hcopy⟩ hcell)
  rw [pc_cond hpc, labelAt r hp b119_in_code rfl]
  have h64' : (r.env m).load 0 64 8 = (pos + 1).toUInt64.toBitVec :=
    load_word (vars := fun _ ↦ 0) (ret := 0) h64
  sym_simp
  rw [h64']
  obtain rfl | rfl | rfl : pos = 0 ∨ pos = 1 ∨ pos = 2 := by omega
  all_goals rfl

/-- **`b148`**: the padded block XORed into hasher A's zero state, `keccak_f`; then `b149`. -/
theorem seg_b148 (hp : Placed Sphincs.SphincsVerify.code r.k) (hc : Callees) (hpre : r.Pre)
    {l : Nat} {x E : List UInt8} (hx : x.length = 64) (hE : E.length ≤ 1024) {i pos : Nat}
    (hpos : pos ≤ 2) {T : List UInt8} (hT : T.length = 64) {R : MachineState → Prop}
    {m : MachineData} (hK : Keep r l x E i m) (h12 : Run.RegIs m .r12 (r.off 4096))
    (hbx : Run.RegIs m .rbx (BitVec.ofNat 64 64)) (h64 : r.WordAt m 64 (pos + 1).toUInt64)
    (hA0 : BytesAt m.dmem (r.off 4096) (List.replicate 200 0))
    (hblk : BytesAt m.dmem (r.off 2048) (T ++ List.replicate 72 0))
    (hcopy : Run.RegIs m .r15 (Labels.label "memcpy").toBitVec)
    (hset : Run.RegIs m .r14 (Labels.label "memset").toBitVec)
    (cont : StepCont r l x E i pos T R) :
    Eventually (step1 Host.exe) R ⟨m, r.pc NativeRustcX64.Sphincs.SphincsVerify.b148Offset⟩ := by
  have hwf := r.frame_wf hpre hK.1.2.2.2 (fun _ ↦ 0) (r.pc NativeRustcX64.Sphincs.SphincsVerify.b149Offset).toBitVec
  have hm := match_frameS hpre hK.1 hK.2.1 (ret := (r.pc NativeRustcX64.Sphincs.SphincsVerify.b149Offset).toBitVec)
    (k := [(.rbx, .lit 64), (.r12, .ptr 0 4096), (.r14, .label "memset")])
    ⟨known_lit hbx, known_ptr h12, hset, trivial⟩
  refine blk r hp b148_in_code (List.cons_ne_nil _ _) run_b148 hwf (fun _ _ ↦ rfl) hm
    fun st hm' hpc ↦ ?_
  have hK1 := KeepC.of_block hpre hx hE hK hm' hwf (by decide +kernel) rfl
  have hxor := xorFinal hm' hwf (r := 0) (b := r.base) (sz := frameRegion) rfl (oA := 4096)
    (oK := 2048) (by decide) (by decide +kernel) hT (by decide) hblk
  have hz : bytesOf m.dmem (r.off 4096) 200 = List.replicate 200 0 := by
    have := bytesOf_of_bytesAt hA0
    rwa [List.length_replicate] at this
  have hxor' : BytesAt st.data.dmem (r.off 4096)
      (Keccak.xorBlock (List.replicate 200 0) (Keccak.finalBlock T)) := by
    rw [← hz]
    exact hxor
  have h0 : Run.RegIs st.data .rdi (r.off 4096) := regIs_ptr hm' rfl
  have h12' : Run.RegIs st.data .r12 (r.off 4096) := regIs_ptr hm' rfl
  have h64' := r.bytesAt_kept hpre hm' hwf (by simp [NativeRustc.length_wordBytes]) h64
    (by rw [NativeRustc.length_wordBytes]; decide +kernel)
  refine call_then hpc hc.2.2.2.2 (r.keccakF_pre hpre hK1.1 h0 (by decide))
    fun st2 hpc2 hrsp2 hpost ↦ ?_
  obtain ⟨hk2, hout, hS⟩ := r.keccakF_out h0 hpost
  have hK2 := Keep.of_call hpre hx hE hK1 hS hrsp2 (a := 4096) (n := 200)
    (by unfold Scratch; omega) (by decide) hout
  have hlen : (Keccak.xorBlock (List.replicate 200 0) (Keccak.finalBlock T)).length = 200 :=
    Keccak.length_stateBytes _
  rw [← hlen, bytesOf_of_bytesAt hxor'] at hk2
  exact pc_at (a := r.pc NativeRustcX64.Sphincs.SphincsVerify.b149Offset) (by rw [hpc2]; rfl)
    (seg_b149 hp hpre hx hE hpos (by rw [Keccak.keccakF, Keccak.length_stateBytes]; decide) hK2
      (RegIs.of_saved hS rfl h12')
      (r.bytesAt_of_call hpre hK1.1 (a := 4096) (n := 200) (by decide) (by decide) hout
        (by simp [NativeRustc.length_wordBytes]) (by simp [NativeRustc.length_wordBytes]) h64')
      hk2 (RegIs.of_saved hS rfl (regIs_reg hm' rfl hcopy))
      (RegIs.of_saved hS rfl (regIs_label (y := .rbx) hm' rfl)) cont)

end

end NativeRustcX64.SphincsVerifyProof.Chains
