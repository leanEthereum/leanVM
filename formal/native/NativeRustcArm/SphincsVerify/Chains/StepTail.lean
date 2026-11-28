module

public import NativeRustcArm.SphincsVerify.Chains.StepBase
public import NativeRustcArm.SphincsVerify.InlineTh.Final

/-!
# A chain's step, its end: the final absorb and the new value

From the padded block's bytes at `24720` and the zero state of hasher A (`16400`): `b140` XORs
the padded block into the state and calls `keccak_f` (`seg_b140`), `b141` copies the first 16 bytes
to the chain's value at `15984` and goes back to the step's head `b116` or on to `b142`
(`seg_b141`).
-/

namespace NativeRustcArm.SphincsVerifyProof.Chains

open NativeRustc NativeRustc.Sphincs NativeRustcArm.Sym NativeRustcArm.Sphincs.SphincsVerify
open NativeRustcArm.SphincsVerifyProof.InlineTh

@[expose] public section

/-- The registers a step keeps: X19 the position, X20 the chain's word `i << 24`, X28 the chain. -/
def Regs (m : MachineData) (pos i : Nat) : Prop :=
  Run.RegIs m .X19 (BitVec.ofNat 64 pos) ∧ Run.RegIs m .X20 (BitVec.ofNat 64 (i * 16777216)) ∧
    Run.RegIs m .X28 (BitVec.ofNat 64 i)

theorem Regs.of_block [Labels] {r : Run} {m m' : MachineData} {S : SState}
    (hm : Match (r.env m) S m') (h19 : S.reg .X19 = some (.reg .X19))
    (h20 : S.reg .X20 = some (.reg .X20)) (h28 : S.reg .X28 = some (.reg .X28)) {pos i : Nat}
    (h : Regs m pos i) : Regs m' pos i :=
  ⟨regIs_reg hm h19 h.1, regIs_reg hm h20 h.2.1, regIs_reg hm h28 h.2.2⟩

theorem Regs.of_saved {m m' : MachineData} (hS : Saved m m') {pos i : Nat} (h : Regs m pos i) :
    Regs m' pos i :=
  ⟨RegIs.of_saved hS rfl h.1, RegIs.of_saved hS rfl h.2.1, RegIs.of_saved hS rfl h.2.2⟩

/-- A conditional exit's pc. -/
theorem pc_cond [Labels] {env : Env} {c : SBool} {l : Label} {next : Int64} {st : MachineState}
    (h : PcOk env (.cond c l) next st) : st.pc = if c.eval env then Labels.label l else next := h

theorem take_of_bytesAt {d : DataMem} {a : BitVec 64} {bs : List UInt8} (h : BytesAt d a bs)
    (n : Nat) : BytesAt d a (bs.take n) :=
  BytesAt.left (cs := bs.drop n) (by rwa [List.take_append_drop])

variable [NativeRustcArm.Host] {r : Run}

/-- What follows a step that leaves the chain's value `th` of the padded `T`: from the frame's
state after `b141`, at `b116` for the next step or `b142` after position 2. -/
def StepCont (r : Run) (l : Nat) (x E : List UInt8) (pos i : Nat) (T : List UInt8)
    (R : MachineState → Prop) : Prop :=
  ∀ m', Keep r l x E m' → Regs m' (pos + 1) i → Run.RegIs m' .X22 (r.off 21648) →
    BytesAt m'.dmem (r.off 15984)
      ((Keccak.keccakF (Keccak.xorBlock (List.replicate 200 0) (Keccak.finalBlock T))).take 16) →
    Eventually (step1 NativeRustcArm.Host.exe) R ⟨m', if pos + 1 = 3 then r.pc NativeRustcArm.Sphincs.SphincsVerify.b142Offset else r.pc NativeRustcArm.Sphincs.SphincsVerify.b116Offset⟩

/-- **`b141`**: the first 16 bytes of hasher A become the chain's value; on to the next step or,
after position 2, to `b142`. -/
theorem seg_b141 (hp : Placed Sphincs.SphincsVerify.code r.k) (hpre : r.Pre) {l : Nat}
    {x E : List UInt8} (hx : x.length = 64) (hE : E.length ≤ 1024) {pos i : Nat} (hpos : pos ≤ 2)
    {A : List UInt8} (hA16 : 16 ≤ A.length) {R : MachineState → Prop} {m : MachineData}
    (hK : Keep r l x E m) (hR : Regs m (pos + 1) i) (h22 : Run.RegIs m .X22 (r.off 21648))
    (hA : BytesAt m.dmem (r.off 16400) A)
    (cont : ∀ m', Keep r l x E m' → Regs m' (pos + 1) i → Run.RegIs m' .X22 (r.off 21648) →
      BytesAt m'.dmem (r.off 15984) (A.take 16) →
      Eventually (step1 NativeRustcArm.Host.exe) R ⟨m', if pos + 1 = 3 then r.pc NativeRustcArm.Sphincs.SphincsVerify.b142Offset else r.pc NativeRustcArm.Sphincs.SphincsVerify.b116Offset⟩) :
    Eventually (step1 NativeRustcArm.Host.exe) R ⟨m, r.pc NativeRustcArm.Sphincs.SphincsVerify.b141Offset⟩ := by
  have hwf := r.frame_wf hpre hK.1 (fun _ ↦ 0)
  have hm := match_frameS hpre hK (k := []) trivial
  refine blk r hp b141_in_code (List.cons_ne_nil _ _) run_b141 hwf hm fun st hm' hpc ↦ ?_
  have hK' := Keep.of_block hpre hx hE hK hm' hwf (by decide +kernel)
  have hcell := frame_copy16 hm' (o := 15984) (o' := 16400) (by decide) (by decide +kernel)
    (by decide +kernel) (bs := A.take 16) (by simp; omega) (take_of_bytesAt hA 16)
  refine pc_at ?_ (cont _ hK' (Regs.of_block hm' rfl rfl rfl hR) (regIs_reg hm' rfl h22) hcell)
  have h' := pc_cond hpc
  rw [h', labelAt r hp b116_in_code rfl]
  have h19 : (r.env m).regs .X19 = BitVec.ofNat 64 (pos + 1) := hR.1
  sym_simp
  rw [h19]
  obtain rfl | rfl | rfl : pos = 0 ∨ pos = 1 ∨ pos = 2 := by omega
  all_goals rfl

/-- **`b140`**: the padded block XORed into hasher A's zero state, `keccak_f`; then `b141`. -/
theorem seg_b140 (hp : Placed Sphincs.SphincsVerify.code r.k) (hc : Callees) (hpre : r.Pre)
    {l : Nat} {x E : List UInt8} (hx : x.length = 64) (hE : E.length ≤ 1024) {pos i : Nat}
    (hpos : pos ≤ 2) {T : List UInt8} (hT : T.length = 64) {R : MachineState → Prop}
    {m : MachineData} (hK : Keep r l x E m) (hR : Regs m (pos + 1) i)
    (h24 : Run.RegIs m .X24 (BitVec.ofNat 64 64))
    (hA0 : BytesAt m.dmem (r.off 16400) (List.replicate 200 0))
    (hblk : BytesAt m.dmem (r.off 24720) (T ++ List.replicate 72 0))
    (cont : StepCont r l x E pos i T R) :
    Eventually (step1 NativeRustcArm.Host.exe) R ⟨m, r.pc NativeRustcArm.Sphincs.SphincsVerify.b140Offset⟩ := by
  have hwf := r.frame_wf hpre hK.1 (fun _ ↦ 0)
  have hm := match_frameS hpre hK (k := [(.X24, .lit 64)]) ⟨known_lit h24, trivial⟩
  refine blk r hp b140_in_code (List.cons_ne_nil _ _) run_b140 hwf hm fun st hm' hpc ↦ ?_
  have hK1 := Keep.of_block hpre hx hE hK hm' hwf (by decide +kernel)
  have hxor := xorFinal hm' hwf (r := 0) (b := r.base) (sz := 29376) rfl (oA := 16400)
    (oK := 24720) (by decide) (by decide +kernel) hT (by decide) hblk
  have hz : bytesOf m.dmem (r.off 16400) 200 = List.replicate 200 0 := by
    have := bytesOf_of_bytesAt hA0
    rwa [List.length_replicate] at this
  have hxor' : BytesAt st.data.dmem (r.off 16400)
      (Keccak.xorBlock (List.replicate 200 0) (Keccak.finalBlock T)) := by
    rw [← hz]
    exact hxor
  have h0 : Run.RegIs st.data .X0 (r.off 16400) := regIs_ptr hm' rfl
  have hR1 := Regs.of_block hm' rfl rfl rfl hR
  have h22 : Run.RegIs st.data .X22 (r.off 21648) := regIs_ptr hm' rfl
  refine call_then hpc hc.2.2.2.2 (r.keccakF_pre hpre hK1.1 h0 (by decide)) fun st2 hpc2 hpost ↦ ?_
  obtain ⟨hk2, hout, hS⟩ := r.keccakF_out h0 hpost
  have hK2 := Keep.of_call hpre hx hE hK1 hS (a := 16400) (n := 200) (by unfold Scratch; omega)
    (by decide) hout
  have hlen : (Keccak.xorBlock (List.replicate 200 0) (Keccak.finalBlock T)).length = 200 :=
    Keccak.length_stateBytes _
  rw [← hlen, bytesOf_of_bytesAt hxor'] at hk2
  exact pc_at (a := r.pc NativeRustcArm.Sphincs.SphincsVerify.b141Offset) (by rw [hpc2]; rfl)
    (seg_b141 hp hpre hx hE hpos (by rw [Keccak.keccakF, Keccak.length_stateBytes]; decide) hK2
      (Regs.of_saved hS hR1) (RegIs.of_saved hS rfl h22) hk2 cont)

end

end NativeRustcArm.SphincsVerifyProof.Chains
