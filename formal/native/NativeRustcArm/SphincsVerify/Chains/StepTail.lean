module

public import NativeRustcArm.SphincsVerify.Chains.StepBase
public import NativeRustcArm.SphincsVerify.InlineTh.Final

/-!
# A chain's step, its end: the final absorb and the new value

From the padded block's bytes at `16960` and the zero state of hasher A (`8640`): `b131` XORs
the padded block into the state and calls `keccak_f` (`seg_b131`), `b132` copies the first 16 bytes
to the chain's value at `8224` and goes back to the step's head `b107` or on to `b133`
(`seg_b132`).
-/

namespace NativeRustcArm.SphincsVerifyProof.Chains

open NativeRustc NativeRustc.Sphincs NativeRustcArm.Sym NativeRustcArm.Sphincs.SphincsVerify
open NativeRustcArm.SphincsVerifyProof.InlineTh

@[expose] public section

/-- The registers and chain-index spill a step keeps: X20 the position, X26 the chain's word
`i << 24`, spill `416` the chain index `i`. -/
def Regs (r : Run) (m : MachineData) (pos i : Nat) : Prop :=
  Run.RegIs m .X20 (BitVec.ofNat 64 pos) ∧ Run.RegIs m .X26 (BitVec.ofNat 64 (i * 16777216)) ∧
    r.WordAt m 416 i.toUInt64

theorem Regs.of_block [Labels] {r : Run} (hpre : r.Pre) {m m' : MachineData} {S : SState}
    (hm : Match (r.env m) S m') (hwf : (r.env m).WF) (h20 : S.reg .X20 = some (.reg .X20))
    (h26 : S.reg .X26 = some (.reg .X26)) (hn : Run.noWriteIn S 416 8 = true) {pos i : Nat}
    (h : Regs r m pos i) : Regs r m' pos i :=
  ⟨regIs_reg hm h20 h.1, regIs_reg hm h26 h.2.1,
    r.bytesAt_kept hpre hm hwf (by rw [NativeRustc.length_wordBytes]; decide) h.2.2
      (by rw [NativeRustc.length_wordBytes]; exact hn)⟩

theorem Regs.of_call [Labels] {r : Run} (hpre : r.Pre) {m m' : MachineData} (hF : r.Frame m)
    (hS : Saved m m') {a n N : Nat} (ha : Scratch a n) (hN : N ≤ finalizeStack)
    (hout : SameOutside m.dmem m'.dmem (r.CallOut m a n N)) {pos i : Nat}
    (h : Regs r m pos i) : Regs r m' pos i :=
  ⟨RegIs.of_saved hS rfl h.1, RegIs.of_saved hS rfl h.2.1,
    r.bytesAt_of_call hpre hF (by unfold Scratch at ha; omega) hN hout
      (by rw [NativeRustc.length_wordBytes]; decide)
      (by rw [NativeRustc.length_wordBytes]; unfold Scratch at ha; omega) h.2.2⟩

/-- A conditional exit's pc. -/
theorem pc_cond [Labels] {env : Env} {c : SBool} {l : Label} {next : Int64} {st : MachineState}
    (h : PcOk env (.cond c l) next st) : st.pc = if c.eval env then Labels.label l else next := h

theorem take_of_bytesAt {d : DataMem} {a : BitVec 64} {bs : List UInt8} (h : BytesAt d a bs)
    (n : Nat) : BytesAt d a (bs.take n) :=
  BytesAt.left (cs := bs.drop n) (by rwa [List.take_append_drop])

variable [ElfHost] {r : Run}

/-- What follows a step that leaves the chain's value `th` of the padded `T`: from the frame's
state after `b132`, at `b107` for the next step or `b133` after position 2. -/
def StepCont (r : Run) (l : Nat) (x E : List UInt8) (pos i : Nat) (T : List UInt8)
    (R : MachineState → Prop) : Prop :=
  ∀ m', Keep r l x E m' → Regs r m' (pos + 1) i →
    BytesAt m'.dmem (r.off 8224)
      ((Keccak.keccakF (Keccak.xorBlock (List.replicate 200 0) (Keccak.finalBlock T))).take 16) →
    Eventually (elfStep1 ElfHost.exe) R ⟨m', if pos + 1 = 3 then r.pc NativeRustcArm.Sphincs.SphincsVerify.b133Offset else r.pc NativeRustcArm.Sphincs.SphincsVerify.b107Offset⟩

/-- **`b132`**: the first 16 bytes of hasher A become the chain's value; on to the next step or,
after position 2, to `b133`. -/
theorem seg_b132 (hp : PlacedIn Sphincs.SphincsVerify.code r.sec r.k) (hpre : r.Pre) {l : Nat}
    {x E : List UInt8} (hx : x.length = 64) (hE : E.length ≤ 1024) {pos i : Nat} (hpos : pos ≤ 2)
    {A : List UInt8} (hA16 : 16 ≤ A.length) {R : MachineState → Prop} {m : MachineData}
    (hK : Keep r l x E m) (hR : Regs r m (pos + 1) i)
    (hA : BytesAt m.dmem (r.off 8640) A)
    (cont : ∀ m', Keep r l x E m' → Regs r m' (pos + 1) i →
      BytesAt m'.dmem (r.off 8224) (A.take 16) →
      Eventually (elfStep1 ElfHost.exe) R ⟨m', if pos + 1 = 3 then r.pc NativeRustcArm.Sphincs.SphincsVerify.b133Offset else r.pc NativeRustcArm.Sphincs.SphincsVerify.b107Offset⟩) :
    Eventually (elfStep1 ElfHost.exe) R ⟨m, r.pc NativeRustcArm.Sphincs.SphincsVerify.b132Offset⟩ := by
  have hwf := r.frame_wf hpre hK.1 (fun _ ↦ 0)
  have hm := match_frameS hpre hK (k := []) trivial
  refine blk r hp b132_in_code (List.cons_ne_nil _ _) run_b132 hwf hm fun st hm' hpc ↦ ?_
  have hK' := Keep.of_block hpre hx hE hK hm' hwf (by decide +kernel)
  have hcell := frame_copy16 hm' (o := 8224) (o' := 8640) (by decide) (by decide +kernel)
    (by decide +kernel) (bs := A.take 16) (by simp; omega) (take_of_bytesAt hA 16)
  refine pc_at ?_ (cont _ hK' (Regs.of_block hpre hm' hwf rfl rfl (by decide +kernel) hR) hcell)
  have h' := pc_cond hpc
  rw [h', labelAt r hp b107_in_code rfl]
  have h20 : (r.env m).regs .X20 = BitVec.ofNat 64 (pos + 1) := hR.1
  sym_simp
  rw [h20]
  obtain rfl | rfl | rfl : pos = 0 ∨ pos = 1 ∨ pos = 2 := by omega
  all_goals rfl

/-- **`b131`**: the padded block XORed into hasher A's zero state, `keccak_f`; then `b132`. -/
theorem seg_b131 (hp : PlacedIn Sphincs.SphincsVerify.code r.sec r.k) (hc : Callees) (hpre : r.Pre)
    {l : Nat} {x E : List UInt8} (hx : x.length = 64) (hE : E.length ≤ 1024) {pos i : Nat}
    (hpos : pos ≤ 2) {T : List UInt8} (hT : T.length = 64) {R : MachineState → Prop}
    {m : MachineData} (hK : Keep r l x E m) (hR : Regs r m (pos + 1) i)
    (h24 : Run.RegIs m .X24 (BitVec.ofNat 64 64))
    (hA0 : BytesAt m.dmem (r.off 8640) (List.replicate 200 0))
    (hblk : BytesAt m.dmem (r.off 16960) (T ++ List.replicate 72 0))
    (cont : StepCont r l x E pos i T R) :
    Eventually (elfStep1 ElfHost.exe) R ⟨m, r.pc NativeRustcArm.Sphincs.SphincsVerify.b131Offset⟩ := by
  have hwf := r.frame_wf hpre hK.1 (fun _ ↦ 0)
  have hm := match_frameS hpre hK (k := [(.X24, .lit 64)]) ⟨known_lit h24, trivial⟩
  refine blk r hp b131_in_code (List.cons_ne_nil _ _) run_b131 hwf hm fun st hm' hpc ↦ ?_
  have hK1 := Keep.of_block hpre hx hE hK hm' hwf (by decide +kernel)
  have hxor := xorFinal hm' hwf (r := 0) (b := r.base) (sz := 21616) rfl (oA := 8640)
    (oK := 16960) (by decide) (by decide +kernel) hT (by decide) hblk
  have hz : bytesOf m.dmem (r.off 8640) 200 = List.replicate 200 0 := by
    have := bytesOf_of_bytesAt hA0
    rwa [List.length_replicate] at this
  have hxor' : BytesAt st.data.dmem (r.off 8640)
      (Keccak.xorBlock (List.replicate 200 0) (Keccak.finalBlock T)) := by
    rw [← hz]
    exact hxor
  have h0 : Run.RegIs st.data .X0 (r.off 8640) := regIs_ptr hm' rfl
  have hR1 := Regs.of_block hpre hm' hwf rfl rfl (by decide +kernel) hR
  refine call_then_elf hpc hc.2.2.2.2 (r.keccakF_pre hpre hK1.1 h0 (by decide)) fun st2 hpc2 hpost ↦ ?_
  obtain ⟨hk2, hout, hS⟩ := r.keccakF_out h0 hpost
  have hK2 := Keep.of_call hpre hx hE hK1 hS (a := 8640) (n := 200) (by unfold Scratch; omega)
    (by decide) hout
  have hlen : (Keccak.xorBlock (List.replicate 200 0) (Keccak.finalBlock T)).length = 200 :=
    Keccak.length_stateBytes _
  rw [← hlen, bytesOf_of_bytesAt hxor'] at hk2
  exact pc_at (a := r.pc NativeRustcArm.Sphincs.SphincsVerify.b132Offset) (by rw [hpc2]; rfl)
    (seg_b132 hp hpre hx hE hpos (by rw [Keccak.keccakF, Keccak.length_stateBytes]; decide) hK2
      (Regs.of_call hpre hK1.1 hS (a := 8640) (n := 200) (by unfold Scratch; omega) (by decide) hout hR1)
      hk2 cont)

end

end NativeRustcArm.SphincsVerifyProof.Chains
