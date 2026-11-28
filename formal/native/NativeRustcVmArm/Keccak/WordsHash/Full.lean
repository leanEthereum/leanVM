module

public import NativeRustcVmArm.Keccak.WordsHash.Lane
public import NativeRustcVmArm.Keccak.WordsHash.Call

/-!
# `keccak256_words::<hash_words's closure>`: a whole block's lanes

In whole block `b < nb` (its words region 1, the 136 bytes at `ws + 136 b`, X26 at their byte 64,
X25 its first word's index `17 b`), every word is in the slice, so each lane's branch goes on to
the next lane's loaded block. `FullLaneAt m0 k b j s`: before lane `j` at `s`, the first `j` lanes
XORed. `fullL_step`: one lane, `j < 16`.
-/

namespace NativeRustcVmArm.WordsHash

open NativeRustcArm NativeRustcArm.Sym NativeRustc NativeRustc.Keccak LeanVM.Semantics
open NativeRustcArm.KeccakF (WordAt wordAt_of_eq wordAt_write wordAt_keep load_of_wordAt)
open NativeRustcVm.Keccak NativeRustcVmArm.Keccak

@[expose] public section

/-- Word `17 b + j` is below the bound X22. -/
def cmpF (j : Nat) : SBool := .cmp .ult .W64 (.bin .add .W64 (.reg .X25) (.lit j)) (.reg .X22)

/-- The address of whole block `b`'s words. -/
def blockAddr (m0 : MachineData) (b : Nat) : BitVec 64 :=
  m0.regs.X3.toBitVec + BitVec.ofNat 64 (8 * (17 * b))

/-- **Before lane `j` of whole block `b`**, at `s`. -/
def FullLaneAt [Host] (m0 : MachineData) (k b j s : Nat) (st : MachineState) : Prop :=
  Ctx m0 st.data ∧ Lanes m0 st.data (pre (wordBlocks (word m0) b) (word m0) (17 * b) j) ∧
    (st.data.regs.getXReg .X25).toBitVec = BitVec.ofNat 64 (17 * b) ∧
    (st.data.regs.getXReg .X26).toBitVec = blockAddr m0 b + BitVec.ofInt 64 64 ∧
    b < nb m0 ∧ st.pc = Host.addrOf (k + s)

end

public section

theorem full_in {m0 : MachineData} (g : Geo m0) {b : Nat} (hb : b < nb m0) :
    17 * b + 17 ≤ m0.regs.X4.toNat := by
  have := g.len
  unfold nb at hb
  omega

/-- The branch after a lane of a whole block: always on. -/
theorem cmpF_eval [Labels] {m0 m : MachineData} (g : Geo m0) (hc : Ctx m0 m) {b j : Nat} (hb : b < nb m0)
    (hj : j < 16) (hx25 : (m.regs.getXReg .X25).toBitVec = BitVec.ofNat 64 (17 * b))
    {rs : List (BitVec 64 × Nat)} : (cmpF (j + 1)).eval (Env.ofMachine m rs) = true := by
  have hin := full_in g hb
  have h4 := m0.regs.X4.toNat_lt
  have e : m0.regs.X4.toBitVec = BitVec.ofNat 64 m0.regs.X4.toNat := by simp
  simp only [cmpF, SBool.eval, Sym.eval, CmpOp.apply, Sym.low_W64, add64, Env.ofMachine_regs]
  rw [hx25, hc.x22, e, ult_ofNat (by omega) h4]
  simp
  omega

variable [Host]

/-- **A lane of a whole block.** -/
theorem fullL_step {k : Nat} {m0 m : MachineData} (g : Geo m0) {b j : Nat} (hb : b < nb m0)
    (hj : j < 16) (hc : Ctx m0 m)
    (hl : Lanes m0 m (pre (wordBlocks (word m0) b) (word m0) (17 * b) j))
    (hx25 : (m.regs.getXReg .X25).toBitVec = BitVec.ofNat 64 (17 * b))
    (hx26 : (m.regs.getXReg .X26).toBitVec = blockAddr m0 b + BitVec.ofInt 64 64)
    {blk : List Directive} {s : Nat} {S : SState} {x : Exit}
    (hk : blk.IsInfixAt Host.prog (k + s)) (hx : exec blk startFull = some (S, x))
    (hmem : S.mem = [⟨0, 8 + 8 * j, 8, .bin .eor .W64 (.load 0 (8 + 8 * j) 8) (.load 1 (8 * j) 8)⟩])
    (hsp : S.sp = .ptr 0 0) (hregs : AllOf (fun r => S.reg r = some (.reg r)) ctxRegs)
    (h25 : S.reg .X25 = some (.reg .X25)) (h26 : S.reg .X26 = some (.ptr 1 64))
    {pos : Bool} {lbl : Label}
    (hexit : x = .cond (if pos then cmpF (j + 1) else .not (cmpF (j + 1))) lbl) {sN : Nat}
    (hnext : if pos then Labels.label lbl = Host.addrOf (k + sN) else s + blk.length = sN) :
    Eventually (step1 Host.exe) (FullLaneAt m0 k b (j + 1) sN) ⟨m, Host.addrOf (k + s)⟩ := by
  have hstk := g.stk
  have hin := full_in g hb
  obtain ⟨hat, hreg1, hap1⟩ := slice_region g hc (i0 := 17 * b) (c := 17) hin (by omega)
  let env := Env.ofMachine m [(frame m0, 288), (blockAddr m0 b, 136)]
  have hwf : env.WF :=
    Env.wf_of ⟨⟨frame_mapped hstk hc.kept, frame_noWrap hstk⟩, hreg1, trivial⟩
      (List.pairwise_pair.mpr hap1)
  have hm : Match env startFull m :=
    match_ofMachine ⟨rfl, fun _ => frame_aligned hstk, rfl, fun h => absurd h (by decide),
      trivial⟩ (by rw [hc.sp]; simp [Sym.eval]) ⟨hx26, trivial⟩ trivial trivial trivial
  refine exec_then hk hx hwf hm fun st hm' hpc => .done _ ⟨?_, ?_, ?_, ?_, hb, ?_⟩
  · refine ctx_step hstk hc hm' hwf rfl hsp hregs fun w hw => ?_
    rw [hmem, List.mem_singleton] at hw
    subst hw
    exact ⟨rfl, by simp; omega⟩
  · have hw : env.load 1 (8 * j) 8 = (word m0 (17 * b + j)).toBitVec :=
      load_word (r := 1) rfl (by omega) fun t ht => slice_same g hc (by omega)
    have := lanes_step (j := j) hm' rfl (by omega) hmem hl
      (x := Keccak.lane (wordBlocks (word m0) b) j ^^^ word m0 (17 * b + j))
      (by
        show BinOp.apply .eor .W64 (env.load 0 (8 + 8 * j) 8) (env.load 1 (8 * j) 8) = _
        rw [eor64, load_of_wordAt (r := 0) (hl j (by omega)), hw]
        simp [pre])
    rwa [pre_succ _ _ _ _ rfl] at this
  · exact (hm'.regs .X25 _ h25).trans hx25
  · exact (hm'.regs .X26 _ h26).trans rfl
  · have hev := cmpF_eval (j := j) g hc hb hj hx25 (rs := [(frame m0, 288), (blockAddr m0 b, 136)])
    rw [hexit] at hpc
    simp only [PcOk] at hpc
    rw [hpc]
    cases pos
    · simp only [Bool.false_eq_true, ↓reduceIte, SBool.eval] at hnext ⊢
      rw [hev, Nat.add_assoc, hnext]
      rfl
    · simp only [↓reduceIte] at hnext ⊢
      rw [hev]
      exact hnext

end

end NativeRustcVmArm.WordsHash
