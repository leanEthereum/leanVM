module

public import NativeRustcVmArm.Code.Vm.KeccakF.Names
public import NativeRustcVmArm.Keccak.WordsHash.FullEnd

/-!
# `keccak256_words::<hash_words's closure>`: the whole blocks' loop and the last block's head

`full_loop`: from the head of whole block `b` (`FullLaneAt m0 k b 0 NativeRustcVmArm.Vm.Keccak256WordsOfHashWords.b24Offset`), the machine inevitably
reaches the last block's head (`TailStart`), by induction on the blocks left (`Sym.loop`), each
turn the block's lanes (`full_lanes`) and its end (`fullEnd`). `tail_head`: from `TailStart`, the
last block's head (`tailHead`, `b2`) branches to its first lane, loaded or zero (`TailAt m0 k 0`).
-/

namespace NativeRustcVmArm.WordsHash

open NativeRustcArm NativeRustcArm.Sym NativeRustc NativeRustc.Keccak LeanVM.Semantics
open NativeRustcArm.KeccakF (wordAt_keep)
open Vm.Keccak256WordsOfHashWords

public section

variable [Host]

/-- **The whole blocks' loop.** -/
theorem full_loop (hkf : Spec (label NativeRustcVmArm.Vm.KeccakF.entryLabel) NativeRustcVmArm.KeccakFPre
      NativeRustcVmArm.KeccakFPost) {k : Nat} (hp : Placed code k) {m0 : MachineData}
    (g : Geo m0) (hrc : NativeRustcVmArm.RcAt m0 NativeRustcVmArm.keccak256WordsStack)
    {b : Nat} {st : MachineState} (h : FullLaneAt m0 k b 0 NativeRustcVmArm.Vm.Keccak256WordsOfHashWords.b24Offset st) :
    Eventually (step1 Host.exe) (TailStart m0 k) st :=
  Sym.loop (tr := step1 Host.exe) (Q := TailStart m0 k)
    (fun n st => ∃ b, n = nb m0 - b ∧ FullLaneAt m0 k b 0 NativeRustcVmArm.Vm.Keccak256WordsOfHashWords.b24Offset st)
    (fun _ st ⟨b, hn, h⟩ => Eventually.bind (full_lanes hp g h) fun _ h1 =>
      Eventually.mono (fullEnd hkf hp g hrc h1) fun _ h2 => by
        rcases h2 with h2 | h2
        · exact .inr ⟨nb m0 - (b + 1), by have := h.2.2.2.2.1; omega, b + 1, rfl, h2⟩
        · exact .inl h2)
    ⟨b, rfl, h⟩

/-- **The last block's head**: to its first lane, loaded if word `base` is in the slice. -/
theorem tail_head {k : Nat} (hp : Placed code k) {m0 : MachineData} (g : Geo m0)
    {st : MachineState} (h : TailStart m0 k st) :
    Eventually (step1 Host.exe) (TailAt m0 k 0 28 405) st := by
  obtain ⟨hc, hl, hpc⟩ := h
  obtain ⟨m, pc⟩ := st
  simp only at hc hl hpc
  subst hpc
  have hstk := g.stk
  have hb := base_le g
  let env := Env.ofMachine m [(frame m0, 288)]
  have hwf : env.WF :=
    Env.wf_of ⟨⟨frame_mapped hstk hc.kept, frame_noWrap hstk⟩, trivial⟩
      (List.pairwise_singleton _ _)
  have hm : Match env startMain m :=
    match_ofMachine ⟨rfl, fun _ => frame_aligned hstk, trivial⟩
      (by rw [hc.sp]; simp [Sym.eval]) trivial trivial trivial trivial
  refine exec_then (b2_in_code.trans hp.1 (List.cons_ne_nil _ _)) tailHead hwf hm
    fun st hm' hpc => .done _ ⟨?_, ?_, fun h => absurd rfl h, ?_⟩
  · exact ctx_step hstk hc hm' hwf rfl rfl ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, trivial⟩
      (fun w hw => by cases hw)
  · rw [pre_zero]
    exact fun i hi => wordAt_keep (r := 0) (sz := 288) hm' rfl (by omega) rfl (hl i hi)
  · have h4 := m0.regs.X4.toNat_lt
    have e : m0.regs.X4.toBitVec = BitVec.ofNat 64 m0.regs.X4.toNat := by simp
    have hult : (BitVec.ofNat 64 (base m0)).ult (BitVec.ofNat 64 m0.regs.X4.toNat) =
        decide (base m0 + 0 < m0.regs.X4.toNat) := by
      simp only [BitVec.ult, BitVec.toNat_ofNat, Nat.add_zero, decide_eq_decide]
      rw [Nat.mod_eq_of_lt (by unfold base at hb ⊢; omega), Nat.mod_eq_of_lt h4]
    simp only [PcOk, SBool.eval, Sym.eval, CmpOp.apply, Sym.low_W64] at hpc
    rw [hpc]
    show (if (!((m.regs.getXReg .X23).toBitVec).ult (m.regs.getXReg .X22).toBitVec) = true then _
      else _) = _
    rw [hc.x23, hc.x22, e, show 17 * nb m0 = base m0 from rfl, hult]
    by_cases h : base m0 + 0 < m0.regs.X4.toNat
    · simp only [h, decide_true, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
      rfl
    · simp only [h, decide_false, Bool.not_false, ↓reduceIte]
      exact label_at hp b59_in_code rfl

end

end NativeRustcVmArm.WordsHash
