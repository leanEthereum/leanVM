module

public import NativeRustcVmX64.KeccakGkr.KeccakOpen.FoldBase

/-! # `keccak_open`: the two row buffers at an inner-loop entry -/

namespace NativeRustcVmX64.KeccakGkr.KeccakOpen

open NativeRustcX64 NativeRustcX64.Sym NativeVm.Model NativeRustcVmX64.Transcript
open NativeRustcVm.Transcript (off off_zero off_off off_add toNat_off Mapped.keeps DecArea)

@[expose] public section

abbrev loadEnv [Labels] (m0 d : MachineData) (j : Nat) (ret : BitVec 64) : Env :=
  Env.ofMachine d [(fbA m0, 8), (off (fbA m0) (112 + 16 * j), 1040)] (fun _ ↦ 0) ret

end

public section

variable [Labels] {a : DecArea} {s : TState} {c : KeccakClaimW} {m0 d : MachineData}

theorem load_wf (h : PreOk a s c m0) (hk : Kept m0.dmem d.dmem) {j : Nat} (hj : j < 64)
    {ret : BitVec 64} : (loadEnv m0 d j ret).WF := by
  have hn := nums h
  have := hn.r1; have := hn.r2
  have hfb := fbA_toNat h
  have hjn := fb_off h (j := 112 + 16 * j) (by omega)
  have hfm := Mapped.keeps (frame_mapped h.st (F := 2208) (by rw [stack_eq]; decide)) hk
  refine Env.wf_of ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, trivial⟩ (List.pairwise_pair.mpr ?_)
  · change NativeRustcVm.Mapped d.dmem (fbA m0) 8
    simpa only [off_zero] using (mapped_off (o := 0) (k := 8) hfm (by decide))
  · change (fbA m0).toNat + 8 ≤ 2 ^ 64
    omega
  · exact mapped_off (o := 112 + 16 * j) hfm (by omega)
  · change (off (fbA m0) (112 + 16 * j)).toNat + 1040 ≤ 2 ^ 64
    omega
  · change (fbA m0).toNat + 8 ≤ (off (fbA m0) (112 + 16 * j)).toNat ∨
      (off (fbA m0) (112 + 16 * j)).toNat + 1040 ≤ (fbA m0).toNat
    omega

omit [Labels] in
theorem load_alias (b : BitVec 64) (s0 j : Nat) :
    (b + 8#64) + BitVec.ofNat 64 (s0 + 16 * j) =
      off b (112 + 16 * j) + BitVec.ofInt 64 ((s0 : Int) - 104) := by
  rw [BitVec.add_assoc]
  change b + (BitVec.ofInt 64 8 + BitVec.ofInt 64 ((s0 + 16 * j : Nat) : Int)) =
    b + BitVec.ofInt 64 ((112 + 16 * j : Nat) : Int) + BitVec.ofInt 64 ((s0 : Int) - 104)
  rw [BitVec.add_assoc, ← BitVec.ofInt_add, ← BitVec.ofInt_add]
  congr 2
  omega

theorem load_match {cx : Cx} (hm : Mid cx m0 8 d) {ib : Reg64} {s0 j : Nat}
    (hib : reg d ib = BitVec.ofNat 64 (s0 + 16 * j)) {ret : BitVec 64} :
    Match (loadEnv m0 d j ret) (loS ib s0) d := by
  refine match_ofMachine ⟨rfl, rfl, trivial⟩ ⟨?_, trivial⟩ trivial trivial ⟨?_, trivial⟩
  · change rspOf d = fbA m0 + BitVec.ofInt 64 8
    exact hm.fr.sp
  · simp only [Sym.eval, BinOp.apply, low_W64, ext_W64, Env.ofMachine_regs]
    change (fbA m0 + 8#64) + reg d ib =
      off (fbA m0) (112 + 16 * j) + BitVec.ofInt 64 ((s0 : Int) - 104)
    rw [hib]
    exact load_alias _ _ _

theorem load_buffer {fa fb : Nat → EW} {j : Nat} (hj : j < 64)
    (ha : ElemsAt d.dmem (off (fbA m0) 112) fa 64)
    (hb : ElemsAt d.dmem (off (fbA m0) 1136) fb 64) {ret : BitVec 64} :
    (loadEnv m0 d j ret).load 1 0 8 = (fa j).c0.toBitVec ∧
    (loadEnv m0 d j ret).load 1 8 8 = (fa j).c1.toBitVec ∧
    (loadEnv m0 d j ret).load 1 1024 8 = (fb j).c0.toBitVec ∧
    (loadEnv m0 d j ret).load 1 1032 8 = (fb j).c1.toBitVec := by
  have ha' := NativeRustcVm.ewAt_iff.mp (ha j hj)
  have hb' := NativeRustcVm.ewAt_iff.mp (hb j hj)
  rw [off_off, off_add] at ha' hb'
  refine ⟨load_of_wordAt ?_, load_of_wordAt ?_, load_of_wordAt ?_, load_of_wordAt ?_⟩
  · change NativeRustcVm.WordAt d.dmem (off (off (fbA m0) (112 + 16 * j)) 0) _
    simpa only [off_zero] using ha'.1
  · change NativeRustcVm.WordAt d.dmem (off (off (fbA m0) (112 + 16 * j)) 8) _
    simpa only [off_off] using ha'.2
  · change NativeRustcVm.WordAt d.dmem (off (off (fbA m0) (112 + 16 * j)) 1024) _
    rw [off_off, show 112 + 16 * j + 1024 = 1136 + 16 * j by omega]
    exact hb'.1
  · change NativeRustcVm.WordAt d.dmem (off (off (fbA m0) (112 + 16 * j)) 1032) _
    rw [off_off, show 112 + 16 * j + 1032 = 1136 + 16 * j + 8 by omega]
    exact hb'.2

end

end NativeRustcVmX64.KeccakGkr.KeccakOpen
