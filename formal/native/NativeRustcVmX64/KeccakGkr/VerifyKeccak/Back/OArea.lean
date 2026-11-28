module

public import NativeRustcVmX64.KeccakGkr.VerifyKeccak.Back.Chg

/-!
# `verify_keccak`: `keccak_open`'s footprint (x86-64)

At both openings (`b40`, `b57`; RSP at the frame's start, the stack arguments from `8`): written
the output's `Option<EW>` in the frame at `O`, the `TState`, the slot point at `232`, the scratch's
`rows`; read the decoded area, the claim's point in the frame at `P` (`n` elements, at most 30),
its bit weights in the scratch at `W`, the round constants, the stack arguments.
-/

namespace NativeRustcVmX64.KeccakGkr.VerifyKeccak.Back

open NativeRustcX64 NativeRustcX64.Sym NativeRustcVmX64.KeccakGkr.SeqZ NativeVm.Model
open LeanVM.Parameters LeanVM.Protocol.Verifier
open NativeRustcVm.Transcript (DecArea TStateAt tstateBytes)
open NativeRustcVm.KeccakGkr (off rowsBytes weightsBytes)
open NativeRustcVm (Region)

public section

theorem ko_le : 3344 - 0 + keccakOpenStack ≤ verifyKeccakStack := by rw [vk_eq]; decide

theorem tsb : tstateBytes = 760 := rfl
theorem rwb : rowsBytes = 65536 := rfl
theorem wtb : weightsBytes = 25600 := rfl

variable [Labels] {m0 mc : MachineData} {a : DecArea} {inst : Array EW} {wr : Nat → Bool}

/-- Two frame ranges apart (any sizes). -/
theorem sepF0 (c : Ctx a inst m0) {o1 n1 o2 n2 : Nat} (h1 : o1 < 3344) (h2 : o2 < 3344)
    (h : o1 + n1 ≤ o2 ∨ o2 + n2 ≤ o1) :
    Sep (off (fb m0) o1).toNat n1 (off (fb m0) o2).toNat n2 := by
  rw [off_fb c (by omega), off_fb c (by omega)]; unfold Sep; omega

/-- A callee's stack and a frame range above its RSP (any size). -/
theorem sepSF0 (c : Ctx a inst m0) {oc : Nat} (ca : CallAt m0 wr oc mc) {N : Nat}
    (hN : 3344 - oc + N ≤ verifyKeccakStack) {o n : Nat} (ho : oc + 8 ≤ o) (ho' : o < 3344) :
    Sep (stackBelow mc N).toNat (N + 8) (off (fb m0) o).toNat n := by
  have hb := ca.sb c hN
  have := ca.oc8
  have := c.sp
  rw [hb, off_fb c (by omega)]
  unfold Sep
  omega

/-- **`keccak_open`'s footprint.** -/
theorem areas_ko (c : Ctx a inst m0) (h : LayZ m0 3344 3368 verifyKeccakStack (rsOf m0))
    (ca : CallAt m0 wr 0 mc) {O P n W : Nat} (hO : 56 ≤ O) (hO' : O + 24 ≤ 3344) (hP : 56 ≤ P)
    (hP' : P + 480 ≤ 3344) (hn : n ≤ 30) (hW : W + 25600 ≤ 140288)
    (hOs : O + 24 ≤ 232 ∨ 328 ≤ O) (hOP : O + 24 ≤ P ∨ P + 480 ≤ O)
    (hsP : 328 ≤ P ∨ P + 480 ≤ 232) :
    Areas mc keccakOpenStack
      [⟨off (fb m0) O, 24⟩, ⟨reg m0 .rdi, tstateBytes⟩,
        ewsRegion (off (fb m0) 232) qkeccakSlotBits, ⟨off (reg m0 .r9) 140288, rowsBytes⟩]
      [a.region, ewsRegion (off (fb m0) P) n, ⟨off (reg m0 .r9) W, weightsBytes⟩, rcRegion,
        argsRegion mc 6] := by
  have hN := ko_le
  have hS := stk_callee c ca hN
  have hwM := NativeRustcVm.Transcript.Mapped.keeps c.wM ca.kept
  have hrcM := NativeRustcVm.Transcript.Mapped.keeps c.rcM ca.kept
  rw [← ob1, ← ob2 140288, ← ob2 W, argsRegion, args_eq ca]
  simp only [ewsRegion, slotBits_eq, tsb, rwb, wtb, DecArea.region, rcRegion]
  refine areas_of ?_ ?_ ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with (rfl | rfl | rfl | rfl) | (rfl | rfl | rfl | rfl | rfl) <;> dsimp only
    · exact mapF h ca (by omega)
    · exact mapR h ca (by decide) (by decide) (by decide)
    · exact mapF h ca (by omega)
    · exact mapR h ca (by decide) (by decide) (by decide)
    · exact hwM
    · exact mapF h ca (by omega)
    · exact mapR h ca (by decide) (by decide) (by simp only [rsz]; omega)
    · exact hrcM
    · exact mapF h ca (by omega)
  · intro r hr
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with (rfl | rfl | rfl | rfl) | (rfl | rfl | rfl | rfl | rfl) <;> dsimp only
    · exact nwF c (by omega)
    · exact nwR c (by decide) (by decide) (by decide)
    · exact nwF c (by omega)
    · exact nwR c (by decide) (by decide) (by decide)
    · exact c.wW
    · exact nwF c (by omega)
    · exact nwR c (by decide) (by decide) (by simp only [rsz]; omega)
    · exact c.rcW
    · exact nwF c (by omega)
  · simp only [List.pairwise_cons, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
      forall_eq, List.Pairwise.nil, and_true, false_implies, implies_true]
    refine ⟨⟨(sepRF c (by decide) (by decide) (by decide) (by decide)
        (stk_frame c (by omega))).symm,
      sepF0 c (by omega) (by omega) (by omega),
      (sepRF c (by decide) (by decide) (by decide) (by decide) (stk_frame c (by omega))).symm⟩,
      ⟨sepRF c (by decide) (by decide) (by decide) (by decide) (stk_frame c (by omega)),
        sepRR c (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
          (by decide) (by decide) (by decide)⟩,
      (sepRF c (by decide) (by decide) (by decide) (by decide) (stk_frame c (by omega))).symm⟩
  · intro w hw
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases hw with rfl | rfl | rfl | rfl <;> dsimp only
    · exact (sepSF0 c ca hN (by omega) (by omega)).symm
    · exact sepRF c (by decide) (by decide) (by decide) (by decide) hS
    · exact (sepSF0 c ca hN (by omega) (by omega)).symm
    · exact sepRF c (by decide) (by decide) (by decide) (by decide) hS
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl <;> dsimp only
    · exact sep_stk hS c.wS
    · exact sepSF0 c ca hN (by omega) (by omega)
    · exact (sepRF c (by decide) (by decide) (by simp only [rsz]; omega) (by decide) hS).symm
    · exact sep_stk hS c.rcS
    · exact sepSF0 c ca hN (by omega) (by omega)
  · intro w hw r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hw hr
    rcases hw with rfl | rfl | rfl | rfl <;> rcases hr with rfl | rfl | rfl | rfl | rfl <;>
      dsimp only
    · exact sepFX c (by omega) c.wS
    · exact sepF0 c (by omega) (by omega) (by omega)
    · exact (sepRF c (by decide) (by decide) (by simp only [rsz]; omega) (by decide)
        (stk_frame c (by omega))).symm
    · exact sepFX c (by omega) c.rcS
    · exact sepF0 c (by omega) (by omega) (by omega)
    · exact sepRX c (by decide) (by decide) (by decide) (by decide) c.tw
    · exact sepRF c (by decide) (by decide) (by decide) (by decide) (stk_frame c (by omega))
    · exact sepRR c (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        (by simp only [rsz]; omega) (by decide) (by decide)
    · exact sepRX c (by decide) (by decide) (by decide) (by decide) c.trc
    · exact sepRF c (by decide) (by decide) (by decide) (by decide) (stk_frame c (by omega))
    · exact sepFX c (by omega) c.wS
    · exact sepF0 c (by omega) (by omega) (by omega)
    · exact (sepRF c (by decide) (by decide) (by simp only [rsz]; omega) (by decide)
        (stk_frame c (by omega))).symm
    · exact sepFX c (by omega) c.rcS
    · exact sepF0 c (by omega) (by omega) (by omega)
    · exact sepRX c (by decide) (by decide) (by decide) (by decide) c.sw
    · exact sepRF c (by decide) (by decide) (by decide) (by decide) (stk_frame c (by omega))
    · exact sepR2 c (by decide) (by decide) (by decide) (by simp only [rsz]; omega) (by decide)
        (by decide) (by omega)
    · exact sepRX c (by decide) (by decide) (by decide) (by decide) c.src
    · exact sepRF c (by decide) (by decide) (by decide) (by decide) (stk_frame c (by omega))

end

end NativeRustcVmX64.KeccakGkr.VerifyKeccak.Back
