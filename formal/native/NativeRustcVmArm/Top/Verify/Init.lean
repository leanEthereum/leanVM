module

public import NativeRustcVmArm.Top.Verify.Basic
public import NativeRustcVm.Transcript.Update

/-!
# `verify`: `TState::new`

`b1`, run from `SA` (after `seed`) with the frame (region 0) and the `Decoded` (region 1), writes
`TState::new`'s fields around the seed's lanes: no waiting scalar, no ground challenge, the
`Decoded`'s three words, cursor, phase and root count zero (`initWords`). The `TState` in the frame
then represents the model's first state `start` (`tstateAt_start`), the decoded area untouched.
-/

namespace NativeRustcVmArm.Top.Verify

open NativeRustcArm NativeRustcArm.Sym NativeRustcVmArm.Vm.Verify NativeVm.Model
open NativeRustcVm.Transcript
open NativeRustcVm (WordAt WordsAt Region wordsOf wordOf)

public section

/-- A word `b1` writes: its bytes `initWords` gives, at its offset in the frame. -/
theorem wordAt_b1 [Labels] {env : Env} {st : MachineData} (hm : Match env (after b1 initS) st)
    {F : BitVec 64} (hb : env.regions[0]? = some (F, 832)) {o : Nat} {v : Sym}
    (hp : (o, v) ∈ initWords) {w : UInt64} (hv : v.eval env = w.toBitVec) :
    WordAt st.dmem (F + BitVec.ofNat 64 o) w := by
  have hw := b1_words _ hp
  have hle : o + 8 ≤ 832 := by
    simp only [initWords, List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hp
    rcases hp with h | h | h | h | h | h | h | h <;> rw [h.1] <;> decide
  unfold WordAt
  rw [wordBytes_byteOf, ← hv]
  exact hm.bytesAt_write hb hle hw

/-- The `TState`'s byte `j` is the frame's byte `8 + j`. -/
theorem off_tOf (m0 : MachineData) (j : Nat) :
    off (tOf m0) j = frameOf m0 + BitVec.ofNat 64 (8 + j) :=
  NativeRustcVm.addr_add_add _ _ _

/-- **The first state**: after `b1`, the `TState` in the frame represents `start`, given the
seed's lanes there, the `Decoded`'s words at region 1, the decoded area and the frame's footprint. -/
theorem tstateAt_start [Labels] {env : Env} {st : MachineData} {m0 : MachineData}
    (hm : Match env (after b1 initS) st) (hb0 : env.regions[0]? = some (frameOf m0, 832))
    {a : DecArea} {stream : Array EW} {openings : Array (Array OpeningW)}
    {bcw : List UInt64} {P : Vector UInt64 4}
    (hseed : WordsAt st.dmem (tOf m0) (seed bcw.toArray P).toList)
    (hdec0 : env.load 1 0 8 = a.words) (hdec1 : env.load 1 8 8 = a.len.toUInt64.toBitVec)
    (hdec2 : env.load 1 16 8 = a.l.toUInt64.toBitVec)
    (hD : DecodedAt st.dmem a stream openings) (hf : Footprint st.dmem (tOf m0) a) :
    TStateAt st.dmem (tOf m0) a (start bcw P stream openings) := by
  have w0 : ∀ o, (o, Sym.lit 0) ∈ initWords → WordAt st.dmem (off (tOf m0) (o - 8)) 0 := by
    intro o ho
    have h8 : 8 ≤ o := by
      simp only [initWords, List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at ho
      omega
    rw [off_tOf, show 8 + (o - 8) = o by omega]
    exact wordAt_b1 hm hb0 ho rfl
  refine ⟨hf, ⟨hseed, Nat.zero_le _, ?_, fun i h ↦ absurd h (Nat.not_lt_zero _), ?_⟩,
    ⟨?_, ?_, ?_⟩, hD, Nat.zero_le _, ?_, Nat.zero_le _, ?_, Nat.zero_le _, ?_,
    fun i h ↦ absurd h (Nat.not_lt_zero _)⟩
  · exact w0 304 (by simp [initWords])
  · exact w0 312 (by simp [initWords])
  · rw [off_tOf]
    exact wordAt_b1 hm hb0 (o := 8 + 328) (v := .load 1 0 8) (w := UInt64.ofBitVec a.words)
      (by simp [initWords]) hdec0
  · rw [off_off, off_tOf]
    exact wordAt_b1 hm hb0 (o := 8 + (328 + 8)) (v := .load 1 8 8) (by simp [initWords]) hdec1
  · rw [off_off, off_tOf]
    exact wordAt_b1 hm hb0 (o := 8 + (328 + 16)) (v := .load 1 16 8) (by simp [initWords]) hdec2
  · exact w0 360 (by simp [initWords])
  · exact w0 368 (by simp [initWords])
  · exact w0 760 (by simp [initWords])

end

end NativeRustcVmArm.Top.Verify
