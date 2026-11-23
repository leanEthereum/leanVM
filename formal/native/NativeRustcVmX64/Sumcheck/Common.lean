module

public import NativeRustcVmX64.Transcript.Frame

/-!
# Helpers of the sumcheck area's proofs (x86-64)

Four words a block wrote (`WordsW`, `wordsAt_written`); bytes of the frame a block did not write
(`keep_frame`); a block's writes in a frame environment with one more region (`written_frame2`);
the `bool` a callee returns in AL, tested by `test %al, %al` (`eval_testAl`).
-/

namespace NativeRustcVmX64.Sumcheck

open NativeRustcX64 NativeRustcX64.Sym NativeRustcVm.Transcript NativeRustcVmX64.Transcript

@[expose] public section

/-- Four words of region `r` at `o`, each word `i` the symbolic value `v i`. -/
def WordsW (r o : Nat) (v : Nat → Sym) (S : SState) : Prop :=
  ∀ i < 4, ∀ t < 8, findWrite r (o + 8 * i + t) S.mem = some (v i, t)

instance (r o : Nat) (v : Nat → Sym) (S : SState) : Decidable (WordsW r o v S) := by
  unfold WordsW; infer_instance

/-- A word of region `r` at `o` written as `v`. -/
def WordW (r o : Nat) (v : Sym) (S : SState) : Prop :=
  ∀ t < 8, findWrite r (o + t) S.mem = some (v, t)

instance (r o : Nat) (v : Sym) (S : SState) : Decidable (WordW r o v S) := by
  unfold WordW; infer_instance

end

public section

theorem writesIn_of_mid {F o : Nat} {sl : Slots} {S : SState} (h : MidOk F o sl S = true) :
    writesIn S = true := by
  simp only [MidOk, Bool.and_eq_true] at h
  exact h.1.1.2

theorem belowRet_of_mid {F o : Nat} {sl : Slots} {S : SState} (h : MidOk F o sl S = true) :
    belowRet F S = true := by
  simp only [MidOk, Bool.and_eq_true] at h
  exact h.1.1.1.2

theorem belowRet_of_pro {F o : Nat} {sl : Slots} {S : SState} (h : ProOk F o sl S = true) :
    belowRet F S = true := by
  simp only [ProOk, Bool.and_eq_true] at h
  exact h.1.1.2

theorem writesIn_of_pro {F o : Nat} {sl : Slots} {S : SState} (h : ProOk F o sl S = true) :
    writesIn S = true := by
  simp only [ProOk, Bool.and_eq_true] at h
  exact h.1.2

variable [Labels] {m0 : MachineData}

/-- Bytes of the frame a block does not write are kept. -/
theorem keep_frame {F : Nat} {rest : List (BitVec 64 × Nat)} {vars : Nat → BitVec 64}
    {ret : BitVec 64} {S : SState} {d d' : MachineData}
    (hwf : (frameEnv m0 d F rest vars ret).WF) (hm : Match (frameEnv m0 d F rest vars ret) S d')
    (hin : writesIn S = true) {o : Nat} {bs : List UInt8} (hle : o + bs.length ≤ F + 8)
    (hmiss : ∀ w ∈ S.mem, w.r = 0 → w.off + w.n ≤ o ∨ o + bs.length ≤ w.off)
    (h : NativeRustcVm.BytesAt d.dmem (off (stackBelow m0 F) o) bs) :
    NativeRustcVm.BytesAt d'.dmem (off (stackBelow m0 F) o) bs := by
  intro i hi
  rw [off_add]
  rw [hm.get?_mem0 hwf (not_written0 hwf hm hin (by omega) fun w hw hr ↦ by
    rcases hmiss w hw hr with h' | h'
    · exact Or.inl (by omega)
    · exact Or.inr (by omega))]
  have := h i hi
  rwa [off_add] at this

/-- A word of the frame a block does not write is kept. -/
theorem keepW {F : Nat} {rest : List (BitVec 64 × Nat)} {vars : Nat → BitVec 64}
    {ret : BitVec 64} {S : SState} {d d' : MachineData}
    (hwf : (frameEnv m0 d F rest vars ret).WF) (hm : Match (frameEnv m0 d F rest vars ret) S d')
    (hin : writesIn S = true) {o : Nat} {w : UInt64} (hle : o + 8 ≤ F + 8)
    (hmiss : ∀ w ∈ S.mem, w.r = 0 → w.off + w.n ≤ o ∨ o + 8 ≤ w.off)
    (h : NativeRustcVm.WordAt d.dmem (off (stackBelow m0 F) o) w) :
    NativeRustcVm.WordAt d'.dmem (off (stackBelow m0 F) o) w :=
  keep_frame hwf hm hin (bs := NativeRustcVm.wordBytes w) hle hmiss h

/-- A word written by a block. -/
theorem wordAt_written {env : Env} {S : SState} {d : MachineData} (hm : Match env S d)
    {r o : Nat} {b : BitVec 64} {sz : Nat} (hb : env.regions[r]? = some (b, sz))
    (hle : o + 8 ≤ sz) {v : Sym} (hw : WordW r o v S) {w : UInt64} (hv : v.eval env = w.toBitVec) :
    NativeRustcVm.WordAt d.dmem (off b o) w := by
  have := wordAt_write hm hb hle hw
  rwa [hv] at this

/-- Four words written by a block (`WordsW`): the digest of their values. -/
theorem wordsAt_written {env : Env} {S : SState} {d : MachineData} (hm : Match env S d)
    {r o : Nat} {b : BitVec 64} {sz : Nat} (hb : env.regions[r]? = some (b, sz))
    (hle : o + 32 ≤ sz) {v : Nat → Sym} (hw : WordsW r o v S) {D : LeanVM.Protocol.Digest}
    (hv : ∀ i (hi : i < 4), (v i).eval env = (D.toList[i]'(by simpa using hi)).toBitVec) :
    NativeRustcVm.WordsAt d.dmem (off b o) D.toList := by
  rw [wordsAt_iff]
  intro i hi
  have hi4 : i < 4 := by simpa using hi
  have := wordAt_write hm (o := o + 8 * i) hb (by omega) (hw i hi4)
  rw [hv i hi4] at this
  rwa [off_off]

/-- **A block's writes** in the frame environment with one more region `x`: below the frame's
offset `F`, or in `x`. -/
theorem written_frame2 {F : Nat} {x : BitVec 64} {n : Nat} {vars : Nat → BitVec 64}
    {ret : BitVec 64} {S : SState} {d d' : MachineData}
    (hm : Match (frameEnv m0 d F [(x, n)] vars ret) S d') (hin : writesIn S = true)
    (hbr : belowRet F S = true) (hnw : NativeRustcVm.NoWrap x n)
    (hfnw : NativeRustcVm.NoWrap (stackBelow m0 F) (F + 8)) {q : BitVec 64}
    (h : Written (frameEnv m0 d F [(x, n)] vars ret) S q) :
    NativeRustcVm.InRange (stackBelow m0 F) F q ∨ NativeRustcVm.InRange x n q := by
  obtain ⟨w, hw, b, sz, hb, h1, h2⟩ := h
  unfold writesIn at hin
  rw [List.all_eq_true] at hin
  have hw' := hin w hw
  obtain ⟨sz', hS'⟩ : ∃ sz', S.regions[w.r]? = some sz' := by
    revert hw'
    cases S.regions[w.r]? with
    | none => simp
    | some x => exact fun _ ↦ ⟨x, rfl⟩
  rw [hS'] at hw'
  simp only [decide_eq_true_eq] at hw'
  obtain ⟨b', hb'⟩ := hm.regions _ _ hS'
  rw [hb] at hb'
  cases hb'
  match hr : w.r, hb with
  | 0, hb =>
    cases hb
    have := belowRet_spec hbr w hw hr
    left
    rw [inRange_iff' (hfnw.mono (by omega))]
    omega
  | 1, hb =>
    cases hb
    right
    rw [inRange_iff' hnw]
    omega
  | r + 2, hb => simp at hb

omit [Labels] in
/-- **A block's writes** in the frame environment with one more region `x`: below the frame's
offset `F`, or in the first `hi` bytes of `x`. -/
theorem written_frame_hi {F : Nat} {x : BitVec 64} {n hi : Nat} {vars : Nat → BitVec 64}
    {ret : BitVec 64} {S : SState} {d : MachineData} (hnw : NativeRustcVm.NoWrap x n)
    (hhi : hi ≤ n) (hfnw : NativeRustcVm.NoWrap (stackBelow m0 F) (F + 8))
    (hS : ∀ w ∈ S.mem, (w.r = 0 ∧ w.off + w.n ≤ F) ∨ (w.r = 1 ∧ w.off + w.n ≤ hi))
    {q : BitVec 64} (h : Written (frameEnv m0 d F [(x, n)] vars ret) S q) :
    NativeRustcVm.InRange (stackBelow m0 F) F q ∨ NativeRustcVm.InRange x hi q := by
  obtain ⟨w, hw, b, sz, hb, h1, h2⟩ := h
  rcases hS w hw with ⟨hr, hle⟩ | ⟨hr, hle⟩
  · rw [hr] at hb
    cases hb
    left
    rw [inRange_iff' (hfnw.mono (by omega))]
    omega
  · rw [hr] at hb
    cases hb
    right
    rw [inRange_iff' (hnw.mono hhi)]
    omega

omit [Labels] in
/-- The low byte of a value whose low byte was replaced. -/
theorem low8_merge (x : BitVec 64) (y : BitVec 8) : low .W8 (x.replaceLow y) = y := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  have hi8 : i < 8 := hi
  simp only [low, BitVec.replaceLow, BitVec.getLsbD_setWidth]
  change (decide (i < 8) && (decide (i < 64) && ((x.drop 8) ++ y).getLsbD i)) = _
  rw [BitVec.getLsbD_append]
  simp [hi8, show i < 64 by omega]

omit [Labels] in
/-- `test %al, %al` of a `bool` AL: zero exactly when it is `false`. -/
theorem testAl_eq (x : BitVec 64) :
    (CmpOp.apply .eq .W8 (BinOp.apply .and .W8 x x) (BitVec.ofNat 64 0)) =
      decide (x.toNat % 256 = 0) := by
  simp only [CmpOp.apply, BinOp.apply, low_ext, BitVec.and_self]
  rw [Bool.eq_iff_iff, beq_iff_eq, decide_eq_true_iff, ← BitVec.toNat_inj]
  simp [low, BitVec.toNat_setWidth]

end

end NativeRustcVmX64.Sumcheck
