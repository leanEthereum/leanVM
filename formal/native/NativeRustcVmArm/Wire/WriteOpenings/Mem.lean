module

public import NativeRustcVmArm.Wire.WriteOpenings.Basic

/-!
# `write_openings`' writes

What a block stores (`stored`: a register's word, `copied`: a word loaded from another region),
and what survives a write into the phase from byte `o` on (`Run.wordsAt_keep`, `Done.keep`): the
head and the openings before.
-/

namespace NativeRustcVmArm.Wire.WriteOpenings

open NativeRustcArm NativeRustcArm.Sym NativeRustcVm.Wire NativeVm.Wire
open NativeRustcVmArm.Ring (Fr base)
open NativeRustcVm (WordAt WordsAt wordOf)

public section

section
variable [Labels] {env : Env} {S : SState} {m : MachineData}

/-- **A stored value**: where the newest write of `v` covers 8 bytes at `o` of region `r`. -/
theorem stored (hm : Match env S m) {r o sz : Nat} {b : BitVec 64}
    (hb : env.regions[r]? = some (b, sz)) (ho : o + 8 ≤ sz) {v : Sym}
    (hw : ∀ i < 8, findWrite r (o + i) S.mem = some (v, i)) :
    WordAt m.dmem (b + BitVec.ofNat 64 o) (UInt64.ofBitVec (v.eval env)) := by
  have h := hm.bytesAt_write (r := r) (o := o) (n := 8) (b := b) (sz := sz) hb ho hw
  rw [byteOf_range] at h
  exact h

/-- **A copied word**: where the newest write is region `r'`'s 8 bytes at `o'`. -/
theorem copied (hm : Match env S m) {r o sz r' o' : Nat} {b : BitVec 64}
    (hb : env.regions[r]? = some (b, sz)) (ho : o + 8 ≤ sz)
    (hw : ∀ i < 8, findWrite r (o + i) S.mem = some (.load r' o' 8, i)) :
    WordAt m.dmem (b + BitVec.ofNat 64 o) (wordOf env.mem0 (env.base r' + BitVec.ofNat 64 o')) := by
  have h := stored hm hb ho hw
  simp only [Sym.eval, Ring.load_eq_wordOf] at h
  exact h

end

variable {R : Run}

theorem Geo.outNw (G : Geo R) : NativeRustcVm.NoWrap R.out phaseBytes :=
  G.noWrap (i := 7) (by omega)

/-- Words of the phase from byte `a` survive a write of its `n` bytes from `o`, apart. -/
theorem Geo.wordsAt_keep (G : Geo R) {d d' : Mem 64} {o n : Nat}
    (hs : SameOutside d d' (InRange (R.oa o) n)) (hon : o + n ≤ phaseBytes) {a : Nat}
    {ws : List UInt64} (h : WordsAt d (R.oa a) ws) (ha : a + 8 * ws.length ≤ phaseBytes)
    (hd : a + 8 * ws.length ≤ o ∨ o + n ≤ a) : WordsAt d' (R.oa a) ws :=
  NativeRustcVm.BytesAt.of_sameOutside h hs fun i hi ↦ by
    rw [NativeRustcVm.length_wordsBytes] at hi
    rw [NativeRustcVm.addr_add_add]
    exact NativeRustcVm.not_inRange_sub G.outNw hon (by omega) (by omega)

theorem Geo.wordAt_keep (G : Geo R) {d d' : Mem 64} {o n : Nat}
    (hs : SameOutside d d' (InRange (R.oa o) n)) (hon : o + n ≤ phaseBytes) {a : Nat}
    {w : UInt64} (h : WordAt d (R.oa a) w) (ha : a + 8 ≤ phaseBytes)
    (hd : a + 8 ≤ o ∨ o + n ≤ a) : WordAt d' (R.oa a) w := by
  rw [← NativeRustcVm.wordsAt_singleton_iff] at h ⊢
  exact G.wordsAt_keep hs hon h (by simpa using ha) (by simpa using hd)

theorem ob_le {j : Nat} (hj : j < 256) : ob j + 1544 ≤ phaseBytes := by
  unfold ob phaseBytes NativeVm.phaseWords NativeVm.openingWords
  simp only [LeanVM.Protocol.Compile.wireMaxQueries, LeanVM.Protocol.Compile.wireMaxLeafWords,
    LeanVM.Protocol.Compile.wireMaxHeight]
  omega

theorem digest_length (l : Nat) (q : UInt64) : (R.digest l q).length = 4 := by
  unfold Run.digest
  split <;> simp

theorem path_length (q : UInt64) :
    ∀ L, ((List.range L).flatMap fun l ↦ R.digest l q).length = 4 * L
  | 0 => rfl
  | L + 1 => by
    rw [List.range_succ, List.flatMap_append, List.length_append, path_length q L]
    simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, digest_length]
    omega

/-- **An opening survives** a write apart from it. -/
theorem Geo.opening_keep (G : Geo R) {d d' : Mem 64} {o n : Nat}
    (hs : SameOutside d d' (InRange (R.oa o) n)) (hon : o + n ≤ phaseBytes) {j : Nat}
    (hj : j < R.nq) (h : R.Opening d j) (hd : ob j + 1544 ≤ o ∨ o + n ≤ ob j) :
    R.Opening d' j := by
  obtain ⟨i, hi, hq, hl, hp⟩ := h
  have hlw := G.lw64
  have hh := G.h32
  have hob := ob_le (j := j) (by have := G.nq256; omega)
  refine ⟨i, hi, G.wordAt_keep hs hon hq (by omega) (by omega), ?_, ?_⟩
  · exact G.wordsAt_keep hs hon hl (by simp; omega) (by simp; omega)
  · exact G.wordsAt_keep hs hon hp (by rw [path_length]; omega) (by rw [path_length]; omega)

/-- **The head and the first `j` openings survive** a write from opening `j` on. -/
theorem Geo.done_keep (G : Geo R) {d d' : Mem 64} {o n : Nat}
    (hs : SameOutside d d' (InRange (R.oa o) n)) (hon : o + n ≤ phaseBytes) {j : Nat}
    (hj : j ≤ R.nq) (h : R.Done d j) (ho : ob j ≤ o) : R.Done d' j := by
  obtain ⟨⟨h0, h8, h16⟩, hop⟩ := h
  have e : ob j = 24 + 1544 * j := rfl
  refine ⟨⟨G.wordAt_keep hs hon h0 (by decide) (by omega),
    G.wordAt_keep hs hon h8 (by decide) (by omega),
    G.wordAt_keep hs hon h16 (by decide) (by omega)⟩, fun j' hj' ↦ ?_⟩
  exact G.opening_keep hs hon (by omega) (hop j' hj') (.inl (by unfold ob at *; omega))

/-! ## A block's writes -/

/-- Writes in the frame below the slots. -/
theorem writesOk_frame {env : Env} {outs : BitVec 64 → Prop} {ws : List Write}
    (hall : ∀ w ∈ ws, w.r = 0 ∧ w.off + w.n ≤ 80) :
    ∀ w ∈ ws, Ring.WriteOk env 176 slots outs w := fun w hw ↦
  have h := hall w hw
  .inl ⟨h.1, by omega, fun p hp ↦ .inl (by
    have := (show ∀ p ∈ slots, 80 ≤ p.1 by decide) p hp; omega)⟩

/-- Writes in a region of the phase. -/
theorem Geo.writesOk_out (G : Geo R) {env : Env} {ws : List Write} {r : Nat} {b : BitVec 64}
    {sz : Nat} (hr0 : r ≠ 0) (hb : env.regions[r]? = some (b, sz)) (hin : Inside b sz (R.big 7))
    (hall : ∀ w ∈ ws, w.r = r ∧ w.off + w.n ≤ sz) :
    ∀ w ∈ ws, Ring.WriteOk env 176 slots (Outs R) w := fun w hw ↦ by
  obtain ⟨hr, hle⟩ := hall w hw
  subst hr
  refine .inr ⟨hr0, fun b' sz' hb' ↦ ?_⟩
  rw [hb] at hb'
  cases hb'
  refine ⟨hle, fun i hi ↦ hin.inRange G.outNw (NativeRustcVm.inRange_add hi ?_)⟩
  have := hin.noWrap G.outNw
  unfold NativeRustcVm.NoWrap at this
  omega

/-! ## Values -/

theorem memExt0 (x : BitVec 64) : BitVec.ofInt 64 (x.apply_mem_extend ⟨.UXTX, .E0⟩) = x := by
  apply BitVec.eq_of_toNat_eq
  simp [BitVec.apply_mem_extend, BitVec.unsigned]

theorem memExt3 (x : BitVec 64) :
    BitVec.ofInt 64 (x.apply_mem_extend ⟨.UXTX, .E3⟩) = BitVec.ofNat 64 (8 * x.toNat) := by
  simp only [BitVec.apply_mem_extend, BitVec.unsigned, Int.shiftLeft_eq]
  rw [show ((x.toNat : Int) * 2 ^ 3) = ((8 * x.toNat : Nat) : Int) by push_cast; omega,
    BitVec.ofInt_natCast]

theorem ofNat_add (a b : Nat) : BitVec.ofNat 64 a + BitVec.ofNat 64 b = BitVec.ofNat 64 (a + b) :=
  (BitVec.ofNat_add a b).symm

theorem ofNat_sub {a b : Nat} (h : b ≤ a) :
    BitVec.ofNat 64 a - BitVec.ofNat 64 b = BitVec.ofNat 64 (a - b) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]
  have h1 := Nat.mod_lt a (show 0 < 2 ^ 64 by decide)
  by_cases ha : a < 2 ^ 64
  · rw [Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt (by omega : b < 2 ^ 64), Nat.mod_eq_of_lt
      (by omega : a - b < 2 ^ 64)]
    omega
  · omega

theorem ofNat_toNat {n : Nat} (h : n < 2 ^ 64) : (BitVec.ofNat 64 n).toNat = n :=
  NativeRustcVm.toNat_ofNat_of_lt h

theorem and124 {n : Nat} (h : n < 128) :
    BitVec.ofNat 64 n &&& BitVec.ofNat 64 124 = BitVec.ofNat 64 (n / 4 * 4) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_and, ofNat_toNat (by omega), ofNat_toNat (by omega), ofNat_toNat (by omega)]
  have key : ∀ n < 128, n &&& 124 = n / 4 * 4 := by decide
  exact key n h

theorem addr_add {a : BitVec 64} {x y z : Nat} (h : x + y = z) :
    a + BitVec.ofNat 64 x + BitVec.ofNat 64 y = a + BitVec.ofNat 64 z := by
  rw [NativeRustcVm.addr_add_add, h]

theorem addr_sub {a : BitVec 64} {x y z : Nat} (h : z + y = x) :
    a + BitVec.ofNat 64 x - BitVec.ofNat 64 y = a + BitVec.ofNat 64 z := by
  rw [← h, ← NativeRustcVm.addr_add_add, BitVec.add_sub_cancel]

/-- Registers whose symbolic value is unchanged keep their value. -/
theorem regs_keep [Labels] {env : Env} {S S' : SState} {s s' : MachineData} (hm : Match env S s)
    (hm' : Match env S' s') {rs : List XReg}
    (h : ∀ r ∈ rs, S.reg r = some (.reg r) ∧ S'.reg r = some (.reg r)) :
    ∀ r ∈ rs, s'.regs.getXReg r = s.regs.getXReg r := fun r hr ↦
  Match.reg_eq hm hm' (h r hr).1 (h r hr).2

/-- Four words from four. -/
theorem words4 {d : Mem 64} {a : BitVec 64} {w0 w1 w2 w3 : UInt64} (h0 : WordAt d a w0)
    (h1 : WordAt d (a + BitVec.ofNat 64 8) w1) (h2 : WordAt d (a + BitVec.ofNat 64 16) w2)
    (h3 : WordAt d (a + BitVec.ofNat 64 24) w3) : WordsAt d a [w0, w1, w2, w3] := by
  rw [NativeRustcVm.wordsAt_iff]
  intro i hi
  simp only [List.length_cons, List.length_nil] at hi
  rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3) with rfl | rfl | rfl | rfl
  · simpa using h0
  · exact h1
  · exact h2
  · exact h3

/-- An environment's load of a word in chunk `r`. -/
theorem envLoad {m : MachineData} {cs : List (BitVec 64 × Nat)} {r : Nat} {a : BitVec 64}
    {sz : Nat} (h : ((base R.m0 176, 176) :: cs)[r]? = some (a, sz)) (o : Nat) :
    (envOf R m cs).load r o 8 = (wordOf m.dmem (a + BitVec.ofNat 64 o)).toBitVec := by
  rw [Ring.load_eq_wordOf, Env.base_ofMachine _ _ _ h]
  rfl

/-- An environment's load of a frame word. -/
theorem frLoad {m : MachineData} {cs : List (BitVec 64 × Nat)} {o : Nat} {v : UInt64}
    (h : WordAt m.dmem (base R.m0 176 + BitVec.ofNat 64 o) v) :
    (envOf R m cs).load 0 o 8 = v.toBitVec :=
  Ring.load_word h

@[simp] theorem base1 {m : MachineData} {a : BitVec 64} {n : Nat} {cs : List (BitVec 64 × Nat)} :
    (envOf R m ((a, n) :: cs)).base 1 = a := rfl

@[simp] theorem base2 {m : MachineData} {a b : BitVec 64} {n n' : Nat}
    {cs : List (BitVec 64 × Nat)} :
    (envOf R m ((a, n) :: (b, n') :: cs)).base 2 = b := rfl

end

end NativeRustcVmArm.Wire.WriteOpenings
