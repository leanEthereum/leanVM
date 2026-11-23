module

public import NativeRustcVmX64.Wire.WriteOpenings.Basic

/-!
# `write_openings`' writes and reads (x86-64)

What survives a write into the phase from byte `o` on (`Geo.done_keep`, `Geo.opening_keep`) or
apart from the phase (`Geo.done_keepW`, `Geo.begun_keepW`, `Geo.leaf_keepW`); the first position
of a query (`pos_some`, `pos_none`); a leaf copied word by word (`leaf_succ`). What a block
stores (`stored`, a register's word; `copied`, a word loaded from another region); what it loads
from the argument words (`arg_load`) and from an input region (`in_load`). The executor's
arithmetic (`add_eval`, `and124`, `and3`, …).
-/

namespace NativeRustcVmX64.Wire.WriteOpenings

open NativeRustcX64 hiding InRange SameOutside
open NativeRustcX64.Sym NativeRustcVm.Wire NativeVm.Wire
open NativeRustcVm (WordAt WordsAt wordOf InRange SameOutside)

public section

variable {R : Run}

/-! ## The phase's words -/

/-- The frame's bytes are apart from the phase. -/
theorem Geo.frame_out (G : Geo R) :
    ∀ p, InRange R.out phaseBytes p → ¬InRange R.fb 160 p := by
  intro p hp hq
  refine G.not_in (i := 0) (j := 7) (by omega) (by omega) (by omega) (a := R.fb) (n := 160)
    ⟨le_refl _, by show _ ≤ R.fb.toNat + 168; omega⟩ hq hp

/-- Words of the phase from byte `a` survive a write of the frame and the phase's `n` bytes from
`o`, apart. -/
theorem Geo.wordsAt_keep (G : Geo R) {d d' : Mem 64} {o n : Nat}
    (hs : SameOutside d d' (R.FO o n)) (hon : o + n ≤ phaseBytes) {a : Nat}
    {ws : List UInt64} (h : WordsAt d (R.oa a) ws) (ha : a + 8 * ws.length ≤ phaseBytes)
    (hd : a + 8 * ws.length ≤ o ∨ o + n ≤ a) : WordsAt d' (R.oa a) ws :=
  NativeRustcVm.BytesAt.of_sameOutside h hs fun i hi ↦ by
    rw [NativeRustcVm.length_wordsBytes] at hi
    rw [NativeRustcVm.addr_add_add]
    rintro (hq | hq)
    · exact G.frame_out _ (NativeRustcVm.inRange_add (by omega) (by
        have := G.outNw; unfold NativeRustcVm.NoWrap at this; omega)) hq
    · exact NativeRustcVm.not_inRange_sub G.outNw hon (by omega) (by omega) hq

theorem Geo.wordAt_keep (G : Geo R) {d d' : Mem 64} {o n : Nat}
    (hs : SameOutside d d' (R.FO o n)) (hon : o + n ≤ phaseBytes) {a : Nat}
    {w : UInt64} (h : WordAt d (R.oa a) w) (ha : a + 8 ≤ phaseBytes)
    (hd : a + 8 ≤ o ∨ o + n ≤ a) : WordAt d' (R.oa a) w := by
  rw [← NativeRustcVm.wordsAt_singleton_iff] at h ⊢
  exact G.wordsAt_keep hs hon h (by simpa using ha) (by simpa using hd)

theorem phaseBytes_val : phaseBytes = 395288 := by
  unfold phaseBytes NativeVm.phaseWords NativeVm.openingWords
  simp only [LeanVM.Protocol.Compile.wireMaxQueries, LeanVM.Protocol.Compile.wireMaxLeafWords,
    LeanVM.Protocol.Compile.wireMaxHeight]

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
    (hs : SameOutside d d' (R.FO o n)) (hon : o + n ≤ phaseBytes) {j : Nat}
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
    (hs : SameOutside d d' (R.FO o n)) (hon : o + n ≤ phaseBytes) {j : Nat}
    (hj : j ≤ R.nq) (h : R.Done d j) (ho : ob j ≤ o) : R.Done d' j := by
  obtain ⟨⟨h0, h8, h16⟩, hop⟩ := h
  have e : ob j = 24 + 1544 * j := rfl
  refine ⟨⟨G.wordAt_keep hs hon h0 (by decide) (by omega),
    G.wordAt_keep hs hon h8 (by decide) (by omega),
    G.wordAt_keep hs hon h16 (by decide) (by omega)⟩, fun j' hj' ↦ ?_⟩
  exact G.opening_keep hs hon (by omega) (hop j' hj') (.inl (by unfold ob at *; omega))

/-- **Opening `j` begun survives** a write from its leaf on. -/
theorem Geo.begun_keep (G : Geo R) {d d' : Mem 64} {o n : Nat}
    (hs : SameOutside d d' (R.FO o n)) (hon : o + n ≤ phaseBytes) {j : Nat}
    (hj : j < R.nq) (h : R.Begun j d) (ho : ob j + 8 ≤ o) : R.Begun j d' :=
  ⟨G.done_keep hs hon (by omega) h.1 (by omega),
    G.wordAt_keep hs hon h.2 (by have := ob_le (j := j) (by have := G.nq256; omega); omega)
      (.inl ho)⟩

/-- Opening `j`'s leaf words survive a write past them. -/
theorem Geo.leaf_keep (G : Geo R) {d d' : Mem 64} {o n : Nat}
    (hs : SameOutside d d' (R.FO o n)) (hon : o + n ≤ phaseBytes) {j i t : Nat}
    (hj : j < R.nq) (h : R.LeafPart d j i t) (ho : ob j + 8 + 8 * t ≤ o) :
    R.LeafPart d' j i t := by
  have hob := ob_le (j := j) (by have := G.nq256; omega)
  exact G.wordsAt_keep hs hon h (by simp; omega) (.inl (by simp; omega))

/-- Opening `j`'s path survives a write past it. -/
theorem Geo.path_keep (G : Geo R) {d d' : Mem 64} {o n : Nat}
    (hs : SameOutside d d' (R.FO o n)) (hon : o + n ≤ phaseBytes) {j L : Nat}
    (hj : j < R.nq) (h : R.PathPart d j L) (ho : ob j + 520 + 32 * L ≤ o) :
    R.PathPart d' j L := by
  have hob := ob_le (j := j) (by have := G.nq256; omega)
  exact G.wordsAt_keep hs hon h (by rw [path_length]; omega) (.inl (by rw [path_length]; omega))

/-- Words of the phase survive a write apart from the phase. -/
theorem Geo.wordsAt_keepW (G : Geo R) {d d' : Mem 64} {W : BitVec 64 → Prop}
    (hs : SameOutside d d' W) (hW : ∀ p, InRange R.out phaseBytes p → ¬W p) {a : Nat}
    {ws : List UInt64} (h : WordsAt d (R.oa a) ws) (ha : a + 8 * ws.length ≤ phaseBytes) :
    WordsAt d' (R.oa a) ws :=
  NativeRustcVm.BytesAt.of_sameOutside h hs fun i hi ↦ by
    rw [NativeRustcVm.length_wordsBytes] at hi
    rw [NativeRustcVm.addr_add_add]
    exact hW _ (NativeRustcVm.inRange_add (by omega) (by
      have := G.outNw; unfold NativeRustcVm.NoWrap at this; omega))

theorem Geo.wordAt_keepW (G : Geo R) {d d' : Mem 64} {W : BitVec 64 → Prop}
    (hs : SameOutside d d' W) (hW : ∀ p, InRange R.out phaseBytes p → ¬W p) {a : Nat}
    {w : UInt64} (h : WordAt d (R.oa a) w) (ha : a + 8 ≤ phaseBytes) : WordAt d' (R.oa a) w := by
  rw [← NativeRustcVm.wordsAt_singleton_iff] at h ⊢
  exact G.wordsAt_keepW hs hW h (by simpa using ha)

theorem Geo.done_keepW (G : Geo R) {d d' : Mem 64} {W : BitVec 64 → Prop}
    (hs : SameOutside d d' W) (hW : ∀ p, InRange R.out phaseBytes p → ¬W p) {j : Nat}
    (hj : j ≤ R.nq) (h : R.Done d j) : R.Done d' j := by
  obtain ⟨⟨h0, h8, h16⟩, hop⟩ := h
  have hlw := G.lw64
  have hh := G.h32
  refine ⟨⟨G.wordAt_keepW hs hW h0 (by decide), G.wordAt_keepW hs hW h8 (by decide),
    G.wordAt_keepW hs hW h16 (by decide)⟩, fun j' hj' ↦ ?_⟩
  obtain ⟨i, hi, hq, hl, hp⟩ := hop j' hj'
  have hob := ob_le (j := j') (by have := G.nq256; omega)
  refine ⟨i, hi, G.wordAt_keepW hs hW hq (by omega), G.wordsAt_keepW hs hW hl (by simp; omega),
    G.wordsAt_keepW hs hW hp (by rw [path_length]; omega)⟩

theorem Geo.begun_keepW (G : Geo R) {d d' : Mem 64} {W : BitVec 64 → Prop}
    (hs : SameOutside d d' W) (hW : ∀ p, InRange R.out phaseBytes p → ¬W p) {j : Nat}
    (hj : j < R.nq) (h : R.Begun j d) : R.Begun j d' :=
  ⟨G.done_keepW hs hW (by omega) h.1,
    G.wordAt_keepW hs hW h.2 (by have := ob_le (j := j) (by have := G.nq256; omega); omega)⟩

theorem Geo.leaf_keepW (G : Geo R) {d d' : Mem 64} {W : BitVec 64 → Prop}
    (hs : SameOutside d d' W) (hW : ∀ p, InRange R.out phaseBytes p → ¬W p) {j i t : Nat}
    (hj : j < R.nq) (ht : t ≤ R.lw) (h : R.LeafPart d j i t) : R.LeafPart d' j i t := by
  have hob := ob_le (j := j) (by have := G.nq256; omega)
  have := G.lw64
  exact G.wordsAt_keepW hs hW h (by simp; omega)

theorem Geo.path_keepW (G : Geo R) {d d' : Mem 64} {W : BitVec 64 → Prop}
    (hs : SameOutside d d' W) (hW : ∀ p, InRange R.out phaseBytes p → ¬W p) {j L : Nat}
    (hj : j < R.nq) (hL : L ≤ 32) (h : R.PathPart d j L) : R.PathPart d' j L := by
  have hob := ob_le (j := j) (by have := G.nq256; omega)
  exact G.wordsAt_keepW hs hW h (by rw [path_length]; omega)

/-! ## Positions, leaves -/

theorem pos_some {q : UInt64} {i : Nat} (hi : i < R.np) (he : R.pw i = q)
    (hm : ∀ i' < i, R.pw i' ≠ q) : R.pos q = some i := by
  unfold Run.pos
  rw [List.findIdx?_eq_some_iff_getElem]
  refine ⟨by simpa using hi, by simp [he], fun i' hi' ↦ ?_⟩
  simp only [List.getElem_map, List.getElem_range, beq_iff_eq]
  exact hm i' hi'

theorem pos_none {q : UInt64} (hm : ∀ i < R.np, R.pw i ≠ q) : R.pos q = none := by
  unfold Run.pos
  rw [List.findIdx?_eq_none_iff]
  intro x hx
  simp only [List.mem_map, List.mem_range] at hx
  obtain ⟨i, hi, rfl⟩ := hx
  exact beq_eq_false_iff_ne.mpr (hm i hi)

/-- No position holds query `j`: a rejection. -/
theorem bad_of_none {j : Nat} (hj : j < R.nq) (hm : ∀ i < R.np, R.pw i ≠ R.qw j) : R.Bad :=
  .inl ⟨j, hj, pos_none hm⟩

/-- One more leaf word copied. -/
theorem leaf_succ {d : Mem 64} {j i t : Nat} (h : R.LeafPart d j i t)
    (hw : WordAt d (R.oa (ob j + 8 + 8 * t)) (R.lfw i t)) : R.LeafPart d j i (t + 1) := by
  unfold Run.LeafPart at *
  rw [List.range_succ, List.map_append, NativeRustcVm.wordsAt_append_iff]
  refine ⟨h, ?_⟩
  rw [List.length_map, List.length_range, NativeRustcVm.addr_add_add]
  simpa [NativeRustcVm.wordsAt_singleton_iff] using hw

theorem leaf_zero {d : Mem 64} {j i : Nat} : R.LeafPart d j i 0 := by
  unfold Run.LeafPart
  simp [NativeRustcVm.WordsAt, NativeRustcVm.BytesAt]

theorem path_zero {d : Mem 64} {j : Nat} : R.PathPart d j 0 := by
  unfold Run.PathPart
  simp [NativeRustcVm.WordsAt, NativeRustcVm.BytesAt]

/-- One more level's digest. -/
theorem path_succ {d : Mem 64} {j l : Nat} (h : R.PathPart d j l)
    (hw : WordsAt d (R.oa (ob j + 520 + 32 * l)) (R.digest l (R.qw j))) :
    R.PathPart d j (l + 1) := by
  unfold Run.PathPart at *
  rw [List.range_succ, List.flatMap_append, NativeRustcVm.wordsAt_append_iff, path_length]
  refine ⟨h, ?_⟩
  rw [NativeRustcVm.addr_add_add, show ob j + 520 + 8 * (4 * l) = ob j + 520 + 32 * l by omega]
  simpa using hw

/-- Words written at the phase's byte `o`, inside the phase. -/
theorem Geo.out_inside (G : Geo R) {o n : Nat} (h : o + n ≤ phaseBytes) (hn : 0 < n) :
    Inside (R.oa o) n (R.big 7) :=
  inside_off (A := R.big 7) G.outNw h hn

/-! ## Stores and loads -/

section
variable [Labels] {env : Env} {S : SState} {m : MachineData}

/-- **A stored value**: where the newest write of `v` covers 8 bytes at `o` of region `r`. -/
theorem stored (hm : Match env S m) {r o sz : Nat} {b : BitVec 64}
    (hb : env.regions[r]? = some (b, sz)) (ho : o + 8 ≤ sz) {v : Sym}
    (hw : ∀ i < 8, findWrite r (o + i) S.mem = some (v, i)) :
    WordAt m.dmem (b + BitVec.ofNat 64 o) (UInt64.ofBitVec (v.eval env)) :=
  NativeRustcVmX64.Transcript.wordAt_write hm hb ho hw

/-- **A copied word**: where the newest write is region `r'`'s 8 bytes at `o'`. -/
theorem copied (hm : Match env S m) {r o sz r' o' : Nat} {b : BitVec 64}
    (hb : env.regions[r]? = some (b, sz)) (ho : o + 8 ≤ sz)
    (hw : ∀ i < 8, findWrite r (o + i) S.mem = some (.load r' o' 8, i)) :
    WordAt m.dmem (b + BitVec.ofNat 64 o) (wordOf env.mem0 (env.base r' + BitVec.ofNat 64 o')) := by
  have h := stored hm hb ho hw
  simp only [Sym.eval, load_eq_wordOf] at h
  exact h

end

/-- **A word of an input region**, in the memory of a state of the run. -/
theorem Geo.in_load (G : Geo R) {m : MachineData} (hc : R.Chg m.dmem) {cs : List (BitVec 64 × Nat)}
    {ret : BitVec 64} {r : Nat} {a : BitVec 64} {n : Nat}
    (hr : ((R.ab, 32) :: cs)[r - 1]? = some (a, n)) (h1 : 1 ≤ r) {o i : Nat} (hi : i < 7)
    (hi0 : i ≠ 0) (hin : Inside (a + BitVec.ofNat 64 o) 8 (R.big i)) :
    (envOf R m cs ret).load r o 8 = (wordOf R.d0 (a + BitVec.ofNat 64 o)).toBitVec := by
  rw [load_eq_wordOf, Env.ofMachine_mem0, G.rd hc hi hi0 (by
    rwa [Env.base_ofMachine _ _ _ _ (b := a) (n := n) (by
      obtain ⟨r', rfl⟩ : ∃ r', r = r' + 1 := ⟨r - 1, by omega⟩
      simpa using hr)])]
  congr 3
  exact Env.base_ofMachine _ _ _ _ (b := a) (n := n) (by
    obtain ⟨r', rfl⟩ : ∃ r', r = r' + 1 := ⟨r - 1, by omega⟩
    simpa using hr)

/-- The argument word `i` is the entry's. -/
theorem stackArg_eq (i : Nat) :
    stackArg R.m0 i = (wordOf R.d0 (R.ab + BitVec.ofNat 64 (8 * i))).toBitVec := by
  unfold stackArg
  rw [show R.ab = rspOf R.m0 + BitVec.ofNat 64 8 from rfl, NativeRustcVm.addr_add_add]

/-- **An argument word loaded** (region 1). -/
theorem Geo.arg_load (G : Geo R) {m : MachineData} (hc : R.Chg m.dmem)
    {cs : List (BitVec 64 × Nat)} {ret : BitVec 64} {i : Nat} (hi : i < 4) :
    (envOf R m cs ret).load 1 (8 * i) 8 = stackArg R.m0 i := by
  rw [stackArg_eq, G.in_load hc (r := 1) (a := R.ab) (n := 32) rfl (le_refl _) (i := 1)
    (by omega) (by omega) (inside_off (A := R.big 1) (G.noWrap (by omega))
      (by show 8 * i + 8 ≤ 32; omega) (by omega))]

/-! ## Arithmetic -/

theorem add_eval (x y : BitVec 64) : BinOp.apply .add .W64 x y = x + y := by
  simp [BinOp.apply]

theorem mul_eval (x y : BitVec 64) : BinOp.apply .mul .W64 x y = x * y := by
  simp [BinOp.apply]

theorem and_self_eval (x : BitVec 64) : BinOp.apply .and .W64 x x = x := by
  simp [BinOp.apply]

theorem eq_eval (x y : BitVec 64) : CmpOp.apply .eq .W64 x y = (x == y) := by
  simp [CmpOp.apply]

theorem ult_eval (x y : BitVec 64) : CmpOp.apply .ult .W64 x y = decide (x.toNat < y.toNat) := by
  simp [CmpOp.apply, BitVec.ult]

theorem ofNat_add (a b : Nat) : BitVec.ofNat 64 a + BitVec.ofNat 64 b = BitVec.ofNat 64 (a + b) :=
  (BitVec.ofNat_add a b).symm

theorem ofNat_mul (a b : Nat) : BitVec.ofNat 64 a * BitVec.ofNat 64 b = BitVec.ofNat 64 (a * b) := by
  apply BitVec.eq_of_toNat_eq
  simp [BitVec.toNat_mul, Nat.mul_mod]

theorem ofNat_sub {a b : Nat} (h : b ≤ a) (ha : a < 2 ^ 64) :
    BitVec.ofNat 64 a - BitVec.ofNat 64 b = BitVec.ofNat 64 (a - b) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt (by omega : b < 2 ^ 64), Nat.mod_eq_of_lt
    (by omega : a - b < 2 ^ 64)]
  omega

theorem addr_add {a : BitVec 64} {x y z : Nat} (h : x + y = z) :
    a + BitVec.ofNat 64 x + BitVec.ofNat 64 y = a + BitVec.ofNat 64 z := by
  rw [NativeRustcVm.addr_add_add, h]

theorem lit_add {a : BitVec 64} {x y z : Nat} (h : x + y = z) :
    BitVec.ofNat 64 y + (a + BitVec.ofNat 64 x) = a + BitVec.ofNat 64 z := by
  rw [BitVec.add_comm, NativeRustcVm.addr_add_add, h]

theorem toNat_ofNat {n : Nat} (h : n < 2 ^ 64) : (BitVec.ofNat 64 n).toNat = n :=
  NativeRustcVm.toNat_ofNat_of_lt h

theorem ofNat_toNat' (x : BitVec 64) : BitVec.ofNat 64 x.toNat = x := by simp

theorem toUInt64_toNat (x : BitVec 64) : x.toNat.toUInt64 = UInt64.ofBitVec x := by
  apply UInt64.toBitVec_inj.mp
  apply BitVec.eq_of_toNat_eq
  show (UInt64.ofNat x.toNat).toBitVec.toNat = x.toNat
  simp

theorem and124 {n : Nat} (h : n < 128) :
    BinOp.apply .and .W32 (BitVec.ofNat 64 n) (BitVec.ofNat 64 124) = BitVec.ofNat 64 (n / 4 * 4) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BinOp.apply, toNat_ext, BitVec.toNat_and, toNat_low, toNat_ofNat (by omega : n < 2 ^ 64),
    toNat_ofNat (by decide : 124 < 2 ^ 64), toNat_ofNat (by omega : n / 4 * 4 < 2 ^ 64)]
  have key : ∀ n < 128, n % 2 ^ 32 &&& 124 % 2 ^ 32 = n / 4 * 4 := by decide
  exact key n h

theorem and3 {n : Nat} (h : n < 128) :
    BinOp.apply .and .W32 (UnOp.apply .trunc .W32 (BitVec.ofNat 64 n)) (BitVec.ofNat 64 3) =
      BitVec.ofNat 64 (n % 4) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BinOp.apply, UnOp.apply, toNat_ext, BitVec.toNat_and, toNat_low,
    toNat_ofNat (by omega : n < 2 ^ 64), toNat_ofNat (by decide : 3 < 2 ^ 64),
    toNat_ofNat (by omega : n % 4 < 2 ^ 64)]
  have key : ∀ n < 128, n % 2 ^ 32 % 2 ^ 32 &&& 3 % 2 ^ 32 = n % 4 := by decide
  exact key n h

theorem and124' {n : Nat} (h : n < 128) :
    BinOp.apply .and .W32 (UnOp.apply .trunc .W32 (BitVec.ofNat 64 n)) (BitVec.ofNat 64 124) =
      BitVec.ofNat 64 (n / 4 * 4) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BinOp.apply, UnOp.apply, toNat_ext, BitVec.toNat_and, toNat_low,
    toNat_ofNat (by omega : n < 2 ^ 64), toNat_ofNat (by decide : 124 < 2 ^ 64),
    toNat_ofNat (by omega : n / 4 * 4 < 2 ^ 64)]
  have key : ∀ n < 128, n % 2 ^ 32 % 2 ^ 32 &&& 124 % 2 ^ 32 = n / 4 * 4 := by decide
  exact key n h

theorem shl3 {x : BitVec 64} (h : x.toNat < 2 ^ 32) :
    BinOp.apply .shl .W64 x (BitVec.ofNat 64 3) = BitVec.ofNat 64 (8 * x.toNat) := by
  have hs : shiftCount .W64 (BitVec.ofNat 64 3) = 3 := by decide
  apply BitVec.eq_of_toNat_eq
  simp only [BinOp.apply, low_W64, ext_W64, hs, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq,
    toNat_ofNat (by omega : 8 * x.toNat < 2 ^ 64)]
  omega

theorem shr_trunc {x : BitVec 64} {l : Nat} (hl : l < 32) :
    BinOp.apply .shr .W64 x (UnOp.apply .trunc .W32 (BitVec.ofNat 64 l)) = x >>> l := by
  have hs : shiftCount .W64 (UnOp.apply .trunc .W32 (BitVec.ofNat 64 l)) = l := by
    simp only [shiftCount, shiftMask, UnOp.apply, toNat_low, toNat_ext,
      toNat_ofNat (by omega : l < 2 ^ 64)]
    have key : ∀ l < 32, l % 2 ^ 32 % 2 ^ 8 &&& 63 = l := by decide
    exact key l hl
  simp only [BinOp.apply, low_W64, ext_W64, hs]
  rfl

end

end NativeRustcVmX64.Wire.WriteOpenings
