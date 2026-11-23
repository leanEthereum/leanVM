module

public import NativeRustcArm.Sym
public import NativeRustcArm.Hasher.Bytes
public import NativeRustcArm.Code.Infix
public import NativeRustcVm.Transcript.Update

/-!
# Glue between the symbolic executor and the transcript's memory

`after ds S`, the state a block run ends in; a placed function's block in the program
(`infix_of`); a word a block stored (`wordAt_write`); a word a block loads (`load_of_wordAt`); the
bytes a block's writes cover, as offsets of its regions (`written_off`, `touch_of_written`).
-/

namespace NativeRustcVmArm.Transcript

open NativeRustcArm NativeRustcArm.Sym NativeRustcVm.Transcript
open LeanVM.Protocol.KeccakHash

@[expose] public section

/-- The state `exec ds S` ends in (`S` where it fails). -/
def after (ds : List Directive) (S : SState) : SState :=
  match exec ds S with
  | some (S', _) => S'
  | none => S

end

public section

theorem after_eq {ds : List Directive} {S S₁ : SState} {x : Exit} (h : exec ds S = some (S₁, x)) :
    after ds S = S₁ := by
  rw [after, h]

theorem exec_after {ds ds' : List Directive} {S S₁ : SState} {x : Exit}
    (h : exec ds S = some (S₁, x)) {r : Option (SState × Exit)} (h' : exec ds' (after ds S) = r) :
    exec ds' S₁ = r := by
  rw [after, h] at h'
  exact h'

/-- A block of a placed function in the program. -/
theorem infix_of [Host] {F b : List Directive} {k j : Nat} (hb : b.IsInfixAt F j) (hne : b ≠ [])
    (hp : Placed F k) : b.IsInfixAt Host.prog (k + j) :=
  List.IsInfixAt.trans hb hp.1 hne

/-- A word's bytes loaded: the word. -/
theorem ofInt_ofBytes_wordBytes (v : UInt64) :
    BitVec.ofInt 64 (Int.ofBytes (wordBytes v)) = v.toBitVec := by
  have := Hasher.ofInt_ofBytes_byteOf v.toBitVec
  rwa [← Hasher.wordBytes_ofBitVec] at this

theorem ofInt_zero64 : BitVec.ofInt 64 0 = 0#64 := rfl

theorem toBitVec_ofBitVec (x : BitVec 64) : (UInt64.ofBitVec x).toBitVec = x := rfl

variable [Labels] {env : Env} {S : SState} {m : MachineData}

/-- Region `i`'s base. -/
theorem eval_ptr {regions : List (BitVec 64 × Nat)} {vars : Nat → BitVec 64} {i n : Nat}
    {b : BitVec 64} (hb : regions[i]? = some (b, n)) :
    (Sym.ptr i 0).eval (Env.ofMachine m regions vars) = b := by
  rw [Sym.eval, Env.base_ofMachine m regions vars hb, ofInt_zero64, BitVec.add_zero]

/-- A register holding region `i`'s base. -/
theorem known_ptr {regions : List (BitVec 64 × Nat)} {vars : Nat → BitVec 64} {i n : Nat}
    {b : BitVec 64} (hb : regions[i]? = some (b, n)) {r : XReg} (h : (m.regs.getXReg r).toBitVec = b) :
    (m.regs.getXReg r).toBitVec = (Sym.ptr i 0).eval (Env.ofMachine m regions vars) := by
  rw [h, Sym.eval, Env.base_ofMachine m regions vars hb, ofInt_zero64, BitVec.add_zero]

omit [Labels] in
/-- **A word loaded** from the environment's memory. -/
theorem load_of_wordAt {r o : Nat} {w : UInt64}
    (h : NativeRustcVm.WordAt env.mem0 (env.base r + BitVec.ofNat 64 o) w) :
    env.load r o 8 = w.toBitVec := by
  rw [Env.load_of_bytesAt (bs := wordBytes w) (n := 8) rfl h]
  exact ofInt_ofBytes_wordBytes w

omit [Labels] in
/-- **A word loaded** from a machine state's region. -/
theorem load_ofMachine {rs : List (BitVec 64 × Nat)} {vs : Nat → BitVec 64} {r n o : Nat}
    {b : BitVec 64} (hb : rs[r]? = some (b, n)) {w : UInt64}
    (h : NativeRustcVm.WordAt m.dmem (off b o) w) :
    (Env.ofMachine m rs vs).load r o 8 = w.toBitVec :=
  load_of_wordAt (by rw [Env.base_ofMachine m rs vs hb]; exact h)

omit [Labels] in
/-- **A tag word's low half loaded**: a tag `0` or `1`. -/
theorem load4_of_tag {r o : Nat} {w : UInt64} (hw : w = 0 ∨ w = 1)
    (h : NativeRustcVm.WordAt env.mem0 (env.base r + BitVec.ofNat 64 o) w) :
    env.load r o 4 = BitVec.ofNat 64 w.toNat := by
  have h4 : NativeRustcVm.BytesAt env.mem0 (env.base r + BitVec.ofNat 64 o) ((wordBytes w).take 4) :=
    fun i hi ↦ by
      have hi' : i < 4 := by simp at hi; omega
      have := h i (by simp [wordBytes]; omega)
      rw [List.getElem_take]
      exact this
  rw [Env.load_of_bytesAt (n := 4) (by simp [wordBytes]) h4]
  rcases hw with rfl | rfl <;> decide

/-- **A word stored** by a block. -/
theorem wordAt_write (hm : Match env S m) {r o : Nat} {b : BitVec 64} {sz : Nat}
    (hb : env.regions[r]? = some (b, sz)) (hle : o + 8 ≤ sz) {v : Sym}
    (hw : ∀ i < 8, findWrite r (o + i) S.mem = some (v, i)) :
    NativeRustcVm.WordAt m.dmem (off b o) (UInt64.ofBitVec (v.eval env)) := by
  have := hm.bytesAt_write hb hle hw
  rwa [← Hasher.wordBytes_ofBitVec] at this

omit [Labels] in
/-- The bytes a block's writes cover: offsets of its writes in their regions. -/
theorem written_off (hwf : env.WF) {q : BitVec 64} (h : Written env S q) :
    ∃ w ∈ S.mem, ∃ b sz, env.regions[w.r]? = some (b, sz) ∧
      ∃ j, w.off ≤ j ∧ j < w.off + w.n ∧ q = off b j := by
  obtain ⟨w, hw, b, sz, hb, h1, h2⟩ := h
  have hnw := hwf.noWrap _ b sz hb
  refine ⟨w, hw, b, sz, hb, q.toNat - b.toNat, by omega, by omega, ?_⟩
  apply BitVec.eq_of_toNat_eq
  rw [toNat_off (by have := q.isLt; omega)]
  omega

omit [Labels] in
/-- The bytes a block's writes cover, all in region `r` between offsets `lo` and `hi`. -/
theorem touch_of_written (hwf : env.WF) {r : Nat} {b : BitVec 64} {N lo hi : Nat}
    (hb : env.regions[r]? = some (b, N)) (hhi : hi ≤ N)
    (hS : ∀ w ∈ S.mem, w.r = r ∧ lo ≤ w.off ∧ w.off + w.n ≤ hi) {q : BitVec 64}
    (h : Written env S q) : Touch b N (fun j ↦ lo ≤ j ∧ j < hi) q := by
  obtain ⟨w, hw, b', sz, hb', j, h1, h2, rfl⟩ := written_off hwf h
  obtain ⟨hr, hlo, hhi'⟩ := hS w hw
  rw [hr, hb] at hb'
  cases hb'
  exact ⟨j, by omega, ⟨by omega, by omega⟩, rfl⟩

omit [Labels] in
/-- An offset of an area is in it. -/
theorem inRange_of_touch {b q : BitVec 64} {N : Nat} {W : Nat → Prop} (hN : b.toNat + N ≤ 2 ^ 64)
    (h : Touch b N W q) : NativeRustcVm.InRange b N q := by
  obtain ⟨j, hj, -, rfl⟩ := h
  exact inRange_off_self hj (by omega)

/-- **A block writing only region `r`** changes no byte outside it. -/
theorem sameOutside_region (hwf : env.WF) (hm : Match env S m) {r : Nat} {b : BitVec 64} {N : Nat}
    (hb : env.regions[r]? = some (b, N)) (hS : ∀ w ∈ S.mem, w.r = r ∧ 0 ≤ w.off ∧ w.off + w.n ≤ N) :
    SameOutside env.mem0 m.dmem (NativeRustcVm.InRange b N) := fun _ hq ↦
  hm.get?_mem0 hwf fun hW ↦ hq (inRange_of_touch (hwf.noWrap r b N hb)
    (touch_of_written hwf hb le_rfl hS hW))

/-- **A block writing only offsets `lo` to `hi` of region `r`.** -/
theorem sameOutside_touch (hwf : env.WF) (hm : Match env S m) {r : Nat} {b : BitVec 64}
    {N lo hi : Nat} (hb : env.regions[r]? = some (b, N)) (hhi : hi ≤ N)
    (hS : ∀ w ∈ S.mem, w.r = r ∧ lo ≤ w.off ∧ w.off + w.n ≤ hi) :
    SameOutside env.mem0 m.dmem (fun q ↦ Touch b N (fun j ↦ lo ≤ j ∧ j < hi) q ∨ False) :=
  fun _ hq ↦ hm.get?_mem0 hwf fun hW ↦ hq (Or.inl (touch_of_written hwf hb hhi hS hW))

omit [Labels] in
/-- The bytes a block's writes cover, all in region `r` at offsets `W`. -/
theorem touch_of_written_W (hwf : env.WF) {r : Nat} {b : BitVec 64} {N : Nat}
    (hb : env.regions[r]? = some (b, N)) {W : Nat → Prop}
    (hS : ∀ w ∈ S.mem, w.r = r ∧ w.off + w.n ≤ N ∧ ∀ j, w.off ≤ j → j < w.off + w.n → W j)
    {q : BitVec 64} (h : Written env S q) : Touch b N W q := by
  obtain ⟨w, hw, b', sz, hb', j, h1, h2, rfl⟩ := written_off hwf h
  obtain ⟨hr, hle, hW⟩ := hS w hw
  rw [hr, hb] at hb'
  cases hb'
  exact ⟨j, by omega, hW j h1 h2, rfl⟩

/-- **A block writing only offsets `W` of region `r`.** -/
theorem sameOutside_W (hwf : env.WF) (hm : Match env S m) {r : Nat} {b : BitVec 64} {N : Nat}
    (hb : env.regions[r]? = some (b, N)) {W : Nat → Prop}
    (hS : ∀ w ∈ S.mem, w.r = r ∧ w.off + w.n ≤ N ∧ ∀ j, w.off ≤ j → j < w.off + w.n → W j) :
    SameOutside env.mem0 m.dmem (fun q ↦ Touch b N W q ∨ False) :=
  fun _ hq ↦ hm.get?_mem0 hwf fun hW ↦ hq (Or.inl (touch_of_written_W hwf hb hS hW))

omit [Labels] in
/-- The bytes a block's writes cover, in region `r` between offsets `lo` and `hi` or in region
`r'`. -/
theorem touch_of_written2 (hwf : env.WF) {r r' : Nat} {b b' : BitVec 64} {N N' lo hi : Nat}
    (hb : env.regions[r]? = some (b, N)) (hb' : env.regions[r']? = some (b', N')) (hhi : hi ≤ N)
    (hS : ∀ w ∈ S.mem, (w.r = r ∧ lo ≤ w.off ∧ w.off + w.n ≤ hi) ∨ (w.r = r' ∧ w.off + w.n ≤ N'))
    {q : BitVec 64} (h : Written env S q) :
    Touch b N (fun j ↦ lo ≤ j ∧ j < hi) q ∨ InRange b' N' q := by
  obtain ⟨w, hw, b₁, sz, hb₁, j, h1, h2, rfl⟩ := written_off hwf h
  rcases hS w hw with ⟨hr, hlo, hhi'⟩ | ⟨hr, hle⟩
  · rw [hr, hb] at hb₁
    cases hb₁
    exact Or.inl ⟨j, by omega, ⟨by omega, by omega⟩, rfl⟩
  · rw [hr, hb'] at hb₁
    cases hb₁
    have := hwf.noWrap r' b' N' hb'
    exact Or.inr (inRange_off_self (by omega) (by omega))

end

end NativeRustcVmArm.Transcript
