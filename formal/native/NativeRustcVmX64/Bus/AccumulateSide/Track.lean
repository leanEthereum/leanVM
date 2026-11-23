module

public import NativeRustcVmX64.Transcript.Frame

/-!
# Tracking values through straight-line code (x86-64)

The x86-64 twin of `NativeRustcVmArm.Ring.Track`. A state description `D : List (Sym × Nat)`:
each location `s` (a register, a word of a region, a literal) holds the value `V n` of a table
`V : Nat → UInt64` (`Holds rs V D m`, the locations evaluated in the environment of `m` with the
regions `rs`). After a block from `m` (a `Match` in that environment), a location's content is a
symbolic value of the block's start (`content`, by the literal result); where that is a location
`D` describes with index `n`, the location holds `V n` (`trackOk`, `Holds.after`).
-/

namespace NativeRustcVmX64.Bus.AccumulateSide

open NativeRustcX64 NativeRustcX64.Sym

@[expose] public section

/-- A location's content after a block, as a symbolic value of the block's start: a register's,
a literal, a word of region `r` (of size `sz.getD r 0`) no write touched or one write stored. -/
def content (sz : List Nat) (S : SState) : Sym → Option Sym
  | .reg r => S.reg r
  | .lit c => some (.lit c)
  | .load r off 8 =>
    if off + 8 ≤ sz.getD r 0 then
      if (List.range 8).all (fun i ↦ findWrite r (off + i) S.mem == none) then some (.load r off 8)
      else match findWrite r off S.mem with
        | some (v, _) =>
          if (List.range 8).all (fun i ↦ findWrite r (off + i) S.mem == some (v, i)) then some v
          else none
        | none => none
    else none
  | _ => none

/-- Every location of `D'` holds, after the block, a location `D` describes with its index. -/
def trackOk (sz : List Nat) (S : SState) (D D' : List (Sym × Nat)) : Bool :=
  D'.all fun p ↦ match content sz S p.1 with
    | some c => D.contains (c, p.2)
    | none => false

/-- A location: a register, a literal, a word of a region. -/
def isLoc : Sym → Bool
  | .reg _ => true
  | .lit _ => true
  | .load _ _ 8 => true
  | _ => false

/-- A location of region `0` or a register or a literal. -/
def loc0 : Sym → Bool
  | .reg _ => true
  | .lit _ => true
  | .load 0 _ 8 => true
  | _ => false

/-- A location kept: a register `rk` says kept, a literal, a frame word below `top` outside
`[lo, hi)`. -/
def keepLoc (rk : Reg64 → Bool) (lo hi top : Nat) : Sym → Bool
  | .reg r => rk r
  | .lit _ => true
  | .load 0 o 8 => decide (o + 8 ≤ lo ∨ hi ≤ o ∧ o + 8 ≤ top)
  | _ => false

section
variable [Labels]

/-- A location's value in `m`, the regions `rs`. -/
def tval (rs : List (BitVec 64 × Nat)) (m : MachineData) (s : Sym) : UInt64 :=
  UInt64.ofBitVec (s.eval (Env.ofMachine m rs))

/-- **The description holds**: each location of `D` holds its value. -/
def Holds (rs : List (BitVec 64 × Nat)) (V : Nat → UInt64) (D : List (Sym × Nat))
    (m : MachineData) : Prop :=
  ∀ p ∈ D, tval rs m p.1 = V p.2

end

end

public section

theorem getD_sz {rs : List (BitVec 64 × Nat)} {sz : List Nat} (hsz : rs.map Prod.snd = sz)
    {r n : Nat} (h : n ≤ sz.getD r 0) (hn : 0 < n) :
    ∃ b, rs[r]? = some (b, sz.getD r 0) := by
  subst hsz
  rw [List.getD_eq_getElem?_getD, List.getElem?_map] at h ⊢
  cases hr : rs[r]? with
  | none => rw [hr] at h; simp at h; omega
  | some e => exact ⟨e.1, by simp⟩

section
variable [Labels] {rs : List (BitVec 64 × Nat)} {sz : List Nat} {V : Nat → UInt64}
  {D D' : List (Sym × Nat)}

theorem Holds.mono {m : MachineData} (h : Holds rs V D m) (hs : ∀ p ∈ D', p ∈ D) :
    Holds rs V D' m := fun p hp ↦ h p (hs p hp)

theorem Holds.append {m : MachineData} (h : Holds rs V D m) (h' : Holds rs V D' m) :
    Holds rs V (D ++ D') m := fun p hp ↦ (List.mem_append.mp hp).elim (h p) (h' p)

theorem holds_nil (rs : List (BitVec 64 × Nat)) (V : Nat → UInt64) (m : MachineData) :
    Holds rs V [] m := fun _ h ↦ by cases h

theorem holds_cons {m : MachineData} {s : Sym} {i : Nat} (h : tval rs m s = V i)
    (h' : Holds rs V D m) : Holds rs V ((s, i) :: D) m := fun p hp ↦ by
  rcases List.mem_cons.mp hp with rfl | hp
  · exact h
  · exact h' p hp

theorem Holds.congrV {V' : Nat → UInt64} {m : MachineData} (h : Holds rs V D m)
    (hV : ∀ p ∈ D, V p.2 = V' p.2) : Holds rs V' D m := fun p hp ↦ (h p hp).trans (hV p hp)

/-- A location evaluates alike whatever the variables and the return address. -/
theorem eval_loc {m : MachineData} {vs : Nat → BitVec 64} {ret : BitVec 64} {s : Sym}
    (h : isLoc s = true) : s.eval (Env.ofMachine m rs vs ret) = s.eval (Env.ofMachine m rs) := by
  match s, h with
  | .reg _, _ => rfl
  | .lit _, _ => rfl
  | .load _ _ 8, _ => rfl

/-- **A location's value after a block** is its content's at the block's start. -/
theorem content_eval (hsz : rs.map Prod.snd = sz) {m m' : MachineData} {vs : Nat → BitVec 64}
    {ret : BitVec 64} {S : SState} (hm : Match (Env.ofMachine m rs vs ret) S m') {s c : Sym}
    (h : content sz S s = some c) :
    tval rs m' s = UInt64.ofBitVec (c.eval (Env.ofMachine m rs vs ret)) := by
  unfold tval
  congr 1
  match s, h with
  | .reg r, h => exact hm.regs r c h
  | .lit _, h => simp only [content, Option.some.injEq] at h; subst h; rfl
  | .load r off 8, h =>
    simp only [content] at h
    split at h
    case isFalse => cases h
    case isTrue hle =>
    obtain ⟨b, hb⟩ := getD_sz hsz hle (by omega)
    have hbm : (Env.ofMachine m rs vs ret).regions[r]? = some (b, sz.getD r 0) := hb
    have hbm' : (Env.ofMachine m' rs).base r = b := Env.base_ofMachine m' rs _ _ hb
    split at h
    case isTrue hall =>
      simp only [Option.some.injEq] at h
      subst h
      simp only [List.all_eq_true, List.mem_range, beq_iff_eq] at hall
      simp only [Sym.eval, Env.load]
      rw [hbm', Env.base_ofMachine m rs vs ret hb]
      congr 2
      apply List.map_congr_left
      intro i hi
      rw [List.mem_range] at hi
      rw [show (Env.ofMachine m' rs).mem0 = m'.dmem from rfl,
        hm.mem r b _ hbm (off + i) (by omega)]
      unfold memByte
      rw [hall i hi]
    case isFalse =>
      split at h
      case h_2 => cases h
      case h_1 v t _ =>
      split at h
      case isFalse => cases h
      case isTrue hall =>
      simp only [Option.some.injEq] at h
      subst h
      simp only [List.all_eq_true, List.mem_range, beq_iff_eq] at hall
      simp only [Sym.eval, Env.load]
      rw [hbm']
      have hbytes : ((List.range 8).map fun i ↦
          ((Env.ofMachine m' rs).mem0.get? (b + BitVec.ofNat 64 (off + i))).getD 0) =
          (List.range 8).map fun i ↦ byteOf (v.eval (Env.ofMachine m rs vs ret)) (0 + i) := by
        apply List.map_congr_left
        intro i hi
        rw [List.mem_range] at hi
        rw [show (Env.ofMachine m' rs).mem0 = m'.dmem from rfl,
          hm.mem r b _ hbm (off + i) (by omega)]
        unfold memByte
        rw [hall i hi, Nat.zero_add]
        rfl
      rw [hbytes, ofBytes_byteOf, BitVec.ofInt_natCast]
      apply BitVec.eq_of_toNat_eq
      simp only [Nat.mul_zero, Nat.pow_zero, Nat.div_one, BitVec.toNat_ofNat]
      have := (v.eval (Env.ofMachine m rs vs ret)).isLt
      omega

/-- **The description after a block.** -/
theorem Holds.after (hsz : rs.map Prod.snd = sz) {m m' : MachineData} {vs : Nat → BitVec 64}
    {ret : BitVec 64} {S : SState} (h : Holds rs V D m) (hD : D.all (fun p ↦ isLoc p.1) = true)
    (hm : Match (Env.ofMachine m rs vs ret) S m') (ht : trackOk sz S D D' = true) :
    Holds rs V D' m' := by
  intro p hp
  simp only [trackOk, List.all_eq_true] at ht
  have := ht p hp
  split at this
  case h_2 => cases this
  case h_1 c hc =>
  have hmem := List.contains_iff_mem.mp this
  rw [content_eval hsz hm hc, eval_loc (List.all_eq_true.mp hD _ hmem)]
  exact h (c, p.2) hmem

/-- **A description over another list of regions** with the same region `0`. -/
theorem Holds.reg0 {rs' : List (BitVec 64 × Nat)} {m : MachineData} (h : Holds rs V D m)
    (hD : D.all (fun p ↦ loc0 p.1) = true) (h0 : (rs[0]?).map (·.1) = (rs'[0]?).map (·.1)) :
    Holds rs' V D m := by
  intro p hp
  rw [← h p hp]
  have hl := List.all_eq_true.mp hD p hp
  unfold tval
  congr 1
  match hs : p.1, hl with
  | .reg r, _ => rfl
  | .lit _, _ => rfl
  | .load 0 o 8, _ =>
    simp only [Sym.eval, Env.load, Env.base_ofMachine_eq, h0]
    rfl

/-- **A description kept** where its registers and its frame words are. -/
theorem Holds.keep {b : BitVec 64} {n : Nat} {m m' : MachineData} {rk : Reg64 → Bool}
    {lo hi top : Nat}
    (h : Holds [(b, n)] V D m) (hD : D.all (fun p ↦ keepLoc rk lo hi top p.1) = true)
    (hr : ∀ r, rk r = true → m'.regs.get64 r = m.regs.get64 r)
    (hw : ∀ j, (j < lo ∨ hi ≤ j ∧ j < top) → m'.dmem.get? (b + BitVec.ofNat 64 j) =
      m.dmem.get? (b + BitVec.ofNat 64 j)) : Holds [(b, n)] V D m' := by
  intro p hp
  rw [← h p hp]
  have hk := List.all_eq_true.mp hD p hp
  unfold tval
  congr 1
  match hs : p.1, hk with
  | .reg r, hk =>
    show m'.regs.get64 r = m.regs.get64 r
    exact hr r hk
  | .lit _, _ => rfl
  | .load 0 o 8, hk =>
    simp only [keepLoc, decide_eq_true_eq] at hk
    simp only [Sym.eval, Env.load]
    congr 2
    apply List.map_congr_left
    intro j hj
    rw [List.mem_range] at hj
    show (m'.dmem.get? (b + BitVec.ofNat 64 (o + j))).getD 0 =
      (m.dmem.get? (b + BitVec.ofNat 64 (o + j))).getD 0
    rw [hw (o + j) (by omega)]

/-- A register's value from a description. -/
theorem Holds.reg {m : MachineData} (h : Holds rs V D m) {r : Reg64} {i : Nat}
    (hp : (Sym.reg r, i) ∈ D) : m.regs.get64 r = (V i).toBitVec := by
  have := h _ hp
  simp only [tval, Sym.eval, Env.ofMachine_regs] at this
  rw [← this]

/-- A region's word from a description. -/
theorem Holds.load {m : MachineData} (h : Holds rs V D m) {r o i : Nat}
    (hp : (Sym.load r o 8, i) ∈ D) : (Env.ofMachine m rs).load r o 8 = (V i).toBitVec := by
  have := h _ hp
  simp only [tval, Sym.eval] at this
  rw [← this]

end

end

end NativeRustcVmX64.Bus.AccumulateSide
