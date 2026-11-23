module

public import NativeRustcVmArm.Wire.InsD.Exec
public import NativeRustcVmArm.Wire.Common
public import NativeRustcVmArm.Spec.Wire
public import NativeRustcVm.Wire.InsD
public import NativeRustcVm.Wire.WordsFacts

/-!
# `ins_d`'s states

The words `L` (the list `l = L.map toNat`) at `a` (X0), `n = L.length` (X1), `x` (X2). What every
state keeps (`Kp`), the environments of one or two elements (`env1`, `env2`), and the states at
the blocks: the scan's head `b1` (`SInv`), the shift's set-up `b6` (`SixInv`), the shift's head
`b7` (`TInv`), the store `b8` (`EInv`); the result (`Post`, from `post_of`).
-/

namespace NativeRustcVmArm.Wire.InsD

open NativeRustcArm NativeRustcArm.Sym NativeRustcVm.Wire NativeVm.Wire
open NativeRustcVm (WordAt WordsAt)
open NativeRustcVmArm.Vm.InsD

public section

theorem after_eq {ds : List Directive} {S S₁ : SState} {x : Exit} (h : exec ds S = some (S₁, x)) :
    after ds S = S₁ := by
  rw [after, h]

theorem elem_reg (r : XReg) : elem (.reg r) =
    .bin .add .W64 (.reg .X0) (.un (.memExtend ⟨.UXTX, .E3⟩) .W64 (.bin .and .W64 (.reg r) (.lit 255))) :=
  rfl

theorem elem_sub : elem (mkBin .sub .W64 (.reg .X9) (.lit 1)) =
    .bin .add .W64 (.reg .X0) (.un (.memExtend ⟨.UXTX, .E3⟩) .W64
      (.bin .and .W64 (.bin .sub .W64 (.reg .X9) (.lit 1)) (.lit 255))) :=
  rfl

/-- `[x0, y, lsl #3]`'s index. -/
theorem memExt3 (y : BitVec 64) :
    UnOp.apply (.memExtend ⟨.UXTX, .E3⟩) .W64 y = BitVec.ofNat 64 (8 * y.toNat) := by
  simp only [UnOp.apply, BitVec.apply_mem_extend, BitVec.unsigned, Int.shiftLeft_eq]
  rw [show (y.toNat : Int) * 2 ^ 3 = ((8 * y.toNat : Nat) : Int) by push_cast; ring, BitVec.ofInt_natCast]

theorem and255 (y : BitVec 64) : (BinOp.apply .and .W64 y (BitVec.ofNat 64 255)).toNat = y.toNat % 256 := by
  simp only [BinOp.apply, Sym.low_W64, Sym.ext_W64, BitVec.toNat_and, BitVec.toNat_ofNat]
  rw [show (255 : Nat) % 2 ^ 64 = 2 ^ 8 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]

theorem eval_elem [Labels] (env : Env) (y : Sym) :
    (Sym.bin .add .W64 (.reg .X0) (.un (.memExtend ⟨.UXTX, .E3⟩) .W64 (.bin .and .W64 y (.lit 255)))).eval env =
      env.regs .X0 + BitVec.ofNat 64 (8 * ((y.eval env).toNat % 256)) := by
  have h := and255 (y.eval env)
  simp only [Sym.eval, BinOp.apply, Sym.low_W64, Sym.ext_W64] at h ⊢
  rw [memExt3, h]

theorem set_mid {α : Type} (A B : List α) (g w : α) : (A ++ g :: B).set A.length w = A ++ w :: B := by
  induction A with
  | nil => rfl
  | cons a A ih => simp [ih]

/-- The words after a step of the shift: word `j` copied up. -/
theorem shift_words (L : List UInt64) (g : UInt64) {j : Nat} (hj : j < L.length) :
    (L.take (j + 1) ++ g :: L.drop (j + 1)).set (j + 1) L[j] = L.take j ++ L[j] :: L.drop j := by
  have ht : (L.take (j + 1)).length = j + 1 := by simp; omega
  have h := set_mid (L.take (j + 1)) (L.drop (j + 1)) g L[j]
  rw [ht] at h
  rw [h, List.take_add_one, List.getElem?_eq_getElem hj, Option.toList_some, List.append_assoc,
    List.singleton_append, List.drop_eq_getElem_cons hj]

variable [Labels] {m : MachineData}

/-- The array's address. -/
abbrev arr (m : MachineData) : BitVec 64 := m.regs.X0.toBitVec

/-- Element `p`'s address. -/
abbrev pos (m : MachineData) (p : Nat) : BitVec 64 := arr m + BitVec.ofNat 64 (8 * p)

/-- What every state of `ins_d` keeps of its entry state `m`. -/
structure Kp (m s : MachineData) : Prop where
  x0 : s.regs.getXReg .X0 = m.regs.getXReg .X0
  x1 : s.regs.getXReg .X1 = m.regs.getXReg .X1
  x2 : s.regs.getXReg .X2 = m.regs.getXReg .X2
  x30 : s.regs.getXReg .X30 = m.regs.getXReg .X30
  sv : Saved m s
  so : NativeRustcVm.SameOutside m.dmem s.dmem (NativeRustcVm.InRange (arr m) 2048)

omit [Labels] in
theorem Kp.refl (m : MachineData) : Kp m m :=
  ⟨rfl, rfl, rfl, rfl, Saved.refl m, fun _ _ ↦ rfl⟩

/-- A block run from a state that keeps `m`'s, keeping X0, X1, X2, X30, the callee-saved registers,
SP, and changing at most the array. -/
theorem Kp.block {s s' : MachineData} {env : Env} {S S' : SState} (hk : Kp m s)
    (hm : Match env S s) (hm' : Match env S' s') (hwf : env.WF) (hd : s.dmem = env.mem0)
    (hkeep : keeps S S' = true)
    (hregs : ∀ r ∈ [XReg.X0, .X1, .X2, .X30], S.reg r = some (.reg r) ∧ S'.reg r = some (.reg r))
    (hso : NativeRustcVm.SameOutside s.dmem s'.dmem (NativeRustcVm.InRange (arr m) 2048)) :
    Kp m s' where
  x0 := (Match.reg_eq hm hm' (hregs .X0 (by simp)).1 (hregs .X0 (by simp)).2).trans hk.x0
  x1 := (Match.reg_eq hm hm' (hregs .X1 (by simp)).1 (hregs .X1 (by simp)).2).trans hk.x1
  x2 := (Match.reg_eq hm hm' (hregs .X2 (by simp)).1 (hregs .X2 (by simp)).2).trans hk.x2
  x30 := (Match.reg_eq hm hm' (hregs .X30 (by simp)).1 (hregs .X30 (by simp)).2).trans hk.x30
  sv := hk.sv.trans (Match.saved hm hm' hwf hd hkeep)
  so := fun p hp ↦ (hso p hp).trans (hk.so p hp)

/-- The environment of element `p`. -/
abbrev env1 (m s : MachineData) (p : Nat) : Env := Env.ofMachine s [(pos m p, 8)]

/-- The environment of elements `p` and `p + 1`. -/
abbrev env2 (m s : MachineData) (p : Nat) : Env := Env.ofMachine s [(pos m p, 8), (pos m (p + 1), 8)]

section Geo

variable (hok : NativeRustcVm.Mapped m.dmem (arr m) 2048 ∧ NativeRustcVm.NoWrap (arr m) 2048)
include hok

omit [Labels] in
theorem pos_mapped {s : MachineData} (hk : Kp m s) {p : Nat} (hp : p < 256) :
    NativeRustcVm.Mapped s.dmem (pos m p) 8 :=
  fun i hi ↦ hk.sv.2.2 _ (hok.1.sub (o := 8 * p) (m := 8) (by omega) i hi)

omit [Labels] in
theorem pos_noWrap {p : Nat} (hp : p < 256) : NativeRustcVm.NoWrap (pos m p) 8 :=
  hok.2.sub (by omega)

omit [Labels] in
theorem pos_toNat {p : Nat} (hp : p < 256) : (pos m p).toNat = (arr m).toNat + 8 * p :=
  NativeRustcVm.toNat_add_ofNat (by have := hok.2; unfold NativeRustcVm.NoWrap at this; omega)

omit [Labels] in
theorem env1_wf {s : MachineData} (hk : Kp m s) {p : Nat} (hp : p < 256) : (env1 m s p).WF :=
  Env.wf_of ⟨⟨pos_mapped hok hk hp, pos_noWrap hok hp⟩, trivial⟩ (List.pairwise_singleton _ _)

omit [Labels] in
theorem env2_wf {s : MachineData} (hk : Kp m s) {p : Nat} (hp : p + 1 < 256) : (env2 m s p).WF := by
  refine Env.wf_of ⟨⟨pos_mapped hok hk (by omega), pos_noWrap hok (by omega)⟩,
    ⟨pos_mapped hok hk hp, pos_noWrap hok hp⟩, trivial⟩ (List.pairwise_pair.mpr ?_)
  show NativeRustcArm.Apart _ _ _ _
  unfold NativeRustcArm.Apart
  dsimp only
  rw [pos_toNat hok (by omega), pos_toNat hok hp]
  omega

omit [Labels] in
/-- A write into element `p` changes only the array. -/
theorem pos_sub {p : Nat} (hp : p < 256) {d d' : Mem 64}
    (h : NativeRustcVm.SameOutside d d' (NativeRustcVm.InRange (pos m p) 8)) :
    NativeRustcVm.SameOutside d d' (NativeRustcVm.InRange (arr m) 2048) :=
  NativeRustcVm.SameOutside.mono h fun _ hq ↦ NativeRustcVm.InRange.of_sub hq hok.2 (by omega)

end Geo

theorem elem_alias {s : MachineData} (hk : Kp m s) {regions : List (BitVec 64 × Nat)} {r p : Nat}
    (hp : p < 256) (hb : regions[r]? = some (pos m p, 8)) {y : Sym}
    (hy : (y.eval (Env.ofMachine s regions)).toNat = p) :
    (Sym.bin .add .W64 (.reg .X0) (.un (.memExtend ⟨.UXTX, .E3⟩) .W64
      (.bin .and .W64 y (.lit 255)))).eval (Env.ofMachine s regions) =
      (Env.ofMachine s regions).base r + BitVec.ofInt 64 0 := by
  rw [eval_elem, Env.base_ofMachine _ _ _ hb, hy, Nat.mod_eq_of_lt hp, Env.ofMachine_regs, hk.x0,
    show BitVec.ofInt 64 0 = 0#64 from rfl, BitVec.add_zero]
  rfl

omit [Labels] in
theorem load_pos {s : MachineData} {regions : List (BitVec 64 × Nat)} {r p : Nat}
    (hb : regions[r]? = some (pos m p, 8)) {w : UInt64} (h : WordAt s.dmem (pos m p) w) :
    (Env.ofMachine s regions).load r 0 8 = w.toBitVec :=
  load_word (by rw [Env.base_ofMachine _ _ _ hb, NativeRustcVm.addr_add_zero]; exact h)

/-- The value `x` at element `p` after a store of X2 there (`b3`, `b8`). -/
theorem store_x2 {s s' : MachineData} {S : SState} {p : Nat} (hk : Kp m s)
    (hm : Match (env1 m s p) S s')
    (hw : ∀ i < 8, findWrite 0 (0 + i) S.mem = some (.reg .X2, i)) :
    WordAt s'.dmem (pos m p) m.regs.X2 := by
  have h := hm.bytesAt_write (r := 0) (o := 0) (n := 8) (b := pos m p) (sz := 8) rfl (by omega) hw
  rw [byteOf_range, NativeRustcVm.addr_add_zero] at h
  simp only [Sym.eval, Env.ofMachine_regs, hk.x2] at h
  exact h

/-! ## The states -/

section States

variable (m) (L : List UInt64)

/-- The model's list. -/
abbrev lst : List Nat := L.map UInt64.toNat

/-- `x`. -/
abbrev xv : Nat := m.regs.X2.toNat

/-- What `ins_d` reaches: its postcondition at the return address. -/
abbrev Post (st : MachineState) : Prop := st.pc = retOf m ∧ InsDPost m st.data

/-- The elements before `i` are below `x`. -/
@[expose] def Below (i : Nat) : Prop := ∀ j (hj : j < i) (hjn : j < L.length), L[j].toNat < xv m

/-- Element `i`, if there is one, is above `x`. -/
@[expose] def Above (i : Nat) : Prop := ∀ (h : i < L.length), xv m < L[i].toNat

variable [Host] (k : Nat)

/-- The scan's head (`b1`) at element `i < n`. -/
structure SInv (i : Nat) (st : MachineState) : Prop where
  pc : st.pc = Host.addrOf (k + NativeRustcVmArm.Vm.InsD.b1Offset)
  kp : Kp m st.data
  d : st.data.dmem = m.dmem
  x8 : (st.data.regs.getXReg .X8).toNat = i
  lt : i < L.length
  below : Below m L i

/-- The shift's set-up (`b6`), `x` to go in at `i ≤ n`. -/
structure SixInv (i : Nat) (st : MachineState) : Prop where
  pc : st.pc = Host.addrOf (k + NativeRustcVmArm.Vm.InsD.b6Offset)
  kp : Kp m st.data
  d : st.data.dmem = m.dmem
  x8 : (st.data.regs.getXReg .X8).toNat = i
  le : i ≤ L.length
  below : Below m L i
  above : Above m L i

/-- The shift's head (`b7`): the elements from `j` moved up one, `i < j ≤ n`, word `g` at `j`. -/
structure TInv (i j : Nat) (g : UInt64) (st : MachineState) : Prop where
  pc : st.pc = Host.addrOf (k + NativeRustcVmArm.Vm.InsD.b7Offset)
  kp : Kp m st.data
  x8 : (st.data.regs.getXReg .X8).toNat = i
  x9 : (st.data.regs.getXReg .X9).toNat = j
  lt : i < j
  le : j ≤ L.length
  below : Below m L i
  above : Above m L i
  w : WordsAt st.data.dmem (arr m) (L.take j ++ g :: L.drop j)

/-- The store (`b8`): the elements from `i` moved up one. -/
structure EInv (i : Nat) (g : UInt64) (st : MachineState) : Prop where
  pc : st.pc = Host.addrOf (k + NativeRustcVmArm.Vm.InsD.b8Offset)
  kp : Kp m st.data
  x8 : (st.data.regs.getXReg .X8).toNat = i
  le : i ≤ L.length
  below : Below m L i
  above : Above m L i
  w : WordsAt st.data.dmem (arr m) (L.take i ++ g :: L.drop i)

end States

omit [Labels] in
/-- **The postcondition** from the words `L` the array held, and the result for their list. -/
theorem post_of {L : List UInt64} (hL : L.length = m.regs.X1.toNat)
    (hW : WordsAt m.dmem (arr m) L) {m' : MachineData} (hsv : Saved m m')
    (hso : NativeRustcVm.SameOutside m.dmem m'.dmem (NativeRustcVm.InRange (arr m) 2048))
    (h0 : m'.regs.X0.toNat = (insD (lst L) (xv m)).length)
    (hw : WordsAt m'.dmem (arr m) ((insD (lst L) (xv m)).map Nat.toUInt64)) : InsDPost m m' := by
  refine ⟨fun l hl hb hwl ↦ ?_, hso, hsv⟩
  have he : l.map Nat.toUInt64 = L := wordsAt_unique hwl hW (by simp only [List.length_map]; omega)
  have : l = lst L := by rw [eq_map_toNat hb, he]
  subst this
  exact ⟨h0, hw⟩

omit [Labels] in
/-- `insD` where `x` goes in at `i`, as words. -/
theorem insD_words {L : List UInt64} {i : Nat} (hle : i ≤ L.length) (hb : Below m L i)
    (ha : Above m L i) :
    insD (lst L) (xv m) = (lst L).take i ++ xv m :: (lst L).drop i ∧
      ((lst L).take i ++ xv m :: (lst L).drop i).map Nat.toUInt64 =
        L.take i ++ m.regs.X2 :: L.drop i := by
  refine ⟨?_, ?_⟩
  · rcases Nat.lt_or_eq_of_le hle with hi | rfl
    · exact insD_at _ _ i (by simpa using hi) (fun j hj ↦ by simpa using hb j hj (by omega))
        (by simpa using ha hi)
    · have hall : ∀ y ∈ lst L, y < xv m := fun y hy ↦ by
        obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hy
        simpa using hb j (by simpa using hj) (by simpa using hj)
      rw [insD_end _ _ hall, List.take_of_length_le (by simp), List.drop_of_length_le (by simp)]
  · simp only [List.map_append, List.map_cons, List.map_take, List.map_drop, map_toUInt64_toNat]
    simp [xv]

end

end NativeRustcVmArm.Wire.InsD
