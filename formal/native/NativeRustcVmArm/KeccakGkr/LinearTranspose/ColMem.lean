module

public import NativeRustcVmArm.KeccakGkr.LinearTranspose.Lanes

/-!
# `linear_transpose`: an element of a column

Each column loop (`b11`, `b13`, `b15`, `b17`, `b19`, column `x`) loads the five elements of `g` at
position `z` of the column's lanes `x + 5 y` (from the region at `g + 16 z`, offsets
`1024 x + 5120 y`), sums them (`tree`, the `eor` tree rustc emits) and stores the sum at the column's
element `z`. `col_mem`: what memory then holds (`ColMem`).
-/

namespace NativeRustcVmArm.KeccakGkr.LinearTranspose

open NativeRustcArm NativeRustcArm.Sym NativeVm.Model
open NativeRustcVmArm.Arrays NativeRustcVmArm.Sumcheck
open NativeRustcVmArm.Vm.LinearTranspose LeanVM.Parameters
open NativeRustcVm (Region)
open NativeRustcVm.KeccakGkr (gW colW outW weightsBytes)

@[expose] public section

/-- The load of word `d` of lane `x + 5 y`'s element. -/
def ldx (x y d : Nat) : Sym := .load 0 (1024 * x + 5120 * y + d) 8

/-- The sum of a column's word `d`, as rustc's `eor` tree. -/
def tree (x d : Nat) : Sym :=
  .bin .eor .W64 (ldx x 4 d) (.bin .eor .W64 (.bin .eor .W64 (ldx x 3 d) (ldx x 2 d))
    (.bin .eor .W64 (ldx x 1 d) (ldx x 0 d)))

/-- What the column loops' memory holds: `g`, and the columns up to column `x`'s element `z`. -/
structure ColMem [Labels] (m0 : MachineData) (ws : Array EW) (x z : Nat) (st : MachineData) :
    Prop where
  g : ElemsAt st.dmem (gA m0) (gF ws) 1600
  c : ElemsAt st.dmem (cA m0) (cF ws) (64 * x + z)

end

public section

theorem tree_eval [Labels] (env : Env) (x d : Nat) :
    (tree x d).eval env = env.load 0 (1024 * x + 5120 * 4 + d) 8 ^^^
      ((env.load 0 (1024 * x + 5120 * 3 + d) 8 ^^^ env.load 0 (1024 * x + 5120 * 2 + d) 8) ^^^
        (env.load 0 (1024 * x + 5120 * 1 + d) 8 ^^^ env.load 0 (1024 * x + 5120 * 0 + d) 8)) := by
  simp [tree, ldx, Sym.eval, BinOp.apply]

/-- The five elements summed as the `eor` trees. -/
theorem col_ew (a0 a1 a2 a3 a4 : EW) :
    (⟨UInt64.ofBitVec (a4.c0.toBitVec ^^^ ((a3.c0.toBitVec ^^^ a2.c0.toBitVec) ^^^
        (a1.c0.toBitVec ^^^ a0.c0.toBitVec))),
      UInt64.ofBitVec (a4.c1.toBitVec ^^^ ((a3.c1.toBitVec ^^^ a2.c1.toBitVec) ^^^
        (a1.c1.toBitVec ^^^ a0.c1.toBitVec)))⟩ : EW) = a0 + a1 + a2 + a3 + a4 := by
  show EW.mk _ _ = EW.mk ((((a0.c0 ^^^ a1.c0) ^^^ a2.c0) ^^^ a3.c0) ^^^ a4.c0)
    ((((a0.c1 ^^^ a1.c1) ^^^ a2.c1) ^^^ a3.c1) ^^^ a4.c1)
  congr 1 <;> apply UInt64.toBitVec_inj.mp <;> simp only [UInt64.toBitVec_xor] <;> ac_rfl

theorem cF_eq (ws : Array EW) {x z : Nat} (hz : z < 64) :
    cF ws (64 * x + z) = gF ws (64 * (x + 5 * 0) + z) + gF ws (64 * (x + 5 * 1) + z) +
      gF ws (64 * (x + 5 * 2) + z) + gF ws (64 * (x + 5 * 3) + z) + gF ws (64 * (x + 5 * 4) + z) := by
  simp only [cF, gF, colW]
  rw [show (64 * x + z) / 64 = x by omega, show (64 * x + z) % 64 = z by omega]
  simp only [show ∀ y, (64 * (x + 5 * y) + z) / 64 = x + 5 * y from fun y ↦ by omega,
    show ∀ y, (64 * (x + 5 * y) + z) % 64 = z from fun y ↦ by omega]
  rfl

variable [Labels] {ws : Array EW} {m0 : MachineData}

/-- **An element of a column**: after a column loop's block from the state `s` (regions: `g`'s
lanes from `g + 16 z`, the column's element), memory holds it. -/
theorem col_mem (hpre : LinearTransposePre ws m0) {x z : Nat} (hz : z < 64)
    {s s' : MachineData} (hI : ColMem m0 ws x z s) {n : Nat}
    (hn : 1024 * x + 20496 ≤ n) (hn' : 16 * z + n ≤ 25600) {S' : SState}
    (hm' : Match (Env.ofMachine s [(gA m0 + BitVec.ofNat 64 (16 * z), n),
      (cA m0 + BitVec.ofNat 64 (16 * (64 * x + z)), 16)]) S' s')
    (hwf : (Env.ofMachine s [(gA m0 + BitVec.ofNat 64 (16 * z), n),
      (cA m0 + BitVec.ofNat 64 (16 * (64 * x + z)), 16)]).WF)
    (hmem : S'.mem = [⟨1, 8, 8, tree x 8⟩, ⟨1, 0, 8, tree x 0⟩]) :
    ColMem m0 ws x (z + 1) s' := by
  have hA := pre_areas hpre
  have hgok := Areas.ok hA (r := ⟨gA m0, weightsBytes⟩) (Or.inl (by simp [wsR]))
  have hcok := Areas.ok hA (r := ⟨cA m0, 5120⟩) (Or.inl (by simp [wsR]))
  have hgc := Areas.apart_ws hA (i := 0) (j := 1) (by simp [wsR]) (by simp [wsR]) (by decide)
  simp only [wsR, List.getElem_cons_zero, List.getElem_cons_succ] at hgc
  have hnw1 := (sub_ok hcok (o := 16 * (64 * x + z)) (n := 16)
    (by show 16 * (64 * x + z) + 16 ≤ 5120; omega)).2
  have h := KeccakGkr.Match.ewAt_write2 hm' (pre := []) (by rw [hmem]; rfl) rfl nofun (r := 1) rfl
    (by decide)
  rw [tree_eval, tree_eval] at h
  have hld : ∀ y < 5,
      (Env.ofMachine s [(gA m0 + BitVec.ofNat 64 (16 * z), n),
        (cA m0 + BitVec.ofNat 64 (16 * (64 * x + z)), 16)]).load 0 (1024 * x + 5120 * y + 0) 8 =
        (gF ws (64 * (x + 5 * y) + z)).c0.toBitVec ∧
      (Env.ofMachine s [(gA m0 + BitVec.ofNat 64 (16 * z), n),
        (cA m0 + BitVec.ofNat 64 (16 * (64 * x + z)), 16)]).load 0 (1024 * x + 5120 * y + 8) 8 =
        (gF ws (64 * (x + 5 * y) + z)).c1.toBitVec := by
    intro y hy
    have he := hI.g (64 * (x + 5 * y) + z) (by omega)
    rw [show gA m0 + BitVec.ofNat 64 (16 * (64 * (x + 5 * y) + z)) =
        (gA m0 + BitVec.ofNat 64 (16 * z)) + BitVec.ofNat 64 (1024 * x + 5120 * y) by
      rw [NativeRustcVm.addr_add_add]; congr 2; omega] at he
    exact load_ew (env := Env.ofMachine s [(gA m0 + BitVec.ofNat 64 (16 * z), n),
      (cA m0 + BitVec.ofNat 64 (16 * (64 * x + z)), 16)]) (r := 0) he
  rw [(hld 0 (by decide)).1, (hld 1 (by decide)).1, (hld 2 (by decide)).1, (hld 3 (by decide)).1,
    (hld 4 (by decide)).1, (hld 0 (by decide)).2, (hld 1 (by decide)).2, (hld 2 (by decide)).2,
    (hld 3 (by decide)).2, (hld 4 (by decide)).2, col_ew, ← cF_eq ws hz] at h
  have hW : ∀ w ∈ S'.mem, w.r = 1 ∧ w.off + w.n ≤ 16 := by
    rw [hmem]; intro w hw; simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases hw with rfl | rfl <;> exact ⟨rfl, by simp⟩
  have hso : SameOutside s.dmem s'.dmem (InRange (cA m0 + BitVec.ofNat 64 (16 * (64 * x + z))) 16) :=
    NativeRustcVm.SameOutside.mono (hm'.sameOutside hwf) fun p hw ↦
      Written.inRange (env := Env.ofMachine s [(gA m0 + BitVec.ofNat 64 (16 * z), n),
        (cA m0 + BitVec.ofNat 64 (16 * (64 * x + z)), 16)]) (r := 1) rfl hnw1 hW hw
  refine ⟨hI.g.keep hso (fun p hp hc ↦ ?_) (by unfold NoWrap; have := hgok.2; unfold NativeRustcVm.NoWrap at this; simp only [weightsBytes] at this; omega), ?_⟩
  · have hgc' : Apart (gA m0) (16 * 1600) (cA m0 + BitVec.ofNat 64 (16 * (64 * x + z))) 16 := by
      have := Apart.sub (o := 0) (n := 16 * 1600) (o' := 16 * (64 * x + z)) (n' := 16) hgc hgok.2
        hcok.2 (by decide) (by show 16 * (64 * x + z) + 16 ≤ 5120; omega) (by decide) (by decide)
      rwa [NativeRustcVm.addr_add_zero] at this
    exact NativeRustcVm.Apart.not_inRange hgc'
      (by unfold NativeRustcVm.NoWrap; have := hgok.2; unfold NativeRustcVm.NoWrap at this; simp only [weightsBytes] at this; omega)
      hnw1 hp hc
  · rw [show 64 * x + (z + 1) = 64 * x + z + 1 by omega]
    refine hI.c.grow (k := 1) (NativeRustcVm.NoWrap.sub (o := 0) (by rw [NativeRustcVm.addr_add_zero] at *; exact hcok.2)
        (by show 0 + 16 * (64 * x + z + 1) ≤ 5120; omega) |>.trans_eq' (by rw [NativeRustcVm.addr_add_zero]))
      (by rw [Nat.mul_one]; exact hso) fun j hj ↦ ?_
    obtain rfl : j = 0 := by omega
    rw [Nat.add_zero]
    rw [NativeRustcVm.addr_add_zero] at h
    exact h

end

end NativeRustcVmArm.KeccakGkr.LinearTranspose
