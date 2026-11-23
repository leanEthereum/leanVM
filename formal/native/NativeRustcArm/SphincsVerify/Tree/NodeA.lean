module

public import NativeRustcArm.Code.Common.Memset.Names

public import NativeRustcArm.SphincsVerify.Tree.Leaf1
public import NativeRustcArm.SphincsVerify.Tree.NodeExec

/-!
# The fold's node: the loop head

At the loop head `b153` with the fold's value after `z` steps at `20624` (`AtNode`), the node's
children (`Run.children`: the value and the sibling, bit `z` of the key's leaf saying which is
left) go to `22672`, its address (`Run.nodeAdrs`) to `23696`, then `memset` zeroes hasher A
(`nodeA`, to `AtN2`).
-/

namespace NativeRustcArm.SphincsVerifyProof.Run

open NativeRustc NativeRustc.Sphincs

variable (r : Run)

/-- The address of the node above height `z`. -/
@[expose] public def nodeAdrs (l z : Nat) : List UInt8 :=
  withTreeIndex (withTreeHeight (withType (r.key l).treeAdrs 2) (z + 1).toUInt32)
    ((r.key l).leaf.toNat >>> (z + 1)).toUInt32

/-- The children of the node above height `z`, from the value `cur`. -/
@[expose] public def children (l : Nat) (cur : List UInt8) (z : Nat) : List UInt8 :=
  if (r.key l).leaf.toNat >>> z &&& 1 = 0 then cur ++ r.sibling l z else r.sibling l z ++ cur

public theorem foldStep_eq (l : Nat) (cur : List UInt8) (z : Nat) :
    r.foldStep l cur z = th r.seed (r.nodeAdrs l z) (r.children l cur z) := rfl

end NativeRustcArm.SphincsVerifyProof.Run

namespace NativeRustcArm.SphincsVerifyProof.Tree

open NativeRustc NativeRustc.Keccak NativeRustc.Sphincs NativeRustcArm.Sym NativeRustcArm
  LeanVM.Protocol.KeccakHash Native.Keccak
open NativeRustcArm.Sphincs.SphincsVerify

public section

/-! ## Bits and bytes -/

theorem length_th (seed adrs m : List UInt8) : (th seed adrs m).length = 16 := by
  rw [th, List.length_take, NativeRustc.Sphincs.length_hashBytes]
  rfl

theorem length_foldUpTo (r : Run) (l : Nat) (e : List (List UInt8)) (z : Nat) :
    (r.foldUpTo l e z).length = 16 := by
  induction z with
  | zero => exact length_th _ _ _
  | succ z _ => rw [Tree.foldUpTo_succ]; exact length_th _ _ _

/-- The test of bit `z`. -/
theorem bit_test (x : BitVec 64) {z : Nat} (hz : z < 64) :
    ((1#64 <<< z &&& x) == 0#64) = decide (x.toNat >>> z &&& 1 = 0) := by
  rw [Bool.eq_iff_iff, beq_iff_eq, decide_eq_true_iff]
  constructor
  · intro h
    have := congrArg (fun v : BitVec 64 ↦ v.getLsbD z) h
    simp only [BitVec.getLsbD_and, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_zero] at this
    have hb : x.getLsbD z = false := by
      simpa [hz, BitVec.getLsbD_one] using this
    rw [BitVec.getLsbD, Nat.testBit] at hb
    simpa [Nat.shiftRight_eq_div_pow, Nat.one_and_eq_mod_two, Nat.and_comm] using hb
  · intro h
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    simp only [BitVec.getLsbD_and, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_zero]
    by_cases hiz : i = z
    · subst hiz
      have : x.getLsbD i = false := by
        rw [BitVec.getLsbD, Nat.testBit]
        simpa [Nat.shiftRight_eq_div_pow, Nat.one_and_eq_mod_two, Nat.and_comm] using h
      simp [this]
    · simp [BitVec.getLsbD_one]
      omega

/-- The 32-bit word `l << 24` is `be32 l` in memory. -/
theorem bytes_layer {l : Nat} (hl : l < 3) :
    (List.range 4).map (byteOf (BitVec.ofNat 64 (l * 16777216))) = be32 l.toUInt32 := by
  interval_cases l <;> decide

/-- `rev` of a 32-bit value in memory is its big-endian bytes. -/
theorem bytes_rev_ofNat (n : Nat) :
    (List.range 4).map (byteOf (UnOp.apply .rev .W32 (BitVec.ofNat 64 n))) = be32 n.toUInt32 := by
  rw [bytes_rev32]
  congr 1
  apply UInt32.toNat.inj
  simp only [UInt32.toNat_ofNat', BitVec.toNat_ofNat, Nat.toUInt32_eq]
  exact Nat.mod_mod_of_dvd n (by decide)

end

/-! ## The loop head -/

/-- The bit test of `b153`. -/
@[expose] public def bitC : SBool :=
  .cmp .eq .W64 (.bin .and .W64 (.bin .lslv .W64 (.lit 1) (.reg .X19)) (.load 0 32 8)) (.lit 0)

/-- The sibling's index of `b153`. -/
@[expose] public def idxS : Sym := .un (.shift .LSL 4) .W64 (.reg .X19)


public section

variable [Host] (r : Run)

/-- **The loop head**, `z` steps of the fold done: the node's registers (X19 `z`, X24 the layer's
path, X20 `21648`, X27 the layer's word `l << 24`), the value at `20624`. -/
@[expose] def AtNode (l : Nat) (e : List (List UInt8)) (z : Nat) (m : MachineData) : Prop :=
  Base r l m ∧ z < heightOf l ∧ Run.RegIs m .X19 (BitVec.ofNat 64 z) ∧
    Run.RegIs m .X24 (r.off (12468 + 16 * pathStart l)) ∧ Run.RegIs m .X20 (r.off 21648) ∧
    Run.RegIs m .X27 (BitVec.ofNat 64 (l * 16777216)) ∧
    BytesAt m.dmem (r.off 20624) (r.foldUpTo l e z)

/-- **After the node's `memset`**: X19 `z + 1`; hasher A zero, the address at `23696`, the
children at `22672`. -/
@[expose] def AtN2 (l : Nat) (e : List (List UInt8)) (z : Nat) (m : MachineData) : Prop :=
  Base r l m ∧ z < heightOf l ∧ Run.RegIs m .X19 (BitVec.ofNat 64 (z + 1)) ∧
    Run.RegIs m .X24 (r.off (12468 + 16 * pathStart l)) ∧ Run.RegIs m .X20 (r.off 21648) ∧
    Run.RegIs m .X27 (BitVec.ofNat 64 (l * 16777216)) ∧
    BytesAt m.dmem (r.off 16400) (List.replicate 344 0) ∧
    BytesAt m.dmem (r.off 23696) (r.nodeAdrs l z) ∧
    BytesAt m.dmem (r.off 22672) (r.children l (r.foldUpTo l e z) z)

variable {r}

omit [Host] in
theorem pathStart_cases {l : Nat} (hl : l < 3) :
    pathStart l = 0 ∨ pathStart l = 8 ∨ pathStart l = 16 := by
  interval_cases l <;> decide

omit [Host] in
theorem heightOf_le {l : Nat} (hl : l < 3) : heightOf l ≤ 10 := by
  interval_cases l <;> decide

omit [Host] in
theorem allOf_append {α : Type} {P : α → Prop} : ∀ {l₁ l₂ : List α}, AllOf P l₁ → AllOf P l₂ →
    AllOf P (l₁ ++ l₂)
  | [], _, _, h => h
  | _ :: _, _, ⟨h, h₁⟩, h₂ => ⟨h, allOf_append h₁ h₂⟩

omit [Host] in
/-- A 16-byte value's low 8 bytes, as loaded. -/
theorem load_lo {m : MachineData} {vars : Nat → BitVec 64} {o : Nat} {v : List UInt8}
    (h : BytesAt m.dmem (r.off o) v) (hl : v.length = 16) :
    (List.range 8).map (byteOf ((r.env m vars).load 0 o 8)) = v.take 8 := by
  rw [← List.take_append_drop 8 v] at h
  exact bytes_load (bytesAt_append_left h) (by simp [hl]) (by decide)

omit [Host] in
/-- A 16-byte value's high 8 bytes, as loaded. -/
theorem load_hi {m : MachineData} {vars : Nat → BitVec 64} {o : Nat} {v : List UInt8}
    (h : BytesAt m.dmem (r.off o) v) (hl : v.length = 16) :
    (List.range 8).map (byteOf ((r.env m vars).load 0 (o + 8) 8)) = v.drop 8 := by
  rw [← List.take_append_drop 8 v] at h
  have h2 := bytesAt_append_right h
  rw [List.length_take, Nat.min_eq_left (by omega), Run.off_add] at h2
  exact bytes_load h2 (by simp [hl]) (by decide)

omit [Host] in
/-- **A write of `n` bytes** whose value evaluates to `w`. -/
theorem write_eval [Labels] {m m' : MachineData} {vars : Nat → BitVec 64} {S : SState}
    (hm : Match (r.env m vars) S m') {o n : Nat} {v : Sym} {w : BitVec 64} (hle : o + n ≤ 29376)
    (hw : ∀ i < n, findWrite 0 (o + i) S.mem = some (v, i)) (hv : v.eval (r.env m vars) = w)
    {bs : List UInt8} (hbs : (List.range n).map (byteOf w) = bs) : BytesAt m'.dmem (r.off o) bs :=
  write_bytes hm hle hw (hv ▸ hbs)

omit [Host] in
/-- **Two 16-byte values** written as four 8-byte halves from `o`. -/
theorem write_pair [Labels] {m m' : MachineData} {vars : Nat → BitVec 64} {S : SState}
    (hm : Match (r.env m vars) S m') {o : Nat} (ho : o + 32 ≤ 29376) {a b : List UInt8}
    (ha : a.length = 16) (hb : b.length = 16) {v₀ v₁ v₂ v₃ : Sym}
    (h₀ : ∀ i < 8, findWrite 0 (o + i) S.mem = some (v₀, i))
    (h₁ : ∀ i < 8, findWrite 0 (o + 8 + i) S.mem = some (v₁, i))
    (h₂ : ∀ i < 8, findWrite 0 (o + 16 + i) S.mem = some (v₂, i))
    (h₃ : ∀ i < 8, findWrite 0 (o + 24 + i) S.mem = some (v₃, i))
    (e₀ : (List.range 8).map (byteOf (v₀.eval (r.env m vars))) = a.take 8)
    (e₁ : (List.range 8).map (byteOf (v₁.eval (r.env m vars))) = a.drop 8)
    (e₂ : (List.range 8).map (byteOf (v₂.eval (r.env m vars))) = b.take 8)
    (e₃ : (List.range 8).map (byteOf (v₃.eval (r.env m vars))) = b.drop 8) :
    BytesAt m'.dmem (r.off o) (a ++ b) := by
  rw [← List.take_append_drop 8 a, ← List.take_append_drop 8 b]
  simp only [List.append_assoc]
  have l8 : ∀ x : List UInt8, x.length = 16 → (x.take 8).length = 8 := fun x hx ↦ by simp [hx]
  have l8' : ∀ x : List UInt8, x.length = 16 → (x.drop 8).length = 8 := fun x hx ↦ by simp [hx]
  refine bytesAt_cat (l8 a ha) (write_bytes hm (by omega) h₀ e₀) ?_
  refine bytesAt_cat (l8' a ha) (write_bytes hm (by omega) h₁ e₁) ?_
  refine bytesAt_cat (l8 b hb) (write_bytes hm (by omega) h₂ e₂) ?_
  exact write_bytes hm (by omega) h₃ e₃

omit [Host] in
theorem eval_load [Labels] {m : MachineData} {vars : Nat → BitVec 64} (o n : Nat) :
    (Sym.load 0 o n).eval (r.env m vars) = (r.env m vars).load 0 o n := rfl

omit [Host] in
/-- The sibling's index: `z << 4`. -/
theorem eval_idx [Labels] {m : MachineData} {vars : Nat → BitVec 64} {z : Nat}
    (h19 : Run.RegIs m .X19 (BitVec.ofNat 64 z)) (hz : z < 10) :
    ((Sym.un (.shift .LSL 4) .W64 (.reg .X19)).eval (r.env m vars)).toNat = 16 * z := by
  simp only [Sym.eval, UnOp.apply, low_W64, ext_W64, shiftW, Env.ofMachine_regs]
  rw [h19, BitVec.toNat_shiftLeft, BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt (by omega), Nat.shiftLeft_eq, Nat.mod_eq_of_lt (by omega)]
  omega

end

/-! ## The node's `memset` -/

public section

variable [Host] {r : Run}

/-- **`b153` and `memset`**, from the symbolic run's facts. -/
theorem nodeA_gen (hp : Placed code r.k) (hc : Callees) (hpre : r.Pre) {l : Nat}
    {e : List (List UInt8)} {z : Nat} {m : MachineData} (h : AtNode r l e z m) {p : Nat}
    (hpp : pathStart l = p) {S' : SState} (hrun : exec b153 (nodeS p) = some (S', .call NativeRustcArm.Common.Memset.entryLabel))
    (hsp : S'.sp = .ptr 0 0) (h29 : S'.reg .X29 = some (.ptr 0 29280))
    (hfw : Run.frameWrites S' = true) (hnw : Run.noWriteIn S' 0 15984 = true)
    (h21 : S'.reg .X21 = some (.ptr 0 26968)) (h25 : S'.reg .X25 = some (.ptr 0 16600))
    (h26 : S'.reg .X26 = some (.lit 136))
    (hx0 : S'.reg .X0 = some (.ptr 0 16400)) (hx1 : S'.reg .X1 = some (.lit 0))
    (hx2 : S'.reg .X2 = some (.lit 344))
    (hx19 : S'.reg .X19 = some (.bin .add .W64 (.reg .X19) (.lit 1)))
    (hx24 : S'.reg .X24 = some (.ptr 0 ((12468 + 16 * p : Nat) : Int))) (hx20 : S'.reg .X20 = some (.ptr 0 21648))
    (hx27 : S'.reg .X27 = some (.reg .X27))
    (wA0 : ∀ i < 4, findWrite 0 (23696 + i) S'.mem = some (.reg .X27, i))
    (wA1 : ∀ i < 4, findWrite 0 (23700 + i) S'.mem = some (.lit 0, i))
    (wA2 : ∀ i < 8, findWrite 0 (23704 + i) S'.mem = some (.load 0 424 8, i))
    (wA3 : ∀ i < 8, findWrite 0 (23712 + i) S'.mem = some (.lit 33554432, i))
    (wA4 : ∀ i < 4, findWrite 0 (23720 + i) S'.mem =
      some (.un .rev .W32 (.bin .add .W64 (.reg .X19) (.lit 1)), i))
    (wA5 : ∀ i < 4, findWrite 0 (23724 + i) S'.mem = some (.un .rev .W32 (.bin .lsrv .W64
      (.load 0 32 8) (.bin .add .W64 (.reg .X19) (.lit 1))), i))
    (wC0 : ∀ i < 8, findWrite 0 (22672 + i) S'.mem = some (.ite (bitC) (.load 0 20624 8)
      (.loadx 0 (12468 + 16 * p) idxS 8), i))
    (wC1 : ∀ i < 8, findWrite 0 (22672 + 8 + i) S'.mem = some (.ite (bitC) (.load 0 20632 8)
      (.loadx 0 (12476 + 16 * p) idxS 8), i))
    (wC2 : ∀ i < 8, findWrite 0 (22672 + 16 + i) S'.mem = some (.ite (bitC)
      (.loadx 0 (12468 + 16 * p) idxS 8) (.load 0 20624 8), i))
    (wC3 : ∀ i < 8, findWrite 0 (22672 + 24 + i) S'.mem = some (.ite (bitC)
      (.loadx 0 (12476 + 16 * p) idxS 8) (.load 0 20632 8), i)) :
    Eventually (step1 Host.exe) (fun st ↦ st.pc = r.pc NativeRustcArm.Sphincs.SphincsVerify.b154Offset ∧ AtN2 r l e z st.data)
      ⟨m, r.pc NativeRustcArm.Sphincs.SphincsVerify.b153Offset⟩ := by
  obtain ⟨hB, hz, h19, h24, h20, h27, hV⟩ := h
  have hl := hB.1
  have hh := heightOf_le hl
  have hwf := r.frame_wf hpre hB.2.1 (fun _ ↦ 0)
  have hm0 : Match (r.env m) (nodeS p) m := r.match_frame hpre hB.2.1
    (allOf_append (allOf_keptRegs hB _) ⟨h24.trans (hpp ▸ (eval_ptr _).symm),
      h20.trans (eval_ptr _).symm, trivial⟩) trivial
    ⟨by show (m.regs.getXReg .X19).toBitVec.toNat < 10; rw [h19, BitVec.toNat_ofNat]; omega,
      trivial⟩ trivial
  refine exec_then (hb153 hp) hrun hwf hm0 fun st hm hpc ↦ ?_
  have hB1 := Base.of_match hpre hB hm hwf hsp h29 hfw hnw h21 h25 h26
  have h0 : Run.RegIs st.data .X0 (r.off 16400) := (hm.regs .X0 _ hx0).trans (eval_ptr 16400)
  have h1 : st.data.regs.X1 = 0 := UInt64.toBitVec_inj.mp (hm.regs .X1 _ hx1)
  have h2 : st.data.regs.X2.toNat = 344 := regIs_toNat (hm.regs .X2 _ hx2) (by decide)
  have hK := hB.2.2.1
  obtain ⟨-, -, -, -, h32, -, -, -, -, -, h424⟩ := hK.2
  -- the address
  have hA : BytesAt st.data.dmem (r.off 23696) (r.nodeAdrs l z) := by
    rw [Run.nodeAdrs, nodeAdrs_eq, show (r.key l).layer = l from rfl]
    refine bytesAt_cat rfl (write_eval hm (by decide) wA0 (h27 : _) (bytes_layer hl)) ?_
    refine bytesAt_cat rfl (write_eval hm (by decide) wA1 rfl (by simp only [Sym.eval]; decide)) ?_
    refine bytesAt_cat rfl (write_eval hm (by decide) wA2 rfl (bytes_load h424 rfl (by decide))) ?_
    rw [← List.append_assoc]
    refine bytesAt_cat rfl (write_eval hm (by decide) wA3 rfl (by simp only [Sym.eval]; decide)) ?_
    have e4 : (Sym.un .rev .W32 (.bin .add .W64 (.reg .X19) (.lit 1))).eval (r.env m) =
        UnOp.apply .rev .W32 (BitVec.ofNat 64 (z + 1)) := by
      simp only [Sym.eval, BinOp.apply, low_W64, ext_W64, Env.ofMachine_regs]
      rw [h19, BitVec.ofNat_add]
    have e5 : (Sym.un .rev .W32 (.bin .lsrv .W64 (.load 0 32 8) (.bin .add .W64 (.reg .X19)
        (.lit 1)))).eval (r.env m) =
        UnOp.apply .rev .W32 (BitVec.ofNat 64 ((r.key l).leaf.toNat >>> (z + 1))) := by
      simp only [Sym.eval, BinOp.apply, low_W64, ext_W64, Env.ofMachine_regs]
      rw [h19, load_word h32]
      congr 1
      apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
      show ((r.key l).leaf.toUInt64.toBitVec.ushiftRight
        ((z % 2 ^ 64 + 1 % 2 ^ 64) % 2 ^ 64 % 64)).toNat = (r.key l).leaf.toNat >>> (z + 1) % 2 ^ 64
      have key : ∀ (x : BitVec 64) (n : Nat), (x.ushiftRight n).toNat = x.toNat >>> n :=
        fun x n ↦ BitVec.toNat_ushiftRight x n
      rw [key, UInt64.toNat_toBitVec, UInt32.toNat_toUInt64]
      have hlt : (r.key l).leaf.toNat < 2 ^ 32 := (r.key l).leaf.toNat_lt
      rw [Nat.mod_eq_of_lt (a := z) (by omega), Nat.mod_eq_of_lt (a := 1) (by omega),
        Nat.mod_eq_of_lt (a := z + 1) (by omega), Nat.mod_eq_of_lt (a := z + 1) (by omega)]
      exact (Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.shiftRight_le _ _) (by omega))).symm
    refine bytesAt_cat rfl (write_eval hm (by decide) wA4 e4 (bytes_rev_ofNat (z + 1))) ?_
    exact write_eval hm (by decide) wA5 e5 (bytes_rev_ofNat _)
  -- the children
  have hcur := length_foldUpTo r l e z
  have hsib := length_sibling r hl hz
  have hsibB := bytesAt_sibling r hK.1.2.1 hl hz
  rw [hpp] at hsibB
  have hbit : bitC.eval (r.env m) = decide ((r.key l).leaf.toNat >>> z &&& 1 = 0) := by
    simp only [bitC, SBool.eval, Sym.eval, CmpOp.apply, BinOp.apply, low_W64, ext_W64,
      Env.ofMachine_regs]
    rw [h19, load_word h32]
    have hzz : (BitVec.ofNat 64 z).toNat % 64 = z := by
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
    show ((BitVec.ofNat 64 1 <<< ((BitVec.ofNat 64 z).toNat % 64) &&&
      (r.key l).leaf.toUInt64.toBitVec) == BitVec.ofNat 64 0) = _
    rw [hzz, bit_test _ (by omega), UInt64.toNat_toBitVec, UInt32.toNat_toUInt64]
  have hix : ((idxS).eval (r.env m)).toNat = 16 * z := eval_idx h19 (by omega)
  have sLo : (List.range 8).map (byteOf ((Sym.loadx 0 (12468 + 16 * p) idxS 8).eval (r.env m))) =
      (r.sibling l z).take 8 := by
    show (List.range 8).map (byteOf ((r.env m).load 0 (12468 + 16 * p + (idxS.eval (r.env m)).toNat) 8)) = _
    rw [hix, show 12468 + 16 * p + 16 * z = 12468 + 16 * (p + z) by omega]
    exact load_lo hsibB hsib
  have sHi : (List.range 8).map (byteOf ((Sym.loadx 0 (12476 + 16 * p) idxS 8).eval (r.env m))) =
      (r.sibling l z).drop 8 := by
    show (List.range 8).map (byteOf ((r.env m).load 0 (12476 + 16 * p + (idxS.eval (r.env m)).toNat) 8)) = _
    rw [hix, show 12476 + 16 * p + 16 * z = 12468 + 16 * (p + z) + 8 by omega]
    exact load_hi hsibB hsib
  have cLo : (List.range 8).map (byteOf ((Sym.load 0 20624 8).eval (r.env m))) =
      (r.foldUpTo l e z).take 8 := load_lo hV hcur
  have cHi : (List.range 8).map (byteOf ((Sym.load 0 20632 8).eval (r.env m))) =
      (r.foldUpTo l e z).drop 8 := load_hi hV hcur
  have hC : BytesAt st.data.dmem (r.off 22672) (r.children l (r.foldUpTo l e z) z) := by
    have eI : ∀ (a b : Sym), (Sym.ite bitC a b).eval (r.env m) =
        if bitC.eval (r.env m) then a.eval (r.env m) else b.eval (r.env m) := fun _ _ ↦ rfl
    unfold Run.children
    by_cases hb : (r.key l).leaf.toNat >>> z &&& 1 = 0
    · rw [Sym.ite_pos hb]
      have hct : bitC.eval (r.env m) = true := by rw [hbit]; exact decide_eq_true hb
      exact write_pair hm (by decide) hcur hsib wC0 wC1 wC2 wC3
        (by rw [eI, hct]; exact cLo) (by rw [eI, hct]; exact cHi)
        (by rw [eI, hct]; exact sLo) (by rw [eI, hct]; exact sHi)
    · rw [Sym.ite_neg hb]
      have hcf : bitC.eval (r.env m) = false := by rw [hbit]; exact decide_eq_false hb
      exact write_pair hm (by decide) hsib hcur wC0 wC1 wC2 wC3
        (by rw [eI, hcf]; exact sLo) (by rw [eI, hcf]; exact sHi)
        (by rw [eI, hcf]; exact cLo) (by rw [eI, hcf]; exact cHi)
  -- the registers
  have r19 : Run.RegIs st.data .X19 (BitVec.ofNat 64 (z + 1)) := by
    unfold Run.RegIs
    rw [hm.regs .X19 _ hx19]
    simp only [Sym.eval, BinOp.apply, low_W64, ext_W64, Env.ofMachine_regs]
    rw [h19, BitVec.ofNat_add]
  have r24 : Run.RegIs st.data .X24 (r.off (12468 + 16 * pathStart l)) :=
    (hm.regs .X24 _ hx24).trans (hpp ▸ eval_ptr _)
  have r20 : Run.RegIs st.data .X20 (r.off 21648) := (hm.regs .X20 _ hx20).trans (eval_ptr _)
  have r27 : Run.RegIs st.data .X27 (BitVec.ofNat 64 (l * 16777216)) :=
    (hm.regs .X27 _ hx27).trans h27
  -- the call
  refine call_then hpc hc.2.1 (r.memset_pre hpre hB1.2.1 h0 h2 (by decide)) fun st' hpc' hpost ↦ ?_
  obtain ⟨hz0, hout, hS⟩ := r.memset_out h0 h2 hpost
  have keep : ∀ x : XReg, calleeSaved x = true → ∀ v, Run.RegIs st.data x v → Run.RegIs st'.data x v :=
    fun x hx v h ↦ by unfold Run.RegIs; rw [hS.1 x hx]; exact h
  have hlen : (r.nodeAdrs l z).length = 32 := by
    rw [Run.nodeAdrs, nodeAdrs_eq]; simp [be32, be64]
  have hlenC : (r.children l (r.foldUpTo l e z) z).length = 32 := by
    unfold Run.children; split <;> simp [hcur, hsib]
  refine .done _ ⟨hpc'.trans (pc_after NativeRustcArm.Sphincs.SphincsVerify.b153_next),
    hB1.of_call hpre hS (by decide) (by decide) (by decide) hout, hz, keep .X19 rfl _ r19,
    keep .X24 rfl _ r24, keep .X20 rfl _ r20, keep .X27 rfl _ r27, ?_, ?_, ?_⟩
  · rw [h1] at hz0; exact hz0
  · exact r.bytesAt_of_call hpre hB1.2.1 (by decide) (by decide) hout (by omega) (by omega) hA
  · exact r.bytesAt_of_call hpre hB1.2.1 (by decide) (by decide) hout (by omega) (by omega) hC

/-- **`b153` and `memset`**: from the loop head to `b154`. -/
theorem nodeA (hp : Placed code r.k) (hc : Callees) (hpre : r.Pre) {l : Nat}
    {e : List (List UInt8)} {z : Nat} {m : MachineData} (h : AtNode r l e z m) :
    Eventually (step1 Host.exe) (fun st ↦ st.pc = r.pc NativeRustcArm.Sphincs.SphincsVerify.b154Offset ∧ AtN2 r l e z st.data)
      ⟨m, r.pc NativeRustcArm.Sphincs.SphincsVerify.b153Offset⟩ := by
  rcases pathStart_cases h.1.1 with hpp | hpp | hpp
  · exact nodeA_gen hp hc hpre h hpp run_b153_0 rfl rfl (by decide) (by decide) rfl rfl rfl rfl rfl rfl rfl
      (by decide) rfl rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide)
  · exact nodeA_gen hp hc hpre h hpp run_b153_8 rfl rfl (by decide) (by decide) rfl rfl rfl rfl rfl rfl rfl
      (by decide) rfl rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide)
  · exact nodeA_gen hp hc hpre h hpp run_b153_16 rfl rfl (by decide) (by decide) rfl rfl rfl rfl rfl rfl rfl
      (by decide) rfl rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide)

end

end NativeRustcArm.SphincsVerifyProof.Tree
