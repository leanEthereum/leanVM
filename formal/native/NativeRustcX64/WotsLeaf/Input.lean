module

public import NativeRustcX64.WotsLeaf.Steps

/-!
# The inputs and the words of the frame

`wots_leaf`'s inputs (the public parameter, the message, the randomizer, the chain values) and
its output are apart from the stack area, the return address and the stack arguments
(`WotsLeafPre.Input`): in any state of the frame they hold their bytes at entry
(`Run.input_bytes`) and, as extra regions of the executor, are apart from the frame's two
(`Run.extraOK_input`). A word the frame holds as a register's bytes loads as the register's value
(`Run.load_word`); the stack arguments load as the randomizer's and the chain values' addresses
(`Run.load_rndPtr`, `Run.load_valuesPtr`).
-/

namespace NativeRustcX64.WotsLeafProof

open NativeRustc NativeRustcX64.Sym

public section

namespace Run

variable (r : Run) [Labels]

theorem pre_out (hpre : r.Pre) : WotsLeafPre.Input r.m0 r.out 75 := hpre.2.2.2.2.1
theorem pre_pp (hpre : r.Pre) : WotsLeafPre.Input r.m0 (reg r.m0 .rsi) 16 := hpre.2.2.2.2.2.1
theorem pre_msg (hpre : r.Pre) :
    WotsLeafPre.Input r.m0 (reg r.m0 .r8) (reg r.m0 .r9).toNat := hpre.2.2.2.2.2.2.1
theorem pre_rnd (hpre : r.Pre) : WotsLeafPre.Input r.m0 (WotsLeafPre.rndPtr r.m0) 16 :=
  hpre.2.2.2.2.2.2.2.1
theorem pre_values (hpre : r.Pre) :
    WotsLeafPre.Input r.m0 (WotsLeafPre.valuesPtr r.m0) (16 * 58) := hpre.2.2.2.2.2.2.2.2.1

omit [Labels] in
/-- A part of an input is an input. -/
theorem Input.sub {b : BitVec 64} {n : Nat} (h : WotsLeafPre.Input r.m0 b n) {o n' : Nat}
    (ho : o + n' ≤ n) (hn : o < n) : WotsLeafPre.Input r.m0 (b + BitVec.ofNat 64 o) n' := by
  obtain ⟨hm, hw, ha⟩ := h
  unfold NoWrap Apart at *
  have hb : (b + BitVec.ofNat 64 o).toNat = b.toNat + o := Sym.toNat_add_ofNat _ _ (by omega)
  refine ⟨fun i hi ↦ ?_, by unfold NoWrap; rw [hb]; omega, by unfold Apart; rw [hb]; omega⟩
  rw [addr_add_add]
  exact hm _ (by omega)

/-- **An input's bytes** in any state of the frame are its bytes at entry. -/
theorem input_bytes (hpre : r.Pre) {sp : BitVec 64} {m : MachineData} (hF : r.FrameAt sp m)
    {b : BitVec 64} {n : Nat} (h : WotsLeafPre.Input r.m0 b n) :
    BytesAt m.dmem b (bytesOf r.m0.dmem b n) := by
  have hl := length_bytesOf r.m0.dmem b n
  exact r.bytesAt_entry hpre hF (bytesAt_bytesOf h.1) (by rw [hl]; exact r.input_apart h)
    (by rw [hl]; exact h.2.1)

/-- An input is apart from the frame's two regions. -/
theorem apart_regions (hpre : r.Pre) {b : BitVec 64} {n : Nat} (h : WotsLeafPre.Input r.m0 b n) :
    Apart r.base regionSize b n ∧ Apart (r.base - 8#64) 8 b n := by
  have := r.below_toNat hpre
  have := r.callSp_toNat hpre
  have := r.base_top hpre
  have ha := h.2.2
  unfold Apart regionSize at *
  simp only [wotsLeafStack_eq'] at *
  omega

/-- **An input as the executor's extra region.** -/
theorem extraOK_input (hpre : r.Pre) {m : MachineData} (hk : Kept r.m0.dmem m.dmem) {b : BitVec 64}
    {n : Nat} (h : WotsLeafPre.Input r.m0 b n)
    (hg : ∀ l ∈ ["memcpy", "memset"], Apart (gotAddr l) 8 b n) : ExtraOK r m [(b, n)] :=
  ⟨⟨⟨fun i hi ↦ hk _ (h.1 i hi), h.2.1⟩, trivial⟩, ⟨r.apart_regions hpre h, trivial⟩,
    List.pairwise_singleton _ _, by
      intro l hl e he
      simp only [List.mem_singleton] at he
      subst e
      exact hg l hl⟩

/-- **A word the frame holds as a value's bytes** loads as the value. -/
theorem load_word {m : MachineData} {extra : List (BitVec 64 × Nat)} {ret : BitVec 64} {o : Nat}
    {v : BitVec 64} (h : BytesAt m.dmem (r.off o) ((List.range 8).map (byteOf v))) :
    (r.envR m extra ret).load 0 o 8 = v := by
  rw [Env.load_of_bytesAt (by simp) h]
  have hb := Sym.ofBytes_byteOf v 0 8
  simp only [Nat.zero_add, Nat.mul_zero, Nat.pow_zero, Nat.div_one] at hb
  rw [hb, BitVec.ofInt_natCast]
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ofNat]
  have := v.isLt
  omega

/-- The frame's byte `2768`: RSP + 8 at the entry. -/
theorem off_args (hpre : r.Pre) : r.off 2768 = rspOf r.m0 + 8#64 := by
  have hb := r.base_toNat hpre
  have ho := r.off_toNat hpre (a := 2768) (by decide)
  apply BitVec.eq_of_toNat_eq
  rw [ho, show (8#64) = BitVec.ofNat 64 8 from rfl, Sym.toNat_add_ofNat _ _ (by omega)]
  omega

/-- A stack argument in a state of the frame: the pointer at entry. -/
theorem load_arg (hpre : r.Pre) {m : MachineData} (hs : SameOutside r.m0.dmem m.dmem r.Changed)
    {extra : List (BitVec 64 × Nat)} {ret : BitVec 64} {o : Nat} (h1 : 2760 ≤ o) (h2 : o + 8 ≤ 2784) :
    (r.envR m extra ret).load 0 o 8 = ptrAt r.m0.dmem (r.off o) := by
  have hB := r.bytesAt_top hpre hs (a := o) (n := 8) (by omega) h2
  rw [Env.load_of_bytesAt (length_bytesOf _ _ _) hB, ptrAt,
    Sym.loadInt_of_get? _ _ 8 (fun i ↦ (r.m0.dmem.get? (r.off o + BitVec.ofNat 64 i)).getD 0)]
  · rfl
  · intro i hi
    have := (r.frame_mapped_kept hpre (fun _ h ↦ h) (a := o) (n := 8) h2).1 i hi
    revert this
    cases r.m0.dmem.get? (r.off o + BitVec.ofNat 64 i) <;> simp

/-- The randomizer's address, the stack argument at `2768`. -/
theorem load_rndPtr (hpre : r.Pre) {m : MachineData}
    (hs : SameOutside r.m0.dmem m.dmem r.Changed)
    {extra : List (BitVec 64 × Nat)} {ret : BitVec 64} :
    (r.envR m extra ret).load 0 2768 8 = WotsLeafPre.rndPtr r.m0 := by
  rw [r.load_arg hpre hs (by decide) (by decide), r.off_args hpre]
  rfl

/-- The chain values' address, the stack argument at `2776`. -/
theorem load_valuesPtr (hpre : r.Pre) {m : MachineData}
    (hs : SameOutside r.m0.dmem m.dmem r.Changed)
    {extra : List (BitVec 64 × Nat)} {ret : BitVec 64} :
    (r.envR m extra ret).load 0 2776 8 = WotsLeafPre.valuesPtr r.m0 := by
  rw [r.load_arg hpre hs (by decide) (by decide)]
  have : r.off 2776 = rspOf r.m0 + 16#64 := by
    rw [show (2776 : Nat) = 2768 + 8 from rfl, ← off_add, r.off_args hpre]
    rw [BitVec.add_assoc]
    rfl
  rw [this]
  rfl

end Run

end

end NativeRustcX64.WotsLeafProof
