module

public import NativeRustcVmArm.Sumcheck.Climb.Exec
public import NativeRustcVmArm.Sumcheck.Common
public import NativeRustcVmArm.Spec.Sumcheck

/-!
# `climb`'s frame and its exit

The 144-byte frame below the entry's SP (`fr`): the accumulator's four words at `0`, the sibling
at `32`, `hash_pair`'s output at `64`, the saved X30, X23, …, X19 at `96` (`slotWords`). `Frame m0 D
m`: SP at the frame, X19 the output, the accumulator `D`, the saved registers in their slots,
X24-X29 the entry's, memory changed only in `climb`'s stack. From it at `.LClimb_8`, `b10` copies
the accumulator to the output and returns (`exit_spec`).
-/

namespace NativeRustcVmArm.Sumcheck.Climb

open NativeRustcArm NativeRustcArm.Sym NativeRustcVmArm.Vm.Climb
open NativeVm.Model LeanVM.Protocol

@[expose] public section

/-- The frame's address: 144 bytes below the entry's SP. -/
def fr (m0 : MachineData) : BitVec 64 := m0.regs.SP.toBitVec - BitVec.ofNat 64 144

/-- The saved registers' words, from offset 96 of the frame. -/
def slotWords (m0 : MachineData) : List UInt64 :=
  [m0.regs.X30, m0.regs.getXReg .X23, m0.regs.getXReg .X22, m0.regs.getXReg .X21,
    m0.regs.getXReg .X20, m0.regs.getXReg .X19]

/-- The callee-saved registers `climb` does not touch. -/
def outer : List XReg := [.X24, .X25, .X26, .X27, .X28, .X29]

/-- The output's address: X0 at the entry. -/
def outAt (m0 : MachineData) : BitVec 64 := m0.regs.X0.toBitVec

/-- **The frame** with the accumulator `D`. -/
structure Frame (m0 : MachineData) (D : Digest) (m : MachineData) : Prop where
  sp : m.regs.SP.toBitVec = fr m0
  x19 : (m.regs.getXReg .X19).toBitVec = outAt m0
  acc : NativeRustcVm.WordsAt m.dmem (fr m0) D.toList
  slots : NativeRustcVm.WordsAt m.dmem (fr m0 + BitVec.ofNat 64 96) (slotWords m0)
  regs : ∀ r ∈ outer, m.regs.getXReg r = m0.regs.getXReg r
  same : SameOutside m0.dmem m.dmem (InRange (stackBelow m0 climbStack) climbStack)
  kept : Kept m0.dmem m.dmem

end

public section

theorem climbStack_eq : climbStack = 912 := rfl

variable [Host] {N : Digest} {P : Array Digest} {m0 : MachineData}

/-- The entry's SP, its frame and the output as numbers. -/
structure Geo (m0 : MachineData) : Prop where
  al : m0.regs.SP.toNat % 16 = 0
  le : 912 ≤ m0.regs.SP.toNat
  lt : m0.regs.SP.toNat < 2 ^ 64
  fr : (fr m0).toNat = m0.regs.SP.toNat - 144
  stk : (stackBelow m0 climbStack).toNat = m0.regs.SP.toNat - 912
  out : (outAt m0).toNat + 32 ≤ m0.regs.SP.toNat - 912 ∨ m0.regs.SP.toNat ≤ (outAt m0).toNat
  outNw : (outAt m0).toNat + 32 ≤ 2 ^ 64

theorem geo_of (h : ClimbPre N P m0) : Geo m0 := by
  obtain ⟨⟨hal, hle, -⟩, -, -, -, -, -, -, -, -, hon, -, -, hos, -⟩ := h
  have hs : m0.regs.SP.toNat = m0.regs.SP.toBitVec.toNat := rfl
  have hlt := m0.regs.SP.toBitVec.isLt
  have hstk : (stackBelow m0 climbStack).toNat = m0.regs.SP.toNat - 912 :=
    NativeRustcVm.toNat_sub_ofNat (by rw [← hs]; exact hle)
  rw [climbStack_eq] at hle
  refine ⟨hal, hle, by omega, NativeRustcVm.toNat_sub_ofNat (by omega), hstk, ?_, hon⟩
  unfold Apart at hos
  rw [hstk, climbStack_eq] at hos
  show m0.regs.X0.toBitVec.toNat + 32 ≤ _ ∨ _ ≤ m0.regs.X0.toBitVec.toNat
  omega

omit [Host] in
/-- The frame is in `climb`'s stack. -/
theorem fr_inRange (g : Geo m0) {p : BitVec 64} (h : InRange (fr m0) 144 p) :
    InRange (stackBelow m0 climbStack) climbStack p := by
  have ⟨_, _, _, _, _, _, _⟩ := g
  rw [Sym.inRange_iff (by rw [g.fr]; omega)] at h
  rw [Sym.inRange_iff (by rw [g.stk, climbStack_eq]; omega),
    g.stk, climbStack_eq]
  rw [g.fr] at h
  omega

/-- The frame's bytes are memory. -/
theorem mapped_fr (h : ClimbPre N P m0) {m : MachineData} (hk : Kept m0.dmem m.dmem) :
    Mapped m.dmem (fr m0) 144 := by
  have g := geo_of h
  have ⟨_, _, _, _, _, _, _⟩ := g
  obtain ⟨⟨-, -, hmap⟩, -⟩ := h
  intro i hi
  apply hk
  have : fr m0 + BitVec.ofNat 64 i =
      m0.regs.SP.toBitVec - BitVec.ofNat 64 climbStack + BitVec.ofNat 64 (768 + i) := by
    apply BitVec.eq_of_toNat_eq
    have e := g.stk
    unfold stackBelow at e
    rw [NativeRustcVm.toNat_add_ofNat (by rw [g.fr]; omega),
      NativeRustcVm.toNat_add_ofNat (by rw [e]; omega), g.fr, e]
    omega
  rw [this]
  exact hmap _ (by rw [climbStack_eq]; omega)

omit [Host] in
/-- The output is apart from the frame. -/
theorem apart_out_fr (g : Geo m0) : Apart (fr m0) 144 (outAt m0) 32 := by
  have ⟨_, _, _, _, _, _, _⟩ := g
  unfold Apart
  rw [g.fr]
  omega

omit [Host] in
/-- Digest `l` of a path's words. -/
theorem wordsAt_path {d : Mem 64} {a : BitVec 64} (h : NativeRustcVm.WordsAt d a (pathWords P))
    {l : Nat} (hl : l < P.size) :
    NativeRustcVm.WordsAt d (a + BitVec.ofNat 64 (32 * l)) P[l].toList := by
  unfold NativeRustcVm.WordsAt pathWords at *
  rw [List.flatMap_assoc] at h
  have := NativeRustcVm.BytesAt.flatMap_getElem
    (f := fun D : Digest ↦ D.toList.flatMap NativeRustcVm.wordBytes) (k := 32)
    (fun D ↦ by rw [NativeRustcVm.length_wordsBytes]; simp) h (i := l) (by simpa using hl)
  simpa using this

omit [Host] in
theorem slot_word {D : Digest} {m : MachineData} (hf : Frame m0 D m) (i : Nat) (hi : i < 6) :
    NativeRustcVm.WordAt m.dmem (fr m0 + BitVec.ofNat 64 (96 + 8 * i)) ((slotWords m0)[i]'(by
      simp [slotWords]; omega)) := by
  have := hf.slots.getElem (i := i) (by simp [slotWords]; omega)
  rwa [NativeRustcVm.addr_add_add] at this

variable {k : Nat}

/-- **The exit**: the accumulator copied to the output, the registers restored, `ret`. -/
theorem exit_spec (hp : Placed code k) (hpre : ClimbPre N P m0) {D : Digest} {m : MachineData}
    (hf : Frame m0 D m) :
    Eventually (step1 Host.exe)
      (fun st ↦ st.pc = retOf m0 ∧ NativeRustcVm.WordsAt st.data.dmem (outAt m0) D.toList ∧
        SameOutside m0.dmem st.data.dmem (fun p ↦ InRange (outAt m0) 32 p ∨
          InRange (stackBelow m0 climbStack) climbStack p) ∧ Saved m0 st.data)
      ⟨m, Host.addrOf (k + NativeRustcVmArm.Vm.Climb.b10Offset)⟩ := by
  have g := geo_of hpre
  have ⟨_, _, _, _, _, _, _⟩ := g
  have hk : b10.IsInfixAt Host.prog (k + NativeRustcVmArm.Vm.Climb.b10Offset) := b10_in_code.trans hp.1 (by simp [b10])
  let env := Env.ofMachine m [(fr m0, 144), (outAt m0, 32)]
  have hmo : Mapped m.dmem (outAt m0) 32 := fun i hi ↦ hf.kept _ (hpre.2.2.2.2.2.2.2.2.1 i hi)
  have hwf : env.WF :=
    Env.wf_of ⟨⟨mapped_fr hpre hf.kept, by show _ + 144 ≤ _; rw [g.fr]; omega⟩,
      ⟨hmo, g.outNw⟩, trivial⟩
      (List.Pairwise.cons (by simpa using apart_out_fr g) (List.pairwise_singleton _ _))
  have hm : Match env exitS m :=
    match_ofMachine ⟨rfl, fun _ ↦ by rw [g.fr]; omega, rfl, by simp, trivial⟩
      (by simp [Sym.eval, hf.sp]) ⟨by simp [Sym.eval, hf.x19], trivial⟩ trivial
      trivial trivial
  have hb0 : env.base 0 = fr m0 := rfl
  have hb1 : env.base 1 = outAt m0 := rfl
  have hslot : ∀ i (hi : i < 6),
      env.load 0 (96 + 8 * i) 8 = ((slotWords m0)[i]'(by simp [slotWords]; omega)).toBitVec :=
    fun i hi ↦ load_word (by rw [hb0]; exact slot_word hf i hi)
  have hacc : ∀ i (hi : i < 4), env.load 0 (8 * i) 8 = (D.toList[i]'(by simpa using hi)).toBitVec :=
    fun i hi ↦ load_word (by
      rw [hb0]
      exact hf.acc.getElem (i := i) (by simpa using hi))
  refine exec_then hk run_b10 hwf hm fun st hm' hpc ↦ ?_
  have hmA : Match env (after b10 exitS) st.data := by rw [after_eq run_b10]; exact hm'
  have hslotR : ∀ (r : XReg) (i : Nat) (hi : i < 6),
      (after b10 exitS).reg r = some (.load 0 (96 + 8 * i) 8) →
      st.data.regs.getXReg r = (slotWords m0)[i]'(by simp [slotWords]; omega) :=
    fun r i hi hr ↦ UInt64.toBitVec_inj.mp ((hmA.regs r _ hr).trans (hslot i hi))
  have hkeep : ∀ r ∈ outer, st.data.regs.getXReg r = m0.regs.getXReg r := by
    intro r hr
    rw [← hf.regs r hr]
    apply UInt64.toBitVec_inj.mp
    refine (hmA.regs r (.reg r) ?_).trans rfl
    simp only [outer, List.mem_cons, List.not_mem_nil, or_false] at hr
    rw [after_eq run_b10]
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
  have r30 := hslotR .X30 0 (by decide) (by rw [after_eq run_b10]; rfl)
  refine Eventually.done _ ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hpc]
    simp only [retOf]
    rw [show st.data.regs.X30 = st.data.regs.getXReg .X30 from rfl, r30]
    rfl
  · rw [NativeRustcVm.wordsAt_iff]
    intro i hi
    have hD : D.toList.length = 4 := by simp
    rw [hD] at hi
    have hw : ∀ i < 4, ∀ j < 8,
        findWrite 1 (8 * i + j) (after b10 exitS).mem = some (.load 0 (8 * i) 8, j) := by
      rw [after_eq run_b10]; decide
    have := NativeRustcVmArm.Sumcheck.Match.wordAt_write hmA (r := 1) (o := 8 * i) rfl (by omega) (hw i hi)
    rw [show (Sym.load 0 (8 * i) 8).eval env = env.load 0 (8 * i) 8 from rfl, hacc i hi] at this
    exact this
  · intro p hpn
    rw [hm'.get?_mem0 hwf fun hw ↦ hpn (Or.inl (Written.inRange (r := 1) rfl g.outNw
      (by decide) hw))]
    exact hf.same p fun h' ↦ hpn (Or.inr h')
  · intro r hr
    cases r <;> simp [calleeSaved] at hr
    · exact hslotR .X19 5 (by decide) (by rw [after_eq run_b10]; rfl)
    · exact hslotR .X20 4 (by decide) (by rw [after_eq run_b10]; rfl)
    · exact hslotR .X21 3 (by decide) (by rw [after_eq run_b10]; rfl)
    · exact hslotR .X22 2 (by decide) (by rw [after_eq run_b10]; rfl)
    · exact hslotR .X23 1 (by decide) (by rw [after_eq run_b10]; rfl)
    all_goals exact hkeep _ (by simp [outer])
  · apply UInt64.toBitVec_inj.mp
    rw [hm'.sp]
    simp only [Sym.eval, hb0, fr]
    simp
  · exact fun p hp ↦ hm'.kept hwf p (hf.kept p hp)

end

end NativeRustcVmArm.Sumcheck.Climb
