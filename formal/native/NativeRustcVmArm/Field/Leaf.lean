module

public import NativeRustcVmArm.Field.Frame
public import NativeRustcVmArm.Spec.Field

/-!
# Straight-line functions

`leaf_spec`: a function that is one block, run from `frameS F` to `ret`, keeping SP, the
callee-saved registers and X30 and writing only in its frame, meets the contract `StackOk m F` /
`Q m m'`, nothing changed outside the `F` bytes below SP, `Saved m m'`, for any `Q` that every
state the block's summary describes satisfies.
-/

namespace NativeRustcVmArm.Field

open NativeRustcArm NativeRustcArm.Sym

public section

theorem ofInt_natCast_eq (n : Nat) : BitVec.ofInt 64 (n : Int) = BitVec.ofNat 64 n := by
  rw [BitVec.ofInt_natCast]

variable [Host]

/-- **A straight-line function** meets its contract. -/
theorem leaf_spec {l : Label} {k F : Nat} {ds : List Directive} {S' : SState}
    (hk : ds.IsInfixAt Host.prog k) (hl : Labels.label l = Host.addrOf k) (hF : F % 16 = 0)
    (hrun : exec ds (frameS F) = some (S', .ret)) (hkeep : keeps (frameS F) S' = true)
    (h30 : (S'.reg .X30 == some (.reg .X30)) = true) (hw : ∀ w ∈ S'.mem, w.r = 0 ∧ w.off + w.n ≤ F)
    {Q : MachineData → MachineData → Prop}
    (hQ : ∀ m m', StackOk m F → Match (Env.ofMachine m [(stackBelow m F, F)]) S' m' → Q m m') :
    Spec (Labels.label l) (fun m ↦ StackOk m F) (fun m m' ↦ Q m m' ∧
      SameOutside m.dmem m'.dmem (InRange (stackBelow m F) F) ∧ Saved m m') := by
  intro m hpre
  obtain ⟨hal, hle, hmap⟩ := hpre
  have hsp : m.regs.SP.toBitVec.toNat = m.regs.SP.toNat := rfl
  have hb : (stackBelow m F).toNat = m.regs.SP.toNat - F := by
    unfold stackBelow
    rw [toNat_sub_of_le _ _ (by rw [BitVec.toNat_ofNat]; have := m.regs.SP.toNat_lt; omega),
      BitVec.toNat_ofNat, hsp, Nat.mod_eq_of_lt (by have := m.regs.SP.toNat_lt; omega)]
  have hnw : (stackBelow m F).toNat + F ≤ 2 ^ 64 := by
    rw [hb]; have := m.regs.SP.toNat_lt; omega
  let env := Env.ofMachine m [(stackBelow m F, F)]
  have hwf : env.WF := Env.wf_of ⟨⟨hmap, hnw⟩, trivial⟩ (List.pairwise_singleton _ _)
  have hm : Match env (frameS F) m :=
    match_ofMachine ⟨rfl, fun _ ↦ by rw [hb]; omega, trivial⟩
      (by
        show m.regs.SP.toBitVec = env.base 0 + BitVec.ofInt 64 (F : Int)
        rw [Env.base_ofMachine m _ _ rfl, ofInt_natCast_eq]
        exact (BitVec.sub_add_cancel _ _).symm)
      trivial trivial trivial trivial
  rw [hl]
  refine exec_then hk hrun hwf hm fun st hm' hpc' ↦ .done _ ⟨?_, hQ m st.data ⟨hal, hle, hmap⟩ hm',
    ?_, Match.saved hm hm' hwf rfl hkeep⟩
  · have h30' : st.data.regs.X30 = m.regs.X30 :=
      Match.reg_eq (r := .X30) hm hm' rfl (beq_iff_eq.mp h30)
    simp only [PcOk] at hpc'
    rw [hpc']
    simp only [retOf, h30']
  · intro p hp
    refine hm'.get?_mem0 hwf fun ⟨w, hwm, b, sz, hbs, h1, h2⟩ ↦ hp ?_
    obtain ⟨hr, hn⟩ := hw w hwm
    rw [hr] at hbs
    cases hbs
    rw [inRange_iff hnw]
    omega

end

end NativeRustcVmArm.Field
