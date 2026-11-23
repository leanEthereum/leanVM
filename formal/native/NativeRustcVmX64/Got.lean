module

public import NativeRustcVmX64.Basic
public import NativeRustcX64.Got

/-!
# GOT regions in VM symbolic environments

The loader's slots remain ordinary memory. Their separation from a caller's areas supplies
well-formed appended symbolic regions and the geometry of callees' smaller areas.
-/

namespace NativeRustcVmX64

open NativeRustcX64 NativeRustcX64.Sym

public section

variable [Labels]

theorem GotAt.unchanged_vm {m d : MachineData} {n : Nat}
    {areas : List (BitVec 64 × Nat)} {symbols : List Label}
    (h : NativeRustcX64.GotAt m n areas symbols) (hstack : StackOk m n)
    (hareas : ∀ a ∈ areas, NativeRustcVm.NoWrap a.1 a.2)
    (hsame : NativeRustcVm.SameOutside m.dmem d.dmem (fun p =>
      NativeRustcVm.InRange (stackBelow m n) n p ∨
        ∃ a ∈ areas, NativeRustcVm.InRange a.1 a.2 p)) :
    ∀ l ∈ symbols, ∀ i < 8,
      d.dmem.get? (gotAddr l + BitVec.ofNat 64 i) =
        m.dmem.get? (gotAddr l + BitVec.ofNat 64 i) := by
  apply NativeRustcX64.GotAt.unchanged h hstack
  · intro a ha
    exact noWrap_iff.mpr (hareas a ha)
  · simpa only [sameOutside_iff, inRange_iff, stackBelow] using hsame

/-- Stack-only writes preserve the loader slots without hypotheses on unrelated areas. -/
theorem GotAt.unchanged_stack {m d : MachineData} {n : Nat}
    {areas : List (BitVec 64 × Nat)} {symbols : List Label}
    (h : GotAt m n areas symbols) (hst : StackOk m n)
    (hs : SameOutside m.dmem d.dmem (InRange (stackBelow m n) n)) :
    ∀ l ∈ symbols, ∀ i < 8,
      d.dmem.get? (gotAddr l + BitVec.ofNat 64 i) =
        m.dmem.get? (gotAddr l + BitVec.ofNat 64 i) := by
  apply (h.areas (areas' := []) (by simp)).unchanged hst (by simp)
  intro p hp
  exact hs p (fun hin => hp (Or.inl hin))

/-- Append the known loader slots to already separated ordinary-memory regions. -/
theorem GotAt.regions_wf {m : MachineData} {n : Nat}
    {areas regions : List (BitVec 64 × Nat)} {symbols : List Label}
    (h : GotAt m n areas symbols)
    (hok : ∀ a ∈ regions, Mapped m.dmem a.1 a.2 ∧ NoWrap a.1 a.2)
    (hpair : regions.Pairwise fun a b => Apart a.1 a.2 b.1 b.2)
    (hap : ∀ l ∈ symbols, ∀ a ∈ regions, Apart (gotAddr l) 8 a.1 a.2)
    (vars : Nat → BitVec 64 := fun _ => 0) (ret : BitVec 64 := 0) :
    (Env.ofMachine m (regions ++ symbols.map (fun l => (gotAddr l, 8))) vars ret).WF := by
  apply Env.wf_of
  · have hall : ∀ a ∈ regions ++ symbols.map (fun l => (gotAddr l, 8)),
        Mapped m.dmem a.1 a.2 ∧ NoWrap a.1 a.2 := by
      intro a ha
      rcases List.mem_append.mp ha with ha | ha
      · exact hok a ha
      · obtain ⟨l, hl, rfl⟩ := List.mem_map.mp ha
        exact ⟨h.mapped hl, (h.1 l hl).2.1⟩
    generalize regions ++ symbols.map (fun l => (gotAddr l, 8)) = rs at hall ⊢
    induction rs with
    | nil => trivial
    | cons a rs ih =>
      exact ⟨hall a (by simp), ih (fun b hb => hall b (by simp [hb]))⟩
  · change List.Pairwise (fun a b : BitVec 64 × Nat => Apart a.1 a.2 b.1 b.2)
      (regions ++ symbols.map (fun l => (gotAddr l, 8)))
    rw [List.pairwise_append]
    refine ⟨hpair, ?_, ?_⟩
    · simpa only [List.pairwise_map] using h.2
    · intro a ha b hb
      obtain ⟨l, hl, rfl⟩ := List.mem_map.mp hb
      exact (hap l hl a ha).symm

/-- A callee may protect subranges of the caller's stack and protected areas. -/
theorem GotAt.callee {m d : MachineData} {n n' : Nat}
    {areas areas' : List (BitVec 64 × Nat)} {symbols : List Label}
    (h : GotAt m n areas symbols)
    (hbytes : ∀ l ∈ symbols, ∀ i < 8,
      d.dmem.get? (gotAddr l + BitVec.ofNat 64 i) =
        m.dmem.get? (gotAddr l + BitVec.ofNat 64 i))
    (hlo : (stackBelow m n).toNat ≤ (stackBelow d n').toNat)
    (hhi : (stackBelow d n').toNat + (n' + 8) ≤ (stackBelow m n).toNat + (n + 8))
    (hcover : ∀ a ∈ areas', ∃ b ∈ (stackBelow m n, n + 8) :: areas,
      b.1.toNat ≤ a.1.toNat ∧ a.1.toNat + a.2 ≤ b.1.toNat + b.2) :
    GotAt d n' areas' symbols := by
  apply h.transport hbytes
  · intro l hl
    exact NativeRustcVm.Apart.mono_right (h.1 l hl).2.2.1 hlo hhi
  · intro l hl a ha
    obtain ⟨b, hb, hlo, hhi⟩ := hcover a ha
    apply NativeRustcVm.Apart.mono_right (x := b.1) (N := b.2) _ hlo hhi
    rcases List.mem_cons.mp hb with rfl | hb
    · exact (h.1 l hl).2.2.1
    · exact (h.1 l hl).2.2.2 b hb

end

end NativeRustcVmX64
