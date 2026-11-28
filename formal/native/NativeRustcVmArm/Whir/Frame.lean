module

public import NativeRustcVmArm.Ring.Frame
public import NativeRustcVmArm.Whir.Common

/-!
# Checking a block's writes against the frame

`NativeRustcVmArm.Ring.Fr.ofBlockW` carries a function's frame across a block whose writes are in
the frame (not its slots) or in regions inside the outputs (`WriteOk`). `frameWrites S F slots wr`
checks on the literal state that every write is in region `0` below `F` apart from the slots, or
in one of the regions `wr`; `writeOk_of` turns it into `WriteOk` given that those regions are
outputs.
-/

namespace NativeRustcVmArm.Whir

open NativeRustcArm NativeRustcArm.Sym NativeRustcVmArm.Ring

@[expose] public section

/-- Every write is in region `0` below `F` apart from the slots, or in a region of `wr` within
its size. -/
def frameWrites (S : SState) (F : Nat) (slots : List (Nat × XReg)) (wr : List Nat) : Bool :=
  S.mem.all fun w ↦
    (w.r == 0 && decide (w.off + w.n ≤ F) &&
      slots.all fun p ↦ decide (w.off + w.n ≤ p.1) || decide (p.1 + 8 ≤ w.off)) ||
    (wr.contains w.r && w.r != 0 && match S.regions[w.r]? with
      | some (sz, _) => decide (w.off + w.n ≤ sz)
      | none => false)

end

public section

variable [Labels]

/-- **`frameWrites` gives `WriteOk`**, the regions `wr` being outputs. -/
theorem writeOk_of {env : Env} {S : SState} {m : MachineData} (hm : Match env S m) {F : Nat}
    {slots : List (Nat × XReg)} {wr : List Nat} {outs : BitVec 64 → Prop}
    (hw : frameWrites S F slots wr = true)
    (hwr : ∀ r ∈ wr, ∀ b sz, env.regions[r]? = some (b, sz) → ∀ i < sz,
      outs (b + BitVec.ofNat 64 i)) :
    ∀ w ∈ S.mem, WriteOk env F slots outs w := by
  intro w hwm
  unfold WriteOk
  simp only [frameWrites, List.all_eq_true] at hw
  have := hw w hwm
  simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq,
    List.all_eq_true, bne_iff_ne, ne_eq] at this
  rcases this with ⟨⟨hr, hle⟩, hs⟩ | ⟨⟨hc, hr⟩, hsz⟩
  · exact Or.inl ⟨hr, hle, fun p hp ↦ by simpa using hs p hp⟩
  · refine Or.inr ⟨hr, fun b sz hb ↦ ⟨?_, hwr w.r (by simpa using hc) b sz hb⟩⟩
    split at hsz
    · rename_i sz' al hreg
      obtain ⟨b', hb', -⟩ := hm.regions _ _ _ hreg
      rw [hb] at hb'
      cases hb'
      simpa using hsz
    · cases hsz

end

end NativeRustcVmArm.Whir
