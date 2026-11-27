module

public import NativeRustcArm.SphincsVerify.Tree.NodeE
public import NativeRustcArm.SphincsVerify.Tree.Leaf2
public import NativeRustcArm.SphincsVerify.Compose

/-!
# The fold

A node (`node`: `nodeA` .. `nodeH`), the loop over the heights (`fold`, by `Sym.loop` on the
heights left), its entry from the one-time leaf's hash (`b140` .. `b143`: the path's slice
checks, the loop's registers; `entry`), and the region from layer `l`'s chain ends to the fold's
end (`toFold`).
-/

namespace NativeRustcArm.SphincsVerifyProof.Tree

open NativeRustc NativeRustc.Keccak NativeRustc.Sphincs NativeRustcArm.Sym NativeRustcArm
  LeanVM.Protocol.KeccakHash Native.Keccak
open NativeRustcArm.Sphincs.SphincsVerify

public section

variable [ElfHost] {r : Run}

/-- **A node of the fold**: from the loop head with `z` steps done, the loop head with `z + 1`
or, after the last, the fold's end. -/
theorem node (hp : PlacedIn code r.sec r.k) (hc : Callees) (hpre : r.Pre) {l : Nat}
    {e : List (List UInt8)} {z : Nat} {m : MachineData} (h : AtNode r l e z m) :
    Eventually (elfStep1 ElfHost.exe) (fun st ↦ (z + 1 < heightOf l ∧ st.pc = r.pc NativeRustcArm.Sphincs.SphincsVerify.b144Offset ∧
      AtNode r l e (z + 1) st.data) ∨ (z + 1 = heightOf l ∧ st.pc = r.pc NativeRustcArm.Sphincs.SphincsVerify.b170Offset ∧ AtFold r l e st.data))
      ⟨m, r.pc NativeRustcArm.Sphincs.SphincsVerify.b144Offset⟩ :=
  Eventually.bind_elf (nodeA hp hc hpre h) <| at_pc fun _ h ↦
  Eventually.bind_elf (nodeB hp hc hpre h) <| at_pc fun _ h ↦
  Eventually.bind_elf (nodeC hp hc hpre h) <| at_pc fun _ h ↦
  Eventually.bind_elf (nodeD hp hc hpre h) <| at_pc fun _ h ↦
  Eventually.bind_elf (nodeE hp hc hpre h) <| at_pc fun _ h ↦
  Eventually.bind_elf (nodeF hp hc hpre h) <| at_pc fun _ h ↦
  Eventually.bind_elf (nodeG hp hc hpre h) <| at_pc fun _ h ↦ nodeH hp hpre h

/-- **The fold's loop**: from the loop head with no step done to the fold's end. -/
theorem fold (hp : PlacedIn code r.sec r.k) (hc : Callees) (hpre : r.Pre) {l : Nat}
    {e : List (List UInt8)} {m : MachineData} (h : AtNode r l e 0 m) :
    Eventually (elfStep1 ElfHost.exe) (fun st ↦ st.pc = r.pc NativeRustcArm.Sphincs.SphincsVerify.b170Offset ∧ AtFold r l e st.data)
      ⟨m, r.pc NativeRustcArm.Sphincs.SphincsVerify.b144Offset⟩ := by
  refine Sym.loop (fun n st ↦ ∃ z, z + n = heightOf l ∧ st.pc = r.pc NativeRustcArm.Sphincs.SphincsVerify.b144Offset ∧ AtNode r l e z st.data)
    (fun n st ⟨z, hn, hpc, hz⟩ ↦ ?_) (n := heightOf l) ⟨0, by omega, rfl, h⟩
  refine Eventually.mono_elf (at_pc (fun m h ↦ node hp hc hpre h) st ⟨hpc, hz⟩) fun st' h' ↦ ?_
  rcases h' with ⟨hlt, hpc', h'⟩ | ⟨-, hpc', h'⟩
  · exact Or.inr ⟨n - 1, by omega, z + 1, by omega, hpc', h'⟩
  · exact Or.inl ⟨hpc', h'⟩

end

end NativeRustcArm.SphincsVerifyProof.Tree
