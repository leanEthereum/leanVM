module

public import NativeRustcVmX64.Wire.ClimbLevel.Read
public import NativeRustcVmX64.Code.Vm.HashPair.Names
public import NativeRustcVmX64.Code.Vm.ReaderDigest.Names

/-!
# `climb_level`'s loop over the nodes (x86-64)

The scan for node `i`'s sibling to its end (`scan_spec`): read or found; node `i`'s step from the
loop's head (`node_spec`): its sibling and parent, then the next node's check; the loop
(`loop_spec`).
-/

namespace NativeRustcVmX64.Wire.ClimbLevel

open NativeRustcX64 NativeRustcX64.Sym NativeRustcVm.Wire NativeVm.Wire
open NativeRustcVmX64.Vm.ClimbLevel
open LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.Compile

public section

variable [Host] {k : Nat} {m0 : MachineData} {bp : BitVec 64} {B : List UInt8} {c : Nat}
  {ns : List (Nat × Digest)}

section
variable (hp : Placed code k) (g : Geo m0 bp B.length) (hl : ns.length = cnt m0)
include hp g hl

/-- **The scan** for node `i`'s sibling from node `j`: read, or found. -/
theorem scan_spec {i : Nat} {sl : List (Nat × Digest × Bool)} {ci j : Nat} {st : MachineState}
    (hS : Scan k m0 bp B c ns i sl ci j st) :
    Eventually (step1 Host.exe) (fun st' ↦ Rd k m0 bp B c ns i sl ci st' ∨
      ∃ j', Fnd k m0 bp B c ns i sl ci j' st') st := by
  refine Sym.loop (fun n st ↦ ∃ j, n = cnt m0 - j ∧ Scan k m0 bp B c ns i sl ci j st)
    (fun n st ⟨j, hn, hS⟩ ↦ ?_) ⟨j, rfl, hS⟩
  refine Eventually.mono (scan_step hp g hl hS) fun st' h ↦ ?_
  rcases h with h | h | h
  · exact .inl (.inl h)
  · exact .inl (.inr h)
  · exact .inr ⟨_, by have := h.le; omega, j + 1, rfl, h⟩

variable (hh : Spec (Labels.label NativeRustcVmX64.Vm.HashPair.entryLabel) HashPairPre HashPairPost)
  (hd : Spec (Labels.label NativeRustcVmX64.Vm.ReaderDigest.entryLabel) ReaderDigestPre ReaderDigestPost)
  (hR : ReaderAt m0.dmem (rdr m0) bp B c) (hns : NodesAt m0.dmem (nodes m0) ns)
include hh hd hR hns

/-- **Node `i`'s step** from the loop's head: the return, or the loop's head after `i + 1`
nodes. -/
theorem node_spec {i : Nat} {sl : List (Nat × Digest × Bool)} {ci : Nat} {st : MachineState}
    (hH : Head k m0 bp B c ns i sl ci st) :
    Eventually (step1 Host.exe) (fun st' ↦ Post m0 st' ∨
      ∃ sl' ci', Head k m0 bp B c ns (i + 1) sl' ci' st') st := by
  have hN : ∀ st', (∃ sl' ci', Nxt k m0 bp B c ns (i + 1) sl' ci' st') →
      Eventually (step1 Host.exe) (fun st' ↦ Post m0 st' ∨
        ∃ sl' ci', Head k m0 bp B c ns (i + 1) sl' ci' st') st' := fun st' ⟨sl', ci', h⟩ ↦
    Eventually.mono (nxt_step hp g hl hR hns h) fun _ h ↦ h.imp_right fun h ↦ ⟨sl', ci', h⟩
  refine Eventually.bind (head_step hp g hl hH) fun s1 h1 ↦ ?_
  refine Eventually.bind (scan_spec hp g hl h1) fun s2 h2 ↦ ?_
  rcases h2 with h2 | ⟨j, h2⟩
  · refine Eventually.bind (read_spec hp g hl hh hd hR hns h2) fun s3 h3 ↦ ?_
    rcases h3 with h3 | h3
    · exact .done _ (.inl h3)
    · exact hN s3 h3
  · exact Eventually.bind (found_spec hp g hl hh h2) hN

/-- **The loop** from its head after `i` nodes. -/
theorem loop_spec {i : Nat} {sl : List (Nat × Digest × Bool)} {ci : Nat} {st : MachineState}
    (hH : Head k m0 bp B c ns i sl ci st) : Eventually (step1 Host.exe) (Post m0) st := by
  refine Sym.loop (fun n st ↦ ∃ i sl ci, n = cnt m0 - i ∧ Head k m0 bp B c ns i sl ci st)
    (fun n st ⟨i, sl, ci, hn, hH⟩ ↦ ?_) ⟨i, sl, ci, rfl, hH⟩
  refine Eventually.mono (node_spec hp g hl hh hd hR hns hH) fun st' h ↦ ?_
  rcases h with h | ⟨sl', ci', h⟩
  · exact .inl h
  · exact .inr ⟨_, by have := h.lt; omega, i + 1, sl', ci', rfl, h⟩

end

end

end NativeRustcVmX64.Wire.ClimbLevel
