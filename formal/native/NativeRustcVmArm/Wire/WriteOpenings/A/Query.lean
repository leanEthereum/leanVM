module

public import NativeRustcVmArm.Code.Vm.Find.Names
public import NativeRustcVmArm.Wire.WriteOpenings.A.Chunk
public import NativeRustcVmArm.Wire.WriteOpenings.A.Next

/-!
# `write_openings`' queries' loop (`h > 0`)

Query `j` found: its leaf copied, the first level (`copy_step`). From the queries' loop head
(`HeadA`): the query stored, found, copied, its levels, the next query; at last the epilogue
(`query_loop`).
-/

namespace NativeRustcVmArm.Wire.WriteOpenings

open NativeRustcArm NativeRustcArm.Sym NativeRustcVm.Wire NativeVm.Wire
open NativeRustcVmArm.Vm.WriteOpenings

public section

variable {R : Run} [Host]

/-- **The leaf copied**, from the query's position. -/
theorem copy_step (hp : Placed code R.k) (G : Geo R) {j i : Nat} {st : MachineState}
    (H : FoundA R j i st) : Eventually (step1 Host.exe) (LevA R j 0) st := by
  have rem : ∀ {t : Nat} {s : MachineState}, AtB11 R j i t s →
      Eventually (step1 Host.exe) (LevA R j 0) s := fun h ↦
    eventually_trans _ _ _ _ (b11_step hp G h) fun _ h3 ↦
      eventually_trans _ _ _ _ (rem_loop hp G h3) fun _ h4 ↦ b13_step hp G h4
  refine eventually_trans _ _ _ _ (found_step hp G H) fun s1 h1 ↦ ?_
  rcases h1 with h1 | h1
  · refine eventually_trans _ _ _ _ (b7_step hp G h1) fun s2 h2 ↦ ?_
    rcases h2 with h2 | h2
    · refine eventually_trans _ _ _ _ (chunk_loop hp G h2) fun s3 h3 ↦ ?_
      rcases h3 with h3 | h3
      · exact b13_step hp G h3
      · exact rem h3
    · exact rem h2
  · exact b13_step hp G h1

/-- **The queries' loop** with levels, from query `j`: the epilogue. -/
theorem query_loop (hp : Placed code R.k) (G : Geo R)
    (hfind : Spec (Labels.label NativeRustcVmArm.Vm.Find.entryLabel) FindPre FindPost) {j : Nat} {st : MachineState}
    (H : HeadA R j st) : Eventually (step1 Host.exe) (Post R) st := by
  refine Sym.loop (fun n st ↦ ∃ j, n = R.nq - j ∧ HeadA R j st) (fun n st ⟨j, hn, H⟩ ↦ ?_)
    ⟨j, rfl, H⟩
  have hj := H.lt
  refine eventually_trans _ _ _ _ (head_step hp G H) fun s1 h1 ↦ ?_
  refine eventually_trans _ _ _ _ (scan_loop hp G h1) fun s2 h2 ↦ ?_
  rcases h2 with h2 | ⟨i, h2⟩
  · exact .done _ (.inl h2)
  refine eventually_trans _ _ _ _ (copy_step hp G h2) fun s3 h3 ↦ ?_
  refine eventually_trans _ _ _ _ (lev_loop hp G hfind h3) fun s4 h4 ↦ ?_
  rcases h4 with h4 | h4
  · exact .done _ (.inl h4)
  refine Eventually.mono (next_step hp G h4) fun s5 h5 ↦ ?_
  rcases h5 with h5 | h5
  · exact .inl h5
  · exact .inr ⟨R.nq - (j + 1), by omega, j + 1, rfl, h5⟩

end

end NativeRustcVmArm.Wire.WriteOpenings
