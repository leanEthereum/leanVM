module

public import NativeRustcVmX64.Wire.WriteOpenings.A.Scan
public import NativeRustcVmX64.Wire.WriteOpenings.A.Copy
public import NativeRustcVmX64.Wire.WriteOpenings.A.Lev
public import NativeRustcVmX64.Wire.WriteOpenings.A.Next
public import NativeRustcVmX64.Wire.WriteOpenings.B
public import NativeRustcVmX64.Code.Vm.Find.Names
public import NativeRustcVmX64.Code.Vm.WriteOpenings.Names

/-!
# `write_openings` meets its contract (x86-64)

`writeOpenings_spec`: the prologue (`entry_spec`), then with levels (`A_loop`: per query its word,
its position, its leaf, each level's digest by `find`) or without (`noLev`: paths B and C). Every
query found and every level of at most `256` siblings: AL `1` and the phase of the model's
openings at `out` (`end_spec`); otherwise a rejection, which the postcondition's hypotheses rule
out (`Hyp.not_bad`).
-/

namespace NativeRustcVmX64.Wire.WriteOpenings

open NativeRustcX64 hiding InRange SameOutside
open NativeRustcVmX64.Vm.WriteOpenings

public section

variable {R : Run} {j : Nat} [Host]

/-- **The levels of opening `j`**, from level `l`: a rejection, or the opening written. -/
theorem levels (hp : Placed code R.k) (G : Geo R)
    (hfind : Spec (Labels.label NativeRustcVmX64.Vm.Find.entryLabel) FindPre FindPost) {l : Nat} {st : MachineState}
    (H : LevA R j l st) :
    Eventually (step1 Host.exe) (fun st' ↦ Post R st' ∨ NextA R j st') st := by
  refine Sym.loop (fun n st ↦ ∃ l, n = R.h - l ∧ LevA R j l st) (fun n st ⟨l, hn, H⟩ ↦ ?_)
    ⟨l, rfl, H⟩
  have hl := H.s.llt
  refine (cnt_step hp G H).bind fun s1 h1 ↦ ?_
  rcases h1 with h1 | H1
  · exact .done _ (.inl (.inl h1))
  refine (call_step hp G hfind H1).bind fun s2 H2 ↦ (ret_step hp G H2).bind fun s3 H3 ↦
    (dig_step hp G H3).bind fun s4 h4 ↦ ?_
  rcases h4 with H4 | H4
  · exact .done _ (.inr ⟨R.h - (l + 1), by omega, l + 1, rfl, H4⟩)
  · exact .done _ (.inl (.inr H4))

/-- **The leaf of opening `j`** (at position `i`), from four words at a time. -/
theorem chunks (hp : Placed code R.k) (G : Geo R) {i t : Nat} {st : MachineState}
    (H : ChunkA R j i t st) :
    Eventually (step1 Host.exe) (fun st' ↦ LeafA R j i st' ∨ PreRemA R j i st') st := by
  refine Sym.loop (fun n st ↦ ∃ t, n = q4 R.lw - t ∧ ChunkA R j i t st)
    (fun n st ⟨t, hn, H⟩ ↦ (chunk_step hp G H).bind fun s h ↦ ?_) ⟨t, rfl, H⟩
  rcases h with H' | H' | H'
  · exact .done _ (.inr ⟨q4 R.lw - (t + 4), by have := H.tq; omega, t + 4, rfl, H'⟩)
  · exact .done _ (.inl (.inl H'))
  · exact .done _ (.inl (.inr H'))

/-- **The remaining leaf words.** -/
theorem rems (hp : Placed code R.k) (G : Geo R) {i : Nat} {st : MachineState}
    (H : PreRemA R j i st) : Eventually (step1 Host.exe) (LeafA R j i) st := by
  refine (rem_start hp G H).bind fun s H0 ↦ ?_
  refine Sym.loop (fun n st ↦ ∃ u, n = R.lw % 4 - u ∧ RemA R j i u st)
    (fun n st ⟨u, hn, H⟩ ↦ (rem_step hp G H).bind fun s h ↦ ?_) ⟨0, rfl, H0⟩
  rcases h with H' | H'
  · exact .done _ (.inr ⟨R.lw % 4 - (u + 1), by have := H.ult; omega, u + 1, rfl, H'⟩)
  · exact .done _ (.inl H')

/-- **The path with levels**, from its head at query `j`. -/
theorem A_loop (hp : Placed code R.k) (G : Geo R)
    (hfind : Spec (Labels.label NativeRustcVmX64.Vm.Find.entryLabel) FindPre FindPost) {st : MachineState}
    (H : HeadA R j st) : Eventually (step1 Host.exe) (Post R) st := by
  refine Sym.loop (fun n st ↦ ∃ j, n = R.nq - j ∧ HeadA R j st) (fun n st ⟨j, hn, H⟩ ↦ ?_)
    ⟨j, rfl, H⟩
  have hj := H.lt
  have after_leaf : ∀ {i} s, LeafA R j i s → Eventually (step1 Host.exe)
      (fun st' ↦ Post R st' ∨ ∃ n' < n, ∃ j, n' = R.nq - j ∧ HeadA R j st') s := fun s H5 ↦
    (leaf_step hp G H5).bind fun s6 H6 ↦ (levels hp G hfind H6).bind fun s7 h7 ↦ by
      rcases h7 with h7 | H7
      · exact .done _ (.inl h7)
      refine (next_step hp G H7).bind fun s8 h8 ↦ ?_
      rcases h8 with H8 | h8
      · exact .done _ (.inr ⟨R.nq - (j + 1), by omega, j + 1, rfl, H8⟩)
      · exact (end_spec hp G h8).mono fun _ h ↦ .inl h
  refine (head_step hp G H).bind fun s1 H1 ↦ (scan_loop hp G H1).bind fun s2 h2 ↦ ?_
  rcases h2 with h2 | ⟨i, H2⟩
  · exact .done _ (.inl h2)
  refine (found_step hp G H2).bind fun s3 h3 ↦ ?_
  rcases h3 with H3 | H3 | H3
  · exact after_leaf _ H3
  · refine (chunks hp G H3).bind fun s4 h4 ↦ ?_
    rcases h4 with H4 | H4
    · exact after_leaf _ H4
    · exact (rems hp G H4).bind fun s5 H5 ↦ after_leaf _ H5
  · exact (rems hp G H3).bind fun s5 H5 ↦ after_leaf _ H5

/-- **`write_openings` meets its contract.** -/
theorem writeOpenings_spec {k : Nat} (hp : Placed code k)
    (hfind : Spec (Labels.label NativeRustcVmX64.Vm.Find.entryLabel) FindPre FindPost) :
    Spec (Labels.label NativeRustcVmX64.Vm.WriteOpenings.entryLabel) WriteOpeningsPre WriteOpeningsPost := by
  intro m hpre
  have G : Geo ⟨m, k⟩ := geo_of hpre
  rw [show Labels.label NativeRustcVmX64.Vm.WriteOpenings.entryLabel = pcOf ⟨m, k⟩ 0 from hp.label NativeRustcVmX64.Vm.WriteOpenings.entry_at]
  refine (entry_spec (R := ⟨m, k⟩) hp G).bind fun st h ↦ ?_
  rcases h with ⟨H, h0⟩ | ⟨H, h0⟩
  · exact (start_step hp G H h0).bind fun st' H' ↦ A_loop hp G hfind H'
  · exact noLev hp G H h0

end

end NativeRustcVmX64.Wire.WriteOpenings

/--
info: 'NativeRustcVmX64.Wire.WriteOpenings.writeOpenings_spec' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms NativeRustcVmX64.Wire.WriteOpenings.writeOpenings_spec
