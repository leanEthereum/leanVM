/-
  LeanVM.Guest.B1.Link.RoundsMain

  B1 for `link_rounds` (six specializations): the link's sum-check rounds.
-/

module

public import LeanVM.Guest.B1.Link.RoundsLoop
import LeanVM.Guest.CoreRef

/-!
# `link_rounds`

Each specialization `link_rounds__L{nt}_L{bits}` (the index side's `(1, 0)`, the row side's
`(d + 1, LINK_ROW_GRIND[d])` and the pointer columns' `(d, LINK_PTR_GRIND[d])`, `6 ≤ d ≤ 9`) implies
`MeaningLR`: its count `g^count`, `count < 64`, and a chain of `count` rounds, so a run of
`sumcheck claim (nt + 2) (replicate count none)` (`chain_runsTo`), given `grind_check`'s soundness
at one bit (`GcSound1`, `gcSound1_image` on a memory image) and the windows table at `tabs`.
-/

namespace LeanVM.Guest.B1.Link

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.B1

@[expose] public section

set_option maxRecDepth 100000 in
theorem link_rounds_L1_L0_sound (rd : Reader) (hgc : 0 ≠ 0 → GcSound1 rd) (args rets : List E) :
    coreProgram.Rel rd "link_rounds__L1_L0" args rets → MeaningLR 1 0 rd args rets :=
  lrMain_sound (by decide) (by decide) (Or.inl rfl) hgc
    (coreProgram_find?_at (j := idx% «link_rounds__L1_L0») rfl) rfl lrMain_L1_L0_body
    (coreProgram_find?_at (j := idx% «link_rounds__L1_L0_loop0») rfl) rfl lrLoop_L1_L0_body rfl
    (fun k hk args rets h ↦ by
      simp only [List.length_cons, List.length_nil] at hk
      interval_cases k
      · exact lrl_L1_L0_L0_sound rd args rets h
      · exact lrl_L1_L0_L1_sound rd hgc args rets h
      · exact lrl_L1_L0_L2_sound rd hgc args rets h
      · exact lrl_L1_L0_L3_sound rd hgc args rets h)
    args rets

set_option maxRecDepth 100000 in
theorem link_rounds_L7_L0_sound (rd : Reader) (hgc : 0 ≠ 0 → GcSound1 rd) (args rets : List E) :
    coreProgram.Rel rd "link_rounds__L7_L0" args rets → MeaningLR 7 0 rd args rets :=
  lrMain_sound (by decide) (by decide) (Or.inl rfl) hgc
    (coreProgram_find?_at (j := idx% «link_rounds__L7_L0») rfl) rfl lrMain_L7_L0_body
    (coreProgram_find?_at (j := idx% «link_rounds__L7_L0_loop0») rfl) rfl lrLoop_L7_L0_body rfl
    (fun k hk args rets h ↦ by
      simp only [List.length_cons, List.length_nil] at hk
      interval_cases k
      · exact lrl_L7_L0_L0_sound rd args rets h
      · exact lrl_L7_L0_L1_sound rd hgc args rets h
      · exact lrl_L7_L0_L2_sound rd hgc args rets h
      · exact lrl_L7_L0_L3_sound rd hgc args rets h)
    args rets

set_option maxRecDepth 100000 in
theorem link_rounds_L6_L0_sound (rd : Reader) (hgc : 0 ≠ 0 → GcSound1 rd) (args rets : List E) :
    coreProgram.Rel rd "link_rounds__L6_L0" args rets → MeaningLR 6 0 rd args rets :=
  lrMain_sound (by decide) (by decide) (Or.inl rfl) hgc
    (coreProgram_find?_at (j := idx% «link_rounds__L6_L0») rfl) rfl lrMain_L6_L0_body
    (coreProgram_find?_at (j := idx% «link_rounds__L6_L0_loop0») rfl) rfl lrLoop_L6_L0_body rfl
    (fun k hk args rets h ↦ by
      simp only [List.length_cons, List.length_nil] at hk
      interval_cases k
      · exact lrl_L6_L0_L0_sound rd args rets h
      · exact lrl_L6_L0_L1_sound rd hgc args rets h
      · exact lrl_L6_L0_L2_sound rd hgc args rets h
      · exact lrl_L6_L0_L3_sound rd hgc args rets h)
    args rets

set_option maxRecDepth 100000 in
theorem link_rounds_L8_L1_sound (rd : Reader) (hgc : 1 ≠ 0 → GcSound1 rd) (args rets : List E) :
    coreProgram.Rel rd "link_rounds__L8_L1" args rets → MeaningLR 8 1 rd args rets :=
  lrMain_sound (by decide) (by decide) (Or.inr ⟨rfl, by decide⟩) hgc
    (coreProgram_find?_at (j := idx% «link_rounds__L8_L1») rfl) rfl lrMain_L8_L1_body
    (coreProgram_find?_at (j := idx% «link_rounds__L8_L1_loop0») rfl) rfl lrLoop_L8_L1_body rfl
    (fun k hk args rets h ↦ by
      simp only [List.length_cons, List.length_nil] at hk
      interval_cases k
      · exact lrl_L8_L1_L0_sound rd args rets h
      · exact lrl_L8_L1_L1_sound rd hgc args rets h
      · exact lrl_L8_L1_L2_sound rd hgc args rets h
      · exact lrl_L8_L1_L3_sound rd hgc args rets h)
    args rets

set_option maxRecDepth 100000 in
theorem link_rounds_L9_L1_sound (rd : Reader) (hgc : 1 ≠ 0 → GcSound1 rd) (args rets : List E) :
    coreProgram.Rel rd "link_rounds__L9_L1" args rets → MeaningLR 9 1 rd args rets :=
  lrMain_sound (by decide) (by decide) (Or.inr ⟨rfl, by decide⟩) hgc
    (coreProgram_find?_at (j := idx% «link_rounds__L9_L1») rfl) rfl lrMain_L9_L1_body
    (coreProgram_find?_at (j := idx% «link_rounds__L9_L1_loop0») rfl) rfl lrLoop_L9_L1_body rfl
    (fun k hk args rets h ↦ by
      simp only [List.length_cons, List.length_nil] at hk
      interval_cases k
      · exact lrl_L9_L1_L0_sound rd args rets h
      · exact lrl_L9_L1_L1_sound rd hgc args rets h
      · exact lrl_L9_L1_L2_sound rd hgc args rets h
      · exact lrl_L9_L1_L3_sound rd hgc args rets h)
    args rets

set_option maxRecDepth 100000 in
theorem link_rounds_L10_L1_sound (rd : Reader) (hgc : 1 ≠ 0 → GcSound1 rd) (args rets : List E) :
    coreProgram.Rel rd "link_rounds__L10_L1" args rets → MeaningLR 10 1 rd args rets :=
  lrMain_sound (by decide) (by decide) (Or.inr ⟨rfl, by decide⟩) hgc
    (coreProgram_find?_at (j := idx% «link_rounds__L10_L1») rfl) rfl lrMain_L10_L1_body
    (coreProgram_find?_at (j := idx% «link_rounds__L10_L1_loop0») rfl) rfl lrLoop_L10_L1_body rfl
    (fun k hk args rets h ↦ by
      simp only [List.length_cons, List.length_nil] at hk
      interval_cases k
      · exact lrl_L10_L1_L0_sound rd args rets h
      · exact lrl_L10_L1_L1_sound rd hgc args rets h
      · exact lrl_L10_L1_L2_sound rd hgc args rets h
      · exact lrl_L10_L1_L3_sound rd hgc args rets h)
    args rets

end
end LeanVM.Guest.B1.Link
