/-
  LeanVM.Guest.B1.VsC.TablePointC

  `table_point__L{h}` completes, layout-free.
-/

module

public import LeanVM.Guest.B1.VsC.Fwd
public import LeanVM.Guest.B1.Link.TablePoint
import LeanVM.Guest.CoreRef

/-!
# `table_point`, complete

`table_point(theta, tau, chi, bits, h)` loads `h` words at `tau` and `chi` and `h + 1` at `bits`,
asserts nothing and hints nothing. `table_point_complete`: for every `h ≤ 24`, on every memory
holding `ts` at `tau`, `xs` at `chi` and `cs ++ [top]` at `bits`, the call returns the soundness
stream's meaning (`MeaningTablePoint`), popping nothing, exact. By `callCompletes0_pure`: the kernel
checks each specialization's core IR is pure (`pureChecks`), and the meaning pins the returns.
-/

namespace LeanVM.Guest.B1.VsC

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Memory LeanVM.Guest.B1
open LeanVM.Guest.B1.Link LeanVM.Guest.Complete LeanVM.Guest.B1.Fwd LeanVM.Protocol.Verifier

@[expose] public section

/-- What `table_point__L{h}`'s completeness gives: its returns on the words in memory. -/
def TablePointComplete (kd h : ℕ) (name : String) : Prop :=
  ∀ (theta tau chi bits top : E) (ts xs cs : List E), ts.length = h → xs.length = h → cs.length = h →
    CallCompletes0 kd name [theta, tau, chi, bits]
      [theta * tpTotalG ts xs cs top h, 1 + (1 + top) * tpPad cs xs, tpFullAt ts xs h]
      (fun rd ↦ ReadsAt rd tau ts ∧ ReadsAt rd chi xs ∧ ReadsAt rd bits (cs ++ [top])) PostQuiet

/-- The arrays `table_point__L{h}` reads. -/
def tpArrays (h : ℕ) : List (ℕ × ℕ) := [(1, h), (2, h), (3, h + 1)]

/-- **`table_point__L{h}` completes**, given its core IR pure. -/
theorem tp_complete {kd h : ℕ} (hh : h ≤ 24) {f : Fn} (hfind : coreProgram.find? (tpNames.getD h "") = some f)
    (hparams : f.params = [.n 0, .n 1, .n 2, .n 3]) (hck : pureChecks 4 (tpArrays h) f.body = true) :
    TablePointComplete kd h (tpNames.getD h "") := by
  intro theta tau chi bits top ts xs cs hts hxs hcs
  refine callCompletes0_pure (tpArrays h) hfind (by rw [hparams]; rfl) hck (by simp [tpArrays]) ?_ ?_
  · rintro rd - ⟨ht, hx, hb⟩ q hq
    simp only [tpArrays, List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact ⟨ts, by omega, ht⟩
    · exact ⟨xs, by omega, hx⟩
    · exact ⟨cs ++ [top], by simp; omega, hb⟩
  · rintro rd - ⟨ht, hx, hb⟩ rets' hR
    obtain ⟨ts', xs', cs', top', l1, l2, l3, r1, r2, r3, lt, rfl⟩ := table_point_sound h hh rd _ _ hR
    rw [readsAt_eq r1 ht (by omega), readsAt_eq r2 hx (by omega),
      readsAt_eq r3 (readsAt_prefix hb) (by omega), loadHolds_unique lt (hcs ▸ readsAt_last hb)]

set_option maxRecDepth 100000 in
theorem table_point_L0_complete (kd : ℕ) : TablePointComplete kd 0 (tpNames.getD 0 "") :=
  tp_complete (by norm_num) (coreProgram_find?_at (j := idx% «table_point__L0») rfl) rfl (by decide +kernel)

set_option maxRecDepth 100000 in
theorem table_point_L1_complete (kd : ℕ) : TablePointComplete kd 1 (tpNames.getD 1 "") :=
  tp_complete (by norm_num) (coreProgram_find?_at (j := idx% «table_point__L1») rfl) rfl (by decide +kernel)

set_option maxRecDepth 100000 in
theorem table_point_L2_complete (kd : ℕ) : TablePointComplete kd 2 (tpNames.getD 2 "") :=
  tp_complete (by norm_num) (coreProgram_find?_at (j := idx% «table_point__L2») rfl) rfl (by decide +kernel)

set_option maxRecDepth 100000 in
theorem table_point_L3_complete (kd : ℕ) : TablePointComplete kd 3 (tpNames.getD 3 "") :=
  tp_complete (by norm_num) (coreProgram_find?_at (j := idx% «table_point__L3») rfl) rfl (by decide +kernel)

set_option maxRecDepth 100000 in
theorem table_point_L4_complete (kd : ℕ) : TablePointComplete kd 4 (tpNames.getD 4 "") :=
  tp_complete (by norm_num) (coreProgram_find?_at (j := idx% «table_point__L4») rfl) rfl (by decide +kernel)

set_option maxRecDepth 100000 in
theorem table_point_L5_complete (kd : ℕ) : TablePointComplete kd 5 (tpNames.getD 5 "") :=
  tp_complete (by norm_num) (coreProgram_find?_at (j := idx% «table_point__L5») rfl) rfl (by decide +kernel)

set_option maxRecDepth 100000 in
theorem table_point_L6_complete (kd : ℕ) : TablePointComplete kd 6 (tpNames.getD 6 "") :=
  tp_complete (by norm_num) (coreProgram_find?_at (j := idx% «table_point__L6») rfl) rfl (by decide +kernel)

set_option maxRecDepth 100000 in
theorem table_point_L7_complete (kd : ℕ) : TablePointComplete kd 7 (tpNames.getD 7 "") :=
  tp_complete (by norm_num) (coreProgram_find?_at (j := idx% «table_point__L7») rfl) rfl (by decide +kernel)

set_option maxRecDepth 100000 in
theorem table_point_L8_complete (kd : ℕ) : TablePointComplete kd 8 (tpNames.getD 8 "") :=
  tp_complete (by norm_num) (coreProgram_find?_at (j := idx% «table_point__L8») rfl) rfl (by decide +kernel)

set_option maxRecDepth 100000 in
theorem table_point_L9_complete (kd : ℕ) : TablePointComplete kd 9 (tpNames.getD 9 "") :=
  tp_complete (by norm_num) (coreProgram_find?_at (j := idx% «table_point__L9») rfl) rfl (by decide +kernel)

set_option maxRecDepth 100000 in
theorem table_point_L10_complete (kd : ℕ) : TablePointComplete kd 10 (tpNames.getD 10 "") :=
  tp_complete (by norm_num) (coreProgram_find?_at (j := idx% «table_point__L10») rfl) rfl (by decide +kernel)

set_option maxRecDepth 100000 in
theorem table_point_L11_complete (kd : ℕ) : TablePointComplete kd 11 (tpNames.getD 11 "") :=
  tp_complete (by norm_num) (coreProgram_find?_at (j := idx% «table_point__L11») rfl) rfl (by decide +kernel)

set_option maxRecDepth 100000 in
theorem table_point_L12_complete (kd : ℕ) : TablePointComplete kd 12 (tpNames.getD 12 "") :=
  tp_complete (by norm_num) (coreProgram_find?_at (j := idx% «table_point__L12») rfl) rfl (by decide +kernel)

set_option maxRecDepth 100000 in
theorem table_point_L13_complete (kd : ℕ) : TablePointComplete kd 13 (tpNames.getD 13 "") :=
  tp_complete (by norm_num) (coreProgram_find?_at (j := idx% «table_point__L13») rfl) rfl (by decide +kernel)

set_option maxRecDepth 100000 in
theorem table_point_L14_complete (kd : ℕ) : TablePointComplete kd 14 (tpNames.getD 14 "") :=
  tp_complete (by norm_num) (coreProgram_find?_at (j := idx% «table_point__L14») rfl) rfl (by decide +kernel)

set_option maxRecDepth 100000 in
theorem table_point_L15_complete (kd : ℕ) : TablePointComplete kd 15 (tpNames.getD 15 "") :=
  tp_complete (by norm_num) (coreProgram_find?_at (j := idx% «table_point__L15») rfl) rfl (by decide +kernel)

set_option maxRecDepth 100000 in
theorem table_point_L16_complete (kd : ℕ) : TablePointComplete kd 16 (tpNames.getD 16 "") :=
  tp_complete (by norm_num) (coreProgram_find?_at (j := idx% «table_point__L16») rfl) rfl (by decide +kernel)

set_option maxRecDepth 100000 in
theorem table_point_L17_complete (kd : ℕ) : TablePointComplete kd 17 (tpNames.getD 17 "") :=
  tp_complete (by norm_num) (coreProgram_find?_at (j := idx% «table_point__L17») rfl) rfl (by decide +kernel)

set_option maxRecDepth 100000 in
theorem table_point_L18_complete (kd : ℕ) : TablePointComplete kd 18 (tpNames.getD 18 "") :=
  tp_complete (by norm_num) (coreProgram_find?_at (j := idx% «table_point__L18») rfl) rfl (by decide +kernel)

set_option maxRecDepth 100000 in
theorem table_point_L19_complete (kd : ℕ) : TablePointComplete kd 19 (tpNames.getD 19 "") :=
  tp_complete (by norm_num) (coreProgram_find?_at (j := idx% «table_point__L19») rfl) rfl (by decide +kernel)

set_option maxRecDepth 100000 in
theorem table_point_L20_complete (kd : ℕ) : TablePointComplete kd 20 (tpNames.getD 20 "") :=
  tp_complete (by norm_num) (coreProgram_find?_at (j := idx% «table_point__L20») rfl) rfl (by decide +kernel)

set_option maxRecDepth 100000 in
theorem table_point_L21_complete (kd : ℕ) : TablePointComplete kd 21 (tpNames.getD 21 "") :=
  tp_complete (by norm_num) (coreProgram_find?_at (j := idx% «table_point__L21») rfl) rfl (by decide +kernel)

set_option maxRecDepth 100000 in
theorem table_point_L22_complete (kd : ℕ) : TablePointComplete kd 22 (tpNames.getD 22 "") :=
  tp_complete (by norm_num) (coreProgram_find?_at (j := idx% «table_point__L22») rfl) rfl (by decide +kernel)

set_option maxRecDepth 100000 in
theorem table_point_L23_complete (kd : ℕ) : TablePointComplete kd 23 (tpNames.getD 23 "") :=
  tp_complete (by norm_num) (coreProgram_find?_at (j := idx% «table_point__L23») rfl) rfl (by decide +kernel)

set_option maxRecDepth 100000 in
theorem table_point_L24_complete (kd : ℕ) : TablePointComplete kd 24 (tpNames.getD 24 "") :=
  tp_complete (by norm_num) (coreProgram_find?_at (j := idx% «table_point__L24») rfl) rfl (by decide +kernel)

/-- **Every `table_point__L{h}` completes**, `h ≤ 24` (`N_ROW_LOGS`). -/
theorem table_point_complete (kd : ℕ) : ∀ h ≤ 24, TablePointComplete kd h (tpNames.getD h "") := by
  intro h hh
  interval_cases h
  exacts [table_point_L0_complete kd, table_point_L1_complete kd, table_point_L2_complete kd, table_point_L3_complete kd, table_point_L4_complete kd, table_point_L5_complete kd, table_point_L6_complete kd, table_point_L7_complete kd, table_point_L8_complete kd, table_point_L9_complete kd, table_point_L10_complete kd, table_point_L11_complete kd, table_point_L12_complete kd, table_point_L13_complete kd, table_point_L14_complete kd, table_point_L15_complete kd, table_point_L16_complete kd, table_point_L17_complete kd, table_point_L18_complete kd, table_point_L19_complete kd, table_point_L20_complete kd, table_point_L21_complete kd, table_point_L22_complete kd, table_point_L23_complete kd, table_point_L24_complete kd]

end
end LeanVM.Guest.B1.VsC
