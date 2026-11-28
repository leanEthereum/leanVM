/-
  LeanVM.Guest.B1.VsC.RingColsC

  `ring_cols__L{n}` completes, layout-free.
-/

module

public import LeanVM.Guest.B1.VsC.Fwd
public import LeanVM.Guest.B1.Ring.Cols
import LeanVM.Guest.CoreRef

/-!
# `ring_cols`, complete

`ring_cols(row, scl, msk, n)` loads the row's 64 words, the `n` scales and the `n` selectors and
sums; its body is pure (`pureChecks`, by the kernel), and the guest stream's `ring_cols_holds`
pins its return. `ring_cols_complete`: at each deployed `n`, on every memory holding `rs` at `row`,
`ss` at `scl` and `ms` at `msk`, the call returns `Σ_q m_q · frobSum rs s_q`, popping nothing,
exact.
-/

namespace LeanVM.Guest.B1.VsC

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Memory LeanVM.Guest.B1
open LeanVM.Guest.Complete LeanVM.Guest.B1.Fwd LeanVM.Guest.B1.VerifySub
open LeanVM.Guest.Value LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile
open LeanVM.Protocol.Verifier

@[expose] public section

/-- What `ring_cols__L{n}`'s completeness gives. -/
def RingColsComplete (kd n : ℕ) (name : String) : Prop :=
  ∀ (row scl msk : E) (rs ss ms : List E), rs.length = kBits → ss.length = n → ms.length = n →
    CallCompletes kd name [row, scl, msk]
      [∑ q ∈ Finset.range n, ms.getD q 0 * frobSum rs (ss.getD q 0)]
      (fun rd ↦ ReadsAt rd row rs ∧ ReadsAt rd scl ss ∧ ReadsAt rd msk ms) PostQuiet

theorem rc_complete {kd : ℕ} (p : ℕ × String) (hp : p ∈ ringColsNames) {f : Fn}
    (hfind : coreProgram.find? p.2 = some f) (hparams : f.params = [.n 0, .n 1, .n 2])
    (hck : pureChecks 3 [(0, kBits), (1, p.1), (2, p.1)] f.body = true) :
    RingColsComplete kd p.1 p.2 := by
  intro row scl msk rs ss ms hrs hss hms
  refine callCompletes_pure [(0, kBits), (1, p.1), (2, p.1)] hfind (by rw [hparams]; rfl) hck
    (by simp) ?_ ?_
  · rintro rd - ⟨h1, h2, h3⟩ q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact ⟨rs, by simp [hrs], h1⟩
    · exact ⟨ss, by simp [hss], h2⟩
    · exact ⟨ms, by simp [hms], h3⟩
  · rintro rd - ⟨h1, h2, h3⟩ rets' hR
    obtain ⟨rs', ss', ms', l1, l2, l3, r1, r2, r3, rfl⟩ := ring_cols_holds p hp rd _ _ hR
    rw [readsAt_eq r1 h1 (by rw [l1, hrs]), readsAt_eq r2 h2 (by rw [l2, hss]),
      readsAt_eq r3 h3 (by rw [l3, hms])]

set_option maxRecDepth 100000 in
theorem ring_cols_L3_complete (kd : ℕ) : RingColsComplete kd 3 "ring_cols__L3" :=
  rc_complete (3, "ring_cols__L3") (by decide) (coreProgram_find?_at (j := idx% «ring_cols__L3») rfl) rfl
    (by decide +kernel)

set_option maxRecDepth 100000 in
theorem ring_cols_L5_complete (kd : ℕ) : RingColsComplete kd 5 "ring_cols__L5" :=
  rc_complete (5, "ring_cols__L5") (by decide) (coreProgram_find?_at (j := idx% «ring_cols__L5») rfl) rfl
    (by decide +kernel)

set_option maxRecDepth 100000 in
theorem ring_cols_L10_complete (kd : ℕ) : RingColsComplete kd 10 "ring_cols__L10" :=
  rc_complete (10, "ring_cols__L10") (by decide) (coreProgram_find?_at (j := idx% «ring_cols__L10») rfl) rfl
    (by decide +kernel)

/-- **Every deployed `ring_cols__L{n}` completes.** -/
theorem ring_cols_complete (kd : ℕ) : ∀ p ∈ ringColsNames, RingColsComplete kd p.1 p.2 := by
  intro p hp
  simp only [ringColsNames, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl
  exacts [ring_cols_L3_complete kd, ring_cols_L5_complete kd, ring_cols_L10_complete kd]

end
end LeanVM.Guest.B1.VsC
