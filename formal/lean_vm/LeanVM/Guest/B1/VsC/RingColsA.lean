/-
  LeanVM.Guest.B1.VsC.RingColsA

  `ring_cols__L{3,5,10}` complete placed.
-/

module

public import LeanVM.Guest.B1.VsC.RingColsC
public import LeanVM.Guest.B1.VsC.SqueezeFwd
import LeanVM.Guest.CoreRef

/-!
# `ring_cols`, placed

`ring_cols(row, scl, msk)` is a pure leaf: its loads go through its three parameters at offsets
below `64`, `n`, `n`. `rc_complete0`: the layout-free completeness in `CallCompletes0` form
(`callCompletes0_pure`, the return pinned by the guest stream's `ring_cols_holds`);
`ring_cols_placed`: placed by `callAtA_leaf0`, its arrays' cells in `R`, no words of its own.
-/

namespace LeanVM.Guest.B1.VsC

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Memory LeanVM.Guest.B1
open LeanVM.Guest.Complete LeanVM.Guest.B1.Fwd LeanVM.Guest.B1.VerifySub
open LeanVM.Guest.Value LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile
open LeanVM.Protocol.Verifier

@[expose] public section

/-- `ring_cols__L{n}`'s completeness, its words chosen per memory. -/
def RingColsComplete0 (kd n : ℕ) (name : String) : Prop :=
  ∀ (row scl msk : E) (rs ss ms : List E), rs.length = kBits → ss.length = n → ms.length = n →
    CallCompletes0 kd name [row, scl, msk]
      [∑ q ∈ Finset.range n, ms.getD q 0 * frobSum rs (ss.getD q 0)]
      (fun rd ↦ ReadsAt rd row rs ∧ ReadsAt rd scl ss ∧ ReadsAt rd msk ms) PostQuiet

theorem rc_complete0 {kd : ℕ} (p : ℕ × String) (hp : p ∈ ringColsNames) {f : Fn}
    (hfind : coreProgram.find? p.2 = some f) (hparams : f.params = [.n 0, .n 1, .n 2])
    (hck : pureChecks 3 [(0, kBits), (1, p.1), (2, p.1)] f.body = true) :
    RingColsComplete0 kd p.1 p.2 := by
  intro row scl msk rs ss ms hrs hss hms
  refine callCompletes0_pure [(0, kBits), (1, p.1), (2, p.1)] hfind (by rw [hparams]; rfl) hck
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

/-- `ring_cols`' names. -/
def rcNames : List String := ["ring_cols__L3", "ring_cols__L5", "ring_cols__L10"]

theorem rc_pureIn : coreProgram.PureIn rcNames := by
  intro g hg fn hf
  simp only [rcNames, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl
  · rw [coreProgram_find?_at (j := idx% «ring_cols__L3») rfl] at hf
    obtain rfl := Option.some.inj hf; decide +kernel
  · rw [coreProgram_find?_at (j := idx% «ring_cols__L5») rfl] at hf
    obtain rfl := Option.some.inj hf; decide +kernel
  · rw [coreProgram_find?_at (j := idx% «ring_cols__L10») rfl] at hf
    obtain rfl := Option.some.inj hf; decide +kernel

variable {fs : String → ℕ} {al : String → Bool} {cert : String → V → ℕ}

set_option maxRecDepth 100000 in
/-- **`ring_cols__L{n}` completes placed**, its three arrays' cells in `R`. -/
theorem ring_cols_placed (kd : ℕ) {n : ℕ} {name : String} (hp : (n, name) ∈ ringColsNames) {row scl msk : E}
    {rs ss ms : List E} (hrs : rs.length = kBits) (hss : ss.length = n) (hms : ms.length = n) {R : ℕ → Prop}
    (hptr : ∀ q ∈ [(0, kBits), (1, n), (2, n)], ∀ off < q.2,
      ∃ i, ([row, scl, msk].getD q.1 0).limb 0 * addressOfIndex off = addressOfIndex i ∧ R i) (fp c : ℕ) :
    CallAtA fs al cert kd name [row, scl, msk] [∑ q ∈ Finset.range n, ms.getD q 0 * frobSum rs (ss.getD q 0)]
      R (fun _ => False) (fun _ => True) (fun rd ↦ ReadsAt rd row rs ∧ ReadsAt rd scl ss ∧ ReadsAt rd msk ms)
      PostQuiet (fs name) fp c c := by
  simp only [ringColsNames, List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at hp
  rcases hp with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · have h := rc_complete0 (kd := kd) (3, "ring_cols__L3") (by decide)
      (coreProgram_find?_at (j := idx% «ring_cols__L3») rfl) rfl (by decide +kernel) row scl msk rs ss ms hrs hss hms
    exact callAtA_leaf0 rc_pureIn (by simp [rcNames]) (by decide +kernel)
      (coreProgram_find?_at (j := idx% «ring_cols__L3») rfl) rfl (by decide +kernel) (by decide +kernel)
      (by simp) hptr h fp c
  · have h := rc_complete0 (kd := kd) (5, "ring_cols__L5") (by decide)
      (coreProgram_find?_at (j := idx% «ring_cols__L5») rfl) rfl (by decide +kernel) row scl msk rs ss ms hrs hss hms
    exact callAtA_leaf0 rc_pureIn (by simp [rcNames]) (by decide +kernel)
      (coreProgram_find?_at (j := idx% «ring_cols__L5») rfl) rfl (by decide +kernel) (by decide +kernel)
      (by simp) hptr h fp c
  · have h := rc_complete0 (kd := kd) (10, "ring_cols__L10") (by decide)
      (coreProgram_find?_at (j := idx% «ring_cols__L10») rfl) rfl (by decide +kernel) row scl msk rs ss ms hrs hss hms
    exact callAtA_leaf0 rc_pureIn (by simp [rcNames]) (by decide +kernel)
      (coreProgram_find?_at (j := idx% «ring_cols__L10») rfl) rfl (by decide +kernel) (by decide +kernel)
      (by simp) hptr h fp c

end
end LeanVM.Guest.B1.VsC
