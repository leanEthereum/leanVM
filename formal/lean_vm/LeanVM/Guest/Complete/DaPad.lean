module

public import LeanVM.Guest.Complete.DaBlob
public import LeanVM.Guest.Value.KeccakConst
import LeanVM.Guest.CoreRef
import LeanVM.Guest.ValRef
import LeanVM.Guest.Data.ValNames.«da_pad»
import LeanVM.Guest.Data.ValNames.«da_pad_loop0»

/-!
# `da_pad`, complete

`da_pad(roots, g^r, g^d)` writes the padding blob's root into the slots `r ..< r + d`; it and its
loop take no words of their own: on memories holding those roots (`PadPre`), they complete popping
nothing (`da_pad_completes`).
-/

namespace LeanVM.Guest.Complete

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Memory LeanVM.Guest.B1
open LeanVM.Guest.B1.Da LeanVM.Guest.B1.Digest LeanVM.Protocol LeanVM.Protocol.KeccakHash
open LeanVM.Protocol.Verifier (gen)
open LeanVM.Guest.Value LeanVM.Guest.Value.Keccak

@[expose] public section

set_option linter.constructorNameAsVariable false

/-- The padding loop's block. -/
def padLPre : List Stmt := [
  .atom (.mul (.n 4) (.n 3) (.n 3)),
  .atom (.mul (.n 5) (.n 2) (.n 4)),
  .atom (.mul (.n 6) (.n 0) (.n 0)),
  .atom (.mul (.n 7) (.n 5) (.n 6)),
  .atom (.const (.n 8) (word 8002054802297438051 4108169256045952147)),
  .atom (.load (.n 8) (.n 7) 0),
  .atom (.const (.n 9) (word 12830724869163462953 1721925254677230945)),
  .atom (.load (.n 9) (.n 7) 1),
  .atom (.const (.n 10) (word 2 0)),
  .atom (.mul (.n 11) (.n 0) (.n 10)),
  .atom (.add (.n 12) (.n 11) (.n 1)),
  .atom (.const (.n 13) (word 2 0)),
  .atom (.mul (.n 14) (.n 0) (.n 13)),
  .callIf (.n 12) name% «da_pad_loop0» [.n 14, .n 1, .n 2, .n 3]]

theorem padL_body : (fn% «da_pad_loop0»).body = padLPre ++ [.ret []] := rfl
theorem padL_params : (fn% «da_pad_loop0»).params = [.n 0, .n 1, .n 2, .n 3] := rfl

set_option maxRecDepth 100000 in
theorem find_padL : coreProgram.find? name% «da_pad_loop0» = some fn% «da_pad_loop0» :=
  coreProgram_find?_at (j := idx% «da_pad_loop0») rfl

/-- The padding blob's root's cells. -/
def padCells : List E := [(digestHalves daPadBlobDigest).1, (digestHalves daPadBlobDigest).2]

/-- Iteration `j`'s valuation. -/
noncomputable def padLσ (j d : ℕ) (roots nb : E) : Val := fun v =>
  [gen ^ j, gen ^ d, roots, nb, nb * nb, roots * (nb * nb), gen ^ j * gen ^ j, roots * (nb * nb) * (gen ^ j * gen ^ j),
    word 8002054802297438051 4108169256045952147, word 12830724869163462953 1721925254677230945, word 2 0,
    gen ^ j * word 2 0, gen ^ j * word 2 0 + gen ^ d, word 2 0, gen ^ j * word 2 0].getD v.idx 0

/-- What `da_pad` writes: the padding root at slots `r + j`, `j < d`. -/
def PadPre (r d : ℕ) (roots : E) (rd : Reader) : Prop :=
  ∀ j < d, ReadsAt rd (roots * gen ^ (2 * (r + j))) padCells

/-- A tree popping nothing. -/
def PopsNil (rd : Reader) (t : Tree) : Prop := t.pops coreProgram rd = []

theorem pad_slot (r j : ℕ) (roots : E) :
    roots * (gen ^ r * gen ^ r) * (gen ^ j * gen ^ j) = roots * gen ^ (2 * (r + j)) := by
  rw [gen_sq, gen_sq, mul_assoc, ← pow_add]; congr 2; ring

set_option maxRecDepth 100000 in
theorem padL_step (k : ℕ) {r d : ℕ} (hd : d < 2 ^ 34) (roots : E) {j : ℕ} (hj : j < d)
    (htail : j + 1 < d → CallCompletes0 k name% «da_pad_loop0» [gen ^ (j + 1), gen ^ d, roots, gen ^ r] []
      (PadPre r d roots) PopsNil) :
    CallCompletes0 k name% «da_pad_loop0» [gen ^ j, gen ^ d, roots, gen ^ r] [] (PadPre r d roots) PopsNil := by
  refine callCompletes0_straight find_padL padL_body rfl fun rd hl hp => ?_
  set σ := padLσ j d roots (gen ^ r) with hσ
  have e12 : σ (.n 12) = gen ^ j * word 2 0 + gen ^ d := rfl
  have hargs : [V.n 14, .n 1, .n 2, .n 3].map σ = [gen ^ (j + 1), gen ^ d, roots, gen ^ r] := by
    show [gen ^ j * word 2 0, gen ^ d, roots, gen ^ r] = _; rw [gen_mul_two]
  have hR := hp j hj
  have hslot : σ (.n 7) = roots * gen ^ (2 * (r + j)) := pad_slot r j roots
  have hc := daPadBlob_cells
  simp only [Prod.ext_iff] at hc
  obtain ⟨t1, hk1, hb1, hp1⟩ : ∃ t1 : Tree,
      Tree.KidsValid coreProgram rd σ [⟨name% «da_pad_loop0», [.n 14, .n 1, .n 2, .n 3], [],
        decide (σ (.n 12) ≠ 0)⟩] [t1] ∧ t1.BufsOk coreProgram ∧ t1.pops coreProgram rd = [] := by
    by_cases hlt : j + 1 < d
    · obtain ⟨t1, hn, hv1, hb, hp'⟩ := htail hlt rd hl hp
      have htk : decide (σ (.n 12) ≠ 0) = true := by
        rw [e12, loopGuard_taken hd (by omega)]; exact decide_eq_true (by omega)
      exact ⟨t1, kidsValid_cons_taken htk hn (by rw [hargs]; exact hv1) kidsValid_nil, hb, hp'⟩
    · have htk : decide (σ (.n 12) ≠ 0) = false := by
        rw [e12, loopGuard_taken hd (by omega)]; exact decide_eq_false (by omega)
      exact ⟨.phantom name% «da_pad_loop0» (padLσ (j + 1) d roots (gen ^ r)),
        kidsValid_cons_skip htk find_padL (by rw [padL_params, hargs]; rfl) kidsValid_nil,
        by rw [Tree.BufsOk]; trivial, by rw [Tree.pops]⟩
  refine ⟨σ, [t1], rfl, rfl, ?_, hk1, ⟨hb1, trivial⟩, ?_⟩
  · intro s hs
    simp only [padLPre, List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact rfl
    · exact rfl
    · exact rfl
    · exact rfl
    · exact rfl
    · show LoadHolds rd (σ (.n 7)) 0 (word 8002054802297438051 4108169256045952147)
      rw [hslot, hc.1]; exact hR 0 (by simp [padCells])
    · exact rfl
    · show LoadHolds rd (σ (.n 7)) 1 (word 12830724869163462953 1721925254677230945)
      rw [hslot, hc.2]; exact hR 1 (by simp [padCells])
    · exact rfl
    · exact rfl
    · exact rfl
    · exact rfl
    · exact rfl
    · show IsInK (gen ^ j * word 2 0 + gen ^ d); rw [gen_mul_two]; exact gen_pow_add_isInK _ _
  · show _ = _
    rw [pops_straight_none find_padL padL_body rfl rfl hk1, Tree.popsKids, Tree.popsKids, hp1]
    rfl

theorem pad_loop_completes (k : ℕ) {r d : ℕ} (hd : d < 2 ^ 34) (roots : E) :
    ∀ j < d, CallCompletes0 k name% «da_pad_loop0» [gen ^ j, gen ^ d, roots, gen ^ r] [] (PadPre r d roots)
      PopsNil := by
  have key : ∀ t j, j + 1 + t = d → CallCompletes0 k name% «da_pad_loop0» [gen ^ j, gen ^ d, roots, gen ^ r] []
      (PadPre r d roots) PopsNil := by
    intro t
    induction t with
    | zero => intro j hj; exact padL_step k hd roots (by omega) fun h' => absurd h' (by omega)
    | succ t ih => intro j hj; exact padL_step k hd roots (by omega) fun _ => ih (j + 1) (by omega)
  intro j hj
  exact key (d - j - 1) j (by omega)

/-- `da_pad`'s block. -/
def padPre : List Stmt := [
  .atom (.const (.n 3) (word 1 0)),
  .atom (.add (.n 4) (.n 3) (.n 2)),
  .atom (.const (.n 5) (word 1 0)),
  .callIf (.n 4) name% «da_pad_loop0» [.n 5, .n 2, .n 0, .n 1]]

theorem pad_body : (fn% «da_pad»).body = padPre ++ [.ret []] := rfl

set_option maxRecDepth 100000 in
theorem find_pad : coreProgram.find? name% «da_pad» = some fn% «da_pad» :=
  coreProgram_find?_at (j := idx% «da_pad») rfl

theorem one_add_gen_pow_ne {d : ℕ} (hd : d < 2 ^ 34) : decide (word 1 0 + gen ^ d ≠ 0) = decide (d ≠ 0) := by
  rw [word_one]
  refine decide_eq_decide.mpr ⟨fun h he => h (by rw [he, pow_zero]; exact e_add_eq_zero_iff.mpr rfl),
    fun h he => h ?_⟩
  have := e_add_eq_zero_iff.mp he
  rw [← pow_zero gen] at this
  exact (gen_pow_inj' (by omega) hd this).symm

set_option maxRecDepth 100000 in
/-- **`da_pad` completes**, taking no words of its own, on memories holding the padding roots. -/
theorem da_pad_completes (k : ℕ) {r d : ℕ} (hd : d < 2 ^ 34) (roots : E) :
    CallCompletes0 k "da_pad" [roots, gen ^ r, gen ^ d] [] (PadPre r d roots) PopsNil := by
  refine callCompletes0_straight find_pad pad_body rfl fun rd hl hp => ?_
  set σ : Val := fun v => [roots, gen ^ r, gen ^ d, word 1 0, word 1 0 + gen ^ d, word 1 0].getD v.idx 0 with hσ
  have hargs : [V.n 5, .n 2, .n 0, .n 1].map σ = [gen ^ 0, gen ^ d, roots, gen ^ r] := by
    show [word 1 0, gen ^ d, roots, gen ^ r] = _; rw [word_one, pow_zero]
  obtain ⟨t1, hk1, hb1, hp1⟩ : ∃ t1 : Tree,
      Tree.KidsValid coreProgram rd σ [⟨name% «da_pad_loop0», [.n 5, .n 2, .n 0, .n 1], [],
        decide (σ (.n 4) ≠ 0)⟩] [t1] ∧ t1.BufsOk coreProgram ∧ t1.pops coreProgram rd = [] := by
    by_cases h0 : d = 0
    · have htk : decide (σ (.n 4) ≠ 0) = false := by
        show decide (word 1 0 + gen ^ d ≠ 0) = false; rw [one_add_gen_pow_ne hd]; exact decide_eq_false (by omega)
      exact ⟨.phantom name% «da_pad_loop0» (padLσ 0 d roots (gen ^ r)),
        kidsValid_cons_skip htk find_padL (by rw [padL_params, hargs]; rfl) kidsValid_nil,
        by rw [Tree.BufsOk]; trivial, by rw [Tree.pops]⟩
    · have htk : decide (σ (.n 4) ≠ 0) = true := by
        show decide (word 1 0 + gen ^ d ≠ 0) = true; rw [one_add_gen_pow_ne hd]; exact decide_eq_true h0
      obtain ⟨t1, hn, hv1, hb, hp'⟩ := pad_loop_completes k hd roots 0 (by omega) rd hl hp
      exact ⟨t1, kidsValid_cons_taken htk hn (by rw [hargs]; exact hv1) kidsValid_nil, hb, hp'⟩
  refine ⟨σ, [t1], rfl, rfl, ?_, hk1, ⟨hb1, trivial⟩, ?_⟩
  · intro s hs
    simp only [padPre, List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl | rfl | rfl
    · exact rfl
    · exact rfl
    · exact rfl
    · show IsInK (word 1 0 + gen ^ d); rw [word_one, ← pow_zero gen]; exact gen_pow_add_isInK _ _
  · show _ = _
    rw [pops_straight_none find_pad pad_body rfl rfl hk1, Tree.popsKids, Tree.popsKids, hp1]
    rfl

end
end LeanVM.Guest.Complete
