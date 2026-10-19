/-
  LeanVM.Guest.B1.G1Placed

  Shared pieces of group 1's placed completeness: pinned reads lie in the caller's words,
  `CompleteMem`, and the certificate facts the frame runs need.
-/

module

public import LeanVM.Guest.B1.Uniform

/-!
# Group 1, placed: shared pieces

* `pinned_region`, `loadHolds_lift`, `readsAt_lift`: a word every memory defined below `2^k` and
  holding the caller's words `Lin` reads at the same address with the same value lies in `Lin`, so
  every memory holding `Lin` reads it (given one memory defined below `2^k` that holds `Lin`);
* `CompleteMem`: complete on every precondition that holds on every memory holding `Lin` (the form
  in which a pure function lifts, `completeMem_of_iff`);
* `G1Certs`: the certificate facts of group 1's two frame runs (`grind_check`,
  `decode_query_bits__L{d}`), which the certificate generator discharges.
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Memory
open LeanVM.Guest.B1.Main (Layout MemL RegionL)

@[expose] public section

/-! ## Pinned reads -/

open Classical in
/-- `rd` with the word `w` at `A`. -/
noncomputable def g1Poke (rd : Reader) (A : K) (w : E) : Reader := fun B => if B = A then some w else rd B

theorem g1_ne_add_one (v : E) : v + 1 ≠ v := fun h =>
  one_ne_zero (add_left_cancel (a := v) (by rw [h, add_zero]))

/-- **A word read alike on every memory defined below `2^k` holding `Lin` lies in `Lin`.** -/
theorem pinned_region {k : ℕ} {Lin : Layout} {rd1 : Reader} (hl1 : LowDef k rd1) (hL1 : MemL rd1 Lin)
    {A : K} {v : E} (h : ∀ rd, LowDef k rd → MemL rd Lin → rd A = some v) :
    ∃ i, A = gpow i ∧ RegionL Lin i := by
  classical
  by_contra hn
  have hpk : LowDef k (g1Poke rd1 A (v + 1)) := fun i hi => by
    unfold g1Poke; split
    · rfl
    · exact hl1 i hi
  have hpm : MemL (g1Poke rd1 A (v + 1)) Lin := fun q hq j hj => by
    refine ⟨(hL1 q hq j hj).1, ?_⟩
    have hne : (ofK (gpow q.1)).limb 0 * gpow j ≠ A := by
      rw [Main.addr_ofK]
      intro he
      exact hn ⟨q.1 + j, he.symm, q, hq, by omega, by omega⟩
    unfold g1Poke
    rw [ite_neg' hne]
    exact (hL1 q hq j hj).2
  have := h _ hpk hpm
  unfold g1Poke at this
  rw [ite_pos' rfl, Option.some.injEq] at this
  exact g1_ne_add_one v this

/-- **A load pinned on every memory defined below `2^k` holding `Lin` reads `Lin`**, so it holds on
every memory holding `Lin`. -/
theorem loadHolds_lift {k : ℕ} {Lin : Layout} {rd1 : Reader} (hl1 : LowDef k rd1) (hL1 : MemL rd1 Lin)
    {p : E} {j : ℕ} {v : E} (h : ∀ rd, LowDef k rd → MemL rd Lin → LoadHolds rd p j v) :
    (∃ i, p.limb 0 * gpow j = gpow i ∧ RegionL Lin i) ∧ ∀ rd, MemL rd Lin → LoadHolds rd p j v := by
  obtain ⟨i, hi, hr⟩ := pinned_region hl1 hL1 (fun rd hl hL => (h rd hl hL).2)
  refine ⟨⟨i, hi, hr⟩, fun rd hL => ⟨(h rd1 hl1 hL1).1, ?_⟩⟩
  rw [hi, Main.memL_agree hL hL1 i hr, ← hi]
  exact (h rd1 hl1 hL1).2

theorem readsAt_lift {k : ℕ} {Lin : Layout} {rd1 : Reader} (hl1 : LowDef k rd1) (hL1 : MemL rd1 Lin)
    {p : E} {xs : List E} (h : ∀ rd, LowDef k rd → MemL rd Lin → ReadsAt rd p xs) :
    (∀ j < xs.length, ∃ i, p.limb 0 * gpow j = gpow i ∧ RegionL Lin i) ∧
      ∀ rd, MemL rd Lin → ReadsAt rd p xs :=
  ⟨fun j hj => (loadHolds_lift hl1 hL1 fun rd hl hL => h rd hl hL j hj).1,
    fun rd hL j hj => (loadHolds_lift hl1 hL1 fun rd hl hL => h rd hl hL j hj).2 rd hL⟩

/-! ## Complete on every memory holding the caller's words -/

/-- **`f` is complete on every precondition `Pre` that holds on every memory holding the caller's
words `Lin`**, returning the words `Pre` names and no buffer. -/
def CompleteMem (fs : String → ℕ) (cert : String → V → ℕ) (k : ℕ) (f : String)
    (Pre : Reader → List E → List E → Prop) : Prop :=
  ∀ (args rets : List E) (Lin : Layout), (∀ rd, MemL rd Lin → Pre rd args rets) →
    CompleteAt fs cert k f Lin args (Returns rets)

/-- **A pure function lifts its relation**, through its meaning. -/
theorem completeMem_of_iff {fs : String → ℕ} {cert : String → V → ℕ} {S : List String}
    (hS : coreProgram.PureIn S) {f : String} (hf : f ∈ S) {M : Reader → List E → List E → Prop}
    (hiff : ∀ rd args rets, coreProgram.Rel rd f args rets ↔ M rd args rets) (k : ℕ) :
    CompleteMem fs cert k f M := fun _ _ _ h =>
  completeAt_of_rel_pure hS hf (fun rd hL => (hiff rd _ _).mpr (h rd hL)) k

/-- `CompleteRel` from a lift of the precondition to every memory holding `Lin`. -/
theorem completeRel_of_lift {fs : String → ℕ} {cert : String → V → ℕ} {k : ℕ} {f : String}
    {Pre : Reader → List E → List E → Prop} (h : CompleteMem fs cert k f Pre)
    (hlift : ∀ (args rets : List E) (Lin : Layout) (rd1 : Reader), LowDef k rd1 → MemL rd1 Lin →
      (∀ rd, LowDef k rd → MemL rd Lin → Pre rd args rets) → ∀ rd, MemL rd Lin → Pre rd args rets) :
    CompleteRel fs cert k f Pre := by
  intro args rets Lin hpre fp
  classical
  by_cases hex : ∃ rd1, LowDef k rd1 ∧ MemL rd1 Lin
  · obtain ⟨rd1, hl1, hL1⟩ := hex
    exact h args rets Lin (hlift args rets Lin rd1 hl1 hL1 hpre) fp
  · exact ⟨0, [], rets, [], ⟨rfl, rfl⟩, by simp [Within], fun rd hl hL =>
      absurd ⟨rd, hl, by simpa using hL⟩ hex⟩

/-- A precondition that does not read the memory lifts. -/
theorem completeRel_of_const {fs : String → ℕ} {cert : String → V → ℕ} {k : ℕ} {f : String}
    {Pre : List E → List E → Prop} (h : CompleteMem fs cert k f fun _ => Pre) :
    CompleteRel fs cert k f fun _ => Pre :=
  completeRel_of_lift h fun _ _ _ rd1 hl1 hL1 hpre _ _ => hpre rd1 hl1 hL1

theorem isEmpty_filterMap_eq {α β : Type} {f : α → Option β} {l : List α}
    (h : (l.filterMap f).isEmpty = true) : l.filterMap f = [] := List.isEmpty_iff.mp h

/-! ## Purity -/

theorem g1_pure_one {f : String} {fn : Fn} (hf : coreProgram.find? f = some fn)
    (hb : Stmt.pureList [f] fn.body = true) : coreProgram.PureIn [f] := by
  intro g hg fn' hf'
  rw [List.mem_singleton] at hg
  subst hg
  rw [hf, Option.some.injEq] at hf'
  subst hf'
  exact hb

theorem g1_pure_two {f g : String} {fn gn : Fn} (hf : coreProgram.find? f = some fn)
    (hg : coreProgram.find? g = some gn) (hb1 : Stmt.pureList [f, g] fn.body = true)
    (hb2 : Stmt.pureList [f, g] gn.body = true) : coreProgram.PureIn [f, g] := by
  intro h hh hn hfn
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hh
  rcases hh with rfl | rfl
  · rw [hf, Option.some.injEq] at hfn; subst hfn; exact hb1
  · rw [hg, Option.some.injEq] at hfn; subst hfn; exact hb2

/-! ## Certificate facts -/

/-- `decode_query_bits` at depth `d`. -/
def dqName (d : ℕ) : String := s!"decode_query_bits__L{d}"

/-- **The certificate facts of group 1's frame runs**: each run lies in its function's frame. -/
structure G1Certs (fs : String → ℕ) (cert : String → V → ℕ) : Prop where
  grind : cert "grind_check" (.n 34) + 64 ≤ fs "grind_check"
  decode : ∀ d, 14 ≤ d → d ≤ 26 → cert (dqName d) (.n 3) + 192 ≤ fs (dqName d)

end
end LeanVM.Guest.B1
