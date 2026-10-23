/-
  LeanVM.Guest.Memory.GuestSize

  The words of the guest's functions that call only themselves, for any frame sizes.
-/

module

public import LeanVM.Guest.Memory.GuestStatic
public import LeanVM.Guest.Memory.SizeTotal

/-!
# Words of the guest's self-calling functions

A function `coreProgram[j]` whose paths call only itself (`blockCallees`) and whose words are
`w` (`blockWords`, both decided by the kernel) has `LocLe` at `fs f + wordsVal fs w` and
`CallsIn` on itself (`self_hyps`). Its static certificate counts its instances (`total_le_self`
at `omegaOf`), so its words are at most that count times `fs f + wordsVal fs w`, for every `fs`.
-/

namespace LeanVM.Guest

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Value Core Memory Data

@[expose] public section

theorem core_find {j : ℕ} (hj : j < coreProgram.length) {g : String} (h : coreProgram[j].name = g) :
    coreProgram.find? g = some coreProgram[j] := h ▸ coreProgram_find_getElem hj

/-- **The hypotheses of `total_le_self` for a guest function calling only itself.** -/
theorem self_hyps {fs : String → ℕ} {j : ℕ} (hj : j < coreProgram.length) {f : String}
    (hn : coreProgram[j].name = f) (hc : (Stmt.blockCallees coreProgram[j].body).all (· == f) = true)
    {w : ℕ × List String} (hw : Stmt.blockWords coreProgram[j].body = some w) :
    LocLe coreProgram fs (fun _ => fs f + wordsVal fs w) (· = f) ∧ CallsIn coreProgram (· = f) := by
  have hf := core_find hj hn
  refine ⟨locLe_of_words fun g hg fn hfn => ?_, callsIn_of_callees fun g hg fn hfn h hh => ?_⟩
  · subst hg
    rw [hf, Option.some.injEq] at hfn
    subst hfn
    exact ⟨w, hw, le_rfl⟩
  · subst hg
    rw [hf, Option.some.injEq] at hfn
    subst hfn
    simpa using List.all_eq_true.mp hc h hh

theorem wordsVal_self (fs : String → ℕ) (f : String) : wordsVal fs (0, [f]) = fs f := by
  simp [wordsVal]

theorem wordsVal_zero (fs : String → ℕ) : wordsVal fs (0, []) = 0 := by
  simp [wordsVal]

private theorem j1 : 1 < coreProgram.length := by rw [coreProgram_length]; decide
private theorem j174 : 174 < coreProgram.length := by rw [coreProgram_length]; decide
private theorem j175 : 175 < coreProgram.length := by rw [coreProgram_length]; decide

/-- **`assert_canonical` allocates its frame.** -/
theorem assert_canonical_totalLe (fs : String → ℕ) :
    TotalLe coreProgram fs "assert_canonical" fun _ => fs "assert_canonical" := by
  have hn : (coreProgram[1]'j1).name = "assert_canonical" := by decide +kernel
  obtain ⟨hl, hc⟩ := self_hyps (fs := fs) j1 hn (by decide +kernel) (w := (0, [])) (by decide +kernel)
  have hcf : staticCertOf "assert_canonical" = .stat [] ⟨8, []⟩ [] := by
    rw [certOf_of_idx (j := 1) (by decide +kernel)]; rfl
  have hω : omegaOf "assert_canonical" = 8 := by
    rw [omegaOf_of_idx (j := 1) (by decide +kernel)]; rfl
  intro rd t args rets htn hv hb
  have hw := weightLe_of_stat coreProgram_checked hcf rd t args rets htn hv hb
  have := total_le_self (ω := omegaOf) (n := 1) hl hc htn hv hb (by rw [hω]; decide) (by rw [hω]; simpa using hw)
  simpa [wordsVal_zero] using this

/-- **`__loop84` from `g^a` to its end `g^64`**: `64 - a` instances, each its frame and the
phantom's. -/
theorem loop84_totalLe (fs : String → ℕ) :
    TotalLeOn coreProgram fs "__loop84" (fun args => ∃ a, args.getD 0 0 = ofK (gpow a) ∧ a < 64)
      fun args => (64 - logG (args.getD 0 0)) * (2 * fs "__loop84") := by
  have hn : (coreProgram[174]'j174).name = "__loop84" := by decide +kernel
  obtain ⟨hl, hc⟩ := self_hyps (fs := fs) j174 hn (by decide +kernel) (w := (0, ["__loop84"]))
    (by decide +kernel)
  have hcf : staticCertOf "__loop84" = .loop (some 64) [] ⟨109, []⟩ [] := by
    rw [certOf_of_idx (j := 174) (by decide +kernel)]; rfl
  have hω : omegaOf "__loop84" = 109 := by
    rw [omegaOf_of_idx (j := 174) (by decide +kernel)]; rfl
  intro rd t args rets htn ⟨a, ha, ha64⟩ hv hb
  have hw := weight_le_of_loop coreProgram_checked hcf htn hv hb ha rfl ha64 (by decide)
    (fun _ h => (List.not_mem_nil h).elim)
  have := total_le_self (ω := omegaOf) (n := 64 - a) hl hc htn hv hb (by rw [hω]; decide)
    (by rw [hω]; simpa [Aff.eval] using hw)
  dsimp only
  rw [ha, logG_spec (by omega)]
  simpa [wordsVal_self, two_mul] using this

/-- **`__loop85` from `g^a` to its end `g^e`, its second argument**: `e - a` instances, each its
frame and the phantom's. -/
theorem loop85_totalLe (fs : String → ℕ) :
    TotalLeOn coreProgram fs "__loop85"
      (fun args => ∃ a e, args.getD 0 0 = ofK (gpow a) ∧ args.getD 1 0 = ofK (gpow e) ∧ a < e ∧
        e < 2 ^ 64 - 1)
      fun args => (logG (args.getD 1 0) - logG (args.getD 0 0)) * (2 * fs "__loop85") := by
  have hn : (coreProgram[175]'j175).name = "__loop85" := by decide +kernel
  obtain ⟨hl, hc⟩ := self_hyps (fs := fs) j175 hn (by decide +kernel) (w := (0, ["__loop85"]))
    (by decide +kernel)
  have hcf : staticCertOf "__loop85" = .loop none [] ⟨20, []⟩ [] := by
    rw [certOf_of_idx (j := 175) (by decide +kernel)]; rfl
  have hω : omegaOf "__loop85" = 20 := by
    rw [omegaOf_of_idx (j := 175) (by decide +kernel)]; rfl
  intro rd t args rets htn ⟨a, e, ha, he, hae, heo⟩ hv hb
  have hw := weight_le_of_loop coreProgram_checked hcf htn hv hb ha he hae heo
    (fun _ h => (List.not_mem_nil h).elim)
  have := total_le_self (ω := omegaOf) (n := e - a) hl hc htn hv hb (by rw [hω]; decide)
    (by rw [hω]; simpa [Aff.eval] using hw)
  dsimp only
  rw [ha, he, logG_spec heo, logG_spec (by omega)]
  simpa [wordsVal_self, two_mul] using this

end
end LeanVM.Guest
