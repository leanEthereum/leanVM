/-
  LeanVM.Guest.Budget.BoundedE

  The tree-predicate forms (`CompleteAtDT`, `CompleteAtL`, `CompleteAtDTB`, `CompleteAtDTBR`, `CompleteAtLR`) gain
  `Tree.Every` for a callee all of whose valid trees satisfy it, such as one exact for free.
-/

module

public import LeanVM.Guest.Budget.BoundedL
public import LeanVM.Guest.B1.Main.CompleteE

/-!
# Tree-predicate forms with `Every`

The tree-predicate forms carry any predicate through their composition (`kidsFromInT_of_kidsDT`,
`kidsFromInT_of_kidsDTB`, `kidsFromInT_of_kidsDTBR`), and `RelAtInT.every_of_walk` puts a node satisfying `Every Q` on
its callees' trees satisfying `T ∧ Every Q`. At a callee all of whose valid trees satisfy it, `andEvery` adds it:
on every memory (`EveryAll`) for the forms whose predicate does not read the memory, on the memory served (`EveryOn`)
for the others. `everyAll_exact`: a function passing `exactFree` is exact on every memory. `completeAt_leafBE`: a leaf
with its pops and its valuation's `Q`, the form a leaf supplies exactness in.
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Memory
open LeanVM.Guest.B1.Main (Layout MemL RegionL)

@[expose] public section

/-- **Every valid tree of `f` at `args` satisfies `Every (Q rd')` on every memory `rd'`**, its validity on a memory
`rd` of the caller's words. -/
def EveryAll (k : ℕ) (f : String) (Lin : Layout) (args : List E) (Q : Reader → String → Val → Prop) : Prop :=
  ∀ rd, LowDef k rd → MemL rd Lin → ∀ (t : Tree) (rets : List E), t.name = f → t.Valid coreProgram rd args rets →
    ∀ rd', t.Every (Q rd')

variable {fs : String → ℕ} {cert : String → V → ℕ} {k : ℕ} {f : String} {Lin : Layout} {args : List E}
  {Out : List E → Layout → Prop} {Q : Reader → String → Val → Prop}

/-- **A function passing `exactFree` is exact**, on every memory. -/
theorem everyAll_exact (hg : ExactFreeG f) : EveryAll k f Lin args fun rd => ExactAt coreProgram rd :=
  fun _ _ _ _ _ hn hv rd' => every_exact_of_free hg hv hn rd'

theorem EveryAll.everyOn (h : EveryAll k f Lin args Q) : EveryOn k f Lin args Q :=
  fun rd hl hm t rets hn hv => h rd hl hm t rets hn hv rd

theorem CompleteAtDT.andEvery {T : Tree → Prop} (h : CompleteAtDT fs cert k f Lin args Out T)
    (hQ : EveryAll k f Lin args Q) :
    CompleteAtDT fs cert k f Lin args Out fun t => T t ∧ ∀ rd, t.Every (Q rd) := fun fp =>
  let ⟨n, Lown, rets, Lout, ho, hw, hd, hr⟩ := h fp
  ⟨n, Lown, rets, Lout, ho, hw, hd, fun rd hl hm =>
    let ⟨t, ht, hT⟩ := hr rd hl hm
    ⟨t, ht, hT, hQ rd hl (Main.memL_append.mp hm).2 t rets ht.1 ht.2.1⟩⟩

theorem CompleteAtL.andEvery {T : Tree → Prop} {Bd : ℕ → Prop} (h : CompleteAtL fs cert k f Lin args Out T Bd)
    (hQ : EveryAll k f Lin args Q) :
    CompleteAtL fs cert k f Lin args Out (fun t => T t ∧ ∀ rd, t.Every (Q rd)) Bd :=
  let ⟨B, hB⟩ := h
  ⟨B, fun fp c hc =>
    let ⟨n, Lown, rets, Lout, hn, ho, hw, hd, hr⟩ := hB fp c hc
    ⟨n, Lown, rets, Lout, hn, ho, hw, hd, fun rd hl hm =>
      let ⟨t, ht, hT⟩ := hr rd hl hm
      ⟨t, ht, hT, hQ rd hl (Main.memL_append.mp hm).2 t rets ht.1 ht.2.1⟩⟩⟩

theorem CompleteAtDTB.andEvery {T : Tree → Prop} {B : ℕ} (h : CompleteAtDTB fs cert k f Lin args Out T B)
    (hQ : EveryAll k f Lin args Q) :
    CompleteAtDTB fs cert k f Lin args Out (fun t => T t ∧ ∀ rd, t.Every (Q rd)) B :=
  h.and_valid_on fun rd hl hm t rets hn hv _ => hQ rd hl hm t rets hn hv

theorem CompleteAtDTBR.andEvery {T : Reader → Tree → Prop} {B : ℕ}
    (h : CompleteAtDTBR fs cert k f Lin args Out T B) (hQ : EveryOn k f Lin args Q) :
    CompleteAtDTBR fs cert k f Lin args Out (fun rd t => T rd t ∧ t.Every (Q rd)) B := fun fp =>
  let ⟨n, Lown, rets, Lout, hn, ho, hw, hd, hr⟩ := h fp
  ⟨n, Lown, rets, Lout, hn, ho, hw, hd, fun rd hl hm =>
    let ⟨t, ht, hT⟩ := hr rd hl hm
    ⟨t, ht, hT, hQ rd hl (Main.memL_append.mp hm).2 t rets ht.1 ht.2.1⟩⟩

theorem CompleteAtLR.andEvery {T : Reader → Tree → Prop} {Bd : ℕ → Prop}
    (h : CompleteAtLR fs cert k f Lin args Out T Bd) (hQ : EveryOn k f Lin args Q) :
    CompleteAtLR fs cert k f Lin args Out (fun rd t => T rd t ∧ t.Every (Q rd)) Bd :=
  let ⟨B, hB⟩ := h
  ⟨B, fun fp c hc =>
    let ⟨n, Lown, rets, Lout, hn, ho, hw, hd, hr⟩ := hB fp c hc
    ⟨n, Lown, rets, Lout, hn, ho, hw, hd, fun rd hl hm =>
      let ⟨t, ht, hT⟩ := hr rd hl hm
      ⟨t, ht, hT, hQ rd hl (Main.memL_append.mp hm).2 t rets ht.1 ht.2.1⟩⟩⟩

/-- **A bounded callee with its pops and `Every (Q rd)`**: the `E` form's predicate as one of the memory. -/
theorem CompleteAtDTBR.withPopsEvery {T : Reader → Tree → Prop} {B : ℕ} {ps : Reader → List Pop}
    (h : CompleteAtDTBR fs cert k f Lin args Out T B)
    (hp : ∀ rd, LowDef k rd → MemL rd Lin → ∀ t rets, t.Valid coreProgram rd args rets → T rd t →
      t.pops coreProgram rd = ps rd) (hQ : EveryOn k f Lin args Q) :
    CompleteAtDTBR fs cert k f Lin args Out
      (fun rd t => (T rd t ∧ t.pops coreProgram rd = ps rd) ∧ t.Every (Q rd)) B :=
  (h.withPops hp).andEvery hQ

/-! ## Leaves -/

/-- **A leaf with its pops and `Every (Q rd)`**: `completeAt_leafB`, its path popping `ps rd` and its valuation
satisfying `Q rd f`. -/
theorem completeAt_leafBE {fn : Fn} (hf : coreProgram.find? f = some fn) (hl : coreProgram.loop f = false)
    (k : ℕ) (Lin : Layout) (args rets : List E) (sizes : List ℕ) (ps : Reader → List Pop)
    (own : ℕ → List (List E)) (hown : ∀ fp, List.Forall₂ (fun c s => c.length ≤ s) (own fp) sizes)
    (hσ : ∀ fp rd, LowDef k rd → MemL rd (bufL (fp + fs f) sizes (own fp)) → MemL rd Lin →
      ∃ (σ : Val) (es : List Ev) (vs : List V), fn.params.map σ = args ∧
        walk σ fn.body = .ret es vs ∧ vs.map σ = rets ∧ (∀ e ∈ es, e.Holds rd σ) ∧
        calls es = [] ∧ addrs es = [] ∧ allocs σ es = sizes ∧
        (allocDsts es).map σ = (bases (fp + fs f) sizes).map (fun b => ofK (addressOfIndex b)) ∧
        (∀ A ∈ loadAddrs σ es, ∃ i, A = addressOfIndex i ∧
          (RegionL (bufL (fp + fs f) sizes (own fp)) i ∨ RegionL Lin i)) ∧
        splice rd σ es [] = ps rd ∧ Q rd f σ) :
    CompleteAtDTBR fs cert k f Lin args (Returns rets)
      (fun rd t => t.pops coreProgram rd = ps rd ∧ t.Every (Q rd)) (fs f + sizes.sum) := by
  intro fp
  refine ⟨fs f + sizes.sum, bufL (fp + fs f) sizes (own fp), rets, [], le_rfl, ⟨rfl, rfl⟩,
    by simpa using (bufL_within _ _ _ (hown fp)).mono (by omega) (by omega),
    by simpa using bufL_disj _ _ _ (hown fp), fun rd hlow hL => ?_⟩
  simp only [List.nil_append] at hL
  obtain ⟨hL1, hL2⟩ := Main.memL_append.mp hL
  obtain ⟨σ, es, vs, hp, hw, hr, hes, hc, ha, hal, hbuf, hload, hps, hq⟩ := hσ fp rd hlow hL1 hL2
  have h := relAtInPE_of_walk (P := coreProgram) (fs := fs) (cert := cert) (Q := Q rd) (R := RegionL Lin)
    (D := RegionL []) (Dk := fun _ => False) (N := 0) (fp := fp) (pss := []) coreProgram_wf hf (Or.inl hl) hp hw
    hr hes (by rw [hal]; exact hbuf) (by rw [ha]; simp)
    (by rw [hc]; exact ⟨rfl, fun _ h => h⟩) (fun A hA => ?_)
    (fun i hi => by obtain ⟨q, hq, _⟩ := hi; simp at hq) hps hq
  · rw [hal] at h; simpa using h
  · obtain ⟨i, hi, h | h⟩ := hload A hA
    · exact ⟨i, hi, Or.inl (Or.inl (by rw [hal]; exact bufL_region _ _ _ (hown fp) i h))⟩
    · exact ⟨i, hi, Or.inr (Or.inl h)⟩

end
end LeanVM.Guest.B1
