module

public import LeanVM.Guest.Complete.CallComplete

/-!
# Composing layout-free completeness

A node's completeness (`CallCompletes`) from its own part and its callees': from base `b` the node
holds its own words in `[b, b + m)`, its valuation's path returns, its events hold on every memory
holding its words and its inputs, and each call it enters completes from the bases after its own
(`KidsCompl`), on memories holding the node's words and inputs. The callees are placed one after
another (`kidsCompl_words`); the node's tree is the node over its callees' trees
(`callCompletes_node`).
-/

namespace LeanVM.Guest.Complete

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Memory LeanVM.Node LeanVM.Guest.B1

@[expose] public section

/-! ## Runs of words -/

theorem holdsWords_append {rd : Reader} {W W' : Words} :
    HoldsWords rd (W ++ W') ↔ HoldsWords rd W ∧ HoldsWords rd W' := by
  simp only [HoldsWords, List.mem_append]
  exact ⟨fun h => ⟨fun q hq => h q (Or.inl hq), fun q hq => h q (Or.inr hq)⟩,
    fun h q hq => hq.elim (h.1 q) (h.2 q)⟩

theorem wordsIn_nil (b : ℕ) : WordsIn [] b 0 := ⟨by simp, List.Pairwise.nil⟩

/-- Runs in `[b, b + m)` then runs in `[b + m, b + m + n)` lie in `[b, b + m + n)`, disjoint. -/
theorem WordsIn.append {W W' : Words} {b m n : ℕ} (h : WordsIn W b m) (h' : WordsIn W' (b + m) n) :
    WordsIn (W ++ W') b (m + n) := by
  refine ⟨fun q hq => ?_, List.pairwise_append.mpr ⟨h.2, h'.2, fun q hq q' hq' => ?_⟩⟩
  · rcases List.mem_append.mp hq with hq | hq
    · have := h.1 q hq; omega
    · have := h'.1 q hq; omega
  · have := h.1 q hq; have := h'.1 q' hq'; omega

/-! ## The callees -/

/-- The callees' trees satisfy their predicates: an entered call's tree its predicate. -/
def KidsPost (rd : Reader) : List (Reader → Tree → Prop) → List Call → List Tree → Prop
  | Q :: Qs, c :: cs, t :: ts => (c.taken = true → Q rd t) ∧ KidsPost rd Qs cs ts
  | _, _, _ => True

/-- **Each call of `cs` completes on `σ`'s words**: an entered one by `CallCompletes` under `Pk`,
its tree satisfying its predicate; a skipped one has a phantom frame. -/
def KidsCompl (k : ℕ) (σ : Val) (Pk : Reader → Prop) :
    List (Reader → Tree → Prop) → List Call → Prop
  | _, [] => True
  | Qs, c :: cs =>
    (if c.taken then CallCompletes k c.f (c.args.map σ) (c.rets.map σ) Pk (Qs.headD fun _ _ => True)
      else ∃ σ', Phantom coreProgram (.phantom c.f σ') (c.args.map σ)) ∧
      KidsCompl k σ Pk Qs.tail cs

theorem kidsPost_cons {rd : Reader} {Q : Reader → Tree → Prop} {Qs : List (Reader → Tree → Prop)}
    {c : Call} {cs : List Call} {t : Tree} {ts : List Tree} :
    KidsPost rd (Q :: Qs) (c :: cs) (t :: ts) ↔ (c.taken = true → Q rd t) ∧ KidsPost rd Qs cs ts := by
  rw [KidsPost]

/-- **The callees complete from consecutive bases.** -/
theorem kidsCompl_words {k : ℕ} {σ : Val} {Pk : Reader → Prop} :
    ∀ (cs : List Call) (Qs : List (Reader → Tree → Prop)), KidsCompl k σ Pk Qs cs →
      ∀ b, ∃ (n : ℕ) (W : Words), WordsIn W b n ∧ ∀ rd, LowDef k rd → HoldsWords rd W → Pk rd →
        ∃ ts, Tree.KidsValid coreProgram rd σ cs ts ∧ Tree.BufsOkKids coreProgram ts ∧
          KidsPost rd Qs cs ts
  | [], Qs, _, b => ⟨0, [], wordsIn_nil b, fun _ _ _ _ => ⟨[], by rw [Tree.KidsValid]; trivial,
      by rw [Tree.BufsOkKids]; trivial, by cases Qs <;> simp [KidsPost]⟩⟩
  | c :: cs, Qs, ⟨hc, hcs⟩, b => by
    by_cases ht : c.taken = true
    · simp only [ht, ↓reduceIte] at hc
      obtain ⟨n1, W1, hW1, h1⟩ := hc b
      obtain ⟨n2, W2, hW2, h2⟩ := kidsCompl_words cs Qs.tail hcs (b + n1)
      refine ⟨n1 + n2, W1 ++ W2, hW1.append hW2, fun rd hl hW hP => ?_⟩
      obtain ⟨hw1, hw2⟩ := holdsWords_append.mp hW
      obtain ⟨t, hn, hv, hb, hq⟩ := h1 rd hl hw1 hP
      obtain ⟨ts, hvs, hbs, hqs⟩ := h2 rd hl hw2 hP
      refine ⟨t :: ts, ?_, ?_, ?_⟩
      · rw [Tree.KidsValid]; simp only [ht, ↓reduceIte]; exact ⟨hn, hv, hvs⟩
      · rw [Tree.BufsOkKids]; exact ⟨hb, hbs⟩
      · cases Qs with
        | nil => simp [KidsPost]
        | cons Q Qs => exact kidsPost_cons.mpr ⟨fun _ => hq, hqs⟩
    · have ht' : c.taken = false := by simpa using ht
      simp only [ht', Bool.false_eq_true, ↓reduceIte] at hc
      obtain ⟨σ', hph⟩ := hc
      obtain ⟨n2, W2, hW2, h2⟩ := kidsCompl_words cs Qs.tail hcs b
      refine ⟨n2, W2, hW2, fun rd hl hW hP => ?_⟩
      obtain ⟨ts, hvs, hbs, hqs⟩ := h2 rd hl hW hP
      refine ⟨.phantom c.f σ' :: ts, ?_, ?_, ?_⟩
      · rw [Tree.KidsValid]; simp only [ht', Bool.false_eq_true, ↓reduceIte]; exact ⟨rfl, ⟨⟨c.f, σ', rfl⟩, hph⟩, hvs⟩
      · rw [Tree.BufsOkKids, Tree.BufsOk]; exact ⟨trivial, hbs⟩
      · cases Qs with
        | nil => simp [KidsPost]
        | cons Q Qs => exact kidsPost_cons.mpr ⟨fun h => absurd h ht, hqs⟩

/-! ## A node -/

/-- **A node completes** from its own part: from every base `b`, its own words in `[b, b + m)`, a
valuation whose path returns `rets` from `args`, its events holding on every memory holding its
words and inputs, its callees complete after its own words on such memories, and `Post` of the node
over callees' trees satisfying their predicates. -/
theorem callCompletes_node {k : ℕ} {f : String} {args rets : List E} {Pre : Reader → Prop}
    {Post : Reader → Tree → Prop}
    (h : ∀ b, ∃ (m : ℕ) (Wo : Words) (σ : Val) (fn : Core.Fn) (es : List Ev) (vs : List V)
        (Qs : List (Reader → Tree → Prop)),
      WordsIn Wo b m ∧ coreProgram.find? f = some fn ∧ fn.params.map σ = args ∧
      walk σ fn.body = .ret es vs ∧ vs.map σ = rets ∧
      (∀ rd, LowDef k rd → HoldsWords rd Wo → Pre rd → ∀ e ∈ es, e.Holds rd σ) ∧
      KidsCompl k σ (fun rd => HoldsWords rd Wo ∧ Pre rd) Qs (calls es) ∧
      ∀ rd ts, LowDef k rd → HoldsWords rd Wo → Pre rd → Tree.KidsValid coreProgram rd σ (calls es) ts →
        KidsPost rd Qs (calls es) ts → Post rd (.node f σ (allocs σ es) ts)) :
    CallCompletes k f args rets Pre Post := by
  intro b
  obtain ⟨m, Wo, σ, fn, es, vs, Qs, hWo, hf, hp, hw, hr, hev, hk, hpost⟩ := h b
  obtain ⟨n, Wk, hWk, hks⟩ := kidsCompl_words (calls es) Qs hk (b + m)
  refine ⟨m + n, Wo ++ Wk, hWo.append hWk, fun rd hl hW hP => ?_⟩
  obtain ⟨ho, hkw⟩ := holdsWords_append.mp hW
  obtain ⟨ts, hvs, hbs, hqs⟩ := hks rd hl hkw ⟨ho, hP⟩
  have hev' : Tree.events coreProgram (.node f σ (allocs σ es) ts) = es := by
    simp only [Tree.events, Tree.name, Tree.val, hf, hw]
  refine ⟨.node f σ (allocs σ es) ts, rfl, ⟨fn, hf, hp, es, vs, hw, hr, hev rd hl ho hP, hvs⟩, ?_,
    hpost rd ts hl ho hP hvs hqs⟩
  rw [Tree.BufsOk, hev']
  exact ⟨rfl, hbs⟩

end
end LeanVM.Guest.Complete
