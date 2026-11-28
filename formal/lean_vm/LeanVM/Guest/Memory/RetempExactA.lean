/-
  LeanVM.Guest.Memory.RetempExactA

  Exactness survives the aligned re-choice of temporaries, and a node predicate of every node of a
  tree holds at each of its aligned instances.
-/

module

public import LeanVM.Guest.Exact.Every
public import LeanVM.Guest.Memory.RetempA
public import LeanVM.Guest.Memory.MemoryA

/-!
# Exactness on the aligned re-chosen tree

The tag's `Bridge/PairEvery.lean` on `Tree.retempA`: a hint names no temporary (`Program.Fresh`), so
its exactness reads only values the re-choice keeps (`hintExact_congr`), and an exact tree's
re-choice is exact (`every_exact_retempA`). `every_instsA`: a node predicate of every node holds at
each aligned instance's function and valuation.
-/

namespace LeanVM.Guest.Memory

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core

public section

variable {rd : Reader} {σ σ' : Val}

theorem destWords_congr : ∀ {d : Dest}, (∀ v ∈ destUses d, σ' v = σ v) → d.words rd σ' = d.words rd σ
  | .stack vs, h => List.map_congr_left fun v hv ↦ h v hv
  | .heap p off len, h => by simp only [Dest.words, h p (by simp [destUses])]

/-- **A hint's exactness reads only the values it names.** -/
theorem hintExact_congr : ∀ {h : Core.Hint}, (∀ v ∈ hintUses h, σ' v = σ v) → h.Exact rd σ → h.Exact rd σ'
  | .witness .., _, _ => trivial
  | .alloc .., _, _ => trivial
  | .allocDyn .., _, _ => trivial
  | .bits v start nbits d, hu, hx => by
    have hv := hu v (by simp [hintUses])
    have hd := destWords_congr (rd := rd) (d := d) fun w hw ↦ hu w (by simp [hintUses, hw])
    simp only [Core.Hint.Exact] at hx ⊢
    rw [hd, hv, hx]
  | .bitsExp v nbits d, hu, hx => by
    have hv := hu v (by simp [hintUses])
    have hd := destWords_congr (rd := rd) (d := d) fun w hw ↦ hu w (by simp [hintUses, hw])
    obtain ⟨n, h1, h2, h3⟩ := hx
    exact ⟨n, h1, by rw [hv, h2], by rw [hd, h3]⟩
  | .digitsExp v nbits ndigits digitBits start sc d, hu, hx => by
    have hv := hu v (by simp [hintUses])
    have hd := destWords_congr (rd := rd) (d := d) fun w hw ↦ hu w (by simp [hintUses, hw])
    obtain ⟨n, st, h1, h2, h3, h4⟩ := hx
    refine ⟨n, st, h1, by rw [hv, h2], ?_, by rw [hd, h4]⟩
    cases sc with
    | none => exact h3
    | some c => exact ⟨h3.1, by rw [hu c (by simp [hintUses]), h3.2]⟩
  | .windowsExp v start width count d, hu, hx => by
    have hv := hu v (by simp [hintUses])
    have hd := destWords_congr (rd := rd) (d := d) fun w hw ↦ hu w (by simp [hintUses, hw])
    simp only [Core.Hint.Exact] at hx ⊢
    rw [hd, hv, hx]
  | .limbs v ds, hu, hx => by
    have hv := hu v (by simp [hintUses])
    have hd : ds.map σ' = ds.map σ := List.map_congr_left fun w hw ↦ hu w (by simp [hintUses, hw])
    simp only [Core.Hint.Exact] at hx ⊢
    rw [hd, hv, hx]
  | .log2Ceil b nbits floor dst, hu, hx => by
    have hv := hu dst (by simp [hintUses])
    have hd := destWords_congr (rd := rd) (d := b) fun w hw ↦ hu w (by simp [hintUses, hw])
    simp only [Core.Hint.Exact] at hx ⊢
    rw [hd, hv, hx]
  | .inverse x d, hu, hx => by
    have hx' := hu x (by simp [hintUses])
    have hd := hu d (by simp [hintUses])
    simp only [Core.Hint.Exact] at hx ⊢
    rw [hd, hx', hx]

theorem evExact_congr {e : Ev} (hu : ∀ v ∈ e.uses, σ' v = σ v) (hx : e.Exact rd σ) : e.Exact rd σ' := by
  rcases e with a | _ | _ | _
  · cases a with
    | hint h => exact hintExact_congr (h := h) hu hx
    | _ => trivial
  all_goals trivial

variable {P : Core.Program} {fs : String → ℕ} {al : String → Bool} {ν : ℕ → String → Val → V → E}

mutual
/-- **An exact tree's aligned re-choice is exact.** -/
theorem every_exact_retempA (hF : P.Fresh) : ∀ (t : Tree) (pos : ℕ × ℕ), t.Every (ExactAt P rd) →
    (t.retempA P fs al ν pos).Every (ExactAt P rd)
  | .node f σ bufs kids, pos, h => by
    rw [Tree.every_node] at h
    rw [retempA_node, Tree.every_node]
    refine ⟨fun e he ↦ ?_, everyKids_exact_retempA hF _ kids h.2⟩
    rw [events_retemp hF (bufs' := []) (ks' := [])] at he
    have hx := h.1 e he
    unfold Tree.events at he
    simp only [Tree.name, Tree.val] at he
    cases hf : P.find? f with
    | none => simp [hf] at he
    | some fn =>
      simp only [hf] at he
      cases hw : walk σ fn.body with
      | ret es vs =>
        simp only [hw] at he
        exact evExact_congr (evAgree_retemp hF hf hw e he) hx
      | fall _ => simp [hw] at he
      | stuck => simp [hw] at he
  | .phantom f σ, pos, _ => by rw [retempA_phantom]; exact Tree.every_phantom

/-- `every_exact_retempA` for the callees. -/
theorem everyKids_exact_retempA (hF : P.Fresh) : ∀ (ps : List (ℕ × ℕ)) (ks : List Tree),
    Tree.EveryKids (ExactAt P rd) ks → Tree.EveryKids (ExactAt P rd) (Tree.retempKidsA P fs al ν ps ks)
  | _, [], h => by rw [retempKidsA_nil]; exact h
  | [], k :: ks, h => by rw [Tree.retempKidsA]; exact h
  | p :: ps, k :: ks, h => by
    rw [Tree.EveryKids] at h
    rw [retempKidsA_cons, Tree.EveryKids]
    exact ⟨every_exact_retempA hF k p h.1, everyKids_exact_retempA hF ps ks h.2⟩
end

variable {lp : String → Bool} {H : Inst → ℕ → E × E} {Q : String → Val → Prop}

mutual
/-- **A node predicate of every node holds at each aligned instance.** -/
theorem every_instsA : ∀ (t : Tree) (p : ℕ × ℕ) (hdr : E × E), t.Every Q → ∀ I ∈ t.instsA fs lp al H p hdr,
    ∀ f σ bufs kids, I.t = .node f σ bufs kids → Q f σ
  | .node f σ bufs kids, p, hdr, h, I, hI, f', σ', bufs', kids', hIt => by
    rw [Tree.every_node] at h
    rw [instsA_node] at hI
    simp only [List.mem_cons] at hI
    rcases hI with rfl | hI
    · simp only [Tree.node.injEq] at hIt
      obtain ⟨rfl, rfl, -, -⟩ := hIt
      exact h.1
    · exact everyKids_instsA kids _ _ 0 h.2 I hI f' σ' bufs' kids' hIt
  | .phantom f σ, p, hdr, _, I, hI, f', σ', bufs', kids', hIt => by
    rw [instsA_phantom, List.mem_singleton] at hI
    subst hI
    cases hIt

/-- `every_instsA` for the callees. -/
theorem everyKids_instsA : ∀ (ks : List Tree) (ps : List (ℕ × ℕ)) (J : Inst) (j : ℕ), Tree.EveryKids Q ks →
    ∀ I ∈ Tree.instsKidsA fs lp al H J j ps ks, ∀ f σ bufs kids, I.t = .node f σ bufs kids → Q f σ
  | [], _, _, _, _, I, hI => by rw [instsKidsA_nil] at hI; exact (List.not_mem_nil hI).elim
  | _ :: _, [], _, _, _, I, hI => by rw [instsKidsA_nil_left] at hI; exact (List.not_mem_nil hI).elim
  | k :: ks, p :: ps, J, j, h, I, hI => by
    rw [Tree.EveryKids] at h
    rw [instsKidsA_cons, List.mem_append] at hI
    rcases hI with hI | hI
    · exact every_instsA k p _ h.1 I hI
    · exact everyKids_instsA ks ps J (j + 1) h.2 I hI
end

end

end LeanVM.Guest.Memory
