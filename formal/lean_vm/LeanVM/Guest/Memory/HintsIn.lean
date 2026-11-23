/-
  LeanVM.Guest.Memory.HintsIn

  Where the hints of a placed call tree write to the heap: in its own data or in a region its
  caller hands it, as `Tree.LoadsIn` for loads.
-/

module

public import LeanVM.Guest.Memory.Regions
public import LeanVM.Guest.Memory
public import LeanVM.Guest.Memory.Fresh
public import LeanVM.Guest.Memory.HintsCheck

/-!
# Hint regions

A hint with a heap destination (`Dest.heap p off len`; a witness entry, or a computed decomposition) writes the words `σ p · g^(off + k)`,
`k < len`, read later or not (`heapHintAddrs`). `Tree.HintsIn P fs cert R p t`: every such word
of an instance is in its subtree's data or the region `R` its caller hands it, a callee getting
its caller's subtree's data and `R`, as `Tree.LoadsIn`. At the root (`hints_insts`), every heap
hint word of a node instance is in the tree's data or `R`. `hintWords` lists them over the
placed instances, and does not see the temporaries' values (`heapHintAddrs_congr`).
-/

namespace LeanVM.Guest.Memory

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core

@[expose] public section

/-- The words an event's hint writes to the heap. -/
def Ev.hintAddrs (σ : Val) : Ev → List K
  | .atom (.hint h) => match (hintDest? h).bind destHeap? with
    | some (p, off, len) => (List.range len).map fun k => (σ p).limb 0 * addressOfIndex (off + k)
    | none => []
  | _ => []

/-- The words a path's hints write to the heap. -/
def heapHintAddrs (σ : Val) (es : List Ev) : List K := es.flatMap (Ev.hintAddrs σ)

variable (P : Core.Program) (fs : String → ℕ) (cert : String → V → ℕ)

mutual
/-- **Heap hints in a region**: every heap word a hint of an instance of `t` placed from `p` writes
is in its subtree's data or `R`; a callee's region is its caller's subtree's data and `R`. -/
def Tree.HintsIn : (ℕ → Prop) → ℕ × ℕ → Tree → Prop
  | R, p, t@(.node f σ bufs kids) =>
      (∀ A ∈ heapHintAddrs σ (t.events P), ∃ i, A = addressOfIndex i ∧ (t.Data P fs cert p i ∨ R i)) ∧
        Tree.HintsInKids (fun i => t.Data P fs cert p i ∨ R i)
          (kidPos fs P.loop p f bufs (kids.map (Tree.sz fs P.loop))) kids
  | _, _, .phantom .. => True

/-- `Tree.HintsIn` of the callees `ks` at `ps`. -/
def Tree.HintsInKids : (ℕ → Prop) → List (ℕ × ℕ) → List Tree → Prop
  | _, _, [] => True
  | _, [], _ :: _ => True
  | R, p :: ps, k :: ks => k.HintsIn R p ∧ Tree.HintsInKids R ps ks
end

/-- The heap words an instance's hints write, none for a phantom. -/
noncomputable def Inst.hintAddrs (I : Inst) : List K :=
  match I.t with
  | .node _ σ _ _ => heapHintAddrs σ (I.t.events P)
  | .phantom .. => []

/-- **The heap words the hints of a placed tree write**, over its instances. -/
noncomputable def hintWords (H : Inst → ℕ → E × E) (hdr : E × E) (T : Tree) : List K :=
  (honestInsts P fs H hdr T).flatMap (Inst.hintAddrs P)

variable {P fs cert}

theorem hintsIn_node {R : ℕ → Prop} {p : ℕ × ℕ} {f : String} {σ : Val} {bufs : List ℕ}
    {kids : List Tree} :
    (Tree.node f σ bufs kids).HintsIn P fs cert R p ↔
      (∀ A ∈ heapHintAddrs σ ((Tree.node f σ bufs kids).events P), ∃ i, A = addressOfIndex i ∧
        ((Tree.node f σ bufs kids).Data P fs cert p i ∨ R i)) ∧
      Tree.HintsInKids P fs cert (fun i => (Tree.node f σ bufs kids).Data P fs cert p i ∨ R i)
        (kidPos fs P.loop p f bufs (kids.map (Tree.sz fs P.loop))) kids := by
  rw [Tree.HintsIn]

theorem hintsIn_phantom {R : ℕ → Prop} {p : ℕ × ℕ} {f : String} {σ : Val} :
    (Tree.phantom f σ).HintsIn P fs cert R p := by
  rw [Tree.HintsIn]; trivial

theorem hintsInKids_cons {R : ℕ → Prop} {p : ℕ × ℕ} {ps : List (ℕ × ℕ)} {k : Tree}
    {ks : List Tree} :
    Tree.HintsInKids P fs cert R (p :: ps) (k :: ks) ↔
      k.HintsIn P fs cert R p ∧ Tree.HintsInKids P fs cert R ps ks := by
  rw [Tree.HintsInKids]

theorem hintsInKids_nil {R : ℕ → Prop} {ps : List (ℕ × ℕ)} :
    Tree.HintsInKids P fs cert R ps [] := by
  cases ps <;> (rw [Tree.HintsInKids]; trivial)

mutual
/-- A larger region keeps the hints in. -/
theorem hintsIn_mono : ∀ (t : Tree) {R R' : ℕ → Prop} (p : ℕ × ℕ), (∀ i, R i → R' i) →
    t.HintsIn P fs cert R p → t.HintsIn P fs cert R' p
  | .node f σ bufs kids, R, R', p, hR, h => by
      rw [hintsIn_node] at h ⊢
      exact ⟨fun A hA => let ⟨i, hi, h'⟩ := h.1 A hA; ⟨i, hi, h'.imp_right (hR i)⟩,
        hintsInKids_mono kids _ (fun i h' => h'.imp_right (hR i)) h.2⟩
  | .phantom .., _, _, _, _, _ => hintsIn_phantom

/-- `hintsIn_mono` for the callees. -/
theorem hintsInKids_mono : ∀ (ks : List Tree) {R R' : ℕ → Prop} (ps : List (ℕ × ℕ)),
    (∀ i, R i → R' i) → Tree.HintsInKids P fs cert R ps ks → Tree.HintsInKids P fs cert R' ps ks
  | [], _, _, _, _, _ => hintsInKids_nil
  | _ :: _, _, _, [], _, _ => by rw [Tree.HintsInKids]; trivial
  | k :: ks, R, R', p :: ps, hR, h => by
      rw [hintsInKids_cons] at h ⊢
      exact ⟨hintsIn_mono k p hR h.1, hintsInKids_mono ks ps hR h.2⟩
end

section Root

variable {H : Inst → ℕ → E × E}

mutual
/-- **Every heap hint word of a node instance is in its tree's data or its region.** -/
theorem hints_insts : ∀ (t : Tree) (R : ℕ → Prop) (p : ℕ × ℕ) (hdr : E × E),
    t.HintsIn P fs cert R p → ∀ I ∈ t.insts fs P.loop H p hdr, ∀ A ∈ I.hintAddrs P,
      ∃ i, A = addressOfIndex i ∧ (t.Data P fs cert p i ∨ R i)
  | .node f σ bufs kids, R, p, hdr, h, I, hI, A, hA => by
      rw [hintsIn_node] at h
      rw [insts_node, List.mem_cons] at hI
      rcases hI with rfl | hI
      · exact h.1 A hA
      · obtain ⟨i, hi, h'⟩ := hintsKids_insts kids _ _ _ 0 h.2 I hI A hA
        refine ⟨i, hi, ?_⟩
        rcases h' with h' | h'
        · exact Or.inl (data_node.mpr (Or.inr h'))
        · exact h'
  | .phantom f σ, _, p, hdr, _, I, hI, _, hA => by
      rw [insts_phantom, List.mem_singleton] at hI
      subst hI
      exact (List.not_mem_nil hA).elim

/-- `hints_insts` for the callees. -/
theorem hintsKids_insts : ∀ (ks : List Tree) (R : ℕ → Prop) (ps : List (ℕ × ℕ)) (J : Inst) (j : ℕ),
    Tree.HintsInKids P fs cert R ps ks → ∀ I ∈ Tree.instsKids fs P.loop H J j ps ks,
      ∀ A ∈ I.hintAddrs P, ∃ i, A = addressOfIndex i ∧ (Tree.DataKids P fs cert ps ks i ∨ R i)
  | [], _, _, _, _, _, I, hI, _, _ => by
      rw [instsKids_nil] at hI; exact (List.not_mem_nil hI).elim
  | _ :: _, _, [], _, _, _, I, hI, _, _ => by
      rw [instsKids_nil_left] at hI; exact (List.not_mem_nil hI).elim
  | k :: ks, R, p :: ps, J, j, h, I, hI, A, hA => by
      rw [hintsInKids_cons] at h
      rw [instsKids_cons, List.mem_append] at hI
      rcases hI with hI | hI
      · obtain ⟨i, hi, h'⟩ := hints_insts k R p _ h.1 I hI A hA
        exact ⟨i, hi, h'.imp_left fun h => dataKids_cons.mpr (Or.inl h)⟩
      · obtain ⟨i, hi, h'⟩ := hintsKids_insts ks R ps J (j + 1) h.2 I hI A hA
        exact ⟨i, hi, h'.imp_left fun h => dataKids_cons.mpr (Or.inr h)⟩
end

end Root

theorem mem_hintUses {h : Hint} {p : V} {off len : ℕ}
    (hp : (hintDest? h).bind destHeap? = some (p, off, len)) : p ∈ hintUses h := by
  have hd : ∀ d : Dest, destHeap? d = some (p, off, len) → p ∈ destUses d := fun d hd => by
    cases d with
    | heap q o l =>
      simp only [destHeap?, Option.some.injEq, Prod.mk.injEq] at hd
      simp [destUses, hd.1]
    | stack _ => simp [destHeap?] at hd
  cases h <;> simp only [hintDest?, Option.bind_some, Option.bind_none, reduceCtorEq] at hp <;>
    simp [hintUses, hd _ hp]

/-- **An event's heap hint words do not see what its uses do not**: a hint's pointer is a use. -/
theorem Ev.hintAddrs_congr {σ σ' : Val} (e : Ev) (h : ∀ v ∈ e.uses, σ' v = σ v) :
    e.hintAddrs σ' = e.hintAddrs σ := by
  unfold Ev.hintAddrs
  split
  · rename_i hh
    split
    · rename_i p off len hp
      rw [h p (by simpa [Ev.uses, atomUses] using mem_hintUses hp)]
    · rfl
  · rfl

/-- **The heap hint words do not see what the uses do not.** -/
theorem heapHintAddrs_congr {σ σ' : Val} {es : List Ev} (h : ∀ e ∈ es, ∀ v ∈ e.uses, σ' v = σ v) :
    heapHintAddrs σ' es = heapHintAddrs σ es :=
  List.flatMap_congr fun e he => e.hintAddrs_congr (h e he)

end
end LeanVM.Guest.Memory
