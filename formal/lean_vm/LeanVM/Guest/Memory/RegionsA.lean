/-
  LeanVM.Guest.Memory.RegionsA

  Where the loads of a call tree placed by the aligned allocator read (`Memory/Regions.lean`'s
  regions, for `Tree.instsA`).
-/

module

public import LeanVM.Guest.Memory.Regions
public import LeanVM.Guest.Memory.PlacedA

/-!
# Load regions, aligned

`Tree.DataA`, `Tree.LoadsInA`, `RelAtInA`, `RelAtInCA`, `KidsFromInA`: `Regions.lean`'s, the
callees at the aligned allocator's positions (`kidPosA`), a region by its end. `loads_instsA`:
every load of an instance reads its tree's data or its region. The composition along a path
(`relAtIn_of_walk` at `Regions.lean`) is B1's, for the aligned allocator to be restated beside it.
-/

namespace LeanVM.Guest.Memory

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core

@[expose] public section

variable (P : Core.Program) (fs : String → ℕ) (al : String → Bool) (cert : String → V → ℕ)

mutual
/-- **A subtree's data**: the own data of its instances placed from `p`. -/
def Tree.DataA (p : ℕ × ℕ) : Tree → ℕ → Prop
  | t@(.node f _ bufs kids), i =>
      ownData cert p.1 p.2 f bufs (t.events P) i ∨
        Tree.DataKidsA (kidPosA fs P.loop al p f bufs kids) kids i
  | .phantom .., _ => False

/-- The data of the callees `ks` placed at `ps`. -/
def Tree.DataKidsA : List (ℕ × ℕ) → List Tree → ℕ → Prop
  | _, [], _ => False
  | [], _ :: _, _ => False
  | p :: ps, k :: ks, i => k.DataA p i ∨ Tree.DataKidsA ps ks i
end

mutual
/-- **Loads in a region**: every load of every instance of `t` placed from `p` reads its
subtree's data or `R`; a callee's region is its caller's subtree's data and `R`. -/
def Tree.LoadsInA : (ℕ → Prop) → ℕ × ℕ → Tree → Prop
  | R, p, t@(.node f σ bufs kids) =>
      (∀ A ∈ loadAddrs σ (t.events P), ∃ i, A = addressOfIndex i ∧ (t.DataA P fs al cert p i ∨ R i)) ∧
        Tree.LoadsInKidsA (fun i => t.DataA P fs al cert p i ∨ R i)
          (kidPosA fs P.loop al p f bufs kids) kids
  | _, _, .phantom .. => True

/-- `Tree.LoadsIn` of the callees `ks` at `ps`. -/
def Tree.LoadsInKidsA : (ℕ → Prop) → List (ℕ × ℕ) → List Tree → Prop
  | _, _, [] => True
  | _, [], _ :: _ => True
  | R, p :: ps, k :: ks => k.LoadsInA R p ∧ Tree.LoadsInKidsA R ps ks
end


/-- **`Program.Rel` placed at `fp`, loading from `R`**: `RelAtA` by a tree whose loads read its
data or `R`, and whose data contains `D`. -/
def RelAtInA (rd : Reader) (R D : ℕ → Prop) (fp e : ℕ) (f : String) (args rets : List E) : Prop :=
  ∃ t : Tree, t.name = f ∧ t.Valid P rd args rets ∧ t.BufsOk P ∧
    t.PlacedA P fs al cert (fp, fp + t.block fs P.loop) ∧ t.endA fs P.loop al (fp + t.block fs P.loop) = e ∧
    t.LoadsInA P fs al cert R (fp, fp + t.block fs P.loop) ∧
    ∀ i, D i → t.DataA P fs al cert (fp, fp + t.block fs P.loop) i

/-- **`RelAtInA` of a loop's iterations from one on**: its frames, `B` words, from `fp`, the rest
of its subtree from `c`, ending at `e`. -/
def RelAtInCA (rd : Reader) (R D : ℕ → Prop) (fp c B e : ℕ) (f : String) (args rets : List E) :
    Prop :=
  ∃ t : Tree, t.name = f ∧ t.Valid P rd args rets ∧ t.BufsOk P ∧ t.PlacedA P fs al cert (fp, c) ∧
    t.block fs P.loop = B ∧ t.endA fs P.loop al c = e ∧ t.LoadsInA P fs al cert R (fp, c) ∧
    ∀ i, D i → t.DataA P fs al cert (fp, c) i

/-- **The callees of the frames `cs` sets up**, one after another from the cursor `b`, the last
ending at `e`, each frame at the aligned base `allocBase (al c.f) b`, each loading from a region
within `R` and the data `Dacc` earlier callees claimed, claiming data `Dk` for the later ones;
`Dend` within all claimed. -/
def KidsFromInA (rd : Reader) (σ : Val) (R : ℕ → Prop) :
    (ℕ → Prop) → List Call → ℕ → ℕ → (ℕ → Prop) → Prop
  | Dacc, [], b, e, Dend => e = b ∧ ∀ i, Dend i → Dacc i
  | Dacc, c :: cs, b, e, Dend => ∃ (m : ℕ) (Rk Dk : ℕ → Prop),
      (∀ i, Rk i → R i ∨ Dacc i) ∧
      (if c.taken then RelAtInA P fs al cert rd Rk Dk (Prover.Exec.allocBase (al c.f) b) m c.f (c.args.map σ)
          (c.rets.map σ)
        else m = Prover.Exec.allocBase (al c.f) b + fs (tailKey c.f)) ∧
      KidsFromInA rd σ R (fun i => Dacc i ∨ (c.taken = true ∧ Dk i)) cs m e Dend

variable {P fs al cert}

/-! ## Unfolding -/

theorem dataA_node {p : ℕ × ℕ} {f : String} {σ : Val} {bufs : List ℕ} {kids : List Tree} {i : ℕ} :
    (Tree.node f σ bufs kids).DataA P fs al cert p i ↔
      ownData cert p.1 p.2 f bufs ((Tree.node f σ bufs kids).events P) i ∨
        Tree.DataKidsA P fs al cert (kidPosA fs P.loop al p f bufs kids) kids i := by
  rw [Tree.DataA]

theorem dataA_phantom {p : ℕ × ℕ} {f : String} {σ : Val} {i : ℕ} :
    ¬ (Tree.phantom f σ).DataA P fs al cert p i := by
  rw [Tree.DataA]; exact id

theorem dataKidsA_cons {p : ℕ × ℕ} {ps : List (ℕ × ℕ)} {k : Tree} {ks : List Tree} {i : ℕ} :
    Tree.DataKidsA P fs al cert (p :: ps) (k :: ks) i ↔ k.DataA P fs al cert p i ∨ Tree.DataKidsA P fs al cert ps ks i := by
  rw [Tree.DataKidsA]

theorem not_dataKidsA_nil {ps : List (ℕ × ℕ)} {i : ℕ} : ¬ Tree.DataKidsA P fs al cert ps [] i := by
  cases ps <;> (rw [Tree.DataKidsA]; exact id)

theorem dataKidsA_append : ∀ {ps : List (ℕ × ℕ)} {ks : List Tree} {ps' : List (ℕ × ℕ)}
    {ks' : List Tree} {i : ℕ},
    ps.length = ks.length →
    (Tree.DataKidsA P fs al cert (ps ++ ps') (ks ++ ks') i ↔
      Tree.DataKidsA P fs al cert ps ks i ∨ Tree.DataKidsA P fs al cert ps' ks' i)
  | [], [], _, _, _, _ => by simp [not_dataKidsA_nil]
  | p :: ps, k :: ks, _, _, _, hl => by
      rw [List.cons_append, List.cons_append, dataKidsA_cons, dataKidsA_cons,
        dataKidsA_append (by simpa using hl), or_assoc]
  | [], _ :: _, _, _, _, hl => absurd hl (by simp)
  | _ :: _, [], _, _, _, hl => absurd hl (by simp)

theorem loadsInA_node {R : ℕ → Prop} {p : ℕ × ℕ} {f : String} {σ : Val} {bufs : List ℕ}
    {kids : List Tree} :
    (Tree.node f σ bufs kids).LoadsInA P fs al cert R p ↔
      (∀ A ∈ loadAddrs σ ((Tree.node f σ bufs kids).events P), ∃ i, A = addressOfIndex i ∧
        ((Tree.node f σ bufs kids).DataA P fs al cert p i ∨ R i)) ∧
      Tree.LoadsInKidsA P fs al cert (fun i => (Tree.node f σ bufs kids).DataA P fs al cert p i ∨ R i)
        (kidPosA fs P.loop al p f bufs kids) kids := by
  rw [Tree.LoadsInA]

theorem loadsInA_phantom {R : ℕ → Prop} {p : ℕ × ℕ} {f : String} {σ : Val} :
    (Tree.phantom f σ).LoadsInA P fs al cert R p := by
  rw [Tree.LoadsInA]; trivial

theorem loadsInKidsA_cons {R : ℕ → Prop} {p : ℕ × ℕ} {ps : List (ℕ × ℕ)} {k : Tree}
    {ks : List Tree} :
    Tree.LoadsInKidsA P fs al cert R (p :: ps) (k :: ks) ↔
      k.LoadsInA P fs al cert R p ∧ Tree.LoadsInKidsA P fs al cert R ps ks := by
  rw [Tree.LoadsInKidsA]

theorem loadsInKidsA_nil {R : ℕ → Prop} {ps : List (ℕ × ℕ)} :
    Tree.LoadsInKidsA P fs al cert R ps [] := by
  cases ps <;> (rw [Tree.LoadsInKidsA]; trivial)

theorem loadsInKidsA_append : ∀ {R : ℕ → Prop} {ps : List (ℕ × ℕ)} {ks : List Tree} {ps' : List (ℕ × ℕ)}
    {ks' : List Tree}, ps.length = ks.length → Tree.LoadsInKidsA P fs al cert R ps ks →
      Tree.LoadsInKidsA P fs al cert R ps' ks' → Tree.LoadsInKidsA P fs al cert R (ps ++ ps') (ks ++ ks')
  | _, [], [], _, _, _, _, h => h
  | _, p :: ps, k :: ks, _, _, hl, h, h' => by
      rw [loadsInKidsA_cons] at h
      rw [List.cons_append, List.cons_append, loadsInKidsA_cons]
      exact ⟨h.1, loadsInKidsA_append (by simpa using hl) h.2 h'⟩
  | _, [], _ :: _, _, _, hl, _, _ => absurd hl (by simp)
  | _, _ :: _, [], _, _, hl, _, _ => absurd hl (by simp)

mutual
/-- A wider region. -/
theorem loadsInA_mono : ∀ (t : Tree) {R R' : ℕ → Prop} (p : ℕ × ℕ), (∀ i, R i → R' i) →
    t.LoadsInA P fs al cert R p → t.LoadsInA P fs al cert R' p
  | .node f σ bufs kids, R, R', p, hR, h => by
      rw [loadsInA_node] at h ⊢
      refine ⟨fun A hA => ?_, loadsInKidsA_mono kids _ (fun i => Or.imp_right (hR i)) h.2⟩
      obtain ⟨i, hi, h'⟩ := h.1 A hA
      exact ⟨i, hi, h'.imp_right (hR i)⟩
  | .phantom .., _, _, _, _, _ => loadsInA_phantom

/-- `loadsInA_mono` for the callees. -/
theorem loadsInKidsA_mono : ∀ (ks : List Tree) {R R' : ℕ → Prop} (ps : List (ℕ × ℕ)),
    (∀ i, R i → R' i) → Tree.LoadsInKidsA P fs al cert R ps ks → Tree.LoadsInKidsA P fs al cert R' ps ks
  | [], _, _, _, _, _ => loadsInKidsA_nil
  | _ :: _, _, _, [], _, _ => by rw [Tree.LoadsInKidsA]; trivial
  | k :: ks, R, R', p :: ps, hR, h => by
      rw [loadsInKidsA_cons] at h ⊢
      exact ⟨loadsInA_mono k p hR h.1, loadsInKidsA_mono ks ps hR h.2⟩
end

/-! ## Composition -/

/-! ## Loads by region only -/

section Pure

mutual
/-- Loads in `R` are loads in `R` and the subtree's data, wherever it is placed. -/
theorem loadsInA_of_loadsR : ∀ (t : Tree) (R : ℕ → Prop) (p : ℕ × ℕ), t.LoadsR P R →
    t.LoadsInA P fs al cert R p
  | .node f σ bufs kids, R, p, h => by
      rw [Tree.LoadsR] at h
      rw [loadsInA_node]
      refine ⟨fun A hA => ?_, loadsInKidsA_mono kids _ (fun i hi => Or.inr hi)
        (loadsInKidsA_of_loadsR kids R _ h.2)⟩
      obtain ⟨i, hi, hR⟩ := h.1 A hA
      exact ⟨i, hi, Or.inr hR⟩
  | .phantom .., _, _, _ => loadsInA_phantom

/-- `loadsInA_of_loadsR` for the callees. -/
theorem loadsInKidsA_of_loadsR : ∀ (ks : List Tree) (R : ℕ → Prop) (ps : List (ℕ × ℕ)),
    Tree.LoadsRKids P R ks → Tree.LoadsInKidsA P fs al cert R ps ks
  | [], _, _, _ => loadsInKidsA_nil
  | _ :: _, _, [], _ => by rw [Tree.LoadsInKidsA]; trivial
  | k :: ks, R, p :: ps, h => by
      rw [Tree.LoadsRKids] at h
      rw [loadsInKidsA_cons]
      exact ⟨loadsInA_of_loadsR k R p h.1, loadsInKidsA_of_loadsR ks R ps h.2⟩
end

end Pure

/-! ## At the root -/

section Root

variable {H : Inst → ℕ → E × E}

mutual
/-- **Every load of an instance reads its tree's data or its region.** -/
theorem loads_instsA : ∀ (t : Tree) (R : ℕ → Prop) (p : ℕ × ℕ) (hdr : E × E),
    t.LoadsInA P fs al cert R p → ∀ I ∈ t.instsA fs P.loop al H p hdr,
      (∃ f σ bufs kids, I.t = .node f σ bufs kids) →
      ∀ A ∈ loadAddrs I.t.val (I.t.events P), ∃ i, A = addressOfIndex i ∧
        (t.DataA P fs al cert p i ∨ R i)
  | .node f σ bufs kids, R, p, hdr, h, I, hI, hn, A, hA => by
      rw [loadsInA_node] at h
      rw [instsA_node, List.mem_cons] at hI
      rcases hI with rfl | hI
      · exact h.1 A hA
      · obtain ⟨i, hi, h'⟩ := loadsKids_instsA kids _ _ _ 0 h.2 I hI hn A hA
        refine ⟨i, hi, ?_⟩
        rcases h' with h' | h'
        · exact Or.inl (dataA_node.mpr (Or.inr h'))
        · exact h'
  | .phantom f σ, _, p, hdr, _, I, hI, hn, _, _ => by
      rw [instsA_phantom, List.mem_singleton] at hI
      subst hI
      obtain ⟨_, _, _, _, h⟩ := hn
      cases h

/-- `loads_instsA` for the callees. -/
theorem loadsKids_instsA : ∀ (ks : List Tree) (R : ℕ → Prop) (ps : List (ℕ × ℕ)) (J : Inst) (j : ℕ),
    Tree.LoadsInKidsA P fs al cert R ps ks → ∀ I ∈ Tree.instsKidsA fs P.loop al H J j ps ks,
      (∃ f σ bufs kids, I.t = .node f σ bufs kids) → ∀ A ∈ loadAddrs I.t.val (I.t.events P),
        ∃ i, A = addressOfIndex i ∧ (Tree.DataKidsA P fs al cert ps ks i ∨ R i)
  | [], _, _, _, _, _, I, hI, _, _, _ => by
      rw [instsKidsA_nil] at hI; exact (List.not_mem_nil hI).elim
  | _ :: _, _, [], _, _, _, I, hI, _, _, _ => by
      rw [instsKidsA_nil_left] at hI; exact (List.not_mem_nil hI).elim
  | k :: ks, R, p :: ps, J, j, h, I, hI, hn, A, hA => by
      rw [loadsInKidsA_cons] at h
      rw [instsKidsA_cons, List.mem_append] at hI
      rcases hI with hI | hI
      · obtain ⟨i, hi, h'⟩ := loads_instsA k R p _ h.1 I hI hn A hA
        exact ⟨i, hi, h'.imp_left fun h => dataKidsA_cons.mpr (Or.inl h)⟩
      · obtain ⟨i, hi, h'⟩ := loadsKids_instsA ks R ps J (j + 1) h.2 I hI hn A hA
        exact ⟨i, hi, h'.imp_left fun h => dataKidsA_cons.mpr (Or.inr h)⟩
end

end Root
end
end LeanVM.Guest.Memory
