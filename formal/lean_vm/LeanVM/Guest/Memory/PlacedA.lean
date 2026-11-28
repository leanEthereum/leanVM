/-
  LeanVM.Guest.Memory.PlacedA

  Call trees placed by the aligned allocator (`Memory/AllocA.lean`): `Memory/Placed.lean`'s
  placement, every callee where Hotwire's executor puts it.
-/

module

public import LeanVM.Guest.Memory.Placed
public import LeanVM.Guest.Memory.AllocA

/-!
# Placed call trees, aligned

`Tree.PlacedA P fs al cert p t`: `Tree.Placed`, the callees at the aligned allocator's positions
(`kidPosA`); `RelAtA`, `KidsFromA`: `RelAt`, `KidsFrom` with each region's end, its frame at the
aligned base. `insts_placedAtA`, `Inst.nodeAtA`, `eqns_instsA`: `Placed.lean`'s, for `Tree.instsA`.
-/

namespace LeanVM.Guest.Memory

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core

@[expose] public section

variable (P : Core.Program) (fs : String → ℕ) (al : String → Bool) (cert : String → V → ℕ)

mutual
/-- **A placed tree**: every instance of `t` placed from `p` is `NodeAt` its position. -/
def Tree.PlacedA (p : ℕ × ℕ) : Tree → Prop
  | t@(.node f σ bufs kids) =>
      NodeAt cert p f σ bufs (t.events P) ∧
        Tree.PlacedKidsA (kidPosA fs P.loop al p f bufs kids) kids
  | .phantom .. => True

/-- The callees `ks` placed at `ps`. -/
def Tree.PlacedKidsA : List (ℕ × ℕ) → List Tree → Prop
  | _, [] => True
  | [], _ :: _ => True
  | p :: ps, k :: ks => k.PlacedA p ∧ Tree.PlacedKidsA ps ks
end

/-- **`Program.Rel` placed at `fp`**: a valid tree of `f` on `args`, `rets`, its `HeapBuf`s those
of its paths, placed fresh at `fp`, its region ending at `e`. -/
def RelAtA (rd : Reader) (fp e : ℕ) (f : String) (args rets : List E) : Prop :=
  ∃ t : Tree, t.name = f ∧ t.Valid P rd args rets ∧ t.BufsOk P ∧
    t.PlacedA P fs al cert (fp, fp + t.block fs P.loop) ∧ t.endA fs P.loop al (fp + t.block fs P.loop) = e

/-- **The callees of the frames `cs` sets up**, their regions one after another from the cursor
`b`, the last ending at `e`: each frame at the aligned base `allocBase (al c.f) b`, each call
entered `RelAtA` there, each not entered a phantom of its callee's tail (`tailKey`). -/
def KidsFromA (rd : Reader) (σ : Val) : List Call → ℕ → ℕ → Prop
  | [], b, e => e = b
  | c :: cs, b, e => ∃ m,
      (if c.taken then RelAtA P fs al cert rd (Prover.Exec.allocBase (al c.f) b) m c.f (c.args.map σ) (c.rets.map σ)
        else m = Prover.Exec.allocBase (al c.f) b + fs (tailKey c.f)) ∧
      KidsFromA rd σ cs m e

variable {P fs al cert}

/-- A placed relation is a relation. -/
theorem RelAtA.rel {rd : Reader} {fp n : ℕ} {f : String} {args rets : List E}
    (h : RelAtA P fs al cert rd fp n f args rets) : P.Rel rd f args rets :=
  let ⟨t, hn, hv, _⟩ := h
  hn ▸ hv.rel t

theorem placedA_node {p : ℕ × ℕ} {f : String} {σ : Val} {bufs : List ℕ} {kids : List Tree} :
    (Tree.node f σ bufs kids).PlacedA P fs al cert p ↔
      NodeAt cert p f σ bufs ((Tree.node f σ bufs kids).events P) ∧
        Tree.PlacedKidsA P fs al cert (kidPosA fs P.loop al p f bufs kids) kids := by
  rw [Tree.PlacedA]

theorem placedA_phantom {p : ℕ × ℕ} {f : String} {σ : Val} : (Tree.phantom f σ).PlacedA P fs al cert p := by
  rw [Tree.PlacedA]; trivial

theorem placedKidsA_cons {p : ℕ × ℕ} {ps : List (ℕ × ℕ)} {k : Tree} {ks : List Tree} :
    Tree.PlacedKidsA P fs al cert (p :: ps) (k :: ks) ↔ k.PlacedA P fs al cert p ∧ Tree.PlacedKidsA P fs al cert ps ks := by
  rw [Tree.PlacedKidsA]

theorem placedKidsA_nil {ps : List (ℕ × ℕ)} : Tree.PlacedKidsA P fs al cert ps [] := by
  cases ps <;> (rw [Tree.PlacedKidsA]; trivial)

theorem placedKidsA_append : ∀ {ps : List (ℕ × ℕ)} {ks : List Tree} {ps' : List (ℕ × ℕ)}
    {ks' : List Tree},
    ps.length = ks.length → Tree.PlacedKidsA P fs al cert ps ks → Tree.PlacedKidsA P fs al cert ps' ks' →
      Tree.PlacedKidsA P fs al cert (ps ++ ps') (ks ++ ks')
  | [], [], _, _, _, _, h => h
  | p :: ps, k :: ks, _, _, hl, h, h' => by
      rw [placedKidsA_cons] at h
      rw [List.cons_append, List.cons_append, placedKidsA_cons]
      exact ⟨h.1, placedKidsA_append (by simpa using hl) h.2 h'⟩
  | [], _ :: _, _, _, hl, _, _ => absurd hl (by simp)
  | _ :: _, [], _, _, hl, _, _ => absurd hl (by simp)


/-! ## Subtrees with nothing to place -/

section Pure

variable {S : List String} {σ : Val} {rd : Reader}

variable {rd : Reader}

mutual
/-- A valid tree of a function of a pure set is placed anywhere. -/
theorem placedA_of_pure (hS : P.PureIn S) : ∀ (t : Tree) {args rets : List E},
    t.Valid P rd args rets → t.BufsOk P → t.name ∈ S → ∀ p, t.PlacedA P fs al cert p
  | .node f σ bufs kids, _, _, ⟨fn, hf, _, es, vs, hw, _, _, hk⟩, hb, hn, p => by
      have hpure : ∀ e ∈ es, e.pure S := by
        have := walk_pure (σ := σ) fn.body (hS f hn fn hf)
        rwa [hw] at this
      rw [Tree.BufsOk, events_node hf hw, allocs_pure hpure] at hb
      obtain ⟨rfl, hkb⟩ := hb
      rw [placedA_node, events_node hf hw]
      refine ⟨⟨by rw [allocDsts_pure hpure]; rfl, fun q hq => by
        rw [addrs_pure hpure] at hq; exact (List.not_mem_nil hq).elim⟩, ?_⟩
      exact placedKidsA_of_pure hS kids σ (calls es) hk hkb (calls_pure hpure) _
  | .phantom .., _, _, h, _, _, _ => h.elim

/-- `placedA_of_pure` for the callees. -/
theorem placedKidsA_of_pure (hS : P.PureIn S) : ∀ (ks : List Tree) (σ : Val) (cs : List Call),
    Tree.KidsValid P rd σ cs ks → Tree.BufsOkKids P ks → (∀ c ∈ cs, c.f ∈ S) →
      ∀ ps, Tree.PlacedKidsA P fs al cert ps ks
  | [], _, _, _, _, _, _ => placedKidsA_nil
  | _ :: _, _, _, _, _, _, [] => by rw [Tree.PlacedKidsA]; trivial
  | k :: ks, σ, c :: cs, ⟨hn, hc, hks⟩, hb, hS', p :: ps => by
      rw [Tree.BufsOkKids] at hb
      rw [placedKidsA_cons]
      refine ⟨?_, placedKidsA_of_pure hS ks σ cs hks hb.2
        (fun c' hc' => hS' c' (List.mem_cons_of_mem _ hc')) ps⟩
      by_cases ht : c.taken = true
      · rw [ite_eq_left ht] at hc
        exact placedA_of_pure hS k hc hb.1 (hn ▸ hS' c List.mem_cons_self) p
      · rw [ite_eq_right ht] at hc
        obtain ⟨⟨f, σ', rfl⟩, -⟩ := hc
        exact placedA_phantom
  | _ :: _, _, [], h, _, _, _ :: _ => h.elim
end

end Pure

/-! ## The instances of a placed tree -/

section Insts

variable {lp : String → Bool} {H : Inst → ℕ → E × E}

mutual
/-- **Every instance of a placed tree is placed at its frame.** -/
theorem insts_placedAtA : ∀ (t : Tree) (p : ℕ × ℕ) (hdr : E × E), t.PlacedA P fs al cert p →
    ∀ I ∈ t.instsA fs P.loop al H p hdr, I.t.PlacedA P fs al cert (I.fp, I.cur)
  | .node f σ bufs kids, p, hdr, hp, I, hI => by
      rw [instsA_node, List.mem_cons] at hI
      rcases hI with rfl | hI
      · exact hp
      · rw [placedA_node] at hp
        exact instsKids_placedAtA kids _ _ 0 hp.2 I hI
  | .phantom .., p, hdr, _, I, hI => by
      rw [instsA_phantom, List.mem_singleton] at hI
      subst hI
      exact placedA_phantom

/-- `insts_placedAtA` for the callees. -/
theorem instsKids_placedAtA : ∀ (ks : List Tree) (ps : List (ℕ × ℕ)) (J : Inst) (j : ℕ),
    Tree.PlacedKidsA P fs al cert ps ks → ∀ I ∈ Tree.instsKidsA fs P.loop al H J j ps ks,
      I.t.PlacedA P fs al cert (I.fp, I.cur)
  | [], _, _, _, _, I, hI => by rw [instsKidsA_nil] at hI; exact (List.not_mem_nil hI).elim
  | _ :: _, [], _, _, _, I, hI => by
      rw [instsKidsA_nil_left] at hI; exact (List.not_mem_nil hI).elim
  | k :: ks, p :: ps, J, j, hp, I, hI => by
      rw [placedKidsA_cons] at hp
      rw [instsKidsA_cons, List.mem_append] at hI
      rcases hI with hI | hI
      · exact insts_placedAtA k p _ hp.1 I hI
      · exact instsKids_placedAtA ks ps J (j + 1) hp.2 I hI
end

/-- **An instance's `HeapBuf` pointers are its `bufBases`, its `frameAddr`s in its frame.** -/
theorem Inst.nodeAtA {I : Inst} (hp : I.t.PlacedA P fs al cert (I.fp, I.cur)) (hI : I.PlacedA fs P.loop al)
    {f : String} {σ : Val} {bufs : List ℕ} {kids : List Tree} (ht : I.t = .node f σ bufs kids) :
    (allocDsts (I.t.events P)).map σ = I.bufBases.map (fun b => ofK (addressOfIndex b)) ∧
      ∀ q ∈ addrs (I.t.events P), σ q.1 = ofK (addressOfIndex (I.fp + cert f q.2)) := by
  rw [ht, placedA_node] at hp
  rw [hI.2.1, ht]
  exact hp.1

theorem length_kidPosA_kids {p : ℕ × ℕ} {f : String} {bufs : List ℕ} {kids : List Tree} :
    (kidPosA fs lp al p f bufs kids).length = kids.length := by
  rw [length_kidPosA]

mutual
/-- **Every equation is an instance's**: an atom's on the path of a node instance. -/
theorem eqns_instsA : ∀ (t : Tree) (p : ℕ × ℕ) (hdr : E × E), ∀ q ∈ t.eqns P,
    ∃ I ∈ t.instsA fs lp al H p hdr, (∃ f σ bufs kids, I.t = .node f σ bufs kids) ∧
      ∃ a, Ev.atom a ∈ I.t.events P ∧ q ∈ atomEqns I.t.val a
  | .node f σ bufs kids, p, hdr, q, hq => by
      rw [Tree.eqns, List.mem_append] at hq
      rw [instsA_node]
      rcases hq with hq | hq
      · obtain ⟨e, he, hqe⟩ := List.mem_flatMap.mp hq
        cases e with
        | atom a => exact ⟨_, List.mem_cons_self, ⟨f, σ, bufs, kids, rfl⟩, a, he, hqe⟩
        | inK _ => exact (List.not_mem_nil hqe).elim
        | call _ _ _ => exact (List.not_mem_nil hqe).elim
        | skip _ _ => exact (List.not_mem_nil hqe).elim
      · obtain ⟨J, hJ, h⟩ := eqnsKids_instsA kids _ _ 0 length_kidPosA_kids q hq
        exact ⟨J, List.mem_cons_of_mem _ hJ, h⟩
  | .phantom .., _, _, q, hq => by rw [Tree.eqns] at hq; exact (List.not_mem_nil hq).elim

/-- `eqns_instsA` for the callees. -/
theorem eqnsKids_instsA : ∀ (ks : List Tree) (ps : List (ℕ × ℕ)) (I : Inst) (j : ℕ),
    ps.length = ks.length →
    ∀ q ∈ Tree.eqnsKids P ks, ∃ J ∈ Tree.instsKidsA fs lp al H I j ps ks,
      (∃ f σ bufs kids, J.t = .node f σ bufs kids) ∧ ∃ a, Ev.atom a ∈ J.t.events P ∧ q ∈ atomEqns J.t.val a
  | [], _, _, _, _, q, hq => by rw [Tree.eqnsKids] at hq; exact (List.not_mem_nil hq).elim
  | _ :: _, [], _, _, hl, _, _ => absurd hl (by simp)
  | k :: ks, p :: ps, I, j, hl, q, hq => by
      rw [Tree.eqnsKids, List.mem_append] at hq
      rw [instsKidsA_cons]
      rcases hq with hq | hq
      · obtain ⟨J, hJ, h⟩ := eqns_instsA k p (H I j) q hq
        exact ⟨J, List.mem_append_left _ hJ, h⟩
      · obtain ⟨J, hJ, h⟩ := eqnsKids_instsA ks ps I (j + 1) (by simpa using hl) q hq
        exact ⟨J, List.mem_append_right _ hJ, h⟩
end

end Insts
end
end LeanVM.Guest.Memory
