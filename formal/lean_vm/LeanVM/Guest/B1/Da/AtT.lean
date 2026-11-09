/-
  LeanVM.Guest.B1.Da.AtT

  Helpers for `da_verify`'s honest shapes (`Budget.NodeHonest`): callees without predicates,
  the trivial predicates, data and layout monotonicity of the placed relations with trees.

  `da_verify` checks Benedikt Wagner's LeanDA witnesses (`Da.MatrixWitness.Opens`), as ported here.
-/

module

public import LeanVM.Guest.B1.Main.NodeHonestAt
public import LeanVM.Guest.B1.Da.AtBase

/-!
# Helpers for honest shapes

`kidsFromInT_nil_of`: `KidsFromIn` is `KidsFromInT` with no predicates. `kidsT_true`: trivial
predicates hold of any callees. `relAtInT_nodeHonest_true`: a composition by a node with callees
under no predicate has the honest shape with trivial predicates. `relAtInT_dmono`,
`completeAtDT_lin_mono`: as `relAtIn_dmono`, `completeAtD_lin_mono`.
-/

namespace LeanVM.Guest.B1.Da

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Memory
open LeanVM.Guest.Budget (NodeHonest)
open LeanVM.Guest.B1 (CompleteAtDT)
open LeanVM.Guest.B1.Main (Layout MemL RegionL memL_append)

@[expose] public section

variable {fs : String → ℕ} {cert : String → V → ℕ}

theorem kidsFromInT_nil_of {rd : Reader} {σ : Val} {R : ℕ → Prop} :
    ∀ (cs : List Call) (Dacc : ℕ → Prop) (b n : ℕ) (Dend : ℕ → Prop),
      KidsFromIn coreProgram fs cert rd σ R Dacc cs b n Dend →
      KidsFromInT coreProgram fs cert rd σ R Dacc cs [] b n Dend
  | [], _, _, _, _, h => h
  | c :: cs, _, _, _, _, ⟨m, n', Rk, Dk, hn, hR, hc, hk⟩ => ⟨m, n', Rk, Dk, hn, hR, by
      cases ht : c.taken
      · simp only [ht, Bool.false_eq_true, ↓reduceIte] at hc ⊢
        exact hc
      · simp only [ht, ↓reduceIte] at hc ⊢
        exact hc.relAtInT, kidsFromInT_nil_of cs _ _ _ _ hk⟩

theorem kidsT_true : ∀ (cs : List Call) (ks : List Tree) (n : ℕ),
    KidsT cs (List.replicate n fun _ => True) ks
  | [], _, _ => trivial
  | _ :: _, _, 0 => trivial
  | _ :: _, [], _ + 1 => trivial
  | _ :: cs, _ :: ks, n + 1 => ⟨fun _ => trivial, kidsT_true cs ks n⟩

/-- **A composition's node, its callees under no predicate, has its honest shape.** -/
theorem relAtInT_nodeHonest_true {rd : Reader} {σ : Val} {R D : ℕ → Prop} {fp n : ℕ} {f : String}
    {args rets : List E} {fn : Fn} {es : List Ev} {vs : List V} {Q : Val → Prop}
    {cs : Val → List Call} {bs : Val → List ℕ} {Ts0 : List (Tree → Prop)} {k : ℕ}
    (h : RelAtInT coreProgram fs cert rd R D fp n f args rets
      (fun t => ∃ ks, t = .node f σ (allocs σ es) ks ∧ KidsT (calls es) Ts0 ks))
    (hf : coreProgram.find? f = some fn) (hw : walk σ fn.body = .ret es vs) (hQ : Q σ)
    (hcs : calls es = cs σ) (hbs : allocs σ es = bs σ) (hk : (cs σ).length ≤ k) :
    RelAtInT coreProgram fs cert rd R D fp n f args rets
      (NodeHonest coreProgram f Q cs bs (List.replicate k fun _ => True)) :=
  relAtInT_nodeHonest (h.mono fun _ ⟨ks, he, _⟩ => ⟨ks, he, kidsT_true _ _ _⟩) hf hw hQ hcs hbs
    (by simpa using hk)

theorem relAtInT_dmono {rd : Reader} {R D D' : ℕ → Prop} {fp n : ℕ} {f : String}
    {args rets : List E} {T : Tree → Prop}
    (h : RelAtInT coreProgram fs cert rd R D fp n f args rets T) (hD : ∀ i, D' i → D i) :
    RelAtInT coreProgram fs cert rd R D' fp n f args rets T :=
  let ⟨t, ⟨hn, hv, hb, hp, ht, hl, hd⟩, hT⟩ := h
  ⟨t, ⟨hn, hv, hb, hp, ht, hl, fun i hi => hd i (hD i hi)⟩, hT⟩

/-- A callee's completeness reading fewer words holds reading more. -/
theorem completeAtDT_lin_mono {κ : ℕ} {f : String} {Lin Lin' : Layout} {args : List E}
    {Out : List E → Layout → Prop} {T : Tree → Prop}
    (hm : ∀ rd, MemL rd Lin' → MemL rd Lin) (hr : ∀ i, RegionL Lin i → RegionL Lin' i)
    (h : CompleteAtDT fs cert κ f Lin args Out T) : CompleteAtDT fs cert κ f Lin' args Out T := by
  intro fp
  obtain ⟨n, Lown, rets, Lout, ho, hw, hd, hR⟩ := h fp
  refine ⟨n, Lown, rets, Lout, ho, hw, hd, fun rd hl hM => ?_⟩
  obtain ⟨t, ⟨hn, hv, hb, hp, ht, hlo, hdd⟩, hT⟩ := hR rd hl (by
    rw [memL_append] at hM ⊢; exact ⟨hM.1, hm rd hM.2⟩)
  exact ⟨t, ⟨hn, hv, hb, hp, ht, loadsIn_mono t fp hr hlo, hdd⟩, hT⟩

end
end LeanVM.Guest.B1.Da
