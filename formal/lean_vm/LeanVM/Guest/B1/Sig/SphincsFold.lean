/-
  LeanVM.Guest.B1.Sig.SphincsFold

  `sp_fold`, `sp_subtree_arm` and `sp_tree_arm` (G:2486-2522): a leaf of a forest tree folded up its
  hinted path to the tree's two top nodes, one arm per leaf index, sound.
-/

module

public import LeanVM.Guest.B1.Sig.XmssScheme
public import LeanVM.Guest.B1.Sig.Template

namespace LeanVM.Guest.B1.Sig

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.Verifier
open LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Value

@[expose] public section

variable {C : CallRel} {rd : Reader}

/-- The address cells of a fold at leaf `index` over the tree's address `adr`. -/
def foldAddr (σ : Val) (adr : V) (F : Fold) (index : Nat) : Nat → E := fun l => σ adr + word (F.addr index l) 0 0

/-- **A level is sound**: the node is the hash of the pair in the order of the bit. -/
theorem spLevel_sound {σ : Val} {pp md adr cur o0 o1 : V} {addr b : Nat} {bit : Bool}
    (hmd : σ md = mdw 64 true) {next : Prop} {kret : List E → Prop}
    (h : Stmt.HoldsList C rd σ (spLevel pp md adr addr bit cur b o0 o1) next kret) :
    σ o0 = (hcell [σ pp, σ adr + word addr 0 0, if bit then σ (.n b) else σ cur,
      if bit then σ cur else σ (.n b)]).1 ∧ next := by
  simp only [spLevel, hintW, cst, ivs, addS, List.cons_append, List.nil_append, holdsList_cons_atom,
    Atom.Holds, true_and] at h
  obtain ⟨h1, h2, h3, h4, h⟩ := h
  cases bit <;> simp only [b2s, Bool.false_eq_true, ↓reduceIte, holdsList_cons_atom, holdsList_nil,
    Atom.Holds] at h ⊢ <;> obtain ⟨hc, hn⟩ := h <;> rw [h2, h1, h3, h4, hmd] at hc <;>
    exact ⟨congrArg Prod.fst (compress4_iff.mp hc).2, hn⟩

/-- **Levels of a fold are sound.** -/
theorem spLevels_sound {σ : Val} {pp md adr : V} (F : Fold) (index : Nat) (hmd : σ md = mdw 64 true) :
    ∀ (m l : Nat) (cur : V) (b : Nat) {next : Prop} {kret : List E → Prop},
      Stmt.HoldsList C rd σ (spLevels pp md adr F index m l cur b).1 next kret →
      (∃ sibs : Nat → E, σ (spLevels pp md adr F index m l cur b).2 =
        mFold (σ pp) (foldAddr σ adr F index) (fun l => index.testBit l) sibs m l (σ cur)) ∧ next
  | 0, _, _, _, _, _, h => ⟨⟨fun _ => 0, rfl⟩, h⟩
  | m + 1, l, cur, b, next, kret, h => by
      simp only [spLevels, holdsList_append] at h ⊢
      obtain ⟨hl, h⟩ := spLevel_sound hmd h
      obtain ⟨⟨sibs, hs⟩, hn⟩ := spLevels_sound F index hmd m (l + 1) _ _ h
      refine ⟨⟨fun l' => if l' = l then σ (.n b) else sibs l', ?_⟩, hn⟩
      rw [hs, hl, mFold]
      refine (mFold_congr _ _ _ m (l + 1) (sibs := sibs) (sibs' := fun l' => if l' = l then σ (.n b) else sibs l')
        (fun l' h1 _ => by simp [show l' ≠ l by omega]) _).trans ?_
      simp [foldAddr]

theorem mFold_last (pp : E) (A : Nat → E) (bits : Nat → Bool) (sibs : Nat → E) (m : Nat) (x s : E) :
    mFold pp A bits (fun l => if l = m then s else sibs l) (m + 1) 0 x =
      (hcell [pp, A m, if bits m then s else mFold pp A bits sibs m 0 x,
        if bits m then mFold pp A bits sibs m 0 x else s]).1 := by
  rw [mFold_succ, Nat.zero_add, mFold_congr _ _ _ m 0 (sibs := fun l => if l = m then s else sibs l)
    (sibs' := sibs) (fun l' _ h2 => by simp [show l' ≠ m by omega])]
  simp

/-- **An arm of a fold is sound**: the node it reaches, `height - 1` levels up, lands in the
output its top bit names; the arm's constants land in `ret1` and `ret2`. -/
theorem spArm_sound {σ : Val} {pp md adr node ret1 ret2 : V} {F : Fold} {out : Nat → V} {r1 r2 : E}
    {index b : Nat} (hmd : σ md = mdw 64 true) (hF : 2 ≤ F.height) {next : Prop} {kret : List E → Prop}
    (h : Stmt.HoldsList C rd σ (spArm pp md adr node F out ret1 ret2 r1 r2 index b) next kret) :
    (∃ sibs : Nat → E, σ (out (2 * (index / 2 ^ (F.height - 1)))) =
      mFold (σ pp) (foldAddr σ adr F index) (fun l => index.testBit l) sibs (F.height - 1) 0 (σ node)) ∧
      σ ret1 = r1 ∧ σ ret2 = r2 ∧ next := by
  simp only [spArm, holdsList_append] at h
  obtain ⟨⟨sibs, hs⟩, h⟩ := spLevels_sound F index hmd _ 0 node b h
  obtain ⟨hl, h⟩ := spLevel_sound hmd h
  simp only [hintW, holdsList_cons_atom, holdsList_nil, Atom.Holds, true_and] at h
  obtain ⟨h1, h2, hn⟩ := h
  refine ⟨⟨fun l => if l = F.height - 2 then σ (.n (b + 7 * (F.height - 2))) else sibs l, ?_⟩, h1, h2, hn⟩
  have e : ∀ sb : Nat → E, mFold (σ pp) (foldAddr σ adr F index) (fun l => index.testBit l) sb (F.height - 1) 0 (σ node) =
      mFold (σ pp) (foldAddr σ adr F index) (fun l => index.testBit l) sb (F.height - 2 + 1) 0 (σ node) := fun sb => by
    rw [show F.height - 1 = F.height - 2 + 1 by omega]
  rw [e, mFold_last, ← hs, hl]
  rfl

/-- Arm `j` of a fold's dispatch. -/
theorem spArms_get (pp md adr node : V) (F : Fold) (out : Nat → V) (ret1 ret2 : V) (r1 r2 : Nat → E) :
    ∀ (m a b j : Nat), j < m → ∃ bj,
      (spArms pp md adr node F out ret1 ret2 r1 r2 m a b).1[j]? =
        some (spArm pp md adr node F out ret1 ret2 (r1 (a + j)) (r2 (a + j)) (a + j) bj)
  | 0, _, _, _, h => absurd h (by omega)
  | m + 1, a, b, 0, _ => ⟨b, by simp [spArms]⟩
  | m + 1, a, b, j + 1, h => by
      obtain ⟨bj, hj⟩ := spArms_get pp md adr node F out ret1 ret2 r1 r2 m (a + 1) _ j (by omega)
      refine ⟨bj, ?_⟩
      simp only [spArms, List.getElem?_cons_succ]
      rw [hj, show a + 1 + j = a + (j + 1) by omega]

theorem spArms_length (pp md adr node : V) (F : Fold) (out : Nat → V) (ret1 ret2 : V) (r1 r2 : Nat → E) :
    ∀ (m a b : Nat), (spArms pp md adr node F out ret1 ret2 r1 r2 m a b).1.length = m
  | 0, _, _ => rfl
  | m + 1, a, b => by simp only [spArms, List.length_cons, spArms_length pp md adr node F out ret1 ret2 r1 r2 m]

/-- **A fold's dispatch is sound**: some arm `a < m`, at `x = g^a`, holds. -/
theorem spMatch_sound {σ : Val} {pp md adr node ret1 ret2 x : V} {F : Fold} {out : Nat → V} {r1 r2 : Nat → E}
    {m b : Nat} (hmd : σ md = mdw 64 true) (hF : 2 ≤ F.height) {ss : List Stmt} {next : Prop}
    {kret : List E → Prop}
    (h : Stmt.HoldsList C rd σ (.match_ x (spArms pp md adr node F out ret1 ret2 r1 r2 m 0 b).1 :: ss) next kret) :
    ∃ a < m, σ x = ofK (gpow a) ∧ (∃ sibs : Nat → E, σ (out (2 * (a / 2 ^ (F.height - 1)))) =
      mFold (σ pp) (foldAddr σ adr F a) (fun l => a.testBit l) sibs (F.height - 1) 0 (σ node)) ∧
      σ ret1 = r1 a ∧ σ ret2 = r2 a ∧ Stmt.HoldsList C rd σ ss next kret := by
  obtain ⟨j, hj, hx, ha⟩ := (holds_match_iff x _ _ _).mp h
  rw [spArms_length] at hj
  obtain ⟨bj, hget⟩ := spArms_get pp md adr node F out ret1 ret2 r1 r2 m 0 b j hj
  rw [List.getElem?_eq_getElem (by rw [spArms_length]; exact hj), Option.some.injEq, Nat.zero_add] at hget
  rw [hget] at ha
  obtain ⟨hs, h1, h2, hn⟩ := spArm_sound hmd hF ha
  exact ⟨j, hj, hx, hs, h1, h2, hn⟩

end
end LeanVM.Guest.B1.Sig
