/-
  LeanVM.Guest.B1.Sig.SphincsCoordComplete

  The leanSPHINCS forest's sub-trees and coordinates are complete: from a key and a codeword in
  range, canonical values and siblings, the dispatches and folds hold.
-/

module

public import LeanVM.Guest.B1.Sig.SphincsKeyComplete
public import LeanVM.Guest.B1.Sig.SphincsFoldComplete
public import LeanVM.Guest.B1.Sig.SphincsCoord

namespace LeanVM.Guest.B1.Sig

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.Blake2sHash
open LeanVM.Protocol.Verifier LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Value

@[expose] public section

variable {C : CallRel} {rd : Reader}

/-- The forest keys are complete under the call relation `C`. -/
def FkComplete (C : CallRel) : Prop :=
  ∀ t < 256, ∀ ka pp : E, IsCanonical128 ka → IsCanonical128 pp → ∀ vals : Nat → E, (∀ k, IsCanonical128 (vals k)) →
    C (fkNames.getD t "") [ka, pp] [fkLeaf t pp ka vals, word t 0 0]

theorem fkComplete_rel : FkComplete (coreProgram.Rel rd) :=
  fun _ ht _ _ hka hpp vals hvals => sp_forest_key_complete ht hka hpp vals hvals

theorem g255_eq : g255 = ofK (gpow 255) := by
  rw [g255, word_eOfNat, eOfNat, ← gpowK_eq (by unfold u128Bound; omega)]
  exact congrArg ofK (by decide +kernel)

theorem canonical_fkLeaf (t : Nat) (pp ka : E) (vals : Nat → E) : IsCanonical128 (fkLeaf t pp ka vals) :=
  (isCanonical128_hb _).1

/-! ## A sub-tree -/

/-- The statements of a sub-tree before its fold. -/
def sSubPre (subAt : V) (b : Nat) : List Stmt :=
  [hintW "sp_keys" [.n b, .n (b + 1)]] ++ rangeS (.n b) 8 (b + 2) ++ [hintW "sp_words" [.n (b + 6)],
    cst (b + 7) g255, .atom (.rangeCheck (.n (b + 6)) (.n (b + 8)) (.n (b + 9)) (.n (b + 10)) (.n (b + 7))),
    addS (.n (b + 11)) subAt (.n (b + 1)),
    .dispatch (.n (b + 6)) fkNames [.n (b + 11), .n 1] [.n (b + 12), .n (b + 13)]]

/-- A sub-tree's dispatch over its keys. -/
def sSubArms (c j : Nat) (subAt : V) (b : Nat) : List (List Stmt) × Nat :=
  spArms (.n 1) (.n 3) subAt (.n (b + 12)) subFoldT (spOut subFoldT (b + 14)) (.n (b + 1))
    (spRet2 subFoldT (b + 14)) (fun a => word (a * 2 ^ 40) 0 0)
    (fun a => lit (a * 2 ^ (58 + 3 * (2 * c + j)))) (2 ^ subFoldT.height) 0 (b + 14)

theorem sSub_eq (c j : Nat) (subAt bound : V) (b : Nat) :
    sSub c j subAt bound b = (sSubPre subAt b ++ ([.match_ (.n b) (sSubArms c j subAt b).1] ++
      [addS (.n (sSubArms c j subAt b).2) bound (spRet2 subFoldT (b + 14))]), (sSubArms c j subAt b).2 + 1,
      .n (b + 13), spOut subFoldT (b + 14), .n (sSubArms c j subAt b).2) := by
  simp only [sSub, sSubPre, sSubArms, List.append_assoc, List.cons_append, List.nil_append]
  rfl

theorem sSubPre_below {subAt : V} {b : Nat} (hsub : NB b subAt) :
    NumBelow (b + 14) (Stmt.valsList (sSubPre subAt b)) := by
  obtain ⟨k, hk, rfl⟩ := hsub
  simp only [sSubPre, rangeS, hintW, cst, addS, List.cons_append, List.nil_append, valsList_cons, valsList_nil,
    Stmt.vals, Atom.vals, Hint.vals, Dest.vals, List.append_nil, List.cons_append]
  repeat (first | exact .nil _ | (refine .cons ⟨_, ?_, rfl⟩ ?_; omega))

/-- **The statements before a sub-tree's fold are complete**: key `a` and codeword `t` in range, the
forest key of the values at the key's address. -/
theorem sSubPre_complete (hfk : FkComplete C) (hrd : MemOK rd 256) {σ : Val} (hpp : IsCanonical128 (σ (.n 1)))
    {subAt : V} {b : Nat} (hb : 2 ≤ b) (hsub : NB b subAt) (hsubc : IsCanonical128 (σ subAt)) {t a : Nat}
    (ht : t < 256) (ha : a < 8) (vals : Nat → E) (hvals : ∀ k, IsCanonical128 (vals k)) :
    Completes C rd b (b + 14) (sSubPre subAt b) σ (fun σ' =>
      σ' (.n b) = ofK (gpow a) ∧ σ' (.n (b + 1)) = word (a * 2 ^ 40) 0 0 ∧
      σ' (.n (b + 12)) = fkLeaf t (σ (.n 1)) (σ subAt + word (a * 2 ^ 40) 0 0) vals ∧
      σ' (.n (b + 13)) = word t 0 0 ∧ AgreeBelow b σ σ') := by
  obtain ⟨ks, hks, rfl⟩ := hsub
  obtain ⟨y1, u1, u2, hl1, hk1, hl2⟩ := rangeCheck_witness (hrd.mono (by norm_num) : MemOK rd 8) (by norm_num) ha
  obtain ⟨y2, w1, w2, hm1, hk2, hm2⟩ := rangeCheck_witness hrd (by norm_num) ht
  set KA := σ (.n ks) + word (a * 2 ^ 40) 0 0
  set vs : List E := [ofK (gpow a), word (a * 2 ^ 40) 0 0, word (2 ^ 7) 0 0, y1, u1, u2, ofK (gpow t), g255, y2,
    w1, w2, KA, fkLeaf t (σ (.n 1)) KA vals, word t 0 0]
  set σ' := upds σ ((List.range 14).map fun k => (b + k, vs.getD k 0))
  have he : Ext b (b + 14) σ σ' := upds_ext σ _ (by simp)
  have v : ∀ k < 14, σ' (.n (b + k)) = vs.getD k 0 := upds_range_at b _ 14 σ
  have hk : ∀ k < b, σ' (.n k) = σ (.n k) := fun k hk => (he.agree k hk).symm
  have v0 : σ' (.n b) = ofK (gpow a) := by have := v 0 (by omega); rwa [Nat.add_zero] at this
  refine ⟨σ', he, ⟨v0, v 1 (by omega), v 12 (by omega), v 13 (by omega), he.agree⟩, fun next kret hn => ?_⟩
  simp only [sSubPre, rangeS, hintW, cst, addS, List.cons_append, List.nil_append, holdsList_cons_atom, Atom.Holds,
    true_and]
  refine ⟨by rw [v 2 (by omega)]; rfl, ?_⟩
  rw [v0, v 2 (by omega), v 3 (by omega), v 4 (by omega), v 5 (by omega), v 6 (by omega), v 7 (by omega),
    v 8 (by omega), v 9 (by omega), v 10 (by omega), v 11 (by omega), hk ks hks, v 1 (by omega)]
  simp only [vs, List.getD_cons_succ, List.getD_cons_zero]
  refine ⟨⟨hl1, by rw [word_two_pow (by norm_num)]; exact hk1, hl2⟩, trivial, ⟨hm1, by rw [g255_eq]; exact hk2, hm2⟩,
    rfl, ?_⟩
  refine (holdsList_cons_dispatch _ _ _ _ _ _ _ _).mpr ⟨⟨t, by rw [fkNames_length]; exact ht, ?_, ?_⟩, hn⟩
  · rw [v 6 (by omega)]; rfl
  · simp only [List.map_cons, List.map_nil]
    rw [v 11 (by omega), v 12 (by omega), v 13 (by omega), hk 1 (by omega)]
    simp only [vs, List.getD_cons_succ, List.getD_cons_zero]
    rw [← List.getD_eq_getElem fkNames "" (by rw [fkNames_length]; exact ht)]
    exact hfk t ht KA _ (isCanonical128_add hsubc (isCanonical128_word _ _)) hpp vals hvals

theorem sSubArms_snd (c j : Nat) (subAt : V) (b : Nat) : (sSubArms c j subAt b).2 = b + 14 + 101 := by
  rw [sSubArms, spArms_snd_eq]; simp only [Nat.zero_add]; rw [spArm_base]; rfl

/-- **A sub-tree is complete**: key `a`, codeword `t`, the forest key of the values folded two
levels over the siblings, the bound gaining the key's field. -/
theorem sSub_complete (hfk : FkComplete C) (hrd : MemOK rd 256) {σ : Val} (hmd : σ (.n 3) = mdw 64 true)
    (hpp : IsCanonical128 (σ (.n 1))) {c j : Nat} {subAt bound : V} {b : Nat} (hb : 4 ≤ b) (hsub : NB b subAt)
    (hbound : NB b bound) (hsubc : IsCanonical128 (σ subAt)) {t a : Nat} (ht : t < 256) (ha : a < 8)
    (vals sibs : Nat → E) (hvals : ∀ k, IsCanonical128 (vals k)) (hsibs : ∀ l, IsCanonical128 (sibs l)) :
    Completes C rd b (sSub c j subAt bound b).2.1 (sSub c j subAt bound b).1 σ (fun σ' =>
      σ' (.n (b + 1)) = word (a * 2 ^ 40) 0 0 ∧ σ' (sSub c j subAt bound b).2.2.1 = word t 0 0 ∧
      σ' ((sSub c j subAt bound b).2.2.2.1 (2 * (a / 4))) = mFold (σ (.n 1)) (foldAddr σ subAt subFoldT a)
        (fun l => a.testBit l) sibs 2 0 (fkLeaf t (σ (.n 1)) (σ subAt + word (a * 2 ^ 40) 0 0) vals) ∧
      σ' ((sSub c j subAt bound b).2.2.2.1 (2 - 2 * (a / 4))) = sibs 2 ∧
      σ' (sSub c j subAt bound b).2.2.2.2 = σ bound + lit (a * 2 ^ (58 + 3 * (2 * c + j))) ∧
      AgreeBelow b σ σ') := by
  have hF : subFoldT.height = 3 ∨ subFoldT.height = 4 := Or.inl rfl
  have ha' : a < 2 ^ subFoldT.height := ha
  obtain ⟨-, -, -, hq, hout, -, hpRe, -⟩ := spMatch_layout (b := b + 14) hF ha'
  have hend := sSubArms_snd c j subAt b
  rw [sSub_eq]
  dsimp only
  rw [hend]
  have hS1 : NB b (V.n 1) := ⟨1, by omega, rfl⟩
  have hS3 : NB b (V.n 3) := ⟨3, by omega, rfl⟩
  refine Completes.append (m := b + 14) (by omega) (by omega) (sSubPre_below hsub)
    (sSubPre_complete hfk hrd hpp (by omega) hsub hsubc ht ha vals hvals) fun σ1 _ ⟨h0, h1, h12, h13, hag1⟩ => ?_
  have hk1 : ∀ v : V, NB b v → σ1 v = σ v := fun v ⟨k, hk, e⟩ => by rw [e]; exact (hag1 k hk).symm
  have hmatch := spMatch_complete (C := C) (rd := rd) (σ := σ1) (pp := .n 1) (md := .n 3) (adr := subAt)
    (node := .n (b + 12)) (ret1 := .n (b + 1)) (x := .n b) (F := subFoldT) hF
    (r1 := fun a => word (a * 2 ^ 40) 0 0) (r2 := fun a => lit (a * 2 ^ (58 + 3 * (2 * c + j)))) (b := b + 14)
    ha' ⟨hS1.mono (by omega), hS3.mono (by omega), hsub.mono (by omega), ⟨b + 12, by omega, rfl⟩,
      ⟨b + 1, by omega, rfl⟩, ⟨b, by omega, rfl⟩⟩ (by rw [hk1 _ hS3, hmd]) (by rw [hk1 _ hS1]; exact hpp)
    (by rw [hk1 _ hsub]; exact hsubc) (by rw [h12]; exact canonical_fkLeaf _ _ _ _) sibs hsibs h0 h1
  rw [← sSubArms, hend] at hmatch
  refine Completes.append (m := b + 14 + 101) (by omega) (by omega)
    (by have := spMatch_below (r1 := fun a => word (a * 2 ^ 40) 0 0)
          (r2 := fun a => lit (a * 2 ^ (58 + 3 * (2 * c + j)))) hF (b := b + 14) (pp := .n 1) (md := .n 3)
          (adr := subAt) (node := .n (b + 12)) (ret1 := .n (b + 1)) (x := .n b)
          ⟨hS1.mono (by omega), hS3.mono (by omega), hsub.mono (by omega), ⟨b + 12, by omega, rfl⟩,
            ⟨b + 1, by omega, rfl⟩, ⟨b, by omega, rfl⟩⟩
        rw [← sSubArms, hend] at this; exact this)
    hmatch.withExt fun σ2 _ ⟨⟨ho, hs, hr⟩, he2⟩ => ?_
  have hk2 : ∀ k < b + 14, σ2 (.n k) = σ1 (.n k) := fun k hk => (he2.agree k hk).symm
  have hbd : σ2 bound = σ bound := by
    obtain ⟨kb, hkb, e⟩ := hbound; rw [e, hk2 kb (by omega), ← e, hk1 bound ⟨kb, hkb, e⟩]
  set val := σ2 bound + σ2 (spRet2 subFoldT (b + 14))
  have hne : ∀ p, p < b + 14 + 101 → (V.n p) ≠ .n (b + 14 + 101) := fun p hp e => by
    simp only [V.mk.injEq] at e; omega
  refine Completes.atom_cons val le_rfl ?_ ?_ (Completes.nil _ _ _ ?_)
  · obtain ⟨kb, hkb, e⟩ := hbound
    simp only [Atom.vals, spRet2]
    exact .cons ⟨_, by omega, rfl⟩ (.cons ⟨kb, by omega, e⟩ (.cons ⟨_, by omega, rfl⟩ (.nil _)))
  · obtain ⟨kb, hkb, e⟩ := hbound
    show _ = _ + _
    rw [Function.update_self, e, Function.update_of_ne (hne kb (by omega)), spRet2,
      Function.update_of_ne (hne _ (by simp only [subFoldT]; omega)), ← e]
    rfl
  · have hu : ∀ p, p < b + 14 + 101 → Function.update σ2 (.n (b + 14 + 101)) val (.n p) = σ2 (.n p) :=
      fun p hp => Function.update_of_ne (hne p hp) _ _
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [hu _ (by omega), hk2 _ (by omega), h1]
    · rw [hu _ (by omega), hk2 _ (by omega), h13]
    · rw [spOut_eq, hu _ (hout _ (by omega)).2.1, ← spOut_eq]
      refine ho.trans ?_
      rw [hk1 _ hS1, h12]
      have hA : foldAddr σ1 subAt subFoldT a = foldAddr σ subAt subFoldT a := by
        funext l'; simp only [foldAddr, hk1 subAt hsub]
      rw [hA]; rfl
    · rw [spOut_eq, hu _ (hout _ (by omega)).2.1, ← spOut_eq]
      exact hs
    · rw [Function.update_self]
      show σ2 bound + σ2 (spRet2 subFoldT (b + 14)) = _
      rw [hbd, hr]
    · exact fun k hk => (hag1 k hk).trans ((hk2 k (by omega)).symm.trans (hu k (by omega)).symm)

theorem sSub_below {c j : Nat} {subAt bound : V} {b : Nat} (hb : 4 ≤ b) (hsub : NB b subAt) (hbound : NB b bound) :
    NumBelow (sSub c j subAt bound b).2.1 (Stmt.valsList (sSub c j subAt bound b).1) := by
  have hend := sSubArms_snd c j subAt b
  rw [sSub_eq]
  dsimp only
  rw [hend, valsList_append, valsList_append]
  have hm := spMatch_below (r1 := fun a => word (a * 2 ^ 40) 0 0)
    (r2 := fun a => lit (a * 2 ^ (58 + 3 * (2 * c + j)))) (Or.inl rfl) (b := b + 14) (pp := .n 1) (md := .n 3)
    (adr := subAt) (node := .n (b + 12)) (ret1 := .n (b + 1)) (x := .n b) (F := subFoldT)
    ⟨⟨1, by omega, rfl⟩, ⟨3, by omega, rfl⟩, hsub.mono (by omega), ⟨b + 12, by omega, rfl⟩, ⟨b + 1, by omega, rfl⟩,
      ⟨b, by omega, rfl⟩⟩
  rw [← sSubArms, hend] at hm
  obtain ⟨kb, hkb, e⟩ := hbound
  refine (((sSubPre_below hsub).mono (by omega)).append (hm.mono (by omega))).append ?_
  simp only [addS, valsList_cons, valsList_nil, Stmt.vals, Atom.vals, List.append_nil, spRet2]
  exact .cons ⟨_, by omega, rfl⟩ (.cons ⟨kb, by omega, e⟩ (.cons ⟨_, by simp only [subFoldT]; omega, rfl⟩ (.nil _)))

theorem sSub_snd (c j : Nat) (subAt bound : V) (b : Nat) : (sSub c j subAt bound b).2.1 = b + 116 := by
  rw [sSub_eq]; dsimp only; rw [sSubArms_snd]

/-! ## A coordinate in the scheme, from its cells -/

section Scheme

open Sphincs Sphincs.Concrete

variable {inst : HasQuery Sphincs.HashSpec Id}

/-- **A coordinate's two top nodes from the cells**: the sub-trees' top nodes, the super-child and
the top tree's two top nodes, each as the fold reaches it. -/
theorem coordRecover_cells (hq : SQ inst) {pp : E} (index : Index) (c : Coord) (mark : CoordMark)
    (opening : CoordOpening) (vals0 vals1 sibs0 sibs1 tsibs : Nat → E)
    (hv0 : (opening.sub 0).values = fun i => sv (vals0 i.val)) (hv1 : (opening.sub 1).values = fun i => sv (vals1 i.val))
    (hp0 : (opening.sub 0).path = fun l => sv (sibs0 l.val)) (hp1 : (opening.sub 1).path = fun l => sv (sibs1 l.val))
    (htp : opening.top = fun l => sv (tsibs l.val)) {X00 X02 X10 X12 SUP T0 T1 : E}
    (h0x : (if (mark.child 0).val / 4 = 0 then X00 else X02) =
      mFold pp (fun l => eOfNat (fpos index.val c.val mark.super.val 0 0) + word (subFoldT.addr (mark.child 0).val l) 0 0)
        (fun l => (mark.child 0).val.testBit l) sibs0 2 0
        (fkLeaf (mark.word 0).val pp (eOfNat (fpos index.val c.val mark.super.val 0 (mark.child 0).val)) vals0))
    (h0y : (if (mark.child 0).val / 4 = 0 then X02 else X00) = sibs0 2)
    (h1x : (if (mark.child 1).val / 4 = 0 then X10 else X12) =
      mFold pp (fun l => eOfNat (fpos index.val c.val mark.super.val 1 0) + word (subFoldT.addr (mark.child 1).val l) 0 0)
        (fun l => (mark.child 1).val.testBit l) sibs1 2 0
        (fkLeaf (mark.word 1).val pp (eOfNat (fpos index.val c.val mark.super.val 1 (mark.child 1).val)) vals1))
    (h1y : (if (mark.child 1).val / 4 = 0 then X12 else X10) = sibs1 2)
    (hsup : SUP = (hcell [pp, eOfNat (fpos index.val c.val mark.super.val 0 0) + word (tw 18) 0 0, X00, X02, X10,
      X12]).1)
    (htx : (if mark.super.val / 8 = 0 then T0 else T1) =
      mFold pp (fun l => eOfNat (fpos index.val c.val 0 0 0) + word (topFoldT.addr mark.super.val l) 0 0)
        (fun l => mark.super.val.testBit l) tsibs 3 0 SUP)
    (hty : (if mark.super.val / 8 = 0 then T1 else T0) = tsibs 3) :
    @coordRecover Id _ inst (spp pp) index c mark opening = (sv T0, sv T1) := by
  have hsub : (fun j : SubIdx => orderTops ((mark.child j).val.testBit (subHeight - 1))
      (@subFold Id _ inst (spp pp) index c mark.super j (mark.child j) (opening.sub j).path (subHeight - 1)
        (@childRecover Id _ inst (spp pp) index c mark.super j (mark.child j) (lut (mark.word j))
          (opening.sub j).values))
      ((opening.sub j).path subTopLevel)) =
      fun j => if j = 0 then (sv X00, sv X02) else (sv X10, sv X12) := by
    funext j
    fin_cases j
    · simp only [Fin.zero_eta, Fin.isValue, ↓reduceIte, hv0, hp0]
      exact sp_subTops hq index c mark.super 0 (mark.child 0) (mark.word 0) vals0 sibs0 h0x h0y
    · simp only [Fin.mk_one, Fin.isValue, one_ne_zero, ↓reduceIte, hv1, hp1]
      exact sp_subTops hq index c mark.super 1 (mark.child 1) (mark.word 1) vals1 sibs1 h1x h1y
  rw [sCoordRecover_id, hsub, sSuperHash_cells hq (superChild_addr index c mark.super), ← hsup, htp]
  exact sp_topTops hq index c mark.super tsibs htx hty

end Scheme

/-! ## A coordinate -/

theorem sSub_bound (c j : Nat) (subAt bound : V) (b : Nat) : (sSub c j subAt bound b).2.2.2.2 = .n (b + 115) := by
  rw [sSub_eq]; dsimp only; rw [sSubArms_snd]

theorem sSub_word (c j : Nat) (subAt bound : V) (b : Nat) : (sSub c j subAt bound b).2.2.1 = .n (b + 13) := by
  rw [sSub_eq]

theorem sSub_outs (c j : Nat) (subAt bound : V) (b : Nat) :
    (sSub c j subAt bound b).2.2.2.1 = spOut subFoldT (b + 14) := by
  rw [sSub_eq]

/-- A coordinate's first block: the tree's leaf in range and the leaf's address. -/
def coordA (treeAt : V) (b0 : Nat) : List Stmt :=
  [hintW "sp_leaves" [.n b0, .n (b0 + 1)]] ++ rangeS (.n b0) 16 (b0 + 2) ++ [addS (.n (b0 + 6)) treeAt (.n (b0 + 1))]

/-- The second sub-tree's address. -/
def coordB (b0 : Nat) : List Stmt :=
  [cst (b0 + 123) (word (2 ^ 39) 0 0), addS (.n (b0 + 124)) (.n (b0 + 6)) (.n (b0 + 123))]

/-- The super-child's hash. -/
def coordD (b0 : Nat) : List Stmt :=
  let f := b0 + 241
  [cst f (word (tw 18) 0 0), addS (.n (f + 1)) (.n (b0 + 6)) (.n f)] ++ ivs (f + 2) ++
    [cst (f + 4) (mdw 64 false),
      b2s (.n 1) (.n (f + 1)) (spOut subFoldT (b0 + 21) 0) (spOut subFoldT (b0 + 21) 2) (.n (f + 2)) (.n (f + 3))
        (.n (f + 5)) (.n (f + 6)) (.n (f + 4)),
      cst (f + 7) (word 0 0 0), cst (f + 8) (word 0 0 0), cst (f + 9) (mdw 96 true),
      b2s (spOut subFoldT (b0 + 139) 0) (spOut subFoldT (b0 + 139) 2) (.n (f + 7)) (.n (f + 8)) (.n (f + 5))
        (.n (f + 6)) (.n (f + 10)) (.n (f + 11)) (.n (f + 9))]

/-- The top tree's dispatch. -/
def topArms (c : Nat) (treeAt : V) (b0 : Nat) : List (List Stmt) × Nat :=
  spArms (.n 1) (.n 3) treeAt (.n (b0 + 251)) topFoldT (spOut topFoldT (b0 + 253)) (.n (b0 + 1))
    (spRet2 topFoldT (b0 + 253)) (fun s => word (s * 2 ^ 35) 0 0) (fun s => lit (s * 2 ^ (26 + 4 * c)))
    (2 ^ topFoldT.height) 0 (b0 + 253)

theorem topArms_snd (c : Nat) (treeAt : V) (b0 : Nat) : (topArms c treeAt b0).2 = b0 + 253 + 309 := by
  rw [topArms, spArms_snd_eq]; simp only [Nat.zero_add]; rw [spArm_base]; rfl

theorem sCoordT_eq (c : Nat) (bound treeAt : V) (b0 : Nat) :
    sCoordT c bound treeAt b0 = (coordA treeAt b0 ++ ((sSub c 0 (.n (b0 + 6)) bound (b0 + 7)).1 ++ (coordB b0 ++
      ((sSub c 1 (.n (b0 + 124)) (.n (b0 + 122)) (b0 + 125)).1 ++ (coordD b0 ++ ([.match_ (.n b0) (topArms c treeAt b0).1] ++
        [addS (.n (b0 + 253 + 309)) (.n (b0 + 240)) (spRet2 topFoldT (b0 + 253))]))))),
      b0 + 253 + 309 + 1, (.n (b0 + 20), .n (b0 + 138)), (spOut topFoldT (b0 + 253) 0, spOut topFoldT (b0 + 253) 2),
      .n (b0 + 253 + 309)) := by
  rw [← topArms_snd c treeAt b0]
  simp only [sCoordT, sSub_snd, sSub_bound, sSub_word, sSub_outs, coordA, coordB, coordD, topArms, ivs, List.append_assoc,
    List.cons_append, List.nil_append]
  rfl

theorem coordA_below {treeAt : V} {b0 : Nat} (htB : NB b0 treeAt) : NumBelow (b0 + 7) (Stmt.valsList (coordA treeAt b0)) := by
  obtain ⟨k, hk, rfl⟩ := htB
  simp only [coordA, rangeS, hintW, cst, addS, List.cons_append, List.nil_append, valsList_cons, valsList_nil,
    Stmt.vals, Atom.vals, Hint.vals, Dest.vals, List.append_nil, List.cons_append]
  repeat (first | exact .nil _ | (refine .cons ⟨_, ?_, rfl⟩ ?_; omega))

theorem coordB_below (b0 : Nat) : NumBelow (b0 + 125) (Stmt.valsList (coordB b0)) := by
  simp only [coordB, cst, addS, List.cons_append, List.nil_append, valsList_cons, valsList_nil, Stmt.vals, Atom.vals,
    List.append_nil, List.cons_append]
  repeat (first | exact .nil _ | (refine .cons ⟨_, ?_, rfl⟩ ?_; omega))

theorem coordD_below (b0 : Nat) : NumBelow (b0 + 253) (Stmt.valsList (coordD b0)) := by
  simp only [coordD, ivs, cst, addS, b2s, spOut, subFoldT, List.cons_append, List.nil_append, valsList_cons,
    valsList_nil, Stmt.vals, Atom.vals, List.append_nil, List.cons_append]
  repeat (first | exact .nil _ | (refine .cons ⟨_, ?_, rfl⟩ ?_; simp; omega) | (refine .cons ⟨_, ?_, rfl⟩ ?_; omega))

/-- **A coordinate's first block is complete**: the tree's leaf `s` in range. -/
theorem coordA_complete (hrd : MemOK rd 256) {σ : Val} {treeAt : V} {b0 : Nat} (htB : NB b0 treeAt) {s : Nat}
    (hs : s < 16) :
    Completes C rd b0 (b0 + 7) (coordA treeAt b0) σ (fun σ' =>
      σ' (.n b0) = ofK (gpow s) ∧ σ' (.n (b0 + 1)) = word (s * 2 ^ 35) 0 0 ∧
      σ' (.n (b0 + 6)) = σ treeAt + word (s * 2 ^ 35) 0 0 ∧ AgreeBelow b0 σ σ') := by
  obtain ⟨kt, hkt, rfl⟩ := htB
  obtain ⟨y1, u1, u2, hl1, hk1, hl2⟩ := rangeCheck_witness (hrd.mono (by norm_num) : MemOK rd 16) (by norm_num) hs
  set vs : List E := [ofK (gpow s), word (s * 2 ^ 35) 0 0, word (2 ^ 15) 0 0, y1, u1, u2,
    σ (.n kt) + word (s * 2 ^ 35) 0 0]
  set σ' := upds σ ((List.range 7).map fun k => (b0 + k, vs.getD k 0))
  have he : Ext b0 (b0 + 7) σ σ' := upds_ext σ _ (by simp)
  have v : ∀ k < 7, σ' (.n (b0 + k)) = vs.getD k 0 := upds_range_at b0 _ 7 σ
  have hk : ∀ k < b0, σ' (.n k) = σ (.n k) := fun k hk => (he.agree k hk).symm
  have v0 : σ' (.n b0) = ofK (gpow s) := by have := v 0 (by omega); rwa [Nat.add_zero] at this
  refine ⟨σ', he, ⟨v0, v 1 (by omega), v 6 (by omega), he.agree⟩, fun next kret hn => ?_⟩
  simp only [coordA, rangeS, hintW, cst, addS, List.cons_append, List.nil_append, holdsList_cons_atom, Atom.Holds,
    true_and]
  rw [v0, v 2 (by omega), v 3 (by omega), v 4 (by omega), v 5 (by omega), v 6 (by omega), v 1 (by omega),
    hk kt hkt]
  simp only [vs, List.getD_cons_succ, List.getD_cons_zero]
  exact ⟨trivial, ⟨hl1, by rw [word_two_pow (by norm_num)]; exact hk1, hl2⟩, trivial, hn⟩

/-- **The second sub-tree's address is complete.** -/
theorem coordB_complete {σ : Val} {b0 : Nat} :
    Completes C rd (b0 + 123) (b0 + 125) (coordB b0) σ (fun σ' =>
      σ' (.n (b0 + 124)) = σ (.n (b0 + 6)) + word (2 ^ 39) 0 0 ∧ AgreeBelow (b0 + 123) σ σ') := by
  set vs : List E := [word (2 ^ 39) 0 0, σ (.n (b0 + 6)) + word (2 ^ 39) 0 0]
  set σ' := upds σ ((List.range 2).map fun k => (b0 + 123 + k, vs.getD k 0))
  have he : Ext (b0 + 123) (b0 + 123 + 2) σ σ' := upds_ext σ _ (by simp)
  have v : ∀ k < 2, σ' (.n (b0 + 123 + k)) = vs.getD k 0 := upds_range_at (b0 + 123) _ 2 σ
  have hk : ∀ k < b0 + 123, σ' (.n k) = σ (.n k) := fun k hk => (he.agree k hk).symm
  refine ⟨σ', he, ⟨v 1 (by omega), he.agree⟩, fun next kret hn => ?_⟩
  simp only [coordB, cst, addS, holdsList_cons_atom, holdsList_nil, Atom.Holds]
  have v0 := v 0 (by omega)
  rw [Nat.add_zero] at v0
  rw [v0, show b0 + 124 = b0 + 123 + 1 by omega, v 1 (by omega), hk (b0 + 6) (by omega)]
  exact ⟨rfl, rfl, hn⟩

/-- **The super-child's hash is complete.** -/
theorem coordD_complete {σ : Val} {b0 : Nat} (hpp : IsCanonical128 (σ (.n 1)))
    (hla : IsCanonical128 (σ (.n (b0 + 6))))
    (hx : IsCanonical128 (σ (spOut subFoldT (b0 + 21) 0)) ∧ IsCanonical128 (σ (spOut subFoldT (b0 + 21) 2)) ∧
      IsCanonical128 (σ (spOut subFoldT (b0 + 139) 0)) ∧ IsCanonical128 (σ (spOut subFoldT (b0 + 139) 2))) :
    Completes C rd (b0 + 241) (b0 + 253) (coordD b0) σ (fun σ' =>
      σ' (.n (b0 + 251)) = (hcell [σ (.n 1), σ (.n (b0 + 6)) + word (tw 18) 0 0, σ (spOut subFoldT (b0 + 21) 0),
        σ (spOut subFoldT (b0 + 21) 2), σ (spOut subFoldT (b0 + 139) 0), σ (spOut subFoldT (b0 + 139) 2)]).1 ∧
      AgreeBelow (b0 + 241) σ σ') := by
  set f := b0 + 241
  set A := σ (.n (b0 + 6)) + word (tw 18) 0 0
  set X00 := σ (spOut subFoldT (b0 + 21) 0)
  set X02 := σ (spOut subFoldT (b0 + 21) 2)
  set X10 := σ (spOut subFoldT (b0 + 139) 0)
  set X12 := σ (spOut subFoldT (b0 + 139) 2)
  set x := hmid ![σ (.n 1), A, X00, X02]
  set o := hb (blockBytes ![σ (.n 1), A, X00, X02] ++ [X10, X12].flatMap cellBytes)
  set vs : List E := [word (tw 18) 0 0, A, iv0, iv1, mdw 64 false, x.1, x.2, 0, 0, mdw 96 true, o.1, o.2]
  set σ' := upds σ ((List.range 12).map fun k => (f + k, vs.getD k 0))
  have he : Ext f (f + 12) σ σ' := upds_ext σ _ (by simp)
  have v : ∀ k < 12, σ' (.n (f + k)) = vs.getD k 0 := upds_range_at f _ 12 σ
  have hk : ∀ k < f, σ' (.n k) = σ (.n k) := fun k hk => (he.agree k hk).symm
  have hr : ([X10, X12].flatMap cellBytes).length = 32 := by rw [length_flatMap_cellBytes']; rfl
  have hcmp := (compress_two_iff (b0 := ![σ (.n 1), A, X00, X02]) (b1 := ![X10, X12, 0, 0]) (x0 := x.1) (x1 := x.2)
    (o0 := o.1) (o1 := o.2) (blockBytes_two X10 X12) (by rw [hr]; omega) (by rw [hr]; omega)).mpr
    ⟨fin4_canonical.mpr ⟨hpp, isCanonical128_add hla (isCanonical128_word _ _), hx.1, hx.2.1⟩,
      fin4_canonical.mpr ⟨hx.2.2.1, hx.2.2.2, isCanonical128_zero, isCanonical128_zero⟩, rfl, rfl⟩
  rw [hr] at hcmp
  have ho0 : σ' (spOut subFoldT (b0 + 21) 0) = X00 := hk _ (by simp [subFoldT]; omega)
  have ho2 : σ' (spOut subFoldT (b0 + 21) 2) = X02 := hk _ (by simp [subFoldT]; omega)
  have ho10 : σ' (spOut subFoldT (b0 + 139) 0) = X10 := hk _ (by simp [subFoldT]; omega)
  have ho12 : σ' (spOut subFoldT (b0 + 139) 2) = X12 := hk _ (by simp [subFoldT]; omega)
  refine ⟨σ', he, ⟨?_, he.agree⟩, fun next kret hn => ?_⟩
  · rw [show b0 + 251 = f + 10 by omega, v 10 (by omega)]
    simp only [vs, o, List.getD_cons_succ, List.getD_cons_zero, blockBytes_four, hcell, ← List.flatMap_append]
    rfl
  · simp only [coordD, ivs, cst, addS, b2s, List.cons_append, List.nil_append, holdsList_cons_atom, holdsList_nil,
      Atom.Holds]
    have v0 := v 0 (by omega)
    rw [Nat.add_zero] at v0
    rw [v0, v 1 (by omega), v 2 (by omega), show f + 2 + 1 = f + 3 by omega, v 3 (by omega), v 4 (by omega),
      v 5 (by omega), v 6 (by omega), v 7 (by omega), v 8 (by omega), v 9 (by omega), v 10 (by omega),
      v 11 (by omega), hk 1 (by omega), hk (b0 + 6) (by omega), ho0, ho2, ho10, ho12]
    simp only [vs, List.getD_cons_succ, List.getD_cons_zero, word_zero]
    obtain ⟨hc1, hc2⟩ := hcmp
    refine ⟨?_, ?_, ?_, ?_, ?_, hc1, ?_, ?_, ?_, hc2, hn⟩ <;> trivial

theorem mFold_canon (pp : E) (A : Nat → E) (bits : Nat → Bool) (sibs : Nat → E) :
    ∀ (m l : Nat) (x : E), (0 < m ∨ IsCanonical128 x) → IsCanonical128 (mFold pp A bits sibs m l x)
  | 0, _, _, h => h.resolve_left (by omega)
  | m + 1, l, x, _ => mFold_canon pp A bits sibs m (l + 1) _ (Or.inr (isCanonical128_hb _).1)

/-- The cells of a function on `Fin n`, zero outside. -/
def finCells {n : Nat} (f : Fin n → BitVec 128) : Nat → E := fun i => if h : i < n then cellOf (f ⟨i, h⟩) else 0

theorem canonical_finCells {n : Nat} (f : Fin n → BitVec 128) (i : Nat) : IsCanonical128 (finCells f i) := by
  unfold finCells; split
  · exact isCanonical128_cellOf _
  · exact isCanonical128_zero

theorem sv_finCells {n : Nat} (f : Fin n → Sphincs.Digest) : f = fun i => sv (finCells f i.val) := by
  funext i
  simp only [finCells, i.isLt, ↓reduceDIte]
  exact (cellVal_cellOf _).symm

section Scheme

open Sphincs Sphincs.Concrete

variable {inst : HasQuery Sphincs.HashSpec Id}

/-- **A coordinate is complete** (after its tree's address): from a mark and an opening, the
coordinate's two top nodes in the scheme land in its outputs, the codeword cells hold the mark's
codewords, and the bound gains the mark's fields. -/
theorem sCoordT_complete (hq : SQ inst) (hfk : FkComplete C) (hrd : MemOK rd 256) {σ : Val}
    (hmd : σ (.n 3) = mdw 64 true) (hpp : IsCanonical128 (σ (.n 1))) (index : Index) (c : Coord) {bound treeAt : V}
    {b0 : Nat} (hb0 : 4 ≤ b0) (htB : NB b0 treeAt) (hbB : NB b0 bound)
    (htree : σ treeAt = eOfNat (fpos index.val c.val 0 0 0)) (mark : CoordMark) (opening : CoordOpening) :
    Completes C rd b0 (sCoordT c.val bound treeAt b0).2.1 (sCoordT c.val bound treeAt b0).1 σ (fun σ' =>
      @coordRecover Id _ inst (spp (σ (.n 1))) index c mark opening =
        (sv (σ' (sCoordT c.val bound treeAt b0).2.2.2.1.1), sv (σ' (sCoordT c.val bound treeAt b0).2.2.2.1.2)) ∧
      IsCanonical128 (σ' (sCoordT c.val bound treeAt b0).2.2.2.1.1) ∧
      IsCanonical128 (σ' (sCoordT c.val bound treeAt b0).2.2.2.1.2) ∧
      σ' (sCoordT c.val bound treeAt b0).2.2.1.1 = word (mark.word 0).val 0 0 ∧
      σ' (sCoordT c.val bound treeAt b0).2.2.1.2 = word (mark.word 1).val 0 0 ∧
      σ' (sCoordT c.val bound treeAt b0).2.2.2.2 = σ bound + coordWeight c.val mark ∧ AgreeBelow b0 σ σ') := by
  rw [sCoordT_eq]
  dsimp only
  have hidx := index.isLt
  have hc8 := c.isLt
  simp only [totalHeight, forestCoords] at hidx hc8
  have hs16 := mark.super.isLt
  have ha0 := (mark.child 0).isLt
  have ha1 := (mark.child 1).isLt
  simp only [topHeight, subHeight] at hs16 ha0 ha1
  have hS1 : NB b0 (V.n 1) := ⟨1, by omega, rfl⟩
  have hS3 : NB b0 (V.n 3) := ⟨3, by omega, rfl⟩
  -- block A
  refine Completes.append (m := b0 + 7) (by omega) (by omega) (coordA_below htB)
    (coordA_complete (C := C) hrd htB hs16).withExt fun σA _ ⟨⟨hA0, hA1, hA6, hagA⟩, heA⟩ => ?_
  have hkA : ∀ v : V, NB b0 v → σA v = σ v := fun v ⟨k, hk, e⟩ => by rw [e]; exact (hagA k hk).symm
  have hLA : σA (.n (b0 + 6)) = eOfNat (fpos index.val c.val mark.super.val 0 0) := by
    rw [hA6, htree, show mark.super.val * 2 ^ 35 = 2 ^ 35 * mark.super.val by ring,
      sp_add_word (by unfold fpos; omega)]
    congr 1; unfold fpos; ring
  -- the first sub-tree
  have hsub0 := sSub_complete (C := C) (rd := rd) (c := c.val) (j := 0) hfk hrd (σ := σA)
    (by rw [hkA _ hS3, hmd]) (by rw [hkA _ hS1]; exact hpp) (b := b0 + 7) (by omega) ⟨b0 + 6, by omega, rfl⟩
    (hbB.mono (by omega)) (by rw [hLA]; exact isCanonical128_eOfNat _) (mark.word 0).isLt ha0
    (finCells (opening.sub 0).values) (finCells (opening.sub 0).path) (canonical_finCells _)
    (canonical_finCells _)
  rw [sSub_snd, sSub_word, sSub_outs, sSub_bound] at hsub0
  have hsub0B := sSub_below (c := c.val) (j := 0) (b := b0 + 7) (by omega) ⟨b0 + 6, by omega, rfl⟩
    (hbB.mono (by omega)) (bound := bound)
  rw [sSub_snd] at hsub0B
  refine Completes.append (m := b0 + 123) (by omega) (by omega) hsub0B hsub0.withExt
    fun σ0 _ ⟨⟨h01, h0w, h0o, h0s, h0b, hag0⟩, he0⟩ => ?_
  have hk0 : ∀ k < b0 + 7, σ0 (.n k) = σA (.n k) := fun k hk => (hag0 k hk).symm
  -- the second sub-tree's address
  refine Completes.append (m := b0 + 125) (by omega) (by omega) (coordB_below b0) (coordB_complete (C := C)).withExt
    fun σB _ ⟨⟨hB, hagB⟩, heB⟩ => ?_
  have hkB : ∀ k < b0 + 123, σB (.n k) = σ0 (.n k) := fun k hk => (hagB k hk).symm
  have hLB : σB (.n (b0 + 124)) = eOfNat (fpos index.val c.val mark.super.val 1 0) := by
    rw [hB, hk0 _ (by omega), hLA, show (2 : Nat) ^ 39 = 2 ^ 39 * 1 by ring, sp_add_word (by unfold fpos; omega)]
    congr 1; unfold fpos; ring
  -- the second sub-tree
  have hpB : σB (.n 1) = σ (.n 1) := by rw [hkB 1 (by omega), hk0 1 (by omega), hkA _ hS1]
  have hmB : σB (.n 3) = σ (.n 3) := by rw [hkB 3 (by omega), hk0 3 (by omega), hkA _ hS3]
  have hsub1 := sSub_complete (C := C) (rd := rd) (c := c.val) (j := 1) hfk hrd (σ := σB)
    (by rw [hmB, hmd]) (by rw [hpB]; exact hpp) (b := b0 + 125) (by omega) ⟨b0 + 124, by omega, rfl⟩
    ⟨b0 + 122, by omega, rfl⟩ (by rw [hLB]; exact isCanonical128_eOfNat _) (mark.word 1).isLt ha1
    (finCells (opening.sub 1).values) (finCells (opening.sub 1).path) (canonical_finCells _)
    (canonical_finCells _)
  rw [sSub_snd, sSub_word, sSub_outs, sSub_bound] at hsub1
  have hsub1B := sSub_below (c := c.val) (j := 1) (b := b0 + 125) (by omega) ⟨b0 + 124, by omega, rfl⟩
    ⟨b0 + 122, by omega, rfl⟩ (subAt := .n (b0 + 124)) (bound := .n (b0 + 122))
  rw [sSub_snd] at hsub1B
  refine Completes.append (m := b0 + 241) (by omega) (by omega) hsub1B hsub1.withExt
    fun σ1 _ ⟨⟨h11, h1w, h1o, h1s, h1b, hag1⟩, he1⟩ => ?_
  have hk1 : ∀ k < b0 + 125, σ1 (.n k) = σB (.n k) := fun k hk => (hag1 k hk).symm
  have hq0 : (mark.child 0).val / 4 = 0 ∨ (mark.child 0).val / 4 = 1 := by omega
  have hq1 : (mark.child 1).val / 4 = 0 ∨ (mark.child 1).val / 4 = 1 := by omega
  have hqs : mark.super.val / 8 = 0 ∨ mark.super.val / 8 = 1 := by omega
  have hO : ∀ k (b : Nat), spOut subFoldT b k = .n (spOutN subFoldT b k) := fun k b => spOut_eq _ _ _
  have hON : ∀ k b, k < 3 → spOutN subFoldT b k = b + 12 + k := fun k b hk => by
    simp [spOutN, subFoldT, hk]
  -- the sub-trees' top nodes, kept
  have hX0 : ∀ k < 3, σ1 (spOut subFoldT (b0 + 21) k) = σ0 (spOut subFoldT (b0 + 21) k) := fun k hk => by
    rw [hO, hON k _ hk, hk1 _ (by omega), hkB _ (by omega)]
  have hcan0 : IsCanonical128 (σ0 (spOut subFoldT (b0 + 21) 0)) ∧ IsCanonical128 (σ0 (spOut subFoldT (b0 + 21) 2)) := by
    rcases hq0 with h | h <;> rw [h] at h0o h0s <;> simp only [Nat.mul_zero, Nat.mul_one, Nat.sub_zero,
      Nat.sub_self] at h0o h0s
    · exact ⟨by rw [h0o]; exact mFold_canon _ _ _ _ _ _ _ (Or.inl (by norm_num)),
        by rw [h0s]; exact canonical_finCells _ _⟩
    · exact ⟨by rw [h0s]; exact canonical_finCells _ _,
        by rw [h0o]; exact mFold_canon _ _ _ _ _ _ _ (Or.inl (by norm_num))⟩
  have hcan1 : IsCanonical128 (σ1 (spOut subFoldT (b0 + 139) 0)) ∧ IsCanonical128 (σ1 (spOut subFoldT (b0 + 139) 2)) := by
    rcases hq1 with h | h <;> rw [h] at h1o h1s <;> simp only [Nat.mul_zero, Nat.mul_one, Nat.sub_zero,
      Nat.sub_self] at h1o h1s
    · exact ⟨by rw [h1o]; exact mFold_canon _ _ _ _ _ _ _ (Or.inl (by norm_num)),
        by rw [h1s]; exact canonical_finCells _ _⟩
    · exact ⟨by rw [h1s]; exact canonical_finCells _ _,
        by rw [h1o]; exact mFold_canon _ _ _ _ _ _ _ (Or.inl (by norm_num))⟩
  have hp1 : σ1 (.n 1) = σ (.n 1) := by rw [hk1 1 (by omega), hpB]
  have hla1 : σ1 (.n (b0 + 6)) = eOfNat (fpos index.val c.val mark.super.val 0 0) := by
    rw [hk1 _ (by omega), hkB _ (by omega), hk0 _ (by omega), hLA]
  -- the super-child
  refine Completes.append (m := b0 + 253) (by omega) (by omega) (coordD_below b0)
    (coordD_complete (C := C) (rd := rd) (σ := σ1) (by rw [hp1]; exact hpp) (by rw [hla1]; exact isCanonical128_eOfNat _)
      ⟨by rw [hX0 0 (by omega)]; exact hcan0.1, by rw [hX0 2 (by omega)]; exact hcan0.2, hcan1.1, hcan1.2⟩).withExt
    fun σD _ ⟨⟨hD, hagD⟩, heD⟩ => ?_
  have hkD : ∀ k < b0 + 241, σD (.n k) = σ1 (.n k) := fun k hk => (hagD k hk).symm
  have hkD0 : ∀ v : V, NB b0 v → σD v = σ v := fun v ⟨k, hk, e⟩ => by
    rw [e, hkD k (by omega), hk1 k (by omega), hkB k (by omega), hk0 k (by omega), hkA _ ⟨k, hk, rfl⟩]
  -- the top tree
  have hM := spMatch_complete (C := C) (rd := rd) (σ := σD) (pp := .n 1) (md := .n 3) (adr := treeAt)
    (node := .n (b0 + 251)) (ret1 := .n (b0 + 1)) (x := .n b0) (F := topFoldT) (Or.inr rfl)
    (r1 := fun s => word (s * 2 ^ 35) 0 0) (r2 := fun s => lit (s * 2 ^ (26 + 4 * c.val))) (b := b0 + 253)
    (a := mark.super.val) hs16 ⟨hS1.mono (by omega), hS3.mono (by omega), htB.mono (by omega),
      ⟨b0 + 251, by omega, rfl⟩, ⟨b0 + 1, by omega, rfl⟩, ⟨b0, by omega, rfl⟩⟩
    (by rw [hkD0 _ hS3, hmd]) (by rw [hkD0 _ hS1]; exact hpp) (by rw [hkD0 _ htB, htree]; exact isCanonical128_eOfNat _)
    (by rw [hD]; exact (isCanonical128_hb _).1) (finCells opening.top) (canonical_finCells _)
    (by rw [hkD _ (by omega), hk1 _ (by omega), hkB _ (by omega), hk0 _ (by omega), hA0])
    (by rw [hkD _ (by omega), hk1 _ (by omega), hkB _ (by omega), hk0 _ (by omega), hA1])
  have hMB := spMatch_below (r1 := fun s => word (s * 2 ^ 35) 0 0) (r2 := fun s => lit (s * 2 ^ (26 + 4 * c.val)))
    (Or.inr rfl) (b := b0 + 253) (pp := .n 1) (md := .n 3) (adr := treeAt) (node := .n (b0 + 251))
    (ret1 := .n (b0 + 1)) (x := .n b0) (F := topFoldT)
    ⟨hS1.mono (by omega), hS3.mono (by omega), htB.mono (by omega), ⟨b0 + 251, by omega, rfl⟩,
      ⟨b0 + 1, by omega, rfl⟩, ⟨b0, by omega, rfl⟩⟩
  rw [← topArms, topArms_snd] at hM hMB
  refine Completes.append (m := b0 + 253 + 309) (by omega) (by omega) hMB hM.withExt
    fun σM _ ⟨⟨hMo, hMs, hMr⟩, heM⟩ => ?_
  have hkM : ∀ k < b0 + 253, σM (.n k) = σD (.n k) := fun k hk => (heM.agree k hk).symm
  set val := σM (.n (b0 + 240)) + σM (spRet2 topFoldT (b0 + 253))
  have hne : ∀ p, p < b0 + 253 + 309 → (V.n p) ≠ .n (b0 + 253 + 309) := fun p hp e => by
    simp only [V.mk.injEq] at e; omega
  have hR2 : spRet2 topFoldT (b0 + 253) = .n (b0 + 275) := by simp [spRet2, topFoldT]
  have hOT : ∀ k (b : Nat), spOut topFoldT b k = .n (spOutN topFoldT b k) := fun k b => spOut_eq _ _ _
  have hOTN : ∀ k b, k < 3 → spOutN topFoldT b k = b + 19 + k := fun k b hk => by
    simp [spOutN, topFoldT, hk]
  refine Completes.atom_cons val le_rfl ?_ ?_ (Completes.nil _ _ _ ?_)
  · simp only [Atom.vals, hR2]
    exact .cons ⟨_, by omega, rfl⟩ (.cons ⟨b0 + 240, by omega, rfl⟩ (.cons ⟨_, by omega, rfl⟩ (.nil _)))
  · show _ = _ + _
    rw [Function.update_self, Function.update_of_ne (hne _ (by omega)), hR2,
      Function.update_of_ne (hne _ (by omega)), ← hR2]
  · set σZ := Function.update σM (.n (b0 + 253 + 309)) val
    have hu : ∀ p, p < b0 + 253 + 309 → σZ (.n p) = σM (.n p) := fun p hp => Function.update_of_ne (hne p hp) _ _
    -- the cells, back to the stages that wrote them
    have hZ1 : ∀ p, p < b0 + 241 → σZ (.n p) = σ1 (.n p) := fun p hp => by
      rw [hu p (by omega), hkM p (by omega), hkD p hp]
    have hZ0 : ∀ p, p < b0 + 123 → σZ (.n p) = σ0 (.n p) := fun p hp => by
      rw [hZ1 p (by omega), hk1 p (by omega), hkB p hp]
    have hpA : σA (.n 1) = σ (.n 1) := hkA _ hS1
    have hfA : foldAddr σA (.n (b0 + 6)) subFoldT (mark.child 0).val =
        fun l => eOfNat (fpos index.val c.val mark.super.val 0 0) + word (subFoldT.addr (mark.child 0).val l) 0 0 := by
      funext l; rw [foldAddr, hLA]
    have hfB : foldAddr σB (.n (b0 + 124)) subFoldT (mark.child 1).val =
        fun l => eOfNat (fpos index.val c.val mark.super.val 1 0) + word (subFoldT.addr (mark.child 1).val l) 0 0 := by
      funext l; rw [foldAddr, hLB]
    have hkey0 : σA (.n (b0 + 6)) + word ((mark.child 0).val * 2 ^ 40) 0 0 =
        eOfNat (fpos index.val c.val mark.super.val 0 (mark.child 0).val) := by
      rw [hLA, show (mark.child 0).val * 2 ^ 40 = 2 ^ 40 * (mark.child 0).val by ring,
        sp_add_word (by unfold fpos; omega)]
      congr 1; unfold fpos; ring
    have hkey1 : σB (.n (b0 + 124)) + word ((mark.child 1).val * 2 ^ 40) 0 0 =
        eOfNat (fpos index.val c.val mark.super.val 1 (mark.child 1).val) := by
      rw [hLB, show (mark.child 1).val * 2 ^ 40 = 2 ^ 40 * (mark.child 1).val by ring,
        sp_add_word (by unfold fpos; omega)]
      congr 1; unfold fpos; ring
    rw [hpA, hfA, hkey0] at h0o
    rw [hpB, hfB, hkey1] at h1o
    have hfD : foldAddr σD treeAt topFoldT mark.super.val =
        fun l => eOfNat (fpos index.val c.val 0 0 0) + word (topFoldT.addr mark.super.val l) 0 0 := by
      funext l; rw [foldAddr, hkD0 _ htB, htree]
    rw [hkD0 _ hS1, hfD, show topFoldT.height - 1 = 3 from rfl, show (2 : Nat) ^ 3 = 8 from rfl] at hMo
    rw [show topFoldT.height - 1 = 3 from rfl, show (2 : Nat) ^ 3 = 8 from rfl] at hMs
    have hX00 : σZ (spOut subFoldT (b0 + 21) 0) = σ0 (spOut subFoldT (b0 + 21) 0) := by
      rw [hO, hON 0 _ (by omega)]; exact hZ0 _ (by omega)
    have hX02 : σZ (spOut subFoldT (b0 + 21) 2) = σ0 (spOut subFoldT (b0 + 21) 2) := by
      rw [hO, hON 2 _ (by omega)]; exact hZ0 _ (by omega)
    have hX10 : σZ (spOut subFoldT (b0 + 139) 0) = σ1 (spOut subFoldT (b0 + 139) 0) := by
      rw [hO, hON 0 _ (by omega)]; exact hZ1 _ (by omega)
    have hX12 : σZ (spOut subFoldT (b0 + 139) 2) = σ1 (spOut subFoldT (b0 + 139) 2) := by
      rw [hO, hON 2 _ (by omega)]; exact hZ1 _ (by omega)
    have hT0 : σZ (spOut topFoldT (b0 + 253) 0) = σM (spOut topFoldT (b0 + 253) 0) := by
      rw [hOT, hOTN 0 _ (by omega)]; exact hu _ (by omega)
    have hT2 : σZ (spOut topFoldT (b0 + 253) 2) = σM (spOut topFoldT (b0 + 253) 2) := by
      rw [hOT, hOTN 2 _ (by omega)]; exact hu _ (by omega)
    have hcanT : IsCanonical128 (σZ (spOut topFoldT (b0 + 253) 0)) ∧
        IsCanonical128 (σZ (spOut topFoldT (b0 + 253) 2)) := by
      rw [hT0, hT2]
      rcases hqs with h | h <;> rw [h] at hMo hMs <;> simp only [Nat.mul_zero, Nat.mul_one, Nat.sub_zero,
        Nat.sub_self] at hMo hMs
      · exact ⟨by rw [hMo]; exact mFold_canon _ _ _ _ _ _ _ (Or.inl (by norm_num)),
          by rw [hMs]; exact canonical_finCells _ _⟩
      · exact ⟨by rw [hMs]; exact canonical_finCells _ _,
          by rw [hMo]; exact mFold_canon _ _ _ _ _ _ _ (Or.inl (by norm_num))⟩
    refine ⟨?_, hcanT.1, hcanT.2, by rw [hZ0 _ (by omega)]; exact h0w, by rw [hZ1 _ (by omega)]; exact h1w, ?_,
      fun k hk => (hagA k hk).trans ((hk0 k (by omega)).symm.trans ((hkB k (by omega)).symm.trans
        ((hk1 k (by omega)).symm.trans ((hkD k (by omega)).symm.trans ((hkM k (by omega)).symm.trans
          (hu k (by omega)).symm)))))⟩
    · refine coordRecover_cells hq index c mark opening (finCells (opening.sub 0).values)
        (finCells (opening.sub 1).values) (finCells (opening.sub 0).path) (finCells (opening.sub 1).path)
        (finCells opening.top) (sv_finCells _) (sv_finCells _) (sv_finCells _) (sv_finCells _) (sv_finCells _)
        (X00 := σZ (spOut subFoldT (b0 + 21) 0)) (X02 := σZ (spOut subFoldT (b0 + 21) 2))
        (X10 := σZ (spOut subFoldT (b0 + 139) 0)) (X12 := σZ (spOut subFoldT (b0 + 139) 2))
        (SUP := σZ (.n (b0 + 251))) ?_ ?_ ?_ ?_ ?_ ?_ ?_
      · rw [hX00, hX02]
        rcases hq0 with h | h <;> rw [h] at h0o ⊢ <;> simp only [Nat.mul_zero, Nat.mul_one] at h0o <;> simp [h0o]
      · rw [hX00, hX02]
        rcases hq0 with h | h <;> rw [h] at h0s ⊢ <;> simp only [Nat.mul_zero, Nat.mul_one, Nat.sub_zero,
          Nat.sub_self] at h0s <;> simp [h0s]
      · rw [hX10, hX12]
        rcases hq1 with h | h <;> rw [h] at h1o ⊢ <;> simp only [Nat.mul_zero, Nat.mul_one] at h1o <;> simp [h1o]
      · rw [hX10, hX12]
        rcases hq1 with h | h <;> rw [h] at h1s ⊢ <;> simp only [Nat.mul_zero, Nat.mul_one, Nat.sub_zero,
          Nat.sub_self] at h1s <;> simp [h1s]
      · rw [hu _ (by omega), hkM _ (by omega), hD, hp1, hla1, hX00, hX02, hX10, hX12, hX0 0 (by omega),
          hX0 2 (by omega)]
      · rw [hT0, hT2, hu _ (by omega), hkM _ (by omega)]
        rcases hqs with h | h <;> rw [h] at hMo ⊢ <;> simp only [Nat.mul_zero, Nat.mul_one] at hMo <;> simp [hMo]
      · rw [hT0, hT2]
        rcases hqs with h | h <;> rw [h] at hMs ⊢ <;> simp only [Nat.mul_zero, Nat.mul_one, Nat.sub_zero,
          Nat.sub_self] at hMs <;> simp [hMs]
    · rw [show σZ (.n (b0 + 253 + 309)) = val from Function.update_self _ _ _]
      show σM (.n (b0 + 240)) + σM (spRet2 topFoldT (b0 + 253)) = _
      rw [hMr, hkM _ (by omega), hkD _ (by omega), h1b, hkB _ (by omega), h0b, hkA _ hbB, coordWeight]
      simp only [Nat.add_zero]
      abel

end Scheme

theorem sCoordT_snd (c : Nat) (bound treeAt : V) (b0 : Nat) : (sCoordT c bound treeAt b0).2.1 = b0 + 563 := by
  rw [sCoordT_eq]

theorem sCoordT_below {c : Nat} {bound treeAt : V} {b0 : Nat} (hb0 : 4 ≤ b0) (htB : NB b0 treeAt) (hbB : NB b0 bound) :
    NumBelow (sCoordT c bound treeAt b0).2.1 (Stmt.valsList (sCoordT c bound treeAt b0).1) := by
  rw [sCoordT_eq]
  dsimp only
  have h0 := sSub_below (c := c) (j := 0) (b := b0 + 7) (by omega) ⟨b0 + 6, by omega, rfl⟩ (hbB.mono (by omega))
  have h1 := sSub_below (c := c) (j := 1) (b := b0 + 125) (by omega) ⟨b0 + 124, by omega, rfl⟩
    ⟨b0 + 122, by omega, rfl⟩ (subAt := .n (b0 + 124)) (bound := .n (b0 + 122))
  rw [sSub_snd] at h0 h1
  have hM := spMatch_below (r1 := fun s => word (s * 2 ^ 35) 0 0) (r2 := fun s => lit (s * 2 ^ (26 + 4 * c)))
    (Or.inr rfl) (b := b0 + 253) (pp := .n 1) (md := .n 3) (adr := treeAt) (node := .n (b0 + 251))
    (ret1 := .n (b0 + 1)) (x := .n b0) (F := topFoldT)
    ⟨⟨1, by omega, rfl⟩, ⟨3, by omega, rfl⟩, htB.mono (by omega), ⟨b0 + 251, by omega, rfl⟩,
      ⟨b0 + 1, by omega, rfl⟩, ⟨b0, by omega, rfl⟩⟩
  rw [← topArms, topArms_snd] at hM
  simp only [valsList_append]
  refine ((coordA_below htB).mono (by omega)).append ((h0.mono (by omega)).append (((coordB_below b0).mono
    (by omega)).append ((h1.mono (by omega)).append (((coordD_below b0).mono (by omega)).append
      ((hM.mono (by omega)).append ?_)))))
  simp only [addS, valsList_cons, valsList_nil, Stmt.vals, Atom.vals, List.append_nil, spRet2, topFoldT]
  exact .cons ⟨_, by omega, rfl⟩ (.cons ⟨b0 + 240, by omega, rfl⟩ (.cons ⟨_, by omega, rfl⟩ (.nil _)))

theorem sCoord_snd (c : Nat) (bound : V) (b : Nat) : (sCoord c bound b).2.1 = b + (if c = 0 then 0 else 2) + 563 := by
  rw [sCoord_eq]; dsimp only; rw [sCoordT_snd]; split <;> omega

theorem sCoord_below {c : Nat} {bound : V} {b : Nat} (hb : 143 ≤ b) (hbB : NB b bound) :
    NumBelow (sCoord c bound b).2.1 (Stmt.valsList (sCoord c bound b).1) := by
  rw [sCoord_eq]
  dsimp only
  rw [valsList_append]
  by_cases h0 : c = 0
  · simp only [h0, ↓reduceIte, valsList_nil]
    exact (NumBelow.nil _).append (sCoordT_below (by omega) ⟨142, by omega, rfl⟩ hbB)
  · simp only [h0, ↓reduceIte]
    have := sCoordT_below (c := c) (bound := bound) (treeAt := .n (b + 1)) (b0 := b + 2) (by omega)
      ⟨b + 1, by omega, rfl⟩ (hbB.mono (by omega))
    refine NumBelow.append ?_ this
    rw [sCoordT_snd]
    simp only [cst, addS, valsList_cons, valsList_nil, Stmt.vals, Atom.vals, List.append_nil, List.cons_append,
      List.nil_append]
    exact .cons ⟨b, by omega, rfl⟩ (.cons ⟨b + 1, by omega, rfl⟩ (.cons ⟨142, by omega, rfl⟩ (.cons ⟨b, by omega, rfl⟩
      (.nil _))))

theorem sCoord_outs (c : Nat) (bound : V) (b : Nat) : ∃ b0, b ≤ b0 ∧ (sCoord c bound b).2.1 = b0 + 563 ∧
    (sCoord c bound b).2.2.1 = (.n (b0 + 20), .n (b0 + 138)) ∧
    (sCoord c bound b).2.2.2.1 = (.n (b0 + 272), .n (b0 + 274)) ∧ (sCoord c bound b).2.2.2.2 = .n (b0 + 562) := by
  refine ⟨if c = 0 then b else b + 2, by split <;> omega, ?_⟩
  rw [sCoord_eq]; dsimp only; rw [sCoordT_eq]; dsimp only
  simp only [spOut, topFoldT]
  norm_num

theorem sCoords_snd_ge : ∀ (m c : Nat) (bound : V) (b : Nat), b ≤ (sCoords m c bound b).2.1
  | 0, _, _, _ => le_rfl
  | m + 1, c, bound, b => by
      simp only [sCoords]
      have := sCoords_snd_ge m (c + 1) (sCoord c bound b).2.2.2.2 (sCoord c bound b).2.1
      obtain ⟨b0, hb0, h1, -⟩ := sCoord_outs c bound b
      omega

theorem sCoords_below : ∀ (m c : Nat) (bound : V) (b : Nat), 143 ≤ b → NB b bound →
    NumBelow (sCoords m c bound b).2.1 (Stmt.valsList (sCoords m c bound b).1)
  | 0, _, _, _, _, _ => NumBelow.nil _
  | m + 1, c, bound, b, hb, hbB => by
      simp only [sCoords, valsList_append]
      obtain ⟨b0, hb0, h1, -, -, h4⟩ := sCoord_outs c bound b
      have := sCoords_snd_ge m (c + 1) (sCoord c bound b).2.2.2.2 (sCoord c bound b).2.1
      exact ((sCoord_below hb hbB).mono this).append
        (sCoords_below m (c + 1) _ _ (by omega) ⟨b0 + 562, by omega, h4⟩)

section Scheme

open Sphincs Sphincs.Concrete

variable {inst : HasQuery Sphincs.HashSpec Id}

/-- **A coordinate is complete.** -/
theorem sCoord_complete (hq : SQ inst) (hfk : FkComplete C) (hrd : MemOK rd 256) {σ : Val}
    (hmd : σ (.n 3) = mdw 64 true) (hpp : IsCanonical128 (σ (.n 1))) (index : Index) (c : Coord)
    (hidx : σ (.n 142) = eOfNat index.val) {bound : V} {b : Nat} (hb : 143 ≤ b) (hbB : NB b bound)
    (mark : CoordMark) (opening : CoordOpening) :
    Completes C rd b (sCoord c.val bound b).2.1 (sCoord c.val bound b).1 σ (fun σ' =>
      @coordRecover Id _ inst (spp (σ (.n 1))) index c mark opening =
        (sv (σ' (sCoord c.val bound b).2.2.2.1.1), sv (σ' (sCoord c.val bound b).2.2.2.1.2)) ∧
      IsCanonical128 (σ' (sCoord c.val bound b).2.2.2.1.1) ∧ IsCanonical128 (σ' (sCoord c.val bound b).2.2.2.1.2) ∧
      σ' (sCoord c.val bound b).2.2.1.1 = word (mark.word 0).val 0 0 ∧
      σ' (sCoord c.val bound b).2.2.1.2 = word (mark.word 1).val 0 0 ∧
      σ' (sCoord c.val bound b).2.2.2.2 = σ bound + coordWeight c.val mark ∧ AgreeBelow b σ σ') := by
  have hidx' := index.isLt
  have hc8 := c.isLt
  simp only [totalHeight, forestCoords] at hidx' hc8
  rw [sCoord_eq]
  dsimp only
  by_cases h0 : c.val = 0
  · simp only [h0, ↓reduceIte, List.nil_append]
    have := sCoordT_complete (C := C) (rd := rd) hq hfk hrd hmd hpp index c (bound := bound) (treeAt := .n 142)
      (b0 := b) (by omega) ⟨142, by omega, rfl⟩ hbB (by rw [hidx]; congr 1; simp [fpos, h0]) mark opening
    rw [h0] at this
    exact this
  · simp only [h0, ↓reduceIte]
    have hpre : Completes C rd b (b + 2) [cst b (word (c.val * hiMul) 0 0), addS (.n (b + 1)) (.n 142) (.n b)] σ
        (fun σ' => σ' (.n (b + 1)) = eOfNat (fpos index.val c.val 0 0 0) ∧ AgreeBelow b σ σ') := by
      set σ' := upds σ [(b, word (c.val * hiMul) 0 0), (b + 1, σ (.n 142) + word (c.val * hiMul) 0 0)]
      have he : Ext b (b + 2) σ σ' := upds_ext σ _ (by simp)
      have hk : ∀ k < b, σ' (.n k) = σ (.n k) := fun k hk => (he.agree k hk).symm
      have v0 : σ' (.n b) = word (c.val * hiMul) 0 0 := by simp [σ', upds]
      have v1 : σ' (.n (b + 1)) = σ (.n 142) + word (c.val * hiMul) 0 0 := by simp [σ', upds]
      refine ⟨σ', he, ⟨?_, he.agree⟩, fun next kret hn => ?_⟩
      · rw [v1, hidx, show c.val * hiMul = 2 ^ 32 * c.val by simp only [hiMul]; ring, sp_add_word (by omega)]
        congr 1; simp only [fpos]; ring
      · simp only [cst, addS, holdsList_cons_atom, holdsList_nil, Atom.Holds]
        rw [v0, v1, hk 142 (by omega)]
        exact ⟨rfl, rfl, hn⟩
    refine Completes.append (m := b + 2) (by omega) (by rw [sCoordT_snd]; omega) ?_ hpre fun σ1 _ ⟨h1, hag1⟩ => ?_
    · simp only [cst, addS, valsList_cons, valsList_nil, Stmt.vals, Atom.vals, List.append_nil, List.cons_append,
        List.nil_append]
      exact .cons ⟨b, by omega, rfl⟩ (.cons ⟨b + 1, by omega, rfl⟩ (.cons ⟨142, by omega, rfl⟩ (.cons ⟨b, by omega, rfl⟩
        (.nil _))))
    have hk1 : ∀ k < b, σ1 (.n k) = σ (.n k) := fun k hk => (hag1 k hk).symm
    refine (sCoordT_complete (C := C) (rd := rd) hq hfk hrd (by rw [hk1 3 (by omega), hmd])
      (by rw [hk1 1 (by omega)]; exact hpp) index c (bound := bound) (treeAt := .n (b + 1)) (b0 := b + 2) (by omega)
      ⟨b + 1, by omega, rfl⟩ (hbB.mono (by omega)) h1 mark opening).mono le_rfl le_rfl fun σ2 ⟨h2, hc1, hc2, h3, h4, h5, hag2⟩ =>
      ⟨?_, hc1, hc2, h3, h4, ?_, fun k hk => (hag1 k hk).trans (hag2 k (by omega))⟩
    · rw [hk1 1 (by omega)] at h2; exact h2
    · rw [h5]; obtain ⟨kb, hkb, e⟩ := hbB; rw [e, hk1 kb hkb]

/-- **The coordinates are complete.** -/
theorem sCoords_complete (hq : SQ inst) (hfk : FkComplete C) (hrd : MemOK rd 256) (index : Index)
    (marks : Nat → CoordMark) (openings : Nat → CoordOpening) :
    ∀ (m c : Nat) (bound : V) (b : Nat) (σ : Val) (_ : c + m ≤ 8), 143 ≤ b → NB b bound →
      σ (.n 3) = mdw 64 true → IsCanonical128 (σ (.n 1)) → σ (.n 142) = eOfNat index.val →
      Completes C rd b (sCoords m c bound b).2.1 (sCoords m c bound b).1 σ (fun σ' =>
        (∀ r (hr : r < m),
          @coordRecover Id _ inst (spp (σ (.n 1))) index ⟨c + r, by simp only [forestCoords]; omega⟩
              (marks (c + r)) (openings (c + r)) =
            (sv (σ' ((sCoords m c bound b).2.2.2.1.getD r (.n 0, .n 0)).1),
              sv (σ' ((sCoords m c bound b).2.2.2.1.getD r (.n 0, .n 0)).2)) ∧
          IsCanonical128 (σ' ((sCoords m c bound b).2.2.2.1.getD r (.n 0, .n 0)).1) ∧
          IsCanonical128 (σ' ((sCoords m c bound b).2.2.2.1.getD r (.n 0, .n 0)).2) ∧
          σ' ((sCoords m c bound b).2.2.1.getD r (.n 0, .n 0)).1 = word ((marks (c + r)).word 0).val 0 0 ∧
          σ' ((sCoords m c bound b).2.2.1.getD r (.n 0, .n 0)).2 = word ((marks (c + r)).word 1).val 0 0) ∧
        σ' (sCoords m c bound b).2.2.2.2 = σ bound + ∑ r ∈ Finset.range m, coordWeight (c + r) (marks (c + r)) ∧
        AgreeBelow b σ σ')
  | 0, _, bound, b, σ, _, _, _, _, _, _ => Completes.nil _ _ _ ⟨fun _ h => absurd h (by omega), by simp [sCoords],
      fun _ _ => rfl⟩
  | m + 1, c, bound, b, σ, hcm, hb, hbB, hmd, hpp, hidx => by
      simp only [sCoords]
      obtain ⟨b0, hb0, hs1, hs2, hs3, hs4⟩ := sCoord_outs c bound b
      refine Completes.append (m := (sCoord c bound b).2.1) (by omega) (by
          have := sCoords_snd_ge m (c + 1) (sCoord c bound b).2.2.2.2 (sCoord c bound b).2.1; omega)
        (sCoord_below hb hbB)
        (sCoord_complete (C := C) (rd := rd) hq hfk hrd hmd hpp index ⟨c, by simp only [forestCoords]; omega⟩ hidx hb
          hbB (marks c) (openings c)) fun σ1 _ ⟨h1, hca, hcb, hw0, hw1, hbd, hag1⟩ => ?_
      have hk1 : ∀ k < b, σ1 (.n k) = σ (.n k) := fun k hk => (hag1 k hk).symm
      have hbound' : NB (sCoord c bound b).2.1 (sCoord c bound b).2.2.2.2 := ⟨b0 + 562, by omega, hs4⟩
      refine (sCoords_complete hq hfk hrd index marks openings m (c + 1) _ _ σ1 (by omega) (by omega) hbound'
        (by rw [hk1 3 (by omega), hmd]) (by rw [hk1 1 (by omega)]; exact hpp)
        (by rw [hk1 142 (by omega), hidx])).mono le_rfl le_rfl fun σ2 ⟨hr, hbs, hag2⟩ => ⟨fun r hr' => ?_, ?_, ?_⟩
      · have hk2 : ∀ k < b0 + 563, σ2 (.n k) = σ1 (.n k) := fun k hk => (hag2 k (by omega)).symm
        rcases r with _ | r
        · simp only [List.getD_cons_zero, Nat.add_zero]
          simp only at h1 hca hcb hw0 hw1
          rw [hs3] at h1 hca hcb
          rw [hs2] at hw0 hw1
          rw [hs2, hs3]
          rw [hk2 _ (by omega), hk2 _ (by omega), hk2 _ (by omega), hk2 _ (by omega)]
          exact ⟨h1, hca, hcb, hw0, hw1⟩
        · have := hr r (by omega)
          simp only [List.getD_cons_succ]
          have hF : (⟨c + (r + 1), by simp only [forestCoords]; omega⟩ : Coord) =
              ⟨c + 1 + r, by simp only [forestCoords]; omega⟩ := Fin.ext (by simp only; omega)
          rw [hk1 1 (by omega)] at this
          rw [hF, show c + (r + 1) = c + 1 + r by omega]
          exact this
      · have hk2 : ∀ k < b0 + 563, σ2 (.n k) = σ1 (.n k) := fun k hk => (hag2 k (by omega)).symm
        rw [hbs, Finset.sum_range_succ']
        have hb1 : σ1 (sCoord c bound b).2.2.2.2 = σ bound + coordWeight c (marks c) := hbd
        rw [hb1]
        have hsum : ∑ r ∈ Finset.range m, coordWeight (c + (r + 1)) (marks (c + (r + 1))) =
            ∑ r ∈ Finset.range m, coordWeight (c + 1 + r) (marks (c + 1 + r)) :=
          Finset.sum_congr rfl fun r _ => by rw [show c + (r + 1) = c + 1 + r by omega]
        rw [hsum, add_assoc, add_comm (∑ r ∈ Finset.range m, _)]
        simp only [Nat.add_zero]
      · exact fun k hk => (hag1 k hk).trans (hag2 k (by omega))

end Scheme

end
end LeanVM.Guest.B1.Sig
