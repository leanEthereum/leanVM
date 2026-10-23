/-
  LeanVM.Guest.B1.Sig.Merkle

  `merkle_path` with `is_child` (G:2298-2304, G:2363-2382): the two children of each node hinted in
  order, the reached node checked to be the one the level's bit names, the parent hashed under
  the level's address; sound and complete for the fold of a path.
-/

module

public import LeanVM.Guest.B1.Sig.HashValues
public import LeanVM.Guest.Value.Bits

namespace LeanVM.Guest.B1.Sig

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.Blake2sHash
open LeanVM.Protocol.Verifier LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Value

@[expose] public section

variable {C : CallRel} {rd : Reader}

/-- The address cell of level `l`: the constant, plus the parent's index unless at the end. -/
def mAddr (σ : Val) (node : Nat → V) (addr : Nat → Nat) (isEnd : Nat → Bool) (l : Nat) : E :=
  if isEnd l then word (addr l) 0 0 else word (addr l) 0 0 + σ (node (l + 1))

/-- `m` levels of a path from `x` at level `l`: at each level the pair in the order of the bit,
the sibling the other child. -/
def mFold (pp : E) (A : Nat → E) (bits : Nat → Bool) (sibs : Nat → E) : Nat → Nat → E → E
  | 0, _, x => x
  | m + 1, l, x =>
      mFold pp A bits sibs m (l + 1) (hcell [pp, A l, if bits l then sibs l else x, if bits l then x else sibs l]).1

/-- `is_child`: `x + k0 = β (k0 + k1)` makes `x` the child the bit names, and the other the sibling. -/
theorem isChild_iff {x k0 k1 : E} (β : Bool) :
    x + k0 = bitE β * (k0 + k1) ↔ (if β then k1 else k0) = x := by
  cases β
  · simp only [bitE, Bool.false_eq_true, ↓reduceIte, zero_mul]
    rw [e_add_eq_zero_iff, eq_comm]
  · simp only [bitE, ↓reduceIte, one_mul]
    constructor
    · intro h
      exact (add_right_cancel (h.trans (add_comm k0 k1))).symm
    · rintro rfl
      exact add_comm _ _

theorem mFold_congr (pp : E) (A : Nat → E) (bits : Nat → Bool) {sibs sibs' : Nat → E} :
    ∀ (m l : Nat), (∀ l', l ≤ l' → l' < l + m → sibs l' = sibs' l') → ∀ x,
      mFold pp A bits sibs m l x = mFold pp A bits sibs' m l x
  | 0, _, _, _ => rfl
  | m + 1, l, h, x => by
      simp only [mFold]
      rw [h l le_rfl (by omega), mFold_congr pp A bits m (l + 1) (fun l' h1 h2 => h l' (by omega) (by omega))]

theorem mFold_congr2 (pp : E) (bits : Nat → Bool) {A A' : Nat → E} {sibs sibs' : Nat → E} :
    ∀ (m l : Nat), (∀ l', l ≤ l' → l' < l + m → A l' = A' l' ∧ sibs l' = sibs' l') → ∀ x,
      mFold pp A bits sibs m l x = mFold pp A' bits sibs' m l x
  | 0, _, _, _ => rfl
  | m + 1, l, h, x => by
      simp only [mFold]
      rw [(h l le_rfl (by omega)).1, (h l le_rfl (by omega)).2,
        mFold_congr2 pp bits m (l + 1) (fun l' h1 h2 => h l' (by omega) (by omega))]

theorem merkle_eq (pp : V) (bit node : Nat → V) (addr : Nat → Nat) (isEnd : Nat → Bool) (m l : Nat) (cur : V)
    (b : Nat) : merkle pp bit node addr isEnd (m + 1) l cur b =
      let a := if isEnd l then b + 4 else b + 5
      let rest := merkle pp bit node addr isEnd m (l + 1) (.n (a + 4)) (a + 6)
      ([hintW "siblings" [.n b, .n (b + 1)], addS (.n (b + 2)) cur (.n b),
        addS (.n (b + 3)) (.n b) (.n (b + 1)), mulS (.n (b + 2)) (bit l) (.n (b + 3)),
        cst (b + 4) (word (addr l) 0 0)] ++
        (if isEnd l then [] else [addS (.n (b + 5)) (.n (b + 4)) (node (l + 1))]) ++
        ivs (a + 1) ++ [cst (a + 3) (mdw 64 true),
          b2s pp (.n a) (.n b) (.n (b + 1)) (.n (a + 1)) (.n (a + 2)) (.n (a + 4)) (.n (a + 5)) (.n (a + 3))] ++
        rest.1, rest.2) := rfl

/-- One level's statements hold exactly when the children are in the order of the bit, the
address is the level's and the parent their hash. -/
theorem merkleLevel_iff {σ : Val} {pp cur : V} {bit node : Nat → V} {addr : Nat → Nat} {isEnd : Nat → Bool}
    {l b : Nat} {β : Bool} (hβ : σ (bit l) = bitE β) {X : Prop} {kret : List E → Prop} :
    let a := if isEnd l then b + 4 else b + 5
    Stmt.HoldsList C rd σ ([hintW "siblings" [.n b, .n (b + 1)], addS (.n (b + 2)) cur (.n b),
        addS (.n (b + 3)) (.n b) (.n (b + 1)), mulS (.n (b + 2)) (bit l) (.n (b + 3)),
        cst (b + 4) (word (addr l) 0 0)] ++
        (if isEnd l then [] else [addS (.n (b + 5)) (.n (b + 4)) (node (l + 1))]) ++
        ivs (a + 1) ++ [cst (a + 3) (mdw 64 true),
          b2s pp (.n a) (.n b) (.n (b + 1)) (.n (a + 1)) (.n (a + 2)) (.n (a + 4)) (.n (a + 5)) (.n (a + 3))]) X kret ↔
      (σ (.n (b + 2)) = σ cur + σ (.n b) ∧ σ (.n (b + 3)) = σ (.n b) + σ (.n (b + 1)) ∧
        σ (.n (b + 4)) = word (addr l) 0 0 ∧ (isEnd l = false → σ (.n (b + 5)) = σ (.n (b + 4)) + σ (node (l + 1))) ∧
        σ (.n (a + 1)) = iv0 ∧ σ (.n (a + 2)) = iv1 ∧ σ (.n (a + 3)) = mdw 64 true) ∧
      (if β then σ (.n (b + 1)) else σ (.n b)) = σ cur ∧
      (IsCanonical128 (σ pp) ∧ IsCanonical128 (mAddr σ node addr isEnd l) ∧ IsCanonical128 (σ (.n b)) ∧
        IsCanonical128 (σ (.n (b + 1)))) ∧
      (σ (.n (a + 4)), σ (.n (a + 5))) = hcell [σ pp, mAddr σ node addr isEnd l, σ (.n b), σ (.n (b + 1))] ∧ X := by
  intro a
  cases he : isEnd l
  · simp only [a, he, Bool.false_eq_true, ↓reduceIte, hintW, addS, mulS, cst, ivs, b2s, List.cons_append,
      List.nil_append, holdsList_cons_atom, holdsList_nil, Atom.Holds,
      true_and, forall_const]
    constructor
    · rintro ⟨h2, h3, h2', h4, h5, h6, h7, h8, hc, hX⟩
      rw [h2, hβ, h3, isChild_iff] at h2'
      rw [h6, h7, h8, h5, h4, compress4_iff] at hc
      refine ⟨⟨h2, h3, h4, h5, h6, h7, h8⟩, h2', ?_, ?_, hX⟩
      · simpa [mAddr, he] using hc.1
      · simpa [mAddr, he] using hc.2
    · rintro ⟨⟨h2, h3, h4, h5, h6, h7, h8⟩, h2', hcan, hh, hX⟩
      refine ⟨h2, h3, ?_, h4, h5, h6, h7, h8, ?_, hX⟩
      · rw [h2, hβ, h3, isChild_iff]; exact h2'
      · rw [h6, h7, h8, h5, h4, compress4_iff]
        exact ⟨by simpa [mAddr, he] using hcan, by simpa [mAddr, he] using hh⟩
  · simp only [a, he, ↓reduceIte, hintW, addS, mulS, cst, ivs, b2s, List.cons_append,
      List.nil_append, holdsList_cons_atom, holdsList_nil, Atom.Holds,
      true_and, List.append_nil, Bool.true_eq_false, IsEmpty.forall_iff]
    constructor
    · rintro ⟨h2, h3, h2', h4, h6, h7, h8, hc, hX⟩
      rw [h2, hβ, h3, isChild_iff] at h2'
      rw [h6, h7, h8, h4, compress4_iff] at hc
      refine ⟨⟨h2, h3, h4, h6, h7, h8⟩, h2', ?_, ?_, hX⟩
      · simpa [mAddr, he] using hc.1
      · simpa [mAddr, he] using hc.2
    · rintro ⟨⟨h2, h3, h4, h6, h7, h8⟩, h2', hcan, hh, hX⟩
      refine ⟨h2, h3, ?_, h4, h6, h7, h8, ?_, hX⟩
      · rw [h2, hβ, h3, isChild_iff]; exact h2'
      · rw [h6, h7, h8, h4, compress4_iff]
        exact ⟨by simpa [mAddr, he] using hcan, by simpa [mAddr, he] using hh⟩

/-- **A Merkle path is sound**: the root is the fold of the leaf along some siblings, in the
order of the bits. -/
theorem merkle_sound {σ : Val} {pp : V} {bit node : Nat → V} {addr : Nat → Nat} {isEnd : Nat → Bool}
    {β : Nat → Bool} : ∀ (m l : Nat) (cur : V) (b : Nat) {next : Prop} {kret : List E → Prop},
      (∀ l', l ≤ l' → l' < l + m → σ (bit l') = bitE (β l')) →
      Stmt.HoldsList C rd σ (merkle pp bit node addr isEnd m l cur b).1 next kret →
      (∃ sibs : Nat → E, σ (merkle pp bit node addr isEnd m l cur b).2.1 =
        mFold (σ pp) (mAddr σ node addr isEnd) β sibs m l (σ cur)) ∧ next
  | 0, _, _, _, _, _, _, h => ⟨⟨fun _ => 0, rfl⟩, h⟩
  | m + 1, l, cur, b, next, kret, hβ, h => by
      rw [merkle_eq] at h ⊢
      dsimp only at h ⊢
      rw [holdsList_append] at h
      obtain ⟨-, hord, -, hh, h⟩ := (merkleLevel_iff (hβ l le_rfl (by omega))).mp h
      obtain ⟨⟨sibs, hs⟩, hn⟩ := merkle_sound m (l + 1) _ _ (fun l' h1 h2 => hβ l' (by omega) (by omega)) h
      refine ⟨⟨fun l'' => if l'' = l then (if β l then σ (.n b) else σ (.n (b + 1))) else sibs l'', ?_⟩, hn⟩
      have hc := mFold_congr (σ pp) (mAddr σ node addr isEnd) β
        (sibs := fun l'' => if l'' = l then (if β l then σ (.n b) else σ (.n (b + 1))) else sibs l'')
        (sibs' := sibs) m (l + 1) (fun l' h1 _ => by simp [show l' ≠ l by omega])
      rw [hs, mFold, hc]
      congr 1
      have h1 := congrArg Prod.fst hh
      simp only at h1
      rw [h1]
      cases hb : β l <;> simp [hb] at hord ⊢ <;> rw [hord]

theorem upds_ne (σ : Val) {j : Nat} (l : List (Nat × E)) (h : ∀ p ∈ l, j ≠ p.1) : upds σ l (.n j) = σ (.n j) :=
  upds_of_not_mem σ l fun p hp e => h p hp (by simpa using e)

theorem merkleLevel_below {pp cur : V} {bit node : Nat → V} {addr : Nat → Nat} {isEnd : Nat → Bool} {l b : Nat}
    (hpp : NB b pp) (hcur : NB b cur) (hb1 : NB b (bit l)) (hn1 : NB b (node (l + 1))) :
    let a := if isEnd l then b + 4 else b + 5
    NumBelow (a + 6) (Stmt.valsList ([hintW "siblings" [.n b, .n (b + 1)], addS (.n (b + 2)) cur (.n b),
        addS (.n (b + 3)) (.n b) (.n (b + 1)), mulS (.n (b + 2)) (bit l) (.n (b + 3)),
        cst (b + 4) (word (addr l) 0 0)] ++
        (if isEnd l then [] else [addS (.n (b + 5)) (.n (b + 4)) (node (l + 1))]) ++
        ivs (a + 1) ++ [cst (a + 3) (mdw 64 true),
          b2s pp (.n a) (.n b) (.n (b + 1)) (.n (a + 1)) (.n (a + 2)) (.n (a + 4)) (.n (a + 5)) (.n (a + 3))])) := by
  intro a
  have ha : a = if isEnd l then b + 4 else b + 5 := rfl
  have hpp' := hpp.mono (show b ≤ a + 6 by rw [ha]; split <;> omega)
  cases hE : isEnd l <;> simp only [hE, ↓reduceIte, Bool.false_eq_true] at ha <;>
    simp only [↓reduceIte, Bool.false_eq_true, hintW, addS, mulS, cst, ivs, b2s, List.cons_append,
      List.nil_append, List.append_nil, valsList_cons, valsList_nil, Stmt.vals, Atom.vals, Hint.vals, Dest.vals]
  · exact .cons ⟨b, by omega, rfl⟩ (.cons ⟨b + 1, by omega, rfl⟩ (.cons ⟨b + 2, by omega, rfl⟩
      (.cons (hcur.mono (by omega)) (.cons ⟨b, by omega, rfl⟩ (.cons ⟨b + 3, by omega, rfl⟩
      (.cons ⟨b, by omega, rfl⟩ (.cons ⟨b + 1, by omega, rfl⟩ (.cons ⟨b + 2, by omega, rfl⟩
      (.cons (hb1.mono (by omega)) (.cons ⟨b + 3, by omega, rfl⟩ (.cons ⟨b + 4, by omega, rfl⟩
      (.cons ⟨b + 5, by omega, rfl⟩ (.cons ⟨b + 4, by omega, rfl⟩ (.cons (hn1.mono (by omega))
      (.cons ⟨a + 1, by omega, rfl⟩ (.cons ⟨a + 2, by omega, rfl⟩ (.cons ⟨a + 3, by omega, rfl⟩
      (.cons hpp' (.cons ⟨a, by omega, rfl⟩ (.cons ⟨b, by omega, rfl⟩ (.cons ⟨b + 1, by omega, rfl⟩
      (.cons ⟨a + 1, by omega, rfl⟩ (.cons ⟨a + 2, by omega, rfl⟩ (.cons ⟨a + 4, by omega, rfl⟩
      (.cons ⟨a + 5, by omega, rfl⟩ (.cons ⟨a + 3, by omega, rfl⟩ (.nil _)))))))))))))))))))))))))))
  · exact .cons ⟨b, by omega, rfl⟩ (.cons ⟨b + 1, by omega, rfl⟩ (.cons ⟨b + 2, by omega, rfl⟩
      (.cons (hcur.mono (by omega)) (.cons ⟨b, by omega, rfl⟩ (.cons ⟨b + 3, by omega, rfl⟩
      (.cons ⟨b, by omega, rfl⟩ (.cons ⟨b + 1, by omega, rfl⟩ (.cons ⟨b + 2, by omega, rfl⟩
      (.cons (hb1.mono (by omega)) (.cons ⟨b + 3, by omega, rfl⟩ (.cons ⟨b + 4, by omega, rfl⟩
      (.cons ⟨a + 1, by omega, rfl⟩ (.cons ⟨a + 2, by omega, rfl⟩ (.cons ⟨a + 3, by omega, rfl⟩
      (.cons hpp' (.cons ⟨a, by omega, rfl⟩ (.cons ⟨b, by omega, rfl⟩ (.cons ⟨b + 1, by omega, rfl⟩
      (.cons ⟨a + 1, by omega, rfl⟩ (.cons ⟨a + 2, by omega, rfl⟩ (.cons ⟨a + 4, by omega, rfl⟩
      (.cons ⟨a + 5, by omega, rfl⟩ (.cons ⟨a + 3, by omega, rfl⟩ (.nil _))))))))))))))))))))))))

theorem merkle_snd_ge (pp : V) (bit node : Nat → V) (addr : Nat → Nat) (isEnd : Nat → Bool) :
    ∀ (m l : Nat) (cur : V) (b : Nat), b ≤ (merkle pp bit node addr isEnd m l cur b).2.2
  | 0, _, _, _ => le_rfl
  | m + 1, l, cur, b => by
      rw [merkle_eq]
      dsimp only
      exact le_trans (by split <;> omega) (merkle_snd_ge pp bit node addr isEnd m (l + 1) _ _)

/-- **A Merkle path is complete**: from any siblings, the children hinted in the bits' order. -/
theorem merkle_complete {pp : V} {bit node : Nat → V} {addr : Nat → Nat} {isEnd : Nat → Bool}
    {β : Nat → Bool} {sibs : Nat → E} :
    ∀ (m l : Nat) (cur : V) (b : Nat) (σ : Val), NB b pp → NB b cur →
      (∀ l', l ≤ l' → l' < l + m → NB b (bit l') ∧ NB b (node (l' + 1))) →
      (∀ l', l ≤ l' → l' < l + m → σ (bit l') = bitE (β l') ∧ IsCanonical128 (sibs l') ∧
        IsCanonical128 (mAddr σ node addr isEnd l')) →
      IsCanonical128 (σ pp) → IsCanonical128 (σ cur) →
      Completes C rd b (merkle pp bit node addr isEnd m l cur b).2.2 (merkle pp bit node addr isEnd m l cur b).1 σ
        (fun σ' => σ' (merkle pp bit node addr isEnd m l cur b).2.1 =
          mFold (σ pp) (mAddr σ node addr isEnd) β sibs m l (σ cur))
  | 0, _, _, _, σ, _, _, _, _, _, _ => ⟨σ, Ext.refl _ _ _, rfl, fun _ _ hn => hn⟩
  | m + 1, l, cur, b, σ, hpp, hcur, hin, hval, hppc, hcurc => by
      rw [merkle_eq]
      dsimp only
      set a := if isEnd l then b + 4 else b + 5 with ha
      have hab : b + 4 ≤ a ∧ a ≤ b + 5 := by rw [ha]; split <;> omega
      set x := σ cur
      set A := mAddr σ node addr isEnd l
      set k0 := if β l then sibs l else x
      set k1 := if β l then x else sibs l
      set h := hcell [σ pp, A, k0, k1]
      obtain ⟨hβl, hsc, hAc⟩ := hval l le_rfl (by omega)
      have hk0c : IsCanonical128 k0 := by simp only [k0]; split <;> assumption
      have hk1c : IsCanonical128 k1 := by simp only [k1]; split <;> assumption
      -- the level's valuation
      let L : List (Nat × E) := [(b, k0), (b + 1, k1), (b + 2, x + k0), (b + 3, k0 + k1),
        (b + 4, word (addr l) 0 0)] ++ (if isEnd l then [] else [(b + 5, A)]) ++
        [(a + 1, iv0), (a + 2, iv1), (a + 3, mdw 64 true), (a + 4, h.1), (a + 5, h.2)]
      let σ1 := upds σ L
      have hL : ∀ p ∈ L, b ≤ p.1 ∧ p.1 < a + 6 := by
        simp only [L, List.forall_mem_append, List.forall_mem_cons]
        split <;> simp <;> omega
      have he1 : Ext b (a + 6) σ σ1 := upds_ext σ L hL
      have hσ1 : σ1 (.n b) = k0 ∧ σ1 (.n (b + 1)) = k1 ∧ σ1 (.n (b + 2)) = x + k0 ∧
          σ1 (.n (b + 3)) = k0 + k1 ∧ σ1 (.n (b + 4)) = word (addr l) 0 0 ∧
          (isEnd l = false → σ1 (.n (b + 5)) = A) ∧ σ1 (.n (a + 1)) = iv0 ∧ σ1 (.n (a + 2)) = iv1 ∧
          σ1 (.n (a + 3)) = mdw 64 true ∧ σ1 (.n (a + 4)) = h.1 ∧ σ1 (.n (a + 5)) = h.2 := by
        cases hE : isEnd l <;> simp only [hE, ↓reduceIte, Bool.false_eq_true] at ha <;>
          simp only [σ1, L, hE, ↓reduceIte, Bool.false_eq_true, List.cons_append, List.nil_append,
            List.append_nil] <;>
          refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
          first
          | (intro hf; exact Bool.noConfusion hf)
          | ((try intro); simp (disch := omega) only [upds_cons_self, upds_cons_ne])
      have hk : ∀ {v : V}, NB b v → σ1 v = σ v := fun hv => he1.below hv
      obtain ⟨hb0, hb1, hb2, hb3, hb4, hb5, ha1, ha2, ha3, ha4, ha5⟩ := hσ1
      have hA1 : mAddr σ1 node addr isEnd l = A := by
        simp only [mAddr, A]; rw [hk (hin l le_rfl (by omega)).2]
      refine Completes.append (m := a + 6) (P := fun σ' => σ' (.n (a + 4)) = h.1 ∧ Ext b (a + 6) σ σ') (by omega)
        (merkle_snd_ge _ _ _ _ _ _ _ _ _) ?_ ⟨σ1, he1, ⟨ha4, he1⟩, fun next kret hn => ?_⟩ ?_
      · exact merkleLevel_below hpp hcur (hin l le_rfl (by omega)).1 (hin l le_rfl (by omega)).2
      · refine (merkleLevel_iff (hβ := by rw [hk (hin l le_rfl (by omega)).1]; exact hβl)).mpr
          ⟨⟨by rw [hb2, hb0, hk hcur], by rw [hb3, hb0, hb1], hb4, fun hE => by
            rw [hb5 hE, hb4, hk (hin l le_rfl (by omega)).2]; simp [A, mAddr, hE], ha1, ha2, ha3⟩, ?_, ?_, ?_, hn⟩
        · rw [hb0, hb1, hk hcur]; cases hb : β l <;> simp [k0, k1, hb, x]
        · rw [hk hpp, hA1, hb0, hb1]; exact ⟨hppc, hAc, hk0c, hk1c⟩
        · rw [ha4, ha5, hk hpp, hA1, hb0, hb1]
      · intro σ' he' ⟨hσ'4, he''⟩
        have hk' : ∀ {v : V}, NB b v → σ' v = σ v := fun hv => he''.below hv
        have := merkle_complete (sibs := sibs) m (l + 1) (.n (a + 4)) (a + 6) σ' (hpp.mono (by omega)) ⟨_, by omega, rfl⟩
          (fun l' h1 h2 => ⟨(hin l' (by omega) (by omega)).1.mono (by omega), (hin l' (by omega) (by omega)).2.mono (by omega)⟩)
          (fun l' h1 h2 => by
            obtain ⟨e1, e2, e3⟩ := hval l' (by omega) (by omega)
            refine ⟨by rw [hk' (hin l' (by omega) (by omega)).1]; exact e1, e2, ?_⟩
            have : mAddr σ' node addr isEnd l' = mAddr σ node addr isEnd l' := by
              simp only [mAddr]; rw [hk' (hin l' (by omega) (by omega)).2]
            rw [this]; exact e3)
          (by rw [hk' hpp]; exact hppc) (by rw [hσ'4]; exact (isCanonical128_hb _).1)
        refine this.mono le_rfl le_rfl fun σ'' h'' => ?_
        rw [h'', hk' hpp, hσ'4, mFold]
        refine mFold_congr2 _ _ m (l + 1) (fun l' h1 h2 => ⟨?_, rfl⟩) _
        simp only [mAddr]; rw [hk' (hin l' (by omega) (by omega)).2]

theorem merkle_below {pp : V} {bit node : Nat → V} {addr : Nat → Nat} {isEnd : Nat → Bool} :
    ∀ (m l : Nat) (cur : V) (b : Nat), NB b pp → NB b cur →
      (∀ l', l ≤ l' → l' < l + m → NB b (bit l') ∧ NB b (node (l' + 1))) →
      NumBelow (merkle pp bit node addr isEnd m l cur b).2.2 (Stmt.valsList (merkle pp bit node addr isEnd m l cur b).1)
  | 0, _, _, _, _, _, _ => NumBelow.nil _
  | m + 1, l, cur, b, hpp, hcur, hin => by
      rw [merkle_eq]
      dsimp only
      have hab : b + 4 ≤ (if isEnd l then b + 4 else b + 5) := by split <;> omega
      have hr := merkle_snd_ge pp bit node addr isEnd m (l + 1) (.n ((if isEnd l then b + 4 else b + 5) + 4))
        ((if isEnd l then b + 4 else b + 5) + 6)
      rw [valsList_append]
      exact ((merkleLevel_below hpp hcur (hin l le_rfl (by omega)).1 (hin l le_rfl (by omega)).2).mono hr).append
        (merkle_below m (l + 1) _ _ (hpp.mono (by omega)) ⟨_, by omega, rfl⟩
          (fun l' h1 h2 => ⟨(hin l' (by omega) (by omega)).1.mono (by omega),
            (hin l' (by omega) (by omega)).2.mono (by omega)⟩))

end
end LeanVM.Guest.B1.Sig
