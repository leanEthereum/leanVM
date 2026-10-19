/-
  LeanVM.Guest.B1.Sig.SphincsFoldComplete

  The forest folds are complete: a level, the levels of an arm, an arm with its outputs preset,
  and a fold's dispatch.
-/

module

public import LeanVM.Guest.B1.Sig.SphincsFold
public import LeanVM.Guest.B1.Sig.Walk
public import LeanVM.Guest.B1.Sig.Group
public import LeanVM.Guest.B1.Sig.XmssPrologue

namespace LeanVM.Guest.B1.Sig

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.Verifier
open LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Value

@[expose] public section

variable {C : CallRel} {rd : Reader}

/-- The node a level hashes, from the sibling `s` and the node reached `x`. -/
def lvlHash (pp A : E) (bit : Bool) (s x : E) : E × E :=
  hcell [pp, A, if bit then s else x, if bit then x else s]

/-- **A level is complete**: from the sibling `s`, its outputs preset to the hash. -/
theorem spLevel_complete {σ : Val} {pp md adr cur o0 o1 : V} {addr b : Nat} {bit : Bool} (hin : NB b pp ∧ NB b md ∧
    NB b adr ∧ NB b cur) (ho0 : Out b (b + 5) o0) (ho1 : Out b (b + 5) o1) (hmd : σ md = mdw 64 true)
    (hpp : IsCanonical128 (σ pp)) (hadr : IsCanonical128 (σ adr)) (hcur : IsCanonical128 (σ cur)) {s : E}
    (hs : IsCanonical128 s) (ho : (σ o0, σ o1) = lvlHash (σ pp) (σ adr + word addr 0 0) bit s (σ cur)) :
    Completes C rd b (b + 5) (spLevel pp md adr addr bit cur b o0 o1) σ (fun σ' => σ' (.n b) = s) := by
  obtain ⟨⟨kp, hkp, rfl⟩, ⟨km, hkm, rfl⟩, ⟨ka, hka, rfl⟩, ⟨kc, hkc, rfl⟩⟩ := hin
  set A := σ (.n ka) + word addr 0 0
  set vs : List E := [s, word addr 0 0, A, iv0, iv1]
  set σ' := upds σ ((List.range 5).map fun k => (b + k, vs.getD k 0))
  have he : Ext b (b + 5) σ σ' := upds_ext σ _ (by simp)
  have v : ∀ k < 5, σ' (.n (b + k)) = vs.getD k 0 := upds_range_at b _ 5 σ
  have hk : ∀ k < b, σ' (.n k) = σ (.n k) := fun k hk => (he.agree k hk).symm
  have hAc : IsCanonical128 A := isCanonical128_add hadr (isCanonical128_word _ _)
  refine ⟨σ', he, ?_, fun next kret hn => ?_⟩
  · have := v 0 (by omega); rwa [Nat.add_zero] at this
  · have hb0 : σ' (.n b) = s := by have := v 0 (by omega); rwa [Nat.add_zero] at this
    have hc4 : CompressCells ![σ (.n kp), A, if bit then s else σ (.n kc), if bit then σ (.n kc) else s] iv0 iv1
        (σ o0) (σ o1) (mdw 64 true) :=
      compress4_iff.mpr ⟨⟨hpp, hAc, by split <;> assumption, by split <;> assumption⟩, ho⟩
    cases bit <;>
    · simp only [spLevel, hintW, cst, addS, ivs, b2s, Bool.false_eq_true, ↓reduceIte, List.cons_append,
        List.nil_append, holdsList_cons_atom, holdsList_nil, Atom.Holds, true_and] at hc4 ⊢
      rw [v 1 (by omega), v 2 (by omega), v 3 (by omega), show b + 3 + 1 = b + 4 by omega, v 4 (by omega),
        hk ka hka, hk kp hkp, hk km hkm, hk kc hkc, hb0, he.out ho0, he.out ho1, hmd]
      simp only [vs, List.getD_cons_succ, List.getD_cons_zero]
      refine ⟨?_, ?_, ?_, ?_, hc4, hn⟩ <;> trivial

theorem spLevel_below {pp md adr cur o0 o1 : V} {addr b hi : Nat} {bit : Bool} (hin : NB hi pp ∧ NB hi md ∧
    NB hi adr ∧ NB hi cur) (ho0 : NB hi o0) (ho1 : NB hi o1) (hb : b + 5 ≤ hi) :
    NumBelow hi (Stmt.valsList (spLevel pp md adr addr bit cur b o0 o1)) := by
  obtain ⟨hp, hm, ha, hc⟩ := hin
  cases bit <;>
  · simp only [spLevel, hintW, cst, addS, ivs, b2s, Bool.false_eq_true, ↓reduceIte, List.cons_append, List.nil_append,
      valsList_cons, valsList_nil, Stmt.vals, Atom.vals, Hint.vals, Dest.vals, List.append_nil]
    exact .cons ⟨b, by omega, rfl⟩ (.cons ⟨b + 1, by omega, rfl⟩ (.cons ⟨b + 2, by omega, rfl⟩ (.cons ha
      (.cons ⟨b + 1, by omega, rfl⟩ (.cons ⟨b + 3, by omega, rfl⟩ (.cons ⟨b + 4, by omega, rfl⟩ (by
        first
        | exact .cons hp (.cons ⟨b + 2, by omega, rfl⟩ (.cons hc (.cons ⟨b, by omega, rfl⟩ (.cons ⟨b + 3, by omega, rfl⟩
            (.cons ⟨b + 4, by omega, rfl⟩ (.cons ho0 (.cons ho1 (.cons hm (.nil _)))))))))
        | exact .cons hp (.cons ⟨b + 2, by omega, rfl⟩ (.cons ⟨b, by omega, rfl⟩ (.cons hc (.cons ⟨b + 3, by omega, rfl⟩
            (.cons ⟨b + 4, by omega, rfl⟩ (.cons ho0 (.cons ho1 (.cons hm (.nil _))))))))))))))))

theorem spLevels_below {pp md adr : V} (F : Fold) (index : Nat) :
    ∀ (m l : Nat) (cur : V) (b : Nat), NB b pp ∧ NB b md ∧ NB b adr ∧ NB b cur →
      NumBelow (b + 7 * m) (Stmt.valsList (spLevels pp md adr F index m l cur b).1) ∧
        NB (b + 7 * m) (spLevels pp md adr F index m l cur b).2 ∧
        (0 < m → b ≤ ((spLevels pp md adr F index m l cur b).2).idx)
  | 0, _, cur, b, hin => ⟨.nil _, by simpa [spLevels] using hin.2.2.2, fun h => absurd h (by omega)⟩
  | m + 1, l, cur, b, ⟨hp, hm, ha, hc⟩ => by
      simp only [spLevels, valsList_append]
      obtain ⟨h1, h2, h3⟩ := spLevels_below F index m (l + 1) (.n (b + 5)) (b + 7)
        ⟨hp.mono (by omega), hm.mono (by omega), ha.mono (by omega), ⟨b + 5, by omega, rfl⟩⟩
      refine ⟨(spLevel_below ⟨hp.mono (by omega), hm.mono (by omega), ha.mono (by omega), hc.mono (by omega)⟩
          ⟨b + 5, by omega, rfl⟩ ⟨b + 6, by omega, rfl⟩ (by omega)).append (h1.mono (by omega)),
        h2.mono (by omega), fun _ => ?_⟩
      rcases m with _ | m
      · simp [spLevels]
      · have := h3 (by omega); omega

/-- **The levels of a fold are complete**, from canonical siblings. -/
theorem spLevels_complete {pp md adr : V} (F : Fold) (index : Nat) (sibs : Nat → E)
    (hsibs : ∀ l, IsCanonical128 (sibs l)) :
    ∀ (m l : Nat) (cur : V) (b : Nat) (σ : Val), NB b pp ∧ NB b md ∧ NB b adr ∧ NB b cur →
      σ md = mdw 64 true → IsCanonical128 (σ pp) → IsCanonical128 (σ adr) → IsCanonical128 (σ cur) →
      Completes C rd b (b + 7 * m) (spLevels pp md adr F index m l cur b).1 σ (fun σ' =>
        σ' (spLevels pp md adr F index m l cur b).2 =
          mFold (σ pp) (foldAddr σ adr F index) (fun l => index.testBit l) sibs m l (σ cur))
  | 0, _, cur, b, σ, _, _, _, _, _ => Completes.nil _ _ _ rfl
  | m + 1, l, cur, b, σ, ⟨hp, hm, ha, hc⟩, hmd, hpp, hadr, hcur => by
      simp only [spLevels]
      set h := lvlHash (σ pp) (σ adr + word (F.addr index l) 0 0) (index.testBit l) (sibs l) (σ cur)
      set σ1 := upds σ [(b + 5, h.1), (b + 6, h.2)]
      have he1 : Ext b (b + 7) σ σ1 := upds_ext σ _ (by simp)
      have hk1 : ∀ k < b, σ1 (.n k) = σ (.n k) := fun k hk => (he1.agree k hk).symm
      have hkeep : ∀ v : V, NB b v → σ1 v = σ v := fun v ⟨k, hk, e⟩ => by rw [e]; exact hk1 k hk
      have h5 : σ1 (.n (b + 5)) = h.1 := by simp [σ1, upds]
      have h6 : σ1 (.n (b + 6)) = h.2 := by simp [σ1, upds]
      obtain ⟨hbl, -, -⟩ := spLevels_below (pp := pp) (md := md) (adr := adr) F index m (l + 1) (.n (b + 5)) (b + 7)
        ⟨hp.mono (by omega), hm.mono (by omega), ha.mono (by omega), ⟨b + 5, by omega, rfl⟩⟩
      have hlvl : Completes C rd b (b + 7) (spLevel pp md adr (F.addr index l) (index.testBit l) cur b (.n (b + 5))
          (.n (b + 6))) σ (fun σ' => σ' (.n (b + 5)) = h.1 ∧ AgreeBelow b σ σ') := by
        refine Completes.of_ext he1 ((spLevel_complete (C := C) (rd := rd) ⟨hp, hm, ha, hc⟩
          (out_of_ge ⟨b + 5, le_rfl, rfl⟩) (out_of_ge ⟨b + 6, by omega, rfl⟩) (by rw [hkeep md hm, hmd])
          (by rw [hkeep pp hp]; exact hpp) (by rw [hkeep adr ha]; exact hadr) (by rw [hkeep cur hc]; exact hcur)
          (hsibs l) (by rw [h5, h6, hkeep pp hp, hkeep adr ha, hkeep cur hc])).withExt.mono le_rfl (by omega)
          fun σ' ⟨_, he'⟩ => ⟨by rw [he'.apply (Or.inr (by omega)), h5],
            fun k hk => (he1.agree k hk).trans (he'.agree k hk)⟩)
      refine Completes.append (m := b + 7) (by omega) (by omega)
        (spLevel_below ⟨hp.mono (by omega), hm.mono (by omega), ha.mono (by omega), hc.mono (by omega)⟩
          ⟨b + 5, by omega, rfl⟩ ⟨b + 6, by omega, rfl⟩ (by omega)) hlvl fun σ' _ ⟨hv5, hag⟩ => ?_
      have hk' : ∀ v : V, NB b v → σ' v = σ v := fun v ⟨k, hk, e⟩ => by rw [e]; exact (hag k hk).symm
      refine (spLevels_complete F index sibs hsibs m (l + 1) (.n (b + 5)) (b + 7) σ'
        ⟨hp.mono (by omega), hm.mono (by omega), ha.mono (by omega), ⟨b + 5, by omega, rfl⟩⟩
        (by rw [hk' md hm, hmd]) (by rw [hk' pp hp]; exact hpp) (by rw [hk' adr ha]; exact hadr)
        (by rw [hv5]; exact (isCanonical128_hb _).1)).mono (by omega) (by omega) fun σ'' h'' => ?_
      rw [h'', hk' pp hp, hv5, mFold]
      have hA : foldAddr σ' adr F index = foldAddr σ adr F index := by
        funext l'; simp only [foldAddr, hk' adr ha]
      rw [hA]
      rfl

/-- A completing block followed by statements that hold on any valuation it reaches. -/
theorem Completes.append_tail {lo hi : Nat} {xs ys : List Stmt} {σ : Val} {P : Val → Prop}
    (h : Completes C rd lo hi xs σ P)
    (hys : ∀ σ', Ext lo hi σ σ' → ∀ (next : Prop) (kret : List E → Prop), next → Stmt.HoldsList C rd σ' ys next kret) :
    Completes C rd lo hi (xs ++ ys) σ P := by
  obtain ⟨σ', he, hp, hh⟩ := h
  exact ⟨σ', he, hp, fun next kret hn => by rw [holdsList_append]; exact hh _ _ (hys σ' he next kret hn)⟩

/-- **An arm is complete**, its outputs and constants preset: the node reached, `height - 1` levels
up from the node over the siblings, in the outputs its top bit names. -/
theorem spArm_complete {σ : Val} {pp md adr node ret1 ret2 : V} {F : Fold} {out : Nat → V} {r1 r2 : E}
    {index b : Nat} (hF : 2 ≤ F.height) (hin : NB b pp ∧ NB b md ∧ NB b adr ∧ NB b node)
    (hout : ∀ k, Out b (b + 7 * (F.height - 2) + 5) (out k)) (hr1 : Out b (b + 7 * (F.height - 2) + 5) ret1)
    (hr2 : Out b (b + 7 * (F.height - 2) + 5) ret2) (hmd : σ md = mdw 64 true) (hpp : IsCanonical128 (σ pp))
    (hadr : IsCanonical128 (σ adr)) (hnode : IsCanonical128 (σ node)) (sibs : Nat → E)
    (hsibs : ∀ l, IsCanonical128 (sibs l))
    (ho : (σ (out (2 * (index / 2 ^ (F.height - 1)))), σ (out (2 * (index / 2 ^ (F.height - 1)) + 1))) =
      lvlHash (σ pp) (σ adr + word (F.addr index (F.height - 2)) 0 0) (index.testBit (F.height - 2))
        (sibs (F.height - 2)) (mFold (σ pp) (foldAddr σ adr F index) (fun l => index.testBit l) sibs
          (F.height - 2) 0 (σ node)))
    (hret1 : σ ret1 = r1) (hret2 : σ ret2 = r2) :
    Completes C rd b (b + 7 * (F.height - 2) + 5) (spArm pp md adr node F out ret1 ret2 r1 r2 index b) σ
      (fun _ => True) := by
  obtain ⟨hp, hm, ha, hn⟩ := hin
  obtain ⟨hlb, hlv, hlvge⟩ := spLevels_below (pp := pp) (md := md) (adr := adr) F index (F.height - 2) 0 node b
    ⟨hp, hm, ha, hn⟩
  simp only [spArm, List.append_assoc]
  refine Completes.append (m := b + 7 * (F.height - 2)) (by omega) (by omega) hlb
    (spLevels_complete F index sibs hsibs (F.height - 2) 0 node b σ ⟨hp, hm, ha, hn⟩ hmd hpp hadr hnode).withExt
    fun σ1 _ ⟨hv, he1⟩ => ?_
  have hk1 : ∀ v : V, NB b v → σ1 v = σ v := fun v hv' => he1.out (out_of_lt hv')
  have hko : ∀ v : V, Out b (b + 7 * (F.height - 2) + 5) v → σ1 v = σ v := fun v hv' =>
    he1.out (hv'.mono le_rfl (by omega))
  refine Completes.append_tail ((spLevel_complete (C := C) (rd := rd) (s := sibs (F.height - 2))
    ⟨hp.mono (by omega), hm.mono (by omega), ha.mono (by omega), hlv⟩
    ((hout _).mono (by omega) le_rfl) ((hout _).mono (by omega) le_rfl) (by rw [hk1 md hm, hmd])
    (by rw [hk1 pp hp]; exact hpp) (by rw [hk1 adr ha]; exact hadr) ?_ (hsibs _) ?_).mono (by omega) (by omega)
    fun _ _ => trivial) fun σ2 he2 next kret hnx => ?_
  · rw [hv]
    rcases Nat.eq_zero_or_pos (F.height - 2) with h0 | h0
    · rw [h0]; exact hnode
    · obtain ⟨k, hk⟩ : ∃ k, F.height - 2 = k + 1 := ⟨F.height - 2 - 1, by omega⟩
      rw [hk, mFold_succ]; exact (isCanonical128_hb _).1
  · rw [hko _ (hout _), hko _ (hout _), ho, hv, hk1 pp hp, hk1 adr ha]
  · simp only [hintW, holdsList_cons_atom, holdsList_nil, Atom.Holds, true_and]
    have hk2 : ∀ v : V, Out b (b + 7 * (F.height - 2) + 5) v → σ2 v = σ v := fun v hv' =>
      (he2.out (hv'.mono (by omega) le_rfl)).trans (hko v hv')
    exact ⟨by rw [hk2 _ hr1, hret1], by rw [hk2 _ hr2, hret2], hnx⟩

/-! ## A fold's dispatch -/

theorem spArms_get_base (pp md adr node : V) (F : Fold) (out : Nat → V) (ret1 ret2 : V) (r1 r2 : Nat → E) :
    ∀ (m a b j : Nat), j < m → (spArms pp md adr node F out ret1 ret2 r1 r2 m a b).1[j]? =
      some (spArm pp md adr node F out ret1 ret2 (r1 (a + j)) (r2 (a + j)) (a + j)
        (b + ∑ i ∈ Finset.range j, spArmSize F (a + i)))
  | 0, _, _, _, h => absurd h (by omega)
  | m + 1, a, b, 0, _ => by simp [spArms]
  | m + 1, a, b, j + 1, h => by
      simp only [spArms, List.getElem?_cons_succ]
      rw [spArms_get_base pp md adr node F out ret1 ret2 r1 r2 m (a + 1) _ j (by omega),
        show a + 1 + j = a + (j + 1) by omega, Finset.sum_range_succ' _ j, Nat.add_zero]
      have e : ∑ i ∈ Finset.range j, spArmSize F (a + 1 + i) = ∑ i ∈ Finset.range j, spArmSize F (a + (i + 1)) :=
        Finset.sum_congr rfl fun i _ => by rw [show a + 1 + i = a + (i + 1) by omega]
      rw [e, show b + spArmSize F a + ∑ i ∈ Finset.range j, spArmSize F (a + (i + 1)) =
        b + (∑ i ∈ Finset.range j, spArmSize F (a + (i + 1)) + spArmSize F a) by omega]
      simp only [Nat.add_zero]

theorem spArms_snd_eq (pp md adr node : V) (F : Fold) (out : Nat → V) (ret1 ret2 : V) (r1 r2 : Nat → E) :
    ∀ (m a b : Nat), (spArms pp md adr node F out ret1 ret2 r1 r2 m a b).2 =
      b + ∑ i ∈ Finset.range m, spArmSize F (a + i)
  | 0, _, b => by simp [spArms]
  | m + 1, a, b => by
      simp only [spArms]
      rw [spArms_snd_eq pp md adr node F out ret1 ret2 r1 r2 m (a + 1), Finset.sum_range_succ' _ m, Nat.add_zero]
      have e : ∑ i ∈ Finset.range m, spArmSize F (a + 1 + i) = ∑ i ∈ Finset.range m, spArmSize F (a + (i + 1)) :=
        Finset.sum_congr rfl fun i _ => by rw [show a + 1 + i = a + (i + 1) by omega]
      rw [e]
      simp only [Nat.add_zero]
      omega

theorem sum_arm_sizes {f : Nat → Nat} {X H : Nat} (hH : 0 < H)
    (hf : ∀ i, f i = X + (if i = 0 then 4 else if i = H then 1 else 0)) :
    ∀ a, ∑ i ∈ Finset.range a, f i = a * X + (if 0 < a then 4 else 0) + (if H < a then 1 else 0)
  | 0 => by simp
  | a + 1 => by
      rw [Finset.sum_range_succ, sum_arm_sizes hH hf a, hf, Nat.succ_mul]
      split_ifs <;> omega

/-- The base of arm `a` of a dispatch from `b`. -/
theorem spArm_base (F : Fold) (b a : Nat) :
    b + ∑ i ∈ Finset.range a, spArmSize F i =
      b + (a * (7 * (F.height - 2) + 5) + (if 0 < a then 4 else 0) + (if 2 ^ (F.height - 1) < a then 1 else 0)) := by
  rw [sum_arm_sizes (Nat.two_pow_pos _) (fun i => by unfold spArmSize; rfl) a]

/-- The number of output `k` of a dispatch from `b`. -/
def spOutN (F : Fold) (b k : Nat) : Nat :=
  if k < 3 then b + 7 * (F.height - 2) + 5 + k
  else b + 7 * (F.height - 2) + 9 + (2 ^ (F.height - 1) - 1) * (7 * (F.height - 2) + 5) + 7 * (F.height - 2) + 5

theorem spOut_eq (F : Fold) (b k : Nat) : spOut F b k = .n (spOutN F b k) := by
  unfold spOut spOutN; split <;> rfl

theorem spArm_below {pp md adr node ret1 ret2 : V} {F : Fold} {out : Nat → V} {r1 r2 : E} {index b hi : Nat}
    (hF : 2 ≤ F.height) (hidx : index < 2 ^ F.height) (hin : NB b pp ∧ NB b md ∧ NB b adr ∧ NB b node)
    (hout : ∀ k < 4, NB hi (out k)) (hr1 : NB hi ret1) (hr2 : NB hi ret2) (hb : b + 7 * (F.height - 2) + 5 ≤ hi) :
    NumBelow hi (Stmt.valsList (spArm pp md adr node F out ret1 ret2 r1 r2 index b)) := by
  obtain ⟨hp, hm, ha, hn⟩ := hin
  obtain ⟨hlb, hlv, -⟩ := spLevels_below (pp := pp) (md := md) (adr := adr) F index (F.height - 2) 0 node b
    ⟨hp, hm, ha, hn⟩
  have hh : index / 2 ^ (F.height - 1) < 2 :=
    Nat.div_lt_of_lt_mul (by rw [← pow_succ, show F.height - 1 + 1 = F.height by omega]; exact hidx)
  simp only [spArm, valsList_append]
  refine ((hlb.mono (by omega)).append (spLevel_below ⟨hp.mono (by omega), hm.mono (by omega), ha.mono (by omega),
    hlv.mono (by omega)⟩ (hout _ (by omega)) (hout _ (by omega)) (by omega))).append ?_
  simp only [hintW, valsList_cons, valsList_nil, Stmt.vals, Atom.vals, Hint.vals, Dest.vals, List.append_nil,
    List.cons_append, List.nil_append]
  exact .cons (hout _ (by omega)) (.cons hr1 (.cons hr2 (.nil _)))

/-- The layout of a dispatch over `2^height` arms, for the two folds' heights. -/
theorem spMatch_layout {F : Fold} (hF : F.height = 3 ∨ F.height = 4) {a b : Nat} (ha : a < 2 ^ F.height) :
    let sz := 7 * (F.height - 2) + 5
    let ba := b + (a * sz + (if 0 < a then 4 else 0) + (if 2 ^ (F.height - 1) < a then 1 else 0))
    let en := b + (2 ^ F.height * sz + 4 + 1)
    let h := a / 2 ^ (F.height - 1)
    let pR := b + 7 * (F.height - 2) + 8
    b ≤ ba ∧ ba + sz ≤ en ∧ 2 ≤ F.height ∧ h < 2 ∧
      (∀ k < 4, b ≤ spOutN F b k ∧ spOutN F b k < en ∧ (spOutN F b k < ba ∨ ba + sz ≤ spOutN F b k)) ∧
      b ≤ pR ∧ pR < en ∧ (pR < ba ∨ ba + sz ≤ pR) ∧
      spOutN F b (2 * h) ≠ spOutN F b (2 * h + 1) ∧ spOutN F b (2 * h) ≠ spOutN F b (2 - 2 * h) ∧
      spOutN F b (2 * h + 1) ≠ spOutN F b (2 - 2 * h) ∧ spOutN F b (2 * h) ≠ pR ∧
      spOutN F b (2 * h + 1) ≠ pR ∧ spOutN F b (2 - 2 * h) ≠ pR := by
  intro sz ba en h pR
  rcases hF with hh | hh <;> simp only [sz, ba, en, h, pR, spOutN, hh] at ha ⊢ <;>
    refine ⟨?_, ?_, ?_, ?_, fun k hk => ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> first | omega | (split_ifs <;> omega)

theorem spOutN_min (F : Fold) (b k : Nat) : spOutN F b k = spOutN F b (min k 3) := by
  unfold spOutN; split_ifs <;> omega

/-- **A fold's dispatch is complete**: at `x = g^a`, the fold of `node` at leaf `a` over the
siblings lands in the output the leaf's top bit names, the last sibling in the other, the arm's
second constant in `ret2`. -/
theorem spMatch_complete {σ : Val} {pp md adr node ret1 x : V} {F : Fold} (hF : F.height = 3 ∨ F.height = 4)
    {r1 r2 : Nat → E} {b a : Nat} (ha : a < 2 ^ F.height)
    (hin : NB b pp ∧ NB b md ∧ NB b adr ∧ NB b node ∧ NB b ret1 ∧ NB b x)
    (hmd : σ md = mdw 64 true) (hpp : IsCanonical128 (σ pp)) (hadr : IsCanonical128 (σ adr))
    (hnode : IsCanonical128 (σ node)) (sibs : Nat → E) (hsibs : ∀ l, IsCanonical128 (sibs l))
    (hx : σ x = ofK (gpow a)) (hret1 : σ ret1 = r1 a) :
    Completes C rd b (spArms pp md adr node F (spOut F b) ret1 (spRet2 F b) r1 r2 (2 ^ F.height) 0 b).2
      [.match_ x (spArms pp md adr node F (spOut F b) ret1 (spRet2 F b) r1 r2 (2 ^ F.height) 0 b).1] σ
      (fun σ' => σ' (spOut F b (2 * (a / 2 ^ (F.height - 1)))) =
          mFold (σ pp) (foldAddr σ adr F a) (fun l => a.testBit l) sibs (F.height - 1) 0 (σ node) ∧
        σ' (spOut F b (2 - 2 * (a / 2 ^ (F.height - 1)))) = sibs (F.height - 1) ∧ σ' (spRet2 F b) = r2 a) := by
  obtain ⟨hp, hm, hadB, hn, hr1B, hxB⟩ := hin
  obtain ⟨hba, hbae, h2, hh, hout, hpRb, hpRe, hpRo, d1, d2, d3, d4, d5, d6⟩ := spMatch_layout (b := b) hF ha
  have hH : 2 ^ (F.height - 1) < 2 ^ F.height := Nat.pow_lt_pow_right (by norm_num) (by omega)
  have hend : (spArms pp md adr node F (spOut F b) ret1 (spRet2 F b) r1 r2 (2 ^ F.height) 0 b).2 =
      b + (2 ^ F.height * (7 * (F.height - 2) + 5) + 4 + 1) := by
    rw [spArms_snd_eq]; simp only [Nat.zero_add]; rw [spArm_base]
    simp only [Nat.two_pow_pos, ↓reduceIte, hH]
  rw [hend]
  set ba := b + (a * (7 * (F.height - 2) + 5) + (if 0 < a then 4 else 0) + (if 2 ^ (F.height - 1) < a then 1 else 0))
  set en := b + (2 ^ F.height * (7 * (F.height - 2) + 5) + 4 + 1)
  set q := a / 2 ^ (F.height - 1)
  set pO := spOutN F b (2 * q)
  set pO1 := spOutN F b (2 * q + 1)
  set pS := spOutN F b (2 - 2 * q)
  set pR := b + 7 * (F.height - 2) + 8
  set y := mFold (σ pp) (foldAddr σ adr F a) (fun l => a.testBit l) sibs (F.height - 2) 0 (σ node)
  set o := lvlHash (σ pp) (σ adr + word (F.addr a (F.height - 2)) 0 0) (a.testBit (F.height - 2))
    (sibs (F.height - 2)) y
  set σ1 := upds σ [(pO, o.1), (pO1, o.2), (pS, sibs (F.height - 1)), (pR, r2 a)]
  have hmem : ∀ p ∈ [(pO, o.1), (pO1, o.2), (pS, sibs (F.height - 1)), (pR, r2 a)], b ≤ p.1 ∧ p.1 < en := by
    have := hout (2 * q) (by omega); have := hout (2 * q + 1) (by omega); have := hout (2 - 2 * q) (by omega)
    simp only [List.mem_cons, List.mem_nil_iff, or_false]
    rintro p (rfl | rfl | rfl | rfl) <;> omega
  have he1 : Ext b en σ σ1 := upds_ext σ _ hmem
  have hk1 : ∀ v : V, NB b v → σ1 v = σ v := fun v hv => he1.out (out_of_lt hv)
  have l1 : σ1 (.n pO) = o.1 := upds_cons_self _ _ _ _
  have l2 : σ1 (.n pO1) = o.2 := by
    simp only [σ1]; rw [upds_cons_ne _ _ _ (Ne.symm d1)]; exact upds_cons_self _ _ _ _
  have l3 : σ1 (.n pS) = sibs (F.height - 1) := by
    simp only [σ1]; rw [upds_cons_ne _ _ _ (Ne.symm d2), upds_cons_ne _ _ _ (Ne.symm d3)]; exact upds_cons_self _ _ _ _
  have l4 : σ1 (.n pR) = r2 a := by
    simp only [σ1]
    rw [upds_cons_ne _ _ _ (Ne.symm d4), upds_cons_ne _ _ _ (Ne.symm d5), upds_cons_ne _ _ _ (Ne.symm d6)]
    exact upds_cons_self _ _ _ _
  have houtA : ∀ k, Out ba (ba + (7 * (F.height - 2) + 5)) (spOut F b k) := fun k => by
    rw [spOut_eq, spOutN_min]
    rcases (hout (min k 3) (by omega)).2.2 with h' | h'
    · exact out_of_lt ⟨_, h', rfl⟩
    · exact out_of_ge ⟨_, h', rfl⟩
  have hR2 : Out ba (ba + (7 * (F.height - 2) + 5)) (spRet2 F b) := by
    rcases hpRo with h' | h'
    · exact out_of_lt ⟨pR, h', rfl⟩
    · exact out_of_ge ⟨pR, h', rfl⟩
  have hA : foldAddr σ1 adr F a = foldAddr σ adr F a := by funext l'; simp only [foldAddr, hk1 adr hadB]
  have harm := spArm_complete (C := C) (rd := rd) (σ := σ1) (pp := pp) (md := md) (adr := adr) (node := node)
    (ret1 := ret1) (ret2 := spRet2 F b) (F := F) (out := spOut F b) (r1 := r1 a) (r2 := r2 a) (index := a)
    (b := ba) (by omega) ⟨hp.mono hba, hm.mono hba, hadB.mono hba, hn.mono hba⟩ houtA (out_of_lt (hr1B.mono hba))
    hR2 (by rw [hk1 md hm, hmd]) (by rw [hk1 pp hp]; exact hpp) (by rw [hk1 adr hadB]; exact hadr)
    (by rw [hk1 node hn]; exact hnode) sibs hsibs
    (by rw [spOut_eq, spOut_eq, l1, l2, hk1 pp hp, hk1 adr hadB, hk1 node hn, hA]) (by rw [hk1 ret1 hr1B, hret1]) l4
  obtain ⟨σ', he', -, hh2⟩ := harm
  have hget := spArms_get_base pp md adr node F (spOut F b) ret1 (spRet2 F b) r1 r2 (2 ^ F.height) 0 b a ha
  rw [List.getElem?_eq_getElem (by rw [spArms_length]; exact ha), Option.some.injEq] at hget
  simp only [Nat.zero_add] at hget
  rw [spArm_base] at hget
  refine ⟨σ', he1.comp (he'.mono hba hbae), ⟨?_, ?_, ?_⟩, fun next kret hnx => ?_⟩
  · rw [he'.out (houtA _), spOut_eq, l1, show F.height - 1 = F.height - 2 + 1 by omega, mFold_succ]
    simp only [o, lvlHash, Nat.zero_add, foldAddr]
    rfl
  · rw [he'.out (houtA _), spOut_eq, l3]
  · rw [he'.out hR2]; exact l4
  · refine (holdsList_match_single x _ next kret σ').mpr ⟨a, by rw [spArms_length]; exact ha, ?_, ?_⟩
    · rw [he'.out (out_of_lt (hxB.mono hba)), hk1 x hxB, hx]
    · rw [hget]; exact hh2 next kret hnx

theorem spMatch_below {pp md adr node ret1 x : V} {F : Fold} (hF : F.height = 3 ∨ F.height = 4) {r1 r2 : Nat → E}
    {b : Nat} (hin : NB b pp ∧ NB b md ∧ NB b adr ∧ NB b node ∧ NB b ret1 ∧ NB b x) :
    NumBelow (spArms pp md adr node F (spOut F b) ret1 (spRet2 F b) r1 r2 (2 ^ F.height) 0 b).2
      (Stmt.valsList [.match_ x (spArms pp md adr node F (spOut F b) ret1 (spRet2 F b) r1 r2 (2 ^ F.height) 0 b).1]) := by
  obtain ⟨hp, hm, hadB, hn, hr1B, hxB⟩ := hin
  have hH : 2 ^ (F.height - 1) < 2 ^ F.height := Nat.pow_lt_pow_right (by norm_num) (by rcases hF with h | h <;> omega)
  have hend : (spArms pp md adr node F (spOut F b) ret1 (spRet2 F b) r1 r2 (2 ^ F.height) 0 b).2 =
      b + (2 ^ F.height * (7 * (F.height - 2) + 5) + 4 + 1) := by
    rw [spArms_snd_eq]; simp only [Nat.zero_add]; rw [spArm_base]
    simp only [Nat.two_pow_pos, ↓reduceIte, hH]
  rw [hend]
  simp only [valsList_cons, valsList_nil, Stmt.vals, List.append_nil]
  refine .cons (hxB.mono (by omega)) (numBelow_valsArms _ fun arm harm => ?_)
  obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp harm
  rw [spArms_length] at hj
  obtain ⟨hba, hbae, h2, -, hout, -, hpRe, -⟩ := spMatch_layout (b := b) hF hj
  have hget := spArms_get_base pp md adr node F (spOut F b) ret1 (spRet2 F b) r1 r2 (2 ^ F.height) 0 b j hj
  rw [List.getElem?_eq_getElem (by rw [spArms_length]; exact hj), Option.some.injEq] at hget
  simp only [Nat.zero_add] at hget
  rw [spArm_base] at hget
  rw [hget]
  exact spArm_below (by omega) hj ⟨hp.mono hba, hm.mono hba, hadB.mono hba, hn.mono hba⟩
    (fun k hk => by rw [spOut_eq]; exact ⟨_, (hout k hk).2.1, rfl⟩) (hr1B.mono (by omega)) ⟨_, hpRe, rfl⟩ hbae

end
end LeanVM.Guest.B1.Sig
