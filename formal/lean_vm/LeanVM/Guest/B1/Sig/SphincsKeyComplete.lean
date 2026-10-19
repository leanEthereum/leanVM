/-
  LeanVM.Guest.B1.Sig.SphincsKeyComplete

  `sp_forest_key__L{t}` is complete: for canonical values at a canonical address, it returns the
  child leaf of codeword `t`'s chains and `t`.
-/

module

public import LeanVM.Guest.B1.Sig.SphincsKey
public import LeanVM.Guest.B1.Sig.XmssPrologue

namespace LeanVM.Guest.B1.Sig

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.Blake2sHash
open LeanVM.Protocol.Verifier LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Value

@[expose] public section

variable {C : CallRel} {rd : Reader}

/-! ## A step of a forest chain -/

/-- Step `j` of forest chain `i` walked its deficit `d` from base `b`. -/
def fkStepBlock (i d b j : Nat) : List Stmt :=
  let c := b + 1 + 8 * j
  [cst c (word (tw 15 + i * 2 ^ 43 + (4 - d + j) * stepMul) 0 0), addS (.n (c + 1)) (.n 0) (.n c),
    cst (c + 2) (word 0 0 0)] ++ ivs (c + 3) ++ [cst (c + 5) (mdw 48 true),
    b2s (.n 1) (.n (c + 1)) (if j = 0 then .n b else .n (c - 2)) (.n (c + 2)) (.n (c + 3))
      (.n (c + 4)) (.n (c + 6)) (.n (c + 7)) (.n (c + 5))]

theorem fkChain_eq (i d b : Nat) :
    fkChain i d b = hintW "sp_forest_values" [.n b] :: (List.range d).flatMap (fkStepBlock i d b) := rfl

/-- The value a step reads. -/
def fkPrev (b j : Nat) : V := if j = 0 then .n b else .n (b + 1 + 8 * j - 2)

theorem fkPrev_after (σ : Val) (b j : Nat) : σ (fkPrev b j) = fkAfter σ b j := by
  unfold fkPrev fkAfter
  split
  · rfl
  · congr 2; omega

theorem fkStepBlock_below (i d b j : Nat) (hb : 2 ≤ b) :
    NumBelow (b + 1 + 8 * j + 8) (Stmt.valsList (fkStepBlock i d b j)) := by
  by_cases hj : j = 0
  · simp only [fkStepBlock, hj, ↓reduceIte, ivs, cst, addS, b2s, List.cons_append, List.nil_append, valsList_cons,
      valsList_nil, Stmt.vals, Atom.vals, List.append_nil]
    repeat (first | exact .nil _ | refine .cons ⟨_, by omega, rfl⟩ ?_)
  · simp only [fkStepBlock, hj, ↓reduceIte, ivs, cst, addS, b2s, List.cons_append, List.nil_append, valsList_cons,
      valsList_nil, Stmt.vals, Atom.vals, List.append_nil]
    repeat (first | exact .nil _ | (refine .cons ⟨_, ?_, rfl⟩ ?_; omega))

/-- **A step is complete**: the next value is the hash of the parameter, the step's address and
the value read. -/
theorem fkStep_complete {σ : Val} {i d b j : Nat} (hb : 2 ≤ b) (hpp : IsCanonical128 (σ (.n 1)))
    (hka : IsCanonical128 (σ (.n 0))) (hprev : IsCanonical128 (σ (fkPrev b j))) :
    Completes C rd (b + 1 + 8 * j) (b + 1 + 8 * j + 8) (fkStepBlock i d b j) σ (fun σ' =>
      σ' (.n (b + 1 + 8 * j + 6)) = (hcell [σ (.n 1), σ (.n 0) + eOfNat (tw 15 + i * 2 ^ 43 + (4 - d + j) * stepMul),
        σ (fkPrev b j)]).1 ∧ AgreeBelow (b + 1 + 8 * j) σ σ') := by
  set c := b + 1 + 8 * j with hc
  set A := word (tw 15 + i * 2 ^ 43 + (4 - d + j) * stepMul) 0 0
  set o := hcell [σ (.n 1), σ (.n 0) + A, σ (fkPrev b j)]
  set vs : List E := [A, σ (.n 0) + A, 0, iv0, iv1, mdw 48 true, o.1, o.2]
  set σ' := upds σ ((List.range 8).map fun k => (c + k, vs.getD k 0))
  have he : Ext c (c + 8) σ σ' := upds_ext σ _ (by simp)
  have v : ∀ k < 8, σ' (.n (c + k)) = vs.getD k 0 := upds_range_at c _ 8 σ
  have hk : ∀ k < c, σ' (.n k) = σ (.n k) := fun k hk => (he.agree k hk).symm
  have hpv : σ' (fkPrev b j) = σ (fkPrev b j) := by
    unfold fkPrev; split <;> exact hk _ (by omega)
  have hAc : IsCanonical128 (σ (.n 0) + A) := isCanonical128_add hka (isCanonical128_word _ _)
  have hcmp : CompressCells ![σ (.n 1), σ (.n 0) + A, σ (fkPrev b j), 0] iv0 iv1 o.1 o.2 (mdw 48 true) :=
    compress3_iff.mpr ⟨⟨hpp, hAc, hprev⟩, rfl⟩
  refine ⟨σ', he, ⟨?_, he.agree⟩, fun next kret hn => ?_⟩
  · rw [v 6 (by omega)]
    simp only [vs, o, A, List.getD_cons_succ, List.getD_cons_zero, word_eq_eOfNat]
  · simp only [fkStepBlock, ivs, cst, addS, b2s, List.cons_append, List.nil_append, holdsList_cons_atom,
      holdsList_nil, Atom.Holds]
    have v0 := v 0 (by omega)
    rw [Nat.add_zero] at v0
    have hprev' : σ' (if j = 0 then .n b else .n (c - 2)) = σ (fkPrev b j) := hpv
    rw [v0, v 1 (by omega), v 2 (by omega), v 3 (by omega), show c + 3 + 1 = c + 4 by omega, v 4 (by omega),
      v 5 (by omega), v 6 (by omega), v 7 (by omega), hk 0 (by omega), hk 1 (by omega), hprev']
    simp only [vs, List.getD_cons_succ, List.getD_cons_zero, word_zero]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, hcmp, hn⟩ <;> trivial

theorem canonical_fChain (pp ka : E) (i s : Nat) {x : E} (hx : IsCanonical128 x) :
    ∀ n, IsCanonical128 (fChain pp ka i s x n)
  | 0 => hx
  | _ + 1 => (isCanonical128_hb _).1

/-- **A forest chain is complete**: from the value `x`, its tip is the chain walked its deficit. -/
theorem fkChain_complete {σ : Val} {i d b : Nat} (hb : 2 ≤ b) (hpp : IsCanonical128 (σ (.n 1)))
    (hka : IsCanonical128 (σ (.n 0))) {x : E} (hx : IsCanonical128 x) :
    Completes C rd b (b + fkChainSize d) (fkChain i d b) σ (fun σ' =>
      σ' (.n (fkTip d b)) = fChain (σ (.n 1)) (σ (.n 0)) i (4 - d) x d ∧ AgreeBelow b σ σ') := by
  rw [fkChain_eq, hintW]
  apply Completes.hint_cons
  let σ1 := Function.update σ (.n b) x
  have he1 : Ext b (b + 1) σ σ1 := ext_update σ x le_rfl (by omega)
  have h01 : σ1 (.n 0) = σ (.n 0) ∧ σ1 (.n 1) = σ (.n 1) :=
    ⟨Function.update_of_ne (by simp; omega) _ _, Function.update_of_ne (by simp; omega) _ _⟩
  refine Completes.of_ext (he1.mono le_rfl (by simp [fkChainSize])) ?_
  have hfm := Completes.flatMap_range (C := C) (rd := rd) (f := fkStepBlock i d b) (base := fun j => b + 1 + 8 * j)
    (Inv := fun j σ' => σ' (.n 0) = σ (.n 0) ∧ σ' (.n 1) = σ (.n 1) ∧
      fkAfter σ' b j = fChain (σ (.n 1)) (σ (.n 0)) i (4 - d) x j ∧ AgreeBelow b σ σ')
    (fun j => by omega) d (fun j _ => by have := fkStepBlock_below i d b j hb; simpa [Nat.mul_add, Nat.add_assoc]
      using this)
    (fun j _ σ' ⟨h0, h1, hj, hag⟩ => by
      have hpc : IsCanonical128 (σ' (fkPrev b j)) := by
        rw [fkPrev_after σ' b j, hj]; exact canonical_fChain _ _ _ _ hx _
      refine (fkStep_complete (C := C) (rd := rd) (i := i) (d := d) hb (by rw [h1]; exact hpp)
        (by rw [h0]; exact hka) hpc).mono le_rfl (by omega) fun σ'' ⟨ho, hag'⟩ => ⟨?_, ?_, ?_, ?_⟩
      · rw [← hag' 0 (by omega), h0]
      · rw [← hag' 1 (by omega), h1]
      · rw [fkAfter, ite_neg' (by omega), show b + 1 + 8 * (j + 1 - 1) + 6 = b + 1 + 8 * j + 6 by omega, ho, h0, h1,
          fkPrev_after σ' b j, hj, fChain]
      · exact fun k hk => (hag k hk).trans (hag' k (by omega)))
    σ1 ⟨h01.1, h01.2, by simp [fkAfter, σ1, fChain], fun k hk => (he1.agree k hk)⟩
  refine hfm.mono (by omega) (by simp [fkChainSize]; omega) fun σ' ⟨_, _, hj, hag⟩ => ⟨?_, hag⟩
  rw [fkTip_after σ' d b, hj]

theorem fkChain_below (i d b : Nat) (hb : 2 ≤ b) :
    NumBelow (b + fkChainSize d) (Stmt.valsList (fkChain i d b)) := by
  rw [fkChain_eq, hintW, valsList_cons]
  refine (NumBelow.cons ⟨b, by simp [fkChainSize], rfl⟩ (NumBelow.nil _)).append
    (numBelow_valsList_flatMap _ _ fun j hj => ?_)
  rw [List.mem_range] at hj
  exact (fkStepBlock_below i d b j hb).mono (by simp only [fkChainSize]; omega)

theorem fkTip_lt (d b : Nat) : fkTip d b < b + fkChainSize d := by
  unfold fkTip fkChainSize; split <;> omega

theorem fkChains_snd (t : Nat) : ∀ m i b, b ≤ (fkChains t m i b).2.1
  | 0, _, _ => le_rfl
  | m + 1, i, b => by
      simp only [fkChains]
      have := fkChains_snd t m (i + 1) (b + fkChainSize (spCode t i))
      omega

theorem fkChains_below (t : Nat) : ∀ m i b, 2 ≤ b →
    NumBelow (fkChains t m i b).2.1 (Stmt.valsList (fkChains t m i b).1)
  | 0, _, _, _ => NumBelow.nil _
  | m + 1, i, b, hb => by
      simp only [fkChains, valsList_append]
      exact ((fkChain_below i _ b hb).mono (fkChains_snd t m (i + 1) _)).append
        (fkChains_below t m (i + 1) _ (by omega))

/-- **The chains of a forest key are complete**, from canonical values. -/
theorem fkChains_complete (t : Nat) {pp ka : E} (hpp : IsCanonical128 pp) (hka : IsCanonical128 ka)
    (vals : Nat → E) (hvals : ∀ k, IsCanonical128 (vals k)) :
    ∀ (m i b : Nat) (σ : Val), 2 ≤ b → σ (.n 1) = pp → σ (.n 0) = ka →
      Completes C rd b (fkChains t m i b).2.1 (fkChains t m i b).1 σ (fun σ' =>
        (∀ r < m, σ' (.n ((fkChains t m i b).2.2.getD r 0)) =
          fChain pp ka (i + r) (4 - spCode t (i + r)) (vals (i + r)) (spCode t (i + r))) ∧ AgreeBelow b σ σ')
  | 0, _, b, σ, _, _, _ => Completes.nil _ _ _ ⟨fun _ h => absurd h (by omega), fun _ _ => rfl⟩
  | m + 1, i, b, σ, hb, h1, h0 => by
      simp only [fkChains]
      refine Completes.append (m := b + fkChainSize (spCode t i)) (by omega)
        (fkChains_snd t m (i + 1) _) (fkChain_below i _ b hb)
        (fkChain_complete hb (by rw [h1]; exact hpp) (by rw [h0]; exact hka) (hvals i))
        fun σ1 _ ⟨htip, hag1⟩ => ?_
      refine (fkChains_complete t hpp hka vals hvals m (i + 1) _ σ1 (by omega)
        (by rw [← hag1 1 (by omega), h1]) (by rw [← hag1 0 (by omega), h0])).mono le_rfl le_rfl
        fun σ2 ⟨hr, hag2⟩ => ⟨fun r hr' => ?_, fun k hk => (hag1 k hk).trans (hag2 k (by omega))⟩
      rcases r with _ | r
      · simp only [List.getD_cons_zero, Nat.add_zero]
        rw [← hag2 _ (fkTip_lt _ _), htip, h1, h0]
      · simp only [List.getD_cons_succ]
        rw [hr r (by omega), show i + 1 + r = i + (r + 1) by omega]

/-! ## The key -/

/-- The statements after the chains. -/
def fkTail (t B : Nat) (tip : Nat → V) : List Stmt :=
  [cst B (word (tw 16) 0 0), addS (.n (B + 1)) (.n 0) (.n B), cst (B + 2) iv0, cst (B + 3) iv1,
    cst (B + 4) (mdw 64 false),
    b2s (.n 1) (.n (B + 1)) (tip 0) (tip 1) (.n (B + 2)) (.n (B + 3)) (.n (B + 5)) (.n (B + 6)) (.n (B + 4)),
    cst (B + 7) (mdw 128 true),
    b2s (tip 2) (tip 3) (tip 4) (tip 5) (.n (B + 5)) (.n (B + 6)) (.n (B + 8)) (.n (B + 9)) (.n (B + 7)),
    .atom (.copy (.n (B + 10)) (.n (B + 8))), cst (B + 11) (word t 0 0)]

theorem fkBody_split (t : Nat) : fkBody t = ((fkChains t 6 0 2).1 ++ fkTail t (fkChains t 6 0 2).2.1
    (fun i => .n ((fkChains t 6 0 2).2.2.getD i 0))) ++
      [.ret [.n ((fkChains t 6 0 2).2.1 + 10), .n ((fkChains t 6 0 2).2.1 + 11)]] := by
  simp only [fkBody, fkTail, ivs, List.append_assoc, List.cons_append, List.nil_append]

/-- **The statements after the chains are complete**: the child leaf of the tips, and `t`. -/
theorem fkTail_complete (t : Nat) {σ : Val} {B : Nat} {tip : Nat → V} (htip : ∀ i < 6, NB B (tip i))
    (hpp : IsCanonical128 (σ (.n 1))) (hka : IsCanonical128 (σ (.n 0))) (h2 : 2 ≤ B)
    (htc : ∀ i < 6, IsCanonical128 (σ (tip i))) :
    Completes C rd B (B + 12) (fkTail t B tip) σ (fun σ' =>
      σ' (.n (B + 10)) = (hcell (σ (.n 1) :: (σ (.n 0) + eOfNat (tw 16)) ::
        (List.range 6).map fun i => σ (tip i))).1 ∧ σ' (.n (B + 11)) = word t 0 0) := by
  set A := σ (.n 0) + word (tw 16) 0 0
  set b0 : Fin 4 → E := ![σ (.n 1), A, σ (tip 0), σ (tip 1)]
  set b1 : Fin 4 → E := ![σ (tip 2), σ (tip 3), σ (tip 4), σ (tip 5)]
  set x := hmid b0
  set o := hb (blockBytes b0 ++ blockBytes b1)
  set vs : List E := [word (tw 16) 0 0, A, iv0, iv1, mdw 64 false, x.1, x.2, mdw 128 true, o.1, o.2, o.1, word t 0 0]
  set σ' := upds σ ((List.range 12).map fun k => (B + k, vs.getD k 0))
  have he : Ext B (B + 12) σ σ' := upds_ext σ _ (by simp)
  have v : ∀ k < 12, σ' (.n (B + k)) = vs.getD k 0 := upds_range_at B _ 12 σ
  have hk : ∀ k < B, σ' (.n k) = σ (.n k) := fun k hk => (he.agree k hk).symm
  have htk : ∀ i < 6, σ' (tip i) = σ (tip i) := fun i hi => by
    obtain ⟨k, hk', e⟩ := htip i hi; rw [e]; exact hk k hk'
  have hr : (blockBytes b1).length = 64 := length_blockBytes _
  have hcmp := (compress_two_iff (b0 := b0) (b1 := b1) (x0 := x.1) (x1 := x.2) (o0 := o.1) (o1 := o.2)
    (r := blockBytes b1) (by rw [hr]; simp) (by rw [hr]) (by rw [hr]; omega)).mpr
    ⟨fin4_canonical.mpr ⟨hpp, isCanonical128_add hka (isCanonical128_word _ _), htc 0 (by omega), htc 1 (by omega)⟩,
      fin4_canonical.mpr ⟨htc 2 (by omega), htc 3 (by omega), htc 4 (by omega), htc 5 (by omega)⟩, rfl, rfl⟩
  rw [hr] at hcmp
  refine ⟨σ', he, ⟨?_, ?_⟩, fun next kret hn => ?_⟩
  · rw [v 10 (by omega)]
    simp only [vs, o, b0, b1, A, List.getD_cons_succ, List.getD_cons_zero, blockBytes_four, hcell,
      ← List.flatMap_append, word_eq_eOfNat]
    simp [List.range_succ]
  · rw [v 11 (by omega)]; rfl
  · simp only [fkTail, cst, addS, b2s, holdsList_cons_atom, holdsList_nil, Atom.Holds]
    have v0 := v 0 (by omega)
    rw [Nat.add_zero] at v0
    rw [v0, v 1 (by omega), v 2 (by omega), v 3 (by omega), v 4 (by omega), v 5 (by omega), v 6 (by omega),
      v 7 (by omega), v 8 (by omega), v 9 (by omega), v 10 (by omega), v 11 (by omega), hk 0 (by omega),
      hk 1 (by omega), htk 0 (by omega), htk 1 (by omega), htk 2 (by omega), htk 3 (by omega), htk 4 (by omega),
      htk 5 (by omega)]
    simp only [vs, List.getD_cons_succ, List.getD_cons_zero]
    obtain ⟨hc1, hc2⟩ := hcmp
    refine ⟨?_, ?_, ?_, ?_, ?_, hc1, ?_, hc2, ?_, ?_, hn⟩ <;> trivial

theorem fkChains_tip_lt (t : Nat) : ∀ m i b r, r < m →
    (fkChains t m i b).2.2.getD r 0 < (fkChains t m i b).2.1
  | 0, _, _, _, h => absurd h (by omega)
  | m + 1, i, b, 0, _ => by
      simp only [fkChains, List.getD_cons_zero]
      exact lt_of_lt_of_le (fkTip_lt _ _) (fkChains_snd t m (i + 1) _)
  | m + 1, i, b, r + 1, h => by
      simp only [fkChains, List.getD_cons_succ]
      exact fkChains_tip_lt t m (i + 1) _ r (by omega)

/-- **`sp_forest_key__L{t}`'s body holds** of canonical values at a canonical address. -/
theorem fkBody_holds (t : Nat) {pp ka : E} (hpp : IsCanonical128 pp) (hka : IsCanonical128 ka) (vals : Nat → E)
    (hvals : ∀ k, IsCanonical128 (vals k)) :
    ∃ σ : Val, σ (.n 0) = ka ∧ σ (.n 1) = pp ∧
      Stmt.HoldsList C rd σ (fkBody t) False (fun rs => rs = [fkLeaf t pp ka vals, word t 0 0]) := by
  set σ0 : Val := fun v => if v = .n 0 then ka else if v = .n 1 then pp else 0
  have h00 : σ0 (.n 0) = ka := by simp [σ0]
  have h01 : σ0 (.n 1) = pp := by simp [σ0]
  have hB := fkChains_snd t 6 0 2
  have htipB : ∀ i < 6, NB (fkChains t 6 0 2).2.1 (V.n ((fkChains t 6 0 2).2.2.getD i 0)) :=
    fun i hi => ⟨_, fkChains_tip_lt t 6 0 2 i hi, rfl⟩
  have hc : Completes C rd 2 ((fkChains t 6 0 2).2.1 + 12) ((fkChains t 6 0 2).1 ++ fkTail t (fkChains t 6 0 2).2.1
      (fun i => .n ((fkChains t 6 0 2).2.2.getD i 0))) σ0 (fun σ' =>
        σ' (.n ((fkChains t 6 0 2).2.1 + 10)) = fkLeaf t pp ka vals ∧
        σ' (.n ((fkChains t 6 0 2).2.1 + 11)) = word t 0 0) :=
    Completes.append (m := (fkChains t 6 0 2).2.1) (by omega) (by omega) (fkChains_below t 6 0 2 le_rfl) (fkChains_complete t hpp hka vals hvals 6 0 2 σ0 le_rfl h01 h00)
    (fun σ1 _ ⟨htips, hag⟩ => (fkTail_complete (C := C) (rd := rd) t htipB
      (by rw [← hag 1 (by omega), h01]; exact hpp) (by rw [← hag 0 (by omega), h00]; exact hka) (by omega)
      (fun i hi => by rw [htips i hi]; exact canonical_fChain _ _ _ _ (hvals _) _)).mono le_rfl le_rfl
      fun σ2 h => ⟨by
        rw [h.1, ← hag 0 (by omega), ← hag 1 (by omega), h00, h01, fkLeaf]
        congr 4
        refine List.map_congr_left fun k hk => ?_
        rw [List.mem_range] at hk
        rw [htips k hk, Nat.zero_add], h.2⟩)
  obtain ⟨σ', he, ⟨hlf, hw⟩, hh⟩ := hc
  refine ⟨σ', (he.apply (Or.inl (by omega))).trans h00, (he.apply (Or.inl (by omega))).trans h01, ?_⟩
  rw [fkBody_split, holdsList_append]
  refine hh _ _ ?_
  simp only [Stmt.HoldsList, Stmt.Holds, List.map_cons, List.map_nil, hlf, hw]

/-- **`sp_forest_key__L{t}` is complete**: at a canonical address and parameter, it returns the
child leaf of any canonical values, and `t`. -/
theorem sp_forest_key_complete {t : Nat} (ht : t < 256) {ka pp : E} (hka : IsCanonical128 ka)
    (hpp : IsCanonical128 pp) (vals : Nat → E) (hvals : ∀ k, IsCanonical128 (vals k)) :
    coreProgram.Rel rd (fkNames.getD t "") [ka, pp] [fkLeaf t pp ka vals, word t 0 0] := by
  obtain ⟨σ, h0, h1, hb⟩ := fkBody_holds (C := coreProgram.Rel rd) (rd := rd) t hpp hka vals hvals
  exact (rel_iff_sem (find_fk ht) _ _).mpr ⟨σ, by simp [fkFn, h0, h1], hb⟩

end
end LeanVM.Guest.B1.Sig
