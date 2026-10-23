/-
  LeanVM.Guest.B1.Sig.SphincsKey

  `sp_forest_key__L{t}` (G:2461-2483): one opened WOTS key of the leanSPHINCS forest at codeword
  `t`, its six chains walked up to the top and hashed into the child leaf, sound.
-/

module

public import LeanVM.Guest.B1.Sig.SphincsScheme
public import LeanVM.Guest.B1.Sig.SphincsData
public import LeanVM.Guest.B1.Sig.HashValues
public import LeanVM.Guest.B1.Basic

namespace LeanVM.Guest.B1.Sig

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.Blake2sHash
open LeanVM.Protocol.Verifier LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Value

@[expose] public section

variable {C : CallRel} {rd : Reader}

/-! ## The codeword table -/

theorem spCode_eq (t i : Nat) : spCode t i = Sphincs.codewordCodes.getD t 0 / 5 ^ (5 - i) % 5 := rfl

/-- The deficits are `lut`'s. -/
theorem spCode_lut {t : Nat} (ht : t < 256) (i : Sphincs.FChain) :
    spCode t i.val = (Sphincs.lut ⟨t, ht⟩ i).val := rfl

theorem spCode_le (t i : Nat) : spCode t i ≤ 4 := by
  rw [spCode_eq]; have := Nat.mod_lt (Sphincs.codewordCodes.getD t 0 / 5 ^ (5 - i)) (show 5 > 0 by norm_num); omega

/-! ## A chain -/

/-- The value after `j` steps of the chain walked from base `b`. -/
def fkAfter (σ : Val) (b j : Nat) : E := if j = 0 then σ (.n b) else σ (.n (b + 1 + 8 * (j - 1) + 6))

theorem fkTip_after (σ : Val) (d b : Nat) : σ (.n (fkTip d b)) = fkAfter σ b d := by
  unfold fkTip fkAfter fkChainSize
  split
  · rfl
  · congr 2; omega

/-- **A forest chain is sound**: its tip is the chain walked its deficit from the hinted value. -/
theorem fkChain_sound {σ : Val} {i d b : Nat} {next : Prop} {kret : List E → Prop}
    (h : Stmt.HoldsList C rd σ (fkChain i d b) next kret) :
    σ (.n (fkTip d b)) = fChain (σ (.n 1)) (σ (.n 0)) i (4 - d) (σ (.n b)) d ∧ next := by
  rw [fkChain, hintW, holds_hint_cons, holdsList_flatMap_range _ (fun _ => rfl)] at h
  obtain ⟨hb, hn⟩ := h
  refine ⟨?_, hn⟩
  rw [fkTip_after σ d b]
  suffices ∀ m ≤ d, fkAfter σ b m = fChain (σ (.n 1)) (σ (.n 0)) i (4 - d) (σ (.n b)) m from this d le_rfl
  intro m hm
  induction m with
  | zero => rfl
  | succ m ih =>
      have hj := hb m (by omega)
      simp only [cst, ivs, b2s, addS, List.cons_append, List.nil_append, holdsList_cons_atom, holdsList_nil,
        Atom.Holds] at hj
      obtain ⟨h0, h1, h2, h3, h4, h5, hc, -⟩ := hj
      rw [h1, h0, h2, h3, h4, h5, word_zero] at hc
      have hprev : σ (if m = 0 then V.n b else V.n (b + 1 + 8 * m - 2)) = fkAfter σ b m := by
        unfold fkAfter; split
        · rfl
        · congr 2; omega
      rw [hprev, ih (by omega)] at hc
      obtain ⟨-, ho⟩ := compress3_iff.mp hc
      have ho1 : σ (.n (b + 1 + 8 * m + 6)) = _ := congrArg Prod.fst ho
      rw [fkAfter, ite_neg' (by omega), show b + 1 + 8 * (m + 1 - 1) + 6 = b + 1 + 8 * m + 6 by omega,
        ho1, fChain, word_eq_eOfNat]

/-- **The chains of a forest key are sound.** -/
theorem fkChains_sound (t : Nat) {σ : Val} :
    ∀ (m i b : Nat) {next : Prop} {kret : List E → Prop},
      Stmt.HoldsList C rd σ (fkChains t m i b).1 next kret →
      (∃ vals : Nat → E, ∀ r < m, σ (.n ((fkChains t m i b).2.2.getD r 0)) =
        fChain (σ (.n 1)) (σ (.n 0)) (i + r) (4 - spCode t (i + r)) (vals (i + r)) (spCode t (i + r))) ∧ next
  | 0, _, _, _, _, h => ⟨⟨fun _ => 0, fun _ h => absurd h (by omega)⟩, h⟩
  | m + 1, i, b, next, kret, h => by
      simp only [fkChains, holdsList_append] at h ⊢
      obtain ⟨htip, h⟩ := fkChain_sound h
      obtain ⟨⟨vals, hv⟩, hn⟩ := fkChains_sound t m (i + 1) _ h
      refine ⟨⟨fun k => if k = i then σ (.n b) else vals k, fun r hr => ?_⟩, hn⟩
      rcases r with _ | r
      · simpa using htip
      · have := hv r (by omega)
        simp only [List.getD_cons_succ]
        rw [this, show i + 1 + r = i + (r + 1) by omega]
        simp

/-! ## The key -/

/-- The child leaf of forest key `t` at the address `ka` over the parameter `pp`, from the
chains' hinted values. -/
def fkLeaf (t : Nat) (pp ka : E) (vals : Nat → E) : E :=
  (hcell (pp :: (ka + eOfNat (tw 16)) :: (List.range 6).map fun k =>
    fChain pp ka k (4 - spCode t k) (vals k) (spCode t k))).1

/-- **`sp_forest_key__L{t}` is sound**: it returns the child leaf of its six chains and `t`. -/
theorem fkBody_sound (t : Nat) {σ : Val} {rets : List E}
    (h : Stmt.HoldsList C rd σ (fkBody t) False (fun rs => rs = rets)) :
    ∃ vals : Nat → E, rets = [fkLeaf t (σ (.n 1)) (σ (.n 0)) vals, word t 0 0] := by
  simp only [fkBody, holdsList_append] at h
  obtain ⟨⟨vals, hv⟩, h⟩ := fkChains_sound t 6 0 2 h
  simp only [cst, ivs, b2s, addS, holdsList_cons_atom, Atom.Holds, Stmt.HoldsList, Stmt.Holds, List.map_cons,
    List.map_nil] at h
  obtain ⟨h0, h1, h2, h3, h4, hc1, h7, hc2, h10, h11, hr⟩ := h
  refine ⟨vals, ?_⟩
  rw [← hr, h10, h11]
  rw [h1, h0, h2, h3, h4] at hc1
  rw [h7] at hc2
  have hr4 : (blockBytes ![σ (.n ((fkChains t 6 0 2).2.2.getD 2 0)), σ (.n ((fkChains t 6 0 2).2.2.getD 3 0)),
      σ (.n ((fkChains t 6 0 2).2.2.getD 4 0)), σ (.n ((fkChains t 6 0 2).2.2.getD 5 0))]).length = 64 :=
    length_blockBytes _
  have hc2' := hc2
  rw [show (128 : Nat) = 64 + (blockBytes ![σ (.n ((fkChains t 6 0 2).2.2.getD 2 0)),
      σ (.n ((fkChains t 6 0 2).2.2.getD 3 0)), σ (.n ((fkChains t 6 0 2).2.2.getD 4 0)),
      σ (.n ((fkChains t 6 0 2).2.2.getD 5 0))]).length by rw [hr4]] at hc2'
  obtain ⟨-, -, -, ho⟩ := (compress_two_iff (b1 := ![σ (.n ((fkChains t 6 0 2).2.2.getD 2 0)),
      σ (.n ((fkChains t 6 0 2).2.2.getD 3 0)), σ (.n ((fkChains t 6 0 2).2.2.getD 4 0)),
      σ (.n ((fkChains t 6 0 2).2.2.getD 5 0))]) (r := blockBytes _)
    (by rw [hr4]; simp) (by rw [hr4]) (by rw [hr4]; omega)).mp ⟨hc1, hc2'⟩
  congr 1
  have ho1 : σ (.n ((fkChains t 6 0 2).2.1 + 8)) = _ := congrArg Prod.fst ho
  rw [ho1, fkLeaf, blockBytes_four, blockBytes_four, hcell, ← List.flatMap_append,
    word_eq_eOfNat]
  congr 2
  simp only [List.range_succ, List.range_zero, List.nil_append, List.map_cons, List.map_nil, List.cons_append]
  rw [← hv 0 (by omega), ← hv 1 (by omega), ← hv 2 (by omega), ← hv 3 (by omega), ← hv 4 (by omega),
    ← hv 5 (by omega)]

/-! ## As a function of the program -/

theorem find_fk {t : Nat} (ht : t < 256) : coreProgram.find? (fkNames.getD t "") = some (fkFn t) := by
  obtain ⟨hd, hi⟩ := fk_data t ht
  refine Program.find?_of_indexOf? hi ?_
  obtain ⟨f, hf, he⟩ := Option.map_eq_some_iff.mp hd
  rw [hf]
  obtain ⟨n, p, b⟩ := f
  simp only [Prod.mk.injEq] at he
  obtain ⟨rfl, rfl, rfl⟩ := he
  rfl

/-- **`sp_forest_key__L{t}(at, pp)`**: the child leaf of codeword `t`'s chains at the address `at`,
from some values, and `t`. -/
def Meaning_sp_forest_key (t : Nat) (_rd : Reader) (args rets : List E) : Prop :=
  ∃ ka pp, args = [ka, pp] ∧ ∃ vals : Nat → E, rets = [fkLeaf t pp ka vals, word t 0 0]

theorem sp_forest_key_sound {t : Nat} (ht : t < 256) {args rets : List E}
    (h : coreProgram.Rel rd (fkNames.getD t "") args rets) : Meaning_sp_forest_key t rd args rets := by
  obtain ⟨σ, hp, hb⟩ := (rel_iff_sem (find_fk ht) args rets).mp h
  obtain ⟨vals, hv⟩ := fkBody_sound t hb
  exact ⟨σ (.n 0), σ (.n 1), hp.symm, vals, hv⟩

end
end LeanVM.Guest.B1.Sig
