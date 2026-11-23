/-
  LeanVM.Guest.B1.Sig.SpWotsRef

  `sp_wots`'s reference function, read from the guest's source, and its meaning.
-/

module

public import LeanVM.Guest.Ref.Keccak
public import LeanVM.Guest.Ref.Link
public import LeanVM.Guest.B1.Sig.SpWotsGroups
public import LeanVM.Guest.B1.Sig.CwComplete

/-!
# `sp_wots`, from its source

`spWotsRef` is `sp_wots(pp, a0, a1, encoding)` of `guests/lean_ethereum.py`, with `walk_group`
and `walk` (`lx = 0`) inline (`LeanVM.Guest.Ref.Lang`): `at = [a0, a1]` is the parameters' names;
`powers[s] = GEN ** s` an assertion on a name, `GEN ** s` evaluated; a hint a name; `keccak` and
`keccak_cells` the sponge (`LeanVM.Guest.Ref.Keccak`); each `match` a `match` whose arms assert the
next group's `digit_product` and `encoded`. What the compiler folds is folded in Lean:
`1 * powers[s]` and `0 + digits` in the first group, `x + const(0)` (`addLit`), a group's digit
constants into one (`spDigitsC`, their fields apart).

* `MeaningSpWots`: what it checks: 64 digits below `4` of sum `128` whose encoding is the fourth
  argument, each group's digit word range-checked in the memory, and the one-time leaf of some
  chain starts at those digits as its return;
* `spWotsRef_sat`: what its commands give on the names, the digits the arms its `match`es take
  (soundness goes through it, at the names the decoder reads);
* `spWotsRef_honest`, `spWotsRef_sem`: an honest run, each group's word and its arm's starts at
  their names; its relation is its meaning (completeness goes through them).

The reference function is not trusted: the link (`B1/Sig/SpWotsLinks*.lean`) ties the compiled
function to it, and `spWotsRef_sem` ties it to the meaning.
-/

namespace LeanVM.Guest.B1.Sig

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Ref
open LeanVM.Guest.Value LeanVM.Guest.Value.Keccak LeanVM.Protocol LeanVM.Protocol.KeccakHash
open LeanVM.Protocol.Verifier

@[expose] public section

/-! ## The reference function -/

/-- The names of `sp_wots`. -/
inductive SpName where
  | pp
  | a0
  | a1
  | encoding
  /-- `powers[s]`. -/
  | powers (s : ℕ)
  /-- Group `p`'s hinted digit word. -/
  | group (p : ℕ)
  /-- Group `p`'s range check: its complement (`j = 0`) and the two words it reads. -/
  | rc (p j : ℕ)
  /-- Chain `i`'s hinted start in arm `k` of its group. -/
  | start (i k : ℕ)
  /-- `walks[o]`. -/
  | walks (o : ℕ)
  /-- `digit_product` after the first `p` groups. -/
  | prod (p : ℕ)
  /-- `encoded` after the first `p` groups. -/
  | enc (p : ℕ)
  /-- Cell `c` of the leaf hash's state before block `b`. -/
  | st (b c : ℕ)
  /-- `leaf[0]`. -/
  | leaf
  deriving DecidableEq

instance : Coded SpName where
  code
    | .pp => 0
    | .a0 => 8
    | .a1 => 16
    | .encoding => 24
    | .leaf => 32
    | .powers s => 8 * s + 1
    | .group p => 8 * p + 2
    | .rc p j => 8 * (3 * p + j) + 3
    | .start i k => 8 * (64 * i + k) + 4
    | .walks o => 8 * o + 5
    | .prod p => 16 * p + 6
    | .enc p => 16 * p + 14
    | .st b c => 8 * (13 * b + c) + 7

/-- `a + const(n)`, as the compiler folds it: `a` itself at `n = 0`. -/
def addLit {X : Type} (a : Tm X) (n : ℕ) : Tm X := if n = 0 then a else .add a (.const (lit n))

/-- `walk(at, pp, walks, tags, powers, i, k, 0)` in arm `a` of its group: chain `i` from position
`k`, its start hinted (at `k = 3` the hint lands on the tip: no command). -/
def spWalk (i k a : ℕ) : List (Cmd SpName) :=
  unroll k 3 fun s => sponge (fun _ _ => .const 0)
    [.v .pp, .v .a0, addLit (.v .a1) (spStepC i s),
      if s = k then .v (.start i a) else .v (.walks (3 * i + s - 1))] 4 [.v (.walks (3 * i + s))]

/-- `walk_group(at, pp, walks, powers, 3p, n, k, 0, powers, digit_product, encoded)`, arm `k` of
group `p`: its walks, then the product and the encoding into the next group's names. -/
def spGroup (p n k : ℕ) : List (Cmd SpName) :=
  unroll 0 n (fun r => spWalk (3 * p + r) (k / 4 ^ r % 4) k) ++
    [.eq (.v (.prod (p + 1))) (if p = 0 then .v (.powers (digitSum k n))
        else .mul (.v (.prod p)) (.v (.powers (digitSum k n)))),
      .eq (.v (.enc (p + 1))) (if p = 0 then .const (lit (spDigitsC (3 * p) n k))
        else addLit (.v (.enc p)) (spDigitsC (3 * p) n k))]

/-- **`sp_wots(pp, a0, a1, encoding)`.** -/
def spWotsRef : Func SpName where
  params := [.pp, .a0, .a1, .encoding]
  body :=
    unroll 0 10 (fun s => [.eq (.v (.powers s)) (.const (word (2 ^ s) 0))]) ++
    unroll 0 22 (fun p =>
      [.range (.v (.group p)) (.v (.rc p 0)) (.v (.rc p 1)) (.v (.rc p 2))
          (.const (word (2 ^ (4 ^ spN p - 1)) 0)),
        .match_ (.v (.group p)) ((List.range (4 ^ spN p)).map (spGroup p (spN p)))]) ++
    [.eq (.v (.enc 22)) (.v .encoding), .eq (.v (.prod 22)) (.const spTarget)] ++
    sponge (fun b c => .v (.st b c))
      (.v .pp :: .v .a0 :: addLit (.v .a1) (2 ^ 24) ::
        (List.range 64).map fun i => .v (.walks (3 * i + 2)))
      67 [.v .leaf]
  rets := [.v .leaf]

/-! ## The meaning -/

/-- **What `sp_wots` relates**: 64 digits below `4`, of sum `128`, whose encoding (`spX`, each
where the digest holds it) is the fourth argument; each group's `n` digits a base-4 word `w`,
range-checked in the memory (`RangeChecked`: `g^w` and its complement to `g^(4^n - 1)` point to
words); and the one-time leaf of some chain starts at those digits (`spLeafCell`) as the one
return word. -/
def MeaningSpWots (rd : Reader) (args rets : List E) : Prop :=
  ∃ (pp a0 a1 : E) (d : ℕ → ℕ) (starts : ℕ → E),
    args = [pp, a0, a1, eOfNat128 (spX d 64)] ∧ rets = [spLeafCell pp a0 a1 d starts] ∧
    (∀ i < 64, d i < 4) ∧ ∑ i ∈ Finset.range 64, d i = 128 ∧
    ∀ p < 22, ∃ w < 4 ^ spN p, (∀ r < spN p, d (3 * p + r) = w / 4 ^ r % 4) ∧
      RangeChecked rd (ofK (addressOfIndex w)) (ofK (addressOfIndex (4 ^ spN p - 1)))

/-! ## Proofs -/

/-- The arm group `p`'s `match` takes, on the names. -/
noncomputable def spArm (ρ : SpName → E) (p : ℕ) : ℕ := logG (ρ (.group p)) (4 ^ spN p)

/-- Chain `i`'s digit, on the names. -/
noncomputable def spDig (ρ : SpName → E) (i : ℕ) : ℕ := spArm ρ (i / 3) / 4 ^ (i % 3) % 4

/-- Where chain `i` starts in arm `k` of its group: its hint, or its tip at digit `3`. -/
def spStartN (i k : ℕ) : SpName :=
  if k / 4 ^ (i % 3) % 4 = 3 then .walks (3 * i + 2) else .start i k

variable {rd : Reader} {ρ : SpName → E}

private theorem eval_addLit {X : Type} (σ : X → E) (a : Tm X) (n : ℕ) :
    (addLit a n).eval σ = a.eval σ + lit n := by
  unfold addLit; split <;> simp [Tm.eval, *, lit_zero]

private theorem satList_spWalk {i k a : ℕ} :
    Cmd.SatList rd ρ (spWalk i k a) ↔ ∀ s, k ≤ s → s < 3 → ρ (.walks (3 * i + s)) =
      spStepCell (ρ .pp) (ρ .a0) (ρ .a1) i s
        (ρ (if s = k then .start i a else .walks (3 * i + s - 1))) := by
  simp only [spWalk, Cmd.satList_unroll]
  refine forall₂_congr fun s _ => forall_congr' fun _ => ?_
  rw [satList_sponge (m := 4) _ _ rfl _ (.inl rfl)]
  simp only [Tm.eval, List.map_cons, List.map_nil, eval_addLit, apply_ite (Tm.eval ρ), apply_ite ρ,
    spStepCell, hcell, cellsBytes, List.length_singleton, List.take, List.cons.injEq, and_true]
  exact ⟨fun h => h.2, fun h => ⟨fun b h0 h1 => absurd h1 (by simp [blocks, rate]; omega), h⟩⟩

/-- **A walk reaches its tip** from its start. -/
private theorem spWalk_tip {i k a : ℕ} (hk : k ≤ 3) (h : Cmd.SatList rd ρ (spWalk i k a)) :
    ρ (.walks (3 * i + 2)) = chainT (spStepCell (ρ .pp) (ρ .a0) (ρ .a1)) i (3 - k) k
      (ρ (if k = 3 then .walks (3 * i + 2) else .start i a)) := by
  rw [satList_spWalk] at h
  by_cases h3 : k = 3
  · simp [h3, chainT]
  have key : ∀ m, k + m < 3 → ρ (.walks (3 * i + (k + m))) =
      chainT (spStepCell (ρ .pp) (ρ .a0) (ρ .a1)) i (m + 1) k (ρ (.start i a)) := by
    intro m
    induction m with
    | zero => intro hm; rw [Nat.add_zero, h k le_rfl (by omega), ite_eq_left rfl]; rfl
    | succ m ih =>
      intro hm
      rw [h (k + (m + 1)) (by omega) hm, ite_eq_right (by omega), chainT_succ,
        show 3 * i + (k + (m + 1)) - 1 = 3 * i + (k + m) by omega, ih (by omega)]
  have := key (2 - k) (by omega)
  rw [show k + (2 - k) = 2 by omega, show 2 - k + 1 = 3 - k by omega] at this
  rw [this, ite_eq_right h3]

private theorem satList_spGroup {p n k : ℕ} :
    Cmd.SatList rd ρ (spGroup p n k) ↔
      (∀ r < n, Cmd.SatList rd ρ (spWalk (3 * p + r) (k / 4 ^ r % 4) k)) ∧
      ρ (.prod (p + 1)) = (if p = 0 then 1 else ρ (.prod p)) * ρ (.powers (digitSum k n)) ∧
      ρ (.enc (p + 1)) = (if p = 0 then 0 else ρ (.enc p)) + lit (spDigitsC (3 * p) n k) := by
  simp only [spGroup, Cmd.satList_append, Cmd.satList_unroll, Cmd.satList_cons, Cmd.satList_nil,
    and_true, Cmd.Sat, zero_le, true_implies]
  split_ifs <;> simp [Tm.eval, eval_addLit]

/-- **What `sp_wots`'s commands give**, on the names: the arm `spArm ρ p` each group's `match`
takes, its digit word's range check, the digits' sum and encoding, and the leaf of the chains
from their starts. -/
theorem spWotsRef_sat (h : Cmd.SatList rd ρ spWotsRef.body) :
    (∀ p < 22, spArm ρ p < 4 ^ spN p ∧ ρ (.group p) = ofK (addressOfIndex (spArm ρ p)) ∧
      LoadHolds rd (ρ (.group p)) 0 (ρ (.rc p 1)) ∧
      word (2 ^ (4 ^ spN p - 1)) 0 = ρ (.group p) * ρ (.rc p 0) ∧
      LoadHolds rd (ρ (.rc p 0)) 0 (ρ (.rc p 2))) ∧
    ∑ i ∈ Finset.range 64, spDig ρ i = 128 ∧ ρ .encoding = eOfNat128 (spX (spDig ρ) 64) ∧
    ρ .leaf = spLeafCell (ρ .pp) (ρ .a0) (ρ .a1) (spDig ρ)
      (fun i => ρ (spStartN i (spArm ρ (i / 3)))) := by
  simp only [spWotsRef, Cmd.satList_append] at h
  obtain ⟨⟨⟨hpow, hgrp⟩, hchk⟩, hleaf⟩ := h
  simp only [Cmd.satList_unroll, Cmd.satList_cons, Cmd.satList_nil, and_true, Cmd.Sat, Tm.eval,
    zero_le, true_implies] at hpow hgrp hchk
  obtain ⟨henc, hprod⟩ := hchk
  have harm : ∀ p < 22, spArm ρ p < 4 ^ spN p ∧ ρ (.group p) = ofK (addressOfIndex (spArm ρ p)) ∧
      Cmd.SatList rd ρ (spGroup p (spN p) (spArm ρ p)) := by
    intro p hp
    obtain ⟨i, hi, hx, ha⟩ := (Cmd.satArms_iff 0 _).mp (hgrp p hp).2
    simp only [List.length_map, List.length_range, Nat.zero_add, List.getElem_map,
      List.getElem_range] at hi hx ha
    obtain rfl : spArm ρ p = i := logG_eq hi (by unfold spN; split <;> norm_num) hx
    exact ⟨hi, hx, ha⟩
  have hg := fun p (hp : p < 22) => satList_spGroup.mp (harm p hp).2.2
  have hpw : ∀ s < 10, ρ (.powers s) = gen ^ s := fun s hs => by
    rw [hpow s hs, word_eq_eOfNat, Value.gen_pow_eq_eOfNat (by omega)]
  have hprod22 := spCodeword_prod (G := 21) (by norm_num) le_rfl (spArm ρ)
    (fun p hp => (harm p (by omega)).1) (fun s => ρ (.powers s)) hpw (fun p => ρ (.prod (p + 1)))
    (by simpa [spN, cwN] using (hg 0 (by norm_num)).2.1)
    (fun p hp => by simpa [spN, cwN, hp] using (hg (p + 1) (by omega)).2.1)
  have henc22 := spCodeword_enc (spArm ρ) (fun p => ρ (.enc (p + 1)))
    (by simpa [spN] using (hg 0 (by norm_num)).2.2)
    (fun p hp => by simpa using (hg (p + 1) (by omega)).2.2)
  have htip : ∀ i < 64, ρ (.walks (3 * i + 2)) = chainT (spStepCell (ρ .pp) (ρ .a0) (ρ .a1)) i
      (3 - spDig ρ i) (spDig ρ i) (ρ (spStartN i (spArm ρ (i / 3)))) := by
    intro i hi
    have hr : i % 3 < spN (i / 3) := by unfold spN; split <;> omega
    have h4 := Nat.mod_lt (spArm ρ (i / 3) / 4 ^ (i % 3)) (show 0 < 4 by omega)
    have := spWalk_tip (by omega) ((hg (i / 3) (by omega)).1 (i % 3) hr)
    rwa [Nat.div_add_mod] at this
  refine ⟨fun p hp => ⟨(harm p hp).1, (harm p hp).2.1, (hgrp p hp).1⟩, ?_, ?_, ?_⟩
  · exact Value.gen_pow_inj (lt_of_le_of_lt (Finset.sum_le_sum (g := fun _ => 3) fun i _ =>
      Nat.le_of_lt_succ (Nat.mod_lt _ (by norm_num))) (by norm_num)) (by norm_num)
      (hprod22.symm.trans (hprod.trans spTarget_eq))
  · exact henc.symm.trans henc22
  · refine (List.head_eq_of_cons_eq
      ((satList_sponge (m := 67) _ _ (by simp) _ (.inl rfl)).mp hleaf).2).trans ?_
    rw [spLeafCell, hcell, cellsBytes]
    simp only [List.map_cons, List.map_map, Tm.eval, eval_addLit, Function.comp_def,
      show lit (2 ^ 24) = spPkC from rfl]
    rw [List.map_congr_left fun i hi => htip i (List.mem_range.mp hi)]

/-- The running product of `sp_wots`'s groups from their digit words `w`. -/
private def spProdOf (w : ℕ → ℕ) : ℕ → E
  | 0 => word (2 ^ digitSum (w 0) 3) 0
  | p + 1 => spProdOf w p * word (2 ^ digitSum (w (p + 1)) (spN (p + 1))) 0

/-- The running encoding of `sp_wots`'s groups from their digit words `w`. -/
private def spEncOf (w : ℕ → ℕ) : ℕ → E
  | 0 => lit (spDigitsC 0 3 (w 0))
  | p + 1 => spEncOf w p + lit (spDigitsC (3 * (p + 1)) (spN (p + 1)) (w (p + 1)))

/-- The names' words of an honest run: the group words `w`, the range checks' words `y`, `t1`,
`t2`, the chains walked from `starts`, the running product and encoding, the leaf's sponge. -/
private def spVal (pp a0 a1 : E) (d w : ℕ → ℕ) (starts : ℕ → E) (y t1 t2 : ℕ → E) : SpName → E
  | .pp => pp
  | .a0 => a0
  | .a1 => a1
  | .encoding => eOfNat128 (spX d 64)
  | .powers s => word (2 ^ s) 0
  | .group p => ofK (addressOfIndex (w p))
  | .rc p 0 => y p
  | .rc p 1 => t1 p
  | .rc p _ => t2 p
  | .start i _ => starts i
  | .walks o =>
      chainT (spStepCell pp a0 a1) (o / 3) (o % 3 + 1 - d (o / 3)) (d (o / 3)) (starts (o / 3))
  | .prod p => spProdOf w (p - 1)
  | .enc p => spEncOf w (p - 1)
  | .st b c => if h : c < 13 then spongeSt (padCells (pp :: a0 :: (a1 + lit (2 ^ 24)) ::
      (List.range 64).map fun i => chainT (spStepCell pp a0 a1) i (3 - d i) (d i) (starts i))
      (16 * 67)) (blocks 67) b ⟨c, h⟩ else 0
  | .leaf => spLeafCell pp a0 a1 d starts

/-- **An honest run of `sp_wots`'s reference function**: for digits of sum `128` whose groups'
words `w p` hold them and are range-checked, and any chain starts, some valuation of the names
satisfies the commands with the arguments `pp`, `a0`, `a1` and the digits' encoding, returning the
one-time leaf, each group's word `w p` at its name and each chain's start at the name the arm its
group takes hints it into. -/
theorem spWotsRef_honest {pp a0 a1 : E} {d w : ℕ → ℕ} (starts : ℕ → E)
    (hsum : ∑ i ∈ Finset.range 64, d i = 128)
    (hw : ∀ p < 22, w p < 4 ^ spN p ∧ (∀ r < spN p, d (3 * p + r) = w p / 4 ^ r % 4) ∧
      RangeChecked rd (ofK (addressOfIndex (w p))) (ofK (addressOfIndex (4 ^ spN p - 1)))) :
    ∃ ρ : SpName → E, spWotsRef.params.map ρ = [pp, a0, a1, eOfNat128 (spX d 64)] ∧
      Cmd.SatList rd ρ spWotsRef.body ∧
      spWotsRef.rets.map (Tm.eval ρ) = [spLeafCell pp a0 a1 d starts] ∧
      (∀ p < 22, ρ (.group p) = ofK (addressOfIndex (w p))) ∧
      ∀ i < 64, ρ (spStartN i (w (i / 3))) = starts i := by
  unfold RangeChecked at hw
  choose! hwlt hwd y t1 t2 hl1 hk hl2 using hw
  have hdig : ∀ i < 64, w (i / 3) / 4 ^ (i % 3) % 4 = d i := fun i hi => by
    rw [← hwd (i / 3) (by omega) (i % 3) (by unfold spN; split <;> omega), Nat.div_add_mod]
  set ρ := spVal pp a0 a1 d w starts y t1 t2
  have hmsg : (Tm.v SpName.pp :: Tm.v .a0 :: addLit (.v .a1) (2 ^ 24) ::
      (List.range 64).map fun i => Tm.v (SpName.walks (3 * i + 2))).map (Tm.eval ρ) =
      pp :: a0 :: (a1 + lit (2 ^ 24)) :: (List.range 64).map fun i =>
        chainT (spStepCell pp a0 a1) i (3 - d i) (d i) (starts i) := by
    simp only [List.map_cons, List.map_map, Tm.eval, eval_addLit, Function.comp_def]
    refine congrArg (pp :: a0 :: (a1 + lit (2 ^ 24)) :: ·) (List.map_congr_left fun i _ => ?_)
    simp only [ρ, spVal, show (3 * i + 2) / 3 = i by omega, show (3 * i + 2) % 3 = 2 by omega]
  have hpw : ∀ s < 10, word (2 ^ s) 0 = gen ^ s := fun s hs => by
    rw [word_eq_eOfNat, Value.gen_pow_eq_eOfNat (by omega)]
  refine ⟨ρ, rfl, ?_, by simp [spWotsRef, Tm.eval, ρ, spVal], fun p _ => rfl, fun i hi => ?_⟩
  swap
  · simp only [spStartN, hdig i hi, apply_ite ρ, ρ, spVal, show (3 * i + 2) / 3 = i by omega,
      show (3 * i + 2) % 3 = 2 by omega]
    split_ifs with h3 <;> simp [h3, chainT]
  simp only [spWotsRef, Cmd.satList_append, Cmd.satList_unroll, Cmd.satList_cons,
    Cmd.satList_nil, and_true, Cmd.Sat, Tm.eval, zero_le, true_implies]
  refine ⟨⟨⟨fun s _ => rfl, fun p hp => ⟨⟨hl1 p hp, ?rc, hl2 p hp⟩, ?arm⟩⟩, ?enc, ?prod⟩, ?leaf⟩
  case rc => exact (word_two_pow_eq (by unfold spN; split <;> norm_num)).trans (hk p hp)
  case arm =>
    refine (Cmd.satArms_iff 0 _).mpr ⟨w p, by simpa using hwlt p hp, by simp [ρ, spVal], ?_⟩
    rw [List.getElem_map, List.getElem_range, satList_spGroup]
    refine ⟨fun r hr => satList_spWalk.mpr fun s hs1 hs2 => ?_, ?_, ?_⟩
    · have hi : d (3 * p + r) = w p / 4 ^ r % 4 := hwd p hp r hr
      simp only [ρ, spVal, show (3 * (3 * p + r) + s) / 3 = 3 * p + r by omega,
        show (3 * (3 * p + r) + s) % 3 = s by omega, ← hi]
      split_ifs with e
      · subst e
        rw [show d (3 * p + r) + 1 - d (3 * p + r) = 0 + 1 by omega]
        rfl
      · simp only [show (3 * (3 * p + r) + s - 1) / 3 = 3 * p + r by omega,
          show (3 * (3 * p + r) + s - 1) % 3 = s - 1 by omega]
        rw [show s + 1 - d (3 * p + r) = (s - d (3 * p + r)) + 1 by omega, chainT_succ,
          show s - 1 + 1 - d (3 * p + r) = s - d (3 * p + r) by omega,
          show d (3 * p + r) + (s - d (3 * p + r)) = s by omega]
    · rcases p with _ | p <;> simp [ρ, spVal, spProdOf, spN]
    · rcases p with _ | p <;> simp [ρ, spVal, spEncOf, spN]
  case enc =>
    exact (spCodeword_enc w (spEncOf w) rfl fun p _ => rfl).trans (congrArg _ (spX_congr hdig))
  case prod =>
    rw [show ρ (.prod 22) = spProdOf w 21 from rfl, spCodeword_prod (G := 21) (by norm_num) le_rfl
      w (fun p hp => hwlt p (by omega)) (fun s => word (2 ^ s) 0) hpw (spProdOf w) rfl
      (fun p _ => rfl), spTarget_eq]
    exact congrArg (gen ^ ·)
      ((Finset.sum_congr rfl fun i hi => hdig i (Finset.mem_range.mp hi)).trans hsum)
  case leaf =>
    rw [satList_sponge (m := 67) _ _ (by simp) _ (.inl rfl), hmsg]
    refine ⟨fun b _ _ c => by
      simp only [Tm.eval, ρ, spVal, c.isLt, dite_true, List.length_cons, List.length_map,
        List.length_range], congrArg ([·]) ?_⟩
    show spLeafCell pp a0 a1 d starts = _
    rw [spLeafCell, hcell, cellsBytes, show lit (2 ^ 24) = spPkC from rfl]

/-- **`sp_wots`'s reference function is its meaning.** -/
theorem spWotsRef_sem (args rets : List E) :
    spWotsRef.Sem rd args rets ↔ MeaningSpWots rd args rets := by
  constructor
  · rintro ⟨ρ, rfl, h, rfl⟩
    obtain ⟨hg, hsum, henc, hleaf⟩ := spWotsRef_sat h
    refine ⟨ρ .pp, ρ .a0, ρ .a1, spDig ρ, fun i => ρ (spStartN i (spArm ρ (i / 3))),
      by simp [spWotsRef, henc], by simp [spWotsRef, Tm.eval, hleaf],
      fun i _ => Nat.mod_lt _ (by norm_num), hsum,
      fun p hp => ⟨spArm ρ p, (hg p hp).1, fun r hr => by
        have : r < 3 := by unfold spN at hr; split at hr <;> omega
        simp only [spDig, show (3 * p + r) / 3 = p by omega, show (3 * p + r) % 3 = r by omega],
        ?_⟩⟩
    obtain ⟨-, hx, h1, hk, h2⟩ := hg p hp
    unfold RangeChecked
    rw [← hx, ← word_two_pow_eq (by unfold spN; split <;> norm_num), hk]
    exact ⟨_, _, _, h1, rfl, h2⟩
  · rintro ⟨pp, a0, a1, d, starts, rfl, rfl, -, hsum, hw⟩
    choose! w hw using hw
    obtain ⟨ρ, hp, hs, hr, -⟩ := spWotsRef_honest starts hsum hw
    exact ⟨ρ, hp, hs, hr⟩

end
end LeanVM.Guest.B1.Sig
