/-
  LeanVM.Guest.B1.VsC.Os.LeftLevels

  `open_stacked`'s levels' callees placed one level after the other, and the named callees'
  meanings at the node's valuation.
-/

module

public import LeanVM.Guest.B1.VsC.Os.LeftLevel

/-!
# The levels' callees

`allOk_calls`: on a flat body with no conditional call and short dispatches, holding at a callee
relation `C`, every call of its path at a valuation whose rate selector is `g^ri` is in `C`.
`osCmin_calls`: `open_stacked`'s calls at the node's valuation satisfy `osCmin` (`OsBodyAt`).

`forall₂_append_split`, `osLvQs_length`; **`HonRun.kidsAtF_lvls`**: the first `n` levels' calls
(matching `(range n).flatMap (osLvSpec c)`) complete in order from the chain's cursor `cs 0` to
`cs n`, level by level (`kidsAtF_lvl`, `kidsAtF_append`).
-/

namespace LeanVM.Guest.B1.VsC

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Memory LeanVM.Guest.B1
open LeanVM.Guest.Complete LeanVM.Guest.Value LeanVM.Guest.B1.Whir LeanVM.Protocol LeanVM.Protocol.Verifier
open LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile

@[expose] public section

/-- **The calls of a flat body holding at `C` are in `C`**, each dispatch at arm `ri`. -/
theorem allOk_calls {C : CallRel} {rd : Reader} {σ : Val} {ri : ℕ} (hri : logG (σ (.n osRate)) = ri) :
    ∀ ss : List Stmt, ss.all Stmt.callOkD = true → ss.all Stmt.armsShort = true → AllOk C rd σ ss →
      ∀ c ∈ calls (ss.flatMap (fdEvs σ)), C c.f (c.args.map σ) (c.rets.map σ) := by
  intro ss hok hsh hall c hc
  rw [calls_flatD_eq hri ss hok, List.mem_filterMap] at hc
  obtain ⟨s, hs, hcs⟩ := hc
  have hst := hall s hs
  have hsok := List.all_eq_true.mp hok s hs
  have hshort := List.all_eq_true.mp hsh s hs
  cases s
  case call f a r =>
    simp only [Stmt.callD, Option.some.injEq] at hcs
    subst hcs
    exact hst
  case dispatch x fs a r =>
    simp only [Stmt.callD, Option.some.injEq] at hcs
    subst hcs
    change (Stmt.flatD (.dispatch x fs a r) && (some x).all (· == .n osRate)) = true at hsok
    simp only [Stmt.flatD, Option.all_some, Bool.true_and, beq_iff_eq] at hsok
    subst hsok
    obtain ⟨j, hj, hx, hC⟩ := hst
    have hlen : fs.length ≤ 2 ^ 64 - 1 := by simpa [Stmt.armsShort] using hshort
    have hjr : j = ri := by rw [← hri, hx, logG_spec (by omega)]
    change C (fs.getD ri "") (a.map σ) (r.map σ)
    rw [← hjr, List.getD_eq_getElem _ _ hj]
    exact hC
  all_goals simp [Stmt.callD] at hcs

/-- **`open_stacked`'s calls at the node's valuation satisfy the named callees' meanings.** -/
theorem osCmin_calls {m ri : ℕ} (hm : m < 15) {b : ℕ} {args : List E} {cur tabs : E} {xs : List E}
    {tgt inn res : E} {own : List (List E)} {D : ℕ → OsLvData} {rd : Reader} {σ : Val}
    (h : OsBodyAt (osCfgR m ri) b args cur tabs xs tgt inn res own D rd σ) (hri : logG (σ (.n osRate)) = ri) :
    ∀ c ∈ calls ((osBodyA (osCfgR m ri)).flatMap (fdEvs σ)),
      osCmin (osCfgR m ri) b own cur tabs xs rd c.f (c.args.map σ) (c.rets.map σ) := by
  have hc := osCallsOk_all m hm
  simp only [OsCallsOk, Bool.and_eq_true] at hc
  have hf := flatBody_all m hm
  rw [osBodyA_rate m ri] at hf hc
  have hsh : (osBodyA (osCfgR m ri)).all Stmt.armsShort = true := by
    simp only [FlatBody, List.all_eq_true, Bool.and_eq_true] at hf
    exact List.all_eq_true.mpr fun s hs ↦ (hf s hs).2
  exact allOk_calls hri _ hc.1 hsh h.2.1

theorem forall₂_append_split {α β : Type _} {R : α → β → Prop} :
    ∀ {cs : List α} (A B : List β), List.Forall₂ R cs (A ++ B) →
      ∃ c1 c2, cs = c1 ++ c2 ∧ List.Forall₂ R c1 A ∧ List.Forall₂ R c2 B
  | cs, [], _, h => ⟨[], cs, rfl, .nil, h⟩
  | _, _ :: A, B, .cons h1 h2 =>
    let ⟨c1, c2, e, f1, f2⟩ := forall₂_append_split A B h2
    ⟨_ :: c1, c2, by rw [e]; rfl, .cons h1 f1, f2⟩

theorem osLvQs_length (c : OsCfg) (os : List (List Opening)) (l : ℕ) :
    (osLvQs c os l).length = (osLvSpec c l).length := by
  unfold osLvQs osLvSpec
  split_ifs <;> rfl

theorem osLvsQs_length (c : OsCfg) (os : List (List Opening)) (n : ℕ) :
    ((List.range n).flatMap (osLvQs c os)).length = ((List.range n).flatMap (osLvSpec c)).length := by
  simp only [List.length_flatMap, osLvQs_length]

end
end LeanVM.Guest.B1.VsC

namespace LeanVM.Guest.B1.Whir.HonRun

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest LeanVM.Guest.B1 LeanVM.Guest.B1.VsC
open LeanVM.Guest.Memory LeanVM.Guest.Complete LeanVM.Guest.Value
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

variable {μ r : ℕ} {target : E} {S : KeccakState} {root : Digest} {xs : List E}
  {os : List (List Opening)} {w : WhirEnd} {cfg : List Whir.Level} {Ls : List LvAt}
  (hR : HonRun μ r target S root xs os w cfg Ls)
include hR

set_option hygiene false in
local notation "CC" => osCfgR (μ - minOpenLog) (r - 1)

set_option hygiene false in
local notation "HH" => hR.osHonest (cur := cur) (tabs := tabs)

/-- **The first `n` levels' callees complete in order**, from the chain's cursor `cs 0` to `cs n`. -/
theorem kidsAtF_lvls {cur tabs : E} (al : String → Bool) (k : ℕ) (σ0 : Val) (rd0 : Reader) (b it : ℕ)
    (htabs : tabs = ptrAt it) (R Rn Sc : ℕ → Prop) (Pre : Reader → Prop)
    (hRR : ∀ i, R i → Rn i) (hRb : ∀ i, osBufCells CC b i → Rn i) (hRS : ∀ i, Sc i → Rn i)
    (hPre : ∀ rd, Pre rd → ReadsAt rd cur xs ∧ WinTabs rd tabs)
    (cs : ℕ → ℕ) (hch : ∀ l, LvStep hR cur tabs al k b it R l (cs l) (cs (l + 1)))
    (O : Reader → Prop) (Dacc : ℕ → Prop)
    (hO : ∀ rd, O rd → HoldsWords rd (osWords CC b (HH).own (osWq al CC fun l => osLpC al CC l (cs l))))
    (hv : OsHelperVals CC b tabs (HH).own (HH).D σ0)
    (h0 : OsNF CC b (HH).own cur tabs xs rd0) (hS0 : OsNF CC b (HH).own cur tabs xs (restrict rd0 Sc)) :
    ∀ n, n ≤ (CC).levels.length → ∀ {cl : List Call},
      List.Forall₂ (fun c s => callMatches c s = true) cl ((List.range n).flatMap (osLvSpec CC)) →
      (∀ c ∈ cl, osCmin CC b (HH).own cur tabs xs rd0 c.f (c.args.map σ0) (c.rets.map σ0)) →
      KidsAtF B2C.fs al B2C.cert k σ0 Rn Pre O Dacc ((List.range n).flatMap (osLvQs CC os)) cl (cs 0) (cs n)
        O Dacc := by
  intro n
  induction n with
  | zero =>
    intro _ cl hc _
    simp only [List.range_zero, List.flatMap_nil] at hc ⊢
    cases hc
    exact kidsAtF_nilStep (fun _ h => h) (fun _ h => h)
  | succ n ih =>
    intro hn cl hc hcall
    rw [List.range_succ, List.flatMap_append, List.flatMap_singleton] at hc ⊢
    obtain ⟨c1, c2, rfl, f1, f2⟩ := forall₂_append_split _ _ hc
    have h1 := ih (by omega) f1 fun c hc' => hcall c (List.mem_append_left _ hc')
    have h2 := hR.kidsAtF_lvl (cur := cur) (tabs := tabs) al k (l := n) (by omega) σ0 rd0 b it htabs R Rn Sc Pre
      hRR hRb hRS hPre _ O Dacc hO hv h0 hS0 f2 (fun c hc' => hcall c (List.mem_append_right _ hc')) rfl (hch n)
    exact kidsAtF_append _ _ _ _ _ _ _ _ _ _ _ _ _
      (by rw [osLvsQs_length]; exact f1.length_eq.symm) h1 h2

end
end LeanVM.Guest.B1.Whir.HonRun
