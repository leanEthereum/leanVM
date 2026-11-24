/-
  LeanVM.Guest.B1.Sig.CodewordComplete

  A WOTS+C codeword's group completes from any valuation, dispatching on the digits hinted.
-/

module

public import LeanVM.Guest.B1.Sig.CwComplete
public import LeanVM.Guest.B1.Sig.Codeword

/-!
# A codeword's group, complete

* `Completes.withHolds`: a completed block holds of its valuation; `Completes.keep`: a predicate
  stable under extension carried along;
* `groupD_load`: a group completes from any valuation, its digits and starts loaded.
-/

namespace LeanVM.Guest.B1.Sig

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Protocol.Verifier (gen)

@[expose] public section

variable {C : CallRel} {rd : Reader}

theorem Completes.withHolds {lo hi : Nat} {ss : List Stmt} {σ : Val} {P : Val → Prop}
    (h : Completes C rd lo hi ss σ P) :
    Completes C rd lo hi ss σ (fun σ' => P σ' ∧ Stmt.HoldsList C rd σ' ss True (fun _ => True)) :=
  let ⟨σ', he, hp, hh⟩ := h
  ⟨σ', he, ⟨hp, hh True (fun _ => True) trivial⟩, hh⟩

theorem cwState_succ (W : WotsT) (b p : Nat) :
    (cwState W b (p + 1)).2.2 = (groupT W (3 * p) 3 (p == 0) (cwState W b p).1 (cwState W b p).2.1
      (cwState W b p).2.2).2 := rfl

theorem Completes.keep {lo hi : Nat} {ss : List Stmt} {σ : Val} {P : Val → Prop} {Q Q' : Val → Prop}
    (h : Completes C rd lo hi ss σ P) (hq : Q σ) (ht : ∀ σ', Ext lo hi σ σ' → Q σ → Q' σ') :
    Completes C rd lo hi ss σ (fun σ' => P σ' ∧ Q' σ') :=
  let ⟨σ', he, hp, hh⟩ := h
  ⟨σ', he, ⟨hp, ht σ' he hq⟩, hh⟩

theorem groupT_snd_eq (W : WotsT) (first n : Nat) (fold : Bool) (prodIn encIn : V) (b : Nat) :
    (groupT W first n fold prodIn encIn b).2 = armB W first n fold prodIn encIn b (4 ^ n) := by
  simp only [groupT, groupD, groupArmsT]; rw [armsT_snd]; rfl

/-- **A group completes from any valuation**, its digits `k` loaded at `d` and its arm's starts
`vals`, its statements `pre` a sequential block on `d + 5 ..< b + 5` after which `good` holds. -/
theorem groupD_load {W : WotsT} {B : Nat} {good : Val → Prop} (hW : StepShape W B)
    (hc : GoodStable B good) {first n : Nat} {fold : Bool} {prodIn encIn : V} {d : Nat}
    {pre : List Stmt} {b k : Nat}
    (hn : n ≤ 3) (hk : k < 4 ^ n) (hm : MemOK rd 64) (hdb : d ≤ b) (hB : B ≤ b + 5)
    (hpre : SeqOK (d + 5) pre (b + 5)) (hpi : NBv B prodIn)
    (hei : NBv B encIn) (hpw : NBv B (W.power (digitSum k n))) (vals : Nat → E) (σ : Val)
    (hg : ∀ σ', AgreeBelow d σ σ' → AtomsHold rd σ' pre → good σ') :
    Completes C rd d (groupD W first n fold prodIn encIn d pre b).2 (groupD W first n fold prodIn encIn d pre b).1 σ
      (fun σ' => σ' (.n d) = ofK (addressOfIndex k) ∧
        (∀ t < n, σ' (grpPos W first n fold prodIn encIn b k t) = vals t) ∧ good σ') := by
  obtain ⟨hl1, hl2, hl3⟩ := gLoadD_spec W first n fold prodIn encIn d b k vals σ hk hdb
  have hend : (groupD W first n fold prodIn encIn d pre b).2 = armB W first n fold prodIn encIn b (4 ^ n) := by
    simp only [groupD, groupArmsT]; rw [armsT_snd]; rfl
  rw [← hend] at hl1
  refine ((groupD_complete (C := C) (rd := rd) hW hc hn hk hm hdb hB hpre hpi hei hpw _
    (fun σ' he hh => hg σ' (fun j hj => (hl1.apply (Or.inl hj)).symm.trans (he.agree j (by omega))) hh)
    hl2).reload hl1).mono le_rfl le_rfl
    (fun σ' ⟨h1, h3, h4⟩ => ⟨h1, fun t ht => by rw [h3 t ht, hl3 t ht], h4⟩)

end
end LeanVM.Guest.B1.Sig
