/-
  LeanVM.Guest.B1.Sig.CodewordComplete

  The WOTS+C codeword completes: its groups dispatch on the digits hinted, the encoding is the
  digest's first cell and the product the target.
-/

module

public import LeanVM.Guest.B1.Sig.CwComplete
public import LeanVM.Guest.B1.Sig.Codeword

/-!
# The codeword, complete

* `StepShape.mono`, `StepCanon.mono`: a step's shape above a larger bound;
* `Completes.withHolds`: a completed block holds of its valuation;
* `groupT_load`: a group completes from any valuation, its digits and starts loaded;
* `cwPos`: the start of a codeword's chain, in the arm of its group's digits;
* `groupT_end`, `groupsT_complete`, `codewordT_complete`: the groups complete in sequence, then the
  codeword, its starts kept.
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

theorem groupT_end (W : WotsT) (first n : Nat) (fold : Bool) (prodIn encIn : V) (b : Nat) :
    groupStart fold b + chainStride W * n + 2 ≤ (groupT W first n fold prodIn encIn b).2 := by
  have : (groupT W first n fold prodIn encIn b).2 = armB W first n fold prodIn encIn b (4 ^ n) := by
    simp only [groupT, groupD, groupArmsT]; rw [armsT_snd]; rfl
  rw [this, ← armB_one W first n fold prodIn encIn b]
  exact armB_mono W first n fold prodIn encIn b (Nat.one_le_two_pow.trans
    (Nat.pow_le_pow_left (by norm_num) n))

theorem cwState_succ (W : WotsT) (b p : Nat) :
    (cwState W b (p + 1)).2.2 = (groupT W (3 * p) 3 (p == 0) (cwState W b p).1 (cwState W b p).2.1
      (cwState W b p).2.2).2 := rfl

theorem cwState_mono (W : WotsT) (b : Nat) : ∀ p, b ≤ (cwState W b p).2.2
  | 0 => le_rfl
  | p + 1 => by
      rw [cwState_succ]
      have := groupT_end W (3 * p) 3 (p == 0) (cwState W b p).1 (cwState W b p).2.1 (cwState W b p).2.2
      have := cwState_mono W b p
      rw [groupStart_eq] at *
      omega

theorem Completes.keep {lo hi : Nat} {ss : List Stmt} {σ : Val} {P : Val → Prop} {Q Q' : Val → Prop}
    (h : Completes C rd lo hi ss σ P) (hq : Q σ) (ht : ∀ σ', Ext lo hi σ σ' → Q σ → Q' σ') :
    Completes C rd lo hi ss σ (fun σ' => P σ' ∧ Q' σ') :=
  let ⟨σ', he, hp, hh⟩ := h
  ⟨σ', he, ⟨hp, ht σ' he hq⟩, hh⟩

theorem cwState_in (W : WotsT) {b : Nat} (hb : 0 < b) :
    ∀ p, NBv (cwState W b p).2.2 (cwState W b p).1 ∧ NBv (cwState W b p).2.2 (cwState W b p).2.1
  | 0 => ⟨⟨0, hb, rfl⟩, ⟨0, hb, rfl⟩⟩
  | p + 1 => by
      have := groupT_end W (3 * p) 3 (p == 0) (cwState W b p).1 (cwState W b p).2.1 (cwState W b p).2.2
      rw [cwState_succ]
      exact ⟨⟨_, by omega, rfl⟩, ⟨_, by omega, rfl⟩⟩

theorem cwState_le (W : WotsT) (b p : Nat) : ∀ m, (cwState W b p).2.2 ≤ (cwState W b (p + m)).2.2
  | 0 => le_rfl
  | m + 1 => by
      have := cwState_le W b p m
      have h2 := groupT_end W (3 * (p + m)) 3 (p + m == 0) (cwState W b (p + m)).1
        (cwState W b (p + m)).2.1 (cwState W b (p + m)).2.2
      rw [show p + (m + 1) = p + m + 1 by omega, cwState_succ]
      rw [groupStart_eq] at h2
      omega

theorem groupT_snd_eq (W : WotsT) (first n : Nat) (fold : Bool) (prodIn encIn : V) (b : Nat) :
    (groupT W first n fold prodIn encIn b).2 = armB W first n fold prodIn encIn b (4 ^ n) := by
  simp only [groupT, groupD, groupArmsT]; rw [armsT_snd]; rfl

/-- **A group completes from any valuation**, its digits `k` loaded at `d` and its arm's starts
`vals`, its statements `pre` a sequential block on `d + 5 ..< b + 5` after which `good` holds. -/
theorem groupD_load {W : WotsT} {B : Nat} {good : Val → Prop} (hW : StepShape W B)
    (hc : StepCanon W B good) {first n : Nat} {fold : Bool} {prodIn encIn : V} {d : Nat}
    {pre : List Stmt} {b k : Nat}
    (hn : n ≤ 3) (hk : k < 4 ^ n) (hm : MemOK rd 64) (hdb : d ≤ b) (hB : B ≤ b + 5)
    (hpre : SeqOK (d + 5) pre (b + 5)) (hpi : NBv B prodIn)
    (hei : NBv B encIn) (hpw : NBv B (W.power (digitSum k n))) (vals : Nat → E)
    (hv : ∀ t < n, IsCanonical128 (vals t)) (σ : Val)
    (hg : ∀ σ', AgreeBelow d σ σ' → AtomsHold rd σ' pre → good σ') :
    Completes C rd d (groupD W first n fold prodIn encIn d pre b).2 (groupD W first n fold prodIn encIn d pre b).1 σ
      (fun σ' => σ' (.n d) = ofK (addressOfIndex k) ∧ (∀ t < n, IsCanonical128 (σ' (.n (slotsT W fold b t 2)))) ∧
        (∀ t < n, σ' (grpPos W first n fold prodIn encIn b k t) = vals t) ∧ good σ') := by
  obtain ⟨hl1, hl2, hl3⟩ := gLoadD_spec W first n fold prodIn encIn d b k vals σ hk hdb
  have hend : (groupD W first n fold prodIn encIn d pre b).2 = armB W first n fold prodIn encIn b (4 ^ n) := by
    simp only [groupD, groupArmsT]; rw [armsT_snd]; rfl
  rw [← hend] at hl1
  refine ((groupD_complete (C := C) (rd := rd) hW hc hn hk hm hdb hB hpre hpi hei hpw _
    (fun σ' he hh => hg σ' (fun j hj => (hl1.apply (Or.inl hj)).symm.trans (he.agree j (by omega))) hh)
    hl2 (fun t ht => ?_)).reload hl1).mono le_rfl le_rfl
    (fun σ' ⟨h1, h2, h3, h4⟩ => ⟨h1, h2, fun t ht => by rw [h3 t ht, hl3 t ht], h4⟩)
  show IsCanonical128 (gLoadD W first n fold prodIn encIn d b k vals σ (grpPos W first n fold prodIn encIn b k t))
  rw [hl3 t ht]
  exact hv t ht

/-- **A group completes from any valuation**, its digits `k` and its arm's starts `vals` loaded. -/
theorem groupT_load {W : WotsT} {B : Nat} {good : Val → Prop} (hW : StepShape W B)
    (hc : StepCanon W B good) {first n : Nat} {fold : Bool} {prodIn encIn : V} {b k : Nat}
    (hn : n ≤ 3) (hk : k < 4 ^ n) (hm : MemOK rd 64) (hB : B ≤ b) (hpi : NBv B prodIn)
    (hei : NBv B encIn) (hpw : ∀ j, NBv B (W.power j)) (vals : Nat → E)
    (hv : ∀ t < n, IsCanonical128 (vals t)) (σ : Val) (hg : good σ) :
    Completes C rd b (groupT W first n fold prodIn encIn b).2 (groupT W first n fold prodIn encIn b).1 σ
      (fun σ' => σ' (.n b) = ofK (addressOfIndex k) ∧ (∀ t < n, IsCanonical128 (σ' (.n (slotsT W fold b t 2)))) ∧
        ∀ t < n, σ' (grpPos W first n fold prodIn encIn b k t) = vals t) := by
  obtain ⟨hl1, hl2, hl3⟩ := gLoad_spec W first n fold prodIn encIn b k vals σ hk
  rw [← groupT_snd_eq] at hl1
  have hgr : good (gLoad W first n fold prodIn encIn b k vals σ) :=
    hc.1 _ _ (fun j hj => (hl1.apply (Or.inl (by omega))).symm) hg
  refine ((groupT_complete (C := C) (rd := rd) hW hc hn hk hm hB hpi hei hpw _ hgr hl2
    (fun t ht => ?_)).reload hl1).mono le_rfl le_rfl
    (fun σ' ⟨h1, h2, h3⟩ => ⟨h1, h2, fun t ht => by rw [h3 t ht, hl3 t ht]⟩)
  show IsCanonical128 (gLoad W first n fold prodIn encIn b k vals σ (grpPos W first n fold prodIn encIn b k t))
  rw [hl3 t ht]
  exact hv t ht

/-- The start of chain `i` of a codeword, in the arm of its group's digits `K`. -/
def cwPos (W : WotsT) (G b : Nat) (K : Nat → Nat) (i : Nat) : V :=
  grpPos W (3 * (i / 3)) (cwN G (i / 3)) (i / 3 == 0) (cwState W b (i / 3)).1 (cwState W b (i / 3)).2.1
    (cwState W b (i / 3)).2.2 (K (i / 3)) (i % 3)

theorem cwPos_eq (W : WotsT) (G b : Nat) (K : Nat → Nat) (q t : Nat) (ht : t < 3) :
    cwPos W G b K (3 * q + t) = grpPos W (3 * q) (cwN G q) (q == 0) (cwState W b q).1
      (cwState W b q).2.1 (cwState W b q).2.2 (K q) t := by
  have h1 : (3 * q + t) / 3 = q := by omega
  have h2 : (3 * q + t) % 3 = t := by omega
  simp only [cwPos, h1, h2]

/-- **The groups of a codeword complete**, each from its digits `K q` and its starts `vals` loaded. -/
theorem groupsT_complete {W : WotsT} {B : Nat} {good : Val → Prop} (hW : StepShape W B)
    (hc : StepCanon W B good) {G b : Nat} (hb0 : 0 < b) (hB : B ≤ b) (hm : MemOK rd 64)
    (hpw : ∀ j, NBv B (W.power j)) (K : Nat → Nat) (hK : ∀ q < G, K q < 64) (vals : Nat → E)
    (hv : ∀ i, IsCanonical128 (vals i)) :
    ∀ m p, p + m ≤ G → ∀ σ, good σ →
      Completes C rd (cwState W b p).2.2 (cwState W b (p + m)).2.2
        (groupsT W m p (cwState W b p).1 (cwState W b p).2.1 (cwState W b p).2.2).1 σ
        (fun σ' => good σ' ∧ ∀ q, p ≤ q → q < p + m → σ' (.n (cwState W b q).2.2) = ofK (addressOfIndex (K q)) ∧
          (∀ t < 3, IsCanonical128 (σ' (.n (slotsT W (q == 0) (cwState W b q).2.2 t 2)))) ∧
          ∀ t < 3, σ' (cwPos W G b K (3 * q + t)) = vals (3 * q + t))
  | 0, p, _, σ, hg => ⟨σ, Ext.refl _ _ _, ⟨hg, fun q h1 h2 => by omega⟩, fun _ _ hn => hn⟩
  | m + 1, p, hpm, σ, hg => by
      have hbp := cwState_mono W b p
      have hBp : B ≤ (cwState W b p).2.2 := by omega
      obtain ⟨hpi, hei⟩ := cwState_in W hb0 p
      have hpwp : ∀ j, NBv (cwState W b p).2.2 (W.power j) := fun j => (hpw j).mono' hBp
      have hn : cwN G p = 3 := by simp [cwN]; omega
      have hgroup := groupT_load (C := C) (rd := rd) (first := 3 * p) (fold := p == 0) (hW.mono hBp)
        (hc.mono hBp) (le_refl 3) (show K p < 4 ^ 3 from hK p (by omega)) hm le_rfl hpi hei hpwp
        (fun t => vals (3 * p + t)) (fun t _ => hv _) σ hg
      have hnb := groupT_numBelow (first := 3 * p) (n := 3) (fold := p == 0) hW hBp hpi hei hpwp
      have hle := cwState_le W b (p + 1) m
      have hend : (cwState W b (p + 1)).2.2 =
          armB W (3 * p) 3 (p == 0) (cwState W b p).1 (cwState W b p).2.1 (cwState W b p).2.2 (4 ^ 3) := by
        rw [cwState_succ, groupT_snd_eq]
      simp only [groupsT]
      refine Completes.append (m := (cwState W b (p + 1)).2.2) (cwState_le W b p 1)
        (by rw [show p + (m + 1) = p + 1 + m by omega]; exact hle) hnb hgroup (fun σ1 he1 hp1 => ?_)
      have hag : AgreeBelow B σ σ1 := fun k hk => he1.agree k (by omega)
      have hg1 := hc.1 _ _ hag hg
      have ih := groupsT_complete hW hc hb0 hB hm hpw K hK vals hv m (p + 1) (by omega) σ1 hg1
      rw [show p + (m + 1) = p + 1 + m by omega]
      refine (ih.keep (Q := fun σ
          => σ (.n (cwState W b p).2.2) = ofK (addressOfIndex (K p)) ∧ (∀ t < 3,
          IsCanonical128 (σ (.n (slotsT W (p == 0) (cwState W b p).2.2 t 2)))) ∧
          ∀ t < 3, σ (grpPos W (3 * p) 3 (p == 0) (cwState W b p).1 (cwState W b p).2.1
            (cwState W b p).2.2 (K p) t) = vals (3 * p + t))
        (Q' := fun σ => σ (.n (cwState W b p).2.2) = ofK (addressOfIndex (K p)) ∧ (∀ t < 3,
          IsCanonical128 (σ (.n (slotsT W (p == 0) (cwState W b p).2.2 t 2)))) ∧
          ∀ t < 3, σ (grpPos W (3 * p) 3 (p == 0) (cwState W b p).1 (cwState W b p).2.1
            (cwState W b p).2.2 (K p) t) = vals (3 * p + t))
        hp1 (fun σ' he' hq => ⟨?_, fun t ht => ?_, fun t ht => ?_⟩)).mono le_rfl le_rfl
        (fun σ' ⟨⟨hg', hr⟩, hq'⟩ => ⟨hg', fun q h1 h2 => ?_⟩)
      · have := cwState_le W b p 1
        have := groupT_end W (3 * p) 3 (p == 0) (cwState W b p).1 (cwState W b p).2.1 (cwState W b p).2.2
        rw [he'.apply (Or.inl (by rw [cwState_succ]; rw [groupStart_eq] at this; omega))]
        exact hq.1
      · have hs := (slot_bounds W (p == 0) (cwState W b p).2.2 t 2 (by norm_num)).2
        have := groupT_end W (3 * p) 3 (p == 0) (cwState W b p).1 (cwState W b p).2.1 (cwState W b p).2.2
        have : chainStride W * (t + 1) ≤ chainStride W * 3 := Nat.mul_le_mul_left _ (by omega)
        rw [he'.apply (Or.inl (by rw [cwState_succ]; omega))]
        exact hq.2.1 t ht
      · obtain ⟨j, ej, -, hj, -⟩ := grpPos_spec W (3 * p) 3 (p == 0) (cwState W b p).1 (cwState W b p).2.1
          (cwState W b p).2.2 (K p) t (hK p (by omega)) ht
        rw [ej, he'.apply (Or.inl (by rw [hend]; exact hj)), ← ej]
        exact hq.2.2 t ht
      · rcases Nat.lt_or_ge q (p + 1) with hq | hq
        · have : q = p := by omega
          subst this
          refine ⟨hq'.1, hq'.2.1, fun t ht => ?_⟩
          rw [cwPos_eq W G b K q t ht, hn]
          exact hq'.2.2 t ht
        · exact hr q hq (by omega)

/-- The digit `i` of the digits `K` of the groups. -/
def digK (K : Nat → Nat) (i : Nat) : Nat := K (i / 3) / 4 ^ (i % 3) % 4

theorem codewordT_eq (W : WotsT) (G : Nat) (target : E) (d0 : V) (b : Nat) :
    (codewordT W G target d0 b).1 =
      (groupsT W G 0 (cwState W b 0).1 (cwState W b 0).2.1 (cwState W b 0).2.2).1 ++
        (groupT W (3 * G) 1 false (cwState W b G).1 (cwState W b G).2.1 (cwState W b G).2.2).1 ++
        [copyS d0 (encT W false 1 (cwState W b G).2.2),
          cst (groupT W (3 * G) 1 false (cwState W b G).1 (cwState W b G).2.1 (cwState W b G).2.2).2 target,
          .atom (.assertEq (prodT W false 1 (cwState W b G).2.2)
            (.n (groupT W (3 * G) 1 false (cwState W b G).1 (cwState W b G).2.1 (cwState W b G).2.2).2))] := by
  have hgs := groupsT_eq W b G 0
  simp only [Nat.zero_add] at hgs
  have hgs' : (groupsT W G 0 (.n 0) (.n 0) b).2 = _ := hgs
  simp only [codewordT]
  rw [hgs']
  rfl

theorem codewordT_snd (W : WotsT) (G : Nat) (target : E) (d0 : V) (b : Nat) :
    (codewordT W G target d0 b).2.1 =
      (groupT W (3 * G) 1 false (cwState W b G).1 (cwState W b G).2.1 (cwState W b G).2.2).2 + 1 := by
  have hgs := groupsT_eq W b G 0
  simp only [Nat.zero_add] at hgs
  have hgs' : (groupsT W G 0 (.n 0) (.n 0) b).2 = _ := hgs
  simp only [codewordT]
  rw [hgs']

theorem groupsT_numBelow {W : WotsT} {B : Nat} (hW : StepShape W B) {b : Nat} (hb0 : 0 < b) (hB : B ≤ b)
    (hpw : ∀ j, NBv B (W.power j)) : ∀ m p,
    NumBelow (cwState W b (p + m)).2.2
      (Stmt.valsList (groupsT W m p (cwState W b p).1 (cwState W b p).2.1 (cwState W b p).2.2).1)
  | 0, _ => NumBelow.nil _
  | m + 1, p => by
      have hbp := cwState_mono W b p
      obtain ⟨hpi, hei⟩ := cwState_in W hb0 p
      have h1 := groupT_numBelow (first := 3 * p) (n := 3) (fold := p == 0) hW (show B ≤ (cwState W b p).2.2 by omega)
        hpi hei (fun j => (hpw j).mono' (by omega))
      have h2 := groupsT_numBelow hW hb0 hB hpw m (p + 1)
      have hle := cwState_le W b (p + 1) m
      simp only [groupsT, valsList_append]
      rw [show p + (m + 1) = p + 1 + m by omega]
      exact (h1.mono (by rw [← cwState_succ]; exact hle)).append h2

/-- **The codeword completes**: its groups dispatching on the digits `K`, the digest's first cell
their base-4 number and the target `g` to their sum, the chains' starts `vals` loaded and kept. -/
theorem codewordT_complete {W : WotsT} {B : Nat} {good : Val → Prop} (hW : StepShape W B)
    (hc : StepCanon W B good) (hWa : StepAtoms W) {F : Val → Nat → Nat → E → E}
    (hss : ∀ σ, good σ → StepSound rd σ W (F σ)) (hpow : ∀ σ, good σ → ∀ s < 10, σ (W.power s) = gen ^ s)
    {G : Nat} {target : E} {d0 : V} {b : Nat} (hG : 0 < G) (hG21 : G ≤ 21) (hb0 : 0 < b) (hB : B ≤ b)
    (hm : MemOK rd 64) (hpw : ∀ j, NBv B (W.power j)) (hd0 : NBv b d0) (K : Nat → Nat)
    (hK : ∀ q ≤ G, K q < 4 ^ cwN G q) (vals : Nat → E) (hv : ∀ i, IsCanonical128 (vals i)) (σ : Val)
    (hg : good σ)
    (hsum : gen ^ (∑ i ∈ Finset.range (3 * G + 1), digK K i) = target)
    (hd0v : σ d0 = lit (∑ i ∈ Finset.range (3 * G + 1), digK K i * 4 ^ i))
    (hE : ∀ first n k, W.enc first n k = k * 4 ^ first := by intros; rfl) :
    Completes C rd b (codewordT W G target d0 b).2.1 (codewordT W G target d0 b).1 σ
      (fun σ' => good σ' ∧ (∀ i < 3 * G + 1, IsCanonical128 (σ' (cwTip W b i))) ∧
        (∀ q ≤ G, σ' (.n (cwState W b q).2.2) = ofK (addressOfIndex (K q))) ∧
        ∀ i < 3 * G + 1, σ' (cwPos W G b K i) = vals i) := by
  have hbG := cwState_mono W b G
  obtain ⟨hpiG, heiG⟩ := cwState_in W hb0 G
  have hpwG : ∀ j, NBv (cwState W b G).2.2 (W.power j) := fun j => (hpw j).mono' (by omega)
  have hendL := groupT_end W (3 * G) 1 false (cwState W b G).1 (cwState W b G).2.1 (cwState W b G).2.2
  rw [groupStart_eq] at hendL
  simp only [Bool.false_eq_true, ↓reduceIte, Nat.add_zero] at hendL
  rw [codewordT_eq, codewordT_snd]
  have hnbG := groupsT_numBelow hW hb0 hB hpw G 0
  simp only [Nat.zero_add] at hnbG
  have hnbL := groupT_numBelow (first := 3 * G) (n := 1) (fold := false) hW
    (show B ≤ (cwState W b G).2.2 by omega) hpiG heiG hpwG
  have hfG : (G == 0) = false := by simp; omega
  have hnG : cwN G G = 1 := by simp [cwN]
  have hK3 : ∀ q < G, K q < 64 := fun q hq => by simpa [cwN, hq] using hK q (by omega)
  -- where the starts are
  have hposq : ∀ q < G, ∀ t < 3, ∃ j, cwPos W G b K (3 * q + t) = .n j ∧ j < (cwState W b G).2.2 := by
    intro q hq t ht
    rw [cwPos_eq W G b K q t ht]
    have hn3 : cwN G q = 3 := by simp [cwN, hq]
    obtain ⟨j, ej, -, hj, -⟩ := grpPos_spec W (3 * q) (cwN G q) (q == 0) (cwState W b q).1
      (cwState W b q).2.1 (cwState W b q).2.2 (K q) t (hK q (by omega)) (by rw [hn3]; exact ht)
    refine ⟨j, ej, ?_⟩
    have hle := cwState_le W b (q + 1) (G - (q + 1))
    rw [show q + 1 + (G - (q + 1)) = G by omega, cwState_succ, groupT_snd_eq] at hle
    rw [hn3] at hj
    omega
  have hposG : ∃ j, cwPos W G b K (3 * G + 0) = .n j ∧
      j < (groupT W (3 * G) 1 false (cwState W b G).1 (cwState W b G).2.1 (cwState W b G).2.2).2 := by
    rw [cwPos_eq W G b K G 0 (by omega)]
    obtain ⟨j, ej, -, hj, -⟩ := grpPos_spec W (3 * G) (cwN G G) (G == 0) (cwState W b G).1
      (cwState W b G).2.1 (cwState W b G).2.2 (K G) 0 (hK G le_rfl) (by rw [hnG]; omega)
    refine ⟨j, ej, ?_⟩
    rw [groupT_snd_eq]
    rw [hnG, hfG] at hj
    exact hj
  -- the groups, then the last chain's
  have hgl : Completes C rd b (groupT W (3 * G) 1 false (cwState W b G).1 (cwState W b G).2.1
      (cwState W b G).2.2).2
      ((groupsT W G 0 (cwState W b 0).1 (cwState W b 0).2.1 (cwState W b 0).2.2).1 ++
        (groupT W (3 * G) 1 false (cwState W b G).1 (cwState W b G).2.1 (cwState W b G).2.2).1) σ
      (fun σ' => good σ' ∧ (∀ q ≤ G, σ' (.n (cwState W b q).2.2) = ofK (addressOfIndex (K q))) ∧
        (∀ i < 3 * G + 1, IsCanonical128 (σ' (cwTip W b i))) ∧
        ∀ i < 3 * G + 1, σ' (cwPos W G b K i) = vals i) := by
    have hgc := groupsT_complete (C := C) (rd := rd) hW hc hb0 hB hm hpw K hK3 vals hv G 0 (by omega) σ hg
    rw [Nat.zero_add] at hgc
    refine Completes.append (m := (cwState W b G).2.2) hbG (by omega) hnbG hgc (fun σ1 he1 hp1 => ?_)
    obtain ⟨hg1, hq1⟩ := hp1
    have hlast := groupT_load (C := C) (rd := rd) (first := 3 * G) (prodIn := (cwState W b G).1)
      (encIn := (cwState W b G).2.1) (fold := false)
      (hW.mono (show B ≤ (cwState W b G).2.2 by omega)) (hc.mono (show B ≤ (cwState W b G).2.2 by omega))
      (by norm_num) (show K G < 4 ^ 1 by simpa [hnG] using hK G le_rfl) hm le_rfl hpiG heiG hpwG
      (fun t => vals (3 * G + t)) (fun t _ => hv _) σ1 hg1
    refine (hlast.keep (Q := fun σ => good σ ∧ ∀ q < G, σ (.n (cwState W b q).2.2) = ofK (addressOfIndex (K q)) ∧
        (∀ t < 3, IsCanonical128 (σ (.n (slotsT W (q == 0) (cwState W b q).2.2 t 2)))) ∧
        ∀ t < 3, σ (cwPos W G b K (3 * q + t)) = vals (3 * q + t))
      (Q' := fun σ => good σ ∧ ∀ q < G, σ (.n (cwState W b q).2.2) = ofK (addressOfIndex (K q)) ∧
        (∀ t < 3, IsCanonical128 (σ (.n (slotsT W (q == 0) (cwState W b q).2.2 t 2)))) ∧
        ∀ t < 3, σ (cwPos W G b K (3 * q + t)) = vals (3 * q + t))
      ⟨hg1, fun q hq => hq1 q (by omega) (by omega)⟩ (fun σ' he' hq => ⟨?_, fun q hqG => ?_⟩)).mono
      le_rfl le_rfl (fun σ' ⟨⟨hhint, htip, hkl⟩, hgood, hgr⟩ =>
        ⟨hgood, fun q hq => ?_, fun i hi => ?_, fun i hi => ?_⟩)
    · exact hc.1 _ _ (fun j hj => he'.agree j (by omega)) hq.1
    · have hle := cwState_le W b (q + 1) (G - (q + 1))
      rw [show q + 1 + (G - (q + 1)) = G by omega] at hle
      have hend := groupT_end W (3 * q) 3 (q == 0) (cwState W b q).1 (cwState W b q).2.1 (cwState W b q).2.2
      rw [← cwState_succ, groupStart_eq] at hend
      refine ⟨by rw [he'.apply (Or.inl (by split at hend <;> omega))]; exact (hq.2 q hqG).1,
        fun t ht => ?_, fun t ht => ?_⟩
      · have hs := (slot_bounds W (q == 0) (cwState W b q).2.2 t 2 (by norm_num)).2
        have : chainStride W * (t + 1) ≤ chainStride W * 3 := Nat.mul_le_mul_left _ (by omega)
        rw [groupStart_eq] at hs
        rw [he'.apply (Or.inl (by split at hs <;> split at hend <;> omega))]
        exact (hq.2 q hqG).2.1 t ht
      · obtain ⟨j, ej, hj⟩ := hposq q hqG t ht
        rw [ej, he'.apply (Or.inl hj), ← ej]
        exact (hq.2 q hqG).2.2 t ht
    · rcases Nat.lt_or_ge q G with hq' | hq'
      · exact (hgr q hq').1
      · have : q = G := by omega
        subst this
        exact hhint
    · unfold cwTip
      rcases Nat.lt_or_ge (i / 3) G with hq' | hq'
      · exact (hgr (i / 3) hq').2.1 (i % 3) (Nat.mod_lt _ (by norm_num))
      · have h1 : i / 3 = G := by omega
        have h2 : i % 3 = 0 := by omega
        rw [h1, h2, hfG]
        exact htip 0 (by norm_num)
    · have hi' : i = 3 * (i / 3) + i % 3 := by omega
      rw [hi']
      rcases Nat.lt_or_ge (i / 3) G with hq' | hq'
      · exact (hgr (i / 3) hq').2.2 (i % 3) (Nat.mod_lt _ (by norm_num))
      · have h1 : i / 3 = G := by omega
        have h2 : i % 3 = 0 := by omega
        rw [h1, h2, cwPos_eq W G b K G 0 (by omega), hnG, hfG]
        exact hkl 0 (by norm_num)
  have hnb1 : NumBelow (groupT W (3 * G) 1 false (cwState W b G).1 (cwState W b G).2.1 (cwState W b G).2.2).2
      (Stmt.valsList ((groupsT W G 0 (cwState W b 0).1 (cwState W b 0).2.1 (cwState W b 0).2.2).1 ++
        (groupT W (3 * G) 1 false (cwState W b G).1 (cwState W b G).2.1 (cwState W b G).2.2).1)) := by
    rw [valsList_append]
    exact (hnbG.mono (by omega)).append hnbL
  refine Completes.append (m := (groupT W (3 * G) 1 false (cwState W b G).1 (cwState W b G).2.1
    (cwState W b G).2.2).2) (by omega) (Nat.le_succ _) hnb1 hgl.withHolds (fun σ1 he1 hp1 => ?_)
  obtain ⟨⟨hg1, hk1, ht1, hkept1⟩, hhold⟩ := hp1
  -- the groups' facts
  have hgrp : ∀ p ≤ G, ∃ k < 4 ^ cwN G p, σ1 (.n (cwState W b p).2.2) = ofK (addressOfIndex k) ∧
      AtomsHold rd σ1 (cwArm W G b p k).1 := by
    obtain ⟨h1, hg⟩ := groupsT_sound (rd := rd) (σ := σ1) (C := C) hWa b G 0 hhold
    obtain ⟨-, kL, hkL, hxL, haL⟩ := groupT_sound (rest := []) hWa (by simpa using h1)
    intro p hp
    by_cases hpG : p < G
    · obtain ⟨k, hk, hx, ha⟩ := hg p hpG
      simp only [Nat.zero_add] at hk hx ha
      exact ⟨k, by simp only [cwN, hpG, ↓reduceIte]; exact hk, hx, by simpa [cwArm, cwN, hpG] using ha⟩
    · have hpe : p = G := by omega
      subst hpe
      exact ⟨kL, by simpa [cwN] using hkL, hxL, by simpa [cwArm, cwN, hfG] using haL⟩
  obtain ⟨-, hprod, henc⟩ := codeword_vals (hss σ1 hg1) (hpow σ1 hg1) hG hG21 hgrp hE
  have hdig : ∀ i < 3 * G + 1, cwDigit W G b σ1 i = digK K i := by
    intro i hi
    have hb : 4 ^ cwN G (i / 3) ≤ 2 ^ 64 - 1 := by unfold cwN; split <;> norm_num
    unfold cwDigit cwK digK
    rw [logG_eq (hK (i / 3) (by omega)) hb (hk1 (i / 3) (by omega))]
  have hs1 : ∑ i ∈ Finset.range (3 * G + 1), cwDigit W G b σ1 i = ∑ i ∈ Finset.range (3 * G + 1), digK K i :=
    Finset.sum_congr rfl fun i hi => hdig i (Finset.mem_range.mp hi)
  have hs2 : ∑ i ∈ Finset.range (3 * G + 1), cwDigit W G b σ1 i * 4 ^ i =
      ∑ i ∈ Finset.range (3 * G + 1), digK K i * 4 ^ i :=
    Finset.sum_congr rfl fun i hi => by rw [hdig i (Finset.mem_range.mp hi)]
  rw [hs1, hsum] at hprod
  rw [hs2, ← hd0v] at henc
  have hd01 : σ1 d0 = σ d0 := by
    obtain ⟨j, hj, rfl⟩ := hd0
    exact he1.apply (Or.inl hj)
  -- the checks
  set c := (groupT W (3 * G) 1 false (cwState W b G).1 (cwState W b G).2.1 (cwState W b G).2.2).2 with hcdef
  have hext : Ext c (c + 1) σ1 (upds σ1 [(c, target)]) := upds_ext σ1 _ (by simp)
  have hpo : (prodT W false 1 (cwState W b G).2.2) = .n (groupStart false (cwState W b G).2.2 + chainStride W * 1) :=
    rfl
  have heo : (encT W false 1 (cwState W b G).2.2) = .n (groupStart false (cwState W b G).2.2 + chainStride W * 1 + 1) :=
    rfl
  have hgs : groupStart false (cwState W b G).2.2 = (cwState W b G).2.2 + 6 := by simp [groupStart]
  have hpv : upds σ1 [(c, target)] (prodT W false 1 (cwState W b G).2.2) = target := by
    rw [hpo, hext.apply (Or.inl (by rw [hgs]; omega)), ← hpo, hprod]
  have hev : upds σ1 [(c, target)] (encT W false 1 (cwState W b G).2.2) = σ d0 := by
    rw [heo, hext.apply (Or.inl (by rw [hgs]; omega)), ← heo, henc]
  have hdv : upds σ1 [(c, target)] d0 = σ d0 := by
    obtain ⟨j, hj, rfl⟩ := hd0
    rw [hext.apply (Or.inl (by omega))]
    exact hd01
  refine completes_atoms rfl hext ⟨hc.1 _ _ (fun j hj => hext.agree j (by omega)) hg1, fun i hi => ?_,
    fun q hq => ?_, fun i hi => ?_⟩ (fun a ha => ?_)
  · have := ht1 i hi
    unfold cwTip at this ⊢
    have hlt : slotsT W (i / 3 == 0) (cwState W b (i / 3)).2.2 (i % 3) 2 < c := by
      have hs := (slot_bounds W (i / 3 == 0) (cwState W b (i / 3)).2.2 (i % 3) 2 (by norm_num)).2
      rcases Nat.lt_or_ge (i / 3) G with hq | hq
      · have hle := cwState_le W b (i / 3 + 1) (G - (i / 3 + 1))
        rw [show i / 3 + 1 + (G - (i / 3 + 1)) = G by omega] at hle
        have hend := groupT_end W (3 * (i / 3)) 3 (i / 3 == 0) (cwState W b (i / 3)).1
          (cwState W b (i / 3)).2.1 (cwState W b (i / 3)).2.2
        rw [← cwState_succ] at hend
        have : chainStride W * (i % 3 + 1) ≤ chainStride W * 3 := Nat.mul_le_mul_left _ (by omega)
        omega
      · have h1 : i / 3 = G := by omega
        have h2 : i % 3 = 0 := by omega
        rw [h1, h2, hfG] at hs ⊢
        rw [hgs] at hs
        omega
    rw [hext.apply (Or.inl hlt)]
    exact this
  · have hle := cwState_le W b q (G - q)
    rw [show q + (G - q) = G by omega] at hle
    rw [hext.apply (Or.inl (by omega))]
    exact hk1 q hq
  · have hj : ∃ j, cwPos W G b K i = .n j ∧ j < c := by
      have hi' : i = 3 * (i / 3) + i % 3 := by omega
      rcases Nat.lt_or_ge (i / 3) G with hq' | hq'
      · obtain ⟨j, ej, hj⟩ := hposq (i / 3) hq' (i % 3) (Nat.mod_lt _ (by norm_num))
        rw [← hi'] at ej
        exact ⟨j, ej, by omega⟩
      · obtain ⟨j, ej, hj⟩ := hposG
        rw [show 3 * G + 0 = i by omega] at ej
        exact ⟨j, ej, hj⟩
    obtain ⟨j, ej, hj⟩ := hj
    rw [ej, hext.apply (Or.inl hj), ← ej]
    exact hkept1 i hi
  · simp only [copyS, cst, List.mem_cons, Stmt.atom.injEq, List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl | rfl
    · show upds σ1 [(c, target)] d0 = upds σ1 [(c, target)] (encT W false 1 (cwState W b G).2.2)
      rw [hdv, hev]
    · exact upds_cons_self σ1 c target []
    · show upds σ1 [(c, target)] _ + upds σ1 [(c, target)] (.n c) = 0
      rw [hpv, upds_cons_self]
      exact e_add_self _

end
end LeanVM.Guest.B1.Sig
