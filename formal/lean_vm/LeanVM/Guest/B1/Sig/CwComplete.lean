/-
  LeanVM.Guest.B1.Sig.CwComplete

  A WOTS+C group completes: its digits hinted, their range check on a memory of at least `4^n`
  words, the dispatch taking the arm of the digits.
-/

module

public import LeanVM.Guest.B1.Sig.WotsGroupComplete
public import LeanVM.Guest.B1.Sig.CwKeep
public import LeanVM.Guest.B1.Sig.Interface
public import LeanVM.Guest.B1.Sig.Shifts

/-!
# A group, complete

* `hintKeep_complete`: a hint completes keeping the valuation;
* `rangeS_complete`: a range check of `g^k`, `k < K ≤ n`, completes on a memory of `n` words;
* `holdsArms_of`, `match_complete`: a dispatch completes by its arm;
* `groupT_complete`: a group of digits `k`, its arm's starts kept.
-/

namespace LeanVM.Guest.B1.Sig

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Value

@[expose] public section

variable {C : CallRel} {rd : Reader}

theorem hintKeep_complete (σ : Val) (s : String) (vs : List V) (lo hi : Nat) :
    Completes C rd lo hi [hintW s vs] σ (fun σ' => σ' = σ) :=
  completes_atoms rfl (Ext.refl _ _ _) rfl (fun a ha => by
    simp only [hintW, List.mem_singleton, Stmt.atom.injEq] at ha
    subst ha
    trivial)

theorem load_gpow {n : Nat} (hm : MemOK rd n) {i : Nat} (hi : i < n) :
    ∃ w, LoadHolds rd (ofK (addressOfIndex i)) 0 w := by
  obtain ⟨w, hw⟩ := Option.isSome_iff_exists.mp (hm i hi)
  refine ⟨w, (isInK_iff _).mpr ⟨_, rfl⟩, ?_⟩
  simp only [limb_ofK, Fin.isValue, addressOfIndex, pow_zero, mul_one]
  simpa [addressOfIndex] using hw

/-- **A range check of `g^k` completes**, `k < K`, on a memory of `n ≥ K` words. -/
theorem rangeS_complete {n K k : Nat} (hm : MemOK rd n) (hK : K ≤ n) (hk : k < K) (σ : Val) (x : V)
    {b : Nat} (hx : ∃ j < b, x = .n j) (hxv : σ x = ofK (addressOfIndex k)) :
    Completes C rd b (b + 4) (rangeS x (ofK (addressOfIndex (K - 1))) b) σ (fun _ => True) := by
  obtain ⟨t1, h1⟩ := load_gpow hm (show k < n by omega)
  obtain ⟨t2, h2⟩ := load_gpow hm (show K - 1 - k < n by omega)
  set σ' := upds σ [(b, ofK (addressOfIndex (K - 1))), (b + 1, ofK (addressOfIndex (K - 1 - k))), (b + 2, t1), (b + 3, t2)]
  have hext : Ext b (b + 4) σ σ' := upds_ext σ _ (by
    intro p hp
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl <;> simp)
  have hx' : σ' x = σ x := by
    obtain ⟨j, hj, rfl⟩ := hx
    exact hext.apply (Or.inl hj)
  have e0 : σ' (.n b) = ofK (addressOfIndex (K - 1)) := by simp [σ', upds]
  have e1 : σ' (.n (b + 1)) = ofK (addressOfIndex (K - 1 - k)) := by simp [σ', upds]
  have e2 : σ' (.n (b + 2)) = t1 := by simp [σ', upds]
  have e3 : σ' (.n (b + 3)) = t2 := by simp [σ', upds]
  refine completes_atoms rfl hext trivial (fun a ha => ?_)
  simp only [rangeS, cst, List.mem_cons, Stmt.atom.injEq, List.not_mem_nil, or_false] at ha
  rcases ha with rfl | rfl
  · exact e0
  · refine ⟨by rw [hx', hxv, e2]; exact h1, ?_, by rw [e1, e3]; exact h2⟩
    rw [e0, hx', hxv, e1, ← ofK_mul, addressOfIndex, addressOfIndex, addressOfIndex, ← pow_add]
    congr 2
    omega

theorem holdsArms_of {x : V} {σ : Val} : ∀ (arms : List (List Stmt)) (j0 k : Nat) (hk : k < arms.length)
    {N : Prop} {kret : List E → Prop}, σ x = ofK (addressOfIndex (j0 + k)) →
    Stmt.HoldsList C rd σ arms[k] N kret → Stmt.HoldsArms C rd σ x j0 arms N kret
  | [], _, _, hk, _, _, _, _ => absurd hk (by simp)
  | a :: as, j0, 0, _, _, _, hx, h => Or.inl ⟨by simpa using hx, h⟩
  | a :: as, j0, k + 1, hk, _, _, hx, h =>
      Or.inr (holdsArms_of as (j0 + 1) k (by simpa using hk)
        (by rw [hx]; congr 2; omega) h)

/-- **A dispatch completes** by the arm its value selects. -/
theorem match_complete {x : V} {arms : List (List Stmt)} {k lo hi : Nat} (hk : k < arms.length)
    (hx : ∃ j < lo, x = .n j) {σ : Val} (hxv : σ x = ofK (addressOfIndex k)) {Post : Val → Prop}
    (h : Completes C rd lo hi arms[k] σ Post) :
    Completes C rd lo hi [.match_ x arms] σ Post := by
  obtain ⟨σ', he, hp, hh⟩ := h
  refine ⟨σ', he, hp, fun next kret hn => ?_⟩
  have hx' : σ' x = σ x := by
    obtain ⟨j, hj, rfl⟩ := hx
    exact he.apply (Or.inl hj)
  exact holdsArms_of arms 0 k hk (by rw [hx', hxv, Nat.zero_add]) (hh next kret hn)

theorem word_two_pow_eq {j : Nat} (hj : j < 64) : word (2 ^ j) 0 = ofK (addressOfIndex j) := by
  rw [word_eq_eOfNat, ← Value.gen_pow_eq_eOfNat hj, Value.gen_pow_eq_ofK]

/-- **A group completes**, its digits `k` hinted at `d`, its statements `pre` a sequential block on
`d + 5 ..< b + 5` after which `good` holds, its arms laid out from `b`. -/
theorem groupD_complete {W : WotsT} {B : Nat} {good : Val → Prop} (hW : StepShape W B)
    (hc : GoodStable B good) {first n : Nat} {fold : Bool} {prodIn encIn : V} {d : Nat}
    {pre : List Stmt} {b k : Nat}
    (hn : n ≤ 3) (hk : k < 4 ^ n) (hm : MemOK rd 64) (hdb : d ≤ b) (hB : B ≤ b + 5)
    (hpre : SeqOK (d + 5) pre (b + 5)) (hpi : NBv B prodIn)
    (hei : NBv B encIn) (hpw : NBv B (W.power (digitSum k n))) (σ : Val)
    (hg : ∀ σ', Ext (d + 1) (b + 5) σ σ' → AtomsHold rd σ' pre → good σ')
    (hb : σ (.n d) = ofK (addressOfIndex k)) :
    Completes C rd d (groupD W first n fold prodIn encIn d pre b).2 (groupD W first n fold prodIn encIn d pre b).1 σ
      (fun σ' => σ' (.n d) = ofK (addressOfIndex k) ∧
        (∀ t < n, σ' (grpPos W first n fold prodIn encIn b k t) = σ (grpPos W first n fold prodIn encIn b k t)) ∧
        good σ') := by
  have h4n : 4 ^ n ≤ 64 := by
    calc 4 ^ n ≤ 4 ^ 3 := Nat.pow_le_pow_right (by norm_num) hn
      _ = 64 := by norm_num
  have hend : (groupD W first n fold prodIn encIn d pre b).2 = armB W first n fold prodIn encIn b (4 ^ n) := by
    simp only [groupD, groupArmsT]
    rw [armsT_snd]
    rfl
  have hge : b + 6 ≤ armB W first n fold prodIn encIn b (4 ^ n) := by
    rw [← armB_zero W first n fold prodIn encIn b]
    exact armB_mono W first n fold prodIn encIn b (Nat.zero_le _)
  have hpl := hpre.le
  rw [hend]
  simp only [groupD, List.cons_append, List.append_assoc]
  show Completes C rd d _ ([hintW "digits" [.n d]] ++
    (rangeS (.n d) (word (2 ^ (4 ^ n - 1)) 0) (d + 1) ++ (pre ++ ([cst (b + 5) closeLane] ++
      [.match_ (.n d) _])))) σ _
  refine Completes.append (m := d + 1) (by omega) (by omega)
    (by rw [valsList_hint]; exact .cons ⟨d, by omega, rfl⟩ (.nil _)) (hintKeep_complete σ _ _ _ _)
    (fun σ1 he1 hp1 => ?_)
  rw [hp1, word_two_pow_eq (by omega)]
  refine Completes.append (m := d + 5) (by omega) (by omega) ?_
    (rangeS_complete (n := 64) (K := 4 ^ n) hm h4n hk σ (.n d) ⟨d, by omega, rfl⟩ hb)
    (fun σ2 he2 _ => ?_)
  · simp only [rangeS, cst, valsList_cons, valsList_nil, Stmt.vals, Atom.vals, List.append_nil,
      List.cons_append, List.nil_append]
    repeat (first | exact .nil _ | (refine .cons ⟨_, ?_, rfl⟩ ?_; omega))
  refine Completes.append hpl (by omega) hpre.numBelow (seq_completes hpre σ2) (fun σ3 he3 hh3 => ?_)
  have he23 : Ext (d + 1) (b + 5) σ σ3 := he2.trans he3 (by omega) (by omega)
  have hg3 : good σ3 := hg σ3 he23 hh3
  refine Completes.append (m := b + 6) (by omega) (by omega) ?_ (cst_complete σ3 (b + 5) closeLane)
    (fun σ4 he4 _ => ?_)
  · simp only [cst, valsList_cons, valsList_nil, Stmt.vals, Atom.vals, List.append_nil]
    exact .cons ⟨b + 5, by omega, rfl⟩ (.nil _)
  have he4' : Ext (d + 1) (b + 6) σ σ4 := he23.trans he4 (by omega) (by omega)
  have hag : AgreeBelow (d + 1) σ σ4 := he4'.agree
  have hb4 : σ4 (.n d) = ofK (addressOfIndex k) := by rw [← hag d (by omega)]; exact hb
  have hg4 : good σ4 := hc _ _ (fun j hj => he4.agree j (by omega)) hg3
  have hk' : k < (groupArmsT W first n fold prodIn encIn b).1.length := by
    simp only [groupArmsT]; rw [armsT_length]; exact hk
  refine match_complete hk' ⟨d, by omega, rfl⟩ hb4 ?_
  simp only [groupArmsT]
  rw [armsT_getElem]
  simp only [Nat.zero_add]
  obtain ⟨σ', he', hp', hh'⟩ := groupArm_complete (C := C) (rd := rd) (first := first) (n := n) (fold := fold)
    (prodIn := prodIn) (encIn := encIn) (b := b) (k := k) hW hk (by omega) hpi hei hpw σ4
  refine ⟨σ', he', ⟨by rw [he'.apply (Or.inl (by omega))]; exact hb4, fun t ht => ?_,
    hc _ _ (fun j hj => he'.agree j (by omega)) hg4⟩, hh'⟩
  obtain ⟨j, ej, hj, -⟩ := grpPos_spec W first n fold prodIn encIn b k t hk ht
  rw [hp'.1, ej, fwd_hint_keep _ σ4 hp'.2
    (armStart_mem W (slotsT W fold b) first n fold prodIn encIn (prodT W fold n b) (encT W fold n b) k
      (armB W first n fold prodIn encIn b k) ht) (.n j) (by rw [← ej]; exact List.mem_singleton_self _),
    he4'.apply (Or.inr (by omega))]

/-- **A group completes**, its digits `k` hinted. -/
theorem groupT_complete {W : WotsT} {B : Nat} {good : Val → Prop} (hW : StepShape W B)
    (hc : GoodStable B good) {first n : Nat} {fold : Bool} {prodIn encIn : V} {b k : Nat}
    (hn : n ≤ 3) (hk : k < 4 ^ n) (hm : MemOK rd 64) (hB : B ≤ b) (hpi : NBv B prodIn)
    (hei : NBv B encIn) (hpw : ∀ j, NBv B (W.power j)) (σ : Val) (hg : good σ)
    (hb : σ (.n b) = ofK (addressOfIndex k)) :
    Completes C rd b (groupT W first n fold prodIn encIn b).2 (groupT W first n fold prodIn encIn b).1 σ
      (fun σ' => σ' (.n b) = ofK (addressOfIndex k) ∧
        ∀ t < n, σ' (grpPos W first n fold prodIn encIn b k t) = σ (grpPos W first n fold prodIn encIn b k t)) :=
  (groupD_complete (pre := []) hW hc hn hk hm le_rfl (by omega) rfl hpi hei (hpw _) σ
    (fun σ' he _ => hc _ _ (fun j hj => (he.agree j (by omega))) hg) hb).mono le_rfl le_rfl
    (fun _ h => ⟨h.1, h.2.1⟩)

end
end LeanVM.Guest.B1.Sig
