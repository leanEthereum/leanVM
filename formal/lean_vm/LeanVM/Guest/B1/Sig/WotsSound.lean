/-
  LeanVM.Guest.B1.Sig.WotsSound

  What the WOTS+C templates compute, for any chain step: a walk's tip is its chain from the
  hinted start, an arm folds its digits' sum and the digits, a group's dispatch takes one arm.
-/

module

public import LeanVM.Guest.B1.Sig.WotsT
public import LeanVM.Guest.B1.Sig.KeccakMsg

/-!
# WOTS+C, sound

Generic in the scheme's step: `StepSound rd σ W f` says that a step's atoms holding make its
output's first cell `f i s` of its input value (the step of chain `i` leaving position `s`).

* `walkT_sound`: chain `i` walked from digit `d` reaches its tip, `chainT f i (3 - d) d` of the
  start (`walkStartV`: the hinted value, the tip itself at `d = 3`);
* `armT_sound`: arm `k` walks each chain from its digit `k / 4^r % 4`, multiplies the product by
  `g^(digit sum)` and adds `k · 4^first` to the encoding;
* `groupT_sound`: a group's dispatch runs one arm `k < 4^n`, its selector `g^k`.
-/

namespace LeanVM.Guest.B1.Sig

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core

@[expose] public section

variable {C : CallRel} {rd : Reader} {σ : Val} {kret : List E → Prop}

/-- What a scheme's step computes: its output's first cell, `f i s` of its input value. -/
def StepSound (rd : Reader) (σ : Val) (W : WotsT) (f : Nat → Nat → E → E) : Prop :=
  ∀ i s v c o, AtomsHold rd σ (W.step i s v c o) → σ (.n o) = f i s (σ v)

/-- `m` steps of chain `i` from position `s`. -/
def chainT (f : Nat → Nat → E → E) (i : Nat) : Nat → Nat → E → E
  | 0, _, x => x
  | m + 1, s, x => chainT f i m (s + 1) (f i s x)

theorem chainT_succ (f : Nat → Nat → E → E) (i : Nat) :
    ∀ (m s : Nat) (x : E), chainT f i (m + 1) s x = f i (s + m) (chainT f i m s x)
  | 0, s, x => by simp [chainT]
  | m + 1, s, x => by
      rw [chainT, chainT_succ f i m (s + 1), chainT]
      congr 1
      omega

/-- Where a walk's start is: its hint at the base, or the tip at `d = 3`. -/
def walkStartV (slot : Nat → Nat) (d b : Nat) : V := if d = 3 then .n (slot 2) else .n b

theorem mem_walkT_step (W : WotsT) {i : Nat} {slot : Nat → Nat} {stride d b j : Nat} (hd : d ≠ 3)
    (hj : j < 3 - d) {x : Stmt}
    (hx : x ∈ W.step i (d + j) (if j = 0 then .n b else .n (slot (d + j - 1))) (b + 1 + j * stride)
      (slot (d + j))) :
    x ∈ walkT W i slot stride d b := by
  simp only [walkT, hd, ↓reduceIte, List.mem_cons, List.mem_flatMap, List.mem_range]
  exact Or.inr ⟨j, hj, hx⟩

/-- **A walk reaches its tip**: the slot of step `2` holds chain `i` from the start, `3 - d` steps
from position `d`. -/
theorem walkT_sound {W : WotsT} {f : Nat → Nat → E → E} (hs : StepSound rd σ W f) {i : Nat}
    {slot : Nat → Nat} {stride d b : Nat} (hd : d ≤ 3) (h : AtomsHold rd σ (walkT W i slot stride d b)) :
    σ (.n (slot 2)) = chainT f i (3 - d) d (σ (walkStartV slot d b)) := by
  by_cases h3 : d = 3
  · subst h3; simp [walkStartV, chainT]
  · have key : ∀ j, j < 3 - d → σ (.n (slot (d + j))) = chainT f i (j + 1) d (σ (.n b)) := by
      intro j
      induction j with
      | zero =>
          intro hj
          have e := hs i (d + 0) _ _ _ (h.sub fun x hx => mem_walkT_step W h3 hj hx)
          simp only [↓reduceIte] at e
          rw [e]
          simp [chainT]
      | succ j ih =>
          intro hj
          have e := hs i (d + (j + 1)) _ _ _ (h.sub fun x hx => mem_walkT_step W h3 hj hx)
          simp only [show j + 1 ≠ 0 by omega, ↓reduceIte, show d + (j + 1) - 1 = d + j by omega] at e
          rw [e, ih (by omega), chainT_succ f i (j + 1) d]
    have := key (2 - d) (by omega)
    rw [show d + (2 - d) = 2 by omega, show 2 - d + 1 = 3 - d by omega] at this
    simpa [walkStartV, h3] using this

/-! ## Arms -/

/-- The base chain `r + j` walks from in `walksT` from chain `r` at base `b`. -/
def walkBase (stride k : Nat) : Nat → Nat → Nat → Nat
  | _, 0, b => b
  | r, j + 1, b => walkBase stride k (r + 1) j (b + walkSize stride (k / 4 ^ r % 4))

theorem mem_walksT (W : WotsT) (slots : Nat → Nat → Nat) (first k stride : Nat) :
    ∀ (m r b j : Nat), j < m → ∀ x ∈ walkT W (first + (r + j)) (slots (r + j)) stride
      (k / 4 ^ (r + j) % 4) (walkBase stride k r j b), x ∈ (walksT W slots first k stride m r b).1
  | 0, _, _, j, hj => absurd hj (by omega)
  | m + 1, r, b, 0, _ => fun x hx => by
      simp only [walksT, List.mem_append]
      exact Or.inl (by simpa [walkBase] using hx)
  | m + 1, r, b, j + 1, hj => fun x hx => by
      simp only [walksT, List.mem_append]
      refine Or.inr (mem_walksT W slots first k stride m (r + 1) _ j (by omega) x ?_)
      simpa [walkBase, show r + 1 + j = r + (j + 1) by omega] using hx

theorem word_two : word 2 0 = LeanVM.Protocol.Verifier.gen := by
  simp only [word, LeanVM.Protocol.Verifier.gen, LeanVM.Protocol.Verifier.eOfNat, Value.ofBits_zero]
  exact (ofK_eq_ofLimbs _).symm

theorem word_eq_eOfNat (n : Nat) : word n 0 = LeanVM.Protocol.Verifier.eOfNat n := by
  simp only [word, LeanVM.Protocol.Verifier.eOfNat, Value.ofBits_zero]
  exact (ofK_eq_ofLimbs _).symm

theorem word_zero : word 0 0 = 0 := by
  simp only [word, Value.ofBits_zero]
  exact Value.zero_eq_ofLimbs.symm

/-- The literal `lit c` is the 192-bit word of `c < 2^128`. -/
theorem lit_eq (c : Nat) (hc : c < 2 ^ 128) : lit c = Value.eOfNat192 c := by
  simp only [lit, word, Value.eOfNat192]
  rw [Nat.div_eq_of_lt (b := 2 ^ 128) hc, Nat.mod_eq_of_lt (a := c / 2 ^ 64) (by omega),
    Value.ofBits_mod]

/-- What arm `k` establishes, chain `r` starting at `start r`. -/
structure ArmOK (W : WotsT) (f : Nat → Nat → E → E) (σ : Val) (slots : Nat → Nat → Nat)
    (first n : Nat) (fold : Bool) (prodIn encIn prodOut encOut : V) (k : Nat)
    (start : Nat → V) : Prop where
  tip : ∀ r < n, σ (.n (slots r 2)) =
    chainT f (first + r) (3 - k / 4 ^ r % 4) (k / 4 ^ r % 4) (σ (start r))
  prod : σ prodOut = (if fold then 1 else σ prodIn) * σ (W.power (digitSum k n))
  enc : σ encOut = (if fold then 0 else σ encIn) + lit (W.enc first n k)

/-- The start of chain `r` in arm `k` from base `b`. -/
def armStart (W : WotsT) (slots : Nat → Nat → Nat) (fold : Bool) (k b r : Nat) : V :=
  walkStartV (slots r) (k / 4 ^ r % 4)
    (walkBase (if k = 0 then W.size + 1 else W.size) k 0 r (if fold then b + 1 else b))

/-- **An arm**: its walks reach their tips from their starts, the product and the encoding are
folded. -/
theorem armT_sound {W : WotsT} {f : Nat → Nat → E → E} (hs : StepSound rd σ W f)
    {slots : Nat → Nat → Nat} {first n : Nat} {fold : Bool} {prodIn encIn prodOut encOut : V}
    {k b : Nat} (h : AtomsHold rd σ (armT W slots first n fold prodIn encIn prodOut encOut k b).1) :
    ArmOK W f σ slots first n fold prodIn encIn prodOut encOut k (armStart W slots fold k b) := by
  have hws : AtomsHold rd σ (walksT W slots first k (if k = 0 then W.size + 1 else W.size) n 0
      (if fold then b + 1 else b)).1 := by
    refine h.sub fun x hx => ?_
    unfold armT
    by_cases hk : k = 0 <;> simp [hk] at hx ⊢ <;> simp [hx]
  refine ⟨fun r hr => ?_, ?_, ?_⟩
  · have := walkT_sound hs (Nat.le_of_lt_succ (Nat.mod_lt _ (by norm_num))) (hws.sub fun x hx =>
      mem_walksT W slots first k _ n 0 _ r hr x (by simpa using hx))
    simpa [armStart] using this
  · have hp : AtomsHold rd σ [if fold then copyS prodOut (W.power (digitSum k n))
        else mulS prodOut prodIn (W.power (digitSum k n))] := by
      refine h.sub fun x hx => ?_
      unfold armT
      simp only [List.mem_singleton] at hx
      subst hx
      split <;> simp
    cases fold
    · have := hp.atom (List.mem_singleton_self _)
      simpa [mulS, Atom.Holds] using this
    · have := hp.atom (List.mem_singleton_self _)
      simpa [copyS, Atom.Holds] using this
  · have hz : fold = true → σ (.n b) = 0 := by
      intro hf
      have hc : AtomsHold rd σ [cst b (word 0 0)] := by
        refine h.sub fun x hx => ?_
        unfold armT
        simp only [List.mem_singleton] at hx
        subst hx
        by_cases hk : k = 0 <;> simp [hk, hf]
      have := hc.atom (List.mem_singleton_self _)
      simpa [cst, Atom.Holds, word_zero] using this
    have henc0 : σ (if fold then V.n b else encIn) = if fold then 0 else σ encIn := by
      cases fold
      · rfl
      · simpa using hz rfl
    by_cases hk : k = 0
    · subst hk
      have he : AtomsHold rd σ [copyS encOut (if fold then V.n b else encIn)] := by
        refine h.sub fun x hx => ?_
        unfold armT
        simp only [List.mem_singleton] at hx
        subst hx
        simp
      have e := he.atom (List.mem_singleton_self _)
      simp only [Atom.Holds] at e
      have hl : lit (W.enc first n 0) = 0 := by simp [W.enc_zero, lit, word_zero]
      rw [e, hl, add_zero, henc0]
    · have he : AtomsHold rd σ
          [cst (walksT W slots first k W.size n 0 (if fold then b + 1 else b)).2 (lit (W.enc first n k)),
            addS encOut (if fold then V.n b else encIn)
              (.n (walksT W slots first k W.size n 0 (if fold then b + 1 else b)).2)] := by
        refine h.sub fun x hx => ?_
        unfold armT
        simp only [hk, ↓reduceIte, List.mem_append, List.mem_cons] at hx ⊢
        tauto
      have e1 := he.atom (List.mem_cons_self ..)
      have e2 := he.atom (List.mem_cons_of_mem _ (List.mem_singleton_self _))
      simp only [Atom.Holds] at e1 e2
      rw [e2, e1, henc0]

/-! ## Groups -/

/-- The step of a scheme is atoms. -/
def StepAtoms (W : WotsT) : Prop := ∀ i s v c o, atomsOnly (W.step i s v c o) = true

theorem atomsOnly_cons_atom (a : Atom) (ss : List Stmt) : atomsOnly (.atom a :: ss) = atomsOnly ss := rfl

theorem atomsOnly_flatMap {α : Type} (f : α → List Stmt) (hf : ∀ a, atomsOnly (f a) = true) :
    ∀ l : List α, atomsOnly (l.flatMap f) = true
  | [] => rfl
  | a :: l => by rw [List.flatMap_cons, atomsOnly_append, hf a, atomsOnly_flatMap f hf l]; rfl

theorem walkT_atoms {W : WotsT} (hW : StepAtoms W) (i : Nat) (slot : Nat → Nat) (stride d b : Nat) :
    atomsOnly (walkT W i slot stride d b) = true := by
  unfold walkT
  split
  · rfl
  · simp only [hintW, atomsOnly_cons_atom]
    exact atomsOnly_flatMap _ (fun j => hW _ _ _ _ _) _

theorem walksT_atoms {W : WotsT} (hW : StepAtoms W) (slots : Nat → Nat → Nat) (first k stride : Nat) :
    ∀ m r b, atomsOnly (walksT W slots first k stride m r b).1 = true
  | 0, _, _ => rfl
  | m + 1, r, b => by
      simp only [walksT, atomsOnly_append, walkT_atoms hW, walksT_atoms hW slots first k stride m,
        Bool.and_self]

theorem armT_atoms {W : WotsT} (hW : StepAtoms W) (slots : Nat → Nat → Nat) (first n : Nat)
    (fold : Bool) (prodIn encIn prodOut encOut : V) (k b : Nat) :
    atomsOnly (armT W slots first n fold prodIn encIn prodOut encOut k b).1 = true := by
  simp only [armT]
  split_ifs <;> simp [atomsOnly_append, walksT_atoms hW, atomsOnly, cst, copyS, mulS, addS]

/-- The base arm `k + j` of `armsT` starts from. -/
def armBase (W : WotsT) (slots : Nat → Nat → Nat) (first n : Nat) (fold : Bool)
    (prodIn encIn prodOut encOut : V) : Nat → Nat → Nat → Nat
  | _, 0, b => b
  | k, j + 1, b => armBase W slots first n fold prodIn encIn prodOut encOut (k + 1) j
      (if k = 0 then (armT W slots first n fold prodIn encIn prodOut encOut k b).2 + 2
        else (armT W slots first n fold prodIn encIn prodOut encOut k b).2)

theorem armsT_length (W : WotsT) (slots : Nat → Nat → Nat) (first n : Nat) (fold : Bool)
    (prodIn encIn prodOut encOut : V) :
    ∀ m k b, (armsT W slots first n fold prodIn encIn prodOut encOut m k b).1.length = m
  | 0, _, _ => rfl
  | m + 1, k, b => by simp [armsT, armsT_length W slots first n fold prodIn encIn prodOut encOut m]

theorem armsT_getElem (W : WotsT) (slots : Nat → Nat → Nat) (first n : Nat) (fold : Bool)
    (prodIn encIn prodOut encOut : V) :
    ∀ m k b j (hj : j < (armsT W slots first n fold prodIn encIn prodOut encOut m k b).1.length),
      (armsT W slots first n fold prodIn encIn prodOut encOut m k b).1[j] =
        (armT W slots first n fold prodIn encIn prodOut encOut (k + j)
          (armBase W slots first n fold prodIn encIn prodOut encOut k j b)).1
  | 0, _, _, j, hj => absurd hj (by simp [armsT])
  | m + 1, k, b, 0, _ => by simp [armsT, armBase]
  | m + 1, k, b, j + 1, hj => by
      simp only [armsT, List.getElem_cons_succ]
      rw [armsT_getElem W slots first n fold prodIn encIn prodOut encOut m (k + 1) _ j
        (by simp [armsT, armsT_length] at hj ⊢; omega)]
      simp only [armBase, show k + 1 + j = k + (j + 1) by omega]

/-- **A group's dispatch takes one arm**: the statements `pre` hold, and some `k < 4^n` is the
selector's exponent at `d` and arm `k`'s atoms hold, from its base. -/
theorem groupD_sound {W : WotsT} (hW : StepAtoms W) {first n : Nat} {fold : Bool} {prodIn encIn : V}
    {d : Nat} {pre : List Stmt} (hpre : atomsOnly pre = true) {b : Nat} {rest : List Stmt} {next : Prop}
    (h : Stmt.HoldsList C rd σ ((groupD W first n fold prodIn encIn d pre b).1 ++ rest) next kret) :
    Stmt.HoldsList C rd σ rest next kret ∧ AtomsHold rd σ pre ∧ ∃ k < 4 ^ n,
      σ (.n d) = ofK (addressOfIndex k) ∧
      AtomsHold rd σ (armT W (slotsT W fold b) first n fold prodIn encIn (prodT W fold n b)
        (encT W fold n b) k (armBase W (slotsT W fold b) first n fold prodIn encIn (prodT W fold n b)
          (encT W fold n b) 0 k (b + 6))).1 := by
  simp only [groupD, rangeS, List.cons_append, List.nil_append, List.append_assoc] at h
  have h1 := holdsList_split_atoms hpre h.2.2.2
  have hm : Stmt.Holds C rd σ (.match_ (.n d) _) (Stmt.HoldsList C rd σ rest next kret) kret :=
    h1.2.2
  rw [holds_match_iff] at hm
  obtain ⟨j, hj, hx, ha⟩ := hm
  simp only [groupArmsT] at hj ha
  rw [armsT_length] at hj
  rw [armsT_getElem] at ha
  simp only [Nat.zero_add] at ha
  have ha' := (holdsList_noRet _ (noRetList_of_atomsOnly (armT_atoms hW _ _ _ _ _ _ _ _ _ _)) _ _).mp ha
  exact ⟨ha'.2, atomsHold_of_holdsList hpre h1.1, j, hj, hx,
    atomsHold_of_holdsList (armT_atoms hW _ _ _ _ _ _ _ _ _ _) ha'.1⟩

/-- **A group's dispatch takes one arm**: some `k < 4^n` is the selector's exponent, and arm `k`'s
atoms hold, from its base. -/
theorem groupT_sound {W : WotsT} (hW : StepAtoms W) {first n : Nat} {fold : Bool} {prodIn encIn : V}
    {b : Nat} {rest : List Stmt} {next : Prop}
    (h : Stmt.HoldsList C rd σ ((groupT W first n fold prodIn encIn b).1 ++ rest) next kret) :
    Stmt.HoldsList C rd σ rest next kret ∧ ∃ k < 4 ^ n, σ (.n b) = ofK (addressOfIndex k) ∧
      AtomsHold rd σ (armT W (slotsT W fold b) first n fold prodIn encIn (prodT W fold n b)
        (encT W fold n b) k (armBase W (slotsT W fold b) first n fold prodIn encIn (prodT W fold n b)
          (encT W fold n b) 0 k (b + 6))).1 :=
  let r := groupD_sound (pre := []) hW rfl h
  ⟨r.1, r.2.2⟩

end
end LeanVM.Guest.B1.Sig
