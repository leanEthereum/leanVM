/-
  LeanVM.Guest.B1.Sig.XmssSegArms

  The codeword of the leanXMSS check in `main_loop2` (`lean_ethereum.py:3654-3674`), sound: its
  fifteen dispatches each take one arm, and the arms' walks, products and encodings give the chains'
  tips, the target sum and the digest's first cell.
-/

module

public import LeanVM.Guest.B1.Sig.XmssSegT

/-!
# The codeword's groups of four, sound

* `armM_sound`: arm `k` of a group (`armM`) walks its chains from their starts and folds the digit
  sum into the product, `k`'s own `n` digits into the encoding (`ArmOKM`);
* `armsM_getElem`: arm `k` of `armsM` is `armM … k` from `armBaseM … k`;
* `sSt`: group `p`'s running product, encoding and virtual base; `sGroupsT_sound`: each of the
  groups' dispatches takes an arm `k < 256` (`GroupOKM`);
* `sCodewordT_sound`: with group `p`'s arm `sK p`, each chain's tip (`sTip`) is its chain from its
  start (`sStart`) at digit `lxDigit sK i`, the digits sum to the target in the exponent, and the
  digest's first cell is their base-4 number.
-/

namespace LeanVM.Guest.B1.Sig

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Protocol.Verifier

@[expose] public section

variable {C : CallRel} {rd : Reader} {σ : Val} {kret : List E → Prop}

/-! ## An arm -/

/-- What arm `k` of a group establishes: `ArmOK` with the encoding of `k`'s own `n` digits. -/
structure ArmOKM (W : WotsT) (f : Nat → Nat → E → E) (σ : Val) (slots : Nat → Nat → Nat)
    (first n : Nat) (fold : Bool) (prodIn encIn prodOut encOut : V) (k : Nat)
    (start : Nat → V) : Prop where
  tip : ∀ r < n, σ (.n (slots r 2)) =
    chainT f (first + r) (3 - k / 4 ^ r % 4) (k / 4 ^ r % 4) (σ (start r))
  prod : σ prodOut = (if fold then 1 else σ prodIn) * σ (W.power (digitSum k n))
  enc : σ encOut = (if fold then 0 else σ encIn) + lit (W.enc first n (k % 4 ^ n))

theorem armM_atoms {W : WotsT} (hW : StepAtoms W) (slots : Nat → Nat → Nat) (first n : Nat)
    (fold : Bool) (prodIn encIn prodOut encOut : V) (k b : Nat) :
    atomsOnly (armM W slots first n fold prodIn encIn prodOut encOut k b).1 = true := by
  simp only [armM]
  split_ifs <;> simp [atomsOnly_append, walksT_atoms hW, atomsOnly, cst, copyS, mulS, addS]

/-- **An arm of a group of `main_loop2`'s codeword**: its walks reach their tips from their starts,
the product and the encoding are folded. -/
theorem armM_sound {W : WotsT} {f : Nat → Nat → E → E} (hs : StepSound rd σ W f)
    {slots : Nat → Nat → Nat} {first n : Nat} {fold : Bool} {prodIn encIn prodOut encOut : V}
    {k b : Nat} (h : AtomsHold rd σ (armM W slots first n fold prodIn encIn prodOut encOut k b).1) :
    ArmOKM W f σ slots first n fold prodIn encIn prodOut encOut k (armStart W slots fold k b) := by
  have hws : AtomsHold rd σ (walksT W slots first k (if k = 0 then W.size + 1 else W.size) n 0
      (if fold then b + 1 else b)).1 := by
    refine h.sub fun x hx => ?_
    unfold armM
    by_cases hk : k % 4 ^ n = 0 <;> simp [hk] at hx ⊢ <;> simp [hx]
  refine ⟨fun r hr => ?_, ?_, ?_⟩
  · have := walkT_sound hs (Nat.le_of_lt_succ (Nat.mod_lt _ (by norm_num))) (hws.sub fun x hx =>
      mem_walksT W slots first k _ n 0 _ r hr x (by simpa using hx))
    simpa [armStart] using this
  · have hp : AtomsHold rd σ [if fold then copyS prodOut (W.power (digitSum k n))
        else mulS prodOut prodIn (W.power (digitSum k n))] := by
      refine h.sub fun x hx => ?_
      unfold armM
      simp only [List.mem_singleton] at hx
      subst hx
      by_cases hk : k % 4 ^ n = 0 <;> simp [hk]
    cases fold
    · have := hp.atom (List.mem_singleton_self _)
      simpa [mulS, Atom.Holds] using this
    · have := hp.atom (List.mem_singleton_self _)
      simpa [copyS, Atom.Holds] using this
  · have hz : fold = true → σ (.n b) = 0 := by
      intro hf
      have hc : AtomsHold rd σ [cst b (word 0 0)] := by
        refine h.sub fun x hx => ?_
        unfold armM
        simp only [List.mem_singleton] at hx
        subst hx
        by_cases hk : k % 4 ^ n = 0 <;> simp [hk, hf]
      have := hc.atom (List.mem_singleton_self _)
      simpa [cst, Atom.Holds, word_zero] using this
    have henc0 : σ (if fold then V.n b else encIn) = if fold then 0 else σ encIn := by
      cases fold
      · rfl
      · simpa using hz rfl
    by_cases hk : k % 4 ^ n = 0
    · have he : AtomsHold rd σ [copyS encOut (if fold then V.n b else encIn)] := by
        refine h.sub fun x hx => ?_
        unfold armM
        simp only [List.mem_singleton] at hx
        subst hx
        simp [hk]
      have e := he.atom (List.mem_singleton_self _)
      simp only [Atom.Holds] at e
      have hl : lit (W.enc first n (k % 4 ^ n)) = 0 := by simp [hk, W.enc_zero, lit, word_zero]
      rw [e, hl, add_zero, henc0]
    · have he : AtomsHold rd σ
          [cst (walksT W slots first k (if k = 0 then W.size + 1 else W.size) n 0
              (if fold then b + 1 else b)).2 (lit (W.enc first n (k % 4 ^ n))),
            addS encOut (if fold then V.n b else encIn)
              (.n (walksT W slots first k (if k = 0 then W.size + 1 else W.size) n 0
                (if fold then b + 1 else b)).2)] := by
        refine h.sub fun x hx => ?_
        unfold armM
        simp only [hk, ↓reduceIte, List.mem_append, List.mem_cons] at hx ⊢
        tauto
      have e1 := he.atom (List.mem_cons_self ..)
      have e2 := he.atom (List.mem_cons_of_mem _ (List.mem_singleton_self _))
      simp only [Atom.Holds] at e1 e2
      rw [e2, e1, henc0]

/-! ## The arms of a dispatch -/

/-- The base arm `k + j` of `armsM` starts from. -/
def armBaseM (W : WotsT) (slots : Nat → Nat → Nat) (first n : Nat) (fold : Bool)
    (prodIn encIn prodOut encOut : V) : Nat → Nat → Nat → Nat
  | _, 0, b => b
  | k, j + 1, b => armBaseM W slots first n fold prodIn encIn prodOut encOut (k + 1) j
      (if k = 0 then (armM W slots first n fold prodIn encIn prodOut encOut k b).2 + 2
        else (armM W slots first n fold prodIn encIn prodOut encOut k b).2)

theorem armsM_length (W : WotsT) (slots : Nat → Nat → Nat) (first n : Nat) (fold : Bool)
    (prodIn encIn prodOut encOut : V) :
    ∀ m k b, (armsM W slots first n fold prodIn encIn prodOut encOut m k b).1.length = m
  | 0, _, _ => rfl
  | m + 1, k, b => by simp [armsM, armsM_length W slots first n fold prodIn encIn prodOut encOut m]

theorem armsM_getElem (W : WotsT) (slots : Nat → Nat → Nat) (first n : Nat) (fold : Bool)
    (prodIn encIn prodOut encOut : V) :
    ∀ m k b j (hj : j < (armsM W slots first n fold prodIn encIn prodOut encOut m k b).1.length),
      (armsM W slots first n fold prodIn encIn prodOut encOut m k b).1[j] =
        (armM W slots first n fold prodIn encIn prodOut encOut (k + j)
          (armBaseM W slots first n fold prodIn encIn prodOut encOut k j b)).1
  | 0, _, _, j, hj => absurd hj (by simp [armsM])
  | m + 1, k, b, 0, _ => by simp [armsM, armBaseM]
  | m + 1, k, b, j + 1, hj => by
      simp only [armsM, List.getElem_cons_succ]
      rw [armsM_getElem W slots first n fold prodIn encIn prodOut encOut m (k + 1) _ j
        (by simp [armsM, armsM_length] at hj ⊢; omega)]
      simp only [armBaseM, show k + 1 + j = k + (j + 1) by omega]

/-! ## The groups -/

/-- Group `p`'s running product and encoding cells and its virtual base, the groups from `vb0`. -/
def sSt (W : WotsT) (vb0 : Nat) : Nat → V × V × Nat
  | 0 => (.n 0, .n 0, vb0)
  | p + 1 =>
      let st := sSt W vb0 p
      (prodT W (p == 0) (lxN p) st.2.2, encT W (p == 0) (lxN p) st.2.2,
        (sGroupArms W p st.1 st.2.1 st.2.2).2 - 6)

/-- Group `p`'s arm `k`, from its base. -/
def sArm (W : WotsT) (vb0 p k : Nat) : List Stmt × Nat :=
  armM W (slotsT W (p == 0) (sSt W vb0 p).2.2) (4 * p) (lxN p) (p == 0) (sSt W vb0 p).1
    (sSt W vb0 p).2.1 (prodT W (p == 0) (lxN p) (sSt W vb0 p).2.2)
    (encT W (p == 0) (lxN p) (sSt W vb0 p).2.2) k
    (armBaseM W (slotsT W (p == 0) (sSt W vb0 p).2.2) (4 * p) (lxN p) (p == 0) (sSt W vb0 p).1
      (sSt W vb0 p).2.1 (prodT W (p == 0) (lxN p) (sSt W vb0 p).2.2)
      (encT W (p == 0) (lxN p) (sSt W vb0 p).2.2) 0 k ((sSt W vb0 p).2.2 + 6))

/-- What group `p`'s dispatch establishes: its digit word `g^k`, `k < 256`, and arm `k`'s atoms. -/
def GroupOKM (rd : Reader) (σ : Val) (W : WotsT) (dg vb0 p : Nat) : Prop :=
  ∃ k < 256, σ (.n (dg + p)) = ofK (addressOfIndex k) ∧ AtomsHold rd σ (sArm W vb0 p k).1

theorem sGroupsT_eq (W : WotsT) (dg vb0 : Nat) : ∀ (m p : Nat),
    (sGroupsT W dg m p (sSt W vb0 p).1 (sSt W vb0 p).2.1 (sSt W vb0 p).2.2).2 =
      ((sSt W vb0 (p + m)).2.2, (List.range m).flatMap (fun j => (List.range (lxN (p + j))).map fun r =>
        V.n (slotsT W (p + j == 0) (sSt W vb0 (p + j)).2.2 r 2)),
        (sSt W vb0 (p + m)).1, (sSt W vb0 (p + m)).2.1)
  | 0, p => rfl
  | m + 1, p => by
      have ih := sGroupsT_eq W dg vb0 m (p + 1)
      have e : (sGroupsT W dg m (p + 1) (prodT W (p == 0) (lxN p) (sSt W vb0 p).2.2)
          (encT W (p == 0) (lxN p) (sSt W vb0 p).2.2)
          ((sGroupArms W p (sSt W vb0 p).1 (sSt W vb0 p).2.1 (sSt W vb0 p).2.2).2 - 6)).2 =
          ((sSt W vb0 (p + 1 + m)).2.2, (List.range m).flatMap (fun j => (List.range (lxN (p + 1 + j))).map
            fun r => V.n (slotsT W (p + 1 + j == 0) (sSt W vb0 (p + 1 + j)).2.2 r 2)),
            (sSt W vb0 (p + 1 + m)).1, (sSt W vb0 (p + 1 + m)).2.1) := ih
      simp only [sGroupsT]
      rw [e, show p + 1 + m = p + (m + 1) by omega]
      simp only [Prod.mk.injEq, true_and, and_true]
      rw [List.range_succ_eq_map (n := m), List.flatMap_cons, List.flatMap_map]
      simp only [Nat.add_zero]
      refine congrArg (_ ++ ·) (List.flatMap_congr fun j _ => ?_)
      simp only [Nat.succ_eq_add_one, show p + 1 + j = p + (j + 1) by omega]

theorem sGroupsT_sound {W : WotsT} (hW : StepAtoms W) (dg vb0 : Nat) {rest : List Stmt} {next : Prop} :
    ∀ (m p : Nat),
    Stmt.HoldsList C rd σ ((sGroupsT W dg m p (sSt W vb0 p).1 (sSt W vb0 p).2.1
      (sSt W vb0 p).2.2).1 ++ rest) next kret →
      Stmt.HoldsList C rd σ rest next kret ∧ ∀ j < m, GroupOKM rd σ W dg vb0 (p + j)
  | 0, p, h => ⟨by simpa [sGroupsT] using h, fun j hj => absurd hj (by omega)⟩
  | m + 1, p, h => by
      simp only [sGroupsT, List.cons_append, Stmt.HoldsList] at h
      rw [holds_match_iff] at h
      obtain ⟨j, hj, hx, ha⟩ := h
      simp only [sGroupArms] at hj ha
      rw [armsM_length] at hj
      rw [armsM_getElem] at ha
      simp only [Nat.zero_add] at ha
      have ha' := (holdsList_noRet _ (noRetList_of_atomsOnly (armM_atoms hW _ _ _ _ _ _ _ _ _ _)) _ _).mp ha
      have ih := sGroupsT_sound hW dg vb0 m (p + 1) (by simpa only [sSt, sGroupArms] using ha'.2)
      refine ⟨ih.1, fun i hi => ?_⟩
      rcases i with _ | i
      · exact ⟨j, hj, hx, atomsHold_of_holdsList (armM_atoms hW _ _ _ _ _ _ _ _ _ _) ha'.1⟩
      · have := ih.2 i (by omega)
        rwa [show p + 1 + i = p + (i + 1) by omega] at this

/-! ## The codeword's values -/

/-- The arm group `p`'s dispatch takes: its digit word's exponent. -/
noncomputable def sK (σ : Val) (dg p : Nat) : Nat := logG (σ (.n (dg + p))) 256

/-- **Chain `i`'s tip**: the slot of its last step. -/
def sTip (W : WotsT) (vb0 i : Nat) : V :=
  .n (slotsT W (i / 4 == 0) (sSt W vb0 (i / 4)).2.2 (i % 4) 2)

/-- **Chain `i`'s start**: the value its walk hints, in the arm its group's dispatch takes. -/
noncomputable def sStart (W : WotsT) (σ : Val) (dg vb0 i : Nat) : V :=
  armStart W (slotsT W (i / 4 == 0) (sSt W vb0 (i / 4)).2.2) (i / 4 == 0) (sK σ dg (i / 4))
    (armBaseM W (slotsT W (i / 4 == 0) (sSt W vb0 (i / 4)).2.2) (4 * (i / 4)) (lxN (i / 4))
      (i / 4 == 0) (sSt W vb0 (i / 4)).1 (sSt W vb0 (i / 4)).2.1
      (prodT W (i / 4 == 0) (lxN (i / 4)) (sSt W vb0 (i / 4)).2.2)
      (encT W (i / 4 == 0) (lxN (i / 4)) (sSt W vb0 (i / 4)).2.2) 0 (sK σ dg (i / 4))
      ((sSt W vb0 (i / 4)).2.2 + 6)) (i % 4)

theorem sDigitChecks_atoms (dg : Nat) : atomsOnly (sDigitChecks dg) = true :=
  atomsOnly_flatMap _ (fun _ => rfl) _

/-- **The codeword of `main_loop2`, sound.** With the digits `lxDigit (sK σ dg)` its dispatches
choose, each chain's tip is its chain from its start, the digits sum to the target in the exponent,
and the digest's first cell is their base-4 number. -/
theorem sCodewordT_sound {W : WotsT} (hW : StepAtoms W) {f : Nat → Nat → E → E}
    (hs : StepSound rd σ W f) (hpow : ∀ s < 13, σ (W.power s) = gen ^ s) {target : E} {d0 : V}
    {dg : Nat} {rest : List Stmt} {next : Prop}
    (h : Stmt.HoldsList C rd σ ((sCodewordT W target d0 dg).1 ++ rest) next kret)
    (hE : ∀ first n k, W.enc first n k = k * 4 ^ first := by intros; rfl) :
    Stmt.HoldsList C rd σ rest next kret ∧
      (∀ i < 58, σ (sTip W (dg + 70) i) = chainT f i (3 - lxDigit (sK σ dg) i) (lxDigit (sK σ dg) i)
          (σ (sStart W σ dg (dg + 70) i))) ∧
      gen ^ (∑ i ∈ Finset.range 58, lxDigit (sK σ dg) i) = target ∧
      σ d0 = lit (∑ i ∈ Finset.range 58, lxDigit (sK σ dg) i * 4 ^ i) := by
  have hgs := sGroupsT_eq W dg (dg + 70) 15 0
  simp only [Nat.zero_add] at hgs
  have hgs' : (sGroupsT W dg 15 0 (.n 0) (.n 0) (dg + 70)).2 = _ := hgs
  simp only [sCodewordT, List.append_assoc] at h
  rw [hgs'] at h
  have h0 := holdsList_split_atoms (xs := [hintW "lx_digits" (runV dg 15)] ++ sDigitChecks dg ++
    [cst (dg + 75) closeLane]) (by
      rw [atomsOnly_append, atomsOnly_append, sDigitChecks_atoms]; rfl) (by
      simpa only [List.append_assoc] using h)
  obtain ⟨h1, hg⟩ := sGroupsT_sound (rd := rd) (σ := σ) (C := C) (kret := kret) hW dg (dg + 70) 15 0
    h0.2
  have hc := h1
  simp only [List.cons_append, List.nil_append, Stmt.HoldsList] at hc
  have e1 : σ d0 = σ (sSt W (dg + 70) 15).2.1 := hc.1
  have e2 := hc.2.1
  have e3 := hc.2.2.1
  simp only [Atom.Holds] at e2 e3
  have hprod : σ (sSt W (dg + 70) 15).1 = target := by
    rw [← e2]; exact (Value.e_add_eq_zero_iff).mp e3
  -- the arms taken
  set K := sK σ dg with hKdef
  have hK : ∀ p < 15, K p < 256 ∧ AtomsHold rd σ (sArm W (dg + 70) p (K p)).1 := by
    intro p hp
    obtain ⟨k, hk, hx, ha⟩ := hg p hp
    simp only [Nat.zero_add] at hx ha
    have e : K p = k := logG_eq hk (by norm_num) hx
    rw [e]
    exact ⟨hk, ha⟩
  have harm : ∀ p < 15, ArmOKM W f σ (slotsT W (p == 0) (sSt W (dg + 70) p).2.2) (4 * p) (lxN p)
      (p == 0) (sSt W (dg + 70) p).1 (sSt W (dg + 70) p).2.1
      (prodT W (p == 0) (lxN p) (sSt W (dg + 70) p).2.2)
      (encT W (p == 0) (lxN p) (sSt W (dg + 70) p).2.2) (K p)
      (armStart W (slotsT W (p == 0) (sSt W (dg + 70) p).2.2) (p == 0) (K p)
        (armBaseM W (slotsT W (p == 0) (sSt W (dg + 70) p).2.2) (4 * p) (lxN p) (p == 0)
          (sSt W (dg + 70) p).1 (sSt W (dg + 70) p).2.1
          (prodT W (p == 0) (lxN p) (sSt W (dg + 70) p).2.2)
          (encT W (p == 0) (lxN p) (sSt W (dg + 70) p).2.2) 0 (K p) ((sSt W (dg + 70) p).2.2 + 6))) :=
    fun p hp => armM_sound hs (hK p hp).2
  have hN : ∀ p, lxN p ≤ 4 := fun p => by unfold lxN; split <;> omega
  refine ⟨hc.2.2.2, fun i hi => ?_, ?_, ?_⟩
  · -- the tips
    have hp : i / 4 < 15 := by omega
    have hr : i % 4 < lxN (i / 4) := by
      unfold lxN; split
      · omega
      · omega
    have := (harm (i / 4) hp).tip (i % 4) hr
    rw [show 4 * (i / 4) + i % 4 = i by omega] at this
    exact this
  · -- the product
    have hpr : ∀ p < 15, σ (sSt W (dg + 70) (p + 1)).1 =
        gen ^ (∑ q ∈ Finset.range (p + 1), digitSum (K q) (lxN q)) := by
      intro p hp
      have hle : ∀ q, digitSum (K q) (lxN q) < 13 := fun q => by
        have := lx_digitSum_le (K q) (lxN q); have := hN q; omega
      induction p with
      | zero =>
          have := (harm 0 (by omega)).prod
          simp only [sSt, beq_self_eq_true, ↓reduceIte, one_mul] at this ⊢
          rw [this, hpow _ (hle 0)]
          simp
      | succ p ih =>
          have := (harm (p + 1) (by omega)).prod
          simp only [Nat.add_one_ne_zero, beq_iff_eq, ↓reduceIte] at this
          show σ (prodT W (p + 1 == 0) (lxN (p + 1)) (sSt W (dg + 70) (p + 1)).2.2) = _
          rw [this, hpow _ (hle _), Finset.sum_range_succ (n := p + 1), pow_add, ← ih (by omega)]
    rw [← hprod, hpr 14 (by omega), lx_digitSum_total]
  · -- the encoding
    have hen : ∀ p < 15, σ (sSt W (dg + 70) (p + 1)).2.1 =
        lit (∑ q ∈ Finset.range (p + 1), lxEncTerm K q) := by
      intro p hp
      induction p with
      | zero =>
          have := (harm 0 (by omega)).enc
          rw [hE] at this
          simp only [sSt, beq_self_eq_true, ↓reduceIte, zero_add] at this ⊢
          rw [this]
          simp [lxEncTerm]
      | succ p ih =>
          have := (harm (p + 1) (by omega)).enc
          rw [hE] at this
          simp only [Nat.add_one_ne_zero, beq_iff_eq, ↓reduceIte] at this
          show σ (encT W (p + 1 == 0) (lxN (p + 1)) (sSt W (dg + 70) (p + 1)).2.2) = _
          rw [this, ih (by omega), ← lx_enc_step K hp]
          rfl
    rw [e1, hen 14 (by omega), lx_enc_total]

end
end LeanVM.Guest.B1.Sig
