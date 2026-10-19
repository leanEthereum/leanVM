/-
  LeanVM.Guest.B1.Tables.FlockCRounds

  `verify_flock`'s sumcheck rounds, complete: the interpolation's scaling, the seven fixed rounds
  and the lincheck's eight.
-/

module

public import LeanVM.Guest.B1.Tables.FlockCBody
public import LeanVM.Guest.B1.Sig.Steps

/-!
# The rounds, complete

`c_p5`: the interpolation scaled, the zerocheck's starting claim. `c_fr`: fixed round `i`
(`frBlk`) from the claim and state of `scSt` after `i` rounds to those after `i + 1`, its
challenge checked against `zerocheck_chis`. `c_lc`: lincheck round `i` (`lcBlk`) likewise for
`lcSt`, its challenge checked against `lincheck_rs`.
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Protocol LeanVM.Protocol.Blake2sHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Guest.B1.VerifySub LeanVM.Guest.B1.Sig

@[expose] public section

section
variable {rd : Reader} {τ : ℕ} {cv : Digest} {xs : List E} {cur zchis lrs zpart p11 p24 p40 p2220 : E}

theorem upd_ne {σ : Val} {k j : ℕ} {e : E} (h : j ≠ k) : Function.update σ (.n k) e (.n j) = σ (.n j) :=
  Function.update_of_ne (by simp only [ne_eq, V.mk.injEq, true_and]; exact h) _ _

theorem upd_eq {σ : Val} {k : ℕ} {e : E} : Function.update σ (.n k) e (.n k) = e := by simp

/-- The invariant of the fixed rounds before round `i`. -/
def FrInv (τ : ℕ) (cv : Digest) (xs : List E) (cur zchis p11 : E) (i : ℕ) (σ : Val) : Prop :=
  Fixes σ [(2, cur), (4, zchis), (11, p11)] ∧ σ (.n (frC i)) = (flScAt τ cv xs i).1 ∧
    (σ (.n (frS i)), σ (.n (frS i + 1))) = digestScalars (flScAt τ cv xs i).2

theorem fr_below : ∀ i < 7,
    numBelowB (frB i + 16) (Stmt.valsList
      (fsNextT (.n (frS i)) (.n (frS i + 1)) (.n 2) (64 + 2 * i) (frB i + 1))) = true ∧
    numBelowB (frB i + 31) (Stmt.valsList
      (fsNextT (.n (frB i + 14)) (.n (frB i + 15)) (.n 2) (65 + 2 * i) (frB i + 16))) = true ∧
    numBelowB (frB i + 48) (Stmt.valsList (squeezeT (.n (frB i + 29)) (.n (frB i + 30)) (frB i + 34))) =
      true ∧ frS i + 1 < frB i ∧ frC i < frB i ∧
    numBelowB (frB i + 34) (Stmt.valsList [.atom (.add (.n (frB i + 31)) (.n (frB i + 1)) (.n (frB i + 16))),
      .atom (.mul (.n (frB i + 32)) (.n (frB i)) (.n (frB i + 31))),
      .atom (.add (.n (frB i + 33)) (.n (frC i)) (.n (frB i + 32)))]) = true := by
  decide +kernel

/-- **Fixed round `i`** (G:1879-1886). -/
theorem c_fr (hM : FlMem rd τ cv xs cur zchis lrs zpart p11 p24 p40 p2220) (hτ : τ < 29) {i : ℕ}
    (hi : i < 7) (σ : Val) (hI : FrInv τ cv xs cur zchis p11 i σ) :
    Completes (coreProgram.Rel rd) rd (frB i) (frB (i + 1)) (frBlk i) σ
      (FrInv τ cv xs cur zchis p11 (i + 1)) := by
  obtain ⟨hF, hc, hs⟩ := hI
  obtain ⟨b1, b2, b3, hsB, hcB, b4⟩ := fr_below i hi
  have h2 : σ (.n 2) = cur := hF.get (k := 2) (e := cur) (by simp)
  have h4 : σ (.n 4) = zchis := hF.get (k := 4) (e := zchis) (by simp)
  have h11 : σ (.n 11) = p11 := hF.get (k := 11) (e := p11) (by simp)
  have hB1 : frB (i + 1) = frB i + 52 := by simp [frB]; ring
  have h11B : 11 < frB i := by simp [frB]; omega
  rw [hB1]
  simp only [frBlk, List.append_assoc]
  rw [List.cons_append]
  set B := frB i with hB
  set st := flScAt τ cv xs i
  set g1 := xs.getD (64 + 2 * i) 0
  set g2 := xs.getD (65 + 2 * i) 0
  set e := flE τ cv i
  set cv2 := obsCv st.2 g1
  set cv3 := obsCv cv2 g2
  set ch := challengeOf (sqCv cv3)
  refine Completes.atom_cons e (by omega) (NumBelow.cons ⟨B, by omega, rfl⟩
    (NumBelow.cons ⟨11, by omega, rfl⟩ (NumBelow.nil _))) ?_ ?_
  · show LoadHolds rd (Function.update σ (.n B) e (.n 11)) (6 + i) (Function.update σ (.n B) e (.n B))
    rw [upd_ne (by omega), upd_eq, h11]; exact hM.zr i (by omega)
  set σ1 := Function.update σ (.n B) e
  have k1 : ∀ j < B, σ1 (.n j) = σ (.n j) := fun j hj => upd_ne (by omega)
  refine Completes.append (m := B + 16) (by omega) (by omega) (numBelow_of_B b1)
    (completes_fsNextT (x := g1) (cv := st.2) ⟨_, by omega, rfl⟩ ⟨_, by omega, rfl⟩
      ⟨2, by omega, rfl⟩ (by rw [k1 _ (by omega), k1 _ (by omega)]; exact hs)
      (by rw [k1 _ (by omega), h2]; exact hM.words _ (by unfold flLen; omega))
      (Post := fun σ' => Ext (B + 1) (B + 16) σ1 σ' ∧ σ' (.n (B + 1)) = g1 ∧
        (σ' (.n (B + 1 + 13)), σ' (.n (B + 1 + 14))) = digestScalars cv2)
      fun σ' he hb ho => ⟨he, hb, ho⟩) fun σ2 _ ⟨he2, hg1, ho2⟩ => ?_
  refine Completes.append (m := B + 31) (by omega) (by omega) (numBelow_of_B b2)
    (completes_fsNextT (x := g2) (cv := cv2) ⟨_, by omega, rfl⟩ ⟨_, by omega, rfl⟩
      ⟨2, by omega, rfl⟩ (by rw [show B + 14 = B + 1 + 13 by ring, show B + 15 = B + 1 + 14 by ring]; exact ho2)
      (by rw [he2.apply (Or.inl (by omega)), k1 _ (by omega), h2]; exact hM.words _ (by unfold flLen; omega))
      (Post := fun σ' => Ext (B + 16) (B + 31) σ2 σ' ∧ σ' (.n (B + 16)) = g2 ∧
        (σ' (.n (B + 16 + 13)), σ' (.n (B + 16 + 14))) = digestScalars cv3)
      fun σ' he hb ho => ⟨he, hb, ho⟩) fun σ3 _ ⟨he3, hg2, ho3⟩ => ?_
  have a3 : ∀ j < B + 1, σ3 (.n j) = σ1 (.n j) := fun j hj => by
    rw [he3.apply (Or.inl (by omega)), he2.apply (Or.inl (by omega))]
  have f1 : σ3 (.n (B + 1)) = g1 := by rw [he3.apply (Or.inl (by omega))]; exact hg1
  have fB : σ3 (.n B) = e := by rw [a3 B (by omega)]; simp [σ1]
  have fC : σ3 (.n (frC i)) = st.1 := by rw [a3 _ (by omega), k1 _ hcB, hc]
  have f4 : σ3 (.n 4) = zchis := by rw [a3 _ (by omega), k1 _ (by omega), h4]
  have hs3 : (σ3 (.n (B + 29)), σ3 (.n (B + 30))) = digestScalars cv3 := by
    rw [show B + 29 = B + 16 + 13 by ring, show B + 30 = B + 16 + 14 by ring]; exact ho3
  set l1 : List (ℕ × E) := [(B + 31, g1 + g2), (B + 32, e * (g1 + g2)), (B + 33, st.1 + e * (g1 + g2))]
  have r1 : ∀ p ∈ l1, B + 31 ≤ p.1 ∧ p.1 < B + 34 := by
    simp only [l1, List.mem_cons, List.not_mem_nil, or_false]
    rintro p (rfl | rfl | rfl) <;> simp
  have u1 : ∀ j < B + 31, upds σ3 l1 (.n j) = σ3 (.n j) := fun j hj =>
    upds_of_not_mem σ3 _ fun p hp => by
      have := r1 p hp; simp only [ne_eq, V.mk.injEq, true_and]; omega
  refine Completes.append (m := B + 34) (by omega) (by omega)
    (numBelow_of_B b4)
    (completes_upds l1 r1 (fun next kret hn => ?_) (Post := fun σ' => σ' = upds σ3 l1) rfl)
    fun σ4 _ hσ4 => ?_
  · simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds]
    rw [u1 (B + 1) (by omega), u1 (B + 16) (by omega), u1 B (by omega), u1 (frC i) (by omega), f1,
      hg2, fB, fC]
    simp only [l1]
    fl_ev
    exact ⟨trivial, trivial, trivial, hn⟩
  subst hσ4
  refine Completes.append (m := B + 48) (by omega) (by omega) (numBelow_of_B b3)
    (completes_squeezeT (cv := cv3) ⟨_, by omega, rfl⟩ ⟨_, by omega, rfl⟩
      (by rw [u1 (B + 29) (by omega), u1 (B + 30) (by omega)]; exact hs3)
      (Post := fun σ' => Ext (B + 34) (B + 48) (upds σ3 l1) σ' ∧
        (σ' (.n (B + 34 + 5)), σ' (.n (B + 34 + 6))) = digestScalars (sqCv cv3) ∧
        σ' (.n (B + 34 + 13)) = ch) fun σ' he h1 h2 => ⟨he, h1, h2⟩) fun σ5 _ ⟨he5, hs5, hch⟩ => ?_
  have a5 : ∀ j < B + 31, σ5 (.n j) = σ3 (.n j) := fun j hj => by
    rw [he5.apply (Or.inl (by omega)), u1 j hj]
  have f33 : σ5 (.n (B + 33)) = st.1 + e * (g1 + g2) := by
    rw [he5.apply (Or.inl (by omega))]; simp only [l1]; fl_ev
  set l2 : List (ℕ × E) := [(B + 48, ch * g2), (B + 49, g1 + ch * g2), (B + 50, ch * (g1 + ch * g2)),
    (B + 51, st.1 + e * (g1 + g2) + ch * (g1 + ch * g2))]
  have r2 : ∀ p ∈ l2, B + 48 ≤ p.1 ∧ p.1 < B + 52 := by
    simp only [l2, List.mem_cons, List.not_mem_nil, or_false]
    rintro p (rfl | rfl | rfl | rfl) <;> simp
  have u2 : ∀ j < B + 48, upds σ5 l2 (.n j) = σ5 (.n j) := fun j hj =>
    upds_of_not_mem σ5 _ fun p hp => by
      have := r2 p hp; simp only [ne_eq, V.mk.injEq, true_and]; omega
  refine completes_upds l2 r2 (fun next kret hn => ?_) ⟨fun p hp => ?_, ?_, ?_⟩
  · simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds]
    rw [u2 4 (by omega), u2 (B + 47) (by omega), u2 (B + 16) (by omega), u2 (B + 1) (by omega),
      u2 (B + 33) (by omega), a5 4 (by omega), a5 (B + 16) (by omega), a5 (B + 1) (by omega),
      show B + 47 = B + 34 + 13 by ring, hch, f1, hg2, f4, f33]
    simp only [l2]
    fl_ev
    exact ⟨hM.chis i (by omega), trivial, trivial, trivial, trivial, hn⟩
  · have hp' : p.1 < 12 := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl | rfl <;> simp
    rw [u2 _ (by omega), a5 _ (by omega), a3 _ (by omega), k1 _ (by omega)]
    exact hF p hp
  · rw [show frC (i + 1) = B + 51 by simp [frC, hB, frB]; omega]
    simp only [l2]
    fl_ev
    rfl
  · rw [show frS (i + 1) = B + 39 by simp [frS, hB, frB]; omega, u2 _ (by omega), u2 _ (by omega),
      show B + 39 = B + 34 + 5 by ring, show B + 34 + 5 + 1 = B + 34 + 6 by ring]
    exact hs5

/-! ## The lincheck's rounds -/

/-- The lincheck's state after `j` rounds. -/
abbrev flLcAt (τ : ℕ) (cv : Digest) (xs : List E) (j : ℕ) : E × Digest :=
  lcSt (flG' τ xs) (flSt0' τ cv xs) j

/-- The invariant of the lincheck before round `i`. -/
def LcInv (τ : ℕ) (cv : Digest) (xs : List E) (cur lrs : E) (i : ℕ) (σ : Val) : Prop :=
  Fixes σ [(5, lrs), (2240, cur * gen ^ (64 + 2 * (τ + 8)))] ∧ σ (.n (lcC i)) = (flLcAt τ cv xs i).1 ∧
    (σ (.n (lcS i)), σ (.n (lcS i + 1))) = digestScalars (flLcAt τ cv xs i).2

theorem lc_below : ∀ i < 8,
    numBelowB (lcB i + 15) (Stmt.valsList
      (fsNextT (.n (lcS i)) (.n (lcS i + 1)) (.n 2240) (2 + 2 * i) (lcB i))) = true ∧
    numBelowB (lcB i + 30) (Stmt.valsList
      (fsNextT (.n (lcB i + 13)) (.n (lcB i + 14)) (.n 2240) (3 + 2 * i) (lcB i + 15))) = true ∧
    numBelowB (lcB i + 45) (Stmt.valsList (squeezeT (.n (lcB i + 28)) (.n (lcB i + 29)) (lcB i + 31))) =
      true ∧ lcS i + 1 < lcB i ∧ lcC i < lcB i ∧ 2240 < lcB i ∧
    numBelowB (lcB i + 31) (Stmt.valsList [.atom (.add (.n (lcB i + 30)) (.n (lcC i)) (.n (lcB i + 15)))]) =
      true := by
  decide +kernel

/-- **Lincheck round `i`** (G:1931-1937). -/
theorem c_lc (hM : FlMem rd τ cv xs cur zchis lrs zpart p11 p24 p40 p2220) {i : ℕ}
    (hi : i < 8) (σ : Val) (hI : LcInv τ cv xs cur lrs i σ) :
    Completes (coreProgram.Rel rd) rd (lcB i) (lcB (i + 1)) (lcBlk i) σ (LcInv τ cv xs cur lrs (i + 1)) := by
  obtain ⟨hF, hc, hs⟩ := hI
  obtain ⟨b1, b2, b3, hsB, hcB, hCB, b4⟩ := lc_below i hi
  have h5 : σ (.n 5) = lrs := hF.get (k := 5) (e := lrs) (by simp)
  have hcu : σ (.n 2240) = cur * gen ^ (64 + 2 * (τ + 8)) :=
    hF.get (k := 2240) (e := cur * gen ^ (64 + 2 * (τ + 8))) (by simp)
  have hB1 : lcB (i + 1) = lcB i + 49 := by simp [lcB]; ring
  rw [hB1]
  simp only [lcBlk, List.append_assoc]
  set B := lcB i with hB
  set st := flLcAt τ cv xs i
  set g1 := xs.getD (66 + 2 * (τ + 8) + 2 * i) 0
  set g2 := xs.getD (67 + 2 * (τ + 8) + 2 * i) 0
  set cv2 := obsCv st.2 g1
  set cv3 := obsCv cv2 g2
  set r := challengeOf (sqCv cv3)
  refine Completes.append (m := B + 15) (by omega) (by omega) (numBelow_of_B b1)
    (completes_fsNextT (x := g1) (cv := st.2) ⟨_, by omega, rfl⟩ ⟨_, by omega, rfl⟩
      ⟨2240, by omega, rfl⟩ hs
      (by rw [hcu]; exact lh_back (hM.words _ (by unfold flLen; omega)) (by omega))
      (Post := fun σ' => Ext B (B + 15) σ σ' ∧ σ' (.n B) = g1 ∧
        (σ' (.n (B + 13)), σ' (.n (B + 14))) = digestScalars cv2)
      fun σ' he hb ho => ⟨he, hb, ho⟩) fun σ2 _ ⟨he2, hg1, ho2⟩ => ?_
  refine Completes.append (m := B + 30) (by omega) (by omega) (numBelow_of_B b2)
    (completes_fsNextT (x := g2) (cv := cv2) ⟨_, by omega, rfl⟩ ⟨_, by omega, rfl⟩
      ⟨2240, by omega, rfl⟩ ho2
      (by rw [he2.apply (Or.inl (by omega)), hcu]; exact lh_back (hM.words _ (by unfold flLen; omega)) (by omega))
      (Post := fun σ' => Ext (B + 15) (B + 30) σ2 σ' ∧ σ' (.n (B + 15)) = g2 ∧
        (σ' (.n (B + 15 + 13)), σ' (.n (B + 15 + 14))) = digestScalars cv3)
      fun σ' he hb ho => ⟨he, hb, ho⟩) fun σ3 _ ⟨he3, hg2, ho3⟩ => ?_
  have a3 : ∀ j < B, σ3 (.n j) = σ (.n j) := fun j hj => by
    rw [he3.apply (Or.inl (by omega)), he2.apply (Or.inl (by omega))]
  have f1 : σ3 (.n B) = g1 := by rw [he3.apply (Or.inl (by omega))]; exact hg1
  have fC : σ3 (.n (lcC i)) = st.1 := by rw [a3 _ hcB, hc]
  have f5 : σ3 (.n 5) = lrs := by rw [a3 _ (by omega), h5]
  have hs3 : (σ3 (.n (B + 28)), σ3 (.n (B + 29))) = digestScalars cv3 := by
    rw [show B + 28 = B + 15 + 13 by ring, show B + 29 = B + 15 + 14 by ring]; exact ho3
  set l1 : List (ℕ × E) := [(B + 30, st.1 + g2)]
  have r1 : ∀ p ∈ l1, B + 30 ≤ p.1 ∧ p.1 < B + 31 := by simp [l1]
  have u1 : ∀ j < B + 30, upds σ3 l1 (.n j) = σ3 (.n j) := fun j hj =>
    upds_of_not_mem σ3 _ fun p hp => by
      have := r1 p hp; simp only [ne_eq, V.mk.injEq, true_and]; omega
  refine Completes.append (m := B + 31) (by omega) (by omega) (numBelow_of_B b4)
    (completes_upds l1 r1 (fun next kret hn => ?_) (Post := fun σ' => σ' = upds σ3 l1) rfl)
    fun σ4 _ hσ4 => ?_
  · simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds]
    rw [u1 (B + 15) (by omega), u1 (lcC i) (by omega), hg2, fC]
    simp only [l1]
    fl_ev
    exact ⟨trivial, hn⟩
  subst hσ4
  refine Completes.append (m := B + 45) (by omega) (by omega) (numBelow_of_B b3)
    (completes_squeezeT (cv := cv3) ⟨_, by omega, rfl⟩ ⟨_, by omega, rfl⟩
      (by rw [u1 (B + 28) (by omega), u1 (B + 29) (by omega)]; exact hs3)
      (Post := fun σ' => Ext (B + 31) (B + 45) (upds σ3 l1) σ' ∧
        (σ' (.n (B + 31 + 5)), σ' (.n (B + 31 + 6))) = digestScalars (sqCv cv3) ∧
        σ' (.n (B + 31 + 13)) = r) fun σ' he h1 h2 => ⟨he, h1, h2⟩) fun σ5 _ ⟨he5, hs5, hch⟩ => ?_
  have a5 : ∀ j < B + 30, σ5 (.n j) = σ3 (.n j) := fun j hj => by
    rw [he5.apply (Or.inl (by omega)), u1 j hj]
  have f30 : σ5 (.n (B + 30)) = st.1 + g2 := by
    rw [he5.apply (Or.inl (by omega))]; simp only [l1]; fl_ev
  set l2 : List (ℕ × E) := [(B + 45, r * g2), (B + 46, st.1 + g2 + r * g2),
    (B + 47, r * (st.1 + g2 + r * g2)), (B + 48, g1 + r * (st.1 + g2 + r * g2))]
  have r2 : ∀ p ∈ l2, B + 45 ≤ p.1 ∧ p.1 < B + 49 := by
    simp only [l2, List.mem_cons, List.not_mem_nil, or_false]
    rintro p (rfl | rfl | rfl | rfl) <;> simp
  have u2 : ∀ j < B + 45, upds σ5 l2 (.n j) = σ5 (.n j) := fun j hj =>
    upds_of_not_mem σ5 _ fun p hp => by
      have := r2 p hp; simp only [ne_eq, V.mk.injEq, true_and]; omega
  refine completes_upds l2 r2 (fun next kret hn => ?_) ⟨fun p hp => ?_, ?_, ?_⟩
  · simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds]
    rw [u2 5 (by omega), u2 (B + 44) (by omega), u2 (B + 15) (by omega), u2 (B + 30) (by omega),
      u2 B (by omega), a5 5 (by omega), a5 (B + 15) (by omega), a5 B (by omega),
      show B + 44 = B + 31 + 13 by ring, hch, f1, hg2, f5, f30]
    simp only [l2]
    fl_ev
    exact ⟨hM.rcs i hi, trivial, trivial, trivial, trivial, hn⟩
  · have hp' : p.1 < 2241 := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl <;> simp
    rw [u2 _ (by omega), a5 _ (by omega), a3 _ (by omega)]
    exact hF p hp
  · rw [show lcC (i + 1) = B + 48 by simp [lcC, hB, lcB]; omega]
    simp only [l2]
    fl_ev
    rfl
  · rw [show lcS (i + 1) = B + 36 by simp [lcS, hB, lcB]; omega, u2 _ (by omega), u2 _ (by omega),
      show B + 36 = B + 31 + 5 by ring, show B + 31 + 5 + 1 = B + 31 + 6 by ring]
    exact hs5

end

end
end LeanVM.Guest.B1
