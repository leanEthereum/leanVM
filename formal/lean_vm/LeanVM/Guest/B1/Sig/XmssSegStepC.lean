/-
  LeanVM.Guest.B1.Sig.XmssSegStepC

  leanXMSS's chain step inline in `__loop2`, for completeness: the step clamped to the chains,
  steps and powers the codeword uses, its reads below the codeword's base; a block completing
  inside another's range, and a `KECCAK` writing an earlier run.
-/

module

public import LeanVM.Guest.B1.Sig.XmssStep
public import LeanVM.Guest.B1.Sig.XmssSegT
public import LeanVM.Guest.B1.Sig.CompleteKit

/-!
# The chain step in `__loop2`, complete

* `sWc`: `sW` with its step's address, chain index and power clamped (`sW_weq`, `sW_power`), so
  that every value it reads lies below the codeword's digits;
* `SGood`: the values the step reads (`P`, the step addresses, the chain indices, the padding run
  and the powers `g^s`, `s < 13`); `sWc_shape`, `sWc_canon`, `sWc_sound`;
* `Completes.append_in`: a block, then one changing values in a range its predecessor does not
  read (a window's arm writes its output where arm `0` numbered it);
* `kecS_complete_at`, `k64_complete_at`: a `KECCAK` writing a run its inputs avoid.
-/

namespace LeanVM.Guest.B1.Sig

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Protocol.Verifier (gen)

@[expose] public section

variable {C : CallRel} {rd : Reader}

/-! ## The step, clamped -/

/-- **`sW` clamped**: the step's address, chain index and power clamped to the ones the codeword
uses. -/
def sWc (layer b : Nat) : WotsT where
  step i s v c o := k64 sLxPad sLxPP (.n (sA layer b + 2 * min s 2 + 1)) v (sTag (min i 57)) c o
  size := 1
  power j := sPower (min j 12)

theorem sW_weq (layer b : Nat) : WEq (sW layer b) (sWc layer b) 58 := by
  refine ⟨rfl, fun i hi s hs => ?_, fun j hj => ?_⟩
  · funext v c o
    simp only [sW, sWots, sWc, Nat.min_eq_left (show s ≤ 2 by omega),
      Nat.min_eq_left (show i ≤ 57 by omega)]
  · simp only [sW, sWots, sWc, Nat.min_eq_left (show j ≤ 12 by omega)]

theorem sW_power (layer b : Nat) {j : Nat} (hj : j ≤ 12) : (sW layer b).power j = (sWc layer b).power j := by
  simp only [sW, sWots, sWc, Nat.min_eq_left hj]

theorem sTag_nbB : ∀ i < 58, nbB 100 (sTag i) = true := by decide

theorem sTag_nb (i : Nat) : NBv 100 (sTag (min i 57)) :=
  nbB_ok (sTag_nbB _ (by have := Nat.min_le_right i 57; omega))

/-- The values leanXMSS's chain step reads in layer `layer` from base `b`. -/
def SGood (layer b : Nat) (σ : Val) : Prop :=
  IsCanonical128 (σ sLxPP) ∧ (∀ s < 3, IsCanonical128 (σ (.n (sA layer b + 2 * s + 1)))) ∧
    (∀ i < 58, IsCanonical128 (σ (sTag i))) ∧ PadOK σ sLxPad ∧ ∀ s < 13, σ (sPower s) = gen ^ s

theorem sWc_atoms (layer b : Nat) : StepAtoms (sWc layer b) := fun _ _ _ _ _ => rfl

theorem sWc_shape {layer b : Nat} (hB : 103 ≤ sA layer b) : StepShape (sWc layer b) (sA layer b + 6) := by
  intro i s v c o hc ho hco h1 h2
  have hs2 : min s 2 ≤ 2 := Nat.min_le_right _ _
  obtain ⟨jt, hjt, et⟩ := sTag_nb i
  refine ⟨k64_ssa hco (fun x hx => ?_) (Or.inl (by simp [sLxPad]; omega)), fun x hx => ?_, fun x hx => ?_⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · rintro ⟨j, hj, e⟩; simp only [sLxPP, V.mk.injEq, true_and] at e; omega
    · rintro ⟨j, hj, e⟩; simp only [V.mk.injEq, true_and] at e; omega
    · exact h2
    · rw [et]; rintro ⟨j, hj, e⟩; simp only [V.mk.injEq, true_and] at e; omega
  · change x ∈ outsList (k64 sLxPad sLxPP (.n (sA layer b + 2 * min s 2 + 1)) v (sTag (min i 57)) c o) at hx
    rw [k64_outs] at hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact Or.inl ⟨0, by simp [sWc], by simp⟩
    · exact Or.inr (mem_runV.mp hx)
  · rcases k64_vals _ _ _ _ _ c o hx with hx | rfl | ⟨k, hk, rfl⟩ | hx
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl
      · exact Or.inr (Or.inl ⟨66, by omega, rfl⟩)
      · exact Or.inr (Or.inl ⟨_, by omega, rfl⟩)
      · exact Or.inl rfl
      · exact Or.inr (Or.inl ⟨jt, by omega, et⟩)
    · exact Or.inr (Or.inr (Or.inl ⟨0, by simp [sWc], by simp⟩))
    · exact Or.inr (Or.inl ⟨_, by simp [sLxPad]; omega, rfl⟩)
    · exact Or.inr (Or.inr (Or.inr hx))

theorem sPower_nb (j : Nat) : NBv 88 (sPower (min j 12)) :=
  ⟨75 + min j 12, by have := Nat.min_le_right j 12; omega, rfl⟩

theorem sGood_congr {layer b : Nat} (hB : 103 ≤ sA layer b) {σ σ' : Val}
    (hσ : AgreeBelow (sA layer b + 6) σ σ') (h : SGood layer b σ) : SGood layer b σ' := by
  obtain ⟨g1, g2, g3, g4, g5⟩ := h
  refine ⟨by rw [show sLxPP = V.n 66 from rfl, hσ.apply ⟨66, by omega, rfl⟩]; exact g1, fun s hs => ?_, fun i hi => ?_,
    g4.congr (b := sA layer b + 6) (by simp [sLxPad]; omega) hσ, fun s hs => ?_⟩
  · rw [hσ.apply ⟨sA layer b + 2 * s + 1, by omega, rfl⟩]; exact g2 s hs
  · obtain ⟨j, hj, e⟩ := nbB_ok (sTag_nbB i hi)
    rw [e, hσ.apply ⟨j, by omega, rfl⟩, ← e]; exact g3 i hi
  · rw [show sPower s = V.n (75 + s) from rfl, hσ.apply ⟨75 + s, by omega, rfl⟩]; exact g5 s hs

theorem sWc_canon {layer b : Nat} (hB : 103 ≤ sA layer b) :
    StepCanon (sWc layer b) (sA layer b + 6) (SGood layer b) := by
  refine ⟨fun σ σ' hσ h => sGood_congr hB hσ h, fun i s v c o σ hc ho hco h1 h2 hg hv => ?_⟩
  obtain ⟨g1, g2, g3, g4, -⟩ := hg
  have hs2 : min s 2 < 3 := by have := Nat.min_le_right s 2; omega
  have hi57 : min i 57 < 58 := by have := Nat.min_le_right i 57; omega
  obtain ⟨jt, hjt, et⟩ := sTag_nb i
  refine k64_fwd_canon σ hco (fun x hx => ?_) (by simp [sLxPad]; omega) (by simp [sLxPad]; omega) g4
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
  have hv1 : v ≠ .n c := fun e => h1 ⟨0, by simp [sWc], by rw [e]; simp⟩
  rcases hx with rfl | rfl | rfl | rfl
  · exact ⟨by rintro ⟨j, hj, e⟩; simp only [sLxPP, V.mk.injEq, true_and] at e; omega,
      by simp only [sLxPP, ne_eq, V.mk.injEq, true_and]; omega, g1⟩
  · exact ⟨by rintro ⟨j, hj, e⟩; simp only [V.mk.injEq, true_and] at e; omega,
      by simp only [ne_eq, V.mk.injEq, true_and]; omega, g2 _ hs2⟩
  · exact ⟨h2, hv1, hv⟩
  · refine ⟨by rw [et]; rintro ⟨j, hj, e⟩; simp only [V.mk.injEq, true_and] at e; omega,
      by rw [et]; simp only [ne_eq, V.mk.injEq, true_and]; omega, g3 _ hi57⟩

theorem sWc_sound {layer b : Nat} {σ : Val} (hg : SGood layer b σ) :
    StepSound rd σ (sWc layer b)
      (fun i s y => (hcell [σ sLxPP, σ (.n (sA layer b + 2 * min s 2 + 1)), y, σ (sTag (min i 57))]).1) := by
  intro i s v c o h
  exact k64_sound hg.2.2.2.1 h

theorem sWc_pow {layer b : Nat} {σ : Val} (hg : SGood layer b σ) :
    ∀ s < 13, σ ((sWc layer b).power s) = gen ^ s := by
  intro s hs
  simp only [sWc, Nat.min_eq_left (show s ≤ 12 by omega)]
  exact hg.2.2.2.2 s hs

theorem sWc_pw (layer b : Nat) (hB : 103 ≤ sA layer b) : ∀ j, NBv (sA layer b + 6) ((sWc layer b).power j) :=
  fun j => (sPower_nb j).mono' (by omega)

/-! ## A block inside another's range -/

/-- **Completeness in sequence, the second block inside the range**: a first block completing on
`lo ..< m`, then one changing only `lo2 ..< hi2` inside `lo ..< hi`, values the first does not
read. -/
theorem Completes.append_in {lo m hi lo2 hi2 : Nat} {xs ys : List Stmt} {σ : Val} {P Q : Val → Prop}
    (hlo : lo ≤ lo2) (hhi2 : hi2 ≤ hi) (hm : m ≤ hi)
    (hxs : ∀ v ∈ Stmt.valsList xs, ∀ k, lo2 ≤ k → k < hi2 → v ≠ .n k)
    (h1 : Completes C rd lo m xs σ P) (h2 : ∀ σ', Ext lo m σ σ' → P σ' → Completes C rd lo2 hi2 ys σ' Q) :
    Completes C rd lo hi (xs ++ ys) σ Q := by
  obtain ⟨σ1, he1, hp1, hh1⟩ := h1
  obtain ⟨σ2, he2, hq2, hh2⟩ := h2 σ1 he1 hp1
  refine ⟨σ2, fun v hv => ?_, hq2, fun next kret hn => ?_⟩
  · rw [he2 v (fun k h1 h2 => hv k (by omega) (by omega)), he1 v (fun k h1 h2 => hv k h1 (by omega))]
  · rw [holdsList_append]
    exact (holdsList_congr xs (fun v hv => (he2 v (hxs v hv)).symm) _ _).mp (hh1 _ kret (hh2 next kret hn))

/-! ## A `KECCAK` writing an earlier run -/

/-- **A `KECCAK` completes** writing the run of its `n` outputs (one, two or thirteen) at `o`, its
inputs off the run. -/
theorem kecS_complete_at (σ : Val) {ins : List V} (o : Nat) {n : Nat} (hn : n = 1 ∨ n = 2 ∨ n = 13)
    (hl : ins.length = 13) (hin : ∀ v ∈ ins, ¬ InR o n v)
    (hc : ∀ c : Fin 13, IsCanonical128 (cells13 (ins.map σ) c)) (inOdd outOdd : Bool) :
    Completes C rd o (o + n) [kecS ins (runV o n) inOdd outOdd] σ
      (fun σ' => ∀ c < n, σ' (.n (o + c)) = kOut (ins.map σ) inOdd outOdd c) := by
  obtain ⟨oc, rfl⟩ := exists_cellCount hn
  have hins : ins.map (updRun σ o oc.cellCount (kOut (ins.map σ) inOdd outOdd)) = ins.map σ :=
    List.map_congr_left fun v hv => (updRun_ext σ o _ _) v (fun k h1 h2 e => hin v hv ⟨k - o,
      by omega, by rw [e]; congr 1; omega⟩)
  refine completes_atoms rfl (updRun_ext σ o _ _) (fun c hc => updRun_at σ o _ _ hc)
    (fun a ha => ?_)
  simp only [kecS, List.mem_singleton, Stmt.atom.injEq] at ha
  subst ha
  refine ⟨hl, oc, by simp [runV], ?_⟩
  rw [hins]
  refine ⟨hc, fun c hco => ?_⟩
  simp only [cells13, runV, List.map_map, List.getD_eq_getElem?_getD, List.getElem?_map,
    List.getElem?_range hco, Option.map_some, Option.getD_some, Function.comp]
  rw [updRun_at σ o _ _ hco, kOut]
  simp [c.isLt]

/-- **A 64-byte `keccak` completes writing the run at `o`**, below its constant or right after it,
its inputs canonical, below its constant and off the run: its constant's range `c ..< c + 1` and
the run's inside `lo ..< hi`. -/
theorem k64_complete_at {pad : Nat} {m0 m1 m2 m3 : V} {c o lo hi : Nat} (σ : Val) (hp : PadOK σ pad)
    (hpc : pad + 5 ≤ lo) (hlc : lo ≤ c) (hch : c + 1 ≤ hi) (hlo : lo ≤ o) (hoh : o + 1 ≤ hi)
    (hco : c + 1 ≤ o ∨ o + 1 ≤ c)
    (hm : ∀ v ∈ [m0, m1, m2, m3], NBv c v ∧ ¬ InR o 1 v ∧ IsCanonical128 (σ v)) :
    Completes C rd lo hi (k64 pad m0 m1 m2 m3 c o) σ
      (fun σ' => σ' (.n o) = (hcell [σ m0, σ m1, σ m2, σ m3]).1 ∧
        IsCanonical128 (σ' (.n o))) := by
  have hmc : ∀ v ∈ [m0, m1, m2, m3], v ≠ .n c := fun v hv e => by
    obtain ⟨⟨j, hj, rfl⟩, -⟩ := hm v hv
    simp only [V.mk.injEq, true_and] at e
    omega
  have hcr : ¬ InR o 1 (.n c) := by
    rintro ⟨j, hj, e⟩; simp only [V.mk.injEq, true_and] at e; omega
  obtain ⟨σ1, he1, hp1, hh1⟩ := cst_complete (C := C) (rd := rd) σ c (word (2 ^ 63) 0)
  have hσ1 : ∀ v, v ≠ .n c → σ1 v = σ v := fun v hv => he1 v (fun k h1 h2 e => hv (by rw [e]; congr 1; omega))
  have hin : ∀ v ∈ [m0, m1, m2, m3, .n pad, .n (pad + 1), .n (pad + 2), .n (pad + 3), .n c, .n (pad + 1),
      .n (pad + 2), .n (pad + 3), .n (pad + 4)], ¬ InR o 1 v := by
    intro v hv
    rcases (k64_ins pad m0 m1 m2 m3 c v).mp hv with h | rfl | ⟨k, hk, rfl⟩
    · exact (hm v h).2.1
    · exact hcr
    · rintro ⟨j, hj, e⟩; simp only [V.mk.injEq, true_and] at e; omega
  obtain ⟨q0, q1, q2, q3, q4⟩ := hp
  have hpk : ∀ k < 5, σ1 (.n (pad + k)) = σ (.n (pad + k)) := fun k hk =>
    hσ1 _ (by simp only [ne_eq, V.mk.injEq, true_and]; omega)
  have p0 := hpk 0 (by norm_num)
  have p1 := hpk 1 (by norm_num)
  have p2 := hpk 2 (by norm_num)
  have p3 := hpk 3 (by norm_num)
  have p4 := hpk 4 (by norm_num)
  simp only [Nat.add_zero] at p0
  have h4 : ∀ v ∈ [m0, m1, m2, m3], IsCanonical128 (σ1 v) := fun v hv => by
    rw [hσ1 v (hmc v hv)]; exact (hm v hv).2.2
  have hcan : ∀ cc : Fin 13, IsCanonical128 (cells13 ([m0, m1, m2, m3, .n pad, .n (pad + 1), .n (pad + 2),
      .n (pad + 3), .n c, .n (pad + 1), .n (pad + 2), .n (pad + 3), .n (pad + 4)].map σ1) cc) := by
    intro cc
    fin_cases cc <;> simp [cells13, q0, q1, q2, q3, q4, p0, p1, p2, p3, p4, hp1] <;>
      first | exact h4 _ (by simp) | exact canon_word _ _
  obtain ⟨σ2, he2, hp2, hh2⟩ := kecS_complete_at (C := C) (rd := rd) σ1 o (.inl rfl) rfl hin hcan false false
  have hσ2 : ∀ v, ¬ InR o 1 v → σ2 v = σ1 v := fun v hv => he2 v (fun k h1 h2 e => hv ⟨k - o, by omega,
    by rw [e]; congr 1; omega⟩)
  have hc2 : σ2 (.n c) = σ1 (.n c) := hσ2 _ hcr
  have hhold : ∀ next kret, next → Stmt.HoldsList C rd σ2 (k64 pad m0 m1 m2 m3 c o) next kret := by
    intro next kret hn
    rw [k64_vals_eq, holdsList_append]
    refine (holdsList_congr [cst c (word (2 ^ 63) 0)] (fun v hv => ?_) _ _).mp (hh1 _ kret (hh2 next kret hn))
    simp only [cst, valsList_cons, valsList_nil, Stmt.vals, Atom.vals, List.append_nil,
      List.mem_singleton] at hv
    subst hv
    exact hc2.symm
  refine ⟨σ2, fun v hv => ?_, ⟨?_, ?_⟩, hhold⟩
  · rw [he2 v (fun k h1 h2 => hv k (by omega) (by omega)), he1 v (fun k h1 h2 => hv k (by omega) (by omega))]
  · have hk := k64_sound (rd := rd) (σ := σ2) (pad := pad) (m0 := m0) (m1 := m1) (m2 := m2) (m3 := m3)
      (c := c) (o := o) ⟨by rw [hσ2 _ (hin _ (by simp)), p0]; exact q0,
        by rw [hσ2 _ (hin _ (by simp)), p1]; exact q1, by rw [hσ2 _ (hin _ (by simp)), p2]; exact q2,
        by rw [hσ2 _ (hin _ (by simp)), p3]; exact q3, by rw [hσ2 _ (hin _ (by simp)), p4]; exact q4⟩
      (atomsHold_of_holdsList rfl (hhold True (fun _ => True) trivial))
    rw [hk]
    have e : ∀ v ∈ [m0, m1, m2, m3], σ2 v = σ v := fun v hv => by
      rw [hσ2 v (hm v hv).2.1, hσ1 v (hmc v hv)]
    rw [e m0 (by simp), e m1 (by simp), e m2 (by simp), e m3 (by simp)]
  · have := hp2 0 (by norm_num)
    rw [Nat.add_zero] at this
    rw [this]
    exact canon_kOut _ _ _ _

end
end LeanVM.Guest.B1.Sig
