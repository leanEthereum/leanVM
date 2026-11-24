/-
  LeanVM.Guest.B1.Sig.XmssSegStepC

  leanXMSS's chain step inline in `main_loop2`, for completeness: the step clamped to the chains,
  steps and powers the codeword uses, its reads below the codeword's base; a block completing
  inside another's range, and a `KECCAK` writing an earlier run.
-/

module

public import LeanVM.Guest.B1.Sig.XmssStep
public import LeanVM.Guest.B1.Sig.XmssSegT
public import LeanVM.Guest.B1.Sig.CompleteKit
import LeanVM.Guest.ValRef
import LeanVM.Guest.Data.ValNames.«main_loop2»

/-!
# The chain step in `main_loop2`, complete

* `sWc`: `sW` with its step's address, chain index and power clamped (`sW_weq`, `sW_power`), so
  that every value it reads lies below the codeword's digits;
* `SGood`: the values the step reads that its proofs need (the padding run and the powers `g^s`,
  `s < 13`); `sWc_shape`, `sGood_stable`, `sWc_sound`;
* `kecS_complete_at`: a `KECCAK` writing a run its inputs avoid.
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

theorem sTag_nb (i : Nat) : NBv (val% «main_loop2» "s3.i3:verify_lean_xmss.s7.u0.s3.t.s0#6[2]") (sTag (min i 57)) :=
  nbB_ok (sTag_nbB _ (by have := Nat.min_le_right i 57; omega))

/-- The values leanXMSS's chain step reads in layer `layer` from base `b` that its proofs need: the
padding run and the powers. -/
def SGood (_layer _b : Nat) (σ : Val) : Prop :=
  PadOK σ sLxPad ∧ ∀ s < 13, σ (sPower s) = gen ^ s

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

theorem sPower_nb (j : Nat) : NBv (val% «main_loop2» "rho@1") (sPower (min j 12)) :=
  ⟨75 + min j 12, by have := Nat.min_le_right j 12; omega, rfl⟩

theorem sGood_congr {layer b : Nat} (hB : 103 ≤ sA layer b) {σ σ' : Val}
    (hσ : AgreeBelow (sA layer b + 6) σ σ') (h : SGood layer b σ) : SGood layer b σ' := by
  obtain ⟨g4, g5⟩ := h
  refine ⟨g4.congr (b := sA layer b + 6) (by simp [sLxPad]; omega) hσ, fun s hs => ?_⟩
  rw [show sPower s = V.n (75 + s) from rfl, hσ.apply ⟨75 + s, by omega, rfl⟩]; exact g5 s hs

theorem sGood_stable {layer b : Nat} (hB : 103 ≤ sA layer b) :
    GoodStable (sA layer b + 6) (SGood layer b) :=
  fun _ _ hσ h => sGood_congr hB hσ h

theorem sWc_sound {layer b : Nat} {σ : Val} (hg : SGood layer b σ) :
    StepSound rd σ (sWc layer b)
      (fun i s y => (hcell [σ sLxPP, σ (.n (sA layer b + 2 * min s 2 + 1)), y, σ (sTag (min i 57))]).1) := by
  intro i s v c o h
  exact k64_sound hg.1 h

theorem sWc_pow {layer b : Nat} {σ : Val} (hg : SGood layer b σ) :
    ∀ s < 13, σ ((sWc layer b).power s) = gen ^ s := by
  intro s hs
  simp only [sWc, Nat.min_eq_left (show s ≤ 12 by omega)]
  exact hg.2 s hs

theorem sWc_pw (layer b : Nat) (hB : 103 ≤ sA layer b) : ∀ j, NBv (sA layer b + 6) ((sWc layer b).power j) :=
  fun j => (sPower_nb j).mono' (by omega)

/-! ## A `KECCAK` writing an earlier run -/

/-- **A `KECCAK` completes** writing the run of its `n` outputs (one, two or thirteen) at `o`, its
inputs off the run. -/
theorem kecS_complete_at (σ : Val) {ins : List V} (o : Nat) {n : Nat} (hn : n = 1 ∨ n = 2 ∨ n = 13)
    (hl : ins.length = 13) (hin : ∀ v ∈ ins, ¬ InR o n v) (inOdd outOdd : Bool) :
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
  intro c hco
  simp only [cells13, runV, List.map_map, List.getD_eq_getElem?_getD, List.getElem?_map,
    List.getElem?_range hco, Option.map_some, Option.getD_some, Function.comp]
  rw [updRun_at σ o _ _ hco, kOut]
  simp [c.isLt]

end
end LeanVM.Guest.B1.Sig
