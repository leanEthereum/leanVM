/-
  LeanVM.Guest.B1.VsC.KLPack

  `keccak_layer`'s pack section, completely: its atoms hold and its two dispatches are taken.
-/

module

public import LeanVM.Guest.B1.KeccakGkr.LayerSecB
public import LeanVM.Guest.B1.VsC.KLBlock
import LeanVM.Guest.ValRef
import LeanVM.Guest.Data.ValNames.«keccak_layer__L»

/-!
# The pack section, completely

`pack_complete`: on an evaluated valuation, the claim's point pointer in its record, `step_g` and
`rem_g` powers of `g` below the dispatches' sizes, the pack section (`packT o`) holds under any call
relation that holds of its two dispatched calls; its values are the point pointer, the oracle's
words (the point's base, the dispatches' returns, the local point's base) and their products with
`step_g^16`.
-/

namespace LeanVM.Guest.B1.VerifySub.KL

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Guest.B1.Fwd

@[expose] public section

variable {C : CallRel} {rd : Reader} {S : List Atom} {w : ℕ → E} {σ : Val}

theorem good_of_mem {s : Stmt} {B : List Stmt} (hg : ∀ s ∈ B, GoodS rd S w σ s) (h : s ∈ B) :
    GoodS rd S w σ s := hg s h

set_option maxRecDepth 4000 in
/-- **The pack section, completely.** -/
theorem pack_complete {o : ℕ} (ho : 20 ≤ o + 20) (hg : ∀ s ∈ packT o, GoodS rd S w σ s)
    (hS : Atom.load (.n (o + 781)) (.n (valf% «keccak_layer» "claim")) 2 ∉ S) {pp : E}
    (hpp : LoadHolds rd (σ (.n (valf% «keccak_layer» "claim"))) 2 pp)
    {j1 j2 : ℕ} (hj1 : j1 < 2) (hx1 : σ (.n (valf% «keccak_layer» "step_g")) = gen ^ j1)
    (hj2 : j2 < 16) (hx2 : σ (.n (valf% «keccak_layer» "rem_g")) = gen ^ j2)
    (hc1 : C (stepNames.getD j1 "") ((cap5 (o + 539)).map σ ++
          [σ (.n (valf% «keccak_layer» "cursor@1")) * gen ^ 48, σ (.n (o + 780)), pp,
            w (o + 782), σ (.n (valf% «keccak_layer» "tabs"))])
          ((List.range 7).map fun k ↦ w (o + 785 + k)))
    (hc2 : C (remNames.getD j2 "") (((List.range 7).map fun k ↦ w (o + 785 + k)) ++
          [pp * gen ^ (krStep * j1), w (o + 782) * gen ^ (krStep * j1),
            σ (.n (valf% «keccak_layer» "tabs"))])
          ((List.range 7).map fun k ↦ w (o + 798 + k))) :
    σ (.n (o + 781)) = pp ∧ σ (.n (o + 782)) = w (o + 782) ∧
      σ (.n (o + 784)) = σ (.n (valf% «keccak_layer» "cursor@1")) * gen ^ 48 ∧
      (∀ k < 7, σ (.n (o + 785 + k)) = w (o + 785 + k)) ∧
      σ (.n (o + 796)) = pp * gen ^ (krStep * j1) ∧
      σ (.n (o + 797)) = w (o + 782) * gen ^ (krStep * j1) ∧
      (∀ k < 7, σ (.n (o + 798 + k)) = w (o + 798 + k)) ∧
      (∀ j < 5, σ (.n (o + 805 + j)) = w (o + 798 + j)) ∧ σ (.n (o + 810)) = w (o + 810) ∧
      ∀ {next : Prop} {kret : List E → Prop}, next → Stmt.HoldsList C rd σ (packT o) next kret := by
  have hm : ∀ s, s ∈ packT o → GoodS rd S w σ s := hg
  have g781 : Good rd S w σ (.load (.n (o + 781)) (.n (valf% «keccak_layer» "claim")) 2) :=
    hm (.atom (.load (.n (o + 781)) (.n (valf% «keccak_layer» "claim")) 2)) (by simp [packT])
  have e781 : σ (.n (o + 781)) = pp := load_val g781 hS hpp
  have e782 : σ (.n (o + 782)) = w (o + 782) :=
    hm (.atom (.hint (.allocDyn (.n (o + 782)) (.n (valf% «keccak_layer» "y_g"))))) (by simp [packT])
  have e783 : σ (.n (o + 783)) = word 281474976710656 0 :=
    hm (.atom (.const (.n (o + 783)) (word 281474976710656 0))) (by simp [packT])
  have e784 := mul_good (d := o + 784) (x := valf% «keccak_layer» "cursor@1") (y := o + 783)
    (by omega) (by omega) (hm _ (by simp [packT]))
  have r1 : ∀ v ∈ (List.range 7).map (fun k ↦ V.n (o + 785 + k)), σ v = w v.idx :=
    hm (.dispatch (.n (valf% «keccak_layer» "step_g")) stepNames
      ((cap5 (o + 539)) ++ [.n (o + 784), .n (o + 780), .n (o + 781), .n (o + 782),
        .n (valf% «keccak_layer» "tabs")]) ((List.range 7).map fun k ↦ .n (o + 785 + k)))
      (by simp [packT])
  have e785 : ∀ k < 7, σ (.n (o + 785 + k)) = w (o + 785 + k) := fun k hk ↦
    r1 _ (List.mem_map.mpr ⟨k, List.mem_range.mpr hk, rfl⟩)
  have e792 := mul_good (d := o + 792) (x := valf% «keccak_layer» "step_g")
    (y := valf% «keccak_layer» "step_g") (by omega) (by omega) (hm _ (by simp [packT]))
  have e793 := mul_good (d := o + 793) (x := o + 792) (y := o + 792) (by omega) (by omega)
    (hm _ (by simp [packT]))
  have e794 := mul_good (d := o + 794) (x := o + 793) (y := o + 793) (by omega) (by omega)
    (hm _ (by simp [packT]))
  have e795 := mul_good (d := o + 795) (x := o + 794) (y := o + 794) (by omega) (by omega)
    (hm _ (by simp [packT]))
  have e796 := mul_good (d := o + 796) (x := o + 781) (y := o + 795) (by omega) (by omega)
    (hm _ (by simp [packT]))
  have e797 := mul_good (d := o + 797) (x := o + 782) (y := o + 795) (by omega) (by omega)
    (hm _ (by simp [packT]))
  have r2 : ∀ v ∈ (List.range 7).map (fun k ↦ V.n (o + 798 + k)), σ v = w v.idx :=
    hm (.dispatch (.n (valf% «keccak_layer» "rem_g")) remNames
      (((List.range 7).map fun k ↦ .n (o + 785 + k)) ++ [.n (o + 796), .n (o + 797),
        .n (valf% «keccak_layer» "tabs")]) ((List.range 7).map fun k ↦ .n (o + 798 + k)))
      (by simp [packT])
  have e798 : ∀ k < 7, σ (.n (o + 798 + k)) = w (o + 798 + k) := fun k hk ↦
    r2 _ (List.mem_map.mpr ⟨k, List.mem_range.mpr hk, rfl⟩)
  have ecp : ∀ j < 5, σ (.n (o + 805 + j)) = σ (.n (o + 798 + j)) := fun j hj ↦
    hm (.atom (.copy (.n (o + 805 + j)) (.n (o + 798 + j)))) (by
      simp only [packT, List.mem_append, List.mem_map, List.mem_range]
      exact Or.inl (Or.inr ⟨j, hj, rfl⟩))
  have e810 : σ (.n (o + 810)) = w (o + 810) :=
    hm (.atom (.hint (.alloc (.n (o + 810)) 11))) (by simp [packT])
  have h16 : σ (.n (o + 795)) = gen ^ (krStep * j1) := by
    rw [e795, e794, e793, e792, hx1, krStep, pow_mul]; ring
  refine ⟨e781, e782, by rw [e784, e783, gen48], e785, by rw [e796, e781, h16],
    by rw [e797, e782, h16], e798, fun j hj ↦ by rw [ecp j hj, e798 j (by omega)], e810,
    fun {next kret} hn ↦ ?_⟩
  rw [packT, holdsList_append, holdsList_append, holdsList_map_atoms]
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds, List.map_append, List.map_cons,
    List.map_nil, List.map_map]
  have hm1 : ((List.range 7).map ((σ ∘ fun k ↦ V.n (o + 785 + k)))) =
      (List.range 7).map fun k ↦ w (o + 785 + k) :=
    List.map_congr_left fun k hk ↦ e785 k (List.mem_range.mp hk)
  have hm2 : ((List.range 7).map ((σ ∘ fun k ↦ V.n (o + 798 + k)))) =
      (List.range 7).map fun k ↦ w (o + 798 + k) :=
    List.map_congr_left fun k hk ↦ e798 k (List.mem_range.mp hk)
  refine ⟨by rw [e781]; exact hpp, trivial, e783, e784,
    ⟨j1, by simp [stepNames]; omega, by rw [hx1, gen_pow_eq_ofK], ?_⟩, e792, e793, e794, e795, e796,
    e797, ⟨j2, by simp [remNames]; omega, by rw [hx2, gen_pow_eq_ofK], ?_⟩,
    fun j hj ↦ ecp j hj, trivial, hn⟩
  · rw [dispatch_getD (by simp [stepNames]; omega), hm1, e781, e782, e784, e783, gen48]
    exact hc1
  · rw [dispatch_getD (by simp [remNames]; omega), hm1, hm2, e796, e797, e781, e782, h16]
    exact hc2

end
end LeanVM.Guest.B1.VerifySub.KL
