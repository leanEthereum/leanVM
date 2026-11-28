/-
  LeanVM.Guest.CoreMode.Fn.verify_keccak.ExpB

  `verify_keccak`'s exponent facts (`Fam.lean`'s `expFam`, its rule file's `arg_bound`s and `fact`): `e(pack_g) < 21`
  (value `18`), `e(step_g) < 2` (`29`), `e(rem_g) < 16` (`48`) and `e(tau_g) ≥ 9` (`6`), at its honest instances whose
  table height `tau_g = g^h` has `9 ≤ h ≤ 24` (`vkHeadT_holds`), from that carried height (`expFam_okA_of`).
-/

module

public import LeanVM.Guest.EndExecCoreResA
public import LeanVM.Guest.CoreMode.Fn.verify_keccak.Fam
public import LeanVM.Guest.B1.KeccakGkr.VkHolds
public import LeanVM.Guest.B1.KeccakGkr.VkBody
public import LeanVM.Guest.CoreMode.Fn.verify_sub.VkCarry

namespace LeanVM.Guest.CoreMode.Own.verify_keccak

open LeanVM.Parameters LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Memory LeanVM.Guest.EndExec LeanVM.Guest.B1.VerifySub
open LeanVM.Guest.Value (gen_pow_eq_ofK)
open LeanVM.Protocol.Verifier (gen)

public section

variable {al : String → Bool} {D : Ref → RefD}

/-- **The head's exponents** at an honest instance of `verify_keccak` with `tau_g = g^h`, `9 ≤ h ≤ 24`:
`pack_g = g^(h - 4)`, `step_g = g^((h - 3) / 16)`, `rem_g = g^((h - 3) % 16)`. -/
theorem vk_exps {r : Ref} (hR : RefH (layB al) (D r) r) {I : Inst} (hI : I ∈ instsR al D r) {σ : Val}
    {bufs : List ℕ} {kids : List Tree} (ht : I.t = .node "verify_keccak" σ bufs kids) {h : ℕ} (h1 : 9 ≤ h)
    (h2 : h ≤ 24) (htg : σ (.n 6) = gen ^ h) :
    σ (.n 18) = gen ^ (h - 4) ∧ σ (.n 29) = gen ^ ((h - 3) / krStep) ∧ σ (.n 48) = gen ^ ((h - 3) % krStep) := by
  obtain ⟨args, rets, hvI⟩ := inst_validA hR hI ht
  obtain ⟨-, hb⟩ := Res.holds_of_valid Res.fs_pos hvI EndExec.find_vk
  rw [vk_body, vkT, holdsList_append] at hb
  obtain ⟨e18, -, e29, e48, -⟩ := vkHeadT_holds h1 (by omega) htg hb
  exact ⟨e18, e29, e48⟩

/-- **Step `0`'s claim point is the point** at an honest instance: both values are loaded at `claims·g^KC_POINT`
(top-level `load`s of value `156` at offset `2`). -/
theorem vk_ptEq {r : Ref} (hR : RefH (layB al) (D r) r) {I : Inst} (hI : I ∈ instsR al D r) {σ : Val}
    {bufs : List ℕ} {kids : List Tree} (ht : I.t = .node "verify_keccak" σ bufs kids) :
    σ (.n 443) = σ (.n 62) := by
  obtain ⟨args, rets, fn', hf', -, es, vs, hw, -, hh, -⟩ := inst_validA hR hI ht
  obtain rfl : fn' = fn% «verify_keccak» := Option.some.inj (hf'.symm.trans EndExec.find_vk)
  have hall : ∀ a ∈ LeanVM.Guest.Res.topAtoms (fn% «verify_keccak»).body, a.Holds r.img.read σ :=
    fun a ha ↦ hh _ (LeanVM.Guest.EndExec.topAtoms_on_path hw ha)
  have h1 := hall (.load (.n 62) (.n 156) 2) (by decide +kernel)
  have h2 := hall (.load (.n 443) (.n 156) 2) (by decide +kernel)
  simp only [Atom.Holds, LoadHolds] at h1 h2
  exact Option.some.inj (h2.2.symm.trans h1.2)

/-- **Its equation residual holds** at an honest instance (`vk_ptEq`). -/
theorem ptEq_holds {r : Ref} (hR : RefH (layB al) (D r) r) {I : Inst} (hI : I ∈ instsR al D r) {σ : Val}
    {bufs : List ℕ} {kids : List Tree} (ht : I.t = .node "verify_keccak" σ bufs kids) : ptEq.Holds σ := by
  show CCell.valW _ _ = CCell.valW _ _
  simp only [CCell.valW, prodW, vw, pow_one, mul_one, pow_zero]
  rw [vk_ptEq hR hI ht]

/-- **Its exponent facts hold** at every honest instance, given the carried height (`VkQ`'s shape). -/
theorem expFam_okA_of
    (hQ : ∀ {r : Ref}, RefH (layB al) (D r) r → r.Ok → ∀ J ∈ instsR al D r, ∀ σ bufs kids,
      J.t = .node "verify_keccak" σ bufs kids → ∃ h, 9 ≤ h ∧ h ≤ 24 ∧ σ (.n 6) = gen ^ h) :
    OwnOkA al D ("verify_keccak", fun _ r ↦ expFam r) := by
  intro r hR hr I hI σ bufs kids ht fn _ x hx
  obtain ⟨h, h1, h2, htg⟩ := hQ hR hr I hI σ bufs kids ht
  obtain ⟨e18, e29, e48⟩ := vk_exps hR hI ht h1 h2 htg
  simp only [expFam] at hx
  split at hx
  · rename_i y n
    simp only [Bool.and_eq_true, Nat.blt_eq, expB, List.any_cons, List.any_nil, Bool.or_false,
      Bool.or_eq_true, Nat.beq_eq, Nat.ble_eq] at hx
    obtain ⟨hn, (⟨rfl, hb⟩ | ⟨rfl, hb⟩ | ⟨rfl, hb⟩ | ⟨rfl, hb⟩)⟩ := hx
    · exact ltF_of_pow (e := h - 4) hn (by omega) (by rw [e18, gen_pow_eq_ofK])
    · exact ltF_of_pow (e := (h - 3) / krStep) hn (by rw [show krStep = 16 from rfl]; omega) (by rw [e29, gen_pow_eq_ofK])
    · exact ltF_of_pow (e := (h - 3) % krStep) hn (by rw [show krStep = 16 from rfl]; omega) (by rw [e48, gen_pow_eq_ofK])
    · exact ltF_of_pow (e := h) hn (by omega) (by rw [htg, gen_pow_eq_ofK])
  · rename_i c y
    simp only [Bool.and_eq_true, Nat.beq_eq, Nat.blt_eq] at hx
    obtain ⟨rfl, hc⟩ := hx
    refine ⟨c, h, CoreMode.rep_const (by unfold capE; omega), ?_, by omega⟩
    simp only [idxC, CoreMode.valW_baseC, vw, htg, gen_pow_eq_ofK]
    exact CoreMode.rep_of (by unfold capE; omega)
  · cases hx

end

end LeanVM.Guest.CoreMode.Own.verify_keccak
