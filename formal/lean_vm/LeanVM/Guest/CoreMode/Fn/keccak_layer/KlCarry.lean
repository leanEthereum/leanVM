/-
  LeanVM.Guest.CoreMode.Fn.keccak_layer.KlCarry

  `keccak_layer`'s point length at the honest instances of b2c's aligned tree (`KlQ`), carried from `verify_keccak`.
-/

module

public import LeanVM.Guest.CoreMode.Fn.verify_keccak.ExpB
public import LeanVM.Guest.B1.KeccakGkr.LayerHolds

/-!
# `keccak_layer`'s `y_g`, carried down

`keccak_layer__L{0,1}`'s only caller is `verify_keccak` (`Own.keccak_layer.stCallers`, the whole program's check
`Res.termCallers_all`), which passes as its `y_g`, `step_g`, `rem_g` (parameters `8`, `9`, `10`) a value `pack_g·g`
it defines at the top level, and its values `29`, `48` (`vk_kl_sites`). At `verify_keccak`'s `tau_g = g^h`
(`vkQ_allA`), `vk_exps` gives `y_g = g^(h - 3) = step_g^16·rem_g`, `h - 3 < 32`.

`klQ_allA`: `KlQ` at every honest instance (`insts_allA`).
-/

namespace LeanVM.Guest.EndExec

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Memory
open LeanVM.Protocol.Verifier (gen)

@[expose] public section

/-- **`keccak_layer`'s point length at an instance**: `y_g = g^y`, `y < 32`, `step_g = g^s`, `s < 2`, and
`y_g = step_g^16·rem_g`. -/
def KlQ (J : Inst) : Prop :=
  ∀ f σ bufs kids, J.t = .node f σ bufs kids → (f = name% «keccak_layer__L0» ∨ f = name% «keccak_layer__L1») →
    ∃ y s, y < 32 ∧ s < 2 ∧ σ (.n 8) = gen ^ y ∧ σ (.n 9) = gen ^ s ∧ σ (.n 8) = σ (.n 9) ^ 16 * σ (.n 10)

/-- A value `y` the top level of `body` defines as `pack_g·g` (value `18`). -/
noncomputable def klY (body : List Stmt) (y : Core.V) : Bool :=
  (Res.topAtoms body).any fun
    | .mul d a b => d == y && a == .n 18 && (Res.topAtoms body).contains (.const b (word 2 0))
    | _ => false

/-- A `keccak_layer` call site of `body`: its `y_g` a top-level product `pack_g·g` (`klY`), its `step_g` and `rem_g`
the values `29` and `48`. -/
noncomputable def klSite (body : List Stmt) (g : String) (args : List Core.V) : Bool :=
  (g != name% «keccak_layer__L0» && g != name% «keccak_layer__L1») ||
    ((match args[8]? with
      | some y => klY body y
      | none => false) && args[9]? == some (.n 29) && args[10]? == some (.n 48))

end

public section

theorem vk_kl_sites :
    Res.sitesB (fun g args _ ↦ klSite (fn% «verify_keccak»).body g args) (fn% «verify_keccak»).body = true := by
  decide +kernel

theorem kl_facts : (fn% «keccak_layer__L0»).params[8]? = some (.n 8) ∧
    (fn% «keccak_layer__L0»).params[9]? = some (.n 9) ∧ (fn% «keccak_layer__L0»).params[10]? = some (.n 10) ∧
    (fn% «keccak_layer__L0»).loop = false ∧
    (fn% «keccak_layer__L1»).params[8]? = some (.n 8) ∧
    (fn% «keccak_layer__L1»).params[9]? = some (.n 9) ∧ (fn% «keccak_layer__L1»).params[10]? = some (.n 10) ∧
    (fn% «keccak_layer__L1»).loop = false := by
  decide +kernel

variable {al : String → Bool} {D : Ref → RefD} {r : Ref}

/-- **`KlQ` passes down a call**: from `verify_keccak`'s carried `tau_g` (`vkQ_allA`, `vk_exps`). -/
theorem klQ_stepA (hR : RefH (layB al) (D r) r) (hr : r.Ok) :
    Res.KidStep coreProgram r.img.read B2C.H (instsR al D r) KlQ := by
  intro I hI fI σI bufsI kidsI hIt fnI hfI es vs hw hh i c J hci hJS hk _ _ hname hval hph _
    f σ bufs kids hJt hf
  have hct : c.taken = true := by
    cases h : c.taken
    · obtain ⟨g', σ', h'⟩ := hph h
      rw [hJt] at h'; cases h'
    · rfl
  have hJv := hval hct
  rw [hJt] at hJv
  obtain ⟨fn, hfn, hpar, -⟩ := hJv
  have hcf : c.f = f := by rw [← hname, hJt]; rfl
  have hc : c ∈ calls es := List.mem_of_getElem? hci
  obtain ⟨p8, p9, p10, hpl⟩ : fn.params[8]? = some (.n 8) ∧ fn.params[9]? = some (.n 9) ∧
      fn.params[10]? = some (.n 10) ∧ fn.loop = false := by
    obtain ⟨a8, a9, a10, al0, b8, b9, b10, bl1⟩ := kl_facts
    rcases hf with rfl | rfl
    · obtain rfl : fn = fn% «keccak_layer__L0» := Option.some.inj (hfn.symm.trans B1.VerifySub.find_layer265)
      exact ⟨a8, a9, a10, al0⟩
    · obtain rfl : fn = fn% «keccak_layer__L1» := Option.some.inj (hfn.symm.trans B1.VerifySub.find_layer264)
      exact ⟨b8, b9, b10, bl1⟩
  -- the caller is `verify_keccak`
  have hmem : (f, name% «verify_keccak») ∈ Res.termCallers :=
    CoreMode.FnReg.stCallers_of_keccak_layer _ (by
      rcases hf with rfl | rfl <;> simp [CoreMode.Own.keccak_layer.stCallers])
  have hcal := List.all_eq_true.mp (Res.calls_sites (Res.termCallers_all fnI (List.mem_of_find?_eq_some hfI))
    hw c hc) _ hmem
  have hnI := find_name' hfI
  rw [hcf] at hcal
  simp only [bne_self_eq_false, Bool.false_or, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq] at hcal
  have hvk : fI = name% «verify_keccak» := by
    rcases hcal with h | ⟨h, hl⟩
    · rw [← hnI, h]
    · exfalso
      rw [hnI] at h
      subst h
      obtain rfl : fnI = fn := Option.some.inj (hfI.symm.trans hfn)
      rw [hpl] at hl; cases hl
  subst hvk
  obtain rfl : fnI = fn% «verify_keccak» := Option.some.inj (hfI.symm.trans find_vk)
  -- the site
  have hs := Res.calls_sites vk_kl_sites hw c hc
  rw [hcf] at hs
  have hkl : (f != name% «keccak_layer__L0» && f != name% «keccak_layer__L1») = false := by
    rcases hf with rfl | rfl <;> decide
  simp only [klSite, hkl, Bool.false_or, Bool.and_eq_true, beq_iff_eq] at hs
  obtain ⟨⟨hy, h9⟩, h10⟩ := hs
  have hall : ∀ a ∈ Res.topAtoms (fn% «verify_keccak»).body, a.Holds r.img.read σI :=
    fun a ha ↦ hh _ (topAtoms_on_path hw ha)
  obtain ⟨y, h8, hy⟩ : ∃ y, c.args[8]? = some y ∧ klY (fn% «verify_keccak»).body y = true := by
    split at hy
    · exact ⟨_, by assumption, hy⟩
    · cases hy
  obtain ⟨a, ha, hm⟩ := List.any_eq_true.mp hy
  obtain ⟨b, em, ec⟩ : ∃ b : Core.V, σI y = σI (.n 18) * σI b ∧ σI b = word 2 0 := by
    split at hm
    · rename_i d a1 b1
      simp only [Bool.and_eq_true, beq_iff_eq, List.contains_iff_mem] at hm
      obtain ⟨⟨rfl, rfl⟩, hc⟩ := hm
      exact ⟨b1, hall _ ha, hall _ hc⟩
    · cases hm
  have q8 : σ (.n 8) = σI y := param_of hpar p8 h8
  have q9 : σ (.n 9) = σI (.n 29) := param_of hpar p9 h9
  have q10 : σ (.n 10) = σI (.n 48) := param_of hpar p10 h10
  -- `verify_keccak`'s exponents
  obtain ⟨h, h1, h2, htg⟩ := vkQ_allA hR hr I hI σI bufsI kidsI hIt
  have h1' : 9 ≤ h := by rw [show LeanVM.Protocol.Verifier.keccakMinStepsLog = 9 from rfl] at h1; exact h1
  obtain ⟨e18, e29, e48⟩ := CoreMode.Own.verify_keccak.vk_exps hR hI hIt h1' h2 htg
  have hy8 : σ (.n 8) = gen ^ (h - 3) := by
    rw [q8, em, ec, e18, B1.word_gen, ← pow_succ, show h - 4 + 1 = h - 3 by omega]
  refine ⟨h - 3, (h - 3) / B1.VerifySub.krStep, by omega,
    by rw [show B1.VerifySub.krStep = 16 from rfl]; omega, hy8, by rw [q9, e29], ?_⟩
  rw [hy8, q9, q10, e29, e48, ← pow_mul, ← pow_add, show B1.VerifySub.krStep = 16 from rfl, mul_comm,
    Nat.div_add_mod]

/-- **`keccak_layer`'s point length at every honest instance.** -/
theorem klQ_allA (hR : RefH (layB al) (D r) r) (hr : r.Ok) : ∀ J ∈ instsR al D r, KlQ J := by
  refine insts_allA hR (klQ_stepA hR hr) fun J hm ↦ ?_
  intro f σ bufs kids hJt hf
  have hn := hm _ _ _ _ hJt
  rcases hf with rfl | rfl <;> exact absurd hn (by decide +kernel)

end

end LeanVM.Guest.EndExec
