/-
  LeanVM.Guest.CoreMode.Fn.verify_keccak.Runs

  `verify_keccak`'s runs over its head's exponents (`Fam.lean`'s `runFam`): at an honest instance with
  `tau_g = g^h`, `9 ≤ h ≤ 24`, `pack_g = tau_g·g^-4 = g^(h-4)` and `y_g = step_g^16·rem_g = g^(h-3)`, so each run of
  `vkRuns` lies in its outer run, and the exponent bounds over `pack_g` hold (`runFam_holds`).
-/

module

public import LeanVM.Guest.CoreMode.Fn.verify_keccak.ExpB

namespace LeanVM.Guest.CoreMode.Own.verify_keccak

open LeanVM.Parameters LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Memory LeanVM.Guest.EndExec LeanVM.Guest.B1.VerifySub
open LeanVM.Guest.Value (gen_pow_eq_ofK)
open LeanVM.Protocol.Verifier (gen)

public section

variable {al : String → Bool} {D : Ref → RefD}

/-- **A run inside a run of the same base**: each cell `B·g^(tq + Sq·j)` of the first is `B·g^(tr + Sr·j')` of the
second, the exponents of the bounds known. -/
theorem subR_gen {σ : Val} {q r : CRun} {B : E} {tq tr sq sr ql qh rl rh : ℕ}
    (hq : q.base.valW (vw σ) = B * gen ^ tq) (hr : r.base.valW (vw σ) = B * gen ^ tr)
    (hsq : q.stride = sq) (hsr : r.stride = sr)
    (h1 : rep ((idxC q.lo).valW (vw σ)) = some ql) (h2 : rep ((idxC q.hi).valW (vw σ)) = some qh)
    (h3 : rep ((idxC r.lo).valW (vw σ)) = some rl) (h4 : rep ((idxC r.hi).valW (vw σ)) = some rh)
    (hk : ∀ j, ql ≤ j → j < qh → ∃ j', rl ≤ j' ∧ j' < rh ∧ tq + sq * j = tr + sr * j') :
    (CRes.subR q r).Holds σ := by
  intro x hx
  unfold CRun.Set RunSet at hx ⊢
  obtain ⟨ylo, yhi, j, e1, e2, hj1, hj2, rfl⟩ := hx
  obtain rfl := Option.some.inj (h1.symm.trans e1)
  obtain rfl := Option.some.inj (h2.symm.trans e2)
  obtain ⟨j', a1, a2, a3⟩ := hk j hj1 hj2
  refine ⟨rl, rh, j', h3, h4, a1, a2, ?_⟩
  rw [hq, hr, hsq, hsr]
  simp only [← gen_pow_eq_ofK]
  rw [mul_assoc, mul_assoc, ← pow_add, ← pow_add, a3]

/-- `g^e`'s exponent, below `2^62`. -/
theorem rep_gen {e : ℕ} (he : e < capE) : rep (gen ^ e) = some e := by
  rw [gen_pow_eq_ofK]; exact rep_of he

/-- **The runs hold** at a valuation whose head words are `g^h`, `g^(h-4)`, `g^((h-3)/16)`, `g^((h-3)%16)`. -/
theorem vkRuns_holds {σ : Val} {h : ℕ} (h1 : 9 ≤ h) (h2 : h ≤ 24) (htg : σ (.n 6) = gen ^ h)
    (hP : σ (.n 6) * σ (.n 17) = gen ^ (h - 4)) (hS : σ (.n 29) = gen ^ ((h - 3) / 16))
    (hRm : σ (.n 33) * (σ (.n 37) * (σ (.n 42) * σ (.n 47))) = gen ^ ((h - 3) % 16)) :
    ∀ x ∈ vkRuns, x.Holds σ := by
  have cap : ∀ {e : ℕ}, e < 1099511627776 → e < capE := fun he ↦ by unfold capE; omega
  have vP : ∀ k, (⟨pM, k⟩ : CCell).valW (vw σ) = gen ^ (h - 4 + k) := by
    intro k
    simp only [CCell.valW, prodW, pM, vw, pow_one, mul_one]
    rw [hP, ← gen_pow_eq_ofK, pow_add]
  have vY : yC.valW (vw σ) = gen ^ (h - 3) := by
    simp only [CCell.valW, prodW, yC, remM, vw, pow_one, mul_one]
    rw [hS, hRm, ← gen_pow_eq_ofK, pow_zero, mul_one, ← pow_mul, ← pow_add]
    congr 1
    omega
  have vR : (⟨remM, 0⟩ : CCell).valW (vw σ) = gen ^ ((h - 3) % 16) := by
    simp only [CCell.valW, prodW, remM, vw, pow_one, mul_one]
    rw [hRm, ← gen_pow_eq_ofK, pow_zero, mul_one]
  have vb : ∀ b o, (⟨[(b, 1)], o⟩ : CCell).valW (vw σ) = σ (.n b) * gen ^ o := by
    intro b o
    simp only [CCell.valW, prodW, vw, pow_one, mul_one, gen_pow_eq_ofK]
  have v62 : (⟨[(29, 16), (62, 1)], 0⟩ : CCell).valW (vw σ) = σ (.n 62) * gen ^ ((h - 3) / 16 * 16) := by
    simp only [CCell.valW, prodW, vw, pow_one, mul_one]
    rw [hS, ← gen_pow_eq_ofK, pow_zero, mul_one, ← pow_mul]
    exact mul_comm _ _
  have rn : ∀ n, n < capE → rep ((idxC (.num n)).valW (vw σ)) = some n := fun n hn ↦ rep_const hn
  have r6 : rep ((idxC (.val 6)).valW (vw σ)) = some h := by
    show rep ((baseC 6).valW (vw σ)) = some h
    rw [valW_baseC, vw, htg]; exact rep_gen (cap (by omega))
  have r29 : rep ((idxC (.val 29)).valW (vw σ)) = some ((h - 3) / 16) := by
    show rep ((baseC 29).valW (vw σ)) = some _
    rw [valW_baseC, vw, hS]; exact rep_gen (cap (by omega))
  have rP : ∀ k, k < 4294967296 → rep ((idxC (.mono ⟨pM, k⟩)).valW (vw σ)) = some (h - 4 + k) := fun k hk ↦ by
    show rep ((⟨pM, k⟩ : CCell).valW (vw σ)) = _
    rw [vP]; exact rep_gen (cap (by omega))
  have rY : rep ((idxC (.mono yC)).valW (vw σ)) = some (h - 3) := by
    show rep (yC.valW (vw σ)) = _
    rw [vY]; exact rep_gen (cap (by omega))
  have rR : rep ((idxC (.mono ⟨remM, 0⟩)).valW (vw σ)) = some ((h - 3) % 16) := by
    show rep ((⟨remM, 0⟩ : CCell).valW (vw σ)) = _
    rw [vR]; exact rep_gen (cap (by omega))
  have c0 : (0 : ℕ) < capE := cap (by omega)
  have c4 : (4 : ℕ) < capE := cap (by omega)
  intro x hx
  simp only [vkRuns, List.mem_append, List.mem_cons, List.mem_map, List.mem_range, List.not_mem_nil,
    or_false] at hx
  rcases hx with (rfl | rfl | rfl | rfl | rfl) | ⟨d, hd, rfl⟩
  · exact subR_gen (sq := 1) (sr := 1) (vb 7 4) (vb 7 0) rfl rfl (rn 0 c0) (rP 0 (by norm_num)) (rn 0 c0) r6
      fun j _ hj ↦ ⟨4 + j, by omega, by omega, by omega⟩
  · exact subR_gen (sq := 1) (sr := 1) v62 (vb 62 0) rfl rfl (rn 0 c0) rR (rn 0 c0) rY
      fun j _ hj ↦ ⟨(h - 3) / 16 * 16 + j, by omega, by omega, by omega⟩
  · exact subR_gen (sq := 1) (sr := 1) (vb 1740 0) (vb 1740 0) rfl rfl (rn 0 c0) (rP 0 (by norm_num)) (rn 0 c0) rY
      fun j _ hj ↦ ⟨j, by omega, by omega, by omega⟩
  · exact subR_gen (sq := 1) (sr := 1) (vb 9 0) (vb 9 4) rfl rfl (rn 4 c4) r6 (rn 0 c0) (rP 0 (by norm_num))
      fun j hj0 hj ↦ ⟨j - 4, by omega, by omega, by omega⟩
  · exact subR_gen (sq := 1) (sr := 1) (vb 9 39) (vb 9 43) rfl rfl (rn 4 c4) r6 (rn 0 c0) (rP 0 (by norm_num))
      fun j hj0 hj ↦ ⟨j - 4, by omega, by omega, by omega⟩
  · exact subR_gen (sq := 16) (sr := 1) (vb 62 d) (vb 62 0) rfl rfl (rn 0 c0) r29 (rn 0 c0) rY
      fun j _ hj ↦ ⟨d + 16 * j, by omega, by omega, by omega⟩

/-- **Its runs hold** at the same valuations (`vkRuns_holds`, the exponent bounds over `pack_g`). -/
theorem runFam_holds {σ : Val} {h : ℕ} (h1 : 9 ≤ h) (h2 : h ≤ 24) (htg : σ (.n 6) = gen ^ h)
    (hP : σ (.n 6) * σ (.n 17) = gen ^ (h - 4)) (hS : σ (.n 29) = gen ^ ((h - 3) / 16))
    (hRm : σ (.n 33) * (σ (.n 37) * (σ (.n 42) * σ (.n 47))) = gen ^ ((h - 3) % 16)) {x : CRes}
    (hx : runFam x = true) : x.Holds σ := by
  have hR := vkRuns_holds h1 h2 htg hP hS hRm
  have cap : ∀ {e : ℕ}, e < 1099511627776 → e < capE := fun he ↦ by unfold capE; omega
  unfold runFam at hx
  simp only [Bool.or_eq_true, decide_eq_true_eq] at hx
  rcases hx with hm | hx
  · exact hR x hm
  split at hx
  · simp only [decide_eq_true_eq] at hx
    exact fun _ ↦ hR _ hx
  · rename_i c n
    simp only [Bool.and_eq_true, decide_eq_true_eq, Nat.ble_eq, Nat.blt_eq] at hx
    obtain ⟨⟨rfl, hn⟩, hc⟩ := hx
    refine ⟨h - 4, n, ?_, rep_const hc, by omega⟩
    show rep ((⟨pM, 0⟩ : CCell).valW (vw σ)) = _
    simp only [CCell.valW, prodW, pM, vw, pow_one, mul_one]
    rw [hP, ← gen_pow_eq_ofK, pow_zero, mul_one]
    exact rep_gen (cap (by omega))
  · rename_i c m
    obtain ⟨bs, k⟩ := m
    simp only [Bool.and_eq_true, decide_eq_true_eq, Nat.blt_eq] at hx
    obtain ⟨⟨rfl, hc⟩, hk⟩ := hx
    refine ⟨c, h - 4 + k, rep_const (cap (by omega)), ?_, by omega⟩
    show rep ((⟨pM, k⟩ : CCell).valW (vw σ)) = _
    simp only [CCell.valW, prodW, pM, vw, pow_one, mul_one]
    rw [hP, ← gen_pow_eq_ofK, ← pow_add]
    exact rep_gen (cap (by omega))
  · cases hx

/-- **The head's words** at an honest instance with `tau_g = g^h`, `9 ≤ h ≤ 24`: `tau_g·g^-4 = g^(h-4)` (the top-level
product `pack_g = tau_g·g^-4`), `step_g = g^((h-3)/16)`, and `rem_g`'s bit factors' product `g^((h-3)%16)` (the
top-level products that make `rem_g`). -/
theorem vk_headWords {r : Ref} (hR : RefH (layB al) (D r) r) {I : Inst} (hI : I ∈ instsR al D r) {σ : Val}
    {bufs : List ℕ} {kids : List Tree} (ht : I.t = .node "verify_keccak" σ bufs kids) {h : ℕ} (h1 : 9 ≤ h)
    (h2 : h ≤ 24) (htg : σ (.n 6) = gen ^ h) :
    σ (.n 6) * σ (.n 17) = gen ^ (h - 4) ∧ σ (.n 29) = gen ^ ((h - 3) / 16) ∧
      σ (.n 33) * (σ (.n 37) * (σ (.n 42) * σ (.n 47))) = gen ^ ((h - 3) % 16) := by
  obtain ⟨e18, e29, e48⟩ := vk_exps hR hI ht h1 h2 htg
  rw [show krStep = 16 from rfl] at e29 e48
  obtain ⟨args, rets, fn', hf', -, es, vs, hw, -, hh, -⟩ := inst_validA hR hI ht
  obtain rfl : fn' = fn% «verify_keccak» := Option.some.inj (hf'.symm.trans EndExec.find_vk)
  have hall : ∀ a ∈ LeanVM.Guest.Res.topAtoms (fn% «verify_keccak»).body, a.Holds r.img.read σ :=
    fun a ha ↦ hh _ (LeanVM.Guest.EndExec.topAtoms_on_path hw ha)
  have m18 := hall (.mul (.n 18) (.n 6) (.n 17)) (by decide +kernel)
  have m38 := hall (.mul (.n 38) (.n 33) (.n 37)) (by decide +kernel)
  have m43 := hall (.mul (.n 43) (.n 38) (.n 42)) (by decide +kernel)
  have m48 := hall (.mul (.n 48) (.n 43) (.n 47)) (by decide +kernel)
  simp only [Atom.Holds] at m18 m38 m43 m48
  refine ⟨by rw [← m18, e18], e29, ?_⟩
  calc σ (.n 33) * (σ (.n 37) * (σ (.n 42) * σ (.n 47))) = σ (.n 33) * σ (.n 37) * σ (.n 42) * σ (.n 47) := by ring
    _ = σ (.n 48) := by rw [← m38, ← m43, ← m48]
    _ = _ := e48

end

end LeanVM.Guest.CoreMode.Own.verify_keccak
