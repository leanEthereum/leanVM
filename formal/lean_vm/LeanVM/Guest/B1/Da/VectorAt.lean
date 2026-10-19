/-
  LeanVM.Guest.B1.Da.VectorAt

  `da_vector_cell__L0` and `__L1` placed by the bump allocator, loading from a region
  (`RelAtIn`): the weights' frame run at the frame position the certificate gives.
-/

module

public import LeanVM.Guest.B1.Da.Vector
public import LeanVM.Guest.B1.Da.Atoms
public import LeanVM.Guest.B1.Da.WeightIn

/-!
# `da_vector_cell__L{final}`, placed

At frame position `fp`, `da_vector_cell` returns as its weights' address the cell of its frame
holding the first weight, `g^(fp + cert f (.n 4))`, loads only the four counter words at
`counters·xb³` (the region `R`), and owns its weights' run, which its caller may rely on (`D`).
It allocates nothing and calls nothing, so its words are its frame's.
-/

namespace LeanVM.Guest.B1.Digest

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.Blake2sHash
open LeanVM.Guest.Core LeanVM.Guest.Memory LeanVM.Guest.Value
open LeanVM.Protocol.Verifier (gen)
open LeanVM.Guest.B1.Main (RelAtInW relAtInW_of_walk)

@[expose] public section

theorem vx_noAlloc (final : Bool) : (vxAtoms final).all (fun a => !atomAllocB a) = true := by
  cases final <;> decide +kernel

theorem vx_addrs (final : Bool) : (vxAtoms final).filterMap atomAddr? = [(.n (vxF final), .n 4)] := by
  cases final <;> decide +kernel

theorem vx_runs (final : Bool) : (vxAtoms final).filterMap atomRun? = [(.n 4, 256)] := by
  cases final <;> decide +kernel

theorem vx_loads (final : Bool) :
    (vxAtoms final).filterMap atomLoad? = [(.n 3464, 0), (.n 3468, 1), (.n 3600, 1), (.n 3732, 1)] := by
  cases final <;> decide +kernel

/-- **`da_vector_cell__L{final}`, placed at `fp`**: on a memory holding the counter words at
`counters·xb³` and, in its frame, the weights, its relation by a tree of its frame's words, loading
the counters from `R`, whose data covers any `D` within the weights' run. -/
theorem vx_relAtIn (fs : String → ℕ) (cert : String → V → ℕ) (final : Bool) {xb h0 h1 ctr o0 o1 : E}
    {ws cv : List E} {b c : ℕ} {R D : ℕ → Prop} (hxb : xb = gen ^ b) (hctr : ctr = gen ^ c)
    (hch : ChainCells (h0, h1) (vxBlocks (ws.getD · 0)) (vxMd final (cv.getD · 0)) 96 (o0, o1))
    (hR : ∀ k < 4, R (c + 3 * b + k)) (fp : ℕ)
    (hD : ∀ i, D i → fp + cert (vxName final) (.n 4) ≤ i ∧ i < fp + cert (vxName final) (.n 4) + 256)
    (rd : Reader) (hcv : CellsAt rd (ctr * (xb * xb * xb)) cv) (hcl : cv.length = 4)
    (hws : ∀ k < 256, ∀ v, rd (gpow (fp + cert (vxName final) (.n 4) + k)) = some v → v = ws.getD k 0) :
    RelAtInW fs cert wId rd R D fp (fs (vxName final)) (vxName final) [xb, h0, h1, ctr]
      [o0, o1, gen ^ (fp + cert (vxName final) (.n 4))] fun θ => θ (vxName final) := by
  rcases hch with ⟨h96, -⟩ | ⟨-, hd, hst0, hcan, hout⟩
  · omega
  set a0 := fp + cert (vxName final) (.n 4)
  have hcv' : ∀ k < 4, LoadHolds rd (ctr * (xb * xb * xb)) k (cv.getD k 0) := fun k hk => by
    rw [List.getD_eq_getElem _ _ (by omega)]; exact hcv k (by omega)
  have hfr : IsInK (gen ^ a0) ∧ ∀ k < 256, ∀ v, rd ((gen ^ a0).limb 0 * Parameters.gpow k) = some v →
      v = ws.getD k 0 := ⟨by rw [gen_pow_eq_ofK]; exact ofK_isInK _, fun k hk v hv => hws k hk v (by
        rwa [limb0_gen_pow, gpow_add'] at hv)⟩
  obtain ⟨ha, hr, hp⟩ := vx_core_holds (final := final) (wsf := (ws.getD · 0)) (cvf := (cv.getD · 0))
    (st := fun i => digestScalars (chainRun hd (vxBlocks (ws.getD · 0)) (vxMd final (cv.getD · 0)) i))
    hcv' hfr hst0.symm hout.symm (fun j hj => (compressCells_chainRun (hcan j hj).1 (hcan j hj).2).mpr rfl)
  set σ : Val := fun v => vxVals final xb h0 h1 ctr (gen ^ a0) (ws.getD · 0) (cv.getD · 0)
    (fun i => digestScalars (chainRun hd (vxBlocks (ws.getD · 0)) (vxMd final (cv.getD · 0)) i))
    (vxMd final (cv.getD · 0)) v.idx with hσ
  have h3464 : σ (.n 3464) = gen ^ (c + 3 * b) := by
    show ctr * (xb * xb * xb) = _; rw [hxb, hctr]; ring
  have h3468 : σ (.n 3468) = gen ^ (c + 3 * b) := h3464
  have h3600 : σ (.n 3600) = gen ^ (c + 3 * b + 1) := by
    show ctr * (xb * xb * xb * word 2 0 0) = _
    rw [hxb, hctr, word_gen]; ring
  have h3732 : σ (.n 3732) = gen ^ (c + 3 * b + 2) := by
    show ctr * (xb * xb * xb * word 4 0 0) = _
    rw [hxb, hctr, word4]; ring
  have hload : ∀ A ∈ loadAddrs σ ((vxAtoms final).map Ev.atom), ∃ i, A = gpow i ∧
      (ownData cert fp (fp + fs (vxName final)) (vxName final) (allocs σ ((vxAtoms final).map Ev.atom))
        ((vxAtoms final).map Ev.atom) i ∨ R i ∨ (fun _ => False) i) := by
    rw [loadAddrs_atoms, vx_loads]
    intro A hA
    simp only [List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false] at hA
    rcases hA with rfl | rfl | rfl | rfl
    · exact ⟨c + 3 * b + 0, by rw [h3464, limb0_gen_pow, gpow_add'], Or.inr (Or.inl (hR 0 (by omega)))⟩
    · exact ⟨c + 3 * b + 1, by rw [h3468, limb0_gen_pow, gpow_add'], Or.inr (Or.inl (hR 1 (by omega)))⟩
    · exact ⟨c + 3 * b + 2, by rw [h3600, limb0_gen_pow, gpow_add'], Or.inr (Or.inl (hR 2 (by omega)))⟩
    · exact ⟨c + 3 * b + 3, by rw [h3732, limb0_gen_pow, gpow_add'], Or.inr (Or.inl (hR 3 (by omega)))⟩
  have h := relAtInW_of_walk (fs := fs) (cert := cert) (w := wId) (σ := σ) (rd := rd)
    (R := R) (D := D) (Dk := fun _ => False) (fp := fp) (N := 0) (bws := []) (find_vx final)
    (Or.inr (calls_atoms _)) hp (walk_atoms σ (vxAtoms final) _) hr (holds_atoms ha)
    (by rw [allocDsts_atoms (vx_noAlloc final), allocs_atoms σ (vx_noAlloc final)]; rfl)
    (fun q hq => by
      rw [addrs_atoms, vx_addrs] at hq
      obtain rfl := List.mem_singleton.mp hq
      show σ (.n (vxF final)) = _
      rw [show σ (.n (vxF final)) = gen ^ a0 by cases final <;> rfl, gen_pow_eq_ofK])
    (by rw [calls_atoms]; exact ⟨rfl, fun i h => h⟩) hload
    (fun i hi => Or.inl (Or.inr ⟨(.n 4, 256), by rw [runs_atoms, vx_runs]; simp, (hD i hi).1, (hD i hi).2⟩))
  simp only [allocs_atoms σ (vx_noAlloc final), List.sum_nil, Nat.add_zero, List.map_nil] at h
  exact h

/-- **The uniform placed form.** -/
theorem vx_relAtIn_uniform (fs : String → ℕ) (cert : String → V → ℕ) (final : Bool)
    {xb h0 h1 ctr o0 o1 : E} {ws cv : List E} {b c : ℕ} {R : ℕ → Prop} (hxb : xb = gen ^ b)
    (hctr : ctr = gen ^ c)
    (hch : ChainCells (h0, h1) (vxBlocks (ws.getD · 0)) (vxMd final (cv.getD · 0)) 96 (o0, o1))
    (hR : ∀ k < 4, R (c + 3 * b + k)) (hcl : cv.length = 4) :
    ∀ fp, ∃ n, ∀ rd, (CellsAt rd (ctr * (xb * xb * xb)) cv ∧
      ∀ k < 256, ∀ v, rd (gpow (fp + cert (vxName final) (.n 4) + k)) = some v → v = ws.getD k 0) →
      RelAtInW fs cert wId rd R
        (fun i => fp + cert (vxName final) (.n 4) ≤ i ∧ i < fp + cert (vxName final) (.n 4) + 256) fp n
        (vxName final) [xb, h0, h1, ctr] [o0, o1, gen ^ (fp + cert (vxName final) (.n 4))]
        fun θ => θ (vxName final) :=
  fun fp => ⟨_, fun rd hm => vx_relAtIn fs cert final hxb hctr hch hR fp (fun _ h => h) rd hm.1 hcl hm.2⟩

end
end LeanVM.Guest.B1.Digest
