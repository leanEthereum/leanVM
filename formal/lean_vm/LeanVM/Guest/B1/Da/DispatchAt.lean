/-
  LeanVM.Guest.B1.Da.DispatchAt

  `da_vector_dispatch` placed by the bump allocator, loading from a region (`RelAtIn`): its vector
  cell right after its frame.
-/

module

public import LeanVM.Guest.B1.Da.VectorAt
public import LeanVM.Guest.B1.Da.Column

/-!
# `da_vector_dispatch`, placed

At `fp`, `da_vector_dispatch(g^b, …)` runs `da_vector_cell__L{b = 127}` at `fp + fs
"da_vector_dispatch"`, whose weights' run its caller relies on.
-/

namespace LeanVM.Guest.B1.Digest

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.Blake2sHash
open LeanVM.Guest.Core LeanVM.Guest.Memory LeanVM.Guest.Value
open LeanVM.Protocol.Verifier (gen)
open LeanVM.Guest.B1.Main (RelAtInW relAtInW_of_walk)

@[expose] public section

/-- The path of `da_vector_dispatch`, the cell `final` taken. -/
def vdEs (final : Bool) : List Ev :=
  [.atom (.const (.n 4) (word 9223372036854775983 0 0)), .atom (.add (.n 5) (.n 0) (.n 4)), .inK (.n 5)] ++
    (if final then
      [.call "da_vector_cell__L1" [.n 0, .n 1, .n 2, .n 3] [.n 6, .n 7, .n 8], .atom (.copy (.n 9) (.n 6)),
        .atom (.copy (.n 10) (.n 7)), .atom (.copy (.n 11) (.n 8))]
    else
      [.call "da_vector_cell__L0" [.n 0, .n 1, .n 2, .n 3] [.n 12, .n 13, .n 14],
        .atom (.copy (.n 9) (.n 12)), .atom (.copy (.n 10) (.n 13)), .atom (.copy (.n 11) (.n 14))]) ++
    [.atom (.copy (.n 15) (.n 9)), .atom (.copy (.n 16) (.n 10)), .atom (.copy (.n 17) (.n 11))]

theorem vd_walk (σ : Val) (final : Bool) (h5 : σ (.n 5) = 0 ↔ final = true) :
    walk σ vdBody = .ret (vdEs final) [.n 15, .n 16, .n 17] := by
  cases final
  · have : σ (.n 5) ≠ 0 := fun h => by simpa using h5.mp h
    simp [vdBody, vdEs, walk, walk1, Out.seq, Out.pre, this]
  · have : σ (.n 5) = 0 := h5.mpr rfl
    simp [vdBody, vdEs, walk, walk1, Out.seq, Out.pre, this]

/-- `da_vector_dispatch` at `fp`, its selector's branch given. -/
theorem vd_relAtIn' (fs : String → ℕ) (cert : String → V → ℕ) {xb h0 h1 ctr o0 o1 : E} {ws cv : List E}
    (final : Bool) {b c : ℕ} {R D : ℕ → Prop}
    (hf5 : xb + word 9223372036854775983 0 0 = 0 ↔ final = true) (hxb : xb = gen ^ b) (hctr : ctr = gen ^ c)
    (hch : ChainCells (h0, h1) (vxBlocks (ws.getD · 0)) (vxMd (final) (cv.getD · 0)) 96 (o0, o1))
    (hR : ∀ k < 4, R (c + 3 * b + k)) (fp : ℕ)
    (hD : ∀ i, D i → fp + fs "da_vector_dispatch" + cert (vxName (final)) (.n 4) ≤ i ∧
      i < fp + fs "da_vector_dispatch" + cert (vxName (final)) (.n 4) + 256)
    (rd : Reader) (hcv : CellsAt rd (ctr * (xb * xb * xb)) cv) (hcl : cv.length = 4)
    (hws : ∀ k < 256, ∀ v, rd (gpow (fp + fs "da_vector_dispatch" + cert (vxName (final)) (.n 4) + k)) =
      some v → v = ws.getD k 0) :
    RelAtInW fs cert wId rd R D fp (fs "da_vector_dispatch" + fs (vxName (final)))
      "da_vector_dispatch" [xb, h0, h1, ctr]
      [o0, o1, gen ^ (fp + fs "da_vector_dispatch" + cert (vxName (final)) (.n 4))]
      fun θ => θ "da_vector_dispatch" + θ (vxName final) := by
  set wp := gen ^ (fp + fs "da_vector_dispatch" + cert (vxName final) (.n 4))
  let σ : Val := listVal [xb, h0, h1, ctr, word 9223372036854775983 0 0, xb + word 9223372036854775983 0 0,
    o0, o1, wp, o0, o1, wp, o0, o1, wp, o0, o1, wp]
  have h5 : σ (.n 5) = 0 ↔ final = true := hf5
  have hkid := vx_relAtIn fs cert final hxb hctr hch hR (fp + fs "da_vector_dispatch" + 0)
    (D := fun i => fp + fs "da_vector_dispatch" + cert (vxName final) (.n 4) ≤ i ∧
      i < fp + fs "da_vector_dispatch" + cert (vxName final) (.n 4) + 256)
    (fun i h => by rw [Nat.add_zero]; exact h) rd hcv hcl (by rw [Nat.add_zero]; exact hws)
  have h := relAtInW_of_walk (fs := fs) (cert := cert) (w := wId) (σ := σ) (rd := rd)
    (R := R) (D := D) (Dk := fun i => fp + fs "da_vector_dispatch" + cert (vxName final) (.n 4) ≤ i ∧
      i < fp + fs "da_vector_dispatch" + cert (vxName final) (.n 4) + 256)
    (fp := fp) (N := fs (vxName final)) (bws := [fun θ => θ (vxName final)]) find_vd (Or.inl (by decide +kernel)) rfl (vd_walk σ final h5)
    rfl
    (fun e he => by
      have hk : IsInK (σ (.n 5)) := (isInK_add_left (by rw [hxb]; exact isInK_gen_pow b)).mpr
        (by rw [word_g127]; exact isInK_gen_pow 127)
      cases final <;> simp [vdEs] at he <;>
        rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        first | rfl | exact trivial | exact hk)
    (by cases final <;> rfl) (fun q hq => by cases final <;> simp [vdEs, addrs, Ev.addr?] at hq)
    (by
      have hc : calls (vdEs final) = [⟨vxName final, [.n 0, .n 1, .n 2, .n 3],
          if final then [.n 6, .n 7, .n 8] else [.n 12, .n 13, .n 14], true⟩] := by
        cases final <;> rfl
      have e : allocs σ (vdEs final) = [] := by cases final <;> rfl
      rw [hc, e]
      refine ⟨fs (vxName final), 0, R, _, rfl, fun i hi => Or.inl (Or.inl hi), ?_, rfl, fun i hi => Or.inr ⟨rfl, hi⟩⟩
      simp only [↓reduceIte]
      have hr : (if final then [Core.V.n 6, .n 7, .n 8] else [.n 12, .n 13, .n 14]).map σ = [o0, o1, wp] := by
        cases final <;> rfl
      rw [List.sum_nil, Nat.add_zero, hr]
      exact hkid)
    (fun A hA => by cases final <;> simp [vdEs, loadAddrs, Ev.loadAddr?] at hA)
    (fun i hi => Or.inr (hD i hi))
  have e : allocs σ (vdEs final) = [] := by cases final <;> rfl
  simp only [e, List.sum_nil, Nat.add_zero, List.map_cons, List.map_nil, List.sum_cons] at h
  exact h

/-- **`da_vector_dispatch` at `fp`**: the cell at `fp + fs "da_vector_dispatch"`, as
`vx_relAtIn`. -/
theorem vd_relAtIn (fs : String → ℕ) (cert : String → V → ℕ) {xb h0 h1 ctr o0 o1 : E} {ws cv : List E}
    {b c : ℕ} {R D : ℕ → Prop} (hb : b < 128) (hxb : xb = gen ^ b) (hctr : ctr = gen ^ c)
    (hch : ChainCells (h0, h1) (vxBlocks (ws.getD · 0)) (vxMd (decide (b = 127)) (cv.getD · 0)) 96 (o0, o1))
    (hR : ∀ k < 4, R (c + 3 * b + k)) (fp : ℕ)
    (hD : ∀ i, D i → fp + fs "da_vector_dispatch" + cert (vxName (decide (b = 127))) (.n 4) ≤ i ∧
      i < fp + fs "da_vector_dispatch" + cert (vxName (decide (b = 127))) (.n 4) + 256)
    (rd : Reader) (hcv : CellsAt rd (ctr * (xb * xb * xb)) cv) (hcl : cv.length = 4)
    (hws : ∀ k < 256, ∀ v, rd (gpow (fp + fs "da_vector_dispatch" + cert (vxName (decide (b = 127))) (.n 4) + k)) =
      some v → v = ws.getD k 0) :
    RelAtInW fs cert wId rd R D fp (fs "da_vector_dispatch" + fs (vxName (decide (b = 127))))
      "da_vector_dispatch" [xb, h0, h1, ctr]
      [o0, o1, gen ^ (fp + fs "da_vector_dispatch" + cert (vxName (decide (b = 127))) (.n 4))]
      fun θ => θ "da_vector_dispatch" + θ (vxName (decide (b = 127))) :=
  vd_relAtIn' fs cert (decide (b = 127)) (by
    rw [e_add_eq_zero_iff, word_g127, hxb, decide_eq_true_iff]
    exact ⟨fun h => gen_pow_inj' (by omega) (by omega) h, fun h => by rw [h]⟩) hxb hctr hch hR fp hD rd hcv hcl hws

end
end LeanVM.Guest.B1.Digest
