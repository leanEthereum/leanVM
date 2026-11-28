/-
  LeanVM.Guest.B1.VsC.VsOrcBnd

  The phase boundary `Bnd` through a phase that adds quiet posts.
-/

module

public import LeanVM.Guest.B1.VsC.VsOrcSpec

/-!
# `Bnd` through quiet phases

`verify_sub`'s honest pops (`vsPs`) are empty from entry `13` to `29` (between `certify_stack`'s stack hints
and the Merkle hints), so a phase whose callees all pop nothing (`PostQuiet`) keeps `Bnd`'s prefix of the
honest pops there: **`VsCtx.Bnd.quiet`**, with the cursor moving forward and the words kept.
-/

namespace LeanVM.Guest.B1.VsC

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Memory LeanVM.Guest.B1
open LeanVM.Guest.Complete LeanVM.Guest.B1.Fwd LeanVM.Node LeanVM.Protocol LeanVM.Protocol.Verifier

@[expose] public section

theorem vsPs_length_ge (σ : Val) (ch stk mk : List Pop) : 32 ≤ (vsPs σ ch stk mk).length := by
  unfold vsPs; split_ifs <;> simp

theorem vsPs_get_nil (σ : Val) (ch stk mk : List Pop) {j : ℕ} (h1 : 13 ≤ j) (h2 : j ≤ 29) :
    (vsPs σ ch stk mk)[j]? = some [] := by
  unfold vsPs
  split_ifs <;> interval_cases j <;> rfl

theorem forall₂_quiet {rd : Reader} : ∀ Qs : List (Reader → Tree → Prop), (∀ Q ∈ Qs, Q = PostQuiet) →
    List.Forall₂ (fun Q P => ∀ t, Q rd t → PopsPost P rd t) Qs (List.replicate Qs.length [])
  | [], _ => List.Forall₂.nil
  | Q :: Qs, h => by
    rw [List.length_cons, List.replicate_succ]
    refine List.Forall₂.cons (fun t hq => ?_) (forall₂_quiet Qs fun Q hQ => h Q (List.mem_cons_of_mem _ hQ))
    rw [h Q List.mem_cons_self] at hq
    exact popsPost_quiet hq

/-- **Quiet posts extend the honest pops' prefix** between entries `13` and `30`. -/
theorem vsPsH_quiet {rd : Reader} {seed : Digest} {c : Child} {σ : Val} {Qs Qs' : List (Reader → Tree → Prop)}
    (h : List.Forall₂ (fun Q P => ∀ t, Q rd t → PopsPost P rd t) Qs ((vsPsH seed c σ).take Qs.length))
    (hl : 13 ≤ Qs.length) (hl' : Qs.length + Qs'.length ≤ 30) (hq : ∀ Q ∈ Qs', Q = PostQuiet) :
    List.Forall₂ (fun Q P => ∀ t, Q rd t → PopsPost P rd t) (Qs ++ Qs')
      ((vsPsH seed c σ).take (Qs ++ Qs').length) := by
  have hlen := h.length_eq
  obtain ⟨ch, stk, mk, hL⟩ : ∃ ch stk mk, vsPsH seed c σ = vsPs σ ch stk mk := by
    unfold vsPsH at hlen ⊢
    rcases hA : announcedLayoutAndRate guestBytecode c.proof.stream with _ | ⟨layout, r⟩
    · exfalso; simp [hA] at hlen; simp [hlen] at hl
    · exact ⟨_, _, _, rfl⟩
  rw [hL] at h ⊢
  have hge := vsPs_length_ge σ ch stk mk
  rw [List.length_append, List.take_add]
  refine List.rel_append h ?_
  have e : ((vsPs σ ch stk mk).drop Qs.length).take Qs'.length = List.replicate Qs'.length [] := by
    rw [List.eq_replicate_iff]
    refine ⟨by simp; omega, fun b hb => ?_⟩
    obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hb
    have hi' : i < Qs'.length := by simp at hi; omega
    have g := vsPs_get_nil σ ch stk mk (j := Qs.length + i) (by omega) (by omega)
    rw [List.getElem_take, List.getElem_drop]
    rw [List.getElem?_eq_getElem (by omega)] at g
    exact Option.some.inj g
  rw [e]
  exact forall₂_quiet Qs' hq

/-- **`Bnd` through a quiet phase**: the `HeapBuf` cursor kept, the callees' cursor forward, words kept, the
posts added quiet, inside the honest pops' empty stretch. -/
theorem VsCtx.Bnd.quiet {x : VsCtx} {st : St} (hb : x.Bnd st) {kc : ℕ} {O : Reader → Prop} {D : ℕ → Prop}
    {Qs' : List (Reader → Tree → Prop)} (hkc : st.kc ≤ kc) (hO : ∀ rd, O rd → st.O rd)
    (hl : 13 ≤ st.Qs.length) (hl' : st.Qs.length + Qs'.length ≤ 30) (hq : ∀ Q ∈ Qs', Q = PostQuiet) :
    x.Bnd ⟨st.a, kc, O, D, st.Qs ++ Qs'⟩ :=
  ⟨hb.ha, le_trans hb.hkc hkc, fun rd h => hb.hO rd (hO rd h),
    fun rd hl0 hp ho => vsPsH_quiet (hb.hQ rd hl0 hp (hO rd ho)) hl hl' hq⟩

end
end LeanVM.Guest.B1.VsC
