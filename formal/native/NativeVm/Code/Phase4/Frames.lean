module

public import NativeVm.Code.Phase4.Glue

/-!
# The working area's words through a block

`WF env W s s'`: every word `69 ≤ k < 85438` of the working area outside `W` is kept. A transcript
gadget gives it for any `W` (`WF.ofKeeps`: it writes only the transcript's words), a block of
phase 4's code for the words it writes (`WF.ofWr`). The facts a block passes on survive it when
they lie outside `W` (`EWAt.wf`, `EWArr.wf`, `WF.word`, `WF.same`). The phase's own frame (`Fr`)
follows from `Wr` (`Fr.ofWr`, `Only.ofWr`).
-/

@[expose] public section

namespace NativeVm.Code.P4

open Native NativeVm.Model NativeVm.Transcript NativeVm.Field LeanVM.Parameters

variable {env : Env} {W V : Nat → Prop} {s s' s'' : QState}

/-- The working area's words outside `W` are kept. -/
def WF (env : Env) (W : Nat → Prop) (s s' : QState) : Prop :=
  ∀ k, 69 ≤ k → k < 85438 → ¬ W k → s'.mem (wd env.work k) = s.mem (wd env.work k)

theorem WF.refl (W : Nat → Prop) (s : QState) : WF env W s s := fun _ _ _ _ ↦ rfl

theorem WF.trans (h : WF env W s s') (h' : WF env W s' s'') : WF env W s s'' :=
  fun k h1 h2 hk ↦ (h' k h1 h2 hk).trans (h k h1 h2 hk)

theorem WF.mono (h : WF env W s s') (hWV : ∀ k, W k → V k) : WF env V s s' :=
  fun k h1 h2 hk ↦ h k h1 h2 fun hw ↦ hk (hWV k hw)

theorem WF.ofWr (h : Wr env.work W s s') (hW : ∀ k, W k → k < 85438) : WF env W s s' :=
  fun k _ h2 hk ↦ h _ fun k' hk' e ↦ by
    rw [wd_inj (by omega) (by have := hW k' hk'; omega)] at e
    subst e; exact hk hk'

theorem WF.ofKeeps (h4 : Env4 env) (hk : Keeps clobbers (Foot env) s s') : WF env W s s' :=
  fun k h1 h2 _ ↦ hk.mem _ (h4.notFoot k (by rw [tWorkWords_val]; exact h1)
    (by rw [dataEnd_val]; exact h2))

theorem WF.ofEq (hm : s'.mem = s.mem) : WF env W s s' := fun _ _ _ _ ↦ by rw [hm]

theorem WF.word (h : WF env W s s') {k : Nat} (h1 : 69 ≤ k) (h2 : k < 85438) (hk : ¬ W k)
    {v : Option UInt64} (hv : s.mem (wd env.work k) = v) : s'.mem (wd env.work k) = v := by
  rw [h k h1 h2 hk, hv]

theorem EWAt.wf (h : WF env W s s') {j : Nat} {x : EW} (hx : EWAt s.mem (wd env.work j) x)
    (h1 : 69 ≤ j) (h2 : j + 1 < 85438) (hW : ¬ W j ∧ ¬ W (j + 1)) : EWAt s'.mem (wd env.work j) x := by
  unfold EWAt at hx ⊢
  rw [wd_wd] at hx ⊢
  exact ⟨h.word h1 (by omega) hW.1 hx.1, h.word (by omega) h2 hW.2 hx.2⟩

theorem EWArr.wf (h : WF env W s s') {j : Nat} {xs : Array EW} (hx : EWArr s.mem (wd env.work j) xs)
    (h1 : 69 ≤ j) (h2 : j + 2 * xs.size ≤ 85438) (hW : ∀ i < 2 * xs.size, ¬ W (j + i)) :
    EWArr s'.mem (wd env.work j) xs := fun i hi ↦ by
  have := hx i hi
  rw [wd_wd] at this ⊢
  exact EWAt.wf h this (by omega) (by omega)
    ⟨hW (2 * i) (by omega), by rw [Nat.add_assoc]; exact hW (2 * i + 1) (by omega)⟩

theorem NatAt.wf (h : WF env W s s') {j n : Nat} (hx : NatAt s.mem (wd env.work j) n)
    (h1 : 69 ≤ j) (h2 : j < 85438) (hW : ¬ W j) : NatAt s'.mem (wd env.work j) n :=
  ⟨hx.1, h.word h1 h2 hW hx.2⟩

/-- A region outside `W` is kept. -/
theorem WF.same (h : WF env W s s') {q : Region} (h1 : 69 ≤ q.off) (h2 : q.off + q.size ≤ 85438)
    (hW : ∀ k, W k → k < q.off ∨ q.off + q.size ≤ k) : Same s.mem s'.mem (q.at env.work) q.size :=
  fun k hk ↦ by
    rw [Region.at, wd_wd]
    exact h _ (by omega) (by omega) fun hw ↦ by have := hW _ hw; omega

/-- `WF` from the phase's frame. -/
theorem WF.ofFr (h4 : Env4 env) {ws : List Region} {rs : List Reg64} (hf : Fr env ws rs s s')
    (hm : Mine ws) : WF env (fun k ↦ ∃ r ∈ ws, r.off ≤ k ∧ k < r.stop) s s' :=
  fun k h1 h2 hk ↦ hf.mem _ (h4.notFoot k (by rw [tWorkWords_val]; exact h1)
    (by rw [dataEnd_val]; exact h2)) fun r hr ⟨j, hj, e⟩ ↦ by
      have := hm r hr
      unfold Region.stop at this
      rw [tWorkWords_val, dataEnd_val] at this
      rw [wd_inj (by omega) (by omega)] at e
      exact hk ⟨r, hr, by omega, by unfold Region.stop; omega⟩

/-! ## The phase's frame from `Wr` -/

/-- Writes inside the regions `ws`. -/
def InRs (ws : List Region) (W : Nat → Prop) : Prop :=
  ∀ k, W k → ∃ r ∈ ws, r.off ≤ k ∧ k < r.stop

theorem Only.ofWr {ws : List Region} (h : Wr env.work W s s') (hW : InRs ws W) :
    Only env ws s s' := fun a ha ↦ h a fun k hk e ↦ by
  obtain ⟨r, hr, h1, h2⟩ := hW k hk
  exact ha r hr (e ▸ Region.in_wd h1 h2)

theorem Fr.ofWr {ws : List Region} {rs : List Reg64} (h : Wr env.work W s s') (hW : InRs ws W)
    (hd : DomEq s s') (hr : RegsFrame rs s s') (hrdi : Reg64.rdi ∉ rs) : Fr env ws rs s s' :=
  (Only.ofWr h hW).fr (hr .rdi hrdi) hr hd

/-- A word of the scratch region. -/
theorem inS {k : Nat} (h1 : 52670 ≤ k) (h2 : k < 52670 + 32768) :
    ∃ r ∈ [evalsR, scratchR], r.off ≤ k ∧ k < r.stop :=
  ⟨scratchR, by simp, by rw [scratchR_off]; exact h1, by
    show k < scratchR.off + scratchR.size; rw [scratchR_off]; exact h2⟩

/-- A word of the evaluations' region. -/
theorem inE {k : Nat} (h1 : 14093 ≤ k) (h2 : k < 14093 + 1476) :
    ∃ r ∈ [evalsR, scratchR], r.off ≤ k ∧ k < r.stop :=
  ⟨evalsR, by simp, by rw [evalsR_off]; exact h1, by
    show k < evalsR.off + evalsR.size; rw [evalsR_off]; exact h2⟩

end NativeVm.Code.P4
