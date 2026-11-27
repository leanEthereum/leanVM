/-
  LeanVM.Guest.B1.Gkr.Gls

  `gkr_layers__L{o}`, its loop and `gkr_last_layers__L{r}_L{o}`, soundly: they call every layer
  `j < 4n + r`.
-/

module

public import LeanVM.Guest.B1.Gkr.GlLayer
public import LeanVM.Guest.B1.Gkr.GlCLayers
import LeanVM.Guest.ValRef
import LeanVM.Guest.Data.ValNames.«gkr_layers__L»
import LeanVM.Guest.Data.ValNames.«gkr_layers__L_loop0»

/-!
# The radix-four layers' dispatch, soundly

On the templates of `GlCLayers` (`glcLsBody`, `glcLsLBody`, `glcLastBody`, the chain of layer
calls `glcChain`):

* `glcChain_sound`: the chain calls `gkr_layer__L{p}_L{o}` at `x_j = x0·g^p`, `p < r`;
* `gls_sound`: `gkr_layers__L{o}` at `n_four = g^n`, `rem_g = g^r` calls every layer `j < 4n + r`
  (`GlLay`), its loop the first `4n`, `gkr_last_layers__L{r}_L{o}` the last `r`;
* `gls_lyB`: so every layer `j < 4n + r` is a step of two levels (`LyB`, `gl_layer`).
-/

namespace LeanVM.Guest.B1.Tables

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Protocol LeanVM.Protocol.Verifier
open LeanVM.Guest.B1

@[expose] public section

theorem glcStep_noRet (o : ℕ) (hd : List V) (x0 c0 p : ℕ) :
    Stmt.noRetList (glcStep o hd x0 c0 p) = true := by
  unfold glcStep; split <;> rfl

theorem glcChain_noRet (o : ℕ) (hd : List V) (x0 c0 r : ℕ) :
    Stmt.noRetList (glcChain o hd x0 c0 r) = true :=
  tb_noRetList_flatten_range r _ (glcStep_noRet o hd x0 c0)

section Sem

variable {C : CallRel} {rd : Reader} {σ : Val} {kret : List E → Prop}

/-- **The chain of layer calls, soundly.** -/
theorem glcChain_sound {o : ℕ} {hd : List V} {x0 c0 : ℕ} : ∀ r,
    Stmt.HoldsList C rd σ (glcChain o hd x0 c0 r) True kret →
      (∀ p < r, σ (.n (glcXj x0 c0 p)) = σ (.n x0) * gen ^ p) ∧
      ∀ p < r, C (glName p o) (hd.map σ ++ [σ (.n x0) * gen ^ p, σ (.n 5), σ (.n 6), σ (.n 7),
        σ (.n 8)]) []
  | 0, _ => ⟨fun _ h => absurd h (by omega), fun _ h => absurd h (by omega)⟩
  | r + 1, h => by
    rw [glcChain, List.range_succ, List.map_append, List.flatten_append,
      tb_holdsList_append_noRet (tb_noRetList_flatten_range r _ (glcStep_noRet o hd x0 c0))] at h
    obtain ⟨ih1, ih2⟩ := glcChain_sound r h.1
    have h2 := h.2
    simp only [List.map_cons, List.map_nil, List.flatten_cons, List.flatten_nil, List.append_nil,
      glcStep] at h2
    have hx : σ (.n (glcXj x0 c0 r)) = σ (.n x0) * gen ^ r := by
      unfold glcXj
      split
      · rename_i h0; subst h0; rw [pow_zero, mul_one]
      · rename_i h0
        simp only [h0, ↓reduceIte, List.cons_append, List.nil_append, Stmt.HoldsList, Stmt.Holds,
          Atom.Holds] at h2
        obtain ⟨c, m, -⟩ := h2
        rw [m, c, word_gen, ih1 (r - 1) (by omega), mul_assoc, ← pow_succ,
          Nat.sub_add_cancel (by omega)]
    have hcall : C (glName r o) (hd.map σ ++ [σ (.n x0) * gen ^ r, σ (.n 5), σ (.n 6), σ (.n 7),
        σ (.n 8)]) [] := by
      split at h2
      · simp only [List.nil_append, Stmt.HoldsList, Stmt.Holds, List.map_append, List.map_cons,
          List.map_nil] at h2
        rw [← hx]; exact h2.1
      · simp only [List.cons_append, List.nil_append, Stmt.HoldsList, Stmt.Holds,
          List.map_append, List.map_cons, List.map_nil] at h2
        rw [← hx]; exact h2.2.2.1
    refine ⟨fun p hp => ?_, fun p hp => ?_⟩
    · rcases Nat.lt_succ_iff_lt_or_eq.mp hp with hp | rfl
      · exact ih1 p hp
      · exact hx
    · rcases Nat.lt_succ_iff_lt_or_eq.mp hp with hp | rfl
      · exact ih2 p hp
      · exact hcall

end Sem

section Calls

variable {rd : Reader}

theorem gls_last {o r : ℕ} (ho : o < 2) (hr : r < 4) {layers rounds pts xm x4 start gmu tabs stream : E}
    {rets : List E}
    (h : coreProgram.Rel rd (glcLastN r o) [layers, rounds, pts, xm, x4, start, gmu, tabs, stream]
      rets) :
    ∀ p < r, coreProgram.Rel rd (glName p o) [layers, rounds, pts, xm, x4 * gen ^ p, start, gmu,
      tabs, stream] [] := by
  obtain ⟨fn, hf, hp, hb⟩ := glcFnCheck_sound ((glc_layers_check o ho).2.2 r hr)
  obtain ⟨σ, hpar, hbody⟩ := (rel_iff_sem hf _ _).mp h
  rw [hp] at hpar
  simp only [glcPar9, List.range_succ, List.range_zero, List.map_cons, List.map_nil,
    List.nil_append, List.cons_append, List.cons.injEq, and_true] at hpar
  obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ := hpar
  rw [hb, glcLastBody, holdsList_append, holdsList_noRet _ (glcChain_noRet ..)] at hbody
  intro p hp
  simpa using (glcChain_sound r hbody.1).2 p hp

/-- An iteration of `gkr_layers__L{o}`'s loop: its four layers, and the next iteration. -/
theorem glsl_step {o : ℕ} (ho : o < 2) {N layers rounds pts start gmu tabs stream : E} (d : ℕ)
    (x : E) (h : coreProgram.relN rd (d + 1) (glcLsLN o)
      (x :: [N, layers, rounds, pts, start, gmu, tabs, stream]) []) :
    (∀ p < 4, coreProgram.Rel rd (glName p o) [layers, rounds, pts, x, x * x * (x * x) * gen ^ p,
      start, gmu, tabs, stream] []) ∧
      (x * gen + N ≠ 0 → coreProgram.relN rd d (glcLsLN o)
        (x * gen :: [N, layers, rounds, pts, start, gmu, tabs, stream]) []) := by
  obtain ⟨fn, hf, σ, hpar, hbody⟩ := h
  obtain ⟨fn', hf', hp, hb⟩ := glcFnCheck_sound (glc_layers_check o ho).2.1
  rw [hf] at hf'
  obtain rfl := Option.some.inj hf'
  rw [hp] at hpar
  simp only [glcPar9, List.range_succ, List.range_zero, List.map_cons, List.map_nil,
    List.nil_append, List.cons_append, List.cons.injEq, and_true] at hpar
  obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ := hpar
  rw [hb, glcLsLBody, holdsList_append, holdsList_append,
    holdsList_noRet _ (by rfl : Stmt.noRetList [.atom (.mul (.n (valf% «gkr_layers» «_loop0» "x4~0")) (.n (valf% «gkr_layers» «_loop0» "x_m")) (.n (valf% «gkr_layers» «_loop0» "x_m"))),
      .atom (.mul (.n (valf% «gkr_layers» «_loop0» "x4")) (.n (valf% «gkr_layers» «_loop0» "x4~0")) (.n (valf% «gkr_layers» «_loop0» "x4~0")))] = true),
    holdsList_noRet _ (glcChain_noRet ..)] at hbody
  obtain ⟨hpre, hch, hpost⟩ := hbody
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds, and_true] at hpre
  obtain ⟨m9, m10⟩ := hpre
  obtain ⟨-, hcalls⟩ := glcChain_sound 4 hch
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds, List.map_cons, List.map_nil] at hpost
  obtain ⟨c17, m18, a19, c20, m21, -, hnext, -⟩ := hpost
  rw [word_gen] at c17 c20
  refine ⟨fun p hp => ?_, fun hne => ?_⟩
  · have := relN_le_rel coreProgram d _ _ _ (hcalls p hp)
    simpa [m10, m9] using this
  · have := hnext (by rw [a19, m18, c17]; exact hne)
    rw [m21, c20] at this
    exact this

/-- **`gkr_layers__L{o}`, soundly**: at `n_four = g^n`, `rem_g = g^r`, every layer `j < 4n + r`
is called. -/
theorem gls_sound {o n r : ℕ} (ho : o < 2) (hr : r < 4) (hn : n < 2 ^ 30)
    {layers rounds pts start gmu tabs stream : E} {rets : List E}
    (h : coreProgram.Rel rd (glcLsN o) [layers, rounds, pts, gen ^ n, gen ^ r, start, gmu, tabs,
      stream] rets) :
    ∀ j < 4 * n + r, GlLay rd o layers rounds pts start gmu tabs stream j := by
  obtain ⟨fn, hf, hp, hb⟩ := glcFnCheck_sound (glc_layers_check o ho).1
  obtain ⟨σ, hpar, hbody⟩ := (rel_iff_sem hf _ _).mp h
  rw [hp] at hpar
  simp only [glcPar9, List.range_succ, List.range_zero, List.map_cons, List.map_nil,
    List.nil_append, List.cons_append, List.cons.injEq, and_true] at hpar
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8⟩ := hpar
  rw [hb, glcLsBody] at hbody
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds, List.map_cons, List.map_nil] at hbody
  obtain ⟨c9, a10, c11, -, hloop, m12, m13, ⟨jj, hjj, hx, hlast⟩, -⟩ := hbody
  rw [word_one] at c9 c11
  -- the last `r` layers
  have hjr : jj = r := by
    simp only [List.length_cons, List.length_nil] at hjj
    rw [h4, ← gen_pow_eq_ofK] at hx
    exact (gen_pow_inj (by omega) (by omega) hx).symm
  subst hjr
  have hlast' : coreProgram.Rel rd (glcLastN jj o) [layers, rounds, pts, gen ^ n, gen ^ (4 * n),
      start, gmu, tabs, stream] [σ (.n (valf% «gkr_layers» "done"))] := by
    have e : [glcLastN 0 o, glcLastN 1 o, glcLastN 2 o, glcLastN 3 o][jj] = glcLastN jj o := by
      interval_cases jj <;> rfl
    rw [e, m13, m12, h0, h1, h2, h3, h5, h6, h7, h8,
      show gen ^ n * gen ^ n * (gen ^ n * gen ^ n) = gen ^ (4 * n) by ring] at hlast
    exact hlast
  have L1 := gls_last ho hr hlast'
  -- the loop's `4n`
  intro j hj
  unfold GlLay
  rcases Nat.lt_or_ge j (4 * n) with hjn | hjn
  · have hne : σ (.n (valf% «gkr_layers» "s0#1")) ≠ 0 := by
      rw [a10, c9, h3]
      intro h0'
      have := gen_pow_inj (by omega) (by omega) ((e_add_eq_zero_iff.mp h0').symm.trans
        (pow_zero gen).symm)
      omega
    have hrel := hloop hne
    rw [c11, h3, h0, h1, h2, h5, h6, h7, h8, ← pow_zero gen] at hrel
    obtain ⟨m', -, hN, hall⟩ := tb_loop_sound
      (B := fun x ↦ ∀ p < 4, coreProgram.Rel rd (glName p o) [layers, rounds, pts, x,
        x * x * (x * x) * gen ^ p, start, gmu, tabs, stream] [])
      (fun d x hx => glsl_step ho d x hx) 0 hrel
    have hnm : n ≤ m' := by
      by_contra hc
      have := gen_pow_inj (by omega) (by omega) hN
      omega
    have := hall (j / 4) (by omega) (by omega) (j % 4) (by omega)
    rwa [show gen ^ (j / 4) * gen ^ (j / 4) * (gen ^ (j / 4) * gen ^ (j / 4)) * gen ^ (j % 4) =
      gen ^ j by simp only [← pow_add]; congr 1; omega] at this
  · have := L1 (j - 4 * n) (by omega)
    rw [← pow_add, show 4 * n + (j - 4 * n) = j by omega] at this
    rwa [show j % 4 = j - 4 * n by omega, show j / 4 = n by omega]

/-- **Every layer below `4n + r` is a step of two levels.** -/
theorem gls_lyB {o n r : ℕ} (ho : o < 2) (hr : r < 4) (hn : 4 * n + r < 2 ^ 30)
    {layers rounds pts gmu tabs stream : E} {rets : List E}
    (h : coreProgram.Rel rd (glcLsN o) [layers, rounds, pts, gen ^ n, gen ^ r, gen ^ (2 - o), gmu,
      tabs, stream] rets) :
    ∀ j < 4 * n + r, LyB rd o layers pts j := by
  intro j hj s cur st pos hslot
  have hL := gls_sound ho hr (by omega) h j hj
  unfold GlLay at hL
  obtain ⟨m, p, hp, rfl⟩ : ∃ m p, p < 4 ∧ j = 4 * m + p :=
    ⟨j / 4, j % 4, Nat.mod_lt _ (by omega), by omega⟩
  rw [show (4 * m + p) % 4 = p by omega, show (4 * m + p) / 4 = m by omega] at hL
  exact gl_layer hp ho hL rfl rfl rfl (by omega) hslot

end Calls

end
end LeanVM.Guest.B1.Tables
