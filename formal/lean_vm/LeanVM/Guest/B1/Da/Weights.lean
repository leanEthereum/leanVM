/-
  LeanVM.Guest.B1.Da.Weights

  `da_weights`' core IR gives the weights: column `h`'s pointer is a run of the dual codeword.
-/

module

public import LeanVM.Guest.B1.Da.Blob
public import LeanVM.Guest.B1.Da.VerifyChk
public import LeanVM.Guest.B1.Main.Facts
import LeanVM.Guest.ValRef
import LeanVM.Guest.Data.ValNames.«da_weights»

/-!
# `da_weights`, sound

`ws_sound`: a run of `da_weights` makes, at every column `h < 128`, `weights[h]` the result of
`da_expand__L6_L7` on `top_leaves[h]` and the offsets shifted by `g^(7h)` (`wsOk`: the offsets'
pointer moves by `g^7` from column to column). `weightsAt_of`: with `da_vector`'s meaning, the
weights are the dual codeword of `z` (`WeightsAt`).
-/

namespace LeanVM.Guest.B1.Da

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Protocol.Verifier
open LeanVM.Guest.B1.Digest LeanVM.Guest.B1.Main

@[expose] public section

variable {rd : Reader}

/-- Column `h`'s expansion, as `da_weights` runs it. -/
def WeightCol (rd : Reader) (tl cf zs off wt : E) (h : ℕ) : Prop :=
  ∃ t lv : E, LoadHolds rd (tl * gen ^ h) 0 t ∧
    coreProgram.Rel rd "da_expand__L6_L7" [t, cf, zs, off * (gen ^ h) ^ 7] [lv] ∧
    LoadHolds rd (wt * gen ^ h) 0 lv

/-- **`da_weights`' run** expands every column. -/
theorem ws_sound {tl cf zs off wt : E}
    (h : coreProgram.Rel rd name% «da_weights» [tl, cf, zs, off] [wt]) :
    ∀ k < 128, WeightCol rd tl cf zs off wt k := by
  have hok := ws_ok
  unfold wsOk at hok
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range] at hok
  obtain ⟨⟨⟨⟨hparams, hbody⟩, hflat⟩, hcp⟩, hall⟩ := hok
  obtain ⟨σ, hpar, hb⟩ := (rel_iff_sem find_da_weights _ _).mp h
  rw [hparams] at hpar
  simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true] at hpar
  obtain ⟨h0, h1, h2, h3⟩ := hpar
  rw [stmtsEqb_sound hbody, holdsList_append] at hb
  obtain ⟨hallS, hret⟩ := holdsList_flat wsP (List.all_eq_true.mpr hflat) _ _ hb
  simp only [Stmt.HoldsList, Stmt.Holds, List.map_cons, List.map_nil] at hret
  have hat := atoms_of_flat hallS
  have hw : σ (.n (val% «da_weights» "weights")) = wt := by
    rw [← copy_sound hcp hat]; simpa using hret
  have hoff : ∀ k < 128, σ (wsOff k) = off * (gen ^ k) ^ 7 := by
    intro k hk
    induction k with
    | zero => simp [wsOff, h3]
    | succ k ih =>
      have hm := (hall (k + 1) hk).2
      simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq] at hm
      rcases hm with hm | ⟨hc, hmul⟩
      · exact absurd hm (by omega)
      rw [isMul_sound hmul hat, Nat.add_sub_cancel, ih (by omega), const_sound hc hat,
        show (128 : ℕ) = 2 ^ 7 from rfl, word_two_pow (by norm_num)]
      ring
  intro k hk
  obtain ⟨⟨⟨hc, hl1⟩, hl2⟩, -⟩ := hall k hk
  refine ⟨σ (wsLeaf k), σ (.n (4 * k + 6)), ?_, ?_, ?_⟩
  · rw [loadHolds_mul_gen_pow, add_zero, ← h0]; exact load_sound hl1 hat
  · have hcall := call_of_flat hallS hc
    simp only [List.map_cons, List.map_nil] at hcall
    rwa [h1, h2, hoff k hk] at hcall
  · rw [loadHolds_mul_gen_pow, add_zero, ← hw]; exact load_sound hl2 hat

/-- **The weights are the dual codeword of `z`**, every column expanded from `da_vector`'s
builders. -/
theorem weightsAt_of {z zs tl cf off wt : E} (hvec : MeaningDaVector rd [z] [zs, tl, cf, off])
    (hcol : ∀ k < 128, WeightCol rd tl cf zs off wt k) : WeightsAt rd z wt := by
  obtain ⟨hzs, htl, hcf, hoff⟩ := hvec
  intro hc hh
  obtain ⟨t, lv, ht, he, hl⟩ := hcol hc hh
  refine ⟨lv, hl, ?_⟩
  rw [loadHolds_mul_gen_pow, add_zero] at ht
  have e8 := runAt_load htl hh ht
  have hE := (da_expand_holds).2 rd _ _ he
  simp only [MeaningDaExpand] at hE
  obtain ⟨F, Z, S, hF, hZ, hS, hrun⟩ := hE
  intro e hel v hv
  rw [hrun.2 e (by norm_num; omega) v hv, e8, ← cellLeaf_eq z hel]
  refine expandLeaf_congr (by norm_num; omega) (fun n n1 n2 ↦ ?_) (fun d hd ↦ ?_) (fun d hd ↦ ?_)
  · exact loadHolds_unique (hF n n1 n2) (hcf n n1 (by norm_num at n2 ⊢; omega))
  · exact loadHolds_unique (hZ d hd) (hzs _ (by omega))
  · have := hS d hd
    rw [← pow_mul, loadHolds_mul_gen_pow] at this
    exact loadHolds_unique this (by
      rw [show hc * 7 + (6 - d) = 7 * hc + (6 - d) by ring]; exact hoff hc hh (6 - d) (by omega))

end
end LeanVM.Guest.B1.Da
