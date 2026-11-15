/-
  LeanVM.Guest.B1.Da.RootsTree

  The roots' tree's arms `da_roots_tree__L{k}`, `da_pad` and its loop `da_pad_loop0`: what a run
  establishes (G:4547-4561).
-/

module

public import LeanVM.Guest.B1.Da.VerifyChk
public import LeanVM.Guest.B1.Da.Help
public import LeanVM.Guest.Data.NameStrings

/-!
# The roots' tree (G:4547-4561)

`da_roots_tree__L{k}(roots, n_blob_g, gap_g)` (`rtBody k`): `da_pad`, then `da_levels` over the
`2^k` roots. `da_pad` (`padBody`) runs `da_pad_loop0` from `1` while `gap_g ≠ 1`, each iteration
writing `DA_PAD_BLOB`'s cells at `roots·n_blob_g²·x²`. `rt_sound`: at `gap_g = g^d`, every padding
blob `j < d`'s cells and the levels' run.
-/

namespace LeanVM.Guest.B1.Da

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Value.Keccak
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Guest.B1.Digest LeanVM.Guest.B1.Main

@[expose] public section

variable {rd : Reader}

theorem padL_step {x : E} {ps : List E} (h : coreProgram.Rel rd name% «da_pad_loop0» (x :: ps) []) :
    (∀ N roots nb, ps = [N, roots, nb] →
      LoadHolds rd (roots * nb ^ 2 * x ^ 2) 0 (digestHalves daPadBlobDigest).1 ∧
      LoadHolds rd (roots * nb ^ 2 * x ^ 2) 1 (digestHalves daPadBlobDigest).2) ∧
      (x * gen + ps.headD 0 ≠ 0 → coreProgram.Rel rd name% «da_pad_loop0» (x * gen :: ps) []) := by
  have hok := padL_ok
  simp only [Bool.and_eq_true, decide_eq_true_eq, padLOk] at hok
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨hshape, hlen⟩, hm4⟩, hm5⟩, hm6⟩, hm7⟩, hc8⟩, hl8⟩, hc9⟩, hl9⟩ := hok
  obtain ⟨σ, hx, hps, hall, hnext⟩ :=
    loop_stepF (find_of_idx dv_loops_idx.2) hshape h
  refine ⟨fun N roots nb hN ↦ ?_, hnext⟩
  have hat := atoms_of_flat hall
  have hpar : (coreProgram.getD idx% «da_pad_loop0» default).params = [V.n 0, V.n 1, V.n 2,
      V.n 3] := by
    rw [loop_params hshape hlen]; rfl
  rw [hpar, hN] at hps
  simp only [List.tail_cons, List.map_cons, List.map_nil, List.cons.injEq, and_true] at hps
  obtain ⟨-, h2, h3⟩ := hps
  have p7 : σ (.n 7) = roots * nb ^ 2 * x ^ 2 := by
    rw [isMul_sound hm7 hat, isMul_sound hm5 hat, isMul_sound hm6 hat, isMul_sound hm4 hat, h2, h3,
      hx, sq, sq]
  have c8 := hasAtom_sound hc8 hat
  have c9 := hasAtom_sound hc9 hat
  simp only [Atom.Holds] at c8 c9
  have l8 := load_sound hl8 hat
  have l9 := load_sound hl9 hat
  rw [p7, c8] at l8
  rw [p7, c9] at l9
  have hp := daPadBlob_cells
  simp only [Prod.ext_iff] at hp
  rw [← hp.1, ← hp.2]
  exact ⟨l8, l9⟩

/-- **`da_pad`'s run** at `gap = g^d`: the padding blobs `j < d`. -/
theorem pad_sound {roots nb : E} {d : ℕ} (hd : d < ordG)
    (hrel : coreProgram.Rel rd "da_pad" [roots, nb, gen ^ d] []) :
    ∀ j < d, LoadHolds rd (roots * nb ^ 2 * (gen ^ j) ^ 2) 0 (digestHalves daPadBlobDigest).1 ∧
      LoadHolds rd (roots * nb ^ 2 * (gen ^ j) ^ 2) 1 (digestHalves daPadBlobDigest).2 := by
  have hok := pad_ok
  unfold padOk at hok
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hok
  obtain ⟨hparams, hbody⟩ := hok
  obtain ⟨σ, hpar, hb⟩ := (rel_iff_sem find_da_pad _ _).mp hrel
  rw [stmtsEqb_sound hbody] at hb
  rw [hparams] at hpar
  simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true] at hpar
  obtain ⟨h0, h1, h2⟩ := hpar
  simp only [padBody, Stmt.HoldsList, Stmt.Holds, Atom.Holds, List.map_cons, List.map_nil] at hb
  obtain ⟨c3, a4, c5, -, hcall, -⟩ := hb
  refine loop_sound (f := name% «da_pad_loop0») (ps := [gen ^ d, roots, nb]) hd rfl
    (fun y hy => by
      obtain ⟨k1, k2⟩ := padL_step hy
      exact ⟨k1 _ _ _ rfl, k2⟩)
    (fun hne => ?_)
  have := hcall (by rw [a4, c3, word_one, h2]; exact hne)
  rw [c5, word_one, h2, h0, h1] at this
  exact this

/-- **The roots' tree's arm `k`'s run** at `gap = g^d`: the padding blobs `j < d` and the levels'
run. -/
theorem rt_sound {k : ℕ} (hk : k < 11) {roots nb c0 c1 : E} {d : ℕ} (hd : d < ordG)
    (hrel : coreProgram.Rel rd (rtName k) [roots, nb, gen ^ d] [c0, c1]) :
    (∀ j < d, LoadHolds rd (roots * nb ^ 2 * (gen ^ j) ^ 2) 0 (digestHalves daPadBlobDigest).1 ∧
      LoadHolds rd (roots * nb ^ 2 * (gen ^ j) ^ 2) 1 (digestHalves daPadBlobDigest).2) ∧
      coreProgram.Rel rd (daLevelsName k) [roots] [c0, c1] := by
  obtain ⟨hf, hok⟩ := rt_find hk
  unfold rtOk at hok
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hok
  obtain ⟨hparams, hbody⟩ := hok
  obtain ⟨σ, hpar, hb⟩ := (rel_iff_sem hf _ _).mp hrel
  rw [stmtsEqb_sound hbody] at hb
  rw [hparams] at hpar
  simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true] at hpar
  obtain ⟨h0, h1, h2⟩ := hpar
  simp only [rtBody, Stmt.HoldsList, Stmt.Holds, Atom.Holds, List.map_cons, List.map_nil] at hb
  obtain ⟨hpad, hlv, cp5, cp6, hret⟩ := hb
  simp only [List.cons.injEq, and_true] at hret
  rw [h0, h1, h2] at hpad
  rw [h0] at hlv
  refine ⟨pad_sound hd hpad, ?_⟩
  rw [← hret.1, ← hret.2, cp5, cp6]
  exact hlv

end
end LeanVM.Guest.B1.Da
