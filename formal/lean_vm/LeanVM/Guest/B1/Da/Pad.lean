/-
  LeanVM.Guest.B1.Da.Pad

  `da_pad` and its loop `da_pad_loop0`: what a run establishes.
-/

module

public import LeanVM.Guest.B1.Da.VerifyChk
public import LeanVM.Guest.B1.Da.Help
public import LeanVM.Guest.Data.NameStrings
import LeanVM.Guest.ValRef
import LeanVM.Guest.Data.ValNames.«da_pad_loop0»
import LeanVM.Guest.B1.Common.Vc

/-!
# The padding blobs

`da_pad(roots, n_blob_g, gap_g)` (`dpadBody`) runs `da_pad_loop0` from `1` while `gap_g ≠ 1`, each
iteration writing `DA_PAD_BLOB`'s cells at `roots·n_blob_g²·x²`. `pad_sound`: at `gap_g = g^d`,
every padding blob `j < d`'s cells.
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
  have hpar : (coreProgram.getD idx% «da_pad_loop0» default).params = [V.n (val% «da_pad_loop0» "xd"), V.n (val% «da_pad_loop0» "bound"), V.n (val% «da_pad_loop0» "roots"),
      V.n (val% «da_pad_loop0» "n_blob_g")] := by
    rw [loop_params hshape hlen]; rfl
  rw [hpar, hN] at hps
  simp only [List.tail_cons, List.map_cons, List.map_nil, List.cons.injEq, and_true] at hps
  obtain ⟨-, h2, h3⟩ := hps
  have p7 : σ (.n (val% «da_pad_loop0» "pad")) = roots * nb ^ 2 * x ^ 2 := by
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
  revert hrel
  rw [rel_iff_fnSem find_da_pad]
  vc [word_one]
  rintro ⟨-, hcall, -⟩
  exact loop_sound (f := name% «da_pad_loop0») (ps := [gen ^ d, roots, nb]) hd rfl
    (fun y hy => by
      obtain ⟨k1, k2⟩ := padL_step hy
      exact ⟨k1 _ _ _ rfl, k2⟩) hcall

end
end LeanVM.Guest.B1.Da
