/-
  LeanVM.Guest.B1.Da.WitnessAtTB

  `da_verify` placed on a LeanDA witness, by a tree of its honest shape, within its words bound
  (`dvB`) at the witness's row count and padded log, for the budget.

  The witness and `Da.MatrixWitness.Opens` are Benedikt Wagner's LeanDA formalization, as ported here.
-/

module

public import LeanVM.Guest.B1.Da.DvAt
public import LeanVM.Guest.B1.Da.Witness
public import LeanVM.Guest.Data.NameStrings

/-!
# `da_verify` on a witness, within its bound

`dvBs_le`: `da_verify`'s callees' bounds at the frame sizes within `dvKB`, on the static bounds
(`DvStaticB`). `da_verify_completeAtTB`: for a witness opening `(root, z)`, `da_verify` is complete,
placed at `g_squares = g^s` reading `g^(2^L)` at `g^(s + L)` (`L = wLog w`), by a tree of
`dvNH r L` within `dvB fs SB SK r L` (`r` its rows), returning the root's cells and `z`.
-/

namespace LeanVM.Guest.B1.Da

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Memory
open LeanVM.Guest.Value.Keccak
open LeanVM.Protocol LeanVM.Protocol.Verifier
open LeanVM.Guest.B1.Digest
open LeanVM.Guest.B1 (CompleteAtDTB Returns)

@[expose] public section

variable {fs : String → ℕ} {SB SK : String → ℕ}

theorem clB_mono {f : String} {Bc Bc' t : ℕ} (h : Bc ≤ Bc') : clB fs f Bc t ≤ clB fs f Bc' t := by
  unfold clB
  have := Nat.mul_le_mul_left t (Nat.add_le_add_left h (fs f))
  omega

/-- **`da_verify`'s callees' bounds within `dvKB`**, on the static bounds. -/
theorem dvBs_le (hS : DvStaticB fs SB SK) {r L : ℕ} (hL : L ≤ 10) :
    (dvBs fs SB SK r L).sum ≤ dvKB fs SB SK r L := by
  have hv : vecB fs SK ≤ SB "da_vector" := hS.vec
  have hc : clB fs name% «da_verify_loop1» (colBf fs SK r) 128 ≤ clB fs name% «da_verify_loop1»
      (colB fs SB SK r) 128 :=
    clB_mono (by unfold colBf colB; have := hS.exp; omega)
  simp only [dvBs, dvKB, List.sum_cons, List.sum_nil, dlNames_bang hL]
  omega

variable (fs) (cert : String → V → ℕ)

/-- **`da_verify` is complete, placed, on a witness, by a tree of its honest shape, within
`dvB`.** -/
theorem da_verify_completeAtTB (hrf : Lift.RunsFit fs cert) {w : LeanVM.Da.MatrixWitness}
    {root : Digest} {z : E} (hw : w.Opens root z) (s : ℕ) (hS : DvStaticB fs SB SK) :
    CompleteAtDTB fs cert 16 "da_verify" [(s + wLog w, [gen ^ 2 ^ wLog w])] [gen ^ s]
      (Returns (digestCells root ++ [z]))
      (dvNH w.rows.length (wLog w)) (dvB fs SB SK w.rows.length (wLog w)) := by
  have hr1 := hw.1
  have hr := hw.2.1
  have hL : 2 ^ wLog w = LeanDa.paddedRowCount w.rows.length := rfl
  have hL10 : wLog w ≤ 10 := by
    obtain ⟨hlo, hhi⟩ := nPad_bounds hr1
    have hr' : w.rows.length ≤ 1024 := hr
    have hlt : 2 ^ wLog w < 2 ^ 11 := by
      calc 2 ^ wLog w < 2 * w.rows.length := hL ▸ hhi
        _ ≤ 2 ^ 11 := by norm_num; omega
    have := (Nat.pow_lt_pow_iff_right (by norm_num : 1 < 2)).mp hlt
    omega
  rw [opens_eq hw]
  refine (dv_completeAtB fs cert hrf hS.off hS.l17 hS.l19 hS.l20 hS.l21
    (by rw [← dlNames_bang hL10]; exact hS.dl _ hL10) hr1 hr hL (wSyms_len hw) (wDot hw) s).mono
    ?_ fun _ h => h
  have := dvBs_le hS (r := w.rows.length) hL10
  unfold dvB
  omega

end
end LeanVM.Guest.B1.Da
