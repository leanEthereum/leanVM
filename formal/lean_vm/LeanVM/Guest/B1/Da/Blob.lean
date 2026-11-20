/-
  LeanVM.Guest.B1.Da.Blob

  `da_verify_blob` and its cell loop `da_verify_blob_loop0`: what a run of a blob establishes
-/

module

public import LeanVM.Guest.B1.Da.BlobChk
public import LeanVM.Guest.B1.Da.VectorHolds
public import LeanVM.Guest.B1.Da.Help
public import LeanVM.Guest.B1.Main.LoopsC
public import LeanVM.Guest.Data.NameStrings
import LeanVM.Guest.ValRef
import LeanVM.Guest.Data.ValNames.«da_verify_blob»
import LeanVM.Guest.Data.ValNames.«da_verify_blob_loop0»

/-!
# `da_verify_blob`

`da_verify_blob(weights)`: a fresh region `base`, its running sum's first word (`512`) zero, then
`da_verify_blob_loop0` over the cells `h < 128`: a `da_verify_cell` run on `weights[h]`, its sum
added to the running sum (word `512 + h` to `513 + h`), its digest the tree's leaf `h` (words `2h`,
`2h + 1`); the running sum's last word (`640`) is zero, and the root of the region's tree is
returned. `blob_ok` and `c_ok` check the bodies (kernel evaluation in `BlobChk`); `blob_stepW` is a
blob's run under a call relation that unfolds at a frame map `Vm`, on weights that are the dual
codeword of `z` (`WeightsAt`), the symbols those of the cell checks' frames (`blobSyms`): they are
orthogonal to the dual codeword, and the returned cells are the root of their digests' tree.
-/

namespace LeanVM.Guest.B1.Da

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Verifier
open LeanVM.Guest.B1.Digest LeanVM.Guest.B1.Main

@[expose] public section

variable {rd : Reader} {C : CallRel} {Vm : FrameMap}

/-- **A loop from `g^a`**, under `C`: a run at `g^a` gives the body at every `g^j`, `a ≤ j < m`. -/
theorem loop_fromC {f : String} {ps : List E} {N : E} {m a : ℕ} {B : E → Prop}
    (hm : m < ordG) (hN : N = gen ^ m)
    (hstep : ∀ x, C f (x :: ps) [] → B x ∧ (x * gen + N ≠ 0 → C f (x * gen :: ps) []))
    (h : C f (gen ^ a :: ps) []) : ∀ j, a ≤ j → j < m → B (gen ^ j) := by
  have key : ∀ t k, k + t = m → C f (gen ^ k :: ps) [] →
      ∀ j, k ≤ j → j < m → B (gen ^ j) := by
    intro t
    induction t with
    | zero => intro k hk _ j h1 h2; omega
    | succ t ih =>
      intro k hk hrun j h1 h2
      obtain ⟨hB, hnext⟩ := hstep _ hrun
      rcases Nat.eq_or_lt_of_le h1 with rfl | hlt
      · exact hB
      · have hne : gen ^ k * gen + N ≠ 0 := by
          intro he
          rw [gen_pow_add_eq_zero_iff, hN] at he
          have := gen_pow_inj hm (by unfold ordG at hm; omega) he
          omega
        have := hnext hne
        rw [gen_pow_mul_gen] at this
        exact ih (k + 1) (by omega) this j hlt h2
  intro j h1 h2
  exact key (m - a) a (by omega) h j h1 h2

/-! ## The cell loop -/

/-- **Cell `x` of the blob, at the loop's valuation `σc`**: `weights[x]` is `σc (.n 4)`, a
`da_verify_cell` call on it, its sum `σc (.n 7)` added to the running sum at `base·x`, its digest
`σc (.n 5)`, `σc (.n 6)` the leaf at `base·x²`. -/
def CellStepB (C : CallRel) (rd : Reader) (σc : Val) (w base x : E) : Prop :=
  LoadHolds rd (w * x) 0 (σc (.n (val% «da_verify_blob_loop0» "d0~4"))) ∧
    C "da_verify_cell" [σc (.n (val% «da_verify_blob_loop0» "d0~4"))] [σc (.n (val% «da_verify_blob_loop0» "d0")), σc (.n (val% «da_verify_blob_loop0» "d1")), σc (.n (val% «da_verify_blob_loop0» "s"))] ∧
    ∃ a : E, LoadHolds rd (base * x) 512 a ∧ LoadHolds rd (base * x) 513 (a + σc (.n (val% «da_verify_blob_loop0» "s"))) ∧
      LoadHolds rd (base * x ^ 2) 0 (σc (.n (val% «da_verify_blob_loop0» "d0"))) ∧ LoadHolds rd (base * x ^ 2) 1 (σc (.n (val% «da_verify_blob_loop0» "d1")))

theorem c_stepW (hVm : UnfoldsV rd C Vm) {x : E} {ps : List E}
    (h : C name% «da_verify_blob_loop0» (x :: ps) []) :
    (∀ w base, ps = [w, base] → CellStepB C rd (Vm name% «da_verify_blob_loop0» (x :: ps) []) w base x) ∧
      (x * gen + word 325 0 ≠ 0 → C name% «da_verify_blob_loop0» (x * gen :: ps) []) := by
  have hok := c_ok
  unfold cOk at hok
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hok
  obtain ⟨hparams, hbody⟩ := hok
  obtain ⟨hpar, hb⟩ := body_ofV hVm find_c h
  set σ := Vm name% «da_verify_blob_loop0» (x :: ps) [] with hσ
  rw [stmtsEqb_sound hbody] at hb
  rw [hparams] at hpar
  simp only [List.map_cons, List.map_nil] at hpar
  obtain ⟨hx, hps⟩ := List.cons.inj hpar
  simp only [cBody, Stmt.HoldsList, Stmt.Holds, Atom.Holds, List.map_cons, List.map_nil] at hb
  obtain ⟨m3, l4, hc, m8, l9, a10, l10, m11, m12, l5, l6, c13, m14, c15, a16, c17, m18, -, hcall, -⟩ := hb
  refine ⟨fun w base hwb => ?_, fun hne => ?_⟩
  · rw [hwb] at hps
    simp only [List.cons.injEq, and_true] at hps
    obtain ⟨h1, h2⟩ := hps
    rw [m3, h1, hx] at l4
    rw [m8, h2, hx] at l9 l10
    rw [a10] at l10
    rw [m12, m11, h2, hx, ← sq] at l5 l6
    exact ⟨l4, hc, _, l9, l10, l5, l6⟩
  · have e16 : σ (.n (val% «da_verify_blob_loop0» "s7#3")) = x * gen + word 325 0 := by rw [a16, m14, c13, c15, word_gen, hx]
    have e18 : σ (.n (val% «da_verify_blob_loop0» "s7#5")) = x * gen := by rw [m18, c17, word_gen, hx]
    have := hcall (by rw [e16]; exact hne)
    rw [e18] at this
    rw [← hps]
    exact this

/-! ## The blob -/

/-- A frame run's word, read. -/
theorem runAt_load {p : E} {n : ℕ} {f : ℕ → E} (hr : RunAt rd p n f) {k : ℕ} (hk : k < n) {v : E}
    (h : LoadHolds rd p k v) : v = f k :=
  hr.2 k hk v h.2

/-- **A blob's run** on weights that are the dual codeword of `z`, under a call relation that
unfolds at `Vm` and lies below `coreProgram.Rel`: its cells' symbols (`blobSyms`) are `128` long
and orthogonal to the dual codeword, and the returned cells are the root of their digests' tree. -/
theorem blob_stepW (hVm : UnfoldsV rd C Vm) (hle : CallRel.Le C (coreProgram.Rel rd)) {z w c0 c1 : E}
    (hw : WeightsAt rd z w) (hrel : C "da_verify_blob" [w] [c0, c1]) :
    (∀ h < 128, (blobSyms Vm w c0 c1 h).length = 128) ∧
      ∑ h ∈ Finset.range 128, ∑ e ∈ Finset.range 128,
        dualAt z (128 * h + e) * (blobSyms Vm w c0 c1 h).getD e 0 = 0 ∧
      (c0, c1) = digestHalves (mRoot 7 fun h => keccak256 ((blobSyms Vm w c0 c1 h).flatMap E.toBytes)) := by
  have hok := blob_ok
  unfold blobOk at hok
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hok
  obtain ⟨hparams, hbody⟩ := hok
  obtain ⟨hpar, hb⟩ := body_ofV hVm find_da_verify_blob hrel
  set σ := Vm "da_verify_blob" [w] [c0, c1] with hσ
  rw [stmtsEqb_sound hbody] at hb
  rw [hparams] at hpar
  simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true] at hpar
  simp only [blobBody, Stmt.HoldsList, Stmt.Holds, Atom.Holds, List.map_cons, List.map_nil] at hb
  obtain ⟨-, c2, l2, c3, hloop, l4, c5, a45, hlv, cp8, cp9, hret⟩ := hb
  simp only [List.cons.injEq, and_true] at hret
  rw [c2, word_zero] at l2
  rw [c3, word_one, ← pow_zero gen, hpar] at hloop
  -- the cells
  have L : ∀ h < 128, CellStepB C rd (blobCellV Vm w c0 c1 h) w (σ (.n (val% «da_verify_blob» "base"))) (gen ^ h) :=
    fun h hh => loop_fromC (C := C) (f := name% «da_verify_blob_loop0») (N := gen ^ 128) (m := 128) (a := 0)
      (B := fun x => CellStepB C rd (Vm name% «da_verify_blob_loop0» [x, w, σ (.n (val% «da_verify_blob» "base"))] []) w (σ (.n (val% «da_verify_blob» "base"))) x)
      (by unfold ordG; omega) rfl (fun x hx => by
        obtain ⟨k1, k2⟩ := c_stepW hVm hx
        exact ⟨k1 _ _ rfl, by rw [← word_g128]; exact k2⟩)
      hloop h (Nat.zero_le _) hh
  have cell : ∀ h < 128, (blobSyms Vm w c0 c1 h).length = 128 ∧ ∃ a : E,
      LoadHolds rd (σ (.n (val% «da_verify_blob» "base"))) (h + 512) a ∧
      LoadHolds rd (σ (.n (val% «da_verify_blob» "base"))) (h + 513) (a + ∑ e ∈ Finset.range 128, dualAt z (128 * h + e) *
        (blobSyms Vm w c0 c1 h).getD e 0) ∧
      LoadHolds rd (σ (.n (val% «da_verify_blob» "base"))) (2 * h) (digestHalves (keccak256 ((blobSyms Vm w c0 c1 h).flatMap E.toBytes))).1 ∧
      LoadHolds rd (σ (.n (val% «da_verify_blob» "base"))) (2 * h + 1)
        (digestHalves (keccak256 ((blobSyms Vm w c0 c1 h).flatMap E.toBytes))).2 := by
    intro h hh
    obtain ⟨hwl, hc, a, ha, has, hd0, hd1⟩ := L h hh
    obtain ⟨lv, hlv0, hlvv⟩ := hw h hh
    have e4 := loadHolds_unique hwl hlv0
    rw [e4] at hc
    obtain ⟨hpc, hbc⟩ := body_ofV hVm find_da_verify_cell hc
    obtain ⟨lv', hlv', hsl, hrd, hlen, hrets⟩ := da_verify_cell_val hpc hbc
    simp only [List.cons.injEq, and_true] at hlv'
    subst hlv'
    have hsy : blobSyms Vm w c0 c1 h = cellSymsOf (Vm "da_verify_cell" [lv]
        [blobCellV Vm w c0 c1 h (.n (val% «da_verify_blob_loop0» "d0")), blobCellV Vm w c0 c1 h (.n (val% «da_verify_blob_loop0» "d1")), blobCellV Vm w c0 c1 h (.n (val% «da_verify_blob_loop0» "s"))]) := by
      rw [blobSyms, e4]
    rw [hsy]
    simp only [digestCells, List.cons_append, List.nil_append, List.cons.injEq, and_true] at hrets
    obtain ⟨e0, e1, es⟩ := hrets
    rw [loadHolds_mul_gen_pow] at ha has
    rw [shift2] at hd0 hd1
    refine ⟨hsl, a, ha, ?_, by rw [← e0]; simpa using hd0, by rw [← e1]; exact hd1⟩
    rw [es] at has
    convert has using 2
    rw [← list_sum_range]
    unfold LeanDa.cellSymbols
    refine congrArg _ (List.map_congr_left fun e he ↦ ?_)
    have he' := List.mem_range.mp he
    rw [List.getD_eq_getElem (memRun rd lv 128) 0 (show e < _ by rw [hlen]; unfold LeanDa.cellSymbols; omega),
      hlvv e he' _ (hrd e (by rw [hlen]; unfold LeanDa.cellSymbols; omega)).2]
  refine ⟨fun h hh => (cell h hh).1, ?_, ?_⟩
  · -- the running sum
    have run : ∀ h ≤ 128, LoadHolds rd (σ (.n (val% «da_verify_blob» "base"))) (h + 512)
        (∑ h' ∈ Finset.range h, ∑ e ∈ Finset.range 128,
          dualAt z (128 * h' + e) * (blobSyms Vm w c0 c1 h').getD e 0) := by
      intro h
      induction h with
      | zero => intro _; simpa using l2
      | succ h ih =>
        intro hh
        obtain ⟨-, a, k2, k3, -, -⟩ := cell h (by omega)
        rw [loadHolds_unique k2 (ih (by omega))] at k3
        rw [Finset.sum_range_succ, show h + 1 + 512 = h + 513 by ring]
        exact k3
    rw [c5, word_zero, add_zero] at a45
    rw [a45] at l4
    exact loadHolds_unique (run 128 le_rfl) (by simpa using l4)
  · -- the root
    have e01 : (c0, c1) = (σ (.n (val% «da_verify_blob» "b0")), σ (.n (val% «da_verify_blob» "b1"))) := by rw [← hret.1, ← hret.2, cp8, cp9]
    rw [e01]
    have hl7 : coreProgram.Rel rd (daLevelsName 7) [σ (.n (val% «da_verify_blob» "base"))] [σ (.n (val% «da_verify_blob» "b0")), σ (.n (val% «da_verify_blob» "b1"))] := hle _ _ _ hlv
    have hk7 : ofK (Parameters.addressOfIndex 7) = gen ^ 7 := (gen_pow_eq_ofK 7).symm
    have hf : ∀ i < 2 ^ 7, LoadHolds rd (σ (.n (val% «da_verify_blob» "base"))) (2 * i)
        (digestHalves (keccak256 ((blobSyms Vm w c0 c1 i).flatMap E.toBytes))).1 ∧
        LoadHolds rd (σ (.n (val% «da_verify_blob» "base"))) (2 * i + 1)
          (digestHalves (keccak256 ((blobSyms Vm w c0 c1 i).flatMap E.toBytes))).2 := fun i hi => by
      obtain ⟨-, -, -, -, k0, k1⟩ := cell i (by norm_num at hi; omega)
      exact ⟨k0, k1⟩
    exact levels_root_of (k := 7) (L := 7) (g := fun i => keccak256 ((blobSyms Vm w c0 c1 i).flatMap E.toBytes))
      (Or.inr rfl) (by norm_num) hk7 hl7 hf

end
end LeanVM.Guest.B1.Da
