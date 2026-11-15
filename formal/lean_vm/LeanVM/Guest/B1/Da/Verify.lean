/-
  LeanVM.Guest.B1.Da.Verify

  `da_verify`'s core IR gives its meaning (TRIAGE G #90).
-/

module

public import LeanVM.Guest.B1.Da.Weights
public import LeanVM.Guest.B1.Da.RootsTree
public import LeanVM.Guest.B1.Da.RowShape
public import LeanVM.Guest.B1.Da.VerifyMath
public import LeanVM.Guest.B1.Main.LoopsC
public import LeanVM.Guest.B1.Main.Facts
public import LeanVM.Guest.Data.NameStrings

/-!
# `da_verify`, sound

`da_verify_sound_w`: under a call relation that unfolds at a frame map `Vm` and lies below
`coreProgram.Rel`, with the exponent table, a run of `da_verify` returns the cells of a root and
a challenge `z` that the witness `dvWit σ Vm` opens (`opens_of`); with `coreProgram.Rel` and a
frame map by choice, `da_verify_holds : da_verify_sound_Spec`. `da_weights` makes the weights the
dual codeword of `z` (`ws_sound`, `weightsAt_of`); the witness's row `i` is the symbols of blob `i`'s cell checks'
frames (`blobSyms`, at the blob loop's iteration `i`, `dvBlobV`), orthogonal to the dual codeword,
its root at `roots·g^(2i)` (`blob_stepW`); it mentions no hash. The returned root is the tree's
over the blob roots and the padding blob roots (`rt_sound`, `levels_root_of`).
-/

namespace LeanVM.Guest.B1.Da

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Value.Keccak
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Guest.B1.Digest LeanVM.Guest.B1.Main

@[expose] public section

variable {rd : Reader}

theorem ordG_of {x : ℕ} (h : x ≤ 4096) : x < ordG := by unfold ordG; omega

/-! ## The blobs -/

theorem b_stepW {C : CallRel} {Vm : FrameMap} (hVm : UnfoldsV rd C Vm) {x : E} {ps : List E}
    (h : C name% «da_verify_loop0» (x :: ps) []) :
    (∀ N wt roots, ps = [N, wt, roots] →
      C "da_verify_blob" [wt] [Vm name% «da_verify_loop0» (x :: ps) [] (.n 4),
        Vm name% «da_verify_loop0» (x :: ps) [] (.n 5)] ∧
      LoadHolds rd (roots * x ^ 2) 0 (Vm name% «da_verify_loop0» (x :: ps) [] (.n 4)) ∧
      LoadHolds rd (roots * x ^ 2) 1 (Vm name% «da_verify_loop0» (x :: ps) [] (.n 5))) ∧
      (x * gen + ps.headD 0 ≠ 0 → C name% «da_verify_loop0» (x * gen :: ps) []) := by
  have hok := b_ok
  simp only [Bool.and_eq_true, decide_eq_true_eq, bOk] at hok
  obtain ⟨⟨⟨⟨⟨⟨hshape, hlen⟩, hcall⟩, hm6⟩, hm7⟩, hl4⟩, hl5⟩ := hok
  obtain ⟨hx, hps, hall, hnext⟩ := loop_stepV hVm (find_of_idx dv_loops_idx.1) hshape h
  set σ := Vm name% «da_verify_loop0» (x :: ps) [] with hσ
  refine ⟨fun N wt roots hN ↦ ?_, hnext⟩
  have hat := atoms_of_flat hall
  have hpar : (coreProgram.getD idx% «da_verify_loop0» default).params = [V.n 0, V.n 1, V.n 2,
      V.n 3] := by
    rw [loop_params hshape hlen]; rfl
  rw [hpar, hN] at hps
  simp only [List.tail_cons, List.map_cons, List.map_nil, List.cons.injEq, and_true] at hps
  obtain ⟨-, h2, h3⟩ := hps
  have c := call_of_flat hall hcall
  simp only [List.map_cons, List.map_nil] at c
  rw [h2] at c
  have p7 : σ (.n 7) = roots * x ^ 2 := by rw [isMul_sound hm7 hat, isMul_sound hm6 hat, h3, hx, sq]
  have l4 := load_sound hl4 hat
  have l5 := load_sound hl5 hat
  rw [p7] at l4 l5
  exact ⟨c, l4, l5⟩

/-- `guard_soundC` for any continuation of `ret`. -/
theorem guardK_soundC {C : CallRel} {σ : Val} {P : List Stmt} {gc : V} {f : String} {one N : V}
    {rest : List V} (h : guardOk P gc f one N rest = true) {kret : List E → Prop}
    (hall : ∀ s ∈ P, Stmt.Holds C rd σ s True kret) :
    1 + σ N ≠ 0 → C f (1 :: σ N :: rest.map σ) [] := by
  simp only [guardOk, Bool.and_eq_true] at h
  obtain ⟨⟨hc, ha⟩, h1⟩ := h
  have hat := atoms_of_flat hall
  have hcall := callIf_of_flat hall hc
  split at ha
  · rename_i p q hpq
    simp only [Bool.and_eq_true, decide_eq_true_eq] at ha
    obtain ⟨hp1, rfl⟩ := ha
    intro hne
    have hgc : σ gc = 1 + σ q := by rw [addOf_sound hpq hat, const_sound hp1 hat, word_one]
    have := hcall.2 (by rw [hgc]; exact hne)
    rwa [List.map_cons, List.map_cons, const_sound h1 hat, word_one] at this
  · exact absurd ha (by simp)

/-- Trees agreeing on their `2^d` leaves have one root. -/
theorem mRoot_congr : ∀ (d : ℕ) {g g' : ℕ → Digest}, (∀ i < 2 ^ d, g i = g' i) → mRoot d g = mRoot d g'
  | 0, g, g', h => by simp only [mRoot]; exact h 0 (by norm_num)
  | d + 1, g, g', h => by
    simp only [mRoot]
    exact mRoot_congr d fun i hi => by
      simp only [upD]
      rw [h (2 * i) (by rw [pow_succ]; omega), h (2 * i + 1) (by rw [pow_succ]; omega)]

/-! ## The witness -/

/-- Blob `i`'s iteration of the blob loop, at the frame map `Vm`. -/
def dvBlobV (σ : Val) (Vm : FrameMap) (i : ℕ) : Val :=
  Vm name% «da_verify_loop0» [gen ^ i, σ (.n 1), σ (.n 14), σ (.n 17)] []

/-- Cell `(i, h)`'s symbols: blob `i`'s cell check's. -/
def dvSyms (σ : Val) (Vm : FrameMap) (i h : ℕ) : List K :=
  blobSyms Vm (σ (.n 14)) (dvBlobV σ Vm i (.n 4)) (dvBlobV σ Vm i (.n 5)) h

/-- The number of rows: the shape's count, at most `LeanDa.maxRows = 1024` (`da_verify` asserts
it, so on its runs the clamp is the count; it bounds the witness on every memory). -/
noncomputable def dvRows (σ : Val) : ℕ := min (gLog (σ (.n 1))) 1024

/-- The symbols, padded outside the matrix. -/
noncomputable def dvSymsP (σ : Val) (Vm : FrameMap) (i h : ℕ) : List K :=
  if i < dvRows σ ∧ h < 128 then dvSyms σ Vm i h else List.replicate 256 0

/-- **`da_verify`'s witness**: the rows of the cells' symbols, as many as the shape's count (at
most `1024`, `dvRows`). -/
noncomputable def dvWit (σ : Val) (Vm : FrameMap) : LeanVM.Da.MatrixWitness :=
  ⟨daRows (dvRows σ) (dvSymsP σ Vm)⟩

/-! ## The body -/

variable {C : CallRel} {Vm : FrameMap}

/-- **`da_verify`, soundly, its witness named**: under a call relation that unfolds at `Vm` and
lies below `coreProgram.Rel`, on a memory image with the exponent table at its argument, the
returned words are the cells of a root and a challenge `z` that `dvWit σ Vm` opens. -/
theorem da_verify_sound_w (hVm : UnfoldsV rd C Vm) (hle : CallRel.Le C (coreProgram.Rel rd))
    (hm : MemOk rd) {σ : Val} {gsq : E} {rets : List E} (hpar0 : (fn% «da_verify»).params.map σ =
        [gsq])
    (hb : Stmt.HoldsList C rd σ (Fn.body fn% «da_verify») False (fun rs => rs = rets))
    (hsq0 : SquaresAt rd gsq) :
    ∃ (root : Digest) (z : E), (dvWit σ Vm).Opens root z ∧ rets = digestCells root ++ [z] := by
  have hok := dv_ok
  unfold dvOk at hok
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hok
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hparams, hbody⟩, hflat⟩, hrc2⟩, hcrs⟩, hcv⟩, hcw⟩, hg1⟩, hdisp⟩,
    hcp23⟩, hcp24⟩, hcp25⟩ := hok
  have hσ0 : σ (.n 0) = gsq := by
    rw [hparams] at hpar0
    simpa using hpar0
  have hsq : SquaresAt rd (σ (.n 0)) := by rw [hσ0]; exact hsq0
  rw [stmtsEqb_sound hbody, holdsList_append] at hb
  obtain ⟨hallC, hret⟩ := holdsList_flat dvP hflat _ _ hb
  have hall : ∀ s ∈ dvP, Stmt.Holds (coreProgram.Rel rd) rd σ s True (fun rs => rs = rets) :=
    fun s hs => holds_mono hle s id (fun _ h => h) (hallC s hs)
  simp only [Stmt.HoldsList, Stmt.Holds, List.map_cons, List.map_nil] at hret
  have hat := atoms_of_flat hall
  -- the shape
  obtain ⟨L, hL, h2⟩ := rcConst_sound hm (by norm_num) word_g10 hrc2 hat
  have hrs := da_row_shape_holds rd hm _ _ (call_of_flat hall hcrs)
  simp only [List.map_cons, List.map_nil, MeaningDaRowShape] at hrs
  obtain ⟨r, hr1, hr, h1, hnp, h34⟩ := hrs hsq L hL h2
  simp only [List.cons.injEq, and_true] at h34
  obtain ⟨h7, h8⟩ := h34
  unfold LeanDa.maxRows at hr
  have hL2 : 2 ^ L ≤ 1024 := by
    calc 2 ^ L ≤ 2 ^ 10 := Nat.pow_le_pow_right (by norm_num) hL
      _ = 1024 := by norm_num
  have hrL : r ≤ 2 ^ L := by
    rw [hnp, LeanDa.paddedRowCount, LeanDa.logPaddedRowCount]; exact Nat.le_pow_clog (by norm_num) r
  have hr' : r < ordG := ordG_of (by omega)
  have hg' : 2 ^ L - r < ordG := ordG_of (by omega)
  -- the challenge
  set z := σ (.n 9)
  -- the dual codeword's builders, the weights
  have hvec := da_vector_holds rd _ _ (call_of_flat hall hcv)
  simp only [List.map_cons, List.map_nil] at hvec
  have cw := call_of_flat hall hcw
  simp only [List.map_cons, List.map_nil] at cw
  have hW : WeightsAt rd z (σ (.n 14)) := weightsAt_of hvec (ws_sound cw)
  -- the blobs
  have L1 : ∀ i < r, C "da_verify_blob" [σ (.n 14)] [dvBlobV σ Vm i (.n 4), dvBlobV σ Vm i (.n 5)] ∧
      LoadHolds rd (σ (.n 17) * (gen ^ i) ^ 2) 0 (dvBlobV σ Vm i (.n 4)) ∧
      LoadHolds rd (σ (.n 17) * (gen ^ i) ^ 2) 1 (dvBlobV σ Vm i (.n 5)) :=
    loop_soundC (C := C) (f := name% «da_verify_loop0») (ps := [σ (.n 1), σ (.n 14), σ (.n 17)]) hr' h1
      (fun y hy => by
        obtain ⟨k1, k2⟩ := b_stepW hVm hy
        exact ⟨k1 _ _ _ rfl, k2⟩)
      (fun hne => by simpa using guardK_soundC hg1 hallC hne)
  have hrows : dvRows σ = r := by
    rw [dvRows, h1, gLog_gen_pow (by omega)]; omega
  let symsP : ℕ → ℕ → List K := dvSymsP σ Vm
  have hsP : ∀ i h, i < r → h < 128 → symsP i h = dvSyms σ Vm i h := fun i h hi hh => by
    simp only [symsP, dvSymsP, hrows, hi, hh, and_self, ite_true]
  have blob := fun i (hi : i < r) => blob_stepW hVm hle hW (L1 i hi).1
  have hsL : ∀ i h, (symsP i h).length = 256 := fun i h => by
    by_cases hc : i < r ∧ h < 128
    · rw [hsP i h hc.1 hc.2]; exact (blob i hc.1).1 h hc.2
    · simp only [symsP, dvSymsP, hrows, hc, ite_false, List.length_replicate]
  have hdot : ∀ i < r, ∑ h ∈ Finset.range 128, ∑ e ∈ Finset.range 256,
      dualAt z (256 * h + e) * ofK ((symsP i h).getD e 0) = 0 := by
    intro i hi
    rw [← (blob i hi).2.1]
    refine Finset.sum_congr rfl fun h hh => ?_
    rw [hsP i h hi (Finset.mem_range.mp hh)]
    rfl
  have hblob : ∀ i < r, LoadHolds rd (σ (.n 17)) (2 * i) (digestHalves (blobLeaf r symsP i)).1 ∧
      LoadHolds rd (σ (.n 17)) (2 * i + 1) (digestHalves (blobLeaf r symsP i)).2 := by
    intro i hi
    obtain ⟨-, k0, k1⟩ := L1 i hi
    have hroot := (blob i hi).2.2
    have hc : mRoot 7 (fun h => keccak256 ((blobSyms Vm (σ (.n 14)) (dvBlobV σ Vm i (.n 4))
        (dvBlobV σ Vm i (.n 5)) h).flatMap K.toBytes)) = mRoot 7 (cellD symsP i) :=
      mRoot_congr 7 fun h hh => by simp only [cellD, hsP i h hi (by norm_num at hh; omega)]; rfl
    rw [hc] at hroot
    rw [shift2] at k0 k1
    simp only [Prod.ext_iff] at hroot
    simp only [blobLeaf, hi, ite_true]
    rw [← hroot.1, ← hroot.2]
    exact ⟨by simpa using k0, k1⟩
  -- the root
  have hrt : (σ (.n 21), σ (.n 22)) = digestHalves (daRoot r L symsP) := by
    obtain ⟨k, hk, hk2, hrel⟩ := dispatch_of_flat hall hdisp
    simp only [rtNames, List.length_map, List.length_range] at hk
    simp only [rtNames, List.getElem_map, List.getElem_range, List.map_cons, List.map_nil] at hrel
    rw [h8] at hrel
    obtain ⟨L20, hlv⟩ := rt_sound hk hg' hrel
    refine levels_root_of hk hL (by rw [← hk2, h2]) hlv fun i hi => ?_
    by_cases hir : i < r
    · exact hblob i hir
    · obtain ⟨g0, g1⟩ := L20 (i - r) (by omega)
      rw [h1, ← pow_mul, shift, show r * 2 + 2 * (i - r) = 2 * i by omega] at g0 g1
      simp only [blobLeaf, hir, ite_false]
      exact ⟨by simpa using g0, g1⟩
  refine ⟨daRoot r L symsP, z, ?_, ?_⟩
  · rw [dvWit, hrows]
    exact opens_of hr1 (by unfold LeanDa.maxRows; exact hr) hnp.symm hrL hsL hdot
  rw [← hret, copy_sound hcp23 hat, copy_sound hcp24 hat, copy_sound hcp25 hat]
  simp only [Prod.ext_iff] at hrt
  simp [digestCells, ← hrt.1, ← hrt.2, z]


/-- **`da_verify`'s core IR gives its meaning.** -/
theorem da_verify_holds : da_verify_sound_Spec := by
  intro rd hm args rets hrel
  obtain ⟨σ, hpar, hb⟩ := (rel_iff_sem find_da_verify _ _).mp hrel
  have hp : (fn% «da_verify»).params.map σ = [σ (.n 0)] := rfl
  rw [hp] at hpar
  subst hpar
  simp only [MeaningDaVerify]
  intro hsq
  obtain ⟨root, z, ho, hr⟩ :=
    da_verify_sound_w (unfoldsV_rel rd) (fun _ _ _ h => h) hm hp hb hsq
  exact ⟨_, root, z, ho, hr⟩
end
end LeanVM.Guest.B1.Da
