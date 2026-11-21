/-
  LeanVM.Guest.B1.Da.Verify

  `da_verify`'s core IR gives its meaning (TRIAGE G #90).
-/

module

public import LeanVM.Guest.B1.Da.Weights
public import LeanVM.Guest.B1.Da.Pad
public import LeanVM.Guest.B1.Da.Padding
public import LeanVM.Guest.B1.Da.VerifyMath
public import LeanVM.Guest.B1.Main.LoopsC
public import LeanVM.Guest.B1.Main.Facts
public import LeanVM.Guest.Data.NameStrings
public import LeanVM.Guest.GuestConst
-- Private: `guest_const%` inserts literals, so importers need not see the guest's source.
import LeanVM.Guest.Data.Consts
import LeanVM.Guest.ValRef
import LeanVM.Guest.Data.ValNames.«da_verify»
import LeanVM.Guest.Data.ValNames.«da_verify_loop0»

/-!
# `da_verify`, sound

`da_verify_sound_w`: under a call relation that unfolds at a frame map `Vm` and lies below
`coreProgram.Rel`, on the count table at its argument, a run of `da_verify` returns the cells of a
root and a challenge `z` that the witness `dvWit σ Vm` opens (`opens_of`); with `coreProgram.Rel`
and a frame map by choice, `da_verify_holds : da_verify_sound_Spec`. `da_weights` makes the weights
the dual codeword of `z` (`ws_sound`, `weightsAt_of`); the witness's row `i` is the symbols of blob
`i`'s cell checks' frames (`blobSyms`, at the blob loop's iteration `i`, `dvBlobV`), orthogonal to
the dual codeword, its root at `roots·g^(2i)` (`blob_stepW`); it mentions no hash. The tree is over
the blob roots and the padding blob roots (`pad_sound`, `levels_root_of`), its root hashed with the
count's word (`pairHashV_sound`).
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
      C "da_verify_blob" [wt] [Vm name% «da_verify_loop0» (x :: ps) [] (.n (val% «da_verify_loop0» "b0")),
        Vm name% «da_verify_loop0» (x :: ps) [] (.n (val% «da_verify_loop0» "b1"))] ∧
      LoadHolds rd (roots * x ^ 2) 0 (Vm name% «da_verify_loop0» (x :: ps) [] (.n (val% «da_verify_loop0» "b0"))) ∧
      LoadHolds rd (roots * x ^ 2) 1 (Vm name% «da_verify_loop0» (x :: ps) [] (.n (val% «da_verify_loop0» "b1")))) ∧
      (x * gen + ps.headD 0 ≠ 0 → C name% «da_verify_loop0» (x * gen :: ps) []) := by
  have hok := b_ok
  simp only [Bool.and_eq_true, decide_eq_true_eq, bOk] at hok
  obtain ⟨⟨⟨⟨⟨⟨hshape, hlen⟩, hcall⟩, hm6⟩, hm7⟩, hl4⟩, hl5⟩ := hok
  obtain ⟨hx, hps, hall, hnext⟩ := loop_stepV hVm (find_of_idx dv_loops_idx.1) hshape h
  set σ := Vm name% «da_verify_loop0» (x :: ps) [] with hσ
  refine ⟨fun N wt roots hN ↦ ?_, hnext⟩
  have hat := atoms_of_flat hall
  have hpar : (coreProgram.getD idx% «da_verify_loop0» default).params = [V.n (val% «da_verify_loop0» "xi"), V.n (val% «da_verify_loop0» "bound"), V.n (val% «da_verify_loop0» "weights"),
      V.n (val% «da_verify_loop0» "roots")] := by
    rw [loop_params hshape hlen]; rfl
  rw [hpar, hN] at hps
  simp only [List.tail_cons, List.map_cons, List.map_nil, List.cons.injEq, and_true] at hps
  obtain ⟨-, h2, h3⟩ := hps
  have c := call_of_flat hall hcall
  simp only [List.map_cons, List.map_nil] at c
  rw [h2] at c
  have p7 : σ (.n (val% «da_verify_loop0» "slot")) = roots * x ^ 2 := by rw [isMul_sound hm7 hat, isMul_sound hm6 hat, h3, hx, sq]
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
  Vm name% «da_verify_loop0» [gen ^ i, σ (.n (val% «da_verify» "n_blob_g")), σ (.n (val% «da_verify» "weights")), σ (.n (val% «da_verify» "roots"))] []

/-- Cell `(i, h)`'s symbols: blob `i`'s cell check's. -/
def dvSyms (σ : Val) (Vm : FrameMap) (i h : ℕ) : List E :=
  blobSyms Vm (σ (.n (val% «da_verify» "weights"))) (dvBlobV σ Vm i (.n (val% «da_verify_loop0» "b0"))) (dvBlobV σ Vm i (.n (val% «da_verify_loop0» "b1"))) h

/-- The number of rows: the hinted count, at most `DA_MAX_ROWS` (`da_padding` asserts it, so on
its runs the clamp is the count; it bounds the witness on every memory). -/
noncomputable def dvRows (σ : Val) : ℕ := min (gLog (σ (.n (val% «da_verify» "n_blob_g")))) (guest_const% DA_MAX_ROWS)

/-- The symbols, padded outside the matrix. -/
noncomputable def dvSymsP (σ : Val) (Vm : FrameMap) (i h : ℕ) : List E :=
  if i < dvRows σ ∧ h < 128 then dvSyms σ Vm i h else List.replicate 128 0

/-- **`da_verify`'s witness**: the rows of the cells' symbols, as many as the hinted count (at
most `DA_MAX_ROWS`, `dvRows`). -/
noncomputable def dvWit (σ : Val) (Vm : FrameMap) : LeanVM.Da.MatrixWitness :=
  ⟨daRows (dvRows σ) (dvSymsP σ Vm)⟩

/-! ## The body -/

variable {C : CallRel} {Vm : FrameMap}

/-- **`da_verify`, soundly, its witness named**: under a call relation that unfolds at `Vm` and
lies below `coreProgram.Rel`, on a memory image holding the count table at its argument, the
returned words are the cells of a root and a challenge `z` that `dvWit σ Vm` opens. -/
theorem da_verify_sound_w (hVm : UnfoldsV rd C Vm) (hle : CallRel.Le C (coreProgram.Rel rd))
    (hm : MemOk rd) {σ : Val} {rets : List E} (hcw : CountWords rd (σ (.n (val% «da_verify» "byte_bits"))))
    (hb : Stmt.HoldsList C rd σ (Fn.body fn% «da_verify») False (fun rs => rs = rets)) :
    ∃ (root : Digest) (z : E), (dvWit σ Vm).Opens root z ∧ rets = digestCells root ++ [z] := by
  have hok := dv_ok
  unfold dvOk at hok
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hok
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨-, hbody⟩, hflat⟩, hpd⟩, hcv⟩, hcw8⟩, hg1⟩, hpad⟩, hdl⟩, hm16⟩, hld17⟩,
    hc19⟩, hph⟩, hcp26⟩, hcp27⟩, hcp28⟩ := hok
  rw [stmtsEqb_sound hbody, holdsList_append] at hb
  obtain ⟨hallC, hret⟩ := holdsList_flat dvP hflat _ _ hb
  have hall : ∀ s ∈ dvP, Stmt.Holds (coreProgram.Rel rd) rd σ s True (fun rs => rs = rets) :=
    fun s hs => holds_mono hle s id (fun _ h => h) (hallC s hs)
  simp only [Stmt.HoldsList, Stmt.Holds, List.map_cons, List.map_nil] at hret
  have hat := atoms_of_flat hall
  -- the blob count and the padding rows'
  have hpd' := da_padding_holds rd hm _ _ (call_of_flat hall hpd)
  simp only [List.map_cons, List.map_nil, MeaningDaPadding] at hpd'
  obtain ⟨r, hr1, hr, h1, h2⟩ := hpd'
  simp only [List.cons.injEq, and_true] at h2
  rw [maxRows_eq] at hr h2
  have hr' : r < ordG := ordG_of (by omega)
  have hg' : guest_const% DA_MAX_ROWS - r < ordG := ordG_of (by omega)
  -- the challenge
  set z := σ (.n (val% «da_verify» "z"))
  -- the dual codeword's builders, the weights
  have hvec := da_vector_holds rd _ _ (call_of_flat hall hcv)
  simp only [List.map_cons, List.map_nil] at hvec
  have cw := call_of_flat hall hcw8
  simp only [List.map_cons, List.map_nil] at cw
  have hW : WeightsAt rd z (σ (.n (val% «da_verify» "weights"))) := weightsAt_of hvec (ws_sound cw)
  -- the blobs
  have L1 : ∀ i < r, C "da_verify_blob" [σ (.n (val% «da_verify» "weights"))] [dvBlobV σ Vm i (.n (val% «da_verify_loop0» "b0")), dvBlobV σ Vm i (.n (val% «da_verify_loop0» "b1"))] ∧
      LoadHolds rd (σ (.n (val% «da_verify» "roots")) * (gen ^ i) ^ 2) 0 (dvBlobV σ Vm i (.n (val% «da_verify_loop0» "b0"))) ∧
      LoadHolds rd (σ (.n (val% «da_verify» "roots")) * (gen ^ i) ^ 2) 1 (dvBlobV σ Vm i (.n (val% «da_verify_loop0» "b1"))) :=
    loop_soundC (C := C) (f := name% «da_verify_loop0») (ps := [σ (.n (val% «da_verify» "n_blob_g")), σ (.n (val% «da_verify» "weights")), σ (.n (val% «da_verify» "roots"))]) hr' h1
      (fun y hy => by
        obtain ⟨k1, k2⟩ := b_stepW hVm hy
        exact ⟨k1 _ _ _ rfl, k2⟩)
      (fun hne => by simpa using guardK_soundC hg1 hallC hne)
  have hrows : dvRows σ = r := by
    rw [dvRows, h1, gLog_gen_pow (by omega)]; omega
  let symsP : ℕ → ℕ → List E := dvSymsP σ Vm
  have hsP : ∀ i h, i < r → h < 128 → symsP i h = dvSyms σ Vm i h := fun i h hi hh => by
    simp only [symsP, dvSymsP, hrows, hi, hh, and_self, ite_true]
  have blob := fun i (hi : i < r) => blob_stepW hVm hle hW (L1 i hi).1
  have hsL : ∀ i h, (symsP i h).length = 128 := fun i h => by
    by_cases hc : i < r ∧ h < 128
    · rw [hsP i h hc.1 hc.2]; exact (blob i hc.1).1 h hc.2
    · simp only [symsP, dvSymsP, hrows, hc, ite_false, List.length_replicate]
  have hdot : ∀ i < r, ∑ h ∈ Finset.range 128, ∑ e ∈ Finset.range 128,
      dualAt z (128 * h + e) * (symsP i h).getD e 0 = 0 := by
    intro i hi
    refine Eq.trans ?_ (blob i hi).2.1
    refine Finset.sum_congr rfl fun h hh => ?_
    rw [hsP i h hi (Finset.mem_range.mp hh), dvSyms]
  have hblob : ∀ i < r, LoadHolds rd (σ (.n (val% «da_verify» "roots"))) (2 * i) (digestHalves (blobLeaf r symsP i)).1 ∧
      LoadHolds rd (σ (.n (val% «da_verify» "roots"))) (2 * i + 1) (digestHalves (blobLeaf r symsP i)).2 := by
    intro i hi
    obtain ⟨-, k0, k1⟩ := L1 i hi
    have hroot := (blob i hi).2.2
    have hc : mRoot 7 (fun h => keccak256 ((blobSyms Vm (σ (.n (val% «da_verify» "weights"))) (dvBlobV σ Vm i (.n (val% «da_verify_loop0» "b0")))
        (dvBlobV σ Vm i (.n (val% «da_verify_loop0» "b1"))) h).flatMap E.toBytes)) = mRoot 7 (cellD symsP i) :=
      mRoot_congr 7 fun h hh => by simp only [cellD, hsP i h hi (by norm_num at hh; omega)]; rfl
    rw [hc] at hroot
    rw [shift2] at k0 k1
    simp only [Prod.ext_iff] at hroot
    simp only [blobLeaf, hi, ite_true]
    rw [← hroot.1, ← hroot.2]
    exact ⟨by simpa using k0, k1⟩
  -- the padding blobs
  have L20 : ∀ d < guest_const% DA_MAX_ROWS - r,
      LoadHolds rd (σ (.n (val% «da_verify» "roots")) * σ (.n (val% «da_verify» "n_blob_g")) ^ 2 * (gen ^ d) ^ 2) 0 (digestHalves daPadBlobDigest).1 ∧
      LoadHolds rd (σ (.n (val% «da_verify» "roots")) * σ (.n (val% «da_verify» "n_blob_g")) ^ 2 * (gen ^ d) ^ 2) 1 (digestHalves daPadBlobDigest).2 := by
    have hrel := call_of_flat hall hpad
    simp only [List.map_cons, List.map_nil] at hrel
    rw [h2] at hrel
    exact pad_sound hg' hrel
  -- the tree over the blob roots
  have hrt : (σ (.n (val% «da_verify» "r0")), σ (.n (val% «da_verify» "r1"))) = digestHalves (daTree r (guest_const% DA_LOG_MAX_ROWS) symsP) := by
    have hrel := call_of_flat hall hdl
    simp only [List.map_cons, List.map_nil] at hrel
    refine levels_root_of (Or.inl rfl) (by norm_num) (gen_pow_eq_ofK _).symm hrel fun i hi => ?_
    by_cases hir : i < r
    · exact hblob i hir
    · obtain ⟨g0, g1⟩ := L20 (i - r) (by norm_num at hi ⊢; omega)
      rw [h1, ← pow_mul, shift, show r * 2 + 2 * (i - r) = 2 * i by omega] at g0 g1
      simp only [blobLeaf, hir, ite_false]
      exact ⟨by simpa using g0, g1⟩
  -- the count's word, read off the table
  have hcnt : σ (.n (val% «da_verify» "s10#1")) = word r 0 := by
    have l := load_sound hld17 hat
    rw [isMul_sound hm16 hat, h1, loadHolds_mul_gen_pow, Nat.add_zero] at l
    exact loadHolds_unique l (hcw r (by rw [maxRows_eq]; exact hr))
  -- the root: the tree's, hashed with the count's word
  have hroot : (σ (.n (val% «da_verify» "commitment[0]")), σ (.n (val% «da_verify» "commitment[1]"))) = digestHalves (daRoot r (guest_const% DA_LOG_MAX_ROWS) symsP) := by
    simp only [Prod.ext_iff] at hrt
    rw [pairHashV_sound hph hat, hcnt, const_sound hc19 hat, word_zero, hrt.1, hrt.2,
      daRoot_cells (by rw [maxRows_eq]; exact hr)]
  refine ⟨daRoot r (guest_const% DA_LOG_MAX_ROWS) symsP, z, ?_, ?_⟩
  · rw [dvWit, hrows]
    exact opens_of hr1 (by rw [maxRows_eq]; exact hr) (by rw [maxRows_eq]; norm_num) hsL hdot
  rw [← hret, copy_sound hcp26 hat, copy_sound hcp27 hat, copy_sound hcp28 hat]
  simp only [Prod.ext_iff] at hroot
  simp [digestCells, ← hroot.1, ← hroot.2, z]


/-- **`da_verify`'s core IR gives its meaning.** -/
theorem da_verify_holds : da_verify_sound_Spec := by
  intro rd hm args rets hrel
  obtain ⟨σ, hpar, hb⟩ := (rel_iff_sem find_da_verify _ _).mp hrel
  have hp : (fn% «da_verify»).params.map σ = [σ (.n (val% «da_verify» "byte_bits"))] := rfl
  rw [hp] at hpar
  subst hpar
  simp only [MeaningDaVerify]
  intro hcw
  obtain ⟨root, z, ho, hr⟩ := da_verify_sound_w (unfoldsV_rel rd) (fun _ _ _ h => h) hm hcw hb
  exact ⟨_, root, z, ho, hr⟩
end
end LeanVM.Guest.B1.Da
