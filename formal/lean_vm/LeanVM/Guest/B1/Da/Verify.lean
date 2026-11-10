/-
  LeanVM.Guest.B1.Da.Verify

  `da_verify`'s core IR gives its meaning (TRIAGE G #90).
-/

module

public import LeanVM.Guest.B1.Da.Column
public import LeanVM.Guest.B1.Da.ColumnChk
public import LeanVM.Guest.B1.Da.VerifyChk
public import LeanVM.Guest.B1.Da.VerifyMath
public import LeanVM.Guest.B1.Main.LoopsC
public import LeanVM.Guest.B1.Main.Facts

/-!
# `da_verify`, sound

`da_verify_sound_w`: under a call relation that unfolds at a frame map `Vm` and lies below
`coreProgram.Rel`, with the exponent table, a run of `da_verify` returns the cells of a root and
the rate cells of a challenge `z` that the witness `dvWit σ Vm` opens (`opens_of`); with
`coreProgram.Rel` and a frame map by choice, `da_verify_holds : da_verify_sound_Spec`. The
witness's rows are the symbols of the cell checks' frames (`colSyms`, at the calls
`da_verify`'s structure makes: column `h`'s call `dvColArgs σ h`, its blob loop's iteration `i`,
its cell check); it mentions no hash. The run's loops make each blob's region
hold its cell digests (the leaves of its tree, whose root `da_levels__L128_L7` computes) and its
running sum of the cells' inner products with the dual codeword of `z` (`col_step`), which
`__loop23` checks to be zero; the returned root is the tree's over the blob roots and the padding
blob roots (`levels_root_of`).
-/

namespace LeanVM.Guest.B1.Da

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Value.Keccak
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Guest.B1.Digest LeanVM.Guest.B1.Main

@[expose] public section

variable {rd : Reader}

theorem ordG_of {x : ℕ} (h : x ≤ 4096) : x < ordG := by unfold ordG; omega

/-! ## The loops' steps -/

theorem l17_step {x : E} {ps : List E} (h : coreProgram.Rel rd "__loop21" (x :: ps) []) :
    (∀ N bl rb, ps = [N, bl, rb] →
      LoadHolds rd (rb * x) 0 (bl * x ^ 641) ∧ LoadHolds rd (bl * x ^ 641) 512 0) ∧
      (x * gen + ps.headD 0 ≠ 0 → coreProgram.Rel rd "__loop21" (x * gen :: ps) []) := by
  have hok := l17_ok
  simp only [Bool.and_eq_true, decide_eq_true_eq, l17Ok] at hok
  obtain ⟨⟨⟨⟨⟨⟨hshape, hlen⟩, hm15⟩, hm16⟩, hl15⟩, hc17⟩, hl17⟩ := hok
  obtain ⟨σ, hx, hps, hall, hnext⟩ :=
    loop_stepF (find_of_idx dv_loops_idx.1 (by rw [coreProgram_length]; omega)) hshape h
  refine ⟨fun N bl rb hN ↦ ?_, hnext⟩
  have hat := atoms_of_flat hall
  have hpar : (coreProgram.getD 416 default).params = [V.n 0, V.n 1, V.n 2, V.n 3] := by
    rw [loop_params hshape hlen]; rfl
  rw [hpar, hN] at hps
  simp only [List.tail_cons, List.map_cons, List.map_nil, List.cons.injEq, and_true] at hps
  obtain ⟨-, h2, h3⟩ := hps
  have p15 : σ (.n 15) = bl * x ^ 641 := by rw [monoIs_sound hm15 hat, h2, hx]
  have a := load_sound hl15 hat
  have b := load_sound hl17 hat
  rw [isMul_sound hm16 hat, h3, hx, p15] at a
  rw [p15, const_sound hc17 hat, word_zero] at b
  exact ⟨a, b⟩

theorem l19_step {x : E} {ps : List E} (h : coreProgram.Rel rd "__loop23" (x :: ps) []) :
    (∀ N rb roots, ps = [N, rb, roots] → ∃ base c0 c1, LoadHolds rd (rb * x) 0 base ∧
      LoadHolds rd base 640 0 ∧ coreProgram.Rel rd "da_levels__L128_L7" [base] [c0, c1] ∧
      LoadHolds rd (roots * x ^ 2) 0 c0 ∧ LoadHolds rd (roots * x ^ 2) 1 c1) ∧
      (x * gen + ps.headD 0 ≠ 0 → coreProgram.Rel rd "__loop23" (x * gen :: ps) []) := by
  have hok := l19_ok
  simp only [Bool.and_eq_true, decide_eq_true_eq, l19Ok] at hok
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hshape, hlen⟩, hm4⟩, hl5⟩, hl6⟩, hc7⟩, hae⟩, hcall⟩, hm10⟩, hm11⟩, hl8⟩,
    hl9⟩ := hok
  obtain ⟨σ, hx, hps, hall, hnext⟩ :=
    loop_stepF (find_of_idx dv_loops_idx.2.2.1 (by rw [coreProgram_length]; omega)) hshape h
  refine ⟨fun N rb roots hN ↦ ?_, hnext⟩
  have hat := atoms_of_flat hall
  have hpar : (coreProgram.getD 418 default).params = [V.n 0, V.n 1, V.n 2, V.n 3] := by
    rw [loop_params hshape hlen]; rfl
  rw [hpar, hN] at hps
  simp only [List.tail_cons, List.map_cons, List.map_nil, List.cons.injEq, and_true] at hps
  obtain ⟨-, h2, h3⟩ := hps
  have l5 := load_sound hl5 hat
  rw [isMul_sound hm4 hat, h2, hx] at l5
  have l6 := load_sound hl6 hat
  rw [assertEq_sound hae hat, const_sound hc7 hat, word_zero] at l6
  have c := call_of_flat hall hcall
  simp only [List.map_cons, List.map_nil] at c
  have p11 : σ (.n 11) = roots * x ^ 2 := by rw [isMul_sound hm11 hat, isMul_sound hm10 hat, h3, hx, sq]
  have l8 := load_sound hl8 hat
  have l9 := load_sound hl9 hat
  rw [p11] at l8 l9
  exact ⟨_, _, _, l5, l6, c, l8, l9⟩

theorem l20_step {x : E} {ps : List E} (h : coreProgram.Rel rd "__loop24" (x :: ps) []) :
    (∀ N roots nb, ps = [N, roots, nb] →
      LoadHolds rd (roots * nb ^ 2 * x ^ 2) 0 (digestHalves daPadBlobDigest).1 ∧
      LoadHolds rd (roots * nb ^ 2 * x ^ 2) 1 (digestHalves daPadBlobDigest).2) ∧
      (x * gen + ps.headD 0 ≠ 0 → coreProgram.Rel rd "__loop24" (x * gen :: ps) []) := by
  have hok := l20_ok
  simp only [Bool.and_eq_true, decide_eq_true_eq, l20Ok] at hok
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨hshape, hlen⟩, hm4⟩, hm5⟩, hm6⟩, hm7⟩, hc8⟩, hl8⟩, hc9⟩, hl9⟩ := hok
  obtain ⟨σ, hx, hps, hall, hnext⟩ :=
    loop_stepF (find_of_idx dv_loops_idx.2.2.2 (by rw [coreProgram_length]; omega)) hshape h
  refine ⟨fun N roots nb hN ↦ ?_, hnext⟩
  have hat := atoms_of_flat hall
  have hpar : (coreProgram.getD 419 default).params = [V.n 0, V.n 1, V.n 2, V.n 3] := by
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

/-! ## The witness -/

/-- Column `h`'s call's words. -/
def dvColArgs (σ : Val) (h : ℕ) : List E :=
  [gen ^ h, σ (.n 1), σ (.n 32), σ (.n 16), σ (.n 17), σ (.n 18), σ (.n 19)]

/-- Cell `(i, h)`'s symbols: its cell check's. -/
def dvSyms (σ : Val) (Vm : FrameMap) (i h : ℕ) : List K := colSyms Vm (dvColArgs σ h) i

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

/-! ## The columns, at the frame map -/

variable {C : CallRel} {Vm : FrameMap}

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

theorem l18_stepW (hVm : UnfoldsV rd C Vm) {x : E} {ps : List E} (h : C "__loop22" (x :: ps) []) :
    C "da_verify_column" (x :: ps) [] ∧
      (x * gen + word 325 0 ≠ 0 → C "__loop22" (x * gen :: ps) []) := by
  have hok := l18_ok
  unfold l18Ok at hok
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hok
  obtain ⟨hparams, hbody⟩ := hok
  obtain ⟨hpar, hb⟩ := body_ofV hVm (find_of_idx dv_loops_idx.2.1
    (by rw [coreProgram_length]; omega)) h
  set σ := Vm "__loop22" (x :: ps) [] with hσ
  rw [stmtsEqb_sound hbody] at hb
  have r7 : (List.range 7).map V.n = [V.n 0, V.n 1, V.n 2, V.n 3, V.n 4, V.n 5, V.n 6] := rfl
  have r6 : (List.range 6).map (fun k => V.n (k + 1)) =
      [V.n 1, V.n 2, V.n 3, V.n 4, V.n 5, V.n 6] := rfl
  rw [hparams, r7] at hpar
  simp only [List.map_cons, List.map_nil] at hpar
  obtain ⟨hx, hps⟩ := List.cons.inj hpar
  simp only [l18Body, Stmt.HoldsList, Stmt.Holds, Atom.Holds, r7, r6, List.map_cons,
    List.map_nil] at hb
  obtain ⟨hc, h7, h8, h9, h10, h11, h12, -, hcall, -⟩ := hb
  refine ⟨?_, fun hne => ?_⟩
  · rw [← hx, ← hps]; exact hc
  · have e10 : σ (.n 10) = x * gen + word 325 0 := by rw [h10, h8, h7, h9, word_gen, hx]
    have e12 : σ (.n 12) = x * gen := by rw [h12, h11, word_gen, hx]
    have := hcall (by rw [e10]; exact hne)
    rw [e12] at this
    rw [← hps]
    exact this

/-! ## The body -/

/-- **`da_verify`, soundly, its witness named**: under a call relation that unfolds at `Vm` and
lies below `coreProgram.Rel`, on a memory image with the exponent table at its argument, the
returned words are the cells of a root and the rate cells of a challenge `z` that `dvWit σ Vm`
opens. -/
theorem da_verify_sound_w (hVm : UnfoldsV rd C Vm) (hle : CallRel.Le C (coreProgram.Rel rd))
    (hm : MemOk rd) {σ : Val} {gsq : E} {rets : List E} (hpar0 : Data.core27.params.map σ = [gsq])
    (hb : Stmt.HoldsList C rd σ (Fn.body Data.core27) False (fun rs => rs = rets))
    (hsq0 : SquaresAt rd gsq) :
    ∃ (root : Digest) (z c2 : E), (dvWit σ Vm).Opens root z ∧ IsInK c2 ∧
      rets = digestCells root ++ [z + y * y * c2, c2 + y * eOfNat 0] := by
  have hok := dv_ok
  unfold dvOk at hok
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hok
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hparams, hbody⟩, hflat⟩, hcrs⟩, hc6⟩, hink⟩, hc10⟩, hm11⟩,
    ha12⟩, hc13⟩, hm14⟩, ha15⟩, hcv⟩, hg17⟩, hc36⟩, hc18⟩, hm38⟩, hg19⟩, hg20⟩, hdisp⟩, hcp48⟩,
    hcp49⟩, hcp50⟩, hcp51⟩ := hok
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
  have hrs := da_row_shape_holds rd hm _ _ (call_of_flat hall hcrs)
  simp only [List.map_cons, List.map_nil, MeaningDaRowShape] at hrs
  obtain ⟨r, L, hr1, hr, hL, h1, h2, hnp, h34⟩ := hrs hsq
  simp only [List.cons.injEq, and_true] at h34
  obtain ⟨h3, h4⟩ := h34
  unfold LeanDa.maxRows at hr
  have hL2 : 2 ^ L ≤ 1024 := by
    calc 2 ^ L ≤ 2 ^ 10 := Nat.pow_le_pow_right (by norm_num) hL
      _ = 1024 := by norm_num
  have hrL : r ≤ 2 ^ L := by
    rw [hnp, LeanDa.paddedRowCount, LeanDa.logPaddedRowCount]; exact Nat.le_pow_clog (by norm_num) r
  have hr' : r < ordG := ordG_of (by omega)
  have hg' : 2 ^ L - r < ordG := ordG_of (by omega)
  -- the challenge's cells
  set z := σ (.n 5)
  have c6 := hasAtom_sound hc6 hat
  have c10 := hasAtom_sound hc10 hat
  have m11 := hasAtom_sound hm11 hat
  have a12 := hasAtom_sound ha12 hat
  have c13 := hasAtom_sound hc13 hat
  have m14 := hasAtom_sound hm14 hat
  have a15 := hasAtom_sound ha15 hat
  have ik := hasAtom_sound hink hat
  simp only [Atom.Holds] at c6 c10 m11 a12 c13 m14 a15 ik
  have e12 : σ (.n 12) = z + y * y * σ (.n 9) := by rw [a12, m11, c10, word_yy]
  have e15 : σ (.n 15) = σ (.n 9) + y * eOfNat 0 := by rw [a15, m14, c13, c6, word_y, word_eOfNat]
  -- the dual codeword's builders
  have hvec := da_vector_holds rd _ _ (call_of_flat hall hcv)
  simp only [List.map_cons, List.map_nil] at hvec
  -- the regions
  have L17 : ∀ i < r, LoadHolds rd (σ (.n 32) * gen ^ i) 0 (σ (.n 31) * (gen ^ i) ^ 641) ∧
      LoadHolds rd (σ (.n 31) * (gen ^ i) ^ 641) 512 0 :=
    loop_sound (f := "__loop21") (ps := [σ (.n 1), σ (.n 31), σ (.n 32)]) hr' h1
      (fun y hy => by
        obtain ⟨k1, k2⟩ := l17_step hy
        exact ⟨k1 _ _ _ rfl, k2⟩)
      (fun hne => by simpa using guardK_sound hg17 hall hne)
  -- the columns
  have c18 := call_of_flat hallC hc18
  simp only [List.map_cons, List.map_nil] at c18
  rw [const_sound hc36 hat, word_one, ← pow_zero gen] at c18
  have Cc : ∀ h < 128, C "da_verify_column" (dvColArgs σ h) [] := fun h hh =>
    loop_fromC (C := C) (f := "__loop22") (N := gen ^ 128) (m := 128) (a := 0) (ordG_of (by omega))
      rfl (fun x hx => by
        obtain ⟨k1, k2⟩ := l18_stepW hVm hx
        exact ⟨k1, by rw [← word_g128]; exact k2⟩) c18 h (Nat.zero_le _) hh
  have hcargs : ∀ h, dvColArgs σ h = [gen ^ h, gen ^ r, σ (.n 32), σ (.n 16), σ (.n 17),
      σ (.n 18), σ (.n 19)] := fun h => by rw [dvColArgs, h1]
  have colF : ∀ h i, ∃ a : E, h < 128 → i < r → (dvSyms σ Vm i h).length = 256 ∧
      LoadHolds rd (σ (.n 31) * (gen ^ i) ^ 641) (2 * h)
        (digestHalves (keccak256 ((dvSyms σ Vm i h).flatMap K.toBytes))).1 ∧
      LoadHolds rd (σ (.n 31) * (gen ^ i) ^ 641) (2 * h + 1)
        (digestHalves (keccak256 ((dvSyms σ Vm i h).flatMap K.toBytes))).2 ∧
      LoadHolds rd (σ (.n 31) * (gen ^ i) ^ 641) (h + 512) a ∧
      LoadHolds rd (σ (.n 31) * (gen ^ i) ^ 641) (h + 513)
        (a + ∑ e ∈ Finset.range 256, dualAt z (256 * h + e) * ofK ((dvSyms σ Vm i h).getD e 0)) := by
    intro h i
    by_cases hhi : h < 128 ∧ i < r
    · have hc := Cc h hhi.1
      rw [hcargs] at hc
      obtain ⟨hl, base, a, hb0, k0, k1, k2, k3⟩ :=
        col_stepW hVm hle col_ok l21_ok l21_idx hhi.1 hr' hvec hc i hhi.2
      have e := loadHolds_unique hb0 (L17 i hhi.2).1
      rw [e] at k0 k1 k2 k3
      have hs : dvSyms σ Vm i h = colSyms Vm [gen ^ h, gen ^ r, σ (.n 32), σ (.n 16), σ (.n 17),
          σ (.n 18), σ (.n 19)] i := by rw [dvSyms, hcargs]
      rw [hs]
      exact ⟨a, fun _ _ => ⟨hl, k0, k1, k2, k3⟩⟩
    · exact ⟨0, fun a b => absurd ⟨a, b⟩ hhi⟩
  choose acc hcell using colF
  -- the witness's symbols, padded outside the run's ranges
  have hrows : dvRows σ = r := by
    rw [dvRows, h1, gLog_gen_pow (by omega)]; omega
  let symsP : ℕ → ℕ → List K := dvSymsP σ Vm
  have hsP : ∀ i h, i < r → h < 128 → symsP i h = dvSyms σ Vm i h := fun i h hi hh => by
    simp only [symsP, dvSymsP, hrows, hi, hh, and_self, ite_true]
  have hsL : ∀ i h, (symsP i h).length = 256 := fun i h => by
    by_cases hc : i < r ∧ h < 128
    · rw [hsP i h hc.1 hc.2]; exact (hcell h i hc.2 hc.1).1
    · simp only [symsP, dvSymsP, hrows, hc, ite_false, List.length_replicate]
  -- the blobs' sums and roots
  have L19 : ∀ i < r, ∃ base c0 c1, LoadHolds rd (σ (.n 32) * gen ^ i) 0 base ∧
      LoadHolds rd base 640 0 ∧ coreProgram.Rel rd "da_levels__L128_L7" [base] [c0, c1] ∧
      LoadHolds rd (σ (.n 39) * (gen ^ i) ^ 2) 0 c0 ∧ LoadHolds rd (σ (.n 39) * (gen ^ i) ^ 2) 1 c1 :=
    loop_sound (f := "__loop23") (ps := [σ (.n 1), σ (.n 32), σ (.n 39)]) hr' h1
      (fun y hy => by
        obtain ⟨k1, k2⟩ := l19_step hy
        exact ⟨k1 _ _ _ rfl, k2⟩)
      (fun hne => by simpa using guardK_sound hg19 hall hne)
  have hdot : ∀ i < r, ∑ h ∈ Finset.range 128, ∑ e ∈ Finset.range 256,
      dualAt z (256 * h + e) * ofK ((symsP i h).getD e 0) = 0 := by
    intro i hi
    obtain ⟨base, c0, c1, hb0, h640, -, -, -⟩ := L19 i hi
    rw [loadHolds_unique hb0 (L17 i hi).1] at h640
    have run : ∀ h ≤ 128, LoadHolds rd (σ (.n 31) * (gen ^ i) ^ 641) (h + 512)
        (∑ h' ∈ Finset.range h, ∑ e ∈ Finset.range 256,
          dualAt z (256 * h' + e) * ofK ((symsP i h').getD e 0)) := by
      intro h
      induction h with
      | zero => intro _; simpa using (L17 i hi).2
      | succ h ih =>
        intro hh
        obtain ⟨-, -, -, k2, k3⟩ := hcell h i (by omega) hi
        rw [loadHolds_unique k2 (ih (by omega)), ← hsP i h hi (by omega)] at k3
        rw [Finset.sum_range_succ, show h + 1 + 512 = h + 513 by ring]
        exact k3
    exact loadHolds_unique (run 128 le_rfl) h640
  have hblob : ∀ i < r, LoadHolds rd (σ (.n 39)) (2 * i) (digestHalves (blobLeaf r symsP i)).1 ∧
      LoadHolds rd (σ (.n 39)) (2 * i + 1) (digestHalves (blobLeaf r symsP i)).2 := by
    intro i hi
    obtain ⟨base, c0, c1, hb0, -, hlv, k0, k1⟩ := L19 i hi
    rw [loadHolds_unique hb0 (L17 i hi).1] at hlv
    have hroot := levels_root_of (k := 7) (L := 7) (g := cellD symsP i) (by norm_num) (by norm_num)
      (gen_pow_eq_ofK 7).symm hlv fun h hh => by
        obtain ⟨-, k0, k1, -, -⟩ := hcell h i (by simpa using hh) hi
        simp only [cellD, hsP i h hi (by simpa using hh)]
        exact ⟨k0, k1⟩
    rw [shift2] at k0 k1
    simp only [Prod.ext_iff] at hroot
    simp only [blobLeaf, hi, ite_true]
    rw [← hroot.1, ← hroot.2]
    exact ⟨by simpa using k0, k1⟩
  -- the padding blobs
  have L20 : ∀ d < 2 ^ L - r, LoadHolds rd (σ (.n 39) * σ (.n 1) ^ 2 * (gen ^ d) ^ 2) 0
        (digestHalves daPadBlobDigest).1 ∧
      LoadHolds rd (σ (.n 39) * σ (.n 1) ^ 2 * (gen ^ d) ^ 2) 1 (digestHalves daPadBlobDigest).2 :=
    loop_sound (f := "__loop24") (ps := [σ (.n 4), σ (.n 39), σ (.n 1)]) hg' h4
      (fun y hy => by
        obtain ⟨k1, k2⟩ := l20_step hy
        exact ⟨k1 _ _ _ rfl, k2⟩)
      (fun hne => by simpa using guardK_sound hg20 hall hne)
  -- the root
  have hrt : (σ (.n 46), σ (.n 47)) = digestHalves (daRoot r L symsP) := by
    obtain ⟨k, hk, hk2, hrel⟩ := dispatch_of_flat hall hdisp
    simp only [dlNames, List.length_map, List.length_range] at hk
    simp only [dlNames, List.getElem_map, List.getElem_range, List.map_cons, List.map_nil] at hrel
    refine levels_root_of hk hL (by rw [← hk2, h2]) hrel fun i hi => ?_
    by_cases hir : i < r
    · exact hblob i hir
    · obtain ⟨g0, g1⟩ := L20 (i - r) (by omega)
      rw [h1, ← pow_mul, shift, show r * 2 + 2 * (i - r) = 2 * i by omega] at g0 g1
      simp only [blobLeaf, hir, ite_false]
      exact ⟨by simpa using g0, g1⟩
  refine ⟨daRoot r L symsP, z, σ (.n 9), ?_, ik.1, ?_⟩
  · rw [dvWit, hrows]
    exact opens_of hr1 (by unfold LeanDa.maxRows; exact hr) hnp.symm hrL hsL hdot
  rw [← hret, copy_sound hcp48 hat, copy_sound hcp49 hat, copy_sound hcp50 hat,
    copy_sound hcp51 hat, e12, e15]
  simp only [Prod.ext_iff] at hrt
  simp [digestCells, ← hrt.1, ← hrt.2]


/-- **`da_verify`'s core IR gives its meaning.** -/
theorem da_verify_holds : da_verify_sound_Spec := by
  intro rd hm args rets hrel
  obtain ⟨σ, hpar, hb⟩ := (rel_iff_sem find_da_verify _ _).mp hrel
  have hp : Data.core27.params.map σ = [σ (.n 0)] := rfl
  rw [hp] at hpar
  subst hpar
  simp only [MeaningDaVerify]
  intro hsq
  obtain ⟨root, z, c2, ho, hc, hr⟩ :=
    da_verify_sound_w (unfoldsV_rel rd) (fun _ _ _ h => h) hm hp hb hsq
  exact ⟨_, root, z, c2, ho, hc, hr⟩
end
end LeanVM.Guest.B1.Da
