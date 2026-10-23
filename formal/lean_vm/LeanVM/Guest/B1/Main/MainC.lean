/-
  LeanVM.Guest.B1.Main.MainC

  `main` (G:3119-3316) backward: its honest valuation, and its body from its callees' relations and
  the honest words in memory.
-/

module

public import LeanVM.Guest.B1.Main.ChildrenC
public import LeanVM.Guest.B1.Main.Sound
public import LeanVM.Guest.B1.Uniform

/-!
# `main`, backward

`MainRun` is the words a run of `main` computes: the counts (declared claims, duplicates and raw
signatures per scheme, children, raw DA claims, declared and duplicate DA claims), the seed, the
pointers of its `HeapBuf`s and of the exponent tables, the digests its callees return, the direct
DA claim's cells and the leaf's deferred values. `mainVal rd R` is its valuation, each range
check's temporaries the words `rd` holds there. `MainOk C` is what the body needs of its callees
(under the call relation `C`) and of the memory; `main_body_holds` checks the body against the
valuation.
-/

namespace LeanVM.Guest.B1.Main

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Protocol LeanVM.Protocol.Blake2sHash LeanVM.Protocol.Verifier LeanVM.Node

@[expose] public section

variable {rd : Reader} {C : CallRel}

/-- **The words a run of `main` computes.** -/
structure MainRun where
  /-- Declared leanXMSS claims, their duplicates, the raw leanXMSS signatures. -/
  dx : ℕ
  ux : ℕ
  rx : ℕ
  /-- The same for leanSPHINCS. -/
  ds : ℕ
  us : ℕ
  rs : ℕ
  /-- Children, raw DA claims, declared DA claims, DA duplicates. -/
  nc : ℕ
  rd : ℕ
  da : ℕ
  ud : ℕ
  /-- The seed. -/
  seed : Digest
  /-- The exponent tables. -/
  glp : E
  gsq : E
  /-- The `HeapBuf`s: DA roots, the two claim tables, the signer pair, the coverage table, the
  children's public inputs, fresh and carried claims, the running counts, `defer_stmt`. -/
  daT : E
  xT : E
  sT : E
  sigp : E
  cover : E
  cpi : E
  cfresh : E
  carried : E
  written : E
  dstmt : E
  /-- The digests the callees return. -/
  daDig : Digest
  xDig : Digest
  sDig : Digest
  sigDig : Digest
  stDig : Digest
  /-- The direct DA claim's cells. -/
  dr0 : E
  dr1 : E
  dr2 : E
  dr3 : E
  /-- The leaf's deferred values. -/
  lbv : E
  lmA : E
  lmB : E

/-- The coverage table's size. -/
def MainRun.total (R : MainRun) : ℕ := R.dx + R.ux + (R.ds + R.us) + (R.da + R.ud)

/-- **`main`'s honest valuation**, the range checks' temporaries read from `rd`. -/
noncomputable def mainVal (rd : Reader) (R : MainRun) : Val :=
  setl (setv (setl (Val.ofArgs []) 0
    [gen ^ R.dx,
      gen ^ R.ux,
      gen ^ R.rx,
      gen ^ R.ds,
      gen ^ R.us,
      gen ^ R.rs,
      gen ^ R.nc,
      gen ^ R.rd,
      gen ^ 65535,
      gen ^ (65535 - R.dx),
      cellAt rd (gen ^ R.dx) 0,
      cellAt rd (gen ^ (65535 - R.dx)) 0,
      gen ^ 65535,
      gen ^ (65535 - R.ux),
      cellAt rd (gen ^ R.ux) 0,
      cellAt rd (gen ^ (65535 - R.ux)) 0,
      gen ^ 65535,
      gen ^ (65535 - R.rx),
      cellAt rd (gen ^ R.rx) 0,
      cellAt rd (gen ^ (65535 - R.rx)) 0,
      gen ^ 65535,
      gen ^ (65535 - R.ds),
      cellAt rd (gen ^ R.ds) 0,
      cellAt rd (gen ^ (65535 - R.ds)) 0,
      gen ^ 65535,
      gen ^ (65535 - R.us),
      cellAt rd (gen ^ R.us) 0,
      cellAt rd (gen ^ (65535 - R.us)) 0,
      gen ^ 65535,
      gen ^ (65535 - R.rs),
      cellAt rd (gen ^ R.rs) 0,
      cellAt rd (gen ^ (65535 - R.rs)) 0,
      gen ^ 16,
      gen ^ (16 - R.nc),
      cellAt rd (gen ^ R.nc) 0,
      cellAt rd (gen ^ (16 - R.nc)) 0,
      gen ^ 1,
      gen ^ (1 - R.rd),
      cellAt rd (gen ^ R.rd) 0,
      cellAt rd (gen ^ (1 - R.rd)) 0,
      gen ^ R.da,
      gen ^ R.ud,
      gen ^ 16,
      gen ^ (16 - R.da),
      cellAt rd (gen ^ R.da) 0,
      cellAt rd (gen ^ (16 - R.da)) 0,
      gen ^ 257,
      gen ^ (257 - R.ud),
      cellAt rd (gen ^ R.ud) 0,
      cellAt rd (gen ^ (257 - R.ud)) 0,
      gen ^ R.da * gen ^ R.ud,
      gen ^ 257,
      gen ^ (257 - (R.da + R.ud)),
      cellAt rd (gen ^ R.da * gen ^ R.ud) 0,
      cellAt rd (gen ^ (257 - (R.da + R.ud))) 0,
      gen ^ R.dx * gen ^ R.ux,
      gen ^ R.ds * gen ^ R.us,
      gen ^ R.dx * gen ^ R.ux * (gen ^ R.ds * gen ^ R.us),
      gen ^ R.dx * gen ^ R.ux * (gen ^ R.ds * gen ^ R.us) * (gen ^ R.da * gen ^ R.ud),
      gen ^ 65535,
      gen ^ (65535 - R.total),
      cellAt rd (gen ^ R.dx * gen ^ R.ux * (gen ^ R.ds * gen ^ R.us) * (gen ^ R.da * gen ^ R.ud)) 0,
      cellAt rd (gen ^ (65535 - R.total)) 0,
      (digestScalars R.seed).1,
      (digestScalars R.seed).2,
      R.glp,
      R.gsq,
      gen ^ R.da * gen ^ R.ud * (gen ^ R.da * gen ^ R.ud),
      gen ^ R.da * gen ^ R.ud * (gen ^ R.da * gen ^ R.ud) * (gen ^ R.da * gen ^ R.ud * (gen ^ R.da * gen ^ R.ud)),
      R.daT,
      1,
      1 + gen ^ R.da * gen ^ R.ud,
      1,
      (digestScalars R.daDig).1,
      (digestScalars R.daDig).2,
      gen ^ R.dx * gen ^ R.ux * (gen ^ R.dx * gen ^ R.ux),
      gen ^ R.dx * gen ^ R.ux * (gen ^ R.dx * gen ^ R.ux) * (gen ^ R.dx * gen ^ R.ux * (gen ^ R.dx * gen ^ R.ux)),
      R.xT,
      gen ^ R.ds * gen ^ R.us * (gen ^ R.ds * gen ^ R.us),
      gen ^ R.ds * gen ^ R.us * (gen ^ R.ds * gen ^ R.us) * (gen ^ R.ds * gen ^ R.us * (gen ^ R.ds * gen ^ R.us)),
      R.sT,
      (digestScalars R.xDig).1,
      (digestScalars R.xDig).2,
      (digestScalars R.sDig).1,
      (digestScalars R.sDig).2,
      1,
      1 + gen ^ R.ux,
      1,
      1,
      1 + gen ^ R.us,
      1,
      gen ^ R.dx * gen ^ R.ds,
      gen ^ R.dx * gen ^ R.ds * gen ^ R.da,
      1,
      gen ^ R.dx * gen ^ R.ds * gen ^ R.da + 1,
      (gen ^ R.dx * gen ^ R.ds * gen ^ R.da + 1)⁻¹,
      (gen ^ R.dx * gen ^ R.ds * gen ^ R.da + 1) * (gen ^ R.dx * gen ^ R.ds * gen ^ R.da + 1)⁻¹,
      Value.ivCells.1,
      Value.ivCells.2,
      metadataCell 64 true,
      (digestScalars R.sigDig).1,
      (digestScalars R.sigDig).2,
      R.sigp,
      R.cover,
      R.cover * (gen ^ R.dx * gen ^ R.ux * (gen ^ R.ds * gen ^ R.us)),
      1,
      1 + gen ^ R.rx,
      1,
      1,
      1 + gen ^ R.rs,
      1,
      gen,
      gen ^ R.rd + gen,
      R.dr0,
      R.dr1,
      R.dr2,
      R.dr3,
      gen ^ R.rx * gen ^ R.rs,
      R.dr0,
      R.dr1,
      R.dr2,
      R.dr3,
      gen ^ R.nc * gen ^ R.nc,
      R.cpi,
      gen ^ (2 * R.nc),
      gen ^ (3 * R.nc),
      gen ^ (6 * R.nc),
      gen ^ (12 * R.nc),
      gen ^ (13 * R.nc),
      gen ^ (26 * R.nc),
      gen ^ (52 * R.nc),
      gen ^ (53 * R.nc),
      gen ^ (106 * R.nc),
      R.cfresh,
      gen ^ (2 * R.nc),
      gen ^ (3 * R.nc),
      gen ^ (6 * R.nc),
      gen ^ (12 * R.nc),
      gen ^ (13 * R.nc),
      gen ^ (26 * R.nc),
      gen ^ (52 * R.nc),
      gen ^ (53 * R.nc),
      R.carried,
      gen,
      gen ^ R.nc * gen,
      R.written,
      gen ^ R.rx * gen ^ R.rs,
      gen ^ R.rx * gen ^ R.rs * gen ^ R.rd,
      1,
      1 + gen ^ R.nc,
      1,
      R.written * gen ^ R.nc,
      gen ^ R.dx * gen ^ R.ux * (gen ^ R.ds * gen ^ R.us) * (gen ^ R.da * gen ^ R.ud),
      R.dstmt,
      1,
      gen ^ R.nc + 1,
      R.lbv,
      R.lmA,
      R.lmB]) 159 50 fun _ => 0) 209
    [(digestScalars R.stDig).1,
      (digestScalars R.stDig).2,
      1,
      (digestScalars R.stDig).1,
      1,
      gen,
      1 * gen,
      (digestScalars R.stDig).2]

/-- **What `main`'s body needs**: the counts' bounds, its callees' relations, the compression of
the signer set, and the words of its `HeapBuf`s and of the public input. -/
structure MainOk (C : CallRel) (rd : Reader) (R : MainRun) : Prop where
  low : LeanVM.Guest.B1.LowDef 16 rd
  total : R.total ≤ 65535
  nc : R.nc ≤ 16
  rd1 : R.rd ≤ 1
  da : R.da ≤ 16
  ud : R.ud ≤ 257
  dau : R.da + R.ud ≤ 257
  rx : R.rx ≤ 65535
  rs : R.rs ≤ 65535
  decl : 0 < R.dx + R.ds + R.da
  tables : C "exponent_tables" [] [R.glp, R.gsq]
  loop0 : R.da + R.ud ≠ 0 → C "__loop0" [1, gen ^ R.da * gen ^ R.ud, R.daT] []
  daList : C "da_list_digest" [R.daT, gen ^ R.da]
    [(digestScalars R.daDig).1, (digestScalars R.daDig).2]
  xList : C "claim_list_digest" [R.xT, gen ^ R.dx, R.gsq]
    [(digestScalars R.xDig).1, (digestScalars R.xDig).2]
  sList : C "claim_list_digest" [R.sT, gen ^ R.ds, R.gsq]
    [(digestScalars R.sDig).1, (digestScalars R.sDig).2]
  loop1 : R.ux ≠ 0 → C "__loop1" [1, gen ^ R.ux, R.xT, gen ^ R.dx] []
  loop2 : R.us ≠ 0 → C "__loop2" [1, gen ^ R.us, R.sT, gen ^ R.ds] []
  sig : CompressCells ![(digestScalars R.xDig).1, (digestScalars R.xDig).2, (digestScalars R.sDig).1,
    (digestScalars R.sDig).2] Value.ivCells.1 Value.ivCells.2 (digestScalars R.sigDig).1
    (digestScalars R.sigDig).2 (metadataCell 64 true)
  sigp : ReadsAt rd R.sigp [(digestScalars R.sigDig).1, (digestScalars R.sigDig).2]
  loop3 : R.rx ≠ 0 → C "__loop3"
    [1, gen ^ R.rx, gen ^ R.dx * gen ^ R.ux, R.cover, R.xT] []
  loop4 : R.rs ≠ 0 → C "__loop4"
    [1, gen ^ R.rs, gen ^ R.ds * gen ^ R.us, R.cover, gen ^ R.dx * gen ^ R.ux, gen ^ R.rx, R.sT] []
  daVerify : R.rd = 1 → C "da_verify" [R.gsq] [R.dr0, R.dr1, R.dr2, R.dr3]
  daCover : R.rd = 1 → C "cover_da_root"
    [R.daT, R.cover * (gen ^ R.dx * gen ^ R.ux * (gen ^ R.ds * gen ^ R.us)),
      gen ^ R.da * gen ^ R.ud, gen ^ R.rx * gen ^ R.rs] [R.dr0, R.dr1, R.dr2, R.dr3]
  written0 : LoadHolds rd R.written 0 (gen ^ R.rx * gen ^ R.rs * gen ^ R.rd)
  loop5 : R.nc ≠ 0 → C "__loop5"
    [1, gen ^ R.nc, R.written, R.xT, R.cover, gen ^ R.dx * gen ^ R.ux, R.gsq, R.sT,
      gen ^ R.ds * gen ^ R.us, R.carried, R.daT,
      R.cover * (gen ^ R.dx * gen ^ R.ux * (gen ^ R.ds * gen ^ R.us)), gen ^ R.da * gen ^ R.ud,
      (digestScalars R.seed).1, (digestScalars R.seed).2, R.cpi, R.glp, R.cfresh] []
  writtenN : LoadHolds rd R.written R.nc
    (gen ^ R.dx * gen ^ R.ux * (gen ^ R.ds * gen ^ R.us) * (gen ^ R.da * gen ^ R.ud))
  leaf : R.nc = 0 → ReadsAt rd R.dstmt
    (List.replicate 22 0 ++ [R.lbv] ++ List.replicate 28 0 ++ [R.lmA, R.lmB])
  agg : R.nc ≠ 0 → C "aggregate_claims"
    [gen ^ R.nc, R.cpi, R.cfresh, R.carried, R.dstmt] []
  stmt : C "statement_digest"
    [(digestScalars R.seed).1, (digestScalars R.seed).2, R.sigp, (digestScalars R.daDig).1,
      (digestScalars R.daDig).2, R.dstmt] [(digestScalars R.stDig).1, (digestScalars R.stDig).2]
  pub0 : rd 1 = some (digestScalars R.stDig).1
  pub1 : rd g = some (digestScalars R.stDig).2

theorem loadHolds_cellAt_gen (hl : LeanVM.Guest.B1.LowDef 16 rd) {e : ℕ} (he : e < 2 ^ 16) :
    LoadHolds rd (gen ^ e) 0 (cellAt rd (gen ^ e) 0) := by
  have := LeanVM.Guest.B1.loadHolds_low hl he
  rw [gen_pow_eq_ofK, cellAt, addr_ofK, Nat.add_zero]
  exact this

theorem ne_zero_of_one_add {k : ℕ} (h : 1 + gen ^ k ≠ 0) : k ≠ 0 := fun hk =>
  h (by rw [hk, pow_zero]; exact e_add_eq_zero_iff.mpr rfl)

theorem one_add_isInK (k : ℕ) : IsInK (1 + gen ^ k) :=
  isInK_add (by simpa using gen_pow_isInK 0) (gen_pow_isInK _)

theorem one_add_isInK' (a b : ℕ) : IsInK (1 + gen ^ a * gen ^ b) := by
  rw [← pow_add]; exact one_add_isInK _

set_option maxRecDepth 100000 in
theorem main_pre_holds {R : MainRun} (h : MainOk C rd R) :
    Stmt.HoldsList C rd (mainVal rd R) mainPre True (fun rs => rs = []) := by
  simp only [mainPre, Stmt.HoldsList, Stmt.Holds, Atom.Holds, List.map_cons, List.map_nil,
    word_gmax, word_g16, word_g257, word_gen, word_one, word_iv0, word_iv1, word_md64]
  simp only [mainVal]
  b1_look
  simp only [true_and, and_true]
  have hm := h.low
  have ht := h.total
  have hda := h.dau
  simp only [MainRun.total] at ht
  have e50 : gen ^ R.da * gen ^ R.ud = gen ^ (R.da + R.ud) := (pow_add _ _ _).symm
  have e58 : gen ^ R.dx * gen ^ R.ux * (gen ^ R.ds * gen ^ R.us) * (gen ^ R.da * gen ^ R.ud) =
      gen ^ R.total := by rw [MainRun.total]; simp only [← pow_add]
  have hT : R.total ≤ 65535 := h.total
  have rc : ∀ e b, e ≤ b → b < 2 ^ 16 → LoadHolds rd (gen ^ e) 0 (cellAt rd (gen ^ e) 0) ∧
      gen ^ b = gen ^ e * gen ^ (b - e) ∧
      LoadHolds rd (gen ^ (b - e)) 0 (cellAt rd (gen ^ (b - e)) 0) := fun e b h1 h2 =>
    ⟨loadHolds_cellAt_gen hm (by omega), by rw [← pow_add]; congr 1; omega,
      loadHolds_cellAt_gen hm (by omega)⟩
  have h0 : 0 < R.dx + R.ds + R.da := h.decl
  refine ⟨rc _ _ (by omega) (by norm_num), rc _ _ (by omega) (by norm_num),
    rc _ _ h.rx (by norm_num), rc _ _ (by omega) (by norm_num), rc _ _ (by omega) (by norm_num),
    rc _ _ h.rs (by norm_num), rc _ _ h.nc (by norm_num), pow_one gen, rc _ _ h.rd1 (by norm_num),
    rc _ _ h.da (by norm_num), rc _ _ h.ud (by norm_num), ?_, ?_, h.tables, one_add_isInK' _ _,
    fun hne => h.loop0 (by intro hz; apply hne; rw [e50, hz, pow_zero]; exact e_add_eq_zero_iff.mpr rfl),
    h.daList, h.xList, h.sList, one_add_isInK _, fun hne => h.loop1 (ne_zero_of_one_add hne),
    one_add_isInK _, fun hne => h.loop2 (ne_zero_of_one_add hne), ?_, h.sig,
    by simpa using h.sigp 0 (by simp), by simpa using h.sigp 1 (by simp), one_add_isInK _,
    fun hne => h.loop3 (ne_zero_of_one_add hne), one_add_isInK _,
    fun hne => h.loop4 (ne_zero_of_one_add hne)⟩
  · rw [e50]; exact rc _ _ hda (by norm_num)
  · rw [e58]; exact rc _ _ hT (by norm_num)
  · apply mul_inv_cancel₀
    rw [← pow_add, ← pow_add, add_comm]
    exact one_add_gen_pow_ne_zero h0 (by unfold ordG; omega)

theorem gen_pow_add_gen_eq_zero {k : ℕ} (hk : k ≤ 1) (h : gen ^ k + gen = 0) : k = 1 := by
  rcases Nat.lt_or_ge k 1 with h' | h'
  · rw [show k = 0 by omega, pow_zero] at h
    exact absurd h (by simpa using one_add_gen_pow_ne_zero (m := 1) (by norm_num) (by unfold ordG; omega))
  · omega

set_option maxRecDepth 100000 in
theorem main_da_holds {R : MainRun} (h : MainOk C rd R) (h0 : mainVal rd R (.n 112) = 0) :
    Stmt.HoldsList C rd (mainVal rd R) daBranch True (fun rs => rs = []) := by
  have e : mainVal rd R (.n 112) = gen ^ R.rd + gen := by simp only [mainVal]; b1_look
  have h1 := gen_pow_add_gen_eq_zero h.rd1 (e ▸ h0)
  simp only [daBranch, Stmt.HoldsList, Stmt.Holds, Atom.Holds, List.map_cons, List.map_nil]
  simp only [mainVal]
  b1_look
  simp only [true_and, and_true]
  exact ⟨h.daVerify h1, h.daCover h1, e_add_eq_zero_iff.mpr rfl, e_add_eq_zero_iff.mpr rfl,
    e_add_eq_zero_iff.mpr rfl, e_add_eq_zero_iff.mpr rfl⟩

set_option maxRecDepth 100000 in
theorem main_mid_holds {R : MainRun} (h : MainOk C rd R) :
    Stmt.HoldsList C rd (mainVal rd R) mainMid True (fun rs => rs = []) := by
  simp only [mainMid, Stmt.HoldsList, Stmt.Holds, Atom.Holds, List.map_cons, List.map_nil, word_gen,
    word_one]
  simp only [mainVal]
  b1_look
  simp only [true_and, and_true]
  refine ⟨by ring, by ring, by ring, by ring, by ring, by ring, by ring, by ring, by ring, by ring,
    by ring, by ring, by ring, by ring, by ring, by ring, by ring, h.written0, one_add_isInK _,
    fun hne => h.loop5 (ne_zero_of_one_add hne), loadHolds_of_mul0 rfl h.writtenN,
    e_add_eq_zero_iff.mpr rfl⟩

theorem gen_pow_add_one_eq_zero {k : ℕ} (hk : k ≤ 16) (h : gen ^ k + 1 = 0) : k = 0 := by
  by_contra hne
  rw [add_comm] at h
  exact one_add_gen_pow_ne_zero (by omega) (by unfold ordG; omega) h

set_option maxRecDepth 100000 in
theorem main_leaf_holds {R : MainRun} (h : MainOk C rd R) (h0 : mainVal rd R (.n 155) = 0) :
    Stmt.HoldsList C rd (mainVal rd R) leafT True (fun rs => rs = []) := by
  have e : mainVal rd R (.n 155) = gen ^ R.nc + 1 := by simp only [mainVal]; b1_look
  have h1 := gen_pow_add_one_eq_zero h.nc (e ▸ h0)
  have hl := h.leaf h1
  rw [leafT, Stmt.HoldsList, Stmt.Holds]
  simp only [holdsList_append]
  rw [holdsList_range_flatten 22 (zeroStores 159 0) (fun _ => rfl),
    holdsList_range_flatten 28 (zeroStores 181 23) (fun _ => rfl)]
  simp only [zeroStores, Stmt.HoldsList, Stmt.Holds, Atom.Holds, word_zero, and_true, true_and]
  have hs : ∀ k < 53, LoadHolds rd R.dstmt k
      ((List.replicate 22 (0 : E) ++ [R.lbv] ++ List.replicate 28 0 ++ [R.lmA, R.lmB]).getD k 0) :=
    fun k hk => readsAt_getD' hl (by simp; omega)
  have z1 : ∀ k < 22,
      (List.replicate 22 (0 : E) ++ [R.lbv] ++ List.replicate 28 0 ++ [R.lmA, R.lmB]).getD k 0 = 0 := by
    intro k hk
    interval_cases k <;> rfl
  have z2 : ∀ k < 28,
      (List.replicate 22 (0 : E) ++ [R.lbv] ++ List.replicate 28 0 ++ [R.lmA, R.lmB]).getD (23 + k) 0 =
        0 := by
    intro k hk
    interval_cases k <;> rfl
  simp only [mainVal]
  refine ⟨fun k hk => ⟨by b1_look, ?_⟩, ?_, fun k hk => ⟨by b1_look, ?_⟩, ?_, ?_⟩
  · b1_look; rw [← z1 k hk]; exact hs k (by omega)
  · b1_look; exact hs 22 (by omega)
  · b1_look; rw [← z2 k hk]; exact hs _ (by omega)
  · b1_look; exact hs 51 (by omega)
  · b1_look; exact hs 52 (by omega)

set_option maxRecDepth 100000 in
theorem main_agg_holds {R : MainRun} (h : MainOk C rd R) (h0 : mainVal rd R (.n 155) ≠ 0) :
    Stmt.HoldsList C rd (mainVal rd R) aggT True (fun rs => rs = []) := by
  have e : mainVal rd R (.n 155) = gen ^ R.nc + 1 := by simp only [mainVal]; b1_look
  have h1 : R.nc ≠ 0 := fun hz => h0 (by rw [e, hz, pow_zero]; exact e_add_eq_zero_iff.mpr rfl)
  simp only [aggT, Stmt.HoldsList, Stmt.Holds, List.map_cons, List.map_nil, and_true]
  simp only [mainVal]
  b1_look
  exact h.agg h1

set_option maxRecDepth 100000 in
theorem main_post_holds {R : MainRun} (h : MainOk C rd R) :
    Stmt.HoldsList C rd (mainVal rd R) mainPost False (fun rs => rs = []) := by
  simp only [mainPost, Stmt.HoldsList, Stmt.Holds, Atom.Holds, List.map_cons, List.map_nil, word_gen,
    word_one]
  simp only [mainVal]
  b1_look
  simp only [true_and, and_true]
  have l1 : LoadHolds rd 1 0 (digestScalars R.stDig).1 := by
    refine ⟨by simpa using gen_pow_isInK 0, ?_⟩
    rw [show (1 : E).limb 0 * Parameters.gpow 0 = 1 by
      rw [← ofK_one, limb_ofK]; simp [Parameters.gpow]]
    exact h.pub0
  have l2 : LoadHolds rd gen 0 (digestScalars R.stDig).2 := by
    refine ⟨by simpa using gen_pow_isInK 1, ?_⟩
    rw [show gen.limb 0 * Parameters.gpow 0 = g by simp [Parameters.gpow, gen_eq_ofK]]
    exact h.pub1
  exact ⟨h.stmt, l1, e_add_eq_zero_iff.mpr rfl, by rw [one_mul]; exact l2, e_add_eq_zero_iff.mpr rfl⟩

/-- **`main`'s body on its honest valuation.** -/
theorem main_body_holds {R : MainRun} (h : MainOk C rd R) :
    Stmt.HoldsList C rd (mainVal rd R) mainBody False (fun rs => rs = []) := by
  rw [mainBody, holdsList_append, holdsList_noRet mainPre rfl, Stmt.HoldsList,
    holds_ite_noRet (.n 112) daBranch [] rfl rfl, holdsList_append, holdsList_noRet mainMid rfl,
    show Stmt.HoldsList C rd (mainVal rd R) (Stmt.ite (.n 155) leafT aggT :: mainPost)
      False (fun rs => rs = []) = Stmt.Holds C rd (mainVal rd R)
        (Stmt.ite (.n 155) leafT aggT)
        (Stmt.HoldsList C rd (mainVal rd R) mainPost False (fun rs => rs = []))
        (fun rs => rs = []) from rfl,
    holds_ite_noRet (.n 155) leafT aggT rfl rfl]
  refine ⟨main_pre_holds h, ⟨?_, main_da_holds h, fun _ => trivial⟩, main_mid_holds h,
    ⟨?_, main_leaf_holds h, main_agg_holds h⟩, main_post_holds h⟩
  · have e : mainVal rd R (.n 112) = gen ^ R.rd + gen := by simp only [mainVal]; b1_look
    rw [e]; exact isInK_add (gen_pow_isInK _) (by simpa using gen_pow_isInK 1)
  · have e : mainVal rd R (.n 155) = gen ^ R.nc + 1 := by simp only [mainVal]; b1_look
    rw [e]; exact isInK_add (gen_pow_isInK _) (by simpa using gen_pow_isInK 0)

/-- **`main` holds** once its body's needs hold (`MainOk`). -/
theorem main_rel_of_ok {R : MainRun} (h : MainOk (coreProgram.Rel rd) rd R) :
    coreProgram.Rel rd "main" [] [] := by
  rw [rel_iff_sem find_main]
  exact ⟨mainVal rd R, rfl, by rw [core0_body]; exact main_body_holds h⟩

end
end LeanVM.Guest.B1.Main
