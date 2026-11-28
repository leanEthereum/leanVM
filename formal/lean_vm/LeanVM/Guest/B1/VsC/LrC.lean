/-
  LeanVM.Guest.B1.VsC.LrC

  `level_residual`'s two loops complete with no words of their own, and every valid tree of them
  has its shape.
-/

module

public import LeanVM.Guest.B1.VsC.LoopFlat
public import LeanVM.Guest.B1.Whir.LrSound

/-!
# `level_residual`'s loops, complete

`level_residual` at `q` queries runs `b = q / resBatch` batches (`lrLoop1Body`, `resBatch` inline
residual queries an iteration), then `r = q % resBatch` single steps (`lrLoop2Body`), advancing the
two chains it keeps in its buffer `chain`: pair `i` (cells `2i`, `2i + 1`) holds the chains over the
first `lrCnt b i` positions (`lrPair`), the honest words `lrChainL`.

Each iteration is evaluated forward (`fwdVal`) on the memory: its atoms need no side condition or
load through a pointer the kernel's `lr1Checks` / `lr2Checks` names (the row, the high part, the
iteration's positions, the iteration's chain pair), but for its two stores, whose words are the
next pair (the guest stream's `osResSteps_val`, `osResQuery_val`).

* `lr1_loop`, `lr2_loop`: the loops complete from iteration `j`, with no words of their own.
* `lr1_shape`, `lr2_shape`: every valid tree of them from iteration `j` has block `lpB`, ends at
  its cursor, and loads from the region holding the arrays.
-/

namespace LeanVM.Guest.B1.VsC

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Memory LeanVM.Guest.B1
open LeanVM.Guest.Complete LeanVM.Guest.B1.Fwd LeanVM.Guest.Value LeanVM.Guest.B1.Whir
open LeanVM.Protocol.Verifier

@[expose] public section

/-! ## The honest chain -/

/-- The positions folded into pair `i`: `resBatch` a batch for the `b` batches, then one a step. -/
def lrCnt (b i : ℕ) : ℕ := if i ≤ b then resBatch * i else resBatch * b + (i - b)

/-- The chains over the first `n` positions. -/
def lrPair (P H : E → E) (mu : E) (Pos : ℕ → E) (n : ℕ) : E × E :=
  resFold P H mu (0, 0) ((List.range n).map Pos)

/-- The chain buffer's honest words: pair `i` for `i ≤ b + r`. -/
def lrChainL (P H : E → E) (mu : E) (Pos : ℕ → E) (b r : ℕ) : List E :=
  (List.range (2 * (b + r + 1))).map fun i =>
    if i % 2 = 0 then (lrPair P H mu Pos (lrCnt b (i / 2))).1 else (lrPair P H mu Pos (lrCnt b (i / 2))).2

theorem lrPair_add (P H : E → E) (mu : E) (Pos : ℕ → E) (n m : ℕ) :
    resFold P H mu (lrPair P H mu Pos n) ((List.range m).map fun i => Pos (n + i)) = lrPair P H mu Pos (n + m) := by
  simp only [lrPair]
  rw [← resFold_append, List.range_add, List.map_append, List.map_map]
  rfl

/-- A word at `a + m + o` of a run at `ptrAt a`, read at `ptrAt (a + m)`. -/
theorem readsAt_off {rd : Reader} {a : ℕ} {l : List E} (h : ReadsAt rd (ptrAt a) l) {m o : ℕ}
    (hk : m + o < l.length) : LoadHolds rd (ptrAt (a + m)) o l[m + o] := by
  rw [← ptrAt_mul_gen, loadHolds_mul_gen_pow]; exact h _ hk

theorem loadHolds_ptrAt_add {rd : Reader} {a m o : ℕ} {v : E} :
    LoadHolds rd (ptrAt (a + m)) o v ↔ LoadHolds rd (ptrAt a) (m + o) v := by
  rw [← ptrAt_mul_gen, loadHolds_mul_gen_pow]

theorem lrChain_load {rd : Reader} {P H : E → E} {mu : E} {Pos : ℕ → E} {b r a : ℕ}
    (h : ReadsAt rd (ptrAt a) (lrChainL P H mu Pos b r)) {i : ℕ} (hi : i ≤ b + r) :
    LoadHolds rd (ptrAt a) (2 * i) (lrPair P H mu Pos (lrCnt b i)).1 ∧
      LoadHolds rd (ptrAt a) (2 * i + 1) (lrPair P H mu Pos (lrCnt b i)).2 := by
  constructor
  · have := h (2 * i) (by simp [lrChainL]; omega)
    simp only [lrChainL, List.getElem_map, List.getElem_range] at this
    split at this
    · rwa [show 2 * i / 2 = i by omega] at this
    · omega
  · have := h (2 * i + 1) (by simp [lrChainL]; omega)
    simp only [lrChainL, List.getElem_map, List.getElem_range] at this
    split at this
    · omega
    · rwa [show (2 * i + 1) / 2 = i by omega] at this

/-- The parameters of a valuation mapping `osParams n` to `args`. -/
theorem param_of_map {σ : Val} {args : List E} {n : ℕ} (h : (osParams n).map σ = args) {i : ℕ}
    (hi : i < n) : σ (.n i) = args.getD i 0 := by
  rw [← h]
  simp [osParams, List.getD_eq_getElem?_getD, hi]

/-- `osLoopTailA`'s atoms need no side condition. -/
theorem osLoopTailA_noSide (k : ℕ) : ∀ s ∈ osLoopTailA k, ∃ a, s = .atom a ∧ needsSide a = false := by
  intro s hs
  simp only [osLoopTailA, List.mem_cons, List.not_mem_nil, or_false] at hs
  rcases hs with rfl | rfl | rfl | rfl | rfl <;> exact ⟨_, rfl, by simp [needsSide]⟩

/-- The block of atoms `L` holds where its atoms needing no side condition do. -/
theorem allOk_noSide {C : CallRel} {rd : Reader} {σ : Val} {L L' : List Stmt}
    (hsub : ∀ s ∈ L', s ∈ L) (hL : ∀ s ∈ L', ∃ a, s = .atom a ∧ needsSide a = false)
    (h : ∀ a, Stmt.atom a ∈ L → needsSide a = false → a.Holds rd σ) : AllOk C rd σ L' := by
  intro s hs
  obtain ⟨a, rfl, hn⟩ := hL s hs
  exact h a (hsub _ hs) hn

/-- What a `level_residual` loop reads: the positions, the row, the high part, the chain. -/
def LrMem (q cols nhs hbits ip irow ihs ic : ℕ) (mu : E) (D Pos : ℕ → E) (hsv : List E) (rd : Reader) : Prop :=
  ReadsAt rd (ptrAt ip) (posL q Pos) ∧ ReadsAt rd (ptrAt irow) ((List.range cols).map D) ∧
    ReadsAt rd (ptrAt ihs) hsv ∧
    ReadsAt rd (ptrAt ic) (lrChainL (lrP cols D) (lrH cols nhs hbits hsv) mu Pos (q / resBatch) (q % resBatch))

theorem lrMem_row {q cols nhs hbits ip irow ihs ic : ℕ} {mu : E} {D Pos : ℕ → E} {hsv : List E} {rd : Reader}
    (h : LrMem q cols nhs hbits ip irow ihs ic mu D Pos hsv rd) {s : ℕ} (hs : s < cols) :
    LoadHolds rd (ptrAt irow) s (D s) := by
  have := h.2.1 s (by simpa using hs)
  simpa using this

theorem lrMem_high {q cols nhs hbits ip irow ihs ic : ℕ} {mu : E} {D Pos : ℕ → E} {hsv : List E} {rd : Reader}
    (h : LrMem q cols nhs hbits ip irow ihs ic mu D Pos hsv rd) {c : ℕ} (hc : c < hsv.length) :
    LoadHolds rd (ptrAt ihs) c (hsv.getD c 0) := by
  rw [List.getD_eq_getElem _ _ hc]; exact h.2.2.1 c hc

theorem lrMem_pos {q cols nhs hbits ip irow ihs ic : ℕ} {mu : E} {D Pos : ℕ → E} {hsv : List E} {rd : Reader}
    (h : LrMem q cols nhs hbits ip irow ihs ic mu D Pos hsv rd) {m o : ℕ} (hk : m + o < q) :
    LoadHolds rd (ptrAt (ip + m)) o (Pos (m + o)) := by
  have := readsAt_off h.1 (m := m) (o := o) (by simpa [posL] using hk)
  simpa [posL] using this

/-! ## The batches' loop -/

/-- The batches' loop's stores: the next pair into the iteration's chain cells `2`, `3`. -/
def lr1Stores (cols nhs hbits : ℕ) : List Atom :=
  [.load (.n (lr1St cols nhs hbits).2.1) (.n (7 + batchLen + 2)) 2,
    .load (.n (lr1St cols nhs hbits).2.2.1) (.n (7 + batchLen + 2)) 3]

/-- The batches' loop's pointers: the row, the high part, the batch's positions, its chain pair. -/
def lr1Ps (cols nhs : ℕ) : List (ℕ × ℕ) :=
  [(4, cols), (5, nhs), (7 + batchLen, resBatch), (7 + batchLen + 2, 4)]

/-- The batches' loop's body before its tail call. -/
abbrev lr1L (cols nhs hbits : ℕ) : List Stmt := lr1A cols nhs hbits ++ osLoopTailA (lr1St cols nhs hbits).2.2.2

/-- The tail call's arguments. -/
abbrev lr1T (cols nhs hbits : ℕ) : List V :=
  .n ((lr1St cols nhs hbits).2.2.2 + 4) :: (List.range (7 - 1)).map fun i ↦ .n (i + 1)

/-- What the kernel checks of a specialization's batches' loop. -/
def lr1Checks (cols nhs hbits : ℕ) (name : String) : Bool :=
  (chk 7 (lrLoop1Body cols nhs hbits name)).isSome &&
    decide (storesOf 7 (lrLoop1Body cols nhs hbits name) = lr1Stores cols nhs hbits) &&
    (lr1L cols nhs hbits).all Stmt.isAtom &&
    (atomsOf (lr1L cols nhs hbits)).all (loadOkB (lr1Ps cols nhs)) &&
    (lr1St cols nhs hbits).1.all Stmt.isAtom &&
    (atomsOf (lr1St cols nhs hbits).1).all (fun a => decide (a ∉ lr1Stores cols nhs hbits)) &&
    decide (1 ≤ cols ∧ 1 ≤ nhs ∧ hbits ≤ 3 ∧ hbits ≤ cols + 1)

/-- The batches' loop's fixed atoms need no side condition. -/
theorem lr1_fixed :
    (osBatchPow 7).1.all (fun s => match s with | .atom a => !needsSide a | _ => false) = true ∧
      needsSide (.mul (.n (7 + batchLen)) (.n 2) (.n (osBatchPow 7).2)) = false ∧
      needsSide (.mul (.n (7 + batchLen + 1)) (.n 3) (.n 0)) = false ∧
      needsSide (.mul (.n (7 + batchLen + 2)) (.n (7 + batchLen + 1)) (.n 0)) = false := by
  decide +kernel

/-- The batches' loop's arguments at iteration `j` of `b`. -/
def lr1Args (j b ip ic irow ihs : ℕ) (mu : E) : List E :=
  [gen ^ j, gen ^ b, ptrAt ip, ptrAt ic, ptrAt irow, ptrAt ihs, mu]

theorem lr1_body {cols nhs hbits : ℕ} {name : String} (hat : (lr1L cols nhs hbits).all Stmt.isAtom = true) :
    lrLoop1Body cols nhs hbits name = ((atomsOf (lr1L cols nhs hbits)).map Stmt.atom ++
      [Stmt.callIf (.n ((lr1St cols nhs hbits).2.2.2 + 2)) name (lr1T cols nhs hbits)]) ++ [.ret []] := by
  rw [lrLoop1Body_split, ← eq_map_atomsOf (allAtoms_of_isAtom hat)]
  simp [List.append_assoc]

theorem mem_lr1L_pow {cols nhs hbits : ℕ} {s : Stmt} (h : s ∈ (osBatchPow 7).1) : s ∈ lr1L cols nhs hbits := by
  simp [lr1L, lr1A, h]

theorem mem_lr1L_st {cols nhs hbits : ℕ} {s : Stmt} (h : s ∈ (lr1St cols nhs hbits).1) :
    s ∈ lr1L cols nhs hbits := by
  simp [lr1L, lr1A, h]

theorem mem_lr1L_tail {cols nhs hbits : ℕ} {s : Stmt} (h : s ∈ osLoopTailA (lr1St cols nhs hbits).2.2.2) :
    s ∈ lr1L cols nhs hbits := by
  simp [lr1L, h]

/-- **The batches' loop's pointers and guard**, on a valuation with the arguments whose atoms
needing no side condition hold. -/
theorem lr1_vals {cols nhs hbits : ℕ} {rd : Reader} {σ : Val} {j b ip ic irow ihs : ℕ} {mu : E}
    (hp : ∀ i < 7, σ (.n i) = (lr1Args j b ip ic irow ihs mu).getD i 0)
    (hNS : ∀ a, Stmt.atom a ∈ lr1L cols nhs hbits → needsSide a = false → a.Holds rd σ) :
    σ (.n (7 + batchLen)) = ptrAt (ip + j * resBatch) ∧ σ (.n (7 + batchLen + 2)) = ptrAt (ic + 2 * j) ∧
      σ (.n 4) = ptrAt irow ∧ σ (.n 5) = ptrAt ihs ∧ σ (.n 6) = mu ∧
      σ (.n ((lr1St cols nhs hbits).2.2.2 + 2)) = gen ^ (j + 1) + gen ^ b ∧
      (lr1T cols nhs hbits).map σ = lr1Args (j + 1) b ip ic irow ihs mu := by
  have p0 : σ (.n 0) = gen ^ j := hp 0 (by decide)
  have p1 : σ (.n 1) = gen ^ b := hp 1 (by decide)
  have p2 : σ (.n 2) = ptrAt ip := hp 2 (by decide)
  have p3 : σ (.n 3) = ptrAt ic := hp 3 (by decide)
  have p4 : σ (.n 4) = ptrAt irow := hp 4 (by decide)
  have p5 : σ (.n 5) = ptrAt ihs := hp 5 (by decide)
  have p6 : σ (.n 6) = mu := hp 6 (by decide)
  have hpw : AllOk (fun _ _ _ => True) rd σ (osBatchPow 7).1 :=
    allOk_noSide (fun _ h => mem_lr1L_pow h) (fun s hs => by
      have := List.all_eq_true.mp lr1_fixed.1 s hs
      cases s with
      | atom a => exact ⟨a, rfl, by simpa using this⟩
      | _ => simp at this) hNS
  have hpow : σ (.n (osBatchPow 7).2) = σ (.n 0) ^ resBatch := osBatchPow_val 7 hpw
  have eY : σ (.n (7 + batchLen)) = σ (.n 2) * σ (.n (osBatchPow 7).2) :=
    hNS _ (by simp [lr1L, lr1A]) lr1_fixed.2.1
  have eY1 : σ (.n (7 + batchLen + 1)) = σ (.n 3) * σ (.n 0) :=
    hNS _ (by simp [lr1L, lr1A]) lr1_fixed.2.2.1
  have eY2 : σ (.n (7 + batchLen + 2)) = σ (.n (7 + batchLen + 1)) * σ (.n 0) :=
    hNS _ (by simp [lr1L, lr1A]) lr1_fixed.2.2.2
  have hT : AllOk (fun _ _ _ => True) rd σ (osLoopTailA (lr1St cols nhs hbits).2.2.2) :=
    allOk_noSide (fun _ h => mem_lr1L_tail h) (osLoopTailA_noSide _) hNS
  obtain ⟨t2, t4⟩ := osLoopTailA_val hT
  refine ⟨?_, ?_, p4, p5, p6, ?_, ?_⟩
  · rw [eY, hpow, p2, p0, ← pow_mul, ptrAt_mul_gen]
  · rw [eY2, eY1, p3, p0, ptrAt_mul_gen, ptrAt_mul_gen, show ic + j + j = ic + 2 * j by omega]
  · rw [t2, p0, p1, ← pow_succ]
  · show [σ (.n ((lr1St cols nhs hbits).2.2.2 + 4)), σ (.n 1), σ (.n 2), σ (.n 3), σ (.n 4), σ (.n 5),
      σ (.n 6)] = _
    rw [t4, p0, p1, p2, p3, p4, p5, p6, ← pow_succ]
    rfl

/-- **One iteration of the batches' loop completes**, the next one completing when `j + 1 < b`. -/
theorem lr1_step {kd : ℕ} {cols nhs hbits : ℕ} {name : String} {fn : Fn}
    (hfind : coreProgram.find? name = some fn) (hpar : fn.params = osParams 7)
    (hbody : fn.body = lrLoop1Body cols nhs hbits name) (hck : lr1Checks cols nhs hbits name = true)
    {q : ℕ} (hq : q < 2 ^ 30) (ip irow ihs ic : ℕ) (mu : E) (D Pos : ℕ → E) (hsv : List E)
    (hlen : hsv.length = nhs) {j : ℕ} (hj : j < q / resBatch)
    (hnext : j + 1 < q / resBatch → CallCompletes0 kd name (lr1Args (j + 1) (q / resBatch) ip ic irow ihs mu) []
      (LrMem q cols nhs hbits ip irow ihs ic mu D Pos hsv) PostQuiet) :
    CallCompletes0 kd name (lr1Args j (q / resBatch) ip ic irow ihs mu) []
      (LrMem q cols nhs hbits ip irow ihs ic mu D Pos hsv) PostQuiet := by
  simp only [lr1Checks, Bool.and_eq_true, decide_eq_true_eq] at hck
  obtain ⟨⟨⟨⟨⟨⟨hc, hst⟩, hat⟩, hok⟩, hat1⟩, hns⟩, hc1, hn1, hb3, hbn⟩ := hck
  obtain ⟨c', hc⟩ := Option.isSome_iff_exists.mp hc
  set b := q / resBatch with hb
  have hbq : resBatch * b ≤ q := Nat.mul_div_le q resBatch
  have hb30 : b < 2 ^ 30 := lt_of_le_of_lt (Nat.div_le_self _ _) hq
  set args := lr1Args j b ip ic irow ihs mu with hargs
  have hb' := lr1_body (name := name) hat
  have hchk : chk args.length fn.body = some c' := by rw [hbody]; exact hc
  refine callCompletes0_loopFlat hfind (by rw [hbody]; exact hb') (by rw [hpar]; rfl) hok
    (fun rd => fwdVal rd (fun _ => 0) args fn.body) fun rd hl hP => ?_
  set s := fwdVal rd (fun _ => 0) args fn.body with hs
  have hmem : ∀ a, Stmt.atom a ∈ lr1L cols nhs hbits → Stmt.atom a ∈ fn.body := fun a ha => by
    rw [hbody, hb']
    exact List.mem_append_left _ (List.mem_append_left _ (List.mem_map.mpr ⟨a, mem_atomsOf' ha, rfl⟩))
  have hNS : ∀ a, Stmt.atom a ∈ lr1L cols nhs hbits → needsSide a = false → a.Holds rd s :=
    fun a ha hn => fwd_holds_noSide hchk (hmem a ha) hn
  have hp : ∀ i < 7, s (.n i) = args.getD i 0 := fun i hi => fwd_param hchk (by simpa [hargs, lr1Args] using hi)
  obtain ⟨vY, vY2, p4, p5, p6, vg, vt⟩ := lr1_vals hp hNS
  have hbase : ∀ q' ∈ lr1Ps cols nhs, ∃ a, s (.n q'.1) = ptrAt a ∧
      ∀ o < q'.2, ∃ v, LoadHolds rd (ptrAt a) o v := by
    intro q' hq'
    simp only [lr1Ps, List.mem_cons, List.not_mem_nil, or_false] at hq'
    rcases hq' with rfl | rfl | rfl | rfl
    · exact ⟨irow, p4, fun o ho => ⟨_, lrMem_row hP ho⟩⟩
    · exact ⟨ihs, p5, fun o ho => ⟨_, lrMem_high hP (by omega)⟩⟩
    · refine ⟨ip + j * resBatch, vY, fun o ho => ⟨_, lrMem_pos hP ?_⟩⟩
      have : (j + 1) * resBatch ≤ b * resBatch := Nat.mul_le_mul_right _ hj
      simp only at ho
      nlinarith
    · refine ⟨ic + 2 * j, vY2, fun o ho => ⟨_, readsAt_off hP.2.2.2 ?_⟩⟩
      simp only at ho
      simp [lrChainL]; omega
  -- every atom but the stores
  have hP1 : ∀ a, Stmt.atom a ∈ lr1L cols nhs hbits → a ∉ lr1Stores cols nhs hbits → a.Holds rd s := by
    intro a ha hS
    cases hn : needsSide a
    · exact hNS a ha hn
    · have hk := List.all_eq_true.mp hok a (mem_atomsOf' ha)
      cases a with
      | load d p off =>
        refine fwd_holds_load hchk (hmem _ ha) ?_ (loadHolds_of_loadOk hbase hk)
        show Atom.load d p off ∉ storesOf 7 fn.body
        rw [hbody, hst]; exact hS
      | _ => simp [loadOkB, hn] at hk
  -- the chain pair it reads
  have hrd : j ≤ b + q % resBatch := by omega
  obtain ⟨c0, c1⟩ := lrChain_load hP.2.2.2 hrd
  have l3 : LoadHolds rd (s (.n (7 + batchLen + 2))) 0 (s (.n (7 + batchLen + 3))) :=
    hP1 (.load (.n (7 + batchLen + 3)) (.n (7 + batchLen + 2)) 0) (by simp [lr1L, lr1A]) (by simp [lr1Stores])
  have l4 : LoadHolds rd (s (.n (7 + batchLen + 2))) 1 (s (.n (7 + batchLen + 4))) :=
    hP1 (.load (.n (7 + batchLen + 4)) (.n (7 + batchLen + 2)) 1) (by simp [lr1L, lr1A]) (by simp [lr1Stores])
  rw [vY2, loadHolds_ptrAt_add, Nat.add_zero] at l3
  rw [vY2, loadHolds_ptrAt_add] at l4
  have e3 : s (.n (7 + batchLen + 3)) = (lrPair (lrP cols D) (lrH cols nhs hbits hsv) mu Pos (lrCnt b j)).1 :=
    loadHolds_unique l3 c0
  have e4 : s (.n (7 + batchLen + 4)) = (lrPair (lrP cols D) (lrH cols nhs hbits hsv) mu Pos (lrCnt b j)).2 :=
    loadHolds_unique l4 c1
  -- the steps
  have hst1 : AllOk (fun _ _ _ => True) rd s (osResSteps (7 + batchLen) 4 0 5 0 (lrVo cols) cols nhs hbits 6
      (List.range resBatch) (7 + batchLen + 3) (7 + batchLen + 4) (7 + batchLen + 5)).1 := by
    intro st hst'
    have h1 := List.all_eq_true.mp hat1 st hst'
    cases st with
    | atom a =>
      refine hP1 a (mem_lr1L_st hst') ?_
      have := List.all_eq_true.mp hns a (mem_atomsOf' hst')
      simpa using this
    | _ => simp [Stmt.isAtom] at h1
  have hDs : ∀ t < cols, LoadHolds rd (s (.n 4)) (0 + t) (D t) := fun t ht => by
    rw [p4, Nat.zero_add]; exact lrMem_row hP ht
  have hHs : ∀ c < nhs, LoadHolds rd (s (.n 5)) (0 + c) (hsv.getD c 0) := fun c hc => by
    rw [p5, Nat.zero_add]; exact lrMem_high hP (by omega)
  obtain ⟨ps, hF, hv⟩ := osResSteps_val hc1 hn1 hb3 hbn hDs hlen hHs (List.range resBatch) _ _ _ hst1
  obtain ⟨hpl, hF⟩ := forall₂_range_to _ _ hF
  have hps : ps = (List.range resBatch).map fun i => Pos (j * resBatch + i) := by
    refine List.ext_getElem (by simp [hpl]) fun i h1 h2 => ?_
    have hi : i < resBatch := by simpa using h2
    have := hF i hi
    rw [vY] at this
    have hk : j * resBatch + i < q := by
      have : (j + 1) * resBatch ≤ b * resBatch := Nat.mul_le_mul_right _ hj
      nlinarith
    rw [List.getD_eq_getElem _ _ (by omega)] at this
    rw [loadHolds_unique this (lrMem_pos hP hk)]
    simp
  have hcj : lrCnt b j = j * resBatch := by simp only [lrCnt, hj.le, ↓reduceIte]; ring
  have hcj1 : lrCnt b (j + 1) = j * resBatch + resBatch := by
    simp only [lrCnt, show j + 1 ≤ b by omega, ↓reduceIte]; ring
  have hnew : (s (.n (lr1St cols nhs hbits).2.1), s (.n (lr1St cols nhs hbits).2.2.1)) =
      lrPair (lrP cols D) (lrH cols nhs hbits hsv) mu Pos (lrCnt b (j + 1)) := by
    have hv' : (s (.n (lr1St cols nhs hbits).2.1), s (.n (lr1St cols nhs hbits).2.2.1)) = _ := hv
    rw [hv', e3, e4, p6, hps, hcj, hcj1, ← lrPair_add]
    rfl
  obtain ⟨d0, d1⟩ := lrChain_load hP.2.2.2 (i := j + 1) (by omega)
  -- the stores
  have hS1 : LoadHolds rd (s (.n (7 + batchLen + 2))) 2 (s (.n (lr1St cols nhs hbits).2.1)) := by
    have h1 : s (.n (lr1St cols nhs hbits).2.1) = (lrPair (lrP cols D) (lrH cols nhs hbits hsv) mu Pos
        (lrCnt b (j + 1))).1 := congrArg Prod.fst hnew
    rw [vY2, loadHolds_ptrAt_add, h1]
    rw [show 2 * j + 2 = 2 * (j + 1) by ring]; exact d0
  have hS2 : LoadHolds rd (s (.n (7 + batchLen + 2))) 3 (s (.n (lr1St cols nhs hbits).2.2.1)) := by
    have h1 : s (.n (lr1St cols nhs hbits).2.2.1) = (lrPair (lrP cols D) (lrH cols nhs hbits hsv) mu Pos
        (lrCnt b (j + 1))).2 := congrArg Prod.snd hnew
    rw [vY2, loadHolds_ptrAt_add, h1]
    rw [show 2 * j + 3 = 2 * (j + 1) + 1 by ring]; exact d1
  refine ⟨by rw [hpar]; exact fwd_params hchk, fun a ha => ?_, ?_, fun hz => ?_⟩
  · have ha' := mem_of_mem_atomsOf ha
    by_cases hS : a ∈ lr1Stores cols nhs hbits
    · simp only [lr1Stores, List.mem_cons, List.not_mem_nil, or_false] at hS
      rcases hS with rfl | rfl
      · exact hS1
      · exact hS2
    · exact hP1 a ha' hS
  · rw [vg]; exact isInK_add (gen_pow_isInK _) (gen_pow_isInK _)
  · have hne : j + 1 ≠ b := fun h => hz (by rw [vg, h]; exact CharTwo.add_self_eq_zero _)
    obtain ⟨t, hn, hv2, hb2, hq2⟩ := hnext (by omega) rd hl hP
    exact ⟨t, hn, by rw [vt]; exact hv2, hb2, hq2⟩

/-- **The batches' loop completes from iteration `j`**, every `j < b`. -/
theorem lr1_loop {kd : ℕ} {cols nhs hbits : ℕ} {name : String} {fn : Fn}
    (hfind : coreProgram.find? name = some fn) (hpar : fn.params = osParams 7)
    (hbody : fn.body = lrLoop1Body cols nhs hbits name) (hck : lr1Checks cols nhs hbits name = true)
    {q : ℕ} (hq : q < 2 ^ 30) (ip irow ihs ic : ℕ) (mu : E) (D Pos : ℕ → E) (hsv : List E)
    (hlen : hsv.length = nhs) :
    ∀ m j, q / resBatch = j + m + 1 → CallCompletes0 kd name (lr1Args j (q / resBatch) ip ic irow ihs mu) []
      (LrMem q cols nhs hbits ip irow ihs ic mu D Pos hsv) PostQuiet := by
  intro m
  induction m with
  | zero =>
    intro j hj
    exact lr1_step hfind hpar hbody hck hq ip irow ihs ic mu D Pos hsv hlen (by omega) (fun h => absurd h (by omega))
  | succ m IH =>
    intro j hj
    exact lr1_step hfind hpar hbody hck hq ip irow ihs ic mu D Pos hsv hlen (by omega) (fun _ => IH (j + 1) (by omega))

/-- What the batches' loop loads from: the positions, the row, the high part and the chain. -/
def LrRegion (q cols nhs ip irow ihs ic : ℕ) (R : ℕ → Prop) : Prop :=
  (∀ i < q, R (ip + i)) ∧ (∀ i < cols, R (irow + i)) ∧ (∀ i < nhs, R (ihs + i)) ∧
    ∀ i < 2 * (q / resBatch + q % resBatch + 1), R (ic + i)

/-- **Every valid tree of the batches' loop from iteration `j < b` has its shape.** -/
theorem lr1_shape {fs : String → ℕ} {al : String → Bool} {cols nhs hbits : ℕ} {name : String} {fn : Fn}
    (hfind : coreProgram.find? name = some fn) (hpar : fn.params = osParams 7)
    (hbody : fn.body = lrLoop1Body cols nhs hbits name) (hls : coreProgram.loop name = true)
    (hck : lr1Checks cols nhs hbits name = true) {q : ℕ} (hq : q < 2 ^ 30) {ip irow ihs ic : ℕ} {mu : E}
    {R : ℕ → Prop} (hR : LrRegion q cols nhs ip irow ihs ic R) :
    ∀ m j, q / resBatch = j + m + 1 → ∀ rd t, t.name = name →
      t.Valid coreProgram rd (lr1Args j (q / resBatch) ip ic irow ihs mu) [] → t.BufsOk coreProgram →
      ShapeR fs al (lpB fs name (q / resBatch) j) _root_.id R t := by
  simp only [lr1Checks, Bool.and_eq_true, decide_eq_true_eq] at hck
  obtain ⟨⟨⟨⟨⟨⟨-, -⟩, hat⟩, hok⟩, -⟩, -⟩, -⟩ := hck
  have hb' := lr1_body (name := name) hat
  set b := q / resBatch with hb
  have hbq : resBatch * b ≤ q := Nat.mul_div_le q resBatch
  have hb30 : b < 2 ^ 30 := lt_of_le_of_lt (Nat.div_le_self _ _) hq
  intro m
  induction m with
  | zero =>
    intro j hj rd t hn hv hbt
    have h := shapeR_loopFlat (fs := fs) (al := al) (args := lr1Args j b ip ic irow ihs mu) (R := R)
      (Bt := lpB fs name b (j + 1)) hfind (by rw [hbody]; exact hb') hls hok ?_ rd t hn hv hbt
    · have e : fs name + lpB fs name b (j + 1) = lpB fs name b j := by
        simp only [lpB]; rw [show b - j = (b - (j + 1)) + 1 by omega]; ring
      rwa [e] at h
    · intro rd' σ hp hA
      have hp' : ∀ i < 7, σ (.n i) = (lr1Args j b ip ic irow ihs mu).getD i 0 :=
        fun i hi => param_of_map (by rw [← hpar]; exact hp) hi
      obtain ⟨vY, vY2, p4, p5, -, vg, -⟩ := lr1_vals hp' fun a ha _ => hA a (mem_atomsOf' ha)
      refine ⟨?_, fun _ => by simp only [lpB]; rw [show b - (j + 1) = 0 by omega]; ring, fun hz => ?_⟩
      · intro q' hq'
        simp only [lr1Ps, List.mem_cons, List.not_mem_nil, or_false] at hq'
        rcases hq' with rfl | rfl | rfl | rfl
        · exact ⟨irow, p4, hR.2.1⟩
        · exact ⟨ihs, p5, hR.2.2.1⟩
        · refine ⟨ip + j * resBatch, vY, fun o ho => ?_⟩
          rw [Nat.add_assoc]; refine hR.1 _ ?_
          simp only at ho
          have : (j + 1) * resBatch ≤ b * resBatch := Nat.mul_le_mul_right _ (by omega)
          nlinarith
        · refine ⟨ic + 2 * j, vY2, fun o ho => ?_⟩
          rw [Nat.add_assoc]; refine hR.2.2.2 _ ?_
          simp only at ho
          omega
      · exact absurd (by rw [vg, show j + 1 = b by omega]; exact CharTwo.add_self_eq_zero _) hz
  | succ m IH =>
    intro j hj rd t hn hv hbt
    have h := shapeR_loopFlat (fs := fs) (al := al) (args := lr1Args j b ip ic irow ihs mu) (R := R)
      (Bt := lpB fs name b (j + 1)) hfind (by rw [hbody]; exact hb') hls hok ?_ rd t hn hv hbt
    · have e : fs name + lpB fs name b (j + 1) = lpB fs name b j := by
        simp only [lpB]; rw [show b - j = (b - (j + 1)) + 1 by omega]; ring
      rwa [e] at h
    · intro rd' σ hp hA
      have hp' : ∀ i < 7, σ (.n i) = (lr1Args j b ip ic irow ihs mu).getD i 0 :=
        fun i hi => param_of_map (by rw [← hpar]; exact hp) hi
      obtain ⟨vY, vY2, p4, p5, -, vg, vt⟩ := lr1_vals hp' fun a ha _ => hA a (mem_atomsOf' ha)
      refine ⟨?_, fun hz => absurd hz ?_, fun _ t' hn' hv' hb'' => ?_⟩
      · intro q' hq'
        simp only [lr1Ps, List.mem_cons, List.not_mem_nil, or_false] at hq'
        rcases hq' with rfl | rfl | rfl | rfl
        · exact ⟨irow, p4, hR.2.1⟩
        · exact ⟨ihs, p5, hR.2.2.1⟩
        · refine ⟨ip + j * resBatch, vY, fun o ho => ?_⟩
          rw [Nat.add_assoc]; refine hR.1 _ ?_
          simp only at ho
          have : (j + 1) * resBatch ≤ b * resBatch := Nat.mul_le_mul_right _ (by omega)
          nlinarith
        · refine ⟨ic + 2 * j, vY2, fun o ho => ?_⟩
          rw [Nat.add_assoc]; refine hR.2.2.2 _ ?_
          simp only at ho
          omega
      · rw [vg]; exact (gen_add_ne' (by omega) (by omega)).not.mpr (by omega)
      · rw [vt] at hv'
        exact IH (j + 1) (by omega) rd' t' hn' hv' hb''

end
end LeanVM.Guest.B1.VsC
