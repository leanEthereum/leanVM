/-
  LeanVM.Guest.B1.VerifySub.CFront

  `verify_sub`'s first blocks, complete: the seed, the announced sizes, the rate and the memory's
  log, `kappa_base`, `block_kappa`, the push side's total and the root.
-/

module

public import LeanVM.Guest.B1.VerifySub.CBlocks

/-!
# The first blocks, complete (G:2091-2135)

Each lemma completes one block of `vsBody` on its range of values, from the values it reads
(`Fixes`) to the values later blocks read.
-/

namespace LeanVM.Guest.B1.VerifySub

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.Blake2sHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Guest.B1.Sig

@[expose] public section

variable {C : CallRel} {rd : Reader} {D : VsData} {P : VsPtrs}

/-! ## The seed -/

theorem compress_seed (seed pi : Digest) :
    CompressCells ![(digestScalars seed).1, (digestScalars seed).2, (digestScalars pi).1,
      (digestScalars pi).2] ivCells.1 ivCells.2
      (digestScalars (blake2sBytes (digestBytes seed ++ digestBytes pi))).1
      (digestScalars (blake2sBytes (digestBytes seed ++ digestBytes pi))).2
      (metadataCell 64 true) := by
  refine (blake2s_default_iff fun i => ?_).mpr ?_
  · fin_cases i
    · exact (isCanonical128_digestScalars seed).1
    · exact (isCanonical128_digestScalars seed).2
    · exact (isCanonical128_digestScalars pi).1
    · exact (isCanonical128_digestScalars pi).2
  · simp only [blockBytes, digestBytes_eq, List.append_assoc]
    rfl

/-- The values the seed block leaves. -/
def seedOut (D : VsData) (P : VsPtrs) : List (ℕ × E) :=
  [(7, P.pool), (8, P.cplen), (12, (digestScalars D.cv0).1), (13, (digestScalars D.cv0).2),
    (14, P.stream)]

/-- **The seed** (G:2092-2094). -/
theorem c_seed (σ : Val) (h2 : σ (.n 2) = (digestScalars D.seed).1)
    (h3 : σ (.n 3) = (digestScalars D.seed).2) (h0 : σ (.n 0) = (digestScalars D.pi).1)
    (h1 : σ (.n 1) = (digestScalars D.pi).2) :
    Completes C rd 7 15 bSeed σ (fun σ' => Fixes σ' (seedOut D P)) := by
  refine completes_upds [(7, P.pool), (8, P.cplen), (9, word 13503953895743350343 11912009169889063794 0),
    (10, word 11170449402626986623 6620516960021240235 0), (11, word 64 4294967295 0),
    (12, (digestScalars D.cv0).1), (13, (digestScalars D.cv0).2), (14, P.stream)]
    (by simp) (fun next kret hn => ?_) ?_
  · simp only [bSeed, Stmt.HoldsList, Stmt.Holds, Atom.Holds, upds_n, upds_nil]
    simp only [Nat.reduceEqDiff, ↓reduceIte, true_and, word_iv0, word_iv1, word_md64,
      h0, h1, h2, h3]
    exact ⟨compress_seed D.seed D.pi, hn⟩
  · intro p hp
    simp only [seedOut, List.mem_cons, List.mem_nil_iff, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl <;> simp [upds_n]

/-! ## The announced sizes -/

theorem ann_length (h : D.rows.length = 6) : D.ann.length = 8 := by
  simp [VsData.ann, announce, h]

theorem ann_take_succ {k : ℕ} (h : D.rows.length = 6) (hk : k < 8) :
    D.ann.take (k + 1) = D.ann.take k ++ [D.ann.getD k 0] := by
  rw [List.take_add_one, List.getElem?_eq_getElem (by rw [ann_length h]; exact hk),
    List.getD_eq_getElem _ _ (by rw [ann_length h]; exact hk)]
  rfl

theorem rdS_lt : ∀ k < 8, rdS k + 1 < rdB k := by decide

theorem rdS_succ (k : ℕ) : rdS (k + 1) = rdB k + 13 := rfl

/-- **One announced word** (G:2103-2107): read at offset `k`, absorbed. -/
theorem c_read {k : ℕ} (hk : k < 8) (hl : D.rows.length = 6) (σ : Val)
    (h14 : σ (.n 14) = P.stream) (hx : LoadHolds rd P.stream k (D.ann.getD k 0))
    (hs : (σ (.n (rdS k)), σ (.n (rdS k + 1))) = digestScalars (obsAll D.cv0 (D.ann.take k))) :
    Completes C rd (rdB k) (rdB k + 15) (bRead k) σ (fun σ' =>
      σ' (.n (rdB k)) = D.ann.getD k 0 ∧ (σ' (.n (rdS (k + 1))), σ' (.n (rdS (k + 1) + 1))) =
        digestScalars (obsAll D.cv0 (D.ann.take (k + 1)))) := by
  have h1 := rdS_lt k hk
  have h2 : 14 < rdB k := (show ∀ k < 8, 14 < rdB k by decide) k hk
  refine completes_fsNextT ⟨_, by omega, rfl⟩ ⟨_, h1, rfl⟩ ⟨14, h2, rfl⟩ hs (by rw [h14]; exact hx)
    fun σ' _ hb ho => ⟨hb, ?_⟩
  rw [rdS_succ, ann_take_succ hl hk, obsAll_append_one]
  exact ho

/-- Row count `t` read and stored at `table_rows`. -/
def bReadRow (t : ℕ) : List Stmt := bRead (t + 1) ++ [.atom (.load (.n (rdB (t + 1))) (.n 30) t)]

theorem bReads_eq : bReads = bRead 0 ++ [.atom (.hint (.alloc (.n 30) 6))] ++
    ((List.range 6).map bReadRow).flatten ++ bRead 7 := rfl

/-- The values the announced sizes leave. -/
def readsOut (D : VsData) (P : VsPtrs) : List (ℕ × E) :=
  [(15, eOfNat D.logMem), (30, P.rows), (121, eOfNat D.rate),
    (134, (digestScalars (obsAll D.cv0 D.ann)).1), (135, (digestScalars (obsAll D.cv0 D.ann)).2)]

theorem ann_getD_zero : D.ann.getD 0 0 = eOfNat D.logMem := rfl

theorem ann_getD_seven (hl : D.rows.length = 6) : D.ann.getD 7 0 = eOfNat D.rate := by
  obtain ⟨a, b, c, d, e, f, h⟩ : ∃ a b c d e f, D.rows = [a, b, c, d, e, f] := by
    match D.rows, hl with
    | [a, b, c, d, e, f], _ => exact ⟨a, b, c, d, e, f, rfl⟩
  simp [VsData.ann, announce, h]

theorem ann_getD_row (hl : D.rows.length = 6) {t : ℕ} (ht : t < 6) :
    D.ann.getD (t + 1) 0 = eOfNat (D.rows.getD t 0) := by
  simp only [VsData.ann, announce, List.cons_append, List.getD_cons_succ]
  rw [List.getD_eq_getElem _ _ (by simp [hl]; omega), List.getElem_append_left (by simp [hl]; omega),
    List.getElem_map, List.getD_eq_getElem _ _ (by omega)]

theorem numBelow_reads :
    NumBelow 30 (Stmt.valsList (bRead 0)) ∧ NumBelow 31 (Stmt.valsList (bRead 0 ++
      [.atom (.hint (.alloc (.n 30) 6))])) ∧
    NumBelow 121 (Stmt.valsList (bRead 0 ++ [.atom (.hint (.alloc (.n 30) 6))] ++
      ((List.range 6).map bReadRow).flatten)) ∧
    ∀ t < 6, NumBelow (rdB (t + 2)) (Stmt.valsList (bReadRow t)) :=
  ⟨numBelow_of_B (by decide +kernel), numBelow_of_B (by decide +kernel),
    numBelow_of_B (by decide +kernel), fun t ht => numBelow_of_B (by revert t ht; decide +kernel)⟩

/-- **The eight announced words** (G:2103-2107), the row counts stored at `table_rows`. -/
theorem c_reads (hl : D.rows.length = 6) (σ : Val) (hσ : Fixes σ (seedOut D P))
    (hst : ∀ k < 8, LoadHolds rd P.stream k (D.ann.getD k 0))
    (hrows : ∀ t < 6, LoadHolds rd P.rows t (eOfNat (D.rows.getD t 0))) :
    Completes C rd 15 136 bReads σ (fun σ' => Fixes σ' (readsOut D P)) := by
  have h14 : σ (.n 14) = P.stream := hσ.get (by simp [seedOut])
  have hs0 : (σ (.n (rdS 0)), σ (.n (rdS 0 + 1))) = digestScalars (obsAll D.cv0 (D.ann.take 0)) := by
    show (σ (.n 12), σ (.n 13)) = _
    rw [hσ.get (k := 12) (e := (digestScalars D.cv0).1) (by simp [seedOut]),
      hσ.get (k := 13) (e := (digestScalars D.cv0).2) (by simp [seedOut])]
    rfl
  obtain ⟨nb0, nb1, nb2, nbf⟩ := numBelow_reads
  rw [bReads_eq]
  -- the first word, then `table_rows`
  have c0 := (c_read (C := C) (P := P) (rd := rd) (by omega) hl σ h14 (hst 0 (by omega)) hs0).keep
    (l := [(14, P.stream)]) (by intro p hp; simp at hp; subst hp; exact h14) (by simp [rdB])
  refine Completes.append (m := 121) (P := fun σ' ↦ (σ' (.n 14) = P.stream ∧ σ' (.n 30) = P.rows ∧
      (σ' (.n (rdS (6 + 1))), σ' (.n (rdS (6 + 1) + 1))) =
        digestScalars (obsAll D.cv0 (D.ann.take (6 + 1)))) ∧ Fixes σ' [(15, eOfNat D.logMem)])
    (by omega) (by omega) nb2 ?_ fun σ1 e1 h1 => ?_
  · refine Completes.append (m := 31) (P := fun σ' => σ' (.n 15) = eOfNat D.logMem ∧
        σ' (.n 14) = P.stream ∧ σ' (.n 30) = P.rows ∧ (σ' (.n 28), σ' (.n 29)) =
          digestScalars (obsAll D.cv0 (D.ann.take 1))) (by omega) (by omega) nb1 ?_
      fun σ1 e1 h1 => ?_
    · refine Completes.append (m := 30) (by omega) (by omega) nb0 c0 fun σ1 e1 h1 => ?_
      exact completes_hint (k := 30) P.rows (Post := fun σ' => σ' (.n 15) = eOfNat D.logMem ∧
        σ' (.n 14) = P.stream ∧ σ' (.n 30) = P.rows ∧ (σ' (.n 28), σ' (.n 29)) =
          digestScalars (obsAll D.cv0 (D.ann.take 1))) (by
        obtain ⟨⟨hb, hs⟩, hf⟩ := h1
        vs_ev
        exact ⟨hb, hf.get (by simp), by first | rfl | trivial, hs⟩)
    · -- the six row counts
      obtain ⟨h15, h14', h30, hs⟩ := h1
      have := Completes.flatten (C := C) (rd := rd) (blk := bReadRow)
        (st := fun t ↦ rdB (t + 1)) (Inv := fun t σ' ↦ σ' (.n 14) = P.stream ∧
          σ' (.n 30) = P.rows ∧ (σ' (.n (rdS (t + 1))), σ' (.n (rdS (t + 1) + 1))) =
            digestScalars (obsAll D.cv0 (D.ann.take (t + 1))))
        6 (fun t _ => by simp [rdB]) (fun t ht => nbf t ht) (fun t ht σ' ⟨i14, i30, is⟩ => ?_)
        σ1 ⟨h14', h30, hs⟩
      · exact (this.keep (l := [(15, eOfNat D.logMem)]) (by intro p hp; simp at hp; subst hp; exact h15)
          (by simp [rdB])).post fun _ _ h => h
      · have c := (c_read (C := C) (P := P) (rd := rd) (k := t + 1) (by omega) hl σ' i14
          (hst (t + 1) (by omega)) is).keep (l := [(14, P.stream), (30, P.rows)])
          (by intro p hp; simp at hp; rcases hp with rfl | rfl <;> assumption)
          (by intro p hp; simp at hp; rcases hp with rfl | rfl <;> simp [rdB] <;> omega)
        refine (c.append_atom fun σ'' ⟨⟨hb, hs'⟩, hf⟩ => ⟨?_, hf.get (e := P.stream) (by simp), hf.get (e := P.rows) (by simp), hs'⟩)
        show LoadHolds rd (σ'' (.n 30)) t (σ'' (.n (rdB (t + 1))))
        rw [hf.get (k := 30) (e := P.rows) (by simp), hb, ann_getD_row hl ht]
        exact hrows t ht
  · -- the rate
    obtain ⟨⟨h14', h30, hs⟩, h15⟩ := h1
    have c := (c_read (C := C) (P := P) (rd := rd) (k := 7) (by omega) hl σ1 h14' (hst 7 (by omega)) hs).keep
      (l := [(15, eOfNat D.logMem), (30, P.rows)])
      (by intro p hp; simp at hp; rcases hp with rfl | rfl
          · exact h15.get (by simp)
          · exact h30) (by intro p hp; simp at hp; rcases hp with rfl | rfl <;> simp [rdB])
    refine c.post fun σ' _ ⟨⟨hb, hs'⟩, hf⟩ => ?_
    rw [ann_take_succ hl (by omega), ann_getD_seven hl] at hs'
    rw [ann_getD_seven hl] at hb
    have htake : D.ann.take 7 ++ [eOfNat D.rate] = D.ann := by
      rw [← ann_getD_seven hl, ← ann_take_succ hl (by omega), List.take_of_length_le (by rw [ann_length hl])]
    rw [htake] at hs'
    intro p hp
    simp only [readsOut, List.mem_cons, List.mem_nil_iff, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl
    · exact hf.get (by simp)
    · exact hf.get (by simp)
    · exact hb
    · exact congrArg Prod.fst hs'
    · exact congrArg Prod.snd hs'

/-! ## The rate and the memory's log -/

/-- The values the sizes leave. -/
def sizesOut (D : VsData) (P : VsPtrs) : List (ℕ × E) :=
  [(138, gen ^ (D.rate - 1)), (143, P.dims), (144, gen ^ D.logMem)]

/-- **The rate, `dims_g[0]` and the memory's log** (G:2108-2115). -/
theorem c_sizes (hlow : LowDef 6 rd) {lp sq : E} (hm1 : 16 ≤ D.logMem) (hm2 : D.logMem ≤ 32) (hr1 : 1 ≤ D.rate)
    (hr2 : D.rate ≤ 4) {bytecode : List K} (hC : VsCallsOk C bytecode D P lp sq)
    (hd0 : LoadHolds rd P.dims 0 (gen ^ D.logMem)) (σ : Val)
    (hσ : Fixes σ [(5, sq), (15, eOfNat D.logMem), (121, eOfNat D.rate)]) :
    Completes C rd 136 155 bSizes σ
      (fun σ' => Fixes σ' (sizesOut D P)) := by
  have h5 : σ (.n 5) = sq := hσ.get (by simp)
  have h15 : σ (.n 15) = eOfNat D.logMem := hσ.get (by simp)
  have h121 : σ (.n 121) = eOfNat D.rate := hσ.get (by simp)
  set r := D.rate
  set m := D.logMem
  refine completes_upds [(136, gen ^ r), (137, word 2 0 0), (138, gen ^ (r - 1)), (139, word 8 0 0),
    (140, (rcLow rd (r - 1) 4).1), (141, (rcLow rd (r - 1) 4).2.1),
    (142, (rcLow rd (r - 1) 4).2.2), (143, P.dims), (144, gen ^ m),
    (145, word 4294967296 0 0), (146, (rcLow rd m 33).1), (147, (rcLow rd m 33).2.1),
    (148, (rcLow rd m 33).2.2), (149, word 4294967296 0 0), (150, word 65536 0 0),
    (151, gen ^ (m - 16)), (152, (rcLow rd (m - 16) 33).1),
    (153, (rcLow rd (m - 16) 33).2.1), (154, (rcLow rd (m - 16) 33).2.2)]
    (by simp) (fun next kret hn => ?_) ?_
  · simp only [bSizes, Stmt.HoldsList, Stmt.Holds, List.map_cons, List.map_nil]
    refine ⟨?_, ?_, ?_, ?_, ?_, trivial, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, trivial, hn⟩
    · vs_ev
      rw [h121, h5]
      exact hC.gpwRate
    · simp [Atom.Holds, upds_n]
    · simp only [Atom.Holds]
      vs_ev
      rw [word_gen]
      rw [← pow_succ, show r - 1 + 1 = r by omega]
    · simp [Atom.Holds, upds_n]
    · exact rc_holds_low hlow (K := 4) (e := r - 1) (by omega) (by omega) (by simp [upds_n])
        (by simp [upds_n]) (by simp [upds_n]) (by simp [upds_n])
        (by vs_ev
            exact word_two_pow (a := 3) (by decide))
    · vs_ev
      rw [h15, h5]
      exact hC.gpwMem
    · simp [Atom.Holds, upds_n]
    · exact rc_holds_low hlow (K := 33) (e := m) (by omega) (by omega) (by simp [upds_n])
        (by simp [upds_n]) (by simp [upds_n]) (by simp [upds_n])
        (by vs_ev
            exact word_two_pow (a := 32) (by decide))
    · simp [Atom.Holds, upds_n]
    · simp [Atom.Holds, upds_n]
    · simp only [Atom.Holds]
      vs_ev
      have w16 : word 65536 0 0 = gen ^ 16 := word_two_pow (a := 16) (by decide)
      rw [w16, ← pow_add, show m - 16 + 16 = m by omega]
    · exact rc_holds_low hlow (K := 33) (e := m - 16) (by omega) (by omega) (by simp [upds_n])
        (by simp [upds_n]) (by simp [upds_n]) (by simp [upds_n])
        (by vs_ev
            exact word_two_pow (a := 32) (by decide))
    · simp only [Atom.Holds]
      vs_ev
      exact hd0
  · intro p hp
    simp only [sizesOut, List.mem_cons, List.mem_nil_iff, or_false] at hp
    rcases hp with rfl | rfl | rfl <;> simp [upds_n, r, m]

/-! ## `kappa_base` and `block_kappa` -/

/-- The honest values of `kappa_base`'s block. -/
def kbVals (P : VsPtrs) (hs : List ℕ) : ℕ → E
  | 0 => P.kbase
  | 1 => word 1 0 0
  | t + 2 => gen ^ hs.getD t 0

/-- **`kappa_base`** (G:2117-2120): `[1, g^log_mem, dims_g[1..7]]`. -/
theorem c_kbase (σ : Val) (hσ : Fixes σ [(143, P.dims), (144, gen ^ D.logMem)])
    (hd : ∀ t < 6, LoadHolds rd P.dims (1 + t) (gen ^ D.hs.getD t 0))
    (hk0 : LoadHolds rd P.kbase 0 1) (hk1 : LoadHolds rd P.kbase 1 (gen ^ D.logMem))
    (hk : ∀ t < 6, LoadHolds rd P.kbase (2 + t) (gen ^ D.hs.getD t 0)) :
    Completes C rd 155 163 bKBase σ (fun σ' => Fixes σ' [(155, P.kbase)]) := by
  refine completes_setv (lo := 155) (n := 8) (kbVals P D.hs) (fun next kret hn => ?_) ?_
  · rw [bKBase, holdsList_append, holdsList_range_flatten 6 _ (fun _ => rfl)]
    simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds]
    have e143 : setv σ 155 8 (kbVals P D.hs) (.n 143) = P.dims := by
      rw [set_n_lt (by omega)]; exact hσ.get (by simp)
    have e144 : setv σ 155 8 (kbVals P D.hs) (.n 144) = gen ^ D.logMem := by
      rw [set_n_lt (by omega)]; exact hσ.get (by simp)
    have e155 : setv σ 155 8 (kbVals P D.hs) (.n 155) = P.kbase := by
      rw [set_n_in (by omega) (by omega)]; rfl
    have e156 : setv σ 155 8 (kbVals P D.hs) (.n 156) = word 1 0 0 := by
      rw [set_n_in (by omega) (by omega)]; rfl
    have et : ∀ t < 6, setv σ 155 8 (kbVals P D.hs) (.n (157 + t)) = gen ^ D.hs.getD t 0 :=
      fun t ht => by rw [set_n_in (by omega) (by omega), show 157 + t - 155 = t + 2 by omega]; rfl
    rw [e143, e144, e155, e156, word_one]
    refine ⟨trivial, rfl, hk0, hk1, fun t ht => ?_, hn⟩
    rw [et t ht]
    exact ⟨hd t ht, hk t ht, trivial⟩
  · intro p hp
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hp
    subst hp
    show setv σ 155 8 (kbVals P D.hs) (.n 155) = P.kbase
    rw [set_n_in (by omega) (by omega), Nat.sub_self]
    simp only [kbVals]

/-- The base word block `b` of `block_kappa` reads. -/
def bkSrc (D : VsData) (b : ℕ) : E := (kappaBase (gen ^ D.logMem) (D.hs.map (gen ^ ·))).getD (blockKappaSrc.getD b 0) 0

/-- The honest values of block `b` of `block_kappa`. -/
def bkUpds (D : VsData) (b : ℕ) : List (ℕ × E) :=
  if b = 2 ∨ b = 39 then [(bkV b, bkSrc D b), (bkV b + 1, word 262144 0 0), (bkV b + 2, bkSrc D b * word 262144 0 0)]
  else [(bkV b, bkSrc D b)]

theorem bkV_succ : ∀ b < 102, bkV (b + 1) = bkV b + if b = 2 ∨ b = 39 then 3 else 1 := by decide

theorem bkV_ge : ∀ b < 102, 164 ≤ bkV b := by decide

theorem numBelow_bk : ∀ b < 102, NumBelow (bkV (b + 1)) (Stmt.valsList (bkBlk b)) :=
  fun b hb => numBelow_of_B (by revert b hb; decide +kernel)

/-- **Block `b` of `block_kappa`** (G:2121-2123). -/
theorem c_bkBlk {b : ℕ} (hb : b < 102) (σ : Val) (h155 : σ (.n 155) = P.kbase)
    (h163 : σ (.n 163) = P.bk) (hsrc : LoadHolds rd P.kbase (blockKappaSrc.getD b 0) (bkSrc D b))
    (hbk : LoadHolds rd P.bk b ((blockKappas (gen ^ D.logMem) (D.hs.map (gen ^ ·))).getD b 0)) :
    Completes C rd (bkV b) (bkV (b + 1)) (bkBlk b) σ
      (fun σ' => σ' (.n 155) = P.kbase ∧ σ' (.n 163) = P.bk) := by
  have hge := bkV_ge b hb
  have hs := bkV_succ b hb
  have hval : (blockKappas (gen ^ D.logMem) (D.hs.map (gen ^ ·))).getD b 0 =
      bkSrc D b * gen ^ blockKappaAdj.getD b 0 := by
    simp only [blockKappas, bkSrc]
    rw [List.getD_eq_getElem _ _ (by simp; omega), List.getElem_map, List.getElem_range]
  rw [blockKappaAdj_eq b hb] at hval
  refine completes_upds (bkUpds D b) ?_ (fun next kret hn => ?_) ?_
  · rw [hs]
    unfold bkUpds
    by_cases hadj : b = 2 ∨ b = 39
    · simp only [hadj, ↓reduceIte, List.mem_cons, List.mem_nil_iff, or_false]
      rintro p (rfl | rfl | rfl) <;> simp only <;> omega
    · simp only [hadj, ↓reduceIte, List.mem_cons, List.mem_nil_iff, or_false]
      rintro p rfl; simp only; omega
  · unfold bkBlk bkUpds
    by_cases hadj : b = 2 ∨ b = 39
    · have h0 : blockKappaSrc.getD b 0 = 0 := by rcases hadj with rfl | rfl <;> rfl
      simp only [hadj, ↓reduceIte, Stmt.HoldsList, Stmt.Holds, Atom.Holds, upds_n, upds_nil]
      simp only [show (155 : ℕ) ≠ bkV b by omega, show (155 : ℕ) ≠ bkV b + 1 by omega,
        show (155 : ℕ) ≠ bkV b + 2 by omega, show (163 : ℕ) ≠ bkV b by omega,
        show (163 : ℕ) ≠ bkV b + 1 by omega, show (163 : ℕ) ≠ bkV b + 2 by omega,
        show bkV b + 1 ≠ bkV b by omega, show bkV b + 2 ≠ bkV b by omega,
        show bkV b + 2 ≠ bkV b + 1 by omega, ↓reduceIte, h155, h163]
      refine ⟨by rw [← h0]; exact hsrc, by first | rfl | trivial, by first | rfl | trivial, ?_, hn⟩
      have w18 : word 262144 0 0 = gen ^ 18 := word_two_pow (a := 18) (by decide)
      simp only [hadj, ↓reduceIte] at hval
      rw [w18, ← hval]
      exact hbk
    · simp only [hadj, ↓reduceIte, Stmt.HoldsList, Stmt.Holds, Atom.Holds, upds_n, upds_nil]
      simp only [show (155 : ℕ) ≠ bkV b by omega, show (163 : ℕ) ≠ bkV b by omega, ↓reduceIte,
        h155, h163]
      refine ⟨hsrc, ?_, hn⟩
      rw [hval] at hbk
      simpa [hadj] using hbk
  · unfold bkUpds
    split <;> simp only [upds_n, upds_nil, show (155 : ℕ) ≠ bkV b by omega,
      show (155 : ℕ) ≠ bkV b + 1 by omega, show (155 : ℕ) ≠ bkV b + 2 by omega,
      show (163 : ℕ) ≠ bkV b by omega, show (163 : ℕ) ≠ bkV b + 1 by omega,
      show (163 : ℕ) ≠ bkV b + 2 by omega, ↓reduceIte, h155, h163, and_self]

/-- **`block_kappa`** (G:2121-2123). -/
theorem c_blockKappa (σ : Val) (h155 : σ (.n 155) = P.kbase)
    (hsrc : ∀ b < 102, LoadHolds rd P.kbase (blockKappaSrc.getD b 0) (bkSrc D b))
    (hbk : ∀ b < 102, LoadHolds rd P.bk b
      ((blockKappas (gen ^ D.logMem) (D.hs.map (gen ^ ·))).getD b 0)) :
    Completes C rd 163 270 bBlockKappa σ
      (fun σ' => Fixes σ' [(155, P.kbase), (163, P.bk)]) := by
  rw [bBlockKappa, ← List.singleton_append]
  refine Completes.append (m := 164) (by omega) (by omega) (numBelow_of_B (by decide +kernel))
    (completes_hint (k := 163) P.bk (Post := fun σ' => σ' (.n 155) = P.kbase ∧ σ' (.n 163) = P.bk)
      (by vs_ev; exact ⟨h155, by first | rfl | trivial⟩)) fun σ1 _ h1 => ?_
  have := Completes.flatten (C := C) (rd := rd) (blk := bkBlk) (st := bkV)
    (Inv := fun _ σ' => σ' (.n 155) = P.kbase ∧ σ' (.n 163) = P.bk) 102
    (fun b hb => by rw [bkV_succ b hb]; omega) numBelow_bk
    (fun b hb σ' ⟨i1, i2⟩ => c_bkBlk hb σ' i1 i2 (hsrc b hb) (hbk b hb)) σ1 h1
  refine this.post fun σ' _ ⟨i1, i2⟩ p hp => ?_
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hp
  rcases hp with rfl | rfl
  · exact i1
  · exact i2

/-! ## The push side's total -/

/-- Push block `b`'s kappa and the running sum of `2^κ` through block `b`. -/
def pkap (D : VsData) (b : ℕ) : ℕ := (pushKappas D.logMem D.hs).getD b 0

def pS (D : VsData) (b : ℕ) : ℕ := ((List.range (b + 1)).map fun i ↦ 2 ^ pkap D i).sum

theorem pushK_succ (b : ℕ) : pushK (b + 1) = 273 + 4 * b := by simp [pushK]

theorem pushP_eq (b : ℕ) : pushP b = 272 + 4 * b := by
  cases b with
  | zero => rfl
  | succ b => simp [pushP, pushK]; omega

theorem pS_succ (b : ℕ) : pS D (b + 1) = pS D b + 2 ^ pkap D (b + 1) := by
  simp only [pS, List.range_succ (n := b + 1), List.map_append, List.sum_append, List.map_cons,
    List.map_nil, List.sum_cons, List.sum_nil, add_zero]

theorem pS_total (hl : D.rows.length = 6) : pS D 36 = D.pushTotal := by
  have hlen : (pushKappas D.logMem D.hs).length = 37 := pushKappas_length _ _ (by simp [VsData.hs, hl])
  rw [VsData.pushTotal, ← map_getD_range _ (2 ^ ·), hlen]
  rfl

theorem numBelow_push : ∀ b < 36, NumBelow (273 + 4 * (b + 1)) (Stmt.valsList (pushBlk b)) :=
  fun b hb => numBelow_of_B (by revert b hb; decide +kernel)

/-- The pointers into `g_squares` the push blocks load through, up to block `b`. -/
def pushPtrs (D : VsData) (sq : E) (b : ℕ) : List (ℕ × E) :=
  (List.range (b + 1)).map fun j => (pushK j + 1, sq * gen ^ pkap D j)

theorem pushK_lt : ∀ j, pushK j + 1 < 273 + 4 * j := by intro j; unfold pushK; split <;> omega

theorem c_pushBlk0 {lp sq : E} (ht : ExpTables rd lp sq) {b : ℕ} (hb : b < 36)
    (hk : pkap D (b + 1) < 34) (hbk : LoadHolds rd P.bk (b + 1) (gen ^ pkap D (b + 1))) (σ : Val)
    (h5 : σ (.n 5) = sq) (h163 : σ (.n 163) = P.bk) (hP : σ (.n (pushP b)) = gen ^ pS D b) :
    Completes C rd (273 + 4 * b) (273 + 4 * (b + 1)) (pushBlk b) σ
      (fun σ' => σ' (.n 5) = sq ∧ σ' (.n 163) = P.bk ∧ σ' (.n (pushP (b + 1))) = gen ^ pS D (b + 1) ∧
        σ' (.n (274 + 4 * b)) = sq * gen ^ pkap D (b + 1)) := by
  rw [pushP_eq] at hP
  have n1 : 274 + 4 * b ≠ 273 + 4 * b := by omega
  have n2 : 275 + 4 * b ≠ 273 + 4 * b := by omega
  have n3 : 275 + 4 * b ≠ 274 + 4 * b := by omega
  have n4 : 276 + 4 * b ≠ 273 + 4 * b := by omega
  have n5 : 276 + 4 * b ≠ 274 + 4 * b := by omega
  have n6 : 276 + 4 * b ≠ 275 + 4 * b := by omega
  have m1 : (163 : ℕ) ≠ 273 + 4 * b := by omega
  have m2 : (163 : ℕ) ≠ 274 + 4 * b := by omega
  have m3 : (163 : ℕ) ≠ 275 + 4 * b := by omega
  have m4 : (163 : ℕ) ≠ 276 + 4 * b := by omega
  have k1 : (5 : ℕ) ≠ 273 + 4 * b := by omega
  have k2 : (5 : ℕ) ≠ 274 + 4 * b := by omega
  have k3 : (5 : ℕ) ≠ 275 + 4 * b := by omega
  have k4 : (5 : ℕ) ≠ 276 + 4 * b := by omega
  have p1 : 272 + 4 * b ≠ 273 + 4 * b := by omega
  have p2 : 272 + 4 * b ≠ 274 + 4 * b := by omega
  have p3 : 272 + 4 * b ≠ 275 + 4 * b := by omega
  have p4 : 272 + 4 * b ≠ 276 + 4 * b := by omega
  have e1 : 273 + 4 * b + 1 = 274 + 4 * b := by omega
  have e2 : 273 + 4 * b + 2 = 275 + 4 * b := by omega
  have e3 : 272 + 4 * (b + 1) = 276 + 4 * b := by omega
  refine completes_upds [(273 + 4 * b, gen ^ pkap D (b + 1)),
    (274 + 4 * b, sq * gen ^ pkap D (b + 1)), (275 + 4 * b, gen ^ 2 ^ pkap D (b + 1)),
    (276 + 4 * b, gen ^ pS D (b + 1))] (by simp; omega) (fun next kret hn => ?_) ?_
  · simp only [pushBlk, pushK_succ, pushP_eq, Stmt.HoldsList, Stmt.Holds, Atom.Holds, upds_n,
      upds_nil, e1, e2, e3]
    simp only [n1, n2, n3, n4, n5, n6, m1, m2, m3, m4, k1, k2, k3, k4, p1, p2, p3, p4, ↓reduceIte,
      h5, h163, hP]
    refine ⟨hbk, by first | rfl | trivial, ?_, ?_, hn⟩
    · rw [loadHolds_mul_gen_pow, Nat.add_zero]; exact (ht _ hk).2
    · rw [pS_succ, pow_add]
  · simp only [pushP_eq, upds_n, upds_nil, e3]
    simp only [n1, n4, n5, n6, m1, m2, m3, m4, k1, k2, k3, k4, ↓reduceIte, h5, h163]
    exact ⟨trivial, trivial, trivial, trivial⟩

/-- **Push block `b + 1`** (G:2124-2127): the running total times `g_squares[block_kappa[b+1]]`. -/
theorem c_pushBlk {lp sq : E} (ht : ExpTables rd lp sq) {b : ℕ} (hb : b < 36)
    (hk : pkap D (b + 1) < 34) (hbk : LoadHolds rd P.bk (b + 1) (gen ^ pkap D (b + 1))) (σ : Val)
    (h5 : σ (.n 5) = sq) (h163 : σ (.n 163) = P.bk) (hP : σ (.n (pushP b)) = gen ^ pS D b)
    (hF : Fixes σ (pushPtrs D sq b)) :
    Completes C rd (273 + 4 * b) (273 + 4 * (b + 1)) (pushBlk b) σ
      (fun σ' => σ' (.n 5) = sq ∧ σ' (.n 163) = P.bk ∧ σ' (.n (pushP (b + 1))) = gen ^ pS D (b + 1) ∧
        Fixes σ' (pushPtrs D sq (b + 1))) := by
  refine (Completes.keep (c_pushBlk0 ht hb hk hbk σ h5 h163 hP) hF (fun p hp => ?_)).post
    fun σ' _ ⟨⟨a1, a2, a3, a4⟩, hf⟩ => ⟨a1, a2, a3, fun p hp => ?_⟩
  · simp only [pushPtrs, List.mem_map, List.mem_range] at hp
    obtain ⟨j, hj, rfl⟩ := hp
    have := pushK_lt j; simp only; omega
  · simp only [pushPtrs, List.range_succ (n := b + 1), List.map_append, List.mem_append,
      List.map_cons, List.map_nil, List.mem_cons, List.mem_nil_iff, or_false] at hp
    rcases hp with hp | rfl
    · exact hf p (by simpa [pushPtrs] using hp)
    · rw [pushK_succ]; simpa [show 273 + 4 * b + 1 = 274 + 4 * b by omega] using a4

/-- The values the push side leaves. -/
def pushOut (D : VsData) (P : VsPtrs) (sq : E) : List (ℕ × E) :=
  [(417, gen ^ log2Ceil D.pushTotal), (418, P.zeta)] ++ pushPtrs D sq 36

/-- **The push side's total and `g_bus_mu`** (G:2124-2128). -/
theorem c_push {lp sq : E}
    (ht : ExpTables rd lp sq) (hl : D.rows.length = 6) (hm : D.logMem ≤ 32)
    (hh : ∀ h ∈ D.hs, h < 29) (hdep : log2Ceil D.pushTotal < 33)
    (hbk : ∀ b < 37, LoadHolds rd P.bk b (gen ^ pkap D b)) {bytecode : List K}
    (hC : VsCallsOk C bytecode D P lp sq) (σ : Val)
    (hσ : Fixes σ [(4, lp), (5, sq), (163, P.bk)]) :
    Completes C rd 270 419 bPush σ (fun σ' => Fixes σ' (pushOut D P sq)) := by
  have h4 : σ (.n 4) = lp := hσ.get (by simp)
  have h5 : σ (.n 5) = sq := hσ.get (by simp)
  have h163 : σ (.n 163) = P.bk := hσ.get (by simp)
  have hhl : D.hs.length = 6 := by simp [VsData.hs, hl]
  have hk : ∀ b < 37, pkap D b < 34 := fun b hb => by
    have := pushKappas_le D.logMem D.hs hhl hm hh b hb; unfold pkap; omega
  have hN : D.pushTotal < 2 ^ 34 :=
    lt_of_le_of_lt (le_two_pow_log2Ceil _) (Nat.pow_lt_pow_right (by decide) (by omega))
  rw [bPush]
  refine Completes.append (m := 417) (P := fun σ' => (σ' (.n 5) = sq ∧ σ' (.n 163) = P.bk ∧
      σ' (.n (pushP 36)) = gen ^ pS D 36 ∧ Fixes σ' (pushPtrs D sq 36)) ∧ Fixes σ' [(4, lp)])
    (by omega) (by omega)
    (numBelow_of_B (by decide +kernel)) ?_ fun σ2 e2 h2 => ?_
  · refine Completes.append (m := 273) (P := fun σ' => σ' (.n 4) = lp ∧ σ' (.n 5) = sq ∧
        σ' (.n 163) = P.bk ∧ σ' (.n 272) = gen ^ pS D 0 ∧ Fixes σ' (pushPtrs D sq 0)) (by omega)
      (by omega)
      (numBelow_of_B (by decide +kernel)) ?_ fun σ1 e1 h1 => ?_
    · refine completes_upds [(270, gen ^ pkap D 0), (271, sq * gen ^ pkap D 0),
        (272, gen ^ 2 ^ pkap D 0)] (by simp) (fun next kret hn => ?_) ?_
      · simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds]
        vs_ev
        rw [h5, h163]
        refine ⟨hbk 0 (by omega), rfl, ?_, hn⟩
        rw [loadHolds_mul_gen_pow, Nat.add_zero]; exact (ht _ (hk 0 (by omega))).2
      · vs_ev
        rw [h4, h5, h163]
        refine ⟨rfl, rfl, rfl, by simp [pS], fun p hp => ?_⟩
        simp [pushPtrs] at hp
        subst hp
        simp only [pushK, ↓reduceIte, Nat.reduceAdd]
        vs_ev
    · obtain ⟨i4, i5, i163, i272, iF⟩ := h1
      have := Completes.flatten (C := C) (rd := rd) (blk := pushBlk)
        (st := fun b ↦ 273 + 4 * b) (Inv := fun b σ' ↦ σ' (.n 5) = sq ∧ σ' (.n 163) = P.bk ∧
          σ' (.n (pushP b)) = gen ^ pS D b ∧ Fixes σ' (pushPtrs D sq b)) 36 (fun b _ => by omega)
        numBelow_push
        (fun b hb σ' ⟨j5, j163, jP, jF⟩ => c_pushBlk ht hb (hk (b + 1) (by omega))
          (hbk (b + 1) (by omega)) σ' j5 j163 jP jF) σ1 ⟨i5, i163, i272, iF⟩
      exact this.keep (l := [(4, lp)]) (by intro p hp; simp at hp; subst hp; exact i4) (by simp)
  · obtain ⟨⟨j5, -, jP, jF⟩, j4⟩ := h2
    have j4' : σ2 (.n 4) = lp := j4.get (by simp)
    rw [pushP_eq, pS_total hl] at jP
    refine completes_upds [(417, gen ^ log2Ceil D.pushTotal), (418, P.zeta)] (by simp)
      (fun next kret hn => ?_) ?_
    · simp only [Stmt.HoldsList, Stmt.Holds, List.map_cons, List.map_nil]
      vs_ev
      rw [jP, j4', j5]
      exact ⟨hC.log2Push, trivial, hn⟩
    · intro p hp
      rcases List.mem_append.mp hp with hp | hp
      · simp only [List.mem_cons, List.mem_nil_iff, or_false] at hp
        rcases hp with rfl | rfl <;> simp [upds_n]
      · rw [upds_of_not_mem]
        · exact jF p hp
        · intro q hq
          simp only [List.mem_cons, List.mem_nil_iff, or_false] at hq
          simp only [pushPtrs, List.mem_map, List.mem_range] at hp
          obtain ⟨j, hj, rfl⟩ := hp
          have := pushK_lt j
          rcases hq with rfl | rfl <;> simp <;> omega

/-! ## The root -/

/-- The values the root leaves. -/
def rootOut (D : VsData) : List (ℕ × E) :=
  [(419, D.x0), (434, D.x1), (447, (digestScalars D.cv10).1), (448, (digestScalars D.cv10).2)]

/-- **The stack's root** (G:2131-2135): its two words read at offsets `8`, `9`, absorbed, both
canonical. -/
theorem c_root (σ : Val) (h14 : σ (.n 14) = P.stream)
    (hs : (σ (.n 134), σ (.n 135)) = digestScalars (obsAll D.cv0 D.ann))
    (h8 : LoadHolds rd P.stream 8 D.x0) (h9 : LoadHolds rd P.stream 9 D.x1) {bytecode : List K}
    {lp sq : E} (hC : VsCallsOk C bytecode D P lp sq) :
    Completes C rd 419 451 bRoot σ (fun σ' => Fixes σ' (rootOut D)) := by
  rw [bRoot]
  refine Completes.append (m := 449) (P := fun σ' => Fixes σ' (rootOut D)) (by omega) (by omega)
    (numBelow_of_B (by decide +kernel)) ?_ fun σ2 _ h2 => ?_
  · refine Completes.append (m := 434) (P := fun σ' => σ' (.n 419) = D.x0 ∧ σ' (.n 14) = P.stream ∧
        (σ' (.n 432), σ' (.n 433)) = digestScalars (obsCv (obsAll D.cv0 D.ann) D.x0)) (by omega)
      (by omega) (numBelow_of_B (by decide +kernel)) ?_ fun σ1 e1 h1 => ?_
    · exact completes_fsNextT (b := 419) ⟨134, by omega, rfl⟩ ⟨135, by omega, rfl⟩
        ⟨14, by omega, rfl⟩ hs (by rw [h14]; exact h8) fun σ' e hb ho =>
          ⟨hb, by rw [e.apply (by omega)]; exact h14, ho⟩
    · obtain ⟨h419, h14', h432⟩ := h1
      exact completes_fsNextT (b := 434) ⟨432, by omega, rfl⟩ ⟨433, by omega, rfl⟩
        ⟨14, by omega, rfl⟩ h432 (by rw [h14']; exact h9) fun σ' e hb ho => by
          intro p hp
          simp only [rootOut, List.mem_cons, List.mem_nil_iff, or_false] at hp
          rcases hp with rfl | rfl | rfl | rfl
          · rw [e.apply (by omega)]; exact h419
          · exact hb
          · exact congrArg Prod.fst ho
          · exact congrArg Prod.snd ho
  · refine completes_upds [(449, 0), (450, 0)] (by simp) (fun next kret hn => ?_) ?_
    · simp only [Stmt.HoldsList, Stmt.Holds, List.map_cons, List.map_nil]
      vs_ev
      rw [h2.get (k := 419) (e := D.x0) (by simp [rootOut]),
        h2.get (k := 434) (e := D.x1) (by simp [rootOut])]
      exact ⟨hC.canon0, hC.canon1, hn⟩
    · intro p hp
      rw [upds_of_not_mem]
      · exact h2 p hp
      · intro q hq
        simp only [rootOut, List.mem_cons, List.mem_nil_iff, or_false] at hp
        simp only [List.mem_cons, List.mem_nil_iff, or_false] at hq
        rcases hp with rfl | rfl | rfl | rfl <;> rcases hq with rfl | rfl <;> simp

end
end LeanVM.Guest.B1.VerifySub
