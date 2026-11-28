/-
  LeanVM.Guest.B1.VsC.VsNatFs

  The guest's sponge before the link is the native verifier's: the out-of-domain grind's permutation, and
  the Fiat-Shamir facts `VsFsChecks1` at the honest context.
-/

module

public import LeanVM.Guest.B1.VsC.VsNatLink
public import LeanVM.Guest.B1.VsC.VsOrcPh46
public import LeanVM.Guest.B1.VerifySub.Front
public import LeanVM.Guest.B1.VerifySub.PhLinkRun
public import LeanVM.Guest.B1.VsC.SqueezeFwd

/-!
# The front's sponge, natively

**The bridge** (`vsVal_oodS`): on `verify_sub`'s forward valuation at a child's arguments, with the stream's
pointer `w 55` reading the stream's first eleven words, the out-of-domain grind's `KECCAK` (statement `441`,
`vsC3p`) writes the cells of `natOodS seed c`, the native verifier's permutation of the nonce (word `10`). Its
inputs are the seed's capacity (`seed_cap`, statement `23`), the first eight words absorbed by two permutations
(statements `53`, `99`), and words `8`, `9` waiting: `natF2`'s.

**`VsCtx.fsChecks1`**: `VsFsChecks1 x` from the context's placement, the stream's buffer, and the honest
choices `RetFs` (`squeeze_point_from`'s and `opening_message`'s returns, natively: `spfN`, `omN`) and `BwFs`
(the point's buffer `.n 22`, the opening's `.n 23`). The two grinds pass by the accepted child's run
(`natFront`'s `powOk`, `natChildLink`'s link grind at `2` bits).
-/

namespace LeanVM.Guest.B1.VsC

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Memory LeanVM.Guest.B1
open LeanVM.Guest.Complete LeanVM.Guest.B1.Fwd LeanVM.Node LeanVM.Protocol LeanVM.Protocol.Verifier
open LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Link

@[expose] public section

/-! ## The bridge -/

set_option maxRecDepth 200000 in
/-- Statements `432 ..< 442`: `vsC3p`. -/
theorem vsC3p_eq : (vsC.drop 4).take 10 = vsC3p.map Stmt.atom := stmtsEqb_sound (by decide +kernel)

theorem nmem_of_not_contains {S : List Atom} {a : Atom} (h : (!S.contains a) = true) : a ∉ S :=
  fun hS => absurd h (by simpa using hS)

/-- An entry of a list, by its index. -/
theorem mem_of_getElem?' {l : List Atom} {a : Atom} (i : ℕ) (h : l[i]? = some a) : a ∈ l := by
  obtain ⟨hi, e⟩ := List.getElem?_eq_some_iff.mp h
  exact e ▸ List.getElem_mem hi

/-- A fresh load of window `6`, off the eight-word buffer, is no store. -/
theorem vsW6_freshAt {d pv off : ℕ} (hq : (d, pv, off) ∈ vsW6ld) (hne : pv ≠ 112) :
    Atom.load (.n d) (.n pv) off ∉ storesOf 6 vsAf := fun h' =>
  absurd (List.all_eq_true.mp vsW6_fresh (d, pv, off) (List.mem_filter.mpr ⟨hq, by simpa using hne⟩))
    (by simpa using h')

section
variable {rd0 : Reader} {w : ℕ → E} {args : List E}

set_option maxRecDepth 100000 in
/-- **The front's sponge on the guest's values**: the out-of-domain grind's permutation is the nonce's on the
seed's capacity with the stream's first ten words absorbed. -/
theorem vsFront_cells (ha : args.length = 6) :
    cells13 (([.n 499, .n 500, .n 501, .n 502, .n 503, .n 504, .n 505, .n 506, .n 507, .n 508, .n 509, .n 510,
      .n 511] : List V).map (vsVal rd0 w args)) = cellsOfState
      (((((⟨[vsVal rd0 w args (.n 37), vsVal rd0 w args (.n 38), vsVal rd0 w args (.n 39),
          vsVal rd0 w args (.n 40), vsVal rd0 w args (.n 41)], []⟩ : Fs).absorbAll
        [vsVal rd0 w args (.n 57), vsVal rd0 w args (.n 60), vsVal rd0 w args (.n 63), vsVal rd0 w args (.n 66),
          vsVal rd0 w args (.n 82), vsVal rd0 w args (.n 85), vsVal rd0 w args (.n 88),
          vsVal rd0 w args (.n 91)] dsObserve).absorb (vsVal rd0 w args (.n 134)) dsObserve).absorb
        (vsVal rd0 w args (.n 137)) dsObserve).nonceState (vsVal rd0 w args (.n 494))) false := by
  set σ := vsVal rd0 w args with hσ
  have g2 := vsA_run_good (rd0 := rd0) (w := w) ha vsW2_eq vsW2_ne
  have g6 := vsW6_good (rd0 := rd0) (w := w) ha
  have g3 := vsC_run_good (rd0 := rd0) (w := w) ha vsC3p_eq
  -- the first eight words' permutation
  have k1 : (Atom.keccak [.n 58, .n 59, .n 61, .n 62, .n 64, .n 65, .n 67, .n 68, .n 37, .n 38, .n 39, .n 40, .n 41]
      [.n 69, .n 70, .n 71, .n 72, .n 73, .n 74, .n 75, .n 76, .n 77, .n 78, .n 79, .n 80, .n 81]
      false false).Holds rd0 σ := holds_of_good' (g2 _ (mem_of_getElem?' (l := vsW2) 16 rfl)) rfl
  have c58 : σ (.n 58) = σ (.n 57) := g2 (.copy (.n 58) (.n 57)) (mem_of_getElem?' (l := vsW2) 2 rfl)
  have c61 : σ (.n 61) = σ (.n 60) := g2 (.copy (.n 61) (.n 60)) (mem_of_getElem?' (l := vsW2) 5 rfl)
  have c64 : σ (.n 64) = σ (.n 63) := g2 (.copy (.n 64) (.n 63)) (mem_of_getElem?' (l := vsW2) 9 rfl)
  have c67 : σ (.n 67) = σ (.n 66) := g2 (.copy (.n 67) (.n 66)) (mem_of_getElem?' (l := vsW2) 13 rfl)
  have t59 : σ (.n 59) = word 0 1 := g2 (.const (.n 59) (word 0 1)) (mem_of_getElem?' (l := vsW2) 3 rfl)
  have t62 : σ (.n 62) = word 0 1 := g2 (.const (.n 62) (word 0 1)) (mem_of_getElem?' (l := vsW2) 6 rfl)
  have t65 : σ (.n 65) = word 0 1 := g2 (.const (.n 65) (word 0 1)) (mem_of_getElem?' (l := vsW2) 10 rfl)
  have t68 : σ (.n 68) = word 0 1 := g2 (.const (.n 68) (word 0 1)) (mem_of_getElem?' (l := vsW2) 14 rfl)
  -- the next four words' permutation
  have k2 : (Atom.keccak [.n 83, .n 84, .n 86, .n 87, .n 89, .n 90, .n 92, .n 93, .n 77, .n 78, .n 79, .n 80, .n 81]
      [.n 121, .n 122, .n 123, .n 124, .n 125, .n 126, .n 127, .n 128, .n 129, .n 130, .n 131, .n 132, .n 133]
      false false).Holds rd0 σ := holds_of_good' (g6 _ (mem_of_getElem?' (l := vsW6) 24 rfl)) rfl
  have c83 : σ (.n 83) = σ (.n 82) := g2 (.copy (.n 83) (.n 82)) (mem_of_getElem?' (l := vsW2) 18 rfl)
  have c86 : σ (.n 86) = σ (.n 85) := g2 (.copy (.n 86) (.n 85)) (mem_of_getElem?' (l := vsW2) 22 rfl)
  have c89 : σ (.n 89) = σ (.n 88) := g2 (.copy (.n 89) (.n 88)) (mem_of_getElem?' (l := vsW2) 26 rfl)
  have c92 : σ (.n 92) = σ (.n 91) := g2 (.copy (.n 92) (.n 91)) (mem_of_getElem?' (l := vsW2) 30 rfl)
  have t84 : σ (.n 84) = word 0 1 := g2 (.const (.n 84) (word 0 1)) (mem_of_getElem?' (l := vsW2) 19 rfl)
  have t87 : σ (.n 87) = word 0 1 := g2 (.const (.n 87) (word 0 1)) (mem_of_getElem?' (l := vsW2) 23 rfl)
  have t90 : σ (.n 90) = word 0 1 := g2 (.const (.n 90) (word 0 1)) (mem_of_getElem?' (l := vsW2) 27 rfl)
  have t93 : σ (.n 93) = word 0 1 := g2 (.const (.n 93) (word 0 1)) (mem_of_getElem?' (l := vsW2) 31 rfl)
  -- the nonce's permutation
  have k3 : (Atom.keccak [.n 135, .n 136, .n 138, .n 139, .n 495, .n 496, .n 497, .n 498, .n 129, .n 130, .n 131,
      .n 132, .n 133] [.n 499, .n 500, .n 501, .n 502, .n 503, .n 504, .n 505, .n 506, .n 507, .n 508, .n 509,
      .n 510, .n 511] false false).Holds rd0 σ := holds_of_good' (g3 _ (mem_of_getElem?' (l := vsC3p) 9 rfl)) rfl
  have c135 : σ (.n 135) = σ (.n 134) := g6 (.copy (.n 135) (.n 134)) (mem_of_getElem?' (l := vsW6) 26 rfl)
  have c138 : σ (.n 138) = σ (.n 137) := g6 (.copy (.n 138) (.n 137)) (mem_of_getElem?' (l := vsW6) 29 rfl)
  have t136 : σ (.n 136) = word 0 1 := g6 (.const (.n 136) (word 0 1)) (mem_of_getElem?' (l := vsW6) 27 rfl)
  have t139 : σ (.n 139) = word 0 1 := g6 (.const (.n 139) (word 0 1)) (mem_of_getElem?' (l := vsW6) 30 rfl)
  have c495 : σ (.n 495) = σ (.n 494) := g3 (.copy (.n 495) (.n 494)) (mem_of_getElem?' (l := vsC3p) 5 rfl)
  have t496 : σ (.n 496) = word 0 4 := g3 (.const (.n 496) (word 0 4)) (mem_of_getElem?' (l := vsC3p) 6 rfl)
  have t497 : σ (.n 497) = 0 := (g3 (.const (.n 497) (word 0 0)) (mem_of_getElem?' (l := vsC3p) 7 rfl)).trans word_zero
  have t498 : σ (.n 498) = 0 := (g3 (.const (.n 498) (word 0 0)) (mem_of_getElem?' (l := vsC3p) 8 rfl)).trans word_zero
  clear_value σ
  have cap1 := VerifySub.fs_perm_cap (s := ⟨[σ (.n 37), σ (.n 38), σ (.n 39), σ (.n 40), σ (.n 41)],
      [(σ (.n 57), dsObserve), (σ (.n 60), dsObserve), (σ (.n 63), dsObserve), (σ (.n 66), dsObserve)]⟩) k1
    (by simp) (by simp only [List.map_cons, List.map_nil, c58, c61, c64, c67, t59, t62, t65, t68]; rfl)
  have cap2 := VerifySub.fs_perm_cap (s := ⟨[σ (.n 77), σ (.n 78), σ (.n 79), σ (.n 80), σ (.n 81)],
      [(σ (.n 82), dsObserve), (σ (.n 85), dsObserve), (σ (.n 88), dsObserve), (σ (.n 91), dsObserve)]⟩) k2
    (by simp) (by simp only [List.map_cons, List.map_nil, c83, c86, c89, c92, t84, t87, t90, t93]; rfl)
  have hK := keccakA_fs (s := ⟨[σ (.n 129), σ (.n 130), σ (.n 131), σ (.n 132), σ (.n 133)],
      [(σ (.n 134), dsObserve), (σ (.n 137), dsObserve), (σ (.n 494), dsPowNonce)]⟩) k3 (by simp)
    (by simp only [List.map_cons, List.map_nil, c135, c138, t136, t139, c495, t496, t497, t498]; rfl)
  rw [hK]
  refine congrArg (fun S => cellsOfState S false) ?_
  simp only [Fs.nonceState, Fs.absorbAll, List.foldl_cons, List.foldl_nil, Fs.absorb, List.length_nil,
    List.length_cons, List.nil_append, List.cons_append, rateScalars, Nat.reduceAdd, Nat.reduceEqDiff,
    ↓reduceIte]
  rw [← cap1, ← cap2]

end

/-- The padded stream's words are the stream's. -/
theorem padStream_getDF {s : List E} {i : ℕ} (h : i < s.length) : (padStream s).getD i 0 = s.getD i 0 := by
  simp [padStream, List.getD_eq_getElem?_getD, List.getElem?_append_left h]

theorem getElem_getD {l : List E} {i : ℕ} (h : i < l.length) : l[i] = l.getD i 0 :=
  (List.getD_eq_getElem _ _ h).symm

/-- The stream's first eight words, listed. -/
theorem take8_eq {xs : List E} (h : 8 ≤ xs.length) : xs.take 8 = [xs.getD 0 0, xs.getD 1 0, xs.getD 2 0,
    xs.getD 3 0, xs.getD 4 0, xs.getD 5 0, xs.getD 6 0, xs.getD 7 0] := by
  rcases xs with _ | ⟨x0, _ | ⟨x1, _ | ⟨x2, _ | ⟨x3, _ | ⟨x4, _ | ⟨x5, _ | ⟨x6, _ | ⟨x7, xs⟩⟩⟩⟩⟩⟩⟩⟩ <;> simp_all

section
variable {rd0 : Reader} {w : ℕ → E} {args : List E} {seed : Digest} {c : Child} {gsq out : E}

/-- **The bridge**: at a child's arguments, with the stream's pointer reading its first eleven words, the
out-of-domain grind's `KECCAK` writes the cells of the native verifier's nonce permutation `natOodS`. -/
theorem vsVal_oodS (hargs : args = vsArgs seed c gsq out) {s : ℕ} {ws : List E} (hw55 : w 55 = ptrAt s)
    (h0 : ReadsAt rd0 (ptrAt s) ws) (hl : 11 ≤ c.proof.stream.length)
    (hws : ∀ i < 11, ws.getD i 0 = c.proof.stream.getD i 0) (hwl : 11 ≤ ws.length) :
    cells13 (([.n 499, .n 500, .n 501, .n 502, .n 503, .n 504, .n 505, .n 506, .n 507, .n 508, .n 509, .n 510,
      .n 511] : List V).map (vsVal rd0 w args)) = cellsOfState (natOodS seed c) false := by
  have ha : args.length = 6 := by rw [hargs]; rfl
  rw [vsFront_cells ha]
  -- the seed's capacity
  have g0 : ∀ a ∈ vsW0, Good rd0 (storesOf 6 vsAf) w (vsVal rd0 w args) a := fun a h => vsW0_good ha h
  have k0 : (Atom.keccak [.n 2, .n 3, .n 0, .n 1, .n 25, .n 26, .n 27, .n 28, .n 25, .n 25, .n 26, .n 27, .n 28]
      [.n 29, .n 30, .n 31, .n 32, .n 33, .n 34, .n 35, .n 36, .n 37, .n 38, .n 39, .n 40, .n 41]
      false false).Holds rd0 (vsVal rd0 w args) := holds_of_good' (g0 _ (mem_of_getElem?' (l := vsW0) 23 rfl)) rfl
  have z25 : vsVal rd0 w args (.n 25) = 0 :=
    (g0 (.const (.n 25) (word 0 0)) (mem_of_getElem?' (l := vsW0) 19 rfl)).trans word_zero
  have z26 : vsVal rd0 w args (.n 26) = 0 :=
    (g0 (.const (.n 26) (word 0 0)) (mem_of_getElem?' (l := vsW0) 20 rfl)).trans word_zero
  have z27 : vsVal rd0 w args (.n 27) = 0 :=
    (g0 (.const (.n 27) (word 0 0)) (mem_of_getElem?' (l := vsW0) 21 rfl)).trans word_zero
  have z28 : vsVal rd0 w args (.n 28) = 0 :=
    (g0 (.const (.n 28) (word 0 0)) (mem_of_getElem?' (l := vsW0) 22 rfl)).trans word_zero
  have hseed := VerifySub.seed_cap k0 z25 z26 z27 z28
  have p0 : vsVal rd0 w args (.n 0) = (digestHalves (statementDigest seed c.statement)).1 := by
    rw [vsVal_param ha (i := 0) (by norm_num), hargs]; rfl
  have p1 : vsVal rd0 w args (.n 1) = (digestHalves (statementDigest seed c.statement)).2 := by
    rw [vsVal_param ha (i := 1) (by norm_num), hargs]; rfl
  have p2 : vsVal rd0 w args (.n 2) = (digestHalves seed).1 := by
    rw [vsVal_param ha (i := 2) (by norm_num), hargs]; rfl
  have p3 : vsVal rd0 w args (.n 3) = (digestHalves seed).2 := by
    rw [vsVal_param ha (i := 3) (by norm_num), hargs]; rfl
  rw [p0, p1, p2, p3, Prod.mk.eta, Prod.mk.eta, digestOfScalars_digestScalars, digestOfScalars_digestScalars]
    at hseed
  -- the stream's words
  have wv : ∀ q ∈ vsW2ld, vsVal rd0 w args (.n q.1) = c.proof.stream.getD q.2 0 := by
    intro q hq
    have hq2 : q.2 < 11 := by
      have := List.all_eq_true.mp vsW2_offs.1 q hq; simp only [decide_eq_true_eq] at this; omega
    rw [vsW2_val ha hw55 h0 q hq (by omega), getElem_getD, hws _ hq2]
  have w57 : vsVal rd0 w args (.n 57) = c.proof.stream.getD 0 0 := wv (57, 0) (by simp [vsW2ld])
  have w60 : vsVal rd0 w args (.n 60) = c.proof.stream.getD 1 0 := wv (60, 1) (by simp [vsW2ld])
  have w63 : vsVal rd0 w args (.n 63) = c.proof.stream.getD 2 0 := wv (63, 2) (by simp [vsW2ld])
  have w66 : vsVal rd0 w args (.n 66) = c.proof.stream.getD 3 0 := wv (66, 3) (by simp [vsW2ld])
  have w82 : vsVal rd0 w args (.n 82) = c.proof.stream.getD 4 0 := wv (82, 4) (by simp [vsW2ld])
  have w85 : vsVal rd0 w args (.n 85) = c.proof.stream.getD 5 0 := wv (85, 5) (by simp [vsW2ld])
  have w88 : vsVal rd0 w args (.n 88) = c.proof.stream.getD 6 0 := wv (88, 6) (by simp [vsW2ld])
  have w91 : vsVal rd0 w args (.n 91) = c.proof.stream.getD 7 0 := wv (91, 7) (by simp [vsW2ld])
  have g6 := vsW6_good (rd0 := rd0) (w := w) ha
  have p55 : vsVal rd0 w args (.n 55) = ptrAt s := by rw [vsVal_55 ha, hw55]
  have v134 : vsVal rd0 w args (.n 134) = c.proof.stream.getD 8 0 := by
    rw [good_loadAt (vsW6_freshAt (d := 134) (pv := 55) (off := 8) (by simp [vsW6ld]) (by decide)) (g6 _ (mem_of_getElem?' (l := vsW6) 25 rfl)) p55 (by omega) h0,
      getElem_getD, hws 8 (by norm_num)]
  have v137 : vsVal rd0 w args (.n 137) = c.proof.stream.getD 9 0 := by
    rw [good_loadAt (vsW6_freshAt (d := 137) (pv := 55) (off := 9) (by simp [vsW6ld]) (by decide)) (g6 _ (mem_of_getElem?' (l := vsW6) 28 rfl)) p55 (by omega) h0,
      getElem_getD, hws 9 (by norm_num)]
  have g3 := vsC_run_good (rd0 := rd0) (w := w) ha vsC3p_eq
  have v494 : vsVal rd0 w args (.n 494) = c.proof.stream.getD 10 0 := by
    rw [good_loadAt (fun hS => absurd vsC3_fresh (by simpa using hS)) (g3 _ (mem_of_getElem?' (l := vsC3p) 4 rfl)) p55 (by omega) h0,
      getElem_getD, hws 10 (by norm_num)]
  rw [w57, w60, w63, w66, w82, w85, w88, w91, v134, v137, v494, hseed, ← take8_eq (by omega)]
  rfl

end

/-! ## The native squeezes -/

/-- The out-of-domain point's squeezes and the sponge after them, natively. -/
def natSpf (seed : Digest) (c : Child) (μ : ℕ) : List E × Fs :=
  (⟨capOf (natOodS seed c), []⟩ : Fs).squeezeN (μ - 1)

theorem squeezeN_pendF : ∀ (n : ℕ) (s : Fs), s.pend = [] → (s.squeezeN n).2.pend = []
  | 0, _, h => h
  | n + 1, _, _ => squeezeN_pendF n _ rfl

theorem squeezeN_cap_length : ∀ (n : ℕ) (s : Fs), s.cap.length = 5 → (s.squeezeN n).2.cap.length = 5
  | 0, _, h => h
  | n + 1, _, _ => squeezeN_cap_length n _ rfl

theorem natOodZ_eq (seed : Digest) (c : Child) (μ : ℕ) :
    natOodZ seed c μ = challengeOf (natOodS seed c) :: (natSpf seed c μ).1 := rfl

theorem natF3_eq (seed : Digest) (c : Child) (μ : ℕ) :
    natF3 seed c μ = (⟨(natSpf seed c μ).2.cap, []⟩ : Fs).absorb (c.proof.stream.getD 11 0) dsObserve := by
  have h := squeezeN_pendF (μ - 1) (⟨capOf (natOodS seed c), []⟩ : Fs) rfl
  unfold natF3
  congr 1
  rw [natSpf]
  rcases e : (⟨capOf (natOodS seed c), []⟩ : Fs).squeezeN (μ - 1) with ⟨l, ⟨cp, pd⟩⟩
  rw [e] at h
  simp only at h
  subst h
  rfl

theorem list5_getD {l : List E} (h : l.length = 5) :
    [l.getD 0 0, l.getD 1 0, l.getD 2 0, l.getD 3 0, l.getD 4 0] = l := by
  rcases l with _ | ⟨a0, _ | ⟨a1, _ | ⟨a2, _ | ⟨a3, _ | ⟨a4, _ | ⟨a5, l⟩⟩⟩⟩⟩⟩ <;> simp_all

theorem list8_getD {l : List E} (h : l.length = 8) :
    [l.getD 0 0, l.getD 1 0, l.getD 2 0, l.getD 3 0, l.getD 4 0, l.getD 5 0, l.getD 6 0, l.getD 7 0] = l := by
  rcases l with _ | ⟨a0, _ | ⟨a1, _ | ⟨a2, _ | ⟨a3, _ | ⟨a4, _ | ⟨a5, _ | ⟨a6, _ | ⟨a7, _ | ⟨a8, l⟩⟩⟩⟩⟩⟩⟩⟩⟩ <;>
    simp_all

/-! ## The honest choices the Fiat-Shamir facts rest on -/

namespace VsCtx

variable (x : VsCtx)

/-- `squeeze_point_from`'s returns, natively: the capacity after the out-of-domain point's squeezes. -/
noncomputable def spfN : List E := (natSpf x.seed x.c x.lay.stackLog).2.cap

/-- `opening_message__L1_L1`'s returns, natively: the value (the stream's word `11`) absorbed, the link
grind's nonce (word `12`) permuted. -/
noncomputable def omN : List E :=
  omRets (x.spfN.getD 0 0) (x.spfN.getD 1 0) (x.spfN.getD 2 0) (x.spfN.getD 3 0) (x.spfN.getD 4 0)
    (ptrAt (x.base 18 + 11)) [(padStream x.c.proof.stream).getD 11 0] ((padStream x.c.proof.stream).getD 12 0)

/-- **The honest return rule at the out-of-domain point and the opening message.** -/
structure RetFs : Prop where
  r566 : ∀ j < 5, ∀ σ, x.ret (566 + j) σ = x.spfN.getD j 0
  r573 : ∀ j < 8, ∀ σ, x.ret (573 + j) σ = x.omN.getD j 0

/-- **The honest words of the point's buffer `.n 22` and the opening's `.n 23`.** -/
structure BwFs : Prop where
  b16 : ∀ k < (natOodZ x.seed x.c x.lay.stackLog).length,
    (x.bw.getD 16 [])[k]? = (natOodZ x.seed x.c x.lay.stackLog)[k]?
  b17 : x.bw.getD 17 [] = [(padStream x.c.proof.stream).getD 11 0]

/-- The context's facts below `Hon` the memory needs: the placement, the buffers' sizes, a causal rule. -/
structure HonB : Prop where
  ok : x.Ok
  hbw : x.bw.map List.length = vsAllocSz x.p
  hret : CausalRule x.ret

end VsCtx

/-! ## The stream's buffer on the evaluation memory -/

section
variable {x : VsCtx}

theorem VsCtx.p_leB (hx : x.HonB) : x.p ≤ 32 := by
  obtain ⟨_, _, _, _, hN⟩ := frontNum_of_child hx.ok.child
  exact hN.hp

theorem VsCtx.len_bwB (hx : x.HonB) {j : ℕ} (hj : j < 24) :
    (x.bw.getD j []).length = (vsAllocSz x.p).getD j 0 := by
  have hl' : x.bw.length = 24 := by
    have := congrArg List.length hx.hbw
    simpa [vsAllocSz_lengthF] using this
  have hl : j < x.bw.length := by rw [hl']; exact hj
  rw [List.getD_eq_getElem _ _ hl, List.getD_eq_getElem _ _ (by rw [vsAllocSz_lengthF]; exact hj)]
  have := List.getElem_of_eq hx.hbw (by simpa using hl)
  simpa using this

theorem VsCtx.holds_rd1B (hx : x.HonB) : HoldsWords x.rd1 (vsRuns x.cur x.bw) := by
  have hc := hx.ok.hcur
  have h := holdsWords_rdW (bases_zip_pairwise x.cur x.bw) fun q hq => by
    have := bases_zip_in x.cur x.bw q hq
    have hs : (x.bw.map List.length).sum ≤ 2 ^ 14 := by
      rw [hx.hbw]
      have hp := x.p_leB hx
      simp only [vsAllocSz, vsSz0, List.cons_append, List.nil_append, List.sum_cons, List.sum_nil]
      omega
    omega
  show HoldsWords (vsRd1 x.rdP x.cur x.bw x.ex) _
  unfold vsRd1
  exact holdsWords_or (rd' := fun A => (exAt x.ex A).or (some ((x.rdP A).getD 0))) h

theorem VsCtx.mem_runsB (hx : x.HonB) {j : ℕ} (hj : j < 24) : (x.base j, x.bw.getD j []) ∈ vsRuns x.cur x.bw := by
  have hl' : x.bw.length = 24 := by
    have := congrArg List.length hx.hbw
    simpa [vsAllocSz_lengthF] using this
  unfold vsRuns VsCtx.base
  rw [hx.hbw]
  exact mem_zip_getD (by rw [bases_lengthF, vsAllocSz_lengthF]; exact hj) (by rw [hl']; exact hj)

theorem VsCtx.reads_rd0_ofB (hx : x.HonB) {j : ℕ} (hj : j < 24)
    (hd : x.base j + (vsAllocSz x.p).getD j 0 ≤ x.base 13 ∨ x.base 13 + 12 ≤ x.base j)
    (hbd : x.base j + (vsAllocSz x.p).getD j 0 < 2 ^ 64 - 1) :
    ReadsAt x.rd0 (ptrAt (x.base j)) (x.bw.getD j []) := by
  have h1 : ReadsAt x.rd1 (ptrAt (x.base j)) (x.bw.getD j []) := x.holds_rd1B hx _ (x.mem_runsB hx hj)
  have hc := hx.ok.hcur
  have h13 : x.base 13 = x.cur + 639 := vsBaseF_13 _ _
  refine readsAt_rdSet (rd := x.rd1) (cells := x.cells19) h1 (by rw [x.len_bwB hx hj]; exact hbd) ?_
  intro c hcm
  simp only [VsCtx.cells19, vsCells19, List.mem_map, List.mem_range] at hcm
  obtain ⟨i, hi, rfl⟩ := hcm
  rw [x.len_bwB hx hj]
  dsimp only
  omega

/-- **`rd0` reads the stream's buffer.** -/
theorem VsCtx.reads18B (hx : x.HonB) : ReadsAt x.rd0 (ptrAt (x.base 18)) (x.bw.getD 18 []) := by
  have hc := hx.ok.hcur
  have hp := x.p_leB hx
  have b13 : x.base 13 = x.cur + 639 := vsBaseF_13 _ _
  have e : x.base 18 = x.cur + 824 := vsBaseF_18 _ _
  have s : (vsAllocSz x.p).getD 18 0 = 256 * x.p := rfl
  exact x.reads_rd0_ofB hx (by norm_num) (by omega) (by omega)

end

/-! ## The Fiat-Shamir facts -/

theorem chunks_width {w : ℕ} {ch : Chunks} (h : Chunks.new w = some ch) : ch.width = w := by
  unfold Chunks.new at h
  split_ifs at h
  obtain rfl := Option.some.inj h
  rfl

theorem oodGrindingBits_eq : Whir.oodGrindingBits = 15 := rfl

set_option maxHeartbeats 1000000 in
/-- **`VsFsChecks1` at the honest context**: from the placement, the stream's buffer, and the honest returns
and buffers at the out-of-domain point and the opening message. -/
theorem VsCtx.fsChecks1 {x : VsCtx} (hx : x.HonB) (hb18 : x.bw.getD 18 [] = padStream x.c.proof.stream)
    (hR : x.RetFs) (hB : x.BwFs) : VsFsChecks1 x := by
  have ha : x.args.length = 6 := rfl
  have hr := hx.hret
  obtain ⟨layout, r, hann, S, hlen, hpow, ood, link, st3, st4, -, -, -, -, -, -⟩ := natFront hx.ok.child
  obtain ⟨layout', r', hann', -, link', L, rest, hdrop, hL⟩ := natChildLink hx.ok.child
  rw [hann] at hann'
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hann')
  obtain ⟨layout'', r'', hann'', -, hN⟩ := frontNum_of_child hx.ok.child
  rw [hann] at hann''
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hann'')
  have hlay : x.lay = layout := by simp [VsCtx.lay, hann]
  -- the bridge on the context
  have hws : ∀ i < x.c.proof.stream.length,
      (padStream x.c.proof.stream).getD i 0 = x.c.proof.stream.getD i 0 := fun i hi => padStream_getDF hi
  have hwl : x.c.proof.stream.length ≤ (padStream x.c.proof.stream).length := by simp [padStream]
  have h0 : ReadsAt x.rd0 (ptrAt (x.base 18)) (padStream x.c.proof.stream) := by
    rw [← hb18]; exact x.reads18B hx
  have hw55 : x.w 55 = ptrAt (x.base 18) :=
    vsW_buf (rd1 := x.rd1) ha hr (j := 18) (by norm_num) rfl
  have hB13 := vsVal_oodS (rd0 := x.rd0) (args := x.args) (seed := x.seed) (c := x.c) (gsq := ptrAt x.qt)
    (out := ptrAt x.qo) rfl hw55 h0 (by omega) (fun i hi => hws i (by omega)) (by omega)
  have e499 : x.σ0 (.n 499) = cellsOfState (natOodS x.seed x.c) false 0 := outs_eq hB13 0 (by simp)
  have e500 : x.σ0 (.n 500) = cellsOfState (natOodS x.seed x.c) false 1 := outs_eq hB13 1 (by simp)
  have ecap : [x.σ0 (.n 507), x.σ0 (.n 508), x.σ0 (.n 509), x.σ0 (.n 510), x.σ0 (.n 511)] =
      capOf (natOodS x.seed x.c) := by
    have e8 : x.σ0 (.n 507) = cellsOfState (natOodS x.seed x.c) false 8 := outs_eq hB13 8 (by simp)
    have e9 : x.σ0 (.n 508) = cellsOfState (natOodS x.seed x.c) false 9 := outs_eq hB13 9 (by simp)
    have e10 : x.σ0 (.n 509) = cellsOfState (natOodS x.seed x.c) false 10 := outs_eq hB13 10 (by simp)
    have e11 : x.σ0 (.n 510) = cellsOfState (natOodS x.seed x.c) false 11 := outs_eq hB13 11 (by simp)
    have e12 : x.σ0 (.n 511) = cellsOfState (natOodS x.seed x.c) false 12 := outs_eq hB13 12 (by simp)
    rw [e8, e9, e10, e11, e12]
    rfl
  have hspf : x.spf = natSpf x.seed x.c x.lay.stackLog := by
    unfold VsCtx.spf natSpf; rw [ecap]
  -- the returns
  have hsl : x.spfN.length = 5 := by unfold VsCtx.spfN natSpf; exact squeezeN_cap_length _ _ rfl
  have e566 : x.w 566 = x.spfN.getD 0 0 := vsW_retC ha hr (by decide) (hR.r566 0 (by norm_num))
  have e567 : x.w 567 = x.spfN.getD 1 0 := vsW_retC ha hr (by decide) (hR.r566 1 (by norm_num))
  have e568 : x.w 568 = x.spfN.getD 2 0 := vsW_retC ha hr (by decide) (hR.r566 2 (by norm_num))
  have e569 : x.w 569 = x.spfN.getD 3 0 := vsW_retC ha hr (by decide) (hR.r566 3 (by norm_num))
  have e570 : x.w 570 = x.spfN.getD 4 0 := vsW_retC ha hr (by decide) (hR.r566 4 (by norm_num))
  have w566 : [x.w 566, x.w 567, x.w 568, x.w 569, x.w 570] = x.spfN := by
    rw [e566, e567, e568, e569, e570]; exact list5_getD hsl
  have hol : x.omN.length = 8 := by simp [VsCtx.omN, omRets, capOf]
  have e573 : x.w 573 = x.omN.getD 0 0 := vsW_retC ha hr (by decide) (hR.r573 0 (by norm_num))
  have e574 : x.w 574 = x.omN.getD 1 0 := vsW_retC ha hr (by decide) (hR.r573 1 (by norm_num))
  have e575 : x.w 575 = x.omN.getD 2 0 := vsW_retC ha hr (by decide) (hR.r573 2 (by norm_num))
  have e576 : x.w 576 = x.omN.getD 3 0 := vsW_retC ha hr (by decide) (hR.r573 3 (by norm_num))
  have e577 : x.w 577 = x.omN.getD 4 0 := vsW_retC ha hr (by decide) (hR.r573 4 (by norm_num))
  have e578 : x.w 578 = x.omN.getD 5 0 := vsW_retC ha hr (by decide) (hR.r573 5 (by norm_num))
  have e579 : x.w 579 = x.omN.getD 6 0 := vsW_retC ha hr (by decide) (hR.r573 6 (by norm_num))
  have e580 : x.w 580 = x.omN.getD 7 0 := vsW_retC ha hr (by decide) (hR.r573 7 (by norm_num))
  have w573 : [x.w 573, x.w 574, x.w 575, x.w 576, x.w 577, x.w 578, x.w 579, x.w 580] = x.omN := by
    rw [e573, e574, e575, e576, e577, e578, e579, e580]
    exact list8_getD hol
  -- the link grind
  have hn24 : hMax layout ≤ 24 := by obtain ⟨t, ht, e⟩ := hN.hn; rw [← e]; exact hN.h24 t ht
  have hwd : L.chunks.width = widthOf layout := chunks_width hL.chunks
  have hbits : L.bits layout = 2 := by
    unfold LinkNat.bits
    rw [hwd]
    exact VerifySub.linkGrind_bits (n := linkRows layout) hn24 hN.hw19 hN.hw24
  have hn0 : x.c.proof.stream.getD 12 0 = L.n0 := by
    have := getD_of_drop hdrop 0
    simp only [Nat.add_zero] at this
    rw [this, LinkNat.words, hbits]
    rfl
  have hl13 : 13 ≤ x.c.proof.stream.length := by
    have h1 : 1 ≤ (x.c.proof.stream.drop 12).length := by
      rw [hdrop, LinkNat.words, hbits]; simp [grindWords]
    rw [List.length_drop] at h1
    omega
  have hg := hL.grind
  rw [hbits] at hg
  have hg' := (grindOk_iff (s := natF3 x.seed x.c layout.stackLog) (by norm_num) L.n0).mp hg
  refine ⟨?_, ?_, ?_, ?_, ?_, hB.b17⟩
  · -- hlow5
    rw [e500, ← LeanVM.Guest.Value.Keccak.powLane_cells]
    have h := hpow
    rw [oodGrindingBits_eq, powOk, decide_eq_true_iff] at h
    exact h
  · -- hlow6
    rw [e574]
    have hcap : [x.spfN.getD 0 0, x.spfN.getD 1 0, x.spfN.getD 2 0, x.spfN.getD 3 0, x.spfN.getD 4 0] =
        (natSpf x.seed x.c layout.stackLog).2.cap := by rw [list5_getD hsl, VsCtx.spfN, hlay]
    simp only [VsCtx.omN, omRets, List.cons_append, List.getD_cons_succ, List.getD_cons_zero]
    rw [hcap, hws 11 (by omega), hws 12 (by omega), hn0]
    simp only [omState, Fs.absorbAll, List.foldl_cons, List.foldl_nil]
    rw [← natF3_eq]
    exact hg'
  · -- hspf
    rw [w566, hspf]; rfl
  · -- hP22
    have e : x.σ0 (.n 499) :: x.spf.1 = natOodZ x.seed x.c x.lay.stackLog := by
      rw [e499, hspf, natOodZ_eq, LeanVM.Guest.Value.Keccak.challengeOf_cells]
    rw [e]
    exact hB.b16
  · -- hom
    rw [w573, VsCtx.omN, e566, e567, e568, e569, e570]

/-! ## The export's converse: the fresh claim's point is the index point's first `19` words -/

/-- **The fresh claim's point, natively**: the link's index point `L.r` has the pointer width's words, at least
`19`, its first `19` the fresh claim's point (`L.Ok.point` at `logBytecode = 19`). -/
theorem natFreshPoint {seed : Digest} {c : Child} (hc : VsChildOk guestBytecode seed c) :
    ∃ (layout : Layout) (r : ℕ), announcedLayoutAndRate guestBytecode c.proof.stream = some (layout, r) ∧
      ∃ (link : LinkEnd) (L : LinkNat) (rest : List E), c.proof.stream.drop 12 = L.words layout ++ rest ∧
        L.Ok layout (natF3 seed c layout.stackLog) c.freshClaim link ∧
        (L.r layout (natF3 seed c layout.stackLog)).length = widthOf layout ∧ 19 ≤ widthOf layout ∧
        (L.r layout (natF3 seed c layout.stackLog)).take 19 = c.freshClaim.point := by
  obtain ⟨layout, r, hann, S, link, L, rest, hdrop, hL⟩ := natChildLink hc
  have hlb : layout.logBytecode = 19 :=
    Nat.pow_right_injective (le_refl 2) (S.logBytecode_eq.symm.trans guest_logBytecode)
  obtain ⟨layout'', r'', hann'', -, hN⟩ := frontNum_of_child hc
  rw [hann] at hann''
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hann'')
  have hlen : (L.r layout (natF3 seed c layout.stackLog)).length = widthOf layout := by
    unfold LinkNat.r LinkNat.chainI
    rw [List.length_map, natChain_length, chunks_width hL.chunks]
    rfl
  refine ⟨layout, r, hann, link, L, rest, hdrop, hL, hlen, hN.hw19, ?_⟩
  have := hL.point
  rwa [hlb] at this

/-- **`Bw3`'s `hpt`** at `r_pt`'s honest words, the index point then anything. -/
theorem freshPoint_of_bw6 {c : Child} {layout : Layout} {L : LinkNat} {F : Fs} {pad : List E}
    {bw6 : List E} (h6 : bw6 = L.r layout F ++ pad) (hl : 19 ≤ (L.r layout F).length)
    (hp : (L.r layout F).take 19 = c.freshClaim.point) : c.freshClaim.point = bw6.take 19 := by
  rw [h6, List.take_append_of_le_length hl, hp]

end
end LeanVM.Guest.B1.VsC
