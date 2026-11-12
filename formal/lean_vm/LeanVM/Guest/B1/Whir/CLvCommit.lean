/-
  LeanVM.Guest.B1.Whir.CLvCommit

  A non-final level's next commitment honestly: the message and its OOD nonce, the OOD grind,
  point and value, and the query nonce.
-/

module

public import LeanVM.Guest.B1.Whir.CLvMsg
public import LeanVM.Guest.B1.Whir.CAtoms

/-!
# A non-final level's message, honestly (G:1570-1592)

`osCommit_complete`: `sent` allocated at a given pointer; `opening_message` reads the next root's
two cells, the high part and the OOD nonce (`omRets`), the root stored in `sent` and
`level_roots`; the OOD grind's check; the OOD point (`squeeze_point_from`, returning `spfRets`);
the value and the query nonce read and permuted (`commitS`), the zero run allocated if it was not.
-/

namespace LeanVM.Guest.B1.Whir

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest LeanVM.Guest.B1
open LeanVM.Guest.Value LeanVM.Protocol LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

variable {H : CallRel → Reader → Prop}

/-- The OOD point's capacity after its squeezes (`squeeze_point_from`'s returns). -/
def spfRets (cap msg : List E) (n1 : E) (n : ℕ) : List E :=
  ((⟨capOf (omState cap msg (some n1)), []⟩ : Fs).squeezeN (n - 1)).2.cap

/-- The query nonce's permutation after the OOD value. -/
def commitS (cap msg : List E) (n1 : E) (n : ℕ) (y0 nq : E) : KeccakState :=
  ((⟨spfRets cap msg n1 n, []⟩ : Fs).absorbAll [y0] dsObserve).nonceState nq

theorem squeezeN_cap_length : ∀ (n : ℕ) (s : Fs), s.cap.length = 5 →
    (s.squeezeN n).2.cap.length = 5
  | 0, _, h => h
  | n + 1, s, _ => squeezeN_cap_length n s.squeeze.2 (by simp [Fs.squeeze, capOf])

theorem spfRets_length (cap msg : List E) (n1 : E) (n : ℕ) : (spfRets cap msg n1 n).length = 5 :=
  squeezeN_cap_length _ _ (by simp [capOf])

/-- The cells the OOD value and the query nonce take: the capacity's copy, the value and the
nonce with their tags. -/
def oodVals (cp : List E) (y0 nq : E) : List E :=
  cp ++ [y0, y0, word 0 1, nq, nq, word 0 4]

theorem five_getD {l : List E} (h : l.length = 5) :
    l = [l.getD 0 0, l.getD 1 0, l.getD 2 0, l.getD 3 0, l.getD 4 0] := by
  match l, h with
  | [a, b, c, d, e], _ => rfl

theorem commitS_eq (cp : List E) (y0 nq : E) :
    ((⟨cp, []⟩ : Fs).absorbAll [y0] dsObserve).nonceState nq =
      (⟨cp, [(y0, dsObserve), (nq, dsPowNonce)]⟩ : Fs).perm := by
  simp [Fs.absorbAll, Fs.nonceState, Fs.absorb, rateScalars]

/-- **A non-final level's message, honestly** (G:1570-1592). -/
theorem osCommit_complete {c : OsCfg} {lvl : ℕ} {lv : OsLv} {st : OsSt} (σ : Val) (hsf : st.Sf)
    (hok : ∀ C rd, H C rd → st.Ok σ) (x0 x1 : E) (high : List E) (n1 y0 nq pS : E)
    (hoff : (lvl + 1) * ligColsCap < u128Bound)
    (hom : ∀ C rd, H C rd → C ("opening_message__L" ++ natStr (2 + lv.folds) ++ "_L1")
      (st.fsv σ ++ [st.cur σ, pS])
      (omRets (st.fsv σ) (x0 :: x1 :: high) (some n1) (st.cur σ) (2 + lv.folds + 1)))
    (hg : ∀ C rd, H C rd → C ("grind_check__L" ++ natStr levelOodGrind)
      [cellsOfState (omState (st.fsv σ) (x0 :: x1 :: high) (some n1)) false 1, σ (.n osTabs)] [])
    (hsent : ∀ C rd, H C rd → LoadHolds rd pS 0 x0 ∧ LoadHolds rd pS 1 x1 ∧
      LoadHolds rd (σ (.n osRoots)) (2 * lvl + 2) x0 ∧ LoadHolds rd (σ (.n osRoots)) (2 * lvl + 3) x1)
    (hspf : ∀ C rd, H C rd → C ("squeeze_point_from__L" ++ natStr lv.logCols)
      (capOf (omState (st.fsv σ) (x0 :: x1 :: high) (some n1)) ++
        [cellsOfState (omState (st.fsv σ) (x0 :: x1 :: high) (some n1)) false 0,
          σ (.n osOodz) * gen ^ ((lvl + 1) * ligColsCap)])
      (spfRets (st.fsv σ) (x0 :: x1 :: high) n1 lv.logCols))
    (hys : ∀ C rd, H C rd → ReadsAt rd (st.cur σ * gen ^ (2 + lv.folds + 1)) [y0, nq]) :
    BlkA H σ st.k (osCommit c lvl lv st).2.k (osCommit c lvl lv st).1 (fun σ' ↦
      OsStep σ σ' st (osCommit c lvl lv st).2 ∧
      (osCommit c lvl lv st).2.F σ' =
        ⟨capOf (commitS (st.fsv σ) (x0 :: x1 :: high) n1 lv.logCols y0 nq), []⟩ ∧
      σ' (.n (osCommit c lvl lv st).2.word0) =
        rdCell (commitS (st.fsv σ) (x0 :: x1 :: high) n1 lv.logCols y0 nq) 0 ∧
      σ' (.n (osCommit c lvl lv st).2.pow0) =
        rdCell (commitS (st.fsv σ) (x0 :: x1 :: high) n1 lv.logCols y0 nq) 1 ∧
      (osCommit c lvl lv st).2.ys = [(osCommit c lvl lv st).2.ys.getD 0 0] ∧
      σ' (.n ((osCommit c lvl lv st).2.ys.getD 0 0)) = y0 ∧
      σ' (.n (osCommit c lvl lv st).2.sent) = pS ∧ σ' (.n st.k) = gw (2 + lv.folds) ∧
      (osCommit c lvl lv st).2.cur σ' = st.cur σ * gen ^ (2 + lv.folds) * gen ^ 3 ∧
      (osCommit c lvl lv st).2.claim = st.claim) := by
  set k := st.k with hk
  set msg := x0 :: x1 :: high with hmsg
  set cap := st.fsv σ with hcap
  set cur := st.cur σ with hcur
  set s0 : OsSt := { st with k := k + 2 } with hs0
  set cu := osCurS s0 with hcu
  set r := cu.2.2.k with hr
  set s1 : OsSt := { cu.2.2 with k := r + 10 } with hs1
  set row0 := (lvl + 1) * ligColsCap with hrow0
  set o0 := osMatS c.plan osOodz row0 s1 with ho0
  set q := o0.2.2.k with hq
  set b := q + 10 with hbd
  set p := (osPad o0.2.2.pad (b + 6)).2.1 with hp
  set j := (osPad o0.2.2.pad (b + 6)).2.2 with hj
  set S1 := omState cap msg (some n1) with hS1
  set spf := spfRets cap msg n1 lv.logCols with hspf'
  set S := commitS cap msg n1 lv.logCols y0 nq with hS
  have k36 : 33 ≤ k := hsf.k
  have kr : k + 2 ≤ r := osCurS_k s0
  have kq : r + 10 ≤ q := osMatS_k c.plan osOodz row0 s1
  have bj : b + 6 ≤ j := osPad_next _ _
  have hpad0 : o0.2.2.pad = st.pad := rfl
  have hpj : p + 4 < j := by
    rcases osPad_ptr o0.2.2.pad (b + 6) (fun q' hq' ↦ by
      rw [hpad0] at hq'; have := hsf.padB q' hq'; omega) with h | h <;> omega
  have pcu : cu.2.1 < r := osMat_ptr_lt _ _ _ (show st.cb < k + 2 by have := hsf.below.cb; omega)
  have po0 : o0.2.1 < q := osMatS_ptr_lt _ _ _ _ (show 26 < r + 10 by omega)
  have hmb1 : MatsBelow s1.k s1.mats := show MatsBelow (r + 10) st.mats from fun m hm ↦ by
    obtain ⟨a, b, d⟩ := hsf.below.mats m hm; exact ⟨by omega, by omega, by omega⟩
  -- the heap and the cursor
  have b1 := BlkA.seq (H := H) (show k ≤ k + 2 by omega) kr (heap_blk σ (2 + lv.folds) k pS)
    (B := cu.1) (OutB := fun σ' ↦ σ' (.n cu.2.1) = σ (.n st.cb) * gen ^ st.co) fun σ1 ha1 _ ↦ by
      have hc := osCurS_blkA (H := H) (st := s0) σ1 (show st.cb < k + 2 by have := hsf.below.cb; omega)
        hsf.co
      rw [ha1 st.cb hsf.below.cb] at hc
      exact hc
  -- the message, its grind and the root
  have b2 := BlkA.seq (H := H) (le_trans (by omega) kr) (show r ≤ r + 8 by omega) b1
    (B := [.call ("opening_message__L" ++ natStr (2 + lv.folds) ++ "_L1")
      ((st.fs ++ [cu.2.1, k + 1]).map V.n) (osRun r 8)])
    (OutB := fun σ' ↦ ∀ j < 8, σ' (.n (r + j)) =
      (omRets cap msg (some n1) cur (2 + lv.folds + 1)).getD j 0)
    fun σ1 ha1 ho1 ↦ by
      refine call_blk _ (omRets_length _ _ _ _ _) (fun i hi ↦ ?_) fun C rd hH ↦ ?_
      · simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hi
        rcases hi with hi | rfl | rfl
        · have := hsf.below.fs i hi; omega
        · exact pcu
        · omega
      · obtain ⟨⟨-, e1⟩, ecu⟩ := ho1 C rd hH
        have hargs : (st.fs ++ [cu.2.1, k + 1]).map (fun i ↦ σ1 (.n i)) = cap ++ [cur, pS] := by
          simp only [List.map_append, List.map_cons, List.map_nil, hcap, OsSt.fsv]
          congr 1
          · exact List.map_congr_left fun f hf ↦ ha1 f (hsf.below.fs f hf)
          · rw [ecu, e1]; rfl
        rw [hargs]
        exact hom C rd hH
  have b2g := BlkA.seq (H := H) (show k ≤ r + 8 by omega) (show r + 8 ≤ r + 8 from le_rfl) b2
    (B := [.call ("grind_check__L" ++ natStr levelOodGrind) ([r + 1, osTabs].map V.n) []])
    (OutB := fun σ' ↦ ([r + 1, osTabs].map V.n).map σ' = [cellsOfState S1 false 1, σ (.n osTabs)])
    fun σ1 ha1 ho1 ↦ by
      have h := call0_blk (H := H) (σ := σ1) (k := r + 8)
        (f := "grind_check__L" ++ natStr levelOodGrind) (args := [r + 1, osTabs]) (fun i hi ↦ by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
          rcases hi with rfl | rfl
          · omega
          · show 10 < r + 8; omega) fun C rd hH ↦ by
        obtain ⟨-, e2⟩ := ho1 C rd hH
        simp only [List.map_cons, List.map_nil]
        rw [e2 1 (by omega), ha1 _ (show 10 < k by omega)]
        simpa [omRets] using hg C rd hH
      refine h.monoH fun C rd hH σ' ha e ↦ ?_
      obtain ⟨-, e2⟩ := ho1 C rd hH
      rw [e]
      simp only [List.map_cons, List.map_nil]
      rw [e2 1 (by omega), ha1 _ (show 10 < k by omega)]
      simp [omRets, hS1]
  have b3 := BlkA.seq (H := H) (show k ≤ r + 8 by omega) (show r + 8 ≤ r + 10 by omega) b2g
    (B := [osLd (r + 8) (k + 1) 0, osLd (r + 8) osRoots (2 * lvl + 2), osLd (r + 9) (k + 1) 1,
      osLd (r + 9) osRoots (2 * lvl + 3)])
    (OutB := fun σ' ↦ σ' (.n (r + 8)) = x0 ∧ σ' (.n (r + 9)) = x1) fun σ1 ha1 ho1 ↦ by
      refine ⟨lstF (r + 8) [x0, x1], fun C rd hH σ' ha hr' ↦ ?_⟩
      have v0 := lstF_at hr' (by simp) 0 (by simp)
      have v1 := lstF_at hr' (by simp) 1 (by simp)
      simp only [List.getD_cons_zero, List.getD_cons_succ, Nat.add_zero] at v0 v1
      rw [show r + 8 + 1 = r + 9 by omega] at v1
      obtain ⟨⟨⟨⟨-, e1⟩, -⟩, -⟩, -⟩ := ho1 C rd hH
      obtain ⟨l0, l1, l2, l3⟩ := hsent C rd hH
      have ep : σ' (.n (k + 1)) = pS := by rw [ha _ (by omega), e1]
      have er : σ' (.n osRoots) = σ (.n osRoots) := by
        rw [ha _ (show 14 < r + 8 by omega), ha1 _ (by show 14 < k; omega)]
      refine ⟨?_, v0, v1⟩
      simp only [allOk_cons, allOk_nil, and_true, stmtOk_atom, holds_load, osLd, ep, er, v0, v1]
      exact ⟨l0, l2, l1, l3⟩
  -- the OOD point
  have b4 := BlkA.seq (H := H) (show k ≤ r + 10 by omega) kq b3 (B := o0.1)
    (OutB := fun σ' ↦ σ' (.n o0.2.1) = σ (.n osOodz) * gen ^ row0 ∧ MatsOk σ' o0.2.2.mats ∧
      MatsBelow o0.2.2.k o0.2.2.mats) fun σ1 ha1 _ ↦ by
      have h := osMatS_blkA (H := H) (P := c.plan) (base := osOodz) (off := row0) (s := s1) σ1
        (show 26 < r + 10 by omega) hmb1 (fun C rd hH ↦
          matsOk_agree (hok C rd hH).mats hsf.below.mats fun i hi ↦ ha1 i hi) hoff
      rw [ha1 osOodz (by show 26 < k; omega)] at h
      exact h
  have b5 := BlkA.seq (H := H) (show k ≤ q by omega) (show q ≤ q + 5 by omega) b4
    (B := [.call ("squeeze_point_from__L" ++ natStr lv.logCols)
      ([r + 2, r + 3, r + 4, r + 5, r + 6, r, o0.2.1].map V.n) (osRun q 5)])
    (OutB := fun σ' ↦ ∀ j < 5, σ' (.n (q + j)) = spf.getD j 0) fun σ1 ha1 ho1 ↦ by
      refine call_blk _ (spfRets_length _ _ _ _) (fun i hi ↦ ?_) fun C rd hH ↦ ?_
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
        rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega
      · obtain ⟨⟨⟨⟨-, e2⟩, -⟩, -⟩, eo, -⟩ := ho1 C rd hH
        have e : ∀ j < 8, σ1 (.n (r + j)) =
            (omRets cap msg (some n1) cur (2 + lv.folds + 1)).getD j 0 := e2
        have hargs : [r + 2, r + 3, r + 4, r + 5, r + 6, r, o0.2.1].map (fun i ↦ σ1 (.n i)) =
            capOf S1 ++ [cellsOfState S1 false 0, σ (.n osOodz) * gen ^ row0] := by
          simp only [List.map_cons, List.map_nil]
          rw [e 2 (by omega), e 3 (by omega), e 4 (by omega), e 5 (by omega), e 6 (by omega),
            show r = r + 0 from rfl, e 0 (by omega), eo]
          simp [omRets, capOf, hS1]
        rw [hargs]
        exact hspf C rd hH
  -- the value and the query nonce
  have b8 := BlkA.seq (H := H) (show k ≤ q + 5 by omega) (show q + 5 ≤ b + 6 by omega) b5
    (B := ((List.range 5).map fun i ↦ osCp (q + 5 + i) (q + i)) ++
      [osLd b (r + 7) 0, osCp (b + 1) b, osCst (b + 2) (word 0 1),
        osLd (b + 3) (r + 7) 1, osCp (b + 4) (b + 3), osCst (b + 5) (word 0 4)])
    (OutB := fun σ' ↦ ∀ j < 11, σ' (.n (q + 5 + j)) = (oodVals spf y0 nq).getD j 0)
    fun σ1 ha1 ho1 ↦ by
      have hsl : spf.length = 5 := spfRets_length _ _ _ _
      refine ⟨lstF (q + 5) (oodVals spf y0 nq), fun C rd hH σ' ha hr' ↦ ?_⟩
      have hv : ∀ j < 11, σ' (.n (q + 5 + j)) = (oodVals spf y0 nq).getD j 0 := fun j hj ↦
        lstF_at hr' (by simp [oodVals, hsl, hbd]) j (by simp [oodVals, hsl]; omega)
      refine ⟨?_, hv⟩
      obtain ⟨⟨⟨⟨⟨⟨-, -⟩, e2⟩, -⟩, -⟩, -⟩, e7⟩ := ho1 C rd hH
      have hs : ∀ j < 5, σ' (.n (q + j)) = spf.getD j 0 := fun j hj ↦ by
        rw [ha _ (by omega)]; exact e7 j hj
      have hcb : σ' (.n (r + 7)) = cur * gen ^ (2 + lv.folds + 1) := by
        rw [ha _ (by omega), e2 7 (by omega)]; simp [omRets, capOf]
      have hys' := hys C rd hH
      have l0 : LoadHolds rd (σ' (.n (r + 7))) 0 y0 := by rw [hcb]; exact hys' 0 (by simp)
      have l1 : LoadHolds rd (σ' (.n (r + 7))) 1 nq := by rw [hcb]; exact hys' 1 (by simp)
      have w : ∀ j, 5 ≤ j → j < 16 → σ' (.n (q + j)) = (oodVals spf y0 nq).getD (j - 5) 0 :=
        fun j h1 h2 ↦ by
          have := hv (j - 5) (by omega)
          rwa [show q + 5 + (j - 5) = q + j by omega] at this
      simp only [hbd, List.range_succ, List.range_zero, List.map_cons, List.map_nil, List.nil_append,
        List.cons_append, allOk_cons, allOk_nil, and_true, stmtOk_atom,
        holds_copy, holds_load, holds_const, osCp, osLd, osCst, Nat.add_assoc, Nat.reduceAdd]
      simp (disch := omega) only [w, hs, Nat.reduceSub, oodVals]
      simp (disch := simp [hsl]) only [List.getD_append, List.getD_append_right, hsl, Nat.reduceSub,
        List.getD_cons_zero, List.getD_cons_succ]
      exact ⟨trivial, trivial, trivial, trivial, trivial, l0, trivial, trivial, l1, trivial,
        trivial⟩
  -- the zero run
  have b8p := BlkA.seq (H := H) (show k ≤ b + 6 by omega) bj b8 (B := (osPad o0.2.2.pad (b + 6)).1)
    (OutB := fun σ' ↦ PadOk σ' (some p)) fun σ1 ha1 _ ↦
      osPad_blk σ1 o0.2.2.pad (b + 6) (fun C rd hH ↦ by
        rw [hpad0]; exact ((hok C rd hH).agree fun i hi ↦ ha1 i (by omega)).pad)
        (fun q' hq' ↦ by rw [hpad0] at hq'; have := hsf.padB q' hq'; omega)
  -- the permutation
  have b9 := BlkA.seq (H := H) (show k ≤ j by omega) (show j ≤ j + 13 by omega) b8p
    (B := [osKeccak [b + 1, b + 2, b + 4, b + 5, p + 1, p + 2, p + 3, p + 4, q + 5, q + 6, q + 7,
      q + 8, q + 9] j])
    (OutB := fun σ' ↦ ∀ i < 13, σ' (.n (j + i)) = rdCell S i) fun σ1 ha1 ho1 ↦ by
      have hsl : spf.length = 5 := spfRets_length _ _ _ _
      refine keccak_blk ⟨spf, [(y0, dsObserve), (nq, dsPowNonce)]⟩ (by simp)
        (by simp) (fun i hi ↦ by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
          rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
            omega) (fun C rd hH ↦ ?_) |>.mono fun σ' h i hi ↦ by
        rw [h i hi, hS, commitS, commitS_eq]
      obtain ⟨⟨-, e8⟩, z⟩ := ho1 C rd hH
      obtain ⟨z1, z2, z3, z4⟩ := z p rfl
      have w : ∀ i, 5 ≤ i → i < 16 → σ1 (.n (q + i)) = (oodVals spf y0 nq).getD (i - 5) 0 :=
        fun i h1 h2 ↦ by
          have := e8 (i - 5) (by omega)
          rwa [show q + 5 + (i - 5) = q + i by omega] at this
      simp only [hbd, List.map_cons, List.map_nil, Nat.add_assoc, Nat.reduceAdd, z1, z2, z3, z4]
      simp (disch := omega) only [w, Nat.reduceSub]
      simp (disch := simp [hsl]) only [oodVals, List.getD_append, List.getD_append_right, hsl,
        Nat.reduceSub, List.getD_cons_zero, List.getD_cons_succ]
      conv_rhs => rw [five_getD hsl]
      simp [pendCells, Keccak.scalarCells, dsObserve, dsPowNonce, word]
      exact ⟨rfl, rfl⟩
  have ek : (osCommit c lvl lv st).2.k = j + 13 := rfl
  rw [ek]
  refine BlkA.congr (BlkA.monoH b9.agree fun C rd hH σ' ha ⟨ho, hag⟩ ↦ ?_) (by
    simp only [osCommit, List.append_assoc, List.cons_append, List.nil_append]; rfl)
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨eh0, eh1⟩, -⟩, e2⟩, -⟩, -⟩, -, hm1, hb1⟩, -⟩, e8⟩, hpadP⟩, e9⟩ := ho
  have hok' := hok C rd hH
  have hsl : spf.length = 5 := spfRets_length _ _ _ _
  have w : ∀ i, 5 ≤ i → i < 16 → σ' (.n (q + i)) = (oodVals spf y0 nq).getD (i - 5) 0 :=
    fun i h1 h2 ↦ by
      have := e8 (i - 5) (by omega)
      rwa [show q + 5 + (i - 5) = q + i by omega] at this
  refine ⟨⟨⟨⟨rfl, ⟨?_, ?_, ?_, ?_⟩, by show 2 < u128Bound; unfold u128Bound; omega,
    fun p' hp' ↦ ?_, by omega⟩, hm1, ?_⟩, by omega, hag⟩, ?_, ?_, ?_, rfl, ?_, ?_, eh0, ?_, rfl⟩
  · intro f hf
    have hf' : f ∈ [j + 8, j + 9, j + 10, j + 11, j + 12] := hf
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hf'
    rcases hf' with rfl | rfl | rfl | rfl | rfl <;> omega
  · show r + 7 < j + 13; omega
  · show st.claim < j + 13; have := hsf.below.claim; omega
  · intro m hm; obtain ⟨a, b', d⟩ := hb1 m hm
    exact ⟨by have : m.out < q := a; omega, by have : m.src < q := b'; omega,
      by have : m.base < q := d; omega⟩
  · have hq' : some p = some p' := hp'
    simp only [Option.some.injEq] at hq'; subst hq'; omega
  · intro p' hp'
    have hq' : some p = some p' := hp'
    simp only [Option.some.injEq] at hq'; subst hq'
    obtain ⟨z1, z2, z3, z4⟩ := hpadP p rfl
    exact ⟨z1, z2, z3, z4⟩
  · show (⟨[j + 8, j + 9, j + 10, j + 11, j + 12].map (fun i ↦ σ' (.n i)), []⟩ : Fs) = _
    simp only [List.map_cons, List.map_nil]
    rw [e9 8 (by omega), e9 9 (by omega), e9 10 (by omega), e9 11 (by omega), e9 12 (by omega)]
    simp only [capOf, ← rdCell_eq]
    rfl
  · show σ' (.n j) = _
    simpa using e9 0 (by omega)
  · show σ' (.n (j + 1)) = _
    exact e9 1 (by omega)
  · show σ' (.n b) = y0
    rw [show b = q + 10 from rfl, w 10 (by omega) (by omega)]
    simp (disch := simp [hsl]) [oodVals, hsl]
  · show σ' (.n (k + 1)) = pS; exact eh1
  · simp only [OsSt.cur]
    show σ' (.n (r + 7)) * gen ^ 2 = _
    rw [e2 7 (by omega)]
    simp [omRets, capOf, hcur]
    ring

end
end LeanVM.Guest.B1.Whir
