/-
  LeanVM.Guest.B1.Whir.CLvCommit

  A non-final level's next commitment honestly on f128: the message, the out-of-domain points and
  values and the query nonce.
-/

module

public import LeanVM.Guest.B1.Whir.CLvMsg
public import LeanVM.Guest.B1.Whir.CAtoms

/-!
# A non-final level's message, honestly (G:1577-1603)

`osCommit_complete`: `sent` allocated at a given pointer; `opening_message` reads the next root's
two cells and the high part (`omRets`, no nonce), the root stored in `sent` and `level_roots`; the
two out-of-domain points (`squeeze_point_from`, `squeeze_point`, returning `spfRets`, `spRets`);
the two values and the query nonce read and permuted (`commitS`).
-/

namespace LeanVM.Guest.B1.Whir

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest LeanVM.Guest.B1
open LeanVM.Guest.Value LeanVM.Protocol LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

variable {H : CallRel → Reader → Prop}

/-- The first out-of-domain point's capacity after its squeezes (`squeeze_point_from`'s
returns). -/
def spfRets (cap msg : List E) (n : ℕ) : List E :=
  ((⟨capOf (omState cap msg none), []⟩ : Fs).squeezeN (n - 1)).2.cap

/-- The second's (`squeeze_point`'s returns). -/
def spRets (cap msg : List E) (n : ℕ) : List E :=
  ((⟨spfRets cap msg n, []⟩ : Fs).squeezeN n).2.cap

/-- The query nonce's permutation after the out-of-domain values. -/
def commitS (cap msg : List E) (n : ℕ) (y0 y1 nq : E) : KeccakState :=
  ((⟨spRets cap msg n, []⟩ : Fs).absorbAll [y0, y1] dsObserve).nonceState nq

theorem squeezeN_cap_length : ∀ (n : ℕ) (s : Fs), s.cap.length = 5 →
    (s.squeezeN n).2.cap.length = 5
  | 0, _, h => h
  | n + 1, s, _ => squeezeN_cap_length n s.squeeze.2 (by simp [Fs.squeeze, capOf])

theorem spfRets_length (cap msg : List E) (n : ℕ) : (spfRets cap msg n).length = 5 :=
  squeezeN_cap_length _ _ (by simp [capOf])

theorem spRets_length (cap msg : List E) (n : ℕ) : (spRets cap msg n).length = 5 :=
  squeezeN_cap_length _ _ (spfRets_length _ _ _)

/-- The cells the out-of-domain values and the query nonce take: the capacity's copy, the values
and the nonce with their tags. -/
def oodVals (cp : List E) (y0 y1 nq : E) : List E :=
  cp ++ [y0, y0, word 0 1, y0, y1, y1, word 0 1, y1, nq, nq, word 0 4, word 0 0, word 0 0]

theorem five_getD {l : List E} (h : l.length = 5) :
    l = [l.getD 0 0, l.getD 1 0, l.getD 2 0, l.getD 3 0, l.getD 4 0] := by
  match l, h with
  | [a, b, c, d, e], _ => rfl

theorem commitS_eq (cp : List E) (y0 y1 nq : E) :
    ((⟨cp, []⟩ : Fs).absorbAll [y0, y1] dsObserve).nonceState nq =
      (⟨cp, [(y0, dsObserve), (y1, dsObserve), (nq, dsPowNonce)]⟩ : Fs).perm := by
  rw [absorbAll_short _ _ _ (by simp)]
  simp [Fs.nonceState, Fs.absorb, rateScalars]

/-- **A non-final level's message, honestly** (G:1577-1603). -/
theorem osCommit_complete {c : OsCfg} {lvl : ℕ} {lv : OsLv} {st : OsSt} (σ : Val) (hsf : st.Sf)
    (hok : ∀ C rd, H C rd → st.Ok σ) (x0 x1 : E) (high : List E) (y0 y1 nq pS : E)
    (hoff : (oodSamples * (lvl + 1) + 1) * ligColsCap < u128Bound)
    (hom : ∀ C rd, H C rd → C ("opening_message__L" ++ natStr (2 + lv.folds) ++ "_L0")
      (st.fsv σ ++ [st.cur σ, pS]) (omRets (st.fsv σ) (x0 :: x1 :: high) none (st.cur σ) (2 + lv.folds)))
    (hsent : ∀ C rd, H C rd → LoadHolds rd pS 0 x0 ∧ LoadHolds rd pS 1 x1 ∧
      LoadHolds rd (σ (.n osRoots)) (2 * lvl + 2) x0 ∧ LoadHolds rd (σ (.n osRoots)) (2 * lvl + 3) x1)
    (hspf : ∀ C rd, H C rd → C ("squeeze_point_from__L" ++ natStr lv.logCols)
      (capOf (omState (st.fsv σ) (x0 :: x1 :: high) none) ++
        [cellsOfState (omState (st.fsv σ) (x0 :: x1 :: high) none) false 0,
          σ (.n osOodz) * gen ^ (oodSamples * (lvl + 1) * ligColsCap)])
      (spfRets (st.fsv σ) (x0 :: x1 :: high) lv.logCols))
    (hsp : ∀ C rd, H C rd → C ("squeeze_point__L" ++ natStr lv.logCols)
      (spfRets (st.fsv σ) (x0 :: x1 :: high) lv.logCols ++
        [σ (.n osOodz) * gen ^ ((oodSamples * (lvl + 1) + 1) * ligColsCap)])
      (spRets (st.fsv σ) (x0 :: x1 :: high) lv.logCols))
    (hys : ∀ C rd, H C rd → ReadsAt rd (st.cur σ * gen ^ (2 + lv.folds)) [y0, y1, nq]) :
    BlkA H σ st.k (osCommit c lvl lv st).2.k (osCommit c lvl lv st).1 (fun σ' ↦
      OsStep σ σ' st (osCommit c lvl lv st).2 ∧
      (osCommit c lvl lv st).2.F σ' =
        ⟨capOf (commitS (st.fsv σ) (x0 :: x1 :: high) lv.logCols y0 y1 nq), []⟩ ∧
      σ' (.n (osCommit c lvl lv st).2.word0) =
        rdCell (commitS (st.fsv σ) (x0 :: x1 :: high) lv.logCols y0 y1 nq) 0 ∧
      σ' (.n (osCommit c lvl lv st).2.pow0) =
        rdCell (commitS (st.fsv σ) (x0 :: x1 :: high) lv.logCols y0 y1 nq) 1 ∧
      (osCommit c lvl lv st).2.ys = [(osCommit c lvl lv st).2.ys.getD 0 0,
        (osCommit c lvl lv st).2.ys.getD 1 0] ∧
      σ' (.n ((osCommit c lvl lv st).2.ys.getD 0 0)) = y0 ∧
      σ' (.n ((osCommit c lvl lv st).2.ys.getD 1 0)) = y1 ∧
      σ' (.n (osCommit c lvl lv st).2.sent) = pS ∧ σ' (.n st.k) = gw (2 + lv.folds) ∧
      (osCommit c lvl lv st).2.cur σ' = st.cur σ * gen ^ (2 + lv.folds) * gen ^ 3 ∧
      (osCommit c lvl lv st).2.claim = st.claim ∧ (osCommit c lvl lv st).2.pad = st.pad) := by
  set k := st.k with hk
  set msg := x0 :: x1 :: high with hmsg
  set cap := st.fsv σ with hcap
  set cur := st.cur σ with hcur
  set s0 : OsSt := { st with k := k + 2 } with hs0
  set cu := osCurS s0 with hcu
  set r := cu.2.2.k with hr
  set s1 : OsSt := { cu.2.2 with k := r + 10 } with hs1
  set row0 := oodSamples * (lvl + 1) * ligColsCap with hrow0
  set row1 := (oodSamples * (lvl + 1) + 1) * ligColsCap with hrow1
  set o0 := osMatS c.plan osOodz row0 s1 with ho0
  set q := o0.2.2.k with hq
  set s2 : OsSt := { o0.2.2 with k := q + 5 } with hs2
  set o1 := osMatS c.plan osOodz row1 s2 with ho1
  set t := o1.2.2.k with ht
  set S1 := omState cap msg none with hS1
  set spf := spfRets cap msg lv.logCols with hspf'
  set spr := spRets cap msg lv.logCols with hspr
  set S := commitS cap msg lv.logCols y0 y1 nq with hS
  have hr0 : row0 < u128Bound := lt_of_le_of_lt (by rw [hrow0, hrow1]; unfold ligColsCap; omega) hoff
  have k36 : 36 ≤ k := hsf.k
  have kr : k + 2 ≤ r := osCurS_k s0
  have kq : r + 10 ≤ q := osMatS_k c.plan osOodz row0 s1
  have kt : q + 5 ≤ t := osMatS_k c.plan osOodz row1 s2
  have pcu : cu.2.1 < r := osMat_ptr_lt _ _ _ (show st.cb < k + 2 by have := hsf.below.cb; omega)
  have po0 : o0.2.1 < q := osMatS_ptr_lt _ _ _ _ (show 29 < r + 10 by omega)
  have po1 : o1.2.1 < t := osMatS_ptr_lt _ _ _ _ (show 29 < q + 5 by omega)
  have hmb1 : MatsBelow s1.k s1.mats := show MatsBelow (r + 10) st.mats from fun m hm ↦ by
    obtain ⟨a, b, d⟩ := hsf.below.mats m hm; exact ⟨by omega, by omega, by omega⟩
  -- the heap and the cursor
  have b1 := BlkA.seq (H := H) (show k ≤ k + 2 by omega) kr (heap_blk σ (2 + lv.folds) k pS)
    (B := cu.1) (OutB := fun σ' ↦ σ' (.n cu.2.1) = σ (.n st.cb) * gen ^ st.co) fun σ1 ha1 _ ↦ by
      have hc := osCurS_blkA (H := H) (st := s0) σ1 (show st.cb < k + 2 by have := hsf.below.cb; omega)
        hsf.co
      rw [ha1 st.cb hsf.below.cb] at hc
      exact hc
  -- the message and the root
  have b2 := BlkA.seq (H := H) (le_trans (by omega) kr) (show r ≤ r + 8 by omega) b1
    (B := [.call ("opening_message__L" ++ natStr (2 + lv.folds) ++ "_L0")
      ((st.fs ++ [cu.2.1, k + 1]).map V.n) (osRun r 8)])
    (OutB := fun σ' ↦ ∀ j < 8, σ' (.n (r + j)) = (omRets cap msg none cur (2 + lv.folds)).getD j 0)
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
  have b3 := BlkA.seq (H := H) (show k ≤ r + 8 by omega) (show r + 8 ≤ r + 10 by omega) b2
    (B := [osLd (r + 8) (k + 1) 0, osLd (r + 8) osRoots (2 * lvl + 2), osLd (r + 9) (k + 1) 1,
      osLd (r + 9) osRoots (2 * lvl + 3)])
    (OutB := fun σ' ↦ σ' (.n (r + 8)) = x0 ∧ σ' (.n (r + 9)) = x1) fun σ1 ha1 ho1 ↦ by
      refine ⟨lstF (r + 8) [x0, x1], fun C rd hH σ' ha hr' ↦ ?_⟩
      have v0 := lstF_at hr' (by simp) 0 (by simp)
      have v1 := lstF_at hr' (by simp) 1 (by simp)
      simp only [List.getD_cons_zero, List.getD_cons_succ, Nat.add_zero] at v0 v1
      rw [show r + 8 + 1 = r + 9 by omega] at v1
      obtain ⟨⟨⟨-, e1⟩, -⟩, -⟩ := ho1 C rd hH
      obtain ⟨l0, l1, l2, l3⟩ := hsent C rd hH
      have ep : σ' (.n (k + 1)) = pS := by rw [ha _ (by omega), e1]
      have er : σ' (.n osRoots) = σ (.n osRoots) := by
        rw [ha _ (show 17 < r + 8 by omega), ha1 _ (by show 17 < k; omega)]
      refine ⟨?_, v0, v1⟩
      simp only [allOk_cons, allOk_nil, and_true, stmtOk_atom, holds_load, osLd, ep, er, v0, v1]
      exact ⟨l0, l2, l1, l3⟩
  -- the out-of-domain points
  have b4 := BlkA.seq (H := H) (show k ≤ r + 10 by omega) kq b3 (B := o0.1)
    (OutB := fun σ' ↦ σ' (.n o0.2.1) = σ (.n osOodz) * gen ^ row0 ∧ MatsOk σ' o0.2.2.mats ∧
      MatsBelow o0.2.2.k o0.2.2.mats) fun σ1 ha1 _ ↦ by
      have h := osMatS_blkA (H := H) (P := c.plan) (base := osOodz) (off := row0) (s := s1) σ1
        (show 29 < r + 10 by omega) hmb1 (fun C rd hH ↦
          matsOk_agree (hok C rd hH).mats hsf.below.mats fun i hi ↦ ha1 i hi) hr0
      rw [ha1 osOodz (by show 29 < k; omega)] at h
      exact h
  have b5 := BlkA.seq (H := H) (show k ≤ q by omega) (show q ≤ q + 5 by omega) b4
    (B := [.call ("squeeze_point_from__L" ++ natStr lv.logCols)
      ([r + 2, r + 3, r + 4, r + 5, r + 6, r, o0.2.1].map V.n) (osRun q 5)])
    (OutB := fun σ' ↦ ∀ j < 5, σ' (.n (q + j)) = spf.getD j 0) fun σ1 ha1 ho1 ↦ by
      refine call_blk _ (spfRets_length _ _ _) (fun i hi ↦ ?_) fun C rd hH ↦ ?_
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
        rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega
      · obtain ⟨⟨⟨-, e2⟩, -⟩, eo, -⟩ := ho1 C rd hH
        have e : ∀ j < 8, σ1 (.n (r + j)) = (omRets cap msg none cur (2 + lv.folds)).getD j 0 := e2
        have hargs : [r + 2, r + 3, r + 4, r + 5, r + 6, r, o0.2.1].map (fun i ↦ σ1 (.n i)) =
            capOf S1 ++ [cellsOfState S1 false 0, σ (.n osOodz) * gen ^ row0] := by
          simp only [List.map_cons, List.map_nil]
          rw [e 2 (by omega), e 3 (by omega), e 4 (by omega), e 5 (by omega), e 6 (by omega),
            show r = r + 0 from rfl, e 0 (by omega), eo]
          simp [omRets, capOf, hS1]
        rw [hargs]
        exact hspf C rd hH
  have b6 := BlkA.seq (H := H) (show k ≤ q + 5 by omega) kt b5 (B := o1.1)
    (OutB := fun σ' ↦ σ' (.n o1.2.1) = σ (.n osOodz) * gen ^ row1 ∧ MatsOk σ' o1.2.2.mats ∧
      MatsBelow o1.2.2.k o1.2.2.mats) fun σ1 ha1 ho1 ↦ by
      have hmb2 : MatsBelow s2.k s2.mats := show MatsBelow (q + 5) o0.2.2.mats from fun m hm ↦ by
        obtain ⟨a, b, d⟩ := osMatS_below (P := c.plan) (off := row0) hmb1
          (show 29 < r + 10 by omega) m hm
        exact ⟨by have : m.out < q := a; omega, by have : m.src < q := b; omega, by have : m.base < q := d; omega⟩
      have h := osMatS_blkA (H := H) (P := c.plan) (base := osOodz) (off := row1) (s := s2) σ1
        (show 29 < q + 5 by omega) hmb2 (fun C rd hH ↦ (ho1 C rd hH).1.2.2.1) hoff
      rw [ha1 osOodz (by show 29 < k; omega)] at h
      exact h
  have b7 := BlkA.seq (H := H) (show k ≤ t by omega) (show t ≤ t + 5 by omega) b6
    (B := [.call ("squeeze_point__L" ++ natStr lv.logCols)
      ([q, q + 1, q + 2, q + 3, q + 4, o1.2.1].map V.n) (osRun t 5)])
    (OutB := fun σ' ↦ ∀ j < 5, σ' (.n (t + j)) = spr.getD j 0) fun σ1 ha1 ho1 ↦ by
      refine call_blk _ (spRets_length _ _ _) (fun i hi ↦ ?_) fun C rd hH ↦ ?_
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
        rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;> omega
      · obtain ⟨⟨-, e5⟩, eo, -⟩ := ho1 C rd hH
        have e : ∀ j < 5, σ1 (.n (q + j)) = spf.getD j 0 := e5
        have hargs : [q, q + 1, q + 2, q + 3, q + 4, o1.2.1].map (fun i ↦ σ1 (.n i)) =
            spf ++ [σ (.n osOodz) * gen ^ row1] := by
          simp only [List.map_cons, List.map_nil]
          rw [show q = q + 0 from rfl, e 0 (by omega), e 1 (by omega), e 2 (by omega),
            e 3 (by omega), e 4 (by omega), eo]
          conv_rhs => rw [five_getD (show spf.length = 5 from spfRets_length _ _ _)]
          rfl
        rw [hargs]
        exact hsp C rd hH
  -- the values, the nonce and its permutation
  have b8 := BlkA.seq (H := H) (show k ≤ t + 5 by omega) (show t + 5 ≤ t + 23 by omega) b7
    (B := ((List.range 5).map fun i ↦ osCp (t + 5 + i) (t + i)) ++ osOodNext (r + 7) 0 (t + 10) ++
      osOodNext (r + 7) 1 (t + 10 + 4) ++
      [osLd (t + 10 + 8) (r + 7) 2, osCp (t + 10 + 9) (t + 10 + 8), osCst (t + 10 + 10) (word 0 4),
        osCst (t + 10 + 11) (word 0 0), osCst (t + 10 + 12) (word 0 0)])
    (OutB := fun σ' ↦ ∀ j < 18, σ' (.n (t + 5 + j)) = (oodVals spr y0 y1 nq).getD j 0)
    fun σ1 ha1 ho1 ↦ by
      have hsl : spr.length = 5 := spRets_length _ _ _
      refine ⟨lstF (t + 5) (oodVals spr y0 y1 nq), fun C rd hH σ' ha hr' ↦ ?_⟩
      have hv : ∀ j < 18, σ' (.n (t + 5 + j)) = (oodVals spr y0 y1 nq).getD j 0 := fun j hj ↦
        lstF_at hr' (by simp [oodVals, hsl]) j (by simp [oodVals, hsl]; omega)
      refine ⟨?_, hv⟩
      obtain ⟨⟨⟨⟨⟨⟨⟨-, -⟩, e2⟩, -⟩, -⟩, -⟩, -⟩, e7⟩ := ho1 C rd hH
      have hs : ∀ j < 5, σ' (.n (t + j)) = spr.getD j 0 := fun j hj ↦ by
        rw [ha _ (by omega)]; exact e7 j hj
      have hcb : σ' (.n (r + 7)) = cur * gen ^ (2 + lv.folds) := by
        rw [ha _ (by omega), e2 7 (by omega)]; simp [omRets, capOf]
      have hys' := hys C rd hH
      have l0 : LoadHolds rd (σ' (.n (r + 7))) 0 y0 := by rw [hcb]; exact hys' 0 (by simp)
      have l1 : LoadHolds rd (σ' (.n (r + 7))) 1 y1 := by rw [hcb]; exact hys' 1 (by simp)
      have l2 : LoadHolds rd (σ' (.n (r + 7))) 2 nq := by rw [hcb]; exact hys' 2 (by simp)
      have w : ∀ j, 5 ≤ j → j < 23 → σ' (.n (t + j)) = (oodVals spr y0 y1 nq).getD (j - 5) 0 :=
        fun j h1 h2 ↦ by
          have := hv (j - 5) (by omega)
          rwa [show t + 5 + (j - 5) = t + j by omega] at this
      simp only [List.range_succ, List.range_zero, List.map_cons, List.map_nil, List.nil_append, osOodNext,
        List.cons_append, allOk_cons, allOk_nil, and_true, stmtOk_atom,
        holds_copy, holds_load, holds_const, osCp, osLd, osCst, Nat.add_assoc, Nat.reduceAdd]
      simp (disch := omega) only [w, hs, Nat.reduceSub, oodVals]
      simp (disch := simp [hsl]) only [List.getD_append, List.getD_append_right, hsl, Nat.reduceSub,
        List.getD_cons_zero, List.getD_cons_succ]
      exact ⟨trivial, trivial, trivial, trivial, trivial, l0, trivial, trivial, trivial, l1, trivial,
        trivial, trivial, l2, trivial, trivial, trivial, trivial⟩
  have b9 := BlkA.seq (H := H) (show k ≤ t + 23 by omega) (show t + 23 ≤ t + 10 + 13 + 13 by omega) b8
    (B := [osKeccak [t + 10 + 1, t + 10 + 2, t + 10 + 5, t + 10 + 6, t + 10 + 9, t + 10 + 10,
      t + 10 + 11, t + 10 + 12, t + 5, t + 6, t + 7, t + 8, t + 9] (t + 10 + 13)])
    (OutB := fun σ' ↦ ∀ j < 13, σ' (.n (t + 10 + 13 + j)) = rdCell S j) fun σ1 ha1 ho1 ↦ by
      have hsl : spr.length = 5 := spRets_length _ _ _
      refine keccak_blk ⟨spr, [(y0, dsObserve), (y1, dsObserve), (nq, dsPowNonce)]⟩ (by simp)
        (by simp) (fun i hi ↦ by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
          rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
            omega) (fun C rd hH ↦ ?_) |>.mono fun σ' h j hj ↦ by
        rw [h j hj, hS, commitS, commitS_eq]
      obtain ⟨-, e8⟩ := ho1 C rd hH
      have w : ∀ j, 5 ≤ j → j < 23 → σ1 (.n (t + j)) = (oodVals spr y0 y1 nq).getD (j - 5) 0 :=
        fun j h1 h2 ↦ by
          have := e8 (j - 5) (by omega)
          rwa [show t + 5 + (j - 5) = t + j by omega] at this
      simp only [List.map_cons, List.map_nil, Nat.add_assoc, Nat.reduceAdd]
      simp (disch := omega) only [w, Nat.reduceSub]
      simp (disch := simp [hsl]) only [oodVals, List.getD_append, List.getD_append_right, hsl,
        Nat.reduceSub, List.getD_cons_zero, List.getD_cons_succ]
      conv_rhs => rw [five_getD hsl]
      simp [pendCells, Keccak.scalarCells, dsObserve, dsPowNonce, word]
      exact ⟨rfl, rfl, word_zero⟩
  have ek : (osCommit c lvl lv st).2.k = t + 10 + 13 + 13 := rfl
  rw [ek]
  refine BlkA.congr (BlkA.monoH b9.agree fun C rd hH σ' ha ⟨ho, hag⟩ ↦ ?_) (by
    simp only [osCommit, List.append_assoc, List.cons_append, List.nil_append]; rfl)
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨eh0, eh1⟩, -⟩, e2⟩, -⟩, -⟩, -⟩, -, hm1, hb1⟩, -⟩, e8⟩, e9⟩ := ho
  have hok' := hok C rd hH
  have hsl : spr.length = 5 := spRets_length _ _ _
  have w : ∀ j, 5 ≤ j → j < 23 → σ' (.n (t + j)) = (oodVals spr y0 y1 nq).getD (j - 5) 0 :=
    fun j h1 h2 ↦ by
      have := e8 (j - 5) (by omega)
      rwa [show t + 5 + (j - 5) = t + j by omega] at this
  have c9 : ∀ j < 13, σ' (.n (t + (23 + j))) = rdCell S j := fun j hj ↦ by
    rw [show t + (23 + j) = t + 10 + 13 + j by omega]; exact e9 j hj
  have ekk : ∀ m, m + 4 < st.k → m + 4 < t + 10 + 13 + 13 := fun m h ↦ by omega
  refine ⟨⟨⟨⟨rfl, ⟨?_, ?_, ?_, ?_⟩, by show 3 < u128Bound; unfold u128Bound; omega, fun p hp ↦ ekk p
    (hsf.padB p hp), by omega⟩, hm1, ?_⟩, by omega, hag⟩, ?_, ?_, ?_, rfl, ?_, ?_, ?_, eh0, ?_, rfl, rfl⟩
  · intro f hf
    have hf' : f ∈ [t + 10 + 21, t + 10 + 22, t + 10 + 23, t + 10 + 24, t + 10 + 25] := hf
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hf'
    rcases hf' with rfl | rfl | rfl | rfl | rfl <;> omega
  · show r + 7 < t + 10 + 13 + 13; omega
  · show st.claim < t + 10 + 13 + 13; have := hsf.below.claim; omega
  · intro m hm; obtain ⟨a, b, d⟩ := hb1 m hm
    exact ⟨by have : m.out < t := a; omega, by have : m.src < t := b; omega,
      by have : m.base < t := d; omega⟩
  · intro p hp
    have hb := hsf.padB p hp
    obtain ⟨z1, z2, z3, z4⟩ := hok'.pad p hp
    rw [ha _ (by omega), ha _ (by omega), ha _ (by omega), ha _ (by omega)]
    exact ⟨z1, z2, z3, z4⟩
  · show (⟨[t + 10 + 21, t + 10 + 22, t + 10 + 23, t + 10 + 24, t + 10 + 25].map
      (fun i ↦ σ' (.n i)), []⟩ : Fs) = _
    simp only [List.map_cons, List.map_nil, Nat.add_assoc, Nat.reduceAdd]
    rw [c9 8 (by omega), c9 9 (by omega), c9 10 (by omega), c9 11 (by omega), c9 12 (by omega)]
    simp only [capOf, ← rdCell_eq]
    rfl
  · show σ' (.n (t + 10 + 13)) = _
    rw [show t + 10 + 13 = t + (23 + 0) by omega, c9 0 (by omega)]
  · show σ' (.n (t + 10 + 14)) = _
    rw [show t + 10 + 14 = t + (23 + 1) by omega, c9 1 (by omega)]
  · show σ' (.n (t + 10 + 3)) = y0
    rw [show t + 10 + 3 = t + 13 by omega, w 13 (by omega) (by omega)]
    simp (disch := simp [hsl]) [oodVals, hsl]
  · show σ' (.n (t + 10 + 7)) = y1
    rw [show t + 10 + 7 = t + 17 by omega, w 17 (by omega) (by omega)]
    simp (disch := simp [hsl]) [oodVals, hsl]
  · show σ' (.n (k + 1)) = pS; exact eh1
  · simp only [OsSt.cur]
    show σ' (.n (r + 7)) * gen ^ 3 = _
    rw [e2 7 (by omega)]
    simp [omRets, capOf, hcur]

end
end LeanVM.Guest.B1.Whir
