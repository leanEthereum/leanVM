/-
  LeanVM.Guest.B1.VsC.RoundsMainA

  `link_rounds` completes placed, from its loop's and last arms' placed completeness.
-/

module

public import LeanVM.Guest.B1.VsC.RoundsLoopA
public import LeanVM.Guest.B1.VsC.RoundsLastA
public import LeanVM.Guest.B1.VsC.SqueezePackedA
public import LeanVM.Guest.B1.VsC.LinkCalleesA
public import LeanVM.Guest.B1.VsC.CalleesB
import LeanVM.Guest.CoreRef

/-!
# `link_rounds`, placed

`link_rounds__L{nt}_L{bits}(fs0..fs4, cursor, claim, point, g^n, tabs)`, `n < 64`, placed at frame
`fp`, its cursor `c` right after: `n = 4 q + r` from six hinted bits, its records buffer of `7 (q + 2)`
words at `c` (its own words `lrWords`: record `m ≤ q` the state after `4 m` rounds, then the state
after all `n`), the loop over the `q` records (entered when `q ≠ 0`), the last arm on the `r` rounds
left, the state after them read back. One valuation fixed before the memory (`lrVals`), by
`callAtA_node`. `lr_main_placed` takes the loop's and the last arms' placed completeness as
hypotheses (`LrLoopA`, `LrLastA`), discharged with no grind by `lrL_callAtA0`, `lrl_placed0` and
`lrl0_placed` (`link_rounds_L{1,6,7}_L0_completeA`).

The chain's cursors advance by `rlen` a round (`CurChain`, a consequence of `RoundChain` that reads
no memory), so the stream words the rounds read lie in the cursor's run of `nw` words; a chain whose
cursors do not advance so has no `RoundChain`, and the statement is vacuous there.
-/

namespace LeanVM.Guest.B1.VsC

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Memory LeanVM.Guest.B1
open LeanVM.Guest.B1.Link LeanVM.Guest.Complete LeanVM.Guest.B1.Fwd LeanVM.Protocol.Verifier
open LeanVM.Guest.Value
open LeanVM.Prover.Exec (allocBase bitWord)

@[expose] public section

/-! ## Cursors -/

/-- The chain's cursors advance by `rlen` a round. -/
def CurChain (nt bits : ℕ) : RSt → List (E × RSt) → Prop
  | _, [] => True
  | st, (_, st') :: l => st'.cur = st.cur * gen ^ rlen nt bits ∧ CurChain nt bits st' l

theorem roundChain_curChain {rd : Reader} {nt bits : ℕ} : ∀ {st : RSt} {l : List (E × RSt)},
    RoundChain rd nt bits st l → CurChain nt bits st l
  | _, [], _ => trivial
  | _, (_, _) :: _, ⟨hs, h⟩ => ⟨roundStep_cur hs, roundChain_curChain h⟩

theorem curChain_cur {nt bits : ℕ} : ∀ (st : RSt) (l : List (E × RSt)), CurChain nt bits st l →
    ∀ r ≤ l.length, (chainLast st (l.take r)).cur = st.cur * gen ^ (r * rlen nt bits)
  | st, [], _, r, hr => by
    obtain rfl : r = 0 := by simpa using hr
    simp [chainLast]
  | st, (y, st') :: l, ⟨hs, hc⟩, r, hr => by
    rcases r with _ | r
    · simp [chainLast]
    · simp only [List.take_succ_cons, chainLast]
      rw [curChain_cur st' l hc r (by simpa using hr), hs, mul_assoc, ← pow_add]
      congr 2; ring

theorem curChain_drop {nt bits : ℕ} : ∀ (st : RSt) (l : List (E × RSt)) (m : ℕ), CurChain nt bits st l →
    CurChain nt bits (chainLast st (l.take m)) (l.drop m)
  | _, [], _, _ => by simp [CurChain]
  | _, _ :: _, 0, h => h
  | _, (_, st') :: l, m + 1, ⟨_, h⟩ => curChain_drop st' l m h

theorem gen_pow_mod (m : ℕ) : gen ^ m = gen ^ (m % ordG) := by
  conv_lhs => rw [← Nat.mod_add_div m ordG, pow_add, pow_mul, gen_pow_ordG, one_pow, mul_one]

/-- **The words read lie in the cursor's run**: a chain of `n` rounds from `cur ≠ 0` ending at
`cur·g^nw` consumes at most `nw` words. -/
theorem chain_words_le {nt bits : ℕ} {st : RSt} {l : List (E × RSt)} (hc : CurChain nt bits st l)
    (h0 : st.cur ≠ 0) {nw : ℕ} (hnw : (chainLast st l).cur = st.cur * gen ^ nw) (hl : l.length < 64)
    (hnt : nt ≤ 32) : l.length * rlen nt bits ≤ nw := by
  have h1 := curChain_cur st l hc l.length le_rfl
  rw [List.take_length, hnw] at h1
  have h2 := mul_left_cancel₀ h0 h1
  rw [gen_pow_mod nw] at h2
  have hb : l.length * rlen nt bits < ordG := by
    have h34 : rlen nt bits ≤ 34 := by unfold rlen; split <;> omega
    have : l.length * rlen nt bits ≤ 64 * 34 := Nat.mul_le_mul (by omega) h34
    unfold ordG; omega
  have := gen_pow_inj (Nat.mod_lt _ (by norm_num)) hb h2
  have := Nat.mod_le nw ordG
  omega

/-! ## The callees' statements -/

/-- What the loop reads and writes of its caller's. -/
def LrLPreB (nt bits : ℕ) (st0 : RSt) (l : List (E × RSt)) (q cm : ℕ) (point tabs : E) (rd : Reader) : Prop :=
  (bits ≠ 0 → WinTabs rd tabs) ∧ RoundChain rd nt bits st0 l ∧ ReadsAt rd point (l.map Prod.fst) ∧
    ∀ m ≤ q, ReadsAt rd (ptrAt (cm + 7 * m)) (lrRec st0 l m).cells

/-- **`link_rounds`' loop completes placed** from its first iteration. -/
def LrLoopA (fs : String → ℕ) (al : String → Bool) (cert : String → V → ℕ) (k nt bits : ℕ) (name : String) :
    Prop :=
  ∀ (st0 : RSt) (l : List (E × RSt)) (q cm : ℕ) (point tabs : E) (R : ℕ → Prop), st0.cap.length = 5 →
    4 * q ≤ l.length → q < 16 → 0 < q →
    (∀ t < l.length, ∃ i, point.limb 0 * addressOfIndex t = addressOfIndex i ∧ R i) →
    (∀ t < l.length * rlen nt bits, ∃ i, st0.cur.limb 0 * addressOfIndex t = addressOfIndex i ∧ R i) →
    (∀ i, cm ≤ i → i < cm + 7 * (q + 2) → R i) →
    (bits ≠ 0 → ∀ t < 2 ^ winTabBits, ∃ i, tabs.limb 0 * addressOfIndex t = addressOfIndex i ∧ R i) →
    ∀ fp c, fp + lrBlock fs name q ≤ c →
      CallAtA fs al cert k name [gen ^ 0, gen ^ q, ptrAt cm, point, tabs] [] R (fun _ => False) (fun _ => True)
        (LrLPreB nt bits st0 l q cm point tabs) PostQuiet (lrBlock fs name q) fp c c

/-- **`link_rounds_last__L{nt}_L{bits}_L{r}` completes placed.** -/
def LrLastA (fs : String → ℕ) (al : String → Bool) (cert : String → V → ℕ) (k nt bits : ℕ) (name : String)
    (r : ℕ) : Prop :=
  ∀ (R : ℕ → Prop) (rp out pts tabs : E) (st : RSt) (l : List (E × RSt)), st.cap.length = 5 → l.length = r →
    (∀ off < 7, ∃ i, rp.limb 0 * addressOfIndex off = addressOfIndex i ∧ R i) →
    (∀ off < 7, ∃ i, out.limb 0 * addressOfIndex off = addressOfIndex i ∧ R i) →
    (∀ off < r, ∃ i, pts.limb 0 * addressOfIndex off = addressOfIndex i ∧ R i) →
    (∀ t < r * rlen nt bits, ∃ i, st.cur.limb 0 * addressOfIndex t = addressOfIndex i ∧ R i) →
    (bits ≠ 0 → ∀ t < 2 ^ winTabBits, ∃ i, tabs.limb 0 * addressOfIndex t = addressOfIndex i ∧ R i) →
    ∀ fp c, CallAtA fs al cert k name [rp, out, pts, tabs] [0] R (fun _ => False) (fun _ => True)
      (fun rd ↦ ReadsAt rd rp st.cells ∧ (bits ≠ 0 → WinTabs rd tabs) ∧ RoundChain rd nt bits st l ∧
        ReadsAt rd pts (l.map Prod.fst) ∧ ReadsAt rd out (chainLast st l).cells)
      PostQuiet (fs name) fp c c

/-! ## The template -/

/-- `link_rounds`' statements before its dispatch. -/
def lrMPre (loop : String) : List Stmt :=
  [.atom (.hint (.bitsExp (.n 8) 6 (.stack [.n 10, .n 11, .n 12, .n 13, .n 14, .n 15]))),
    .atom (.mul (.n 10) (.n 10) (.n 10)),
    .atom (.const (.n 16) (word 1 0)),
    .atom (.const (.n 17) (word 3 0)),
    .atom (.mul (.n 18) (.n 10) (.n 17)),
    .atom (.add (.n 19) (.n 16) (.n 18)),
    .atom (.mul (.n 11) (.n 11) (.n 11)),
    .atom (.const (.n 20) (word 1 0)),
    .atom (.const (.n 21) (word 5 0)),
    .atom (.mul (.n 22) (.n 11) (.n 21)),
    .atom (.add (.n 23) (.n 20) (.n 22)),
    .atom (.mul (.n 24) (.n 19) (.n 23)),
    .atom (.mul (.n 12) (.n 12) (.n 12)),
    .atom (.const (.n 25) (word 1 0)),
    .atom (.const (.n 26) (word 3 0)),
    .atom (.mul (.n 27) (.n 12) (.n 26)),
    .atom (.add (.n 28) (.n 25) (.n 27)),
    .atom (.mul (.n 13) (.n 13) (.n 13)),
    .atom (.const (.n 29) (word 1 0)),
    .atom (.const (.n 30) (word 5 0)),
    .atom (.mul (.n 31) (.n 13) (.n 30)),
    .atom (.add (.n 32) (.n 29) (.n 31)),
    .atom (.mul (.n 33) (.n 28) (.n 32)),
    .atom (.mul (.n 14) (.n 14) (.n 14)),
    .atom (.const (.n 34) (word 1 0)),
    .atom (.const (.n 35) (word 17 0)),
    .atom (.mul (.n 36) (.n 14) (.n 35)),
    .atom (.add (.n 37) (.n 34) (.n 36)),
    .atom (.mul (.n 38) (.n 33) (.n 37)),
    .atom (.mul (.n 15) (.n 15) (.n 15)),
    .atom (.const (.n 39) (word 1 0)),
    .atom (.const (.n 40) (word 257 0)),
    .atom (.mul (.n 41) (.n 15) (.n 40)),
    .atom (.add (.n 42) (.n 39) (.n 41)),
    .atom (.mul (.n 43) (.n 38) (.n 42)),
    .atom (.mul (.n 44) (.n 43) (.n 43)),
    .atom (.mul (.n 45) (.n 44) (.n 44)),
    .atom (.mul (.n 46) (.n 45) (.n 24)),
    .atom (.assertEq (.n 46) (.n 8)),
    .atom (.const (.n 47) (word 4 0)),
    .atom (.mul (.n 48) (.n 43) (.n 47)),
    .atom (.mul (.n 49) (.n 48) (.n 48)),
    .atom (.mul (.n 50) (.n 49) (.n 48)),
    .atom (.mul (.n 51) (.n 50) (.n 50)),
    .atom (.mul (.n 52) (.n 51) (.n 48)),
    .atom (.hint (.allocDyn (.n 53) (.n 52))),
    .atom (.load (.n 0) (.n 53) 0),
    .atom (.load (.n 1) (.n 53) 1),
    .atom (.load (.n 2) (.n 53) 2),
    .atom (.load (.n 3) (.n 53) 3),
    .atom (.load (.n 4) (.n 53) 4),
    .atom (.load (.n 5) (.n 53) 5),
    .atom (.load (.n 6) (.n 53) 6),
    .atom (.const (.n 54) (word 1 0)),
    .atom (.add (.n 55) (.n 54) (.n 43)),
    .atom (.const (.n 56) (word 1 0)),
    .callIf (.n 55) loop [.n 56, .n 43, .n 53, .n 7, .n 9],
    .atom (.mul (.n 57) (.n 43) (.n 43)),
    .atom (.mul (.n 58) (.n 57) (.n 43)),
    .atom (.mul (.n 59) (.n 58) (.n 58)),
    .atom (.mul (.n 60) (.n 59) (.n 43)),
    .atom (.mul (.n 61) (.n 53) (.n 60)),
    .atom (.const (.n 62) (word 128 0)),
    .atom (.mul (.n 63) (.n 61) (.n 62)),
    .atom (.mul (.n 64) (.n 43) (.n 43)),
    .atom (.mul (.n 65) (.n 64) (.n 64)),
    .atom (.mul (.n 66) (.n 7) (.n 65))]

/-- After the dispatch: the state after the rounds read back. -/
def lrMPost : List Stmt :=
  [.atom (.load (.n 68) (.n 61) 7),
    .atom (.load (.n 69) (.n 61) 8),
    .atom (.load (.n 70) (.n 61) 9),
    .atom (.load (.n 71) (.n 61) 10),
    .atom (.load (.n 72) (.n 61) 11),
    .atom (.load (.n 73) (.n 61) 12),
    .atom (.load (.n 74) (.n 61) 13)]

theorem lrMain_eq (loop : String) (lasts : List String) :
    lrMainBody loop lasts = lrMPre loop ++ .dispatch (.n 24) lasts [.n 61, .n 63, .n 66, .n 9] [.n 67] ::
      (lrMPost ++ [.ret [.n 68, .n 69, .n 70, .n 71, .n 72, .n 73, .n 74]]) := rfl

theorem lrMPre_straight (loop : String) : (lrMPre loop).all Stmt.straight = true := rfl
theorem lrMPost_straight : lrMPost.all Stmt.straight = true := rfl
theorem lrMPre_allocSz (loop : String) : (lrMPre loop).filterMap Stmt.allocSz = [(.n 53, .inr (.n 52))] := rfl
theorem lrMPre_addrS (loop : String) : (lrMPre loop).filterMap Stmt.addrS = [] := rfl
theorem lrMPre_callS (loop : String) :
    (lrMPre loop).filterMap Stmt.callS = [(some (.n 55), loop, [.n 56, .n 43, .n 53, .n 7, .n 9], [])] := rfl
theorem lrMPost_allocSz : lrMPost.filterMap Stmt.allocSz = [] := rfl
theorem lrMPost_addrS : lrMPost.filterMap Stmt.addrS = [] := rfl
theorem lrMPost_callS : lrMPost.filterMap Stmt.callS = [] := rfl
theorem lrMPre_loads (loop : String) : (lrMPre loop).filterMap stmtLoad? =
    [(.n 53, 0), (.n 53, 1), (.n 53, 2), (.n 53, 3), (.n 53, 4), (.n 53, 5), (.n 53, 6)] := rfl
theorem lrMPost_loads : lrMPost.filterMap stmtLoad? =
    [(.n 61, 7), (.n 61, 8), (.n 61, 9), (.n 61, 10), (.n 61, 11), (.n 61, 12), (.n 61, 13)] := rfl
theorem lrMPre_quiet (loop : String) : (lrMPre loop).all stmtQuietB = true := rfl
theorem lrMPost_quiet : lrMPost.all stmtQuietB = true := rfl
theorem lrMPre_noComputed (loop : String) : (lrMPre loop).tail.all noComputedB = true := rfl
theorem lrMPost_noComputed : lrMPost.all noComputedB = true := rfl
theorem lrMPre_noHeap (loop : String) : (lrMPre loop).all noHeapHintB = true := rfl
theorem lrMPost_noHeap : lrMPost.all noHeapHintB = true := rfl

/-- `link_rounds`' valuation: the arguments, the count's bits, the records at `c`, the state after. -/
def lrVals (f0 f1 f2 f3 f4 cur cl point tabs : E) (l : List (E × RSt)) (c : ℕ) (fin : List E) : List E :=
  let b0 : E := bitWord (l.length.testBit 0)
  let b1 : E := bitWord (l.length.testBit 1)
  let b2 : E := bitWord (l.length.testBit 2)
  let b3 : E := bitWord (l.length.testBit 3)
  let b4 : E := bitWord (l.length.testBit 4)
  let b5 : E := bitWord (l.length.testBit 5)
  let v16 := word 1 0
  let v17 := word 3 0
  let v18 := b0 * v17
  let v19 := v16 + v18
  let v20 := word 1 0
  let v21 := word 5 0
  let v22 := b1 * v21
  let v23 := v20 + v22
  let v24 := v19 * v23
  let v25 := word 1 0
  let v26 := word 3 0
  let v27 := b2 * v26
  let v28 := v25 + v27
  let v29 := word 1 0
  let v30 := word 5 0
  let v31 := b3 * v30
  let v32 := v29 + v31
  let v33 := v28 * v32
  let v34 := word 1 0
  let v35 := word 17 0
  let v36 := b4 * v35
  let v37 := v34 + v36
  let v38 := v33 * v37
  let v39 := word 1 0
  let v40 := word 257 0
  let v41 := b5 * v40
  let v42 := v39 + v41
  let v43 := v38 * v42
  let v44 := v43 * v43
  let v45 := v44 * v44
  let v46 := v45 * v24
  let v47 := word 4 0
  let v48 := v43 * v47
  let v49 := v48 * v48
  let v50 := v49 * v48
  let v51 := v50 * v50
  let v52 := v51 * v48
  let v53 := ofK (addressOfIndex c)
  let v54 := word 1 0
  let v55 := v54 + v43
  let v56 := word 1 0
  let v57 := v43 * v43
  let v58 := v57 * v43
  let v59 := v58 * v58
  let v60 := v59 * v43
  let v61 := v53 * v60
  let v62 := word 128 0
  let v63 := v61 * v62
  let v64 := v43 * v43
  let v65 := v64 * v64
  let v66 := point * v65
  [f0, f1, f2, f3, f4, cur, cl, point, gen ^ l.length, tabs, b0, b1, b2, b3, b4, b5, v16, v17, v18, v19, v20, v21, v22, v23, v24, v25, v26, v27, v28, v29, v30, v31, v32, v33, v34, v35, v36, v37, v38, v39, v40, v41, v42, v43, v44, v45, v46, v47, v48, v49, v50, v51, v52, v53, v54, v55, v56, v57, v58, v59, v60, v61, v62, v63, v64, v65, v66, 0, fin.getD 0 0, fin.getD 1 0, fin.getD 2 0, fin.getD 3 0, fin.getD 4 0, fin.getD 5 0, fin.getD 6 0]

/-- `link_rounds`' own words: record `m ≤ q`, then the state after all the rounds. -/
def lrWords (st0 : RSt) (l : List (E × RSt)) : List E :=
  (List.range (7 * (l.length / 4 + 2))).map fun o =>
    if o / 7 ≤ l.length / 4 then (lrRec st0 l (o / 7)).cells.getD (o % 7) 0 else (chainLast st0 l).cells.getD (o % 7) 0

theorem lrWords_recs {rd : Reader} {st0 : RSt} {l : List (E × RSt)} {c : ℕ} (hch : ∃ nt bits, RoundChain rd nt bits st0 l)
    (h5 : st0.cap.length = 5) (h : ReadsAt rd (ptrAt c) (lrWords st0 l)) :
    (∀ m ≤ l.length / 4, ReadsAt rd (ptrAt (c + 7 * m)) (lrRec st0 l m).cells) ∧
      ReadsAt rd (ptrAt (c + 7 * (l.length / 4 + 1))) (chainLast st0 l).cells := by
  obtain ⟨nt, bits, hch⟩ := hch
  have hl7 : ∀ st : RSt, st.cap.length = 5 → st.cells.length = 7 := fun st h => by simp [RSt.cells, h]
  refine ⟨fun m hm => readsAt_shift fun i hi => ?_, readsAt_shift fun i hi => ?_⟩
  · rw [hl7 _ (lrRec_cap h5 hch m)] at hi
    have := h (7 * m + i) (by simp [lrWords]; omega)
    simp only [lrWords, List.getElem_map, List.getElem_range] at this
    rwa [show (7 * m + i) / 7 = m by omega, show (7 * m + i) % 7 = i by omega, ite_eq_left hm] at this
  · rw [hl7 _ (chainLast_cap_length h5 hch)] at hi
    have := h (7 * (l.length / 4 + 1) + i) (by simp [lrWords]; omega)
    simp only [lrWords, List.getElem_map, List.getElem_range] at this
    rwa [show (7 * (l.length / 4 + 1) + i) / 7 = l.length / 4 + 1 by omega,
      show (7 * (l.length / 4 + 1) + i) % 7 = i by omega,
      ite_eq_right (show ¬l.length / 4 + 1 ≤ l.length / 4 by omega)] at this

/-! ## Placed -/

variable {fs : String → ℕ} {al : String → Bool} {cert : String → V → ℕ}

set_option maxHeartbeats 4000000 in
/-- **`link_rounds` completes placed**, from its loop's and last arms', its end within `2^21` of its
cursor when every frame is below `2^16`. -/
theorem lr_main_placed {k nt bits : ℕ} (hnt : nt ≤ 32) {name loop : String} {lasts : List String} {fn : Fn}
    (hfind : coreProgram.find? name = some fn) (hlp : coreProgram.loop name = false)
    (hparams : fn.params = [.n 0, .n 1, .n 2, .n 3, .n 4, .n 5, .n 6, .n 7, .n 8, .n 9])
    (hbody : fn.body = lrMainBody loop lasts) (hll : lasts.length = 4) {loopFn : Fn}
    (hlf : coreProgram.find? loop = some loopFn) (hlpar : loopFn.params = [.n 0, .n 1, .n 2, .n 3, .n 4])
    (hloop : LrLoopA fs al cert k nt bits loop) (hlast : ∀ r < 4, LrLastA fs al cert k nt bits (lasts.getD r "") r) :
    LinkRoundsCompleteAE fs al cert k nt bits name (fun c e => FsSmall fs → e ≤ c + 2 ^ 21) := by
  intro f0 f1 f2 f3 f4 cur cl point tabs l nw fp hl64 hc0 hnw hpb
  set st0 : RSt := ⟨[f0, f1, f2, f3, f4], cur, cl⟩ with hst0
  have hs5 : st0.cap.length = 5 := rfl
  set c := fp + fs name with hc
  set n := l.length with hn
  set q := n / 4 with hq
  set r := n % 4 with hr
  have hpqr : n = 4 * q + r := by omega
  have hq16 : q < 16 := by omega
  have hr4 : r < 4 := by omega
  -- the vacuous cases: no chain from `st0`
  by_cases hcc : CurChain nt bits st0 l
  swap
  · exact ⟨c, fun _ => Nat.le_add_right _ _, [], ⟨by simp, List.Pairwise.nil⟩, le_rfl, fun _ _ => trivial,
      fun rd _ _ hP => absurd (roundChain_curChain hP.2.1) hcc⟩
  by_cases h5 : (chainLast st0 l).cap.length = 5
  swap
  · exact ⟨c, fun _ => Nat.le_add_right _ _, [], ⟨by simp, List.Pairwise.nil⟩, le_rfl, fun _ _ => trivial,
      fun rd _ _ hP => absurd (chainLast_cap_length rfl hP.2.1) h5⟩
  by_cases h5q : (lrRec st0 l q).cap.length = 5
  swap
  · exact ⟨c, fun _ => Nat.le_add_right _ _, [], ⟨by simp, List.Pairwise.nil⟩, le_rfl, fun _ _ => trivial,
      fun rd _ _ hP => absurd (lrRec_cap hs5 hP.2.1 q) h5q⟩
  obtain ⟨hb1, hb2⟩ := bits64 n hl64
  have hnwle : n * rlen nt bits ≤ nw := chain_words_le hcc hc0 hnw hl64 hnt
  set fin := (chainLast st0 l).cells with hfin
  set σ : Val := fun v => (lrVals f0 f1 f2 f3 f4 cur cl point tabs l c fin).getD v.idx 0 with hσ
  -- the values
  have w3 : word 3 0 = gen ^ 1 + 1 := word_two_pow_xor_one (a := 1) (by norm_num)
  have w5 : word 5 0 = gen ^ 2 + 1 := word_two_pow_xor_one (a := 2) (by norm_num)
  have w17 : word 17 0 = gen ^ 4 + 1 := word_two_pow_xor_one (a := 4) (by norm_num)
  have w257 : word 257 0 = gen ^ 8 + 1 := word_two_pow_xor_one (a := 8) (by norm_num)
  have h24 : σ (.n 24) = gen ^ r := by
    show (word 1 0 + bitWord (n.testBit 0) * word 3 0) * (word 1 0 + bitWord (n.testBit 1) * word 5 0) = _
    rw [w3, w5, bitf, bitf, ← pow_add]; congr 1; omega
  have h43 : σ (.n 43) = gen ^ q := by
    show (((word 1 0 + bitWord (n.testBit 2) * word 3 0) * (word 1 0 + bitWord (n.testBit 3) * word 5 0)) *
      (word 1 0 + bitWord (n.testBit 4) * word 17 0)) * (word 1 0 + bitWord (n.testBit 5) * word 257 0) = _
    rw [w3, w5, w17, w257, bitf, bitf, bitf, bitf, ← pow_add, ← pow_add, ← pow_add]; congr 1; omega
  have hassert : σ (.n 46) + σ (.n 8) = 0 := by
    rw [show σ (.n 46) = σ (.n 43) * σ (.n 43) * (σ (.n 43) * σ (.n 43)) * σ (.n 24) from rfl, h43, h24,
      show σ (.n 8) = gen ^ n from rfl, hpqr]
    rw [show gen ^ q * gen ^ q * (gen ^ q * gen ^ q) * gen ^ r = gen ^ (4 * q + r) by ring]
    exact add_self_E _
  have w4 : word 4 0 = gen ^ 2 := word_two_pow (a := 2) (by norm_num)
  have h52 : σ (.n 52) = gen ^ (7 * (q + 2)) := by
    rw [show σ (.n 52) = (σ (.n 43) * word 4 0) * (σ (.n 43) * word 4 0) * (σ (.n 43) * word 4 0) *
      ((σ (.n 43) * word 4 0) * (σ (.n 43) * word 4 0) * (σ (.n 43) * word 4 0)) * (σ (.n 43) * word 4 0) from rfl,
      h43, w4]
    ring
  have h53 : σ (.n 53) = ptrAt c := rfl
  have h55 : σ (.n 55) = word 1 0 + σ (.n 43) := rfl
  have h61 : σ (.n 61) = ptrAt (c + 7 * q) := by
    rw [show σ (.n 61) = σ (.n 53) * ((σ (.n 43) * σ (.n 43) * σ (.n 43)) * (σ (.n 43) * σ (.n 43) * σ (.n 43)) *
      σ (.n 43)) from rfl, h53, h43, ← ptrAt_mul_gen_pow' c (7 * q)]
    ring
  have h63 : σ (.n 63) = ptrAt (c + 7 * q + 7) := by
    rw [show σ (.n 63) = σ (.n 61) * word 128 0 from rfl, h61, show (128 : ℕ) = 2 ^ 7 from rfl,
      word_two_pow (by norm_num), ptrAt_mul_gen_pow']
  have h66 : σ (.n 66) = point * gen ^ (4 * q) := by
    rw [show σ (.n 66) = point * ((σ (.n 43) * σ (.n 43)) * (σ (.n 43) * σ (.n 43))) from rfl, h43]; ring
  have hrets : [V.n 68, .n 69, .n 70, .n 71, .n 72, .n 73, .n 74].map σ = fin := by
    obtain ⟨x0, x1, x2, x3, x4, x5, x6, he, -⟩ := cells_eq_seven h5
    rw [hfin, he]; simp only [hσ, lrVals, hfin, he]; rfl
  -- the path
  have hlr : lasts[r]! = lasts.getD r "" := by
    simp [List.getD_eq_getElem?_getD, List.getElem!_eq_getElem?_getD]
  set es := (lrMPre loop).flatMap (slEvs σ) ++ .call (lasts.getD r "") [.n 61, .n 63, .n 66, .n 9] [.n 67] ::
    lrMPost.flatMap (slEvs σ) with hes
  have hw : walk σ fn.body = .ret es [.n 68, .n 69, .n 70, .n 71, .n 72, .n 73, .n 74] := by
    rw [hbody, lrMain_eq, hes, ← hlr]
    exact walk_dispatch σ (lrMPre loop) lrMPost (lrMPre_straight _) lrMPost_straight (.n 24) lasts _ _ _ (i := r)
      (by omega) (by omega) (by rw [h24, gen_pow_eq_ofK])
  have hpre := straight_parts σ (lrMPre loop) (lrMPre_straight _)
  have hpost := straight_parts σ lrMPost lrMPost_straight
  have hallocs : allocs σ es = [7 * (q + 2)] := by
    rw [hes, allocs_append, hpre.2.1, allocs, List.filterMap_cons, ← allocs, hpost.2.1]
    simp [lrMPre_allocSz, lrMPost_allocSz, Ev.alloc?, h52, logG_gen_pow (show 7 * (q + 2) < 2 ^ 64 - 1 by omega)]
  have hdsts : allocDsts es = [.n 53] := by
    rw [hes, allocDsts_append, hpre.1, allocDsts, List.filterMap_cons, ← allocDsts, hpost.1]
    simp [lrMPre_allocSz, lrMPost_allocSz, Ev.allocDst?]
  have haddrs : addrs es = [] := by
    rw [hes, addrs_append, hpre.2.2.1, addrs, List.filterMap_cons, ← addrs, hpost.2.2.1]
    simp [lrMPre_addrS, lrMPost_addrS, Ev.addr?]
  have hcalls : calls es = [⟨loop, [.n 56, .n 43, .n 53, .n 7, .n 9], [], decide (σ (.n 55) ≠ 0)⟩,
      ⟨lasts.getD r "", [.n 61, .n 63, .n 66, .n 9], [.n 67], true⟩] := by
    rw [hes, calls_append, hpre.2.2.2, calls, List.filterMap_cons, ← calls, hpost.2.2.2]
    simp [lrMPre_callS, lrMPost_callS, mkCall, Ev.call?]
  have htk : decide (σ (.n 55) ≠ 0) = decide (q ≠ 0) := by
    rw [h55, h43, word_one]
    refine decide_eq_decide.mpr ⟨fun h he => h (by rw [he, pow_zero]; exact add_self_E _), fun h he => h ?_⟩
    have := e_add_eq_zero_iff.mp he
    rw [← pow_zero gen] at this
    exact (gen_pow_inj (by omega) (by omega) this).symm
  -- the regions
  set Rm := ptrRegion (lrArrays cur point tabs nw n) with hRm
  have hRp : ∀ t < n, ∃ i, point.limb 0 * addressOfIndex t = addressOfIndex i ∧ Rm i := fun t ht => by
    obtain ⟨i, -, hi⟩ := hpb (point, n) (by simp [lrArrays]) t ht
    exact ⟨i, hi, _, by simp [lrArrays], t, ht, hi⟩
  have hRc : ∀ t < n * rlen nt bits, ∃ i, cur.limb 0 * addressOfIndex t = addressOfIndex i ∧ Rm i := fun t ht => by
    obtain ⟨i, -, hi⟩ := hpb (cur, nw) (by simp [lrArrays]) t (lt_of_lt_of_le ht hnwle)
    exact ⟨i, hi, _, by simp [lrArrays], t, lt_of_lt_of_le ht hnwle, hi⟩
  have hRt : ∀ t < 2 ^ winTabBits, ∃ i, tabs.limb 0 * addressOfIndex t = addressOfIndex i ∧ Rm i := fun t ht => by
    obtain ⟨i, -, hi⟩ := hpb (tabs, 2 ^ winTabBits) (by simp [lrArrays]) t ht
    exact ⟨i, hi, _, by simp [lrArrays], t, ht, hi⟩
  set Rl : ℕ → Prop := fun i => Rm i ∨ (c ≤ i ∧ i < c + 7 * (q + 2)) with hRl
  have hown : ∀ i, c ≤ i → i < c + 7 * (q + 2) → ownData cert fp c name [7 * (q + 2)] es i := fun i h1 h2 =>
    Or.inl ⟨(7 * (q + 2), c), by simp [bases], h1, by omega⟩
  have hRl' : ∀ i, Rl i → Rm i ∨ ownData cert fp c name [7 * (q + 2)] es i := fun i hi => by
    rcases hi with hi | hi
    · exact Or.inl hi
    · exact Or.inr (hown i hi.1 hi.2)
  have hcell : ∀ b off, b + off < c + 7 * (q + 2) → c ≤ b →
      ∃ i, (ptrAt b).limb 0 * addressOfIndex off = addressOfIndex i ∧ Rl i := fun b off h1 h2 =>
    ⟨b + off, Main.addr_ofK _ _, Or.inr ⟨by omega, h1⟩⟩
  -- the words the callees read
  have hrecs : ∀ rd, RoundChain rd nt bits st0 l → HoldsWords rd [(c, lrWords st0 l)] →
      (∀ m ≤ q, ReadsAt rd (ptrAt (c + 7 * m)) (lrRec st0 l m).cells) ∧
        ReadsAt rd (ptrAt (c + 7 * (q + 1))) (chainLast st0 l).cells :=
    fun rd hch hw => lrWords_recs ⟨nt, bits, hch⟩ hs5 (hw _ List.mem_cons_self)
  have hdrop : chainLast (lrRec st0 l q) (l.drop (4 * q)) = chainLast st0 l := by
    unfold lrRec; rw [← chainLast_append', List.take_append_drop]
  have hdl : (l.drop (4 * q)).length = r := by simp; omega
  have hlastPre : ∀ rd, ((bits ≠ 0 → WinTabs rd tabs) ∧ RoundChain rd nt bits st0 l ∧ ReadsAt rd point (l.map Prod.fst)) →
      HoldsWords rd [(c, lrWords st0 l)] →
      ReadsAt rd (σ (.n 61)) (lrRec st0 l q).cells ∧ (bits ≠ 0 → WinTabs rd (σ (.n 9))) ∧
        RoundChain rd nt bits (lrRec st0 l q) (l.drop (4 * q)) ∧
        ReadsAt rd (σ (.n 66)) ((l.drop (4 * q)).map Prod.fst) ∧
        ReadsAt rd (σ (.n 63)) (chainLast (lrRec st0 l q) (l.drop (4 * q))).cells := by
    intro rd ⟨hwt, hch, hpts⟩ hw
    obtain ⟨hr1, hr2⟩ := hrecs rd hch hw
    refine ⟨by rw [h61]; exact hr1 q le_rfl, hwt, ?_, ?_, ?_⟩
    · have h := hch
      rw [← List.take_append_drop (4 * q) l] at h
      exact (roundChain_append_inv h).2
    · rw [h66]
      refine readsAt_of_getD fun i hi => ?_
      simp only [List.length_map, hdl] at hi
      have := readsAt_getD hpts (i := 4 * q + i) (by simp; omega)
      simpa [List.getD_eq_getElem?_getD, List.getElem?_drop] using this
    · rw [hdrop, h63, show c + 7 * q + 7 = c + 7 * (q + 1) by ring]; exact hr2
  have hcur : ∀ t < r * rlen nt bits, ∃ i, (lrRec st0 l q).cur.limb 0 * addressOfIndex t = addressOfIndex i ∧ Rl i := by
    intro t ht
    have e : (lrRec st0 l q).cur = cur * gen ^ (4 * q * rlen nt bits) := curChain_cur st0 l hcc (4 * q) (by omega)
    obtain ⟨i, hi, hRi⟩ := hRc (4 * q * rlen nt bits + t) (by
      have : (4 * q + r) * rlen nt bits = 4 * q * rlen nt bits + r * rlen nt bits := by ring
      rw [hpqr, this]; omega)
    refine ⟨i, ?_, Or.inl hRi⟩
    rw [e, ← hi, gen_pow_eq_ofK, limb0_mul_ofK, mul_assoc, addressOfIndex, addressOfIndex, addressOfIndex, ← pow_add]
  have hlastA := hlast r hr4 Rl (σ (.n 61)) (σ (.n 63)) (σ (.n 66)) (σ (.n 9)) (lrRec st0 l q) (l.drop (4 * q)) h5q hdl
    (fun off h => by rw [h61]; exact hcell _ _ (by omega) (by omega))
    (fun off h => by rw [h63]; exact hcell _ _ (by omega) (by omega))
    (fun off h => by
      obtain ⟨i, hi, hRi⟩ := hRp (4 * q + off) (by omega)
      refine ⟨i, ?_, Or.inl hRi⟩
      rw [h66, ← hi, gen_pow_eq_ofK, limb0_mul_ofK, mul_assoc, addressOfIndex, addressOfIndex, addressOfIndex,
        ← pow_add])
    hcur (fun _ t ht => (fun ⟨i, hi, hRi⟩ => ⟨i, hi, Or.inl hRi⟩) (hRt t ht))
  have hst : ∀ rd, RoundChain rd nt bits st0 l → HoldsWords rd [(c, lrWords st0 l)] →
      ∀ i < 7, LoadHolds rd (σ (.n 53)) i (st0.cells.getD i 0) := by
    intro rd hch hw i hi
    have := (hrecs rd hch hw).1 0 (Nat.zero_le _)
    simp only [Nat.mul_zero, Nat.add_zero, lrRec, List.take_zero, chainLast] at this
    exact readsAt_getD this (by simp [RSt.cells, hst0]; omega)
  set cur0 := c + 7 * (q + 2) with hcur0
  set c2 := allocBase (al loop) cur0 + lrBlock fs loop q with hc2
  have hub : FsSmall fs → allocBase (al (lasts.getD r "")) c2 + fs (lasts.getD r "") ≤ c + 2 ^ 21 := by
    intro hfs
    have := allocBase_le (al loop) cur0
    have := step_le hfs (al (lasts.getD r "")) (lasts.getD r "") c2
    have : lrBlock fs loop q ≤ (q + 1) * 2 ^ 16 := by
      have h := lpB_le hfs loop q 0
      simp only [lpB, Nat.sub_zero] at h
      unfold lrBlock; exact h
    omega
  refine ⟨allocBase (al (lasts.getD r "")) c2 + fs (lasts.getD r ""), hub, callAtA_node hlp le_rfl
    ⟨σ, fn, es, [.n 68, .n 69, .n 70, .n 71, .n 72, .n 73, .n 74], [(c, lrWords st0 l)], [PostQuiet, PostQuiet],
      fun rd => HoldsWords rd [(c, lrWords st0 l)], fun _ => False, hfind, by rw [hparams]; rfl, hw, hrets,
      ?_, ?_, ?_, ?_, fun _ h => h.elim, ?_, fun _ _ => trivial, ?_, ?_⟩⟩
  · rw [hallocs]
    exact ⟨by rw [hdsts]; simp [bases, h53], by rw [haddrs]; simp⟩
  · rw [hallocs]
    exact ⟨fun q' hq' => by
      rw [List.mem_singleton] at hq'; subst hq'
      exact Or.inr ⟨le_rfl, by simp [lrWords]; omega⟩, List.pairwise_singleton _ _⟩
  · -- the loads
    intro A hA
    rw [hallocs]
    rw [hes, loadAddrs_append, LeanVM.Guest.Memory.loadAddrs_straight _ _ (lrMPre_straight _), loadAddrs,
      List.filterMap_cons, ← loadAddrs, LeanVM.Guest.Memory.loadAddrs_straight _ _ lrMPost_straight] at hA
    simp only [Ev.loadAddr?, List.mem_append, List.mem_map] at hA
    rcases hA with ⟨⟨x, off⟩, hq', rfl⟩ | ⟨⟨x, off⟩, hq', rfl⟩
    · have h53' : ∀ off < 7, ∃ i, (σ (.n 53)).limb 0 * addressOfIndex off = addressOfIndex i ∧
          (ownData cert fp c name [7 * (q + 2)] es i ∨ Rm i ∨ False) :=
        fun off hoff => ⟨c + off, by rw [h53]; exact Main.addr_ofK _ _, Or.inl (hown _ (by omega) (by omega))⟩
      rw [lrMPre_loads] at hq'
      simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hq'
      rcases hq' with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
        exact h53' _ (by norm_num)
    · have h61' : ∀ off, 7 ≤ off → off < 14 → ∃ i, (σ (.n 61)).limb 0 * addressOfIndex off = addressOfIndex i ∧
          (ownData cert fp c name [7 * (q + 2)] es i ∨ Rm i ∨ False) :=
        fun off h1 h2 => ⟨c + 7 * q + off, by rw [h61]; exact Main.addr_ofK _ _, Or.inl (hown _ (by omega) (by omega))⟩
      rw [lrMPost_loads] at hq'
      simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hq'
      rcases hq' with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
        exact h61' _ (by norm_num) (by norm_num)
  · -- no heap hint
    intro A hA
    rw [hes, heapHintAddrs_append, heapHintAddrs_nil_of _ (lrMPre_noHeap _), heapHintAddrs, List.flatMap_cons,
      ← heapHintAddrs, heapHintAddrs_nil_of _ lrMPost_noHeap] at hA
    simp [Ev.hintAddrs] at hA
  · -- the callees
    rw [hcalls, hallocs, htk]
    by_cases hq0 : q = 0
    · have hd : decide (q ≠ 0) = false := decide_eq_false (by omega)
      simp only [KidsAtF, hd, Bool.false_eq_true, ↓reduceIte, List.headD_cons, List.tail_cons]
      have e : allocBase (al loop) (c + [7 * (q + 2)].sum) + fs (tailKey loop) = c2 := by
        simp only [hc2, hcur0, lrBlock, List.sum_cons, List.sum_nil, Nat.add_zero, hq0, zero_mul, zero_add]
      refine ⟨⟨fun v => ([V.n 56, .n 43, .n 53, .n 7, .n 9].map σ).getD v.idx 0, loopFn, hlf, by rw [hlpar]; rfl⟩,
        fs (lasts.getD r ""), allocBase (al (lasts.getD r "")) c2 + fs (lasts.getD r ""), Rl, fun _ => False,
        fun _ => True, fun i hi => Or.inl (hRl' i hi), ?_, rfl, fun _ h => h.1, fun _ h => h.elim⟩
      · rw [e]
        exact (hlastA _ _).mono (fun _ h => h) (fun _ h => h) (fun _ _ => trivial)
          (fun rd h => hlastPre rd h.1 h.2) (fun _ _ _ h => h)
    · have hd : decide (q ≠ 0) = true := decide_eq_true hq0
      simp only [KidsAtF, hd, ↓reduceIte, List.headD_cons, List.tail_cons]
      refine ⟨lrBlock fs loop q, c2, Rl, fun _ => False, fun _ => True, fun i hi => Or.inl (hRl' i hi), ?_,
        fs (lasts.getD r ""), allocBase (al (lasts.getD r "")) c2 + fs (lasts.getD r ""), Rl, fun _ => False,
        fun _ => True, fun i hi => Or.inl (hRl' i hi), ?_, rfl, fun _ h => h.1.1, fun _ h => h.elim⟩
      · have h0 : [V.n 56, .n 43, .n 53, .n 7, .n 9].map σ = [gen ^ 0, gen ^ q, ptrAt c, point, tabs] := by
          simp only [List.map_cons, List.map_nil, h43, h53, pow_zero]
          rfl
        rw [h0]
        exact (hloop st0 l q c point tabs Rl hs5 (by omega) hq16 (by omega)
          (fun t ht => (fun ⟨i, hi, hRi⟩ => ⟨i, hi, Or.inl hRi⟩) (hRp t ht))
          (fun t ht => (fun ⟨i, hi, hRi⟩ => ⟨i, hi, Or.inl hRi⟩) (hRc t ht))
          (fun i h1 h2 => Or.inr ⟨h1, h2⟩)
          (fun _ t ht => (fun ⟨i, hi, hRi⟩ => ⟨i, hi, Or.inl hRi⟩) (hRt t ht))
          (allocBase (al loop) cur0) (allocBase (al loop) cur0 + lrBlock fs loop q) (by simp)).mono
          (fun _ h => h) (fun _ h => h) (fun _ _ => trivial)
          (fun rd h => ⟨h.1.1, h.1.2.1, h.1.2.2, (hrecs rd h.1.2.1 h.2).1⟩) (fun _ _ _ h => h)
      · exact (hlastA _ _).mono (fun _ h => h) (fun _ h => h) (fun _ _ => trivial)
          (fun rd h => hlastPre rd h.1 h.2.1) (fun _ _ _ h => h)
  · -- the events
    intro rd _ hP hw ev hev
    have hch := hP.2.1
    rw [hes] at hev
    simp only [List.mem_append, List.mem_cons] at hev
    rcases hev with hev | rfl | hev
    · obtain ⟨s, hs, hev⟩ := List.mem_flatMap.mp hev
      have hK55 : IsInK (σ (.n 55)) := by
        rw [h55, h43, word_one, ← pow_zero gen]; exact isInK_add (gen_pow_isInK _) (gen_pow_isInK _)
      have hst := hst rd hch hw
      have hs' : SOkV rd σ s := by
        simp only [lrMPre, List.mem_cons, List.not_mem_nil, or_false] at hs
        rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
        exacts [trivial, bitWord_sq _, rfl, rfl, rfl, rfl, bitWord_sq _, rfl, rfl, rfl, rfl, rfl, bitWord_sq _, rfl, rfl, rfl, rfl, bitWord_sq _, rfl, rfl, rfl, rfl, rfl, bitWord_sq _, rfl, rfl, rfl, rfl, rfl, bitWord_sq _, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, hassert, rfl, rfl, rfl, rfl, rfl, rfl, trivial, hst 0 (by norm_num), hst 1 (by norm_num), hst 2 (by norm_num), hst 3 (by norm_num), hst 4 (by norm_num), hst 5 (by norm_num), hst 6 (by norm_num), rfl, rfl, rfl, hK55, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl]
      exact events_sokV hs' hev
    · trivial
    · obtain ⟨s, hs, hev⟩ := List.mem_flatMap.mp hev
      have hr2 := (hrecs rd hch hw).2
      have hpost7 : ∀ i < 7, LoadHolds rd (σ (.n 61)) (7 + i) (fin.getD i 0) := fun i hi => by
        rw [h61, ← loadHolds_mul_gen_pow, ptrAt_mul_gen_pow', show c + 7 * q + 7 = c + 7 * (q + 1) by ring]
        exact readsAt_getD hr2 (by simp [RSt.cells, h5]; exact hi)
      simp only [lrMPost, List.mem_cons, List.not_mem_nil, or_false] at hs
      rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp only [slEvs, List.mem_singleton] at hev <;>
        subst hev
      exacts [hpost7 0 (by norm_num), hpost7 1 (by norm_num), hpost7 2 (by norm_num), hpost7 3 (by norm_num),
        hpost7 4 (by norm_num), hpost7 5 (by norm_num), hpost7 6 (by norm_num)]
  · -- the post
    intro rd ts _ _ _ hv hp'
    refine postQuiet_node hfind hw (fun a ha => ?_) (fun ev hev => ?_) hv (by rw [hcalls] at hp' ⊢; exact hp') _
    · rw [hes] at ha
      simp only [List.mem_append, List.mem_cons, reduceCtorEq, false_or] at ha
      rcases ha with ha | ha
      · obtain ⟨s, hs, ha⟩ := List.mem_flatMap.mp ha
        exact quiet_of_slEvs (List.all_eq_true.mp (lrMPre_quiet _) s hs) ha
      · obtain ⟨s, hs, ha⟩ := List.mem_flatMap.mp ha
        exact quiet_of_slEvs (List.all_eq_true.mp lrMPost_quiet s hs) ha
    · rw [hes] at hev
      simp only [List.mem_append, List.mem_cons] at hev
      rcases hev with hev | rfl | hev
      · obtain ⟨s, hs, hev⟩ := List.mem_flatMap.mp hev
        rw [lrMPre] at hs
        rcases List.mem_cons.mp hs with rfl | hs
        · simp only [slEvs, List.mem_singleton] at hev
          subst hev
          exact ⟨n, hl64, by rw [show σ (.n 8) = gen ^ n from rfl, gen_pow_eq_ofK], rfl⟩
        · exact exact_of_slEvs (List.all_eq_true.mp (lrMPre_noComputed loop) s hs) hev
      · trivial
      · obtain ⟨s, hs, hev⟩ := List.mem_flatMap.mp hev
        exact exact_of_slEvs (List.all_eq_true.mp lrMPost_noComputed s hs) hev

end
end LeanVM.Guest.B1.VsC
