/-
  LeanVM.Protocol.EndToEnd.Front.KeccakBridge

  The table seam read as the public-input phase's doom, and the Keccak phase of the verifier
  program (`keccakPhase`) specified from the public-input phase's doom to the doom ring switching
  starts from, by the Keccak reduction's specification (`KeccakGkr.gkrSpec`).
-/

module

public import LeanVM.Protocol.Verifier.Claims
public import LeanVM.Protocol.EndToEnd.Front.TablePhase
public import LeanVM.Protocol.EndToEnd.Front.TableFidLeanIsaBus
public import LeanVM.Protocol.EndToEnd.Front.BusTable
public import LeanVM.Protocol.EndToEnd.Front.LayoutBridgeB
public import LeanVM.Protocol.EndToEnd.Front.KeccakLayout
public import LeanVM.Protocol.EndToEnd.Sound.Returns
public import LeanVM.Protocol.EndToEnd.Sound.Frame
public import LeanVM.Protocol.Keccak.Gkr

/-!
# The Keccak phase on doom

Step 6 of `verify_execution` (`keccakPhase`, `crates/verifier/src/lib.rs:283-300` at leanVM
`40f877dc`): the table's 25 claims on the `KECCAK` output lanes,
all at one point `inst`, leave the batch and are the Keccak reduction's claim on the permutation's
output; the reduction (`verifyKeccak`) adds its claims on `q_keccak` to the batch and leaves a point
and 64 bit-slice claims of `q_keccak` for ring switching.

**The doom carried in.** After the table sumcheck and the public input, no candidate satisfies the
program's claims read on it (`WireHolds`: an output lane's claim on the derived column, the
second segment of the committed middle state; every other claim on the stack) and the Keccak
predicate at the table sumcheck's point `pt` (`M3Instance.auxAt`), the output lanes' claims being
at `pt`'s low `τ_KECCAK` coordinates (`OutLanesAt`). `tablePost_pubPre` reads the table seam so.

**The bridge.** Once the program's check on the lanes passes, `inst` is `pt`'s low coordinates
(`inst_eq`), the lanes' claims are the reduction's `outClaimsTrueMid` (`laneHolds_iff`), and the
Keccak predicate at `pt` is the reduction's `midAgree` (`auxAt_iff_midAgree`): the reduction's
precondition is the doom carried in. Its postcondition, the column claims it returns on `q_keccak`
(`colTrue`, which `qkHolds_iff` reads as the program's claims on the stack, the returned claims
being on `QKECCAK` at `τ_KECCAK + 6` coordinates, `retOK_verifyKeccak`) and the slices, is the doom
ring switching starts from (`KeccakOut`).
-/

namespace LeanVM.Protocol.EndToEnd.Front

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.Compile
open LeanVM.Protocol.Verifier LeanVM.Protocol.LeanIsa CompPoly CMlPolynomialEval
open LeanVM.Protocol.EndToEnd.Sound (RetOK RetOK.ret RetOK.bind RetOK.bind_true)
open LeanVM.Protocol.TableSumcheck (Data tableOut)
open Finset
open scoped NNReal ENNReal

@[expose] public section

/-! ## The returns of the Keccak reduction -/

/-- A sumcheck returns one challenge per round. -/
theorem retOK_sumcheck (count : ℕ) : ∀ (eqs : List (Option E)) (claim : E),
    RetOK (fun r : List E × E ↦ r.1.length = eqs.length) (Verifier.sumcheck claim count eqs)
  | [], _ => RetOK.ret rfl
  | _ :: eqs, _ => RetOK.bind_true fun _ ↦ RetOK.bind_true fun _ ↦
      (retOK_sumcheck count eqs _).bind fun r hr ↦ RetOK.ret (by simp [hr])

/-- `keccak_open` returns a slot of six challenges. -/
theorem retOK_keccakOpen (logSteps : ℕ) (claim : KeccakClaim) (first count : ℕ) (value : E) :
    RetOK (fun r : List E × List E × E ↦ r.1.length = qkeccakSlotBits)
      (keccakOpen logSteps claim first count value) :=
  (retOK_sumcheck 3 _ value).bind fun r hr ↦ RetOK.ret (by simpa using hr)

/-- **The Keccak reduction's column claims are on `QKECCAK`**, at `|inst| + 6` coordinates when
`inst` has at least four. -/
theorem retOK_verifyKeccak (logSteps : ℕ) (inst output : List E) (hi : 4 ≤ inst.length) :
    RetOK (fun r : List Verifier.ColumnClaim × List E × List E ↦
      ∀ c ∈ r.1, c.column = qkeccak ∧ c.point.length = inst.length + 6)
      (verifyKeccak logSteps inst output) := by
  unfold verifyKeccak
  refine RetOK.bind_true fun _ ↦ RetOK.bind_true fun _ ↦ RetOK.bind_true fun _ ↦
    RetOK.bind_true fun _ ↦ ?_
  simp only [show 1 < keccakSegments from by decide, ↓reduceIte]
  refine (retOK_keccakOpen _ _ _ _ _).bind fun r hr ↦ ?_
  obtain ⟨slot, weights, value⟩ := r
  refine RetOK.bind_true fun _ ↦ RetOK.bind_true fun _ ↦
    (RetOK.ret (Q := fun cs : List Verifier.ColumnClaim ↦
      ∀ c ∈ cs, c.column = qkeccak ∧ c.point.length = inst.length + 6) ?_).bind fun cs hcs ↦ ?_
  · intro c hc
    simp only [List.mem_singleton] at hc
    subst hc
    refine ⟨rfl, ?_⟩
    simp only [List.length_append, List.length_take, List.length_drop]
    rw [show (slot, weights, value).1 = slot from rfl] at hr
    rw [hr, show qkeccakSlotBits = 6 by decide]
    omega
  · refine RetOK.bind_true fun r ↦ ?_
    obtain ⟨low, v⟩ := r
    refine RetOK.bind_true fun r ↦ ?_
    obtain ⟨slot', weights', value'⟩ := r
    exact RetOK.bind_true fun _ ↦ RetOK.bind_true fun _ ↦ RetOK.ret hcs

/-- The Keccak reduction returns one column claim. -/
theorem retOK_verifyKeccak_count (logSteps : ℕ) (inst output : List E) :
    RetOK (fun r : List Verifier.ColumnClaim × List E × List E ↦ r.1.length ≤ 1)
      (verifyKeccak logSteps inst output) := by
  unfold verifyKeccak
  refine RetOK.bind_true fun _ ↦ RetOK.bind_true fun _ ↦ RetOK.bind_true fun _ ↦
    RetOK.bind_true fun _ ↦ ?_
  simp only [show 1 < keccakSegments from by decide, ↓reduceIte]
  refine RetOK.bind_true fun r ↦ ?_
  obtain ⟨slot, weights, value⟩ := r
  refine RetOK.bind_true fun _ ↦ RetOK.bind_true fun _ ↦
    (RetOK.ret (Q := fun cs : List Verifier.ColumnClaim ↦ cs.length ≤ 1) (by simp)).bind
      fun cs hcs ↦ ?_
  refine RetOK.bind_true fun r ↦ ?_
  obtain ⟨low, v⟩ := r
  refine RetOK.bind_true fun r ↦ ?_
  obtain ⟨slot', weights', value'⟩ := r
  exact RetOK.bind_true fun _ ↦ RetOK.bind_true fun _ ↦ RetOK.ret hcs

/-- The Keccak phase returns at most one claim more than it receives. -/
theorem retOK_keccakPhase (layout : Verifier.Layout) (claims : List Verifier.ColumnClaim) :
    RetOK (fun r : List Verifier.ColumnClaim × List E × List E ↦
      r.1.length ≤ claims.length + 1) (keccakPhaseClaims layout claims) := by
  refine RetOK.bind_true fun _ ↦ (retOK_verifyKeccak_count _ _ _).bind fun r hr ↦ RetOK.ret ?_
  simp only [List.length_append]
  have := List.length_filter_le (fun c : Verifier.ColumnClaim ↦ decide (c.column ∉ keccakOutputColumns)) claims
  omega

/-- `sampleN n` returns `n` challenges. -/
theorem retOK_sampleN : ∀ n : ℕ, RetOK (fun xs : List E ↦ xs.length = n)
    (VerifierProgram.sampleChallenges n)
  | 0 => RetOK.ret rfl
  | n + 1 => RetOK.bind_true fun _ ↦ (retOK_sampleN n).bind fun xs hxs ↦
      RetOK.ret (by simp [hxs])

/-- The pack rounds return one challenge per coordinate of the point. -/
theorem retOK_keccakPackRounds : ∀ (rs : List E) (value scale : E),
    RetOK (fun r : E × E × List E ↦ r.2.2.length = rs.length) (keccakPackRounds rs value scale)
  | [], _, _ => RetOK.ret rfl
  | _ :: rs, _, _ => RetOK.bind_true fun _ ↦ RetOK.bind_true fun _ ↦
      (retOK_keccakPackRounds rs _ _).bind fun r hr ↦ RetOK.ret (by simp [hr])

/-- A layer keeps the length of the claim's point. -/
theorem retOK_verifyKeccakLayer (logSteps step : ℕ) (claim : KeccakClaim) :
    RetOK (fun c : KeccakClaim ↦ c.point.length = claim.point.length)
      (verifyKeccakLayer logSteps step claim) := by
  unfold verifyKeccakLayer
  refine RetOK.bind_true fun _ ↦ RetOK.bind_true fun _ ↦ RetOK.bind_true fun _ ↦ ?_
  refine (retOK_keccakPackRounds _ _ _).bind fun r hr ↦ ?_
  obtain ⟨value, scale, point⟩ := r
  refine RetOK.bind_true fun r ↦ ?_
  obtain ⟨localPoint, value'⟩ := r
  exact RetOK.bind_true fun _ ↦ RetOK.bind_true fun _ ↦ RetOK.bind_true fun _ ↦ RetOK.ret hr

/-- The layers keep the length of the claim's point. -/
theorem retOK_keccakLayers (logSteps : ℕ) : ∀ (steps : List ℕ) (claim : KeccakClaim),
    RetOK (fun c : KeccakClaim ↦ c.point.length = claim.point.length)
      (keccakLayers logSteps steps claim)
  | [], _ => RetOK.ret rfl
  | _ :: steps, _ => (retOK_verifyKeccakLayer _ _ _).bind fun c hc ↦
      (retOK_keccakLayers logSteps steps c).mono fun _ h ↦ h.trans hc

/-- **The Keccak reduction's point and slices**: the point it leaves for ring switching has
`|inst| + 6` coordinates, and it leaves 64 slices, when `inst` has at least four. -/
theorem retOK_verifyKeccak_point (logSteps : ℕ) (inst output : List E)
    (hi : 4 ≤ inst.length) (hl : inst.length = logSteps) :
    RetOK (fun r : List Verifier.ColumnClaim × List E × List E ↦
      r.2.1.length = inst.length + 6 ∧ r.2.2.length = 64)
      (verifyKeccak logSteps inst output) := by
  unfold verifyKeccak
  refine (retOK_sampleN _).bind fun segment hseg ↦ RetOK.bind_true fun _ ↦
    RetOK.bind_true fun _ ↦ ?_
  refine (retOK_keccakLayers _ _ _).bind fun claim hclaim ↦ ?_
  simp only [show 1 < keccakSegments from by decide, ↓reduceIte]
  refine RetOK.bind_true fun r ↦ ?_
  obtain ⟨slot, weights, value⟩ := r
  refine RetOK.bind_true fun _ ↦ RetOK.bind_true fun _ ↦ RetOK.bind_true fun _ ↦ ?_
  refine (retOK_sumcheck 3 _ _).bind fun r hr ↦ ?_
  obtain ⟨low, v⟩ := r
  refine (retOK_keccakOpen _ _ _ _ _).bind fun r hr' ↦ ?_
  obtain ⟨slot', weights', value'⟩ := r
  refine (RetOK.readN _).bind fun slices hs ↦ RetOK.bind_true fun _ ↦ RetOK.ret ⟨?_, ?_⟩
  · simp only [List.length_append, List.length_take] at hr hr' ⊢
    rw [hclaim]
    simp only [keccakFirstClaim, List.length_append, List.length_drop, List.length_replicate]
      at hr ⊢
    rw [hseg, hr, hr', show qkeccakSlotBits = 6 by decide,
      show keccakSegmentBits = 1 by decide]
    omega
  · exact hs

/-! ## Equality weights -/

/-- The cube point of `x` on `n + 1` coordinates: bit `0`, then the cube point of `x / 2`. -/
theorem boolPoint_succ (n x : ℕ) :
    boolPoint (n + 1) x = (if x.testBit 0 then 1 else 0) :: boolPoint n (x / 2) := by
  simp only [boolPoint, List.range_succ_eq_map, List.map_cons, List.map_map]
  congr 1
  refine List.map_congr_left fun i _ ↦ ?_
  simp [Nat.testBit_succ]

/-- `eq_eval` at the cube point of `x` is the Keccak reduction's equality weight of `x`. -/
theorem eqAt_eq_eqEval : ∀ (pt : List E) (x : ℕ),
    KeccakGkr.eqAt pt x = eqEval pt (boolPoint pt.length x)
  | [], x => by simp [eqEval]
  | r :: rs, x => by
    rw [KeccakGkr.eqAt_cons, eqAt_eq_eqEval rs (x / 2), List.length_cons, boolPoint_succ,
      eqEval_eq_list_prod, eqEval_eq_list_prod, List.zipWith_cons_cons, List.prod_cons,
      Nat.testBit_zero]
    congr 1
    by_cases h : x % 2 = 1
    · simp only [h, ↓reduceIte, decide_true]
      rw [add_comm 1 r, add_assoc, CharTwo.add_self_eq_zero, add_zero]
    · simp [h]

/-- The table sumcheck's zero test weighs as the Keccak reduction (characteristic two). -/
theorem keccakZero_eqAt : ∀ (pt : List E) (x : ℕ), KeccakZero.eqAt pt x = KeccakGkr.eqAt pt x
  | [], _ => rfl
  | r :: rs, x => by
    rw [KeccakZero.eqAt, KeccakGkr.eqAt_cons, keccakZero_eqAt rs, CharTwo.sub_eq_add]

/-- **A column's extension** is the sum of its cells weighted by the equality weights of the
point. -/
theorem eval₂Mle_eq_sum_eqAt {n : ℕ} (v : Vector K (2 ^ n)) (z : Vector E n) :
    eval₂Mle v (algebraMap K E) z =
      ∑ x ∈ range (2 ^ n), KeccakGkr.eqAt z.toList x * ofK (v.getD x 0) := by
  rw [← sum_eqEval_mul z ⟨v⟩, Finset.sum_range]
  refine Finset.sum_congr rfl fun x _ ↦ ?_
  rw [eqAt_eq_eqEval, Vector.length_toList]

/-! ## `q_keccak` on a candidate -/

section Reading

variable (prog : LeanIsaProgram) (s : Sizes)

/-- `q_keccak`'s words on a candidate are its reading's cells past `QKECCAK`'s offset. -/
theorem qkOf_eq (q : Column (verifierLayout prog s).stackLog) (n : ℕ) :
    qkOf (verifierLayout prog s) q n =
      (toI prog s q).values.toArray.getD ((blocks prog s).offset (keccakBlock prog s) + n) 0 := by
  unfold qkOf
  rw [placement_qkeccak]
  rfl

/-- Word `x` of slot `slot` of the Keccak region of a candidate's reading is `q_keccak`'s word
`x + 2^τ · slot`. -/
theorem word_eq_qkOf (q : Column (verifierLayout prog s).stackLog) (slot : ℕ) (hslot : slot < 64)
    (x : Fin (2 ^ s.τ 5)) :
    (keccakRegion prog s).word ((leanIsaInstance prog s).keccakColumn (keccakRegion prog s)
        (toI prog s q)) slot x =
      qkOf (verifierLayout prog s) q (x.val + 2 ^ s.τ 5 * slot) := by
  have hlt := (blocks prog s).offset_add_pow_le_total (keccakBlock prog s)
  have hfit := blocks_fits prog s
  have h1 := slot_lt x slot hslot
  have h2 : 2 ^ (s.τ 5 + 6) = 2 ^ (blocks prog s).size (keccakBlock prog s) := by
    rw [size_keccakBlock]
  rw [word_keccakColumn prog s _ slot hslot, qkOf_eq, Array.getD_eq_getD_getElem?,
    Array.getElem?_eq_getElem (by rw [Vector.size_toArray]; omega), Option.getD_some]
  simp only [Vector.getElem_toArray]
  congr 1
  omega

/-- The state a slot range of the Keccak region of a candidate's reading holds is the Keccak
reduction's `inState` of `q_keccak`. -/
theorem state_eq_inState (q : Column (verifierLayout prog s).stackLog) (m : ℕ) (hm : m < 2)
    (x : Fin (2 ^ s.τ 5)) :
    (keccakRegion prog s).state ((leanIsaInstance prog s).keccakColumn (keccakRegion prog s)
        (toI prog s q)) (25 * m) x =
      KeccakGkr.inState (s.τ 5) (qkOf (verifierLayout prog s) q) m x.val := by
  unfold KeccakRegion.state laneState KeccakGkr.inState
  congr 1
  funext l
  exact congrArg K.lane (word_eq_qkOf prog s q (25 * m + l) (by omega) x)

/-- Cell `x` of a derived output lane of a candidate's reading is lane `l` of the second segment
of the committed middle state `q_keccak` holds at step `x`. -/
theorem outCol_getD (q : Column (verifierLayout prog s).stackLog) (l : Fin 25) {x : ℕ}
    (hx : x < 2 ^ s.τ 5) :
    ((leanIsaInstance prog s).column (toI prog s q) (outCol l)).values.getD x 0 =
      KeccakGkr.laneWord (KeccakGkr.roundsFrom 12 12
        (KeccakGkr.inState (s.τ 5) (qkOf (verifierLayout prog s) q) 1 x)) l := by
  have h := column_outCol prog s (toI prog s q) l ⟨x, hx⟩
  rw [show (25 : ℕ) = 25 * 1 from rfl, state_eq_inState prog s q 1 (by norm_num)] at h
  rw [Vector.getD, Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem
    (by rw [Vector.size_toArray]; exact hx), Option.getD_some]
  exact h

/-- The global column of output lane `l` is `113 + l`. -/
theorem refCol_outCol : ∀ l : Fin 25, refCol (outCol l) = 113 + l.val := by
  decide +kernel

/-- **A lane's claim is the Keccak reduction's output claim**: the program's claim on output lane
`l` at `inst` (on `τ_KECCAK` coordinates) holds of a candidate, read on the derived column, exactly
when the extension over the steps of lane `l` of the second segment of the committed middle state
is the claimed value. -/
theorem laneHolds_iff (q : Column (verifierLayout prog s).stackLog) (l : Fin 25) (inst : List E)
    (hi : inst.length = s.τ 5) (v : E) :
    WireHolds prog s ⟨113 + l.val, inst, v⟩ q ↔
      KeccakGkr.stepMle (s.τ 5) inst (fun x ↦ KeccakGkr.laneWord (KeccakGkr.roundsFrom 12 12
        (KeccakGkr.inState (s.τ 5) (qkOf (verifierLayout prog s) q) 1 x)) l) = v := by
  let z : Vector E (s.τ 5) := ⟨inst.toArray, by simpa using hi⟩
  have hz : z.toList = inst := by simp [z]
  have h := wireHolds_iff prog s (outCol l) z v q
  rw [refCol_outCol] at h
  refine (show WireHolds prog s ⟨113 + l.val, inst, v⟩ q ↔ _ from h).trans ?_
  have hs : ∀ x ∈ range (2 ^ s.τ 5), KeccakGkr.eqAt inst x *
      ofK (((leanIsaInstance prog s).column (toI prog s q) (outCol l)).values.getD x 0) =
      KeccakGkr.eqAt inst x * ofK (KeccakGkr.laneWord (KeccakGkr.roundsFrom 12 12
        (KeccakGkr.inState (s.τ 5) (qkOf (verifierLayout prog s) q) 1 x)) l) :=
    fun x hx ↦ by rw [outCol_getD prog s q l (Finset.mem_range.1 hx)]
  have hsum := (eval₂Mle_eq_sum_eqAt
    (((leanIsaInstance prog s).column (toI prog s q) (outCol l)).values) z).trans
    ((congrArg (fun p ↦ ∑ x ∈ range (2 ^ s.τ 5), KeccakGkr.eqAt p x *
      ofK (((leanIsaInstance prog s).column (toI prog s q) (outCol l)).values.getD x 0)) hz).trans
      (Finset.sum_congr rfl hs))
  constructor
  · intro h'
    exact hsum.symm.trans h'
  · intro h'
    exact hsum.trans h'

/-- The region's difference at step `w` of a candidate's reading, in the Keccak reduction's
terms. -/
theorem delta_eq (q : Column (verifierLayout prog s).stackLog) (l : Fin 25) {w : ℕ}
    (hw : w < 2 ^ s.τ 5) :
    (keccakRegion prog s).delta ((leanIsaInstance prog s).keccakColumn (keccakRegion prog s)
        (toI prog s q)) l w =
      ofK (KeccakGkr.laneWord (KeccakGkr.roundsFrom 0 12
          (KeccakGkr.inState (s.τ 5) (qkOf (verifierLayout prog s) q) 0 w)) l) -
        ofK (qkOf (verifierLayout prog s) q (w + 2 ^ s.τ 5 * (25 + l.val))) := by
  unfold KeccakRegion.delta
  rw [dite_eq_left (show w < 2 ^ (keccakRegion prog s).logSteps from hw)]
  have h0 := state_eq_inState prog s q 0 (by norm_num) ⟨w, hw⟩
  have h1 := word_eq_qkOf prog s q (25 + l.val) (by omega) ⟨w, hw⟩
  simp only [Nat.mul_zero] at h0
  refine congrArg₂ (fun a b ↦ ofK a - ofK b) ?_ ?_
  · exact congrArg (fun S ↦ stateLanes (keccakSegment 0 S) l) h0
  · exact h1

/-- **The Keccak predicate at the table sumcheck's point is the Keccak reduction's `midAgree`**
at the point's low `τ_KECCAK` coordinates. -/
theorem auxAt_iff_midAgree (q : Column (verifierLayout prog s).stackLog) (pt : List E)
    (hpt : s.τ 5 ≤ pt.length) (hτ : s.τ 5 ≤ (leanIsaInstance prog s).τmax) :
    (leanIsaInstance prog s).auxAt pt (toI prog s q) ↔
      KeccakGkr.midAgree (s.τ 5) (qkOf (verifierLayout prog s) q) (pt.take (s.τ 5)) := by
  have hmin : min (keccakRegion prog s).logSteps (leanIsaInstance prog s).τmax = s.τ 5 :=
    min_eq_left hτ
  have hlen : (pt.take (s.τ 5)).length = s.τ 5 := by simp [hpt]
  show (∀ r ∈ some (keccakRegion prog s), _) ↔ _
  simp only [Option.mem_def, Option.some.injEq, forall_eq']
  rw [hmin]
  unfold KeccakRegion.HoldsOn KeccakGkr.midAgree
  constructor
  · intro h l hl
    have hz := (KeccakZero.zeroOnHi_full _ hlen).mp (h ⟨l, hl⟩)
    unfold KeccakGkr.stepMle
    rw [← sub_eq_zero, ← Finset.sum_sub_distrib]
    refine Eq.trans (Finset.sum_congr rfl fun w hw ↦ ?_) hz
    rw [keccakZero_eqAt, delta_eq prog s q ⟨l, hl⟩ (Finset.mem_range.1 hw), mul_sub]
  · intro h l
    refine (KeccakZero.zeroOnHi_full _ hlen).mpr ?_
    have hz := h l.val l.isLt
    unfold KeccakGkr.stepMle at hz
    rw [← sub_eq_zero, ← Finset.sum_sub_distrib] at hz
    refine Eq.trans (Finset.sum_congr rfl fun w hw ↦ ?_) hz
    rw [keccakZero_eqAt, delta_eq prog s q l (Finset.mem_range.1 hw), mul_sub]

/-- Cell `n` of `QKECCAK` of a candidate's reading is `q_keccak`'s word `n`. -/
theorem keccakCol_getD (q : Column (verifierLayout prog s).stackLog) {n : ℕ}
    (hn : n < 2 ^ (s.τ 5 + 6)) :
    ((leanIsaInstance prog s).column (toI prog s q) keccakCol).values.getD n 0 =
      qkOf (verifierLayout prog s) q n := by
  have hlt := (blocks prog s).offset_add_pow_le_total (keccakBlock prog s)
  have hfit := blocks_fits prog s
  have h2 : 2 ^ (s.τ 5 + 6) = 2 ^ (blocks prog s).size (keccakBlock prog s) := by
    rw [size_keccakBlock]
  have h := column_committed prog s (toI prog s q) keccakCol not_isVirtual_keccakCol ⟨n, hn⟩
  rw [Vector.getD, Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem
    (by rw [Vector.size_toArray]; exact hn), Option.getD_some, qkOf_eq,
    Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem
      (by rw [Vector.size_toArray]; unfold leanIsaμ at hfit ⊢; omega), Option.getD_some]
  refine h.trans ?_
  simp only [Vector.getElem_toArray]
  congr 1
  rw [Nat.add_comm]
  rfl

/-- **A claim on `QKECCAK` is the Keccak reduction's column claim**: at `τ_KECCAK + 6`
coordinates, the program's claim on `QKECCAK` holds of a candidate on the stack exactly when its
value is the extension of `q_keccak`'s words at its point. -/
theorem qkHolds_iff (q : Column (verifierLayout prog s).stackLog) (c : Verifier.ColumnClaim)
    (hc : c.column = qkeccak) (hl : c.point.length = s.τ 5 + 6) :
    StackClaim.Holds (verifierLayout prog s).stackLog (c.stackClaim (verifierLayout prog s)) q ↔
      c.value = ∑ n ∈ range (2 ^ (s.τ 5 + 6)),
        KeccakGkr.eqAt c.point n * ofK (qkOf (verifierLayout prog s) q n) := by
  obtain ⟨col, pt, v⟩ := c
  simp only at hc hl ⊢
  subst hc
  let z : Vector E (s.τ 5 + 6) := ⟨pt.toArray, by simpa using hl⟩
  have hnm : refCol keccakCol ∉ keccakOutputColumns := by decide +kernel
  have h := wireHolds_iff prog s keccakCol z v q
  rw [refCol_keccakCol, wireHolds_of_not_mem prog s hnm] at h
  refine (show StackClaim.Holds _ ((⟨qkeccak, pt, v⟩ : Verifier.ColumnClaim).stackClaim _) q ↔ _
    from h).trans ?_
  have hs : ∀ n ∈ range (2 ^ (s.τ 5 + 6)), KeccakGkr.eqAt pt n *
      ofK (((leanIsaInstance prog s).column (toI prog s q) keccakCol).values.getD n 0) =
      KeccakGkr.eqAt pt n * ofK (qkOf (verifierLayout prog s) q n) :=
    fun n hn ↦ by rw [keccakCol_getD prog s q (Finset.mem_range.1 hn)]
  have hsum := (eval₂Mle_eq_sum_eqAt
    (((leanIsaInstance prog s).column (toI prog s q) keccakCol).values) z).trans
    (Finset.sum_congr rfl hs)
  constructor
  · intro h'
    exact h'.symm.trans hsum
  · intro h'
    exact hsum.trans h'.symm

end Reading

/-! ## The table seam as the public input's doom -/

section TablePub

variable (prog : LeanIsaProgram) (s : Sizes)

/-- The program's claims hold claims on all 25 output lanes at the low `τ_KECCAK` coordinates of
the point `pt`. -/
def OutLanesAt (claims : List Verifier.ColumnClaim) (pt : List E) : Prop :=
  ∀ l : Fin 25, ∃ v, (⟨113 + l.val, pt.take (s.τ 5), v⟩ : Verifier.ColumnClaim) ∈ claims

/-- The `KECCAK` table is a sumcheck table. -/
theorem keccak_sumcheckTable : (leanIsaInstance prog s).SumcheckTable (opIdx 5) :=
  sumcheckTable_opIdx (fl := some (keccakRegion prog s)) prog s 5

/-- The table sumcheck's output holds a claim on every output lane at the point's low `τ_KECCAK`
coordinates. -/
theorem outLane_mem_tableOut (st : SumcheckRound.Stmt (Data (leanIsaInstance prog s)) E
      (leanIsaInstance prog s).τmax)
    (v : Vector E (leanIsaInstance prog s).tableColumns) (l : Fin 25) :
    ∃ c ∈ (tableOut (leanIsaInstance prog s) st v).2.columns.toList,
      refCol c.col = 113 + l.val ∧ c.point.toList = st.2.1.reverse.toList.take (s.τ 5) := by
  let j : (leanIsaInstance prog s).SumcheckTables := ⟨opIdx 5, keccak_sumcheckTable prog s⟩
  let i : Fin ((leanIsaInstance prog s).width j.1) := (outCol l).2
  let k := TableSumcheck.columnPos (leanIsaInstance prog s) ⟨j, i⟩
  have hk : (TableSumcheck.finalClaims (leanIsaInstance prog s) st.2.1.reverse v)[k] =
      TableSumcheck.finalClaim (leanIsaInstance prog s) st.2.1.reverse v k := by
    simp [TableSumcheck.finalClaims]
  refine ⟨(TableSumcheck.finalClaims (leanIsaInstance prog s) st.2.1.reverse v)[k], ?_, ?_, ?_⟩
  · simp only [tableOut, Vector.toList_append, List.mem_append]
    exact Or.inr (Vector.mem_toList_iff.mpr (Vector.getElem_mem _))
  · rw [hk, ← refCol_outCol l]
    simp only [TableSumcheck.finalClaim, k]
    rw [Equiv.symm_apply_apply]
    rfl
  · rw [hk]
    simp only [TableSumcheck.finalClaim, k, Equiv.symm_apply_apply, M3Instance.lowPoint,
      Vector.toList_cast, Vector.toList_take]
    rfl

/-- **The table seam on the wire is the public-input phase's doom**: at the verifier's layout,
if the table seam holds of no candidate at the protocol's output, then, at the table sumcheck's
point `pt`, no candidate of `C` satisfies the program's claims read on it (`WireHolds`), the public
lines and the Keccak predicate at `pt`, `C` being read off the same commitment; and the program's
claims hold claims on every output lane at `pt`'s low `τ_KECCAK` coordinates. -/
theorem tablePost_pubPre (cands' : Word → Set (∀ i, TheOracle (leanIsaInstance prog s) i))
    (input' : PublicInput) (C : List Ev → Set (Column (verifierLayout prog s).stackLog))
    (hC : ∀ h q, q ∈ C h → ∀ W, firstWord h = some W → (fun _ ↦ toI prog s q) ∈ cands' W)
    (claims : List Verifier.ColumnClaim) (h : List Ev)
    (hpost : TablePost (leanIsaInstance prog s) cands' input' refCol claims h) :
    ∃ pt : Vector E (leanIsaInstance prog s).τmax, OutLanesAt s claims pt.toList ∧
      PubPre prog s (verifierLayout prog s) C (toI prog s) (WireHolds prog s) claims input' pt h := by
  obtain ⟨W, tout, hW, hR, hin, hcl, st, v, rfl⟩ := hpost
  refine ⟨st.2.1.reverse, fun l ↦ ?_, ?_⟩
  · obtain ⟨c, hc, hcol, hpt⟩ := outLane_mem_tableOut prog s st v l
    refine ⟨c.value, ?_⟩
    have := hcl c hc
    rw [hcol, hpt] at this
    exact this
  · rintro q hq ⟨hcols, hpl, haux⟩
    refine hR _ (hC h q hq W hW) ⟨fun c hc ↦ ?_, by rw [hin]; exact hpl, haux⟩
    exact (wireHolds_iff prog s c.col c.point c.value q).mp (hcols _ (hcl c hc))

end TablePub

/-! ## The Keccak phase -/

section Phase

variable (prog : LeanIsaProgram) (s : Sizes) (C : List Ev → Set (Column (verifierLayout prog
    s).stackLog))

/-- **The Keccak phase's precondition**: at some point `pt` of the table sumcheck at whose low
`τ_KECCAK` coordinates the claims hold claims on every output lane, no candidate satisfies the
claims read on it (`WireHolds`) and the Keccak predicate at `pt`. -/
def KeccakPre (claims : List Verifier.ColumnClaim) (h : List Ev) : Prop :=
  ∃ pt : Vector E (leanIsaInstance prog s).τmax, OutLanesAt s claims pt.toList ∧
    Doomed C (fun q ↦ ClaimsHoldBy (WireHolds prog s) claims q ∧
      (leanIsaInstance prog s).auxAt pt.toList (toI prog s q)) h

/-- **The Keccak phase's postcondition**, ring switching's precondition: the point has
`τ_KECCAK + 6` coordinates and there are 64 slices, and no candidate satisfies the claims left on
the stack and the slices of its `q_keccak`. -/
def KeccakOut (r : List Verifier.ColumnClaim × List E × List E) (h : List Ev) : Prop :=
  (r.2.1.length = s.τ 5 + 6 ∧ r.2.2.length = 64) ∧
    Doomed C (fun q ↦ ColumnClaimsHold (verifierLayout prog s) r.1 q ∧
      KeccakGkr.slicesTrue (s.τ 5) (qkOf (verifierLayout prog s) q) r.2.1 r.2.2) h

/-- The output lanes' claims of a claim list. -/
abbrev lanesOf (claims : List Verifier.ColumnClaim) : List Verifier.ColumnClaim :=
  claims.filter fun c ↦ c.column ∈ keccakOutputColumns

/-- The program's check on the lanes. -/
abbrev LanesOk (claims : List Verifier.ColumnClaim) : Prop :=
  (lanesOf claims).map (·.column) = keccakOutputColumns ∧
    ∀ c ∈ lanesOf claims, c.point = ((lanesOf claims).headD default).point

/-- The Keccak phase is the check on the lanes, then the reduction on them. -/
theorem keccakPhase_eq (layout : Verifier.Layout) (claims : List Verifier.ColumnClaim) :
    keccakPhaseClaims layout claims = (VerifierProgram.require (LanesOk claims)).bind fun _ ↦
      (verifyKeccak (layout.tableLogHeights.getD opKeccak 0) ((lanesOf claims).headD default).point
        ((lanesOf claims).map (·.value))).bind fun r ↦
        VerifierProgram.ret (claims.filter (fun c ↦ c.column ∉ keccakOutputColumns) ++ r.1, r.2.1,
            r.2.2) :=
  rfl

/-- Once the check passes, the lanes' common point is the low `τ_KECCAK` coordinates of `pt`. -/
theorem inst_eq {claims : List Verifier.ColumnClaim} {pt : List E} (hok : LanesOk claims)
    (hout : OutLanesAt s claims pt) :
    ((lanesOf claims).headD default).point = pt.take (s.τ 5) := by
  obtain ⟨v, hv⟩ := hout 0
  have hmem : (⟨113 + (0 : Fin 25).val, pt.take (s.τ 5), v⟩ : Verifier.ColumnClaim) ∈
      lanesOf claims := by
    rw [List.mem_filter]
    refine ⟨hv, ?_⟩
    simp [keccakOutputColumns_eq]
  exact (hok.2 _ hmem).symm

/-- The lanes are 25. -/
theorem length_lanesOf {claims : List Verifier.ColumnClaim} (hok : LanesOk claims) :
    (lanesOf claims).length = 25 := by
  have := congrArg List.length hok.1
  rw [List.length_map, keccakOutputColumns_eq] at this
  simpa using this

/-- The column of lane `i` is `113 + i`. -/
theorem column_lanesOf {claims : List Verifier.ColumnClaim} (hok : LanesOk claims) (i : ℕ)
    (hi : i < (lanesOf claims).length) : ((lanesOf claims)[i]).column = 113 + i := by
  have h := congrArg (·[i]?) hok.1
  simp only [List.getElem?_map, List.getElem?_eq_getElem hi, keccakOutputColumns_eq,
    Option.map_some] at h
  rw [List.getElem?_range (by rw [length_lanesOf hok] at hi; exact hi)] at h
  simpa using h

/-- **The doom carried in is the reduction's precondition**: once the check on the lanes passes,
a candidate satisfying the reduction's output claims against the committed middle state,
`midAgree` and the claims off the lanes satisfies the claims and the Keccak predicate at `pt`. -/
theorem gkrPre_of_keccakPre {claims : List Verifier.ColumnClaim} {h : List Ev}
    (hpre : KeccakPre prog s C claims h) (hok : LanesOk claims) :
    Doomed C (fun q ↦ KeccakGkr.outClaimsTrueMid (s.τ 5) (qkOf (verifierLayout prog s) q)
        ((lanesOf claims).headD default).point ((lanesOf claims).map (·.value)) ∧
      KeccakGkr.midAgree (s.τ 5) (qkOf (verifierLayout prog s) q)
        ((lanesOf claims).headD default).point ∧
      ColumnClaimsHold (verifierLayout prog s)
        (claims.filter fun c ↦ c.column ∉ keccakOutputColumns) q) h := by
  obtain ⟨pt, hout, hdoom⟩ := hpre
  have hinst := inst_eq s hok hout
  have hτ : s.τ 5 ≤ (leanIsaInstance prog s).τmax :=
    (leanIsaInstance prog s).τ_le_τmax ⟨opIdx 5, keccak_sumcheckTable prog s⟩
  have hptl : s.τ 5 ≤ pt.toList.length := by simpa using hτ
  have hil : ((lanesOf claims).headD default).point.length = s.τ 5 := by
    rw [hinst]; simpa using hτ
  intro q hq ⟨hmid, hagree, hR⟩
  refine hdoom q hq ⟨fun c hc ↦ ?_, ?_⟩
  · by_cases hm : c.column ∈ keccakOutputColumns
    · have hcl : c ∈ lanesOf claims := List.mem_filter.mpr ⟨hc, by simpa using hm⟩
      obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hcl
      have hi25 : i < 25 := by rw [length_lanesOf hok] at hi; exact hi
      have hcol := column_lanesOf hok i hi
      have hpt := hok.2 _ hcl
      have hval : ((lanesOf claims).map (·.value)).getD i 0 = ((lanesOf claims)[i]).value := by
        simp [hi]
      have e : (lanesOf claims)[i] = ⟨113 + (⟨i, hi25⟩ : Fin 25).val,
          ((lanesOf claims).headD default).point, ((lanesOf claims)[i]).value⟩ := by
        rw [← hcol, ← hpt]
      rw [e, laneHolds_iff prog s q ⟨i, hi25⟩ _ hil]
      exact (hmid i hi25).trans hval
    · rw [wireHolds_of_not_mem prog s hm]
      exact hR c (List.mem_filter.mpr ⟨hc, by simpa using hm⟩)
  · rw [auxAt_iff_midAgree prog s q pt.toList hptl hτ, ← hinst]
    exact hagree

open Classical in
/-- **The Keccak phase's specification**: from the doom the table sumcheck and the public input
leave (`KeccakPre`) to the doom ring switching starts from (`KeccakOut`), by the Keccak
reduction's specification (`KeccakGkr.gkrSpec`): lead `L₀ · 6/|E|` (the segment and lane
challenges), every later group at most `L₀ · 46/|E|`. -/
noncomputable def keccakPhaseSpec (hst : Stable C) {L₀ : ℕ} (hcard : ∀ h, (C h).ncard ≤ L₀)
    {εmax T : ℝ≥0∞} (hT : T ≤ εmax) (h46 : (L₀ : ℝ≥0∞) * KeccakGkr.errE 46 ≤ εmax)
    (claims : List Verifier.ColumnClaim) :
    Spec (keccakPhaseClaims (verifierLayout prog s) claims) (KeccakPre prog s C claims)
      (KeccakOut prog s C) εmax ((L₀ : ℝ≥0∞) * KeccakGkr.errE 6) T :=
  haveI := finite_column (verifierLayout prog s).stackLog
  have hP : s.τ 5 - 4 + 4 = s.τ 5 := by
    have := s.minSteps_le
    simp only [keccakMinStepsLog] at this
    omega
  have hτ : (verifierLayout prog s).tableLogHeights.getD opKeccak 0 = s.τ 5 - 4 + 4 := by
    rw [tableLogHeights_keccak, hP]
  let inst := ((lanesOf claims).headD default).point
  let output := (lanesOf claims).map (·.value)
  let claims' := claims.filter fun c ↦ c.column ∉ keccakOutputColumns
  let qk := qkOf (verifierLayout prog s)
  let R := fun q ↦ ColumnClaimsHold (verifierLayout prog s) claims' q
  Spec.congr (keccakPhase_eq _ claims).symm <|
  (Spec.require (Post := fun _ h ↦ LanesOk claims ∧ KeccakPre prog s C claims h)
      (fun _ hp hc ↦ ⟨hc, hp⟩)).bind' fun _ ↦
  if hi : inst.length = s.τ 5 - 4 + 4 then
    if ho : output.length = 25 then
      Spec.congr (by rw [hτ]; rfl) <|
      ((Sound.Spec.retInv ((KeccakGkr.gkrSpec hst hcard R qk (s.τ 5 - 4) hi ho hT h46).mono
          (Pre' := fun h ↦ LanesOk claims ∧ KeccakPre prog s C claims h)
          (fun h hp ↦ by rw [hP]; exact gkrPre_of_keccakPre prog s C hp.2 hp.1)
          (fun _ _ hq ↦ hq) le_rfl le_rfl le_rfl)
        (fun r ↦ (∀ c ∈ r.1, c.column = qkeccak ∧ c.point.length = inst.length + 6) ∧
          r.2.1.length = inst.length + 6 ∧ r.2.2.length = 64)
        (fun l r hl ↦ ⟨retOK_verifyKeccak _ _ _ (by omega) l r hl,
          retOK_verifyKeccak_point _ _ _ (by omega) hi l r hl⟩)).bind' fun r ↦
        (Spec.ret (Post := KeccakOut prog s C) (claims' ++ r.1, r.2.1, r.2.2)).mono
          (fun h ⟨hpost, hshape, hpl, hsl⟩ ↦ by
            rw [hi, hP] at hpl hshape
            refine ⟨⟨hpl, hsl⟩, fun q hq ⟨hcl, hsq⟩ ↦ hpost q hq ⟨fun c hc ↦ ?_, ?_, ?_⟩⟩
            · obtain ⟨hcc, hcp⟩ := hshape c hc
              rw [hP]
              refine ⟨hcc, hcp, ?_⟩
              exact (qkHolds_iff prog s q c hcc hcp).mp
                (hcl c (List.mem_append_right _ hc))
            · rw [hP]; exact hsq
            · exact fun c hc ↦ hcl c (List.mem_append_left _ hc))
          (fun _ _ h ↦ h) le_rfl le_rfl le_rfl)
    else specOfFalse fun _ hp ↦ ho (by simp [output, length_lanesOf hp.1])
  else specOfFalse fun _ hp ↦ by
    obtain ⟨pt, hout, -⟩ := hp.2
    have hτ' : s.τ 5 ≤ (leanIsaInstance prog s).τmax :=
      (leanIsaInstance prog s).τ_le_τmax ⟨opIdx 5, keccak_sumcheckTable prog s⟩
    refine hi ?_
    rw [hP]
    show ((lanesOf claims).headD default).point.length = s.τ 5
    rw [inst_eq s hp.1 hout]
    simpa using hτ'

end Phase

end
end LeanVM.Protocol.EndToEnd.Front
