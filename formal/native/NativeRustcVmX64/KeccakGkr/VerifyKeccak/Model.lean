module

public import NativeVm.Math.Keccak.Facts
public import NativeRustcVmX64.KeccakGkr.VerifyLayer.Model
public import NativeRustcVmX64.Bus.GkrModel
public import NativeRustcVm.KeccakGkr.Open

/-!
# `verifyKeccak` as `verify_keccak` runs it (x86-64)

The model's phase in the order of the Rust's calls (`verifyKeccak_eq`): the grind, the segment
and lane challenges, the committed outputs' claim, the layers one by one (`layersFrom`), the
opening of the committed outputs (`restOpen`), the sumcheck over the pack's instances and the
opening of the inputs (`restSum`). A step's run, `some` or `none` (`run_bind_some`,
`run_bind_none`); sizes: the layers keep the point's (`layer_point_size`), the first claim's point
(`first_point`), an opening's slot and weights (`open_weights_size`). (Arch-neutral; copied from
the AArch64 proof's `VerifyKeccak/Model`, which x86-64 files may not import.)
-/

namespace NativeRustcVmX64.KeccakGkr.VerifyKeccak

open NativeVm.Model LeanVM.Parameters LeanVM.Protocol.Verifier

@[expose] public section

/-- `verifyKeccak`'s result. -/
abbrev Res := Array ColumnClaimW × Array EW × Array EW

/-- The phase's grind's bits. -/
abbrev gBits : Nat := grindingBits (keccakSegmentBits + keccakLaneBits)

/-- After the committed outputs' column claim: the sumcheck over the pack's instances, the
opening of the inputs, the final check. -/
def restSum (logSteps : Nat) (claim : KeccakClaimW) (outputs : Array ColumnClaimW) : VM Res := do
  let (low, value) ← sumcheckPlain claim.value 3 4
  let (slot, weights, value) ← keccakOpen logSteps claim 0 keccakSegments value
  let slices ← readScalars kBits
  require (multilinearEval claim.mu low * dot weights slices == value)
  pure (outputs, low ++ claim.point.extract 0 (logSteps - 4) ++ slot, slices)

/-- After the opening's sumcheck: the committed word, its check, then `restSum`. -/
def restWord (logSteps : Nat) (inst slot : Array EW) (weights : Array EW) (value : EW)
    (claim : KeccakClaimW) : VM Res := do
  let word ← readScalar
  require (weights.getD 0 0 * word == value)
  restSum logSteps claim
    #[(⟨qkeccak, inst.extract 0 4 ++ inst.extract 4 inst.size ++ slot, word⟩ : ColumnClaimW)]

/-- After the layers: the opening of the committed outputs, then `restWord`. -/
def restOpen (logSteps : Nat) (inst : Array EW) (first : KeccakClaimW) (committed : EW)
    (claim : KeccakClaimW) : VM Res := do
  let (slot, weights, value) ← keccakOpen logSteps first 1 (keccakSegments - 1) committed
  restWord logSteps inst slot weights value claim

/-- The layers from `j` on. -/
def layersFrom (logSteps j : Nat) (c : KeccakClaimW) : VM KeccakClaimW :=
  (List.range' j (keccakDepth - j)).foldlM (fun c step ↦ verifyKeccakLayer logSteps step c) c

/-- After the first claim: the layers from `j`, then `restOpen`. -/
def afterLayers (logSteps j : Nat) (inst : Array EW) (first : KeccakClaimW) (committed : EW)
    (c : KeccakClaimW) : VM Res := do
  let claim ← layersFrom logSteps j c
  restOpen logSteps inst first committed claim

/-- After the lane challenges. -/
def afterLane (logSteps : Nat) (inst output segment lanePoint : Array EW) : VM Res := do
  let committed ← readScalar
  let first := keccakFirstClaim inst segment lanePoint output committed
  afterLayers logSteps 0 inst first committed first

/-- After the segment challenge. -/
def afterSeg (logSteps : Nat) (inst output segment : Array EW) : VM Res := do
  let lanePoint ← sampleChallenges keccakLaneBits
  afterLane logSteps inst output segment lanePoint

/-- After the grind. -/
def afterGrind (logSteps : Nat) (inst output : Array EW) : VM Res := do
  let segment ← sampleChallenges keccakSegmentBits
  afterSeg logSteps inst output segment

end

public section

theorem run_bind_some {α β : Type} {x : VM α} {f : α → VM β} {s s' : TState} {a : α}
    (h : x.run s = some (a, s')) : (x >>= f).run s = (f a).run s' := by
  simp only [StateT.run_bind, h]
  rfl

theorem run_bind_none {α β : Type} {x : VM α} {f : α → VM β} {s : TState}
    (h : x.run s = none) : (x >>= f).run s = none := by
  simp only [StateT.run_bind, h]
  rfl

theorem require_true {b : Bool} (h : b = true) (s : TState) :
    (require b).run s = some ((), s) := by
  subst h; rfl

theorem require_false {b : Bool} (h : b = false) (s : TState) : (require b).run s = none := by
  subst h; rfl

theorem pure_run {α : Type} (a : α) (s : TState) : (pure a : VM α).run s = some (a, s) := rfl

theorem keccakLayers_eq (logSteps : Nat) (c : KeccakClaimW) :
    keccakLayers logSteps c = layersFrom logSteps 0 c := by
  rw [NativeVm.Model.keccakLayers, layersFrom, List.range_eq_range']
  rfl

/-- **The phase in the Rust's order.** -/
theorem verifyKeccak_grind (logSteps : Nat) (inst output : Array EW) :
    NativeVm.Model.verifyKeccak logSteps inst output =
      (grind gBits >>= fun _ ↦ afterGrind logSteps inst output) := by
  unfold NativeVm.Model.verifyKeccak afterGrind afterSeg afterLane afterLayers restOpen restWord
    restSum
  have h : 1 < keccakSegments := by decide
  simp only [h, ↓reduceIte, keccakLayers_eq]
  rfl

theorem segBits_eq : keccakSegmentBits = 1 := by decide

theorem laneBits_eq : keccakLaneBits = 5 := by decide

theorem afterGrind_run {logSteps : Nat} {inst output seg : Array EW} {s s' : TState}
    (h : (sampleChallenges 1).run s = some (seg, s')) :
    (afterGrind logSteps inst output).run s = (afterSeg logSteps inst output seg).run s' := by
  unfold afterGrind; rw [segBits_eq]; exact run_bind_some h

theorem afterSeg_run {logSteps : Nat} {inst output seg lp : Array EW} {s s' : TState}
    (h : (sampleChallenges 5).run s = some (lp, s')) :
    (afterSeg logSteps inst output seg).run s = (afterLane logSteps inst output seg lp).run s' := by
  unfold afterSeg; rw [laneBits_eq]; exact run_bind_some h

theorem afterLane_run {logSteps : Nat} {inst output seg lp : Array EW} {s s' : TState} {c : EW}
    (h : readScalar.run s = some (c, s')) :
    (afterLane logSteps inst output seg lp).run s =
      (afterLayers logSteps 0 inst (keccakFirstClaim inst seg lp output c) c
        (keccakFirstClaim inst seg lp output c)).run s' :=
  run_bind_some h

theorem afterLane_none {logSteps : Nat} {inst output seg lp : Array EW} {s : TState}
    (h : readScalar.run s = none) : (afterLane logSteps inst output seg lp).run s = none :=
  run_bind_none h

theorem layersFrom_succ (logSteps : Nat) {j : Nat} (hj : j < keccakDepth) (c : KeccakClaimW) :
    layersFrom logSteps j c =
      (verifyKeccakLayer logSteps j c >>= layersFrom logSteps (j + 1)) := by
  rw [layersFrom, show keccakDepth - j = (keccakDepth - (j + 1)) + 1 by omega, List.range'_succ,
    List.foldlM_cons]
  rfl

theorem layersFrom_end (logSteps : Nat) (c : KeccakClaimW) :
    layersFrom logSteps keccakDepth c = pure c := by
  rw [layersFrom, Nat.sub_self]
  rfl

/-- A layer, `some`: the next layers' run. -/
theorem afterLayers_some {logSteps j : Nat} (hj : j < keccakDepth) {inst : Array EW}
    {first c c' : KeccakClaimW} {committed : EW} {s s' : TState}
    (h : (verifyKeccakLayer logSteps j c).run s = some (c', s')) :
    (afterLayers logSteps j inst first committed c).run s =
      (afterLayers logSteps (j + 1) inst first committed c').run s' := by
  unfold afterLayers
  rw [layersFrom_succ logSteps hj, bind_assoc]
  exact run_bind_some h

/-- A layer, `none`. -/
theorem afterLayers_none {logSteps j : Nat} (hj : j < keccakDepth) {inst : Array EW}
    {first c : KeccakClaimW} {committed : EW} {s : TState}
    (h : (verifyKeccakLayer logSteps j c).run s = none) :
    (afterLayers logSteps j inst first committed c).run s = none := by
  unfold afterLayers
  rw [layersFrom_succ logSteps hj, bind_assoc]
  exact run_bind_none h

/-- After the last layer. -/
theorem afterLayers_end {logSteps : Nat} {inst : Array EW} {first c : KeccakClaimW}
    {committed : EW} :
    afterLayers logSteps keccakDepth inst first committed c =
      restOpen logSteps inst first committed c := by
  unfold afterLayers
  rw [layersFrom_end, pure_bind]

/-- A layer keeps the claim's point's size. -/
theorem layer_point_size {logSteps step : Nat} {c c' : KeccakClaimW} {s s' : TState}
    (h : (verifyKeccakLayer logSteps step c).run s = some (c', s')) :
    c'.point.size = c.point.size := by
  rw [VerifyLayer.run_eq] at h
  cases h1 : (readScalars productBits).run s with
  | none => rw [h1] at h; cases h
  | some p =>
    rw [h1, Option.bind_some] at h
    split at h
    · cases h2 : (grind (grindingBits (productBits - 1))).run p.2 with
      | none => rw [h2] at h; cases h
      | some q =>
        rw [h2, Option.bind_some] at h
        cases h3 : (sumcheck (polyEval p.1 (VerifyLayer.sqS q.2).1) 3 (c.point.map some)).run
          (VerifyLayer.sqS q.2).2 with
        | none => rw [h3] at h; cases h
        | some r =>
          rw [h3, Option.bind_some] at h
          cases h4 : (sumcheckPlain r.1.2 4 keccakLocalBits).run r.2 with
          | none => rw [h4] at h; cases h
          | some u =>
            rw [h4, Option.bind_some] at h
            cases h5 : (readScalars 3).run u.2 with
            | none => rw [h5] at h; cases h
            | some v =>
              rw [h5, Option.bind_some] at h
              split at h
              · cases h6 : (grind (grindingBits 2)).run v.2 with
                | none => rw [h6] at h; cases h
                | some w =>
                  rw [h6, Option.bind_some, Option.some.injEq, Prod.mk.injEq] at h
                  rw [← h.1]
                  show r.1.1.size = _
                  obtain ⟨⟨xs, cv⟩, s3⟩ := r
                  rw [← NativeRustcVm.Sumcheck.sumcheckFn_getElem?] at h3
                  have := Bus.Gkr.sumcheckFn_size _ _ _ _ h3
                  simpa using this
              · cases h
    · cases h

/-- The first claim's point: `inst`'s coordinates past the low four, then the segment's. -/
theorem first_point (inst segment lanePoint output : Array EW) (committed : EW) :
    (keccakFirstClaim inst segment lanePoint output committed).point =
      inst.extract 4 inst.size ++ segment := rfl

theorem first_point_size (inst segment lanePoint output : Array EW) (committed : EW)
    (hs : segment.size = 1) :
    (keccakFirstClaim inst segment lanePoint output committed).point.size = inst.size - 4 + 1 := by
  rw [first_point, Array.size_append, Array.size_extract, hs]
  omega

/-- An opening's slot (6 challenges) and the rows it folds: 64 of 64 entries. -/
theorem open_weights_size {logSteps : Nat} {c : KeccakClaimW} {first count : Nat} {v : EW}
    {s s' : TState} {sl ws : Array EW} {v' : EW}
    (h : (keccakOpen logSteps c first count v).run s = some ((sl, ws, v'), s')) :
    sl.size = 6 ∧ ws.size = 64 := by
  cases h1 : (sumcheckPlain v 3 qkeccakSlotBits).run s with
  | none =>
    rw [NativeVm.Model.keccakOpen, run_bind_none h1] at h; cases h
  | some p =>
    obtain ⟨⟨slot, val⟩, s1⟩ := p
    rw [NativeVm.Model.keccakOpen, run_bind_some h1] at h
    simp only [pure_run, Option.some.injEq, Prod.mk.injEq] at h
    have hsl : slot.size = 6 := by
      rw [← NativeRustcVm.Sumcheck.sumcheckFn_none] at h1
      rw [Bus.Gkr.sumcheckFn_size _ _ _ _ h1]
      decide
    obtain ⟨⟨rfl, rfl, -⟩, -⟩ := h
    refine ⟨hsl, ?_⟩
    rw [NativeRustcVm.KeccakGkr.keccakOpen_rows]
    obtain ⟨hs, hr⟩ := NativeVm.Math.Keccak.slotWeights_size logSteps c first count
    have hsz := NativeRustcVm.KeccakGkr.openRows_size slot
      (NativeVm.Model.keccakSlotWeights logSteps c first count) (t := slot.size) le_rfl
    rw [hs] at hsz
    exact NativeRustcVm.KeccakGkr.openRows_row_size slot _ (fun r h ↦ hr r (by omega)) le_rfl 0
      (by rw [hsz, hsl]; decide)

/-- The phase's grind: `bitLength 5 - 3 = 0` bits. -/
theorem gBits_eq : gBits = 0 := by decide

theorem bitLength_five : bitLength 5 = 3 := by decide

end

end NativeRustcVmX64.KeccakGkr.VerifyKeccak
