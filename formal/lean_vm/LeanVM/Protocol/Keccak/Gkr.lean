/-
  LeanVM.Protocol.Keccak.Gkr

  The round-by-round soundness of the Keccak reduction `verifyKeccak`: a doom specification
  from "no candidate makes the table's output claims true" to "no candidate makes the column
  claims and slice claims the reduction leaves true", with the escape of every challenge.
-/

module

public import LeanVM.Protocol.Keccak.GkrTail

/-!
# `verifyKeccak` as a specification

`verify_keccak` (`crates/verifier/src/keccak.rs:235-294`) is `gkrProg` (by `rfl`): the segment and
lane challenges, `committed`, twelve layers, the committed outputs' opening and the inputs' opening
(`inputTail`). Candidates are stacks of type `β`, each with its `q_keccak` column `qk q` (word `n`
at `qk q n`); `C h` is the set of candidates a history binds (`Stable`, at most `L₀`).

**Alive predicates**, in order (`R` is carried throughout):

| after | a candidate `q` is alive when |
| --- | --- |
| the start | `outClaimsTrueMid` and `midAgree` at `inst` |
| `j` of the six segment and lane challenges | the mismatch table's extension at them is zero (`ZeroOn`) |
| `committed` | the first claim holds of `q`'s states, and `committed` opens `q`'s middle state |
| each layer | as in `layerSpec`; the open value is carried |
| the outputs' slot rounds | as in `sumcheckSpec`, for the family `Fo` |
| `word` and the check | the column claim at `(inst, ρ)` holds; the claim at depth `12` is carried |
| the inputs' opening | as in `inputSpec` |

**Escape bounds** (each group, `|E| = 2^192`): the start's six challenges `L₀/|E|` each (lead
`L₀·6/|E|`); per layer, `s` at `L₀·46/|E|`, each of the `P + 1` pack rounds and `11` position
rounds at `L₀·3/|E|`, `β` at `L₀·2/|E|`; the openings' `6 + 4 + 6` rounds at `L₀·2/|E|`. The
largest is `L₀·46/|E|`, which is the hypothesis `h46 : L₀·46/|E| ≤ εmax`; for `L₀ ≤ 2^12` it is
below `2^-174 < 2^-128` (`EndToEnd.Sound.phase_errors`).

`gkrSpec` states it with `Pre := Doomed C (outClaimsTrueMid ∧ midAgree ∧ R)`. The statement in
terms of `keccakF` of the inputs needs `RegionValid` (the committed middle state is twelve
rounds of the input at every step): `gkrSpec_regionValid`, from `Doomed C (outClaimsTrue ∧
RegionValid ∧ R)` to doom of the reduction's claims with `RegionValid` carried. `RegionValid`
cannot be dropped from the carried predicate: `inst` is drawn before this phase, and a middle
state wrong at some step but agreeing with twelve rounds of the input at `inst` passes every
check here (the phase drawing `inst` charges that, `zeroOn_escape`).
-/

namespace LeanVM.Protocol.KeccakGkr

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Protocol.EndToEnd.Front LeanVM.Protocol.EndToEnd.Complete Finset
open scoped ENNReal

@[expose] public section

/-! ## The program -/

/-- `verify_keccak`, the `do` block's join points inlined. -/
def gkrProg (h : ℕ) (inst output : List E) : VerifierProgram (List ColumnClaim × List E × List E) :=
  VerifierProgram.sampleChallenges keccakSegmentBits >>= fun segment ↦
  VerifierProgram.sampleChallenges keccakLaneBits >>= fun lanesPt ↦
  VerifierProgram.readScalar >>= fun committed ↦
  keccakLayers h (List.range keccakDepth) (firstClaim inst segment lanesPt output committed) >>=
    fun claim ↦
  keccakOpen h (firstClaim inst segment lanesPt output committed) 1 (keccakSegments - 1)
    committed >>= fun x ↦
  VerifierProgram.readScalar >>= fun word ↦
  VerifierProgram.require (x.2.1.headD 0 * word = x.2.2) >>= fun _ ↦
  inputTail h claim [(⟨qkeccak, inst.take 4 ++ inst.drop 4 ++ x.1, word⟩ : ColumnClaim)]

theorem verifyKeccak_eq (h : ℕ) (inst output : List E) :
    verifyKeccak h inst output = gkrProg h inst output := rfl

/-! ## The committed outputs' check -/

/-- **The outputs' check**: a true column claim and the check give the slot rounds' last
claim. -/
theorem final_out (P : ℕ) (col : ℕ → K) {inst segment lanesPt output : List E}
    (hi : inst.length = P + 4) (committed : E) {slot : List E} (hslot : slot.length = 6)
    (word value : E)
    (htrue : colTrue (P + 4) col ⟨qkeccak, inst.take 4 ++ inst.drop 4 ++ slot, word⟩)
    (hc : ((foldAll slot (keccakSlotWeights (P + 4)
      (firstClaim inst segment lanesPt output committed) 1 1)).headD []).headD 0 * word = value) :
    value = Fo (P + 4) col inst segment lanesPt slot := by
  rw [← hc, fold_out hi committed hslot, Fo, cubeSum_full _ hslot]
  refine congrArg (HMul.hMul _) ?_
  obtain ⟨-, -, hv⟩ := htrue
  change word = _ at hv
  rw [hv, List.take_append_drop, ← hslot, col_split hi, Qo, hslot]
  rfl

/-! ## The specification -/

variable {β : Type} [Finite β] {C : List Ev → Set β} {L₀ : ℕ} {εmax T : ℝ≥0∞}

/-- The alive predicate after `committed`. -/
def AliveC (qk : β → ℕ → K) (R : β → Prop) (P : ℕ) (inst segment lanesPt output : List E)
    (committed : E) (q : β) : Prop :=
  ClaimTrue (statesAt (P + 4) (qk q) 0) P (firstClaim inst segment lanesPt output committed) ∧
    (OpenTrue (P + 4) (qk q) inst segment lanesPt committed ∧ R q)

/-- The postcondition: the column claims and the slice claims. -/
def KeccakPost (qk : β → ℕ → K) (R : β → Prop) (P : ℕ) (C : List Ev → Set β)
    (res : List ColumnClaim × List E × List E) (h : List Ev) : Prop :=
  Doomed C (fun q ↦ (∀ c ∈ res.1, colTrue (P + 4) (qk q) c) ∧
    slicesTrue (P + 4) (qk q) res.2.1 res.2.2 ∧ R q) h

open Classical in
/-- After `committed`: the layers and the two openings. Lead `0`. -/
noncomputable def midSpec (hst : Stable C) (hcard : ∀ h, (C h).ncard ≤ L₀) (R : β → Prop)
    (qk : β → ℕ → K) (P : ℕ) {inst segment lanesPt : List E} (output : List E)
    (hi : inst.length = P + 4) (hs : segment.length = 1) (hl : lanesPt.length = 5)
    (committed : E) (hT : T ≤ εmax)
    (h46 : (L₀ : ℝ≥0∞) * errE 46 ≤ εmax) :
    Spec (keccakLayers (P + 4) (List.range keccakDepth)
        (firstClaim inst segment lanesPt output committed) >>= fun claim ↦
      keccakOpen (P + 4) (firstClaim inst segment lanesPt output committed) 1 (keccakSegments - 1)
        committed >>= fun x ↦
      VerifierProgram.readScalar >>= fun word ↦
      VerifierProgram.require (x.2.1.headD 0 * word = x.2.2) >>= fun _ ↦
      inputTail (P + 4) claim [(⟨qkeccak, inst.take 4 ++ inst.drop 4 ++ x.1, word⟩ : ColumnClaim)])
      (Doomed C (AliveC qk R P inst segment lanesPt output committed))
      (KeccakPost qk R P C) εmax 0 T :=
  have h0 : (0 : ℝ≥0∞) ≤ εmax := zero_le
  have h2 : (L₀ : ℝ≥0∞) * errE 2 ≤ εmax := le_trans (by gcongr; exact errE_mono (by norm_num)) h46
  have h2' : (L₀ : ℝ≥0∞) * errE 2 + 0 ≤ εmax := by rw [add_zero]; exact h2
  let first := firstClaim inst segment lanesPt output committed
  (Spec.congr (p := keccakLayers (P + 4) (List.range' 0 12) first) (by rw [List.range_eq_range']; rfl)
    (layersSpec (T := 0) hst hcard (fun q ↦ OpenTrue (P + 4) (qk q) inst segment lanesPt committed ∧ R q)
      qk P h46 h2' 12 0 rfl first (firstClaim_shape committed hi hs))).bind' fun claim ↦
  if hc : ClaimShape P claim then
    (Spec.congr (keccakOpen_eq (P + 4) first 1 (keccakSegments - 1) committed).symm <|
      Spec.congr (p := sumcheck committed 3 (List.replicate 6 none) >>= fun x ↦
        VerifierProgram.ret (x.1, (foldAll x.1 (keccakSlotWeights (P + 4) first 1 1)).headD
            [], x.2))
        (by rw [qkeccakSlotBits_eq]; rfl) <|
      ((sumcheckSpec (T := 0) hst hcard
        (fun q ↦ ClaimTrue (statesAt (P + 4) (qk q) 12) P claim ∧ R q)
        (Fo_plainFamily (P + 4) qk inst segment lanesPt) (count := 3) (by norm_num)
        (by norm_num) h0 h2' 6 [] committed (by simp)).mono
        (fun _ (hd : ClaimShape P claim ∧ Doomed C _ _) ↦ Doomed.mono hd.2
          fun q ⟨hv, hct, hR⟩ ↦ ⟨hct, by
            rw [OpenTrue, hv, Fo_nil (P + 4) (qk q) inst hs hl], hR⟩)
        (fun _ _ h' ↦ h') le_rfl le_rfl le_rfl).bind' fun x ↦
      (Spec.ret (Post := fun (x' : List E × List E × E) h ↦ x'.1.length = 6 ∧
          x'.2.1 = (foldAll x'.1 (keccakSlotWeights (P + 4) first 1 1)).headD [] ∧
          Doomed C (fun q ↦ x'.2.2 = Fo (P + 4) (qk q) inst segment lanesPt x'.1 ∧
            (ClaimTrue (statesAt (P + 4) (qk q) 12) P claim ∧ R q)) h)
        (x.1, (foldAll x.1 (keccakSlotWeights (P + 4) first 1 1)).headD [], x.2)).mono
        (fun _ hd ↦ ⟨hd.1, rfl, by simpa using hd.2⟩) (fun _ _ h' ↦ h') le_rfl le_rfl
        le_rfl).bind' fun x ↦
    if hx : x.1.length = 6 ∧
        x.2.1 = (foldAll x.1 (keccakSlotWeights (P + 4) first 1 1)).headD [] then
      ((doomRead (T := 0) hst _ h0).mono (fun _ hd ↦ hd.2.2) (fun _ _ h' ↦ h') le_rfl le_rfl
        le_rfl).bind' fun word ↦
      (Spec.require
        (Pre := Doomed C (fun q ↦ x.2.2 = Fo (P + 4) (qk q) inst segment lanesPt x.1 ∧
            (ClaimTrue (statesAt (P + 4) (qk q) 12) P claim ∧ R q)))
        (Post := fun _ h ↦ Doomed C (fun q ↦ ClaimTrue (statesAt (P + 4) (qk q) 12) P claim ∧
          ((∀ c ∈ [(⟨qkeccak, inst.take 4 ++ inst.drop 4 ++ x.1, word⟩ : ColumnClaim)],
            colTrue (P + 4) (qk q) c) ∧ R q)) h)
        fun _ hd hcheck ↦ Doomed.mono hd fun q ⟨hct, hcol, hR⟩ ↦ ⟨by
          rw [hx.2] at hcheck
          exact final_out P (qk q) hi committed hx.1 word _ (hcol _ (List.mem_singleton_self _))
            hcheck, hct, hR⟩).bind' fun _ ↦
      (inputSpec hst hcard _ qk P claim hc _ hT h2).mono (fun _ h' ↦ h')
        (fun res h' (hr : res.1 = _ ∧ _) ↦ Doomed.mono hr.2 fun q ⟨hcol, hsl, hR⟩ ↦
          ⟨hsl, by rw [← hr.1]; exact hcol, hR⟩) le_rfl le_rfl le_rfl
    else Spec.dead.mono (fun _ hd ↦ hx ⟨hd.1, hd.2.1⟩) (fun _ _ h' ↦ h') le_rfl le_rfl le_rfl
  else Spec.dead.mono (fun _ hd ↦ hc hd.1) (fun _ _ h' ↦ h') le_rfl le_rfl le_rfl

/-! ## The start -/

/-- The escape bound of the `i`-th of `n` zero-test coordinates (`1` past them, never used). -/
noncomputable def ztE (n i : ℕ) : ℝ≥0∞ := if i < n then errE 1 else 1

omit [Finite β] in
theorem zt_escape (δ : β → ℕ → E) (R : β → Prop) (pre : List E) {n : ℕ}
    (hpre : pre.length + n = 6) (acc : List E) (q : β)
    (hq : ¬ (ZeroOn (δ q) (pre ++ acc) 6 ∧ R q)) :
    avgE (fun c ↦ indE (ZeroOn (δ q) (pre ++ (acc ++ [c])) 6 ∧ R q)) ≤ ztE n acc.length := by
  unfold ztE
  split_ifs with hn
  · by_cases hR : R q
    · refine (avgE_mono fun c ↦ indE_mono fun hc ↦ ?_).trans
        (zeroOn_escape (δ q) (acc := pre ++ acc) (by simp; omega) fun h ↦ hq ⟨h, hR⟩)
      rw [List.append_assoc]; exact hc.1
    · exact (avgE_mono fun c ↦ indE_mono (q := False) fun h ↦ hR h.2).trans
        ((avgE_le_of_le fun c ↦ (indE_of_not not_false).le).trans zero_le)
  · exact avgE_indE_le_one _

theorem keccakSegmentBits_eq : keccakSegmentBits = 1 := by decide

theorem lead_eq (L₀ : ℕ) :
    (∑ i ∈ range 1, (L₀ : ℝ≥0∞) * ztE 6 (0 + i)) +
        ((∑ i ∈ range 5, (L₀ : ℝ≥0∞) * ztE 5 (0 + i)) + 0) = (L₀ : ℝ≥0∞) * errE 6 := by
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, ztE, errE]
  norm_num
  ring

open Classical in
/-- **The Keccak reduction** (`verify_keccak`, `keccak.rs:235-294`), round by round: from
doom of "the output-lane claims (against the committed middle state) and the middle state's
claims hold at `inst`" to doom of "the column claims and the `64` slice claims it leaves hold".
Lead `L₀·6/|E|` (the segment and lane challenges); every other group's lead is at most
`L₀·46/|E| ≤ εmax`; the follower's lead `T` after the slices. -/
noncomputable def gkrSpec (hst : Stable C) (hcard : ∀ h, (C h).ncard ≤ L₀) (R : β → Prop)
    (qk : β → ℕ → K) (P : ℕ) {inst output : List E} (hi : inst.length = P + 4)
    (ho : output.length = 25) (hT : T ≤ εmax) (h46 : (L₀ : ℝ≥0∞) * errE 46 ≤ εmax) :
    Spec (verifyKeccak (P + 4) inst output)
      (Doomed C (fun q ↦ outClaimsTrueMid (P + 4) (qk q) inst output ∧
        midAgree (P + 4) (qk q) inst ∧ R q))
      (KeccakPost qk R P C) εmax ((L₀ : ℝ≥0∞) * errE 6) T :=
  have h0 : (0 : ℝ≥0∞) ≤ εmax := zero_le
  let δ := fun q ↦ startDelta (P + 4) (qk q) inst output
  Spec.congr (verifyKeccak_eq (P + 4) inst output).symm <|
  Spec.congr (by rw [gkrProg, keccakSegmentBits_eq]; rfl) <|
  ((doomSampleN (εmax := εmax) hst hcard (fun acc q ↦ ZeroOn (δ q) ([] ++ acc) 6 ∧ R q)
    (ztE 6) (fun acc q hq ↦ zt_escape δ R [] (by simp) acc q hq) 1 []).mono
    (fun _ hd ↦ Doomed.mono hd fun q ⟨hz, hR⟩ ↦ by
      obtain ⟨h1, h2⟩ := claims_of_zeroOn (P + 4) (qk q) inst output (by simpa using hz)
      exact ⟨h1, h2, hR⟩)
    (fun _ _ h' ↦ h') le_rfl (le_of_eq (lead_eq L₀)) le_rfl).bind' fun segment ↦
  if hs : segment.length = 1 then
    ((doomSampleN (εmax := εmax) hst hcard (fun acc q ↦ ZeroOn (δ q) (segment ++ acc) 6 ∧ R q)
      (ztE 5) (fun acc q hq ↦ zt_escape δ R segment (by rw [hs]) acc q hq) 5 []).mono
      (fun _ (hd : segment.length = 1 ∧ _) ↦ by simpa using hd.2) (fun _ _ h' ↦ h') le_rfl
      le_rfl le_rfl).bind' fun lanesPt ↦
    if hl : lanesPt.length = 5 then
      (Spec.readE (Pre := fun h ↦ lanesPt.length = 5 ∧
          Doomed C (fun q ↦ ZeroOn (δ q) (segment ++ ([] ++ lanesPt)) 6 ∧ R q) h)
        (Post := fun c h ↦ Doomed C (AliveC qk R P inst segment lanesPt output c) h)
        (fun h₀ c hd ↦ (Doomed.append hst rfl).mpr (Doomed.mono hd.2 fun q ⟨htrue, hopen, hR⟩ ↦
          ⟨by
            rw [List.nil_append]
            exact zeroOn_of_first (P + 4) P rfl (qk q) hi hs hl ho c hopen htrue, hR⟩))
        h0).bind' fun committed ↦
      midSpec hst hcard R qk P output hi hs hl committed hT h46
    else Spec.dead.mono (fun _ hd ↦ hl hd.1) (fun _ _ h' ↦ h') le_rfl le_rfl le_rfl
  else Spec.dead.mono (fun _ hd ↦ hs hd.1) (fun _ _ h' ↦ h') le_rfl le_rfl le_rfl

/-! ## The statement against `keccakF` -/

theorem outClaims_iff_of_regionValid (h : ℕ) (col : ℕ → K) (inst output : List E)
    (hv : RegionValid h col) :
    outClaimsTrue h col inst output ↔ outClaimsTrueMid h col inst output := by
  have hx : ∀ x ∈ range (2 ^ h), keccakF1600 (inState h col 0 x) = roundsFrom 12 12 (inState h col 1 x) :=
    fun x hx ↦ by rw [keccakF_eq, hv x (Finset.mem_range.1 hx)]
  have e : ∀ l, stepMle h inst (fun x ↦ laneWord (keccakF1600 (inState h col 0 x)) l) =
      stepMle h inst (fun x ↦ laneWord (roundsFrom 12 12 (inState h col 1 x)) l) := fun l ↦
    Finset.sum_congr rfl fun x hxr ↦ by simp only; rw [hx x hxr]
  unfold outClaimsTrue outClaimsTrueMid
  simp only [e]

/-- **The Keccak reduction against `keccakF`**: from doom of "the output-lane claims against
`keccakF` of the inputs hold at `inst`, the region is valid, and `R`", to doom of the reduction's
claims with `RegionValid` and `R` carried. -/
noncomputable def gkrSpec_regionValid (hst : Stable C) (hcard : ∀ h, (C h).ncard ≤ L₀)
    (R : β → Prop) (qk : β → ℕ → K) (P : ℕ) {inst output : List E} (hi : inst.length = P + 4)
    (ho : output.length = 25) (hT : T ≤ εmax) (h46 : (L₀ : ℝ≥0∞) * errE 46 ≤ εmax) :
    Spec (verifyKeccak (P + 4) inst output)
      (Doomed C (fun q ↦ outClaimsTrue (P + 4) (qk q) inst output ∧
        RegionValid (P + 4) (qk q) ∧ R q))
      (KeccakPost qk (fun q ↦ RegionValid (P + 4) (qk q) ∧ R q) P C) εmax
      ((L₀ : ℝ≥0∞) * errE 6) T :=
  (gkrSpec hst hcard (fun q ↦ RegionValid (P + 4) (qk q) ∧ R q) qk P hi ho hT h46).mono
    (fun _ hd ↦ Doomed.mono hd fun _ ⟨hmid, _, hv, hR⟩ ↦
      ⟨(outClaims_iff_of_regionValid _ _ _ _ hv).2 hmid, hv, hR⟩)
    (fun _ _ h' ↦ h') le_rfl le_rfl le_rfl

/-- A column given on `Fin (2^(h + 6))`, read as words of `ℕ` (`0` past the end). -/
def colOfFin {h : ℕ} (c : Fin (2 ^ (h + 6)) → K) : ℕ → K :=
  fun n ↦ if hn : n < 2 ^ (h + 6) then c ⟨n, hn⟩ else 0

end
end LeanVM.Protocol.KeccakGkr
