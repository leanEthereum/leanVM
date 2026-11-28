/-
  LeanVM.Guest.B1.VerifySub.PhOodRingOod

  `verify_sub`'s out-of-domain phase: its grind, `squeeze_point_from` and the value's read run
  `readOod`.
-/

module

public import LeanVM.Guest.B1.VerifySub.Sizes
public import LeanVM.Guest.B1.VerifySub.PhOodRingGrind
public import LeanVM.Guest.B1.Fs.MessageComplete
public import LeanVM.Guest.B1.Fs.SqueezePoint
import LeanVM.Guest.ValRef
import LeanVM.Guest.Data.ValNames.«verify_sub»

/-!
# The out-of-domain phase

`vsOodT` (statements `436 .. 487`, checked by the kernel): the grind's nonce at `stream·g^10`
joins the root's two words (`fs_grind_squeeze` at two waiting scalars), the nonce's permutation,
`grind_check` of `OOD_GRIND_BITS = 15` inlined with the tables folded into its reads
(`gcInlineAt`), the dispatch to `squeeze_point_from__L{stackLog}` from the permutation's
challenge, and `opening_message__L1_L1`, whose first word is the value, at `stream·g^11`.
`phOod`: they run `readOod stackLog` from `vsF2`, the point at `ood_z`, the value at `ood_value`
waiting in `vsF3`.
-/

namespace LeanVM.Guest.B1.VerifySub

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

/-- `verify_sub`'s statements 436 to 441: the nonce, its cells and the permutation. -/
def vsOodPreT : List Stmt := (
  .atom (.load (.n 494) (.n 55) 10) ::
  .atom (.copy (.n 495) (.n 494)) ::
  .atom (.const (.n 496) (word 0 4)) ::
  .atom (.const (.n 497) (word 0 0)) ::
  .atom (.const (.n 498) (word 0 0)) ::
  .atom (.keccak [.n 135, .n 136, .n 138, .n 139, .n 495, .n 496, .n 497, .n 498, .n 129, .n 130, .n 131, .n 132, .n 133] [.n 499, .n 500, .n 501, .n 502, .n 503, .n 504, .n 505, .n 506, .n 507, .n 508, .n 509, .n 510, .n 511] false false) ::
  [])

/-- `verify_sub`'s statements 484 to 487: the point, the value's message. -/
def vsOodPostT : List Stmt := (
  .dispatch (.n 489) ["squeeze_point_from__L16", "squeeze_point_from__L17", "squeeze_point_from__L18", "squeeze_point_from__L19", "squeeze_point_from__L20", "squeeze_point_from__L21", "squeeze_point_from__L22", "squeeze_point_from__L23", "squeeze_point_from__L24", "squeeze_point_from__L25", "squeeze_point_from__L26", "squeeze_point_from__L27", "squeeze_point_from__L28", "squeeze_point_from__L29", "squeeze_point_from__L30"] [.n 507, .n 508, .n 509, .n 510, .n 511, .n 499, .n 22] [.n 566, .n 567, .n 568, .n 569, .n 570] ::
  .atom (.const (.n 571) (word 2048 0)) ::
  .atom (.mul (.n 572) (.n 55) (.n 571)) ::
  .call "opening_message__L1_L1" [.n 566, .n 567, .n 568, .n 569, .n 570, .n 572, .n 23] [.n 573, .n 574, .n 575, .n 576, .n 577, .n 578, .n 579, .n 580] ::
  [])

/-- `verify_sub`'s statements 436 to 487. -/
def vsOodT : List Stmt := vsOodPreT ++ gcInlineAt 15 512 178 (.n 500) (.n 4) ++ vsOodPostT

theorem vsOodT_eq : (vsPre.drop 436).take 52 = vsOodT := stmtsEqb_sound (by decide +kernel)

theorem spfNames_getElem (j : ℕ) (hj : j < 15) :
    ["squeeze_point_from__L16", "squeeze_point_from__L17", "squeeze_point_from__L18", "squeeze_point_from__L19", "squeeze_point_from__L20", "squeeze_point_from__L21", "squeeze_point_from__L22", "squeeze_point_from__L23", "squeeze_point_from__L24", "squeeze_point_from__L25", "squeeze_point_from__L26", "squeeze_point_from__L27", "squeeze_point_from__L28", "squeeze_point_from__L29", "squeeze_point_from__L30"][j]'(by simpa using hj) =
      spfName (j + 16) := by
  interval_cases j <;> rfl

theorem sqN_length : ∀ (n : ℕ) (s : Fs), (s.squeezeN n).1.length = n
  | 0, _ => rfl
  | n + 1, s => by simp only [Fs.squeezeN, List.length_cons, sqN_length n]

theorem sqN_pend : ∀ (n : ℕ) (s : Fs), s.pend = [] → (s.squeezeN n).2.pend = []
  | 0, _, h => h
  | n + 1, s, _ => sqN_pend n s.squeeze.2 rfl

/-- **`n + 1` challenges after a grind**: the ground one, then `n` squeezes of its capacity. -/
theorem runsFromG_sampleN (n : ℕ) (cap : List E) (c : E) :
    RunsFromG (VerifierProgram.sampleChallenges (n + 1)) cap c []
      (c :: ((⟨cap, []⟩ : Fs).squeezeN n).1) ((⟨cap, []⟩ : Fs).squeezeN n).2 := by
  have h := (runsFromG_sample cap c).bind
    (f := fun x => do let xs ← VerifierProgram.sampleChallenges n; return x :: xs)
    ((runsTo_sampleN n ⟨cap, []⟩).bind
      (f := fun xs => (pure (c :: xs) : VerifierProgram (List E))) (runsTo_ret _ _))
  simpa [VerifierProgram.sampleChallenges] using h

/-- **The out-of-domain sample**, sound. -/
theorem phOod : PhOod := by
  intro bytecode κ L C Vm σ rets R
  have Z := R.sizesOk
  obtain ⟨-, hwin, h11⟩ := R.pre
  -- the root's waiting cells and the seed's zeros
  have hR := R.slice vsReadsT_eq
  simp only [vsReadsT, Stmt.HoldsList, Stmt.Holds, List.map_cons, List.map_nil] at hR
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -,
    -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -,
    a101, a102, -, a104, a105, -⟩ := hR
  have c135 : σ (.n 135) = σ (.n 134) := a101
  have c136 : σ (.n 136) = word 0 1 := a102
  have c138 : σ (.n 138) = σ (.n 137) := a104
  have c139 : σ (.n 139) = word 0 1 := a105
  -- the phase
  have h := R.slice vsOodT_eq
  rw [vsOodT, holdsList_append, holdsList_append] at h
  simp only [vsOodPreT, Stmt.HoldsList, Stmt.Holds] at h
  obtain ⟨a436, a437, a438, a439, a440, a441, hg⟩ := h
  have hwt : WinTabs L.read (σ (.n 4) * gen ^ 178) := winTabs_of_expWinTab hwin
  obtain ⟨hpow, hpost⟩ := gcInlineAt_sound R.hκ h11 L (by decide) hwt hg
  simp only [vsOodPostT, Stmt.HoldsList, Stmt.Holds, List.map_cons, List.map_nil] at hpost
  obtain ⟨⟨j, hj, hsel, hspf⟩, a485, a486, hom, -⟩ := hpost
  have c495 : σ (.n 495) = σ (.n 494) := a437
  have c496 : σ (.n 496) = word 0 4 := a438
  have c497 : σ (.n 497) = 0 := by rw [show σ (.n 497) = word 0 0 from a439, word_zero]
  have c498 : σ (.n 498) = 0 := by rw [show σ (.n 498) = word 0 0 from a440, word_zero]
  -- the nonce's permutation
  set nonce := vsOodNonce σ with hnonce
  set S := (vsF2 σ).nonceState nonce with hS
  have habs : (vsF2 σ).absorb nonce dsPowNonce =
      ⟨(vsF2 σ).cap, (vsF2 σ).pend ++ [(nonce, dsPowNonce)]⟩ := by
    simp [Fs.absorb, vsF2, rateScalars]
  have hK := keccakA_fs (s := (vsF2 σ).absorb nonce dsPowNonce) a441 (by rw [habs]; simp [vsF2])
    (by
      rw [habs]
      simp only [List.map_cons, List.map_nil, c135, c136, c138, c139, c496, c497, c498]
      rfl)
  have hcell : ∀ k : Fin 13, ∀ hk : k.val < 13,
      σ ([.n 499, .n 500, .n 501, .n 502, .n 503, .n 504, .n 505, .n 506, .n 507, .n 508, .n 509,
        .n 510, .n 511] : List V)[k.val] = cellsOfState S false k :=
    fun k hk ↦ outs_eq hK k (by simp)
  have e499 : σ (.n 499) = cellsOfState S false 0 := hcell 0 (by decide)
  have e500 : σ (.n 500) = cellsOfState S false 1 := hcell 1 (by decide)
  have hcap : [σ (.n 507), σ (.n 508), σ (.n 509), σ (.n 510), σ (.n 511)] = capOf S := by
    simp only [capOf]
    rw [← hcell 8 (by decide), ← hcell 9 (by decide), ← hcell 10 (by decide),
      ← hcell 11 (by decide), ← hcell 12 (by decide)]
    rfl
  have hok : (vsF2 σ).GrindOk Whir.oodGrindingBits nonce :=
    (grindOk_iff (by decide) nonce).mpr (by rw [← hS, ← e500]; exact hpow)
  have hG := runsToG_grind (by decide) (vsF2 σ) nonce (hok.resolve_left (by decide))
  -- the point
  set μ := (vsLayout bytecode σ).stackLog with hμ
  have hj15 : j < 15 := by simpa using hj
  have hjμ : j = μ - Whir.minOpenLog := by
    have e1 := dispatchIdx_eq (x := σ (.n 489)) (j := j) (by exact hj15) hsel
    have e2 := dispatchIdx_eq (x := σ (.n 489)) (j := μ - Whir.minOpenLog)
      (by have : Whir.openArms = 15 := rfl; have : Whir.minOpenLog = 16 := rfl; have := Z.st1;
          have := Z.st2; omega) Z.sizeSel
    rw [← e1, e2]
  have hmo : Whir.minOpenLog = 16 := rfl
  have hμ16 : j + 16 = μ := by have := Z.st1; omega
  rw [spfNames_getElem j hj15] at hspf
  have hM := (squeeze_point_from_holds (j + 16)
    (List.mem_map.mpr ⟨j + 10, List.mem_range.mpr (by omega), by omega⟩) L.read _ _).mp
    (R.hle _ _ _ hspf)
  simp only [MeaningSqueezePointFrom,
    show j + 16 - 1 = j + 15 by omega] at hM
  obtain ⟨hpt, hfs⟩ := hM
  rw [hcap] at hpt hfs
  rw [e499, ← Keccak.challengeOf_cells] at hpt
  -- the value
  have hM2 := (opening_message_holds (1, 1) (by decide) L.read _ _).mp (R.hle _ _ _ hom)
  simp only [MeaningOpeningMessage] at hM2
  obtain ⟨xs, hxl, hxc, hxo, -⟩ := hM2
  obtain ⟨v, rfl⟩ : ∃ v, xs = [v] := by
    match xs, hxl with
    | [v], _ => exact ⟨v, rfl⟩
  have e572 : σ (.n 572) = vsStream σ * gen ^ 11 := by
    rw [a486, show σ (.n 571) = word 2048 0 from a485, show (2048 : ℕ) = 2 ^ 11 from rfl,
      gen_word 11 (by decide)]
    rfl
  have hv : vsOodValue L.read σ = v := by
    have := wordsAt_eq hxo
    simp only [List.length_cons, List.length_nil] at this
    simp only [vsOodValue, this]
    rfl
  have hz : vsOodZ L.read σ μ = challengeOf S :: ((⟨capOf S, []⟩ : Fs).squeezeN (j + 15)).1 := by
    have := wordsAt_eq hpt
    rw [List.length_cons, sqN_length, show j + 15 + 1 = μ by omega] at this
    exact this
  refine ⟨?_, ?_, by rw [hz]; exact hpt⟩
  · intro k hk
    simp only [List.length_cons, List.length_nil] at hk
    interval_cases k
    · refine (loadHolds_mul_gen_pow _ _ _ _ _).mpr ?_
      rw [show nonce = σ (.n 494) from c495]
      exact a436
    · refine (loadHolds_mul_gen_pow _ _ _ _ _).mpr ?_
      rw [hv]
      have := (loadHolds_mul_gen_pow _ _ _ _ _).mp (e572 ▸ hxc 0 (by simp))
      simpa using this
  · -- the run
    have hs3 : (((⟨capOf S, []⟩ : Fs).squeezeN (j + 15)).2).absorb v dsObserve = vsF3 L.read σ := by
      have hp := sqN_pend (j + 15) ⟨capOf S, []⟩ rfl
      simp only [Fs.absorb, hp, List.length_nil, rateScalars, List.nil_append]
      simp only [vsF3, ← hfs, hv]
      rfl
    have hRS := RunsFromG.bind (runsFromG_sampleN (j + 15) (capOf S) (challengeOf S))
      (f := fun z => (do let value ← VerifierProgram.readScalar; return (fun x ↦ eqEval z x, value) :
        VerifierProgram StackClaim))
      ((runsTo_readE _ v).bind (f := fun value => (pure (fun x ↦ eqEval
        (challengeOf S :: ((⟨capOf S, []⟩ : Fs).squeezeN (j + 15)).1) x, value) :
          VerifierProgram StackClaim)) (runsTo_ret _ _))
    have hrun := hG.bindFrom (f := fun _ => (do
      let z ← VerifierProgram.sampleChallenges (j + 15 + 1)
      let value ← VerifierProgram.readScalar
      return (fun x ↦ eqEval z x, value) : VerifierProgram StackClaim)) hRS
    rw [show j + 15 + 1 = μ by omega] at hrun
    refine RunsTo.of_eq hrun rfl ?_ ?_ hs3
    · rw [hv]; rfl
    · rw [hz, hv]

end
end LeanVM.Guest.B1.VerifySub
