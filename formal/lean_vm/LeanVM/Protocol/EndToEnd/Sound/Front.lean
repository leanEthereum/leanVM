/-
  LeanVM.Protocol.EndToEnd.Sound.Front

  The front phases of leanVM's verifier at `f128`, composed: the bus and the table sumcheck, the
  public input and the Keccak reduction, on the one candidate the commitment's OOD sample leaves
  (`FrontIface`).
-/

module

public import LeanVM.Protocol.EndToEnd.Sound.Assemble
public import LeanVM.Protocol.EndToEnd.Sound.BusDepth
public import LeanVM.Protocol.EndToEnd.Front.TableFidLeanIsa
public import LeanVM.Protocol.EndToEnd.Front.KeccakBridge
public import LeanVM.Protocol.EndToEnd.Front.PubPhase
public import LeanVM.Protocol.EndToEnd.Complete.Public

/-!
# The front phases

`frontIface prog input : FrontIface computedBytecodeValue prog input (publicInputDigest input)`
composes W3's phase specifications on a constant candidate set `S` of at most one stack (`L₀ = 1`):

1. the bus phase and the table sumcheck (`busTableSpec_leanIsa`), from the commitment's doom read
   on the candidates `toI '' S` (`HDoom`) to the table seam (`TablePost`);
2. at the table sumcheck's point (`tablePost_pubPre`), the public input (`pubPhaseSpec`);
3. the Keccak reduction (`keccakPhaseSpec`), ending in `KeccakOut`: no candidate meets the claims
   left with true slices, which is `FrontPost`.

The public input's challenge and the Keccak reduction's six first challenges are one group, of
error `7/|E|`; the table sumcheck's final values are read before it (`TableFid.rows`), so it is
the bus and table phases' follower lead alone. Every other group's error, at `L₀ = 1`, is at most
`8/|E| = 2^-125` after its grind (`frontErrors`); the bus's fingerprint group, of error
`2^μ_bus/|E|`, is ground by `μ_bus − 3` bits, and is the lead when it grinds none.
-/

namespace LeanVM.Protocol.EndToEnd.Sound

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.Compile
open LeanVM.Protocol.Verifier LeanVM.Protocol.LeanIsa LeanVM.Protocol.EndToEnd.Front
open LeanVM.Protocol.EndToEnd.Complete (publicInputDigest)
open scoped ENNReal NNReal

@[expose] public section

/-! ## The errors at `L₀ = 1` -/

/-- `c/|E|` in `ℝ≥0∞`, from `ℝ≥0` over `Nat.card`. -/
theorem coe_div_natCard_E (c : ℕ) :
    ((((c : ℝ≥0) / (Nat.card E : ℝ≥0) : ℝ≥0)) : ℝ≥0∞) = (c : ℝ≥0∞) / Fintype.card E := by
  rw [Nat.card_eq_fintype_card, ENNReal.coe_div (by simp [Protocol.card_E]), ENNReal.coe_natCast,
    ENNReal.coe_natCast]

/-- `c/|E|` in `ℝ≥0∞`. -/
theorem coe_overE_E (c : ℕ) : ((overE c : ℝ≥0) : ℝ≥0∞) = (c : ℝ≥0∞) / Fintype.card E := by
  rw [overE, ENNReal.coe_div (by simp [Protocol.card_E]), ENNReal.coe_natCast, ENNReal.coe_natCast]

theorem div_E_add_div_E (a b : ℕ) :
    (a : ℝ≥0∞) / Fintype.card E + (b : ℝ≥0∞) / Fintype.card E =
      ((a + b : ℕ) : ℝ≥0∞) / Fintype.card E := by
  rw [ENNReal.div_add_div_same, Nat.cast_add]

/-- An error `N/|E|` with `N ≤ 8` needs no grind. -/
theorem le_εmsg {x : ℝ≥0∞} {N : ℕ} (hx : x = (N : ℝ≥0∞) / Fintype.card E) (hN : N ≤ 8) :
    x ≤ εmsg := by
  have := discount_le 0 N hN
  rwa [pow_zero, one_mul, ← hx] at this

theorem roundError_one (d : ℕ) : roundError 1 d = (d : ℝ≥0∞) / Fintype.card E := by
  rw [roundError, coe_div_natCard_E, Nat.cast_one, one_mul]

theorem lambdaError_one : lambdaError 1 = ((2 : ℕ) : ℝ≥0∞) / Fintype.card E := by
  rw [lambdaError, coe_div_natCard_E, Nat.cast_one, one_mul]

theorem unitError_one : unitError 1 = ((1 : ℕ) : ℝ≥0∞) / Fintype.card E := by
  rw [unitError, Nat.cast_one, one_mul, ENNReal.div_eq_inv_mul, mul_one]

theorem mul_errE_one (d : ℕ) :
    ((1 : ℕ) : ℝ≥0∞) * KeccakGkr.errE d = (d : ℝ≥0∞) / Fintype.card E := by
  rw [KeccakGkr.errE, Nat.cast_one, one_mul, ENNReal.div_eq_inv_mul, mul_comm]

/-- The Keccak reduction's lead at `L₀ = 1`: its segment and lane challenges. -/
noncomputable abbrev keccakLead : ℝ≥0∞ := ((1 : ℕ) : ℝ≥0∞) * KeccakGkr.errE 6

/-- The public input's lead at `L₀ = 1`: its challenge, then the Keccak reduction's lead. -/
noncomputable abbrev pubLead : ℝ≥0∞ := ((1 : ℕ) : ℝ≥0∞) * ((overE 1 : ℝ≥0) : ℝ≥0∞) + keccakLead

theorem pubLead_eq : pubLead = ((7 : ℕ) : ℝ≥0∞) / Fintype.card E := by
  rw [pubLead, keccakLead, mul_errE_one, coe_overE_E, Nat.cast_one, one_mul,
    ENNReal.div_add_div_same]
  norm_num

/-! ## The bus's depth -/

/-- **The bus's depth at admissible sizes is at most `41`**: the push side's leaves are the three
framework seeds and every opcode table's push flushes, each at most `2^32` rows. -/
theorem μBus_le_of_admissible {prog : LeanIsaProgram} {s : Sizes} (hs : s.Admissible prog) :
    (leanIsaInstance prog s).μBus ≤ 41 := by
  have hτ : ∀ t, s.τ t ≤ 32 := fun t ↦
    max_le (Nat.clog_le_of_le_pow (hs.2.2.1 t))
      (by fin_cases t <;> decide +kernel)
  have hc : ∀ t : Fin 6,
      ((LeanIsa.flushes (opIdx t)).filter fun f ↦ decide (f.1 = Side.push)).length ≤ 64 := by
    decide +kernel
  have hsum : ∑ t : Fin 6, ((LeanIsa.flushes (opIdx t)).filter fun f ↦
      decide (f.1 = Side.push)).length * 2 ^ s.τ t ≤ ∑ _t : Fin 6, 64 * 2 ^ 32 :=
    Finset.sum_le_sum fun t _ ↦
      Nat.mul_le_mul (hc t) (Nat.pow_le_pow_right (by norm_num) (hτ t))
  have hm : 2 ^ s.logMem ≤ 2 ^ 32 := Nat.pow_le_pow_right (by norm_num) hs.2.1
  have hb : 2 ^ prog.logSize ≤ 2 ^ 32 := Nat.pow_le_pow_right (by norm_num) prog.logSize_le
  have hp : (leanIsaInstance prog s).pushLeaves ≤ 2 ^ 41 := by
    rw [pushLeaves_leanIsa]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul] at hsum
    norm_num at hsum hm hb ⊢
    omega
  exact Nat.clog_le_of_le_pow hp

/-! ## The front phases -/

section Front

variable (prog : LeanIsaProgram) (input : PublicInput) (s : Sizes)
  (S : Set (Column (verifierLayout prog s).stackLog))

/-- The candidates as oracles of the instance, whatever the word. -/
def candsS : Word → Set (∀ i, TheOracle (leanIsaInstance prog s) i) :=
  fun _ ↦ (fun q ↦ fun _ ↦ toI prog s q) '' S

/-- The candidates on the stack, whatever the history. -/
abbrev CS : List Ev → Set (Column (verifierLayout prog s).stackLog) := fun _ ↦ S

variable {prog s S}

theorem candsS_finite (hS : S.Finite) (W : Word) : (candsS prog s S W).Finite := hS.image _

theorem candsS_ncard (hS : S.Finite) (h1 : S.ncard ≤ 1) (W : Word) :
    (candsS prog s S W).ncard ≤ 1 :=
  (Set.ncard_image_le hS).trans h1

/-- **The Keccak reduction, to `FrontPost`**, for at most `159` claims. -/
noncomputable def keccakPart (hS1 : S.ncard ≤ 1) {T : ℝ≥0∞} (hT : T ≤ εmsg)
    (claims : List Verifier.ColumnClaim) (hcl : claims.length ≤ 159) :
    Spec (keccakPhaseClaims (verifierLayout prog s) claims) (KeccakPre prog s (CS prog s S) claims)
      (FrontPost prog s S) εmsg keccakLead T :=
  (Spec.retInv (keccakPhaseSpec prog s (CS prog s S) (fun _ _ _ ↦ rfl) (L₀ := 1) (fun _ ↦ hS1) hT
      (by
        rw [KeccakGkr.grindingBits_product, mul_errE_one]
        exact discount_le 3 46 (by norm_num))
      (le_εmsg (mul_errE_one 3) (by norm_num)) claims)
    (fun r ↦ r.1.length ≤ claims.length + 1) (retOK_keccakPhase _ claims)).mono (fun _ h ↦ h)
    (fun r h ⟨⟨⟨hpl, hsl⟩, hD⟩, hlen⟩ ↦ by
      refine ⟨hpl, hsl, by simp only [maxStackedClaims]; omega, fun q hq hG ↦ hD q hq ⟨hG.1, ?_⟩⟩
      refine ⟨hpl, hsl, fun i hi ↦ ?_⟩
      have := (hG.2 ⟨i, hi⟩).symm
      rw [qkOf_eq_qkAt, placement_qkeccak]
      exact this)
    le_rfl le_rfl le_rfl

open Classical in
/-- **The public input at the table sumcheck's point `pt`, then the Keccak reduction**, after at
most `157` claims of the table phase. -/
noncomputable def pubPart (hS1 : S.ncard ≤ 1) {T : ℝ≥0∞} (hT : T ≤ εmsg)
    (cl : List Verifier.ColumnClaim) (hcl : cl.length ≤ 157)
    (pt : Vector E (leanIsaInstance prog s).τmax) :
    Spec ((Verifier.publicInputPhase (verifierLayout prog s) (publicInputDigest input)).bind
        fun pc ↦ keccakPhaseClaims (verifierLayout prog s) (cl ++ pc))
      (fun h ↦ OutLanesAt s cl pt.toList ∧
        PubPre prog s (verifierLayout prog s) (CS prog s S) (toI prog s) (WireHolds prog s) cl
          input pt h)
      (FrontPost prog s S) εmsg pubLead T :=
  if hout : OutLanesAt s cl pt.toList then
    ((Spec.retInv (pubPhaseSpec prog s (verifierLayout prog s) (CS prog s S) (toI prog s)
        (WireHolds prog s) cl input pt (pubLayoutHyp_verifierLayout prog s)
        (Complete.digestScalars_publicDigest input) (fun _ _ _ ↦ rfl) (L₀ := 1) (fun _ ↦ hS1)
        (εmax := εmsg) (T := keccakLead))
      (fun pc ↦ pc.length ≤ 2) (retOK_publicInputPhase _ _)).mono
      (Pre' := fun h ↦ OutLanesAt s cl pt.toList ∧
        PubPre prog s (verifierLayout prog s) (CS prog s S) (toI prog s) (WireHolds prog s) cl
          input pt h)
      (fun _ hp ↦ hp.2) (fun _ _ h ↦ h) le_rfl le_rfl le_rfl).bind' fun pc ↦
      if hpc : pc.length ≤ 2 then
        (keccakPart hS1 hT (cl ++ pc) (by rw [List.length_append]; omega)).mono
          (fun _ hp ↦ ⟨pt, fun l ↦ (hout l).imp fun _ hv ↦ List.mem_append_left _ hv, hp.1⟩)
          (fun _ _ h ↦ h) le_rfl le_rfl le_rfl
      else Spec.dead.mono (fun _ hp ↦ hpc hp.2) (fun _ _ h ↦ h) le_rfl le_rfl le_rfl
  else Spec.dead.mono (fun _ hp ↦ hout hp.1) (fun _ _ h ↦ h) le_rfl le_rfl le_rfl

/-- **The front phases' errors at `L₀ = 1`**, each at most `2^-125` after its grind. -/
theorem frontErrors (hs : s.Admissible prog) :
    abError (leanIsaInstance prog s) 1 < 1 ∧
    (2 : ℝ≥0∞)⁻¹ ^ busGrindingBits (leanIsaInstance prog s).μBus *
      (abError (leanIsaInstance prog s) 1 + 0) ≤ εmsg ∧
    roundError 1 4 ≤ εmsg ∧ interpLead 1 2 (lambdaError 1) ≤ εmsg ∧
    lambdaError 1 + 0 ≤ εmsg ∧ roundError 1 2 + 0 ≤ εmsg ∧ roundError 1 3 ≤ εmsg ∧
    pubLead ≤ εmsg ∧
    (2 : ℝ≥0∞)⁻¹ ^ xiGrindBits * (xiError (leanIsaInstance prog s) 1 + sumcheckLead
      (List.replicate ((verifierLayout prog s).tableLogHeights.foldl max 0) none) pubLead) ≤
        εmsg := by
  have hab : abError (leanIsaInstance prog s) 1 =
      ((2 ^ (leanIsaInstance prog s).μBus : ℕ) : ℝ≥0∞) / Fintype.card E := by
    rw [abError, coe_overE_E, Nat.cast_one, one_mul]
  refine ⟨?_, ?_, le_εmsg (roundError_one 4) (by norm_num), ?_, ?_, ?_,
    le_εmsg (roundError_one 3) (by norm_num), le_εmsg pubLead_eq (by norm_num), ?_⟩
  · rw [hab]
    exact div_card_lt_one (Nat.pow_le_pow_right (by norm_num)
      ((μBus_le_of_admissible hs).trans (by norm_num)))
  · rw [add_zero, hab]
    exact discount_le _ _ (le_two_pow_grindingBits _)
  · show unitError 1 + (unitError 1 + lambdaError 1) ≤ εmsg
    rw [unitError_one, lambdaError_one, div_E_add_div_E, div_E_add_div_E]
    exact le_εmsg rfl (by norm_num)
  · rw [add_zero]; exact le_εmsg lambdaError_one (by norm_num)
  · rw [add_zero]; exact le_εmsg (roundError_one 2) (by norm_num)
  · have hn : (verifierLayout prog s).tableLogHeights.foldl max 0 ≠ 0 := by
      rw [rounds_leanIsa prog s (fl := some (keccakRegion prog s))]
      show (leanIsaInstance prog s).τmax ≠ 0
      have : s.τ 5 ≤ (leanIsaInstance prog s).τmax :=
        (leanIsaInstance prog s).τ_le_τmax ⟨opIdx 5, keccak_sumcheckTable prog s⟩
      have h9 := s.minSteps_le
      simp only [keccakMinStepsLog] at h9
      omega
    obtain ⟨n, hn'⟩ := Nat.exists_eq_succ_of_ne_zero hn
    rw [hn', List.replicate_succ]
    simp only [sumcheckLead]
    rw [add_zero, show xiGrindBits = 0 by decide +kernel, pow_zero, one_mul, xiError,
      coe_div_natCard_E, Nat.cast_one, one_mul]
    refine le_εmsg rfl ?_
    have := B_leanIsa prog s
    omega

/-- **The front phases**, from the commitment's doom on `S` to `FrontPost`. -/
noncomputable def frontSpecAt (hs : s.Admissible prog) (hS : S.Finite) (hS1 : S.ncard ≤ 1)
    {T : ℝ≥0∞} (hT : T ≤ εmsg) :
    Spec (frontProg computedBytecodeValue (verifierLayout prog s) (publicInputDigest input))
      (fun h ↦ (∃ W, firstWord h = some W) ∧
        ∀ q ∈ S, ¬ M3Holds (leanIsaInstance prog s) input (toI prog s q))
      (FrontPost prog s S) εmsg εmsg T :=
  have he := frontErrors (prog := prog) (s := s) hs
  Spec.congr (by simp only [frontProg, VerifierProgram.bind_eq, VerifierProgram.bind_assoc]) <|
    ((Spec.retInv (busTableSpec_leanIsa prog s input (fl := some (keccakRegion prog s))
        (candsS prog s S) (candsS_finite hS) (candsS_ncard hS hS1) he.1 he.2.1 he.2.2.1
        he.2.2.2.1 he.2.2.2.2.1 he.2.2.2.2.2.1 he.2.2.2.2.2.2.1 he.2.2.2.2.2.2.2.1
        he.2.2.2.2.2.2.2.2)
      (fun cl ↦ cl.length ≤ 157) (retOK_busTable _ _)).mono
      (Pre' := fun h ↦ (∃ W, firstWord h = some W) ∧
        ∀ q ∈ S, ¬ M3Holds (leanIsaInstance prog s) input (toI prog s q))
      (fun _ hp ↦ by
        obtain ⟨⟨W, hW⟩, hd⟩ := hp
        exact ⟨W, hW, by rintro _ ⟨q, hq, rfl⟩ hin; exact hd q hq hin⟩)
      (fun _ _ h ↦ h) le_rfl (grindLead_le_of_discount he.2.1) le_rfl).bind' fun cl ↦
    if hcl : cl.length ≤ 157 then
      (Spec.exPre fun pt ↦ pubPart input hS1 hT cl hcl pt).mono
        (fun h hp ↦ tablePost_pubPre prog s (candsS prog s S) input (CS prog s S)
          (fun _ q hq _ _ ↦ ⟨q, hq, rfl⟩) cl h hp.1) (fun _ _ h ↦ h) le_rfl le_rfl le_rfl
    else Spec.dead.mono (fun _ hp ↦ hcl hp.2) (fun _ _ h ↦ h) le_rfl le_rfl le_rfl

end Front

/-- **The front phases' interface**, built. -/
noncomputable def frontIface (prog : LeanIsaProgram) (input : PublicInput) :
    FrontIface computedBytecodeValue prog input (publicInputDigest input) where
  frontSpec _ _ hs _ _ hS hS1 _ hT := frontSpecAt input hs hS hS1 hT

end
end LeanVM.Protocol.EndToEnd.Sound
