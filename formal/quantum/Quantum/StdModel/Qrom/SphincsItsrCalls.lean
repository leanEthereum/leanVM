module

public import Quantum.StdModel.Qrom.SphincsItsrGame
public import Quantum.Qrom.Sphincs.End

@[expose] public section

/-!
# The calls of the ITSR template game of leanSPHINCS's B3

Charge bounds on `gameIT M upd pol A` (`SphincsItsrGame`) by kind, as `GameTCalls` does for
`gameT`: `a` per call of `F`, `b` per read, `c` per program call, `d` per reveal (`tChargeQ`;
realized, `rChargeQ`).

* `chg_foldT`: two reveals and one program call per signed message; `chg_tailIT`: two reads (the
  two `H_msg` calls of the forgery's digest).
* `chg_prefixIT`, `chg_gameIT` and their realizations: the prefix's calls, `signatureLimit` folds,
  the tail.
* **Counts** for an adversary with at most `q` hash calls and `signatureLimit` signing requests:
  `advCalls_gameIQ`, `advCalls_prefixIQ` (at most `q` calls of `F`), `readCalls_gameIQ` (at most
  `clsCapQ` reads), `clsCalls_prefixIQ` (at most `clsCapI` classical calls), and the tail's
  `chg_tailIQ_oneQ` (two calls), `chg_tailIQ_nonKeepQ` (only reads keeping the memory).
-/

open IPFunctor
open scoped ENNReal

open HashSig hiding PublicKey
open Sphincs hiding HashDomain

namespace Quantum.StdModel.Sphincs.SphItsr

open Quantum QuantumRuntime Common
open Quantum.Qrom.Sphincs
open Quantum.Sponge (portCharge)
open Quantum.Xmss.Assembly (recHwSpec recSpec realizeT revealThen progThen extCls chg_map
  tmplLens readLens isChargeBound_mono_charge nonKeep nonKeep_le_one liftRead)

local notation "hashChargeQ" => Quantum.Qrom.SufCma.cmdCharge Quantum.Qrom.SufCma.hashCharge
local notation "signChargeQ" => Quantum.Qrom.SufCma.cmdCharge Quantum.Qrom.SufCma.signCharge

attribute [local irreducible] Quantum.Qrom.hashQ LeanSphincsOver.messageDigest

/-! ## Charges by kind -/

section charges

variable {M : Type} [Fintype M] [DecidableEq M] (a b c d : ℕ)

omit [Fintype M] [DecidableEq M] in
/-- **The fold's calls**: per signed message two reveals and the digest's program call. -/
theorem chg_foldT (pol : DigestPolicy) (B : QReg) :
    ∀ msgs : List Message, IFreeM.IsChargeBound (foldT M pol B msgs)
      (portCharge (tChargeQ M a b c d)) ((2 * d + c) * msgs.length)
  | [] => trivial
  | msg :: ms => by
    rw [foldT]
    refine IFreeM.IsChargeBound.mono (chg_revealThen a b c d _ _ fun r₁ ↦
      chg_revealThen a b c d _ _ fun r₂ ↦ chg_progThen a b c d _ trivial _
        (FreeM₂.isChargeBound_bind (n₁ := (2 * d + c) * ms.length) (n₂ := 0)
          (chg_foldT pol B ms) fun _ ↦ trivial)) (le_of_eq ?_)
    rw [List.length_cons]
    ring

omit [Fintype M] [DecidableEq M] in
/-- **The tail's calls**: one read per call of `H` of the forgery's digest, two. -/
theorem chg_tailIT (y : PreI) :
    IFreeM.IsChargeBound (tailIT M y) (portCharge (tChargeQ M a b c d)) (b * 2) := by
  unfold tailIT
  rw [readsThenT_eq]
  exact IFreeM.IsChargeBound.mono (FreeM₂.isChargeBound_bind (n₁ := b * 2) (n₂ := 0)
    (isChargeBound_readLift a b c d (chg_map _ Prod.fst
      (chg_readsProgram a b (QReg.of Unit) (messageDigest_cost y.1 y.2.1.1.signature.randomizer
        y.2.1.1.message)))) fun _ ↦ trivial)
    (Nat.add_zero _).le

theorem length_logMsgsT_le (log : SufCma.SignLog Message (Option Signature)) :
    (logMsgsT log).length ≤ signatureLimit :=
  List.length_take_le _ _

variable (upd : TrialUpd M) {q : ℕ} (pol : DigestPolicy) (A : SAdversary)
  (hhash : ∀ pk, IFreeM.IsChargeBound (A pk) hashChargeQ q)
  (hsign : ∀ pk, IFreeM.IsChargeBound (A pk) signChargeQ signatureLimit)

include hhash hsign

omit [Fintype M] [DecidableEq M] in
/-- **The prefix with the data**: the prefix's calls and `signatureLimit` folds. -/
theorem chg_prefixIT :
    IFreeM.IsChargeBound (prefixIT M upd pol A) (portCharge (tChargeQ M a b c d))
      (prefixCallsQ a b c d q + (2 * d + c) * signatureLimit) := by
  unfold prefixIT
  refine FreeM₂.isChargeBound_bind (n₁ := prefixCallsQ a b c d q)
    (n₂ := (2 * d + c) * signatureLimit) (chg_prefixT a b c d upd pol A hhash hsign) fun x ↦ ?_
  refine IFreeM.IsChargeBound.mono (FreeM₂.isChargeBound_bind (n₁ := (2 * d + c) * signatureLimit)
    (n₂ := 0) ((chg_foldT a b c d pol _ (logMsgsT x.2.2)).mono
      (Nat.mul_le_mul_left _ (length_logMsgsT_le _))) fun _ ↦ trivial) (Nat.add_zero _).le

omit [Fintype M] [DecidableEq M] in
/-- **The game's calls by kind.** -/
theorem chg_gameIT :
    IFreeM.IsChargeBound (gameIT M upd pol A) (portCharge (tChargeQ M a b c d))
      (prefixCallsQ a b c d q + (2 * d + c) * signatureLimit + b * 2) :=
  FreeM₂.isChargeBound_bind (n₁ := prefixCallsQ a b c d q + (2 * d + c) * signatureLimit)
    (n₂ := b * 2) (chg_prefixIT a b c d upd pol A hhash hsign) fun y ↦ chg_tailIT a b c d y

omit [Fintype M] [DecidableEq M] in
theorem chg_realizeT_prefixIT (θ : TVals) :
    IFreeM.IsChargeBound (realizeT θ (prefixIT M upd pol A)) (portCharge (rChargeQ M a b c d))
      (prefixCallsQ a b c d q + (2 * d + c) * signatureLimit) :=
  isChargeBound_realizeT a b c d θ (chg_prefixIT a b c d upd pol A hhash hsign)

omit [Fintype M] [DecidableEq M] in
theorem chg_realizeT_gameIT (θ : TVals) :
    IFreeM.IsChargeBound (realizeT θ (gameIT M upd pol A)) (portCharge (rChargeQ M a b c d))
      (prefixCallsQ a b c d q + (2 * d + c) * signatureLimit + b * 2) :=
  isChargeBound_realizeT a b c d θ (chg_gameIT a b c d upd pol A hhash hsign)

end charges

/-! ## Counts -/

/-- **The classical calls of the prefix with the data**: those of the game (`clsCapQ`) and three
per fold. -/
def clsCapI : ℕ :=
  clsCapQ + 3 * signatureLimit

section counts

variable {q : ℕ} (pol : DigestPolicy) (A : SAdversary)
  (hhash : ∀ pk, IFreeM.IsChargeBound (A pk) hashChargeQ q)
  (hsign : ∀ pk, IFreeM.IsChargeBound (A pk) signChargeQ signatureLimit)

include hhash hsign

/-- **At most `q` calls of `F`** in the realized game. -/
theorem advCalls_gameIQ (θ : TVals) :
    IFreeM.IsChargeBound (gameIQ pol A θ)
      (portCharge fun i ↦ if extCls PairOut Qrom.HashDomain (Finset TPos × SelMem)
        (recSpec TPos SelMem) i then 0 else 1) q := by
  rw [advCharge_eq SelMem]
  exact IFreeM.IsChargeBound.mono (chg_realizeT_gameIT 1 0 0 0 cwUpd pol A hhash hsign θ)
    (le_of_eq (by simp [prefixCallsQ, signCallsQ, selCallsQ, pubCallsQ]))

/-- **At most `q` calls of `F`** in the realized prefix with the data. -/
theorem advCalls_prefixIQ (θ : TVals) :
    IFreeM.IsChargeBound (prefixIQ pol A θ)
      (portCharge fun i ↦ if extCls PairOut Qrom.HashDomain (Finset TPos × SelMem)
        (recSpec TPos SelMem) i then 0 else 1) q := by
  rw [advCharge_eq SelMem]
  exact IFreeM.IsChargeBound.mono (chg_realizeT_prefixIT 1 0 0 0 cwUpd pol A hhash hsign θ)
    (le_of_eq (by simp [prefixCallsQ, signCallsQ, selCallsQ, pubCallsQ]))

/-- **At most `clsCapQ` reads** in the realized game. -/
theorem readCalls_gameIQ (θ : TVals) :
    IFreeM.IsChargeBound (gameIQ pol A θ)
      (portCharge fun i ↦ if readPortQ i = true then 1 else 0) clsCapQ := by
  have he : (fun i ↦ if readPortQ i = true then 1 else 0) = rChargeQ SelMem 0 1 0 0 := by
    funext i
    rcases i with ((i | c) | c) | T <;> rfl
  rw [he]
  refine IFreeM.IsChargeBound.mono (chg_realizeT_gameIT 0 1 0 0 cwUpd pol A hhash hsign θ) ?_
  have h : signCallsQ 1 0 0 ≤ signCallsQ 1 1 1 := by
    simp only [signCallsQ, selCallsQ, pubCallsQ]
    omega
  have h' := Nat.mul_le_mul_right signatureLimit h
  simp only [clsCapQ, gameCallsQ, prefixCallsQ, verifyCalls_eq]
  omega

/-- **At most `clsCapI` classical calls** in the realized prefix with the data. -/
theorem clsCalls_prefixIQ (θ : TVals) :
    IFreeM.IsChargeBound (prefixIQ pol A θ)
      (portCharge fun i ↦ if extCls PairOut Qrom.HashDomain (Finset TPos × SelMem)
        (recSpec TPos SelMem) i then 1 else 0) clsCapI := by
  have he : (fun i ↦ if extCls PairOut Qrom.HashDomain (Finset TPos × SelMem)
      (recSpec TPos SelMem) i then 1 else 0) = rChargeQ SelMem 0 1 1 1 := by
    funext i
    rcases i with ((i | c) | c) | T <;> rfl
  rw [he]
  refine IFreeM.IsChargeBound.mono (chg_realizeT_prefixIT 0 1 1 1 cwUpd pol A hhash hsign θ) ?_
  simp only [clsCapI, clsCapQ, gameCallsQ, prefixCallsQ]
  omega

end counts

/-! ## The tail -/

/-- **The tail's calls**: at most two. -/
theorem chg_tailIQ_oneQ (θ : TVals) (y : PreI) :
    IFreeM.IsChargeBound (realizeT θ (tailIT SelMem y)) (portCharge fun _ ↦ 1) 2 := by
  have he : rChargeQ SelMem 1 1 1 1 = fun _ ↦ 1 := by
    funext i
    rcases i with ((i | c) | c) | T <;> rfl
  have h := isChargeBound_realizeT (M := SelMem) 1 1 1 1 θ (chg_tailIT (M := SelMem) 1 1 1 1 y)
  rw [he] at h
  simpa using h

/-- **The tail calls only reads that keep the memory.** -/
theorem chg_tailIQ_nonKeepQ (θ : TVals) (y : PreI) :
    IFreeM.IsChargeBound (realizeT θ (tailIT SelMem y))
      (portCharge (nonKeep PairOut Qrom.HashDomain TPos SelMem)) 0 := by
  rw [tailIT, readsThenT_eq]
  refine IFreeM.IsChargeBound.mapLens (tmplLens θ) ?_
  refine FreeM₂.isChargeBound_bind (n₁ := 0) (n₂ := 0) ?_ fun _ ↦ trivial
  refine IFreeM.IsChargeBound.mapLens (readLens goodQ) ?_
  refine isChargeBound_mono_charge (fun s a ↦ ?_)
    (chg_map _ Prod.fst (sChg_simulateQ_romReadImpl_keep (M := SelMem) (QReg.of Unit) _ []))
  rcases a with o | ⟨i | c, E, ℓ⟩
  · exact le_rfl
  · exact le_rfl
  · show nonKeep PairOut Qrom.HashDomain TPos SelMem (.inl (.inl (.inr (liftRead c)))) ≤
      nonKeepRdQ SelMem (.inr c)
    by_cases hc : c.KeepsMem
    · have h0 : nonKeep PairOut Qrom.HashDomain TPos SelMem
          (.inl (.inl (.inr (liftRead c)))) = 0 := by
        simp only [nonKeep, keepUpd_liftReadQ c hc, ↓reduceIte]
      omega
    · have h1 : nonKeepRdQ SelMem (.inr c) = 1 := by simp only [nonKeepRdQ, hc, ↓reduceIte]
      have h2 := nonKeep_le_one (X := PairOut) (Z := Qrom.HashDomain) (S := TPos) (M := SelMem)
        (.inl (.inl (.inr (liftRead c))))
      omega

end Quantum.StdModel.Sphincs.SphItsr

end
