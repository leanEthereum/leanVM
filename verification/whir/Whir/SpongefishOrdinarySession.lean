import Whir.SpongefishPCSRoundFrames
import Whir.AnchoredByteStreamSampler
import Whir.WHIRModeFinal
import Whir.PublicCompressionCouplingActualCausalBound
import Whir.PublicCompressionModeSecurity

/-! The current session ID is computed by observed ordinary primitive queries.
This bridge preserves adaptive continuation dependence on that computed ID and
charges the entire derivation before using the ID as the duplex model domain.
It is a hand-port of the pinned ordinary plan, not compiler or native acceptance
refinement. No session ID is conditioned to an externally selected digest. -/
namespace Whir.SpongefishOrdinarySession
open Concrete FiatShamirGame DuplexRefinement DuplexFraming DuplexModeGame
open SpongefishSessionAdapter
set_option autoImplicit false

/-- Sequential ordinary calls retain every repeated input and answer. -/
def instructions (cv : Digest32) : List DuplexEncoding.Instruction → Program Digest32
  | [] => .done cv
  | i :: rest => .ask (.primitive .auxiliary ⟨cv,i.1,i.2,true⟩)
      (fun answer => instructions answer rest)

/- Reply materialization belongs to the data-valued executable interpreters,
not this instruction syntax: duplicating it here would snapshot every ordinary
answer twice. The same stored reply becomes the next input and final result. -/

theorem instructions_counted (cv : Digest32) (xs : List DuplexEncoding.Instruction) :
    Counts xs.length (instructions cv xs) := by
  induction xs generalizing cv with
  | nil => trivial
  | cons i rest ih =>
    simp only [instructions,Counts,Query.cost,List.length_cons]
    exact ⟨by omega,fun answer => by simpa using ih answer⟩

theorem instructions_real (C : PrimitiveOracle) (iv cv : Digest32)
    (xs : List DuplexEncoding.Instruction) :
    (runReal C iv (instructions cv xs)).view.result = evalPlan (compressionOf C) cv xs := by
  induction xs generalizing cv with
  | nil => rfl
  | cons i rest ih =>
    simpa only [instructions,runReal,prepend,realAnswer,evalPlan,List.foldl_cons,compressionOf]
      using ih (C ⟨cv,i.1,i.2,true⟩)

theorem instructions_observation_count (C : PrimitiveOracle) (iv cv : Digest32)
    (xs : List DuplexEncoding.Instruction) :
    (runReal C iv (instructions cv xs)).view.observations.length = xs.length := by
  induction xs generalizing cv with
  | nil => rfl
  | cons i rest ih =>
    simpa only [instructions,runReal,prepend,realAnswer,List.length_cons]
      using congrArg Nat.succ (ih (C ⟨cv,i.1,i.2,true⟩))

private theorem derive_cursor (c : Compression) (parameter : Digest32) (tag : List Byte) :
    (finish c (absorb c (init c parameter derivationIV) tag)).consumed = 0 := by
  rw [finish_consumed]
  by_cases empty : tag = []
  · simp [empty,init,seed]
  · exact absorb_nonempty_cursor c _ tag empty

theorem derive_output_block (c : Compression) (parameter : Digest32) (tag : List Byte) :
    derive c parameter tag =
      outputBlock c (finalized c (absorb c (init c parameter derivationIV) tag)) 0 := by
  let s := finish c (absorb c (init c parameter derivationIV) tag)
  have cursor : s.consumed = 0 := derive_cursor c parameter tag
  have cache : CacheValid c s := by simp [CacheValid,cursor]
  funext i
  unfold derive
  have value := AnchoredByteStreamSampler.squeezeLoop_getElem c s 32 i.val cache i.isLt
  simpa only [s,cursor,finish_cv,Nat.zero_add,Nat.div_eq_of_lt i.isLt,
    Nat.mod_eq_of_lt i.isLt] using value

theorem derivation_plan_evaluates (c : Compression) (parameter : Digest32) (tag : List Byte) :
    evalPlan c parameter (derivationPlan tag) = derive c parameter tag := by
  rw [derive_output_block]
  have chunks := chunks_evaluate c (init c parameter derivationIV) tag rfl
  change evalPlan c (init c parameter derivationIV).cv
    (DuplexEncoding.chunks true 0 [] tag ++ [(wordsBlock [0],UInt64.ofNat (6*2^56))]) = _
  rw [evalPlan_append]
  have chunks' : evalPlan c (init c parameter derivationIV).cv
      (DuplexEncoding.chunks true 0 [] tag) =
      finalized c (absorb c (init c parameter derivationIV) tag) := chunks
  rw [chunks']
  rfl

/-- SessionId::new's entire computation is ordinary observed work. -/
def deriveProgram (parameter : Digest32) (tag : List Byte) : Program Digest32 :=
  instructions parameter (derivationPlan tag)

theorem deriveProgram_counted (parameter : Digest32) (tag : List Byte) :
    Counts (derivationPrimitiveCost tag) (deriveProgram parameter tag) :=
  instructions_counted parameter _

theorem deriveProgram_real (C : PrimitiveOracle) (iv parameter : Digest32) (tag : List Byte) :
    (runReal C iv (deriveProgram parameter tag)).view.result =
      derive (compressionOf C) parameter tag := by
  rw [deriveProgram,instructions_real,derivation_plan_evaluates]

theorem deriveProgram_observation_count (C : PrimitiveOracle) (iv parameter : Digest32)
    (tag : List Byte) :
    (runReal C iv (deriveProgram parameter tag)).view.observations.length =
      2 + (tag.length+63)/64 := by
  rw [deriveProgram,instructions_observation_count]
  exact derivation_cost_closed tag

/-- The continuation receives the actually computed session ID, not a premise. -/
def afterDerive {R : Type} (parameter : Digest32) (tag : List Byte)
    (next : Digest32 → Program R) : Program R :=
  WHIRModeFinal.bind (deriveProgram parameter tag) next

theorem afterDerive_counted {R : Type} (parameter : Digest32) (tag : List Byte)
    (next : Digest32 → Program R) (B : Nat) (counted : ∀ session, Counts B (next session)) :
    Counts (derivationPrimitiveCost tag+B) (afterDerive parameter tag next) :=
  WHIRModeFinal.bind_counted _ _ _ _ (deriveProgram_counted parameter tag) counted

theorem afterDerive_real {R : Type} (C : PrimitiveOracle) (iv parameter : Digest32)
    (tag : List Byte) (next : Digest32 → Program R) :
    (runReal C iv (afterDerive parameter tag next)).view.result =
      (runReal C iv (next (derive (compressionOf C) parameter tag))).view.result := by
  rw [afterDerive,WHIRModeFinal.bind_real_result,deriveProgram_real]

open Classical in
/-- The global loss charges ordinary derivation and all adaptive continuation
work together. It is ideal-compression mode security, not BLAKE2s security. -/
theorem afterDerive_mode_bound {Coins R : Type} [Fintype Coins]
    (parameter : Digest32) (tag : List Byte) (B : Nat)
    (next : Coins → Digest32 → Program R)
    (counted : ∀ coin session, Counts B (next coin session)) (D : View R → Bool) :
    let Q := derivationPrimitiveCost tag+B
    letI := DuplexPublicSimulator.seedFintype
    ModeAdv (DuplexPublicSimulator.simulator Q) parameter
      (fun coin => afterDerive parameter tag (next coin))
      (fun coin => afterDerive_counted parameter tag (next coin) B (counted coin)) D ≤
      min 1 ((2*(Q : ℚ)^2-(Q : ℚ))/2^256) := by
  simpa only [duplexModeLoss_eq] using PublicCompressionCouplingActualJoint.actual_modeAdv_le_duplexModeLoss
    (AdvCoins := Coins) (R := R) (derivationPrimitiveCost tag+B) parameter
    (fun coin => afterDerive parameter tag (next coin))
    (fun coin => afterDerive_counted parameter tag (next coin) B (counted coin)) D

#print axioms derivation_plan_evaluates
#print axioms deriveProgram_real
#print axioms deriveProgram_observation_count
#print axioms afterDerive_counted
#print axioms afterDerive_real
#print axioms afterDerive_mode_bound
end Whir.SpongefishOrdinarySession
