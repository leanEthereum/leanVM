import Whir.WHIRRawReplay
import Whir.WHIRRawHistory

namespace Whir.WHIRRawROM
open Concrete Protocol CausalProbability ParameterBounds
open FiatShamirGame (Digest32 average)
open RawOracleCoupling RawOracleCoupling.Concrete WHIRRawReplay
open Classical
set_option maxHeartbeats 800000
set_option maxRecDepth 100000

abbrev Catalogs (cap : Nat) := (p : Profile) → FiatShamirGame.FramedHistory →
  Option (WHIRFiatShamir.StackInitial p cap)

def localCatalog {cap : Nat} (catalog : Catalogs cap) (p : Profile)
    (entry : FiatShamirGame.FramedHistory) : StackWHIRReplay.Catalog p cap :=
  fun seed => if seed = entry.statement then catalog p entry else none
abbrev RootFamilies := (p : Profile) → StackWHIRReplay.Roots

def epsilon (cap : Nat) : ℚ := (1 : ℚ)/2^79 + WHIRFiatShamir.ringCharge cap

theorem epsilon_nonneg (cap : Nat) : 0 ≤ epsilon cap :=
  add_nonneg (by positivity) (WHIRFiatShamir.ringCharge_nonneg cap)

def bad (ctx : RawWHIRKeys.Context) (stack : ctx.mode = .stack) (Q cap : Nat)
    (catalog : Catalogs cap) (roots : RootFamilies) :
    (label : AllocationKey ctx Q) → AllocationAnswer ctx Q label → Prop
  | (.inl packet,history),raw =>
    StackWHIRROM.keyBad packet.val.profile cap
      (localCatalog catalog packet.val.profile (callerEntry ctx Q packet)) (roots packet.val.profile)
      (localKey (allocationKey ctx stack Q packet history)) (decodePacket ctx stack Q packet raw)
  | (.inr _,_),_ => False

attribute [local irreducible] StackWHIRROM.keyBad StackWHIRCodec.blockDecode

private theorem average_instances {α : Type} (old new : Fintype α) (f : α → ℚ) :
    @average α old f = @average α new f := by
  cases Subsingleton.elim old new
  rfl

theorem sparse (ctx : RawWHIRKeys.Context) (stack : ctx.mode = .stack) (Q cap : Nat)
    (catalog : Catalogs cap) (roots : RootFamilies) (label : AllocationKey ctx Q) :
    average (fun raw => if bad ctx stack Q cap catalog roots label raw then 1 else 0) ≤ epsilon cap := by
  rcases label with ⟨group,history⟩
  cases group with
  | inr garbage =>
    simp only [bad, ↓reduceIte, FiatShamirGame.average_const]
    exact epsilon_nonneg cap
  | inl packet =>
    refine (average_instances _ (inferInstance : Fintype (GroupAnswer ctx Q (.inl packet)))
      (fun raw : GroupAnswer ctx Q (.inl packet) =>
        if bad ctx stack Q cap catalog roots (.inl packet,history) raw then 1 else 0)).trans_le ?_
    let key := localKey (allocationKey ctx stack Q packet history)
    have bound := StackWHIRCodec.key_block_sparse packet.val.profile cap
      (localCatalog catalog packet.val.profile (callerEntry ctx Q packet)) (roots packet.val.profile) key
    have scale : WHIRFiatShamir.stackEta packet.val.profile cap ≤ epsilon cap := by
      exact add_le_add (WHIRFiatShamir.eta_le packet.val.profile)
        (le_refl (WHIRFiatShamir.ringCharge cap))
    have finalBound := bound.trans scale
    have equal := RawOracleCoupling.average_equiv (packetEquiv ctx stack Q packet)
      (fun raw => if StackWHIRROM.keyBad packet.val.profile cap
        (localCatalog catalog packet.val.profile (callerEntry ctx Q packet))
        (roots packet.val.profile) key (StackWHIRCodec.blockDecode
          (StackWHIRReplay.query packet.val.profile (packet.val.statement,packet.val.messages)) raw)
        then (1 : ℚ) else 0)
    change average (fun raw : GroupAnswer ctx Q (.inl packet) =>
      if StackWHIRROM.keyBad packet.val.profile cap
        (localCatalog catalog packet.val.profile (callerEntry ctx Q packet)) (roots packet.val.profile) key
        (decodePacket ctx stack Q packet raw) then 1 else 0) ≤ epsilon cap
    exact equal.le.trans finalBound

theorem lift_bad_member (ctx : RawWHIRKeys.Context) (stack : ctx.mode = .stack) (Q cap : Nat)
    (catalog : Catalogs cap) (roots : RootFamilies) (p : Profile)
    (entry : FiatShamirGame.FramedHistory)
    (trace : List (Sigma (AllocationAnswer ctx Q)))
    (covered : ∃ ka ∈ localTrace p entry (decodedTrace ctx stack Q trace),
      StackWHIRROM.keyBad p cap (localCatalog catalog p entry) (roots p) ka.1 ka.2) :
    ∃ ka ∈ trace, bad ctx stack Q cap catalog roots ka.1 ka.2 := by
  obtain ⟨ka,member,failed⟩ := covered
  obtain ⟨encoded,inDecoded,restricted⟩ := List.mem_filterMap.mp member
  obtain ⟨allocation,inTrace,decoded⟩ := List.mem_filterMap.mp inDecoded
  rcases allocation with ⟨⟨group,history⟩,raw⟩
  cases group with
  | inr garbage => simp only [decodeAllocation, reduceCtorEq] at decoded
  | inl packet =>
    simp only [decodeAllocation, Option.some.injEq] at decoded
    subst encoded
    simp only [restrictAllocation, allocationKey] at restricted
    by_cases same : packet.val.profile = p
    · simp only [same, ↓reduceDIte] at restricted
      by_cases sameEntry : callerEntry ctx Q packet = entry
      · simp only [sameEntry, ↓reduceIte] at restricted
        subst p
        subst entry
        cases restricted
        exact ⟨_,inTrace,failed⟩
      · simp only [sameEntry, ↓reduceIte, reduceCtorEq] at restricted
    · simp only [same, ↓reduceDIte, reduceCtorEq] at restricted

def completedHistory (ctx : RawWHIRKeys.Context) (stack : ctx.mode = .stack) (Q : Nat)
    (cache : TypedFiatShamirGame.Cache (GroupKey ctx Q) (GroupAnswer ctx Q))
    (packet : RawWHIRKeys.Packet ctx Q) (raw : GroupAnswer ctx Q (.inl packet)) :
    List (LocalEntry packet.val.profile) :=
  (packetEntry ctx stack Q packet raw ::
    decodeHistory ctx stack Q (WHIRRawHistory.Ancestors ctx Q cache packet)).filterMap
      (restrictEntry packet.val.profile)

/-- The terminal predicate parses and verifies the actual completed cache. A
rejected submission selects no packet; no fabricated fallback is introduced. -/
def Failure (ctx : RawWHIRKeys.Context) (stack : ctx.mode = .stack) (Q cap : Nat)
    (catalog : Catalogs cap) (roots : RootFamilies)
    (selected : Option (RawWHIRKeys.Packet ctx Q))
    (cache : TypedFiatShamirGame.Cache (GroupKey ctx Q) (GroupAnswer ctx Q)) : Prop :=
  ∃ packet, selected = some packet ∧ ∃ raw, cache (.inl packet) = some raw ∧
    StackWHIRROM.HistoryFailure packet.val.profile cap
      (localCatalog catalog packet.val.profile (callerEntry ctx Q packet)) (roots packet.val.profile)
      packet.val.statement packet.val.messages (completedHistory ctx stack Q cache packet raw)

theorem compiler_cover (ctx : RawWHIRKeys.Context) (stack : ctx.mode = .stack) (Q cap : Nat)
    (catalog : Catalogs cap) (roots : RootFamilies) {R : Type} {K : Nat}
    (final : R → Option (RawWHIRKeys.Packet ctx Q))
    (program : TypedOracleCompiler.Sampling (DuplexModeGame.RawKey Q) (fun _ => Digest32) R K)
    (trace result)
    (run : TypedOracleCompiler.Sampling.Runs (compile ctx Q final program) trace result)
    (failed : Failure ctx stack Q cap catalog roots (final result.1) result.2) :
    ∃ ka ∈ trace, bad ctx stack Q cap catalog roots ka.1 ka.2 := by
  obtain ⟨packet,_,raw,hit,failed⟩ := failed
  have recorded := WHIRRawHistory.recorded_history ctx stack Q result.2 trace
    (RawOracleCoupling.Concrete.recorded ctx Q final program run).2 packet raw hit
  have localProof := restrict_recorded packet.val.profile (callerEntry ctx Q packet)
    (decodedTrace ctx stack Q trace) packet.val.messages _ recorded
  have covered := StackWHIRROM.recorded_history_cover packet.val.profile cap
    (localCatalog catalog packet.val.profile (callerEntry ctx Q packet))
    (roots packet.val.profile) packet.val.statement packet.val.messages _
    (localTrace packet.val.profile (callerEntry ctx Q packet) (decodedTrace ctx stack Q trace)) localProof failed
  exact lift_bad_member ctx stack Q cap catalog roots packet.val.profile (callerEntry ctx Q packet) trace covered

theorem allocation_list_binding (ctx : RawWHIRKeys.Context) (stack : ctx.mode = .stack)
    (Q cap : Nat) (catalog : Catalogs cap) (roots : RootFamilies) {R : Type} {K : Nat}
    (final : R → Option (RawWHIRKeys.Packet ctx Q))
    (program : TypedOracleCompiler.Sampling (DuplexModeGame.RawKey Q) (fun _ => Digest32) R K) :
    TypedOracleCompiler.Sampling.failureProbability
      (fun result => Failure ctx stack Q cap catalog roots (final result.1) result.2)
      (compile ctx Q final program) ≤
        min 1 (((allocationBudget ctx * (K+1) : Nat) : ℚ) * epsilon cap) := by
  apply le_min
  · apply TypedOracleCompiler.Sampling.expectation_le_one
    intro result
    split <;> norm_num
  · have cover := TypedOracleCompiler.Sampling.failure_le_risk
      (bad ctx stack Q cap catalog roots)
      (fun result => Failure ctx stack Q cap catalog roots (final result.1) result.2)
      (compile ctx Q final program) (compiler_cover ctx stack Q cap catalog roots final program)
    have bounded := TypedFiatShamirGame.risk_bound (bad ctx stack Q cap catalog roots)
      (epsilon cap) (epsilon_nonneg cap) (sparse ctx stack Q cap catalog roots)
      (TypedOracleCompiler.Sampling.erase (compile ctx Q final program))
    simpa only [Nat.mul_add, Nat.mul_one] using cover.trans bounded

private instance : Finite UInt64 :=
  Finite.of_injective ByteCodec.encodeK ByteCodec.encodeK_injective
private noncomputable instance : Fintype UInt64 := Fintype.ofFinite _

/-- All raw requests, including garbage, partial blocks and final completion,
share one coupled cache. This theorem conditions on no future oracle values. -/
theorem raw_table_list_binding (ctx : RawWHIRKeys.Context) (stack : ctx.mode = .stack)
    (Q cap : Nat) (catalog : Catalogs cap) (roots : RootFamilies) {R : Type} {K : Nat}
    (final : R → Option (RawWHIRKeys.Packet ctx Q))
    (program : TypedOracleCompiler.Sampling (DuplexModeGame.RawKey Q) (fun _ => Digest32) R K) :
    average (fun table : DuplexModeGame.RawKey Q → Digest32 =>
      let result := tableExecution ctx Q final program table
      if Failure ctx stack Q cap catalog roots (final result.1) result.2 then 1 else 0) ≤
        min 1 (((allocationBudget ctx * (K+1) : Nat) : ℚ) * epsilon cap) := by
  rw [RawOracleCoupling.Concrete.distribution_full ctx Q final program
    (fun result => if Failure ctx stack Q cap catalog roots (final result.1) result.2 then 1 else 0)]
  exact allocation_list_binding ctx stack Q cap catalog roots final program

end Whir.WHIRRawROM
