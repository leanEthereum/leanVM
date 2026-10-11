import Whir.WHIRObservableSource
import Whir.WHIRRealSimulator
import Whir.PublicCompressionModeSecurity

namespace Whir.WHIRObservableSecurity
open FiatShamirGame DuplexModeGame RawOracleCoupling.Concrete
open WHIRCallerRegistry WHIRSourceChronology WHIRObservableSource
set_option maxRecDepth 100000
set_option maxHeartbeats 800000

variable {cap : Nat} {R Coins : Type}

private instance : Finite UInt64 :=
  Finite.of_injective ByteCodec.encodeK ByteCodec.encodeK_injective
private noncomputable instance : Fintype UInt64 := Fintype.ofFinite _

noncomputable local instance : Fintype DuplexPublicSimulator.Seed :=
  DuplexPublicSimulator.seedFintype

/-- The public event never receives the adversary program, adversary coins, simulator seed, or a total raw oracle. -/
noncomputable def distinguisher (registry : Public) (Q : Nat)
    (select : R → Option (RawWHIRKeys.Packet (context registry) Q)) :
    View (WHIRPublicBackfill.Completed (context registry) Q (Result cap R)) → Bool := by
  classical
  exact fun view => decide (Failure registry Q select view.result)

def adversary (registry : Public) (Q : Nat) (sources : Coins → Source cap R)
    (select : R → Option (RawWHIRKeys.Packet (context registry) Q)) :
    Coins → Program (WHIRPublicBackfill.Completed (context registry) Q (Result cap R)) :=
  fun coins => WHIRSourceBackfill.instrument (context registry) Q (sources coins) select

def romBound (registry : Public) (A cap : Nat) : ℚ :=
  min 1 (((allocationBudget (context registry) * (A+1) : Nat) : ℚ) * WHIRRawROM.epsilon cap)

theorem source_counted (registry : Public) (Q A Mf : Nat) (source : Source cap R)
    (before : Counts A source) (envelope : WHIRSourceBackfill.budget (context registry) A Mf ≤ Q) :
    Counts Q source := by
  apply (compile_counted source Q).mp
  apply WHIRModeFinal.counts_mono ((compile_counted source A).mpr before)
  unfold WHIRSourceBackfill.budget at envelope
  omega

/-- Physical accounting is source-only and noncircular, including every repeated completion occurrence. -/
theorem adversary_counted (registry : Public) (Q A Mf : Nat) (sources : Coins → Source cap R)
    (select : R → Option (RawWHIRKeys.Packet (context registry) Q))
    (before : ∀ coins, Counts A (sources coins))
    (paths : ∀ coins, WHIRSourceBackfill.AllResults
      (fun result => ∀ packet, select result = some packet →
        DuplexFraming.pathCost (RawWHIRKeys.coordinate (context registry) packet.val 0) ≤ Mf)
      (erase (sources coins)))
    (envelope : WHIRSourceBackfill.budget (context registry) A Mf ≤ Q) :
    ∀ coins, DuplexModeGame.Counts Q (adversary registry Q sources select coins) := by
  intro coins
  exact WHIRModeFinal.counts_mono
    (WHIRSourceBackfill.counted_reachable (context registry) Q A Mf (sources coins) select
      (before coins) (paths coins)) envelope

theorem average_product {X Y : Type} [Fintype X] [Fintype Y] (f : X × Y → ℚ) :
    average f = average (fun x => average (fun y => f (x,y))) := by
  classical
  simp only [average,Fintype.sum_prod_type,Finset.sum_div,Fintype.card_prod,Nat.cast_mul,div_div]
  rw [mul_comm]

/-- Averaging over independent raw tables, simulator coins and adversary coins preserves the checked source-budgeted ROM bound. -/
theorem ideal_list_binding [Fintype Coins] [Nonempty Coins]
    (registry : Public) (Q A : Nat) (sources : Coins → Source cap R)
    (select : R → Option (RawWHIRKeys.Packet (context registry) Q))
    (sourceQ : ∀ coins, Counts Q (sources coins)) (before : ∀ coins, Counts A (sources coins))
    (whole : ∀ coins, DuplexModeGame.Counts Q (adversary registry Q sources select coins)) :
    idealProbability (DuplexPublicSimulator.simulator Q) registry.iv
      (adversary registry Q sources select) whole (distinguisher registry Q select) ≤ romBound registry A cap := by
  classical
  unfold idealProbability
  rw [distinguish_average (inferInstance : Fintype ((RawKey Q → Digest32) × DuplexPublicSimulator.Seed × Coins))]
  rw [average_product (X := RawKey Q → Digest32) (Y := DuplexPublicSimulator.Seed × Coins)]
  rw [RawOracleCoupling.average_comm
    (X := RawKey Q → Digest32) (Y := DuplexPublicSimulator.Seed × Coins)]
  calc
    _ ≤ average (fun _ : DuplexPublicSimulator.Seed × Coins => romBound registry A cap) := by
      apply average_mono
      intro coins
      simp only [distinguisher,adversary]
      simp_rw [ideal_output registry Q _ coins.1 (sources coins.2) (sourceQ coins.2) select (whole coins.2)]
      simpa only [decide_eq_true_eq,romBound] using
        public_table_list_binding registry Q coins.1 (sources coins.2) (sourceQ coins.2)
          A (before coins.2) select
    _ = _ := average_const _

/-- The actual adaptive whole-view coupling bounds the pinned #552 public-compression mode. It does not cover the older keyed transcript. -/
theorem random_compression_list_binding [Fintype Coins] [Nonempty Coins]
    (registry : Public) (Q A Mf : Nat) (sources : Coins → Source cap R)
    (select : R → Option (RawWHIRKeys.Packet (context registry) Q))
    (before : ∀ coins, Counts A (sources coins))
    (paths : ∀ coins, WHIRSourceBackfill.AllResults
      (fun result => ∀ packet, select result = some packet →
        DuplexFraming.pathCost (RawWHIRKeys.coordinate (context registry) packet.val 0) ≤ Mf)
      (erase (sources coins)))
    (envelope : WHIRSourceBackfill.budget (context registry) A Mf ≤ Q) :
    realProbability registry.iv (adversary registry Q sources select) (distinguisher registry Q select) ≤
      romBound registry A cap + duplexModeLoss Q := by
  apply randomCompression_transfer (DuplexPublicSimulator.simulator Q) registry.iv
    (DuplexPublicSimulator.modeSecurity Q registry.iv)
    (adversary registry Q sources select) (adversary_counted registry Q A Mf sources select before paths envelope)
    (distinguisher registry Q select)
  exact ideal_list_binding registry Q A sources select
    (fun coins => source_counted registry Q A Mf (sources coins) (before coins) envelope) before _

/-- Concrete BLAKE2s retains an explicit full-public-view replacement gap, not a justified computational hash assumption; the mode coupling and algebraic ROM bound are proved separately. -/
theorem concrete_list_binding [Fintype Coins] [Nonempty Coins]
    (registry : Public) (Q A Mf : Nat) (sources : Coins → Source cap R)
    (select : R → Option (RawWHIRKeys.Packet (context registry) Q))
    (before : ∀ coins, Counts A (sources coins))
    (paths : ∀ coins, WHIRSourceBackfill.AllResults
      (fun result => ∀ packet, select result = some packet →
        DuplexFraming.pathCost (RawWHIRKeys.coordinate (context registry) packet.val 0) ≤ Mf)
      (erase (sources coins)))
    (envelope : WHIRSourceBackfill.budget (context registry) A Mf ≤ Q)
    (Allowed : (C : Type) → [Fintype C] → (Output : Type) →
      (C → Program Output) → (View Output → Bool) → Prop)
    (primitiveLoss : ℚ) (primitive : ConcretePrimitiveGap Q registry.iv primitiveLoss Allowed)
    (permitted : Allowed Coins _ (adversary registry Q sources select) (distinguisher registry Q select)) :
    concreteProbability registry.iv (adversary registry Q sources select) (distinguisher registry Q select) ≤
      romBound registry A cap + duplexModeLoss Q + primitiveLoss := by
  apply concrete_transfer (DuplexPublicSimulator.simulator Q) registry.iv
    (DuplexPublicSimulator.modeSecurity Q registry.iv) Allowed primitive
    (adversary registry Q sources select) (adversary_counted registry Q A Mf sources select before paths envelope)
    (distinguisher registry Q select) permitted
  exact ideal_list_binding registry Q A sources select
    (fun coins => source_counted registry Q A Mf (sources coins) (before coins) envelope) before _

/-- Real-world reconstruction uses the deterministic selected-simulator realization only here, never as an independence premise in the probability proof. -/
theorem observe_real (registry : Public) (Q : Nat) (C : PrimitiveOracle)
    (source : Source cap R) (counted : Counts Q source) (A : Nat) (before : Counts A source)
    (select : R → Option (RawWHIRKeys.Packet (context registry) Q))
    (whole : DuplexModeGame.Counts Q (WHIRSourceBackfill.instrument (context registry) Q source select)) :
    observe registry Q select (runReal C registry.iv
      (WHIRSourceBackfill.instrument (context registry) Q source select)).view.result =
      some (tableObservation registry Q (WHIRRealSimulator.rawTable Q C) C source counted A before select) := by
  rw [WHIRRealSimulator.real_ideal_view C registry.iv
    (WHIRSourceBackfill.instrument (context registry) Q source select) whole]
  exact observe_ideal registry Q _ C source counted A before select whole

end Whir.WHIRObservableSecurity
