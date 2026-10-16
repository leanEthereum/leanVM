module

public import LeanVMCircuits.ClockCircuit

@[expose] public section

/-!
# The clock circuit

The verdict of the order checks and the step port of `Clock::builder`, on the circuits of `ClockCircuit`.
-/

namespace LeanVMCircuits

open ClockValues

attribute [local irreducible] Adder.circuit ClockChain.circuit ClockLow.circuit ClockCompare.circuit
  ClockAccess.circuit ClockAccesses.circuit ClockAll.circuit

namespace ClockStep

structure Input (n : ℕ) (F : Type) where
  ts : Vector F 36
  prev : Vector (fields 41 F) n
  deriving ProvableStruct

/-- The step port's bits 5 to 41, read as an integer, are `Clock.step` of the slots on the ports' integers. -/
def Spec (slots : List (Fin 32)) (input : Input slots.length Bit) (output : Vector Bit 37) : Prop :=
  2 ^ 5 * Adder.value output =
    Clock.step (slots.map Fin.val) (input.prev.toList.map Adder.value) (tsNum input.ts)

/-- The step's bits 5 to 40 are the carries of `ts / 2^5 + live`, and bit 41 is `fail`. -/
theorem step_value (ts : Vector Bit 36) (chain : List Bit) (fail : Bit) (failing : Bool)
    (hchain : chain = prefixes ts[35] (slice ts 0 35 (by omega)).toList)
    (hfail : fail = if failing then 1 else 0) :
    2 ^ 5 * valueL ((ts[35] :: chain) ++ [fail]) =
      (((tsNum ts / 2 ^ 5 + if Clock.live (tsNum ts) then 1 else 0) ^^^ (tsNum ts / 2 ^ 5)) % 2 ^ 36) * 2 ^ 5 +
        if failing then 2 ^ 41 else 0 := by
  have hlen : chain.length = 35 := by rw [hchain, length_prefixes, Vector.length_toList]
  have hcarries := carries_value (slice ts 0 35 (by omega)).toList ts[35] (Adder.value ts)
    (by rw [Vector.length_toList, ← value_eq, ts_cycle])
  rw [Vector.length_toList, ← hchain] at hcarries
  have hdiv : tsNum ts / 2 ^ 5 = Adder.value ts := by unfold tsNum; omega
  have hlive : (if Clock.live (tsNum ts) then 1 else 0) = ts[35].val := by
    rw [Clock.live, tsNum, ts_live]
    rcases bit_zero_or_one ts[35] with h | h <;> simp [h]
  rw [valueL_append, hcarries, hdiv, hlive, hfail, List.length_cons, hlen]
  cases failing <;> simp <;> ring

/-- The verdict bit is `Clock.fail` of the order checks and the live bits' disagreement. -/
theorem fail_value (slots : List (Fin 32)) (ts : Vector Bit 36) (prev : Vector (Vector Bit 41) slots.length)
    (hne : slots ≠ []) (inOrder : Vector Bit slots.length) (ordered disagree : Bit)
    (hin : ∀ i (hi : i < slots.length), inOrder[i] =
      if Clock.ordered (tsNum ts) (Adder.value prev[i]) (ClockAccesses.slotAt slots i).val then 1 else 0)
    (hord : ordered = if ∀ i (hi : i < slots.length), inOrder[i] = 1 then 1 else 0)
    (hdis : disagree = if ∃ i, ∃ hi : i < slots.length, Clock.disagrees (tsNum ts) (Adder.value prev[i]) = true
      then 1 else 0) :
    BooleanOr.select (ts[35] * (ordered + 1)) disagree =
      if Clock.fail (slots.map Fin.val) (prev.toList.map Adder.value) (tsNum ts) then 1 else 0 := by
  have hall : (∀ i (hi : i < slots.length), inOrder[i] = 1) ↔
      ((prev.toList.map Adder.value).zip (slots.map Fin.val)).all
        (fun ps => Clock.ordered (tsNum ts) ps.1 ps.2) = true := by
    rw [zip_all_iff _ _ (by simp)]
    simp only [List.length_map, Vector.length_toList, List.getElem_map, Vector.getElem_toList]
    apply forall_congr'; intro i; apply forall_congr'; intro hi
    rw [hin i hi, ClockAccesses.slotAt, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by simpa using hi),
      Option.getD_some]
    split_ifs with h <;> simp [h]
  have hany : (∃ i, ∃ hi : i < slots.length, Clock.disagrees (tsNum ts) (Adder.value prev[i]) = true) ↔
      (prev.toList.map Adder.value).any (Clock.disagrees (tsNum ts)) = true := by
    rw [any_iff]
    simp only [List.length_map, Vector.length_toList, List.getElem_map, Vector.getElem_toList]
  have hempty : (slots.map Fin.val).isEmpty = false := by
    cases slots with
    | nil => exact absurd rfl hne
    | cons s rest => rfl
  have hlive : Clock.live (tsNum ts) = decide (ts[35] = 1) := by rw [Clock.live, tsNum, ts_live]
  rw [hord, hdis, Clock.fail, hempty, hlive]
  by_cases hA : ∀ i (hi : i < slots.length), inOrder[i] = 1 <;>
    by_cases hD : ∃ i, ∃ hi : i < slots.length, Clock.disagrees (tsNum ts) (Adder.value prev[i]) = true <;>
    rcases bit_zero_or_one ts[35] with hL | hL <;>
    simp [hA, hD, hL, (hall.mp ·), BooleanOr.select] <;>
    simp_all

/-- The verdict's products: the accesses', then the AND of their order checks, `late` and `fail`. -/
def verdictLength (slot : Fin 32) (rest : List (Fin 32)) : ℕ :=
  ClockAccesses.length (slot :: rest) rest.length + rest.length + 2

theorem accesses_channels (slots : List (Fin 32)) (k : ℕ) :
    (ClockAccesses.circuit slots k).channelsWithGuarantees = [] := ClockAccesses.circuit_guarantees slots k

theorem all_channels (n : ℕ) : (ClockAll.circuit n).channelsWithGuarantees = [] := ClockAll.circuit_guarantees n

theorem chain_channels (n : ℕ) : (ClockChain.circuit n).channelsWithGuarantees = [] :=
  ClockChain.circuit_guarantees n

/-- The verdict of the clock circuit of the slots `slot :: rest`: the order checks, their AND, `late`, `fail`.

The AND's input is the accesses' output, which moves with the offset, so the length is stated rather than derived:
derived, it would be the AND's length at the accesses' output at offset 0, which the kernel cannot see is the same at
every offset. -/
def verdict (slot : Fin 32) (rest : List (Fin 32)) : FormalCircuit Bit (Input (rest.length + 1)) field where
  main := fun input => do
    let accesses ← ClockAccesses.circuit (slot :: rest) rest.length { ts := input.ts, prev := input.prev }
    let ordered ← ClockAll.circuit rest.length { word := accesses.inOrder }
    let late ← Product.circuit { x := input.ts[35], y := ordered + 1 }
    BooleanOr.circuit { x := late, y := accesses.disagree }
  elaborated := {
    localLength := fun _ => verdictLength slot rest
    localLength_eq := by
      intro input offset
      simp only [verdictLength, circuit_norm, ClockAccesses.circuit_length, ClockAll.circuit_length]
      omega
    channelsLawful := by
      dsimp only [ElaboratedCircuit.ChannelsLawful]
      simp only [circuit_norm, seval, accesses_channels, all_channels, List.append_nil, List.nil_subset] }
  Spec := fun input output => output =
    if Clock.fail ((slot :: rest).map Fin.val) (input.prev.toList.map Adder.value) (tsNum input.ts) then 1 else 0
  soundness := by
    circuit_proof_start [ClockAccesses.Spec, ClockAll.Spec, Product.circuit, Product.Spec, BooleanOr.circuit]
    rcases h_input with ⟨hts, hprev⟩
    simp only [FormalCircuitBase.output] at h_holds ⊢
    simp only [ClockAccesses.eval_inOrder, ClockAccesses.eval_disagree] at h_holds
    rcases h_holds with ⟨⟨hin, hdis⟩, hord, hlate, hfail⟩
    have ht35 : Expression.eval env input_var_ts[35] = input_ts[35] := by rw [← hts, Vector.getElem_map]
    rw [ht35] at hlate
    have hF := fail_value (slot :: rest) input_ts input_prev (by simp) _ _ _ hin hord hdis
    rw [← hlate, ← hfail] at hF
    simp only [List.map_cons] at hF ⊢
    exact hF
  completeness := by circuit_proof_start [Product.circuit, BooleanOr.circuit]

@[circuit_norm] theorem verdict_assumptions (slot : Fin 32) (rest : List (Fin 32)) :
    (verdict slot rest).Assumptions = fun _ => True := rfl
@[circuit_norm] theorem verdict_spec (slot : Fin 32) (rest : List (Fin 32)) :
    (verdict slot rest).Spec = fun input output => output =
      if Clock.fail ((slot :: rest).map Fin.val) (input.prev.toList.map Adder.value) (tsNum input.ts) then 1 else 0 :=
  rfl
@[circuit_norm] theorem verdict_requirements (slot : Fin 32) (rest : List (Fin 32)) :
    (verdict slot rest).channelsWithRequirements = [] := rfl
@[circuit_norm] theorem verdict_guarantees (slot : Fin 32) (rest : List (Fin 32)) :
    (verdict slot rest).elaborated.channelsWithGuarantees = [] := rfl
theorem verdict_channels (slot : Fin 32) (rest : List (Fin 32)) :
    (verdict slot rest).channelsWithGuarantees = [] := rfl
@[circuit_norm] theorem verdict_length (slot : Fin 32) (rest : List (Fin 32))
    (input : Var (Input (rest.length + 1)) Bit) :
    (verdict slot rest).localLength input = verdictLength slot rest := rfl

end ClockStep

attribute [local irreducible] ClockStep.verdict

namespace ClockStep

/-- The clock circuit of the slots `slot :: rest`, product for product `Clock::builder`'s. -/
def circuit (slot : Fin 32) (rest : List (Fin 32)) :
    FormalCircuit Bit (Input (rest.length + 1)) (fields 37) where
  main := fun input => do
    let fail ← verdict slot rest input
    let chain ← ClockChain.circuit 35 { x := slice input.ts 0 35 (by omega), carry := input.ts[35] }
    return (#v[input.ts[35]] ++ chain.bits).push fail
  elaborated := {
    localLength := fun _ => verdictLength slot rest + 35
    localLength_eq := by
      intro input offset
      simp only [circuit_norm, verdict_length, ClockChain.circuit_length]
    channelsLawful := by
      dsimp only [ElaboratedCircuit.ChannelsLawful]
      simp only [circuit_norm, seval, verdict_channels, chain_channels, List.append_nil, List.nil_subset] }
  Spec := Spec (slot :: rest)
  soundness := by
    circuit_proof_start [ClockChain.Spec]
    rcases h_input with ⟨hts, hprev⟩
    simp only [FormalCircuitBase.output] at h_holds ⊢
    simp only [map_slice, hts] at h_holds
    rcases h_holds with ⟨hF, hbits, -⟩
    have ht35 : Expression.eval env input_var_ts[35] = input_ts[35] := by rw [← hts, Vector.getElem_map]
    rw [ht35, Vector.toList_map] at hbits
    simp only [value_eq, Vector.toList_map, Vector.toList_push, List.map_append, List.map_cons, List.map_nil,
      hF] at ⊢
    rw [toList_singleton_append, List.map_cons, ht35, hbits, List.cons_append, Clock.step]
    exact step_value input_ts _ _ _ rfl rfl
  completeness := by circuit_proof_start

end ClockStep

end LeanVMCircuits
