import Whir.WHIRModeProgram
import Whir.RawOracleProvenance

/-! Metered physical final verification completion. The final selection is made
from the preceding program result. Prior caller outputs, followed by oldest-first
ancestor packets and the final packet, are actually queried before returning
their data to a view observer. No observer receives an oracle or performs
unmetered caller recovery or packet completion. -/
namespace Whir.WHIRModeFinal
open FiatShamirGame DuplexRefinement DuplexFraming DuplexModeGame
open RawWHIRKeys (Context Packet)
open RawOracleCoupling.Concrete (GroupAnswer terminalCompletion)

variable {R S : Type}

structure Completed (ctx : Context) (Q : Nat) (R : Type) where
  result : R
  packet : Option (Packet ctx Q)
  history : List (Sigma (GroupAnswer ctx Q))

def bind : Program R → (R → Program S) → Program S
  | .done r, next => next r
  | .ask q next, after => .ask q (fun answer => bind (next answer) after)

theorem counts_mono {p : Program R} {a b : Nat} (h : Counts a p) (hab : a ≤ b) : Counts b p := by
  induction p generalizing a b with
  | done => trivial
  | ask q next ih =>
    exact ⟨h.1.trans hab, fun answer => ih answer (h.2 answer) (Nat.sub_le_sub_right hab _)⟩

theorem bind_counted (p : Program R) (next : R → Program S) (a b : Nat)
    (before : Counts a p) (after : ∀ r, Counts b (next r)) : Counts (a+b) (bind p next) := by
  induction p generalizing a with
  | done r => exact counts_mono (after r) (by omega)
  | ask q cont ih =>
    refine ⟨by have := before.1; omega, fun answer => ?_⟩
    have h := ih answer (a-q.cost) (before.2 answer)
    have he : a+b-q.cost = (a-q.cost)+b := by have := before.1; omega
    simpa only [he] using h

/-- An appended program's certificate already certifies its whole prefix. -/
theorem bind_prefix_counted (p : Program R) (next : R → Program S) (budget : Nat)
    (counted : Counts budget (bind p next)) : Counts budget p := by
  induction p generalizing budget with
  | done => trivial
  | ask q cont ih => exact ⟨counted.1, fun answer => ih answer _ (counted.2 answer)⟩

def request (ctx : Context) (Q : Nat) (p : Packet ctx Q)
    (i : Fin (RawWHIRKeys.blocks ctx p.val)) : Query :=
  .construction (RawWHIRKeys.coordinate ctx p.val i.val)
    (RawWHIRKeys.coordinate_admissible ctx Q ⟨p,i⟩)

def realPacket (ctx : Context) (Q : Nat) (oracle : PrimitiveOracle) (p : Packet ctx Q) :
    GroupAnswer ctx Q (.inl p) := fun i =>
  evalCoordinate (compressionOf oracle) ctx.iv (RawWHIRKeys.coordinate ctx p.val i.val)

def idealPacket (ctx : Context) (Q : Nat) (ro : RawKey Q → Digest32) (p : Packet ctx Q) :
    GroupAnswer ctx Q (.inl p) := fun i => ro (RawWHIRKeys.encode ctx Q ⟨p,i⟩)

def packetCost (ctx : Context) (Q : Nat) (p : Packet ctx Q) : Nat :=
  ∑ i : Fin (RawWHIRKeys.blocks ctx p.val), pathCost (RawWHIRKeys.coordinate ctx p.val i.val)

def packetsCost (ctx : Context) (Q : Nat) (ps : List (Packet ctx Q)) : Nat :=
  (ps.map (packetCost ctx Q)).sum

abbrev CallerPosition (ctx : Context) (Q : Nat) (p : Packet ctx Q) :=
  {q : Coordinate // q ∈ WHIRCallerOutputs.callerOutputs (RawWHIRKeys.entry ctx p.val)}

def callerPositions (ctx : Context) (Q : Nat) (p : Packet ctx Q) : List (CallerPosition ctx Q p) :=
  (WHIRCallerOutputs.callerOutputs (RawWHIRKeys.entry ctx p.val)).attach

def callerCost {ctx : Context} {Q : Nat} {p : Packet ctx Q} (qs : List (CallerPosition ctx Q p)) : Nat :=
  (qs.map (fun q => pathCost q.val)).sum

def completionCost (ctx : Context) (Q : Nat) : Option (Packet ctx Q) → Nat
  | none => 0
  | some p => callerCost (callerPositions ctx Q p) + packetsCost ctx Q (terminalCompletion ctx Q (some p))

def readPackets (ctx : Context) (Q : Nat) : List (Packet ctx Q) →
    (List (Sigma (GroupAnswer ctx Q)) → Program R) → Program R
  | [], next => next []
  | p :: ps, next =>
    WHIRModeProgram.readPacket (RawWHIRKeys.blocks ctx p.val) (request ctx Q p)
      (fun raw => readPackets ctx Q ps (fun rest => next (⟨.inl p,raw⟩ :: rest)))

/-- Caller singleton reads and packet reads form one continuation chain.
History cells are built once, without copying an intermediate caller list. -/
def readCallerThenPackets (ctx : Context) (Q : Nat) (p : Packet ctx Q) :
    List (CallerPosition ctx Q p) → List (Packet ctx Q) →
      (List (Sigma (GroupAnswer ctx Q)) → Program R) → Program R
  | [], ps, next => readPackets ctx Q ps next
  | q :: qs, ps, next =>
    .ask (.construction q.val (RawWHIRKeys.callerOutput_admissible ctx Q p q.val q.property))
      (fun answer => readCallerThenPackets ctx Q p qs ps (fun rest =>
        next (⟨.inr (RawWHIRKeys.callerOutputKey ctx Q p q.val q.property),answer⟩ :: rest)))

def finish (ctx : Context) (Q : Nat) (r : R) :
    Option (Packet ctx Q) → Program (Completed ctx Q R)
  | none => .done ⟨r,none,[]⟩
  | some p => readCallerThenPackets ctx Q p (callerPositions ctx Q p)
      (terminalCompletion ctx Q (some p)) (fun history => .done ⟨r,some p,history⟩)

def append (ctx : Context) (Q : Nat) (p : Program R) (final : R → Option (Packet ctx Q)) :
    Program (Completed ctx Q R) := bind p (fun r => finish ctx Q r (final r))

def realHistory (ctx : Context) (Q : Nat) (oracle : PrimitiveOracle) (ps : List (Packet ctx Q)) :
    List (Sigma (GroupAnswer ctx Q)) := ps.map (fun p => ⟨.inl p,realPacket ctx Q oracle p⟩)

def idealHistory (ctx : Context) (Q : Nat) (ro : RawKey Q → Digest32) (ps : List (Packet ctx Q)) :
    List (Sigma (GroupAnswer ctx Q)) := ps.map (fun p => ⟨.inl p,idealPacket ctx Q ro p⟩)

def realCallers (ctx : Context) (Q : Nat) (oracle : PrimitiveOracle) (p : Packet ctx Q)
    (qs : List (CallerPosition ctx Q p)) : List (Sigma (GroupAnswer ctx Q)) :=
  qs.map (fun q => ⟨.inr (RawWHIRKeys.callerOutputKey ctx Q p q.val q.property),
    evalCoordinate (compressionOf oracle) ctx.iv q.val⟩)

def idealCallers (ctx : Context) (Q : Nat) (ro : RawKey Q → Digest32) (p : Packet ctx Q)
    (qs : List (CallerPosition ctx Q p)) : List (Sigma (GroupAnswer ctx Q)) :=
  qs.map (fun q => ⟨.inr (RawWHIRKeys.callerOutputKey ctx Q p q.val q.property),
    ro (RawWHIRKeys.callerOutputKey ctx Q p q.val q.property).val⟩)

/-- Exact cache annotation order for the coordinate-backed caller requests. -/
theorem idealCallers_groups (ctx : Context) (Q : Nat) (ro : RawKey Q → Digest32) (p : Packet ctx Q) :
    idealCallers ctx Q ro p (callerPositions ctx Q p) =
      (RawWHIRKeys.callerGroups ctx Q p).map (fun key => ⟨.inr key,ro key.val⟩) := by
  simp only [idealCallers, callerPositions, RawWHIRKeys.callerGroups, List.map_map, Function.comp_def]

def realCompletion (ctx : Context) (Q : Nat) (oracle : PrimitiveOracle) :
    Option (Packet ctx Q) → List (Sigma (GroupAnswer ctx Q))
  | none => []
  | some p => realCallers ctx Q oracle p (callerPositions ctx Q p) ++
      realHistory ctx Q oracle (terminalCompletion ctx Q (some p))

def idealCompletion (ctx : Context) (Q : Nat) (ro : RawKey Q → Digest32) :
    Option (Packet ctx Q) → List (Sigma (GroupAnswer ctx Q))
  | none => []
  | some p => idealCallers ctx Q ro p (callerPositions ctx Q p) ++
      idealHistory ctx Q ro (terminalCompletion ctx Q (some p))

theorem idealCompletion_some (ctx : Context) (Q : Nat) (ro : RawKey Q → Digest32) (p : Packet ctx Q) :
    idealCompletion ctx Q ro (some p) =
      (RawWHIRKeys.callerGroups ctx Q p).map (fun key => ⟨.inr key,ro key.val⟩) ++
        idealHistory ctx Q ro (RawWHIRKeys.ancestors ctx Q p ++ [p]) := by
  rw [idealCompletion, idealCallers_groups]
  rfl

theorem bind_real_result (oracle : PrimitiveOracle) (iv : Digest32) (p : Program R)
    (next : R → Program S) :
    (runReal oracle iv (bind p next)).view.result =
      (runReal oracle iv (next (runReal oracle iv p).view.result)).view.result := by
  induction p with
  | done r => rfl
  | ask q cont ih => simpa only [bind, runReal, prepend] using ih (realAnswer oracle iv q)

theorem readPackets_real_result (ctx : Context) (Q : Nat) (oracle : PrimitiveOracle)
    (ps : List (Packet ctx Q)) (next : List (Sigma (GroupAnswer ctx Q)) → Program R) :
    (runReal oracle ctx.iv (readPackets ctx Q ps next)).view.result =
      (runReal oracle ctx.iv (next (realHistory ctx Q oracle ps))).view.result := by
  induction ps generalizing next with
  | nil => rfl
  | cons p ps ih =>
    simp only [readPackets, WHIRModeProgram.readPacket_result, ih]
    rfl

theorem readCallerThenPackets_real_result (ctx : Context) (Q : Nat) (oracle : PrimitiveOracle)
    (p : Packet ctx Q) (qs : List (CallerPosition ctx Q p)) (ps : List (Packet ctx Q))
    (next : List (Sigma (GroupAnswer ctx Q)) → Program R) :
    (runReal oracle ctx.iv (readCallerThenPackets ctx Q p qs ps next)).view.result =
      (runReal oracle ctx.iv
        (next (realCallers ctx Q oracle p qs ++ realHistory ctx Q oracle ps))).view.result := by
  induction qs generalizing next with
  | nil => exact readPackets_real_result ctx Q oracle ps next
  | cons q qs ih =>
    simp only [readCallerThenPackets, runReal, prepend, ih]
    rfl

theorem finish_real_result (ctx : Context) (Q : Nat) (oracle : PrimitiveOracle)
    (r : R) (p : Option (Packet ctx Q)) :
    (runReal oracle ctx.iv (finish ctx Q r p)).view.result =
      ⟨r,p,realCompletion ctx Q oracle p⟩ := by
  cases p with
  | none => rfl
  | some p =>
    rw [finish, readCallerThenPackets_real_result]
    rfl

theorem append_real_result (ctx : Context) (Q : Nat) (oracle : PrimitiveOracle)
    (p : Program R) (final : R → Option (Packet ctx Q)) :
    (runReal oracle ctx.iv (append ctx Q p final)).view.result =
      let r := (runReal oracle ctx.iv p).view.result
      (⟨r,final r,realCompletion ctx Q oracle (final r)⟩ : Completed ctx Q R) := by
  rw [append, bind_real_result, finish_real_result]

/-- A construction-only packet does not change the private primitive simulator
state. Its replies are the actual mode raw keys, independent of proof budgets. -/
theorem readPacket_ideal_result {Q : Nat} {Seed State : Type} (sim : Simulator Q Seed State)
    (ro : RawKey Q → Digest32) (iv : Digest32) (state : State) (n : Nat)
    (coords : Fin n → Coordinate) (valid : ∀ i, DuplexEncoding.Admissible (coords i))
    (bound : ∀ i, pathCost (coords i) ≤ Q) (next : (Fin n → Digest32) → Program R)
    (value : (Fin n → Digest32) → R)
    (after : ∀ raw remaining (cap : remaining ≤ Q) (counted : Counts remaining (next raw)),
      (runIdeal sim ro iv state (next raw) remaining cap counted).view.result = value raw)
    (remaining : Nat) (cap : remaining ≤ Q)
    (counted : Counts remaining (WHIRModeProgram.readPacket n (fun i => .construction (coords i) (valid i)) next)) :
    (runIdeal sim ro iv state (WHIRModeProgram.readPacket n (fun i => .construction (coords i) (valid i)) next)
      remaining cap counted).view.result =
      value (fun i => ro (constructionKey Q iv (coords i) (bound i))) := by
  induction n generalizing remaining with
  | zero =>
    have h := after Fin.elim0 remaining cap counted
    have he : (fun i : Fin 0 => ro (constructionKey Q iv (coords i) (bound i))) = Fin.elim0 := by
      funext i; exact Fin.elim0 i
    simpa only [WHIRModeProgram.readPacket, he] using h
  | succ n ih =>
    let answer := ro (constructionKey Q iv (coords 0) (bound 0))
    have h := ih (fun i => coords i.succ) (fun i => valid i.succ) (fun i => bound i.succ)
      (fun rest => next (Fin.cases answer rest)) (fun rest => value (Fin.cases answer rest))
      (fun rest rem hc hn => after (Fin.cases answer rest) rem hc hn)
      (remaining-pathCost (coords 0)) (by omega) (counted.2 answer)
    have he : Fin.cases answer (fun i => ro (constructionKey Q iv (coords i.succ) (bound i.succ))) =
        (fun i => ro (constructionKey Q iv (coords i) (bound i))) := by
      funext i
      refine Fin.cases ?_ (fun j => ?_) i <;> rfl
    simpa only [WHIRModeProgram.readPacket, runIdeal, prepend, he] using h

theorem readPackets_ideal_result (ctx : Context) (Q : Nat) {Seed State : Type}
    (sim : Simulator Q Seed State) (ro : RawKey Q → Digest32) (state : State)
    (ps : List (Packet ctx Q)) (next : List (Sigma (GroupAnswer ctx Q)) → Program R)
    (value : List (Sigma (GroupAnswer ctx Q)) → R)
    (after : ∀ history remaining (cap : remaining ≤ Q) (counted : Counts remaining (next history)),
      (runIdeal sim ro ctx.iv state (next history) remaining cap counted).view.result = value history)
    (remaining : Nat) (cap : remaining ≤ Q) (counted : Counts remaining (readPackets ctx Q ps next)) :
    (runIdeal sim ro ctx.iv state (readPackets ctx Q ps next) remaining cap counted).view.result =
      value (idealHistory ctx Q ro ps) := by
  induction ps generalizing next value remaining with
  | nil => exact after [] remaining cap counted
  | cons p ps ih =>
    exact readPacket_ideal_result sim ro ctx.iv state (RawWHIRKeys.blocks ctx p.val)
      (fun i => RawWHIRKeys.coordinate ctx p.val i.val)
      (fun i => RawWHIRKeys.coordinate_admissible ctx Q ⟨p,i⟩)
      (fun i => by rw [RawWHIRKeys.pathCost_block]; exact RawWHIRKeys.packet_pathBound ctx Q p)
      (fun raw => readPackets ctx Q ps (fun rest => next (⟨.inl p,raw⟩ :: rest)))
      (fun raw => value (⟨.inl p,raw⟩ :: idealHistory ctx Q ro ps))
      (fun raw rem hc hn => ih _ _ (fun rest => after (⟨.inl p,raw⟩ :: rest)) rem hc hn)
      remaining cap counted

theorem readCallerThenPackets_ideal_result (ctx : Context) (Q : Nat) {Seed State : Type}
    (sim : Simulator Q Seed State) (ro : RawKey Q → Digest32) (state : State)
    (p : Packet ctx Q) (qs : List (CallerPosition ctx Q p)) (ps : List (Packet ctx Q))
    (next : List (Sigma (GroupAnswer ctx Q)) → Program R)
    (value : List (Sigma (GroupAnswer ctx Q)) → R)
    (after : ∀ history remaining (cap : remaining ≤ Q) (counted : Counts remaining (next history)),
      (runIdeal sim ro ctx.iv state (next history) remaining cap counted).view.result = value history)
    (remaining : Nat) (cap : remaining ≤ Q)
    (counted : Counts remaining (readCallerThenPackets ctx Q p qs ps next)) :
    (runIdeal sim ro ctx.iv state (readCallerThenPackets ctx Q p qs ps next)
      remaining cap counted).view.result =
      value (idealCallers ctx Q ro p qs ++ idealHistory ctx Q ro ps) := by
  induction qs generalizing next value remaining with
  | nil => exact readPackets_ideal_result ctx Q sim ro state ps next value after remaining cap counted
  | cons q qs ih =>
    let key := RawWHIRKeys.callerOutputKey ctx Q p q.val q.property
    let answer := ro key.val
    exact ih (fun rest => next (⟨.inr key,answer⟩ :: rest))
      (fun rest => value (⟨.inr key,answer⟩ :: rest))
      (fun rest => after (⟨.inr key,answer⟩ :: rest))
      (remaining-pathCost q.val) (by omega) (counted.2 answer)

theorem finish_ideal_result (ctx : Context) (Q : Nat) {Seed State : Type}
    (sim : Simulator Q Seed State) (ro : RawKey Q → Digest32) (state : State)
    (r : R) (p : Option (Packet ctx Q)) (remaining : Nat) (cap : remaining ≤ Q)
    (counted : Counts remaining (finish ctx Q r p)) :
    (runIdeal sim ro ctx.iv state (finish ctx Q r p) remaining cap counted).view.result =
      ⟨r,p,idealCompletion ctx Q ro p⟩ := by
  cases p with
  | none => rfl
  | some p =>
    apply readCallerThenPackets_ideal_result ctx Q sim ro state p _ _
      _ (fun history => ⟨r,some p,history⟩)
      (fun _ _ _ _ => rfl) remaining cap counted

theorem append_ideal_result (ctx : Context) (Q : Nat) {Seed State : Type}
    (sim : Simulator Q Seed State) (ro : RawKey Q → Digest32) (state : State)
    (p : Program R) (final : R → Option (Packet ctx Q)) (remaining : Nat) (cap : remaining ≤ Q)
    (before : Counts remaining p) (counted : Counts remaining (append ctx Q p final)) :
    (runIdeal sim ro ctx.iv state (append ctx Q p final) remaining cap counted).view.result =
      let r := (runIdeal sim ro ctx.iv state p remaining cap before).view.result
      (⟨r,final r,idealCompletion ctx Q ro (final r)⟩ : Completed ctx Q R) := by
  induction p generalizing state remaining with
  | done r => exact finish_ideal_result ctx Q sim ro state r (final r) remaining cap counted
  | ask q next ih =>
    cases q with
    | primitive purpose input =>
      exact ih (runRO ro (sim.answer state input)).1.2 (runRO ro (sim.answer state input)).1.1
        (remaining-1) (by omega) (before.2 _) (counted.2 _)
    | construction q valid =>
      exact ih (ro (constructionKey Q ctx.iv q (before.1.trans cap))) state
        (remaining-pathCost q) (by omega) (before.2 _) (counted.2 _)

theorem readPackets_counted (ctx : Context) (Q : Nat) (ps : List (Packet ctx Q))
    (next : List (Sigma (GroupAnswer ctx Q)) → Program R) (budget : Nat)
    (after : ∀ history, Counts budget (next history)) :
    Counts (packetsCost ctx Q ps + budget) (readPackets ctx Q ps next) := by
  induction ps generalizing next with
  | nil => simpa only [packetsCost, List.map_nil, List.sum_nil, Nat.zero_add, readPackets] using after []
  | cons p ps ih =>
    have h := WHIRModeProgram.readPacket_counted (RawWHIRKeys.blocks ctx p.val) (request ctx Q p)
      (fun raw => readPackets ctx Q ps (fun rest => next (⟨.inl p,raw⟩ :: rest)))
      (packetsCost ctx Q ps + budget) (fun raw => ih _ (fun rest => after (⟨.inl p,raw⟩ :: rest)))
    simpa only [packetsCost, List.map_cons, List.sum_cons, packetCost, request, Query.cost, Nat.add_assoc,
      readPackets] using h

theorem readCallerThenPackets_counted (ctx : Context) (Q : Nat)
    (p : Packet ctx Q) (qs : List (CallerPosition ctx Q p)) (ps : List (Packet ctx Q))
    (next : List (Sigma (GroupAnswer ctx Q)) → Program R) (budget : Nat)
    (after : ∀ history, Counts budget (next history)) :
    Counts (callerCost qs + packetsCost ctx Q ps + budget)
      (readCallerThenPackets ctx Q p qs ps next) := by
  induction qs generalizing next with
  | nil =>
    simpa only [callerCost, List.map_nil, List.sum_nil, Nat.zero_add, readCallerThenPackets]
      using readPackets_counted ctx Q ps next budget after
  | cons q qs ih =>
    simp only [readCallerThenPackets, Counts, callerCost, List.map_cons, List.sum_cons, Query.cost]
    refine ⟨by omega, fun answer => ?_⟩
    have h := ih (fun rest => next
      (⟨.inr (RawWHIRKeys.callerOutputKey ctx Q p q.val q.property),answer⟩ :: rest))
      (fun rest => after (⟨.inr (RawWHIRKeys.callerOutputKey ctx Q p q.val q.property),answer⟩ :: rest))
    convert h using 1
    dsimp only [callerCost]
    omega

theorem finish_counted (ctx : Context) (Q : Nat) (r : R) (p : Option (Packet ctx Q)) :
    Counts (completionCost ctx Q p) (finish ctx Q r p) := by
  cases p with
  | none => trivial
  | some p =>
    simpa only [Nat.add_zero, completionCost, finish] using
      readCallerThenPackets_counted ctx Q p (callerPositions ctx Q p) (terminalCompletion ctx Q (some p))
        (fun history => Program.done (⟨r,some p,history⟩ : Completed ctx Q R)) 0 (fun _ => True.intro)

/-- Every caller output and final packet block pays its entire uncached path.
Neither cached caller replies nor already-seen packets receive a silent discount. -/
theorem append_counted (ctx : Context) (Q : Nat) (p : Program R)
    (final : R → Option (Packet ctx Q)) (a b : Nat) (before : Counts a p)
    (after : ∀ r, completionCost ctx Q (final r) ≤ b) : Counts (a+b) (append ctx Q p final) :=
  bind_counted p _ a b before (fun r => counts_mono (finish_counted ctx Q r (final r)) (after r))

@[simp] theorem finish_none (ctx : Context) (Q : Nat) (r : R) :
    finish ctx Q r none = .done ⟨r,none,[]⟩ := rfl

end Whir.WHIRModeFinal
