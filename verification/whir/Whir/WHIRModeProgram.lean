import Whir.WHIRROM
import Whir.DuplexModeGame

/-! Executable construction-query realization of the typed compiler. This is
only the checked construction linker; direct primitive/simulator interactions
remain in DuplexModeGame's shared public-oracle experiment. -/
namespace Whir.WHIRModeProgram
open Concrete Protocol CausalProbability ParameterBounds FiatShamirGame WHIRROM
open DuplexModeGame

variable {R : Type}

def readPacket (n : Nat) (request : Fin n → Query)
    (next : (Fin n → Digest32) → Program R) : Program R :=
  match n with
  | 0 => next Fin.elim0
  | n+1 => .ask (request 0) (fun first =>
      readPacket n (fun i => request i.succ) (fun rest => next (Fin.cases first rest)))

theorem readPacket_result (oracle : PrimitiveOracle) (iv : Digest32) (n : Nat)
    (request : Fin n → Query) (next : (Fin n → Digest32) → Program R) :
    (runReal oracle iv (readPacket n request next)).view.result =
      (runReal oracle iv (next (fun i => realAnswer oracle iv (request i)))).view.result := by
  induction n with
  | zero =>
    unfold readPacket
    congr 3
    apply congrArg next
    funext i
    exact Fin.elim0 i
  | succ n ih =>
    simp only [readPacket, runReal, prepend]
    rw [ih]
    congr 3
    apply congrArg next
    funext i
    refine Fin.cases ?_ (fun j => ?_) i <;> rfl

def coordinate (p : Profile) (domain : Digest32) (key : WHIRROM.Key p) (block : Nat) :
    FiatShamirGame.Coordinate :=
  WHIRHistoryKey.outputKey (WHIRHistoryKey.standaloneWidth (config p))
    domain key.statement key.messages block

def AdmissibleTree {p : Profile} (domain : Digest32) {n : Nat} :
    TypedOracleCompiler.Sampling (WHIRROM.Key p)
      WHIRROM.Packet R n → Prop
  | .ret _ => True
  | .draw key next => WHIRHistoryKey.Normal key.messages ∧
      (∀ i : Fin (outputBlocks (WHIRROM.query p (key.statement,key.messages))),
        DuplexEncoding.Admissible (coordinate p domain key i.val)) ∧
      ∀ a, AdmissibleTree domain (next a)

def ScheduledTree {p : Profile} {n : Nat} :
    TypedOracleCompiler.Sampling (WHIRROM.Key p)
      WHIRROM.Packet R n → Prop
  | .ret _ => True
  | .draw key next => key.messages ≠ [] ∧
      WHIRHistory.scheduledAdmissible (config p) key.messages = true ∧
      ∀ a, ScheduledTree (next a)

theorem scheduled_admissible {p : Profile} (domain : Digest32) {n : Nat}
    (tree : TypedOracleCompiler.Sampling (WHIRROM.Key p)
      WHIRROM.Packet R n)
    (scheduled : ScheduledTree tree) : AdmissibleTree domain tree := by
  induction tree with
  | ret r => trivial
  | draw key next ih =>
    refine ⟨WHIRHistoryKey.scheduled_normal _ _ scheduled.1 scheduled.2.1, ?_,
      fun a => ih a (scheduled.2.2 a)⟩
    intro i
    apply WHIRHistoryKey.production_outputKey_admissible p domain key.statement key.messages
      i.val scheduled.1 scheduled.2.1
    simpa only [WHIRHistoryKey.standaloneWidth, outputBlocks, WHIRROM.query,
      WHIRHistory.queryFor, List.getD, Nat.mul_comm] using i.isLt

def program {p : Profile} (domain : Digest32) {n : Nat}
    (tree : TypedOracleCompiler.Sampling (WHIRROM.Key p)
      WHIRROM.Packet R n)
    (valid : AdmissibleTree domain tree) : Program R :=
  match tree with
  | .ret r => .done r
  | .draw key next =>
    readPacket (outputBlocks (WHIRROM.query p (key.statement,key.messages)))
      (fun i => .construction (coordinate p domain key i.val) (valid.2.1 i))
      (fun raw => program domain (next raw) (valid.2.2 raw))

/-- Concrete evaluation equality, with no distribution, correctness, or PCS
acceptance assumption. The side condition is solely checked frame syntax. -/
theorem program_real_result {p : Profile} (domain : Digest32) (oracle : PrimitiveOracle)
    (iv : Digest32) {n : Nat}
    (tree : TypedOracleCompiler.Sampling (WHIRROM.Key p)
      WHIRROM.Packet R n)
    (valid : AdmissibleTree domain tree) :
    (runReal oracle iv (program domain tree valid)).view.result =
      TypedOracleCompiler.Sampling.eval (physicalPacket p (compressionOf oracle) iv domain) tree := by
  induction tree with
  | ret r => rfl
  | draw key next ih =>
    simp only [program]
    rw [readPacket_result]
    rw [ih]
    simp only [TypedOracleCompiler.Sampling.eval]
    rfl

theorem readPacket_counted (n : Nat) (request : Fin n → Query)
    (next : (Fin n → Digest32) → Program R) (budget : Nat)
    (after : ∀ raw, Counts budget (next raw)) :
    Counts ((∑ i, (request i).cost) + budget) (readPacket n request next) := by
  induction n generalizing budget with
  | zero => simpa only [readPacket, Fin.sum_univ_zero, Nat.zero_add] using after Fin.elim0
  | succ n ih =>
    simp only [readPacket, Counts, Fin.sum_univ_succ]
    constructor
    · omega
    · intro first
      convert ih (fun i => request i.succ) (fun rest => next (Fin.cases first rest))
        budget (fun rest => after (Fin.cases first rest)) using 1
      omega

/-- Every output block pays its complete uncached primitive path. -/
def packetCost (p : Profile) (domain : Digest32) (key : WHIRROM.Key p) : Nat :=
  ∑ i : Fin (outputBlocks (WHIRROM.query p (key.statement,key.messages))),
    DuplexFraming.pathCost (coordinate p domain key i.val)

def CostBound {p : Profile} (domain : Digest32) {n : Nat} (Q : Nat) :
    TypedOracleCompiler.Sampling (WHIRROM.Key p)
      WHIRROM.Packet R n → Prop
  | .ret _ => True
  | .draw key next => packetCost p domain key ≤ Q ∧
      ∀ a, CostBound domain (Q-packetCost p domain key) (next a)

theorem program_counted {p : Profile} (domain : Digest32) {n Q : Nat}
    (tree : TypedOracleCompiler.Sampling (WHIRROM.Key p)
      WHIRROM.Packet R n)
    (valid : AdmissibleTree domain tree) (counted : CostBound domain Q tree) :
    Counts Q (program domain tree valid) := by
  induction tree generalizing Q with
  | ret r => trivial
  | draw key next ih =>
    have h := readPacket_counted
      (outputBlocks (WHIRROM.query p (key.statement,key.messages)))
      (fun i => Query.construction (coordinate p domain key i.val) (valid.2.1 i))
      (fun raw => program domain (next raw) (valid.2.2 raw))
      (Q-packetCost p domain key)
      (fun raw => ih _ (valid.2.2 _) (counted.2 _))
    change Counts (packetCost p domain key + (Q-packetCost p domain key))
      (program domain (.draw key next) valid) at h
    simpa only [Nat.add_sub_of_le counted.1] using h

end Whir.WHIRModeProgram
