import Whir.PublicCompressionProgram

/-! HISTORICAL byte-level hand-port of the pre-#552 tagged-scalar transcript
observed in `crates/fiat_shamir/src/lib.rs` before the #552 merge. This is NOT
the current merged #552 framed-byte duplex. The primitive is shared with
ordinary hashing and exposes its full chosen-CV interface. These historical
source equations assert neither Rust compiler equivalence nor security. -/
namespace Whir.DeployedTranscript
open FiatShamirGame DuplexRefinement DuplexFraming DuplexModeGame
open PublicCompressionProgram TypedOracleCompiler

/-- Exactly the source's three reachable pending-buffer shapes. -/
inductive Pending where
  | empty
  | one (last : Scalar24)
  | two (first last : Scalar24)

def Pending.count : Pending → Nat
  | .empty => 0
  | .one _ => 1
  | .two _ _ => 2

def Pending.first : Pending → Scalar24
  | .two first _ => first
  | _ => fun _ => 0

def Pending.last : Pending → Scalar24
  | .empty => fun _ => 0
  | .one last | .two _ last => last

/-- Tags are in block word 7. Counter 64 never encodes the role. -/
inductive Role where
  | observe | squeeze | powBase | powNonce
  deriving DecidableEq

def Role.word : Role → Nat
  | .observe => 1
  | .squeeze => 2
  | .powBase => 3
  | .powNonce => 4

/-- Words 0..2 = first scalar, word 3 = count, words 4..6 = last
scalar, word 7 = role, all little endian as in `step_block`. -/
def stepBlock (pending : Pending) (role : Role) : Block64 := fun i =>
  if h : i.val < 24 then pending.first ⟨i.val,h⟩
  else if h' : i.val < 32 then ByteCodec.encodeNat 8 pending.count ⟨i.val-24,by omega⟩
  else if h'' : i.val < 56 then pending.last ⟨i.val-32,by omega⟩
  else ByteCodec.encodeNat 8 role.word ⟨i.val-56,by omega⟩

def stepNode (cv : Digest32) (pending : Pending) (role : Role) : Node :=
  ⟨cv,stepBlock pending role,UInt64.ofNat 64,true⟩

def step (C : PrimitiveOracle) (cv : Digest32) (pending : Pending) (role : Role) : Digest32 :=
  C (stepNode cv pending role)

structure Context where
  cv : Digest32
  pending : Pending

def emptyContext (cv : Digest32) : Context := ⟨cv,.empty⟩

/-- Source `new` uses ordinary 64-byte hashing from the parameter IV;
its `iv` argument is the first message half, not the primitive chaining value. -/
def seedNode (iv publicInput : Digest32) : Node :=
  ⟨DuplexCompression.parameterIV,ByteCodec.pairBytes (iv,publicInput),UInt64.ofNat 64,true⟩

def new (C : PrimitiveOracle) (iv publicInput : Digest32) : Context :=
  emptyContext (C (seedNode iv publicInput))

/-- Source `from_label` uses the ordinary variable-length hash entry path,
including the actual length counters and final flag. No fixed seed is imposed. -/
def fromLabel (C : PrimitiveOracle) (label : List Byte) : Context :=
  emptyContext (PublicMerkleLog.hash C label)

/-- Nonmutating `state()` absorbs a nonempty buffer under tag 1. -/
def exportedState (C : PrimitiveOracle) (context : Context) : Digest32 :=
  match context.pending with
  | .empty => context.cv
  | _ => step C context.cv context.pending .observe

def stateCost (context : Context) : Nat :=
  match context.pending with
  | .empty => 0
  | _ => 1

def flush (C : PrimitiveOracle) (context : Context) : Context :=
  emptyContext (exportedState C context)

def observe (C : PrimitiveOracle) (context : Context) (scalar : Scalar24) : Context :=
  match context.pending with
  | .empty => ⟨context.cv,.one scalar⟩
  | .one previous => ⟨context.cv,.two previous scalar⟩
  | .two _ _ => ⟨exportedState C context,.one scalar⟩

def observeCost (context : Context) : Nat :=
  match context.pending with
  | .two _ _ => 1
  | _ => 0

/-- The challenge comprises exactly the first three 64-bit words. -/
def challenge (digest : Digest32) : Scalar24 := fun i => digest ⟨i.val,by omega⟩

def sample (C : PrimitiveOracle) (context : Context) : Context × Scalar24 :=
  let digest := step C context.cv context.pending .squeeze
  (emptyContext digest,challenge digest)

def powBase (C : PrimitiveOracle) (context : Context) : Digest32 :=
  step C (exportedState C context) .empty .powBase

def absorbNonce (C : PrimitiveOracle) (context : Context) (nonce : Scalar24) : Context :=
  emptyContext (step C (exportedState C context) (.one nonce) .powNonce)

/-- This predicate uses ordinary hashing, not keyed transcript `step`.
The deployed search and verification evaluate this shared primitive as well. -/
def powNode (base : Digest32) (nonce : Scalar24) : Node :=
  ⟨DuplexCompression.parameterIV,
    ByteCodec.pairBytes (base,fun i =>
      if h : i.val < 24 then nonce ⟨i.val,h⟩
      else ByteCodec.encodeNat 8 4 ⟨i.val-24,by omega⟩),UInt64.ofNat 64,true⟩

@[simp] theorem sample_context (C : PrimitiveOracle) (context : Context) :
    (sample C context).1 = emptyContext (C (stepNode context.cv context.pending .squeeze)) := rfl

@[simp] theorem sample_challenge (C : PrimitiveOracle) (context : Context) :
    (sample C context).2 = challenge (sample C context).1.cv := rfl

@[simp] theorem sample_pending (C : PrimitiveOracle) (context : Context) :
    (sample C context).1.pending = .empty := rfl

@[simp] theorem observe_empty (C : PrimitiveOracle) (cv : Digest32) (x : Scalar24) :
    observe C (emptyContext cv) x = ⟨cv,.one x⟩ := rfl

@[simp] theorem observe_second (C : PrimitiveOracle) (cv : Digest32) (x y : Scalar24) :
    observe C ⟨cv,.one x⟩ y = ⟨cv,.two x y⟩ := rfl

@[simp] theorem observe_third (C : PrimitiveOracle) (cv : Digest32) (x y z : Scalar24) :
    observe C ⟨cv,.two x y⟩ z = ⟨step C cv (.two x y) .observe,.one z⟩ := rfl

/-- Exact operational lowering counts even construction calls whose internal
answers are not publicly exposed. Public primitive calls share this same table. -/
def stateCalls : (context : Context) → Computation Digest32 (stateCost context)
  | ⟨cv,.empty⟩ => .ret cv
  | ⟨cv,.one x⟩ => .draw (stepNode cv (.one x) .observe) (fun d => .ret d)
  | ⟨cv,.two x y⟩ => .draw (stepNode cv (.two x y) .observe) (fun d => .ret d)

def observeCalls : (context : Context) → Scalar24 → Computation Context (observeCost context)
  | ⟨cv,.empty⟩, scalar => .ret ⟨cv,.one scalar⟩
  | ⟨cv,.one previous⟩, scalar => .ret ⟨cv,.two previous scalar⟩
  | ⟨cv,.two x y⟩, scalar => .draw (stepNode cv (.two x y) .observe)
      (fun d => .ret ⟨d,.one scalar⟩)

def sampleCalls (context : Context) : Computation (Context × Scalar24) 1 :=
  .draw (stepNode context.cv context.pending .squeeze) (fun d => .ret (emptyContext d,challenge d))

def newCalls (iv publicInput : Digest32) : Computation Context 1 :=
  .draw (seedNode iv publicInput) (fun d => .ret (emptyContext d))

def powBaseCalls (context : Context) : Computation Digest32 (stateCost context+1) :=
  Sampling.bind (stateCalls context) (fun d =>
    .draw (stepNode d .empty .powBase) (fun answer => .ret answer))

def absorbNonceCalls (context : Context) (nonce : Scalar24) :
    Computation Context (stateCost context+1) :=
  Sampling.bind (stateCalls context) (fun d =>
    .draw (stepNode d (.one nonce) .powNonce) (fun answer => .ret (emptyContext answer)))

theorem stateCalls_eval (C : PrimitiveOracle) (context : Context) :
    Sampling.eval C (stateCalls context) = exportedState C context := by
  cases context with
  | mk cv pending => cases pending <;> rfl

theorem observeCalls_eval (C : PrimitiveOracle) (context : Context) (scalar : Scalar24) :
    Sampling.eval C (observeCalls context scalar) = observe C context scalar := by
  cases context with
  | mk cv pending => cases pending <;> rfl

theorem sampleCalls_eval (C : PrimitiveOracle) (context : Context) :
    Sampling.eval C (sampleCalls context) = sample C context := rfl

theorem newCalls_eval (C : PrimitiveOracle) (iv publicInput : Digest32) :
    Sampling.eval C (newCalls iv publicInput) = new C iv publicInput := rfl

theorem powBaseCalls_eval (C : PrimitiveOracle) (context : Context) :
    Sampling.eval C (powBaseCalls context) = powBase C context := by
  simp only [powBaseCalls,Sampling.eval_bind,stateCalls_eval]
  rfl

theorem absorbNonceCalls_eval (C : PrimitiveOracle) (context : Context) (nonce : Scalar24) :
    Sampling.eval C (absorbNonceCalls context nonce) = absorbNonce C context nonce := by
  simp only [absorbNonceCalls,Sampling.eval_bind,stateCalls_eval]
  rfl

def countBytes (block : Block64) : Fin 8 → Byte := fun i => block ⟨i.val+24,by omega⟩
def roleBytes (block : Block64) : Fin 8 → Byte := fun i => block ⟨i.val+56,by omega⟩
def firstBytes (block : Block64) : Scalar24 := fun i => block ⟨i.val,by omega⟩
def lastBytes (block : Block64) : Scalar24 := fun i => block ⟨i.val+32,by omega⟩

@[simp] theorem countBytes_stepBlock (pending : Pending) (role : Role) :
    countBytes (stepBlock pending role) = ByteCodec.encodeNat 8 pending.count := by
  funext i
  simp [countBytes,stepBlock,show ¬i.val+24 < 24 by omega,show i.val+24 < 32 by omega]

@[simp] theorem roleBytes_stepBlock (pending : Pending) (role : Role) :
    roleBytes (stepBlock pending role) = ByteCodec.encodeNat 8 role.word := by
  funext i
  simp [roleBytes,stepBlock,show ¬i.val+56 < 24 by omega,
    show ¬i.val+56 < 32 by omega,show ¬i.val+56 < 56 by omega]

@[simp] theorem firstBytes_stepBlock (pending : Pending) (role : Role) :
    firstBytes (stepBlock pending role) = pending.first := by
  funext i
  simp [firstBytes,stepBlock,i.isLt]

@[simp] theorem lastBytes_stepBlock (pending : Pending) (role : Role) :
    lastBytes (stepBlock pending role) = pending.last := by
  funext i
  simp [lastBytes,stepBlock,show ¬i.val+32 < 24 by omega,
    show ¬i.val+32 < 32 by omega,show i.val+32 < 56 by omega]

theorem stepBlock_injective {a b : Pending} {r s : Role}
    (same : stepBlock a r = stepBlock b s) : a = b ∧ r = s := by
  have count := congrArg (ByteCodec.decodeNat 8 ∘ countBytes) same
  have role := congrArg (ByteCodec.decodeNat 8 ∘ roleBytes) same
  have first := congrArg firstBytes same
  have last := congrArg lastBytes same
  have ac : a.count < 256^8 := by cases a <;> norm_num [Pending.count]
  have bc : b.count < 256^8 := by cases b <;> norm_num [Pending.count]
  have rr : r.word < 256^8 := by cases r <;> norm_num [Role.word]
  have ss : s.word < 256^8 := by cases s <;> norm_num [Role.word]
  simp only [Function.comp_apply,countBytes_stepBlock,
    ByteCodec.decodeNat_encodeNat _ _ ac,ByteCodec.decodeNat_encodeNat _ _ bc] at count
  simp only [Function.comp_apply,roleBytes_stepBlock,
    ByteCodec.decodeNat_encodeNat _ _ rr,ByteCodec.decodeNat_encodeNat _ _ ss] at role
  simp only [firstBytes_stepBlock] at first
  simp only [lastBytes_stepBlock] at last
  constructor
  · cases a <;> cases b <;> simp_all [Pending.count,Pending.first,Pending.last]
  · cases r <;> cases s <;> simp_all [Role.word]

/-- The readonly original CV plus pending buffer uniquely names a squeeze
input. This is a codec theorem, not a hash-binding assumption. -/
theorem sampleNode_injective {a b : Context}
    (same : stepNode a.cv a.pending .squeeze = stepNode b.cv b.pending .squeeze) :
    a = b := by
  have hc := congrArg Node.cv same
  have hb := congrArg Node.block same
  have hp := (stepBlock_injective hb).1
  cases a; cases b
  simp_all [stepNode]

/-- Variable-length ordinary hashing for the source's `from_label` constructor:
every chunk has its actual counter and final flag, including an empty label. -/
def labelChunkCalls (cv : Digest32) (count : Nat) :
    (chunks : List (List Byte)) → Computation (Option Digest32) chunks.length
  | [] => .ret none
  | [b] => .draw (PublicMerkleLog.node cv count b true) (fun d => .ret (some d))
  | b :: next :: rest => .draw (PublicMerkleLog.node cv count b false)
      (fun d => labelChunkCalls d (count+b.length) (next::rest))

def fromLabelCalls (label : List Byte) :
    Computation Context (PublicMerkleLog.chunks label).length :=
  mapResult (fun out => emptyContext (out.getD DuplexCompression.parameterIV))
    (labelChunkCalls DuplexCompression.parameterIV 0 (PublicMerkleLog.chunks label))

theorem labelChunkCalls_eval (C : PrimitiveOracle) (cv : Digest32) (count : Nat)
    (chunks : List (List Byte)) :
    Sampling.eval C (labelChunkCalls cv count chunks) =
      PublicMerkleLog.run (fun n => some (C n)) cv count chunks := by
  induction chunks generalizing cv count with
  | nil => rfl
  | cons b rest ih =>
    cases rest with
    | nil => rfl
    | cons next rest =>
      simpa only [labelChunkCalls,Sampling.eval,PublicMerkleLog.run,
        Option.bind_eq_bind,Option.bind_some] using ih (C (PublicMerkleLog.node cv count b false))
          (count+b.length)

theorem fromLabelCalls_eval (C : PrimitiveOracle) (label : List Byte) :
    Sampling.eval C (fromLabelCalls label) = fromLabel C label := by
  simp only [fromLabelCalls,eval_mapResult,labelChunkCalls_eval,fromLabel,PublicMerkleLog.hash]

#print axioms stepBlock_injective
#print axioms sampleNode_injective
#print axioms fromLabelCalls_eval

#print axioms sampleCalls_eval
#print axioms powBaseCalls_eval
#print axioms absorbNonceCalls_eval
end Whir.DeployedTranscript
