import Whir.WHIRFiatShamir
import Whir.WHIRHistory
import Whir.TypedOracleCompiler
import Whir.DuplexRefinement
import Whir.WHIRReplay
import Whir.WHIRHistoryKey

/-! Source-pinned streaming interface and classical typed stopped-ROM game.
The full-public-view random-compression mode coupling is proved separately in
`PublicCompressionModeSecurity`; this module proves the typed ROM list bound,
not deterministic primitive security or universal deployed-source refinement. -/
namespace Whir.WHIRROM
open Concrete Protocol CausalGame CausalProbability ParameterBounds
open FiatShamirGame WHIRFiatShamir
open Classical

abbrev Key (p : Profile) :=
  TypedFiatShamirGame.FullInput Digest32 WHIRHistory.Pending (Coordinate (config p)) Sample

def query (p : Profile) : Digest32 × List WHIRHistory.Pending → Coordinate (config p) :=
  WHIRHistory.queryFor (config p)

/-- The canonical syntax recovery model shared with the physical key-injection
proof. The domain and statement are part of the framed history. -/
def beforeModel (p : Profile) (domain : Digest32) (key : Key p) : DuplexRefinement.Model :=
  WHIRHistoryKey.beforeModel (WHIRHistoryKey.standaloneWidth (config p))
    domain key.statement key.messages
theorem beforeModel_consumed (p : Profile) (domain : Digest32) (key : Key p)
    (normal : WHIRHistoryKey.Normal key.messages) : (beforeModel p domain key).consumed = 0 := by
  rcases key with ⟨statement,messages,ancestors⟩
  change WHIRHistoryKey.Normal messages at normal
  unfold beforeModel
  cases normal with
  | initial => rfl
  | @cons ps prior m nonempty =>
    have bytes : WHIRHistory.scalarBytes m.scalars ≠ [] :=
      fun h => nonempty ((WHIRHistory.scalarBytes_empty _).mp h)
    simp only [WHIRHistoryKey.beforeModel, WHIRHistory.pendingModel]
    cases m.nonce <;> simp [DuplexRefinement.modelAbsorb, bytes, DuplexRefinement.modelNonce]

theorem stream_ofFn (compression : DuplexRefinement.Compression) (cv : Digest32)
    (offset n : Nat) :
    DuplexRefinement.stream compression cv offset n =
      List.ofFn (fun i : Fin n => DuplexRefinement.outputBlock compression cv
        ((offset+i.val)/32) ⟨(offset+i.val)%32,Nat.mod_lt _ (by decide)⟩) := by
  induction n generalizing offset with
  | zero => rfl
  | succ n ih =>
    simp only [DuplexRefinement.stream, List.ofFn_succ, Fin.val_zero, Nat.add_zero]
    rw [ih]
    congr 1
    apply congrArg List.ofFn
    funext i
    simp only [Fin.val_succ]
    simp only [Nat.add_left_comm, Nat.add_comm]

/-- Byte positions are disjoint scalar24 slices. In particular, lambda follows
all query chunks in the same vector; it is not another allocation. -/
def slices {c : Config} (q : Coordinate c) (bytes : List Byte) : Bytes q :=
  match q with
  | .initial => fun j => bytes[j.val]!
  | .fold _ _ => fun j => bytes[j.val]!
  | .ood _ _ => fun i j => bytes[24*i.val+j.val]!
  | .query i => (fun k j => bytes[24*k.val+j.val]!,
      fun j => bytes[24*queryChunks c i+j.val]!)
  | .tail _ => fun j => bytes[j.val]!

/-- The concrete #552 framed-history stream; the reference oracle recomputes
full root-to-terminal paths, so resource accounting cannot claim cached work. -/
def modeOracle (p : Profile) (compression : DuplexRefinement.Compression)
    (iv domain : Digest32) : TypedFiatShamirGame.Oracle (A := Sample) (query p) := fun key =>
  let m := beforeModel p domain key
  let q := query p (key.statement, key.messages)
  codec q (slices q (DuplexRefinement.stream compression
    (DuplexRefinement.evalHistory compression iv (DuplexRefinement.closeRun m).history)
    m.consumed (24 * WHIRHistory.scalarCount q)))

/-- This is an equality to the actual checked streaming operation, not a parser
or mode-correctness hypothesis. Reachability/limits are checked separately. -/
theorem modeOracle_squeeze (p : Profile) (compression : DuplexRefinement.Compression)
    (iv domain : Digest32) (key : Key p) (state next : DuplexRefinement.State)
    (bytes : List Byte)
    (represents : DuplexRefinement.Represents compression iv (beforeModel p domain key) state)
    (squeezed : DuplexRefinement.squeeze compression state
      (24 * WHIRHistory.scalarCount (query p (key.statement, key.messages))) = .ok (next, bytes)) :
    modeOracle p compression iv domain key =
      codec (query p (key.statement, key.messages))
        (slices (query p (key.statement, key.messages)) bytes) := by
  have h := DuplexRefinement.squeeze_frame_bytes compression iv (beforeModel p domain key)
    state next represents _ bytes squeezed
  unfold modeOracle
  rw [h]

def appendScalar (n : Nat) :
    ((Fin n → Scalar24) × Scalar24) ≃ (Fin (n+1) → Scalar24) where
  toFun p := Fin.lastCases p.2 p.1
  invFun f := (fun i => f i.castSucc, f (Fin.last n))
  left_inv p := by
    apply Prod.ext
    · funext i
      simp only [Fin.lastCases_castSucc]
    · simp only [Fin.lastCases_last]
  right_inv f := by
    funext i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · exact Fin.lastCases_last
    · exact Fin.lastCases_castSucc j

def scalarVector {c : Config} (q : Coordinate c) :
    Bytes q ≃ (Fin (WHIRHistory.scalarCount q) → Scalar24) :=
  match q with
  | .initial => (Equiv.funUnique (Fin 1) Scalar24).symm
  | .fold _ _ => (Equiv.funUnique (Fin 1) Scalar24).symm
  | .ood _ _ => Equiv.refl _
  | .query i => appendScalar (queryChunks c i)
  | .tail _ => (Equiv.funUnique (Fin 1) Scalar24).symm

/-- Bijection to the actual contiguous field-byte region, before independent
whole-block padding. There are no per-tag uniformity shortcuts. -/
def packedBytes {c : Config} (q : Coordinate c) :
    Bytes q ≃ (Fin (WHIRHistory.scalarCount q * 24) → Byte) :=
  (scalarVector q).trans
    ((Equiv.curry (Fin (WHIRHistory.scalarCount q)) (Fin 24) Byte).symm.trans
      (Equiv.arrowCongr finProdFinEquiv (Equiv.refl Byte)))

theorem packed_average {c : Config} (q : Coordinate c) (f : Sample q → ℚ) :
    average (fun bytes : Fin (WHIRHistory.scalarCount q * 24) → Byte =>
      f (codec q ((packedBytes q).symm bytes))) = average f := by
  have h : average (fun bytes : Fin (WHIRHistory.scalarCount q * 24) → Byte =>
      f (codec q ((packedBytes q).symm bytes))) =
      average (fun bytes : Bytes q => f (codec q bytes)) := by
    unfold average
    rw [Fintype.sum_equiv (packedBytes q).symm
      (fun bytes => f (codec q ((packedBytes q).symm bytes)))
      (fun bytes : Bytes q => f (codec q bytes)) (fun _ => rfl),
      Fintype.card_congr (packedBytes q).symm]
  exact h.trans (codec_average q f)

private theorem byte_at {n : Nat} (bytes : Fin n → Byte) (i : Nat) (hi : i < n) :
    (List.ofFn bytes)[i]! = bytes ⟨i, hi⟩ := by
  rw [getElem!_pos _ _ (by simpa using hi)]
  exact List.getElem_ofFn _

theorem slices_packed {c : Config} (q : Coordinate c)
    (bytes : Fin (WHIRHistory.scalarCount q * 24) → Byte) :
    slices q (List.ofFn bytes) = (packedBytes q).symm bytes := by
  cases q with
  | initial =>
    funext j
    change (List.ofFn bytes)[j.val]! = bytes j
    exact byte_at bytes j.val j.isLt
  | fold i k =>
    funext j
    change (List.ofFn bytes)[j.val]! = bytes j
    exact byte_at bytes j.val j.isLt
  | tail k =>
    funext j
    change (List.ofFn bytes)[j.val]! = bytes j
    exact byte_at bytes j.val j.isLt
  | ood i k =>
    funext l j
    have h : 24*l.val+j.val < remaining c i * 24 := by omega
    change (List.ofFn bytes)[24*l.val+j.val]! = bytes ⟨j.val+24*l.val, by simp only [WHIRHistory.scalarCount]; omega⟩
    rw [byte_at bytes _ h]
    congr 1
    apply Fin.ext
    dsimp only
    omega
  | query i =>
    apply Prod.ext
    · funext l j
      have h : 24*l.val+j.val < (queryChunks c i+1)*24 := by omega
      change (List.ofFn bytes)[24*l.val+j.val]! = bytes ⟨j.val+24*l.val, by simp only [WHIRHistory.scalarCount]; omega⟩
      rw [byte_at bytes _ h]
      congr 1
      apply Fin.ext
      dsimp only
      omega
    · funext j
      have h : 24*queryChunks c i+j.val < (queryChunks c i+1)*24 := by omega
      change (List.ofFn bytes)[24*queryChunks c i+j.val]! =
        bytes ⟨j.val+24*queryChunks c i, by simp only [WHIRHistory.scalarCount]; omega⟩
      rw [byte_at bytes _ h]
      congr 1
      apply Fin.ext
      dsimp only
      omega

theorem slices_average {c : Config} (q : Coordinate c) (f : Sample q → ℚ) :
    average (fun bytes : Fin (WHIRHistory.scalarCount q * 24) → Byte =>
      f (codec q (slices q (List.ofFn bytes)))) = average f := by
  simp_rw [slices_packed]
  exact packed_average q f

def splitBytes (n m : Nat) :
    (Fin (n+m) → Byte) ≃ (Fin n → Byte) × (Fin m → Byte) where
  toFun f := (fun i => f (i.castAdd m), fun j => f (j.natAdd n))
  invFun p := Fin.addCases p.1 p.2
  left_inv f := by
    funext i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;> simp
  right_inv p := by
    apply Prod.ext <;> funext i <;> simp

/-- Projection from a padded maximal byte vector preserves the exact payload
distribution. Unused final-block bytes never become additional challenges. -/
theorem padded_average {c : Config} (q : Coordinate c) (padding : Nat)
    (f : Sample q → ℚ) :
    average (fun bytes : Fin (WHIRHistory.scalarCount q * 24 + padding) → Byte =>
      f (codec q (slices q (List.ofFn (fun i => bytes (i.castAdd padding)))))) =
      average f := by
  let n := WHIRHistory.scalarCount q * 24
  let g := fun bytes : Fin n → Byte => f (codec q (slices q (List.ofFn bytes)))
  have hs : average (fun bytes : Fin (n+padding) → Byte =>
      g (fun i => bytes (i.castAdd padding))) =
      average (fun pair : (Fin n → Byte) × (Fin padding → Byte) => g pair.1) := by
    unfold average
    rw [Fintype.sum_equiv (splitBytes n padding)
      (fun bytes => g (fun i => bytes (i.castAdd padding)))
      (fun pair => g pair.1) (fun _ => rfl), Fintype.card_congr (splitBytes n padding)]
  exact hs.trans ((padding_average g).trans (slices_average q f))

def blockBytes (n : Nat) : (Fin n → Digest32) ≃ (Fin (n*32) → Byte) :=
  (Equiv.curry (Fin n) (Fin 32) Byte).symm.trans
    (Equiv.arrowCongr finProdFinEquiv (Equiv.refl Byte))

def outputBlocks {c : Config} (q : Coordinate c) : Nat :=
  (WHIRHistory.scalarCount q * 24 + 31) / 32

theorem payload_le_outputBlocks {c : Config} (q : Coordinate c) :
    WHIRHistory.scalarCount q * 24 ≤ outputBlocks q * 32 := by
  unfold outputBlocks
  omega

def blockDecode {c : Config} (q : Coordinate c) (raw : Fin (outputBlocks q) → Digest32) :
    Sample q :=
  codec q (slices q (List.ofFn (fun i : Fin (WHIRHistory.scalarCount q * 24) =>
    blockBytes (outputBlocks q) raw ⟨i.val, lt_of_lt_of_le i.isLt (payload_le_outputBlocks q)⟩)))

/-- Exact projection of independently uniform 32-byte output blocks to the
maximal WHIR vector. A partial last block contributes no additional event. -/
theorem block_average {c : Config} (q : Coordinate c) (f : Sample q → ℚ) :
    average (fun raw : Fin (outputBlocks q) → Digest32 => f (blockDecode q raw)) =
      average f := by
  let n := WHIRHistory.scalarCount q * 24
  let total := outputBlocks q * 32
  have enough : n ≤ total := payload_le_outputBlocks q
  have size : n+(total-n) = total := by omega
  let payload := fun bytes : Fin total → Byte =>
    f (codec q (slices q (List.ofFn (fun i : Fin n =>
      bytes ⟨i.val, lt_of_lt_of_le i.isLt enough⟩))))
  have first : average (fun raw : Fin (outputBlocks q) → Digest32 =>
      f (blockDecode q raw)) = average payload := by
    unfold average
    rw [Fintype.sum_equiv (blockBytes (outputBlocks q))
      (fun raw => f (blockDecode q raw)) payload (fun _ => rfl),
      Fintype.card_congr (blockBytes (outputBlocks q))]
  have second : average payload =
      average (fun bytes : Fin (n+(total-n)) → Byte =>
        f (codec q (slices q (List.ofFn (fun i : Fin n => bytes (i.castAdd (total-n))))))) := by
    let e := Equiv.arrowCongr (finCongr size.symm) (Equiv.refl Byte)
    unfold average
    rw [Fintype.sum_equiv e payload
      (fun bytes => f (codec q (slices q
        (List.ofFn (fun i : Fin n => bytes (i.castAdd (total-n))))))) (fun _ => rfl),
      Fintype.card_congr e]
  exact first.trans (second.trans (padded_average q (total-n) f))

abbrev Packet {p : Profile} (key : Key p) :=
  Fin (outputBlocks (query p (key.statement,key.messages))) → Digest32

/-- Replace each fresh maximal-vector allocation by its complete packet of
32-byte outputs. Cache hits remain absent from the allocation tree. -/
def packetize {p : Profile} {R : Type*} {n : Nat} :
    TypedOracleCompiler.Sampling (Key p) (TypedOracleCompiler.Fiber (query p)) R n →
      TypedOracleCompiler.Sampling (Key p) Packet R n
  | .ret r => .ret r
  | .draw key next => .draw key (fun raw =>
      packetize (next (blockDecode (query p (key.statement,key.messages)) raw)))

theorem packetize_eval {p : Profile} {R : Type*} {n : Nat}
    (oracle : (key : Key p) → Packet key)
    (tree : TypedOracleCompiler.Sampling (Key p) (TypedOracleCompiler.Fiber (query p)) R n) :
    TypedOracleCompiler.Sampling.eval oracle (packetize tree) =
      TypedOracleCompiler.Sampling.eval (Answer := TypedOracleCompiler.Fiber (query p))
        (fun key : Key p => blockDecode (query p (key.statement,key.messages)) (oracle key)) tree := by
  induction tree with
  | ret r => rfl
  | draw key next ih =>
    simp only [packetize, TypedOracleCompiler.Sampling.eval]
    exact ih _

/-- Equality for every terminal payoff, not merely the PCS failure indicator. -/
theorem packetize_distribution {p : Profile} {R : Type*} {n : Nat}
    (payoff : R → ℚ)
    (tree : TypedOracleCompiler.Sampling (Key p) (TypedOracleCompiler.Fiber (query p)) R n) :
    TypedOracleCompiler.Sampling.expectation payoff (packetize tree) =
      TypedOracleCompiler.Sampling.expectation payoff tree := by
  induction tree with
  | ret r => rfl
  | draw key next ih =>
    simp only [packetize, TypedOracleCompiler.Sampling.expectation]
    simp_rw [ih]
    exact block_average (query p (key.statement,key.messages))
      (fun a => TypedOracleCompiler.Sampling.expectation payoff (next a))

def physicalPacket (p : Profile) (compression : DuplexRefinement.Compression)
    (iv domain : Digest32) (key : Key p) : Packet key := fun i =>
  DuplexRefinement.evalCoordinate compression iv
    (WHIRHistoryKey.outputKey (WHIRHistoryKey.standaloneWidth (config p))
      domain key.statement key.messages i.val)

/-- Whole-packet construction queries evaluate to exactly the bytes consumed
by the pinned streaming implementation, not a separate transcript oracle. -/
theorem modeOracle_packet (p : Profile) (compression : DuplexRefinement.Compression)
    (iv domain : Digest32) (key : Key p) (normal : WHIRHistoryKey.Normal key.messages) :
    modeOracle p compression iv domain key =
      blockDecode (query p (key.statement,key.messages))
        (physicalPacket p compression iv domain key) := by
  unfold modeOracle
  dsimp only
  rw [beforeModel_consumed p domain key normal, stream_ofFn]
  simp only [Nat.zero_add]
  unfold blockDecode
  rw [Nat.mul_comm 24]
  rfl

def keyBad (p : Profile) (catalog : WHIRReplay.Catalog p) (roots : WHIRReplay.Roots)
    (key : Key p) (x : Sample (query p (key.statement,key.messages))) : Prop :=
  match WHIRReplay.decode p catalog roots key with
  | none => False
  | some replay => allocationBad (WHIRReplay.request key replay) x

theorem key_sparse (p : Profile) (catalog : WHIRReplay.Catalog p) (roots : WHIRReplay.Roots)
    (key : Key p) :
    average (fun x => if keyBad p catalog roots key x then 1 else 0) ≤ eta p := by
  cases decoded : WHIRReplay.decode p catalog roots key with
  | none => simp only [keyBad, decoded, ↓reduceIte, average_const]; exact eta_nonneg p
  | some replay =>
    simp only [keyBad, decoded]
    convert allocation_sparse p (WHIRReplay.request key replay) using 1
    rfl

/-- The predicate runs the actual causal verifier on the concretely parsed
canonical transcript and tests the commitment-time candidate list. -/
def FalseOpening {p : Profile} (r : WHIRReplay.Replay p) : Prop :=
  experiment r.statement.input (CausalStrategy.indexedStrategy r.replies) r.tape = true ∧
  ¬ ∃ w ∈ InitialCandidates.witnesses (config p) r.statement.lanes r.statement.root,
    ∀ claim ∈ r.statement.claims.toList,
      dot (paddedWitness (config p) r.statement.lanes w) claim.weight = claim.value

abbrev TerminalView (p : Profile) (B : Nat) :=
  TypedOracleCompiler.Terminal (A := @Sample (config p)) (query p) B

/-- A final submission must contain the entire fixed challenge schedule, and
must parse under the actual scalar decoder. No algebraic success defines syntax. -/
def TerminalFailure (p : Profile) (catalog : WHIRReplay.Catalog p) (roots : WHIRReplay.Roots)
    {B : Nat} (result : TerminalView p B) : Prop :=
  ∃ head past, ∃ x : Sample (query p (result.request.statement,result.request.messages)),
    ∃ replay : WHIRReplay.Replay p,
      result.allocation.history =
        (head,⟨query p (result.request.statement,result.request.messages),x⟩)::past ∧
      result.request.messages.length = WHIRHistory.depth (config p) ∧
      WHIRReplay.decode p catalog roots
        ⟨result.request.statement,result.request.messages,past⟩ = some replay ∧
      FalseOpening (WHIRReplay.finish
        ⟨result.request.statement,result.request.messages,past⟩ replay x)

/-- Accepted false final replays are covered by an actual fresh allocation in
the compiler trace, including when that allocation was made on a cloned branch. -/
theorem recorded_terminal_cover (p : Profile) (catalog : WHIRReplay.Catalog p)
    (roots : WHIRReplay.Roots) {B : Nat}
    (trace : List (Sigma (TypedOracleCompiler.Fiber (query p)))) (result : TerminalView p B)
    (recorded : TypedOracleCompiler.HistoryRecorded (query p) result.request.statement
      trace result.request.messages result.allocation.history)
    (failed : TerminalFailure p catalog roots result) :
    ∃ ka ∈ trace, keyBad p catalog roots ka.1 ka.2 := by
  obtain ⟨head,past,x,replay,history,length,decoded,failed⟩ := failed
  let key : Key p := ⟨result.request.statement,result.request.messages,past⟩
  let final := WHIRReplay.finish key replay x
  change FalseOpening final at failed
  obtain ⟨q,bad⟩ := accepted_false_prefix_cover p final.statement
    (CausalStrategy.indexedStrategy final.replies) final.tape failed.1 failed.2
  let i := result.request.messages.length - position q - 1
  have bound : position q < result.request.messages.length := by
    rw [length]
    exact WHIRHistory.position_lt_depth q
  have hi : i < key.messages.length := by dsimp [i,key]; omega
  rw [history] at recorded
  obtain ⟨m,tail,ancestors,a,before,_,allocated,parsed,agree,sample,pos⟩ :=
    WHIRReplay.trace_realization catalog roots key replay decoded x head trace recorded i hi
  have qeq : q = query p (key.statement,m::tail) := by
    apply CausalPrefix.position_injective
    change position q = position (WHIRReplay.query p (key.statement,m::tail))
    rw [pos]
    dsimp [i,key]
    omega
  subst q
  refine ⟨⟨⟨key.statement,m::tail,ancestors⟩,a⟩,allocated,?_⟩
  simp only [keyBad, parsed]
  change allocationBad (requestOfTape before.statement
    (CausalStrategy.indexedStrategy before.replies)
    (query p (key.statement,m::tail)) before.tape) a
  have congr := CausalStrategy.allocationBad_indexed_congr p before.statement
    before.replies final.replies (query p (key.statement,m::tail))
    before.tape final.tape a agree.replies agree.tape
  apply congr.mpr
  rw [agree.statement]
  exact Eq.mp (congrArg (fun value : Sample (query p (key.statement,m::tail)) =>
    allocationBad (requestOfTape final.statement (CausalStrategy.indexedStrategy final.replies)
      (query p (key.statement,m::tail)) final.tape) value) sample) bad

theorem terminal_cover (p : Profile) (catalog : WHIRReplay.Catalog p)
    (roots : WHIRReplay.Roots) {B K : Nat}
    (machine : TypedOracleCompiler.Machine Digest32 WHIRHistory.Pending
      (@Sample (config p)) B K) (trace result)
    (run : TypedOracleCompiler.Sampling.Runs
      (TypedOracleCompiler.compile (query p) machine (fun _ => none)) trace result)
    (failed : TerminalFailure p catalog roots result) :
    ∃ ka ∈ trace, keyBad p catalog roots ka.1 ka.2 :=
  recorded_terminal_cover p catalog roots trace result
    (TypedOracleCompiler.final_history_in_trace (query p) machine run) failed

/-- Full adaptive stopped-ROM list binding. The only hypothesis on a machine is
the syntactic request-depth cap encoded by its type; the final verifier run is
included in `K+1`. There is no supplied acceptance-to-event implication. -/
theorem rom_list_binding (p : Profile) (catalog : WHIRReplay.Catalog p)
    (roots : WHIRReplay.Roots) {B K : Nat}
    (machine : TypedOracleCompiler.Machine Digest32 WHIRHistory.Pending
      (@Sample (config p)) B K) :
    TypedOracleCompiler.Sampling.failureProbability (TerminalFailure p catalog roots)
      (TypedOracleCompiler.compile (query p) machine (fun _ => none)) ≤
      min 1 (((B*(K+1) : Nat) : ℚ) * eta p) := by
  apply le_min
  · apply TypedOracleCompiler.Sampling.expectation_le_one
    intro result
    split <;> norm_num
  · exact TypedOracleCompiler.compiler_failure_bound (query p) machine
      (keyBad p catalog roots) (TerminalFailure p catalog roots)
      (eta p) (eta_nonneg p) (key_sparse p catalog roots)
      (terminal_cover p catalog roots machine)

theorem rom_list_binding_numeric (p : Profile) (catalog : WHIRReplay.Catalog p)
    (roots : WHIRReplay.Roots) {B K : Nat}
    (machine : TypedOracleCompiler.Machine Digest32 WHIRHistory.Pending
      (@Sample (config p)) B K) :
    TypedOracleCompiler.Sampling.failureProbability (TerminalFailure p catalog roots)
      (TypedOracleCompiler.compile (query p) machine (fun _ => none)) ≤
      min 1 (((B*(K+1) : Nat) : ℚ) / 2^79) := by
  apply (rom_list_binding p catalog roots machine).trans
  apply min_le_min_left
  simpa only [div_eq_mul_inv, one_div, one_mul] using
    mul_le_mul_of_nonneg_left (eta_le p) (Nat.cast_nonneg (B*(K+1)))

end Whir.WHIRROM
