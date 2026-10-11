import Whir.Soundness

/-! Ordinary, classical full-transcript ROM adapter for the #552 framed-history
contract. This module proves causal ancestor completion, its finite allocation
cap, and a stopped grouped sparse-relation reduction. It does not assert Rust
refinement, a compression-mode theorem, PCS RBR soundness, or a PoW advantage.
All those boundaries are explicit below. The reference is #552's
`doc/leanvm/body/08-end-to-end-protocol.tex:60-80` at
`ff6a275304a3b577118b066ddcff83bfafa5998d`; the older #551 transcript
does not inherit this correspondence automatically. -/
namespace Whir.FiatShamirGame
open scoped BigOperators

abbrev Byte := Fin 256
abbrev Digest32 := Fin 32 → Byte
abbrev Scalar24 := Fin 24 → Byte

/-- Completed absorb runs, not raw API-call logs. The consumed count is history
data: it does not instruct the adapter to expand earlier streams. -/
inductive Frame where
  | absorb (previousConsumed : Nat) (bytes : List Byte)
  | nonce (previousConsumed difficulty : Nat) (nonce : Scalar24)
  deriving DecidableEq

structure FramedHistory where
  domain : Digest32
  statement : Digest32
  frames : List Frame
  deriving DecidableEq

/-- The three disjoint terminal families of the single DMV mode. -/
inductive Terminal where
  | output (block : Nat)
  | commitment (consumed : Nat)
  | powBase (consumed difficulty : Nat)

structure Coordinate where
  history : FramedHistory
  terminal : Terminal

/-- The query-vector squeezes and adjacent lambda are indivisible here. -/
inductive BatchKind where
  | initial
  | fold (level round : Nat)
  | ood (level index dimension : Nat)
  | queryAndLambda (level queryChunks : Nat)
  | tail (round : Nat)
  deriving DecidableEq

/-- Typed transcript messages identify what must be absorbed/reconstructed.
Merkle side hints are deliberately absent: their authentication is separate. -/
inductive Message where
  | root (digest : Digest32)
  | intro (coefficients : List Scalar24)
  | roundPolynomial (coefficients : List Scalar24)
  | oodAnswer (value : Scalar24)
  | residual (values : List Scalar24)
  | nonce (difficulty : Nat) (value : Scalar24)

structure Turn where
  messages : List Message
  batch : BatchKind

/-- Specification events, including authenticated but unabsorbed side data.
These fragments state the order required of the source-specific parser; they
are not a theorem equating a hand port to Rust. -/
inductive Event where
  | seed (domain statement : Digest32)
  | absorb (message : Message)
  | challenge (batch : BatchKind)
  | authenticate (level : Nat)

def initialTrace (domain statement root : Digest32) (boundClaims : List Message)
    (intro : List Scalar24) : List Event :=
  [.seed domain statement, .absorb (.root root)] ++ boundClaims.map Event.absorb ++
    [.challenge .initial, .absorb (.intro intro)]

def foldTrace (level round : Nat) (coefficients : List Scalar24) : List Event :=
  [.challenge (.fold level round), .absorb (.roundPolynomial coefficients)]

def oodTrace (level index dimension : Nat) (answer : Scalar24)
    (intro : List Scalar24) : List Event :=
  [.challenge (.ood level index dimension), .absorb (.oodAnswer answer),
    .absorb (.intro intro)]

/-- `queryChunks` field squeezes plus one scalar are one maximal run, before
authentication/intro. No intermediate prover turn or extra ROM query is added. -/
def queryTrace (level queryChunks : Nat) (intro : List Scalar24) : List Event :=
  [.challenge (.queryAndLambda level queryChunks), .authenticate level,
    .absorb (.intro intro)]

/-- A boundary announcement precedes every OOD and query challenge. The final
boundary sends the residual instead of a further commitment. PoW is bound before
the grouped query, but its unground error is used by the theorem below. -/
def boundaryTrace (level queryChunks : Nat) (boundary : Digest32 ⊕ List Scalar24)
    (oods : List (Nat × Scalar24 × List Scalar24)) (dimension difficulty : Nat)
    (nonce : Scalar24) (intro : List Scalar24) : List Event :=
  [Event.absorb (match boundary with | .inl root => .root root | .inr ys => .residual ys)] ++
    oods.flatMap (fun o => oodTrace level o.1 dimension o.2.1 o.2.2) ++
    [.absorb (.nonce difficulty nonce)] ++ queryTrace level queryChunks intro

/-- A source-specific parser must enforce this boundary on *all* queried
histories, including rejecting continuations. `encode` reconstructs omitted
coefficients using ancestor challenges; the injectivity obligation is on
canonical protocol inputs, not arbitrary raw serialization call logs. -/
structure TranscriptInterface (Statement ProverMessage Challenge : Type*) where
  admissible : Statement → List ProverMessage → Prop
  depthCap : Nat
  depth_bound : ∀ s p, admissible s p → p.length ≤ depthCap
  classify : Statement → List ProverMessage → Turn
  encode : Statement → List (ProverMessage × Challenge) → ProverMessage → Coordinate
  paddedBlocks : Statement → List ProverMessage → Nat
  /-- Charge output expansion and encoding, separately from primitive queries. -/
  encodingCost : Statement → List ProverMessage → Nat

/-- Full-transcript inputs include every preceding verifier batch. Lists here
are reverse chronological, so the head is the latest prover turn. -/
structure FullInput (Statement ProverMessage Challenge : Type*) where
  statement : Statement
  ancestors : List (ProverMessage × Challenge)
  current : ProverMessage
  deriving DecidableEq

variable {S M C : Type*}

/-- Functional semantics of the global cache: repeated inputs necessarily reuse
the same answer. A lazy implementation need only materialize allocated prefixes. -/
def complete (oracle : FullInput S M C → C) (statement : S) : List M → List (M × C)
  | [] => []
  | m :: older =>
    let ancestors := complete oracle statement older
    (m, oracle ⟨statement, ancestors, m⟩) :: ancestors

 theorem complete_erases (oracle : FullInput S M C → C) (s : S) (p : List M) :
    (complete oracle s p).map Prod.fst = p := by
  induction p with
  | nil => rfl
  | cons m p ih => simp [complete, ih]

 theorem complete_length (oracle : FullInput S M C → C) (s : S) (p : List M) :
    (complete oracle s p).length = p.length := by
  have h := congrArg List.length (complete_erases oracle s p)
  simpa using h

 theorem full_input_injective (oracle : FullInput S M C → C)
    {s t : S} {p q : List M} {m n : M}
    (same : (FullInput.mk s (complete oracle s p) m) =
      FullInput.mk t (complete oracle t q) n) : s = t ∧ m :: p = n :: q := by
  refine ⟨congrArg FullInput.statement same, ?_⟩
  have hm := congrArg FullInput.current same
  have hp := congrArg (fun a : FullInput S M C => a.ancestors.map Prod.fst) same
  simp only [complete_erases] at hp
  change m = n at hm
  rw [hm, hp]

abbrev Cache (S M C : Type*) := (S × List M) → Option C

structure Allocation (S M C : Type*) where
  history : List (M × C)
  cache : Cache S M C
  fresh : Nat

/-- Ancestors are completed before looking up the current batch. All branches,
clones, and statements share this cache; a hit performs no oracle request. -/
def allocate [DecidableEq S] [DecidableEq M] (oracle : FullInput S M C → C)
    (s : S) : List M → Cache S M C → Allocation S M C
  | [], cache => ⟨[], cache, 0⟩
  | m :: p, cache =>
    let a := allocate oracle s p cache
    match a.cache (s, m :: p) with
    | some c => ⟨(m, c) :: a.history, a.cache, a.fresh⟩
    | none =>
      let c := oracle ⟨s, a.history, m⟩
      ⟨(m, c) :: a.history, Function.update a.cache (s, m :: p) (some c), a.fresh + 1⟩

def canonicalAnswer (oracle : FullInput S M C → C) (key : S × List M) : Option C :=
  match key.2 with
  | [] => none
  | m :: p => some (oracle ⟨key.1, complete oracle key.1 p, m⟩)

def CacheCorrect (oracle : FullInput S M C → C) (cache : Cache S M C) : Prop :=
  ∀ key c, cache key = some c → canonicalAnswer oracle key = some c

theorem empty_cache_correct (oracle : FullInput S M C → C) :
    CacheCorrect oracle (fun _ => none) := by
  intro key c h
  cases h

theorem allocate_correct [DecidableEq S] [DecidableEq M] (oracle : FullInput S M C → C)
    (s : S) (p : List M) (cache : Cache S M C) (correct : CacheCorrect oracle cache) :
    (allocate oracle s p cache).history = complete oracle s p ∧
      CacheCorrect oracle (allocate oracle s p cache).cache := by
  induction p generalizing cache with
  | nil => exact ⟨rfl, correct⟩
  | cons m p ih =>
    obtain ⟨hh, hc⟩ := ih cache correct
    simp only [allocate]
    split
    next c h =>
      have he := hc (s, m :: p) c h
      simp only [canonicalAnswer, Option.some.injEq] at he
      exact ⟨by simp [complete, hh, he], hc⟩
    next h =>
      constructor
      · simp [complete, hh]
      · intro key c he
        by_cases hk : key = (s, m :: p)
        · subst key
          simp only [Function.update_self, Option.some.injEq] at he
          simp [canonicalAnswer, hh, ← he]
        · exact hc key c (by simpa only [Function.update_of_ne hk] using he)

theorem allocate_fresh_le [DecidableEq S] [DecidableEq M] (oracle : FullInput S M C → C)
    (s : S) (p : List M) (cache : Cache S M C) :
    (allocate oracle s p cache).fresh ≤ p.length := by
  induction p with
  | nil => simp [allocate]
  | cons m p ih =>
    simp only [allocate]
    split <;> simp only [List.length_cons] <;> omega

/-- Every ancestor is allocated before its descendant, regardless of request
order. Prefixes are represented backwards, hence these are nonempty suffixes. -/
def ancestors : List M → List (List M)
  | [] => []
  | m :: p => ancestors p ++ [m :: p]

 theorem ancestors_length (p : List M) : (ancestors p).length = p.length := by
  induction p with
  | nil => rfl
  | cons m p ih => simp [ancestors, ih]

/-- Flattening deliberately overcounts shared ancestors. The final verification
is one additional request, and simulator requests belong in `requests`. -/
def allocationWork (requests : List (List M)) : Nat :=
  (requests.map fun p => (ancestors p).length).sum

 theorem allocation_cap (B K : Nat) (requests : List (List M)) (final : List M)
    (budget : requests.length ≤ K) (bounded : ∀ p ∈ requests, p.length ≤ B)
    (finalBound : final.length ≤ B) : allocationWork (requests ++ [final]) ≤ B * (K + 1) := by
  have sumBound : ∀ (rs : List (List M)), (∀ p ∈ rs, p.length ≤ B) →
      allocationWork rs ≤ rs.length * B := by
    intro rs hr
    induction rs with
    | nil => simp [allocationWork]
    | cons p ps ih =>
      have hp := hr p (by simp)
      have hi := ih (fun q h => hr q (by simp [h]))
      simp only [allocationWork, List.map_cons, List.sum_cons, ancestors_length] at *
      simp only [List.length_cons]
      nlinarith
  have hsum := sumBound requests bounded
  simp only [allocationWork, List.map_append, List.sum_append, List.map_cons,
    List.map_nil, List.sum_cons, List.sum_nil, Nat.add_zero, ancestors_length] at *
  nlinarith

/-- Serve arbitrary branches and statements through one cache. Invalid
coordinates belong to the independent nonprotocol table, not this routine. -/
def serve [DecidableEq S] [DecidableEq M] (oracle : FullInput S M C → C) :
    List (S × List M) → Cache S M C → Cache S M C × Nat
  | [], cache => (cache, 0)
  | key :: rest, cache =>
    let a := allocate oracle key.1 key.2 cache
    let b := serve oracle rest a.cache
    (b.1, a.fresh + b.2)

theorem serve_cost_le [DecidableEq S] [DecidableEq M] (oracle : FullInput S M C → C)
    (requests : List (S × List M)) (cache : Cache S M C) :
    (serve oracle requests cache).2 ≤ allocationWork (requests.map Prod.snd) := by
  induction requests generalizing cache with
  | nil => simp [serve, allocationWork]
  | cons key rest ih =>
    have ha := allocate_fresh_le oracle key.1 key.2 cache
    have hb := ih (allocate oracle key.1 key.2 cache).cache
    simpa only [serve, allocationWork, List.map_cons, List.sum_cons, ancestors_length]
      using Nat.add_le_add ha hb

theorem serve_cap [DecidableEq S] [DecidableEq M] (oracle : FullInput S M C → C)
    (B K : Nat) (requests : List (S × List M)) (final : S × List M)
    (cache : Cache S M C) (budget : requests.length ≤ K)
    (bounded : ∀ key ∈ requests, key.2.length ≤ B) (finalBound : final.2.length ≤ B) :
    (serve oracle (requests ++ [final]) cache).2 ≤ B * (K + 1) := by
  apply (serve_cost_le oracle _ cache).trans
  simp only [List.map_append, List.map_cons, List.map_nil]
  apply allocation_cap B K (requests.map Prod.snd) final.2
  · simpa using budget
  · intro p hp
    obtain ⟨key, hk, rfl⟩ := List.mem_map.mp hp
    exact bounded key hk
  · exact finalBound

section StoppedGame
variable [Fintype C] [Nonempty C]

/-- Uniform fresh *whole* vector; overlapping slices must not call this twice. -/
def average (f : C → ℚ) : ℚ := (∑ c, f c) / Fintype.card C

 theorem average_mono {f g : C → ℚ} (h : ∀ c, f c ≤ g c) : average f ≤ average g := by
  exact div_le_div_of_nonneg_right (Finset.sum_le_sum fun c _ => h c) (by positivity)

 theorem average_const (a : ℚ) : average (fun _ : C => a) = a := by
  have hn : (Fintype.card C : ℚ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  simp [average, hn]

omit [Nonempty C] in
 theorem average_add (f g : C → ℚ) :
    average (fun c => f c + g c) = average f + average g := by
  simp [average, Finset.sum_add_distrib, add_div]

omit [Nonempty C] in
/-- Exact finite lazy-sampling identity. A fresh oracle coordinate is uniform
even conditional on arbitrary information about every other coordinate. After
fixing an exposed causal history, `key` is fixed and this identity supplies the
fresh-vector distribution used by `risk`. Repeated coordinates instead reuse
their original table entry. -/
theorem fresh_coordinate {Key : Type*} [Fintype Key] [DecidableEq Key]
    (key : Key) (f : ({j : Key // j ≠ key} → C) → C → ℚ) :
    average (fun table : Key → C => f (fun j => table j) (table key)) =
      average (fun rest : {j : Key // j ≠ key} → C => average (f rest)) := by
  let e := Equiv.piSplitAt key (fun _ : Key => C)
  have hs :
      (∑ table : Key → C, f (fun j => table j) (table key)) =
        ∑ pair : C × ({j : Key // j ≠ key} → C), f pair.2 pair.1 := by
    exact Fintype.sum_equiv e _ _ (fun _ => rfl)
  have hc := Fintype.card_congr e
  unfold average
  rw [hs, hc, Fintype.card_prod, Fintype.sum_prod_type]
  rw [Finset.sum_comm]
  simp only [Nat.cast_mul, ← Finset.sum_div]
  ring

/-- Deterministic adversarial control between fresh allocations. State includes
its coins, complete exposed cache, statement, and every branch it has queried.
`active` permits adaptive stopping, but there is still a deterministic cap. -/
structure Machine (State Challenge : Type*) where
  active : State → Bool
  next : State → Challenge → State
  accepts : State → Bool
  escape : State → Challenge → Bool

variable {State : Type*}

/-- Actual finite experiment acceptance, including acceptance on early stop. -/
def win (G : Machine State C) : Nat → State → ℚ
  | 0, s => if G.accepts s then 1 else 0
  | n + 1, s => if G.active s then average (fun c => win G n (G.next s c))
      else if G.accepts s then 1 else 0

/-- Probability that at least one allocated vector escapes the sparse relation. -/
def risk (G : Machine State C) : Nat → State → ℚ
  | 0, _ => 0
  | n + 1, s => if G.active s then
      average (fun c => if G.escape s c then 1 else risk G n (G.next s c)) else 0

 theorem risk_nonneg (G : Machine State C) (n : Nat) (s : State) : 0 ≤ risk G n s := by
  induction n generalizing s with
  | zero => rfl
  | succ n ih =>
    simp only [risk]
    split
    · rw [← average_const (C := C) 0]
      apply average_mono
      intro c
      split
      · norm_num
      · exact ih _
    · rfl

 theorem win_le_one (G : Machine State C) (n : Nat) (s : State) : win G n s ≤ 1 := by
  induction n generalizing s with
  | zero => simp only [win]; split <;> norm_num
  | succ n ih =>
    simp only [win]
    split
    · rw [← average_const (C := C) 1]
      exact average_mono fun c => ih _
    · split <;> norm_num

/-- The RBR premise is local: nonescaping transitions preserve doom, and a
doomed stopped state cannot accept. No whole-FS soundness premise is assumed. -/
 theorem win_le_risk (G : Machine State C) (doomed : State → Prop)
    (terminal : ∀ s, doomed s → G.accepts s = false)
    (preserve : ∀ s c, doomed s → G.escape s c = false → doomed (G.next s c))
    (n : Nat) (s : State) (initial : doomed s) : win G n s ≤ risk G n s := by
  induction n generalizing s with
  | zero => simp [win, risk, terminal s initial]
  | succ n ih =>
    simp only [win, risk]
    split
    · apply average_mono
      intro c
      cases he : G.escape s c with
      | false => simpa [he] using ih _ (preserve s c initial he)
      | true => simpa [he] using win_le_one G n (G.next s c)
    · simp [terminal s initial]

/-- Uniform conditional sparsity must hold at *every* admissible exposed
history, including simulator requests and branches not finally submitted.
The same epsilon bounds whole grouped vectors, never individual query slots. -/
 theorem risk_bound (G : Machine State C) (epsilon : ℚ) (nonneg : 0 ≤ epsilon)
    (sparse : ∀ s, average (fun c => if G.escape s c then 1 else 0) ≤ epsilon)
    (n : Nat) (s : State) : risk G n s ≤ n * epsilon := by
  induction n generalizing s with
  | zero => simp [risk]
  | succ n ih =>
    simp only [risk]
    split
    · calc
        _ ≤ average (fun c => (if G.escape s c then 1 else 0) + n * epsilon) := by
          apply average_mono
          intro c
          split
          · have hn : (0 : ℚ) ≤ n * epsilon := mul_nonneg (by positivity) nonneg
            linarith
          · simpa using ih (G.next s c)
        _ = average (fun c => if G.escape s c then 1 else 0) + n * epsilon := by
          rw [average_add, average_const]
        _ ≤ epsilon + n * epsilon := by have h := sparse s; linarith
        _ = (n + 1 : Nat) * epsilon := by push_cast; ring
    · positivity

 theorem ordinary_soundness (G : Machine State C) (doomed : State → Prop)
    (terminal : ∀ s, doomed s → G.accepts s = false)
    (preserve : ∀ s c, doomed s → G.escape s c = false → doomed (G.next s c))
    (epsilon : ℚ) (nonneg : 0 ≤ epsilon)
    (sparse : ∀ s, average (fun c => if G.escape s c then 1 else 0) ≤ epsilon)
    (B K : Nat) (s : State) (initial : doomed s) :
    win G (B * (K + 1)) s ≤ min 1 ((B * (K + 1) : Nat) * epsilon) := by
  exact le_min (win_le_one G _ s)
    ((win_le_risk G doomed terminal preserve _ s initial).trans (risk_bound G epsilon nonneg sparse _ s))

end StoppedGame

/-- Finite real/ideal oracle-view experiments. `View` includes everything the
resource-bounded distinguisher observes, not an adversarial acceptance flag.
The concrete mode/simulator instantiation is a separate cryptographic proof.
Q counts all primitive evaluations, not coordinate requests K or allocations N. -/
structure ModeGame (Coins View : Type*) where
  real : Coins → View
  ideal : Coins → View
  primitiveQueries : Nat

def distinguishProbability {Coins View : Type*} [Fintype Coins]
    (experiment : Coins → View) (distinguisher : View → Bool) : ℚ := by
  classical
  exact Soundness.uniformProb (Finset.univ.filter fun r => distinguisher (experiment r) = true)

theorem distinguish_average {Coins View : Type*} {old : Fintype Coins}
    (new : Fintype Coins) (experiment : Coins → View) (D : View → Bool) :
    @distinguishProbability Coins View old experiment D =
      @average Coins new (fun coin => if D (experiment coin) = true then 1 else 0) := by
  classical
  cases Subsingleton.elim old new
  simp only [distinguishProbability, Soundness.uniformProb, average, Finset.sum_boole]

/-- A standard distinguishing assumption, universally quantified over the
permitted view distinguishers; it contains no PCS relation or FS acceptance. -/
def ModeSecure {Coins View : Type*} [Fintype Coins] (G : ModeGame Coins View)
    (allowed : (View → Bool) → Prop) (loss : ℚ) : Prop :=
  ∀ D, allowed D →
    |distinguishProbability G.real D - distinguishProbability G.ideal D| ≤ loss

theorem mode_transfer {Coins View : Type*} [Fintype Coins] (G : ModeGame Coins View)
    (allowed : (View → Bool) → Prop) (loss : ℚ) (secure : ModeSecure G allowed loss)
    (D : View → Bool) (permitted : allowed D) (bound : ℚ)
    (ideal : distinguishProbability G.ideal D ≤ bound) :
    distinguishProbability G.real D ≤ bound + loss := by
  have h := (abs_le.mp (secure D permitted)).2
  linarith

/-- Sharp birthday subevent budget, not the whole-view duplex loss. -/
def compressionBirthdayLoss (Q : Nat) : ℚ := min 1 ((Q.choose 2 : ℚ) / (2 ^ 256 : ℚ))

/-- Actual adaptive whole-view duplex budget: output collisions, public late
links, and guesses of unrevealed construction states share one Counts Q cap. -/
def duplexModeLoss (Q : Nat) : ℚ :=
  min 1 ((2 * (Q.choose 2 : ℚ) + (Q : ℚ) * Q) / (2 ^ 256 : ℚ))

/-! Remaining instantiation obligations (not axioms):

* Refine #552's byte framing, canonical root halves, coefficient reconstruction,
  consumed counts, 24-byte field codec, and maximal squeeze runs to this interface.
  Prove injective parsing on admissible histories (modulo explicit statement
  digest-binding loss); route all other coordinates to an independent table.
* Refine the executable `allocate` cache and completed-history encoding to the
  protocol parser. `allocate_correct`, `full_input_injective`, and
  `fresh_coordinate` justify fresh allocations, not rereading unused/padding
  bytes as new challenges. Charge padded vector size, root-to-terminal mode calls,
  encoding size, and simulator runtime.
* Instantiate `Machine` with the causal PCS adversary and prove local `preserve`,
  `terminal`, and whole-batch `sparse` using the parent's grouped RBR theorem.
  For variable-length batches, use projections of uniformly sampled capped
  block vectors and prove their codec distribution; uniform sampling from a sum
  of differently sized batch types would not supply this premise.
  A syntactic parser must include rejecting histories; acceptance cannot define
  admissibility. Include simulator coordinate requests in K and final verification
  in the extra one. Adaptive stopping uses this deterministic cap.
* Discharge Merkle query-table collision/preimage games and auxiliary binding
  losses. Supply the real/ideal mode view games and DMV hypotheses, or state the
  resulting primitive assumption. No grinding amplification, runtime-source
  correspondence, knowledge extraction, or numerical 128-bit claim follows here.
-/

end Whir.FiatShamirGame
