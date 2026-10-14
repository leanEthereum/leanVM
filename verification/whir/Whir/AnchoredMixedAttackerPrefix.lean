import Whir.AnchoredSourceGroups
import Whir.PublicCompressionCouplingMixed
import Whir.PCSBCSMerkleRootCache
import Whir.PCSBCSMixedOrdinaryMerkle

/-! Mixed attacker-prefix grouping. The ordinary summand exposes its full
compression reply, including repeated requests. The construction summand is
literal bounded raw input. At first contact with any point block, preparation
uses only the strict completed mixed history; it freezes the decoded header's
public ordinary Merkle prefix before the whole-run answer is allocated.

The final specialization of the existing public-simulator lowering preserves
its entire View. Its public ordinary log contains completed fallback draws.
AnchoredMixedAttackerPrefixSource proves that omitted cache hits preserve the
frozen root table when the SAME actual ordinary trace's OutputCollision alarm
is quiet. No native body/knowledge or current-607 correspondence is asserted. -/
namespace Whir.AnchoredMixedAttackerPrefix
open Concrete FiatShamirGame DuplexModeGame ParameterBounds TypedOracleCompiler
open RawOracleCoupling AnchoredByteStreamCausal AnchoredByteStreamGroups

abbrev Key := PublicCompressionCouplingMixed.Key
abbrev History (Q : Nat) := List (Key Q × Digest32)

noncomputable def recognize (Q dimension : Nat) (iv : Digest32)
    (accept : FramedHistory → Bool) : Key Q →
    Option (Sigma (fun _ : Packet Q dimension iv accept =>
      Fin (AnchoredFiatShamirSecurityCodec.blockCount dimension)))
  | .inl _ => none
  | .inr raw => AnchoredByteStreamCausal.recognize Q dimension iv accept raw

noncomputable def partition (Q dimension : Nat) (iv : Digest32)
    (accept : FramedHistory → Bool) : Partition (Key Q)
      (Packet Q dimension iv accept)
      (fun _ => Fin (AnchoredFiatShamirSecurityCodec.blockCount dimension)) where
  encode := fun c => .inr (AnchoredByteStreamCausal.encode Q dimension iv accept c)
  recognize := recognize Q dimension iv accept
  recognize_encode := fun c => AnchoredByteStreamCausal.recognize_encode Q dimension iv accept c
  encode_recognize := by
    intro raw c found
    cases raw with
    | inl input => simp [recognize] at found
    | inr raw =>
      exact congrArg Sum.inr
        (AnchoredByteStreamCausal.encode_recognize Q dimension iv accept raw c found)

/-- Newest-first, actual completed ordinary replies only. In particular no raw
construction answer can masquerade as a compression preimage. -/
def ordinaryPrefix (past : History Q) : PublicMerkleLog.PublicLog :=
  past.filterMap fun (key,answer) => match key with
    | .inl input => if DuplexFraming.tag input = 0 then some (input,answer) else none
    | .inr _ => none

@[simp] theorem ordinaryPrefix_raw (raw : RawKey Q) (answer : Digest32) (past : History Q) :
    ordinaryPrefix ((.inr raw,answer)::past) = ordinaryPrefix past := rfl

@[simp] theorem ordinaryPrefix_ordinary (input : DuplexFraming.Node) (answer : Digest32)
    (past : History Q) (ordinary : DuplexFraming.tag input = 0) :
    ordinaryPrefix ((.inl input,answer)::past) = (input,answer)::ordinaryPrefix past := by
  simp [ordinaryPrefix,ordinary]

namespace Grouped
open Concrete Protocol CausalGame ParameterBounds CommitmentAnchor FiatShamirGame
open TypedOracleCompiler RawOracleCoupling RawOracleCoupling.Concrete
open AnchoredFiatShamirSecurityCodec AnchoredByteStreamGroups
open DuplexFraming DuplexModeGame

noncomputable local instance (P : Prop) : Decidable P := Classical.propDecidable P
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

variable {p : Profile} {Q : Nat} {iv : Digest32} {accept : FramedHistory → Bool}

abbrev PointPacket (p : Profile) (Q : Nat) (iv : Digest32) (accept : FramedHistory → Bool) :=
  Packet Q (config p).logN iv accept
abbrev Records := AnchoredFiatShamirSecurity.Cache p (PointPacket p Q iv accept)
abbrev Group := (partition Q (config p).logN iv accept).Key
abbrev Reply := (partition Q (config p).logN iv accept).Answer (D := Digest32)
abbrev GroupCache := TypedFiatShamirGame.Cache (Group (p := p) (Q := Q) (iv := iv) (accept := accept))
  (Reply (p := p) (Q := Q) (iv := iv) (accept := accept))

structure Policy (p : Profile) (Q : Nat) (iv : Digest32) (accept : FramedHistory → Bool) where
  prepare : History Q → PointPacket p Q iv accept → AnchoredFiatShamirSecurity.PreAnchor p
  advertise : History Q → PointPacket p Q iv accept → Joint (config p).logN → E

noncomputable def step (policy : Policy p Q iv accept) (past : History Q)
    (records : Records (p := p) (Q := Q) (iv := iv) (accept := accept))
    (packet : PointPacket p Q iv accept) (blocks : Blocks (config p).logN) :=
  AnchoredFiatShamirSecurity.advance
    { choose := fun _ => packet
      prepare := fun _ _ => policy.prepare past packet
      advertise := fun _ _ answer => policy.advertise past packet answer }
    records (vectorParts (config p).logN blocks)

theorem repeated_original (policy : Policy p Q iv accept) (past : History Q)
    (records : Records (p := p) (Q := Q) (iv := iv) (accept := accept))
    (packet : PointPacket p Q iv accept) (e : AnchoredFiatShamirSecurity.Entry p _)
    (hit : AnchoredFiatShamirSecurity.lookup records packet = some e)
    (blocks : Blocks (config p).logN) : step policy past records packet blocks = e :: records := by
  exact AnchoredFiatShamirSecurity.repeated_key _ records e hit _

noncomputable def compile (policy : Policy p Q iv accept) {R : Type} : {n : Nat} →
    Sampling (Key Q) (fun _ => Digest32) R n → History Q →
    Records (p := p) (Q := Q) (iv := iv) (accept := accept) →
    Sampling (Group (p := p) (Q := Q) (iv := iv) (accept := accept))
      (Reply (p := p) (Q := Q) (iv := iv) (accept := accept))
      (R × Records (p := p) (Q := Q) (iv := iv) (accept := accept)) n
  | _, .ret result, _, records => .ret (result,records)
  | _, .draw raw next, past, records =>
    match h : recognize Q (config p).logN iv accept raw with
    | some c => .draw (.inl c.1) (fun blocks =>
        compile policy (next (blocks c.2)) ((raw,blocks c.2)::past)
          (step policy past records c.1 blocks))
    | none => .draw (.inr ⟨raw,h⟩) (fun answer =>
        compile policy (next answer) ((raw,answer)::past) records)

private def Seen (records : Records (p := p) (Q := Q) (iv := iv) (accept := accept))
    (cache : GroupCache (p := p) (Q := Q) (iv := iv) (accept := accept)) : Prop :=
  ∀ packet blocks, cache (.inl packet) = some blocks →
    ∃ e, AnchoredFiatShamirSecurity.lookup records packet = some e

private theorem step_clean (policy : Policy p Q iv accept) (past : History Q)
    (records : Records (p := p) (Q := Q) (iv := iv) (accept := accept))
    (clean : ¬ AnchoredFiatShamirSecurity.Dirty records) (packet : PointPacket p Q iv accept)
    (blocks : Blocks (config p).logN)
    (separated : ¬ Ambiguous p (policy.prepare past packet).lanes
      (policy.prepare past packet).root (point (config p).logN blocks)) :
    ¬ AnchoredFiatShamirSecurity.Dirty (step policy past records packet blocks) := by
  classical
  unfold step AnchoredFiatShamirSecurity.advance
  dsimp only
  cases hit : AnchoredFiatShamirSecurity.lookup records packet with
  | none =>
    simp only [AnchoredFiatShamirSecurity.Dirty, List.mem_cons, exists_eq_or_imp]
    exact not_or.mpr ⟨separated,clean⟩
  | some e =>
    have member : e ∈ records := List.mem_of_find?_eq_some hit
    simp only [AnchoredFiatShamirSecurity.Dirty, List.mem_cons, exists_eq_or_imp]
    exact not_or.mpr ⟨fun bad => clean ⟨e,member,bad⟩,clean⟩

private theorem step_seen (policy : Policy p Q iv accept) (past : History Q)
    (records : Records (p := p) (Q := Q) (iv := iv) (accept := accept))
    (cache : GroupCache (p := p) (Q := Q) (iv := iv) (accept := accept)) (seen : Seen records cache)
    (packet : PointPacket p Q iv accept) (blocks : Blocks (config p).logN) :
    Seen (step policy past records packet blocks) (TypedFiatShamirGame.put cache (.inl packet) blocks) := by
  classical
  intro wanted value present
  unfold step AnchoredFiatShamirSecurity.advance
  dsimp only
  cases hit : AnchoredFiatShamirSecurity.lookup records packet with
  | none =>
    by_cases same : wanted = packet
    · subst wanted
      refine ⟨⟨packet,
        ⟨(policy.prepare past packet).lanes,(policy.prepare past packet).root,
          (vectorParts (config p).logN blocks).1,
          policy.advertise past packet (vectorParts (config p).logN blocks),
          (policy.prepare past packet).occupied⟩,
        (vectorParts (config p).logN blocks).2⟩,?_⟩
      simp [AnchoredFiatShamirSecurity.lookup]
    · have old : cache (.inl wanted) = some value := by
        simpa [TypedFiatShamirGame.put, same] using present
      obtain ⟨e,found⟩ := seen wanted value old
      exact ⟨e,by simpa [AnchoredFiatShamirSecurity.lookup, Ne.symm same] using found⟩
  | some e =>
    by_cases same : wanted = packet
    · subst wanted
      refine ⟨e,?_⟩
      have keyeq : e.key = packet := by
        have member := List.find?_some hit
        simpa using member
      simp [AnchoredFiatShamirSecurity.lookup, keyeq]
    · have old : cache (.inl wanted) = some value := by
        simpa [TypedFiatShamirGame.put, same] using present
      obtain ⟨other,found⟩ := seen wanted value old
      have keyeq : e.key = packet := by
        have member := List.find?_some hit
        simpa using member
      exact ⟨other,by simpa [AnchoredFiatShamirSecurity.lookup, keyeq, Ne.symm same] using found⟩

private theorem ambiguity_average (pre : AnchoredFiatShamirSecurity.PreAnchor p) :
    average (fun blocks : Blocks (config p).logN =>
      if Ambiguous p pre.lanes pre.root (point (config p).logN blocks) then (1 : ℚ) else 0) ≤
      (1 : ℚ)/2^124 := by
  rw [vector_point_average (config p).logN
    (fun pt => if Ambiguous p pre.lanes pre.root pt then (1 : ℚ) else 0)]
  have h := ambiguity_probability_numeric p pre.lanes pre.root pre.occupied.2
  simpa only [average, Soundness.uniformProb, Finset.card_filter, Nat.cast_sum,
    Nat.cast_ite, Nat.cast_one, Nat.cast_zero] using h

private theorem memo_bound (policy : Policy p Q iv accept) {R : Type} {n : Nat}
    (source : Sampling (Key Q) (fun _ => Digest32) R n) (past : History Q)
    (records : Records (p := p) (Q := Q) (iv := iv) (accept := accept))
    (cache : GroupCache (p := p) (Q := Q) (iv := iv) (accept := accept))
    (seen : Seen records cache) (clean : ¬ AnchoredFiatShamirSecurity.Dirty records) :
    Sampling.expectation (fun result =>
      if AnchoredFiatShamirSecurity.Dirty result.1.2 then (1 : ℚ) else 0)
      (RawOracleCoupling.memo (compile policy source past records) cache) ≤ (n : ℚ)/2^124 := by
  classical
  induction source generalizing past records cache with
  | ret result =>
    simp only [compile, RawOracleCoupling.memo, Sampling.expectation, clean, ↓reduceIte]
    positivity
  | @draw n raw next ih =>
    unfold compile
    split
    · rename_i c recognized
      cases cached : cache (.inl c.1) with
      | some blocks =>
        obtain ⟨e,hit⟩ := seen c.1 blocks cached
        have repeated := repeated_original policy past records c.1 e hit blocks
        have nextClean : ¬ AnchoredFiatShamirSecurity.Dirty (step policy past records c.1 blocks) := by
          rw [repeated]
          have member : e ∈ records := List.mem_of_find?_eq_some hit
          simp only [AnchoredFiatShamirSecurity.Dirty, List.mem_cons, exists_eq_or_imp]
          exact not_or.mpr ⟨fun bad => clean ⟨e,member,bad⟩,clean⟩
        have nextSeen : Seen (step policy past records c.1 blocks) cache := by
          have s := step_seen policy past records cache seen c.1 blocks
          have putSame : TypedFiatShamirGame.put cache (.inl c.1) blocks = cache := by
            funext k
            by_cases same : k = .inl c.1
            · subst k; simp [cached]
            · simp [TypedFiatShamirGame.put_other _ _ _ _ same]
          simpa [putSame] using s
        simp only [RawOracleCoupling.memo, cached, Sampling.expectation_pad]
        exact (ih (blocks c.2) _ _ _ nextSeen nextClean).trans
          (div_le_div_of_nonneg_right (by exact_mod_cast Nat.le_succ n) (by positivity))
      | none =>
        simp only [RawOracleCoupling.memo, cached, Sampling.expectation]
        have fiber (blocks : Blocks (config p).logN) :
            Sampling.expectation (fun result =>
              if AnchoredFiatShamirSecurity.Dirty result.1.2 then (1 : ℚ) else 0)
              (RawOracleCoupling.memo
                (compile policy (next (blocks c.2)) ((raw,blocks c.2)::past)
                  (step policy past records c.1 blocks))
                (TypedFiatShamirGame.put cache (.inl c.1) blocks)) ≤
            (if Ambiguous p (policy.prepare past c.1).lanes (policy.prepare past c.1).root
              (point (config p).logN blocks) then 1 else 0) + (n : ℚ)/2^124 := by
          by_cases bad : Ambiguous p (policy.prepare past c.1).lanes (policy.prepare past c.1).root
              (point (config p).logN blocks)
          · have one := Sampling.expectation_le_one
              (fun result : (R × Records (p := p) (Q := Q) (iv := iv) (accept := accept)) ×
                GroupCache (p := p) (Q := Q) (iv := iv) (accept := accept) =>
                if AnchoredFiatShamirSecurity.Dirty result.1.2 then (1 : ℚ) else 0)
              (fun result => by split <;> norm_num)
              (RawOracleCoupling.memo
                (compile policy (next (blocks c.2)) ((raw,blocks c.2)::past)
                  (step policy past records c.1 blocks))
                (TypedFiatShamirGame.put cache (.inl c.1) blocks))
            simpa [bad] using one.trans (le_add_of_nonneg_right (by positivity : 0 ≤ (n : ℚ)/2^124))
          · simpa [bad] using ih (blocks c.2) _ _ _
              (step_seen policy past records cache seen c.1 blocks)
              (step_clean policy past records clean c.1 blocks bad)
        have averaged := average_mono fiber
        have badBound := ambiguity_average (policy.prepare past c.1)
        have bound :
            average (fun blocks : Blocks (config p).logN =>
              Sampling.expectation (fun result =>
                if AnchoredFiatShamirSecurity.Dirty result.1.2 then (1 : ℚ) else 0)
                (RawOracleCoupling.memo
                  (compile policy (next (blocks c.2)) ((raw,blocks c.2)::past)
                    (step policy past records c.1 blocks))
                  (TypedFiatShamirGame.put cache (.inl c.1) blocks))) ≤
              (1 : ℚ)/2^124 + (n : ℚ)/2^124 := averaged.trans (by
          rw [average_add, average_const]
          exact add_le_add badBound le_rfl)
        have arithmetic : (1 : ℚ)/2^124 + (n : ℚ)/2^124 =
            ((n+1 : Nat) : ℚ)/2^124 := by push_cast; ring
        refine le_trans (le_of_eq ?_) (bound.trans_eq arithmetic)
        refine @RawOracleCoupling.average_equiv
          (Reply (p := p) (Q := Q) (iv := iv) (accept := accept) (.inl c.1))
          (Blocks (config p).logN) ?_ ?_ (Equiv.refl (Blocks (config p).logN))
          (fun blocks : Blocks (config p).logN =>
            Sampling.expectation (fun result =>
              if AnchoredFiatShamirSecurity.Dirty result.1.2 then (1 : ℚ) else 0)
              (RawOracleCoupling.memo
                (compile policy (next (blocks c.2)) ((raw,blocks c.2)::past)
                  (step policy past records c.1 blocks))
                (TypedFiatShamirGame.put cache (.inl c.1) blocks)))
    · rename_i unrecognized
      have updatedSeen (answer : Digest32) :
          Seen records (TypedFiatShamirGame.put cache (.inr ⟨raw,unrecognized⟩) answer) := by
        intro packet blocks present
        apply seen packet blocks
        simpa [TypedFiatShamirGame.put] using present
      cases cached : cache (.inr ⟨raw,unrecognized⟩) with
      | some answer =>
        simp only [RawOracleCoupling.memo, cached, Sampling.expectation_pad]
        exact (ih answer _ _ _ seen clean).trans
          (div_le_div_of_nonneg_right (by exact_mod_cast Nat.le_succ n) (by positivity))
      | none =>
        simp only [RawOracleCoupling.memo, cached, Sampling.expectation]
        apply (average_mono (fun answer => ih answer _ _ _ (updatedSeen answer) clean)).trans
        rw [average_const]
        exact div_le_div_of_nonneg_right (by exact_mod_cast Nat.le_succ n) (by positivity)

/-- Genuine adaptive source-key preparation. Roots depend on the completed raw
history, including every fourth word actually queried. First contact may be ANY
point block; the whole run is memoized and repeats preserve the same point.
No fresh-source-key assumption occurs in this theorem. -/
theorem causal_prepared_ambiguity {R : Type} {n : Nat} (policy : Policy p Q iv accept)
    (source : Sampling (Key Q) (fun _ => Digest32) R n) :
    Sampling.expectation (fun result =>
      if AnchoredFiatShamirSecurity.Dirty result.1.2 then (1 : ℚ) else 0)
      (RawOracleCoupling.memo (compile policy source [] []) (fun _ => none)) ≤ (n : ℚ)/2^124 :=
  memo_bound policy source [] [] (fun _ => none)
    (by intro packet blocks present; contradiction)
    (by simp [AnchoredFiatShamirSecurity.Dirty])

theorem profile_blocks : ∀ p : Profile, 0 < blockCount (config p).logN := by
  decide +kernel

noncomputable def execution (policy : Policy p Q iv accept) {R : Type} {n : Nat}
    (source : Sampling (Key Q) (fun _ => Digest32) R n) (table : Key Q → Digest32) :=
  Sampling.eval ((partition Q (config p).logN iv accept).split table)
    (RawOracleCoupling.memo (compile policy source [] []) (fun _ => none))

private theorem compile_result {R : Type} {n : Nat} (policy : Policy p Q iv accept)
    (source : Sampling (Key Q) (fun _ => Digest32) R n) (past : History Q)
    (records : Records (p := p) (Q := Q) (iv := iv) (accept := accept))
    (table : Key Q → Digest32) :
    (Sampling.eval ((partition Q (config p).logN iv accept).split table)
      (compile policy source past records)).1 = Sampling.eval table source := by
  induction source generalizing past records with
  | ret result => rfl
  | draw raw next ih =>
    unfold compile
    split
    · rename_i c recognized
      simp only [Sampling.eval, Partition.split, ih]
      change Sampling.eval table
        (next (table ((partition Q (config p).logN iv accept).encode c))) = _
      rw [(partition Q (config p).logN iv accept).encode_recognize raw c recognized]
    · simp only [Sampling.eval, Partition.split, ih]

/-- The compiler changes no raw reply or continuation. Its extra state consists
only of the immutable prepared records and the memoized complete point runs. -/
theorem execution_result {R : Type} {n : Nat} (policy : Policy p Q iv accept)
    (source : Sampling (Key Q) (fun _ => Digest32) R n) (table : Key Q → Digest32) :
    (execution policy source table).1.1 = Sampling.eval table source := by
  unfold execution
  rw [RawOracleCoupling.memo_eval_first, RawOracleCoupling.overlay_empty]
  rw [compile_result]

/-- Joint coupling includes the actual source result, immutable records and
private grouped cache. No part of any public raw answer is erased. -/
theorem prepared_full_distribution {R : Type} {n : Nat} (policy : Policy p Q iv accept)
    (source : Sampling (Key Q) (fun _ => Digest32) R n)
    (payoff : (R × Records (p := p) (Q := Q) (iv := iv) (accept := accept)) ×
      GroupCache (p := p) (Q := Q) (iv := iv) (accept := accept) → ℚ) :
    average (fun table : Key Q → Digest32 => payoff (execution policy source table)) =
      Sampling.expectation payoff
        (RawOracleCoupling.memo (compile policy source [] []) (fun _ => none)) := by
  classical
  let _ := packetFintype Q (config p).logN iv accept (profile_blocks p)
  have h := RawOracleCoupling.average_equiv
    ((partition Q (config p).logN iv accept).tableEquiv (D := Digest32))
    (fun table => payoff (Sampling.eval table
      (RawOracleCoupling.memo (compile policy source [] []) (fun _ => none))))
  rw [show average (fun table : Key Q → Digest32 => payoff (execution policy source table)) =
    average (fun table => payoff (Sampling.eval table
      (RawOracleCoupling.memo (compile policy source [] []) (fun _ => none)))) from h]
  exact RawOracleCoupling.table_eq_memo_full _ (fun _ => none) payoff

theorem prepared_raw_table_ambiguity {R : Type} {n : Nat} (policy : Policy p Q iv accept)
    (source : Sampling (Key Q) (fun _ => Digest32) R n) :
    Soundness.uniformProb (Finset.univ.filter fun table : Key Q → Digest32 =>
      AnchoredFiatShamirSecurity.Dirty (execution policy source table).1.2) ≤ (n : ℚ)/2^124 := by
  classical
  have h := prepared_full_distribution policy source
    (fun result => if AnchoredFiatShamirSecurity.Dirty result.1.2 then (1 : ℚ) else 0)
  have bound := causal_prepared_ambiguity policy source
  rw [← h] at bound
  simpa only [average, Soundness.uniformProb, Finset.card_filter, Nat.cast_sum,
    Nat.cast_ite, Nat.cast_one, Nat.cast_zero] using bound

/-- Count actual construction-summand requests; ordinary draws cost no raw
request here, and repetitions still cost one request. -/
def rawRequests (table : Key Q → Digest32) : {n : Nat} →
    Sampling (Key Q) (fun _ => Digest32) R n → Nat
  | _, .ret _ => 0
  | _, .draw key next =>
    (match key with | .inl _ => 0 | .inr _ => 1) +
      rawRequests table (next (table key))

theorem rawRequests_le (table : Key Q → Digest32)
    (source : Sampling (Key Q) (fun _ => Digest32) R n) :
    rawRequests table source ≤ n := by
  induction source with
  | ret => simp [rawRequests]
  | draw key next ih =>
    have bound := ih (table key)
    cases key <;> simp only [rawRequests] <;> omega

theorem step_length (policy : Policy p Q iv accept) (past : History Q)
    (records : Records (p := p) (Q := Q) (iv := iv) (accept := accept))
    (packet : PointPacket p Q iv accept) (blocks : Blocks (config p).logN) :
    (step policy past records packet blocks).length = records.length+1 := by
  unfold step AnchoredFiatShamirSecurity.advance
  dsimp only
  split <;> rfl

theorem compile_records_length (policy : Policy p Q iv accept)
    (source : Sampling (Key Q) (fun _ => Digest32) R n) (past : History Q)
    (records : Records (p := p) (Q := Q) (iv := iv) (accept := accept))
    (table : Key Q → Digest32) :
    (Sampling.eval ((partition Q (config p).logN iv accept).split table)
      (compile policy source past records)).2.length ≤
      records.length + rawRequests table source := by
  induction source generalizing past records with
  | ret result => simp [compile,Sampling.eval,rawRequests]
  | draw raw next ih =>
    unfold compile
    split
    · rename_i c recognized
      have same := (partition Q (config p).logN iv accept).encode_recognize raw c recognized
      simp only [Sampling.eval,Partition.split]
      have bound := ih (table ((partition Q (config p).logN iv accept).encode c))
        ((raw,table ((partition Q (config p).logN iv accept).encode c))::past)
        (step policy past records c.1
          (fun i => table ((partition Q (config p).logN iv accept).encode ⟨c.1,i⟩)))
      rw [same,step_length] at bound
      cases raw with
      | inl input => simp [recognize] at recognized
      | inr raw => simpa only [same,rawRequests,Nat.add_assoc] using bound
    · rename_i unrecognized
      simp only [Sampling.eval,Partition.split]
      have bound := ih (table raw) ((raw,table raw)::past) records
      cases raw <;> simp only [rawRequests] <;> omega

/-- One allocation per distinct packet, whereas the records list includes
repeated observations of the original immutable entry. -/
noncomputable def allocations
    (records : Records (p := p) (Q := Q) (iv := iv) (accept := accept)) : Nat := by
  classical
  exact (records.map (fun e => e.key)).toFinset.card

theorem allocation_budget (policy : Policy p Q iv accept)
    (source : Sampling (Key Q) (fun _ => Digest32) R n) (table : Key Q → Digest32) :
    allocations (execution policy source table).1.2 ≤ rawRequests table source ∧
      rawRequests table source ≤ n := by
  classical
  refine ⟨?_,rawRequests_le table source⟩
  unfold execution
  rw [RawOracleCoupling.memo_eval_first,RawOracleCoupling.overlay_empty]
  have lengthBound := compile_records_length policy source [] [] table
  simp only [List.length_nil,zero_add] at lengthBound
  exact ((List.toFinset_card_le _).trans_eq (List.length_map ..)).trans lengthBound

theorem repeated_allocation (policy : Policy p Q iv accept) (past : History Q)
    (records : Records (p := p) (Q := Q) (iv := iv) (accept := accept))
    (packet : PointPacket p Q iv accept) (e : AnchoredFiatShamirSecurity.Entry p _)
    (hit : AnchoredFiatShamirSecurity.lookup records packet = some e)
    (blocks : Blocks (config p).logN) :
    allocations (step policy past records packet blocks) = allocations records := by
  classical
  rw [repeated_original policy past records packet e hit blocks]
  have member : e.key ∈ (records.map (fun e => e.key)).toFinset :=
    List.mem_toFinset.mpr (List.mem_map.mpr ⟨e,List.mem_of_find?_eq_some hit,rfl⟩)
  simp only [allocations,List.map_cons,List.toFinset_cons]
  rw [Finset.insert_eq_of_mem member]


end Grouped

open AnchoredHeaderRoots AnchoredFiatShamirSecurityCodec

noncomputable local instance (P : Prop) : Decidable P := Classical.propDecidable P

/-- Full leaf-image width is distinct from occupied lanes. -/
def rootShape (header : Header) : PCSBCSMerkleRootCache.Shape :=
  ⟨header.shape.logN-header.shape.logBatch+header.shape.logRate,
    2^header.shape.logBatch,header.shape.lanes⟩

structure PrefixState where
  log : PublicMerkleLog.PublicLog := []
  roots : PCSBCSMerkleRootCache.Registry := ∅

/-- Recording an ordinary answer is the only operation that extends the
ordinary log. Raw requests merely freeze a decoded root/shape address. -/
noncomputable def completed (registry : Public) (state : PrefixState)
    (key : Key Q) (answer : Digest32) : PrefixState :=
  match key with
  | .inl input =>
    if DuplexFraming.tag input = 0 then {state with log := (input,answer)::state.log}
    else state
  | .inr raw =>
    match rawHeader registry raw with
    | none => state
    | some header => {state with roots :=
        PCSBCSMerkleRootCache.register state.roots state.log header.root (rootShape header)}

/-- Tail-first traversal replays the newest-first public history in chronology.
At a raw event, `completed` does not inspect that event's answer. -/
noncomputable def replay (registry : Public) : History Q → PrefixState
  | [] => {}
  | (key,answer)::past => completed registry (replay registry past) key answer

theorem replay_log (registry : Public) (past : History Q) :
    (replay registry past).log = ordinaryPrefix past := by
  induction past with
  | nil => rfl
  | cons item past ih =>
    rcases item with ⟨key,answer⟩
    cases key with
    | inl input =>
      simp only [replay,completed,ordinaryPrefix,List.filterMap_cons]
      split <;> simp_all [ordinaryPrefix]
    | inr raw =>
      simp only [replay,completed,ordinaryPrefix,List.filterMap_cons]
      cases rawHeader registry raw <;> exact ih

theorem completed_preserves (registry : Public) (state : PrefixState)
    (key : Key Q) (answer : Digest32) (header : Header)
    (frozen : PCSBCSMerkleRootCache.Frozen)
    (known : state.roots[PCSBCSMerkleRootCache.cacheKey header.root (rootShape header)]? =
      some frozen) :
    (completed registry state key answer).roots[
      PCSBCSMerkleRootCache.cacheKey header.root (rootShape header)]? = some frozen := by
  cases key with
  | inl input => simp only [completed]; split <;> exact known
  | inr raw =>
    simp only [completed]
    cases rawHeader registry raw with
    | none => exact known
    | some other => exact PCSBCSMerkleRootCache.register_preserves _ _ _ _ _ _ _ known

theorem replay_wellFormed (registry : Public) (past : History Q) :
    PCSBCSMerkleRootCache.WellFormed (replay registry past).roots := by
  induction past with
  | nil => exact PCSBCSMerkleRootCache.empty_wellFormed
  | cons item past ih =>
    rcases item with ⟨key,answer⟩
    cases key with
    | inl input => simp only [replay,completed]; split <;> exact ih
    | inr raw =>
      simp only [replay,completed]
      cases rawHeader registry raw with
      | none => exact ih
      | some header => exact PCSBCSMerkleRootCache.register_wellFormed _ _ _ _ ih

/-- The current reply is absent: registration takes the earlier replay log and
the literal header only. No compression oracle is an argument. -/
noncomputable def beforeHeader (registry : Public) (past : History Q) (header : Header) :
    PCSBCSMerkleRootCache.Registry :=
  PCSBCSMerkleRootCache.register (replay registry past).roots (replay registry past).log
    header.root (rootShape header)

noncomputable def frozenHeader (registry : Public) (past : History Q) (header : Header) :
    PCSBCSMerkleRootCache.Frozen :=
  (beforeHeader registry past header)[
    PCSBCSMerkleRootCache.cacheKey header.root (rootShape header)]?.getD
      (PCSBCSMerkleRootCache.freeze (ordinaryPrefix past) header.root (rootShape header))

theorem frozenHeader_known (registry : Public) (past : History Q) (header : Header) :
    (beforeHeader registry past header)[
      PCSBCSMerkleRootCache.cacheKey header.root (rootShape header)]? =
      some (frozenHeader registry past header) := by
  unfold beforeHeader frozenHeader
  cases known : (replay registry past).roots[
      PCSBCSMerkleRootCache.cacheKey header.root (rootShape header)]? with
  | none => simp [beforeHeader,PCSBCSMerkleRootCache.register,known]
  | some frozen => simp [beforeHeader,PCSBCSMerkleRootCache.register,known]

theorem frozenHeader_provenance (registry : Public) (past : History Q) (header : Header) :
    frozenHeader registry past header =
      PCSBCSMerkleRootCache.freeze (frozenHeader registry past header).queryPrefix
        header.root (rootShape header) := by
  have valid := PCSBCSMerkleRootCache.register_wellFormed (replay registry past).roots
    (replay registry past).log header.root (rootShape header) (replay_wellFormed registry past)
  exact valid header.root (rootShape header) _ (frozenHeader_known registry past header)

theorem frozenHeader_geometry (registry : Public) (past : History Q)
    (header : Header) (valid : header.shape.Valid) :
    (frozenHeader registry past header).raw.size =
      2^(header.shape.logN-header.shape.logBatch+header.shape.logRate) ∧
    ∀ row ∈ (frozenHeader registry past header).raw.toList, row.size = header.shape.lanes := by
  rw [frozenHeader_provenance]
  exact PCSBCSMerkleRootCache.freeze_shape _ _ _ valid.2.2.2.2.2

theorem frozenHeader_first (registry : Public) (past : History Q) (header : Header)
    (absent : (replay registry past).roots[
      PCSBCSMerkleRootCache.cacheKey header.root (rootShape header)]? = none) :
    frozenHeader registry past header =
      PCSBCSMerkleRootCache.freeze (ordinaryPrefix past) header.root (rootShape header) := by
  simp [frozenHeader,beforeHeader,PCSBCSMerkleRootCache.register,absent,replay_log]

theorem frozenHeader_repeated (registry : Public) (past : History Q) (header : Header)
    (frozen : PCSBCSMerkleRootCache.Frozen)
    (known : (replay registry past).roots[
      PCSBCSMerkleRootCache.cacheKey header.root (rootShape header)]? = some frozen) :
    frozenHeader registry past header = frozen := by
  simp [frozenHeader,beforeHeader,PCSBCSMerkleRootCache.register,known]

/-- A raw header is registered before its own reply and retained at every
later completed event, regardless of ordinary replies or raw block indices. -/
theorem first_raw_freezes (registry : Public) (past : History Q)
    (raw : RawKey Q) (header : Header) (parsed : rawHeader registry raw = some header)
    (answer : Digest32) (later : History Q) :
    (replay registry (later ++ ((.inr raw,answer)::past))).roots[
      PCSBCSMerkleRootCache.cacheKey header.root (rootShape header)]? =
      some (frozenHeader registry past header) := by
  have first : (replay registry ((.inr raw,answer)::past)).roots[
      PCSBCSMerkleRootCache.cacheKey header.root (rootShape header)]? =
      some (frozenHeader registry past header) := by
    simpa only [replay,completed,parsed,beforeHeader] using frozenHeader_known registry past header
  induction later with
  | nil => exact first
  | cons item later ih =>
    exact completed_preserves registry _ item.1 item.2 header _ ih

abbrev Packet (registry : Public) (p : Profile) (Q : Nat) :=
  AnchoredSourceGroups.Packet registry p Q

theorem recognized_raw_header (registry : Public) (p : Profile) (raw : RawKey Q)
    (c : Sigma (fun _ : Packet registry p Q => Fin (blockCount (config p).logN)))
    (recognized : recognize Q (config p).logN registry.iv
      (AnchoredSourceGroups.accept registry p) (.inr raw) = some c) :
    rawHeader registry raw = some (AnchoredSourceGroups.header registry p Q c.1) := by
  have same := AnchoredByteStreamCausal.encode_recognize Q (config p).logN registry.iv
    (AnchoredSourceGroups.accept registry p) raw c recognized
  rw [← same]
  exact AnchoredSourceGroups.packet_key_header registry p Q c.1 c.2

/-- All geometry/admission obligations here are decoded from the packet.
No before-point certificate, final-root policy, or source chronology is a premise. -/
theorem packet_guards (registry : Public) (p : Profile) (packet : Packet registry p Q) :
    let h := AnchoredSourceGroups.header registry p Q packet
    registry.shapes h.statement = some h.shape ∧ h.shape.Valid ∧
    h.shape.logN = (config p).logN ∧ h.shape.logBatch = (config p).folds[0]! ∧
    (∀ i : Fin (blockCount (config p).logN),
      DuplexEncoding.Admissible (AnchoredByteStreamGroups.coordinate packet.val i)) ∧
    (∀ i : Fin (blockCount (config p).logN),
      DuplexFraming.pathCost (AnchoredByteStreamGroups.coordinate packet.val i) ≤ Q) := by
  have decoded := fromHistory_valid registry packet.val.history
    (AnchoredSourceGroups.header registry p Q packet)
    (AnchoredSourceGroups.header_parsed registry p Q packet)
  have geometry := (AnchoredSourceGroups.packet_header registry p Q packet).choose_spec.2
  dsimp only
  exact ⟨decoded.2.1 ▸ decoded.2.2.1,decoded.2.2.2,geometry.1,geometry.2,
    packet.val.admissible,packet.val.bounded⟩

/-- The root is exactly the compact table of the immutable public prefix.
Absent images use the existing freeze representation, not a fabricated oracle. -/
noncomputable def prepare (registry : Public) (p : Profile) (Q : Nat)
    (past : History Q) (packet : Packet registry p Q) :
    AnchoredFiatShamirSecurity.PreAnchor p :=
  let h := AnchoredSourceGroups.header registry p Q packet
  let valid := (fromHistory_valid registry packet.val.history h
    (AnchoredSourceGroups.header_parsed registry p Q packet)).2.2.2
  let bound : h.shape.lanes ≤ 2^(config p).folds[0]! := by
    rw [← AnchoredSourceGroups.header_batch registry p Q packet]
    exact valid.2.2.2.2.2
  ⟨h.shape.lanes,(frozenHeader registry past h).raw,⟨valid.2.2.2.2.1,bound⟩⟩

/-- The prepared table is literal frozen extraction, not an externally chosen
oracle or a root reconstructed from the point answer. -/
theorem prepare_literal (registry : Public) (p : Profile) (Q : Nat)
    (past : History Q) (packet : Packet registry p Q) :
    (prepare registry p Q past packet).root =
      (frozenHeader registry past (AnchoredSourceGroups.header registry p Q packet)).raw ∧
    (prepare registry p Q past packet).lanes =
      (AnchoredSourceGroups.header registry p Q packet).shape.lanes := ⟨rfl,rfl⟩

noncomputable def policy (registry : Public) (p : Profile) (Q : Nat)
    (advertise : History Q → Packet registry p Q → Joint (config p).logN → E) :
    Grouped.Policy p Q registry.iv (AnchoredSourceGroups.accept registry p) :=
  ⟨prepare registry p Q,advertise⟩

noncomputable def execution (registry : Public) (p : Profile) (Q : Nat)
    (advertise : History Q → Packet registry p Q → Joint (config p).logN → E)
    (source : Sampling (Key Q) (fun _ => Digest32) R n) (table : Key Q → Digest32) :=
  Grouped.execution (policy registry p Q advertise) source table

/-- Genuine mixed adaptive ambiguity, including repeated keys and arbitrary
ordinary replies. `n` is the aggregate mixed-draw cap, not n*point-block-count. -/
theorem mixed_ambiguity (registry : Public) (p : Profile) (Q : Nat)
    (advertise : History Q → Packet registry p Q → Joint (config p).logN → E)
    (source : Sampling (Key Q) (fun _ => Digest32) R n) :
    Soundness.uniformProb (Finset.univ.filter fun table : Key Q → Digest32 =>
      AnchoredFiatShamirSecurity.Dirty (execution registry p Q advertise source table).1.2) ≤
      (n : ℚ)/2^124 :=
  Grouped.prepared_raw_table_ambiguity (policy registry p Q advertise) source

theorem mixed_execution_result (registry : Public) (p : Profile) (Q : Nat)
    (advertise : History Q → Packet registry p Q → Joint (config p).logN → E)
    (source : Sampling (Key Q) (fun _ => Digest32) R n) (table : Key Q → Digest32) :
    (execution registry p Q advertise source table).1.1 = Sampling.eval table source :=
  Grouped.execution_result (policy registry p Q advertise) source table

/-- The existing whole source lowering is preserved as an entire public View,
not merely an opening tape or a restricted observer projection. -/
theorem source_observations_exact (registry : Public) (p : Profile)
    (seed : DuplexPublicSimulator.Seed) (ro : RawKey Q → Digest32)
    (advertise : History Q → Packet registry p Q → Joint (config p).logN → E)
    (program : Program R) (remaining : Nat) (cap : remaining ≤ Q)
    (counted : Counts remaining program) :
    (execution registry p Q advertise
      (PublicCompressionCouplingMixed.compile Q registry.iv [] program remaining cap counted)
      (PublicCompressionCouplingMixed.oracle seed ro)).1.1 =
    (runIdeal (DuplexPublicSimulator.simulator Q) ro registry.iv ⟨seed,[]⟩
      program remaining cap counted).view := by
  rw [mixed_execution_result,PublicCompressionCouplingMixed.compile_actual]

/-- Counts charges each complete construction path as well as each ordinary
query. Ideal raw lookup counts are not substituted for that aggregate work. -/
theorem source_aggregate_ambiguity (registry : Public) (p : Profile)
    (advertise : History Q → Packet registry p Q → Joint (config p).logN → E)
    (program : Program R) (remaining : Nat) (cap : remaining ≤ Q)
    (counted : Counts remaining program) :
    Soundness.uniformProb (Finset.univ.filter fun table : Key Q → Digest32 =>
      AnchoredFiatShamirSecurity.Dirty (execution registry p Q advertise
        (PublicCompressionCouplingMixed.compile Q registry.iv [] program remaining cap counted)
        table).1.2) ≤ (remaining : ℚ)/2^124 :=
  mixed_ambiguity registry p Q advertise _

def primitiveRequests (observations : List Observation) : Nat :=
  (observations.map fun o => match o.query with
    | .primitive _ _ => 1 | .construction _ _ => 0).sum

def constructionRequests (observations : List Observation) : Nat :=
  (observations.map fun o => match o.query with
    | .primitive _ _ => 0 | .construction _ _ => 1).sum

def constructionWork (observations : List Observation) : Nat :=
  (observations.map fun o => match o.query with
    | .primitive _ _ => 0
    | .construction coordinate _ => DuplexFraming.pathCost coordinate).sum

theorem work_decomposition (observations : List Observation) :
    primitiveRequests observations + constructionWork observations =
      (observations.map (fun o => o.query.cost)).sum := by
  induction observations with
  | nil => rfl
  | cons observation observations ih =>
    cases query : observation.query <;>
      simp_all [primitiveRequests,constructionWork,Query.cost] <;> omega

theorem constructionRequests_le_work (observations : List Observation) :
    constructionRequests observations ≤ constructionWork observations := by
  induction observations with
  | nil => rfl
  | cons observation observations ih =>
    cases query : observation.query with
    | primitive purpose input =>
      simpa [constructionRequests,constructionWork,query] using ih
    | construction coordinate valid =>
      have positive := DuplexRawProgram.pathCost_pos coordinate
      simp only [constructionRequests,constructionWork,List.map_cons,List.sum_cons,query] at *
      omega

theorem source_work_budget (registry : Public) (p : Profile)
    (seed : DuplexPublicSimulator.Seed) (ro : RawKey Q → Digest32)
    (advertise : History Q → Packet registry p Q → Joint (config p).logN → E)
    (program : Program R) (remaining : Nat) (cap : remaining ≤ Q)
    (counted : Counts remaining program) :
    let observations := (execution registry p Q advertise
      (PublicCompressionCouplingMixed.compile Q registry.iv [] program remaining cap counted)
      (PublicCompressionCouplingMixed.oracle seed ro)).1.1.observations
    constructionRequests observations ≤ constructionWork observations ∧
      primitiveRequests observations + constructionWork observations ≤ remaining := by
  dsimp only
  rw [source_observations_exact]
  refine ⟨constructionRequests_le_work _,?_⟩
  rw [work_decomposition]
  exact PublicCompressionCouplingMixed.runIdeal_viewCost Q seed ro registry.iv []
    program remaining cap counted

/-- The three budgets are not equated: allocations ≤ completed raw draw
requests ≤ aggregate cap. Source path work is accounted separately above. -/
theorem mixed_allocation_budget (registry : Public) (p : Profile) (Q : Nat)
    (advertise : History Q → Packet registry p Q → Joint (config p).logN → E)
    (source : Sampling (Key Q) (fun _ => Digest32) R n) (table : Key Q → Digest32) :
    Grouped.allocations (execution registry p Q advertise source table).1.2 ≤
      Grouped.rawRequests table source ∧ Grouped.rawRequests table source ≤ n :=
  Grouped.allocation_budget (policy registry p Q advertise) source table

#print axioms Grouped.repeated_original
#print axioms Grouped.repeated_allocation
#print axioms first_raw_freezes
#print axioms packet_guards
#print axioms frozenHeader_provenance
#print axioms frozenHeader_geometry
#print axioms prepare_literal
#print axioms mixed_ambiguity
#print axioms mixed_execution_result
#print axioms Grouped.prepared_full_distribution
#print axioms source_observations_exact
#print axioms source_aggregate_ambiguity
#print axioms source_work_budget
#print axioms mixed_allocation_budget

end Whir.AnchoredMixedAttackerPrefix
