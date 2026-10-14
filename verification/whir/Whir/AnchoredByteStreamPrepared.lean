import Whir.AnchoredByteStreamCausal

/-! Causal preparation on actual completed raw-byte history. The earliest query
into any point block prepares the root, then allocates the entire byte run.
All later indices reuse the immutable original record. -/
namespace Whir.AnchoredByteStreamPrepared
open Concrete Protocol CausalGame ParameterBounds CommitmentAnchor FiatShamirGame
open TypedOracleCompiler RawOracleCoupling RawOracleCoupling.Concrete
open AnchoredFiatShamirSecurityCodec AnchoredByteStreamGroups
open AnchoredByteStreamCausal
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
  prepare : ByteHistory Q → PointPacket p Q iv accept → AnchoredFiatShamirSecurity.PreAnchor p
  advertise : ByteHistory Q → PointPacket p Q iv accept → Joint (config p).logN → E

noncomputable def step (policy : Policy p Q iv accept) (past : ByteHistory Q)
    (records : Records (p := p) (Q := Q) (iv := iv) (accept := accept))
    (packet : PointPacket p Q iv accept) (blocks : Blocks (config p).logN) :=
  AnchoredFiatShamirSecurity.advance
    { choose := fun _ => packet
      prepare := fun _ _ => policy.prepare past packet
      advertise := fun _ _ answer => policy.advertise past packet answer }
    records (vectorParts (config p).logN blocks)

theorem repeated_original (policy : Policy p Q iv accept) (past : ByteHistory Q)
    (records : Records (p := p) (Q := Q) (iv := iv) (accept := accept))
    (packet : PointPacket p Q iv accept) (e : AnchoredFiatShamirSecurity.Entry p _)
    (hit : AnchoredFiatShamirSecurity.lookup records packet = some e)
    (blocks : Blocks (config p).logN) : step policy past records packet blocks = e :: records := by
  exact AnchoredFiatShamirSecurity.repeated_key _ records e hit _

noncomputable def compile (policy : Policy p Q iv accept) {R : Type} : {n : Nat} →
    Sampling (RawKey Q) (fun _ => Digest32) R n → ByteHistory Q →
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

private theorem step_clean (policy : Policy p Q iv accept) (past : ByteHistory Q)
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

private theorem step_seen (policy : Policy p Q iv accept) (past : ByteHistory Q)
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
    (source : Sampling (RawKey Q) (fun _ => Digest32) R n) (past : ByteHistory Q)
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
    (source : Sampling (RawKey Q) (fun _ => Digest32) R n) :
    Sampling.expectation (fun result =>
      if AnchoredFiatShamirSecurity.Dirty result.1.2 then (1 : ℚ) else 0)
      (RawOracleCoupling.memo (compile policy source [] []) (fun _ => none)) ≤ (n : ℚ)/2^124 :=
  memo_bound policy source [] [] (fun _ => none)
    (by intro packet blocks present; contradiction)
    (by simp [AnchoredFiatShamirSecurity.Dirty])

private theorem profile_blocks : ∀ p : Profile, 0 < blockCount (config p).logN := by
  decide +kernel

noncomputable def execution (policy : Policy p Q iv accept) {R : Type} {n : Nat}
    (source : Sampling (RawKey Q) (fun _ => Digest32) R n) (table : RawKey Q → Digest32) :=
  Sampling.eval ((partition Q (config p).logN iv accept).split table)
    (RawOracleCoupling.memo (compile policy source [] []) (fun _ => none))

private theorem compile_result {R : Type} {n : Nat} (policy : Policy p Q iv accept)
    (source : Sampling (RawKey Q) (fun _ => Digest32) R n) (past : ByteHistory Q)
    (records : Records (p := p) (Q := Q) (iv := iv) (accept := accept))
    (table : RawKey Q → Digest32) :
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
        (next (table (AnchoredByteStreamCausal.encode Q (config p).logN iv accept c))) = _
      rw [AnchoredByteStreamCausal.encode_recognize Q (config p).logN iv accept raw c recognized]
    · simp only [Sampling.eval, Partition.split, ih]

/-- The compiler changes no raw reply or continuation. Its extra state consists
only of the immutable prepared records and the memoized complete point runs. -/
theorem execution_result {R : Type} {n : Nat} (policy : Policy p Q iv accept)
    (source : Sampling (RawKey Q) (fun _ => Digest32) R n) (table : RawKey Q → Digest32) :
    (execution policy source table).1.1 = Sampling.eval table source := by
  unfold execution
  rw [RawOracleCoupling.memo_eval_first, RawOracleCoupling.overlay_empty]
  rw [compile_result]

/-- Joint coupling includes the actual source result, immutable records and
private grouped cache. No part of any public raw answer is erased. -/
theorem prepared_full_distribution {R : Type} {n : Nat} (policy : Policy p Q iv accept)
    (source : Sampling (RawKey Q) (fun _ => Digest32) R n)
    (payoff : (R × Records (p := p) (Q := Q) (iv := iv) (accept := accept)) ×
      GroupCache (p := p) (Q := Q) (iv := iv) (accept := accept) → ℚ) :
    average (fun table : RawKey Q → Digest32 => payoff (execution policy source table)) =
      Sampling.expectation payoff
        (RawOracleCoupling.memo (compile policy source [] []) (fun _ => none)) := by
  classical
  let _ := packetFintype Q (config p).logN iv accept (profile_blocks p)
  have h := RawOracleCoupling.average_equiv
    ((partition Q (config p).logN iv accept).tableEquiv (D := Digest32))
    (fun table => payoff (Sampling.eval table
      (RawOracleCoupling.memo (compile policy source [] []) (fun _ => none))))
  rw [show average (fun table : RawKey Q → Digest32 => payoff (execution policy source table)) =
    average (fun table => payoff (Sampling.eval table
      (RawOracleCoupling.memo (compile policy source [] []) (fun _ => none)))) from h]
  exact RawOracleCoupling.table_eq_memo_full _ (fun _ => none) payoff

theorem prepared_raw_table_ambiguity {R : Type} {n : Nat} (policy : Policy p Q iv accept)
    (source : Sampling (RawKey Q) (fun _ => Digest32) R n) :
    Soundness.uniformProb (Finset.univ.filter fun table : RawKey Q → Digest32 =>
      AnchoredFiatShamirSecurity.Dirty (execution policy source table).1.2) ≤ (n : ℚ)/2^124 := by
  classical
  have h := prepared_full_distribution policy source
    (fun result => if AnchoredFiatShamirSecurity.Dirty result.1.2 then (1 : ℚ) else 0)
  have bound := causal_prepared_ambiguity policy source
  rw [← h] at bound
  simpa only [average, Soundness.uniformProb, Finset.card_filter, Nat.cast_sum,
    Nat.cast_ite, Nat.cast_one, Nat.cast_zero] using bound


end Whir.AnchoredByteStreamPrepared

#print axioms Whir.AnchoredByteStreamPrepared.repeated_original
#print axioms Whir.AnchoredByteStreamPrepared.causal_prepared_ambiguity
#print axioms Whir.AnchoredByteStreamPrepared.execution_result
#print axioms Whir.AnchoredByteStreamPrepared.prepared_full_distribution
#print axioms Whir.AnchoredByteStreamPrepared.prepared_raw_table_ambiguity
