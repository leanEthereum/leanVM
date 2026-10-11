import Whir.AnchoredByteStreamGroups

/-! Any first raw query into a recognized original point run allocates its whole
byte vector. Later queries, even with different block indices, reuse that same
immutable run. Off-image queries and complete public replies are preserved. -/
namespace Whir.AnchoredByteStreamCausal
open Concrete FiatShamirGame DuplexFraming DuplexModeGame
open RawOracleCoupling RawOracleCoupling.Concrete TypedOracleCompiler
open AnchoredFiatShamirSecurityCodec AnchoredByteStreamGroups

noncomputable local instance (P : Prop) : Decidable P := Classical.propDecidable P

variable (Q dimension : Nat) (iv : Digest32) (accept : FramedHistory → Bool)

abbrev Packet := {run : Run Q dimension iv // accept run.history = true}

private theorem run_ext {a b : Run Q dimension iv} (history : a.history = b.history) : a = b := by
  cases a
  cases b
  cases history
  rfl

private theorem packet_key_injective (positive : 0 < blockCount dimension) :
    Function.Injective (fun packet : Packet Q dimension iv accept =>
      key packet.val ⟨0,positive⟩) := by
  intro a b same
  dsimp only at same
  have hb := key_decodes b.val ⟨0,positive⟩
  rw [← same] at hb
  have h := (key_decodes a.val ⟨0,positive⟩).symm.trans hb
  apply Subtype.ext
  apply run_ext
  exact congrArg Coordinate.history (Option.some.inj h)

@[instance_reducible] noncomputable def packetFintype (positive : 0 < blockCount dimension) :
    Fintype (Packet Q dimension iv accept) :=
  Fintype.ofInjective (fun packet => key packet.val ⟨0,positive⟩)
    (packet_key_injective Q dimension iv accept positive)

noncomputable def recognize (raw : RawKey Q) :
    Option (Sigma (fun _ : Packet Q dimension iv accept => Fin (blockCount dimension))) := do
  let q ← WHIRHeaderRoots.decodeRaw iv raw
  match q.terminal with
  | .output block =>
    if good : accept q.history = true ∧
        (∀ i : Fin (blockCount dimension),
          DuplexEncoding.Admissible (⟨q.history,.output i.val⟩ : Coordinate)) ∧
        (∀ i : Fin (blockCount dimension),
          pathCost (⟨q.history,.output i.val⟩ : Coordinate) ≤ Q) ∧
        block < blockCount dimension then
      some ⟨⟨⟨q.history,good.2.1,good.2.2.1⟩,good.1⟩,⟨block,good.2.2.2⟩⟩
    else none
  | _ => none

def encode (c : Sigma (fun _ : Packet Q dimension iv accept => Fin (blockCount dimension))) :
    RawKey Q := key c.1.val c.2

theorem recognize_encode (c : Sigma
    (fun _ : Packet Q dimension iv accept => Fin (blockCount dimension))) :
    recognize Q dimension iv accept (encode Q dimension iv accept c) = some c := by
  rcases c with ⟨⟨⟨history,admissible,bounded⟩,accepted⟩,i⟩
  simp [recognize, encode, key_decodes, coordinate, accepted, admissible, bounded]

theorem encode_recognize (raw : RawKey Q) (c : Sigma
    (fun _ : Packet Q dimension iv accept => Fin (blockCount dimension)))
    (recognized : recognize Q dimension iv accept raw = some c) :
    encode Q dimension iv accept c = raw := by
  unfold recognize at recognized
  cases decoded : WHIRHeaderRoots.decodeRaw iv raw with
  | none => simp [decoded] at recognized
  | some q =>
    simp only [decoded] at recognized
    dsimp only [Bind.bind, Option.bind] at recognized
    cases terminal : q.terminal with
    | output block =>
      rw [terminal] at recognized
      dsimp only at recognized
      split at recognized
      · rename_i good
        have eq := Option.some.inj recognized
        subst c
        obtain ⟨bound,valid,exactRaw⟩ := WHIRHeaderRoots.decodeRaw_sound iv raw q decoded
        simpa [encode, key, coordinate, ← terminal] using exactRaw
      · contradiction
    | commitment consumed => simp [terminal] at recognized
    | powBase consumed bits => simp [terminal] at recognized

noncomputable def partition : Partition (RawKey Q) (Packet Q dimension iv accept)
    (fun _ => Fin (blockCount dimension)) where
  encode := encode Q dimension iv accept
  recognize := recognize Q dimension iv accept
  recognize_encode := recognize_encode Q dimension iv accept
  encode_recognize := encode_recognize Q dimension iv accept

/-- The recognizer is exact, including flags, IV, path holes and all raw bits.
A physical header predicate is read from the key history, never its answer. -/
theorem recognized_history (raw : RawKey Q) (c : Sigma
    (fun _ : Packet Q dimension iv accept => Fin (blockCount dimension)))
    (recognized : recognize Q dimension iv accept raw = some c) :
    WHIRHeaderRoots.decodeRaw iv raw = some (coordinate c.1.val c.2) := by
  rw [← encode_recognize Q dimension iv accept raw c recognized]
  exact key_decodes c.1.val c.2

noncomputable def request {R : Type} {n : Nat}
    (next : Digest32 → Sampling ((partition Q dimension iv accept).Key)
      ((partition Q dimension iv accept).Answer (D := Digest32)) R n) (raw : RawKey Q) :
    Sampling ((partition Q dimension iv accept).Key)
      ((partition Q dimension iv accept).Answer (D := Digest32)) R (n+1) :=
  match h : recognize Q dimension iv accept raw with
  | some c => .draw (.inl c.1) (fun blocks => next (blocks c.2))
  | none => .draw (.inr ⟨raw,h⟩) next

noncomputable def compile {R : Type} : {n : Nat} →
    Sampling (RawKey Q) (fun _ => Digest32) R n →
    Sampling ((partition Q dimension iv accept).Key)
      ((partition Q dimension iv accept).Answer (D := Digest32)) R n
  | _, .ret result => .ret result
  | _, .draw raw next => request Q dimension iv accept
      (fun answer => compile (next answer)) raw

theorem compile_eval {R : Type} {n : Nat}
    (source : Sampling (RawKey Q) (fun _ => Digest32) R n)
    (table : RawKey Q → Digest32) :
    Sampling.eval ((partition Q dimension iv accept).split table)
      (compile Q dimension iv accept source) = Sampling.eval table source := by
  induction source with
  | ret result => rfl
  | draw raw next ih =>
    unfold compile request
    split
    · rename_i c h
      simp only [Sampling.eval, Partition.split, ih]
      change Sampling.eval table (next (table (encode Q dimension iv accept c))) = _
      rw [encode_recognize Q dimension iv accept raw c h]
    · simp only [Sampling.eval, Partition.split, ih]

/-- Exact coupling for every adaptive raw continuation. The actual requested
full block is exposed; proactive coordinates are not additional raw replies. -/
theorem causal_raw_distribution {R : Type} {n : Nat}
    (positive : 0 < blockCount dimension)
    (source : Sampling (RawKey Q) (fun _ => Digest32) R n) (payoff : R → ℚ) :
    average (fun table : RawKey Q → Digest32 => payoff (Sampling.eval table source)) =
      Sampling.expectation (fun result => payoff result.1)
        (RawOracleCoupling.memo (compile Q dimension iv accept source) (fun _ => none)) := by
  classical
  let _ := packetFintype Q dimension iv accept positive
  rw [← RawOracleCoupling.empty_table_eq_memo]
  have h := RawOracleCoupling.average_equiv
    ((partition Q dimension iv accept).tableEquiv (D := Digest32))
    (fun table => payoff (Sampling.eval table (compile Q dimension iv accept source)))
  simpa only [Partition.tableEquiv, Equiv.coe_fn_mk, compile_eval] using h

/-- The completed whole-run cache is also preserved jointly; a final observer
may inspect all allocated public bytes without a restricted-observer premise. -/
theorem causal_full_distribution {R : Type} {n : Nat}
    (positive : 0 < blockCount dimension)
    (source : Sampling (RawKey Q) (fun _ => Digest32) R n)
    (payoff : R × TypedFiatShamirGame.Cache ((partition Q dimension iv accept).Key)
      ((partition Q dimension iv accept).Answer (D := Digest32)) → ℚ) :
    average (fun table : RawKey Q → Digest32 => payoff
      (Sampling.eval ((partition Q dimension iv accept).split table)
        (RawOracleCoupling.memo (compile Q dimension iv accept source) (fun _ => none)))) =
      Sampling.expectation payoff
        (RawOracleCoupling.memo (compile Q dimension iv accept source) (fun _ => none)) := by
  classical
  let _ := packetFintype Q dimension iv accept positive
  have h := RawOracleCoupling.average_equiv
    ((partition Q dimension iv accept).tableEquiv (D := Digest32))
    (fun table => payoff (Sampling.eval table
      (RawOracleCoupling.memo (compile Q dimension iv accept source) (fun _ => none))))
  exact h.trans (RawOracleCoupling.table_eq_memo_full _ (fun _ => none) payoff)

end Whir.AnchoredByteStreamCausal

#print axioms Whir.AnchoredByteStreamCausal.causal_raw_distribution
#print axioms Whir.AnchoredByteStreamCausal.causal_full_distribution
