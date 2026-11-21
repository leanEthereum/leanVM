module

public import Quantum.StdModel.Sphincs.Reduction
public import Quantum.StdModel.Sphincs.CostsScheme

@[expose] public section

/-!
# leanSPHINCS's reductions: their honest work and their challenger queries

The charge lemmas of the six reductions of Theorem 2 without cost hypotheses. A world's cost per
hash call is `κ` (`HashCostLe W κ`: coins free, Keccak-256 at most `κ` port calls on an input of
at most `maxLen` bytes); `romWorld` has `κ = 1` (`hashCostLe_romWorld`).

* Routing (`routeHash_kinds`): a routed hash keeps the bounds per kind when the secrets cost at
  most a `PRF` call and the randomizers a `PRF_msg` call (a routed input is the input of a `.prf`
  or `.prfMsg` slot, `slot_eq_prf`, `slot_eq_prfMsg`).
* The recorded verification (`recVerify_cost`): `879 κ`, recording at most `879` inputs of at
  most `maxLen` bytes; hashing them again costs `879 κ` more (`recVerify_mapM_cost`).
* Hash calls (`isChargeBound_*_hash`), with `q` hash calls and `signs` signing requests of `A`:
  - B1, B2: `273410 κ + ((q + 12886291206 κ · signs) + 879 κ)`;
  - B3 (`itsrRed`): `273410 κ + ((q + 12886291206 κ · signs) + 0)`;
  - B4 (`encRed`): `0 + ((q + 12886291206 κ · signs) + 1758 κ)`;
  - B5 (`cpreRed`): `0 + ((q + 2 κ · signs) + 1758 κ)`;
  - B6 (`tcrRed`): `273410 κ + ((q + 12886291206 κ · signs) + 1758 κ)`.
* Challenger queries (`isChargeBound_*_call`): B1 `65538 + (286912 · signs + 0)` (the secrets'
  `PRF` calls), B2 `0 + (1 · signs + 0)`, B5
  `(keyOrder.length + 885443715538058477568 + 52776558133248 + 1) + (24 · signs + 0)` (the
  build, the counter search of every key at its cap, the openings, the reveal; the FORS
  secrets of a signature).
-/

open IPFunctor OracleComp OracleSpec
open HashSig hiding PublicKey
open Sphincs hiding HashDomain
open Sphincs.KeyGenerationAndSigning (ExpandedKey)
open Quantum.Sphincs (Slot messageDigestInput prfMessageInput)
open Quantum.Qrom.Sphincs (RawPos Pos slotInput SlotPayload length_slotInput_le)
open Common (QueryCostAtMost QueryCostAtMost.bind QueryCostAtMost.mono isWeightBound_pure
  isWeightBound_query isWeightBound_map isWeightBound_query_bind_iff
  QueryCostAtMost.bind_of_support)

namespace Quantum.StdModel.Sphincs

/-! ## Lifted world programs -/

section Lift

variable (W : OracleWorld) {Q' : Type} {R' : OracleSpec.{0, 0} Q'}

/-- Any program costs nothing under the zero cost. -/
theorem queryCostAtMost_zero {ι α : Type} {O : OracleSpec.{0, 0} ι} (oa : OracleComp O α) :
    QueryCostAtMost oa (fun _ ↦ 0) 0 := by
  induction oa using OracleComp.inductionOn with
  | pure a => trivial
  | query_bind t k ih => exact (isWeightBound_query_bind_iff _ _ _ _).mpr ⟨le_rfl, ih⟩

/-- A world program within `n` under `c` is within `n` as a reduction's program, when a world
query costs at most `c`. -/
theorem queryCostAtMost_liftW_of {w : (W.Oracles + R').Domain → ℕ} {c : W.Oracles.Domain → ℕ}
    (hw : ∀ t, w (.inl t) ≤ c t) {α : Type} {oa : OracleComp W.Oracles α} {n : ℕ}
    (h : QueryCostAtMost oa c n) : QueryCostAtMost (liftW R' oa) w n := by
  unfold liftW
  induction oa using OracleComp.inductionOn generalizing n with
  | pure a =>
    rw [simulateQ_pure]
    trivial
  | query_bind t k ih =>
    rw [isWeightBound_query_bind_iff] at h
    simp only [simulateQ_bind, simulateQ_spec_query]
    exact (isWeightBound_query_bind_iff _ _ _ _).mpr ⟨(hw t).trans h.1, fun u ↦
      (ih u (h.2 u)).mono (by have := hw t; omega)⟩

/-- A program lifted to the left summand is the lifted world program. -/
theorem liftLeft_eq_liftW {α : Type} (oa : OracleComp W.Oracles α) :
    liftLeft (spec₂ := R') oa = liftW R' oa := by
  have h := simulateQ_liftLeft (QueryImpl.id' (W.Oracles + R'))
    (fun t ↦ liftM ((W.Oracles + R').query (.inl t)) :
      QueryImpl W.Oracles (OracleComp (W.Oracles + R'))) (fun _ ↦ rfl) oa
  rwa [simulateQ_id'] at h

/-- The same for a program lifted to the left summand. -/
theorem queryCostAtMost_liftLeft_of {w : (W.Oracles + R').Domain → ℕ}
    {c : W.Oracles.Domain → ℕ} (hw : ∀ t, w (.inl t) ≤ c t) {α : Type}
    {oa : OracleComp W.Oracles α} {n : ℕ} (h : QueryCostAtMost oa c n) :
    QueryCostAtMost (liftLeft (spec₂ := R') oa) w n := by
  rw [liftLeft_eq_liftW]
  exact queryCostAtMost_liftW_of W hw h

/-- A query of the challenger's port costs its cost. -/
theorem queryCostAtMost_portQ {w : (W.Oracles + R').Domain → ℕ} {b : ℕ} (hw : ∀ q, w (.inr q) ≤ b)
    (q : Q') : QueryCostAtMost (portQ W R' q) w b :=
  (isWeightBound_query _ _).mono (hw q)

end Lift

/-! ## The world's cost per hash call -/

/-- **A world's cost `κ` per hash call**: a coin costs nothing, Keccak-256 at most `κ` calls of
the ports on an input of at most `maxLen` bytes. -/
structure HashCostLe (W : OracleWorld) (κ : ℕ) : Prop where
  /-- A coin costs nothing. -/
  coin : ∀ n, W.cost (.inl n) = 0
  /-- Keccak-256 costs at most `κ` on an input of at most `maxLen` bytes. -/
  hash : ∀ l : HashInput, l.length ≤ Quantum.Qrom.maxLen → QueryCostAtMost (W.hash l) W.cost κ

section World

variable {W : OracleWorld} {κ : ℕ} (hW : HashCostLe W κ) {Q' : Type} {R' : OracleSpec.{0, 0} Q'}
include hW

/-- A challenger's sample costs nothing. -/
theorem queryCostAtMost_sample (α : Type) [SampleableType α] :
    QueryCostAtMost (Props.sample W α) W.cost 0 :=
  Common.isWeightBound_liftM_probComp W.cost hW.coin ($ᵗ α)

/-- The world's hash in a reduction costs at most `κ` on every kind. -/
theorem hashKinds_liftW :
    HashKinds (fun l ↦ liftW R' (W.hash l)) (hcallCost W (R' := R')) (Kinds.const κ) :=
  hashKinds_const fun l hl ↦ queryCostAtMost_liftW_of W (fun _ ↦ le_rfl) (hW.hash l hl)

/-- The same for `hashL`. -/
theorem hashKinds_hashL :
    HashKinds (hashL W R') (hcallCost W (R' := R')) (Kinds.const κ) :=
  hashKinds_const fun l hl ↦ queryCostAtMost_liftLeft_of W (fun _ ↦ le_rfl) (hW.hash l hl)

end World

/-- **The QROM world costs one call per hash.** -/
theorem hashCostLe_romWorld : HashCostLe romWorld 1 where
  coin _ := rfl
  hash l _ := by
    change QueryCostAtMost (Quantum.Qrom.hashQ l) Quantum.Qrom.hashCallCost 1
    unfold Quantum.Qrom.hashQ
    split
    · exact isWeightBound_query _ _
    · exact isWeightBound_pure _ _ _

/-- A world program makes no challenger query, whatever the kinds' bounds. -/
theorem hashKinds_liftW_port (W : OracleWorld) {Q' : Type} {R' : OracleSpec.{0, 0} Q'}
    (c : Kinds) : HashKinds (fun l ↦ liftW R' (W.hash l)) (portCost W (R' := R')) c :=
  fun _ _ _ _ ↦ (queryCostAtMost_liftW_of W (c := fun _ ↦ 0) (fun _ ↦ le_rfl)
    (queryCostAtMost_zero _)).mono (Nat.zero_le _)

/-- The same for `hashL`. -/
theorem hashKinds_hashL_port (W : OracleWorld) {Q' : Type} {R' : OracleSpec.{0, 0} Q'}
    (c : Kinds) : HashKinds (hashL W R') (portCost W (R' := R')) c :=
  fun _ _ _ _ ↦ (queryCostAtMost_liftLeft_of W (c := fun _ ↦ 0) (fun _ ↦ le_rfl)
    (queryCostAtMost_zero _)).mono (Nat.zero_le _)

/-! ## Routing -/

/-- The length of a slot's input. -/
def slotLen : Slot → ℕ
  | .chain .. => 64
  | .leaf .. => 1072
  | .node .. => 80
  | .enc .. => 68
  | .forsLeaf .. => 64
  | .forsNode .. => 80
  | .forsRoots _ => 432
  | .prf _ => 80
  | .hmsg .. => 84
  | .prfMsg _ => 93
  | .expand _ => 44

theorem length_slotInput (key : ExpandedKey) (root : Digest) (s : Slot) (p : SlotPayload s) :
    (slotInput key root s p).length = slotLen s := by
  cases s with
  | chain | forsLeaf | prf =>
    simp [slotInput, slotLen, Quantum.Sphincs.length_addressedHashInput, littleEndianBytes]
  | node | forsNode =>
    simp [slotInput, slotLen, Quantum.Sphincs.length_addressedHashInput,
      HashSig.OverPermutation.nodePayload, littleEndianBytes]
  | enc =>
    simp [slotInput, slotLen, Quantum.Sphincs.length_addressedHashInput, littleEndianBytes,
      bigEndianBytes]
  | leaf =>
    rw [slotInput, Quantum.Sphincs.length_addressedHashInput,
      Quantum.Sphincs.length_digestsPayload (n := chainCount) p]
    rfl
  | forsRoots =>
    rw [slotInput, Quantum.Sphincs.length_addressedHashInput,
      Quantum.Sphincs.length_digestsPayload (n := forsTreeCount) p]
    rfl
  | hmsg => rw [slotInput, Quantum.Sphincs.length_messageDigestInput]; rfl
  | prfMsg => exact Quantum.Sphincs.length_prfMessageInput _ _ _
  | expand => rw [slotInput, Quantum.Sphincs.length_keyDerivationInput]; rfl

/-- Two addressed inputs with the same bytes have the same address and payload. -/
theorem addressedHashInput_inj {Q Q' : PublicParameter} {a a' : Address} {p p' : HashInput}
    (h : addressedHashInput Q a p = addressedHashInput Q' a' p') : a = a' ∧ p = p' := by
  unfold addressedHashInput hasherInput at h
  obtain ⟨h1, h2⟩ := List.append_inj h
    (by simp [littleEndianBytes, Quantum.Sphincs.length_toBytes])
  obtain ⟨-, h3⟩ := List.append_inj h1 (by simp [littleEndianBytes])
  exact ⟨Quantum.Sphincs.toBytes_injective h3, h2⟩

/-- **A routed secret's input is a `PRF` input**: the slot of an input equal to a secret's
`PRF` input under `SK.seed = 0` is a `.prf` slot. -/
theorem slot_eq_prf {P : PublicParameter} {d : KeygenDomain} {key : ExpandedKey} {root : Digest}
    {s : Slot} {p : SlotPayload s}
    (h : addressedHashInput P (keygenDomainFields d) (littleEndianBytes 32 (0 : MasterSeed)) =
      slotInput key root s p) : ∃ d', s = .prf d' := by
  have hl := (congrArg List.length h).trans (length_slotInput key root s p)
  rw [Quantum.Sphincs.length_addressedHashInput] at hl
  cases s with
  | prf d' => exact ⟨d', rfl⟩
  | node =>
    obtain ⟨ha, -⟩ := addressedHashInput_inj h
    cases d <;> simp [keygenDomainFields, hashDomainFields, makeAddress] at ha
  | forsNode =>
    obtain ⟨ha, -⟩ := addressedHashInput_inj h
    cases d <;> simp [keygenDomainFields, hashDomainFields, makeAddress] at ha
  | _ => simp [slotLen, littleEndianBytes] at hl

/-- **A routed randomizer's input is a `PRF_msg` input.** -/
theorem slot_eq_prfMsg {P : PublicParameter} {M : Message} {key : ExpandedKey} {root : Digest}
    {s : Slot} {p : SlotPayload s} (h : prfMessageInput 0 P M = slotInput key root s p) :
    ∃ M', s = .prfMsg M' := by
  have hl := (congrArg List.length h).trans (length_slotInput key root s p)
  rw [show (prfMessageInput 0 P M).length = 93 from
    Quantum.Sphincs.length_prfMessageInput _ _ _] at hl
  cases s with
  | prfMsg M' => exact ⟨M', rfl⟩
  | _ => simp [slotLen] at hl

/-- **The routed hash keeps the bounds per kind** when a secret costs at most a `PRF` call and a
randomizer at most a `PRF_msg` call. -/
theorem routeHash_kinds {ι : Type} {O : OracleSpec.{0, 0} ι} {P : PublicParameter}
    {sec : KeygenDomain → OracleComp O Digest} {rnd : Message → OracleComp O Digest}
    {h : HashInput → OracleComp O HashOutput} {cost : ι → ℕ} {c : Kinds}
    (hh : HashKinds h cost c) (hs : ∀ d, QueryCostAtMost (sec d) cost c.prf)
    (hr : ∀ M, QueryCostAtMost (rnd M) cost c.prfMsg) :
    HashKinds (routeHash P sec rnd h) cost c := by
  intro key root s p
  unfold routeHash
  split
  · rename_i hx
    have hq : ∀ q : RawPos, secInput P q = slotInput key root s p →
        QueryCostAtMost (secAnswer P sec rnd q) cost (c.of s) := by
      intro q he
      cases q with
      | chainStart l τ e i =>
        obtain ⟨d, rfl⟩ := slot_eq_prf (d := .oneTimeChain l τ e i) he
        exact isWeightBound_map _ (hs _)
      | forsSecret idx κ j =>
        obtain ⟨d, rfl⟩ := slot_eq_prf (d := .forsSecret idx κ j) he
        exact isWeightBound_map _ (hs _)
      | prfMsg M =>
        obtain ⟨M', rfl⟩ := slot_eq_prfMsg (M := M) he
        exact isWeightBound_map _ (hr _)
      | _ => exact isWeightBound_pure _ _ _
    exact hq _ hx.choose_spec.2
  · exact hh key root s p

/-! ## The recorded verification -/

section Rec

variable {ι : Type} {O : OracleSpec.{0, 0} ι}

/-- The weight of a hash query: one on an input of at most `maxLen` bytes, `B` on a longer one. -/
def recW (B : ℕ) (l : HashInput) : ℕ :=
  if l.length ≤ Quantum.Qrom.maxLen then 1 else B

/-- **A recorded computation** within `n < B` queries under `recW B` costs at most `n κ` and
records at most `n` inputs of at most `maxLen` bytes. -/
theorem rec_cost {h : HashInput → OracleComp O HashOutput} {cost : ι → ℕ} {κ B : ℕ}
    (hh : ∀ l : HashInput, l.length ≤ Quantum.Qrom.maxLen → QueryCostAtMost (h l) cost κ)
    {α : Type} (x : OracleComp Common.SufCma.SchemeHashSpec α) :
    ∀ n : ℕ, n < B → QueryCostAtMost x (recW B) n → ∀ l0 : List HashInput,
      QueryCostAtMost ((simulateQ (recImpl h) x).run l0) cost (n * κ) ∧
        ∀ r ∈ support ((simulateQ (recImpl h) x).run l0), ∃ new : List HashInput,
          r.2 = l0 ++ new ∧ new.length ≤ n ∧ ∀ y ∈ new, y.length ≤ Quantum.Qrom.maxLen := by
  induction x using OracleComp.inductionOn with
  | pure a =>
    intro n _ _ l0
    rw [simulateQ_pure, StateT.run_pure]
    refine ⟨trivial, fun r hr ↦ ⟨[], ?_, by simp, by simp⟩⟩
    rw [support_pure, Set.mem_singleton_iff] at hr
    rw [hr, List.append_nil]
  | query_bind t k ih =>
    intro n hn hx l0
    rw [isWeightBound_query_bind_iff] at hx
    have ht : t.length ≤ Quantum.Qrom.maxLen := by
      by_contra hc
      have h1 := hx.1
      simp only [recW, hc, ↓reduceIte] at h1
      omega
    have h1 : recW B t = 1 := by simp [recW, ht]
    rw [h1] at hx
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    have hk : ∀ o, QueryCostAtMost (k o) (recW B) m := fun o ↦ (hx.2 o).mono (by omega)
    rw [simulateQ_bind, simulateQ_spec_query, StateT.run_bind]
    have hq : (recImpl h t).run l0 = (fun o ↦ (o, l0 ++ [t])) <$> h t := by
      simp [recImpl, StateT.run_bind, StateT.run_monadLift, StateT.run_modify]
    rw [hq, bind_map_left]
    refine ⟨((hh t ht).bind fun o ↦ (ih o m (by omega) (hk o) (l0 ++ [t])).1).mono
      (by rw [Nat.succ_mul]; omega), fun r hr ↦ ?_⟩
    rw [mem_support_bind_iff] at hr
    obtain ⟨o, -, hr⟩ := hr
    obtain ⟨new, e, hl, hs⟩ := (ih o m (by omega) (hk o) (l0 ++ [t])).2 r hr
    refine ⟨t :: new, by rw [e, List.append_assoc]; rfl, by simp; omega, fun y hy ↦ ?_⟩
    rcases List.mem_cons.mp hy with rfl | hy
    · exact ht
    · exact hs y hy

theorem hashQuery_recW (B : ℕ) (l : HashInput) (hl : l.length ≤ Quantum.Qrom.maxLen) :
    QueryCostAtMost (Quantum.Sphincs.WithHash.hashQuery l) (recW B) 1 := by
  rw [Quantum.Sphincs.WithHash.hashQuery, HasQuery.instOfMonadLift_query]
  exact (isWeightBound_query _ _).mono (by simp [recW, hl])

/-- The hash-query verifier makes at most `879` queries, each of at most `maxLen` bytes. -/
theorem verify_recW (B : ℕ) (pk : PublicKey) (M : Message) (σ : Signature) :
    QueryCostAtMost (Quantum.Sphincs.WithHash.verify Quantum.Sphincs.WithHash.hashQuery pk M σ)
      (recW B) 879 := by
  have h := verify_cost (hashKinds_const (hashQuery_recW B)) pk M σ
  rw [verifyW_const, Nat.mul_one] at h
  rw [← Quantum.Qrom.Sphincs.verify_eq_withHash]
  exact h

variable {h : HashInput → OracleComp O HashOutput} {cost : ι → ℕ} {κ : ℕ}
  (hh : ∀ l : HashInput, l.length ≤ Quantum.Qrom.maxLen → QueryCostAtMost (h l) cost κ)
include hh

/-- **The recorded verification** costs at most `879 κ` and records at most `879` inputs of at
most `maxLen` bytes. -/
theorem recVerify_cost (pk : PublicKey) (M : Message) (σ : Signature) :
    QueryCostAtMost (recVerify h pk M σ) cost (879 * κ) ∧
      ∀ r ∈ support (recVerify h pk M σ),
        r.2.length ≤ 879 ∧ ∀ y ∈ r.2, y.length ≤ Quantum.Qrom.maxLen := by
  have := rec_cost hh _ 879 (by norm_num : 879 < 880) (verify_recW 880 pk M σ) []
  refine ⟨this.1, fun r hr ↦ ?_⟩
  obtain ⟨new, e, hl, hs⟩ := this.2 r hr
  rw [List.nil_append] at e
  exact ⟨e ▸ hl, e ▸ hs⟩

omit hh in
/-- `mapM` over a list whose elements' steps cost at most `b`. -/
theorem mapM_cost_mem {α β : Type} {f : α → OracleComp O β} {b : ℕ} :
    ∀ xs : List α, (∀ x ∈ xs, QueryCostAtMost (f x) cost b) →
      QueryCostAtMost (xs.mapM f) cost (xs.length * b)
  | [], _ => by
    rw [List.mapM_nil]
    exact isWeightBound_pure _ _ _
  | x :: xs, hx => by
    rw [List.mapM_cons, List.length_cons, Nat.succ_mul, Nat.add_comm]
    exact (hx x List.mem_cons_self).bind fun _ ↦ ((mapM_cost_mem xs fun y hy ↦
      hx y (List.mem_cons_of_mem _ hy)).bind fun _ ↦ isWeightBound_pure _ cost 0).mono le_rfl

/-- **The recorded verification, then the recorded inputs hashed again**: at most `879 κ` each. -/
theorem recVerify_mapM_cost {γ : Type} (F : Bool × List HashInput → List HashOutput → γ)
    (pk : PublicKey) (M : Message) (σ : Signature) :
    QueryCostAtMost (do
        let rv ← recVerify h pk M σ
        let os ← rv.2.mapM h
        pure (F rv os)) cost (879 * κ + 879 * κ) := by
  refine QueryCostAtMost.bind_of_support (recVerify_cost hh pk M σ).1 fun rv hrv ↦ ?_
  obtain ⟨hl, hs⟩ := (recVerify_cost hh pk M σ).2 rv hrv
  exact ((mapM_cost_mem rv.2 fun y hy ↦ hh y (hs y hy)).bind fun _ ↦
    isWeightBound_pure _ _ 0).mono (by rw [Nat.add_zero]; exact Nat.mul_le_mul_right _ hl)

end Rec

/-! ## Programs of challenger queries -/

section Ports

variable {ι : Type} {O : OracleSpec.{0, 0} ι} {w : ι → ℕ} {b : ℕ}

/-- A fold of steps of cost at most `b` costs at most `b` per element. -/
theorem foldlM_cost {α β : Type} {f : β → α → OracleComp O β}
    (hf : ∀ t a, QueryCostAtMost (f t a) w b) :
    ∀ (L : List α) (t : β), QueryCostAtMost (L.foldlM f t) w (L.length * b)
  | [], _ => isWeightBound_pure _ _ _
  | a :: L, t => by
    rw [List.foldlM_cons, List.length_cons, Nat.succ_mul, Nat.add_comm]
    exact (hf t a).bind fun t' ↦ foldlM_cost hf L t'

/-- The build of asks of cost at most `b` costs at most `b` per key position. -/
theorem buildDig_cost {ask : RawPos → (RawPos → Digest) → OracleComp O Digest}
    (hask : ∀ p t, QueryCostAtMost (ask p t) w b) :
    QueryCostAtMost (buildDig ask) w (keyOrder.length * b) := by
  unfold buildDig
  refine foldlM_cost (f := buildStep ask) (fun t p ↦ ?_) keyOrder _
  unfold buildStep
  exact ((hask p.1 t).bind fun _ ↦ isWeightBound_pure _ _ 0).mono (Nat.le_of_eq (Nat.add_zero _))

/-- A table of steps of cost at most `b` costs at most `b` per element. -/
theorem cpreTab_cost {α β : Type} [DecidableEq α] (L : List α) (x : β)
    {f : α → OracleComp O β} (hf : ∀ a, QueryCostAtMost (f a) w b) :
    QueryCostAtMost (cpreTab L x f) w (L.length * b) :=
  foldlM_cost (fun _ a ↦ ((hf a).bind fun _ ↦ isWeightBound_pure _ _ 0).mono
    (Nat.le_of_eq (Nat.add_zero _))) L _

end Ports

/-! ## B1 and B2: the routed reductions -/

section Routed

variable (W : OracleWorld) {Q' : Type} (R' : OracleSpec.{0, 0} Q') {C : Type}
  (par : C → PublicParameter) (sec : C → KeygenDomain → OracleComp (W.Oracles + R') Digest)
  (rnd : C → Message → OracleComp (W.Oracles + R') Digest)
  {cost : (W.Oracles + R').Domain → ℕ} {c : Kinds}

/-- **The routed setup's calls**: the context's, then key generation. -/
theorem rPre_cost (hk : HashKinds (hashL W R') cost c)
    (hs : ∀ x d, QueryCostAtMost (sec x d) cost c.prf)
    (hr : ∀ x M, QueryCostAtMost (rnd x M) cost c.prfMsg) (ctx : OracleComp (W.Oracles + R') C)
    {n₀ : ℕ} (hctx : QueryCostAtMost ctx cost n₀) :
    QueryCostAtMost (rPre W R' par sec rnd ctx) cost (n₀ + (keygenW c + 0)) := by
  unfold rPre
  exact hctx.bind fun x ↦ (keygenFromSeed_cost (routeHash_kinds hk (hs x) (hr x)) 0).bind
    fun _ ↦ isWeightBound_pure _ _ 0

/-- **The routed signer's calls.** -/
theorem rSign_cost (hk : HashKinds (hashL W R') cost c)
    (hs : ∀ x d, QueryCostAtMost (sec x d) cost c.prf)
    (hr : ∀ x M, QueryCostAtMost (rnd x M) cost c.prfMsg) (st : C × SignLog) (M : Message) :
    QueryCostAtMost (rSign W R' par sec rnd st M) cost (signW c + 0) := by
  unfold rSign
  exact (sign_cost (routeHash_kinds hk (hs st.1) (hr st.1)) 0 M).bind fun _ ↦
    isWeightBound_pure _ _ 0

/-- **The routed output's calls**: the verifier's. -/
theorem rPost_cost (hk : HashKinds (hashL W R') cost c) (a : C × PublicKey) (f : Forgery)
    (st : C × SignLog) : QueryCostAtMost (rPost W R' a f st) cost (verifyW c + 0) := by
  unfold rPost
  exact (verify_cost hk _ _ _).bind fun _ ↦ isWeightBound_pure _ _ 0

end Routed

/-- The kinds' bounds of the challenger calls of B1: one per `PRF` call. -/
def prfKinds : Kinds :=
  { Kinds.const 0 with prf := 1 }

/-- The kinds' bounds of the challenger calls of B2: one per `PRF_msg` call. -/
def prfMsgKinds : Kinds :=
  { Kinds.const 0 with prfMsg := 1 }

theorem keygenW_prfKinds : keygenW prfKinds = 65536 := by
  simp only [keygenW, treeLevelsW, otsPublicLeafW, prfKinds, Kinds.const, chainCount]
  norm_num

theorem signW_prfKinds : signW prfKinds = 286912 := by
  simp only [signW, treeLevelsW, otsPublicLeafW, forsOpenW, forsTreeOpenW, signLayerW, otsSignW,
    openW, prfKinds, Kinds.const, chainCount, forsTreeCount, forsTreeHeight, encodingAttemptLimit]
  norm_num

theorem verifyW_prfKinds : verifyW prfKinds = 0 := by
  simp only [verifyW, forsRecoverW, forsTreeRecoverW, layerW, otsLeafW, prfKinds, Kinds.const,
    chainCount, forsTreeCount, forsTreeHeight, layerCount]

theorem keygenW_prfMsgKinds : keygenW prfMsgKinds = 0 := by
  simp only [keygenW, treeLevelsW, otsPublicLeafW, prfMsgKinds, Kinds.const, chainCount]
  norm_num

theorem signW_prfMsgKinds : signW prfMsgKinds = 1 := by
  simp only [signW, treeLevelsW, otsPublicLeafW, forsOpenW, forsTreeOpenW, signLayerW, otsSignW,
    openW, prfMsgKinds, Kinds.const, chainCount, forsTreeCount, forsTreeHeight,
    encodingAttemptLimit]
  norm_num

theorem verifyW_prfMsgKinds : verifyW prfMsgKinds = 0 := by
  simp only [verifyW, forsRecoverW, forsTreeRecoverW, layerW, otsLeafW, prfMsgKinds, Kinds.const,
    chainCount, forsTreeCount, forsTreeHeight, layerCount]

section B12

variable {W : OracleWorld} {κ : ℕ} (hW : HashCostLe W κ) (A : SAdv W) {q signs : ℕ}
  (hq : ∀ pk, IFreeM.IsChargeBound (A pk) (cmdCharge hashCharge) q)
  (hs : ∀ pk, IFreeM.IsChargeBound (A pk) (cmdCharge callCharge) signs)

include hs in
/-- **B1's challenger queries**: `PK.seed` and `SK.prf`, the `PRF` calls of key generation and
`286912` per signing request (the trees' levels and the FORS secrets). -/
theorem isChargeBound_B1_call :
    IFreeM.IsChargeBound (B1 W A ()) (cmdCharge callCharge) (65538 + (286912 * signs + 0)) := by
  have hctx : QueryCostAtMost (b1Ctx W) (portCost W (R' := KimSpec)) 2 := by
    unfold b1Ctx
    exact (queryCostAtMost_portQ W (b := 1) (fun _ ↦ le_rfl) _).bind fun _ ↦
      (queryCostAtMost_portQ W (b := 1) (fun _ ↦ le_rfl) _).bind fun _ ↦ isWeightBound_pure _ _ 0
  have hsec : ∀ x d, QueryCostAtMost (b1Sec W x d) (portCost W (R' := KimSpec)) prfKinds.prf :=
    fun _ _ ↦ isWeightBound_map _ (queryCostAtMost_portQ W (b := 1) (fun _ ↦ le_rfl) _)
  have hrnd : ∀ x M, QueryCostAtMost (b1Rnd W x M) (portCost W (R' := KimSpec))
      prfKinds.prfMsg := fun _ _ ↦
    isWeightBound_map _ (queryCostAtMost_liftLeft_of W (c := fun _ ↦ 0) (fun _ ↦ le_rfl)
      (queryCostAtMost_zero _))
  have h := isChargeBound_routedRed_call W KimSpec Prod.fst (b1Sec W) (b1Rnd W) A (b1Ctx W)
    (rPre_cost W KimSpec Prod.fst (b1Sec W) (b1Rnd W) (hashKinds_hashL_port W prfKinds) hsec
      hrnd _ hctx)
    (rSign_cost W KimSpec Prod.fst (b1Sec W) (b1Rnd W) (hashKinds_hashL_port W prfKinds) hsec
      hrnd)
    (rPost_cost W KimSpec (hashKinds_hashL_port W prfKinds)) hs ()
  rw [keygenW_prfKinds, signW_prfKinds, verifyW_prfKinds] at h
  exact h

include hs in
/-- **B2's challenger queries**: one `PRF_msg` query per signing request. -/
theorem isChargeBound_B2_call :
    IFreeM.IsChargeBound (B2 W A ()) (cmdCharge callCharge) (0 + (1 * signs + 0)) := by
  have hctx : QueryCostAtMost (b2Ctx W) (portCost W (R' := MsgSpec)) 0 := by
    unfold b2Ctx
    exact (queryCostAtMost_liftLeft_of W (c := fun _ ↦ 0) (fun _ ↦ le_rfl)
      (queryCostAtMost_zero _)).bind fun _ ↦ (queryCostAtMost_liftLeft_of W (c := fun _ ↦ 0)
        (fun _ ↦ le_rfl) (queryCostAtMost_zero _)).bind fun _ ↦ isWeightBound_pure _ _ 0
  have hsec : ∀ x d, QueryCostAtMost (b2Sec W x d) (portCost W (R' := MsgSpec))
      prfMsgKinds.prf := fun _ _ ↦ isWeightBound_pure _ _ _
  have hrnd : ∀ x M, QueryCostAtMost (b2Rnd W x M) (portCost W (R' := MsgSpec))
      prfMsgKinds.prfMsg := fun _ _ ↦ queryCostAtMost_portQ W (b := 1) (fun _ ↦ le_rfl) _
  have h := isChargeBound_routedRed_call W MsgSpec Prod.fst (b2Sec W) (b2Rnd W) A (b2Ctx W)
    (rPre_cost W MsgSpec Prod.fst (b2Sec W) (b2Rnd W) (hashKinds_hashL_port W prfMsgKinds) hsec
      hrnd _ hctx)
    (rSign_cost W MsgSpec Prod.fst (b2Sec W) (b2Rnd W) (hashKinds_hashL_port W prfMsgKinds) hsec
      hrnd)
    (rPost_cost W MsgSpec (hashKinds_hashL_port W prfMsgKinds)) hs ()
  rw [keygenW_prfMsgKinds, signW_prfMsgKinds, verifyW_prfMsgKinds] at h
  exact h

include hW hq hs

/-- **B1's hash calls**: `A`'s, key generation `273410 κ`, the signer `12886291206 κ` per
signing request, the verifier `879 κ`. -/
theorem isChargeBound_B1_hash :
    IFreeM.IsChargeBound (B1 W A ()) (cmdCharge hashCharge)
      (273410 * κ + ((q + 12886291206 * κ * signs) + 879 * κ)) := by
  have hk := hashKinds_hashL (R' := KimSpec) hW
  have hctx : QueryCostAtMost (b1Ctx W) (hcallCost W (R' := KimSpec)) 0 := by
    unfold b1Ctx
    exact (queryCostAtMost_portQ W (b := 0) (fun _ ↦ le_rfl) _).bind fun _ ↦
      (queryCostAtMost_portQ W (b := 0) (fun _ ↦ le_rfl) _).bind fun _ ↦ isWeightBound_pure _ _ 0
  have hsec : ∀ x d, QueryCostAtMost (b1Sec W x d) (hcallCost W (R' := KimSpec))
      (Kinds.const κ).prf := fun _ _ ↦
    (isWeightBound_map _ (queryCostAtMost_portQ W (b := 0) (fun _ ↦ le_rfl) _)).mono
      (Nat.zero_le _)
  have hrnd : ∀ x M, QueryCostAtMost (b1Rnd W x M) (hcallCost W (R' := KimSpec))
      (Kinds.const κ).prfMsg := fun x M ↦
    isWeightBound_map _ (hk ⟨0, x.2, x.1⟩ 0 (.prfMsg M) ())
  have h := isChargeBound_routedRed W KimSpec Prod.fst (b1Sec W) (b1Rnd W) A (b1Ctx W)
    (rPre_cost W KimSpec Prod.fst (b1Sec W) (b1Rnd W) hk hsec hrnd _ hctx)
    (rSign_cost W KimSpec Prod.fst (b1Sec W) (b1Rnd W) hk hsec hrnd)
    (rPost_cost W KimSpec hk) hq hs ()
  rw [keygenW_const, signW_const, verifyW_const] at h
  simp only [Nat.zero_add, Nat.add_zero] at h
  exact h

/-- **B2's hash calls**: `A`'s, key generation `273410 κ`, the signer `12886291206 κ` per
signing request, the verifier `879 κ`. -/
theorem isChargeBound_B2_hash :
    IFreeM.IsChargeBound (B2 W A ()) (cmdCharge hashCharge)
      (273410 * κ + ((q + 12886291206 * κ * signs) + 879 * κ)) := by
  have hk := hashKinds_hashL (R' := MsgSpec) hW
  have hctx : QueryCostAtMost (b2Ctx W) (hcallCost W (R' := MsgSpec)) 0 := by
    unfold b2Ctx
    exact (queryCostAtMost_liftLeft_of W (c := W.cost) (fun _ ↦ le_rfl)
      (queryCostAtMost_sample hW _)).bind fun _ ↦ (queryCostAtMost_liftLeft_of W (c := W.cost)
        (fun _ ↦ le_rfl) (queryCostAtMost_sample hW _)).bind fun _ ↦ isWeightBound_pure _ _ 0
  have hsec : ∀ x d, QueryCostAtMost (b2Sec W x d) (hcallCost W (R' := MsgSpec))
      (Kinds.const κ).prf := fun _ _ ↦ isWeightBound_pure _ _ _
  have hrnd : ∀ x M, QueryCostAtMost (b2Rnd W x M) (hcallCost W (R' := MsgSpec))
      (Kinds.const κ).prfMsg := fun _ _ ↦
    (queryCostAtMost_portQ W (b := 0) (fun _ ↦ le_rfl) _).mono (Nat.zero_le _)
  have h := isChargeBound_routedRed W MsgSpec Prod.fst (b2Sec W) (b2Rnd W) A (b2Ctx W)
    (rPre_cost W MsgSpec Prod.fst (b2Sec W) (b2Rnd W) hk hsec hrnd _ hctx)
    (rSign_cost W MsgSpec Prod.fst (b2Sec W) (b2Rnd W) hk hsec hrnd)
    (rPost_cost W MsgSpec hk) hq hs ()
  rw [keygenW_const, signW_const, verifyW_const] at h
  simp only [Nat.zero_add, Nat.add_zero] at h
  exact h

end B12

end Quantum.StdModel.Sphincs

end
