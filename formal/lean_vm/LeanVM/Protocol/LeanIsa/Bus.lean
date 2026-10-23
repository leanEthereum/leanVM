/-
  LeanVM.Protocol.LeanIsa.Bus

  The bus of a leanISA witness read as the M3 model's one bus: the sixteen-slot tuples of its
  interactions, side by side, and the three channel pairs' balances as one permutation.
-/

module

public import LeanVM.Protocol.LeanIsa.Read

/-!
# The leanISA bus as one bus

leanISA's constraint system has six channels, three pairs, and balances each pair as a multiset
of messages (`BalancedPair`). The M3 model has one bus of sixteen-slot tuples, the separator first,
pushes against pulls (`M3Instance.Balanced`). This module relates the two on any witness of the
ensemble.

* `interaction_channel`: every interaction of a witness is on one of the six channels, with that
  channel's arity: the ensemble's components emit on nothing else.
* `sideTuples w side`: the tuples a witness flushes on one side: every interaction whose channel's
  direction is that side, as `flushTuple`, leanISA's `busTuple`.
* `balanced_iff`: the two sides are one multiset exactly when the three channel pairs balance. A
  tuple's separator names its pair, and on one channel the tuple determines the message, since no
  message has more than fifteen coordinates.
-/

namespace LeanVM.Protocol.LeanIsa

open LeanVM.Parameters LeanVM.Semantics LeanVM.Arithmetization
open Air.Flat (Component EnsembleWitness Ensemble)

@[expose] public section

/-! ## The six channels -/

/-- The six channels by name, with their arities. -/
def channelTable : List (String × ℕ) :=
  [(StatePull.name, 2), (StatePush.name, 2), (MemPull.name, 5), (MemPush.name, 5),
    (BytecodePull.name, 10), (BytecodePush.name, 10)]

/-- The eight components of the ensemble emit on the six channels only, with their arities. -/
private theorem tables_channels :
    ∀ c ∈ ([⟨xorTable⟩, ⟨mulTable⟩, ⟨setTable⟩, ⟨derefTable⟩, ⟨jumpTable⟩, ⟨blake2sTable⟩,
      ⟨memTable⟩, ⟨bytecodeTable⟩] : List (Component K)),
      ∀ ai ∈ c.rowOperations.interactions, (ai.channel.name, ai.channel.arity) ∈ channelTable := by
  decide +kernel

/-- Every component of the ensemble, the verifier included, emits on the six channels only. -/
private theorem components_channels (prog : Program) :
    ∀ c ∈ (leanIsaEnsemble prog).allTables, ∀ ai ∈ c.rowOperations.interactions,
      (ai.channel.name, ai.channel.arity) ∈ channelTable := by
  intro c hc
  rcases List.mem_cons.mp hc with rfl | hc
  · intro ai hai
    have h : (leanIsaEnsemble prog).verifierTable.rowOperations.interactions.map
        (fun ai ↦ (ai.channel.name, ai.channel.arity)) =
          [(StatePush.name, 2), (StatePull.name, 2)] :=
      rfl
    have := List.mem_map_of_mem (f := fun ai : AbstractInteraction K ↦
      (ai.channel.name, ai.channel.arity)) hai
    rw [h] at this
    simp only [List.mem_cons, List.not_mem_nil, or_false] at this
    rcases this with h | h <;> rw [h] <;> simp [channelTable]
  · exact tables_channels c hc

variable {prog : Program}

/-- An interaction of a witness is the evaluation of one of its components' interactions on a
row. -/
private theorem mem_interactions {w : EnsembleWitness (leanIsaEnsemble prog)} {i : Interaction K}
    (hi : i ∈ w.interactions) :
    ∃ t ∈ w.allTables, ∃ row ∈ t.table, ∃ ai ∈ t.component.rowOperations.interactions,
      i = ai.eval (t.environment row) := by
  simp only [EnsembleWitness.interactions, List.mem_flatMap, Air.Flat.Table.interactions,
    Operations.interactionValues, List.mem_map, Air.Flat.Component.interactions_eq] at hi
  obtain ⟨t, ht, row, hrow, ai, hai, rfl⟩ := hi
  exact ⟨t, ht, row, hrow, ai, hai, rfl⟩

/-- Every interaction of a witness is on one of the six channels, with its arity. -/
theorem interaction_channel {w : EnsembleWitness (leanIsaEnsemble prog)} {i : Interaction K}
    (hi : i ∈ w.interactions) : (i.channel.name, i.channel.arity) ∈ channelTable := by
  obtain ⟨t, ht, row, _, ai, hai, rfl⟩ := mem_interactions hi
  exact components_channels prog t.component
    (EnsembleWitness.mem_allTables_component_of_mem_allTables ht) ai hai

/-! ## Tuples and separators -/

/-- The push channel of pair `k`: state, memory, bytecode. -/
def pushOf (k : Fin 3) : RawChannel K := ![StatePush.toRaw, MemPush.toRaw, BytecodePush.toRaw] k

/-- The pull channel of pair `k`. -/
def pullOf (k : Fin 3) : RawChannel K := ![StatePull.toRaw, MemPull.toRaw, BytecodePull.toRaw] k

/-- The channel of pair `k` on one side. -/
def channelOf : Side → Fin 3 → RawChannel K
  | .push => pushOf
  | .pull => pullOf

/-- The arity of pair `k`'s messages. -/
def arityOf (k : Fin 3) : ℕ := ![2, 5, 10] k

/-- The three separators are distinct and nonzero. -/
private theorem gpow_facts : gpow 0 ≠ gpow 1 ∧ gpow 0 ≠ gpow 2 ∧ gpow 1 ≠ gpow 2 ∧ gpow 0 ≠ 0 ∧
    gpow 1 ≠ 0 ∧ gpow 2 ≠ 0 := by
  decide +kernel

/-- An interaction's side and separator are those of pair `k` exactly on pair `k`'s channel of
that side: the bus reads both off the channel's name. -/
private theorem view_iff (ch : RawChannel K) (side : Side) (k : Fin 3) :
    (sideOf (channelDir ch) = side ∧ channelSep ch = gpow k) ↔
      ch.name = (channelOf side k).name := by
  obtain ⟨h01, h02, h12, h0, h1, h2⟩ := gpow_facts
  unfold channelDir channelSep
  generalize ch.name = n
  simp only [StatePull, StatePush, MemPull, MemPush, BytecodePull, BytecodePush]
  by_cases a : n = "st.pull"
  · subst a; cases side <;> fin_cases k <;> simp_all [sideOf, channelOf, pushOf, pullOf,
        Channel.toRaw, StatePull, StatePush, MemPull, MemPush, BytecodePull, BytecodePush, Ne.symm]
  by_cases b : n = "st.push"
  · subst b; cases side <;> fin_cases k <;> simp_all [sideOf, channelOf, pushOf, pullOf,
        Channel.toRaw, StatePull, StatePush, MemPull, MemPush, BytecodePull, BytecodePush, Ne.symm]
  by_cases c : n = "mem.pull"
  · subst c; cases side <;> fin_cases k <;> simp_all [sideOf, channelOf, pushOf, pullOf,
        Channel.toRaw, StatePull, StatePush, MemPull, MemPush, BytecodePull, BytecodePush, Ne.symm]
  by_cases d : n = "mem.push"
  · subst d; cases side <;> fin_cases k <;> simp_all [sideOf, channelOf, pushOf, pullOf,
        Channel.toRaw, StatePull, StatePush, MemPull, MemPush, BytecodePull, BytecodePush, Ne.symm]
  by_cases e : n = "bc.pull"
  · subst e; cases side <;> fin_cases k <;> simp_all [sideOf, channelOf, pushOf, pullOf,
        Channel.toRaw, StatePull, StatePush, MemPull, MemPush, BytecodePull, BytecodePush, Ne.symm]
  by_cases f : n = "bc.push"
  · subst f; cases side <;> fin_cases k <;> simp_all [sideOf, channelOf, pushOf, pullOf,
        Channel.toRaw, StatePull, StatePush, MemPull, MemPush, BytecodePull, BytecodePush, Ne.symm]
  cases side <;> fin_cases k <;> simp_all [sideOf, channelOf, pushOf, pullOf, Channel.toRaw,
      StatePull, StatePush, MemPull, MemPush, BytecodePull, BytecodePush, Ne.symm]

/-- A channel of the table has the separator of one of the three pairs. -/
private theorem channelSep_of_mem {ch : RawChannel K} (h : (ch.name, ch.arity) ∈ channelTable) :
    ∃ k : Fin 3, channelSep ch = gpow k := by
  unfold channelSep
  simp only [channelTable, StatePull, StatePush, MemPull, MemPush, BytecodePull, BytecodePush,
    List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at h
  rcases h with ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ <;>
    simp only [h, StatePull, StatePush, MemPull, MemPush, BytecodePull, BytecodePush]
  exacts [⟨0, by simp⟩, ⟨0, by simp⟩, ⟨1, by simp⟩, ⟨1, by simp⟩, ⟨2, by simp⟩, ⟨2, by simp⟩]

/-- A channel of the table named as pair `k`'s channel of a side has pair `k`'s arity. -/
private theorem arity_of_mem {ch : RawChannel K} (h : (ch.name, ch.arity) ∈ channelTable)
    {side : Side}
    {k : Fin 3} (hn : ch.name = (channelOf side k).name) : ch.arity = arityOf k := by
  simp only [channelTable, List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at h
  cases side <;> fin_cases k <;>
    simp only [channelOf, pushOf, pullOf, arityOf, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk,
      Matrix.cons_val, Channel.toRaw] at hn ⊢ <;>
    rcases h with ⟨h, h'⟩ | ⟨h, h'⟩ | ⟨h, h'⟩ | ⟨h, h'⟩ | ⟨h, h'⟩ | ⟨h, h'⟩ <;>
    simp_all [StatePull, StatePush, MemPull, MemPush, BytecodePull, BytecodePush]

/-- The sixteen-slot tuple of a message with the separator `σ`. -/
def tupleOf (σ : K) (m : Array K) : Vector K 16 :=
  Vector.ofFn fun k ↦ if k.val = 0 then σ else m[k.val - 1]?.getD 0

/-- A message of at most fifteen coordinates is read back off its tuple. -/
theorem tupleMsg_tupleOf (σ : K) (m : Array K) (h : m.size ≤ 15) :
    tupleMsg m.size (tupleOf σ m) = m := by
  apply Array.ext (by simp [tupleMsg])
  intro k _ hk
  simp only [tupleMsg, Array.getElem_ofFn]
  rw [Vector.getElem?_eq_getElem (by omega), Option.getD_some]
  simp only [tupleOf, Vector.getElem_ofFn, Nat.add_one_ne_zero, ite_false, Nat.add_sub_cancel]
  rw [Array.getElem?_eq_getElem hk, Option.getD_some]

/-- Messages of one length at most fifteen are read back off their tuples. -/
theorem map_tupleMsg_tupleOf {σ : K} {a : ℕ} (l : List (Array K)) (hl : ∀ m ∈ l, m.size = a)
    (ha : a ≤ 15) : (l.map (tupleOf σ)).map (tupleMsg a) = l := by
  rw [List.map_map]
  conv_rhs => rw [← List.map_id l]
  refine List.map_congr_left fun m hm ↦ ?_
  rw [Function.comp_apply, ← hl m hm, tupleMsg_tupleOf _ _ (by rw [hl m hm]; exact ha), id]

/-- The side and tuple of an interaction on the bus. -/
def busView (i : Interaction K) : Side × Vector K 16 :=
  (sideOf (channelDir i.channel), flushTuple channelSep i)

/-- The tuples a list of interactions flushes on one side. -/
def tuplesOn (l : List (Interaction K)) (side : Side) : List (Vector K 16) :=
  ((l.map busView).filter fun v ↦ decide (v.1 = side)).map (·.2)

/-- The tuples a witness flushes on one side of the bus. -/
abbrev sideTuples (w : EnsembleWitness (leanIsaEnsemble prog)) (side : Side) :
    List (Vector K 16) :=
  tuplesOn w.interactions side

/-- The tuples one side flushes with pair `k`'s separator are the messages on pair `k`'s channel of
that side, as tuples. -/
theorem filter_tuplesOn (l : List (Interaction K)) (side : Side) (k : Fin 3) :
    (tuplesOn l side).filter (fun v : Vector K 16 ↦ decide (v[0] = gpow k)) =
      ((l.filter fun i ↦ decide (i.channel.name = (channelOf side k).name)).map (·.msg)).map
        (tupleOf (gpow k)) := by
  induction l with
  | nil => rfl
  | cons i l ih =>
    have hv := view_iff i.channel side k
    have h0 : (flushTuple channelSep i)[0] = channelSep i.channel := by simp [flushTuple]
    by_cases hn : i.channel.name = (channelOf side k).name
    · have hv' := hv.mpr hn
      simp only [tuplesOn, List.map_cons, List.filter_cons, busView, hv'.1, decide_true,
        ite_true, List.filter_cons, h0, hv'.2, hn] at ih ⊢
      rw [ih]
      show tupleOf (channelSep i.channel) i.msg :: _ = _
      rw [hv'.2]
    · have hv' : ¬ (sideOf (channelDir i.channel) = side ∧ channelSep i.channel = gpow k) :=
        fun h ↦ hn (hv.mp h)
      simp only [tuplesOn] at ih ⊢
      rw [List.filter_cons_of_neg (by simpa using hn), List.map_cons, List.filter_cons]
      by_cases hs : sideOf (channelDir i.channel) = side
      · simp only [busView, hs, decide_true, ite_true, List.map_cons, List.filter_cons, h0,
          show ¬ channelSep i.channel = gpow k from fun h ↦ hv' ⟨hs, h⟩, decide_false,
          Bool.false_eq_true, ite_false]
        exact ih
      · simp only [busView, hs, decide_false, Bool.false_eq_true, ite_false]
        exact ih

/-- Every tuple of a witness's bus has the separator of one of the three pairs. -/
private theorem sideTuples_sep {w : EnsembleWitness (leanIsaEnsemble prog)} {side : Side}
    {v : Vector K 16} (hv : v ∈ sideTuples w side) : ∃ k : Fin 3, v[0] = gpow k := by
  simp only [sideTuples, tuplesOn, List.mem_map, List.mem_filter] at hv
  obtain ⟨_, ⟨⟨i, hi, rfl⟩, -⟩, rfl⟩ := hv
  obtain ⟨k, hk⟩ := channelSep_of_mem (interaction_channel hi)
  exact ⟨k, by simp [busView, flushTuple, hk]⟩

/-- A message on pair `k`'s channel of a side has pair `k`'s arity. -/
private theorem size_of_mem_messagesOn {w : EnsembleWitness (leanIsaEnsemble prog)} {side : Side}
    {k : Fin 3} {m : Array K}
    (hm : m ∈ (w.interactions.filter fun i ↦ decide (i.channel.name = (channelOf side k).name)).map
      (·.msg)) : m.size = arityOf k := by
  obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hm
  rw [List.mem_filter, decide_eq_true_eq] at hi
  rw [i.same_size]
  exact arity_of_mem (interaction_channel hi.1) hi.2

/-- Pair `k` balances exactly when the two sides' tuples with its separator are one multiset. -/
theorem balancedPair_iff (w : EnsembleWitness (leanIsaEnsemble prog)) (k : Fin 3) :
    BalancedPair w (pullOf k) (pushOf k) ↔
      ((sideTuples w .push).filter fun v : Vector K 16 ↦ decide (v[0] = gpow k)).Perm
        ((sideTuples w .pull).filter fun v : Vector K 16 ↦ decide (v[0] = gpow k)) := by
  rw [filter_tuplesOn, filter_tuplesOn]
  constructor
  · exact fun h ↦ h.map _
  · intro h
    have hk : arityOf k ≤ 15 := by fin_cases k <;> decide
    have h' := h.map (tupleMsg (arityOf k))
    rwa [map_tupleMsg_tupleOf _ (fun m hm ↦ size_of_mem_messagesOn hm) hk,
      map_tupleMsg_tupleOf _ (fun m hm ↦ size_of_mem_messagesOn hm) hk] at h'

/-- The two sides of the bus are one multiset exactly when the three channel pairs balance. -/
theorem balanced_iff (w : EnsembleWitness (leanIsaEnsemble prog)) :
    (sideTuples w .push).Perm (sideTuples w .pull) ↔ ∀ k : Fin 3,
        BalancedPair w (pullOf k) (pushOf k) := by
  simp only [balancedPair_iff]
  constructor
  · exact fun h k ↦ h.filter _
  · intro h
    rw [List.perm_iff_count]
    intro v
    by_cases hv : ∃ k : Fin 3, v[0] = gpow k
    · obtain ⟨k, hk⟩ := hv
      have := (List.perm_iff_count.mp (h k)) v
      simpa only [List.count_filter, hk, decide_true, ite_true] using this
    · rw [List.count_eq_zero_of_not_mem fun hm ↦ hv (sideTuples_sep hm),
        List.count_eq_zero_of_not_mem fun hm ↦ hv (sideTuples_sep hm)]

/-! ## A component's tuples -/

/-- The direction of the channel named `n`, as `channelDir` reads it. -/
private def nameDir (n : String) : Arithmetization.Direction :=
  if n = StatePull.name ∨ n = MemPull.name ∨ n = BytecodePull.name then .pull else .push

/-- The separator of the channel named `n`, as `channelSep` reads it. -/
private def nameSep (n : String) : K :=
  if n = StatePull.name ∨ n = StatePush.name then gpow 0
  else if n = MemPull.name ∨ n = MemPush.name then gpow 1
  else if n = BytecodePull.name ∨ n = BytecodePush.name then gpow 2
  else 0

/-- The side and tuple of a message on the channel of a name. -/
private def nameView (p : String × Array K) : Side × Vector K 16 :=
  (sideOf (nameDir p.1), tupleOf (nameSep p.1) p.2)

/-- The tuples of a list of interactions depend only on their channels' names and their
messages. -/
private theorem tuplesOn_eq (l : List (Interaction K)) (side : Side) :
    tuplesOn l side = ((((l.map fun i ↦ (i.channel.name, i.msg)).map nameView).filter
      fun v ↦ decide (v.1 = side)).map (·.2)) := by
  rw [tuplesOn, List.map_map]
  rfl

/-- Ten coordinates written as one vector. -/
private theorem vec_ten {α : Type} (a b c d e f g h i j : α) :
    #v[a] ++ (#v[b] ++ (#v[c] ++ #v[d, e, f, g, h, i, j])) = #v[a, b, c, d, e, f, g, h, i, j] := by
  apply Vector.toArray_inj.mp
  simp only [Vector.toArray_append]
  simp

/-- The memory block's two messages on a row: the seed push `(idx, 1, m)` and the finalize pull
`(idx, cntFin, m)`. -/
theorem memTable_messages (idx cnt a b c : K) (data : ProverData K) :
    ((⟨memTable⟩ : Component K).operations.interactionValues
      (Environment.fromArray (toElements (⟨idx, cnt, #v[a, b, c]⟩ : MemRow K)).toArray data)).map
        (fun i ↦ (i.channel.name, i.msg)) =
      [(MemPush.name, #[idx, 1, a, b, c]), (MemPull.name, #[idx, cnt, a, b, c])] := by
  rw [Air.Flat.Component.interactionsValues_eq]
  simp [Operations.interactionValues, Air.Flat.Component.rowOperations, memTable, circuit_norm,
    AbstractInteraction.eval, explicit_provable_type, MemPush, MemPull, -BitVec.reduceNeg,
    ProvableStruct.componentsToElements, ProvableStruct.toComponents, toComponents]
  refine ⟨Array.ext (by simp) fun i h1 _ ↦ ?_, Array.ext (by simp) fun i h1 _ ↦ ?_⟩ <;>
    simp only [Array.size_map, Vector.size_toArray] at h1 <;>
    simp only [Array.getElem_map, Vector.getElem_toArray] <;> interval_cases i <;> rfl

/-- The bytecode block's two messages on a row: the seed push `(idx, 1, opcode, op)` and the
finalize pull `(idx, cntFin, opcode, op)`. -/
theorem bytecodeTable_messages (idx cnt opc o₁ o₂ o₃ o₄ o₅ o₆ o₇ : K) (data : ProverData K) :
    ((⟨bytecodeTable⟩ : Component K).operations.interactionValues
      (Environment.fromArray (toElements (⟨idx, cnt, opc, #v[o₁, o₂, o₃, o₄, o₅, o₆, o₇]⟩ :
        BytecodeRow K)).toArray data)).map (fun i ↦ (i.channel.name, i.msg)) =
      [(BytecodePush.name, #[idx, 1, opc, o₁, o₂, o₃, o₄, o₅, o₆, o₇]),
        (BytecodePull.name, #[idx, cnt, opc, o₁, o₂, o₃, o₄, o₅, o₆, o₇])] := by
  rw [Air.Flat.Component.interactionsValues_eq]
  simp only [Operations.interactionValues, Air.Flat.Component.rowOperations, bytecodeTable,
    circuit_norm, -BitVec.reduceNeg]
  simp only [List.cons.injEq, Prod.mk.injEq, true_and, and_true, AbstractInteraction.eval]
  simp only [Vector.mapRange_succ, Vector.mapRange_zero, Nat.add_zero, Vector.push_mk,
    Nat.reduceAdd, Array.push_empty, ChannelInteraction.toRaw_channel, Channel.toRaw_arity, size,
    ProvableStruct.combinedSize, ProvableStruct.combinedSize', instProvableTypeFields.eq_1,
    ProvableStruct.combinedSize'.eq_2, ProvableStruct.combinedSize'.eq_1, toElements,
    ProvableStruct.structToElements_eq, components, toComponents,
    ProvableStruct.componentsToElements, Vector.append_empty, Vector.cast_rfl,
    Vector.getElem?_toArray, ChannelInteraction.toRaw_msg, List.push_toArray, List.cons_append,
    List.nil_append, pushed_msg, Vector.toArray_map, pulled_msg]
  rw [vec_ten, vec_ten, vec_ten]
  simp [Expression.eval]

/-- The verifier's two messages, on any row: the initial state pushed, the final state pulled. -/
theorem verifier_messages (prog : Program) (env : Environment K) :
    ((leanIsaEnsemble prog).verifierTable.operations.interactionValues env).map
        (fun i ↦ (i.channel.name, i.msg)) =
      [(StatePush.name, #[1, 1]), (StatePull.name, #[prog.finalPc, 1])] := by
  rw [Air.Flat.Component.interactionsValues_eq]
  simp [Operations.interactionValues, Air.Flat.Component.rowOperations, leanIsaEnsemble,
    leanIsaVerifier, Ensemble.verifierTable, circuit_norm, AbstractInteraction.eval,
    explicit_provable_type, StatePush, StatePull, -BitVec.reduceNeg,
    ProvableStruct.componentsToElements, ProvableStruct.toComponents, toComponents]

/-! ## The opcode tables -/

/-- Opcode table `j` of a witness. -/
abbrev opTable (w : EnsembleWitness (leanIsaEnsemble prog)) (j : Fin 6) : Air.Flat.Table K :=
  tableAt w ⟨j, by omega⟩

/-- Opcode table `j` of a witness runs the ensemble's opcode component `j`. -/
theorem opTable_component (w : EnsembleWitness (leanIsaEnsemble prog)) (j : Fin 6) :
    (opTable w j).component = opcodeComponent j := by
  rw [opTable, tableAt_component]
  fin_cases j <;> rfl

/-- Every message coordinate of an opcode table reads within its width. -/
theorem opcode_withinWidth : ∀ j : Fin 6, ∀ ai ∈ (opcodeComponent j).rowOperations.interactions,
    ∀ e ∈ ai.msg.toList, e.WithinWidth (opcodeComponent j).width := by
  decide +kernel

/-- The tuples of two lists side by side. -/
private theorem tuplesOn_append (l₁ l₂ : List (Interaction K)) (side : Side) :
    tuplesOn (l₁ ++ l₂) side = tuplesOn l₁ side ++ tuplesOn l₂ side := by
  simp only [tuplesOn, List.map_append, List.filter_append]

/-- The tuples of a list built by rows are the rows' tuples. -/
private theorem tuplesOn_flatMap {α : Type} (l : List α) (f : α → List (Interaction K))
    (side : Side) :
    tuplesOn (l.flatMap f) side = l.flatMap fun a ↦ tuplesOn (f a) side := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    rw [List.flatMap_cons, List.flatMap_cons, ← ih]
    simp only [tuplesOn, List.map_append, List.filter_append]

/-- A component whose messages read within its width flushes the same tuples on a row as on the
row's first `width` cells. -/
private theorem tuplesOn_truncate (c : Component K)
    (hw : ∀ ai ∈ c.rowOperations.interactions, ∀ e ∈ ai.msg.toList, e.WithinWidth c.width)
    (row : Array K) (r : Fin c.width → K) (hr : ∀ i : Fin c.width, row[(i : ℕ)]?.getD 0 = r i)
    (data : ProverData K) (side : Side) :
    tuplesOn (c.operations.interactionValues (Environment.fromArray row data)) side =
      tuplesOn (c.operations.interactionValues (Environment.fromArray (Array.ofFn r) data)) side
          := by
  have hrow : (Array.ofFn fun i : Fin c.width ↦ row[(i : ℕ)]?.getD 0) = Array.ofFn r :=
    congrArg Array.ofFn (funext hr)
  rw [Air.Flat.Component.interactionsValues_eq, Air.Flat.Component.interactionsValues_eq]
  simp only [tuplesOn, Operations.interactionValues, List.map_map]
  congr 2
  refine List.map_congr_left fun ai hai ↦ ?_
  have hm : ai.msg.map (fun x ↦ Expression.eval (Environment.fromArray row data) x) =
      ai.msg.map (fun x ↦ Expression.eval (Environment.fromArray (Array.ofFn r) data) x) := by
    refine Vector.ext fun k hk ↦ ?_
    rw [Vector.getElem_map, Vector.getElem_map, Expression.eval_fromArray_truncate row data
      (hw ai hai _ (Vector.mem_toList_iff.mpr (Vector.getElem_mem hk))), hrow]
  simp only [Function.comp_apply, busView, AbstractInteraction.eval, hm]
  rfl

/-- On a row of its width, an opcode table flushes, on one side, its flushes of that side
evaluated on the row. -/
private theorem tuplesOn_opcode_row (j : Fin 6) (r : Fin (opcodeComponent j).width → K)
    (data : ProverData K) (side : Side) :
    tuplesOn ((opcodeComponent j).operations.interactionValues
        (Environment.fromArray (Array.ofFn r) data)) side =
      ((opcodeTable j).flushes.filter fun f ↦ decide (sideOf f.1 = side)).map
        fun f ↦ f.2.map (·.eval r) := by
  have h := toM3_flushes_eq (opcodeComponent j) channelSep channelDir counted r data
  have hv : (((opcodeComponent j).operations.interactionValues
      (Environment.fromArray (Array.ofFn r) data)).map busView) =
      ((opcodeTable j).flushes.map fun f ↦ (sideOf f.1, f.2.map (·.eval r))) := by
    have := congrArg (List.map fun p : Arithmetization.Direction × Vector K 16 ↦
      (sideOf p.1, p.2)) h
    simp only [List.map_map] at this
    exact this.symm
  rw [tuplesOn, hv, List.filter_map]
  simp only [List.map_map, Function.comp_def]

/-- Swapping the two loops of a product enumeration permutes it. -/
private theorem perm_flatMap_swap {α β γ : Type} (l₁ : List α) (l₂ : List β) (g : α → β → γ) :
    (l₁.flatMap fun a ↦ l₂.map (g a)).Perm (l₂.flatMap fun b ↦ l₁.map fun a ↦ g a b) := by
  rw [← Multiset.coe_eq_coe, ← Multiset.coe_bind, ← Multiset.coe_bind]
  simp only [← Multiset.map_coe]
  exact Multiset.bind_map_comm _ _

/-- A list of known length, enumerated by its indices. -/
private theorem flatMap_eq_finRange {α β : Type} (l : List α) {n : ℕ} (hn : l.length = n)
    (g : α → List β) :
    l.flatMap g =
      (List.finRange n).flatMap fun x : Fin n ↦ g (l[x.val]'(by rw [hn]; exact x.isLt)) := by
  subst hn
  conv_lhs => rw [← List.map_getElem_finRange l]
  rw [List.flatMap_map]

/-! ## A stack and a witness that agree -/

section Agrees

variable (F : FlockSpec) (s : Sizes) (q : Column (leanIsaμ prog s))

/-- A stack and a witness agree: the opcode tables have the announced heights and, within their
widths, the stack's rows; the memory and bytecode blocks are the stack's. -/
structure Agrees (w : EnsembleWitness (leanIsaEnsemble prog)) : Prop where
  /-- Opcode table `j` has the announced `rows_j` rows, its executed ones. -/
  length : ∀ j : Fin 6, (opTable w j).table.length = s.rows j
  /-- Its cells within its width are the stack's executed row. -/
  cells : ∀ (j : Fin 6) (x : Fin (s.rows j)) (i : Fin (opcodeComponent j).width),
    cellOf (opTable w j) x i =
      (leanIsaInstance F prog s).row q (opIdx j) (Fin.castLE (s.rows_le j) x) i
  /-- The memory block's rows are the stack's. -/
  memRows : memBlockRows w = memBlockRowsOf F prog s q
  /-- The bytecode block's rows are the stack's. -/
  bytecodeRows : bytecodeBlockRows w = bytecodeBlockRowsOf F prog s q

variable {F s q}

/-- Opcode table `j` flushes, on one side, its flushes of that side on every executed row of the
stack. -/
theorem tuplesOn_opTable {w : EnsembleWitness (leanIsaEnsemble prog)} (h : Agrees F s q w)
    (j : Fin 6) (side : Side) :
    tuplesOn (opTable w j).interactions side =
      (List.finRange (s.rows j)).flatMap fun x ↦
        ((opcodeTable j).flushes.filter fun f ↦ decide (sideOf f.1 = side)).map fun f ↦
          f.2.map (·.eval ((leanIsaInstance F prog s).row q (opIdx j) (Fin.castLE (s.rows_le j) x))) := by
  rw [Air.Flat.Table.interactions, tuplesOn_flatMap, flatMap_eq_finRange _ (h.length j)]
  refine List.flatMap_congr fun x _ ↦ ?_
  rw [Air.Flat.Table.environment, opTable_component]
  refine (tuplesOn_truncate (opcodeComponent j) (opcode_withinWidth j) _
    ((leanIsaInstance F prog s).row q (opIdx j) (Fin.castLE (s.rows_le j) x)) (fun i ↦ ?_) _
      side).trans
    (tuplesOn_opcode_row j _ _ side)
  rw [← h.cells j x i, cellOf, List.getElem?_eq_getElem]
  rfl

/-! ## The boundary blocks -/

/-- A boundary block's coordinates, the separator first, are the tuple of the rest. -/
private theorem coords_coordCell (I : M3Instance) {κ : ℕ} (σ : K) (rest : List (Coord I.toShape κ))
    (q : Column I.μ) (x : Fin (2 ^ κ)) :
    (coords (.const σ :: rest)).map (fun co ↦ I.coordCell q co x) =
      tupleOf σ (rest.map fun co ↦ I.coordCell q co x).toArray := by
  apply Vector.ext
  intro k hk
  simp only [coords, tupleOf, Vector.getElem_map, Vector.getElem_ofFn]
  rcases k with _ | k
  · rfl
  · simp only [List.getD_cons_succ, Nat.add_one_ne_zero, ite_false, Nat.add_sub_cancel,
      List.getElem?_toArray, List.getElem?_map]
    by_cases hr : k < rest.length
    · rw [List.getD_eq_getElem _ _ hr, List.getElem?_eq_getElem hr]
      rfl
    · rw [List.getD_eq_default _ _ (by omega), List.getElem?_eq_none (by omega)]
      rfl

variable (F : FlockSpec) (s : Sizes) (q : Column (leanIsaμ prog s))

/-- The memory columns' cells of row `x`: the three limbs. -/
abbrev memLimbs (x : Fin (2 ^ s.logMem)) : List K :=
  [cell F prog s q (memCol 0) x, cell F prog s q (memCol 1) x, cell F prog s q (memCol 2) x]

/-- The program's entry at slot `i`, its eight coordinates. -/
abbrev entryList (i : Fin (2 ^ prog.logSize)) : List K :=
  (List.finRange 8).map fun k ↦ (entry (prog.code i))[k]

/-- The push side's boundary tuples: the initial state, the memory seed, the bytecode seed. -/
theorem boundaryTuples_push :
    (leanIsaInstance F prog s).boundaryTuples q .push =
      [tupleOf (gpow 0) #[1, 1]] ++
      ((List.finRange (2 ^ s.logMem)).map fun x : Fin (2 ^ s.logMem) ↦
        tupleOf (gpow 1) (#[gpow x, 1] ++ (memLimbs F s q x).toArray)) ++
      ((List.finRange (2 ^ prog.logSize)).map fun i : Fin (2 ^ prog.logSize) ↦
        tupleOf (gpow 2) (#[gpow i, 1] ++ (entryList i).toArray)) := by
  simp only [M3Instance.boundaryTuples, boundary, List.filter_cons, List.filter_nil,
    reduceCtorEq, decide_true, decide_false, ite_true, Bool.false_eq_true, ite_false,
    List.flatMap_cons, List.flatMap_nil, List.append_nil, List.append_assoc]
  refine congrArg₂ (fun a b : List (Vector K 16) ↦ a ++ b) ?_
    (congrArg₂ (fun a b : List (Vector K 16) ↦ a ++ b) ?_ ?_)
  · rw [show List.finRange (2 ^ 0) = [0] from rfl, List.map_singleton]
    refine congrArg (· :: []) ((coords_coordCell (leanIsaInstance F prog s) _ _ q 0).trans ?_)
    rfl
  · refine List.map_congr_left fun x _ ↦ (coords_coordCell (leanIsaInstance F prog s) _ _ q
        x).trans ?_
    simp [M3Instance.coordCell, idxColumn, powersTable, Vector.get_ofFn]
    rfl
  · refine List.map_congr_left fun i _ ↦ (coords_coordCell (leanIsaInstance F prog s) _ _ q
        i).trans ?_
    have hl : ((Coord.known (idxColumn prog.logSize) :: Coord.const 1 ::
        (List.finRange 8).map fun k ↦ (Coord.known (entryColumn prog k) :
          Coord (shape prog s) prog.logSize)).map
        fun co ↦ (leanIsaInstance F prog s).coordCell q co i) = gpow i :: 1 :: entryList i := by
      simp only [List.map_cons, List.map_map]
      refine congrArg₂ _ (Vector.get_ofFn _ _) (congrArg _ (List.map_congr_left fun k _ ↦ ?_))
      exact Vector.get_ofFn _ _
    exact (congrArg (fun l : List K ↦ tupleOf (gpow 2) l.toArray) hl).trans rfl

/-- The pull side's boundary tuples: the final state, the memory finalize, the bytecode finalize. -/
theorem boundaryTuples_pull :
    (leanIsaInstance F prog s).boundaryTuples q .pull =
      [tupleOf (gpow 0) #[prog.finalPc, 1]] ++
      ((List.finRange (2 ^ s.logMem)).map fun x : Fin (2 ^ s.logMem) ↦
        tupleOf (gpow 1) (#[gpow x, cell F prog s q (memCol 3) x] ++ (memLimbs F s q x).toArray)) ++
      ((List.finRange (2 ^ prog.logSize)).map fun i : Fin (2 ^ prog.logSize) ↦
        tupleOf (gpow 2) (#[gpow i, cell F prog s q bfcntCol i] ++ (entryList i).toArray)) := by
  simp only [M3Instance.boundaryTuples, boundary, List.filter_cons, List.filter_nil,
    reduceCtorEq, decide_true, decide_false, ite_true, Bool.false_eq_true, ite_false,
    List.flatMap_cons, List.flatMap_nil, List.append_nil, List.append_assoc]
  refine congrArg₂ (fun a b : List (Vector K 16) ↦ a ++ b) ?_
    (congrArg₂ (fun a b : List (Vector K 16) ↦ a ++ b) ?_ ?_)
  · rw [show List.finRange (2 ^ 0) = [0] from rfl, List.map_singleton]
    refine congrArg (· :: []) ((coords_coordCell (leanIsaInstance F prog s) _ _ q 0).trans ?_)
    rfl
  · refine List.map_congr_left fun x _ ↦ (coords_coordCell (leanIsaInstance F prog s) _ _ q
        x).trans ?_
    simp [M3Instance.coordCell, idxColumn, powersTable, Vector.get_ofFn]
    rfl
  · refine List.map_congr_left fun i _ ↦ (coords_coordCell (leanIsaInstance F prog s) _ _ q
        i).trans ?_
    have hl : ((Coord.known (idxColumn prog.logSize) :: Coord.committed bfcntCol rfl ::
        (List.finRange 8).map fun k ↦ (Coord.known (entryColumn prog k) :
          Coord (shape prog s) prog.logSize)).map
        fun co ↦ (leanIsaInstance F prog s).coordCell q co i) =
          gpow i :: cell F prog s q bfcntCol i :: entryList i := by
      simp only [List.map_cons, List.map_map]
      refine congrArg₂ _ (Vector.get_ofFn _ _) (congrArg₂ _ rfl (List.map_congr_left fun k _ ↦ ?_))
      exact Vector.get_ofFn _ _
    exact (congrArg (fun l : List K ↦ tupleOf (gpow 2) l.toArray) hl).trans rfl
/-- How the bus views the six channels' messages. -/
private theorem nameView_six (m : Array K) :
    nameView (StatePush.name, m) = (.push, tupleOf (gpow 0) m) ∧
    nameView (StatePull.name, m) = (.pull, tupleOf (gpow 0) m) ∧
    nameView (MemPush.name, m) = (.push, tupleOf (gpow 1) m) ∧
    nameView (MemPull.name, m) = (.pull, tupleOf (gpow 1) m) ∧
    nameView (BytecodePush.name, m) = (.push, tupleOf (gpow 2) m) ∧
    nameView (BytecodePull.name, m) = (.pull, tupleOf (gpow 2) m) := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- The tuples of a push and a pull message, on each side. -/
private theorem tuplesOn_pair {l : List (Interaction K)} {nPull nPush : String}
    {mPull mPush : Array K} {σ : K}
    (h : l.map (fun i ↦ (i.channel.name, i.msg)) = [(nPush, mPush), (nPull, mPull)])
    (hu : nameView (nPush, mPush) = (.push, tupleOf σ mPush))
    (hp : nameView (nPull, mPull) = (.pull, tupleOf σ mPull)) (side : Side) :
    tuplesOn l side = [tupleOf σ (if side = .push then mPush else mPull)] := by
  rw [tuplesOn_eq, h]
  cases side <;> simp [hu, hp]

variable {F s q}

/-- The memory block flushes its seed and finalize tuples, on the stack's memory columns. -/
theorem tuplesOn_memBlock {w : EnsembleWitness (leanIsaEnsemble prog)} (h : Agrees F s q w)
    (side : Side) :
    tuplesOn (tableAt w 6).interactions side =
      (List.finRange (2 ^ s.logMem)).map fun x : Fin (2 ^ s.logMem) ↦
        tupleOf (gpow 1) ((if side = .push then #[gpow x, 1]
          else #[gpow x, cell F prog s q (memCol 3) x]) ++ (memLimbs F s q x).toArray) := by
  rw [Air.Flat.Table.interactions, tuplesOn_flatMap,
    show (tableAt w 6).table = memBlockRowsOf F prog s q from h.memRows, memBlockRowsOf,
    List.ofFn_eq_map, List.flatMap_map, tableAt_component]
  rw [← List.flatMap_pure_eq_map]
  refine List.flatMap_congr fun x _ ↦ ?_
  refine (tuplesOn_pair (memTable_messages _ _ _ _ _ (tableAt w 6).data)
    (nameView_six _).2.2.1 (nameView_six _).2.2.2.1 side).trans ?_
  cases side <;> rfl

/-- The bytecode block flushes the program's seed and finalize tuples, with the stack's finalize
counts. -/
theorem tuplesOn_bytecodeBlock {w : EnsembleWitness (leanIsaEnsemble prog)} (h : Agrees F s q w)
    (side : Side) :
    tuplesOn (tableAt w 7).interactions side =
      (List.finRange (2 ^ prog.logSize)).map fun i : Fin (2 ^ prog.logSize) ↦
        tupleOf (gpow 2) ((if side = .push then #[gpow i, 1]
          else #[gpow i, cell F prog s q bfcntCol i]) ++ (entryList i).toArray) := by
  rw [Air.Flat.Table.interactions, tuplesOn_flatMap,
    show (tableAt w 7).table = bytecodeBlockRowsOf F prog s q from h.bytecodeRows,
    bytecodeBlockRowsOf, List.ofFn_eq_map, List.flatMap_map, tableAt_component]
  rw [← List.flatMap_pure_eq_map]
  refine List.flatMap_congr fun i _ ↦ ?_
  refine (tuplesOn_pair (bytecodeTable_messages _ _ _ _ _ _ _ _ _ _ (tableAt w 7).data)
    (nameView_six _).2.2.2.2.1 (nameView_six _).2.2.2.2.2 side).trans ?_
  cases side <;> simp [entryList, List.finRange_succ]

/-- The verifier flushes the initial state and pulls the final state. -/
theorem tuplesOn_verifier (w : EnsembleWitness (leanIsaEnsemble prog)) (side : Side) :
    tuplesOn w.verifierTable.interactions side =
      [tupleOf (gpow 0) (if side = .push then #[1, 1] else #[prog.finalPc, 1])] := by
  rw [Air.Flat.Table.interactions, tuplesOn_flatMap]
  simp only [Air.Flat.EnsembleWitness.verifierTable, List.flatMap_cons, List.flatMap_nil,
    List.append_nil]
  exact tuplesOn_pair (verifier_messages prog _) (nameView_six _).1 (nameView_six _).2.1 side

/-- The instance's tables: the three column groups, then the six opcode tables. -/
private theorem finRange_nine : List.finRange 9 = [0, 1, 2] ++ (List.finRange 6).map opIdx := by
  decide

/-- The witness's tables, in order. -/
theorem tables_eq (w : EnsembleWitness (leanIsaEnsemble prog)) :
    w.tables = (List.finRange 8).map (tableAt w) := by
  apply List.ext_getElem
  · rw [List.length_map, List.length_finRange, ← w.same_length]
    rfl
  · intro n h₁ h₂
    rw [List.getElem_map, List.getElem_finRange]
    rfl

/-- Filtering a mapped list before a loop is filtering and mapping inside it. -/
private theorem filter_map_flatMap {α β γ : Type} (l : List α) (f : α → β) (p : β → Bool)
    (g : β → List γ) : ((l.map f).filter p).flatMap g = (l.filter (p ∘ f)).flatMap (g ∘ f) := by
  rw [List.filter_map, List.flatMap_map]
  rfl

/-- The instance's flush tuples, table by table. -/
private theorem flushTuples_eq (side : Side) :
    (leanIsaInstance F prog s).flushTuples q side =
      (List.finRange 9).flatMap fun j ↦ ((flushes j).filter fun f ↦ decide (f.1 = side)).flatMap
        fun f ↦ ((leanIsaInstance F prog s).executed j).map fun x ↦
          f.2.map fun P ↦ P.eval ((leanIsaInstance F prog s).row q j x) := rfl

/-- The flushes of opcode table `j`, on one side: a permutation of what the table's rows emit
there. -/
private theorem flushTuples_opIdx_perm {w : EnsembleWitness (leanIsaEnsemble prog)}
    (h : Agrees F s q w)
    (j : Fin 6) (side : Side) :
    (((flushes (opIdx j)).filter fun f ↦ decide (f.1 = side)).flatMap
        fun f ↦ ((leanIsaInstance F prog s).executed (opIdx j)).map fun x ↦
          f.2.map fun P ↦ P.eval ((leanIsaInstance F prog s).row q (opIdx j) x)).Perm
      (tuplesOn (opTable w j).interactions side) := by
  have he : (leanIsaInstance F prog s).executed (opIdx j) =
      (List.finRange (s.rows j)).map (Fin.castLE (s.rows_le j)) :=
    M3Instance.executed_eq _ _
  rw [tuplesOn_opTable h]
  refine List.Perm.trans (List.Perm.of_eq ?_) (perm_flatMap_swap _ _ _)
  show (((opcodeTable j).flushes.map fun f ↦ (sideOf f.1, f.2)).filter _).flatMap _ = _
  refine (filter_map_flatMap _ _ _ _).trans (List.flatMap_congr fun f _ ↦ ?_)
  exact (congrArg (List.map _) he).trans List.map_map

/-- **The bus, read off a stack, is the bus of a witness that agrees with it**: on each side, the
instance's tuples (the opcode tables' flushes and the six boundary blocks) are a permutation of
the tuples the witness's interactions flush. -/
theorem tuples_perm {w : EnsembleWitness (leanIsaEnsemble prog)} (h : Agrees F s q w)
    (side : Side) : ((leanIsaInstance F prog s).tuples q side).Perm (sideTuples w side) := by
  have hb : (leanIsaInstance F prog s).boundaryTuples q side =
      tuplesOn w.verifierTable.interactions side ++ tuplesOn (tableAt w 6).interactions side ++
        tuplesOn (tableAt w 7).interactions side := by
    rw [tuplesOn_verifier, tuplesOn_memBlock h, tuplesOn_bytecodeBlock h]
    cases side
    · rw [boundaryTuples_push]
      simp
    · rw [boundaryTuples_pull]
      simp
  have hf : ((leanIsaInstance F prog s).flushTuples q side).Perm
      ((List.finRange 6).flatMap fun j ↦ tuplesOn (opTable w j).interactions side) := by
    rw [flushTuples_eq, finRange_nine, List.flatMap_append, List.flatMap_map]
    have h0 : ([0, 1, 2] : List (Fin 9)).flatMap (fun j ↦
        ((flushes j).filter fun f ↦ decide (f.1 = side)).flatMap fun f ↦
          ((leanIsaInstance F prog s).executed j).map fun x ↦
            f.2.map fun P ↦ P.eval ((leanIsaInstance F prog s).row q j x)) = [] := rfl
    rw [h0, List.nil_append]
    exact List.Perm.flatMap_left _ fun j _ ↦ flushTuples_opIdx_perm h j side
  rw [M3Instance.tuples, hb, sideTuples, EnsembleWitness.interactions,
    EnsembleWitness.allTables, List.flatMap_cons, tables_eq, List.flatMap_map,
    show List.finRange 8 = (List.finRange 6).map (fun j : Fin 6 ↦ (⟨j, by omega⟩ : Fin 8)) ++
      [6, 7] by decide, List.flatMap_append, List.flatMap_map, tuplesOn_append, tuplesOn_append,
    tuplesOn_flatMap,
    tuplesOn_flatMap]
  refine (hf.append_right _).trans ?_
  rw [List.perm_iff_count]
  intro v
  simp only [List.count_append, List.flatMap_cons, List.flatMap_nil, List.append_nil, opTable]
  omega

end Agrees

end

end LeanVM.Protocol.LeanIsa
