module

public import LeanVMCircuits.Rec.RecParts
public import LeanVMCircuits.Rec.BusBalance
public import LeanVMCircuits.Rec.StmtFirst

@[expose] public section

/-!
The AIR link: the recursion machine's AIR claims on a committed witness of a circuit give the model's circuit satisfied.

A committed witness (`Witness`) has each table's height and each row's columns. Row `z` of an owned table (`EMUL`, `EXK`, `HASH`, `SPLIT`, `CAST`) is the builder's row `z` of that table, its slot `i` carrying the limbs the table's forms (`Tables`) give its columns; the public table's row `z` is the circuit's public row `z`, its one slot carrying the row's four value columns. Every slot of every row up to the table's height (padding included) is on the bus with its key (`SlotKey::new`), and its `next` is the following slot of its wire class in table, row and slot order, the class's first after its last (`classNext`, `FixedColumns::of`); a padding slot is a class of its own, whose `next` is its own key.

The AIR's claims (`Claims`): the layout's and rows' (`RowClaims`: every table holds its rows below `2^32` rows, every row of the circuit satisfies its table (`SPLIT`'s identities, `HASH`'s packed BLAKE2s witness and mux bit, which is `HashRow`; the other tables have no identities, `Table::identities`), and the public columns carry each public row's constant or statement word), and the bus balances (`Balanced`). The assignment the witness carries (`assign`) gives each wire the limbs of the first slot of its class. `sat_of_claims`: the claims give `Model.Sat` at that assignment, by the copy argument (`copy_argument`) and the tables' rows. `claims_of_sat`: conversely, every satisfied circuit within the layout's bounds has a witness meeting the claims, so the claims are satisfiable exactly when the circuit is.

The bus's balance is derived from its product check. `ProductClaim` at a draw `(β, A)`: the products of `β + fp_A(t)` over the pulls and over the pushes agree, the bus GKR's root claims, which `bus::verify_balance` holds equal. Off the draw event `busDraws` (the draws at which an unbalanced bus's products agree) it gives the bus balanced (`bus_of_product`), and `busDraws_card` bounds that event by `4n/|E|` of the draws (`bus_event`, `bus_balance_sound`). Over outcomes, `busBad` is where the outcome's draw is in its committed witness's draw event, at most `4N/|E|` of the outcomes when the draw is uniform and made after the commitment (`busBad_frac`, a lens as `Bind.card_lens` takes). The honest witness meets the product claim at every draw (`product_honest`).

`hair_of_air` derives `RecParts.hrec`'s premise `hair` from `ChecksGiveRows` and each child's assignment being its committed witness's, for the parts with each child's collision event grown by its AIR event `airBad`: the constraint batch's event `batchBad`, left abstract, and the bus's `busBad`. `ChecksGiveRows` is what remains: where the parent's circuit is satisfied, every check's inputs are true, no compression collides, the parent's verifier reads statement `st` and off `batchBad`, the child's committed witness meets `RowClaims` at `st` and its product claim at the outcome's draw. `RecParts.inOk` is abstract, so nothing more of that implication follows from the check certificates. `tree_sound_air` is `tree_sound_parts` with it, its bound adding each child's `batchBad` and `busBad` fractions.

The Rust circuit orders the public rows statement first (`Builder::statement_first`), so that the statement's words sit on the public table's first rows (`FixedColumns::public_values`), and the model keeps building order. The Rust verifier's public columns, keys and bus roots are the reordered circuit's, `Model.stmtFirst`, which has the same `Model.Sat` (`Sat.pub` reads the public rows as a set, `Model.sat_stmtFirst`), so `tree_sound_air` states each child's side at `stmtFirst` and gives the replayed circuit satisfied; it requires only that each statement word be exposed once, at its index, which `expose`'s counter gives, so that the Rust public column's row `z` is `srcVal` of its row.
-/

namespace LeanVMCircuits.Rec.AirLink

open LeanVMCircuits.Rec Model Finset Classical

/-! The tables as the AIR lays them out. -/

/-- A table's slots' forms: an owned table's from `Tables`, the public table's one slot its four value columns. -/
def forms : Table → List (List Form)
  | .emul => Rec.emul
  | .exk => Rec.exk
  | .hash => Rec.hash
  | .split => Rec.split
  | .cast => Rec.cast
  | .pub => [dSlot 0]

theorem forms_length (T : Table) : (forms T).length = T.nSlots := by
  cases T <;> rfl

/-- What a row's columns satisfy: `HASH`'s a packed BLAKE2s witness with the row's ports and a Boolean mux bit, `SPLIT`'s its identities, the other tables' nothing. -/
def holds : Table → (ℕ → K) → Prop
  | .hash => HashRow
  | .split => fun col => ∀ id ∈ splitIdentities, id.eval col = 0
  | _ => fun _ => True

/-- A table's rows, a wire per slot: an owned table's the circuit's, the public table's each public row's wire. -/
def rowsOf (s : State) : Table → Array (List ℕ)
  | .emul => s.emul
  | .exk => s.exk
  | .hash => s.hash
  | .split => s.split
  | .cast => s.cast
  | .pub => s.pub.map fun p => [p.1]

/-- Reordering the public rows keeps every table's number of rows. -/
theorem size_rowsOf_stmtFirst (s : State) (T : Table) : (rowsOf (stmtFirst s) T).size = (rowsOf s T).size := by
  cases T <;> first | rfl | simp only [rowsOf, Array.size_map, size_stmtFirst_pub]

/-- `Table::first_slot`: a table's first slot among all tables' slots. -/
def firstSlot : Table → ℕ
  | .emul => 0
  | .exk => 4
  | .hash => 8
  | .split => 24
  | .cast => 89
  | .pub => 97

theorem firstSlot_inj {T T' : Table} {i i' : ℕ} (hi : i < T.nSlots) (hi' : i' < T'.nSlots)
    (h : firstSlot T + i = firstSlot T' + i') : T = T' ∧ i = i' := by
  cases T <;> cases T' <;> simp only [firstSlot, Table.nSlots] at hi hi' h <;>
    first | exact ⟨rfl, by omega⟩ | exact absurd h (by omega)

/-! The committed witness and the bus. -/

/-- A committed witness: each table's height and each row's columns. The public table's columns are its four value columns, which the verifier computes from the circuit and the statement. -/
structure Witness where
  height : Table → ℕ
  cols : Table → ℕ → ℕ → K

/-- A slot of the bus: its table, row and slot. -/
abbrev Slot := Table × ℕ × ℕ

/-- Every slot of every table's rows up to its height, in table, row and slot order. -/
def slots (w : Witness) : List Slot :=
  Table.all.flatMap fun T => (List.range (w.height T)).flatMap fun z => (List.range T.nSlots).map fun i => (T, z, i)

/-- A slot's key (`SlotKey::new`). -/
def key (e : Slot) : ℕ := slotKey (firstSlot e.1 + e.2.2) e.2.1

/-- The limbs a slot carries: its table's forms on its row's columns. -/
noncomputable def carried (w : Witness) (e : Slot) : Fin 4 → K := fun i => limbs (forms e.1) e.2.2 (w.cols e.1 e.2.1) i

/-- A slot's wire. -/
def wireOf (s : State) (e : Slot) : ℕ := ((rowsOf s e.1).getD e.2.1 []).getD e.2.2 0

/-- Wires held equal: the equivalence the unions generate, whose classes are the builder's (`Builder::find`). -/
def Joined (s : State) : ℕ → ℕ → Prop := Relation.EqvGen fun a b => (a, b) ∈ s.unions

/-- A wire's class: the least wire held equal to it. -/
noncomputable def wireClass (s : State) (x : ℕ) : ℕ :=
  Nat.find (⟨x, Relation.EqvGen.refl x⟩ : ∃ y, Joined s x y)

/-- A slot's class: its wire's (even) on a row of the circuit, its own (odd) on a padding row. -/
noncomputable def slotClass (s : State) (e : Slot) : ℕ :=
  if e.2.1 < (rowsOf s e.1).size then 2 * wireClass s (wireOf s e) else 2 * key e + 1

/-- The bus balances: each slot pulls its key and limbs and pushes its `next` slot's key (`classNext`) and its limbs, and the pulls and pushes balance. -/
def BusBalances (s : State) (w : Witness) : Prop :=
  Balanced (fun i : Fin (slots w).length => key (slots w)[i]) (classNext fun i => slotClass s (slots w)[i])
    (fun i => carried w (slots w)[i])

/-- The AIR's claims on a committed witness `w` of circuit `s` at statement `st` but the bus's: the layout and the rows. -/
structure RowClaims (s : State) (st : ℕ → Fin 4 → K) (w : Witness) : Prop where
  /-- Every table holds its rows, below `2^32` rows (`RecLayout::new`, `MAX_TAU`). -/
  fits : ∀ T, (rowsOf s T).size ≤ w.height T ∧ w.height T ≤ 2 ^ 32
  /-- Every row of the circuit satisfies its table. -/
  tables : ∀ T, ∀ z < (rowsOf s T).size, holds T (w.cols T z)
  /-- The public columns carry each public row's constant or statement word. -/
  pub : ∀ z (hz : z < s.pub.size) (i : Fin 4), w.cols .pub z i = srcVal st s.pub[z].2 i

/-- The AIR's claims on a committed witness `w` of circuit `s` at statement `st`: the rows', and the bus balances. -/
structure Claims (s : State) (st : ℕ → Fin 4 → K) (w : Witness) : Prop extends RowClaims s st w where
  /-- The bus balances. -/
  bus : BusBalances s w

/-- The assignment the witness carries: each wire's value the limbs of the first slot of its class, zero when its class has none. -/
noncomputable def assign (s : State) (w : Witness) : Val := fun x =>
  match (slots w).find? (fun e => decide (slotClass s e = 2 * wireClass s x)) with
  | some e => carried w e
  | none => 0

/-! Classes. -/

theorem wireClass_spec (s : State) (x : ℕ) : Joined s x (wireClass s x) :=
  Nat.find_spec (⟨x, Relation.EqvGen.refl x⟩ : ∃ y, Joined s x y)

theorem wireClass_eq_iff (s : State) (x y : ℕ) : wireClass s x = wireClass s y ↔ Joined s x y := by
  constructor
  · intro h
    have hy := wireClass_spec s y
    rw [← h] at hy
    exact Relation.EqvGen.trans _ _ _ (wireClass_spec s x) (Relation.EqvGen.symm _ _ hy)
  · intro h
    refine le_antisymm (Nat.find_min' _ ?_) (Nat.find_min' _ ?_)
    · exact Relation.EqvGen.trans _ _ _ h (wireClass_spec s y)
    · exact Relation.EqvGen.trans _ _ _ (Relation.EqvGen.symm _ _ h) (wireClass_spec s x)

theorem assign_class {s : State} {w : Witness} {x y : ℕ} (h : wireClass s x = wireClass s y) :
    assign s w x = assign s w y := by
  unfold assign
  rw [h]

/-- A satisfying assignment gives wires held equal the same value. -/
theorem joined_val {st : ℕ → Fin 4 → K} {s : State} {val : Val} (h : Sat st s val) {a b : ℕ} (hab : Joined s a b) :
    val a = val b := by
  induction hab with
  | rel x y hxy => exact h.unions (x, y) hxy
  | refl => rfl
  | symm _ _ _ ih => exact ih.symm
  | trans _ _ _ _ _ ih1 ih2 => exact ih1.trans ih2

/-! The bus's keys are distinct. -/

theorem mem_slots {w : Witness} {e : Slot} : e ∈ slots w ↔ e.2.1 < w.height e.1 ∧ e.2.2 < e.1.nSlots := by
  obtain ⟨T, z, i⟩ := e
  simp only [slots, List.mem_flatMap, List.mem_map, List.mem_range, Prod.mk.injEq]
  constructor
  · rintro ⟨T', -, z', hz', i', hi', rfl, rfl, rfl⟩
    exact ⟨hz', hi'⟩
  · rintro ⟨hz, hi⟩
    exact ⟨T, by cases T <;> simp [Table.all], z, hz, i, hi, rfl, rfl, rfl⟩

theorem pairwise_disjoint {α β : Type} {l : List α} {f : α → List β} (hl : l.Nodup)
    (hf : ∀ a b, a ≠ b → ∀ x ∈ f a, x ∉ f b) : l.Pairwise fun a b => List.Disjoint (f a) (f b) :=
  hl.imp fun {a b} hne x hx hy => hf a b hne x hx hy

theorem slots_nodup (w : Witness) : (slots w).Nodup := by
  have hrow : ∀ (T : Table) (z : ℕ), ((List.range T.nSlots).map fun i => ((T, z, i) : Slot)).Nodup :=
    fun T z => List.nodup_range.map fun a b h => by simpa using h
  have htab : ∀ T : Table, ((List.range (w.height T)).flatMap fun z =>
      (List.range T.nSlots).map fun i => ((T, z, i) : Slot)).Nodup := by
    intro T
    refine List.nodup_flatMap.mpr ⟨fun z _ => hrow T z, pairwise_disjoint List.nodup_range ?_⟩
    intro a b hne x hx hy
    simp only [List.mem_map, List.mem_range] at hx hy
    obtain ⟨i, -, rfl⟩ := hx
    obtain ⟨j, -, hj⟩ := hy
    simp only [Prod.mk.injEq] at hj
    exact hne hj.2.1.symm
  refine List.nodup_flatMap.mpr ⟨fun T _ => htab T, pairwise_disjoint (by decide) ?_⟩
  intro a b hne x hx hy
  simp only [List.mem_flatMap, List.mem_map, List.mem_range] at hx hy
  obtain ⟨z, -, i, -, rfl⟩ := hx
  obtain ⟨z', -, j, -, hj⟩ := hy
  simp only [Prod.mk.injEq] at hj
  exact hne hj.1.symm

theorem key_inj {w : Witness} (hfit : ∀ T, w.height T ≤ 2 ^ 32) {e e' : Slot} (he : e ∈ slots w)
    (he' : e' ∈ slots w) (h : key e = key e') : e = e' := by
  obtain ⟨hz, hi⟩ := mem_slots.mp he
  obtain ⟨hz', hi'⟩ := mem_slots.mp he'
  have hp := slotKey_injective (firstSlot e.1 + e.2.2, e.2.1) (firstSlot e'.1 + e'.2.2, e'.2.1)
    (lt_of_lt_of_le hz (hfit _)) (lt_of_lt_of_le hz' (hfit _)) h
  simp only [Prod.mk.injEq] at hp
  obtain ⟨hT, hs⟩ := firstSlot_inj hi hi' hp.1
  obtain ⟨T, z, i⟩ := e
  obtain ⟨T', z', i'⟩ := e'
  simp only at hT hs hp
  rw [hT, hs, hp.2]

theorem key_injective {w : Witness} (hfit : ∀ T, w.height T ≤ 2 ^ 32) :
    Function.Injective fun i : Fin (slots w).length => key (slots w)[i] := by
  intro i j h
  have := key_inj hfit (List.getElem_mem _) (List.getElem_mem _) h
  exact Fin.ext ((slots_nodup w).getElem_inj_iff.mp this)

/-! The claims give the circuit satisfied. -/

/-- Slots of one class carry the same limbs: the copy argument on the balanced bus. -/
theorem copy {s : State} {st : ℕ → Fin 4 → K} {w : Witness} (h : Claims s st w) {e e' : Slot}
    (he : e ∈ slots w) (he' : e' ∈ slots w) (hc : slotClass s e = slotClass s e') : carried w e = carried w e' := by
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem he
  obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem he'
  exact copy_argument (fun i : Fin (slots w).length => key (slots w)[i]) (key_injective fun T => (h.fits T).2)
    (fun i : Fin (slots w).length => slotClass s (slots w)[i]) (fun i => carried w (slots w)[i]) h.bus
    ⟨i, hi⟩ ⟨j, hj⟩ hc

/-- A wire's value is the limbs of every slot of its class. -/
theorem assign_eq {s : State} {st : ℕ → Fin 4 → K} {w : Witness} (h : Claims s st w) {e : Slot} {x : ℕ}
    (he : e ∈ slots w) (hx : slotClass s e = 2 * wireClass s x) : assign s w x = carried w e := by
  unfold assign
  split
  · next e' hf =>
    have hm := List.mem_of_find?_eq_some hf
    have hp := List.find?_some hf
    simp only [decide_eq_true_eq] at hp
    exact copy h hm he (hp.trans hx.symm)
  · next hf =>
    have := List.find?_eq_none.mp hf e he
    simp [hx] at this

theorem slotClass_row {s : State} {T : Table} {z i : ℕ} (hz : z < (rowsOf s T).size) :
    slotClass s (T, z, i) = 2 * wireClass s ((rowsOf s T)[z].getD i 0) := by
  simp [slotClass, wireOf, hz, Array.getD_eq_getD_getElem?]

/-- Every row of the circuit is a row of its table whose slots carry its wires' values. -/
theorem row_sat {s : State} {st : ℕ → Fin 4 → K} {w : Witness} (h : Claims s st w) (T : Table) {z : ℕ}
    (hz : z < (rowsOf s T).size) : RowSat (forms T) (holds T) (assign s w) (rowsOf s T)[z] := by
  refine ⟨w.cols T z, h.tables T z hz, fun i hi k => ?_⟩
  have he : (T, z, i) ∈ slots w :=
    mem_slots.mpr ⟨lt_of_lt_of_le hz (h.fits T).1, by rw [forms_length] at hi; exact hi⟩
  rw [assign_eq h he (slotClass_row hz)]
  rfl

theorem limbs_pub (col : ℕ → K) (i : Fin 4) : limbs (forms .pub) 0 col i = col i := by
  fin_cases i <;> rfl

/-- The AIR's claims on a committed witness give the circuit satisfied at the statement, at the witness's assignment. -/
theorem sat_of_claims {s : State} {st : ℕ → Fin 4 → K} {w : Witness} (h : Claims s st w) :
    Sat st s (assign s w) where
  unions p hp := assign_class ((wireClass_eq_iff s _ _).mpr (Relation.EqvGen.rel _ _ hp))
  emul r hr := by
    obtain ⟨z, hz, rfl⟩ := Array.mem_iff_getElem.mp hr
    exact row_sat h .emul (z := z) hz
  exk r hr := by
    obtain ⟨z, hz, rfl⟩ := Array.mem_iff_getElem.mp hr
    exact row_sat h .exk (z := z) hz
  hash r hr := by
    obtain ⟨z, hz, rfl⟩ := Array.mem_iff_getElem.mp hr
    exact row_sat h .hash (z := z) hz
  split r hr := by
    obtain ⟨z, hz, rfl⟩ := Array.mem_iff_getElem.mp hr
    exact row_sat h .split (z := z) hz
  cast r hr := by
    obtain ⟨z, hz, rfl⟩ := Array.mem_iff_getElem.mp hr
    exact row_sat h .cast (z := z) hz
  pub x src hp := by
    obtain ⟨z, hz, hzeq⟩ := Array.mem_iff_getElem.mp hp
    have hz' : z < (rowsOf s .pub).size := by simpa [rowsOf] using hz
    have he : ((.pub, z, 0) : Slot) ∈ slots w :=
      mem_slots.mpr ⟨lt_of_lt_of_le hz' (h.fits .pub).1, Nat.one_pos⟩
    have hx : slotClass s (.pub, z, 0) = 2 * wireClass s x := by
      rw [slotClass_row hz']
      simp [rowsOf, hzeq]
    funext i
    rw [assign_eq h he hx]
    show limbs (forms .pub) 0 (w.cols .pub z) i = _
    rw [limbs_pub, h.pub z hz i, hzeq]

/-! Non-vacuity: every satisfied circuit within the layout's bounds has a witness meeting the claims. -/

theorem sat_row {st : ℕ → Fin 4 → K} {s : State} {val : Val} (h : Sat st s val) (T : Table) {z : ℕ}
    (hz : z < (rowsOf s T).size) : RowSat (forms T) (holds T) val (rowsOf s T)[z] := by
  cases T
  · exact h.emul _ (Array.getElem_mem hz)
  · exact h.exk _ (Array.getElem_mem hz)
  · exact h.hash _ (Array.getElem_mem hz)
  · exact h.split _ (Array.getElem_mem hz)
  · exact h.cast _ (Array.getElem_mem hz)
  · refine ⟨fun c => if hc : c < 4 then val (rowsOf s .pub)[z].head! ⟨c, hc⟩ else 0, trivial, ?_⟩
    intro i hi k
    have hi0 : i = 0 := by simpa [forms] using hi
    subst hi0
    rw [limbs_pub]
    simp [rowsOf]

/-- If every slot carries its `next` slot's limbs and `next` is a permutation, the bus balances. -/
theorem balanced_of_next {n : ℕ} {V : Type} [DecidableEq V] (key : Fin n → ℕ) (next : Fin n → Fin n)
    (hnext : Function.Injective next) (v : Fin n → V) (h : ∀ s, v (next s) = v s) : Balanced key next v := by
  intro x
  congr 1
  symm
  refine Finset.card_bij (fun s _ => next s) ?_ ?_ ?_
  · intro s hs
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hs ⊢
    rw [h s]
    exact hs
  · intro a _ b _ hab
    exact hnext hab
  · intro t ht
    obtain ⟨s, rfl⟩ := (Finite.injective_iff_surjective.mp hnext) t
    refine ⟨s, ?_, rfl⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ht ⊢
    rw [h s] at ht
    exact ht

/-- The honest witness of a satisfied circuit: each table at its rows' height, each row's columns those `Sat` gives. -/
noncomputable def honest {st : ℕ → Fin 4 → K} {s : State} {val : Val} (h : Sat st s val) : Witness where
  height T := (rowsOf s T).size
  cols T z := if hz : z < (rowsOf s T).size then Classical.choose (sat_row h T hz) else 0

theorem honest_carried {st : ℕ → Fin 4 → K} {s : State} {val : Val} (h : Sat st s val) {e : Slot}
    (he : e ∈ slots (honest h)) : carried (honest h) e = val (wireOf s e) := by
  obtain ⟨T, z, i⟩ := e
  obtain ⟨hz, hi⟩ := mem_slots.mp he
  change z < (rowsOf s T).size at hz
  funext k
  have := (Classical.choose_spec (sat_row h T hz)).2 i (by rw [forms_length]; exact hi) k
  simp only [carried, honest, dif_pos hz]
  rw [this]
  simp [wireOf, Array.getD_eq_getD_getElem?, hz]

/-- In the honest witness every slot carries its `next` slot's limbs. -/
theorem honest_next {st : ℕ → Fin 4 → K} {s : State} {val : Val} (h : Sat st s val)
    (i : Fin (slots (honest h)).length) :
    carried (honest h) (slots (honest h))[classNext (fun i : Fin (slots (honest h)).length =>
      slotClass s (slots (honest h))[i]) i] = carried (honest h) (slots (honest h))[i] := by
  let cls := fun i : Fin (slots (honest h)).length => slotClass s (slots (honest h))[i]
  have hcls : slotClass s (slots (honest h))[classNext cls i] = slotClass s (slots (honest h))[i] :=
    classNext_cls cls i
  have hmi : (slots (honest h))[i] ∈ slots (honest h) := List.getElem_mem _
  have hmj : (slots (honest h))[classNext cls i] ∈ slots (honest h) := List.getElem_mem _
  rw [honest_carried h hmi, honest_carried h hmj]
  have hrow : ∀ e ∈ slots (honest h), slotClass s e = 2 * wireClass s (wireOf s e) := by
    intro e he
    have hz := (mem_slots.mp he).1
    exact if_pos hz
  rw [hrow _ hmi, hrow _ hmj] at hcls
  exact joined_val h ((wireClass_eq_iff s _ _).mp (by omega))

/-- Non-vacuity of `Claims`: every satisfied circuit whose tables have at most `2^32` rows has a witness meeting the AIR's claims. -/
theorem claims_of_sat {st : ℕ → Fin 4 → K} {s : State} {val : Val} (h : Sat st s val)
    (hsize : ∀ T, (rowsOf s T).size ≤ 2 ^ 32) : Claims s st (honest h) where
  fits T := ⟨le_rfl, hsize T⟩
  tables T z hz := by
    simp only [honest, dif_pos hz]
    exact (Classical.choose_spec (sat_row h T hz)).1
  pub z hz i := by
    have hz' : z < (rowsOf s .pub).size := by simpa [rowsOf] using hz
    have := (Classical.choose_spec (sat_row h .pub hz')).2 0 (by decide) i
    rw [limbs_pub] at this
    simp only [honest, dif_pos hz']
    have hw : (rowsOf s .pub)[z].getD 0 0 = s.pub[z].1 := by simp [rowsOf]
    rw [this, hw, h.pub s.pub[z].1 s.pub[z].2 (Array.getElem_mem hz)]
  bus := balanced_of_next _ _ (classNext_injective _) _ (honest_next h)

/-! Mutation tests: circuits no witness meets the claims of. -/

theorem limbsOf_zero (i : Fin 4) : limbsOf [0, 0, 0, 0] i = 0 := by
  fin_cases i <;> simp [limbsOf, ofWord_zero]

theorem limbsOf_one0 : limbsOf [1, 0, 0, 0] 0 = 1 := by
  simp [limbsOf, ofWord_one]

/-- A wire held equal to two public rows of different constants: no witness's bus balances with them. -/
theorem union_rejected (st : ℕ → Fin 4 → K) :
    ¬ ∃ w, Claims { unions := #[(0, 1)], pub := #[(0, .const [0, 0, 0, 0]), (1, .const [1, 0, 0, 0])] } st w := by
  rintro ⟨w, hw⟩
  have h := sat_of_claims hw
  have h0 := h.pub 0 (.const [0, 0, 0, 0]) (by simp)
  have h1 := h.pub 1 (.const [1, 0, 0, 0]) (by simp)
  have hu := h.unions (0, 1) (by simp)
  have := congrFun (h0.symm.trans (hu.trans h1)) 0
  simp only [srcVal, limbsOf_zero, limbsOf_one0] at this
  exact zero_ne_one this

/-- A public statement row whose statement word is not the constant its wire is held to. -/
theorem statement_rejected :
    ¬ ∃ w, Claims { pub := #[(0, .statement 0), (0, .const [1, 0, 0, 0])] } (fun _ => limbsOf [0, 0, 0, 0]) w := by
  rintro ⟨w, hw⟩
  have h := sat_of_claims hw
  have h0 := h.pub 0 (.statement 0) (by simp)
  have h1 := h.pub 0 (.const [1, 0, 0, 0]) (by simp)
  have := congrFun (h0.symm.trans h1) 0
  simp only [srcVal, limbsOf_zero, limbsOf_one0] at this
  exact zero_ne_one this

theorem ev_limbsOf_one (val : Val) (x : ℕ) (h : val x = limbsOf [1, 0, 0, 0]) : Model.ev val x = 1 := by
  have h1 : limbsOf [1, 0, 0, 0] 1 = 0 := by simp [limbsOf, ofWord_zero]
  have h2 : limbsOf [1, 0, 0, 0] 2 = 0 := by simp [limbsOf, ofWord_zero]
  simp only [Model.ev, h, limbsOf_one0, h1, h2, toE, emb_zero, zero_mul, add_zero]
  exact map_one _

theorem ev_limbsOf_zero (val : Val) (x : ℕ) (h : val x = limbsOf [0, 0, 0, 0]) : Model.ev val x = 0 := by
  simp only [Model.ev, h, limbsOf_zero, toE, emb_zero, zero_mul, add_zero]

/-- An `EMUL` row whose result is not `a·b + d`: `1·1 + 0` held to `0`. -/
theorem emul_rejected (st : ℕ → Fin 4 → K) :
    ¬ ∃ w, Claims { emul := #[[0, 0, 1, 1]], pub := #[(0, .const [1, 0, 0, 0]), (1, .const [0, 0, 0, 0])] } st w := by
  rintro ⟨w, hw⟩
  have h := sat_of_claims hw
  have h0 := ev_limbsOf_one _ 0 (h.pub 0 (.const [1, 0, 0, 0]) (by simp))
  have h1 := ev_limbsOf_zero _ 1 (h.pub 1 (.const [0, 0, 0, 0]) (by simp))
  have := emul_row_ev h (a := 0) (b := 0) (d := 1) (c := 1) (by simp)
  rw [h0, h1, mul_one, add_zero] at this
  exact zero_ne_one this

/-- Non-vacuity on a circuit with a union and a statement row: its statement word is held to a constant, which the honest witness meets. -/
theorem claims_example : Claims { unions := #[(0, 1)], pub := #[(0, .statement 0), (1, .const [5, 0, 0, 0])] }
    (fun _ => limbsOf [5, 0, 0, 0]) (honest (st := fun _ => limbsOf [5, 0, 0, 0])
      (s := { unions := #[(0, 1)], pub := #[(0, .statement 0), (1, .const [5, 0, 0, 0])] })
      (val := fun _ => limbsOf [5, 0, 0, 0])
      ⟨fun _ _ => rfl, by simp, by simp, by simp, by simp, by simp, by
        intro x src hp
        simp only [List.mem_toArray, List.mem_cons, Prod.mk.injEq, List.mem_nil_iff, or_false] at hp
        rcases hp with ⟨-, rfl⟩ | ⟨-, rfl⟩ <;> rfl⟩) :=
  claims_of_sat _ fun T => by cases T <;> simp [rowsOf]

/-! The bus's claim from its product check. -/

/-- A bus tuple as the product check weighs it (`fingerprint_weights`): the key, then the four limbs, as its first five coordinates in `E`. -/
noncomputable def busTuple (p : ℕ × (Fin 4 → K)) : UnionSound.Tuple := fun k =>
  if k.val = 0 then emb (ofWord p.1) else if h : k.val < 5 then emb (p.2 ⟨k.val - 1, by omega⟩) else 0

theorem busTuple_injOn : Set.InjOn busTuple {p | p.1 < 2 ^ 64} := by
  intro p hp q hq h
  have hemb : Function.Injective emb := (AdjoinRoot.of extModulus).injective
  obtain ⟨a, u⟩ := p
  obtain ⟨b, u'⟩ := q
  change a < 2 ^ 64 at hp
  change b < 2 ^ 64 at hq
  have h0 := congrFun h 0
  simp only [busTuple, Fin.val_zero, if_true] at h0
  have hab : a = b := by
    have := congrArg toWord (hemb h0)
    rwa [toWord_ofWord a hp, toWord_ofWord b hq] at this
  refine Prod.ext hab (funext fun i => hemb ?_)
  have := congrFun h ⟨i.val + 1, by omega⟩
  simp only [busTuple, Nat.add_one_ne_zero, if_false, show i.val + 1 < 5 by omega, dif_pos,
    Nat.add_sub_cancel, Fin.eta] at this
  exact this

theorem key_lt {w : Witness} (hfit : ∀ T, w.height T ≤ 2 ^ 32) {e : Slot} (he : e ∈ slots w) : key e < 2 ^ 64 := by
  obtain ⟨hz, hi⟩ := mem_slots.mp he
  have hz' := lt_of_lt_of_le hz (hfit e.1)
  obtain ⟨T, z, i⟩ := e
  have h97 : firstSlot T + i ≤ 97 := by
    cases T <;> simp only [firstSlot, Table.nSlots] at hi ⊢ <;> omega
  simp only [key, slotKey] at hz' ⊢
  rw [show (2 : ℕ) ^ 32 = 4294967296 by norm_num] at hz' ⊢
  rw [show (2 : ℕ) ^ 64 = 18446744073709551616 by norm_num]
  omega

/-- The bus's product claim at a draw `f = (β, A)`: the products of `β + fp_A(t)` over the pulls and over the pushes agree. These are the bus GKR's two root claims, which `bus::verify_balance` holds equal. -/
def ProductClaim (s : State) (w : Witness) (f : Fin 5 → E) : Prop :=
  UnionSound.prodAt (pulls busTuple (fun i : Fin (slots w).length => key (slots w)[i])
      (fun i => carried w (slots w)[i])) (f 0) (Fin.tail f) =
    UnionSound.prodAt (pushes busTuple (fun i : Fin (slots w).length => key (slots w)[i])
      (classNext fun i => slotClass s (slots w)[i]) (fun i => carried w (slots w)[i])) (f 0) (Fin.tail f)

/-- The bus's product check (`bus::verify_balance`): where the bus does not balance, the draws `(β, A)` of `S^5` at which its product claim holds are at most a `4n/|S|` fraction, `n` the bus's slots (`bus_balance_sound`). -/
theorem bus_event (s : State) (w : Witness) (hfit : ∀ T, w.height T ≤ 2 ^ 32) (hne : ¬ BusBalances s w)
    (S : Finset E) :
    (#{f ∈ Fintype.piFinset fun _ : Fin 5 => S | ProductClaim s w f} : ℚ≥0) / (#S ^ 5 : ℚ≥0) ≤
      4 * (slots w).length / #S :=
  bus_balance_sound busTuple {p | p.1 < 2 ^ 64} busTuple_injOn _ _ _
    (fun _ => ⟨key_lt hfit (List.getElem_mem _), key_lt hfit (List.getElem_mem _)⟩) hne S

/-- The bus's draw event for a committed witness: the draws at which its product claim holds though its bus does not balance. -/
noncomputable def busDraws (s : State) (w : Witness) : Finset (Fin 5 → E) :=
  {f | ProductClaim s w f ∧ ¬ BusBalances s w}

/-- Off the draw event, the product claim at the draw gives the bus balanced. -/
theorem bus_of_product {s : State} {w : Witness} {f : Fin 5 → E} (hf : f ∉ busDraws s w)
    (hp : ProductClaim s w f) : BusBalances s w := by
  by_contra hne
  exact hf (by simp only [busDraws, Finset.mem_filter, Finset.mem_univ, true_and]; exact ⟨hp, hne⟩)

/-- The draw event is at most a `4n/|E|` fraction of the draws `E^5`: `bus_event` over all of `E`. -/
theorem busDraws_card (s : State) (w : Witness) (hfit : ∀ T, w.height T ≤ 2 ^ 32) :
    #(busDraws s w) * Fintype.card E ≤ 4 * (slots w).length * Fintype.card E ^ 5 := by
  by_cases hb : BusBalances s w
  · have : busDraws s w = ∅ := by
      ext f
      simp only [busDraws, Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty, iff_false, not_and,
        not_not]
      exact fun _ => hb
    simp [this]
  · have h := bus_event s w hfit hb univ
    rw [Fintype.piFinset_univ, card_univ] at h
    have hE : (0 : ℚ≥0) < Fintype.card E := by exact_mod_cast Fintype.card_pos
    rw [div_le_div_iff₀ (by positivity) hE] at h
    have h' : #({f | ProductClaim s w f} : Finset (Fin 5 → E)) * Fintype.card E ≤
        4 * (slots w).length * Fintype.card E ^ 5 := by exact_mod_cast h
    refine le_trans (Nat.mul_le_mul_right _ (card_le_card fun f hf => ?_)) h'
    simp only [busDraws, Finset.mem_filter, Finset.mem_univ, true_and] at hf ⊢
    exact hf.1

/-- Non-vacuity of `ProductClaim`: the honest witness of a satisfied circuit has its product claim at every draw, its pushes being its pulls permuted. -/
theorem product_honest {st : ℕ → Fin 4 → K} {s : State} {val : Val} (h : Sat st s val) (f : Fin 5 → E) :
    ProductClaim s (honest h) f := by
  have hmulti : ∀ key : Fin (slots (honest h)).length → ℕ,
      pulls busTuple key (fun i => carried (honest h) (slots (honest h))[i]) =
        pushes busTuple key (classNext fun i => slotClass s (slots (honest h))[i])
          (fun i => carried (honest h) (slots (honest h))[i]) := by
    intro key
    have hperm : (univ.val : Multiset (Fin (slots (honest h)).length)).map
        (classNext fun i => slotClass s (slots (honest h))[i]) = univ.val :=
      Multiset.map_univ_val_equiv (Equiv.ofBijective _ (Finite.injective_iff_bijective.mp (classNext_injective _)))
    unfold pulls pushes
    conv_lhs => rw [← hperm]
    rw [Multiset.map_map]
    refine Multiset.map_congr rfl fun i _ => ?_
    simp only [Function.comp_apply]
    rw [honest_next h i]
  unfold ProductClaim
  rw [hmulti]

/-- Mutation test of the product claim: on the circuit holding a wire equal to two different public constants, a witness meeting the rows' claims has its product claim only at draws of the draw event. -/
theorem product_rejected (st : ℕ → Fin 4 → K) (w : Witness) (f : Fin 5 → E)
    (hr : RowClaims { unions := #[(0, 1)], pub := #[(0, .const [0, 0, 0, 0]), (1, .const [1, 0, 0, 0])] } st w)
    (hp : ProductClaim { unions := #[(0, 1)], pub := #[(0, .const [0, 0, 0, 0]), (1, .const [1, 0, 0, 0])] } w f) :
    f ∈ busDraws { unions := #[(0, 1)], pub := #[(0, .const [0, 0, 0, 0]), (1, .const [1, 0, 0, 0])] } w := by
  by_contra hf
  exact union_rejected st ⟨w, ⟨hr, bus_of_product hf hp⟩⟩

/-! The bus's draw over outcomes. -/

/-- The bus's event over outcomes: where the outcome's draw is in the draw event of the outcome's committed witness. -/
noncomputable def busBad {Ω : Type} [Fintype Ω] (s : State) (wit : Ω → Witness) (draw : Ω → Fin 5 → E) : Finset Ω :=
  {ω | draw ω ∈ busDraws s (wit ω)}

/-- The bus's event is at most a `4N/|E|` fraction of the outcomes when the draw is uniform and made after the commitment: a lens `put`/`draw` from outcomes to draws (`Bind.card_lens`) that leaves the committed witness unchanged (`hwit`), every witness's bus having at most `N` slots. -/
theorem busBad_frac {Ω : Type} [Fintype Ω] (s : State) (wit : Ω → Witness) (draw : Ω → Fin 5 → E)
    (put : Ω → (Fin 5 → E) → Ω) (hgp : ∀ ω x, draw (put ω x) = x) (hpg : ∀ ω, put ω (draw ω) = ω)
    (hpp : ∀ ω x y, put (put ω x) y = put ω y) (hwit : ∀ ω x, wit (put ω x) = wit ω)
    (hfit : ∀ ω T, (wit ω).height T ≤ 2 ^ 32) (N : ℕ) (hN : ∀ ω, (slots (wit ω)).length ≤ N) :
    (#(busBad s wit draw) : ℚ≥0) / Fintype.card Ω ≤ ((4 * N : ℕ) : ℚ≥0) / Fintype.card E := by
  have hpos : 0 < Fintype.card E := Fintype.card_pos
  have hterm : ∀ ω, #(busDraws s (wit ω)) ≤ 4 * N * Fintype.card E ^ 4 := by
    intro ω
    have hc := busDraws_card s (wit ω) (hfit ω)
    refine Nat.le_of_mul_le_mul_right ?_ hpos
    calc #(busDraws s (wit ω)) * Fintype.card E ≤ 4 * (slots (wit ω)).length * Fintype.card E ^ 5 := hc
      _ ≤ 4 * N * Fintype.card E ^ 5 := by gcongr; exact hN ω
      _ = 4 * N * Fintype.card E ^ 4 * Fintype.card E := by ring
  have hlens := Bind.card_lens put draw hgp hpg hpp fun ω => draw ω ∈ busDraws s (wit ω)
  have hA : #(busBad s wit draw) * Fintype.card (Fin 5 → E) ≤
      Fintype.card Ω * (4 * N * Fintype.card E ^ 4) := by
    refine le_trans (Nat.mul_le_mul_right _ (card_le_card ?_)) (hlens.trans ?_)
    · intro ω hω
      simp only [busBad, Finset.mem_filter, Finset.mem_univ, true_and] at hω ⊢
      exact hω
    · calc _ ≤ ∑ _ω : Ω, 4 * N * Fintype.card E ^ 4 :=
            sum_le_sum fun ω _ => (card_le_card fun x hx => by
              simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx
              rwa [hgp, hwit] at hx).trans (hterm ω)
        _ = _ := by rw [sum_const, card_univ, smul_eq_mul]
  have hX : Fintype.card (Fin 5 → E) = Fintype.card E ^ 5 := by simp
  rw [hX] at hA
  refine Bind.frac_of_card 4 ?_
  calc #(busBad s wit draw) * Fintype.card E * Fintype.card E ^ 4 =
        #(busBad s wit draw) * Fintype.card E ^ 5 := by ring
    _ ≤ Fintype.card Ω * (4 * N * Fintype.card E ^ 4) := hA
    _ = Fintype.card Ω * (4 * N) * Fintype.card E ^ 4 := by ring

/-! The AIR link in the tree. -/

section Tree

variable {ι Ω : Type}

open Edges

/-- The parts with the AIR's event added to each child's collision event. -/
noncomputable def withAir (P : RecParts ι Ω) (airBad : ι → Finset Ω) : RecParts ι Ω :=
  { P with crBad := fun v => P.crBad v ∪ airBad v }

/-- Child `v`'s AIR event: the constraint batch's event `batchBad v` and the bus's draw event at its committed witness. -/
noncomputable def airBad [Fintype Ω] (t : ι → State) (wit : ι → Ω → Witness) (draw : ι → Ω → Fin 5 → E)
    (batchBad : ι → Finset Ω) (v : ι) : Finset Ω :=
  batchBad v ∪ busBad (t v) (wit v) (draw v)

/-- The premise the AIR link leaves: where the parent's circuit is satisfied, every check's inputs are true, no compression collides (off `crBad v`), the parent's verifier reads statement `st` and off the constraint batch's event `batchBad v`, child `v`'s committed witness `wit v ω` meets the layout's and rows' claims at `st` (`RowClaims`) and its bus's product claim at the outcome's draw `draw v ω` (`ProductClaim`). `RecParts.inOk` being abstract, this is what "every check's inputs are true" must mean: the product claim is the bus GKR's root claims at its draw, and the rows' claims are what the constraint batch's claim gives off `batchBad v`, the draws of its random combination of the identities at which a row breaking one still sums to the claimed value. -/
def ChecksGiveRows (T : TreeSound.Tree ι) (cert : ι → EdgeCert) (t : ι → State) (os : ι → Array (List ℕ))
    (L : Layout) (slot : ι → ℕ) (stRoot : Ω → ℕ → Fin 4 → K) (val : ι → Ω → Val) (P : RecParts ι Ω)
    (batchBad : ι → Finset Ω) (draw : ι → Ω → Fin 5 → E) (wit : ι → Ω → Witness) : Prop :=
  ∀ v ∈ T.nodes, v ≠ T.root → ∀ ω,
    Sat (treeStmt T cert slot stRoot val (T.parent v) ω) (t (T.parent v)) (val (T.parent v) ω) →
    (∀ j < P.J v, P.inOk v j ω) → ω ∉ P.crBad v → ω ∉ batchBad v →
    ((cert (T.parent v)).children.getD (slot v) default).inst.VerifiesAt (cert (T.parent v)).calls
      (os (T.parent v)) (val (T.parent v) ω) (treeStmt T cert slot stRoot val v ω) L.len →
    RowClaims (t v) (treeStmt T cert slot stRoot val v ω) (wit v ω) ∧ ProductClaim (t v) (wit v ω) (draw v ω)

/-- Non-vacuity of `ChecksGiveRows`: parts whose one check per child has the rows' and product claims as its inputs meet it with no constraint batch event. -/
theorem checksGiveRows_claims (T : TreeSound.Tree ι) (cert : ι → EdgeCert) (t : ι → State)
    (os : ι → Array (List ℕ)) (L : Layout) (slot : ι → ℕ) (stRoot : Ω → ℕ → Fin 4 → K) (val : ι → Ω → Val)
    (draw : ι → Ω → Fin 5 → E) (wit : ι → Ω → Witness) (outOk : ι → ℕ → Ω → Prop)
    (testBad : ι → ℕ → Finset Ω) (pcsBad crBad : ι → Finset Ω) :
    ChecksGiveRows T cert t os L slot stRoot val
      ⟨fun _ => 1, fun v _ ω => RowClaims (t v) (treeStmt T cert slot stRoot val v ω) (wit v ω) ∧
        ProductClaim (t v) (wit v ω) (draw v ω), outOk, testBad, pcsBad, crBad⟩ (fun _ => ∅) draw wit :=
  fun _ _ _ _ _ hin _ _ _ => hin 0 Nat.one_pos

/-- `RecParts.hrec`'s premise `hair` for the parts with the AIR's event (the constraint batch's and the bus's draw event), from `ChecksGiveRows` and each child's assignment being its committed witness's (`hval`): off the bus's draw event the product claim gives the bus balanced (`bus_of_product`), and the claims give the child's circuit satisfied (`sat_of_claims`). -/
theorem hair_of_air [Fintype Ω] (T : TreeSound.Tree ι) (cert : ι → EdgeCert) (t : ι → State)
    (os : ι → Array (List ℕ)) (L : Layout) (slot : ι → ℕ) (stRoot : Ω → ℕ → Fin 4 → K) (val : ι → Ω → Val)
    (P : RecParts ι Ω) (batchBad : ι → Finset Ω) (draw : ι → Ω → Fin 5 → E) (wit : ι → Ω → Witness)
    (hval : ∀ v ∈ T.nodes, v ≠ T.root → ∀ ω, val v ω = assign (t v) (wit v ω))
    (hlink : ChecksGiveRows T cert t os L slot stRoot val P batchBad draw wit) :
    ∀ v ∈ T.nodes, v ≠ T.root → ∀ ω,
      Sat (treeStmt T cert slot stRoot val (T.parent v) ω) (t (T.parent v)) (val (T.parent v) ω) →
      (∀ j < (withAir P (airBad t wit draw batchBad)).J v, (withAir P (airBad t wit draw batchBad)).inOk v j ω) →
      ω ∉ (withAir P (airBad t wit draw batchBad)).crBad v →
      ((cert (T.parent v)).children.getD (slot v) default).inst.VerifiesAt (cert (T.parent v)).calls
        (os (T.parent v)) (val (T.parent v) ω) (treeStmt T cert slot stRoot val v ω) L.len →
      Sat (treeStmt T cert slot stRoot val v ω) (t v) (val v ω) := by
  intro v hv hne ω hps hin hcr hver
  have hcr' : ω ∉ P.crBad v ∪ (batchBad v ∪ busBad (t v) (wit v) (draw v)) := hcr
  simp only [Finset.mem_union, not_or] at hcr'
  obtain ⟨hrows, hprod⟩ := hlink v hv hne ω hps hin hcr'.1 hcr'.2.1 hver
  have hdraw : draw v ω ∉ busDraws (t v) (wit v ω) := by
    intro hm
    exact hcr'.2.2 (by simp only [busBad, Finset.mem_filter, Finset.mem_univ, true_and]; exact hm)
  have := sat_of_claims (⟨hrows, bus_of_product hdraw hprod⟩ : Claims (t v) _ (wit v ω))
  rw [hval v hv hne ω]
  exact this

/-- `tree_sound_parts` with the AIR link: the outcomes at which some node's statement or input claims are false are at most the sum over the nodes of their reduction's `bad`, their checks' `testBad`, `pcsBad`, `crBad`, the constraint batch's `batchBad` and the bus's draw event `busBad` fractions (each child's bounded by `busBad_frac`). In place of `hair` it takes each child's assignment being its committed witness's (`hval`) and `ChecksGiveRows`. The child side is the child's circuit with its public rows in the Rust order (`stmtFirst`), which the verifier's committed witness, keys and bus roots are over; it has the same satisfaction (`sat_stmtFirst`). -/
theorem tree_sound_air [Fintype Ω] (T : TreeSound.Tree ι) (cert : ι → EdgeCert) (t : ι → State)
    (os : ι → Array (List ℕ)) (hr : ∀ v ∈ T.nodes, replayR (cert v).calls #[] 0 {} #[] = some (t v, os v))
    (hacc : ∀ v ∈ T.nodes, (cert v).accepts (os v) = true) (hver : ∀ v ∈ T.nodes, (cert v).verifies (os v) = true)
    (L : Layout) (hL : ∀ v ∈ T.nodes, (cert v).layout = L)
    (slot : ι → ℕ) (hslot : ∀ v ∈ T.nodes, v ≠ T.root → slot v < (cert (T.parent v)).children.length)
    (stRoot : Ω → ℕ → Fin 4 → K) (val : ι → Ω → Val)
    (hsroot : ∀ ω, Sat (stRoot ω) (t T.root) (val T.root ω)) (P : RecParts ι Ω)
    (hP : P.Ok fun v ω => Sat (treeStmt T cert slot stRoot val (T.parent v) ω) (t (T.parent v))
      (val (T.parent v) ω))
    (batchBad : ι → Finset Ω) (draw : ι → Ω → Fin 5 → E) (wit : ι → Ω → Witness)
    (hval : ∀ v ∈ T.nodes, v ≠ T.root → ∀ ω, val v ω = assign (stmtFirst (t v)) (wit v ω))
    (hlink : ChecksGiveRows T cert (fun v => stmtFirst (t v)) os L slot stRoot val P batchBad draw wit)
    (tD : Dense E → Prop) (tM : Matrix E → Prop) (bad : ι → Finset Ω)
    (hstep : ∀ v ∈ T.nodes, ∀ ω, ω ∉ bad v →
      stmt T cert slot L (treeStmt T cert slot stRoot val) tD tM v ω → ins cert val tD tM v ω)
    (hroot : ∀ ω, stmt T cert slot L (treeStmt T cert slot stRoot val) tD tM T.root ω) :
    (Finset.card {ω | ∃ v ∈ T.nodes, ¬ (stmt T cert slot L (treeStmt T cert slot stRoot val) tD tM v ω ∧
        ins cert val tD tM v ω)} : ℚ≥0) / Fintype.card Ω ≤
      ∑ v ∈ T.nodes, ((bad v).card + ∑ j ∈ range (P.J v), (P.testBad v j).card + (P.pcsBad v).card +
        (P.crBad v).card + (batchBad v).card + (busBad (stmtFirst (t v)) (wit v) (draw v)).card : ℚ≥0) /
        Fintype.card Ω := by
  have hP' : (withAir P (airBad (fun v => stmtFirst (t v)) wit draw batchBad)).Ok fun v ω =>
      Sat (treeStmt T cert slot stRoot val (T.parent v) ω) (t (T.parent v)) (val (T.parent v) ω) :=
    ⟨fun v j ω hj hh hc => hP.test v j ω hj hh fun h => hc (Finset.mem_union_left _ h), hP.flow⟩
  have hair0 := hair_of_air T cert (fun v => stmtFirst (t v)) os L slot stRoot val P batchBad draw wit hval hlink
  have hair := fun v hv hne ω hps hin hcr hver =>
    sat_stmtFirst.mp (hair0 v hv hne ω (sat_stmtFirst.mpr hps) hin hcr hver)
  have hparts := tree_sound_parts T cert t os hr hacc hver L hL slot hslot stRoot val hsroot
    (withAir P (airBad (fun v => stmtFirst (t v)) wit draw batchBad)) hP' hair tD tM bad hstep hroot
  refine hparts.trans ?_
  refine sum_le_sum fun v _ => div_le_div_of_nonneg_right ?_ (by positivity)
  have key : ∀ (a b c : ℚ≥0) (d e f g : ℕ), d ≤ e + (f + g) →
      a + b + c + (d : ℚ≥0) ≤ a + b + c + e + f + g := by
    intro a b c d e f g h
    have : (d : ℚ≥0) ≤ e + (f + g) := by exact_mod_cast h
    calc a + b + c + (d : ℚ≥0) ≤ a + b + c + (e + (f + g)) := by gcongr
      _ = a + b + c + e + f + g := by ring
  exact key _ _ _ _ _ _ _ ((card_union_le _ _).trans (Nat.add_le_add_left (card_union_le _ _) _))

end Tree

end LeanVMCircuits.Rec.AirLink
