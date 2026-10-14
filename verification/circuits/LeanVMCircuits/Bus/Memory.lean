module

public import LeanVMCircuits.Bus.Walk

@[expose] public section

/-!
# Memory consistency

Theorem `thm:rwmem` of `doc/leanvm/body/06-bus-interactions.tex` (§sec:memchan). One read-write array: every cell is
seeded at the live timestamp of cycle 0 with its initial value and finalized with its last timestamp and value; every
access pulls the cell at its previous timestamp and pushes it at the row's clock plus its slot. If those are the
only flushes carrying the array's separator, every access is in order (`eq:order`), and the live accesses carry
distinct timestamps after the seeds' (Corollary `cor:clock`), then balance makes the live accesses at each cell a
chain from its initial value to its final one (`memory_consistent`). Accesses of rows without the live bit, padding
rows among them, only ever meet each other's tuples and constrain nothing.
-/

namespace LeanVMCircuits.Bus

open LeanVMCircuits.Rec

/-! ### Timestamps -/

theorem slot_xor (q k : ℕ) (hk : k < 2 ^ 5) : (2 ^ 5 * q) ^^^ k = 2 ^ 5 * q + k := by
  apply Nat.eq_of_testBit_eq
  intro j
  rw [Nat.testBit_xor, Nat.testBit_two_pow_mul, Nat.testBit_two_pow_mul_add q hk]
  by_cases hj : j < 5
  · simp [hj, show ¬ 5 ≤ j by omega]
  · have k_bit : k.testBit j = false :=
      Nat.testBit_lt_two_pow (lt_of_lt_of_le hk (Nat.pow_le_pow_right (by norm_num) (by omega)))
    simp [hj, k_bit, show 5 ≤ j by omega]

/-- An access's timestamp `ts + ⟨k⟩`, a sum in `K`, is the word `ts + k`: the clock's five low bits are zero. -/
theorem ofWord_add_slot (q k : ℕ) (hk : k < 2 ^ 5) (h : 2 ^ 5 * q + k < 2 ^ 64) :
    ofWord (2 ^ 5 * q) + ofWord k = ofWord (2 ^ 5 * q + k) := by
  unfold ofWord
  rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt h, ← ev_xor, slot_xor q k hk]

/--
An access (§sec:memchan) at address `addr` in slot `slot` of a row whose clock names the integer `clock`: it pulls
`⟨sep, addr, ts_prev, old⟩`, `ts_prev` naming `prev`, and pushes `⟨sep, addr, ts + ⟨slot⟩, new⟩`.
-/
structure Access where
  addr : K
  clock : ℕ
  slot : ℕ
  prev : ℕ
  old : K
  new : K

namespace Access

/-- The timestamp an access is ordered at, `ts + k`. -/
def time (x : Access) : ℕ := x.clock + x.slot

/-- The access's row is live: its clock has bit 40. -/
def Live (x : Access) : Prop := 2 ^ 40 ≤ x.clock

/-- A clock below `2^41` with its five slot bits clear, a slot below `2^5`, a previous timestamp below `2^41`. -/
def WellFormed (x : Access) : Prop := x.clock < 2 ^ 41 ∧ 2 ^ 5 ∣ x.clock ∧ x.slot < 2 ^ 5 ∧ x.prev < 2 ^ 41

/-- The order check `eq:order`: `ts_prev` has the row's live bit, and on a live row `ts_prev < ts + k`. -/
def InOrder (x : Access) : Prop := (2 ^ 40 ≤ x.prev ↔ 2 ^ 40 ≤ x.clock) ∧ (2 ^ 40 ≤ x.clock → x.prev < x.time)

/-- The tuple an access pulls. -/
noncomputable def pull (sep : K) (x : Access) : Tuple := tuple [sep, x.addr, ofWord x.prev, x.old]

/-- The tuple an access pushes, at `ts + ⟨k⟩`. -/
noncomputable def push (sep : K) (x : Access) : Tuple := tuple [sep, x.addr, ofWord x.clock + ofWord x.slot, x.new]

theorem push_time {x : Access} (wf : x.WellFormed) (sep : K) : (x.push sep)[2] = ofWord x.time := by
  obtain ⟨ clock_lt, ⟨ q, hq ⟩, slot_lt, - ⟩ := wf
  have coord : (x.push sep)[2] = ofWord x.clock + ofWord x.slot := by simp [push, tuple_get]
  rw [coord, time, hq, ofWord_add_slot q x.slot slot_lt (by omega)]

end Access

/-- A read-write array (§sec:memchan): `size` cells at pairwise distinct addresses under a separator, with their
initial values and the committed final values and last timestamps. -/
structure MemArray where
  sep : K
  size : ℕ
  addr : Fin size → K
  addr_injective : Function.Injective addr
  init : Fin size → K
  fin : Fin size → K
  tsfin : Fin size → K

namespace MemArray

variable (mem : MemArray)

/-- The seed of cell `i`, pushed at the live timestamp of cycle 0. -/
noncomputable def seed (i : Fin mem.size) : Tuple := tuple [mem.sep, mem.addr i, ofWord (2 ^ 40), mem.init i]

/-- The finalization of cell `i`, pulled at its committed last timestamp. -/
noncomputable def final (i : Fin mem.size) : Tuple := tuple [mem.sep, mem.addr i, mem.tsfin i, mem.fin i]

/-- The array's flushes: the seeds, the accesses and the finalizations. -/
noncomputable def flushes (accesses : List Access) : Flushes where
  pushes := (List.finRange mem.size).map mem.seed ++ accesses.map (Access.push mem.sep)
  pulls := accesses.map (Access.pull mem.sep) ++ (List.finRange mem.size).map mem.final

end MemArray

/-! ### The chain at one address -/

section Chain

variable {ι V : Type} [DecidableEq V] (L : List ι) (time prev : ι → ℕ) (new old : ι → V)

omit [DecidableEq V] in
theorem card_filter_map (g : ι → ℕ × V) (T : ℕ) :
    ((L.map g : Multiset (ℕ × V)).filter fun p => p.1 < T).card = L.countP fun x => (g x).1 < T := by
  simp [Multiset.filter_coe, List.filter_map, List.countP_eq_length_filter, Function.comp_def]

theorem countP_lt_of_imp (p q : ι → Prop) [DecidablePred p] [DecidablePred q] (hpq : ∀ w ∈ L, p w → q w)
    {x : ι} (hx : x ∈ L) (np : ¬ p x) (hq : q x) : L.countP (fun w => p w) < L.countP fun w => q w := by
  induction L with
  | nil => simp at hx
  | cons w L ih =>
    have hpq' : ∀ w ∈ L, p w → q w := fun w hw => hpq w (List.mem_cons_of_mem _ hw)
    rcases List.mem_cons.mp hx with rfl | hx
    · have mono := List.countP_mono_left (l := L) (p := fun w => decide (p w)) (q := fun w => decide (q w))
        (by simpa using hpq')
      simp only [List.countP_cons, np, hq, decide_false, decide_true]
      simp only [Bool.false_eq_true, if_false, if_true, add_zero]
      omega
    · have := ih hpq' hx
      simp only [List.countP_cons]
      by_cases hw : p w
      · simp [hw, hpq w (List.mem_cons_self ..) hw]
        omega
      · by_cases hw' : q w <;> simp [hw, hw'] <;> omega

omit [DecidableEq V] in
/-- Without a seed, no live access can be at the address: the earliest one's pull matches nothing. -/
theorem chain_empty_of_no_seed (F : Multiset (ℕ × V)) (prev_lt : ∀ x ∈ L, prev x < time x)
    (balance : (L.map fun x => (time x, new x) : Multiset (ℕ × V)) = (L.map fun x => (prev x, old x) : Multiset _) + F) :
    L = [] := by
  classical
  by_contra ne_nil
  obtain ⟨ x0, x0_mem ⟩ := List.exists_mem_of_ne_nil L ne_nil
  have exists_time : ∃ n, ∃ x ∈ L, time x = n := ⟨ _, x0, x0_mem, rfl ⟩
  obtain ⟨ x, x_mem, x_time ⟩ := Nat.find_spec exists_time
  have mem : (prev x, old x) ∈ (L.map fun x => (time x, new x) : Multiset (ℕ × V)) := by
    rw [balance]
    exact Multiset.mem_add.mpr (Or.inl (Multiset.mem_coe.mpr (List.mem_map_of_mem x_mem)))
  obtain ⟨ y, y_mem, y_eq ⟩ := List.mem_map.mp (Multiset.mem_coe.mp mem)
  have := Nat.find_min' exists_time ⟨ y, y_mem, rfl ⟩
  have := prev_lt x x_mem
  simp only [Prod.mk.injEq] at y_eq
  omega

/--
The chain at one address with a seed `(s0, v0)`: every access reads either the seed, being the earliest, or the
latest earlier access; the finalization, the only other pull, takes the latest access, or the seed if none.
-/
theorem chain_of_seed (s0 : ℕ) (v0 : V) (F : Multiset (ℕ × V)) (after : ∀ x ∈ L, s0 < time x)
    (prev_lt : ∀ x ∈ L, prev x < time x)
    (balance : (s0, v0) ::ₘ (L.map fun x => (time x, new x) : Multiset (ℕ × V)) =
      (L.map fun x => (prev x, old x) : Multiset _) + F) :
    (∀ x ∈ L, (prev x = s0 ∧ old x = v0 ∧ ∀ y ∈ L, time x ≤ time y) ∨
      ∃ y ∈ L, time y = prev x ∧ old x = new y ∧ ∀ z ∈ L, time z < time x → time z ≤ time y) ∧
    ((L = [] ∧ F = {(s0, v0)}) ∨ ∃ y ∈ L, F = {(time y, new y)} ∧ ∀ z ∈ L, time z ≤ time y) := by
  classical
  -- counting the tuples below any timestamp
  have count : ∀ T, (if s0 < T then 1 else 0) + L.countP (fun x => time x < T) =
      L.countP (fun x => prev x < T) + (F.filter fun p => p.1 < T).card := by
    intro T
    have := congrArg (fun M : Multiset (ℕ × V) => (M.filter fun p => p.1 < T).card) balance
    simp only [Multiset.filter_cons, Multiset.filter_add, Multiset.card_add, card_filter_map] at this
    split_ifs at this ⊢ with h <;> simp_all
  -- no access lies strictly between an access and the timestamp it reads
  have gap : ∀ x ∈ L, ∀ z ∈ L, prev x < time z → time z < time x → False := by
    intro x x_mem z z_mem below above
    have h1 := countP_lt_of_imp L (fun w => time w < time z) (fun w => time w ≤ time z)
      (fun w _ h => Nat.le_of_lt h) z_mem (Nat.lt_irrefl _) (Nat.le_refl _)
    have h2 := countP_lt_of_imp L (fun w => time w ≤ time z) (fun w => prev w < time z)
      (fun w w_mem h => Nat.lt_of_lt_of_le (prev_lt w w_mem) h) x_mem (by omega) below
    have := count (time z)
    split_ifs at this <;> omega
  constructor
  · intro x x_mem
    have mem : (prev x, old x) ∈ (s0, v0) ::ₘ (L.map fun x => (time x, new x) : Multiset (ℕ × V)) := by
      rw [balance]
      exact Multiset.mem_add.mpr (Or.inl (Multiset.mem_coe.mpr (List.mem_map_of_mem x_mem)))
    rcases Multiset.mem_cons.mp mem with seed_eq | mem
    · simp only [Prod.mk.injEq] at seed_eq
      refine Or.inl ⟨ seed_eq.1, seed_eq.2, fun y y_mem => ?_ ⟩
      by_contra earlier
      exact gap x x_mem y y_mem (by have := after y y_mem; omega) (by omega)
    · obtain ⟨ y, y_mem, y_eq ⟩ := List.mem_map.mp (Multiset.mem_coe.mp mem)
      simp only [Prod.mk.injEq] at y_eq
      refine Or.inr ⟨ y, y_mem, y_eq.1, y_eq.2.symm, fun z z_mem z_lt => ?_ ⟩
      by_contra later
      exact gap x x_mem z z_mem (by omega) z_lt
  · -- the finalization is the one pull left
    have card_eq := congrArg Multiset.card balance
    simp only [Multiset.card_cons, Multiset.card_add, Multiset.coe_card, List.length_map] at card_eq
    obtain ⟨ f, rfl ⟩ := Multiset.card_eq_one.mp (by omega : F.card = 1)
    have f_mem : f ∈ (s0, v0) ::ₘ (L.map fun x => (time x, new x) : Multiset (ℕ × V)) := by
      rw [balance]
      exact Multiset.mem_add.mpr (Or.inr (Multiset.mem_singleton_self f))
    by_cases empty : L = []
    · subst empty
      simp only [List.map_nil, Multiset.coe_nil, Multiset.mem_cons, Multiset.notMem_zero, or_false] at f_mem
      exact Or.inl ⟨ rfl, by rw [f_mem] ⟩
    obtain ⟨ ymax, ymax_mem, ymax_max ⟩ := L.toFinset.exists_max_image time
      (List.toFinset_nonempty_iff L |>.mpr empty)
    rw [List.mem_toFinset] at ymax_mem
    have ymax_max' : ∀ z ∈ L, time z ≤ time ymax := fun z hz => ymax_max z (List.mem_toFinset.mpr hz)
    -- every pull of an access is below the latest timestamp, so the finalization is not
    have all_prev : L.countP (fun x => prev x < time ymax) = L.length := by
      rw [List.countP_eq_length]
      intro x hx
      simpa using Nat.lt_of_lt_of_le (prev_lt x hx) (ymax_max' x hx)
    have some_time := countP_lt_of_imp L (fun w => time w < time ymax) (fun w => time w ≤ time ymax)
      (fun _ _ h => Nat.le_of_lt h) ymax_mem (Nat.lt_irrefl _) (Nat.le_refl _)
    have all_le : L.countP (fun w => time w ≤ time ymax) = L.length :=
      List.countP_eq_length.mpr fun x hx => by simpa using ymax_max' x hx
    rw [all_le] at some_time
    have := count (time ymax)
    rw [if_pos (after ymax ymax_mem), all_prev] at this
    have f_late : time ymax ≤ f.1 := by
      by_contra f_early
      simp only [Multiset.filter_singleton, if_pos (Nat.lt_of_not_le f_early), Multiset.card_singleton] at this
      omega
    rcases Multiset.mem_cons.mp f_mem with rfl | f_mem
    · have := after ymax ymax_mem
      omega
    · obtain ⟨ y, y_mem, rfl ⟩ := List.mem_map.mp (Multiset.mem_coe.mp f_mem)
      refine Or.inr ⟨ y, y_mem, rfl, fun z z_mem => ?_ ⟩
      have := ymax_max' z z_mem
      omega

end Chain

/-! ### One array -/

theorem ofWord_toWord (x : K) : ofWord (toWord x) = x := FiniteField.fromNat_val x

/-- What a memory tuple says about its cell: its timestamp as an integer, and its value. -/
noncomputable def stamp (t : Tuple) : ℕ × K := (toWord t[2], t[3])

theorem map_filter_map {β : Type} (l : List β) (f : β → Tuple) (P : Tuple → Prop) [DecidablePred P]
    (Q : β → Prop) [DecidablePred Q] (g : β → ℕ × K) (hQ : ∀ b ∈ l, P (f b) ↔ Q b)
    (hg : ∀ b ∈ l, Q b → stamp (f b) = g b) :
    ((l.map f).filter fun t => P t).map stamp = (l.filter fun b => Q b).map g := by
  induction l with
  | nil => rfl
  | cons b l ih =>
    have ih' := ih (fun b' h => hQ b' (List.mem_cons_of_mem _ h)) (fun b' h => hg b' (List.mem_cons_of_mem _ h))
    by_cases hb : Q b
    · simp [(hQ b (List.mem_cons_self ..)).mpr hb, hb, hg b (List.mem_cons_self ..) hb, ih']
    · simp [mt (hQ b (List.mem_cons_self ..)).mp hb, hb, ih']

theorem finRange_filter_addr (mem : MemArray) (i : Fin mem.size) :
    (List.finRange mem.size).filter (fun j => decide (mem.addr j = mem.addr i)) = [i] := by
  rw [List.filter_congr (q := fun j => decide (j = i))
    (fun j _ => by simp [mem.addr_injective.eq_iff]), List.filter_eq,
    List.count_eq_one_of_mem (List.nodup_finRange _) (List.mem_finRange i)]
  rfl

/--
Theorem `thm:rwmem` for one array. Let the seeds, the accesses and the finalizations be the only flushes carrying the
array's separator, every access be well formed and in order (`eq:order`), and every live access come after the
seeds (its row's cycle is at least 1, Corollary `cor:clock`). If the bus balances:
every live access is at an address of the array;
each live access either is the earliest at its cell, reading the cell's initial value at the seed's timestamp
`2^40`, or reads the value the latest earlier live access at its cell wrote, at that access's timestamp;
and each cell's final value and last timestamp are those of its latest live access, or its initial value and `2^40`
if it has none.
-/
theorem memory_consistent (mem : MemArray) (accesses : List Access)
    (wf : ∀ x ∈ accesses, x.WellFormed) (in_order : ∀ x ∈ accesses, x.InOrder)
    (after_seeds : ∀ x ∈ accesses, x.Live → 2 ^ 40 < x.time)
    (rest : Flushes) (avoids : rest.Avoids fun t => t[0] = mem.sep)
    (balance : (rest ++ mem.flushes accesses).Balanced) :
    (∀ x ∈ accesses, x.Live → ∃ i, x.addr = mem.addr i) ∧
    (∀ x ∈ accesses, x.Live →
      (x.prev = 2 ^ 40 ∧ (∀ i, x.addr = mem.addr i → x.old = mem.init i) ∧
          ∀ y ∈ accesses, y.Live → y.addr = x.addr → x.time ≤ y.time) ∨
        ∃ y ∈ accesses, y.Live ∧ y.addr = x.addr ∧ y.time = x.prev ∧ x.old = y.new ∧
          ∀ z ∈ accesses, z.Live → z.addr = x.addr → z.time < x.time → z.time ≤ y.time) ∧
    (∀ i, ((∀ y ∈ accesses, y.Live → y.addr ≠ mem.addr i) ∧ mem.tsfin i = ofWord (2 ^ 40) ∧
          mem.fin i = mem.init i) ∨
        ∃ y ∈ accesses, y.Live ∧ y.addr = mem.addr i ∧ mem.tsfin i = ofWord y.time ∧ mem.fin i = y.new ∧
          ∀ z ∈ accesses, z.Live → z.addr = mem.addr i → z.time ≤ y.time) := by
  classical
  -- the coordinates of the array's tuples
  have time_lt : ∀ x ∈ accesses, x.time < 2 ^ 41 := by
    intro x hx
    obtain ⟨ clock_lt, ⟨ q, hq ⟩, slot_lt, - ⟩ := wf x hx
    unfold Access.time
    omega
  have push_coords : ∀ x ∈ accesses, (x.push mem.sep)[0] = mem.sep ∧ (x.push mem.sep)[1] = x.addr ∧
      toWord (x.push mem.sep)[2] = x.time ∧ (x.push mem.sep)[3] = x.new := by
    intro x hx
    refine ⟨ by simp [Access.push, tuple_get], by simp [Access.push, tuple_get], ?_, by simp [Access.push, tuple_get] ⟩
    rw [Access.push_time (wf x hx), toWord_ofWord _ (by have := time_lt x hx; omega)]
  have pull_coords : ∀ x ∈ accesses, (x.pull mem.sep)[0] = mem.sep ∧ (x.pull mem.sep)[1] = x.addr ∧
      toWord (x.pull mem.sep)[2] = x.prev ∧ (x.pull mem.sep)[3] = x.old := by
    intro x hx
    have prev_lt := (wf x hx).2.2.2
    refine ⟨ by simp [Access.pull, tuple_get], by simp [Access.pull, tuple_get], ?_, by simp [Access.pull, tuple_get] ⟩
    have coord : (x.pull mem.sep)[2] = ofWord x.prev := by simp [Access.pull, tuple_get]
    rw [coord]
    exact toWord_ofWord _ (by omega)
  have live_time : ∀ x ∈ accesses, (2 ^ 40 ≤ x.time ↔ x.Live) := by
    intro x hx
    obtain ⟨ clock_lt, ⟨ q, hq ⟩, slot_lt, - ⟩ := wf x hx
    unfold Access.time Access.Live
    omega
  have live_prev : ∀ x ∈ accesses, (2 ^ 40 ≤ x.prev ↔ x.Live) := fun x hx => (in_order x hx).1
  -- at each address, the live tuples' timestamps and values balance
  have per_address : ∀ a : K,
      ((((List.finRange mem.size).filter fun i => mem.addr i = a).map fun i => ((2 ^ 40 : ℕ), mem.init i)) ++
        (accesses.filter fun x => x.addr = a ∧ x.Live).map (fun x => (x.time, x.new)) : Multiset (ℕ × K)) =
      ((accesses.filter fun x => x.addr = a ∧ x.Live).map (fun x => (x.prev, x.old)) ++
        ((List.finRange mem.size).filter fun i => mem.addr i = a ∧ 2 ^ 40 ≤ toWord (mem.tsfin i) ∧
          toWord (mem.tsfin i) < 2 ^ 41).map (fun i => (toWord (mem.tsfin i), mem.fin i)) :
        Multiset (ℕ × K)) := by
    intro a
    let P : Tuple → Prop := fun t => t[0] = mem.sep ∧ t[1] = a ∧ 2 ^ 40 ≤ toWord t[2] ∧ toWord t[2] < 2 ^ 41
    have eq := Flushes.filter_eq_of_balanced balance P
    have avoids' : rest.Avoids P := ⟨ fun t ht hP => avoids.1 t ht hP.1, fun t ht hP => avoids.2.1 t ht hP.1,
      fun p hp hne hP => avoids.2.2 p hp hne hP.1 ⟩
    simp only [Flushes.pushed_append, Flushes.pulled_append, Multiset.filter_add,
      Flushes.filter_pushed_of_avoids avoids', Flushes.filter_pulled_of_avoids avoids', zero_add] at eq
    have pushed_eq : (mem.flushes accesses).pushed =
        (((List.finRange mem.size).map mem.seed ++ accesses.map (Access.push mem.sep) : List Tuple) :
          Multiset Tuple) := by
      simp [Flushes.pushed, MemArray.flushes]
    have pulled_eq : (mem.flushes accesses).pulled =
        ((accesses.map (Access.pull mem.sep) ++ (List.finRange mem.size).map mem.final : List Tuple) :
          Multiset Tuple) := rfl
    rw [pushed_eq, pulled_eq] at eq
    have stamps := congrArg (Multiset.map stamp) eq
    simp only [Multiset.filter_coe, Multiset.map_coe, List.filter_append, List.map_append] at stamps
    have seed_time : ∀ i, toWord (mem.seed i)[2] = 2 ^ 40 := by
      intro i
      have coord : (mem.seed i)[2] = ofWord (2 ^ 40) := by simp [MemArray.seed, tuple_get]
      rw [coord, toWord_ofWord _ (by norm_num)]
    have seeds := map_filter_map (List.finRange mem.size) mem.seed P (fun i => mem.addr i = a)
      (fun i => ((2 ^ 40 : ℕ), mem.init i))
      (fun i _ => by
        have h0 : (mem.seed i)[0] = mem.sep := by simp [MemArray.seed, tuple_get]
        have h1 : (mem.seed i)[1] = mem.addr i := by simp [MemArray.seed, tuple_get]
        simp only [P, h0, h1, seed_time i, true_and]
        constructor
        · exact fun h => h.1
        · exact fun h => ⟨ h, le_refl _, by norm_num ⟩)
      (fun i _ _ => by
        have h3 : (mem.seed i)[3] = mem.init i := by simp [MemArray.seed, tuple_get]
        simp only [stamp, seed_time i, h3])
    have pushes := map_filter_map accesses (Access.push mem.sep) P (fun x => x.addr = a ∧ x.Live)
      (fun x => (x.time, x.new))
      (fun x hx => by
        obtain ⟨ h0, h1, h2, - ⟩ := push_coords x hx
        simp only [P, h0, h1, h2, true_and, ← live_time x hx]
        have := time_lt x hx
        constructor
        · rintro ⟨ ha, hl, - ⟩
          exact ⟨ ha, hl ⟩
        · rintro ⟨ ha, hl ⟩
          exact ⟨ ha, hl, this ⟩)
      (fun x hx _ => by
        obtain ⟨ -, -, h2, h3 ⟩ := push_coords x hx
        simp only [stamp, h2, h3])
    have pulls := map_filter_map accesses (Access.pull mem.sep) P (fun x => x.addr = a ∧ x.Live)
      (fun x => (x.prev, x.old))
      (fun x hx => by
        obtain ⟨ h0, h1, h2, - ⟩ := pull_coords x hx
        simp only [P, h0, h1, h2, true_and, ← live_prev x hx]
        have := (wf x hx).2.2.2
        constructor
        · rintro ⟨ ha, hl, - ⟩
          exact ⟨ ha, hl ⟩
        · rintro ⟨ ha, hl ⟩
          exact ⟨ ha, hl, this ⟩)
      (fun x hx _ => by
        obtain ⟨ -, -, h2, h3 ⟩ := pull_coords x hx
        simp only [stamp, h2, h3])
    have finals := map_filter_map (List.finRange mem.size) mem.final P
      (fun i => mem.addr i = a ∧ 2 ^ 40 ≤ toWord (mem.tsfin i) ∧ toWord (mem.tsfin i) < 2 ^ 41)
      (fun i => (toWord (mem.tsfin i), mem.fin i))
      (fun i _ => by simp [P, MemArray.final, tuple_get])
      (fun i _ _ => by simp [stamp, MemArray.final, tuple_get])
    rw [seeds, pushes, pulls, finals] at stamps
    exact stamps
  -- the live accesses at an address
  let at_ (a : K) := accesses.filter fun x => x.addr = a ∧ x.Live
  have mem_at : ∀ a x, x ∈ at_ a ↔ x ∈ accesses ∧ x.addr = a ∧ x.Live := by
    intro a x
    simp [at_]
  have prev_lt : ∀ a, ∀ x ∈ at_ a, x.prev < x.time := by
    intro a x hx
    obtain ⟨ hx, -, live ⟩ := (mem_at a x).mp hx
    exact (in_order x hx).2 live
  have after : ∀ a, ∀ x ∈ at_ a, 2 ^ 40 < x.time := by
    intro a x hx
    obtain ⟨ hx, -, live ⟩ := (mem_at a x).mp hx
    exact after_seeds x hx live
  -- with no cell at an address, no live access is there
  have in_range : ∀ x ∈ accesses, x.Live → ∃ i, x.addr = mem.addr i := by
    intro x hx live
    by_contra no_cell
    push Not at no_cell
    have balance_a := per_address x.addr
    have no_seed : ((List.finRange mem.size).filter fun i => mem.addr i = x.addr) = [] :=
      List.filter_eq_nil_iff.mpr fun i _ => by simpa using (no_cell i).symm
    have no_final : ((List.finRange mem.size).filter fun i => mem.addr i = x.addr ∧
        2 ^ 40 ≤ toWord (mem.tsfin i) ∧ toWord (mem.tsfin i) < 2 ^ 41) = [] :=
      List.filter_eq_nil_iff.mpr fun i _ => by simp [(no_cell i).symm]
    rw [no_seed, no_final] at balance_a
    simp only [List.map_nil, List.nil_append, List.append_nil] at balance_a
    have empty := chain_empty_of_no_seed (at_ x.addr) Access.time Access.prev Access.new Access.old 0
      (prev_lt x.addr) (by rw [add_zero]; exact balance_a)
    have : x ∈ at_ x.addr := (mem_at x.addr x).mpr ⟨ hx, rfl, live ⟩
    rw [empty] at this
    simp at this
  -- at a cell, the chain
  have seeded : ∀ i : Fin mem.size,
      ((2 ^ 40 : ℕ), mem.init i) ::ₘ
          (((at_ (mem.addr i)).map fun x => (x.time, x.new) : List (ℕ × K)) : Multiset (ℕ × K)) =
        (((at_ (mem.addr i)).map fun x => (x.prev, x.old) : List (ℕ × K)) : Multiset (ℕ × K)) +
          ((((List.finRange mem.size).filter fun j => mem.addr j = mem.addr i ∧ 2 ^ 40 ≤ toWord (mem.tsfin j) ∧
            toWord (mem.tsfin j) < 2 ^ 41).map fun j => (toWord (mem.tsfin j), mem.fin j) : List (ℕ × K)) :
              Multiset (ℕ × K)) := by
    intro i
    have balance_i := per_address (mem.addr i)
    rw [finRange_filter_addr mem i, List.map_cons, List.map_nil, List.singleton_append] at balance_i
    rw [Multiset.coe_add, Multiset.cons_coe]
    exact balance_i
  have chain := fun i : Fin mem.size => chain_of_seed (at_ (mem.addr i)) Access.time Access.prev Access.new
    Access.old (2 ^ 40) (mem.init i) _ (after _) (prev_lt _) (seeded i)
  refine ⟨ in_range, ?_, ?_ ⟩
  · intro x hx live
    obtain ⟨ i, hi ⟩ := in_range x hx live
    have x_at : x ∈ at_ (mem.addr i) := (mem_at _ x).mpr ⟨ hx, hi, live ⟩
    rcases (chain i).1 x x_at with ⟨ prev_eq, old_eq, earliest ⟩ | ⟨ y, y_at, y_time, old_eq, latest ⟩
    · refine Or.inl ⟨ prev_eq, fun j hj => ?_, fun y hy y_live y_addr => earliest y ((mem_at _ y).mpr
        ⟨ hy, y_addr.trans hi, y_live ⟩) ⟩
      rw [mem.addr_injective (hi.symm.trans hj)] at old_eq
      exact old_eq
    · obtain ⟨ hy, y_addr, y_live ⟩ := (mem_at _ y).mp y_at
      exact Or.inr ⟨ y, hy, y_live, y_addr.trans hi.symm, y_time, old_eq, fun z hz z_live z_addr z_lt =>
        latest z ((mem_at _ z).mpr ⟨ hz, z_addr.trans hi, z_live ⟩) z_lt ⟩
  · intro i
    have final_mem : ∀ v, (((List.finRange mem.size).filter fun j => mem.addr j = mem.addr i ∧
        2 ^ 40 ≤ toWord (mem.tsfin j) ∧ toWord (mem.tsfin j) < 2 ^ 41).map
          (fun j => (toWord (mem.tsfin j), mem.fin j)) : Multiset (ℕ × K)) = {v} →
        (toWord (mem.tsfin i), mem.fin i) = v := by
      intro v hv
      have v_mem : v ∈ (((List.finRange mem.size).filter fun j => mem.addr j = mem.addr i ∧
          2 ^ 40 ≤ toWord (mem.tsfin j) ∧ toWord (mem.tsfin j) < 2 ^ 41).map
            (fun j => (toWord (mem.tsfin j), mem.fin j)) : Multiset (ℕ × K)) := by
        rw [hv]
        exact Multiset.mem_singleton_self v
      obtain ⟨ j, j_mem, rfl ⟩ := List.mem_map.mp (Multiset.mem_coe.mp v_mem)
      simp only [List.mem_filter, decide_eq_true_eq] at j_mem
      rw [mem.addr_injective j_mem.2.1]
    rcases (chain i).2 with ⟨ empty, final_eq ⟩ | ⟨ y, y_at, final_eq, latest ⟩
    · have := final_mem _ final_eq
      simp only [Prod.mk.injEq] at this
      refine Or.inl ⟨ fun y hy y_live y_addr => ?_, by rw [← ofWord_toWord (mem.tsfin i), this.1], this.2 ⟩
      have : y ∈ at_ (mem.addr i) := (mem_at _ y).mpr ⟨ hy, y_addr, y_live ⟩
      rw [empty] at this
      simp at this
    · have := final_mem _ final_eq
      simp only [Prod.mk.injEq] at this
      obtain ⟨ hy, y_addr, y_live ⟩ := (mem_at _ y).mp y_at
      exact Or.inr ⟨ y, hy, y_live, y_addr, by rw [← ofWord_toWord (mem.tsfin i), this.1], this.2,
        fun z hz z_live z_addr => latest z ((mem_at _ z).mpr ⟨ hz, z_addr, z_live ⟩) ⟩

/-! ### With the state walk -/

/--
`thm:rwmem` with its clock hypothesis derived from Corollary `cor:clock`: when every access belongs to a row of the
state interaction (its clock is that row's), the walk gives every live row a clock `2^40 + 2^5 i` with `i ≥ 1`, so
every live access comes after the seeds.
-/
theorem memory_consistent_of_state_walk (rows : List StateRow) (pcEntry pcHalt : K) (cycles : ℕ)
    (cycles_lt : cycles < 2 ^ 35) (clock_lt : ∀ r ∈ rows, r.clock < 2 ^ 41)
    (stateRest : Flushes) (stateAvoids : stateRest.Avoids fun t => t[0] = sepST)
    (stateBalance : (stateRest ++ stateFlushes rows pcEntry pcHalt cycles).Balanced)
    (mem : MemArray) (accesses : List Access)
    (wf : ∀ x ∈ accesses, x.WellFormed) (in_order : ∀ x ∈ accesses, x.InOrder)
    (row_clock : ∀ x ∈ accesses, ∃ r ∈ rows, x.clock = r.clock)
    (rest : Flushes) (avoids : rest.Avoids fun t => t[0] = mem.sep)
    (balance : (rest ++ mem.flushes accesses).Balanced) :
    (∀ x ∈ accesses, x.Live → ∃ i, x.addr = mem.addr i) ∧
    (∀ x ∈ accesses, x.Live →
      (x.prev = 2 ^ 40 ∧ (∀ i, x.addr = mem.addr i → x.old = mem.init i) ∧
          ∀ y ∈ accesses, y.Live → y.addr = x.addr → x.time ≤ y.time) ∨
        ∃ y ∈ accesses, y.Live ∧ y.addr = x.addr ∧ y.time = x.prev ∧ x.old = y.new ∧
          ∀ z ∈ accesses, z.Live → z.addr = x.addr → z.time < x.time → z.time ≤ y.time) ∧
    (∀ i, ((∀ y ∈ accesses, y.Live → y.addr ≠ mem.addr i) ∧ mem.tsfin i = ofWord (2 ^ 40) ∧
          mem.fin i = mem.init i) ∨
        ∃ y ∈ accesses, y.Live ∧ y.addr = mem.addr i ∧ mem.tsfin i = ofWord y.time ∧ mem.fin i = y.new ∧
          ∀ z ∈ accesses, z.Live → z.addr = mem.addr i → z.time ≤ y.time) := by
  obtain ⟨ -, walk, others, perm, -, -, clocks, others_dead, - ⟩ :=
    state_walk rows pcEntry pcHalt cycles cycles_lt clock_lt stateRest stateAvoids stateBalance
  apply memory_consistent mem accesses wf in_order _ rest avoids balance
  intro x hx live
  obtain ⟨ r, hr, hclock ⟩ := row_clock x hx
  unfold Access.Live at live
  unfold Access.time
  rcases List.mem_append.mp (perm.mem_iff.mp hr) with hw | ho
  · obtain ⟨ i, hi, rfl ⟩ := List.getElem_of_mem hw
    have := clocks i hi
    omega
  · have := others_dead r ho
    omega

/-! ### RAM and the advice -/

/--
RAM and the advice share the separator `g^1` (§sec:memchan), at disjoint addresses: as one array, their cells side by
side, `thm:rwmem` applies to both at once.
-/
noncomputable def MemArray.union (ram adv : MemArray)
    (disjoint : ∀ i j, ram.addr i ≠ adv.addr j) : MemArray where
  sep := ram.sep
  size := ram.size + adv.size
  addr := Fin.append ram.addr adv.addr
  addr_injective := by
    intro i j h
    induction i using Fin.addCases with
    | left a =>
      induction j using Fin.addCases with
      | left b => simp only [Fin.append_left] at h; rw [ram.addr_injective h]
      | right b => simp only [Fin.append_left, Fin.append_right] at h; exact absurd h (disjoint a b)
    | right a =>
      induction j using Fin.addCases with
      | left b => simp only [Fin.append_left, Fin.append_right] at h; exact absurd h.symm (disjoint b a)
      | right b => simp only [Fin.append_right] at h; rw [adv.addr_injective h]
  init := Fin.append ram.init adv.init
  fin := Fin.append ram.fin adv.fin
  tsfin := Fin.append ram.tsfin adv.tsfin

theorem finRange_add_map {α : Type} (m n : ℕ) (g : Fin (m + n) → α) :
    (List.finRange (m + n)).map g =
      (List.finRange m).map (fun i => g (Fin.castAdd n i)) ++ (List.finRange n).map (fun i => g (Fin.natAdd m i)) := by
  rw [← List.ofFn_eq_map, List.ofFn_add, List.ofFn_eq_map, List.ofFn_eq_map]
  rfl

/--
`thm:rwmem` for RAM and the advice together: if the seeds, accesses and finalizations of both arrays are the only flushes
under their shared separator, the conclusions of `memory_consistent` hold for the two as one array, every live access
being at a RAM or an advice address.
-/
theorem memory_consistent_shared (ram adv : MemArray) (same_sep : ram.sep = adv.sep)
    (disjoint : ∀ i j, ram.addr i ≠ adv.addr j) (ramAccesses advAccesses : List Access)
    (wf : ∀ x ∈ ramAccesses ++ advAccesses, x.WellFormed) (in_order : ∀ x ∈ ramAccesses ++ advAccesses, x.InOrder)
    (after_seeds : ∀ x ∈ ramAccesses ++ advAccesses, x.Live → 2 ^ 40 < x.time)
    (rest : Flushes) (avoids : rest.Avoids fun t => t[0] = ram.sep)
    (balance : (rest ++ ram.flushes ramAccesses ++ adv.flushes advAccesses).Balanced) :
    let mem := MemArray.union ram adv disjoint
    let accesses := ramAccesses ++ advAccesses
    (∀ x ∈ accesses, x.Live → ∃ i, x.addr = mem.addr i) ∧
    (∀ x ∈ accesses, x.Live →
      (x.prev = 2 ^ 40 ∧ (∀ i, x.addr = mem.addr i → x.old = mem.init i) ∧
          ∀ y ∈ accesses, y.Live → y.addr = x.addr → x.time ≤ y.time) ∨
        ∃ y ∈ accesses, y.Live ∧ y.addr = x.addr ∧ y.time = x.prev ∧ x.old = y.new ∧
          ∀ z ∈ accesses, z.Live → z.addr = x.addr → z.time < x.time → z.time ≤ y.time) ∧
    (∀ i, ((∀ y ∈ accesses, y.Live → y.addr ≠ mem.addr i) ∧ mem.tsfin i = ofWord (2 ^ 40) ∧
          mem.fin i = mem.init i) ∨
        ∃ y ∈ accesses, y.Live ∧ y.addr = mem.addr i ∧ mem.tsfin i = ofWord y.time ∧ mem.fin i = y.new ∧
          ∀ z ∈ accesses, z.Live → z.addr = mem.addr i → z.time ≤ y.time) := by
  intro mem accesses
  apply memory_consistent mem accesses wf in_order after_seeds rest avoids
  rw [Flushes.balanced_iff] at balance ⊢
  have seeds : (List.finRange mem.size).map mem.seed =
      (List.finRange ram.size).map ram.seed ++ (List.finRange adv.size).map adv.seed := by
    refine (finRange_add_map ram.size adv.size mem.seed).trans ?_
    congr 1 <;> apply List.map_congr_left <;> intro i _ <;>
      simp [mem, MemArray.union, MemArray.seed, Fin.append_left, Fin.append_right, same_sep]
  have finals : (List.finRange mem.size).map mem.final =
      (List.finRange ram.size).map ram.final ++ (List.finRange adv.size).map adv.final := by
    refine (finRange_add_map ram.size adv.size mem.final).trans ?_
    congr 1 <;> apply List.map_congr_left <;> intro i _ <;>
      simp [mem, MemArray.union, MemArray.final, Fin.append_left, Fin.append_right, same_sep]
  have pushed_eq : (mem.flushes accesses).pushed =
      (ram.flushes ramAccesses).pushed + (adv.flushes advAccesses).pushed := by
    simp only [Flushes.pushed, MemArray.flushes, seeds, accesses, List.map_append, ← Multiset.coe_add,
      List.map_nil, List.sum_nil, add_zero]
    rw [show mem.sep = ram.sep from rfl, ← same_sep]
    abel
  have pulled_eq : (mem.flushes accesses).pulled =
      (ram.flushes ramAccesses).pulled + (adv.flushes advAccesses).pulled := by
    simp only [Flushes.pulled, MemArray.flushes, finals, accesses, List.map_append, ← Multiset.coe_add]
    rw [show mem.sep = ram.sep from rfl, ← same_sep]
    abel
  simp only [Flushes.pushed_append, Flushes.pulled_append] at balance ⊢
  rw [pushed_eq, pulled_eq, ← add_assoc, ← add_assoc]
  exact balance

end LeanVMCircuits.Bus
