module

public import LeanVMCircuits.Bus.Lookup
public import LeanVMCircuits.Bus.Memory

@[expose] public section

/-!
# The machine's bus

The end-to-end bus theorem of `doc/leanvm/body/06-bus-interactions.tex`, over an abstract row type. A row
(`MachineRow`) makes the flushes the Rust `FlushBuilder` gives a table row: it pulls its state `⟨ST, pc, ts, 0⟩` and
pushes `⟨ST, npc, ts + step, exit⟩`, pulls its bytecode reads `⟨BC, a, v⟩`, and makes its register and memory
accesses, each pulling `⟨sep, a, ts_prev, old⟩` and pushing `⟨sep, a, ts_k, new⟩`. The bus (`Machine.flushes`) is
the rows' flushes, the state boundary, the bytecode producer, and the seeds and finalizations of the registers, RAM
and the advice.

What the row's clock circuit guarantees enters as three hypotheses, `MachineRow.C1` to `MachineRow.C3`: the clock is
a clock, `ts + step` is the next clock, and every access is at its slot's timestamp and in order when the row says
so. Under those, if the bus balances (`machine_correct`), or the product identity holds with Boolean producer bits
(`machine_correct_of_product_check`), every bytecode read is correct, the live rows form one walk from the initial
state to the final one in clock order, and the registers and RAM with the advice are consistent (`Machine.Correct`).
-/

namespace LeanVMCircuits.Bus

open LeanVMCircuits.Rec

/-! ### Separators -/

theorem sep_ne {a b : ℕ} (ha : a < 2 ^ 64) (hb : b < 2 ^ 64) (h : a ≠ b) : ofWord a ≠ ofWord b :=
  fun e => h (ofWord_injective ha hb e)

theorem sepST_ne_sepMEM : sepST ≠ sepMEM := sep_ne (a := 1) (b := 2) (by norm_num) (by norm_num) (by norm_num)
theorem sepST_ne_sepBC : sepST ≠ sepBC := sep_ne (a := 1) (b := 4) (by norm_num) (by norm_num) (by norm_num)
theorem sepST_ne_sepREG : sepST ≠ sepREG := sep_ne (a := 1) (b := 8) (by norm_num) (by norm_num) (by norm_num)
theorem sepMEM_ne_sepBC : sepMEM ≠ sepBC := sep_ne (a := 2) (b := 4) (by norm_num) (by norm_num) (by norm_num)
theorem sepMEM_ne_sepREG : sepMEM ≠ sepREG := sep_ne (a := 2) (b := 8) (by norm_num) (by norm_num) (by norm_num)
theorem sepBC_ne_sepREG : sepBC ≠ sepREG := sep_ne (a := 4) (b := 8) (by norm_num) (by norm_num) (by norm_num)

/-! ### Flushes under one separator -/

namespace Flushes

/-- Every tuple of the flushes carries the separator `s`. -/
def Carries (f : Flushes) (s : K) : Prop :=
  (∀ t ∈ f.pushes, t[0] = s) ∧ (∀ t ∈ f.pulls, t[0] = s) ∧ ∀ p ∈ f.produced, p.1[0] = s

theorem Carries.avoids {f : Flushes} {s s' : K} (hf : f.Carries s) (ne : s ≠ s') :
    f.Avoids fun t => t[0] = s' :=
  ⟨ fun t ht h => ne ((hf.1 t ht).symm.trans h), fun t ht h => ne ((hf.2.1 t ht).symm.trans h),
    fun p hp _ h => ne ((hf.2.2 p hp).symm.trans h) ⟩

theorem Avoids.append {f g : Flushes} {S : Tuple → Prop} (hf : f.Avoids S) (hg : g.Avoids S) :
    (f ++ g).Avoids S := by
  refine ⟨ fun t ht => ?_, fun t ht => ?_, fun p hp => ?_ ⟩
  · simp only [append_pushes, List.mem_append] at ht
    rcases ht with ht | ht
    · exact hf.1 t ht
    · exact hg.1 t ht
  · simp only [append_pulls, List.mem_append] at ht
    rcases ht with ht | ht
    · exact hf.2.1 t ht
    · exact hg.2.1 t ht
  · simp only [append_produced, List.mem_append] at hp
    rcases hp with hp | hp
    · exact hf.2.2 p hp
    · exact hg.2.2 p hp

/-- Balance depends only on the pushed and pulled multisets. -/
theorem balanced_of_eq {f g : Flushes} (pushed_eq : f.pushed = g.pushed) (pulled_eq : f.pulled = g.pulled)
    (balance : f.Balanced) : g.Balanced := by
  rw [balanced_iff] at balance ⊢
  rw [← pushed_eq, ← pulled_eq]
  exact balance

end Flushes

theorem stateFlushes_carries (rows : List StateRow) (pcEntry pcHalt : K) (cycles : ℕ) :
    (stateFlushes rows pcEntry pcHalt cycles).Carries sepST := by
  refine ⟨ fun t ht => ?_, fun t ht => ?_, fun p hp => ?_ ⟩
  · simp only [stateFlushes, List.mem_cons, List.mem_map] at ht
    rcases ht with rfl | ⟨ r, -, rfl ⟩
    · simp [initialState, tuple_get]
    · exact r.push_sep
  · simp only [stateFlushes, List.mem_cons, List.mem_map] at ht
    rcases ht with rfl | ⟨ r, -, rfl ⟩
    · simp [finalState, tuple_get]
    · exact r.pull_sep
  · simp [stateFlushes] at hp

theorem LookupArray.flushes_carries {n : ℕ} (lut : LookupArray n) (mult : Fin lut.size → ℕ)
    (reads : List (K × Vector K n)) : (lut.flushes mult reads).Carries lut.sep := by
  refine ⟨ fun t ht => ?_, fun t ht => ?_, fun p hp => ?_ ⟩
  · simp [LookupArray.flushes] at ht
  · simp only [LookupArray.flushes, List.mem_map] at ht
    obtain ⟨ r, -, rfl ⟩ := ht
    exact lut.readTuple_sep _ _
  · simp only [LookupArray.flushes, List.mem_map, List.mem_finRange, true_and] at hp
    obtain ⟨ i, rfl ⟩ := hp
    exact lut.readTuple_sep _ _

theorem MemArray.flushes_carries (mem : MemArray) (accesses : List Access) :
    (mem.flushes accesses).Carries mem.sep := by
  refine ⟨ fun t ht => ?_, fun t ht => ?_, fun p hp => ?_ ⟩
  · simp only [MemArray.flushes, List.mem_append, List.mem_map, List.mem_finRange, true_and] at ht
    rcases ht with ⟨ i, rfl ⟩ | ⟨ x, -, rfl ⟩
    · simp [MemArray.seed, tuple_get]
    · simp [Access.push, tuple_get]
  · simp only [MemArray.flushes, List.mem_append, List.mem_map, List.mem_finRange, true_and] at ht
    rcases ht with ⟨ x, -, rfl ⟩ | ⟨ i, rfl ⟩
    · simp [Access.pull, tuple_get]
    · simp [MemArray.final, tuple_get]
  · simp [MemArray.flushes] at hp

theorem stateFlushes_pushed (rows : List StateRow) (pcEntry pcHalt : K) (cycles : ℕ) :
    (stateFlushes rows pcEntry pcHalt cycles).pushed =
      {initialState pcEntry} + ((rows.map StateRow.push : List Tuple) : Multiset Tuple) := by
  simp [stateFlushes, Flushes.pushed]

theorem stateFlushes_pulled (rows : List StateRow) (pcEntry pcHalt : K) (cycles : ℕ) :
    (stateFlushes rows pcEntry pcHalt cycles).pulled =
      {finalState pcHalt cycles} + ((rows.map StateRow.pull : List Tuple) : Multiset Tuple) := by
  simp [stateFlushes, Flushes.pulled]

theorem MemArray.flushes_pushed (mem : MemArray) (accesses : List Access) :
    (mem.flushes accesses).pushed = (((List.finRange mem.size).map mem.seed : List Tuple) : Multiset Tuple) +
      ((accesses.map (Access.push mem.sep) : List Tuple) : Multiset Tuple) := by
  simp [MemArray.flushes, Flushes.pushed]

theorem MemArray.flushes_pulled (mem : MemArray) (accesses : List Access) :
    (mem.flushes accesses).pulled = ((accesses.map (Access.pull mem.sep) : List Tuple) : Multiset Tuple) +
      (((List.finRange mem.size).map mem.final : List Tuple) : Multiset Tuple) := by
  simp [MemArray.flushes, Flushes.pulled]

/-! ### Rows -/

/-- An access as a row makes it: it pulls `⟨sep, addr, prev, old⟩` and pushes `⟨sep, addr, ts, new⟩`, where `ts` is
the timestamp coordinate of its slot (the row's clock column, plus the slot's constant for a nonzero slot). -/
structure RowAccess where
  addr : K
  slot : ℕ
  ts : K
  prev : K
  old : K
  new : K

namespace RowAccess

/-- The tuple an access pulls. -/
noncomputable def pull (sep : K) (x : RowAccess) : Tuple := tuple [sep, x.addr, x.prev, x.old]

/-- The tuple an access pushes. -/
noncomputable def push (sep : K) (x : RowAccess) : Tuple := tuple [sep, x.addr, x.ts, x.new]

end RowAccess

/-- The tuple a bytecode read of `v` at `a` pulls, `⟨BC, a, v⟩`. -/
noncomputable def bytecodeRead (q : K × Vector K 10) : Tuple := tuple (sepBC :: q.1 :: q.2.toList)

/--
A row of a table, as its flushes see it: the state columns `pc`, `ts`, `step`, `npc`, `exit`; the verdict `inOrder`
of its clock circuit's order check; its bytecode reads; and its register and memory (RAM or advice) accesses.
-/
structure MachineRow where
  pc : K
  ts : K
  step : K
  npc : K
  exit : K
  inOrder : Bool
  reads : List (K × Vector K 10)
  regs : List RowAccess
  mems : List RowAccess

namespace MachineRow

variable (r : MachineRow)

/-- The integer the row's clock column names. -/
noncomputable def clock : ℕ := toWord r.ts

/-- An access of the row as the memory theorem sees it: at the row's clock, its previous timestamp as an integer. -/
noncomputable def access (x : RowAccess) : Access := ⟨ x.addr, r.clock, x.slot, toWord x.prev, x.old, x.new ⟩

/-- The row's part in the state interaction. -/
noncomputable def state : StateRow := ⟨ r.pc, r.clock, r.npc, r.exit, r.inOrder ⟩

/-- The state the row pulls, `⟨ST, pc, ts, 0⟩`. -/
noncomputable def statePull : Tuple := tuple [sepST, r.pc, r.ts, 0]

/-- The state the row pushes, `⟨ST, npc, ts + step, exit⟩`. -/
noncomputable def statePush : Tuple := tuple [sepST, r.npc, r.ts + r.step, r.exit]

/-- The row's flushes, as the Rust `FlushBuilder` makes them. -/
noncomputable def flushes : Flushes where
  pushes := r.statePush :: (r.regs.map (RowAccess.push sepREG) ++ r.mems.map (RowAccess.push sepMEM))
  pulls := r.statePull :: (r.reads.map bytecodeRead ++ r.regs.map (RowAccess.pull sepREG) ++
    r.mems.map (RowAccess.pull sepMEM))

/-- Clock fact C1: the row's clock is below `2^41`, its five slot bits clear. -/
def C1 : Prop := r.clock < 2 ^ 41 ∧ 2 ^ 5 ∣ r.clock

/-- Clock fact C2: the clock the row pushes is the next clock, `ts + step = nextClock clock inOrder`. -/
def C2 : Prop := r.ts + r.step = ofWord (nextClock r.clock r.inOrder)

/-- Clock fact C3: the row's accesses are in pairwise distinct slots below `2^5`, each at the timestamp
`clock + slot` with a previous timestamp below `2^41`, and each satisfies the order check `eq:order` when the row
is in order. -/
def C3 : Prop :=
  ((r.regs ++ r.mems).map RowAccess.slot).Nodup ∧
    ∀ x ∈ r.regs ++ r.mems, x.slot < 2 ^ 5 ∧ x.ts = ofWord (r.clock + x.slot) ∧ toWord x.prev < 2 ^ 41 ∧
      (r.inOrder = true → (r.access x).InOrder)

theorem state_pull : r.state.pull = r.statePull := by
  simp only [StateRow.pull, statePull, state, clock, ofWord_toWord]

theorem state_push (c2 : r.C2) : r.state.push = r.statePush := by
  simp only [StateRow.push, statePush, state]
  rw [show r.ts + r.step = ofWord (nextClock r.clock r.inOrder) from c2]

theorem access_pull (sep : K) (x : RowAccess) : (r.access x).pull sep = x.pull sep := by
  simp only [Access.pull, RowAccess.pull, access, ofWord_toWord]

theorem access_push (c1 : r.C1) (x : RowAccess) (slot_lt : x.slot < 2 ^ 5) (ts_eq : x.ts = ofWord (r.clock + x.slot))
    (sep : K) : (r.access x).push sep = x.push sep := by
  obtain ⟨ clock_lt, q, hq ⟩ := c1
  have sum : ofWord r.clock + ofWord x.slot = x.ts := by
    rw [ts_eq, hq]
    exact ofWord_add_slot q x.slot slot_lt (by omega)
  show tuple [sep, x.addr, ofWord r.clock + ofWord x.slot, x.new] = tuple [sep, x.addr, x.ts, x.new]
  rw [sum]

theorem flushes_pushes (c1 : r.C1) (c2 : r.C2) (c3 : r.C3) :
    (r.flushes.pushes : Multiset Tuple) = {r.state.push} +
      (((r.regs.map r.access).map (Access.push sepREG) : List Tuple) : Multiset Tuple) +
      (((r.mems.map r.access).map (Access.push sepMEM) : List Tuple) : Multiset Tuple) := by
  obtain ⟨ -, facts ⟩ := c3
  have push_eq : ∀ sep, ∀ l : List RowAccess, (∀ x ∈ l, x ∈ r.regs ++ r.mems) →
      (l.map r.access).map (Access.push sep) = l.map (RowAccess.push sep) := by
    intro sep l hl
    rw [List.map_map]
    apply List.map_congr_left
    intro x hx
    obtain ⟨ slot_lt, ts_eq, - ⟩ := facts x (hl x hx)
    exact r.access_push c1 x slot_lt ts_eq sep
  rw [push_eq sepREG r.regs (fun _ hx => List.mem_append_left _ hx),
    push_eq sepMEM r.mems (fun _ hx => List.mem_append_right _ hx), r.state_push c2]
  simp only [flushes, ← Multiset.coe_add, ← Multiset.cons_coe, ← Multiset.singleton_add]
  abel

theorem flushes_pulls :
    (r.flushes.pulls : Multiset Tuple) = {r.state.pull} + ((r.reads.map bytecodeRead : List Tuple) : Multiset Tuple) +
      (((r.regs.map r.access).map (Access.pull sepREG) : List Tuple) : Multiset Tuple) +
      (((r.mems.map r.access).map (Access.pull sepMEM) : List Tuple) : Multiset Tuple) := by
  have pull_eq : ∀ sep, ∀ l : List RowAccess, (l.map r.access).map (Access.pull sep) = l.map (RowAccess.pull sep) := by
    intro sep l
    rw [List.map_map]
    exact List.map_congr_left fun x _ => r.access_pull sep x
  rw [pull_eq, pull_eq, r.state_pull]
  simp only [flushes, ← Multiset.coe_add, ← Multiset.cons_coe, ← Multiset.singleton_add]
  abel

end MachineRow

/-- The register accesses of the rows. -/
noncomputable def regAccesses (rows : List MachineRow) : List Access := rows.flatMap fun r => r.regs.map r.access

/-- The memory (RAM and advice) accesses of the rows. -/
noncomputable def memAccesses (rows : List MachineRow) : List Access := rows.flatMap fun r => r.mems.map r.access

/-- The rows' flushes, together. -/
noncomputable def rowFlushes (rows : List MachineRow) : Flushes where
  pushes := rows.flatMap fun r => r.flushes.pushes
  pulls := rows.flatMap fun r => r.flushes.pulls

theorem rows_pushes (rows : List MachineRow) (c1 : ∀ r ∈ rows, r.C1) (c2 : ∀ r ∈ rows, r.C2)
    (c3 : ∀ r ∈ rows, r.C3) :
    ((rows.flatMap fun r => r.flushes.pushes : List Tuple) : Multiset Tuple) =
      (((rows.map MachineRow.state).map StateRow.push : List Tuple) : Multiset Tuple) +
      (((regAccesses rows).map (Access.push sepREG) : List Tuple) : Multiset Tuple) +
      (((memAccesses rows).map (Access.push sepMEM) : List Tuple) : Multiset Tuple) := by
  induction rows with
  | nil => simp [regAccesses, memAccesses]
  | cons r rows ih =>
    have ih' := ih (fun r' h => c1 r' (List.mem_cons_of_mem _ h)) (fun r' h => c2 r' (List.mem_cons_of_mem _ h))
      (fun r' h => c3 r' (List.mem_cons_of_mem _ h))
    have mem := List.mem_cons_self (a := r) (l := rows)
    simp only [List.flatMap_cons, ← Multiset.coe_add]
    rw [r.flushes_pushes (c1 r mem) (c2 r mem) (c3 r mem), ih']
    simp only [regAccesses, memAccesses, List.flatMap_cons, List.map_cons, List.map_append, ← Multiset.coe_add,
      ← Multiset.cons_coe, ← Multiset.singleton_add]
    abel

theorem rows_pulls (rows : List MachineRow) :
    ((rows.flatMap fun r => r.flushes.pulls : List Tuple) : Multiset Tuple) =
      (((rows.map MachineRow.state).map StateRow.pull : List Tuple) : Multiset Tuple) +
      (((rows.flatMap MachineRow.reads).map bytecodeRead : List Tuple) : Multiset Tuple) +
      (((regAccesses rows).map (Access.pull sepREG) : List Tuple) : Multiset Tuple) +
      (((memAccesses rows).map (Access.pull sepMEM) : List Tuple) : Multiset Tuple) := by
  induction rows with
  | nil => simp [regAccesses, memAccesses]
  | cons r rows ih =>
    simp only [List.flatMap_cons, ← Multiset.coe_add]
    rw [r.flushes_pulls, ih]
    simp only [regAccesses, memAccesses, List.flatMap_cons, List.map_cons, List.map_append, ← Multiset.coe_add,
      ← Multiset.cons_coe, ← Multiset.singleton_add]
    abel

/-- Lift a permutation of the images of a list's elements to a permutation of the list. -/
theorem exists_perm_of_map_perm {α β : Type} [DecidableEq α] (f : α → β) (b : List β) :
    ∀ l : List α, (l.map f).Perm b → ∃ l', l.Perm l' ∧ l'.map f = b := by
  induction b with
  | nil =>
    intro l h
    exact ⟨ [], by simpa using h, rfl ⟩
  | cons y b ih =>
    intro l h
    obtain ⟨ x, x_mem, rfl ⟩ := List.mem_map.mp (h.symm.subset (List.mem_cons_self ..))
    have perm := List.perm_cons_erase x_mem
    have h' : ((l.erase x).map f).Perm b := by simpa using (perm.map f).symm.trans h
    obtain ⟨ l', hl', rfl ⟩ := ih (l.erase x) h'
    exact ⟨ x :: l', perm.trans (hl'.cons x), rfl ⟩

theorem MachineRow.isWalk_of_state (f : Tuple) (w : List MachineRow) (c2 : ∀ r ∈ w, r.C2) :
    ∀ s, IsWalk StateRow.pull StateRow.push s f (w.map MachineRow.state) →
      IsWalk MachineRow.statePull MachineRow.statePush s f w := by
  induction w with
  | nil => intro s h; exact h
  | cons r w ih =>
    intro s h
    simp only [List.map_cons, IsWalk] at h ⊢
    rw [← r.state_pull, ← r.state_push (c2 r (List.mem_cons_self ..))]
    exact ⟨ h.1, ih (fun r' hr' => c2 r' (List.mem_cons_of_mem _ hr')) _ h.2 ⟩

/-! ### The machine -/

/--
The public data of a run and the committed final columns: the boundary states (`cycles` sets the final clock
`2^40 + 2^5 cycles`), the bytecode with its decoding, and the registers, RAM and the advice as read-write arrays
under their separators, RAM and the advice at disjoint addresses.
-/
structure Machine where
  pcEntry : K
  pcHalt : K
  cycles : ℕ
  cycles_lt : cycles < 2 ^ 35
  tbase : ℕ
  kbc : ℕ
  fits : tbase + 4 * 2 ^ kbc ≤ 2 ^ 64
  decoded : Fin (2 ^ kbc) → Vector K 10
  reg : MemArray
  ram : MemArray
  adv : MemArray
  reg_sep : reg.sep = sepREG
  ram_sep : ram.sep = sepMEM
  adv_sep : adv.sep = sepMEM
  disjoint : ∀ i j, ram.addr i ≠ adv.addr j

/-- The consistency `thm:rwmem` concludes for one array: every live access is at a cell of the array; each reads
either the cell's initial value, being its earliest live access, or the value the latest earlier live access at the
cell wrote; and each cell's final value and last timestamp are those of its latest live access, or its initial value
and `2^40` if it has none. -/
def MemArray.Consistent (mem : MemArray) (accesses : List Access) : Prop :=
  (∀ x ∈ accesses, x.Live → ∃ i, x.addr = mem.addr i) ∧
  (∀ x ∈ accesses, x.Live →
    (x.prev = 2 ^ 40 ∧ (∀ i, x.addr = mem.addr i → x.old = mem.init i) ∧
        ∀ y ∈ accesses, y.Live → y.addr = x.addr → x.time ≤ y.time) ∨
      ∃ y ∈ accesses, y.Live ∧ y.addr = x.addr ∧ y.time = x.prev ∧ x.old = y.new ∧
        ∀ z ∈ accesses, z.Live → z.addr = x.addr → z.time < x.time → z.time ≤ y.time) ∧
  (∀ i, ((∀ y ∈ accesses, y.Live → y.addr ≠ mem.addr i) ∧ mem.tsfin i = ofWord (2 ^ 40) ∧
        mem.fin i = mem.init i) ∨
      ∃ y ∈ accesses, y.Live ∧ y.addr = mem.addr i ∧ mem.tsfin i = ofWord y.time ∧ mem.fin i = y.new ∧
        ∀ z ∈ accesses, z.Live → z.addr = mem.addr i → z.time ≤ y.time)

namespace Machine

variable (m : Machine)

/-- The bytecode as a lookup array. -/
noncomputable def lut : LookupArray 10 := bytecode m.tbase m.kbc m.fits m.decoded

/-- The state boundary: `σ_initial` pushed, `σ_final` pulled. -/
noncomputable def boundary : Flushes where
  pushes := [initialState m.pcEntry]
  pulls := [finalState m.pcHalt m.cycles]

/-- Every flush but the bytecode producer's: the rows', the state boundary, the seeds and finalizations. -/
noncomputable def tableFlushes (rows : List MachineRow) : Flushes :=
  rowFlushes rows ++ m.boundary ++ m.reg.flushes [] ++ m.ram.flushes [] ++ m.adv.flushes []

/-- The bus, the bytecode producer pushing entry `i` with multiplicity `mult i`. -/
noncomputable def flushes (mult : Fin (2 ^ m.kbc) → ℕ) (rows : List MachineRow) : Flushes :=
  m.tableFlushes rows ++ m.lut.flushes mult []

theorem boundary_pushed : m.boundary.pushed = {initialState m.pcEntry} := by
  simp [boundary, Flushes.pushed]

theorem boundary_pulled : m.boundary.pulled = {finalState m.pcHalt m.cycles} := by
  simp [boundary, Flushes.pulled]

theorem rowFlushes_pushed (rows : List MachineRow) :
    (rowFlushes rows).pushed = ((rows.flatMap fun r => r.flushes.pushes : List Tuple) : Multiset Tuple) := by
  simp [rowFlushes, Flushes.pushed]

theorem rowFlushes_pulled (rows : List MachineRow) :
    (rowFlushes rows).pulled = ((rows.flatMap fun r => r.flushes.pulls : List Tuple) : Multiset Tuple) := rfl

/-- Regrouped by separator, the bus pushes the state, bytecode, register and memory flushes. -/
theorem flushes_pushed (mult : Fin (2 ^ m.kbc) → ℕ) (rows : List MachineRow) (c1 : ∀ r ∈ rows, r.C1)
    (c2 : ∀ r ∈ rows, r.C2) (c3 : ∀ r ∈ rows, r.C3) :
    (m.flushes mult rows).pushed =
      (stateFlushes (rows.map MachineRow.state) m.pcEntry m.pcHalt m.cycles).pushed +
      (m.lut.flushes mult (rows.flatMap MachineRow.reads)).pushed +
      (m.reg.flushes (regAccesses rows)).pushed + (m.ram.flushes (memAccesses rows)).pushed +
      (m.adv.flushes []).pushed := by
  have lut_pushed : (m.lut.flushes mult (rows.flatMap MachineRow.reads)).pushed =
      (m.lut.flushes mult []).pushed := rfl
  rw [lut_pushed]
  simp only [flushes, tableFlushes, Flushes.pushed_append, rowFlushes_pushed, rows_pushes rows c1 c2 c3,
    boundary_pushed, MemArray.flushes_pushed, stateFlushes_pushed, m.reg_sep, m.ram_sep, List.map_nil,
    Multiset.coe_nil, add_zero]
  abel

/-- Regrouped by separator, the bus pulls the state, bytecode, register and memory flushes. -/
theorem flushes_pulled (mult : Fin (2 ^ m.kbc) → ℕ) (rows : List MachineRow) :
    (m.flushes mult rows).pulled =
      (stateFlushes (rows.map MachineRow.state) m.pcEntry m.pcHalt m.cycles).pulled +
      (m.lut.flushes mult (rows.flatMap MachineRow.reads)).pulled +
      (m.reg.flushes (regAccesses rows)).pulled + (m.ram.flushes (memAccesses rows)).pulled +
      (m.adv.flushes []).pulled := by
  have lut_pulled : (m.lut.flushes mult (rows.flatMap MachineRow.reads)).pulled =
      (((rows.flatMap MachineRow.reads).map bytecodeRead : List Tuple) : Multiset Tuple) := rfl
  have lut_pulled_nil : (m.lut.flushes mult []).pulled = 0 := by
    simp [LookupArray.flushes, Flushes.pulled]
  rw [lut_pulled]
  simp only [flushes, tableFlushes, Flushes.pulled_append, lut_pulled_nil, rowFlushes_pulled, rows_pulls rows,
    boundary_pulled, MemArray.flushes_pulled, stateFlushes_pulled, m.reg_sep, m.ram_sep, List.map_nil,
    Multiset.coe_nil, add_zero, zero_add]
  abel

/--
What the bus proves of a run, the bytecode producer pushing entry `i` with multiplicity `mult i`:
every bytecode read is the decoded entry at an instruction address, entry `i` being read `mult i` times;
every row is in order; the rows split into a walk from `σ_initial` to `σ_final`, its `i`-th row having the live
clock `2^40 + 2^5 (i + 1)`, and other rows, whose clocks lack the live bit, so that the live rows are exactly the
walk's, and the walk's accesses have pairwise distinct timestamps;
and the registers, and RAM with the advice as one array, are consistent (`MemArray.Consistent`).
-/
def Correct (mult : Fin (2 ^ m.kbc) → ℕ) (rows : List MachineRow) : Prop :=
  (∀ r ∈ rows, ∀ q ∈ r.reads, ∃ i : Fin (2 ^ m.kbc), q = (ofWord (m.tbase + 4 * i), m.decoded i)) ∧
  (∀ i : Fin (2 ^ m.kbc), Multiset.count (ofWord (m.tbase + 4 * i), m.decoded i)
    ((rows.flatMap MachineRow.reads : List (K × Vector K 10)) : Multiset (K × Vector K 10)) = mult i) ∧
  (∀ r ∈ rows, r.inOrder = true) ∧
  (∃ walk others : List MachineRow, rows.Perm (walk ++ others) ∧
    IsWalk MachineRow.statePull MachineRow.statePush (initialState m.pcEntry) (finalState m.pcHalt m.cycles) walk ∧
    walk.length + 1 = m.cycles ∧
    (∀ i (hi : i < walk.length), walk[i].clock = 2 ^ 40 + 2 ^ 5 * (i + 1)) ∧
    (∀ r ∈ rows, 2 ^ 40 ≤ r.clock ↔ r ∈ walk) ∧
    (∀ r ∈ others, r.clock < 2 ^ 40) ∧
    (walk.flatMap fun r => (r.regs ++ r.mems).map fun x => (r.access x).time).Nodup) ∧
  m.reg.Consistent (regAccesses rows) ∧
  (MemArray.union m.ram m.adv m.disjoint).Consistent (memAccesses rows)

end Machine

/--
The end-to-end bus theorem. If every row's clock circuit gives the clock facts C1 to C3 and the bus balances, the
bytecode producer pushing entry `i` with multiplicity `mult i`, then every bytecode read is correct, the live rows
form one walk from the initial state to the final one in clock order, and the register and RAM/advice accesses are
consistent (`Machine.Correct`).
-/
theorem machine_correct (m : Machine) (rows : List MachineRow) (mult : Fin (2 ^ m.kbc) → ℕ)
    (c1 : ∀ r ∈ rows, r.C1) (c2 : ∀ r ∈ rows, r.C2) (c3 : ∀ r ∈ rows, r.C3)
    (balance : (m.flushes mult rows).Balanced) : m.Correct mult rows := by
  classical
  unfold Machine.Correct
  have pushed_eq := m.flushes_pushed mult rows c1 c2 c3
  have pulled_eq := m.flushes_pulled mult rows
  have regroup : ∀ g : Flushes, g.pushed = (m.flushes mult rows).pushed → g.pulled = (m.flushes mult rows).pulled →
      g.Balanced := fun g h1 h2 => Flushes.balanced_of_eq h1.symm h2.symm balance
  -- the components and their separators
  have stC := stateFlushes_carries (rows.map MachineRow.state) m.pcEntry m.pcHalt m.cycles
  have bcC := m.lut.flushes_carries mult (rows.flatMap MachineRow.reads)
  have regC := m.reg.flushes_carries (regAccesses rows)
  have ramC := m.ram.flushes_carries (memAccesses rows)
  have advC := m.adv.flushes_carries []
  have reg_ne : ∀ {s : K}, s ≠ sepREG → m.reg.sep ≠ s := fun h => by rw [m.reg_sep]; exact h.symm
  have ram_ne : ∀ {s : K}, s ≠ sepMEM → m.ram.sep ≠ s := fun h => by rw [m.ram_sep]; exact h.symm
  have adv_ne : ∀ {s : K}, s ≠ sepMEM → m.adv.sep ≠ s := fun h => by rw [m.adv_sep]; exact h.symm
  -- the bytecode reads
  obtain ⟨ reads_ok, counts ⟩ := m.lut.lookup_correct (by norm_num) mult (rows.flatMap MachineRow.reads)
    (stateFlushes (rows.map MachineRow.state) m.pcEntry m.pcHalt m.cycles ++ m.reg.flushes (regAccesses rows) ++
      m.ram.flushes (memAccesses rows) ++ m.adv.flushes [])
    ((((stC.avoids (sepST_ne_sepBC : sepST ≠ m.lut.sep)).append
      (regC.avoids (reg_ne sepBC_ne_sepREG))).append (ramC.avoids (ram_ne sepMEM_ne_sepBC.symm))).append
      (advC.avoids (adv_ne sepMEM_ne_sepBC.symm)))
    (regroup _ (by rw [pushed_eq]; simp only [Flushes.pushed_append]; abel)
      (by rw [pulled_eq]; simp only [Flushes.pulled_append]; abel))
  -- the state walk
  have clock_lt : ∀ r ∈ rows, r.clock < 2 ^ 41 := fun r hr => by
    obtain ⟨ h, - ⟩ := c1 r hr
    exact h
  obtain ⟨ in_order, walk0, others0, perm0, is_walk0, length0, clocks0, dead0, - ⟩ :=
    state_walk (rows.map MachineRow.state) m.pcEntry m.pcHalt m.cycles m.cycles_lt
      (fun s hs => by
        obtain ⟨ r, hr, rfl ⟩ := List.mem_map.mp hs
        exact clock_lt r hr)
      (m.lut.flushes mult (rows.flatMap MachineRow.reads) ++ m.reg.flushes (regAccesses rows) ++
        m.ram.flushes (memAccesses rows) ++ m.adv.flushes [])
      ((((bcC.avoids (sepST_ne_sepBC.symm : m.lut.sep ≠ sepST)).append
        (regC.avoids (reg_ne sepST_ne_sepREG))).append (ramC.avoids (ram_ne sepST_ne_sepMEM))).append
        (advC.avoids (adv_ne sepST_ne_sepMEM)))
      (regroup _ (by rw [pushed_eq]; simp only [Flushes.pushed_append]; abel)
        (by rw [pulled_eq]; simp only [Flushes.pulled_append]; abel))
  have in_order' : ∀ r ∈ rows, r.inOrder = true := fun r hr => in_order r.state (List.mem_map_of_mem hr)
  obtain ⟨ rows', perm', map_eq ⟩ := exists_perm_of_map_perm MachineRow.state _ rows perm0
  obtain ⟨ walk, others, rfl, rfl, rfl ⟩ := List.map_eq_append_iff.mp map_eq
  have walk_mem : ∀ r ∈ walk, r ∈ rows := fun r hr => perm'.symm.subset (List.mem_append_left _ hr)
  have clocks : ∀ i (hi : i < walk.length), walk[i].clock = 2 ^ 40 + 2 ^ 5 * (i + 1) := by
    intro i hi
    have := clocks0 i (by simpa using hi)
    simpa [MachineRow.state] using this
  have dead : ∀ r ∈ others, r.clock < 2 ^ 40 := fun r hr => dead0 r.state (List.mem_map_of_mem hr)
  have live_walk : ∀ r ∈ walk, 2 ^ 40 + 2 ^ 5 ≤ r.clock := by
    intro r hr
    obtain ⟨ i, hi, rfl ⟩ := List.getElem_of_mem hr
    have := clocks i hi
    omega
  have live_iff : ∀ r ∈ rows, 2 ^ 40 ≤ r.clock ↔ r ∈ walk := by
    intro r hr
    constructor
    · intro live
      rcases List.mem_append.mp (perm'.subset hr) with h | h
      · exact h
      · have := dead r h
        omega
    · intro h
      have := live_walk r h
      omega
  -- the accesses
  have access_facts : ∀ r ∈ rows, ∀ y ∈ r.regs ++ r.mems,
      (r.clock < 2 ^ 41 ∧ 2 ^ 5 ∣ r.clock ∧ y.slot < 2 ^ 5 ∧ toWord y.prev < 2 ^ 41) ∧ (r.access y).InOrder ∧
        (2 ^ 40 ≤ r.clock → 2 ^ 40 < r.clock + y.slot) := by
    intro r hr y hy
    obtain ⟨ clock_lt', clock_dvd ⟩ := c1 r hr
    obtain ⟨ -, facts ⟩ := c3 r hr
    obtain ⟨ slot_lt, -, prev_lt, ordered ⟩ := facts y hy
    refine ⟨ ⟨ clock_lt', clock_dvd, slot_lt, prev_lt ⟩, ordered (in_order' r hr), fun live => ?_ ⟩
    have := live_walk r ((live_iff r hr).mp live)
    omega
  have reg_facts : ∀ x ∈ regAccesses rows, x.WellFormed ∧ x.InOrder ∧ (x.Live → 2 ^ 40 < x.time) := by
    intro x hx
    simp only [regAccesses, List.mem_flatMap, List.mem_map] at hx
    obtain ⟨ r, hr, y, hy, rfl ⟩ := hx
    obtain ⟨ wf, io, after ⟩ := access_facts r hr y (List.mem_append_left _ hy)
    exact ⟨ wf, io, after ⟩
  have mem_facts : ∀ x ∈ memAccesses rows, x.WellFormed ∧ x.InOrder ∧ (x.Live → 2 ^ 40 < x.time) := by
    intro x hx
    simp only [memAccesses, List.mem_flatMap, List.mem_map] at hx
    obtain ⟨ r, hr, y, hy, rfl ⟩ := hx
    obtain ⟨ wf, io, after ⟩ := access_facts r hr y (List.mem_append_right _ hy)
    exact ⟨ wf, io, after ⟩
  -- the registers
  have reg_ok := memory_consistent m.reg (regAccesses rows) (fun x hx => (reg_facts x hx).1)
    (fun x hx => (reg_facts x hx).2.1) (fun x hx => (reg_facts x hx).2.2)
    (stateFlushes (rows.map MachineRow.state) m.pcEntry m.pcHalt m.cycles ++
      m.lut.flushes mult (rows.flatMap MachineRow.reads) ++ m.ram.flushes (memAccesses rows) ++ m.adv.flushes [])
    ((((stC.avoids (reg_ne sepST_ne_sepREG).symm).append
      (bcC.avoids ((reg_ne sepBC_ne_sepREG).symm : m.lut.sep ≠ m.reg.sep))).append
      (ramC.avoids (by rw [m.reg_sep, m.ram_sep]; exact sepMEM_ne_sepREG))).append
      (advC.avoids (by rw [m.reg_sep, m.adv_sep]; exact sepMEM_ne_sepREG)))
    (regroup _ (by rw [pushed_eq]; simp only [Flushes.pushed_append]; abel)
      (by rw [pulled_eq]; simp only [Flushes.pulled_append]; abel))
  -- RAM and the advice
  have mem_ok := memory_consistent_shared m.ram m.adv (m.ram_sep.trans m.adv_sep.symm) m.disjoint
    (memAccesses rows) [] (fun x hx => (mem_facts x (by simpa using hx)).1)
    (fun x hx => (mem_facts x (by simpa using hx)).2.1) (fun x hx => (mem_facts x (by simpa using hx)).2.2)
    (stateFlushes (rows.map MachineRow.state) m.pcEntry m.pcHalt m.cycles ++
      m.lut.flushes mult (rows.flatMap MachineRow.reads) ++ m.reg.flushes (regAccesses rows))
    (((stC.avoids (ram_ne sepST_ne_sepMEM).symm).append
      (bcC.avoids ((ram_ne sepMEM_ne_sepBC.symm).symm : m.lut.sep ≠ m.ram.sep))).append
      (regC.avoids (by rw [m.reg_sep, m.ram_sep]; exact sepMEM_ne_sepREG.symm)))
    (regroup _ (by rw [pushed_eq]; simp only [Flushes.pushed_append])
      (by rw [pulled_eq]; simp only [Flushes.pulled_append]))
  simp only [List.append_nil] at mem_ok
  refine ⟨ fun r hr q hq => reads_ok q (List.mem_flatMap.mpr ⟨ r, hr, hq ⟩), counts, in_order',
    ⟨ walk, others, perm', ?_, by simpa using length0, clocks, live_iff, dead, ?_ ⟩, reg_ok, mem_ok ⟩
  · exact MachineRow.isWalk_of_state _ walk (fun r hr => c2 r (walk_mem r hr)) _ is_walk0
  · -- the walk's accesses have pairwise distinct timestamps
    rw [List.nodup_flatMap]
    constructor
    · intro r hr
      obtain ⟨ slots, - ⟩ := c3 r (walk_mem r hr)
      have eq : ((r.regs ++ r.mems).map fun x => (r.access x).time) =
          ((r.regs ++ r.mems).map RowAccess.slot).map fun k => r.clock + k := by
        rw [List.map_map]
        rfl
      rw [eq]
      exact List.Nodup.map (fun a b h => by simpa using h) slots
    · rw [List.pairwise_iff_getElem]
      intro i j hi hj hij
      simp only [Function.onFun]
      intro t ti tj
      simp only [List.mem_map] at ti tj
      obtain ⟨ x, hx, rfl ⟩ := ti
      obtain ⟨ y, hy, eq ⟩ := tj
      have xs := (access_facts _ (walk_mem _ (List.getElem_mem hi)) x hx).1.2.2.1
      have ys := (access_facts _ (walk_mem _ (List.getElem_mem hj)) y hy).1.2.2.1
      have ci := clocks i hi
      have cj := clocks j hj
      simp only [Access.time, MachineRow.access] at eq
      omega

/--
The end-to-end bus theorem from the product check: if every row's clock circuit gives the clock facts C1 to C3,
the bytecode producer's bits are Boolean, and the pushed tuples' factors times the producer's leaves equal the pulled
tuples' factors as polynomials in the formal challenges, then `Machine.Correct` holds with entry `i` read
`m_i = ∑_k b_{i,k} 2^k` times.
-/
theorem machine_correct_of_product_check (m : Machine) (rows : List MachineRow) (bits : Fin (2 ^ m.kbc) → ℕ → K)
    (nbit : ℕ) (boolean : ∀ i, ∀ k < nbit, bits i k = 0 ∨ bits i k = 1)
    (c1 : ∀ r ∈ rows, r.C1) (c2 : ∀ r ∈ rows, r.C2) (c3 : ∀ r ∈ rows, r.C3)
    (check : product (m.tableFlushes rows).pushed * (m.lut.producer bits nbit boolean).leaves =
      product (m.tableFlushes rows).pulled) :
    m.Correct (fun i => bitsValue (bits i) nbit) rows := by
  apply machine_correct m rows _ c1 c2 c3
  refine Flushes.balanced_of_eq ?_ ?_ (balanced_of_product_check _ _ check)
  · simp only [Machine.flushes, Flushes.pushed_append]
    congr 1
    simp [Producer.flushes, LookupArray.producer, LookupArray.flushes, Flushes.pushed, List.map_map,
      Function.comp_def]
  · simp only [Machine.flushes, Flushes.pulled_append]
    congr 1

end LeanVMCircuits.Bus
