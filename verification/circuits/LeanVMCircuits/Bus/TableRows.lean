module

public import LeanVMCircuits.Bus.ClockFacts
public import LeanVMCircuits.Bus.Machine
public import LeanVMCircuits.Bus.TableFlushes
public import LeanVMCircuits.Rec.Tables

@[expose] public section

/-!
# An instruction table's row on the bus

A row of an instruction table, its column `i` holding `v i`, makes the flushes of `ClassTable.Spec.pushes` and
`ClassTable.Spec.pulls` evaluated at `v` (`Spec.flushes`). They are, as multisets, the flushes of the `MachineRow`
`Spec.row` (`Spec.pushes_eq`, `Spec.pulls_eq`): its state columns, the verdict of its clock circuit, its bytecode read
of the ten decoded coordinates at `pc`, and its accesses, the registers' those whose separator evaluates to `REG`.
When the clock circuit's ports hold words satisfying `Clock.Holds`, the row satisfies the clock facts C1 to C3
(`Spec.row_c1`, `Spec.row_c2`, `Spec.row_c3`), by the clock reference's `clock_next` and `clock_in_order`;
`row_correct` puts it together for every table of `ClassTable.all`.
-/

namespace LeanVMCircuits.Bus.ClassTable

open LeanVMCircuits.Rec

/-! ### Values -/

/-- A coordinate's value on a row whose column `i` holds `v i`. -/
noncomputable def Coord.eval (v : ℕ → K) : Coord → K
  | .col i => v i
  | .const w => ofWord w
  | .sum a b => a.eval v + b.eval v
  | .scaled w i => ofWord w * v i

/-- The same supported coordinate language as actual Clean expressions of row columns. -/
noncomputable def Coord.expr : Coord → Expression K
  | .col i => var ⟨i⟩
  | .const w => .const (ofWord w)
  | .sum a b => a.expr + b.expr
  | .scaled w i => Expression.const (ofWord w) * var ⟨i⟩

/-- Lowering a Clean coordinate to the exported coordinate data preserves every row's value. -/
theorem Coord.eval_expr (v : ℕ → K) : (c : Coord) → c.expr.eval (rowEnv v) = c.eval v
  | .col _ => rfl
  | .const _ => rfl
  | .scaled _ _ => rfl
  | .sum a b => by
    show a.expr.eval (rowEnv v) + b.expr.eval (rowEnv v) = a.eval v + b.eval v
    rw [Coord.eval_expr v a, Coord.eval_expr v b]

/-- A tuple's value. -/
noncomputable def evalTuple (v : ℕ → K) (cs : List Coord) : Tuple := tuple (cs.map (Coord.eval v))

/-- A source tuple of Clean expressions, with the actual channel's zero padding. -/
noncomputable def sourceTuple (v : ℕ → K) (cs : List Coord) : Tuple :=
  tuple (cs.map fun c => c.expr.eval (rowEnv v))

theorem sourceTuple_eq (v : ℕ → K) (cs : List Coord) : sourceTuple v cs = evalTuple v cs := by
  simp only [sourceTuple, evalTuple, Coord.eval_expr]

theorem ofWord_zero : ofWord 0 = 0 := by simp [ofWord, ev_zero]

namespace Spec

variable (s : Spec) (v : ℕ → K)

/-- The row's flushes. -/
noncomputable def flushes : Flushes where
  pushes := s.pushes.map (evalTuple v)
  pulls := s.pulls.map (evalTuple v)

/-- Actual Clean integer-multiplicity interactions: no field-valued multiplicity or ignored lookup. -/
noncomputable def source : List (Interaction K ℤ) :=
  s.pushes.map (fun cs => interaction 1 (sourceTuple v cs)) ++
    s.pulls.map (fun cs => interaction (-1) (sourceTuple v cs))

/-- The exact data emitted into production denotes these Clean interactions for every column assignment. -/
theorem source_eq : s.source v = (s.flushes v).interactions := by
  simp only [source, flushes, Flushes.interactions, List.map_map, List.map_nil, List.append_nil,
    sourceTuple_eq, Function.comp_def]

/-- The integer the clock column names. -/
noncomputable def clockWord : ℕ := toWord (v s.layout.ts)

/-- The integers the previous-timestamp columns name. -/
noncomputable def prevWords : List ℕ := (List.range s.slots.length).map fun i => toWord (v (s.layout.prev + i))

/-- An access as the row makes it, with its slot and index. -/
noncomputable def rowAccess (x : Access × ℕ × ℕ) : RowAccess :=
  ⟨ x.1.addr.eval v, x.2.1, (timeAt s.layout.ts x.2.1).eval v, v (s.layout.prev + x.2.2), x.1.old.eval v,
    x.1.new.eval v ⟩

/-- The ten decoded coordinates of the entry the row reads. -/
noncomputable def decoded : Vector K 10 := Vector.ofFn fun j => ((s.bytecode.drop 2).map (Coord.eval v)).getD j 0

/-- The row as the bus theorem sees it: its register accesses are those whose separator is the registers'. -/
noncomputable def row : MachineRow where
  pc := v s.layout.pc
  ts := v s.layout.ts
  step := v s.layout.step
  npc := s.layout.npc.eval v
  exit := s.layout.exit.eval v
  inOrder := !Clock.fail s.slots (s.prevWords v) (s.clockWord v)
  reads := [(v s.layout.pc, s.decoded v)]
  regs := (s.indexed.filter fun x => decide (x.1.sep.eval v = sepREG)).map (s.rowAccess v)
  mems := (s.indexed.filter fun x => !decide (x.1.sep.eval v = sepREG)).map (s.rowAccess v)

/-- The flag bit `base` that picks an extension-field limb's separator is Boolean. -/
def BaseBit : Prop := ∀ b, s.layout.flagBits = some b → v (b + 1) = 0 ∨ v (b + 1) = 1

theorem sep_cases {sep : Coord} (h : s.SepOk sep) (base : s.BaseBit v) :
    sep.eval v = sepREG ∨ sep.eval v = sepMEM := by
  rcases h with rfl | rfl | h
  · exact Or.inl rfl
  · exact Or.inr rfl
  · obtain ⟨ b, hb, rfl ⟩ := Option.map_eq_some_iff.mp h
    rcases base b hb with h0 | h1
    · right
      simp only [Coord.eval, h0, mul_zero, add_zero]
      rfl
    · left
      simp only [Coord.eval, h1, mul_one]
      rw [ofWord_xor (by norm_num [memWord]) (by norm_num [memWord, regWord])]
      rfl

theorem mem_indexed {x : Access × ℕ × ℕ} (hx : x ∈ s.indexed) :
    x.1 ∈ s.accesses ∧ ∃ j, ∃ hj : j < s.slots.length, x.2 = (s.slots[j], j) := by
  obtain ⟨ a, k, i ⟩ := x
  refine ⟨ (List.of_mem_zip hx).1, ?_ ⟩
  obtain ⟨ j, hj, e ⟩ := List.mem_iff_getElem.mp (List.of_mem_zip hx).2
  simp only [List.length_zip, List.length_range, Nat.min_self] at hj
  refine ⟨ j, hj, ?_ ⟩
  rw [← e]
  simp

/-- The register and memory accesses of the row, `f sep x` the tuple of `x` under separator `sep`, are the row's
accesses under their own separators, as a multiset. -/
theorem split_eq (wf : s.WellFormed) (base : s.BaseBit v) (f : K → RowAccess → Tuple) :
    ((s.indexed.map fun x => f (x.1.sep.eval v) (s.rowAccess v x) : List Tuple) : Multiset Tuple) =
      ((s.row v).regs.map (f sepREG) ++ (s.row v).mems.map (f sepMEM) : List Tuple) := by
  obtain ⟨ -, -, -, -, -, seps ⟩ := wf
  have regs : ∀ x ∈ s.indexed.filter (fun x => decide (x.1.sep.eval v = sepREG)),
      f sepREG (s.rowAccess v x) = f (x.1.sep.eval v) (s.rowAccess v x) := by
    intro x hx
    rw [(by simpa using (List.mem_filter.mp hx).2 : x.1.sep.eval v = sepREG)]
  have mems : ∀ x ∈ s.indexed.filter (fun x => !decide (x.1.sep.eval v = sepREG)),
      f sepMEM (s.rowAccess v x) = f (x.1.sep.eval v) (s.rowAccess v x) := by
    intro x hx
    obtain ⟨ mem, ne ⟩ := List.mem_filter.mp hx
    rcases s.sep_cases v (seps _ (s.mem_indexed mem).1) base with h | h
    · simp [h] at ne
    · rw [h]
  apply Multiset.coe_eq_coe.mpr
  simp only [row, List.map_map, Function.comp_def]
  rw [List.map_congr_left regs, List.map_congr_left mems, ← List.map_append]
  exact ((List.filter_append_perm _ _).map _).symm

/-- The row's pushes are the `MachineRow`'s. -/
theorem pushes_eq (wf : s.WellFormed) (base : s.BaseBit v) :
    ((s.flushes v).pushes : Multiset Tuple) = (s.row v).flushes.pushes := by
  have split := s.split_eq v wf base RowAccess.push
  rw [show (s.row v).flushes.pushes = (s.row v).statePush ::
    ((s.row v).regs.map (RowAccess.push sepREG) ++ (s.row v).mems.map (RowAccess.push sepMEM)) from rfl]
  simp only [flushes, pushes, List.map_cons, List.map_map]
  apply Multiset.coe_eq_coe.mpr
  exact List.Perm.cons _ (Multiset.coe_eq_coe.mp split)

/-- The entry the row reads is `⟨BC, pc, decoded⟩`. -/
theorem bytecode_eq (wf : s.WellFormed) : evalTuple v s.bytecode = bytecodeRead (v s.layout.pc, s.decoded v) := by
  obtain ⟨ -, -, -, hb, hlen, - ⟩ := wf
  have dec : (s.decoded v).toList = (s.bytecode.drop 2).map (Coord.eval v) := by
    apply List.ext_getElem
    · rw [Vector.length_toList, List.length_map, hlen]
    · intro j h1 h2
      simp only [decoded, Vector.toList_ofFn, List.getElem_ofFn]
      exact List.getD_eq_getElem _ _ h2
  unfold bytecodeRead evalTuple
  rw [dec]
  conv_lhs => rw [hb]
  rfl

/-- The row's pulls are the `MachineRow`'s. -/
theorem pulls_eq (wf : s.WellFormed) (base : s.BaseBit v) :
    ((s.flushes v).pulls : Multiset Tuple) = (s.row v).flushes.pulls := by
  have split := s.split_eq v wf base RowAccess.pull
  have state : evalTuple v s.layout.statePull = (s.row v).statePull := by
    simp only [evalTuple, Layout.statePull, List.map_cons, List.map_nil, Coord.eval, ofWord_zero]
    rfl
  rw [show (s.row v).flushes.pulls = (s.row v).statePull :: bytecodeRead (v s.layout.pc, s.decoded v) ::
    ((s.row v).regs.map (RowAccess.pull sepREG) ++ (s.row v).mems.map (RowAccess.pull sepMEM)) from rfl]
  simp only [flushes, pulls, List.map_cons, List.map_map]
  rw [state, s.bytecode_eq v wf]
  apply Multiset.coe_eq_coe.mpr
  exact List.Perm.cons _ (List.Perm.cons _ (Multiset.coe_eq_coe.mp split))

/-! ### The clock facts -/

variable {s v} {ts step : ℕ} {prev : List ℕ}

theorem clock_eq (holds : Clock.Holds s.slots prev ts step) (ts_col : v s.layout.ts = ofWord ts) :
    (s.row v).clock = ts := by
  show toWord (v s.layout.ts) = ts
  rw [ts_col, toWord_ofWord ts (lt_trans holds.1 (by norm_num))]

theorem prevWord_eq (holds : Clock.Holds s.slots prev ts step)
    (prev_col : ∀ i (hi : i < prev.length), v (s.layout.prev + i) = ofWord prev[i]) (i : ℕ) (hi : i < prev.length) :
    toWord (v (s.layout.prev + i)) = prev[i] := by
  rw [prev_col i hi, toWord_ofWord _ (lt_trans (holds.2.2.2.1 _ (List.getElem_mem hi)) (by norm_num))]

theorem inOrder_eq (holds : Clock.Holds s.slots prev ts step) (ts_col : v s.layout.ts = ofWord ts)
    (prev_col : ∀ i (hi : i < prev.length), v (s.layout.prev + i) = ofWord prev[i]) :
    (s.row v).inOrder = !Clock.fail s.slots prev ts := by
  have words : s.prevWords v = prev := by
    apply List.ext_getElem
    · simp [prevWords, holds.2.2.1]
    · intro i h1 h2
      simp only [prevWords, List.getElem_map, List.getElem_range]
      exact prevWord_eq holds prev_col i h2
  show (!Clock.fail s.slots (s.prevWords v) (toWord (v s.layout.ts))) = _
  rw [words, ← show (s.row v).clock = toWord (v s.layout.ts) from rfl, clock_eq holds ts_col]

/-- C1: the clock column names a clock. -/
theorem row_c1 (holds : Clock.Holds s.slots prev ts step) (ts_col : v s.layout.ts = ofWord ts) : (s.row v).C1 := by
  rw [MachineRow.C1, clock_eq holds ts_col]
  exact ⟨ holds.1, holds.2.1 ⟩

/-- C2: the clock the row pushes is the next clock. -/
theorem row_c2 (holds : Clock.Holds s.slots prev ts step) (ts_col : v s.layout.ts = ofWord ts)
    (prev_col : ∀ i (hi : i < prev.length), v (s.layout.prev + i) = ofWord prev[i])
    (step_col : v s.layout.step = ofWord step) : (s.row v).C2 := by
  rw [MachineRow.C2, clock_eq holds ts_col, inOrder_eq holds ts_col prev_col]
  show v s.layout.ts + v s.layout.step = _
  rw [ts_col, step_col, holds.2.2.2.2]
  exact clock_next _ _ _ holds.1 holds.2.1

/-- C3: the row's accesses are in distinct slots, at their slots' timestamps, and in order when the row is. -/
theorem row_c3 (wf : s.WellFormed) (holds : Clock.Holds s.slots prev ts step)
    (ts_col : v s.layout.ts = ofWord ts)
    (prev_col : ∀ i (hi : i < prev.length), v (s.layout.prev + i) = ofWord prev[i]) : (s.row v).C3 := by
  obtain ⟨ nodup, slot_lt, acc_len, -, -, - ⟩ := wf
  have ts_lt := holds.1
  have ts_dvd := holds.2.1
  have len := holds.2.2.1
  have prev_lt := holds.2.2.2.1
  have perm : List.Perm ((s.row v).regs ++ (s.row v).mems) (s.indexed.map (s.rowAccess v)) := by
    simp only [row]
    rw [← List.map_append]
    exact (List.filter_append_perm _ _).map _
  have slots_eq : (s.indexed.map (s.rowAccess v)).map RowAccess.slot = s.slots := by
    rw [List.map_map, show RowAccess.slot ∘ s.rowAccess v = Prod.fst ∘ Prod.snd from rfl, ← List.map_map, indexed,
      List.map_snd_zip (by simp [acc_len]), List.map_fst_zip (by simp)]
  refine ⟨ ?_, fun x hx => ?_ ⟩
  · rw [(perm.map RowAccess.slot).nodup_iff, slots_eq]
    exact nodup
  obtain ⟨ y, hy, rfl ⟩ := List.mem_map.mp (perm.subset hx)
  obtain ⟨ -, j, hj, e ⟩ := s.mem_indexed hy
  obtain ⟨ a, k, i ⟩ := y
  obtain ⟨ hk, hi ⟩ := Prod.mk.inj e
  subst k i
  have hc := clock_eq holds ts_col
  have kl : s.slots[j] < 2 ^ 5 := slot_lt _ (List.getElem_mem hj)
  have pw := prevWord_eq holds prev_col j (by omega)
  refine ⟨ kl, ?_, ?_, fun h => ?_ ⟩
  · show (timeAt s.layout.ts s.slots[j]).eval v = ofWord ((s.row v).clock + s.slots[j])
    rw [hc]
    unfold timeAt
    split
    · rename_i h0
      simp [Coord.eval, ts_col, h0]
    · obtain ⟨ q, rfl ⟩ := ts_dvd
      simp only [Coord.eval, ts_col]
      exact ofWord_add_slot q _ kl (by omega)
  · show toWord (v (s.layout.prev + j)) < 2 ^ 41
    rw [pw]
    exact prev_lt _ (List.getElem_mem _)
  · rw [inOrder_eq holds ts_col prev_col, Bool.not_eq_true'] at h
    obtain ⟨ h1, h2 ⟩ := clock_in_order _ _ _ ts_lt ts_dvd prev_lt slot_lt len h j hj
    show (2 ^ 40 ≤ toWord (v (s.layout.prev + j)) ↔ 2 ^ 40 ≤ (s.row v).clock) ∧
      (2 ^ 40 ≤ (s.row v).clock → toWord (v (s.layout.prev + j)) < (s.row v).clock + s.slots[j])
    rw [pw, hc]
    exact ⟨ h1, h2 ⟩

/-- A row of an instruction table whose clock circuit's ports hold words satisfying `Clock.Holds`, and whose
extension-field flag bit `base` is Boolean, makes the flushes of a `MachineRow` that satisfies the clock facts. -/
theorem row_correct (wf : s.WellFormed) (holds : Clock.Holds s.slots prev ts step) (ts_col : v s.layout.ts = ofWord ts)
    (prev_col : ∀ i (hi : i < prev.length), v (s.layout.prev + i) = ofWord prev[i])
    (step_col : v s.layout.step = ofWord step) (base : s.BaseBit v) :
    ((s.flushes v).pushes : Multiset Tuple) = (s.row v).flushes.pushes ∧
      ((s.flushes v).pulls : Multiset Tuple) = (s.row v).flushes.pulls ∧
      (s.row v).C1 ∧ (s.row v).C2 ∧ (s.row v).C3 :=
  ⟨ s.pushes_eq v wf base, s.pulls_eq v wf base, row_c1 holds ts_col, row_c2 holds ts_col prev_col step_col,
    row_c3 wf holds ts_col prev_col ⟩

/-- The row reads its entry at its own `pc`, as `machine_reads_at_pc` asks. -/
theorem row_reads : (s.row v).reads = [((s.row v).pc, s.decoded v)] := rfl

end Spec

/-- Every instruction table: a row whose clock circuit's ports hold words satisfying `Clock.Holds` on the table's
slots, and whose extension-field flag bit `base` is Boolean, makes exactly (as multisets) the flushes of the
`MachineRow` `s.row v`, which satisfies C1 to C3. -/
theorem row_correct {s : Spec} (hs : s ∈ all) (v : ℕ → K)
    {ts step : ℕ} {prev : List ℕ} (holds : Clock.Holds s.slots prev ts step) (ts_col : v s.layout.ts = ofWord ts)
    (prev_col : ∀ i (hi : i < prev.length), v (s.layout.prev + i) = ofWord prev[i])
    (step_col : v s.layout.step = ofWord step) (base : s.BaseBit v) :
    ((s.flushes v).pushes : Multiset Tuple) = (s.row v).flushes.pushes ∧
      ((s.flushes v).pulls : Multiset Tuple) = (s.row v).flushes.pulls ∧
      (s.row v).C1 ∧ (s.row v).C2 ∧ (s.row v).C3 :=
  Spec.row_correct (all_wellFormed s hs) holds ts_col prev_col step_col base

end LeanVMCircuits.Bus.ClassTable
