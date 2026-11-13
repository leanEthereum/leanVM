module

public import LeanVM.Prover.ExecuteCompleteMem

/-!
# The executor's hints are complete

`Fine M s`: the state's memory agrees with the reference `M`, its logarithm table is right and
small, and its frame lies below `maxCells`. `HintOk C M s h` states what hint `h` needs from the
state `s` it runs from: its pointers and exponents written as powers in range, the stream entry
it pops of the right length, and the values it writes equal to `M` at their cells below
`maxCells`; an allocation's pointer written, or `M` holding `g^nextFree` there with the
reservation in range. Then the hint succeeds, keeps `Fine` and the registers, and extends the
memory (`runHint_complete`).
-/

namespace LeanVM.Prover.Exec

open LeanVM.Parameters LeanVM.Semantics

@[expose] public section

/-- The completeness invariant of a state against the reference `M`. -/
structure Fine (M : ℕ → E) (s : St) : Prop where
  agree : Agree s.mem M
  dl : s.dl.Ok
  small : s.dl.Small
  fp : s.fp < maxCells

/-- `s'` follows `s` through a hint: still fine, the same registers and count, more memory. -/
structure Moves (M : ℕ → E) (s s' : St) : Prop where
  fine : Fine M s'
  le : s.mem ≤ s'.mem
  pc : s'.pc = s.pc
  fp : s'.fp = s.fp
  steps : s'.steps = s.steps

theorem Moves.trans {M : ℕ → E} {a b c : St} (h1 : Moves M a b) (h2 : Moves M b c) : Moves M a c :=
  ⟨h2.fine, Mem.le_trans h1.le h2.le, h2.pc.trans h1.pc, h2.fp.trans h1.fp, h2.steps.trans h1.steps⟩

theorem Moves.dl {M : ℕ → E} {s : St} (hs : Fine M s) {D : Dlog} (h1 : D.Ok) (h2 : D.Small) :
    Moves M s { s with dl := D } :=
  ⟨⟨hs.agree, h1, h2, hs.fp⟩, Mem.le_refl _, rfl, rfl, rfl⟩

theorem Moves.mem {M : ℕ → E} {s : St} (hs : Fine M s) {m : Mem} (h1 : Agree m M) (h2 : s.mem ≤ m) :
    Moves M s { s with mem := m } :=
  ⟨⟨h1, hs.dl, hs.small, hs.fp⟩, h2, rfl, rfl, rfl⟩

/-! ## Primitives -/

theorem ok_bind {ε α β : Type} (a : α) (f : α → Except ε β) : (Except.ok a >>= f) = f a := rfl

theorem pure_bind' {ε α β : Type} (a : α) (f : α → Except ε β) :
    ((pure a : Except ε α) >>= f) = f a :=
  rfl

theorem cellAt_eq {base off : ℕ} (h : base + off < maxCells) :
    cellAt base off = .ok (base + off) := by
  unfold cellAt; rw [ite_eq_left h]; rfl

theorem inK_ofK (what : String) (a : K) : inK what (ofK a) = .ok a := by
  unfold inK
  rw [ite_eq_left (by simp [limb_ofK])]
  simp [limb_ofK]

theorem St.withMem_eq {s : St} {f : Mem → Except Fault Mem} {m : Mem} (h : f s.mem = .ok m) :
    s.withMem f = .ok { s with mem := m } := by
  unfold St.withMem
  dsimp only
  rw [h]
  rfl

/-- Cell `c` holds the pointer `g^b`, with `b < maxCells`. -/
def PtrAt (s : St) (c b : ℕ) : Prop := s.mem.peek c = ofK (g ^ b) ∧ b < maxCells

theorem heapBase_complete {M : ℕ → E} {s : St} (hs : Fine M s) {c b : ℕ} {what : String}
    (h : PtrAt s c b) : ∃ s', heapBase s c what = .ok (b, s') ∧ Moves M s s' := by
  obtain ⟨D', e, h1, h2⟩ := St.logOr_complete hs.dl hs.small (f := .notAGPower what (g ^ b)) h.2
    (by unfold maxCells; norm_num)
  refine ⟨_, ?_, Moves.dl hs h1 h2⟩
  unfold heapBase
  rw [h.1, inK_ofK, ok_bind, e]

/-- Where a run starts, satisfying `P`: frame cells from `fp + base`, or heap cells from a
pointer. -/
def DestOk (s : St) (P : ℕ → Prop) : BitsDest → Prop
  | .stack base => P (s.fp + base)
  | .heap ptr => ∃ b, PtrAt s (s.fp + ptr) b ∧ P b

theorem bitsBase_complete {M : ℕ → E} {s : St} (hs : Fine M s) {P : ℕ → Prop} {d : BitsDest}
    {what : String} (h : DestOk s P d) :
    ∃ b s', bitsBase s d what = .ok (b, s') ∧ P b ∧ Moves M s s' ∧ s'.mem = s.mem := by
  cases d with
  | stack base =>
    exact ⟨_, s, rfl, h, ⟨hs, Mem.le_refl _, rfl, rfl, rfl⟩, rfl⟩
  | heap ptr =>
    obtain ⟨b, hb, hP⟩ := h
    obtain ⟨s', e, hm⟩ := heapBase_complete hs (what := what) hb
    refine ⟨b, s', e, hP, hm, ?_⟩
    unfold heapBase at e
    rw [hb.1, inK_ofK, ok_bind] at e
    obtain ⟨D', e', -, -⟩ := St.logOr_complete hs.dl hs.small
      (f := .notAGPower what (g ^ b)) hb.2 (by unfold maxCells; norm_num)
    rw [e'] at e
    cases e
    rfl

/-- The next entry of stream `name` is `e`. -/
def StreamNext (C : Ctx) (s : St) (name : String) (e : List E) : Prop :=
  ∃ entries, C.streams[name]? = some entries ∧ entries[s.cursor.getD name 0]? = some e

theorem pop_complete {C : Ctx} {M : ℕ → E} {s : St} (hs : Fine M s) {name : String} {e : List E}
    {len : ℕ} (h : StreamNext C s name e) (hl : e.length = len) :
    ∃ s', pop C s name len = .ok (e, s') ∧ Moves M s s' ∧ s'.mem = s.mem := by
  obtain ⟨entries, h1, h2⟩ := h
  refine ⟨{ s with cursor := s.cursor.insert name (s.cursor.getD name 0 + 1) }, ?_,
    ⟨⟨hs.agree, hs.dl, hs.small, hs.fp⟩, Mem.le_refl _, rfl, rfl, rfl⟩, rfl⟩
  unfold pop
  simp only [h1, h2, hl, ne_eq, not_true_eq_false, ↓reduceIte]
  rfl

/-- The word at `c` is `g^n`, with `n < 2^nbits`. -/
def ExpAt (s : St) (c n nbits : ℕ) : Prop := s.mem.peek c = ofK (g ^ n) ∧ n < 2 ^ nbits

theorem expOf_complete {s : St} {c n nbits : ℕ} {what : String} (h : ExpAt s c n nbits)
    (hn : nbits ≤ 62) : expOf what (s.mem.peek c) nbits = .ok n := by
  unfold expOf
  rw [h.1, inK_ofK, ok_bind, boundedDlog_complete h.2 hn]
  rfl

/-- An allocation of `size` cells with its pointer at `fp + ptr`: the pointer written, or `M`
holding `g^nextFree` there and the reservation below `maxCells`. -/
def AllocOk (M : ℕ → E) (s : St) (ptr size : ℕ) : Prop :=
  s.mem.written (s.fp + ptr) = true ∨
    (s.fp + ptr < maxCells ∧ s.nextFree + size < maxCells ∧ M (s.fp + ptr) = ofK (g ^ s.nextFree))

theorem allocate_complete {M : ℕ → E} {s : St} (hs : Fine M s) {ptr size : ℕ}
    (h : AllocOk M s ptr size) : ∃ s', allocate s ptr size = .ok s' ∧ Moves M s s' := by
  by_cases hw : s.mem.written (s.fp + ptr) = true
  · refine ⟨s, ?_, ⟨hs, Mem.le_refl _, rfl, rfl, rfl⟩⟩
    unfold allocate
    simp only [hw, ↓reduceIte]
    rfl
  · obtain ⟨hcu, hnu, hM⟩ := h.resolve_left hw
    have hm0 : Agree (if s.nextFree < s.nextFree + size then s.mem.ensure (s.nextFree + size - 1)
        else s.mem) M := by
      split_ifs
      · exact hs.agree.ensure (by omega)
      · exact hs.agree
    have hle0 : s.mem ≤ (if s.nextFree < s.nextFree + size then s.mem.ensure (s.nextFree + size - 1)
        else s.mem) := by
      split_ifs
      · exact Mem.le_ensure _ _
      · exact Mem.le_refl _
    obtain ⟨m', e, h', le', -⟩ := hm0.put hM hcu
    have hD := (hs.dl.grow (s.nextFree + size)).note s.nextFree
    have hS := (hs.small.grow (n := s.nextFree + size) (by unfold maxCells at hnu; omega)).note
      (k := s.nextFree) (by unfold maxCells at hnu; omega)
    refine ⟨{ s with
      mem := m', nextFree := s.nextFree + size,
      dl := (s.dl.grow (s.nextFree + size)).note s.nextFree },
      ?_,
      ⟨⟨h', hD, hS, hs.fp⟩, Mem.le_trans hle0 le', rfl, rfl, rfl⟩⟩
    unfold allocate
    simp only [hw, Bool.false_eq_true, ↓reduceIte]
    rw [cellAt_eq hnu, ok_bind, St.withMem_eq e]
    rfl

/-! ## The hints -/

/-- `⌈log₂⌉` of the integer of the `nbits` bits from cell `b` (`log2Ceil`). -/
def log2CeilOf (m : Mem) (b nbits : ℕ) : ℕ :=
  let word := (List.range nbits).foldl (fun w j ↦ if m.peek (b + j) = 0 then w else w + 2 ^ j) 0
  if word ≤ 1 then 0 else Nat.log2 (word - 1) + 1

/-- What hint `h` needs from the state it runs from. -/
def HintOk (C : Ctx) (M : ℕ → E) (s : St) : Hint → Prop
  | .frameAddress offset => s.fp + offset < maxCells
  | .alloc ptr size => AllocOk M s ptr size
  | .allocDyn ptr size => ∃ n, PtrAt s (s.fp + size) n ∧ AllocOk M s ptr n
  | .allocArm ptr sel sizes => ∃ k n, PtrAt s (s.fp + sel) k ∧ sizes[k]? = some n ∧ AllocOk M s ptr n
  | .cellAddress ptr cell => s.fp + cell < maxCells ∧ s.fp + ptr < maxCells ∧
    M (s.fp + ptr) = ofK (g ^ (s.fp + cell))
  | .allocFrames ptr size stop startInverse tail => ∃ v n, s.mem.peek (s.fp + stop) = ofK v ∧
    v * startInverse = g ^ n ∧ n < maxCells ∧ AllocOk M s ptr (size * n + tail)
  | .witnessStack name base len => ∃ e, StreamNext C s name e ∧ e.length = len ∧
    RunOk M (s.fp + base) e
  | .witnessHeap name ptr lo len => ∃ b e, PtrAt s (s.fp + ptr) b ∧ StreamNext C s name e ∧
    e.length = len ∧ RunOk M (b + lo) e
  | .log2Ceil bits dst nbits floor => DestOk s (fun b ↦ s.fp + dst < maxCells ∧
    M (s.fp + dst) = ofK (g ^ max (log2CeilOf s.mem b nbits) floor)) bits
  | .bitDecompose value bits nbits => DestOk s (fun b ↦ RunOk M b ((List.range nbits).map
    fun j ↦ bitWord ((wordNat (s.mem.peek (s.fp + value))).testBit j))) bits
  | .bitDecomposeExp value bits nbits => nbits ≤ 62 ∧ ∃ n, ExpAt s (s.fp + value) n nbits ∧
    DestOk s (fun b ↦ RunOk M b ((List.range nbits).map fun j ↦ bitWord (n.testBit j))) bits
  | .windowsExp value dest pos start width count => DestOk s (fun b ↦ RunOk M (b + pos)
    ((List.range count).map fun i ↦
      ofK (g ^ ((wordNat (s.mem.peek (s.fp + value)) >>> (start + i * width)) % 2 ^ width)))) dest
  | .digitDecomposeExp value dst nbits ndigits digitBits start startCell => nbits ≤ 62 ∧
    ∃ n st, ExpAt s (s.fp + value) n nbits ∧
      (match startCell with
        | none => st = start
        | some c => ExpAt s (s.fp + c) st 7) ∧
      DestOk s (fun b ↦ RunOk M b ((List.range ndigits).map fun j ↦ ofK (g ^
        (if 128 ≤ st + digitBits * j then 0 else (n >>> (st + digitBits * j)) % 2 ^ digitBits))))
        dst
  | .fieldLimbs value base len => RunOk M (s.fp + base) ((List.range len).map fun j ↦
    ofK (if j = 0 then (s.mem.peek (s.fp + value)).limb 0 else (s.mem.peek (s.fp + value)).limb 1))
  | .inverse value dst => s.fp + dst < maxCells ∧
    M (s.fp + dst) = if s.mem.peek (s.fp + value) = 0 then 0 else (s.mem.peek (s.fp + value))⁻¹

theorem putRun_moves {M : ℕ → E} {s : St} (hs : Fine M s) {b : ℕ} {vs : List E}
    (h : RunOk M b vs) : ∃ s', s.withMem (putRun b vs) = .ok s' ∧ Moves M s s' := by
  obtain ⟨m', e, h1, h2⟩ := hs.agree.putRun h
  exact ⟨_, St.withMem_eq e, Moves.mem hs h1 h2⟩

theorem put_moves {M : ℕ → E} {s : St} (hs : Fine M s) {c : ℕ} {v : E} (hv : M c = v)
    (hc : c < maxCells) : ∃ s', s.withMem (·.put c v) = .ok s' ∧ Moves M s s' := by
  obtain ⟨m', e, h1, h2, -⟩ := hs.agree.put hv hc
  exact ⟨_, St.withMem_eq e, Moves.mem hs h1 h2⟩

/-- A hint whose needs hold succeeds, keeping `Fine` and the registers. -/
theorem runHint_complete {C : Ctx} {M : ℕ → E} {s : St} (hs : Fine M s) {h : Hint}
    (hh : HintOk C M s h) : ∃ s', runHint C s h = .ok s' ∧ Moves M s s' := by
  cases h with
  | frameAddress offset =>
    have hh : s.fp + offset < maxCells := hh
    refine ⟨_, ?_, Moves.dl hs (hs.dl.note _) (hs.small.note (k := s.fp + offset)
      (by unfold maxCells at hh; omega))⟩
    simp only [runHint]
    rw [cellAt_eq hh, ok_bind]
    rfl
  | alloc ptr size => exact allocate_complete hs hh
  | allocDyn ptr size =>
    obtain ⟨n, hp, ha⟩ := hh
    obtain ⟨D', e, h1, h2⟩ := St.logOr_complete hs.dl hs.small
      (f := .notAGPower "HeapBuf size" (g ^ n))
      hp.2 (by unfold maxCells; norm_num)
    obtain ⟨s', e', hm⟩ := allocate_complete (Moves.dl hs h1 h2).fine (s := { s with dl := D' }) ha
    refine ⟨s', ?_, (Moves.dl hs h1 h2).trans hm⟩
    simp only [runHint]
    rw [hp.1, inK_ofK, ok_bind, e, ok_bind]
    exact e'
  | allocArm ptr sel sizes =>
    obtain ⟨k, n, hp, hk, ha⟩ := hh
    obtain ⟨D', e, h1, h2⟩ := St.logOr_complete hs.dl hs.small
      (f := .notAGPower "dispatch selector" (g ^ k))
      hp.2 (by unfold maxCells; norm_num)
    obtain ⟨s', e', hm⟩ := allocate_complete (Moves.dl hs h1 h2).fine (s := { s with dl := D' }) ha
    refine ⟨s', ?_, (Moves.dl hs h1 h2).trans hm⟩
    simp only [runHint]
    rw [hp.1, inK_ofK, ok_bind, e, ok_bind]
    simp only [hk]
    exact e'
  | cellAddress ptr cell =>
    obtain ⟨hc, hp, hM⟩ := hh
    obtain ⟨s', e, hm⟩ := put_moves hs hM hp
    refine ⟨s', ?_, hm⟩
    simp only [runHint]
    rw [cellAt_eq hc, ok_bind]
    exact e
  | allocFrames ptr size stop startInverse tail =>
    obtain ⟨v, n, hv, hvn, hn, ha⟩ := hh
    obtain ⟨D', e, h1, h2⟩ := St.logOr_complete hs.dl hs.small
      (f := .notAGPower "loop bound" (g ^ n))
      hn (by unfold maxCells; norm_num)
    obtain ⟨s', e', hm⟩ := allocate_complete (Moves.dl hs h1 h2).fine (s := { s with dl := D' }) ha
    refine ⟨s', ?_, (Moves.dl hs h1 h2).trans hm⟩
    simp only [runHint]
    rw [hv, inK_ofK, ok_bind, hvn, ite_eq_right (pow_ne_zero n g_ne_zero), e, ok_bind]
    exact e'
  | witnessStack name base len =>
    obtain ⟨e, hn, hl, hr⟩ := hh
    obtain ⟨s1, e1, m1, hmem⟩ := pop_complete hs hn hl
    obtain ⟨s2, e2, m2⟩ := putRun_moves m1.fine (b := s1.fp + base) (by rw [m1.fp]; exact hr)
    refine ⟨s2, ?_, m1.trans m2⟩
    simp only [runHint]
    rw [e1, ok_bind]
    exact e2
  | witnessHeap name ptr lo len =>
    obtain ⟨b, e, hp, hn, hl, hr⟩ := hh
    obtain ⟨s1, e1, m1⟩ := heapBase_complete hs (what := "hint_witness heap pointer") hp
    have hs1 : s1.mem = s.mem ∧ s1.cursor = s.cursor := by
      unfold heapBase at e1
      rw [hp.1, inK_ofK, ok_bind] at e1
      obtain ⟨D', e', -, -⟩ := St.logOr_complete hs.dl hs.small
        (f := .notAGPower "hint_witness heap pointer" (g ^ b)) hp.2 (by unfold maxCells; norm_num)
      rw [e'] at e1
      cases e1
      exact ⟨rfl, rfl⟩
    obtain ⟨s2, e2, m2, -⟩ := pop_complete m1.fine (name := name) (len := len)
      (by obtain ⟨en, h1, h2⟩ := hn; exact ⟨en, h1, by rw [hs1.2]; exact h2⟩) hl
    obtain ⟨s3, e3, m3⟩ := putRun_moves m2.fine hr
    refine ⟨s3, ?_, m1.trans (m2.trans m3)⟩
    simp only [runHint]
    rw [e1, ok_bind, e2, ok_bind]
    exact e3
  | log2Ceil bits dst nbits floor =>
    dsimp only [HintOk] at hh
    obtain ⟨b, s1, e1, ⟨hd, hM⟩, m1, hmem⟩ := bitsBase_complete hs (what := "log2_ceil pointer") hh
    obtain ⟨s2, e2, m2⟩ := put_moves m1.fine (c := s1.fp + dst)
      (v := ofK (g ^ max (log2CeilOf s1.mem b nbits) floor)) (by rw [m1.fp, hmem]; exact hM)
      (by rw [m1.fp]; exact hd)
    refine ⟨s2, ?_, m1.trans m2⟩
    simp only [runHint]
    rw [e1, ok_bind]
    exact e2
  | bitDecompose value bits nbits =>
    dsimp only [HintOk] at hh
    obtain ⟨b, s1, e1, hr, m1, hmem⟩ := bitsBase_complete hs (what := "decompose pointer") hh
    obtain ⟨s2, e2, m2⟩ := putRun_moves m1.fine hr
    refine ⟨s2, ?_, m1.trans m2⟩
    simp only [runHint]
    rw [e1, ok_bind]
    exact e2
  | bitDecomposeExp value bits nbits =>
    obtain ⟨hn, n, he, hd⟩ := hh
    obtain ⟨b, s1, e1, hr, m1, hmem⟩ :=
      bitsBase_complete hs (what := "hint_decompose_bits_exponent pointer") hd
    obtain ⟨s2, e2, m2⟩ := putRun_moves m1.fine hr
    refine ⟨s2, ?_, m1.trans m2⟩
    simp only [runHint]
    rw [expOf_complete he hn, ok_bind, e1, ok_bind]
    exact e2
  | windowsExp value dest pos start width count =>
    dsimp only [HintOk] at hh
    obtain ⟨b, s1, e1, hr, m1, hmem⟩ := bitsBase_complete hs (what := "windows pointer") hh
    obtain ⟨s2, e2, m2⟩ := putRun_moves m1.fine hr
    refine ⟨s2, ?_, m1.trans m2⟩
    simp only [runHint]
    rw [e1, ok_bind]
    exact e2
  | digitDecomposeExp value dst nbits ndigits digitBits start startCell =>
    obtain ⟨hn, n, st, he, hst, hd⟩ := hh
    obtain ⟨b, s1, e1, hr, m1, hmem⟩ :=
      bitsBase_complete hs (what := "hint_decompose_digits_exponent pointer") hd
    obtain ⟨s2, e2, m2⟩ := putRun_moves m1.fine hr
    refine ⟨s2, ?_, m1.trans m2⟩
    cases startCell with
    | none =>
      subst hst
      simp only [runHint]
      rw [expOf_complete he hn, ok_bind, pure_bind', e1, ok_bind]
      exact e2
    | some c =>
      simp only [runHint]
      rw [expOf_complete he hn, ok_bind, expOf_complete hst (by norm_num), ok_bind, e1, ok_bind]
      exact e2
  | fieldLimbs value base len => exact putRun_moves hs hh
  | inverse value dst => exact put_moves hs hh.2 hh.1

end

end LeanVM.Prover.Exec
