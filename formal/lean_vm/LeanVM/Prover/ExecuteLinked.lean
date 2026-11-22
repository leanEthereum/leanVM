module

public import LeanVM.Prover.ExecuteKeccak
public import LeanVM.Prover.ExecuteCompleteMem

/-!
# The executor's links agree, and its memory stays within `maxCells`

`Mem.Sound m`: `m` agrees with its own reads (`Agree m m.peek`): its classes are recorded, every
link's two cells are in one class, and `used ≤ maxCells`. A successful hint or instruction keeps it
(`runHint_sound`, `runOp_sound`): every cell they touch is checked below `maxCells`, and a link only
joins or merges classes. So the executor needs no check at the end of a run.
-/

namespace LeanVM.Prover.Exec

open LeanVM.Parameters LeanVM.Semantics

@[expose] public section

/-- The memory agrees with its own reads. -/
abbrev Mem.Sound (m : Mem) : Prop := Agree m m.peek

/-- An agreement with any reference gives one with the memory's own reads. -/
theorem Agree.self {m : Mem} {M : ℕ → E} (h : Agree m M) : m.Sound :=
  ⟨⟨h.wf, fun _ _ hv ↦ Mem.peek_of_get hv,
    fun c d k hc hd ↦ by unfold Mem.peek; rw [SameCls.get_eq ⟨k, hc, hd⟩],
    h.mem, h.size, h.used⟩,
    fun p hp ↦ ⟨by unfold Mem.peek; rw [(h.links p hp).2.get_eq], (h.links p hp).2⟩⟩

/-- A sound memory agrees with the reads of an extension keeping its classes. -/
theorem Mem.Sound.transfer {m m' : Mem} (h : m.Sound) (hle : m ≤ m')
    (hcls : ∀ d k, m.cellOf d = .cls k → m'.cellOf d = .cls k) : Agree m m'.peek :=
  ⟨⟨h.wf, fun c v hv ↦ Mem.peek_of_get (hle.get c v hv),
    fun c d k hc hd ↦ by unfold Mem.peek; rw [SameCls.get_eq ⟨k, hcls c k hc, hcls d k hd⟩],
    h.mem, h.size, h.used⟩,
    fun p hp ↦ by
      obtain ⟨k, h1, h2⟩ := (h.links p hp).2
      exact ⟨by unfold Mem.peek; rw [SameCls.get_eq ⟨k, hcls _ k h1, hcls _ k h2⟩], k, h1, h2⟩⟩

/-- `put` keeps every class. -/
theorem Mem.put_cls {m m' : Mem} {c d k : ℕ} {v : E} (e : m.put c v = .ok m')
    (h : m.cellOf d = .cls k) : m'.cellOf d = .cls k := by
  simp only [Mem.put] at e
  have h1 : (m.ensure c).cellOf d = .cls k := h
  generalize m.ensure c = m1 at h1 e
  obtain ⟨cells, vals, members, links, used⟩ := m1
  simp only at e
  split at e
  · split_ifs at e
    simp only [pure_ok] at e; subst e; exact h1
  · split at e
    · split_ifs at e
      simp only [pure_ok] at e; subst e; exact h1
    · simp only [pure_ok] at e; subst e; exact h1
  · rename_i hx1 hx2
    simp only [pure_ok] at e; subst e
    rw [Mem.cellOf_setCell]
    split_ifs with hdc
    · subst hdc
      rw [Mem.cellOf_mk] at h1
      cases hcd : cells[d]? with
      | none => rw [hcd] at h1; cases h1
      | some x =>
        rw [hcd] at h1
        cases h1
        exact absurd hcd (hx2 k)
    · exact h1

theorem Mem.Sound.ensure {m : Mem} (h : m.Sound) {c : ℕ} (hc : c < maxCells) :
    (m.ensure c).Sound :=
  (Agree.ensure h hc).self

theorem Mem.Sound.foldl_ensure {m : Mem} (h : m.Sound) (l : List ℕ) (hl : ∀ c ∈ l, c < maxCells) :
    (l.foldl Mem.ensure m).Sound :=
  (Agree.foldl_ensure l m h hl).self

theorem Mem.Sound.put {m m' : Mem} {c : ℕ} {v : E} (h : m.Sound) (hc : c < maxCells)
    (e : m.put c v = .ok m') : m'.Sound := by
  obtain ⟨hle, -, hget⟩ := Mem.put_ok h.wf e
  obtain ⟨m'', e', h', -, -⟩ :=
    (h.transfer hle fun _ _ hd ↦ Mem.put_cls e hd).put (Mem.peek_of_get hget) hc
  obtain rfl : m' = m'' := Except.ok.inj (e.symm.trans e')
  exact h'.self

theorem Mem.Sound.link {m : Mem} (h : m.Sound) {a b : ℕ} (ha : m.get a = none)
    (hb : m.get b = none) (hau : a < maxCells) (hbu : b < maxCells) : (m.link a b).Sound :=
  (Agree.link h ha hb (by simp only [Mem.peek, ha, hb]) hau hbu).self

/-- A fold whose every step keeps soundness. -/
theorem Mem.Sound.foldlM {α : Type} (f : Mem → α → Except Fault Mem) (P : α → Prop)
    (hf : ∀ m x m', m.Sound → P x → f m x = .ok m' → m'.Sound) :
    ∀ (l : List α) (m m' : Mem), m.Sound → (∀ x ∈ l, P x) → l.foldlM f m = .ok m' → m'.Sound
  | [], m, m', h, _, e => by
    simp only [List.foldlM_nil, pure_ok] at e; subst e; exact h
  | x :: l, m, m', h, hl, e => by
    rw [List.foldlM_cons, bind_ok] at e
    obtain ⟨m1, e1, e⟩ := e
    exact Mem.Sound.foldlM f P hf l m1 m' (hf m x m1 h (hl x (List.mem_cons_self ..)) e1)
      (fun y hy ↦ hl y (List.mem_cons_of_mem _ hy)) e

theorem Mem.Sound.putRun {m m' : Mem} {b : ℕ} {vs : List E} (h : m.Sound)
    (hb : b + vs.length ≤ maxCells) (e : putRun b vs m = .ok m') : m'.Sound := by
  unfold Exec.putRun at e
  refine Mem.Sound.foldlM _ (fun x : E × ℕ ↦ x.2 < vs.length) (fun m x m' hm hx e ↦ ?_) _ m m' h
    (fun x hx ↦ ?_) e
  · obtain ⟨v, k⟩ := x
    exact hm.put (by dsimp only at hx; omega) e
  · obtain ⟨v, k⟩ := x
    exact (List.getElem?_eq_some_iff.mp (List.mem_zipIdx_iff_getElem?.mp hx)).1

/-! ## The state -/

theorem St.logOr_mem {s s' : St} {x : K} {b k : ℕ} {f : Fault} (h : s.logOr x b f = .ok (k, s')) :
    s'.mem = s.mem := by
  obtain ⟨D, rfl⟩ := St.logOr_dl h
  rfl

theorem heapBase_memEq {s s' : St} {c b : ℕ} {what : String} (h : heapBase s c what = .ok (b, s')) :
    s'.mem = s.mem := by
  unfold heapBase at h
  rw [bind_ok] at h
  obtain ⟨p, -, h⟩ := h
  exact St.logOr_mem h

theorem bitsBase_memEq {s s' : St} {d : BitsDest} {len : ℕ} {what : String} {b : ℕ}
    (h : bitsBase s d len what = .ok (b, s')) : s'.mem = s.mem ∧ b + len ≤ maxCells := by
  unfold bitsBase at h
  split at h
  · simp only [bind_ok, pure_ok, Prod.mk.injEq] at h
    obtain ⟨c, hc, rfl, rfl⟩ := h
    exact ⟨rfl, (runAt_ok hc).2⟩
  · simp only [bind_ok, pure_ok, Prod.mk.injEq] at h
    obtain ⟨c, -, ⟨b', s1⟩, h1, c2, hc2, rfl, rfl⟩ := h
    exact ⟨heapBase_memEq h1, (runAt_ok hc2).2⟩

theorem pop_memEq {C : Ctx} {s s' : St} {name : String} {len : ℕ} {v : List E}
    (h : pop C s name len = .ok (v, s')) : s'.mem = s.mem ∧ v.length = len := by
  unfold pop at h
  split at h
  · dsimp only at h
    split at h
    · split_ifs at h with hl
      · cases h
      · simp only [pure_ok, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        exact ⟨rfl, not_not.mp hl⟩
    · simp at h
  · simp at h

theorem withPut_sound {s s' : St} {c : ℕ} {v : E} (h : s.mem.Sound) (hc : c < maxCells)
    (e : s.withMem (·.put c v) = .ok s') : s'.mem.Sound := by
  obtain ⟨m, hm, rfl⟩ := St.withMem_ok e
  exact h.put hc hm

theorem withRun_sound {s s' : St} {b : ℕ} {vs : List E} (h : s.mem.Sound)
    (hb : b + vs.length ≤ maxCells) (e : s.withMem (putRun b vs) = .ok s') : s'.mem.Sound := by
  obtain ⟨m, hm, rfl⟩ := St.withMem_ok e
  exact h.putRun hb hm

theorem allocate_sound {s s' : St} {ptr size : ℕ} (h : s.mem.Sound)
    (e : allocate s ptr size = .ok s') : s'.mem.Sound := by
  unfold allocate at e
  rw [bind_ok] at e
  obtain ⟨cell, hcell, e⟩ := e
  dsimp only at e
  split at e
  · cases e
  · rename_i hn
    rw [bind_ok] at e
    obtain ⟨s1, h1, e⟩ := e
    simp only [pure_ok] at e
    subst e
    obtain ⟨m, hm, rfl⟩ := St.withMem_ok h1
    have hc := (cellAt_ok hcell).2
    split_ifs at hm with hb
    · exact (h.ensure (by omega)).put hc hm
    · exact h.put hc hm

/-- **A hint keeps the memory sound.** -/
theorem runHint_sound {C : Ctx} {s s' : St} {hint : Hint} (h : s.mem.Sound)
    (e : runHint C s hint = .ok s') : s'.mem.Sound := by
  cases hint with
  | frameAddress offset =>
    simp only [runHint, bind_ok, pure_ok] at e
    obtain ⟨c, -, rfl⟩ := e
    exact h
  | alloc ptr size => exact allocate_sound h e
  | allocDyn ptr size =>
    simp only [runHint, bind_ok] at e
    obtain ⟨c, -, sz, -, ⟨n, s1⟩, h1, e⟩ := e
    exact allocate_sound (by rw [St.logOr_mem h1]; exact h) e
  | allocArm ptr sel sizes =>
    simp only [runHint, bind_ok] at e
    obtain ⟨c, -, x, -, ⟨k, s1⟩, h1, e⟩ := e
    split at e
    · exact allocate_sound (by rw [St.logOr_mem h1]; exact h) e
    · simp at e
  | cellAddress ptr cell =>
    simp only [runHint, bind_ok] at e
    obtain ⟨c, -, p, hp, e⟩ := e
    exact withPut_sound h (cellAt_ok hp).2 e
  | allocFrames ptr size stop startInverse =>
    simp only [runHint, bind_ok] at e
    obtain ⟨c, -, sp, -, e⟩ := e
    split_ifs at e
    · simp [bind_ok] at e
    · rw [bind_ok] at e
      obtain ⟨⟨n, s1⟩, h1, e⟩ := e
      exact allocate_sound (by rw [St.logOr_mem h1]; exact h) e
  | witnessStack name base len =>
    simp only [runHint, bind_ok] at e
    obtain ⟨b, hb, ⟨v, s1⟩, h1, e⟩ := e
    obtain ⟨hm1, hv⟩ := pop_memEq h1
    exact withRun_sound (by rw [hm1]; exact h) (by rw [hv]; exact (runAt_ok hb).2) e
  | witnessHeap name ptr lo len =>
    simp only [runHint, bind_ok] at e
    obtain ⟨c, -, ⟨hb, s1⟩, h1, b, hb', ⟨v, s2⟩, h2, e⟩ := e
    obtain ⟨hm2, hv⟩ := pop_memEq h2
    exact withRun_sound (by rw [hm2, heapBase_memEq h1]; exact h)
      (by rw [hv]; exact (runAt_ok hb').2) e
  | log2Ceil bits dst nbits floor =>
    simp only [runHint, bind_ok] at e
    obtain ⟨⟨b, s1⟩, h1, d, hd, e⟩ := e
    exact withPut_sound (by rw [(bitsBase_memEq h1).1]; exact h) (cellAt_ok hd).2 e
  | bitDecompose value bits nbits =>
    simp only [runHint, bind_ok] at e
    obtain ⟨c, -, ⟨b, s1⟩, h1, e⟩ := e
    exact withRun_sound (by rw [(bitsBase_memEq h1).1]; exact h)
      (by rw [List.length_map, List.length_range]; exact (bitsBase_memEq h1).2) e
  | bitDecomposeExp value bits nbits =>
    simp only [runHint, bind_ok] at e
    obtain ⟨c, -, n, -, ⟨b, s1⟩, h1, e⟩ := e
    exact withRun_sound (by rw [(bitsBase_memEq h1).1]; exact h)
      (by rw [List.length_map, List.length_range]; exact (bitsBase_memEq h1).2) e
  | windowsExp value dest pos start width count =>
    simp only [runHint, bind_ok] at e
    obtain ⟨c, -, ⟨b, s1⟩, h1, e⟩ := e
    have := (bitsBase_memEq h1).2
    exact withRun_sound (by rw [(bitsBase_memEq h1).1]; exact h)
      (by rw [List.length_map, List.length_range]; omega) e
  | digitDecomposeExp value dst nbits ndigits digitBits start startCell =>
    simp only [runHint, bind_ok] at e
    obtain ⟨c, -, n, -, e⟩ := e
    split at e
    · simp only [bind_ok] at e
      obtain ⟨st, -, ⟨b, s1⟩, h1, e⟩ := e
      exact withRun_sound (by rw [(bitsBase_memEq h1).1]; exact h)
        (by rw [List.length_map, List.length_range]; exact (bitsBase_memEq h1).2) e
    · simp only [bind_ok] at e
      obtain ⟨c', -, st, -, ⟨b, s1⟩, h1, e⟩ := e
      exact withRun_sound (by rw [(bitsBase_memEq h1).1]; exact h)
        (by rw [List.length_map, List.length_range]; exact (bitsBase_memEq h1).2) e
  | fieldLimbs value base len =>
    simp only [runHint, bind_ok] at e
    obtain ⟨c, -, b, hb, e⟩ := e
    exact withRun_sound h (by rw [List.length_map, List.length_range]; exact (runAt_ok hb).2) e
  | inverse value dst =>
    simp only [runHint, bind_ok] at e
    obtain ⟨c, -, d, hd, e⟩ := e
    exact withPut_sound h (cellAt_ok hd).2 e

/-- The hints at a `pc`, in order. -/
theorem hints_sound {C : Ctx} :
    ∀ (l : List Hint) (s s' : St), s.mem.Sound → l.foldlM (runHint C) s = .ok s' → s'.mem.Sound
  | [], s, s', h, e => by
    simp only [List.foldlM_nil, pure_ok] at e; subst e; exact h
  | x :: l, s, s', h, e => by
    rw [List.foldlM_cons, bind_ok] at e
    obtain ⟨s1, e1, e⟩ := e
    exact hints_sound l s1 s' (runHint_sound h e1) e

/-- The cells a `mapM` of checked cells gives lie below `maxCells`. -/
theorem mapM_cells_lt {α : Type} (f : α → Except Fault ℕ) (hf : ∀ a c, f a = .ok c → c < maxCells) :
    ∀ (l : List α) (l' : List ℕ), l.mapM f = .ok l' → ∀ c ∈ l', c < maxCells
  | [], l', h, c, hc => by
    simp only [List.mapM_nil, pure_ok] at h; subst h; simp at hc
  | a :: l, l', h, c, hc => by
    simp only [List.mapM_cons, bind_ok, pure_ok] at h
    obtain ⟨b, hb, bs, hbs, rfl⟩ := h
    rcases List.mem_cons.mp hc with rfl | hc
    · exact hf a _ hb
    · exact mapM_cells_lt f hf l bs hbs c hc

/-- **An instruction keeps the memory sound.** -/
theorem runOp_sound {C : Ctx} {s s' : St} {op : Op} (hs : s.Good) (h : s.mem.Sound)
    (e : runOp C s op = .ok s') : s'.mem.Sound := by
  cases op with
  | xor a b c =>
    simp only [runOp, bind_ok] at e
    obtain ⟨ca, hca, cb, hcb, cc, hcc, va, -, vb, -, s1, hs1, e⟩ := e
    simp only [pure_ok] at e; subst e
    obtain ⟨m, hm, rfl⟩ := St.withMem_ok hs1
    rw [bind_ok] at hm
    obtain ⟨m1, hm1, hm⟩ := hm
    simp only [pure_ok] at hm; subst hm
    exact ((h.put (cellAt_ok hcc).2 hm1).ensure (cellAt_ok hca).2).ensure (cellAt_ok hcb).2
  | mul a b c =>
    simp only [runOp, bind_ok] at e
    obtain ⟨ca, hca, cb, hcb, cc, hcc, s1, hs1, e⟩ := e
    simp only [pure_ok] at e; subst e
    obtain ⟨m, hm, rfl⟩ := St.withMem_ok hs1
    have hA := (cellAt_ok hca).2
    have hB := (cellAt_ok hcb).2
    have hC := (cellAt_ok hcc).2
    have key : ∃ m1 : Mem, m1.Sound ∧ ∃ va vb m2, m1.put cc (va * vb) = .ok m2 ∧
        m = (m2.ensure ca).ensure cb := by
      split_ifs at hm <;> simp only [bind_ok, pure_ok, throw_ok, false_and, exists_false] at hm
      all_goals first
        | (obtain ⟨m1, rfl, va, -, vb, -, m2, hm2, rfl⟩ := hm
           exact ⟨_, h, va, vb, m2, hm2, rfl⟩)
        | (obtain ⟨m1, hm1, va, -, vb, -, m2, hm2, rfl⟩ := hm
           exact ⟨m1, h.put (by assumption) hm1, va, vb, m2, hm2, rfl⟩)
    obtain ⟨m1, h1, va, vb, m2, hm2, rfl⟩ := key
    exact ((h1.put hC hm2).ensure hA).ensure hB
  | set o k =>
    simp only [runOp, bind_ok] at e
    obtain ⟨ca, hca, s1, hs1, e⟩ := e
    simp only [pure_ok] at e; subst e
    exact (withPut_sound h (cellAt_ok hca).2 hs1 : s1.mem.Sound)
  | deref o1 o2 o3 mode =>
    simp only [runOp, bind_ok] at e
    obtain ⟨a1, ha1, p, -, e⟩ := e
    split_ifs at e with hpk
    · simp [bind_ok] at e
    simp only [bind_ok] at e
    obtain ⟨⟨a2, s2⟩, hlog, a3, ha3, s3, hs3, e⟩ := e
    simp only [pure_ok] at e; subst e
    obtain ⟨-, -, h2⟩ := St.derefCell_ok hs hlog
    obtain ⟨D, rfl⟩ := St.derefCell_dl hlog
    obtain ⟨m', hm', rfl⟩ := St.withMem_ok hs3
    have h1 := (cellAt_ok ha1).2
    have h3 := (cellAt_ok ha3).2
    have key : ∃ m0 : Mem, m0.Sound ∧ m' = ((m0.ensure a1).ensure a2).ensure a3 := by
      cases mode with
      | cell =>
        simp only at hm'
        split_ifs at hm' with hw2 hw3
        · simp only [bind_ok, pure_ok] at hm'
          obtain ⟨m0, hm0, rfl⟩ := hm'
          exact ⟨m0, h.put h3 hm0, rfl⟩
        · simp only [bind_ok, pure_ok] at hm'
          obtain ⟨m0, hm0, rfl⟩ := hm'
          exact ⟨m0, h.put h2 hm0, rfl⟩
        · simp only [bind_ok, pure_ok] at hm'
          obtain ⟨m0, rfl, rfl⟩ := hm'
          exact ⟨_, h.link (Mem.get_of_not_written hw2) (Mem.get_of_not_written hw3) h2 h3, rfl⟩
      | pc =>
        simp only [bind_ok, pure_ok] at hm'
        obtain ⟨m0, hm0, rfl⟩ := hm'
        exact ⟨m0, h.put h2 hm0, rfl⟩
      | fp =>
        simp only [bind_ok, pure_ok] at hm'
        obtain ⟨m0, hm0, rfl⟩ := hm'
        exact ⟨m0, h.put h2 hm0, rfl⟩
    obtain ⟨m0, h0, rfl⟩ := key
    exact ((h0.ensure h1).ensure h2).ensure h3
  | jump c d f =>
    simp only [runOp, bind_ok] at e
    obtain ⟨ca, hca, cb, hcb, cc, hcc, wc, -, vc, -, wd, -, vd, -, wf, -, vf, -, s1, hs1, e⟩ := e
    obtain ⟨m, hm, rfl⟩ := St.withMem_ok hs1
    simp only [pure_ok] at hm; subst hm
    have h1 := ((h.ensure (cellAt_ok hca).2).ensure (cellAt_ok hcb).2).ensure (cellAt_ok hcc).2
    split_ifs at e
    · simp only [pure_ok] at e; subst e; exact h1
    · simp only [bind_ok, pure_ok] at e
      obtain ⟨⟨pc', s2⟩, e2, ⟨fp', s3⟩, e3, rfl⟩ := e
      show s3.mem.Sound
      rw [St.logOr_mem e3, St.logOr_mem e2]
      exact h1
  | keccak ins out inOdd outOdd count =>
    simp only [runOp, bind_ok] at e
    obtain ⟨cells, hcells, input, -, outs, houts, s1, hs1, e⟩ := e
    simp only [pure_ok] at e; subst e
    obtain ⟨m, hm, rfl⟩ := St.withMem_ok hs1
    rw [bind_ok] at hm
    obtain ⟨m1, hm1, hm⟩ := hm
    simp only [pure_ok] at hm; subst hm
    have hc := mapM_cells_lt _ (fun _ _ h ↦ (cellAt_ok h).2) _ _ hcells
    have ho := mapM_cells_lt _ (fun _ _ h ↦ (cellAt_ok h).2) _ _ houts
    have h1 : m1.Sound := by
      refine Mem.Sound.foldlM _ (fun x : ℕ × ℕ ↦ x.1 < maxCells) (fun m x m' hm hx e ↦ ?_) _ s.mem
        m1 h (fun x hx ↦ ?_) hm1
      · obtain ⟨c, k⟩ := x
        exact hm.put hx e
      · obtain ⟨c, k⟩ := x
        exact ho c (List.mem_of_getElem? (List.mem_zipIdx_iff_getElem?.mp hx))
    exact h1.foldl_ensure _ fun c hc' ↦ by
      rcases List.mem_append.mp hc' with hc' | hc'
      · exact hc c hc'
      · exact ho c hc'

/-- **A step keeps the memory sound.** -/
theorem step_sound {C : Ctx} {s s' : St} (hs : s.Good) (h : s.mem.Sound) (e : step C s = .ok s') :
    s'.mem.Sound := by
  simp only [step, bind_ok] at e
  obtain ⟨s1, h1, e⟩ := e
  rw [mapError_ok] at h1
  have f1 := hints_follows _ s s1 hs h1
  have g1 := hints_sound _ s s1 h h1
  split at e
  · rename_i op hop
    rw [bind_ok] at e
    obtain ⟨s2, h2, e⟩ := e
    rw [mapError_ok] at h2
    simp only [pure_ok] at e; subst e
    exact (runOp_sound f1.good g1 h2 : s2.mem.Sound)
  · simp at e

end

end LeanVM.Prover.Exec
