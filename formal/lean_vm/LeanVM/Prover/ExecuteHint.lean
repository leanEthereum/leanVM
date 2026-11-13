module

public import LeanVM.Prover.ExecuteDlog

/-!
# The executor's hints are harmless

`St.Follows s s'`: `s'` keeps `s`'s registers and step count, extends its memory, and is good
(`St.Good`: a well-formed memory and a right logarithm table). Every successful hint gives a state
following its own (`runHint_follows`): a hint only allocates, pops streams and writes advice, which
the instructions go on to check.
-/

namespace LeanVM.Prover.Exec

open LeanVM.Parameters LeanVM.Semantics

@[expose] public section

/-- The run's invariant. -/
structure St.Good (s : St) : Prop where
  wf : s.mem.WF
  dl : s.dl.Ok

/-- `s'` follows `s`: the same registers and count, more memory, good. -/
structure St.Follows (s s' : St) : Prop where
  good : s'.Good
  le : s.mem ≤ s'.mem
  pc : s'.pc = s.pc
  fp : s'.fp = s.fp
  steps : s'.steps = s.steps

theorem St.Follows.refl {s : St} (h : s.Good) : St.Follows s s :=
  ⟨h, Mem.le_refl _, rfl, rfl, rfl⟩

theorem St.Follows.trans {a b c : St} (h1 : St.Follows a b) (h2 : St.Follows b c) :
    St.Follows a c :=
  ⟨h2.good, Mem.le_trans h1.le h2.le, h2.pc.trans h1.pc, h2.fp.trans h1.fp, h2.steps.trans h1.steps⟩

/-! ## The state's primitives -/

theorem cellAt_ok {base off c : ℕ} (h : cellAt base off = .ok c) :
    c = base + off ∧ c < maxCells := by
  unfold cellAt at h
  split_ifs at h with hc
  simp only [pure_ok] at h; exact ⟨h.symm, h ▸ hc⟩

theorem Mem.read_ok {m : Mem} {c : ℕ} {v : E} (h : m.read c = .ok v) : m.get c = some v := by
  unfold Mem.read at h
  split at h
  · rename_i w hw; simp only [pure_ok] at h; rw [hw, h]
  · simp at h

theorem inK_ok {what : String} {v : E} {a : K} (h : inK what v = .ok a) :
    v.limb 1 = 0 ∧ a = v.limb 0 := by
  unfold inK at h
  split_ifs at h with hv
  simp only [pure_ok] at h; exact ⟨hv, h.symm⟩

theorem St.withMem_ok {s s' : St} {f : Mem → Except Fault Mem} (h : s.withMem f = .ok s') :
    ∃ m, f s.mem = .ok m ∧ s' = { s with mem := m } := by
  unfold St.withMem at h
  rw [bind_ok] at h
  obtain ⟨m, hm, h⟩ := h
  simp only [pure_ok] at h
  exact ⟨m, hm, h.symm⟩

theorem St.withMem_follows {s s' : St} {f : Mem → Except Fault Mem} (hs : s.Good)
    (hf : ∀ m', f s.mem = .ok m' → s.mem ≤ m' ∧ m'.WF) (h : s.withMem f = .ok s') :
    St.Follows s s' := by
  obtain ⟨m, hm, rfl⟩ := St.withMem_ok h
  obtain ⟨h1, h2⟩ := hf m hm
  exact ⟨⟨h2, hs.dl⟩, h1, rfl, rfl, rfl⟩

theorem St.log_eq (s : St) (x : K) (b : ℕ) :
    s.log x b = ((s.dl.log x b).1, { s with dl := (s.dl.log x b).2 }) := by
  unfold St.log
  dsimp only

theorem St.logOr_ok {s s' : St} {x : K} {b k : ℕ} {f : Fault} (hs : s.Good)
    (h : s.logOr x b f = .ok (k, s')) : St.Follows s s' ∧ g ^ k = x ∧ k < b := by
  unfold St.logOr at h
  rw [St.log_eq] at h
  obtain ⟨hok, hk⟩ := Dlog.log_ok hs.dl x b
  split at h
  · rename_i k' s1 hp
    simp only [pure_ok, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    simp only [Prod.mk.injEq] at hp
    obtain ⟨h1, rfl⟩ := hp
    exact ⟨⟨⟨hs.wf, hok⟩, Mem.le_refl _, rfl, rfl, rfl⟩, hk k' h1⟩
  · simp at h

theorem pop_follows {C : Ctx} {s s' : St} {name : String} {len : ℕ} {v : List E} (hs : s.Good)
    (h : pop C s name len = .ok (v, s')) : St.Follows s s' := by
  unfold pop at h
  split at h
  · dsimp only at h
    split at h
    · split_ifs at h
      · cases h
      · simp only [pure_ok, Prod.mk.injEq] at h
        obtain ⟨-, rfl⟩ := h
        exact ⟨⟨hs.wf, hs.dl⟩, Mem.le_refl _, rfl, rfl, rfl⟩
    · simp at h
  · simp at h

theorem heapBase_follows {s s' : St} {c b : ℕ} {what : String} (hs : s.Good)
    (h : heapBase s c what = .ok (b, s')) : St.Follows s s' := by
  unfold heapBase at h
  rw [bind_ok] at h
  obtain ⟨p, -, h⟩ := h
  exact (St.logOr_ok hs h).1

theorem bitsBase_follows {s s' : St} {d : BitsDest} {what : String} {b : ℕ} (hs : s.Good)
    (h : bitsBase s d what = .ok (b, s')) : St.Follows s s' := by
  unfold bitsBase at h
  split at h
  · simp only [pure_ok, Prod.mk.injEq] at h
    obtain ⟨-, rfl⟩ := h
    exact St.Follows.refl hs
  · exact heapBase_follows hs h

theorem put_le {m m' : Mem} {c : ℕ} {v : E} (hm : m.WF) (h : m.put c v = .ok m') : m ≤ m' ∧ m'.WF :=
  ⟨(Mem.put_ok hm h).1, (Mem.put_ok hm h).2.1⟩

theorem allocate_follows {s s' : St} {ptr size : ℕ} (hs : s.Good)
    (h : allocate s ptr size = .ok s') :
    St.Follows s s' := by
  unfold allocate at h
  dsimp only at h
  split_ifs at h
  · simp only [pure_ok] at h; subst h; exact St.Follows.refl hs
  · rw [bind_ok] at h
    obtain ⟨next, -, h⟩ := h
    rw [bind_ok] at h
    obtain ⟨s1, h1, h⟩ := h
    have f1 := St.withMem_follows hs (fun m' hm ↦ by
      split_ifs at hm
      · obtain ⟨h1, h2⟩ := put_le (hs.wf.ensure _) hm
        exact ⟨Mem.le_trans (Mem.le_ensure _ _) h1, h2⟩
      · exact put_le hs.wf hm) h1
    simp only [pure_ok] at h
    subst h
    exact f1.trans ⟨⟨f1.good.wf, (f1.good.dl.grow next).note _⟩, Mem.le_refl _, rfl, rfl, rfl⟩

theorem putRun_follows {s s' : St} {b : ℕ} {vs : List E} (hs : s.Good)
    (h : s.withMem (putRun b vs) = .ok s') : St.Follows s s' :=
  St.withMem_follows hs (fun _ hm ↦ putRun_ok hs.wf hm) h

theorem put_follows {s s' : St} {c : ℕ} {v : E} (hs : s.Good)
    (h : s.withMem (·.put c v) = .ok s') : St.Follows s s' :=
  St.withMem_follows hs (fun _ hm ↦ put_le hs.wf hm) h

/-- A hint keeps the registers and the count, and only extends the memory. -/
theorem runHint_follows {C : Ctx} {s s' : St} {hint : Hint} (hs : s.Good)
    (h : runHint C s hint = .ok s') : St.Follows s s' := by
  cases hint with
  | frameAddress offset =>
    simp only [runHint, bind_ok, pure_ok] at h
    obtain ⟨c, -, rfl⟩ := h
    exact ⟨⟨hs.wf, hs.dl.note c⟩, Mem.le_refl _, rfl, rfl, rfl⟩
  | alloc ptr size => exact allocate_follows hs h
  | allocDyn ptr size =>
    simp only [runHint, bind_ok] at h
    obtain ⟨sz, -, ⟨n, s1⟩, h1, h⟩ := h
    have f1 := (St.logOr_ok hs h1).1
    exact f1.trans (allocate_follows f1.good h)
  | allocFrames ptr size stop startInverse tail =>
    simp only [runHint, bind_ok] at h
    obtain ⟨sp, -, h⟩ := h
    split_ifs at h
    · simp [bind_ok] at h
    · rw [bind_ok] at h
      obtain ⟨⟨n, s1⟩, h1, h⟩ := h
      have f1 := (St.logOr_ok hs h1).1
      exact f1.trans (allocate_follows f1.good h)
  | witnessStack name base len =>
    simp only [runHint, bind_ok] at h
    obtain ⟨⟨v, s1⟩, h1, h⟩ := h
    have f1 := pop_follows hs h1
    exact f1.trans (putRun_follows f1.good h)
  | witnessHeap name ptr lo len =>
    simp only [runHint, bind_ok] at h
    obtain ⟨⟨b, s1⟩, h1, ⟨v, s2⟩, h2, h⟩ := h
    have f1 := heapBase_follows hs h1
    have f2 := pop_follows f1.good h2
    exact f1.trans (f2.trans (putRun_follows f2.good h))
  | log2Ceil bits dst nbits floor =>
    simp only [runHint, bind_ok] at h
    obtain ⟨⟨b, s1⟩, h1, h⟩ := h
    have f1 := bitsBase_follows hs h1
    exact f1.trans (put_follows f1.good h)
  | bitDecompose value bits nbits =>
    simp only [runHint, bind_ok] at h
    obtain ⟨⟨b, s1⟩, h1, h⟩ := h
    have f1 := bitsBase_follows hs h1
    exact f1.trans (putRun_follows f1.good h)
  | bitDecomposeExp value bits nbits =>
    simp only [runHint, bind_ok] at h
    obtain ⟨n, -, ⟨b, s1⟩, h1, h⟩ := h
    have f1 := bitsBase_follows hs h1
    exact f1.trans (putRun_follows f1.good h)
  | windowsExp value dest pos start width count =>
    simp only [runHint, bind_ok] at h
    obtain ⟨⟨b, s1⟩, h1, h⟩ := h
    have f1 := bitsBase_follows hs h1
    exact f1.trans (putRun_follows f1.good h)
  | digitDecomposeExp value dst nbits ndigits digitBits start startCell =>
    simp only [runHint, bind_ok] at h
    obtain ⟨n, -, h⟩ := h
    split at h <;>
    · simp only [bind_ok] at h
      obtain ⟨st, -, ⟨b, s1⟩, h1, h⟩ := h
      have f1 := bitsBase_follows hs h1
      exact f1.trans (putRun_follows f1.good h)
  | fieldLimbs value base len => exact putRun_follows hs h
  | inverse value dst => exact put_follows hs h

/-- The hints at a `pc`, in order. -/
theorem hints_follows {C : Ctx} :
    ∀ (l : List Hint) (s s' : St), s.Good → l.foldlM (runHint C) s = .ok s' → St.Follows s s'
  | [], s, s', hs, h => by
    simp only [List.foldlM_nil, pure_ok] at h; subst h; exact St.Follows.refl hs
  | x :: l, s, s', hs, h => by
    rw [List.foldlM_cons, bind_ok] at h
    obtain ⟨s1, h1, h⟩ := h
    have f1 := runHint_follows hs h1
    exact f1.trans (hints_follows l s1 s' f1.good h)

end

end LeanVM.Prover.Exec
