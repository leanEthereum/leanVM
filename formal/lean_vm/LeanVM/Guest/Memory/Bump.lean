/-
  LeanVM.Guest.Memory.Bump

  How far a hint moves the executor's bump pointer, read off the reference memory.
-/

module

public import LeanVM.Prover.ExecuteCompleteHint
public import LeanVM.Guest.Memory.Tree

/-!
# The bump pointer's moves

`rsz C M s h`: the cells hint `h` reserves from state `s`, its sizes read off the reference `M`
(a size cell's exponent), the stream's next entry, or nothing for a late hint whose pointer is
written. `runHint_nextFree`: a hint that succeeds from a state whose memory agrees with `M` moves
`nextFree` by exactly that.
-/

namespace LeanVM.Guest.Memory

open LeanVM.Parameters LeanVM.Semantics LeanVM.Prover.Exec

@[expose] public section

/-- The exponent of a stream's next entry, a single word; `0` for an empty entry. -/
noncomputable def advSize (C : Ctx) (s : St) (S : String) : ℕ :=
  match (C.streams[S]?).bind fun es ↦ es[s.cursor.getD S 0]? with
  | some [w] => logG w
  | _ => 0

/-- **The cells hint `h` reserves from `s`**, its sizes read off `M`. -/
noncomputable def rsz (C : Ctx) (M : ℕ → E) (s : St) : Hint → ℕ
  | .alloc _ n => n
  | .allocDyn _ c => logG (M (s.fp + c))
  | .allocAdvice _ S => advSize C s S
  | .allocArm _ sel sizes => sizes.getD (logG (M (s.fp + sel))) 0
  | .allocFrames _ size stop si tail => size * logG (ofK ((M (s.fp + stop)).limb 0 * si)) + tail
  | .allocLate p (.cells n) => if s.mem.written (s.fp + p) then 0 else n
  | .allocLate p (.exp c) => if s.mem.written (s.fp + p) then 0 else logG (M (s.fp + c))
  | _ => 0

end

public section

theorem allocate_nextFree {s s' : St} {ptr size : ℕ} (h : allocate s ptr size = .ok s') :
    s'.nextFree = s.nextFree + size := by
  unfold allocate at h
  dsimp only at h
  split at h
  · cases h
  · rw [bind_ok] at h
    obtain ⟨s1, -, h⟩ := h
    simp only [pure_ok] at h
    subst h
    rfl

theorem allocateLate_nextFree {s s' : St} {ptr size : ℕ} (h : allocateLate s ptr size = .ok s') :
    s'.nextFree = s.nextFree + if s.mem.written (s.fp + ptr) then 0 else size := by
  unfold allocateLate at h
  by_cases hw : s.mem.written (s.fp + ptr) = true
  · rw [ite_eq_left hw] at h
    simp only [pure_ok] at h
    subst h
    rw [ite_eq_left hw]
    rfl
  · rw [ite_eq_right hw] at h
    rw [ite_eq_right hw]
    exact allocate_nextFree h

theorem withMem_nextFree {s s' : St} {f : Mem → Except Fault Mem} (h : s.withMem f = .ok s') :
    s'.nextFree = s.nextFree ∧ s'.fp = s.fp ∧ s'.cursor = s.cursor := by
  obtain ⟨m, -, rfl⟩ := St.withMem_ok h
  exact ⟨rfl, rfl, rfl⟩

theorem logOr_keep {s s' : St} {x : K} {b k : ℕ} {f : Fault} (hD : s.dl.Ok) (h : s.logOr x b f = .ok (k, s')) :
    s'.nextFree = s.nextFree ∧ s'.fp = s.fp ∧ s'.mem = s.mem ∧ s'.cursor = s.cursor ∧ g ^ k = x ∧ k < b := by
  unfold St.logOr at h
  rw [St.log_eq] at h
  obtain ⟨-, hk⟩ := Dlog.log_ok hD x b
  split at h
  · rename_i k' s1 hp
    simp only [pure_ok, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    simp only [Prod.mk.injEq] at hp
    obtain ⟨h1, rfl⟩ := hp
    exact ⟨rfl, rfl, rfl, rfl, hk _ h1⟩
  · simp at h

theorem popEntry_eq {C : Ctx} {s s' : St} {name : String} {v : List E} (h : popEntry C s name = .ok (v, s')) :
    ((C.streams[name]?).bind fun es ↦ es[s.cursor.getD name 0]?) = some v ∧ s'.nextFree = s.nextFree ∧
      s'.dl = s.dl ∧ s'.mem = s.mem ∧ s'.fp = s.fp := by
  unfold popEntry at h
  split at h
  · rename_i entries hS
    dsimp only at h
    split at h
    · rename_i w hw
      simp only [pure_ok, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      rw [hS, Option.bind_some, hw]
      exact ⟨rfl, rfl, rfl, rfl, rfl⟩
    · simp at h
  · simp at h

theorem nf_pop {C : Ctx} {s s' : St} {name : String} {len : ℕ} {v : List E}
    (h : pop C s name len = .ok (v, s')) : s'.nextFree = s.nextFree := by
  unfold pop at h
  split at h
  · dsimp only at h
    split at h
    · split_ifs at h
      · cases h
      · simp only [pure_ok, Prod.mk.injEq] at h
        obtain ⟨-, rfl⟩ := h
        rfl
    · simp at h
  · simp at h

theorem nf_heapBase {s s' : St} {c b : ℕ} {what : String} (hD : s.dl.Ok) (h : heapBase s c what = .ok (b, s')) :
    s'.nextFree = s.nextFree := by
  unfold heapBase at h
  rw [bind_ok] at h
  obtain ⟨p, -, h⟩ := h
  exact (logOr_keep hD h).1

theorem nf_bitsBase {s s' : St} {d : BitsDest} {what : String} {b : ℕ} (hD : s.dl.Ok)
    (h : bitsBase s d what = .ok (b, s')) : s'.nextFree = s.nextFree := by
  unfold bitsBase at h
  split at h
  · simp only [pure_ok, Prod.mk.injEq] at h
    obtain ⟨-, rfl⟩ := h
    rfl
  · exact nf_heapBase hD h

/-- **A word read as a power `g^k`**, `k < maxCells`, from a memory agreeing with `M`: `M`'s word. -/
theorem peek_pow {m : Mem} {M : ℕ → E} (hm : ∀ c v, m.get c = some v → M c = v) {c k : ℕ} {what : String} {x : K}
    (hx : inK what (m.peek c) = .ok x) (hk : g ^ k = x) (hlt : k < maxCells) :
    M c = ofK (g ^ k) ∧ logG (M c) = k := by
  obtain ⟨h1, rfl⟩ := inK_ok hx
  have hv : m.peek c = ofK (g ^ k) := E.ext fun i ↦ by
    fin_cases i
    · simp [hk]
    · simpa using h1
  have hMc : M c = ofK (g ^ k) := by
    cases hg : m.get c with
    | none =>
      rw [Mem.peek, hg] at hv
      exact absurd hv.symm ((map_ne_zero (algebraMap K E)).mpr (pow_ne_zero _ g_ne_zero))
    | some w => rw [hm c w hg, ← hv, Mem.peek, hg]; rfl
  refine ⟨hMc, ?_⟩
  rw [hMc]
  exact logG_spec (by unfold maxCells at hlt; omega)

/-- **A hint moves `nextFree` by the cells it reserves**, from a state whose written cells hold
`M`'s words. -/
theorem runHint_nextFree {C : Ctx} {M : ℕ → E} {s s' : St} (hM : ∀ c v, s.mem.get c = some v → M c = v)
    (hD : s.dl.Ok) {h : Hint} (e : runHint C s h = .ok s') : s'.nextFree = s.nextFree + rsz C M s h := by
  cases h with
  | frameAddress offset =>
    simp only [runHint, bind_ok, pure_ok] at e
    obtain ⟨c, -, rfl⟩ := e
    rfl
  | alloc ptr size => exact allocate_nextFree e
  | allocDyn ptr size =>
    simp only [runHint, bind_ok] at e
    obtain ⟨sz, hsz, ⟨n, s1⟩, h1, e⟩ := e
    obtain ⟨n1, -, hm1, -, hg, hlt⟩ := logOr_keep hD h1
    rw [allocate_nextFree e, n1, rsz, (peek_pow hM hsz hg hlt).2]
  | allocAdvice ptr stream =>
    simp only [runHint, bind_ok] at e
    obtain ⟨⟨v, s1⟩, h1, e⟩ := e
    obtain ⟨hv, n1, d1, -, -⟩ := popEntry_eq h1
    rw [rsz, advSize, hv]
    rcases v with _ | ⟨w, _ | ⟨w', v⟩⟩ <;> dsimp only at e ⊢
    · simp only [pure_ok] at e; subst e; rw [n1]; rfl
    · simp only [bind_ok] at e
      obtain ⟨sz, hsz, ⟨n, s2⟩, h2, e⟩ := e
      obtain ⟨n2, -, -, -, hg, hlt⟩ := logOr_keep (d1 ▸ hD) h2
      obtain ⟨hl1, rfl⟩ := inK_ok hsz
      rw [allocate_nextFree e, n2, n1]
      congr 1
      have hw' : w = ofK (g ^ n) := E.ext fun i ↦ by
        fin_cases i
        · simp [hg]
        · simpa using hl1
      rw [hw']
      exact (logG_spec (by unfold maxCells at hlt; omega)).symm
    · simp at e
  | allocArm ptr sel sizes =>
    simp only [runHint, bind_ok] at e
    obtain ⟨x, hx, ⟨k, s1⟩, h1, e⟩ := e
    obtain ⟨n1, -, hm1, -, hg, hlt⟩ := logOr_keep hD h1
    split at e
    · rename_i n hn
      rw [allocate_nextFree e, n1, rsz, (peek_pow hM hx hg hlt).2, List.getD_eq_getElem?_getD, hn]
      rfl
    · simp at e
  | allocFrames ptr size stop startInverse tail =>
    simp only [runHint, bind_ok] at e
    obtain ⟨sp, hsp, e⟩ := e
    split_ifs at e with h0
    · simp [bind_ok] at e
    · rw [bind_ok] at e
      obtain ⟨⟨n, s1⟩, h1, e⟩ := e
      obtain ⟨n1, -, -, -, hg, hlt⟩ := logOr_keep hD h1
      obtain ⟨hl1, rfl⟩ := inK_ok hsp
      rw [allocate_nextFree e, n1, rsz]
      have hne : s.mem.peek (s.fp + stop) ≠ 0 := fun h ↦ h0 (by rw [h, limb_zero, zero_mul])
      have hMs : M (s.fp + stop) = s.mem.peek (s.fp + stop) := by
        cases hgt : s.mem.get (s.fp + stop) with
        | none => exact absurd (by rw [Mem.peek, hgt]; rfl) hne
        | some w => rw [hM _ w hgt, Mem.peek, hgt]; rfl
      rw [hMs, ← hg, logG_spec (by unfold maxCells at hlt; omega)]
  | allocLate ptr size =>
    simp only [runHint, bind_ok] at e
    obtain ⟨⟨n, s1⟩, h1, e⟩ := e
    rw [allocateLate_nextFree e]
    cases size with
    | cells k =>
      simp only [bufSize, pure_ok, Prod.mk.injEq] at h1
      obtain ⟨rfl, rfl⟩ := h1
      rfl
    | exp c =>
      simp only [bufSize, bind_ok] at h1
      obtain ⟨sz, hsz, h1⟩ := h1
      obtain ⟨n1, f1, m1, -, hg, hlt⟩ := logOr_keep hD h1
      rw [n1, f1, m1, rsz, (peek_pow hM hsz hg hlt).2]
  | cellAddress ptr cell =>
    simp only [runHint, bind_ok] at e
    obtain ⟨c, -, e⟩ := e
    exact (withMem_nextFree e).1
  | witnessStack name base len =>
    simp only [runHint, bind_ok] at e
    obtain ⟨⟨v, s1⟩, h1, e⟩ := e
    rw [(withMem_nextFree e).1, nf_pop h1]
    rfl
  | witnessHeap name ptr lo len =>
    simp only [runHint, bind_ok] at e
    obtain ⟨⟨b, s1⟩, h1, ⟨v, s2⟩, h2, e⟩ := e
    rw [(withMem_nextFree e).1, nf_pop h2, nf_heapBase hD h1]
    rfl
  | log2Ceil bits dst nbits floor =>
    simp only [runHint, bind_ok] at e
    obtain ⟨⟨b, s1⟩, h1, e⟩ := e
    rw [(withMem_nextFree e).1, nf_bitsBase hD h1]
    rfl
  | bitDecompose value bits nbits =>
    simp only [runHint, bind_ok] at e
    obtain ⟨⟨b, s1⟩, h1, e⟩ := e
    rw [(withMem_nextFree e).1, nf_bitsBase hD h1]
    rfl
  | bitDecomposeExp value bits nbits =>
    simp only [runHint, bind_ok] at e
    obtain ⟨n, -, ⟨b, s1⟩, h1, e⟩ := e
    rw [(withMem_nextFree e).1, nf_bitsBase hD h1]
    rfl
  | windowsExp value dest pos start width count =>
    simp only [runHint, bind_ok] at e
    obtain ⟨⟨b, s1⟩, h1, e⟩ := e
    rw [(withMem_nextFree e).1, nf_bitsBase hD h1]
    rfl
  | digitDecomposeExp value dst nbits ndigits digitBits start startCell =>
    simp only [runHint, bind_ok] at e
    obtain ⟨n, -, e⟩ := e
    split at e
    all_goals
      simp only [bind_ok] at e
      obtain ⟨st, -, ⟨b, s1⟩, h1, e⟩ := e
      rw [(withMem_nextFree e).1, nf_bitsBase hD h1]
      rfl
  | fieldLimbs value base len => rw [(withMem_nextFree e).1]; rfl
  | inverse value dst =>
    simp only [runHint] at e
    rw [(withMem_nextFree e).1]
    rfl

/-- **The hints at a pc move `nextFree` by the sizes `ns`**, the `i`-th hint reserving `ns[i]`
from the state the hints before it reach, all from a state whose cells written by their end hold
`M`'s words. -/
theorem hints_nextFree {C : Ctx} {M : ℕ → E} :
    ∀ (l : List Hint) (ns : List ℕ) (s s1 : St), s.Good → l.foldlM (runHint C) s = .ok s1 →
      (∀ c v, s1.mem.get c = some v → M c = v) → l.length = ns.length →
      (∀ (i : ℕ) (h : Hint) (sx : St), l[i]? = some h → (l.take i).foldlM (runHint C) s = .ok sx →
        rsz C M sx h = ns.getD i 0) →
      s1.nextFree = s.nextFree + ns.sum
  | [], ns, s, s1, _, e, _, hl, _ => by
    simp only [List.foldlM_nil, pure_ok] at e
    subst e
    cases ns with
    | nil => rfl
    | cons => simp at hl
  | h :: l, ns, s, s1, hs, e, hM, hl, hsz => by
    rw [List.foldlM_cons, bind_ok] at e
    obtain ⟨s2, e2, e⟩ := e
    cases ns with
    | nil => simp at hl
    | cons n ns =>
      have f2 := runHint_follows hs e2
      have f1 := hints_follows l s2 s1 f2.good e
      have hM2 : ∀ c v, s2.mem.get c = some v → M c = v := fun c v hv ↦ hM c v (f1.le.get _ _ hv)
      have hMs : ∀ c v, s.mem.get c = some v → M c = v := fun c v hv ↦ hM2 c v (f2.le.get _ _ hv)
      have h0 := runHint_nextFree hMs hs.dl e2
      rw [hsz 0 h s rfl rfl] at h0
      have ih := hints_nextFree l ns s2 s1 f2.good e hM (by simpa using hl) fun i h' sx hi hx ↦ by
        have := hsz (i + 1) h' sx (by simpa using hi) (by
          rw [List.take_succ_cons, List.foldlM_cons, e2]
          exact hx)
        simpa using this
      rw [ih, h0, List.sum_cons]
      simp only [List.getD_cons_zero]
      omega

end

end LeanVM.Guest.Memory
