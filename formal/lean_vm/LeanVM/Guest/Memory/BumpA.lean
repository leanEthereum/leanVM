/-
  LeanVM.Guest.Memory.BumpA

  How far a hint moves the executor's bump pointer, aligned allocations included, read off the
  reference memory.
-/

module

public import LeanVM.Prover.ExecuteCompleteHint
public import LeanVM.Guest.Memory.Tree

/-!
# The bump pointer's moves, aligned

Hotwire's executor reserves a region of `n` cells from `allocBase a nextFree` (`Prover.Exec.allocate`):
at the next free cell, or for an `aligned` region at the next multiple of `keccakWindow`. So a hint
moves the bump pointer by a *step* `(a, n)`, `c ↦ allocBase a c + n` (`bump`), not by a size.

`rszA M s h`: the step hint `h` takes from state `s`, its sizes read off the reference `M` (a size
cell's exponent), `(false, 0)` for a hint reserving nothing. `runHint_nextFreeA`: a hint that
succeeds from a state whose memory agrees with `M` moves `nextFree` by exactly that step;
`hints_nextFreeA`: the hints at a pc move it by their steps in turn (`bumpL`).
-/

namespace LeanVM.Guest.Memory

open LeanVM.Parameters LeanVM.Semantics LeanVM.Prover.Exec

@[expose] public section

/-- **One bump**: a region of `q.2` cells reserved from `c`, aligned when `q.1`. -/
def bump (c : ℕ) (q : Bool × ℕ) : ℕ := allocBase q.1 c + q.2

/-- **The bump pointer after steps `qs` from `c`.** -/
def bumpL (c : ℕ) (qs : List (Bool × ℕ)) : ℕ := qs.foldl bump c

/-- **The step hint `h` takes from `s`**, its sizes read off `M`: its alignment and its cells. -/
noncomputable def rszA (M : ℕ → E) (s : St) : Hint → Bool × ℕ
  | .alloc _ n a => (a, n)
  | .allocDyn _ c => (false, logG (M (s.fp + c)))
  | .allocArm _ sel sizes a => (a, sizes.getD (logG (M (s.fp + sel))) 0)
  | .allocFrames _ size stop si tail a => (a, size * logG (ofK ((M (s.fp + stop)).limb 0 * si)) + tail)
  | _ => (false, 0)

/-- **The steps hints `hs` take**: a buffer hint the `n`-th buffer's cells on from `n`, unaligned, a
frame hint `fr`, any other hint none. -/
def stepsOf (isB isF : Hint → Bool) (buf : ℕ → ℕ) (fr : Bool × ℕ) : List Hint → ℕ → List (Bool × ℕ)
  | [], _ => []
  | h :: hs, n => (bif isB h then (false, buf n) else bif isF h then fr else (false, 0)) ::
      stepsOf isB isF buf fr hs (bif isB h then n + 1 else n)

/-- **The hints at an offset in their order**: once a frame is pending (`p`), no buffer and no frame
hint follows. -/
def ordHints (isB isF : Hint → Bool) : Bool → List Hint → Bool
  | _, [] => true
  | p, h :: hs => (!p || (!isB h && !isF h)) && ordHints isB isF (p || isF h) hs

end

public section

theorem length_stepsOf (isB isF : Hint → Bool) (buf : ℕ → ℕ) (fr : Bool × ℕ) :
    ∀ (hs : List Hint) (n : ℕ), (stepsOf isB isF buf fr hs n).length = hs.length
  | [], _ => rfl
  | _ :: hs, _ => by rw [stepsOf, List.length_cons, length_stepsOf _ _ _ _ hs, List.length_cons]

theorem allocBase_false (c : ℕ) : allocBase false c = c := by
  unfold allocBase; simp

theorem bump_nil (c : ℕ) : bumpL c [] = c := rfl

theorem bumpL_cons (c : ℕ) (q : Bool × ℕ) (qs : List (Bool × ℕ)) :
    bumpL c (q :: qs) = bumpL (bump c q) qs := rfl

theorem bumpL_append (c : ℕ) (qs qs' : List (Bool × ℕ)) :
    bumpL c (qs ++ qs') = bumpL (bumpL c qs) qs' := by
  unfold bumpL; rw [List.foldl_append]

theorem bumpL_concat (c : ℕ) (qs : List (Bool × ℕ)) (q : Bool × ℕ) :
    bumpL c (qs ++ [q]) = bump (bumpL c qs) q := by
  rw [bumpL_append]; rfl

theorem bump_zero (c : ℕ) : bump c (false, 0) = c := by
  unfold bump; rw [allocBase_false]; rfl

theorem le_bump (c : ℕ) (q : Bool × ℕ) : c ≤ bump c q := by
  unfold bump allocBase keccakWindow; split <;> omega

theorem le_bumpL : ∀ (c : ℕ) (qs : List (Bool × ℕ)), c ≤ bumpL c qs
  | _, [] => le_rfl
  | c, q :: qs => (le_bump c q).trans (le_bumpL _ qs)

theorem bump_mono {c c' : ℕ} (h : c ≤ c') (q : Bool × ℕ) : bump c q ≤ bump c' q := by
  unfold bump allocBase keccakWindow
  split
  · have := Nat.div_le_div_right (c := 16) (show c + 16 - 1 ≤ c' + 16 - 1 by omega)
    have := Nat.mul_le_mul_right 16 this
    omega
  · omega

theorem bumpL_mono : ∀ {c c' : ℕ} (_ : c ≤ c') (qs : List (Bool × ℕ)), bumpL c qs ≤ bumpL c' qs
  | _, _, h, [] => h
  | _, _, h, q :: qs => bumpL_mono (bump_mono h q) qs

theorem allocate_nextFree {s s' : St} {ptr size : ℕ} {a : Bool} (h : allocate s ptr size a = .ok s') :
    s'.nextFree = allocBase a s.nextFree + size := by
  unfold allocate at h
  rw [bind_ok] at h
  obtain ⟨cell, -, h⟩ := h
  dsimp only at h
  split at h
  · cases h
  · rw [bind_ok] at h
    obtain ⟨s1, h1, h⟩ := h
    simp only [pure_ok] at h
    subst h
    obtain ⟨m, -, rfl⟩ := St.withMem_ok h1
    rfl

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

theorem nf_bitsBase {s s' : St} {d : BitsDest} {len : ℕ} {what : String} {b : ℕ} (hD : s.dl.Ok)
    (h : bitsBase s d len what = .ok (b, s')) : s'.nextFree = s.nextFree := by
  unfold bitsBase at h
  split at h
  · simp only [bind_ok, pure_ok, Prod.mk.injEq] at h
    obtain ⟨c, -, -, rfl⟩ := h
    rfl
  · simp only [bind_ok, pure_ok, Prod.mk.injEq] at h
    obtain ⟨c, -, ⟨b', s1⟩, h1, c2, -, -, rfl⟩ := h
    exact nf_heapBase hD h1

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

/-- **A hint moves `nextFree` by the step it takes**, from a state whose written cells hold `M`'s
words. -/
theorem runHint_nextFreeA {C : Ctx} {M : ℕ → E} {s s' : St} (hM : ∀ c v, s.mem.get c = some v → M c = v)
    (hD : s.dl.Ok) {h : Hint} (e : runHint C s h = .ok s') : s'.nextFree = bump s.nextFree (rszA M s h) := by
  cases h with
  | frameAddress offset =>
    simp only [runHint, bind_ok, pure_ok] at e
    obtain ⟨c, -, rfl⟩ := e
    exact (bump_zero _).symm
  | alloc ptr size a => exact allocate_nextFree e
  | allocDyn ptr size =>
    simp only [runHint, bind_ok] at e
    obtain ⟨c, hc, sz, hsz, ⟨n, s1⟩, h1, e⟩ := e
    obtain ⟨rfl, -⟩ := cellAt_ok hc
    obtain ⟨n1, -, hm1, -, hg, hlt⟩ := logOr_keep hD h1
    rw [allocate_nextFree e, n1, rszA, (peek_pow hM hsz hg hlt).2]
    rfl
  | allocArm ptr sel sizes a =>
    simp only [runHint, bind_ok] at e
    obtain ⟨c, hc, x, hx, ⟨k, s1⟩, h1, e⟩ := e
    obtain ⟨rfl, -⟩ := cellAt_ok hc
    obtain ⟨n1, -, hm1, -, hg, hlt⟩ := logOr_keep hD h1
    split at e
    · rename_i n hn
      rw [allocate_nextFree e, n1, rszA, (peek_pow hM hx hg hlt).2, bump, List.getD_eq_getElem?_getD, hn]
      rfl
    · simp at e
  | allocFrames ptr size stop startInverse tail a =>
    simp only [runHint, bind_ok] at e
    obtain ⟨c, hc, sp, hsp, e⟩ := e
    obtain ⟨rfl, -⟩ := cellAt_ok hc
    split_ifs at e with h0
    · simp [bind_ok] at e
    · rw [bind_ok] at e
      obtain ⟨⟨n, s1⟩, h1, e⟩ := e
      obtain ⟨n1, -, -, -, hg, hlt⟩ := logOr_keep hD h1
      obtain ⟨hl1, rfl⟩ := inK_ok hsp
      rw [allocate_nextFree e, n1, rszA, bump]
      have hne : s.mem.peek (s.fp + stop) ≠ 0 := fun h ↦ h0 (by rw [h, limb_zero, zero_mul])
      have hMs : M (s.fp + stop) = s.mem.peek (s.fp + stop) := by
        cases hgt : s.mem.get (s.fp + stop) with
        | none => exact absurd (by rw [Mem.peek, hgt]; rfl) hne
        | some w => rw [hM _ w hgt, Mem.peek, hgt]; rfl
      dsimp only
      rw [hMs, ← hg, logG_spec (by unfold maxCells at hlt; omega)]
  | cellAddress ptr cell =>
    simp only [runHint, bind_ok] at e
    obtain ⟨c, -, p, -, e⟩ := e
    rw [(withMem_nextFree e).1]
    exact (bump_zero _).symm
  | witnessStack name base len =>
    simp only [runHint, bind_ok] at e
    obtain ⟨bs, -, ⟨v, s1⟩, h1, e⟩ := e
    rw [(withMem_nextFree e).1, nf_pop h1]
    exact (bump_zero _).symm
  | witnessHeap name ptr lo len =>
    simp only [runHint, bind_ok] at e
    obtain ⟨c, -, ⟨b, s1⟩, h1, bl, -, ⟨v, s2⟩, h2, e⟩ := e
    rw [(withMem_nextFree e).1, nf_pop h2, nf_heapBase hD h1]
    exact (bump_zero _).symm
  | log2Ceil bits dst nbits floor =>
    simp only [runHint, bind_ok] at e
    obtain ⟨⟨b, s1⟩, h1, d, -, e⟩ := e
    rw [(withMem_nextFree e).1, nf_bitsBase hD h1]
    exact (bump_zero _).symm
  | bitDecompose value bits nbits =>
    simp only [runHint, bind_ok] at e
    obtain ⟨c, -, ⟨b, s1⟩, h1, e⟩ := e
    rw [(withMem_nextFree e).1, nf_bitsBase hD h1]
    exact (bump_zero _).symm
  | bitDecomposeExp value bits nbits =>
    simp only [runHint, bind_ok] at e
    obtain ⟨c, -, n, -, ⟨b, s1⟩, h1, e⟩ := e
    rw [(withMem_nextFree e).1, nf_bitsBase hD h1]
    exact (bump_zero _).symm
  | windowsExp value dest pos start width count =>
    simp only [runHint, bind_ok] at e
    obtain ⟨c, -, ⟨b, s1⟩, h1, e⟩ := e
    rw [(withMem_nextFree e).1, nf_bitsBase hD h1]
    exact (bump_zero _).symm
  | digitDecomposeExp value dst nbits ndigits digitBits start startCell =>
    simp only [runHint, bind_ok] at e
    obtain ⟨c, -, n, -, e⟩ := e
    split at e
    · simp only [bind_ok] at e
      obtain ⟨st, -, ⟨b, s1⟩, h1, e⟩ := e
      rw [(withMem_nextFree e).1, nf_bitsBase hD h1]
      exact (bump_zero _).symm
    · simp only [bind_ok] at e
      obtain ⟨c', -, st, -, ⟨b, s1⟩, h1, e⟩ := e
      rw [(withMem_nextFree e).1, nf_bitsBase hD h1]
      exact (bump_zero _).symm
  | fieldLimbs value base len =>
    simp only [runHint, bind_ok] at e
    obtain ⟨c, -, b, -, e⟩ := e
    rw [(withMem_nextFree e).1]
    exact (bump_zero _).symm
  | inverse value dst =>
    simp only [runHint, bind_ok] at e
    obtain ⟨c, -, d, -, e⟩ := e
    rw [(withMem_nextFree e).1]
    exact (bump_zero _).symm

/-- **The steps of ordered hints from a cursor form**: from `cf n p` (the cursor past `n` buffers, a
frame pending when `p`), hints in their order (`ordHints`) bump it to the cursor past their
buffers, a frame pending when one was or is reserved; each buffer step moves `cf n false` to
`cf (n + 1) false` (needed only when there is a buffer hint), a frame step `cf n false` to
`cf n true`. -/
theorem bump_stepsOf {isB isF : Hint → Bool} {buf : ℕ → ℕ} {fr : Bool × ℕ} {cf : ℕ → Bool → ℕ}
    (hF : ∀ n, bump (cf n false) fr = cf n true) (hBF : ∀ h, isB h = true → isF h = false) :
    ∀ (hs : List Hint) (n : ℕ) (p : Bool), ordHints isB isF p hs = true →
      (0 < hs.countP isB → ∀ n, bump (cf n false) (false, buf n) = cf (n + 1) false) →
      bumpL (cf n p) (stepsOf isB isF buf fr hs n) = cf (n + hs.countP isB) (p || hs.any isF)
  | [], n, p, _, _ => by simp [stepsOf, bumpL]
  | h :: hs, n, p, ho, hB => by
    simp only [ordHints, Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true'] at ho
    obtain ⟨h1, h2⟩ := ho
    have hB' : 0 < hs.countP isB → ∀ n, bump (cf n false) (false, buf n) = cf (n + 1) false :=
      fun hc ↦ hB (by rw [List.countP_cons]; omega)
    rw [stepsOf, bumpL_cons, List.countP_cons, List.any_cons]
    cases hb : isB h
    · cases hf : isF h
      · have h2' : ordHints isB isF p hs = true := by simpa [hf] using h2
        have ih := bump_stepsOf hF hBF hs n p h2' hB'
        simp only [Bool.cond_false, bump_zero]
        rw [ih]
        simp
      · have hp : p = false := by
          rcases h1 with h1 | ⟨-, h1⟩
          · exact h1
          · rw [hf] at h1; cases h1
        subst hp
        have h2' : ordHints isB isF true hs = true := by simpa [hf] using h2
        have ih := bump_stepsOf hF hBF hs n true h2' hB'
        simp only [Bool.cond_false, Bool.cond_true, hF]
        rw [ih]
        simp
    · have hf : isF h = false := hBF h hb
      have hp : p = false := by
        rcases h1 with h1 | ⟨h1, -⟩
        · exact h1
        · rw [hb] at h1; cases h1
      subst hp
      have h2' : ordHints isB isF false hs = true := by simpa [hf] using h2
      have ih := bump_stepsOf hF hBF hs (n + 1) false h2' hB'
      simp only [Bool.cond_true, hB (by rw [List.countP_cons, hb]; simp) n]
      rw [ih]
      simp only [hf, Bool.false_or, ↓reduceIte]
      congr 1
      omega

/-- **The hints at a pc move `nextFree` by the steps `qs`**, the `i`-th hint taking `qs[i]` from
the state the hints before it reach, all from a state whose cells written by their end hold `M`'s
words. -/
theorem hints_nextFreeA {C : Ctx} {M : ℕ → E} :
    ∀ (l : List Hint) (qs : List (Bool × ℕ)) (s s1 : St), s.Good → l.foldlM (runHint C) s = .ok s1 →
      (∀ c v, s1.mem.get c = some v → M c = v) → l.length = qs.length →
      (∀ (i : ℕ) (h : Hint) (sx : St), l[i]? = some h → (l.take i).foldlM (runHint C) s = .ok sx →
        rszA M sx h = qs.getD i (false, 0)) →
      s1.nextFree = bumpL s.nextFree qs
  | [], qs, s, s1, _, e, _, hl, _ => by
    simp only [List.foldlM_nil, pure_ok] at e
    subst e
    cases qs with
    | nil => rfl
    | cons => simp at hl
  | h :: l, qs, s, s1, hs, e, hM, hl, hsz => by
    rw [List.foldlM_cons, bind_ok] at e
    obtain ⟨s2, e2, e⟩ := e
    cases qs with
    | nil => simp at hl
    | cons q qs =>
      have f2 := runHint_follows hs e2
      have f1 := hints_follows l s2 s1 f2.good e
      have hM2 : ∀ c v, s2.mem.get c = some v → M c = v := fun c v hv ↦ hM c v (f1.le.get _ _ hv)
      have hMs : ∀ c v, s.mem.get c = some v → M c = v := fun c v hv ↦ hM2 c v (f2.le.get _ _ hv)
      have h0 := runHint_nextFreeA hMs hs.dl e2
      rw [hsz 0 h s rfl rfl] at h0
      have ih := hints_nextFreeA l qs s2 s1 f2.good e hM (by simpa using hl) fun i h' sx hi hx ↦ by
        have := hsz (i + 1) h' sx (by simpa using hi) (by
          rw [List.take_succ_cons, List.foldlM_cons, e2]
          exact hx)
        simpa using this
      rw [ih, h0, bumpL_cons]
      rfl

end

end LeanVM.Guest.Memory
