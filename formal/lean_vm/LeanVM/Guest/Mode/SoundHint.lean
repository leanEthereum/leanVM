module

public import LeanVM.Guest.Mode.SoundDeref

/-!
# One hint of the walk is sound

`stepHint_sound`: a hint the walk accepts reads written cells (`HintIn`: the cells its value reads
peek, so that they read what the reference holds), and leaves a state where the walk's next set
holds.
-/

namespace LeanVM.Guest.Mode

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest
open LeanVM.Prover.Exec

@[expose] public section

/-- A run's start reads written cells: a heap run's pointer. -/
def DestIn (s : St) : BitsDest → Prop
  | .stack _ => True
  | .heap ptr => s.mem.written (s.fp + ptr) = true

/-- The cells a hint reads are written. -/
def HintIn (s : St) : Hint → Prop
  | .allocDyn _ size => s.mem.written (s.fp + size) = true
  | .allocArm _ sel _ => s.mem.written (s.fp + sel) = true
  | .allocFrames _ _ stop _ _ => s.mem.written (s.fp + stop) = true
  | .witnessHeap _ ptr _ _ => s.mem.written (s.fp + ptr) = true
  | .log2Ceil bits _ nbits _ => match bits with
    | .stack base => ∀ j < nbits, s.mem.written (s.fp + base + j) = true
    | .heap ptr => s.mem.written (s.fp + ptr) = true ∧ ∀ p x, s.mem.get (s.fp + ptr) = some p →
        Names p x → ∀ j < nbits, x + j < maxCells → s.mem.written (x + j) = true
  | .bitDecompose value bits _ => s.mem.written (s.fp + value) = true ∧ DestIn s bits
  | .bitDecomposeExp value bits _ => s.mem.written (s.fp + value) = true ∧ DestIn s bits
  | .windowsExp value dest _ _ _ _ => s.mem.written (s.fp + value) = true ∧ DestIn s dest
  | .digitDecomposeExp value dst _ _ _ _ startCell => s.mem.written (s.fp + value) = true ∧
    (∀ c, startCell = some c → s.mem.written (s.fp + c) = true) ∧ DestIn s dst
  | .fieldLimbs value _ _ => s.mem.written (s.fp + value) = true
  | .inverse value _ => s.mem.written (s.fp + value) = true
  | _ => True

/-! ## What hints write -/

theorem putRun_vals {b : ℕ} {vs : List E} {m m' : Mem} (hm : m.WF) (e : putRun b vs m = .ok m') :
    m ≤ m' ∧ ∀ j (hj : j < vs.length), m'.get (b + j) = some vs[j] := by
  unfold putRun at e
  obtain ⟨h1, -, h3⟩ := Mem.foldlM_ok _ (fun (x : E × ℕ) (m : Mem) ↦ m.get (b + x.2) = some x.1)
    (fun x m m' (h : m.get (b + x.2) = some x.1) (hle : m ≤ m') ↦ hle.get _ _ h)
    (fun m x m' hm e ↦ by
      obtain ⟨v, k⟩ := x
      obtain ⟨h1, h2, h3⟩ := Mem.put_ok hm e
      exact ⟨h1, h2, h3⟩) _ m m' hm e
  exact ⟨h1, fun j hj ↦ h3 (vs[j], j) (List.mem_iff_getElem.mpr ⟨j, by simpa using hj, by simp⟩)⟩

theorem withMem_putRun {s s' : St} {b : ℕ} {vs : List E} (hs : s.Good)
    (e : s.withMem (putRun b vs) = .ok s') :
    s.mem ≤ s'.mem ∧ s'.fp = s.fp ∧ ∀ j (hj : j < vs.length), s'.mem.get (b + j) = some vs[j] := by
  obtain ⟨m, hm, rfl⟩ := St.withMem_ok e
  obtain ⟨h1, h2⟩ := putRun_vals hs.wf hm
  exact ⟨h1, rfl, h2⟩

theorem heapBase_val {s s1 : St} {c b : ℕ} {what : String} (hs : s.Good)
    (h : heapBase s c what = .ok (b, s1)) (hw : s.mem.written c = true) :
    St.Follows s s1 ∧ s1.mem = s.mem ∧ ∃ p, s.mem.get c = some p ∧ p = ofK (g ^ b) ∧ b < maxCells := by
  unfold heapBase at h
  rw [bind_ok] at h
  obtain ⟨x, hx, h⟩ := h
  obtain ⟨f, hg, hb⟩ := St.logOr_ok hs h
  obtain ⟨p, hp⟩ := Mem.get_of_written hw
  obtain ⟨h1, rfl⟩ := inK_ok hx
  rw [Mem.peek_of_get hp] at h1 hg
  have hmem : s1.mem = s.mem := by
    unfold St.logOr at h; rw [St.log_eq] at h
    split at h
    · rename_i k' s2 hk
      simp only [pure_ok, Prod.mk.injEq] at h
      obtain ⟨-, rfl⟩ := h
      simp only [Prod.mk.injEq] at hk
      obtain ⟨-, rfl⟩ := hk
      rfl
    · simp at h
  refine ⟨f, hmem, p, hp, E.ext fun i ↦ ?_, hb⟩
  fin_cases i
  · simp [hg]
  · simpa using h1

theorem bitsBase_val {s s1 : St} {d : BitsDest} {what : String} {b : ℕ} (hs : s.Good)
    (h : bitsBase s d what = .ok (b, s1)) (hd : DestIn s d) :
    St.Follows s s1 ∧ s1.mem = s.mem ∧
      (∀ base, d = .stack base → b = s.fp + base) ∧
      (∀ ptr, d = .heap ptr → ∃ p, s.mem.get (s.fp + ptr) = some p ∧ p = ofK (g ^ b) ∧ b < maxCells) := by
  cases d with
  | stack base =>
    simp only [bitsBase, pure_ok, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨St.Follows.refl hs, rfl, fun _ h ↦ by cases h; rfl, fun _ h ↦ nomatch h⟩
  | heap ptr =>
    obtain ⟨f, hm, hp⟩ := heapBase_val hs h hd
    exact ⟨f, hm, fun _ h ↦ BitsDest.noConfusion h, fun _ h ↦ by cases h; exact hp⟩

theorem allocate_written {s s' : St} {ptr size : ℕ} (hs : s.Good) (h : allocate s ptr size = .ok s') :
    St.Follows s s' ∧ s'.mem.written (s.fp + ptr) = true := by
  refine ⟨allocate_follows hs h, ?_⟩
  unfold allocate at h
  dsimp only at h
  split_ifs at h with hw
  · simp only [pure_ok] at h; subst h; exact hw
  · rw [bind_ok] at h
    obtain ⟨next, -, h⟩ := h
    rw [bind_ok] at h
    obtain ⟨s1, h1, h⟩ := h
    simp only [pure_ok] at h; subst h
    obtain ⟨m, hm, rfl⟩ := St.withMem_ok h1
    split_ifs at hm
    · exact put_written (hs.wf.ensure _) hm
    · exact put_written hs.wf hm

/-! ## Runs -/

theorem foldl_range_holds {s : St} (F : Abs → ℕ → Abs) (A : Abs) (n : ℕ) (hA : Holds s A)
    (hF : ∀ B k, k < n → Holds s B → Holds s (F B k)) : Holds s ((List.range n).foldl F A) := by
  induction n with
  | zero => exact hA
  | succ n ih =>
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    exact hF _ n (by omega) (ih fun B k hk hB ↦ hF B k (by omega) hB)

/-- Writing a run: what the walk adds holds when the run's cells were written (and, for exponents
below `2^b`, hold powers). -/
theorem writeRun_sound {s : St} {A : Abs} (hH : Holds s A) (hfp : s.fp < maxCells)
    (hu : s.mem.used ≤ maxCells) (hwf : s.mem.WF) {dst : Option ℕ × Option Mono} {pos n : ℕ} {bits : Option ℕ}
    (hst : ∀ base, dst.1 = some base → ∀ j < n, ∃ v, s.mem.get (s.fp + (base + pos + j)) = some v ∧
      ∀ b, bits = some b → ∃ w < 2 ^ b, v = ofK (g ^ w))
    (hhp : ∀ m, dst = (none, some m) → ∃ p b, MonoVal s m p ∧ p = ofK (g ^ b) ∧
      ∀ j < n, s.mem.written (b + (pos + j)) = true) :
    Holds s (writeRun A dst pos n bits) := by
  rcases dst with ⟨_ | base, mo⟩
  · cases mo with
    | none => exact hH
    | some m =>
      obtain ⟨p, b, hm, hp, hw⟩ := hhp m rfl
      refine foldl_range_holds _ A n hH fun B k hk hB ↦ ?_
      have hwk := hw k hk
      obtain ⟨u, hu'⟩ := Mem.get_of_written hwk
      have hlt := hwf.get_lt hu'
      have hkv := hm.shift (pos + k)
      have hX : Names (p * ofK (g ^ (pos + k))) (b + (pos + k)) := by
        refine ⟨?_, by omega⟩
        rw [hp, ← ofK_mul, ← pow_add]; simp
      exact hB.addH ⟨_, _, hkv, hX, hwk⟩
        fun d hd ↦ by rw [← own_names hfp hd hkv hX]; exact hwk
  · refine foldl_range_holds _ A n hH fun B k hk hB ↦ ?_
    obtain ⟨v, hv, hb⟩ := hst base rfl k hk
    have h1 := hB.addW (o := base + pos + k) (written_of_get hv)
    dsimp only
    cases bits with
    | none => exact h1
    | some b =>
      obtain ⟨w, hw, rfl⟩ := hb b rfl
      have h2 := h1.addNz (o := base + pos + k) ⟨_, hv, ofK_gpow_ne_zero w⟩
      dsimp only
      split_ifs with h61
      · exact h2.addLt ⟨w, 2 ^ b, ⟨_, w, hv, rfl, lt_of_lt_of_le hw
          (Nat.pow_le_pow_right (by norm_num) (by omega)), rfl⟩, rfl, hw⟩
      · exact h2

theorem pop_len {C : Ctx} {s s1 : St} {name : String} {len : ℕ} {v : List E} (hs : s.Good)
    (h : pop C s name len = .ok (v, s1)) : v.length = len ∧ St.Follows s s1 ∧ s1.mem = s.mem := by
  refine ⟨?_, pop_follows hs h, ?_⟩ <;>
  · unfold pop at h
    split at h
    · dsimp only at h
      split at h
      · split_ifs at h with hl
        · cases h
        · simp only [pure_ok, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          first | exact not_not.mp hl | rfl
      · simp at h
    · simp at h

/-- The state after a hint whose effect on the memory is `hm`: the walk's set, unchanged, holds. -/
theorem Holds.follows {s s' : St} {A : Abs} (hH : Holds s A) (f : St.Follows s s') : Holds s' A :=
  hH.mono f.le f.fp

theorem destOf_heap {A : Abs} {ptr : ℕ} {d : Option ℕ × Option Mono} (h : destOf A (.heap ptr) = some d) :
    A.hasW ptr = true ∧ ∃ m, A.mono ptr = some m ∧ d = (none, some m) := by
  simp only [destOf] at h
  split_ifs at h with hw
  obtain ⟨m, hm, rfl⟩ := Option.map_eq_some_iff.mp h
  exact ⟨hw, m, hm, rfl⟩

/-- Writing a run from a hint's start `b` (`bitsBase`), `vs` its words: what `writeRun` adds holds. -/
theorem runFrom_sound {s s' : St} {A : Abs} (hH : Holds s A) (hfp : s.fp < maxCells)
    {bits : BitsDest} {d : Option ℕ × Option Mono} (hd : destOf A bits = some d) {b pos : ℕ}
    {vs : List E} {bb : Option ℕ}
    (hb1 : ∀ base, bits = .stack base → b = s.fp + base)
    (hb2 : ∀ ptr, bits = .heap ptr → ∃ p, s.mem.get (s.fp + ptr) = some p ∧ p = ofK (g ^ b) ∧ b < maxCells)
    (hle : s.mem ≤ s'.mem) (hfp' : s'.fp = s.fp) (hu : s'.mem.used ≤ maxCells) (hwf : s'.mem.WF)
    (hvs : ∀ j (hj : j < vs.length), s'.mem.get (b + pos + j) = some vs[j])
    (hpow : ∀ j (hj : j < vs.length), ∀ c, bb = some c → ∃ w < 2 ^ c, vs[j] = ofK (g ^ w)) :
    Holds s' (writeRun A d pos vs.length bb) := by
  have hH' := hH.mono hle hfp'
  cases bits with
  | stack base =>
    simp only [destOf, Option.some.injEq] at hd
    subst hd
    obtain rfl := hb1 base rfl
    refine writeRun_sound hH' (hfp' ▸ hfp) hu hwf (fun base' hb j hj ↦ ?_) (fun _ h ↦ by cases h)
    cases hb
    refine ⟨vs[j], ?_, fun c hc ↦ hpow j hj c hc⟩
    rw [hfp', ← hvs j hj]; congr 1; omega
  | heap ptr =>
    obtain ⟨hw, m, hm, rfl⟩ := destOf_heap hd
    obtain ⟨p, hp, hpb, hbl⟩ := hb2 ptr rfl
    refine writeRun_sound hH' (hfp' ▸ hfp) hu hwf (fun _ h ↦ by cases h) (fun m' h ↦ ?_)
    cases h
    obtain ⟨u, hu1, hu2⟩ := hH.mono_val hm (hH.written hw)
    rw [hp] at hu1; cases hu1
    refine ⟨p, b, hu2.mono hle hfp', hpb, fun j hj ↦ ?_⟩
    rw [← Nat.add_assoc]
    exact written_of_get (hvs j hj)

theorem bits_run {s s' : St} {b : ℕ} {f : ℕ → E} {n : ℕ} (hs : s.Good)
    (e : s.withMem (putRun b ((List.range n).map f)) = .ok s') :
    s.mem ≤ s'.mem ∧ s'.fp = s.fp ∧ s'.mem.WF ∧
      ∀ j (hj : j < ((List.range n).map f).length), s'.mem.get (b + 0 + j) = some ((List.range n).map f)[j] := by
  obtain ⟨m, hm, rfl⟩ := St.withMem_ok e
  obtain ⟨h1, h2⟩ := putRun_vals hs.wf hm
  exact ⟨h1, rfl, (putRun_ok hs.wf hm).2, fun j hj ↦ by rw [Nat.add_zero]; exact h2 j hj⟩

/-- **One hint the walk accepts.** -/
theorem stepHint_sound {C : Ctx} {s s' : St} {A A' : Abs} {h : Hint} (hs : s.Good)
    (hfp : s.fp < maxCells) (hu : s.mem.used ≤ maxCells) (hH : Holds s A)
    (hstep : stepHint A h = some A') :
    HintIn s h ∧ (runHint C s h = .ok s' → s'.mem.used ≤ maxCells → Holds s' A') := by
  cases h with
  | frameAddress offset =>
    cases hstep
    exact ⟨trivial, fun e _ ↦ hH.follows (runHint_follows hs e)⟩
  | alloc ptr size =>
    cases hstep
    refine ⟨trivial, fun e _ ↦ ?_⟩
    obtain ⟨f, hw⟩ := allocate_written hs e
    exact (hH.follows f).addW (by rw [f.fp]; exact hw)
  | allocDyn ptr size =>
    simp only [stepHint] at hstep
    split_ifs at hstep with hw
    cases hstep
    refine ⟨hH.written hw, fun e _ ↦ ?_⟩
    simp only [runHint, bind_ok] at e
    obtain ⟨sz, -, ⟨n, s1⟩, h1, e⟩ := e
    have f1 := (St.logOr_ok hs h1).1
    obtain ⟨f2, hw2⟩ := allocate_written f1.good e
    exact (hH.follows (f1.trans f2)).addW (show s'.mem.written (s'.fp + ptr) = true by
      rw [f2.fp]; exact hw2)
  | allocAdvice ptr stream =>
    cases hstep
    exact ⟨trivial, fun e _ ↦ hH.follows (runHint_follows hs e)⟩
  | allocArm ptr sel sizes =>
    simp only [stepHint] at hstep
    split_ifs at hstep with hw
    cases hstep
    refine ⟨hH.written hw, fun e _ ↦ ?_⟩
    simp only [runHint, bind_ok] at e
    obtain ⟨x, -, ⟨k, s1⟩, h1, e⟩ := e
    have f1 := (St.logOr_ok hs h1).1
    split at e
    · obtain ⟨f2, hw2⟩ := allocate_written f1.good e
      exact (hH.follows (f1.trans f2)).addW (show s'.mem.written (s'.fp + ptr) = true by
        rw [f2.fp]; exact hw2)
    · simp at e
  | allocFrames ptr size stop startInverse tail =>
    simp only [stepHint] at hstep
    split_ifs at hstep with hw
    cases hstep
    refine ⟨hH.written hw, fun e _ ↦ ?_⟩
    simp only [runHint, bind_ok] at e
    obtain ⟨sp, -, e⟩ := e
    split_ifs at e
    · simp [bind_ok] at e
    · rw [bind_ok] at e
      obtain ⟨⟨n, s1⟩, h1, e⟩ := e
      have f1 := (St.logOr_ok hs h1).1
      obtain ⟨f2, hw2⟩ := allocate_written f1.good e
      exact (hH.follows (f1.trans f2)).addW (show s'.mem.written (s'.fp + ptr) = true by
        rw [f2.fp]; exact hw2)
  | cellAddress ptr cell =>
    cases hstep
    refine ⟨trivial, fun e _ ↦ ?_⟩
    simp only [runHint, bind_ok] at e
    obtain ⟨c, hc, e⟩ := e
    obtain ⟨rfl, -⟩ := cellAt_ok hc
    obtain ⟨m, hm, rfl⟩ := St.withMem_ok e
    obtain ⟨hle, -, hget⟩ := Mem.put_ok hs.wf hm
    have hH' : Holds { s with mem := m } A := hH.mono (s' := { s with mem := m }) hle rfl
    exact ((hH'.addW (written_of_get hget)).addV (x := .m (.own cell)) ⟨_, hget, MonoVal.own (s := { s with mem := m }) cell⟩).addNz
      ⟨_, hget, ofK_gpow_ne_zero _⟩
  | witnessStack name base len =>
    cases hstep
    refine ⟨trivial, fun e hu ↦ ?_⟩
    simp only [runHint, bind_ok] at e
    obtain ⟨⟨v, s1⟩, h1, e⟩ := e
    obtain ⟨hl, f1, -⟩ := pop_len hs h1
    obtain ⟨m, hm, rfl⟩ := St.withMem_ok e
    obtain ⟨hle, hv⟩ := putRun_vals f1.good.wf hm
    have hH' := (hH.follows f1).mono (s' := { s1 with mem := m }) hle rfl
    subst hl
    refine writeRun_sound hH' (by rw [f1.fp]; exact hfp) hu (putRun_ok f1.good.wf hm).2
      (fun base' hb j hj ↦ ?_) (fun _ h ↦ by cases h)
    cases hb
    exact ⟨v[j], by rw [Nat.add_zero, ← Nat.add_assoc]; exact hv j hj, fun _ h ↦ by cases h⟩
  | witnessHeap name ptr lo len =>
    simp only [stepHint] at hstep
    obtain ⟨d, hd, rfl⟩ := Option.map_eq_some_iff.mp hstep
    obtain ⟨hw, m, hm, rfl⟩ := destOf_heap hd
    refine ⟨hH.written hw, fun e hu ↦ ?_⟩
    simp only [runHint, bind_ok] at e
    obtain ⟨⟨b, s1⟩, h1, ⟨v, s2⟩, h2, e⟩ := e
    obtain ⟨f1, hm1, p, hp, hpb, hbl⟩ := heapBase_val hs h1 (hH.written hw)
    obtain ⟨hl, f2, hm2⟩ := pop_len f1.good h2
    obtain ⟨hle, hfp3, hv⟩ := withMem_putRun f2.good e
    subst hl
    have hs2 : s2.mem = s.mem := hm2.trans hm1
    have hle' : s.mem ≤ s'.mem := hs2 ▸ hle
    have hfp' : s'.fp = s.fp := by rw [hfp3, f2.fp, f1.fp]
    obtain ⟨m', hm', rfl⟩ := St.withMem_ok e
    refine writeRun_sound (hH.mono hle' hfp') (by rw [hfp']; exact hfp) hu
      (putRun_ok f2.good.wf hm').2 (fun _ h ↦ by cases h) (fun m2 h ↦ ?_)
    cases h
    obtain ⟨u, hu1, hu2⟩ := hH.mono_val hm (hH.written hw)
    rw [hp] at hu1; cases hu1
    refine ⟨p, b, hu2.mono hle' hfp', hpb, fun j hj ↦ ?_⟩
    rw [← Nat.add_assoc]
    exact written_of_get (hv j hj)
  | log2Ceil bits dst nbits floor =>
    simp only [stepHint] at hstep
    split at hstep
    · rename_i base _ hd
      split_ifs at hstep with hall
      cases hstep
      have hbase : bits = .stack base := by
        cases bits with
        | stack b' => simp only [destOf, Option.some.injEq, Prod.mk.injEq] at hd; rw [hd.1]
        | heap ptr => obtain ⟨-, m, -, h⟩ := destOf_heap hd; cases h
      subst hbase
      refine ⟨fun j hj ↦ ?_, fun e _ ↦ ?_⟩
      · rw [Nat.add_assoc]; exact hH.written (List.all_eq_true.mp hall j (List.mem_range.mpr hj))
      · simp only [runHint, bind_ok] at e
        obtain ⟨⟨b, s1⟩, h1, e⟩ := e
        have f1 := bitsBase_follows hs h1
        obtain ⟨m, hm, rfl⟩ := St.withMem_ok e
        obtain ⟨hle, -, hget⟩ := Mem.put_ok f1.good.wf hm
        have hH' := (hH.follows f1).mono (s' := { s1 with mem := m }) hle rfl
        rw [f1.fp] at hget
        exact (hH'.addW (by rw [f1.fp]; exact written_of_get hget)).addNz
          ⟨_, by rw [f1.fp]; exact hget, ofK_gpow_ne_zero _⟩
    · rename_i m hd
      split_ifs at hstep with hall
      cases hstep
      cases bits with
      | stack b' => simp [destOf] at hd
      | heap ptr =>
      obtain ⟨hw, m', hm', hdm⟩ := destOf_heap hd
      cases hdm
      refine ⟨⟨hH.written hw, fun p x hp hx j hj hjx ↦ ?_⟩, fun e _ ↦ ?_⟩
      · obtain ⟨u, hu1, hu2⟩ := hH.mono_val hm' (hH.written hw)
        rw [hp] at hu1; cases hu1
        have hX : Names (p * ofK (g ^ j)) (x + j) := names_shift hx.1 hjx
        exact Abs.covered_sound hH hs.wf hu (List.all_eq_true.mp hall j (List.mem_range.mpr hj))
          (hu2.shift j) hX
      · simp only [runHint, bind_ok] at e
        obtain ⟨⟨b, s1⟩, h1, e⟩ := e
        have f1 := bitsBase_follows hs h1
        obtain ⟨m, hm, rfl⟩ := St.withMem_ok e
        obtain ⟨hle, -, hget⟩ := Mem.put_ok f1.good.wf hm
        have hH' := (hH.follows f1).mono (s' := { s1 with mem := m }) hle rfl
        rw [f1.fp] at hget
        exact (hH'.addW (by rw [f1.fp]; exact written_of_get hget)).addNz
          ⟨_, by rw [f1.fp]; exact hget, ofK_gpow_ne_zero _⟩
    · cases hstep
  | bitDecompose value bits nbits =>
    simp only [stepHint] at hstep
    by_cases hw : A.hasW value = true
    swap
    · rw [ite_eq_right hw] at hstep; cases hstep
    rw [ite_eq_left hw] at hstep
    obtain ⟨d, hd, rfl⟩ := Option.map_eq_some_iff.mp hstep
    have hdin : DestIn s bits := by
      cases bits with
      | stack => trivial
      | heap ptr => exact hH.written (destOf_heap hd).1
    refine ⟨⟨hH.written hw, hdin⟩, fun e hu' ↦ ?_⟩
    simp only [runHint, bind_ok] at e
    obtain ⟨⟨b, s1⟩, h1, e⟩ := e
    obtain ⟨f1, hm1, hb1, hb2⟩ := bitsBase_val hs h1 hdin
    obtain ⟨hle, hfp', hwf, hv⟩ := bits_run f1.good e
    have := runFrom_sound hH hfp hd hb1 hb2 (hm1 ▸ hle) (hfp'.trans f1.fp) hu' hwf hv
      (bb := none) (fun _ _ _ h ↦ by cases h)
    simpa using this
  | bitDecomposeExp value bits nbits =>
    simp only [stepHint] at hstep
    by_cases hw : A.hasW value = true
    swap
    · rw [ite_eq_right hw] at hstep; cases hstep
    rw [ite_eq_left hw] at hstep
    obtain ⟨d, hd, rfl⟩ := Option.map_eq_some_iff.mp hstep
    have hdin : DestIn s bits := by
      cases bits with
      | stack => trivial
      | heap ptr => exact hH.written (destOf_heap hd).1
    refine ⟨⟨hH.written hw, hdin⟩, fun e hu' ↦ ?_⟩
    simp only [runHint, bind_ok] at e
    obtain ⟨n, -, ⟨b, s1⟩, h1, e⟩ := e
    obtain ⟨f1, hm1, hb1, hb2⟩ := bitsBase_val hs h1 hdin
    obtain ⟨hle, hfp', hwf, hv⟩ := bits_run f1.good e
    have := runFrom_sound hH hfp hd hb1 hb2 (hm1 ▸ hle) (hfp'.trans f1.fp) hu' hwf hv
      (bb := none) (fun _ _ _ h ↦ by cases h)
    simpa using this
  | windowsExp value dest pos start width count =>
    simp only [stepHint] at hstep
    by_cases hw : A.hasW value = true
    swap
    · rw [ite_eq_right hw] at hstep; cases hstep
    rw [ite_eq_left hw] at hstep
    obtain ⟨d, hd, rfl⟩ := Option.map_eq_some_iff.mp hstep
    have hdin : DestIn s dest := by
      cases dest with
      | stack => trivial
      | heap ptr => exact hH.written (destOf_heap hd).1
    refine ⟨⟨hH.written hw, hdin⟩, fun e hu' ↦ ?_⟩
    simp only [runHint, bind_ok] at e
    obtain ⟨⟨b, s1⟩, h1, e⟩ := e
    obtain ⟨f1, hm1, hb1, hb2⟩ := bitsBase_val hs h1 hdin
    obtain ⟨hle, hfp', hwf, hv⟩ := bits_run f1.good e
    have := runFrom_sound hH hfp hd hb1 hb2 (pos := pos) (hm1 ▸ hle) (hfp'.trans f1.fp) hu' hwf
      (fun j hj ↦ by have := hv j hj; simpa using this) (bb := some width)
      (fun j hj c hc ↦ by
        cases hc
        simp only [List.getElem_map, List.getElem_range]
        exact ⟨_, Nat.mod_lt _ (Nat.two_pow_pos _), rfl⟩)
    simpa using this
  | digitDecomposeExp value dst nbits ndigits digitBits start startCell =>
    simp only [stepHint] at hstep
    split_ifs at hstep with hw
    simp only [Bool.and_eq_true] at hw
    obtain ⟨d, hd, rfl⟩ := Option.map_eq_some_iff.mp hstep
    have hdin : DestIn s dst := by
      cases dst with
      | stack => trivial
      | heap ptr => exact hH.written (destOf_heap hd).1
    refine ⟨⟨hH.written hw.1, fun c hc ↦ by subst hc; exact hH.written (by simpa using hw.2), hdin⟩,
      fun e hu' ↦ ?_⟩
    simp only [runHint, bind_ok] at e
    obtain ⟨n, -, e⟩ := e
    split at e
    · simp only [pure_bind, bind_ok] at e
      obtain ⟨⟨b, s1⟩, h1, e⟩ := e
      obtain ⟨f1, hm1, hb1, hb2⟩ := bitsBase_val hs h1 hdin
      obtain ⟨hle, hfp', hwf, hv⟩ := bits_run f1.good e
      have := runFrom_sound hH hfp hd hb1 hb2 (hm1 ▸ hle) (hfp'.trans f1.fp) hu' hwf hv
        (bb := some digitBits)
        (fun j hj c hc ↦ by
          cases hc
          simp only [List.getElem_map, List.getElem_range]
          refine ⟨_, ?_, rfl⟩
          split_ifs
          · exact Nat.two_pow_pos _
          · exact Nat.mod_lt _ (Nat.two_pow_pos _))
      simpa using this

    · simp only [bind_ok] at e
      obtain ⟨st, -, ⟨b, s1⟩, h1, e⟩ := e
      obtain ⟨f1, hm1, hb1, hb2⟩ := bitsBase_val hs h1 hdin
      obtain ⟨hle, hfp', hwf, hv⟩ := bits_run f1.good e
      have := runFrom_sound hH hfp hd hb1 hb2 (hm1 ▸ hle) (hfp'.trans f1.fp) hu' hwf hv
        (bb := some digitBits)
        (fun j hj c hc ↦ by
          cases hc
          simp only [List.getElem_map, List.getElem_range]
          refine ⟨_, ?_, rfl⟩
          split_ifs
          · exact Nat.two_pow_pos _
          · exact Nat.mod_lt _ (Nat.two_pow_pos _))
      simpa using this

  | fieldLimbs value base len =>
    simp only [stepHint] at hstep
    by_cases hw : A.hasW value = true
    swap
    · rw [ite_eq_right hw] at hstep; cases hstep
    rw [ite_eq_left hw] at hstep
    obtain rfl := Option.some.inj hstep
    refine ⟨hH.written hw, fun e hu' ↦ ?_⟩
    obtain ⟨hle, hfp', hwf, hv⟩ := bits_run hs e
    have := runFrom_sound (bits := .stack base) (d := (some base, none)) hH hfp rfl
      (fun _ h ↦ by cases h; rfl) (fun _ h ↦ by cases h) hle hfp' hu' hwf hv (bb := none)
      (fun _ _ _ h ↦ by cases h)
    simpa using this
  | inverse value dst =>
    simp only [stepHint] at hstep
    by_cases hw : A.hasW value = true
    swap
    · rw [ite_eq_right hw] at hstep; cases hstep
    rw [ite_eq_left hw] at hstep
    obtain rfl := Option.some.inj hstep
    refine ⟨hH.written hw, fun e _ ↦ ?_⟩
    simp only [runHint] at e
    obtain ⟨m, hm, rfl⟩ := St.withMem_ok e
    obtain ⟨hle, -, hget⟩ := Mem.put_ok hs.wf hm
    have hH' : Holds { s with mem := m } A := hH.mono (s' := { s with mem := m }) hle rfl
    have h1 := hH'.addW (o := dst) (written_of_get hget)
    by_cases hn : A.hasNz value = true
    · rw [ite_eq_left hn]
      refine h1.addNz ⟨_, hget, ?_⟩
      obtain ⟨u, hu, hne⟩ := hH.nzAt hn
      rw [Mem.peek_of_get hu]
      simp [hne]
    · rw [ite_eq_right hn]; exact h1

end

end LeanVM.Guest.Mode
