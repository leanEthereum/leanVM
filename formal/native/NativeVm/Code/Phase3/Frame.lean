module

public import NativeVm.Code.Phase3.EOps

/-!
# Carrying values through phase 3's parts

A run that keeps the words outside the transcript's and the regions it writes keeps any element
or array at words apart from those regions (`Step3.ewat`, `Step3.ewarr`, `Step3.word`). A
straight-line program over slots inside one region `r` writes only `r` (`ops_wrote`); its inputs
come from a list of slots and values (`vOf`, `holds_vOf`).
-/

@[expose] public section

namespace NativeVm.Code.P3

open Native NativeVm.Model NativeVm.Code NativeVm.Transcript LeanVM.Parameters

variable {env : Env} {inp : Input} {t : TState} {s s' : QState}

/-- Words `a .. b` of the working area are apart from the regions `ws`. -/
def Clear (ws : List Region) (a b : Nat) : Prop :=
  Transcript.workWords ≤ a ∧ b ≤ dataEnd ∧ ∀ r ∈ ws, b ≤ r.off ∨ r.stop ≤ a

instance (ws : List Region) (a b : Nat) : Decidable (Clear ws a b) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _))

theorem Step3.word {regs : List Reg64} {ws : List Region} (hs : Step3 env regs ws s s')
    (hi : Inputs env inp s.mem) (hws : ∀ r ∈ ws, Ok3 r) {a b k : Nat} (hc : Clear ws a b)
    (hk : a ≤ k) (hk' : k < b) : s'.mem (wd env.work k) = s.mem (wd env.work k) := by
  have hdl := dataEnd_le inp.bytecode.size
  have hww := workWords_lt hi
  obtain ⟨h1, h2, h3⟩ := hc
  refine hs.mem _ (hi.not_foot_work (by omega) (by omega)) fun r hr ⟨j, hj, e⟩ ↦ ?_
  have hb := (hws r hr).bounds
  have := h3 r hr
  unfold Region.stop at hb this
  rw [wd_inj (by omega) (by omega)] at e
  omega

theorem Step3.ewat {regs : List Reg64} {ws : List Region} (hs : Step3 env regs ws s s')
    (hi : Inputs env inp s.mem) (hws : ∀ r ∈ ws, Ok3 r) {k : Nat} (hc : Clear ws k (k + 2))
    {x : EW} (h : EWAt s.mem (wd env.work k) x) : EWAt s'.mem (wd env.work k) x := by
  refine ⟨(hs.word hi hws hc le_rfl (by omega)).trans h.1, ?_⟩
  rw [wd_wd, hs.word hi hws hc (by omega) (by omega), ← wd_wd]
  exact h.2

theorem Step3.ewarr {regs : List Reg64} {ws : List Region} (hs : Step3 env regs ws s s')
    (hi : Inputs env inp s.mem) (hws : ∀ r ∈ ws, Ok3 r) {k n : Nat} {xs : Array EW}
    (hc : Clear ws k (k + n)) (hn : 2 * xs.size ≤ n) (h : EWArr s.mem (wd env.work k) xs) :
    EWArr s'.mem (wd env.work k) xs := fun i hi' ↦ by
  rw [wd_wd]
  have hc' : Clear ws (k + 2 * i) (k + 2 * i + 2) :=
    ⟨by have := hc.1; omega, by have := hc.2.1; omega,
      fun r hr ↦ by rcases hc.2.2 r hr with h | h <;> [left; right] <;> omega⟩
  have := h i hi'
  rw [wd_wd] at this
  exact hs.ewat hi hws hc' this

theorem Step3.natAt {regs : List Reg64} {ws : List Region} (hs : Step3 env regs ws s s')
    (hi : Inputs env inp s.mem) (hws : ∀ r ∈ ws, Ok3 r) {k n : Nat} (hc : Clear ws k (k + 1))
    (h : NatAt s.mem (wd env.work k) n) : NatAt s'.mem (wd env.work k) n :=
  h.congr (hs.word hi hws hc le_rfl (by omega))

/-- A store into a region, from a state with the start's memory. -/
theorem wrote_store {ws : List Region} {r : Region} {s1 : QState} (hr : r ∈ ws) {k : Nat}
    (hk1 : r.off ≤ k) (hk2 : k < r.stop) (hm : s1.mem = s.mem) (hrdi : s1.reg .rdi = s.reg .rdi)
    (hs : (s.mem (wd env.work k)).isSome) (v : UInt64) :
    Wrote env ws s (s1.setMem (wd env.work k) v) := by
  refine ⟨by rw [QState.setMem_reg, hrdi], fun a ha ↦ ?_, fun a ↦ ?_⟩
  · have hne : a ≠ wd env.work k := by
      rintro rfl
      exact ha r hr ⟨k - r.off, by unfold Region.stop at hk2; omega, by congr 1; omega⟩
    rw [QState.setMem_mem, ite_eq_right_of_eq_false _ _ (eq_false hne), hm]
  · rw [QState.setMem_mem]
    split
    · subst a; exact hs.symm
    · rw [hm]

theorem not_in_of {r : Region} {k : Nat} (h : k < r.off ∨ r.stop ≤ k) (hk : k < 2 ^ 61)
    (hr : r.stop ≤ 2 ^ 61) : ¬ r.In env.work (wd env.work k) := by
  rintro ⟨j, hj, e⟩
  unfold Region.stop at h hr
  rw [wd_inj (by omega) (by omega)] at e
  omega

/-- A word apart from the regions a run writes survives it. -/
theorem Wrote.word {ws : List Region} (hw : Wrote env ws s s') {k : Nat}
    (hk : ∀ r ∈ ws, k < r.off ∨ r.stop ≤ k) (hk' : k < 2 ^ 61) (hws : ∀ r ∈ ws, r.stop ≤ 2 ^ 61) :
    s'.mem (wd env.work k) = s.mem (wd env.work k) :=
  hw.mem _ fun r hr ↦ not_in_of (hk r hr) hk' (hws r hr)

/-- A run writing regions inside others writes those. -/
theorem Wrote.widen {ws ws' : List Region} (hw : Wrote env ws s s')
    (h : ∀ r ∈ ws, ∃ q ∈ ws', Within r q) : Wrote env ws' s s' :=
  ⟨hw.rdi, fun a ha ↦ hw.mem a fun r hr hin ↦ by
    obtain ⟨q, hq, hrq⟩ := h r hr
    exact ha q hq (in_within hin hrq), hw.dom⟩

theorem Step3.widen {regs : List Reg64} {ws ws' : List Region} (hw : Step3 env regs ws s s')
    (h : ∀ r ∈ ws, ∃ q ∈ ws', Within r q) : Step3 env regs ws' s s' :=
  ⟨hw.rdi, hw.regs, fun a hf ha ↦ hw.mem a hf fun r hr hin ↦ by
    obtain ⟨q, hq, hrq⟩ := h r hr
    exact ha q hq (in_within hin hrq), hw.dom⟩

/-! ## Values of slots -/

/-- The value of slot `k` in a list of slots and values (the first entry), `0` if absent. -/
def vOf (l : List (Nat × EW)) (k : Nat) : EW := ((l.find? (·.1 == k)).map (·.2)).getD 0

theorem vOf_cons (k : Nat) (x : EW) (l : List (Nat × EW)) (j : Nat) :
    vOf ((k, x) :: l) j = if j = k then x else vOf l j := by
  unfold vOf
  rw [List.find?_cons]
  by_cases h : j = k
  · subst h; simp
  · have : (k == j) = false := by simp [Ne.symm h]
    simp [this, h]

/-- The slots of `l` hold their values when each entry's does and the keys are distinct. -/
theorem holds_vOf {m : UInt64 → Option UInt64} {w : UInt64} :
    ∀ (l : List (Nat × EW)), (l.map (·.1)).Nodup → (∀ p ∈ l, EWAt m (wd w p.1) p.2) →
      Holds m w (l.map (·.1)) (vOf l)
  | [], _, _ => fun _ h ↦ by simp at h
  | (k, x) :: l, hd, h => by
    intro j hj
    rw [vOf_cons]
    simp only [List.map_cons, List.mem_cons] at hj
    by_cases e : j = k
    · subst e; simp only [↓reduceIte]; exact h _ (List.mem_cons_self ..)
    · simp only [e, ↓reduceIte]
      rcases hj with rfl | hj
      · exact absurd rfl e
      · simp only [List.map_cons, List.nodup_cons] at hd
        exact holds_vOf l hd.2 (fun p hp ↦ h p (List.mem_cons_of_mem _ hp)) j hj

/-- **A straight-line program** writing slots of the region `r` only. -/
theorem ops_wrote (l : List EOp) {S : List Nat} {v : Nat → EW} {r : Region} {E : QState → Prop}
    (hr : Ok3 r) (hi : Inputs env inp s.mem) (h14 : s.reg .r14 = env.work)
    (hS : Holds s.mem env.work S v) (hSe : ∀ k ∈ S, k % 2 = 0 ∧ k + 1 < 2 ^ 60)
    (hval : opsValid l S = true) (hde : ∀ d ∈ opsDsts l, d % 2 = 0 ∧ r.off ≤ d ∧ d + 2 ≤ r.stop) :
    WP (opsCode l) s (fun s' ↦ Holds s'.mem env.work (opsDsts l ++ S) (opsRun l v) ∧
      Wrote env [r] s s' ∧ RegsFrame opRegs s s') E := by
  have hb := hr.bounds
  have hdl := dataEnd_le inp.bytecode.size
  have hww := workWords_lt hi
  unfold Region.stop at hb hde
  rw [dataEnd_val] at hb
  refine WP.mono (ops_spec l (lim := 2 ^ 60) (by norm_num) h14 hS hSe hval
    (fun d hd ↦ ⟨(hde d hd).1, by have := hde d hd; omega⟩)
    (fun d hd ↦ ⟨hi.ok3_some' hr (by have := hde d hd; unfold Region.stop; omega),
      hi.ok3_some' hr (by have := hde d hd; unfold Region.stop; omega)⟩)) ?_ fun _ h ↦ h
  rintro s' ⟨hH, hk, hsome, hout, hf⟩
  refine ⟨hH, ⟨hf .rdi (by decide), fun a ha ↦ ?_, hsome⟩, hf⟩
  by_cases hw : ∃ k < 2 ^ 60, a = wd env.work k
  · obtain ⟨k, hk', rfl⟩ := hw
    refine hk k hk' fun d hd ↦ ?_
    have hd' := hde d hd
    constructor
    · intro e
      exact ha r (by simp) ⟨k - r.off, by omega, by congr 1; omega⟩
    · intro e
      exact ha r (by simp) ⟨k - r.off, by omega, by congr 1; omega⟩
  · exact hout a fun k hk' e ↦ hw ⟨k, hk', e⟩

end NativeVm.Code.P3
