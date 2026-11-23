module

public import LeanVM.Guest.CoreMode.Frame
public import LeanVM.Guest.Exec
public import LeanVM.Guest.Mode.SoundOp

/-!
# What the frame walk's state means

At an executor state `s` of frame `s.fp`, a path's state `A` holds (`FHolds img s A`) when its
value facts hold of the reference image `img` at the frame (`FVal`: `Exec`'s state, nonzero
words, self frame pointers, copies, `1 +` words; true at any time) and its written facts of the
executor's memory (`FWr`: frame offsets, cells past a frame cell's word; monotone in the memory,
`FWr.mono`). Each update of the state keeps it (`FWr.addW`, …), joins keep either side
(`FHolds.meet_left`, `meet_right`), and a back-solve's divisor the state accepts is nonzero
(`divOk_sound`).
-/

namespace LeanVM.Guest.CoreMode

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest
open LeanVM.Prover.Exec (Mem maxCells gpow_inj Mem.le_trans Mem.get_of_written)
open LeanVM.Guest.Mode (Names written_of_get written_mono names_inj)

@[expose] public section

/-! ## Tries of `Unit` -/

theorem has_iff {t : Exec.Trie Unit} {o : ℕ} : has t o = true ↔ t.get o = some () := by
  unfold has
  cases h : t.get o <;> simp

theorem get_set_unit {t : Exec.Trie Unit} {d n m : ℕ} (h : (t.set () d n).get m = some ()) :
    m = n ∨ t.get m = some () := by
  rcases Exec.Trie.get_set h with ⟨rfl, -⟩ | h
  · exact Or.inl rfl
  · exact Or.inr h

theorem get_inter_unit {a b : Exec.Trie Unit} {n : ℕ}
    (h : (Exec.Trie.inter (fun _ _ ↦ true) a b).get n = some ()) : a.get n = some () ∧ b.get n = some () :=
  Exec.Trie.get_inter (fun _ _ _ ↦ rfl) h

theorem get_inter_nat {a b : Exec.Trie ℕ} {n x : ℕ} (h : (Exec.Trie.inter Nat.beq a b).get n = some x) :
    a.get n = some x ∧ b.get n = some x :=
  Exec.Trie.get_inter (fun _ _ h ↦ Nat.eq_of_beq_eq_true h) h

theorem hqKey_inj {q o q' o' : ℕ} (ho : o < hqLim) (ho' : o' < hqLim) (h : hqKey q o = hqKey q' o') :
    q = q' ∧ o = o' := by
  unfold hqKey hqLim at *
  omega

/-! ## The meaning -/

section

variable {κ : ℕ} (img : MemoryImage κ)

/-- Frame cell `o`'s word in the reference image at frame `fp`. -/
noncomputable abbrev Rd (fp o : ℕ) : Option E := img.read (g ^ fp * addressOfIndex o)

/-- **The value facts** of a path, of the reference image at frame `fp`. -/
structure FVal (fp : ℕ) (A : FSt) : Prop where
  st : Exec.St.Holds img (g ^ fp) A.st
  nz : ∀ o, A.nz.get o = some () → ∃ v, Rd img fp o = some v ∧ v ≠ 0
  hs : ∀ q o, o < hqLim → A.hs.get (hqKey q o) = some () →
    ∃ p, Rd img fp q = some p ∧ IsInK p ∧ img.read (p.limb 0 * addressOfIndex o) = some p
  cp : ∀ t c, A.cp.get t = some c → ∃ v, Rd img fp t = some v ∧ Rd img fp c = some v
  one : ∀ c x, A.one.get c = some x → ∃ v, Rd img fp x = some v ∧ Rd img fp c = some (1 + v)

/-- **The written facts** of a path, of the executor's memory. -/
structure FWr (s : Prover.Exec.St) (A : FSt) : Prop where
  w : ∀ o, A.w.get o = some () → s.mem.written (s.fp + o) = true
  hq : ∀ q o, o < hqLim → A.hq.get (hqKey q o) = some () →
    ∃ p x, s.mem.get (s.fp + q) = some p ∧ Names (p * ofK (g ^ o)) x ∧ s.mem.written x = true

/-- **A path's state holds** at an executor state. -/
def FHolds (s : Prover.Exec.St) (A : FSt) : Prop := FVal img s.fp A ∧ FWr s A

end

/-! ## Monotone in the run -/

theorem FWr.mono {s s' : Prover.Exec.St} {A : FSt} (h : FWr s A) (hle : s.mem ≤ s'.mem)
    (hfp : s'.fp = s.fp) : FWr s' A where
  w o ho := by rw [hfp]; exact written_mono hle (h.w o ho)
  hq q o hl ho := by
    obtain ⟨p, x, h1, h2, h3⟩ := h.hq q o hl ho
    exact ⟨p, x, by rw [hfp]; exact hle.get _ _ h1, h2, written_mono hle h3⟩

theorem FHolds.mono {κ : ℕ} {img : MemoryImage κ} {s s' : Prover.Exec.St} {A : FSt}
    (h : FHolds img s A) (hle : s.mem ≤ s'.mem) (hfp : s'.fp = s.fp) : FHolds img s' A :=
  ⟨hfp ▸ h.1, h.2.mono hle hfp⟩

/-! ## Updates -/

theorem stHolds_init {κ : ℕ} {img : MemoryImage κ} {fp : K} {env : Exec.Trie Exec.Sym}
    (h : Exec.EnvHolds img fp env) : Exec.St.Holds img fp (Exec.St.init env) :=
  ⟨h, fun _ _ _ hm ↦ by simp [Exec.St.init] at hm, fun _ hm ↦ by simp [Exec.St.init] at hm⟩

section Updates

variable {κ : ℕ} {img : MemoryImage κ} {fp : ℕ} {s : Prover.Exec.St} {A : FSt}

theorem FWr.addW (h : FWr s A) {o : ℕ} (hw : s.mem.written (s.fp + o) = true) : FWr s (A.addW o) where
  w o' ho' := by
    rcases get_set_unit (t := A.w) (d := Exec.envDepth) (n := o) ho' with rfl | ho'
    · exact hw
    · exact h.w o' ho'
  hq := h.hq

theorem FWr.addQ (h : FWr s A) {q o : ℕ}
    (hw : o < hqLim → ∃ p x, s.mem.get (s.fp + q) = some p ∧ Names (p * ofK (g ^ o)) x ∧
      s.mem.written x = true) : FWr s (A.addQ q o) := by
  unfold FSt.addQ
  split_ifs with hl
  · refine ⟨h.w, fun q' o' hl' ho' ↦ ?_⟩
    rcases get_set_unit (t := A.hq) (d := hqDepth) (n := hqKey q o) ho' with he | ho'
    · obtain ⟨rfl, rfl⟩ := hqKey_inj hl' hl he
      exact hw hl
    · exact h.hq q' o' hl' ho'
  · exact h

theorem FWr.addNz (h : FWr s A) (o : ℕ) : FWr s (A.addNz o) := ⟨h.w, h.hq⟩

theorem FWr.addS (h : FWr s A) (q o : ℕ) : FWr s (A.addS q o) := by
  unfold FSt.addS
  split_ifs
  · exact ⟨h.w, h.hq⟩
  · exact h

theorem FVal.addW (h : FVal img fp A) (o : ℕ) : FVal img fp (A.addW o) :=
  ⟨h.st, h.nz, h.hs, h.cp, h.one⟩

theorem FVal.addQ (h : FVal img fp A) (q o : ℕ) : FVal img fp (A.addQ q o) := by
  unfold FSt.addQ
  split_ifs
  · exact ⟨h.st, h.nz, h.hs, h.cp, h.one⟩
  · exact h

theorem FVal.addNz (h : FVal img fp A) {o : ℕ} (hn : ∃ v, Rd img fp o = some v ∧ v ≠ 0) :
    FVal img fp (A.addNz o) where
  st := h.st
  nz o' ho' := by
    rcases get_set_unit (t := A.nz) (d := Exec.envDepth) (n := o) ho' with rfl | ho'
    · exact hn
    · exact h.nz o' ho'
  hs := h.hs
  cp := h.cp
  one := h.one

theorem FVal.addS (h : FVal img fp A) {q o : ℕ}
    (hs : o < hqLim → ∃ p, Rd img fp q = some p ∧ IsInK p ∧ img.read (p.limb 0 * addressOfIndex o) = some p) :
    FVal img fp (A.addS q o) := by
  unfold FSt.addS
  split_ifs with hl
  · refine ⟨h.st, h.nz, fun q' o' hl' ho' ↦ ?_, h.cp, h.one⟩
    rcases get_set_unit (t := A.hs) (d := hqDepth) (n := hqKey q o) ho' with he | ho'
    · obtain ⟨rfl, rfl⟩ := hqKey_inj hl' hl he
      exact hs hl
    · exact h.hs q' o' hl' ho'
  · exact h

theorem FVal.reset (h : FVal img fp A) : FVal img fp A.reset :=
  ⟨stHolds_init h.st.1, h.nz, h.hs, h.cp, h.one⟩

theorem FWr.reset (h : FWr s A) : FWr s A.reset := ⟨h.w, h.hq⟩

theorem FHolds.reset (h : FHolds img s A) : FHolds img s A.reset := ⟨h.1.reset, h.2.reset⟩

end Updates

/-! ## Joins -/

section Meet

variable {κ : ℕ} {img : MemoryImage κ} {s : Prover.Exec.St} {A B : FSt}

theorem envHolds_inter_left {fp : K} {a b : Exec.Trie Exec.Sym} (h : Exec.EnvHolds img fp a) :
    Exec.EnvHolds img fp (Exec.Trie.inter Exec.Sym.beq a b) := fun n v hv ↦
  h n v (Exec.Trie.get_inter (fun _ _ ↦ Exec.Sym.beq_eq) hv).1

theorem envHolds_inter_right {fp : K} {a b : Exec.Trie Exec.Sym} (h : Exec.EnvHolds img fp b) :
    Exec.EnvHolds img fp (Exec.Trie.inter Exec.Sym.beq a b) := fun n v hv ↦
  h n v (Exec.Trie.get_inter (fun _ _ ↦ Exec.Sym.beq_eq) hv).2

theorem FHolds.meet_left (h : FHolds img s A) : FHolds img s (A.meet B) := by
  obtain ⟨hv, hw⟩ := h
  refine ⟨⟨stHolds_init (envHolds_inter_left hv.st.1), fun o ho ↦ hv.nz o (get_inter_unit ho).1,
    fun q o hl ho ↦ hv.hs q o hl (get_inter_unit ho).1, fun t c ho ↦ hv.cp t c (get_inter_nat ho).1,
    fun c x ho ↦ hv.one c x (get_inter_nat ho).1⟩,
    ⟨fun o ho ↦ hw.w o (get_inter_unit ho).1, fun q o hl ho ↦ hw.hq q o hl (get_inter_unit ho).1⟩⟩

theorem FHolds.meet_right (h : FHolds img s B) : FHolds img s (A.meet B) := by
  obtain ⟨hv, hw⟩ := h
  refine ⟨⟨stHolds_init (envHolds_inter_right hv.st.1), fun o ho ↦ hv.nz o (get_inter_unit ho).2,
    fun q o hl ho ↦ hv.hs q o hl (get_inter_unit ho).2, fun t c ho ↦ hv.cp t c (get_inter_nat ho).2,
    fun c x ho ↦ hv.one c x (get_inter_nat ho).2⟩,
    ⟨fun o ho ↦ hw.w o (get_inter_unit ho).2, fun q o hl ho ↦ hw.hq q o hl (get_inter_unit ho).2⟩⟩

theorem get_of_sub_unit {a b : Exec.Trie Unit} (h : a.sub (fun _ _ ↦ true) b = true) {n : ℕ}
    (ha : a.get n = some ()) : b.get n = some () :=
  Exec.Trie.get_of_sub (fun _ _ _ ↦ rfl) h ha

theorem get_of_sub_nat {a b : Exec.Trie ℕ} (h : a.sub Nat.beq b = true) {n x : ℕ}
    (ha : a.get n = some x) : b.get n = some x :=
  Exec.Trie.get_of_sub (fun _ _ h ↦ Nat.eq_of_beq_eq_true h) h ha

/-- **A weaker state holds** where a stronger one does (a cut). -/
theorem FHolds.sub (h : FHolds img s A) (hs : B.sub A = true) : FHolds img s B.reset := by
  obtain ⟨hv, hw⟩ := h
  simp only [FSt.sub, Bool.and_eq_true] at hs
  obtain ⟨⟨⟨⟨⟨⟨he, h1⟩, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩ := hs
  refine ⟨⟨stHolds_init (Exec.EnvHolds.sub he hv.st.1), fun o ho ↦ hv.nz o (get_of_sub_unit h2 ho),
    fun q o hl ho ↦ hv.hs q o hl (get_of_sub_unit h4 ho), fun t c ho ↦ hv.cp t c (get_of_sub_nat h5 ho),
    fun c x ho ↦ hv.one c x (get_of_sub_nat h6 ho)⟩,
    ⟨fun o ho ↦ hw.w o (get_of_sub_unit h1 ho), fun q o hl ho ↦ hw.hq q o hl (get_of_sub_unit h3 ho)⟩⟩

end Meet

end

end LeanVM.Guest.CoreMode
