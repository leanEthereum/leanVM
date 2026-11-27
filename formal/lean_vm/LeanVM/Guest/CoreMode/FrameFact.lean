module

public import LeanVM.Guest.CoreMode.FrameOp

/-!
# The frame walk's facts, one at a time

The frame walk's state (`FSt`) is a set of facts about a frame: cells written in the executor's
memory, and words of the reference image. A local certificate names them one by one: an
instruction reads some, each established by an earlier instruction on its path, and establishes
others. `FFact` is one fact, `FFact.Holds` what it says at an executor state (the clause of
`FVal` or `FWr` it is), `FSt.Has` that a state holds it.

* `FHolds.fact`: a fact a state has holds where the state does. So the facts an instruction's
  step establishes (in the state `stepF` returns) hold after it.
* `viewOf`: the state of a list of facts, and `FHolds.viewOf`: it holds where each fact does. So
  the frame walk's step (`stepF`, `offF`) and its soundness (`FrameOp`, `FrameSound`) apply to the
  few facts an instruction reads, wherever each holds.
-/

namespace LeanVM.Guest.CoreMode

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest
open LeanVM.Prover.Exec (Mem)
open LeanVM.Guest.Mode (Names)

@[expose] public section

/-- **A fact of a frame**, as the frame walk's state holds it. -/
inductive FFact where
  /-- Frame offset `o` written. -/
  | w (o : ℕ)
  /-- The cell `o` past frame cell `q`'s word written. -/
  | q (q o : ℕ)
  /-- Frame cell `o` nonzero in the reference. -/
  | nz (o : ℕ)
  /-- The cell `o` past frame cell `q`'s word holds that word. -/
  | s (q o : ℕ)
  /-- Frame cell `t` holds frame cell `c`'s word. -/
  | cp (t c : ℕ)
  /-- Frame cell `c` holds `1` plus frame cell `x`'s word. -/
  | one (c x : ℕ)
  /-- Frame cell `o` holds the word `v`. -/
  | env (o : ℕ) (v : Exec.Sym)
  /-- The cell `off` past frame cell `q`'s word holds `v`. -/
  | mem (q off : ℕ) (v : Exec.Sym)
  /-- The non-`JUMP` instruction `i` at pc `pc` holds in the reference. -/
  | ins (pc : ℕ) (i : OffsetInstruction)

section

variable {κ : ℕ} (img : MemoryImage κ)

/-- **What a fact says** at an executor state `s`, of the reference image `img` at frame `s.fp`
or of the executor's memory. -/
def FFact.Holds (s : Prover.Exec.St) : FFact → Prop
  | .w o => s.mem.written (s.fp + o) = true
  | .q a o => o < hqLim → ∃ p x, s.mem.get (s.fp + a) = some p ∧ Names (p * ofK (g ^ o)) x ∧
      s.mem.written x = true
  | .nz o => ∃ v, Rd img s.fp o = some v ∧ v ≠ 0
  | .s a o => o < hqLim → ∃ p, Rd img s.fp a = some p ∧ IsInK p ∧ img.read (p.limb 0 * addressOfIndex o) = some p
  | .cp t c => ∃ v, Rd img s.fp t = some v ∧ Rd img s.fp c = some v
  | .one c x => ∃ v, Rd img s.fp x = some v ∧ Rd img s.fp c = some (1 + v)
  | .env o v => img.read (g ^ s.fp * addressOfIndex o) = some (v.val (g ^ s.fp))
  | .mem a off v => ∃ p, img.read (g ^ s.fp * addressOfIndex a) = some p ∧ IsInK p ∧
      img.read (p.limb 0 * addressOfIndex off) = some (v.val (g ^ s.fp))
  | .ins pc i => Guest.Holds img pc (g ^ s.fp) i

end

/-- **The state has the fact.** -/
noncomputable def FSt.Has (A : FSt) : FFact → Prop
  | .w o => A.hasW o = true
  | .q a o => A.hasQ a o = true
  | .nz o => Bits.has A.nz o = true
  | .s a o => A.hasS a o = true
  | .cp t c => A.cp.get t = some c
  | .one c x => A.one.get c = some x
  | .env o v => A.st.env.get o = some v
  | .mem a off v => (a, off, v) ∈ A.st.mem
  | .ins pc i => (pc, i) ∈ A.st.prev

/-- **The state with the fact added.** -/
noncomputable def FSt.addFact (A : FSt) : FFact → FSt
  | .w o => A.addW o
  | .q a o => A.addQ a o
  | .nz o => A.addNz o
  | .s a o => A.addS a o
  | .cp t c => { A with cp := A.cp.set c Exec.envDepth t }
  | .one c x => { A with one := A.one.set x Exec.envDepth c }
  | .env o v => { A with st := { A.st with env := A.st.env.set v Exec.envDepth o } }
  | .mem a off v => { A with st := { A.st with mem := (a, off, v) :: A.st.mem } }
  | .ins pc i => { A with st := { A.st with prev := (pc, i) :: A.st.prev } }

/-- The state with nothing. -/
def FSt.empty : FSt := ⟨Exec.St.init .nil, 0, 0, .nil, .nil, .nil, .nil⟩

/-- **The state of a list of facts.** -/
noncomputable def viewOf (fs : List FFact) : FSt := fs.foldl FSt.addFact FSt.empty

section

variable {κ : ℕ} {img : MemoryImage κ} {s : Prover.Exec.St} {A : FSt}

private theorem hq_of {A : FSt} {q o : ℕ} (h : A.hasQ q o = true) : o < hqLim ∧ A.hq.get (hqKey q o) = some () := by
  simp only [FSt.hasQ, Bool.and_eq_true, decide_eq_true_eq] at h
  exact ⟨h.1, has_iff.mp h.2⟩

private theorem hs_of {A : FSt} {q o : ℕ} (h : A.hasS q o = true) : o < hqLim ∧ A.hs.get (hqKey q o) = some () := by
  simp only [FSt.hasS, Bool.and_eq_true, decide_eq_true_eq] at h
  exact ⟨h.1, has_iff.mp h.2⟩

/-- **A fact a state has holds** where the state does. -/
theorem FHolds.fact (h : FHolds img s A) : ∀ {f : FFact}, A.Has f → f.Holds img s
  | .w o, hf => h.2.w o hf
  | .q a o, hf => fun _ ↦ let ⟨hl, hg⟩ := hq_of hf; h.2.hq a o hl hg
  | .nz o, hf => h.1.nz o hf
  | .s a o, hf => fun _ ↦ let ⟨hl, hg⟩ := hs_of hf; h.1.hs a o hl hg
  | .cp t c, hf => h.1.cp t c hf
  | .one c x, hf => h.1.one c x hf
  | .env o v, hf => h.1.st.1 o v hf
  | .mem a off v, hf => h.1.st.2.1 a off v hf
  | .ins _ _, hf => h.1.st.2.2 _ hf

theorem FHolds.empty : FHolds img s FSt.empty := by
  refine ⟨⟨⟨fun n v hv ↦ by simp [FSt.empty, Exec.St.init] at hv, fun _ _ _ hm ↦ by
      simp [FSt.empty, Exec.St.init] at hm, fun _ hm ↦ by simp [FSt.empty, Exec.St.init] at hm⟩,
    fun o ho ↦ by simp [FSt.empty, Bits.has_zero] at ho, fun _ _ _ ho ↦ by simp [FSt.empty] at ho,
    fun _ _ ho ↦ by simp [FSt.empty] at ho, fun _ _ ho ↦ by simp [FSt.empty] at ho⟩,
    ⟨fun o ho ↦ by simp [FSt.empty, Bits.has_zero] at ho, fun _ _ _ ho ↦ by simp [FSt.empty] at ho⟩⟩

/-- **Adding a fact that holds keeps the state holding.** -/
theorem FHolds.addFact (h : FHolds img s A) : ∀ {f : FFact}, f.Holds img s → FHolds img s (A.addFact f)
  | .w o, hf => ⟨h.1.addW o, h.2.addW hf⟩
  | .q a o, hf => ⟨h.1.addQ a o, h.2.addQ hf⟩
  | .nz o, hf => ⟨h.1.addNz hf, h.2.addNz o⟩
  | .s a o, hf => ⟨h.1.addS hf, h.2.addS a o⟩
  | .cp t c, hf => ⟨h.1.setCp hf, ⟨h.2.w, h.2.hq⟩⟩
  | .one c x, hf => by
    refine ⟨⟨h.1.st, h.1.nz, h.1.hs, h.1.cp, fun c' x' hx ↦ ?_⟩, ⟨h.2.w, h.2.hq⟩⟩
    replace hx : (A.one.set x Exec.envDepth c).get c' = some x' := hx
    rcases Exec.Trie.get_set hx with ⟨rfl, rfl⟩ | hx
    · exact hf
    · exact h.1.one c' x' hx
  | .env o v, hf => by
    refine ⟨⟨⟨fun n v' hv ↦ ?_, h.1.st.2.1, h.1.st.2.2⟩, h.1.nz, h.1.hs, h.1.cp, h.1.one⟩, ⟨h.2.w, h.2.hq⟩⟩
    replace hv : (A.st.env.set v Exec.envDepth o).get n = some v' := hv
    rcases Exec.Trie.get_set hv with ⟨rfl, rfl⟩ | hv
    · exact hf
    · exact h.1.st.1 n v' hv
  | .mem a off v, hf => by
    refine ⟨⟨⟨h.1.st.1, fun q' off' v' hm ↦ ?_, h.1.st.2.2⟩, h.1.nz, h.1.hs, h.1.cp, h.1.one⟩, ⟨h.2.w, h.2.hq⟩⟩
    rcases List.mem_cons.mp hm with he | hm
    · simp only [Prod.mk.injEq] at he
      obtain ⟨rfl, rfl, rfl⟩ := he
      exact hf
    · exact h.1.st.2.1 q' off' v' hm
  | .ins pc i, hf => by
    refine ⟨⟨⟨h.1.st.1, h.1.st.2.1, fun x hm ↦ ?_⟩, h.1.nz, h.1.hs, h.1.cp, h.1.one⟩, ⟨h.2.w, h.2.hq⟩⟩
    rcases List.mem_cons.mp hm with rfl | hm
    · exact hf
    · exact h.1.st.2.2 x hm

theorem FHolds.foldl_addFact : ∀ {fs : List FFact} {A : FSt}, FHolds img s A → (∀ f ∈ fs, f.Holds img s) →
    FHolds img s (fs.foldl FSt.addFact A)
  | [], _, h, _ => h
  | f :: fs, A, h, hf => by
    rw [List.foldl_cons]
    exact FHolds.foldl_addFact (FHolds.addFact h (hf f List.mem_cons_self)) fun f' hm ↦
      hf f' (List.mem_cons_of_mem _ hm)

/-- **The state of facts that hold holds.** -/
theorem FHolds.viewOf {fs : List FFact} (hf : ∀ f ∈ fs, f.Holds img s) : FHolds img s (viewOf fs) :=
  FHolds.empty.foldl_addFact hf

end

end

end LeanVM.Guest.CoreMode
