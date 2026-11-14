/-
  LeanVM.Guest.EndExecXTrace

  The tree track along a node's reference run, from `main`'s entry: a trace of track states at the
  run's registers, each frame an honest instance below `maxCells`, and a frame at a function's entry
  pc an instance of that function.
-/

module

public import LeanVM.Guest.Bridge.RefHonest
public import LeanVM.Guest.EndExec

/-!
# The tree track along the reference run

`RefTrack A r`: the tree track's invariant (`Bridge.RefOk`) on the reference run `r`, its honest tree
and memory, at the entries and alignment `A` gives. `traceRef`: for alignments of the program's
functions (`ProgAl`), `main` at its entry, where the top frame of every state of the track has its
jumps' cells (`JumpCells`), a trace of track states along `r`'s run from `main`'s entry, as
`Bridge.trace_deployed` gives on the trees it builds, here on `r`'s own. `inst_fp_lt`: an honest
instance's frame is below `maxCells`.

`entry_of_atPc`: a frame at pc `pc` of the track, with `pc` a guest function's entry, is an instance
of a function entered at `pc`, where each function's alignment is at its compiled function's entry
over at most its instructions (`AlLayout`), since the functions lie one after another
(`consecutive_entry`).
-/

namespace LeanVM.Guest.EndExec

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Memory LeanVM.Guest.Bridge
open LeanVM.Guest.End (mainEntry)
open LeanVM.Prover.Exec

@[expose] public section

/-- **The tree track against `r`'s run**, at the entries and alignment `A` gives. -/
abbrev RefTrack (A : String → FnAl) (r : Ref) : ℕ → ℕ → List Pop × List Ent → Prop :=
  Bridge.RefOk coreProgram r.rd0 (honestInsts coreProgram B2C.fs B2C.H r.hdr r.T) r.T (memOf r.img) (entOf A)
    (alOf A)

/-- **The trace along a node's reference run**, from `main`'s entry: a track state at the run's
registers after each of its `N` steps to the final registers but the last. -/
theorem traceRef {A : String → FnAl} (hP : ProgAl guestProgram coreProgram A)
    (hmain : entOf A "main" = mainEntry) {r : Ref} (hr : r.Ok)
    (hJ : ∀ pc fp done e st, RefTrack A r pc fp (done, e :: st) → JumpCells r.img A e) {N : ℕ}
    (hN : run guestProgram r.img N (regs mainEntry 0) = some (Registers.final guestProgram)) :
    ∃ tr : ℕ → ℕ × ℕ × (List Pop × List Ent), ∀ k < N,
      run guestProgram r.img k (regs mainEntry 0) = some (regs (tr k).1 (tr k).2.1) ∧
        RefTrack A r (tr k).1 (tr k).2.1 (tr k).2.2 := by
  obtain ⟨rd, hH, -⟩ := hr.honest
  obtain ⟨I, hI, hIt, hfp, -⟩ := root_inst (P := coreProgram) (fs := B2C.fs) (H := B2C.H) (hdr := r.hdr)
    (T := r.T)
  have hv := hH.valid
  rw [← hIt] at hv
  obtain ⟨fn, hf⟩ : ∃ fn, coreProgram.find? I.t.name = some fn := by
    rcases hIt' : I.t with ⟨f, σ, bufs, kids⟩ | ⟨f, σ⟩
    · rw [hIt'] at hv
      obtain ⟨fn, hf, -⟩ := hv
      exact ⟨fn, hf⟩
    · rw [hIt'] at hv; exact hv.elim
  have htr := trackOk_init (rd := r.rd0) hI hf hv
  rw [hIt] at htr
  have hname : I.t.name = "main" := by rw [hIt]; exact hr.name
  have hal0 : alOf A "main" 0 = some fn.body := by
    rw [hname] at hf
    change alignAt (A "main").X (A "main").body (A "main").code (A "main").d 0 = some fn.body
    rw [alignAt_zero (hP.ok _ _ hf), hP.body _ _ hf]
  have h0 := refOk_init (M := memOf r.img) (ent := entOf A) (al := alOf A) htr hfp (by rw [hname]; exact hal0)
  rw [hname, hmain] at h0
  obtain ⟨tr, -, htr', -⟩ := refTrace (stepRule_of hP honest_closed hJ) hN h0
  exact ⟨tr, htr'⟩

/-- **An honest instance's frame is below `maxCells`.** -/
theorem inst_fp_lt {r : Ref} (hr : r.Ok) {I : Inst} (hI : I ∈ honestInsts coreProgram B2C.fs B2C.H r.hdr r.T) :
    I.fp < maxCells := by
  obtain ⟨rd, hH, -⟩ := hr.honest
  have h2 := hH.cells.two_le I hI
  have hw := honest_within hI (by omega)
  have hle := le_two_pow_logMem (r.T.total B2C.fs)
  have h28 : 2 ^ logMem (r.T.total B2C.fs) ≤ 2 ^ 28 :=
    Nat.pow_le_pow_right (by norm_num) (logMemorySize_le_28 (e := r.exec) hr.size)
  unfold maxCells
  omega

/-! ## The functions' layout -/

theorem consecutive_bounds : ∀ {s e : ℕ} {fns : List CompiledFunction}, consecutive s fns e = true →
    ∀ f ∈ fns, s ≤ f.entryPc ∧ f.entryPc + f.instructionCount ≤ e
  | _, _, [], _, _, hf => absurd hf List.not_mem_nil
  | _, _, f0 :: gs, h, f, hf => by
    simp only [consecutive, Bool.and_eq_true, beq_iff_eq] at h
    obtain ⟨hg, hgs⟩ := h
    have := consecutive_le hgs
    rcases List.mem_cons.mp hf with rfl | hf
    · omega
    · have := consecutive_bounds hgs f hf
      omega

/-- **Consecutive functions**: an entry within a function's instructions is that function's
entry. -/
theorem consecutive_entry : ∀ {s e : ℕ} {fns : List CompiledFunction}, consecutive s fns e = true →
    ∀ f ∈ fns, ∀ f' ∈ fns, f.entryPc ≤ f'.entryPc → f'.entryPc < f.entryPc + f.instructionCount →
      f'.entryPc = f.entryPc
  | _, _, [], _, _, hf, _, _, _, _ => absurd hf List.not_mem_nil
  | _, _, f0 :: gs, h, f, hf, f', hf', h1, h2 => by
    simp only [consecutive, Bool.and_eq_true, beq_iff_eq] at h
    obtain ⟨hg, hgs⟩ := h
    rcases List.mem_cons.mp hf with rfl | hfs <;> rcases List.mem_cons.mp hf' with rfl | hfs'
    · rfl
    · have := (consecutive_bounds hgs f' hfs').1
      omega
    · have := (consecutive_bounds hgs f hfs).1
      omega
    · exact consecutive_entry hgs f hfs f' hfs' h1 h2

/-- **The alignments at the compiled functions**: each function's alignment is at its compiled
function's entry, over at most its instructions, the entry `B2C.entryOf` names. -/
def AlLayout (A : String → FnAl) : Prop :=
  ∀ f fn, coreProgram.find? f = some fn → ∃ cf ∈ Data.functions, entOf A f = cf.entryPc ∧
    B2C.entryOf f = cf.entryPc ∧ (A f).code.length ≤ cf.instructionCount

/-- **A frame at a function's entry is an instance of that function**: a frame of the track at pc
`pc`, where `pc` is a guest function's entry, is an instance of a function entered at `pc`. -/
theorem entry_of_atPc {A : String → FnAl} (hP : ProgAl guestProgram coreProgram A) (hL : AlLayout A)
    {Is : List Inst} {e : Ent} (hE : EntOk coreProgram Is e) {pc : ℕ} (hat : AtPc (entOf A) (alOf A) e pc) :
    pc < 2 ^ guestProgram.logSize - 1 ∧
      ∀ f' ∈ Data.functions, f'.entryPc = pc → B2C.entryOf e.I.t.name = pc := by
  obtain ⟨off, rfl, p, hal, -⟩ := hat
  obtain ⟨cf, hcf, hent, hentry, hlen⟩ := hL _ _ hE.find
  obtain ⟨ins, -, -, -, -, hins, -⟩ := alignAt_step (hP.ok _ _ hE.find) (show alignAt _ _ _ _ off = some p from hal)
  have hoff : off < cf.instructionCount :=
    lt_of_lt_of_le (List.getElem?_eq_some_iff.mp hins).1 hlen
  refine ⟨by rw [hent]; exact guest_pc_lt hcf hoff, fun f' hf' hpc ↦ ?_⟩
  rw [hent] at hpc
  have := consecutive_entry functions_consecutive cf hcf f' hf' (by omega) (by omega)
  rw [hentry, hent]
  omega

end

end LeanVM.Guest.EndExec
