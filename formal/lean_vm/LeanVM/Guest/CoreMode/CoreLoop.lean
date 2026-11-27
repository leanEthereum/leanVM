/-
  LeanVM.Guest.CoreMode.CoreLoop

  Facts a loop helper's frame interface uses: memories agreeing with the reference, the entry
  abstraction, the next frame's header.
-/

module

public import LeanVM.Guest.CoreMode.CoreSound
public import LeanVM.Guest.CoreMode.LoopSig

/-!
# A loop helper's frame facts

What `frameSpec_loopC` (`CoreLoopC.lean`) uses beyond the function route's: a memory agreeing with the
reference reads the reference (`rdE_of_get`, `parAt_of`); the entry abstraction's facts (`entry_facts`);
the next frame's header (`hdr_copy`).
-/

namespace LeanVM.Guest.CoreMode

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Memory
open LeanVM.Guest.Bridge (AlignCtx Zip ZOk fwdJ flowAtom isaFlowHint stmtsOf stmtsSub zok_stmts Pairs
  walk_ret_cons walk_callIf_cons)
open LeanVM.Guest.Check (getF)
open LeanVM.Prover.Exec (Hint St Ctx Fine Moves StepOk HintOk refMem maxCells runOp Mem gpow_inj
  Mem.get_of_written OpModed OnRef Agree)
open LeanVM.Guest.Mode (Names written_of_get written_mono names_inj opOfOff RefOk HintIn Holds entryAbs
  FrameSpec Out HintsAt ResAt RetAll RetHolds HW RW MonoVal BsVal BaseVal IdxVal stOf CodeOk TermAt LTF Back
  TermEntry)

@[expose] public section

variable {κ : ℕ}

/-! ## Facts about memories agreeing with the reference -/

theorem refMem_eq_of_rd {img : MemoryImage κ} (hκ : κ ≤ 28) {a b : ℕ} (ha : a < 2 ^ 62) (hb : b < 2 ^ 62)
    (h : img.read (g ^ a) = img.read (g ^ b)) : refMem img a = refMem img b := by
  have hz : ∀ c, c < 2 ^ 62 → img.read (g ^ c) = none → refMem img c = 0 := fun c hc hn ↦ by
    unfold refMem
    split_ifs with hlt
    · exfalso
      have := (MemoryImage.read_eq_none_iff img).mp hn ⟨c, hlt⟩
      exact this rfl
    · rfl
  rcases hra : img.read (g ^ a) with _ | v
  · rw [hra] at h
    rw [hz a ha hra, hz b hb h.symm]
  · rw [hra] at h
    rw [(Prover.Exec.refRd_img hκ img a v ha hra).2, (Prover.Exec.refRd_img hκ img b v hb h.symm).2]

/-- **A frame agreeing with the reference, its entry cells written**, holds at its parameter cells the
words the reference does. -/
theorem parAt_of {img : MemoryImage κ} (hκ : κ ≤ 28) {G : Mode.Sig} {np : ℕ} {m : Mem} (ha : Agree m (refMem img))
    {fp : ℕ} (hfp : fp < maxCells) (hw : ∀ o ∈ G.entry, m.written (fp + o) = true) {ws : List E}
    (hws : ∀ b < np, Rd img fp (2 + b) = some (slotW ws b)) : ParAt G np (stOf m fp) ws := by
  intro o ho
  obtain ⟨h2, hn, h28, hent⟩ := parCell_spec ho
  obtain ⟨u, hu⟩ := Mem.get_of_written (hw o hent)
  show m.get (fp + o) = _
  rw [hu, rd_getA hκ ha hfp h28 (by have := hws (o - 2) hn; rwa [show 2 + (o - 2) = o by omega] at this) hu]

/-! ## The entry abstraction -/

theorem monoVal_own0 {s : St} {u : E} (h : MonoVal s (Mode.Mono.own 0) u) : u = ofK (g ^ s.fp) := by
  obtain ⟨w, hw, rfl⟩ := h
  simp only [Mode.Mono.own, BsVal] at hw
  simp [hw, Mode.Mono.own]

/-- **What the entry abstraction holds**: the entry cells written, the preconditions, the self cell
holding its frame's address. -/
theorem entry_facts {E0 : Mode.Env} {G : Mode.Sig} (hent : ∀ o ∈ G.entry, o + 1 < 2 ^ Exec.envDepth)
    (hso : ∀ o, G.self = some o → o + 1 < 2 ^ Exec.envDepth) {s : St} (h : Mode.Holds s (entryAbs E0 G)) :
    (∀ o ∈ G.entry, s.mem.written (s.fp + o) = true) ∧ (∀ m ∈ G.pre, HW s m) ∧ (∀ r ∈ G.preR, RW s r) ∧
      ∀ o, G.self = some o → s.mem.written (s.fp + o) = true ∧ s.mem.get (s.fp + o) = some (ofK (g ^ s.fp)) := by
  unfold entryAbs at h
  rcases hs : G.self with _ | o
  · rw [hs] at h
    exact ⟨fun o ho ↦ h.w o (foldlT_mem _ _ hent ho), h.h, fun r hr ↦ h.r r (List.mem_cons_of_mem _ hr),
      fun o ho ↦ by cases ho⟩
  · rw [hs] at h
    have ho1 := hso o hs
    simp only [Mode.Abs.addW, Mode.Abs.addV, Mode.Abs.addNz] at h
    rw [trieNil_get rfl] at h
    simp only at h
    refine ⟨fun o' ho' ↦ h.w o' ?_, h.h, fun r hr ↦ h.r r (List.mem_cons_of_mem _ hr), fun o' ho' ↦ ?_⟩
    · show (Exec.Trie.set () Exec.envDepth (Mode.foldlT .nil G.entry) o).get o' = some ()
      rw [Check.get_set_eq () _ _ o o' ho1]
      split_ifs
      · rfl
      · exact foldlT_mem _ _ hent ho'
    · cases ho'
      refine ⟨h.w o ?_, ?_⟩
      · show (Exec.Trie.set () Exec.envDepth (Mode.foldlT .nil G.entry) o).get o = some ()
        rw [Check.get_set_eq () _ _ o o ho1]
        simp
      · obtain ⟨u, hu, hv⟩ := h.v o (.m (Mode.Mono.own 0)) (by
          show (Exec.Trie.set (Mode.Val.m (Mode.Mono.own 0)) Exec.envDepth .nil o).get o = _
          rw [Check.get_set_eq _ _ _ o o ho1]
          simp)
        rw [hu, monoVal_own0 hv]

/-! ## The next frame's header -/

/-- **Two cells the reference reads alike**, both written in a memory agreeing with it, hold one
word. -/
theorem hdr_copy {img : MemoryImage κ} (hκ : κ ≤ 28) {m : Mem} (ha : Agree m (refMem img)) {a b o : ℕ}
    (hab : Rd img b o = Rd img a o) (hwa : m.written (a + o) = true) (hwb : m.written (b + o) = true)
    (hla : a + o < 2 ^ 62) (hlb : b + o < 2 ^ 62) : ∃ u, m.get (a + o) = some u ∧ m.get (b + o) = some u := by
  obtain ⟨u, hu⟩ := Mem.get_of_written hwa
  obtain ⟨u', hu'⟩ := Mem.get_of_written hwb
  refine ⟨u, hu, ?_⟩
  rw [hu', ← ha.get _ _ hu', ← ha.get _ _ hu]
  exact congrArg some (refMem_eq_of_rd hκ hlb hla (by simpa [Rd, addressOfIndex, pow_add] using hab))

end

end LeanVM.Guest.CoreMode
