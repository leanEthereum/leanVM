/-
  LeanVM.Guest.EndExecACurHyps

  `CurHyps` from one check per function: `Bridge.allocFnChk` over each function's alignment.
-/

module

public import LeanVM.Guest.EndExecACur
public import LeanVM.Guest.Bridge.CurChk

/-!
# The guest's cursor facts from the check

`curHyps_of : ProgAl … A → (∀ f fn, coreProgram.find? f = some fn → allocFnChk (A f).X fn (A f).code (A f).d
= true) → CurHyps L D A`: `facts` by `Bridge.curFactsX_of`, `loopNext` by `Bridge.loop_of_nextOk`,
`notLast` by `Bridge.loopX_notLast`, and `bufsLe`: every honest instance's `HeapBuf`s are its path's
(`HonestAtA.bufsOk`, kept by every instance, `instsA_bufsOk`), at most the body's allocation atoms
(`Bridge.allocDsts_le_cnt`), at most the function's buffer hints (the check's `cntL`).
-/

namespace LeanVM.Guest.EndExec

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Memory
open LeanVM.Guest.Core hiding Hint
open LeanVM.Guest.Bridge hiding St
open LeanVM.Prover.Exec

public section

/-! ## The instances' buffers -/

section Bufs

variable {P : Core.Program} {fs : String → ℕ} {lp : String → Bool} {al : String → Bool} {H : Inst → ℕ → E × E}

mutual
/-- **Every instance of a tree whose buffers are its paths' has its path's buffers.** -/
theorem instsA_bufsOk : ∀ (t : Tree) (p : ℕ × ℕ) (hdr : E × E), t.BufsOk P →
    ∀ I ∈ t.instsA fs lp al H p hdr, I.t.BufsOk P
  | .node f σ bufs kids, p, hdr, hb, I, hI => by
    rw [instsA_node, List.mem_cons] at hI
    rcases hI with rfl | hI
    · exact hb
    · exact instsKidsA_bufsOk kids _ 0 _ hb.2 I hI
  | .phantom f σ, p, hdr, _, I, hI => by
    rw [instsA_phantom, List.mem_singleton] at hI
    subst hI
    trivial

/-- `instsA_bufsOk` for the callees. -/
theorem instsKidsA_bufsOk : ∀ (ks : List Tree) (I : Inst) (j : ℕ) (ps : List (ℕ × ℕ)), Tree.BufsOkKids P ks →
    ∀ J ∈ Tree.instsKidsA fs lp al H I j ps ks, J.t.BufsOk P
  | [], _, _, _, _, J, hJ => by rw [instsKidsA_nil] at hJ; exact (List.not_mem_nil hJ).elim
  | _ :: _, _, _, [], _, J, hJ => by rw [instsKidsA_nil_left] at hJ; exact (List.not_mem_nil hJ).elim
  | k :: ks, I, j, p :: ps, hb, J, hJ => by
    rw [instsKidsA_cons, List.mem_append] at hJ
    rcases hJ with hJ | hJ
    · exact instsA_bufsOk k p _ hb.1 J hJ
    · exact instsKidsA_bufsOk ks I (j + 1) ps hb.2 J hJ
end

end Bufs

theorem alloc?_isSome (σ : Val) (e : Ev) : (Ev.alloc? σ e).isSome = (Ev.allocDst? e).isSome := by
  unfold Ev.alloc? Ev.allocDst?
  split <;> split <;> simp_all

theorem allocs_length (σ : Val) (es : List Ev) : (allocs σ es).length = (allocDsts es).length := by
  unfold allocs allocDsts
  rw [List.length_filterMap_eq_countP, List.length_filterMap_eq_countP]
  congr 1
  funext e
  rw [alloc?_isSome]

/-- **A tree's `HeapBuf`s, its path's, are at most its body's allocation atoms.** -/
theorem bufs_le_cntL {P : Core.Program} {t : Tree} (hb : t.BufsOk P) {fn : Fn} (hf : P.find? t.name = some fn) :
    t.bufs.length ≤ cntL fn.body := by
  cases t with
  | phantom => exact Nat.zero_le _
  | node f σ bufs kids =>
    have h1 : bufs = allocs σ (Memory.Tree.events P (.node f σ bufs kids)) := hb.1
    change bufs.length ≤ _
    rw [h1, allocs_length]
    unfold Tree.events
    rw [hf]
    dsimp only [Tree.val]
    split
    · rename_i es vs hw; exact allocDsts_le_cnt hw
    · simp [allocDsts]

/-- A tree whose function is not in the program has no `HeapBuf`. -/
theorem bufs_nil_of_none {P : Core.Program} {t : Tree} (hb : t.BufsOk P) (hf : P.find? t.name = none) :
    t.bufs.length = 0 := by
  cases t with
  | phantom => rfl
  | node f σ bufs kids =>
    have h1 : bufs = allocs σ (Memory.Tree.events P (.node f σ bufs kids)) := hb.1
    change bufs.length = 0
    rw [h1]
    unfold Tree.events
    rw [hf]
    rfl

/-! ## `CurHyps` -/

variable {L : Lay} {D : Ref → RefD} {A : String → FnAl}

/-- **The guest's cursor facts from one check per function.** -/
theorem curHyps_of (hP : ProgAl guestProgram coreProgram A)
    (hchk : ∀ f fn, coreProgram.find? f = some fn → allocFnChk (A f).X fn (A f).code (A f).d = true) :
    CurHyps L D A where
  facts f fn hf := by
    have h := hchk f fn hf
    simp only [allocFnChk, Bool.and_eq_true] at h
    rw [hP.body f fn hf]
    exact curFactsX_of h.1.1
  loopNext f fn hf off oc od of hi hn := by
    have h := hchk f fn hf
    simp only [allocFnChk, Bool.and_eq_true] at h
    rw [Program.loop_of_find? hf]
    exact loop_of_nextOk h.1.2 hi hn
  notLast f fn hf hl σ es vs hw i c hc q s hs := by
    have h := hchk f fn hf
    simp only [allocFnChk, Bool.and_eq_true] at h
    rw [Program.loop_of_find? hf] at hl
    have h2 := h.2
    rw [hl, Bool.not_true, Bool.false_or] at h2
    exact loopX_notLast h2 hw hc hs
  bufsLe r hR _ I hI := by
    obtain ⟨rd, hH, -⟩ := hR.honest
    have hI' : I ∈ (D r).T.instsA L.fs coreProgram.loop L.al L.H (0, (D r).T.block L.fs coreProgram.loop) r.hdr := hI
    have hb := instsA_bufsOk _ _ _ hH.bufsOk I hI'
    cases hf : coreProgram.find? I.t.name with
    | none => rw [bufs_nil_of_none hb hf]; exact Nat.zero_le _
    | some fn =>
      have h := hchk _ fn hf
      simp only [allocFnChk, Bool.and_eq_true] at h
      have hc := cnt_of_curChkX h.1.1
      exact (bufs_le_cntL hb hf).trans hc

end

end LeanVM.Guest.EndExec
