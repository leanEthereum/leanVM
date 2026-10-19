/-
  LeanVM.Guest.B2C.CplRun

  B2's completeness for one compiled function: its checked parts compose into a counted run
  from its entry to its return registers.
-/

module

public import LeanVM.Guest.B2C.CplWalk

/-!
# A function's run

`checkWin_cpl` reads off a soundness window's check what the completeness walk relies on: the
window's cells are the certificate's, its segments are linked, its first segment's environment
holds where its start's does, and it hands on to the next window's start an environment holding
the next window's. `cplRun_of_walk`: given the walk lemma (`WGood` for every block and position),
the parts of the windows compose, part after part along the path, into the run `CplRun` states.
-/

namespace LeanVM.Guest.B2C

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Exec
open LeanVM.Guest.Check LeanVM.Guest.Memory

@[expose] public section

/-! ## What a soundness window's check gives -/

section Win

variable {j i : ℕ}

/-- The segments of window `i` of function `j`. -/
noncomputable def segsW (j i : ℕ) : List Exec.Seg :=
  (execWin (certOf j).facts (fnOf j) ((certOf j).cutAt i).J ((certOf j).cutAt i).env
    ((certOf j).endAt (fnOf j) i)).segs

/-- The offset window `i` hands on at, where no segment of it starts. -/
noncomputable def wJW (j i : ℕ) : ℕ :=
  bif Nat.blt i (certOf j).cuts.length then ((certOf j).cutAt (i + 1)).J else 0

/-- The environment window `i` hands on there. -/
noncomputable def wenvW (j i : ℕ) : Trie Sym :=
  bif Nat.blt i (certOf j).cuts.length then envOf ((certOf j).cutAt (i + 1)).env else .nil

/-- **What a soundness window's check gives the completeness walk.** -/
theorem checkWin_cpl (hc : checkWin glob (fnOf j) (coreOf j) (certOf j) (j == 1) i = true) :
    (certOf j).contOk i = true ∧ (certOf j).insOk (nth (certOf j).ins i []) = true ∧
      linkedWeak (index (segsW j i)) (segsW j i) (wJW j i) (wenvW j i) = true ∧
      (∃ s, getF (index (segsW j i)) ((certOf j).cutAt i).J = some s ∧
        s.start = ((certOf j).cutAt i).J ∧ s.env.sub Sym.beq (envOf ((certOf j).cutAt i).env) = true) ∧
      (i < (certOf j).cuts.length → ((certOf j).cutAt i).start ≤ ((certOf j).cutAt (i + 1)).start ∧
        ∀ s, getF (index (segsW j i)) ((certOf j).cutAt (i + 1)).J = some s →
          s.start = ((certOf j).cutAt (i + 1)).J ∧
            (envOf ((certOf j).cutAt (i + 1)).env).sub Sym.beq s.env = true) := by
  unfold checkWin at hc
  unfold segsW
  rcases hR : execWin (certOf j).facts (fnOf j) ((certOf j).cutAt i).J ((certOf j).cutAt i).env
    ((certOf j).endAt (fnOf j) i) with ⟨segs, dead⟩
  rw [hR] at hc
  simp only [listSeq_eq, Trie.seq_eq, Bool.and_eq_true] at hc
  obtain ⟨⟨⟨⟨⟨h1, h2⟩, -⟩, hlink⟩, -⟩, hc⟩ := hc
  refine ⟨h1, h2, ?_, ?_, ?_⟩
  · simpa [Cert.fxAt, wJW, wenvW] using hlink
  · split at hc
    · rename_i st hst
      unfold segAt at hst
      split at hst
      · rename_i s hs
        cases hb : s.start == ((certOf j).cutAt i).J
        · rw [hb] at hst; cases hst
        · rw [hb] at hst
          obtain rfl := Option.some.inj hst
          simp only [Bool.and_eq_true] at hc
          exact ⟨s, by simpa [Cert.fxAt] using hs, beq_iff_eq.mp hb, hc.1⟩
      · cases hst
    · cases hc
  · intro hi
    have hb : Nat.blt i (certOf j).cuts.length = true := Nat.blt_eq.mpr hi
    split at hc
    · simp only [Bool.and_eq_true] at hc
      have hw := hc.2
      unfold winEnd at hw
      rw [hb] at hw
      simp only [Bool.cond_true, Bool.and_eq_true, Nat.ble_eq] at hw
      obtain ⟨⟨-, hle⟩, henv⟩ := hw
      refine ⟨hle, fun s hs ↦ ?_⟩
      rw [hs] at henv
      simp only [Bool.and_eq_true] at henv
      exact ⟨beq_iff_eq.mp henv.1, henv.2⟩
    · cases hc

end Win

/-! ## A part's context -/

theorem fnOf_memC {j : ℕ} (h : j < nFns) : fnOf j ∈ Data.functions := by
  unfold fnOf
  rw [nth_eq (functions_lengthC ▸ h)]
  exact List.getElem_mem _

/-- The context of part `k` of window `i` of function `j`. -/
noncomputable def Xp (j i k : ℕ) : CX :=
  cxOf j (index (segsW j i)) (clocW (certOf j) i) (statT (fsN j) (plumbOf j).stat .nil)
    (nvOf (coreOf j).body 0) (stopOf j i k)

/-- The walk's start of part `k`. -/
noncomputable def st0 (j i k : ℕ) (s : Exec.Seg) : CW :=
  ⟨s, s.items.drop (partM j i k), fileB (clocW (certOf j) i) (fsN j) (partStmts j i k) .nil, [], [], [],
    partC j i k, partU j i k, bif Nat.beq (partM j i k) 0 then some (partJ j i k) else none, 0⟩

theorem cplRes_eq (j i k : ℕ) : cplRes j i k = (match getF (index (segsW j i)) (partJ j i k) with
    | some s => bif Nat.beq s.start (partJ j i k) then cw (Xp j i k) (partStmts j i k) (st0 j i k s)
      else .fail 91
    | none => .fail 90) := by
  unfold cplRes Xp st0 segsW
  rw [execWinC_eq]
  rcases execWin (certOf j).facts (fnOf j) ((certOf j).cutAt i).J ((certOf j).cutAt i).env
    ((certOf j).endAt (fnOf j) i) with ⟨segs, dead⟩
  simp only [listSeq_eq, Trie.seq_eq, CLoc.seq_eq, Cnt.seq_eq, natSeq_eq]
  rfl

/-! ## A loop helper's last call -/

theorem loop_split {fn : Core.Fn} (h : fn.loop = true) :
    ∃ A c args, fn.body = A ++ [.callIf c fn.name args, .ret []] := by
  unfold Core.Fn.loop at h
  split at h
  · rename_i c g args rest hr
    refine ⟨rest.reverse, c, args, ?_⟩
    rw [← List.reverse_reverse fn.body, hr, ← beq_iff_eq.mp h]
    simp
  · cases h

/-- On a path through a loop helper returning only at its end, its last call is its closing one. -/
theorem lastCall_of {fn : Core.Fn} {σ : Val} {es : List Ev} {vs : List V}
    (hw : walk σ fn.body = .ret es vs) (hl : fn.loop = true) (hok : lastOkC fn.body = true) :
    ∀ c, (calls es).getLast? = some c → c.f = fn.name := by
  obtain ⟨A, c, args, hb⟩ := loop_split hl
  obtain ⟨A', vs', hb', hA'⟩ := lastOkC_split hok
  rw [hb, show A ++ [Stmt.callIf c fn.name args, .ret []] =
    (A ++ [.callIf c fn.name args]) ++ [.ret []] by simp] at hb'
  obtain ⟨rfl, -⟩ := List.append_inj' hb' rfl
  rw [noRetList_append] at hA'
  rw [hb, walk_appendC] at hw
  rcases walk_noRetC A ((Bool.and_eq_true _ _).mp hA').1 with ⟨eA, h1⟩ | h1
  · have hw2 : walk σ [Stmt.callIf c fn.name args, .ret []] =
        .ret [Ev.inK c, if σ c = 0 then Ev.skip fn.name args else Ev.call fn.name args []] [] := rfl
    rw [h1, hw2] at hw
    simp only [Out.seq, Out.pre, Out.ret.injEq] at hw
    obtain ⟨rfl, -⟩ := hw
    intro c' hc'
    simp [calls, List.filterMap_append, callIf_ev] at hc'
    rw [← hc']
  · rw [h1] at hw
    cases hw

/-! ## A part's hypotheses -/

section Part

variable {κ : ℕ} {L : MemImage κ} {j fp : ℕ} {σ : Val} {es : List Ev} {vs : List V}
  {kfps : List ℕ} {hdr : E × E} {ck : List (Opcode → ℕ)}

/-- **What `cpl_run` assumes of function `j`'s instance.** -/
structure FnH (L : MemImage κ) (j fp : ℕ) (σ : Val) (es : List Ev) (vs : List V) (kfps : List ℕ)
    (hdr : E × E) (ck : List (Opcode → ℕ)) : Prop where
  j1 : 1 ≤ j
  jn : j < nFns
  ok : CplOk j
  chk : ∀ i ≤ (certOf j).cuts.length, checkWin glob (fnOf j) (coreOf j) (certOf j) (j == 1) i = true
  pows : (certOf j).facts.pows.Ok
  le32 : κ ≤ 32
  jt : JTHolds glob L
  tab : ∀ q ∈ Memory.tableCells, L.read (gpow q.1) = some q.2
  main : j = 1 → fp = 0
  frame : FrameHolds L j fp σ es vs kfps hdr
  kids : KidsRun L σ es kfps ck
  hev : ∀ e ∈ es, e.Holds L.read σ
  walk : walk σ (coreOf j).body = .ret es vs

theorem one_le_nParts (j i : ℕ) : 0 < nParts j i := by
  unfold nParts
  exact Nat.lt_of_lt_of_le Nat.zero_lt_one (Nat.le_max_left _ _)

theorem winOkC_of {j i : ℕ} (h : cplWin j i 0 = true) : winOkC j i = true := by
  simp only [cplWin, Nat.beq_refl, Bool.cond_true, Bool.and_eq_true] at h
  exact h.1.1.1

theorem FnH.ctx (F : FnH L j fp σ es vs kfps hdr ck) : Exec.Ctx (certOf j).facts κ (gpow fp) := by
  refine ⟨F.pows, fun h ↦ ?_, F.le32⟩
  have := checkWin_fpOne (F.chk 0 (Nat.zero_le _))
  rw [h] at this
  rw [F.main (by simpa using this), gpow_zero']

/-- **The walk's hypotheses hold in every part**, the part's atoms being events. -/
theorem wh_part (F : FnH L j fp σ es vs kfps hdr ck)
    (hlb : lastOkC (coreOf j).body = true) {i k : ℕ} (hi : i ≤ (certOf j).cuts.length) :
    WH L j fp (Xp j i k) (segsW j i) (wJW j i) (wenvW j i) σ es vs kfps hdr ck := by
  have hctx := F.ctx
  have hfet := guest_fetches (fnOf_memC F.jn)
  have hcw := checkWin_cpl (F.chk i hi)
  have hw0 := winOkC_of (F.ok i hi 0 (one_le_nParts j i))
  simp only [winOkC, Bool.and_eq_true] at hw0
  obtain ⟨⟨⟨⟨hpack, -⟩, -⟩, hpar⟩, -⟩ := hw0
  refine ⟨cxOk F.frame F.pows _ _ _ _, hctx, fun s hs ↦ execWin_z hctx hfet hs,
    fun s hs ↦ (execWin_good (L := L) hctx hfet _ _ _ s hs).2.2, rfl, hcw.2.2.1,
    fun v c h ↦ clocW_get (cont_of F.chk) hi hcw.2.1 rfl hpack h, rfl, rfl, rfl, rfl, rfl, rfl,
    rfl, rfl, rfl, fun n hsel ↦ ?_, F.frame, F.kids, F.hev, fun hl ↦ lastCall_of F.walk hl hlb, F.jt,
    F.tab, F.j1, F.jn⟩
  simp only [Bool.or_eq_true, Nat.blt_eq] at hsel
  unfold namedOf
  rcases hsel with h | h
  · have hpe : (coreOf j).params = (List.range (coreOf j).params.length).map V.n := beq_iff_eq.mp hpar
    refine List.mem_append_left _ (List.mem_append_left _ ?_)
    have : (Xp j i k).nargs = (coreOf j).params.length := rfl
    rw [this] at h
    rw [hpe]
    exact List.mem_map.mpr ⟨n, List.mem_range.mpr h, rfl⟩
  · rw [bitK_eq] at h
    rcases nvOf_spec _ 0 n h with h' | ⟨a, ha, hm⟩
    · simp at h'
    · exact List.mem_append_left _ (List.mem_append_right _
        (List.mem_flatMap.mpr ⟨_, atoms_last hlb F.walk (fun h ↦ by cases h) ha, hm⟩))

end Part

end
end LeanVM.Guest.B2C
