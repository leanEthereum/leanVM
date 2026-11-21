/-
  LeanVM.Guest.CoreMode.SigSplit

  `sigOk` in four parts, each its own kernel evaluation, for a long body's signature check (`core.py`'s `SPLIT`).
-/

module

public import LeanVM.Guest.CoreMode.Core

namespace LeanVM.Guest.CoreMode

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core

@[expose] public section

/-- `sigOk`'s preconditions and pointer facts. -/
noncomputable def sigOkPre (G : Mode.Sig) (Cf : CFun) (np nr : ℕ) (jt : Mode.Rng) : Bool :=
  G.self.isNone && G.term.isEmpty && G.postL.isEmpty &&
    (G.postP.all fun r ↦ monoR G np nr (rngM r.1) && expI G Cf.H.res np (np + nr) r.1.lo &&
      expI G Cf.H.res np (np + nr) r.1.hi &&
      Cf.H.sig.postPR.any (prunIs r ·) && Cf.H.sig.postR.any (rngXIs r.1 ·)) && G.postLP.isEmpty &&
    G.postT.isEmpty && G.postC.isEmpty && Cf.H.sig.preP.all (hpAll G np G.pre) &&
    (Cf.H.sig.prePR.all fun p ↦ G.preP.any fun r ↦ monoS G np false (rngM r.1) && prunIs r p) &&
    preCov G np (Cf.H.sig.pre.filter fun c ↦ !mainPre Cf G c) &&
    Cf.H.sig.preR.all (fun q ↦ ((jt :: G.preR).any fun r ↦ (monoS G np false r.q && rngIs r q) ||
      (monoS G np false (rngM r) && rngXIs r q) || ((rngM r).bs.all (baseS Cf.gl (gpOf np Cf.H.sig.gw) np ·.1) &&
        rngLIs Cf.gl (gpOf np Cf.H.sig.gw) r q)) || runCov G np q ||
      G.pre.any fun m ↦ m.bs.all (baseS Cf.gl (gpOf np Cf.H.sig.gw) np ·.1) && ptLIs Cf.gl (gpOf np Cf.H.sig.gw) m q)

/-- `sigOk`'s promised cells. -/
noncomputable def sigOkPost (G : Mode.Sig) (Cf : CFun) (np nr : ℕ) : Bool :=
  G.post.all (fun m ↦ (monoR G np nr m && match monoC m with
      | some c => cellIn c Cf.posts
      | none => false) || postIn Cf.X Cf.fn.body G np (Cf.post.map (·.1)) m ||
      hpIn G np true Cf.H.sig.postP Cf.posts m || postNIn Cf.X Cf.fn.body G np Cf.H.sig m)

/-- `sigOk`'s promised run `r`. -/
noncomputable def postRP (G : Mode.Sig) (Cf : CFun) (np nr : ℕ) (r : Mode.Rng) : Bool :=
  (monoR G np nr r.q && ((Cf.H.sig.postR.any fun q ↦ rngIs r q) ||
      match monoC r.q, runPts ⟨[], 0⟩ r with
      | some c, some l => l.all fun p ↦ cellIn ⟨c.bases, c.off + p.off⟩ Cf.posts
      | _, _ => false)) || postRIn Cf.X Cf.fn.body G np (Cf.post.map (·.1)) r ||
      (monoR G np nr (rngM r) && expI G Cf.H.res np (np + nr) r.lo && expI G Cf.H.res np (np + nr) r.hi &&
        Cf.H.sig.postR.any (rngXIs r ·)) || postRB G Cf np r || postRNIn Cf.X Cf.fn.body G np Cf.H r

/-- `sigOk`'s promised runs. -/
noncomputable def sigOkPostR (G : Mode.Sig) (Cf : CFun) (np nr : ℕ) : Bool := G.postR.all (postRP G Cf np nr)

/-- `sigOk`'s ghost slots. -/
noncomputable def sigOkGh (Cf : CFun) (np : ℕ) : Bool :=
  Nat.ble Cf.H.sig.ghosts (Cf.gl.length + Cf.H.sig.gw.length) &&
    Cf.H.sig.gw.all fun x ↦ Nat.blt x.2 Cf.H.sig.ghosts && match x.1.bases with
      | [(p, 1)] => Nat.blt p np
      | _ => false

theorem sigOk_of {G : Mode.Sig} {Cf : CFun} {np nr : ℕ} {jt : Mode.Rng} (h1 : sigOkPre G Cf np nr jt = true)
    (h2 : sigOkPost G Cf np nr = true) (h3 : sigOkPostR G Cf np nr = true) (h4 : sigOkGh Cf np = true) :
    sigOk G Cf np nr jt = true := by
  simp only [sigOkPre, sigOkPost, sigOkPostR, sigOkGh, Bool.and_eq_true] at h1 h2 h3 h4
  simp only [sigOk, Bool.and_eq_true]
  exact ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4.1⟩, h4.2⟩

/-- Entry `i` of `l` satisfies `p` (none past its end). -/
def chunkAll {α : Type} (p : α → Bool) (l : List α) (i : ℕ) : Bool := ((l.drop i).take 1).all p

/-- **A list whose entries all satisfy `p`**, entry by entry. -/
theorem all_of_chunks {α : Type} {p : α → Bool} {l : List α} (n : ℕ) (hn : l.length ≤ n)
    (h : ∀ i < n, chunkAll p l i = true) : l.all p = true := by
  rw [List.all_eq_true]
  intro x hx
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hx
  have := h i (by omega)
  simp only [chunkAll, List.all_eq_true] at this
  refine this _ ?_
  rw [List.drop_eq_getElem_cons hi, List.take_succ_cons, List.take_zero]
  exact List.mem_singleton_self _

/-- **A long body's own signature check**, in parts (no heap contract). -/
theorem ownOk_of {G : Mode.Sig} {Cf : CFun} {np nr : ℕ} {jt : Mode.Rng} (hc : Cf.hc = false)
    (h1 : sigOkPre G Cf np nr jt = true) (h2 : sigOkPost G Cf np nr = true) (h3 : sigOkPostR G Cf np nr = true)
    (h4 : sigOkGh Cf np = true) : ownOk G Cf np nr jt = true := by
  simp only [ownOk, hc, Bool.cond_false]
  exact sigOk_of h1 h2 h3 h4

end

end LeanVM.Guest.CoreMode
