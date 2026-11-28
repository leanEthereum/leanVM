/-
  LeanVM.Guest.B1.VsC.WinSeg

  The windows of a long body, by kind: a run of atoms, one call (a `call` or a `dispatch`), a
  branch on its taken arm.
-/

module

public import LeanVM.Guest.Complete.SegA
public import LeanVM.Guest.Memory.Fresh

/-!
# Windows by kind

`SegA` (`Complete/SegA.lean`) is one window of a node's body. Its three kinds here:

* `segA_atoms`: a run of atoms places its `HeapBuf`s from the cursor and enters no callee; what is
  left is, per memory, its allocations, their pointers, its `frameAddr`s, its loads and heap
  hints in the regions, and its atoms holding.
* `segA_call1`: a statement entering one callee on every memory's valuation (a `call`, or a
  `dispatch` by `walk_dispatch`) is a window from the callee's `CallAtA` at the aligned base of the
  callees' cursor, the words it holds and the data it claims added.
* `segA_ite`: a branch whose selector every memory's valuation reads as `σ0` does is a window from
  its taken arm's.
-/

namespace LeanVM.Guest.B1.VsC

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Memory LeanVM.Guest.B1
open LeanVM.Guest.Complete
open LeanVM.Prover.Exec (allocBase)

@[expose] public section

variable {fs : String → ℕ} {al : String → Bool} {cert : String → V → ℕ}

theorem walk_atomsF (σ : Val) : ∀ as : List Atom, walk σ (as.map Stmt.atom) = .fall (as.map Ev.atom)
  | [] => by rw [List.map_nil, walk]; rfl
  | a :: as => by
    rw [List.map_cons, walk, walk1, walk_atomsF σ as]
    simp [Out.seq, Out.pre]

theorem calls_atomsE : ∀ as : List Atom, calls (as.map Ev.atom) = []
  | [] => rfl
  | _ :: as => by simp only [List.map_cons, calls, List.filterMap_cons, Ev.call?]; exact calls_atomsE as

/-- **A run of atoms is a window**: its `HeapBuf`s from `a`, no callee. -/
theorem segA_atoms {k : ℕ} {f : String} {fp : ℕ} {σ0 : Val} {σ : Reader → Val} {Own R : ℕ → Prop}
    {Pre : Reader → Prop} {as : List Atom} {a kc : ℕ} {O : Reader → Prop} {D : ℕ → Prop}
    (h : ∀ rd, LowDef k rd → Pre rd → O rd →
      allocs (σ rd) (as.map Ev.atom) = allocs σ0 (as.map Ev.atom) ∧
      (allocDsts (as.map Ev.atom)).map (σ rd) =
        (bases a (allocs σ0 (as.map Ev.atom))).map (fun b => ofK (addressOfIndex b)) ∧
      (∀ q ∈ addrs (as.map Ev.atom), σ rd q.1 = ofK (addressOfIndex (fp + cert f q.2))) ∧
      (∀ A ∈ loadAddrs (σ rd) (as.map Ev.atom), ∃ i, A = addressOfIndex i ∧ (Own i ∨ R i ∨ D i)) ∧
      (∀ A ∈ heapHintAddrs (σ rd) (as.map Ev.atom), ∃ i, A = addressOfIndex i ∧ (Own i ∨ R i ∨ D i)) ∧
      ∀ x ∈ as, x.Holds rd (σ rd)) :
    SegA (fs := fs) (al := al) (cert := cert) k f fp σ0 σ Own R Pre (as.map Stmt.atom) (as.map Ev.atom)
      a (a + (allocs σ0 (as.map Ev.atom)).sum) kc kc O O D D [] := by
  refine ⟨rfl, by rw [calls_atomsE]; rfl, fun _ h => h, fun _ h => h, ?_, fun rd hl hp ho => ?_⟩
  · rw [calls_atomsE, KidsAtF]; exact ⟨rfl, fun _ h => h, fun _ h => h⟩
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := h rd hl hp ho
  refine ⟨walk_atomsF _ as, h1, h2, h3, by rw [calls_atomsE]; simp [CallsAgree], h4, h5, fun e he => ?_⟩
  obtain ⟨x, hx, rfl⟩ := List.mem_map.mp he
  exact h6 x hx

/-- **A statement entering one callee is a window**: the callee at the aligned base of the callees'
cursor `kc`, completing from what the window starts with, its words and claimed data added. -/
theorem segA_call1 {k : ℕ} {f : String} {fp : ℕ} {σ0 : Val} {σ : Reader → Val} {Own R : ℕ → Prop}
    {Pre : Reader → Prop} {s : Stmt} {g : String} {args rets : List V} {a kc : ℕ}
    {O : Reader → Prop} {D : ℕ → Prop} {Q : Reader → Tree → Prop} {Bc ec : ℕ} {Rc Dc : ℕ → Prop}
    {Oc : Reader → Prop}
    (hw : ∀ rd, LowDef k rd → Pre rd → O rd → Oc rd → walk (σ rd) [s] = .fall [.call g args rets])
    (hag : ∀ rd, LowDef k rd → Pre rd → O rd → Oc rd →
      args.map σ0 = args.map (σ rd) ∧ rets.map σ0 = rets.map (σ rd))
    (hR : ∀ i, Rc i → (R i ∨ Own i) ∨ D i)
    (hc : CallAtA fs al cert k g (args.map σ0) (rets.map σ0) Rc Dc Oc (fun rd => Pre rd ∧ O rd) Q Bc
      (allocBase (al g) kc) (allocBase (al g) kc + Bc) ec) :
    SegA (fs := fs) (al := al) (cert := cert) k f fp σ0 σ Own R Pre [s] [.call g args rets] a a kc ec O
      (fun rd => O rd ∧ Oc rd) D (fun i => D i ∨ Dc i) [Q] := by
  have hcs : calls [Ev.call g args rets] = [⟨g, args, rets, true⟩] := rfl
  refine ⟨by rw [show allocs σ0 [Ev.call g args rets] = [] from rfl]; rfl, by rw [hcs]; rfl, fun _ h => h.1, fun _ h => Or.inl h, ?_,
    fun rd hl hp ho => ?_⟩
  · rw [hcs, KidsAtF]
    simp only [↓reduceIte, List.headD_cons, List.tail_cons]
    refine ⟨Bc, ec, Rc, Dc, Oc, hR, hc, ?_⟩
    rw [KidsAtF]
    exact ⟨rfl, fun _ h => h, fun _ h => h⟩
  have hal : ∀ τ : Val, allocs τ [Ev.call g args rets] = [] := fun _ => rfl
  refine ⟨hw rd hl hp ho.1 ho.2, by rw [hal, hal], by simp [allocDsts, Ev.allocDst?, hal, bases],
    by simp [addrs, Ev.addr?], ?_, by simp [loadAddrs, Ev.loadAddr?],
    by simp [heapHintAddrs, Ev.hintAddrs], fun e he => ?_⟩
  · rw [hcs]
    intro c hc'
    rw [List.mem_singleton] at hc'
    subst hc'
    exact hag rd hl hp ho.1 ho.2
  · rw [List.mem_singleton] at he
    subst he
    trivial

/-- A `call` enters its callee. -/
theorem walk_call (σ : Val) (g : String) (args rets : List V) :
    walk σ [.call g args rets] = .fall [.call g args rets] := by
  simp [walk, walk1, Out.seq, Out.pre]

/-- A `dispatch` enters the callee its selector picks, on any valuation reading the selector as
`σ0` does. -/
theorem walk_dispatch {σ σ0 : Val} {x : V} {gs : List String} {g : String} {args rets : List V}
    (hx : σ x = σ0 x) (hp : pick σ0 x args rets 0 gs = .fall [.call g args rets]) :
    walk σ [.dispatch x gs args rets] = .fall [.call g args rets] := by
  rw [walk, walk, walk1, pick_congr hx gs 0, hp]
  simp [Out.seq, Out.pre]

/-- **A branch is a window from its taken arm's**, its selector in `K` and read as `σ0` does. -/
theorem segA_ite {k : ℕ} {f : String} {fp : ℕ} {σ0 : Val} {σ : Reader → Val} {Own R : ℕ → Prop}
    {Pre : Reader → Prop} {c : V} {z n : List Stmt} {es : List Ev} {a a' kc kc' : ℕ}
    {O O' : Reader → Prop} {D D' : ℕ → Prop} {Qs : List (Reader → Tree → Prop)}
    (hc : ∀ rd, LowDef k rd → Pre rd → O' rd → σ rd c = σ0 c) (hK : IsInK (σ0 c))
    (h : SegA (fs := fs) (al := al) (cert := cert) k f fp σ0 σ Own R Pre (if σ0 c = 0 then z else n) es
      a a' kc kc' O O' D D' Qs) :
    SegA (fs := fs) (al := al) (cert := cert) k f fp σ0 σ Own R Pre [.ite c z n] (.inK c :: es)
      a a' kc kc' O O' D D' Qs := by
  obtain ⟨ha, hl, hO, hD, hk, hr⟩ := h
  have hal : ∀ τ : Val, allocs τ (.inK c :: es) = allocs τ es := fun _ => rfl
  have hcl : calls (.inK c :: es) = calls es := rfl
  refine ⟨by rw [hal]; exact ha, by rw [hcl]; exact hl, hO, hD, by rw [hcl]; exact hk,
    fun rd hl' hp ho => ?_⟩
  obtain ⟨w, al1, ad1, ar1, ag1, lo1, hh1, ev1⟩ := hr rd hl' hp ho
  have hcr := hc rd hl' hp ho
  refine ⟨?_, by rw [hal, hal]; exact al1, by rw [hal]; exact ad1, fun q hq => ar1 q hq,
    by rw [hcl]; exact ag1, fun A hA => lo1 A hA, fun A hA => hh1 A (by simpa [heapHintAddrs,
      Ev.hintAddrs] using hA), fun e he => ?_⟩
  · rw [walk, walk1, hcr]
    rw [show walk (σ rd) [] = .fall [] from rfl]
    by_cases h0 : σ0 c = 0
    · simp only [h0, ↓reduceIte] at w ⊢
      rw [w]; simp [Out.seq, Out.pre]
    · simp only [h0, ↓reduceIte] at w ⊢
      rw [w]; simp [Out.seq, Out.pre]
  · rcases List.mem_cons.mp he with rfl | he
    · show IsInK (σ rd c); rw [hcr]; exact hK
    · exact ev1 e he

end
end LeanVM.Guest.B1.VsC
