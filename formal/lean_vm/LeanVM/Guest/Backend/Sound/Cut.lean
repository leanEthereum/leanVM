/-
  LeanVM.Guest.Backend.Sound.Cut

  A function's piece from its parts (`Backend.Cut`): the walk glued at its cuts, and the code
  chunk by chunk.
-/

module

public import LeanVM.Guest.Backend.Cut
public import LeanVM.Guest.Backend.Sound.Compiles

/-!
# Cut pieces glued

`pieceOk_of_cut`: if a function's walk from its start state reaches `st₁` at its first cut
(`placeHead`), each next cut from the one before (`placeBlockN`), and its end `st` from the last
cut (`placeTail`), and `fnPreOk`, `cutHeadOk` and every `cutChunkOk` hold of `st`, its piece holds:
`pieceOk … = true`, the very Bool `compiles_of_pieces` reads, with no evaluation of the whole walk.
The glue is the walk's own structure: `placeBlock` of a block is `placeBlockN` of its first `n`
statements then `placeBlock` of the rest (`placeBlock_split`).
-/

namespace LeanVM.Guest.Backend

open LeanVM.Guest.Core

@[expose] public section

/-- A walk that succeeds, then another: their sequence. -/
theorem P.bind_ok {α β : Type} {m : P α} {f : α → P β} {ctx : Ctx} {st st' : St} {a : α}
    (h : m ctx st = .ok (a, st')) : (m >>= f) ctx st = f a ctx st' := by
  show (do let (a, s) ← m ctx st; f a ctx s : Except String (β × St)) = _
  rw [h]
  rfl

theorem placeBlock_cons (s : Stmt) (rest : List Stmt) :
    placeBlock (s :: rest) = (do placeStmt s rest; endStmt; placeBlock rest) := by
  rw [placeBlock]

/-- **A block's walk at a cut**: its first `n` statements, then the rest. -/
theorem placeBlock_split : ∀ (l : List Stmt) (n : ℕ),
    placeBlock l = (do placeBlockN l n; placeBlock (l.drop n))
  | [], n => by
      rw [placeBlockN, List.drop_nil, pure_bind]
  | _ :: _, 0 => by
      rw [placeBlockN, List.drop_zero, pure_bind]
  | s :: rest, n + 1 => by
      rw [placeBlock_cons, placeBlock_split rest n, placeBlockN, List.drop_succ_cons]
      simp only [bind_assoc]

theorem placeBlockN_add : ∀ (l : List Stmt) (n m : ℕ),
    placeBlockN l (n + m) = (do placeBlockN l n; placeBlockN (l.drop n) m)
  | [], n, m => by
      rw [placeBlockN, placeBlockN, List.drop_nil, placeBlockN, pure_bind]
  | s :: rest, 0, m => by
      rw [Nat.zero_add, placeBlockN, List.drop_zero, pure_bind]
  | s :: rest, n + 1, m => by
      rw [Nat.add_right_comm, placeBlockN, placeBlockN, placeBlockN_add rest n m, List.drop_succ_cons]
      simp only [bind_assoc]

/-- **Two consecutive cuts glued**: the walk to cut `k`, then over the next `m` statements. -/
theorem placeHead_add {tf : TracedFn} {k m : ℕ} {ctx : Ctx} {st st₁ st₂ : St}
    (h₁ : placeHead tf k ctx st = .ok ((), st₁))
    (h₂ : placeBlockN (tf.core.body.drop k) m ctx st₁ = .ok ((), st₂)) :
    placeHead tf (k + m) ctx st = .ok ((), st₂) := by
  have : placeHead tf (k + m) = (placeHead tf k >>= fun _ => placeBlockN (tf.core.body.drop k) m) := by
    simp only [placeHead, placeBlockN_add, bind_assoc]
  rw [this, P.bind_ok h₁, h₂]

/-- **A function's walk from its cut parts.** -/
theorem placeBody_of_cut {tf : TracedFn} {k : ℕ} {ctx : Ctx} {st st₁ st₂ : St}
    (h₁ : placeHead tf k ctx st = .ok ((), st₁)) (h₂ : placeTail tf k ctx st₁ = .ok ((), st₂)) :
    placeBody tf ctx st = .ok ((), st₂) := by
  have : placeBody tf = (placeHead tf k >>= fun _ => placeTail tf k) := by
    simp only [placeBody, placeHead, placeTail, placeParams, placeBlock_split tf.core.body k,
      bind_assoc]
  rw [this, P.bind_ok h₁, h₂]

/-- `placeFn` from its walk and its other checks. -/
theorem placeFn_of_cut {loops : Loops} {sigs : SMap (ℕ × ℕ)} {t : Tables} {tf : TracedFn}
    {st : St} (hpre : fnPreOk loops tf st = true)
    (hbody : placeBody tf (ctxOf loops sigs tf) (initSt loops t tf) = .ok ((), st)) :
    placeFn loops sigs t tf = .ok (placedOf tf st) := by
  simp only [fnPreOk, Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true,
    decide_eq_true_eq] at hpre
  obtain ⟨⟨hreg, hret⟩, hlt⟩ := hpre
  unfold placeFn
  simp only [hreg, Bool.false_eq_true, ↓reduceIte]
  split
  · rw [hbody]
    simp only [Nat.not_le.mpr hlt, ↓reduceIte]
    rfl
  · next hne =>
    split at hret
    · next vs hvs => exact absurd hvs (hne vs)
    · cases hret

/-- **A function's piece from its parts**: its placement, `pieceOk`'s comparisons but the code's,
and its code chunk by chunk. -/
theorem pieceOk_of_cut {loops : Loops} {sigs : SMap (ℕ × ℕ)} {l : Layout} {t : Tables}
    {tf : TracedFn} {o : FnOut} {pc0 frame : ℕ} {cf : CompiledFunction} {pf : Placed} {t' : Tables}
    (hplace : placeFn loops sigs t tf = .ok (pf, t'))
    (hhead : cutHeadOk t tf o pc0 cf pf t' = true)
    (hchunks : ∀ c < cf.chunks.length, cutChunkOk l pc0 frame cf pf c = true) :
    pieceOk loops sigs l t tf o pc0 frame cf = true := by
  simp only [cutHeadOk, Bool.and_eq_true, beq_iff_eq] at hhead
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩, h10⟩ := hhead
  unfold pieceOk pieceOkWith
  rw [hplace]
  simp only [decide_eq_true_eq] at h3 h7
  simp only [Bool.and_eq_true, beq_iff_eq, h1, h2, h3, h4, h5, h6, h7, h8, h9, and_true, true_and,
    decide_eq_true_eq, decide_true]
  have hlen : (resolvedFn l pc0 { (emitFn pf.fn).1 with frameSize := frame }).length = o.size := by
    simp [resolvedFn, h6]
  rw [chunked_eq, hlen]
  apply List.ext_getElem
  · simp [h10]
  · intro i _ h2'
    have := hchunks i h2'
    simp only [cutChunkOk, decide_eq_true_eq, List.getD_eq_getElem?_getD,
      List.getElem?_eq_getElem h2', Option.getD_some] at this
    simp [this]

/-- **Function `j`'s piece from its parts**, as `pieceAt` reads it. -/
theorem pieceAt_of_cut {loops : Loops} {sigs : SMap (ℕ × ℕ)} {l : Layout} {p : List TracedFn}
    {os : List FnOut} {cfs : List CompiledFunction} {j k : ℕ} {st₁ st : St}
    (h₁ : placeHead (p.getD j default) k (ctxOf loops sigs (p.getD j default))
      (initSt loops (tablesAt os j) (p.getD j default)) = .ok ((), st₁))
    (h₂ : placeTail (p.getD j default) k (ctxOf loops sigs (p.getD j default)) st₁ = .ok ((), st))
    (hhead : cutHeadAt loops p os cfs j st = true)
    (hchunks : ∀ c < (cfs.getD j noFunction).chunks.length, cutChunkAt l p os cfs j st c = true) :
    pieceAt loops sigs l p os cfs j = true := by
  simp only [cutHeadAt, Bool.and_eq_true] at hhead
  exact pieceOk_of_cut (placeFn_of_cut hhead.1 (placeBody_of_cut h₁ h₂)) hhead.2 hchunks

theorem pieceOkWith_of_pieceOk {test : VMap Loc → Bool} {loops : Loops} {sigs : SMap (ℕ × ℕ)}
    {l : Layout} {t : Tables} {tf : TracedFn} {o : FnOut} {pc0 frame : ℕ} {cf : CompiledFunction}
    {pf : Placed} {t' : Tables} (h : pieceOk loops sigs l t tf o pc0 frame cf = true)
    (hplace : placeFn loops sigs t tf = .ok (pf, t')) (hx : test pf.locs = true) :
    pieceOkWith test loops sigs l t tf o pc0 frame cf = true := by
  unfold pieceOk pieceOkWith at *
  rw [hplace] at h ⊢
  simp only [Bool.and_eq_true] at h ⊢
  exact ⟨h.1, hx⟩

/-- **Function `j`'s piece with a test, from its parts.** -/
theorem pieceAtWith_of_cut {extra : ℕ → VMap Loc → Bool} {loops : Loops} {sigs : SMap (ℕ × ℕ)}
    {l : Layout} {p : List TracedFn} {os : List FnOut} {cfs : List CompiledFunction} {j k : ℕ}
    {st₁ st : St}
    (h₁ : placeHead (p.getD j default) k (ctxOf loops sigs (p.getD j default))
      (initSt loops (tablesAt os j) (p.getD j default)) = .ok ((), st₁))
    (h₂ : placeTail (p.getD j default) k (ctxOf loops sigs (p.getD j default)) st₁ = .ok ((), st))
    (hhead : cutHeadAt loops p os cfs j st = true)
    (hx : extra j (placedOf (p.getD j default) st).1.locs = true)
    (hchunks : ∀ c < (cfs.getD j noFunction).chunks.length, cutChunkAt l p os cfs j st c = true) :
    pieceAtWith extra loops sigs l p os cfs j = true := by
  have h := pieceAt_of_cut h₁ h₂ hhead hchunks
  simp only [cutHeadAt, Bool.and_eq_true] at hhead
  exact pieceOkWith_of_pieceOk h (placeFn_of_cut hhead.1 (placeBody_of_cut h₁ h₂)) hx

end
end LeanVM.Guest.Backend
