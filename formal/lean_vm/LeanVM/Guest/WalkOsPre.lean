/-
  LeanVM.Guest.WalkOsPre

  What `open_stacked`'s dispatch into `level_positions` writes: at the rate's arm, the squeezes'
  decodes, whose window pointers name windows (`QueryWinsOk`), the walk's obligation
  (`OqMainWins`) at the level's queries.
-/

module

public import LeanVM.Guest.WalkOsDefs
public import LeanVM.Guest.B1.Whir.LpSound
public import LeanVM.Guest.B1.Opening.QueriesWalk
public import LeanVM.Guest.B1.Bits.QueryWindowsAll

/-!
# `level_positions`' windows

* `holdsList_flatD`: a block of atoms, calls and dispatches that holds holds statement by
  statement (`StmtOkD`, a dispatch's arm at its selector).
* `queryWinsOk_of_lp`: from `level_positions`' meaning (`MeaningLevelPositions`, `Whir/LpSound`),
  the window pointers at `qbp` name the windows of every query its `S·128/d` decodes cover.
* `lp_walk`: from a call of a specialization of `lpTable` at `[w0, fs0..fs4, qpos, qbp, tabs]`,
  `OqMainWins` at `g^n` for a walk of `oqCount odd base n ≤ S·128/d` queries.
-/

namespace LeanVM.Guest.End

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest LeanVM.Guest.B1
open LeanVM.Guest.B1.Whir LeanVM.Guest.Value LeanVM.Protocol.Verifier

@[expose] public section

variable {C : CallRel} {rd : Reader} {σ : Val}

/-! ## Flat blocks with dispatches -/

/-- A statement's relation, a dispatch's at its selector's arm. -/
def StmtOkD (C : CallRel) (rd : Reader) (σ : Val) : Stmt → Prop
  | .atom a => a.Holds rd σ
  | .call f args rets => C f (args.map σ) (rets.map σ)
  | .callIf c f args => IsInK (σ c) ∧ (σ c ≠ 0 → C f (args.map σ) [])
  | .dispatch x fs args rets => ∃ (j : ℕ) (h : j < fs.length), σ x = ofK (addressOfIndex j) ∧
      C fs[j] (args.map σ) (rets.map σ)
  | _ => True

/-- **A block of atoms, calls and dispatches holds** statement by statement. -/
theorem holdsList_flatD : ∀ (ss : List Stmt), ss.all flatD = true → ∀ (next : Prop)
    (kret : List E → Prop), Stmt.HoldsList C rd σ ss next kret → (∀ s ∈ ss, StmtOkD C rd σ s) ∧ next
  | [], _, _, _, h => ⟨fun _ hs ↦ absurd hs (by simp), h⟩
  | s :: ss, hf, next, kret, h => by
    simp only [List.all_cons, Bool.and_eq_true] at hf
    obtain ⟨hs, hf⟩ := hf
    have key : StmtOkD C rd σ s ∧ Stmt.HoldsList C rd σ ss next kret := by
      match s, hs with
      | .atom a, _ => exact h
      | .call f args rets, _ => exact h
      | .callIf c f args, _ => exact ⟨⟨h.1, h.2.1⟩, h.2.2⟩
      | .dispatch x fs args rets, _ => exact h
    obtain ⟨hk, ht⟩ := key
    obtain ⟨hall, hn⟩ := holdsList_flatD ss hf next kret ht
    refine ⟨fun t ht' ↦ ?_, hn⟩
    rcases List.mem_cons.mp ht' with rfl | ht'
    · exact hk
    · exact hall t ht'

/-- Every statement before `start` holds (one past the body a `ret`, which says nothing). -/
theorem okAt {body : List Stmt} {start i : ℕ} (h : ∀ s ∈ body.take start, StmtOkD C rd σ s)
    (hi : i < start) : StmtOkD C rd σ (stmtAt body i) := by
  unfold stmtAt
  by_cases hl : i < body.length
  · rw [List.getD_eq_getElem _ _ hl]
    exact h _ (List.mem_iff_getElem.mpr ⟨i, by simp; omega, by simp⟩)
  · rw [List.getD_eq_default _ _ (by omega)]
    trivial

/-! ## The windows -/

/-- **The window pointers name windows**: every query `S·128/d` decodes covers, its pointer at
`qbp` a frame run of its windows at a position below `2^d`. -/
theorem queryWinsOk_of_lp {S d cd q : ℕ} (hd : 1 ≤ 128 / d) (hq : q ≤ S * (128 / d))
    {args rets : List E} (h : MeaningLevelPositions S d cd rd args rets) :
    QueryWinsOk rd (args.getD 7 0) q d cd := by
  intro k hk bp hbp
  set per := 128 / d
  have hjj : k / per < S := by
    rw [Nat.div_lt_iff_lt_mul (by omega)]; exact lt_of_lt_of_le hk hq
  have ht : k % per < per := Nat.mod_lt _ (by omega)
  have hk' : k = k / per * per + k % per := by
    have := Nat.div_add_mod k per; rw [Nat.mul_comm] at this; omega
  have hw := h.1 (k / per) hjj
  simp only [MeaningDecodeQueryWindows] at hw
  obtain ⟨-, hall⟩ := hw
  obtain ⟨-, p, hptr, hrun⟩ := hall (k % per) ht
  rw [loadHolds_mul_gen_pow, ← hk'] at hptr
  rw [loadHolds_unique hbp hptr]
  exact ⟨_, by unfold qwPosOf; exact Nat.mod_lt _ (by positivity), hrun⟩

/-- **A call of `level_positions`** of `lpTable` at `[w0, fs0..fs4, qpos, qbp, tabs]`, the table
at `tabs`: its window pointers at `qbp` name windows for the walk of `oqCount odd base n` queries
it covers. -/
theorem lp_walk {κ : ℕ} (hκ : κ ≤ 32) (L : MemoryImage κ) {e : String × ℕ × String × ℕ × ℕ}
    (he : e ∈ lpTable) {n odd base : ℕ} (hodd : odd = 1 → base = 1)
    (hcov : lpCovers e.2.1 n odd base e.2.2.2.1 e.2.2.2.2 = true)
    {args rets : List E} (hwt : WinTabs L.read (args.getD 8 0))
    (hrel : coreProgram.Rel L.read e.1 args rets) :
    OqMainWins L.read e.2.2.2.1 e.2.2.2.2 odd base (args.getD 7 0) (gen ^ n) := by
  obtain ⟨hf, hl⟩ := lpTable_ok e he
  simp only [lpCovers, Bool.and_eq_true, Nat.ble_eq, Nat.blt_eq, beq_iff_eq,
    List.contains_iff_mem] at hcov
  obtain ⟨⟨⟨⟨⟨⟨hq, hper⟩, hpw⟩, hs0⟩, hso⟩, hs5⟩, hshape⟩ := hcov
  have hm := Whir.lp_sound hf hl hpw hs0 hso hs5
    (fun a r ha hc ↦ decode_query_windows_all_holds _ hshape hκ L a r ha hc) hwt hrel
  exact oqMainWins_of_queryWinsOk hodd (queryWinsOk_of_lp hper hq hm)

end
end LeanVM.Guest.End
