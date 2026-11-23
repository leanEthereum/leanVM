module

public import NativeVm.Math.Roots
public import NativeVm.Math.Layout
public import NativeVm.Math.Tables.Claims
public import NativeVm.Math.Tables.Rows
public import NativeVm.Math.Tables.Weights
public import NativeRustcVm.Sumcheck.RoundPoly

/-!
# What `verify_execution`'s phases return, for the contracts of the next ones

`Gives m P`: every run of `m` that succeeds returns a value satisfying `P` (`Gives.bind`,
`Gives.foldlM`). Phase 1's layout holds the bytecode, its stack's log-size and memory column `0`'s
variable count are at most `30`, and it reads no root (`readAnnouncedSizes_some`); phase 2's
commitment adds one root (`commitStack_roots`), ring switching none (`ringSwitch_roots`). The bus
returns four claims (`verifyBusBalance_claims`), the public input two (`publicInputPhase_size`);
the table sumcheck six tables' points and evaluations, table `t`'s evaluations `widths[t]` long at
its point's first `heights[t]` coordinates (`tablePhase_shape`), so `153` column claims
(`tableColumnClaims_size`).
-/

namespace NativeRustcVm.Top

open NativeVm.Model NativeVm.Math LeanVM.Parameters
open LeanVM.Protocol.Verifier (memory0 opKeccak keccakOut bitLength)

public section

/-! ## `Gives` -/

/-- Every run of `m` that succeeds returns a value satisfying `P` (a structure, so that no tactic
unfolds it). -/
structure Gives {α : Type} (m : VM α) (P : α → Prop) : Prop where
  gives : ∀ t x t', m.run t = some (x, t') → P x

theorem Gives.mono {α : Type} {m : VM α} {P Q : α → Prop} (h : Gives m P) (hPQ : ∀ x, P x → Q x) :
    Gives m Q :=
  ⟨fun t x t' hr ↦ hPQ x (h.gives t x t' hr)⟩

theorem Gives.bind' {α β : Type} {m : VM α} {f : α → VM β} {Q : α → Prop} {P : β → Prop}
    (hm : Gives m Q) (hf : ∀ a, Q a → Gives (f a) P) : Gives (m >>= f) P := by
  refine ⟨fun t x t' h ↦ ?_⟩
  simp only [StateT.run_bind, Option.bind_eq_bind] at h
  cases hr : m.run t with
  | none => rw [hr] at h; cases h
  | some p =>
    rw [hr, Option.bind_some] at h
    exact (hf p.1 (hm.gives _ _ _ hr)).gives _ _ _ h

theorem Gives.any {α : Type} (m : VM α) : Gives m (fun _ ↦ True) := ⟨fun _ _ _ _ ↦ trivial⟩

theorem Gives.bind {α β : Type} {m : VM α} {f : α → VM β} {P : β → Prop}
    (hf : ∀ a, Gives (f a) P) : Gives (m >>= f) P :=
  (Gives.any m).bind' fun a _ ↦ hf a

theorem Gives.pure {α : Type} {a : α} {P : α → Prop} (h : P a) : Gives (pure a : VM α) P :=
  ⟨fun _ _ _ h' ↦ by cases h'; exact h⟩

/-- A fold whose every step adds one to `μ` adds the list's length. -/
theorem Gives.foldlM {α β : Type} {f : β → α → VM β} (μ : β → Nat)
    (hf : ∀ b a, Gives (f b a) (fun b' ↦ μ b' = μ b + 1)) :
    ∀ (l : List α) (b : β), Gives (l.foldlM f b) (fun b' ↦ μ b' = μ b + l.length)
  | [], _ => Gives.pure (by simp)
  | a :: l, b => by
    rw [List.foldlM_cons]
    exact (hf b a).bind' fun b' h ↦ (Gives.foldlM μ hf l b').mono fun x hx ↦ by
      simp only [List.length_cons]; omega

/-- A goal `Gives m P`, `P` read off `m`'s last `pure`: split into its steps. -/
macro "gives" : tactic => `(tactic| repeat' (first
  | (with_reducible apply Gives.bind)
  | (with_reducible refine Gives.pure ?_)
  | rfl
  | (intro)
  | split
  | (dsimp only)))

theorem readScalars_gives (n : Nat) : Gives (readScalars n) (·.size = n) :=
  ⟨fun _ _ _ h ↦ NativeRustcVm.Sumcheck.readScalars_size h⟩

/-! ## Phases 1, 2 and 7: the layout and the roots -/

/-- **Phase 1's layout**: the bytecode, the stack's log-size and memory column `0`'s variable
count at most `30`, no root read. -/
theorem readAnnouncedSizes_some {bc : Array UInt64} {s s' : TState} {L : LayoutW} {rate : Nat}
    (h : (readAnnouncedSizes bc).run s = some ((L, rate), s')) :
    L.bytecode = bc ∧ L.stackLog ≤ 30 ∧ (L.placement memory0).variableCount ≤ 30 ∧
      s'.roots = s.roots := by
  have hroots := (readAnnouncedSizes_roots bc).keeps _ _ _ h
  rw [NativeVm.Math.Layout.readAnnouncedSizes_run] at h
  cases hr : (readScalars (2 + nTables)).run s with
  | none => rw [hr] at h; cases h
  | some p =>
    obtain ⟨a, t1⟩ := p
    rw [hr, Option.bind_some] at h
    have ha : a.size = 8 := NativeRustcVm.Sumcheck.readScalars_size hr
    rw [NativeVm.Math.Layout.tailP_eq bc a ha] at h
    split_ifs at h with hok
    swap
    · cases h
    simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨⟨rfl, -⟩, -⟩ := h
    obtain ⟨-, -, -, -, ⟨-, hlm⟩, -, hsl⟩ := hok
    obtain ⟨-, -, f3, -, -, -, f7, -⟩ :=
      NativeVm.Math.Layout.layoutF_facts bc (NativeVm.Math.Layout.lmA a) (bitLength bc.size - 5) (NativeVm.Math.Layout.rowsA a)
    refine ⟨f3, hsl, ?_, hroots⟩
    have hp := f7 0 (by omega)
    rw [Array.getD_eq_getD_getElem?] at hp
    show ((((NativeVm.Math.Layout.layoutA bc a).placements[0]?).getD none).getD default).variableCount ≤ 30
    rw [show NativeVm.Math.Layout.layoutA bc a = NativeVm.Math.Layout.layoutF bc (NativeVm.Math.Layout.lmA a) (bitLength bc.size - 5)
      (NativeVm.Math.Layout.rowsA a) from rfl, hp]
    simp only [NativeVm.Math.Layout.plF, NativeVm.Math.Layout.slotF, NativeVm.Math.Layout.outF, NativeVm.Math.Layout.kapF]
    simpa using hlm

/-- **Phase 2's commitment** reads one root. -/
theorem commitStack_roots (logN rate : Nat) : GrowsRoots 1 (commitStack logN rate) := by
  unfold commitStack
  refine (GrowsRoots.bind (b := 1) (KeepsRoots.liftOpt _).grows fun config ↦ ?_).mono (by omega)
  split
  · exact KeepsRoots.reject.grows.mono (by omega)
  · exact readCommitment_roots _ _

/-- **Ring switching** reads no root. -/
theorem ringSwitch_roots (point s : Array EW) : KeepsRoots (ringSwitch point s) := by
  unfold ringSwitch; keeps

/-! ## Phases 3 and 5: the claims' counts -/

/-- **The bus** returns four claims. -/
theorem verifyBusBalance_claims (L : LayoutW) : Gives (verifyBusBalance L) (·.claims.size = 4) := by
  unfold verifyBusBalance; gives

/-- **The public input** returns two claims. -/
theorem publicInputPhase_size (L : LayoutW) (P : Vector UInt64 4) :
    Gives (publicInputPhase L P) (·.size = 2) := by
  unfold publicInputPhase; gives

/-! ## Phase 4: the tables' evaluations -/

theorem sumcheck_size (claim : EW) (count : Nat) (eqs : Array (Option EW)) :
    Gives (sumcheck claim count eqs) (fun p ↦ p.1.size = eqs.size) := by
  unfold sumcheck
  rw [← Array.foldlM_toList]
  refine (Gives.foldlM (fun p : Array EW × EW ↦ p.1.size) (fun b a ↦ ?_) eqs.toList _).mono
    fun x hx ↦ by simpa using hx
  exact Gives.bind fun _ ↦ Gives.bind fun _ ↦ Gives.pure (by simp)

theorem le_foldl_max : ∀ (l : List Nat) (acc : Nat),
    acc ≤ l.foldl max acc ∧ ∀ x ∈ l, x ≤ l.foldl max acc
  | [], acc => ⟨le_rfl, fun _ h ↦ absurd h (by simp)⟩
  | a :: l, acc => by
    obtain ⟨h1, h2⟩ := le_foldl_max l (max acc a)
    refine ⟨le_trans (Nat.le_max_left _ _) h1, fun x hx ↦ ?_⟩
    rcases List.mem_cons.mp hx with rfl | hx
    · exact le_trans (Nat.le_max_right _ _) h1
    · exact h2 x hx

/-- One table's row of `tableTerms`: its point's first `height` coordinates and `width`
evaluations, after the earlier rows. -/
theorem tableTerms_fold (cp fp point : Array EW) :
    ∀ (l : List (TableW × Nat × Array FormW × EW)) (acc : Nat × EW × Array (Array EW × Array EW)),
    Gives (l.foldlM (tableTermsStep cp fp point) acc) (fun r ↦
      r.2.2.size = acc.2.2.size + l.length ∧
      (∀ i (h : i < acc.2.2.size), r.2.2[i]? = some acc.2.2[i]) ∧
      ∀ j (h : j < l.length), ∃ e : Array EW,
        r.2.2[acc.2.2.size + j]? = some (point.extract 0 l[j].2.1, e) ∧ e.size = l[j].1.width)
  | [], acc => Gives.pure ⟨by simp, fun i h ↦ by simp [h], fun j h ↦ absurd h (by simp)⟩
  | a :: l, acc => by
    obtain ⟨cursor, final, out⟩ := acc
    obtain ⟨table, height, forms, weight⟩ := a
    rw [List.foldlM_cons, NativeVm.Math.Tables.tableTermsStep_eq]
    refine ((readScalars_gives table.width).bind' fun ev hev ↦
      Gives.pure (P := fun (acc' : Nat × EW × Array (Array EW × Array EW)) ↦
      ∃ e : Array EW, acc'.2.2 = out.push (point.extract 0 height, e) ∧ e.size = table.width)
      ⟨ev, rfl, hev⟩).bind' fun (acc' : Nat × EW × Array (Array EW × Array EW)) ⟨e, he, hes⟩ ↦
      (tableTerms_fold cp fp point l acc').mono
      fun r ⟨h1, h2, h3⟩ ↦ ?_
    simp only [he, Array.size_push] at h1 h2 h3
    dsimp only
    refine ⟨by simp only [List.length_cons]; omega, fun i hi ↦ ?_, fun j hj ↦ ?_⟩
    · rw [h2 i (by omega), Array.getElem_push_lt hi]
    · rcases j with _ | j
      · refine ⟨e, ?_, hes⟩
        rw [Nat.add_zero, h2 out.size (by omega), Array.getElem_push_eq]
        rfl
      · obtain ⟨e', h, h'⟩ := h3 j (by simp only [List.length_cons] at hj; omega)
        exact ⟨e', by rw [show out.size + (j + 1) = out.size + 1 + j by omega, h]; rfl, h'⟩

/-- **The table sumcheck's evaluations**: six tables, table `t`'s `widths[t]` evaluations at its
point's first `heights[t]` coordinates. -/
theorem tableSumcheck_shape (heights : Array Nat) (forms : Array (Array FormW))
    (cp fp eqp : Array EW) (target : EW) (hh : heights.size = 6) (hf : forms.size = 6) :
    Gives (tableSumcheck heights forms cp fp eqp target) (fun ev ↦ ev.size = 6 ∧
      ∀ t < 6, (ev.getD t (#[], #[])).2.size = NativeVm.Math.Tables.widths.getD t 0 ∧
        (ev.getD t (#[], #[])).1.size = heights.getD t 0) := by
  unfold tableSumcheck
  refine (sumcheck_size _ _ _).bind' fun ⟨ch, claim⟩ hch ↦ ?_
  simp only [Array.size_replicate] at hch
  have hw : (tableWeights heights eqp ch.reverse).size = 6 := by rw [NativeVm.Math.Tables.tableWeights_size, hh]
  have hl := NativeVm.Math.Tables.rows_length hh hf hw
  dsimp only
  rw [NativeVm.Math.Tables.tableTerms_eq, bind_assoc]
  refine (tableTerms_fold cp fp ch.reverse _ (0, 0, #[])).bind' fun r ⟨h1, _, h3⟩ ↦ ?_
  refine Gives.bind' (Gives.pure (P := fun p ↦ p = (r.2.1, r.2.2)) rfl) fun p hp ↦ ?_
  subst hp
  refine Gives.bind fun _ ↦ Gives.pure ⟨by rw [h1, hl]; rfl, fun t ht ↦ ?_⟩
  obtain ⟨e, he, hes⟩ := h3 t (by rw [hl]; exact ht)
  rw [NativeVm.Math.Tables.rows_get hh hf hw] at he hes
  simp only [Array.size_empty, Nat.zero_add] at he
  rw [Array.getD_eq_getD_getElem?, he, Option.getD_some]
  refine ⟨by rw [hes, NativeVm.Math.Tables.tablesW_width ht], ?_⟩
  simp only [Array.size_extract, Array.size_reverse]
  have hle := (le_foldl_max heights.toList 0).2 (heights.getD t 0) (by
    rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem (by omega), Option.getD_some]
    exact Array.getElem_mem_toList _)
  rw [Array.foldl_toList] at hle
  omega

/-- **Phase 4's evaluations**: six tables, table `t`'s `widths[t]` evaluations at its point's
first `heights[t]` coordinates. -/
theorem tablePhase_shape {L : LayoutW} {bus : BusResultW} (hh : L.tableLogHeights.size = 6)
    (hf : bus.forms.size = 6) {s s' : TState} {ev : Array (Array EW × Array EW)}
    (h : (tablePhase L bus).run s = some (ev, s')) :
    ev.size = 6 ∧ ∀ t < 6, (ev.getD t (#[], #[])).2.size = NativeVm.Math.Tables.widths.getD t 0 ∧
      (ev.getD t (#[], #[])).1.size = L.tableLogHeights.getD t 0 := by
  rw [NativeVm.Math.Tables.tablePhase_eq] at h
  exact (Gives.bind fun _ ↦ tableSumcheck_shape _ _ _ _ _ _ hh hf).gives _ _ _ h

/-- The tables' column claims of evaluations as phase 4 returns them: `153`. -/
theorem tableColumnClaims_size {ev : Array (Array EW × Array EW)} (hev : ev.size = 6)
    (hwid : ∀ t < 6, (ev.getD t (#[], #[])).2.size = NativeVm.Math.Tables.widths.getD t 0) :
    (tableColumnClaims ev).size = 153 :=
  NativeVm.Math.Tables.tableColumnClaims_size hev hwid

theorem keccakOut_le : keccakOut + 25 ≤ NativeVm.Math.Tables.widths.getD opKeccak 0 := by decide

end

end NativeRustcVm.Top
