/-
  LeanVM.Guest.B1.Opening.QueriesFlatC

  Blocks of atoms, `match`es of atom arms and calls: their relation, statement by statement, and
  `mul_range` loops whose body calls.
-/

module

public import LeanVM.Guest.B1.Opening.QueriesFlat

/-!
# Flat blocks with calls

A query of `opening_queries` calls `walk_path` (a function of its own, lean_ethereum.py:1302-1337)
instead of walking its path inline. `FlatC ss`: every statement is an atom, a `match` of atom arms or
a call. `holdsList_flatC`: such a block holds exactly when every statement does (`StmtOkC C`: a call
holds in the call relation `C`), then `next`. `blockOkC_relN`: a block holding under the program's
relation holds at a finite depth. `loop_iffC`, `guarded_loop_iffC`: `loop_iff`, `guarded_loop_iff`
for a loop whose body's meaning reads the call relation (monotone, reached at a finite depth).
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

/-- Every statement is an atom, a `match` of atom arms, or a call. -/
def FlatC (ss : List Stmt) : Prop :=
  ∀ s ∈ ss, (∃ a, s = .atom a) ∨ (∃ x arms, s = .match_ x arms ∧ ∀ arm ∈ arms, AllAtoms arm) ∨
    ∃ f args rets, s = .call f args rets

/-- What a statement of a flat block with calls asks of a valuation. -/
def StmtOkC (C : CallRel) (rd : Reader) (σ : Val) : Stmt → Prop
  | .atom a => a.Holds rd σ
  | .match_ x arms => StmtOk rd σ (.match_ x arms)
  | .call f args rets => C f (args.map σ) (rets.map σ)
  | _ => False

/-- The statements of a block hold, statement by statement, calls in `C`. -/
def BlockOkC (C : CallRel) (rd : Reader) (σ : Val) (ss : List Stmt) : Prop := ∀ s ∈ ss, StmtOkC C rd σ s

variable {C : CallRel} {rd : Reader} {σ : Val}

theorem flatC_of_flat {ss : List Stmt} (h : Flat ss) : FlatC ss := fun s hs ↦
  (h s hs).elim Or.inl fun h' ↦ Or.inr (Or.inl h')

theorem flatC_append {ss ts : List Stmt} (h1 : FlatC ss) (h2 : FlatC ts) : FlatC (ss ++ ts) :=
  fun s hs ↦ (List.mem_append.mp hs).elim (h1 s) (h2 s)

theorem flatC_call (f : String) (args rets : List V) : FlatC [.call f args rets] := fun s hs ↦ by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
  exact Or.inr (Or.inr ⟨f, args, rets, hs⟩)

theorem flatC_cons {s : Stmt} {ss : List Stmt} (h : FlatC (s :: ss)) : FlatC ss :=
  fun t ht ↦ h t (List.mem_cons_of_mem _ ht)

theorem blockOkC_cons {s : Stmt} {ss : List Stmt} :
    BlockOkC C rd σ (s :: ss) ↔ StmtOkC C rd σ s ∧ BlockOkC C rd σ ss := by
  simp [BlockOkC]

/-- **A flat block with calls holds exactly when each of its statements does.** -/
theorem holdsList_flatC : ∀ {ss : List Stmt}, FlatC ss →
    ∀ (next : Prop) (kret : List E → Prop),
      (Stmt.HoldsList C rd σ ss next kret ↔ BlockOkC C rd σ ss ∧ next)
  | [], _, _, _ => by simp [Stmt.HoldsList, BlockOkC]
  | s :: ss, h, next, kret => by
    have ih : Stmt.HoldsList C rd σ ss next kret ↔ BlockOkC C rd σ ss ∧ next :=
      holdsList_flatC (flatC_cons h) next kret
    rw [blockOkC_cons]
    rcases h s (by simp) with ⟨a, rfl⟩ | ⟨x, arms, rfl, harms⟩ | ⟨f, args, rets, rfl⟩
    · simp only [Stmt.HoldsList, Stmt.Holds, ih, StmtOkC]
      tauto
    · simp only [Stmt.HoldsList, Stmt.Holds, holdsArms_iff, Nat.zero_add, StmtOkC, StmtOk]
      constructor
      · rintro ⟨j, hj, hx, ha⟩
        rw [holdsList_atoms (harms _ (List.getElem_mem hj)), ih] at ha
        exact ⟨⟨⟨j, hj, hx, ha.1⟩, ha.2.1⟩, ha.2.2⟩
      · rintro ⟨⟨⟨j, hj, hx, ha⟩, hss⟩, hn⟩
        refine ⟨j, hj, hx, ?_⟩
        rw [holdsList_atoms (harms _ (List.getElem_mem hj)), ih]
        exact ⟨ha, hss, hn⟩
    · simp only [Stmt.HoldsList, Stmt.Holds, ih, StmtOkC]
      tauto

theorem blockOkC_of_blockOk {ss : List Stmt} (h : BlockOk rd σ ss) : BlockOkC C rd σ ss :=
  fun s hs ↦ by
    have := h s hs
    match s, this with
    | .atom _, h => exact h
    | .match_ _ _, h => exact h

theorem BlockOkC.blockOk {ss : List Stmt} (h : BlockOkC C rd σ ss) (hF : Flat ss) : BlockOk rd σ ss :=
  fun s hs ↦ by
    have := h s hs
    rcases hF s hs with ⟨a, rfl⟩ | ⟨x, arms, rfl, -⟩
    · exact this
    · exact this

theorem BlockOkC.mono {ss ts : List Stmt} (h : BlockOkC C rd σ ts) (hs : ∀ s ∈ ss, s ∈ ts) :
    BlockOkC C rd σ ss := fun s hs' ↦ h s (hs s hs')

theorem BlockOkC.atom {ss : List Stmt} (h : BlockOkC C rd σ ss) {a : Atom} (ha : Stmt.atom a ∈ ss) :
    a.Holds rd σ := h _ ha

theorem BlockOkC.call {ss : List Stmt} (h : BlockOkC C rd σ ss) {f : String} {args rets : List V}
    (ha : Stmt.call f args rets ∈ ss) : C f (args.map σ) (rets.map σ) := h _ ha

theorem blockOkC_append {ss ts : List Stmt} :
    BlockOkC C rd σ (ss ++ ts) ↔ BlockOkC C rd σ ss ∧ BlockOkC C rd σ ts := by
  simp only [BlockOkC, List.mem_append]
  exact ⟨fun h ↦ ⟨fun s hs ↦ h s (Or.inl hs), fun s hs ↦ h s (Or.inr hs)⟩,
    fun h s hs ↦ hs.elim (h.1 s) (h.2 s)⟩

theorem stmtOkC_mono {C C' : CallRel} (hC : CallRel.Le C C') :
    ∀ s : Stmt, StmtOkC C rd σ s → StmtOkC C' rd σ s
  | .atom _, h => h
  | .match_ _ _, h => h
  | .call _ _ _, h => hC _ _ _ h

theorem BlockOkC.monoC {C C' : CallRel} (hC : CallRel.Le C C') {ss : List Stmt}
    (h : BlockOkC C rd σ ss) : BlockOkC C' rd σ ss := fun s hs ↦ stmtOkC_mono hC s (h s hs)

/-- **A block holding under the program's relation holds at a finite depth.** -/
theorem blockOkC_relN (P : Core.Program) : ∀ {ss : List Stmt},
    BlockOkC (P.Rel rd) rd σ ss → ∃ D, BlockOkC (P.relN rd D) rd σ ss
  | [], _ => ⟨0, fun _ h ↦ absurd h (by simp)⟩
  | s :: ss, h => by
    obtain ⟨D, hD⟩ := blockOkC_relN P (ss := ss) (h.mono fun t ht ↦ List.mem_cons_of_mem _ ht)
    have hs := h s (by simp)
    have key : ∃ d, StmtOkC (P.relN rd d) rd σ s := by
      match s, hs with
      | .atom _, h => exact ⟨0, h⟩
      | .match_ _ _, h => exact ⟨0, h⟩
      | .call _ _ _, ⟨d, hd⟩ => exact ⟨d, hd⟩
    obtain ⟨d, hd⟩ := key
    refine ⟨max D d, fun t ht ↦ ?_⟩
    rcases List.mem_cons.mp ht with rfl | ht
    · exact stmtOkC_mono (relN_mono P (le_max_right D d)) _ hd
    · exact stmtOkC_mono (relN_mono P (le_max_left D d)) _ (hD t ht)

/-- The meaning of a flat loop body with calls at the arguments `args`. -/
def FlatBodyC (C : CallRel) (rd : Reader) (params : List V) (A : List Stmt) (args : List E) : Prop :=
  ∃ σ : Val, params.map σ = args ∧ BlockOkC C rd σ A

theorem FlatBodyC.monoC {C C' : CallRel} (hC : CallRel.Le C C') {params : List V} {A : List Stmt}
    {args : List E} (h : FlatBodyC C rd params A args) : FlatBodyC C' rd params A args :=
  let ⟨σ, hp, hA⟩ := h; ⟨σ, hp, hA.monoC hC⟩

/-- **A `mul_range` loop whose body calls** (`loop_iff` with the body's meaning `B C x` read in
the call relation `C`, monotone in it and reached at a finite depth). -/
theorem loop_iffC {P : Core.Program} {f : String} {ps : List E} {N : E}
    {B : CallRel → E → Prop}
    (hmono : ∀ {C C' : CallRel} {x : E}, CallRel.Le C C' → B C x → B C' x)
    (hfin : ∀ {x : E}, B (P.Rel rd) x → ∃ D, B (P.relN rd D) x)
    (hstep : ∀ d x, P.relN rd (d + 1) f (x :: ps) [] ↔
      B (P.relN rd d) x ∧ IsInK (x * gen + N) ∧ (x * gen + N ≠ 0 → P.relN rd d f (x * gen :: ps) []))
    (k : ℕ) :
    P.Rel rd f (gen ^ k :: ps) [] ↔
      ∃ m, k < m ∧ N = gen ^ m ∧ (∀ j, k < j → j < m → gen ^ j ≠ N) ∧
        ∀ j, k ≤ j → j < m → B (P.Rel rd) (gen ^ j) := by
  constructor
  · rintro ⟨d, hd⟩
    induction d generalizing k with
    | zero => exact hd.elim
    | succ d ih =>
      obtain ⟨hB, -, hnext⟩ := (hstep d _).mp hd
      have hB' := hmono (relN_le_rel P d) hB
      by_cases h0 : gen ^ k * gen + N = 0
      · refine ⟨k + 1, by omega, (gen_pow_add_eq_zero_iff k).mp h0, fun j h1 h2 => by omega,
          fun j h1 h2 => ?_⟩
        rwa [show j = k by omega]
      · have := hnext h0
        rw [gen_pow_mul_gen] at this
        obtain ⟨m, hm, hN, hfirst, hall⟩ := ih (k + 1) this
        refine ⟨m, by omega, hN, fun j h1 h2 => ?_, fun j h1 h2 => ?_⟩
        · rcases Nat.lt_or_ge (k + 1) j with h | h
          · exact hfirst j h h2
          · rw [show j = k + 1 by omega]
            intro he
            exact h0 ((gen_pow_add_eq_zero_iff k).mpr he.symm)
        · rcases Nat.lt_or_ge k j with h | h
          · exact hall j (by omega) h2
          · rwa [show j = k by omega]
  · rintro ⟨m, hkm, hN, hfirst, hall⟩
    obtain ⟨t, rfl⟩ : ∃ t, m = k + 1 + t := ⟨m - k - 1, by omega⟩
    have hK : ∀ j, IsInK (gen ^ j * gen + N) := fun j => by
      rw [hN]; exact isInK_add (isInK_mul (gen_pow_isInK j) (by simpa using gen_pow_isInK 1)) (gen_pow_isInK _)
    suffices h : ∃ d, P.relN rd d f (gen ^ k :: ps) [] from h
    induction t generalizing k with
    | zero =>
      obtain ⟨D, hD⟩ := hfin (hall k le_rfl (by omega))
      exact ⟨D + 1, (hstep D _).mpr ⟨hD, hK k,
        fun h => absurd ((gen_pow_add_eq_zero_iff k).mpr hN) h⟩⟩
    | succ t ih =>
      obtain ⟨D, hD⟩ := hfin (hall k le_rfl (by omega))
      obtain ⟨d', hd'⟩ := ih (k + 1) (by omega) (by rw [hN]; congr 1; omega)
        (fun j h1 h2 => hfirst j (by omega) (by omega)) (fun j h1 h2 => hall j (by omega) (by omega))
      refine ⟨max D d' + 1, (hstep (max D d') _).mpr ⟨hmono (relN_mono P (le_max_left D d')) hD,
        hK k, fun _ => ?_⟩⟩
      rw [gen_pow_mul_gen]
      exact relN_mono P (le_max_right D d') _ _ _ hd'

/-- **A guarded `mul_range` loop whose body calls** (`guarded_loop_iff` for `loop_iffC`). -/
theorem guarded_loop_iffC {P : Core.Program} {f : String} {ps : List E} {N : E}
    {B : CallRel → E → Prop}
    (hmono : ∀ {C C' : CallRel} {x : E}, CallRel.Le C C' → B C x → B C' x)
    (hfin : ∀ {x : E}, B (P.Rel rd) x → ∃ D, B (P.relN rd D) x)
    (hstep : ∀ d x, P.relN rd (d + 1) f (x :: ps) [] ↔
      B (P.relN rd d) x ∧ IsInK (x * gen + N) ∧ (x * gen + N ≠ 0 → P.relN rd d f (x * gen :: ps) [])) :
    (IsInK (1 + N) ∧ (1 + N ≠ 0 → P.Rel rd f (1 :: ps) [])) ↔
      ∃ m < ordG, N = gen ^ m ∧ ∀ j < m, B (P.Rel rd) (gen ^ j) := by
  have hl := loop_iffC (B := B) (fun h hb ↦ hmono h hb) (fun hb ↦ hfin hb) hstep 0
  rw [pow_zero] at hl
  constructor
  · rintro ⟨hK, hrun⟩
    by_cases h1 : 1 + N = 0
    · refine ⟨0, by decide, ?_, fun j hj => absurd hj (Nat.not_lt_zero j)⟩
      rw [pow_zero]; exact (e_add_eq_zero_iff.mp h1).symm
    · obtain ⟨m, hm, hN, hfirst, hall⟩ := hl.mp (hrun h1)
      refine ⟨m, ?_, hN, fun j hj => hall j (Nat.zero_le j) hj⟩
      by_contra hge
      rcases Nat.lt_or_ge ordG m with hgt | hle
      · have : gen ^ (m - ordG) = N := by
          obtain ⟨t, rfl⟩ : ∃ t, m = ordG + t := ⟨m - ordG, by omega⟩
          rw [hN, pow_add, gen_pow_ordG, one_mul, Nat.add_sub_cancel_left]
        exact hfirst (m - ordG) (Nat.sub_pos_of_lt hgt) (Nat.sub_lt (by omega) ordG_pos) this
      · have hm' : m = ordG := by omega
        rw [hm', gen_pow_ordG] at hN
        exact h1 (by rw [hN]; exact e_add_self 1)
  · rintro ⟨m, hm, hN, hall⟩
    refine ⟨?_, fun h1 => ?_⟩
    · rw [hN]
      exact isInK_add (by rw [← pow_zero gen]; exact gen_pow_isInK 0) (gen_pow_isInK m)
    have hm0 : 0 < m := by
      rcases Nat.eq_zero_or_pos m with h | h
      · exact absurd (show 1 + N = 0 by rw [hN, h, pow_zero]; exact e_add_self 1) h1
      · exact h
    exact hl.mpr ⟨m, hm0, hN, first_hit_of_lt hm hN, fun j _ hj => hall j hj⟩

end
end LeanVM.Guest.B1
