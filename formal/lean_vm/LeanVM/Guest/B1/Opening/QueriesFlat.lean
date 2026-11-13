/-
  LeanVM.Guest.B1.Opening.QueriesFlat

  Blocks of atoms and `match`es of atom arms: their relation, statement by statement.
-/

module

public import LeanVM.Guest.B1.Common.Loops

/-!
# Flat blocks

A query of `opening_queries` (1a379148) walks its Merkle path by `match`es on window words
(`walk_path`), each arm a run of atoms (`walk_window`). `Flat ss`: every statement is an atom or a
`match` whose arms are atoms only. `holdsList_flat`: such a block holds exactly when every
statement does (`StmtOk`: an atom holds; a `match` on `x` picks an arm `j` with `x = g^j` whose
atoms hold), then `next`. `match_arm_of_gen_pow`: on `x = g^v`, `v` below the arms' count, the arm
picked is `v`.
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

/-- Every statement is an atom, or a `match` of atom arms. -/
def Flat (ss : List Stmt) : Prop :=
  ∀ s ∈ ss, (∃ a, s = .atom a) ∨ ∃ x arms, s = .match_ x arms ∧ ∀ arm ∈ arms, AllAtoms arm

/-- What a statement of a flat block asks of a valuation. -/
def StmtOk (rd : Reader) (σ : Val) : Stmt → Prop
  | .atom a => a.Holds rd σ
  | .match_ x arms => ∃ (j : ℕ) (h : j < arms.length), σ x = ofK (addressOfIndex j) ∧
      ∀ a, Stmt.atom a ∈ arms[j] → a.Holds rd σ
  | _ => False

theorem flat_cons {s : Stmt} {ss : List Stmt} (h : Flat (s :: ss)) : Flat ss :=
  fun t ht ↦ h t (List.mem_cons_of_mem _ ht)

/-- **A flat block holds exactly when each of its statements does.** -/
theorem holdsList_flat {C : CallRel} {rd : Reader} {σ : Val} : ∀ {ss : List Stmt}, Flat ss →
    ∀ (next : Prop) (kret : List E → Prop),
      (Stmt.HoldsList C rd σ ss next kret ↔ (∀ s ∈ ss, StmtOk rd σ s) ∧ next)
  | [], _, _, _ => by simp [Stmt.HoldsList]
  | s :: ss, h, next, kret => by
    have ih := holdsList_flat (C := C) (rd := rd) (σ := σ) (flat_cons h) next kret
    rcases h s (by simp) with ⟨a, rfl⟩ | ⟨x, arms, rfl, harms⟩
    · simp only [Stmt.HoldsList, Stmt.Holds, ih, List.forall_mem_cons, StmtOk]
      tauto
    · simp only [Stmt.HoldsList, Stmt.Holds, holdsArms_iff, Nat.zero_add, List.forall_mem_cons,
        StmtOk]
      constructor
      · rintro ⟨j, hj, hx, ha⟩
        rw [holdsList_atoms (harms _ (List.getElem_mem hj)), ih] at ha
        exact ⟨⟨⟨j, hj, hx, ha.1⟩, ha.2.1⟩, ha.2.2⟩
      · rintro ⟨⟨⟨j, hj, hx, ha⟩, hss⟩, hn⟩
        refine ⟨j, hj, hx, ?_⟩
        rw [holdsList_atoms (harms _ (List.getElem_mem hj)), ih]
        exact ⟨ha, hss, hn⟩

/-- **The arm a `match` picks on `g^v`** is `v`. -/
theorem match_arm_of_gen_pow {x : E} {j v : ℕ} (hj : j < 2 ^ 32) (hv : v < 2 ^ 32)
    (h1 : x = ofK (addressOfIndex j)) (h2 : x = gen ^ v) : j = v := by
  rw [h2, gen_pow_eq_ofK] at h1
  exact (gpow_injOn (by simp only [Set.mem_Iio]; omega) (by simp only [Set.mem_Iio]; omega)
    (ofK_injective h1)).symm

/-- The statements of a block hold, statement by statement. -/
def BlockOk (rd : Reader) (σ : Val) (ss : List Stmt) : Prop := ∀ s ∈ ss, StmtOk rd σ s

theorem BlockOk.atom {rd : Reader} {σ : Val} {ss : List Stmt} (h : BlockOk rd σ ss) {a : Atom}
    (ha : Stmt.atom a ∈ ss) : a.Holds rd σ := h _ ha

theorem BlockOk.mono {rd : Reader} {σ : Val} {ss ts : List Stmt} (h : BlockOk rd σ ts)
    (hs : ∀ s ∈ ss, s ∈ ts) : BlockOk rd σ ss := fun s hs' ↦ h s (hs s hs')

theorem blockOk_append {rd : Reader} {σ : Val} {ss ts : List Stmt} :
    BlockOk rd σ (ss ++ ts) ↔ BlockOk rd σ ss ∧ BlockOk rd σ ts := by
  simp only [BlockOk, List.mem_append]
  exact ⟨fun h ↦ ⟨fun s hs ↦ h s (Or.inl hs), fun s hs ↦ h s (Or.inr hs)⟩,
    fun h s hs ↦ hs.elim (h.1 s) (h.2 s)⟩

theorem blockOk_of_atoms {rd : Reader} {σ : Val} {ss : List Stmt} (hA : AllAtoms ss)
    (h : ∀ a, Stmt.atom a ∈ ss → a.Holds rd σ) : BlockOk rd σ ss := fun s hs ↦ by
  obtain ⟨a, rfl⟩ := hA s hs
  exact h a hs

theorem flat_of_atoms {ss : List Stmt} (h : AllAtoms ss) : Flat ss := fun s hs ↦ Or.inl (h s hs)

theorem flat_append {ss ts : List Stmt} (h1 : Flat ss) (h2 : Flat ts) : Flat (ss ++ ts) :=
  fun s hs ↦ (List.mem_append.mp hs).elim (h1 s) (h2 s)

theorem flat_flatten {bs : List (List Stmt)} (h : ∀ b ∈ bs, Flat b) : Flat bs.flatten := fun s hs ↦ by
  obtain ⟨b, hb, hs⟩ := List.mem_flatten.mp hs
  exact h b hb s hs

theorem flat_map_flatten {α : Type} {xs : List α} {f : α → List Stmt} (h : ∀ x ∈ xs, Flat (f x)) :
    Flat (xs.map f).flatten :=
  flat_flatten fun b hb ↦ by obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hb; exact h x hx

/-- The meaning of a flat loop body at the arguments `args`. -/
def FlatBody (rd : Reader) (params : List V) (A : List Stmt) (args : List E) : Prop :=
  ∃ σ : Val, params.map σ = args ∧ BlockOk rd σ A

/-- **A loop of a flat body** (`loop_step_atoms` with `match`es of atom arms). -/
theorem loop_step_flat {P : Core.Program} {rd : Reader} {f : String} {fn : Fn}
    (hf : P.find? f = some fn) {A : List Stmt} {c : ℕ} {args : List V}
    (hb : fn.body = A ++ [.callIf (.n c) f args, .ret []]) (hA : Flat A)
    {x N : E} {rest : List E}
    (hc : ∀ σ : Val, fn.params.map σ = x :: N :: rest → BlockOk rd σ A →
      σ (.n c) = x * gen + N ∧ args.map σ = x * gen :: N :: rest) (d : ℕ) :
    P.relN rd (d + 1) f (x :: N :: rest) [] ↔
      FlatBody rd fn.params A (x :: N :: rest) ∧ IsInK (x * gen + N) ∧
        (x * gen + N ≠ 0 → P.relN rd d f (x * gen :: N :: rest) []) := by
  rw [relN_succ_iff hf, hb]
  constructor
  · rintro ⟨σ, hp, h⟩
    rw [holdsList_append, holdsList_flat hA] at h
    obtain ⟨hall, hK, hcall, -⟩ := h
    obtain ⟨e1, e2⟩ := hc σ hp hall
    rw [e1] at hK hcall
    rw [e2] at hcall
    exact ⟨⟨σ, hp, hall⟩, hK, hcall⟩
  · rintro ⟨⟨σ, hp, hall⟩, hK, hcall⟩
    obtain ⟨e1, e2⟩ := hc σ hp hall
    refine ⟨σ, hp, ?_⟩
    rw [holdsList_append, holdsList_flat hA]
    refine ⟨hall, ?_, ?_, rfl⟩
    · rw [e1]; exact hK
    · rw [e1, e2]; exact hcall

end
end LeanVM.Guest.B1
