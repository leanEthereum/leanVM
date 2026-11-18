/-
  LeanVM.Guest.CoreMode.PairJumpC

  `PairJump`'s lemmas on what the pairing's normalizations add, over `WrittenC`.
-/

module

public import LeanVM.Guest.CoreMode.PairJump
public import LeanVM.Guest.CoreMode.PairC

/-!
# Normalizations over `WrittenC`

`succ_normC`: a normalization's skipped atoms add nothing to `WrittenC`; `writtenC_noAtom`: neither
does an event that is no atom or call; `writtenC_prefix`: written before, written after more events.
-/

namespace LeanVM.Guest.CoreMode

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Memory LeanVM.Guest.Bridge

@[expose] public section

variable {X : AlignCtx} {H : HCert} {O S : Exec.Trie Unit} {sigOf : String → HSig} {rd : Reader} {σ : Val}
  {ws0 : List E}

theorem writtenC_prefix {l l' : List Ev} {x : K} (h : WrittenC sigOf H rd σ ws0 l x) :
    WrittenC sigOf H rd σ ws0 (l ++ l') x :=
  writtenC_left h

/-- **A normalization's skipped atoms** write nothing: what is written after them was before. -/
theorem succ_normC {z0 c : Zip} (hn : (PairCtx.ofH X H O S).nL z0 = some c) {es : List Ev} {vs : List V}
    (hp : walk σ z0.pos = .ret es vs) :
    ∃ evs es', es = evs ++ es' ∧ walk σ c.pos = .ret es' vs ∧ (∀ e ∈ evs, EvM sigOf rd σ e) ∧
      ∀ pre x, WrittenC sigOf H rd σ ws0 (pre ++ evs) x → WrittenC sigOf H rd σ ws0 pre x := by
  obtain ⟨as, has, hpos, -⟩ := normG_pos _ _ hn
  rw [hpos] at hp
  obtain ⟨es', hes', rfl⟩ := walk_atoms_ret hp
  refine ⟨as.map Ev.atom, es', rfl, hes', evM_atoms _, fun pre x hx ↦ ?_⟩
  rcases writtenC_append hx with h | ⟨e, he, hw⟩
  · exact h
  · obtain ⟨b, hb, rfl⟩ := List.mem_map.mp he
    exact absurd hw (no_writes_of_stopL (has b hb))

/-- An event that is no atom and no call adds nothing to `WrittenC`. -/
theorem writtenC_noAtom {e : Ev} (he : ∀ a, e ≠ .atom a) (hc : ∀ f a r, e ≠ .call f a r) {pre : List Ev} {x : K}
    (h : WrittenC sigOf H rd σ ws0 (pre ++ [e]) x) : WrittenC sigOf H rd σ ws0 pre x := by
  rcases writtenC_append h with h | ⟨e', he', hw⟩
  · exact h
  · rw [List.mem_singleton] at he'
    rw [he'] at hw
    cases e with
    | atom a => exact absurd rfl (he a)
    | call f a r => exact absurd rfl (hc f a r)
    | _ => exact hw.elim

end

end LeanVM.Guest.CoreMode
