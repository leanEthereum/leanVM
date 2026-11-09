/-
  LeanVM.Guest.B1.Digest.StatementComplete

  `statement_digest`, completely: its meaning gives its core IR relation.
-/

module

public import LeanVM.Guest.B1.Digest.StatementChk
public import LeanVM.Guest.B1.Digest.PairComplete
public import LeanVM.Guest.B1.Digest.Steps
public import LeanVM.Guest.B1.Digest.Chain

/-!
# `statement_digest`, completely

The honest valuation is the template evaluated on the arguments (`Fwd.ev`, its checks in
`StatementChk`): the pairs' loads (`pair_holds`) hold on the words the meaning reads, the `KECCAK`
inputs are canonical (the header cells by the meaning, the pairs' cells packed, the constants), so every atom holds (`Fwd.atoms_holds`). The relation then holds at the
valuation's returns, which soundness makes the meaning's digest; the meaning's words are the
memory's, so its returns are these.
-/

namespace LeanVM.Guest.B1.Digest

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Value.Keccak
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Guest.B1.Fwd

@[expose] public section

theorem mem_sd_pair {p : ℕ} (hp : p < 12) {a : Atom} (ha : a ∈ pairAtoms (.n 8) (2 * p) (17 + 27 * p)) :
    a ∈ sdAtoms := by
  unfold sdAtoms
  refine List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _
    (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ ?_)))))
  exact List.mem_flatMap.mpr ⟨p, List.mem_range.mpr hp, ha⟩

theorem mem_sd_hdr {a : Atom} (ha : a ∈ sdHdr) : a ∈ sdAtoms := by
  unfold sdAtoms
  exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _
    (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ ha)))))

theorem mem_sd_const {a : Atom} (ha : a ∈ sdConsts) : a ∈ sdAtoms := by
  unfold sdAtoms
  exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _
    (List.mem_append_left _ (List.mem_append_right _ ha))))

theorem mem_sd_blk5 {a : Atom} (ha : a ∈ sdBlk5) : a ∈ sdAtoms := by
  unfold sdAtoms
  exact List.mem_append_left _ (List.mem_append_right _ ha)

/-- The meaning's words are the memory's: its returns are determined. -/
theorem statement_digest_unique {rd : Reader} {args r r' : List E}
    (h : MeaningStatementDigest rd args r) (h' : MeaningStatementDigest rd args r') : r = r' := by
  match args, h, h' with
  | [s0, s1, x0, x1, y0, y1, a0, a1, dp], h, h' =>
    obtain ⟨cells, hlen, hreads, -, hr⟩ := h
    obtain ⟨cells', hlen', hreads', -, hr'⟩ := h'
    have hc : cells' = cells := by
      rw [readsAt_memRun hreads, readsAt_memRun hreads', hlen, hlen']
    rw [hr, hr', hc]

set_option maxRecDepth 10000 in
/-- **`statement_digest` is complete.** -/
theorem statement_digest_complete : statement_digest_complete_Spec := by
  intro rd args rets h
  match args, h with
  | [s0, s1, x0, x1, y0, y1, a0, a1, dp], h =>
    have hM := h
    obtain ⟨cells, hlen, hreads, hcan, -⟩ := h
    let args : List E := [s0, s1, x0, x1, y0, y1, a0, a1, dp]
    let σ : Val := B1.Val.ofArgs (ev rd (fun _ => 0) args sdBody)
    obtain ⟨-, -, hgs⟩ := ev_spec rd (fun _ => 0) sdBody args sd_chk
    rw [show args.length = 9 from rfl, sd_stores] at hgs
    have hg : ∀ a ∈ sdAtoms, Good rd [] (fun _ => 0) σ a := fun a ha =>
      hgs (.atom a) (List.mem_append_left _ (List.mem_map_of_mem ha))
    have hpar : ∀ i < 9, σ (.n i) = args.getD i 0 := fun i hi => ev_params rd _ (l := args) sd_chk hi
    have e8 : σ (.n 8) = dp := hpar 8 (by omega)
    have hl24 : cells.length = 24 := hlen
    -- the pairs
    have hP : ∀ p < 12, ∀ a ∈ pairAtoms (.n 8) (2 * p) (17 + 27 * p), a.Holds rd σ := by
      intro p hp
      refine pair_holds (fun a ha => hg a (mem_sd_pair hp ha)) (fun a ha => absurd ha (by simp))
        (s := cells[2 * p]'(by omega)) (t := cells[2 * p + 1]'(by omega)) ?_ ?_
      · rw [e8]; exact hreads _ _
      · rw [e8]; exact hreads _ _
    -- the header
    have g := fun a (ha : a ∈ sdHdr) => hg a (mem_sd_hdr ha)
    simp only [sdHdr, List.forall_mem_cons, List.not_mem_nil, IsEmpty.forall_iff,
      implies_true, and_true] at g
    obtain ⟨g9, g10, g11, g12, g13, g14, g15, g16⟩ := g
    simp only [Good] at g9 g10 g11 g12 g13 g14 g15 g16
    -- the canonical values
    have hA : ∀ i ∈ sdA, IsCanonical128 (σ (.n i)) := by
      have hc := fun x (hx : x ∈ [s0, s1, x0, x1, y0, y1, a0, a1]) => hcan x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hc
      obtain ⟨c0, c1, c2, c3, c4, c5, c6, c7⟩ := hc
      have gc := fun a (ha : a ∈ sdConsts) => hg a (mem_sd_const ha)
      simp only [sdConsts, List.forall_mem_cons, List.not_mem_nil, IsEmpty.forall_iff,
        implies_true, and_true, Good] at gc
      obtain ⟨k341, k342, k343, k344, k345⟩ := gc
      have g5 := fun a (ha : a ∈ sdBlk5) => hg a (mem_sd_blk5 ha)
      simp only [sdBlk5, List.forall_mem_cons, List.not_mem_nil,
        IsEmpty.forall_iff, implies_true, and_true, Good] at g5
      obtain ⟨-, -, -, k450, -, -⟩ := g5
      intro i hi
      simp only [sdA, List.mem_append] at hi
      rcases hi with (hi | hi) | hi
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
        rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
        · rw [g9, hpar 0 (by omega)]; exact c0
        · rw [g10, hpar 1 (by omega)]; exact c1
        · rw [g11, hpar 2 (by omega)]; exact c2
        · rw [g12, hpar 3 (by omega)]; exact c3
        · rw [g13, hpar 4 (by omega)]; exact c4
        · rw [g14, hpar 5 (by omega)]; exact c5
        · rw [g15, hpar 6 (by omega)]; exact c6
        · rw [g16, hpar 7 (by omega)]; exact c7
      · obtain ⟨p, hp, hi⟩ := List.mem_flatMap.mp hi
        obtain ⟨-, -, hc3⟩ := pair_fwd (hP p (List.mem_range.mp hp))
        have hm : σ (.n i) ∈ [σ (.n (17 + 27 * p + 8)), σ (.n (17 + 27 * p + 17)),
            σ (.n (17 + 27 * p + 26))] := by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hi ⊢
          rcases hi with rfl | rfl | rfl <;> simp
        rw [hc3] at hm
        exact pairCells_canonical _ _ _ hm
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
        rcases hi with rfl | rfl | rfl | rfl | rfl | rfl
        · rw [k341]; exact isCanonical128_word _ _
        · rw [k342]; exact isCanonical128_word _ _
        · rw [k343]; exact isCanonical128_word _ _
        · rw [k344]; exact isCanonical128_word _ _
        · rw [k345]; exact isCanonical128_word _ _
        · rw [k450]; exact isCanonical128_word _ _
    -- every atom
    have hat : ∀ a ∈ sdAtoms, a.Holds rd σ := by
      refine atoms_holds (fun v => rfl) sd_canon hg hA fun a ha hn => Or.inl ?_
      have hf : a ∈ sdAtoms.filter needsSide := List.mem_filter.mpr ⟨ha, hn⟩
      rw [sd_needs] at hf
      obtain ⟨p, hp, hf⟩ := List.mem_flatMap.mp hf
      exact hP p (List.mem_range.mp hp) a (List.mem_filter.mp hf).1
    -- the relation, and its returns
    have hrel : coreProgram.Rel rd "statement_digest" args [σ (.n 454), σ (.n 455)] := by
      refine (rel_iff_sem find_statement_digest _ _).mpr ⟨σ, ?_, ?_⟩
      · rw [core20_params]
        simp only [List.map_cons, List.map_nil]
        rw [hpar 0 (by omega), hpar 1 (by omega), hpar 2 (by omega), hpar 3 (by omega),
          hpar 4 (by omega), hpar 5 (by omega), hpar 6 (by omega), hpar 7 (by omega),
          hpar 8 (by omega)]
        rfl
      · rw [core20_body, holdsList_atoms_ret]
        exact ⟨hat, rfl⟩
    rw [statement_digest_unique hM (statement_digest_sound rd _ _ hrel)]
    exact hrel
  | [], h => exact h.elim
  | [_], h => exact h.elim
  | [_, _], h => exact h.elim
  | [_, _, _], h => exact h.elim
  | [_, _, _, _], h => exact h.elim
  | [_, _, _, _, _], h => exact h.elim
  | [_, _, _, _, _, _], h => exact h.elim
  | [_, _, _, _, _, _, _], h => exact h.elim
  | [_, _, _, _, _, _, _, _], h => exact h.elim
  | _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _, h => exact h.elim

end
end LeanVM.Guest.B1.Digest
