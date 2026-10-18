/-
  LeanVM.Guest.B1.Sig.XmssPrologue

  The prologue of `verify_lean_xmss` (G:2390-2400): the public parameter loaded, the leaf index's
  bits hinted and pinned Boolean, its shifts, the powers `g^s`.
-/

module

public import LeanVM.Guest.B1.Sig.Steps

namespace LeanVM.Guest.B1.Sig

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.Verifier
open LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Value

@[expose] public section

variable {C : CallRel} {rd : Reader}

/-- What the prologue leaves for the leaf index `L`. -/
structure XPre (σ : Val) (L : Nat) : Prop where
  md : σ (.n 2) = mdw 64 true
  lt : L < 2 ^ 32
  bits : ∀ j < 32, σ (.n (3 + j)) = bitE (L.testBit j)
  nodes : ∀ l < 32, σ (.n (128 - 3 * l)) = eOfNat (L / 2 ^ l)
  pow : ∀ s < 10, σ (.n (129 + s)) = gen ^ s

theorem XPre.congr {σ σ' : Val} {L : Nat} (h : XPre σ L) (hag : AgreeBelow 139 σ σ') : XPre σ' L :=
  ⟨(hag 2 (by omega)).symm.trans h.md, h.lt, fun j hj => (hag _ (by omega)).symm.trans (h.bits j hj),
    fun l hl => (hag _ (by omega)).symm.trans (h.nodes l hl), fun s hs => (hag _ (by omega)).symm.trans (h.pow s hs)⟩

theorem xPrologue_eq : xPrologue = .atom (.load (.n 1) (.n 0) 1) :: cst 2 (mdw 64 true) ::
    hintW "leaf_index_bits" ((List.range 32).map fun j => .n (3 + j)) ::
    (booleans 3 32 ++ (shifts 3 32 35 ++ powers 129)) := by
  simp only [xPrologue, List.append_assoc, List.cons_append, List.nil_append]

theorem nodes_of_shifts {σ : Val} {L : Nat} (h : ∀ r < 32, σ (.n (35 + 3 * r)) = eOfNat (L / 2 ^ (32 - 1 - r))) :
    ∀ l < 32, σ (.n (128 - 3 * l)) = eOfNat (L / 2 ^ l) := fun l hl => by
  have := h (31 - l) (by omega)
  rwa [show 35 + 3 * (31 - l) = 128 - 3 * l by omega, show 32 - 1 - (31 - l) = l by omega] at this

/-- **The prologue is sound.** -/
theorem xPrologue_sound {σ : Val} {next : Prop} {kret : List E → Prop}
    (h : Stmt.HoldsList C rd σ xPrologue next kret) :
    LoadHolds rd (σ (.n 0)) 1 (σ (.n 1)) ∧ (∃ L, XPre σ L) ∧ next := by
  rw [xPrologue_eq, holdsList_cons_atom, cst, holdsList_cons_atom, hintW, holds_hint_cons, holdsList_append,
    booleans_iff, holdsList_append] at h
  obtain ⟨hl, hmd, hbool, h⟩ := h
  set f : Nat → Bool := fun j => decide (σ (.n (3 + j)) = 1)
  set L := bitsVal f 32
  have hL : L < 2 ^ 32 := bitsVal_lt f 32
  have hbits : ∀ j < 32, σ (.n (3 + j)) = bitE (L.testBit j) := fun j hj => by
    rw [testBit_bitsVal, decide_eq_true hj, Bool.true_and]
    exact bitE_of_mul_self (hbool j hj)
  obtain ⟨hsh, h⟩ := shifts_sound (by omega) (by omega) hL hbits h
  obtain ⟨hpow, hn⟩ := (powers_iff 129).mp h
  exact ⟨hl, ⟨L, hmd, hL, hbits, nodes_of_shifts hsh, hpow⟩, hn⟩

theorem upds_append (σ : Val) (l1 l2 : List (Nat × E)) : upds σ (l1 ++ l2) = upds (upds σ l2) l1 := by
  induction l1 with
  | nil => rfl
  | cons p l1 ih => obtain ⟨k, e⟩ := p; simp only [List.cons_append, upds, ih]

theorem upds_range_at (b : Nat) (f : Nat → E) :
    ∀ (n : Nat) (σ : Val), ∀ j < n, upds σ ((List.range n).map fun j => (b + j, f j)) (.n (b + j)) = f j
  | 0, _, _, h => absurd h (by omega)
  | n + 1, σ, j, hj => by
      rw [List.range_succ, List.map_append, upds_append]
      rcases Nat.lt_or_eq_of_le (Nat.lt_succ_iff.mp hj) with hj | rfl
      · exact upds_range_at b f n _ j hj
      · rw [upds_of_not_mem]
        · simp [upds]
        · intro p hp
          simp only [List.mem_map, List.mem_range] at hp
          obtain ⟨i, hi, rfl⟩ := hp
          simp only [ne_eq, V.mk.injEq, true_and]
          omega

theorem shifts_below : NumBelow 129 (Stmt.valsList (shifts 3 32 35)) := by
  have := shifts_eq 3 32 35
  exact (show NumBelow 129 _ from fun v hv => by
      rw [this] at hv
      simp only [valsList_cons, Stmt.vals, Atom.vals, List.cons_append, List.nil_append, List.mem_cons] at hv
      rcases hv with rfl | rfl | hv
      · exact ⟨35, by omega, rfl⟩
      · exact ⟨34, by omega, rfl⟩
      · exact numBelow_valsList_flatMap _ _ (fun j hj => by
          simp only [List.mem_range] at hj
          simp only [shiftBlock, cst, addS, mulS, valsList_cons, valsList_nil, Stmt.vals, Atom.vals,
            List.cons_append, List.nil_append, List.append_nil]
          exact .cons ⟨_, by omega, rfl⟩ (.cons ⟨_, by omega, rfl⟩ (.cons ⟨_, by omega, rfl⟩
            (.cons ⟨_, by omega, rfl⟩ (.cons ⟨_, by omega, rfl⟩ (.cons ⟨_, by omega, rfl⟩
            (.cons ⟨_, by omega, rfl⟩ (.nil _)))))))) v hv)

theorem xPrologue_below : NumBelow 139 (Stmt.valsList xPrologue) := by
  rw [xPrologue_eq]
  simp only [cst, hintW, valsList_cons, Stmt.vals, Atom.vals, Hint.vals, Dest.vals, List.cons_append,
    List.nil_append, valsList_append]
  refine .cons ⟨1, by omega, rfl⟩ (.cons ⟨0, by omega, rfl⟩ (.cons ⟨2, by omega, rfl⟩ ?_))
  refine NumBelow.append (fun v hv => ?_) (((valsList_booleans 3 32).mono (by omega)).append
    ((shifts_below.mono (by omega)).append ?_))
  · simp only [List.mem_map, List.mem_range] at hv
    obtain ⟨j, hj, rfl⟩ := hv
    exact ⟨_, by omega, rfl⟩
  · simp only [powers, List.range_succ, List.range_zero, List.nil_append, List.map_cons, List.map_nil,
      cst, valsList_cons, valsList_nil, Stmt.vals, Atom.vals, List.cons_append,
      List.nil_append, List.append_nil]
    repeat (first | exact .nil _ | refine .cons ⟨_, by omega, rfl⟩ ?_)

/-- **The prologue is complete**: from the pointer's parameter word and any leaf index. -/
theorem xPrologue_complete {σ : Val} {param : E} (hl : LoadHolds rd (σ (.n 0)) 1 param) {L : Nat}
    (hL : L < 2 ^ 32) :
    Completes C rd 1 139 xPrologue σ (fun σ' => XPre σ' L ∧ σ' (.n 1) = param ∧ AgreeBelow 1 σ σ') := by
  rw [xPrologue_eq]
  set σ1 := Function.update σ (.n 1) param
  set σ2 := Function.update σ1 (.n 2) (mdw 64 true)
  have ne : ∀ a b : Nat, a ≠ b → (V.n a) ≠ V.n b := fun a b h e => h (by cases e; rfl)
  refine Completes.atom_cons param (by omega) (.cons ⟨_, by omega, rfl⟩ (.cons ⟨_, by omega, rfl⟩ (.nil _))) ?_ ?_
  · show LoadHolds rd (Function.update σ (.n 1) param (.n 0)) 1 (Function.update σ (.n 1) param (.n 1))
    rwa [Function.update_self, Function.update_of_ne (ne _ _ (by omega))]
  refine Completes.atom_cons (mdw 64 true) (by omega) (.cons ⟨_, by omega, rfl⟩ (.nil _)) (Function.update_self _ _ _) ?_
  refine Completes.hint_cons (.witness "leaf_index_bits" (.stack ((List.range 32).map fun j => .n (3 + j)))) ?_
  set bl := (List.range 32).map fun j => (3 + j, bitE (L.testBit j))
  set σ3 := upds σ2 bl
  have he3 : Ext 3 139 σ2 σ3 := upds_ext σ2 bl (by simp [bl]; omega)
  have hb3 : ∀ j < 32, σ3 (.n (3 + j)) = bitE (L.testBit j) := upds_range_at 3 _ 32 σ2
  refine Completes.of_ext he3 (Completes.mono (lo := 35) ?_ (by omega) le_rfl fun σ' h => h)
  refine Completes.append_holds (valsList_booleans 3 32) (fun next kret hn =>
    (booleans_iff 3 32).mpr ⟨fun j hj => by rw [hb3 j hj]; exact bitE_mul_self _, hn⟩) ?_
  have hsh := shifts_complete (C := C) (rd := rd) (σ := σ3) (outBase := 35) (by omega) (by omega) hL (by omega) hb3
  refine Completes.append (m := 129) (by omega) (by omega) ?_ hsh fun σ4 he4 ⟨hs4, hag4⟩ =>
    (powers_complete 129).mono le_rfl le_rfl fun σ5 ⟨hp5, hag5⟩ => ?_
  · exact shifts_below
  · have h5 : ∀ k < 35, σ5 (.n k) = σ3 (.n k) := fun k hk => ((hag4 k hk).trans (hag5 k (by omega))).symm
    have h3 : ∀ k < 3, σ3 (.n k) = σ2 (.n k) := fun k hk => (he3.agree k hk).symm
    refine ⟨⟨?_, hL, fun j hj => ?_, nodes_of_shifts fun r hr => ?_, hp5⟩, ?_, fun k hk => ?_⟩
    · rw [h5 _ (by omega), h3 _ (by omega)]; exact Function.update_self _ _ _
    · rw [h5 _ (by omega)]; exact hb3 j hj
    · rw [← hag5 _ (by omega)]; exact hs4 r hr
    · rw [h5 _ (by omega), h3 _ (by omega)]
      simp [σ2, σ1]
    · rw [h5 _ (by omega), h3 _ (by omega)]
      simp only [σ2, σ1]
      rw [Function.update_of_ne (ne _ _ (by omega)), Function.update_of_ne (ne _ _ (by omega))]

end
end LeanVM.Guest.B1.Sig
