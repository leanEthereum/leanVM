/-
  LeanVM.Guest.Ref.KeccakCells

  `keccak_cells` into the digest's two cells, as commands of reference functions, the padding's
  zero cells folded as the compiler folds them.
-/

module

public import LeanVM.Guest.Ref.Keccak
public import LeanVM.Guest.B1.Common.Basic

/-!
# The sponge into two cells

`emit_keccak_message` (`crates/zkdsl_compiler/src/lower/builtins.rs`) XORs a block's rate cell into
the state only where the padded cell is not a literal zero; where it is, the `KECCAK` reads the
state cell itself. `sponge` (`LeanVM.Guest.Ref.Keccak`) adds every padded cell, which matches the
compiled code only when no later block reads a zero padding cell. Here:

* `addCell a P`: `a + P`, or `a` where `P` is the constant zero;
* `spongeTo st msg m o0 o1`: `sponge`'s chain with the zero cells folded, the last block writing
  the two cells `o0`, `o1`;
* `satList_spongeTo`: its commands hold exactly when the states are the absorbed blocks'
  (`spongeSt`) and `o0`, `o1` are the cells of the Keccak-256 digest of the message's bytes.
-/

namespace LeanVM.Guest.Ref

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Guest.Value.Keccak LeanVM.Protocol LeanVM.Protocol.KeccakHash

@[expose] public section

variable {X : Type}

/-- `a + P`, as the compiler emits it: `a` itself where the padded cell `P` is the constant zero. -/
def addCell (a P : Tm X) : Tm X :=
  match P with
  | .const w => bif eEqb w 0 then a else .add a P
  | _ => .add a P

/-- Block `b`'s thirteen read cells over the padded cells `P`, as `spongeIn`, the zero padded cells
of a block after the first folded. -/
def spongeInZ (st : Nat → Nat → Tm X) (P : List (Tm X)) (b : Nat) : List (Tm X) :=
  (List.range 13).map fun c =>
    if b = 0 then (if c < 9 then P.getD c (.const 0) else .const 0)
    else if c < 9 then addCell (st b c) (P.getD (17 * b / 2 + c) (.const 0)) else st b c

/-- **`keccak_cells(msg, [o0, o1])`**, `msg` of `m` cells: one `KECCAK` a block, the last into the
digest's two cells. -/
def spongeTo (st : Nat → Nat → Tm X) (msg : List (Tm X)) (m : Nat) (o0 o1 : Tm X) : List (Cmd X) :=
  unroll 0 (blocks m) fun b =>
    [.keccak (spongeInZ st (msg ++ (padTail m).map Tm.const) b)
      (if b + 1 = blocks m then [o0, o1] else (List.range 13).map (st (b + 1)))
      (inLayout b) (outLayout (blocks m) b)]

theorem eval_addCell (ρ : X → E) (a P : Tm X) : (addCell a P).eval ρ = a.eval ρ + P.eval ρ := by
  unfold addCell
  split
  · rename_i w
    cases h : eEqb w 0
    exacts [rfl, by simp [Tm.eval, eEqb_sound h]]
  · rfl

private theorem eval_getD (ρ : X → E) (P : List (Tm X)) (i : Nat) :
    (P[i]?.getD (.const 0)).eval ρ = (Option.map (Tm.eval ρ) P[i]?).getD 0 := by
  cases P[i]? <;> rfl

private theorem cells13_spongeInZ {ρ : X → E} {st : Nat → Nat → Tm X} {P : List (Tm X)} {b : Nat}
    {S : Fin 13 → E} (hS : b = 0 ∧ S = 0 ∨ b ≠ 0 ∧ ∀ c : Fin 13, (st b c).eval ρ = S c) :
    cells13 ((spongeInZ st P b).map (Tm.eval ρ)) = blockIn (P.map (Tm.eval ρ)) b S := by
  funext c
  simp only [cells13, spongeInZ, List.map_map, List.getD_eq_getElem?_getD, List.getElem?_map,
    List.getElem?_range c.isLt, Option.map_some, Option.getD_some, Function.comp_apply, blockIn]
  rcases hS with ⟨rfl, rfl⟩ | ⟨hb, hS⟩ <;> split_ifs <;> simp_all [eval_getD, eval_addCell, Tm.eval]

private theorem length_spongeInZ (st : Nat → Nat → Tm X) (P : List (Tm X)) (b : Nat) :
    (spongeInZ st P b).length = 13 := by simp [spongeInZ]

private theorem cells13_map_range {ρ : X → E} (t : Nat → Tm X) (c : Fin 13) :
    cells13 (((List.range 13).map t).map (Tm.eval ρ)) c = (t c).eval ρ := by
  simp [cells13, List.getD_eq_getElem?_getD]

/-- The last state's first two cells are the digest's. -/
private theorem spongeSt_pair (cs : List E) :
    (spongeSt (padCells cs (16 * cs.length)) (blocks cs.length) (blocks cs.length) 0,
      spongeSt (padCells cs (16 * cs.length)) (blocks cs.length) (blocks cs.length) 1) =
      digestHalves (keccak256 (cellsBytes cs)) := by
  have h := keccak_final_digest (pre := []) (n := 0) (cells := cs) (len := 16 * cs.length)
    (I := fun b => blockIn (padCells cs (16 * cs.length)) b
      (spongeSt (padCells cs (16 * cs.length)) (blocks cs.length) b))
    (O := spongeSt (padCells cs (16 * cs.length)) (blocks cs.length)) rfl le_rfl
    (getD_cellsBytes_of_le le_rfl) (funext fun c => (cellsOfState_zero false c).symm)
    (fun k _ c hc => by simp [blockIn, hc]) (fun k _ c hc => by simp [blockIn, not_lt.mpr hc])
    (fun k _ c _ => rfl)
  rwa [List.nil_append, List.take_of_length_le (by simp)] at h

/-- **`keccak_cells(msg, [o0, o1])`'s commands hold exactly when** its states are the absorbed
blocks' and `o0`, `o1` are the Keccak-256 digest's cells of the message's bytes. -/
theorem satList_spongeTo {rd : Reader} {ρ : X → E} (st : Nat → Nat → Tm X) (msg : List (Tm X))
    {m : Nat} (hm : msg.length = m) (o0 o1 : Tm X) :
    Cmd.SatList rd ρ (spongeTo st msg m o0 o1) ↔
      (∀ b, 0 < b → b < blocks msg.length → ∀ c : Fin 13, (st b c).eval ρ =
          spongeSt (padCells (msg.map (Tm.eval ρ)) (16 * msg.length)) (blocks msg.length) b c) ∧
        (o0.eval ρ, o1.eval ρ) = digestHalves (keccak256 (cellsBytes (msg.map (Tm.eval ρ)))) := by
  subst hm
  simp only [spongeTo, Cmd.satList_unroll, Cmd.satList_cons, Cmd.satList_nil, and_true, Cmd.Sat,
    KeccakWords, List.length_map, length_spongeInZ, true_and, zero_le, forall_const]
  have hd := spongeSt_pair (msg.map (Tm.eval ρ))
  rw [List.length_map] at hd
  rw [← hd]
  set B := blocks msg.length
  set P := padCells (msg.map (Tm.eval ρ)) (16 * msg.length)
  have hP : (msg ++ (padTail msg.length).map Tm.const).map (Tm.eval ρ) = P := by
    have e := padCells_eq (msg.map (Tm.eval ρ))
    rw [List.length_map] at e
    simp [P, e, Function.comp_def, Tm.eval]
  have hB : 0 < B := Nat.succ_pos _
  have cell : ∀ b, (b = 0 ∨ ∀ c : Fin 13, (st b c).eval ρ = spongeSt P B b c) →
      cells13 ((spongeInZ st (msg ++ (padTail msg.length).map Tm.const) b).map (Tm.eval ρ)) =
        blockIn P b (spongeSt P B b) := fun b hb => by
    rw [cells13_spongeInZ (S := spongeSt P B b), hP]
    rcases Nat.eq_zero_or_pos b with rfl | hb0
    exacts [.inl ⟨rfl, rfl⟩, .inr ⟨by omega, hb.resolve_left (by omega)⟩]
  have last : (∃ oc : KeccakOutputCells, 2 = oc.cellCount ∧
      KeccakCellsRelation (blockIn P (B - 1) (spongeSt P B (B - 1))) (inLayout (B - 1))
        (cells13 [o0.eval ρ, o1.eval ρ]) (outLayout B (B - 1)) oc) ↔
      (o0.eval ρ, o1.eval ρ) = (spongeSt P B B 0, spongeSt P B B 1) := by
    rw [show spongeSt P B B = spongeSt P B (B - 1 + 1) by rw [Nat.sub_add_cancel hB]]
    refine ⟨fun ⟨oc, hoc, h⟩ => ?_, fun h => ⟨.two, rfl, fun c hc => ?_⟩⟩
    · obtain rfl : oc = .two := by cases oc <;> first | rfl | simp [KeccakOutputCells.cellCount] at hoc
      exact Prod.ext (h 0 (by decide)) (h 1 (by decide))
    · obtain rfl | rfl : c = 0 ∨ c = 1 := by
        rcases c with ⟨_ | _ | _, _⟩ <;> simp_all [KeccakOutputCells.cellCount]
      exacts [congrArg Prod.fst h, congrArg Prod.snd h]
  constructor
  · intro h
    have hst : ∀ b, b < B → b = 0 ∨ ∀ c : Fin 13, (st b c).eval ρ = spongeSt P B b c := by
      intro b
      induction b with
      | zero => exact fun _ => .inl rfl
      | succ b ih =>
        intro hb
        obtain ⟨oc, hoc, hK⟩ := h b (by omega)
        rw [ite_eq_right (show ¬ b + 1 = B by omega)] at hoc hK
        rw [List.length_map, List.length_range] at hoc
        obtain rfl : oc = .all := by
          cases oc <;> first | rfl | simp [KeccakOutputCells.cellCount] at hoc
        refine .inr fun c => ?_
        have := hK c c.isLt
        rwa [cell b (ih (by omega)), cells13_map_range] at this
    refine ⟨fun b hb hbB => (hst b hbB).resolve_left (by omega), ?_⟩
    have := h (B - 1) (by omega)
    rw [ite_eq_left (show B - 1 + 1 = B by omega), cell (B - 1) (hst (B - 1) (by omega))] at this
    exact last.mp this
  · rintro ⟨hs, ho'⟩ b hb
    have hc := cell b (by rcases Nat.eq_zero_or_pos b with h | h; exacts [.inl h, .inr (hs b h hb)])
    rw [hc]
    by_cases e : b + 1 = B
    · rw [ite_eq_left e]
      obtain rfl : b = B - 1 := by omega
      exact last.mpr ho'
    · rw [ite_eq_right e]
      refine ⟨.all, by simp [KeccakOutputCells.cellCount], fun c _ => ?_⟩
      rw [cells13_map_range, hs (b + 1) (by omega) (by omega) c]
      rfl

end
end LeanVM.Guest.Ref
