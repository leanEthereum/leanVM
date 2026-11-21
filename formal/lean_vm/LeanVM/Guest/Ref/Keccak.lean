/-
  LeanVM.Guest.Ref.Keccak

  The `keccak` builtins on message cells, as commands of reference functions: the chain of
  `KECCAK`s the compiler lowers them to, and the digest it computes.
-/

module

public import LeanVM.Guest.Ref.Lang
public import LeanVM.Guest.Value.KeccakSponge
public import LeanVM.Guest.B1.Common.Basic
import LeanVM.Guest.Vc

/-!
# The sponge, as commands

`keccak_cells(cells, out)` and `keccak(a, b, out)` (`crates/zkdsl_compiler/zkDSL.md`) hash the
bytes of their message cells with Keccak-256 and write the digest's first one or two cells. The
compiler lowers them to a chain of `KECCAK` instructions (`emit_keccak_message`, as
`LeanVM.Guest.Value.KeccakSponge` transcribes it): the message's `16 m` bytes padded
(`padCells`), block `b` reading nine rate cells from cell `17b / 2` in the layout of `b`'s parity,
XORed into the state before it (none for the first; the state cell itself where the padded cell is
a literal zero, `addCell`), and its four capacity cells, the last block writing the output cells.

* `sponge st msg m out`: that chain over the `m` message cells, the cells of the state before
  block `b` named `st b c`, the padding cells constants;
* `satList_sponge`: its commands hold exactly when the states are the absorbed blocks' (`spongeSt`)
  and the one or two cells `out` are the first of the Keccak-256 digest of the message's bytes.
-/

namespace LeanVM.Guest.Ref

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Guest.Value.Keccak LeanVM.Protocol LeanVM.Protocol.KeccakHash

@[expose] public section

variable {X : Type}

/-- The padding cells after `m` message cells: `padCells` of `16 m` bytes past the message. -/
def padTail (m : Nat) : List E := (padCells (List.replicate m 0) (16 * m)).drop m

/-- The blocks a message of `m` cells takes. -/
def blocks (m : Nat) : Nat := 16 * m / rate + 1

/-- `a + P`, as the compiler emits it: `a` itself where the padded cell `P` is the constant zero
(`sponge_xor`). -/
def addCell (a P : Tm X) : Tm X :=
  match P with
  | .const w => bif eEqb w 0 then a else .add a P
  | _ => .add a P

/-- Block `b`'s thirteen read cells over the padded cells `P`, the state before it named `st b`. -/
def spongeIn (st : Nat → Nat → Tm X) (P : List (Tm X)) (b : Nat) : List (Tm X) :=
  (List.range 13).map fun c =>
    if b = 0 then (if c < 9 then P.getD c (.const 0) else .const 0)
    else if c < 9 then addCell (st b c) (P.getD (17 * b / 2 + c) (.const 0)) else st b c

/-- **`keccak_cells(msg, out)`**, `msg` of `m` cells: one `KECCAK` a block, the last into `out`.
The padding is a function of `m` alone, so the kernel evaluates it once per length. -/
def sponge (st : Nat → Nat → Tm X) (msg : List (Tm X)) (m : Nat) (out : List (Tm X)) :
    List (Cmd X) :=
  unroll 0 (blocks m) fun b =>
    [.keccak (spongeIn st (msg ++ (padTail m).map Tm.const) b)
      (if b + 1 = blocks m then out else (List.range 13).map (st (b + 1)))
      (inLayout b) (outLayout (blocks m) b)]

/-- Block `b`'s read cells on words: the state `S` with the padded cells `P` from `17b / 2` in its
rate. -/
def blockIn (P : List E) (b : Nat) (S : Fin 13 → E) (c : Fin 13) : E :=
  S c + if c.val < 9 then P.getD (17 * b / 2 + c) 0 else 0

/-- **The states of the sponge** over the padded cells `P` in `B` blocks: zero, then each block
permuted, in the next block's layout (the last in the even one). -/
def spongeSt (P : List E) (B : Nat) : Nat → Fin 13 → E
  | 0 => 0
  | b + 1 => cellsOfState (keccakF1600 (stateOfCells (blockIn P b (spongeSt P B b)) (inLayout b)))
      (outLayout B b)

/-- The last state's first two cells are the digest's. -/
theorem spongeSt_digest (cs : List E) :
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

private theorem modify_append_ge {α : Type} (r : List α) (f : α → α) :
    ∀ (l : List α) {i : Nat}, l.length ≤ i → (l ++ r).modify i f = l ++ r.modify (i - l.length) f
  | [], i, _ => by simp
  | a :: l, i + 1, h => by
    simp [List.modify_succ_cons, modify_append_ge r f l (i := i) (by simpa using h)]

theorem padCells_eq (cs : List E) : padCells cs (16 * cs.length) = cs ++ padTail cs.length := by
  have h1 : cs.length ≤ 16 * cs.length / 16 := by omega
  have h2 : cs.length ≤ (rate * (16 * cs.length / rate + 1) - 1) / 16 := by simp only [rate]; omega
  have e : ∀ l : List E, l.length = cs.length → padCells l (16 * cs.length) = l ++
      ((List.replicate (padRead (16 * cs.length) - cs.length) 0).modify
        (16 * cs.length / 16 - cs.length) (· + byteCell (16 * cs.length) 1)).modify
          ((rate * (16 * cs.length / rate + 1) - 1) / 16 - cs.length)
          (· + byteCell (rate * (16 * cs.length / rate + 1) - 1) 0x80) := fun l hl => by
    rw [padCells, xorByte, xorByte, hl, modify_append_ge _ _ _ (hl ▸ h1), modify_append_ge _ _ _ (by
      simpa [hl] using h2), hl]
  rw [padTail, e cs rfl, e _ (List.length_replicate ..), List.drop_left' (List.length_replicate ..)]

private theorem eval_addCell (ρ : X → E) (a P : Tm X) :
    (addCell a P).eval ρ = a.eval ρ + P.eval ρ := by
  unfold addCell
  split
  · rename_i w
    cases h : eEqb w 0
    exacts [rfl, by simp [Tm.eval, eEqb_sound h]]
  · rfl

private theorem eval_getD (ρ : X → E) (P : List (Tm X)) (i : Nat) :
    (P[i]?.getD (.const 0)).eval ρ = (Option.map (Tm.eval ρ) P[i]?).getD 0 := by
  cases P[i]? <;> rfl

private theorem cells13_spongeIn {ρ : X → E} {st : Nat → Nat → Tm X} {P : List (Tm X)} {b : Nat}
    {S : Fin 13 → E} (hS : b = 0 ∧ S = 0 ∨ b ≠ 0 ∧ ∀ c : Fin 13, (st b c).eval ρ = S c) :
    cells13 ((spongeIn st P b).map (Tm.eval ρ)) = blockIn (P.map (Tm.eval ρ)) b S := by
  funext c
  simp only [cells13, spongeIn, List.map_map, List.getD_eq_getElem?_getD, List.getElem?_map,
    List.getElem?_range c.isLt, Option.map_some, Option.getD_some, Function.comp_apply, blockIn]
  rcases hS with ⟨rfl, rfl⟩ | ⟨hb, hS⟩ <;> split_ifs <;> simp_all [eval_getD, eval_addCell, Tm.eval]

private theorem length_spongeIn (st : Nat → Nat → Tm X) (P : List (Tm X)) (b : Nat) :
    (spongeIn st P b).length = 13 := by simp [spongeIn]

private theorem cells13_map_range {ρ : X → E} (t : Nat → Tm X) (c : Fin 13) :
    cells13 (((List.range 13).map t).map (Tm.eval ρ)) c = (t c).eval ρ := by
  simp [cells13, List.getD_eq_getElem?_getD]

/-- One or two output cells `vs` of a `KECCAK` are its output's first. -/
private theorem out_iff {vs : List E} (ho : vs.length = 1 ∨ vs.length = 2) {I : Fin 13 → E}
    {i o : Bool} :
    (∃ oc : KeccakOutputCells, vs.length = oc.cellCount ∧
      KeccakCellsRelation I i (cells13 vs) o oc) ↔
      vs = [cellsOfState (keccakF1600 (stateOfCells I i)) o 0,
        cellsOfState (keccakF1600 (stateOfCells I i)) o 1].take vs.length := by
  match vs, ho with
  | [_], _ => exact keccak_cells_one.trans (by simp)
  | [_, _], _ => exact keccak_cells_two.trans (by simp)

/-- **The sponge's commands hold exactly when** its states are the absorbed blocks' and the one or
two cells `out` are the first of the Keccak-256 digest of the message's bytes. -/
theorem satList_sponge {rd : Reader} {ρ : X → E} (st : Nat → Nat → Tm X) (msg : List (Tm X))
    {m : Nat} (hm : msg.length = m) (out : List (Tm X)) (ho : out.length = 1 ∨ out.length = 2) :
    Cmd.SatList rd ρ (sponge st msg m out) ↔
      (∀ b, 0 < b → b < blocks msg.length → ∀ c : Fin 13, (st b c).eval ρ =
          spongeSt (padCells (msg.map (Tm.eval ρ)) (16 * msg.length)) (blocks msg.length) b c) ∧
        out.map (Tm.eval ρ) =
          [(digestHalves (keccak256 (cellsBytes (msg.map (Tm.eval ρ))))).1,
            (digestHalves (keccak256 (cellsBytes (msg.map (Tm.eval ρ))))).2].take out.length := by
  subst hm
  simp only [sponge, Cmd.satList_unroll, Cmd.satList_cons, Cmd.satList_nil, and_true, Cmd.Sat,
    KeccakWords, List.length_map, length_spongeIn, true_and, zero_le, forall_const]
  have hd := spongeSt_digest (msg.map (Tm.eval ρ))
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
      cells13 ((spongeIn st (msg ++ (padTail msg.length).map Tm.const) b).map (Tm.eval ρ)) =
        blockIn P b (spongeSt P B b) := fun b hb => by
    rw [cells13_spongeIn (S := spongeSt P B b), hP]
    rcases Nat.eq_zero_or_pos b with rfl | hb0
    exacts [.inl ⟨rfl, rfl⟩, .inr ⟨by omega, hb.resolve_left (by omega)⟩]
  have last := out_iff (vs := out.map (Tm.eval ρ)) (by simpa using ho)
    (I := blockIn P (B - 1) (spongeSt P B (B - 1))) (i := inLayout (B - 1))
    (o := outLayout B (B - 1))
  rw [List.length_map] at last
  rw [show spongeSt P B B = spongeSt P B (B - 1 + 1) by rw [Nat.sub_add_cancel hB]]
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
        refine .inr fun c => ?_
        have := hK c (hoc ▸ c.isLt)
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
