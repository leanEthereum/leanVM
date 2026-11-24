/-
  LeanVM.Guest.B1.Da.CellRef

  `da_verify_cell`'s reference function: what its commands give, and its honest run.
-/

module

public import LeanVM.Guest.Ref.Link
public import LeanVM.Guest.Ref.Keccak
public import LeanVM.Guest.B1.Da.Interface
-- Private: `guest_const%` inserts literals, so importers need not see the guest's source.
import LeanVM.Guest.Data.Source

/-!
# `da_verify_cell`, from its source

`cellRef` is `da_verify_cell(lvals)` of `guests/lean_ethereum.py` read line by line
(`LeanVM.Guest.Ref.Lang`): the hinted symbols are the names `sym e`; the loop's reads of the
weights are commands and its arithmetic the returned term `dotTm`; `keccak_cells(sym, st)` into the
two cells of `st` is `sponge`. `cellRef_sat` is what its commands give, `cellRef_honest` its
honest run; `CellLink.lean` ties the compiled function to it.
-/

namespace LeanVM.Guest.B1.Da

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Ref
open LeanVM.Protocol.KeccakHash LeanVM.Guest.Value.Keccak LeanVM.Guest.B1.Digest

@[expose] public section

/-- The names of `da_verify_cell`. -/
inductive CellName where
  /-- The argument, the weights' pointer. -/
  | lvals
  /-- `sym[e]`, hinted. -/
  | sym (e : ℕ)
  /-- `lvals[GEN ** e]`. -/
  | w (e : ℕ)
  /-- Cell `c` of the hash's state before block `b`. -/
  | state (b c : ℕ)
  /-- `st[j]`. -/
  | out (j : ℕ)
  deriving DecidableEq

instance : Coded CellName where
  code
    | .lvals => 0
    | .sym e => 4 * e + 1
    | .w e => 4 * e + 2
    | .state b c => 4 * (13 * b + c) + 3
    | .out j => 4 * j + 4

/-- `s` after `n` symbols; the compiler folds `0 + x`. -/
def dotTm : ℕ → Tm CellName
  | 0 => .const 0
  | 1 => .mul (.v (.w 0)) (.v (.sym 0))
  | n + 1 => .add (dotTm n) (.mul (.v (.w n)) (.v (.sym n)))

/-- **`da_verify_cell(lvals)`.** -/
def cellRef : Func CellName where
  params := [.lvals]
  body := unroll 0 (guest_const% DA_CELL) (fun e => [.load (.v (.w e)) (.v .lvals) e]) ++
    sponge (fun b c => .v (.state b c)) ((List.range (guest_const% DA_CELL)).map (.v <| .sym ·))
      (guest_const% DA_CELL) [.v (.out 0), .v (.out 1)]
  rets := [.v (.out 0), .v (.out 1), dotTm (guest_const% DA_CELL)]

theorem eval_dotTm (ρ : CellName → E) :
    ∀ n, (dotTm n).eval ρ = ((List.range n).map fun e => ρ (.w e) * ρ (.sym e)).sum
  | 0 => by simp [dotTm, Tm.eval]
  | 1 => by simp [dotTm, Tm.eval]
  | n + 2 => by
    show (dotTm (n + 1)).eval ρ + _ = _
    rw [eval_dotTm ρ (n + 1), List.range_succ (n := n + 1)]
    simp [Tm.eval]

/-- The symbols, on the names. -/
def symsOf (ρ : CellName → E) : List E :=
  (List.range (guest_const% DA_CELL)).map fun e => ρ (.sym e)

/-- The weights, on the names. -/
def wsOf (ρ : CellName → E) : List E :=
  (List.range (guest_const% DA_CELL)).map fun e => ρ (.w e)

/-- **What the commands give**, on the names: the weights read at `lvals`, and the returned words
are the symbols' digest and their dot product with the weights. -/
theorem cellRef_sat {rd : Reader} {ρ : CellName → E} (h : Cmd.SatList rd ρ cellRef.body) :
    ReadsAt rd (ρ .lvals) (wsOf ρ) ∧ cellRef.rets.map (Tm.eval ρ) =
      digestCells (keccak256 ((symsOf ρ).flatMap E.toBytes)) ++
        [((List.range LeanDa.cellSymbols).map fun e ↦
          (wsOf ρ).getD e 0 * (symsOf ρ).getD e 0).sum] := by
  rw [cellRef, Cmd.satList_append, Cmd.satList_unroll,
    satList_sponge _ _ (by simp) _ (.inr rfl)] at h
  refine ⟨fun k hk => ?_, ?_⟩
  · simpa [Cmd.SatList, Cmd.Sat, Tm.eval, wsOf] using
      h.1 k (Nat.zero_le _) (by simpa [wsOf] using hk)
  · have hd : [ρ (.out 0), ρ (.out 1)] = digestCells (keccak256 ((symsOf ρ).flatMap E.toBytes)) :=
      h.2.2
    rw [← hd]
    simp only [cellRef, List.map_cons, List.map_nil, Tm.eval, eval_dotTm, List.cons_append,
      List.nil_append, LeanDa.cellSymbols, List.cons.injEq, and_true, true_and]
    refine congrArg List.sum (List.map_congr_left fun e he => ?_)
    simp [wsOf, symsOf, List.getD_eq_getElem?_getD, List.mem_range.mp he]

/-- The names' words, from the argument, the symbols and the weights. -/
private def cellVal (lv : E) (syms ws : List E) : CellName → E
  | .lvals => lv
  | .sym e => syms.getD e 0
  | .w e => ws.getD e 0
  | .state b c => if h : c < 13 then
      spongeSt (padCells syms (16 * syms.length)) (blocks syms.length) b ⟨c, h⟩ else 0
  | .out j => (digestCells (keccak256 (syms.flatMap E.toBytes))).getD j 0

/-- **An honest run of `da_verify_cell`'s reference function**: for `128` symbols and the `128`
weights read at `lv`, a valuation of the names satisfies the commands with the argument `lv`,
returning the symbols' digest and their dot product with the weights, each symbol at its name. -/
theorem cellRef_honest {rd : Reader} {lv : E} {syms ws : List E}
    (hsl : syms.length = LeanDa.cellSymbols) (hr : ReadsAt rd lv ws)
    (hwl : ws.length = LeanDa.cellSymbols) :
    ∃ ρ : CellName → E, cellRef.params.map ρ = [lv] ∧ Cmd.SatList rd ρ cellRef.body ∧
      cellRef.rets.map (Tm.eval ρ) = digestCells (keccak256 (syms.flatMap E.toBytes)) ++
        [((List.range LeanDa.cellSymbols).map fun e ↦ ws.getD e 0 * syms.getD e 0).sum] ∧
      ∀ j, ρ (.sym j) = syms.getD j 0 := by
  simp only [LeanDa.cellSymbols] at hsl hwl
  have hs : ((List.range (guest_const% DA_CELL)).map (Tm.v <| CellName.sym ·)).map
      (Tm.eval (cellVal lv syms ws)) = syms :=
    List.ext_getElem (by simp [hsl]) fun i _ h => by
      simp [Tm.eval, cellVal, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h]
  refine ⟨cellVal lv syms ws, rfl, ?_, ?_, fun _ => rfl⟩
  · rw [cellRef, Cmd.satList_append, Cmd.satList_unroll,
      satList_sponge _ _ (by simp) _ (.inr rfl), hs]
    refine ⟨fun i _ hi => ⟨?_, trivial⟩, fun b _ _ c => ?_, ?_⟩
    · simpa [Cmd.Sat, Tm.eval, cellVal, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem
        (show i < ws.length by omega)] using hr i (by omega)
    · simp [Tm.eval, cellVal, hsl, c.isLt]
    · rfl
  · simp [cellRef, Tm.eval, eval_dotTm, cellVal, digestCells, LeanDa.cellSymbols]

end
end LeanVM.Guest.B1.Da
