/-
  LeanVM.Guest.B1.Digest.StatementRef

  `statement_digest`'s reference function and its meaning.
-/

module

public import LeanVM.Guest.Ref.Link
public import LeanVM.Guest.Ref.Keccak
public import LeanVM.Guest.B1.Digest.Interface

/-!
# `statement_digest`, from its source

`sdRef` is `statement_digest(seed_0, …, da_1, defer)` of `guests/lean_ethereum.py` read line by
line (`LeanVM.Guest.Ref.Lang`): the header cells are the first eight parameters' names (a store of
a parameter into a cell is that parameter's word), the deferred cells are read at `defer`, and
`keccak_cells(cells, st)` into the two cells of `st` is `sponge`. `sdRef_sem` is its meaning;
`StatementLink.lean` ties the compiled function to it.
-/

namespace LeanVM.Guest.B1.Digest

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Ref
open LeanVM.Protocol.KeccakHash LeanVM.Guest.Value.Keccak

@[expose] public section

/-- The names of `statement_digest`. -/
inductive SdName where
  /-- Parameter `i`: `seed_0, seed_1, xd_0, xd_1, sd_0, sd_1, da_0, da_1, defer`. -/
  | arg (i : ℕ)
  /-- `defer[GEN ** i]`. -/
  | cell (i : ℕ)
  /-- Cell `c` of the hash's state before block `b`. -/
  | state (b c : ℕ)
  /-- `st[j]`. -/
  | out (j : ℕ)
  deriving DecidableEq

instance : Coded SdName where
  code
    | .arg i => 4 * i
    | .cell i => 4 * i + 1
    | .state b c => 4 * (13 * b + c) + 2
    | .out j => 4 * j + 3

/-- The hashed cells: the eight header parameters, then the deferred cells. -/
def sdMsg : List (Tm SdName) :=
  (List.range 8).map (Tm.v <| .arg ·) ++ (List.range deferStmtCells).map (Tm.v <| .cell ·)

/-- **`statement_digest(seed_0, …, da_1, defer)`.** -/
def sdRef : Func SdName where
  params := [.arg 0, .arg 1, .arg 2, .arg 3, .arg 4, .arg 5, .arg 6, .arg 7, .arg 8]
  body := unroll 0 deferStmtCells (fun i => [.load (.v (.cell i)) (.v (.arg 8)) i]) ++
    sponge (fun b c => .v (.state b c)) sdMsg 32 [.v (.out 0), .v (.out 1)]
  rets := [.v (.out 0), .v (.out 1)]

/-- The hashed cells, on the names. -/
theorem sdMsg_eval (ρ : SdName → E) : sdMsg.map (Tm.eval ρ) =
    [ρ (.arg 0), ρ (.arg 1), ρ (.arg 2), ρ (.arg 3), ρ (.arg 4), ρ (.arg 5), ρ (.arg 6),
      ρ (.arg 7)] ++ (List.range deferStmtCells).map (ρ <| .cell ·) := by
  simp [sdMsg, List.range_succ, Tm.eval]

theorem sdMsg_length : sdMsg.length = 32 := by simp [sdMsg, deferStmtCells]

/-- The statement's bytes are its cells'. -/
theorem stmtBytes_eq (hdr defer : List E) : stmtBytes hdr defer = cellsBytes (hdr ++ defer) := by
  rw [stmtBytes, cellsBytes_append]
  rfl

/-- The names' words, from the arguments and the deferred cells. -/
private def sdVal (args cells : List E) : SdName → E
  | .arg i => args.getD i 0
  | .cell i => cells.getD i 0
  | .state b c => if h : c < 13 then
      spongeSt (padCells (args.take 8 ++ cells) (16 * 32)) (blocks 32) b ⟨c, h⟩ else 0
  | .out j => (digestCells (keccak256 (cellsBytes (args.take 8 ++ cells)))).getD j 0

/-- **`statement_digest`'s reference function is its meaning.** -/
theorem sdRef_sem (rd : Reader) (args rets : List E) :
    sdRef.Sem rd args rets ↔ MeaningStatementDigest rd args rets := by
  constructor
  · rintro ⟨ρ, rfl, hb, rfl⟩
    rw [sdRef, Cmd.satList_append, Cmd.satList_unroll, satList_sponge _ _ sdMsg_length _ (.inr rfl)]
      at hb
    have hd : [ρ (.out 0), ρ (.out 1)] =
        digestCells (keccak256 (cellsBytes (sdMsg.map (Tm.eval ρ)))) := hb.2.2
    rw [sdMsg_eval] at hd
    refine ⟨(List.range deferStmtCells).map (ρ <| .cell ·), by simp, fun k hk => ?_, ?_⟩
    · simpa [Cmd.SatList, Cmd.Sat, Tm.eval] using hb.1 k (Nat.zero_le _) (by simpa using hk)
    · rw [stmtBytes_eq]
      exact hd
  · intro hm
    obtain ⟨s0, s1, x0, x1, y0, y1, a0, a1, dp, rfl⟩ :
        ∃ s0 s1 x0 x1 y0 y1 a0 a1 dp, args = [s0, s1, x0, x1, y0, y1, a0, a1, dp] := by
      match args, hm with
      | [s0, s1, x0, x1, y0, y1, a0, a1, dp], _ => exact ⟨s0, s1, x0, x1, y0, y1, a0, a1, dp, rfl⟩
    obtain ⟨cells, hlen, hr, rfl⟩ := hm
    have hmsg : sdMsg.map (Tm.eval (sdVal [s0, s1, x0, x1, y0, y1, a0, a1, dp] cells)) =
        [s0, s1, x0, x1, y0, y1, a0, a1] ++ cells := by
      rw [sdMsg_eval]
      congr 1
      exact List.ext_getElem (by simp [hlen]) fun i _ h => by
        simp [sdVal, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h]
    refine ⟨sdVal [s0, s1, x0, x1, y0, y1, a0, a1, dp] cells, rfl, ?_, ?_⟩
    · rw [sdRef, Cmd.satList_append, Cmd.satList_unroll,
        satList_sponge _ _ sdMsg_length _ (.inr rfl), hmsg, sdMsg_length]
      refine ⟨fun i _ hi => ⟨?_, trivial⟩, fun b _ _ c => ?_, ?_⟩
      · show LoadHolds rd dp i (cells.getD i 0)
        rw [List.getD_eq_getElem _ _ (hlen ▸ hi)]
        exact hr i (hlen ▸ hi)
      · simp [Tm.eval, sdVal, c.isLt]
      · simp [Tm.eval, sdVal, digestCells]
    · simp [sdRef, Tm.eval, sdVal, stmtBytes_eq, digestCells]

end
end LeanVM.Guest.B1.Digest
