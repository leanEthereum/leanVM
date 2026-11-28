/-
  LeanVM.Guest.B1.VerifySub.PhLinkEnd

  What the link's end holds of its columns and ring pieces, at the concrete tables: the row
  side's fold read only for its points, its sent values and its pieces.
-/

module

public import LeanVM.Guest.B1.Link.Arith.Program
public import LeanVM.Guest.B1.Stack.Interface
public import LeanVM.Guest.B1.Link.ArithTac

/-!
# The link's end, its columns and pieces

At a layout of the concrete tables (`layoutOf`) and a message of `144` words (`f 0 .. f 143`),
`linkTail`'s row side (`tailRowSide`) folds to columns whose points are `chi`'s prefixes at the
heights and whose columns are the non-pointer ones (`rs_columns_shape`), whose values are the
message's first `80` words in order (`rs_columns_values`), whose `KECCAK` output lanes are the
words from `SENT_OUT_LANES = 55` on (`rs_keccak`), and whose ring pieces are
`Stack.pointerPieces` (`rs_pieces`). Each is a definitional unfolding over the concrete tables,
checked by the kernel (`kernel_eq`).
-/

namespace LeanVM.Guest.B1.VerifySub

open LeanVM.Parameters LeanVM.Protocol.Verifier LeanVM.Protocol.Link LeanVM.Guest.B1.Link.Arith

@[expose] public section

section

variable (lm lb : ℕ) (bc : List K) (rows : List ℕ) (pl : List (Option Placement)) (sl : ℕ)
  (hts : List ℕ) (chunks : Chunks) (theta0 : E) (drawn r : List E) (m1 : E) (fresh : List E)
  (split : Split) (chi qPoint : List E) (f : ℕ → E)

/-- The row side at a layout of the tables and a message of `144` words. -/
abbrev rsOf : LinkRowSide :=
  tailRowSide (layoutOf lm lb bc rows pl sl hts) chunks theta0 drawn r m1 fresh split chi qPoint
    ((List.range 144).map f)

theorem rs_columns_shape :
    (rsOf lm lb bc rows pl sl hts chunks theta0 drawn r m1 fresh split chi qPoint f).columns.map
        (fun c ↦ (c.1, c.2.map (·.1))) =
      tables.zipIdx.map (fun (table, t) ↦ (chi.take (hts.getD t 0), Stack.nonPointerColumns table)) := by
  kernel_eq

theorem rs_columns_values :
    (rsOf lm lb bc rows pl sl hts chunks theta0 drawn r m1 fresh split chi qPoint f).columns.flatMap
        (fun c ↦ c.2.map (·.2)) = (List.range 80).map f := by
  kernel_eq

theorem rs_keccak :
    ((List.range keccakStateLanes).mapM fun lane ↦
        (((rsOf lm lb bc rows pl sl hts chunks theta0 drawn r m1 fresh split chi qPoint f).columns.getD
          opKeccak ([], [])).2.find? fun value ↦ value.1 = keccakOut + lane).map (·.2)) =
      some ((List.range 25).map fun lane ↦ f (55 + lane)) := by
  kernel_eq

theorem rs_keccak_point :
    ((rsOf lm lb bc rows pl sl hts chunks theta0 drawn r m1 fresh split chi qPoint f).columns.getD
      opKeccak ([], [])).1 = chi.take (hts.getD opKeccak 0) := by
  kernel_eq

theorem rs_pieces :
    (rsOf lm lb bc rows pl sl hts chunks theta0 drawn r m1 fresh split chi qPoint f).pieces =
      Stack.pointerPieces (layoutOf lm lb bc rows pl sl hts) chi qPoint := by
  kernel_eq

end

/-! ## At a layout of the tables -/

section

variable {layout : Layout} (h : layout.tables = tables) (chunks : Chunks) (theta0 : E) (drawn r : List E)
  (m1 : E) (fresh : List E) (split : Split) (chi qPoint : List E) {message : List E}
  (hm : message.length = 144)

include h hm

theorem end_columns_shape :
    (tailRowSide layout chunks theta0 drawn r m1 fresh split chi qPoint message).columns.map
        (fun c ↦ (c.1, c.2.map (·.1))) =
      tables.zipIdx.map (fun (table, t) ↦
        (chi.take (layout.tableLogHeights.getD t 0), Stack.nonPointerColumns table)) := by
  obtain ⟨lm, lb, bc, tbls, rows, pl, sl, hts⟩ := layout
  simp only at h
  subst h
  rw [list_canon_eq message 144 hm]
  exact rs_columns_shape lm lb bc rows pl sl hts chunks theta0 drawn r m1 fresh split chi qPoint _

theorem end_columns_values :
    (tailRowSide layout chunks theta0 drawn r m1 fresh split chi qPoint message).columns.flatMap
        (fun c ↦ c.2.map (·.2)) = (List.range 80).map (message.getD · 0) := by
  obtain ⟨lm, lb, bc, tbls, rows, pl, sl, hts⟩ := layout
  simp only at h
  subst h
  conv_lhs => rw [list_canon_eq message 144 hm]
  exact rs_columns_values lm lb bc rows pl sl hts chunks theta0 drawn r m1 fresh split chi qPoint _

theorem end_keccak :
    ((List.range keccakStateLanes).mapM fun lane ↦
        (((tailRowSide layout chunks theta0 drawn r m1 fresh split chi qPoint message).columns.getD
          opKeccak ([], [])).2.find? fun value ↦ value.1 = keccakOut + lane).map (·.2)) =
      some ((List.range 25).map fun lane ↦ message.getD (55 + lane) 0) := by
  obtain ⟨lm, lb, bc, tbls, rows, pl, sl, hts⟩ := layout
  simp only at h
  subst h
  conv_lhs => rw [list_canon_eq message 144 hm]
  exact rs_keccak lm lb bc rows pl sl hts chunks theta0 drawn r m1 fresh split chi qPoint _

theorem end_keccak_point :
    ((tailRowSide layout chunks theta0 drawn r m1 fresh split chi qPoint message).columns.getD
      opKeccak ([], [])).1 = chi.take (layout.tableLogHeights.getD opKeccak 0) := by
  obtain ⟨lm, lb, bc, tbls, rows, pl, sl, hts⟩ := layout
  simp only at h
  subst h
  rw [list_canon_eq message 144 hm]
  exact rs_keccak_point lm lb bc rows pl sl hts chunks theta0 drawn r m1 fresh split chi qPoint _

theorem end_pieces :
    (tailRowSide layout chunks theta0 drawn r m1 fresh split chi qPoint message).pieces =
      Stack.pointerPieces layout chi qPoint := by
  obtain ⟨lm, lb, bc, tbls, rows, pl, sl, hts⟩ := layout
  simp only at h
  subst h
  rw [list_canon_eq message 144 hm]
  exact rs_pieces lm lb bc rows pl sl hts chunks theta0 drawn r m1 fresh split chi qPoint _

end

end
end LeanVM.Guest.B1.VerifySub
