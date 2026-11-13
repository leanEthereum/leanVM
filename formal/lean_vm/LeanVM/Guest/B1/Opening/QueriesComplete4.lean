/-
  LeanVM.Guest.B1.Opening.QueriesComplete4

  The completeness of one query of `opening_queries`: every statement holds at the honest
  values, and the query's result is its fold (or, at the final level, `0`).
-/

module

public import LeanVM.Guest.B1.Opening.QueriesComplete1
public import LeanVM.Guest.B1.Opening.QueriesComplete3

/-!
# One query, completeness

`QD.Ok` is what the opening, the windows and the challenges say of an honest query: the siblings,
the row's length, the walk's memory (`MemOk`), the position below `2^depth`, the rounds at `coefs` and, at the
final level, the coefficients at `hs`
and the fold equal to their novel sum (`QueryHolds`' last clause). `foldVal_eq`: the guest's fold
of the honest values is the Spec's `foldRow` (`guestFold_value`). `query_complete`: at a valuation
that is the honest values on the query's indices, with the padding run `1, 0, 0, 0, 0`, every
statement of `oqQueryT` holds, its result is `qwFold` (or `0`), and its leaf cells the leaf's
digest's halves.
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

theorem getD_extRow : ∀ (l : List K) (i : ℕ), 2 * i + 1 < l.length →
    (extRow l).getD i 0 = E.ofLimbs (l.getD (2 * i) 0) (l.getD (2 * i + 1) 0)
  | c0 :: c1 :: rest, 0, _ => by simp [extRow]
  | c0 :: c1 :: rest, i + 1, h => by
    rw [extRow, List.getD_cons_succ, getD_extRow rest i (by simp at h; omega)]
    simp only [show 2 * (i + 1) = 2 * i + 1 + 1 by omega, List.getD_cons_succ]
  | [_], _, h => by simp at h
  | [], _, h => by simp at h

theorem length_extRow' : ∀ l : List K, (extRow l).length = l.length / 2
  | _ :: _ :: rest => by simp only [extRow, List.length_cons, length_extRow' rest]; omega
  | [_] => by simp [extRow]
  | [] => rfl

theorem getD_reverse_map (l : List K) {i : ℕ} (h : i < l.length) :
    (l.reverse.map ofK).getD i 0 = ofK (l.getD (l.length - 1 - i) 0) := by
  rw [List.getD_eq_getElem _ _ (by simpa using h), List.getD_eq_getElem _ _ (by omega)]
  simp [List.getElem_reverse]

namespace QD

/-- What the opening, the windows and the challenges say of an honest query. -/
structure Ok (d : QD) (rd : Reader) (coefsv hsp bpv : E) : Prop where
  hsibs : d.sibs.length = d.s.pd
  hrow : d.row.length = rowLen d.s.base d.s.folds
  hmem : (d.wd bpv).MemOk rd
  hq : d.q < 2 ^ (d.s.pd + d.s.cd)
  hR : RoundsAt rd coefsv d.rounds
  hrl : d.rounds.length = d.s.folds
  hfin : d.s.final = 1 → WordsAt rd hsp d.hsv ∧ d.hsv.length = d.s.nHs ∧
    foldRow (lanesOf d.s.base d.row) (K.ofBits d.q) d.rounds =
      novelSum d.hsv (wsChain (d.s.vs.map K.ofBits) (eOfNat d.q)) d.s.nHs d.s.hsBits

variable (d : QD) {rd : Reader} {σ : Val}

theorem x_eq : d.x = ofK (K.ofBits d.q) := rfl

/-- **The guest's fold of the honest values is the Spec's.** -/
theorem foldVal_eq (hs : d.s.RowShape) (hrow : d.row.length = rowLen d.s.base d.s.folds)
    (hrl : d.rounds.length = d.s.folds) :
    d.foldVal = foldRow (lanesOf d.s.base d.row) (K.ofBits d.q) d.rounds := by
  have hf1 : 1 ≤ d.s.folds := by rcases hs with ⟨-, h⟩ | ⟨-, h⟩ <;> omega
  have hI : d.s.I = 2 ^ d.s.folds := rfl
  have h2 : 2 ^ d.s.folds = 2 * 2 ^ (d.s.folds - 1) := by rw [← pow_succ']; congr 1; omega
  rw [foldRow_eq, foldVal]
  refine guestFold_value hrl hf1 ?_ (acc := d.acc) (ts := d.t) (fun j _ ↦ rfl) (fun m hm ↦ ?_)
    (fun j _ m _ ↦ rfl)
  · unfold lanesOf; unfold rowLen at hrow
    split
    · rename_i hb
      simp only [hb, ↓reduceIte] at hrow
      simp [hrow]
    · rename_i hb
      simp only [hb, ↓reduceIte] at hrow
      rw [length_extRow', hrow]; omega
  · unfold acc lane0 lanesOf cell
    unfold rowLen at hrow
    split
    · rename_i hb
      simp only [hb, ↓reduceIte] at hrow ⊢
      rw [getD_reverse_map _ (by omega), getD_reverse_map _ (by omega), hrow, ← hI,
        show d.s.I - 1 - (2 * m + 1) = d.s.I - 2 - 2 * m by omega]
    · rename_i hb
      simp only [hb, ↓reduceIte] at hrow ⊢
      rw [getD_extRow _ _ (by omega), getD_extRow _ _ (by omega)]

/-- The final level's equation in the honest values' terms. -/
theorem finEq_of (hs : d.s.RowShape) (hrow : d.row.length = rowLen d.s.base d.s.folds)
    (hrl : d.rounds.length = d.s.folds)
    (h : foldRow (lanesOf d.s.base d.row) (K.ofBits d.q) d.rounds =
      novelSum d.hsv (wsChain (d.s.vs.map K.ofBits) (eOfNat d.q)) d.s.nHs d.s.hsBits) :
    d.finEq := by
  rw [finEq, d.foldVal_eq hs hrow hrl, h]; rfl

/-- The padding run a query emits. -/
theorem pad_of_emit (he : d.emit = true) (hv : d.Hv σ) :
    σ (.n d.prV) = word 1 0 ∧ ∀ i < 4, σ (.n (d.prV + 1 + i)) = word 0 0 := by
  have hk1 := d.k1_eq
  have hkL := d.kL_eq
  have hc := d.ch_eq
  have hcv := d.ch_le_v
  have hpl : d.padVals.length = 5 := by rw [padVals_length, he]; rfl
  have hpr : d.prV = d.k1 := by simp only [prV, oqPr, he, ↓reduceIte]; rfl
  refine ⟨?_, fun i hi => ?_⟩
  · have := d.hv_of hv (i := d.k1 + 0) (by omega) (by omega)
    rw [val_pad d he (by omega)] at this
    simpa only [hpr, Nat.add_zero, List.getD_cons_zero] using this
  · have := d.hv_of hv (i := d.k1 + (i + 1)) (by omega) (by omega)
    rw [val_pad d he (by omega)] at this
    rw [hpr, show d.k1 + 1 + i = d.k1 + (i + 1) by omega, this]
    interval_cases i <;> rfl

theorem rowLen_eq (hs : d.s.RowShape) : rowLen d.s.base d.s.folds = 2 * d.s.ncells := by
  rcases shape_nums hs with ⟨hb, hI, hn, -⟩ | ⟨hb, hI, hn, -⟩ <;>
    simp [rowLen, hb, ← hI, Oq.I, hn]

/-- The query's statements, by piece. -/
theorem oqQueryT_eq (s : Oq) (x bp cap flags coefs hs : V) (b : ℕ) (emit : Bool) (pr : ℕ)
    (walk : String) :
    oqQueryT s x bp cap flags coefs hs b emit pr walk =
      (oqPrepT s b ++ (if emit then oqPadT (oqK1 s b) else []) ++
        oqLeafT s b (oqPr s b emit pr) (oqKL s b emit)) ++
      [.call walk [.n (oqOut s (oqKL s b emit) (s.B - 1) 0), .n (oqOut s (oqKL s b emit) (s.B - 1) 1),
        bp, cap, flags] []] ++
      (oqFoldT s coefs x b (oqCh s b emit) ++
        (if s.final = 1 then oqFinT s x hs (oqVal s (oqCh s b emit)) else [])) := by
  simp only [oqQueryT, List.append_assoc]

/-- **One query holds at the honest values**, its call of `walk` in `C` on the leaf's halves, the
window pointer, the cap and the flags; its result is its fold (`qwFold`), or `0` at the final
level; its leaf cells are the leaf's digest's halves. -/
theorem query_complete (hs : d.s.RowShape) (hfin : d.s.FinOk) {walk : String} {C : CallRel}
    {x bp cap flags coefs hsp : V} (hok : d.Ok rd (σ coefs) (σ hsp) (σ bp)) (hv : d.Hv σ)
    (hx : σ x = d.x) (hpad : σ (.n d.prV) = word 1 0) (hz : ∀ i < 4, σ (.n (d.prV + 1 + i)) = word 0 0)
    (hcap : σ cap = d.capv) (hflags : σ flags = d.flagsv)
    (hC : C walk [(digestHalves d.leaf).1, (digestHalves d.leaf).2, σ bp, d.capv, d.flagsv] []) :
    BlockOkC C rd σ (oqQueryT d.s x bp cap flags coefs hsp d.b d.emit d.pr walk) ∧
      σ (.n (oqRes d.s d.b d.emit)) =
        (if d.s.final = 1 then 0 else qwFold d.s.base d.rounds (d.q, d.row, d.sibs)) ∧
      (σ (.n (oqOut d.s d.kL (d.s.B - 1) 0)), σ (.n (oqOut d.s d.kL (d.s.B - 1) 1))) =
        digestHalves d.leaf := by
  have hf1 : 1 ≤ d.s.folds := by rcases hs with ⟨-, h⟩ | ⟨-, h⟩ <;> omega
  have hrow2 : d.row.length = 2 * d.s.ncells := by rw [hok.hrow, d.rowLen_eq hs]
  have hleaf := d.oqLeaf_digest hs hrow2 hv hpad hz
  -- the atoms before the call
  have hA1 : BlockOkC C rd σ (oqPrepT d.s d.b ++ (if d.emit then oqPadT (oqK1 d.s d.b) else []) ++
      oqLeafT d.s d.b (oqPr d.s d.b d.emit d.pr) (oqKL d.s d.b d.emit)) := by
    refine blockOkC_of_blockOk (blockOk_of_atoms (allAtoms_append (allAtoms_append
      (oqPrepT_atoms _ _) (by split; exact oqPadT_atoms _; exact allAtoms_nil)) (oqLeafT_atoms _ _ _ _))
      fun a ha ↦ ?_)
    rcases List.mem_append.mp ha with ha | ha
    · rcases List.mem_append.mp ha with ha | ha
      · unfold oqPrepT at ha
        rcases List.mem_append.mp ha with ha | ha
        · simp only [oqRowT, List.mem_singleton, Stmt.atom.injEq] at ha
          subst ha; trivial
        · split at ha
          · rename_i hb
            exact d.oqPacks_complete hb hv a ha
          · simp at ha
      · cases he : d.emit
        · simp [he] at ha
        · simp only [he, ↓reduceIte] at ha
          exact d.oqPad_complete he hv a ha
    · exact d.oqLeaf_complete hs hv hpad hz a ha
  -- the fold and the check
  have hA2 : BlockOkC C rd σ (oqFoldT d.s coefs x d.b (oqCh d.s d.b d.emit) ++
      (if d.s.final = 1 then oqFinT d.s x hsp (oqVal d.s (oqCh d.s d.b d.emit)) else [])) := by
    refine blockOkC_of_blockOk (blockOk_of_atoms (allAtoms_append (oqFoldT_atoms _ _ _ _ _)
      (by split; exact oqFinT_atoms _ _ _ _; exact allAtoms_nil)) fun a ha ↦ ?_)
    rcases List.mem_append.mp ha with ha | ha
    · exact d.oqFold_complete hf1 hv hok.hR hok.hrl hx a ha
    · split at ha
      · rename_i hfinal
        obtain ⟨hW, hl, heq⟩ := hok.hfin hfinal
        exact d.oqFin_complete hf1 hfinal hfin hv hx hW hl
          (d.finEq_of hs hok.hrow hok.hrl heq) a ha
      · simp at ha
  refine ⟨?_, ?_, hleaf⟩
  · rw [oqQueryT_eq]
    refine blockOkC_append.mpr ⟨blockOkC_append.mpr ⟨hA1, fun s hs ↦ ?_⟩, hA2⟩
    simp only [List.mem_singleton] at hs
    subst hs
    show C walk [σ (.n (oqOut d.s d.kL (d.s.B - 1) 0)), σ (.n (oqOut d.s d.kL (d.s.B - 1) 1)), σ bp,
      σ cap, σ flags] []
    have e0 := congrArg Prod.fst hleaf
    have e1 := congrArg Prod.snd hleaf
    simp only at e0 e1
    rw [e0, e1, hcap, hflags]
    exact hC
  · by_cases hfinal : d.s.final = 1
    · obtain ⟨hW, hl, heq⟩ := hok.hfin hfinal
      have hA := d.oqFin_complete (rd := rd) hf1 hfinal hfin hv hx hW hl
        (d.finEq_of hs hok.hrow hok.hrl heq)
      have h := hA _ (List.mem_append_right _ (List.mem_cons_of_mem _ (List.mem_singleton_self _)))
      simp only [Atom.Holds] at h
      simp only [oqRes, hfinal, ↓reduceIte]
      rw [show oqVal d.s (oqCh d.s d.b d.emit) = d.v from rfl, show (oqNovel d.s (.n 0) d.v).2.2 =
        (oqNovel d.s hsp d.v).2.2 from rfl, h, word_zero]
    · simp only [oqRes, hfinal, ↓reduceIte]
      rw [show oqVal d.s (oqCh d.s d.b d.emit) = d.v from rfl,
        d.hv_of hv (by have := d.b_le_ch; have := d.ch_le_v; omega) le_rfl, d.val_v hf1,
        d.foldVal_eq hs hok.hrow hok.hrl]
      rfl

end QD

end
end LeanVM.Guest.B1
