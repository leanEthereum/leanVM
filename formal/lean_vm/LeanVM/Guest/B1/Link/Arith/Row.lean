/-
  LeanVM.Guest.B1.Link.Arith.Row

  The row side's identity: the guest's `coef`, `shifts`, `cert_w` and `base` are `linkTail`'s
  row side's.
-/

module

public import LeanVM.Guest.B1.Link.Arith.RowStd
public import LeanVM.Guest.B1.Link.Arith.Program

/-!
# The row side

Three kernel checks, each of one table fold, chained by rewriting (one check across all three
recurses too deep in the kernel):

* `rowA`: `linkTail`'s row side is `rowSideG` at `E` on its `let`s (any inputs);
* `lets_*`: at challenges `θ_0`, then `88` entries, then any rest, and five fresh coefficients,
  the `let`s sliced from them are `tailIn`'s challenges (`gammaState`, `gammaMem`, `mu`, `etaMem`,
  `etaBc`, `eps`, `jump`);
* `rowB`: `rowSideG` at `E` on those inputs, the message's first `80` values then its rest, over
  `tablesL` (`tablesL_eq`), is `stdRow` evaluated at `tailIn`'s inputs.

`row_norm`: `stdRow`'s normal forms are the guest's at `stdIn`, by the kernel. `rowIdentity`
assembles them.
-/

namespace LeanVM.Guest.B1.Link.Arith

open LeanVM.Parameters LeanVM.Guest LeanVM.Protocol.Verifier

@[expose] public section

theorem row_norm : (gCoef stdIn).norm = stdRow.coef.norm ∧
    (gShifts stdIn).map (·.norm) = stdRow.shifts.map (·.norm) ∧
    (gCertW stdIn).norm = stdRow.certWeight.norm ∧ (gBase stdIn).norm = stdRow.base.norm := by
  decide +kernel

/-- The row side's inputs as `linkTail`'s `let`s give them. -/
abbrev rowOfLets (tbls : List Table) (L : TailLets) (hts rows : List ℕ) (chi message : List E)
    (m1 : E) (gammaState gammaMem jump eps : List E) (mu : List (List E)) (etaMem etaBc : E) :
    RowAcc E :=
  let height := fun (t : ℕ) ↦ hts.getD t 0
  rowSideG tbls (fun t ↦ omegaAt (L.theta.getD t 0) (L.tau.take (height t)) (chi.take (height t))
      (rows.getD t 0))
    (fun t ↦ lessThan (chi.take (height t)) (rows.getD t 0))
    (fun t ↦ eqEval (L.tau.take (height t)) (chi.take (height t)))
    (fun t ↦ prodE ((chi.drop (height t)).map (1 + ·)))
    gammaState gammaMem L.slot jump eps L.eqQ message mu etaMem etaBc L.eqZetaR L.shiftZetaR
    L.xBc L.pFp L.yMem m1 L.eq0R Table.constraints

section A

variable (lm lb : ℕ) (bc : List K) (rows : List ℕ) (pl : List (Option Placement)) (sl : ℕ)
  (hts : List ℕ) (chunks : Chunks) (theta0 : E) (drawn r : List E) (m1 : E) (fresh : List E)
  (split : Split) (chi qPoint message : List E)

/-- The `let`s of a layout of `tables()`. -/
abbrev letsOf : TailLets :=
  tailLets (layoutOf lm lb bc rows pl sl hts) chunks theta0 drawn r m1 fresh split qPoint

/-- `linkTail`'s row side at a layout of `tables()`. -/
abbrev rowOf : LinkRowSide :=
  tailRowSide (layoutOf lm lb bc rows pl sl hts) chunks theta0 drawn r m1 fresh split chi qPoint message

/-- `rowOfLets` at the `let`s themselves. -/
abbrev rowLets : RowAcc E :=
  let L := letsOf lm lb bc rows pl sl hts chunks theta0 drawn r m1 fresh split qPoint
  rowOfLets tables L hts rows chi message m1 L.gammaState L.gammaMem L.jump L.eps L.mu L.etaMem
    L.etaBc

theorem rowA_coef : (rowOf lm lb bc rows pl sl hts chunks theta0 drawn r m1 fresh split chi qPoint
    message).coef = (rowLets lm lb bc rows pl sl hts chunks theta0 drawn r m1 fresh split chi qPoint
    message).coef := by
  kernel_eq

theorem rowA_shifts : (rowOf lm lb bc rows pl sl hts chunks theta0 drawn r m1 fresh split chi
    qPoint message).shifts = (rowLets lm lb bc rows pl sl hts chunks theta0 drawn r m1 fresh split
    chi qPoint message).shifts := by
  kernel_eq

theorem rowA_certWeight : (rowOf lm lb bc rows pl sl hts chunks theta0 drawn r m1 fresh split chi
    qPoint message).certWeight = (rowLets lm lb bc rows pl sl hts chunks theta0 drawn r m1 fresh
    split chi qPoint message).certWeight := by
  kernel_eq

theorem rowA_base : (rowOf lm lb bc rows pl sl hts chunks theta0 drawn r m1 fresh split chi qPoint
    message).base = (rowLets lm lb bc rows pl sl hts chunks theta0 drawn r m1 fresh split chi qPoint
    message).base := by
  kernel_eq

end A

/-- The row side at the guest's inputs `v`, the message its `80` sent values then `rest`. -/
abbrev rowV (v : LinkIn E) (rest : List E) : RowAcc E :=
  rowSideG tablesL v.omega v.act v.eqTau v.corner [v.gs0, v.gs1] [v.gm0, v.gm1, v.gm1 * eY, v.gm3]
    ((List.range 16).map v.slot) ((List.range 4).map v.jump) ((List.range 33).map v.eps)
    ((List.range 64).map v.eqQ) ((List.range 80).map v.sent ++ rest) (muOf v.chal) v.etaMem v.etaBc
    v.eqzr v.shz v.xBc v.pFp v.yMem v.m1 v.eq0R Table.constraints

section B

variable (v : LinkIn E) (rest : List E)

theorem rowB_coef : (rowV v rest).coef = stdRow.coef.eval (envOf v) := by kernel_eq

theorem rowB_shifts : (rowV v rest).shifts = stdRow.shifts.map (Ex.eval (envOf v)) := by kernel_eq

theorem rowB_certWeight : (rowV v rest).certWeight = stdRow.certWeight.eval (envOf v) := by kernel_eq

theorem rowB_base : (rowV v rest).base = stdRow.base.eval (envOf v) := by kernel_eq

end B

section C

variable (lm lb : ℕ) (bc : List K) (rows : List ℕ) (pl : List (Option Placement)) (sl : ℕ)
  (hts : List ℕ) (chunks : Chunks) (theta0 : E) (f : ℕ → E) (rest r : List E) (m1 : E)
  (h : ℕ → E) (g : ℕ → E) (chi : List E) (p : ℕ → E) (message : List E)

/-- The guest's inputs at challenges `θ_0`, `88` entries `f`, a rest, five fresh coefficients `h`,
`36` split values `g` and a point `p` of six coordinates. -/
abbrev inC : LinkIn E :=
  tailIn (layoutOf lm lb bc rows pl sl hts) chunks theta0 ((List.range 88).map f ++ rest) r m1
    ((List.range 5).map h) ((List.range 36).map g) chi ((List.range 6).map p) message

/-- The `let`s at the same. -/
abbrev letsC : TailLets :=
  letsOf lm lb bc rows pl sl hts chunks theta0 ((List.range 88).map f ++ rest) r m1
    ((List.range 5).map h) (Split.ofColumns tables ((List.range 36).map g)) ((List.range 6).map p)

/-- **The `let`s' slices are the guest's inputs**: `rowOfLets` at them, the message's first `80`
values then its rest, is `rowV` at `tailIn`'s inputs (the kernel compares the arguments). -/
theorem rowOfLets_eq :
    let L := letsC lm lb bc rows pl sl hts chunks theta0 f rest r m1 h g p
    rowOfLets tablesL L hts rows chi ((List.range 80).map (message.getD · 0) ++ message.drop 80) m1
        L.gammaState L.gammaMem L.jump L.eps L.mu L.etaMem L.etaBc =
      rowV (inC lm lb bc rows pl sl hts chunks theta0 f rest r m1 h g chi p message)
        (message.drop 80) := by
  intro L
  kernel_eq

end C

theorem gShifts_eval (v : LinkIn E) : gShifts v = (gShifts stdIn).map (Ex.eval (envOf v)) := by
  rw [gShifts, gShifts, List.map_map]
  refine List.map_congr_left fun s hs ↦ ?_
  exact gShift_eval v s (List.mem_range.mp hs)

theorem map_eval_eq_of_norm {as bs : List Ex} (h : as.map (·.norm) = bs.map (·.norm)) (ρ : ℕ → E) :
    as.map (Ex.eval ρ) = bs.map (Ex.eval ρ) := by
  induction as generalizing bs with
  | nil => cases bs with
    | nil => rfl
    | cons _ _ => simp at h
  | cons a as ih => cases bs with
    | nil => simp at h
    | cons b bs =>
      simp only [List.map_cons, List.cons.injEq] at h ⊢
      exact ⟨eval_eq_of_norm h.1 ρ, ih h.2⟩

/-- `rowOfLets` reads the message only through its first `80` values. -/
theorem rowOfLets_message (tbls : List Table) (L : TailLets) (hts rows : List ℕ)
    (chi message : List E) (m1 : E) (gammaState gammaMem jump eps : List E) (mu : List (List E))
    (etaMem etaBc : E) (hm : 80 ≤ message.length) :
    rowOfLets tbls L hts rows chi message m1 gammaState gammaMem jump eps mu etaMem etaBc =
      rowOfLets tbls L hts rows chi ((List.range 80).map (message.getD · 0) ++ message.drop 80) m1
        gammaState gammaMem jump eps mu etaMem etaBc := by
  rw [← list_canon message 80 hm]

/-- `rowOfLets` over `tablesL`. -/
theorem rowOfLets_tablesL : rowOfLets tables = rowOfLets tablesL := by rw [tablesL_eq]

/-- **The row side.** -/
theorem rowIdentity : RowIdentity := by
  intro layout chunks theta0 drawn r m1 fresh splitv chi qPoint message hs
  obtain ⟨htab, hd, hf, hsv, hq, hm⟩ := hs
  obtain ⟨lm, lb, bc, tbls, rows, pl, sl, hts⟩ := layout
  simp only at htab
  subst htab
  have hsv' : splitv.length = 36 := hsv
  have hq' : qPoint.length = 6 := hq
  have hm' : 80 ≤ message.length := hm
  dsimp only
  rw [list_canon drawn 88 hd, list_canon_eq fresh 5 hf, list_canon_eq splitv 36 hsv',
    list_canon_eq qPoint 6 hq']
  obtain ⟨h1, h2, h3, h4⟩ := row_norm
  have hr := rowOfLets_eq lm lb bc rows pl sl hts chunks theta0 (drawn.getD · 0) (drawn.drop 88) r m1
    (fresh.getD · 0) (splitv.getD · 0) chi (qPoint.getD · 0) message
  dsimp only at hr
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [gCoef_eval, rowA_coef]
    dsimp only [rowLets]
    rw [rowOfLets_tablesL, rowOfLets_message _ _ _ _ _ _ _ _ _ _ _ _ _ _ hm', hr, rowB_coef]
    exact eval_eq_of_norm h1 _
  · rw [gShifts_eval, rowA_shifts]
    dsimp only [rowLets]
    rw [rowOfLets_tablesL, rowOfLets_message _ _ _ _ _ _ _ _ _ _ _ _ _ _ hm', hr, rowB_shifts]
    exact map_eval_eq_of_norm h2 _
  · rw [gCertW_eval, rowA_certWeight]
    dsimp only [rowLets]
    rw [rowOfLets_tablesL, rowOfLets_message _ _ _ _ _ _ _ _ _ _ _ _ _ _ hm', hr, rowB_certWeight]
    exact eval_eq_of_norm h3 _
  · rw [gBase_eval, rowA_base]
    dsimp only [rowLets]
    rw [rowOfLets_tablesL, rowOfLets_message _ _ _ _ _ _ _ _ _ _ _ _ _ _ hm', hr, rowB_base]
    exact eval_eq_of_norm h4 _

end

end LeanVM.Guest.B1.Link.Arith
