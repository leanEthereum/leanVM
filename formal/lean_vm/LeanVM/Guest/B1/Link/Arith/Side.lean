/-
  LeanVM.Guest.B1.Link.Arith.Side

  The index side's claim, `y_mem`, `x_bc`, `p_fp`, the terminal's arguments, and `linkTail`
  with its `let`s named.
-/

module

public import LeanVM.Guest.B1.Link.Arith.Row
public import LeanVM.Guest.B1.Link.Forms
import Mathlib.Tactic.Ring
import LeanVM.Guest.Value.Bits
import Mathlib.Data.List.GetD

/-!
# The rest of the link's arithmetic

* `claimIdentity`: `indexClaim` and the guest's claim unfold (by the kernel) to the same products
  of `eq(ζ, 0)`, `eq(ζ, T)` and the state challenges, `g^(2^BYTECODE_LOG - 1)` the compiler's
  word for `gpow`;
* `sideIdentity`: `y_mem` by the kernel, `x_bc` and `p_fp` from the program side;
* `terminalIdentity`: `eq_q[0]` is `eq0(q_point)` (`eqKernel_getD_zero`), and the certificates'
  weight is the row side's;
* `linkTailEq`: `linkTail` is `linkTailR`, by the kernel.
-/

namespace LeanVM.Guest.B1.Link.Arith

open LeanVM.Parameters LeanVM.Guest LeanVM.Protocol.Verifier LeanVM.Protocol.Link

@[expose] public section

/-! ## The index side's claim -/

theorem indexClaim_unfold (layout : Layout) (chunks : Chunks) (theta0 : E) (drawn r : List E) (m1 : E)
    (fresh : List E) (split : Split) (qPoint : List E) :
    indexClaim layout chunks drawn =
      let Lz := (tailLets layout chunks theta0 drawn r m1 fresh split qPoint).zeta
      let gs := (drawn.drop (nTables - 1)).take 2
      linkEqAt Lz 0 * (1 + gs.getD 0 0 * 1 + gs.getD 1 0 * 1) +
        linkEqAt Lz (linkCycles layout) *
          (1 + gs.getD 0 0 * gpow (2 ^ layout.logBytecode - 1) + gs.getD 1 0 * 1) := by
  kernel_eq

theorem gClaim_unfold (layout : Layout) (chunks : Chunks) (theta0 : E) (drawn r : List E) (m1 : E)
    (fresh splitv chi qPoint message : List E) :
    gClaim (tailIn layout chunks theta0 drawn r m1 fresh splitv chi qPoint message) =
      let Lz := (tailLets layout chunks theta0 drawn r m1 fresh (Split.ofColumns tables splitv)
        qPoint).zeta
      linkEqAt Lz 0 * (1 + drawn.getD 5 0 + drawn.getD 6 0) +
        linkEqAt Lz (linkCycles layout) *
          (1 + drawn.getD 5 0 * gpowE (2 ^ 19 - 1) + drawn.getD 6 0) := by
  kernel_eq

theorem getD_take_drop (l : List E) (a b i : ℕ) (h : i < b) :
    ((l.drop a).take b).getD i 0 = l.getD (a + i) 0 := by
  simp [List.getD_eq_getElem?_getD, h, List.getElem?_drop]

theorem gpowE_eq_gpow {n : ℕ} (h : n < u128Bound) : gpowE n = gpow n := by
  rw [gpowE, gpowK_eq h, gpow, Value.gen_pow_eq_ofK]

/-- **The index side's claim.** -/
theorem claimIdentity : ClaimIdentity := by
  intro layout chunks theta0 drawn r m1 fresh splitv chi qPoint message hlb
  rw [gClaim_unfold, indexClaim_unfold layout chunks theta0 drawn r m1 fresh
    (Split.ofColumns tables splitv) qPoint]
  dsimp only
  have hn : nTables - 1 = 5 := rfl
  rw [hn, show ((drawn.drop 5).take 2).getD 0 0 = drawn.getD 5 0 from getD_take_drop _ _ _ _ (by norm_num),
    show ((drawn.drop 5).take 2).getD 1 0 = drawn.getD 6 0 from getD_take_drop _ _ _ _ (by norm_num), hlb,
    gpowE_eq_gpow (by decide)]
  ring

/-! ## `y_mem`, `x_bc`, `p_fp` -/

section

variable (lm lb : ℕ) (bc : List K) (rows : List ℕ) (pl : List (Option Placement)) (sl : ℕ)
  (hts : List ℕ) (chunks : Chunks) (theta0 : E) (f : ℕ → E) (rest r : List E) (m1 : E)
  (fresh : List E) (g : ℕ → E) (chi qPoint message : List E)

/-- The `let`s at challenges `θ_0`, `88` entries `f`, a rest, and split values `g`. -/
abbrev letsS : TailLets :=
  tailLets (layoutOf lm lb bc rows pl sl hts) chunks theta0 ((List.range 88).map f ++ rest) r m1 fresh
    (Split.ofColumns tables ((List.range 36).map g)) qPoint

/-- `tailIn` at the same. -/
abbrev inS : LinkIn E :=
  tailIn (layoutOf lm lb bc rows pl sl hts) chunks theta0 ((List.range 88).map f ++ rest) r m1 fresh
    ((List.range 36).map g) chi qPoint message

theorem yMem_eq : gYMem (inS lm lb bc rows pl sl hts chunks theta0 f rest r m1 fresh g chi qPoint
    message) = (letsS lm lb bc rows pl sl hts chunks theta0 f rest r m1 fresh g qPoint).yMem := by
  kernel_eq

theorem xBc_eq (p : E) : (inS lm lb bc rows pl sl hts chunks theta0 f rest r m1 fresh g chi qPoint
    message).etaBc * (inS lm lb bc rows pl sl hts chunks theta0 f rest r m1 fresh g chi qPoint
    message).slot 1 * (inS lm lb bc rows pl sl hts chunks theta0 f rest r m1 fresh g chi qPoint
    message).idx + (inS lm lb bc rows pl sl hts chunks theta0 f rest r m1 fresh g chi qPoint
    message).belowBc * ((inS lm lb bc rows pl sl hts chunks theta0 f rest r m1 fresh g chi qPoint
    message).etaBc * (inS lm lb bc rows pl sl hts chunks theta0 f rest r m1 fresh g chi qPoint
    message).slot 2 + p) =
    let L := letsS lm lb bc rows pl sl hts chunks theta0 f rest r m1 fresh g qPoint
    L.etaBc * L.slot.getD 1 0 * indexMle r + L.belowBc * (L.etaBc * L.slot.getD 2 0 + p) := by
  kernel_eq

theorem xBc_lets : (letsS lm lb bc rows pl sl hts chunks theta0 f rest r m1 fresh g qPoint).xBc =
    let L := letsS lm lb bc rows pl sl hts chunks theta0 f rest r m1 fresh g qPoint
    L.etaBc * L.slot.getD 1 0 * indexMle r + L.belowBc * (L.etaBc * L.slot.getD 2 0 + L.program) := by
  kernel_eq

theorem pFp_lets : (letsS lm lb bc rows pl sl hts chunks theta0 f rest r m1 fresh g qPoint).pFp =
    let L := letsS lm lb bc rows pl sl hts chunks theta0 f rest r m1 fresh g qPoint
    L.belowBc * L.frameProgram := by
  kernel_eq

end

/-- **`y_mem`, `x_bc`, `p_fp`.** -/
theorem sideIdentity : SideIdentity := by
  intro layout chunks theta0 drawn r m1 fresh splitv chi qPoint message hs
  have hp := programIdentity layout chunks theta0 drawn r m1 fresh splitv chi qPoint message hs
  obtain ⟨htab, hd, -, hsv, -, -⟩ := hs
  obtain ⟨lm, lb, bc, tbls, rows, pl, sl, hts⟩ := layout
  simp only at htab
  subst htab
  have hsv' : splitv.length = 36 := hsv
  dsimp only at hp ⊢
  rw [list_canon drawn 88 hd, list_canon_eq splitv 36 hsv'] at hp ⊢
  obtain ⟨hp1, hp2⟩ := Prod.ext_iff.mp hp
  refine ⟨yMem_eq .., ?_, ?_⟩
  · rw [gXBc, hp1, xBc_eq, xBc_lets]
  · rw [gPFp, hp2, pFp_lets]
    rfl

/-! ## The terminal's arguments -/

/-- `eq(point, 0)` is `Π (1 + x)`. -/
theorem eqKernel_getD_zero (pt : List E) : (eqKernel pt).getD 0 0 = prodE (pt.map (1 + ·)) := by
  induction pt using List.reverseRecOn with
  | nil => rfl
  | append_singleton pt r ih =>
    rw [LeanVM.Protocol.Hotwire.eqKernel_append, List.getD_append _ _ _ _ (by
        rw [List.length_map, LeanVM.Protocol.Hotwire.eqKernel_length]; positivity),
      LeanVM.Protocol.Hotwire.getD_map_mul, ih, List.map_append, prodE_append]
    simp [prodE]

/-- **The terminal's arguments.** -/
theorem terminalIdentity : TerminalIdentity := by
  intro layout chunks theta0 drawn r m1 fresh splitv chi qPoint message hs
  obtain ⟨-, -, hcert, hbase⟩ := rowIdentity layout chunks theta0 drawn r m1 fresh splitv chi qPoint
    message hs
  dsimp only at hcert hbase ⊢
  refine ⟨?_, ?_⟩
  · rw [gRest, ← hbase]
    exact congrArg (· * _) (eqKernel_getD_zero qPoint)
  · rw [hcert]
    refine List.map_congr_left fun n _ ↦ ?_
    exact congrArg (· * n) (mul_comm _ _)

/-! ## `linkTail`, its `let`s named -/

/-- **`linkTail` is `linkTailR`.** -/
theorem linkTailEq : LinkTailEq := by
  intro layout chunks theta0 drawn r m1 fresh split chi qPoint claim
  kernel_eq

end

end LeanVM.Guest.B1.Link.Arith
