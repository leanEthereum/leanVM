/-
  LeanVM.Guest.B1.VerifySub.CPlaced0

  `verify_sub` placed: its `HeapBuf`s at the allocator's bases and their honest words, the
  tables' context of the run, and the path of its body (straight-line around one dispatch).
-/

module

public import LeanVM.Guest.B1.VerifySub.CGroup1
public import LeanVM.Guest.B1.Tables.TCtx

/-!
# `verify_sub` placed: buffers and path

* `vsSizes`, `vsBufs`: the nineteen `HeapBuf`s' sizes and honest words, in allocation order;
  `vsPtrsAt`: the pointers at the allocator's bases from `fp + fs "verify_sub"`;
* `VsData.TOk`: what the run's tables hand the terminal (the claims' columns and points, each
  point of its column's length, the sumcheck's point `chis`) and the stream's bound, which the
  honest memory needs;
* `vsBody_split`: the body is a straight-line prefix, the dispatch on the stack's size, and a
  straight-line suffix, with its `HeapBuf` hints, frames and loads read off by the kernel.
-/

namespace LeanVM.Guest.B1.VerifySub

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.Blake2sHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Guest.Memory

@[expose] public section

/-! ## The tables' context and the bounds -/

/-- **What the run's tables hand the terminal**, and the stream's bound. -/
structure VsData.TOk (bytecode : List K) (D : VsData) : Prop where
  chis_le : D.chis.length ≤ D.gr.2.1.length
  gzcn : D.gzcn = gen ^ D.chis.length
  columns : D.claims.map (·.column) = claimColumns
  points : ∀ j (p : List E), (D.claims.map (·.point))[j]? = some p →
    (j < 5 → p = D.gr.2.1.take p.length) ∧ (5 ≤ j → j < nPooled → p = D.chis.take p.length) ∧
      (nPooled ≤ j → p = D.rm :: List.replicate
        (((layoutOf bytecode D.logMem D.rows).placements.getD memory0 default).vars - 1) 0)
  stream_le : D.stream.length ≤ 8192
  point_vars : ∀ c ∈ D.claims,
    c.point.length = ((layoutOf bytecode D.logMem D.rows).placements.getD c.column default).vars
  chis_len : D.chis.length = (layoutOf bytecode D.logMem D.rows).tableLogHeights.foldl max 0

/-- **The tables' claims as the terminal reads them**: the claims' columns, their points (the
bus's a prefix of the GKR point `point`, the pooled ones a prefix of the sumcheck's point `chis`,
the public input's `rm` then zeros), each point of its column's length, and `chis` no longer than
`point`. -/
def TablesClaimsOk (layout : Layout) (point : List E) (claims : List ColumnClaim) (chis : List E)
    (rm : E) : Prop :=
  chis.length ≤ point.length ∧ claims.map (·.column) = claimColumns ∧
    (∀ j (p : List E), (claims.map (·.point))[j]? = some p →
      (j < 5 → p = point.take p.length) ∧ (5 ≤ j → j < nPooled → p = chis.take p.length) ∧
        (nPooled ≤ j → p = rm :: List.replicate ((layout.placements.getD memory0 default).vars - 1) 0)) ∧
    ∀ c ∈ claims, c.point.length = (layout.placements.getD c.column default).vars

theorem VsData.TOk.of_claims {bytecode : List K} {D : VsData}
    (h : TablesClaimsOk (layoutOf bytecode D.logMem D.rows) D.gr.2.1 D.claims D.chis D.rm)
    (hg : D.gzcn = gen ^ D.chis.length) (hs : D.stream.length ≤ 8192)
    (hc : D.chis.length = (layoutOf bytecode D.logMem D.rows).tableLogHeights.foldl max 0) :
    D.TOk bytecode :=
  ⟨h.1, hg, h.2.1, h.2.2.1, hs, h.2.2.2, hc⟩

/-- The claims' point lengths in `claim_cplen_g`. -/
def cplenWords (D : VsData) : List E := (D.claims.take nPooled).map fun c => gen ^ c.point.length

/-! ## The buffers -/

/-- The `HeapBuf`s' sizes, in allocation order (G:2092-2228). -/
def vsSizes (D : VsData) : List ℕ :=
  [112, 112, 8192, 6, 7, 8, 102, D.gr.2.1.length, 4, 16, 34, D.tau + 8, 8, 64, 6, 64, 41, 130, 112]

/-- Their honest words. -/
def vsBufs (D : VsData) : List (List E) :=
  [D.claims.map (·.value), cplenWords D, D.stream, D.rows.map eOfNat,
    gen ^ D.logMem :: D.hs.map (gen ^ ·), kappaBase (gen ^ D.logMem) (D.hs.map (gen ^ ·)),
    blockKappas (gen ^ D.logMem) (D.hs.map (gen ^ ·)), D.gr.2.1, D.alphas, eqKernel D.alphas, D.chis,
    D.chi, D.rcs, D.s, D.mcs, ringCoefficients D.mcs, D.fpoint, D.rsChain,
    powersFrom D.lam D.lam nClaims]

/-- The allocator's bases from `b`. -/
def vsBases (D : VsData) (b : ℕ) : List ℕ := bases b (vsSizes D)

/-- The `HeapBuf` pointers at `fp`, the returned buffers' given. -/
def vsPtrsAt (fs : String → ℕ) (fp : ℕ) (D : VsData) (off kap pt : E) : VsPtrs :=
  let B := fun i => ofK (Parameters.gpow ((vsBases D (fp + fs "verify_sub")).getD i 0))
  ⟨B 0, B 1, B 2, B 3, B 4, B 5, B 6, B 7, B 8, B 9, B 10, B 11, B 12, B 13, B 14, B 15, B 16, B 17,
    B 18, 0, 0, 0, 0, 0, 0, off, kap, pt, [], [], [], [], [], []⟩

/-! ## The path -/

/-- The statements before the dispatch. -/
noncomputable def vsPre1 : List Stmt := vsBody.take 1926

/-- The dispatch on the stack's size (G:2246-2252). -/
def vsDisp : Stmt :=
  .dispatch (.n 1643) openNames [.n 1171, .n 1172, .n 1627, .n 419, .n 434, .n 726]
    [.n 1648, .n 1649, .n 1650, .n 1651]

/-- The statements after it. -/
noncomputable def vsPost2 : List Stmt := vsBody.drop 1927

set_option maxRecDepth 100000 in
theorem vsBody_split : vsBody = vsPre1 ++ vsDisp :: vsPost2 := stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem vsPre1_straight : vsPre1.all Main.Stmt.straight = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem vsPost2_straight : vsPost2.all Main.Stmt.straight = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem vsPre1_allocs : vsPre1.filterMap Main.Stmt.allocSz =
    [(.n 7, .inl 112), (.n 8, .inl 112), (.n 14, .inl 8192), (.n 30, .inl 6), (.n 143, .inl 7),
      (.n 155, .inl 8), (.n 163, .inl 102), (.n 418, .inr (.n 417)), (.n 451, .inl 4),
      (.n 508, .inl 16), (.n 709, .inl 34), (.n 721, .inr (.n 720)), (.n 722, .inl 8),
      (.n 723, .inl 64), (.n 732, .inl 6), (.n 733, .inl 64), (.n 734, .inl 41),
      (.n 1144, .inl 130), (.n 1180, .inl 112)] := by decide +kernel

set_option maxRecDepth 100000 in
theorem vsPost2_allocs : vsPost2.filterMap Main.Stmt.allocSz = [] := by decide +kernel

set_option maxRecDepth 100000 in
theorem vsPre1_addrs : vsPre1.filterMap Main.Stmt.addrS = [] := by decide +kernel

set_option maxRecDepth 100000 in
theorem vsPost2_addrs : vsPost2.filterMap Main.Stmt.addrS = [] := by decide +kernel

set_option maxRecDepth 100000 in
theorem vsPre1_calls : vsPre1.filterMap Main.Stmt.callS =
    [(none, "g_power_of_word__L6", [.n 121, .n 5], [.n 136]),
      (none, "g_power_of_word__L6", [.n 15, .n 5], [.n 144]),
      (none, "log2_ceil_in_the_exponent__L0_L34", [.n 416, .n 4, .n 5], [.n 417]),
      (none, "assert_canonical", [.n 419], [.n 449]), (none, "assert_canonical", [.n 434], [.n 450]),
      (none, "verify_bus_gkr", [.n 690, .n 691, .n 700, .n 417, .n 418],
        [.n 701, .n 702, .n 703, .n 704, .n 705, .n 706]),
      (none, "verify_tables", [.n 707, .n 708, .n 703, .n 0, .n 1, .n 418, .n 417, .n 143, .n 30,
        .n 163, .n 5, .n 508, .n 698, .n 7, .n 8, .n 709, .n 704, .n 705, .n 706],
        [.n 710, .n 711, .n 712, .n 713, .n 714, .n 715]),
      (none, "verify_flock", [.n 716, .n 717, .n 712, .n 718, .n 721, .n 722, .n 723],
        [.n 724, .n 725, .n 726, .n 727, .n 728, .n 729]),
      (none, "__loop84", [.n 1147, .n 723, .n 732, .n 1144], []),
      (some (.n 1160), "__loop85", [.n 1161, .n 718, .n 1163, .n 1165], []),
      (none, "certify_placement", [.n 155, .n 5], [.n 1629, .n 1630, .n 1631]),
      (none, "log2_ceil_in_the_exponent__L15_L34", [.n 1629, .n 4, .n 5], [.n 1632])] := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem vsPost2_calls : vsPost2.filterMap Main.Stmt.callS =
    [(none, "check_opening_terminal", [.n 418, .n 709, .n 715, .n 417, .n 713, .n 144, .n 718, .n 8,
      .n 1180, .n 1630, .n 1631, .n 734, .n 733, .n 1649, .n 1650, .n 1651, .n 1648], [])] := by
  decide +kernel

/-- Where a load of the body reads: through one of `verify_sub`'s buffers below its size, through
`defer_out` below `106`, or through a push block's pointer into `g_squares` at offset `0`. -/
def loadOkB (q : V × ℕ) : Bool :=
  let (p, off) := q
  (p == .n 7 && decide (off < 112)) || (p == .n 14 && decide (off < 10)) ||
    (p == .n 30 && decide (off < 6)) || (p == .n 143 && decide (off < 7)) ||
    (p == .n 155 && decide (off < 8)) || (p == .n 163 && decide (off < 102)) ||
    (p == .n 418 && decide (off < 18)) || (p == .n 451 && decide (off < 4)) ||
    (p == .n 508 && decide (off < 16)) || (p == .n 721 && decide (off < 8)) ||
    (p == .n 722 && decide (off < 8)) || (p == .n 723 && decide (off < 64)) ||
    (p == .n 732 && decide (off < 6)) || (p == .n 733 && decide (off < 64)) ||
    (p == .n 734 && decide (off < 8)) || (p == .n 1144 && decide (off < 2)) ||
    (p == .n 1149 && off == 1) || (p == .n 1180 && decide (off < 112)) ||
    (p == .n 6 && decide (off < 106)) ||
    ((List.range 37).any fun b => p == .n (pushK b + 1)) && off == 0

set_option maxRecDepth 100000 in
theorem vsPre1_loads : (vsPre1.filterMap Stmt.loadS).all loadOkB = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem vsPost2_loads : (vsPost2.filterMap Stmt.loadS).all loadOkB = true := by decide +kernel

end
end LeanVM.Guest.B1.VerifySub
