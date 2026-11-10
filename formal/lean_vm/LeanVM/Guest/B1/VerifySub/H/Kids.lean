/-
  LeanVM.Guest.B1.VerifySub.H.Kids

  `verify_sub`'s sixteen callees on an honest child, each a `KidD`: their names, arguments, words
  read and results, from the child's segments (`ChildSegs`).
-/

module

public import LeanVM.Guest.B1.VerifySub.Segments
public import LeanVM.Guest.B1.VerifySub.Template
public import LeanVM.Guest.B1.VerifySub.WordsB
public import LeanVM.Guest.B1.Terminal.TermKids
public import LeanVM.Guest.B1.Placement.CertifyAt
public import LeanVM.Guest.B1.Tables.VtC.AMain
public import LeanVM.Guest.B1.Gkr.VbgAt
public import LeanVM.Guest.B1.KeccakGkr.LayerCLift
public import LeanVM.Guest.B1.Fs.Message

/-!
# The callees

On the own buffers' first words `bs` (allocation order, `vb bs i`: `claim_pool`, the stream,
`table_rows`, `dims_g`, `kappa_base`, `zeta`, `ood_z`, `ood_value`, `fp_w`, `chi`, `bc_point`,
`z_vals`, `slices`, the ring map's challenges, `c_table`) and the exponent tables at `sqE`
(`vsExpLin`, the window tables at `sqE + winTabAt`), the callees in call order (G:3600-3749):

0, 1. `g_power_of_word` on the rate's and the memory's log's words;
2. `log2_ceil_in_the_exponent__L0_L34` on the push blocks' total `g^pushT`: the bus depth;
3. `certify_placement` on `kappa_base`;
4. `log2_ceil_in_the_exponent__L15_L34` on the stack's total: `g^m`;
5. `grind_check__L15` on the out-of-domain grind's permutation (`oodSt`);
6. `squeeze_point_from__L{m}`: the out-of-domain point at `ood_z`;
7. `opening_message__L1_L1`: the point's value (stored at `ood_value`) and the bus grind's nonce,
   their permutation `busSt`;
8. `bus_grind_check__L{d - 16}` on `busSt`;
9. `verify_bus_gkr` on the stream past the out-of-domain and bus words, `zeta`;
10. `verify_tables` (`VtHonest.args`, `linL`), its GKR leaves where `verify_bus_gkr` returned them
    (`leavesB`);
11. `verify_keccak` on the stream past the tables, `chi`, the output lanes (in the stream, at the
    tables' evaluations), `z_vals`, `slices`;
12. `grind_check__L14` on the ring map's grind's permutation (`ringSt`);
13. `ring_switch_target` on `slices` and the ring map's challenges;
14. `open_stacked`'s candidate on the stream past the ring switch's nonce;
15. `check_opening_terminal`, on `certify_placement`'s offsets and `open_stacked`'s point buffers
    when they are what those return (`termOk`).
-/

namespace LeanVM.Guest.B1.VerifySub

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Node LeanVM.Guest.Memory

@[expose] public section

/-- Buffer `i`'s first word. -/
def vb (bs : List ℕ) (i : ℕ) : ℕ := bs.getD i 0

/-- The own buffers' sizes, the bus depth `d`. -/
def vsBufSizes (d : ℕ) : List ℕ :=
  [159, 8192, 6, 7, 8, d, 28, 1, 16, 34, 4, 78, 64, 16, 64]

/-- What `open_stacked` returns and the buffers it hands back (`Place/OsSpec`'s `OsOut`). -/
def vsOsOut (μ : ℕ) (w : Whir.WhirEnd) : List E → Main.Layout → Prop := fun rets Lout ↦
  ∃ b b1 : ℕ, rets = [w.target, ptr b, ptr b1, w.inner, w.residual] ∧
    Lout = [(b, w.point ++ List.replicate (Whir.pointCap - μ) 0),
      (b1, w.point.map (1 + ·) ++ List.replicate (Whir.pointCap - μ) 1)]

/-- The words in chunks of the given lengths. -/
def vsChunks : List ℕ → List E → List (List E)
  | [], _ => []
  | n :: ns, xs => xs.take n :: vsChunks ns (xs.drop n)

namespace ChildSegs

variable {bytecode : List K} {seed : Digest} {c : Child} (S : ChildSegs bytecode seed c)

/-! ## The honest values -/

/-- The stack's log. -/
def μs : ℕ := S.layout.stackLog

/-- The tables' heights. -/
def hs : List ℕ := Tables.tableHeightsOf S.rowsN

/-- The columns' logs. -/
def kappas : List ℕ := columnKappas S.logMem Tables.guestLogBytecode S.hs

/-- The push side's depth. -/
def d : ℕ := busDepth S.layout

/-- The push blocks' total. -/
def pushT : ℕ := ((List.range 54).map fun b ↦ 2 ^ pushKappa S.logMem S.hs b).sum

/-- The sponge the out-of-domain grind starts from: the root's two words absorbed. -/
def sR : Fs := (S.s1.absorb S.x0 dsObserve).absorb S.x1 dsObserve

/-- The out-of-domain grind's nonce and the point's value. -/
def oodN : E := S.xsO.getD 0 0
def oodV : E := S.xsO.getD 1 0

/-- The out-of-domain grind's permutation. -/
def oodSt : KeccakState := S.sR.nonceState S.oodN

/-- The out-of-domain point: the grind's challenge, then `m - 1` squeezes. -/
def oodZ : List E := challengeOf S.oodSt :: ((⟨capOf S.oodSt, []⟩ : Fs).squeezeN (S.μs - 1)).1

/-- The sponge after the point. -/
def sZ : Fs := ((⟨capOf S.oodSt, []⟩ : Fs).squeezeN (S.μs - 1)).2

/-- The bus grind's nonce. -/
def busN : E := S.xsB.getD 0 0

/-- The bus grind's permutation: the value absorbed, then the nonce. -/
def busSt : KeccakState := omState S.sZ.cap [S.oodV] (some S.busN)

/-- The tables' rounds: the largest height. -/
def nT : ℕ := S.hs.foldl max 0

/-- **`verify_tables`' honest data**, the tables' words split. -/
noncomputable def H : Tables.VtHonest :=
  ⟨bytecode, S.logMem, Node.statementDigest seed c.statement, S.wb.1, S.rG.2.1, S.rG.2.2, S.wb.2,
    S.rowsN, S.s4.cap, claimedBytecodeValue c.freshClaim, S.xsT.take 4, (S.xsT.drop 4).take 10,
    (S.xsT.drop 14).take (3 * S.nT), vsChunks (tables.map (·.width)) (S.xsT.drop (14 + 3 * S.nT)),
    S.bus, S.claims, S.s5.cap⟩

/-- The Keccak table's height. -/
def τ : ℕ := S.layout.tableLogHeights.getD opKeccak 0

/-- The Keccak reduction's claim on its committed outputs. -/
def kOut : ColumnClaim := S.kc.1.getLastD default

/-- The output lanes' values. -/
def outs : List E := (lanesOf S.claims).map (·.value)

/-- The ring map's grind's nonce and permutation. -/
def ringN : E := S.xsR.getD 0 0
def ringSt : KeccakState := S.s6.nonceState S.ringN

/-- The ring map's challenges: the grind's challenge, then fifteen squeezes. -/
def rchs : List E := challengeOf S.ringSt :: ((⟨capOf S.ringSt, []⟩ : Fs).squeezeN 15).1

/-- The batching challenge. -/
def lam : E := S.s7.squeeze.1

/-- The opening's target. -/
noncomputable def target : E := batchTarget (stackClaims S.layout S.kc.1 S.rs.1 S.rs.2 S.ood) S.lam

/-! ## The cursors and buffers -/

variable (bs : List ℕ)

/-- The GKR's cursor: past the announced words, the root, the two grinds' nonces and the value. -/
def cG : ℕ := vb bs 1 + 13

/-- The tables' cursor. -/
def cT : ℕ := cG bs + S.xsG.length

/-- The Keccak reduction's cursor. -/
def cK : ℕ := S.cT bs + S.xsT.length

/-- The ring switch's cursor (its nonce), and the opening's. -/
def cR : ℕ := S.cK bs + S.xsK.length
def cW : ℕ := S.cR bs + S.xsR.length

/-- The tables' evaluations' cursor (`col_eval_words`). -/
def cE : ℕ := S.cT bs + 13 + 1 + 3 * S.nT

/-- The output lanes' cursor: `col_eval_words·g^101` (`KECCAK_OUT_POOL - N_BUS_CLAIMS`). -/
def cL : ℕ := S.cE bs + 101

/-- `verify_tables`' buffers, its GKR leaves at `leaves`. -/
def vtB (sqE leaves : ℕ) : Tables.VtBases :=
  ⟨S.cT bs, vb bs 5, vb bs 3, vb bs 2, sqE, vb bs 8, vb bs 0, vb bs 9, leaves, vb bs 10, 0⟩

/-- `verify_bus_gkr`'s result among the results before. -/
def gkRes (pv : List (List E × Main.Layout)) : List E × Main.Layout := pv.getD 9 ([], [])

/-- `certify_placement`'s result among the results before. -/
def cpRes (pv : List (List E × Main.Layout)) : List E × Main.Layout := pv.getD 3 ([], [])

/-- `open_stacked`'s result among the results before. -/
def osRes (pv : List (List E × Main.Layout)) : List E × Main.Layout := pv.getD 14 ([], [])

open Classical in
/-- Where `verify_bus_gkr` returned the GKR leaves. -/
noncomputable def leavesB (pv : List (List E × Main.Layout)) : ℕ :=
  if h : ∃ b, (gkRes pv).1.getD 6 0 = ptr b ∧ (b, S.rG.2.2) ∈ (gkRes pv).2 then
    Classical.choose h else 0

/-- The terminal is entered on what `certify_placement` and `open_stacked` return. -/
def termOk (pv : List (List E × Main.Layout)) : Prop :=
  Tables.cpOut S.logMem S.hs (cpRes pv).1 (cpRes pv).2 ∧
    vsOsOut S.μs S.w (osRes pv).1 (osRes pv).2

open Classical in
/-- The bases the terminal reads `certify_placement`'s and `open_stacked`'s buffers at. -/
noncomputable def termBs (pv : List (List E × Main.Layout)) : ℕ × ℕ × ℕ :=
  if h : ∃ e b b1 : ℕ, (cpRes pv).1.getD 1 0 = ptr e ∧ (osRes pv).1.getD 1 0 = ptr b ∧
      (osRes pv).1.getD 2 0 = ptr b1 then
    (Classical.choose h, Classical.choose (Classical.choose_spec h),
      Classical.choose (Classical.choose_spec (Classical.choose_spec h)))
  else (0, 0, 0)

/-- The terminal's bases. -/
noncomputable def termB (sqE : ℕ) (pv : List (List E × Main.Layout)) : TermBases :=
  ⟨sqE, vb bs 5, vb bs 9, vb bs 4, (termBs pv).1, vb bs 11, vb bs 14, (termBs pv).2.1,
    (termBs pv).2.2, vb bs 6⟩

/-- The terminal's words: `zeta`, `chi`, `kappa_base`, the exponent tables, `z_vals`, `c_table`,
`ood_z`. -/
noncomputable def termLin (sqE : ℕ) : Main.Layout :=
  [(vb bs 5, S.rG.2.1), (vb bs 9, S.H.chiW), (vb bs 4, 1 :: gen ^ S.logMem :: S.hs.map (gen ^ ·)),
    (sqE, expTabAllWords), (vb bs 11, S.kOut.point ++ List.replicate (qkeccakVarsCap -
      S.kOut.point.length) 0 ++ S.kc.2.1), (vb bs 14, ringCoefficients (S.rchs.take ringMapWidth)
        (S.rchs.drop ringMapWidth)), (vb bs 6, S.oodZ)]

/-- **`verify_sub`'s callees on an honest child.** -/
noncomputable def kids (sqE : ℕ) : List KidD :=
  [fun _ ↦ ⟨"g_power_of_word", true, [eOfNat S.rate], [], Returns [gen ^ S.rate]⟩,
    fun _ ↦ ⟨"g_power_of_word", true, [eOfNat S.logMem], [], Returns [gen ^ S.logMem]⟩,
    fun _ ↦ ⟨"log2_ceil_in_the_exponent__L0_L34", true, [gen ^ S.pushT, ptr sqE], log2Lin sqE,
      Returns [gen ^ max 0 (log2Ceil S.pushT)]⟩,
    fun _ ↦ ⟨"certify_placement", true, [ptr (vb bs 4), ptr sqE],
      Tables.cpLin S.logMem S.hs (vb bs 4) sqE, Tables.cpOut S.logMem S.hs⟩,
    fun _ ↦ ⟨"log2_ceil_in_the_exponent__L15_L34", true,
      [gen ^ Tables.stackTotal S.kappas, ptr sqE], log2Lin sqE,
      Returns [gen ^ max 15 (log2Ceil (Tables.stackTotal S.kappas))]⟩,
    fun _ ↦ ⟨"grind_check__L15", true, [cellsOfState S.oodSt false 1, ptr sqE * gen ^ winTabAt],
      vsExpLin sqE, Returns []⟩,
    fun _ ↦ ⟨squeezeNames.getD (S.μs - 22) "", true,
      capOf S.oodSt ++ [challengeOf S.oodSt, ptr (vb bs 6)], [(vb bs 6, S.oodZ)], Returns S.sZ.cap⟩,
    fun _ ↦ ⟨"opening_message__L1_L1", true, S.sZ.cap ++ [ptr (vb bs 1) * gen ^ 11, ptr (vb bs 7)],
      [(vb bs 1 + 11, [S.oodV, S.busN]), (vb bs 7, [S.oodV])],
      Returns ([cellsOfState S.busSt false 0, cellsOfState S.busSt false 1] ++ capOf S.busSt ++
        [ptr (vb bs 1) * gen ^ 11 * gen ^ 2])⟩,
    fun _ ↦ ⟨busGrindNames.getD (S.d - 16) "", true,
      [cellsOfState S.busSt false 1, ptr sqE * gen ^ winTabAt], vsExpLin sqE, Returns [0]⟩,
    fun _ ↦ ⟨"verify_bus_gkr", true,
      S.s3.cap ++ [ptr (cG bs), gen ^ S.d, ptr (vb bs 5), ptr sqE * gen ^ winTabAt],
      [(cG bs, S.xsG), (vb bs 5, S.rG.2.1)],
      Tables.VbgOut S.s4.cap (ptr (cG bs) * gen ^ S.xsG.length) S.rG.2.2⟩,
    fun pv ↦ ⟨"verify_tables", true, S.H.args (S.vtB bs sqE (S.leavesB pv)),
      S.H.linL (S.vtB bs sqE (S.leavesB pv)), Returns (S.H.retsH (S.vtB bs sqE (S.leavesB pv)))⟩,
    fun _ ↦ ⟨"verify_keccak", true,
      S.H.s3.squeeze.2.cap ++ [ptr (S.cK bs), gen ^ S.τ, ptr (vb bs 9), ptr (S.cL bs),
        ptr (vb bs 11), ptr (vb bs 12), ptr (sqE + winTabAt)],
      [(S.cK bs, S.xsK), (vb bs 9, S.H.chiW), (S.cL bs, S.outs), (vb bs 11, S.kOut.point),
        (vb bs 11 + qkeccakVarsCap, S.kc.2.1), (vb bs 12, S.kc.2.2),
        (sqE + winTabAt, winTabWords)],
      Returns (capOf S.s6.perm ++ [ptr (S.cK bs) * gen ^ S.xsK.length, S.kOut.value])⟩,
    fun _ ↦ ⟨"grind_check__L14", true, [cellsOfState S.ringSt false 1, ptr sqE * gen ^ winTabAt],
      vsExpLin sqE, Returns []⟩,
    fun _ ↦ ⟨"ring_switch_target", true, [ptr (vb bs 12), ptr (vb bs 13)],
      [(vb bs 12, S.kc.2.2), (vb bs 13, S.rchs)],
      Returns [ringTarget S.kc.2.2 (S.rchs.take ringMapWidth) (S.rchs.drop ringMapWidth)]⟩,
    fun _ ↦ ⟨Whir.openName S.μs S.rate, true,
      capOf S.s7.perm ++ [S.target, (digestHalves S.root).1, (digestHalves S.root).2,
        ptr (S.cW bs), ptr sqE * gen ^ winTabAt],
      [(S.cW bs, S.xsW), (sqE, expTabAllWords)], vsOsOut S.μs S.w⟩,
    fun pv ↦
      open Classical in
      ⟨"check_opening_terminal", decide (S.termOk pv),
        termArgs (termB bs sqE pv) S.H.rm (gen ^ S.d) (gen ^ S.nT) (gen ^ S.logMem)
          (gen ^ S.τ) S.lam S.w.inner S.w.residual S.w.target
          (gen ^ max 15 (log2Ceil (Tables.stackTotal S.kappas))),
        if S.termOk pv then (cpRes pv).2 ++ (osRes pv).2 ++ S.termLin bs sqE else [],
        Returns []⟩]

theorem kids_length (sqE : ℕ) : (S.kids bs sqE).length = 16 := rfl

end ChildSegs

end
end LeanVM.Guest.B1.VerifySub
