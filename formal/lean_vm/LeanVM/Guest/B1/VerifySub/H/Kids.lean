/-
  LeanVM.Guest.B1.VerifySub.H.Kids

  `verify_sub`'s thirteen callees on an honest child, each a `KidD` (the terminal on the results of
  `certify_placement` and `open_stacked`): their names, arguments, words read and results.
-/

module

public import LeanVM.Guest.B1.VerifySub.H.Own
public import LeanVM.Guest.B1.Terminal.KidsDep
public import LeanVM.Guest.B1.Placement.CertifyAt
public import LeanVM.Guest.B1.Whir.Interface
public import LeanVM.Guest.B1.Bits.Log2Placed

/-!
# The callees

On the buffers' first words `bs` (`b i`, allocation order: `claim_pool`, the stream, `table_rows`,
`dims_g`, `kappa_base`, `zeta`, `bus_alpha`, `fp_w`, `chi`, `z_vals`, `slices`, the ring map's
challenges, `c_table`) and the exponent table at `sqE` (G:3318-3436, at 40f877dc):

0, 1. `g_power_of_word` on the rate's and the memory's log's words;
2. `log2_ceil_in_the_exponent__L0_L34` on `g^(push total)`;
3, 4. `assert_canonical` on the root's two words;
5. `verify_bus_gkr` on the stream past the announced words and the root, `zeta`;
6. `verify_tables` (B1-c's `VtHonest.args`, `linL` at `vtB`), returning `vtRetsOf` (its ten
   returns, the last `col_eval_words`, the stream's cursor at the tables' evaluations);
7. `verify_keccak` on the stream past the tables' words, `chi`, the output lanes (in the stream, at
   `col_eval_words·g^107`), `z_vals`, `slices`;
8. `ring_switch_target` on `slices` and the ring map's challenges;
9. `certify_placement` on `kappa_base` and the exponent table;
10. `log2_ceil_in_the_exponent__L15_L34` on `g^(stack total)`;
11. `open_stacked`'s candidate on the stream past the Keccak reduction's words;
12. `check_opening_terminal`, on `certify_placement`'s buffers and `open_stacked`'s points when
    they are what those return (`termOk`).
-/

namespace LeanVM.Guest.B1.VerifySub

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Node LeanVM.Guest.Memory

@[expose] public section

/-- What `open_stacked` returns and the buffers it hands back (B1-b's `OsOut`, `Place/OsFinal`). -/
def vsOsOut (μ : ℕ) (w : Whir.WhirEnd) : List E → Main.Layout → Prop := fun rets Lout ↦
  ∃ b b1 : ℕ, rets = [w.target, ofK (addressOfIndex b), ofK (addressOfIndex b1), w.inner,
      w.residual] ∧
    Lout = [(b, w.point ++ List.replicate (Whir.pointCap - μ) 0),
      (b1, w.point.map (1 + ·) ++ List.replicate (Whir.pointCap - μ) 1)]

/-- Buffer `i`'s first word. -/
def vb (bs : List ℕ) (i : ℕ) : ℕ := bs.getD i 0

/-- The GKR's cursor: past the announced words and the root. -/
def vcG (bs : List ℕ) : ℕ := vb bs 1 + 10

namespace ChildSegs

variable {bytecode : List K} {seed : Digest} {c : Child} (S : ChildSegs bytecode seed c)

/-- The stack's log. -/
def μs : ℕ := S.layout.stackLog

/-- The columns' logs. -/
def kappas : List ℕ := columnKappas S.logMem Tables.guestLogBytecode S.hs

/-- The opening's target. -/
noncomputable def target : E :=
  batchTarget (stackClaims S.layout S.claims S.km.1.1 S.km.1.2.1 S.km.1.2.2 (S.km.2 :: S.chs))
    S.lam

variable (bs : List ℕ)

/-- The tables' cursor. -/
def cT : ℕ := vcG bs + S.xsG.length

/-- The Keccak reduction's cursor. -/
def cK : ℕ := S.cT bs + S.xsT.length

/-- The opening's cursor. -/
def cW : ℕ := S.cK bs + S.xsK.length

/-- The output lanes' cursor: `col_eval_words·g^107`, the tables' evaluations past the five
framework words and the rounds' `3 n`. -/
noncomputable def cL : ℕ := S.cT bs + 5 + 3 * S.H.n + 107

/-- `verify_tables`' buffers. -/
def vtB (sqE : ℕ) : Tables.VtBases :=
  ⟨S.cT bs, vb bs 5, vb bs 3, vb bs 2, sqE, vb bs 7, vb bs 0, vb bs 8, 0⟩

/-- `verify_tables`' honest returns: the capacity, the cursor past its words, `g^n`, the
bytecode's value, the public input's point, `col_eval_words`. -/
noncomputable def vtRetsOf : List E :=
  S.H.s3.squeeze.2.cap ++ [ofK (addressOfIndex (S.cT bs)) * gen ^ 5 * gen ^ (3 * S.H.n) * gen ^ 159,
    gen ^ S.H.n, S.H.bv, S.H.rm, ofK (addressOfIndex (S.cT bs)) * gen ^ 5 * gen ^ (3 * S.H.n)]

/-- `certify_placement`'s result among the results before. -/
def cpRes (pv : List (List E × Main.Layout)) : List E × Main.Layout := pv.getD 9 ([], [])

/-- `open_stacked`'s result among the results before. -/
def osRes (pv : List (List E × Main.Layout)) : List E × Main.Layout := pv.getD 11 ([], [])

/-- The terminal is entered on what `certify_placement` and `open_stacked` return. -/
def termOk (pv : List (List E × Main.Layout)) : Prop :=
  Tables.cpOut S.logMem S.hs (cpRes pv).1 (cpRes pv).2 ∧ vsOsOut S.μs S.w (osRes pv).1 (osRes pv).2

/-- The terminal's own words: `zeta`, `chi`, `kappa_base`, the exponent table (the selectors'
nibble shares at `g_squares·g^34`), `z_vals`, `c_table`. -/
noncomputable def termLin (sqE : ℕ) : Main.Layout :=
  [(vb bs 5, S.point), (vb bs 8, S.chis), (vb bs 4, vsKbW S.logMem S.hs), (sqE, expTableWords),
    (vb bs 9, zvW S.op S.kpt), (vb bs 12, ringCoefficients S.rchs)]

/-- **`verify_sub`'s callees on an honest child.** -/
noncomputable def kids (sqE : ℕ) : List KidD :=
  [fun _ ↦ ⟨"g_power_of_word", true, [eOfNat S.rate], [], Returns [gen ^ S.rate]⟩,
    fun _ ↦ ⟨"g_power_of_word", true, [eOfNat S.logMem], [], Returns [gen ^ S.logMem]⟩,
    fun _ ↦ ⟨"log2_ceil_in_the_exponent__L0_L34", true,
      [gen ^ pushTotal S.logMem S.hs, ofK (addressOfIndex sqE)], log2Lin sqE,
      Returns [gen ^ max 0 (log2Ceil (pushTotal S.logMem S.hs))]⟩,
    fun _ ↦ ⟨"assert_canonical", true, [S.x0], [], Returns [0]⟩,
    fun _ ↦ ⟨"assert_canonical", true, [S.x1], [], Returns [0]⟩,
    fun _ ↦ ⟨"verify_bus_gkr", true,
      S.capS ++ [ofK (addressOfIndex (vcG bs)), gen ^ S.μ, ofK (addressOfIndex (vb bs 5))],
      [(vcG bs, S.xsG), (vb bs 5, S.point)],
      Returns (S.s5.cap ++ [ofK (addressOfIndex (vcG bs)) * gen ^ S.xsG.length] ++ S.vals)⟩,
    fun _ ↦ ⟨"verify_tables", true, S.H.args (S.vtB bs sqE), S.H.linL (S.vtB bs sqE),
      Returns (S.vtRetsOf bs)⟩,
    fun _ ↦ ⟨"verify_keccak", true,
      S.s6.cap ++ [ofK (addressOfIndex (S.cK bs)), gen ^ S.τ, ofK (addressOfIndex (vb bs 8)),
        ofK (addressOfIndex (S.cL bs)), ofK (addressOfIndex (vb bs 9)),
        ofK (addressOfIndex (vb bs 10))],
      [(S.cK bs, S.xsK), (vb bs 8, S.chis), (S.cL bs, S.outs), (vb bs 9, S.op),
        (vb bs 9 + qkeccakVarsCap, S.kpt), (vb bs 10, S.slices)],
      Returns (S.s7.cap ++ [ofK (addressOfIndex (S.cK bs)) * gen ^ S.xsK.length, S.word, S.m0])⟩,
    fun _ ↦ ⟨"ring_switch_target", true,
      [ofK (addressOfIndex (vb bs 10)), ofK (addressOfIndex (vb bs 11))],
      [(vb bs 10, S.slices), (vb bs 11, S.rchs)],
      Returns [polyEval (S.slices.map (phiMap · S.rchs)) gen]⟩,
    fun _ ↦ ⟨"certify_placement", true, [ofK (addressOfIndex (vb bs 4)), ofK (addressOfIndex sqE)],
      Tables.cpLin S.logMem S.hs (vb bs 4) sqE, Tables.cpOut S.logMem S.hs⟩,
    fun _ ↦ ⟨"log2_ceil_in_the_exponent__L15_L34", true,
      [gen ^ Tables.stackTotal S.kappas, ofK (addressOfIndex sqE)], log2Lin sqE,
      Returns [gen ^ max 15 (log2Ceil (Tables.stackTotal S.kappas))]⟩,
    fun _ ↦ ⟨B1.Whir.openName S.μs S.rate, true,
      capOf S.s8.perm ++ [S.target, (digestHalves S.root).1, (digestHalves S.root).2,
        ofK (addressOfIndex (S.cW bs))],
      [(S.cW bs, S.xsW)], vsOsOut S.μs S.w⟩,
    fun pv ↦
      open Classical in
      ⟨"check_opening_terminal", decide (S.termOk pv),
        [ofK (addressOfIndex sqE), ofK (addressOfIndex (vb bs 5)), ofK (addressOfIndex (vb bs 8)),
          S.H.rm, gen ^ S.μ, gen ^ S.H.n, gen ^ S.logMem, gen ^ S.τ,
          ofK (addressOfIndex (vb bs 4)), S.lam, (cpRes pv).1.getD 1 0,
          ofK (addressOfIndex (vb bs 9)), ofK (addressOfIndex (vb bs 12)),
          (osRes pv).1.getD 1 0, (osRes pv).1.getD 2 0, (osRes pv).1.getD 3 0,
          (osRes pv).1.getD 4 0, (osRes pv).1.getD 0 0],
        if S.termOk pv then (cpRes pv).2 ++ (osRes pv).2 ++ S.termLin bs sqE else [],
        Returns []⟩]

theorem vtRetsOf_getD9 : (S.vtRetsOf bs).getD 9 0 =
    ofK (addressOfIndex (S.cT bs)) * gen ^ 5 * gen ^ (3 * S.H.n) := by
  have hc : S.H.s3.squeeze.2.cap.length = 5 := rfl
  rw [vtRetsOf, List.getD_append_right _ _ _ _ (by omega), hc]
  rfl

theorem cT_eq : S.cT bs = bs.getD 1 0 + (10 + S.xsG.length) := by
  simp only [cT, vcG, vb]; omega

theorem kids_length (sqE : ℕ) : (S.kids bs sqE).length = 13 := rfl

end ChildSegs

end
end LeanVM.Guest.B1.VerifySub
