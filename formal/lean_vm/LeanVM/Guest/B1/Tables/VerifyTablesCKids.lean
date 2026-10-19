/-
  LeanVM.Guest.B1.Tables.VerifyTablesCKids

  `verify_tables`' 205 buffers' pointers and its 75 callees, as the placed form reads them.
-/

module

public import LeanVM.Guest.B1.Tables.VerifyTablesCOwn
public import LeanVM.Guest.B1.Tables.VtCPad
public import LeanVM.Guest.B1.Uniform
public import LeanVM.Guest.B1.Tables.FlatAt
public import LeanVM.Guest.B1.Tables.VerifyTablesCAt
public import LeanVM.Guest.B1.Tables.VerifyTablesCTrace

/-!
# Pointers and callees

`vtAllocVar`: the values the 205 `HeapBuf` hints set, in order; `vtPtr b n i` the `i`-th pointer
from the base `b`. `vtKids`: the six dispatched padding weights, then the 69 loops in order (the
65 selectors, the two index chains after selectors `1` and `2`, `__loop79`, `__loop80`), on the
caller's words and the buffers.
-/

namespace LeanVM.Guest.B1.VerifySub

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.Blake2sHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Guest.Memory
open LeanVM.Guest.B1.Main (MemL RegionL)

@[expose] public section

/-- The values the `HeapBuf` hints set, in allocation order. -/
def vtAllocVar : List ℕ :=
  [24, 25, 128, 1817, 1852, 1867, 1870, 1871, 1905, 1908, 1909, 1925, 2009, 2012, 2013, 2029,
    2089, 2092, 2093, 2118, 2121, 2122, 2147, 2150, 2151, 2176, 2179, 2180, 2205, 2208, 2209, 2234,
    2237, 2238, 2263, 2266, 2267, 2292, 2295, 2296, 2321, 2324, 2325, 2350, 2353, 2354, 2379, 2382,
    2383, 2408, 2411, 2412, 2437, 2440, 2441, 2466, 2469, 2470, 2495, 2498, 2499, 2524, 2527, 2528,
    2553, 2556, 2557, 2582, 2585, 2586, 2611, 2614, 2615, 2640, 2643, 2644, 2669, 2672, 2673, 2698,
    2701, 2702, 2727, 2730, 2731, 2756, 2759, 2760, 2785, 2788, 2789, 2814, 2817, 2818, 2843, 2846,
    2847, 2872, 2875, 2876, 2901, 2904, 2905, 2930, 2933, 2934, 2959, 2962, 2963, 2988, 2991, 2992,
    3017, 3020, 3021, 3046, 3049, 3050, 3718, 3721, 3722, 3746, 3749, 3750, 3775, 3778, 3779, 3804,
    3807, 3808, 3833, 3836, 3837, 3862, 3865, 3866, 3891, 3894, 3895, 3920, 3923, 3924, 3949, 3952,
    3953, 3978, 3981, 3982, 4007, 4010, 4011, 4036, 4039, 4040, 4065, 4068, 4069, 4094, 4097, 4098,
    4123, 4126, 4127, 4152, 4155, 4156, 4181, 4184, 4185, 4210, 4213, 4214, 4239, 4242, 4243, 4268,
    4271, 4272, 4297, 4300, 4301, 4326, 4329, 4330, 4355, 4358, 4359, 4384, 4387, 4388, 4413, 4416,
    4417, 4442, 4445, 4446, 4471, 4474, 4475, 4500, 4503, 4504, 4636, 4639, 4655]

/-- Buffer `i`'s pointer from the base `b`. -/
def vtPtr (b n i : ℕ) : E := ofK (Parameters.gpow ((bases b (vtSizes n)).getD i 0))

/-- Selector `i`'s first buffer's index. -/
def selBuf (i : ℕ) : ℕ := if i = 0 then 5 else if i = 1 then 8 else if i = 2 then 12 else 16 + 3 * (i - 3)

/-- The callees: the six padding weights at the tables' log-heights `τs` and row counts `nr`,
then the 69 loops, the selectors' at the blocks' log-heights `ks`, on the bus point of length
`μ`. -/
noncomputable def vtKids (Lin : Main.Layout) (b n μ logMem : ℕ) (ks τs nr : ℕ → ℕ) (point : List E)
    (zeta sq chiP : E) (own : List (List E)) : List Kid :=
  let L := Lin ++ bufL b (vtSizes n) own
  let sel := fun i => (⟨selNames.getD i "", decide (μ - ks (selBlk.getD i 0) ≠ 0),
    [1, gen ^ (μ - ks (selBlk.getD i 0)), vtPtr b n (selBuf i) * gen ^ ks (selBlk.getD i 0),
      vtPtr b n (selBuf i + 1), zeta * gen ^ ks (selBlk.getD i 0), vtPtr b n (selBuf i + 2), sq,
      gen ^ ks (selBlk.getD i 0)], L, Returns []⟩ : Kid)
  (List.range 6).map (fun t => (⟨pwNames.getD (τs t) "", true, [eOfNat (nr t), zeta], Lin,
      Returns [paddingWeight (point.take (τs t)) (nr t), pwLead (τs t) (nr t), pwRest (τs t) (nr t)]⟩ : Kid)) ++
    [sel 0, sel 1, ⟨"__loop14", decide (logMem ≠ 0), [1, gen ^ logMem, vtPtr b n 11, zeta, vtPtr b n 3], L,
      Returns []⟩, sel 2, ⟨"__loop16", true, [1, gen ^ 18, vtPtr b n 15, zeta, vtPtr b n 3], L, Returns []⟩] ++
    (List.range 62).map (fun i => sel (i + 3)) ++
    [⟨"__loop79", decide (n ≠ 0), [1, gen ^ n, vtPtr b n 202, chiP, gen ^ n, vtPtr b n 203], L, Returns []⟩,
      ⟨"__loop80", decide (n ≠ 0), [1, gen ^ n, vtPtr b n 204, zeta, chiP], L, Returns []⟩]

set_option maxRecDepth 100000 in
theorem vtAllocVar_ok : vtAllocVar = (vtPre.filterMap Main.Stmt.allocSz).map fun x => x.1.idx := by
  decide +kernel

/-- **The placed form's conditions on a valuation of the body** (g5b): on a valuation under which
all of `vtPre` holds (`VtHolds`), with the arguments, the 205 hinted pointers from the base `b` and
`g^n`, on a memory defined below `2^κ` holding the caller's words `Lin` (`CompleteTablesAt`'s reads)
and the honest buffers, the hints' sizes are `vtSizes n`, their pointers the allocator's, the
dispatches' selectors powers of `g`, the frames `vtKids`', and every load reads the caller's words
or the buffers. The run's facts: `rowsN` the row counts (log-heights `τs`), `ks` the blocks'
log-heights `vtKs logMem τs`, `n` the largest `τs`, the stream `xs` of `5 + 3n + 104` words. -/
def VtPlacedOk : Prop :=
  ∀ (κ : ℕ), 7 ≤ κ → ∀ (rd : Reader) (σ : Val) (Lin : Main.Layout) (b : ℕ)
    (logMem n : ℕ) (rowsN : List ℕ) (point xs chis : List E) (claims cpw : List E)
    (cvr : ℕ → Digest) (cl ch : ℕ → E) (alphas : List E)
    (c z lp sq dims rows bk fpw pool cplen chi : ℕ) (outs : List (List E × Main.Layout)),
    VtHolds rd σ → LowDef κ rd → MemL rd Lin →
    point.length < 33 → 16 ≤ logMem → logMem ≤ 32 → rowsN.length = 6 → (∀ m ∈ rowsN, log2Ceil m < 29) →
    alphas.length = 4 → n = ((List.range 6).map fun t => log2Ceil (rowsN.getD t 0)).foldl max 0 →
    n ≤ point.length → xs.length = 5 + 3 * n + 104 → claims.length = nClaims → chis.length = n →
    cpw.length = nPooled →
    σ (.n 2) = ofK (Parameters.gpow c) → σ (.n 5) = ofK (Parameters.gpow z) →
    σ (.n 6) = gen ^ point.length → σ (.n 7) = ofK (Parameters.gpow dims) →
    σ (.n 8) = ofK (Parameters.gpow rows) → σ (.n 9) = ofK (Parameters.gpow bk) →
    σ (.n 10) = ofK (Parameters.gpow sq) → σ (.n 11) = ofK (Parameters.gpow fpw) →
    σ (.n 13) = ofK (Parameters.gpow pool) → σ (.n 14) = ofK (Parameters.gpow cplen) →
    σ (.n 15) = ofK (Parameters.gpow chi) →
    (∀ i < 205, σ (.n (vtAllocVar.getD i 0)) = vtPtr b n i) → σ (.n 4554) = gen ^ n →
    (∀ rd, LowDef κ rd → MemL rd Lin →
      ReadsAt rd (ofK (Parameters.gpow c)) xs ∧ ReadsAt rd (ofK (Parameters.gpow z)) point ∧
      ExpTables rd (ofK (Parameters.gpow lp)) (ofK (Parameters.gpow sq)) ∧
      ReadsAt rd (ofK (Parameters.gpow rows)) (rowsN.map eOfNat) ∧
      ReadsAt rd (ofK (Parameters.gpow dims)) (gen ^ logMem :: rowsN.map fun m ↦ gen ^ log2Ceil m) ∧
      ReadsAt rd (ofK (Parameters.gpow bk))
        (blockKappas (gen ^ logMem) (rowsN.map fun m ↦ gen ^ log2Ceil m)) ∧
      ReadsAt rd (ofK (Parameters.gpow fpw)) (eqKernel alphas) ∧
      ReadsAt rd (ofK (Parameters.gpow pool)) claims ∧
      ReadsAt rd (ofK (Parameters.gpow chi)) chis ∧
      ReadsAt rd (ofK (Parameters.gpow cplen)) cpw) →
    MemL rd (bufL b (vtSizes n) (vtOwnW (vtKs logMem fun t => log2Ceil (rowsN.getD t 0)) point logMem n
      cvr (ofK (Parameters.gpow c)) cl ch chis)) →
    OutsOk (vtKids Lin b n point.length logMem (vtKs logMem fun t => log2Ceil (rowsN.getD t 0))
      (fun t => log2Ceil (rowsN.getD t 0)) (fun t => rowsN.getD t 0) point (ofK (Parameters.gpow z))
      (ofK (Parameters.gpow sq)) (ofK (Parameters.gpow chi))
      (vtOwnW (vtKs logMem fun t => log2Ceil (rowsN.getD t 0)) point logMem n cvr
        (ofK (Parameters.gpow c)) cl ch chis)) outs →
    (∀ s ∈ vtPre, DispOk σ s) ∧
      (vtPre.filterMap Main.Stmt.allocSz).map (fun x => x.2.elim id fun s => logG (σ s)) = vtSizes n ∧
      ((vtPre.filterMap Main.Stmt.allocSz).map Prod.fst).map σ =
        (bases b (vtSizes n)).map (fun b => ofK (Parameters.gpow b)) ∧
      CallsMatch σ ((vtPre.filterMap (Stmt.callSF σ)).map (Main.mkCall σ))
        (vtKids Lin b n point.length logMem (vtKs logMem fun t => log2Ceil (rowsN.getD t 0))
          (fun t => log2Ceil (rowsN.getD t 0)) (fun t => rowsN.getD t 0) point (ofK (Parameters.gpow z))
          (ofK (Parameters.gpow sq)) (ofK (Parameters.gpow chi))
          (vtOwnW (vtKs logMem fun t => log2Ceil (rowsN.getD t 0)) point logMem n cvr
            (ofK (Parameters.gpow c)) cl ch chis)) outs ∧
      ∀ q ∈ vtPre.filterMap Stmt.loadS, ∃ i, (σ q.1).limb 0 * Parameters.gpow q.2 = Parameters.gpow i ∧
        (RegionL Lin i ∨ RegionL (bufL b (vtSizes n) (vtOwnW (vtKs logMem fun t => log2Ceil (rowsN.getD t 0))
          point logMem n cvr (ofK (Parameters.gpow c)) cl ch chis)) i)

end
end LeanVM.Guest.B1.VerifySub
