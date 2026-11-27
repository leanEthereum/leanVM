/-
  LeanVM.Guest.B1.VerifySub.SoundFront

  `verify_sub` up to `verify_keccak`'s call, assembled: the seed, the announced sizes, the root,
  the placement, the out-of-domain sample, the bus's challenges, its GKR and `verify_tables`.
-/

module

public import LeanVM.Guest.B1.VerifySub.SoundLib
public import LeanVM.Guest.B1.VerifySub.Ood
public import LeanVM.Guest.B1.VerifySub.Bus
public import LeanVM.Guest.B1.VerifySub.Tail
public import LeanVM.Guest.B1.Placement.Certify
public import LeanVM.Guest.B1.Gkr.Holds
public import LeanVM.Guest.B1.Tables.Vt.VerifyTables
import LeanVM.Guest.ValRef
import LeanVM.Guest.Data.ValNames.«verify_sub»

/-!
# The front of `verify_sub`, assembled

`vs_front`: a run of `verify_sub`'s body under its precondition, on a memory image of at most
`2^32` words, holds `VsFront` and the statements from `ring_switch`'s grind on (`vsMapsT`). Every
section is read off by its own lemma (`Front`, `Mid`, `Known`, `Ood`, `Bus`, `Tail`); the
sections are tied here: the announced words are the memory's log, the rows `verify_tables`
certifies and the rate; the placement's heights are those rows'; the bus depth is the push side's,
`μ ≥ 16` from the bus grind's range check, so `verify_bus_gkr` runs at a depth other than `0`.
-/

namespace LeanVM.Guest.B1.VerifySub

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

/-- The rest of the body after `verify_keccak`'s call. -/
abbrev vsBackT : List Stmt := vsMapsT ++ (vsCtabT ++ (vsLamT ++ vsTailT))

/-- **What `verify_sub`'s front establishes.** -/
structure VsFront (bytecode : List K) (C : CallRel) (rd : Reader) (σ : Val) : Type where
  seed : Digest
  pi : Digest
  hseed : (σ (.n (val% «verify_sub» "seed_0")), σ (.n (val% «verify_sub» "seed_1"))) = digestHalves seed
  hpi : (σ (.n (val% «verify_sub» "pi_0")), σ (.n (val% «verify_sub» "pi_1"))) = digestHalves pi
  hcap0 : [σ (.n (val% «verify_sub» "sp[8]")), σ (.n (val% «verify_sub» "sp[9]")), σ (.n (val% «verify_sub» "sp[10]")), σ (.n (val% «verify_sub» "sp[11]")), σ (.n (val% «verify_sub» "sp[12]"))] =
    capOf (keccakF1600 (seedInput seed pi))
  h8 : σ (.n (val% «verify_sub» "s3#0[1]")) = 0
  h9 : σ (.n (val% «verify_sub» "s3#0[2]")) = 0
  h10 : σ (.n (val% «verify_sub» "s3#0[3]")) = 0
  h11 : σ (.n (val% «verify_sub» "s3#0[4]")) = 0
  -- the announced sizes
  logMem : ℕ
  lir : ℕ
  rowsN : List ℕ
  hrowsL : rowsN.length = 6
  hh31 : ∀ h ∈ Tables.tableHeightsOf rowsN, h < 31
  hm1 : 1 ≤ logMem
  hm30 : logMem ≤ 30
  hl1 : 1 ≤ lir
  hl4 : lir ≤ 4
  h66 : σ (.n (val% «verify_sub» "rate_sel")) = gen ^ (lir - 1)
  h72 : σ (.n (val% «verify_sub» "g_log_mem")) = gen ^ logMem
  hw : ∀ i < 8, WordAt rd σ i (vsX i)
  hwords : vsWords σ = eOfNat logMem :: rowsN.map eOfNat ++ [eOfNat lir]
  habs1 : (⟨[σ (.n (val% «verify_sub» "sp[8]")), σ (.n (val% «verify_sub» "sp[9]")), σ (.n (val% «verify_sub» "sp[10]")), σ (.n (val% «verify_sub» "sp[11]")), σ (.n (val% «verify_sub» "sp[12]"))], []⟩ : Fs).absorbAll
      (vsWords σ) dsObserve =
    ⟨[σ (.n (val% «verify_sub» "nxt[8]@1")), σ (.n (val% «verify_sub» "nxt[9]@1")), σ (.n (val% «verify_sub» "nxt[10]@1")), σ (.n (val% «verify_sub» "nxt[11]@1")), σ (.n (val% «verify_sub» "nxt[12]@1"))],
      [(σ (.n (val% «verify_sub» "x@5")), dsObserve), (σ (.n (val% «verify_sub» "x@6")), dsObserve), (σ (.n (val% «verify_sub» "x@7")), dsObserve),
        (σ (.n (val% «verify_sub» "x@8")), dsObserve)]⟩
  habs2 : (((⟨[σ (.n (val% «verify_sub» "nxt[8]@1")), σ (.n (val% «verify_sub» "nxt[9]@1")), σ (.n (val% «verify_sub» "nxt[10]@1")), σ (.n (val% «verify_sub» "nxt[11]@1")), σ (.n (val% «verify_sub» "nxt[12]@1"))],
      [(σ (.n (val% «verify_sub» "x@5")), dsObserve), (σ (.n (val% «verify_sub» "x@6")), dsObserve), (σ (.n (val% «verify_sub» "x@7")), dsObserve),
        (σ (.n (val% «verify_sub» "x@8")), dsObserve)]⟩ : Fs).absorb (σ (.n (val% «verify_sub» "x@9"))) dsObserve).absorb (σ (.n (val% «verify_sub» "x@10")))
        dsObserve) =
    ⟨[σ (.n (val% «verify_sub» "nxt[8]@2")), σ (.n (val% «verify_sub» "nxt[9]@2")), σ (.n (val% «verify_sub» "nxt[10]@2")), σ (.n (val% «verify_sub» "nxt[11]@2")), σ (.n (val% «verify_sub» "nxt[12]@2"))],
      [(σ (.n (val% «verify_sub» "x@9")), dsObserve), (σ (.n (val% «verify_sub» "x@10")), dsObserve)]⟩
  w268 : WordAt rd σ 8 268
  w271 : WordAt rd σ 9 271
  hkb : ReadsAt rd (σ (.n (val% «verify_sub» "kappa_base"))) (1 :: gen ^ logMem :: (Tables.tableHeightsOf rowsN).map (gen ^ ·))
  hdims : ReadsAt rd (σ (.n (val% «verify_sub» "dims_g"))) (gen ^ logMem :: (Tables.tableHeightsOf rowsN).map (gen ^ ·))
  -- the placement and the stack's log
  hP : Tables.PCtx rd (columnKappas logMem 19 (Tables.tableHeightsOf rowsN)) (σ (.n (val% «verify_sub» "col_offsets")))
  hKB : Tables.KappasBelow (columnKappas logMem 19 (Tables.tableHeightsOf rowsN))
  hst20 : 20 ≤ (Tables.layoutOf bytecode logMem rowsN).stackLog
  hst30 : (Tables.layoutOf bytecode logMem rowsN).stackLog ≤ 30
  h276 : σ (.n (val% «verify_sub» "gmv")) = gen ^ (Tables.layoutOf bytecode logMem rowsN).stackLog
  h278 : σ (.n (val% «verify_sub» "size_sel")) = gen ^ ((Tables.layoutOf bytecode logMem rowsN).stackLog - 20)
  -- the out-of-domain sample
  z : List E
  v : E
  nn : E
  hO : RunsTo (readOod (Tables.layoutOf bytecode logMem rowsN).stackLog)
    ⟨[σ (.n (val% «verify_sub» "nxt[8]@2")), σ (.n (val% «verify_sub» "nxt[9]@2")), σ (.n (val% «verify_sub» "nxt[10]@2")), σ (.n (val% «verify_sub» "nxt[11]@2")), σ (.n (val% «verify_sub» "nxt[12]@2"))],
      [(σ (.n (val% «verify_sub» "x@9")), dsObserve), (σ (.n (val% «verify_sub» "x@10")), dsObserve)]⟩
    [σ (.n (val% «verify_sub» "s38.i0:fs_grind_squeeze.s0.e.s0.e.s0#0")), v] (fun x ↦ eqEval z x, v)
    ⟨[σ (.n (val% «verify_sub» "fs0@1")), σ (.n (val% «verify_sub» "fs1@1")), σ (.n (val% «verify_sub» "fs2@1")), σ (.n (val% «verify_sub» "fs3@1")), σ (.n (val% «verify_sub» "fs4@1"))], [(v, dsObserve)]⟩
  hzL : z.length = (Tables.layoutOf bytecode logMem rowsN).stackLog
  hz : ReadsAt rd (σ (.n (val% «verify_sub» "ood_z"))) z
  hv : ReadsAt rd (σ (.n (val% «verify_sub» "ood_value"))) [v]
  hn283 : LoadHolds rd (σ (.n (val% «verify_sub» "stream"))) 10 (σ (.n (val% «verify_sub» "s38.i0:fs_grind_squeeze.s0.e.s0.e.s0#0")))
  h312 : σ (.n (val% «verify_sub» "word0~9")) = σ (.n (val% «verify_sub» "stream")) * gen ^ 11
  hv312 : LoadHolds rd (σ (.n (val% «verify_sub» "word0~9"))) 0 v
  hnn : LoadHolds rd (σ (.n (val% «verify_sub» "word0~9"))) 1 nn
  h320 : σ (.n (val% «verify_sub» "cursor@1")) = σ (.n (val% «verify_sub» "word0~9")) * gen ^ 2
  -- the bus's challenges
  weights : List E
  hwL : weights.length = 16
  hB : RunsTo (busChallenges (busDepth (Tables.layoutOf bytecode logMem rowsN)))
    ⟨[σ (.n (val% «verify_sub» "fs0@1")), σ (.n (val% «verify_sub» "fs1@1")), σ (.n (val% «verify_sub» "fs2@1")), σ (.n (val% «verify_sub» "fs3@1")), σ (.n (val% «verify_sub» "fs4@1"))], [(v, dsObserve)]⟩ [nn]
    (weights, σ (.n (val% «verify_sub» "nxt[0]@19"))) ⟨[σ (.n (val% «verify_sub» "nxt[8]@19")), σ (.n (val% «verify_sub» "nxt[9]@19")), σ (.n (val% «verify_sub» "nxt[10]@19")), σ (.n (val% «verify_sub» "nxt[11]@19")), σ (.n (val% «verify_sub» "nxt[12]@19"))], []⟩
  hdep20 : 20 ≤ busDepth (Tables.layoutOf bytecode logMem rowsN)
  hdep34 : busDepth (Tables.layoutOf bytecode logMem rowsN) < 34
  hdep19 : 19 ≤ busDepth (Tables.layoutOf bytecode logMem rowsN)
  h253 : σ (.n (val% «verify_sub» "g_bus_mu")) = gen ^ busDepth (Tables.layoutOf bytecode logMem rowsN)
  -- the bus's GKR
  xsG : List E
  r : E × List E × List E
  hxsG : ReadsAt rd (σ (.n (val% «verify_sub» "cursor@1"))) xsG
  hG : RunsTo (Tables.gkrPhase (busDepth (Tables.layoutOf bytecode logMem rowsN)))
    ⟨[σ (.n (val% «verify_sub» "nxt[8]@19")), σ (.n (val% «verify_sub» "nxt[9]@19")), σ (.n (val% «verify_sub» "nxt[10]@19")), σ (.n (val% «verify_sub» "nxt[11]@19")), σ (.n (val% «verify_sub» "nxt[12]@19"))], []⟩ xsG r
    ⟨[σ (.n (val% «verify_sub» "fs0@3")), σ (.n (val% «verify_sub» "fs1@3")), σ (.n (val% «verify_sub» "fs2@3")), σ (.n (val% «verify_sub» "fs3@3")), σ (.n (val% «verify_sub» "fs4@3"))], []⟩
  hrL : r.2.1.length = busDepth (Tables.layoutOf bytecode logMem rowsN)
  hzeta : ReadsAt rd (σ (.n (val% «verify_sub» "zeta"))) r.2.1
  h567 : σ (.n (val% «verify_sub» "cursor@2")) = σ (.n (val% «verify_sub» "cursor@1")) * gen ^ xsG.length
  -- the tables
  xsT : List E
  bus : BusResult
  claims : List ColumnClaim
  slots : List E
  hslL : slots.length = busBits
  hsl : ReadsAt rd (σ (.n (val% «verify_sub» "bc_point"))) slots
  hbp : bus.bytecodePoint = r.2.1.take 19 ++ slots
  hxsT : ReadsAt rd (σ (.n (val% «verify_sub» "cursor@2"))) xsT
  hT : RunsTo (Tables.tablesSeg (claimedBytecodeValue ⟨bus.bytecodePoint, σ (.n (val% «verify_sub» "bc_value"))⟩)
      (Tables.layoutOf bytecode logMem rowsN) pi weights (σ (.n (val% «verify_sub» "nxt[0]@19"))) r.2.1 r.2.2)
    ⟨[σ (.n (val% «verify_sub» "fs0@3")), σ (.n (val% «verify_sub» "fs1@3")), σ (.n (val% «verify_sub» "fs2@3")), σ (.n (val% «verify_sub» "fs3@3")), σ (.n (val% «verify_sub» "fs4@3"))], []⟩ xsT (bus, claims)
    ⟨[σ (.n (val% «verify_sub» "fs0@4")), σ (.n (val% «verify_sub» "fs1@4")), σ (.n (val% «verify_sub» "fs2@4")), σ (.n (val% «verify_sub» "fs3@4")), σ (.n (val% «verify_sub» "fs4@4"))], []⟩
  hcl : claims.length = 159
  hpool : ReadsAt rd (σ (.n (val% «verify_sub» "claim_pool"))) ((claims.take 4).map (·.value))
  hcew : ReadsAt rd (σ (.n (val% «verify_sub» "col_eval_words"))) (((claims.drop 4).take 153).map (·.value))
  hpiv : ReadsAt rd (σ (.n (val% «verify_sub» "claim_pool")) * gen ^ 157) ((claims.drop 157).map (·.value))
  hctx : Tables.TCtx rd (Tables.layoutOf bytecode logMem rowsN) bus claims
    [σ (.n (val% «verify_sub» "zeta")), σ (.n (val% «verify_sub» "chi")), σ (.n (val% «verify_sub» "rm")), σ (.n (val% «verify_sub» "g_bus_mu")), σ (.n (val% «verify_sub» "g_zc_n"))]
  h578 : σ (.n (val% «verify_sub» "cursor@3")) = σ (.n (val% «verify_sub» "cursor@2")) * gen ^ xsT.length
  -- `verify_keccak`'s call
  h583 : σ (.n (val% «verify_sub» "tau_keccak_g")) = gen ^ (Tables.tableHeightsOf rowsN).getD 5 0
  h587 : σ (.n (val% «verify_sub» "fs0@5~8")) = σ (.n (val% «verify_sub» "col_eval_words")) * gen ^ 101
  h589 : σ (.n (val% «verify_sub» "fs0@5~10")) = σ (.n (val% «verify_sub» "g_squares")) * gen ^ winTabAt
  hkc : C "verify_keccak" [σ (.n (val% «verify_sub» "fs0@4")), σ (.n (val% «verify_sub» "fs1@4")), σ (.n (val% «verify_sub» "fs2@4")), σ (.n (val% «verify_sub» "fs3@4")), σ (.n (val% «verify_sub» "fs4@4")), σ (.n (val% «verify_sub» "cursor@3")),
    σ (.n (val% «verify_sub» "tau_keccak_g")), σ (.n (val% «verify_sub» "chi")), σ (.n (val% «verify_sub» "fs0@5~8")), σ (.n (val% «verify_sub» "z_vals")), σ (.n (val% «verify_sub» "slices")), σ (.n (val% «verify_sub» "fs0@5~10")), σ (.n (val% «verify_sub» "stream"))]
    [σ (.n (val% «verify_sub» "fs0@5")), σ (.n (val% «verify_sub» "fs1@5")), σ (.n (val% «verify_sub» "fs2@5")), σ (.n (val% «verify_sub» "fs3@5")), σ (.n (val% «verify_sub» "fs4@5")), σ (.n (val% «verify_sub» "cursor@4")), σ (.n (val% «verify_sub» "keccak_word"))]
  -- what `verify_tables` is called under
  hTP : Tables.TablesPre pi logMem weights r.2.1 r.2.2 rd
    [σ (.n (val% «verify_sub» "fs0@3")), σ (.n (val% «verify_sub» "fs1@3")), σ (.n (val% «verify_sub» "fs2@3")), σ (.n (val% «verify_sub» "fs3@3")), σ (.n (val% «verify_sub» "fs4@3")), σ (.n (val% «verify_sub» "cursor@2")), σ (.n (val% «verify_sub» "pi_0")), σ (.n (val% «verify_sub» "pi_1")),
      σ (.n (val% «verify_sub» "zeta")), σ (.n (val% «verify_sub» "g_bus_mu")), σ (.n (val% «verify_sub» "dims_g")), σ (.n (val% «verify_sub» "table_rows")), σ (.n (val% «verify_sub» "g_squares")), σ (.n (val% «verify_sub» "fp_w")), σ (.n (val% «verify_sub» "nxt[0]@19")), σ (.n (val% «verify_sub» "claim_pool")),
      σ (.n (val% «verify_sub» "chi")), σ (.n (val% «verify_sub» "gkr_leaves")), σ (.n (val% «verify_sub» "fs0@4~11")), σ (.n (val% «verify_sub» "bc_point")), σ (.n (val% «verify_sub» "stream"))]

/-! ## Facts the assembly ties the sections with -/

/-- The size selector: `g^m·g^-20` below `g^11` gives `20 ≤ m`, `size_sel = g^(m - 20)`. -/
theorem vsPlaceT_size {κ : ℕ} (hκ : κ ≤ 32) (_hκ6 : 6 ≤ κ) (L : MemoryImage κ) {C : CallRel}
    {σ : Val} {next : Prop} {kret : List E → Prop} {m : ℕ} (hm : m ≤ 30)
    (h276 : σ (.n (val% «verify_sub» "gmv")) = gen ^ m) (h : Stmt.HoldsList C L.read σ vsPlaceT next kret) :
    20 ≤ m ∧ σ (.n (val% «verify_sub» "size_sel")) = gen ^ (m - 20) := by
  simp only [vsPlaceT, Stmt.HoldsList, Stmt.Holds, vsCall, vsConst, vsMul, vsRange,
    List.map_cons, List.map_nil, Atom.Holds] at h
  obtain ⟨-, -, e277, m278, e279, r278, -⟩ := h
  obtain ⟨e, he, h278⟩ := rc_pow hκ L (a := 10) (by norm_num)
    (by rw [e279, show (1024 : ℕ) = 2 ^ 10 from rfl, word_two_pow (by norm_num)]) r278
  have hme : m = e + 20 := by
    have := congrArg (· * gen ^ 20) (m278.symm.trans h278)
    simp only [h276, e277, mul_assoc, vsGinv20_mul, mul_one, ← pow_add] at this
    exact gen_pow_inj (by omega) (by omega) this
  exact ⟨by omega, by rw [h278, hme, Nat.add_sub_cancel]⟩

/-- Two lists of `g`-powers below `2^40` agree exponent by exponent. -/
theorem map_gpow_inj : ∀ {as bs : List ℕ}, (∀ x ∈ as, x < 2 ^ 40) → (∀ x ∈ bs, x < 2 ^ 40) →
    as.map (gen ^ ·) = bs.map (gen ^ ·) → as = bs
  | [], [], _, _, _ => rfl
  | a :: as, b :: bs, ha, hb, h => by
    simp only [List.map_cons, List.cons.injEq] at h
    rw [gen_pow_inj (by have := ha a (by simp); omega) (by have := hb b (by simp); omega) h.1,
      map_gpow_inj (fun x hx ↦ ha x (by simp [hx])) (fun x hx ↦ hb x (by simp [hx])) h.2]
  | [], _ :: _, _, _, h => by simp at h
  | _ :: _, [], _, _, h => by simp at h

/-! ## The front -/

set_option maxHeartbeats 1000000 in
/-- **`verify_sub`'s front.** -/
theorem vs_front {κ : ℕ} (hκ : κ ≤ 32) (L : MemoryImage κ) {C : CallRel}
    (hC : CallRel.Le C (coreProgram.Rel L.read)) {bytecode : List K} (hbl : bytecode.length = 2 ^ 23)
    {σ : Val} {rets : List E} (hexp : ExpTables L.read (σ (.n (val% «verify_sub» "g_squares"))))
    (hwin : ExpWinTab L.read (σ (.n (val% «verify_sub» "g_squares"))))
    (hb : Stmt.HoldsList C L.read σ vsT False (fun rs ↦ rs = rets)) :
    Nonempty (VsFront bytecode C L.read σ) ∧
      Stmt.HoldsList C L.read σ vsBackT False (fun rs ↦ rs = rets) := by
  have hκw := winTab_kappa hκ L hwin
  have hκ6 : 6 ≤ κ := by simp only [winTabBits] at hκw; omega
  rw [vsT_split] at hb
  simp only [holdsList_append] at hb
  -- the head, the words, the sizes
  obtain ⟨h8, h9, h10, h11, hk, hb⟩ := vsHeadT_holds hb
  obtain ⟨seed, pi, hseed, hpi, hcap0⟩ := vs_seed hk h8 h9 h10 h11
  obtain ⟨hw, hrw, hk39, hb⟩ := vsReadsT_holds hb
  obtain ⟨lir, logMem, hl1, hl4, h61, h66, hm1, hm30, h27, h72, ds, hdsL, hdims, hkb, hkbv, hb⟩ :=
    vsSizesT_holds hκ L hC hb
  -- the push side, the root
  obtain ⟨hpush, hb⟩ := (holdsList_noRet _ vsPushT_noRet _ _).1 hb
  obtain ⟨μ, hμ34, h253, -⟩ := vsPushT_depth hκ hκ6 L hC hexp hpush
  obtain ⟨hk255, w268, w271, hb⟩ := vsRootsT_holds hb
  -- the placement
  obtain ⟨hplace, hb⟩ := (holdsList_noRet _ vsPlaceT_noRet _ _).1 hb
  obtain ⟨⟨hs, -, hds, -, hhs29, -, off, -, h275, hPC, h276, hM30⟩, -⟩ :=
    vsPlaceT_known hκ hκ6 L hC (Tables.certify_placement_holds hκ L) hexp (hm30.trans (by norm_num)) hdsL hkb hplace
  obtain ⟨hM22, h278⟩ := vsPlaceT_size hκ hκ6 L hM30 h276 hplace
  -- the out-of-domain sample
  obtain ⟨z, v, nn, hO, hzL, hz, hv, hn283, h312, hv312, hnn, hom, hb⟩ :=
    vsOodT_holds hκ hκw L hC hwin hM22 hM30 h278 w268 w271 hb
  have hS := (List.append_inj' (show [σ (.n (val% «verify_sub» "word0")), σ (.n (val% «verify_sub» "pow_word")), σ (.n (val% «verify_sub» "fs0@2")), σ (.n (val% «verify_sub» "fs1@2")), σ (.n (val% «verify_sub» "fs2@2")),
    σ (.n (val% «verify_sub» "fs3@2")), σ (.n (val% «verify_sub» "fs4@2"))] ++ [σ (.n (val% «verify_sub» "cursor@1"))] = _ from hom) rfl)
  -- the bus's challenges
  rw [← holdsList_append] at hb
  obtain ⟨hμ16, weights, hwL, hw335, hBus, hb⟩ :=
    vsBusFpw_holds hκ hκw L hC hwin h8 h9 h10 h11 hμ34 h253
      (s := ⟨[σ (.n (val% «verify_sub» "fs0@1")), σ (.n (val% «verify_sub» "fs1@1")), σ (.n (val% «verify_sub» "fs2@1")), σ (.n (val% «verify_sub» "fs3@1")), σ (.n (val% «verify_sub» "fs4@1"))], [(v, dsObserve)]⟩)
      hS.1 hb
  -- the calls
  obtain ⟨h561, hgkr, h572, htab, h583l, h587, h589, hkc, hb⟩ := vsCallsT_holds hb
  -- the bus's GKR
  obtain ⟨depth, xsG, r, capG, leaves, hgm, hd33, hxsG, hrunG, hrL, hvL, hzeta, hleaves, hretG⟩ :=
    Tables.verify_bus_gkr_holds hκ L _ _
      (by simp only [List.getD_cons_succ, List.getD_cons_zero, h253]
          exact vs_gen_pow_ne_one (by omega) (by omega))
      (hC _ _ _ hgkr)
  have hμd : μ = depth := gen_pow_inj (by omega) (by omega) (h253.symm.trans hgm)
  subst hμd
  obtain ⟨hcapG, hcurG⟩ := List.append_inj' (show [σ (.n (val% «verify_sub» "fs0@3")), σ (.n (val% «verify_sub» "fs1@3")), σ (.n (val% «verify_sub» "fs2@3")), σ (.n (val% «verify_sub» "fs3@3")),
    σ (.n (val% «verify_sub» "fs4@3"))] ++ [σ (.n (val% «verify_sub» "cursor@2")), σ (.n (val% «verify_sub» "gkr_leaves"))] = _ from hretG) rfl
  simp only [List.cons.injEq, and_true] at hcurG
  -- the tables
  have hTP : Tables.TablesPre pi logMem weights r.2.1 r.2.2 L.read
      [σ (.n (val% «verify_sub» "fs0@3")), σ (.n (val% «verify_sub» "fs1@3")), σ (.n (val% «verify_sub» "fs2@3")), σ (.n (val% «verify_sub» "fs3@3")), σ (.n (val% «verify_sub» "fs4@3")), σ (.n (val% «verify_sub» "cursor@2")), σ (.n (val% «verify_sub» "pi_0")), σ (.n (val% «verify_sub» "pi_1")),
        σ (.n (val% «verify_sub» "zeta")), σ (.n (val% «verify_sub» "g_bus_mu")), σ (.n (val% «verify_sub» "dims_g")), σ (.n (val% «verify_sub» "table_rows")), σ (.n (val% «verify_sub» "g_squares")), σ (.n (val% «verify_sub» "fp_w")), σ (.n (val% «verify_sub» "nxt[0]@19")), σ (.n (val% «verify_sub» "claim_pool")),
        σ (.n (val% «verify_sub» "chi")), σ (.n (val% «verify_sub» "gkr_leaves")), σ (.n (val% «verify_sub» "fs0@4~11")), σ (.n (val% «verify_sub» "bc_point")), σ (.n (val% «verify_sub» "stream"))] :=
    ⟨hpi, hzeta, by rw [h253, hrL], by omega, hm1, hm30.trans (by norm_num), ⟨ds, hdsL, hdims⟩,
      expTablesAt_of hexp hwin, h572, hwL, hw335, hvL, by rw [hcurG.2]; exact hleaves⟩
  obtain ⟨xsT, capT, rowsN, bus, claims, hrowsL, hrows, hdims', hh31, hxsT, ⟨slots, hslL, hsl, hbp⟩,
      hT, hcl, hpool, hcew, hpiv, hctx, hcapT, h578⟩ :=
    Tables.verify_tables_holds hκ L bytecode hbl pi logMem weights r.2.1 r.2.2 _ _ hTP
      (hC _ _ _ htab)
  rw [logBytecode_eq hbl] at hbp
  have hHL := tableHeights_length rowsN hrowsL
  -- the heights are the placement's
  have eds : ds = (Tables.tableHeightsOf rowsN).map (gen ^ ·) := by
    have := readsAt_ext (by simp [hdsL, hHL]) hdims hdims'
    simpa using this
  have ehs : hs = Tables.tableHeightsOf rowsN :=
    map_gpow_inj (fun x hx ↦ by have := hhs29 x hx; omega) (fun x hx ↦ by have := hh31 x hx; omega)
      (hds.symm.trans eds)
  subst ehs
  -- the bus depth is the push side's
  have hkbv' : ∀ s < 8, σ (.n ((val% «verify_sub» "kb[0]") + s)) = gen ^ (([0, logMem] ++ Tables.tableHeightsOf rowsN).getD s 0) :=
    fun s hs ↦ by rw [hkbv s hs, eds, kbase_getD hHL hs]
  obtain ⟨hpd, hpd34, -⟩ := vsPushT_holds hκ hκ6 L hC hexp (fun x hx ↦ by have := hh31 x hx; omega)
    (hm30.trans (by norm_num)) hkbv' hpush
  have hdep : busDepth (Tables.layoutOf bytecode logMem rowsN) = μ := by
    have e := pushDepth_eq hbl logMem rowsN hrowsL
    exact (gen_pow_inj (by omega) (by omega) (hgm.symm.trans hpd)).trans e.symm |>.symm
  -- the stack's log
  have hstk := stackLog_eq hbl logMem rowsN
  have h30 : log2Ceil (Tables.stackTotal (columnKappas logMem 19 (Tables.tableHeightsOf rowsN))) ≤ 30 :=
    le_trans (le_max_right _ _) hM30
  -- the announced words
  have hwords : vsWords σ = eOfNat logMem :: rowsN.map eOfNat ++ [eOfNat lir] := by
    have hr : [σ (.n (val% «verify_sub» "x@2")), σ (.n (val% «verify_sub» "x@3")), σ (.n (val% «verify_sub» "x@4")), σ (.n (val% «verify_sub» "x@5")), σ (.n (val% «verify_sub» "x@6")), σ (.n (val% «verify_sub» "x@7"))] =
        rowsN.map eOfNat := by
      refine readsAt_ext (by simp [hrowsL]) (fun k hk ↦ ?_) hrows
      simp only [List.length_cons, List.length_nil] at hk
      have := hrw k hk
      interval_cases k <;> exact this
    rw [vsWords, ← hr, ← h27, ← h61]
    rfl
  -- `verify_keccak`'s table height
  have h583 : σ (.n (val% «verify_sub» "tau_keccak_g")) = gen ^ (Tables.tableHeightsOf rowsN).getD 5 0 := by
    refine loadHolds_unique h583l ?_
    have h6 := hdims' 6 (by simp [hHL])
    rw [List.getD_eq_getElem _ _ (show 5 < (Tables.tableHeightsOf rowsN).length by omega)]
    simpa using h6
  refine ⟨⟨{
      seed := seed,
      pi := pi,
      hseed := hseed,
      hpi := hpi,
      hcap0 := hcap0,
      h8 := h8,
      h9 := h9,
      h10 := h10,
      h11 := h11,
      logMem := logMem,
      lir := lir,
      rowsN := rowsN,
      hrowsL := hrowsL,
      hh31 := hh31,
      hm1 := hm1,
      hm30 := hm30,
      hl1 := hl1,
      hl4 := hl4,
      h66 := h66,
      h72 := h72,
      hw := hw,
      hwords := hwords,
      habs1 := vs_absorb8 hw hk39,
      habs2 := vs_absorbRoot hw hk255,
      w268 := w268,
      w271 := w271,
      hkb := by rw [← eds]; exact hkb,
      hdims := by rw [← eds]; exact hdims,
      hP := by rw [h275]; exact hPC,
      hKB := Tables.hypKappa_holds _ (Tables.columnKappas_length _ _ _) h30,
      hst20 := by rw [hstk]; exact hM22,
      hst30 := by rw [hstk]; exact hM30,
      h276 := by rw [hstk]; exact h276,
      h278 := by rw [hstk]; exact h278,
      z := z,
      v := v,
      nn := nn,
      hO := by rw [hstk]; exact hO,
      hzL := by rw [hstk]; exact hzL,
      hz := hz,
      hv := hv,
      hn283 := hn283,
      h312 := h312,
      hv312 := hv312,
      hnn := hnn,
      h320 := by simpa using hS.2,
      weights := weights,
      hwL := hwL,
      hB := by rw [hdep]; exact hBus,
      hdep20 := by rw [hdep]; exact hμ16,
      hdep34 := by rw [hdep]; exact hμ34,
      hdep19 := by
        have e := pushDepth_eq hbl logMem rowsN hrowsL
        have := depth_ge (logMem := logMem) hHL
        unfold pushTotal at this
        exact le_trans (by omega) (le_of_le_of_eq this e.symm),
      h253 := by rw [hdep]; exact h253,
      xsG := xsG,
      r := r,
      hxsG := hxsG,
      hG := by rw [hdep, hcapG]; exact hrunG,
      hrL := by rw [hdep]; exact hrL,
      hzeta := hzeta,
      h567 := hcurG.1,
      xsT := xsT,
      bus := bus,
      claims := claims,
      slots := slots,
      hslL := hslL,
      hsl := hsl,
      hbp := hbp,
      hxsT := hxsT,
      hT := by rw [hcapT]; exact hT _ (bytecodeAt_claimed _ _ _),
      hcl := hcl,
      hpool := hpool,
      hcew := hcew,
      hpiv := hpiv,
      hctx := hctx,
      h578 := h578,
      h583 := h583,
      h587 := h587,
      h589 := h589,
      hkc := hkc,
      hTP := hTP }⟩, ?_⟩
  simpa only [vsBackT, holdsList_append] using hb

end
end LeanVM.Guest.B1.VerifySub
