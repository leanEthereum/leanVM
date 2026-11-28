module

public import LeanVM.Guest.Complete.MainA
public import LeanVM.Guest.Complete.DigestA
public import LeanVM.Guest.Complete.ComposeRd
public import LeanVM.Guest.Complete.DaPadA
public import LeanVM.Guest.B1.VsC.TableSizeC
import LeanVM.Guest.CoreRef
import LeanVM.Guest.ValRef

/-!
# `main_loop4`, the children's loop, placed

`main_loop4` checks child `c` per iteration: its two list lengths (`child_meta`, touched by
`assert_gpow`), its two claim lists rebuilt from this node's tables (`child_claim_list_digest`,
twice), its carried claim and DA digest hinted into `main`'s `child_carried` and `da_digests`, its
statement's digest (`statement_digest`) written to `child_pi`, its proof (`verify_sub`), and the
next write count. It allocates nothing and takes no `frameAddr` (its `StackBuf` is frame cells), so
its words are its callees': each iteration's callees are placed fresh from the cursor, the next
iteration at the next frame (`KidsAtL`), the block `kidBlock`.

The callees: `child_claim_list_digest`'s two calls are hypotheses (`KidHyps.lx`, `KidHyps.sp`,
placed, at every position), `statement_digest` completes placed loading its argument's `26`
cells (`statement_digest_callAtA`, the region at the base, not `argRegion`), `verify_sub` by
`VsCompleteHypA.at`. The touched cells are read per memory (`callAtA_nodeLRd`).

`kidL_callAtA`: from iteration `j`, at every frame and cursor past its block and past the
exponent tables and the fresh claims (`top`), `main_loop4` completes placed, its pops the
children's (`kidPush`) stream by stream, every node exact.
-/

namespace LeanVM.Guest.Complete

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Memory LeanVM.Guest.B1
open LeanVM.Node LeanVM.Protocol LeanVM.Protocol.KeccakHash
open LeanVM.Protocol.Verifier (gen)
open LeanVM.Guest.Value
open LeanVM.Prover.Exec (allocBase)
open LeanVM.Guest.B1.VsC LeanVM.Guest.B1.Digest

@[expose] public section

set_option linter.constructorNameAsVariable false

/-! ## `statement_digest` loading at its argument's base -/

/-- The cells of the arrays `ps` (argument index, length), each from its base `bs`. -/
def argRegionAt (ps : List (ℕ × ℕ)) (bs : ℕ → ℕ) (i : ℕ) : Prop := ∃ q ∈ ps, bs q.1 ≤ i ∧ i < bs q.1 + q.2

/-- `loadsR_hintsR_of_loadOk` with each array's base given. -/
theorem loadsR_hintsR_of_loadOkAt {f : String} {fn : Fn} {ps : List (ℕ × ℕ)} {bs : ℕ → ℕ} {args rets : List E}
    {rd : Reader} {t : Tree} (R R' : ℕ → Prop) (hreg : ∀ i, argRegionAt ps bs i → R' i)
    (hfind : coreProgram.find? f = some fn)
    (hparams : fn.params = (List.range args.length).map V.n)
    (hL : (atomsOf fn.body).all (loadOkB ps) = true) (hr : (retOf fn.body).isSome = true)
    (hargs : ∀ q ∈ ps, q.1 < args.length) (hptr : ∀ q ∈ ps, args.getD q.1 0 = ptrAt (bs q.1))
    (hn : t.name = f) (hv : t.Valid coreProgram rd args rets) :
    t.LoadsR coreProgram R' ∧ t.HintsR coreProgram R := by
  obtain ⟨vs0, hr⟩ := Option.isSome_iff_exists.mp hr
  obtain ⟨ss, hbody, hss⟩ := retOf_spec hr
  cases t with
  | phantom _ _ => exact hv.elim
  | node g σ bufs kids =>
    obtain ⟨fn', hfn, hpar, es, vs, hw, _, _, hk⟩ := hv
    simp only [Tree.name] at hn
    subst hn
    rw [hfind] at hfn
    cases hfn
    have hb' : fn.body = (atomsOf ss).map Stmt.atom ++ [.ret vs0] := by rw [hbody, ← eq_map_atomsOf hss]
    have hw' : walk σ fn.body = .ret ((atomsOf ss).map Ev.atom) vs0 := by rw [hb']; exact walk_atoms _ _ _
    rw [hw'] at hw
    cases hw
    have hev : (Memory.Tree.node g σ bufs kids).events coreProgram = (atomsOf ss).map Ev.atom := by
      simp only [Tree.events, Tree.name, Tree.val, hfind, hw']
    rw [calls_atoms] at hk
    have hkids : kids = [] := by
      cases kids with
      | nil => rfl
      | cons _ _ => simp [Tree.KidsValid] at hk
    subst hkids
    have hok : ∀ a ∈ atomsOf ss, loadOkB ps a = true := fun a ha =>
      List.all_eq_true.mp hL a (mem_atomsOf' (by rw [hbody]; exact List.mem_append_left _ (mem_of_mem_atomsOf ha)))
    have hσ : ∀ j < args.length, σ (.n j) = args.getD j 0 := by
      intro j hj
      have hj' : (((List.range args.length).map V.n).map σ)[j]? = args[j]? := by rw [← hparams, hpar]
      simp [hj] at hj'
      simpa [List.getD_eq_getElem?_getD, hj] using hj'
    refine ⟨?_, ?_⟩
    · rw [Tree.LoadsR, hev]
      refine ⟨fun A hA => ?_, by rw [Tree.LoadsRKids]; trivial⟩
      simp only [loadAddrs, List.filterMap_map, List.mem_filterMap, Function.comp] at hA
      obtain ⟨a, ha, hA⟩ := hA
      have hk := hok a ha
      cases a with
      | load d p off =>
        simp only [Ev.loadAddr?, Option.some.injEq] at hA
        simp only [loadOkB, List.any_eq_true, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hk
        obtain ⟨q, hqm, rfl, hoff⟩ := hk
        refine ⟨bs q.1 + off, ?_, hreg _ ⟨q, hqm, by omega, by omega⟩⟩
        rw [← hA, hσ _ (hargs q hqm), hptr q hqm]
        exact Main.addr_ofK _ off
      | _ => simp [Ev.loadAddr?] at hA
    · rw [Tree.HintsR, hev]
      refine ⟨fun A hA => ?_, by rw [Tree.HintsRKids]; trivial⟩
      simp only [heapHintAddrs, List.flatMap_map, List.mem_flatMap] at hA
      obtain ⟨a, ha, hA⟩ := hA
      have hk := hok a ha
      cases a with
      | hint _ => simp [loadOkB] at hk
      | _ => simp [Ev.hintAddrs] at hA

/-- **`statement_digest` completes placed** at any frame and cursor, loading only the `26` cells at
its last argument's base `b`: block its frame, ending at its cursor, popping nothing, exact. -/
theorem statement_digest_callAtA {fs : String → ℕ} {al : String → Bool} {cert : String → V → ℕ}
    (hwf : coreProgram.Wf) (k : ℕ) {args rets : List E} (hlen : args.length = 9) {b : ℕ}
    (hb : args.getD 8 0 = ptrAt b) {Pre : Reader → Prop}
    (hm : ∀ rd, Pre rd → Digest.MeaningStatementDigest rd args rets) (fp c : ℕ) :
    CallAtA fs al cert k "statement_digest" args rets (fun i => b ≤ i ∧ i < b + 26) (fun _ => False)
      (fun _ => True) Pre FreePost (fs "statement_digest") fp c c := by
  obtain ⟨vs0, hr'⟩ := Option.isSome_iff_exists.mp
    (by decide +kernel : (retOf (fn% «statement_digest»).body).isSome = true)
  obtain ⟨ss, hbody, hss⟩ := retOf_spec hr'
  have hnc : ∀ fn σ es vs, coreProgram.find? "statement_digest" = some fn → walk σ fn.body = .ret es vs →
      calls es = [] := by
    intro fn σ es vs hfn hw
    rw [Digest.find_statement_digest] at hfn
    cases hfn
    have hb' : (fn% «statement_digest»).body = (atomsOf ss).map Stmt.atom ++ [.ret vs0] := by
      rw [hbody, ← eq_map_atomsOf hss]
    rw [hb', walk_atoms] at hw
    cases hw
    exact calls_atoms _
  have hreg : ∀ i, argRegionAt [(8, 26)] (fun _ => b) i → b ≤ i ∧ i < b + 26 := by
    rintro i ⟨q, hq, h⟩
    simp only [List.mem_singleton] at hq
    subst hq
    exact h
  refine (callAtA_of_callCompletes0 statement_digest_pureIn List.mem_cons_self le_rfl
    (callCompletes0_free hwf statement_digest_free.1 statement_digest_free.2 fun rd _ hp =>
      Digest.statement_digest_complete rd args rets (hm rd hp))
    fun rd t _ _ hn hv hbo _ => ?_)
  have hbe := block_endA_leaf (fs := fs) (al := al) statement_digest_pureIn List.mem_cons_self
    statement_digest_not_loop hnc hn hv hbo c
  obtain ⟨hlo, hhi⟩ := loadsR_hintsR_of_loadOkAt (bs := fun _ => b) (fun i => b ≤ i ∧ i < b + 26) _ hreg
    Digest.find_statement_digest (by rw [hlen]; rfl) (by decide +kernel) (by decide +kernel)
    (fun q hq => by simp only [List.mem_singleton] at hq; subst hq; simp [hlen])
    (fun q hq => by simp only [List.mem_singleton] at hq; subst hq; exact hb) hn hv
  exact ⟨hbe.1, hbe.2, hlo, hhi⟩

/-! ## `main_loop4`'s body -/

/-- `main_loop4`'s body before its `ret`. -/
def kidPre : List Stmt := [
    .atom (.mul (.n 16) (.n 2) (.n 0)),
    .atom (.load (.n 17) (.n 16) 0),
    .atom (.hint (.witness "child_meta" (.stack [.n 18, .n 19]))),
    .atom (.touch (.n 20) (.n 18)),
    .atom (.touch (.n 21) (.n 19)),
    .atom (.mul (.n 22) (.n 18) (.n 19)),
    .call "child_claim_list_digest" [.n 3, .n 4, .n 17, .n 5, .n 18] [.n 23, .n 24],
    .atom (.mul (.n 25) (.n 17) (.n 18)),
    .call "child_claim_list_digest" [.n 6, .n 7, .n 25, .n 8, .n 19] [.n 26, .n 27],
    .atom (.mul (.n 28) (.n 0) (.n 0)),
    .atom (.mul (.n 29) (.n 28) (.n 0)),
    .atom (.mul (.n 30) (.n 29) (.n 29)),
    .atom (.mul (.n 31) (.n 30) (.n 30)),
    .atom (.mul (.n 32) (.n 31) (.n 0)),
    .atom (.mul (.n 33) (.n 32) (.n 32)),
    .atom (.mul (.n 34) (.n 9) (.n 33)),
    .atom (.hint (.witness "child_defer" (.heap (.n 34) 0 26))),
    .atom (.mul (.n 35) (.n 0) (.n 0)),
    .atom (.mul (.n 36) (.n 10) (.n 35)),
    .atom (.hint (.witness "child_da" (.heap (.n 36) 0 2))),
    .atom (.load (.n 37) (.n 36) 0),
    .atom (.load (.n 38) (.n 36) 1),
    .call "statement_digest" [.n 11, .n 12, .n 23, .n 24, .n 26, .n 27, .n 37, .n 38, .n 34] [.n 39, .n 40],
    .atom (.mul (.n 41) (.n 0) (.n 0)),
    .atom (.mul (.n 42) (.n 13) (.n 41)),
    .atom (.load (.n 39) (.n 42) 0),
    .atom (.mul (.n 43) (.n 13) (.n 41)),
    .atom (.load (.n 40) (.n 43) 1),
    .atom (.mul (.n 44) (.n 0) (.n 0)),
    .atom (.mul (.n 45) (.n 44) (.n 0)),
    .atom (.mul (.n 46) (.n 45) (.n 45)),
    .atom (.mul (.n 47) (.n 46) (.n 46)),
    .atom (.mul (.n 48) (.n 47) (.n 0)),
    .atom (.mul (.n 49) (.n 48) (.n 48)),
    .atom (.mul (.n 50) (.n 49) (.n 0)),
    .atom (.mul (.n 51) (.n 50) (.n 50)),
    .atom (.mul (.n 52) (.n 51) (.n 0)),
    .atom (.mul (.n 53) (.n 15) (.n 52)),
    .call "verify_sub" [.n 39, .n 40, .n 11, .n 12, .n 14, .n 53] [],
    .atom (.mul (.n 54) (.n 17) (.n 22)),
    .atom (.mul (.n 55) (.n 2) (.n 0)),
    .atom (.load (.n 54) (.n 55) 1),
    .atom (.const (.n 56) (word 2 0)),
    .atom (.mul (.n 57) (.n 0) (.n 56)),
    .atom (.add (.n 58) (.n 57) (.n 1)),
    .atom (.const (.n 59) (word 2 0)),
    .atom (.mul (.n 60) (.n 0) (.n 59)),
    .callIf (.n 58) "__loop4_main" [.n 60, .n 1, .n 2, .n 3, .n 4, .n 5, .n 6, .n 7, .n 8, .n 9, .n 10, .n 11, .n 12, .n 13, .n 14, .n 15]
  ]

theorem kid_body : (fn% «main_loop4»).body = kidPre ++ [.ret []] := rfl

set_option maxRecDepth 100000 in
theorem find_kid : coreProgram.find? name% «main_loop4» = some fn% «main_loop4» :=
  coreProgram_find?_at (j := idx% «main_loop4») rfl

theorem kid_loop : coreProgram.loop name% «main_loop4» = true := by decide +kernel

theorem kidPre_straight : kidPre.all Stmt.straight = true := rfl

set_option maxRecDepth 100000 in
theorem kid_pin : Stmt.blockNextOk isComputed pinsInverse (fn% «main_loop4»).body = true := by
  rw [kid_body]; decide +kernel

/-! ## The children's data -/

/-- What `main` hands `main_loop4`, as word indices and exponents: the children's count `n`, the
write counts `W`, the leanXMSS table `TX`, coverage `CV` and its slots `g^sx`, the leanSPHINCS table
`TS`, coverage `SC` and slots `g^ss`, the carried claims `CC`, the DA digests `DD`, the children's
digests `PI`, the exponent tables `GS`, the fresh claims `CF`, and the seed. -/
structure KidPtrs where
  n : ℕ
  W : ℕ
  TX : ℕ
  CV : ℕ
  sx : ℕ
  TS : ℕ
  SC : ℕ
  ss : ℕ
  CC : ℕ
  DD : ℕ
  PI : ℕ
  GS : ℕ
  CF : ℕ
  seed : Digest

/-- Child `c`'s data: the child, its write count `g^base`, its lists' lengths, the digests the two
claim walks return, its DA digest's cells and carried claim's, the claim walks' pops. -/
structure KidData where
  child : ℕ → Child
  base : ℕ → ℕ
  nx : ℕ → ℕ
  ns : ℕ → ℕ
  dx : ℕ → E × E
  ds : ℕ → E × E
  da : ℕ → E × E
  defer : ℕ → List E
  px : ℕ → List Pop
  ps : ℕ → List Pop

/-- `main_loop4`'s arguments at the counter `g^j`. -/
def kidArgs (P : KidPtrs) (j : ℕ) : List E :=
  [gen ^ j, gen ^ P.n, ptrAt P.W, ptrAt P.TX, ptrAt P.CV, gen ^ P.sx, ptrAt P.TS, ptrAt P.SC, gen ^ P.ss,
    ptrAt P.CC, ptrAt P.DD, (digestHalves P.seed).1, (digestHalves P.seed).2, ptrAt P.PI, ptrAt P.GS, ptrAt P.CF]

/-- Iteration `c`'s valuation, the touched cells `a`, `b`. -/
noncomputable def kidσ (P : KidPtrs) (D : KidData) (c : ℕ) (a b : E) : Val := B1.Val.ofArgs
  (kidArgs P c ++
  [ptrAt (P.W + c), gen ^ D.base c, gen ^ D.nx c, gen ^ D.ns c, a, b,
    gen ^ D.nx c * gen ^ D.ns c, (D.dx c).1, (D.dx c).2, gen ^ D.base c * gen ^ D.nx c, (D.ds c).1, (D.ds c).2,
    gen ^ (2 * c), gen ^ (3 * c), gen ^ (6 * c), gen ^ (12 * c), gen ^ (13 * c), gen ^ (26 * c),
    ptrAt (P.CC + 26 * c), gen ^ (2 * c), ptrAt (P.DD + 2 * c), (D.da c).1, (D.da c).2,
    (digestHalves (statementDigest P.seed (D.child c).statement)).1,
    (digestHalves (statementDigest P.seed (D.child c).statement)).2,
    gen ^ (2 * c), ptrAt (P.PI + 2 * c), ptrAt (P.PI + 2 * c),
    gen ^ (2 * c), gen ^ (3 * c), gen ^ (6 * c), gen ^ (12 * c), gen ^ (13 * c), gen ^ (26 * c), gen ^ (27 * c),
    gen ^ (54 * c), gen ^ (55 * c), ptrAt (P.CF + 55 * c),
    gen ^ D.base c * (gen ^ D.nx c * gen ^ D.ns c), ptrAt (P.W + c), word 2 0, gen ^ (c + 1),
    gen ^ (c + 1) + gen ^ P.n, word 2 0, gen ^ (c + 1)])

/-- Child `c`'s pushes: its lengths, its two lists' slots, its carried claim and DA digest, its hints. -/
def kidPush (bytecode : List K) (P : KidPtrs) (D : KidData) (c : ℕ) : List Pop :=
  ("child_meta", [gen ^ D.nx c, gen ^ D.ns c]) :: (D.px c ++ (D.ps c ++
    (("child_defer", D.defer c) :: ("child_da", [(D.da c).1, (D.da c).2]) ::
      Prover.childHints bytecode P.seed (D.child c))))

/-- `main_loop4` from the counter `g^j`: the children `j ..< n`'s pushes, every node exact. -/
def KidPost (bytecode : List K) (P : KidPtrs) (D : KidData) (j : ℕ) (rd : Reader) (t : Tree) : Prop :=
  SameStreams (t.pops coreProgram rd) ((List.range' j (P.n - j)).flatMap (kidPush bytecode P D)) ∧
    t.Every (ExactAt coreProgram rd)

/-- The cells of `main`'s arrays iteration `c` reads or writes. -/
def KidCells (P : KidPtrs) (D : KidData) (c i : ℕ) : Prop :=
  i = P.W + c ∨ i = P.W + c + 1 ∨ (P.CC + 26 * c ≤ i ∧ i < P.CC + 26 * c + 26) ∨
    (P.DD + 2 * c ≤ i ∧ i < P.DD + 2 * c + 2) ∨ (P.PI + 2 * c ≤ i ∧ i < P.PI + 2 * c + 2) ∨
    vsRegion P.GS (P.CF + 55 * c) (D.child c).freshClaim.cells.length i

/-- What iteration `c` reads of `main`'s words: the write counts, the carried claim, the DA digest,
the child's digest, `verify_sub`'s tables and the fresh claim. -/
def KidPre (P : KidPtrs) (D : KidData) (rd : Reader) : Prop :=
  ∀ c < P.n, LoadHolds rd (ptrAt (P.W + c)) 0 (gen ^ D.base c) ∧
    LoadHolds rd (ptrAt (P.W + c)) 1 (gen ^ D.base c * (gen ^ D.nx c * gen ^ D.ns c)) ∧
    ReadsAt rd (ptrAt (P.CC + 26 * c)) (D.defer c) ∧
    ReadsAt rd (ptrAt (P.DD + 2 * c)) [(D.da c).1, (D.da c).2] ∧
    ReadsAt rd (ptrAt (P.PI + 2 * c)) [(digestHalves (statementDigest P.seed (D.child c).statement)).1,
      (digestHalves (statementDigest P.seed (D.child c).statement)).2] ∧
    VerifySub.VerifySubPre rd (vsArgs P.seed (D.child c) (ptrAt P.GS) (ptrAt (P.CF + 55 * c))) ∧
    ReadsAt rd (ptrAt (P.CF + 55 * c)) (D.child c).freshClaim.cells

/-- **`main_loop4`'s hypotheses**: the counts (their words defined on every memory `Pre` admits),
the children's statements' digests from their parts, each child accepted, `verify_sub` complete,
the tables and fresh claims below `top`, the cells in `R`, `Pre` giving `KidPre`, and the two claim
walks complete placed at every frame past `top`. -/
structure KidHyps (al : String → Bool) (k : ℕ) (bytecode : List K) (P : KidPtrs) (D : KidData)
    (R : ℕ → Prop) (Pre : Reader → Prop) (top : ℕ) : Prop where
  n_lt : P.n < 2 ^ 34
  low : ∀ c < P.n, ∀ rd, LowDef k rd → Pre rd →
    (rd (addressOfIndex (D.nx c))).isSome ∧ (rd (addressOfIndex (D.ns c))).isSome
  defer_len : ∀ c < P.n, (D.defer c).length = 26
  digest : ∀ c < P.n, statementDigest P.seed (D.child c).statement =
    keccak256 (stmtBytes [(digestHalves P.seed).1, (digestHalves P.seed).2, (D.dx c).1, (D.dx c).2,
      (D.ds c).1, (D.ds c).2, (D.da c).1, (D.da c).2] (D.defer c))
  ok : ∀ c < P.n, VsChildOk bytecode P.seed (D.child c)
  vs : VsCompleteHypA al k bytecode P.seed
  top_tab : P.GS + expTabLen ≤ top
  top_fresh : ∀ c < P.n, P.CF + 55 * c + (D.child c).freshClaim.cells.length ≤ top
  region : ∀ c < P.n, ∀ i, KidCells P D c i → R i
  pre : ∀ rd, Pre rd → KidPre P D rd
  lx : ∀ c < P.n, ∀ fp cur, top ≤ fp → fp + B2C.fs "child_claim_list_digest" ≤ cur → ∃ e,
    (cur < 2 ^ 60 → e ≤ cur + 2 ^ 40) ∧ CallAtA B2C.fs al B2C.cert k "child_claim_list_digest"
      [ptrAt P.TX, ptrAt P.CV, gen ^ D.base c, gen ^ P.sx, gen ^ D.nx c] [(D.dx c).1, (D.dx c).2] R
      (fun _ => False) (fun _ => True) Pre
      (fun rd t => SameStreams (t.pops coreProgram rd) (D.px c) ∧ t.Every (ExactAt coreProgram rd))
      (B2C.fs "child_claim_list_digest") fp cur e
  sp : ∀ c < P.n, ∀ fp cur, top ≤ fp → fp + B2C.fs "child_claim_list_digest" ≤ cur → ∃ e,
    (cur < 2 ^ 60 → e ≤ cur + 2 ^ 40) ∧ CallAtA B2C.fs al B2C.cert k "child_claim_list_digest"
      [ptrAt P.TS, ptrAt P.SC, gen ^ D.base c * gen ^ D.nx c, gen ^ P.ss, gen ^ D.ns c] [(D.ds c).1, (D.ds c).2] R
      (fun _ => False) (fun _ => True) Pre
      (fun rd t => SameStreams (t.pops coreProgram rd) (D.ps c) ∧ t.Every (ExactAt coreProgram rd))
      (B2C.fs "child_claim_list_digest") fp cur e

/-- The block of `main_loop4`'s last `m` iterations and its skipped tail. -/
noncomputable def kidBlock (m : ℕ) : ℕ := m * B2C.fs name% «main_loop4» + B2C.fs (tailKey name% «main_loop4»)

/-- A child's iteration's bound on its cursor step, `2^42` (a constant, so that `omega` takes multiples of
it as atoms). -/
def kidB : ℕ := 2 ^ 42

theorem kidB_eq : kidB = 2 ^ 42 := rfl

/-- At most `16` iterations' block and `2^46` within `2^51`. -/
theorem kidBlock_add_le {n : ℕ} (hn : n ≤ 16) : kidBlock n + 2 ^ 46 ≤ 2 ^ 51 := by
  unfold kidBlock
  have h1 := B2C.fs_lt name% «main_loop4»
  have h2 := B2C.fs_lt (tailKey name% «main_loop4»)
  have : n * B2C.fs name% «main_loop4» ≤ 16 * 2 ^ 30 := Nat.mul_le_mul hn h1.le
  omega

theorem kidBlock_succ (m : ℕ) : kidBlock (m + 1) = B2C.fs name% «main_loop4» + kidBlock m := by
  unfold kidBlock; ring

theorem CallAtA.cur_le {fs : String → ℕ} {al : String → Bool} {cert : String → V → ℕ} {k : ℕ} {f : String}
    {args rets : List E} {R D : ℕ → Prop} {Out Pre : Reader → Prop} {Post : Reader → Tree → Prop} {B fp c e : ℕ}
    (h : CallAtA fs al cert k f args rets R D Out Pre Post B fp c e) : c ≤ e :=
  h.choose_spec.2.1

theorem kid_def {rd : Reader} {e : ℕ} (h : (rd (addressOfIndex e)).isSome) :
    LoadHolds rd (gen ^ e) 0 ((rd (addressOfIndex e)).getD 0) := by
  rw [gen_pow_eq_ofK]
  refine ⟨(isInK_iff _).mpr ⟨_, rfl⟩, ?_⟩
  rw [Main.addr_ofK, Nat.add_zero]
  obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp h
  rw [hv]; rfl

theorem gp {a b c : ℕ} (h : a = b + c) : gen ^ a = gen ^ b * gen ^ c := by rw [h, pow_add]

theorem ss_cons {a b : List Pop} (x : Pop) (h : SameStreams a b) : SameStreams (x :: a) (x :: b) :=
  SameStreams.append (a := [x]) (b := [x]) (fun _ => rfl) h

theorem kidsValid_tail {rd : Reader} {σ : Val} {c : Call} {cs : List Call} {t : Tree} {ts : List Tree}
    (h : Tree.KidsValid coreProgram rd σ (c :: cs) (t :: ts)) : Tree.KidsValid coreProgram rd σ cs ts := by
  rw [Tree.KidsValid] at h
  split at h
  · exact h.2.2
  · exact h.2.2

theorem kid_hints (σ : Val) : heapHintAddrs σ (kidPre.flatMap (slEvs σ)) =
    (List.range 26).map (fun k => (σ (.n 34)).limb 0 * addressOfIndex (0 + k)) ++
      (List.range 2).map (fun k => (σ (.n 36)).limb 0 * addressOfIndex (0 + k)) := by
  by_cases h : σ (.n 58) = 0
  · simp only [kidPre, List.flatMap_cons, List.flatMap_nil, slEvs, h, ↓reduceIte]; rfl
  · simp only [kidPre, List.flatMap_cons, List.flatMap_nil, slEvs, h, ↓reduceIte]; rfl

theorem kid_splice (rd : Reader) (σ : Val) (a b c d e : List Pop) :
    splice rd σ (kidPre.flatMap (slEvs σ)) [a, b, c, d, e] =
      ("child_meta", [σ (.n 18), σ (.n 19)]) :: (a ++ (b ++
        (("child_defer", (Dest.heap (.n 34) 0 26).words rd σ) ::
          ("child_da", (Dest.heap (.n 36) 0 2).words rd σ) :: (c ++ (d ++ e))))) := by
  by_cases h : σ (.n 58) = 0
  · simp only [kidPre, List.flatMap_cons, List.flatMap_nil, slEvs, h, ↓reduceIte]
    simp [splice, Atom.pops, Hint.pops, Dest.words]
  · simp only [kidPre, List.flatMap_cons, List.flatMap_nil, slEvs, h, ↓reduceIte]
    simp [splice, Atom.pops, Hint.pops, Dest.words]

/-! ## One iteration -/

/-- The calls of iteration `c`'s path. -/
theorem kid_calls (σ : Val) : (kidPre.filterMap Stmt.callS).map (mkCall σ) =
    [⟨"child_claim_list_digest", [.n 3, .n 4, .n 17, .n 5, .n 18], [.n 23, .n 24], true⟩,
      ⟨"child_claim_list_digest", [.n 6, .n 7, .n 25, .n 8, .n 19], [.n 26, .n 27], true⟩,
      ⟨"statement_digest", [.n 11, .n 12, .n 23, .n 24, .n 26, .n 27, .n 37, .n 38, .n 34], [.n 39, .n 40], true⟩,
      ⟨"verify_sub", [.n 39, .n 40, .n 11, .n 12, .n 14, .n 53], [], true⟩,
      ⟨name% «main_loop4», [.n 60, .n 1, .n 2, .n 3, .n 4, .n 5, .n 6, .n 7, .n 8, .n 9, .n 10, .n 11, .n 12, .n 13,
        .n 14, .n 15], [], decide (σ (.n 58) ≠ 0)⟩] := rfl


/-! ## Iteration `c`'s values -/

section Vals

variable (P : KidPtrs) (D : KidData) (c : ℕ) (a b : E)

theorem kid_params : (fn% «main_loop4»).params = [.n 0, .n 1, .n 2, .n 3, .n 4, .n 5, .n 6, .n 7, .n 8, .n 9, .n 10,
    .n 11, .n 12, .n 13, .n 14, .n 15] := rfl

theorem kidσ_args : (fn% «main_loop4»).params.map (kidσ P D c a b) = kidArgs P c := by
  rw [kid_params]; simp only [kidσ, kidArgs, B1.ofArgs_n, List.cons_append, List.nil_append, List.getD_cons_succ, List.getD_cons_zero, List.map_cons, List.map_nil]

theorem kid_tailArgs : [V.n 60, .n 1, .n 2, .n 3, .n 4, .n 5, .n 6, .n 7, .n 8, .n 9, .n 10, .n 11, .n 12, .n 13, .n 14,
    .n 15].map (kidσ P D c a b) = kidArgs P (c + 1) := by simp only [kidσ, kidArgs, B1.ofArgs_n, List.cons_append, List.nil_append, List.getD_cons_succ, List.getD_cons_zero, List.map_cons, List.map_nil]

theorem kid_lxArgs : [V.n 3, .n 4, .n 17, .n 5, .n 18].map (kidσ P D c a b) =
    [ptrAt P.TX, ptrAt P.CV, gen ^ D.base c, gen ^ P.sx, gen ^ D.nx c] := by simp only [kidσ, kidArgs, B1.ofArgs_n, List.cons_append, List.nil_append, List.getD_cons_succ, List.getD_cons_zero, List.map_cons, List.map_nil]

theorem kid_lxRets : [V.n 23, .n 24].map (kidσ P D c a b) = [(D.dx c).1, (D.dx c).2] := by simp only [kidσ, kidArgs, B1.ofArgs_n, List.cons_append, List.nil_append, List.getD_cons_succ, List.getD_cons_zero, List.map_cons, List.map_nil]

theorem kid_spArgs : [V.n 6, .n 7, .n 25, .n 8, .n 19].map (kidσ P D c a b) =
    [ptrAt P.TS, ptrAt P.SC, gen ^ D.base c * gen ^ D.nx c, gen ^ P.ss, gen ^ D.ns c] := by simp only [kidσ, kidArgs, B1.ofArgs_n, List.cons_append, List.nil_append, List.getD_cons_succ, List.getD_cons_zero, List.map_cons, List.map_nil]

theorem kid_spRets : [V.n 26, .n 27].map (kidσ P D c a b) = [(D.ds c).1, (D.ds c).2] := by simp only [kidσ, kidArgs, B1.ofArgs_n, List.cons_append, List.nil_append, List.getD_cons_succ, List.getD_cons_zero, List.map_cons, List.map_nil]

theorem kid_sdArgs : [V.n 11, .n 12, .n 23, .n 24, .n 26, .n 27, .n 37, .n 38, .n 34].map (kidσ P D c a b) =
    [(digestHalves P.seed).1, (digestHalves P.seed).2, (D.dx c).1, (D.dx c).2, (D.ds c).1, (D.ds c).2,
      (D.da c).1, (D.da c).2, ptrAt (P.CC + 26 * c)] := by simp only [kidσ, kidArgs, B1.ofArgs_n, List.cons_append, List.nil_append, List.getD_cons_succ, List.getD_cons_zero, List.map_cons, List.map_nil]

theorem kid_sdRets : [V.n 39, .n 40].map (kidσ P D c a b) =
    [(digestHalves (statementDigest P.seed (D.child c).statement)).1,
      (digestHalves (statementDigest P.seed (D.child c).statement)).2] := by simp only [kidσ, kidArgs, B1.ofArgs_n, List.cons_append, List.nil_append, List.getD_cons_succ, List.getD_cons_zero, List.map_cons, List.map_nil]

theorem kid_vsArgs : [V.n 39, .n 40, .n 11, .n 12, .n 14, .n 53].map (kidσ P D c a b) =
    vsArgs P.seed (D.child c) (ptrAt P.GS) (ptrAt (P.CF + 55 * c)) := by simp only [vsArgs, kidσ, kidArgs, B1.ofArgs_n, List.cons_append, List.nil_append, List.getD_cons_succ, List.getD_cons_zero, List.map_cons, List.map_nil]

theorem kid_58 : kidσ P D c a b (.n 58) = gen ^ c * word 2 0 + gen ^ P.n := by
  rw [gen_mul_two]; simp only [kidσ, kidArgs, B1.ofArgs_n, List.cons_append, List.nil_append, List.getD_cons_succ,
    List.getD_cons_zero]

theorem kid_evs (a' b' : E) : kidPre.flatMap (slEvs (kidσ P D c a b)) = kidPre.flatMap (slEvs (kidσ P D c a' b')) := by
  have h : kidσ P D c a b (.n 58) = kidσ P D c a' b' (.n 58) := by rw [kid_58, kid_58]
  simp only [kidPre, List.flatMap_cons, List.flatMap_nil, slEvs, h]

end Vals

theorem kid_guard (P : KidPtrs) (D : KidData) {j : ℕ} (hn : P.n < 2 ^ 34) (hj : j < P.n) (a b : E) :
    decide (kidσ P D j a b (.n 58) ≠ 0) = decide (j + 1 ≠ P.n) := by
  rw [kid_58, loopGuard_taken hn (by omega)]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
/-- **One iteration of `main_loop4` completes placed**, given the next one's completeness. -/
theorem kid_step {al : String → Bool} {k : ℕ} {bytecode : List K} (hwf : coreProgram.Wf) {P : KidPtrs}
    {D : KidData} {R : ℕ → Prop} {Pre : Reader → Prop} {top : ℕ} (H : KidHyps al k bytecode P D R Pre top)
    {j : ℕ} (hj : j < P.n) {fp c : ℕ} (hfc : fp + kidBlock (P.n - j) ≤ c) (htc : top ≤ c)
    (htail : j + 1 < P.n → ∀ fp' c', fp' + kidBlock (P.n - (j + 1)) ≤ c' → top ≤ c' → ∃ e,
      (c' + (P.n - (j + 1)) * kidB < 2 ^ 59 → e ≤ c' + (P.n - (j + 1)) * kidB) ∧
      CallAtA B2C.fs al B2C.cert k name% «main_loop4» (kidArgs P (j + 1)) [] R (fun _ => False) (fun _ => True)
        Pre (KidPost bytecode P D (j + 1)) (kidBlock (P.n - (j + 1))) fp' c' e) :
    ∃ e, (c + (P.n - j) * kidB < 2 ^ 59 → e ≤ c + (P.n - j) * kidB) ∧
      CallAtA B2C.fs al B2C.cert k name% «main_loop4» (kidArgs P j) [] R (fun _ => False) (fun _ => True)
      Pre (KidPost bytecode P D j) (kidBlock (P.n - j)) fp c e := by
  have hblk : kidBlock (P.n - j) = B2C.fs name% «main_loop4» + kidBlock (P.n - (j + 1)) := by
    rw [show P.n - j = P.n - (j + 1) + 1 by omega, kidBlock_succ]
  rw [hblk] at hfc ⊢
  set es := kidPre.flatMap (slEvs (kidσ P D j 0 0)) with hes
  have hcalls : calls es = (kidPre.filterMap Stmt.callS).map (mkCall (kidσ P D j 0 0)) :=
    (straight_parts (kidσ P D j 0 0) kidPre kidPre_straight).2.2.2
  have hal : allocs (kidσ P D j 0 0) es = [] := by
    rw [(straight_parts (kidσ P D j 0 0) kidPre kidPre_straight).2.1]; rfl
  -- the callees' ends
  obtain ⟨e1, hb1, h1⟩ := H.lx j hj (allocBase (al "child_claim_list_digest") c)
    (allocBase (al "child_claim_list_digest") c + B2C.fs "child_claim_list_digest")
    (htc.trans (Memory.le_allocBase _ c)) le_rfl
  have he1 : c ≤ e1 := (Memory.le_allocBase _ c).trans ((Nat.le_add_right _ _).trans h1.cur_le)
  obtain ⟨e2, hb2, h2⟩ := H.sp j hj (allocBase (al "child_claim_list_digest") e1)
    (allocBase (al "child_claim_list_digest") e1 + B2C.fs "child_claim_list_digest")
    (htc.trans (he1.trans (Memory.le_allocBase _ e1))) le_rfl
  have he2 : e1 ≤ e2 := (Memory.le_allocBase _ e1).trans ((Nat.le_add_right _ _).trans h2.cur_le)
  set e3 := allocBase (al "statement_digest") e2 + B2C.fs "statement_digest" with he3d
  have he3 : e2 ≤ e3 := (Memory.le_allocBase _ e2).trans (Nat.le_add_right _ _)
  have h3 := statement_digest_callAtA (fs := B2C.fs) (al := al) (cert := B2C.cert) hwf k
    (args := [(digestHalves P.seed).1, (digestHalves P.seed).2, (D.dx j).1, (D.dx j).2, (D.ds j).1, (D.ds j).2,
      (D.da j).1, (D.da j).2, ptrAt (P.CC + 26 * j)])
    (rets := [(digestHalves (statementDigest P.seed (D.child j).statement)).1,
      (digestHalves (statementDigest P.seed (D.child j).statement)).2]) rfl (b := P.CC + 26 * j) rfl
    (Pre := Pre) (fun rd hp => ⟨D.defer j, H.defer_len j hj, (H.pre rd hp j hj).2.2.1, by rw [H.digest j hj]; rfl⟩)
    (allocBase (al "statement_digest") e2) e3
  obtain ⟨e4, hb4, h4⟩ := H.vs.at (H.ok j hj) (qt := P.GS) (qo := P.CF + 55 * j) (cur := e3)
    (by have := H.top_tab; omega) (by have := H.top_fresh j hj; omega)
  have he4 : e3 ≤ e4 := (Memory.le_allocBase _ e3).trans ((Nat.le_add_right _ _).trans h4.cur_le)
  -- the tail
  obtain ⟨e, hle, hT⟩ : ∃ e, (e4 + (P.n - (j + 1)) * kidB < 2 ^ 59 → e ≤ e4 + (P.n - (j + 1)) * kidB) ∧
      ∀ (R' : ℕ → Prop), (∀ i, R i → R' i) → ∀ (O : Reader → Prop) (Dacc : ℕ → Prop),
      KidsAtL B2C.fs al B2C.cert k (kidσ P D j 0 0) R' Pre (fp + B2C.fs name% «main_loop4») O Dacc
        [KidPost bytecode P D (j + 1)]
        [⟨name% «main_loop4», [.n 60, .n 1, .n 2, .n 3, .n 4, .n 5, .n 6, .n 7, .n 8, .n 9, .n 10, .n 11, .n 12,
          .n 13, .n 14, .n 15], [], decide ((kidσ P D j 0 0) (.n 58) ≠ 0)⟩] e4 e (kidBlock (P.n - (j + 1)))
        (fun _ => True) (fun _ => False) := by
    by_cases hlt : j + 1 < P.n
    · obtain ⟨e5, hb5, h5⟩ := htail hlt (fp + B2C.fs name% «main_loop4») e4 (by omega) (by omega)
      have htk : decide ((kidσ P D j 0 0) (.n 58) ≠ 0) = true := by
        rw [kid_guard P D H.n_lt hj]; exact decide_eq_true (by omega)
      refine ⟨e5, hb5, fun R' hR' O Dacc => ?_⟩
      rw [KidsAtL]; simp only [htk, ↓reduceIte]
      rw [kid_tailArgs, List.map_nil]
      exact ⟨R, fun _ => False, fun _ => True, fun i hi => Or.inl (hR' i hi),
        h5.mono (fun _ h => h) (fun _ h => h) (fun _ _ => trivial) (fun _ h => h.1) (fun _ _ _ h => h),
        fun _ _ _ => trivial, fun _ h => h.elim⟩
    · have htk : decide ((kidσ P D j 0 0) (.n 58) ≠ 0) = false := by
        rw [kid_guard P D H.n_lt hj]; exact decide_eq_false (by omega)
      refine ⟨e4, fun _ => Nat.le_add_right _ _, fun R' hR' O Dacc => ?_⟩
      rw [KidsAtL, ite_eq_right_of_eq_false _ _ (by simp [htk])]
      refine ⟨⟨kidσ P D (j + 1) 0 0, fn% «main_loop4», find_kid,
        (kidσ_args P D (j + 1) 0 0).trans (kid_tailArgs P D j 0 0).symm⟩, ?_, rfl, fun _ _ => trivial,
        fun _ h => h.elim⟩
      rw [show P.n - (j + 1) = 0 by omega, kidBlock]; simp
  have hbound : c + (P.n - j) * kidB < 2 ^ 59 → e ≤ c + (P.n - j) * kidB := fun hc => by
    have hnj : (P.n - j) * kidB = (P.n - (j + 1)) * kidB + kidB := by
      rw [show P.n - j = P.n - (j + 1) + 1 by omega, Nat.add_mul, Nat.one_mul]
    have hK := kidB_eq
    have a1 := Memory.allocBase_le (al "child_claim_list_digest") c
    have a2 := Memory.allocBase_le (al "child_claim_list_digest") e1
    have a3 := Memory.allocBase_le (al "statement_digest") e2
    have a4 := Memory.allocBase_le (al "verify_sub") e3
    have f1 := B2C.fs_lt "child_claim_list_digest"
    have f3 := B2C.fs_lt "statement_digest"
    have f4 := B2C.fs_lt "verify_sub"
    have b1 := hb1 (by omega)
    have b2 := hb2 (by omega)
    have b4 := hb4 (by omega)
    have b5 := hle (by omega)
    omega
  refine ⟨e, hbound, callAtA_nodeLRd kid_loop hfc ⟨(kidσ P D j 0 0), fn% «main_loop4», es, [], [],
    [fun rd t => SameStreams (t.pops coreProgram rd) (D.px j) ∧ t.Every (ExactAt coreProgram rd),
      fun rd t => SameStreams (t.pops coreProgram rd) (D.ps j) ∧ t.Every (ExactAt coreProgram rd),
      FreePost,
      fun rd t => SameStreams (t.pops coreProgram rd) (Prover.childHints bytecode P.seed (D.child j)) ∧
        t.Every (ExactAt coreProgram rd),
      KidPost bytecode P D (j + 1)], fun _ => True, fun _ => False, find_kid, ?_, fun _ h => h.elim, ?_,
    fun _ _ => trivial, ?_⟩⟩
  · rw [hal]; exact ⟨by simp, List.Pairwise.nil⟩
  · -- the callees
    rw [hcalls, hal, kid_calls, List.sum_nil, Nat.add_zero]
    rw [KidsAtL]; simp only [↓reduceIte]
    rw [kid_lxArgs, kid_lxRets]
    refine ⟨B2C.fs "child_claim_list_digest", e1, R, fun _ => False, fun _ => True, fun i hi => Or.inl (Or.inl hi),
      h1.mono (fun _ h => h) (fun _ h => h) (fun _ _ => trivial) (fun _ h => h.1) (fun _ _ _ h => h), ?_⟩
    rw [KidsAtL]; simp only [↓reduceIte]
    rw [kid_spArgs, kid_spRets]
    refine ⟨B2C.fs "child_claim_list_digest", e2, R, fun _ => False, fun _ => True, fun i hi => Or.inl (Or.inl hi),
      h2.mono (fun _ h => h) (fun _ h => h) (fun _ _ => trivial) (fun _ h => h.1) (fun _ _ _ h => h), ?_⟩
    rw [KidsAtL]; simp only [↓reduceIte]
    rw [kid_sdArgs, kid_sdRets]
    refine ⟨B2C.fs "statement_digest", e3, fun i => P.CC + 26 * j ≤ i ∧ i < P.CC + 26 * j + 26, fun _ => False,
      fun _ => True, fun i hi => Or.inl (Or.inl (H.region j hj i (Or.inr (Or.inr (Or.inl hi))))),
      h3.mono (fun _ h => h) (fun _ h => h) (fun _ _ => trivial) (fun _ h => h.1) (fun _ _ _ h => h), ?_⟩
    rw [KidsAtL]; simp only [↓reduceIte]
    rw [kid_vsArgs, List.map_nil]
    refine ⟨B2C.fs "verify_sub", e4, vsRegion P.GS (P.CF + 55 * j) (D.child j).freshClaim.cells.length,
      fun _ => False, fun _ => True,
      fun i hi => Or.inl (Or.inl (H.region j hj i (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hi))))))),
      h4.mono (fun _ h => h) (fun _ h => h) (fun _ _ => trivial)
        (fun rd h => ⟨(H.pre rd h.1 j hj).2.2.2.2.2.1, (H.pre rd h.1 j hj).2.2.2.2.2.2⟩) (fun _ _ _ h => h), ?_⟩
    exact hT _ (fun i h => Or.inl h) _ _
  · -- on each memory
    intro rd hl hp _
    obtain ⟨hw0, hw1, hdf, hda, hpi, -, -⟩ := H.pre rd hp j hj
    set σ := kidσ P D j ((rd (addressOfIndex (D.nx j))).getD 0) ((rd (addressOfIndex (D.ns j))).getD 0) with hσ
    have hesσ : es = kidPre.flatMap (slEvs σ) := by rw [hes, hσ]; exact kid_evs P D j 0 0 _ _
    have hw : walk σ (fn% «main_loop4»).body = .ret es [] := by
      rw [hesσ, kid_body, walk_straight σ [] kidPre kidPre_straight]
    have hda0 : LoadHolds rd (ptrAt (P.DD + 2 * j)) 0 (D.da j).1 := hda 0 (by simp)
    have hda1 : LoadHolds rd (ptrAt (P.DD + 2 * j)) 1 (D.da j).2 := hda 1 (by simp)
    have hpi0 : LoadHolds rd (ptrAt (P.PI + 2 * j)) 0
        (digestHalves (statementDigest P.seed (D.child j).statement)).1 := hpi 0 (by simp)
    have hpi1 : LoadHolds rd (ptrAt (P.PI + 2 * j)) 1
        (digestHalves (statementDigest P.seed (D.child j).statement)).2 := hpi 1 (by simp)
    have hl0 := kid_def (H.low j hj rd hl hp).1
    have hl1 := kid_def (H.low j hj rd hl hp).2
    have hevs : ∀ ev ∈ es, ev.Holds rd σ := by
      rw [hesσ]
      refine events_straight fun s hs => ?_
      simp only [kidPre, List.mem_cons, List.mem_nil_iff, or_false] at hs
      rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
        rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
        rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      all_goals simp only [SOk, Atom.Holds, hσ, kidσ, kidArgs, B1.ofArgs_n, List.cons_append, List.nil_append,
        List.getD_cons_succ, List.getD_cons_zero]
      all_goals first
        | with_reducible exact hw0
        | with_reducible exact hw1
        | with_reducible exact hda0
        | with_reducible exact hda1
        | with_reducible exact hpi0
        | with_reducible exact hpi1
        | with_reducible exact hl0
        | with_reducible exact hl1
        | with_reducible exact (ptrAt_mul_gen_pow _ _).symm
        | with_reducible exact (gen_mul_two _).symm
        | with_reducible exact gen_pow_add_isInK _ _
        | with_reducible exact gp (by ring)
    have halσ : allocs σ es = allocs (kidσ P D j 0 0) es := by
      rw [hal, hesσ, (straight_parts σ kidPre kidPre_straight).2.1]; rfl
    refine ⟨σ, by rw [hσ]; exact kidσ_args P D j _ _, hw, rfl, halσ, ?_, ?_, ?_, ?_, hevs, ?_⟩
    · -- placed: no `HeapBuf`, no `frameAddr`
      rw [hal]
      refine ⟨?_, ?_⟩
      · rw [(straight_parts (kidσ P D j 0 0) kidPre kidPre_straight).1]; rfl
      · rw [(straight_parts (kidσ P D j 0 0) kidPre kidPre_straight).2.2.1]; simp [kidPre, Stmt.addrS]
    · intro cl hcl
      rw [hcalls, kid_calls] at hcl
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hcl
      rcases hcl with rfl | rfl | rfl | rfl | rfl <;>
        simp only [hσ, kid_lxArgs, kid_lxRets, kid_spArgs, kid_spRets, kid_sdArgs, kid_sdRets, kid_vsArgs,
          kid_tailArgs, List.map_nil, and_self]
    · -- the loads
      intro A hA
      rw [hesσ, Memory.loadAddrs_straight σ kidPre kidPre_straight] at hA
      simp only [kidPre, List.filterMap_cons, stmtLoad?, List.filterMap_nil, List.map_cons, List.map_nil,
        List.mem_cons, List.mem_nil_iff, or_false] at hA
      have hR := H.region j hj
      rcases hA with rfl | rfl | rfl | rfl | rfl | rfl
      all_goals simp only [hσ, kidσ, kidArgs, B1.ofArgs_n, List.cons_append, List.nil_append, List.getD_cons_succ, List.getD_cons_zero]
      · exact ⟨P.W + j + 0, Main.addr_ofK _ _, Or.inr (Or.inl (hR _ (by unfold KidCells; omega)))⟩
      · exact ⟨P.DD + 2 * j + 0, Main.addr_ofK _ _, Or.inr (Or.inl (hR _ (by unfold KidCells; omega)))⟩
      · exact ⟨P.DD + 2 * j + 1, Main.addr_ofK _ _, Or.inr (Or.inl (hR _ (by unfold KidCells; omega)))⟩
      · exact ⟨P.PI + 2 * j + 0, Main.addr_ofK _ _, Or.inr (Or.inl (hR _ (by unfold KidCells; omega)))⟩
      · exact ⟨P.PI + 2 * j + 1, Main.addr_ofK _ _, Or.inr (Or.inl (hR _ (by unfold KidCells; omega)))⟩
      · exact ⟨P.W + j + 1, Main.addr_ofK _ _, Or.inr (Or.inl (hR _ (by unfold KidCells; omega)))⟩
    · -- the heap hints
      intro A hA
      rw [hesσ, kid_hints] at hA
      simp only [List.mem_append, List.mem_map, List.mem_range] at hA
      have hR := H.region j hj
      rcases hA with ⟨i, hi, rfl⟩ | ⟨i, hi, rfl⟩
      all_goals simp only [hσ, kidσ, kidArgs, B1.ofArgs_n, List.cons_append, List.nil_append, List.getD_cons_succ, List.getD_cons_zero]
      · exact ⟨P.CC + 26 * j + (0 + i), Main.addr_ofK _ _, Or.inr (Or.inl (hR _ (by unfold KidCells; omega)))⟩
      · exact ⟨P.DD + 2 * j + (0 + i), Main.addr_ofK _ _, Or.inr (Or.inl (hR _ (by unfold KidCells; omega)))⟩
    · -- the tree's pops and exactness
      intro ts hv hq
      have e18 : σ (.n 18) = gen ^ D.nx j := by simp only [hσ, kidσ, kidArgs, B1.ofArgs_n, List.cons_append, List.nil_append, List.getD_cons_succ, List.getD_cons_zero]
      have e19 : σ (.n 19) = gen ^ D.ns j := by simp only [hσ, kidσ, kidArgs, B1.ofArgs_n, List.cons_append, List.nil_append, List.getD_cons_succ, List.getD_cons_zero]
      have e34 : σ (.n 34) = ptrAt (P.CC + 26 * j) := by simp only [hσ, kidσ, kidArgs, B1.ofArgs_n, List.cons_append, List.nil_append, List.getD_cons_succ, List.getD_cons_zero]
      have e36 : σ (.n 36) = ptrAt (P.DD + 2 * j) := by simp only [hσ, kidσ, kidArgs, B1.ofArgs_n, List.cons_append, List.nil_append, List.getD_cons_succ, List.getD_cons_zero]
      rw [hcalls, kid_calls] at hv hq
      obtain ⟨t1, t2, t3, t4, t5, rfl⟩ : ∃ t1 t2 t3 t4 t5, ts = [t1, t2, t3, t4, t5] := by
        have hlen := kidsValid_len hv
        match ts, hlen with
        | [t1, t2, t3, t4, t5], _ => exact ⟨t1, t2, t3, t4, t5, rfl⟩
      rw [kidsPost_cons, kidsPost_cons, kidsPost_cons, kidsPost_cons, kidsPost_cons] at hq
      obtain ⟨q1, q2, q3, q4, q5, -⟩ := hq
      obtain ⟨q1, x1⟩ := q1 rfl
      obtain ⟨q2, x2⟩ := q2 rfl
      obtain ⟨q3, x3⟩ := q3 rfl
      obtain ⟨q4, x4⟩ := q4 rfl
      have h5 : SameStreams (t5.pops coreProgram rd) ((List.range' (j + 1) (P.n - (j + 1))).flatMap
          (kidPush bytecode P D)) ∧ t5.Every (ExactAt coreProgram rd) := by
        by_cases hlt : j + 1 < P.n
        · exact q5 (by
            show decide ((kidσ P D j 0 0) (.n 58) ≠ 0) = true
            rw [kid_guard P D H.n_lt hj]; exact decide_eq_true (by omega))
        · have htk : decide ((kidσ P D j 0 0) (.n 58) ≠ 0) = false := by
            rw [kid_guard P D H.n_lt hj]; exact decide_eq_false (by omega)
          have hv5 := kidsValid_tail (kidsValid_tail (kidsValid_tail (kidsValid_tail hv)))
          rw [Tree.KidsValid] at hv5
          simp only [htk, Bool.false_eq_true, ↓reduceIte] at hv5
          obtain ⟨-, ⟨⟨f', σ', rfl⟩, -⟩, -⟩ := hv5
          rw [show P.n - (j + 1) = 0 by omega]
          exact ⟨fun _ => rfl, Tree.every_phantom⟩
      refine ⟨?_, Tree.every_node.mpr ⟨exactAt_of_walk find_kid hw (exact_of_pinned kid_pin hw hevs rd),
        x1, x2, x3, x4, h5.2, trivial⟩⟩
      have hd34 : (Dest.heap (.n 34) 0 26).words rd σ = D.defer j := by
        have := heap_words (σ := σ) (p := .n 34) (by rw [e34]; exact hdf)
        rwa [H.defer_len j hj] at this
      have hd36 : (Dest.heap (.n 36) 0 2).words rd σ = [(D.da j).1, (D.da j).2] :=
        heap_words (σ := σ) (p := .n 36) (by rw [e36]; exact hda)
      rw [pops_straight find_kid kid_body kidPre_straight σ, Tree.popsKids, Tree.popsKids, Tree.popsKids,
        Tree.popsKids, Tree.popsKids, Tree.popsKids, kid_splice, q3, hd34, hd36, e18, e19,
        show P.n - j = P.n - (j + 1) + 1 by omega, List.range'_succ, List.flatMap_cons]
      simp only [kidPush, List.cons_append, List.append_assoc, List.nil_append]
      exact ss_cons _ (q1.append (q2.append (ss_cons _ (ss_cons _ (q4.append h5.1)))))

/-- **`main_loop4` completes placed** from every child `j < n`, at every frame and cursor past its
block and `top`: its pops the children's pushes stream by stream, every node exact, ending within
`kidB = 2^42` per child left of its cursor when that stays below `2^59`. -/
theorem kidL_callAtA {al : String → Bool} {k : ℕ} {bytecode : List K} (hwf : coreProgram.Wf) {P : KidPtrs}
    {D : KidData} {R : ℕ → Prop} {Pre : Reader → Prop} {top : ℕ} (H : KidHyps al k bytecode P D R Pre top) :
    ∀ j < P.n, ∀ fp c, fp + kidBlock (P.n - j) ≤ c → top ≤ c → ∃ e,
      (c + (P.n - j) * kidB < 2 ^ 59 → e ≤ c + (P.n - j) * kidB) ∧
      CallAtA B2C.fs al B2C.cert k name% «main_loop4» (kidArgs P j) [] R (fun _ => False) (fun _ => True)
        Pre (KidPost bytecode P D j) (kidBlock (P.n - j)) fp c e := by
  have key : ∀ t j, j + 1 + t = P.n → ∀ fp c, fp + kidBlock (P.n - j) ≤ c → top ≤ c → ∃ e,
      (c + (P.n - j) * kidB < 2 ^ 59 → e ≤ c + (P.n - j) * kidB) ∧
      CallAtA B2C.fs al B2C.cert k name% «main_loop4» (kidArgs P j) [] R (fun _ => False) (fun _ => True)
        Pre (KidPost bytecode P D j) (kidBlock (P.n - j)) fp c e := by
    intro t
    induction t with
    | zero => intro j hj fp c hfc htc; exact kid_step hwf H (by omega) hfc htc fun h' => absurd h' (by omega)
    | succ t ih => intro j hj fp c hfc htc; exact kid_step hwf H (by omega) hfc htc fun _ => ih (j + 1) (by omega)
  intro j hj
  exact key (P.n - j - 1) j (by omega)

end
end LeanVM.Guest.Complete
