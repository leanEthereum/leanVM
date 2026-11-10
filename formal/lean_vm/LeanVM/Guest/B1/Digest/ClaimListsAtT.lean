/-
  LeanVM.Guest.B1.Digest.ClaimListsAtT

  `child_claim_list_digest` in the uniform placed form by a tree of honest shape
  (`Budget.NodeHonest`): the honest run takes the walk by hinted indices (`child_mono` hinted `0`),
  `child_claim_list_any`, which places the chain buffer.
-/

module

public import LeanVM.Guest.B1.Digest.ChildListAt
public import LeanVM.Guest.B1.Digest.ChildDigest

/-!
# A child's claim list, placed

The body (G:4186-4207) is a branch on `n = 0` between two runs (`ccd_body`). The empty list's arm
hashes the empty string (`ccz_core`: the evaluated valuation, its atoms holding). The nonempty
list's arm (`ccElse`) calls `list_split`, hints `child_mono`, and branches on `child_mono + g`:
the honest prover hints `0`, so the run takes the walk by hinted indices, a call of
`child_claim_list_any` (`ccEσ`: the valuation, written out). Either walk is sound
(`child_claim_list_digest_sound`); completeness picks its own hints.

`ccQ n σ`: the list's length `g^n` at `v4`; when `n ≠ 0`, `list_split`'s returns `g^a`, `g^b`, `g^c`
at `v26`, `v27`, `v28` (`n = 136a + 17b + c`), the hint `0` at `v29`. `ccCalls n`: none for the
empty list; `list_split`, `child_claim_list_any`. `ccBufs n`: none (`child_claim_list_any` places
the chain buffer). `ccTs n`: `child_claim_list_any`'s tree of honest shape `anyHonest n`.

`cc_nonempty`: the nonempty list placed, given its callees complete at their running offsets
(`KidsAt`, a predicate `P` on their words); `child_claim_list_digest_completeAtT`,
`_completeAt`: `n < 136 · 2^16` honest records among the caller's words (`RecMem`, region form),
the digest of their cells.
-/

namespace LeanVM.Guest.B1.Digest

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Value.Keccak
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Guest.Memory LeanVM.Guest.B1.Fwd
open LeanVM.Guest.B1 (CompleteAtD CompleteAtDT KidsDT kidsFromInT_of_kidsDT Returns Kid DisjL Within
  regionsOk_of LowDef)
open LeanVM.Guest.B1.Main (Layout MemL RegionL memL_append)
open LeanVM.Guest.B1.Da (SlOk slEvs_holds exists_of_length_succ)
open LeanVM.Guest.Budget (NodeHonest)

@[expose] public section

/-! ## The path -/

/-- The head of `child_claim_list_digest`'s body: `n_g + 1`. -/
def ccdHead : List Stmt := [.atom (.const (.n 5) (word 1 0)), .atom (.add (.n 6) (.n 4) (.n 5))]

/-- The final copies of `child_claim_list_digest`. -/
def ccdTail : List Stmt := [.atom (.copy (.n 25) (.n 13)), .atom (.copy (.n 26) (.n 14))]

/-- The nonempty arm before its branch: `list_split`, the hint `child_mono`, `child_mono + g`. -/
def ccE4 : List Stmt :=
  [.call "list_split" [.n 4] [.n 15, .n 16, .n 17],
    .atom (.hint (.witness "child_mono" (.stack [.n 18]))),
    .atom (.const (.n 19) (word 2 0)), .atom (.add (.n 20) (.n 18) (.n 19))]

/-- The gap walk's arm. -/
def ccMonoArm : List Stmt :=
  [.call "child_claim_list_mono" [.n 0, .n 1, .n 2, .n 3, .n 15, .n 16, .n 17] [.n 21, .n 22],
    .atom (.copy (.n 13) (.n 21)), .atom (.copy (.n 14) (.n 22))]

/-- The walk by hinted indices' arm. -/
def ccAnyArm : List Stmt :=
  [.call "child_claim_list_any" [.n 0, .n 1, .n 2, .n 3, .n 15, .n 16, .n 17] [.n 23, .n 24],
    .atom (.copy (.n 13) (.n 23)), .atom (.copy (.n 14) (.n 24))]

/-- The nonempty arm. -/
def ccElse : List Stmt := ccE4 ++ [.ite (.n 20) ccMonoArm ccAnyArm]

theorem ccd_body : Fn.body Data.core24 =
    ccdHead ++ .ite (.n 6) cc25Zero ccElse :: (ccdTail ++ [.ret [.n 25, .n 26]]) := by
  rw [core24_shape]; rfl

set_option maxRecDepth 100000 in
theorem cc25Zero_straight : cc25Zero.all Main.Stmt.straight = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem cc25Zero_parts : cc25Zero.filterMap Main.Stmt.allocSz = [] ∧
    cc25Zero.filterMap Main.Stmt.addrS = [] ∧ cc25Zero.filterMap Main.Stmt.callS = [] ∧
    cc25Zero.filterMap B1.Stmt.loadS = [] ∧ cc25Zero.all isAtomS = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem ccd_loop : coreProgram.loop "child_claim_list_digest" = false := by
  rw [Program.loop_of_find? find_child_claim_list_digest]; decide +kernel

theorem ccd_param (σ : Val) : (Fn.params Data.core24).map σ =
    [σ (.n 0), σ (.n 1), σ (.n 2), σ (.n 3), σ (.n 4)] := rfl

/-- A straight run, then a branch between straight arms, falls through. -/
theorem walk_pre_ite (σ : Val) (z n : List Stmt) (hz : z.all Main.Stmt.straight = true)
    (hn : n.all Main.Stmt.straight = true) (c : V) : ∀ pre : List Stmt,
    pre.all Main.Stmt.straight = true →
    walk σ (pre ++ [.ite c z n]) =
      .fall (pre.flatMap (Main.slEvs σ) ++ .inK c :: (if σ c = 0 then z else n).flatMap (Main.slEvs σ))
  | [], _ => by
    rw [List.nil_append, walk, walk1, walk]
    by_cases h : σ c = 0
    · simp only [h, ↓reduceIte, walk_straight_fall σ z hz, Out.pre, Out.seq, List.flatMap_nil,
        List.nil_append, List.append_nil, List.singleton_append]
    · simp only [h, ↓reduceIte, walk_straight_fall σ n hn, Out.pre, Out.seq, List.flatMap_nil,
        List.nil_append, List.append_nil, List.singleton_append]
  | s :: pre, h => by
    simp only [List.all_cons, Bool.and_eq_true] at h
    rw [List.cons_append, walk, walk_pre_ite σ z n hz hn c pre h.2, Main.walk1_straight σ s h.1,
      Out.seq, Out.pre, List.flatMap_cons, List.append_assoc]

/-! ## The empty list -/

/-- The empty list's run, evaluated. -/
noncomputable def ccZEval : List Stmt := ccdHead ++ cc25Zero ++ fillH 15 25 ++ ccdTail

/-- **The empty list's run, evaluated**: in order, no store, no side condition. -/
noncomputable def cczOk : Bool :=
  (chk 5 ccZEval).isSome && (storesOf 5 ccZEval).isEmpty && canonChk [] (atomsIn ccZEval) &&
    (atomsIn ccZEval).all (fun a => !needsSide a)

set_option maxRecDepth 100000 in
theorem ccz_ok : cczOk = true := by decide +kernel

/-- The empty list's valuation. -/
noncomputable def cczσ (rd : Reader) (args : List E) : Val :=
  B1.Val.ofArgs (ev rd (fun _ => 0) args ccZEval)

variable {rd : Reader}

set_option maxRecDepth 20000 in
/-- **The empty list's valuation**: its atoms hold, it returns the empty string's digest. -/
theorem ccz_core (entries region base limit : E) :
    let σ := cczσ rd [entries, region, base, limit, gen ^ 0]
    (∀ a ∈ atomsIn ccZEval, a.Holds rd σ) ∧
      [σ (.n 0), σ (.n 1), σ (.n 2), σ (.n 3), σ (.n 4)] = [entries, region, base, limit, gen ^ 0] ∧
      σ (.n 6) = 0 ∧ σ (.n 6) = gen ^ 0 + gen ^ 0 ∧
      [σ (.n 25), σ (.n 26)] = digestCells (keccak256 (cellsBytes [])) := by
  intro σ
  have hz1 := cc25z_ok
  have hb1 := ccz_ok
  simp only [cc25ZOk, Bool.and_eq_true, decide_eq_true_eq] at hz1
  simp only [cczOk, Bool.and_eq_true] at hb1
  obtain ⟨⟨⟨-, hzc⟩, hz13⟩, hz14⟩ := hz1
  obtain ⟨⟨⟨b12, b13⟩, b14⟩, b15⟩ := hb1
  have c5 : Stmt.atom (.const (.n 5) (word 1 0)) ∈ ccdHead := by simp [ccdHead]
  have a6 : Stmt.atom (.add (.n 6) (.n 4) (.n 5)) ∈ ccdHead := by simp [ccdHead]
  have t36 : Stmt.atom (.copy (.n 25) (.n 13)) ∈ ccdTail := by simp [ccdTail]
  have t37 : Stmt.atom (.copy (.n 26) (.n 14)) ∈ ccdTail := by simp [ccdTail]
  obtain ⟨c', hchk⟩ := Option.isSome_iff_exists.mp b12
  let args : List E := [entries, region, base, limit, gen ^ 0]
  have hidx : ∀ v, σ v = σ (.n v.idx) := fun v => rfl
  obtain ⟨-, -, hgs⟩ := ev_spec rd (fun _ => 0) ccZEval args hchk
  rw [show args.length = 5 from rfl, List.isEmpty_iff.mp b13] at hgs
  have hg : ∀ a ∈ atomsIn ccZEval, Good rd [] (fun _ => 0) σ a := fun a ha =>
    hgs _ (cl_atom_mem ha)
  have hns : ∀ a ∈ atomsIn ccZEval, needsSide a = false := by
    intro a ha
    have := List.all_eq_true.mp b15 a ha
    simpa using this
  have hat : ∀ a ∈ atomsIn ccZEval, a.Holds rd σ :=
    atoms_holds hidx b14 hg (A := []) (by simp) fun a ha hn => absurd hn (by simp [hns a ha])
  have mH : ∀ s ∈ ccdHead, s ∈ ccZEval := fun s hs => by unfold ccZEval; simp [hs]
  have mZ : ∀ s ∈ cc25Zero, s ∈ ccZEval := fun s hs => by unfold ccZEval; simp [hs]
  have mT : ∀ s ∈ ccdTail, s ∈ ccZEval := fun s hs => by unfold ccZEval; simp [hs]
  have hatZ : ∀ a ∈ atomsIn cc25Zero, a.Holds rd σ := fun a ha =>
    hat a (cl_mem_atoms (mZ _ (cl_atom_mem ha)))
  have par : ∀ i (hi : i < 5), σ (.n i) = args.getD i 0 := fun i hi =>
    ev_params rd _ (l := args) hchk (by simp [args]; omega)
  have v5 : σ (.n 5) = word 1 0 := hat _ (cl_mem_atoms (mH _ c5))
  have v6 : σ (.n 6) = σ (.n 4) + σ (.n 5) := hat _ (cl_mem_atoms (mH _ a6))
  have v36 : σ (.n 25) = σ (.n 13) := hat _ (cl_mem_atoms (mT _ t36))
  have v37 : σ (.n 26) = σ (.n 14) := hat _ (cl_mem_atoms (mT _ t37))
  have v6' : σ (.n 6) = gen ^ 0 + gen ^ 0 := by
    rw [v6, v5, par 4 (by omega), word_one, pow_zero]; rfl
  have h60 : σ (.n 6) = 0 := by rw [v6']; exact e_add_eq_zero_iff.mpr rfl
  obtain ⟨hd, -⟩ := chain_final hzc rfl hatZ (pre := []) (n := 0) rfl
    (fun c => (cellsOfState_zero false c).symm)
  rw [hz13, hz14, show List.take (cc25ZSpec.len / 16) (cc25ZSpec.vals σ) = [] by
    simp [cc25ZSpec], List.nil_append] at hd
  refine ⟨hat, ?_, h60, v6', ?_⟩
  · rw [par 0 (by omega), par 1 (by omega), par 2 (by omega), par 3 (by omega), par 4 (by omega)]
    rfl
  · rw [v36, v37, digestCells, ← hd]

/-! ## The honest shape -/

/-- `child_claim_list_digest`'s words that end its callees' loops (`n = 136a + 17b + c`): the count
at `v4`; when `n ≠ 0`, `list_split`'s returns `g^a`, `g^b`, `g^c` at `v26`, `v27`, `v28`, the hint
`child_mono = 0` at `v29` (the walk by hinted indices). -/
def ccQ (n : ℕ) (σ : Val) : Prop :=
  σ (.n 4) = gen ^ n ∧ (n ≠ 0 → σ (.n 15) = gen ^ (n / 136) ∧ σ (.n 16) = gen ^ (n % 136 / 17) ∧
    σ (.n 17) = gen ^ (n % 17) ∧ σ (.n 18) = 0)

/-- `child_claim_list_digest`'s calls: none for the empty list; `list_split`,
`child_claim_list_any`. -/
def ccCalls (n : ℕ) (_ : Val) : List Call :=
  if n = 0 then [] else
    [⟨"list_split", [.n 4], [.n 15, .n 16, .n 17], true⟩,
      ⟨"child_claim_list_any", [.n 0, .n 1, .n 2, .n 3, .n 15, .n 16, .n 17], [.n 23, .n 24], true⟩]

/-- No `HeapBuf` of its own: `child_claim_list_any` places the chain buffer. -/
def ccBufs (_ : ℕ) (_ : Val) : List ℕ := []

/-- `child_claim_list_any`'s tree of honest shape. -/
def ccTs (n : ℕ) : List (Tree → Prop) := [fun _ => True, anyHonest n]

/-! ## The nonempty list -/

/-- The nonempty list's valuation, written out (the hint `child_mono = 0`). -/
noncomputable def ccEσ (eP rg L n : ℕ) (base : E) (D : Digest) : Val :=
  B1.Val.ofArgs [gen ^ eP, gen ^ rg, base, gen ^ L, gen ^ n, word 1 0, gen ^ n + word 1 0,
    0, 0, 0, 0, 0, 0, (digestHalves D).1, (digestHalves D).2,
    gen ^ (n / 136), gen ^ (n % 136 / 17), gen ^ (n % 17), 0, word 2 0, 0 + word 2 0, 0, 0,
    (digestHalves D).1, (digestHalves D).2, (digestHalves D).1, (digestHalves D).2]

/-- `child_claim_list_digest`'s callees on a nonempty list. -/
def ccKids (Lin : Main.Layout) (eP rg L n : ℕ) (base : E) (D : Digest) : List Kid :=
  [⟨"list_split", true, [gen ^ n], [], Returns [gen ^ (n / 136), gen ^ (n % 136 / 17), gen ^ (n % 17)]⟩,
    ⟨"child_claim_list_any", true, [gen ^ eP, gen ^ rg, base, gen ^ L, gen ^ (n / 136),
      gen ^ (n % 136 / 17), gen ^ (n % 17)], Lin, Returns (digestCells D)⟩]

/-- **Callees complete at their running offsets from `b`**, their words satisfying `P`
(`kidsFromInT_of_kidsDT`'s conclusion). -/
def KidsAt (fs : String → ℕ) (cert : String → V → ℕ) (κ : ℕ) (ks : List Kid)
    (Ts : List (Tree → Prop)) (P : ℕ → Prop) (b : ℕ) : Prop :=
  ∃ (N : ℕ) (L : Main.Layout) (outs : List (List E × Main.Layout)), P N ∧ OutsOk ks outs ∧
    Within L b N ∧ DisjL L ∧ OutsIn ks outs L ∧
    ∀ (rd : Reader) (σ : Val) (cs : List Call) (R Dacc : ℕ → Prop), CallsMatch σ cs ks outs →
      LowDef κ rd → MemL rd L → MemL rd (Kid.lins ks) → RegionsOk R Dacc ks outs →
      KidsFromInT coreProgram fs cert rd σ R Dacc cs Ts b N (fun i => Dacc i ∨ outRegion ks outs i)

theorem kidsAt_of_kidsDT {fs : String → ℕ} {cert : String → V → ℕ} {κ : ℕ} {ks : List Kid}
    {Ts : List (Tree → Prop)} (h : KidsDT fs cert κ ks Ts) (b : ℕ) :
    KidsAt fs cert κ ks Ts (fun _ => True) b :=
  let ⟨N, L, outs, ho, hW, hD, hI, hK⟩ := kidsFromInT_of_kidsDT κ ks Ts h b
  ⟨N, L, outs, trivial, ho, hW, hD, hI, hK⟩

/-- `list_split`, complete, placed, below any `2^κ` past `2^16`. -/
theorem list_split_completeAtK (fs : String → ℕ) (cert : String → V → ℕ) {κ a b c : ℕ}
    (hκ : 16 ≤ κ) (ha : a < maxKeys) (hb : b < bigGroups) (hc : c < claimGroup) :
    CompleteAtD fs cert κ "list_split" [] [gen ^ (claimBig * a + claimGroup * b + c)]
      (Returns [gen ^ a, gen ^ b, gen ^ c]) :=
  Lift.completeAtD_of_relIn list_split_pure (List.mem_singleton_self _) fun rd hl _ =>
    Lift.relIn_of_leaf find_list_split list_split_leafOk
      (fun σ es vs _ hw A hA => by
        have hall : (Out.ret es vs).All (Lift.EvLeafOk noLoad) := by
          have := Lift.walk_leafOk (σ := σ) Data.core22.body list_split_leafOk
          exact (show walk σ Data.core22.body = .ret es vs from hw) ▸ this
        rw [loads_none hall] at hA
        exact absurd hA List.not_mem_nil)
      (list_split_complete' rd (hl.mono hκ) _ _ ⟨a, ha, b, hb, c, hc, rfl, rfl⟩)

theorem list_split_n (fs : String → ℕ) (cert : String → V → ℕ) {κ n : ℕ} (hκ : 16 ≤ κ)
    (hn : n < claimBig * maxKeys) :
    CompleteAtD fs cert κ "list_split" [] [gen ^ n]
      (Returns [gen ^ (n / 136), gen ^ (n % 136 / 17), gen ^ (n % 17)]) := by
  simp only [claimBig, maxKeys] at hn
  have := list_split_completeAtK fs cert (a := n / 136) (b := n % 136 / 17) (c := n % 17) hκ
    (by simp [maxKeys]; omega) (by simp [bigGroups]; omega) (by simp [claimGroup]; omega)
  rwa [show claimBig * (n / 136) + claimGroup * (n % 136 / 17) + n % 17 = n by
    simp [claimBig, claimGroup]; omega] at this

set_option maxRecDepth 20000 in
/-- **The nonempty list, placed**, given its callees complete at their running offsets. -/
theorem cc_nonempty (fs : String → ℕ) (cert : String → V → ℕ) {κ : ℕ} {Lin : Main.Layout}
    {eP rg L n : ℕ} {base : E} {D : Digest} (hn0 : n ≠ 0) (hn : n < claimBig * maxKeys)
    {P : ℕ → Prop} (fp : ℕ)
    (hK : KidsAt fs cert κ (ccKids Lin eP rg L n base D) (ccTs n) P
      (fp + fs "child_claim_list_digest")) :
    ∃ (N : ℕ) (Lown : Main.Layout) (rets : List E) (Lout : Main.Layout), P N ∧
      Returns (digestCells D) rets Lout ∧ Within (Lout ++ Lown) fp (fs "child_claim_list_digest" + N) ∧
      DisjL (Lout ++ Lown) ∧ ∀ rd, LowDef κ rd → MemL rd (Lout ++ Lown ++ Lin) →
        RelAtInT coreProgram fs cert rd (RegionL Lin) (RegionL Lout) fp
          (fs "child_claim_list_digest" + N) "child_claim_list_digest"
          [gen ^ eP, gen ^ rg, base, gen ^ L, gen ^ n] (digestCells D)
          (NodeHonest coreProgram "child_claim_list_digest" (ccQ n) (ccCalls n) (ccBufs n) (ccTs n)) := by
  simp only [claimBig, maxKeys] at hn
  obtain ⟨Nk, Lk, outs, hP, hoo, hW, hD, -, hKids⟩ := hK
  have hl0 : outs.length = 2 := hoo.length
  obtain ⟨o1, t1, rfl, hl1⟩ := exists_of_length_succ hl0
  obtain ⟨o2, t2, rfl, hl2⟩ := exists_of_length_succ hl1
  obtain rfl := List.eq_nil_of_length_eq_zero hl2
  obtain ⟨h1, h2, -⟩ := hoo
  refine ⟨Nk, Lk, _, [], hP, ⟨rfl, rfl⟩, ?_, by rw [List.nil_append]; exact hD, fun rd hlow hm => ?_⟩
  · rw [List.nil_append]; exact hW.mono (by omega) (by omega)
  simp only [List.nil_append] at hm
  obtain ⟨hLk, hLin'⟩ := memL_append.mp hm
  set σ := ccEσ eP rg L n base D with hσ
  have hgn : gen ^ n ≠ 1 := fun h => hn0 ((gen_pow_eq_one_iff (by omega)).mp h)
  have h6ne : σ (.n 6) ≠ 0 := by
    show gen ^ n + word 1 0 ≠ 0
    rw [word_one, Ne, e_add_eq_zero_iff]; exact hgn
  have h31ne : σ (.n 20) ≠ 0 := by
    show 0 + word 2 0 ≠ 0
    rw [zero_add, word_gen]; exact gen_ne_zero
  have hb : (if σ (.n 6) = 0 then walk σ cc25Zero else walk σ ccElse) =
      .fall (ccE4.flatMap (Main.slEvs σ) ++ .inK (.n 20) :: ccAnyArm.flatMap (Main.slEvs σ)) := by
    simp only [h6ne, ↓reduceIte]
    rw [ccElse, walk_pre_ite σ ccMonoArm ccAnyArm rfl rfl (.n 20) ccE4 rfl]
    simp only [h31ne, ↓reduceIte]
  have hw := walk_ite σ ccdTail rfl (.n 6) cc25Zero ccElse [.n 25, .n 26] _ hb ccdHead rfl
  rw [← ccd_body] at hw
  set es := ccdHead.flatMap (Main.slEvs σ) ++ .inK (.n 6) ::
    ((ccE4.flatMap (Main.slEvs σ) ++ .inK (.n 20) :: ccAnyArm.flatMap (Main.slEvs σ)) ++
      ccdTail.flatMap (Main.slEvs σ)) with hes
  have hev : ∀ e ∈ es, e.Holds rd σ := by
    intro e he
    simp only [hes, ccdHead, ccE4, ccAnyArm, ccdTail, List.flatMap_cons, List.flatMap_nil,
      Main.slEvs, List.cons_append, List.nil_append, List.append_nil, List.mem_cons,
      List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · show σ (.n 5) = word 1 0; rfl
    · show σ (.n 6) = σ (.n 4) + σ (.n 5); rfl
    · show IsInK (gen ^ n + word 1 0)
      rw [word_one, ← pow_zero gen]; exact gen_pow_add_isInK _ _
    · trivial
    · trivial
    · show σ (.n 19) = word 2 0; rfl
    · show σ (.n 20) = σ (.n 18) + σ (.n 19); rfl
    · show IsInK (0 + word 2 0)
      rw [zero_add, word_gen, ← pow_one gen]; exact gen_pow_isInK 1
    · trivial
    · show σ (.n 13) = σ (.n 23); rfl
    · show σ (.n 14) = σ (.n 24); rfl
    · show σ (.n 25) = σ (.n 13); rfl
    · show σ (.n 26) = σ (.n 14); rfl
  have hal : allocs σ es = [] := rfl
  have hcalls : calls es = ccCalls n σ := by
    simp only [ccCalls, hn0, ↓reduceIte]; rfl
  have h := relAtInWT_of_walk (P := coreProgram) (fs := fs) (cert := cert) (σ := σ) (rd := rd)
    (R := RegionL Lin) (D := RegionL []) (fp := fp) (N := Nk)
    (args := [gen ^ eP, gen ^ rg, base, gen ^ L, gen ^ n]) (rets := digestCells D)
    (Dk := fun i => (fun _ => False) i ∨ outRegion (ccKids Lin eP rg L n base D) [o1, o2] i)
    coreProgram_wf find_child_claim_list_digest (Or.inl ccd_loop) rfl hw rfl hev
    (by rw [hal]; rfl) (fun q hq => by simp [hes, addrs, Main.slEvs, ccdHead, ccE4, ccAnyArm,
      ccdTail, Ev.addr?] at hq)
    (ccTs n) ?_ ?_ (fun i hi => by obtain ⟨q, hq, -⟩ := hi; simp at hq)
  · have h' := relAtInT_nodeHonest (Q := ccQ n) (cs := ccCalls n) (bs := ccBufs n) h
      find_child_claim_list_digest hw ⟨rfl, fun _ => ⟨rfl, rfl, rfl, rfl⟩⟩ hcalls (by rw [hal]; rfl)
      (by simp [ccCalls, ccTs, hn0])
    rw [hal] at h'
    simpa using h'
  · rw [hcalls, hal]
    simp only [ccCalls, hn0, ↓reduceIte, List.sum_nil, Nat.add_zero]
    refine hKids rd σ _ _ _ ?_ hlow hLk ?_ (regionsOk_of fun k hk _ i hi => ?_)
    · refine ⟨rfl, rfl, fun _ => ⟨rfl, ?_⟩, rfl, rfl, fun _ => ⟨rfl, ?_⟩, trivial⟩
      · rw [(h1 rfl).1]; rfl
      · rw [(h2 rfl).1]; rfl
    · intro q hq
      simp only [Kid.lins, ccKids, List.flatMap_cons, List.flatMap_nil, List.append_nil,
        List.nil_append] at hq
      exact hLin' q hq
    · simp only [ccKids, List.mem_cons, List.not_mem_nil, or_false] at hk
      rcases hk with rfl | rfl
      · obtain ⟨q, hq, -⟩ := hi; simp at hq
      · exact Or.inl (Or.inl hi)
  · intro A hA
    simp [hes, loadAddrs, Main.slEvs, ccdHead, ccE4, ccAnyArm, ccdTail, Ev.loadAddr?] at hA

set_option maxRecDepth 20000 in
/-- **The empty list, placed**: a leaf within its frame. -/
theorem cc_empty (fs : String → ℕ) (cert : String → V → ℕ) {Lin : Main.Layout}
    {eP rg L : ℕ} {base : E} (fp : ℕ) (rd : Reader) :
    RelAtInT coreProgram fs cert rd (RegionL Lin) (RegionL []) fp (fs "child_claim_list_digest")
      "child_claim_list_digest" [gen ^ eP, gen ^ rg, base, gen ^ L, gen ^ 0]
      (digestCells (keccak256 (cellsBytes [])))
      (NodeHonest coreProgram "child_claim_list_digest" (ccQ 0) (ccCalls 0) (ccBufs 0) (ccTs 0)) := by
  have mH : ∀ s ∈ ccdHead, isAtomS s = true := by decide
  have mTl : ∀ s ∈ ccdTail, isAtomS s = true := by decide
  obtain ⟨hat, hpar, h60, h6, hret⟩ := ccz_core (rd := rd) (gen ^ eP) (gen ^ rg) base (gen ^ L)
  set σ := cczσ rd [gen ^ eP, gen ^ rg, base, gen ^ L, gen ^ 0] with hσ
  obtain ⟨z1, z2, z3, z4, z5⟩ := cc25Zero_parts
  have hb : (if σ (.n 6) = 0 then walk σ cc25Zero else walk σ ccElse) =
      .fall (cc25Zero.flatMap (Main.slEvs σ)) := by
    simp only [h60, ↓reduceIte]; exact walk_straight_fall σ _ cc25Zero_straight
  have hw := walk_ite σ ccdTail rfl (.n 6) cc25Zero ccElse [.n 25, .n 26] _ hb ccdHead rfl
  rw [← ccd_body] at hw
  set es := ccdHead.flatMap (Main.slEvs σ) ++ .inK (.n 6) ::
    (cc25Zero.flatMap (Main.slEvs σ) ++ ccdTail.flatMap (Main.slEvs σ)) with hes
  have hmZ : ∀ s ∈ ccdHead ++ cc25Zero ++ ccdTail, ∀ a, s = .atom a → a.Holds rd σ := by
    intro s hs a rfl
    refine hat a (cl_mem_atoms ?_)
    unfold ccZEval
    simp only [List.mem_append] at hs ⊢
    rcases hs with (hs | hs) | hs
    · exact Or.inl (Or.inl (Or.inl hs))
    · exact Or.inl (Or.inl (Or.inr hs))
    · exact Or.inr hs
  have hev : ∀ e ∈ es, e.Holds rd σ := by
    intro e he
    rcases List.mem_append.mp he with he | he
    · exact slEvs_holds (fun s hs => slOk_atomS (mH s hs) (hmZ s (by simp [hs]))) e he
    rcases List.mem_cons.mp he with rfl | he
    · show IsInK (σ (.n 6)); rw [h6]; exact gen_pow_add_isInK 0 0
    rcases List.mem_append.mp he with he | he
    · exact slEvs_holds (fun s hs => slOk_atomS (List.all_eq_true.mp z5 s hs)
        (hmZ s (by simp [hs]))) e he
    · exact slEvs_holds (fun s hs => slOk_atomS (mTl s hs) (hmZ s (by simp [hs]))) e he
  obtain ⟨hzd, hza, hzad, hzc⟩ := Main.straight_parts σ _ cc25Zero_straight
  have hal : allocs σ es = [] := by
    rw [hes, allocs_append, show allocs σ (.inK (.n 6) :: (cc25Zero.flatMap (Main.slEvs σ) ++
      ccdTail.flatMap (Main.slEvs σ))) = allocs σ (cc25Zero.flatMap (Main.slEvs σ) ++
      ccdTail.flatMap (Main.slEvs σ)) from rfl, allocs_append, hza, z1]
    rfl
  have hce : calls es = [] := by
    rw [hes, calls_append, show calls (.inK (.n 6) :: (cc25Zero.flatMap (Main.slEvs σ) ++
      ccdTail.flatMap (Main.slEvs σ))) = calls (cc25Zero.flatMap (Main.slEvs σ) ++
      ccdTail.flatMap (Main.slEvs σ)) from rfl, calls_append, hzc, z3]
    rfl
  have h := relAtInWT_of_walk (P := coreProgram) (fs := fs) (cert := cert) (σ := σ) (rd := rd)
    (R := RegionL Lin) (D := RegionL []) (Dk := fun _ => False) (N := 0) (fp := fp)
    (args := [gen ^ eP, gen ^ rg, base, gen ^ L, gen ^ 0])
    (rets := digestCells (keccak256 (cellsBytes [])))
    coreProgram_wf find_child_claim_list_digest (Or.inl ccd_loop) (by rw [ccd_param]; exact hpar)
    hw hret hev
    (by
      rw [hal, hes, allocDsts_append, show allocDsts (.inK (.n 6) :: (cc25Zero.flatMap
        (Main.slEvs σ) ++ ccdTail.flatMap (Main.slEvs σ))) = allocDsts (cc25Zero.flatMap
        (Main.slEvs σ) ++ ccdTail.flatMap (Main.slEvs σ)) from rfl, allocDsts_append, hzd, z1]
      rfl)
    (fun q hq => by
      rw [hes, addrs_append, show addrs (.inK (.n 6) :: (cc25Zero.flatMap (Main.slEvs σ) ++
        ccdTail.flatMap (Main.slEvs σ))) = addrs (cc25Zero.flatMap (Main.slEvs σ) ++
        ccdTail.flatMap (Main.slEvs σ)) from rfl, addrs_append, hzad, z2] at hq
      simp [ccdHead, ccdTail, addrs, Main.slEvs, Ev.addr?] at hq)
    (ccTs 0)
    (by rw [hce]; exact ⟨rfl, fun _ h => h⟩)
    (fun A hA => by
      rw [hes, loadAddrs_append, show loadAddrs σ (.inK (.n 6) :: (cc25Zero.flatMap
        (Main.slEvs σ) ++ ccdTail.flatMap (Main.slEvs σ))) = loadAddrs σ (cc25Zero.flatMap
        (Main.slEvs σ) ++ ccdTail.flatMap (Main.slEvs σ)) from rfl, loadAddrs_append,
        B1.loadAddrs_straight σ _ rfl, B1.loadAddrs_straight σ _ cc25Zero_straight,
        B1.loadAddrs_straight σ _ rfl, z4] at hA
      simp [ccdHead, ccdTail, B1.Stmt.loadS] at hA)
    (fun i hi => by obtain ⟨q, hq, -⟩ := hi; simp at hq)
  have e4 : σ (.n 4) = gen ^ 0 := by
    simp only [List.cons.injEq] at hpar; exact hpar.2.2.2.2.1
  have h' := relAtInT_nodeHonest (Q := ccQ 0) (cs := ccCalls 0) (bs := ccBufs 0) h
    find_child_claim_list_digest hw ⟨e4, fun h0 => absurd rfl h0⟩ (by rw [hce]; rfl)
    (by rw [hal]; rfl) (by simp [ccCalls, ccTs])
  rw [hal] at h'
  simpa using h'

/-- **`child_claim_list_digest` is complete, placed, by a tree of honest shape**: `n < 136 · 2^16`
honest records among the caller's words (marks `base · g^j` at `g^(rg + o j)`, cells at
`g^(eP + 4 o j)`, slots below `L ≤ 2^κ`); it returns their cells' digest. -/
theorem child_claim_list_digest_completeAtT (fs : String → ℕ) (cert : String → V → ℕ) {κ : ℕ}
    (hκ : 16 ≤ κ) {Lin : Main.Layout} {eP rg L n : ℕ} {base : E} {o : ℕ → ℕ} {cells : List E}
    (hn : n < claimBig * maxKeys) (hl : cells.length = 4 * n) (hc : AllCanonical cells)
    (hL33 : L < 2 ^ 33) (hLκ : L ≤ 2 ^ κ)
    (hrec : ∀ rd, MemL rd Lin → RecMem rd (gen ^ rg) (gen ^ L) (gen ^ eP) base n o cells)
    (hR2 : ∀ j < n, RegionL Lin (rg + o j))
    (hR3 : ∀ j < n, ∀ c < 4, RegionL Lin (eP + 4 * o j + c)) :
    CompleteAtDT fs cert κ "child_claim_list_digest" Lin [gen ^ eP, gen ^ rg, base, gen ^ L, gen ^ n]
      (Returns (digestCells (keccak256 (cellsBytes cells))))
      (NodeHonest coreProgram "child_claim_list_digest" (ccQ n) (ccCalls n) (ccBufs n) (ccTs n)) := by
  intro fp
  rcases Nat.eq_zero_or_pos n with rfl | hn0
  · have hcl : cells = [] := List.eq_nil_of_length_eq_zero (by simpa using hl)
    subst hcl
    exact ⟨fs "child_claim_list_digest", [], _, [], ⟨rfl, rfl⟩, fun q hq => by simp at hq,
      B1.disj_nil, fun rd _ _ => cc_empty fs cert fp rd⟩
  have hok : KidsDT fs cert κ (ccKids Lin eP rg L n base (keccak256 (cellsBytes cells))) (ccTs n) :=
    ⟨fun _ => (list_split_n fs cert hκ hn).toT,
      fun _ => child_claim_list_any_completeAtT fs cert hn hl hc hL33 hLκ hrec hR2 hR3, trivial⟩
  obtain ⟨N, Lown, rets, Lout, -, ⟨rfl, rfl⟩, hW, hD, hr⟩ :=
    cc_nonempty fs cert (by omega) hn fp (kidsAt_of_kidsDT hok _)
  exact ⟨_, Lown, _, [], ⟨rfl, rfl⟩, hW, hD, hr⟩

/-- **`child_claim_list_digest` is complete, placed.** -/
theorem child_claim_list_digest_completeAt (fs : String → ℕ) (cert : String → V → ℕ) {κ : ℕ}
    (hκ : 16 ≤ κ) {Lin : Main.Layout} {eP rg L n : ℕ} {base : E} {o : ℕ → ℕ} {cells : List E}
    (hn : n < claimBig * maxKeys) (hl : cells.length = 4 * n) (hc : AllCanonical cells)
    (hL33 : L < 2 ^ 33) (hLκ : L ≤ 2 ^ κ)
    (hrec : ∀ rd, MemL rd Lin → RecMem rd (gen ^ rg) (gen ^ L) (gen ^ eP) base n o cells)
    (hR2 : ∀ j < n, RegionL Lin (rg + o j))
    (hR3 : ∀ j < n, ∀ c < 4, RegionL Lin (eP + 4 * o j + c)) :
    CompleteAtD fs cert κ "child_claim_list_digest" Lin [gen ^ eP, gen ^ rg, base, gen ^ L, gen ^ n]
      (Returns (digestCells (keccak256 (cellsBytes cells)))) :=
  (child_claim_list_digest_completeAtT fs cert hκ hn hl hc hL33 hLκ hrec hR2 hR3).toD

end
end LeanVM.Guest.B1.Digest
