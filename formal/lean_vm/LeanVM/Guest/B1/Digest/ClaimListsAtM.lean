/-
  LeanVM.Guest.B1.Digest.ClaimListsAtM

  `child_claim_list_digest` by a tree of honest shape on either walk, within bounds before the
  memory: the hint `child_mono = g` takes the gap walk `child_claim_list_mono`, any other hint `h`
  with `h + g` nonzero in `K` the walk by hinted indices `child_claim_list_any` (the honest prover
  hints `count 0 = 1` there).
-/

module

public import LeanVM.Guest.B1.Digest.ClaimListsAtTB
public import LeanVM.Guest.B1.Digest.MonoAt

/-!
# A child's claim list, on either walk

`ccQH n h`: `ccQ n` with the hint `h` at `v29`. `ccCallsM mono n`, `ccTsM mono n`: `list_split`,
then `child_claim_list_mono` (by `monoHonest n`) or `child_claim_list_any` (by `anyHonest n`).
`cc_nonemptyM`: the nonempty list placed on either arm (`cc_nonempty` at the hint `0`).
`ccBM fs SB mono n`: the words, `monoB` or `anyB` after `list_split`.
`child_claim_list_digest_completeAtTB_any`: on the walk by hinted indices at a hint `h`;
`child_claim_list_digest_completeAtTB_mono`: on the gap walk, the claims at strictly increasing
slots, every mark `base`.
-/

namespace LeanVM.Guest.B1.Digest

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Value.Keccak
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Guest.Memory LeanVM.Guest.B1.Fwd
open LeanVM.Guest.B1 (CompleteAtD CompleteAtDT CompleteAtDTB KidsDTB kidsFromInT_of_kidsDTB
  kidsBoundL Returns Kid DisjL Within regionsOk_of LowDef)
open LeanVM.Guest.B1.Main (Layout MemL RegionL memL_append)
open LeanVM.Guest.B1.Da (exists_of_length_succ)
open LeanVM.Guest.Budget (NodeHonest)

@[expose] public section

/-! ## The honest shape -/

/-- `ccQ n` with the hint `child_mono = h`. -/
def ccQH (n : ℕ) (h : E) (σ : Val) : Prop :=
  σ (.n 4) = gen ^ n ∧ (n ≠ 0 → σ (.n 15) = gen ^ (n / 136) ∧ σ (.n 16) = gen ^ (n % 136 / 17) ∧
    σ (.n 17) = gen ^ (n % 17) ∧ σ (.n 18) = h)

/-- The walk's call: `child_claim_list_mono` or `child_claim_list_any`. -/
def ccWalkCall (mono : Bool) : Call :=
  if mono then ⟨"child_claim_list_mono", [.n 0, .n 1, .n 2, .n 3, .n 15, .n 16, .n 17],
      [.n 21, .n 22], true⟩
  else ⟨"child_claim_list_any", [.n 0, .n 1, .n 2, .n 3, .n 15, .n 16, .n 17], [.n 23, .n 24], true⟩

/-- `child_claim_list_digest`'s calls on either walk. -/
def ccCallsM (mono : Bool) (n : ℕ) (_ : Val) : List Call :=
  if n = 0 then [] else [⟨"list_split", [.n 4], [.n 15, .n 16, .n 17], true⟩, ccWalkCall mono]

/-- The walk's tree of honest shape. -/
def ccTsM (mono : Bool) (n : ℕ) : List (Tree → Prop) :=
  [fun _ => True, if mono then monoHonest n else anyHonest n]

/-- **`child_claim_list_digest`'s honest shape** on `n` claims, the walk `mono`, the hint `h`. -/
def ccHonestH (n : ℕ) (mono : Bool) (h : E) : Tree → Prop :=
  NodeHonest coreProgram "child_claim_list_digest" (ccQH n h) (ccCallsM mono n) (ccBufs n)
    (ccTsM mono n)

theorem ccQ_eq (n : ℕ) : ccQ n = ccQH n 0 := rfl

theorem ccCalls_eq (n : ℕ) : ccCalls n = ccCallsM false n := by
  funext σ; simp [ccCalls, ccCallsM, ccWalkCall]

theorem ccTs_eq (n : ℕ) : ccTs n = ccTsM false n := by simp [ccTs, ccTsM]

/-- `child_claim_list_digest`'s honest shape at the hint `0` is `ccHonestH` on the walk by hinted
indices. -/
theorem nodeHonest_cc_eq (n : ℕ) :
    NodeHonest coreProgram "child_claim_list_digest" (ccQ n) (ccCalls n) (ccBufs n) (ccTs n) =
      ccHonestH n false 0 := by
  rw [ccHonestH, ccQ_eq, ccCalls_eq, ccTs_eq]

/-! ## The nonempty list -/

/-- The nonempty list's valuation at the hint `h`. -/
noncomputable def ccEσH (eP rg L n : ℕ) (base : E) (D : Digest) (h : E) : Val :=
  B1.Val.ofArgs [gen ^ eP, gen ^ rg, base, gen ^ L, gen ^ n, word 1 0, gen ^ n + word 1 0,
    0, 0, 0, 0, 0, 0, (digestHalves D).1, (digestHalves D).2,
    gen ^ (n / 136), gen ^ (n % 136 / 17), gen ^ (n % 17), h, word 2 0, h + word 2 0,
    (digestHalves D).1, (digestHalves D).2,
    (digestHalves D).1, (digestHalves D).2, (digestHalves D).1, (digestHalves D).2]

/-- `child_claim_list_digest`'s callees on a nonempty list, on either walk. -/
def ccKidsM (Lin : Main.Layout) (eP rg L n : ℕ) (base : E) (D : Digest) (mono : Bool) :
    List Kid :=
  [⟨"list_split", true, [gen ^ n], [], Returns [gen ^ (n / 136), gen ^ (n % 136 / 17), gen ^ (n % 17)]⟩,
    ⟨if mono then "child_claim_list_mono" else "child_claim_list_any", true, [gen ^ eP, gen ^ rg,
      base, gen ^ L, gen ^ (n / 136), gen ^ (n % 136 / 17), gen ^ (n % 17)], Lin,
      Returns (digestCells D)⟩]

/-- The arm a hint takes. -/
def ccArm (mono : Bool) : List Stmt := if mono then ccMonoArm else ccAnyArm

set_option maxRecDepth 20000 in
/-- **The nonempty list, placed, on either walk**, given its callees complete at their running
offsets: the hint `g` takes the gap walk, a hint `h` with `h + g` nonzero in `K` the other. -/
theorem cc_nonemptyM (fs : String → ℕ) (cert : String → V → ℕ) {κ : ℕ} {Lin : Main.Layout}
    {eP rg L n : ℕ} {base : E} {D : Digest} (hn0 : n ≠ 0) (hn : n < claimBig * bigFramesCap)
    {mono : Bool} {h : E} (hm : mono = true → h = gen)
    (ha : mono = false → h + word 2 0 ≠ 0 ∧ IsInK (h + word 2 0))
    {P : ℕ → Prop} (fp : ℕ)
    (hK : KidsAt fs cert κ (ccKidsM Lin eP rg L n base D mono) (ccTsM mono n) P
      (fp + fs "child_claim_list_digest")) :
    ∃ (N : ℕ) (Lown : Main.Layout) (rets : List E) (Lout : Main.Layout), P N ∧
      Returns (digestCells D) rets Lout ∧ Within (Lout ++ Lown) fp (fs "child_claim_list_digest" + N) ∧
      DisjL (Lout ++ Lown) ∧ ∀ rd, LowDef κ rd → MemL rd (Lout ++ Lown ++ Lin) →
        RelAtInT coreProgram fs cert rd (RegionL Lin) (RegionL Lout) fp
          (fs "child_claim_list_digest" + N) "child_claim_list_digest"
          [gen ^ eP, gen ^ rg, base, gen ^ L, gen ^ n] (digestCells D) (ccHonestH n mono h) := by
  simp only [claimBig, bigFramesCap] at hn
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
  set σ := ccEσH eP rg L n base D h with hσ
  have hgn : gen ^ n ≠ 1 := fun h => hn0 ((gen_pow_eq_one_iff (by omega)).mp h)
  have h6ne : σ (.n 6) ≠ 0 := by
    show gen ^ n + word 1 0 ≠ 0
    rw [word_one, Ne, e_add_eq_zero_iff]; exact hgn
  have h20 : σ (.n 20) = h + word 2 0 := rfl
  have hb : (if σ (.n 6) = 0 then walk σ cc25Zero else walk σ ccElse) =
      .fall (ccE4.flatMap (Main.slEvs σ) ++ .inK (.n 20) :: (ccArm mono).flatMap (Main.slEvs σ)) := by
    simp only [h6ne, ↓reduceIte]
    rw [ccElse, walk_pre_ite σ ccMonoArm ccAnyArm rfl rfl (.n 20) ccE4 rfl]
    cases mono
    · simp only [(ha rfl).1, h20, ↓reduceIte, ccArm, Bool.false_eq_true]
    · have : σ (.n 20) = 0 := by
        rw [h20, hm rfl, word_gen]; exact e_add_eq_zero_iff.mpr rfl
      simp only [this, ↓reduceIte, ccArm]
  have hw := walk_ite σ ccdTail rfl (.n 6) cc25Zero ccElse [.n 25, .n 26] _ hb ccdHead rfl
  rw [← ccd_body] at hw
  set es := ccdHead.flatMap (Main.slEvs σ) ++ .inK (.n 6) ::
    ((ccE4.flatMap (Main.slEvs σ) ++ .inK (.n 20) :: (ccArm mono).flatMap (Main.slEvs σ)) ++
      ccdTail.flatMap (Main.slEvs σ)) with hes
  have hev : ∀ e ∈ es, e.Holds rd σ := by
    intro e he
    cases mono <;>
    simp only [hes, ccdHead, ccE4, ccArm, ccAnyArm, ccMonoArm, ccdTail, List.flatMap_cons,
      List.flatMap_nil, Main.slEvs, List.cons_append, List.nil_append, List.append_nil,
      List.mem_cons, List.not_mem_nil, or_false, Bool.false_eq_true, ↓reduceIte] at he <;>
    rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals first
      | trivial
      | (show IsInK (gen ^ n + word 1 0)
         rw [word_one, ← pow_zero gen]; exact gen_pow_add_isInK _ _)
      | (show IsInK (h + word 2 0); exact (ha rfl).2)
      | (show IsInK (h + word 2 0)
         rw [hm rfl, word_gen, e_add_eq_zero_iff.mpr rfl]; simpa using ofK_isInK 0)
  have hal : allocs σ es = [] := by cases mono <;> rfl
  have hcalls : calls es = ccCallsM mono n σ := by
    cases mono <;> (simp only [ccCallsM, hn0, ↓reduceIte]; rfl)
  have h' := relAtInWT_of_walk (P := coreProgram) (fs := fs) (cert := cert) (σ := σ) (rd := rd)
    (R := RegionL Lin) (D := RegionL []) (fp := fp) (N := Nk)
    (args := [gen ^ eP, gen ^ rg, base, gen ^ L, gen ^ n]) (rets := digestCells D)
    (Dk := fun i => (fun _ => False) i ∨ outRegion (ccKidsM Lin eP rg L n base D mono) [o1, o2] i)
    coreProgram_wf find_child_claim_list_digest (Or.inl ccd_loop) rfl hw rfl hev
    (by rw [hal]; cases mono <;> rfl) (fun q hq => by
      cases mono <;> simp [hes, addrs, Main.slEvs, ccdHead, ccE4, ccArm, ccAnyArm, ccMonoArm,
        ccdTail, Ev.addr?] at hq)
    (ccTsM mono n) ?_ ?_ (fun i hi => by obtain ⟨q, hq, -⟩ := hi; simp at hq)
  · have h'' := relAtInT_nodeHonest (Q := ccQH n h) (cs := ccCallsM mono n) (bs := ccBufs n) h'
      find_child_claim_list_digest hw ⟨rfl, fun _ => ⟨rfl, rfl, rfl, rfl⟩⟩ hcalls (by rw [hal]; rfl)
      (by simp [ccCallsM, ccTsM, hn0])
    rw [hal] at h''
    unfold ccHonestH
    simpa using h''
  · rw [hcalls, hal]
    simp only [ccCallsM, hn0, ↓reduceIte, List.sum_nil, Nat.add_zero]
    refine hKids rd σ _ _ _ ?_ hlow hLk ?_ (regionsOk_of fun k hk _ i hi => ?_)
    · cases mono
      · refine ⟨rfl, rfl, fun _ => ⟨rfl, ?_⟩, rfl, rfl, fun _ => ⟨rfl, ?_⟩, trivial⟩
        · rw [(h1 rfl).1]; rfl
        · rw [(h2 rfl).1]; rfl
      · refine ⟨rfl, rfl, fun _ => ⟨rfl, ?_⟩, rfl, rfl, fun _ => ⟨rfl, ?_⟩, trivial⟩
        · rw [(h1 rfl).1]; rfl
        · rw [(h2 rfl).1]; rfl
    · intro q hq
      simp only [Kid.lins, ccKidsM, List.flatMap_cons, List.flatMap_nil, List.append_nil,
        List.nil_append] at hq
      exact hLin' q hq
    · simp only [ccKidsM, List.mem_cons, List.not_mem_nil, or_false] at hk
      rcases hk with rfl | rfl
      · obtain ⟨q, hq, -⟩ := hi; simp at hq
      · exact Or.inl (Or.inl hi)
  · intro A hA
    cases mono <;> simp [hes, loadAddrs, Main.slEvs, ccdHead, ccE4, ccArm, ccAnyArm, ccMonoArm,
      ccdTail, Ev.loadAddr?] at hA

/-! ## Within bounds -/

/-- **`child_claim_list_digest`'s words** on `n` claims, on the walk `mono`. -/
def ccBM (fs : String → ℕ) (SB : String → ℕ) (mono : Bool) (n : ℕ) : ℕ :=
  if n = 0 then fs "child_claim_list_digest" else
    fs "child_claim_list_digest" + (SB "list_split" + ((if mono then monoB fs n else anyB fs n) + 0))

theorem ccB_eq (fs : String → ℕ) (SB : String → ℕ) (n : ℕ) : ccB fs SB n = ccBM fs SB false n := by
  simp [ccB, ccBM]

/-- The empty list on any hint: the shape at `0` claims names no hint and no callee. -/
theorem ccHonestH_zero {mono : Bool} {h : E} {t : Tree} (ht : ccHonestH 0 false 0 t) :
    ccHonestH 0 mono h t := by
  obtain ⟨σ, ks, rfl, hQ, hc, -, -⟩ := ht
  have e : ∀ m, ccCallsM m 0 σ = [] := fun m => by simp [ccCallsM]
  refine ⟨σ, ks, rfl, ⟨hQ.1, fun h0 => absurd rfl h0⟩, fun fn es vs hf hw => ?_, ?_, ?_⟩
  · rw [hc fn es vs hf hw, e, e]
  · rw [e]; exact Nat.zero_le _
  · rw [e]; trivial

/-- **`child_claim_list_digest` on the walk by hinted indices, at the hint `h`.** -/
theorem child_claim_list_digest_completeAtTB_any (fs : String → ℕ) (cert : String → V → ℕ)
    {κ : ℕ} (hκ : 20 ≤ κ) {Lin : Main.Layout} {eP rg L n : ℕ} {base : E} {o : ℕ → ℕ}
    {cells : List E} {h : E} (hh : h + word 2 0 ≠ 0 ∧ IsInK (h + word 2 0))
    (hn : n < claimBig * bigFramesCap) (hl : cells.length = 4 * n)
    (hL33 : L < 2 ^ 33) (hLκ : L ≤ 2 ^ κ)
    (hrec : ∀ rd, MemL rd Lin → RecMem rd (gen ^ rg) (gen ^ L) (gen ^ eP) base n o cells)
    (hR2 : ∀ j < n, RegionL Lin (rg + o j))
    (hR3 : ∀ j < n, ∀ c < 4, RegionL Lin (eP + 4 * o j + c)) {SB : String → ℕ}
    (hLS : TotalLe coreProgram fs "list_split" (fun _ => SB "list_split")) :
    CompleteAtDTB fs cert κ "child_claim_list_digest" Lin
      [gen ^ eP, gen ^ rg, base, gen ^ L, gen ^ n]
      (Returns (digestCells (keccak256 (cellsBytes cells)))) (ccHonestH n false h)
      (ccBM fs SB false n) := by
  intro fp
  rcases Nat.eq_zero_or_pos n with rfl | hn0
  · have hcl : cells = [] := List.eq_nil_of_length_eq_zero (by simpa using hl)
    subst hcl
    refine ⟨fs "child_claim_list_digest", [], _, [], by simp [ccBM], ⟨rfl, rfl⟩,
      fun q hq => by simp at hq, B1.disj_nil, fun rd _ _ => ?_⟩
    exact (nodeHonest_cc_eq 0 ▸ cc_empty fs cert fp rd).mono fun _ ht => ccHonestH_zero ht
  have hok : KidsDTB fs cert κ (ccKidsM Lin eP rg L n base (keccak256 (cellsBytes cells)) false)
      (ccTsM false n) [SB "list_split", anyB fs n] :=
    ⟨fun _ => list_split_nB fs cert hκ hn hLS,
      fun _ => child_claim_list_any_completeAtTB fs cert hn hl hL33 hLκ hrec hR2 hR3, trivial⟩
  obtain ⟨N, Lown, rets, Lout, hN, ⟨rfl, rfl⟩, hW, hD, hr⟩ :=
    cc_nonemptyM fs cert (by omega) hn (mono := false) (h := h) (fun h => absurd h (by simp))
      (fun _ => hh) fp (kidsAt_of_kidsDTB hok _)
  refine ⟨_, Lown, _, [], ?_, ⟨rfl, rfl⟩, hW, hD, hr⟩
  simp only [kidsBoundL, ccKidsM, List.headD_cons, List.tail_cons, ↓reduceIte] at hN
  simp only [ccBM, show n ≠ 0 by omega, ↓reduceIte, Bool.false_eq_true]
  omega

/-- **`child_claim_list_digest` on the gap walk** (the hint `g`): `n < 136 · 2^20` honest claims
at strictly increasing slots `o j` below `L < 2^κ`, every mark `base`, among the caller's words. -/
theorem child_claim_list_digest_completeAtTB_mono (fs : String → ℕ) (cert : String → V → ℕ)
    {κ : ℕ} (hκ : 20 ≤ κ) {Lin : Main.Layout} {eP rg L n : ℕ} {base : E} {o : ℕ → ℕ}
    {cells : List E} (hn : n < claimBig * bigFramesCap) (hl : cells.length = 4 * n)
    (hLκ : L < 2 ^ κ) (hinc : ∀ j < n, mStart o j ≤ o j) (hend : mStart o n ≤ L)
    (hrec : ∀ rd, MemL rd Lin → MRec rd (gen ^ rg) L (gen ^ eP) base n o cells)
    (hR2 : ∀ j < n, RegionL Lin (rg + o j))
    (hR3 : ∀ j < n, ∀ c < 4, RegionL Lin (eP + 4 * o j + c)) {SB : String → ℕ}
    (hLS : TotalLe coreProgram fs "list_split" (fun _ => SB "list_split")) :
    CompleteAtDTB fs cert κ "child_claim_list_digest" Lin
      [gen ^ eP, gen ^ rg, base, gen ^ L, gen ^ n]
      (Returns (digestCells (keccak256 (cellsBytes cells)))) (ccHonestH n true gen)
      (ccBM fs SB true n) := by
  intro fp
  rcases Nat.eq_zero_or_pos n with rfl | hn0
  · have hcl : cells = [] := List.eq_nil_of_length_eq_zero (by simpa using hl)
    subst hcl
    refine ⟨fs "child_claim_list_digest", [], _, [], by simp [ccBM], ⟨rfl, rfl⟩,
      fun q hq => by simp at hq, B1.disj_nil, fun rd _ _ => ?_⟩
    exact (nodeHonest_cc_eq 0 ▸ cc_empty fs cert fp rd).mono fun _ ht => ccHonestH_zero ht
  have hok : KidsDTB fs cert κ (ccKidsM Lin eP rg L n base (keccak256 (cellsBytes cells)) true)
      (ccTsM true n) [SB "list_split", monoB fs n] :=
    ⟨fun _ => list_split_nB fs cert hκ hn hLS,
      fun _ => child_claim_list_mono_completeAtTB fs cert hn hl hLκ hinc hend hrec hR2 hR3, trivial⟩
  obtain ⟨N, Lown, rets, Lout, hN, ⟨rfl, rfl⟩, hW, hD, hr⟩ :=
    cc_nonemptyM fs cert (by omega) hn (mono := true) (h := gen) (fun _ => rfl)
      (fun h => absurd h (by simp)) fp (kidsAt_of_kidsDTB hok _)
  refine ⟨_, Lown, _, [], ?_, ⟨rfl, rfl⟩, hW, hD, hr⟩
  simp only [kidsBoundL, ccKidsM, List.headD_cons, List.tail_cons, ↓reduceIte] at hN
  simp only [ccBM, show n ≠ 0 by omega, ↓reduceIte]
  omega

end
end LeanVM.Guest.B1.Digest
