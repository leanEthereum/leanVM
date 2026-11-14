/-
  LeanVM.Guest.B1.Digest.ClaimListsAtMP

  `child_claim_list_digest` placed with its pops on either walk: the split, the hint `child_mono`, the walk's gaps or
  indices.
-/

module

public import LeanVM.Guest.B1.Digest.ClaimListsAtM
public import LeanVM.Guest.B1.Digest.ChildListAtNP
public import LeanVM.Guest.B1.Digest.ClaimListPops

/-!
# A child's claim list, placed with its pops

* `kidsT_impD`: callees' predicates weakened; `KidsAtR`, `kidsAtR_of_kidsDTBR`: `KidsAt` by predicates of the memory;
* `ccTsP`, `cc_nonemptyMP`: `cc_nonemptyM`, its callees' trees popping `ls` and `wp`, its tree popping `ls`, the hint,
  `wp`;
* `ccPopsW`: the list's entries; `child_claim_list_digest_completeAtTBP_any`, `_mono`: the two walks with their pops.
-/

namespace LeanVM.Guest.B1.Digest

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Value.Keccak
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Guest.Memory LeanVM.Guest.B1.Fwd
open LeanVM.Guest.B1 (CompleteAtD CompleteAtDT CompleteAtDTB CompleteAtDTBR KidsDTB KidsDTBR
  kidsFromInT_of_kidsDTB kidsFromInT_of_kidsDTBR kidsBoundL Returns Kid DisjL Within regionsOk_of LowDef OutsOk
  OutsIn CallsMatch RegionsOk outRegion)
open LeanVM.Guest.B1.Main (Layout MemL RegionL memL_append)
open LeanVM.Guest.B1.Da (exists_of_length_succ slEvs_holds)
open LeanVM.Guest.Budget (NodeHonest)

@[expose] public section

theorem kidsT_impD : ∀ {cs : List Call} {Ts Ts' : List (Tree → Prop)} {ks : List Tree},
    KidsT cs Ts ks → List.Forall₂ (fun T T' => ∀ t, T t → T' t) Ts Ts' → KidsT cs Ts' ks
  | _ :: _, _ :: _, _ :: _, _ :: _, ⟨h, hs⟩, .cons hT hTs => ⟨fun ht => hT _ (h ht), kidsT_impD hs hTs⟩
  | _ :: _, _ :: _, _ :: _, [], _, _ => trivial
  | [], _, _, _, _, _ => trivial
  | _ :: _, [], [], _, _, _ => trivial
  | _ :: _, _ :: _, [], _, _, h => nomatch h
  | _ :: _, [], _ :: _, _, _, h => nomatch h

/-- **`KidsAt` by predicates of the memory.** -/
def KidsAtR (fs : String → ℕ) (cert : String → V → ℕ) (κ : ℕ) (ks : List Kid)
    (Ts : Reader → List (Tree → Prop)) (P : ℕ → Prop) (b : ℕ) : Prop :=
  ∃ (N : ℕ) (L : Main.Layout) (outs : List (List E × Main.Layout)), P N ∧ OutsOk ks outs ∧
    Within L b N ∧ DisjL L ∧ OutsIn ks outs L ∧
    ∀ (rd : Reader) (σ : Val) (cs : List Call) (R Dacc : ℕ → Prop), CallsMatch σ cs ks outs →
      LowDef κ rd → MemL rd L → MemL rd (Kid.lins ks) → RegionsOk R Dacc ks outs →
      KidsFromInT coreProgram fs cert rd σ R Dacc cs (Ts rd) b N (fun i => Dacc i ∨ outRegion ks outs i)

theorem kidsAtR_of_kidsDTBR {fs : String → ℕ} {cert : String → V → ℕ} {κ : ℕ} {ks : List Kid}
    {Ts : Reader → List (Tree → Prop)} {Bs : List ℕ} (h : KidsDTBR fs cert κ ks Ts Bs) (b : ℕ) :
    KidsAtR fs cert κ ks Ts (· ≤ kidsBoundL fs ks Bs) b :=
  let ⟨N, L, outs, hN, ho, hW, hD, hI, hK⟩ := kidsFromInT_of_kidsDTBR κ ks Ts Bs h b
  ⟨N, L, outs, hN, ho, hW, hD, hI, hK⟩

/-- The callees' trees: `list_split`'s popping `ls`, the walk's of honest shape popping `wp`. -/
def ccTsP (mono : Bool) (n : ℕ) (rd : Reader) (ls wp : List Pop) : List (Tree → Prop) :=
  [fun t => t.pops coreProgram rd = ls,
    fun t => (if mono then monoHonest n else anyHonest n) t ∧ t.pops coreProgram rd = wp]

set_option maxRecDepth 20000 in
/-- **`cc_nonemptyM` with its pops**: its callees' trees popping `ls`, `wp` on each memory, its tree pops `ls`, the
hint, `wp`. -/
theorem cc_nonemptyMP (fs : String → ℕ) (cert : String → V → ℕ) {κ : ℕ} {Lin : Main.Layout}
    {eP rg L n : ℕ} {base : E} {D : Digest} (hn0 : n ≠ 0) (hn : n < claimBig * bigFramesCap)
    {mono : Bool} {h : E} (hm : mono = true → h = gen)
    (ha : mono = false → h + word 2 0 ≠ 0 ∧ IsInK (h + word 2 0))
    {P : ℕ → Prop} (fp : ℕ) {ls wp : List Pop}
    (hK : KidsAtR fs cert κ (ccKidsM Lin eP rg L n base D mono) (fun rd => ccTsP mono n rd ls wp) P
      (fp + fs "child_claim_list_digest")) :
    ∃ (N : ℕ) (Lown : Main.Layout) (rets : List E) (Lout : Main.Layout), P N ∧
      Returns (digestCells D) rets Lout ∧ Within (Lout ++ Lown) fp (fs "child_claim_list_digest" + N) ∧
      DisjL (Lout ++ Lown) ∧ ∀ rd, LowDef κ rd → MemL rd (Lout ++ Lown ++ Lin) →
        RelAtInT coreProgram fs cert rd (RegionL Lin) (RegionL Lout) fp
          (fs "child_claim_list_digest" + N) "child_claim_list_digest"
          [gen ^ eP, gen ^ rg, base, gen ^ L, gen ^ n] (digestCells D)
          (fun t => ccHonestH n mono h t ∧ t.pops coreProgram rd = ls ++ ("child_mono", [h]) :: wp) := by
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
    (ccTsP mono n rd ls wp) ?_ ?_ (fun i hi => by obtain ⟨q, hq, -⟩ := hi; simp at hq)
  · rw [hal] at h'
    simp only [List.sum_nil, Nat.add_zero] at h'
    obtain ⟨t, ht, ks, rfl, hKt⟩ := h'
    refine ⟨_, ht, ⟨σ, ks, rfl, ⟨rfl, fun _ => ⟨rfl, rfl, rfl, rfl⟩⟩,
      fun fn' es' vs' hf' hw' => ?_, by simp [ccCallsM, ccTsM, hn0], ?_⟩, ?_⟩
    · rw [find_child_claim_list_digest] at hf'
      cases hf'
      rw [hw] at hw'
      cases hw'
      exact hcalls
    · rw [← hcalls]
      refine kidsT_impD hKt ?_
      cases mono
      · exact .cons (fun _ _ => trivial) (.cons (fun _ h => h.1) .nil)
      · exact .cons (fun _ _ => trivial) (.cons (fun _ h => h.1) .nil)
    · obtain ⟨fn', hf', -, es', vs', hw', -, -, hkv⟩ := ht.2.1
      rw [find_child_claim_list_digest] at hf'
      cases hf'
      rw [hw] at hw'
      cases hw'
      rw [Tree.pops_node find_child_claim_list_digest hw,
        popsKids_of_kidsT (pss := [ls, wp]) hkv (kidsT_impD hKt (.cons (fun _ h => h)
          (.cons (fun _ h => h.2) .nil))) (by rw [hcalls]; cases mono <;> simp [ccCallsM, ccWalkCall, hn0, KidsPopsOk])]
      have h18 : σ (.n 18) = h := rfl
      cases mono <;>
      simp [hes, ccdHead, ccE4, ccArm, ccAnyArm, ccMonoArm, ccdTail, Main.slEvs, splice, Atom.pops, Hint.pops,
        Dest.words, h18]
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



/-- **A child's claim list's entries**: none for the empty list, else the split, the hint, the walk's `ws`. -/
noncomputable def ccPopsW (n : ℕ) (h : E) (ws : List Pop) : List Pop :=
  if n = 0 then [] else ("signers_split", [gen ^ (n / 136), gen ^ (n % 136 / 17), gen ^ (n % 17)]) ::
    ("child_mono", [h]) :: ws

/-- `list_split`'s entries on `g^n`. -/
noncomputable def lsPops (n : ℕ) : List Pop :=
  [("signers_split", [gen ^ (n / 136), gen ^ (n % 136 / 17), gen ^ (n % 17)])]

theorem cc_zero_popS : (ccdHead ++ (cc25Zero ++ ccdTail)).filterMap Main.Stmt.popS = [] := by decide +kernel

/-- **A tree predicate on the declared returns.** -/
theorem _root_.LeanVM.Guest.B1.CompleteAtDTBR.monoRet {fs : String → ℕ} {cert : String → V → ℕ} {k : ℕ}
    {f : String} {Lin : Main.Layout} {args R : List E} {B : ℕ} {T T' : Reader → Tree → Prop}
    (h : CompleteAtDTBR fs cert k f Lin args (Returns R) T B)
    (hT : ∀ rd t, t.name = f → t.Valid coreProgram rd args R → T rd t → T' rd t) :
    CompleteAtDTBR fs cert k f Lin args (Returns R) T' B := fun fp =>
  let ⟨n, Lown, rets, Lout, hn, ho, hw, hd, hr⟩ := h fp
  ⟨n, Lown, rets, Lout, hn, ho, hw, hd, fun rd hl hm =>
    let ⟨t, ht, hTt⟩ := hr rd hl hm
    ⟨t, ht, hT rd t ht.1 (ho.1 ▸ ht.2.1) hTt⟩⟩

/-- **`list_split` on `g^n` within its static bound, by a tree popping its split.** -/
theorem list_split_nBP (fs : String → ℕ) (cert : String → V → ℕ) {κ n : ℕ} (hκ : 20 ≤ κ)
    (hn : n < claimBig * bigFramesCap) {Bls : ℕ}
    (hT : TotalLe coreProgram fs "list_split" (fun _ => Bls)) :
    CompleteAtDTBR fs cert κ "list_split" [] [gen ^ n]
      (Returns [gen ^ (n / 136), gen ^ (n % 136 / 17), gen ^ (n % 17)])
      (fun rd t => t.pops coreProgram rd = lsPops n) Bls :=
  (list_split_nB fs cert hκ hn hT).toR.monoRet fun _ _ hn hv _ => list_split_pops hn hv

set_option maxRecDepth 20000 in
/-- **The empty list, placed**: a leaf within its frame. -/
theorem cc_emptyP (fs : String → ℕ) (cert : String → V → ℕ) {Lin : Main.Layout}
    {eP rg L : ℕ} {base : E} (fp : ℕ) (rd : Reader) :
    RelAtInT coreProgram fs cert rd (RegionL Lin) (RegionL []) fp (fs "child_claim_list_digest")
      "child_claim_list_digest" [gen ^ eP, gen ^ rg, base, gen ^ L, gen ^ 0]
      (digestCells (keccak256 (cellsBytes [])))
      (fun t => NodeHonest coreProgram "child_claim_list_digest" (ccQ 0) (ccCalls 0) (ccBufs 0) (ccTs 0) t ∧
        t.pops coreProgram rd = []) := by
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
  rw [hal] at h
  simp only [List.sum_nil, Nat.add_zero] at h
  obtain ⟨t, ht, ks, rfl, hK⟩ := h
  obtain ⟨fn', hf', -, es', vs', hw', -, -, hkv⟩ := ht.2.1
  rw [find_child_claim_list_digest] at hf'
  cases hf'
  rw [hw] at hw'
  cases hw'
  rw [hce] at hkv
  obtain rfl : ks = [] := by cases ks with | nil => rfl | cons _ _ => exact hkv.elim
  refine ⟨_, ht, ⟨σ, [], rfl, ⟨e4, fun h0 => absurd rfl h0⟩, fun fn' es' vs' hf' hw' => ?_,
    by simp [ccCalls, ccTs], by simp only [ccCalls, ↓reduceIte]; trivial⟩, ?_⟩
  · rw [find_child_claim_list_digest] at hf'
    cases hf'
    rw [hw] at hw'
    cases hw'
    rw [hce]; rfl
  · rw [Tree.pops_node find_child_claim_list_digest hw, hes, Main.splice_inK_mid,
      ← List.flatMap_append, ← List.flatMap_append, Main.splice_straight _ (by
        rw [List.all_append, List.all_append, cc25Zero_straight]; rfl), cc_zero_popS]
    rfl

/-- **`child_claim_list_digest` on the walk by hinted indices, at the hint `h`, with its pops.** -/
theorem child_claim_list_digest_completeAtTBP_any (fs : String → ℕ) (cert : String → V → ℕ)
    {κ : ℕ} (hκ : 20 ≤ κ) {Lin : Main.Layout} {eP rg L n : ℕ} {base : E} {o : ℕ → ℕ}
    {cells : List E} {h : E} (hh : h + word 2 0 ≠ 0 ∧ IsInK (h + word 2 0))
    (hn : n < claimBig * bigFramesCap) (hl : cells.length = 4 * n)
    (hL33 : L < 2 ^ 33) (hLκ : L ≤ 2 ^ κ)
    (hrec : ∀ rd, MemL rd Lin → RecMem rd (gen ^ rg) (gen ^ L) (gen ^ eP) base n o cells)
    (hR2 : ∀ j < n, RegionL Lin (rg + o j))
    (hR3 : ∀ j < n, ∀ c < 4, RegionL Lin (eP + 4 * o j + c)) {SB : String → ℕ}
    (hLS : TotalLe coreProgram fs "list_split" (fun _ => SB "list_split")) :
    CompleteAtDTBR fs cert κ "child_claim_list_digest" Lin
      [gen ^ eP, gen ^ rg, base, gen ^ L, gen ^ n]
      (Returns (digestCells (keccak256 (cellsBytes cells))))
      (fun rd t => ccHonestH n false h t ∧ t.pops coreProgram rd = ccPopsW n h (idxPops o 0 n))
      (ccBM fs SB false n) := by
  intro fp
  rcases Nat.eq_zero_or_pos n with rfl | hn0
  · have hcl : cells = [] := List.eq_nil_of_length_eq_zero (by simpa using hl)
    subst hcl
    refine ⟨fs "child_claim_list_digest", [], _, [], by simp [ccBM], ⟨rfl, rfl⟩,
      fun q hq => by simp at hq, B1.disj_nil, fun rd _ _ => ?_⟩
    exact (cc_emptyP fs cert fp rd).mono fun _ ht => ⟨ccHonestH_zero (nodeHonest_cc_eq 0 ▸ ht.1), by
      rw [ht.2]; rfl⟩
  have hok : KidsDTBR fs cert κ (ccKidsM Lin eP rg L n base (keccak256 (cellsBytes cells)) false)
      (fun rd => ccTsP false n rd (lsPops n) (idxPops o 0 n)) [SB "list_split", anyB fs n] :=
    ⟨fun _ => list_split_nBP fs cert hκ hn hLS,
      fun _ => child_claim_list_any_completeAtTBP fs cert hn hl hL33 hLκ hrec hR2 hR3, trivial⟩
  obtain ⟨N, Lown, rets, Lout, hN, ⟨rfl, rfl⟩, hW, hD, hr⟩ :=
    cc_nonemptyMP fs cert (by omega) hn (mono := false) (h := h) (fun h => absurd h (by simp))
      (fun _ => hh) fp (kidsAtR_of_kidsDTBR hok _)
  refine ⟨_, Lown, _, [], ?_, ⟨rfl, rfl⟩, hW, hD, fun rd hl hm => ?_⟩
  swap
  · refine (hr rd hl hm).mono fun t ht => ⟨ht.1, ?_⟩
    rw [ht.2, ccPopsW, ite_eq_right (show ¬ n = 0 by omega)]
    rfl
  simp only [kidsBoundL, ccKidsM, List.headD_cons, List.tail_cons, ↓reduceIte] at hN
  simp only [ccBM, show n ≠ 0 by omega, ↓reduceIte, Bool.false_eq_true]
  omega

/-- **`child_claim_list_digest` on the gap walk** (the hint `g`), with its pops. -/
theorem child_claim_list_digest_completeAtTBP_mono (fs : String → ℕ) (cert : String → V → ℕ)
    {κ : ℕ} (hκ : 20 ≤ κ) {Lin : Main.Layout} {eP rg L n : ℕ} {base : E} {o : ℕ → ℕ}
    {cells : List E} (hn : n < claimBig * bigFramesCap) (hl : cells.length = 4 * n)
    (hLκ : L < 2 ^ κ) (hinc : ∀ j < n, mStart o j ≤ o j) (hend : mStart o n ≤ L)
    (hrec : ∀ rd, MemL rd Lin → MRec rd (gen ^ rg) L (gen ^ eP) base n o cells)
    (hR2 : ∀ j < n, RegionL Lin (rg + o j))
    (hR3 : ∀ j < n, ∀ c < 4, RegionL Lin (eP + 4 * o j + c)) {SB : String → ℕ}
    (hLS : TotalLe coreProgram fs "list_split" (fun _ => SB "list_split")) :
    CompleteAtDTBR fs cert κ "child_claim_list_digest" Lin
      [gen ^ eP, gen ^ rg, base, gen ^ L, gen ^ n]
      (Returns (digestCells (keccak256 (cellsBytes cells))))
      (fun rd t => ccHonestH n true gen t ∧ t.pops coreProgram rd = ccPopsW n gen (gapPops o 0 n))
      (ccBM fs SB true n) := by
  intro fp
  rcases Nat.eq_zero_or_pos n with rfl | hn0
  · have hcl : cells = [] := List.eq_nil_of_length_eq_zero (by simpa using hl)
    subst hcl
    refine ⟨fs "child_claim_list_digest", [], _, [], by simp [ccBM], ⟨rfl, rfl⟩,
      fun q hq => by simp at hq, B1.disj_nil, fun rd _ _ => ?_⟩
    exact (cc_emptyP fs cert fp rd).mono fun _ ht => ⟨ccHonestH_zero (nodeHonest_cc_eq 0 ▸ ht.1), by
      rw [ht.2]; rfl⟩
  have hok : KidsDTBR fs cert κ (ccKidsM Lin eP rg L n base (keccak256 (cellsBytes cells)) true)
      (fun rd => ccTsP true n rd (lsPops n) (gapPops o 0 n)) [SB "list_split", monoB fs n] :=
    ⟨fun _ => list_split_nBP fs cert hκ hn hLS,
      fun _ => child_claim_list_mono_completeAtTBP fs cert hn hl hLκ hinc hend hrec hR2 hR3, trivial⟩
  obtain ⟨N, Lown, rets, Lout, hN, ⟨rfl, rfl⟩, hW, hD, hr⟩ :=
    cc_nonemptyMP fs cert (by omega) hn (mono := true) (h := gen) (fun _ => rfl)
      (fun h => absurd h (by simp)) fp (kidsAtR_of_kidsDTBR hok _)
  refine ⟨_, Lown, _, [], ?_, ⟨rfl, rfl⟩, hW, hD, fun rd hl hm => ?_⟩
  swap
  · refine (hr rd hl hm).mono fun t ht => ⟨ht.1, ?_⟩
    rw [ht.2, ccPopsW, ite_eq_right (show ¬ n = 0 by omega)]
    rfl
  simp only [kidsBoundL, ccKidsM, List.headD_cons, List.tail_cons, ↓reduceIte] at hN
  simp only [ccBM, show n ≠ 0 by omega, ↓reduceIte]
  omega


end
end LeanVM.Guest.B1.Digest
