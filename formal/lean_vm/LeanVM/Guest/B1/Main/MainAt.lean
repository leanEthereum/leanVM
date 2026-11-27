/-
  LeanVM.Guest.B1.Main.MainAt

  `main` placed at a frame pointer: its buffers after its frame, `exponent_tables` and its other
  callees after them, loading only its header outside its own data.
-/

module

public import LeanVM.Guest.B1.Main.MainAtDefs
public import LeanVM.Guest.B1.Main.MainCoreThm
public import LeanVM.Guest.B1.Da.AtBase
public import LeanVM.Guest.B1.Main.KidsT
public import LeanVM.Guest.Budget.Bounded
public import LeanVM.Guest.Data.NameStrings
import LeanVM.Guest.ValRef
import LeanVM.Guest.Data.ValNames.«main»
import LeanVM.Guest.LitRef
import LeanVM.Guest.StmtsAppend

/-!
# `main`, placed

`main_relAtInT_core`: at `fp`, with `main`'s honest valuation (`main_core`) on a memory holding its
buffers, `exponent_tables`' tables, its callees' layouts and its header (words `0` and `1`), `main`
holds by a tree placed at `fp` loading outside its own data only its header; its callees are
`exponent_tables` (`et_at`) and the `CompleteAtD` callees `mKids` (hypothesis `hok`, whichever are
entered). The walk takes the direct DA check when `n_direct_da = 1` (else stores the zero
digest) and the batching when `n_children ≠ 0`.
-/

namespace LeanVM.Guest.B1.Main

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Memory
open LeanVM.Protocol LeanVM.Protocol.Verifier LeanVM.Protocol.KeccakHash
open LeanVM.Guest.B1.Digest LeanVM.Guest.B1.Fwd
open LeanVM.Guest.B1 (CompleteAtD CompleteAtDT KidsDT KidsDTB kidsFromInT_of_kidsDTB kidsBoundL Returns Kid OutsOk CallsMatch RegionsOk outRegion DisjL Within LowDef
  disj_append kidsFromIn_of_kidsD regionsOk_of within_append bufL bufL_within bufL_disj bufL_region)
open LeanVM.Guest.B1.Da (SlOk slEvs_holds limb0_gen_pow_mul exists_of_length_succ)

@[expose] public section

/-! ## Walks with a branch -/

theorem walk_ite_straight (σ : Val) (c : V) (z n rest : List Stmt) (hz : z.all Main.Stmt.straight = true)
    (hn : n.all Main.Stmt.straight = true) :
    walk σ (.ite c z n :: rest) =
      (walk σ rest).pre (.inK c :: (if σ c = 0 then z else n).flatMap (Main.slEvs σ)) := by
  rw [walk, walk1]
  split_ifs
  · rw [walk_straight_fall σ z hz]; rfl
  · rw [walk_straight_fall σ n hn]; rfl

/-- `main`'s events under `σ`. -/
noncomputable def mEvs (σ : Val) : List Ev :=
  mPre.flatMap (Main.slEvs σ) ++ (.inK (.n (val% «main» "s50#1")) :: (if σ (.n (val% «main» "s50#1")) = 0 then mDa else mDaZ).flatMap
    (Main.slEvs σ) ++ (mMid.flatMap (Main.slEvs σ) ++ (.inK (.n (val% «main» "s63#1")) :: (if σ (.n (val% «main» "s63#1")) = 0 then mLeaf
      else mAgg).flatMap (Main.slEvs σ) ++ mPost.flatMap (Main.slEvs σ))))

theorem walk_main (σ : Val) : walk σ (Fn.body fn% «main») = .ret (mEvs σ) [] := by
  obtain ⟨s1, s2, s2', s3, s4, s5, s6⟩ := mBlocks_straight
  rw [main_shape, show mPre ⧺ [.ite (.n (val% «main» "s50#1")) mDa mDaZ] ⧺ mMid ⧺ [.ite (.n (val% «main» "s63#1")) mLeaf mAgg] ⧺
      mPost ⧺ [.ret []] = mPre ++ (.ite (.n (val% «main» "s50#1")) mDa mDaZ :: (mMid ++ (.ite (.n (val% «main» "s63#1")) mLeaf mAgg ::
        (mPost ⧺ [.ret []])))) by simp,
    B1.walk_pre_straight σ _ mPre s1, walk_ite_straight σ _ _ _ _ s2 s2',
    B1.walk_pre_straight σ _ mMid s3, walk_ite_straight σ _ _ _ _ s4 s5,
    Main.walk_straight σ [] mPost s6]
  simp only [Out.pre, mEvs, List.cons_append]

/-! ## Kids' bookkeeping -/

theorem outsOk_append : ∀ (k1 k2 : List Kid) (outs : List (List E × B1.Main.Layout)),
    OutsOk (k1 ++ k2) outs → ∃ o1 o2, outs = o1 ++ o2 ∧ OutsOk k1 o1 ∧ OutsOk k2 o2
  | [], _, outs, h => ⟨[], outs, rfl, trivial, h⟩
  | _ :: _, _, [], h => h.elim
  | k :: k1, k2, o :: outs, ⟨h, hs⟩ => by
    obtain ⟨o1, o2, rfl, h1, h2⟩ := outsOk_append k1 k2 outs hs
    exact ⟨o :: o1, o2, rfl, ⟨h, h1⟩, h2⟩

theorem callsMatch_append {σ : Val} : ∀ (c1 : List Call) (k1 : List Kid) (o1 : List (List E × B1.Main.Layout))
    (c2 : List Call) (k2 : List Kid) (o2 : List (List E × B1.Main.Layout)),
    CallsMatch σ c1 k1 o1 → CallsMatch σ c2 k2 o2 → CallsMatch σ (c1 ++ c2) (k1 ++ k2) (o1 ++ o2)
  | [], [], [], _, _, _, _, h => h
  | [], [], _ :: _, _, _, _, h, _ => h.elim
  | [], _ :: _, _, _, _, _, h, _ => h.elim
  | _ :: _, [], _, _, _, _, h, _ => h.elim
  | _ :: _, _ :: _, [], _, _, _, h, _ => h.elim
  | _ :: c1, _ :: k1, _ :: o1, c2, k2, o2, ⟨a, b, c, h⟩, h2 =>
    ⟨a, b, c, callsMatch_append c1 k1 o1 c2 k2 o2 h h2⟩

/-! ## Blocks' events -/

theorem blk_holds {rd : Reader} {σ : Val} {P : List Stmt} {cs : List ℕ}
    (hk : P.all (mKind cs) = true) (hat : ∀ a ∈ atomsIn P, a.Holds rd σ)
    (hc : ∀ j ∈ cs, IsInK (σ (.n j))) : ∀ e ∈ P.flatMap (Main.slEvs σ), e.Holds rd σ := by
  refine slEvs_holds fun st hst => ?_
  have h := List.all_eq_true.mp hk st hst
  match st, h with
  | .atom a, _ => exact hat a (mem_atomsIn' hst)
  | .call .., _ => trivial
  | .callIf c f args, h =>
    simp only [mKind, Bool.and_eq_true, decide_eq_true_eq] at h
    show IsInK (σ c)
    rw [h.1]; exact hc _ h.2
  | .ite .., h => simp [mKind] at h
  | .match_ .., h => simp [mKind] at h
  | .dispatch .., h => simp [mKind] at h
  | .ret _, h => simp [mKind] at h

theorem one_add_isInK (a : ℕ) : IsInK ((1 : E) + gen ^ a) := by
  rw [← pow_zero gen]; exact isInK_add (gen_pow_isInK _) (gen_pow_isInK _)

theorem allocs_inK (σ : Val) (c : V) (xs : List Ev) : allocs σ (.inK c :: xs) = allocs σ xs := rfl
theorem allocDsts_inK (c : V) (xs : List Ev) : allocDsts (.inK c :: xs) = allocDsts xs := rfl
theorem addrs_inK (c : V) (xs : List Ev) : addrs (.inK c :: xs) = addrs xs := rfl
theorem calls_inK (c : V) (xs : List Ev) : calls (.inK c :: xs) = calls xs := rfl
theorem loadAddrs_inK (σ : Val) (c : V) (xs : List Ev) : loadAddrs σ (.inK c :: xs) = loadAddrs σ xs :=
  rfl

/-! ## `main` -/

theorem mKids_lin (m : MainIn) (Lin : B1.Main.Layout) : ∀ k ∈ mKids m Lin, k.Lin = Lin := by
  intro k hk
  unfold mKids at hk
  split_ifs at hk <;> simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false,
    List.append_nil] at hk <;> aesop

theorem reads_of_memL' {rd : Reader} {L : B1.Main.Layout} (h : B1.Main.MemL rd L) {b : ℕ}
    {xs : List E} (hq : (b, xs) ∈ L) : ReadsAt rd (gen ^ b) xs := by
  rw [gen_pow_eq_ofK]; exact h _ hq

theorem one_add_ne_iff {a : ℕ} (ha : a < 2 ^ 64 - 1) : ((1 : E) + gen ^ a ≠ 0) ↔ a ≠ 0 := by
  rw [Ne, e_add_eq_zero_iff, eq_comm, gen_pow_eq_one_iff ha]

theorem taken_eq {σ : Val} {c : V} {a : ℕ} (ha : a < 2 ^ 64 - 1) (h : σ c = 1 + gen ^ a) :
    decide (σ c ≠ 0) = decide (a ≠ 0) := by
  rw [h]; exact decide_eq_decide.mpr (one_add_ne_iff ha)

/-- `main`'s frames, in call order. -/
def mCalls (σ : Val) (m : MainIn) : List Call :=
  (⟨"exponent_tables", [], [.n (val% «main» "g_squares")], true⟩ : Call) ::
    ([⟨"claim_list_digest", [.n (val% «main» "lx_table"), .n (val% «main» "meta[0]")], [.n (val% «main» "xd_0"), .n (val% «main» "xd_1")], true⟩,
      ⟨"claim_list_digest", [.n (val% «main» "lean_sphincs_table"), .n (val% «main» "meta[3]")], [.n (val% «main» "sd_0"), .n (val% «main» "sd_1")], true⟩,
      ⟨name% «main_loop0», [.n (val% «main» "s38#2"), .n (val% «main» "meta[1]"), .n (val% «main» "lx_table"), .n (val% «main» "meta[0]")], [], decide (σ (.n (val% «main» "s38#1")) ≠ 0)⟩,
      ⟨name% «main_loop1», [.n (val% «main» "s39#2"), .n (val% «main» "meta[4]"), .n (val% «main» "lean_sphincs_table"), .n (val% «main» "meta[3]")], [], decide (σ (.n (val% «main» "s39#1")) ≠ 0)⟩,
      ⟨name% «main_loop2», [.n (val% «main» "s46#2"), .n (val% «main» "meta[2]"), .n (val% «main» "lx_slots_g"), .n (val% «main» "cover"), .n (val% «main» "lx_table")] ++ lxTagsV, [],
          decide (σ (.n (val% «main» "s46#1")) ≠ 0)⟩,
      ⟨name% «main_loop3», [.n (val% «main» "s47#2"), .n (val% «main» "meta[5]"), .n (val% «main» "lean_sphincs_slots_g"), .n (val% «main» "sp_cover"), .n (val% «main» "meta[2]"), .n (val% «main» "lean_sphincs_table"), .n (val% «main» "byte_bits")], [],
        decide (σ (.n (val% «main» "s47#1")) ≠ 0)⟩] ++
    (if m.nd = 1 then [(⟨"da_verify", [.n (val% «main» "byte_bits")], [.n (val% «main» "root_0"), .n (val% «main» "root_1"), .n (val% «main» "z")], true⟩ : Call)]
      else []) ++
    [⟨name% «main_loop4», [.n (val% «main» "s56#2"), .n (val% «main» "meta[6]"), .n (val% «main» "written"), .n (val% «main» "lx_table"), .n (val% «main» "cover"), .n (val% «main» "lx_slots_g"), .n (val% «main» "lean_sphincs_table"), .n (val% «main» "sp_cover"), .n (val% «main» "lean_sphincs_slots_g"), .n (val% «main» "child_carried"),
      .n (val% «main» "da_digests"), .n (val% «main» "fs_seed[0]"), .n (val% «main» "fs_seed[1]"), .n (val% «main» "child_pi"), .n (val% «main» "g_squares"), .n (val% «main» "child_fresh")], [], decide (σ (.n (val% «main» "s56#1")) ≠ 0)⟩] ++
    (if m.nc = 0 then [] else [(⟨"aggregate_claims", [.n (val% «main» "meta[6]"), .n (val% «main» "child_pi"), .n (val% «main» "child_fresh"), .n (val% «main» "child_carried"), .n (val% «main» "defer_stmt"), .n (val% «main» "s63.e.s0#1")], [],
      true⟩ : Call)]) ++
    [⟨"statement_digest", [.n (val% «main» "fs_seed[0]"), .n (val% «main» "fs_seed[1]"), .n (val% «main» "xd_0"), .n (val% «main» "xd_1"), .n (val% «main» "sd_0"), .n (val% «main» "sd_1"), .n (val% «main» "own_0~2"), .n (val% «main» "own_0~3"), .n (val% «main» "defer_stmt")],
      [.n (val% «main» "own_0"), .n (val% «main» "own_1")], true⟩])

set_option maxRecDepth 40000 in
/-- **`main` at `fp`**: its honest valuation on a memory holding its buffers `own`,
`exponent_tables`' tables, its callees' layouts and its header holds by a tree placed at `fp`,
loading outside its own data only its header (words `0`, `1`); the tree is `main`'s node at a
valuation with `main`'s honest values (`MVals`). -/
theorem main_relAtInT_core (fs : String → ℕ) (cert : String → V → ℕ) (fp : ℕ) (d : MainData)
    (own : List (List E)) (hfit : List.Forall₂ (fun c s => c.length ≤ s) own (mSizes d))
    (hb : MainBounds (2 ^ 23) (d.toIn fs fp))
    (Ts : Reader → List (Tree → Prop)) (Nk : ℕ) (Lk : B1.Main.Layout) (outs : List (List E × B1.Main.Layout))
    (hoo : OutsOk (mKids (d.toIn fs fp) (bufL (fp + fs "main") (mSizes d) own ++ etL d fs fp)) outs)
    (hW : Within Lk (etB fs (mK0 d fs fp) + lit% B1.expTabN) Nk) (hD : DisjL Lk)
    (hKids : ∀ (rd : Reader) (σ : Val) (cs : List Call) (R Dacc : ℕ → Prop),
      CallsMatch σ cs (mKids (d.toIn fs fp) (bufL (fp + fs "main") (mSizes d) own ++ etL d fs fp)) outs →
      LowDef 23 rd → B1.Main.MemL rd Lk →
      B1.Main.MemL rd (Kid.lins (mKids (d.toIn fs fp) (bufL (fp + fs "main") (mSizes d) own ++ etL d fs fp))) →
      RegionsOk R Dacc (mKids (d.toIn fs fp) (bufL (fp + fs "main") (mSizes d) own ++ etL d fs fp)) outs →
      KidsFromInT coreProgram fs cert rd σ R Dacc cs (Ts rd) (etB fs (mK0 d fs fp) + lit% B1.expTabN) Nk
        (fun i => Dacc i ∨ outRegion (mKids (d.toIn fs fp) (bufL (fp + fs "main") (mSizes d) own ++
          etL d fs fp)) outs i))
    (hmm : ∀ rd, B1.Main.MemL rd (bufL (fp + fs "main") (mSizes d) own) →
      LoadHolds rd 1 0 (digestHalves d.sdg).1 → LoadHolds rd gen 0 (digestHalves d.sdg).2 →
        MainMem rd (d.toIn fs fp)) :
    ∃ (L : B1.Main.Layout),
      Within L fp (fs "main" + (mSizes d).sum + (fs "exponent_tables" + lit% B1.expTabN + Nk)) ∧ (∀ q ∈ L, fp + fs "main" ≤ q.1) ∧ DisjL L ∧
      (∀ q ∈ bufL (fp + fs "main") (mSizes d) own ++ etL d fs fp, q ∈ L) ∧
      ∀ rd, LowDef 23 rd → B1.Main.MemL rd L → LoadHolds rd 1 0 (digestHalves d.sdg).1 →
        LoadHolds rd gen 0 (digestHalves d.sdg).2 →
        RelAtInT coreProgram fs cert rd (fun i => i < 2) (fun _ => False) fp (fs "main" + (mSizes d).sum + (fs "exponent_tables" + lit% B1.expTabN + Nk)) "main"
          [] []
          (fun t => ∃ σ bufs ks, t = .node "main" σ bufs ks ∧ MVals rd σ (d.toIn fs fp) ∧
            KidsT (mCalls σ (d.toIn fs fp)) ((fun _ => True) :: Ts rd) ks ∧
            calls (mEvs σ) = mCalls σ (d.toIn fs fp) ∧ bufs = mSizes d) := by
  set m := d.toIn fs fp with hmd
  set b0 := fp + fs "main" with hb0
  set Lown := bufL b0 (mSizes d) own with hLown
  set Lmain := Lown ++ etL d fs fp with hLmain
  have he : etB fs (mK0 d fs fp) = b0 + (mSizes d).sum + fs "exponent_tables" := rfl
  have hWo : Within Lown b0 (mSizes d).sum := bufL_within _ _ _ hfit
  have hWe : Within (etL d fs fp) (etB fs (mK0 d fs fp)) lit% B1.expTabN := by
    intro q hq
    simp only [etL, List.mem_cons, List.not_mem_nil, or_false] at hq
    subst hq; simp [length_expTabAllWords]
  have hDe : DisjL (etL d fs fp) := List.pairwise_singleton _ _
  have hWb : Within (Lmain ++ Lk) b0 ((mSizes d).sum + (fs "exponent_tables" + lit% B1.expTabN + Nk)) := by
    rw [within_append, within_append]
    exact ⟨⟨hWo.mono (by omega) (by omega), hWe.mono (by omega) (by omega)⟩,
      hW.mono (by omega) (by omega)⟩
  refine ⟨Lmain ++ Lk,
    hWb.mono (by omega) (by omega), fun q hq => (hWb q hq).1, ?_,
    fun q hq => List.mem_append_left _ hq, fun rd hlow hL h0 h1 => ?_⟩
  · have hW1 : Within (Lown ++ etL d fs fp) b0 ((mSizes d).sum + fs "exponent_tables" + lit% B1.expTabN) :=
      within_append.mpr ⟨hWo.mono le_rfl (by omega), hWe.mono (by omega) (by omega)⟩
    exact disj_append (disj_append (bufL_disj _ _ _ hfit) hDe hWo hWe (by omega)) hD hW1 hW
      (by omega)
  obtain ⟨⟨hLo, hLe⟩, hLk⟩ : (B1.Main.MemL rd Lown ∧ B1.Main.MemL rd (etL d fs fp)) ∧
      B1.Main.MemL rd Lk := by
    rw [B1.Main.memL_append, B1.Main.memL_append] at hL; exact hL
  have hmem := hmm rd hLo h0 h1
  obtain ⟨σ, hσ⟩ : ∃ σ, σ = mσ rd m := ⟨_, rfl⟩
  have hv : MVals rd σ m := by rw [hσ]; exact main_core hlow (by norm_num) hb hmem
  have hO : ∀ {j : ℕ}, j ∈ mOrcIdx → σ (.n j) = mOrc m j := fun hj => hv.orc _ hj
  -- the branches
  have hnc : m.nc ≤ 16 := hb.nc
  have hnd : m.nd ≤ 1 := hb.nd
  have h338 : σ (.n (val% «main» "s50#1")) = 0 ↔ m.nd = 1 := by
    rw [hv.v389, e_add_eq_zero_iff]
    constructor
    · intro h
      exact gen_pow_inj' (a := m.nd) (b := 1) (by omega) (by norm_num) (by rw [h, pow_one])
    · intro h; rw [h, pow_one]
  have h404 : σ (.n (val% «main» "s63#1")) = 0 ↔ m.nc = 0 := by
    rw [hv.v451, add_comm, e_add_eq_zero_iff, eq_comm, gen_pow_eq_one_iff (by omega)]
  have hw := walk_main σ
  have hes : mEvs σ = (mPre.flatMap (Main.slEvs σ) ++ (.inK (.n (val% «main» "s50#1")) ::
      (if m.nd = 1 then mDa else mDaZ).flatMap (Main.slEvs σ) ++ (mMid.flatMap (Main.slEvs σ) ++
        (.inK (.n (val% «main» "s63#1")) :: (if m.nc = 0 then mLeaf else mAgg).flatMap (Main.slEvs σ) ++
          mPost.flatMap (Main.slEvs σ))))) := by
    unfold mEvs
    by_cases a : m.nd = 1 <;> by_cases b : m.nc = 0
    · rw [ite_pos' (h338.mpr a), ite_pos' (h404.mpr b), ite_pos' a, ite_pos' b]
    · rw [ite_pos' (h338.mpr a), ite_neg' (fun h => b (h404.mp h)), ite_pos' a, ite_neg' b]
    · rw [ite_neg' (fun h => a (h338.mp h)), ite_pos' (h404.mpr b), ite_neg' a, ite_pos' b]
    · rw [ite_neg' (fun h => a (h338.mp h)), ite_neg' (fun h => b (h404.mp h)), ite_neg' a, ite_neg' b]
  rw [hes] at hw
  obtain ⟨s1, s2, s2', s3, s4, s5, s6⟩ := mBlocks_straight
  obtain ⟨k1, k2, k2', k3, k4, k5, k6⟩ := mBlocks_kind
  have sDa : (if m.nd = 1 then mDa else mDaZ).all Main.Stmt.straight = true := by split <;> simp_all
  have sBr : (if m.nc = 0 then mLeaf else mAgg).all Main.Stmt.straight = true := by split <;> simp_all
  -- the events hold
  have hev : ∀ x ∈ (mPre.flatMap (Main.slEvs σ) ++ (.inK (.n (val% «main» "s50#1")) ::
      (if m.nd = 1 then mDa else mDaZ).flatMap (Main.slEvs σ) ++ (mMid.flatMap (Main.slEvs σ) ++
        (.inK (.n (val% «main» "s63#1")) :: (if m.nc = 0 then mLeaf else mAgg).flatMap (Main.slEvs σ) ++
          mPost.flatMap (Main.slEvs σ))))), x.Holds rd σ := by
    intro x hx
    simp only [List.mem_append, List.mem_cons] at hx
    rcases hx with hx | (rfl | hx) | hx | (rfl | hx) | hx
    · refine blk_holds k1 hv.pre (fun j hj => ?_) x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
      rcases hj with rfl | rfl | rfl | rfl
      · rw [hv.g61]; exact one_add_isInK _
      · rw [hv.g64]; exact one_add_isInK _
      · rw [hv.g377]; exact one_add_isInK _
      · rw [hv.g380]; exact one_add_isInK _
    · show IsInK (σ (.n (val% «main» "s50#1")))
      rw [hv.v389]
      exact isInK_add (gen_pow_isInK _) (by simpa using gen_pow_isInK 1)
    · split at hx
      · rename_i h1
        exact blk_holds k2 (hv.da h1) (fun j hj => by simp at hj) x hx
      · rename_i h1
        exact blk_holds k2' (hv.daZ h1) (fun j hj => by simp at hj) x hx
    · refine blk_holds k3 hv.mid (fun j hj => ?_) x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
      subst hj; rw [hv.g434]; exact one_add_isInK _
    · show IsInK (σ (.n (val% «main» "s63#1")))
      rw [hv.v451, add_comm]; exact one_add_isInK _
    · split at hx
      · rename_i h0'
        exact blk_holds k4 (hv.leaf h0') (fun j hj => by simp at hj) x hx
      · exact blk_holds k5 hv.agg (fun j hj => by simp at hj) x hx
    · exact blk_holds k6 hv.post (fun j hj => by simp at hj) x hx
  -- the path's parts
  obtain ⟨pd1, pa1, pad1, pc1⟩ := Main.straight_parts σ _ s1
  obtain ⟨pd2, pa2, pad2, pc2⟩ := Main.straight_parts σ _ sDa
  obtain ⟨pd3, pa3, pad3, pc3⟩ := Main.straight_parts σ _ s3
  obtain ⟨pd4, pa4, pad4, pc4⟩ := Main.straight_parts σ _ sBr
  obtain ⟨pd5, pa5, pad5, pc5⟩ := Main.straight_parts σ _ s6
  obtain ⟨a1, a2, a2', a3, a4, a5, a6⟩ := mBlocks_allocs
  have aDa : (if m.nd = 1 then mDa else mDaZ).filterMap Main.Stmt.allocSz = [] := by
    split <;> simp_all
  have aBr : (if m.nc = 0 then mLeaf else mAgg).filterMap Main.Stmt.allocSz = [] := by
    split <;> simp_all
  have hX : m.nlx + m.nxd < 2 ^ 23 := by have := hb.total; simp only [MainIn.total] at this; omega
  have hY : m.nls + m.nsd < 2 ^ 23 := by have := hb.total; simp only [MainIn.total] at this; omega
  have hT : m.total < 2 ^ 23 := hb.total
  have hal : allocs σ (mPre.flatMap (Main.slEvs σ) ++ (.inK (.n (val% «main» "s50#1")) ::
      (if m.nd = 1 then mDa else mDaZ).flatMap (Main.slEvs σ) ++ (mMid.flatMap (Main.slEvs σ) ++
        (.inK (.n (val% «main» "s63#1")) :: (if m.nc = 0 then mLeaf else mAgg).flatMap (Main.slEvs σ) ++
          mPost.flatMap (Main.slEvs σ))))) = mSizes d := by
    rw [allocs_append, allocs_append, allocs_inK, allocs_append, allocs_append, allocs_inK, pa1, pa2,
      pa3, pa4, pa5, a1, aDa, a3, aBr, a6]
    simp only [List.map_cons, List.map_nil, Sum.elim_inr, Sum.elim_inl, id, List.append_nil,
      List.nil_append, List.cons_append, hv.v51, hv.v54, hv.v42, hv.v384, hv.v415, hv.v421,
      hv.v427, hv.v430,
      logG_gen_pow (show 4 * (m.nlx + m.nxd) < 2 ^ 64 - 1 by omega),
      logG_gen_pow (show 4 * (m.nls + m.nsd) < 2 ^ 64 - 1 by omega),
      logG_gen_pow (show m.total < 2 ^ 64 - 1 by omega), logG_gen_pow (show 2 * (m.nc + 1) < 2 ^ 64 - 1 by omega),
      logG_gen_pow (show 2 * m.nc < 2 ^ 64 - 1 by omega),
      logG_gen_pow (show 24 * m.nc < 2 ^ 64 - 1 by omega), logG_gen_pow (show m.nc + 1 < 2 ^ 64 - 1 by omega)]
    rfl
  -- the pointers
  have o53 : σ (.n (val% «main» "lx_table")) = gen ^ (Memory.bases b0 (mSizes d)).getD 0 0 := by rw [hO (by decide)]; rfl
  have o56 : σ (.n (val% «main» "lean_sphincs_table")) = gen ^ (Memory.bases b0 (mSizes d)).getD 1 0 := by rw [hO (by decide)]; rfl
  have o67 : σ (.n (val% «main» "cover")) = gen ^ (Memory.bases b0 (mSizes d)).getD 2 0 := by rw [hO (by decide)]; rfl
  have o68 : σ (.n (val% «main» "byte_bits")) = gen ^ (Memory.bases b0 (mSizes d)).getD 3 0 := by rw [hO (by decide)]; rfl
  have o334 : σ (.n (val% «main» "da_digests")) = gen ^ (Memory.bases b0 (mSizes d)).getD 4 0 := by rw [hO (by decide)]; rfl
  have o365 : σ (.n (val% «main» "child_pi")) = gen ^ (Memory.bases b0 (mSizes d)).getD 5 0 := by rw [hO (by decide)]; rfl
  have o371 : σ (.n (val% «main» "child_fresh")) = gen ^ (Memory.bases b0 (mSizes d)).getD 6 0 := by rw [hO (by decide)]; rfl
  have o377 : σ (.n (val% «main» "child_carried")) = gen ^ (Memory.bases b0 (mSizes d)).getD 7 0 := by rw [hO (by decide)]; rfl
  have o380 : σ (.n (val% «main» "written")) = gen ^ (Memory.bases b0 (mSizes d)).getD 8 0 := by rw [hO (by decide)]; rfl
  have o402 : σ (.n (val% «main» "defer_stmt")) = gen ^ (Memory.bases b0 (mSizes d)).getD 9 0 := by rw [hO (by decide)]; rfl
  have hbuf : (allocDsts (mPre.flatMap (Main.slEvs σ) ++ (.inK (.n (val% «main» "s50#1")) ::
      (if m.nd = 1 then mDa else mDaZ).flatMap (Main.slEvs σ) ++ (mMid.flatMap (Main.slEvs σ) ++
        (.inK (.n (val% «main» "s63#1")) :: (if m.nc = 0 then mLeaf else mAgg).flatMap (Main.slEvs σ) ++
          mPost.flatMap (Main.slEvs σ)))))).map σ = (Memory.bases b0 (mSizes d)).map fun b => ofK (addressOfIndex b) := by
    rw [allocDsts_append, allocDsts_append, allocDsts_inK, allocDsts_append, allocDsts_append,
      allocDsts_inK, pd1, pd2, pd3, pd4, pd5, a1, aDa, a3, aBr, a6]
    simp only [List.map_cons, List.map_nil, List.append_nil, List.nil_append, List.cons_append,
      o53, o56, o67, o68, o334, o365, o371, o377, o380, o402, gen_pow_eq_ofK]
    rfl
  -- the calls
  have cDa : (if m.nd = 1 then mDa else mDaZ).filterMap Main.Stmt.callS =
      if m.nd = 1 then [(none, "da_verify", [.n (val% «main» "byte_bits")], [.n (val% «main» "root_0"), .n (val% «main» "root_1"), .n (val% «main» "z")])]
      else [] := by
    split
    · exact mDa_calls
    · exact mDaZ_calls
  have cBr : (if m.nc = 0 then mLeaf else mAgg).filterMap Main.Stmt.callS =
      if m.nc = 0 then [] else [(none, "aggregate_claims", [.n (val% «main» "meta[6]"), .n (val% «main» "child_pi"), .n (val% «main» "child_fresh"), .n (val% «main» "child_carried"), .n (val% «main» "defer_stmt"), .n (val% «main» "s63.e.s0#1")], [])] := by
    split
    · exact mLeaf_calls
    · exact mAgg_calls
  have hcalls : calls (mPre.flatMap (Main.slEvs σ) ++ (.inK (.n (val% «main» "s50#1")) ::
      (if m.nd = 1 then mDa else mDaZ).flatMap (Main.slEvs σ) ++ (mMid.flatMap (Main.slEvs σ) ++
        (.inK (.n (val% «main» "s63#1")) :: (if m.nc = 0 then mLeaf else mAgg).flatMap (Main.slEvs σ) ++
          mPost.flatMap (Main.slEvs σ))))) = mCalls σ m := by
    unfold mCalls
    rw [calls_append, calls_append, calls_inK, calls_append, calls_append, calls_inK, pc1, pc2, pc3, pc4,
      pc5, mPre_calls, cDa, mMid_calls, cBr, mPost_calls]
    split <;> split <;> simp [Main.mkCall]
  -- the own data
  have hzip : ∀ j < 10, ((mSizes d).getD j 0, (Memory.bases b0 (mSizes d)).getD j 0) ∈
      (mSizes d).zip (Memory.bases b0 (mSizes d)) := by
    intro j hj
    interval_cases j <;> simp [mSizes, Memory.bases]
  set es := (mPre.flatMap (Main.slEvs σ) ++ (.inK (.n (val% «main» "s50#1")) ::
      (if m.nd = 1 then mDa else mDaZ).flatMap (Main.slEvs σ) ++ (mMid.flatMap (Main.slEvs σ) ++
        (.inK (.n (val% «main» "s63#1")) :: (if m.nc = 0 then mLeaf else mAgg).flatMap (Main.slEvs σ) ++
          mPost.flatMap (Main.slEvs σ))))) with hesd
  have hown : ∀ j < 10, ∀ k < (mSizes d).getD j 0,
      ownData cert fp b0 "main" (mSizes d) es ((Memory.bases b0 (mSizes d)).getD j 0 + k) :=
    fun j hj k hk => Or.inl ⟨_, hzip j hj, by simp only; omega, by simp only; omega⟩
  -- the callees
  have o49 : σ (.n (val% «main» "g_squares")) = gen ^ etB fs (mK0 d fs fp) := by rw [hO (by decide)]; rfl
  have hExp : ExpTables rd (gen ^ etB fs (mK0 d fs fp)) ∧ ExpWinTab rd (gen ^ etB fs (mK0 d fs fp)) :=
    expTables_of_reads (reads_of_memL' hLe List.mem_cons_self)
  have hlenK := hoo.length
  -- the outputs, by segment
  obtain ⟨oA4, oE, rfl, hoAD, hoE⟩ := outsOk_append _ _ outs hoo
  obtain ⟨oA3, oD, rfl, hoAC, hoD⟩ := outsOk_append _ _ oA4 hoAD
  obtain ⟨oA2, oC, rfl, hoAB, hoC⟩ := outsOk_append _ _ oA3 hoAC
  obtain ⟨oA, oB, rfl, hoA, hoB⟩ := outsOk_append _ _ oA2 hoAB
  have lA0 := hoA.length
  obtain ⟨a1, t1, rfl, lA1⟩ := exists_of_length_succ lA0
  obtain ⟨a2, t2, rfl, lA2⟩ := exists_of_length_succ lA1
  obtain ⟨a3, t3, rfl, lA3⟩ := exists_of_length_succ lA2
  obtain ⟨a4, t4, rfl, lA4⟩ := exists_of_length_succ lA3
  obtain ⟨a5, t5, rfl, lA5⟩ := exists_of_length_succ lA4
  obtain ⟨a6, t6, rfl, lA6⟩ := exists_of_length_succ lA5
  obtain rfl := List.eq_nil_of_length_eq_zero lA6
  obtain ⟨q1, q2, q3, q4, q5, q6, -⟩ := hoA
  have lC0 := hoC.length
  obtain ⟨c5, tc, rfl, lC1⟩ := exists_of_length_succ lC0
  obtain rfl := List.eq_nil_of_length_eq_zero lC1
  have lE0 := hoE.length
  obtain ⟨e1, te, rfl, lE1⟩ := exists_of_length_succ lE0
  obtain rfl := List.eq_nil_of_length_eq_zero lE1
  have hrx := hb.rx
  have hrs := hb.rs
  have hxd := hb.xd
  have hsd := hb.sd
  have hCM : CallsMatch σ ([⟨"claim_list_digest", [.n (val% «main» "lx_table"), .n (val% «main» "meta[0]")], [.n (val% «main» "xd_0"), .n (val% «main» "xd_1")], true⟩,
          ⟨"claim_list_digest", [.n (val% «main» "lean_sphincs_table"), .n (val% «main» "meta[3]")], [.n (val% «main» "sd_0"), .n (val% «main» "sd_1")], true⟩,
          ⟨name% «main_loop0», [.n (val% «main» "s38#2"), .n (val% «main» "meta[1]"), .n (val% «main» "lx_table"), .n (val% «main» "meta[0]")], [], decide (σ (.n (val% «main» "s38#1")) ≠ 0)⟩,
          ⟨name% «main_loop1», [.n (val% «main» "s39#2"), .n (val% «main» "meta[4]"), .n (val% «main» "lean_sphincs_table"), .n (val% «main» "meta[3]")], [], decide (σ (.n (val% «main» "s39#1")) ≠ 0)⟩,
          ⟨name% «main_loop2», [.n (val% «main» "s46#2"), .n (val% «main» "meta[2]"), .n (val% «main» "lx_slots_g"), .n (val% «main» "cover"), .n (val% «main» "lx_table")] ++ lxTagsV, [],
              decide (σ (.n (val% «main» "s46#1")) ≠ 0)⟩,
          ⟨name% «main_loop3», [.n (val% «main» "s47#2"), .n (val% «main» "meta[5]"), .n (val% «main» "lean_sphincs_slots_g"), .n (val% «main» "sp_cover"), .n (val% «main» "meta[2]"), .n (val% «main» "lean_sphincs_table"), .n (val% «main» "byte_bits")], [],
            decide (σ (.n (val% «main» "s47#1")) ≠ 0)⟩] ++
        (if m.nd = 1 then [(⟨"da_verify", [.n (val% «main» "byte_bits")], [.n (val% «main» "root_0"), .n (val% «main» "root_1"), .n (val% «main» "z")], true⟩ : Call)]
          else []) ++
        [⟨name% «main_loop4», [.n (val% «main» "s56#2"), .n (val% «main» "meta[6]"), .n (val% «main» "written"), .n (val% «main» "lx_table"), .n (val% «main» "cover"), .n (val% «main» "lx_slots_g"), .n (val% «main» "lean_sphincs_table"), .n (val% «main» "sp_cover"), .n (val% «main» "lean_sphincs_slots_g"),
            .n (val% «main» "child_carried"),
          .n (val% «main» "da_digests"), .n (val% «main» "fs_seed[0]"), .n (val% «main» "fs_seed[1]"), .n (val% «main» "child_pi"), .n (val% «main» "g_squares"), .n (val% «main» "child_fresh")], [], decide (σ (.n (val% «main» "s56#1")) ≠ 0)⟩] ++
        (if m.nc = 0 then [] else [(⟨"aggregate_claims", [.n (val% «main» "meta[6]"), .n (val% «main» "child_pi"), .n (val% «main» "child_fresh"), .n (val% «main» "child_carried"), .n (val% «main» "defer_stmt"), .n (val% «main» "s63.e.s0#1")], [],
          true⟩ : Call)]) ++
        [⟨"statement_digest", [.n (val% «main» "fs_seed[0]"), .n (val% «main» "fs_seed[1]"), .n (val% «main» "xd_0"), .n (val% «main» "xd_1"), .n (val% «main» "sd_0"), .n (val% «main» "sd_1"), .n (val% «main» "own_0~2"), .n (val% «main» "own_0~3"), .n (val% «main» "defer_stmt")],
          [.n (val% «main» "own_0"), .n (val% «main» "own_1")], true⟩])
      (mKids m Lmain) ([a1, a2, a3, a4, a5, a6] ++ oB ++ [c5] ++ oD ++ [e1]) := by
    unfold mKids
    refine callsMatch_append _ _ _ _ _ _ (callsMatch_append _ _ _ _ _ _ (callsMatch_append _ _ _ _ _ _
      (callsMatch_append _ _ _ _ _ _ ?_ ?_) ?_) ?_) ?_
    · refine ⟨rfl, rfl, fun _ => ⟨?_, ?_⟩, rfl, rfl, fun _ => ⟨?_, ?_⟩,
        rfl, taken_eq (by omega) hv.g61, fun _ => ⟨?_, ?_⟩, rfl, taken_eq (by omega) hv.g64,
        fun _ => ⟨?_, ?_⟩, rfl, taken_eq (by omega) hv.g377, fun _ => ⟨?_, ?_⟩, rfl,
        taken_eq (by omega) hv.g380, fun _ => ⟨?_, ?_⟩, trivial⟩
      · show [σ (.n (val% «main» "lx_table")), σ (.n (val% «main» "meta[0]"))] = _
        rw [hO (by decide), hO (by decide)]; rfl
      · rw [(q1 rfl).1]; show [σ (.n (val% «main» "xd_0")), σ (.n (val% «main» "xd_1"))] = _
        rw [hO (by decide), hO (by decide)]; rfl
      · show [σ (.n (val% «main» "lean_sphincs_table")), σ (.n (val% «main» "meta[3]"))] = _
        rw [hO (by decide), hO (by decide)]; rfl
      · rw [(q2 rfl).1]; show [σ (.n (val% «main» "sd_0")), σ (.n (val% «main» "sd_1"))] = _
        rw [hO (by decide), hO (by decide)]; rfl
      · show [σ (.n (val% «main» "s38#2")), σ (.n (val% «main» "meta[1]")), σ (.n (val% «main» "lx_table")), σ (.n (val% «main» "meta[0]"))] = _
        rw [hv.g62, hO (by decide), hO (by decide), hO (by decide)]; rfl
      · rw [(q3 (by assumption)).1]; rfl
      · show [σ (.n (val% «main» "s39#2")), σ (.n (val% «main» "meta[4]")), σ (.n (val% «main» "lean_sphincs_table")), σ (.n (val% «main» "meta[3]"))] = _
        rw [hv.g65, hO (by decide), hO (by decide), hO (by decide)]; rfl
      · rw [(q4 (by assumption)).1]; rfl
      · show [σ (.n (val% «main» "s46#2")), σ (.n (val% «main» "meta[2]")), σ (.n (val% «main» "lx_slots_g")), σ (.n (val% «main» "cover")), σ (.n (val% «main» "lx_table"))] ++ lxTagsV.map σ = _
        rw [hv.g378, hO (by decide), hv.v40, hO (by decide), hO (by decide), hv.tags]; rfl
      · rw [(q5 (by assumption)).1]; rfl
      · show [σ (.n (val% «main» "s47#2")), σ (.n (val% «main» "meta[5]")), σ (.n (val% «main» "lean_sphincs_slots_g")), σ (.n (val% «main» "sp_cover")), σ (.n (val% «main» "meta[2]")), σ (.n (val% «main» "lean_sphincs_table")), σ (.n (val% «main» "byte_bits"))] = _
        rw [hv.g381, hO (by decide), hv.v41, hv.v67, hO (by decide), hO (by decide),
          hO (by decide)]; rfl
      · rw [(q6 (by assumption)).1]; rfl
    · split
      · rename_i hnd1
        rw [ite_pos' hnd1] at hoB
        have lB0 := hoB.length
        obtain ⟨b1, tb1, rfl, lB1⟩ := exists_of_length_succ lB0
        obtain rfl := List.eq_nil_of_length_eq_zero lB1
        obtain ⟨r1, -⟩ := hoB
        refine ⟨rfl, rfl, fun _ => ⟨?_, ?_⟩, trivial⟩
        · show [σ (.n (val% «main» "byte_bits"))] = _
          rw [hO (by decide)]; rfl
        · rw [(r1 rfl).1]; show [σ (.n (val% «main» "root_0")), σ (.n (val% «main» "root_1")), σ (.n (val% «main» "z"))] = _
          rw [hO (by decide), hO (by decide), hO (by decide)]
          have hl4 := hb.daR hnd1
          obtain ⟨x0, u0, h0', l0⟩ := exists_of_length_succ hl4
          obtain ⟨x1, u1, rfl, l1⟩ := exists_of_length_succ l0
          obtain ⟨x2, u2, rfl, l2⟩ := exists_of_length_succ l1
          obtain rfl := List.eq_nil_of_length_eq_zero l2
          simp [mOrc, h0']
      · rename_i hnd1
        rw [ite_neg' hnd1] at hoB
        have lB := hoB.length
        obtain rfl := List.eq_nil_of_length_eq_zero lB
        trivial
    · obtain ⟨r5, -⟩ := hoC
      refine ⟨rfl, taken_eq (by omega) hv.g434, fun _ => ⟨?_, ?_⟩, trivial⟩
      · show [σ (.n (val% «main» "s56#2")), σ (.n (val% «main» "meta[6]")), σ (.n (val% «main» "written")), σ (.n (val% «main» "lx_table")), σ (.n (val% «main» "cover")), σ (.n (val% «main» "lx_slots_g")), σ (.n (val% «main» "lean_sphincs_table")), σ (.n (val% «main» "sp_cover")),
          σ (.n (val% «main» "lean_sphincs_slots_g")), σ (.n (val% «main» "child_carried")), σ (.n (val% «main» "da_digests")), σ (.n (val% «main» "fs_seed[0]")), σ (.n (val% «main» "fs_seed[1]")), σ (.n (val% «main» "child_pi")), σ (.n (val% «main» "g_squares")),
          σ (.n (val% «main» "child_fresh"))] = _
        rw [hv.g435, hO (by decide), hO (by decide), hO (by decide), hO (by decide), hv.v40,
          hO (by decide), hv.v67, hv.v41, hO (by decide), hO (by decide), hO (by decide),
          hO (by decide), hO (by decide), hO (by decide), hO (by decide)]
        rfl
      · rw [(r5 (by assumption)).1]; rfl
    · split
      · rename_i hnc0
        rw [ite_pos' hnc0] at hoD
        obtain rfl := List.eq_nil_of_length_eq_zero hoD.length
        trivial
      · rename_i hnc0
        rw [ite_neg' hnc0] at hoD
        have lD0 := hoD.length
        obtain ⟨g1, td, rfl, lD1⟩ := exists_of_length_succ lD0
        obtain rfl := List.eq_nil_of_length_eq_zero lD1
        obtain ⟨r6, -⟩ := hoD
        refine ⟨rfl, rfl, fun _ => ⟨?_, ?_⟩, trivial⟩
        · show [σ (.n (val% «main» "meta[6]")), σ (.n (val% «main» "child_pi")), σ (.n (val% «main» "child_fresh")), σ (.n (val% «main» "child_carried")), σ (.n (val% «main» "defer_stmt")), σ (.n (val% «main» "s63.e.s0#1"))] = _
          rw [hO (by decide), hO (by decide), hO (by decide), hO (by decide), hO (by decide),
            hv.v465]; rfl
        · rw [(r6 rfl).1]; rfl
    · obtain ⟨r7, -⟩ := hoE
      refine ⟨rfl, rfl, fun _ => ⟨?_, ?_⟩, trivial⟩
      · show [σ (.n (val% «main» "fs_seed[0]")), σ (.n (val% «main» "fs_seed[1]")), σ (.n (val% «main» "xd_0")), σ (.n (val% «main» "xd_1")), σ (.n (val% «main» "sd_0")), σ (.n (val% «main» "sd_1")), σ (.n (val% «main» "own_0~2")), σ (.n (val% «main» "own_0~3")),
          σ (.n (val% «main» "defer_stmt"))] = _
        rw [hO (by decide), hO (by decide), hO (by decide), hO (by decide), hO (by decide),
          hO (by decide), hv.r476, hv.r477, hO (by decide)]; rfl
      · rw [(r7 rfl).1]; show [σ (.n (val% «main» "own_0")), σ (.n (val% «main» "own_1"))] = _
        rw [hO (by decide), hO (by decide)]; rfl
  -- the placed relation
  have hbase : fp + fs "main" + (mSizes d).sum + (fs "exponent_tables" + lit% B1.expTabN) =
      etB fs (mK0 d fs fp) + lit% B1.expTabN := by simp only [etB, mK0]; omega
  have hlins : B1.Main.MemL rd (B1.Kid.lins (mKids m Lmain)) := by
    intro q hq
    obtain ⟨k, hk, hq⟩ := List.mem_flatMap.mp hq
    rw [mKids_lin m Lmain k hk] at hq
    rcases List.mem_append.mp hq with hq | hq
    · exact hLo q hq
    · exact hLe q hq
  have h := relAtInWT_of_walk (P := coreProgram) (fs := fs) (cert := cert) (σ := σ) (rd := rd)
    (R := fun i => i < 2) (D := fun _ => False) (fp := fp) (N := fs "exponent_tables" + lit% B1.expTabN + Nk)
    (args := []) (rets := [])
    (Dk := fun i => ((fun _ => False) i ∨ ((⟨"exponent_tables", [], [.n (val% «main» "g_squares")], true⟩ : Call).taken
      = true ∧ (etB fs (mK0 d fs fp) ≤ i ∧ i < etB fs (mK0 d fs fp) + lit% B1.expTabN))) ∨
      outRegion (mKids m Lmain) ([a1, a2, a3, a4, a5, a6] ++ oB ++ [c5] ++ oD ++ [e1]) i)
    coreProgram_wf find_main (Or.inl main_loop) rfl hw rfl hev (by rw [hal]; exact hbuf)
    (fun q hq => by
      rw [addrs_append, addrs_append, addrs_inK, addrs_append, addrs_append, addrs_inK, pad1, pad2,
        pad3, pad4, pad5] at hq
      obtain ⟨e1', e2a, e2b, e3', e4a, e4b, e5'⟩ := mBlocks_addrs
      have e2' : (if m.nd = 1 then mDa else mDaZ).filterMap Main.Stmt.addrS = [] := by
        split
        · exact e2a
        · exact e2b
      have e4' : (if m.nc = 0 then mLeaf else mAgg).filterMap Main.Stmt.addrS = [] := by
        split
        · exact e4a
        · exact e4b
      rw [e1', e2', e3', e4', e5'] at hq
      simp at hq)
    ((fun _ => True) :: Ts rd) ?_ ?_ (fun i hi => hi.elim)
  · rw [hal] at h
    obtain ⟨t, ht, ks, rfl, hkT⟩ := h
    rw [hcalls] at hkT
    exact ⟨_, ht, σ, _, ks, rfl, hv, hkT, hes ▸ hcalls, rfl⟩
  · rw [hcalls, hal]
    refine ⟨fs "exponent_tables" + lit% B1.expTabN, Nk, fun _ => False,
      fun i => etB fs (mK0 d fs fp) ≤ i ∧ i < etB fs (mK0 d fs fp) + lit% B1.expTabN, rfl, fun i hi => hi.elim, ?_, ?_⟩
    · show RelAtInT coreProgram fs cert rd (fun _ => False)
        (fun i => etB fs (mK0 d fs fp) ≤ i ∧ i < etB fs (mK0 d fs fp) + lit% B1.expTabN) (mK0 d fs fp)
        (fs "exponent_tables" + lit% B1.expTabN) "exponent_tables" [] [σ (.n (val% «main» "g_squares"))] fun _ => True
      rw [o49]
      exact (et_at fs cert hExp).relAtInT
    · rw [hbase]
      refine hKids rd σ _ _ _ hCM hlow hLk hlins (regionsOk_of fun k hk _ i hi => ?_)
      rw [mKids_lin m Lmain k hk] at hi
      obtain ⟨q, hq, h1', h2'⟩ := hi
      rcases List.mem_append.mp hq with hq | hq
      · exact Or.inl (Or.inr (bufL_region _ _ _ hfit i ⟨q, hq, h1', h2'⟩ |> fun ⟨q', hq', h3, h4⟩ =>
          Or.inl ⟨q', hq', h3, h4⟩))
      · refine Or.inr (Or.inr ⟨rfl, ?_⟩)
        simp only [etL, List.mem_cons, List.not_mem_nil, or_false] at hq
        subst hq; simp [length_expTabAllWords] at h1' h2' ⊢; omega
  · intro A hA
    rw [loadAddrs_append, loadAddrs_append, loadAddrs_inK, loadAddrs_append, loadAddrs_append,
      loadAddrs_inK, B1.loadAddrs_straight σ _ s1, B1.loadAddrs_straight σ _ sDa,
      B1.loadAddrs_straight σ _ s3, B1.loadAddrs_straight σ _ sBr, B1.loadAddrs_straight σ _ s6] at hA
    rw [hal]
    obtain ⟨l1, l2, l2', l3, l4, l5, l6⟩ := mBlocks_loads
    have lDa : (if m.nd = 1 then mDa else mDaZ).filterMap B1.Stmt.loadS = [(.n (val% «main» "own_da"), 0), (.n (val% «main» "own_da"), 1)] := by
      split
      · exact l2
      · exact l2'
    have hpk : d.pick ≤ d.nc := hb.pick
    have hmn : m.nc = d.nc := rfl
    have hmp : m.pick = d.pick := rfl
    have h336 : σ (.n (val% «main» "own_da")) = gen ^ ((Memory.bases b0 (mSizes d)).getD 4 0 + 2 * m.nc) := by
      rw [hv.v387, pow_add]; rfl
    have h401 : σ (.n (val% «main» "da")) = gen ^ ((Memory.bases b0 (mSizes d)).getD 4 0 + 2 * m.pick) := by
      rw [hv.v448, pow_add]; rfl
    simp only [List.mem_append] at hA
    rcases hA with h | h | h | h | h
    · rw [l1] at h
      simp only [List.map_map, List.mem_map, List.mem_range, Function.comp] at h
      obtain ⟨v, hv', rfl⟩ := h
      exact ⟨_, by rw [o68, limb0_gen_pow_mul], Or.inl (hown 3 (by norm_num) v (by simp [mSizes]; omega))⟩
    · rw [lDa] at h
      simp only [List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false] at h
      rcases h with rfl | rfl
      · exact ⟨_, by rw [h336, limb0_gen_pow_mul, Nat.add_assoc],
          Or.inl (hown 4 (by norm_num) (2 * m.nc + 0) (by simp [mSizes]; omega))⟩
      · exact ⟨_, by rw [h336, limb0_gen_pow_mul, Nat.add_assoc],
          Or.inl (hown 4 (by norm_num) (2 * m.nc + 1) (by simp [mSizes]; omega))⟩
    · rw [l3] at h
      simp only [List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false] at h
      rcases h with rfl | rfl
      · exact ⟨_, by rw [o380, limb0_gen_pow_mul], Or.inl (hown 8 (by norm_num) 0 (by simp [mSizes]))⟩
      · have h385 : σ (.n (val% «main» "s57#0")) = gen ^ ((Memory.bases b0 (mSizes d)).getD 8 0 + m.nc) := by
          rw [hv.v436, pow_add]; rfl
        refine ⟨_, by rw [h385, limb0_gen_pow_mul]; rfl,
          Or.inl (hown 8 (by norm_num) m.nc (by simp [mSizes]; rfl))⟩
    · split at h
      · rw [l4] at h
        simp only [List.map_map, List.mem_map, List.mem_range, Function.comp] at h
        obtain ⟨k, hk, rfl⟩ := h
        exact ⟨_, by rw [o402, limb0_gen_pow_mul], Or.inl (hown 9 (by norm_num) k (by simp [mSizes]; omega))⟩
      · rw [l5] at h; simp at h
    · rw [l6] at h
      simp only [List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false] at h
      rcases h with rfl | rfl | rfl | rfl
      · exact ⟨_, by rw [h401, limb0_gen_pow_mul, Nat.add_assoc],
          Or.inl (hown 4 (by norm_num) (2 * m.pick + 0) (by simp [mSizes]; omega))⟩
      · exact ⟨_, by rw [h401, limb0_gen_pow_mul, Nat.add_assoc],
          Or.inl (hown 4 (by norm_num) (2 * m.pick + 1) (by simp [mSizes]; omega))⟩
      · refine ⟨0, ?_, Or.inr (Or.inl (by norm_num))⟩
        rw [hv.v480, ← pow_zero gen, limb0_gen_pow_mul]
      · refine ⟨1, ?_, Or.inr (Or.inl (by norm_num))⟩
        rw [hv.v484, ← pow_one gen, limb0_gen_pow_mul]

/-- **`main`'s words**: its frame, its buffers, `exponent_tables`' frame and tables, its other
callees' bounds (`kidsBoundL`). -/
def mainB (fs : String → ℕ) (d : MainData) (ks : List Kid) (Bs : List ℕ) : ℕ :=
  fs "main" + (mSizes d).sum + (fs "exponent_tables" + lit% B1.expTabN + kidsBoundL fs ks Bs)

end
end LeanVM.Guest.B1.Main
