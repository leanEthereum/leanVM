/-
  LeanVM.Guest.B1.VsC.Os.LeftNode

  `open_stacked`'s node placed, from its callees: `OpenStackedCompleteA` reduced to `KidsAtF` over
  the body's calls and the post on its callees' trees.
-/

module

public import LeanVM.Guest.B1.VsC.Os.LeftHeap
public import LeanVM.Guest.B1.VsC.Os.LeftPre
public import LeanVM.Guest.B1.VsC.Os.CHonMem
public import LeanVM.Guest.B1.VsC.Os.CHonStaticAll
public import LeanVM.Guest.B1.VsC.SlowA
public import LeanVM.Guest.Complete.ComposeRd
public import LeanVM.Guest.Memory.Restrict
public import LeanVM.Guest.B1.Whir.DataAll
public import LeanVM.Guest.B1.Whir.Names
public import LeanVM.Guest.B1.VsC.Os.Left

/-!
# `open_stacked`'s node, from its callees

`callAtA_nodeRd` on `open_stacked__L{m}` at the rate `r`, everything but its callees discharged:

* the function is the template (`osData_all`), not a loop helper;
* its own words `osWords`: the buffers' honest words `H.own` at `bases c (osSizesL …)`, but
  `query_win_ptrs`' words `wq`, which the callees' placement fixes (the windows' frames);
* `σ0`: the body's honest valuation on one memory holding the words (when none does, every
  obligation on a memory is void); on every memory, its valuation (`osHonestA_valC`, at the callee
  relation `osCmin` of the named callees' meanings), its walk, its events, its allocations and
  placement (`osArm_nodeAt`), its calls agreeing with `σ0`'s (`callsAgree_flatD`);
* its loads in the region (`OsLoadsIn` on the memory restricted to the cursor's words, the window
  tables and the buffers, `loadAddrs_flatD`), no heap hint (`noHeap_all`).

`OsKidsAt`: what is left at a position, the callees (`KidsAtF` over the body's calls from the end
of its buffers) and the node's post from its callees' trees, given `σ0` and every memory's
valuation agreeing with it on the calls. `osCallAtA_of_kids` closes the node; `OsKidsHyp` states
`OsKidsAt` at some honest data of every accepting run, and `openStackedCompleteA_of_kids` gives
`OpenStackedCompleteA` from it.
-/

namespace LeanVM.Guest.B1.VsC

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Memory LeanVM.Guest.B1
open LeanVM.Guest.Complete LeanVM.Guest.B1.Whir LeanVM.Guest.Value LeanVM.Protocol
open LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

/-! ## The body on a memory, at the callees' meanings -/

/-- The callee relation of the named callees' meanings, on loads the caller's words fix. -/
def osCmin (c : OsCfg) (b : ℕ) (own : List (List E)) (cur tabs : E) (xs : List E) (rd : Reader) : CallRel :=
  fun f a r => ∀ K, osKindOf f = some K → K.Pre rd a r ∧ OsFixedA c b own cur tabs xs K a

/-- **The body at a valuation on a memory**: the arguments below `11`, every statement holding at
the callees' meanings, its outcome, its loads fixed, its window hints exact. -/
def OsBodyAt (c : OsCfg) (b : ℕ) (args : List E) (cur tabs : E) (xs : List E) (tgt inn res : E)
    (own : List (List E)) (D : ℕ → OsLvData) (rd : Reader) (σ : Val) : Prop :=
  AgreeBelow 11 (Val.ofArgs args) σ ∧ AllOk (osCmin c b own cur tabs xs rd) rd σ (osBodyA c) ∧
    OsOutA c b tabs tgt inn res (cur * gen ^ xs.length) own D σ ∧ OsLoadsIn c b own cur tabs xs σ ∧
    WinEx (osBodyA c) σ

/-- **The body's valuation on a memory**, at the callees' meanings. -/
theorem osHonestA_valC {c : OsCfg} {args : List E} {cur tabs : E} {xs : List E} {tgt inn res : E}
    {pt pt1 : List E} (H : OsHonestA c args cur tabs xs tgt inn res pt pt1) (b : ℕ) :
    ∃ CV : List (List E), ∀ rd, LowDef 11 rd → ReadsAt rd cur xs → WinTabs rd tabs → OsMemA rd c b H.own →
      ∃ σ, OsBodyAt c b args cur tabs xs tgt inn res H.own H.D rd σ ∧
        ((osBodyA c).filterMap Stmt.callVarsS).map (·.map σ) = CV := by
  obtain ⟨CV, hb⟩ := H.body b
  refine ⟨CV, fun rd hl hr hw hm ↦ ?_⟩
  obtain ⟨kEnd, f, hf⟩ := hb rd hl
  have hC : OsHA (osCmin c b H.own cur tabs xs rd) rd c b H.own cur tabs xs :=
    ⟨hr, hw, hm, fun _ K hK _ _ hp hfx K' hK' => by rw [hK] at hK'; cases hK'; exact ⟨hp, hfx⟩,
      fun _ _ _ hn K hK => by rw [hn] at hK; cases hK⟩
  obtain ⟨hok, ho, hcv, hld, hwx⟩ := hf _ rd hC (fun _ _ ↦ rfl)
    (fill (Val.ofArgs args) 11 kEnd f) (agree_fill _ _ _ _) (range_fill _ _ _ _)
  exact ⟨_, ⟨agree_fill _ _ _ _, hok, ho, hld, hwx⟩, hcv⟩

/-! ## The own words -/

/-- The buffers' words: `own`, but `query_win_ptrs`' `wq`. -/
def osOwnW (own : List (List E)) (wq : List E) : List (List E) := own.set osIxQbpA wq

/-- **`open_stacked`'s own words**: buffer `j`'s at its base from `b`. -/
def osWords (c : OsCfg) (b : ℕ) (own : List (List E)) (wq : List E) : Words :=
  (List.range (osSizesL c).length).map fun j => ((bases b (osSizesL c)).getD j 0, (osOwnW own wq).getD j [])

/-- `open_stacked`'s memory facts: the cursor's words and the window tables. -/
def osPre (ic it : ℕ) (xs : List E) (rd : Reader) : Prop :=
  ReadsAt rd (ofK (addressOfIndex ic)) xs ∧ WinTabs rd (ofK (addressOfIndex it))

theorem osBases_getD_in : ∀ (b : ℕ) (L : List ℕ) (j : ℕ), j < L.length →
    b ≤ (bases b L).getD j 0 ∧ (bases b L).getD j 0 + L.getD j 0 ≤ b + L.sum
  | _, [], _, h => absurd h (by simp)
  | b, s :: L, 0, _ => by simp [bases]
  | b, s :: L, j + 1, h => by
    have := osBases_getD_in (b + s) L j (by simpa using h)
    simp only [bases, List.getD_cons_succ, List.sum_cons]
    omega

theorem osBases_getD_lt : ∀ (b : ℕ) (L : List ℕ) (j j' : ℕ), j < j' → j' < L.length →
    (bases b L).getD j 0 + L.getD j 0 ≤ (bases b L).getD j' 0
  | _, [], _, _, _, h => absurd h (by simp)
  | _, _ :: _, _, 0, hj, _ => absurd hj (Nat.not_lt_zero _)
  | b, s :: L, 0, j' + 1, _, h => by
    have := (osBases_getD_in (b + s) L j' (by simpa using h)).1
    simp only [bases, List.getD_cons_succ, List.getD_cons_zero]
    omega
  | b, s :: L, j + 1, j' + 1, hj, h => by
    have := osBases_getD_lt (b + s) L j j' (by omega) (by simpa using h)
    simpa only [bases, List.getD_cons_succ] using this

theorem mem_zip_bases {b : ℕ} {L : List ℕ} {j : ℕ} (hj : j < L.length) :
    (L.getD j 0, (bases b L).getD j 0) ∈ L.zip (bases b L) := by
  have hl : (bases b L).length = L.length := length_bases
  have hz : j < (L.zip (bases b L)).length := by simp [hl, hj]
  have h := List.getElem_mem hz
  rw [List.getElem_zip] at h
  rwa [List.getD_eq_getElem _ _ hj, List.getD_eq_getElem _ _ (hl ▸ hj)]

theorem forall₂_getD {own : List (List E)} {L : List ℕ} (h : List.Forall₂ (fun w s ↦ w.length = s) own L) :
    ∀ j, (own.getD j []).length = L.getD j 0 := by
  induction h with
  | nil => intro j; simp
  | cons hab _ ih =>
    intro j
    cases j with
    | zero => simpa using hab
    | succ j => simpa using ih j

section Words

variable {m ri : ℕ} (hm : m < 15) (hri : ri < 4)
include hm hri

theorem osWords_len {own : List (List E)} {wq : List E}
    (hown : List.Forall₂ (fun w s ↦ w.length = s) own (osSizesL (osCfgR m ri)))
    (hwq : wq.length = osPosTotal (osCfgR m ri)) {j : ℕ} (hj : j < (osSizesL (osCfgR m ri)).length) :
    ((osOwnW own wq).getD j []).length = (osSizesL (osCfgR m ri)).getD j 0 := by
  have hS := honStatic_all m ri hm hri
  have hol : own.length = (osSizesL (osCfgR m ri)).length := hown.length_eq
  by_cases h11 : j = osIxQbpA
  · subst h11
    rw [osOwnW, List.getD_eq_getElem?_getD, List.getElem?_set_self (by rw [hol, hS.len]; simp only [osIxQbpA]; omega),
      Option.getD_some, hwq, hS.head (by decide)]
    rfl
  · rw [osOwnW, List.getD_eq_getElem?_getD, List.getElem?_set_ne (Ne.symm h11), ← List.getD_eq_getElem?_getD]
    exact forall₂_getD hown j

theorem osWords_in {own : List (List E)} {wq : List E}
    (hown : List.Forall₂ (fun w s ↦ w.length = s) own (osSizesL (osCfgR m ri)))
    (hwq : wq.length = osPosTotal (osCfgR m ri)) (lo hi b : ℕ) :
    WordsInA (osWords (osCfgR m ri) b own wq) lo hi b (b + (osSizesL (osCfgR m ri)).sum) := by
  refine ⟨fun q hq => ?_, ?_⟩
  · obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hq
    rw [List.mem_range] at hj
    have h1 := osBases_getD_in b _ j hj
    dsimp only
    rw [osWords_len hm hri hown hwq hj]
    exact Or.inr h1
  · refine List.pairwise_map.mpr ((List.pairwise_lt_range (n := _)).imp_of_mem fun {j j'} hj hj' hlt => ?_)
    rw [List.mem_range] at hj hj'
    dsimp only
    rw [osWords_len hm hri hown hwq hj, osWords_len hm hri hown hwq hj']
    exact Or.inl (osBases_getD_lt b _ j j' hlt hj')

end Words

theorem osOwnW_getD {own : List (List E)} {wq : List E} {j : ℕ} (hne : j ≠ osIxQbpA) :
    (osOwnW own wq).getD j [] = own.getD j [] := by
  rw [osOwnW, List.getD_eq_getElem?_getD, List.getElem?_set_ne (Ne.symm hne), ← List.getD_eq_getElem?_getD]

theorem osWords_mem {c : OsCfg} {own : List (List E)} {wq : List E} {b : ℕ} {rd : Reader}
    (h : HoldsWords rd (osWords c b own wq)) : OsMemA rd c b own := by
  intro j hj hne
  have h1 : ReadsAt rd (ofK (addressOfIndex ((bases b (osSizesL c)).getD j 0))) ((osOwnW own wq).getD j []) :=
    h ((bases b (osSizesL c)).getD j 0, (osOwnW own wq).getD j []) (List.mem_map.mpr ⟨j, List.mem_range.mpr hj, rfl⟩)
  rw [osOwnW_getD hne] at h1
  exact h1

/-! ## Restricted memories -/

theorem ptr_addr (a k : ℕ) : (ofK (addressOfIndex a)).limb 0 * addressOfIndex k = addressOfIndex (a + k) := by
  simp [Parameters.addressOfIndex, pow_add]

theorem readsAt_restrict' {rd : Reader} {S : ℕ → Prop} {b : ℕ} {xs : List E}
    (h : ReadsAt rd (ofK (addressOfIndex b)) xs) (hS : ∀ k < xs.length, S (b + k)) :
    ReadsAt (restrict rd S) (ofK (addressOfIndex b)) xs :=
  fun k hk => loadHolds_restrict (h k hk) ⟨b + k, ptr_addr b k, hS k hk⟩

theorem winTabs_restrict {rd : Reader} {S : ℕ → Prop} {b : ℕ}
    (h : WinTabs rd (ofK (addressOfIndex b))) (hS : ∀ n < 2 ^ winTabBits, S (b + n)) :
    WinTabs (restrict rd S) (ofK (addressOfIndex b)) :=
  fun n hn => loadHolds_restrict (h n hn) ⟨b + n, ptr_addr b n, hS n hn⟩

/-- The cells the body's loads may read: the cursor's words, the window tables and the buffers but
`query_win_ptrs`. -/
def osLoadCells (c : OsCfg) (b ic it : ℕ) (xs : List E) (i : ℕ) : Prop :=
  (∃ j < xs.length, i = ic + j) ∨ (∃ n < 2 ^ winTabBits, i = it + n) ∨
    ∃ j < (osSizesL c).length, (bases b (osSizesL c)).getD j 0 ≤ i ∧
      i < (bases b (osSizesL c)).getD j 0 + (osSizesL c).getD j 0

/-- **The body's loads read the cursor's words, the tables and the buffers.** -/
theorem osLoads_cells {m ri : ℕ} (hm : m < 15) {own : List (List E)}
    (hown : List.Forall₂ (fun w s ↦ w.length = s) own (osSizesL (osCfgR m ri))) {b ic it : ℕ}
    {xs : List E} {σ : Val} (hld : OsLoadsIn (osCfgR m ri) b own (ofK (addressOfIndex ic)) (ofK (addressOfIndex it)) xs σ)
    {rd : Reader} (hp : osPre ic it xs rd) (hmem : OsMemA rd (osCfgR m ri) b own) :
    ∀ A ∈ loadAddrs σ ((osBodyA (osCfgR m ri)).flatMap (fdEvs σ)), ∃ i, A = addressOfIndex i ∧
      osLoadCells (osCfgR m ri) b ic it xs i := by
  have hf := flatBody_all m hm
  rw [osBodyA_rate m ri] at hf
  have h1 : (osBodyA (osCfgR m ri)).all Stmt.flatD = true := by
    simp only [FlatBody, List.all_eq_true, Bool.and_eq_true] at hf
    exact List.all_eq_true.mpr fun s hs ↦ (hf s hs).1
  intro A hA
  rw [loadAddrs_flatD σ _ h1] at hA
  obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hA
  obtain ⟨v, hv⟩ := hld q hq
  set S := osLoadCells (osCfgR m ri) b ic it xs
  have hr : ReadsAt (restrict rd S) (ofK (addressOfIndex ic)) xs :=
    readsAt_restrict' hp.1 fun k hk => Or.inl ⟨k, hk, rfl⟩
  have hw : WinTabs (restrict rd S) (ofK (addressOfIndex it)) :=
    winTabs_restrict hp.2 fun n hn => Or.inr (Or.inl ⟨n, hn, rfl⟩)
  have hm' : OsMemA (restrict rd S) (osCfgR m ri) b own := fun j hj hne =>
    readsAt_restrict' (hmem j hj hne) fun k hk => by
      have hl : (osOwnA own j).length = (osSizesL (osCfgR m ri)).getD j 0 := forall₂_getD hown j
      exact Or.inr (Or.inr ⟨j, hj, by omega, by omega⟩)
  exact restrict_supp (hv _ hr hw hm').2

/-! ## The node -/

theorem openName_m {m : ℕ} (hm : m < ligNSizes) :
    openName (minOpenLog + m) = "open_stacked__L" ++ natStr m := by
  rw [openName, openNames, natStr_eq, Nat.add_sub_cancel_left,
    List.getD_eq_getElem _ _ (by simpa using hm)]
  simp

/-- **`open_stacked__L{m}` is its template**, not a loop helper. -/
theorem os_fn {m : ℕ} (hm : m < 15) : ∃ fn : Fn, coreProgram.find? (openName (minOpenLog + m)) = some fn ∧
    fn.params = osParams 11 ∧ fn.body = osBody (osCfg m) ∧ coreProgram.loop (openName (minOpenLog + m)) = false := by
  have hl : m < ligNSizes := by simp only [ligNSizes]; omega
  have h := osData_all m hl
  unfold OsData at h
  obtain ⟨fn, hf, hps, hb⟩ := h
  rw [← openName_m hl] at hf
  refine ⟨fn, hf, hps, hb, ?_⟩
  rw [Program.loop_of_find? hf]
  obtain ⟨v, vs, hv⟩ : ∃ v vs, osBodyRet (osCfgR m 0) = v :: vs := ⟨_, _, rfl⟩
  unfold Fn.loop
  rw [hb, osBody_rate m 0, osBody_eq, List.reverse_append, hv]
  rfl

variable {fs : String → ℕ} {al : String → Bool} {cert : String → V → ℕ}

variable (fs al cert) in
/-- **What is left of `open_stacked`'s node at a position** `(fp, c)`, at the arm `m`, the rate `r`
and the honest data `own`, `D`: some words `wq` of `query_win_ptrs` such that, at the body's
valuation `σ0` on a memory holding the node's words (and every memory's valuation agreeing with
it on the calls), the callees complete from the end of the buffers (`KidsAtF`), their words held
giving the node's, and the node's post holds of its callees' trees. -/
def OsKidsAt (k m r : ℕ) (args : List E) (ic it : ℕ) (xs : List E) (tgt inn res : E) (own : List (List E))
    (D : ℕ → OsLvData) (R : ℕ → Prop) (Post : Reader → Tree → Prop) (fp c : ℕ) : Prop :=
  ∃ wq : List E, wq.length = osPosTotal (osCfgR m (r - 1)) ∧
  ∀ (σ0 : Val) (rd0 : Reader), LowDef k rd0 → osPre ic it xs rd0 →
    HoldsWords rd0 (osWords (osCfgR m (r - 1)) c own wq) →
    OsBodyAt (osCfgR m (r - 1)) c args (ofK (addressOfIndex ic)) (ofK (addressOfIndex it)) xs tgt inn res
      own D rd0 σ0 →
    (∀ rd, LowDef k rd → osPre ic it xs rd → HoldsWords rd (osWords (osCfgR m (r - 1)) c own wq) →
      ∃ σ, OsBodyAt (osCfgR m (r - 1)) c args (ofK (addressOfIndex ic)) (ofK (addressOfIndex it)) xs tgt inn res
        own D rd σ ∧ VsC.CallsAgree σ0 σ (calls ((osBodyA (osCfgR m (r - 1))).flatMap (fdEvs σ0)))) →
    ∃ (e : ℕ) (Qs : List (Reader → Tree → Prop)) (Oend : Reader → Prop) (Dend : ℕ → Prop),
      ((∀ f, fs f ≤ 2 ^ 16) → e ≤ c + 2 ^ 36) ∧
      KidsAtF fs al cert k σ0 (fun i => R i ∨ ownData cert fp c (openName (minOpenLog + m))
          (allocs σ0 ((osBodyA (osCfgR m (r - 1))).flatMap (fdEvs σ0)))
          ((osBodyA (osCfgR m (r - 1))).flatMap (fdEvs σ0)) i)
        (osPre ic it xs) (fun rd => HoldsWords rd (osWords (osCfgR m (r - 1)) c own wq)) (fun _ => False) Qs
        (calls ((osBodyA (osCfgR m (r - 1))).flatMap (fdEvs σ0)))
        (c + (allocs σ0 ((osBodyA (osCfgR m (r - 1))).flatMap (fdEvs σ0))).sum) e Oend Dend ∧
      (∀ rd, Oend rd → HoldsWords rd (osWords (osCfgR m (r - 1)) c own wq)) ∧
      ∀ rd σ ts, LowDef k rd → osPre ic it xs rd → Oend rd →
        OsBodyAt (osCfgR m (r - 1)) c args (ofK (addressOfIndex ic)) (ofK (addressOfIndex it)) xs tgt inn res
          own D rd σ →
        VsC.CallsAgree σ0 σ (calls ((osBodyA (osCfgR m (r - 1))).flatMap (fdEvs σ0))) →
        Tree.KidsValid coreProgram rd σ (calls ((osBodyA (osCfgR m (r - 1))).flatMap (fdEvs σ0))) ts →
        KidsPost rd Qs (calls ((osBodyA (osCfgR m (r - 1))).flatMap (fdEvs σ0))) ts →
        Post rd (.node (openName (minOpenLog + m)) σ (allocs σ0 ((osBodyA (osCfgR m (r - 1))).flatMap (fdEvs σ0)))
          ts)

set_option maxHeartbeats 800000 in
set_option linter.constructorNameAsVariable false in
/-- **`open_stacked__L{m}`'s node completes placed** from what is left at its position. -/
theorem osCallAtA_of_kids {k m r : ℕ} (hk : 11 ≤ k) (hm : m ≤ 14) (hr1 : 1 ≤ r) (hr4 : r ≤ 4) {args : List E}
    (hargs : args.length = 11) {ic it : ℕ} {xs : List E} {tgt inn res : E} {pt pt1 : List E}
    (H : OsHonestA (osCfgR m (r - 1)) args (ofK (addressOfIndex ic)) (ofK (addressOfIndex it)) xs tgt inn res
      pt pt1)
    {R : ℕ → Prop} (hRx : ∀ i < xs.length, R (ic + i)) (hRt : ∀ n < 2 ^ winTabBits, R (it + n))
    {Post : Reader → Tree → Prop} {fp c : ℕ} (hfc : fp + fs (openName (minOpenLog + m)) ≤ c)
    (hkids : OsKidsAt fs al cert k m r args ic it xs tgt inn res H.own H.D R Post fp c) :
    ∃ e, CallAtA fs al cert k (openName (minOpenLog + m)) args
      [tgt, ofK (addressOfIndex ((bases c (osSizesL (osCfgR m (r - 1)))).getD (osIxPtA (osCfgR m (r - 1))) 0)),
        ofK (addressOfIndex ((bases c (osSizesL (osCfgR m (r - 1)))).getD (osIxPt1A (osCfgR m (r - 1))) 0)),
        inn, res, ofK (addressOfIndex (ic + xs.length))] R
      (fun i => ((bases c (osSizesL (osCfgR m (r - 1)))).getD (osIxPtA (osCfgR m (r - 1))) 0 ≤ i ∧
          i < (bases c (osSizesL (osCfgR m (r - 1)))).getD (osIxPtA (osCfgR m (r - 1))) 0 + pointCap) ∨
        ((bases c (osSizesL (osCfgR m (r - 1)))).getD (osIxPt1A (osCfgR m (r - 1))) 0 ≤ i ∧
          i < (bases c (osSizesL (osCfgR m (r - 1)))).getD (osIxPt1A (osCfgR m (r - 1))) 0 + pointCap))
      (fun rd => ReadsAt rd (ofK (addressOfIndex
          ((bases c (osSizesL (osCfgR m (r - 1)))).getD (osIxPtA (osCfgR m (r - 1))) 0))) pt ∧
        ReadsAt rd (ofK (addressOfIndex
          ((bases c (osSizesL (osCfgR m (r - 1)))).getD (osIxPt1A (osCfgR m (r - 1))) 0))) pt1)
      (osPre ic it xs) Post (fs (openName (minOpenLog + m))) fp c e ∧
      (bases c (osSizesL (osCfgR m (r - 1)))).getD (osIxPtA (osCfgR m (r - 1))) 0 + pointCap ≤ e ∧ (bases c (osSizesL (osCfgR m (r - 1)))).getD (osIxPt1A (osCfgR m (r - 1))) 0 + pointCap ≤ e ∧
      ((∀ f, fs f ≤ 2 ^ 16) → (osSizesL (osCfgR m (r - 1))).sum ≤ 2 ^ 30 → e ≤ c + 2 ^ 36) := by
  have hri : r - 1 < 4 := by omega
  have hm15 : m < 15 := by omega
  have hS := honStatic_all m (r - 1) hm15 hri
  obtain ⟨fn, hfind, hps, hbody, hlp⟩ := os_fn hm15
  obtain ⟨wq, hwq, hK⟩ := hkids
  have hWin := osWords_in hm15 hri H.own_len hwq (fp + 2) (fp + fs (openName (minOpenLog + m))) c
  have hlen := hS.len
  have hpt : osIxPtA (osCfgR m (r - 1)) < (osSizesL (osCfgR m (r - 1))).length ∧
      (osSizesL (osCfgR m (r - 1))).getD (osIxPtA (osCfgR m (r - 1))) 0 = pointCap := by
    refine ⟨by rw [hlen]; simp only [osIxPtA]; omega, ?_⟩
    have h1 := hS.fin (k := 1) (by omega)
    rw [show osIxPtA (osCfgR m (r - 1)) = 13 + (osCfgR m (r - 1)).yrLevel + 1 by simp only [osIxPtA]; omega, h1]
    rfl
  have hpt1 : osIxPt1A (osCfgR m (r - 1)) < (osSizesL (osCfgR m (r - 1))).length ∧
      (osSizesL (osCfgR m (r - 1))).getD (osIxPt1A (osCfgR m (r - 1))) 0 = pointCap := by
    refine ⟨by rw [hlen]; simp only [osIxPt1A]; omega, ?_⟩
    have h1 := hS.fin (k := 2) (by omega)
    rw [show osIxPt1A (osCfgR m (r - 1)) = 13 + (osCfgR m (r - 1)).yrLevel + 2 by simp only [osIxPt1A]; omega, h1]
    rfl
  have hout : ∀ rd, HoldsWords rd (osWords (osCfgR m (r - 1)) c H.own wq) →
      ReadsAt rd (ofK (addressOfIndex
          ((bases c (osSizesL (osCfgR m (r - 1)))).getD (osIxPtA (osCfgR m (r - 1))) 0))) pt ∧
        ReadsAt rd (ofK (addressOfIndex
          ((bases c (osSizesL (osCfgR m (r - 1)))).getD (osIxPt1A (osCfgR m (r - 1))) 0))) pt1 := by
    intro rd hw
    have hmem := osWords_mem hw
    refine ⟨?_, ?_⟩
    · have h1 := hmem (osIxPtA (osCfgR m (r - 1))) hpt.1 (by simp only [osIxPtA, osIxQbpA]; omega)
      rw [H.own_pt] at h1
      exact h1
    · have h1 := hmem (osIxPt1A (osCfgR m (r - 1))) hpt1.1 (by simp only [osIxPt1A, osIxQbpA]; omega)
      rw [H.own_pt1] at h1
      exact h1
  have hp0 := osBases_getD_in c _ _ hpt.1
  have hp1 := osBases_getD_in c _ _ hpt1.1
  rw [hpt.2] at hp0
  rw [hpt1.2] at hp1
  by_cases hex : ∃ rd0, LowDef k rd0 ∧ osPre ic it xs rd0 ∧ HoldsWords rd0 (osWords (osCfgR m (r - 1)) c H.own wq)
  swap
  · refine ⟨c + (osSizesL (osCfgR m (r - 1))).sum, ?_, hp0.2, hp1.2, fun _ hs => ?_⟩
    · exact ⟨_, hWin, by omega, hout, fun rd hl hw hp => absurd ⟨rd, hl, hp, hw⟩ hex⟩
    · have : (2 : ℕ) ^ 30 ≤ 2 ^ 36 := Nat.pow_le_pow_right (by norm_num) (by norm_num)
      omega
  obtain ⟨rd0, hl0, hp0', hw0⟩ := hex
  obtain ⟨CV, hval⟩ := osHonestA_valC H c
  obtain ⟨σ0, hb0, hcv0⟩ := hval rd0 (hl0.mono hk) hp0'.1 hp0'.2 (osWords_mem hw0)
  have hf := flatBody_all m hm15
  rw [osBodyA_rate m (r - 1)] at hf
  have hflat : (osBodyA (osCfgR m (r - 1))).all Stmt.flatD = true := by
    simp only [FlatBody, List.all_eq_true, Bool.and_eq_true] at hf
    exact List.all_eq_true.mpr fun s hs ↦ (hf s hs).1
  have hnh := noHeap_all m hm15
  rw [osBodyA_rate m (r - 1)] at hnh
  have hal0 := (osArm_nodeAt hm15 cert fp (openName (minOpenLog + m)) hb0.2.2.1).1
  have hmem : ∀ rd, LowDef k rd → osPre ic it xs rd → HoldsWords rd (osWords (osCfgR m (r - 1)) c H.own wq) →
      ∃ σ, OsBodyAt (osCfgR m (r - 1)) c args (ofK (addressOfIndex ic)) (ofK (addressOfIndex it)) xs tgt inn res
          H.own H.D rd σ ∧ VsC.CallsAgree σ0 σ (calls ((osBodyA (osCfgR m (r - 1))).flatMap (fdEvs σ0))) ∧
        (osBodyA (osCfgR m (r - 1))).flatMap (fdEvs σ) = (osBodyA (osCfgR m (r - 1))).flatMap (fdEvs σ0) := by
    intro rd hl hp hw
    obtain ⟨σ, hb, hcv⟩ := hval rd (hl.mono hk) hp.1 hp.2 (osWords_mem hw)
    have h0 : σ (.n osRate) = σ0 (.n osRate) := by
      show σ (.n 0) = σ0 (.n 0)
      rw [hb.1 0 (by omega), hb0.1 0 (by omega)]
    exact ⟨σ, hb, callsAgree_flatD hflat (hcv0.trans hcv.symm), osBody_evs_congr hm15 h0⟩
  obtain ⟨e, Qs, Oend, Dend, heB, hKF, hOW, hP⟩ := hK σ0 rd0 hl0 hp0' hw0 hb0
    (fun rd hl hp hw => (hmem rd hl hp hw).imp fun _ h => ⟨h.1, h.2.1⟩)
  have hce : c + (osSizesL (osCfgR m (r - 1))).sum ≤ e := by
    have h := by with_reducible exact (kidsAtF_words _ _ _ _ _ _ _ _ hKF).choose_spec.1
    rw [hal0] at h
    exact h
  refine ⟨e, callAtA_nodeRd (e := e) hlp hfc ?_, le_trans hp0.2 hce, le_trans hp1.2 hce, fun hF _ => heB hF⟩
  refine ⟨σ0, fn, (osBodyA (osCfgR m (r - 1))).flatMap (fdEvs σ0),
    osBodyRet (osCfgR m (r - 1)), osWords (osCfgR m (r - 1)) c H.own wq, Qs, Oend, Dend, hfind,
    ?_, ?_, ?_, fun rd h => hout rd (hOW rd h), ?_⟩
  · rw [hal0]; exact hWin
  · intro i hi
    left
    rw [hal0]
    left
    rcases hi with hi | hi
    · exact ⟨_, mem_zip_bases hpt.1, hi.1, by rw [hpt.2]; exact hi.2⟩
    · exact ⟨_, mem_zip_bases hpt1.1, hi.1, by rw [hpt1.2]; exact hi.2⟩
  · with_reducible exact hKF
  · intro rd hl hp hOe
    obtain ⟨σ, hb, hag, hes⟩ := hmem rd hl hp (hOW rd hOe)
    obtain ⟨hwk, hev⟩ := osBody_walk hm15 hb.2.1
    rw [hes] at hwk hev
    have hnd := osArm_nodeAt hm15 cert fp (openName (minOpenLog + m)) hb.2.2.1
    rw [hes] at hnd
    refine ⟨σ, ?_, by rw [hbody]; exact hwk, ?_, by rw [hal0]; exact hnd.1, by rw [hal0]; exact hnd.2, hag,
      fun A hA => ?_, fun A hA => ?_, hev, fun ts hkv hkp => ?_⟩
    · rw [hps]
      apply List.ext_getElem (by simp [osParams, hargs])
      intro i h1 h2
      simp only [osParams, List.map_map, List.getElem_map, List.getElem_range, Function.comp_apply]
      have hi : i < 11 := by simpa [osParams] using h1
      rw [hb.1 i hi]
      exact List.getD_eq_getElem _ _ h2
    · rw [hb.2.2.1.1, show ofK (addressOfIndex ic) * gen ^ xs.length = ofK (addressOfIndex (ic + xs.length)) from
        ptrAt_mul_gen ic xs.length]
      rfl
    · rw [← hes] at hA
      obtain ⟨i, hi, hc⟩ := osLoads_cells hm15 H.own_len hb.2.2.2.1 hp
        (osWords_mem (hOW rd hOe)) A hA
      refine ⟨i, hi, ?_⟩
      rcases hc with ⟨j, hj, rfl⟩ | ⟨n, hn, rfl⟩ | ⟨j, hj, h1, h2⟩
      · exact Or.inr (Or.inl (hRx j hj))
      · exact Or.inr (Or.inl (hRt n hn))
      · rw [hal0]
        exact Or.inl (Or.inl ⟨_, mem_zip_bases hj, h1, h2⟩)
    · rw [← hes] at hA
      exact (heapHintAddrs_flatD σ hnh A hA).elim
    · with_reducible exact hP rd σ ts hl hp hOe hb hag hkv hkp

/-! ## `OpenStackedCompleteA` from what is left -/

variable (fs al cert) in
/-- **What is left of `open_stacked`**: at every arm, rate and accepting run, at every position, some
honest data of the run with which the callees complete and the node's post holds (`OsKidsAt`,
the post `OpenStackedCompleteA`'s: the run's Merkle hints popped stream by stream, every node
exact). -/
def OsKidsHyp (k : ℕ) : Prop :=
  ∀ m, m ≤ 14 → ∀ (r : ℕ) (root : Digest) (fsv : List E) (target : E) (ic it : ℕ) (xs : List E)
    (os : List (List Opening)) (w : WhirEnd) (s' : Fs) (roots' : List (Digest × ℕ × ℕ))
    (qs : List (ℕ × List ℕ)) (R : ℕ → Prop),
    1 ≤ r → r ≤ 4 → fsv.length = 5 → (∃ sp : Sponge, (⟨fsv, []⟩ : Fs).Carries sp) →
    RunsWith (whirOpen (minOpenLog + m) r target) ⟨fsv, []⟩ xs os [(root, stackShape (minOpenLog + m) r)]
      w s' roots' →
    OpenRunQueries (minOpenLog + m) r root target ⟨fsv, []⟩ xs os qs →
    (∀ i < xs.length, R (ic + i)) → (∀ n < 2 ^ winTabBits, R (it + n)) →
    ∀ fp c, fp + fs (openName (minOpenLog + m)) ≤ c →
      ∃ H : OsHonestA (osCfgR m (r - 1))
          (rateSel r :: fsv ++ [target, (digestHalves root).1, (digestHalves root).2, ofK (addressOfIndex ic),
            ofK (addressOfIndex it)])
          (ofK (addressOfIndex ic)) (ofK (addressOfIndex it)) xs w.target w.inner w.residual
          (w.point ++ List.replicate (pointCap - (minOpenLog + m)) 0)
          (w.point.map (1 + ·) ++ List.replicate (pointCap - (minOpenLog + m)) 1),
        OsKidsAt fs al cert k m r
          (rateSel r :: fsv ++ [target, (digestHalves root).1, (digestHalves root).2, ofK (addressOfIndex ic),
            ofK (addressOfIndex it)])
          ic it xs w.target w.inner w.residual H.own H.D R
          (fun rd t => SameStreams (t.pops coreProgram rd) (Prover.merkleHints true qs os) ∧
            t.Every (ExactAt coreProgram rd)) fp c

/-- **`open_stacked` completes placed at every arm** from what is left of it. -/
theorem openStackedCompleteA_of_kids {k : ℕ} (hk : 11 ≤ k) (h : OsKidsHyp fs al cert k) :
    ∀ m, m ≤ 14 → OpenStackedCompleteA fs al cert k m := by
  intro m hm r root fsv target ic it xs os w s' roots' qs R hr1 hr4 hfl hcar hrun hq hRx hRt fp c hfc
  obtain ⟨H, hK⟩ := h m hm r root fsv target ic it xs os w s' roots' qs R hr1 hr4 hfl hcar hrun hq hRx hRt fp c hfc
  obtain ⟨e, he, -⟩ := osCallAtA_of_kids hk hm hr1 hr4 (by simp [hfl]) H hRx hRt hfc hK
  exact ⟨_, _, e, he⟩

/-- **`OsLeftC` from what is left of `open_stacked`.** -/
theorem osLeftC_of_kids {al : String → Bool} {k : ℕ} (hk : 11 ≤ k) (h : OsKidsHyp B2C.fs al B2C.cert k) :
    OsLeftC al k :=
  fun _ => openStackedCompleteA_of_kids hk h


end
end LeanVM.Guest.B1.VsC
