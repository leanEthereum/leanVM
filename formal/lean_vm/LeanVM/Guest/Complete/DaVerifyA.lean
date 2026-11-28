module

public import LeanVM.Guest.Complete.DaBlobA
import LeanVM.Guest.CoreRef
import LeanVM.Guest.ValRef
import LeanVM.Guest.Data.ValNames.«da_verify_blob»
import LeanVM.Guest.Data.ValNames.«da_verify_loop0»

/-!
# A blob's check and the blob loop, placed

* `blob_callAtA`: `da_verify_blob` at frame `fp` and cursor `c`, its region its own words at `c`,
  its cell loop and its tree's levels (`dl_callAtA`) after them, loading the weights (`wsR`).
* `dvL_callAtA`: `da_verify`'s blob loop from `g^i`, each blob's check fresh from the cursor, its
  root stored at the roots' slot `2i` (`dvLR`).
-/

namespace LeanVM.Guest.Complete

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Memory LeanVM.Guest.B1
open LeanVM.Guest.B1.Da LeanVM.Guest.B1.Digest LeanVM.Protocol.Verifier
open LeanVM.Protocol LeanVM.Protocol.KeccakHash
open LeanVM.Guest.Value
open LeanVM.Prover.Exec (allocBase)

@[expose] public section

set_option linter.constructorNameAsVariable false

variable {fs : String → ℕ} {al : String → Bool} {cert : String → V → ℕ}

theorem blob_not_loop : coreProgram.loop "da_verify_blob" = false := by decide +kernel
theorem dvL_loop : coreProgram.loop name% «da_verify_loop0» = true := by decide +kernel

theorem ptrAt_eq_gen_pow (b : ℕ) : ptrAt b = gen ^ b := (gen_pow_eq_ofK b).symm

set_option maxRecDepth 100000 in
/-- **`da_verify_blob` completes placed** at frame `fp` and cursor `c`: its region at `c` its own
words, a blob orthogonal to the dual codeword returning the root over its cells' digests. -/
theorem blob_callAtA (hfs : ∀ g, fs g < 2 ^ 16) (k : ℕ) (z : E) {syms : ℕ → List E}
    (hsl : ∀ h, (syms h).length = LeanDa.cellSymbols)
    (horth : runSum z syms 128 = 0) {bw : ℕ} {bcol : ℕ → ℕ} {fp c : ℕ} (hfc : fp + fs "da_verify_blob" ≤ c) :
    ∃ e, e ≤ c + 2 ^ 31 ∧ CallAtA fs al cert k "da_verify_blob" [ptrAt bw] [(blobRoot syms).1, (blobRoot syms).2] (wsR bw bcol)
      (fun _ => False) (fun _ => True) (fun rd => HoldsWords rd (wsWords z bw bcol))
      (fun rd t => BlobPost syms rd t ∧ t.Every (ExactAt coreProgram rd)) (fs "da_verify_blob") fp c e := by
  set L := name% «da_verify_blob_loop0»
  set σ := blobσ (ptrAt bw) c (blobRoot syms) with hσ
  have hparts := straight_parts σ blobPre rfl
  have hal : allocs σ (blobPre.flatMap (slEvs σ)) = [641] := by rw [hparts.2.1]; rfl
  have hcalls : calls (blobPre.flatMap (slEvs σ)) = [⟨L, [.n 3, .n 0, .n 1], [], true⟩, ⟨"da_levels__L128_L7", [.n 1], [.n 6, .n 7], true⟩] := by
    rw [hparts.2.2.2]; rfl
  set c1 := allocBase (al L) (c + 641) with hc1
  obtain ⟨e1, he1, h1⟩ := blL_callAtA (fs := fs) (al := al) (cert := cert) hfs k z hsl (bw := bw) (bcol := bcol)
    (bb := c) 0 (by norm_num) c1 (c1 + lpBlk fs L (128 - 0)) le_rfl
  have hce1 : c1 + lpBlk fs L (128 - 0) ≤ e1 := by obtain ⟨_, _, h, _⟩ := h1; exact h
  obtain ⟨e2, he2, h2⟩ := dl_callAtA (fs := fs) (al := al) (cert := cert) hfs (K := k) (k := 7) (Or.inr rfl)
    (b := c) (leaves := blobLeaves syms) (length_blobLeaves syms)
    (Pre := fun rd => HoldsWords rd (wsWords z bw bcol) ∧ (HoldsWords rd [(c, blobRegion z syms)] ∧ True))
    (fun rd _ hp => by
      have hR := readsAt_gen_pow.mp hp.2.1
      rw [← ptrAt_eq_gen_pow, blobRegion, readsAt_append, readsAt_append] at hR
      exact treeMem_of_reads (length_blobLeaves syms) hR.1.1)
    (fp := allocBase (al (daLevelsName 7)) e1) (c := allocBase (al (daLevelsName 7)) e1 + fs (daLevelsName 7))
    le_rfl
  have hown : ∀ i, c ≤ i → i < c + 641 → ownData cert fp c "da_verify_blob" (allocs σ (blobPre.flatMap (slEvs σ))) (blobPre.flatMap (slEvs σ)) i := by
    intro i h1 h2; rw [hal]; exact Or.inl ⟨(641, c), by simp [bases], h1, h2⟩
  have hb : e2 ≤ c + 2 ^ 31 := by
    have h3 := allocBase_le (al L) (c + 641)
    have h4 := lpBlk_le16' hfs L (128 - 0)
    have h5 := allocBase_le (al (daLevelsName 7)) e1
    have h6 := hfs (daLevelsName 7)
    omega
  refine ⟨e2, hb, CallAtA.exact (callAtA_node blob_not_loop hfc ⟨σ, fn% «da_verify_blob», blobPre.flatMap (slEvs σ), [.n 8, .n 9],
    [(c, blobRegion z syms)], [BlobLPost syms 0, FreePost], fun rd => HoldsWords rd [(c, blobRegion z syms)],
    fun _ => False, find_blob, rfl, by rw [blob_body]; exact walk_straight σ _ blobPre rfl, rfl, ?_, ?_, ?_, ?_,
    fun _ h => h.elim, ?_, fun _ _ => trivial, ?_, ?_⟩) da_verify_blob_exactFree⟩
  · rw [hal]
    unfold NodeAt
    refine ⟨by rw [hparts.1]; show [σ (.n 1)] = [ofK (addressOfIndex c)]; rw [← gen_pow_eq_ofK]; rfl, ?_⟩
    intro q hq; rw [hparts.2.2.1] at hq; simp [blobPre, Stmt.addrS] at hq
  · rw [hal]
    exact ⟨fun q hq => by simp only [List.mem_singleton] at hq; subst hq; right; simp [length_blobRegion],
      List.pairwise_singleton _ _⟩
  · intro A hA
    rw [Memory.loadAddrs_straight σ blobPre rfl] at hA
    simp only [blobPre, List.filterMap_cons, stmtLoad?, List.filterMap_nil, List.map_cons, List.map_nil,
      List.mem_cons, List.not_mem_nil, or_false] at hA
    rcases hA with rfl | rfl
    · exact ⟨c + 512, by show (gen ^ c).limb 0 * _ = _; rw [← ptrAt_eq_gen_pow]; exact Main.addr_ofK _ _,
        Or.inl (hown _ (by omega) (by omega))⟩
    · exact ⟨c + 640, by show (gen ^ c).limb 0 * _ = _; rw [← ptrAt_eq_gen_pow]; exact Main.addr_ofK _ _,
        Or.inl (hown _ (by omega) (by omega))⟩
  · intro A hA
    simp [blobPre, slEvs, heapHintAddrs, Ev.hintAddrs, hintDest?] at hA
  · rw [hcalls, hal, KidsAtF]
    simp only [↓reduceIte]
    refine ⟨lpBlk fs L (128 - 0), e1, blobLR bw bcol c, fun _ => False, fun _ => True,
      fun i hi => Or.inl (hi.elim (fun h => Or.inl h) fun h => Or.inr (hown i h.1 h.2)), ?_, ?_⟩
    · have hargs : [V.n 3, .n 0, .n 1].map σ = [gen ^ 0, ptrAt bw, ptrAt c] := by
        show [word 1 0, ptrAt bw, gen ^ c] = _; rw [word_one, pow_zero, ptrAt_eq_gen_pow c]
      rw [hargs]
      refine h1.mono (fun _ h => h) (fun _ h => h) (fun _ _ => trivial) (fun rd hp => ⟨hp.1, ?_⟩)
        (fun _ _ _ h => h)
      have := readsAt_gen_pow.mp hp.2
      rwa [← ptrAt_eq_gen_pow] at this
    · rw [KidsAtF]
      simp only [↓reduceIte]
      refine ⟨fs (daLevelsName 7), e2, treeR c 7, fun _ => False, fun _ => True,
        fun i hi => Or.inl (Or.inr (hown i hi.1 (by have := hi.2; norm_num at this; omega))), ?_, ?_⟩
      · have hargs : [V.n 1].map σ = [ptrAt c] := by show [gen ^ c] = _; rw [ptrAt_eq_gen_pow]
        rw [hargs]
        exact h2.mono (fun _ h => h) (fun _ h => h) (fun _ _ => trivial) (fun _ h => h) (fun _ _ _ h => h)
      · rw [KidsAtF]
        exact ⟨rfl, fun _ h => h.1.1, fun _ h => h.elim⟩
  · intro rd _ _ hw ev hev
    refine events_straight (fun s hs => ?_) ev hev
    have hR := readsAt_gen_pow.mp hw
    have hreg := fun i hi => loadHolds_of_readsAt hR (i := i) (by rw [length_blobRegion]; exact hi)
    simp only [blobPre, List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · trivial
    · exact rfl
    · show LoadHolds rd (gen ^ c) 512 (word 0 0)
      have := hreg 512 (by omega)
      rwa [show 512 = 0 + 512 by rfl, blobRegion_sum z syms (by omega), show runSum z syms 0 = 0 by simp [runSum],
        ← word_zero] at this
    · exact rfl
    · trivial
    · show LoadHolds rd (gen ^ c) 640 (word 0 0)
      have := hreg 640 (by omega)
      rwa [show 640 = 128 + 512 by rfl, blobRegion_sum z syms le_rfl, horth, ← word_zero] at this
    · exact rfl
    · show word 0 0 + word 0 0 = 0
      rw [word_zero, add_zero]
    · trivial
    · exact rfl
    · exact rfl
  · intro rd ts _ _ _ hv hq
    have hlen := kidsValid_len hv
    rw [hcalls] at hlen hq
    rcases ts with _ | ⟨t1, _ | ⟨t2, _ | ⟨t3, ts⟩⟩⟩
    · simp at hlen
    · simp at hlen
    · have e1' : BlobLPost syms 0 rd t1 := (kidsPost_cons.mp hq).1 rfl
      have e2' : FreePost rd t2 := (kidsPost_cons.mp (kidsPost_cons.mp hq).2).1 rfl
      rw [BlobPost, pops_straight_none find_blob blob_body rfl rfl (by rw [← hparts.2.2.2]; exact hv),
        Tree.popsKids, Tree.popsKids, Tree.popsKids, e1', e2'.1, List.range_eq_range']
      simp
    · simp at hlen

/-! ## The blob loop -/

/-- What the blob loop reads: the weights, and blob `j`'s root at the roots' slot `2j`. -/
def DvLPreA (z : E) (r : ℕ) (syms : ℕ → ℕ → List E) (bw : ℕ) (bcol : ℕ → ℕ) (qR : ℕ) (rd : Reader) : Prop :=
  HoldsWords rd (wsWords z bw bcol) ∧
    ∀ j < r, ReadsAt rd (ptrAt qR * gen ^ (2 * j)) [(blobRoot (syms j)).1, (blobRoot (syms j)).2]

/-- The cells the blob loop reads and writes: the weights and the roots' first `2r` cells. -/
def dvLR (bw : ℕ) (bcol : ℕ → ℕ) (qR r : ℕ) (i : ℕ) : Prop := wsR bw bcol i ∨ (qR ≤ i ∧ i < qR + 2 * r)

set_option maxRecDepth 100000 in
theorem dvL_step_A (hfs : ∀ g, fs g < 2 ^ 16) (k : ℕ) (z : E) {r : ℕ} (hr : r < 2 ^ 34) {syms : ℕ → ℕ → List E}
    (hsl : ∀ i h, (syms i h).length = LeanDa.cellSymbols) (horth : ∀ i < r, runSum z (syms i) 128 = 0)
    {bw : ℕ} {bcol : ℕ → ℕ} {qR : ℕ} {i : ℕ} (hi : i < r) {fp c : ℕ}
    (hfc : fp + lpBlk fs name% «da_verify_loop0» (r - i) ≤ c)
    (htail : i + 1 < r → ∀ fp' c', fp' + lpBlk fs name% «da_verify_loop0» (r - (i + 1)) ≤ c' → ∃ e,
      e ≤ c' + (r - (i + 1)) * 2 ^ 32 ∧
      CallAtA fs al cert k name% «da_verify_loop0» [gen ^ (i + 1), gen ^ r, ptrAt bw, ptrAt qR] []
        (dvLR bw bcol qR r) (fun _ => False) (fun _ => True) (DvLPreA z r syms bw bcol qR) (DvLPost syms (i + 1) r)
        (lpBlk fs name% «da_verify_loop0» (r - (i + 1))) fp' c' e) :
    ∃ e, e ≤ c + (r - i) * 2 ^ 32 ∧ CallAtA fs al cert k name% «da_verify_loop0» [gen ^ i, gen ^ r, ptrAt bw, ptrAt qR] []
      (dvLR bw bcol qR r) (fun _ => False) (fun _ => True) (DvLPreA z r syms bw bcol qR) (DvLPost syms i r)
      (lpBlk fs name% «da_verify_loop0» (r - i)) fp c e := by
  set L := name% «da_verify_loop0»
  set σ := dvLσ i r (ptrAt bw) (ptrAt qR) (blobRoot (syms i)) with hσ
  have hblk : lpBlk fs L (r - i) = fs L + lpBlk fs L (r - (i + 1)) := by
    obtain ⟨m, hm⟩ : ∃ m, r - i = m + 1 := ⟨r - i - 1, by omega⟩
    rw [lpBlk, lpBlk, hm, show r - (i + 1) = m by omega, Nat.add_mul, one_mul]; ring
  rw [hblk] at hfc ⊢
  have e10 : σ (.n 10) = gen ^ (i + 1) + gen ^ r := by
    show gen ^ i * word 2 0 + gen ^ r = _; rw [gen_mul_two]
  have hargs : [V.n 12, .n 1, .n 2, .n 3].map σ = [gen ^ (i + 1), gen ^ r, ptrAt bw, ptrAt qR] := by
    show [gen ^ i * word 2 0, gen ^ r, ptrAt bw, ptrAt qR] = _; rw [gen_mul_two]
  have hcalls : (dvLPre.filterMap Stmt.callS).map (mkCall σ) =
      [⟨"da_verify_blob", [.n 2], [.n 4, .n 5], true⟩,
        ⟨L, [.n 12, .n 1, .n 2, .n 3], [], decide (σ (.n 10) ≠ 0)⟩] := rfl
  obtain ⟨eb, heb, hb⟩ := blob_callAtA (fs := fs) (al := al) (cert := cert) hfs k z (hsl i) (horth i hi) (bw := bw)
    (bcol := bcol) (fp := allocBase (al "da_verify_blob") c) (c := allocBase (al "da_verify_blob") c +
      fs "da_verify_blob") le_rfl
  have hce : allocBase (al "da_verify_blob") c + fs "da_verify_blob" ≤ eb := by obtain ⟨_, _, h, _⟩ := hb; exact h
  have htl : ∃ e Bt, Bt = lpBlk fs L (r - (i + 1)) ∧ e ≤ eb + (r - (i + 1)) * 2 ^ 32 ∧
      KidsAtL fs al cert k σ (dvLR bw bcol qR r)
      (DvLPreA z r syms bw bcol qR) (fp + fs L) (fun rd => HoldsWords rd [] ∧ True) (fun i => False ∨ False)
      [DvLPost syms (i + 1) r] [⟨L, [.n 12, .n 1, .n 2, .n 3], [], decide (σ (.n 10) ≠ 0)⟩] eb e Bt
      (fun rd => HoldsWords rd []) (fun _ => False) := by
    by_cases hlt : i + 1 < r
    · have htk : decide (σ (.n 10) ≠ 0) = true := by
        rw [e10, gen_guard hr (by omega)]; exact decide_eq_true (by omega)
      obtain ⟨e, heb', he⟩ := htail hlt (fp + fs L) eb (by have := le_allocBase (al "da_verify_blob") c; omega)
      refine ⟨e, _, rfl, heb', ?_⟩
      rw [KidsAtL]
      simp only [htk, ↓reduceIte]
      refine ⟨dvLR bw bcol qR r, fun _ => False, fun _ => True, fun i hi => Or.inl hi, ?_,
        fun _ h _ => h.1, fun _ h => h.elim⟩
      rw [hargs]
      exact he.mono (fun _ h => h) (fun _ h => h) (fun _ _ => trivial) (fun _ h => h.1) (fun _ _ _ h => h)
    · have htk : decide (σ (.n 10) ≠ 0) = false := by
        rw [e10, gen_guard hr (by omega)]; exact decide_eq_false (by omega)
      refine ⟨eb, _, rfl, by omega, ?_⟩
      rw [KidsAtL]
      simp only [htk, Bool.false_eq_true, ↓reduceIte]
      refine ⟨⟨dvLσ (i + 1) r (ptrAt bw) (ptrAt qR) 0, fn% «da_verify_loop0», find_dvL, ?_⟩, ?_, trivial,
        fun _ h => h.1, fun _ h => h.elim⟩
      · rw [dvL_params, hargs]; rfl
      · rw [show r - (i + 1) = 0 by omega, lpBlk]; simp
  obtain ⟨e, Bt, rfl, hbe, htl⟩ := htl
  refine ⟨e, ?_, callAtA_straightL find_dvL dvL_body rfl (by decide +kernel) dvL_loop hfc σ rfl rfl ?_
    [fun rd t => BlobPost (syms i) rd t ∧ t.Every (ExactAt coreProgram rd), DvLPost syms (i + 1) r]
    (fun rd => HoldsWords rd []) (fun _ => False) ?_ (fun _ _ => trivial) ?_ ?_⟩
  · have h1 := allocBase_le (al "da_verify_blob") c
    have h2 := hfs "da_verify_blob"
    omega
  · intro x hx
    simp only [dvLPre, List.filterMap_cons, stmtLoad?, List.filterMap_nil, List.mem_cons, List.not_mem_nil,
      or_false] at hx
    rcases hx with rfl | rfl
    · exact ⟨qR + 2 * i + 0, by
        show (ptrAt qR * (gen ^ i * gen ^ i)).limb 0 * _ = _; rw [gen_sq, ptrAt_mul_gen_pow]; exact Main.addr_ofK _ _,
        Or.inr ⟨by omega, by omega⟩⟩
    · exact ⟨qR + 2 * i + 1, by
        show (ptrAt qR * (gen ^ i * gen ^ i)).limb 0 * _ = _; rw [gen_sq, ptrAt_mul_gen_pow]; exact Main.addr_ofK _ _,
        Or.inr ⟨by omega, by omega⟩⟩
  · rw [hcalls, KidsAtL]
    simp only [↓reduceIte]
    refine ⟨fs "da_verify_blob", eb, wsR bw bcol, fun _ => False, fun _ => True, fun i hi => Or.inl (Or.inl hi),
      ?_, htl⟩
    exact hb.mono (fun _ h => h) (fun _ h => h) (fun _ _ => trivial) (fun rd hp => hp.1.1) (fun _ _ _ h => h)
  · intro rd _ hp _ s hs
    have hR := hp.2 i hi
    simp only [dvLPre, List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · trivial
    · exact rfl
    · exact rfl
    · show LoadHolds rd (ptrAt qR * (gen ^ i * gen ^ i)) 0 (blobRoot (syms i)).1
      rw [gen_sq]; exact hR 0 (by simp)
    · show LoadHolds rd (ptrAt qR * (gen ^ i * gen ^ i)) 1 (blobRoot (syms i)).2
      rw [gen_sq]; exact hR 1 (by simp)
    · exact rfl
    · exact rfl
    · exact rfl
    · exact rfl
    · exact rfl
    · show IsInK (σ (.n 10)); rw [e10]; exact gen_pow_add_isInK _ _
  · intro rd ts _ _ _ hv hq
    have hlen := kidsValid_len hv
    rw [hcalls] at hlen hq hv
    rcases ts with _ | ⟨t1, _ | ⟨t2, _ | ⟨t3, ts⟩⟩⟩
    · simp at hlen
    · simp at hlen
    · have h1 : BlobPost (syms i) rd t1 := ((kidsPost_cons.mp hq).1 rfl).1
      have h2 : t2.pops coreProgram rd = dvPops syms (i + 1) (r - (i + 1)) := by
        by_cases hlt : i + 1 < r
        · have htk : decide (σ (.n 10) ≠ 0) = true := by
            rw [e10, gen_guard hr (by omega)]; exact decide_eq_true (by omega)
          exact (kidsPost_cons.mp (kidsPost_cons.mp hq).2).1 htk
        · have htk : decide (σ (.n 10) ≠ 0) = false := by
            rw [e10, gen_guard hr (by omega)]; exact decide_eq_false (by omega)
          have hv2 := hv.2.2.2.1
          simp only [htk, Bool.false_eq_true, ↓reduceIte] at hv2
          obtain ⟨⟨f, σ', rfl⟩, -⟩ := hv2
          rw [Tree.pops, show r - (i + 1) = 0 by omega]; rfl
      show _ = _
      rw [pops_straight_none find_dvL dvL_body rfl rfl (by rw [hcalls]; exact hv), Tree.popsKids, Tree.popsKids,
        Tree.popsKids, h1, h2, show r - i = r - (i + 1) + 1 by omega, dvPops, dvPops, List.range'_succ,
        List.flatMap_cons]
      simp
    · simp at hlen

/-- **The blob loop completes placed** from every counter below the count `r`. -/
theorem dvL_callAtA (hfs : ∀ g, fs g < 2 ^ 16) (k : ℕ) (z : E) {r : ℕ} (hr : r < 2 ^ 34) {syms : ℕ → ℕ → List E}
    (hsl : ∀ i h, (syms i h).length = LeanDa.cellSymbols) (horth : ∀ i < r, runSum z (syms i) 128 = 0)
    {bw : ℕ} {bcol : ℕ → ℕ} {qR : ℕ} : ∀ i < r, ∀ fp c, fp + lpBlk fs name% «da_verify_loop0» (r - i) ≤ c →
      ∃ e, e ≤ c + (r - i) * 2 ^ 32 ∧ CallAtA fs al cert k name% «da_verify_loop0» [gen ^ i, gen ^ r, ptrAt bw, ptrAt qR] []
        (dvLR bw bcol qR r) (fun _ => False) (fun _ => True) (DvLPreA z r syms bw bcol qR) (DvLPost syms i r)
        (lpBlk fs name% «da_verify_loop0» (r - i)) fp c e := by
  have key : ∀ t i, i + 1 + t = r → ∀ fp c, fp + lpBlk fs name% «da_verify_loop0» (r - i) ≤ c →
      ∃ e, e ≤ c + (r - i) * 2 ^ 32 ∧ CallAtA fs al cert k name% «da_verify_loop0» [gen ^ i, gen ^ r, ptrAt bw, ptrAt qR] []
        (dvLR bw bcol qR r) (fun _ => False) (fun _ => True) (DvLPreA z r syms bw bcol qR) (DvLPost syms i r)
        (lpBlk fs name% «da_verify_loop0» (r - i)) fp c e := by
    intro t
    induction t with
    | zero => intro i hi fp c hfc; exact dvL_step_A hfs k z hr hsl horth (by omega) hfc fun h' => absurd h' (by omega)
    | succ t ih =>
      intro i hi fp c hfc; exact dvL_step_A hfs k z hr hsl horth (by omega) hfc fun _ => ih (i + 1) (by omega)
  intro i hi
  exact key (r - i - 1) i (by omega)

end
end LeanVM.Guest.Complete
