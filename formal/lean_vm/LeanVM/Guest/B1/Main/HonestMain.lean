/-
  LeanVM.Guest.B1.Main.HonestMain

  `main`'s own callees' preconditions on its honest words: the claim lists, the DA list, the raw
  signatures, the direct DA claim, the signer set, the statement's digest, the running counts.
-/

module

public import LeanVM.Guest.B1.Main.HonestOk

/-!
# `main`'s callees, honestly

On every memory holding `mainIn` for `honestWords`: the tables' prefixes are the declared claims
(`hon_daClaims`, `hon_xList`, `hon_sList`), each raw signature's slot holds its claim and marks
its writer's number (`hon_xRaw`, `hon_sRaw`), the direct DA claim likewise (`hon_daRaw`); the signer
set's compression (`hon_sig`) and the statement (`hon_stmt`).
-/

namespace LeanVM.Guest.B1.Main

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Memory
open LeanVM.Protocol LeanVM.Protocol.Blake2sHash LeanVM.Protocol.Verifier LeanVM.Node
open LeanVM.Guest.Hints (direct)
open LeanVM.Guest.End (Limits coverage)
open LeanVM.Guest.B1 (LowDef Meaning_statement_digest Meaning_da_list_digest DaClaimsAt
  Meaning_verify_lean_xmss Meaning_verify_sig_lean_sphincs)
open LeanVM.Guest.B1.Digest (SquaresAt CellsAt)

@[expose] public section

variable (fs : String → ℕ) {fp : ℕ} {seed : Digest} {s : NodeStatement} {w : NodeWitness}
  {rd : Reader}

/-! ## Reading the tables -/

theorem readsAt_flatMap4 {γ : Type} {f : γ → List E} (hf : ∀ a, (f a).length = 4) {p : E}
    {L : List γ} (h : ReadsAt rd p (L.flatMap f)) (i : ℕ) (hi : i < L.length) :
    ReadsAt rd (p * gen ^ (4 * i)) (f L[i]) :=
  readsAt_flatMap_of L (fun a _ => hf a) h i hi

theorem daClaimsAt_of_reads {p : E} {L : List DaClaim} (h : ReadsAt rd p (L.flatMap daCellsOf)) :
    DaClaimsAt rd p L := by
  intro i hi
  have := readsAt_flatMap4 daCellsOf_length h i hi
  have g : ∀ k (hk : k < 4), LoadHolds rd p (4 * i + k) (daCellsOf L[i])[k] :=
    fun k hk => (loadHolds_mul_gen_pow _ _ _ _ _).mp (this k (by rw [daCellsOf_length]; exact hk))
  exact ⟨by rw [← Nat.add_zero (4 * i)]; exact g 0 (by omega), g 1 (by omega), g 2 (by omega),
    g 3 (by omega)⟩

theorem squaresAt_of_mainIn {W : MainWords} (hL : MemL rd (mainIn fs fp W)) :
    SquaresAt rd (ofK (gpow (mainExpBase fs fp W + 34))) := by
  have h := hL (mainExpBase fs fp W + 34, expTbl2) (List.mem_append_right _ (by simp [mainLexp]))
  intro j hj
  have := h j (by simp [expTbl2]; omega)
  simpa [expTbl2] using this

/-! ## The declared lists -/

theorem hon_daList (hlim : Limits s w) (hL : MemL rd (mainIn fs fp (honestWords seed s w))) :
    DaListPreAt s.claims.da rd [mainPtr fs fp (honestWords seed s w) 0, gen ^ s.claims.da.length]
      [(digestScalars (daListDigest s.claims.da)).1, (digestScalars (daListDigest s.claims.da)).2] := by
  have h := mainIn_reads hL 0 (by omega)
  simp only [MainWords.bufs, honestWords, List.getD_cons_zero, List.flatMap_append] at h
  exact ⟨hlim.daRoots.1, rfl, daClaimsAt_of_reads (readsAt_append'.mp h).1, rfl⟩

theorem hon_xList (hlim : Limits s w) (hL : MemL rd (mainIn fs fp (honestWords seed s w))) :
    ClPreAt (s.claims.xmss.flatMap xCellsOf) rd
      [mainPtr fs fp (honestWords seed s w) 1, gen ^ s.claims.xmss.length,
        ofK (gpow (mainExpBase fs fp (honestWords seed s w) + 34))]
      [(digestScalars (xmssListDigest s.claims.xmss)).1, (digestScalars (xmssListDigest s.claims.xmss)).2] := by
  have h := mainIn_reads hL 1 (by omega)
  simp only [MainWords.bufs, honestWords, List.getD_cons_succ, List.getD_cons_zero,
    List.flatMap_append] at h
  have ht := honest_total (seed := seed) hlim
  refine ⟨squaresAt_of_mainIn fs hL, s.claims.xmss.length,
    by simp only [MainWords.total, honestWords] at ht; omega, rfl,
    length_flatMap_const _ 4 _ fun c _ => xCellsOf_length c, (readsAt_append'.mp h).1,
    xCellsOf_canonical _, ?_⟩
  rw [xCellsOf_bytes]; rfl

theorem hon_sList (hlim : Limits s w) (hL : MemL rd (mainIn fs fp (honestWords seed s w))) :
    ClPreAt (s.claims.sphincs.flatMap sCellsOf) rd
      [mainPtr fs fp (honestWords seed s w) 2, gen ^ s.claims.sphincs.length,
        ofK (gpow (mainExpBase fs fp (honestWords seed s w) + 34))]
      [(digestScalars (sphincsListDigest s.claims.sphincs)).1,
        (digestScalars (sphincsListDigest s.claims.sphincs)).2] := by
  have h := mainIn_reads hL 2 (by omega)
  simp only [MainWords.bufs, honestWords, List.getD_cons_succ, List.getD_cons_zero,
    List.flatMap_append] at h
  have ht := honest_total (seed := seed) hlim
  refine ⟨squaresAt_of_mainIn fs hL, s.claims.sphincs.length,
    by simp only [MainWords.total, honestWords] at ht; omega, rfl,
    length_flatMap_const _ 4 _ fun c _ => sCellsOf_length c, (readsAt_append'.mp h).1,
    sCellsOf_canonical _, ?_⟩
  rw [sCellsOf_bytes]; rfl

/-- **The signer set's block.** -/
theorem hon_sig (a b : Digest) :
    CompressCells ![(digestScalars a).1, (digestScalars a).2, (digestScalars b).1, (digestScalars b).2]
      ivCells.1 ivCells.2 (digestScalars (blake2sBytes (digestBytes a ++ digestBytes b))).1
      (digestScalars (blake2sBytes (digestBytes a ++ digestBytes b))).2 (metadataCell 64 true) := by
  refine (blake2s_default_iff fun i => ?_).mpr ?_
  · fin_cases i
    exacts [(isCanonical128_digestScalars a).1, (isCanonical128_digestScalars a).2,
      (isCanonical128_digestScalars b).1, (isCanonical128_digestScalars b).2]
  · rw [digestBytes_eq, digestBytes_eq]
    simp [blockBytes, List.append_assoc]

/-! ## The coverage marks -/

theorem covOf_getD {sl : List ℕ} {gl : ℕ → ℕ} {n : ℕ} (hnd : sl.Nodup) {r : ℕ} (hr : r < sl.length)
    (hn : sl.getD r 0 < n) : (covOf sl gl n).getD (sl.getD r 0) 0 = gen ^ gl r := by
  rw [List.getD_eq_getElem _ _ (by rw [covOf_length]; exact hn), covOf_slot hnd hr hn]

theorem getD_app_left {l l' : List E} {n : ℕ} (h : n < l.length) : (l ++ l').getD n 0 = l.getD n 0 := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]

theorem getD_app_right {l l' : List E} {m : ℕ} (h : l.length = m) (n : ℕ) :
    (l ++ l').getD (m + n) 0 = l'.getD n 0 := by
  subst h
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_right]

theorem hon_cov_length : (honestWords seed s w).cov.length = (honestWords seed s w).total := by
  simp only [honestWords, List.length_append, covOf_length, MainWords.total]

/-- **A leanXMSS writer's mark**: writer `r`'s slot holds `g^(gX r)`. -/
theorem hon_markX {r : ℕ} (hr : r < (writersX s w).length) :
    (planX s w).1.getD r 0 < s.claims.xmss.length + (planX s w).2.length ∧
    CellL (mainIn fs fp (honestWords seed s w))
      (mainBase fs fp (honestWords seed s w) 4 + (planX s w).1.getD r 0) (gen ^ gX s w r) := by
  have hreg := region_slots s.claims.xmss (writersX s w)
  rw [show assign s.claims.xmss [] [] (writersX s w) = planX s w from rfl] at hreg
  obtain ⟨l1, hnd, hsl⟩ := hreg
  have hs := (hsl r hr).1
  refine ⟨hs, cellL_of_getD (mainIn_mem 4 (by omega)) _ ?_ ?_⟩
  · simp only [MainWords.bufs, List.getD_cons_succ, List.getD_cons_zero]
    rw [hon_cov_length]; simp only [MainWords.total, honestWords]; omega
  · simp only [MainWords.bufs, List.getD_cons_succ, List.getD_cons_zero, honestWords]
    rw [List.append_assoc, getD_app_left (by rw [covOf_length]; exact hs)]
    exact covOf_getD hnd (by omega) hs

/-- **A leanSPHINCS writer's mark.** -/
theorem hon_markS {r : ℕ} (hr : r < (writersS s w).length) :
    (planS s w).1.getD r 0 < s.claims.sphincs.length + (planS s w).2.length ∧
    CellL (mainIn fs fp (honestWords seed s w))
      (mainBase fs fp (honestWords seed s w) 4 + (s.claims.xmss.length + (planX s w).2.length +
        (planS s w).1.getD r 0)) (gen ^ gS s w r) := by
  have hreg := region_slots s.claims.sphincs (writersS s w)
  rw [show assign s.claims.sphincs [] [] (writersS s w) = planS s w from rfl] at hreg
  obtain ⟨l1, hnd, hsl⟩ := hreg
  have hs := (hsl r hr).1
  refine ⟨hs, cellL_of_getD (mainIn_mem 4 (by omega)) _ ?_ ?_⟩
  · simp only [MainWords.bufs, List.getD_cons_succ, List.getD_cons_zero]
    rw [hon_cov_length]; simp only [MainWords.total, honestWords]; omega
  · simp only [MainWords.bufs, List.getD_cons_succ, List.getD_cons_zero, honestWords]
    rw [List.append_assoc, getD_app_right (covOf_length _ _ _),
      getD_app_left (by rw [covOf_length]; exact hs)]
    exact covOf_getD hnd (by omega) hs

/-- **A DA writer's mark.** -/
theorem hon_markD {r : ℕ} (hr : r < (writersD s w).length) :
    (planD s w).1.getD r 0 < s.claims.da.length + (planD s w).2.length ∧
    CellL (mainIn fs fp (honestWords seed s w))
      (mainBase fs fp (honestWords seed s w) 4 + (s.claims.xmss.length + (planX s w).2.length +
        (s.claims.sphincs.length + (planS s w).2.length) + (planD s w).1.getD r 0)) (gen ^ gD s w r) := by
  have hreg := region_slots s.claims.da (writersD s w)
  rw [show assign s.claims.da [] [] (writersD s w) = planD s w from rfl] at hreg
  obtain ⟨l1, hnd, hsl⟩ := hreg
  have hs := (hsl r hr).1
  refine ⟨hs, cellL_of_getD (mainIn_mem 4 (by omega)) _ ?_ ?_⟩
  · simp only [MainWords.bufs, List.getD_cons_succ, List.getD_cons_zero]
    rw [hon_cov_length]; simp only [MainWords.total, honestWords]; omega
  · simp only [MainWords.bufs, List.getD_cons_succ, List.getD_cons_zero, honestWords]
    rw [getD_app_right (by rw [List.length_append, covOf_length, covOf_length])]
    exact covOf_getD hnd (by omega) hs

/-! ## The tables' entries at the writers' slots -/

theorem hon_xEntry (hL : MemL rd (mainIn fs fp (honestWords seed s w))) {r : ℕ}
    (hr : r < (writersX s w).length) {cl : XmssClaim} (hc : (writersX s w)[r]? = some cl) :
    ReadsAt rd (mainPtr fs fp (honestWords seed s w) 1 * gen ^ (4 * (planX s w).1.getD r 0))
      (xCellsOf cl) := by
  have hreg := region_slots s.claims.xmss (writersX s w)
  rw [show assign s.claims.xmss [] [] (writersX s w) = planX s w from rfl] at hreg
  obtain ⟨hs, he⟩ := hreg.2.2 r hr
  have h : ReadsAt rd (mainPtr fs fp (honestWords seed s w) 1)
      ((s.claims.xmss ++ (planX s w).2).flatMap xCellsOf) := mainIn_reads hL 1 (by omega)
  have := readsAt_flatMap4 xCellsOf_length h ((planX s w).1.getD r 0) (by simp only [List.length_append]; exact hs)
  rw [hc, List.getElem?_eq_getElem (by simpa using hs), Option.some.injEq] at he
  rw [he] at this
  exact this

theorem hon_sEntry (hL : MemL rd (mainIn fs fp (honestWords seed s w))) {r : ℕ}
    (hr : r < (writersS s w).length) {cl : SphincsClaim} (hc : (writersS s w)[r]? = some cl) :
    ReadsAt rd (mainPtr fs fp (honestWords seed s w) 2 * gen ^ (4 * (planS s w).1.getD r 0))
      (sCellsOf cl) := by
  have hreg := region_slots s.claims.sphincs (writersS s w)
  rw [show assign s.claims.sphincs [] [] (writersS s w) = planS s w from rfl] at hreg
  obtain ⟨hs, he⟩ := hreg.2.2 r hr
  have h : ReadsAt rd (mainPtr fs fp (honestWords seed s w) 2)
      ((s.claims.sphincs ++ (planS s w).2).flatMap sCellsOf) := mainIn_reads hL 2 (by omega)
  have := readsAt_flatMap4 sCellsOf_length h ((planS s w).1.getD r 0) (by simp only [List.length_append]; exact hs)
  rw [hc, List.getElem?_eq_getElem (by simpa using hs), Option.some.injEq] at he
  rw [he] at this
  exact this

theorem hon_dEntry (hL : MemL rd (mainIn fs fp (honestWords seed s w))) {r : ℕ}
    (hr : r < (writersD s w).length) {cl : DaClaim} (hc : (writersD s w)[r]? = some cl) :
    ReadsAt rd (mainPtr fs fp (honestWords seed s w) 0 * gen ^ (4 * (planD s w).1.getD r 0))
      (daCellsOf cl) := by
  have hreg := region_slots s.claims.da (writersD s w)
  rw [show assign s.claims.da [] [] (writersD s w) = planD s w from rfl] at hreg
  obtain ⟨hs, he⟩ := hreg.2.2 r hr
  have h : ReadsAt rd (mainPtr fs fp (honestWords seed s w) 0)
      ((s.claims.da ++ (planD s w).2).flatMap daCellsOf) := mainIn_reads hL 0 (by omega)
  have := readsAt_flatMap4 daCellsOf_length h ((planD s w).1.getD r 0) (by simp only [List.length_append]; exact hs)
  rw [hc, List.getElem?_eq_getElem (by simpa using hs), Option.some.injEq] at he
  rw [he] at this
  exact this

theorem claimAt_of_reads {p : E} {r q : BitVec 128} {m : BitVec 256}
    (h : ReadsAt rd p (List.ofFn (LeanVM.Guest.B1.claimCells r q m))) :
    LeanVM.Guest.B1.ClaimAt rd p (LeanVM.Guest.B1.claimCells r q m) := fun k => by
  have := h k.val (by simp)
  rw [List.getElem_ofFn] at this
  exact this

/-- **A raw leanXMSS signature verifies its slot's claim.** -/
theorem hon_xSig (hX : List.Forall₂ (XmssHeld w.children) s.claims.xmss w.xmss)
    (hL : MemL rd (mainIn fs fp (honestWords seed s w))) {c : ℕ} (hc : c < hrx s w) :
    Meaning_verify_lean_xmss rd [mainPtr fs fp (honestWords seed s w) 1 *
      gen ^ (4 * (planX s w).1.getD c 0)] [] := by
  have hmem : (direct s.claims.xmss w.xmss)[c]'hc ∈ direct s.claims.xmss w.xmss := List.getElem_mem _
  have hv := direct_mem hX hmem
  have he := hon_xEntry fs hL (by rw [writersX_len]; omega) (writersX_raw hc)
  exact ⟨_, rfl, rfl, _, _, claimAt_of_reads he, _, hv⟩

/-- **A raw leanSPHINCS signature verifies its slot's claim.** -/
theorem hon_sSig (hS : List.Forall₂ (SphincsHeld w.children) s.claims.sphincs w.sphincs)
    (hL : MemL rd (mainIn fs fp (honestWords seed s w))) {c : ℕ} (hc : c < hrs s w) :
    Meaning_verify_sig_lean_sphincs rd [mainPtr fs fp (honestWords seed s w) 2 *
      gen ^ (4 * (planS s w).1.getD c 0)] [] := by
  have hmem : (direct s.claims.sphincs w.sphincs)[c]'hc ∈ direct s.claims.sphincs w.sphincs :=
    List.getElem_mem _
  have hv := direct_mem hS hmem
  have he := hon_sEntry fs hL (by rw [writersS_len]; omega) (writersS_raw hc)
  exact ⟨_, rfl, rfl, _, _, claimAt_of_reads he, _, hv⟩

/-! ## The direct DA claim -/

theorem hon_daVerify (hD : List.Forall₂ (DaHeld w.children) s.claims.da w.da) (h1 : hrd s w = 1) :
    ∃ (wt : Da.Witness) (root vd : Digest), wt.Opens root vd ∧
      wt.rows.length = (honestWords seed s w).drows ∧
      ∀ rd, MemL rd (mainIn fs fp (honestWords seed s w)) →
        DaVerifyPreAt root vd rd [ofK (gpow (mainExpBase fs fp (honestWords seed s w) + 34))]
          [(honestWords seed s w).dr.1, (honestWords seed s w).dr.2.1, (honestWords seed s w).dr.2.2.1,
            (honestWords seed s w).dr.2.2.2] := by
  unfold hrd at h1
  match hd : direct s.claims.da w.da, h1 with
  | [p], _ =>
    have hv := direct_mem hD (p := p) (by rw [hd]; exact List.mem_singleton_self p)
    refine ⟨p.2, p.1.1, p.1.2, hv, by simp [honestWords, hd], fun rd hL => ⟨squaresAt_of_mainIn fs hL, ?_, ?_⟩⟩ <;>
      simp [honestWords, hd, drOf]

theorem loadHolds_cover {p : E} {a b c d i : ℕ} {v : E}
    (h : LoadHolds rd p (a + b + (c + d) + i) v) :
    LoadHolds rd (p * (gen ^ a * gen ^ b * (gen ^ c * gen ^ d)) * gen ^ i) 0 v := by
  rw [loadHolds_mul_gen_pow, ← pow_add, ← pow_add, ← pow_add, loadHolds_mul_gen_pow]
  rwa [Nat.add_zero]

theorem hon_daCover (hlim : Limits s w) (h1 : hrd s w = 1) (hL : MemL rd (mainIn fs fp (honestWords seed s w))) :
    CoverPreAt ((planD s w).1.getD 0 0) rd [mainPtr fs fp (honestWords seed s w) 0,
      mainPtr fs fp (honestWords seed s w) 4 * (gen ^ s.claims.xmss.length * gen ^ (planX s w).2.length *
        (gen ^ s.claims.sphincs.length * gen ^ (planS s w).2.length)),
      gen ^ s.claims.da.length * gen ^ (planD s w).2.length, gen ^ hrx s w * gen ^ hrs s w]
      [(honestWords seed s w).dr.1, (honestWords seed s w).dr.2.1, (honestWords seed s w).dr.2.2.1,
        (honestWords seed s w).dr.2.2.2] := by
  have hr : 0 < (writersD s w).length := by rw [writersD_len]; omega
  obtain ⟨hs, hc⟩ := hon_markD fs (seed := seed) (fp := fp) hr
  have hdau := honest_dau hlim
  have hm := hc.load hL
  rw [gD_raw (by omega), Nat.add_zero, pow_add] at hm
  have he := hon_dEntry fs hL hr (writersD_raw (by omega))
  refine ⟨s.claims.da.length + (planD s w).2.length, by omega, hs,
    (pow_add _ _ _).symm, loadHolds_cover hm, ?_⟩
  unfold hrd at h1
  match hd : direct s.claims.da w.da, h1 with
  | [p], _ =>
    simp only [hd, List.getElem_cons_zero] at he
    simp only [honestWords, hd, drOf]
    exact he

/-! ## The running counts -/

theorem hon_wTab_getD (c : ℕ) (hc : c ≤ w.children.length) :
    (honestWords seed s w).wTab.getD c 0 = gen ^ hbase s w c := by
  simp only [honestWords]
  rw [List.getD_eq_getElem _ _ (by simp; omega)]
  simp

theorem hon_written (c : ℕ) (hc : c ≤ w.children.length) :
    CellL (mainIn fs fp (honestWords seed s w)) (mainBase fs fp (honestWords seed s w) 8 + c)
      (gen ^ hbase s w c) :=
  cellL_of_getD (mainIn_mem 8 (by omega)) c (by simp [MainWords.bufs, honestWords]; omega)
    (hon_wTab_getD c hc)

/-! ## The statement -/

theorem hon_stmt {bytecode : List K} (hb : bytecode.length = 2 ^ 22)
    (hsh : s.defer.Shaped bytecode) (hL : MemL rd (mainIn fs fp (honestWords seed s w))) :
    SdPreAt (signersDigest s.claims.xmss s.claims.sphincs) s.defer.cells rd
      [(digestScalars seed).1, (digestScalars seed).2,
      mainPtr fs fp (honestWords seed s w) 3, (digestScalars (daListDigest s.claims.da)).1,
      (digestScalars (daListDigest s.claims.da)).2, mainPtr fs fp (honestWords seed s w) 9]
      [(digestScalars (statementDigest seed s)).1, (digestScalars (statementDigest seed s)).2] := by
  have h3 : ReadsAt rd (mainPtr fs fp (honestWords seed s w) 3)
      [(digestScalars (signersDigest s.claims.xmss s.claims.sphincs)).1,
        (digestScalars (signersDigest s.claims.xmss s.claims.sphincs)).2] := mainIn_reads hL 3 (by omega)
  have h9 : ReadsAt rd (mainPtr fs fp (honestWords seed s w) 9) s.defer.cells := mainIn_reads hL 9 (by omega)
  exact ⟨seed, daListDigest s.claims.da, defer_cells_length hb hsh, rfl, h3 0 (by simp),
    h3 1 (by simp), rfl, h9, by rw [statementDigest_eq]⟩

end
end LeanVM.Guest.B1.Main
