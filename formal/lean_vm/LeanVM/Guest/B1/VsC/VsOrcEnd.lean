/-
  LeanVM.Guest.B1.VsC.VsOrcEnd

  The honest oracle's final condition: `VsOrc` ending in `VsWinHypW`'s condition, and that condition from
  `vsPostA_final` at the honest oracle.
-/

module

public import LeanVM.Guest.B1.VsC.VsOrcTail
public import LeanVM.Guest.B1.VsC.VsOrcHonest
public import LeanVM.Guest.B1.VsC.VsPostE
public import LeanVM.Guest.B1.Bits.GrindWin

/-!
# `verify_sub`'s final condition at the honest oracle

`vsKEnd` (`VsWinHyp`'s final condition) does not give the body's walk and its events holding on the memory it
quantifies, which `vsPostA_of` needs; `VsWinHypW`'s does (`SegA` supplies them). So the honest oracle's statement
ends in that condition: `vsKEndW`, `VsOrcW` (`VsOrc` with `vsKEndW`), `vsWinHypW_of_orcW`, `VsOrcWFromCallees`,
**`vsWindowsFromCallees_of_orcW`** (`GuestLeft.vsWindows` from it).

`vsKEndW_of`: the condition from `vsPostA_final`'s remaining inputs at the state the windows reach. On the honest
oracle `vsW rd1 args cur (chunksOf len) ret` and a memory `rd0` whose fresh loads read as `rd1`'s (`VsFresh`), the
chunk count and the six grinds' windows hold by the rule (`vsW_hW`, `vsW_h42`): **`vsKEndW_honest`**.
-/

namespace LeanVM.Guest.B1.VsC

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Memory LeanVM.Guest.B1
open LeanVM.Guest.Complete LeanVM.Guest.B1.Fwd LeanVM.Node LeanVM.Protocol LeanVM.Protocol.Verifier
open LeanVM.Guest.Value
open LeanVM.Prover.Exec (wordNat)

@[expose] public section

/-! ## The final condition with the walk -/

/-- **`VsWinHypW`'s final condition**: on every memory with `Pre`, the windows' words, the body's walk and its
events holding, the callees' trees satisfying their posts give `vsPostA`. -/
noncomputable def vsKEndW (k : ℕ) (bytecode : List K) (seed : Digest) (c : Child) (qt qo : ℕ) (σ0 : Val) :
    St → Prop := fun st =>
  ∀ rd, LowDef k rd → vsPreA seed c qt qo rd → st.O rd →
    walk (rdOver σ0 rd) vsSS = .fall (vsEs σ0) → (∀ ev ∈ vsEs σ0, ev.Holds rd (rdOver σ0 rd)) → ∀ ts,
    Tree.KidsValid coreProgram rd (rdOver σ0 rd) (calls (vsEs σ0)) ts →
    KidsPost rd st.Qs (calls (vsEs σ0)) ts →
    vsPostA bytecode seed c rd (.node "verify_sub" (rdOver σ0 rd) (allocs σ0 (vsEs σ0)) ts)

/-- **The honest oracle's statement, ending in `vsKEndW`**: `VsOrc` with `VsWinHypW`'s final condition. -/
def VsOrcW (al : String → Bool) (k : ℕ) (bytecode : List K) (seed : Digest) : Prop :=
  ∀ (c : Child) (qt qo fp cur : ℕ), VsChildOk bytecode seed c → qt + expTabLen ≤ fp →
    qo + c.freshClaim.cells.length ≤ fp → fp + B2C.fs "verify_sub" ≤ cur →
    (∃ rd, vsPreA seed c qt qo rd) → cur < 2 ^ 60 →
    ∃ (rd0 : Reader) (w : ℕ → E) (Wo : Words),
      WordsInA Wo (fp + 2) (fp + B2C.fs "verify_sub") cur
        (cur + (allocs (vsσ rd0 w seed c qt qo) (vsEs (vsσ rd0 w seed c qt qo))).sum) ∧
      FrontOk B2C.fs al B2C.cert k rd0 w (vsArgs seed c (ptrAt qt) (ptrAt qo))
        (vsOwn fp cur (vsσ rd0 w seed c qt qo)) (vsRegion qt qo c.freshClaim.cells.length) (vsPreA seed c qt qo)
        (vsSt0 (vsσ rd0 w seed c qt qo) cur Wo) fun s =>
      WCOk B2C.fs al B2C.cert k rd0 w (vsArgs seed c (ptrAt qt) (ptrAt qo))
        (vsOwn fp cur (vsσ rd0 w seed c qt qo)) (vsRegion qt qo c.freshClaim.cells.length) (vsPreA seed c qt qo)
        s fun st => (cur < 2 ^ 60 → st.kc ≤ cur + 2 ^ 40) ∧ vsKEndW k bytecode seed c qt qo (vsσ rd0 w seed c qt qo) st

/-- **`VsWinHypW` from the honest oracle's statement.** -/
theorem vsWinHypW_of_orcW {al : String → Bool} {k : ℕ} {bytecode : List K} {seed : Digest} (hk : 11 ≤ k)
    (h : VsOrcW al k bytecode seed) : VsWinHypW al k bytecode seed := by
  intro c qt qo fp cur hc ht ho hfc hP hcur
  obtain ⟨rd0, w, Wo, hWo, H⟩ := h c qt qo fp cur hc ht ho hfc hP hcur
  exact ⟨rd0, w, Wo, hWo, vsHyp_of_orc hk rfl H⟩

/-- **What is left of `verify_sub`'s windows**, as the honest oracle's statement ending in `vsKEndW`. -/
def VsOrcWFromCallees (al : String → Bool) (k : ℕ) : Prop :=
  14 ≤ k → VsCalleesCompleteA B2C.fs al B2C.cert k → ∀ seed, VsOrcW al k guestBytecode seed

/-- **`verify_sub`'s windows from the honest oracle's statement** (`GuestLeft.vsWindows`). -/
theorem vsWindowsFromCallees_of_orcW {al : String → Bool} {k : ℕ} (h : VsOrcWFromCallees al k) :
    VsWindowsFromCallees al k :=
  fun hk hc seed => vsWindowsA_of_hypW (vsWinHypW_of_orcW (by omega) (h hk hc seed))

/-! ## The condition from `vsPostA_final` -/

set_option maxRecDepth 100000 in
theorem vs42_rc : vsRcs.lookup (.n 42) = none := by decide +kernel

set_option linter.constructorNameAsVariable false in
/-- **`vsKEndW` from `vsPostA_final`'s inputs** at the state the windows reach: the callees' posts against
`vsPs`' lists, the announced layout, the chunk count, the own witness entries' words, the bits and the windows. -/
theorem vsKEndW_of {k : ℕ} {bytecode : List K} {seed : Digest} {c : Child} {qt qo : ℕ} {rd0 : Reader}
    {w : ℕ → E} {args : List E} {layout : Layout} {rate : ℕ} {st : St} (ha : args.length = 6)
    (hann : announcedLayoutAndRate bytecode c.proof.stream = some (layout, rate))
    (h42 : w 42 = Prover.count (vsPadded c.proof.stream))
    (hQ : ∀ rd, LowDef k rd → vsPreA seed c qt qo rd → st.O rd →
      List.Forall₂ (fun Q P => ∀ t, Q rd t → PopsPost P rd t) st.Qs
        (vsPs (rdOver (vsVal rd0 w args) rd) (vsChunks c.proof.stream)
          (Prover.stackHints (stackKappas layout))
          (Prover.merkleHints true (Prover.childQueries bytecode seed c) c.proof.openings)))
    (h6 : ∀ rd, LowDef k rd → vsPreA seed c qt qo rd → st.O rd →
      (Dest.heap (.n 6) 0 6).words rd (rdOver (vsVal rd0 w args) rd) =
        layout.tableLogHeights.map Prover.count)
    (h9 : ∀ rd, LowDef k rd → vsPreA seed c qt qo rd → st.O rd →
      (Dest.heap (.n 9) 0 4).words rd (rdOver (vsVal rd0 w args) rd) = vsLinkShape layout)
    (h14 : ∀ rd, LowDef k rd → vsPreA seed c qt qo rd → st.O rd →
      (Dest.heap (.n 14) 0 36).words rd (rdOver (vsVal rd0 w args) rd) = c.freshClaim.values)
    (h240 : ∀ rd, LowDef k rd → vsPreA seed c qt qo rd → st.O rd →
      (Hint.bitsExp (.n 240) 24 (.heap (.n 8) 0 24)).Exact rd (vsVal rd0 w args))
    (hW : ∀ q ∈ vsWinL, ∀ i < q.2.2.2.1, w (q.2.2.2.2 + i) =
      ofK (g ^ ((wordNat (vsVal rd0 w args (.n q.1)) >>> (q.2.1 + i * q.2.2.1)) % 2 ^ q.2.2.1))) :
    vsKEndW k bytecode seed c qt qo (vsVal rd0 w args) st := by
  intro rd hl hp ho hw hh ts hv hq
  have h42' : rdOver (vsVal rd0 w args) rd (.n 42) = Prover.count (vsPadded c.proof.stream) := by
    rw [rdOver_eq vs42_rc, vsVal_42 ha, h42]
  -- The events as a variable: unifying `Tree.KidsValid … (calls (vsEs σ))` otherwise unfolds the walk.
  generalize vsEs (vsVal rd0 w args) = es at hw hh hv hq ⊢
  exact vsPostA_final ha hw hh hv hq (hQ rd hl hp ho) hann h42' (h6 rd hl hp ho) (h9 rd hl hp ho) (h14 rd hl hp ho)
    (h240 rd hl hp ho) hW

/-! ## The windows and the chunk count at the honest oracle -/

/-- **A low window of the honest grind** is the word's base-`2^11` window above bit `b`. -/
theorem gcWin_low {b j : ℕ} (hs : b + 11 * gcW b + gcTop b = 64) (x : E) (hj : j < gcW b) :
    gcWin b x j = ofK (g ^ ((wordNat x >>> (b + j * 11)) % 2 ^ 11)) := by
  unfold gcWin
  rw [show 2 + j = gcW b + 2 - (gcW b - j) by omega, gv_win (by omega) (by omega), wordNat_window _ (by omega),
    gen_pow_eq_ofK, gcV, show gcW b - (gcW b - j) = j by omega, Nat.mul_comm 11 j]

/-- **The top window of the honest grind**: the word's bits from `b + 11 · gcW b` on, below bit `64`. -/
theorem gcWin_top {b : ℕ} (hs : b + 11 * gcW b + gcTop b = 64) (x : E) :
    gcWin b x (gcW b) = ofK (g ^ ((wordNat x >>> (b + 11 * gcW b)) % 2 ^ gcTop b)) := by
  have hlt : kToNat (x.limb 0) / 2 ^ (b + 11 * gcW b) < 2 ^ gcTop b := gcV_zero_lt hs x
  unfold gcWin
  rw [Nat.add_comm 2 (gcW b), gv_top, wordNat_window _ (by omega), Nat.mod_eq_of_lt hlt, gen_pow_eq_ofK, gcV,
    Nat.sub_zero]

/-- **The six windows' words** (`vsWinL`) from the oracle's honest windows of the three grinded words. -/
theorem vsHW_of_gcWin {σ : Val} {w : ℕ → E}
    (h15 : ∀ j ≤ gcW 15, w (512 + j) = gcWin 15 (σ (.n 500)) j)
    (h2 : ∀ j ≤ gcW 2, w (581 + j) = gcWin 2 (σ (.n 574)) j)
    (h13 : ∀ j ≤ gcW 13, w (2943 + j) = gcWin 13 (σ (.n 2931)) j) :
    ∀ q ∈ vsWinL, ∀ i < q.2.2.2.1, w (q.2.2.2.2 + i) =
      ofK (g ^ ((wordNat (σ (.n q.1)) >>> (q.2.1 + i * q.2.2.1)) % 2 ^ q.2.2.1)) := by
  have w15 : gcW 15 = 4 := rfl
  have w2 : gcW 2 = 5 := rfl
  have w13 : gcW 13 = 4 := rfl
  have t15 : gcTop 15 = 5 := rfl
  have t2 : gcTop 2 = 7 := rfl
  have t13 : gcTop 13 = 7 := rfl
  intro q hq i hi
  simp only [vsWinL, List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl | rfl | rfl <;> dsimp only at hi ⊢
  · rw [h15 i (by omega), gcWin_low (by rw [w15, t15]) _ (by omega)]
  · obtain rfl : i = 0 := by omega
    have e := gcWin_top (b := 15) (by rw [w15, t15]) (σ (.n 500))
    rw [w15, t15] at e
    exact (h15 4 (by omega)).trans e
  · rw [h2 i (by omega), gcWin_low (by rw [w2, t2]) _ (by omega)]
  · obtain rfl : i = 0 := by omega
    have e := gcWin_top (b := 2) (by rw [w2, t2]) (σ (.n 574))
    rw [w2, t2] at e
    exact (h2 5 (by omega)).trans e
  · rw [h13 i (by omega), gcWin_low (by rw [w13, t13]) _ (by omega)]
  · obtain rfl : i = 0 := by omega
    have e := gcWin_top (b := 13) (by rw [w13, t13]) (σ (.n 2931))
    rw [w13, t13] at e
    exact (h13 4 (by omega)).trans e

set_option maxRecDepth 100000 in
theorem vsGrind_tIdx : tIdx vsRcs 500 = false ∧ tIdx vsRcs 574 = false ∧ tIdx vsRcs 2931 = false := by
  decide +kernel

section
variable {rd1 rd0 : Reader} {args : List E} {cur p : ℕ} {ret : ℕ → (ℕ → E) → E}

/-- **The honest oracle's grind windows**, on the evaluation memory `rd0` whose fresh loads read as `rd1`'s. -/
theorem vsW_gcWin (ha : args.length = 6) (hr : CausalRule ret) (hf : VsFresh rd1 rd0 (vsW rd1 args cur p ret) args) :
    (∀ j ≤ gcW 15, vsW rd1 args cur p ret (512 + j) =
      gcWin 15 (vsVal rd0 (vsW rd1 args cur p ret) args (.n 500)) j) ∧
    (∀ j ≤ gcW 2, vsW rd1 args cur p ret (581 + j) =
      gcWin 2 (vsVal rd0 (vsW rd1 args cur p ret) args (.n 574)) j) ∧
    (∀ j ≤ gcW 13, vsW rd1 args cur p ret (2943 + j) =
      gcWin 13 (vsVal rd0 (vsW rd1 args cur p ret) args (.n 2931)) j) := by
  obtain ⟨t500, t574, t2931⟩ := vsGrind_tIdx
  have w15 : gcW 15 = 4 := rfl
  have w2 : gcW 2 = 5 := rfl
  have w13 : gcW 13 = 4 := rfl
  refine ⟨fun j hj => ?_, fun j hj => ?_, fun j hj => ?_⟩
  · rw [← vsVal_congr ha hf (v := .n 500) t500, vsW_eq ha hr]
    have hn : 512 + j ∉ vsAllocIdx := by
      rw [w15] at hj; simp only [vsAllocIdx, List.mem_cons, List.not_mem_nil, or_false]; omega
    simp only [vsRule, hn, ↓reduceIte, show 512 + j ≠ 42 by omega,
      show 512 ≤ 512 + j ∧ 512 + j ≤ 516 by omega, and_self, Nat.add_sub_cancel_left]
  · rw [← vsVal_congr ha hf (v := .n 574) t574, vsW_eq ha hr]
    have hn : 581 + j ∉ vsAllocIdx := by
      rw [w2] at hj; simp only [vsAllocIdx, List.mem_cons, List.not_mem_nil, or_false]; omega
    simp only [vsRule, hn, ↓reduceIte, show 581 + j ≠ 42 by omega,
      show ¬(512 ≤ 581 + j ∧ 581 + j ≤ 516) by omega,
      show 581 ≤ 581 + j ∧ 581 + j ≤ 586 by omega, and_self, Nat.add_sub_cancel_left]
  · rw [← vsVal_congr ha hf (v := .n 2931) t2931, vsW_eq ha hr]
    have hn : 2943 + j ∉ vsAllocIdx := by
      rw [w13] at hj; simp only [vsAllocIdx, List.mem_cons, List.not_mem_nil, or_false]; omega
    simp only [vsRule, hn, ↓reduceIte, show 2943 + j ≠ 42 by omega,
      show ¬(512 ≤ 2943 + j ∧ 2943 + j ≤ 516) by omega, show ¬(581 ≤ 2943 + j ∧ 2943 + j ≤ 586) by omega,
      show 2943 ≤ 2943 + j ∧ 2943 + j ≤ 2947 by omega, and_self, Nat.add_sub_cancel_left]

set_option linter.constructorNameAsVariable false in
/-- **`vsKEndW` at the honest oracle**: the chunk count and the windows by the rule; what is left is the callees'
posts against `vsPs`, the own witness entries' words and the bits. -/
theorem vsKEndW_honest {k : ℕ} {bytecode : List K} {seed : Digest} {c : Child} {qt qo : ℕ} {layout : Layout}
    {rate : ℕ} {st : St} (ha : args.length = 6) (hr : CausalRule ret)
    (hf : VsFresh rd1 rd0 (vsW rd1 args cur (chunksOf c.proof.stream.length) ret) args)
    (hann : announcedLayoutAndRate bytecode c.proof.stream = some (layout, rate))
    (hQ : ∀ rd, LowDef k rd → vsPreA seed c qt qo rd → st.O rd →
      List.Forall₂ (fun Q P => ∀ t, Q rd t → PopsPost P rd t) st.Qs
        (vsPs (rdOver (vsVal rd0 (vsW rd1 args cur (chunksOf c.proof.stream.length) ret) args) rd)
          (vsChunks c.proof.stream) (Prover.stackHints (stackKappas layout))
          (Prover.merkleHints true (Prover.childQueries bytecode seed c) c.proof.openings)))
    (h6 : ∀ rd, LowDef k rd → vsPreA seed c qt qo rd → st.O rd →
      (Dest.heap (.n 6) 0 6).words rd (rdOver (vsVal rd0 (vsW rd1 args cur (chunksOf c.proof.stream.length) ret)
        args) rd) = layout.tableLogHeights.map Prover.count)
    (h9 : ∀ rd, LowDef k rd → vsPreA seed c qt qo rd → st.O rd →
      (Dest.heap (.n 9) 0 4).words rd (rdOver (vsVal rd0 (vsW rd1 args cur (chunksOf c.proof.stream.length) ret)
        args) rd) = vsLinkShape layout)
    (h14 : ∀ rd, LowDef k rd → vsPreA seed c qt qo rd → st.O rd →
      (Dest.heap (.n 14) 0 36).words rd (rdOver (vsVal rd0 (vsW rd1 args cur (chunksOf c.proof.stream.length) ret)
        args) rd) = c.freshClaim.values)
    (h240 : ∀ rd, LowDef k rd → vsPreA seed c qt qo rd → st.O rd →
      (Hint.bitsExp (.n 240) 24 (.heap (.n 8) 0 24)).Exact rd
        (vsVal rd0 (vsW rd1 args cur (chunksOf c.proof.stream.length) ret) args)) :
    vsKEndW k bytecode seed c qt qo (vsVal rd0 (vsW rd1 args cur (chunksOf c.proof.stream.length) ret) args) st := by
  obtain ⟨w15, w2, w13⟩ := vsW_gcWin ha hr hf
  exact vsKEndW_of ha hann (vsW_42 ha hr) hQ h6 h9 h14 h240 (vsHW_of_gcWin w15 w2 w13)

end

end
end LeanVM.Guest.B1.VsC
