/-
  LeanVM.Guest.B1.Place.LqBound

  Every bound of `level_queries`' valid trees is at least `lqBnd`.
-/

module

public import LeanVM.Guest.B1.Place.LqFresh

/-!
# The bound from a fresh instance

`lqBnd_le`: on the honest cap and flags, a bound `B` of every valid tree of `level_queries`
(`TotalLe`) is at least `lqBnd`. The fresh instance lays the words `opening_queries` reads from
`g^0` (`frV`) in the memory `cellRd`, the chain buffer of `opening_queries` placed where its
index wraps onto them (`addressOfIndex_ordG`); `opening_queries` placed there is a tree of exactly
`oqBound` words (`OqCompleteDB`), `verify_merkle_cap` a tree of at least its frame, and their node
(`lq_node`) a valid tree of `level_queries` of at least `lqBnd` words.
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Memory
open LeanVM.Guest.B1.Main (Layout MemL RegionL)
open LeanVM.Guest.B1.Whir (lqIters lqTable natStr oqName digitsVal osPowDigits lqBody FnIs
  osParams gw)
open LeanVM.Protocol LeanVM.Protocol.KeccakHash
open LeanVM.Protocol.Verifier hiding Layout

@[expose] public section

theorem ordG_eq : ordG = 18446744073709551615 := by decide

theorem getD_range_map (v : ℕ → E) {n i : ℕ} (hi : i < n) :
    ((List.range n).map v).getD i 0 = v i := by
  rw [List.getD_eq_getElem _ _ (by simpa using hi), List.getElem_map, List.getElem_range]

/-- **A bound of `level_queries`' valid trees is at least `lqBnd`**, on the honest cap and flags. -/
theorem lqBnd_le (fs : String → ℕ) (cert : String → V → ℕ) {name : String}
    {q base il leaf d cd : ℕ} (he : LqEntry q base il leaf d cd)
    (hfn : FnIs name (osParams 3) (lqBody q base il leaf d cd)) {lam : E} (hlam : lam ≠ 0)
    (w : ℕ → E) {qs : ℕ → ℕ} {rows : ℕ → List K} {sibs : ℕ → List Digest} {capW flW : List E}
    {r0 r1 : E} (hcaps : LqCaps (lqShape base il d cd) q capW flW r0 r1 qs rows sibs) {B : ℕ}
    (hB : TotalLe coreProgram fs name (fun _ ↦ B)) : lqBnd fs name q base il leaf d cd ≤ B := by
  have hoqm := he.oqMem
  obtain ⟨hvmc, -, hb1, hcd1, hcdd, hcd8, hpw, -, hsize⟩ := he
  obtain ⟨s, hs⟩ : ∃ s, s = lqShape base il d cd := ⟨_, rfl⟩
  have hscd : s.cd = cd := by rw [hs]; rfl
  have hspd : s.pd + s.cd = d := by rw [hs]; simp only [lqShape]; omega
  rw [← hs] at hcaps hoqm
  have hP : 0 < 2 ^ cd := by positivity
  set N := lqIters q base with hN
  set oqN := oqName q base il leaf d cd
  set ds : ℕ → E := fun k ↦ rowDot s.base s.I (rows k) w
  set chain := oqChainVals (q % 2 * base) s.base lam ds N with hchain
  set v := frV s q w qs capW flW chain with hv
  have hS : frCh s q + (N + 1) < ordG := by
    have : frCh s q + (N + 1) = lqFreshSize q base il d cd := by
      rw [hs]
      simp only [frCh, frFl, frC, frW, frQn, lqFreshSize, lqShape, Nat.sub_add_cancel hcdd]
      rfl
    omega
  set S := frCh s q + (N + 1)
  set rd := cellRd S v
  have hR : ∀ i < S, rd (addressOfIndex i) = some (v i) := fun i hi ↦ cellRd_at v hS.le hi
  obtain ⟨hcl, hfll, hvr, hq⟩ := hcaps
  have hcaps : LqCaps s q capW flW r0 r1 qs rows sibs := ⟨hcl, hfll, hvr, hq⟩
  have hfr : frCh s q = frFl s q + 2 ^ cd := by rw [frCh, hscd]
  have hfc : frFl s q = frC s q + 4 * 2 ^ cd := by rw [frFl, hscd]
  have hWC : frW s + q + q * frQn s = frC s q := rfl
  have hWd : frW s = s.lo + s.I / s.lo := rfl
  -- the cap and the flags in the fresh memory
  have hcapR : ∀ j < 4 * 2 ^ s.cd, rd (addressOfIndex (frC s q + j)) = some (capW.getD j 0) :=
    fun j hj ↦ by rw [hR _ (by rw [hscd] at hj; omega), hv, frV_cap hj]
  have hflR : ∀ j < 2 ^ s.cd, rd (addressOfIndex (frFl s q + j)) = some (flW.getD j 0) :=
    fun j hj ↦ by rw [hR _ (by rw [hscd] at hj; omega), hv, frV_fl hj]
  -- `verify_merkle_cap`
  have hvRel := hvr rd (ofK (addressOfIndex (frC s q))) (ofK (addressOfIndex (frFl s q)))
    (readsAt_of_at fun k hk ↦ hcapR k (by rw [hcl] at hk; exact hk))
    (readsAt_of_at fun k hk ↦ hflR k (by rw [hfll] at hk; exact hk))
  obtain ⟨t1, hn1, hv1, hb1'⟩ := Program.Rel.tree coreProgram_wf hvRel
  -- `opening_queries`, its words from `g^0`
  set Lo : Layout := [(0, (List.range (frCh s q)).map v)]
  have hLoReg : ∀ i < frCh s q, RegionL Lo i := fun i hi ↦
    ⟨_, List.mem_singleton_self _, Nat.zero_le _, by simpa using hi⟩
  have hmemOf : ∀ rd' : Reader, (∀ i < frCh s q, rd' (addressOfIndex i) = some (v i)) →
      OqLinMem rd' s (ofK (addressOfIndex (frC s q))) (ofK (addressOfIndex (frFl s q)))
        (ofK (addressOfIndex 0)) (ofK (addressOfIndex (frW s))) w (frEb s q) qs rows sibs q := by
    intro rd' h
    refine oqLinMem_of hcaps (by rw [hscd]; exact hcd1) ⟨fun l hl ↦ ?_, fun k hk ↦ ⟨?_, fun i hi ↦ ?_⟩⟩
      (fun j hj ↦ ?_) (fun j hj ↦ ?_)
    · rw [loadHolds_addr, Nat.zero_add, h _ (by omega), hv, frV_w (by omega)]
    · rw [loadHolds_addr, h _ (by omega), hv, frV_p hk]
    · have hlt : frEb s q k + i < frC s q := by
        unfold frEb frC
        have : k * frQn s + i < q * frQn s := by
          calc k * frQn s + i < k * frQn s + frQn s := by unfold frQn; omega
            _ = (k + 1) * frQn s := by ring
            _ ≤ q * frQn s := Nat.mul_le_mul_right _ hk
        omega
      rw [loadHolds_addr, h _ (by omega), hv, frV_win hk hi]
    · rw [h _ (by rw [hscd] at hj; omega), hv, frV_cap hj]
    · rw [h _ (by rw [hscd] at hj; omega), hv, frV_fl hj]
  have hcount : oqCount (q % 2 * base) s.base N = q := by rw [hs]; exact lq_count hb1
  have hoq := opening_queries_completeAtB fs cert _ hoqm trivial 0 Lo N (frC s q) (frFl s q)
    (frW s) 0 lam (lam ^ q) w (frEb s q) qs rows sibs (by omega) hlam
    (by rw [hcount]; exact fun k hk ↦ ⟨(hq k hk).1, (hq k hk).2.1, (hq k hk).2.2.1⟩)
    (by
      rw [hcount]
      refine oqLinReg_of hcaps (by rw [hscd]; exact hcd1) ⟨fun l hl ↦ hLoReg _ ?_, fun k hk ↦
        ⟨hLoReg _ ?_, fun i hi ↦ hLoReg _ ?_⟩⟩ (fun j hj ↦ hLoReg _ ?_) (fun j hj ↦ hLoReg _ ?_)
      · omega
      · omega
      · have : k * frQn s + i < q * frQn s := by
          calc k * frQn s + i < k * frQn s + frQn s := by unfold frQn; omega
            _ = (k + 1) * frQn s := by ring
            _ ≤ q * frQn s := Nat.mul_le_mul_right _ hk
        unfold frEb; omega
      · rw [hscd] at hj; omega
      · rw [hscd] at hj; omega)
    (by
      rw [hcount]
      intro rd' _ hm
      refine hmemOf rd' fun i hi ↦ ?_
      have := at_of_readsAt (hm _ (List.mem_singleton_self _)) (k := i) (by simpa using hi)
      rwa [Nat.zero_add, getD_range_map v hi] at this)
  obtain ⟨-, -, hr⟩ := hoq (frCh s q + (ordG - 1) * fs oqN)
  have hchainM : MemL rd ([(frCh s q + (ordG - 1) * fs oqN + fs oqN, chain)] ++ Lo) := by
    rw [Main.memL_append]
    refine ⟨fun x hx ↦ ?_, fun x hx ↦ ?_⟩
    · rw [List.mem_singleton] at hx
      subst hx
      refine readsAt_of_at fun k hk ↦ ?_
      have hk' : k < N + 1 := by simpa [hchain, oqChainVals] using hk
      rw [show frCh s q + (ordG - 1) * fs oqN + fs oqN + k = (frCh s q + k) + ordG * fs oqN by
        rw [ordG_eq]; omega, addressOfIndex_ordG, hR _ (by omega), hv, frV_ch]
    · rw [List.mem_singleton] at hx
      subst hx
      refine readsAt_of_at fun k hk ↦ ?_
      have hk' : k < frCh s q := by simpa using hk
      rw [Nat.zero_add, hR _ (by omega), getD_range_map v hk']
  obtain ⟨t2, hn2, hv2, hb2, -, ht2, -⟩ := hr rd (cellRd_low S v 0) hchainM
  have hgw : gw N = gen ^ N := Whir.gw_eq (by unfold u128Bound; rw [ordG_eq] at hS; omega)
  obtain ⟨hn, hvt, hbt, htot⟩ := lq_node fs hfn hpw hcd8 (rd := rd) (lam := lam)
    (WP := ofK (addressOfIndex (frW s))) (RW := ofK (addressOfIndex 0))
    (by rw [hn1, hscd]; rfl) hv1 hb1' hn2
    (by rw [hgw]; exact hv2) hb2
  have hle := hB rd _ _ _ hn hvt hbt
  have h1 : fs (vmcName cd) ≤ t1.total fs := by
    have := le_total (fs := fs) t1
    rw [hn1, hscd] at this
    exact this
  simp only at hle
  rw [htot] at hle
  unfold lqBnd
  rw [← ht2]
  omega

end
end LeanVM.Guest.B1
