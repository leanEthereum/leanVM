/-
  LeanVM.Guest.B1.Place.LqProof

  `level_queries` complete placed, at every specialization of `lqTable`: the proof.
-/

module

public import LeanVM.Guest.B1.Place.LqBound
public import LeanVM.Guest.B1.Place.OsPlaceB
public import LeanVM.Guest.B1.Place.OsKidsB

/-!
# `level_queries`, placed: the proof

`lq_completeAtB`: the straight-line body (`os_completeAt_placeJB`) at the honest valuation
(`lqVal`, its cap and flags at the allocator's pointers), its two buffers the honest cap and
flags, its two callees in sequence (`os_kids_blockB`): `verify_merkle_cap` within its frame
(`vmc_completeAtB`), `opening_queries` within `oqBound` (`opening_queries_completeAtB`, its words
`oqLinMem_of`, `oqLinReg_of`); so within `lqBnd` words. `level_queries_completeAt`: at `Bd = some B`,
`B` bounds the valid trees, so `lqBnd ≤ B` (`lqBnd_le`).
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Memory
open LeanVM.Guest.B1.Main (Layout MemL RegionL)
open LeanVM.Guest.B1.Whir (lqIters lqTable natStr oqName digitsVal osPowDigits osPowLen lqBody
  lqAtoms lqVal lqOqArgs lqVal_facts lqVal_holds lqAtoms_straight lqAtoms_addrs lqAtoms_calls
  lqAtoms_allocs lqBody_atoms FnIs osParams gw lqTable_ok)
open LeanVM.Protocol LeanVM.Protocol.KeccakHash
open LeanVM.Protocol.Verifier hiding Layout

@[expose] public section

theorem regionL_append_right {L L' : Layout} {i : ℕ} (h : RegionL L' i) : RegionL (L ++ L') i :=
  let ⟨q, hq, h1, h2⟩ := h
  ⟨q, List.mem_append_right _ hq, h1, h2⟩

theorem regionL_append_left {L L' : Layout} {i : ℕ} (h : RegionL L i) : RegionL (L ++ L') i :=
  let ⟨q, hq, h1, h2⟩ := h
  ⟨q, List.mem_append_left _ hq, h1, h2⟩

theorem regionL_append {L L' : Layout} {i : ℕ} (h : RegionL (L ++ L') i) :
    RegionL L i ∨ RegionL L' i := by
  obtain ⟨q, hq, h1, h2⟩ := h
  rcases List.mem_append.mp hq with hq | hq
  · exact Or.inl ⟨q, hq, h1, h2⟩
  · exact Or.inr ⟨q, hq, h1, h2⟩

theorem lq_bufL (b x y : ℕ) (capW flW : List E) :
    bufL b [x, y] [capW, flW] = [(b, capW), (b + x, flW)] := by
  simp [bufL, bases]

/-- **`level_queries` at an entry of `lqTable` is complete placed within `lqBnd` words.** -/
theorem lq_completeAtB (fs : String → ℕ) (cert : String → V → ℕ) (κ : ℕ) {name : String}
    {q base il leaf d cd : ℕ} (he : LqEntry q base il leaf d cd)
    (hfn : FnIs name (osParams 3) (lqBody q base il leaf d cd)) (Lin : Layout) (eqp ewp : ℕ)
    {lam : E} (w : ℕ → E) (eb qs : ℕ → ℕ) (rows : ℕ → List K) (sibs : ℕ → List Digest)
    (capW flW : List E) (r0 r1 : E) (hlam : lam ≠ 0)
    (hcaps : LqCaps (lqShape base il d cd) q capW flW r0 r1 qs rows sibs)
    (hreg : LqReg (RegionL Lin) (lqShape base il d cd) q eqp ewp eb)
    (hmem : ∀ rd, LowDef κ rd → MemL rd Lin → LqMem rd (lqShape base il d cd) q eqp ewp w eb qs) :
    CompleteAtB fs cert κ name Lin [lam, ofK (addressOfIndex eqp), ofK (addressOfIndex ewp)]
      (Returns [r0, r1, oqChain (q % 2 * base) base lam⁻¹ (fun k ↦ rowDot base il (rows k) w)
        (lqIters q base) * lam ^ q, lam ^ q]) (lqBnd fs name q base il leaf d cd) := by
  have hoqm := he.oqMem
  obtain ⟨hvmc, -, hb1, hcd1, -, hcd8, hpw, hne, hsize⟩ := he
  obtain ⟨fn, hf, hps, hbody⟩ := hfn
  have hscd : (lqShape base il d cd).cd = cd := rfl
  have hcd1' : 1 ≤ (lqShape base il d cd).cd := hcd1
  have hP : 0 < 2 ^ cd := by positivity
  set N := lqIters q base with hN
  set oqN := oqName q base il leaf d cd with hoqN
  set sum := oqChain (q % 2 * base) base lam⁻¹ (fun k ↦ rowDot base il (rows k) w) N * lam ^ q
  have hN1 : N + 1 < ordG := lt_of_le_of_lt (Nat.le_add_left _ _) hsize
  have hgw : gw N = gen ^ N := Whir.gw_eq (by unfold u128Bound; rw [ordG_eq] at hN1; omega)
  have hcount : oqCount (q % 2 * base) (lqShape base il d cd).base N = q := lq_count hb1
  have hl : coreProgram.loop name = false := by
    rw [Program.loop_of_find? hf, Fn.loop, hbody, lqBody_atoms]
    simp [List.reverse_append]
  have hb' : fn.body = lqAtoms q base il leaf d cd ++ [.ret [.n (9 + osPowLen q + 2),
      .n (9 + osPowLen q + 3), .n (9 + osPowLen q + 4), .n (9 + osPowLen q + 5)]] := by
    rw [hbody, lqBody_atoms]
  have hbound : fs name + [4 * 2 ^ cd, 2 ^ cd].sum +
      (fs (vmcName cd) + oqBound fs oqN (oqLoopOf oqN) N) ≤ lqBnd fs name q base il leaf d cd := by
    simp [lqBnd, oqN, N]
  refine (os_completeAt_placeJB (C := fun _ _ _ ↦ True) hf hl κ Lin _ _ hb'
    (lqAtoms_straight q base il leaf d cd) (lqAtoms_addrs q base il leaf d cd)
    [4 * 2 ^ cd, 2 ^ cd] [] List.nodup_nil (by simp)
    (fs (vmcName cd) + oqBound fs oqN (oqLoopOf oqN) N) fun fp ↦ ?_).mono le_rfl hbound
  set b := fp + fs name
  set CAP := ofK (addressOfIndex b)
  set FL := ofK (addressOfIndex (b + 4 * 2 ^ cd))
  obtain ⟨a0, a1, a2, a3, a4, a5, a6, a7, a8, e0, e1, e2, e3, e4, e5, hp2, -⟩ :=
    lqVal_facts (C := fun _ _ _ ↦ True) (rd := fun _ ↦ none) q cd N hpw lam
      (ofK (addressOfIndex eqp)) (ofK (addressOfIndex ewp)) CAP FL r0 r1 sum
  set σ := lqVal q cd N lam (ofK (addressOfIndex eqp)) (ofK (addressOfIndex ewp)) CAP FL r0 r1 sum
  set own : List (List E) := [capW, flW]
  set Lk : Layout := bufL b [4 * 2 ^ cd, 2 ^ cd] own ++ Lin
  have hLk : Lk = [(b, capW), (b + 4 * 2 ^ cd, flW)] ++ Lin := by
    simp only [Lk, own, lq_bufL]
  obtain ⟨hcl, hfll, hvr, hq⟩ := hcaps
  have hcaps : LqCaps (lqShape base il d cd) q capW flW r0 r1 qs rows sibs := ⟨hcl, hfll, hvr, hq⟩
  -- the cap and the flags on a memory holding `Lk`
  have hcapM : ∀ rd, MemL rd Lk → ReadsAt rd CAP capW ∧ ReadsAt rd FL flW := fun rd hm ↦ by
    rw [hLk] at hm
    exact ⟨hm (b, capW) (by simp), hm (b + 4 * 2 ^ cd, flW) (by simp)⟩
  set Bk : String → ℕ := fun f ↦ if f = vmcName cd then fs (vmcName cd) else
    oqBound fs oqN (oqLoopOf oqN) N
  set cs := ((lqAtoms q base il leaf d cd).filterMap Main.Stmt.callS).map (Main.mkCall σ)
  have hcs : cs = [⟨vmcName cd, [.n 4, .n 6], [.n 7, .n 8], true⟩,
      ⟨oqN, lqOqArgs q, [.n (9 + osPowLen q + 1)], true⟩] := by
    simp only [cs, lqAtoms_calls, List.map_cons, List.map_nil, Main.mkCall]
    rfl
  have hkid : ∀ c ∈ cs, c.taken = true →
      CompleteAtB fs cert κ c.f Lk (c.args.map σ) (Returns (c.rets.map σ)) (Bk c.f) := by
    rw [hcs]
    intro c hc _
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hc
    rcases hc with rfl | rfl
    · simp only [Bk, List.map_cons, List.map_nil, a4, a6, a7, a8, ↓reduceIte]
      exact vmc_completeAtB fs cert κ hvmc fun rd hm ↦
        hvr rd CAP FL (hcapM rd hm).1 (hcapM rd hm).2
    · simp only [Bk, hne, ↓reduceIte, List.map_cons, List.map_nil, lqOqArgs, a4, a6, a0, a1, a2,
        hp2, e0, e1, hgw]
      refine (opening_queries_completeAtB fs cert _ hoqm trivial κ Lk N b (b + 4 * 2 ^ cd) eqp ewp
        lam (lam ^ q) w eb qs rows sibs hN1 hlam ?_ ?_ ?_).toB
      · rw [hcount]; exact fun k hk ↦ ⟨(hq k hk).1, (hq k hk).2.1, (hq k hk).2.2.1⟩
      · rw [hcount]
        refine oqLinReg_of hcaps hcd1'
          ⟨fun l hl ↦ regionL_append_right (hreg.1 l hl), fun k hk ↦
            ⟨regionL_append_right (hreg.2 k hk).1, fun i hi ↦ regionL_append_right ((hreg.2 k hk).2 i hi)⟩⟩
          (fun j hj ↦ ?_) (fun j hj ↦ ?_)
        · rw [hLk]
          have h2 : b + j < b + capW.length := by rw [hcl]; rw [hscd] at hj ⊢; omega
          exact regionL_append_left ⟨(b, capW), by simp, Nat.le_add_right _ _, h2⟩
        · rw [hLk]
          have h2 : b + 4 * 2 ^ cd + j < b + 4 * 2 ^ cd + flW.length := by
            rw [hfll]; rw [hscd] at hj ⊢; omega
          exact regionL_append_left ⟨(b + 4 * 2 ^ cd, flW), by simp, Nat.le_add_right _ _, h2⟩
      · rw [hcount]
        intro rd hlow hm
        have hLin : MemL rd Lin := fun x hx ↦ hm x (List.mem_append_right _ hx)
        obtain ⟨hc, hfl⟩ := hcapM rd hm
        refine oqLinMem_of hcaps hcd1' (hmem rd hlow hLin) (fun j hj ↦ ?_) (fun j hj ↦ ?_)
        · exact at_of_readsAt hc (by rw [hcl]; exact hj)
        · exact at_of_readsAt hfl (by rw [hfll]; exact hj)
  obtain ⟨Nk, L, hW, hD, hNk, hK⟩ := os_kids_blockB (fs := fs) (cert := cert) κ Lk σ cs Bk hkid
    (fp + fs name + [4 * 2 ^ cd, 2 ^ cd].sum)
  refine ⟨σ, own, _, Nk, L, fun _ ↦ False, cs, rfl, ?_, ?_, ⟨rfl, rfl⟩, hW, hD, ?_, ?_, ?_⟩
  · have hfo : fs oqN ≤ oqBound fs oqN (oqLoopOf oqN) N := by unfold oqBound; omega
    rw [hcs] at hNk
    simp only [Bk, hne, ↓reduceIte, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
      max_self] at hNk
    rw [max_eq_right hfo] at hNk
    omega
  · simp only [own, List.forall₂_cons, List.Forall₂.nil, and_true]
    exact ⟨le_of_eq hcl, le_of_eq hfll⟩
  · rw [hps]
    simp only [osParams, List.range_succ, List.range_zero, List.map_cons, List.map_nil,
      List.nil_append, List.cons_append, a0, a1, a2]
  · intro rd _ _ _
    refine ⟨?_, ?_, ?_⟩
    · rw [hbody]
      exact lqVal_holds (C := fun _ _ _ ↦ True) q base il leaf d cd hpw trivial trivial
    · rw [lqAtoms_allocs]
      have hc : 2 ^ cd ≤ 2 ^ 8 := Nat.pow_le_pow_right (by decide) hcd8
      simp only [List.map_cons, List.map_nil, Sum.elim_inr, a3, a5]
      rw [lqLogG_gw (by omega), lqLogG_gw (by omega)]
    · rw [lqAtoms_allocs]
      simp only [List.map_cons, List.map_nil, bases, a4, a6, CAP, FL, b]
  · intro rd hlow hB hL hLin
    have hLk' : MemL rd Lk := Main.memL_append.mpr ⟨hB, hLin⟩
    exact hK rd _ (fun _ ↦ False) hlow hL hLk' fun i hi ↦ Or.inl
      ((regionL_append hi).elim Or.inr Or.inl)

/-- **`level_queries` is complete placed at every specialization.** -/
theorem level_queries_completeAt : level_queries_completeAt_Spec := by
  intro fs cert κ _ _ _ e he Bd Lin eqp ewp lam w eb qs rows sibs capW flW r0 r1 hlam hcaps hreg
    hmem hBd
  have hent := lqTable_entry e he
  have hfn := lqTable_ok e he
  have hB := lq_completeAtB fs cert κ hent hfn Lin eqp ewp w eb qs rows sibs capW flW r0 r1 hlam
    hcaps hreg hmem
  intro fp
  obtain ⟨n, Lown, rets, Lout, ho, hw, hd, hn, hr⟩ := hB fp
  exact ⟨n, Lown, rets, Lout, ho, hw, hd,
    fun B hBm ↦ le_trans hn (lqBnd_le fs cert hent hfn hlam w hcaps (hBd B hBm)), hr⟩

end
end LeanVM.Guest.B1
