/-
  LeanVM.Guest.B1.VerifySub.Bus

  `verify_sub`'s bus challenges (G:3611-3621): the bus grind, the sixteen slot weights and `β`.
-/

module

public import LeanVM.Guest.B1.VerifySub.Ood
public import LeanVM.Guest.B1.VerifySub.Known
public import LeanVM.Guest.B1.VerifySub.Split
public import LeanVM.Guest.B1.Bits.BusGrind

/-!
# The bus challenges

`vsBusFpw_holds`: the bus depth `g^μ` is at least `g^20` (`g^(μ - 20)` range-checked below
`g^14`), `bus_grind_check__L{μ - 20}` checks the proof of work of the nonce's permutation, whose
challenge is the first slot weight; fifteen squeezes give the others, one more `β`:
`busChallenges μ` runs on the nonce.
-/

namespace LeanVM.Guest.B1.VerifySub

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

variable {C : CallRel} {rd : Reader} {σ : Val} {next : Prop} {kret : List E → Prop}

theorem vsGinvBus_mul : vsGinvBus * gen ^ 20 = 1 := by
  rw [show vsGinvBus = ofK (K.ofBits 14347465658197868555) by rw [vsGinvBus, word_eOfNat]; rfl,
    gen_pow_eq_ofK, ← kn_ofK_mul,
    show K.ofBits 14347465658197868555 * Parameters.addressOfIndex 20 = 1 by decide +kernel]
  exact map_one (algebraMap K E)

theorem word_g13 : word 8192 0 = gen ^ 13 := by
  rw [show (8192 : ℕ) = 2 ^ 13 from rfl]; exact word_two_pow (by norm_num)

theorem vsBgName_eq {d : ℕ} (hd : d < 14) (h : d < vsBgNames.length) :
    vsBgNames[d] = busGrindName d := by
  interval_cases d <;> rfl

/-- Five words from `b`. -/
theorem vsRun5 (b : ℕ) : (vsRun b 5).map σ =
    [σ (.n b), σ (.n (b + 1)), σ (.n (b + 2)), σ (.n (b + 3)), σ (.n (b + 4))] := rfl

/-- One slot weight's squeeze and store. -/
def vsFpwBlk (i : ℕ) : List Stmt :=
  vsSqzT (330 + 14 * i) (336 + 14 * i) ++ [vsLd (349 + 14 * i) 335 (i + 1)]

/-- **The slot weights' squeezes**: after `n` of them the sponge's capacity is at `330 + 14 n`,
and squeeze `i` is at `349 + 14 i`, stored at `fp_w[i + 1]`. -/
theorem fpw_loop (h8 : σ (.n 8) = 0) (h9 : σ (.n 9) = 0) (h10 : σ (.n 10) = 0)
    (h11 : σ (.n 11) = 0) : ∀ (n : ℕ) {nx : Prop},
    Stmt.HoldsList C rd σ ((List.range n).flatMap vsFpwBlk) nx kret →
      sqSt ⟨(vsRun 330 5).map σ, []⟩ n = ⟨(vsRun (330 + 14 * n) 5).map σ, []⟩ ∧
        (∀ i < n, (sqSt ⟨(vsRun 330 5).map σ, []⟩ i).squeeze.1 = σ (.n (349 + 14 * i)) ∧
          LoadHolds rd (σ (.n 335)) (i + 1) (σ (.n (349 + 14 * i)))) ∧ nx := by
  intro n
  induction n with
  | zero => exact fun h ↦ ⟨rfl, fun i hi ↦ absurd hi (by omega), h⟩
  | succ n ih =>
    intro nx h
    rw [List.range_succ, List.flatMap_append, holdsList_append] at h
    obtain ⟨hs, hi, h'⟩ := ih h
    rw [List.flatMap_singleton, vsFpwBlk, holdsList_append] at h'
    obtain ⟨hsq, h''⟩ := vsSqzT_holds h8 h9 h10 h11 h'
    obtain ⟨hl, hn⟩ := holds_ld1.1 h''
    have e13 : 336 + 14 * n + 13 = 349 + 14 * n := by omega
    refine ⟨?_, fun i hi' ↦ ?_, hn⟩
    · rw [sqSt, hs, hsq, show 336 + 14 * n + 8 = 330 + 14 * (n + 1) by omega,
        show 336 + 14 * n + 9 = 330 + 14 * (n + 1) + 1 by omega,
        show 336 + 14 * n + 10 = 330 + 14 * (n + 1) + 2 by omega,
        show 336 + 14 * n + 11 = 330 + 14 * (n + 1) + 3 by omega,
        show 336 + 14 * n + 12 = 330 + 14 * (n + 1) + 4 by omega, vsRun5]
    · rcases Nat.lt_succ_iff_lt_or_eq.1 hi' with hi' | rfl
      · exact hi i hi'
      · refine ⟨?_, hl⟩
        rw [hs, hsq, ← e13]

/-- **The bus challenges** (G:3611-3621). -/
theorem vsBusFpw_holds {κ : ℕ} (hκ : κ ≤ 32) (hκw : winTabBits ≤ κ) (L : MemoryImage κ)
    (hC : CallRel.Le C (coreProgram.Rel L.read)) (hwin : ExpWinTab L.read (σ (.n 4)))
    (h8 : σ (.n 8) = 0) (h9 : σ (.n 9) = 0) (h10 : σ (.n 10) = 0) (h11 : σ (.n 11) = 0)
    {μ : ℕ} (hμ : μ < 34) (h253 : σ (.n 253) = gen ^ μ)
    {s : Fs} {nn : E}
    (hS : [σ (.n 313), σ (.n 314), σ (.n 315), σ (.n 316), σ (.n 317), σ (.n 318), σ (.n 319)] =
      [cellsOfState (s.nonceState nn) false 0, cellsOfState (s.nonceState nn) false 1] ++
        capOf (s.nonceState nn))
    (h : Stmt.HoldsList C L.read σ (vsBusGrindT ++ vsFpwT) next kret) :
    20 ≤ μ ∧ ∃ weights : List E, weights.length = 16 ∧ ReadsAt L.read (σ (.n 335)) weights ∧
      RunsTo (busChallenges μ) s [nn] (weights, σ (.n 559))
        ⟨[σ (.n 554), σ (.n 555), σ (.n 556), σ (.n 557), σ (.n 558)], []⟩ ∧ next := by
  have hκ6 : 6 ≤ κ := by simp only [winTabBits] at hκw; omega
  rw [holdsList_append, vsBusGrindT, holdsList_append, holdsList_append] at h
  simp only [Stmt.HoldsList, Stmt.Holds, vsConst, vsMul, vsRange, Atom.Holds] at h
  obtain ⟨e321, m322, e323, r322, h⟩ := h
  obtain ⟨h328, h⟩ := vsTabsT_holds h
  simp only [List.map_cons, List.map_nil] at h
  obtain ⟨⟨j, hj, hj322, hbg⟩, h⟩ := h
  -- the depth
  obtain ⟨e, he, h322⟩ := rc_pow hκ L (a := 13) (by norm_num) (by rw [e323, word_g13]) r322
  have hμe : μ = e + 20 := by
    have h1 : gen ^ (e + 20) = gen ^ μ := by
      rw [pow_add, ← h322, m322, h253, e321, mul_assoc, vsGinvBus_mul, mul_one]
    exact (gen_pow_inj (by omega) (by omega) h1).symm
  have hje : j = e := by
    rw [h322, gen_pow_eq_ofK] at hj322
    exact (gen_pow_inj (by simp [vsBgNames] at hj; omega) (by omega)
      (by rw [gen_pow_eq_ofK, gen_pow_eq_ofK]; exact hj322.symm))
  subst hje
  -- the grind
  rw [vsBgName_eq (by omega) hj] at hbg
  have hwt : WinTabs L.read (σ (.n 328)) := by rw [h328]; exact winTabs_of_expWinTab hwin
  obtain ⟨-, hpow⟩ := (bus_grind_check_holds j (List.mem_range.2 (by omega)) hκ hκw L _ _ hwt _).1
    (hC _ _ _ hbg)
  have hbits : busGrindBits j = busGrindingBits μ := by
    rw [busGrindBits, show busMinMu + j = μ by simp only [busMinMu]; omega]
  have hb0 : busGrindingBits μ ≠ 0 := by rw [← hbits, busGrindBits_eq]; omega
  simp only [List.cons_append, List.nil_append, List.cons.injEq] at hS
  obtain ⟨e313, e314, ecap⟩ := hS
  have hok : powOk (busGrindingBits μ) (Keccak.lane (s.nonceState nn) 2) = true :=
    ((grindOk_iff (s := s) hb0 nn).2 (by rw [← e314, ← hbits]; exact hpow)).resolve_left hb0
  obtain ⟨S, hSd⟩ : ∃ S, s.nonceState nn = S := ⟨_, rfl⟩
  have hG := runsToG_grind hb0 s nn hok
  rw [hSd] at hG e313 ecap
  -- the slot weights
  rw [vsFpwT, holdsList_append, holdsList_append, holdsList_append,
    show (List.range 5) = [0, 1, 2, 3, 4] from rfl] at h
  simp only [List.map_cons, List.map_nil, Stmt.HoldsList, Stmt.Holds, vsCopy, vsAlloc, vsLd,
    Atom.Holds] at h
  obtain ⟨c0, c1, c2, c3, c4, -, l313, hL⟩ := h
  obtain ⟨hs15, hsq, hL'⟩ := fpw_loop h8 h9 h10 h11 15 hL
  obtain ⟨hβ, hn⟩ := vsSqzT_holds h8 h9 h10 h11 hL'
  have hcap : capOf S = (vsRun 330 5).map σ := by
    rw [← ecap]
    show _ = [σ (.n 330), σ (.n 331), σ (.n 332), σ (.n 333), σ (.n 334)]
    rw [c0, c1, c2, c3, c4]
  have hT : ((⟨capOf S, []⟩ : Fs).squeezeN 15).2 = ⟨(vsRun 540 5).map σ, []⟩ := by
    rw [hcap, squeezeN_eq]
    exact hs15
  have hβ' : ((⟨capOf S, []⟩ : Fs).squeezeN 15).2.squeeze =
      (σ (.n 559), ⟨[σ (.n 554), σ (.n 555), σ (.n 556), σ (.n 557), σ (.n 558)], []⟩) := by
    rw [hT]; exact hβ
  have hW : ((⟨capOf S, []⟩ : Fs).squeezeN 15).1 =
      (List.range 15).map fun x ↦ (sqSt ⟨(vsRun 330 5).map σ, []⟩ x).squeeze.1 := by
    rw [hcap, squeezeN_eq]
  refine ⟨by omega, challengeOf S :: ((⟨capOf S, []⟩ : Fs).squeezeN 15).1,
    by simp [vs_squeezeN_length], ?_, ?_, hn⟩
  · rw [hW]
    intro k hk
    rcases k with _ | i
    · simp only [List.getElem_cons_zero]
      rw [Keccak.challengeOf_cells, ← e313]
      exact l313
    · simp only [List.length_cons, List.length_map, List.length_range] at hk
      simp only [List.getElem_cons_succ, List.getElem_map, List.getElem_range]
      rw [(hsq i (by omega)).1]
      exact (hsq i (by omega)).2
  · have hR := ((runsTo_sampleE ((⟨capOf S, []⟩ : Fs).squeezeN 15).2).bind
      (f := fun beta ↦ (pure (challengeOf S :: ((⟨capOf S, []⟩ : Fs).squeezeN 15).1, beta) :
        VerifierProgram (List E × E))) (runsTo_ret _ _))
    rw [hβ'] at hR
    have h2 := (runsFromG_sampleN_succ 15 (capOf S) (challengeOf S)).bind
      (f := fun weights ↦ VerifierProgram.sampleChallenge.bind fun beta ↦
        VerifierProgram.ret (weights, beta)) hR
    have h1 := hG.bindFrom (f := fun _ ↦ (VerifierProgram.sampleChallenges (2 ^ busBits)).bind
      fun weights ↦ VerifierProgram.sampleChallenge.bind fun beta ↦
        VerifierProgram.ret (weights, beta)) h2
    exact h1.of_eq rfl (by simp) rfl rfl

end
end LeanVM.Guest.B1.VerifySub
