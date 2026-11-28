/-
  LeanVM.Guest.B1.VerifySub.PhOodRingRing

  `verify_sub`'s ring switch phase: the grind and the packed draw run `ringSwitch`.
-/

module

public import LeanVM.Guest.B1.VerifySub.Sizes
public import LeanVM.Guest.B1.VerifySub.PhOodRingGrind
public import LeanVM.Guest.B1.VerifySub.PhOodRingCt
public import LeanVM.Guest.B1.VerifySub.PhOodRingRun
import LeanVM.Guest.ValRef
import LeanVM.Guest.Data.ValNames.«verify_sub»

/-!
# The ring switch phase

`vsRingT` (statements `2929 .. 3015`, checked by the kernel): the nonce at `cursor@4` absorbed on
the capacity `verify_keccak` returned (`fs_grind_squeeze` at no waiting scalar), its permutation,
`grind_check` of `BATCH_GRIND_BITS = 13` inlined with the tables folded into its reads
(`gcInlineAt`), the map's challenges `ch[0 .. 15]`, `rho` and `lam` from the grind's permutation and
two permutations of the capacity alone, `ch` stored at `map_challenges`; then `vsCtT`, the
coefficients at `c_table`. `runsTo_grindPacked`: a grind then a packed draw of `18` challenges
(`samplesPacked` after a grind: the ground challenge, the permutation's cells `2 .. 7`, then
eleven of two permutations of the capacity). `phRing`: they run `ringSwitch` on the two ring
claims, `f = ch[0 .. 7]`, `g = ch[8 .. 15]`.
-/

namespace LeanVM.Guest.B1.VerifySub

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

/-- `verify_sub`'s statements 2929 to 2937: the capacity, the nonce and its permutation. -/
def vsRingPreT : List Stmt := (
  .atom (.copy (.n 2922) (.n 2915)) ::
  .atom (.copy (.n 2923) (.n 2916)) ::
  .atom (.copy (.n 2924) (.n 2917)) ::
  .atom (.copy (.n 2925) (.n 2918)) ::
  .atom (.copy (.n 2926) (.n 2919)) ::
  .atom (.load (.n 2927) (.n 2920) 0) ::
  .atom (.copy (.n 2928) (.n 2927)) ::
  .atom (.const (.n 2929) (word 0 4)) ::
  .atom (.keccak [.n 2928, .n 2929, .n 25, .n 25, .n 25, .n 26, .n 27, .n 28, .n 2922, .n 2923, .n 2924, .n 2925, .n 2926] [.n 2930, .n 2931, .n 2932, .n 2933, .n 2934, .n 2935, .n 2936, .n 2937, .n 2938, .n 2939, .n 2940, .n 2941, .n 2942] false false) ::
  [])

/-- `verify_sub`'s statements 2980 to 3015: the challenges and their table. -/
def vsRingRestT : List Stmt := (
  .atom (.copy (.n 2997) (.n 2930)) ::
  .atom (.copy (.n 2998) (.n 2932)) ::
  .atom (.copy (.n 2999) (.n 2933)) ::
  .atom (.copy (.n 3000) (.n 2934)) ::
  .atom (.copy (.n 3001) (.n 2935)) ::
  .atom (.copy (.n 3002) (.n 2936)) ::
  .atom (.copy (.n 3003) (.n 2937)) ::
  .atom (.keccak [.n 25, .n 25, .n 25, .n 25, .n 25, .n 26, .n 27, .n 28, .n 2938, .n 2939, .n 2940, .n 2941, .n 2942] [.n 3004, .n 3005, .n 3006, .n 3007, .n 3008, .n 3009, .n 3010, .n 3011, .n 3012, .n 3013, .n 3014, .n 3015, .n 3016] false false) ::
  .atom (.copy (.n 3017) (.n 3004)) ::
  .atom (.copy (.n 3018) (.n 3005)) ::
  .atom (.copy (.n 3019) (.n 3006)) ::
  .atom (.copy (.n 3020) (.n 3007)) ::
  .atom (.copy (.n 3021) (.n 3008)) ::
  .atom (.copy (.n 3022) (.n 3009)) ::
  .atom (.copy (.n 3023) (.n 3010)) ::
  .atom (.copy (.n 3024) (.n 3011)) ::
  .atom (.keccak [.n 25, .n 25, .n 25, .n 25, .n 25, .n 26, .n 27, .n 28, .n 3012, .n 3013, .n 3014, .n 3015, .n 3016] [.n 3025, .n 3026, .n 3027, .n 3028, .n 3029, .n 3030, .n 3031, .n 3032, .n 3033, .n 3034, .n 3035, .n 3036, .n 3037] false false) ::
  .atom (.copy (.n 3038) (.n 3025)) ::
  .atom (.hint (.alloc (.n 3039) 16)) ::
  .atom (.load (.n 2997) (.n 3039) 0) ::
  .atom (.load (.n 2998) (.n 3039) 1) ::
  .atom (.load (.n 2999) (.n 3039) 2) ::
  .atom (.load (.n 3000) (.n 3039) 3) ::
  .atom (.load (.n 3001) (.n 3039) 4) ::
  .atom (.load (.n 3002) (.n 3039) 5) ::
  .atom (.load (.n 3003) (.n 3039) 6) ::
  .atom (.load (.n 3017) (.n 3039) 7) ::
  .atom (.load (.n 3018) (.n 3039) 8) ::
  .atom (.load (.n 3019) (.n 3039) 9) ::
  .atom (.load (.n 3020) (.n 3039) 10) ::
  .atom (.load (.n 3021) (.n 3039) 11) ::
  .atom (.load (.n 3022) (.n 3039) 12) ::
  .atom (.load (.n 3023) (.n 3039) 13) ::
  .atom (.load (.n 3024) (.n 3039) 14) ::
  .atom (.load (.n 3038) (.n 3039) 15) ::
  .atom (.hint (.alloc (.n 3040) 64)) ::
  [])

/-- `verify_sub`'s statements 2929 to 3015. -/
def vsRingT : List Stmt := vsRingPreT ++ gcInlineAt 13 2943 178 (.n 2931) (.n 4) ++ vsRingRestT

theorem vsRingT_eq : (vsPre.drop 2929).take 87 = vsRingT := stmtsEqb_sound (by decide +kernel)

/-! ## The phase -/

/-- **The ring switch**, sound. -/
theorem phRing : PhRing := by
  intro bytecode κ L C Vm σ rets R link outs kp ks s qp hLF hKF hpend hcap hqp
  obtain ⟨-, hwin, h11⟩ := R.pre
  -- the seed's zeros
  have hS := R.slice vsSeedT_eq
  simp only [vsSeedT, Stmt.HoldsList, Stmt.Holds] at hS
  obtain ⟨-, h25, h26, h27, h28, -, -⟩ := hS
  simp only [Atom.Holds, word_zero] at h25 h26 h27 h28
  -- the phase
  have h := R.slice vsRingT_eq
  rw [vsRingT, holdsList_append, holdsList_append] at h
  simp only [vsRingPreT, Stmt.HoldsList, Stmt.Holds] at h
  obtain ⟨a0, a1, a2, a3, a4, a5, a6, a7, a8, hg⟩ := h
  have hwt : WinTabs L.read (σ (.n 4) * gen ^ 178) := winTabs_of_expWinTab hwin
  obtain ⟨hpow, hrest⟩ := gcInlineAt_sound R.hκ h11 L (by decide) hwt hg
  simp only [vsRingRestT, Stmt.HoldsList, Stmt.Holds] at hrest
  obtain ⟨r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, -,
    m0, m1, m2, m3, m4, m5, m6, m7, m8, m9, m10, m11, m12, m13, m14, m15, -, -⟩ := hrest
  have c2922 : σ (.n 2922) = σ (.n 2915) := a0
  have c2923 : σ (.n 2923) = σ (.n 2916) := a1
  have c2924 : σ (.n 2924) = σ (.n 2917) := a2
  have c2925 : σ (.n 2925) = σ (.n 2918) := a3
  have c2926 : σ (.n 2926) = σ (.n 2919) := a4
  have c2928 : σ (.n 2928) = σ (.n 2927) := a6
  have c2929 : σ (.n 2929) = word 0 4 := a7
  -- the nonce's permutation
  set n := vsRingNonce σ with hn
  set S0 := s.nonceState n with hS0
  have habs : s.absorb n dsPowNonce = ⟨capOf s.perm, [(n, dsPowNonce)]⟩ := by
    simp [Fs.absorb, hpend]
  have hK0 := keccakA_fs (s := s.absorb n dsPowNonce) a8 (by rw [habs]; simp) (by
    rw [habs]
    simp only [hcap, vsCapK, List.map_cons, List.map_nil, c2922, c2923, c2924, c2925, c2926,
      c2929, h25, h26, h27, h28]
    rfl)
  have o0 : ∀ k : Fin 13, ∀ hk : k.val < 13,
      σ ([.n 2930, .n 2931, .n 2932, .n 2933, .n 2934, .n 2935, .n 2936, .n 2937, .n 2938, .n 2939,
        .n 2940, .n 2941, .n 2942] : List V)[k.val] = cellsOfState S0 false k :=
    fun k hk ↦ outs_eq hK0 k (by simp)
  have hok : powOk Whir.batchGrindingBits (Keccak.lane S0 2) = true :=
    ((grindOk_iff (s := s) (by decide) n).mpr (by
      rw [← hS0, ← show σ (.n 2931) = cellsOfState S0 false 1 from o0 1 (by decide)]
      exact hpow)).resolve_left (by decide)
  -- the two permutations of the capacity alone
  have o08 : σ (.n 2938) = cellsOfState S0 false 8 := o0 8 (by decide)
  have o09 : σ (.n 2939) = cellsOfState S0 false 9 := o0 9 (by decide)
  have o010 : σ (.n 2940) = cellsOfState S0 false 10 := o0 10 (by decide)
  have o011 : σ (.n 2941) = cellsOfState S0 false 11 := o0 11 (by decide)
  have o012 : σ (.n 2942) = cellsOfState S0 false 12 := o0 12 (by decide)
  have hin1 : List.map σ [.n 25, .n 25, .n 25, .n 25, .n 25, .n 26, .n 27, .n 28, .n 2938, .n 2939,
      .n 2940, .n 2941, .n 2942] = List.replicate 8 0 ++ capOf S0 := by
    simp only [List.map_cons, List.map_nil, h25, h26, h27, h28, o08, o09, o010, o011, o012]
    rfl
  have hK1 := (keccakA_perm r7).2.2
  rw [hin1] at hK1
  have o1 : ∀ k : Fin 13, ∀ hk : k.val < 13,
      σ ([.n 3004, .n 3005, .n 3006, .n 3007, .n 3008, .n 3009, .n 3010, .n 3011, .n 3012, .n 3013,
        .n 3014, .n 3015, .n 3016] : List V)[k.val] = cellsOfState (Link.pkPerm (capOf S0)) false k :=
    fun k hk ↦ outs_eq hK1 k (by simp)
  have o18 : σ (.n 3012) = cellsOfState (Link.pkPerm (capOf S0)) false 8 := o1 8 (by decide)
  have o19 : σ (.n 3013) = cellsOfState (Link.pkPerm (capOf S0)) false 9 := o1 9 (by decide)
  have o110 : σ (.n 3014) = cellsOfState (Link.pkPerm (capOf S0)) false 10 := o1 10 (by decide)
  have o111 : σ (.n 3015) = cellsOfState (Link.pkPerm (capOf S0)) false 11 := o1 11 (by decide)
  have o112 : σ (.n 3016) = cellsOfState (Link.pkPerm (capOf S0)) false 12 := o1 12 (by decide)
  have hin2 : List.map σ [.n 25, .n 25, .n 25, .n 25, .n 25, .n 26, .n 27, .n 28, .n 3012, .n 3013,
      .n 3014, .n 3015, .n 3016] = List.replicate 8 0 ++ capOf (Link.pkPerm (capOf S0)) := by
    simp only [List.map_cons, List.map_nil, h25, h26, h27, h28, o18, o19, o110, o111, o112]
    rfl
  have hK2 := (keccakA_perm r16).2.2
  rw [hin2] at hK2
  have o2 : ∀ k : Fin 13, ∀ hk : k.val < 13,
      σ ([.n 3025, .n 3026, .n 3027, .n 3028, .n 3029, .n 3030, .n 3031, .n 3032, .n 3033, .n 3034,
        .n 3035, .n 3036, .n 3037] : List V)[k.val] = cellsOfState (Link.pkPerm (capOf (Link.pkPerm (capOf S0)))) false k :=
    fun k hk ↦ outs_eq hK2 k (by simp)
  -- the challenges
  have q0 : σ (.n 2997) = challengeOf S0 := by
    rw [r0, Keccak.challengeOf_cells]; exact o0 0 (by decide)
  have qp : ∀ i, 2 ≤ i → i < 8 → σ (.n (2996 + i)) = packedChallengeOf S0 i := by
    intro i h2 h8
    rw [Link.packedChallengeOf_cell S0 h8]
    interval_cases i
    · rw [show σ (.n (2996 + 2)) = σ (.n 2932) from r1]; exact o0 2 (by decide)
    · rw [show σ (.n (2996 + 3)) = σ (.n 2933) from r2]; exact o0 3 (by decide)
    · rw [show σ (.n (2996 + 4)) = σ (.n 2934) from r3]; exact o0 4 (by decide)
    · rw [show σ (.n (2996 + 5)) = σ (.n 2935) from r4]; exact o0 5 (by decide)
    · rw [show σ (.n (2996 + 6)) = σ (.n 2936) from r5]; exact o0 6 (by decide)
    · rw [show σ (.n (2996 + 7)) = σ (.n 2937) from r6]; exact o0 7 (by decide)
  have q1 : ∀ i, i < 8 → σ (.n (3017 + i)) = Link.cellAt (Link.pkPerm (capOf S0)) i := by
    intro i h8
    interval_cases i
    · rw [show σ (.n (3017 + 0)) = σ (.n 3004) from r8]; exact o1 0 (by decide)
    · rw [show σ (.n (3017 + 1)) = σ (.n 3005) from r9]; exact o1 1 (by decide)
    · rw [show σ (.n (3017 + 2)) = σ (.n 3006) from r10]; exact o1 2 (by decide)
    · rw [show σ (.n (3017 + 3)) = σ (.n 3007) from r11]; exact o1 3 (by decide)
    · rw [show σ (.n (3017 + 4)) = σ (.n 3008) from r12]; exact o1 4 (by decide)
    · rw [show σ (.n (3017 + 5)) = σ (.n 3009) from r13]; exact o1 5 (by decide)
    · rw [show σ (.n (3017 + 6)) = σ (.n 3010) from r14]; exact o1 6 (by decide)
    · rw [show σ (.n (3017 + 7)) = σ (.n 3011) from r15]; exact o1 7 (by decide)
  have q20 : σ (.n 3038) = Link.cellAt (Link.pkPerm (capOf (Link.pkPerm (capOf S0)))) 0 := by
    rw [show σ (.n 3038) = σ (.n 3025) from r17]; exact o2 0 (by decide)
  have q21 : σ (.n 3026) = Link.cellAt (Link.pkPerm (capOf (Link.pkPerm (capOf S0)))) 1 := o2 1 (by decide)
  have q22 : σ (.n 3027) = Link.cellAt (Link.pkPerm (capOf (Link.pkPerm (capOf S0)))) 2 := o2 2 (by decide)
  have hcs : challengeOf S0 :: (List.range 6).map (packedChallengeOf S0 ∘ (· + 2)) ++
      (Link.pkSqueeze 2 (capOf S0)).1.take 11 =
      [σ (.n 2997), σ (.n 2998), σ (.n 2999), σ (.n 3000), σ (.n 3001), σ (.n 3002), σ (.n 3003),
        σ (.n 3017)] ++
      [σ (.n 3018), σ (.n 3019), σ (.n 3020), σ (.n 3021), σ (.n 3022), σ (.n 3023), σ (.n 3024),
        σ (.n 3038)] ++ [σ (.n 3026), σ (.n 3027)] := by
    rw [grindPacked_list, q0, qp 2 (by omega) (by omega), qp 3 (by omega) (by omega),
      qp 4 (by omega) (by omega), qp 5 (by omega) (by omega), qp 6 (by omega) (by omega),
      qp 7 (by omega) (by omega), q1 0 (by omega), q1 1 (by omega), q1 2 (by omega), q1 3 (by omega),
      q1 4 (by omega), q1 5 (by omega), q1 6 (by omega), q1 7 (by omega), q20, q21, q22]
    rfl
  have hcap2 : [σ (.n 3033), σ (.n 3034), σ (.n 3035), σ (.n 3036), σ (.n 3037)] =
      capOf (Link.pkPerm (capOf (Link.pkPerm (capOf S0)))) := by
    rw [show σ (.n 3033) = cellsOfState (Link.pkPerm (capOf (Link.pkPerm (capOf S0)))) false 8 from o2 8 (by decide), show σ (.n 3034) = cellsOfState (Link.pkPerm (capOf (Link.pkPerm (capOf S0)))) false 9 from o2 9 (by decide), show σ (.n 3035) = cellsOfState (Link.pkPerm (capOf (Link.pkPerm (capOf S0)))) false 10 from o2 10 (by decide), show σ (.n 3036) = cellsOfState (Link.pkPerm (capOf (Link.pkPerm (capOf S0)))) false 11 from o2 11 (by decide), show σ (.n 3037) = cellsOfState (Link.pkPerm (capOf (Link.pkPerm (capOf S0)))) false 12 from o2 12 (by decide)]
    rfl
  refine ⟨[σ (.n 2997), σ (.n 2998), σ (.n 2999), σ (.n 3000), σ (.n 3001), σ (.n 3002), σ (.n 3003),
      σ (.n 3017)],
    [σ (.n 3018), σ (.n 3019), σ (.n 3020), σ (.n 3021), σ (.n 3022), σ (.n 3023), σ (.n 3024),
      σ (.n 3038)], σ (.n 3026), σ (.n 3027), ?_, ?_, ?_⟩
  · rw [show n = σ (.n 2927) from c2928]; exact a5
  · unfold ringSwitch
    refine runsTo_grindPacked (bits := Whir.batchGrindingBits) (by decide) s n hok _ ?_
    rw [hcs]
    refine RunsTo.of_eq (runsTo_ret _ _) rfl rfl rfl ?_
    rw [grindPacked_cap, vsF8, hcap2]
  · refine ⟨rfl, rfl, ?_, ?_, rfl, rfl⟩
    · intro k hk
      simp only [List.length_append, List.length_cons, List.length_nil] at hk
      interval_cases k
      exacts [m0, m1, m2, m3, m4, m5, m6, m7, m8, m9, m10, m11, m12, m13, m14, m15]
    · exact ct_reads (fun x hx ↦ R.atom_in vsCtT_eq hx)

end
end LeanVM.Guest.B1.VerifySub
