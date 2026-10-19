/-
  LeanVM.Guest.B1.Tables.FlockAtB

  `verify_flock` complete in the uniform placed form, by a bounded tree.
-/

module

public import LeanVM.Guest.B1.Tables.LoopSize
public import LeanVM.Guest.B1.Tables.FlatAtB
public import LeanVM.Guest.B1.Tables.VtCStraightB

/-!
# `verify_flock`, placed and bounded

Its tree is its frame, its four `HeapBuf`s (`7τ + 150` words) and its two loops, `__loop81`
over `τ + 1` steps and `__loop82` over `τ + 1`, at most 30 frames each for `τ < 29`.
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Memory
open LeanVM.Protocol LeanVM.Protocol.Blake2sHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Guest.B1.VerifySub LeanVM.Guest.B1.Sig
open LeanVM.Guest.B1.Main (Layout MemL RegionL)

@[expose] public section

/-- One of `verify_flock`'s loops, at most 30 frames of each. -/
abbrev flLoopsBound (fs : String → ℕ) : ℕ := 30 * fs "__loop81" + 30 * fs "__loop82"

/-- `verify_flock`'s bound: its frame, its `HeapBuf`s at `τ = 28` and its loops. -/
abbrev flockBound (fs : String → ℕ) : ℕ := fs "verify_flock" + 346 + 2 * flLoopsBound fs

/-- `verify_flock`'s weight: its frame's and its two loops'. -/
abbrev flockBoundW (ω : String → ℕ) : ℕ := ω "verify_flock" + 2 * flLoopsBound ω

set_option maxHeartbeats 4000000 in
/-- **`verify_flock` is complete, placed, by a bounded tree within weights** (TRIAGE #40):
`CompleteFlockAtW` at its frame, its `HeapBuf`s and its two loops at `τ < 29`. -/
theorem verify_flock_completeAtW (fs : String → ℕ) (cert : String → V → ℕ) {Θ : Type} (w : Θ → String → ℕ)
    (κ : ℕ) : CompleteFlockAtW fs cert κ w (flockBound fs) fun θ => flockBoundW (w θ) := by
  intro τ cv xs cv' zSkip alpha mv chi rcs s c zc lr zp Lin hτ hcl hrl hsl hrun hLin
  obtain ⟨hlen, hz, ha, hchiE, hrcE, hsE, hterm, hcv'⟩ :=
    flock_inv (hrun _ (flockEv_at alpha zSkip (chi.take 8) rcs.reverse s mv))
  refine Main.CompleteAtW.bmono ?_ (show fs "verify_flock" + (flSizes τ).sum + 2 * flLoopsBound fs ≤
    flockBound fs by simp only [flSizes, flockBound, List.sum_cons, List.sum_nil]; omega)
  refine completeAt_straightW find_verify_flock fl_not_loop κ Lin _ _ fl_body fl_straight fl_addrs
    (flSizes τ) (fun _ => flOwn τ cv xs (ofK (Parameters.gpow c))) (fun _ => flOwn_fit _ _ _ _)
    (fun fp => flKids τ cv xs (ofK (Parameters.gpow c)) (ofK (Parameters.gpow zc)) Lin
      (fp + fs "verify_flock")) (fun _ => flLoopsBound fs) (fun _ θ => flLoopsBound (w θ))
    (2 * flLoopsBound fs) (fun θ => 2 * flLoopsBound (w θ)) ?_
    (fun fp => by simp [kidsBound, flKids]; omega) (fun fp θ => by simp [Main.kidsBoundW, flKids]; omega) ?_ ?_ ?_
  · intro fp k hk _
    simp only [flKids, List.mem_cons, List.not_mem_nil, or_false] at hk
    rcases hk with rfl | rfl
    · refine vtc_completeAt_of_rel_lowW (B := fun fs' => flLoopsBound fs') pure81 (by simp) κ
        (fun rd hlow hL rd' hag => ?_) fun fs' rd _ t rets' hn hv hbo => ?_
      · obtain ⟨hL1, hL2⟩ := Main.memL_append.mp hL
        have hM := flMem_of hLin hlen hchiE hrcE hsE hlow hL1 hL2 hag
        rw [word_g13, word_g14, ← pow_add]
        exact loop81_complete hτ hM
      · rw [word_g13, word_g14, ← pow_add] at hv
        have := l81_total (fs := fs') (j := 13) (m := τ + 14) (by omega) hn hv hbo
        have : (τ + 14 - 13) * fs' "__loop81" ≤ 29 * fs' "__loop81" := Nat.mul_le_mul_right _ (by omega)
        simp only [flLoopsBound]; omega
    · refine vtc_completeAt_of_rel_lowW (B := fun fs' => flLoopsBound fs') pure82 (by simp) κ
        (fun rd hlow hL rd' hag => ?_) fun fs' rd _ t rets' hn hv hbo => ?_
      · obtain ⟨hL1, hL2⟩ := Main.memL_append.mp hL
        have hM := flMem_of hLin hlen hchiE hrcE hsE hlow hL1 hL2 hag
        rw [word_g7, word_g8, ← pow_add]
        exact loop82_complete hτ hM
      · rw [word_g7, word_g8, ← pow_add] at hv
        have := l82_total (fs := fs') (j := 7) (m := τ + 8) (by omega) hn hv hbo
        have : (τ + 8 - 7) * fs' "__loop82" ≤ 29 * fs' "__loop82" := Nat.mul_le_mul_right _ (by omega)
        simp only [flLoopsBound]; omega
  · intro fp k hk _ i hi
    simp only [flKids, List.mem_cons, List.not_mem_nil, or_false] at hk
    rcases hk with rfl | rfl <;> exact regionL_append.mp hi
  · intro fp rd hB hL k hk
    simp only [flKids, List.mem_cons, List.not_mem_nil, or_false] at hk
    rcases hk with rfl | rfl <;> exact Main.memL_append.mpr ⟨hL, hB⟩
  · intro fp outs ho rd hlow hB hL
    have hM := flMem_of hLin hlen hchiE hrcE hsE hlow hL hB (rd' := rd) (fun _ _ => rfl)
    obtain ⟨σ, he, ⟨hret, F0, F7⟩, hh⟩ := flock_body_complete hτ hM hlen hterm
      (Val.ofArgs [(digestScalars cv).1, (digestScalars cv).2, ofK (Parameters.gpow c), gen ^ τ,
        ofK (Parameters.gpow zc), ofK (Parameters.gpow lr), ofK (Parameters.gpow zp)]) (by
        intro p hp
        simp only [flArgs, List.mem_cons, List.mem_nil_iff, or_false] at hp
        rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl)
    have ag : ∀ i < 7, σ (.n i) = [(digestScalars cv).1, (digestScalars cv).2, ofK (Parameters.gpow c),
        gen ^ τ, ofK (Parameters.gpow zc), ofK (Parameters.gpow lr), ofK (Parameters.gpow zp)].getD i 0 :=
      fun i hi => by rw [he.apply (Or.inl hi)]; rfl
    set b := fp + fs "verify_flock"
    have f10 : σ (.n 10) = gen ^ τ * word 16384 0 0 := F0.get (by simp [flP0Out])
    have f11 : σ (.n 11) = ofK (Parameters.gpow b) := F0.get (by simp [flP0Out])
    have f23 : σ (.n 23) = gen ^ τ * word 16384 0 0 * word 4 0 0 * (gen ^ τ * word 16384 0 0 * word 4 0 0) :=
      F0.get (by simp [flP0Out])
    have f24 : σ (.n 24) = ofK (Parameters.gpow (b + (τ + 14))) := F0.get (by simp [flP0Out])
    have f26 : σ (.n 26) = ofK (Parameters.gpow (b + (τ + 14))) * word 67108864 0 0 :=
      F0.get (by simp [flP0Out])
    have f30 : σ (.n 30) = word 8192 0 0 + gen ^ τ * word 16384 0 0 := F0.get (by simp [flP0Out])
    have f31 : σ (.n 31) = word 8192 0 0 := F0.get (by simp [flP0Out])
    have f33 : σ (.n 33) = gen ^ τ * word 16384 0 0 := F0.get (by simp [flP0Out])
    have f37 : σ (.n 37) = ofK (Parameters.gpow (b + (τ + 14))) *
        (gen ^ τ * word 16384 0 0 * (gen ^ τ * word 16384 0 0)) := F0.get (by simp [flP0Out])
    have f40 : σ (.n 40) = ofK (Parameters.gpow (b + (τ + 14) + (2 * τ + 32))) := F0.get (by simp [flP0Out])
    have f2219 : σ (.n 2219) =
        gen ^ τ * word 16384 0 0 * word 2017612633061982209 0 0 * word 4 0 0 *
          (gen ^ τ * word 16384 0 0 * word 2017612633061982209 0 0 * word 4 0 0) *
        (gen ^ τ * word 16384 0 0 * word 2017612633061982209 0 0 * word 4 0 0 *
          (gen ^ τ * word 16384 0 0 * word 2017612633061982209 0 0 * word 4 0 0)) :=
      F7.get (by simp [flP7Out])
    have f2220 : σ (.n 2220) = ofK (Parameters.gpow (b + (τ + 14) + (2 * τ + 32) + 64)) :=
      F7.get (by simp [flP7Out])
    have f2222 : σ (.n 2222) = ofK (Parameters.gpow (b + (τ + 14) + (2 * τ + 32) + 64)) *
        word 268435456 0 0 := F7.get (by simp [flP7Out])
    have f2228 : σ (.n 2228) = word 128 0 0 + gen ^ τ * word 256 0 0 := F7.get (by simp [flP7Out])
    have f2229 : σ (.n 2229) = word 128 0 0 := F7.get (by simp [flP7Out])
    have f2231 : σ (.n 2231) = gen ^ τ * word 256 0 0 := F7.get (by simp [flP7Out])
    have f2236 : σ (.n 2236) = ofK (Parameters.gpow (b + (τ + 14) + (2 * τ + 32) + 64)) *
        (gen ^ τ * word 256 0 0 * (gen ^ τ * word 256 0 0) *
          (gen ^ τ * word 256 0 0 * (gen ^ τ * word 256 0 0))) := F7.get (by simp [flP7Out])
    have f2240 : σ (.n 2240) = ofK (Parameters.gpow c) * gen ^ (64 + 2 * (τ + 8)) :=
      F7.get (by simp [flP7Out])
    have h4 : word 4 0 0 = gen ^ 2 := word_four'
    obtain ⟨o1, o2, rfl⟩ : ∃ o1 o2, outs = [o1, o2] := by
      match outs, ho.length with
      | [o1, o2], _ => exact ⟨o1, o2, rfl⟩
    have ho1 : o1.1 = [] := (ho.1 rfl).1
    have ho2 : o2.1 = [] := (ho.2.1 rfl).1
    refine ⟨σ, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [core12_params]
      simp only [List.map_cons, List.map_nil]
      rw [ag 0 (by omega), ag 1 (by omega), ag 2 (by omega), ag 3 (by omega), ag 4 (by omega),
        ag 5 (by omega), ag 6 (by omega)]
      rfl
    · rw [fl_body, holdsList_append]
      refine hh _ _ ?_
      simp only [Stmt.HoldsList, Stmt.Holds, List.map_cons, List.map_nil]
      rw [hret, hcv', hz, ha, hlen, mul_assoc, ← pow_add,
        show 64 + 2 * (τ + 8) + 82 = flLen τ by unfold flLen; omega]
    · rw [fl_allocs]
      simp only [List.map_cons, List.map_nil, Sum.elim_inr, Sum.elim_inl, id]
      rw [f10, f23, f2219, fl_v1851, word_g14, h4]
      simp only [← pow_add]
      rw [logG_g _ (by omega), logG_g _ (by omega), logG_g _ (by omega), flSizes]
      congr 2
      · omega
      · congr 2; omega
    · rw [fl_allocs]
      simp only [List.map_cons, List.map_nil, flBases]
      rw [f11, f24, f40, f2220]
    · rw [fl_calls]
      simp only [List.map_cons, List.map_nil, Main.mkCall, flKids]
      refine ⟨rfl, ?_, fun _ => ⟨?_, by rw [ho1]; rfl⟩, rfl, ?_, fun _ => ⟨?_, by rw [ho2]; rfl⟩,
        trivial⟩
      · rw [f30, word_g13, word_g14, ← pow_add]
        simpa using gen_pow_ne_of_lt (a := 13) (b := τ + 14) (by omega) (by omega)
      · simp only [List.map_cons, List.map_nil]; rw [f31, f33, f24, f11]
      · rw [f2228, word_g7, word_g8, ← pow_add]
        simpa using gen_pow_ne_of_lt (a := 7) (b := τ + 8) (by omega) (by omega)
      · simp only [List.map_cons, List.map_nil]; rw [f2229, f2231, f2220, f11, ag 4 (by omega)]; rfl
    · intro q hq
      have hb := List.all_eq_true.mp fl_loads q hq
      obtain ⟨t, ht, htq⟩ := List.any_eq_true.mp hb
      obtain ⟨p, off⟩ := q
      simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at htq
      obtain ⟨⟨hp, hlo⟩, hhi⟩ := htq
      simp only [flLoadT, List.mem_cons, List.not_mem_nil, or_false] at ht
      rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        (dsimp only at hp hlo hhi ⊢; subst hp)
      · obtain ⟨i, hi, hr⟩ := addr_in_region (fun rd h1 h2 => (hLin rd h1 h2).1) hlow hL (j := off) (by rw [hlen]; unfold flLen; omega)
        exact ⟨i, by rw [ag 2 (by omega)]; exact hi, Or.inl hr⟩
      · obtain ⟨i, hi, hr⟩ := addr_in_region (fun rd h1 h2 => (hLin rd h1 h2).1) hlow hL
          (j := 64 + 2 * (τ + 8) + off) (by rw [hlen]; unfold flLen; omega)
        refine ⟨i, ?_, Or.inl hr⟩
        rw [f2240, addr_gen, ← hi, addr_k, Nat.add_assoc]
      · obtain ⟨i, hi, hr⟩ := addr_in_region (fun rd h1 h2 => (hLin rd h1 h2).2.1) hlow hL (j := off) (by rw [hcl]; omega)
        exact ⟨i, by rw [ag 4 (by omega)]; exact hi, Or.inl hr⟩
      · obtain ⟨i, hi, hr⟩ := addr_in_region (fun rd h1 h2 => (hLin rd h1 h2).2.2.1) hlow hL (j := off) (by rw [hrl]; omega)
        exact ⟨i, by rw [ag 5 (by omega)]; exact hi, Or.inl hr⟩
      · obtain ⟨i, hi, hr⟩ := addr_in_region (fun rd h1 h2 => (hLin rd h1 h2).2.2.2) hlow hL (j := off) (by rw [hsl]; omega)
        exact ⟨i, by rw [ag 6 (by omega)]; exact hi, Or.inl hr⟩
      · exact ⟨b + off, by rw [f11, addr_k], Or.inr (region_buf (w := flW11 τ cv)
          (by simp [bufL, flBases, flOwn]) (by simp [flW11]; omega))⟩
      · refine ⟨b + (τ + 14) + (26 + off), by rw [f26, word_g26, addr_gen, Nat.add_assoc],
          Or.inr (region_buf (w := flW24 τ cv) (by simp [bufL, flBases, flOwn]) (by simp [flW24]; omega))⟩
      · refine ⟨b + (τ + 14) + (τ + 14 + (τ + 14) + off), by
          rw [f37, word_g14, ← pow_add, ← pow_add, addr_gen, Nat.add_assoc],
          Or.inr (region_buf (w := flW24 τ cv) (by simp [bufL, flBases, flOwn]) (by simp [flW24]; omega))⟩
      · exact ⟨b + (τ + 14) + (2 * τ + 32) + off, by rw [f40, addr_k], Or.inr (region_buf (w := flW40 xs)
          (by simp [bufL, flBases, flOwn]) (by simp [flW40]; omega))⟩
      · refine ⟨b + (τ + 14) + (2 * τ + 32) + 64 + (28 + off), by
          rw [f2222, LeanVM.Guest.B1.word_g28, addr_gen, Nat.add_assoc],
          Or.inr (region_buf (w := flW2220 τ cv xs (ofK (Parameters.gpow c)))
            (by simp [bufL, flBases, flOwn]) (by simp [flW2220]; omega))⟩
      · refine ⟨b + (τ + 14) + (2 * τ + 32) + 64 + (τ + 8 + (τ + 8) + (τ + 8 + (τ + 8)) + off), by
          rw [f2236, word_g8, ← pow_add]
          simp only [← pow_add]
          rw [addr_gen, Nat.add_assoc],
          Or.inr (region_buf (w := flW2220 τ cv xs (ofK (Parameters.gpow c)))
            (by simp [bufL, flBases, flOwn]) (by simp [flW2220]; omega))⟩


/-- **`verify_flock` is complete, placed, by a bounded tree** (TRIAGE #40): `CompleteFlockAtB`
at its frame, its `HeapBuf`s and its two loops at `τ < 29`. -/
theorem verify_flock_completeAtB (fs : String → ℕ) (cert : String → V → ℕ) (κ : ℕ) :
    CompleteFlockAtB fs cert κ (flockBound fs) :=
  (verify_flock_completeAtW fs cert (Θ := Empty) (fun e => e.elim) κ).toB

/-- **`verify_flock` is complete, placed** (TRIAGE #40): `CompleteFlockAt`. -/
theorem verify_flock_completeAt (fs : String → ℕ) (cert : String → V → ℕ) (κ : ℕ) :
    CompleteFlockAt fs cert κ :=
  fun τ cv xs cv' zSkip alpha mv chi rcs s c zc lr zp Lin h1 h2 h3 h4 h5 h6 =>
    (verify_flock_completeAtB fs cert κ τ cv xs cv' zSkip alpha mv chi rcs s c zc lr zp Lin h1 h2 h3
      h4 h5 h6).toCompleteAtD

end
end LeanVM.Guest.B1
