/-
  LeanVM.Guest.B1.VsC.Log2A

  `log2_ceil_in_the_exponent__L16_L34` completes placed.
-/

module

public import LeanVM.Guest.B1.VsC.Log2C
public import LeanVM.Guest.B1.VsC.AsgA
public import LeanVM.Guest.Complete.ComposeRd
import LeanVM.Guest.CoreRef

/-!
# `log2_ceil_in_the_exponent__L16_L34`, placed

`log2_complete`'s valuation per memory (`lcWords`, the range checks' words read from the low
memory) placed by `callAtA_nodeRd`: no words of its own, its one or two `assert_small_g_power`
calls (`asg_placed`) at the aligned bases past its frame, its two loads in the exponent table at `q`
below `34`, the calls' loads in its nibble shares (`log2_placed`). The path's facts are lemmas over
any valuation (`lc_loadAddrs`, `lc_allocs`, ...), the honest valuation's words lemmas of their own
(`lcW_*`), so the node's proof evaluates nothing.
-/

namespace LeanVM.Guest.B1.VsC

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Memory LeanVM.Guest.B1
open LeanVM.Guest.Complete LeanVM.Guest.Value
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Prover.Exec (allocBase)

@[expose] public section

/-! ## The path, on any valuation -/

theorem lc_allocs (τ σ : Val) : allocs τ (lcEvs σ) = [] := by
  unfold lcEvs; split <;> rfl

theorem lc_allocDsts (σ : Val) : allocDsts (lcEvs σ) = [] := by
  unfold lcEvs; split <;> rfl

theorem lc_addrs (σ : Val) : addrs (lcEvs σ) = [] := by
  unfold lcEvs; split <;> rfl

theorem lc_heapHintAddrs (τ σ : Val) : heapHintAddrs τ (lcEvs σ) = [] := by
  unfold lcEvs; split <;> rfl

/-- The loads: `g_squares[g^L]`, and above the floor `g_squares[g^(L-1)]`. -/
theorem lc_loadAddrs (τ σ : Val) :
    loadAddrs τ (lcEvs σ) = (τ (.n 47)).limb 0 * addressOfIndex 0 ::
      if σ (.n 51) = 0 then [] else [(τ (.n 56)).limb 0 * addressOfIndex 0] := by
  unfold lcEvs
  by_cases h : σ (.n 51) = 0
  · rw [ite_pos' h, ite_pos' h]; rfl
  · rw [ite_neg' h, ite_neg' h]; rfl

theorem lc_quiet : Stmt.atomsAll atomQuiet lcBody = true := by decide +kernel

theorem lc_wf : Stmt.wfList coreProgram lcBody = true := by
  have h := coreProgram_wf _ (List.mem_of_find?_eq_some find_lce_L16)
  rwa [lc_body] at h

theorem lc_loop : coreProgram.loop "log2_ceil_in_the_exponent__L16_L34" = false := by
  rw [Program.loop_of_find? find_lce_L16, Fn.loop, lc_body, lcBody]; simp

/-! ## The honest valuation's words -/

section
variable (rd : Reader) (N L : ℕ) (q : E)

theorem lcW_0 : Val.ofArgs (lcWords rd N L q) (.n 0) = gen ^ N := rfl
theorem lcW_1 : Val.ofArgs (lcWords rd N L q) (.n 1) = q := rfl
theorem lcW_47 : Val.ofArgs (lcWords rd N L q) (.n 47) = q * gen ^ L := rfl
theorem lcW_49 : Val.ofArgs (lcWords rd N L q) (.n 49) = gen ^ (2 ^ L - N) := rfl
theorem lcW_51 : Val.ofArgs (lcWords rd N L q) (.n 51) = gen ^ L + word (2 ^ 16) 0 := rfl
theorem lcW_56 : Val.ofArgs (lcWords rd N L q) (.n 56) = q * (gen ^ L * invGenWord) := rfl
theorem lcW_58 : Val.ofArgs (lcWords rd N L q) (.n 58) = gen ^ (N - (2 ^ (L - 1) + 1)) := rfl
theorem lcW_59 : Val.ofArgs (lcWords rd N L q) (.n 59) = gen ^ L := rfl

theorem lcW_bits : Dest.words rd (Val.ofArgs (lcWords rd N L q)) (.stack lcBits) =
    (List.range 34).map fun j => Prover.Exec.bitWord (N.testBit j) := rfl

end

theorem lcW_51_eq_zero {rd : Reader} {N L : ℕ} {q : E} (h16 : 16 ≤ L) (hL : L < 34) :
    Val.ofArgs (lcWords rd N L q) (.n 51) = 0 ↔ L = 16 := by
  have wfl : word (2 ^ 16) 0 = gen ^ 16 := word_two_pow (by omega)
  rw [lcW_51, wfl, e_add_eq_zero_iff]
  exact ⟨fun h ↦ gen_pow_inj (by omega) (by omega) h, fun h ↦ by rw [h]⟩

theorem lcW_congr51 (rd rd' : Reader) (N L : ℕ) (q : E) :
    lcEvs (Val.ofArgs (lcWords rd N L q)) = lcEvs (Val.ofArgs (lcWords rd' N L q)) :=
  lcEvs_congr ((lcW_51 rd N L q).trans (lcW_51 rd' N L q).symm)

/-- The honest valuation's body holds, on a memory defined below `2^k` with the table at `q`. -/
theorem lc_holds {k : ℕ} (hk : 6 ≤ k) {rd : Reader} (hl : LowDef k rd) {N L : ℕ} {q : E}
    (ht : ExpTables rd q) (hL : L < 34) (hflL : 16 ≤ L) (hle : N ≤ 2 ^ L)
    (hlow : L ≠ 16 → 2 ^ (L - 1) < N) :
    Stmt.HoldsList (fun _ _ _ ↦ True) rd (Val.ofArgs (lcWords rd N L q)) lcBody False
      (fun r ↦ r = [gen ^ L]) := by
  have wfl : word (2 ^ 16) 0 = gen ^ 16 := word_two_pow (by omega)
  have w33 : word (2 ^ 33) 0 = ofK (addressOfIndex (34 - 1)) := by
    rw [word_two_pow (by norm_num), gen_pow_eq_ofK]
  have hK34 : 34 ≤ 2 ^ k := le_trans (by decide) (Nat.pow_le_pow_right (by decide) hk)
  obtain ⟨r1a, r1b, r1c⟩ := rc_complete_low hl (K := 34) hK34 hL
  obtain ⟨r2a, r2b, r2c⟩ := rc_complete_low hl (K := 34) hK34 (show L - 16 < 34 by omega)
  refine (lc_holds_iff _ rd _ _).2 ⟨rfl, ⟨?_, ?_, r1c⟩, rfl, rfl, ?_, ⟨?_, ?_, r2c⟩, rfl,
    ?_, ?_, trivial, rfl, rfl, ⟨?_, fun hne ↦ ?_⟩, rfl, rfl⟩
  · show LoadHolds rd (gen ^ L) 0 _
    rw [gen_pow_eq_ofK]; exact r1a
  · show word (2 ^ 33) 0 = gen ^ L * _
    rw [w33, gen_pow_eq_ofK]; exact r1b
  · show gen ^ L = gen ^ (L - 16) * word (2 ^ 16) 0
    rw [wfl, ← pow_add]; congr 1; omega
  · show LoadHolds rd (gen ^ (L - 16)) 0 _
    rw [gen_pow_eq_ofK]; exact r2a
  · show word (2 ^ 33) 0 = gen ^ (L - 16) * _
    rw [w33, gen_pow_eq_ofK]; exact r2b
  · show LoadHolds rd (q * gen ^ L) 0 (gen ^ 2 ^ L)
    rw [loadHolds_mul_gen_pow, Nat.add_zero]; exact ht.1 L hL
  · show gen ^ 2 ^ L = gen ^ (2 ^ L - N) * gen ^ N
    rw [← pow_add]; congr 1; omega
  · show IsInK (gen ^ L + word (2 ^ 16) 0)
    rw [wfl]; exact isInK_add (gen_pow_isInK _) (gen_pow_isInK _)
  · have hLf : L ≠ 16 := fun h ↦ hne ((lcW_51_eq_zero hflL hL).2 h)
    have hlo := hlow hLf
    obtain ⟨L', hL'⟩ : ∃ L', L = L' + 1 := ⟨L - 1, by omega⟩
    refine ⟨rfl, rfl, rfl, rfl, rfl, ?_, ?_, trivial⟩
    · show LoadHolds rd (q * (gen ^ L * invGenWord)) 0 (gen ^ 2 ^ (L - 1))
      rw [hL', gen_pow_mul_invGen, loadHolds_mul_gen_pow, Nat.add_zero,
        show L' + 1 - 1 = L' by omega]
      exact ht.1 L' (show L' < 34 by omega)
    · show gen ^ N * invGenWord = gen ^ (N - (2 ^ (L - 1) + 1)) * gen ^ 2 ^ (L - 1)
      obtain ⟨N', hN'⟩ : ∃ N', N = N' + 1 :=
        ⟨N - 1, (Nat.sub_add_cancel (lt_of_le_of_lt (Nat.zero_le _) hlo)).symm⟩
      rw [hN', gen_pow_mul_invGen, ← pow_add]
      congr 1; omega

/-- The honest valuation's path is exact. -/
theorem lc_exact {rd : Reader} {N L : ℕ} {q : E} (hN : N < 2 ^ 34) (hLdef : L = max 16 (log2Ceil N))
    (hw : walk (Val.ofArgs (lcWords rd N L q)) lcBody = .ret (lcEvs (Val.ofArgs (lcWords rd N L q))) [.n 59])
    (hev : ∀ e ∈ lcEvs (Val.ofArgs (lcWords rd N L q)), e.Holds rd (Val.ofArgs (lcWords rd N L q))) :
    ∀ e ∈ lcEvs (Val.ofArgs (lcWords rd N L q)), e.Exact rd (Val.ofArgs (lcWords rd N L q)) := by
  refine exact_of_sites lc_sites hw hev fun a ha _ ↦ ?_
  simp only [lcSites, List.mem_cons, List.not_mem_nil, or_false] at ha
  rcases ha with rfl | rfl
  · exact ⟨N, hN, by rw [lcW_0, gen_pow_eq_ofK], lcW_bits rd N L q⟩
  · show Val.ofArgs (lcWords rd N L q) (.n 36) = _
    rw [lcW_bits, bitsNat_bits hN, clog2_eq_log2Ceil, max_comm, ← hLdef, ← gen_pow_eq_ofK]
    rfl

/-! ## The node -/

variable {fs : String → ℕ} {al : String → Bool} {cert : String → V → ℕ}

/-- Where `log2`'s callees end from the cursor `c`: one `assert_small_g_power` at the floor, two
above it. -/
def lcEnd (fs : String → ℕ) (al : String → Bool) (L c : ℕ) : ℕ :=
  if L = 16 then allocBase (al "assert_small_g_power") c + fs "assert_small_g_power"
  else allocBase (al "assert_small_g_power") (allocBase (al "assert_small_g_power") c + fs "assert_small_g_power") +
    fs "assert_small_g_power"

/-- The callees, placed from the cursor `c`. -/
theorem lc_kids {k : ℕ} (hk : 4 ≤ k) {N L : ℕ} (hN : N < 2 ^ 34) (hle : N ≤ 2 ^ L) (hL : L < 34) {q : E}
    {R R' : ℕ → Prop} (hR : ∀ t < 144, ∃ m, q.limb 0 * addressOfIndex (34 + t) = addressOfIndex m ∧ R m)
    (hRR : ∀ i, R i → R' i) {σ : Val} (h1 : σ (.n 1) = q) (h49 : σ (.n 49) = gen ^ (2 ^ L - N))
    (h58 : σ (.n 58) = gen ^ (N - (2 ^ (L - 1) + 1))) (c : ℕ) :
    KidsAtF fs al cert k σ R' (fun rd => ExpTables rd q) (fun rd => HoldsWords rd []) (fun _ => False)
      ((lcCall1 :: if L = 16 then [] else [lcCall2]).map fun _ => PostQuiet)
      (lcCall1 :: if L = 16 then [] else [lcCall2]) c (lcEnd fs al L c) (fun _ => True) (fun _ => False) := by
  have h2L : 2 ^ L < 2 ^ 34 := Nat.pow_lt_pow_right (by decide) hL
  have hasg1 : 2 ^ L - N < 2 ^ 36 := by omega
  have hasg2 : N - (2 ^ (L - 1) + 1) < 2 ^ 36 :=
    lt_of_le_of_lt (Nat.sub_le _ _) (lt_trans hN (by norm_num))
  have a1 : lcCall1.args.map σ = [gen ^ (2 ^ L - N), q] := by
    simp only [lcCall1, List.map_cons, List.map_nil, h49, h1]
  have a2 : lcCall2.args.map σ = [gen ^ (N - (2 ^ (L - 1) + 1)), q] := by
    simp only [lcCall2, List.map_cons, List.map_nil, h58, h1]
  have r1 : lcCall1.rets.map σ = [] := rfl
  have r2 : lcCall2.rets.map σ = [] := rfl
  have t1 : lcCall1.taken = true := rfl
  have t2 : lcCall2.taken = true := rfl
  have hA := fun e (he : e < 2 ^ 36) (fp c : ℕ) =>
    (asg_placed (fs := fs) (al := al) (cert := cert) (k := k) (by omega) he hR fp c).mono
      (R' := R) (D' := fun _ => False) (Out' := fun _ => True)
      (Pre' := fun rd => ExpTables rd q ∧ HoldsWords rd []) (Post' := PostQuiet)
      (fun _ h => h) (fun _ h => h) (fun _ h => h) (fun rd h => h.1) (fun _ _ _ h => h)
  set a := "assert_small_g_power"
  have e1 : allocBase (al a) c + fs a = allocBase (al lcCall1.f) c + fs a := rfl
  by_cases hLf : L = 16
  · rw [ite_pos' hLf, List.map_cons, List.map_nil, KidsAtF]
    simp only [t1, ↓reduceIte]
    refine ⟨fs a, allocBase (al a) c + fs a, R, fun _ => False, fun _ => True,
      fun i hi => Or.inl (hRR i hi), ?_, ?_⟩
    · rw [a1, r1]; exact hA _ hasg1 _ _
    · rw [KidsAtF, lcEnd, ite_pos' hLf]
      exact ⟨rfl, fun _ _ => trivial, fun _ h => h.elim⟩
  · rw [ite_neg' hLf, List.map_cons, List.map_cons, List.map_nil, KidsAtF]
    simp only [t1, ↓reduceIte]
    refine ⟨fs a, allocBase (al a) c + fs a, R, fun _ => False, fun _ => True,
      fun i hi => Or.inl (hRR i hi), ?_, ?_⟩
    · rw [a1, r1]; exact hA _ hasg1 _ _
    rw [KidsAtF]
    simp only [t2, ↓reduceIte]
    refine ⟨fs a, lcEnd fs al L c, R, fun _ => False, fun _ => True,
      fun i hi => Or.inl (hRR i hi), ?_, ?_⟩
    · rw [a2, r2, lcEnd, ite_neg' hLf]
      exact (hA _ hasg2 _ _).mono (fun _ h => h) (fun _ h => h) (fun _ h => h)
        (fun rd h => ⟨h.1, h.2.1⟩) (fun _ _ _ h => h)
    · rw [KidsAtF]
      exact ⟨rfl, fun _ _ => trivial, fun _ h => h.elim⟩

/-- **`log2_ceil_in_the_exponent__L16_L34` completes placed** on `g^N`, `N < 2^34`, its loads in
the exponent table at `q` (`R` holding its first `178` words). -/
theorem log2_placed {k : ℕ} (hk : 6 ≤ k) {N : ℕ} (hN : N < 2 ^ 34) (hL : max 16 (log2Ceil N) < 34) {q : E}
    {R : ℕ → Prop} (hR : ∀ t < 178, ∃ m, q.limb 0 * addressOfIndex t = addressOfIndex m ∧ R m) (fp c : ℕ)
    (hfc : fp + fs "log2_ceil_in_the_exponent__L16_L34" ≤ c) :
    CallAtA fs al cert k "log2_ceil_in_the_exponent__L16_L34" [gen ^ N, q] [gen ^ max 16 (log2Ceil N)] R
      (fun _ => False) (fun _ => True) (fun rd => ExpTables rd q) PostQuiet
      (fs "log2_ceil_in_the_exponent__L16_L34") fp c (lcEnd fs al (max 16 (log2Ceil N)) c) := by
  generalize hLdef : max 16 (log2Ceil N) = L at hL ⊢
  have hle : N ≤ 2 ^ L := log2Ceil_le_iff.mp (hLdef ▸ le_max_right _ _)
  have hflL : 16 ≤ L := hLdef ▸ le_max_left _ _
  have hlow : L ≠ 16 → 2 ^ (L - 1) < N := fun hne ↦ by
    have : L = log2Ceil N := by
      rcases max_choice 16 (log2Ceil N) with h | h
      · exact absurd (hLdef.symm.trans h) hne
      · exact hLdef.symm.trans h
    exact lt_log2Ceil_iff.mp (by omega)
  have hRs : ∀ t < 144, ∃ m, q.limb 0 * addressOfIndex (34 + t) = addressOfIndex m ∧ R m :=
    fun t ht => hR (34 + t) (by omega)
  have hσ0 := fun rd => lcW_congr51 rd (fun _ => none) N L q
  have hcalls : calls (lcEvs (Val.ofArgs (lcWords (fun _ => none) N L q))) =
      lcCall1 :: (if L = 16 then [] else [lcCall2]) := by
    rw [lc_calls_eq]
    by_cases hLf : L = 16
    · rw [ite_pos' ((lcW_51_eq_zero hflL hL).2 hLf), ite_pos' hLf]
    · rw [ite_neg' fun h => hLf ((lcW_51_eq_zero hflL hL).1 h), ite_neg' hLf]
  refine callAtA_nodeRd lc_loop hfc ⟨Val.ofArgs (lcWords (fun _ => none) N L q),
    fn% «log2_ceil_in_the_exponent__L16_L34», lcEvs (Val.ofArgs (lcWords (fun _ => none) N L q)), [.n 59], [],
    (calls (lcEvs (Val.ofArgs (lcWords (fun _ => none) N L q)))).map fun _ => PostQuiet, fun _ => True,
    fun _ => False, find_lce_L16, ?_, fun _ h => h.elim, ?_, fun _ _ => trivial, fun rd hl ht _ => ?_⟩
  · rw [lc_allocs]; exact ⟨by simp, List.Pairwise.nil⟩
  · rw [hcalls, lc_allocs, List.sum_nil, Nat.add_zero]
    exact lc_kids (by omega) hN hle hL hRs (fun i h => Or.inl h) (lcW_1 _ N L q) (lcW_49 _ N L q)
      (lcW_58 _ N L q) c
  -- the memory's valuation
  have hh := lc_holds hk hl ht hL hflL hle hlow
  have hw : walk (Val.ofArgs (lcWords rd N L q)) lcBody =
      .ret (lcEvs (Val.ofArgs (lcWords rd N L q))) [.n 59] := lc_walk _
  have hsat := walk_sat (P := coreProgram) _ lc_wf hh
  rw [hw] at hsat
  have hev : ∀ e ∈ lcEvs (Val.ofArgs (lcWords rd N L q)), e.Holds rd (Val.ofArgs (lcWords rd N L q)) :=
    fun e he ↦ (hsat.1 e he).1
  have hx := lc_exact hN hLdef.symm hw hev
  rw [hσ0 rd] at hw hev hx
  have hw' : walk (Val.ofArgs (lcWords rd N L q)) (fn% «log2_ceil_in_the_exponent__L16_L34»).body =
      .ret (lcEvs (Val.ofArgs (lcWords (fun _ => none) N L q))) [.n 59] := by rw [lc_body]; exact hw
  refine ⟨Val.ofArgs (lcWords rd N L q), by rw [lc_params]; rfl, hw', by rw [List.map_cons, List.map_nil, lcW_59],
    by rw [lc_allocs, lc_allocs], ⟨by rw [lc_allocDsts, lc_allocs]; rfl, by rw [lc_addrs]; simp⟩,
    fun c' hc => ?_, fun A hA => ?_, fun A hA => ?_, hev, fun ts hv hp => ?_⟩
  · rw [hcalls] at hc
    rcases List.mem_cons.mp hc with rfl | hc
    · exact ⟨by simp only [lcCall1, List.map_cons, List.map_nil, lcW_49, lcW_1],
        by simp only [lcCall1, List.map_nil]⟩
    · split at hc
      · exact absurd hc List.not_mem_nil
      · rw [List.mem_singleton] at hc; subst hc
        exact ⟨by simp only [lcCall2, List.map_cons, List.map_nil, lcW_58, lcW_1],
          by simp only [lcCall2, List.map_nil]⟩
  · rw [lc_loadAddrs, lcW_47, lcW_56] at hA
    rcases List.mem_cons.mp hA with rfl | hA
    · obtain ⟨m, hm, hRm⟩ := hR L (by omega)
      exact ⟨m, by rw [limb_gpow_addr, Nat.add_zero, hm], Or.inr (Or.inl hRm)⟩
    · split at hA
      · exact absurd hA List.not_mem_nil
      · rename_i hne
        rw [List.mem_singleton] at hA; subst hA
        have hLf : L ≠ 16 := fun h ↦ hne ((lcW_51_eq_zero hflL hL).2 h)
        obtain ⟨L', hL'⟩ : ∃ L', L = L' + 1 := ⟨L - 1, by omega⟩
        obtain ⟨m, hm, hRm⟩ := hR L' (by omega)
        exact ⟨m, by rw [hL', gen_pow_mul_invGen, limb_gpow_addr, Nat.add_zero, hm], Or.inr (Or.inl hRm)⟩
  · rw [lc_heapHintAddrs] at hA; exact absurd hA List.not_mem_nil
  · exact postQuiet_node find_lce_L16 hw' (walk_quiet (by rw [lc_body]; exact lc_quiet) hw') hx hv hp _

end
end LeanVM.Guest.B1.VsC
