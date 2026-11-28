/-
  LeanVM.Guest.B1.VsC.Log2C

  `log2_ceil_in_the_exponent__L16_L34` completes, layout-free.
-/

module

public import LeanVM.Guest.B1.VsC.AsgC
public import LeanVM.Guest.B1.Bits.Log2
public import LeanVM.Guest.Value.FieldBits
public import LeanVM.Guest.Memory.Straight
public import LeanVM.Guest.Memory.GuestWf
import LeanVM.Guest.CoreRef

/-!
# `log2_ceil_in_the_exponent`, complete

The archive's template (`lcBody`, restored at the floor `16`, the one the guest compiles) and its
honest valuation (`lcVal`): `N`'s bits, `L = max 16 (log2Ceil N)`, the range checks' words read
from the memory, `g^(2^L)` and above the floor `g^(2^(L-1))` from the exponent table.
`log2_complete`: on `g^N`, `N < 2^34`, `L < 34`, a memory defined below `2^k`, `k ≥ 6`, holding
the table at `q`, the call returns `g^L` over one or two quiet `assert_small_g_power` calls,
popping nothing, exact (its bits `N`'s, its log theirs). The range checks' touched words are the
only ones read from the memory, and no call's (`callCompletes_nodeRd`).
-/

namespace LeanVM.Guest.B1.VsC

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Memory LeanVM.Guest.B1
open LeanVM.Guest.Complete LeanVM.Guest.Value
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

/-! ## The template -/

/-- The check above the floor: `g_N · g⁻¹ / g_squares[g^(L-1)]` a small g-power. -/
def lcMin : List Stmt :=
  [.atom (.const (.n 52) invGenWord), .atom (.mul (.n 53) (.n 0) (.n 52)),
    .atom (.const (.n 54) invGenWord), .atom (.mul (.n 55) (.n 36) (.n 54)),
    .atom (.mul (.n 56) (.n 1) (.n 55)), .atom (.load (.n 57) (.n 56) 0),
    .atom (.mul (.n 53) (.n 58) (.n 57)), .call "assert_small_g_power" [.n 58, .n 1] []]

/-- The run of its frame the bits are hinted into. -/
def lcBits : List V := (List.range 34).map fun k => .n (2 + k)

/-- The statements before the check above the floor. -/
def lcHead : List Stmt :=
  [.atom (.hint (.bitsExp (.n 0) 34 (.stack lcBits))),
    .atom (.hint (.log2Ceil (.stack lcBits) 34 16 (.n 36))),
    .atom (.const (.n 37) (word (2 ^ 33) 0)),
    .atom (.rangeCheck (.n 36) (.n 38) (.n 39) (.n 40) (.n 37)),
    .atom (.const (.n 41) (word (2 ^ 33) 0)), .atom (.const (.n 42) (word (2 ^ 16) 0)),
    .atom (.mul (.n 36) (.n 43) (.n 42)),
    .atom (.rangeCheck (.n 43) (.n 44) (.n 45) (.n 46) (.n 41)),
    .atom (.mul (.n 47) (.n 1) (.n 36)), .atom (.load (.n 48) (.n 47) 0),
    .atom (.mul (.n 48) (.n 49) (.n 0)), .call "assert_small_g_power" [.n 49, .n 1] [],
    .atom (.const (.n 50) (word (2 ^ 16) 0)), .atom (.add (.n 51) (.n 36) (.n 50))]

/-- The expansion of `log2_ceil_in_the_exponent__L16_L34`. -/
def lcBody : List Stmt :=
  lcHead ++ [.ite (.n 51) [] lcMin, .atom (.copy (.n 59) (.n 36)), .ret [.n 59]]

theorem lc_body : Fn.body fn% «log2_ceil_in_the_exponent__L16_L34» = lcBody :=
  stmtsEqb_sound (by decide +kernel)

theorem lc_params : Fn.params fn% «log2_ceil_in_the_exponent__L16_L34» = [.n 0, .n 1] := rfl

/-! ## The walk -/

/-- A straight block, then the rest: its events, then the rest's walk. -/
theorem walk_straight_pre (σ : Val) : ∀ (pre rest : List Stmt), pre.all Stmt.straight = true →
    walk σ (pre ++ rest) = (walk σ rest).pre (pre.flatMap (slEvs σ))
  | [], rest, _ => by rw [List.nil_append]; cases walk σ rest <;> rfl
  | s :: pre, rest, h => by
    simp only [List.all_cons, Bool.and_eq_true] at h
    rw [List.cons_append, walk, walk_straight_pre σ pre rest h.2, walk1_straight σ s h.1,
      List.flatMap_cons]
    cases walk σ rest <;> simp [Out.seq, Out.pre]

/-- The events of `log2_ceil_in_the_exponent`. -/
noncomputable def lcEvs (σ : Val) : List Ev :=
  lcHead.flatMap (slEvs σ) ++ (.inK (.n 51) ::
    ((if σ (.n 51) = 0 then [] else lcMin).flatMap (slEvs σ) ++ [.atom (.copy (.n 59) (.n 36))]))

theorem lc_walk (σ : Val) : walk σ lcBody = .ret (lcEvs σ) [.n 59] := by
  rw [lcBody, walk_straight_pre σ _ _ rfl, walk, walk1,
    show [Stmt.atom (.copy (.n 59) (.n 36)), .ret [.n 59]] = [Stmt.atom (.copy (.n 59) (.n 36))] ++
      [.ret [.n 59]] from rfl, walk_straight σ _ _ rfl]
  by_cases h : σ (.n 51) = 0
  · simp [h, lcEvs, walk, Out.seq, Out.pre, slEvs]
  · simp [h, lcEvs, Out.seq, Out.pre, walk_straight_fall σ lcMin rfl, slEvs]

theorem lcEvs_congr {σ σ' : Val} (h : σ (.n 51) = σ' (.n 51)) : lcEvs σ = lcEvs σ' := by
  unfold lcEvs
  rw [h]
  split <;> rfl

/-- The asserted call on `g^(2^L) / g_N`. -/
def lcCall1 : Call := ⟨"assert_small_g_power", [.n 49, .n 1], [], true⟩

/-- The asserted call above the floor. -/
def lcCall2 : Call := ⟨"assert_small_g_power", [.n 58, .n 1], [], true⟩

theorem lc_calls_eq (σ : Val) :
    calls (lcEvs σ) = lcCall1 :: (if σ (.n 51) = 0 then [] else [lcCall2]) := by
  unfold lcEvs
  split <;> rfl

/-- The body under any call relation, valuation and continuation. -/
theorem lc_holds_iff (C : CallRel) (rd : Reader) (σ : Val) (kret : List E → Prop) :
    Stmt.HoldsList C rd σ lcBody False kret ↔
      σ (.n 37) = word (2 ^ 33) 0 ∧
      (LoadHolds rd (σ (.n 36)) 0 (σ (.n 39)) ∧ σ (.n 37) = σ (.n 36) * σ (.n 38) ∧
        LoadHolds rd (σ (.n 38)) 0 (σ (.n 40))) ∧
      σ (.n 41) = word (2 ^ 33) 0 ∧ σ (.n 42) = word (2 ^ 16) 0 ∧
      σ (.n 36) = σ (.n 43) * σ (.n 42) ∧
      (LoadHolds rd (σ (.n 43)) 0 (σ (.n 45)) ∧ σ (.n 41) = σ (.n 43) * σ (.n 44) ∧
        LoadHolds rd (σ (.n 44)) 0 (σ (.n 46))) ∧
      σ (.n 47) = σ (.n 1) * σ (.n 36) ∧ LoadHolds rd (σ (.n 47)) 0 (σ (.n 48)) ∧
      σ (.n 48) = σ (.n 49) * σ (.n 0) ∧
      C "assert_small_g_power" [σ (.n 49), σ (.n 1)] [] ∧
      σ (.n 50) = word (2 ^ 16) 0 ∧ σ (.n 51) = σ (.n 36) + σ (.n 50) ∧
      (IsInK (σ (.n 51)) ∧ (σ (.n 51) ≠ 0 →
        σ (.n 52) = invGenWord ∧ σ (.n 53) = σ (.n 0) * σ (.n 52) ∧ σ (.n 54) = invGenWord ∧
        σ (.n 55) = σ (.n 36) * σ (.n 54) ∧ σ (.n 56) = σ (.n 1) * σ (.n 55) ∧
        LoadHolds rd (σ (.n 56)) 0 (σ (.n 57)) ∧ σ (.n 53) = σ (.n 58) * σ (.n 57) ∧
        C "assert_small_g_power" [σ (.n 58), σ (.n 1)] [])) ∧
      σ (.n 59) = σ (.n 36) ∧ kret [σ (.n 59)] := by
  rw [lcBody, lcHead]
  simp only [List.cons_append, List.nil_append, Stmt.HoldsList]
  simp only [holds_ite_noRet (.n 51) [] lcMin rfl rfl]
  simp only [lcMin, Stmt.HoldsList, Stmt.Holds, Atom.Holds, List.map_cons, List.map_nil, true_and,
    and_true, implies_true]

/-! ## Exactness -/

/-- The computed hints pinned only by the valuation: the bits and their log. -/
def lcSites : List Atom :=
  [.hint (.bitsExp (.n 0) 34 (.stack lcBits)), .hint (.log2Ceil (.stack lcBits) 34 16 (.n 36))]

theorem lc_sites :
    Stmt.blockNextOk (fun a => isComputed a && !decide (a ∈ lcSites)) pinsInverse lcBody = true := by
  decide +kernel

/-- The integer of a number's bit words is the number. -/
theorem bitsNat_bits {N n : ℕ} (hN : N < 2 ^ n) :
    bitsNat ((List.range n).map fun j => Prover.Exec.bitWord (N.testBit j)) n = N := by
  have key : ∀ m ≤ n, (List.range m).foldl (fun w j => if ((List.range n).map fun j =>
      Prover.Exec.bitWord (N.testBit j)).getD j 0 = 0 then w else w + 2 ^ j) 0 = bitsVal N.testBit m := by
    intro m hm
    induction m with
    | zero => rfl
    | succ m ih =>
      rw [List.range_succ, List.foldl_append, ih (by omega), List.foldl_cons, List.foldl_nil, bitsVal,
        List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range (by omega)]
      cases h : N.testBit m <;> simp [h, Prover.Exec.bitWord]
  rw [bitsNat, key n le_rfl, bitsVal_testBit hN]

theorem clog2_eq_log2Ceil (w : ℕ) : clog2 w = log2Ceil w := by
  unfold clog2 log2Ceil bitLength
  split_ifs <;> omega

/-! ## Completeness -/

theorem CallCompletes.mono_pre {k : ℕ} {f : String} {args rets : List E} {P1 P2 : Reader → Prop}
    {Post : Reader → Tree → Prop} (h : CallCompletes k f args rets P1 Post)
    (hp : ∀ rd, P2 rd → P1 rd) : CallCompletes k f args rets P2 Post := fun b =>
  let ⟨n, W, hW, hc⟩ := h b
  ⟨n, W, hW, fun rd hl hw hP => hc rd hl hw (hp rd hP)⟩

/-- The honest words of `log2_ceil_in_the_exponent` on `g^N`, `L` and the table at `q`, the
range checks' words read from `rd`. -/
noncomputable def lcWords (rd : Reader) (N L : ℕ) (q : E) : List E :=
  [gen ^ N, q] ++ (List.range 34).map (fun j => Prover.Exec.bitWord (N.testBit j)) ++
    [gen ^ L, word (2 ^ 33) 0, (rcLow rd L 34).1, (rcLow rd L 34).2.1, (rcLow rd L 34).2.2,
    word (2 ^ 33) 0, word (2 ^ 16) 0, gen ^ (L - 16), (rcLow rd (L - 16) 34).1,
    (rcLow rd (L - 16) 34).2.1, (rcLow rd (L - 16) 34).2.2, q * gen ^ L, gen ^ 2 ^ L,
    gen ^ (2 ^ L - N), word (2 ^ 16) 0, gen ^ L + word (2 ^ 16) 0, invGenWord,
    gen ^ N * invGenWord, invGenWord, gen ^ L * invGenWord, q * (gen ^ L * invGenWord),
    gen ^ 2 ^ (L - 1), gen ^ (N - (2 ^ (L - 1) + 1)), gen ^ L]

set_option maxHeartbeats 2000000 in
/-- **`log2_ceil_in_the_exponent__L16_L34` completes**: on `g^N`, `N < 2^34`, it returns
`g^L`, `L = max 16 (log2Ceil N) < 34`, on a memory defined below `2^k`, `6 ≤ k`, holding the
exponent table at `q`. -/
theorem log2_complete (k : ℕ) (hk : 6 ≤ k) {N : ℕ} (hN : N < 2 ^ 34)
    (hL : max 16 (log2Ceil N) < 34) (q : E) :
    CallCompletes k "log2_ceil_in_the_exponent__L16_L34" [gen ^ N, q] [gen ^ max 16 (log2Ceil N)]
      (fun rd => ExpTables rd q) PostQuiet := by
  set L := max 16 (log2Ceil N) with hLdef
  have hle : N ≤ 2 ^ L := log2Ceil_le_iff.mp (le_max_right _ _)
  have hflL : 16 ≤ L := le_max_left _ _
  have h2L : 2 ^ L < 2 ^ 34 := Nat.pow_lt_pow_right (by decide) hL
  have hlow : L ≠ 16 → 2 ^ (L - 1) < N := fun hne ↦ by
    have : L = log2Ceil N := by
      rcases max_choice 16 (log2Ceil N) with h | h
      · exact absurd (hLdef.trans h) hne
      · exact hLdef.trans h
    exact lt_log2Ceil_iff.mp (by omega)
  clear_value L
  have wfl : word (2 ^ 16) 0 = gen ^ 16 := word_two_pow (by omega)
  have w33 : word (2 ^ 33) 0 = ofK (addressOfIndex (34 - 1)) := by
    rw [word_two_pow (by norm_num), gen_pow_eq_ofK]
  let σ : Reader → Val := fun rd => B1.Val.ofArgs (lcWords rd N L q)
  have e1 : ∀ r, σ r (.n 1) = q := fun _ => rfl
  have e49 : ∀ r, σ r (.n 49) = gen ^ (2 ^ L - N) := fun _ => rfl
  have e51 : ∀ r, σ r (.n 51) = gen ^ L + word (2 ^ 16) 0 := fun _ => rfl
  have e58 : ∀ r, σ r (.n 58) = gen ^ (N - (2 ^ (L - 1) + 1)) := fun _ => rfl
  have h19 : ∀ rd, σ rd (.n 51) = 0 ↔ L = 16 := fun rd => by
    show gen ^ L + word (2 ^ 16) 0 = 0 ↔ _
    rw [wfl, e_add_eq_zero_iff]
    exact ⟨fun h ↦ gen_pow_inj (by omega) (by omega) h, fun h ↦ by rw [h]⟩
  have hes : ∀ rd, lcEvs (σ rd) = lcEvs (σ fun _ => none) := fun rd => lcEvs_congr ((e51 rd).trans (e51 _).symm)
  have hcalls : calls (lcEvs (σ fun _ => none)) = lcCall1 :: (if L = 16 then [] else [lcCall2]) := by
    rw [lc_calls_eq]
    by_cases hLf : L = 16
    · rw [ite_pos' ((h19 _).2 hLf), ite_pos' hLf]
    · rw [ite_neg' fun h => hLf ((h19 _).1 h), ite_neg' hLf]
  have hfind : coreProgram.find? "log2_ceil_in_the_exponent__L16_L34" =
      some fn% «log2_ceil_in_the_exponent__L16_L34» := find_lce_L16
  have hasg1 : 2 ^ L - N < 2 ^ 36 := by omega
  have hasg2 : N - (2 ^ (L - 1) + 1) < 2 ^ 36 :=
    lt_of_le_of_lt (Nat.sub_le _ _) (lt_trans hN (by norm_num))
  refine callCompletes_nodeRd fun b => ⟨0, [], (σ fun _ => none), fn% «log2_ceil_in_the_exponent__L16_L34»,
    lcEvs (σ fun _ => none), [.n 59], (calls (lcEvs (σ fun _ => none))).map fun _ => PostQuiet, wordsIn_nil b, hfind, ?_,
    fun rd hl _ ht => ?_⟩
  · rw [hcalls]
    by_cases hLf : L = 16
    · rw [ite_pos' hLf]
      simp only [KidsCompl, List.map_cons, List.map_nil, List.headD_cons, lcCall1, ↓reduceIte, and_true,
        e49, e1]
      exact CallCompletes.mono_pre (assert_small_g_power_complete k (by omega) hasg1 q) fun _ h => h.2
    · rw [ite_neg' hLf]
      simp only [KidsCompl, List.map_cons, List.map_nil, List.headD_cons, List.tail_cons, lcCall1,
        lcCall2, ↓reduceIte, and_true, e49, e58, e1]
      exact ⟨CallCompletes.mono_pre (assert_small_g_power_complete k (by omega) hasg1 q) fun _ h => h.2,
        CallCompletes.mono_pre (assert_small_g_power_complete k (by omega) hasg2 q) fun _ h => h.2⟩
  -- the memory's valuation
  have hK34 : 34 ≤ 2 ^ k := le_trans (by decide) (Nat.pow_le_pow_right (by decide) hk)
  obtain ⟨r1a, r1b, r1c⟩ := rc_complete_low hl (K := 34) hK34 hL
  obtain ⟨r2a, r2b, r2c⟩ := rc_complete_low hl (K := 34) hK34 (show L - 16 < 34 by omega)
  have hh : Stmt.HoldsList (fun _ _ _ ↦ True) rd (σ rd) lcBody False (fun r ↦ r = [gen ^ L]) := by
    refine (lc_holds_iff _ rd (σ rd) _).2 ⟨rfl, ⟨?_, ?_, r1c⟩, rfl, rfl, ?_, ⟨?_, ?_, r2c⟩, rfl,
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
    · have hLf : L ≠ 16 := fun h ↦ hne ((h19 rd).2 h)
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
  have hw : walk (σ rd) (Fn.body fn% «log2_ceil_in_the_exponent__L16_L34») =
      .ret (lcEvs (σ fun _ => none)) [.n 59] := by rw [lc_body, lc_walk, hes]
  have hh' : Stmt.HoldsList (fun _ _ _ ↦ True) rd (σ rd) (Fn.body fn% «log2_ceil_in_the_exponent__L16_L34»)
      False (fun r ↦ r = [gen ^ L]) := by rw [lc_body]; exact hh
  have hsat := walk_sat (P := coreProgram) _
    (coreProgram_wf _ (List.mem_of_find?_eq_some hfind)) hh'
  rw [hw] at hsat
  have hev : ∀ e ∈ lcEvs (σ fun _ => none), e.Holds rd (σ rd) := fun e he ↦ (hsat.1 e he).1
  refine ⟨σ rd, by rw [lc_params]; rfl, hw, rfl, ?_, hev, fun ts hv hp => ?_⟩
  · intro c hc
    rw [hcalls] at hc
    rcases List.mem_cons.mp hc with rfl | hc
    · exact ⟨by simp only [lcCall1, List.map_cons, List.map_nil, e49, e1],
        by simp only [lcCall1, List.map_nil]⟩
    · split at hc
      · exact absurd hc List.not_mem_nil
      · rw [List.mem_singleton] at hc; subst hc
        exact ⟨by simp only [lcCall2, List.map_cons, List.map_nil, e58, e1],
          by simp only [lcCall2, List.map_nil]⟩
  · have hw' := hw
    rw [← hes rd] at hw'
    have hx : ∀ e ∈ lcEvs (σ rd), e.Exact rd (σ rd) := by
      refine exact_of_sites (by rw [lc_body]; exact lc_sites) hw' (by rw [hes]; exact hev)
        fun a ha _ ↦ ?_
      have hbits : Dest.words rd (σ rd) (.stack lcBits) =
          (List.range 34).map fun j => Prover.Exec.bitWord (N.testBit j) := rfl
      simp only [lcSites, List.mem_cons, List.not_mem_nil, or_false] at ha
      rcases ha with rfl | rfl
      · exact ⟨N, hN, by show gen ^ N = _; rw [gen_pow_eq_ofK], hbits⟩
      · show gen ^ L = _
        rw [hbits, bitsNat_bits hN, clog2_eq_log2Ceil, max_comm, ← hLdef, gen_pow_eq_ofK]
    rw [hes] at hx
    exact postQuiet_node hfind hw (walk_quiet (by rw [lc_body]; decide +kernel) hw) hx hv hp _

end
end LeanVM.Guest.B1.VsC
