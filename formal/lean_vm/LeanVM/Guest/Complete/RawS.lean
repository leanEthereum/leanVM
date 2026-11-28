module

public import LeanVM.Guest.Complete.Sphincs
public import LeanVM.Guest.B1.Main.RawCChk
public import LeanVM.Guest.B1.Digest.CoverComplete
public import LeanVM.Guest.B1.Digest.LoopComplete
public import LeanVM.Guest.B1.Digest.Range
import LeanVM.Guest.ValRef
import LeanVM.Guest.Data.ValNames.«main_loop3»

/-!
# `main_loop3`, the raw leanSPHINCS signatures, complete

`main_loop3` takes no words of its own (its store into the coverage table is a load of the
caller's words): from the counter `g^j`, on memories holding each signature's coverage cell and
claim and the byte table (`RawSPre`), its tree pops, iteration by iteration, the raw index then
the check's entries (`l3Pops`), every node exact (`main_loop3_completes`). Each iteration's
valuation is explicit (`l3σ`, the bus era's `l4σ`); its call of `verify_sig_lean_sphincs` completes
by `verify_sig_lean_sphincs_completes`, its tail call by induction.
-/

namespace LeanVM.Guest.Complete

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Memory
open LeanVM.Guest.B1
open LeanVM.Protocol.Verifier (gen)
open LeanVM.Guest.B1.Main (l4Pre l4_body l4_params l4_find)
open LeanVM.Guest.B1.Digest (gen_pow_mul_ginv gen_pow_add_isInK gen_pow_inj' ginvW)

@[expose] public section

set_option linter.constructorNameAsVariable false

/-! ## A straight run's events -/

/-- What a straight statement's events need: an atom holds, a conditional call's condition is in
`K`. -/
def SlOk (rd : Reader) (σ : Val) : Stmt → Prop
  | .atom a => a.Holds rd σ
  | .callIf c _ _ => IsInK (σ c)
  | _ => True

theorem slEvs_holds {rd : Reader} {σ : Val} {pre : List Stmt} (h : ∀ s ∈ pre, SlOk rd σ s) :
    ∀ e ∈ pre.flatMap (slEvs σ), e.Holds rd σ := by
  intro e he
  obtain ⟨s, hs, he⟩ := List.mem_flatMap.mp he
  have hs' := h s hs
  match s, hs', he with
  | .atom a, hs', he =>
    simp only [slEvs, List.mem_singleton] at he
    subst he; exact hs'
  | .call .., _, he =>
    simp only [slEvs, List.mem_singleton] at he
    subst he; trivial
  | .callIf c f args, hs', he =>
    simp only [slEvs, List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl
    · exact hs'
    · split <;> trivial

/-! ## Arithmetic -/

theorem gen4 (s : ℕ) : gen ^ s * gen ^ s * (gen ^ s * gen ^ s) = gen ^ (4 * s) := by
  simp only [← pow_add]; congr 1; ring

theorem low_read' {k : ℕ} {rd : Reader} (hl : LowDef k rd) {e : ℕ} (he : e < 2 ^ k) :
    LoadHolds rd (gen ^ e) 0 ((rd (addressOfIndex e)).getD 0) := by
  rw [gen_pow_eq_ofK]; exact B1.loadHolds_low hl he

theorem guard_taken {i n : ℕ} (hn : n < 2 ^ 34) (hi : i + 1 ≤ n) :
    decide (gen ^ i * word 2 0 + gen ^ n ≠ 0) = decide (i + 1 ≠ n) := by
  rw [word_gen, gen_pow_mul_gen]
  refine decide_eq_decide.mpr ⟨fun h he => h (by rw [he]; exact e_add_eq_zero_iff.mpr rfl),
    fun h he => h ?_⟩
  exact gen_pow_inj' (by omega) (by omega) (e_add_eq_zero_iff.mp he)

/-! ## `main_loop3` -/

theorem l4Pre_straight : l4Pre.all Stmt.straight = true := rfl

set_option maxRecDepth 100000 in
theorem l3_pin : Stmt.blockNextOk isComputed pinsInverse
    (coreProgram.getD idx% «main_loop3» default).body = true := by
  rw [l4_body]; decide +kernel

/-- The raw leanSPHINCS signatures: per signature its coverage slot, key, message and signature. -/
structure RawSigs where
  slot : ℕ → ℕ
  pk : ℕ → Sphincs.PublicKey
  msg : ℕ → HashSig.Message
  sig : ℕ → Sphincs.Signature

/-- Iteration `i`'s entries: its raw index, then its check's. -/
def l3Pops (D : RawSigs) (i : ℕ) : List Pop :=
  ("sp_raw_index", [gen ^ D.slot i]) :: Sig.spSegPops (D.pk i) (D.msg i) (D.sig i)

/-- What `main_loop3` reads: for each signature `i < nrs`, its coverage cell at `spc·g^slot` holding
`g^(nrx + i)`, its claim at `tbl·g^(4·slot)` and the byte table at `bb`. -/
def RawSPre (D : RawSigs) (nrs nrx : ℕ) (spc tbl bb : E) (rd : Reader) : Prop :=
  ∀ i < nrs, LoadHolds rd (spc * gen ^ D.slot i) 0 (gen ^ nrx * gen ^ i) ∧
    SphincsPre (tbl * gen ^ (4 * D.slot i)) bb (D.pk i) (D.msg i) rd

/-- `main_loop3`'s completeness from the counter `g^j`: iterations `j ..< nrs`' entries, every node
exact. -/
def RawSPost (D : RawSigs) (j nrs : ℕ) (rd : Reader) (t : Tree) : Prop :=
  t.pops coreProgram rd = (List.range' j (nrs - j)).flatMap (l3Pops D) ∧ t.Every (ExactAt coreProgram rd)

/-- `main_loop3`'s arguments at the counter `g^j`. -/
def l3Args (j nrs Y nrx : ℕ) (spc tbl bb : E) : List E :=
  [gen ^ j, gen ^ nrs, gen ^ Y, spc, gen ^ nrx, tbl, bb]

/-- `main_loop3`'s tail call's arguments. -/
def l3TArgs : List V :=
  [.n (val% «main_loop3» "s5#4"), .n (val% «main_loop3» "bound"), .n (val% «main_loop3» "lean_sphincs_slots_g"),
    .n (val% «main_loop3» "sp_cover"), .n (val% «main_loop3» "n_raw_x_g"), .n (val% «main_loop3» "lean_sphincs_table"),
    .n (val% «main_loop3» "byte_bits")]

/-- `main_loop3`'s valuation at the counter `g^j`, the signature's slot `s`. -/
noncomputable def l3σ (rd : Reader) (j nrs Y nrx s : ℕ) (spc tbl bb : E) : Val :=
  B1.Val.ofArgs [gen ^ j, gen ^ nrs, gen ^ Y, spc, gen ^ nrx, tbl, bb,
    gen ^ s, ginvW, gen ^ Y * ginvW, gen ^ (Y - 1 - s), (rd (addressOfIndex s)).getD 0,
    (rd (addressOfIndex (Y - 1 - s))).getD 0, gen ^ nrx * gen ^ j,
    spc * gen ^ s, gen ^ s * gen ^ s, gen ^ s * gen ^ s * (gen ^ s * gen ^ s),
    tbl * (gen ^ s * gen ^ s * (gen ^ s * gen ^ s)), word 2 0, gen ^ j * word 2 0,
    gen ^ j * word 2 0 + gen ^ nrs, word 2 0, gen ^ j * word 2 0]

/-- `main_loop3`'s events pop the raw index, then its two callees' entries. -/
theorem l3_splice (rd : Reader) (σ : Val) (a b : List Pop) :
    splice rd σ (l4Pre.flatMap (slEvs σ)) [a, b] =
      ("sp_raw_index", [σ (.n (val% «main_loop3» "off_hint"))]) :: (a ++ b) := by
  by_cases h : σ (.n (val% «main_loop3» "s5#2")) = 0
  · simp only [l4Pre, List.flatMap_cons, List.flatMap_nil, slEvs, h, ↓reduceIte]
    simp [splice, Atom.pops, Hint.pops, Dest.words]
  · simp only [l4Pre, List.flatMap_cons, List.flatMap_nil, slEvs, h, ↓reduceIte]
    simp [splice, Atom.pops, Hint.pops, Dest.words]

set_option maxRecDepth 100000 in
/-- **One iteration of `main_loop3` completes**, given its tail's completeness. -/
theorem l3_step {k : ℕ} (hk : 8 ≤ k) {nrs Y nrx : ℕ} (hY : Y ≤ 2 ^ k) (hnrs : nrs < 2 ^ 34) (D : RawSigs)
    (hs : ∀ i < nrs, D.slot i < Y)
    (hv : ∀ i < nrs, Sphincs.verifyWithKeccak (D.pk i) (D.msg i) (D.sig i) = true) (spc tbl bb : E) {j : ℕ}
    (hj : j < nrs)
    (htail : j + 1 < nrs → CallCompletes0 k name% «main_loop3» (l3Args (j + 1) nrs Y nrx spc tbl bb) []
      (RawSPre D nrs nrx spc tbl bb) (RawSPost D (j + 1) nrs)) :
    CallCompletes0 k name% «main_loop3» (l3Args j nrs Y nrx spc tbl bb) [] (RawSPre D nrs nrx spc tbl bb)
      (RawSPost D j nrs) := by
  refine callCompletes0_node fun rd hl hp => ?_
  have hsj := hs j hj
  have hYk : Y ≤ 2 ^ k := hY
  set s := D.slot j with hsd
  set σ := l3σ rd j nrs Y nrx s spc tbl bb with hσ
  have hw := walk_straight σ [] l4Pre l4Pre_straight
  rw [← l4_body] at hw
  obtain ⟨-, -, -, hpc⟩ := straight_parts σ _ l4Pre_straight
  have hev : ∀ e ∈ l4Pre.flatMap (slEvs σ), e.Holds rd σ := by
    refine slEvs_holds fun st hst => ?_
    simp only [l4Pre, List.mem_cons, List.not_mem_nil, or_false] at hst
    rcases hst with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl
    all_goals simp only [SlOk, Atom.Holds, hσ, l3σ, B1.ofArgs_n, List.getD_cons_succ,
      List.getD_cons_zero]
    · refine ⟨low_read' hl (by omega), ?_, low_read' hl (by omega)⟩
      rw [gen_pow_mul_ginv (by omega), ← pow_add]; congr 1; omega
    · exact (hp j hj).1
    · rw [word_gen, gen_pow_mul_gen]; exact gen_pow_add_isInK _ _
  have hc : calls (l4Pre.flatMap (slEvs σ)) =
      [⟨"verify_sig_lean_sphincs", [.n (val% «main_loop3» "s3#2"), .n (val% «main_loop3» "byte_bits")], [], true⟩,
        ⟨name% «main_loop3», l3TArgs, [], decide (σ (.n (val% «main_loop3» "s5#2")) ≠ 0)⟩] := by
    rw [hpc]; rfl
  -- the check
  obtain ⟨t0, hn0, hv0, hb0, hp0, hx0⟩ := verify_sig_lean_sphincs_completes hk (tbl * gen ^ (4 * s)) bb
    (D.pk j) (D.msg j) (D.sig j) (hv j hj) rd hl (hp j hj).2
  have hv0' : t0.Valid coreProgram rd
      ([V.n (val% «main_loop3» "s3#2"), .n (val% «main_loop3» "byte_bits")].map σ) [] := by
    have ea : [V.n (val% «main_loop3» "s3#2"), .n (val% «main_loop3» "byte_bits")].map σ =
        [tbl * gen ^ (4 * s), bb] := by
      simp only [List.map_cons, List.map_nil, hσ, l3σ, B1.ofArgs_n, List.getD_cons_succ,
        List.getD_cons_zero, gen4]
    rw [ea]; exact hv0
  -- the tail
  have e52 : σ (.n (val% «main_loop3» "s5#2")) = gen ^ j * word 2 0 + gen ^ nrs := rfl
  obtain ⟨t1, hk1, hb1, hp1, hx1⟩ : ∃ t1 : Tree,
      Tree.KidsValid coreProgram rd σ [⟨name% «main_loop3», l3TArgs, [],
        decide (σ (.n (val% «main_loop3» "s5#2")) ≠ 0)⟩] [t1] ∧ t1.BufsOk coreProgram ∧
      t1.pops coreProgram rd = (List.range' (j + 1) (nrs - (j + 1))).flatMap (l3Pops D) ∧
      t1.Every (ExactAt coreProgram rd) := by
    by_cases hlt : j + 1 < nrs
    · obtain ⟨t1, hn, hv1, hb, hp', hx⟩ := htail hlt rd hl hp
      have htk : decide (σ (.n (val% «main_loop3» "s5#2")) ≠ 0) = true := by
        rw [e52, guard_taken hnrs (by omega)]; exact decide_eq_true (by omega)
      have et : l3TArgs.map σ = l3Args (j + 1) nrs Y nrx spc tbl bb := by
        simp only [l3TArgs, l3Args, List.map_cons, List.map_nil, hσ, l3σ, B1.ofArgs_n, List.getD_cons_succ,
          List.getD_cons_zero, word_gen, gen_pow_mul_gen]
      have hv1' : t1.Valid coreProgram rd (l3TArgs.map σ) [] := by rw [et]; exact hv1
      exact ⟨t1, kidsValid_cons_taken htk hn hv1' kidsValid_nil, hb, hp', hx⟩
    · have htk : decide (σ (.n (val% «main_loop3» "s5#2")) ≠ 0) = false := by
        rw [e52, guard_taken hnrs (by omega)]; exact decide_eq_false (by omega)
      refine ⟨.phantom name% «main_loop3» (B1.Val.ofArgs (l3TArgs.map σ)),
        kidsValid_cons_skip htk l4_find (by rw [l4_params]; rfl) kidsValid_nil, ?_, ?_, Tree.every_phantom⟩
      · rw [Tree.BufsOk]; trivial
      · rw [Tree.pops, show nrs - (j + 1) = 0 by omega]; rfl
  refine ⟨σ, _, _, [], [t0, t1], l4_find, by rw [l4_params]; rfl, hw, rfl, hev, ?_, ?_, ?_, ?_⟩
  · rw [hc]
    exact kidsValid_cons_taken rfl hn0 hv0' hk1
  · rw [Tree.BufsOkKids, Tree.BufsOkKids, Tree.BufsOkKids]
    exact ⟨hb0, hb1, trivial⟩
  · rw [pops_node l4_find hw, Tree.popsKids, Tree.popsKids, Tree.popsKids, l3_splice, hp0, hp1,
      show nrs - j = nrs - (j + 1) + 1 by omega, List.range'_succ, List.flatMap_cons]
    rfl
  · refine Tree.every_node.mpr ⟨exactAt_of_walk l4_find hw (exact_of_pinned l3_pin hw hev rd), ?_⟩
    rw [Tree.EveryKids, Tree.EveryKids, Tree.EveryKids]
    exact ⟨hx0, hx1, trivial⟩

/-- **`main_loop3` completes** from every counter below the count, on memories defined below `2^k`
(`8 ≤ k`, the slots `Y ≤ 2^k`): it pops each iteration's raw index and check's entries, every node
exact. -/
theorem main_loop3_completes {k : ℕ} (hk : 8 ≤ k) {nrs Y nrx : ℕ} (hY : Y ≤ 2 ^ k) (hnrs : nrs < 2 ^ 34)
    (D : RawSigs) (hs : ∀ i < nrs, D.slot i < Y)
    (hv : ∀ i < nrs, Sphincs.verifyWithKeccak (D.pk i) (D.msg i) (D.sig i) = true) (spc tbl bb : E) :
    ∀ j < nrs, CallCompletes0 k name% «main_loop3» (l3Args j nrs Y nrx spc tbl bb) []
      (RawSPre D nrs nrx spc tbl bb) (RawSPost D j nrs) := by
  have key : ∀ t j, j + 1 + t = nrs → CallCompletes0 k name% «main_loop3» (l3Args j nrs Y nrx spc tbl bb) []
      (RawSPre D nrs nrx spc tbl bb) (RawSPost D j nrs) := by
    intro t
    induction t with
    | zero => intro j hj; exact l3_step hk hY hnrs D hs hv spc tbl bb (by omega) fun h => absurd h (by omega)
    | succ t ih => intro j hj; exact l3_step hk hY hnrs D hs hv spc tbl bb (by omega) fun _ => ih (j + 1) (by omega)
  intro j hj
  exact key (nrs - j - 1) j (by omega)

end
end LeanVM.Guest.Complete
