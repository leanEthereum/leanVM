/-
  LeanVM.Guest.B1.Bits.Log2Placed

  `assert_small_g_power` and `log2_ceil_in_the_exponent`, placed and bounded: complete at every
  frame pointer on every memory defined below `2^κ` holding the exponent table, by a tree of at
  most their frames and buffers.
-/

module

public import LeanVM.Guest.B1.Bits.Log2
public import LeanVM.Guest.B1.Bits.Tables
public import LeanVM.Guest.Budget.Bounded
public import LeanVM.Guest.Memory.Uniform

/-!
# `assert_small_g_power` and `log2_ceil_in_the_exponent`, placed

* `asg_completeAtB`: `assert_small_g_power` is a leaf: on `g^e`, `e < 2^36`, and the exponent
  table (`log2Lin sqE`, the `236` words of `exponent_tables`) it returns, within its frame. Its
  range checks read the memory below `2^4` (`asg_rc_low`), its shares the table (`asg_shares`).
* `lce_completeAtB`: `log2_ceil_in_the_exponent` at the floor `fl` allocates the `34` hinted bits
  of `N` (`allocDyn`, read by no instruction), range checks `L` and `L - fl` below `34` (the memory
  below `2^6`), reads `g^(2^L)` (and above the floor `g^(2^(L-1))`) from the table and calls
  `assert_small_g_power` once (`L = fl`) or twice: on `g^N` and the table it returns `g^L`,
  `L = max fl (log2Ceil N)`, within `fs f + 34 + 2 · fs "assert_small_g_power"` words. Its walk
  (`lc_walk`) takes the check above the floor as the valuation says.
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Memory
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Guest.B1.Main (Layout MemL RegionL)

@[expose] public section

variable {fs : String → ℕ} {cert : String → V → ℕ}

/-! ## The layouts -/

/-- The exponent table at `sqE` (`ExpTables`, as words). -/
def log2Lin (sqE : ℕ) : Main.Layout := [(sqE, expTableWords)]

/-- The bits of `N`, low first. -/
def bitWords (N : ℕ) : List E := (List.range 34).map fun j ↦ bitE (N.testBit j)

theorem length_expTableWords : expTableWords.length = 236 := by
  simp [expTableWords, length_etWordsN]

theorem memL_single {rd : Reader} {b : ℕ} {w : List E} (h : MemL rd [(b, w)]) :
    ReadsAt rd (ofK (Parameters.addressOfIndex b)) w := h _ (List.mem_singleton_self _)

theorem expTables_of_memL {rd : Reader} {sqE : ℕ} (h : MemL rd (log2Lin sqE)) :
    ExpTables rd (ofK (Parameters.addressOfIndex sqE)) := by
  refine (expTables_iff_words _ _).2 fun o ho ↦ ?_
  have := memL_single h o (by rw [length_expTableWords]; exact ho)
  rwa [← List.getD_eq_getElem _ (0 : E)] at this

theorem limb_ofK_gpow_gen_off (b n off : ℕ) :
    (ofK (Parameters.addressOfIndex b) * gen ^ n).limb 0 * Parameters.addressOfIndex off =
        Parameters.addressOfIndex (b + n + off) := by
  rw [gen_pow_eq_ofK, ← ofK_mul, limb_ofK]
  simp only [Fin.isValue, Fin.val_zero, ↓reduceIte]
  rw [gpow_add', gpow_add']

theorem regionL_log2Lin {sqE i : ℕ} (h1 : sqE ≤ i) (h2 : i < sqE + 236) :
    RegionL (log2Lin sqE) i :=
  ⟨_, List.mem_singleton_self _, h1, by rw [length_expTableWords]; exact h2⟩

theorem regionL_app {L L' : Main.Layout} {i : ℕ} (h : RegionL (L ++ L') i) :
    RegionL L i ∨ RegionL L' i := by
  obtain ⟨q, hq, h1, h2⟩ := h
  rcases List.mem_append.mp hq with hq | hq
  · exact Or.inl ⟨q, hq, h1, h2⟩
  · exact Or.inr ⟨q, hq, h1, h2⟩

theorem allocDsts_inK (c : V) (es : List Ev) : allocDsts (.inK c :: es) = allocDsts es := rfl
theorem allocs_inK (σ : Val) (c : V) (es : List Ev) : allocs σ (.inK c :: es) = allocs σ es := rfl
theorem addrs_inK (c : V) (es : List Ev) : addrs (.inK c :: es) = addrs es := rfl
theorem calls_inK (c : V) (es : List Ev) : calls (.inK c :: es) = calls es := rfl
theorem loadAddrs_inK (σ : Val) (c : V) (es : List Ev) :
    loadAddrs σ (.inK c :: es) = loadAddrs σ es := rfl
theorem allocDsts_app (a b : List Ev) : allocDsts (a ++ b) = allocDsts a ++ allocDsts b :=
  List.filterMap_append
theorem allocs_app (σ : Val) (a b : List Ev) : allocs σ (a ++ b) = allocs σ a ++ allocs σ b :=
  List.filterMap_append
theorem addrs_app (a b : List Ev) : addrs (a ++ b) = addrs a ++ addrs b := List.filterMap_append
theorem calls_app (a b : List Ev) : calls (a ++ b) = calls a ++ calls b := List.filterMap_append
theorem loadAddrs_app (σ : Val) (a b : List Ev) :
    loadAddrs σ (a ++ b) = loadAddrs σ a ++ loadAddrs σ b := List.filterMap_append

/-! ## `assert_small_g_power`, placed -/

/-- The shares `assert_small_g_power` reads, from the exponent table. -/
theorem asg_shares {rd : Reader} {q : E} (ht : ExpTables rd q) (e : ℕ) :
    ∀ j < 9, LoadHolds rd (q * gen ^ (e / 16 ^ j % 16)) (34 + 16 * j)
      (gen ^ (e / 16 ^ j % 16 * 16 ^ j)) := fun j hj ↦ by
  rw [loadHolds_mul_gen_pow]
  have := ht.2.1 j hj (e / 16 ^ j % 16) (Nat.mod_lt _ (by decide))
  rwa [show sizeBits + 16 * j + e / 16 ^ j % 16 = e / 16 ^ j % 16 + (34 + 16 * j) by
    simp only [sizeBits]; omega] at this

/-- A digit's range check against `g^15` on a memory defined below `2^κ`, `4 ≤ κ`. -/
theorem asg_rc_low {κ : ℕ} (hκ4 : 4 ≤ κ) {rd : Reader} (hlow : LowDef κ rd) {n : ℕ}
    (hn : n < 16) : ∃ y t1 t2 : E, LoadHolds rd (gen ^ n) 0 t1 ∧
      word (2 ^ (16 - 1)) 0 = gen ^ n * y ∧ LoadHolds rd y 0 t2 := by
  obtain ⟨a, b, c⟩ := rc_complete_low hlow (K := 16)
    (le_trans (by decide) (Nat.pow_le_pow_right (by decide) hκ4)) hn
  refine ⟨_, _, _, by rw [gen_pow_eq_ofK]; exact a, ?_, c⟩
  rw [word_two_pow (by norm_num), gen_pow_eq_ofK, gen_pow_eq_ofK]
  exact b

/-- `assert_small_g_power`'s statements before its `ret`. -/
def asgPre : List Stmt :=
  asgHead ++ ((List.range 8).map asgBlk).flatten ++ [.atom (.assertEq (.n 72) (.n 0))]

theorem asgBody_split : asgBody = asgPre ++ [.ret []] := by
  simp only [asgBody, asgPre, List.append_assoc, List.singleton_append]

theorem asgPre_straight : asgPre.all Main.Stmt.straight = true := by decide +kernel

theorem asgPre_loads : asgPre.filterMap Stmt.loadS =
    (List.range 9).map fun j ↦ (.n (asgPtr j), 34 + 16 * j) := by decide +kernel

theorem asg_not_loop : coreProgram.loop "assert_small_g_power" = false := by
  rw [Program.loop_of_find? find_assert_small_g_power]; decide +kernel

/-- **`assert_small_g_power`, placed and bounded**: on `g^e`, `e < 2^36`, and the exponent table, a
leaf within its frame. -/
theorem asg_completeAtB (κ : ℕ) (hκ4 : 4 ≤ κ) (sqE e : ℕ) (he : e < 2 ^ 36) :
    CompleteAtB fs cert κ "assert_small_g_power" (log2Lin sqE)
      [gen ^ e, ofK (Parameters.addressOfIndex sqE)] (Returns []) (fs "assert_small_g_power") := by
  have h := completeAt_leafB (fs := fs) (cert := cert) find_assert_small_g_power asg_not_loop κ
    (log2Lin sqE) [gen ^ e, ofK (Parameters.addressOfIndex sqE)] [] [] (fun _ ↦ [])
    (fun _ ↦ List.Forall₂.nil) ?_
  · simpa using h
  intro fp rd hlow _ hLin
  have ht := expTables_of_memL hLin
  obtain ⟨σ, e0, e1, ep, hh⟩ := asg_holds_of (C := fun _ _ _ ↦ True) (rd := rd)
    (by simpa using he) (fun _ ↦ asg_rc_low hκ4 hlow (Nat.mod_lt _ (by decide))) (asg_shares ht e)
  have hh' : Stmt.HoldsList (fun _ _ _ ↦ True) rd σ (Fn.body fn% «assert_small_g_power») False
      (fun rs ↦ rs = []) := by rw [assert_small_g_power_body]; exact hh
  have hsat := walk_sat (P := coreProgram) _
    (coreProgram_wf _ (List.mem_of_find?_eq_some find_assert_small_g_power)) hh'
  have hw : walk σ (Fn.body fn% «assert_small_g_power») = .ret (asgPre.flatMap (Main.slEvs σ)) []
      := by
    rw [assert_small_g_power_body, asgBody_split, Main.walk_straight σ _ _ asgPre_straight]
  rw [hw] at hsat
  obtain ⟨i1, i2, i3, i4⟩ := Main.straight_parts σ asgPre asgPre_straight
  have ha : asgPre.filterMap Main.Stmt.allocSz = [] := by decide +kernel
  have hd : asgPre.filterMap Main.Stmt.addrS = [] := by decide +kernel
  have hc : asgPre.filterMap Main.Stmt.callS = [] := by decide +kernel
  rw [ha] at i1 i2
  rw [hd] at i3
  rw [hc] at i4
  refine ⟨σ, asgPre.flatMap (Main.slEvs σ), [], by
      rw [show Fn.params fn% «assert_small_g_power» = [.n 0, .n 1] from rfl]; simp [e0, e1], hw,
          rfl,
    fun e he ↦ (hsat.1 e he).1, i4, i3, i2, by rw [i1]; rfl, fun A hA ↦ ?_⟩
  rw [loadAddrs_straight σ _ asgPre_straight, asgPre_loads] at hA
  simp only [List.map_map, List.mem_map, List.mem_range, Function.comp_apply] at hA
  obtain ⟨j, hj, rfl⟩ := hA
  refine ⟨sqE + e / 16 ^ j % 16 + (34 + 16 * j), by rw [ep j hj, limb_ofK_gpow_gen_off], Or.inr ?_⟩
  have : e / 16 ^ j % 16 < 16 := Nat.mod_lt _ (by decide)
  exact regionL_log2Lin (by omega) (by omega)

/-! ## `log2_ceil_in_the_exponent`'s walk -/

/-- The statements before the check above the floor. -/
def lcHead (fl : ℕ) : List Stmt := (lcBody fl).take 16

theorem lcBody_split (fl : ℕ) : lcBody fl =
    lcHead fl ++ (.ite (.n 19) [] lcMin :: [.atom (.copy (.n 27) (.n 4)), .ret [.n 27]]) := rfl

theorem lcHead_straight (fl : ℕ) : (lcHead fl).all Main.Stmt.straight = true := rfl

theorem lcMin_straight : lcMin.all Main.Stmt.straight = true := rfl

/-- A straight block, then the rest: its events, then the rest's walk. -/
theorem walk_straight_pre (σ : Val) : ∀ (pre rest : List Stmt), pre.all Main.Stmt.straight = true →
    walk σ (pre ++ rest) = (walk σ rest).pre (pre.flatMap (Main.slEvs σ))
  | [], rest, _ => by rw [List.nil_append]; cases walk σ rest <;> rfl
  | s :: pre, rest, h => by
    simp only [List.all_cons, Bool.and_eq_true] at h
    rw [List.cons_append, walk, walk_straight_pre σ pre rest h.2, Main.walk1_straight σ s h.1,
      List.flatMap_cons]
    cases walk σ rest <;> simp [Out.seq, Out.pre]

/-- The events of `log2_ceil_in_the_exponent` at the floor `fl`. -/
noncomputable def lcEvs (fl : ℕ) (σ : Val) : List Ev :=
  (lcHead fl).flatMap (Main.slEvs σ) ++ (.inK (.n 19) ::
    ((if σ (.n 19) = 0 then [] else lcMin).flatMap (Main.slEvs σ) ++
      [.atom (.copy (.n 27) (.n 4))]))

theorem lc_walk (fl : ℕ) (σ : Val) : walk σ (lcBody fl) = .ret (lcEvs fl σ) [.n 27] := by
  rw [lcBody_split, walk_straight_pre σ _ _ (lcHead_straight fl), walk, walk1,
    show [Stmt.atom (.copy (.n 27) (.n 4)), .ret [.n 27]] = [Stmt.atom (.copy (.n 27) (.n 4))] ++
      [.ret [.n 27]] from rfl, Main.walk_straight σ _ _ rfl]
  by_cases h : σ (.n 19) = 0
  · simp [h, lcEvs, walk, Out.seq, Out.pre, Main.slEvs]
  · simp [h, lcEvs, Out.seq, Out.pre, walk_straight_fall σ lcMin lcMin_straight, Main.slEvs]

/-- The asserted call on `g^(2^L) / g_N`. -/
def lcCall1 : Call := ⟨"assert_small_g_power", [.n 17, .n 1], [], true⟩

/-- The asserted call above the floor. -/
def lcCall2 : Call := ⟨"assert_small_g_power", [.n 26, .n 1], [], true⟩

theorem lcEvs_parts (fl : ℕ) (σ : Val) :
    allocDsts (lcEvs fl σ) = [.n 3] ∧ allocs σ (lcEvs fl σ) = [logG (σ (.n 2))] ∧
      addrs (lcEvs fl σ) = [] ∧
      calls (lcEvs fl σ) = lcCall1 :: (if σ (.n 19) = 0 then [] else [lcCall2]) ∧
      loadAddrs σ (lcEvs fl σ) = (σ (.n 15)).limb 0 * addressOfIndex 0 ::
        (if σ (.n 19) = 0 then [] else [(σ (.n 24)).limb 0 * addressOfIndex 0]) := by
  obtain ⟨a1, a2, a3, a4⟩ := Main.straight_parts σ _ (lcHead_straight fl)
  obtain ⟨b1, b2, b3, b4⟩ := Main.straight_parts σ _ lcMin_straight
  have la := loadAddrs_straight σ _ (lcHead_straight fl)
  have lb := loadAddrs_straight σ _ lcMin_straight
  have h1 : (lcHead fl).filterMap Main.Stmt.allocSz = [(.n 3, .inr (.n 2))] := rfl
  have h2 : (lcHead fl).filterMap Main.Stmt.addrS = [] := rfl
  have h3 : (lcHead fl).filterMap Main.Stmt.callS =
      [(none, "assert_small_g_power", [.n 17, .n 1], [])] := rfl
  have h4 : (lcHead fl).filterMap Stmt.loadS = [(.n 15, 0)] := rfl
  have m1 : lcMin.filterMap Main.Stmt.allocSz = [] := rfl
  have m2 : lcMin.filterMap Main.Stmt.addrS = [] := rfl
  have m3 : lcMin.filterMap Main.Stmt.callS =
      [(none, "assert_small_g_power", [.n 26, .n 1], [])] := rfl
  have m4 : lcMin.filterMap Stmt.loadS = [(.n 24, 0)] := rfl
  rw [h1] at a1 a2
  rw [h2] at a3
  rw [h3] at a4
  rw [h4] at la
  rw [m1] at b1 b2
  rw [m2] at b3
  rw [m3] at b4
  rw [m4] at lb
  unfold lcEvs
  by_cases h : σ (.n 19) = 0
  · simp only [h, ↓reduceIte, List.flatMap_nil, List.nil_append, allocDsts_app, allocs_app,
      addrs_app, calls_app, loadAddrs_app, a1, a2, a3, a4, la]
    refine ⟨rfl, rfl, rfl, rfl, rfl⟩
  · simp only [h, ↓reduceIte, allocDsts_app, allocs_app, addrs_app, calls_app, loadAddrs_app,
      allocDsts_inK, allocs_inK, addrs_inK, calls_inK, loadAddrs_inK, a1, a2, a3, a4, la, b1, b2,
      b3, b4, lb]
    refine ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- `log2_ceil_in_the_exponent`'s body under any call relation, valuation and continuation. -/
theorem lc_holds_iff (fl : ℕ) (C : CallRel) (rd : Reader) (σ : Val) (kret : List E → Prop) :
    Stmt.HoldsList C rd σ (lcBody fl) False kret ↔
      σ (.n 2) = word (2 ^ 34) 0 ∧ σ (.n 5) = word (2 ^ 33) 0 ∧
      (LoadHolds rd (σ (.n 4)) 0 (σ (.n 7)) ∧ σ (.n 5) = σ (.n 4) * σ (.n 6) ∧
        LoadHolds rd (σ (.n 6)) 0 (σ (.n 8))) ∧
      σ (.n 9) = word (2 ^ 33) 0 ∧ σ (.n 10) = word (2 ^ fl) 0 ∧
      σ (.n 4) = σ (.n 11) * σ (.n 10) ∧
      (LoadHolds rd (σ (.n 11)) 0 (σ (.n 13)) ∧ σ (.n 9) = σ (.n 11) * σ (.n 12) ∧
        LoadHolds rd (σ (.n 12)) 0 (σ (.n 14))) ∧
      σ (.n 15) = σ (.n 1) * σ (.n 4) ∧ LoadHolds rd (σ (.n 15)) 0 (σ (.n 16)) ∧
      σ (.n 16) = σ (.n 17) * σ (.n 0) ∧
      C "assert_small_g_power" [σ (.n 17), σ (.n 1)] [] ∧
      σ (.n 18) = word (2 ^ fl) 0 ∧ σ (.n 19) = σ (.n 4) + σ (.n 18) ∧
      (IsInK (σ (.n 19)) ∧ (σ (.n 19) ≠ 0 →
        σ (.n 20) = invGenWord ∧ σ (.n 21) = σ (.n 0) * σ (.n 20) ∧ σ (.n 22) = invGenWord ∧
        σ (.n 23) = σ (.n 4) * σ (.n 22) ∧ σ (.n 24) = σ (.n 1) * σ (.n 23) ∧
        LoadHolds rd (σ (.n 24)) 0 (σ (.n 25)) ∧ σ (.n 21) = σ (.n 26) * σ (.n 25) ∧
        C "assert_small_g_power" [σ (.n 26), σ (.n 1)] [])) ∧
      σ (.n 27) = σ (.n 4) ∧ kret [σ (.n 27)] := by
  rw [lcBody]
  simp only [Stmt.HoldsList]
  simp only [holds_ite_noRet (.n 19) [] lcMin rfl rfl]
  simp only [lcMin, Stmt.HoldsList, Stmt.Holds, Atom.Holds, List.map_cons, List.map_nil, true_and,
    and_true, implies_true]

/-! ## `log2_ceil_in_the_exponent`, placed -/

/-- `assert_small_g_power`'s call on `g^e` and the table at `sqE`. -/
def asgKid (sqE e : ℕ) : Kid :=
  ⟨"assert_small_g_power", true, [gen ^ e, ofK (Parameters.addressOfIndex sqE)], log2Lin sqE,
    Returns []⟩

/-- **`log2_ceil_in_the_exponent` at the floor `fl`, placed**: on `g^N`, `N < 2^34`, and the
exponent table it returns `g^L`, `L = max fl (log2Ceil N) < 34`, the hinted bits of `N` in its one
buffer, within its frame, `34` words and two frames of `assert_small_g_power`. -/
theorem lce_completeAtB (fl : ℕ) (hfl : fl < 34) {name : String} {fn : Fn}
    (hf : coreProgram.find? name = some fn) (hp : fn.params = [.n 0, .n 1])
    (hb : fn.body = lcBody fl) (hl : coreProgram.loop name = false) (κ : ℕ) (hκ6 : 6 ≤ κ)
    (N sqE : ℕ) (hN : N < 2 ^ 34) (hL : max fl (log2Ceil N) < 34) :
    CompleteAtB fs cert κ name (log2Lin sqE) [gen ^ N, ofK (Parameters.addressOfIndex sqE)]
      (Returns [gen ^ max fl (log2Ceil N)])
      (fs name + 34 + 2 * fs "assert_small_g_power") := by
  intro fp
  set L := max fl (log2Ceil N) with hLdef
  set b := fp + fs name with hbdef
  set q : E := ofK (Parameters.addressOfIndex sqE) with hq
  have hle : N ≤ 2 ^ L := log2Ceil_le_iff.mp (le_max_right _ _)
  have hflL : fl ≤ L := le_max_left _ _
  have h2L : 2 ^ L < 2 ^ 34 := Nat.pow_lt_pow_right (by decide) hL
  -- above the floor, `2^(L-1) < N`
  have hlow : L ≠ fl → 2 ^ (L - 1) < N := fun hne ↦ by
    have : L = log2Ceil N := by
      rcases max_choice fl (log2Ceil N) with h | h
      · exact absurd (hLdef.trans h) hne
      · exact hLdef.trans h
    exact lt_log2Ceil_iff.mp (by omega)
  have hL1 : L ≠ fl → 2 ^ (L - 1) < 2 ^ 34 := fun _ ↦ Nat.pow_lt_pow_right (by decide) (by omega)
  clear_value L
  let extra : List Kid := if L = fl then [] else [asgKid sqE (N - (2 ^ (L - 1) + 1))]
  let kids : List Kid := asgKid sqE (2 ^ L - N) :: extra
  have hown34 : List.Forall₂ (fun c s ↦ c.length ≤ s) [bitWords N] [34] :=
    List.Forall₂.cons (by simp [bitWords]) List.Forall₂.nil
  have hκ4 : 4 ≤ κ := by omega
  obtain ⟨Nk, Lk, outs, ho, hW, hD, hNb, -, hK⟩ := kidsFromIn_of_kidsB (fs := fs) (cert := cert) κ
    (fun _ ↦ fs "assert_small_g_power") kids (fun k hk _ ↦ by
      simp only [kids, extra, List.mem_cons] at hk
      rcases hk with rfl | hk
      · exact asg_completeAtB κ hκ4 sqE (2 ^ L - N) (by omega)
      · split at hk
        · exact absurd hk List.not_mem_nil
        · rename_i hne
          rw [List.mem_singleton] at hk
          subst hk
          exact asg_completeAtB κ hκ4 sqE (N - (2 ^ (L - 1) + 1))
            (lt_of_le_of_lt (Nat.sub_le _ _) (lt_trans hN (by norm_num)))) (b + 34)
  have hNb' : Nk ≤ 2 * fs "assert_small_g_power" := by
    refine hNb.trans ?_
    simp only [kidsBound, kids, extra, asgKid]
    split <;> simp <;> omega
  have hwb : Within (bufL b [34] [bitWords N]) b 34 := by
    simpa using bufL_within b [34] [bitWords N] hown34
  refine ⟨fs name + 34 + Nk, bufL b [34] [bitWords N] ++ Lk, [gen ^ L], [], ⟨rfl, rfl⟩, ?_, ?_,
    by omega, fun rd hlowd hL' ↦ ?_⟩
  · simp only [List.nil_append, within_append]
    exact ⟨hwb.mono (by omega) (by omega), hW.mono (by omega) (by omega)⟩
  · simpa using disj_append (bufL_disj b [34] [bitWords N] hown34) hD hwb hW le_rfl
  simp only [List.nil_append] at hL'
  obtain ⟨hLm, hLin⟩ := Main.memL_append.mp hL'
  obtain ⟨hB, hLk⟩ := Main.memL_append.mp hLm
  have ht := expTables_of_memL hLin
  have hK34 : 34 ≤ 2 ^ κ := le_trans (by decide) (Nat.pow_le_pow_right (by decide) hκ6)
  obtain ⟨r1a, r1b, r1c⟩ := rc_complete_low hlowd (K := 34) hK34 hL
  obtain ⟨r2a, r2b, r2c⟩ := rc_complete_low hlowd (K := 34) hK34 (show L - fl < 34 by omega)
  have w33 : word (2 ^ 33) 0 = ofK (addressOfIndex (34 - 1)) := by
    rw [word_two_pow (by norm_num), gen_pow_eq_ofK]
  have wfl : word (2 ^ fl) 0 = gen ^ fl := word_two_pow (by omega)
  -- the valuation
  let w : List E := [gen ^ N, q, word (2 ^ 34) 0, ofK (Parameters.addressOfIndex b), gen ^ L,
    word (2 ^ 33) 0, (rcLow rd L 34).1, (rcLow rd L 34).2.1, (rcLow rd L 34).2.2,
    word (2 ^ 33) 0, word (2 ^ fl) 0, gen ^ (L - fl), (rcLow rd (L - fl) 34).1,
    (rcLow rd (L - fl) 34).2.1, (rcLow rd (L - fl) 34).2.2, q * gen ^ L, gen ^ 2 ^ L,
    gen ^ (2 ^ L - N), word (2 ^ fl) 0, gen ^ L + word (2 ^ fl) 0, invGenWord,
    gen ^ N * invGenWord, invGenWord, gen ^ L * invGenWord, q * (gen ^ L * invGenWord),
    gen ^ 2 ^ (L - 1), gen ^ (N - (2 ^ (L - 1) + 1)), gen ^ L]
  let σ : Val := Val.ofArgs w
  have h19 : σ (.n 19) = 0 ↔ L = fl := by
    show gen ^ L + word (2 ^ fl) 0 = 0 ↔ _
    rw [wfl, e_add_eq_zero_iff]
    exact ⟨fun h ↦ gen_pow_inj (by omega) (by omega) h, fun h ↦ by rw [h]⟩
  have hh : Stmt.HoldsList (fun _ _ _ ↦ True) rd σ (lcBody fl) False (fun r ↦ r = [gen ^ L]) := by
    refine (lc_holds_iff fl _ rd σ _).2 ⟨rfl, rfl, ⟨?_, ?_, r1c⟩, rfl, rfl, ?_, ⟨?_, ?_, r2c⟩, rfl,
      ?_, ?_, trivial, rfl, rfl, ⟨?_, fun hne ↦ ?_⟩, rfl, rfl⟩
    · show LoadHolds rd (gen ^ L) 0 _
      rw [gen_pow_eq_ofK]; exact r1a
    · show word (2 ^ 33) 0 = gen ^ L * _
      rw [w33, gen_pow_eq_ofK]; exact r1b
    · show gen ^ L = gen ^ (L - fl) * word (2 ^ fl) 0
      rw [wfl, ← pow_add]; congr 1; omega
    · show LoadHolds rd (gen ^ (L - fl)) 0 _
      rw [gen_pow_eq_ofK]; exact r2a
    · show word (2 ^ 33) 0 = gen ^ (L - fl) * _
      rw [w33, gen_pow_eq_ofK]; exact r2b
    · show LoadHolds rd (q * gen ^ L) 0 (gen ^ 2 ^ L)
      rw [loadHolds_mul_gen_pow, Nat.add_zero]; exact ht.1 L hL
    · show gen ^ 2 ^ L = gen ^ (2 ^ L - N) * gen ^ N
      rw [← pow_add]; congr 1; omega
    · show IsInK (gen ^ L + word (2 ^ fl) 0)
      rw [wfl]; exact isInK_add (gen_pow_isInK _) (gen_pow_isInK _)
    · have hLf : L ≠ fl := fun h ↦ hne (h19.2 h)
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
  have hh' : Stmt.HoldsList (fun _ _ _ ↦ True) rd σ fn.body False (fun r ↦ r = [gen ^ L]) := by
    rw [hb]; exact hh
  have hsat := walk_sat (P := coreProgram) fn.body
    (coreProgram_wf fn (List.mem_of_find?_eq_some hf)) hh'
  have hw : walk σ fn.body = .ret (lcEvs fl σ) [.n 27] := by rw [hb, lc_walk]
  rw [hw] at hsat
  obtain ⟨p1, p2, p3, p4, p5⟩ := lcEvs_parts fl σ
  set es := lcEvs fl σ with hes
  have hal : allocs σ es = [34] := by
    rw [p2]
    show [logG (word (2 ^ 34) 0)] = [34]
    rw [word_two_pow (by norm_num), logG_gen_pow (by norm_num)]
  have hown' : ∀ i, RegionL (bufL b [34] [bitWords N]) i →
      ownData cert fp (fp + fs name) name (allocs σ es) es i :=
    fun i hi ↦ Or.inl (by rw [hal]; exact bufL_region _ _ _ hown34 i hi)
  have hcm : CallsMatch σ (calls es) kids outs := by
    rw [p4]
    by_cases hLf : L = fl
    · have e19 : σ (.n 19) = 0 := h19.2 hLf
      have hex : extra = [] := ite_pos' hLf
      simp only [e19, ↓reduceIte, kids, hex] at ho ⊢
      obtain ⟨o, rfl⟩ : ∃ o, outs = [o] := by
        match outs, ho with
        | [o], _ => exact ⟨o, rfl⟩
      obtain ⟨ho1, -⟩ := ho
      refine ⟨rfl, rfl, fun _ ↦ ⟨rfl, (ho1 rfl).1.symm⟩, trivial⟩
    · have e19 : σ (.n 19) ≠ 0 := fun h ↦ hLf (h19.1 h)
      have hex : extra = [asgKid sqE (N - (2 ^ (L - 1) + 1))] := ite_neg' hLf
      simp only [e19, ↓reduceIte, kids, hex] at ho ⊢
      obtain ⟨o1, o2, rfl⟩ : ∃ o1 o2, outs = [o1, o2] := by
        match outs, ho with
        | [o1, o2], _ => exact ⟨o1, o2, rfl⟩
      obtain ⟨ho1, ho2, -⟩ := ho
      exact ⟨rfl, rfl, fun _ ↦ ⟨rfl, (ho1 rfl).1.symm⟩, rfl, rfl,
        fun _ ↦ ⟨rfl, (ho2 rfl).1.symm⟩, trivial⟩
  have hk := hK rd σ (calls es) (fun i ↦ RegionL (log2Lin sqE) i ∨
      ownData cert fp (fp + fs name) name (allocs σ es) es i) (fun _ ↦ False) hcm hlowd hLk
    (memL_lins fun k hk ↦ by
      simp only [kids, extra, List.mem_cons] at hk
      rcases hk with rfl | hk
      · exact hLin
      · split at hk
        · exact absurd hk List.not_mem_nil
        · rw [List.mem_singleton] at hk; subst hk; exact hLin)
    (regionsOk_of fun k hk _ i hi ↦ by
      have : k.Lin = log2Lin sqE := by
        simp only [kids, extra, List.mem_cons] at hk
        rcases hk with rfl | hk
        · rfl
        · split at hk
          · exact absurd hk List.not_mem_nil
          · rw [List.mem_singleton] at hk; subst hk; rfl
      rw [this] at hi
      exact Or.inl (Or.inl hi))
  have hb' : b + 34 = fp + fs name + (allocs σ es).sum := by rw [hal]; simp [hbdef]
  rw [hb'] at hk
  have h := relAtIn_of_walk (P := coreProgram) (fs := fs) (cert := cert)
    (R := RegionL (log2Lin sqE)) (D := RegionL []) (Dk := fun i ↦ False ∨ outRegion kids outs i)
    (N := Nk) (fp := fp) (args := [gen ^ N, q]) (rets := [gen ^ L])
    coreProgram_wf hf (Or.inl hl) (by rw [hp]; rfl) hw rfl (fun e he ↦ (hsat.1 e he).1)
    (by rw [hal, p1]; simp [bases]; rfl) (by rw [p3]; simp) hk
    (fun A hA ↦ by
      rw [p5] at hA
      simp only [List.mem_cons] at hA
      rcases hA with rfl | hA
      · exact ⟨sqE + L + 0, by
          show (q * gen ^ L).limb 0 * addressOfIndex 0 = _
          rw [hq, limb_ofK_gpow_gen_off], Or.inr (Or.inl (regionL_log2Lin (by omega) (by omega)))⟩
      · split at hA
        · exact absurd hA List.not_mem_nil
        · rename_i hne
          have hLf : L ≠ fl := fun h ↦ hne (h19.2 h)
          obtain ⟨L', hL'⟩ : ∃ L', L = L' + 1 := ⟨L - 1, by omega⟩
          rw [List.mem_singleton] at hA
          subst hA
          refine ⟨sqE + L' + 0, ?_, Or.inr (Or.inl (regionL_log2Lin (by omega) (by omega)))⟩
          show (q * (gen ^ L * invGenWord)).limb 0 * addressOfIndex 0 = _
          rw [hL', gen_pow_mul_invGen, hq, limb_ofK_gpow_gen_off])
    (fun i hi ↦ by obtain ⟨q, hq, _⟩ := hi; simp at hq)
  rw [hal] at h
  simpa using h

end
end LeanVM.Guest.B1
