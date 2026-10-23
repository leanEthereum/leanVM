/-
  LeanVM.Guest.B1.Digest.ClaimListAt

  `claim_list_digest` complete in the uniform placed form (`CompleteRel`): its windows' scratch
  table as its own words, the claims and the squares table within the caller's words.
-/

module

public import LeanVM.Guest.Memory.Size
public import LeanVM.Guest.B1.Digest.ClaimList
public import LeanVM.Guest.B1.Digest.Forced
public import LeanVM.Guest.B1.Da.RelIn
public import LeanVM.Guest.Memory.LoopPre

/-!
# `claim_list_digest`, uniformly placed

`claim_list_digest(ptr, g^n, g_squares)`, `n ≥ 1`, allocates its windows' scratch table (`4(w+1)`
words, `w = (n-1)/32`) from `fp + fs "claim_list_digest"`, then calls `__loop86` (the `w` full
windows, when `w > 0`), the tail `claims_tail__L{t}`, `t = (n-1) % 32`, and `scaled_log__L6`, all
of them pure. The claims' cells are words of the caller's layout: a memory holding another word
there, a non-canonical one, would fail the precondition (`forced_load_pred`); so are the squares
table's (`forced_load`). The callees are complete on the layout of the scratch table, the claims and
the squares (`completeAt_of_rel_pure`), composed by `kidsFromIn_of_kids`.
-/

namespace LeanVM.Guest.B1.Digest

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.Blake2sHash
open LeanVM.Guest.Core LeanVM.Guest.Memory LeanVM.Guest.Value
open LeanVM.Protocol.Verifier (gen eOfNat)
open LeanVM.Guest.B1 (LowDef CompleteAt CompleteAtD CompleteAtB kidsBound CompleteRel CompleteRelD DisjL disj_nil disj_append Within Returns Kid)
open LeanVM.Guest.B1.Main (Layout MemL RegionL)

@[expose] public section

/-! ## The path -/

/-- The branch of an empty list. -/
def cldZ : List Stmt := match cldBody with | _ :: _ :: .ite _ z _ :: _ => z | _ => []

/-- The branch of a non-empty list. -/
def cldE : List Stmt := match cldBody with | _ :: _ :: .ite _ _ e :: _ => e | _ => []

def cldPre : List Stmt := cldE.take 37
def cldPost : List Stmt := cldE.drop 38

theorem cldBody_split : cldBody = [.atom (.const (.n 3) (word 1 0 0)), .atom (.add (.n 4) (.n 1) (.n 3)),
    .ite (.n 4) cldZ (cldPre ++ .dispatch (.n 15) ctNames [.n 46, .n 47, .n 48, .n 49] [.n 50, .n 51, .n 52] ::
      cldPost), .atom (.copy (.n 60) (.n 12)), .atom (.copy (.n 61) (.n 13)), .ret [.n 60, .n 61]] := rfl

theorem cldZ_straight : cldZ.all Main.Stmt.straight = true := by decide +kernel
theorem cldPre_straight : cldPre.all Main.Stmt.straight = true := by decide +kernel
theorem cldPost_straight : cldPost.all Main.Stmt.straight = true := by decide +kernel

/-- The head of the path. -/
def cldHead : List Ev := [.atom (.const (.n 3) (word 1 0 0)), .atom (.add (.n 4) (.n 1) (.n 3)), .inK (.n 4)]

/-- The copies of the digest. -/
def cldTail : List Ev := [.atom (.copy (.n 60) (.n 12)), .atom (.copy (.n 61) (.n 13))]

theorem walk_cld_zero (σ : Val) (h4 : σ (.n 4) = 0) :
    walk σ cldBody = .ret (cldHead ++ cldZ.flatMap (Main.slEvs σ) ++ cldTail) [.n 60, .n 61] := by
  rw [cldBody_split]
  simp only [walk, walk1, h4, ↓reduceIte, walk_straight_fall σ cldZ cldZ_straight, Out.seq, Out.pre]
  simp [cldHead, cldTail]

/-- The path of a non-empty list, its tail `ctNames[t]!`. -/
noncomputable def cldEs (σ : Val) (t : ℕ) : List Ev :=
  cldHead ++ (cldPre.flatMap (Main.slEvs σ) ++
    .call ctNames[t]! [.n 46, .n 47, .n 48, .n 49] [.n 50, .n 51, .n 52] :: cldPost.flatMap (Main.slEvs σ)) ++ cldTail

theorem walk_cld_pos (σ : Val) (h4 : σ (.n 4) ≠ 0) {t : ℕ} (ht : t < 32) (h15 : σ (.n 15) = ofK (gpow t)) :
    walk σ cldBody = .ret (cldEs σ t) [.n 60, .n 61] := by
  rw [cldBody_split, cldEs]
  simp only [walk, walk1, h4, ↓reduceIte, walk_dispatch_fall σ cldPre cldPost cldPre_straight cldPost_straight
    (.n 15) ctNames _ _ (i := t) (by simp [ctNames]; omega) (by simp [ctNames]) h15, Out.seq, Out.pre]
  simp [cldHead, cldTail]

/-- The honest values of `claim_list_digest`, `n = 0`. -/
def cldZeroList (p gsq d0 d1 : E) : List E :=
  [p, 1, gsq, word 1 0 0, 1 + word 1 0 0, word 0 0 0, word 0 0 0, word 0 0 0,
    word 0 0 0, word 13503953895743350343 11912009169889063794 0,
    word 11170449402626986623 6620516960021240235 0, word 0 4294967295 0, d0, d1] ++
    List.replicate 46 0 ++ [d0, d1]

theorem cld_holds_zero (rd : Reader) (p gsq : E) {d0 d1 : E}
    (hd : (d0, d1) = digestScalars (blake2sBytes (([] : List E).flatMap cellBytes))) :
    Stmt.HoldsList (coreProgram.Rel rd) rd (listVal (cldZeroList p gsq d0 d1)) cldBody False
      (fun rs => rs = [d0, d1]) := by
  simp only [cldBody, List.cons_append, List.nil_append, Stmt.HoldsList,
    Stmt.Holds, Atom.Holds, true_and, List.map_cons, List.map_nil]
  have h11 : (1 : E) + word 1 0 0 = 0 := by rw [word_one, e_add_self]
  refine ⟨rfl, rfl, ?_, fun _ => ?_, fun h => ?_⟩
  · show IsInK ((1 : E) + word 1 0 0)
    rw [h11, ← ofK_zero]; exact ofK_isInK _
  · refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, ?_, rfl, rfl, rfl⟩
    show CompressCells ![word 0 0 0, word 0 0 0, word 0 0 0, word 0 0 0]
      (word 13503953895743350343 11912009169889063794 0)
      (word 11170449402626986623 6620516960021240235 0) d0 d1 (word 0 4294967295 0)
    rw [word_zero, iv0_word, iv1_word, md_final_word]
    exact compressCells_empty_iff.mpr hd
  · exfalso; apply h; show (1 : E) + word 1 0 0 = 0; exact h11

/-! ## The callees, pure -/

/-- `claim_list_digest`'s callees and theirs. -/
def cldKidSet : List String := ["__loop86", "claims_window", "scaled_log__L11", "scaled_log__L6"] ++ ctNames

theorem ctNames_getElem! {t : ℕ} (ht : t < 32) : ctNames[t]! = ctNames.getD t "" := by
  interval_cases t <;> rfl

theorem ctNames_mem {g : String} (hg : g ∈ ctNames) : ∃ t < 32, g = ctNames.getD t "" := by
  obtain ⟨t, ht, rfl⟩ := List.getElem_of_mem hg
  exact ⟨t, by simpa [ctNames] using ht, by rw [List.getD_eq_getElem]⟩

set_option maxRecDepth 100000 in
theorem cldKid_pure : coreProgram.PureIn cldKidSet := by
  intro g hg fn hf
  simp only [cldKidSet, List.cons_append, List.mem_cons, List.nil_append] at hg
  rcases hg with rfl | rfl | rfl | rfl | hg
  · rw [find_loop86, Option.some.injEq] at hf; subst hf; decide +kernel
  · rw [find_claims_window, Option.some.injEq] at hf; subst hf; decide +kernel
  · rw [find_scaled_log_11, Option.some.injEq] at hf; subst hf; decide +kernel
  · rw [find_scaled_log_6, Option.some.injEq] at hf; subst hf; decide +kernel
  · obtain ⟨t, ht, rfl⟩ := ctNames_mem hg
    rw [find_claims_tail t ht, Option.some.injEq] at hf
    subst hf
    interval_cases t <;> decide +kernel

/-! ## Layouts -/

/-- The windows' scratch slot `q`. -/
def clSlot (p : E) (cs : List E) (q : ℕ) : List E :=
  [(digestScalars (prefixDigest cs (32 * q))).1, (digestScalars (prefixDigest cs (32 * q))).2,
    eOfNat (2 ^ 11 * q), p * gen ^ (128 * q)]

/-- The windows' scratch table at `g^cx`. -/
def clScratchL (p : E) (cs : List E) (cx w : ℕ) : Layout :=
  (List.range (w + 1)).map fun q => (cx + 4 * q, clSlot p cs q)

theorem clScratch_of_memL {rd : Reader} {L : Layout} (h : MemL rd L) {p : E} {cs : List E} {cx w : ℕ}
    (hs : ∀ q ∈ clScratchL p cs cx w, q ∈ L) : ClScratch rd p (gen ^ cx) cs w := fun q hq => by
  rw [← pow_add]
  exact cells_of_memL h (hs _ (List.mem_map.mpr ⟨q, List.mem_range.mpr (by omega), rfl⟩))

theorem clScratch_region {p : E} {cs : List E} {cx w i : ℕ} (h : RegionL (clScratchL p cs cx w) i) :
    cx ≤ i ∧ i < cx + 4 * (w + 1) := by
  obtain ⟨q, hq, h1, h2⟩ := h
  obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hq
  simp only [clSlot, List.length_cons, List.length_nil] at h1 h2
  have := List.mem_range.mp hj
  omega

/-- Single words pinned at indices `idx k`. -/
def pinL (vs : ℕ → E) (idx : ℕ → ℕ) (m : ℕ) : Layout := (List.range m).map fun k => (idx k, [vs k])

theorem pin_loads {rd : Reader} {L : Layout} (h : MemL rd L) {p : E} (hp : IsInK p) {vs : ℕ → E}
    {idx : ℕ → ℕ} {m : ℕ} (hidx : ∀ k < m, p.limb 0 * gpow k = gpow (idx k))
    (hs : ∀ q ∈ pinL vs idx m, q ∈ L) : ∀ k < m, LoadHolds rd p k (vs k) := fun k hk =>
  load_of_pin h hp (hidx k hk) (hs _ (List.mem_map.mpr ⟨k, List.mem_range.mpr hk, rfl⟩))

theorem pin_region {vs : ℕ → E} {idx : ℕ → ℕ} {m i : ℕ} (h : RegionL (pinL vs idx m) i) :
    ∃ k < m, i = idx k := by
  obtain ⟨q, hq, h1, h2⟩ := h
  obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hq
  simp only [List.length_cons, List.length_nil] at h1 h2
  exact ⟨k, List.mem_range.mp hk, by omega⟩

/-- Pinned words of the caller's layout are held by every memory holding it. -/
theorem pin_memL {Lin : Layout} {rd rd1 : Reader} (h : MemL rd Lin) (h1 : MemL rd1 Lin) {vs : ℕ → E}
    {idx : ℕ → ℕ} {m : ℕ} (hR : ∀ k < m, RegionL Lin (idx k)) (hv : ∀ k < m, rd1 (gpow (idx k)) = some (vs k)) :
    MemL rd (pinL vs idx m) := by
  intro q hq k hk
  obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hq
  have hj := List.mem_range.mp hj
  simp only [List.length_cons, List.length_nil] at hk
  obtain rfl : k = 0 := by omega
  refine ⟨ofK_isInK _, ?_⟩
  rw [Main.addr_ofK, Nat.add_zero, Main.memL_agree h h1 _ (hR j hj), hv j hj]
  rfl

theorem addr_mul_gen_pow {p : E} (hp : IsInK p) (a k : ℕ) :
    (p * gen ^ a).limb 0 * gpow k = p.limb 0 * gpow (a + k) := by
  rw [gen_pow_eq_ofK, limb0_mul_ofK hp, mul_assoc, gpow_add']

/-! ## `claim_list_digest`, complete uniformly -/

/-- `claim_list_digest`'s precondition: the squares table, `n < 2^16` canonical claims at `ptr`,
their digest returned. -/
def ClPre (rd : Reader) : List E → List E → Prop
  | [ptr, ng, gsq], [d0, d1] => SquaresAt rd gsq ∧ ∃ n < 2 ^ 16, ng = gen ^ n ∧ ∃ cs : List E,
      cs.length = 4 * n ∧ CellsAt rd ptr cs ∧ (∀ c ∈ cs, IsCanonical128 c) ∧
        (d0, d1) = digestScalars (blake2sBytes (cs.flatMap cellBytes))
  | _, _ => False

theorem clPre_shape {rd : Reader} {args rets : List E} (h : ClPre rd args rets) :
    ∃ p ng gsq d0 d1, args = [p, ng, gsq] ∧ rets = [d0, d1] := by
  unfold ClPre at h
  split at h
  · exact ⟨_, _, _, _, _, rfl, rfl⟩
  · exact h.elim

theorem cld_zero_events (σ : Val) :
    allocDsts (cldHead ++ cldZ.flatMap (Main.slEvs σ) ++ cldTail) = [] ∧
    allocs σ (cldHead ++ cldZ.flatMap (Main.slEvs σ) ++ cldTail) = [] ∧
    addrs (cldHead ++ cldZ.flatMap (Main.slEvs σ) ++ cldTail) = [] ∧
    calls (cldHead ++ cldZ.flatMap (Main.slEvs σ) ++ cldTail) = [] ∧
    loadAddrs σ (cldHead ++ cldZ.flatMap (Main.slEvs σ) ++ cldTail) = [] := by
  obtain ⟨h1, h2, h3, h4⟩ := Main.straight_parts σ _ cldZ_straight
  have h5 := loadAddrs_straight σ _ cldZ_straight
  simp only [allocDsts_append, allocs_append, addrs_append, calls_append, loadAddrs_append, h1, h2, h3, h4, h5,
    show cldZ.filterMap Main.Stmt.allocSz = [] by decide +kernel,
    show cldZ.filterMap Main.Stmt.addrS = [] by decide +kernel,
    show cldZ.filterMap Main.Stmt.callS = [] by decide +kernel,
    show cldZ.filterMap stmtLoad? = [] by decide +kernel]
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem cld_pos_events (σ : Val) (t : ℕ) :
    allocDsts (cldEs σ t) = [.n 36] ∧ allocs σ (cldEs σ t) = [logG (σ (.n 35))] ∧ addrs (cldEs σ t) = [] ∧
    calls (cldEs σ t) = [⟨"__loop86", [.n 42, .n 14, .n 36, .n 2], [], decide (σ (.n 41) ≠ 0)⟩,
      ⟨ctNames[t]!, [.n 46, .n 47, .n 48, .n 49], [.n 50, .n 51, .n 52], true⟩,
      ⟨"scaled_log__L6", [.n 1, .n 2], [.n 53], true⟩] ∧
    loadAddrs σ (cldEs σ t) = ([(.n 36, 0), (.n 36, 1), (.n 36, 2), (.n 36, 3), (.n 45, 0), (.n 45, 1),
      (.n 45, 2), (.n 45, 3), (.n 52, 0), (.n 52, 1), (.n 52, 2), (.n 52, 3)] : List (V × ℕ)).map
        fun q => (σ q.1).limb 0 * gpow q.2 := by
  obtain ⟨h1, h2, h3, h4⟩ := Main.straight_parts σ _ cldPre_straight
  obtain ⟨g1, g2, g3, g4⟩ := Main.straight_parts σ _ cldPost_straight
  have h5 := loadAddrs_straight σ _ cldPre_straight
  have g5 := loadAddrs_straight σ _ cldPost_straight
  unfold cldEs
  simp only [allocDsts_append, allocs_append, addrs_append, calls_append, loadAddrs_append]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [show allocDsts (Ev.call ctNames[t]! [.n 46, .n 47, .n 48, .n 49] [.n 50, .n 51, .n 52] ::
      cldPost.flatMap (Main.slEvs σ)) = allocDsts (cldPost.flatMap (Main.slEvs σ)) from rfl, h1, g1,
      show cldPre.filterMap Main.Stmt.allocSz = [(.n 36, .inr (.n 35))] by decide +kernel,
      show cldPost.filterMap Main.Stmt.allocSz = [] by decide +kernel]
    rfl
  · rw [show allocs σ (Ev.call ctNames[t]! [.n 46, .n 47, .n 48, .n 49] [.n 50, .n 51, .n 52] ::
      cldPost.flatMap (Main.slEvs σ)) = allocs σ (cldPost.flatMap (Main.slEvs σ)) from rfl, h2, g2,
      show cldPre.filterMap Main.Stmt.allocSz = [(.n 36, .inr (.n 35))] by decide +kernel,
      show cldPost.filterMap Main.Stmt.allocSz = [] by decide +kernel]
    rfl
  · rw [show addrs (Ev.call ctNames[t]! [.n 46, .n 47, .n 48, .n 49] [.n 50, .n 51, .n 52] ::
      cldPost.flatMap (Main.slEvs σ)) = addrs (cldPost.flatMap (Main.slEvs σ)) from rfl, h3, g3,
      show cldPre.filterMap Main.Stmt.addrS = [] by decide +kernel,
      show cldPost.filterMap Main.Stmt.addrS = [] by decide +kernel]
    rfl
  · rw [show calls (Ev.call ctNames[t]! [.n 46, .n 47, .n 48, .n 49] [.n 50, .n 51, .n 52] ::
      cldPost.flatMap (Main.slEvs σ)) = ⟨ctNames[t]!, [.n 46, .n 47, .n 48, .n 49], [.n 50, .n 51, .n 52], true⟩ ::
        calls (cldPost.flatMap (Main.slEvs σ)) from rfl, h4, g4,
      show cldPre.filterMap Main.Stmt.callS = [(some (.n 41), "__loop86", [.n 42, .n 14, .n 36, .n 2], [])] by
        decide +kernel,
      show cldPost.filterMap Main.Stmt.callS = [(none, "scaled_log__L6", [.n 1, .n 2], [.n 53])] by decide +kernel]
    rfl
  · rw [show loadAddrs σ (Ev.call ctNames[t]! [.n 46, .n 47, .n 48, .n 49] [.n 50, .n 51, .n 52] ::
      cldPost.flatMap (Main.slEvs σ)) = loadAddrs σ (cldPost.flatMap (Main.slEvs σ)) from rfl, h5, g5,
      show cldPre.filterMap stmtLoad? = [(.n 36, 0), (.n 36, 1), (.n 36, 2), (.n 36, 3), (.n 45, 0), (.n 45, 1),
        (.n 45, 2), (.n 45, 3)] by decide +kernel,
      show cldPost.filterMap stmtLoad? = [(.n 52, 0), (.n 52, 1), (.n 52, 2), (.n 52, 3)] by decide +kernel]
    rfl

/-- The bound of `claim_list_digest` on `n` claims: its frame, the scratch table, the loop, the tail
and the scaled log. -/
def cldBound (fs : String → ℕ) (B86 : E → ℕ) (Bct : ℕ → ℕ) (Bsl6 n : ℕ) : ℕ :=
  fs "claim_list_digest" + 4 * ((n - 1) / 32 + 1) +
    (max (B86 (gen ^ ((n - 1) / 32))) (fs "__loop86") + Bct ((n - 1) % 32) + Bsl6)

theorem ct_ne : ∀ t < 32, ctNames[t]! ≠ "__loop86" ∧ ctNames[t]! ≠ "scaled_log__L6" := by decide

/-- **`claim_list_digest` is complete, uniformly placed**, on a memory defined below `2^κ`,
`κ ≥ 16`. -/
theorem cld_completeRel (fs : String → ℕ) (cert : String → V → ℕ) {κ : ℕ} (hκ : 16 ≤ κ) :
    CompleteRel fs cert κ "claim_list_digest" ClPre := by
  intro args rets Lin hpre fp
  classical
  by_cases hex : ∃ rd1, LowDef κ rd1 ∧ MemL rd1 Lin
  swap
  · refine ⟨0, [], rets, [], ⟨rfl, rfl⟩, by simp [Within], fun rd hl hL => absurd ⟨rd, hl, ?_⟩ hex⟩
    simpa using hL
  obtain ⟨rd1, hl1, hL1⟩ := hex
  obtain ⟨p, ng, gsq, d0, d1, rfl, rfl⟩ := clPre_shape (hpre rd1 hl1 hL1)
  obtain ⟨hT1, n, hn, rfl, cs, hlen, hcells1, hcan, hd⟩ := hpre rd1 hl1 hL1
  have hpre' : ∀ rd, LowDef κ rd → MemL rd Lin → SquaresAt rd gsq ∧ ∃ cs' : List E,
      cs'.length = 4 * n ∧ CellsAt rd p cs' ∧ ∀ c ∈ cs', IsCanonical128 c := by
    intro rd hl hL
    obtain ⟨hT, n', hn', hng', cs', hlen', hc', hcan', -⟩ := hpre rd hl hL
    obtain rfl : n = n' := gen_pow_inj' (by omega) (by omega) hng'
    exact ⟨hT, cs', hlen', hc', hcan'⟩
  -- the claims' and the squares' words are the caller's
  have hF : ∀ k, ∃ i, k < 4 * n → p.limb 0 * gpow k = gpow i ∧ RegionL Lin i := by
    intro k
    by_cases hk : k < 4 * n
    · obtain ⟨i, hi⟩ := forced_load_pred (Q := IsCanonical128) (x := E.ofLimbs 0 0 1) (fun rd hl hL => by
          obtain ⟨-, cs', hlen', hc', hcan'⟩ := hpre' rd hl hL
          exact ⟨cs'[k]'(by omega), hc' k (by omega), hcan' _ (List.getElem_mem _)⟩)
        (by simp [IsCanonical128]) hl1 hL1
      exact ⟨i, fun _ => hi⟩
    · exact ⟨0, fun h => absurd h hk⟩
  choose idx hidx using hF
  have hSq : ∀ j, ∃ i, j < 16 → gsq.limb 0 * gpow j = gpow i ∧ RegionL Lin i := by
    intro j
    by_cases hj : j < 16
    · obtain ⟨i, hi⟩ := forced_load (fun rd hl hL => (hpre' rd hl hL).1 j hj) hl1 hL1
      exact ⟨i, fun _ => hi⟩
    · exact ⟨0, fun h => absurd h hj⟩
  choose sidx hsidx using hSq
  have hgK : IsInK gsq := (hT1 0 (by norm_num)).1
  have hcellsR : ∀ rd, MemL rd Lin → CellsAt rd p cs := fun rd hL k hk =>
    load_agree hL hL1 (hidx k (by omega)).1 (hidx k (by omega)).2 (hcells1 k hk)
  have hlow : ∀ rd, LowDef κ rd → Low16 rd := fun rd hl i hi =>
    hl i (lt_of_lt_of_le hi (Nat.pow_le_pow_right (by norm_num) hκ))
  rcases Nat.eq_zero_or_pos n with rfl | hn1
  · -- no claims: the empty digest
    obtain rfl : cs = [] := List.length_eq_zero_iff.mp (by simpa using hlen)
    refine ⟨fs "claim_list_digest", [], [d0, d1], [], ⟨rfl, rfl⟩, by simp [Within], fun rd hl hL => ?_⟩
    have h4 : listVal (cldZeroList p gsq d0 d1) (.n 4) = 0 := by
      show (1 : E) + word 1 0 0 = 0; rw [word_one, e_add_self]
    have hw := walk_cld_zero _ h4
    have hev := holds_of_holdsList find_claim_list_digest (cld_holds_zero rd p gsq hd) hw
    obtain ⟨e1, e2, e3, e4, e5⟩ := cld_zero_events (listVal (cldZeroList p gsq d0 d1))
    have h := relAtIn_of_walk (P := coreProgram) (fs := fs) (cert := cert) (rd := rd) coreProgram_wf
      (R := RegionL Lin) (D := RegionL []) (Dk := fun _ => False) (fp := fp) (N := 0) find_claim_list_digest
      (Or.inl (by decide +kernel)) rfl hw rfl hev (by rw [e1, e2]; rfl) (by rw [e3]; simp)
      (by rw [e4]; exact ⟨rfl, fun _ h => h⟩) (by rw [e5]; simp) (fun i hi => by obtain ⟨q, hq, _⟩ := hi; simp at hq)
    rwa [e2, List.sum_nil, Nat.add_zero, Nat.add_zero] at h
  -- the windows' scratch table, the tail, the last claim
  have hpK : IsInK p := (hcells1 0 (by omega)).1
  obtain ⟨w, hw⟩ : ∃ w, w = (n - 1) / 32 := ⟨_, rfl⟩
  obtain ⟨t, ht⟩ : ∃ t, t = (n - 1) % 32 := ⟨_, rfl⟩
  have ht32 : t < 32 := by omega
  have hwt : n = 32 * w + t + 1 := by omega
  obtain ⟨cx, hcx⟩ : ∃ cx, cx = fp + fs "claim_list_digest" := ⟨_, rfl⟩
  set KL : Layout := clScratchL p cs cx w ++ pinL (fun k => cs.getD k 0) idx (4 * n) ++
    pinL (fun j => gen ^ 2 ^ j) sidx 16 with hKL
  have hKLmem : ∀ rd', MemL rd' KL → SquaresAt rd' gsq ∧ CellsAt rd' p cs ∧ ClScratch rd' p (gen ^ cx) cs w := by
    intro rd' h
    refine ⟨fun j hj => pin_loads h hgK (fun j hj => (hsidx j hj).1) (fun q hq => List.mem_append_right _ hq) j hj,
      fun k hk => ?_, clScratch_of_memL h fun q hq => List.mem_append_left _ (List.mem_append_left _ hq)⟩
    have := pin_loads h hpK (fun k hk => (hidx k hk).1)
      (fun q hq => List.mem_append_left _ (List.mem_append_right _ hq)) k (by omega)
    rwa [List.getD_eq_getElem _ _ hk] at this
  have hb := blocks_canonical hlen hcan
  have r86 : ∀ rd', MemL rd' KL → w ≠ 0 →
      coreProgram.Rel rd' "__loop86" [word 1 0 0, gen ^ w, gen ^ cx, gsq] [] := fun rd' h hw0 => by
    obtain ⟨hT', hc', hs'⟩ := hKLmem rd' h
    rw [word_one, ← pow_zero gen]
    exact (loop_iff (l86Step_mono rd' (gen ^ cx) gsq) (l86_step rd' (gen ^ w) (gen ^ cx) gsq) 0).mpr
      ⟨w, by omega, rfl, fun j h1 h2 he => by have := gen_pow_inj' (by omega) (by omega) he; omega,
        fun j _ h2 => windows_bwd hT' hlen (by omega) hn hc' hcan hs' j h2⟩
  have rct : ∀ rd', MemL rd' KL → coreProgram.Rel rd' ctNames[t]! (clSlot p cs w)
      [(digestScalars (prefixDigest cs (n - 1))).1, (digestScalars (prefixDigest cs (n - 1))).2,
        p * gen ^ (128 * w) * gen ^ (4 * t)] := fun rd' h => by
    obtain ⟨-, hc', -⟩ := hKLmem rd' h
    rw [ctNames_getElem! ht32, claims_tail_iff t ht32]
    refine ⟨_, _, _, _, _, _, _, rfl, rfl, rfl, sliceOf cs (32 * w) t, length_sliceOf _ _ _, ?_, ?_⟩
    · rw [show 128 * w = 4 * (32 * w) by ring]
      exact cellsAt_sliceOf hc' (by omega)
    · refine (chainCells_prefix (blocksOf_sliceOf cs (32 * w) t)
        (fun j hj => baseMd_eq w j (by omega))).mpr ⟨fun j hj r => hb _ (by omega) r, ?_⟩
      rw [show 32 * w + t = n - 1 by omega]
  have rsl : ∀ rd', MemL rd' KL → coreProgram.Rel rd' "scaled_log__L6" [gen ^ n, gsq] [eOfNat (2 ^ 6 * n)] :=
    fun rd' h => (scaled_log_6_iff (hKLmem rd' h).1 _ _).mpr ⟨_, rfl, n, hn, rfl, rfl⟩
  let ks : List Kid := [⟨"__loop86", decide (word 1 0 0 + gen ^ w ≠ 0), [word 1 0 0, gen ^ w, gen ^ cx, gsq], KL,
      Returns []⟩,
    ⟨ctNames[t]!, true, clSlot p cs w, KL, Returns [(digestScalars (prefixDigest cs (n - 1))).1,
      (digestScalars (prefixDigest cs (n - 1))).2, p * gen ^ (128 * w) * gen ^ (4 * t)]⟩,
    ⟨"scaled_log__L6", true, [gen ^ n, gsq], KL, Returns [eOfNat (2 ^ 6 * n)]⟩]
  have hok : ∀ k ∈ ks, k.taken = true → CompleteAt fs cert κ k.f k.Lin k.args k.Out := by
    intro k hk htk
    simp only [ks, List.mem_cons, List.not_mem_nil, or_false] at hk
    rcases hk with rfl | rfl | rfl
    · refine completeAt_of_rel_pure cldKid_pure (by simp [cldKidSet]) (fun rd' h => r86 rd' h ?_) κ
      intro hw0
      simp only [hw0, pow_zero, word_one, e_add_self, ne_eq, not_true_eq_false, decide_false,
        Bool.false_eq_true] at htk
    · exact completeAt_of_rel_pure cldKid_pure (by
        rw [ctNames_getElem! ht32]; simp only [cldKidSet, List.mem_append]
        rw [List.getD_eq_getElem _ _ (by simp [ctNames]; omega)]
        exact Or.inr (List.getElem_mem _)) rct κ
    · exact completeAt_of_rel_pure cldKid_pure (by simp [cldKidSet]) rsl κ
  obtain ⟨N, LK, outs, hout, hWK, hK⟩ := kidsFromIn_of_kids κ ks hok (cx + 4 * (w + 1))
  refine ⟨fs "claim_list_digest" + 4 * (w + 1) + N, clScratchL p cs cx w ++ LK, [d0, d1], [], ⟨rfl, rfl⟩, ?_,
    fun rd hl hL => ?_⟩
  · rw [List.nil_append, LeanVM.Guest.B1.within_append]
    refine ⟨fun q hq => ?_, hWK.mono (by omega) (by omega)⟩
    obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hq
    have := List.mem_range.mp hj
    simp only [clSlot, List.length_cons, List.length_nil]
    omega
  rw [List.nil_append] at hL
  obtain ⟨hLo, hLin⟩ := Main.memL_append.mp hL
  obtain ⟨hLs, hLK⟩ := Main.memL_append.mp hLo
  have hT := (hpre' rd hl hLin).1
  have hscr : ClScratch rd p (gen ^ cx) cs w := clScratch_of_memL hLs fun q hq => hq
  obtain ⟨t1, t2, t3, t4, hh⟩ := cld_holds_pos (hlow rd hl) hT hn hn1 hlen (hcellsR rd hLin) hcan
    (by rw [← hw]; exact hscr) hd
  rw [← hw, ← ht] at hh
  set σ := listVal (cldList p gsq (gen ^ cx) d0 d1 cs n w t t1 t2 t3 t4) with hσ
  have h4 : σ (.n 4) ≠ 0 := fun h' => by
    have h'' : gen ^ n + word 1 0 0 = 0 := h'
    rw [word_one] at h''
    have := (gen_pow_eq_one_iff (by omega)).mp (e_add_eq_zero_iff.mp h'')
    omega
  have hw' := walk_cld_pos σ h4 ht32 (gen_pow_eq_ofK t)
  have hev := holds_of_holdsList find_claim_list_digest hh hw'
  obtain ⟨e1, e2, e3, e4, e5⟩ := cld_pos_events σ t
  have h35 : logG (σ (.n 35)) = 4 * (w + 1) := by
    rw [show σ (.n 35) = gen ^ (4 * (w + 1)) by
      show gen ^ w * word 2 0 0 * (gen ^ w * word 2 0 0) * (gen ^ w * word 2 0 0 * (gen ^ w * word 2 0 0)) = _
      rw [word_gen]; ring]
    exact logG_gen_pow (by omega)
  rw [h35] at e2
  have hown : ∀ i, cx ≤ i → i < cx + 4 * (w + 1) →
      ownData cert fp (fp + fs "claim_list_digest") "claim_list_digest" (allocs σ (cldEs σ t)) (cldEs σ t) i :=
    fun i h1 h2 => Or.inl ⟨(4 * (w + 1), cx), by rw [e2, hcx]; exact List.mem_singleton_self _, h1, by omega⟩
  have h := relAtIn_of_walk (P := coreProgram) (fs := fs) (cert := cert) (rd := rd) coreProgram_wf
    (R := RegionL Lin) (D := RegionL []) (Dk := fun i => False ∨ LeanVM.Guest.B1.outRegion ks outs i) (fp := fp)
    (N := N) find_claim_list_digest (Or.inl (by decide +kernel)) rfl hw' rfl hev
    (by rw [e1, e2, ← hcx]; simp only [List.map_cons, List.map_nil, bases]; rw [← gen_pow_eq_ofK]; rfl)
    (by rw [e3]; simp) ?_ ?_ (fun i hi => by obtain ⟨q, hq, _⟩ := hi; simp at hq)
  · rwa [e2, List.sum_cons, List.sum_nil, Nat.add_zero] at h
  · rw [e4, e2, List.sum_cons, List.sum_nil, Nat.add_zero, ← hcx]
    match outs, hout with
    | [o1, o2, o3], ⟨h1, h2, h3, _⟩ =>
      refine hK rd σ _ _ (fun _ => False) ⟨rfl, rfl, fun htk => ⟨rfl, ?_⟩, rfl, rfl, fun _ => ⟨rfl, ?_⟩, rfl, rfl,
        fun _ => ⟨rfl, ?_⟩, trivial⟩ hl hLK ?_ ?_
      · rw [(h1 htk).1]; rfl
      · rw [(h2 rfl).1]; rfl
      · rw [(h3 rfl).1]; rfl
      · have hKLr : MemL rd KL := by
          rw [hKL, Main.memL_append, Main.memL_append]
          refine ⟨⟨hLs, pin_memL hLin hL1 (fun k hk => (hidx k hk).2) fun k hk => ?_⟩,
            pin_memL hLin hL1 (fun j hj => (hsidx j hj).2) fun j hj => ?_⟩
          · have := (hcells1 k (by omega)).2
            rw [(hidx k hk).1, ← List.getD_eq_getElem _ 0] at this
            exact this
          · have := (hT1 j hj).2
            rw [(hsidx j hj).1] at this
            exact this
        simp only [LeanVM.Guest.B1.Kid.lins, ks, List.flatMap_cons, List.flatMap_nil, List.append_nil]
        exact Main.memL_append.mpr ⟨hKLr, Main.memL_append.mpr ⟨hKLr, hKLr⟩⟩
      · have hR : ∀ i, RegionL KL i → RegionL Lin i ∨
            ownData cert fp cx "claim_list_digest" [4 * (w + 1)] (cldEs σ t) i := by
          intro i hi
          obtain ⟨q, hq, hq1, hq2⟩ := hi
          rw [hKL, List.mem_append, List.mem_append] at hq
          rcases hq with (hq | hq) | hq
          · obtain ⟨h1, h2⟩ := clScratch_region ⟨q, hq, hq1, hq2⟩
            exact Or.inr (Or.inl ⟨(4 * (w + 1), cx), List.mem_singleton_self _, h1, by omega⟩)
          · obtain ⟨k, hk, rfl⟩ := pin_region ⟨q, hq, hq1, hq2⟩
            exact Or.inl (hidx k hk).2
          · obtain ⟨j, hj, rfl⟩ := pin_region ⟨q, hq, hq1, hq2⟩
            exact Or.inl (hsidx j hj).2
        exact ⟨fun _ i hi => Or.inl (hR i hi), fun _ i hi => Or.inl (hR i hi), fun _ i hi => Or.inl (hR i hi),
          trivial⟩
  · intro A hA
    rw [e5] at hA
    simp only [List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false] at hA
    have g36 : σ (.n 36) = gen ^ cx := rfl
    have g45 : σ (.n 45) = gen ^ (cx + 4 * w) := by
      show gen ^ cx * (gen ^ w * gen ^ w * (gen ^ w * gen ^ w)) = _
      ring
    have g52 : σ (.n 52) = p * gen ^ (128 * w) * gen ^ (4 * t) := rfl
    have hcl : ∀ k < 4, (σ (.n 52)).limb 0 * gpow k = gpow (idx (4 * (n - 1) + k)) := fun k hk => by
      rw [g52, addr_mul_gen_pow ((isInK_mul_gen_pow_iff _ _).mpr hpK), addr_mul_gen_pow hpK,
        show 128 * w + (4 * t + k) = 4 * (n - 1) + k by omega]
      exact (hidx _ (by omega)).1
    rcases hA with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨cx + 0, by rw [g36, limb0_gen_pow, gpow_add'], Or.inl (hown _ (by omega) (by omega))⟩
    · exact ⟨cx + 1, by rw [g36, limb0_gen_pow, gpow_add'], Or.inl (hown _ (by omega) (by omega))⟩
    · exact ⟨cx + 2, by rw [g36, limb0_gen_pow, gpow_add'], Or.inl (hown _ (by omega) (by omega))⟩
    · exact ⟨cx + 3, by rw [g36, limb0_gen_pow, gpow_add'], Or.inl (hown _ (by omega) (by omega))⟩
    · exact ⟨cx + 4 * w + 0, by rw [g45, limb0_gen_pow, gpow_add'], Or.inl (hown _ (by omega) (by omega))⟩
    · exact ⟨cx + 4 * w + 1, by rw [g45, limb0_gen_pow, gpow_add'], Or.inl (hown _ (by omega) (by omega))⟩
    · exact ⟨cx + 4 * w + 2, by rw [g45, limb0_gen_pow, gpow_add'], Or.inl (hown _ (by omega) (by omega))⟩
    · exact ⟨cx + 4 * w + 3, by rw [g45, limb0_gen_pow, gpow_add'], Or.inl (hown _ (by omega) (by omega))⟩
    · exact ⟨_, hcl 0 (by omega), Or.inr (Or.inl (hidx _ (by omega)).2)⟩
    · exact ⟨_, hcl 1 (by omega), Or.inr (Or.inl (hidx _ (by omega)).2)⟩
    · exact ⟨_, hcl 2 (by omega), Or.inr (Or.inl (hidx _ (by omega)).2)⟩
    · exact ⟨_, hcl 3 (by omega), Or.inr (Or.inl (hidx _ (by omega)).2)⟩

theorem clScratchL_within {p : E} {cs : List E} {cx w : ℕ} :
    Within (clScratchL p cs cx w) cx (4 * (w + 1)) := fun q hq => by
  obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hq
  have := List.mem_range.mp hj
  simp only [clSlot, List.length_cons, List.length_nil]
  omega

theorem clScratchL_disj {p : E} {cs : List E} {cx w : ℕ} : DisjL (clScratchL p cs cx w) := by
  unfold DisjL clScratchL
  rw [List.pairwise_map]
  exact (List.pairwise_lt_range (n := w + 1)).imp fun {a b} h => Or.inl (by simp only [clSlot]; simp; omega)

/-- **`claim_list_digest` is complete, uniformly placed**, on a memory defined below `2^κ`,
`κ ≥ 16`. -/
theorem cld_completeRelD (fs : String → ℕ) (cert : String → V → ℕ) {κ : ℕ} (hκ : 16 ≤ κ) :
    CompleteRelD fs cert κ "claim_list_digest" ClPre := by
  intro args rets Lin hpre fp
  classical
  by_cases hex : ∃ rd1, LowDef κ rd1 ∧ MemL rd1 Lin
  swap
  · refine ⟨0, [], rets, [], ⟨rfl, rfl⟩, by simp [Within], disj_nil, fun rd hl hL => absurd ⟨rd, hl, ?_⟩ hex⟩
    simpa using hL
  obtain ⟨rd1, hl1, hL1⟩ := hex
  obtain ⟨p, ng, gsq, d0, d1, rfl, rfl⟩ := clPre_shape (hpre rd1 hl1 hL1)
  obtain ⟨hT1, n, hn, rfl, cs, hlen, hcells1, hcan, hd⟩ := hpre rd1 hl1 hL1
  have hpre' : ∀ rd, LowDef κ rd → MemL rd Lin → SquaresAt rd gsq ∧ ∃ cs' : List E,
      cs'.length = 4 * n ∧ CellsAt rd p cs' ∧ ∀ c ∈ cs', IsCanonical128 c := by
    intro rd hl hL
    obtain ⟨hT, n', hn', hng', cs', hlen', hc', hcan', -⟩ := hpre rd hl hL
    obtain rfl : n = n' := gen_pow_inj' (by omega) (by omega) hng'
    exact ⟨hT, cs', hlen', hc', hcan'⟩
  -- the claims' and the squares' words are the caller's
  have hF : ∀ k, ∃ i, k < 4 * n → p.limb 0 * gpow k = gpow i ∧ RegionL Lin i := by
    intro k
    by_cases hk : k < 4 * n
    · obtain ⟨i, hi⟩ := forced_load_pred (Q := IsCanonical128) (x := E.ofLimbs 0 0 1) (fun rd hl hL => by
          obtain ⟨-, cs', hlen', hc', hcan'⟩ := hpre' rd hl hL
          exact ⟨cs'[k]'(by omega), hc' k (by omega), hcan' _ (List.getElem_mem _)⟩)
        (by simp [IsCanonical128]) hl1 hL1
      exact ⟨i, fun _ => hi⟩
    · exact ⟨0, fun h => absurd h hk⟩
  choose idx hidx using hF
  have hSq : ∀ j, ∃ i, j < 16 → gsq.limb 0 * gpow j = gpow i ∧ RegionL Lin i := by
    intro j
    by_cases hj : j < 16
    · obtain ⟨i, hi⟩ := forced_load (fun rd hl hL => (hpre' rd hl hL).1 j hj) hl1 hL1
      exact ⟨i, fun _ => hi⟩
    · exact ⟨0, fun h => absurd h hj⟩
  choose sidx hsidx using hSq
  have hgK : IsInK gsq := (hT1 0 (by norm_num)).1
  have hcellsR : ∀ rd, MemL rd Lin → CellsAt rd p cs := fun rd hL k hk =>
    load_agree hL hL1 (hidx k (by omega)).1 (hidx k (by omega)).2 (hcells1 k hk)
  have hlow : ∀ rd, LowDef κ rd → Low16 rd := fun rd hl i hi =>
    hl i (lt_of_lt_of_le hi (Nat.pow_le_pow_right (by norm_num) hκ))
  rcases Nat.eq_zero_or_pos n with rfl | hn1
  · -- no claims: the empty digest
    obtain rfl : cs = [] := List.length_eq_zero_iff.mp (by simpa using hlen)
    refine ⟨fs "claim_list_digest", [], [d0, d1], [], ⟨rfl, rfl⟩, by simp [Within], disj_nil, fun rd hl hL => ?_⟩
    have h4 : listVal (cldZeroList p gsq d0 d1) (.n 4) = 0 := by
      show (1 : E) + word 1 0 0 = 0; rw [word_one, e_add_self]
    have hw := walk_cld_zero _ h4
    have hev := holds_of_holdsList find_claim_list_digest (cld_holds_zero rd p gsq hd) hw
    obtain ⟨e1, e2, e3, e4, e5⟩ := cld_zero_events (listVal (cldZeroList p gsq d0 d1))
    have h := relAtIn_of_walk (P := coreProgram) (fs := fs) (cert := cert) (rd := rd) coreProgram_wf
      (R := RegionL Lin) (D := RegionL []) (Dk := fun _ => False) (fp := fp) (N := 0) find_claim_list_digest
      (Or.inl (by decide +kernel)) rfl hw rfl hev (by rw [e1, e2]; rfl) (by rw [e3]; simp)
      (by rw [e4]; exact ⟨rfl, fun _ h => h⟩) (by rw [e5]; simp) (fun i hi => by obtain ⟨q, hq, _⟩ := hi; simp at hq)
    rwa [e2, List.sum_nil, Nat.add_zero, Nat.add_zero] at h
  -- the windows' scratch table, the tail, the last claim
  have hpK : IsInK p := (hcells1 0 (by omega)).1
  obtain ⟨w, hw⟩ : ∃ w, w = (n - 1) / 32 := ⟨_, rfl⟩
  obtain ⟨t, ht⟩ : ∃ t, t = (n - 1) % 32 := ⟨_, rfl⟩
  have ht32 : t < 32 := by omega
  have hwt : n = 32 * w + t + 1 := by omega
  obtain ⟨cx, hcx⟩ : ∃ cx, cx = fp + fs "claim_list_digest" := ⟨_, rfl⟩
  set KL : Layout := clScratchL p cs cx w ++ pinL (fun k => cs.getD k 0) idx (4 * n) ++
    pinL (fun j => gen ^ 2 ^ j) sidx 16 with hKL
  have hKLmem : ∀ rd', MemL rd' KL → SquaresAt rd' gsq ∧ CellsAt rd' p cs ∧ ClScratch rd' p (gen ^ cx) cs w := by
    intro rd' h
    refine ⟨fun j hj => pin_loads h hgK (fun j hj => (hsidx j hj).1) (fun q hq => List.mem_append_right _ hq) j hj,
      fun k hk => ?_, clScratch_of_memL h fun q hq => List.mem_append_left _ (List.mem_append_left _ hq)⟩
    have := pin_loads h hpK (fun k hk => (hidx k hk).1)
      (fun q hq => List.mem_append_left _ (List.mem_append_right _ hq)) k (by omega)
    rwa [List.getD_eq_getElem _ _ hk] at this
  have hb := blocks_canonical hlen hcan
  have r86 : ∀ rd', MemL rd' KL → w ≠ 0 →
      coreProgram.Rel rd' "__loop86" [word 1 0 0, gen ^ w, gen ^ cx, gsq] [] := fun rd' h hw0 => by
    obtain ⟨hT', hc', hs'⟩ := hKLmem rd' h
    rw [word_one, ← pow_zero gen]
    exact (loop_iff (l86Step_mono rd' (gen ^ cx) gsq) (l86_step rd' (gen ^ w) (gen ^ cx) gsq) 0).mpr
      ⟨w, by omega, rfl, fun j h1 h2 he => by have := gen_pow_inj' (by omega) (by omega) he; omega,
        fun j _ h2 => windows_bwd hT' hlen (by omega) hn hc' hcan hs' j h2⟩
  have rct : ∀ rd', MemL rd' KL → coreProgram.Rel rd' ctNames[t]! (clSlot p cs w)
      [(digestScalars (prefixDigest cs (n - 1))).1, (digestScalars (prefixDigest cs (n - 1))).2,
        p * gen ^ (128 * w) * gen ^ (4 * t)] := fun rd' h => by
    obtain ⟨-, hc', -⟩ := hKLmem rd' h
    rw [ctNames_getElem! ht32, claims_tail_iff t ht32]
    refine ⟨_, _, _, _, _, _, _, rfl, rfl, rfl, sliceOf cs (32 * w) t, length_sliceOf _ _ _, ?_, ?_⟩
    · rw [show 128 * w = 4 * (32 * w) by ring]
      exact cellsAt_sliceOf hc' (by omega)
    · refine (chainCells_prefix (blocksOf_sliceOf cs (32 * w) t)
        (fun j hj => baseMd_eq w j (by omega))).mpr ⟨fun j hj r => hb _ (by omega) r, ?_⟩
      rw [show 32 * w + t = n - 1 by omega]
  have rsl : ∀ rd', MemL rd' KL → coreProgram.Rel rd' "scaled_log__L6" [gen ^ n, gsq] [eOfNat (2 ^ 6 * n)] :=
    fun rd' h => (scaled_log_6_iff (hKLmem rd' h).1 _ _).mpr ⟨_, rfl, n, hn, rfl, rfl⟩
  let ks : List Kid := [⟨"__loop86", decide (word 1 0 0 + gen ^ w ≠ 0), [word 1 0 0, gen ^ w, gen ^ cx, gsq], KL,
      Returns []⟩,
    ⟨ctNames[t]!, true, clSlot p cs w, KL, Returns [(digestScalars (prefixDigest cs (n - 1))).1,
      (digestScalars (prefixDigest cs (n - 1))).2, p * gen ^ (128 * w) * gen ^ (4 * t)]⟩,
    ⟨"scaled_log__L6", true, [gen ^ n, gsq], KL, Returns [eOfNat (2 ^ 6 * n)]⟩]
  have hok : ∀ k ∈ ks, k.taken = true → CompleteAtD fs cert κ k.f k.Lin k.args k.Out := by
    intro k hk htk
    simp only [ks, List.mem_cons, List.not_mem_nil, or_false] at hk
    rcases hk with rfl | rfl | rfl
    · refine completeAt_of_rel_pureD cldKid_pure (by simp [cldKidSet]) (fun rd' h => r86 rd' h ?_) κ
      intro hw0
      simp only [hw0, pow_zero, word_one, e_add_self, ne_eq, not_true_eq_false, decide_false,
        Bool.false_eq_true] at htk
    · exact completeAt_of_rel_pureD cldKid_pure (by
        rw [ctNames_getElem! ht32]; simp only [cldKidSet, List.mem_append]
        rw [List.getD_eq_getElem _ _ (by simp [ctNames]; omega)]
        exact Or.inr (List.getElem_mem _)) rct κ
    · exact completeAt_of_rel_pureD cldKid_pure (by simp [cldKidSet]) rsl κ
  obtain ⟨N, LK, outs, hout, hWK, hDK, -, hK⟩ := kidsFromIn_of_kidsD κ ks hok (cx + 4 * (w + 1))
  refine ⟨fs "claim_list_digest" + 4 * (w + 1) + N, clScratchL p cs cx w ++ LK, [d0, d1], [], ⟨rfl, rfl⟩, ?_, ?_,
    fun rd hl hL => ?_⟩
  · rw [List.nil_append, LeanVM.Guest.B1.within_append]
    exact ⟨clScratchL_within.mono (by omega) (by omega), hWK.mono (by omega) (by omega)⟩
  · rw [List.nil_append]
    exact disj_append clScratchL_disj hDK clScratchL_within hWK le_rfl
  rw [List.nil_append] at hL
  obtain ⟨hLo, hLin⟩ := Main.memL_append.mp hL
  obtain ⟨hLs, hLK⟩ := Main.memL_append.mp hLo
  have hT := (hpre' rd hl hLin).1
  have hscr : ClScratch rd p (gen ^ cx) cs w := clScratch_of_memL hLs fun q hq => hq
  obtain ⟨t1, t2, t3, t4, hh⟩ := cld_holds_pos (hlow rd hl) hT hn hn1 hlen (hcellsR rd hLin) hcan
    (by rw [← hw]; exact hscr) hd
  rw [← hw, ← ht] at hh
  set σ := listVal (cldList p gsq (gen ^ cx) d0 d1 cs n w t t1 t2 t3 t4) with hσ
  have h4 : σ (.n 4) ≠ 0 := fun h' => by
    have h'' : gen ^ n + word 1 0 0 = 0 := h'
    rw [word_one] at h''
    have := (gen_pow_eq_one_iff (by omega)).mp (e_add_eq_zero_iff.mp h'')
    omega
  have hw' := walk_cld_pos σ h4 ht32 (gen_pow_eq_ofK t)
  have hev := holds_of_holdsList find_claim_list_digest hh hw'
  obtain ⟨e1, e2, e3, e4, e5⟩ := cld_pos_events σ t
  have h35 : logG (σ (.n 35)) = 4 * (w + 1) := by
    rw [show σ (.n 35) = gen ^ (4 * (w + 1)) by
      show gen ^ w * word 2 0 0 * (gen ^ w * word 2 0 0) * (gen ^ w * word 2 0 0 * (gen ^ w * word 2 0 0)) = _
      rw [word_gen]; ring]
    exact logG_gen_pow (by omega)
  rw [h35] at e2
  have hown : ∀ i, cx ≤ i → i < cx + 4 * (w + 1) →
      ownData cert fp (fp + fs "claim_list_digest") "claim_list_digest" (allocs σ (cldEs σ t)) (cldEs σ t) i :=
    fun i h1 h2 => Or.inl ⟨(4 * (w + 1), cx), by rw [e2, hcx]; exact List.mem_singleton_self _, h1, by omega⟩
  have h := relAtIn_of_walk (P := coreProgram) (fs := fs) (cert := cert) (rd := rd) coreProgram_wf
    (R := RegionL Lin) (D := RegionL []) (Dk := fun i => False ∨ LeanVM.Guest.B1.outRegion ks outs i) (fp := fp)
    (N := N) find_claim_list_digest (Or.inl (by decide +kernel)) rfl hw' rfl hev
    (by rw [e1, e2, ← hcx]; simp only [List.map_cons, List.map_nil, bases]; rw [← gen_pow_eq_ofK]; rfl)
    (by rw [e3]; simp) ?_ ?_ (fun i hi => by obtain ⟨q, hq, _⟩ := hi; simp at hq)
  · rwa [e2, List.sum_cons, List.sum_nil, Nat.add_zero] at h
  · rw [e4, e2, List.sum_cons, List.sum_nil, Nat.add_zero, ← hcx]
    match outs, hout with
    | [o1, o2, o3], ⟨h1, h2, h3, _⟩ =>
      refine hK rd σ _ _ (fun _ => False) ⟨rfl, rfl, fun htk => ⟨rfl, ?_⟩, rfl, rfl, fun _ => ⟨rfl, ?_⟩, rfl, rfl,
        fun _ => ⟨rfl, ?_⟩, trivial⟩ hl hLK ?_ ?_
      · rw [(h1 htk).1]; rfl
      · rw [(h2 rfl).1]; rfl
      · rw [(h3 rfl).1]; rfl
      · have hKLr : MemL rd KL := by
          rw [hKL, Main.memL_append, Main.memL_append]
          refine ⟨⟨hLs, pin_memL hLin hL1 (fun k hk => (hidx k hk).2) fun k hk => ?_⟩,
            pin_memL hLin hL1 (fun j hj => (hsidx j hj).2) fun j hj => ?_⟩
          · have := (hcells1 k (by omega)).2
            rw [(hidx k hk).1, ← List.getD_eq_getElem _ 0] at this
            exact this
          · have := (hT1 j hj).2
            rw [(hsidx j hj).1] at this
            exact this
        simp only [LeanVM.Guest.B1.Kid.lins, ks, List.flatMap_cons, List.flatMap_nil, List.append_nil]
        exact Main.memL_append.mpr ⟨hKLr, Main.memL_append.mpr ⟨hKLr, hKLr⟩⟩
      · have hR : ∀ i, RegionL KL i → RegionL Lin i ∨
            ownData cert fp cx "claim_list_digest" [4 * (w + 1)] (cldEs σ t) i := by
          intro i hi
          obtain ⟨q, hq, hq1, hq2⟩ := hi
          rw [hKL, List.mem_append, List.mem_append] at hq
          rcases hq with (hq | hq) | hq
          · obtain ⟨h1, h2⟩ := clScratch_region ⟨q, hq, hq1, hq2⟩
            exact Or.inr (Or.inl ⟨(4 * (w + 1), cx), List.mem_singleton_self _, h1, by omega⟩)
          · obtain ⟨k, hk, rfl⟩ := pin_region ⟨q, hq, hq1, hq2⟩
            exact Or.inl (hidx k hk).2
          · obtain ⟨j, hj, rfl⟩ := pin_region ⟨q, hq, hq1, hq2⟩
            exact Or.inl (hsidx j hj).2
        exact ⟨fun _ i hi => Or.inl (hR i hi), fun _ i hi => Or.inl (hR i hi), fun _ i hi => Or.inl (hR i hi),
          trivial⟩
  · intro A hA
    rw [e5] at hA
    simp only [List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false] at hA
    have g36 : σ (.n 36) = gen ^ cx := rfl
    have g45 : σ (.n 45) = gen ^ (cx + 4 * w) := by
      show gen ^ cx * (gen ^ w * gen ^ w * (gen ^ w * gen ^ w)) = _
      ring
    have g52 : σ (.n 52) = p * gen ^ (128 * w) * gen ^ (4 * t) := rfl
    have hcl : ∀ k < 4, (σ (.n 52)).limb 0 * gpow k = gpow (idx (4 * (n - 1) + k)) := fun k hk => by
      rw [g52, addr_mul_gen_pow ((isInK_mul_gen_pow_iff _ _).mpr hpK), addr_mul_gen_pow hpK,
        show 128 * w + (4 * t + k) = 4 * (n - 1) + k by omega]
      exact (hidx _ (by omega)).1
    rcases hA with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨cx + 0, by rw [g36, limb0_gen_pow, gpow_add'], Or.inl (hown _ (by omega) (by omega))⟩
    · exact ⟨cx + 1, by rw [g36, limb0_gen_pow, gpow_add'], Or.inl (hown _ (by omega) (by omega))⟩
    · exact ⟨cx + 2, by rw [g36, limb0_gen_pow, gpow_add'], Or.inl (hown _ (by omega) (by omega))⟩
    · exact ⟨cx + 3, by rw [g36, limb0_gen_pow, gpow_add'], Or.inl (hown _ (by omega) (by omega))⟩
    · exact ⟨cx + 4 * w + 0, by rw [g45, limb0_gen_pow, gpow_add'], Or.inl (hown _ (by omega) (by omega))⟩
    · exact ⟨cx + 4 * w + 1, by rw [g45, limb0_gen_pow, gpow_add'], Or.inl (hown _ (by omega) (by omega))⟩
    · exact ⟨cx + 4 * w + 2, by rw [g45, limb0_gen_pow, gpow_add'], Or.inl (hown _ (by omega) (by omega))⟩
    · exact ⟨cx + 4 * w + 3, by rw [g45, limb0_gen_pow, gpow_add'], Or.inl (hown _ (by omega) (by omega))⟩
    · exact ⟨_, hcl 0 (by omega), Or.inr (Or.inl (hidx _ (by omega)).2)⟩
    · exact ⟨_, hcl 1 (by omega), Or.inr (Or.inl (hidx _ (by omega)).2)⟩
    · exact ⟨_, hcl 2 (by omega), Or.inr (Or.inl (hidx _ (by omega)).2)⟩
    · exact ⟨_, hcl 3 (by omega), Or.inr (Or.inl (hidx _ (by omega)).2)⟩

/-- **`claim_list_digest` is complete, uniformly placed**, on a memory defined below `2^κ`,
`κ ≥ 16`. -/
theorem cld_completeRelB (fs : String → ℕ) (cert : String → V → ℕ) {κ : ℕ} (hκ : 16 ≤ κ) (B86 : E → ℕ) (Bct : ℕ → ℕ) (Bsl6 : ℕ)
    (h86 : TotalLeOn coreProgram fs "__loop86" LoopPre fun a => B86 (a.getD 1 0))
    (hct : ∀ t, t < 32 → TotalLe coreProgram fs ctNames[t]! fun _ => Bct t)
    (hsl6 : TotalLe coreProgram fs "scaled_log__L6" fun _ => Bsl6) :
    ∀ (args rets : List E) (Lin : Layout), (∀ rd, LowDef κ rd → MemL rd Lin → ClPre rd args rets) →
      CompleteAtB fs cert κ "claim_list_digest" Lin args (Returns rets)
        (cldBound fs B86 Bct Bsl6 (logG (args.getD 1 0))) := by
  intro args rets Lin hpre fp
  classical
  by_cases hex : ∃ rd1, LowDef κ rd1 ∧ MemL rd1 Lin
  swap
  · refine ⟨0, [], rets, [], ⟨rfl, rfl⟩, by simp [Within], disj_nil, Nat.zero_le _, fun rd hl hL => absurd ⟨rd, hl, ?_⟩ hex⟩
    simpa using hL
  obtain ⟨rd1, hl1, hL1⟩ := hex
  obtain ⟨p, ng, gsq, d0, d1, rfl, rfl⟩ := clPre_shape (hpre rd1 hl1 hL1)
  obtain ⟨hT1, n, hn, rfl, cs, hlen, hcells1, hcan, hd⟩ := hpre rd1 hl1 hL1
  have hlg : logG (gen ^ n) = n := by rw [gen_pow_eq_ofK]; exact logG_spec (by omega)
  rw [show ([p, gen ^ n, gsq] : List E).getD 1 0 = gen ^ n from rfl, hlg]
  have hpre' : ∀ rd, LowDef κ rd → MemL rd Lin → SquaresAt rd gsq ∧ ∃ cs' : List E,
      cs'.length = 4 * n ∧ CellsAt rd p cs' ∧ ∀ c ∈ cs', IsCanonical128 c := by
    intro rd hl hL
    obtain ⟨hT, n', hn', hng', cs', hlen', hc', hcan', -⟩ := hpre rd hl hL
    obtain rfl : n = n' := gen_pow_inj' (by omega) (by omega) hng'
    exact ⟨hT, cs', hlen', hc', hcan'⟩
  -- the claims' and the squares' words are the caller's
  have hF : ∀ k, ∃ i, k < 4 * n → p.limb 0 * gpow k = gpow i ∧ RegionL Lin i := by
    intro k
    by_cases hk : k < 4 * n
    · obtain ⟨i, hi⟩ := forced_load_pred (Q := IsCanonical128) (x := E.ofLimbs 0 0 1) (fun rd hl hL => by
          obtain ⟨-, cs', hlen', hc', hcan'⟩ := hpre' rd hl hL
          exact ⟨cs'[k]'(by omega), hc' k (by omega), hcan' _ (List.getElem_mem _)⟩)
        (by simp [IsCanonical128]) hl1 hL1
      exact ⟨i, fun _ => hi⟩
    · exact ⟨0, fun h => absurd h hk⟩
  choose idx hidx using hF
  have hSq : ∀ j, ∃ i, j < 16 → gsq.limb 0 * gpow j = gpow i ∧ RegionL Lin i := by
    intro j
    by_cases hj : j < 16
    · obtain ⟨i, hi⟩ := forced_load (fun rd hl hL => (hpre' rd hl hL).1 j hj) hl1 hL1
      exact ⟨i, fun _ => hi⟩
    · exact ⟨0, fun h => absurd h hj⟩
  choose sidx hsidx using hSq
  have hgK : IsInK gsq := (hT1 0 (by norm_num)).1
  have hcellsR : ∀ rd, MemL rd Lin → CellsAt rd p cs := fun rd hL k hk =>
    load_agree hL hL1 (hidx k (by omega)).1 (hidx k (by omega)).2 (hcells1 k hk)
  have hlow : ∀ rd, LowDef κ rd → Low16 rd := fun rd hl i hi =>
    hl i (lt_of_lt_of_le hi (Nat.pow_le_pow_right (by norm_num) hκ))
  rcases Nat.eq_zero_or_pos n with rfl | hn1
  · -- no claims: the empty digest
    obtain rfl : cs = [] := List.length_eq_zero_iff.mp (by simpa using hlen)
    refine ⟨fs "claim_list_digest", [], [d0, d1], [], ⟨rfl, rfl⟩, by simp [Within], disj_nil,
      by unfold cldBound; omega, fun rd hl hL => ?_⟩
    have h4 : listVal (cldZeroList p gsq d0 d1) (.n 4) = 0 := by
      show (1 : E) + word 1 0 0 = 0; rw [word_one, e_add_self]
    have hw := walk_cld_zero _ h4
    have hev := holds_of_holdsList find_claim_list_digest (cld_holds_zero rd p gsq hd) hw
    obtain ⟨e1, e2, e3, e4, e5⟩ := cld_zero_events (listVal (cldZeroList p gsq d0 d1))
    have h := relAtIn_of_walk (P := coreProgram) (fs := fs) (cert := cert) (rd := rd) coreProgram_wf
      (R := RegionL Lin) (D := RegionL []) (Dk := fun _ => False) (fp := fp) (N := 0) find_claim_list_digest
      (Or.inl (by decide +kernel)) rfl hw rfl hev (by rw [e1, e2]; rfl) (by rw [e3]; simp)
      (by rw [e4]; exact ⟨rfl, fun _ h => h⟩) (by rw [e5]; simp) (fun i hi => by obtain ⟨q, hq, _⟩ := hi; simp at hq)
    rwa [e2, List.sum_nil, Nat.add_zero, Nat.add_zero] at h
  -- the windows' scratch table, the tail, the last claim
  have hpK : IsInK p := (hcells1 0 (by omega)).1
  obtain ⟨w, hw⟩ : ∃ w, w = (n - 1) / 32 := ⟨_, rfl⟩
  obtain ⟨t, ht⟩ : ∃ t, t = (n - 1) % 32 := ⟨_, rfl⟩
  have ht32 : t < 32 := by omega
  have hwt : n = 32 * w + t + 1 := by omega
  obtain ⟨cx, hcx⟩ : ∃ cx, cx = fp + fs "claim_list_digest" := ⟨_, rfl⟩
  set KL : Layout := clScratchL p cs cx w ++ pinL (fun k => cs.getD k 0) idx (4 * n) ++
    pinL (fun j => gen ^ 2 ^ j) sidx 16 with hKL
  have hKLmem : ∀ rd', MemL rd' KL → SquaresAt rd' gsq ∧ CellsAt rd' p cs ∧ ClScratch rd' p (gen ^ cx) cs w := by
    intro rd' h
    refine ⟨fun j hj => pin_loads h hgK (fun j hj => (hsidx j hj).1) (fun q hq => List.mem_append_right _ hq) j hj,
      fun k hk => ?_, clScratch_of_memL h fun q hq => List.mem_append_left _ (List.mem_append_left _ hq)⟩
    have := pin_loads h hpK (fun k hk => (hidx k hk).1)
      (fun q hq => List.mem_append_left _ (List.mem_append_right _ hq)) k (by omega)
    rwa [List.getD_eq_getElem _ _ hk] at this
  have hb := blocks_canonical hlen hcan
  have r86 : ∀ rd', MemL rd' KL → w ≠ 0 →
      coreProgram.Rel rd' "__loop86" [word 1 0 0, gen ^ w, gen ^ cx, gsq] [] := fun rd' h hw0 => by
    obtain ⟨hT', hc', hs'⟩ := hKLmem rd' h
    rw [word_one, ← pow_zero gen]
    exact (loop_iff (l86Step_mono rd' (gen ^ cx) gsq) (l86_step rd' (gen ^ w) (gen ^ cx) gsq) 0).mpr
      ⟨w, by omega, rfl, fun j h1 h2 he => by have := gen_pow_inj' (by omega) (by omega) he; omega,
        fun j _ h2 => windows_bwd hT' hlen (by omega) hn hc' hcan hs' j h2⟩
  have rct : ∀ rd', MemL rd' KL → coreProgram.Rel rd' ctNames[t]! (clSlot p cs w)
      [(digestScalars (prefixDigest cs (n - 1))).1, (digestScalars (prefixDigest cs (n - 1))).2,
        p * gen ^ (128 * w) * gen ^ (4 * t)] := fun rd' h => by
    obtain ⟨-, hc', -⟩ := hKLmem rd' h
    rw [ctNames_getElem! ht32, claims_tail_iff t ht32]
    refine ⟨_, _, _, _, _, _, _, rfl, rfl, rfl, sliceOf cs (32 * w) t, length_sliceOf _ _ _, ?_, ?_⟩
    · rw [show 128 * w = 4 * (32 * w) by ring]
      exact cellsAt_sliceOf hc' (by omega)
    · refine (chainCells_prefix (blocksOf_sliceOf cs (32 * w) t)
        (fun j hj => baseMd_eq w j (by omega))).mpr ⟨fun j hj r => hb _ (by omega) r, ?_⟩
      rw [show 32 * w + t = n - 1 by omega]
  have rsl : ∀ rd', MemL rd' KL → coreProgram.Rel rd' "scaled_log__L6" [gen ^ n, gsq] [eOfNat (2 ^ 6 * n)] :=
    fun rd' h => (scaled_log_6_iff (hKLmem rd' h).1 _ _).mpr ⟨_, rfl, n, hn, rfl, rfl⟩
  let ks : List Kid := [⟨"__loop86", decide (word 1 0 0 + gen ^ w ≠ 0), [word 1 0 0, gen ^ w, gen ^ cx, gsq], KL,
      Returns []⟩,
    ⟨ctNames[t]!, true, clSlot p cs w, KL, Returns [(digestScalars (prefixDigest cs (n - 1))).1,
      (digestScalars (prefixDigest cs (n - 1))).2, p * gen ^ (128 * w) * gen ^ (4 * t)]⟩,
    ⟨"scaled_log__L6", true, [gen ^ n, gsq], KL, Returns [eOfNat (2 ^ 6 * n)]⟩]
  have hne := ct_ne t ht32
  let bd : Kid → ℕ := fun k => if k.f = "__loop86" then B86 (gen ^ w)
    else if k.f = "scaled_log__L6" then Bsl6 else Bct t
  have hok : ∀ k ∈ ks, k.taken = true → CompleteAtB fs cert κ k.f k.Lin k.args k.Out (bd k) := by
    intro k hk htk
    simp only [ks, List.mem_cons, List.not_mem_nil, or_false] at hk
    rcases hk with rfl | rfl | rfl
    · have hw0 : w ≠ 0 := by
        intro hw0
        simp only [hw0, pow_zero, word_one, e_add_self, ne_eq, not_true_eq_false, decide_false,
          Bool.false_eq_true] at htk
      have hpre86 : LoopPre [word 1 0 0, gen ^ w, gen ^ cx, gsq] := by
        rw [word_one]
        exact loopPre_gen (Nat.pos_of_ne_zero hw0) (by omega) _
      exact completeAt_of_rel_pureBat cldKid_pure (by simp [cldKidSet]) (fun rd' h => r86 rd' h hw0) κ
        fun rd t hn hv hb => h86 rd t [word 1 0 0, gen ^ w, gen ^ cx, gsq] [] hn hpre86 hv hb
    · refine (completeAt_of_rel_pureB cldKid_pure (by
        rw [ctNames_getElem! ht32]; simp only [cldKidSet, List.mem_append]
        rw [List.getD_eq_getElem _ _ (by simp [ctNames]; omega)]
        exact Or.inr (List.getElem_mem _)) rct κ (hct t ht32)).mono le_rfl
        (by simp only [bd, hne.1, hne.2, ↓reduceIte, le_refl])
    · exact completeAt_of_rel_pureB cldKid_pure (by simp [cldKidSet]) rsl κ hsl6
  obtain ⟨N, LK, outs, hout, hWK, hDK, hNb, -, hK⟩ := kidsFromIn_of_kidsB κ bd ks hok (cx + 4 * (w + 1))
  refine ⟨fs "claim_list_digest" + 4 * (w + 1) + N, clScratchL p cs cx w ++ LK, [d0, d1], [], ⟨rfl, rfl⟩, ?_, ?_,
    ?_, fun rd hl hL => ?_⟩
  · rw [List.nil_append, LeanVM.Guest.B1.within_append]
    exact ⟨clScratchL_within.mono (by omega) (by omega), hWK.mono (by omega) (by omega)⟩
  · rw [List.nil_append]
    exact disj_append clScratchL_disj hDK clScratchL_within hWK le_rfl
  · have hw' : w = (n - 1) / 32 := hw
    have e1 : ("scaled_log__L6" = "__loop86") = False := by decide
    simp only [kidsBound, ks, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, bd, hne.1, hne.2, e1,
      ↓reduceIte, Nat.add_zero] at hNb
    unfold cldBound
    rw [← hw', ← ht]
    split at hNb <;> omega
  rw [List.nil_append] at hL
  obtain ⟨hLo, hLin⟩ := Main.memL_append.mp hL
  obtain ⟨hLs, hLK⟩ := Main.memL_append.mp hLo
  have hT := (hpre' rd hl hLin).1
  have hscr : ClScratch rd p (gen ^ cx) cs w := clScratch_of_memL hLs fun q hq => hq
  obtain ⟨t1, t2, t3, t4, hh⟩ := cld_holds_pos (hlow rd hl) hT hn hn1 hlen (hcellsR rd hLin) hcan
    (by rw [← hw]; exact hscr) hd
  rw [← hw, ← ht] at hh
  set σ := listVal (cldList p gsq (gen ^ cx) d0 d1 cs n w t t1 t2 t3 t4) with hσ
  have h4 : σ (.n 4) ≠ 0 := fun h' => by
    have h'' : gen ^ n + word 1 0 0 = 0 := h'
    rw [word_one] at h''
    have := (gen_pow_eq_one_iff (by omega)).mp (e_add_eq_zero_iff.mp h'')
    omega
  have hw' := walk_cld_pos σ h4 ht32 (gen_pow_eq_ofK t)
  have hev := holds_of_holdsList find_claim_list_digest hh hw'
  obtain ⟨e1, e2, e3, e4, e5⟩ := cld_pos_events σ t
  have h35 : logG (σ (.n 35)) = 4 * (w + 1) := by
    rw [show σ (.n 35) = gen ^ (4 * (w + 1)) by
      show gen ^ w * word 2 0 0 * (gen ^ w * word 2 0 0) * (gen ^ w * word 2 0 0 * (gen ^ w * word 2 0 0)) = _
      rw [word_gen]; ring]
    exact logG_gen_pow (by omega)
  rw [h35] at e2
  have hown : ∀ i, cx ≤ i → i < cx + 4 * (w + 1) →
      ownData cert fp (fp + fs "claim_list_digest") "claim_list_digest" (allocs σ (cldEs σ t)) (cldEs σ t) i :=
    fun i h1 h2 => Or.inl ⟨(4 * (w + 1), cx), by rw [e2, hcx]; exact List.mem_singleton_self _, h1, by omega⟩
  have h := relAtIn_of_walk (P := coreProgram) (fs := fs) (cert := cert) (rd := rd) coreProgram_wf
    (R := RegionL Lin) (D := RegionL []) (Dk := fun i => False ∨ LeanVM.Guest.B1.outRegion ks outs i) (fp := fp)
    (N := N) find_claim_list_digest (Or.inl (by decide +kernel)) rfl hw' rfl hev
    (by rw [e1, e2, ← hcx]; simp only [List.map_cons, List.map_nil, bases]; rw [← gen_pow_eq_ofK]; rfl)
    (by rw [e3]; simp) ?_ ?_ (fun i hi => by obtain ⟨q, hq, _⟩ := hi; simp at hq)
  · rwa [e2, List.sum_cons, List.sum_nil, Nat.add_zero] at h
  · rw [e4, e2, List.sum_cons, List.sum_nil, Nat.add_zero, ← hcx]
    match outs, hout with
    | [o1, o2, o3], ⟨h1, h2, h3, _⟩ =>
      refine hK rd σ _ _ (fun _ => False) ⟨rfl, rfl, fun htk => ⟨rfl, ?_⟩, rfl, rfl, fun _ => ⟨rfl, ?_⟩, rfl, rfl,
        fun _ => ⟨rfl, ?_⟩, trivial⟩ hl hLK ?_ ?_
      · rw [(h1 htk).1]; rfl
      · rw [(h2 rfl).1]; rfl
      · rw [(h3 rfl).1]; rfl
      · have hKLr : MemL rd KL := by
          rw [hKL, Main.memL_append, Main.memL_append]
          refine ⟨⟨hLs, pin_memL hLin hL1 (fun k hk => (hidx k hk).2) fun k hk => ?_⟩,
            pin_memL hLin hL1 (fun j hj => (hsidx j hj).2) fun j hj => ?_⟩
          · have := (hcells1 k (by omega)).2
            rw [(hidx k hk).1, ← List.getD_eq_getElem _ 0] at this
            exact this
          · have := (hT1 j hj).2
            rw [(hsidx j hj).1] at this
            exact this
        simp only [LeanVM.Guest.B1.Kid.lins, ks, List.flatMap_cons, List.flatMap_nil, List.append_nil]
        exact Main.memL_append.mpr ⟨hKLr, Main.memL_append.mpr ⟨hKLr, hKLr⟩⟩
      · have hR : ∀ i, RegionL KL i → RegionL Lin i ∨
            ownData cert fp cx "claim_list_digest" [4 * (w + 1)] (cldEs σ t) i := by
          intro i hi
          obtain ⟨q, hq, hq1, hq2⟩ := hi
          rw [hKL, List.mem_append, List.mem_append] at hq
          rcases hq with (hq | hq) | hq
          · obtain ⟨h1, h2⟩ := clScratch_region ⟨q, hq, hq1, hq2⟩
            exact Or.inr (Or.inl ⟨(4 * (w + 1), cx), List.mem_singleton_self _, h1, by omega⟩)
          · obtain ⟨k, hk, rfl⟩ := pin_region ⟨q, hq, hq1, hq2⟩
            exact Or.inl (hidx k hk).2
          · obtain ⟨j, hj, rfl⟩ := pin_region ⟨q, hq, hq1, hq2⟩
            exact Or.inl (hsidx j hj).2
        exact ⟨fun _ i hi => Or.inl (hR i hi), fun _ i hi => Or.inl (hR i hi), fun _ i hi => Or.inl (hR i hi),
          trivial⟩
  · intro A hA
    rw [e5] at hA
    simp only [List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false] at hA
    have g36 : σ (.n 36) = gen ^ cx := rfl
    have g45 : σ (.n 45) = gen ^ (cx + 4 * w) := by
      show gen ^ cx * (gen ^ w * gen ^ w * (gen ^ w * gen ^ w)) = _
      ring
    have g52 : σ (.n 52) = p * gen ^ (128 * w) * gen ^ (4 * t) := rfl
    have hcl : ∀ k < 4, (σ (.n 52)).limb 0 * gpow k = gpow (idx (4 * (n - 1) + k)) := fun k hk => by
      rw [g52, addr_mul_gen_pow ((isInK_mul_gen_pow_iff _ _).mpr hpK), addr_mul_gen_pow hpK,
        show 128 * w + (4 * t + k) = 4 * (n - 1) + k by omega]
      exact (hidx _ (by omega)).1
    rcases hA with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨cx + 0, by rw [g36, limb0_gen_pow, gpow_add'], Or.inl (hown _ (by omega) (by omega))⟩
    · exact ⟨cx + 1, by rw [g36, limb0_gen_pow, gpow_add'], Or.inl (hown _ (by omega) (by omega))⟩
    · exact ⟨cx + 2, by rw [g36, limb0_gen_pow, gpow_add'], Or.inl (hown _ (by omega) (by omega))⟩
    · exact ⟨cx + 3, by rw [g36, limb0_gen_pow, gpow_add'], Or.inl (hown _ (by omega) (by omega))⟩
    · exact ⟨cx + 4 * w + 0, by rw [g45, limb0_gen_pow, gpow_add'], Or.inl (hown _ (by omega) (by omega))⟩
    · exact ⟨cx + 4 * w + 1, by rw [g45, limb0_gen_pow, gpow_add'], Or.inl (hown _ (by omega) (by omega))⟩
    · exact ⟨cx + 4 * w + 2, by rw [g45, limb0_gen_pow, gpow_add'], Or.inl (hown _ (by omega) (by omega))⟩
    · exact ⟨cx + 4 * w + 3, by rw [g45, limb0_gen_pow, gpow_add'], Or.inl (hown _ (by omega) (by omega))⟩
    · exact ⟨_, hcl 0 (by omega), Or.inr (Or.inl (hidx _ (by omega)).2)⟩
    · exact ⟨_, hcl 1 (by omega), Or.inr (Or.inl (hidx _ (by omega)).2)⟩
    · exact ⟨_, hcl 2 (by omega), Or.inr (Or.inl (hidx _ (by omega)).2)⟩
    · exact ⟨_, hcl 3 (by omega), Or.inr (Or.inl (hidx _ (by omega)).2)⟩

/-- `claim_list_digest`'s precondition at the claims `cs`. -/
def ClPreAt (cs : List E) (rd : Reader) : List E → List E → Prop
  | [ptr, ng, gsq], [d0, d1] => SquaresAt rd gsq ∧ ∃ n < 2 ^ 16, ng = gen ^ n ∧ cs.length = 4 * n ∧
      CellsAt rd ptr cs ∧ (∀ c ∈ cs, IsCanonical128 c) ∧
        (d0, d1) = digestScalars (blake2sBytes (cs.flatMap cellBytes))
  | _, _ => False

/-- **`claim_list_digest` is complete, uniformly placed, at the claims `cs`.** -/
theorem cld_completeRelAt (fs : String → ℕ) (cert : String → V → ℕ) {κ : ℕ} (hκ : 16 ≤ κ) (cs : List E) :
    CompleteRel fs cert κ "claim_list_digest" (ClPreAt cs) :=
  completeRel_mono (cld_completeRel fs cert hκ) fun rd args rets h => by
    unfold ClPreAt at h
    split at h
    · obtain ⟨hT, n, hn, hng, hlen, hc, hcan, hd⟩ := h
      exact ⟨hT, n, hn, hng, cs, hlen, hc, hcan, hd⟩
    · exact h.elim

/-- **`claim_list_digest` is complete, uniformly placed, at the claims `cs`.** -/
theorem cld_completeRelAtD (fs : String → ℕ) (cert : String → V → ℕ) {κ : ℕ} (hκ : 16 ≤ κ) (cs : List E) :
    CompleteRelD fs cert κ "claim_list_digest" (ClPreAt cs) :=
  completeRel_monoD (cld_completeRelD fs cert hκ) fun rd args rets h => by
    unfold ClPreAt at h
    split at h
    · obtain ⟨hT, n, hn, hng, hlen, hc, hcan, hd⟩ := h
      exact ⟨hT, n, hn, hng, cs, hlen, hc, hcan, hd⟩
    · exact h.elim

/-- **`claim_list_digest` is complete, uniformly placed, at the claims `cs`**, by a bounded tree. -/
theorem cld_completeRelAtB (fs : String → ℕ) (cert : String → V → ℕ) {κ : ℕ} (hκ : 16 ≤ κ) (cs : List E)
    (B86 : E → ℕ) (Bct : ℕ → ℕ) (Bsl6 : ℕ)
    (h86 : TotalLeOn coreProgram fs "__loop86" LoopPre fun a => B86 (a.getD 1 0))
    (hct : ∀ t, t < 32 → TotalLe coreProgram fs ctNames[t]! fun _ => Bct t)
    (hsl6 : TotalLe coreProgram fs "scaled_log__L6" fun _ => Bsl6) :
    ∀ (args rets : List E) (Lin : Layout), (∀ rd, LowDef κ rd → MemL rd Lin → ClPreAt cs rd args rets) →
      CompleteAtB fs cert κ "claim_list_digest" Lin args (Returns rets)
        (cldBound fs B86 Bct Bsl6 (cs.length / 4)) := by
  intro args rets Lin hpre
  classical
  by_cases hex : ∃ rd1, LowDef κ rd1 ∧ MemL rd1 Lin
  swap
  · intro fp
    exact ⟨0, [], rets, [], ⟨rfl, rfl⟩, by simp [Within], disj_nil, Nat.zero_le _, fun rd hl hL =>
      absurd ⟨rd, hl, by simpa using hL⟩ hex⟩
  obtain ⟨rd1, hl1, hL1⟩ := hex
  have hsh : ∃ p ng gsq d0 d1, args = [p, ng, gsq] ∧ rets = [d0, d1] := by
    have h := hpre rd1 hl1 hL1
    unfold ClPreAt at h
    split at h
    · exact ⟨_, _, _, _, _, rfl, rfl⟩
    · exact h.elim
  obtain ⟨p, ng, gsq, d0, d1, rfl, rfl⟩ := hsh
  obtain ⟨hT, n, hn, rfl, hlen, hc, hcan, hd⟩ := hpre rd1 hl1 hL1
  have hlg : logG (gen ^ n) = n := by rw [gen_pow_eq_ofK]; exact logG_spec (by omega)
  have hbase := cld_completeRelB fs cert hκ B86 Bct Bsl6 h86 hct hsl6 [p, gen ^ n, gsq] [d0, d1] Lin
    (fun rd hl hL => by
      obtain ⟨a, n', b, c, d, e, f, g⟩ := hpre rd hl hL
      exact ⟨a, n', b, c, cs, d, e, f, g⟩)
  refine hbase.mono le_rfl (le_of_eq ?_)
  show cldBound fs B86 Bct Bsl6 (logG (gen ^ n)) = _
  rw [hlg, show cs.length / 4 = n by omega]

end
end LeanVM.Guest.B1.Digest
