/-
  LeanVM.Guest.B1.VerifySub.C.Vals

  `verify_sub`'s honest valuation, its front: the seed's capacity, the announced and root words
  absorbed, the out-of-domain grind's permutation, the bus grind's index, the slot weights, `β`
  and the three calls' arguments.
-/

module

public import LeanVM.Guest.B1.VerifySub.C.Side
public import LeanVM.Guest.B1.VerifySub.Ood
public import LeanVM.Guest.B1.VerifySub.Bus
public import LeanVM.Guest.B1.VerifySub.Tail

/-!
# The front, honestly

On the honest valuation `vsσ rd w args` (`ς`), each section's atoms satisfy their equations, so
its values follow from the oracle's (`w`: the allocations and the callees' returns), the
arguments and the words read. In the carried sponge's terms (`Fs`):

* `vs_seedCap`: the seed's capacity is `keccakF1600 (seedInput seed pi)`'s;
* `vs_word`, `vs_rootFs`: the stream's words `ws` at offsets `0 .. 9` read and absorbed: the root's
  sponge `vsRootFs` is the seed's capacity with the eight announced words, then the root's two,
  absorbed;
* `vs_ood`: the out-of-domain grind's permutation of the nonce `ws[10]` (`vsOodSt`), its cells,
  the point's challenge, `tabs` and the value's pointer;
* `vs_busGrind`: `g^(d - 16)`, the bus grind's index;
* `vs_fpw`: the fifteen slot weights squeezed from `opening_message`'s capacity, then `β`
  (`vsFpwFs`);
* `vs_calls`: the three calls' extra arguments.
-/

namespace LeanVM.Guest.B1.VerifySub

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Guest.B1.Fwd LeanVM.Guest.B1.Tables
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

/-! ## Blocks holding by evaluation alone -/

/-- An atom whose side condition is automatic. -/
def vsNoSideB : Stmt → Bool
  | .atom a => !needsSide a
  | _ => false

/-- **A block of atoms with automatic side conditions holds** from their equations. -/
theorem vs_holdsList_good {rd : Reader} {S : List Atom} {w : ℕ → E} {σ : Val} {C : CallRel}
    {blk : List Stmt} (hb : blk.all vsNoSideB = true) (hg : ∀ s ∈ blk, GoodS rd S w σ s)
    {next : Prop} {kret : List E → Prop} (hn : next) : Stmt.HoldsList C rd σ blk next kret := by
  refine holdsList_straightN blk (List.all_eq_true.mpr fun s hs ↦ ?_) (fun s hs ↦ ?_) hn
  · have := List.all_eq_true.mp hb s hs
    cases s <;> simp_all [vsNoSideB, straightB]
  · have h1 := List.all_eq_true.mp hb s hs
    cases s with
    | atom a =>
      simp only [vsNoSideB, Bool.not_eq_true'] at h1
      exact holds_of_good (hg _ hs) (vs_side_of_not_needs h1)
    | _ => simp [vsNoSideB] at h1

theorem vsg_const {rd : Reader} {S : List Atom} {w : ℕ → E} {σ : Val} {d : ℕ} {e : E}
    (h : GoodS rd S w σ (.atom (.const (.n d) e))) : σ (.n d) = e := h

theorem vsg_copy {rd : Reader} {S : List Atom} {w : ℕ → E} {σ : Val} {d s : ℕ}
    (h : GoodS rd S w σ (.atom (.copy (.n d) (.n s)))) : σ (.n d) = σ (.n s) := h

theorem vsg_mul {rd : Reader} {S : List Atom} {w : ℕ → E} {σ : Val} {d x y : ℕ} (hx : x < d)
    (hy : y < d) (h : GoodS rd S w σ (.atom (.mul (.n d) (.n x) (.n y)))) :
    σ (.n d) = σ (.n x) * σ (.n y) := by
  simp only [GoodS, Good] at h
  rwa [ite_pos' (show (V.n x).idx < (V.n d).idx ∧ (V.n y).idx < (V.n d).idx from ⟨hx, hy⟩)] at h

theorem vsg_quot {rd : Reader} {S : List Atom} {w : ℕ → E} {σ : Val} {d x y : ℕ} (hx : d < x)
    (h : GoodS rd S w σ (.atom (.mul (.n d) (.n x) (.n y)))) :
    σ (.n x) = σ (.n d) * (σ (.n y))⁻¹ := by
  simp only [GoodS, Good] at h
  rwa [ite_neg' (show ¬((V.n x).idx < (V.n d).idx ∧ (V.n y).idx < (V.n d).idx) from
    fun h' ↦ by simp only at h'; omega)] at h

theorem vsg_add {rd : Reader} {S : List Atom} {w : ℕ → E} {σ : Val} {d x y : ℕ}
    (h : GoodS rd S w σ (.atom (.add (.n d) (.n x) (.n y)))) : σ (.n d) = σ (.n x) + σ (.n y) := h

/-- A read through a pointer, of a word the memory holds. -/
theorem vsg_read {rd : Reader} {S : List Atom} {w : ℕ → E} {σ : Val} {d p : V} {off : ℕ} {v : E}
    (hg : GoodS rd S w σ (.atom (.load d p off))) (hS : Atom.load d p off ∉ S)
    (hm : LoadHolds rd (σ p) off v) : σ d = v := by
  simp only [GoodS, Good] at hg
  rw [hg.resolve_left hS, rdAt, hm.2]
  rfl

/-- A read's value, whatever the memory holds. -/
theorem vsg_rdAt {rd : Reader} {S : List Atom} {w : ℕ → E} {σ : Val} {d p : V} {off : ℕ}
    (hg : GoodS rd S w σ (.atom (.load d p off))) (hS : Atom.load d p off ∉ S) :
    σ d = rdAt rd (σ p) off := by
  simp only [GoodS, Good] at hg
  exact hg.resolve_left hS

theorem vsg_atom {rd : Reader} {S : List Atom} {w : ℕ → E} {σ : Val} {a : Atom}
    (h : GoodS rd S w σ (.atom a)) (hn : needsSide a = false) : a.Holds rd σ :=
  holds_of_good h (vs_side_of_not_needs hn)

theorem vsg_fsPack {rd : Reader} {S : List Atom} {w : ℕ → E} {σ : Val} {x : V} {b t : ℕ}
    (hg : ∀ s ∈ fsPackT x b t, GoodS rd S w σ s) : FsPackOk σ x b t :=
  ⟨hg _ List.mem_cons_self, hg _ (List.mem_cons_of_mem _ List.mem_cons_self)⟩

/-- The tail but its `ret`. -/
def vsTailP : List Stmt :=
  [vsMul 1918 66 66, vsMul 1919 1918 66, vsMul 1920 1919 1919, vsMul 1921 1920 66,
    vsMul 1922 278 1921, vsConst 1923 (word 134217728 0), vsRange 1922 1924 1925 1926 1923,
    vsConst 1927 (word 2 0), vsMul 1928 595 1927] ++ vsTabsT 1929 1930 ++
  [.dispatch (.n 1922) vsOpenNames
      [.n 1370, .n 1371, .n 1372, .n 1373, .n 1374, .n 1917, .n 268, .n 271, .n 1928, .n 1930]
      (vsRun 1931 5),
    vsCall "check_opening_terminal" [4, 254, 569, 581, 253, 579, 72, 583, 83, 1375, 275, 584, 848,
      1932, 1933, 1934, 1935, 1931, 304, 276] []] ++
  (List.range 19).flatMap (fun k ↦ [vsLd (1936 + k) 254 k, vsLd (1936 + k) 5 k]) ++
  (List.range 4).flatMap (fun k ↦ [vsLd (1955 + k) 570 k, vsLd (1955 + k) 5 (19 + k)]) ++
  [vsLd 580 5 23]

theorem vsTailT_split : vsTailT = vsTailP ++ [.ret []] := by
  simp only [vsTailT, vsTailP, List.append_assoc, List.cons_append, List.nil_append]

variable {rd : Reader} {w : ℕ → E} {args : List E}

local notation "ς" => vsσ rd w args

/-! ## The sections' equations -/

theorem vsHeadT_good (hl : args.length = 6) : ∀ s ∈ vsHeadT, GoodS rd vsSL w ς s :=
  vs_goodL hl (n := 0) (by decide +kernel)

theorem vsReadsT_good (hl : args.length = 6) : ∀ s ∈ vsReadsT, GoodS rd vsSL w ς s :=
  vs_goodL hl (n := 10) (by decide +kernel)

theorem vsSizesT_good (hl : args.length = 6) : ∀ s ∈ vsSizesT, GoodS rd vsSL w ς s :=
  vs_goodL hl (n := 41) (by decide +kernel)

theorem vsPushT_good (hl : args.length = 6) : ∀ s ∈ vsPushT, GoodS rd vsSL w ς s :=
  vs_goodL hl (n := 73) (by decide +kernel)

theorem vsRootsT_good (hl : args.length = 6) : ∀ s ∈ vsRootsT, GoodS rd vsSL w ς s :=
  vs_goodL hl (n := 236) (by decide +kernel)

theorem vsPlaceT_good (hl : args.length = 6) : ∀ s ∈ vsPlaceT, GoodS rd vsSL w ς s :=
  vs_goodL hl (n := 243) (by decide +kernel)

theorem vsOodT_good (hl : args.length = 6) : ∀ s ∈ vsOodT, GoodS rd vsSL w ς s :=
  vs_goodL hl (n := 249) (by decide +kernel)

theorem vsBusGrindT_good (hl : args.length = 6) : ∀ s ∈ vsBusGrindT, GoodS rd vsSL w ς s :=
  vs_goodL hl (n := 265) (by decide +kernel)

theorem vsFpwT_good (hl : args.length = 6) : ∀ s ∈ vsFpwT, GoodS rd vsSL w ς s :=
  vs_goodL hl (n := 272) (by decide +kernel)

theorem vsCallsT_good (hl : args.length = 6) : ∀ s ∈ vsCallsT, GoodS rd vsSL w ς s :=
  vs_goodL hl (n := 326) (by decide +kernel)

theorem vsMapsT_good (hl : args.length = 6) : ∀ s ∈ vsMapsT, GoodS rd vsSL w ς s :=
  vs_goodL hl (n := 342) (by decide +kernel)

theorem vsCtabT_good (hl : args.length = 6) : ∀ s ∈ vsCtabT, GoodS rd vsSL w ς s :=
  vs_goodL hl (n := 418) (by decide +kernel)

theorem vsLamT_good (hl : args.length = 6) : ∀ s ∈ vsLamT, GoodS rd vsSL w ς s :=
  vs_goodL hl (n := 996) (by decide +kernel)

theorem vsTailP_good (hl : args.length = 6) : ∀ s ∈ vsTailP, GoodS rd vsSL w ς s :=
  vs_goodL hl (n := 1540) (by decide +kernel)

/-! ## The head: the zero cells and the seed -/

theorem vs_zero (hl : args.length = 6) :
    ς (.n 8) = 0 ∧ ς (.n 9) = 0 ∧ ς (.n 10) = 0 ∧ ς (.n 11) = 0 := by
  have hG := vsHeadT_good (rd := rd) (w := w) hl
  have e : ∀ d ∈ [8, 9, 10, 11], ς (.n d) = 0 := by
    intro d hd
    rw [← word_zero]
    refine vsg_const (hG _ ?_)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
    rcases hd with rfl | rfl | rfl | rfl <;> simp [vsHeadT, vsConst]
  exact ⟨e 8 (by simp), e 9 (by simp), e 10 (by simp), e 11 (by simp)⟩

/-- **The seed's capacity** (G:3566-3570), on the arguments' digests. -/
theorem vs_seedCap (hl : args.length = 6) {seed pi : Digest}
    (h0 : args.getD 0 0 = (digestHalves pi).1) (h1 : args.getD 1 0 = (digestHalves pi).2)
    (h2 : args.getD 2 0 = (digestHalves seed).1) (h3 : args.getD 3 0 = (digestHalves seed).2) :
    [ς (.n 20), ς (.n 21), ς (.n 22), ς (.n 23), ς (.n 24)] =
      capOf (keccakF1600 (seedInput seed pi)) := by
  have hG := vsHeadT_good (rd := rd) (w := w) hl
  obtain ⟨z8, z9, z10, z11⟩ := vs_zero (rd := rd) (w := w) hl
  have hk : vsSeedAtom.Holds rd ς := vsg_atom (hG _ (by simp [vsHeadT, keccakA])) rfl
  obtain ⟨seed', pi', e1, e2, hc⟩ := vs_seed hk z8 z9 z10 z11
  have p2 := vsC_param (rd := rd) (w := w) hl (i := 2) (by omega)
  have p3 := vsC_param (rd := rd) (w := w) hl (i := 3) (by omega)
  have p0 := vsC_param (rd := rd) (w := w) hl (i := 0) (by omega)
  have p1 := vsC_param (rd := rd) (w := w) hl (i := 1) (by omega)
  have es : seed' = seed := by
    rw [← digestOfScalars_digestScalars seed', ← e1, p2, p3, h2, h3, digestOfScalars_digestScalars]
  have ep : pi' = pi := by
    rw [← digestOfScalars_digestScalars pi', ← e2, p0, p1, h0, h1, digestOfScalars_digestScalars]
  rw [hc, es, ep]

/-! ## The announced words and the root -/

/-- The values the stream's words at offsets `0 .. 9` are read into. -/
def vsWv (k : ℕ) : ℕ := [27, 30, 33, 36, 52, 55, 58, 61, 268, 271].getD k 0

theorem vsWv_lt : ∀ k < 8, vsWv k = vsX k := by decide

theorem fsNextT_sub_reads : ∀ k < 8, ∀ s ∈ fsNextT (.n 25) k (vsWv k), s ∈ vsReadsT := by
  intro k hk s hs
  interval_cases k <;>
    simp only [vsWv, List.getD_cons_zero, List.getD_cons_succ] at hs <;>
    simp only [vsReadsT, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] <;> tauto

theorem fsNextT_sub_roots : ∀ k, 8 ≤ k → k < 10 → ∀ s ∈ fsNextT (.n 25) k (vsWv k), s ∈ vsRootsT := by
  intro k hk1 hk2 s hs
  obtain rfl | rfl : k = 8 ∨ k = 9 := by omega
  · simp only [vsRootsT, List.mem_append]; exact Or.inl (Or.inr hs)
  · simp only [vsRootsT, List.mem_append]; exact Or.inr hs

theorem vs_notS_word : ∀ k < 10, Atom.load (.n (vsWv k)) (.n 25) k ∉ vsSL := by decide +kernel

/-- **A stream word, read and packed** (`fs_next`), offsets `0 .. 9`. -/
theorem vs_word (hl : args.length = 6) {k : ℕ} (hk : k < 10) {v : E}
    (hv : LoadHolds rd (w 25) k v) : ς (.n (vsWv k)) = v ∧ WordAt rd ς k (vsWv k) := by
  have hg : ∀ s ∈ fsNextT (.n 25) k (vsWv k), GoodS rd vsSL w ς s := by
    intro s hs
    by_cases h8 : k < 8
    · exact vsReadsT_good hl s (fsNextT_sub_reads k h8 s hs)
    · exact vsRootsT_good hl s (fsNextT_sub_roots k (by omega) hk s hs)
  have hv' : LoadHolds rd (ς (.n 25)) k v := by rw [vs_w hl (by decide)]; exact hv
  have e := vsg_read (hg _ List.mem_cons_self) (vs_notS_word k hk) hv'
  refine ⟨e, by rw [e]; exact hv', vsg_fsPack fun s hs ↦ hg s (List.mem_cons_of_mem _ hs)⟩

theorem vsWords_eq (σ : Val) : vsWords σ = (List.range 8).map fun i ↦ σ (.n (vsX i)) := rfl

/-- The root's sponge: the root's two words waiting. -/
noncomputable abbrev vsRootFsV (rd : Reader) (w : ℕ → E) (args : List E) : Fs := vsRootFs (vsσ rd w args)

/-- **The announced and root words absorbed** (G:3584-3637): from the seed's capacity, the stream's
words `0 .. 7` then `8`, `9` give the root's sponge. -/
theorem vs_rootFs (hl : args.length = 6) {ws : List E} (hwl : 10 ≤ ws.length)
    (hws : ∀ k < 10, LoadHolds rd (w 25) k (ws.getD k 0)) :
    (((⟨[ς (.n 20), ς (.n 21), ς (.n 22), ς (.n 23), ς (.n 24)], []⟩ : Fs).absorbAll (ws.take 8)
        dsObserve).absorb (ws.getD 8 0) dsObserve).absorb (ws.getD 9 0) dsObserve =
      vsRootFsV rd w args := by
  have W := fun k (hk : k < 10) ↦ vs_word (rd := rd) (w := w) hl hk (hws k hk)
  have hw8 : ∀ i < 8, WordAt rd ς i (vsX i) := fun i hi ↦ by
    rw [← vsWv_lt i hi]; exact (W i (by omega)).2
  have hk39 : vsAtom39.Holds rd ς :=
    vsg_atom (vsReadsT_good hl _ (by simp [vsReadsT, keccakA])) rfl
  have hk255 : vsAtom255.Holds rd ς :=
    vsg_atom (vsRootsT_good hl _ (by simp [vsRootsT, keccakA])) rfl
  have hws8 : ws.take 8 = vsWords ς := by
    apply List.ext_getElem (by simp [vsWords]; omega)
    intro i h1 h2
    have hi : i < 8 := by simpa [vsWords] using h2
    rw [List.getElem_take, ← List.getD_eq_getElem ws 0 (by omega), ← (W i (by omega)).1,
      vsWv_lt i hi]
    simp only [vsWords_eq, List.getElem_map, List.getElem_range]
  rw [hws8, vs_absorb8 hw8 hk39, ← (W 8 (by omega)).1, ← (W 9 (by omega)).1]
  exact vs_absorbRoot hw8 hk255

/-! ## The out-of-domain sample -/

/-- The out-of-domain grind's permutation: the nonce absorbed into the root's sponge. -/
noncomputable def vsOodSt (rd : Reader) (w : ℕ → E) (args : List E) (n : E) : KeccakState :=
  (vsRootFsV rd w args).nonceState n

theorem vs_ood_cells {σ : Val} {S : KeccakState} (hc : cells13 ((vsRun 288 13).map σ) = cellsOfState S false) :
    σ (.n 288) = cellsOfState S false 0 ∧ σ (.n 289) = cellsOfState S false 1 ∧
      [σ (.n 296), σ (.n 297), σ (.n 298), σ (.n 299), σ (.n 300)] = capOf S :=
  ⟨congrFun hc 0, congrFun hc 1, by
    rw [capOf, ← congrFun hc 8, ← congrFun hc 9, ← congrFun hc 10, ← congrFun hc 11,
      ← congrFun hc 12]; rfl⟩

theorem vsg_tabs {rd : Reader} {S : List Atom} {w : ℕ → E} {σ : Val} {c d : ℕ}
    (hb : (vsTabsT c d).all vsNoSideB = true) (hg : ∀ s ∈ vsTabsT c d, GoodS rd S w σ s) :
    σ (.n d) = σ (.n 4) * gen ^ winTabAt :=
  (vsTabsT_holds (C := fun _ _ _ ↦ True) (kret := fun _ ↦ True)
    (vs_holdsList_good hb hg (next := True) trivial)).1

/-- **The out-of-domain sample** (G:3649-3654): the nonce `n` at stream offset `10` absorbed after
the root's words and permuted (`vsOodSt`), `grind_check`'s cell, the point's capacity and
challenge, `tabs`, and the value's pointer `stream·g^11`. -/
theorem vs_ood (hl : args.length = 6) {ws : List E}
    (hws : ∀ k < 11, LoadHolds rd (w 25) k (ws.getD k 0)) :
    ς (.n 283) = ws.getD 10 0 ∧
      ς (.n 289) = cellsOfState (vsOodSt rd w args (ws.getD 10 0)) false 1 ∧
      [ς (.n 296), ς (.n 297), ς (.n 298), ς (.n 299), ς (.n 300)] =
        capOf (vsOodSt rd w args (ws.getD 10 0)) ∧
      ς (.n 303) = challengeOf (vsOodSt rd w args (ws.getD 10 0)) ∧
      ς (.n 302) = ς (.n 4) * gen ^ winTabAt ∧ ς (.n 312) = w 25 * gen ^ 11 := by
  have hG := vsOodT_good (rd := rd) (w := w) hl
  have W8 := vs_word (rd := rd) (w := w) hl (k := 8) (by omega) (hws 8 (by omega))
  have W9 := vs_word (rd := rd) (w := w) hl (k := 9) (by omega) (hws 9 (by omega))
  have hn : ∀ s ∈ fsNonceT (.n 25) 10 283, GoodS rd vsSL w ς s := fun s hs ↦ hG s (by
    rw [vsOodT]; exact List.mem_append_left _ (List.mem_append_left _
      (List.mem_append_left _ (List.mem_append_left _ hs))))
  have e283 : ς (.n 283) = ws.getD 10 0 :=
    vsg_read (hn _ List.mem_cons_self) (by decide +kernel)
      (by rw [vs_w hl (by decide)]; exact hws 10 (by omega))
  have hp : FsPackOk ς (.n 283) 284 dsPowNonce :=
    vsg_fsPack fun s hs ↦ hn s (List.mem_cons_of_mem _ hs)
  have h286 : ς (.n 286) = 0 := by
    rw [← word_zero]; exact vsg_const (hG _ (by simp [vsOodT, zero2T]))
  have h287 : ς (.n 287) = 0 := by
    rw [← word_zero]; exact vsg_const (hG _ (by simp [vsOodT, zero2T]))
  have hk : vsAtom288.Holds rd ς := vsg_atom (hG _ (by simp [vsOodT, keccakA])) rfl
  have hc := vs_oodPerm (by simpa [vsWv] using W8.2) (by simpa [vsWv] using W9.2) hp h286 h287 hk
  rw [e283] at hc
  obtain ⟨c0, c1, ccap⟩ := vs_ood_cells hc
  have h303 : ς (.n 303) = ς (.n 288) := vsg_copy (hG _ (by simp [vsOodT, vsCopy]))
  have h302 : ς (.n 302) = ς (.n 4) * gen ^ winTabAt := vsg_tabs (c := 301) (by decide) fun s hs ↦ hG s (by
    rw [vsOodT]; exact List.mem_append_left _ (List.mem_append_right _ hs))
  have h311 : ς (.n 311) = word 2048 0 := vsg_const (hG _ (by simp [vsOodT, vsConst]))
  have h312 : ς (.n 312) = ς (.n 25) * ς (.n 311) :=
    vsg_mul (by norm_num) (by norm_num) (hG _ (by simp [vsOodT, vsMul]))
  refine ⟨e283, c1, ccap, ?_, h302, ?_⟩
  · rw [h303, c0, Keccak.challengeOf_cells]; rfl
  · rw [h312, h311, word_g11, vs_w hl (by decide)]

/-! ## The bus grind -/

/-- **The bus grind's index** (G:3661-3663): `g^(d - 16)`, and `tabs`. -/
theorem vs_busGrind (hl : args.length = 6) {d : ℕ} (hd : 16 ≤ d) (h253 : w 253 = gen ^ d) :
    ς (.n 322) = gen ^ (d - 16) ∧ ς (.n 323) = gen ^ 17 ∧
      ς (.n 328) = ς (.n 4) * gen ^ winTabAt := by
  have hG := vsBusGrindT_good (rd := rd) (w := w) hl
  have h321 : ς (.n 321) = vsGinv16 := vsg_const (hG _ (by simp [vsBusGrindT, vsConst]))
  have h322 : ς (.n 322) = ς (.n 253) * ς (.n 321) :=
    vsg_mul (by norm_num) (by norm_num) (hG _ (by simp [vsBusGrindT, vsMul]))
  have h323 : ς (.n 323) = word 131072 0 := vsg_const (hG _ (by simp [vsBusGrindT, vsConst]))
  have h328 : ς (.n 328) = ς (.n 4) * gen ^ winTabAt := vsg_tabs (c := 327) (by decide) fun s hs ↦ hG s (by
    rw [vsBusGrindT]; exact List.mem_append_left _ (List.mem_append_right _ hs))
  refine ⟨?_, by rw [h323, word_g17], h328⟩
  rw [h322, h321, vs_w hl (by decide), h253, show d = (d - 16) + 16 by omega, pow_add,
    Nat.add_sub_cancel, mul_assoc, mul_comm (gen ^ 16), vsGinv16_mul, mul_one]

/-! ## The slot weights and `β` -/

/-- The sponge the slot weights are squeezed from: `opening_message`'s capacity. -/
def vsFpwFs (w : ℕ → E) : Fs := ⟨[w 315, w 316, w 317, w 318, w 319], []⟩

theorem vsSqzT_noSide (capb o : ℕ) : (vsSqzT capb o).all vsNoSideB = true := rfl

theorem vsg_sqz {rd : Reader} {S : List Atom} {w : ℕ → E} {σ : Val} {capb o : ℕ}
    (hz : σ (.n 8) = 0 ∧ σ (.n 9) = 0 ∧ σ (.n 10) = 0 ∧ σ (.n 11) = 0)
    (hg : ∀ s ∈ vsSqzT capb o, GoodS rd S w σ s) :
    (⟨(vsRun capb 5).map σ, []⟩ : Fs).squeeze =
      (σ (.n (o + 13)), ⟨[σ (.n (o + 8)), σ (.n (o + 9)), σ (.n (o + 10)), σ (.n (o + 11)),
        σ (.n (o + 12))], []⟩) :=
  (vsSqzT_holds (C := fun _ _ _ ↦ True) (kret := fun _ ↦ True) hz.1 hz.2.1 hz.2.2.1 hz.2.2.2
    (vs_holdsList_good (vsSqzT_noSide capb o) hg (next := True) trivial)).1

theorem vsSqz_mem_fpw {i : ℕ} (hi : i < 15) {s : Stmt} (hs : s ∈ vsSqzT (330 + 14 * i) (336 + 14 * i)) :
    s ∈ vsFpwT := by
  rw [vsFpwT]
  exact List.mem_append_left _ (List.mem_append_right _
    (List.mem_flatMap.2 ⟨i, List.mem_range.2 hi, List.mem_append_left _ hs⟩))

theorem vs_fpw_loop (hl : args.length = 6) : ∀ n ≤ 15,
    sqSt (vsFpwFs w) n = ⟨(vsRun (330 + 14 * n) 5).map ς, []⟩ ∧
      ∀ i < n, (sqSt (vsFpwFs w) i).squeeze.1 = ς (.n (349 + 14 * i)) := by
  have hG := vsFpwT_good (rd := rd) (w := w) hl
  have hz := vs_zero (rd := rd) (w := w) hl
  intro n
  induction n with
  | zero =>
    intro _
    refine ⟨?_, fun i hi ↦ absurd hi (by omega)⟩
    have c : ∀ i < 5, ς (.n (330 + i)) = w (315 + i) := fun i hi ↦ by
      rw [vsg_copy (hG _ (by
        rw [vsFpwT]
        exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _
          (List.mem_map.2 ⟨i, List.mem_range.2 hi, rfl⟩))))), vs_w hl (by interval_cases i <;> decide)]
    have c0 := c 0 (by omega)
    have c1 := c 1 (by omega)
    have c2 := c 2 (by omega)
    have c3 := c 3 (by omega)
    have c4 := c 4 (by omega)
    simp only [Nat.reduceAdd] at c0 c1 c2 c3 c4
    rw [show sqSt (vsFpwFs w) 0 = vsFpwFs w from rfl, Nat.mul_zero, Nat.add_zero, vsRun5,
      vsFpwFs]
    simp only [Nat.reduceAdd]
    rw [c0, c1, c2, c3, c4]
  | succ n ih =>
    intro hn
    obtain ⟨hs, hi⟩ := ih (by omega)
    have hq := vsg_sqz hz fun s hs ↦ hG s (vsSqz_mem_fpw (i := n) (by omega) hs)
    refine ⟨?_, fun i hi' ↦ ?_⟩
    · rw [sqSt, hs, hq, show 336 + 14 * n + 8 = 330 + 14 * (n + 1) by omega,
        show 336 + 14 * n + 9 = 330 + 14 * (n + 1) + 1 by omega,
        show 336 + 14 * n + 10 = 330 + 14 * (n + 1) + 2 by omega,
        show 336 + 14 * n + 11 = 330 + 14 * (n + 1) + 3 by omega,
        show 336 + 14 * n + 12 = 330 + 14 * (n + 1) + 4 by omega, vsRun5]
    · rcases Nat.lt_succ_iff_lt_or_eq.1 hi' with hi' | rfl
      · exact hi i hi'
      · rw [hs, hq, show 336 + 14 * i + 13 = 349 + 14 * i by omega]

/-- **The slot weights and `β`** (G:3664-3671): squeezed from `opening_message`'s capacity
(`vsFpwFs`), the fifteen weights at `349 + 14 i`, then `β` at `559` with the capacity after at
`554 .. 558`. -/
theorem vs_fpw (hl : args.length = 6) :
    (∀ i < 15, ς (.n (349 + 14 * i)) = ((vsFpwFs w).squeezeN 15).1.getD i 0) ∧
      ((vsFpwFs w).squeezeN 15).2.squeeze =
        (ς (.n 559), ⟨[ς (.n 554), ς (.n 555), ς (.n 556), ς (.n 557), ς (.n 558)], []⟩) := by
  have hG := vsFpwT_good (rd := rd) (w := w) hl
  have hz := vs_zero (rd := rd) (w := w) hl
  obtain ⟨h15, hi⟩ := vs_fpw_loop (rd := rd) (w := w) hl 15 le_rfl
  rw [squeezeN_eq]
  refine ⟨fun i hi' ↦ ?_, ?_⟩
  · rw [List.getD_eq_getElem _ _ (by simpa using hi'), List.getElem_map, List.getElem_range,
      hi i hi']
  · rw [h15]
    exact vsg_sqz hz fun s hs ↦ hG s (by rw [vsFpwT]; exact List.mem_append_right _ hs)

/-! ## The three calls -/

/-- **The three calls' arguments** (G:3674-3685): `tabs` thrice, `τ` read from `dims_g[6]`,
the output lanes at `col_eval_words·g^101`. -/
theorem vs_callsV (hl : args.length = 6) :
    ς (.n 561) = ς (.n 4) * gen ^ winTabAt ∧ ς (.n 572) = ς (.n 4) * gen ^ winTabAt ∧
      ς (.n 589) = ς (.n 4) * gen ^ winTabAt ∧ ς (.n 583) = rdAt rd (w 71) 6 ∧
      ς (.n 587) = w 582 * gen ^ 101 := by
  have hG := vsCallsT_good (rd := rd) (w := w) hl
  have h586 : ς (.n 586) = word 3710851743744 0 := vsg_const (hG _ (by simp [vsCallsT, vsConst]))
  have h587 : ς (.n 587) = ς (.n 582) * ς (.n 586) :=
    vsg_mul (by norm_num) (by norm_num) (hG _ (by simp [vsCallsT, vsMul]))
  have h583 : ς (.n 583) = rdAt rd (ς (.n 71)) 6 :=
    vsg_rdAt (hG _ (by simp [vsCallsT, vsLd])) (by decide +kernel)
  refine ⟨vsg_tabs (c := 560) (by decide) fun s hs ↦ hG s (by
      rw [vsCallsT]; exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _
        (List.mem_append_left _ (List.mem_append_left _ hs))))),
    vsg_tabs (c := 571) (by decide) fun s hs ↦ hG s (by
      rw [vsCallsT]; exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _
        (List.mem_append_right _ hs)))),
    vsg_tabs (c := 588) (by decide) fun s hs ↦ hG s (by
      rw [vsCallsT]; exact List.mem_append_left _ (List.mem_append_right _ hs)),
    by rw [h583, vs_w hl (by decide)], ?_⟩
  rw [h587, h586, word_g101, vs_w hl (by decide)]

end
end LeanVM.Guest.B1.VerifySub
