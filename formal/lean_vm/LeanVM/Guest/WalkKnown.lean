/-
  LeanVM.Guest.WalkKnown

  The windowed Merkle walk's cut obligations (`CutsKnown`) of `opening_queries`' specializations
  and their loops, from B1's facts on the templates (whir's `QueriesWalk`), read through the
  certificates' cells.
-/

module

public import LeanVM.Guest.Sound
public import LeanVM.Guest.WalkKnownDefs
public import LeanVM.Guest.B1.Opening.QueriesWalk

/-!
# The walks' obligations, from the templates

Checker K hands on, at the cuts of `opening_queries__*` and its loops (REC-GUEST-IFACE 'tool: walk
obligations'), the window bounds a `match` reads (`knownIf`: the word at `fp[o]·g^i`, if read, is
`g^e`, `e < n`) and the walk's tuples (`sems`). The certificates' generator writes them on fixed
cells; here a decided check per function (`loopOk`, `mainOk`) says each is one of the forms B1
proves on the template (`B1.Opening.QueriesWalk`):

* a loop's precondition is the walk (`WinWalk` or `WinWalk2`, tag `walkTag`) on its values
  `[2, 0, 1]` and `x ≠ N` (`tagNe`); each window bound is on the cell of a window pointer the prefix
  loads (`oqLoop0T_wins`, `oqLoop1T_wins1`, `oqLoop1T_wins2`: `winTripOk`), the tail call's tuple the
  walk from `x·g` (`oqLoop0T_tail`, `oqLoop1T_tail`);
* a specialization's precondition is `OqMainWins` on its values `[4, 6]`; its window bounds those of
  an odd count's first query (`oqMainT_wins`), and its loop call's tuple the walk from `x = 1`,
  conditional on the argument's cell holding `1` (`impTag … 1 1`, a constant `SET` in the call's
  setup), so it is `OqMainWins`' second half;
* at 40f877dc the queries call `walk_path__L{pd}_L{cd}`, which dispatches on the windows: the cut
  before each call hands it `WinsAt` (`winsTag`) of the loaded window pointer (`winSemOk`, the same
  B1 facts as the window bounds), and `walk_path`'s own precondition `WinsAt` on `wins` (value `2`)
  gives its cuts' window bounds (`wpOk`, `wp_cutsKnown`; PR661-IFACE 'walk-K').

`loop0_cutsKnown`, `loop1_cutsKnown`, `main_cutsKnown`: `CutsKnown j` from the body's template and
the decided check; `wp_cutsKnown` from the decided check alone. The instances are `WalkOq*.lean` and
`WalkWp.lean`.
-/

namespace LeanVM.Guest.End

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Check
open LeanVM.Guest.B1

@[expose] public section

/-! ## The tags -/

theorem walkTag_ge (kind odd d cd : ℕ) : 2 ≤ walkTag kind odd d cd := by
  unfold walkTag; omega

theorem semRel_lt {t : ℕ} (ht : t < 2 ^ 21) (rd : Reader) (ws : List E) :
    SemRel glob t rd ws ↔ SemRel0 glob t rd ws := by
  unfold SemRel
  rw [ite_eq_right_of_eq_false _ _ (eq_false (by omega)),
    ite_eq_right_of_eq_false _ _ (eq_false (by omega))]

/-- A walk tag of a kind but `2` is not `tagGkr` (`2^20`, a multiple of `4`). -/
theorem walkTag_ne_gkr {kind odd d cd : ℕ} (hk : kind < 4) (h2 : kind ≠ 2) :
    walkTag kind odd d cd ≠ tagGkr := by
  rw [show tagGkr = 4 * 262144 from rfl]
  unfold walkTag
  omega

theorem semRel0_walk {t : ℕ} (ht : 2 ≤ t) (hg : t ≠ tagGkr) (hl : t < 2 ^ 21) (rd : Reader)
    (ws : List E) : SemRel0 glob t rd ws ↔ walkSem t rd ws := by
  unfold SemRel0
  rw [ite_eq_right_of_eq_false _ _ (eq_false (by unfold tagNe; omega))]
  obtain ⟨n, rfl⟩ : ∃ n, t = n + 2 := ⟨t - 2, by omega⟩
  change (if n + 2 = tagGkr then GkrPar rd (ws.getD 0 0) (ws.getD 1 0) (ws.getD 2 0) (ws.getD 3 0)
    (ws.getD 4 0) else if 2 ^ 21 ≤ n + 2 then lqSem (n + 2) rd ws else walkSem (n + 2) rd ws) ↔ _
  rw [ite_eq_right_of_eq_false _ _ (eq_false hg), ite_eq_right_of_eq_false _ _ (eq_false (by omega))]

theorem semRel_ne (rd : Reader) (ws : List E) : SemRel glob tagNe rd ws ↔ ws.getD 0 0 ≠ ws.getD 1 0 := by
  rw [semRel_lt (by unfold tagNe; norm_num)]
  unfold SemRel0
  rw [ite_eq_left_of_eq_true _ _ (eq_true rfl)]

theorem semRel0_w0 {d cd : ℕ} (hc : cd < 64) (hl : walkTag 0 0 d cd < 2 ^ 21) (rd : Reader) (ws : List E) :
    SemRel0 glob (walkTag 0 0 d cd) rd ws ↔ WinWalk rd d cd (ws.getD 0 0) (ws.getD 1 0) (ws.getD 2 0) := by
  rw [semRel0_walk (walkTag_ge _ _ _ _) (walkTag_ne_gkr (by omega) (by omega)) hl]
  obtain ⟨h1, h2, h3, h4⟩ := walkTag_decode (d := d) (by decide : 0 < 4) (by decide : 0 < 2) hc
  simp only [walkSem, h1, h2, h3, h4]
  rfl

theorem semRel_w0 {d cd : ℕ} (hc : cd < 64) (hlt : walkTag 0 0 d cd < 2 ^ 21)
    (rd : Reader) (ws : List E) :
    SemRel glob (walkTag 0 0 d cd) rd ws ↔ WinWalk rd d cd (ws.getD 0 0) (ws.getD 1 0) (ws.getD 2 0) := by
  rw [semRel_lt hlt, semRel0_w0 hc hlt]

/-- **`walk_path`'s tag**: its windows at the tuple's one word. -/
theorem semRel_wins {d cd : ℕ} (hc : cd < 64) (hlt : winsTag d cd < 2 ^ 21) (rd : Reader)
    (ws : List E) : SemRel glob (winsTag d cd) rd ws ↔ WinsAt rd d cd (ws.getD 0 0) := by
  unfold winsTag at hlt ⊢
  rw [semRel_lt hlt, semRel0_walk (walkTag_ge _ _ _ _) (walkTag_ne_gkr (by omega) (by omega)) hlt]
  obtain ⟨h1, h2, h3, h4⟩ := walkTag_decode (d := d) (by decide : 0 < 4) (by decide : 1 < 2) hc
  simp only [walkSem, h1, h2, h3, h4]
  rfl

theorem semRel0_w1 {odd d cd : ℕ} (ho : odd < 2) (hc : cd < 64) (hl : walkTag 1 odd d cd < 2 ^ 21)
    (rd : Reader) (ws : List E) :
    SemRel0 glob (walkTag 1 odd d cd) rd ws ↔
      WinWalk2 rd d cd odd (ws.getD 0 0) (ws.getD 1 0) (ws.getD 2 0) := by
  rw [semRel0_walk (walkTag_ge _ _ _ _) (walkTag_ne_gkr (by omega) (by omega)) hl]
  obtain ⟨h1, h2, h3, h4⟩ := walkTag_decode (d := d) (by decide : 1 < 4) ho hc
  simp only [walkSem, h1, h2, h3, h4]

theorem semRel_w1 {odd d cd : ℕ} (ho : odd < 2) (hc : cd < 64) (hlt : walkTag 1 odd d cd < 2 ^ 21)
    (rd : Reader) (ws : List E) :
    SemRel glob (walkTag 1 odd d cd) rd ws ↔
      WinWalk2 rd d cd odd (ws.getD 0 0) (ws.getD 1 0) (ws.getD 2 0) := by
  rw [semRel_lt hlt, semRel0_w1 ho hc hlt]

theorem semRel_main {odd d cd base : ℕ} (ho : odd < 2) (hc : cd < 64) (hb : base < 2)
    (hlt : walkTag (2 + base) odd d cd < tagGkr) (rd : Reader) (ws : List E) :
    SemRel glob (walkTag (2 + base) odd d cd) rd ws ↔
      OqMainWins rd d cd odd base (ws.getD 0 0) (ws.getD 1 0) := by
  have hl : walkTag (2 + base) odd d cd < 2 ^ 21 := lt_trans hlt (by unfold tagGkr; norm_num)
  rw [semRel_lt hl, semRel0_walk (walkTag_ge _ _ _ _) hlt.ne hl]
  obtain ⟨h1, h2, h3, h4⟩ := walkTag_decode (d := d) (by omega : 2 + base < 4) ho hc
  obtain rfl | rfl : base = 0 ∨ base = 1 := by omega
  · simp only [walkSem, h1, h2, h3, h4]
  · simp only [walkSem, h1, h2, h3, h4]

/-- A conditional tag on the immediate `1` at position `1`: the relation holds if the second word
is `1`. -/
theorem semRel_imp {t : ℕ} (ht : t < 2 ^ 21) (rd : Reader) (ws : List E) :
    SemRel glob (impTag t 1 1) rd ws ↔ (ws.getD 1 0 = 1 → SemRel0 glob t rd ws) := by
  have ht : t < 2 ^ 32 := by omega
  have e1 : impPos (impTag t 1 1) = 1 := by
    unfold impPos impTag
    rw [Nat.add_mul_div_left _ _ (by positivity), Nat.div_eq_of_lt ht]
  have e2 : impImm (impTag t 1 1) = 1 := by
    unfold impImm impTag
    rw [Nat.add_mul_div_left _ _ (by positivity), Nat.div_eq_of_lt ht]
  have e3 : impBase (impTag t 1 1) = t := by
    unfold impBase impTag
    rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt ht]
  have hone : OffsetInstruction.immediateWord 1 0 0 = 1 := (Exec.imm_of_ofBits rfl).trans Exec.ofK_one
  unfold SemRel
  rw [ite_eq_left_of_eq_true _ _ (eq_true (by unfold impTag; omega)), e1, e2, e3, hone]

/-- **`level_queries`' tag**: `OqMainWins` of its walk on the tuple's one word, at `g^n`. -/
theorem semRel_lq {n odd base d cd : ℕ} (ho : odd < 2) (hb : base < 2) (hc : cd < 64) (hd : d < 64)
    (hn : n < 992) (rd : Reader) (ws : List E) :
    SemRel glob (lqTag n odd base d cd) rd ws ↔
      OqMainWins rd d cd odd base (ws.getD 0 0) (Protocol.Verifier.gen ^ n) := by
  have hw := walkTag_lt (kind := 2 + base) (by omega) ho hc hd
  have hlt : lqTag n odd base d cd < 2 ^ 26 := by unfold lqTag; omega
  have hge : 2 ^ 21 ≤ lqTag n odd base d cd := by unfold lqTag; omega
  unfold SemRel SemRel0
  rw [ite_eq_right_of_eq_false _ _ (eq_false (by omega)),
    ite_eq_right_of_eq_false _ _ (eq_false (by omega)),
    ite_eq_right_of_eq_false _ _ (eq_false (by unfold tagNe; omega))]
  obtain ⟨m, hm⟩ : ∃ m, lqTag n odd base d cd = m + 2 := ⟨lqTag n odd base d cd - 2, by omega⟩
  change globSem (lqTag n odd base d cd) rd ws ↔ _
  rw [hm]
  change (if m + 2 = tagGkr then GkrPar rd (ws.getD 0 0) (ws.getD 1 0) (ws.getD 2 0) (ws.getD 3 0)
    (ws.getD 4 0) else if 2 ^ 21 ≤ m + 2 then lqSem (m + 2) rd ws else walkSem (m + 2) rd ws) ↔ _
  rw [ite_eq_right_of_eq_false _ _ (eq_false (by unfold tagGkr; omega)),
    ite_eq_left_of_eq_true _ _ (eq_true (by omega)), ← hm]
  obtain ⟨e1, e2⟩ := lqTag_decode (n := n) hb ho hc hd
  obtain ⟨h1, h2, h3, h4⟩ := walkTag_decode (d := d) (by omega : 2 + base < 4) ho hc
  simp only [lqSem, e1, e2, h1, h2, h3, h4, Nat.add_sub_cancel_left]

/-! ## The certificates' cells -/

theorem valG_n {κ : ℕ} (L : MemoryImage κ) (fp : K) (C : Cert) (v : ℕ) :
    valG L fp C (.n v) = wd L fp (C.locs.getD v 0) := rfl

theorem getD_map_lt {f : ℕ → E} {l : List ℕ} {i : ℕ} (h : i < l.length) :
    (l.map f).getD i 0 = f (l.getD i 0) := by
  rw [List.getD_eq_getElem _ _ (by simpa using h), List.getD_eq_getElem _ _ h, List.getElem_map]

theorem cutAt_mem {C : Cert} {i : ℕ} (hi : i ≤ C.cuts.length) (h0 : 0 < i) : C.cutAt i ∈ C.cuts := by
  obtain ⟨i, rfl⟩ : ∃ i', i = i' + 1 := ⟨i - 1, by omega⟩
  have hc : C.cutAt (i + 1) = C.cuts[i]'(by omega) := by
    simp only [Cert.cutAt]
    exact nth_eq _
  rw [hc]
  exact List.getElem_mem _

theorem memIf_of_wins {κ : ℕ} {L : MemoryImage κ} {fp : K} {C : Cert} {d cd start : ℕ}
    {src : List (ℕ × ℕ)} {knownIf : List (ℕ × ℕ × ℕ)}
    (hok : knownIf.all (winTripOk C d cd src start) = true)
    (hw : ∀ v ∈ src, v.2 ≤ start → WinsAt L.read d cd (valG L fp C (.n v.1))) :
    MemIf L fp knownIf := by
  intro m hm val hv
  have h := List.all_eq_true.mp hok m hm
  simp only [winTripOk, List.any_eq_true, Bool.and_eq_true, beq_iff_eq, Nat.ble_eq,
    Nat.blt_eq] at h
  obtain ⟨v, hv', ⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
  have hW := hw v hv' h2
  rw [valG_n, ← h1] at hW
  obtain ⟨e, he, rfl⟩ := hW m.2.1 h3 val hv
  exact ⟨e, lt_of_lt_of_le he h4, rfl⟩

/-- A tuple `winSemOk` accepts holds: `WinsAt` of a loaded window pointer. -/
theorem semRel_of_winSem {κ : ℕ} {L : MemoryImage κ} {fp : K} {C : Cert} {d cd start : ℕ}
    {src : List (ℕ × ℕ)} {t : ℕ × List ℕ} (hc : cd < 64) (hlt : winsTag d cd < 2 ^ 21)
    (hok : winSemOk C d cd src start t = true)
    (hw : ∀ v ∈ src, v.2 ≤ start → WinsAt L.read d cd (valG L fp C (.n v.1))) :
    SemRel glob t.1 L.read (t.2.map (wd L fp)) := by
  simp only [winSemOk, List.any_eq_true, Bool.and_eq_true, beq_iff_eq, Nat.ble_eq] at hok
  obtain ⟨v, hv, rfl, hle⟩ := hok
  rw [semRel_wins hc hlt]
  exact hw v hv hle

/-- The length of a body's prefix does not read `walk_path`'s name. -/
theorem oqQueryT_length_walk (s : Oq) (bp cap flags wp : V) (b : ℕ) (emit : Bool) (pr : ℕ)
    (walk : String) : (oqQueryT s bp cap flags wp b emit pr walk).length =
      (oqQueryT s bp cap flags wp b emit pr "").length := by
  simp [oqQueryT]

theorem oqLoop0A_length_walk (s : Oq) (walk : String) :
    (oqLoop0A s walk).length = (oqLoop0A s "").length := by
  simp only [oqLoop0A, List.length_append, oqQueryT_length_walk]

theorem oqLoop1A_length_walk (s : Oq) (odd : ℕ) (walk : String) :
    (oqLoop1A s odd walk).length = (oqLoop1A s odd "").length := by
  simp only [oqLoop1A, List.length_append, oqQueryT_length_walk]

/-! ## The loops -/

/-- **A loop's cut obligations**, from its certificate's check (`loopOk`) and the walk's facts on
the prefixes of its body: the window pointers `src` name windows, the tail passes the walk on. -/
theorem loop_cutsKnown {j tag d cd xv tl : ℕ} {src : List (ℕ × ℕ)} (hc : cd < 64)
    (hltw : winsTag d cd < 2 ^ 21)
    (hok : loopOk (certOf j) tag d cd src xv tl = true) (W : Reader → E → E → E → Prop)
    (hsem : ∀ rd ws, SemRel glob tag rd ws ↔ W rd (ws.getD 0 0) (ws.getD 1 0) (ws.getD 2 0))
    (hwins : ∀ {κ : ℕ} (L : MemoryImage κ) (σ : Val) (n : ℕ),
      Stmt.HoldsList (coreProgram.Rel L.read) L.read σ ((coreOf j).body.take n) True (fun _ ↦ True) →
      W L.read (σ (.n 2)) (σ (.n 0)) (σ (.n 1)) → σ (.n 0) ≠ σ (.n 1) →
      ∀ v ∈ src, v.2 ≤ n → WinsAt L.read d cd (σ (.n v.1)))
    (htail : ∀ {κ : ℕ} (L : MemoryImage κ) (σ : Val) (n : ℕ), tl ≤ n →
      Stmt.HoldsList (coreProgram.Rel L.read) L.read σ ((coreOf j).body.take n) True (fun _ ↦ True) →
      W L.read (σ (.n 2)) (σ (.n 0)) (σ (.n 1)) → σ (.n 0) ≠ σ (.n 1) →
      W L.read (σ (.n 2)) (σ (.n xv)) (σ (.n 1))) :
    CutsKnown j := by
  intro κ L _ _ fp _ hsem' i hi h0 hl
  simp only [loopOk, Bool.and_eq_true, beq_iff_eq, List.all_eq_true] at hok
  obtain ⟨hs, hcuts⟩ := hok
  rw [hs] at hsem'
  have hW : W L.read (valG L fp (certOf j) (.n 2)) (valG L fp (certOf j) (.n 0))
      (valG L fp (certOf j) (.n 1)) :=
    (hsem _ _).mp (hsem' _ (List.mem_cons_self ..))
  have hne : valG L fp (certOf j) (.n 0) ≠ valG L fp (certOf j) (.n 1) :=
    (semRel_ne _ _).mp (hsem' _ (List.mem_cons_of_mem _ (List.mem_singleton_self _)))
  have hcut := hcuts _ (cutAt_mem hi h0)
  simp only [loopCutOk, Bool.and_eq_true, List.isEmpty_iff, List.all_eq_true] at hcut
  obtain ⟨⟨hkn, hki⟩, hsm⟩ := hcut
  have hwv := fun v hv hle ↦ hwins L _ _ hl hW hne v hv hle
  refine ⟨by rw [hkn]; intro _ h; simp at h, memIf_of_wins (by simpa using hki) hwv,
    fun t ht ↦ ?_⟩
  rcases Bool.or_eq_true_iff.mp (hsm t ht) with h | h
  · simp only [Bool.and_eq_true, beq_iff_eq, Nat.ble_eq] at h
    obtain ⟨rfl, hle⟩ := h
    exact (hsem _ _).mpr (htail L _ _ hle hl hW hne)
  · exact semRel_of_winSem hc hltw h hwv

/-- **A deeper loop's cut obligations** (`oqLoop0T`, the walk `WinWalk`). -/
theorem loop0_cutsKnown {j : ℕ} {s : Oq} {walk name : String}
    (hb : (coreOf j).body = oqLoop0T s walk name) (hc : s.cd < 64)
    (hlt : walkTag 0 0 (s.pd + s.cd) s.cd < 2 ^ 21) (hltw : winsTag (s.pd + s.cd) s.cd < 2 ^ 21)
    (hok : loop0Ok j s = true) :
    CutsKnown j := by
  refine loop_cutsKnown hc hltw hok (fun rd t x N ↦ WinWalk rd (s.pd + s.cd) s.cd t x N)
    (semRel_w0 hc hlt) (fun L σ n hl hw hne v hv hle ↦ ?_) (fun L σ n hle hl hw hne ↦ ?_)
  · simp only [List.mem_singleton] at hv
    subst hv
    rw [hb] at hl
    exact oqLoop0T_wins hle hl hw hne
  · rw [hb] at hl
    rw [← oqLoop0A_length_walk s walk] at hle
    exact oqLoop0T_tail hle hl hw hne

/-- **A level-0 loop's cut obligations** (`oqLoop1T`, the walk `WinWalk2`). -/
theorem loop1_cutsKnown {j odd : ℕ} {s : Oq} {walk name : String}
    (hb : (coreOf j).body = oqLoop1T s odd walk name) (ho : odd < 2) (hc : s.cd < 64)
    (hlt : walkTag 1 odd (s.pd + s.cd) s.cd < 2 ^ 21) (hltw : winsTag (s.pd + s.cd) s.cd < 2 ^ 21)
    (hok : loop1Ok j odd s = true) :
    CutsKnown j := by
  refine loop_cutsKnown hc hltw hok (fun rd t x N ↦ WinWalk2 rd (s.pd + s.cd) s.cd odd t x N)
    (semRel_w1 ho hc hlt) (fun L σ n hl hw hne v hv hle ↦ ?_) (fun L σ n hle hl hw hne ↦ ?_)
  · rw [hb] at hl
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
    rcases hv with rfl | rfl
    · exact oqLoop1T_wins1 hle hl hw hne
    · rw [← oqQueryT_length_walk _ _ _ _ _ _ _ _ walk] at hle
      exact oqLoop1T_wins2 hle hl hw hne
  · rw [hb] at hl
    rw [← oqLoop1A_length_walk s odd walk] at hle
    exact oqLoop1T_tail hle hl hw hne

/-! ## The specializations -/

/-- **A specialization's cut obligations** (`oqMainT`): its precondition `OqMainWins`, the first
query's windows (`oqMainT_wins`, an odd count) and the walk from `1` (its second half). -/
theorem main_cutsKnown {j o : ℕ} {s : Oq} {walk loop : String}
    (hb : (coreOf j).body = oqMainT s o walk loop) (ho : o < 2) (hodd : o = 1 → s.base = 1)
    (hc : s.cd < 64) (hbase : s.base < 2)
    (hlt : walkTag (2 + s.base) o (s.pd + s.cd) s.cd < tagGkr)
    (hltW : walkTag (if s.base = 1 then 1 else 0) o (s.pd + s.cd) s.cd < 2 ^ 21)
    (hltw : winsTag (s.pd + s.cd) s.cd < 2 ^ 21)
    (hok : mainOkS j o s = true) :
    CutsKnown j := by
  intro κ L _ _ fp _ hsem' i hi h0 hl
  simp only [mainOkS, mainOk, Bool.and_eq_true, beq_iff_eq, List.all_eq_true] at hok
  obtain ⟨hs, hcuts⟩ := hok
  rw [hs] at hsem'
  have hW : OqMainWins L.read (s.pd + s.cd) s.cd o s.base (valG L fp (certOf j) (.n 4))
      (valG L fp (certOf j) (.n 6)) :=
    (semRel_main ho hc hbase hlt _ _).mp (hsem' _ (List.mem_singleton_self _))
  have hcut := hcuts _ (cutAt_mem hi h0)
  simp only [mainCutOk, Bool.and_eq_true, List.isEmpty_iff, List.all_eq_true] at hcut
  obtain ⟨⟨hkn, hki⟩, hsm⟩ := hcut
  have hwv : ∀ v ∈ (if o = 1 then [((12 : ℕ), (6 : ℕ))] else []), v.2 ≤ ((certOf j).cutAt i).start →
      WinsAt L.read (s.pd + s.cd) s.cd (valG L fp (certOf j) (.n v.1)) := by
    intro v hv hle
    split at hv
    · rename_i h1
      simp only [List.mem_singleton] at hv
      subst hv
      rw [hb] at hl
      exact oqMainT_wins hle h1 hl hW
    · simp at hv
  refine ⟨by rw [hkn]; intro _ h; simp at h, memIf_of_wins (by simpa using hki) hwv,
    fun t ht ↦ ?_⟩
  rcases Bool.or_eq_true_iff.mp (hsm t ht) with ht' | ht'
  swap
  · exact semRel_of_winSem hc hltw ht' hwv
  · simp only [Bool.and_eq_true, beq_iff_eq] at ht'
    obtain ⟨⟨⟨ht1, hlen⟩, ha⟩, hb'⟩ := ht'
    rw [ht1, semRel_imp hltW]
    intro hx
    rw [getD_map_lt (by omega)] at hx
    have h2 := hW.2
    split at h2
    · rename_i h1
      rw [ite_eq_left_of_eq_true _ _ (eq_true h1), semRel0_w1 ho hc (by simpa [h1] using hltW),
        getD_map_lt (by omega),
        getD_map_lt (by omega), getD_map_lt (by omega), hx, ha, hb']
      exact h2
    · rename_i h1
      obtain rfl : o = 0 := by have := mt hodd h1; omega
      rw [ite_eq_right_of_eq_false _ _ (eq_false h1), semRel0_w0 hc (by simpa [h1] using hltW),
        getD_map_lt (by omega),
        getD_map_lt (by omega), getD_map_lt (by omega), hx, ha, hb']
      exact h2

/-! ## `walk_path` -/

/-- **`walk_path`'s cut obligations**: its precondition `WinsAt` on `wins` (value `2`), every
window bound one of its windows'. -/
theorem wp_cutsKnown {j d cd : ℕ} (hc : cd < 64) (hltw : winsTag d cd < 2 ^ 21)
    (hok : wpOk (certOf j) d cd = true) : CutsKnown j := by
  intro κ L _ _ fp _ hsem' i hi h0 _
  simp only [wpOk, Bool.and_eq_true, beq_iff_eq, List.all_eq_true] at hok
  obtain ⟨hs, hcuts⟩ := hok
  rw [hs] at hsem'
  have hW : WinsAt L.read d cd (valG L fp (certOf j) (.n 2)) := by
    have := (semRel_wins hc hltw _ _).mp (hsem' _ (List.mem_singleton_self _))
    simpa [valG_n] using this
  have hcut := hcuts _ (cutAt_mem hi h0)
  simp only [wpCutOk, Bool.and_eq_true, List.isEmpty_iff] at hcut
  obtain ⟨⟨hkn, hki⟩, hsm⟩ := hcut
  refine ⟨by rw [hkn]; intro _ h; simp at h, memIf_of_wins hki fun v hv _ ↦ ?_,
    by rw [hsm]; intro _ h; simp at h⟩
  simp only [List.mem_singleton] at hv
  subst hv
  exact hW

end
end LeanVM.Guest.End
