/-
  LeanVM.Guest.B1.Gkr.Loop7In

  `__loop6` loads from any region holding, at each iteration, its layer slot, its row, its round
  records and the words at the records' cursors.
-/

module

public import LeanVM.Guest.B1.Gkr.Layer
public import LeanVM.Guest.B1.Gkr.RoundsIn

/-!
# `__loop6`, loading from a region

`__loop6`'s body is straight but for a dispatch on its `parity = g^r` (`gkr_rounds__L{2r}`) and a
branch of straight statements ending in `gkr_rounds__L1` at an odd depth: it walks its statements
in turn, the dispatch's callee and the branch's block when taken (`ly_walk`).

* `Ly7In`: what iteration `j` reads, in `R`: the slot of `L = 2j + sh` (`51` words, through the
  next slot's stores), its row (`L + 42` words), position, `half = g^(j/4)` and
  `parity = g^(j % 4)`; the records from `rounds·pos` (`L + 5173` words), record `r`'s cursor
  `cj·g^(4r)`, the `4L + 12` words from `cj`; the table `k_mod_next` (`8` words).
* `loop7_relIn`: with those at every `j < m`, iteration `j < m` of `__loop6` loads from `R`, by
  the depth of its derivation; its rounds by `loop29_relIn` and `gkr_rounds_relIn`.
-/

namespace LeanVM.Guest.B1.Tables

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Memory
open LeanVM.Protocol.Verifier (gen)

@[expose] public section

/-! ## The walk -/

/-- A block of straight statements walks each, falling through. -/
theorem walk_straight_fall (σ : Val) {z : List Stmt} (h : z.all Main.Stmt.straight = true) :
    walk σ z = .fall (z.flatMap (Main.slEvs σ)) := by
  have e := walk_pre_straight σ [] z h
  rw [List.append_nil] at e
  rw [e, walk, Out.pre, List.append_nil]

/-- A branch between blocks of straight statements: its condition, then the block taken. -/
theorem walk1_ite_straight (σ : Val) (c : V) {z n : List Stmt}
    (hz : z.all Main.Stmt.straight = true) (hn : n.all Main.Stmt.straight = true) :
    walk1 σ (.ite c z n) = .fall (.inK c :: (if σ c = 0 then z else n).flatMap (Main.slEvs σ)) := by
  rw [walk1]
  by_cases hc : σ c = 0
  · simp only [hc, ↓reduceIte, walk_straight_fall σ hz, Out.pre, List.singleton_append]
  · simp only [hc, ↓reduceIte, walk_straight_fall σ hn, Out.pre, List.singleton_append]

/-- `__loop6`'s statements through `__loop36` and the pointers of the dispatched rounds. -/
def lyA : List Stmt := lyBody.take 62

/-- `__loop6`'s statements after the rounds, before its `ret`. -/
def lyB : List Stmt := lyPre.drop 65

/-- The callees of the dispatch on `parity = g^r`: `gkr_rounds__L{2r}`. -/
def lyFs : List String := ["gkr_rounds__L0", "gkr_rounds__L2", "gkr_rounds__L4", "gkr_rounds__L6"]

/-- The round at an odd depth. -/
def ly73 : List Stmt :=
  [.atom (.mul (.n 74) (.n 53) (.n 7)), .atom (.mul (.n 75) (.n 51) (.n 7)),
    .call "gkr_rounds__L1" [.n 74, .n 75] [.n 76]]

theorem lyBody_split : lyBody = lyA ++ (.dispatch (.n 63) lyFs [.n 70, .n 71] [.n 72] ::
    .atom (.add (.n 73) (.n 10) (.n 7)) :: .ite (.n 73) [] ly73 :: (lyB ++ [.ret []])) :=
  tbStmtsEqb_sound (by decide +kernel)

theorem lyA_straight : lyA.all Main.Stmt.straight = true := by decide +kernel
theorem lyB_straight : lyB.all Main.Stmt.straight = true := by decide +kernel
theorem ly73_straight : ly73.all Main.Stmt.straight = true := by decide +kernel

theorem lyA_calls : lyA.filterMap Main.Stmt.callS =
    [(some (.n 65), "__loop36", [.n 66, .n 62, .n 53, .n 51], [])] := by decide +kernel

theorem lyB_calls : lyB.filterMap Main.Stmt.callS =
    [(some (.n 344), "__loop6", [.n 346, .n 1, .n 2, .n 3, .n 4, .n 5, .n 6], [])] := by
  decide +kernel

theorem lyA_loads : lyA.all (loadsViaB [(8, 1), (16, 51), (53, 5173)]) = true := by decide +kernel

theorem lyB_loads : lyB.all (loadsViaB [(16, 51), (51, 42), (77, 5173), (83, 12), (337, 5),
    (340, 1)]) = true := by
  decide +kernel

/-- The events of a branch's block taken or not. -/
noncomputable def lyBr (σ : Val) (c : V) (z : List Stmt) : List Ev :=
  .inK c :: (if σ c = 0 then [] else z).flatMap (Main.slEvs σ)

/-- The dispatch's callee at `parity = g^r`. -/
def lyRn (r : ℕ) : String := lyFs.getD r ""

theorem walk1_dispatch (σ : Val) (x : V) (fs : List String) (args rets : List V) :
    walk1 σ (.dispatch x fs args rets) = pick σ x args rets 0 fs := by
  rw [walk1]

/-- **`__loop6`'s walk**, at `parity = g^r`: its statements in turn, the dispatch's callee
`gkr_rounds__L{2r}`, the odd round's block when taken. -/
theorem ly_walk (σ : Val) {r : ℕ} (hr : r < 4) (h63 : σ (.n 63) = ofK (addressOfIndex r)) :
    walk σ lyBody = .ret (lyA.flatMap (Main.slEvs σ) ++ [.call (lyRn r) [.n 70, .n 71] [.n 72]] ++
      (.atom (.add (.n 73) (.n 10) (.n 7)) :: lyBr σ (.n 73) ly73) ++ lyB.flatMap (Main.slEvs σ))
      [] := by
  have hp : pick σ (.n 63) [.n 70, .n 71] [.n 72] 0 lyFs =
      .fall [.call (lyRn r) [.n 70, .n 71] [.n 72]] := by
    rw [B1.pick_eq σ _ _ _ lyFs 0 r (by omega) (by simp [lyFs]; omega) (by omega) h63]
    interval_cases r <;> rfl
  rw [lyBody_split, walk_pre_straight σ _ lyA lyA_straight, walk, walk1_dispatch, hp, walk, walk,
    walk1_ite_straight σ _ rfl ly73_straight, Main.walk1_straight σ (.atom _) rfl,
    Main.walk_straight σ [] lyB lyB_straight]
  simp only [Out.seq, Out.pre, lyBr, Main.slEvs, List.append_assoc, List.cons_append,
    List.nil_append]

/-- A branch's block without loads loads nothing. -/
theorem loadAddrs_lyBr {σ : Val} {c : V} {z : List Stmt} (hs : z.all Main.Stmt.straight = true)
    (hl : z.filterMap Stmt.loadS = []) : loadAddrs σ (lyBr σ c z) = [] := by
  show loadAddrs σ ((if σ c = 0 then [] else z).flatMap (Main.slEvs σ)) = []
  by_cases hc : σ c = 0
  · simp only [hc, ↓reduceIte, List.flatMap_nil, loadAddrs, List.filterMap_nil]
  · simp only [hc, ↓reduceIte]
    rw [B1.loadAddrs_straight σ z hs, hl]; rfl

/-- A branch's frames: its block's, when taken. -/
theorem calls_lyBr {σ : Val} {c : V} {z : List Stmt} (hs : z.all Main.Stmt.straight = true) :
    calls (lyBr σ c z) = if σ c = 0 then [] else (z.filterMap Main.Stmt.callS).map (Main.mkCall σ) := by
  show calls ((if σ c = 0 then [] else z).flatMap (Main.slEvs σ)) = _
  by_cases hc : σ c = 0
  · simp only [hc, ↓reduceIte, List.flatMap_nil, calls, List.filterMap_nil]
  · simp only [hc, ↓reduceIte]
    exact (Main.straight_parts σ z hs).2.2.2

/-! ## The iterations -/

/-- **What iteration `j` reads, in `R`**: the slot of `L = 2j + sh` through the next slot's stores,
its row, position, `half` and `parity`; the round records from `rounds·pos`, record `r`'s cursor
`cj·g^(4r)`, and the words from `cj` the rounds and the children read. -/
def Ly7In (rd : Reader) (R : ℕ → Prop) (layers rounds : E) (sh j : ℕ) : Prop :=
  ∃ row pos cj : E,
    PtrIn R (layers * gen ^ (17 * (2 * j + sh))) 51 ∧
    LoadHolds rd layers (17 * (2 * j + sh) + 9) row ∧
    LoadHolds rd layers (17 * (2 * j + sh) + 10) pos ∧
    LoadHolds rd layers (17 * (2 * j + sh) + 11) (gen ^ (j / 4)) ∧
    LoadHolds rd layers (17 * (2 * j + sh) + 12) (gen ^ (j % 4)) ∧
    PtrIn R row (2 * j + sh + 42) ∧ PtrIn R (rounds * pos) (2 * j + sh + 5173) ∧
    PtrIn R cj (4 * (2 * j + sh) + 12) ∧
    ∀ r ≤ 2 * j + sh, LoadHolds rd (rounds * pos * gen ^ r) 4310 (cj * gen ^ (4 * r))

theorem tb_lName_gkr_rounds : lName "gkr_rounds" 0 = "gkr_rounds__L0" ∧
    lName "gkr_rounds" 1 = "gkr_rounds__L1" ∧ lName "gkr_rounds" 2 = "gkr_rounds__L2" ∧
    lName "gkr_rounds" 4 = "gkr_rounds__L4" ∧ lName "gkr_rounds" 6 = "gkr_rounds__L6" :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem lyRn_eq {r : ℕ} (hr : r < 4) : lyRn r = lName "gkr_rounds" (2 * r) ∧ 2 * r ∈ grCounts := by
  interval_cases r <;> exact ⟨rfl, by simp [grCounts]⟩

/-- **`__loop6` loads from `R`**, every iteration `j < m`, its slots, rows, records and cursors
in `R` (`Ly7In`), `depth_shift[g_bus_mu]` at `dsh·gmu`, holding `g^sh`, and the table
`k_mod_next` (`kmn`, `8` words) in `R`. -/
theorem loop7_relIn {rd : Reader} {R : ℕ → Prop} {dsh gmu layers rounds kmn : E} {sh m : ℕ}
    (hsh : LoadHolds rd (dsh * gmu) 0 (gen ^ sh)) (hshR : PtrIn R (dsh * gmu) 1)
    (hkR : PtrIn R kmn 8) (hit : ∀ j < m, Ly7In rd R layers rounds sh j) :
    ∀ d j, j < m →
      coreProgram.relN rd d "__loop6" [gen ^ j, gen ^ m, dsh, gmu, layers, rounds, kmn] [] →
      coreProgram.RelIn rd R "__loop6" [gen ^ j, gen ^ m, dsh, gmu, layers, rounds, kmn] [] := by
  intro d
  induction d with
  | zero => intro j _ h; exact h.elim
  | succ d ih =>
    intro j hj h
    obtain ⟨fn, hf, hsem⟩ := h
    obtain ⟨fn', hf', hpm, hb⟩ := lyFound
    rw [hf] at hf'
    obtain rfl := Option.some.inj hf'
    obtain ⟨row, pos, cj, hRL, hrow, hpos, hhalf, hpar, hRrow, hRrec, hRcur, hcur⟩ := hit j hj
    set L := 2 * j + sh with hL
    refine relIn_of_sem hf hsem fun σ hpar' hhl es vs hw ↦ ?_
    rw [hpm] at hpar'
    simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true] at hpar'
    obtain ⟨p0, p1, p2, p3, p4, p5, p6⟩ := hpar'
    rw [hb, lyBody_eq, holdsList_append, holdsList_noRet _ lyPre_noRet] at hhl
    have hP := hhl.1
    have hnr := lyPre_noRet
    have a := fun n a heq ↦ tb_holds_atom hnr hP n a heq
    have m7 := a 0 (.mul (.n 7) (.n 0) (.n 0)) (by decide +kernel)
    have m8 := a 1 (.mul (.n 8) (.n 2) (.n 3)) (by decide +kernel)
    have l9 := a 2 (.load (.n 9) (.n 8) 0) (by decide +kernel)
    have m10 := a 3 (.mul (.n 10) (.n 7) (.n 9)) (by decide +kernel)
    have m11 := a 4 (.mul (.n 11) (.n 10) (.n 10)) (by decide +kernel)
    have m12 := a 5 (.mul (.n 12) (.n 11) (.n 11)) (by decide +kernel)
    have m13 := a 6 (.mul (.n 13) (.n 12) (.n 12)) (by decide +kernel)
    have m14 := a 7 (.mul (.n 14) (.n 13) (.n 13)) (by decide +kernel)
    have m15 := a 8 (.mul (.n 15) (.n 14) (.n 10)) (by decide +kernel)
    have m16 := a 9 (.mul (.n 16) (.n 4) (.n 15)) (by decide +kernel)
    have l51 := a 33 (.load (.n 51) (.n 16) 9) (by decide +kernel)
    have l52 := a 34 (.load (.n 52) (.n 16) 10) (by decide +kernel)
    have m53 := a 35 (.mul (.n 53) (.n 5) (.n 52)) (by decide +kernel)
    have l62 := a 51 (.load (.n 62) (.n 16) 11) (by decide +kernel)
    have l63 := a 52 (.load (.n 63) (.n 16) 12) (by decide +kernel)
    have c64 := a 53 (.const (.n 64) (word 1 0 0)) (by decide +kernel)
    have a65 := a 54 (.add (.n 65) (.n 64) (.n 62)) (by decide +kernel)
    have c66 := a 55 (.const (.n 66) (word 1 0 0)) (by decide +kernel)
    have m67 := a 57 (.mul (.n 67) (.n 62) (.n 62)) (by decide +kernel)
    have m68 := a 58 (.mul (.n 68) (.n 67) (.n 67)) (by decide +kernel)
    have m69 := a 59 (.mul (.n 69) (.n 68) (.n 68)) (by decide +kernel)
    have m70 := a 60 (.mul (.n 70) (.n 53) (.n 69)) (by decide +kernel)
    have m71 := a 61 (.mul (.n 71) (.n 51) (.n 69)) (by decide +kernel)
    have a73 := a 63 (.add (.n 73) (.n 10) (.n 7)) (by decide +kernel)
    have m77 := a 65 (.mul (.n 77) (.n 53) (.n 10)) (by decide +kernel)
    have l83 := a 71 (.load (.n 83) (.n 77) 4310) (by decide +kernel)
    have m337 := a 285 (.mul (.n 337) (.n 6) (.n 63)) (by decide +kernel)
    have m340 := a 289 (.mul (.n 340) (.n 6) (.n 63)) (by decide +kernel)
    have c342 := a 292 (.const (.n 342) (word 2 0 0)) (by decide +kernel)
    have m343 := a 293 (.mul (.n 343) (.n 0) (.n 342)) (by decide +kernel)
    have a344 := a 294 (.add (.n 344) (.n 343) (.n 1)) (by decide +kernel)
    have c345 := a 295 (.const (.n 345) (word 2 0 0)) (by decide +kernel)
    have m346 := a 296 (.mul (.n 346) (.n 0) (.n 345)) (by decide +kernel)
    simp only [Atom.Holds] at m7 m8 l9 m10 m11 m12 m13 m14 m15 m16 l51 l52 m53 l62 l63
    simp only [Atom.Holds] at c64 a65 c66 m67 m68 m69 m70 m71 a73 m77 l83 m337 m340
    simp only [Atom.Holds] at c342 m343 a344 c345 m346
    rw [tb_word_one] at c64 c66
    rw [tb_word_gen] at c342 c345
    rw [m8, p2, p3] at l9
    have e9 := tb_loadHolds_unique l9 hsh
    have e7 : σ (.n 7) = gen ^ (2 * j) := by rw [m7, p0, ← pow_add]; ring_nf
    have e10 : σ (.n 10) = gen ^ L := by rw [m10, e7, e9, hL, pow_add]
    have e16 : σ (.n 16) = layers * gen ^ (17 * L) := by
      rw [m16, m15, m14, m13, m12, m11, e10, p4, ← pow_add, ← pow_add, ← pow_add, ← pow_add]
      ring_nf
    have ld : ∀ k w, LoadHolds rd (σ (.n 16)) k w → LoadHolds rd layers (17 * L + k) w := by
      intro k w h; rwa [e16, tb_loadHolds_mul_gen_pow] at h
    have e51 := tb_loadHolds_unique (ld _ _ l51) hrow
    have e52 := tb_loadHolds_unique (ld _ _ l52) hpos
    have e62 := tb_loadHolds_unique (ld _ _ l62) hhalf
    have e63 := tb_loadHolds_unique (ld _ _ l63) hpar
    have e53 : σ (.n 53) = rounds * pos := by rw [m53, p5, e52]
    have e77 : σ (.n 77) = rounds * pos * gen ^ L := by rw [m77, e53, e10]
    have e69 : σ (.n 69) = gen ^ (8 * (j / 4)) := by
      rw [m69, m68, m67, e62, ← pow_add, ← pow_add, ← pow_add]; ring_nf
    rw [e77] at l83
    have e83 := tb_loadHolds_unique l83 (hcur L le_rfl)
    have hr4 : j % 4 < 4 := Nat.mod_lt _ (by omega)
    have h63 : σ (.n 63) = ofK (addressOfIndex (j % 4)) := by rw [e63, gen_pow_eq_ofK]
    -- a record's cursor
    have hcurIn : ∀ r B, 4 * r + B ≤ 4 * L + 12 → r ≤ L → ∀ c,
        LoadHolds rd (rounds * pos * gen ^ r) 4310 c → PtrIn R c B := by
      intro r B hB hr c hc
      rw [tb_loadHolds_unique hc (hcur r hr)]
      exact ptrIn_mul (ptrIn_mono hRcur hB)
    rw [hb, ly_walk σ hr4 h63] at hw
    injection hw with hes _
    subst hes
    refine ⟨fun A hA ↦ ?_, fun c hc ht ↦ ?_⟩
    · -- the loads
      rw [loadAddrs_append, loadAddrs_append, loadAddrs_append,
        show loadAddrs σ [.call (lyRn (j % 4)) [.n 70, .n 71] [.n 72]] = [] from rfl,
        show loadAddrs σ (.atom (.add (.n 73) (.n 10) (.n 7)) :: lyBr σ (.n 73) ly73) =
          loadAddrs σ (lyBr σ (.n 73) ly73) from rfl,
        loadAddrs_lyBr ly73_straight (by decide +kernel), B1.loadAddrs_straight σ lyA lyA_straight,
        B1.loadAddrs_straight σ lyB lyB_straight] at hA
      simp only [List.append_nil, List.mem_append, List.mem_map] at hA
      rcases hA with ⟨q, hq, rfl⟩ | ⟨q, hq, rfl⟩
      · refine loads_via lyA_loads (fun pb hpb ↦ ?_) q hq
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hpb
        rcases hpb with rfl | rfl | rfl
        · rw [m8, p2, p3]; exact hshR
        · rw [e16]; exact hRL
        · rw [e53]; exact ptrIn_mono hRrec (by omega)
      · refine loads_via lyB_loads (fun pb hpb ↦ ?_) q hq
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hpb
        rcases hpb with rfl | rfl | rfl | rfl | rfl | rfl
        · rw [e16]; exact hRL
        · rw [e51]; exact ptrIn_mono hRrow (by omega)
        · rw [e77]; exact ptrIn_mul hRrec
        · rw [e83]; exact ptrIn_mul hRcur
        · rw [m337, p6, e63]; exact ptrIn_mul (ptrIn_mono hkR (by omega))
        · rw [m340, p6, e63]; exact ptrIn_mul (ptrIn_mono hkR (by omega))
    · -- the calls
      rw [calls_append, calls_append, calls_append,
        show calls [.call (lyRn (j % 4)) [.n 70, .n 71] [.n 72]] =
          [⟨lyRn (j % 4), [.n 70, .n 71], [.n 72], true⟩] from rfl,
        show calls (.atom (.add (.n 73) (.n 10) (.n 7)) :: lyBr σ (.n 73) ly73) =
          calls (lyBr σ (.n 73) ly73) from rfl,
        calls_lyBr ly73_straight, (Main.straight_parts σ lyA lyA_straight).2.2.2,
        (Main.straight_parts σ lyB lyB_straight).2.2.2, lyA_calls, lyB_calls] at hc
      simp only [List.mem_append] at hc
      rcases hc with ((hc | hc) | hc) | hc
      · -- `__loop36`
        simp only [List.map_cons, List.map_nil, List.mem_singleton] at hc
        subst hc
        simp only [Main.mkCall, decide_eq_true_eq] at ht ⊢
        have hci := tb_holds_callIf hnr hP 56 (.n 65) "__loop36" [.n 66, .n 62, .n 53, .n 51]
          (by decide +kernel)
        have hrel := hci.2 ht
        have hK : 0 < j / 4 := by
          rcases Nat.eq_zero_or_pos (j / 4) with h0 | h0
          · exfalso; apply ht
            rw [a65, c64, e62, h0, pow_zero, e_add_self]
          · exact h0
        simp only [List.map_cons, List.map_nil, c66, e62, e53, e51] at hrel ⊢
        rw [show (1 : E) = gen ^ 0 from (pow_zero _).symm] at hrel ⊢
        exact loop29_relIn (ptrIn_mono hRrec (by omega)) (ptrIn_mono hRrow (by omega))
          (fun k hk c hc ↦ hcurIn (8 * k) 32 (by omega) (by omega) c hc) d 0 hK hrel
      · -- `gkr_rounds__L{2r}`, `r = j % 4`
        simp only [List.mem_singleton] at hc
        subst hc
        have hdi := tb_holds_slice hnr hP 62 [.dispatch (.n 63) lyFs [.n 70, .n 71] [.n 72]]
          (by decide +kernel)
        simp only [Stmt.HoldsList, Stmt.Holds] at hdi
        obtain ⟨⟨i, hi, hx, hrel⟩, -⟩ := hdi
        have hij : i = j % 4 := by
          have hi4 : i < 4 := by simpa [lyFs] using hi
          rw [h63, ← gen_pow_eq_ofK, ← gen_pow_eq_ofK] at hx
          exact (gen_pow_inj (by omega) (by omega) hx).symm
        subst hij
        obtain ⟨hnm, hcn⟩ := lyRn_eq hr4
        have hfs : lyFs[j % 4] = lyRn (j % 4) := by
          simp only [lyRn, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, Option.getD_some]
        rw [hfs, hnm] at hrel
        simp only [List.map_cons, List.map_nil, m70, m71, e69, e53, e51] at hrel
        simp only [List.map_cons, List.map_nil, m70, m71, e69, e53, e51, hnm]
        exact gkr_rounds_relIn hcn (ptrIn_mul (ptrIn_mono hRrec (by omega)))
          (ptrIn_mul (ptrIn_mono hRrow (by omega)))
          (hcurIn (8 * (j / 4)) (4 * (2 * (j % 4))) (by omega) (by omega)) ⟨d, hrel⟩
      · -- `gkr_rounds__L1`
        split at hc
        · simp at hc
        rename_i h73
        rw [show ly73.filterMap Main.Stmt.callS =
          [(none, "gkr_rounds__L1", [.n 74, .n 75], [.n 76])] by decide +kernel] at hc
        simp only [List.map_cons, List.map_nil, List.mem_singleton] at hc
        subst hc
        have hsh1 : 1 ≤ sh := by
          by_contra h0
          apply h73
          rw [a73, e10, e7, show L = 2 * j by omega, e_add_self]
        have hi := tb_holds_slice hnr hP 64 [.ite (.n 73) [] ly73] (by decide +kernel)
        have hbr := hi.2.2 h73
        simp only [Stmt.HoldsList, Stmt.Holds, ly73, Atom.Holds, List.map_cons, List.map_nil,
          and_true] at hbr
        obtain ⟨m74, m75, hrel⟩ := hbr
        simp only [Main.mkCall, List.map_cons, List.map_nil]
        rw [m74, m75, e7, e53, e51] at hrel ⊢
        rw [← tb_lName_gkr_rounds.2.1] at hrel ⊢
        exact gkr_rounds_relIn (by simp [grCounts]) (ptrIn_mul (ptrIn_mono hRrec (by omega)))
          (ptrIn_mul (ptrIn_mono hRrow (by omega)))
          (hcurIn (2 * j) (4 * 1) (by omega) (by omega)) ⟨d, hrel⟩
      · -- the next iteration
        simp only [List.map_cons, List.map_nil, List.mem_singleton] at hc
        subst hc
        simp only [Main.mkCall, decide_eq_true_eq] at ht ⊢
        have hci := tb_holds_callIf hnr hP 297 (.n 344) "__loop6"
          [.n 346, .n 1, .n 2, .n 3, .n 4, .n 5, .n 6] (by decide +kernel)
        have hrel := hci.2 ht
        have e346 : σ (.n 346) = gen ^ (j + 1) := by rw [m346, c345, p0, pow_succ]
        have e344 : σ (.n 344) = gen ^ (j + 1) + gen ^ m := by
          rw [a344, m343, c342, p0, p1, pow_succ]
        have hj1 : j + 1 < m := by
          rcases Nat.lt_or_ge (j + 1) m with h' | h'
          · exact h'
          · exfalso
            apply ht
            rw [e344, show j + 1 = m by omega, e_add_eq_zero_iff]
        simp only [List.map_cons, List.map_nil, e346, p1, p2, p3, p4, p5, p6] at hrel ⊢
        exact ih (j + 1) hj1 hrel

end
end LeanVM.Guest.B1.Tables
