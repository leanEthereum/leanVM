/-
  LeanVM.Guest.B1.Gkr.Loop7In

  `verify_bus_gkr_loop0` loads from any region holding, at each iteration, its layer slot, its row,
  its round records and the words at the records' cursors.
-/

module

public import LeanVM.Guest.B1.Gkr.Layer
public import LeanVM.Guest.B1.Gkr.RoundsIn
public import LeanVM.Guest.Data.NameStrings

/-!
# `verify_bus_gkr_loop0`, loading from a region

`verify_bus_gkr_loop0`'s body is straight but for a dispatch on its `parity = g^r`
(`gkr_rounds__L{2r}`) and a branch of straight statements ending in `gkr_rounds__L1` at an odd
depth: it walks its statements in turn, the dispatch's callee and the branch's block when taken
(`ly_walk`).

* `Ly7In`: what iteration `j` reads, in `R`: the slot of `L = 2j + 2 - sh` (`39` words, through
  the next slot's stores), its row (`L + 42` words), position, `half = g^(k/4)` and
  `parity = g^(k % 4)`, `k = j + 1 - sh`; the records from `rounds·pos` (`L + 5173` words),
  record `r`'s cursor `cj·g^(4r)`, the `4L + 12` words from `cj`.
* `loop7_relIn`: with those at every `j < m` and the table `k_mod_next` (`8` words) in `R`,
  iteration `j < m` of `verify_bus_gkr_loop0` loads from `R`, by the depth of its derivation; its
  rounds by `loop29_relIn` and `gkr_rounds_relIn`.
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

/-- `verify_bus_gkr_loop0`'s statements through `verify_bus_gkr_loop0_loop0` and the pointers of the
dispatched rounds. -/
noncomputable def lyA : List Stmt := lyBody.take 49

/-- `verify_bus_gkr_loop0`'s statements after the rounds, before its `ret`. -/
noncomputable def lyB : List Stmt := lyPre.drop 53

/-- The callees of the dispatch on `parity = g^r`: `gkr_rounds__L{2r}`. -/
def lyFs : List String := ["gkr_rounds__L0", "gkr_rounds__L2", "gkr_rounds__L4", "gkr_rounds__L6"]

/-- The round at an odd depth. -/
def ly73 : List Stmt :=
  [.atom (.mul (.n 66) (.n 48) (.n 10)), .atom (.mul (.n 67) (.n 46) (.n 10)),
    .call "gkr_rounds__L1" [.n 66, .n 67, .n 4] [.n 68]]

theorem lyBody_split : lyBody = lyA ++ (.dispatch (.n 54) lyFs [.n 61, .n 62, .n 4] [.n 63] ::
    .atom (.const (.n 64) (word 1 0)) :: .atom (.add (.n 65) (.n 7) (.n 64)) ::
    .ite (.n 65) [] ly73 :: (lyB ++ [.ret []])) :=
  tbStmtsEqb_sound (by decide +kernel)

theorem lyA_straight : lyA.all Main.Stmt.straight = true := by decide +kernel
theorem lyB_straight : lyB.all Main.Stmt.straight = true := by decide +kernel
theorem ly73_straight : ly73.all Main.Stmt.straight = true := by decide +kernel

theorem lyA_calls : lyA.filterMap Main.Stmt.callS =
    [(some (.n 56), name% «verify_bus_gkr_loop0_loop0», [.n 57, .n 53, .n 48, .n 46, .n 4],
        [])] := by decide +kernel

theorem lyB_calls : lyB.filterMap Main.Stmt.callS =
    [(some (.n 236), name% «verify_bus_gkr_loop0», [.n 238, .n 1, .n 2, .n 3, .n 4, .n 5, .n 6,
        .n 7, .n 8, .n 9],
      [])] := by
  decide +kernel

theorem lyA_loads : lyA.all (loadsViaB [(17, 39), (48, 5173)]) = true := by decide +kernel

theorem lyB_loads : lyB.all (loadsViaB [(17, 39), (46, 42), (69, 5173), (75, 12), (229, 5),
    (232, 1)]) = true := by
  decide +kernel

/-- The events of a branch's block taken or not. -/
noncomputable def lyBr (σ : Val) (c : V) (z : List Stmt) : List Ev :=
  .inK c :: (if σ c = 0 then [] else z).flatMap (Main.slEvs σ)

/-- The dispatch's callee at `parity = g^r`. -/
def lyRn (r : ℕ) : String := lyFs.getD r ""

theorem walk1_dispatch (σ : Val) (x : V) (fs : List String) (args rets : List V) :
    walk1 σ (.dispatch x fs args rets) = pick σ x args rets 0 fs := by
  rw [walk1]

/-- **`verify_bus_gkr_loop0`'s walk**, at `parity = g^r`: its statements in turn, the dispatch's
callee
`gkr_rounds__L{2r}`, the odd round's block when taken. -/
theorem ly_walk (σ : Val) {r : ℕ} (hr : r < 4) (h54 : σ (.n 54) = ofK (addressOfIndex r)) :
    walk σ lyBody = .ret (lyA.flatMap (Main.slEvs σ) ++
      [.call (lyRn r) [.n 61, .n 62, .n 4] [.n 63]] ++
      (.atom (.const (.n 64) (word 1 0)) :: .atom (.add (.n 65) (.n 7) (.n 64)) ::
        lyBr σ (.n 65) ly73) ++ lyB.flatMap (Main.slEvs σ)) [] := by
  have hp : pick σ (.n 54) [.n 61, .n 62, .n 4] [.n 63] 0 lyFs =
      .fall [.call (lyRn r) [.n 61, .n 62, .n 4] [.n 63]] := by
    rw [B1.pick_eq σ _ _ _ lyFs 0 r (by omega) (by simp [lyFs]; omega) (by omega) h54]
    interval_cases r <;> rfl
  rw [lyBody_split, walk_pre_straight σ _ lyA lyA_straight, walk, walk1_dispatch, hp, walk, walk,
    walk, Main.walk1_straight σ (.atom _) rfl, Main.walk1_straight σ (.atom _) rfl,
    walk1_ite_straight σ _ rfl ly73_straight, Main.walk_straight σ [] lyB lyB_straight]
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

/-- **What iteration `j` reads, in `R`**: the slot of `L = 2j + 2 - sh` through the next slot's
stores, its row, position, `half` and `parity`; the round records from `rounds·pos`, record `r`'s
cursor `cj·g^(4r)`, and the words from `cj` the rounds and the children read. -/
def Ly7In (rd : Reader) (R : ℕ → Prop) (layers rounds : E) (sh j : ℕ) : Prop :=
  ∃ row pos cj : E,
    PtrIn R (layers * gen ^ (13 * (2 * j + 2 - sh))) 39 ∧
    LoadHolds rd layers (13 * (2 * j + 2 - sh) + 9) row ∧
    LoadHolds rd layers (13 * (2 * j + 2 - sh) + 10) pos ∧
    LoadHolds rd layers (13 * (2 * j + 2 - sh) + 11) (gen ^ ((j + 1 - sh) / 4)) ∧
    LoadHolds rd layers (13 * (2 * j + 2 - sh) + 12) (gen ^ ((j + 1 - sh) % 4)) ∧
    PtrIn R row (2 * j + 2 - sh + 42) ∧ PtrIn R (rounds * pos) (2 * j + 2 - sh + 5173) ∧
    PtrIn R cj (4 * (2 * j + 2 - sh) + 12) ∧
    ∀ r ≤ 2 * j + 2 - sh, LoadHolds rd (rounds * pos * gen ^ r) 4310 (cj * gen ^ (4 * r))

theorem tb_lName_gkr_rounds : lName "gkr_rounds" 0 = "gkr_rounds__L0" ∧
    lName "gkr_rounds" 1 = "gkr_rounds__L1" ∧ lName "gkr_rounds" 2 = "gkr_rounds__L2" ∧
    lName "gkr_rounds" 4 = "gkr_rounds__L4" ∧ lName "gkr_rounds" 6 = "gkr_rounds__L6" :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem lyRn_eq {r : ℕ} (hr : r < 4) : lyRn r = lName "gkr_rounds" (2 * r) ∧ 2 * r ∈ grCounts := by
  interval_cases r <;> exact ⟨rfl, by simp [grCounts]⟩

/-- **`verify_bus_gkr_loop0` loads from `R`**, every iteration `j < m`, its slots, rows, records and
cursors
in `R` (`Ly7In`), and the table `k_mod_next` (`kmn`, `8` words) in `R`. -/
theorem loop7_relIn {rd : Reader} {R : ℕ → Prop} {layers tabs rounds claim gmu kmn : E}
    {sh m : ℕ} (hsh2 : sh < 2) (hkR : PtrIn R kmn 8)
    (hit : ∀ j < m, Ly7In rd R layers rounds sh j) :
    ∀ d j, j < m →
      coreProgram.relN rd d name% «verify_bus_gkr_loop0» [gen ^ j, gen ^ m, gen ^ (2 - sh), layers,
          tabs, rounds,
        claim, gen ^ sh, gmu, kmn] [] →
      coreProgram.RelIn rd R name% «verify_bus_gkr_loop0» [gen ^ j, gen ^ m, gen ^ (2 - sh),
          layers, tabs, rounds,
        claim, gen ^ sh, gmu, kmn] [] := by
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
    set L := 2 * j + 2 - sh with hL
    set k := j + 1 - sh with hk
    refine relIn_of_sem hf hsem fun σ hpar' hhl es vs hw ↦ ?_
    rw [hpm] at hpar'
    have hpar'' : [σ (.n 0), σ (.n 1), σ (.n 2), σ (.n 3), σ (.n 4), σ (.n 5), σ (.n 6), σ (.n 7),
        σ (.n 8), σ (.n 9)] = [gen ^ j, gen ^ m, gen ^ (2 - sh), layers, tabs, rounds, claim,
        gen ^ sh, gmu, kmn] := hpar'
    simp only [List.cons.injEq, and_true] at hpar''
    obtain ⟨p0, p1, p2, p3, p4, p5, p6, p7, p8, p9⟩ := hpar''
    rw [hb, lyBody_eq, holdsList_append, holdsList_noRet _ lyPre_noRet] at hhl
    have hP := hhl.1
    have hnr := lyPre_noRet
    have a := fun n a heq ↦ tb_holds_atom hnr hP n a heq
    have m10 := a 0 (.mul (.n 10) (.n 0) (.n 0)) (by decide +kernel)
    have m11 := a 1 (.mul (.n 11) (.n 10) (.n 2)) (by decide +kernel)
    have m12 := a 2 (.mul (.n 12) (.n 11) (.n 11)) (by decide +kernel)
    have m13 := a 3 (.mul (.n 13) (.n 12) (.n 11)) (by decide +kernel)
    have m14 := a 4 (.mul (.n 14) (.n 13) (.n 13)) (by decide +kernel)
    have m15 := a 5 (.mul (.n 15) (.n 14) (.n 14)) (by decide +kernel)
    have m16 := a 6 (.mul (.n 16) (.n 15) (.n 11)) (by decide +kernel)
    have m17 := a 7 (.mul (.n 17) (.n 3) (.n 16)) (by decide +kernel)
    have l46 := a 24 (.load (.n 46) (.n 17) 9) (by decide +kernel)
    have l47 := a 25 (.load (.n 47) (.n 17) 10) (by decide +kernel)
    have m48 := a 26 (.mul (.n 48) (.n 5) (.n 47)) (by decide +kernel)
    have l53 := a 38 (.load (.n 53) (.n 17) 11) (by decide +kernel)
    have l54 := a 39 (.load (.n 54) (.n 17) 12) (by decide +kernel)
    have c55 := a 40 (.const (.n 55) (word 1 0)) (by decide +kernel)
    have a56 := a 41 (.add (.n 56) (.n 55) (.n 53)) (by decide +kernel)
    have c57 := a 42 (.const (.n 57) (word 1 0)) (by decide +kernel)
    have m58 := a 44 (.mul (.n 58) (.n 53) (.n 53)) (by decide +kernel)
    have m59 := a 45 (.mul (.n 59) (.n 58) (.n 58)) (by decide +kernel)
    have m60 := a 46 (.mul (.n 60) (.n 59) (.n 59)) (by decide +kernel)
    have m61 := a 47 (.mul (.n 61) (.n 48) (.n 60)) (by decide +kernel)
    have m62 := a 48 (.mul (.n 62) (.n 46) (.n 60)) (by decide +kernel)
    have c64 := a 50 (.const (.n 64) (word 1 0)) (by decide +kernel)
    have a65 := a 51 (.add (.n 65) (.n 7) (.n 64)) (by decide +kernel)
    have m69 := a 53 (.mul (.n 69) (.n 48) (.n 11)) (by decide +kernel)
    have l75 := a 59 (.load (.n 75) (.n 69) 4310) (by decide +kernel)
    have m229 := a 179 (.mul (.n 229) (.n 9) (.n 54)) (by decide +kernel)
    have m232 := a 183 (.mul (.n 232) (.n 9) (.n 54)) (by decide +kernel)
    have c234 := a 186 (.const (.n 234) (word 2 0)) (by decide +kernel)
    have m235 := a 187 (.mul (.n 235) (.n 0) (.n 234)) (by decide +kernel)
    have a236 := a 188 (.add (.n 236) (.n 235) (.n 1)) (by decide +kernel)
    have c237 := a 189 (.const (.n 237) (word 2 0)) (by decide +kernel)
    have m238 := a 190 (.mul (.n 238) (.n 0) (.n 237)) (by decide +kernel)
    simp only [Atom.Holds] at m10 m11 m12 m13 m14 m15 m16 m17 l46 l47 m48 l53 l54
    simp only [Atom.Holds] at c55 a56 c57 m58 m59 m60 m61 m62 c64 a65 m69 l75 m229 m232
    simp only [Atom.Holds] at c234 m235 a236 c237 m238
    rw [tb_word_one] at c55 c57 c64
    rw [tb_word_gen] at c234 c237
    have e10 : σ (.n 10) = gen ^ (2 * j) := by rw [m10, p0, ← pow_add]; ring_nf
    have e11 : σ (.n 11) = gen ^ L := by
      rw [m11, e10, p2, ← pow_add, show 2 * j + (2 - sh) = L by omega]
    have e17 : σ (.n 17) = layers * gen ^ (13 * L) := by
      rw [m17, m16, m15, m14, m13, m12, e11, p3, ← pow_add, ← pow_add, ← pow_add, ← pow_add,
        ← pow_add]
      ring_nf
    have ld : ∀ k w, LoadHolds rd (σ (.n 17)) k w → LoadHolds rd layers (13 * L + k) w := by
      intro k w h; rwa [e17, tb_loadHolds_mul_gen_pow] at h
    have e46 := tb_loadHolds_unique (ld _ _ l46) hrow
    have e47 := tb_loadHolds_unique (ld _ _ l47) hpos
    have e53 := tb_loadHolds_unique (ld _ _ l53) hhalf
    have e54 := tb_loadHolds_unique (ld _ _ l54) hpar
    have e48 : σ (.n 48) = rounds * pos := by rw [m48, p5, e47]
    have e69 : σ (.n 69) = rounds * pos * gen ^ L := by rw [m69, e48, e11]
    have e60 : σ (.n 60) = gen ^ (8 * (k / 4)) := by
      rw [m60, m59, m58, e53, ← pow_add, ← pow_add, ← pow_add]; ring_nf
    rw [e69] at l75
    have e75 := tb_loadHolds_unique l75 (hcur L le_rfl)
    have hr4 : k % 4 < 4 := Nat.mod_lt _ (by omega)
    have h54 : σ (.n 54) = ofK (addressOfIndex (k % 4)) := by rw [e54, gen_pow_eq_ofK]
    -- a record's cursor
    have hcurIn : ∀ r B, 4 * r + B ≤ 4 * L + 12 → r ≤ L → ∀ c,
        LoadHolds rd (rounds * pos * gen ^ r) 4310 c → PtrIn R c B := by
      intro r B hB hr c hc
      rw [tb_loadHolds_unique hc (hcur r hr)]
      exact ptrIn_mul (ptrIn_mono hRcur hB)
    rw [hb, ly_walk σ hr4 h54] at hw
    injection hw with hes _
    subst hes
    refine ⟨fun A hA ↦ ?_, fun c hc ht ↦ ?_⟩
    · -- the loads
      rw [loadAddrs_append, loadAddrs_append, loadAddrs_append,
        show loadAddrs σ [.call (lyRn (k % 4)) [.n 61, .n 62, .n 4] [.n 63]] = [] from rfl,
        show loadAddrs σ (.atom (.const (.n 64) (word 1 0)) :: .atom (.add (.n 65) (.n 7) (.n 64)) ::
          lyBr σ (.n 65) ly73) = loadAddrs σ (lyBr σ (.n 65) ly73) from rfl,
        loadAddrs_lyBr ly73_straight (by decide +kernel), B1.loadAddrs_straight σ lyA lyA_straight,
        B1.loadAddrs_straight σ lyB lyB_straight] at hA
      simp only [List.append_nil, List.mem_append, List.mem_map] at hA
      rcases hA with ⟨q, hq, rfl⟩ | ⟨q, hq, rfl⟩
      · refine loads_via lyA_loads (fun pb hpb ↦ ?_) q hq
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hpb
        rcases hpb with rfl | rfl
        · rw [e17]; exact hRL
        · rw [e48]; exact ptrIn_mono hRrec (by omega)
      · refine loads_via lyB_loads (fun pb hpb ↦ ?_) q hq
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hpb
        rcases hpb with rfl | rfl | rfl | rfl | rfl | rfl
        · rw [e17]; exact hRL
        · rw [e46]; exact ptrIn_mono hRrow (by omega)
        · rw [e69]; exact ptrIn_mul hRrec
        · rw [e75]; exact ptrIn_mul hRcur
        · rw [m229, p9, e54]; exact ptrIn_mul (ptrIn_mono hkR (by omega))
        · rw [m232, p9, e54]; exact ptrIn_mul (ptrIn_mono hkR (by omega))
    · -- the calls
      rw [calls_append, calls_append, calls_append,
        show calls [.call (lyRn (k % 4)) [.n 61, .n 62, .n 4] [.n 63]] =
          [⟨lyRn (k % 4), [.n 61, .n 62, .n 4], [.n 63], true⟩] from rfl,
        show calls (.atom (.const (.n 64) (word 1 0)) :: .atom (.add (.n 65) (.n 7) (.n 64)) ::
          lyBr σ (.n 65) ly73) = calls (lyBr σ (.n 65) ly73) from rfl,
        calls_lyBr ly73_straight, (Main.straight_parts σ lyA lyA_straight).2.2.2,
        (Main.straight_parts σ lyB lyB_straight).2.2.2, lyA_calls, lyB_calls] at hc
      simp only [List.mem_append] at hc
      rcases hc with ((hc | hc) | hc) | hc
      · -- `verify_bus_gkr_loop0_loop0`
        simp only [List.map_cons, List.map_nil, List.mem_singleton] at hc
        subst hc
        simp only [Main.mkCall, decide_eq_true_eq] at ht ⊢
        have hci := tb_holds_callIf hnr hP 43 (.n 56) name% «verify_bus_gkr_loop0_loop0»
          [.n 57, .n 53, .n 48, .n 46, .n 4] (by decide +kernel)
        have hrel := hci.2 ht
        have hK : 0 < k / 4 := by
          rcases Nat.eq_zero_or_pos (k / 4) with h0 | h0
          · exfalso; apply ht
            rw [a56, c55, e53, h0, pow_zero, e_add_self]
          · exact h0
        simp only [List.map_cons, List.map_nil, c57, e53, e48, e46, p4] at hrel ⊢
        rw [show (1 : E) = gen ^ 0 from (pow_zero _).symm] at hrel ⊢
        exact loop29_relIn (ptrIn_mono hRrec (by omega)) (ptrIn_mono hRrow (by omega))
          (fun k' hk' c hc ↦ hcurIn (8 * k') 32 (by omega) (by omega) c hc) d 0 hK hrel
      · -- `gkr_rounds__L{2r}`, `r = k % 4`
        simp only [List.mem_singleton] at hc
        subst hc
        have hdi := tb_holds_slice hnr hP 49
          [.dispatch (.n 54) lyFs [.n 61, .n 62, .n 4] [.n 63]] (by decide +kernel)
        simp only [Stmt.HoldsList, Stmt.Holds] at hdi
        obtain ⟨⟨i, hi, hx, hrel⟩, -⟩ := hdi
        have hij : i = k % 4 := by
          have hi4 : i < 4 := by simpa [lyFs] using hi
          rw [h54, ← gen_pow_eq_ofK, ← gen_pow_eq_ofK] at hx
          exact (gen_pow_inj (by omega) (by omega) hx).symm
        subst hij
        obtain ⟨hnm, hcn⟩ := lyRn_eq hr4
        have hfs : lyFs[k % 4] = lyRn (k % 4) := by
          simp only [lyRn, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi,
            Option.getD_some]
        rw [hfs, hnm] at hrel
        simp only [List.map_cons, List.map_nil, m61, m62, e60, e48, e46, p4] at hrel
        simp only [List.map_cons, List.map_nil, m61, m62, e60, e48, e46, p4, hnm]
        exact gkr_rounds_relIn hcn (ptrIn_mul (ptrIn_mono hRrec (by omega)))
          (ptrIn_mul (ptrIn_mono hRrow (by omega)))
          (hcurIn (8 * (k / 4)) (4 * (2 * (k % 4))) (by omega) (by omega)) ⟨d, hrel⟩
      · -- `gkr_rounds__L1`
        split at hc
        · simp at hc
        rename_i h65
        rw [show ly73.filterMap Main.Stmt.callS =
          [(none, "gkr_rounds__L1", [.n 66, .n 67, .n 4], [.n 68])] by decide +kernel] at hc
        simp only [List.map_cons, List.map_nil, List.mem_singleton] at hc
        subst hc
        have hsh1 : sh = 1 := by
          by_contra h0
          apply h65
          rw [a65, c64, p7, show sh = 0 by omega, pow_zero, e_add_self]
        have hi := tb_holds_slice hnr hP 52 [.ite (.n 65) [] ly73] (by decide +kernel)
        have hbr := hi.2.2 h65
        simp only [Stmt.HoldsList, Stmt.Holds, ly73, Atom.Holds, List.map_cons, List.map_nil,
          and_true] at hbr
        obtain ⟨m66, m67, hrel⟩ := hbr
        simp only [Main.mkCall, List.map_cons, List.map_nil]
        rw [m66, m67, e10, e48, e46, p4] at hrel ⊢
        rw [← tb_lName_gkr_rounds.2.1] at hrel ⊢
        exact gkr_rounds_relIn (by simp [grCounts]) (ptrIn_mul (ptrIn_mono hRrec (by omega)))
          (ptrIn_mul (ptrIn_mono hRrow (by omega)))
          (hcurIn (2 * j) (4 * 1) (by omega) (by omega)) ⟨d, hrel⟩
      · -- the next iteration
        simp only [List.map_cons, List.map_nil, List.mem_singleton] at hc
        subst hc
        simp only [Main.mkCall, decide_eq_true_eq] at ht ⊢
        have hci := tb_holds_callIf hnr hP 191 (.n 236) name% «verify_bus_gkr_loop0»
          [.n 238, .n 1, .n 2, .n 3, .n 4, .n 5, .n 6, .n 7, .n 8, .n 9] (by decide +kernel)
        have hrel := hci.2 ht
        have e238 : σ (.n 238) = gen ^ (j + 1) := by rw [m238, c237, p0, pow_succ]
        have e236 : σ (.n 236) = gen ^ (j + 1) + gen ^ m := by
          rw [a236, m235, c234, p0, p1, pow_succ]
        have hj1 : j + 1 < m := by
          rcases Nat.lt_or_ge (j + 1) m with h' | h'
          · exact h'
          · exfalso
            apply ht
            rw [e236, show j + 1 = m by omega, e_add_eq_zero_iff]
        simp only [List.map_cons, List.map_nil, e238, p1, p2, p3, p4, p5, p6, p7, p8, p9]
          at hrel ⊢
        exact ih (j + 1) hj1 hrel

end
end LeanVM.Guest.B1.Tables
