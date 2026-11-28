module

public import LeanVM.Guest.Complete.DaVecA
public import LeanVM.Guest.B1.Da.VerifyChk
import LeanVM.Guest.CoreRef
import LeanVM.Guest.ValRef
import LeanVM.Guest.Data.ValNames.«da_weights»

/-!
# `da_weights`, placed

`da_weights(top_leaves, cell_factors, zs, offsets)` at frame `fp` and cursor `c`: its `HeapBuf`
`weights` (`128` words at `c`, column `h`'s pointer `g^(bcol h + 128)`, `wsTable`) its own words;
its `128` calls of `da_expand__L6_L7` one after another from `c + 128` (`wsCur`), column `h`'s at
the aligned base of the cursor, its run at `bcol h` (`expCell_callAtA`) on the top tree's leaf
`h`, the cell factors, the powers and the offsets moved by `g^(7h)`; by induction on the columns
(`ws_kids`). The body is the template `wsPre` (`ws_cok`, by the kernel), the valuation explicit
(`wsVals`). `daWeightsCompleteA`: `DaWeightsCompleteA` wherever a cell tree's run lies in its frame.
-/

namespace LeanVM.Guest.Complete

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Memory LeanVM.Guest.B1
open LeanVM.Guest.B1.Da LeanVM.Guest.B1.Digest LeanVM.Guest.B1.Fwd
open LeanVM.Protocol.Verifier (gen)
open LeanVM.Guest.Value
open LeanVM.Prover.Exec (allocBase)

@[expose] public section

/-! ## The template -/

/-- Column `h`'s statements: its leaf, the offsets moved by `g^7`, the expansion, its pointer stored. -/
def wsCol (h : ℕ) : List Stmt :=
  if h = 0 then
    [.atom (.load (.n 5) (.n 0) 0), .call "da_expand__L6_L7" [.n 5, .n 1, .n 2, .n 3] [.n 6],
      .atom (.load (.n 6) (.n 4) 0)]
  else
    [.atom (.load (.n (4 * h + 3)) (.n 0) h), .atom (.const (.n (4 * h + 4)) (word 128 0)),
      .atom (.mul (.n (4 * h + 5)) (wsOff (h - 1)) (.n (4 * h + 4))),
      .call "da_expand__L6_L7" [.n (4 * h + 3), .n 1, .n 2, .n (4 * h + 5)] [.n (4 * h + 6)],
      .atom (.load (.n (4 * h + 6)) (.n 4) h)]

/-- **`da_weights`' block.** -/
def wsPre : List Stmt :=
  .atom (.hint (.alloc (.n 4) 128)) :: (List.range 128).flatMap wsCol ++ [.atom (.copy (.n 515) (.n 4))]

/-- Column `h`'s call. -/
def wsCallS (h : ℕ) : Option V × String × List V × List V :=
  (none, "da_expand__L6_L7", [wsLeaf h, .n 1, .n 2, wsOff h], [.n (4 * h + 6)])

set_option maxRecDepth 200000 in
theorem ws_cok : stmtsEqb (fn% «da_weights»).body (wsPre ++ [.ret [.n 515]]) = true ∧
    (fn% «da_weights»).params = [.n 0, .n 1, .n 2, .n 3] ∧ wsPre.all Stmt.straight = true ∧
    wsPre.all noHeapHintS = true ∧ wsPre.filterMap Stmt.allocSz = [(.n 4, .inl 128)] ∧
    wsPre.filterMap Stmt.addrS = [] ∧ wsPre.filterMap Stmt.callS = (List.range 128).map wsCallS ∧
    coreProgram.loop "da_weights" = false := by
  decide +kernel

/-! ## Positions -/

/-- The cursor before column `h`'s call: past the weights, then each call's frame. -/
def wsCur (fs : String → ℕ) (al : String → Bool) (c : ℕ) : ℕ → ℕ
  | 0 => c + 128
  | h + 1 => allocBase (al "da_expand__L6_L7") (wsCur fs al c h) + fs "da_expand__L6_L7"

/-- Column `h`'s run. -/
def wsCol' (fs : String → ℕ) (al : String → Bool) (cert : String → V → ℕ) (c h : ℕ) : ℕ :=
  allocBase (al "da_expand__L6_L7") (wsCur fs al c h) + cert "da_expand__L6_L7" (.n (expB 7 + 1))

/-- The columns' cursor, each column a frame. -/
theorem wsCur_le {fs : String → ℕ} (hfs : ∀ g, fs g < 2 ^ 16) (al : String → Bool) (c : ℕ) :
    ∀ h, wsCur fs al c h ≤ c + 128 + h * 2 ^ 17
  | 0 => by simp [wsCur]
  | h + 1 => by
    rw [wsCur]
    have h1 := wsCur_le hfs al c h
    have h2 := allocBase_le (al "da_expand__L6_L7") (wsCur fs al c h)
    have h3 := hfs "da_expand__L6_L7"
    rw [Nat.succ_mul]
    omega

/-! ## The valuation -/

/-- `da_weights`' valuation: its parameters, `weights`, column `0`'s, the other columns', the copy. -/
def wsVals (z : E) (bt bc bz bo c : ℕ) (bcol : ℕ → ℕ) : List E :=
  [gen ^ (bt + 128), gen ^ bc, gen ^ bz, gen ^ bo, gen ^ c, topLeaf z 0, gen ^ (bcol 0 + 128)] ++
    (List.range 127).flatMap (fun i => [topLeaf z (i + 1), word 128 0, gen ^ (bo + 7 * (i + 1)),
      gen ^ (bcol (i + 1) + 128)]) ++ [gen ^ c]

variable {fs : String → ℕ} {al : String → Bool} {cert : String → V → ℕ}

theorem word_g7 : word 128 0 = gen ^ 7 := word_two_pow (a := 7) (by norm_num)

set_option maxRecDepth 100000 in
/-- **The columns' calls complete placed**, one after another from column `h0`'s cursor. -/
theorem ws_kids {k : ℕ} {σ : Val} {R : ℕ → Prop} {Pre : Reader → Prop} (hE : ExpCert fs cert "da_expand__L6_L7")
    {z : E} {bt bc bz bo c : ℕ}
    (hσ : ∀ h < 128, [wsLeaf h, .n 1, .n 2, wsOff h].map σ = [topLeaf z h, gen ^ bc, gen ^ bz, gen ^ (bo + 7 * h)] ∧
      [V.n (4 * h + 6)].map σ = [gen ^ (wsCol' fs al cert c h + 128)])
    (hR : ∀ i, vecR bz bt bc bo i → R i) (hpre : ∀ rd, Pre rd → HoldsWords rd (vecWords z bz bt bc bo)) :
    ∀ n h0, h0 + n = 128 → ∀ (O : Reader → Prop) (Dacc : ℕ → Prop) (Oend : Reader → Prop) (Dend : ℕ → Prop),
      (∀ rd, O rd → (∀ h, h0 ≤ h → h < 128 → HoldsWords rd [(wsCol' fs al cert c h, colRun z h)]) → Oend rd) →
      (∀ i, Dend i → Dacc i ∨ ∃ h, h0 ≤ h ∧ h < 128 ∧ wsCol' fs al cert c h ≤ i ∧ i < wsCol' fs al cert c h + 256) →
      KidsAtF fs al cert k σ R Pre O Dacc [] ((List.range' h0 n).map (mkCall σ ∘ wsCallS)) (wsCur fs al c h0)
        (wsCur fs al c 128) Oend Dend
  | 0, h0, hn, O, Dacc, Oend, Dend, hOe, hDe => by
    obtain rfl : h0 = 128 := by omega
    rw [List.range'_zero, List.map_nil, KidsAtF]
    refine ⟨rfl, fun rd h => hOe rd h fun _ h1 h2 => absurd h2 (by omega), fun i hi => ?_⟩
    rcases hDe i hi with h | ⟨_, h1, h2, -⟩
    · exact h
    · omega
  | n + 1, h0, hn, O, Dacc, Oend, Dend, hOe, hDe => by
    have hh : h0 < 128 := by omega
    obtain ⟨hargs, hrets⟩ := hσ h0 hh
    rw [List.range'_succ, List.map_cons, KidsAtF]
    simp only [Function.comp, mkCall, wsCallS, ↓reduceIte]
    refine ⟨fs "da_expand__L6_L7", wsCur fs al c (h0 + 1), vecR bz bt bc bo,
      fun i => wsCol' fs al cert c h0 ≤ i ∧ i < wsCol' fs al cert c h0 + 256,
      fun rd => HoldsWords rd [(wsCol' fs al cert c h0, colRun z h0)], fun i hi => Or.inl (hR i hi), ?_, ?_⟩
    · rw [hargs, hrets]
      have hb7 : 7 * h0 + 6 < 896 := by omega
      refine (expCell_callAtA (al := al) hE k (topLeaf z h0) (factorAt (zsVal z) 6) (zsVal z) (colShift z h0)
        (cf := bc) (cz := bz) (cs := bo + 7 * h0) (R := vecR bz bt bc bo)
        (fun n h1 h2 => Or.inr (Or.inr (Or.inl ⟨by omega, by omega⟩)))
        (fun d hd => Or.inl ⟨by omega, by omega⟩) (fun d hd => Or.inr (Or.inr (Or.inr ⟨by omega, by omega⟩)))
        (allocBase (al "da_expand__L6_L7") (wsCur fs al c h0))
        (allocBase (al "da_expand__L6_L7") (wsCur fs al c h0) + fs "da_expand__L6_L7")).mono
        (fun _ h => h) (fun _ h => h) (fun _ h => h) (fun rd h => ?_) (fun _ _ _ _ => trivial)
      have hv := hpre rd h.1
      have hz : ReadsAt rd (gen ^ bz) (zsCells z) := by
        rw [gen_pow_eq_ofK]; exact hv (bz, zsCells z) List.mem_cons_self
      have hf : ReadsAt rd (gen ^ bc) (facCells (zsVal z) 6 7) := by
        rw [gen_pow_eq_ofK]
        exact hv (bc, facCells (zsVal z) 6 7) (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))
      have ho : ReadsAt rd (gen ^ bo) (offCells (zsVal z)) := by
        rw [gen_pow_eq_ofK]
        exact hv (bo, offCells (zsVal z)) (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
          (List.mem_cons_of_mem _ List.mem_cons_self)))
      refine ⟨fun n h1 h2 => ?_, fun d hd => ?_, fun d hd => ?_⟩
      · have := hf n (by simp [facCells]; omega)
        rwa [facCells_getElem h1 h2] at this
      · have := hz (6 - d) (by simp [zsCells]; omega)
        rwa [zsCells_getElem (by omega)] at this
      · have := (loadHolds_mul_gen_pow rd (gen ^ bo) (7 * h0) (6 - d) _).mpr
          (ho (7 * h0 + (6 - d)) (by simp; omega))
        rw [offCells_getElem _ (by omega) (by omega)] at this
        rw [pow_add]
        exact this
    · refine ws_kids hE hσ hR hpre n (h0 + 1) (by omega) _ _ Oend Dend (fun rd h hr => hOe rd h.1 fun h' h1 h2 => ?_)
        (fun i hi => ?_)
      · rcases Nat.lt_or_ge h0 h' with hl | hl
        · exact hr h' (by omega) h2
        · obtain rfl : h' = h0 := by omega
          exact h.2
      · rcases hDe i hi with h | ⟨h', h1, h2, h3, h4⟩
        · exact Or.inl (Or.inl h)
        · rcases Nat.lt_or_ge h0 h' with hl | hl
          · exact Or.inr ⟨h', by omega, h2, h3, h4⟩
          · obtain rfl : h' = h0 := by omega
            exact Or.inl (Or.inr ⟨h3, h4⟩)

set_option maxRecDepth 20000 in
/-- **`da_weights` completes placed** at frame `fp` and cursor `c`, its table at `c`. -/
theorem ws_callAtA (hE : ExpCert fs cert "da_expand__L6_L7") (k : ℕ) (z : E) (bz bt bc bo : ℕ) {fp c : ℕ}
    (hfc : fp + fs "da_weights" ≤ c) :
    CallAtA fs al cert k "da_weights" [gen ^ (bt + 128), gen ^ bc, gen ^ bz, gen ^ bo] [gen ^ c]
      (vecR bz bt bc bo) (wsR c (wsCol' fs al cert c)) (fun rd => HoldsWords rd (wsWords z c (wsCol' fs al cert c)))
      (fun rd => HoldsWords rd (vecWords z bz bt bc bo)) (fun _ _ => True) (fs "da_weights") fp c
      (wsCur fs al c 128) := by
  obtain ⟨hbody, hparams, hstr, hnh, halloc, haddr, hcalls, hlp⟩ := ws_cok
  set bcol := wsCol' fs al cert c with hbcol
  set σ := Val.ofArgs (wsVals z bt bc bz bo c bcol) with hσ
  have hparts := straight_parts σ wsPre hstr
  have hal : allocs σ (wsPre.flatMap (slEvs σ)) = [128] := by rw [hparts.2.1, halloc]; rfl
  -- the valuation
  have hmid : ∀ h, 1 ≤ h → h < 128 → ∀ r < 4, σ (.n (4 * h + 3 + r)) =
      [topLeaf z h, word 128 0, gen ^ (bo + 7 * h), gen ^ (bcol h + 128)].getD r 0 := by
    intro h h1 h2 r hr
    obtain ⟨i, rfl⟩ : ∃ i, h = i + 1 := ⟨h - 1, by omega⟩
    rw [show 4 * (i + 1) + 3 + r = [gen ^ (bt + 128), gen ^ bc, gen ^ bz, gen ^ bo, gen ^ c, topLeaf z 0,
      gen ^ (bcol 0 + 128)].length + (4 * i + r) by simp only [List.length_cons, List.length_nil]; omega]
    exact getD_mid _ _ (fun i => [topLeaf z (i + 1), word 128 0, gen ^ (bo + 7 * (i + 1)),
      gen ^ (bcol (i + 1) + 128)]) (fun _ => rfl) (by omega) hr
  have hleaf : ∀ h < 128, σ (wsLeaf h) = topLeaf z h := fun h hh => by
    rcases Nat.eq_zero_or_pos h with rfl | h1
    · rfl
    · have hne : h ≠ 0 := by omega
      simp only [wsLeaf, hne, ↓reduceIte]
      rw [show 4 * h + 3 = 4 * h + 3 + 0 from rfl, hmid h h1 hh 0 (by norm_num)]; rfl
  have hoff : ∀ h < 128, σ (wsOff h) = gen ^ (bo + 7 * h) := fun h hh => by
    rcases Nat.eq_zero_or_pos h with rfl | h1
    · rfl
    · have hne : h ≠ 0 := by omega
      simp only [wsOff, hne, ↓reduceIte]
      rw [show 4 * h + 5 = 4 * h + 3 + 2 by omega, hmid h h1 hh 2 (by norm_num)]; rfl
  have hret : ∀ h < 128, σ (.n (4 * h + 6)) = gen ^ (bcol h + 128) := fun h hh => by
    rcases Nat.eq_zero_or_pos h with rfl | h1
    · rfl
    · rw [show 4 * h + 6 = 4 * h + 3 + 3 by omega, hmid h h1 hh 3 (by norm_num)]; rfl
  have hc128 : ∀ h, 1 ≤ h → h < 128 → σ (.n (4 * h + 4)) = word 128 0 := fun h h1 hh => by
    rw [show 4 * h + 4 = 4 * h + 3 + 1 by omega, hmid h h1 hh 1 (by norm_num)]; rfl
  have h515 : σ (.n 515) = gen ^ c := by
    show (wsVals z bt bc bz bo c bcol).getD 515 0 = _
    have hl : ([gen ^ (bt + 128), gen ^ bc, gen ^ bz, gen ^ bo, gen ^ c, topLeaf z 0, gen ^ (bcol 0 + 128)] ++
        (List.range 127).flatMap (fun i => [topLeaf z (i + 1), word 128 0, gen ^ (bo + 7 * (i + 1)),
          gen ^ (bcol (i + 1) + 128)])).length = 515 := by
      rw [List.length_append, length_flatMap_range (m := 4) _ (fun _ => rfl)]; rfl
    rw [wsVals, List.getD_append_right _ _ _ _ (by rw [hl]), hl]; rfl
  have hcl : calls (wsPre.flatMap (slEvs σ)) = (List.range' 0 128).map (mkCall σ ∘ wsCallS) := by
    rw [hparts.2.2.2, hcalls, List.map_map, List.range_eq_range']
  have hown : ∀ i, c ≤ i → i < c + 128 → ownData cert fp c "da_weights" (allocs σ (wsPre.flatMap (slEvs σ)))
      (wsPre.flatMap (slEvs σ)) i := fun i h1 h2 => by
    rw [hal]; exact Or.inl (VsC.bufs_cover [128] c i h1 (by simp; omega))
  refine callAtA_node hlp hfc ⟨σ, fn% «da_weights», wsPre.flatMap (slEvs σ), [.n 515], [(c, wsTable bcol)], [],
    fun rd => HoldsWords rd (wsWords z c bcol), fun i => ∃ h < 128, bcol h ≤ i ∧ i < bcol h + 256,
    find_da_weights, by rw [hparams]; rfl, by rw [stmtsEqb_sound hbody]; exact walk_straight σ _ wsPre hstr,
    by simp [h515], ?_, ?_, ?_, ?_, ?_, ?_, fun rd h => h, ?_, fun _ _ _ _ _ _ _ => trivial⟩
  · -- placed
    rw [hal]
    refine ⟨?_, fun q hq => by rw [hparts.2.2.1, haddr] at hq; simp at hq⟩
    rw [hparts.1, halloc]
    show [gen ^ c] = [ofK (addressOfIndex c)]
    rw [gen_pow_eq_ofK]
  · -- the own words
    rw [hal]
    exact ⟨fun q hq => by simp only [List.mem_singleton] at hq; subst hq; right; simp [wsTable],
      List.pairwise_singleton _ _⟩
  · -- the loads
    intro A hA
    rw [Memory.loadAddrs_straight σ wsPre hstr] at hA
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hA
    obtain ⟨s, hs, hq⟩ := List.mem_filterMap.mp hq
    simp only [wsPre, List.mem_cons, List.mem_append, List.mem_flatMap, List.mem_range, List.not_mem_nil,
      or_false] at hs
    rcases hs with (rfl | ⟨h, hh, hs⟩) | rfl
    · simp [stmtLoad?] at hq
    · by_cases h0 : h = 0
      · subst h0
        simp only [wsCol, ↓reduceIte, List.mem_cons, List.not_mem_nil, or_false] at hs
        rcases hs with rfl | rfl | rfl <;> simp only [stmtLoad?, reduceCtorEq, Option.some.injEq] at hq <;>
          subst hq
        · exact ⟨bt + 128 + 0, by show (gen ^ (bt + 128)).limb 0 * _ = _; rw [gen_pow_eq_ofK, Main.addr_ofK],
            Or.inr (Or.inl (Or.inr (Or.inl ⟨by omega, by omega⟩)))⟩
        · exact ⟨c + 0, by show (gen ^ c).limb 0 * _ = _; rw [gen_pow_eq_ofK, Main.addr_ofK],
            Or.inl (hown _ (by omega) (by omega))⟩
      · simp only [wsCol, h0, ↓reduceIte, List.mem_cons, List.not_mem_nil, or_false] at hs
        rcases hs with rfl | rfl | rfl | rfl | rfl <;> simp only [stmtLoad?, reduceCtorEq, Option.some.injEq] at hq <;>
          subst hq
        · exact ⟨bt + 128 + h, by show (gen ^ (bt + 128)).limb 0 * _ = _; rw [gen_pow_eq_ofK, Main.addr_ofK],
            Or.inr (Or.inl (Or.inr (Or.inl ⟨by omega, by omega⟩)))⟩
        · exact ⟨c + h, by show (gen ^ c).limb 0 * _ = _; rw [gen_pow_eq_ofK, Main.addr_ofK],
            Or.inl (hown _ (by omega) (by omega))⟩
    · simp [stmtLoad?] at hq
  · intro A hA
    rw [heapHintAddrs_straight_nil hnh] at hA
    simp at hA
  · intro i hi
    rcases hi with hi | hi
    · exact Or.inl (hown i hi.1 hi.2)
    · exact Or.inr hi
  · -- the calls
    rw [hcl, hal]
    refine ws_kids (z := z) (c := c) hE (fun h hh => ⟨?_, ?_⟩) (fun i hi => Or.inl hi) (fun rd h => h) 128 0 rfl
      _ _ _ _ (fun rd h hr => ?_) (fun i hi => Or.inr ?_)
    · show [σ (wsLeaf h), σ (.n 1), σ (.n 2), σ (wsOff h)] = _
      rw [hleaf h hh, hoff h hh]; rfl
    · show [σ (.n (4 * h + 6))] = _
      rw [hret h hh]
    · intro q hq
      simp only [wsWords, List.mem_cons, List.mem_map, List.mem_range] at hq
      rcases hq with rfl | ⟨h, hh, rfl⟩
      · exact h _ List.mem_cons_self
      · exact hr h (Nat.zero_le _) hh _ List.mem_cons_self
    · obtain ⟨h, hh, h1, h2⟩ := hi
      exact ⟨h, Nat.zero_le _, hh, h1, h2⟩
  · -- the atoms
    intro rd _ hp hO ev hev
    have htl : ∀ h < 128, LoadHolds rd (gen ^ (bt + 128)) h (topLeaf z h) := fun h hh => by
      have : ReadsAt rd (gen ^ bt) (topRun z) := by
        rw [gen_pow_eq_ofK]; exact hp (bt, topRun z) (List.mem_cons_of_mem _ List.mem_cons_self)
      have := (loadHolds_mul_gen_pow rd (gen ^ bt) 128 h _).mpr (this (128 + h) (by simp; omega))
      rw [← pow_add] at this
      convert this using 1
      rw [← List.getD_eq_getElem _ 0, topRun_leaf z hh]
    have hw : ∀ h < 128, LoadHolds rd (gen ^ c) h (gen ^ (bcol h + 128)) := fun h hh => by
      have : ReadsAt rd (gen ^ c) (wsTable bcol) := by
        rw [gen_pow_eq_ofK]; exact hO (c, wsTable bcol) List.mem_cons_self
      have := this h (by simp [wsTable]; exact hh)
      simpa [wsTable] using this
    refine events_straight (fun s hs => ?_) ev hev
    simp only [wsPre, List.mem_cons, List.mem_append, List.mem_flatMap, List.mem_range, List.not_mem_nil,
      or_false] at hs
    rcases hs with (rfl | ⟨h, hh, hs⟩) | rfl
    · trivial
    · by_cases h0 : h = 0
      · subst h0
        simp only [wsCol, ↓reduceIte, List.mem_cons, List.not_mem_nil, or_false] at hs
        rcases hs with rfl | rfl | rfl
        · exact htl 0 (by norm_num)
        · trivial
        · exact hw 0 (by norm_num)
      · have h1 : 1 ≤ h := by omega
        simp only [wsCol, h0, ↓reduceIte, List.mem_cons, List.not_mem_nil, or_false] at hs
        rcases hs with rfl | rfl | rfl | rfl | rfl
        · show LoadHolds rd (gen ^ (bt + 128)) h (σ (.n (4 * h + 3)))
          rw [show 4 * h + 3 = 4 * h + 3 + 0 from rfl, hmid h h1 hh 0 (by norm_num)]
          exact htl h hh
        · exact hc128 h h1 hh
        · show σ (.n (4 * h + 5)) = σ (wsOff (h - 1)) * σ (.n (4 * h + 4))
          rw [hoff (h - 1) (by omega), hc128 h h1 hh, show 4 * h + 5 = 4 * h + 3 + 2 by omega,
            hmid h h1 hh 2 (by norm_num), word_g7, ← pow_add]
          show gen ^ (bo + 7 * h) = gen ^ (bo + 7 * (h - 1) + 7)
          congr 1; omega
        · trivial
        · show LoadHolds rd (gen ^ c) h (σ (.n (4 * h + 6)))
          rw [hret h hh]
          exact hw h hh
    · show σ (.n 515) = σ (.n 4)
      rw [h515]; rfl

/-- **`da_weights` completes placed** (`DaWeightsCompleteA`), wherever a cell tree's run lies in its frame. -/
theorem daWeightsCompleteA (hfs : ∀ g, fs g < 2 ^ 16) (hE : ExpCert fs cert "da_expand__L6_L7") (k : ℕ) :
    DaWeightsCompleteA fs al cert k := by
  intro z bz bt bc bo fp c hfc
  exact ⟨c, wsCol' fs al cert c, wsCur fs al c 128, by have := wsCur_le hfs al c 128; omega,
    (ws_callAtA hE k z bz bt bc bo hfc).free da_weights_free.1 da_weights_free.2⟩

/-- **`da_weights` completes placed at the compiled frames.** -/
theorem daWeightsCompleteA_b2c (al : String → Bool) (k : ℕ) : DaWeightsCompleteA B2C.fs al B2C.cert k :=
  daWeightsCompleteA fs_lt16 expCellCert_b2c k

end
end LeanVM.Guest.Complete
