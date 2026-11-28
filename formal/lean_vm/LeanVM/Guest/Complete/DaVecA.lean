module

public import LeanVM.Guest.Complete.DaOffA
public import LeanVM.Guest.Complete.DaExpA
public import LeanVM.Guest.Complete.DaVerifyNodeA
public import LeanVM.Guest.Complete.AggFree
public import LeanVM.Guest.Complete.DaFree
public import LeanVM.Guest.Complete.FsSmall
import LeanVM.Guest.CoreRef
import LeanVM.Guest.ValRef
import LeanVM.Guest.Data.ValNames.«da_vector»

/-!
# `da_vector`, placed

`da_vector(z)` at frame `fp` and cursor `c`: its `HeapBuf`s `zs` (`zsCells z`, at `c`) and
`above_top` (zeros, at `c + 14`) its own words; its callees from `c + 28`: the top factors
(`facTop_callAtA`), the top tree (`expTop_callAtA`, its run at `bt`), the cell factors
(`facCell_callAtA`, at `bc`) and the column offsets (`off_callAtA`, at `bo`), each at the aligned
base of the cursor the one before leaves. The valuation is explicit (`vecVals`, the archive's
`VecAt`). `daVectorCompleteA`: `DaVectorCompleteA` at every frame table whose top tree's run lies in
its frame (`ExpCert`), so at `B2C.fs`, `B2C.cert` and every `al`.
-/

namespace LeanVM.Guest.Complete

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Memory LeanVM.Guest.B1
open LeanVM.Guest.B1.Da LeanVM.Guest.B1.Digest LeanVM.Guest.B1.Fwd
open LeanVM.Protocol.Verifier (gen)
open LeanVM.Guest.Value
open LeanVM.Prover.Exec (allocBase)

@[expose] public section

/-- `above_top`'s words: zeros (its first seven are never written, and read `0`). -/
def aboveCells : List E := List.replicate 14 0

/-- `da_vector`'s block. -/
def vecPre : List Stmt := [
  .atom (.hint (.alloc (.n 1) 14)),
  .atom (.load (.n 0) (.n 1) 0),
  .atom (.mul (.n 2) (.n 0) (.n 0)),
  .atom (.load (.n 2) (.n 1) 1),
  .atom (.mul (.n 3) (.n 2) (.n 2)),
  .atom (.load (.n 3) (.n 1) 2),
  .atom (.mul (.n 4) (.n 3) (.n 3)),
  .atom (.load (.n 4) (.n 1) 3),
  .atom (.mul (.n 5) (.n 4) (.n 4)),
  .atom (.load (.n 5) (.n 1) 4),
  .atom (.mul (.n 6) (.n 5) (.n 5)),
  .atom (.load (.n 6) (.n 1) 5),
  .atom (.mul (.n 7) (.n 6) (.n 6)),
  .atom (.load (.n 7) (.n 1) 6),
  .atom (.mul (.n 8) (.n 7) (.n 7)),
  .atom (.load (.n 8) (.n 1) 7),
  .atom (.mul (.n 9) (.n 8) (.n 8)),
  .atom (.load (.n 9) (.n 1) 8),
  .atom (.mul (.n 10) (.n 9) (.n 9)),
  .atom (.load (.n 10) (.n 1) 9),
  .atom (.mul (.n 11) (.n 10) (.n 10)),
  .atom (.load (.n 11) (.n 1) 10),
  .atom (.mul (.n 12) (.n 11) (.n 11)),
  .atom (.load (.n 12) (.n 1) 11),
  .atom (.mul (.n 13) (.n 12) (.n 12)),
  .atom (.load (.n 13) (.n 1) 12),
  .atom (.mul (.n 14) (.n 13) (.n 13)),
  .atom (.const (.n 15) (word 0 0)),
  .atom (.load (.n 15) (.n 1) 13),
  .atom (.hint (.alloc (.n 16) 14)),
  .atom (.const (.n 17) (word 0 0)),
  .atom (.load (.n 17) (.n 16) 7),
  .atom (.const (.n 18) (word 0 0)),
  .atom (.load (.n 18) (.n 16) 8),
  .atom (.const (.n 19) (word 0 0)),
  .atom (.load (.n 19) (.n 16) 9),
  .atom (.const (.n 20) (word 0 0)),
  .atom (.load (.n 20) (.n 16) 10),
  .atom (.const (.n 21) (word 0 0)),
  .atom (.load (.n 21) (.n 16) 11),
  .atom (.const (.n 22) (word 0 0)),
  .atom (.load (.n 22) (.n 16) 12),
  .atom (.const (.n 23) (word 0 0)),
  .atom (.load (.n 23) (.n 16) 13),
  .call "da_factors__L13_L7_L0" [.n 1] [.n 24],
  .atom (.const (.n 25) (word 1 0)),
  .call "da_expand__L13_L7" [.n 25, .n 24, .n 1, .n 16] [.n 26],
  .call "da_factors__L6_L7_L128" [.n 1] [.n 27],
  .call "da_column_offsets" [.n 1] [.n 28],
  .atom (.copy (.n 29) (.n 1)),
  .atom (.copy (.n 30) (.n 26)),
  .atom (.copy (.n 31) (.n 27)),
  .atom (.copy (.n 32) (.n 28))]

theorem vec_body : (fn% «da_vector»).body = vecPre ++ [.ret [.n 29, .n 30, .n 31, .n 32]] := rfl
theorem vec_params : (fn% «da_vector»).params = [.n 0] := rfl

set_option maxRecDepth 100000 in
theorem vec_cok : vecPre.all Stmt.straight = true ∧ vecPre.all noHeapHintS = true ∧
    vecPre.filterMap Stmt.addrS = [] ∧ coreProgram.loop "da_vector" = false := by
  decide +kernel

/-- `da_vector`'s valuation: `z`, `zs`, the powers, `above_top`, its callees' returns. -/
def vecVals (z : E) (c : ℕ) (r24 r26 r27 r28 : E) : List E :=
  [z, gen ^ c, z ^ 2 ^ 1, z ^ 2 ^ 2, z ^ 2 ^ 3, z ^ 2 ^ 4, z ^ 2 ^ 5, z ^ 2 ^ 6, z ^ 2 ^ 7, z ^ 2 ^ 8,
    z ^ 2 ^ 9, z ^ 2 ^ 10, z ^ 2 ^ 11, z ^ 2 ^ 12, z ^ 2 ^ 13, 0, gen ^ (c + 14),
    0, 0, 0, 0, 0, 0, 0, r24, 1, r26, r27, r28, gen ^ c, r26, r27, r28]

theorem zsCells_getElem {z : E} {j : ℕ} (hj : j < 14) :
    (zsCells z)[j]'(by simp [zsCells]; exact hj) = zsVal z j := by
  simp [zsCells]

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 20000 in
/-- **`da_vector`'s statements hold** on its valuation, `zs` and `above_top` holding their words. -/
theorem vec_sholds {rd : Reader} (z : E) (c : ℕ) (r24 r26 r27 r28 : E)
    (hzv : ∀ j v, j < 14 → zsVal z j = v → LoadHolds rd (gen ^ c) j v)
    (hav : ∀ j v, j < 14 → v = 0 → LoadHolds rd (gen ^ (c + 14)) j v) :
    ∀ s ∈ vecPre, SOk rd (Val.ofArgs (vecVals z c r24 r26 r27 r28)) s := by
  intro s hs
  simp only [vecPre, List.mem_cons, List.not_mem_nil, or_false] at hs
  rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals simp only [SOk, Atom.Holds, ofArgs_n, vecVals, List.getD_cons_succ, List.getD_cons_zero]
  all_goals first
    | exact word_zero.symm
    | exact word_one.symm
    | (refine hzv _ _ (by norm_num) (by simp [zsVal]))
    | (refine hav _ _ (by norm_num) rfl)
    | ring

variable {fs : String → ℕ} {al : String → Bool} {cert : String → V → ℕ}

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 20000 in
/-- **`da_vector` completes placed** at frame `fp` and cursor `c`, `zs` at `c`. -/
theorem vec_callAtA (hfs : ∀ g, fs g < 2 ^ 16) (hE : ExpCert fs cert "da_expand__L13_L7") (k : ℕ) (z : E)
    {fp c : ℕ} (hfc : fp + fs "da_vector" ≤ c) :
    ∃ (bt bc bo e : ℕ), e ≤ c + 2 ^ 30 ∧ CallAtA fs al cert k "da_vector" [z] (vecRets c bt bc bo) (fun _ => False)
      (vecR c bt bc bo) (fun rd => HoldsWords rd (vecWords z c bt bc bo)) (fun _ => True) (fun _ _ => True)
      (fs "da_vector") fp c e := by
  obtain ⟨hstr, hnh, haddr, hlp⟩ := vec_cok
  set fp1 := allocBase (al "da_factors__L13_L7_L0") (c + 28) with hfp1
  set c1 := fp1 + fs "da_factors__L13_L7_L0" with hc1
  set fp2 := allocBase (al "da_expand__L13_L7") (c1 + 128) with hfp2
  set bt := fp2 + cert "da_expand__L13_L7" (.n (expB 7 + 1)) with hbt
  set fp3 := allocBase (al "da_factors__L6_L7_L128") (fp2 + fs "da_expand__L13_L7") with hfp3
  set bc := fp3 + fs "da_factors__L6_L7_L128" with hbc
  set fp4 := allocBase (al "da_column_offsets") (bc + 128) with hfp4
  set bo := fp4 + fs "da_column_offsets" with hbo
  refine ⟨bt, bc, bo, offFold fs al (List.range 7) (bo + 945), ?_, ?_⟩
  · have h0 := offFold_le (al := al) hfs (List.range 7) (bo + 945) fun b hb => by
      simp only [List.mem_range] at hb; omega
    simp only [List.length_range] at h0
    have h1 := allocBase_le (al "da_factors__L13_L7_L0") (c + 28)
    have h2 := allocBase_le (al "da_expand__L13_L7") (c1 + 128)
    have h3 := allocBase_le (al "da_factors__L6_L7_L128") (fp2 + fs "da_expand__L13_L7")
    have h4 := allocBase_le (al "da_column_offsets") (bc + 128)
    have f1 := hfs "da_factors__L13_L7_L0"
    have f2 := hfs "da_expand__L13_L7"
    have f3 := hfs "da_factors__L6_L7_L128"
    have f4 := hfs "da_column_offsets"
    omega
  set σ := Val.ofArgs (vecVals z c (gen ^ c1) (gen ^ (bt + 128)) (gen ^ bc) (gen ^ bo)) with hσ
  have hparts := straight_parts σ vecPre hstr
  have hal : allocs σ (vecPre.flatMap (slEvs σ)) = [14, 14] := by rw [hparts.2.1]; rfl
  have hcl : calls (vecPre.flatMap (slEvs σ)) = [⟨"da_factors__L13_L7_L0", [.n 1], [.n 24], true⟩,
      ⟨"da_expand__L13_L7", [.n 25, .n 24, .n 1, .n 16], [.n 26], true⟩,
      ⟨"da_factors__L6_L7_L128", [.n 1], [.n 27], true⟩, ⟨"da_column_offsets", [.n 1], [.n 28], true⟩] := by
    rw [hparts.2.2.2]; rfl
  set Wo : Words := [(c, zsCells z), (c + 14, aboveCells)] with hWo
  have hown : ∀ i, c ≤ i → i < c + 28 → ownData cert fp c "da_vector" (allocs σ (vecPre.flatMap (slEvs σ)))
      (vecPre.flatMap (slEvs σ)) i := fun i h1 h2 => by
    rw [hal]; exact Or.inl (VsC.bufs_cover [14, 14] c i h1 (by simp; omega))
  have hzs : ∀ rd, HoldsWords rd Wo → ∀ j < 14, LoadHolds rd (gen ^ c) j (zsVal z j) := fun rd h j hj => by
    have := h (c, zsCells z) List.mem_cons_self
    rw [← gen_pow_eq_ofK] at this
    have := this j (by simp [zsCells]; exact hj)
    rwa [zsCells_getElem hj] at this
  have hab : ∀ rd, HoldsWords rd Wo → ∀ j < 14, LoadHolds rd (gen ^ (c + 14)) j 0 := fun rd h j hj => by
    have := h (c + 14, aboveCells) (List.mem_cons_of_mem _ List.mem_cons_self)
    rw [← gen_pow_eq_ofK] at this
    have := this j (by simp [aboveCells]; exact hj)
    simp only [aboveCells, List.getElem_replicate] at this
    exact this
  have hfac : ∀ rd {b top : ℕ}, HoldsWords rd [(b, facCells (zsVal z) top 7)] → ∀ n, 1 ≤ n → n < 2 ^ 7 →
      LoadHolds rd (gen ^ b) n (factorAt (zsVal z) top n) := fun rd b top h n h1 h2 => by
    have := readsAt_gen_pow.mp h n (by simp [facCells]; omega)
    rwa [facCells_getElem h1 h2] at this
  refine callAtA_node hlp hfc ⟨σ, fn% «da_vector», vecPre.flatMap (slEvs σ), [.n 29, .n 30, .n 31, .n 32], Wo, [],
    fun rd => ((((HoldsWords rd Wo ∧ HoldsWords rd [(c1, facCells (zsVal z) 13 7)]) ∧
      HoldsWords rd [(bt, topRun z)]) ∧ HoldsWords rd [(bc, facCells (zsVal z) 6 7)]) ∧
      HoldsWords rd [(bo, offCells (zsVal z))]),
    fun i => (bt ≤ i ∧ i < bt + 256) ∨ (bc ≤ i ∧ i < bc + 128) ∨ (bo ≤ i ∧ i < bo + 896),
    find_da_vector, by rw [vec_params]; rfl, by rw [vec_body]; exact walk_straight σ _ vecPre hstr, rfl,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun _ _ _ _ _ _ _ => trivial⟩
  · -- placed
    rw [hal]
    refine ⟨?_, fun q hq => by rw [hparts.2.2.1, haddr] at hq; simp at hq⟩
    rw [hparts.1]
    show [gen ^ c, gen ^ (c + 14)] = [ofK (addressOfIndex c), ofK (addressOfIndex (c + 14))]
    rw [gen_pow_eq_ofK, gen_pow_eq_ofK]
  · -- the own words
    rw [hal]
    refine ⟨fun q hq => Or.inr ?_, ?_⟩
    · simp only [hWo, List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl | rfl <;> simp [aboveCells]
    · simp [hWo, aboveCells]
  · -- the loads
    intro A hA
    rw [Memory.loadAddrs_straight σ vecPre hstr] at hA
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hA
    have hq' : (q.1 = .n 1 ∧ q.2 < 14) ∨ (q.1 = .n 16 ∧ q.2 < 14) := by
      simp only [vecPre, List.filterMap_cons, stmtLoad?, List.filterMap_nil, List.mem_cons, List.not_mem_nil,
        or_false] at hq
      rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
        rfl | rfl | rfl | rfl | rfl <;> simp
    obtain ⟨p, o⟩ := q
    rcases hq' with ⟨hp1, ho⟩ | ⟨hp1, ho⟩ <;> simp only at hp1 ho <;> subst hp1
    · refine ⟨c + o, ?_, Or.inl (hown _ (by omega) (by omega))⟩
      rw [show σ (.n 1) = ofK (addressOfIndex c) by rw [← gen_pow_eq_ofK]; rfl, Main.addr_ofK]
    · refine ⟨c + 14 + o, ?_, Or.inl (hown _ (by omega) (by omega))⟩
      rw [show σ (.n 16) = ofK (addressOfIndex (c + 14)) by rw [← gen_pow_eq_ofK]; rfl, Main.addr_ofK]
  · intro A hA
    rw [heapHintAddrs_straight_nil hnh] at hA
    simp at hA
  · -- the data
    intro i hi
    rcases hi with hi | hi
    · exact Or.inl (hown i hi.1 (by omega))
    · exact Or.inr hi
  · -- the callees
    rw [hcl, hal]
    have hR28 : ∀ i, c ≤ i → i < c + 28 → (False ∨ ownData cert fp c "da_vector" [14, 14] (vecPre.flatMap (slEvs σ)) i) ∨
        False := fun i h1 h2 => Or.inl (Or.inr (by have := hown i h1 h2; rwa [hal] at this))
    rw [KidsAtF]; simp only [↓reduceIte]
    refine ⟨fs "da_factors__L13_L7_L0", c1 + 128, fun i => c ≤ i ∧ i < c + 14, fun i => c1 ≤ i ∧ i < c1 + 128,
      fun rd => HoldsWords rd [(c1, facCells (zsVal z) 13 7)], fun i hi => hR28 i hi.1 (by omega), ?_, ?_⟩
    · exact (facTop_callAtA k (zsVal z) c (R := fun i => c ≤ i ∧ i < c + 14) (fun d hd => ⟨by omega, by omega⟩)
        fp1 c1).mono (fun _ h => h) (fun _ h => h) (fun _ h => h)
        (fun rd h d hd => hzs rd h.2 _ (by omega)) (fun _ _ _ _ => trivial)
    rw [KidsAtF]; simp only [↓reduceIte]
    refine ⟨fs "da_expand__L13_L7", fp2 + fs "da_expand__L13_L7",
      fun i => (c ≤ i ∧ i < c + 28) ∨ (c1 ≤ i ∧ i < c1 + 128), fun i => bt ≤ i ∧ i < bt + 256,
      fun rd => HoldsWords rd [(bt, topRun z)], fun i hi => ?_, ?_, ?_⟩
    · rcases hi with hi | hi
      · rcases hR28 i hi.1 hi.2 with h | h
        · exact Or.inl h
        · exact h.elim
      · exact Or.inr (Or.inr hi)
    · show CallAtA _ _ _ _ _ [1, gen ^ c1, gen ^ c, gen ^ (c + 14)] [gen ^ (bt + 128)] _ _ _ _ _ _ _ _ _
      exact (expTop_callAtA hE k 1 (factorAt (zsVal z) 13) (zsVal z) (fun _ => 0)
        (R := fun i => (c ≤ i ∧ i < c + 28) ∨ (c1 ≤ i ∧ i < c1 + 128))
        (fun n h1 h2 => Or.inr ⟨by omega, by omega⟩) (fun d hd => Or.inl ⟨by omega, by omega⟩)
        (fun d hd => Or.inl ⟨by omega, by omega⟩) fp2 (fp2 + fs "da_expand__L13_L7")).mono
        (fun _ h => h) (fun _ h => h) (fun _ h => h)
        (fun rd h => ⟨fun n h1 h2 => hfac rd h.2.2 n h1 h2, fun d hd => hzs rd h.2.1 _ (by omega),
          fun d hd => hab rd h.2.1 _ (by omega)⟩) (fun _ _ _ _ => trivial)
    rw [KidsAtF]; simp only [↓reduceIte]
    refine ⟨fs "da_factors__L6_L7_L128", bc + 128, fun i => c ≤ i ∧ i < c + 14, fun i => bc ≤ i ∧ i < bc + 128,
      fun rd => HoldsWords rd [(bc, facCells (zsVal z) 6 7)], fun i hi => (hR28 i hi.1 (by omega)).imp_right
        (fun h => h.elim), ?_, ?_⟩
    · exact (facCell_callAtA k (zsVal z) c (R := fun i => c ≤ i ∧ i < c + 14) (fun d hd => ⟨by omega, by omega⟩)
        fp3 bc).mono (fun _ h => h) (fun _ h => h) (fun _ h => h)
        (fun rd h d hd => hzs rd h.2.1.1 _ (by omega)) (fun _ _ _ _ => trivial)
    rw [KidsAtF]; simp only [↓reduceIte]
    refine ⟨fs "da_column_offsets", offFold fs al (List.range 7) (bo + 945), fun i => c ≤ i ∧ i < c + 14,
      fun i => bo ≤ i ∧ i < bo + 896, fun rd => HoldsWords rd [(bo, offCells (zsVal z))],
      fun i hi => (hR28 i hi.1 (by omega)).imp_right (fun h => h.elim), ?_, ?_⟩
    · exact (off_callAtA k (zsVal z) c (R := fun i => c ≤ i ∧ i < c + 14) (fun j hj => ⟨by omega, by omega⟩)
        (fp := fp4) (c := bo) le_rfl).mono (fun _ h => h) (fun _ h => h) (fun _ h => h)
        (fun rd h j hj => hzs rd h.2.1.1.1 _ (by omega)) (fun _ _ _ _ => trivial)
    rw [KidsAtF]
    refine ⟨rfl, fun _ h => h, fun i hi => ?_⟩
    rcases hi with hi | hi | hi
    · exact Or.inl (Or.inl (Or.inr hi))
    · exact Or.inl (Or.inr hi)
    · exact Or.inr hi
  · -- the words returned
    intro rd h
    obtain ⟨⟨⟨⟨h0, h1⟩, h2⟩, h3⟩, h4⟩ := h
    intro q hq
    simp only [vecWords, List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact h0 _ List.mem_cons_self
    · exact h2 _ List.mem_cons_self
    · exact h3 _ List.mem_cons_self
    · exact h4 _ List.mem_cons_self
  · -- the atoms
    intro rd _ _ hO ev hev
    have hz := hzs rd hO.1.1.1.1
    have ha := hab rd hO.1.1.1.1
    have hzv : ∀ j v, j < 14 → zsVal z j = v → LoadHolds rd (gen ^ c) j v := fun j v hj hv => hv ▸ hz j hj
    have hav : ∀ j v, j < 14 → v = 0 → LoadHolds rd (gen ^ (c + 14)) j v := fun j v hj hv => hv ▸ ha j hj
    exact events_straight (vec_sholds z c _ _ _ _ hzv hav) ev hev

/-- **`da_vector` completes placed** (`DaVectorCompleteA`), wherever its top tree's run lies in its frame. -/
theorem daVectorCompleteA (hfs : ∀ g, fs g < 2 ^ 16) (hE : ExpCert fs cert "da_expand__L13_L7") (k : ℕ) :
    DaVectorCompleteA fs al cert k := by
  intro z fp c hfc
  obtain ⟨bt, bc, bo, e, he, h⟩ := vec_callAtA (al := al) hfs hE k z hfc
  exact ⟨c, bt, bc, bo, e, he, h.free da_vector_free.1 da_vector_free.2⟩

/-- **`da_vector` completes placed at the compiled frames.** -/
theorem daVectorCompleteA_b2c (al : String → Bool) (k : ℕ) : DaVectorCompleteA B2C.fs al B2C.cert k :=
  daVectorCompleteA fs_lt16 expTopCert_b2c k

end
end LeanVM.Guest.Complete
