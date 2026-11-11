/-
  LeanVM.Guest.B1.Da.VecAt

  `da_vector` placed (G:4396-4415): its two `HeapBuf`s (`zs`, `above_top`), its four callees on
  them, the powers, the top leaves, the cell factors and the column offsets returned, within its
  frame, its buffers and its callees' bounds.
-/

module

public import LeanVM.Guest.B1.Da.VecCChk
public import LeanVM.Guest.B1.Da.FacAt
public import LeanVM.Guest.B1.Da.ExpAt
public import LeanVM.Guest.B1.Da.OffAt
public import LeanVM.Guest.B1.Da.FlatOut

/-!
# `da_vector`, placed

Its buffers at `bz = fp + fs da_vector`: `zs` (`zsCells z`), `above_top` (zeros) at `bz + 15`. Its
callees: the top factors and the cell factors on `zs` (`fac14_completeAtB`, `fac7_completeAtB`),
the top tree from `1` on the top factors, `zs` and `above_top` (`exp7_completeAtB`, the factors'
buffer read off the first callee's result, `outB`), the column offsets on `zs`
(`off_completeAtB`). The valuation is explicit (`vecVals`). `vec_completeAtB`: complete, placed,
within `vecB fs SK`, returning `vecOut z`.
-/

namespace LeanVM.Guest.B1.Da

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Memory
open LeanVM.Protocol.Verifier (gen eOfNat)
open LeanVM.Guest.B1.Fwd LeanVM.Guest.B1.Digest
open LeanVM.Guest.B1 (CompleteAtDTB Kid KidD kidsAt outsL KidsDepBP OutsOk RegionsOk CallsMatch
  Returns completeAt_flatDepOut flatCalls)
open LeanVM.Guest.B1.Main (Layout MemL RegionL iterK)

@[expose] public section

/-- `da_vector`'s callees' words bounds: the factors' frames and buffers, the top tree's frame,
the offsets'. -/
def vecBs (fs : String → ℕ) (SK : String → ℕ) : List ℕ :=
  [fs "da_factors__L14_L7_L0" + 256, fs "da_expand__L14_L7", fs "da_factors__L7_L8_L128" + 256,
    fs "da_column_offsets" + 1080 + offKB fs SK]

/-- **`da_vector`'s words bound**: its frame, its two buffers, its callees'. -/
def vecB (fs : String → ℕ) (SK : String → ℕ) : ℕ := fs "da_vector" + 30 + (vecBs fs SK).sum

/-- The first callee's factors: their buffer's base. -/
noncomputable def vecBf (z : E) (pv : List (List E × Layout)) : ℕ :=
  outB (fun b rets Lo => rets = [gen ^ b] ∧ (b, facCells (zsVal z) 14 7) ∈ Lo) (pv.headD ([], []))

/-- `da_vector`'s callees at `bz`. -/
noncomputable def vecKids (z : E) (bz : ℕ) : List KidD :=
  [fun _ => ⟨"da_factors__L14_L7_L0", true, [gen ^ bz], [(bz, zsCells z)], facOut (zsVal z) 14 7⟩,
    fun pv => ⟨"da_expand__L14_L7", true, [1, gen ^ vecBf z pv, gen ^ bz, gen ^ (bz + 15)],
      [(bz, zsCells z), (bz + 15, aboveCells), (vecBf z pv, facCells (zsVal z) 14 7)],
      expOut 1 (factorAt (zsVal z) 14) (zsVal z) (fun _ => 0) 14 7⟩,
    fun _ => ⟨"da_factors__L7_L8_L128", true, [gen ^ bz], [(bz, zsCells z)], facOut (zsVal z) 7 8⟩,
    fun _ => ⟨"da_column_offsets", true, [gen ^ bz], [(bz, zsCells z)], offOut (zsVal z)⟩]

/-- `da_vector`'s returns on its callees' results. -/
def vecRets (bz : ℕ) (outs : List (List E × Layout)) : List E :=
  [gen ^ bz, ((outs.getD 1 ([], [])).1).headD 0, ((outs.getD 2 ([], [])).1).headD 0,
    ((outs.getD 3 ([], [])).1).headD 0]

/-- `da_vector`'s valuation. -/
def vecVals (z : E) (bz r25 r27 r28 r29 : E) : List E :=
  [z, bz, z ^ 2 ^ 1, z ^ 2 ^ 2, z ^ 2 ^ 3, z ^ 2 ^ 4, z ^ 2 ^ 5, z ^ 2 ^ 6, z ^ 2 ^ 7, z ^ 2 ^ 8,
    z ^ 2 ^ 9, z ^ 2 ^ 10, z ^ 2 ^ 11, z ^ 2 ^ 12, z ^ 2 ^ 13, z ^ 2 ^ 14, 0, bz * gen ^ 15,
    0, 0, 0, 0, 0, 0, 0, r25, 1, r27, r28, r29, bz, r27, r28, r29]

theorem zsCells_get {z : E} {j : ℕ} (hj : j < 15) :
    (zsCells z)[j]'(by simp [zsCells]; exact hj) = zsVal z j := by
  simp [zsCells]

set_option maxRecDepth 20000 in
/-- **`da_vector`'s statements hold** on its valuation, `zs` and `above_top` holding their words. -/
theorem vec_sholds {rd : Reader} (z bz r25 r27 r28 r29 : E)
    (hzv : ∀ j v, j < 15 → zsVal z j = v → LoadHolds rd bz j v)
    (hav : ∀ j v, j < 15 → v = 0 → LoadHolds rd (bz * gen ^ 15) j v) :
    ∀ s ∈ vecP, SHolds (fun _ _ _ => True) rd (Val.ofArgs (vecVals z bz r25 r27 r28 r29)) s := by
  intro s hs
  simp only [vecP, Data.core31, Data.core31.body, List.dropLast_cons_cons, List.dropLast_singleton,
    List.mem_cons, List.not_mem_nil, or_false] at hs
  rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals simp only [SHolds, Atom.Holds, ofArgs_n, vecVals, List.getD_cons_succ,
    List.getD_cons_zero]
  all_goals first | exact word_zero.symm | exact word_one.symm |
    (refine hzv _ _ (by norm_num) (by simp [zsVal])) | (refine hav _ _ (by norm_num) rfl) | ring

variable (fs : String → ℕ) (cert : String → V → ℕ)

set_option maxRecDepth 20000 in
/-- **`da_vector` is complete, placed, within `vecB fs SK`**, returning the powers, the top tree's
run, the cell factors and the column offsets of `z`. -/
theorem vec_completeAtB (hrf : Lift.RunsFit fs cert) {SK : String → ℕ}
    (hT : ∀ b < 7, TotalLeOn coreProgram fs (offLoopName b) LoopPre
      (fun a => logG (a.getD 1 0) * iterK fs SK (offLoopName b) + fs (offLoopName b)))
    (Lin : Layout) (z : E) :
    CompleteAtDTB fs cert 16 "da_vector" Lin [z] (vecOut z) (fun _ => True) (vecB fs SK) := by
  have hcok := vec_cok
  unfold vecCOk at hcok
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hcok
  obtain ⟨⟨⟨⟨⟨⟨hflat, hnd⟩, hni⟩, haddr⟩, halloc⟩, hcalls⟩, hloads⟩ := hcok
  have hb : Fn.body Data.core31 = vecP ++ [.ret [.n 30, .n 31, .n 32, .n 33]] := rfl
  -- the reads every callee needs of `zs` and `above_top`
  have hzsR : ∀ {rd : Reader} {bz : ℕ} {L : Layout}, (bz, zsCells z) ∈ L → MemL rd L →
      ∀ j < 15, LoadHolds rd (gen ^ bz) j (zsVal z j) := fun hq hm j hj => by
    have := reads_of_memL hm hq j (by simp [zsCells]; exact hj)
    rwa [zsCells_get hj] at this
  have hzsr : ∀ {bz : ℕ} {L : Layout}, (bz, zsCells z) ∈ L → ∀ j < 15, RegionL L (bz + j) :=
    fun hq j hj => regionL_of_mem hq (by simp [zsCells]; exact hj)
  refine (completeAt_flatDepOut (fs := fs) (cert := cert) find_da_vector
    (by rw [Program.loop_of_find? find_da_vector]; decide +kernel) 16 Lin [z]
    (fun fp outs => vecRets (fp + fs "da_vector") outs) (vecOut z) hb hflat haddr hni [15, 15]
    (fun _ => [zsCells z, aboveCells]) (fun _ => by simp [zsCells, aboveCells])
    (fun fp => vecKids z (fp + fs "da_vector"))
    ["da_factors__L14_L7_L0", "da_expand__L14_L7", "da_factors__L7_L8_L128", "da_column_offsets"]
    (vecBs fs SK) [fun _ => True, fun _ => True, fun _ => True, fun _ => True] (fun _ => True)
    (fun _ => .cons (fun _ => rfl) (.cons (fun _ => rfl) (.cons (fun _ => rfl)
      (.cons (fun _ => rfl) .nil))))
    (fun fp => ?_) (fun fp outs hlen ho => ?_) (fun fp outs ho => ?_)
    (fun fp outs ho rd _ hB _ hO => ?_) ?_).mono (by simp [vecB]) fun _ _ => trivial
  · -- the callees, within their bounds
    set bz := fp + fs "da_vector"
    refine ⟨fun pv => ⟨fun _ => ?_, fun h => absurd h (by simp)⟩,
      fun pv => ⟨fun _ => ?_, fun h => absurd h (by simp)⟩,
      fun pv => ⟨fun _ => ?_, fun h => absurd h (by simp)⟩,
      fun pv => ⟨fun _ => ?_, fun h => absurd h (by simp)⟩, trivial⟩
    · exact fac14_completeAtB fs cert (fun rd hm d hd => hzsR List.mem_cons_self hm _ (by omega))
        (fun d hd => hzsr List.mem_cons_self _ (by omega))
    · refine exp7_completeAtB fs cert hrf (fun rd hm n h1 h2 => ?_)
        (fun rd hm d hd => hzsR List.mem_cons_self hm _ (by omega)) (fun rd hm d hd => ?_)
        (fun n h1 h2 => ?_) (fun d hd => hzsr List.mem_cons_self _ (by omega)) (fun d hd => ?_)
      · have := reads_of_memL hm (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
          List.mem_cons_self)) n (by simp [facCells]; omega)
        rwa [facCells_get h1 h2 (by norm_num)] at this
      · have := reads_of_memL hm (List.mem_cons_of_mem _ List.mem_cons_self) (14 - d)
          (by simp [aboveCells]; omega)
        simpa only [aboveCells, List.getElem_replicate] using this
      · exact regionL_of_mem (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))
          (by simp [facCells]; omega)
      · exact regionL_of_mem (List.mem_cons_of_mem _ List.mem_cons_self) (by simp [aboveCells]; omega)
    · exact fac7_completeAtB fs cert (fun rd hm d hd => hzsR List.mem_cons_self hm _ (by omega))
        (fun d hd => hzsr List.mem_cons_self _ (by omega))
    · exact off_completeAtB fs cert (fun rd hm j hj => hzsR List.mem_cons_self hm _ (by omega))
        (fun j hj => hzsr List.mem_cons_self _ (by omega)) hT
  · -- the returns
    set bz := fp + fs "da_vector"
    match outs, hlen, ho with
    | [o1, o2, o3, o4], _, ho =>
      obtain ⟨h1, h2, h3, h4, -⟩ := ho
      obtain ⟨b1, e1, m1⟩ := h1 rfl
      obtain ⟨bt, e2, m2⟩ := h2 rfl
      obtain ⟨bc, e3, m3⟩ := h3 rfl
      obtain ⟨bo, e4, m4⟩ := h4 rfl
      refine ⟨bz, bt, bc, bo, ?_, ?_, ?_, ?_, ?_⟩
      · simp [vecRets, e2, e3, e4]
      · exact List.mem_append_left _ List.mem_cons_self
      · simp only [kidsAt, outsL, vecKids, ↓reduceIte, List.mem_append]
        exact Or.inr (Or.inr (Or.inl m2))
      · simp only [kidsAt, outsL, vecKids, ↓reduceIte, List.mem_append]
        exact Or.inr (Or.inr (Or.inr (Or.inl m3)))
      · simp only [kidsAt, outsL, vecKids, ↓reduceIte, List.mem_append]
        exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl m4))))
  · -- the callees' regions
    set bz := fp + fs "da_vector"
    have hown : ∀ {xs : List E} {b : ℕ}, (b, xs) ∈ [(bz, zsCells z), (bz + 15, aboveCells)] →
        ∀ i, RegionL [(b, xs)] i → RegionL (bufL bz [15, 15] [zsCells z, aboveCells]) i :=
      fun hq i ⟨q, hq', h1, h2⟩ => ⟨q, by rw [List.mem_singleton] at hq'; subst hq'; exact hq, h1, h2⟩
    match outs, ho with
    | [], _ => trivial
    | o1 :: os, ho =>
      have hf := outB_spec (P := fun b rets Lo => rets = [gen ^ b] ∧ (b, facCells (zsVal z) 14 7) ∈ Lo)
        (o := o1) (ho.1 rfl)
      have hzR : ∀ i, RegionL [(bz, zsCells z)] i → RegionL Lin i ∨
          RegionL (bufL bz [15, 15] [zsCells z, aboveCells]) i :=
        fun i hi => Or.inr (hown List.mem_cons_self i hi)
      refine ⟨fun _ i hi => Or.inl (hzR i hi), ?_⟩
      match os with
      | [] => trivial
      | o2 :: os =>
        refine ⟨fun _ i hi => ?_, ?_⟩
        · obtain ⟨q, hq, hq1, hq2⟩ := hi
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
          rcases hq with rfl | rfl | rfl
          · exact Or.inl (Or.inr (hown List.mem_cons_self i ⟨_, List.mem_singleton_self _, hq1, hq2⟩))
          · exact Or.inl (Or.inr (hown (List.mem_cons_of_mem _ List.mem_cons_self) i
              ⟨_, List.mem_singleton_self _, hq1, hq2⟩))
          · exact Or.inr (Or.inr ⟨rfl, _, by simpa [vecBf] using hf.2, hq1, hq2⟩)
        match os with
        | [] => trivial
        | o3 :: os =>
          refine ⟨fun _ i hi => Or.inl (hzR i hi), ?_⟩
          match os with
          | [] => trivial
          | o4 :: os => exact ⟨fun _ i hi => Or.inl (hzR i hi), by cases os <;> trivial⟩
  · -- what the callees read
    set bz := fp + fs "da_vector"
    intro q hq
    have hzq : (bz, zsCells z) ∈ bufL bz [15, 15] [zsCells z, aboveCells] := List.mem_cons_self ..
    have haq : (bz + 15, aboveCells) ∈ bufL bz [15, 15] [zsCells z, aboveCells] :=
      List.mem_cons_of_mem _ List.mem_cons_self
    match outs, ho with
    | [], _ => simp [kidsAt, B1.Kid.lins] at hq
    | o1 :: os, ho =>
      have hf := outB_spec (P := fun b rets Lo => rets = [gen ^ b] ∧ (b, facCells (zsVal z) 14 7) ∈ Lo)
        (o := o1) (ho.1 rfl)
      have hfq : (vecBf z [o1], facCells (zsVal z) 14 7) ∈
          outsL (kidsAt (vecKids z bz) [] (o1 :: os)) (o1 :: os) := by
        simp only [kidsAt, outsL, vecKids, ↓reduceIte, List.mem_append]
        exact Or.inl (by simpa [vecBf] using hf.2)
      have hq' : q = (bz, zsCells z) ∨ q = (bz + 15, aboveCells) ∨
          q = (vecBf z [o1], facCells (zsVal z) 14 7) := by
        rcases os with _ | ⟨o2, _ | ⟨o3, _ | ⟨o4, os⟩⟩⟩ <;>
          simp [kidsAt, B1.Kid.lins, vecKids] at hq <;> tauto
      rcases hq' with rfl | rfl | rfl
      · exact hB _ hzq
      · exact hB _ haq
      · exact hO _ hfq
  · -- the valuation
    intro fp outs hlen ho rd _ hB _ _
    set bz := fp + fs "da_vector"
    match outs, hlen, ho with
    | [o1, o2, o3, o4], _, ho =>
      obtain ⟨h1, h2, h3, h4, -⟩ := ho
      have hf := outB_spec (P := fun b rets Lo => rets = [gen ^ b] ∧ (b, facCells (zsVal z) 14 7) ∈ Lo)
        (o := o1) (h1 rfl)
      obtain ⟨b1, e1, -⟩ := h1 rfl
      obtain ⟨bt, e2, -⟩ := h2 rfl
      obtain ⟨bc, e3, -⟩ := h3 rfl
      obtain ⟨bo, e4, -⟩ := h4 rfl
      have hbf : gen ^ vecBf z [o1] = gen ^ b1 := by
        have := hf.1.symm.trans e1
        simpa [vecBf] using this
      obtain ⟨σ, hσ⟩ : ∃ σ : Val, σ = Val.ofArgs (vecVals z (gen ^ bz) (gen ^ b1)
          (gen ^ (bt + 2 ^ 7)) (gen ^ bc) (gen ^ bo)) := ⟨_, rfl⟩
      have hzv : ∀ j v, j < 15 → zsVal z j = v → LoadHolds rd (gen ^ bz) j v := fun j v hj hv => by
        rw [← hv]; exact hzsR List.mem_cons_self hB j hj
      have hav : ∀ j v, j < 15 → v = 0 → LoadHolds rd (gen ^ bz * gen ^ 15) j v := fun j v hj hv => by
        have := reads_of_memL hB (List.mem_cons_of_mem _ List.mem_cons_self) j
          (by simp [aboveCells]; exact hj)
        rw [hv, ← pow_add]
        simpa only [aboveCells, List.getElem_replicate] using this
      have hall := vec_sholds (rd := rd) z (gen ^ bz) (gen ^ b1) (gen ^ (bt + 2 ^ 7)) (gen ^ bc)
        (gen ^ bo) hzv hav
      rw [← hσ] at hall
      have s1 : σ (.n 1) = gen ^ bz := by rw [hσ]; rfl
      have s17 : σ (.n 17) = gen ^ (bz + 15) := by
        rw [hσ]; exact (pow_add gen bz 15).symm
      have hcs : vecP.filterMap (Stmt.callSF σ) = vecCalls := by
        rw [← hcalls]
        refine List.filterMap_congr fun s hs => ?_
        have := List.all_eq_true.mp hnd s hs
        cases s with
        | dispatch => simp [noDispatch] at this
        | _ => rfl
      refine ⟨σ, by rw [hσ]; rfl, fun s hs => ?_, ?_, ?_, ?_, ?_, ?_, trivial⟩
      · have := List.all_eq_true.mp hnd s hs
        cases s with
        | dispatch => simp [noDispatch] at this
        | _ => trivial
      · rw [hb]
        refine holdsList_straight _ _ _ _ hall ?_
        simp [hσ, ofArgs_n, vecVals, vecRets, e2, e3, e4]
      · rw [halloc]; rfl
      · rw [halloc]
        simp [s1, s17, bases, gen_pow_eq_ofK]
      · simp only [flatCalls, hcs, vecCalls, List.map_cons, List.map_nil, Main.mkCall, kidsAt,
          vecKids]
        refine ⟨rfl, rfl, fun _ => ⟨?_, ?_⟩, rfl, rfl, fun _ => ⟨?_, ?_⟩, rfl, rfl, fun _ => ⟨?_, ?_⟩,
          rfl, rfl, fun _ => ⟨?_, ?_⟩, trivial⟩
        all_goals simp [hσ, ofArgs_n, vecVals, e1, e2, e3, e4, hbf, pow_add]
      · rw [hloads]
        intro q hq
        simp only [vecLoads, List.mem_append, List.mem_map, List.mem_range] at hq
        rcases hq with ⟨j, hj, rfl⟩ | ⟨i, hi, rfl⟩
        · exact ⟨bz + j, by rw [s1]; exact limb0_gen_pow_mul _ _, Or.inr (Or.inl
            (regionL_of_mem (List.mem_cons_self ..) (by simp [zsCells]; exact hj)))⟩
        · refine ⟨bz + 15 + (8 + i), ?_, Or.inr (Or.inl (regionL_of_mem
            (List.mem_cons_of_mem _ (List.mem_cons_self ..)) (by simp [aboveCells]; omega)))⟩
          rw [s17]; exact limb0_gen_pow_mul _ _

end
end LeanVM.Guest.B1.Da
