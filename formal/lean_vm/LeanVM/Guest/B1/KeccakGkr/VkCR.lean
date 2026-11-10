/-
  LeanVM.Guest.B1.KeccakGkr.VkCR

  Where `verify_keccak` loads, on its layout.
-/

module

public import LeanVM.Guest.B1.KeccakGkr.VkCQ

/-!
# The loads, on the layout

`vk_loads`: every load of the body is through one of the pointers `vkGroups` lists, at an offset in
its range (a kernel check). `loads_in`: on the layout, each lands in the caller's words, the
buffers or a layer's buffers.
-/

namespace LeanVM.Guest.B1.VerifySub

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Guest.Memory LeanVM.Guest.B1.Fwd
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Protocol.KeccakGkr Finset
open LeanVM.Guest.B1.Main (MemL RegionL)

@[expose] public section

/-- Step `s`'s pointers: its claim's point's segment coordinate, its flips. -/
def stepGroups (s : ℕ) : List (V × ℕ × ℕ) :=
  [(.n (stepB s + 1), 0, 1)] ++
    if s = 0 then [] else (List.range (iotaUsed s).length).map fun j ↦ (.n (stepB s + 6 + 2 * j), 0, 7)

/-- The pointers the body loads through, with their offsets' ranges. -/
def vkGroups : List (V × ℕ × ℕ) :=
  [(.n 5, 0, 1), (.n 7, 0, 4), (.n 8, 0, 25), (.n 9, 0, 4), (.n 9, 39, 43), (.n 10, 0, 64),
    (.n 67, 0, 1), (.n 87, 0, 5), (.n 161, 0, 286), (.n 163, 0, 30), (.n 234, 0, 62),
    (.n 342, 0, 2), (.n 921, 0, 6), (.n 929, 0, 1), (.n 934, 0, 1), (.n 1210, 0, 30),
    (.n 1338, 0, 64), (.n 1330, 0, 6), (.n 1746, 0, 1), (.n 1980, 0, 6), (.n 3143, 0, 25)] ++
    (List.range 12).flatMap stepGroups

/-- A load through one of `vkGroups`. -/
def inGroups (q : V × ℕ) : Bool :=
  vkGroups.any fun g ↦ g.1 == q.1 && decide (g.2.1 ≤ q.2) && decide (q.2 < g.2.2)

theorem vk_loads : (vkPre.filterMap Stmt.loadS).all inGroups = true := by decide +kernel

/-- A load at `ptr a` and `off`, inside an entry of a layout. -/
theorem reg_at {L : Main.Layout} {b : ℕ} {ws : List E} (hq : (b, ws) ∈ L) {T : ℕ → Prop}
    (hT : ∀ i, RegionL L i → T i) {p : E} {a off : ℕ} (hp : p = ptr a) (h1 : b ≤ a + off)
    (h2 : a + off < b + ws.length) :
    ∃ i, p.limb 0 * Parameters.addressOfIndex off = Parameters.addressOfIndex i ∧ T i :=
  ⟨a + off, by rw [hp]; exact Main.addr_ofK a off, hT _ ⟨(b, ws), hq, h1, h2⟩⟩

namespace VkData

variable {D : VkData} {rd : Reader} {B curE chiE olE zvE slE tbE : ℕ} {ls : ℕ → ℕ}

theorem claims_length (h : D.Ok) : (D.claims B ls).length = 286 := by
  rw [claims, List.length_append, cw0_length h, List.length_flatMap]
  simp [outWs_length]

set_option maxRecDepth 20000 in
/-- **Every load lands in the layout.** -/
theorem loads_in (h : D.Ok) (hm : D.Mem rd B curE chiE olE zvE slE tbE ls) {σ : Val}
    (hσd : σ = D.val rd B curE chiE olE zvE slE tbE) {T : ℕ → Prop}
    (hLin : ∀ i, RegionL (D.lin curE chiE olE zvE slE tbE) i → T i)
    (hOwn : ∀ i, RegionL (bufL B D.sizes (D.own B ls)) i → T i)
    (hLay : ∀ s < 12, ∀ i,
      RegionL (layerBufs (D.layer s) (firstOf s) (ptr (curE + D.lcur s)) (ls s)) i → T i) :
    ∀ q ∈ vkPre.filterMap Stmt.loadS,
      ∃ i, (σ q.1).limb 0 * Parameters.addressOfIndex q.2 = Parameters.addressOfIndex i ∧ T i := by
  have hτ1 := h.1
  have hτ2 := h.2.1
  have hchis := h.2.2.1
  have houts : D.outs.length = 25 := h.2.2.2.1
  have hslL : D.slices.length = 64 := h.2.2.2.2.2.2.2.2.2.1
  obtain ⟨-, p5, p6, p7, p8, p9, p10, h17, -, -, a58, -, -, -, e64, -, a90, -, -, -, a201, a203,
    a274, a382, -⟩ := head_first h hm hσd
  obtain ⟨-, -, e3691, -, -, eO, -⟩ := out_on h hm hσd p6 p9 h17 a58 a274
  have e3699 : σ (.n 929) = ptr (curE + D.lcur 12 + 12) := by
    have := eO 5 (by norm_num)
    rw [this, oRets, List.getD_append_right _ _ _ _ (by rw [(O_ok h).2]), (O_ok h).2]
    simp [cL, ptr_mul_gen]
  obtain ⟨-, -, -, -, -, e4107, -, -, e4110, -⟩ := in_on h hm hσd p6 p9 p10 a201 e3699
  have e4115 : σ (.n 1338) = ptr (curE + D.lcur 12 + 33) := by
    rw [show (1338 : ℕ) = 1333 + 5 from rfl, e4110 5 (by norm_num), sRets,
      List.getD_append_right _ _ _ _ (by rw [(S_ok h).2]), (S_ok h).2]
    simp only [Nat.sub_self, List.getD_cons_zero, cL, ptr_mul_gen, ptr_mul_gen1]
  obtain ⟨e4978, e5212, e6363⟩ := fin_ptrs h hm hσd h17 a201
  have e3711 : σ (.n 934) = ptr B * gen ^ (D.τ - 4) := by
    have g : Good rd vkSt (D.w B curE) σ (.mul (.n 934) (.n 61) (.n 18)) := by
      subst hσd
      exact val_good' h (s := .atom (.mul (.n 934) (.n 61) (.n 18)))
        (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ (by simp [vkOutT]))))
    rw [mulG (by norm_num) (by norm_num) g, a58, h17]
  have a3987 : σ (.n 1210) = ptr (B + D.τ + 382) := by
    subst hσd; exact val_alloc h (.n 1210, .inl 30) (by simp [vkAllocs])
  -- the entries
  have mLin : ∀ {b ws}, (b, ws) ∈ [(curE, D.xs), (chiE, D.chis), (olE, D.outs), (zvE, D.op),
      (zvE + qkeccakVarsCap, D.point), (slE, D.slices), (tbE, winTabWords)] →
      ∀ {p : E} {a off : ℕ}, p = ptr a →
      b ≤ a + off → a + off < b + ws.length →
      ∃ i, p.limb 0 * Parameters.addressOfIndex off = Parameters.addressOfIndex i ∧ T i :=
    fun hq _ _ _ hp h1 h2 ↦ reg_at hq hLin hp h1 h2
  have mOwn : ∀ {b ws}, (b, ws) ∈ bufL B D.sizes (D.own B ls) → ∀ {p : E} {a off : ℕ}, p = ptr a →
      b ≤ a + off → a + off < b + ws.length →
      ∃ i, p.limb 0 * Parameters.addressOfIndex off = Parameters.addressOfIndex i ∧ T i :=
    fun hq _ _ _ hp h1 h2 ↦ reg_at hq hOwn hp h1 h2
  have hO := bufL_eq (D := D) (by omega) B ls
  have mLay : ∀ s < 12, ∀ {b ws},
      (b, ws) ∈ layerBufs (D.layer s) (firstOf s) (ptr (curE + D.lcur s)) (ls s) →
      ∀ {p : E} {a off : ℕ}, p = ptr a → b ≤ a + off → a + off < b + ws.length →
      ∃ i, p.limb 0 * Parameters.addressOfIndex off = Parameters.addressOfIndex i ∧ T i :=
    fun s hs _ _ hq _ _ _ hp h1 h2 ↦ reg_at hq (hLay s hs) hp h1 h2
  intro q hq
  have hg := List.all_eq_true.mp vk_loads q hq
  simp only [inGroups, List.any_eq_true, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hg
  obtain ⟨⟨gp, lo, hi⟩, hgm, ⟨hp, hlo⟩, hhi⟩ := hg
  obtain ⟨p, off⟩ := q
  simp only at hp hlo hhi ⊢
  subst hp
  simp only [vkGroups, List.mem_append, List.mem_cons, List.not_mem_nil, or_false,
    List.mem_flatMap, List.mem_range, Prod.mk.injEq] at hgm
  have hy : ∀ k < 12, (D.layer k).y = D.τ - 3 := fun k hk ↦ D.layer_y h hk.le
  have hchs : ∀ k < 12, ((D.layer k).chs (firstOf k)).length = D.τ - 3 := fun k hk ↦ by
    obtain ⟨-, hpm, -⟩ := D.layer_facts h hk
    rw [LayerData.chs_length hpm, hy k hk]
  have hlocL : ∀ k < 12, ((D.layer k).locPt (firstOf k)).length = 11 := fun k hk ↦ locPt_length h hk
  have hpL := point_length h
  have hoL := op_length h
  have hxL := xs_length h
  have hc0 := c0_point_length h
  rcases hgm with (⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ |
    ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ |
    ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ |
    ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ |
    ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩) | ⟨s, hs, hsg⟩
  · exact mLin (b := curE) (ws := D.xs) (by simp) p5 (by omega) (by omega)
  · exact mLin (b := chiE) (ws := D.chis) (by simp) p7 (by omega) (by omega)
  · exact mLin (b := olE) (ws := D.outs) (by simp) p8 (by omega) (by omega)
  · exact mLin (b := zvE) (ws := D.op) (by simp) p9 (by omega) (by omega)
  · exact mLin (b := zvE + qkeccakVarsCap) (ws := D.point) (by simp) p9 (by unfold qkeccakVarsCap; omega)
      (by unfold qkeccakVarsCap; omega)
  · exact mLin (b := slE) (ws := D.slices) (by simp) p10 (by omega) (by omega)
  · exact mOwn (b := B) (ws := D.c0.point) (by rw [hO]; simp) (by rw [e64, ptr_mul_gen])
      (by omega) (by omega)
  · exact mOwn (b := B + (D.τ - 3)) (ws := D.rl) (by rw [hO]; simp) a90 (by omega)
      (by rw [rl_length]; omega)
  · exact mOwn (b := B + D.o201) (ws := D.claims B ls) (by rw [hO]; simp) a201 (by omega)
      (by rw [claims_length h]; omega)
  · exact mOwn (b := B + D.τ + 288) (ws := eqLevels (D.chis.take 4) 4) (by rw [hO]; simp) a203
      (by omega) (by rw [eqLevels_length (by simp; omega)]; norm_num; omega)
  · exact mOwn (b := B + D.o274) (ws := eqLevels D.rl 5) (by rw [hO]; simp) a274 (by omega)
      (by rw [eqLevels_length (by rw [rl_length])]; norm_num; omega)
  · exact mOwn (b := B + D.τ + 380) (ws := eqKernel D.seg) (by rw [hO]; simp) a382 (by omega)
      (by rw [eqKernel_length, seg_length]; norm_num; omega)
  · exact mLin (b := zvE) (ws := D.op) (by simp) (by rw [e3691, ptr_mul_gen]) (by omega)
      (by omega)
  · exact mLin (b := curE) (ws := D.xs) (by simp) e3699 (by omega) (by omega)
  · exact mOwn (b := B) (ws := D.c0.point) (by rw [hO]; simp) (by rw [e3711, ptr_mul_gen])
      (by omega) (by omega)
  · exact mOwn (b := B + D.τ + 382) (ws := eqLevels D.I.1 4) (by rw [hO]; simp) a3987 (by omega)
      (by rw [eqLevels_length (by rw [I1_length h])]; norm_num; omega)
  · exact mLin (b := curE) (ws := D.xs) (by simp) e4115 (by omega) (by omega)
  · exact mLin (b := zvE + qkeccakVarsCap) (ws := D.point) (by simp)
      (by rw [e4107, ptr_mul_gen, ptr_mul_gen]) (by unfold qkeccakVarsCap; omega)
      (by unfold qkeccakVarsCap; omega)
  · exact mLay 11 (by norm_num) (b := ls 11) (ws := (D.layer 11).chs (firstOf 11))
      (by simp [layerBufs_eq]) (by rw [e4978, ptr_mul_gen]) (by omega)
      (by rw [hchs 11 (by norm_num)]; omega)
  · exact mLay 11 (by norm_num) (b := ls 11 + (D.layer 11).y + 128)
      (ws := (D.layer 11).locPt (firstOf 11)) (by simp [layerBufs_eq]) e5212 (by omega)
      (by rw [hlocL 11 (by norm_num)]; omega)
  · exact mLay 11 (by norm_num) (b := ls 11 + (D.layer 11).y + 139)
      (ws := lanesOut ((D.layer 11).locPt (firstOf 11)) ((D.layer 11).beta (firstOf 11)).1)
      (by simp [layerBufs_eq]) e6363 (by omega) (by rw [lanesOut_length]; omega)
  · -- a step's
    obtain ⟨hpp, hfl⟩ := step_ptrs h hm hσd hs h17 a201
    simp only [stepGroups, List.mem_append, List.mem_cons, List.not_mem_nil, or_false,
      Prod.mk.injEq] at hsg
    rcases hsg with ⟨rfl, rfl, rfl⟩ | hsg
    · rcases s with _ | k
      · exact mOwn (b := B) (ws := D.c0.point) (by rw [hO]; simp) (a := B + (D.τ - 4))
          (by rw [hpp, ptr_mul_gen]; rfl) (by omega) (by omega)
      · exact mLay k (by omega) (b := ls k) (ws := (D.layer k).chs (firstOf k))
          (by simp [layerBufs_eq]) (a := ls k + (D.τ - 4)) (by rw [hpp, ptr_mul_gen]; rfl)
          (by omega) (by rw [hchs k (by omega)]; omega)
    · rcases s with _ | k
      · simp at hsg
      · simp only [show k + 1 ≠ 0 by omega, ↓reduceIte, List.mem_map, List.mem_range,
          Prod.mk.injEq] at hsg
        obtain ⟨j, hj, rfl, rfl, rfl⟩ := hsg
        exact mLay k (by omega) (b := ls k + (D.layer k).y + 164)
          (ws := flipsOf (laterWeights (lanesOut ((D.layer k).locPt (firstOf k))
            ((D.layer k).beta (firstOf k)).1) (eqKernel (((D.layer k).locPt (firstOf k)).take 6))))
          (by simp [layerBufs_eq]) (a := ls k + (D.layer k).y + 164)
          (by rw [hfl (by omega) j hj]; rfl) (by omega) (by simp [flipsOf]; omega)

end VkData

end
end LeanVM.Guest.B1.VerifySub
