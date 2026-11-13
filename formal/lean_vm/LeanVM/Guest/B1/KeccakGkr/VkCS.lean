/-
  LeanVM.Guest.B1.KeccakGkr.VkCS

  `verify_keccak`'s callees' words, in memory and within the regions it holds.
-/

module

public import LeanVM.Guest.B1.KeccakGkr.VkCR

/-!
# The callees' words

`kid_lin_mem`: on the layout, the memory holds each callee's words (`KidG.Lin` at the frame
pointers so far); `kid_lin_region`: they lie in the caller's words, the buffers or the earlier
layers' buffers.
-/

namespace LeanVM.Guest.B1.VerifySub

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Guest.Memory LeanVM.Guest.B1.Fwd
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Protocol.KeccakGkr Finset
open LeanVM.Guest.B1.Main (MemL RegionL)

@[expose] public section

/-- A sub-entry's addresses are the entry's. -/
theorem region_sub {L : Main.Layout} {b b' : ℕ} {ws ws' : List E} (hq : (b, ws) ∈ L)
    (h1 : b ≤ b') (h2 : b' + ws'.length ≤ b + ws.length) {x : ℕ} (hx : RegionL [(b', ws')] x) :
    RegionL L x := by
  obtain ⟨q, hq', hx1, hx2⟩ := hx
  simp only [List.mem_singleton] at hq'
  subst hq'
  exact ⟨(b, ws), hq, by simp at hx1 ⊢; omega, by simp at hx2 ⊢; omega⟩

namespace VkData

variable {D : VkData}

theorem CL_congr (B : ℕ) {ls ls' : ℕ → ℕ} {s : ℕ} (h : ∀ k, k + 1 = s → ls k = ls' k) :
    D.CL B ls s = D.CL B ls' s := by
  rcases s with _ | k
  · rfl
  · simp only [CL, outWs, h k rfl]

theorem lsOf_take (fs : String → ℕ) (ps : List ℕ) {n k : ℕ} (hk : k + 1 < n) :
    D.lsOf fs (ps.take n) k = D.lsOf fs ps k := by
  simp only [lsOf, List.getD_eq_getElem?_getD, List.getElem?_take, show k + 1 < n from hk,
    ↓reduceIte]

variable {rd : Reader} {B curE chiE olE zvE slE tbE : ℕ} {fs : String → ℕ} {fps : List ℕ}

theorem take_last {s : ℕ} (hl : s + 2 ≤ fps.length) :
    (fps.take (s + 2)).getLast?.getD 0 = fps.getD (s + 1) 0 := by
  rw [List.getLast?_eq_getElem?, List.length_take, Nat.min_eq_left hl,
    show s + 2 - 1 = s + 1 by omega, List.getElem?_take]
  simp [List.getD_eq_getElem?_getD]

/-- **Layer `s`'s words, in memory.** -/
theorem layKid_lin_mem (h : D.Ok) (hm : D.Mem rd B curE chiE olE zvE slE tbE (D.lsOf fs fps))
    {s : ℕ} (hs : s < 12) (hl : s + 2 ≤ fps.length) :
    MemL rd ((D.layKid fs B curE tbE s).Lin (fps.take (s + 2))) := by
  have hdl : (fps.take (s + 2)).dropLast = fps.take (s + 1) := by
    rw [List.dropLast_eq_take, List.take_take, List.length_take]
    congr 1; omega
  have hCL : D.CL B (D.lsOf fs (fps.take (s + 1))) s = D.CL B (D.lsOf fs fps) s :=
    CL_congr B fun k hk ↦ lsOf_take fs fps (by omega)
  have hlast : (fps.take (s + 2)).getLast?.getD 0 + fs (D.lname s) = D.lsOf fs fps s := by
    rw [take_last hl]; rfl
  simp only [layKid, hdl, hCL, hlast]
  obtain ⟨-, -, m201, -⟩ := own_mem (by have := h.1; omega) hm.own
  obtain ⟨-, hlx, -⟩ := xs_reads h (memL_entry hm.lin (b := curE) (ws := D.xs) (by simp [lin]))
  intro q hq
  simp only [layerLin, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with ((rfl | rfl) | hq) | rfl
  · exact claims_slice h hs m201
  · exact hlx s hs
  · exact CL_mem h hm hs q hq
  · exact memL_entry hm.lin (by simp [lin])

/-- **Layer `s`'s words lie in the caller's words, the buffers or the previous layer's
buffers.** -/
theorem layKid_lin_region (h : D.Ok) {s : ℕ} (hs : s < 12) (hl : s + 2 ≤ fps.length)
    {T : ℕ → Prop} (hLin : ∀ i, RegionL (D.lin curE chiE olE zvE slE tbE) i → T i)
    (hOwn : ∀ i, RegionL (bufL B D.sizes (D.own B (D.lsOf fs fps))) i → T i)
    (hPrev : ∀ k, k + 1 = s → ∀ i, RegionL (layerBufs (D.layer k) (firstOf k)
      (ptr (curE + D.lcur k)) (D.lsOf fs fps k)) i → T i) :
    ∀ x, RegionL ((D.layKid fs B curE tbE s).Lin (fps.take (s + 2))) x → T x := by
  have hdl : (fps.take (s + 2)).dropLast = fps.take (s + 1) := by
    rw [List.dropLast_eq_take, List.take_take, List.length_take]
    congr 1; omega
  have hCL : D.CL B (D.lsOf fs (fps.take (s + 1))) s = D.CL B (D.lsOf fs fps) s :=
    CL_congr B fun k hk ↦ lsOf_take fs fps (by omega)
  have hlast : (fps.take (s + 2)).getLast?.getD 0 + fs (D.lname s) = D.lsOf fs fps s := by
    rw [take_last hl]; rfl
  simp only [layKid, hdl, hCL, hlast]
  have hO := bufL_eq (D := D) (by have := h.1; omega) B (D.lsOf fs fps)
  have own : ∀ {b ws}, (b, ws) ∈ bufL B D.sizes (D.own B (D.lsOf fs fps)) → ∀ {b' ws'},
      b ≤ b' → b' + ws'.length ≤ b + ws.length → ∀ x, RegionL [(b', ws')] x → T x :=
    fun hq _ _ h1 h2 x hx ↦ hOwn x (region_sub hq h1 h2 hx)
  have inLin : ∀ {b ws}, (b, ws) ∈ D.lin curE chiE olE zvE slE tbE → ∀ {b' ws'},
      b ≤ b' → b' + ws'.length ≤ b + ws.length → ∀ x, RegionL [(b', ws')] x → T x :=
    fun hq _ _ h1 h2 x hx ↦ hLin x (region_sub hq h1 h2 hx)
  have hcl := claims_length (D := D) (B := B) (ls := D.lsOf fs fps) h
  intro x ⟨q, hq, hx⟩
  have hx' : RegionL [q] x := ⟨q, List.mem_singleton_self _, hx⟩
  simp only [layerLin, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with ((rfl | rfl) | hq) | rfl
  rotate_right
  · exact inLin (b := tbE) (ws := winTabWords) (by simp [lin]) le_rfl le_rfl x hx'
  · exact own (b := B + D.o201) (ws := D.claims B (D.lsOf fs fps)) (by rw [hO]; simp) (by omega)
      (by rw [hcl, ← outWs, outWs_length]; omega) x hx'
  · exact inLin (b := curE) (ws := D.xs) (by simp [lin]) (by omega)
      (by rw [xs_length h, LayerData.xs_length (D.layer_facts h hs).1 (D.layer_facts h hs).2.2.1
        (D.layer_facts h hs).2.2.2.1, D.layer_y h hs.le]; simp only [lcur]; nlinarith) x hx'
  · rcases s with _ | k
    · simp only [CL, ClaimLay.L, firstOf, ↓reduceIte, List.append_nil, List.mem_cons,
        List.not_mem_nil, or_false] at hq
      rcases hq with rfl | rfl | rfl
      · exact own (b := B + D.o201) (ws := D.claims B (D.lsOf fs fps)) (by rw [hO]; simp)
          (by omega) (by rw [hcl, cw0_length h]; omega) x hx'
      · exact own (b := B) (ws := D.c0.point) (by rw [hO]; simp) le_rfl le_rfl x hx'
      · exact own (b := B + D.o274) (ws := eqLevels D.rl 5) (by rw [hO]; simp) (by omega)
          (by rw [eqLevels_length (by rw [rl_length])]; simp [eqKernel_length, rl_length])
          x hx'
    · have hk : k < 12 := by omega
      have hL := hPrev k rfl
      have lay : ∀ {b ws}, (b, ws) ∈ layerBufs (D.layer k) (firstOf k) (ptr (curE + D.lcur k))
          (D.lsOf fs fps k) → ∀ {b' ws'}, b ≤ b' → b' + ws'.length ≤ b + ws.length →
          ∀ x, RegionL [(b', ws')] x → T x :=
        fun hq _ _ h1 h2 x hx ↦ hL x (region_sub hq h1 h2 hx)
      have hc : (D.layer (k + 1)).c = (D.layer k).next (firstOf k) := by
        show (D.chain (k + 1)).1 = _
        rw [D.layer_succ h hk]
      simp only [CL, ClaimLay.L, show firstOf (k + 1) = 0 from rfl, show (0 : ℕ) ≠ 1 by decide,
        ↓reduceIte, List.mem_append, List.mem_cons, List.not_mem_nil, or_false, hc] at hq
      rcases hq with (rfl | rfl | rfl) | rfl | rfl
      · exact own (b := B + D.o201) (ws := D.claims B (D.lsOf fs fps)) (by rw [hO]; simp)
          (by omega) (by rw [hcl, outWs_length]; omega) x hx'
      · exact lay (b := D.lsOf fs fps k) (ws := (D.layer k).chs (firstOf k))
          (by simp [layerBufs_eq]) le_rfl le_rfl x hx'
      · exact lay (by simp [layerBufs_eq]) le_rfl le_rfl x hx'
      · exact lay (by simp [layerBufs_eq]) le_rfl le_rfl x hx'
      · exact lay (b := D.lsOf fs fps k + (D.layer k).y + 164)
          (ws := flipsOf (laterWeights (lanesOut ((D.layer k).locPt (firstOf k))
            ((D.layer k).beta (firstOf k)).1) (eqKernel (((D.layer k).locPt (firstOf k)).take 6))))
          (by simp [layerBufs_eq]) le_rfl (by simp [flipsOf]) x hx'

theorem kids_length : (D.kids fs B curE chiE olE zvE slE tbE).length = 18 := by simp [kids]

/-- **The callees' words, in memory.** -/
theorem kids_lin_mem (h : D.Ok) (hm : D.Mem rd B curE chiE olE zvE slE tbE (D.lsOf fs fps))
    (hfl : fps.length = 18) :
    ∀ i (hi : i < (D.kids fs B curE chiE olE zvE slE tbE).length),
      MemL rd ((D.kids fs B curE chiE olE zvE slE tbE)[i].Lin (fps.take (i + 1))) := by
  intro i hi
  rw [kids_length] at hi
  obtain ⟨m58, -⟩ := own_mem (by have := h.1; omega) hm.own
  have mlin := hm.lin
  have hL11 := hm.lay 11 (by norm_num)
  rw [layerBufs_eq] at hL11
  interval_cases i
  · intro q hq
    simp only [kids, List.cons_append, List.getElem_cons_zero, List.mem_cons, List.not_mem_nil,
      or_false] at hq
    rcases hq with rfl | rfl
    · exact memL_entry mlin (by simp [lin])
    · exact m58
  · exact layKid_lin_mem h hm (s := 0) (by norm_num) (by omega)
  · exact layKid_lin_mem h hm (s := 1) (by norm_num) (by omega)
  · exact layKid_lin_mem h hm (s := 2) (by norm_num) (by omega)
  · exact layKid_lin_mem h hm (s := 3) (by norm_num) (by omega)
  · exact layKid_lin_mem h hm (s := 4) (by norm_num) (by omega)
  · exact layKid_lin_mem h hm (s := 5) (by norm_num) (by omega)
  · exact layKid_lin_mem h hm (s := 6) (by norm_num) (by omega)
  · exact layKid_lin_mem h hm (s := 7) (by norm_num) (by omega)
  · exact layKid_lin_mem h hm (s := 8) (by norm_num) (by omega)
  · exact layKid_lin_mem h hm (s := 9) (by norm_num) (by omega)
  · exact layKid_lin_mem h hm (s := 10) (by norm_num) (by omega)
  · exact layKid_lin_mem h hm (s := 11) (by norm_num) (by omega)
  · exact mlin
  · show MemL rd [(zvE, D.op), (B, D.c0.point)]
    intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact memL_entry mlin (by simp [lin])
    · exact m58
  · exact mlin
  · exact mlin
  · show MemL rd [(zvE + qkeccakVarsCap, D.point),
      (D.lsOf fs (fps.take 18).dropLast 11, (D.layer 11).chs (firstOf 11))]
    intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact memL_entry mlin (by simp [lin])
    · rw [List.dropLast_eq_take, List.length_take, List.take_take, hfl,
        lsOf_take fs fps (by norm_num)]
      exact memL_entry hL11 (by simp)

/-- **The callees' words lie in the caller's words, the buffers or the earlier layers'
buffers.** -/
theorem kids_lin_region (h : D.Ok) (hfl : fps.length = 18) {T : ℕ → ℕ → Prop}
    (hLin : ∀ j x, RegionL (D.lin curE chiE olE zvE slE tbE) x → T j x)
    (hOwn : ∀ j x, RegionL (bufL B D.sizes (D.own B (D.lsOf fs fps))) x → T j x)
    (hPrev : ∀ k < 12, ∀ j, k + 1 < j → ∀ x, RegionL (layerBufs (D.layer k) (firstOf k)
      (ptr (curE + D.lcur k)) (D.lsOf fs fps k)) x → T j x) :
    ∀ i (hi : i < (D.kids fs B curE chiE olE zvE slE tbE).length), ∀ x,
      RegionL ((D.kids fs B curE chiE olE zvE slE tbE)[i].Lin (fps.take (i + 1))) x → T i x := by
  intro i hi
  rw [kids_length] at hi
  have hO := bufL_eq (D := D) (by have := h.1; omega) B (D.lsOf fs fps)
  have one : ∀ {L : Main.Layout} {b ws}, (b, ws) ∈ L → ∀ {U : ℕ → Prop},
      (∀ x, RegionL L x → U x) → ∀ x, RegionL [(b, ws)] x → U x :=
    fun hq U hU x hx ↦ hU x (region_sub hq le_rfl le_rfl hx)
  interval_cases i
  · intro x ⟨q, hq, hx⟩
    have hx' : RegionL [q] x := ⟨q, List.mem_singleton_self _, hx⟩
    simp only [kids, List.cons_append, List.getElem_cons_zero, List.mem_cons, List.not_mem_nil,
      or_false] at hq
    rcases hq with rfl | rfl
    · exact one (L := D.lin curE chiE olE zvE slE tbE) (by simp [lin]) (hLin 0) x hx'
    · exact one (L := bufL B D.sizes (D.own B (D.lsOf fs fps))) (by rw [hO]; simp) (hOwn 0) x hx'
  · exact layKid_lin_region h (s := 0) (by norm_num) (by omega) (hLin 1) (hOwn 1)
      (fun k hk x hx ↦ hPrev k (by omega) 1 (by omega) x hx)
  · exact layKid_lin_region h (s := 1) (by norm_num) (by omega) (hLin 2) (hOwn 2)
      (fun k hk x hx ↦ hPrev k (by omega) 2 (by omega) x hx)
  · exact layKid_lin_region h (s := 2) (by norm_num) (by omega) (hLin 3) (hOwn 3)
      (fun k hk x hx ↦ hPrev k (by omega) 3 (by omega) x hx)
  · exact layKid_lin_region h (s := 3) (by norm_num) (by omega) (hLin 4) (hOwn 4)
      (fun k hk x hx ↦ hPrev k (by omega) 4 (by omega) x hx)
  · exact layKid_lin_region h (s := 4) (by norm_num) (by omega) (hLin 5) (hOwn 5)
      (fun k hk x hx ↦ hPrev k (by omega) 5 (by omega) x hx)
  · exact layKid_lin_region h (s := 5) (by norm_num) (by omega) (hLin 6) (hOwn 6)
      (fun k hk x hx ↦ hPrev k (by omega) 6 (by omega) x hx)
  · exact layKid_lin_region h (s := 6) (by norm_num) (by omega) (hLin 7) (hOwn 7)
      (fun k hk x hx ↦ hPrev k (by omega) 7 (by omega) x hx)
  · exact layKid_lin_region h (s := 7) (by norm_num) (by omega) (hLin 8) (hOwn 8)
      (fun k hk x hx ↦ hPrev k (by omega) 8 (by omega) x hx)
  · exact layKid_lin_region h (s := 8) (by norm_num) (by omega) (hLin 9) (hOwn 9)
      (fun k hk x hx ↦ hPrev k (by omega) 9 (by omega) x hx)
  · exact layKid_lin_region h (s := 9) (by norm_num) (by omega) (hLin 10) (hOwn 10)
      (fun k hk x hx ↦ hPrev k (by omega) 10 (by omega) x hx)
  · exact layKid_lin_region h (s := 10) (by norm_num) (by omega) (hLin 11) (hOwn 11)
      (fun k hk x hx ↦ hPrev k (by omega) 11 (by omega) x hx)
  · exact layKid_lin_region h (s := 11) (by norm_num) (by omega) (hLin 12) (hOwn 12)
      (fun k hk x hx ↦ hPrev k (by omega) 12 (by omega) x hx)
  · exact hLin 13
  · show ∀ x, RegionL [(zvE, D.op), (B, D.c0.point)] x → T 14 x
    intro x ⟨q, hq, hx⟩
    have hx' : RegionL [q] x := ⟨q, List.mem_singleton_self _, hx⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact one (L := D.lin curE chiE olE zvE slE tbE) (by simp [lin]) (hLin 14) x hx'
    · exact one (L := bufL B D.sizes (D.own B (D.lsOf fs fps))) (by rw [hO]; simp) (hOwn 14) x hx'
  · exact hLin 15
  · exact hLin 16
  · show ∀ x, RegionL [(zvE + qkeccakVarsCap, D.point),
      (D.lsOf fs (fps.take 18).dropLast 11, (D.layer 11).chs (firstOf 11))] x → T 17 x
    intro x ⟨q, hq, hx⟩
    have hx' : RegionL [q] x := ⟨q, List.mem_singleton_self _, hx⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact one (L := D.lin curE chiE olE zvE slE tbE) (by simp [lin]) (hLin 17) x hx'
    · rw [List.dropLast_eq_take, List.length_take, List.take_take, hfl,
        lsOf_take fs fps (by norm_num)] at hx'
      exact one (L := layerBufs (D.layer 11) (firstOf 11) (ptr (curE + D.lcur 11)) (D.lsOf fs fps 11))
        (by simp [layerBufs_eq]) (hPrev 11 (by norm_num) 17 (by norm_num)) x hx'

end VkData

end
end LeanVM.Guest.B1.VerifySub
