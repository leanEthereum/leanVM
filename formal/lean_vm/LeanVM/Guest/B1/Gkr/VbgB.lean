/-
  LeanVM.Guest.B1.Gkr.VbgB

  `verify_bus_gkr`'s callee `__loop6` within its words on the honest buffers.
-/

module

public import LeanVM.Guest.B1.Gkr.Loop7T
public import LeanVM.Guest.B1.Gkr.VbgAt
public import LeanVM.Guest.B1.Gkr.VbgBound
public import LeanVM.Guest.B1.Tables.FlatLiftT

/-!
# `verify_bus_gkr`'s callees, within their words

* `vbg_ly7Mem`: on the honest buffers (`vbgLay`), `__loop6`'s bounds' words (`Ly7Mem`): each
  slot's `half` and `parity`.
* `vbg_loop7_total`: there, a valid tree of `__loop6` from `1` below `g^((depth - 1)/2)` has at
  most `ly7Total` words.
* `verify_bus_gkr_completeAtTB`: `verify_bus_gkr` placed within `vbgBound`: its frame, its
  buffers, `__loop6`'s chain and `__loop7`'s words (`depth · K8` and its run's phantom frame), and
  the frames of its two conditional calls (`flat_completeAtOutTB`).
-/

namespace LeanVM.Guest.B1.Tables

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Memory
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Guest.B1.Main (MemL RegionL)

@[expose] public section

variable {fs : String → ℕ}

/-- **`__loop6`'s bounds' words on the honest buffers.** -/
theorem vbg_ly7Mem {depth : ℕ} (hd : depth ≤ 32) {cap0 xs : List E} {r : E × List E × List E}
    {cap' : List E} (hrun : RunsTo (gkrPhase depth) ⟨cap0, []⟩ xs r ⟨cap', []⟩)
    (hc : ∃ sp, (⟨cap0, []⟩ : Fs).Carries sp) {ec eL eR eP eK eB eO eV : ℕ} {rd : Reader}
    (hm : MemLay rd (vbgLay depth cap0 xs (ofK (addressOfIndex ec)) eL eR eP eK eB eO eV)) :
    Ly7Mem rd (ofK (addressOfIndex eL)) (depth % 2) ((depth - 1) / 2) := by
  obtain ⟨-, -, -, hsteps, -, -, -, -⟩ := gk_walk hrun hc
  obtain ⟨sp, hsp⟩ := hc
  have hsc : capOf sp.state = cap0 := hsp.1
  have hcl : cap0.length = 5 := by rw [← hsc]; simp [capOf]
  unfold vbgLay at hm
  rw [memLay_append, memLay_append, memLay_append] at hm
  obtain ⟨⟨⟨hmS, hmP⟩, -⟩, -⟩ := hm
  set sh := depth % 2 with hsh
  set M := depth / 2 with hM
  have hsh2 : sh < 2 := by omega
  have inv := gkSl_inv (xs := xs) (sh := sh) hcl
  have hpl : ∀ j ≤ M, (gkSl cap0 xs sh j).2.1.point.length = 2 * j + sh :=
    gkSl_point_len (gkSl0_point_len cap0 xs sh hsh2) fun j hj => (hsteps j hj).1
  intro j hj
  set k := j + 1 - sh with hk
  have hi : k + sh - 1 < M + sh := by omega
  have hik : k + sh - 1 + 1 - sh = k := by omega
  have hS := hmS _ (List.mem_map.mpr ⟨k + sh - 1, List.mem_range.mpr hi, rfl⟩)
  have hP := hmP _ (List.mem_map.mpr ⟨k + sh - 1, List.mem_range.mpr hi, rfl⟩)
  simp only [hik] at hS hP
  obtain ⟨-, -, -, -, -, -, -, -, -, -, hhalf, hpar⟩ := gkSlot_of (inv k).1 ((inv k).2.2 (by omega))
    (inv k).2.1 (hpl k (by omega)) (by rw [tb_ofK_gpow_mul]; exact hP) hS
  rw [show 2 * j + 2 - sh = 2 * k + sh by omega]
  exact ⟨hhalf, hpar⟩

/-- **`__loop6`'s words on the honest buffers.** -/
theorem vbg_loop7_total {depth : ℕ} (hd : depth ≤ 32) {cap0 xs : List E}
    {r : E × List E × List E} {cap' : List E}
    (hrun : RunsTo (gkrPhase depth) ⟨cap0, []⟩ xs r ⟨cap', []⟩)
    (hc : ∃ sp, (⟨cap0, []⟩ : Fs).Carries sp) {ec eL eR eP eK eB eO eV : ℕ} {rd : Reader}
    (hm : MemLay rd (vbgLay depth cap0 xs (ofK (addressOfIndex ec)) eL eR eP eK eB eO eV))
    {K29 R : ℕ}
    (h29 : TotalLeOn coreProgram fs "__loop36" LoopPre
      (fun a ↦ logG (a.getD 1 0) * K29 + fs "__loop36"))
    (hR : ∀ n ∈ grCounts, TotalLe coreProgram fs (lName "gkr_rounds" n) (fun _ ↦ R))
    (hm0 : 0 < (depth - 1) / 2) {tabs claim : E} {t : Tree} {rets : List E}
    (hn : t.name = "__loop6")
    (hv : t.Valid coreProgram rd [1, gen ^ ((depth - 1) / 2), gen ^ (2 - depth % 2),
      ofK (addressOfIndex eL), tabs, ofK (addressOfIndex eR), claim, gen ^ (depth % 2),
      gen ^ depth, ofK (addressOfIndex eK)] rets)
    (hb : t.BufsOk coreProgram) :
    t.total fs ≤ ly7Total fs K29 R depth := by
  rw [show (1 : E) = gen ^ 0 from (pow_zero _).symm] at hv
  have hch := ly7_chain (by omega : depth % 2 < 2) (by omega)
    (vbg_ly7Mem hd hrun hc hm) ((depth - 1) / 2) 0 t rets (by omega) hm0 hn hv hb
  exact ly7_total fs (by omega) h29 hR _ _ t _ rets hch hv hb

theorem vbg_noDisp : vbgPre.all noDispB = true := by decide +kernel

theorem vbg_callS : vbgPre.filterMap Main.Stmt.callS =
    [(some (.n 379), "__loop6", [.n 380, .n 382, .n 375, .n 16, .n 8, .n 17, .n 63, .n 142, .n 6,
        .n 64], []),
      (some (.n 392), "__loop7", [.n 393, .n 6, .n 7, .n 390], [])] := by decide +kernel

/-- `verify_bus_gkr`'s frames: `__loop6`'s, then `__loop7`'s. -/
theorem vbg_flatCalls (σ : Val) : flatCalls vbgPre σ =
    [⟨"__loop6", [.n 380, .n 382, .n 375, .n 16, .n 8, .n 17, .n 63, .n 142, .n 6, .n 64], [],
        decide (σ (.n 379) ≠ 0)⟩,
      ⟨"__loop7", [.n 393, .n 6, .n 7, .n 390], [], decide (σ (.n 392) ≠ 0)⟩] := by
  have e : vbgPre.filterMap (Stmt.callSF σ) = vbgPre.filterMap Main.Stmt.callS := by
    refine List.filterMap_congr fun s hs ↦ ?_
    have := List.all_eq_true.mp vbg_noDisp s hs
    cases s <;> first | rfl | simp [noDispB] at this
  unfold flatCalls
  rw [e, vbg_callS]
  rfl

variable {cert : String → V → ℕ}

/-- **`verify_bus_gkr` is complete, placed, within `vbgBound` words** (TRIAGE G #43), given the
words of `__loop36`'s and `__loop7`'s runs (linear in their ends' exponents, `K29`, `K8`, and
their phantom frames once) and of the rounds `gkr_rounds__L{n}`, `n ∈ {0, 1, 2, 4, 6}` (`R`), on
every reader. -/
theorem verify_bus_gkr_completeAtTB {κ depth : ℕ} (hd2 : 2 ≤ depth) (hd : depth ≤ 32)
    (hκ : 6 ≤ κ) {cap0 xs : List E} {r : E × List E × List E} {cap' : List E}
    (hrun : RunsTo (gkrPhase depth) ⟨cap0, []⟩ xs r ⟨cap', []⟩)
    (hc : ∃ sp, (⟨cap0, []⟩ : Fs).Carries sp) (tabs : E) (ec ez : ℕ) {K29 R K8 : ℕ}
    (h29 : TotalLeOn coreProgram fs "__loop36" LoopPre
      (fun a ↦ logG (a.getD 1 0) * K29 + fs "__loop36"))
    (hR : ∀ n ∈ grCounts, TotalLe coreProgram fs (lName "gkr_rounds" n) (fun _ ↦ R))
    (h8 : TotalLeOn coreProgram fs "__loop7" LoopPre
      (fun a ↦ logG (a.getD 1 0) * K8 + fs "__loop7")) :
    CompleteAtDTB fs cert κ "verify_bus_gkr" [(ec, xs), (ez, r.2.1)]
      (cap0 ++ [ofK (addressOfIndex ec), gen ^ depth, ofK (addressOfIndex ez), tabs])
      (VbgOut cap' (ofK (addressOfIndex ec) * gen ^ xs.length) r.2.2) (fun _ ↦ True)
      (vbgBound fs K29 R K8 depth) := by
  have hcl : cap0.length = 5 := by
    obtain ⟨sp, hsp⟩ := hc
    have hsc : capOf sp.state = cap0 := hsp.1
    rw [← hsc]; simp [capOf]
  have hvals : vbgValsW depth cap0 xs = r.2.2 := by
    obtain ⟨-, -, -, -, -, -, hr, -⟩ := gk_walk hrun hc
    rw [hr]; rfl
  obtain ⟨hown, hbufs, hfacts⟩ := vbg_lift_facts (fs := fs) hd2 hd hκ hrun hc tabs ec ez
  refine (flat_completeAtOutTB (cert := cert) vbgFlat [(ec, xs), (ez, r.2.1)] _
    (fun fp ↦ cap' ++ [ofK (addressOfIndex ec) * gen ^ xs.length,
      ofK (addressOfIndex (vbgEV fs depth fp))]) _
    (by simp [vbgFlat, hcl]) (vbgSizes depth)
    (fun fp ↦ vbgOwnW depth cap0 xs (ofK (addressOfIndex ec)) (vbgEP fs depth fp)) hown
    (fun fp ↦ ⟨vbgEV fs depth fp, rfl, by
      rw [show fp + fs vbgFlat.name = fp + fs "verify_bus_gkr" from rfl, vbg_bufL, ← hvals]
      simp⟩)
    (fun fp ↦ vbgW (ofK (addressOfIndex (vbgEL fs fp))) (ofK (addressOfIndex (vbgER fs depth fp)))
      (ofK (addressOfIndex (vbgEP fs depth fp))) (ofK (addressOfIndex (vbgEK fs depth fp)))
      (ofK (addressOfIndex (vbgEB fs depth fp))) (ofK (addressOfIndex (vbgEO fs depth fp)))
      (ofK (addressOfIndex (vbgEV fs depth fp))))
    (vbgBufs fs depth xs ec) hbufs (fun fp rd hlow hL ↦ (hfacts fp rd hlow hL).1)
    (fun _ ↦ True) [fun _ ↦ True, fun _ ↦ True] (fun _ _ _ _ ↦ trivial)
    (by show (vbgPre.filter callB).length ≤ 2; decide +kernel)
    (fun _ _ _ _ i _ _ _ _ _ _ _ _ ↦ by rcases i with _ | _ | _ <;> trivial)
    [ly7Total fs K29 R depth, depth * K8 + fs "__loop7"] _
    (fun fp rd hlow hL i c hci ht rd' hlow' hL' t rr hn hv hb ↦ ?_)
    (fun σ ↦ callsBound_le vbgPre σ _)).mono le_rfl (fun _ _ ↦ trivial)
  obtain ⟨-, hV, -⟩ := hfacts fp rd hlow hL
  have hV' : VbgVals (vbgFlat.σ rd (vbgW (ofK (addressOfIndex (vbgEL fs fp)))
      (ofK (addressOfIndex (vbgER fs depth fp))) (ofK (addressOfIndex (vbgEP fs depth fp)))
      (ofK (addressOfIndex (vbgEK fs depth fp))) (ofK (addressOfIndex (vbgEB fs depth fp)))
      (ofK (addressOfIndex (vbgEO fs depth fp))) (ofK (addressOfIndex (vbgEV fs depth fp))))
      (cap0 ++ [ofK (addressOfIndex ec), gen ^ depth, ofK (addressOfIndex ez), tabs])) depth
      (vbgEL fs fp) (vbgER fs depth fp) (vbgEK fs depth fp) tabs := hV
  obtain ⟨v380, v382, v375, v393, v6, v16, v17, v64, v8, v142, v379⟩ := hV'
  obtain ⟨-, -, hm'⟩ := hfacts fp rd' hlow' hL'
  have hc' := hci
  rw [show vbgFlat.pre = vbgPre from rfl, vbg_flatCalls] at hc'
  rcases i with _ | _ | i
  · simp only [List.getElem?_cons_zero, Option.some.injEq] at hc'
    subst hc'
    simp only [decide_eq_true_eq] at ht
    have hm0 : 0 < (depth - 1) / 2 := by
      rcases Nat.eq_zero_or_pos ((depth - 1) / 2) with h0 | h0
      · exfalso; apply ht
        rw [v379, h0, pow_zero, e_add_self]
      · exact h0
    simp only [List.map_cons, List.map_nil] at hv
    rw [v380, v382, v375, v16, v8, v17, v142, v6, v64] at hv
    exact vbg_loop7_total hd hrun hc hm' h29 hR hm0 hn hv hb
  · simp only [List.getElem?_cons_succ, List.getElem?_cons_zero, Option.some.injEq] at hc'
    subst hc'
    simp only [List.map_cons, List.map_nil] at hv
    rw [v393, v6] at hv
    have hb' := h8 rd' t _ rr hn (loopPre_gen (by omega) (by omega) _) hv hb
    simp only [List.getD_cons_succ, List.getD_cons_zero, gen_pow_eq_ofK,
      logG_spec (show depth < 2 ^ 64 - 1 by omega)] at hb'
    simpa using hb'
  · simp at hc'

end
end LeanVM.Guest.B1.Tables
