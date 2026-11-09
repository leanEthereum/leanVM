/-
  LeanVM.Guest.B1.Gkr.VbgB

  `verify_bus_gkr`'s callee `__loop6` within its words on the honest buffers.
-/

module

public import LeanVM.Guest.B1.Gkr.Loop7T
public import LeanVM.Guest.B1.Gkr.VbgAt
public import LeanVM.Guest.B1.Tables.FlatLiftT

/-!
# `verify_bus_gkr`'s callees, within their words

* `vbg_ly7Mem`: on the honest buffers (`vbgLay`), `__loop6`'s bounds' words (`Ly7Mem`): the
  `depth_shift` word `g^(depth % 2)`, each slot's `half` and `parity`.
* `vbg_loop7_total`: there, a valid tree of `__loop6` from `1` below `g^(depth/2)` has at most
  `ly7Total` words.
* `verify_bus_gkr_completeAtTB`: `verify_bus_gkr` placed within `vbgBound`: its frame, its
  buffers, `__loop6`'s chain and `__loop7`'s words (`depth · K8` and its run's phantom frame), and
  the frames of its two conditional calls (`flat_completeAtTB`).
-/

namespace LeanVM.Guest.B1.Tables

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Memory
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Guest.B1.Main (MemL RegionL)

@[expose] public section

variable {fs : String → ℕ}

/-- **`__loop6`'s bounds' words on the honest buffers.** -/
theorem vbg_ly7Mem {depth : ℕ} (hd : depth ≤ 32) {cap0 xs : List E} {r : E × List E × List E} {cap' : List E}
    (hrun : RunsTo (gkrPhase depth) ⟨cap0, []⟩ xs r ⟨cap', []⟩)
    (hc : ∃ sp, (⟨cap0, []⟩ : Fs).Carries sp) {ec eL eR eP eK ePa eD : ℕ} {rd : Reader}
    (hm : MemLay rd (vbgLay depth cap0 xs (ofK (addressOfIndex ec)) eL eR eP eK ePa eD)) :
    Ly7Mem rd (ofK (addressOfIndex eD)) (gen ^ depth) (ofK (addressOfIndex eL)) (depth % 2) (depth /
        2) := by
  obtain ⟨-, -, -, hsteps, -, -, -, -⟩ := gk_walk hrun hc
  obtain ⟨sp, hsp⟩ := hc
  have hsc : capOf sp.state = cap0 := hsp.1
  have hcl : cap0.length = 5 := by rw [← hsc]; simp [capOf]
  have hcan : AllCanonical cap0 := by rw [← hsc]; exact tb_capOf_canonical _
  unfold vbgLay at hm
  rw [memLay_append, memLay_append, memLay_append, memLay_append] at hm
  obtain ⟨⟨⟨⟨-, hmS⟩, hmP⟩, -⟩, hmT⟩ := hm
  set sh := depth % 2 with hsh
  set m := depth / 2 with hmm
  have hsh2 : sh < 2 := by omega
  have inv := gkSl_inv (xs := xs) (sh := sh) hcl hcan
  have hpl : ∀ j ≤ m, (gkSl cap0 xs sh j).2.1.point.length = 2 * j + sh :=
    gkSl_point_len (gkSl0_point_len cap0 xs sh hsh2) fun j hj => (hsteps j hj).1
  have hD := hmT _ (List.mem_cons_of_mem _ List.mem_cons_self)
  refine ⟨?_, fun j hj ↦ ?_⟩
  · rw [tb_loadHolds_mul_gen_pow, Nat.add_zero]
    have := hD depth (by simp; omega)
    simpa [hsh] using this
  · have hS := hmS _ (List.mem_map.mpr ⟨j, List.mem_range.mpr (show j < m + 1 by omega), rfl⟩)
    obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, hhalf, hpar⟩ :=
      gkSlotC_of (inv j).1 (inv j).2.1 (inv j).2.2.1 (inv j).2.2.2 (hpl j (by omega))
        (by rw [tb_ofK_gpow_mul]
            have := hmP _ (List.mem_map.mpr ⟨j, List.mem_range.mpr (show j < m + 1 by omega), rfl⟩)
            exact this)
        hS
    exact ⟨hhalf, hpar⟩

/-- `__loop6`'s words from `1` below `g^(depth/2)`: the iterations' bounds and the last tail's
frame. -/
def ly7Total (fs : String → ℕ) (K29 R depth : ℕ) : ℕ :=
  Budget.iterSum (ly7B fs K29 R (depth % 2)) 0 (depth / 2) + fs "__loop6"

/-- **`__loop6`'s words on the honest buffers.** -/
theorem vbg_loop7_total {depth : ℕ} (hd : depth ≤ 32) {cap0 xs : List E}
    {r : E × List E × List E} {cap' : List E}
    (hrun : RunsTo (gkrPhase depth) ⟨cap0, []⟩ xs r ⟨cap', []⟩)
    (hc : ∃ sp, (⟨cap0, []⟩ : Fs).Carries sp) {ec eL eR eP eK ePa eD : ℕ} {rd : Reader}
    (hm : MemLay rd (vbgLay depth cap0 xs (ofK (addressOfIndex ec)) eL eR eP eK ePa eD))
    {K29 R : ℕ}
    (h29 : TotalLeOn coreProgram fs "__loop36" LoopPre
      (fun a ↦ logG (a.getD 1 0) * K29 + fs "__loop36"))
    (hR : ∀ n ∈ grCounts, TotalLe coreProgram fs (lName "gkr_rounds" n) (fun _ ↦ R))
    (hm0 : 0 < depth / 2) {t : Tree} {rets : List E} (hn : t.name = "__loop6")
    (hv : t.Valid coreProgram rd [1, gen ^ (depth / 2), ofK (addressOfIndex eD), gen ^ depth,
      ofK (addressOfIndex eL), ofK (addressOfIndex eR), ofK (addressOfIndex eK)] rets)
    (hb : t.BufsOk coreProgram) :
    t.total fs ≤ ly7Total fs K29 R depth := by
  rw [show (1 : E) = gen ^ 0 from (pow_zero _).symm] at hv
  have hch := ly7_chain (rounds := ofK (addressOfIndex eR)) (by omega : depth % 2 < 2) (by omega)
    (vbg_ly7Mem hd hrun hc hm) (depth / 2) 0 t rets (by omega) hm0 hn hv hb
  exact ly7_total fs (by omega) h29 hR _ _ t _ rets hch hv hb

theorem vbg_noDisp : vbgPre.all noDispB = true := by decide +kernel

theorem vbg_callS : vbgPre.filterMap Main.Stmt.callS =
    [(some (.n 312), "__loop6", [.n 313, .n 315, .n 66, .n 6, .n 15, .n 16, .n 56], []),
      (some (.n 325), "__loop7", [.n 326, .n 6, .n 7, .n 323], [])] := by decide +kernel

/-- `verify_bus_gkr`'s frames: `__loop6`'s, then `__loop7`'s. -/
theorem vbg_flatCalls (σ : Val) : flatCalls vbgPre σ =
    [⟨"__loop6", [.n 313, .n 315, .n 66, .n 6, .n 15, .n 16, .n 56], [],
        decide (σ (.n 312) ≠ 0)⟩,
      ⟨"__loop7", [.n 326, .n 6, .n 7, .n 323], [], decide (σ (.n 325) ≠ 0)⟩] := by
  have e : vbgPre.filterMap (Stmt.callSF σ) = vbgPre.filterMap Main.Stmt.callS := by
    refine List.filterMap_congr fun s hs ↦ ?_
    have := List.all_eq_true.mp vbg_noDisp s hs
    cases s <;> first | rfl | simp [noDispB] at this
  unfold flatCalls
  rw [e, vbg_callS]
  rfl

/-- `verify_bus_gkr`'s words: its frame, its buffers, `__loop6`'s chain, `__loop7`'s run (`depth`
iterations of at most `K8` words and its one phantom frame), and the frames of its two conditional
calls. -/
def vbgBound (fs : String → ℕ) (K29 R K8 depth : ℕ) : ℕ :=
  fs "verify_bus_gkr" + (vbgSizes depth).sum +
    ([ly7Total fs K29 R depth, depth * K8 + fs "__loop7"].sum + ifFrames fs vbgPre)

variable {cert : String → V → ℕ}

/-- **`verify_bus_gkr` is complete, placed, within `vbgBound` words** (TRIAGE G #43), given the
words of `__loop36`'s and `__loop7`'s runs (linear in their ends' exponents, `K29`, `K8`, and
their phantom frames once) and of the rounds `gkr_rounds__L{n}`, `n ∈ {0, 1, 2, 4, 6}` (`R`), on
every reader. -/
theorem verify_bus_gkr_completeAtTB {κ depth : ℕ} (hd1 : 1 ≤ depth) (hd : depth ≤ 32)
    (hκ : 6 ≤ κ) {cap0 xs : List E} {r : E × List E × List E} {cap' : List E}
    (hrun : RunsTo (gkrPhase depth) ⟨cap0, []⟩ xs r ⟨cap', []⟩)
    (hc : ∃ sp, (⟨cap0, []⟩ : Fs).Carries sp) (ec ez : ℕ) {K29 R K8 : ℕ}
    (h29 : TotalLeOn coreProgram fs "__loop36" LoopPre
      (fun a ↦ logG (a.getD 1 0) * K29 + fs "__loop36"))
    (hR : ∀ n ∈ grCounts, TotalLe coreProgram fs (lName "gkr_rounds" n) (fun _ ↦ R))
    (h8 : TotalLeOn coreProgram fs "__loop7" LoopPre
      (fun a ↦ logG (a.getD 1 0) * K8 + fs "__loop7")) :
    CompleteAtDTB fs cert κ "verify_bus_gkr" [(ec, xs), (ez, r.2.1)]
      (cap0 ++ [ofK (addressOfIndex ec), gen ^ depth, ofK (addressOfIndex ez)])
      (Returns (cap' ++ [ofK (addressOfIndex ec) * gen ^ xs.length] ++ r.2.2)) (fun _ ↦ True)
      (vbgBound fs K29 R K8 depth) := by
  have hcl : cap0.length = 5 := by
    obtain ⟨sp, hsp⟩ := hc
    have hsc : capOf sp.state = cap0 := hsp.1
    rw [← hsc]; simp [capOf]
  obtain ⟨hown, hbufs, hfacts⟩ := vbg_lift_facts (fs := fs) hd1 hd hκ hrun hc ec ez
  refine (flat_completeAtTB (cert := cert) vbgFlat [(ec, xs), (ez, r.2.1)] _ _
    (by simp [vbgFlat, hcl]) (vbgSizes depth)
    (fun fp ↦ vbgOwnW depth cap0 xs (ofK (addressOfIndex ec)) (fp + fs "verify_bus_gkr" + 17 * (depth + 2) + 6034))
    hown
    (fun fp ↦ vbgW (ofK (addressOfIndex (vbgEL fs fp))) (ofK (addressOfIndex (vbgER fs depth fp)))
      (ofK (addressOfIndex (vbgEP fs depth fp))) (ofK (addressOfIndex (vbgEK fs depth fp)))
      (ofK (addressOfIndex (vbgEPa fs depth fp))) (ofK (addressOfIndex (vbgED fs depth fp))))
    (vbgBufs fs depth xs ec) hbufs (fun fp rd hlow hL ↦ (hfacts fp rd hlow hL).1)
    (fun _ ↦ True) [fun _ ↦ True, fun _ ↦ True] (fun _ _ _ _ ↦ trivial)
    (by show (vbgPre.filter callB).length ≤ 2; decide +kernel)
    (fun _ _ _ _ i _ _ _ _ _ _ _ _ ↦ by rcases i with _ | _ | _ <;> trivial)
    [ly7Total fs K29 R depth, depth * K8 + fs "__loop7"] _ (fun fp rd hlow hL i c hci ht rd' hlow' hL' t rr hn hv hb ↦ ?_)
    (fun σ ↦ callsBound_le vbgPre σ _)).mono le_rfl (fun _ _ ↦ trivial)
  obtain ⟨-, hV, -⟩ := hfacts fp rd hlow hL
  have hV' : VbgVals (vbgFlat.σ rd (vbgW (ofK (addressOfIndex (vbgEL fs fp))) (ofK (addressOfIndex
      (vbgER fs depth fp)))
      (ofK (addressOfIndex (vbgEP fs depth fp))) (ofK (addressOfIndex (vbgEK fs depth fp)))
      (ofK (addressOfIndex (vbgEPa fs depth fp))) (ofK (addressOfIndex (vbgED fs depth fp))))
      (cap0 ++ [ofK (addressOfIndex ec), gen ^ depth, ofK (addressOfIndex ez)])) depth (vbgEL fs fp)
          (vbgER fs depth fp) (vbgEK fs depth fp)
      (vbgED fs depth fp) := hV
  obtain ⟨v313, v315, v326, v6, v66, v15, v16, v56, v312⟩ := hV'
  obtain ⟨-, -, hm'⟩ := hfacts fp rd' hlow' hL'
  have hc' := hci
  rw [show vbgFlat.pre = vbgPre from rfl, vbg_flatCalls] at hc'
  rcases i with _ | _ | i
  · simp only [List.getElem?_cons_zero, Option.some.injEq] at hc'
    subst hc'
    simp only [decide_eq_true_eq] at ht
    have hm0 : 0 < depth / 2 := by
      rcases Nat.eq_zero_or_pos (depth / 2) with h0 | h0
      · exfalso; apply ht
        rw [v312, h0, pow_zero, e_add_self]
      · exact h0
    simp only [List.map_cons, List.map_nil] at hv
    rw [v313, v315, v66, v6, v15, v16, v56] at hv
    exact vbg_loop7_total hd hrun hc hm' h29 hR hm0 hn hv hb
  · simp only [List.getElem?_cons_succ, List.getElem?_cons_zero, Option.some.injEq] at hc'
    subst hc'
    simp only [List.map_cons, List.map_nil] at hv
    rw [v326, v6] at hv
    have hb' := h8 rd' t _ rr hn (loopPre_gen (by omega) (by omega) _) hv hb
    simp only [List.getD_cons_succ, List.getD_cons_zero, gen_pow_eq_ofK,
      logG_spec (show depth < 2 ^ 64 - 1 by omega)] at hb'
    simpa using hb'
  · simp at hc'

end
end LeanVM.Guest.B1.Tables
