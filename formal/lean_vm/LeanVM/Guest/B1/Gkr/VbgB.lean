/-
  LeanVM.Guest.B1.Gkr.VbgB

  `verify_bus_gkr`'s callee `verify_bus_gkr_loop0` within its words on the honest buffers.
-/

module

public import LeanVM.Guest.B1.Gkr.Loop7T
public import LeanVM.Guest.B1.Gkr.VbgAt
public import LeanVM.Guest.B1.Gkr.VbgBound
public import LeanVM.Guest.B1.Tables.FlatLiftT
public import LeanVM.Guest.Data.NameStrings

/-!
# `verify_bus_gkr`'s callees, within their words

* `vbg_loop7_total`: a valid tree of `verify_bus_gkr_loop0` from `1` below `g^((depth -
  1)/2)` has at most `ly7Total` words.
* `verify_bus_gkr_completeAtTB`: `verify_bus_gkr` placed within `vbgBound`: its frame, its
  buffers, `verify_bus_gkr_loop0`'s chain and `verify_bus_gkr_loop1`'s words (`depth · K8` and its
  run's phantom frame), and the frames of its two conditional calls (`flat_completeAtOutTB`).
-/

namespace LeanVM.Guest.B1.Tables

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Memory
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Guest.B1.Main (MemL RegionL)

@[expose] public section

variable {fs : String → ℕ}

/-- **`verify_bus_gkr_loop0`'s words.** -/
theorem vbg_loop7_total {depth : ℕ} (hd : depth ≤ 32) {eL eR eP : ℕ} {rd : Reader}
    {K29 R : ℕ}
    (h29 : TotalLeOn coreProgram fs name% «verify_bus_gkr_loop0_loop0» LoopPre
      (fun a ↦ logG (a.getD 1 0) * K29 + fs name% «verify_bus_gkr_loop0_loop0»))
    (hR : ∀ n ∈ grCounts, TotalLe coreProgram fs (lName "gkr_rounds" n) (fun _ ↦ R))
    (hm0 : 0 < (depth - 1) / 2) {tabs claim stream : E} {t : Tree} {rets : List E}
    (hn : t.name = name% «verify_bus_gkr_loop0»)
    (hv : t.Valid coreProgram rd [1, gen ^ ((depth - 1) / 2), gen ^ (2 - depth % 2),
      ofK (addressOfIndex eL), tabs, ofK (addressOfIndex eP), ofK (addressOfIndex eR), claim,
      gen ^ (depth % 2), stream, gen ^ depth] rets)
    (hb : t.BufsOk coreProgram) :
    t.total fs ≤ ly7Total fs K29 R depth := by
  rw [show (1 : E) = gen ^ 0 from (pow_zero _).symm] at hv
  have hch := ly7_chain (by omega : depth % 2 < 2) (by omega)
    ((depth - 1) / 2) 0 t rets (by omega) hm0 hn hv hb
  exact ly7_total fs h29 hR _ _ t _ rets hch hv hb

theorem vbg_noDisp : vbgPre.all noDispB = true := by decide +kernel

theorem vbg_callS : vbgPre.filterMap Main.Stmt.callS =
    [(some (.n 368), name% «verify_bus_gkr_loop0», [.n 369, .n 366, .n 135, .n 16, .n 8, .n 18,
        .n 17, .n 63, .n 133, .n 9, .n 6], []),
      (some (.n 388), name% «verify_bus_gkr_loop1», [.n 389, .n 6, .n 7, .n 386],
          [])] := by decide +kernel

/-- `verify_bus_gkr`'s frames: `verify_bus_gkr_loop0`'s, then `verify_bus_gkr_loop1`'s. -/
theorem vbg_flatCalls (σ : Val) : flatCalls vbgPre σ =
    [⟨name% «verify_bus_gkr_loop0», [.n 369, .n 366, .n 135, .n 16, .n 8, .n 18, .n 17, .n 63,
        .n 133, .n 9, .n 6], [],
        decide (σ (.n 368) ≠ 0)⟩,
      ⟨name% «verify_bus_gkr_loop1», [.n 389, .n 6, .n 7, .n 386], [],
          decide (σ (.n 388) ≠ 0)⟩] := by
  have e : vbgPre.filterMap (Stmt.callSF σ) = vbgPre.filterMap Main.Stmt.callS := by
    refine List.filterMap_congr fun s hs ↦ ?_
    have := List.all_eq_true.mp vbg_noDisp s hs
    cases s <;> first | rfl | simp [noDispB] at this
  unfold flatCalls
  rw [e, vbg_callS]
  rfl

variable {cert : String → V → ℕ}

/-- **`verify_bus_gkr` is complete, placed, within `vbgBound` words** (TRIAGE G #43), given the
words of `verify_bus_gkr_loop0_loop0`'s and `verify_bus_gkr_loop1`'s runs (linear in their ends'
exponents, `K29`, `K8`, and their phantom frames once) and of the rounds `gkr_rounds__L{n}`,
`n ∈ {1, 2}` (`R`), on every reader. -/
theorem verify_bus_gkr_completeAtTB {κ depth : ℕ} (hd2 : 2 ≤ depth) (hd : depth ≤ 32)
    (hκ : 6 ≤ κ) {cap0 xs : List E} {r : E × List E × List E} {cap' : List E}
    (hrun : RunsTo (gkrPhase depth) ⟨cap0, []⟩ xs r ⟨cap', []⟩)
    (hc : ∃ sp, (⟨cap0, []⟩ : Fs).Carries sp) (tabs stream : E) (ec ez : ℕ) {K29 R K8 : ℕ}
    (h29 : TotalLeOn coreProgram fs name% «verify_bus_gkr_loop0_loop0» LoopPre
      (fun a ↦ logG (a.getD 1 0) * K29 + fs name% «verify_bus_gkr_loop0_loop0»))
    (hR : ∀ n ∈ grCounts, TotalLe coreProgram fs (lName "gkr_rounds" n) (fun _ ↦ R))
    (h8 : TotalLeOn coreProgram fs name% «verify_bus_gkr_loop1» LoopPre
      (fun a ↦ logG (a.getD 1 0) * K8 + fs name% «verify_bus_gkr_loop1»)) :
    CompleteAtDTB fs cert κ "verify_bus_gkr" [(ec, xs), (ez, r.2.1)]
      (cap0 ++ [ofK (addressOfIndex ec), gen ^ depth, ofK (addressOfIndex ez), tabs, stream])
      (VbgOut cap' (ofK (addressOfIndex ec) * gen ^ xs.length) r.2.2) (fun _ ↦ True)
      (vbgBound fs K29 R K8 depth) := by
  have hcl : cap0.length = 5 := by
    obtain ⟨sp, hsp⟩ := hc
    have hsc : capOf sp.state = cap0 := hsp.1
    rw [← hsc]; simp [capOf]
  have hvals : vbgValsW depth cap0 xs = r.2.2 := by
    obtain ⟨-, -, -, -, -, -, hr, -⟩ := gk_walk hrun hc
    rw [hr]; rfl
  obtain ⟨hown, hbufs, hfacts⟩ := vbg_lift_facts (fs := fs) hd2 hd hκ hrun hc tabs stream ec ez
  refine (flat_completeAtOutTB (cert := cert) vbgFlat [(ec, xs), (ez, r.2.1)] _
    (fun fp ↦ cap' ++ [ofK (addressOfIndex ec) * gen ^ xs.length,
      ofK (addressOfIndex (vbgEV fs depth fp))]) _
    (by simp [vbgFlat, hcl]) (vbgSizes depth)
    (fun _ ↦ vbgOwnW depth cap0 xs (ofK (addressOfIndex ec))) hown
    (fun fp ↦ ⟨vbgEV fs depth fp, rfl, by
      rw [show fp + fs vbgFlat.name = fp + fs "verify_bus_gkr" from rfl, vbg_bufL, ← hvals]
      simp⟩)
    (fun fp ↦ vbgW (ofK (addressOfIndex (vbgEL fs fp))) (ofK (addressOfIndex (vbgER fs depth fp)))
      (ofK (addressOfIndex (vbgEP fs depth fp))) (ofK (addressOfIndex (vbgEB fs depth fp)))
      (ofK (addressOfIndex (vbgEO fs depth fp))) (ofK (addressOfIndex (vbgEV fs depth fp))))
    (vbgBufs fs depth xs ec) hbufs (fun fp rd hlow hL ↦ (hfacts fp rd hlow hL).1)
    (fun _ ↦ True) [fun _ ↦ True, fun _ ↦ True] (fun _ _ _ _ ↦ trivial)
    (by show (vbgPre.filter callB).length ≤ 2; decide +kernel)
    (fun _ _ _ _ i _ _ _ _ _ _ _ _ ↦ by rcases i with _ | _ | _ <;> trivial)
    [ly7Total fs K29 R depth, depth * K8 + fs name% «verify_bus_gkr_loop1»] _
    (fun fp rd hlow hL i c hci ht rd' hlow' hL' t rr hn hv hb ↦ ?_)
    (fun σ ↦ callsBound_le vbgPre σ _)).mono le_rfl (fun _ _ ↦ trivial)
  obtain ⟨-, hV, -⟩ := hfacts fp rd hlow hL
  have hV' : VbgVals (vbgFlat.σ rd (vbgW (ofK (addressOfIndex (vbgEL fs fp)))
      (ofK (addressOfIndex (vbgER fs depth fp))) (ofK (addressOfIndex (vbgEP fs depth fp)))
      (ofK (addressOfIndex (vbgEB fs depth fp)))
      (ofK (addressOfIndex (vbgEO fs depth fp))) (ofK (addressOfIndex (vbgEV fs depth fp))))
      (cap0 ++ [ofK (addressOfIndex ec), gen ^ depth, ofK (addressOfIndex ez), tabs, stream]))
      depth (vbgEL fs fp) (vbgER fs depth fp) (vbgEP fs depth fp) tabs stream := hV
  obtain ⟨v369, v366, v135, v389, v6, v16, v17, v18, v8, v9, v133, v368⟩ := hV'
  have hc' := hci
  rw [show vbgFlat.pre = vbgPre from rfl, vbg_flatCalls] at hc'
  rcases i with _ | _ | i
  · simp only [List.getElem?_cons_zero, Option.some.injEq] at hc'
    subst hc'
    simp only [decide_eq_true_eq] at ht
    have hm0 : 0 < (depth - 1) / 2 := by
      rcases Nat.eq_zero_or_pos ((depth - 1) / 2) with h0 | h0
      · exfalso; apply ht
        rw [v368, h0, pow_zero, e_add_self]
      · exact h0
    simp only [List.map_cons, List.map_nil] at hv
    rw [v369, v366, v135, v16, v8, v18, v17, v133, v9, v6] at hv
    exact vbg_loop7_total hd h29 hR hm0 hn hv hb
  · simp only [List.getElem?_cons_succ, List.getElem?_cons_zero, Option.some.injEq] at hc'
    subst hc'
    simp only [List.map_cons, List.map_nil] at hv
    rw [v389, v6] at hv
    have hb' := h8 rd' t _ rr hn (loopPre_gen (by omega) (by omega) _) hv hb
    simp only [List.getD_cons_succ, List.getD_cons_zero, gen_pow_eq_ofK,
      logG_spec (show depth < 2 ^ 64 - 1 by omega)] at hb'
    simpa using hb'
  · simp at hc'

end
end LeanVM.Guest.B1.Tables
