/-
  LeanVM.Guest.B1.Gkr.VbgB

  `verify_bus_gkr`'s callee `verify_bus_gkr_loop0` within its words on the honest buffers.
-/

module

public import LeanVM.Guest.B1.Gkr.VbgAt
public import LeanVM.Guest.B1.Gkr.VbgBound
public import LeanVM.Guest.Memory.LoopPre
public import LeanVM.Guest.B1.Tables.FlatLiftT
public import LeanVM.Guest.Data.NameStrings
import LeanVM.Guest.ValRef
import LeanVM.Guest.Data.ValNames.«verify_bus_gkr»

/-!
# `verify_bus_gkr`'s callees, within their words

`verify_bus_gkr_completeAtTB`: `verify_bus_gkr` placed within `vbgBound`: its frame, its buffers,
the radix-four layers' tree (`gkr_layers__L{o}` at `n_four = g^n`, `n ≤ 3`, `rem_g = g^r`,
`r < 4`: at most `KL` words), `verify_bus_gkr_loop0`'s words (`depth · K8` and its run's phantom
frame), and the frames of its conditional calls (`flat_completeAtOutTB`).
-/

namespace LeanVM.Guest.B1.Tables

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Memory
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Guest.B1.Main (MemL RegionL)

@[expose] public section

variable {fs : String → ℕ}

/-- `verify_bus_gkr`'s frames: the dispatch to `gkr_layers__L{o}`, then
`verify_bus_gkr_loop0`'s. -/
theorem vbg_flatCalls (σ : Val) : flatCalls vbgPre σ =
    [⟨[glcLsN 0, glcLsN 1].getD (logG (σ (.n (val% «verify_bus_gkr» "odd_g")))) "", [.n (val% «verify_bus_gkr» "layers"), .n (val% «verify_bus_gkr» "rounds"), .n (val% «verify_bus_gkr» "gkr_pts"), .n (val% «verify_bus_gkr» "n_four"), .n (val% «verify_bus_gkr» "rem_g"),
        .n (val% «verify_bus_gkr» "start_g"), .n (val% «verify_bus_gkr» "g_bus_mu"), .n (val% «verify_bus_gkr» "tabs"), .n (val% «verify_bus_gkr» "stream")], [.n (val% «verify_bus_gkr» "done")], true⟩,
      ⟨name% «verify_bus_gkr_loop0», [.n (val% «verify_bus_gkr» "s36#2"), .n (val% «verify_bus_gkr» "g_bus_mu"), .n (val% «verify_bus_gkr» "zeta"), .n (val% «verify_bus_gkr» "final_point_row")], [],
          decide (σ (.n (val% «verify_bus_gkr» "s36#1")) ≠ 0)⟩] := by
  unfold flatCalls
  rw [vbgPre_eq']
  rfl

variable {cert : String → V → ℕ}

/-- **`verify_bus_gkr` is complete, placed, within `vbgBound` words** (TRIAGE G #43), given the
words of the radix-four layers' trees (`gkr_layers__L{o}` at `n_four = g^n`, `n ≤ 3`,
`rem_g = g^r`, `r < 4`: `KL`) and of `verify_bus_gkr_loop0`'s runs (linear in their ends'
exponents, `K8`, and their phantom frame once), on every reader. -/
theorem verify_bus_gkr_completeAtTB {κ depth : ℕ} (hd2 : 2 ≤ depth) (hd : depth ≤ 32)
    (hκ : 6 ≤ κ) {cap0 xs : List E} {r : E × List E × List E} {cap' : List E}
    (hrun : RunsTo (gkrPhase depth) ⟨cap0, []⟩ xs r ⟨cap', []⟩)
    (hc : ∃ sp, (⟨cap0, []⟩ : Fs).Carries sp) (tabs stream : E) (ec ez : ℕ) {KL K8 : ℕ}
    (hL : ∀ o < 2, TotalLeOn coreProgram fs (glcLsN o)
      (fun a ↦ ∃ n ≤ 3, ∃ r < 4, a.getD 3 0 = gen ^ n ∧ a.getD 4 0 = gen ^ r) (fun _ ↦ KL))
    (h8 : TotalLeOn coreProgram fs name% «verify_bus_gkr_loop0» LoopPre
      (fun a ↦ logG (a.getD 1 0) * K8 + fs name% «verify_bus_gkr_loop0»)) :
    CompleteAtDTB fs cert κ "verify_bus_gkr" [(ec, xs), (ez, r.2.1)]
      (cap0 ++ [ofK (addressOfIndex ec), gen ^ depth, ofK (addressOfIndex ez), tabs, stream])
      (VbgOut cap' (ofK (addressOfIndex ec) * gen ^ xs.length) r.2.2) (fun _ ↦ True)
      (vbgBound fs KL K8 depth) := by
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
    (fun fp ↦ vbgW (ofK (addressOfIndex (vbgEL fs fp))) (ofK (addressOfIndex (vbgES fs depth fp)))
      (ofK (addressOfIndex (vbgER fs depth fp))) (ofK (addressOfIndex (vbgEP fs depth fp)))
      (ofK (addressOfIndex (vbgEO fs depth fp))) (ofK (addressOfIndex (vbgEB fs depth fp)))
      (ofK (addressOfIndex (vbgEM fs depth fp))) (ofK (addressOfIndex (vbgEV fs depth fp))))
    (vbgBufs fs depth xs ec) hbufs (fun fp rd hlow hL ↦ (hfacts fp rd hlow hL).1)
    (fun _ ↦ True) [fun _ ↦ True, fun _ ↦ True] (fun _ _ _ _ ↦ trivial)
    (by show (vbgPre.filter callB).length ≤ 2; decide +kernel)
    (fun _ _ _ _ i _ _ _ _ _ _ _ _ ↦ by rcases i with _ | _ | _ <;> trivial)
    [KL, depth * K8 + fs name% «verify_bus_gkr_loop0»] _
    (fun fp rd hlow hLm i c hci ht rd' hlow' hL' t rr hn hv hb ↦ ?_)
    (fun σ ↦ callsBound_le vbgPre σ _)).mono le_rfl (fun _ _ ↦ trivial)
  obtain ⟨-, hV, -⟩ := hfacts fp rd hlow hLm
  have hV' : VbgVals (vbgFlat.σ rd (vbgW (ofK (addressOfIndex (vbgEL fs fp)))
      (ofK (addressOfIndex (vbgES fs depth fp))) (ofK (addressOfIndex (vbgER fs depth fp)))
      (ofK (addressOfIndex (vbgEP fs depth fp))) (ofK (addressOfIndex (vbgEO fs depth fp)))
      (ofK (addressOfIndex (vbgEB fs depth fp))) (ofK (addressOfIndex (vbgEM fs depth fp)))
      (ofK (addressOfIndex (vbgEV fs depth fp))))
      (cap0 ++ [ofK (addressOfIndex ec), gen ^ depth, ofK (addressOfIndex ez), tabs, stream]))
      depth (vbgEL fs fp) (vbgER fs depth fp) (vbgEP fs depth fp) tabs stream := hV
  obtain ⟨v167, v400, v402, v169, v426, v6, v16, v17, v18, v8, v9, v425⟩ := hV'
  have hc' := hci
  rw [show vbgFlat.pre = vbgPre from rfl, vbg_flatCalls] at hc'
  rcases i with _ | _ | i
  · simp only [List.getElem?_cons_zero, Option.some.injEq] at hc'
    subst hc'
    have hf : [glcLsN 0, glcLsN 1].getD (logG (gen ^ (depth % 2))) "" = glcLsN (depth % 2) := by
      rw [gen_pow_eq_ofK, logG_spec (by omega)]
      rcases Nat.mod_two_eq_zero_or_one depth with h0 | h0 <;> simp [h0]
    simp only [v167, hf] at hn
    simp only [List.map_cons, List.map_nil] at hv
    rw [v400, v402] at hv
    exact hL (depth % 2) (by omega) rd' t _ rr hn ⟨(depth - 1) / 8, by omega,
      (depth - 1) / 2 % 4, by omega, by simp, by simp⟩ hv hb
  · simp only [List.getElem?_cons_succ, List.getElem?_cons_zero, Option.some.injEq] at hc'
    subst hc'
    simp only [List.map_cons, List.map_nil] at hv
    rw [v426, v6] at hv
    have hb' := h8 rd' t _ rr hn (loopPre_gen (by omega) (by omega) _) hv hb
    simp only [List.getD_cons_succ, List.getD_cons_zero, gen_pow_eq_ofK,
      logG_spec (show depth < 2 ^ 64 - 1 by omega)] at hb'
    simpa using hb'
  · simp at hc'

end
end LeanVM.Guest.B1.Tables
