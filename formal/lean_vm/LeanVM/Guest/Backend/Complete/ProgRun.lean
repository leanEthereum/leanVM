/-
  LeanVM.Guest.Backend.Complete.ProgRun

  Every function of a compiled program passing the per-function conditions runs, counted within
  its placed path maxima and separately counted arms, on any frame holding `FHB`.
-/

module

public import LeanVM.Guest.Backend.Complete.ProgFrames
public import LeanVM.Guest.Backend.Complete.Fn
public import LeanVM.Guest.Backend.Complete.PathOps

/-!
# Each function runs

`cplRun_B`: on a memory holding the jump tables and the frame `FHB` asks, the frame family
`famB` (`famB_ok`) gives the instructions' meaning (`CplBody`), `fnCompleteStmt` the counted run
within `pathOps` and the callees' counts, `pathOpsStmt` (on an aligned body, with `keyedB`'s
distinct selectors) the bound `fnCost`, and the returns are the family's words at the return
cells (`placed_rets`, `FrameClauses.cell`, `FrameOK.own`).
-/

namespace LeanVM.Guest.Backend.Complete

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Memory

@[expose] public section

variable {κ₀ : ℕ} {W : World κ₀}

/-- `keyedB`'s choice has its stages on distinct selectors. -/
theorem keyedB_nodup (keyed : String → Bool) (tf : TracedFn) (pf : Placed) :
    ((armsP (World.keyedB keyed tf pf) tf pf).map (·.1)).Nodup := by
  cases h : World.keyedB keyed tf pf with
  | false => simp [armsP]
  | true =>
    unfold World.keyedB at h
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    exact h.2

/-- **Every function runs, counted**, on a frame holding `FHB`. -/
theorem cplRun_B (hW : W.Compiled) (hC : ∀ tf ∈ W.p, FnConds W tf) (keyed : String → Bool) :
    ∀ tf ∈ W.p, CplRunW W (FHB W) (fun f σ op => W.fnCost keyed f σ op) tf := by
  intro tf htf κ L hJT fp hm σ es vs hw hev kfps hdr hF ck hK
  obtain ⟨tf', pf, hfo, hfok, haddr⟩ := hF
  obtain ⟨htf', hn', hpa, -⟩ := fnOf_spec hfo
  have htt : tf = tf' := eq_of_name (placed_names hW).2 htf htf' hn'.symm
  subst htt
  have hCt := hC tf htf
  have hok := famB_ok hW htf hCt hpa hm kfps hdr
  obtain ⟨hcl, hrun⟩ := hok.2 σ es vs hw haddr
  have hcl' := hcl L.read hev
  have hbody := hrun L ck hfok hev hJT hK
  obtain ⟨r, c, hr, hrunC, hle⟩ := fnCompleteStmt (World.withL W L) hW tf htf pf hpa fp hm σ
    (kfps.zip ck) hbody
  have hlen : kfps.length = ck.length := by rw [hfok.len, hK.1]
  have hzip : (kfps.zip ck).map Prod.snd = ck := List.map_snd_zip (by omega)
  refine ⟨r, c, hr, hrunC, fun op => ?_, fun k hk => ?_⟩
  · have hsum : ((kfps.zip ck).map (·.2 op)).sum = (ck.map (· op)).sum := by
      conv_rhs => rw [← hzip, List.map_map]
      rfl
    have := hle op
    rw [hsum] at this
    show c op ≤ W.fnCost keyed tf.core.name σ op + _
    unfold World.fnCost
    rw [hfo]
    dsimp only
    split
    · next hal =>
      have hops := pathOpsStmt tf pf hal (World.keyedB keyed tf pf)
        (keyedB_nodup keyed tf pf) σ es vs hw op
      omega
    · omega
  · have hrk := placed_rets hW htf hpa hw k hk
    have hcellv := hcl'.cell vs[k] (by simp [readsP, List.getElem_mem]) _ hrk
    have := hfok.own _ hcellv.1 hcellv.2.1
    rw [hcellv.2.2] at this
    exact this

end
end LeanVM.Guest.Backend.Complete
