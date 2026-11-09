/-
  LeanVM.Guest.B1.KeccakGkr.VkCV

  **`verify_keccak` is complete, placed** (`verify_keccak_completeAt`).
-/

module

public import LeanVM.Guest.B1.KeccakGkr.VkCU

/-!
# `verify_keccak`, complete and placed

`VkCompleteAtK fs cert κ`: for every accepting run of `keccakSeg` from a carried capacity `f` (the
instance coordinates `chis`, the output lanes `outs`, the words read `xs`, the committed outputs'
opening `op`, the inputs' point `point`, the slices), `verify_keccak` is complete at every frame
pointer: the caller's words are the stream, the coordinates and lanes, `z_vals` and the slices'
buffer, and the function writes `op` at `z_vals`, `point` at `z_vals·g^39`, the slices at
`slices`, and returns the capacity after, the cursor past `xs`, the word and the ring map's first
challenge.

`verify_keccak_completeAt`: it holds. The run is read back as a `VkData` (`vkData_of_run`); the
body is flat (`completeAt_flatG`): its buffers' words (`VkData.own`), its eighteen callees
(`VkData.kids`, complete by `kids_complete`), its honest valuation on the layout (`body_holds`),
its frames (`calls_match`) and loads (`loads_in`).
-/

namespace LeanVM.Guest.B1.VerifySub

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Guest.Memory LeanVM.Guest.B1.Fwd
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Protocol.KeccakGkr Finset
open LeanVM.Guest.B1.Main (MemL RegionL)

@[expose] public section

/-- **`verify_keccak`, placed** (fork c4's shape, with the carried capacity). -/
def VkCompleteAtK (fs : String → ℕ) (cert : String → V → ℕ) (κ : ℕ) : Prop :=
  ∀ (τ : ℕ) (f chis outs xs op point slices cap' : List E) (word m0 : E)
    (curE chiE olE zvE slE : ℕ), 9 ≤ τ → τ ≤ 28 → τ ≤ chis.length → outs.length = 25 →
    f.length = 5 → AllCanonical f → (∃ sp, (⟨f, []⟩ : Fs).Carries sp) →
    RunsTo (keccakSeg τ (chis.take τ) outs) ⟨f, []⟩ xs
      (([⟨qkeccak, op, word⟩], point, slices), m0) ⟨cap', []⟩ →
    CompleteAtD fs cert κ "verify_keccak"
      [(curE, xs), (chiE, chis), (olE, outs), (zvE, op), (zvE + qkeccakVarsCap, point),
        (slE, slices)]
      (f ++ [ofK (Parameters.addressOfIndex curE), gen ^ τ, ofK (Parameters.addressOfIndex chiE),
        ofK (Parameters.addressOfIndex olE), ofK (Parameters.addressOfIndex zvE), ofK
            (Parameters.addressOfIndex slE)])
      (Returns (cap' ++ [ofK (Parameters.addressOfIndex curE) * gen ^ xs.length, word, m0]))

theorem vk_noLoadIte : vkPre.all noLoadIte = true := by decide +kernel

theorem vk_loop : coreProgram.loop "verify_keccak" = false := by decide +kernel

namespace VkData

variable {D : VkData}

theorem own_fit (h : D.Ok) (B : ℕ) (ls : ℕ → ℕ) :
    List.Forall₂ (fun c s ↦ c.length ≤ s) (D.own B ls) D.sizes := by
  have hτ := h.1
  have e1 : (eqLevels (D.chis.take 4) 4).length = 30 := by
    rw [eqLevels_length (by simp; have := h.2.2.1; omega)]; rfl
  have e2 : (eqLevels D.rl 5).length = 62 := by rw [eqLevels_length (by rw [rl_length])]; rfl
  have e3 : (eqLevels D.I.1 4).length = 30 := by rw [eqLevels_length (by rw [I1_length h])]; rfl
  simp only [own, sizes, List.forall₂_cons, List.Forall₂.nil, and_true]
  simp [c0_point_length h, rl_length, claims_length h, e1, e2, e3, eqKernel_length, seg_length]

theorem kids_lay {fs : String → ℕ} {B curE chiE olE zvE slE : ℕ} {s : ℕ} (hs : s < 12) :
    (D.kids fs B curE chiE olE zvE slE)[s + 1]'(by rw [kids_length]; omega) =
      D.layKid fs B curE s := by
  interval_cases s <;> rfl

end VkData

variable {fs : String → ℕ} {cert : String → V → ℕ}

open VkData in
set_option maxRecDepth 20000 in
/-- **What `completeAt_flatG` asks of `verify_keccak`'s body**, on an honest run's data. -/
theorem vk_obl {D : VkData} (h : D.Ok) {cap' : List E} {m0 : E} (hfin : D.fin = (m0, ⟨cap', []⟩))
    (curE chiE olE zvE slE fp : ℕ) (fps : List ℕ) (outs : List (List E × Main.Layout))
    (hlen : fps.length = (D.kids fs (fp + fs "verify_keccak") curE chiE olE zvE slE).length)
    (hout : OutsOk (atAllG [] (D.kids fs (fp + fs "verify_keccak") curE chiE olE zvE slE) fps) outs)
    (rd : Reader)
    (hB : MemL rd (bufL (fp + fs "verify_keccak") D.sizes
      (D.own (fp + fs "verify_keccak") (D.lsOf fs fps))))
    (hLin : MemL rd (D.lin curE chiE olE zvE slE))
    (hto : MemL rd (takenOuts
      (atAllG [] (D.kids fs (fp + fs "verify_keccak") curE chiE olE zvE slE) fps) outs)) :
    MemL rd (Kid.lins (atAllG [] (D.kids fs (fp + fs "verify_keccak") curE chiE olE zvE slE) fps)) ∧
    RegionsOk (fun i ↦ RegionL (D.lin curE chiE olE zvE slE) i ∨
        RegionL (bufL (fp + fs "verify_keccak") D.sizes
          (D.own (fp + fs "verify_keccak") (D.lsOf fs fps))) i)
      (fun _ ↦ False) (atAllG [] (D.kids fs (fp + fs "verify_keccak") curE chiE olE zvE slE) fps)
      outs ∧
    ∃ σ : Val, Data.core12.params.map σ = D.args curE chiE olE zvE slE ∧
      (∀ s ∈ vkPre, DispOk σ s) ∧
      Stmt.HoldsList (fun _ _ _ ↦ True) rd σ Data.core12.body False
        (fun r ↦ r = cap' ++ [ptr curE * gen ^ D.xs.length, D.word, m0]) ∧
      (vkPre.filterMap Main.Stmt.allocSz).map (fun x ↦ x.2.elim id fun s ↦ logG (σ s)) = D.sizes ∧
      ((vkPre.filterMap Main.Stmt.allocSz).map Prod.fst).map σ =
        (bases (fp + fs "verify_keccak") D.sizes).map (fun b ↦ ofK (Parameters.addressOfIndex b)) ∧
      CallsMatch σ ((vkPre.filterMap (Stmt.callSF σ)).map (Main.mkCall σ))
        (atAllG [] (D.kids fs (fp + fs "verify_keccak") curE chiE olE zvE slE) fps) outs ∧
      ∀ q ∈ vkPre.filterMap Stmt.loadS, ∃ i, (σ q.1).limb 0 * Parameters.addressOfIndex q.2 =
        Parameters.addressOfIndex i ∧
        (RegionL (D.lin curE chiE olE zvE slE) i ∨
          RegionL (bufL (fp + fs "verify_keccak") D.sizes
            (D.own (fp + fs "verify_keccak") (D.lsOf fs fps))) i ∨
          outRegion (atAllG [] (D.kids fs (fp + fs "verify_keccak") curE chiE olE zvE slE) fps)
            outs i) := by
  generalize fp + fs "verify_keccak" = B at hB hout hto hlen ⊢
  have hk := kids_length (D := D) (fs := fs) (B := B) (curE := curE) (chiE := chiE) (olE := olE)
    (zvE := zvE) (slE := slE)
  have hfl : fps.length = 18 := by rw [hlen, hk]
  have hlenA : (atAllG [] (D.kids fs B curE chiE olE zvE slE) fps).length = 18 := by
    rw [atAllG_length, hk, hfl]; rfl
  obtain ⟨hol, hoi⟩ := outsOk_getElem hout
  have hto' := memL_takenOuts hto
  have hol' : outs.length = 18 := by rw [hol, hlenA]
  -- the layers' buffers
  have hlay : ∀ s (hs : s < 12), (outs[s + 1]'(by omega)).2 = layerBufs (D.layer s) (firstOf s)
      (ptr (curE + D.lcur s)) (D.lsOf fs fps s) := by
    intro s hs
    have := hoi (s + 1) (by omega) (by omega) (by rw [atAllG_getElem]; simp [kids_lay hs, layKid])
    rw [atAllG_getElem] at this
    simp only [kids_lay hs, layKid, List.nil_append] at this
    rw [this.2, take_last (by omega)]
    rfl
  have hm : D.Mem rd B curE chiE olE zvE slE (D.lsOf fs fps) := ⟨hB, hLin, fun s hs ↦ by
    rw [← hlay s hs]
    exact hto' (s + 1) (by omega) (by omega) (by rw [atAllG_getElem]; simp [kids_lay hs, layKid])⟩
  set σ := D.val rd B curE chiE olE zvE slE with hσd
  obtain ⟨-, -, -, -, -, -, -, h17, -⟩ := head_first h hm hσd
  refine ⟨memL_lins_of fun i hi ↦ ?_, regionsOk_ofI fun i hi ht x hx ↦ ?_, σ, ?_,
    vkPre_disp σ, ?_, body_sizes h hσd h17, body_bases h hσd,
    calls_match h hm hσd hfl hout, ?_⟩
  · rw [atAllG_getElem]
    have := kids_lin_mem h hm hfl i (by rw [hlenA] at hi; rw [hk]; exact hi)
    simpa using this
  · rw [atAllG_getElem] at hx
    simp only [List.nil_append] at hx
    refine kids_lin_region h hfl (T := fun i x ↦ (RegionL (D.lin curE chiE olE zvE slE) x ∨
        RegionL (bufL B D.sizes (D.own B (D.lsOf fs fps))) x) ∨ False ∨
        ∃ j, ∃ hjk : j < (atAllG [] (D.kids fs B curE chiE olE zvE slE) fps).length,
          ∃ hjo : j < outs.length, j < i ∧ (atAllG [] (D.kids fs B curE chiE olE zvE slE) fps)[j].taken = true ∧
          RegionL (outs[j]).2 x)
      (fun j x hx ↦ Or.inl (Or.inl hx)) (fun j x hx ↦ Or.inl (Or.inr hx))
      (fun k hk j hkj x hx ↦ Or.inr (Or.inr ⟨k + 1, by omega, by omega, hkj,
        by rw [atAllG_getElem]; simp [kids_lay hk, layKid], by rw [hlay k hk]; exact hx⟩))
      i (by rw [hlenA] at hi; rw [hk]; exact hi) x hx
  · rw [show Data.core12.params = [.n 0, .n 1, .n 2, .n 3, .n 4, .n 5, .n 6, .n 7, .n 8, .n 9,
      .n 10] from rfl]
    have hpar := (val_good (rd := rd) (B := B) (curE := curE) (chiE := chiE) (olE := olE)
      (zvE := zvE) (slE := slE) h).2.2
    apply List.ext_getElem (by simp [args_length h])
    intro i h1 h2
    simp only [List.length_map, List.length_cons, List.length_nil] at h1
    rw [List.getElem_map, ← List.getD_eq_getElem _ 0 h2, ← hpar i (by omega)]
    interval_cases i <;> rfl
  · exact vk_body ▸ body_holds h hm hσd hfin
  · exact loads_in h hm hσd (T := fun i ↦ RegionL (D.lin curE chiE olE zvE slE) i ∨
        RegionL (bufL B D.sizes (D.own B (D.lsOf fs fps))) i ∨
        outRegion (atAllG [] (D.kids fs B curE chiE olE zvE slE) fps) outs i)
      (fun i hi ↦ Or.inl hi) (fun i hi ↦ Or.inr (Or.inl hi))
      (fun s hs i hi ↦ Or.inr (Or.inr (outRegion_ofI (s + 1) (by omega) (by omega)
        (by rw [atAllG_getElem]; simp [kids_lay hs, layKid]) (by rw [hlay s hs]; exact hi))))


open VkData in

end
end LeanVM.Guest.B1.VerifySub
