/-
  LeanVM.Guest.B1.VerifySub.H.KidsB

  `verify_sub`'s callees but the tables, the Keccak reduction, the opening and the terminal,
  placed within their bounds, on an honest child's words.
-/

module

public import LeanVM.Guest.B1.VerifySub.H.Runs
public import LeanVM.Guest.B1.VerifySub.BoundsB
public import LeanVM.Guest.B1.Bits.GrindPlaced
public import LeanVM.Guest.B1.Bits.BusGrindPlaced
public import LeanVM.Guest.B1.Fs.SqueezePlaced
public import LeanVM.Guest.B1.Fs.MessagePlaced
public import LeanVM.Guest.B1.Fs.SqueezePoint
public import LeanVM.Guest.B1.Fs.MessageComplete
public import LeanVM.Guest.B1.Bits.Log2PlacedAll
public import LeanVM.Guest.B1.Gkr.VbgB
public import LeanVM.Guest.B1.Ring.CompleteB
public import LeanVM.Guest.Budget.Bounded
public import LeanVM.Guest.B1.Bits.GPower
public import LeanVM.Guest.B1.Fwd.PureIn

/-!
# The plain callees, bounded

`winTabs_vsExp`: the caller's exponent tables (`vsExpLin`) hold the window table. The callees,
each `CompleteAtB` within its `vsBsWith` entry: `g_power_of_word` (`gpw_completeAtB`), a
`grind_check` on a passing proof of work (`grind_kidB`), a `bus_grind_check` arm (`busGrind_kidB`),
`squeeze_point_from` (`spf_kidB`), `opening_message__L1_L1` (`om_kidB`); on an honest child's
segments, `verify_bus_gkr` (`vbg_kidB`).
-/

namespace LeanVM.Guest.B1.VerifySub

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Node LeanVM.Guest.Memory

@[expose] public section

variable {fs : String → ℕ} {cert : String → V → ℕ}

/-- **The exponent tables hold the window table.** -/
theorem winTabs_vsExp {rd : Reader} {sqE : ℕ} (h : Main.MemL rd (vsExpLin sqE)) :
    WinTabs rd (ptr sqE * gen ^ winTabAt) := by
  have hr : ∀ o < 2284, LoadHolds rd (ptr sqE) o (expTabWord o) := by
    intro o ho
    have := h _ List.mem_cons_self o (by rw [length_expTabAllWords]; exact ho)
    simpa [expTabAllWords] using this
  have hw := ((expTabAll_iff rd _).2 hr).2
  exact fun n hn ↦ (loadHolds_mul_gen_pow rd _ _ _ _).2 (hw n hn)

theorem vs_gpw_pure : coreProgram.PureIn ["g_power_of_word"] :=
  Tables.pureIn_of_pureInB (by decide +kernel)

/-- **`g_power_of_word`, placed, within its words.** -/
theorem vs_gpw_completeAtB (κ : ℕ) (Lin : Main.Layout) {n : ℕ} (hn : n < 2 ^ 6) {Bg : ℕ}
    (hg : TotalLe coreProgram fs "g_power_of_word" fun _ ↦ Bg) :
    CompleteAtB fs cert κ "g_power_of_word" Lin [eOfNat n] (Returns [gen ^ n]) Bg :=
  completeAt_of_rel_pureB (B := fun _ ↦ Bg) vs_gpw_pure (List.mem_singleton_self _)
    (fun rd _ ↦ (g_power_of_word_holds rd [eOfNat n] [gen ^ n]).2
      (show ∃ m < 2 ^ 6, eOfNat n = eOfNat m ∧ [gen ^ n] = [gen ^ m] from ⟨n, hn, rfl, rfl⟩)) κ hg

/-- **A `grind_check` on a passing proof of work**, the window table from the caller's. -/
theorem grind_kidB {bits : ℕ} (hb : bits ∈ grindBitsDeployed) {κ : ℕ} (hκ : 11 ≤ κ) {B : ℕ}
    (hT : TotalLe coreProgram fs (grindCheckName bits) fun _ ↦ B) {w : E} (sqE : ℕ)
    (hpow : (w.limb 0).lane.toNat % 2 ^ bits = 0) :
    CompleteAtB fs cert κ (grindCheckName bits) (vsExpLin sqE) [w, ptr sqE * gen ^ winTabAt]
      (Returns []) B :=
  grind_check_completeB_of hb hκ hT _ _ _ fun _ _ hL ↦ ⟨rfl, w, _, rfl, winTabs_vsExp hL, hpow⟩

/-- **A `bus_grind_check` arm on a passing proof of work.** -/
theorem busGrind_kidB {d : ℕ} (hd : d ∈ busGrindDeployed) {κ : ℕ} (hκ : 11 ≤ κ) {w : E}
    (sqE : ℕ) (hpow : (w.limb 0).lane.toNat % 2 ^ busGrindBits d = 0) :
    CompleteAtB fs cert κ (busGrindName d) (vsExpLin sqE) [w, ptr sqE * gen ^ winTabAt]
      (Returns [0]) (fs (busGrindName d) + fs (grindCheckName (busGrindBits d))) :=
  bus_grind_check_completeB hd hκ _ _ _ fun _ _ hL ↦ ⟨rfl, w, _, rfl, winTabs_vsExp hL, hpow⟩

theorem le_busGrindMax {d : ℕ} (hd : d < 14) :
    fs (busGrindName d) + fs (grindCheckName (busGrindBits d)) ≤ busGrindMax fs := by
  rw [busGrindBits_eq]
  exact le_lmax (List.mem_map.2 ⟨d, List.mem_range.2 hd, rfl⟩)

/-- **`squeeze_point_from__L{n}`** from a permutation's challenge and capacity. -/
theorem spf_kidB {n : ℕ} (hn : n ∈ spfDeployed) (κ : ℕ) {B : ℕ}
    (hT : TotalLe coreProgram fs (spfName n) fun _ ↦ B) (S0 : KeccakState) (b : ℕ) :
    CompleteAtB fs cert κ (spfName n)
      [(b, challengeOf S0 :: ((⟨capOf S0, []⟩ : Fs).squeezeN (n - 1)).1)]
      (capOf S0 ++ [challengeOf S0, ptr b])
      (Returns ((⟨capOf S0, []⟩ : Fs).squeezeN (n - 1)).2.cap) B :=
  squeeze_point_from_completeB_of hn κ hT _ _ _ fun _ _ hL ↦ ⟨hL _ List.mem_cons_self, rfl⟩

/-- **`opening_message__L1_L1`**: one value, then the nonce, at the cursor `b + 11`; the value
stored at `o`. -/
theorem om_kidB (κ : ℕ) {B : ℕ} (hT : TotalLe coreProgram fs "opening_message__L1_L1" fun _ ↦ B)
    (cap : List E) (hcap : cap.length = 5) (v nn : E) (b o : ℕ) :
    CompleteAtB fs cert κ "opening_message__L1_L1" [(b + 11, [v, nn]), (o, [v])]
      (cap ++ [ptr b * gen ^ 11, ptr o])
      (Returns ([cellsOfState (omState cap [v] (some nn)) false 0,
        cellsOfState (omState cap [v] (some nn)) false 1] ++ capOf (omState cap [v] (some nn)) ++
        [ptr b * gen ^ 11 * gen ^ 2])) B := by
  match cap, hcap with
  | [f0, f1, f2, f3, f4], _ =>
  refine completeRelB_of_leaf (om_leafSpecOk (1, 1) (by simp [omDeployed]))
    (opening_message_holds (1, 1) (by simp [omDeployed])) (fun _ _ _ h ↦ h.2.2.2)
    (om_pin 1 1 [v, nn]) κ hT _ _ _ fun rd _ hL ↦ ?_
  have hc : ReadsAt rd (ptr b * gen ^ 11) [v, nn] := by
    rw [ofK_gpow_mul_gen]; exact hL _ List.mem_cons_self
  have ho : ReadsAt rd (ptr o) [v] := hL _ (List.mem_cons_of_mem _ List.mem_cons_self)
  have hc1 : ReadsAt rd (ptr b * gen ^ 11) [v] := fun k hk ↦ by
    obtain rfl : k = 0 := by simpa using hk
    exact hc 0 (by simp)
  exact ⟨rfl, hc, ho, [v], rfl, hc1, ho, nn, fun _ ↦ hc 1 (by simp), rfl⟩

namespace ChildSegs

variable {bytecode : List K} {seed : Digest} {c : Child} (S : ChildSegs bytecode seed c)

/-- **`verify_bus_gkr` on an honest child, within `vbgMax`.** -/
theorem vbg_kidB (hbl : bytecode.length = 2 ^ 23) {κ : ℕ} (hκ : 6 ≤ κ) (W : VsWordsOs fs)
    (bs : List ℕ) (sqE : ℕ) :
    CompleteAtB fs cert κ "verify_bus_gkr" [(cG bs, S.xsG), (vb bs 5, S.rG.2.1)]
      (S.s3.cap ++ [ptr (cG bs), gen ^ S.d, ptr (vb bs 5), ptr sqE * gen ^ winTabAt])
      (Tables.VbgOut S.s4.cap (ptr (cG bs) * gen ^ S.xsG.length) S.rG.2.2)
      (vbgMax fs W.K29 W.R W.K8) := by
  have hd := S.d_bounds hbl
  obtain ⟨h3, h4, -⟩ := S.gkr_inv hbl
  have hrun : RunsTo (Tables.gkrPhase S.d) ⟨S.s3.cap, []⟩ S.xsG S.rG ⟨S.s4.cap, []⟩ := by
    rw [← h3, ← h4]; exact S.runG
  have hc : ∃ sp, (⟨S.s3.cap, []⟩ : Fs).Carries sp := by rw [← h3]; exact S.c3
  have hB : Tables.vbgBound fs W.K29 W.R W.K8 S.d ≤ vbgMax fs W.K29 W.R W.K8 := by
    unfold vbgMax
    exact le_lmax (List.mem_map.2 ⟨S.d, List.mem_range.2 (by omega), rfl⟩)
  exact (Tables.verify_bus_gkr_completeAtTB (by omega) (by omega) hκ hrun hc
    (ptr sqE * gen ^ winTabAt) (cG bs) (vb bs 5) W.h29 W.hR W.h8).toCompleteAtB.mono le_rfl hB

end ChildSegs

end
end LeanVM.Guest.B1.VerifySub
