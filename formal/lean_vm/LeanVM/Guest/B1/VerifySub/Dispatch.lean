/-
  LeanVM.Guest.B1.VerifySub.Dispatch

  `verify_sub`'s call of `open_stacked`: its returns, at the witness the frame map gives.
-/

module

public import LeanVM.Guest.B1.VerifySub.Proof
public import LeanVM.Guest.B1.Whir.InterfaceW

/-!
# The call of `open_stacked`

* `vs_dispatch`: given `open_stacked`'s soundness with its witness (`open_stacked_sound_w_Spec`),
  a call of the specialization of the stack log `m` and the rate `lir` on `verify_sub`'s argument
  words (`vsOsArgs`) returns `OpenOutW` at the words and openings `vsOsW` reads off the frame map.
* `cfg_cons`: every admissible stack log and rate has a WHIR ladder of at least one level.
-/

namespace LeanVM.Guest.B1.VerifySub

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

variable {C : CallRel} {σ : Val}

/-- **The call of `open_stacked`** (G:3691-3698): the stack log's arm on the rate's selector; its
returns are `OpenOutW` at the witness of the frame map `V`. -/
theorem vs_dispatch (hos : Whir.open_stacked_sound_w_Spec Whir.open_stacked_osW) {κ : ℕ}
    (hκ : κ ≤ 32) (hκw : winTabBits ≤ κ) (L : MemoryImage κ) {V : FrameMap}
    (hU : UnfoldsV L.read C V) (hC : CallRel.Le C (coreProgram.Rel L.read)) {m lir : ℕ}
    (hm20 : Whir.minOpenLog ≤ m) (hm30 : m ≤ 30) (hl1 : 1 ≤ lir) (hl4 : lir ≤ 4) {root : Digest}
    (h66 : σ (.n 66) = Whir.rateSel lir)
    (hroot : (σ (.n 268), σ (.n 271)) = digestHalves root) (hwin : WinTabs L.read (σ (.n 1921)))
    (hc : C (Whir.openName m) (vsOsArgs σ) (vsOsRets σ)) :
    Whir.OpenOutW L.read m lir root
      [σ (.n 1370), σ (.n 1371), σ (.n 1372), σ (.n 1373), σ (.n 1374)] (σ (.n 1917))
      (σ (.n 1919)) (vsOsRets σ) (vsOsW L.read V (m - Whir.minOpenLog) lir (vsOsArgs σ) (vsOsRets σ)).1
      (vsOsW L.read V (m - Whir.minOpenLog) lir (vsOsArgs σ) (vsOsRets σ)).2 := by
  obtain ⟨fn, hfind, hpar, hbody⟩ := hU _ _ _ hc
  refine hos hκ hκw L C V hU hC m lir hm20 hm30 hl1 hl4 root _ (σ (.n 1917)) (σ (.n 268))
    (σ (.n 271)) (σ (.n 1919)) (σ (.n 1921)) _ fn _ rfl hroot hwin hfind ?_ hbody
  rw [show Whir.openNames.getD (m - Whir.minOpenLog) "" = Whir.openName m from rfl, hpar, vsOsArgs,
    h66]
  rfl

/-- Every admissible ladder has a level. -/
theorem ladder_cons_all : ∀ μ < 31, ∀ r < 5, 20 ≤ μ → 1 ≤ r →
    ((Whir.ladder μ r).map List.isEmpty) = some false := by
  decide +kernel

theorem cfg_cons {μ r : ℕ} (h1 : B1.Whir.minOpenLog ≤ μ) (h2 : μ ≤ 30) (h3 : 1 ≤ r) (h4 : r ≤ 4) :
    ∃ level rest, Whir.ladder μ r = some (level :: rest) := by
  have h := ladder_cons_all μ (by omega) r (by omega) h1 h3
  rcases e : Whir.ladder μ r with _ | _ | ⟨level, rest⟩
  · rw [e] at h; simp at h
  · rw [e] at h; simp at h
  · exact ⟨level, rest, rfl⟩

end
end LeanVM.Guest.B1.VerifySub
