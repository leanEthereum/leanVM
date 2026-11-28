/-
  LeanVM.Guest.B1.Whir.Verify

  `open_stacked`'s run with the terminal's check is a run of the statement's `verifyWhir`.
-/

module

public import LeanVM.Guest.B1.Whir.Sound
public import LeanVM.Guest.B1.Whir.LastRun

/-!
# `open_stacked` runs `verifyWhir`

`open_stacked` runs `verifyWhir` (`Statement/Verifier/Whir.lean`) up to its last `require`, the
terminal's check, which `check_stack_terminal` makes on the returned claim, weight and residual
(`verifyWhir_split`). `OpenOutW.runs_verifyWhir`: at any basis whose value at the returned point
passes that check, the words and openings of a call (`open_stacked_osW`, `open_stacked_sound_w`)
run `verifyWhir stackLog logInvRate target basis` to its end, from the sponge the guest carries as
the capacity `fs` and the stack's root committed with its shape. `open_stacked_verifyWhir`: the
same, for every specialization's call, the statement `verify_sub`'s later sections chain.
-/

namespace LeanVM.Guest.B1.Whir

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

/-- **A call's words and openings run `verifyWhir`**, at a basis passing the terminal's check. -/
theorem OpenOutW.runs_verifyWhir {rd : Reader} {μ r : ℕ} {root : Digest} {fs : List E}
    {target cur : E} {rets xs : List E} {os : List (List Opening)}
    (h : OpenOutW rd μ r root fs target cur rets xs os) :
    ∃ (w : WhirEnd) (s' : Fs) (roots' : List (Digest × ℕ × ℕ)),
      ReadsAt rd cur xs ∧ w.point.length = μ ∧
      (∃ pt pt1 cur' : E, rets = [w.target, pt, pt1, w.inner, w.residual, cur'] ∧
        ReadsAt rd pt (w.point ++ List.replicate (pointCap - μ) 0) ∧
        ReadsAt rd pt1 (w.point.map (1 + ·) ++ List.replicate (pointCap - μ) 1)) ∧
      ∀ basis : List E → E, (w.inner + basis w.point) * w.residual = w.target →
        RunsWith (verifyWhir μ r target basis) ⟨fs, []⟩ xs os [(root, stackShape μ r)] () s'
          roots' := by
  obtain ⟨w, s', roots', hrd, hrun, hlen, hrest⟩ := h
  refine ⟨w, s', roots', hrd, hlen, hrest, fun basis hacc ↦ ?_⟩
  rw [verifyWhir_split]
  have hb := RunsWith.bind (f := fun w : WhirEnd ↦ VerifierProgram.require (w.Accepts basis)) hrun
    (runsWith_require (c := w.Accepts basis) hacc s' roots')
  simpa using hb

/-- **`open_stacked` runs `verifyWhir`**: at every stack log `16 ≤ μ ≤ 30` and rate `1 ≤ r ≤ 4`,
a call of the size's specialization on the rate's selector reads the words and openings
`open_stacked_osW` at its frame, returns the claim, the point (and one plus it), the weight, the
residual and the cursor, and at any basis passing the terminal's check on them, those words and
openings run `verifyWhir μ r target basis`. -/
theorem open_stacked_verifyWhir {κ : ℕ} (hκ : κ ≤ 32) (hwb : winTabBits ≤ κ) (L : MemoryImage κ)
    (C : CallRel) (V : FrameMap) (hU : UnfoldsVP coreProgram L.read C V)
    (hle : CallRel.Le C (coreProgram.Rel L.read)) (μ r : ℕ) (h1 : minOpenLog ≤ μ) (h2 : μ ≤ 30)
    (h3 : 1 ≤ r) (h4 : r ≤ 4) (root : Digest) (fs : List E) (target root0 root1 cur tabs : E)
    (rets : List E) (fn : Fn) (σ : Val) (hfs : fs.length = 5) (hroot : (root0, root1) = digestHalves root)
    (hwt : WinTabs L.read tabs) (hfind : coreProgram.find? (openName μ) = some fn)
    (hp : fn.params.map σ = rateSel r :: fs ++ [target, root0, root1, cur, tabs])
    (hh : Stmt.HoldsList C L.read σ fn.body False (fun rs ↦ rs = rets)) :
    ∃ (w : WhirEnd) (s' : Fs) (roots' : List (Digest × ℕ × ℕ)),
      ReadsAt L.read cur (open_stacked_osW L.read (μ - minOpenLog) r σ V).1 ∧ w.point.length = μ ∧
      (∃ pt pt1 cur' : E, rets = [w.target, pt, pt1, w.inner, w.residual, cur'] ∧
        ReadsAt L.read pt (w.point ++ List.replicate (pointCap - μ) 0) ∧
        ReadsAt L.read pt1 (w.point.map (1 + ·) ++ List.replicate (pointCap - μ) 1)) ∧
      ∀ basis : List E → E, (w.inner + basis w.point) * w.residual = w.target →
        RunsWith (verifyWhir μ r target basis) ⟨fs, []⟩ (open_stacked_osW L.read (μ - minOpenLog) r σ V).1
          (open_stacked_osW L.read (μ - minOpenLog) r σ V).2 [(root, stackShape μ r)] () s' roots' :=
  (open_stacked_sound_w hκ hwb L C V hU hle μ r h1 h2 h3 h4 root fs target root0 root1 cur tabs rets
    fn σ hfs hroot hwt hfind hp hh).runs_verifyWhir

end
end LeanVM.Guest.B1.Whir
