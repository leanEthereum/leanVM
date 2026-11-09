/-
  LeanVM.Guest.B1.VerifySub.H.WhirLen

  `open_stacked` on an honest child: its terminal point has `μ` coordinates, and it is complete as
  `verify_sub`'s twelfth callee (`H/KidsC`'s `hos`).
-/

module

public import LeanVM.Guest.B1.VerifySub.H.TermPre
public import LeanVM.Guest.B1.VerifySub.H.Kids
public import LeanVM.Guest.B1.Whir.BrBody
public import LeanVM.Guest.B1.Place.OsCandAll

namespace LeanVM.Guest.B1.VerifySub

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Node

@[expose] public section

/-- **An accepted opening's terminal point has `μ` coordinates.** -/
theorem whir_point_length {μ r : ℕ} (h1 : 22 ≤ μ) (h2 : μ ≤ 28) (h3 : 1 ≤ r) (h4 : r ≤ 4)
    {S : KeccakState} {root : Digest} {target : E} {xs : List E} {os : List (List Opening)}
    {w : B1.Whir.WhirEnd} {s' : Fs} {roots' : List (Digest × ℕ × ℕ)}
    (hrun : B1.Whir.RunsWith (B1.Whir.whirOpen μ r target) ⟨capOf S, []⟩ xs os
      [(root, B1.Whir.stackShape μ r)] w s' roots')
    (hnz : B1.Whir.NoZeroChallenge μ r target S xs os root) : w.point.length = μ := by
  have hm : B1.Whir.candidate μ r < 28 := by unfold B1.Whir.candidate; omega
  obtain ⟨cfg, hF, -, -⟩ := B1.Whir.candB_sound (B1.Whir.candB_all μ r h1 h2 h3 h4)
  have hs := (placedP_sound (placedP_all _ hm)).2.2.1
  obtain ⟨c0, c2, tr, -, hplen, hptC, -⟩ := B1.Whir.osBodyA_honest hF hs hrun hnz
  unfold B1.Whir.ptC at hptC
  rw [hplen] at hptC
  have := List.append_cancel_right hptC
  rw [← this, hplen]

namespace ChildSegs

variable {bytecode : List K} {seed : Digest} {c : Child} (S : ChildSegs bytecode seed c)

theorem w_point_length : S.w.point.length = S.μs :=
  whir_point_length S.hmu22 S.hmu28 S.hr1 S.hr4 S.runW S.nzW

end ChildSegs

variable {fs : String → ℕ} {cert : String → V → ℕ}

/-- **`open_stacked` is complete on an honest child**, as `verify_sub` calls it. -/
theorem os_kid_complete {bytecode : List K} {seed : Digest} {c : Child} (S : ChildSegs bytecode seed c)
    {κ : ℕ} (hκ : 7 ≤ κ) (hrf : Lift.RunsFit fs cert) (hcons : RunsConsec cert) (bs : List ℕ) :
    CompleteAtD fs cert κ (B1.Whir.openName S.μs S.rate) [(S.cW bs, S.xsW)]
      (capOf S.s8.perm ++ [S.target, (digestHalves S.root).1, (digestHalves S.root).2,
        ofK (addressOfIndex (S.cW bs))]) (vsOsOut S.μs S.w) :=
  B1.open_stacked_completeAtD S.μs S.rate S.hmu22 S.hmu28 S.hr1 S.hr4 fs cert κ hrf hcons hκ
    (fun _ _ ↦ trivial) S.s8.perm S.root S.target _ S.xsW c.proof.openings S.w S.s' S.roots' S.runW
    S.nzW S.capsW [(S.cW bs, S.xsW)] (fun _ _ hm ↦ hm _ List.mem_cons_self)

end
end LeanVM.Guest.B1.VerifySub
