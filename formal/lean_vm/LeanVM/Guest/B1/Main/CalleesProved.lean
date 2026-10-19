/-
  LeanVM.Guest.B1.Main.CalleesProved

  `main`'s callees complete, placed, by bounded trees (`CalleesAt`), from the groups' theorems.
-/

module

public import LeanVM.Guest.B1.Main.CalleesAt
public import LeanVM.Guest.B1.Sig.CompleteAt
public import LeanVM.Guest.B1.Digest.SmallAt
public import LeanVM.Guest.B1.Digest.ClaimListAt
public import LeanVM.Guest.B1.Digest.ChildListAt
public import LeanVM.Guest.B1.Da.CompleteAt
public import LeanVM.Guest.B1.VerifySub.CPlaced8
public import LeanVM.Guest.B1.Tables.VtCGkrB
public import LeanVM.Guest.B1.Tables.FlockAtB
public import LeanVM.Guest.B1.Tables.PlaceAt
public import LeanVM.Guest.B1.Tables.TermAtProof
public import LeanVM.Guest.B1.Tables.VtKidsB
public import LeanVM.Guest.B1.Whir.CapAgrees

/-!
# `main`'s callees, proved

`calleesAt_proved`: `CalleesAt fs cert 16 (VsGoodOf bytecode) (calleeBd H)` from the signature
verifiers' (group 2), the digests', the cover's and `da_verify`'s (group 3) and `verify_sub`'s
(group 6, over its callees' bounded theorems) bounded completeness. What is still assumed is in
`CalleesHyps`: the pure callees' tree bounds (`TotalLe`, for the static checker), `da_verify`'s two
certificate inequalities, and the pending `CompleteTablesAtB` and `CompleteOpenAtB`. A run of
`verify_sub` is good when it is an accepted proof's (`VsData.Ok`, `TOk`) whose openings agree in
the Merkle caps (`CapAgrees`).
-/

namespace LeanVM.Guest.B1.Main

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Protocol LeanVM.Protocol.Blake2sHash LeanVM.Protocol.Verifier LeanVM.Node
open LeanVM.Guest.Memory
open LeanVM.Guest.B1 (CompleteRelB CompleteAtB Returns LowDef Within disj_nil)
open LeanVM.Guest.B1.VerifySub (VsData VsBounds vsBound TCtx layoutOf)

@[expose] public section

/-- **What `CalleesAt` still assumes**: the pure callees' bounds (by the static checker), the
certificate's two inequalities `da_verify` takes, and the pending `verify_tables` and
`open_stacked` theorems. -/
structure CalleesHyps (fs : String → ℕ) (cert : String → V → ℕ) (bytecode : List K) : Type where
  Bx : ℕ
  xmss : TotalLe coreProgram fs "verify_lean_xmss" fun _ => Bx
  Bsp : ℕ
  sphincs : TotalLe coreProgram fs "verify_sig_lean_sphincs" fun _ => Bsp
  Bsd : ℕ
  sd : TotalLe coreProgram fs "statement_digest" fun _ => Bsd
  Bdl : E → ℕ
  dl : TotalLe coreProgram fs "da_list_digest" fun a => Bdl (a.getD 1 0)
  B86 : E → ℕ
  l86 : TotalLeOn coreProgram fs "__loop86" LoopPre fun a => B86 (a.getD 1 0)
  Bct : ℕ → ℕ
  ct : ∀ t, t < 32 → TotalLe coreProgram fs Digest.ctNames[t]! fun _ => Bct t
  Bsl : ℕ
  sl11 : TotalLe coreProgram fs "scaled_log__L11" fun _ => Bsl
  Bsl6 : ℕ
  sl6 : TotalLe coreProgram fs "scaled_log__L6" fun _ => Bsl6
  dvc20 : cert "da_verify" (.n 20) + 385 ≤ fs "da_verify"
  dvc4 : ∀ f, cert (Digest.vxName f) (.n 4) + 256 ≤ fs (Digest.vxName f)
  Btab : ℕ
  tab : VerifySub.CompleteTablesAtB fs cert 16 bytecode TCtx Btab
  tabW : ∀ {Θ : Type} (w : Θ → String → ℕ),
    VerifySub.CompleteTablesAtW fs cert 16 bytecode TCtx w Btab fun θ => VerifySub.vtTablesBoundW (w θ)
  Bop : ℕ
  op : VerifySub.CompleteOpenAtB fs cert 16 CapAgrees Bop

/-- A good run of `verify_sub`: an accepted proof's, its openings agreeing in the caps. -/
def VsGoodOf (bytecode : List K) (D : VsData) : Prop :=
  D.Ok bytecode ∧ D.TOk bytecode ∧
    CapAgrees (layoutOf bytecode D.logMem D.rows).stackLog D.rate D.root D.cvL D.xsW D.os D.target

/-- `verify_sub`'s callees' bounds. -/
def calleeVsB (fs : String → ℕ) {cert : String → V → ℕ} {bytecode : List K} (H : CalleesHyps fs cert bytecode) :
    VsBounds :=
  ⟨VerifySub.vtcGkrBound fs, H.Btab, flockBound fs, fs "certify_placement" + 276, H.Bop, termBound fs⟩

/-- `verify_sub`'s weight at `ω`, its statically bounded callees within `c`: its frame's, its callees'. -/
def vsWOf (ω : String → ℕ) (c : VerifySub.VsStat) : ℕ :=
  ω "verify_sub" + (2 * c.gpw + c.l2a + 2 * c.ac + VerifySub.vtcGkrBoundW ω + VerifySub.vtTablesBoundW ω +
    flockBoundW ω + 64 * (2 * ω "__loop84") + 28 * (2 * ω "__loop85") + c.pl + c.l2b) + c.os + termBoundW ω

/-- **The callees' bounds.** -/
def calleeBd (fs : String → ℕ) {cert : String → V → ℕ} {bytecode : List K} (H : CalleesHyps fs cert bytecode) :
    CalleeBounds where
  xmss := H.Bx
  sphincs := H.Bsp
  sd := H.Bsd
  daList := fun n => H.Bdl (gen ^ n)
  cover := fs "cover_da_root"
  cl := Digest.cldBound fs H.B86 H.Bct H.Bsl6
  ccl := Digest.ccldBound fs (fs "child_claims_window" + H.Bsl) H.Bsl6
  daVerify := Digest.dvTot fs
  daVerifyW := fun θ r => Digest.dvTot θ r
  vs := vsBound fs (calleeVsB fs H)
  vsW := vsWOf

/-- A bound that holds whenever a memory holds the caller's words. -/
theorem cp_atB_le {fs : String → ℕ} {cert : String → V → ℕ} {κ : ℕ} {f : String} {Lin : Layout}
    {args rets : List E} {B C : ℕ} (h : CompleteAtB fs cert κ f Lin args (Returns rets) B)
    (hBC : (∃ rd, LowDef κ rd ∧ MemL rd Lin) → B ≤ C) : CompleteAtB fs cert κ f Lin args (Returns rets) C := by
  intro fp
  by_cases hex : ∃ rd, LowDef κ rd ∧ MemL rd Lin
  · exact (h.mono le_rfl (hBC hex)) fp
  · exact ⟨0, [], rets, [], ⟨rfl, rfl⟩, by simp [Within], disj_nil, Nat.zero_le _, fun rd hl hL =>
      absurd ⟨rd, hl, by simpa using hL⟩ hex⟩

/-! ## The preconditions, group 7's and group 3's -/

theorem cp_sd {sig : Digest} {cells : List E} {rd : Reader} {a r : List E} (h : SdPreAt sig cells rd a r) :
    Digest.SdPreAt sig cells rd a r := by
  match a, r, h with
  | [_, _, _, _, _, _], [_, _], h => exact h

theorem cp_dl {claims : List DaClaim} {rd : Reader} {a r : List E} (h : DaListPreAt claims rd a r) :
    Digest.DaListPreAt claims rd a r := by
  match a, r, h with
  | [_, _], [_, _], h => exact h

theorem cp_cover {i : ℕ} {rd : Reader} {a r : List E} (h : CoverPreAt i rd a r) :
    Digest.CoverPreAt i rd a r := by
  match a, r, h with
  | [_, _, _, _], [_, _, _, _], h => exact h

theorem cp_cl {cs : List E} {rd : Reader} {a r : List E} (h : ClPreAt cs rd a r) : Digest.ClPreAt cs rd a r := by
  match a, r, h with
  | [_, _, _], [_, _], h => exact h

theorem cp_ccl {off : ℕ → ℕ} {cs : List E} {rd : Reader} {a r : List E} (h : CclPreAt off cs rd a r) :
    Digest.CclPreAt off cs rd a r := by
  match a, r, h with
  | [_, _, _, _, _, _, _], [_, _], h => exact h

theorem cp_dv {root vd : Digest} {rd : Reader} {a r : List E} (h : DaVerifyPreAt root vd rd a r) :
    Digest.DaPreAt root vd rd a r := by
  match a, r, h with
  | [_], [_, _, _, _], h => exact h

/-! ## The callees -/

set_option maxRecDepth 100000 in
/-- **`main`'s callees are complete, placed, by bounded trees**, at `κ = 16`, on the hypotheses
`CalleesHyps` still assumes. -/
theorem calleesAt_proved (fs : String → ℕ) (cert : String → V → ℕ) {bytecode : List K}
    (H : CalleesHyps fs cert bytecode) (hb : bytecode.length = 2 ^ 22) :
    CalleesAt fs cert 16 (VsGoodOf bytecode) (calleeBd fs H) where
  verify_lean_xmss := verify_lean_xmss_completeRelB fs cert H.xmss (by norm_num)
  verify_sig_lean_sphincs := verify_sig_lean_sphincs_completeRelB fs cert H.sphincs (by norm_num)
  statement_digest := fun sig cells args rets Lin hpre =>
    Digest.sd_completeRelAtB fs cert sig cells (fun _ => H.Bsd) H.sd args rets Lin
      fun rd h1 h2 => cp_sd (hpre rd h1 h2)
  da_list_digest := fun claims args rets Lin hpre =>
    cp_atB_le (Digest.dl_completeRelAtB fs cert claims (fun a => H.Bdl (a.getD 1 0)) H.dl args rets Lin
      fun rd h1 h2 => cp_dl (hpre rd h1 h2)) fun ⟨rd, h1, h2⟩ => by
        have hp := hpre rd h1 h2
        match args, rets, hp with
        | [_, _], [_, _], hp =>
          obtain ⟨-, rfl, -, -⟩ := hp
          exact le_rfl
  cover_da_root := fun i args rets Lin hpre =>
    Digest.cover_completeRelAtB fs cert (by norm_num) i args rets Lin fun rd h1 h2 => cp_cover (hpre rd h1 h2)
  claim_list_digest := fun cs args rets Lin hpre =>
    Digest.cld_completeRelAtB fs cert (by norm_num) cs H.B86 H.Bct H.Bsl6 H.l86 H.ct H.sl6 args rets Lin
      fun rd h1 h2 => cp_cl (hpre rd h1 h2)
  child_claim_list_digest := fun off cs args rets Lin hpre =>
    Digest.ccld_completeRelAtB fs cert (by norm_num) off cs H.Bsl H.Bsl6 H.sl11 H.sl6 args rets Lin
      fun rd h1 h2 => cp_ccl (hpre rd h1 h2)
  da_verify := fun wt root vd hw args rets Lin hpre =>
    Digest.da_verify_completeRelAtW fs cert (by norm_num) H.dvc20 H.dvc4 wt root vd hw args rets Lin
      fun rd h1 h2 => cp_dv (hpre rd h1 h2)
  verify_sub := fun D hD lpA sqA outA _ w c hc =>
    (VerifySub.verify_sub_completeAtW (bytecode := bytecode) (CapOk := CapAgrees) (Bs := calleeVsB fs H)
      (by norm_num) (VerifySub.VsWeightHyps.ofStat c hc)
      (Bsw := ⟨fun θ => VerifySub.vtcGkrBoundW (w θ), fun θ => VerifySub.vtTablesBoundW (w θ),
        fun θ => flockBoundW (w θ), fun θ => termBoundW (w θ)⟩)
      (VerifySub.verify_bus_gkr_completeAtW fs cert w (by norm_num)) (H.tabW w)
      (verify_flock_completeAtW fs cert w 16) (certify_placement_completeAtB fs cert (by norm_num)) H.op
      (check_opening_terminal_completeAtW fs cert w 16) hb hD.1 hD.2.1 hD.2.2 lpA sqA outA).wmono
      fun _ => le_rfl

end
end LeanVM.Guest.B1.Main
