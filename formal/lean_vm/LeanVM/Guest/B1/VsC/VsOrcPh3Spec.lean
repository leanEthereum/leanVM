/-
  LeanVM.Guest.B1.VsC.VsOrcPh3Spec

  `Ph12toEndS` from the phases' honest inputs on a context, chained.
-/

module

public import LeanVM.Guest.B1.VsC.VsOrcCtxEnd
public import LeanVM.Guest.B1.VsC.VsOrcPhOpenE

/-!
# `Ph12toEndS` from the honest inputs at the pinned ends

`Ph12EndP al x Own st ec ev er`: at `Ph12`'s state `st`, `Ph1213In` at some values with `link_terminal`'s call ending
at `ec`, then `KecEndP` (`Ph35In`, `verify_keccak` and `ring_switch_target` ending at `ev`, `er`), then `OpenEnd`
(`PhOpenIn` with `open_stacked` ending at `x.ec 16`, and `EndOk`, the export's and the end's facts).
**`ph12toEndP_of`**: `Ph12toEndP al` from `Ph12EndP` at the pinned ends, `check_stack_terminal`'s end within `2^24`
of its cursor (vsbnd's `CheckStackTerminalCompleteAE`) and `Hon.hend`, so the end state is within `2^40` of the
cursor (`x.kEndB`).
-/

namespace LeanVM.Guest.B1.VsC

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Memory LeanVM.Guest.B1
open LeanVM.Guest.Complete LeanVM.Guest.B1.Fwd LeanVM.Guest.B1.Stack LeanVM.Guest.B1.Whir LeanVM.Node
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Prover.Exec (wordNat bitWord allocBase)
open LeanVM.Guest.B1.Link (ltNames)

@[expose] public section

/-- **The export's and the end's facts on an honest context**: the overlay fact, the fresh claim's point `r_pt`'s
words, `open_stacked`'s post the Merkle hints' pops, the announced layout, the own entries `.n 6`, `.n 9`, `.n 14`
(the fresh claim's values) and `.n 8` (the bits of `.n 240`'s exponent). -/
def EndOk (x : VsCtx) (O : Reader → Prop) (Qo : Reader → Tree → Prop) : Prop :=
  VsFresh x.rd1 x.rd0 x.w x.args ∧ x.c.freshClaim.point = (x.bw.getD 6 []).take 19 ∧
  (∀ rd, LowDef 17 rd → x.Pre rd → O rd → ∀ t, Qo rd t →
    PopsPost (Prover.merkleHints true (Prover.childQueries guestBytecode x.seed x.c) x.c.proof.openings) rd t) ∧
  ∃ (layout : Layout) (rate : ℕ), announcedLayoutAndRate guestBytecode x.c.proof.stream = some (layout, rate) ∧
    x.bw.getD 0 [] = layout.tableLogHeights.map Prover.count ∧ x.bw.getD 3 [] = vsLinkShape layout ∧
    x.bw.getD 8 [] = x.c.freshClaim.values ∧
    ∃ n, n < 2 ^ 24 ∧ x.σ0 (.n 240) = ofK (g ^ n) ∧
      x.bw.getD 2 [] = (List.range 24).map fun j => bitWord (n.testBit j)

/-- **`PhOpen`'s honest inputs, `open_stacked` ending at `x.ec 16`, and the end's facts** at `PhOpen`'s state `s2`. -/
def OpenEnd (al : String → Bool) (x : VsCtx) (Own : ℕ → Prop) (s2 : St) : Prop :=
  ∃ (b23 bm : ℕ) (xs23 xm : List E) (sl ic0 qt : ℕ) (a96 h1 h2 : E) (fsv : List E)
    (Ro Do : ℕ → Prop) (Oo Po : Reader → Prop) (Qo : Reader → Tree → Prop) (Bo eo : ℕ) (s0 c pp : ℕ)
    (wE : WhirEnd) (bp bp1 nx : ℕ) (layout : Layout) (link : LinkEnd) (chi r qPoint kOut kIn f g' xq z : List E)
    (rho lam rm : E) (outputs : List ColumnClaim) (keccakSlices : List E) (oodValue v0 v1 : E)
    (claims : List StackClaim) (carr : List (ℕ × ℕ)),
    PhOpenIn B2C.fs al B2C.cert 17 x.rd0 x.rd1 x.args x.cur x.p x.ret Own x.R x.Pre s2 b23 bm xs23 xm sl ic0 qt a96 h1
      h2 fsv Ro Do Oo Po Qo Bo eo s0 c pp wE bp bp1 nx layout link chi r qPoint kOut kIn f g' xq z rho lam rm outputs
      keccakSlices oodValue v0 v1 claims carr ∧ eo = x.ec 16 ∧
    EndOk x (fun rd => (s2.O rd ∧ Oo rd) ∧ True) Qo

/-! ## At the honest cursor

`OpenEnd` names `open_stacked`'s point buffers `bp`, `bp1` through `ret` (`PhOpenIn.ro`), and they lie in its frame
or heap past the cursor the ring's call leaves, so `Ph12End`'s continuations at every end of the earlier calls ask
`ret` to name a position that moves with them: `Ph12End` holds at one cursor chain only. The honest chain is pinned:
`Ph12` starts at `x.ec 12`, `link_terminal`, `verify_keccak`, `ring_switch_target` end at `x.ec 13`, `x.ec 14`,
`x.ec 15`. -/

/-- **`Ph35`'s honest inputs, the two calls at the ends `ev`, `er`, then `OpenEnd`** at `Ph35`'s state `s1`. -/
def KecEndP (al : String → Bool) (x : VsCtx) (Own : ℕ → Prop) (s1 : St) (ev er : ℕ) : Prop :=
  ∃ (qt b15 b20 b21 bm cs τ : ℕ) (nz : E) (xs21 xsm chis outs xs op point slices : List E) (kw : E) (s' : Fs),
    Ph35In B2C.fs al B2C.cert 17 x.rd0 x.rd1 x.args x.cur x.p x.ret Own x.R x.Pre s1 qt b15 b20 b21 bm cs τ nz xs21
      xsm chis outs xs op point slices kw s' ∧
    VkCall B2C.fs al B2C.cert 17 x.w b15 b20 b21 qt τ chis outs xs op point slices kw s'
      (allocBase (al "verify_keccak") s1.kc) ev ∧
    RtCall B2C.fs al B2C.cert 17 s1.a (rsW xs21 xsm (vsVal x.rd0 x.w x.args (.n 3026))) (mcW (vsVal x.rd0 x.w x.args))
      (allocBase (al "ring_switch_target") ev) er ∧
    OpenEnd al x Own ⟨s1.a + 144, er, fun rd => (s1.O rd ∧ True) ∧ True, fun i => (s1.D i ∨ False) ∨ False,
      s1.Qs ++ [PostQuiet, PostQuiet]⟩

/-- **`Ph1213`'s honest inputs, `link_terminal`'s call at the end `ec`, then `KecEndP`** at `Ph12`'s state `st`. -/
def Ph12EndP (al : String → Bool) (x : VsCtx) (Own : ℕ → Prop) (st : St) (ec ev er : ℕ) : Prop :=
  ∃ (b18 b1076 b11 b10 b17 b15 b19 b12 bnu wd : ℕ) (xs18 xs1076 xs11 xs10 xs17 xs19 : List E) (hg bb : ℕ → ℕ)
    (ts xs cs : ℕ → List E) (top : ℕ → E) (ch : Chunks) (rs sl shs nus : List E),
    Ph1213In B2C.fs al B2C.cert 17 x.rd0 x.rd1 x.args x.cur x.p x.ret Own x.R x.Pre st b18 b1076 b11 b10 b17 b15 b19
      b12 bnu wd xs18 xs1076 xs11 xs10 xs17 xs19 hg bb ts xs cs top ch rs sl shs nus ∧
    LtCall B2C.fs al B2C.cert 17 wd (vsVal x.rd0 x.w x.args) (x.w 1077) b12 b1076 b19 bnu rs sl shs nus
      (allocBase (al (ltNames.getD (wd - 19) "")) (tpKc B2C.fs al hg 5 st.kc)) ec ∧
    KecEndP al x Own ⟨st.a, ec, fun rd => st.O rd ∧ True, fun i => st.D i ∨ False,
      st.Qs ++ List.replicate 5 PostQuiet ++ [PostQuiet]⟩ ev er

/-- **`wC`'s phases 12 to the end at the honest cursor**: `Ph12toEndS` at the states whose callees' cursor is
`x.ec 12`. -/
def Ph12toEndP (al : String → Bool) : Prop :=
  ∀ x : VsCtx, x.al = al → x.Hon → VsCalleesCompleteA B2C.fs al B2C.cert 17 →
    ∀ Own : ℕ → Prop, (∀ i, x.OwnB i → Own i) → ∀ st : St,
    x.Bnd st → x.Carry11 st → st.kc = x.ec 12 →
    Ph1213Ok B2C.fs al B2C.cert 17 x.rd0 x.w x.args Own x.R x.Pre st fun s =>
    TailOk B2C.fs al B2C.cert 17 x.rd0 x.w x.args Own x.R x.Pre s x.kEndB

/-- **`Ph12toEndP` from the honest inputs at the pinned ends**, `check_stack_terminal`'s end within `2^24` of its
cursor. -/
theorem ph12toEndP_of {al : String → Bool}
    (hC : CheckStackTerminalCompleteAE B2C.fs al B2C.cert 17 fun c e => e ≤ c + 2 ^ 24)
    (h : ∀ x : VsCtx, x.al = al → x.Hon → VsCalleesCompleteA B2C.fs al B2C.cert 17 →
      ∀ Own : ℕ → Prop, (∀ i, x.OwnB i → Own i) → ∀ st : St, x.Bnd st → x.Carry11 st → st.kc = x.ec 12 →
      Ph12EndP al x Own st (x.ec 13) (x.ec 14) (x.ec 15)) :
    Ph12toEndP al := by
  intro x hal hx hc Own hO st hb h11 hk
  have ha : x.args.length = 6 := rfl
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, H1, hlt, H1k⟩ :=
    h x hal hx hc Own hO st hb h11 hk
  refine ph1213Ok_at ha hx.hret H1 hlt ?_
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, H2, hv, hrt, H2k⟩ := H1k
  refine ph35Ok_at ha hx.hret H2 hv hrt ?_
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, H3, heo, hf, hpt, hmk, layout, rate, hann, b0, b3, b8, b2⟩ := H2k
  refine phOpenOk_inE hC ha hx.hret H3 fun ec' _ hB => ?_
  have l8 : (x.bw.getD 8 []).length = 36 := by
    have e := VsCtx.Lw_length hx (j := 8) (by omega)
    simp only [VsCtx.Lw_getD hx (show 8 < 24 by omega), show (8 : ℕ) ≠ 13 by omega, ↓reduceIte] at e
    exact e
  refine VsCtx.phExportOk hx (by intro rd ho; exact hb.hO rd ho.1.1.1.1.1) hO hpt
    (by rw [List.take_of_length_le (by omega), b8]) ?_
  refine ⟨fun _ => ?_, VsCtx.kEndW_bw hx hb h11 hann hf (by intro rd ho; exact ho.1.1.1.1.1) hmk b0 b3 b8 b2⟩
  have h1 := LeanVM.Guest.Memory.allocBase_le (al "check_stack_terminal") (x.ec 16)
  have h2 := fs_lt16 "check_stack_terminal"
  have h3 := hx.hend
  rw [heo] at hB
  dsimp only
  omega

/-- **`Ph12toEndS` is `Ph12toEndP`**: `Carry11` pins the callees' cursor at `x.ec 12` (vspin). -/
theorem ph12toEndS_of_P {al : String → Bool} (h : Ph12toEndP al) : Ph12toEndS al :=
  fun x hal hx hc Own hO st hb h11 => h x hal hx hc Own hO st hb h11 h11.2.2.1

end
end LeanVM.Guest.B1.VsC
