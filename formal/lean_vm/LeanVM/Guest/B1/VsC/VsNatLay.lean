/-
  LeanVM.Guest.B1.VsC.VsNatLay

  The honest context's layout is the native run's, and `open_stacked`'s native call with its end bounds.
-/

module

public import LeanVM.Guest.B1.VsC.VsNatHos
public import LeanVM.Guest.B1.VsC.OpenStackedEndA

/-!
# The layout and `open_stacked`'s bounds, natively

* **`VsCtx.lay_nat`**: `x.lay = N.layout` at any `N.Ok x.seed x.c` (both are the announced layout), so
  **`VsCtx.nF_nat`** (`x.nF = natF3 x.seed x.c N.layout.stackLog`) and **`VsCtx.rm_natOpen`**
  (`N.rm x.seed x.c = (N.L.F4 x.lay x.nF).squeeze.1`); `VsCtx.hgS_nat`, `wdS_nat`, `nS_nat`; `NatOpen.Ok.sl16`,
  `sl30` (`D3.Ok.h16`, `h30`, `hsl`).
* **`openCallEnd_of`**: `openCall_of` from `OpenStackedEndA`, keeping its bounds: both point buffers end at most at
  the call's end, the end within `2^36` of the callee's cursor.
* **`VsCtx.openCallEnd_nat`**: `openCall_nat`'s call with those bounds, so one instance gives `D3.Ok.hos`'s call
  (`hos_honest`), `hbp`, `hbp1` and `EcSteps.s16` at `β = 36`.
-/

namespace LeanVM.Guest.B1.VsC

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Memory LeanVM.Guest.B1 LeanVM.Guest.B1.Whir
open LeanVM.Guest.Complete LeanVM.Guest.B1.Fwd LeanVM.Node LeanVM.Protocol LeanVM.Protocol.Verifier
open LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Link LeanVM.Guest.B1.Stack
open LeanVM.Prover.Exec (allocBase)

@[expose] public section

/-! ## The layout -/

section
variable {x : VsCtx} {N : NatOpen}

/-- **The honest context's layout is the native run's.** -/
theorem VsCtx.lay_nat (hN : N.Ok x.seed x.c) : x.lay = N.layout := VsCtx.lay_of hN.hann

/-- The link's start sponge at the native layout. -/
theorem VsCtx.nF_nat (hN : N.Ok x.seed x.c) : x.nF = natF3 x.seed x.c N.layout.stackLog := by
  rw [VsCtx.nF, x.lay_nat hN]

/-- **The public input's challenge at the context's layout.** -/
theorem VsCtx.rm_natOpen (hN : N.Ok x.seed x.c) : N.rm x.seed x.c = (N.L.F4 x.lay x.nF).squeeze.1 := by
  rw [NatOpen.rm, x.nF_nat hN, x.lay_nat hN]

theorem VsCtx.hgS_nat (hN : N.Ok x.seed x.c) (t : ℕ) : x.hgS t = N.layout.tableLogHeights.getD t 0 := by
  rw [VsCtx.hgS, x.lay_nat hN]

theorem VsCtx.wdS_nat (hN : N.Ok x.seed x.c) : x.wdS = widthOf N.layout := by
  rw [VsCtx.wdS, x.lay_nat hN]

theorem VsCtx.nS_nat (hN : N.Ok x.seed x.c) : x.nS = hMax N.layout := by
  rw [VsCtx.nS, x.lay_nat hN]

end

/-- The native stack's log size, at least `16`. -/
theorem NatOpen.Ok.sl16 {N : NatOpen} {seed : Digest} {c : Child} (hN : N.Ok seed c) : 16 ≤ N.layout.stackLog :=
  hN.shape.stack_ge

/-- The native stack's log size, at most `30`. -/
theorem NatOpen.Ok.sl30 {N : NatOpen} {seed : Digest} {c : Child} (hN : N.Ok seed c) : N.layout.stackLog ≤ 30 :=
  hN.shape.stack_le

/-! ## `open_stacked`'s call with its bounds -/

section
variable {fs : String → ℕ} {al : String → Bool} {cert : String → V → ℕ} {k : ℕ}

/-- **`open_stacked`'s call from its bounded completeness**: `openCall_of`'s call, its point buffers ending at most
at its end `e`, and `e` within `2^36` of the callee's cursor. -/
theorem openCallEnd_of (hO : ∀ m, m ≤ 14 → OpenStackedEndA fs al cert k m) {sl r : ℕ} (h16 : 16 ≤ sl)
    (h30 : sl ≤ 30) {root : Digest} {fsv : List E} {target : E} {ic it : ℕ} {xs : List E}
    {os : List (List Opening)} {wE : WhirEnd} {s' : Fs} {roots' : List (Digest × ℕ × ℕ)} {qs : List (ℕ × List ℕ)}
    {Rg : ℕ → Prop} (hr1 : 1 ≤ r) (hr4 : r ≤ 4) (hf : fsv.length = 5) (hsp : ∃ sp : Sponge, (⟨fsv, []⟩ : Fs).Carries sp)
    (hrun : RunsWith (whirOpen sl r target) ⟨fsv, []⟩ xs os [(root, stackShape sl r)] wE s' roots')
    (hq : OpenRunQueries sl r root target ⟨fsv, []⟩ xs os qs)
    (hxs : ∀ i < xs.length, Rg (ic + i)) (hit : ∀ n < 2 ^ winTabBits, Rg (it + n)) (kc : ℕ) :
    ∃ bp bp1 e : ℕ, CallAtA fs al cert k (Whir.openName sl)
      (rateSel r :: fsv ++ [target, (digestHalves root).1, (digestHalves root).2, ptrAt ic, ptrAt it])
      (osRets wE bp bp1 (ic + xs.length)) Rg
      (fun i => (bp ≤ i ∧ i < bp + pointCap) ∨ (bp1 ≤ i ∧ i < bp1 + pointCap))
      (fun rd => ReadsAt rd (ptrAt bp) (wE.point ++ List.replicate (pointCap - sl) 0) ∧
        ReadsAt rd (ptrAt bp1) (wE.point.map (1 + ·) ++ List.replicate (pointCap - sl) 1))
      (fun rd => ReadsAt rd (ptrAt ic) xs ∧ WinTabs rd (ptrAt it))
      (fun rd t => SameStreams (t.pops coreProgram rd) (Prover.merkleHints true qs os) ∧
        t.Every (ExactAt coreProgram rd))
      (fs (Whir.openName sl)) (allocBase (al (Whir.openName sl)) kc)
      (allocBase (al (Whir.openName sl)) kc + fs (Whir.openName sl)) e ∧
      bp + pointCap ≤ e ∧ bp1 + pointCap ≤ e ∧
      e ≤ allocBase (al (Whir.openName sl)) kc + fs (Whir.openName sl) + 2 ^ 36 := by
  have hsl : minOpenLog + (sl - 16) = sl := by show 16 + (sl - 16) = sl; omega
  have h := hO (sl - 16) (by omega) r root fsv target ic it xs os wE s' roots' qs Rg hr1 hr4 hf hsp
    (by rw [hsl]; exact hrun) (by rw [hsl]; exact hq) hxs hit (allocBase (al (Whir.openName sl)) kc)
    (allocBase (al (Whir.openName sl)) kc + fs (Whir.openName sl)) (le_of_eq (by rw [hsl]))
  rw [hsl] at h
  exact h

end

section
variable {x : VsCtx}

/-- **`open_stacked`'s call, natively, with its bounds**: `openCall_nat`'s call from `OpenStackedEndA`, its point
buffers `bp`, `bp1` ending at most at its end `e` (`D3.Ok.hbp`, `hbp1` at `x.ec 16 := e`), `e` within `2^36` of the
callee's cursor (`EcSteps.s16` at `β = 36`, `kc = x.ec 15`). -/
theorem VsCtx.openCallEnd_nat (hO : ∀ m, m ≤ 14 → OpenStackedEndA B2C.fs x.al B2C.cert 17 m)
    {N : NatOpen} (hN : N.Ok x.seed x.c) {bm nx : ℕ} (hbm : x.base 18 ≤ bm)
    (hin : bm + 144 + nx + 1 + N.ws.length ≤ x.base 18 + 256 * x.p) (kc : ℕ) :
    ∃ bp bp1 e : ℕ, CallAtA B2C.fs x.al B2C.cert 17 (openName N.layout.stackLog)
      (rateSel N.r :: ringCap N.S ++ [N.target x.seed x.c, x.c.proof.stream.getD 8 0, x.c.proof.stream.getD 9 0,
        ptrAt (bm + 144 + nx + 1), ptrAt (x.qt + 178)])
      (osRets N.wE bp bp1 (bm + 144 + nx + 1 + N.ws.length)) (fun i => x.R i ∨ x.OwnB i)
      (fun i => (bp ≤ i ∧ i < bp + pointCap) ∨ (bp1 ≤ i ∧ i < bp1 + pointCap))
      (fun rd => ReadsAt rd (ptrAt bp) (N.wE.point ++ List.replicate (pointCap - N.layout.stackLog) 0) ∧
        ReadsAt rd (ptrAt bp1) (N.wE.point.map (1 + ·) ++ List.replicate (pointCap - N.layout.stackLog) 1))
      (fun rd => ReadsAt rd (ptrAt (bm + 144 + nx + 1)) N.ws ∧ WinTabs rd (ptrAt (x.qt + 178)))
      (fun rd t => SameStreams (t.pops coreProgram rd)
          (Prover.merkleHints true (Prover.childQueries guestBytecode x.seed x.c) x.c.proof.openings) ∧
        t.Every (ExactAt coreProgram rd))
      (B2C.fs (openName N.layout.stackLog)) (allocBase (x.al (openName N.layout.stackLog)) kc)
      (allocBase (x.al (openName N.layout.stackLog)) kc + B2C.fs (openName N.layout.stackLog)) e ∧
      bp + pointCap ≤ e ∧ bp1 + pointCap ≤ e ∧
      e ≤ allocBase (x.al (openName N.layout.stackLog)) kc + B2C.fs (openName N.layout.stackLog) + 2 ^ 36 := by
  have B18 := (bases_of (x := x)).b18
  have hsum := vsAllocSz_sum x.p
  have hxs : ∀ i < N.ws.length, x.R (bm + 144 + nx + 1 + i) ∨ x.OwnB (bm + 144 + nx + 1 + i) :=
    fun i hi => Or.inr (show x.cur ≤ _ ∧ _ < x.cur + (vsAllocSz x.p).sum from ⟨by omega, by omega⟩)
  have hit : ∀ n < 2 ^ winTabBits, x.R (x.qt + 178 + n) ∨ x.OwnB (x.qt + 178 + n) := fun n hn => by
    have h2 : 2 ^ winTabBits = 2048 := rfl
    exact Or.inl (show (x.qt ≤ x.qt + 178 + n ∧ x.qt + 178 + n < x.qt + expTabLen) ∨ _ from
      Or.inl ⟨by omega, by rw [expTabLen_eq]; omega⟩)
  have hh := digestScalars_digestOfScalars (x.c.proof.stream.getD 8 0, x.c.proof.stream.getD 9 0)
  have e8 : x.c.proof.stream.getD 8 0 = (digestHalves (natRoot x.c)).1 := by rw [natRoot, hh]
  have e9 : x.c.proof.stream.getD 9 0 = (digestHalves (natRoot x.c)).2 := by rw [natRoot, hh]
  rw [e8, e9]
  have hsp : ∃ sp : Sponge, (⟨ringCap N.S, []⟩ : Fs).Carries sp :=
    carries_capOf (Link.pkPerm (capOf (Link.pkPerm (capOf N.S))))
  exact openCallEnd_of hO hN.shape.stack_ge hN.shape.stack_le hN.shape.rate_ge hN.shape.rate_le (ringCap_length _)
    hsp hN.hos hN.hq hxs hit kc

end

end
end LeanVM.Guest.B1.VsC
