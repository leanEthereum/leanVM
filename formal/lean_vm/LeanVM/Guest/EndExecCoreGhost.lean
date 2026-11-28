/-
  LeanVM.Guest.EndExecCoreGhost

  `CoreGhost` (`EndExecCoreA.lean`) from the families' soundness at the honest instances of b2c's
  aligned tree: the generic families (`EndExecCoreResA`), `anyLink`'s links (`EndExecCoreLinkA`), and
  each function's own facts and ghost families, as named hypotheses (`GhostOk`).
-/

module

public import LeanVM.Guest.EndExecCoreStA

/-!
# The families' part of an honest frame

The bus era's case split in `EndExecCore.coreHonAll_X` on `honestInstsA`: at the top frame of a
state of the tree track, for core data `Cf` of its function (`CfOk`), an honest valuation, by the
family of `Cf`'s links (`CoreMode.glOk`):

* a frame loop over its caller's table (`cmK`): its ghost words and links by its function's own
  soundness (`CmLoopOkA`);
* a cursor-run loop (`stK`): its ghost words its caller's run base, bound and frame, by its function's own
  soundness (`StLoopOkA`, `st_instA`);
* a ghost family specialization (`mlK`): by its function's own soundness (`MlLoopOkA`);
* no ghost: the residuals of the generic families (`resOk_instA`) and `anyLink`'s links
  (`glF_instA`);
* its own parameter words as ghosts (`gwSlots`): `resOk_instGA` at `setG`;
* a loop callee of `anyLink`: its caller's frame address its ghost word (`alGlF_instA`).

`GhostOk al D`: what each function's own soundness owes (the bus era's `FnReg.*_ok`, its
`Sound.lean`s): its exponent and dimension facts (`ExpOkA`, `DimOkA`), the ghost families' reads and links (`MlLoopOkA`,
`CmLoopOkA`), the cursor-run loops' cursors (`StLoopOkA`), its own residual families (`OwnOkA`), `anyLink`'s checks (`LinkOk`) and the loops' check
(`Res.ProgOk`). `coreGhost_of`.
-/

namespace LeanVM.Guest.EndExec

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Memory
open LeanVM.Guest.B2C (idxOf FrameHolds)
open LeanVM.Guest.Bridge (FnAl)
open LeanVM.Protocol.Verifier (gen)
open LeanVM.Prover.Exec

@[expose] public section

variable {al : String → Bool} {D : Ref → RefD}

/-- **An exponent fact holds** at every honest instance of its function, aligned. -/
def ExpOkA (al : String → Bool) (D : Ref → RefD) (c : String × ℕ × Option ℕ × ℕ) : Prop :=
  ∀ {r : Ref}, RefH (layB al) (D r) r → r.Ok → ∀ J ∈ instsR al D r, ∀ σ bufs kids,
    J.t = .node c.1 σ bufs kids → ∀ fn, coreProgram.find? c.1 = some fn → ∀ v, fn.params[c.2.1]? = some v →
      ExpH r.img.read c.2.2.1 c.2.2.2 (σ v)

/-- **A dimension fact holds** at every honest instance of its function, aligned. -/
def DimOkA (al : String → Bool) (D : Ref → RefD) (c : String × ℕ × ℕ × List (ℕ × ℕ)) : Prop :=
  ∀ {r : Ref}, RefH (layB al) (D r) r → r.Ok → ∀ J ∈ instsR al D r, ∀ σ bufs kids,
    J.t = .node c.1 σ bufs kids → ∀ fn, coreProgram.find? c.1 = some fn → ∀ vk vb, fn.params[c.2.1]? = some vk →
      fn.params[c.2.2.1]? = some vb → DimH r.img.read (σ vk) (σ vb) c.2.2.2

/-- **A ghost family specialization's reads and links** (`CoreMode.mlK`) at every honest instance whose
header cell `1` holds its caller's frame, aligned: ghost words at which its reads (`CoreMode.mlSub`) hold,
and its caller's cells linked as its entry says (`CoreMode.mlGl`) holding there. -/
def MlLoopOkA (al : String → Bool) (D : Ref → RefD) (c : String × ℕ × ℕ × ℕ × ℕ × ℕ × List (ℕ × ℕ × ℕ)) :
    Prop :=
  ∀ {r : Ref}, RefH (layB al) (D r) r → r.Ok → ∀ I ∈ instsR al D r, ∀ σ bufs kids,
    I.t = .node c.1 σ bufs kids → ∀ fn, coreProgram.find? c.1 = some fn → CoreMode.mlK fn = some c.2 →
      r.img.read (addressOfIndex (I.fp + 1)) = some I.hdr.2 → ∃ gw : List E,
        (∀ x, CoreMode.mlSub fn x = true → x.Holds (CoreMode.setG σ gw)) ∧
        ∀ Cf : CoreMode.CFun, Cf.fn = fn → Cf.gl = c.2.2.2.2.2.2 → Cf.H.sig.ghosts = 1 →
          CoreMode.GlF r.img Cf.gl I.fp
            (Cf.fn.params.map (CoreMode.setG σ gw) ++ CoreMode.ownG Cf.H.sig (CoreMode.setG σ gw))

/-- **A frame loop's reads and links** (`CoreMode.cmK`) at every honest instance whose header cell `1`
holds its caller's frame, aligned: ghost words at which its reads (`CoreMode.cmSub`) hold, and its
caller's cells linked as its entry says (`CoreMode.cmGl`) holding there. -/
def CmLoopOkA (al : String → Bool) (D : Ref → RefD) (c : String × ℕ × ℕ × ℕ × ℕ × List ℕ) : Prop :=
  ∀ {r : Ref}, RefH (layB al) (D r) r → r.Ok → ∀ I ∈ instsR al D r, ∀ σ bufs kids,
    I.t = .node c.1 σ bufs kids → ∀ fn, coreProgram.find? c.1 = some fn → CoreMode.cmK fn = some c.2 →
      r.img.read (addressOfIndex (I.fp + 1)) = some I.hdr.2 → ∃ gw : List E,
        (∀ x, CoreMode.cmSub fn x = true → x.Holds (CoreMode.setG σ gw)) ∧
        ∀ Cf : CoreMode.CFun, Cf.fn = fn → Cf.gl = CoreMode.loopGl Cf.fn.params.length c.2.2.2.2.2 →
          Cf.H.sig.ghosts = 3 → CoreMode.GlF r.img Cf.gl I.fp
            (Cf.fn.params.map (CoreMode.setG σ gw) ++ CoreMode.ownG Cf.H.sig (CoreMode.setG σ gw))

/-- **What each function's own soundness owes the core route**, aligned: its exponent and dimension facts, the ghost
families' reads and links, its own families, `anyLink`'s checks and the loops' check. -/
structure GhostOk (al : String → Bool) (D : Ref → RefD) : Prop where
  exp : ∀ c ∈ CoreMode.FnReg.expFacts, ExpOkA al D c
  dim : ∀ c ∈ CoreMode.FnReg.dimFacts, DimOkA al D c
  ml : ∀ c ∈ CoreMode.FnReg.mlLoops, MlLoopOkA al D c
  cm : ∀ c ∈ CoreMode.FnReg.cmLoops, CmLoopOkA al D c
  st : ∀ c ∈ CoreMode.FnReg.stLoops, StLoopOkA al D c
  own : ∀ c ∈ CoreMode.FnReg.fams, OwnOkA al D c
  link : LinkOk Res.anyLink
  prog : Res.ProgOk coreProgram

end

public section

variable {al : String → Bool} {D : Ref → RefD} {A : String → FnAl} {R : Ref → Prop}

/-- **The listed exponent facts at every honest instance.** -/
theorem expQ_allA (hG : GhostOk al D) {r : Ref} (hR : RefH (layB al) (D r) r) (hr : r.Ok) :
    ∀ J ∈ instsR al D r, ExpQ r J := by
  intro J hJ f σ bufs kids hJt fn hf c hc hcf v hv
  subst hcf
  exact hG.exp c hc hR hr J hJ σ bufs kids hJt fn hf v hv

/-- **The listed dimension facts at every honest instance.** -/
theorem dimQ_allA (hG : GhostOk al D) {r : Ref} (hR : RefH (layB al) (D r) r) (hr : r.Ok) :
    ∀ J ∈ instsR al D r, DimQ r J := by
  intro J hJ f σ bufs kids hJt fn hf c hc hcf vk vb hk hb
  subst hcf
  exact hG.dim c hc hR hr J hJ σ bufs kids hJt fn hf vk vb hk hb

/-- **A frame loop is not of the ghost family `ml`.** -/
theorem cmK_mlK {fn : Fn} {p : ℕ × ℕ × ℕ × ℕ × List ℕ} (hk : CoreMode.cmK fn = some p) : CoreMode.mlK fn = none := by
  have hm : ∀ n ∈ CoreMode.FnReg.cmLoops.map (·.1), CoreMode.FnReg.mlLoops.lookup n = none := by decide +kernel
  exact hm _ (List.mem_map_of_mem (f := (·.1)) (CoreMode.lookup_memL hk))

/-- **The families' part of the honest frames** (`CoreGhost`), from each function's own soundness
(`GhostOk`). -/
theorem coreGhost_of {T : List CoreMode.CFun} (hG : GhostOk al D) (hRH : ∀ r, R r → RefH (layB al) (D r) r) :
    CoreGhost (layB al) D A R T := by
  intro r hR0 hr Cf _ hCf pc fp done e st htr j hj _ hc0 hB
  have hR := hRH r hR0
  obtain ⟨rd, hHa, -, hcov⟩ := hR.coversR
  obtain ⟨hI, j', bufs, kids, vs, hj', hIt, hfn, -, hF⟩ :=
    Bridge.RefOk.framesA hR.name hHa hcov htr e List.mem_cons_self
  obtain rfl : j = j' := Option.some.inj (hj.symm.trans hj')
  have hE := htr.track.ents e List.mem_cons_self
  have hfind : coreProgram.find? e.I.t.name = some Cf.fn := by rw [← hc0, hfn]; exact hE.find
  obtain ⟨j0, -, -, -, -, hb0⟩ := hCf
  rw [Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true] at hb0
  obtain ⟨⟨⟨hb0, hres0⟩, hgl0⟩, -⟩ := hb0
  simp only [CoreMode.honB, Bool.and_eq_true, List.all_eq_true] at hb0
  obtain ⟨⟨⟨⟨⟨⟨⟨-, -⟩, -⟩, hpar⟩, -⟩, -⟩, -⟩, -⟩ := hb0
  have hpN : Cf.fn.params = (List.range Cf.fn.params.length).map V.n := by
    rw [List.range_eq_range']; exact CoreMode.paramsN_eq _ 0 hpar
  have hparF := hB.par
  have hExp := expQ_allA hG hR hr e.I hI
  have hDim := dimQ_allA hG hR hr e.I hI
  have hnm : Cf.fn.name = e.I.t.name := find_name' hfind
  cases hck : CoreMode.cmK Cf.fn with
  | some m =>
    -- a frame loop of the gap walk: its ghost words its caller's entries, bound and frame
    have hgl1 := hgl0
    simp only [CoreMode.glOk, hck, Option.isSome_some, Bool.cond_true, CoreMode.cmGl, Option.any_some,
      Bool.and_eq_true, decide_eq_true_eq, Nat.beq_eq] at hgl1
    obtain ⟨⟨⟨hglv, hgh⟩, hng⟩, hgw0⟩ := hgl1
    obtain ⟨gw, hsub, hglF⟩ := hG.cm _ (CoreMode.lookup_memL hck) hR hr _ hI e.σ bufs kids
      (by rw [hnm]; exact hIt) _ (by rw [hnm]; exact hfind) hck hF.hdr1
    refine ⟨CoreMode.setG e.σ gw, CoreMode.honB_setG hB hng, fun hxw ↦ ?_, hglF Cf rfl hglv hgh,
      fun c j hc ↦ by rw [List.isEmpty_iff.mp hgw0] at hc; cases hc⟩
    exact resOk_instGA hG.own hR hr hI hExp hDim hIt hfind hres0 hparF hxw
      (fun m hm ↦ CoreMode.setG_eq (show (V.n m).idx < CoreMode.GB from hm))
      (fun x hx ↦ by cases x <;> simp [CoreMode.mlSub, cmK_mlK hck] at hx)
      (fun x hx ↦ by cases x <;> simp [CoreMode.stSub, cmK_stK hck] at hx) hsub
      (fun c j hc ↦ by rw [List.isEmpty_iff.mp hgw0] at hc; cases hc)
  | none =>
  cases hsk : CoreMode.stK Cf.fn with
  | some p =>
    -- a cursor-run loop: its ghost words its caller's run base and bound, and frame
    obtain ⟨Db, Dn, W, v, S⟩ := p
    have hgl1 := hgl0
    simp only [CoreMode.glOk, hck, hsk, Option.isSome_none, Bool.cond_false, Option.isSome_some, Bool.cond_true,
      CoreMode.stGl, Option.any_some, Bool.and_eq_true, decide_eq_true_eq, Nat.beq_eq] at hgl1
    obtain ⟨⟨⟨hglv, hgh⟩, hng⟩, hgw0⟩ := hgl1
    have hmk := stK_mlK hsk
    obtain ⟨hDb, hDn, a, ha, haDb, haDn, hsub⟩ := st_instA hG.st hR hr hI hIt hfind hsk
    refine ⟨CoreMode.setG e.σ [refMem r.img (a + Db), refMem r.img (a + Dn), ofK (Parameters.g ^ a)],
      CoreMode.honB_setG hB hng, fun hxw ↦ ?_, stGlF hglv hgh hDb hDn (rd_hdr hF.hdr1 ha) haDb haDn,
      fun c j hc ↦ by rw [List.isEmpty_iff.mp hgw0] at hc; cases hc⟩
    exact resOk_instGA hG.own hR hr hI hExp hDim hIt hfind hres0 hparF hxw
      (fun m hm ↦ CoreMode.setG_eq (show (V.n m).idx < CoreMode.GB from hm))
      (fun x hx ↦ by cases x <;> simp [CoreMode.mlSub, hmk] at hx) hsub
      (fun x hx ↦ by rw [CoreMode.cmSub_none hck] at hx; cases hx)
      (fun c j hc ↦ by rw [List.isEmpty_iff.mp hgw0] at hc; cases hc)
  | none =>
  cases hmk : CoreMode.mlK Cf.fn with
  | some k =>
    -- the ghost family: its ghost word the caller's entries table
    have hgl1 := hgl0
    simp only [CoreMode.glOk, hck, hsk, hmk, Option.isSome_none, Option.isSome_some, Bool.cond_false,
      Bool.cond_true, CoreMode.mlGl, Option.any_some, Bool.and_eq_true, decide_eq_true_eq, Nat.beq_eq] at hgl1
    obtain ⟨⟨⟨hglv, hgh⟩, hng⟩, hgw0⟩ := hgl1
    obtain ⟨gw, hsub, hglF⟩ := hG.ml _ (CoreMode.lookup_memL hmk) hR hr _ hI e.σ bufs kids
      (by rw [hnm]; exact hIt) _ (by rw [hnm]; exact hfind) hmk hF.hdr1
    refine ⟨CoreMode.setG e.σ gw, CoreMode.honB_setG hB hng, fun hxw ↦ ?_, hglF Cf rfl hglv hgh,
      fun c j hc ↦ by rw [List.isEmpty_iff.mp hgw0] at hc; cases hc⟩
    exact resOk_instGA hG.own hR hr hI hExp hDim hIt hfind hres0 hparF hxw
      (fun m hm ↦ CoreMode.setG_eq (show (V.n m).idx < CoreMode.GB from hm)) hsub
      (fun x hx ↦ by cases x <;> simp [CoreMode.stSub, hsk] at hx)
      (fun x hx ↦ by rw [CoreMode.cmSub_none hck] at hx; cases hx)
      (fun c j hc ↦ by rw [List.isEmpty_iff.mp hgw0] at hc; cases hc)
  | none =>
    have hgl1 := hgl0
    simp only [CoreMode.glOk, hck, hsk, hmk, Option.isSome_none, Bool.cond_false] at hgl1
    rcases Bool.or_eq_true_iff.mp hgl1 with hgl1 | hal
    · rcases Bool.or_eq_true_iff.mp hgl1 with hgl1 | hgl1
      · -- no ghost: its residuals and linked cells at its valuation
        rw [Bool.and_eq_true, Bool.and_eq_true] at hgl1
        obtain ⟨⟨hgl1, -⟩, hgw0⟩ := hgl1
        refine ⟨e.σ, hB, fun hxw ↦ resOk_instA hG.own hR hr hI hExp hDim hIt hfind hres0 hgw0 hmk hsk hck hparF hxw,
          glF_instA hR hr hG.prog hI hIt hfind hpN hG.link hgl1 hF.hdr1 _, fun c j hc ↦ ?_⟩
        rw [List.isEmpty_iff.mp hgw0] at hc; cases hc
      · -- its ghost words its own parameter words
        rw [Bool.and_eq_true] at hgl1
        obtain ⟨hgle, hgs⟩ := hgl1
        have hng : CoreMode.ngB Cf.fn = true := by
          simp only [CoreMode.gwSlots, Bool.and_eq_true] at hgs; exact hgs.2
        refine ⟨CoreMode.setG e.σ (Cf.H.sig.gw.map fun x ↦ (r.img.read (x.1.addrW (CoreMode.vw e.σ))).getD 0),
          CoreMode.honB_setG hB hng, fun hxw ↦ ?_, fun d b k h ↦ ?_, CoreMode.gwR_setG hgs⟩
        · exact resOk_instGA hG.own hR hr hI hExp hDim hIt hfind hres0 hparF hxw
            (fun m hm ↦ CoreMode.setG_eq (show (V.n m).idx < CoreMode.GB from hm))
            (fun x hx ↦ by cases x <;> simp [CoreMode.mlSub, hmk] at hx)
            (fun x hx ↦ by cases x <;> simp [CoreMode.stSub, hsk] at hx)
            (fun x hx ↦ by rw [CoreMode.cmSub_none hck] at hx; cases hx) (CoreMode.gwR_setG hgs)
        · rw [List.isEmpty_iff.mp hgle] at h; cases h
    · -- a loop callee of `anyLink`: its ghost word its caller's frame address
      simp only [CoreMode.alGl, Bool.and_eq_true, Nat.beq_eq] at hal
      obtain ⟨⟨⟨hany, hgh⟩, hng⟩, hgw0⟩ := hal
      have hnp : Cf.fn.params.length < CoreMode.GB := by
        have := hng
        simp only [CoreMode.ngB, Bool.and_eq_true, Nat.blt_eq] at this
        exact this.1.1
      obtain ⟨a, hglF⟩ := alGlF_instA hR hr hG.prog hI hIt hfind hpN hG.link hany hF.hdr1 hgh hnp
      refine ⟨CoreMode.setG e.σ [ofK (Parameters.g ^ a)], CoreMode.honB_setG hB hng, fun hxw ↦ ?_, hglF,
        fun c j hc ↦ by rw [List.isEmpty_iff.mp hgw0] at hc; cases hc⟩
      exact resOk_instGA hG.own hR hr hI hExp hDim hIt hfind hres0 hparF hxw
        (fun m hm ↦ CoreMode.setG_eq (show (V.n m).idx < CoreMode.GB from hm))
        (fun x hx ↦ by cases x <;> simp [CoreMode.mlSub, hmk] at hx)
        (fun x hx ↦ by cases x <;> simp [CoreMode.stSub, hsk] at hx)
        (fun x hx ↦ by rw [CoreMode.cmSub_none hck] at hx; cases hx)
        (fun c j hc ↦ by rw [List.isEmpty_iff.mp hgw0] at hc; cases hc)

/-- **`CoreHonAll` on the aligned honest tree** from each function's own soundness (`GhostOk`):
`coreHonAll_A` at `coreGhost_of`. -/
theorem coreHonAll_ghost {Ks Ks0 : List Mode.Cert} {Km : Mode.Cert} {E0 : Mode.Env} {Y : Ref → St → Prop}
    {T : List CoreMode.CFun} (certs : ModeCerts Ks0 Km E0) (hsub : ∀ K ∈ Ks, K ∈ Ks0)
    (hKs : ∀ K ∈ Ks0, K.F.entry ≠ 0) (hH : HintHyps (layB al) D A) (hRH : ∀ r, R r → RefH (layB al) (D r) r)
    (hEI : EntIdx A) (hAX : ∀ f j, idxOf f = some j → (A f).X = Bridge.ctxOf j) (hT : ∀ Cf ∈ T, CoreMode.CfOk Cf)
    (hG : GhostOk al D) : CoreHonAll R T Ks (XOf Y) :=
  coreHonAll_A certs hsub hKs hH hRH hEI hAX hT (coreGhost_of hG hRH)

end

end LeanVM.Guest.EndExec
