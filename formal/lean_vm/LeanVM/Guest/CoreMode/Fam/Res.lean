/-
  LeanVM.Guest.CoreMode.Fam.Res

  `ExecGaps.res` reduced to the residuals at the honest frames: at each state of the tree track, its
  top frame an honest instance of the certificate's function at the state's offset, whose frame holds
  what the completeness check reads.
-/

module

public import LeanVM.Guest.EndExecX
public import LeanVM.Guest.Mode.ResFam
public import LeanVM.Guest.B2C.CplSpec
public import LeanVM.Guest.Bridge.FrameMap

/-!
# The residuals at the honest frames

`TopAt A r K i e j`: the frame `e` is the top frame of a state of the tree track along `r`'s run at
offset `i` of certificate `K`'s code: an honest instance of `K`'s function (index `j`), on its path,
its frame holding what the completeness check reads (`FrameHolds`) and within `2^62`, the
instruction at `i`, an `XOR` or a `MUL`, holding on the reference at its frame (`ROp`), and the
path's rest from the frame's position.

`ResTop Ks A`: each residual at such a frame holds of the reference there. `res_of_top`: `ResTop`
gives `ExecGaps.res` for `X = XOf Y`, as `termRef_of` gives `term`: `trackAt_X` puts a state of the
tracks at a track state of its own pc and frame, whose top frame `RefOk.frames` makes an honest
instance; the functions lying one after another (`consecutive_entry`), it is `K`'s function; and the
reference's step gives the instruction (`ref_xor`, `ref_mul`).
-/

namespace LeanVM.Guest.EndExec

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Mode LeanVM.Guest.Core LeanVM.Guest.Memory
open LeanVM.Guest.B2C (idxOf entryOf FrameHolds plumbOf fsN fn_of_idx)
open LeanVM.Guest.Bridge (FnAl ProgAl AtPc Ent entOf alOf alignAt alignAt_step)
open LeanVM.Prover.Exec

@[expose] public section

/-- **An honest frame at an offset of a certificate**: the top frame `e` of a state of the tree track
along `r`'s run at offset `i` of `K`'s code, a `node` instance of `K`'s function (index `j`) on its
path, its frame holding what the completeness check reads and within `2^62`, and the instruction at
`i` holding on the reference at its frame. -/
structure TopAt (A : String → FnAl) (r : Ref) (K : Mode.Cert) (i : ℕ) (e : Ent) (j : ℕ) : Prop where
  inst : e.I ∈ honestInsts coreProgram B2C.fs B2C.H r.hdr r.T
  node : ∃ f bufs kids, e.I.t = .node f e.σ bufs kids
  idx : idxOf e.I.t.name = some j
  entry : entryOf e.I.t.name = K.F.entry
  fn : coreOf j = e.fn
  path : ∃ vs, walk e.σ e.fn.body = .ret (e.pre ++ e.es) vs ∧
    FrameHolds r.img j e.I.fp e.σ (e.pre ++ e.es) vs e.I.kidFps e.I.hdr
  fb : e.I.fp + fsN j ≤ 2 ^ 62
  at' : AtPc (entOf A) (alOf A) e (K.F.entry + i)
  op : ∀ ins, K.code[i]? = some ins → ROp (refMem r.img) e.I.fp ins
  /-- The path from the frame's position. -/
  rest : ∃ vs, walk e.σ e.pos = .ret e.es vs

/-- **The residuals at the honest frames**: at each honest frame at an offset of a certificate, each
residual there whose bases have words holds of the reference at the frame. -/
def ResTop (Ks : List Mode.Cert) (A : String → FnAl) : Prop :=
  ∀ r : Ref, r.Ok → ∀ K ∈ Ks, ∀ i < K.code.length, ∀ e j, TopAt A r K i e j →
    ∀ x ∈ (K.F.res.get i).getD [], RIn (refMem r.img) e.I.fp x → RRes (refMem r.img) e.I.fp x

/-- **`ExecGaps.res` from the honest frames**, for the tracks' invariant `XOf Y`. -/
theorem res_of_top {Ks : List Mode.Cert} {Km : Mode.Cert} {E0 : Mode.Env} {A : String → FnAl}
    {Y : Ref → St → Prop} (certs : ModeCerts Ks Km E0) (hKs : ∀ K ∈ Ks, K.F.entry ≠ 0)
    (hP : ProgAl guestProgram coreProgram A) (hmain : entOf A "main" = End.mainEntry) (hJ : JumpCellsAt A)
    (hL : AlLayout A) (h : ResTop Ks A) : ∀ r, r.Ok → ResRef guestProgram r.img r.n Ks (XOf Y r) := by
  intro r hr K hK s i hX hs hon hi hpc x hx hin
  have hon' : OnRun (XOf Y) r s := ⟨hX, hs, hon⟩
  obtain ⟨f, hf, hcode, hentry, -⟩ := certs.fn K hK
  have hif : i < f.instructionCount := by
    rw [← CompiledFunction.length_code (CompiledFunction.wellChunked_of_mem hf), ← hcode]; exact hi
  have hge : proLen ≤ s.steps := by
    rcases hX.1 with ⟨hlt, hpcs, -⟩ | ⟨hge, -⟩
    · have := consecutive_entry functions_consecutive _ f0_mem f hf (by rw [f0_entry']; omega)
        (by rw [f0_entry']; show f.entryPc < 0 + proLen; omega)
      rw [f0_entry'] at this
      exact absurd (hentry.trans this) (hKs K hK)
    · exact hge
  have hpcf := guest_pc_lt hf hif
  obtain ⟨done, e0, st, htr⟩ := trackAt_X hP hmain hJ hL hr hon' hge (by omega)
  obtain ⟨e, st', hst, hE, hfp, hat⟩ := htr.top
  obtain ⟨rd, hH, hXh⟩ := hr.honest
  obtain ⟨hI, j, -, -, vs, hj, -, hfn, hw, hF⟩ :=
    htr.frames hr.name hH hXh.covers e (by rw [hst]; exact List.mem_cons_self)
  -- the frame's function is `K`'s
  have hent : entryOf e.I.t.name = K.F.entry := by
    obtain ⟨off, hpcoff, p, hal, -⟩ := hat
    obtain ⟨cf, hcf, hcent, hcentry, hlen⟩ := hL _ _ hE.find
    obtain ⟨ins, -, -, -, -, hins, -⟩ :=
      alignAt_step (hP.ok _ _ hE.find) (show alignAt _ _ _ _ off = some p from hal)
    have hoff : off < cf.instructionCount := lt_of_lt_of_le (List.getElem?_eq_some_iff.mp hins).1 hlen
    rw [hcent] at hpcoff
    have heq : cf.entryPc = f.entryPc := by
      rcases le_total cf.entryPc f.entryPc with h1 | h1
      · exact (consecutive_entry functions_consecutive cf hcf f hf h1 (by omega)).symm
      · exact consecutive_entry functions_consecutive f hf cf hcf h1 (by omega)
    rw [hcentry, heq, hentry]
  -- the frame's bound
  have hfb : e.I.fp + fsN j ≤ 2 ^ 62 := by
    obtain ⟨_, -, -, -, -, -, hfs, -⟩ := fn_of_idx hj
    have h2 := hH.cells.two_le e.I hI
    have hwi := honest_within hI (by omega)
    have hle := le_two_pow_logMem (r.T.total B2C.fs)
    have h28 : 2 ^ logMem (r.T.total B2C.fs) ≤ 2 ^ 28 :=
      Nat.pow_le_pow_right (by norm_num) (logMemorySize_le_28 (e := r.exec) hr.size)
    rw [hfs] at hwi
    have : (2 : ℕ) ^ 28 ≤ 2 ^ 62 := Nat.pow_le_pow_right (by norm_num) (by norm_num)
    omega
  -- the instruction at `i` on the reference
  obtain ⟨C, hC⟩ := ctx_of_complete (adv := r.adv) guest_decodable
  have hop := ((progOk_of certs hC).ok K hK).ops i hi
  rw [← hpc] at hop
  have hκ := logMemorySize_le_28 (e := r.exec) hr.size
  have hrop : ∀ ins, K.code[i]? = some ins → ROp (refMem r.img) e.I.fp ins := fun ins hins ↦ by
    rw [List.getElem?_eq_getElem hi, Option.some.injEq] at hins
    rw [hins] at hop
    rw [hfp]
    cases ins with
    | xor a b c => exact ref_xor hκ hC hs hon hop
    | mul a b c => exact ref_mul hκ hC hs hon hop
    | _ => trivial
  have ht : TopAt A r K i e j :=
    ⟨hI, hE.node, hj, hent, hfn, ⟨vs, hw, hF⟩, hfb, hpc ▸ hat, hrop, hE.path.elim fun vs' h ↦ ⟨vs', h.2⟩⟩
  rw [← hfp] at hin ⊢
  exact h r hr K hK i hi e j ht x hx hin

/-! ## By family -/

section

variable {A : String → FnAl} {r : Ref} {K : Mode.Cert} {i : ℕ} {e : Ent} {j : ℕ}

/-- A name is no fact. -/
theorem rres_name {M : ℕ → E} {fp o : ℕ} : RRes M fp (.name o) := trivial

end

/-! ## Termination facts at entered instances -/

/-- **The termination facts of the entered honest instances**: `TermInst` but at `node`s only. A
loop's final, untaken tail call is a `phantom` instance whose frame holds its arguments, the counter
at its bound, so `TermInst` itself fails there. -/
def TermNode (Ks : List Mode.Cert) : Prop :=
  ∀ r : Ref, r.Ok → ∀ K ∈ Ks, ∀ I ∈ honestInsts coreProgram B2C.fs B2C.H r.hdr r.T,
    (∃ f σ bufs kids, I.t = .node f σ bufs kids) → entryOf I.t.name = K.F.entry → ∀ p ∈ K.F.sig.term,
      RIn (refMem r.img) I.fp (.lt p.1 p.2) → RRes (refMem r.img) I.fp (.lt p.1 p.2)

/-- **A frame of the tracks at a function's entry is an entered instance of it** (`entryInst_X`, the
instance a `node`). -/
theorem entryNode_X {Ks : List Mode.Cert} {Km : Mode.Cert} {E0 : Mode.Env} {Y : Ref → St → Prop}
    {A : String → FnAl} (certs : ModeCerts Ks Km E0) (hKs : ∀ K ∈ Ks, K.F.entry ≠ 0)
    (hP : ProgAl guestProgram coreProgram A) (hmain : entOf A "main" = End.mainEntry) (hJ : JumpCellsAt A)
    (hL : AlLayout A) {r : Ref} (hr : r.Ok) {K : Mode.Cert} (hK : K ∈ Ks) {s : St} (hon : OnRun (XOf Y) r s)
    (hpc : s.pc = K.F.entry) :
    ∃ I ∈ honestInsts coreProgram B2C.fs B2C.H r.hdr r.T, (∃ f σ bufs kids, I.t = .node f σ bufs kids) ∧
      entryOf I.t.name = K.F.entry ∧ I.fp = s.fp := by
  obtain ⟨f, hf, -, hentry, -⟩ := certs.fn K hK
  have hfb := consecutive_bounds functions_consecutive f hf
  have hge : proLen ≤ s.steps := by
    rcases hon.1.1 with ⟨hlt, hpcs, -⟩ | ⟨hge, -⟩
    · have := consecutive_entry functions_consecutive _ f0_mem f hf (by rw [f0_entry']; omega)
        (by rw [f0_entry']; show f.entryPc < 0 + proLen; omega)
      rw [f0_entry'] at this
      exact absurd (hentry.trans this) (hKs K hK)
    · exact hge
  have hcode := codeLen_lt
  obtain ⟨_, _, _, h⟩ := trackAt_X hP hmain hJ hL hr hon hge
    (by rw [hpc, hentry, guest_logSize]; omega)
  obtain ⟨e, st', hst, hE, hfp, hat⟩ := h.top
  obtain ⟨g, bufs, kids, hn⟩ := hE.node
  refine ⟨e.I, hE.mem, ⟨g, e.σ, bufs, kids, hn⟩, ?_, hfp⟩
  rw [← hpc]
  exact (entry_of_atPc hP hL hE hat).2 f hf (by rw [hpc, hentry])

/-- **`TermRef` from the entered instances.** -/
theorem termRef_of_node {Ks : List Mode.Cert} {Km : Mode.Cert} {E0 : Mode.Env} {Y : Ref → St → Prop}
    {A : String → FnAl} (certs : ModeCerts Ks Km E0) (hKs : ∀ K ∈ Ks, K.F.entry ≠ 0)
    (hP : ProgAl guestProgram coreProgram A) (hmain : entOf A "main" = End.mainEntry) (hJ : JumpCellsAt A)
    (hL : AlLayout A) (hT : TermNode Ks) : TermRef Ks (XOf Y) := fun r hr K hK s hon hpc p hp hin ↦ by
  obtain ⟨I, hI, hn, he, hfp⟩ := entryNode_X certs hKs hP hmain hJ hL hr hK hon hpc
  rw [← hfp] at hin ⊢
  exact hT r hr K hK I hI hn he p hp hin

/-! ## The assembly -/

/-- **`ExecGaps` with the residuals at the honest frames and the termination facts at the entered
instances**: `ExecGaps.ofX` with `ResTop` for `res` and `TermNode` for `TermInst`. -/
theorem ExecGaps.ofR {Ks : List Mode.Cert} {Km : Mode.Cert} {E0 : Mode.Env} {A : String → FnAl}
    {Y : Ref → St → Prop}
    (certs : ModeCerts Ks Km E0) (main : MainOk Km E0) (mainExact : Budget.MainExactHyp)
    (hintAlloc : ∀ r, r.Ok → ∀ C, Ctx.of guestProgram r.adv = .ok C → ∀ s, OnRun (XOf Y) r s → ∀ pre h post,
      (C.hints[s.pc]?).getD [] = pre ++ h :: post → ∀ s1, pre.foldlM (runHint C) s = .ok s1 →
      Moves (refMem r.img) s s1 → isAllocHint h = true → HintIn s1 h → HintOk C (refMem r.img) s1 h)
    (hintWitness : ∀ r, r.Ok → ∀ C, Ctx.of guestProgram r.adv = .ok C → ∀ s, OnRun (XOf Y) r s → ∀ pre h post,
      (C.hints[s.pc]?).getD [] = pre ++ h :: post → ∀ s1, pre.foldlM (runHint C) s = .ok s1 →
      Moves (refMem r.img) s s1 → isWitnessHint h = true → HintIn s1 h → HintOk C (refMem r.img) s1 h)
    (hintComputed : ∀ r, r.Ok → ∀ C, Ctx.of guestProgram r.adv = .ok C → ∀ s h, OnRun (XOf Y) r s →
      h ∈ (C.hints[s.pc]?).getD [] → isAllocHint h = false → isWitnessHint h = false → ∀ s1,
      Moves (refMem r.img) s s1 → HintIn s1 h → HintOk C (refMem r.img) s1 h)
    (resTop : ResTop Ks A) (termNode : TermNode Ks)
    (progAl : ProgAl guestProgram coreProgram A) (mainAt : entOf A "main" = End.mainEntry) (layout : AlLayout A)
    (jumpCells : JumpCellsAt A) (entries : ∀ K ∈ Ks, K.F.entry ≠ 0) (derefPow : DerefPow Y)
    (hintsUsed : HintsUsed Y) (keepY : KeepY Y) (initY : InitY Y) (core : CoreHonAll Ks (XOf Y)) :
    ExecGaps Ks Km E0 (XOf Y) (fun _ ↦ ProAt) where
  certs := certs
  mainExact := mainExact
  hintAlloc := hintAlloc
  hintWitness := hintWitness
  hintComputed := hintComputed
  res := res_of_top certs entries progAl mainAt jumpCells layout resTop
  term := termRef_of_node certs entries progAl mainAt jumpCells layout termNode
  ref _ hr _ hC _ _ hon hop := refOk_X progAl mainAt jumpCells derefPow hr hC hon hop
  keepOp _ hr _ hC _ _ _ _ hon hop e1 hm e := keep_X progAl mainAt jumpCells derefPow hintsUsed keepY hr hC hon hop e1 hm e
  pro _ _ _ hC _ _ hon hP hop :=
    pro_step main certs.pows (certs.env Km certs.main).2.2.1 (certs.env Km certs.main).2.2.2.1
      certs.mainTerm hC rfl hP hon.2.1 hop
  init _ hr _ _ hC hm := ⟨init_X initY hr hC hm, pro_init hm⟩
  used _ _ _ hX := hX.2.1
  core := core

end

end LeanVM.Guest.EndExec
