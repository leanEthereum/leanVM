module

public import LeanVM.Guest.Mode.Edge
public import LeanVM.Prover.ExecuteComplete

/-!
# The invariant's parts

The executor's stack, read from the frame headers, for any frame predicate `Q K i s` (function `K`'s
frame `s.fp` at offset `i`: the core route's `CoreAt`) and any contracts `Ct` (by
entry pc: what a caller establishes at a function's entry, `PreAt`, and what it guarantees at its
return, `PostAt`; `none`, the mode signature's entry facts and `RetAll`). An activation (`Act`) is a
function's certificate with its frames: the top one, and below it a loop's earlier iterations (`Iter`:
the frame), the first one the frame its caller named. `ActOk`: the iterations chain to the first frame
(`Chain`, `IterOk`: each iteration returns what the next one does, `Back`), each frame having its
function's termination facts (`TermAt`). `Below`: each activation but `main`'s, at the bottom in frame
`0`, returns, by its top frame's header, into the one below it, suspended at a call (`Susp`) whose
frame predicate holds again (`Resume`) once the callee guarantees its signature's facts (`RetAll`).
`StackAt`: the top activation's top frame satisfies `Q` at its offset. Every fact reads only the
memory and frames, so it holds of a larger memory (`*.mono`). `ProgOk`: the certificates the stack is
made of, their code the executor's (`CodeOk`) and tied to each other.
-/

namespace LeanVM.Guest.Mode

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest
open LeanVM.Prover.Exec

@[expose] public section

/-- The state with memory `m` and frame `fp`, for the facts that read only those. -/
def stOf (m : Mem) (fp : ℕ) : St := ⟨m, Dlog.empty, 0, fp, 0, ∅, 0⟩

/-- The signature's termination facts hold at frame `fp`. -/
def TermAt (m : Mem) (fp : ℕ) (G : Sig) : Prop := ∀ p ∈ G.term, LTF (stOf m fp) p.1 p.2

/-- **What a function guarantees at its return** in frame `fp`: its signature's facts and its loop's
runs. -/
def RetAll (m : Mem) (fp : ℕ) (G : Sig) : Prop :=
  RetHolds (stOf m fp) G ∧ (∀ r ∈ G.postL, RW (stOf m fp) r) ∧ ∀ q ∈ G.postLP, PW (stOf m fp) q.1 q.2

/-- **A function's contract**: what a caller establishes at its entry (`pre`, of the memory and the
callee's frame) and what it guarantees at its return (`post`, of the memory and its frame), the latter
kept in any larger memory. -/
structure Ctr where
  pre : Mem → ℕ → Prop
  post : Mem → ℕ → Prop
  mono : ∀ {m m' : Mem} {fp : ℕ}, m ≤ m' → post m fp → post m' fp

/-- **The contracts, by entry pc**: `some c` a function's own contract, `none` its mode signature's. -/
abbrev Cts := ℕ → Option Ctr

/-- **What a caller establishes at the entry** of the function at pc `t`, of mode signature `G`: its
contract's precondition, or the signature's entry facts. -/
def PreAt (Ct : Cts) (E : Env) (t : ℕ) (G : Sig) (s : St) : Prop :=
  match Ct t with
  | some c => c.pre s.mem s.fp
  | none => Holds s (entryAbs E G)

/-- **What the function at pc `t` guarantees at its return** in frame `fp`: its contract's
postcondition, or the signature's facts and its loop's runs. -/
def PostAt (Ct : Cts) (t : ℕ) (G : Sig) (m : Mem) (fp : ℕ) : Prop :=
  match Ct t with
  | some c => c.post m fp
  | none => RetAll m fp G

/-- **Mode contracts at a function and its callees**: at its own entry and at each callee its
environment names. -/
def ModeCts (Ct : Cts) (K : Cert) : Prop :=
  Ct K.F.entry = none ∧ ∀ t G, K.E.sigs.get t = some G → Ct t = none

/-- A loop's iteration in frame `fp` guarantees at its return what the next one, in frame `nx`, does,
in any memory past `m`. -/
def Back (Ct : Cts) (t : ℕ) (G : Sig) (m : Mem) (fp nx : ℕ) : Prop :=
  ∀ m', m ≤ m' → m'.WF → m'.used ≤ maxCells → PostAt Ct t G m' nx → PostAt Ct t G m' fp

/-- A loop's earlier iteration: its frame. -/
structure Iter where
  fp : ℕ

/-- Iteration `it` of a loop of `K`, its next frame `nx`. -/
structure IterOk (Ct : Cts) (m : Mem) (Kc : Cert) (it : Iter) (nx : ℕ) : Prop where
  fp : it.fp < maxCells
  term : TermAt m it.fp Kc.F.sig
  back : Back Ct Kc.F.entry Kc.F.sig m it.fp nx
  nx : nx < maxCells

/-- The iterations below frame `top` chain down to the first frame `fp0`, the latest first. -/
def Chain (Ct : Cts) (m : Mem) (K : Cert) : List Iter → ℕ → ℕ → Prop
  | [], top, fp0 => top = fp0
  | it :: its, top, fp0 => IterOk Ct m K it top ∧ Chain Ct m K its it.fp fp0

/-- An activation: a function's certificate, its loop's earlier iterations, its top and first
frames. -/
structure Act where
  K : Cert
  its : List Iter
  fp : ℕ
  fp0 : ℕ

/-- An activation of one of `Ks`, its frames chained, its top frame's termination facts. -/
structure ActOk (Ct : Cts) (Ks : List Cert) (m : Mem) (a : Act) : Prop where
  mem : a.K ∈ Ks
  chain : Chain Ct m a.K a.its a.fp a.fp0
  term : TermAt m a.fp a.K.F.sig
  fp : a.fp < maxCells

/-- **A suspended caller goes on**: once the callee at pc `t`, of signature `G`, in frame `fpE`
guarantees its contract (`PostAt`) in a memory past `m0`, the caller's frame predicate `Q`, in frame
`fpC`, holds at offset `ro`. -/
def Resume (Ct : Cts) (Q : ℕ → St → Prop) (fpC ro t : ℕ) (G : Sig) (fpE : ℕ) (m0 : Mem) : Prop :=
  ∀ m, m0 ≤ m → m.WF → m.used ≤ maxCells → fpE < maxCells → fpC < maxCells →
    PostAt Ct t G m fpE → TermAt m fpE G → Q ro (stOf m fpC)

/-- Activation `b` is suspended at a call into the callee at pc `t`, of signature `G`, in frame `fpE`,
which returns to pc `r`. -/
def Susp (Ct : Cts) (Q : Cert → ℕ → St → Prop) (m : Mem) (b : Act) (r t : ℕ) (G : Sig) (fpE : ℕ) : Prop :=
  ∃ ro m0, r = b.K.F.entry + ro ∧ ro < b.K.code.length ∧ m0 ≤ m ∧ Resume Ct (Q b.K) b.fp ro t G fpE m0

/-- The activations below `a`: none, `a` being `main`'s in frame `0`, or one suspended at the call
`a`'s header returns to, and those below it. -/
def Below (Ct : Cts) (Q : Cert → ℕ → St → Prop) (Ks : List Cert) (Km : Cert) (m : Mem) : Act → List Act → Prop
  | a, [] => a.K = Km ∧ a.its = [] ∧ a.fp = 0
  | a, b :: rest => a.K.F.main = false ∧ ∃ r, m.get (a.fp + 0) = some (ofK (g ^ r)) ∧
      m.get (a.fp + 1) = some (ofK (g ^ b.fp)) ∧ Susp Ct Q m b r a.K.F.entry a.K.F.sig a.fp0 ∧ ActOk Ct Ks m b ∧
      Below Ct Q Ks Km m b rest

/-- **The stack**: the top activation's top frame is the executor's, its frame predicate holding at
its offset. -/
def StackAt (Ct : Cts) (Q : Cert → ℕ → St → Prop) (Ks : List Cert) (Km : Cert) (s : St) : Prop :=
  ∃ a rest i, ActOk Ct Ks s.mem a ∧ a.fp = s.fp ∧ i < a.K.code.length ∧ s.pc = a.K.F.entry + i ∧
    Q a.K i s ∧ Below Ct Q Ks Km s.mem a rest

/-- The jump table is written: its cells, with their targets' powers. -/
def JtMem (E0 : Env) (m : Mem) : Prop :=
  E0.jtHi ≤ maxCells ∧ (∀ j, E0.jtLo ≤ j → j < E0.jtHi → m.written j = true) ∧
    ∀ d e, E0.jtLo ≤ d → d < E0.jtHi → E0.jt.get d = some e → m.get d = some (ofK (g ^ e))

/-- The registers are the final state's. -/
def Halted (prog : LeanIsaProgram) (s : St) : Prop :=
  (⟨g ^ s.pc, g ^ s.fp⟩ : Registers K) = Registers.final prog

/-- `main`'s entry, after the jump table is written. -/
def StartMain (Km : Cert) (E0 : Env) (s : St) : Prop :=
  s.pc = Km.F.entry ∧ s.fp = 0 ∧ JtMem E0 s.mem ∧ Holds s (entryAbs Km.E Km.F.sig)

/-- A certificate's code is the executor's at its pcs. -/
structure CodeOk (C : Ctx) (K : Cert) : Prop where
  ops : ∀ i (hi : i < K.code.length), C.ops[K.F.entry + i]? = some (opOfOff K.code[i])

/-- **The certificates**: each one's code the executor's, their entries distinct, the signatures each
names its callee's, their program the same, `main` never returning or called. -/
structure ProgOk (prog : LeanIsaProgram) (C : Ctx) (Ks : List Cert) (Km : Cert) (E0 : Env) :
    Prop where
  ok : ∀ K ∈ Ks, CodeOk C K
  ne : ∀ K ∈ Ks, 0 < K.code.length
  uniq : ∀ K ∈ Ks, ∀ K' ∈ Ks, K.F.entry = K'.F.entry → K = K'
  sigs : ∀ K ∈ Ks, ∀ t G, K.E.sigs.get t = some G →
    ∃ K' ∈ Ks, K'.F.entry = t ∧ K'.F.sig = G ∧ K'.F.main = false
  env : ∀ K ∈ Ks, K.E.pows = E0.pows ∧ K.E.jt = E0.jt ∧ K.E.jtLo = E0.jtLo ∧ K.E.jtHi = E0.jtHi ∧
    K.E.halt = E0.halt
  pows : E0.pows.Ok
  jt : ∀ d e, E0.jt.get d = some e → e < 2 ^ 62
  halt : E0.halt = 2 ^ prog.logSize - 1
  main : Km ∈ Ks
  mainF : Km.F.main = true
  mainRet : ∀ (i c : ℕ), Km.code[i]? ≠ some (OffsetInstruction.jump c 0 1)
  mainTerm : Km.F.sig.term = []

/-! ## Facts read off the memory and the frame -/

theorem LTF.mem {m m' : Mem} (hle : m ≤ m') {fp : ℕ} {a b : Idx} (h : LTF (stOf m fp) a b) :
    LTF (stOf m' fp) a b :=
  LTF.mono (s := stOf m fp) (s' := stOf m' fp) hle rfl h

theorem TermAt.mono {m m' : Mem} (hle : m ≤ m') {fp : ℕ} {G : Sig} (h : TermAt m fp G) :
    TermAt m' fp G :=
  fun p hp ↦ (h p hp).mem hle

theorem RetHolds.mono {s s' : St} (hle : s.mem ≤ s'.mem) (hfp : s'.fp = s.fp) {G : Sig}
    (h : RetHolds s G) : RetHolds s' G := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := h
  refine ⟨fun o ho ↦ hfp ▸ written_mono hle (h1 o ho), fun k hk ↦ (h2 k hk).mono hle hfp,
    fun r hr ↦ (h3 r hr).mono hle hfp, fun q hq ↦ (h4 q hq).mono hle hfp, fun p hp ↦ ?_,
    fun p hp ↦ (h6 p hp).mono hle hfp, fun q hq ↦ (h7 q hq).mono hle hfp⟩
  obtain ⟨u, hu, hmu⟩ := h5 p hp
  exact ⟨u, by rw [hfp]; exact hle.get _ _ hu, hmu.mono hle hfp⟩

theorem RetAll.mono {m m' : Mem} (hle : m ≤ m') {fp : ℕ} {G : Sig} (h : RetAll m fp G) : RetAll m' fp G :=
  ⟨RetHolds.mono (s := stOf m fp) (s' := stOf m' fp) hle rfl h.1,
    fun r hr ↦ RW.mono (s := stOf m fp) (s' := stOf m' fp) hle rfl (h.2.1 r hr),
    fun q hq ↦ PW.mono (s := stOf m fp) (s' := stOf m' fp) hle rfl (h.2.2 q hq)⟩

theorem PostAt.mono {Ct : Cts} {t : ℕ} {G : Sig} {m m' : Mem} (hle : m ≤ m') {fp : ℕ}
    (h : PostAt Ct t G m fp) : PostAt Ct t G m' fp := by
  unfold PostAt at h ⊢
  cases hc : Ct t with
  | some c => rw [hc] at h; exact c.mono hle h
  | none => rw [hc] at h; exact h.mono hle

theorem preAt_none {Ct : Cts} {E : Env} {t : ℕ} {G : Sig} {s : St} (h : Ct t = none) :
    PreAt Ct E t G s = Holds s (entryAbs E G) := by
  unfold PreAt; rw [h]

theorem postAt_none {Ct : Cts} {t : ℕ} {G : Sig} {m : Mem} {fp : ℕ} (h : Ct t = none) :
    PostAt Ct t G m fp = RetAll m fp G := by
  unfold PostAt; rw [h]

/-- `PreAt` reads only the memory and the frame. -/
theorem PreAt.congr {Ct : Cts} {E : Env} {t : ℕ} {G : Sig} {s s' : St} (hm : s'.mem = s.mem) (hfp : s'.fp = s.fp)
    (h : PreAt Ct E t G s) : PreAt Ct E t G s' := by
  unfold PreAt at h ⊢
  cases hc : Ct t with
  | some c => rw [hc] at h; rw [hm, hfp]; exact h
  | none => rw [hc] at h; exact Holds.mono (s := s) (s' := s') (by rw [hm]; exact Mem.le_refl _) hfp h

/-- `Back` for a mode contract: the signature's guarantees at the next frame give them at this one. -/
def BackM (m : Mem) (G : Sig) (fp nx : ℕ) : Prop :=
  ∀ m', m ≤ m' → m'.WF → m'.used ≤ maxCells → RetAll m' nx G → RetAll m' fp G

theorem BackM.back {Ct : Cts} {t : ℕ} {G : Sig} {m : Mem} {fp nx : ℕ} (hC : Ct t = none) (h : BackM m G fp nx) :
    Back Ct t G m fp nx := by
  intro m' h1 h2 h3 hP
  rw [postAt_none hC] at hP ⊢
  exact h m' h1 h2 h3 hP

/-- A loop's tail call stated for its mode signature, read for a mode contract. -/
theorem tail_of_mode {Ct : Cts} {K : Cert} {s1 s' : St} {A B D : Prop} (hC : Ct K.F.entry = none)
    (h : A ∧ B ∧ D ∧ BackM s'.mem K.F.sig s1.fp s'.fp ∧ Holds s' (entryAbs K.E K.F.sig)) :
    A ∧ B ∧ D ∧ Back Ct K.F.entry K.F.sig s'.mem s1.fp s'.fp ∧ PreAt Ct K.E K.F.entry K.F.sig s' :=
  ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1.back hC, by rw [preAt_none hC]; exact h.2.2.2.2⟩

theorem Back.mono {Ct : Cts} {t : ℕ} {m m' : Mem} (hle : m ≤ m') {G : Sig} {fp nx : ℕ}
    (h : Back Ct t G m fp nx) : Back Ct t G m' fp nx :=
  fun m'' h2 ↦ h m'' (Mem.le_trans hle h2)

theorem IterOk.mono {Ct : Cts} {m m' : Mem} (hle : m ≤ m') {K : Cert} {it : Iter} {nx : ℕ}
    (h : IterOk Ct m K it nx) : IterOk Ct m' K it nx :=
  ⟨h.fp, h.term.mono hle, h.back.mono hle, h.nx⟩

theorem Chain.mono {Ct : Cts} {m m' : Mem} (hle : m ≤ m') {K : Cert} :
    ∀ {its : List Iter} {top fp0 : ℕ}, Chain Ct m K its top fp0 → Chain Ct m' K its top fp0
  | [], _, _, h => h
  | _ :: _, _, _, ⟨h1, h2⟩ => ⟨h1.mono hle, Chain.mono hle h2⟩

theorem ActOk.mono {Ct : Cts} {Ks : List Cert} {m m' : Mem} (hle : m ≤ m') {a : Act} (h : ActOk Ct Ks m a) :
    ActOk Ct Ks m' a :=
  ⟨h.mem, h.chain.mono hle, h.term.mono hle, h.fp⟩

theorem Susp.mono {Ct : Cts} {Q : Cert → ℕ → St → Prop} {m m' : Mem} (hle : m ≤ m') {b : Act} {r t : ℕ}
    {G : Sig} {fpE : ℕ} (h : Susp Ct Q m b r t G fpE) : Susp Ct Q m' b r t G fpE :=
  let ⟨ro, m0, h1, h2, h3, h4⟩ := h
  ⟨ro, m0, h1, h2, Mem.le_trans h3 hle, h4⟩

theorem Below.mono {Ct : Cts} {Q : Cert → ℕ → St → Prop} {Ks : List Cert} {Km : Cert} {m m' : Mem}
    (hle : m ≤ m') :
    ∀ {a : Act} {rest : List Act}, Below Ct Q Ks Km m a rest → Below Ct Q Ks Km m' a rest
  | _, [], h => h
  | _, _ :: _, ⟨h1, r, h2, h3, h4, h5, h6⟩ =>
    ⟨h1, r, hle.get _ _ h2, hle.get _ _ h3, h4.mono hle, h5.mono hle, Below.mono hle h6⟩

theorem JtMem.mono {E0 : Env} {m m' : Mem} (hle : m ≤ m') (h : JtMem E0 m) : JtMem E0 m' :=
  ⟨h.1, fun j h1 h2 ↦ written_mono hle (h.2.1 j h1 h2), fun d e h1 h2 h3 ↦ hle.get _ _ (h.2.2 d e h1 h2 h3)⟩

/-! ## The program's table -/

theorem envOk_of {prog : LeanIsaProgram} {C : Ctx} {Ks : List Cert} {Km : Cert} {E0 : Env}
    (P : ProgOk prog C Ks Km E0) {K : Cert} (hK : K ∈ Ks) {s : St} (h : JtMem E0 s.mem) :
    EnvOk s K.E := by
  obtain ⟨e1, e2, e3, e4, -⟩ := P.env K hK
  refine ⟨e1 ▸ P.pows, e4 ▸ h.1, fun d e h1 h2 h3 ↦ ?_⟩
  rw [e3] at h1; rw [e4] at h2; rw [e2] at h3
  exact h.2.2 d e h1 h2 h3

theorem rw_jt {E0 E : Env} (h3 : E.jtLo = E0.jtLo) (h4 : E.jtHi = E0.jtHi) {s : St}
    (h : JtMem E0 s.mem) : RW s (jtRng E) := by
  refine ⟨1, E.jtLo, E.jtHi, MonoVal.one', rfl, rfl, fun j hj1 hj2 ↦ ⟨j, ⟨?_, ?_⟩, ?_⟩⟩
  · simp [jtRng]
  · have := h.1; omega
  · exact h.2.1 j (by omega) (by omega)

theorem envSmall_of {prog : LeanIsaProgram} {C : Ctx} {Ks : List Cert} {Km : Cert} {E0 : Env}
    (P : ProgOk prog C Ks Km E0) (hsz : C.ops.size ≤ 2 ^ 30) {K : Cert} (hK : K ∈ Ks) :
    EnvSmall K.E := by
  refine ⟨fun t G hG ↦ ?_, fun d e h ↦ P.jt d e ((P.env K hK).2.1 ▸ h)⟩
  obtain ⟨K', hK', rfl, -, -⟩ := P.sigs K hK t G hG
  have h0 := (P.ok K' hK').ops 0 (P.ne K' hK')
  have : K'.F.entry < C.ops.size := by
    by_contra hn
    rw [Array.getElem?_eq_none (by omega)] at h0
    cases h0
  omega

theorem entryAbs_congr {E E' : Env} (h3 : E.jtLo = E'.jtLo) (h4 : E.jtHi = E'.jtHi) (G : Sig) :
    entryAbs E G = entryAbs E' G := by
  unfold entryAbs jtRng
  rw [h3, h4]

/-- `PreAt` on an environment with the same jump table, of a state with the same memory and frame. -/
theorem PreAt.env {Ct : Cts} {E E' : Env} {t : ℕ} {G : Sig} {s s' : St} (h3 : E.jtLo = E'.jtLo)
    (h4 : E.jtHi = E'.jtHi) (hm : s'.mem = s.mem) (hfp : s'.fp = s.fp) (h : PreAt Ct E t G s) :
    PreAt Ct E' t G s' := by
  have h' := PreAt.congr hm hfp h
  unfold PreAt at h' ⊢
  rw [← entryAbs_congr h3 h4 G]
  exact h'

/-- A function's pcs are the executor's: below its size. -/
theorem code_pc {C : Ctx} {K : Cert} (hK : CodeOk C K) {i : ℕ} (hi : i < K.code.length) :
    K.F.entry + i < C.ops.size := by
  have h0 := hK.ops i hi
  by_contra hn
  rw [Array.getElem?_eq_none (by omega)] at h0
  cases h0

/-! ## The chain of a loop's iterations -/

theorem Chain.fp0 {Ct : Cts} {m : Mem} {K : Cert} :
    ∀ {its : List Iter} {top fp0 : ℕ}, Chain Ct m K its top fp0 → top < maxCells → fp0 < maxCells
  | [], _, _, h, ht => h ▸ ht
  | _ :: _, _, _, ⟨h1, h2⟩, _ => Chain.fp0 h2 h1.fp

theorem Chain.term {Ct : Cts} {m : Mem} {K : Cert} :
    ∀ {its : List Iter} {top fp0 : ℕ}, Chain Ct m K its top fp0 → TermAt m top K.F.sig →
      TermAt m fp0 K.F.sig
  | [], _, _, h, ht => h ▸ ht
  | _ :: _, _, _, ⟨h1, h2⟩, _ => Chain.term h2 h1.term

/-- **A loop's guarantees at return, down its iterations**: each iteration returns what the next one
does (`Back`). -/
theorem Chain.back {Ct : Cts} {m : Mem} {K : Cert} (hwf : m.WF) (hu : m.used ≤ maxCells) :
    ∀ {its : List Iter} {top fp0 : ℕ}, Chain Ct m K its top fp0 → PostAt Ct K.F.entry K.F.sig m top →
      PostAt Ct K.F.entry K.F.sig m fp0
  | [], _, _, h, ht => h ▸ ht
  | _ :: _, _, _, ⟨h1, h2⟩, ht => Chain.back hwf hu h2 (h1.back m (Mem.le_refl _) hwf hu ht)

end

end LeanVM.Guest.Mode
