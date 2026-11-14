module

public import LeanVM.Guest.Mode.Edge
public import LeanVM.Prover.ExecuteComplete

/-!
# The invariant's parts

The executor's stack, read from the frame headers, as the mode walk knows it. An activation (`Act`)
is a function's certificate with its frames: the top one, and below it a loop's earlier iterations
(`Iter`: the frame, the walk's state at its tail call, the offset of the next frame), the first one
the frame its caller named. `ActOk`: the iterations chain to the first frame (`Chain`, `IterOk`), each
frame having its function's termination facts (`TermAt`). `Below`: each activation but `main`'s, at
the bottom in frame `0`, returns, by its top frame's header, into the one below it, suspended at a
call (`Susp`) whose walk goes on (`Resume`) once the callee guarantees its signature's facts.
`StackAt`: the top activation's top frame is at an offset its walk reaches (`AtOff`). Every fact reads
only the memory and frames, so it holds of a larger memory (`*.mono`). `ProgOk`: the certificates
the stack is made of, tied to the executor and to each other.
-/

namespace LeanVM.Guest.Mode

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest
open LeanVM.Prover.Exec

@[expose] public section

/-- The state with memory `m` and frame `fp`, for the facts that read only those. -/
def stOf (m : Mem) (fp : ℕ) : St := ⟨m, Dlog.empty, 0, fp, 0, ∅, 0⟩

/-- The signature's termination facts hold at frame `fp`. -/
def TermAt (m : Mem) (fp : ℕ) (G : Sig) : Prop := ∀ p ∈ G.term, LTF (stOf m fp) p.1 p.2

/-- A signature guarantees nothing at return but its loop's runs. -/
def RetEmpty (G : Sig) : Prop := G.ret = [] ∧ G.post = [] ∧ G.postR = [] ∧ G.postP = [] ∧ G.retV = []

/-- A loop's earlier iteration: its frame, the walk's state at its tail call, the next frame's
offset. -/
structure Iter where
  fp : ℕ
  A : Abs
  e : ℕ

/-- Iteration `it` of a loop of `K`, its next frame `nx`. -/
structure IterOk (m : Mem) (Kc : Cert) (it : Iter) (nx : ℕ) : Prop where
  holds : Holds (stOf m it.fp) it.A
  next : (g : K) ^ nx = g ^ (it.fp + it.e)
  fp : it.fp < maxCells
  nx : nx < maxCells
  loop : loopOk it.A Kc.F.sig = true
  runs : ∀ r ∈ Kc.F.sig.postL ++ Kc.F.sig.postLP.map (·.1),
    trRngUp it.A (.own it.e) r = some ⟨r.q, r.lo.succ, r.hi, r.S, r.d⟩
  term : TermAt m it.fp Kc.F.sig
  ret : RetEmpty Kc.F.sig

/-- The iterations below frame `top` chain down to the first frame `fp0`, the latest first. -/
def Chain (m : Mem) (K : Cert) : List Iter → ℕ → ℕ → Prop
  | [], top, fp0 => top = fp0
  | it :: its, top, fp0 => IterOk m K it top ∧ Chain m K its it.fp fp0

/-- An activation: a function's certificate, its loop's earlier iterations, its top and first
frames. -/
structure Act where
  K : Cert
  its : List Iter
  fp : ℕ
  fp0 : ℕ

/-- An activation of one of `Ks`, its frames chained, its top frame's termination facts. -/
structure ActOk (Ks : List Cert) (m : Mem) (a : Act) : Prop where
  mem : a.K ∈ Ks
  chain : Chain m a.K a.its a.fp a.fp0
  term : TermAt m a.fp a.K.F.sig
  fp : a.fp < maxCells

/-- **A suspended caller goes on**: once the callee of signature `G` in frame `fpE` guarantees its
facts in a memory past `m0`, the caller's walk, in frame `fpC`, is at offset `ro`. -/
def Resume (K : Cert) (fpC ro : ℕ) (G : Sig) (fpE : ℕ) (m0 : Mem) : Prop :=
  ∀ m, m0 ≤ m → m.WF → m.used ≤ maxCells → fpE < maxCells → fpC < maxCells →
    RetHolds (stOf m fpE) G → (∀ r ∈ G.postL, RW (stOf m fpE) r) →
    (∀ q ∈ G.postLP, PW (stOf m fpE) q.1 q.2) → TermAt m fpE G →
    AtOff K.E K.F K.code ro (stOf m fpC)

/-- Activation `b` is suspended at a call into a callee of signature `G` in frame `fpE`, which
returns to pc `r`. -/
def Susp (m : Mem) (b : Act) (r : ℕ) (G : Sig) (fpE : ℕ) : Prop :=
  ∃ ro m0, r = b.K.F.entry + ro ∧ ro < b.K.code.length ∧ m0 ≤ m ∧ Resume b.K b.fp ro G fpE m0

/-- The activations below `a`: none, `a` being `main`'s in frame `0`, or one suspended at the call
`a`'s header returns to, and those below it. -/
def Below (Ks : List Cert) (Km : Cert) (m : Mem) : Act → List Act → Prop
  | a, [] => a.K = Km ∧ a.its = [] ∧ a.fp = 0
  | a, b :: rest => a.K.F.main = false ∧ ∃ r, m.get (a.fp + 0) = some (ofK (g ^ r)) ∧
      m.get (a.fp + 1) = some (ofK (g ^ b.fp)) ∧ Susp m b r a.K.F.sig a.fp0 ∧ ActOk Ks m b ∧
      Below Ks Km m b rest

/-- **The stack**: the top activation's top frame is the executor's, at an offset its walk reaches. -/
def StackAt (Ks : List Cert) (Km : Cert) (s : St) : Prop :=
  ∃ a rest i, ActOk Ks s.mem a ∧ a.fp = s.fp ∧ i < a.K.code.length ∧ s.pc = a.K.F.entry + i ∧
    AtOff a.K.E a.K.F a.K.code i s ∧ Below Ks Km s.mem a rest

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

/-- **The certificates**: each one's walk tied to the executor, their entries distinct, the
signatures each names its callee's, their program the same, `main` never returning or called, a
function tail-calling itself guaranteeing only its runs, which range over its termination facts, and
no walk falling through its function's end. -/
structure ProgOk (prog : LeanIsaProgram) (C : Ctx) (Ks : List Cert) (Km : Cert) (E0 : Env) :
    Prop where
  ok : ∀ K ∈ Ks, CertOk C K
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
  tailRet : ∀ K ∈ Ks, ∀ G, K.E.sigs.get K.F.entry = some G → RetEmpty G
  loopRng : ∀ K ∈ Ks, ∀ r ∈ K.F.sig.postL ++ K.F.sig.postLP.map (·.1), (r.lo, r.hi) ∈ K.F.sig.term
  endOk : ∀ K ∈ Ks, ∀ cur pend, preAt K.E K.F K.code K.code.length = some (cur, pend) → cur = []

/-! ## Facts read off the memory and the frame -/

theorem holds_stOf {s : St} {A : Abs} : Holds s A ↔ Holds (stOf s.mem s.fp) A :=
  ⟨fun h ↦ Holds.mono (s := s) (s' := stOf s.mem s.fp) (Mem.le_refl _) rfl h,
    fun h ↦ Holds.mono (s := stOf s.mem s.fp) (s' := s) (Mem.le_refl _) rfl h⟩

theorem Cov.mono {s s' : St} (hle : s.mem ≤ s'.mem) (hfp : s'.fp = s.fp) {P : Pend} {j : ℕ}
    (h : Cov s P j) : Cov s' P j :=
  let ⟨G, hG, hj, B, hB, hH⟩ := h
  ⟨G, hG, hj, B, hB, hH.mono hle hfp⟩

theorem AtOff.mono {E : Env} {F : Fun} {code : List OffsetInstruction} {i : ℕ} {s s' : St}
    (hle : s.mem ≤ s'.mem) (hfp : s'.fp = s.fp) (h : AtOff E F code i s) : AtOff E F code i s' := by
  obtain ⟨cur, pend, h0, hh⟩ := h
  exact ⟨cur, pend, h0, hh.imp (fun ⟨A, hA, hH⟩ ↦ ⟨A, hA, hH.mono hle hfp⟩) (Cov.mono hle hfp)⟩

theorem LTF.mem {m m' : Mem} (hle : m ≤ m') {fp : ℕ} {a b : Idx} (h : LTF (stOf m fp) a b) :
    LTF (stOf m' fp) a b :=
  LTF.mono (s := stOf m fp) (s' := stOf m' fp) hle rfl h

theorem TermAt.mono {m m' : Mem} (hle : m ≤ m') {fp : ℕ} {G : Sig} (h : TermAt m fp G) :
    TermAt m' fp G :=
  fun p hp ↦ (h p hp).mem hle

theorem IterOk.mono {m m' : Mem} (hle : m ≤ m') {K : Cert} {it : Iter} {nx : ℕ}
    (h : IterOk m K it nx) : IterOk m' K it nx :=
  ⟨Holds.mono (s := stOf m it.fp) (s' := stOf m' it.fp) hle rfl h.holds, h.next, h.fp, h.nx, h.loop,
    h.runs, h.term.mono hle, h.ret⟩

theorem Chain.mono {m m' : Mem} (hle : m ≤ m') {K : Cert} :
    ∀ {its : List Iter} {top fp0 : ℕ}, Chain m K its top fp0 → Chain m' K its top fp0
  | [], _, _, h => h
  | _ :: _, _, _, ⟨h1, h2⟩ => ⟨h1.mono hle, Chain.mono hle h2⟩

theorem ActOk.mono {Ks : List Cert} {m m' : Mem} (hle : m ≤ m') {a : Act} (h : ActOk Ks m a) :
    ActOk Ks m' a :=
  ⟨h.mem, h.chain.mono hle, h.term.mono hle, h.fp⟩

theorem Susp.mono {m m' : Mem} (hle : m ≤ m') {b : Act} {r : ℕ} {G : Sig} {fpE : ℕ}
    (h : Susp m b r G fpE) : Susp m' b r G fpE :=
  let ⟨ro, m0, h1, h2, h3, h4⟩ := h
  ⟨ro, m0, h1, h2, Mem.le_trans h3 hle, h4⟩

theorem Below.mono {Ks : List Cert} {Km : Cert} {m m' : Mem} (hle : m ≤ m') :
    ∀ {a : Act} {rest : List Act}, Below Ks Km m a rest → Below Ks Km m' a rest
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

/-- A function's pcs are the executor's: below its size. -/
theorem cert_pc {C : Ctx} {K : Cert} (hK : CertOk C K) {i : ℕ} (hi : i < K.code.length) :
    K.F.entry + i < C.ops.size := by
  have h0 := hK.ops i hi
  by_contra hn
  rw [Array.getElem?_eq_none (by omega)] at h0
  cases h0

/-! ## The chain of a loop's iterations -/

theorem Chain.fp0 {m : Mem} {K : Cert} :
    ∀ {its : List Iter} {top fp0 : ℕ}, Chain m K its top fp0 → top < maxCells → fp0 < maxCells
  | [], _, _, h, ht => h ▸ ht
  | _ :: _, _, _, ⟨h1, h2⟩, _ => Chain.fp0 h2 h1.fp

theorem Chain.term {m : Mem} {K : Cert} :
    ∀ {its : List Iter} {top fp0 : ℕ}, Chain m K its top fp0 → TermAt m top K.F.sig →
      TermAt m fp0 K.F.sig
  | [], _, _, h, ht => h ▸ ht
  | _ :: _, _, _, ⟨h1, h2⟩, _ => Chain.term h2 h1.term

theorem retHolds_empty {s : St} {G : Sig} (h : RetEmpty G) : RetHolds s G := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> intro x hx <;> simp_all

theorem Chain.ret {m : Mem} {K : Cert} :
    ∀ {its : List Iter} {top fp0 : ℕ}, Chain m K its top fp0 → RetHolds (stOf m top) K.F.sig →
      RetHolds (stOf m fp0) K.F.sig
  | [], _, _, h, ht => h ▸ ht
  | _ :: _, _, _, ⟨h1, _⟩, _ => retHolds_empty h1.ret

/-- The frame `nx`, the next iteration's, as a callee's of iteration `it`'s. -/
theorem IterOk.frames {m : Mem} {K : Cert} {it : Iter} {nx : ℕ} (h : IterOk m K it nx)
    (hwf : m.WF) (hu : m.used ≤ maxCells) : Frames (stOf m it.fp) (stOf m nx) (.own it.e) := by
  have hm := MonoVal.own (s := stOf m it.fp) it.e
  change MonoVal (stOf m it.fp) (.own it.e) (ofK (g ^ (it.fp + it.e))) at hm
  rw [← h.next] at hm
  exact ⟨rfl, hm, h.nx, h.fp, hwf, hu⟩

/-- **A loop's runs, down its iterations**: the runs at the top frame give them at the first. -/
theorem Chain.runs {m : Mem} {K : Cert} (hwf : m.WF) (hu : m.used ≤ maxCells) :
    ∀ {its : List Iter} {top fp0 : ℕ}, Chain m K its top fp0 →
      (∀ r ∈ K.F.sig.postL, RW (stOf m top) r) → (∀ q ∈ K.F.sig.postLP, PW (stOf m top) q.1 q.2) →
      (∀ r ∈ K.F.sig.postL, RW (stOf m fp0) r) ∧ ∀ q ∈ K.F.sig.postLP, PW (stOf m fp0) q.1 q.2
  | [], _, _, h, hR, hP => h ▸ ⟨hR, hP⟩
  | it :: its, top, fp0, ⟨h1, h2⟩, hR, hP => by
    have F := h1.frames hwf hu
    obtain ⟨hpt, hptP⟩ := loopOk_sound h1.holds h1.fp hwf hu h1.loop
    refine Chain.runs hwf hu h2 (fun r hr ↦ ?_) (fun q hq ↦ ?_)
    · exact loop_step h1.holds F (h1.runs r (List.mem_append_left _ hr)) (hR r hr) (hpt r hr)
    · exact loop_stepP h1.holds F
        (h1.runs q.1 (List.mem_append_right _ (List.mem_map_of_mem hq))) (hP q hq) (hptP q hq)

/-- **The exiting iteration's runs**: at a return the walk accepts, each run ranging over a
termination fact is its point. -/
theorem ret_runs {s : St} {A : Abs} {G : Sig} (hA : Holds s A) (hfp : s.fp < maxCells)
    (hwf : s.mem.WF) (hu : s.mem.used ≤ maxCells) (h : retOk A G = true)
    (hT : ∀ p ∈ G.term, LTF s p.1 p.2)
    (hrng : ∀ r ∈ G.postL ++ G.postLP.map (·.1), (r.lo, r.hi) ∈ G.term) :
    (∀ r ∈ G.postL, RW s r) ∧ ∀ q ∈ G.postLP, PW s q.1 q.2 := by
  obtain ⟨-, hpt, hptP⟩ := retOk_sound hA hfp hwf hu h
  have hex := retOk_exit hA h
  refine ⟨fun r hr ↦ ?_, fun q hq ↦ ?_⟩
  · have hp := hrng r (List.mem_append_left _ hr)
    obtain ⟨xa, xb, ha, hb, -⟩ := hT _ hp
    have := hex _ hp xa xb ha hb
    exact RW.last ha (this ▸ hb) (hpt r hr)
  · have hp := hrng q.1 (List.mem_append_right _ (List.mem_map_of_mem hq))
    obtain ⟨xa, xb, ha, hb, -⟩ := hT _ hp
    have := hex _ hp xa xb ha hb
    exact PW.last ha (this ▸ hb) (hptP q hq)

end

end LeanVM.Guest.Mode
