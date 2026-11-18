/-
  LeanVM.Guest.CoreMode.CoreLoop

  The core route for a leaf loop helper: atoms, its tail call, its return.
-/

module

public import LeanVM.Guest.CoreMode.CoreSound
public import LeanVM.Guest.CoreMode.LoopSig
public import LeanVM.Guest.CoreMode.PairLoop
public import LeanVM.Guest.CoreMode.LoopB
public import LeanVM.Guest.Mode.InvCert

/-!
# The core route for a loop helper

A leaf loop helper (`loopB`): a body of atoms, its tail call `callIf c f args` to itself, `ret []`;
compiled (`loopCode`) to code with no `JUMP` but its last two, the tail call's (through a next-frame
cell) and the return. `LoopOk K Cf`: the kernel's checks, as `CoreOk`'s, with the heap check's loop
rules (`heapOkC` at a termination fact) and the loop's mode signature translated (`sigOkL`).

`frameSpec_loop`: such a function meets `FrameSpec` for `CoreAt`.

* The heap facts (`loop_heap`): `heapOkC_sound`, its entry facts the mode signature's termination
  fact (`termAt_entryF`), at any honest valuation of a frame whose parameter cells hold their words
  (`ParAt`).
* A step at the tail `JUMP` (`pair_tailL`): not taken (its condition `0`), the call skipped, the
  position the closing `ret []`; taken, a loop's tail call (`Out.tail`): the frame walk's next frame
  (`JumpOut.tail`), which is the honest tree's (`HonF.tail`): its entry facts are the tail call's
  preconditions at the next counter (`ReadsOkC`, `slot_hwT`, `slot_rwT`), its header this frame's,
  and this iteration returns what the next does (`Back`): its guarantees at its parameters are
  written by its path, the tail call's guarantees being the next iteration's (`PostOkC`,
  `postSet_of_retAll`, `retAll_of_wrk`).
* The return jump (`pair_retL`): the guarantees written by the path (`PostOkC`).
-/

namespace LeanVM.Guest.CoreMode

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Memory
open LeanVM.Guest.Bridge (AlignCtx Zip ZOk fwdJ flowAtom isaFlowHint stmtsOf stmtsSub zok_stmts Pairs
  walk_ret_cons walk_callIf_cons)
open LeanVM.Guest.Check (getF)
open LeanVM.Prover.Exec (Hint St Ctx Fine Moves StepOk HintOk refMem maxCells runOp Mem gpow_inj
  Mem.get_of_written OpModed OnRef Agree)
open LeanVM.Guest.Mode (Names written_of_get written_mono names_inj opOfOff RefOk HintIn Holds entryAbs
  FrameSpec Out HintsAt ResAt RetAll RetHolds HW RW MonoVal BsVal BaseVal IdxVal stOf CodeOk TermAt LTF Back
  TermEntry)

@[expose] public section

variable {κ : ℕ}

/-! ## The shape -/

/-- Not a `JUMP`. -/
def noJump : OffsetInstruction → Bool
  | .jump .. => false
  | _ => true

/-- **A leaf loop helper's code**: no `JUMP` but its last two, the tail call's (its condition no
constant, through a next-frame cell, its pc cell not `0`) and the return (its condition a nonzero
constant). -/
noncomputable def loopCode (X : AlignCtx) (code : List OffsetInstruction) : Bool :=
  match code.reverse with
  | .jump oc' od' of' :: .jump oc od of :: pre =>
    Nat.beq od' 0 && Nat.beq of' 1 && !X.zeroAt oc' && X.nzAt oc' && !X.zeroAt oc && !X.selfAt of &&
      X.nextAt of && (match X.statOf of with
        | some (.fpg S) => !Nat.beq S 0 && decide (S < 2 ^ 30)
        | _ => false) && !Nat.beq od 0 && pre.all noJump
  | _ => false

/-- **The shape around a loop helper**: not `main`, frame cell `1` not its frame pointer, cell `0`
no pc, no `match` table, no table jump, callee or residual for its frame walk, not `main`'s frame;
its entry cells and self cell small, the header among the entry cells. -/
noncomputable def loopShapeOk (Cf : CFun) : Bool :=
  !Cf.X.main && !Cf.X.selfAt 1 && (Cf.X.pcAt 0).isNone && trieNil Cf.X.arms && tgtNone Cf.X.sites && trieNil Cf.frame.tgt &&
    trieNil Cf.frame.sigs && !Cf.frame.F.fpOne && trieNil Cf.frame.nzr &&
    Cf.frame.sig.entry.all (fun o ↦ decide (o + 1 < 2 ^ Exec.envDepth)) &&
    (match Cf.frame.sig.self with
      | some o => decide (o + 1 < 2 ^ Exec.envDepth) && decide (o < 2 ^ 28)
      | none => true) &&
    Cf.frame.sig.entry.contains 0 && Cf.frame.sig.entry.contains 1 &&
    decide (Cf.frame.entry + Cf.frame.len ≤ 2 ^ 30) && Mode.pcsIncr Cf.frame.hints

/-- **The kernel's checks of a loop helper on the core route**, and its ties to its mode certificate
`K`, as `CoreOk`'s. -/
structure LoopOk (K : Mode.Cert) (Cf : CFun) : Prop where
  heap : heapOkC Cf.pows Cf.sigOf Cf.fn Cf.H = true
  ders : Cf.H.ders = []
  gw : Cf.H.sig.gw = []
  nofa : noFA Cf.fn.body = true
  cs : Cf.cs = []
  body : loopB Cf.fn = true
  code : loopCode Cf.X K.code = true
  pair : pairOk Cf.X Cf.H Cf.frame.O Cf.frame.S Cf.fn.body K.code Cf.d = true
  frame : envOk Cf.frame = true ∧ armsOk Cf.frame = true ∧ FrameAcc Cf.frame K.code
  sig : sigOkL K.F.sig Cf.H.sig Cf.fn.params.length = true
  shape : loopShapeOk Cf = true
  sigE : K.E.sigs.get K.F.entry = some K.F.sig
  fsig : Cf.frame.sig = K.F.sig
  fentry : Cf.frame.entry = K.F.entry
  flen : Cf.frame.len = K.code.length
  xentry : Cf.X.entry = K.F.entry
  xlen : Cf.X.len = K.code.length
  dhints : Cf.d.2.2 = Cf.frame.hints
  hints : ∀ i < K.code.length, Mode.hintsAt Data.adviceHints (K.F.entry + i) =
    Mode.hintsAt Cf.frame.hints (K.F.entry + i)
  fetch : Exec.Fetches guestProgram K.F.entry K.code
  small : ∀ i (hi : i < K.code.length), SmallOps K.code[i]
  pows : Cf.pows.Ok
  fpows : Cf.frame.F.pows.Ok
  /-- Its contract is its mode signature's, and its callees'. -/
  hc : Cf.hc = false
  hcs : Cf.hcs = []

/-! ## The body and its path -/

theorem loopStmt_of {as : List Atom} {c : V} {f : String} {args : List V} :
    ∀ s ∈ stmtsOf (as.map Stmt.atom ++ [.callIf c f args, .ret []]), loopStmt s = true := fun s hs ↦ by
  rcases stmts_loop hs with ⟨a, rfl⟩ | rfl | rfl <;> rfl

/-! ## Facts about memories agreeing with the reference -/

theorem rd_of_get {img : MemoryImage κ} (hκ : κ ≤ 28) {m : Mem} (ha : Agree m (refMem img)) {fp o : ℕ}
    {u : E} (hg : m.get (fp + o) = some u) (hu : u ≠ 0) : Rd img fp o = some u := by
  have h1 := ha.get _ _ hg
  unfold refMem at h1
  split_ifs at h1 with hc
  · rw [Rd, ← pow_add, show (g : K) ^ (fp + o) = addressOfIndex (⟨fp + o, hc⟩ : Fin (2 ^ κ)) from rfl,
      MemoryImage.read_gpow (by omega)]
    exact congrArg some h1
  · exact absurd h1.symm hu

theorem refMem_eq_of_rd {img : MemoryImage κ} (hκ : κ ≤ 28) {a b : ℕ} (ha : a < 2 ^ 62) (hb : b < 2 ^ 62)
    (h : img.read (g ^ a) = img.read (g ^ b)) : refMem img a = refMem img b := by
  have hz : ∀ c, c < 2 ^ 62 → img.read (g ^ c) = none → refMem img c = 0 := fun c hc hn ↦ by
    unfold refMem
    split_ifs with hlt
    · exfalso
      have := (MemoryImage.read_eq_none_iff img).mp hn ⟨c, hlt⟩
      exact this rfl
    · rfl
  rcases hra : img.read (g ^ a) with _ | v
  · rw [hra] at h
    rw [hz a ha hra, hz b hb h.symm]
  · rw [hra] at h
    rw [(Prover.Exec.refRd_img hκ img a v ha hra).2, (Prover.Exec.refRd_img hκ img b v hb h.symm).2]

/-- **A frame agreeing with the reference, its entry cells written**, holds at its parameter cells the
words the reference does. -/
theorem parAt_of {img : MemoryImage κ} (hκ : κ ≤ 28) {G : Mode.Sig} {np : ℕ} {m : Mem} (ha : Agree m (refMem img))
    {fp : ℕ} (hfp : fp < maxCells) (hw : ∀ o ∈ G.entry, m.written (fp + o) = true) {ws : List E}
    (hws : ∀ b < np, Rd img fp (2 + b) = some (slotW ws b)) : ParAt G np (stOf m fp) ws := by
  intro o ho
  obtain ⟨h2, hn, h28, hent⟩ := parCell_spec ho
  obtain ⟨u, hu⟩ := Mem.get_of_written (hw o hent)
  show m.get (fp + o) = _
  rw [hu, rd_getA hκ ha hfp h28 (by have := hws (o - 2) hn; rwa [show 2 + (o - 2) = o by omega] at this) hu]

/-! ## The heap facts -/

/-- **A loop helper's calls give nothing beyond their writes**: its only call its own. -/
theorem loop_evM {K : Mode.Cert} {Cf : CFun} (hok : LoopOk K Cf) (rd : Reader) (σ : Val) (e : Ev) :
    EvM Cf.sigOf rd σ e := by
  have hs := sigL_of hok.sig
  cases e with
  | call f args rets =>
    refine ⟨fun k c hkc ↦ ?_, fun i m him ↦ ?_, fun p hp ↦ ?_⟩ <;> unfold CFun.sigOf at * <;> rw [hok.cs] at * <;>
      cases hf : (f == Cf.fn.name) <;> simp_all [hs.hretM, hs.hpostV, hs.hretEq]
  | _ => trivial

/-- **The heap facts of an honest path of a loop helper**, its parameter cells holding its words and
its termination fact holding: every event's needs written before it, its guarantees at return. -/
theorem loop_heap {K : Mode.Cert} {Cf : CFun} (hok : LoopOk K Cf) {σ : Val} {rd : Reader} {es : List Ev}
    {vs : List V} (hw : walk σ Cf.fn.body = .ret es vs) (hh : ∀ e ∈ es, e.Holds rd σ) (hR : ResF Cf.H σ) {s : St}
    (hP : ParAt K.F.sig Cf.fn.params.length s (Cf.fn.params.map σ)) (hT : ∀ p ∈ K.F.sig.term, LTF s p.1 p.2) :
    ReadsOkC Cf.sigOf Cf.H rd σ (Cf.fn.params.map σ) es ∧ PostOkW Cf.sigOf Cf.H rd σ (Cf.fn.params.map σ) es vs := by
  have hs := sigL_of hok.sig
  have hself : Cf.sigOf Cf.fn.name = Cf.H.sig := by simp [CFun.sigOf]
  have hM : ∀ e ∈ es, EvM Cf.sigOf rd σ e := fun e _ ↦ loop_evM hok rd σ e
  obtain ⟨hr, hp, -⟩ := heapOkC_sound hok.pows hok.heap hself hw hh hM (termAt_entryF hs hP hT)
    hR (derOk_nil hok.ders rd σ) (gwOk_nil hok.gw rd σ)
  exact ⟨hr, postOkW_of (noFAW hok.nofa hw) hp⟩

/-! ## The signature at a frame -/

/-- **The guarantees at return**, from their heap cells written, over a frame holding the parameters
whose termination fact holds. -/
theorem retAll_of_wrk {G : Mode.Sig} {h : HSig} {np : ℕ} (hs : SigL G h np) {m : Mem} {fp : ℕ} {ws : List E}
    (hP : ParAt G np (stOf m fp) ws) (hT : ∀ p ∈ G.term, LTF (stOf m fp) p.1 p.2)
    (hpost : ∀ c ∈ h.post, WrK m (c.addrW (slotW ws)))
    (hpostR : ∀ r ∈ h.postR, ∀ x, r.Set (slotW ws) x → WrK m x) : RetAll m fp G := by
  have hRW : ∀ r ∈ G.postR ++ G.postL, RW (stOf m fp) r := fun r hr ↦ by
    obtain ⟨q, hq, hrq⟩ := (mapM_mem hs.postR).2 r hr
    have hk := hs.kpostR r hr
    simp only [rngK, Bool.and_eq_true] at hk
    exact slot_rwT hP hrq (idxK_val hT hk.1) (idxK_val hT hk.2) (hpostR q hq)
  refine ⟨⟨fun o ho ↦ (by rw [hs.ret] at ho; cases ho), fun m0 hm0 ↦ ?_, fun r hr ↦ hRW r (List.mem_append_left _ hr),
    fun q hq ↦ (by rw [hs.postP] at hq; cases hq), fun p hp ↦ (by rw [hs.retV] at hp; cases hp),
    fun p hp ↦ (by rw [hs.postT] at hp; cases hp), fun q hq ↦ (by rw [hs.postC] at hq; cases hq)⟩,
    fun r hr ↦ hRW r (List.mem_append_right _ hr), fun q hq ↦ (by rw [hs.postLP] at hq; cases hq)⟩
  obtain ⟨c, hc, hmc⟩ := (mapM_mem hs.post).2 m0 hm0
  exact slot_hwT hP hmc (hpost c hc)

/-- **What a frame guarantees at return is its heap signature's guarantees written**, over a frame
holding the parameters. -/
theorem postSet_of_retAll {G : Mode.Sig} {h : HSig} {np : ℕ} (hs : SigL G h np) {m : Mem} {fp : ℕ} {ws : List E}
    (hP : ParAt G np (stOf m fp) ws) (hR : RetAll m fp G) {rd : Reader} :
    ∀ x, PostSet rd h ws x → WrK m x := by
  rintro x ((⟨c, hc, rfl⟩ | ⟨r, hr, hx⟩) | (⟨p, hp, -⟩ | ⟨p, hp, -⟩))
  · obtain ⟨m0, hm0, hmc⟩ := (mapM_mem hs.post).1 c hc
    exact hw_slotT hP hmc (hR.1.2.1 m0 hm0)
  · obtain ⟨r0, hr0, hrq⟩ := (mapM_mem hs.postR).1 r hr
    have hRW : RW (stOf m fp) r0 := by
      rcases List.mem_append.mp hr0 with h1 | h1
      · exact hR.1.2.2.1 r0 h1
      · exact hR.2.1 r0 h1
    exact rw_slotT hP hrq hRW x hx
  · rw [hs.hpostP] at hp; cases hp
  · rw [hs.hpostPR] at hp; cases hp

/-- **The preconditions at entry are the heap signature's written**, over a frame holding the
parameters. -/
theorem preSet_of_entry {G : Mode.Sig} {h : HSig} {np : ℕ} (hs : SigL G h np) {s : St} {ws : List E}
    (hP : ParAt G np s ws) (hpre : ∀ m ∈ G.pre, HW s m) (hpreR : ∀ r ∈ G.preR, RW s r) {rd : Reader} :
    ∀ x, PreSet rd h ws x → WrK s.mem x := by
  rintro x ((⟨c, hc, rfl⟩ | ⟨r, hr, hx⟩) | (⟨p, hp, -⟩ | ⟨p, hp, -⟩))
  · obtain ⟨m0, hm0, hmc⟩ := (mapM_mem hs.pre).1 c hc
    exact hw_slotT hP hmc (hpre m0 hm0)
  · obtain ⟨r0, hr0, hrq⟩ := (mapM_mem hs.preR).1 r hr
    exact rw_slotT hP hrq (hpreR r0 hr0) x hx
  · rw [hs.hpreP] at hp; cases hp
  · rw [hs.hprePR] at hp; cases hp

/-- **The entry facts are the heap signature's preconditions**, written, over a frame holding the
parameters whose termination fact holds. -/
theorem entry_of_pre {G : Mode.Sig} {h : HSig} {np : ℕ} (hs : SigL G h np) {s : St} {ws : List E}
    (hP : ParAt G np s ws) (hT : ∀ p ∈ G.term, LTF s p.1 p.2) {W : K → Prop} (hW : ∀ x, W x → WrK s.mem x)
    (hpre : SigOk W h.pre h.preR ws) : (∀ m ∈ G.pre, HW s m) ∧ ∀ r ∈ G.preR, RW s r := by
  refine ⟨fun m hm ↦ ?_, fun r hr ↦ ?_⟩
  · obtain ⟨c, hc, hmc⟩ := (mapM_mem hs.pre).2 m hm
    exact slot_hwT hP hmc (hW _ (hpre.1 c hc))
  · obtain ⟨q, hq, hrq⟩ := (mapM_mem hs.preR).2 r hr
    have hk := hs.kpreR r hr
    simp only [rngK, Bool.and_eq_true] at hk
    exact slot_rwT hP hrq (idxK_val hT hk.1) (idxK_val hT hk.2) fun x hx ↦ hW x (hpre.2 q hq x hx)

/-! ## The entry abstraction -/

theorem monoVal_own0 {s : St} {u : E} (h : MonoVal s (Mode.Mono.own 0) u) : u = ofK (g ^ s.fp) := by
  obtain ⟨w, hw, rfl⟩ := h
  simp only [Mode.Mono.own, BsVal] at hw
  simp [hw, Mode.Mono.own]

/-- **What the entry abstraction holds**: the entry cells written, the preconditions, the self cell
holding its frame's address. -/
theorem entry_facts {E0 : Mode.Env} {G : Mode.Sig} (hent : ∀ o ∈ G.entry, o + 1 < 2 ^ Exec.envDepth)
    (hso : ∀ o, G.self = some o → o + 1 < 2 ^ Exec.envDepth) {s : St} (h : Mode.Holds s (entryAbs E0 G)) :
    (∀ o ∈ G.entry, s.mem.written (s.fp + o) = true) ∧ (∀ m ∈ G.pre, HW s m) ∧ (∀ r ∈ G.preR, RW s r) ∧
      ∀ o, G.self = some o → s.mem.written (s.fp + o) = true ∧ s.mem.get (s.fp + o) = some (ofK (g ^ s.fp)) := by
  unfold entryAbs at h
  rcases hs : G.self with _ | o
  · rw [hs] at h
    exact ⟨fun o ho ↦ h.w o (foldlT_mem _ _ hent ho), h.h, fun r hr ↦ h.r r (List.mem_cons_of_mem _ hr),
      fun o ho ↦ by cases ho⟩
  · rw [hs] at h
    have ho1 := hso o hs
    simp only [Mode.Abs.addW, Mode.Abs.addV, Mode.Abs.addNz] at h
    rw [trieNil_get rfl] at h
    simp only at h
    refine ⟨fun o' ho' ↦ h.w o' ?_, h.h, fun r hr ↦ h.r r (List.mem_cons_of_mem _ hr), fun o' ho' ↦ ?_⟩
    · show (Exec.Trie.set () Exec.envDepth (Mode.foldlT .nil G.entry) o).get o' = some ()
      rw [trie_get_set_eq () _ _ o o' ho1]
      split_ifs
      · rfl
      · exact foldlT_mem _ _ hent ho'
    · cases ho'
      refine ⟨h.w o ?_, ?_⟩
      · show (Exec.Trie.set () Exec.envDepth (Mode.foldlT .nil G.entry) o).get o = some ()
        rw [trie_get_set_eq () _ _ o o ho1]
        simp
      · obtain ⟨u, hu, hv⟩ := h.v o (.m (Mode.Mono.own 0)) (by
          show (Exec.Trie.set (Mode.Val.m (Mode.Mono.own 0)) Exec.envDepth .nil o).get o = _
          rw [trie_get_set_eq _ _ _ o o ho1]
          simp)
        rw [hu, monoVal_own0 hv]

/-- **The entry abstraction holds** of a frame with its entry cells written, its preconditions, the
jump table, its termination facts, its self cell holding its frame's address. -/
theorem holds_entry {E0 : Mode.Env} {G : Mode.Sig}
    (hpP : G.preP = []) {s : St} (hw : ∀ o ∈ G.entry, s.mem.written (s.fp + o) = true)
    (hpre : ∀ m ∈ G.pre, HW s m) (hjt : RW s (Mode.jtRng E0)) (hpreR : ∀ r ∈ G.preR, RW s r)
    (hT : ∀ p ∈ G.term, LTF s p.1 p.2)
    (hself : ∀ o, G.self = some o → s.mem.written (s.fp + o) = true ∧ s.mem.get (s.fp + o) = some (ofK (g ^ s.fp))) :
    Mode.Holds s (entryAbs E0 G) := by
  have h0 : Mode.Holds s ⟨Mode.foldlT .nil G.entry, .nil, .nil, [], G.pre, Mode.jtRng E0 :: G.preR, G.term, [], .nil,
      G.preP, []⟩ :=
    ⟨fun o ho ↦ hw o (foldlT_nil_get ho), fun o x hx ↦ (by rw [trieNil_get rfl] at hx; cases hx),
      fun o hx ↦ (by rw [trieNil_get rfl] at hx; cases hx), fun p hp ↦ (by cases hp), hpre,
      fun r hr ↦ (List.mem_cons.mp hr).elim (fun h ↦ h ▸ hjt) (hpreR r), hT, fun p hp ↦ (by cases hp),
      fun c a b hx ↦ (by rw [trieNil_get rfl] at hx; cases hx), fun q hq ↦ (by rw [hpP] at hq; cases hq),
      fun q hq ↦ (by cases hq)⟩
  unfold entryAbs
  rcases hs : G.self with _ | o
  · exact h0
  · obtain ⟨hwo, hgo⟩ := hself o hs
    refine ((h0.addW hwo).addV ⟨_, hgo, ?_⟩).addNz ⟨_, hgo, Mode.ofK_gpow_ne_zero _⟩
    exact ⟨1, rfl, by simp [Mode.Mono.own]⟩

/-! ## The code -/

theorem loopCode_spec {X : AlignCtx} {code : List OffsetInstruction} (h : loopCode X code = true) :
    ∃ pre oc od of oc', code = pre ++ [.jump oc od of, .jump oc' 0 1] ∧ (∀ ins ∈ pre, noJump ins = true) ∧
      X.zeroAt oc' = false ∧ X.nzAt oc' = true ∧ X.zeroAt oc = false ∧ X.selfAt of = false ∧ X.nextAt of = true ∧
      (∃ S, X.statOf of = some (.fpg S) ∧ S ≠ 0 ∧ S < 2 ^ 30) ∧ od ≠ 0 := by
  unfold loopCode at h
  split at h
  · rename_i oc' od' of' oc od of pre hrev
    simp only [Bool.and_eq_true, Nat.beq_eq, Bool.not_eq_true', List.all_eq_true] at h
    obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨rfl, rfl⟩, h1⟩, h2⟩, h3⟩, h4⟩, h5⟩, hS⟩, h7⟩, h8⟩ := h
    refine ⟨pre.reverse, oc, od, of, oc', ?_, fun ins hi ↦ h8 ins (List.mem_reverse.mp hi), h1, h2, h3, h4, h5,
      ?_, fun h0 ↦ by simp [h0] at h7⟩
    · rw [← List.reverse_reverse code, hrev]
      simp
    · split at hS
      · rename_i S hso
        simp only [Bool.and_eq_true, Bool.not_eq_true', decide_eq_true_eq] at hS
        exact ⟨S, hso, fun h0 ↦ by simp [h0] at hS, hS.2⟩
      · cases hS
  · cases h

/-- **A `JUMP` of a loop helper's code** is its tail call's, second to last, or its return, last. -/
theorem loopCode_jump {code pre : List OffsetInstruction} {oc od of oc' : ℕ}
    (hc : code = pre ++ [.jump oc od of, .jump oc' 0 1]) (hpre : ∀ ins ∈ pre, noJump ins = true) {i a b c : ℕ}
    (h : code[i]? = some (.jump a b c)) :
    (i = pre.length ∧ a = oc ∧ b = od ∧ c = of) ∨ (i = pre.length + 1 ∧ a = oc' ∧ b = 0 ∧ c = 1) := by
  subst hc
  rcases lt_trichotomy i pre.length with hi | rfl | hi
  · rw [List.getElem?_append_left hi] at h
    exact absurd (hpre _ (List.mem_of_getElem? h)) (by simp [noJump])
  · simp only [List.getElem?_append_right le_rfl, Nat.sub_self, List.getElem?_cons_zero, Option.some.injEq,
      OffsetInstruction.jump.injEq] at h
    exact Or.inl ⟨rfl, h.1.symm, h.2.1.symm, h.2.2.symm⟩
  · rw [List.getElem?_append_right (by omega)] at h
    rcases hk : i - pre.length with _ | _ | k
    · omega
    · rw [hk] at h
      simp only [List.getElem?_cons_succ, List.getElem?_cons_zero, Option.some.injEq,
        OffsetInstruction.jump.injEq] at h
      exact Or.inr ⟨by omega, h.1.symm, h.2.1.symm, h.2.2.symm⟩
    · rw [hk] at h
      simp at h

/-! ## The next frame's header -/

theorem retNil_eq {l : List Stmt} (h : Bridge.retNil l = true) : l = [.ret []] := by
  unfold Bridge.retNil at h
  split at h
  · rfl
  · cases h

/-- **Two cells the reference reads alike**, both written in a memory agreeing with it, hold one
word. -/
theorem hdr_copy {img : MemoryImage κ} (hκ : κ ≤ 28) {m : Mem} (ha : Agree m (refMem img)) {a b o : ℕ}
    (hab : Rd img b o = Rd img a o) (hwa : m.written (a + o) = true) (hwb : m.written (b + o) = true)
    (hla : a + o < 2 ^ 62) (hlb : b + o < 2 ^ 62) : ∃ u, m.get (a + o) = some u ∧ m.get (b + o) = some u := by
  obtain ⟨u, hu⟩ := Mem.get_of_written hwa
  obtain ⟨u', hu'⟩ := Mem.get_of_written hwb
  refine ⟨u, hu, ?_⟩
  rw [hu', ← ha.get _ _ hu', ← ha.get _ _ hu]
  exact congrArg some (refMem_eq_of_rd hκ hlb hla (by simpa [Rd, addressOfIndex, pow_add] using hab))

theorem calls_atoms (as : List Atom) : calls (as.map Ev.atom) = [] := by
  induction as with
  | nil => rfl
  | cons a as ih => simp [calls, Ev.call?]

/-- **A loop's tail call taken**, into frame `s.fp + S` of the honest tree: the next iteration's entry
facts (the tail call's preconditions), its header this frame's, and this iteration returning what the
next one does (its guarantees, the tail call's being the next one's). -/
theorem tail_next {K : Mode.Cert} {Cf : CFun} (hok : LoopOk K Cf) {img : MemoryImage κ} (hκ : κ ≤ 28)
    {s s1 s' : St} (hfp0 : s.fp < maxCells) (hfp1 : s1.fp = s.fp) (hle1 : s.mem ≤ s1.mem)
    (hf' : Fine (refMem img) s') (hle' : s1.mem ≤ s'.mem) {S : ℕ} (hfpS : s'.fp = s.fp + S) (hS : S < 2 ^ 30)
    (hpc' : s'.pc = K.F.entry) (hentry : EntryFr img Cf.frame.sig s') (hr0 : Rd img s'.fp 0 = Rd img s1.fp 0)
    (hr1 : Rd img s'.fp 1 = Rd img s1.fp 1) (hTE : TermEntry K s') (hjt : RW s' (Mode.jtRng K.E))
    (hwE : ∀ o ∈ K.F.sig.entry, s.mem.written (s.fp + o) = true)
    (hso : ∀ o, K.F.sig.self = some o → o < 2 ^ 28)
    (hent0 : 0 ∈ Cf.frame.sig.entry) (hent1 : 1 ∈ Cf.frame.sig.entry)
    {σ0 : Val} {rd : Reader} {pre es evs : List Ev} {cs : List Atom} {c : V} {args : List V}
    (hb : walk σ0 Cf.fn.body = .ret (pre ++ es) []) (hh0 : ∀ e ∈ pre ++ es, e.Holds rd σ0) (hR0 : ResF Cf.H σ0)
    (heq : es = evs ++ Ev.inK c :: Ev.call Cf.fn.name args [] :: cs.map Ev.atom)
    (hrw0 : ReadsOkC Cf.sigOf Cf.H rd σ0 (Cf.fn.params.map σ0) (pre ++ es))
    (hWc : ∀ x, WrittenC Cf.sigOf Cf.H rd σ0 (Cf.fn.params.map σ0) (pre ++ evs) x → WrK s'.mem x)
    (hnargs : ∀ k (hk : k < args.length), Rd img (s.fp + S) (2 + k) = some (σ0 args[k]))
    (hargs : args.length = Cf.fn.params.length)
    (hP0 : ParAt K.F.sig Cf.fn.params.length (stOf s.mem s.fp) (Cf.fn.params.map σ0))
    (hT : TermAt s.mem s.fp K.F.sig) (hcs : ∀ a ∈ cs, stopL a = false) :
    s'.pc = K.F.entry ∧ (∀ o ∈ K.F.sig.entry, s'.mem.written (s'.fp + o) = true) ∧
      (∀ o < 2, ∃ u, s'.mem.get (s1.fp + o) = some u ∧ s'.mem.get (s'.fp + o) = some u) ∧
      Mode.BackM s'.mem K.F.sig s1.fp s'.fp ∧ Mode.Holds s' (entryAbs K.E K.F.sig) := by
  have hs := sigL_of hok.sig
  have hle : s.mem ≤ s'.mem := Mem.le_trans hle1 hle'
  have hwN : ∀ o ∈ K.F.sig.entry, s'.mem.written (s'.fp + o) = true := fun o ho ↦ hentry.w o (hok.fsig ▸ ho)
  have hTN : ∀ p ∈ K.F.sig.term, LTF (stOf s'.mem s'.fp) p.1 p.2 :=
    hTE K.F.sig (by rw [hpc']; exact hok.sigE) hwN
  have hPN : ParAt K.F.sig Cf.fn.params.length (stOf s'.mem s'.fp) (args.map σ0) :=
    parAt_of hκ hf'.agree hf'.fp hwN fun b hb' ↦ by
      have hba : b < args.length := by rw [hargs]; exact hb'
      rw [hfpS, slotW_get (by simpa using hba)]
      simpa using hnargs b hba
  have hsigf : Cf.sigOf Cf.fn.name = Cf.H.sig := by simp [CFun.sigOf]
  have hb0 : s.fp < 2 ^ 28 := by unfold maxCells at hfp0; omega
  refine ⟨hpc', hwN, fun o ho ↦ ?_, ?_, ?_⟩
  · -- the header copied
    have hwo : ∀ o ∈ K.F.sig.entry, s'.mem.written (s1.fp + o) = true := fun o ho ↦ by
      rw [hfp1]; exact written_mono hle (hwE o ho)
    interval_cases o
    · exact hdr_copy hκ hf'.agree hr0 (hwo 0 (hok.fsig ▸ hent0)) (hwN 0 (hok.fsig ▸ hent0)) (by omega)
        (by rw [hfpS]; omega)
    · exact hdr_copy hκ hf'.agree hr1 (hwo 1 (hok.fsig ▸ hent1)) (hwN 1 (hok.fsig ▸ hent1)) (by omega)
        (by rw [hfpS]; omega)
  · -- this iteration returns what the next one does
    intro m' hm' _ _ hR
    have hPN' : ParAt K.F.sig Cf.fn.params.length (stOf m' s'.fp) (args.map σ0) :=
      hPN.mono (s := stOf s'.mem s'.fp) (s' := stOf m' s'.fp) hm' rfl
    have hnext := postSet_of_retAll (rd := rd) hs hPN' hR
    obtain ⟨-, hposts⟩ := loop_heap hok hb hh0 hR0 hP0 hT
    simp only [PostOkW, List.map_nil, List.append_nil] at hposts
    have hWall : ∀ x, WrittenC Cf.sigOf Cf.H rd σ0 (Cf.fn.params.map σ0) (pre ++ es) x → WrK m' x := by
      intro x hx
      rw [heq, ← List.append_assoc] at hx
      rcases writtenC_append hx with h | ⟨e, he, hwe⟩
      · exact (hWc x h).mono hm'
      · rcases List.mem_cons.mp he with rfl | he
        · cases hwe
        rcases List.mem_cons.mp he with rfl | he
        · simp only [EvW, List.append_nil] at hwe
          rw [hsigf] at hwe
          exact hnext x hwe
        · obtain ⟨a, ha, rfl⟩ := List.mem_map.mp he
          exact absurd hwe (no_writes_of_stopL (hcs a ha))
    have hP1 : ParAt K.F.sig Cf.fn.params.length (stOf m' s1.fp) (Cf.fn.params.map σ0) :=
      hP0.mono (s := stOf s.mem s.fp) (s' := stOf m' s1.fp) (Mem.le_trans hle hm') hfp1
    exact retAll_of_wrk hs hP1 (fun p hp ↦ by rw [hfp1]; exact Mode.LTF.mem (Mem.le_trans hle hm') (hT p hp))
      (fun c hc ↦ hWall _ (hposts.1.1 c hc)) (fun r hr x hx ↦ hWall x (hposts.1.2 r hr x hx))
  · -- the next iteration's entry facts: the tail call's preconditions
    have hreq := hrw0 (pre ++ evs ++ [Ev.inK c]) (.call Cf.fn.name args []) (cs.map Ev.atom)
      (by rw [heq]; simp)
    replace hreq := callReq_pre hok.ders hreq
    have hreqS := hreq.2.1
    have hga : gargsW Cf.H σ0 Cf.fn.name args = [] := by
      rw [← List.length_eq_zero_iff]
      simp only [gargsW, List.length_map, hreq.1, hsigf, hs.hghost]
    rw [hsigf, hga, List.append_nil] at hreqS
    obtain ⟨hpreN, hpreRN⟩ := entry_of_pre hs hPN hTN
      (W := WrittenC Cf.sigOf Cf.H rd σ0 (Cf.fn.params.map σ0) (pre ++ evs ++ [Ev.inK c]))
      (fun x hx ↦ hWc x (writtenC_noAtom (fun a h ↦ by cases h) (fun f a r h ↦ by cases h) hx)) hreqS
    refine holds_entry hs.preP hwN
      (fun m hm' ↦ Mode.HW.mono (s := stOf s'.mem s'.fp) (s' := s') (Mem.le_refl _) rfl (hpreN m hm'))
      hjt (fun r hr ↦ Mode.RW.mono (s := stOf s'.mem s'.fp) (s' := s') (Mem.le_refl _) rfl (hpreRN r hr))
      (fun p hp ↦ Mode.LTF.mono (s := stOf s'.mem s'.fp) (s' := s') (Mem.le_refl _) rfl (hTN p hp))
      (fun o ho ↦ ?_)
    obtain ⟨hwo, hro⟩ := hentry.self o (hok.fsig ▸ ho)
    obtain ⟨u, hu⟩ := Mem.get_of_written hwo
    exact ⟨hwo, by rw [hu, rd_get hκ hf' (hso o ho) hro hu]⟩

/-! ## The frame interface -/

/-- **A leaf loop helper on the core route meets the frame interface**, for `CoreAt`. -/
theorem frameSpec_loop {K : Mode.Cert} {Cf : CFun} (hok : LoopOk K Cf) {adv : Prover.Exec.Advice} {C : Ctx}
    (hC : Prover.Exec.Ctx.of guestProgram adv = .ok C) (ha : adv.hints = Data.adviceHints) (hK : CodeOk C K)
    {img : MemoryImage κ} {Y : St → Prop} (hκ : κ ≤ 28) (hY : ∀ s, Y s → ∃ n, OnRef guestProgram img n s)
    (hH : CoreHon img Y K Cf) {Ct : Mode.Cts} (hCt : Mode.ModeCts Ct K) :
    FrameSpec C (refMem img) Y Ct K (CoreAt img Cf K.code) := by
  obtain ⟨as0, c0, args0, hbody, hargs⟩ := loopB_spec hok.body
  have hst : ∀ s ∈ stmtsOf Cf.fn.body, loopStmt s = true := by rw [hbody]; exact loopStmt_of
  obtain ⟨cpre, toc, tod, tof, roc, hcode, hcpre, hrz, hrnz, htz, htsf, htnx, ⟨S, hstatS, hS0, hS30⟩, htod⟩ :=
    loopCode_spec hok.code
  have hsh := hok.shape
  simp only [loopShapeOk, Bool.and_eq_true, Bool.not_eq_true', decide_eq_true_eq, List.all_eq_true,
    Option.isNone_iff_eq_none, List.contains_iff_mem] at hsh
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hmainX, hself1⟩, hpc0⟩, harms0⟩, hsites0⟩, htgt0⟩, hsigs0⟩, hfp1⟩, hnzr0⟩, hent⟩, hselfS⟩, hent0⟩,
    hent1⟩, hend⟩, hincr⟩ := hsh
  have hs := sigL_of hok.sig
  obtain ⟨henv, harm, hacc⟩ := hok.frame
  have hent' : ∀ x ∈ K.F.sig.entry, x + 1 < 2 ^ Exec.envDepth := hok.fsig ▸ hent
  have hso : ∀ o, K.F.sig.self = some o → o + 1 < 2 ^ Exec.envDepth ∧ o < 2 ^ 28 := fun o ho ↦ by
    rw [← hok.fsig] at ho
    rw [ho] at hselfS
    simpa using hselfS
  have hpar : Cf.fn.params = (List.range Cf.fn.params.length).map V.n := by
    have h := hok.heap
    unfold heapOkC at h
    simp only [Bool.and_eq_true] at h
    rw [List.range_eq_range']
    exact paramsN_eq _ 0 h.1.1.1.1.1
  set np := Cf.fn.params.length with hnp
  have hws0 : ∀ {fp : ℕ} {σ : Val}, HonF img Cf fp σ →
      ∀ b < np, Rd img fp (2 + b) = some (slotW (Cf.fn.params.map σ) b) := by
    intro fp σ hσ b hb
    rw [slotW_params' hpar hb]
    exact hσ.par b hb
  have hlen : Cf.frame.len = K.code.length := hok.flen
  have hcl : K.code.length = cpre.length + 2 := by rw [hcode]; simp
  refine ⟨fun hle hfp h ↦ h.mono hle hfp, ?_, ?_⟩
  · -- the entry
    intro s hH0 hs0
    rw [Mode.preAt_none hCt.1] at hH0
    obtain ⟨hw, hpre, hpreR, hself⟩ := entry_facts hent' (fun o ho ↦ (hso o ho).1) hH0
    refine coreAt_of (by rw [CFun.xc_of hok.hc, hok.fsig]; exact expW_entry hκ hs0.agree hH0)
      ⟨atF_mono (s := s) (Mem.le_refl _) rfl (atF_entry henv ⟨fun o ho ↦ hw o (hok.fsig ▸ ho),
      fun o hso' ↦ ?_⟩), fun o ho ↦ hw o (hok.fsig ▸ ho), fun σ hσ ↦ ?_⟩
    · rw [hok.fsig] at hso'
      obtain ⟨hwo, hgo⟩ := hself o hso'
      exact ⟨hwo, rd_of_get hκ hs0.agree hgo (Mode.ofK_gpow_ne_zero _)⟩
    obtain ⟨es, vs, -, hwk, -⟩ := hσ.path
    refine ⟨Cf.fn.body, [], es, vs, img.read, rfl, pairAt_zero hok.pair, by simpa using hwk, hwk,
      by simpa using hσ.holds _ _ hwk, fun e _ ↦ loop_evM hok _ _ e,
      fun y hy ↦ ?_⟩
    have hP := parAt_of (G := K.F.sig) hκ hs0.agree hs0.fp hw (hws0 hσ)
    rcases hy with hy | ⟨e, he, -⟩
    · rw [ownG_zero hs.hghost, List.append_nil] at hy
      exact preSet_of_entry hs hP (fun m hm ↦ Mode.HW.mono (s := s) (s' := stOf s.mem s.fp) (Mem.le_refl _) rfl
        (hpre m hm)) (fun r hr ↦ Mode.RW.mono (s := s) (s' := stOf s.mem s.fp) (Mem.le_refl _) rfl (hpreR r hr)) y hy
    · cases he
  · -- a step
    intro s i hi hpc hat hs0 hYs hsz _ henvK _ hjtR hT _ _ hh _ href Inv k
    obtain ⟨hAtF0, hentw, hheap⟩ := hat.2 s.mem (Mem.le_refl _) hs0.agree
    have hxw := hat.1
    have hAtF : AtF img Cf.frame K.code i s := atF_mono (s := Mode.stOf s.mem s.fp) (Mem.le_refl _) rfl hAtF0
    obtain ⟨σ0, hσ0⟩ := hH s i hYs hi hpc
    obtain ⟨n, hon⟩ := hY s hYs
    have hpcF : s.pc = Cf.frame.entry + i := by rw [hok.fentry]; exact hpc
    have hsize := (Prover.Exec.ctx_of_spec hC).1
    have hhintsF : ∀ j < K.code.length, (C.hints[Cf.frame.entry + j]?).getD [] =
        Mode.hintsAt Cf.frame.hints (Cf.frame.entry + j) := by
      intro j hj
      have hpcj : K.F.entry + j < 2 ^ guestProgram.logSize := hsize ▸ Mode.code_pc hK hj
      rw [hok.fentry, Mode.ctx_hints hC (ha ▸ Mode.adviceHints_incr) hpcj, ha, hok.hints j hj]
    have hhd : ∀ j, (Cf.d.2.2.lookup (Cf.X.entry + j)).getD [] = Mode.hintsAt Cf.frame.hints (Cf.frame.entry + j) :=
      fun j ↦ by rw [lookupD_hintsAt, hok.dhints, hok.xentry, hok.fentry]
    have hwE : ∀ o ∈ K.F.sig.entry, s.mem.written (s.fp + o) = true := fun o ho ↦ hentw o (hok.fsig ▸ ho)
    have hPs : ∀ {σ : Val}, HonF img Cf s.fp σ → ParAt K.F.sig np (stOf s.mem s.fp) (Cf.fn.params.map σ) :=
      fun hσ ↦ parAt_of hκ hs0.agree hs0.fp hwE (hws0 hσ)
    have hrwOf : ∀ σ pre es vs rd, HonF img Cf s.fp σ → walk σ Cf.fn.body = .ret (pre ++ es) vs →
        (∀ e ∈ pre ++ es, e.Holds rd σ) → ReadsAt Cf.sigOf Cf.H rd σ (Cf.fn.params.map σ) pre es :=
      fun σ pre es vs rd hσ hb hh0 ↦ readsAt_of_C (loop_heap hok hb hh0 (hσ.res hxw) (hPs hσ) hT).1
    have he1 : ∀ s1, (Mode.hintsAt Cf.frame.hints (Cf.frame.entry + i)).foldlM (Prover.Exec.runHint C) s = .ok s1 →
        ((C.hints[s.pc]?).getD []).foldlM (Prover.Exec.runHint C) s = .ok s1 := fun s1 e1 ↦ by
      rw [hpcF, hhintsF i hi]; exact e1
    have hsm : ∀ oc od of, K.code[i]? = some (.jump oc od of) → oc < 2 ^ 28 ∧ od < 2 ^ 28 ∧ of < 2 ^ 28 :=
      fun oc od of hci ↦ by
        have h := hok.small i hi
        rw [List.getElem?_eq_getElem hi, Option.some.injEq] at hci
        rw [hci] at h
        exact h
    have hselfs : ∀ {σ : Val}, HonF img Cf s.fp σ → ∀ {pre es : List Ev} {vs : List V},
        walk σ Cf.fn.body = .ret (pre ++ es) vs →
        pre ++ es = as0.map Ev.atom ++ [.inK c0, if σ c0 = 0 then .skip Cf.fn.name args0 else .call Cf.fn.name args0 []] ∧
          vs = [] := by
      intro σ _ pre es vs hb
      rw [hbody, walk_loop, Out.ret.injEq] at hb
      exact ⟨hb.1.symm, hb.2.symm⟩
    refine frame_step (prog := guestProgram) (k := n - s.steps) hκ harm hacc hok.fpows hend hsz
      (fun j hj ↦ by rw [hok.fentry]; exact hK.ops j hj) hhintsF (hok.fentry ▸ hok.fetch) hok.small hi hpcF hAtF hs0
      hon.2 (fun h ↦ absurd h (by simp [hfp1]))
      (fun pre h post hp s1 e hm hin ↦ hh pre h post (by rw [hpcF, hhintsF i hi]; exact hp) s1 e hm hin)
      (fun o ho ↦ by simp [trieNil_get hnzr0] at ho) ?_ ?_
      (fun s1 hm ↦ refOk_fp hm.fp href) ?_ ?_
    · -- the oracle's heap cell, written
      intro hOi s1 e1 hm
      have main : ∀ a o c, K.code[i] = .deref a o c .cell → HeapRd s1 (.deref a o c .cell) := by
        intro a o c hci
        obtain ⟨pos, pre, es, vs, rd, hrd, hpos, hb, hwp, hh0, -, hW⟩ := hheap σ0 hσ0
        have hj : jtd Cf.X a o c = false := jtd_none harms0 hsites0 a o c
        obtain ⟨as, dv, pv, off, hpairs, hcell, -, hmem, hwr⟩ := pair_readC hok.pair hpos
          (by rw [List.getElem?_eq_getElem hi, hci]) (by rw [← has_hasP]; exact hOi) hj hwp
          (hrwOf σ0 pre es vs rd hσ0 hb hh0)
        have hwk : WrK s1.mem (cellAt σ0 pv off) := by
          rcases hwr with h | ⟨a', ha', hfa', hma, hwa⟩
          · exact (hW _ h).mono hm.le
          · rw [hhd i] at hpairs
            exact flow_wrk hκ e1 hs0 hm hpairs ha' hfa'
              (fun q hq ↦ hσ0.ptr _ _ hb a' q (List.mem_append_right _ hma) hq) hwa
        simp only [cellsAt, Bool.and_eq_true, Nat.beq_eq] at hcell
        obtain ⟨⟨hloc, hoff⟩, -⟩ := hcell
        intro p x hp hx
        have hsm := hok.small i hi
        rw [hci] at hsm
        obtain ⟨sa, -, -⟩ := hsm
        have hrd : Rd img s1.fp a = some (σ0 pv) := by
          rw [hm.fp, ← hloc]; exact hσ0.ptr _ _ hb (.load dv pv off) pv (List.mem_append_right _ hmem) rfl
        have hpv : p = σ0 pv := rd_get hκ hm.fine sa hrd hp
        obtain ⟨x', hx', hlt', hw'⟩ := hwk
        have h1 := hx.1
        rw [limb0_mul_ofK, hpv, ← hoff] at h1
        have hxx : x = x' := gpow_inj (lt_maxCells_63 hx.2) (lt_maxCells_63 hlt') (h1.symm.trans hx')
        rw [hxx]
        exact hw'
      generalize hci : K.code[i] = ins
      cases ins with
      | deref a o c mode =>
        cases mode with
        | cell => exact main a o c hci
        | pc => trivial
        | fp => trivial
      | _ => trivial
    · -- no table jump
      intro c d f hci cv dv hcv hne hdv pc hpcl hdl kk hk
      rw [trieNil_get htgt0] at hk
      cases hk
    · -- falling through
      intro s1 s' e1 hm hmo e' hpc' hfp' hf' hle' hat' hstw hc0
      have hle : s.mem ≤ s'.mem := Mem.le_trans hm.le hle'
      have hi1 : i + 1 < K.code.length := by
        by_contra hn
        obtain ⟨cur, pend, h0, hh0⟩ := hat'
        obtain ⟨rfl, rfl⟩ := preF_end hacc (by omega) h0
        rcases hh0 with ⟨A, hA, -⟩ | ⟨g', hg', -⟩
        · cases hA
        · cases hg'
      refine k s1 s' (he1 s1 e1) hm hmo e' hf' hle' (.move (i + 1) (hfp'.trans hm.fp.symm) hi1
        (by rw [hpc', hpc]; omega) (coreAt_of (by rw [hfp']; exact hxw) ⟨atF_mono (s := s') (Mem.le_refl _) rfl hat',
          fun o ho ↦ by rw [hfp']; exact written_mono hle (hentw o ho), fun σ hσ ↦ ?_⟩))
      rw [hfp'] at hσ
      obtain ⟨pos, pre, es, vs, rd, hrd, hpos, hb, hwp, hh0, -, hW⟩ := hheap σ hσ
      by_cases hj : ∃ oc od of, K.code[i]? = some (.jump oc od of)
      · obtain ⟨oc, od, of, hci⟩ := hj
        rcases loopCode_jump hcode hcpre hci with ⟨-, rfl, rfl, rfl⟩ | ⟨-, rfl, rfl, rfl⟩
        · -- the tail call not taken: its condition `0`, the call skipped
          obtain ⟨c, f, args, pos', -, hloc, hpos', -, as, hpairs, hsplit⟩ :=
            pair_tailL hok.pair hpos hci htz htsf htnx htod hst
          obtain ⟨evs, cs, es', rfl, hwp', hcs, -, -, hW'⟩ := hsplit hwp (hrwOf σ pre _ vs rd hσ hb hh0)
          have hcond := hσ.jc.cond _ _ hb c (by simp)
          rw [hloc] at hcond
          have hσc : σ c = 0 :=
            (rd_get hκ hm.fine (hsm _ _ _ hci).1 (by rw [hm.fp]; exact hcond) (hc0 _ _ _ hci)).symm
          simp only [hσc, ↓reduceIte] at hb hh0
          refine ⟨pos', pre ++ evs ++ [Ev.inK c, Ev.skip f args] ++ cs.map Ev.atom, es', vs, rd, hrd, hpos',
            by simpa [List.append_assoc] using hb, hwp', by simpa [List.append_assoc] using hh0,
            fun e _ ↦ loop_evM hok _ _ e, fun y hy ↦ ?_⟩
          rcases writtenC_append hy with hy | ⟨e, he, hwe⟩
          · have hy1 : WrittenC Cf.sigOf Cf.H rd σ (Cf.fn.params.map σ) (pre ++ evs) y := by
              have h2 : WrittenC Cf.sigOf Cf.H rd σ (Cf.fn.params.map σ) (pre ++ evs ++ [Ev.inK c] ++ [Ev.skip f args]) y := by
                simpa [List.append_assoc] using hy
              exact writtenC_noAtom (fun a h ↦ by cases h) (fun f a r h ↦ by cases h)
                (writtenC_noAtom (fun a h ↦ by cases h) (fun f a r h ↦ by cases h) h2)
            rcases hW' y hy1 with h | ⟨a, ha, hfa, hma, hwa⟩
            · exact (hW _ h).mono hle
            · rw [hhd i] at hpairs
              exact (flow_wrk hκ e1 hs0 hm hpairs ha hfa (fun q hq ↦ hσ.ptr _ _ hb a q
                (by simp [hma]) hq) hwa).mono hle'
          · obtain ⟨a, ha, rfl⟩ := List.mem_map.mp he
            exact absurd hwe (no_writes_of_stopL (hcs a ha))
        · -- the return jump never falls through
          exfalso
          obtain ⟨w, hw', hw0⟩ := hσ.jc.nz _ hrnz
          exact hw0 (rd_get hκ hm.fine (hsm _ _ _ hci).1 (by rw [hm.fp]; exact hw') (hc0 _ _ _ hci)).symm
      have hnj : ∀ oc od of, K.code[i]? ≠ some (.jump oc od of) := fun oc od of h ↦ hj ⟨oc, od, of, h⟩
      obtain ⟨pos', hpos', as, hpairs, hfallP⟩ := pair_fallC (sigOf := Cf.sigOf) (rd := rd)
        (ws0 := Cf.fn.params.map σ) hok.pair hpos hnj
      obtain ⟨evs, es', rfl, hwp', -, hWr⟩ := hfallP hwp (hrwOf σ pre _ vs rd hσ hb hh0)
      refine ⟨pos', pre ++ evs, es', vs, rd, hrd, hpos', by rw [List.append_assoc]; exact hb, hwp',
        by rw [List.append_assoc]; exact hh0, fun e _ ↦ loop_evM hok _ _ e, fun y hy ↦ ?_⟩
      rcases hWr y hy with h | ⟨a, ha', hfa', hma, hwa⟩ | ⟨o1, o2, o3, dv, pv, off, hci, hS, hcell, hmem, rfl⟩
      · exact (hW y h).mono hle
      · rw [hhd i] at hpairs
        exact (flow_wrk hκ e1 hs0 hm hpairs ha' hfa' (fun q hq ↦ hσ.ptr _ _ hb a q
          (List.mem_append_right _ (List.mem_append_left _ hma)) hq) hwa).mono hle'
      · obtain ⟨p, x, hp, hx, hw⟩ := hstw o1 o2 o3 hci (by rw [has_hasP]; exact hS)
        simp only [cellsAt, Bool.and_eq_true, Nat.beq_eq] at hcell
        obtain ⟨⟨hloc, hoff⟩, -⟩ := hcell
        have hsm := hok.small i hi
        rw [List.getElem?_eq_getElem hi, Option.some.injEq] at hci
        rw [hci] at hsm
        obtain ⟨so1, -, -⟩ := hsm
        have hrd : Rd img s'.fp o1 = some (σ pv) := by
          rw [hfp', ← hloc]
          exact hσ.ptr _ _ hb (.load dv pv off) pv (List.mem_append_right _ (List.mem_append_left _ hmem)) rfl
        have hpv : p = σ pv := rd_get hκ hf' so1 hrd hp
        refine ⟨x, ?_, hx.2, hw⟩
        have h1 := hx.1
        rw [limb0_mul_ofK, hpv, ← hoff] at h1
        exact h1
    · -- a jump taken
      intro s1 s' e1 hm hmo e' hf' hle' hjo hjt hcn
      obtain ⟨oc, od, of, hci, h0, h1, hpcs⟩ := hjt
      obtain ⟨soc, sod, sof⟩ := hsm _ _ _ hci
      have hle : s.mem ≤ s'.mem := Mem.le_trans hm.le hle'
      have hT1 : ∀ p ∈ K.F.sig.term, LTF (stOf s1.mem s1.fp) p.1 p.2 := fun p hp ↦ by
        rw [hm.fp]; exact Mode.LTF.mem hm.le (hT p hp)
      have hP1 : ∀ {σ : Val}, HonF img Cf s.fp σ → ParAt K.F.sig np (stOf s1.mem s1.fp) (Cf.fn.params.map σ) :=
        fun hσ ↦ (hPs hσ).mono (s := stOf s.mem s.fp) (s' := stOf s1.mem s1.fp) hm.le hm.fp
      rcases loopCode_jump hcode hcpre hci with ⟨hi', rfl, rfl, rfl⟩ | ⟨hi', rfl, rfl, rfl⟩
      swap
      · -- the return
        have hrj : ∃ c, K.code[i]? = some (.jump c 0 1) := ⟨_, hci⟩
        cases hjo with
        | «local» t hnr => exact absurd hrj hnr
        | halt hnr => exact absurd hrj hnr
        | tail e hnr => exact absurd hrj hnr
        | call G' t hnr => exact absurd hrj hnr
        | ret hregs hretw _ =>
          refine k s1 s' (he1 s1 e1) hm hmo e' hf' hle' (.ret _ hci (by omega) h0 h1 ?_)
          rw [Mode.postAt_none hCt.1]
          obtain ⟨pos, pre, es, vs, rd, hrd, hpos, hb, hwp, hh0, -, hW⟩ := hheap σ0 hσ0
          obtain ⟨hreads, hposts⟩ := loop_heap hok hb hh0 (hσ0.res hxw) (hPs hσ0) hT
          obtain ⟨as, hpairs, hpr⟩ := pair_retL hok.pair hpos hci hrz hself1 hpc0 hst hwp (readsAt_of_C hreads)
          rw [hhd i] at hpairs
          have W1 : ∀ x, WrittenC Cf.sigOf Cf.H rd σ0 (Cf.fn.params.map σ0) (pre ++ es) x → WrK s1.mem x := by
            intro x hx
            rcases hpr x hx with h | ⟨a, ha, hfa, hma, hwa⟩
            · exact (hW _ h).mono hm.le
            · exact flow_wrk hκ e1 hs0 hm hpairs ha hfa
                (fun q hq ↦ hσ0.ptr _ _ hb a q (List.mem_append_right _ hma) hq) hwa
          have hvs : vs = [] := (hselfs hσ0 hb).2
          subst hvs
          simp only [PostOkW, List.map_nil, List.append_nil] at hposts
          exact retAll_of_wrk hs (hP1 hσ0) hT1 (fun c hc ↦ W1 _ (hposts.1.1 c hc))
            (fun r hr x hx ↦ W1 x (hposts.1.2 r hr x hx))
      · -- the tail call
        obtain ⟨pos, pre, es, vs, rd, hrd, hpos, hb, hwp, hh0, -, hW⟩ := hheap σ0 hσ0
        obtain ⟨c, f, args, pos', hcm, hloc, -, hrn, as, hpairs, hsplit⟩ :=
          pair_tailL hok.pair hpos hci htz htsf htnx htod hst
        have hrw0 := hrwOf σ0 pre es vs rd hσ0 hb hh0
        have hrw0C := (loop_heap hok hb hh0 (hσ0.res hxw) (hPs hσ0) hT).1
        obtain ⟨evs, cs, es', heq, hwp', hcs, -, -, hW'⟩ := hsplit hwp hrw0
        rw [hbody] at hcm
        rcases stmts_loop hcm with ⟨a, ha⟩ | hceq | hceq
        · cases ha
        swap
        · cases hceq
        simp only [Stmt.callIf.injEq] at hceq
        obtain ⟨rfl, rfl, rfl⟩ := hceq
        -- its condition nonzero: the call entered
        obtain ⟨v, hv, hv0⟩ := hcn _ _ _ hci
        have hcond := hσ0.jc.cond _ _ hb c (by rw [heq]; simp)
        rw [hloc] at hcond
        have hσc : σ0 c ≠ 0 := by
          have := rd_get hκ hm.fine soc (by rw [hm.fp]; exact hcond) hv
          rw [← this]; exact hv0
        simp only [hσc, ↓reduceIte] at heq
        obtain ⟨hpe, hvs⟩ := hselfs hσ0 hb
        simp only [hσc, ↓reduceIte] at hpe
        subst hvs
        have hes' : es' = [] := by
          rw [retNil_eq hrn, walk_ret_cons, Out.ret.injEq] at hwp'
          exact hwp'.1.symm
        subst hes'
        -- the next frame, of the honest tree
        have hcl0 : (calls (pre ++ es))[0]? = some ⟨Cf.fn.name, args, [], true⟩ ∧
            0 + 1 = (calls (pre ++ es)).length := by
          rw [hpe]
          have := calls_atoms as0
          simp only [calls, List.filterMap_append] at this ⊢
          rw [this]
          simp [Ev.call?]
          exact ⟨rfl, rfl⟩
        have hfetch := (hok.fetch i _ hci).1
        rw [← hok.xentry] at hfetch
        obtain ⟨hq, hn0, hn1, hnargs⟩ := hσ0.tail _ _ hb 0 _ hcl0.1 hcl0.2 i _ _ _ S (by rw [hok.xlen]; exact hi)
          soc sod sof hfetch hstatS hS0
        have hfpS : s'.fp = s.fp + S := by
          have := rd_get hκ hm.fine sof (by rw [hm.fp]; exact hq) h1
          have h2 := hf'.fp
          have h3 := hs0.fp
          unfold maxCells at h2 h3
          exact gpow_inj (by omega) (by omega) (pow_of_ofK this)
        cases hjo with
        | ret _ _ hr =>
          obtain ⟨c', hc'⟩ := hr
          rw [hci, Option.some.injEq, OffsetInstruction.jump.injEq] at hc'
          exact absurd hc'.2.1 htod
        | «local» t _ hfp' _ _ =>
          exfalso
          rw [hfpS, hm.fp] at hfp'
          omega
        | halt _ h1' _ => simp [hfp1] at h1'
        | call G' t _ _ hsig _ _ _ =>
          rw [trieNil_get hsigs0] at hsig
          cases hsig
        | tail e _ hpc' hfp' hentry hr0 hr1 hret =>
          refine k s1 s' (he1 s1 e1) hm hmo e' hf' hle' (.tail hok.sigE fun hTE ↦ ?_)
          have hWc : ∀ x, WrittenC Cf.sigOf Cf.H rd σ0 (Cf.fn.params.map σ0) (pre ++ evs) x → WrK s'.mem x := by
            intro x hx
            rcases hW' x hx with h | ⟨a, ha, hfa, hma, hwa⟩
            · exact (hW _ h).mono hle
            · rw [hhd i] at hpairs
              exact (flow_wrk hκ e1 hs0 hm hpairs ha hfa (fun q hq ↦ hσ0.ptr _ _ hb a q
                (by rw [heq]; simp [hma]) hq) hwa).mono hle'
          exact Mode.tail_of_mode hCt.1 <| tail_next (c := c) (args := args) hok hκ hs0.fp hm.fp hm.le hf' hle' hfpS hS30
            (hpc'.trans hok.fentry) hentry hr0 hr1 hTE (hjtR s' hle) hwE (fun o ho ↦ (hso o ho).2) hent0 hent1 hb hh0
            (hσ0.res hxw) (by simpa using heq) hrw0C hWc (fun k hk ↦ hnargs k hk) hargs (hPs hσ0) hT hcs

/-- **A leaf loop helper on the core route meets its frame interface**, from the kernel's checks. -/
theorem fnSpecC_of_loop {K : Mode.Cert} {Cf : CFun} (hok : LoopOk K Cf) : Mode.FnSpecC K Cf :=
  fun _ _ hC ha hK _ _ _ _ hκ hY hH _ hCt ↦ frameSpec_loop hok hC ha hK hκ hY hH (modeCts_of hCt hok.hc hok.hcs)

end

end LeanVM.Guest.CoreMode
