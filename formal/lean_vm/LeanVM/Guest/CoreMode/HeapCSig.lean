/-
  LeanVM.Guest.CoreMode.HeapCSig

  The heap check with calls and loops, its signatures: their words at a site, what a path writes and reads, and a run's coverage.
-/

module

public import LeanVM.Guest.CoreMode.Heap
public import LeanVM.Guest.Memory.Static
public import LeanVM.Guest.Memory.Fresh

/-!
# Heap signatures at a site

The definitions `heapOkC` (`HeapC.lean`) checks against: a signature's slots as words (`slotW`, `CCell.valW`), its cells and runs at a site (`PreSet`, `PostSet`), ghost words (`gargsW`), what a path's events write and read (`EvW`, `WrittenC`, `ReadsOkC`, `PostOkC`), monomials at a site (`instC`), and a cell's or a run's coverage by a run in scope (`ptRun`, `runRun`, `shiftR`).
-/

namespace LeanVM.Guest.CoreMode

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Memory
open LeanVM.Guest.Exec (Trie PowTree natSeq)
open LeanVM.Guest.Check (getF setF)

@[expose] public section

/-! ## Words over slots, exponents -/

/-- The product of the bases' powers, each base `b` the word `w b`. -/
def prodW (w : ℕ → E) : List (ℕ × ℕ) → E
  | [] => 1
  | (b, e) :: l => w b ^ e * prodW w l

/-- The word a cell names, each base `b` the word `w b`. -/
def CCell.valW (w : ℕ → E) (c : CCell) : E := prodW w c.bases * ofK (addressOfIndex c.off)

/-- The address of a cell, each base `b` the word `w b`. -/
def CCell.addrW (w : ℕ → E) (c : CCell) : K := (c.valW w).limb 0

/-- Slot `b`'s word. -/
def slotW (ws : List E) (b : ℕ) : E := ws.getD b 0

/-- The words of a valuation's values `V.n k`. -/
def vw (σ : Val) (k : ℕ) : E := σ (V.n k)

/-- The bound `2^62` below which a word `g^y` is read as its exponent `y`. -/
def capE : ℕ := 4611686018427387904

open Classical in
/-- **The exponent of a word**: `y` for the word `g^y`, `y < 2^62`. -/
noncomputable def rep (x : E) : Option ℕ :=
  if h : ∃ y, y < capE ∧ x = ofK (addressOfIndex y) then some (Classical.choose h) else none

/-- An index as a cell: a constant `g^n`, or a base. -/
def idxC : CIdx → CCell
  | .num n => ⟨[], n⟩
  | .val v => baseC v
  | .mono c => c

theorem idxC_vals : ∀ i : CIdx, (idxC i).vals = i.vals
  | .num _ => rfl
  | .val _ => rfl
  | .mono _ => rfl

/-- **The cells of a run** `base · g^(S · j)`, `j` from the exponent of `lo` to below that of `hi`. -/
def RunSet (w : ℕ → E) (base : CCell) (S : ℕ) (lo hi : CCell) (x : K) : Prop :=
  ∃ ylo yhi j, rep (lo.valW w) = some ylo ∧ rep (hi.valW w) = some yhi ∧ ylo ≤ j ∧ j < yhi ∧
    x = (base.valW w * ofK (addressOfIndex (S * j))).limb 0

/-- **A run written**: its cells are in `W` (none when a bound has no exponent). -/
def RunF (W : K → Prop) (w : ℕ → E) (base : CCell) (S : ℕ) (lo hi : CCell) : Prop :=
  ∀ x, RunSet w base S lo hi x → W x

/-- A signature run's cells. -/
def CRun.Set (w : ℕ → E) (r : CRun) : K → Prop := RunSet w r.base r.stride (idxC r.lo) (idxC r.hi)

/-- A signature run written. -/
def CRun.F (W : K → Prop) (w : ℕ → E) (r : CRun) : Prop := RunF W w r.base r.stride (idxC r.lo) (idxC r.hi)

/-- **Exponents in order**: both exist, the first below the second. -/
def LtF (w : ℕ → E) (a b : CCell) : Prop :=
  ∃ ya yb, rep (a.valW w) = some ya ∧ rep (b.valW w) = some yb ∧ ya < yb

/-! ## Signatures at a site, events -/

/-- The addresses of a signature's cells and runs at the slots' words `ws`. -/
def SigSet (cs : List CCell) (rs : List CRun) (ws : List E) (x : K) : Prop :=
  (∃ c ∈ cs, c.addrW (slotW ws) = x) ∨ ∃ r ∈ rs, r.Set (slotW ws) x

/-- **A signature's cells and runs written** in `W`, at the slots' words `ws`. -/
def SigOk (W : K → Prop) (cs : List CCell) (rs : List CRun) (ws : List E) : Prop :=
  (∀ c ∈ cs, W (c.addrW (slotW ws))) ∧ ∀ r ∈ rs, r.F W (slotW ws)

/-- **The cells a pointer fact names**: past the word at `a`, if there is one, at the offsets. -/
def PtrSet (rd : Reader) (a : K) (offs : List ℕ) (x : K) : Prop :=
  ∃ w, rd a = some w ∧ ∃ o ∈ offs, x = w.limb 0 * addressOfIndex o

/-- The cells a signature's pointer facts and pointer runs name at the slots' words `ws`. -/
def PtrSigSet (rd : Reader) (ps : List (CCell × List ℕ)) (prs : List (CRun × List ℕ)) (ws : List E) (x : K) :
    Prop :=
  (∃ p ∈ ps, PtrSet rd (p.1.addrW (slotW ws)) p.2 x) ∨ ∃ p ∈ prs, ∃ a, p.1.Set (slotW ws) a ∧ PtrSet rd a p.2 x

/-- **A signature's pointer facts and runs written** in `W`, at the slots' words `ws`. -/
def PtrOk (W : K → Prop) (rd : Reader) (ps : List (CCell × List ℕ)) (prs : List (CRun × List ℕ)) (ws : List E) :
    Prop :=
  ∀ x, PtrSigSet rd ps prs ws x → W x

/-- **A run at a word**: the cells `w·b·g^(S·j)`, `lo ≤ j < hi`, `b`, `lo`, `hi` at the valuation `v`. -/
def RunSetB (v : ℕ → E) (w : E) (b : CCell) (S : ℕ) (lo hi : CCell) (x : K) : Prop :=
  ∃ ylo yhi j, rep (lo.valW v) = some ylo ∧ rep (hi.valW v) = some yhi ∧ ylo ≤ j ∧ j < yhi ∧
    x = (w * b.valW v * ofK (addressOfIndex (S * j))).limb 0

/-- **The cells a signature's runs at words name** (`postQ`): at each cell holding a word `w`, the run at `w`,
at the slots' words `ws`. -/
def QSet (rd : Reader) (qs : List (CCell × CRun)) (ws : List E) (x : K) : Prop :=
  ∃ p ∈ qs, ∃ w, rd (p.1.addrW (slotW ws)) = some w ∧
    RunSetB (slotW ws) w p.2.base p.2.stride (idxC p.2.lo) (idxC p.2.hi) x

/-- **A signature's preconditions** at the slots' words: its cells, runs, pointer facts and runs. -/
def PreSet (rd : Reader) (G : HSig) (ws : List E) (x : K) : Prop :=
  SigSet G.pre G.preR ws x ∨ PtrSigSet rd G.preP G.prePR ws x

/-- **A signature's guarantees** at the slots' words. -/
def PostSet (rd : Reader) (G : HSig) (ws : List E) (x : K) : Prop :=
  SigSet G.post G.postR ws x ∨ PtrSigSet rd G.postP G.postPR ws x ∨ QSet rd G.postQ ws x

/-! ## Ghost words -/

/-- The first value number of the ghosts: ghost `j` of a function is the value `V.n (GB + j)`. -/
def GB : ℕ := 1048576

/-- A call's values are the values `V.n a`, `a ∈ ks`. -/
def keyOk : List V → List ℕ → Bool
  | [], [] => true
  | v :: vs, k :: ks => (match vnum v with
    | some k' => Nat.beq k' k
    | none => false) && keyOk vs ks
  | _, _ => false

/-- **A call's ghost monomials**: those the certificate names for a call of `g` on `args`, over the
caller's values. -/
def gargsOf (ga : List (String × List ℕ × List CCell)) (g : String) (args : List V) : List CCell :=
  match ga.find? fun p ↦ decide (p.1 = g) && keyOk args p.2.1 with
  | some p => p.2.2
  | none => []

/-- **A call's ghost words**, at the caller's valuation. -/
def gargsW (H : HCert) (σ : Val) (g : String) (args : List V) : List E :=
  (gargsOf H.gargs g args).map fun c ↦ c.valW (vw σ)

/-- **A function's own ghost words**: its values `V.n (GB + j)`. -/
def ownG (G : HSig) (σ : Val) : List E := (List.range G.ghosts).map fun j ↦ vw σ (GB + j)

/-- The first value number of the words at cells (`HCert.ders`): value `DB + k` (below `GB`) is the word at
the cell `ders[k]`. Past every value a function names (`noGhost`). -/
def DB : ℕ := 524288

/-- The numbers, each at its first occurrence (`acc` reversed, the ones kept so far). -/
def nubN : List ℕ → List ℕ → List ℕ
  | acc, [] => acc.reverse
  | acc, k :: l => nubN (bif acc.any (Nat.beq k) then acc else k :: acc) l

/-- **The words at cells monomials name**: `k` for each base `DB + k` below `GB`, once, in order. -/
def derKs (ms : List CCell) : List ℕ :=
  nubN [] ((ms.flatMap CCell.bases).filterMap fun b ↦
    bif Nat.ble DB b.1 && Nat.blt b.1 GB then some (b.1 - DB) else none)

/-- **The words at cells a call's ghost monomials name** (`derKs`). -/
def callDers (H : HCert) (g : String) (args : List V) : List ℕ := derKs (gargsOf H.gargs g args)

/-- **The addresses an event writes**: an atom's, an entered call's callee guarantees at its words. -/
def EvW (sigOf : String → HSig) (rd : Reader) (σ : Val) : Ev → K → Prop
  | .atom a, x => Writes σ a x
  | .call f args rets, x => PostSet rd (sigOf f) ((args ++ rets).map σ) x
  | _, _ => False

/-- **Written after the events `es`**: the own preconditions at the parameters' words `ws0` and the
own ghost words, or an event's write. -/
def WrittenC (sigOf : String → HSig) (H : HCert) (rd : Reader) (σ : Val) (ws0 : List E) (es : List Ev) (x : K) :
    Prop :=
  PreSet rd H.sig (ws0 ++ ownG H.sig σ) x ∨ ∃ e ∈ es, EvW sigOf rd σ e x

/-- **A callee's preconditions written in `W`**, at a call of `g` on `args`: its argument words and
the ghost words the caller names (as many as it has ghosts). -/
def CallPre (sigOf : String → HSig) (H : HCert) (rd : Reader) (σ : Val) (W : K → Prop) (g : String)
    (args : List V) : Prop :=
  (gargsOf H.gargs g args).length = (sigOf g).ghosts ∧
    SigOk W (sigOf g).pre (sigOf g).preR (args.map σ ++ gargsW H σ g args) ∧
    PtrOk W rd (sigOf g).preP (sigOf g).prePR (args.map σ ++ gargsW H σ g args)

/-- **The cells a call's ghost words read are written** in `W`: `ders[k]` for each word at a cell `DB + k` its
ghost monomials name. -/
def DerW (H : HCert) (σ : Val) (W : K → Prop) (g : String) (args : List V) : Prop :=
  ∀ k ∈ callDers H g args, ∀ c, H.ders[k]? = some c → W (c.addrW (vw σ))

/-- **The cells a call's ghost words read are in memory.** -/
def DerDef (H : HCert) (rd : Reader) (σ : Val) (g : String) (args : List V) : Prop :=
  ∀ k ∈ callDers H g args, ∀ c, H.ders[k]? = some c → (rd (c.addrW (vw σ))).isSome

/-- **What a call of `g` on `args` needs written in `W`**: the cells its ghost words read, and, those being in
memory, its callee's preconditions (`CallPre`). -/
def CallReq (sigOf : String → HSig) (H : HCert) (rd : Reader) (σ : Val) (W : K → Prop) (g : String)
    (args : List V) : Prop :=
  DerW H σ W g args ∧ (DerDef H rd σ g args → CallPre sigOf H rd σ W g args)

/-- **The words at cells are the memory's**: value `DB + k` holds the word at `ders[k]`, where there is one. -/
def DerOk (H : HCert) (rd : Reader) (σ : Val) : Prop :=
  ∀ k c, H.ders[k]? = some c → ∀ w, rd (c.addrW (vw σ)) = some w → vw σ (DB + k) = w

theorem derOk_nil {H : HCert} (h : H.ders = []) (rd : Reader) (σ : Val) : DerOk H rd σ := fun k c hk ↦ by
  rw [h] at hk; cases hk

/-- **The own parameter words are the ghosts'**: ghost `j` holds the word at the cell `c` of each `(c, j)` of
`HSig.gw`, where there is one. -/
def GwOk (G : HSig) (rd : Reader) (σ : Val) : Prop :=
  ∀ c j, (c, j) ∈ G.gw → ∀ w, rd (c.addrW (vw σ)) = some w → vw σ (GB + j) = w

theorem gwOk_nil {G : HSig} (h : G.gw = []) (rd : Reader) (σ : Val) : GwOk G rd σ := fun c j hc ↦ by
  rw [h] at hc; cases hc

theorem callDers_nil {H : HCert} (h : H.gargs = []) (g : String) (args : List V) : callDers H g args = [] := by
  simp [callDers, gargsOf, h, derKs, nubN]

/-- A call naming no word at a cell: its callee's preconditions. -/
theorem CallReq.pre {sigOf : String → HSig} {H : HCert} {rd : Reader} {σ : Val} {W : K → Prop} {g : String}
    {args : List V} (h : CallReq sigOf H rd σ W g args) (hd : callDers H g args = []) : CallPre sigOf H rd σ W g args :=
  h.2 fun k hk ↦ by rw [hd] at hk; cases hk

/-- What an event needs written in `W`: an atom its reads, an entered call the cells its ghost words read and its
callee's preconditions at its argument and ghost words (`CallReq`). -/
def ReqOk (sigOf : String → HSig) (H : HCert) (rd : Reader) (σ : Val) (W : K → Prop) : Ev → Prop
  | .atom a => ∀ x, Reads H σ a x → W x
  | .call f args _ => CallReq sigOf H rd σ W f args
  | _ => True

/-- **Every event's needs are written before it.** -/
def ReadsOkC (sigOf : String → HSig) (H : HCert) (rd : Reader) (σ : Val) (ws0 : List E) (es : List Ev) : Prop :=
  ∀ es1 e es2, es = es1 ++ e :: es2 → ReqOk sigOf H rd σ (WrittenC sigOf H rd σ ws0 es1) e

/-- The values a hint's destination names in the frame. -/
def destStack : Dest → List V
  | .stack cs => cs
  | .heap .. => []

/-- **The values an atom defines in its frame**: a constant's, a sum's, a product's, a copy's, and a hint's
frame destinations. -/
def atomDst : Atom → List V
  | .const d _ => [d]
  | .add d _ _ => [d]
  | .mul d _ _ => [d]
  | .copy d _ => [d]
  | .hint (.witness _ dst) => destStack dst
  | .hint (.bits _ _ _ dst) => destStack dst
  | .hint (.bitsExp _ _ dst) => destStack dst
  | .hint (.digitsExp _ _ _ _ _ _ dst) => destStack dst
  | .hint (.windowsExp _ _ _ _ dst) => destStack dst
  | _ => []

/-- **A frame run's cell at return**: the cell `p·g^i` of a `frameAddr p run` on the path, whose value
`run[i]` an atom on the path defines (the frame cell holding it, written by then); or, past the run, a cell `(kp, i)`
of the certificate's frame run cells `fas` (`i` at least the run's length), which the frame walk has written at the
returns (`faRetOk`). -/
def FAW (σ : Val) (fas : List (ℕ × ℕ)) (es : List Ev) (x : K) : Prop :=
  (∃ p run i v, Ev.atom (.frameAddr p run) ∈ es ∧ run[i]? = some v ∧ (∃ a, Ev.atom a ∈ es ∧ v ∈ atomDst a) ∧
    x = cellAt σ p i) ∨
  ∃ kp i run, (kp, i) ∈ fas ∧ Ev.atom (.frameAddr (V.n kp) run) ∈ es ∧ run ≠ [] ∧ run.length ≤ i ∧
    x = cellAt σ (V.n kp) i

/-- **The guarantees at return are written**, at the parameters' words `ws0` and the returned `vs`: by the
events, or a frame run's cells (`FAW`). -/
def PostOkC (sigOf : String → HSig) (H : HCert) (rd : Reader) (σ : Val) (ws0 : List E) (es : List Ev)
    (vs : List V) : Prop :=
  SigOk (fun x ↦ WrittenC sigOf H rd σ ws0 es x ∨ FAW σ H.fas es x) H.sig.post H.sig.postR (ws0 ++ vs.map σ) ∧
    PtrOk (fun x ↦ WrittenC sigOf H rd σ ws0 es x ∨ FAW σ H.fas es x) rd H.sig.postP H.sig.postPR (ws0 ++ vs.map σ) ∧
    (∀ x, QSet rd H.sig.postQ (ws0 ++ vs.map σ) x → WrittenC sigOf H rd σ ws0 es x ∨ FAW σ H.fas es x) ∧
    SigOk (fun x ↦ WrittenC sigOf H rd σ ws0 es x ∨ FAW σ H.fas es x) H.sig.postN H.sig.postRN (H.sig.nv.map (vw σ))

/-- **The guarantees at return written by the events** (`PostOkC` without frame run cells). -/
def PostOkW (sigOf : String → HSig) (H : HCert) (rd : Reader) (σ : Val) (ws0 : List E) (es : List Ev)
    (vs : List V) : Prop :=
  SigOk (WrittenC sigOf H rd σ ws0 es) H.sig.post H.sig.postR (ws0 ++ vs.map σ) ∧
    PtrOk (WrittenC sigOf H rd σ ws0 es) rd H.sig.postP H.sig.postPR (ws0 ++ vs.map σ) ∧
    (∀ x, QSet rd H.sig.postQ (ws0 ++ vs.map σ) x → WrittenC sigOf H rd σ ws0 es x) ∧
    SigOk (WrittenC sigOf H rd σ ws0 es) H.sig.postN H.sig.postRN (H.sig.nv.map (vw σ))

/-- **Returned words' monomials**: each `(k, c)` of the signature's `retM`, returned word `k` is
`c`'s word at the parameters' words `ws0`. -/
def RetMOk (G : HSig) (ws0 rets : List E) : Prop := ∀ k c, (k, c) ∈ G.retM → rets[k]? = some (c.valW (slotW ws0))

/-- **Words at return**: each `(i, m)` of the signature's `postV`, the final memory holds `m`'s word at
`post` cell `i`, at the slots' words `ws`. -/
def RetVOk (rd : Reader) (G : HSig) (ws : List E) : Prop :=
  ∀ i m, (i, m) ∈ G.postV → ∃ c, G.post[i]? = some c ∧ rd (c.addrW (slotW ws)) = some (m.valW (slotW ws))

/-- **Equations at return**: each `(a, b)` of the signature's `retEq`, `a`'s word is `b`'s at the slots'
words `ws`. -/
def RetEqOk (G : HSig) (ws : List E) : Prop := ∀ p ∈ G.retEq, p.1.valW (slotW ws) = p.2.valW (slotW ws)

/-- **What an event gives beyond its writes**: an entered call, its callee's returned words'
monomials, words at return and equations at return, at its words. -/
def EvM (sigOf : String → HSig) (rd : Reader) (σ : Val) : Ev → Prop
  | .call f args rets => RetMOk (sigOf f) (args.map σ) (rets.map σ) ∧ RetVOk rd (sigOf f) ((args ++ rets).map σ) ∧
      RetEqOk (sigOf f) ((args ++ rets).map σ)
  | _ => True

/-- **Every event's needs are written before it, once the calls before it have their callees' returned words**
(`EvM`, a property of the calls already made). -/
def ReadsOkP (sigOf : String → HSig) (H : HCert) (rd : Reader) (σ : Val) (ws0 : List E) (es : List Ev) : Prop :=
  ∀ es1 e es2, es = es1 ++ e :: es2 → (∀ e' ∈ es1, EvM sigOf rd σ e') →
    ReqOk sigOf H rd σ (WrittenC sigOf H rd σ ws0 es1) e

/-- **The needs of the events `es` after `pre` are written before each**, once the calls before it among `es`
have their callees' returned words. -/
def ReadsAt (sigOf : String → HSig) (H : HCert) (rd : Reader) (σ : Val) (ws0 : List E) (pre es : List Ev) : Prop :=
  ∀ es1 e es2, es = es1 ++ e :: es2 → (∀ e' ∈ es1, EvM sigOf rd σ e') →
    ReqOk sigOf H rd σ (WrittenC sigOf H rd σ ws0 (pre ++ es1)) e

section ReadsAt

variable {sigOf : String → HSig} {H : HCert} {rd : Reader} {σ : Val} {ws0 : List E}

theorem readsOkC_of_P {es : List Ev} (h : ReadsOkP sigOf H rd σ ws0 es) (hM : ∀ e ∈ es, EvM sigOf rd σ e) :
    ReadsOkC sigOf H rd σ ws0 es := fun es1 e es2 he ↦
  h es1 e es2 he fun e' he' ↦ hM e' (by rw [he]; exact List.mem_append_left _ he')

/-- The events after `pre`, the calls of `pre` having their callees' returned words. -/
theorem readsAt_of_P {pre es : List Ev} (h : ReadsOkP sigOf H rd σ ws0 (pre ++ es))
    (hm : ∀ e ∈ pre, EvM sigOf rd σ e) : ReadsAt sigOf H rd σ ws0 pre es := fun es1 e es2 he hm1 ↦
  h (pre ++ es1) e es2 (by rw [he, List.append_assoc]) fun e' he' ↦ by
    rcases List.mem_append.mp he' with h' | h'
    · exact hm e' h'
    · exact hm1 e' h'

/-- The events after `pre`, every call's returned words given. -/
theorem readsAt_of_C {pre es : List Ev} (h : ReadsOkC sigOf H rd σ ws0 (pre ++ es)) :
    ReadsAt sigOf H rd σ ws0 pre es := fun es1 e es2 he _ ↦
  h (pre ++ es1) e es2 (by rw [he, List.append_assoc])

theorem ReadsAt.shift {pre X es : List Ev} (h : ReadsAt sigOf H rd σ ws0 pre (X ++ es))
    (hX : ∀ e ∈ X, EvM sigOf rd σ e) : ReadsAt sigOf H rd σ ws0 (pre ++ X) es := fun es1 e es2 he hm ↦ by
  have := h (X ++ es1) e es2 (by rw [he, List.append_assoc]) fun e' he' ↦ by
    rcases List.mem_append.mp he' with h' | h'
    · exact hX e' h'
    · exact hm e' h'
  rwa [← List.append_assoc] at this

theorem ReadsAt.head {pre es : List Ev} {e : Ev} (h : ReadsAt sigOf H rd σ ws0 pre (e :: es)) :
    ReqOk sigOf H rd σ (WrittenC sigOf H rd σ ws0 pre) e := by
  have := h [] e es rfl (by simp)
  rwa [List.append_nil] at this

/-- Atoms give nothing beyond their writes. -/
theorem evM_atoms (as : List Atom) : ∀ e ∈ as.map Ev.atom, EvM sigOf rd σ e := fun e he ↦ by
  obtain ⟨a, -, rfl⟩ := List.mem_map.mp he
  trivial

theorem evM_app {a b : List Ev} (ha : ∀ e ∈ a, EvM sigOf rd σ e) (hb : ∀ e ∈ b, EvM sigOf rd σ e) :
    ∀ e ∈ a ++ b, EvM sigOf rd σ e := fun e he ↦ by
  rcases List.mem_append.mp he with h | h
  · exact ha e h
  · exact hb e h

/-- A branch's condition, a skipped call: nothing beyond their writes. -/
theorem evM_inK_cons {c : V} {l : List Ev} (h : ∀ e ∈ l, EvM sigOf rd σ e) : ∀ e ∈ Ev.inK c :: l, EvM sigOf rd σ e :=
  fun e he ↦ by
    rcases List.mem_cons.mp he with rfl | h'
    · trivial
    · exact h e h'

theorem evM_skip_cons {f : String} {args : List V} {l : List Ev} (h : ∀ e ∈ l, EvM sigOf rd σ e) :
    ∀ e ∈ Ev.skip f args :: l, EvM sigOf rd σ e := fun e he ↦ by
  rcases List.mem_cons.mp he with rfl | h'
  · trivial
  · exact h e h'

theorem evM_nil : ∀ e ∈ ([] : List Ev), EvM sigOf rd σ e := fun _ h ↦ by cases h

end ReadsAt

/-- **What an instance is given at entry**: its termination facts. -/
def EntryF (H : HCert) (ws0 : List E) : Prop := ∀ p ∈ H.sig.term, LtF (slotW ws0) (idxC p.1) (idxC p.2)

/-- **A branch condition holds** at a valuation: the selector's word is `g^j`, the guard's is `0`, or
not. -/
def CCond.Holds (σ : Val) : CCond → Prop
  | .arm x j => σ (V.n x) = ofK (addressOfIndex j)
  | .zero c => σ (V.n c) = 0
  | .nonzero c => σ (V.n c) ≠ 0

/-- **A residual holds** at a valuation, over value numbers: exponents in order (`lt`), a cell in a
run (`sub`), a run in a run (`subR`), a cell among cells (`subP`), and a residual where its branch
conditions hold (`under`). `nz`, which the check does not use, is `True`. -/
def CRes.Holds (σ : Val) : CRes → Prop
  | .lt a b => LtF (vw σ) (idxC a) (idxC b)
  | .nz _ => True
  | .sub c r => r.Set (vw σ) (c.addrW (vw σ))
  | .subR q r => ∀ x, q.Set (vw σ) x → r.Set (vw σ) x
  | .under g r => (∀ c ∈ g, c.Holds σ) → r.Holds σ
  | .subP c cs => ∃ c' ∈ cs, c.addrW (vw σ) = c'.addrW (vw σ)

/-- **The residuals hold** at the instance. -/
def ResF (H : HCert) (σ : Val) : Prop := ∀ r ∈ H.res, r.Holds σ

/-! ## Monomials at a site -/

/-- A monomial's power. -/
def CCell.pow (c : CCell) (e : ℕ) : CCell := ⟨c.bases.map fun b ↦ (b.1, b.2 * e), c.off * e⟩

/-- Entry `n` of a list. -/
def nth {α : Type} : List α → ℕ → Option α
  | [], _ => none
  | a :: _, 0 => some a
  | _ :: l, n + 1 => nth l n

/-- The bases' powers multiplied into `acc`, base `b` the slot monomial `ms[b]`. -/
def instB (ms : List CCell) : List (ℕ × ℕ) → CCell → Option CCell
  | [], acc => some acc
  | (b, e) :: l, acc => match nth ms b with
    | some m => instB ms l (acc.mul (m.pow e))
    | none => none

/-- **A signature cell at a site**, slot `b` the monomial `ms[b]`. -/
def instC (ms : List CCell) (c : CCell) : Option CCell := instB ms c.bases ⟨[], c.off⟩

/-- A signature index at a site. -/
def instI (ms : List CCell) : CIdx → Option CCell
  | .num n => some ⟨[], n⟩
  | .val v => nth ms v
  | .mono c => instC ms c

/-- **A run of the pass**: the cells `base · g^(stride · j)`, `j` from the exponent of `lo` to
below that of `hi`, bounds as monomials. -/
structure PRun where
  base : CCell
  stride : ℕ
  lo : CCell
  hi : CCell

/-- **A dispatch arm's guarantees**: cells, runs, pointer facts, pointer runs. -/
structure CdA where
  cs : List CCell
  rs : List PRun
  ps : List (CCell × List ℕ)
  prs : List (PRun × List ℕ)

/-- **A dispatch's arms' guarantees under its selector** `mx`: if the selector's word is `g^j`, arm `j` ran, and
`arms[j]` holds (one entry per dispatch, so a later dispatch on `mx` looks up its arm `j` by index). -/
structure CdE where
  mx : CCell
  arms : List CdA

/-- A signature run at a site. -/
def instR (ms : List CCell) (r : CRun) : Option PRun :=
  match instC ms r.base, instI ms r.lo, instI ms r.hi with
  | some b, some l, some h => some ⟨b, r.stride, l, h⟩
  | _, _, _ => none

/-- Two runs are equal. -/
def PRun.beq (a b : PRun) : Bool :=
  a.base.beq b.base && Nat.beq a.stride b.stride && a.lo.beq b.lo && a.hi.beq b.hi

/-- `k r`, `r` evaluated first. -/
def PRun.seq {β : Type} (r : PRun) (k : PRun → β) : β :=
  r.base.seq fun b ↦ natSeq r.stride fun s ↦ r.lo.seq fun l ↦ r.hi.seq fun h ↦ k ⟨b, s, l, h⟩

theorem PRun.seq_eq {β : Type} (r : PRun) (k : PRun → β) : r.seq k = k r := by
  simp only [PRun.seq, CCell.seq_eq, Exec.natSeq_eq]

/-- The values' monomials. -/
noncomputable def monos (env : Trie CCell) : List V → Option (List CCell)
  | [] => some []
  | v :: vs => match monoOf env v, monos env vs with
    | some m, some ms => some (m :: ms)
    | _, _ => none

/-- A fact's index: a constant, a value's monomial, or a monomial as it is. -/
noncomputable def idxF (env : Trie CCell) : CIdx → CCell
  | .num n => ⟨[], n⟩
  | .val k => (getF env k).getD (baseC k)
  | .mono c => c

/-! ## Coverage -/

/-- The fact `(a, b)`. -/
def hasF (F : List (CCell × CCell)) (a b : CCell) : Bool := F.any fun p ↦ p.1.beq a && p.2.beq b

/-- A fact `(g^k', b)` with `k ≤ k'`. -/
def hasFC (F : List (CCell × CCell)) (k : ℕ) (b : CCell) : Bool :=
  F.any fun p ↦ p.1.bases.isEmpty && Nat.ble k p.1.off && Nat.blt p.1.off capE && p.2.beq b

/-- A base's exponent in sorted bases, `0` if absent. -/
def expOf : List (ℕ × ℕ) → ℕ → ℕ
  | [], _ => 0
  | (k, e) :: l, k' => bif Nat.beq k k' then e else expOf l k'

/-- The bases of `c` past those of `b`, divided by `S`. -/
def divB (b : List (ℕ × ℕ)) (S : ℕ) : List (ℕ × ℕ) → List (ℕ × ℕ)
  | [] => []
  | (k, e) :: l => bif Nat.blt (expOf b k) e then (k, (e - expOf b k) / S) :: divB b S l else divB b S l

/-- The index `J` with `c = b · J^S` if there is one (`ptIdx` multiplies back). -/
def idxOf (b c : CCell) (S : ℕ) : CCell := ⟨divB b.bases S c.bases, (c.off - b.off) / S⟩

/-- **A cell of a run at any index** `J` (`c = base · J^S`): below the upper bound by a fact
`(J, hi)`, past the lower bound (`g^0`, `J` itself, or a fact `(lo, J·g)`). -/
def ptIdx (F : List (CCell × CCell)) (R : PRun) (c J : CCell) : Bool :=
  c.beq (R.base.mul (J.pow R.stride)) && hasF F J R.hi &&
    ((R.lo.bases.isEmpty && Nat.beq R.lo.off 0) || R.lo.beq J || hasF F R.lo (J.shift 1))

/-- How many indices below the upper bound the cell `c` is: `k` with `c·g^(S·k) = base·hi^S`. -/
def backK (R : PRun) (c : CCell) : ℕ := ((R.base.mul (R.hi.pow R.stride)).off - c.off) / R.stride

/-- **A cell `k ≥ 1` indices below the upper bound** (`c·g^(S·k) = base·hi^S`): a constant lower bound
`lo` and a fact `(g^k', hi)`, `k' ≥ k - 1 + lo` (so `e(hi) - k` is past `lo`). -/
def ptBack (F : List (CCell × CCell)) (R : PRun) (c : CCell) : Bool :=
  Nat.blt 0 (backK R c) && (c.shift (R.stride * backK R c)).beq (R.base.mul (R.hi.pow R.stride)) &&
    R.lo.bases.isEmpty && Nat.blt R.lo.off capE && hasFC F (backK R c - 1 + R.lo.off) R.hi

/-- **A cell of a run in scope**: at its lower bound, the bounds a fact; or at a constant index past
a constant lower bound, below a constant upper bound or a fact's; or at any index (`ptIdx`); or some
indices below the upper bound (`ptBack`). -/
def ptRun (F : List (CCell × CCell)) (R : PRun) (c : CCell) : Bool :=
  (c.beq (R.base.mul (R.lo.pow R.stride)) && hasF F R.lo R.hi) || ptIdx F R c (idxOf R.base c R.stride) ||
  ptBack F R c ||
  (basesBeq c.bases R.base.bases && Nat.ble R.base.off c.off && !Nat.beq R.stride 0 &&
    Nat.beq ((c.off - R.base.off) % R.stride) 0 && R.lo.bases.isEmpty && Nat.blt R.lo.off capE &&
    Nat.ble R.lo.off ((c.off - R.base.off) / R.stride) &&
    ((R.hi.bases.isEmpty && Nat.blt R.hi.off capE && Nat.blt ((c.off - R.base.off) / R.stride) R.hi.off) ||
      hasFC F ((c.off - R.base.off) / R.stride) R.hi))

/-- The power `k` of `M` that `x` would be (by `M`'s first base, else its offset). -/
def powK (M x : CCell) : ℕ := match M.bases with
  | (b, e) :: _ => expOf x.bases b / e
  | [] => x.off / M.off

/-- `x = M^k` and `y = N^k` for the equation `(M, N)`. -/
def eqR (p : CCell × CCell) (x y : CCell) : Bool :=
  x.beq (p.1.pow (powK p.1 x)) && y.beq (p.2.pow (powK p.1 x))

/-- **Two monomials with one word**: equal, or powers of the two sides of an equation of `E` (`rename`:
a bound `M^k` with `M = g^c` is `g^(c·k)`). -/
def eqV (E : List (CCell × CCell)) (x y : CCell) : Bool :=
  x.beq y || E.any fun p ↦ eqR p x y || eqR (p.2, p.1) x y

/-- The lower bound of `Q` at or past that of `R`, its exponent existing. -/
def loOk (F : List (CCell × CCell)) (E : List (CCell × CCell)) (Q R : PRun) : Bool :=
  eqV E Q.lo R.lo ||
  (Q.lo.bases.isEmpty && R.lo.bases.isEmpty && Nat.ble R.lo.off Q.lo.off && Nat.blt Q.lo.off capE) ||
  (Q.lo.beq (R.lo.shift 1) && hasF F R.lo R.hi)

/-- The upper bound of `Q` at or below that of `R`, its exponent existing. -/
def hiOk (F : List (CCell × CCell)) (E : List (CCell × CCell)) (Q R : PRun) : Bool :=
  eqV E Q.hi R.hi || hasF F Q.hi R.hi ||
  (Nat.blt 0 Q.hi.off && hasF F ⟨Q.hi.bases, Q.hi.off - 1⟩ R.hi) ||
  (Q.hi.bases.isEmpty && R.hi.bases.isEmpty && Nat.ble Q.hi.off R.hi.off && Nat.blt R.hi.off capE) ||
  (Q.hi.bases.isEmpty && Nat.blt Q.hi.off capE && hasFC F (Q.hi.off - 1) R.hi) ||
  hasF F Q.hi (R.hi.shift 1)

/-- **A run inside a run in scope.** -/
def runRun (F : List (CCell × CCell)) (E : List (CCell × CCell)) (Q R : PRun) : Bool :=
  Q.base.beq R.base && Nat.beq Q.stride R.stride && loOk F E Q R && hiOk F E Q R

/-- **A run in scope rebased onto `Q`'s base**: its base `t` strides past `Q`'s, its lower bound a constant, `t` more
at most `Q`'s, a constant: its cells from `Q`'s lower bound to its upper bound, which are its own. -/
def shiftR (Q R : PRun) : Option PRun :=
  bif Nat.blt 0 Q.stride && Nat.beq Q.stride R.stride && basesBeq Q.base.bases R.base.bases &&
      Nat.ble Q.base.off R.base.off && Nat.beq ((R.base.off - Q.base.off) % Q.stride) 0 &&
      Q.lo.bases.isEmpty && R.lo.bases.isEmpty &&
      Nat.ble (R.lo.off + (R.base.off - Q.base.off) / Q.stride) Q.lo.off && Nat.blt Q.lo.off capE then
    some ⟨Q.base, Q.stride, Q.lo, R.hi⟩ else none

/-- **A run inside a run in scope**, or inside it rebased (`shiftR`). -/
def runRunS (F : List (CCell × CCell)) (E : List (CCell × CCell)) (Q R : PRun) : Bool :=
  match shiftR Q R with
  | some R2 => runRun F E Q R2
  | none => false

end

end LeanVM.Guest.CoreMode
