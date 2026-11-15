/-
  LeanVM.Guest.Backend.Complete.Frame

  The frame side of completeness, its foundation: frame words, pools on words, the constraint the
  walk of a path puts on its frame, and the placement primitives on the path.
-/

module

public import LeanVM.Guest.Backend.Complete.InFrame
public import LeanVM.Guest.Backend.Complete.Spec

/-!
# Frame words along a path

The frame side fixes, for one instance (a valuation `σ` whose path's events hold on the readers
`Rd`, at the frame `fp`), the words of its own frame cells. The walk of the placement builds them
on `σ`'s path as a **constraint** `C : (ℕ → E) → Prop` on the frame words: a cell taken fresh on
the path gets the word its instruction writes (`assign`), and `C` never mentions a cell from the
next free one on (`Blind C next`). Cells the walk gives out off the path (an arm not taken) get no
constraint, so the arms' rewind of the next free cell keeps `Blind`.

`PoolW Ψ` is soundness's `PoolOK` on the words `Ψ` instead of a memory: the pooled constants,
sums, products, shifted pointers and the frame's own pointer hold their relation on `Ψ`, and a
pooled load's cell holds the word every reader of the path's events gives at its address.

`FAt` is the on-path specification of a placement action: from a state whose constraint `C` is
satisfiable, blind from `next` on and keeps the pools, every success has a stronger constraint
with the same properties, and its result satisfies `R` under it.
-/

namespace LeanVM.Guest.Backend.Complete

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core

@[expose] public section

/-! ## Words -/

/-- The word of a place under the frame words `Ψ`. -/
def locW (Ψ : ℕ → E) : Loc → E
  | .cell n => Ψ n
  | .shifted n e => Ψ n * ofK (addressOfIndex e)

/-- One instance of a function: the valuation, the frame index, the readers the path's events hold
on, the frame size and header, and the words of the `SET` immediates of its straight-line
instructions (as the layout resolves them). -/
structure Inst where
  σ : Val
  fp : ℕ
  Rd : Reader → Prop
  size : ℕ
  hdr : E × E
  kw : KVal → E

/-- The frame pointer's word. -/
def Inst.fpw (I : Inst) : E := ofK (addressOfIndex I.fp)

/-- **The pools of a scope hold on the frame words `Ψ`.** -/
structure PoolW (I : Inst) (Ψ : ℕ → E) (sc : Scope) : Prop where
  consts : ∀ k o, sc.consts.get? k = some o → Ψ o = Guest.word k.1 k.2
  xors : ∀ k o, sc.xors.get? k = some o → Ψ o = Ψ k.1 + Ψ k.2
  muls : ∀ k o, sc.muls.get? k = some o → Ψ o = Ψ k.1 * Ψ k.2
  loads : ∀ k o, sc.loads.get? k = some o →
    IsInK (Ψ k.1) ∧ ∀ rd, I.Rd rd → rd ((Ψ k.1).limb 0 * addressOfIndex k.2) = some (Ψ o)
  mats : ∀ c l, sc.mats.get? c = some l → ∀ p ∈ l, Ψ p.2 = Ψ c * ofK (addressOfIndex p.1)
  selfFp : ∀ o, sc.selfFp = some o → Ψ o = I.fpw

/-! ## Constraints -/

/-- A constraint on frame words that mentions no cell from `n` on. -/
def Blind (C : (ℕ → E) → Prop) (n : ℕ) : Prop :=
  ∀ Ψ c w, n ≤ c → C Ψ → C (Function.update Ψ c w)

/-- A word computed from the cells below `n`. -/
def WBlind (w : (ℕ → E) → E) (n : ℕ) : Prop :=
  ∀ Ψ c x, n ≤ c → w (Function.update Ψ c x) = w Ψ

theorem Blind.mono {C : (ℕ → E) → Prop} {n n' : ℕ} (h : Blind C n) (hn : n ≤ n') : Blind C n' :=
  fun Ψ c w hc hC => h Ψ c w (le_trans hn hc) hC

theorem WBlind.mono {w : (ℕ → E) → E} {n n' : ℕ} (h : WBlind w n) (hn : n ≤ n') : WBlind w n' :=
  fun Ψ c x hc => h Ψ c x (le_trans hn hc)

theorem wblind_const (e : E) (n : ℕ) : WBlind (fun _ => e) n := fun _ _ _ _ => rfl

theorem wblind_cell {a n : ℕ} (ha : a < n) : WBlind (fun Ψ => Ψ a) n := fun Ψ c x hc => by
  show Function.update Ψ c x a = Ψ a
  rw [Function.update_of_ne (by omega)]

theorem wblind_add {w₁ w₂ : (ℕ → E) → E} {n : ℕ} (h₁ : WBlind w₁ n) (h₂ : WBlind w₂ n) :
    WBlind (fun Ψ => w₁ Ψ + w₂ Ψ) n := fun Ψ c x hc => by
  simp only [h₁ Ψ c x hc, h₂ Ψ c x hc]

theorem wblind_mul {w₁ w₂ : (ℕ → E) → E} {n : ℕ} (h₁ : WBlind w₁ n) (h₂ : WBlind w₂ n) :
    WBlind (fun Ψ => w₁ Ψ * w₂ Ψ) n := fun Ψ c x hc => by
  simp only [h₁ Ψ c x hc, h₂ Ψ c x hc]

/-- **A fresh cell gets a word**: the constraint with `Ψ o = w Ψ`, `o` past every cell `C`
mentions and `w` reads, is blind past `o` and as satisfiable as `C`. -/
theorem assign_blind {C : (ℕ → E) → Prop} {n o : ℕ} {w : (ℕ → E) → E} (hC : Blind C n)
    (hw : WBlind w o) (ho : n ≤ o) : Blind (fun Ψ => C Ψ ∧ Ψ o = w Ψ) (o + 1) := by
  intro Ψ c x hc ⟨h1, h2⟩
  refine ⟨hC Ψ c x (by omega) h1, ?_⟩
  rw [Function.update_of_ne (by omega), hw Ψ c x (by omega)]
  exact h2

theorem assign_sat {C : (ℕ → E) → Prop} {n o : ℕ} {w : (ℕ → E) → E} (hC : Blind C n)
    (hw : WBlind w o) (ho : n ≤ o) (hs : ∃ Ψ, C Ψ) : ∃ Ψ, C Ψ ∧ Ψ o = w Ψ := by
  obtain ⟨Ψ, h⟩ := hs
  refine ⟨Function.update Ψ o (w Ψ), hC Ψ o _ ho h, ?_⟩
  rw [Function.update_self, hw Ψ o _ le_rfl]

/-- A constraint the walk of a path keeps: satisfiable, blind from `n` on, every frame word it
allows keeps the pools of `sc`, and the pools' cells are past the header and below `n`. -/
structure COk (I : Inst) (C : (ℕ → E) → Prop) (n : ℕ) (sc : Scope) : Prop where
  sat : ∃ Ψ, C Ψ
  blind : Blind C n
  pools : ∀ Ψ, C Ψ → PoolW I Ψ sc
  cells : ScopeGood n sc

/-- The constraint `C'` is `C` or stronger. -/
def Stronger (C' C : (ℕ → E) → Prop) : Prop := ∀ Ψ, C' Ψ → C Ψ

theorem Stronger.refl (C : (ℕ → E) → Prop) : Stronger C C := fun _ h => h

theorem Stronger.trans {C₁ C₂ C₃ : (ℕ → E) → Prop} (h₁ : Stronger C₂ C₁) (h₂ : Stronger C₃ C₂) :
    Stronger C₃ C₁ := fun Ψ h => h₁ Ψ (h₂ Ψ h)

/-! ## Pools on words: inserts -/

section Inserts

variable {I : Inst} {Ψ : ℕ → E} {sc : Scope}

theorem PoolW.insertConst (h : PoolW I Ψ sc) {k : ℕ × ℕ} {o : Cell}
    (ho : Ψ o = Guest.word k.1 k.2) :
    PoolW I Ψ { sc with consts := sc.consts.insert k o } := by
  refine { h with consts := fun k' o' hk => ?_ }
  rw [PMap.get?_insert] at hk
  split at hk
  · next he => cases hk; subst he; exact ho
  · exact h.consts k' o' hk

theorem PoolW.insertConstIfNew (h : PoolW I Ψ sc) {k : ℕ × ℕ} {o : Cell}
    (ho : Ψ o = Guest.word k.1 k.2) :
    PoolW I Ψ { sc with consts := sc.consts.insertIfNew k o } := by
  refine { h with consts := fun k' o' hk => ?_ }
  rw [PMap.get?_insertIfNew] at hk
  split at hk
  · next he => cases hk; rw [he.1]; exact ho
  · exact h.consts k' o' hk

theorem PoolW.insertXor (h : PoolW I Ψ sc) {k : ℕ × ℕ} {o : Cell}
    (ho : Ψ o = Ψ k.1 + Ψ k.2) :
    PoolW I Ψ { sc with xors := sc.xors.insert k o } := by
  refine { h with xors := fun k' o' hk => ?_ }
  rw [PMap.get?_insert] at hk
  split at hk
  · next he => cases hk; subst he; exact ho
  · exact h.xors k' o' hk

theorem PoolW.insertMul (h : PoolW I Ψ sc) {k : ℕ × ℕ} {o : Cell}
    (ho : Ψ o = Ψ k.1 * Ψ k.2) :
    PoolW I Ψ { sc with muls := sc.muls.insert k o } := by
  refine { h with muls := fun k' o' hk => ?_ }
  rw [PMap.get?_insert] at hk
  split at hk
  · next he => cases hk; subst he; exact ho
  · exact h.muls k' o' hk

theorem PoolW.insertLoad (h : PoolW I Ψ sc) {k : ℕ × ℕ} {o : Cell}
    (ho : IsInK (Ψ k.1) ∧ ∀ rd, I.Rd rd → rd ((Ψ k.1).limb 0 * addressOfIndex k.2) = some (Ψ o)) :
    PoolW I Ψ { sc with loads := sc.loads.insertIfNew k o } := by
  refine { h with loads := fun k' o' hk => ?_ }
  rw [PMap.get?_insertIfNew] at hk
  split at hk
  · next he => cases hk; rw [he.1]; exact ho
  · exact h.loads k' o' hk

theorem PoolW.insertMats (h : PoolW I Ψ sc) {c : ℕ} {l : List (ℕ × Cell)}
    (hl : ∀ p ∈ l, Ψ p.2 = Ψ c * ofK (addressOfIndex p.1)) :
    PoolW I Ψ { sc with mats := sc.mats.insert c l } := by
  refine { h with mats := fun c' l' hc p hp => ?_ }
  rw [NMap.get?_insert] at hc
  split at hc
  · next he => cases hc; subst he; exact hl p hp
  · exact h.mats c' l' hc p hp

theorem PoolW.setSelfFp (h : PoolW I Ψ sc) {o : Cell} (ho : Ψ o = I.fpw) :
    PoolW I Ψ { sc with selfFp := some o } := by
  refine { h with selfFp := fun o' h' => ?_ }
  cases h'
  exact ho

end Inserts

/-! ## Straight-line instructions on frame words -/

/-- A reader holds the frame words `Ψ`: the header at cells `0`, `1`, `Ψ` from `2` to the frame
size. -/
def FrameRd (I : Inst) (Ψ : ℕ → E) (rd : Reader) : Prop :=
  rd (addressOfIndex (I.fp + 0)) = some I.hdr.1 ∧ rd (addressOfIndex (I.fp + 1)) = some I.hdr.2 ∧
    ∀ n, 2 ≤ n → n < I.size → rd (addressOfIndex (I.fp + n)) = some (Ψ n)

/-- The frame word of a cell: the header at `0`, `1`. -/
def fw (I : Inst) (Ψ : ℕ → E) (n : ℕ) : E :=
  if n = 0 then I.hdr.1 else if n = 1 then I.hdr.2 else Ψ n

/-- **What a straight-line instruction says of the frame words**, on every reader that holds them
and the path's events. -/
def OpW (I : Inst) (Ψ : ℕ → E) : LOp → Prop
  | .set o k => fw I Ψ o = I.kw k
  | .xor a b c => fw I Ψ c = fw I Ψ a + fw I Ψ b
  | .mul a b c => fw I Ψ c = fw I Ψ a * fw I Ψ b
  | .deref p off d .cell => IsInK (fw I Ψ p) ∧ ∀ rd, FrameRd I Ψ rd → I.Rd rd →
      rd ((fw I Ψ p).limb 0 * addressOfIndex off) = some (fw I Ψ d)
  | .deref p off _ .fp => IsInK (fw I Ψ p) ∧ ∀ rd, FrameRd I Ψ rd → I.Rd rd →
      rd ((fw I Ψ p).limb 0 * addressOfIndex off) = some I.fpw
  | .deref _ _ _ .pc => False
  | .jump oc od of => fw I Ψ oc = 0 ∧ IsInK (fw I Ψ od) ∧ IsInK (fw I Ψ of)
  | .keccak m0 m1 m2 m3 tail b8 cap out inOdd outOdd oc =>
      KeccakCellsRelation
        (fun c : Fin 13 => fw I Ψ (keccakInOff m0 m1 m2 m3 tail b8 cap c)) inOdd
        (fun c : Fin 13 => fw I Ψ (out + c.val)) outOdd oc
  | .slot _ _ _ => False
  | .mulNextFrame _ _ _ => False

/-! ## The on-path specification of a placement action -/

/-- The statements a walk emitted on the path from `st` to `st'`: straight-line instructions
only, each of whose relation holds on every frame word the constraint allows, once the frame
holds every cell given out (`st'.next ≤ I.size`). -/
def EmitsW (I : Inst) (C : (ℕ → E) → Prop) (st st' : St) : Prop :=
  ∃ ops : List PStmt, st'.out.toList = st.out.toList ++ ops ∧
    (st'.next ≤ I.size → ∀ s ∈ ops, ∃ h o, s = PStmt.op h o ∧ ∀ Ψ, C Ψ → OpW I Ψ o)

/-- **On `σ`'s path, every success of `m` from `st`** strengthens the constraint keeping it
satisfiable, blind from the next free cell on and true of the pools; emits straight-line
instructions whose relations the new constraint gives; does not move the next free cell back;
and its result satisfies `R` under the new constraint and the final state. -/
def FAt {α : Type} (ctx : Ctx) (I : Inst) (C : (ℕ → E) → Prop) (st : St) (m : P α)
    (R : α → ((ℕ → E) → Prop) → St → Prop) : Prop :=
  COk I C st.next st.scope →
  wpP m ctx st fun a st' => ∃ C', COk I C' st'.next st'.scope ∧ Stronger C' C ∧
    st.next ≤ st'.next ∧ EmitsW I C' st st' ∧ R a C' st'

/-- **The words of the values the walk knows on the path** (`ok`): each placed one is past the
header and below the next free cell, and its place holds its word under the constraint. -/
def VW (I : Inst) (C : (ℕ → E) → Prop) (st : St) (ok : V → Prop) : Prop :=
  ∀ v l, ok v → st.locs[v]? = some l →
    2 ≤ locBase l ∧ locBase l < st.next ∧ ∀ Ψ, C Ψ → locW Ψ l = I.σ v

/-- What the walk takes of an instance: some reader holds the path's events, and the layout
resolves a `SET` constant to its word and the frame size to `g^size`. -/
structure Inst.Ok (I : Inst) : Prop where
  rd : ∃ rd, I.Rd rd
  kconst : ∀ x y, I.kw (.const x y) = Guest.word x y
  ksize : I.kw .frameSize = ofK (addressOfIndex I.size)

/-- **The shape of an atom on the path** (`FrameAtoms.lean`): from a state whose known values
include the atom's (a copy dropped into a sponge alias apart), its event on every reader of the
path, an address's word being the frame address of its run's first cell, placing the atom keeps
the known values' words, knows the atom's values, keeps the places and leaves the trace. -/
def AtomFAt (a : Atom) : Prop :=
  ∀ (ctx : Ctx) (I : Inst) (C : (ℕ → E) → Prop) (st : St) (ok : V → Prop),
    I.Ok → (ctx.isMain = true → I.fp = 0) → (∀ rd, I.Rd rd → a.Holds rd I.σ) →
    (∀ p run r0 base, a = .frameAddr p run → run.head? = some r0 →
      st.locs[r0]? = some (.cell base) → I.σ p = ofK (addressOfIndex (I.fp + base))) →
    2 ≤ st.next → VW I C st ok →
    (∀ v ∈ Memory.atomUses a ++ Memory.atomTmps a, ok v ∨ ∃ s, a = .copy v s) →
    FAt ctx I C st (placeAtom a) fun _ C' st' =>
      VW I C' st' (fun v => ok v ∨ v ∈ Memory.atomUses a ++ Memory.atomTmps a) ∧
        st'.rest = st.rest ∧ ∀ (v : V) (l : Loc), st.locs[v]? = some l → st'.locs[v]? = some l

/-! ## Primitives on the path -/

section Prims

variable {ctx : Ctx} {I : Inst} {C : (ℕ → E) → Prop} {st : St}

theorem EmitsW.refl (st : St) : EmitsW I C st st := ⟨[], by simp, fun _ _ h => nomatch h⟩

theorem EmitsW.mono {C' : (ℕ → E) → Prop} {st st' : St} (h : EmitsW I C st st')
    (hs : Stronger C' C) : EmitsW I C' st st' := by
  obtain ⟨ops, ho, hops⟩ := h
  exact ⟨ops, ho, fun hz s hs' => by
    obtain ⟨hh, o, rfl, hw⟩ := hops hz s hs'
    exact ⟨hh, o, rfl, fun Ψ hΨ => hw Ψ (hs Ψ hΨ)⟩⟩

theorem EmitsW.trans {st₁ st₂ st₃ : St} (h₁ : EmitsW I C st₁ st₂) (h₂ : EmitsW I C st₂ st₃)
    (hn : st₂.next ≤ st₃.next) : EmitsW I C st₁ st₃ := by
  obtain ⟨ops₁, ho₁, hops₁⟩ := h₁
  obtain ⟨ops₂, ho₂, hops₂⟩ := h₂
  refine ⟨ops₁ ++ ops₂, by rw [ho₂, ho₁, List.append_assoc], fun hz s hs => ?_⟩
  rcases List.mem_append.mp hs with hs | hs
  · exact hops₁ (le_trans hn hz) s hs
  · exact hops₂ hz s hs

theorem FAt.pure {α : Type} {a : α} {R : α → ((ℕ → E) → Prop) → St → Prop} (h : R a C st) :
    FAt ctx I C st (Pure.pure a) R :=
  fun hc => wp_pure.mpr ⟨C, hc, Stronger.refl C, le_rfl, EmitsW.refl st, h⟩

theorem FAt.bind {α β : Type} {m : P α} {f : α → P β} {R₁ : α → ((ℕ → E) → Prop) → St → Prop}
    {R₂ : β → ((ℕ → E) → Prop) → St → Prop} (hm : FAt ctx I C st m R₁)
    (hf : ∀ a st' C', Stronger C' C → st.next ≤ st'.next → R₁ a C' st' →
      FAt ctx I C' st' (f a) R₂) :
    FAt ctx I C st (m >>= f) R₂ := by
  intro hc
  refine wp_bind.mpr fun a st₁ he b st₂ he' => ?_
  obtain ⟨C₁, hc₁, hs₁, hn₁, he₁, hr₁⟩ := hm hc a st₁ he
  obtain ⟨C₂, hc₂, hs₂, hn₂, he₂, hr₂⟩ := hf a st₁ C₁ hs₁ hn₁ hr₁ hc₁ b st₂ he'
  exact ⟨C₂, hc₂, hs₁.trans hs₂, le_trans hn₁ hn₂, (he₁.mono hs₂).trans he₂ hn₂, hr₂⟩

theorem FAt.get_bind {β : Type} {f : St → P β} {R : β → ((ℕ → E) → Prop) → St → Prop}
    (h : FAt ctx I C st (f st) R) : FAt ctx I C st (get >>= f) R :=
  fun hc => wp_bind.mpr (wp_get.mpr (h hc))

/-- A step that changes nothing the walk on the path reads. -/
theorem FAt.quiet {g : St → St} {R : PUnit → ((ℕ → E) → Prop) → St → Prop}
    (hn : (g st).next = st.next) (hs : (g st).scope = st.scope) (ho : (g st).out = st.out)
    (hr : R ⟨⟩ C (g st)) : FAt ctx I C st (modify g) R := fun hc =>
  wp_modify.mpr ⟨C, by rw [hn, hs]; exact hc, Stronger.refl C, le_of_eq hn.symm,
    ⟨[], by rw [ho]; simp, fun _ _ h => nomatch h⟩, hr⟩

/-- **A pooled constant on the path**: its cell, a good cell, holds the constant; the values'
places and the trace are as they were. -/
theorem constCell_fat (k : ℕ × ℕ) (hkw : I.kw (.const k.1 k.2) = Guest.word k.1 k.2)
    (h2 : 2 ≤ st.next) :
    FAt ctx I C st (constCell k) (fun o C' st' => 2 ≤ o ∧ o < st'.next ∧ st'.locs = st.locs ∧
      st'.rest = st.rest ∧ ∀ Ψ, C' Ψ → Ψ o = Guest.word k.1 k.2) := by
  intro hc
  unfold constCell fresh emitOp takeHints push
  refine wp_bind.mpr (wp_get.mpr ?_)
  split
  · next o ho =>
    exact wp_pure.mpr ⟨C, hc, Stronger.refl C, le_rfl, EmitsW.refl st,
      (hc.cells.consts k o ho).1, (hc.cells.consts k o ho).2, rfl, rfl,
      fun Ψ hΨ => (hc.pools Ψ hΨ).consts k o ho⟩
  · refine wp_bind.mpr (wp_modifyGet.mpr (wp_bind.mpr (wp_bind.mpr (wp_modifyGet.mpr
      (wp_modify.mpr (wp_bind.mpr (wp_modify.mpr (wp_pure.mpr ?_))))))))
    have hw : WBlind (fun _ => Guest.word k.1 k.2) st.next := wblind_const _ _
    have hg : GoodCell (st.next + 1) st.next := ⟨h2, Nat.lt_succ_self _⟩
    have hsc := hc.cells.mono (Nat.le_succ st.next)
    refine ⟨fun Ψ => C Ψ ∧ Ψ st.next = Guest.word k.1 k.2, ⟨assign_sat hc.blind hw le_rfl hc.sat,
      assign_blind hc.blind hw le_rfl, fun Ψ hΨ => (hc.pools Ψ hΨ.1).insertConst hΨ.2,
      { hsc with consts := pmap_insert_imp hsc.consts hg }⟩,
      fun Ψ h => h.1, Nat.le_succ _, ?_, h2, Nat.lt_succ_self _, rfl, rfl, fun Ψ h => h.2⟩
    refine ⟨[.op st.pending.toList (.set st.next (.const k.1 k.2))], by simp, fun _ s' hs' => ?_⟩
    rw [List.mem_singleton] at hs'
    subst hs'
    refine ⟨_, _, rfl, fun Ψ hΨ => ?_⟩
    show fw I Ψ st.next = I.kw (.const k.1 k.2)
    have h0 : st.next ≠ 0 := by have := h2; simp only [Cell] at *; omega
    have h1 : st.next ≠ 1 := by have := h2; simp only [Cell] at *; omega
    rw [hkw, fw, ite_eq_right_iff.mpr (fun h => absurd h h0), ite_eq_right_iff.mpr (fun h => absurd h h1)]
    exact hΨ.2

end Prims

end
end LeanVM.Guest.Backend.Complete
