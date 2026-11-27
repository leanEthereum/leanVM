/-
  LeanVM.Guest.Local.Layout

  A compiled function's code cut along its core body's blocks: each block a code range, nested as
  the blocks are, and every offset in the innermost block whose range holds it. Checked by the
  kernel from a few small records, and what it gives a run.
-/

module

public import LeanVM.Guest.Packed.PTree
public import LeanVM.Guest.Local.Pos

/-!
# The layout of a compiled function

The compiler lays a core body out structured: an `ite` is its branch, the zero arm, a jump to the
join, the nonzero arm; a `match` is its table jump and its arms in order; a call returns to the
offset after its jump. So the body's blocks (the body, each arm of an `ite` or a `match`) are
code ranges nested as the blocks are, and an offset of a block's range outside its arms' ranges
is on the block's own path: it runs whenever the block is entered. A local certificate names
offsets (the instruction an atom rests on, the one that set a cell a jump reads) and needs to
know, in a few lookups, that they ran.

**Blocks.** A layout numbers the blocks in pre-order, the body `0`. Block `b`'s record
(`Block`, a slot of `blockW` bits of the tree `blocks`) holds its parent `par`, the end `hi` of
its subtree's numbers (so `a` is an ancestor of `b`, or `b`, exactly when `a ≤ b < hi a`,
`Anc`), its code range `[cs, ce)`, and its place in the core body in `Pos.lean`'s positions: its
context `⟨se, br, sa⟩` (`Block.ctx`: its first position `sa`, its end `se`, its branch `br`),
its `kind` (`kindBody`, …) and its arm index.

**Runs.** The code offsets `[0, n)` are cut into runs (`Run`, slots of `runW` bits of `runs`),
in code order: run `r` holds the offsets from its start `x` to the next run's (`n` for the last,
`rEnd`), all on the path of its block `b`. `pv` is the last child of `b` whose range ends at or
before the run (or `b` itself): the run meets none of `b`'s children's ranges.

**The check.** `ok` reads each block's and each run's record once, with the records it names:
the root's range is `[0, n)`; a block's parent comes before it, its subtree and range inside its
parent's; its first child (`b + 1`, when `b + 1 < hi b`) and its next sibling (`hi b`, when inside
its parent's subtree) name it and its parent as theirs, the sibling's range after its; each run
starts where the last ended, inside its block's range, clear of its block's children's.

**What it gives** (`ok` true):

* `anc_range`: an ancestor's range holds its descendants'; `disjoint`: two blocks neither of
  which is the other's ancestor have disjoint ranges.
* `run_exists`, `run_unique`: every offset below `n` is in exactly one run.
* `run_inner` (**innermost**): an offset's run's block is a descendant of every block whose range
  holds the offset, so its range is inside theirs (`run_sub`).
* `visits` (**the soundness reading**): a run of the machine is a strictly increasing list of
  offsets (`Hops`), each hop skipping only offsets whose blocks' ranges hold neither of its ends
  (the arms a branch or a join jumps over); then it passes every offset `w` between its first and
  last whose block's range holds its first or its last offset. So an instruction on the path of
  the current block, or of an ancestor before the current block's start, ran (dominance), and
  every instruction on a block's path runs before the run leaves the block's range
  (post-dominance).
* The completeness reading is `run_inner` and the blocks' contexts: a statement in scope of a
  block is one of its own or of its ancestors (`Anc` on block numbers), whose code is on the path.

The tables are `PTree`s (`Packed/PTree.lean`) read by key; the generator (`guest-cert`) writes a
function's layout into its pack, and the families' checks read it. Nothing here is trusted: a
wrong record fails `ok`.
-/

namespace LeanVM.Guest.Local

open LeanVM.Guest.Packed

@[expose] public section

/-! ## Records -/

/-- Bits `[o, o + k)` of `x`. -/
def fld (x o k : ℕ) : ℕ := Nat.mod (Nat.shiftRight x o) (Nat.pow 2 k)

/-- A block's record. -/
structure Block where
  /-- The parent (the body's is itself). -/
  par : ℕ
  /-- One past the last block of its subtree. -/
  hi : ℕ
  /-- Its code range, `[cs, ce)`. -/
  cs : ℕ
  ce : ℕ
  /-- Its first position, its end and its branch's position (`Pos.lean`). -/
  sa : ℕ
  se : ℕ
  br : ℕ
  /-- `kindBody`, `kindZero`, `kindNonzero`, `kindArm`. -/
  kind : ℕ
  /-- Its arm's index in its branch. -/
  arm : ℕ

def kindBody : ℕ := 0
def kindZero : ℕ := 1
def kindNonzero : ℕ := 2
def kindArm : ℕ := 3

/-- The width of a block's slot: `par` 16 bits, `hi` 16, `cs` 20, `ce` 20, `sa` 20, `se` 20,
`br` 20, `kind` 4, `arm` 12, and the slot's own bit. -/
def blockW : ℕ := 150

/-- A block's record from its bits. -/
def Block.ofNat (x : ℕ) : Block :=
  ⟨fld x 0 16, fld x 16 16, fld x 32 20, fld x 52 20, fld x 72 20, fld x 92 20, fld x 112 20,
    fld x 132 4, fld x 136 12⟩

/-- A block's context in its body (`Pos.Ctx`): its end, its branch, its first position. -/
def Block.ctx (B : Block) : Ctx := ⟨B.se, B.br, B.sa⟩

/-- A run's record: its first offset `x`, its block `b`, and `pv`, the last child of `b` whose
range ends at or before `x`, or `b`. -/
structure Run where
  x : ℕ
  b : ℕ
  pv : ℕ

/-- The width of a run's slot: `x` 20 bits, `b` 16, `pv` 16, and the slot's own bit. -/
def runW : ℕ := 53

def Run.ofNat (y : ℕ) : Run := ⟨fld y 0 20, fld y 20 16, fld y 36 16⟩

/-- A compiled function's layout. -/
structure Layout where
  /-- Its number of instructions. -/
  n : ℕ
  /-- Its number of blocks. -/
  nb : ℕ
  /-- Its number of runs. -/
  nr : ℕ
  blocks : PTree
  runs : PTree

namespace Layout

variable (L : Layout)

/-- Block `b`'s record. -/
noncomputable def blk (b : ℕ) : Block := Block.ofNat ((PTree.get blockW L.blocks b).getD 0)

/-- Run `r`'s record. -/
noncomputable def run (r : ℕ) : Run := Run.ofNat ((PTree.get runW L.runs r).getD 0)

/-- The offset run `r` ends at: the next run's start, `n` for the last. -/
noncomputable def rEnd (r : ℕ) : ℕ := bif Nat.blt (r + 1) L.nr then (L.run (r + 1)).x else L.n

/-- `p k` for every `k < n`. -/
def allBelow (p : ℕ → Bool) (n : ℕ) : Bool := Nat.rec (motive := fun _ ↦ Bool) true (fun k r ↦ p k && r) n

/-- Block `c`'s record, against its parent's, its first child's and its next sibling's. -/
noncomputable def okBlock (c : ℕ) : Bool :=
  let B := L.blk c
  let P := L.blk B.par
  (bif Nat.beq c 0 then
    Nat.beq B.par 0 && Nat.beq B.hi L.nb && Nat.beq B.cs 0 && Nat.beq B.ce L.n
  else
    Nat.blt B.par c && Nat.blt c B.hi && Nat.ble B.hi P.hi && Nat.ble P.cs B.cs && Nat.ble B.cs B.ce &&
      Nat.ble B.ce P.ce &&
      (bif Nat.blt B.hi P.hi then Nat.beq (L.blk B.hi).par B.par && Nat.ble B.ce (L.blk B.hi).cs
        else true)) &&
  (bif Nat.blt (c + 1) B.hi then Nat.beq (L.blk (c + 1)).par c else true)

/-- Run `r`'s record: after the last, inside its block's range, clear of its block's children's. -/
noncomputable def okRun (r : ℕ) : Bool :=
  let R := L.run r
  let e := L.rEnd r
  let B := L.blk R.b
  (bif Nat.beq r 0 then Nat.beq R.x 0 else true) && Nat.blt R.x e && Nat.blt R.b L.nb &&
    Nat.ble B.cs R.x && Nat.ble e B.ce &&
    (bif Nat.beq R.pv R.b then
      (bif Nat.blt (R.b + 1) B.hi then Nat.ble e (L.blk (R.b + 1)).cs else true)
    else
      let V := L.blk R.pv
      Nat.blt R.pv L.nb && Nat.beq V.par R.b && Nat.ble V.ce R.x &&
        (bif Nat.blt V.hi B.hi then Nat.ble e (L.blk V.hi).cs else true))

/-- **The layout's check.** -/
noncomputable def ok : Bool :=
  Nat.blt 0 L.nb && Nat.blt 0 L.nr && allBelow L.okBlock L.nb && allBelow L.okRun L.nr

/-! ## What the check says -/

/-- `a` is `b` or an ancestor of `b`. -/
def Anc (a b : ℕ) : Prop := a ≤ b ∧ b < (L.blk a).hi

/-- Offset `y` is in block `b`'s range. -/
def InRange (b y : ℕ) : Prop := (L.blk b).cs ≤ y ∧ y < (L.blk b).ce

/-- Offset `y` is in run `r`. -/
def InRun (r y : ℕ) : Prop := r < L.nr ∧ (L.run r).x ≤ y ∧ y < L.rEnd r

end Layout

end

namespace Layout

public section

variable {L : Layout}

theorem allBelow_iff {p : ℕ → Bool} {n : ℕ} : allBelow p n = true ↔ ∀ k < n, p k = true := by
  induction n with
  | zero => simp [allBelow]
  | succ n ih =>
    show (p n && allBelow p n) = true ↔ _
    rw [Bool.and_eq_true, ih]
    constructor
    · rintro ⟨h1, h2⟩ k hk
      rcases Nat.lt_succ_iff_lt_or_eq.1 hk with hk | rfl
      · exact h2 k hk
      · exact h1
    · intro h; exact ⟨h n (by omega), fun k hk ↦ h k (by omega)⟩

theorem blt_t {a b : ℕ} (h : a < b) : Nat.blt a b = true := by rw [Nat.blt_eq]; exact h
theorem blt_f {a b : ℕ} (h : ¬ a < b) : Nat.blt a b = false := by
  cases hb : Nat.blt a b
  · rfl
  · rw [Nat.blt_eq] at hb; exact absurd hb h
theorem beq_t {a b : ℕ} (h : a = b) : Nat.beq a b = true := by rw [Nat.beq_eq]; exact h
theorem beq_f {a b : ℕ} (h : a ≠ b) : Nat.beq a b = false := by
  cases hb : Nat.beq a b
  · rfl
  · exact absurd (Nat.eq_of_beq_eq_true hb) h

theorem rEnd_succ {r : ℕ} (hr : r + 1 < L.nr) : L.rEnd r = (L.run (r + 1)).x := by
  simp only [rEnd, blt_t hr, Bool.cond_true]

theorem rEnd_last {r : ℕ} (hr : ¬ r + 1 < L.nr) : L.rEnd r = L.n := by
  simp only [rEnd, blt_f hr, Bool.cond_false]

section Facts

variable (h : L.ok = true)
include h

theorem nb_pos : 0 < L.nb := by
  simp only [ok, Bool.and_eq_true, Nat.blt_eq] at h; exact h.1.1.1

theorem nr_pos : 0 < L.nr := by
  simp only [ok, Bool.and_eq_true, Nat.blt_eq] at h; exact h.1.1.2

theorem okBlock_of {c : ℕ} (hc : c < L.nb) : L.okBlock c = true := by
  simp only [ok, Bool.and_eq_true] at h; exact allBelow_iff.1 h.1.2 c hc

theorem okRun_of {r : ℕ} (hr : r < L.nr) : L.okRun r = true := by
  simp only [ok, Bool.and_eq_true] at h; exact allBelow_iff.1 h.2 r hr

/-- The body's record. -/
theorem root : (L.blk 0).par = 0 ∧ (L.blk 0).hi = L.nb ∧ (L.blk 0).cs = 0 ∧ (L.blk 0).ce = L.n := by
  have := okBlock_of h (nb_pos h)
  simp only [okBlock, Nat.beq_refl, Bool.cond_true, Bool.and_eq_true, Nat.beq_eq] at this
  obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, -⟩ := this
  exact ⟨h1, h2, h3, h4⟩

/-- A block's record against its parent's. -/
theorem blk_par {c : ℕ} (hc : c < L.nb) (h0 : 0 < c) :
    (L.blk c).par < c ∧ c < (L.blk c).hi ∧ (L.blk c).hi ≤ (L.blk (L.blk c).par).hi ∧
      (L.blk (L.blk c).par).cs ≤ (L.blk c).cs ∧ (L.blk c).cs ≤ (L.blk c).ce ∧
      (L.blk c).ce ≤ (L.blk (L.blk c).par).ce := by
  have := okBlock_of h hc
  have hb : Nat.beq c 0 = false := beq_f (by omega)
  simp only [okBlock, hb, Bool.cond_false, Bool.and_eq_true, Nat.blt_eq, Nat.ble_eq] at this
  obtain ⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, -⟩, -⟩ := this
  exact ⟨h1, h2, h3, h4, h5, h6⟩

/-- A block's next sibling, inside its parent's subtree. -/
theorem blk_next {c : ℕ} (hc : c < L.nb) (h0 : 0 < c) (hs : (L.blk c).hi < (L.blk (L.blk c).par).hi) :
    (L.blk (L.blk c).hi).par = (L.blk c).par ∧ (L.blk c).ce ≤ (L.blk (L.blk c).hi).cs := by
  have := okBlock_of h hc
  have hb : Nat.beq c 0 = false := beq_f (by omega)
  have hs' : Nat.blt (L.blk c).hi (L.blk (L.blk c).par).hi = true := blt_t hs
  simp only [okBlock, hb, hs', Bool.cond_false, Bool.cond_true, Bool.and_eq_true, Nat.blt_eq,
    Nat.ble_eq, Nat.beq_eq] at this
  exact this.1.2

/-- A block's first child. -/
theorem blk_first {c : ℕ} (hc : c < L.nb) (hs : c + 1 < (L.blk c).hi) : (L.blk (c + 1)).par = c := by
  have := okBlock_of h hc
  have hs' : Nat.blt (c + 1) (L.blk c).hi = true := blt_t hs
  simp only [okBlock, hs', Bool.cond_true, Bool.and_eq_true, Nat.beq_eq] at this
  exact this.2

theorem self_lt_hi {c : ℕ} (hc : c < L.nb) : c < (L.blk c).hi := by
  rcases Nat.eq_zero_or_pos c with rfl | h0
  · rw [(root h).2.1]; exact hc
  · exact (blk_par h hc h0).2.1

/-- Every subtree ends by `nb`. -/
theorem hi_le : ∀ c, c < L.nb → (L.blk c).hi ≤ L.nb := by
  intro c
  induction c using Nat.strong_induction_on with
  | _ c ih =>
    intro hc
    rcases Nat.eq_zero_or_pos c with rfl | h0
    · exact (root h).2.1.le
    · have := blk_par h hc h0
      exact this.2.2.1.trans (ih _ this.1 (by omega))

/-- A child of `a` whose subtree holds `x`, from a child `k ≤ x`, along `k`'s next siblings. -/
theorem kid_from {a x : ℕ} (ha : a < L.nb) (hx : x < (L.blk a).hi) :
    ∀ m k, x - k = m → 0 < k → (L.blk k).par = a → k ≤ x → k < L.nb →
      ∃ k', 0 < k' ∧ (L.blk k').par = a ∧ k' ≤ x ∧ x < (L.blk k').hi ∧ k' < L.nb := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    intro k hm hk0 hka hkx hkn
    by_cases hxk : x < (L.blk k).hi
    · exact ⟨k, hk0, hka, hkx, hxk, hkn⟩
    · have hp := blk_par h hkn hk0
      rw [hka] at hp
      have hlt : (L.blk k).hi < (L.blk (L.blk k).par).hi := by rw [hka]; omega
      have hn := blk_next h hkn hk0 hlt
      rw [hka] at hn
      have hn' : (L.blk k).hi < L.nb := by have := hi_le h a ha; omega
      exact ih (x - (L.blk k).hi) (by omega) _ rfl (by omega) hn.1 (by omega) hn'

/-- **A block's children cover its subtree**: every block after `a` in it is in the subtree of
a child of `a`. -/
theorem kid {a x : ℕ} (ha : a < L.nb) (h1 : a < x) (hx : x < (L.blk a).hi) :
    ∃ k, 0 < k ∧ (L.blk k).par = a ∧ k ≤ x ∧ x < (L.blk k).hi ∧ k < L.nb :=
  kid_from h ha hx _ (a + 1) rfl (by omega) (blk_first h ha (by omega)) (by omega)
    (by have := hi_le h a ha; omega)

/-- A block's parent is in the subtree of every block whose subtree holds it, above it. -/
theorem par_in : ∀ (m a : ℕ), (L.blk a).hi - a = m → a < L.nb → ∀ c, a < c → c < (L.blk a).hi →
    a ≤ (L.blk c).par ∧ (L.blk c).par < (L.blk a).hi := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    intro a hm ha c h1 h2
    obtain ⟨k, hk0, hka, hkc, hck, hkn⟩ := kid h ha h1 h2
    have hp := blk_par h hkn hk0
    rw [hka] at hp
    rcases Nat.eq_or_lt_of_le hkc with rfl | hlt
    · rw [hka]; omega
    · have := ih _ (by omega) k rfl hkn c hlt hck
      omega

theorem anc_par {a c : ℕ} (ha : a < L.nb) (h1 : a < c) (h2 : c < (L.blk a).hi) :
    a ≤ (L.blk c).par ∧ (L.blk c).par < (L.blk a).hi :=
  par_in h _ a rfl ha c h1 h2

/-- **Subtrees nest.** -/
theorem anc_hi : ∀ c a, a < L.nb → L.Anc a c → c < L.nb → (L.blk c).hi ≤ (L.blk a).hi := by
  intro c
  induction c using Nat.strong_induction_on with
  | _ c ih =>
    intro a ha hac hc
    rcases Nat.eq_or_lt_of_le hac.1 with rfl | hlt
    · exact le_rfl
    · have hp := blk_par h hc (by omega)
      have hpa := anc_par h ha hlt hac.2
      rcases Nat.eq_or_lt_of_le hpa.1 with he | hlt'
      · rw [he]; exact hp.2.2.1
      · exact hp.2.2.1.trans (ih _ hp.1 a ha ⟨hlt'.le, hpa.2⟩ (by omega))

/-- **An ancestor's range holds its descendants'.** -/
theorem anc_range : ∀ c a, a < L.nb → L.Anc a c → c < L.nb →
    (L.blk a).cs ≤ (L.blk c).cs ∧ (L.blk c).ce ≤ (L.blk a).ce := by
  intro c
  induction c using Nat.strong_induction_on with
  | _ c ih =>
    intro a ha hac hc
    rcases Nat.eq_or_lt_of_le hac.1 with rfl | hlt
    · exact ⟨le_rfl, le_rfl⟩
    · have hp := blk_par h hc (by omega)
      have hpa := anc_par h ha hlt hac.2
      have := ih _ hp.1 a ha ⟨hpa.1, hpa.2⟩ (by omega)
      exact ⟨this.1.trans hp.2.2.2.1, hp.2.2.2.2.2.trans this.2⟩

/-- Two children of one block: the earlier's subtree ends before the later. -/
theorem sib_hi {b d d' : ℕ} (hd : d < L.nb) (hd0 : 0 < d) (hpd : (L.blk d).par = b)
    (hpd' : (L.blk d').par = b) (hdd : d < d') : (L.blk d).hi ≤ d' := by
  by_contra hc
  have := anc_par h hd hdd (by omega)
  have := (blk_par h hd hd0).1
  omega

/-- **Siblings' ranges are in order.** -/
theorem sib_range : ∀ m d d' b, d' - d = m → d < L.nb → d' < L.nb → 0 < d → 0 < d' →
    (L.blk d).par = b → (L.blk d').par = b → d < d' → (L.blk d).ce ≤ (L.blk d').cs := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    intro d d' b hm hd hd' hd0 hd0' hpd hpd' hdd
    have hs := sib_hi h hd hd0 hpd hpd' hdd
    have hp' := blk_par h hd' hd0'
    rw [hpd'] at hp'
    have hp := blk_par h hd hd0
    rw [hpd] at hp
    have hlt : (L.blk d).hi < (L.blk (L.blk d).par).hi := by rw [hpd]; omega
    have hn := blk_next h hd hd0 hlt
    rw [hpd] at hn
    rcases Nat.eq_or_lt_of_le hs with he | hlt'
    · rw [← he]; exact hn.2
    · have hhn : (L.blk d).hi < L.nb := by omega
      have h2 := ih _ (by omega) _ d' b rfl hhn hd' (by omega) hd0' hn.1 hpd' hlt'
      have h3 := (blk_par h hhn (by omega)).2.2.2.2.1
      omega

/-- **Blocks neither of which is the other's ancestor have disjoint ranges**: the earlier's ends
before the later's starts. -/
theorem disjoint_from : ∀ (m g : ℕ), (L.blk g).hi - g = m → g < L.nb → ∀ a c, L.Anc g a → L.Anc g c →
    a < c → ¬ L.Anc a c → a < L.nb → c < L.nb → (L.blk a).ce ≤ (L.blk c).cs := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    intro g hm hg a c hga hgc hac hnac ha hc
    have hga' : g < a := by
      rcases Nat.eq_or_lt_of_le hga.1 with rfl | h'
      · exact absurd hgc hnac
      · exact h'
    obtain ⟨d, hd0, hdp, hda, had, hdn⟩ := kid h hg hga' hga.2
    have hdhi := blk_par h hdn hd0
    rw [hdp] at hdhi
    by_cases hdc : L.Anc d c
    · exact ih _ (by omega) d rfl hdn a c ⟨hda, had⟩ hdc hac hnac ha hc
    · have hgc' : g < c := by omega
      obtain ⟨d', hd0', hdp', hdc', hcd', hdn'⟩ := kid h hg hgc' hgc.2
      have hne : d ≠ d' := fun e ↦ hdc (e ▸ ⟨hdc', hcd'⟩)
      have hlt : d < d' := by
        rcases Nat.lt_or_gt_of_ne hne with h1 | h1
        · exact h1
        · have := sib_hi h hdn' hd0' hdp' hdp h1
          omega
      have h1 := sib_range h _ d d' g rfl hdn hdn' hd0 hd0' hdp hdp' hlt
      have h2 := anc_range h a d hdn ⟨hda, had⟩ ha
      have h3 := anc_range h c d' hdn' ⟨hdc', hcd'⟩ hc
      have h4 := (blk_par h hdn hd0).2.2.2.2.1
      omega

theorem anc_root {a : ℕ} (ha : a < L.nb) : L.Anc 0 a :=
  show 0 ≤ a ∧ a < (L.blk 0).hi from ⟨Nat.zero_le _, by rw [(root h).2.1]; exact ha⟩

theorem disjoint {a c : ℕ} (hac : a < c) (hnac : ¬ L.Anc a c) (ha : a < L.nb) (hc : c < L.nb) :
    (L.blk a).ce ≤ (L.blk c).cs :=
  disjoint_from h _ 0 rfl (nb_pos h) a c (anc_root h ha) (anc_root h hc) hac hnac ha hc

/-! ## Runs -/

theorem run_facts {r : ℕ} (hr : r < L.nr) :
    (r = 0 → (L.run r).x = 0) ∧ (L.run r).x < L.rEnd r ∧ (L.run r).b < L.nb ∧
      (L.blk (L.run r).b).cs ≤ (L.run r).x ∧ L.rEnd r ≤ (L.blk (L.run r).b).ce := by
  have := okRun_of h hr
  simp only [okRun, Bool.and_eq_true, Nat.blt_eq, Nat.ble_eq] at this
  obtain ⟨⟨⟨⟨⟨h0, h1⟩, h2⟩, h3⟩, h4⟩, -⟩ := this
  refine ⟨fun e ↦ ?_, h1, h2, h3, h4⟩
  subst e
  simpa using h0

/-- **A run meets none of its block's children's ranges.** -/
theorem run_kids {r d : ℕ} (hr : r < L.nr) (hd : d < L.nb) (hd0 : 0 < d) (hdp : (L.blk d).par = (L.run r).b) :
    (L.blk d).ce ≤ (L.run r).x ∨ L.rEnd r ≤ (L.blk d).cs := by
  have hf := run_facts h hr
  have hok := okRun_of h hr
  set b := (L.run r).b with hb
  have hdb := blk_par h hd hd0
  rw [hdp] at hdb
  by_cases hpv : (L.run r).pv = b
  · have hpv' : Nat.beq (L.run r).pv b = true := beq_t hpv
    simp only [okRun, ← hb, hpv', Bool.cond_true, Bool.and_eq_true] at hok
    have hk := hok.2
    by_cases hk1 : b + 1 < (L.blk b).hi
    · have hk1' : Nat.blt (b + 1) (L.blk b).hi = true := blt_t hk1
      rw [hk1', Bool.cond_true, Nat.ble_eq] at hk
      right
      have hb1 : b + 1 < L.nb := by have := hi_le h b hf.2.2.1; omega
      have hp1 := blk_first h hf.2.2.1 hk1
      rcases Nat.eq_or_lt_of_le (show b + 1 ≤ d by omega) with he | hlt
      · rw [← he]; exact hk
      · have := sib_range h _ (b + 1) d b rfl hb1 hd (by omega) hd0 hp1 hdp hlt
        have := (blk_par h hb1 (by omega)).2.2.2.2.1
        omega
    · omega
  · have hpv' : Nat.beq (L.run r).pv b = false := beq_f hpv
    simp only [okRun, ← hb, hpv', Bool.cond_false, Bool.and_eq_true, Nat.blt_eq, Nat.ble_eq,
      Nat.beq_eq] at hok
    obtain ⟨-, ⟨⟨hpvn, hpvp⟩, hpvc⟩, hnext⟩ := hok
    set v := (L.run r).pv
    have hv0 : 0 < v := by
      rcases Nat.eq_zero_or_pos v with he | hp
      · rw [he, (root h).1] at hpvp; exact absurd (he.trans hpvp) hpv
      · exact hp
    have hvb := blk_par h hpvn hv0
    rw [hpvp] at hvb
    rcases Nat.lt_trichotomy d v with hlt | he | hgt
    · left
      have := sib_range h _ d v b rfl hd hpvn hd0 hv0 hdp hpvp hlt
      omega
    · left; rw [he]; exact hpvc
    · right
      have hs := sib_hi h hpvn hv0 hpvp hdp hgt
      by_cases hn : (L.blk v).hi < (L.blk b).hi
      · have hn' : Nat.blt (L.blk v).hi (L.blk b).hi = true := blt_t hn
        rw [hn', Bool.cond_true, Nat.ble_eq] at hnext
        have hlt : (L.blk v).hi < (L.blk (L.blk v).par).hi := by rw [hpvp]; exact hn
        have hnx := blk_next h hpvn hv0 hlt
        rw [hpvp] at hnx
        have hhn : (L.blk v).hi < L.nb := by omega
        rcases Nat.eq_or_lt_of_le hs with he | hlt'
        · rw [← he]; exact hnext
        · have := sib_range h _ _ d b rfl hhn hd (by omega) hd0 hnx.1 hdp hlt'
          have := (blk_par h hhn (by omega)).2.2.2.2.1
          omega
      · omega

/-- **Innermost**: a run's block is a descendant of every block whose range holds an offset of
the run. -/
theorem run_inner {r y c : ℕ} (hr : L.InRun r y) (hy : L.InRange c y) (hc : c < L.nb) :
    L.Anc c (L.run r).b := by
  have hf := run_facts h hr.1
  set b := (L.run r).b
  rcases Nat.lt_trichotomy c b with hlt | he | hgt
  · by_contra hn
    have := disjoint h hlt hn hc hf.2.2.1
    have := hy.2; have := hr.2.1; omega
  · rw [he]; exact ⟨le_rfl, self_lt_hi h hf.2.2.1⟩
  · by_cases hbc : L.Anc b c
    · obtain ⟨d, hd0, hdp, hdc, hcd, hdn⟩ := kid h hf.2.2.1 hgt hbc.2
      have hk := run_kids h hr.1 hdn hd0 hdp
      have := anc_range h c d hdn ⟨hdc, hcd⟩ hc
      have := hy.1; have := hy.2; have := hr.2.1; have := hr.2.2
      omega
    · have := disjoint h hgt hbc hf.2.2.1 hc
      have := hy.1; have := hr.2.2; omega

/-- The offsets of a run are in its block's range. -/
theorem run_range {r y : ℕ} (hr : L.InRun r y) : L.InRange (L.run r).b y := by
  have hf := run_facts h hr.1
  exact ⟨hf.2.2.2.1.trans hr.2.1, lt_of_lt_of_le hr.2.2 hf.2.2.2.2⟩

/-- **A run's block's range is inside every range that holds an offset of the run.** -/
theorem run_sub {r y c : ℕ} (hr : L.InRun r y) (hy : L.InRange c y) (hc : c < L.nb) :
    (L.blk c).cs ≤ (L.blk (L.run r).b).cs ∧ (L.blk (L.run r).b).ce ≤ (L.blk c).ce :=
  anc_range h _ c hc (run_inner h hr hy hc) (run_facts h hr.1).2.2.1

/-- Runs are in order. -/
theorem run_mono : ∀ k r, r + 1 + k < L.nr → L.rEnd r ≤ (L.run (r + 1 + k)).x := by
  intro k
  induction k with
  | zero => intro r hr; exact (rEnd_succ hr).le
  | succ k ih =>
    intro r hr
    have := ih r (by omega)
    have := (run_facts h (r := r + 1 + k) (by omega)).2.1
    rw [rEnd_succ (show r + 1 + k + 1 < L.nr by omega)] at this
    rw [show r + 1 + (k + 1) = r + 1 + k + 1 by omega]
    omega

/-- **An offset is in one run at most.** -/
theorem run_unique {r r' y : ℕ} (hr : L.InRun r y) (hr' : L.InRun r' y) : r = r' := by
  by_contra hne
  rcases Nat.lt_or_gt_of_ne hne with hlt | hlt
  · have := run_mono h (r' - r - 1) r (by have := hr'.1; omega)
    rw [show r + 1 + (r' - r - 1) = r' by omega] at this
    have := hr.2.2; have := hr'.2.1; omega
  · have := run_mono h (r - r' - 1) r' (by have := hr.1; omega)
    rw [show r' + 1 + (r - r' - 1) = r by omega] at this
    have := hr'.2.2; have := hr.2.1; omega

/-- **Every offset below `n` is in a run.** -/
theorem run_exists {y : ℕ} (hy : y < L.n) : ∃ r, L.InRun r y := by
  have key : ∀ k r, r + k + 1 = L.nr → (L.run r).x ≤ y → ∃ r', L.InRun r' y := by
    intro k
    induction k with
    | zero =>
      intro r hr hx
      exact ⟨r, by omega, hx, by rw [rEnd_last (by omega)]; exact hy⟩
    | succ k ih =>
      intro r hr hx
      by_cases he : y < L.rEnd r
      · exact ⟨r, by omega, hx, he⟩
      · exact ih (r + 1) (by omega) (by rw [← rEnd_succ (by omega)]; omega)
  exact key (L.nr - 1) 0 (by have := nr_pos h; omega) (by rw [(run_facts h (nr_pos h)).1 rfl]; exact Nat.zero_le _)

end Facts

/-! ## The soundness reading -/

/-- The last element of `a :: t`. -/
@[expose] def lastOf : ℕ → List ℕ → ℕ
  | a, [] => a
  | _, v :: t => lastOf v t

/-- Each consecutive pair of `a :: t` satisfies `P`. -/
@[expose] def Hops (P : ℕ → ℕ → Prop) : ℕ → List ℕ → Prop
  | _, [] => True
  | a, v :: t => P a v ∧ Hops P v t

/-- A hop of a run of the machine within the function: forward, and every offset it skips in a
block whose range holds neither of its ends (an arm the branch or the join jumps over). -/
@[expose] def Hop (L : Layout) (u v : ℕ) : Prop :=
  u < v ∧ ∀ y r, u < y → y < v → L.InRun r y → ¬ L.InRange (L.run r).b u ∧ ¬ L.InRange (L.run r).b v

theorem lastOf_ge {L : Layout} : ∀ (a : ℕ) (t : List ℕ), Hops (Hop L) a t → a ≤ lastOf a t
  | _, [], _ => le_rfl
  | _, v :: t, ⟨h1, h2⟩ => le_trans h1.1.le (lastOf_ge v t h2)

/-- **A run passes every offset of a block's path between its ends**, when the block's range
holds its first offset (the run is inside the block: post-dominance) or its last (the run
reached the block: dominance). -/
theorem visits {L : Layout} (h : L.ok = true) {w r : ℕ} (hw : L.InRun r w) :
    ∀ (a : ℕ) (t : List ℕ), Hops (Hop L) a t → a ≤ w → w < lastOf a t →
      ((L.blk (L.run r).b).cs ≤ a ∨ lastOf a t < (L.blk (L.run r).b).ce) → w ∈ a :: t := by
  have hR := run_range h hw
  intro a t
  induction t generalizing a with
  | nil => intro _ h1 h2; simp [lastOf] at h2; omega
  | cons v t ih =>
    intro hh h1 h2 hin
    rcases Nat.eq_or_lt_of_le h1 with rfl | hlt
    · exact List.mem_cons_self
    · by_cases hwv : w < v
      · exfalso
        obtain ⟨hu, hv⟩ := hh.1.2 w r hlt hwv hw
        have := lastOf_ge v t hh.2
        rcases hin with hin | hin
        · exact hu ⟨hin, by have := hR.2; omega⟩
        · exact hv ⟨by have := hR.1; omega, by simp only [lastOf] at hin; omega⟩
      · refine List.mem_cons_of_mem _ (ih v hh.2 (by omega) h2 ?_)
        rcases hin with hin | hin
        · left; have := hh.1.1; omega
        · right; exact hin


end

end Layout

end LeanVM.Guest.Local
