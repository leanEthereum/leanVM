module

public import NativeRustcVmArm.Wire.WriteOpenings.Exec
public import NativeRustcVmArm.Wire.Common
public import NativeRustcVmArm.Spec.Wire
public import NativeRustcVmArm.Ring.Frame
public import NativeRustcVm.Arrays.ReadLemmas

/-!
# `write_openings`' run, places and memory

A run (`Run`): the entry state, the placement, the sibling counts' and the phase's addresses (the
two words at SP). What the function reads, as words of the entry's memory: query `j` (`qw`),
position `i` (`pw`), the first position of a word (`pos`), leaf `i`'s word `t` (`lfw`), level
`l`'s count (`cw`) and its digest for a word (`digest`, `find`'s lookup, zeros where none).
What it writes: the phase's head (`Head`) and opening `j` at `ob j` (`Opening`, its parts
`LeafPart`, `PathPart`). Where things are (`Geo`): the eight regions of the precondition
(`bigs`), each a chunk's home (`Inside`); the frame (`Frm`, 176 bytes).
-/

namespace NativeRustcVmArm.Wire.WriteOpenings

open NativeRustcArm NativeRustcArm.Sym NativeRustcVm.Wire NativeVm.Wire
open NativeRustcVmArm.Vm.WriteOpenings
open NativeRustcVmArm.Ring (Fr base)
open NativeRustcVm (WordAt WordsAt InAny Region wordOf)
open LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.Compile

@[expose] public section

/-- A run of `write_openings`: the entry state, the placement, the counts' and the phase's
addresses. -/
structure Run where
  m0 : MachineData
  k : Nat
  cnt : BitVec 64
  out : BitVec 64

/-- The key `find` looks up at level `l` for query word `q`. -/
def skey (q : UInt64) (l : Nat) : UInt64 := UInt64.ofBitVec (q.toBitVec >>> l)

/-- Opening `j`'s offset in the phase. -/
abbrev ob (j : Nat) : Nat := 24 + 1544 * j

namespace Run

variable (R : Run)

/-- The entry's memory. -/
abbrev d0 : Mem 64 := R.m0.dmem
/-- The queries' address. -/
abbrev qa : BitVec 64 := R.m0.regs.X0.toBitVec
/-- The queries' count. -/
abbrev nq : Nat := R.m0.regs.X1.toNat
/-- The positions' address. -/
abbrev pa : BitVec 64 := R.m0.regs.X2.toBitVec
/-- The positions' count. -/
abbrev np : Nat := R.m0.regs.X3.toNat
/-- The leaves' address. -/
abbrev lv : BitVec 64 := R.m0.regs.X4.toBitVec
/-- The leaves' width. -/
abbrev lw : Nat := R.m0.regs.X5.toNat
/-- The height. -/
abbrev h : Nat := R.m0.regs.X6.toNat
/-- The siblings' address. -/
abbrev sb : BitVec 64 := R.m0.regs.X7.toBitVec

/-- Query `j`'s word. -/
def qw (j : Nat) : UInt64 := wordOf R.d0 (R.qa + BitVec.ofNat 64 (8 * j))
/-- Position `i`'s word. -/
def pw (i : Nat) : UInt64 := wordOf R.d0 (R.pa + BitVec.ofNat 64 (8 * i))
/-- The first position holding `q`. -/
def pos (q : UInt64) : Option Nat := ((List.range R.np).map R.pw).findIdx? (· == q)
/-- Word `t` of leaf `i`. -/
def lfw (i t : Nat) : UInt64 := wordOf R.d0 (R.lv + BitVec.ofNat 64 (512 * i + 8 * t))
/-- Level `l`'s sibling count. -/
def cw (l : Nat) : UInt64 := wordOf R.d0 (R.cnt + BitVec.ofNat 64 (8 * l))
/-- Level `l`'s node `n`'s address. -/
def na (l n : Nat) : BitVec 64 := R.sb + BitVec.ofNat 64 (10240 * l + 40 * n)
/-- Level `l`'s keys. -/
def keys (l : Nat) : List UInt64 := (List.range (R.cw l).toNat).map fun n ↦ wordOf R.d0 (R.na l n)
/-- Level `l`'s digest for query word `q`: the found node's four words, else zeros. -/
def digest (l : Nat) (q : UInt64) : List UInt64 :=
  match (R.keys l).findIdx? (· == skey q l) with
  | some n => (List.range 4).map fun u ↦ wordOf R.d0 (R.na l n + BitVec.ofNat 64 (8 + 8 * u))
  | none => [0, 0, 0, 0]

/-- Byte `o` of the phase. -/
abbrev oa (o : Nat) : BitVec 64 := R.out + BitVec.ofNat 64 o
/-- The phase's head: the query count, the height, the leaves' width. -/
def Head (d : Mem 64) : Prop :=
  WordAt d (R.oa 0) R.nq.toUInt64 ∧ WordAt d (R.oa 8) R.h.toUInt64 ∧
    WordAt d (R.oa 16) R.lw.toUInt64

/-- Opening `j`'s first `t` leaf words, of leaf `i`. -/
def LeafPart (d : Mem 64) (j i t : Nat) : Prop :=
  WordsAt d (R.oa (ob j + 8)) ((List.range t).map (R.lfw i))

/-- Opening `j`'s digests of the first `L` levels. -/
def PathPart (d : Mem 64) (j L : Nat) : Prop :=
  WordsAt d (R.oa (ob j + 520)) ((List.range L).flatMap fun l ↦ R.digest l (R.qw j))

/-- **Opening `j` written**: its query found at position `i`, the query's word, the leaf, the
path. -/
def Opening (d : Mem 64) (j : Nat) : Prop :=
  ∃ i, R.pos (R.qw j) = some i ∧ WordAt d (R.oa (ob j)) (R.qw j) ∧ R.LeafPart d j i R.lw ∧
    R.PathPart d j R.h

/-- The first `j` openings and the head written. -/
def Done (d : Mem 64) (j : Nat) : Prop := R.Head d ∧ ∀ j' < j, R.Opening d j'

/-- What makes `write_openings` return `None`: a query at no position, or a level of more than
`256` siblings. -/
def Bad : Prop := (∃ j < R.nq, R.pos (R.qw j) = none) ∨ (∃ l < R.h, 256 < (R.cw l).toNat)

/-! ## Places -/

/-- The precondition's regions: the stack, the two arguments, the queries, the positions, the
leaves, the siblings, the counts, the phase. -/
def bigs : List Region :=
  [⟨base R.m0 176, 176⟩, ⟨R.m0.regs.SP.toBitVec, 16⟩, ⟨R.qa, 8 * R.nq⟩, ⟨R.pa, 8 * R.np⟩,
    ⟨R.lv, 512 * R.np⟩, ⟨R.sb, nodesBytes * R.h⟩, ⟨R.cnt, 8 * R.h⟩,
    ⟨R.out, phaseBytes⟩]

/-- Region `i` of `bigs`. -/
def big (i : Nat) : Region := R.bigs.getD i ⟨0, 0⟩

end Run

/-- The `n` bytes from `a` are inside region `A`. -/
def Inside (a : BitVec 64) (n : Nat) (A : Region) : Prop :=
  A.addr.toNat ≤ a.toNat ∧ a.toNat + n ≤ A.addr.toNat + A.size

/-- **The places**: the stack, the regions mapped, not wrapping, apart; the counts' bounds. -/
structure Geo (R : Run) : Prop where
  st : StackOk R.m0 176
  ok : ∀ i < 8, (R.big i).Ok R.d0
  dj : NativeRustcVm.Disjoint R.bigs
  nq0 : 0 < R.nq
  nq256 : R.nq ≤ 256
  np0 : 0 < R.np
  np256 : R.np ≤ 256
  lw64 : R.lw ≤ 64
  h32 : R.h ≤ 32
  cntW : WordAt R.d0 R.m0.regs.SP.toBitVec (UInt64.ofBitVec R.cnt)
  outW : WordAt R.d0 (R.m0.regs.SP.toBitVec + 8#64) (UInt64.ofBitVec R.out)

/-- The prologue's slots. -/
def slots : List (Nat × XReg) := [(80, .X29), (88, .X30), (96, .X28), (104, .X27), (112, .X26),
  (120, .X25), (128, .X24), (136, .X23), (144, .X22), (152, .X21), (160, .X20), (168, .X19)]

/-- The phase's bytes. -/
abbrev Outs (R : Run) : BitVec 64 → Prop := InRange R.out phaseBytes

/-- **Between the prologue and the epilogue.** -/
abbrev Frm (R : Run) (m : MachineData) : Prop := Fr R.m0 176 176 slots [] (Outs R) m

/-- The pc of directive `j`. -/
abbrev pcOf [Host] (R : Run) (j : Nat) : Int64 := Host.addrOf (R.k + j)

/-- The environment of the frame and the chunks `cs`. -/
abbrev envOf (R : Run) (m : MachineData) (cs : List (BitVec 64 × Nat)) : Env :=
  Env.ofMachine m ((base R.m0 176, 176) :: cs)

end

public section

theorem after_eq {ds : List Directive} {S S₁ : SState} {x : Exit} (h : exec ds S = some (S₁, x)) :
    after ds S = S₁ := by
  rw [after, h]

/-- Mapped bytes hold the word `wordOf` reads. -/
theorem wordAt_wordOf {d : Mem 64} {a : BitVec 64} (h : NativeRustcVm.Mapped d a 8) :
    WordAt d a (wordOf d a) := by
  have hl : (NativeRustcVm.bytesFrom d a 8).length = 8 := by simp [NativeRustcVm.bytesFrom]
  unfold WordAt wordOf
  rw [NativeRustcVm.wordBytes_ofNat_leNat hl]
  intro i hi
  simp only [NativeRustcVm.bytesFrom, List.getElem_map, List.getElem_range]
  have := h i (by rw [hl] at hi; exact hi)
  revert this
  cases d.get? (a + BitVec.ofNat 64 i) <;> simp

/-- A word read in memory changed only where `W` holds, `W` missing its bytes. -/
theorem wordOf_keep {d d' : Mem 64} {W : BitVec 64 → Prop} (hs : SameOutside d d' W) {a : BitVec 64}
    (h : ∀ i < 8, ¬W (a + BitVec.ofNat 64 i)) : wordOf d' a = wordOf d a := by
  unfold wordOf NativeRustcVm.bytesFrom
  congr 2
  apply List.map_congr_left
  intro i hi
  rw [List.mem_range] at hi
  rw [hs _ (h i hi)]

section Inside

variable {a : BitVec 64} {n : Nat} {A : Region}

theorem inside_off (hA : NativeRustcVm.NoWrap A.addr A.size) {o : Nat} (h : o + n ≤ A.size)
    (hn : 0 < n) : Inside (A.addr + BitVec.ofNat 64 o) n A := by
  unfold NativeRustcVm.NoWrap at hA
  unfold Inside
  rw [NativeRustcVm.toNat_add_ofNat (by omega)]
  omega

theorem Inside.noWrap (h : Inside a n A) (hA : NativeRustcVm.NoWrap A.addr A.size) :
    NativeRustcVm.NoWrap a n := by
  unfold NativeRustcVm.NoWrap at *; unfold Inside at h; omega

theorem Inside.mapped {d : Mem 64} (h : Inside a n A) (hA : A.Ok d) :
    NativeRustcVm.Mapped d a n := by
  intro i hi
  have hnw := hA.2
  unfold NativeRustcVm.NoWrap at hnw
  unfold Inside at h
  have := hA.1 (a.toNat - A.addr.toNat + i) (by omega)
  have e : A.addr + BitVec.ofNat 64 (a.toNat - A.addr.toNat + i) = a + BitVec.ofNat 64 i := by
    apply BitVec.eq_of_toNat_eq
    rw [NativeRustcVm.toNat_add_ofNat (by omega), NativeRustcVm.toNat_add_ofNat (by omega)]
    omega
  rwa [e] at this

theorem Inside.apart (h : Inside a n A) {B : Region} {b : BitVec 64} {m : Nat} (hb : Inside b m B)
    (hAB : NativeRustcVm.Apart A.addr A.size B.addr B.size) : NativeRustcVm.Apart a n b m := by
  unfold Inside at h hb; unfold NativeRustcVm.Apart at *; omega

theorem Inside.inRange (h : Inside a n A) (hA : NativeRustcVm.NoWrap A.addr A.size) {p : BitVec 64}
    (hp : InRange a n p) : InRange A.addr A.size p :=
  NativeRustcVm.InRange.mono hp (h.noWrap hA) hA h.1 h.2

theorem Inside.not_inRange (h : Inside a n A) (hA : NativeRustcVm.NoWrap A.addr A.size)
    {B : Region} (hB : NativeRustcVm.NoWrap B.addr B.size)
    (hAB : NativeRustcVm.Apart A.addr A.size B.addr B.size) {p : BitVec 64}
    (hp : InRange a n p) : ¬InRange B.addr B.size p :=
  hAB.not_inRange hA hB (h.inRange hA hp)

theorem Inside.take (h : Inside a n A) {m : Nat} (hm : m ≤ n) : Inside a m A :=
  ⟨h.1, by have := h.2; omega⟩

end Inside

section Geo

variable {R : Run}

theorem Geo.noWrap (G : Geo R) {i : Nat} (hi : i < 8) :
    NativeRustcVm.NoWrap (R.big i).addr (R.big i).size := (G.ok i hi).2

theorem Geo.apart (G : Geo R) {i j : Nat} (hij : i ≠ j) (hi : i < 8) (hj : j < 8) :
    NativeRustcVm.Apart (R.big i).addr (R.big i).size (R.big j).addr (R.big j).size := by
  have hd := G.dj
  unfold NativeRustcVm.Disjoint at hd
  rw [List.pairwise_iff_getElem] at hd
  have hl : R.bigs.length = 8 := rfl
  unfold Run.big
  simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (show i < R.bigs.length by omega),
    List.getElem?_eq_getElem (show j < R.bigs.length by omega), Option.getD_some]
  rcases Nat.lt_or_gt_of_ne hij with h | h
  · exact hd i j (by omega) (by omega) h
  · exact (hd j i (by omega) (by omega) h).symm

/-- A chunk of region `i` misses region `j`. -/
theorem Geo.not_in (G : Geo R) {i j : Nat} (hij : i ≠ j) (hi : i < 8) (hj : j < 8) {a : BitVec 64}
    {n : Nat} (ha : Inside a n (R.big i)) {p : BitVec 64} (hp : InRange a n p) :
    ¬InRange (R.big j).addr (R.big j).size p :=
  ha.not_inRange (G.noWrap hi) (G.noWrap hj) (G.apart hij hi hj) hp

theorem big0 : R.big 0 = ⟨base R.m0 176, 176⟩ := rfl
theorem big2 : R.big 2 = ⟨R.qa, 8 * R.nq⟩ := rfl
theorem big3 : R.big 3 = ⟨R.pa, 8 * R.np⟩ := rfl
theorem big4 : R.big 4 = ⟨R.lv, 512 * R.np⟩ := rfl
theorem big5 : R.big 5 = ⟨R.sb, nodesBytes * R.h⟩ := rfl
theorem big6 : R.big 6 = ⟨R.cnt, 8 * R.h⟩ := rfl
theorem big7 : R.big 7 = ⟨R.out, phaseBytes⟩ := rfl

/-- The frame is region 0. -/
theorem frame_inside : Inside (base R.m0 176) 176 (R.big 0) := ⟨le_refl _, le_refl _⟩

/-- **The environment of the frame and one chunk** of another region is well formed. -/
theorem Geo.wf1 (G : Geo R) {m : MachineData} (hk : Kept R.d0 m.dmem) {a : BitVec 64} {n i : Nat}
    (hi : i < 8) (h0 : i ≠ 0) (ha : Inside a n (R.big i)) : (envOf R m [(a, n)]).WF := by
  have hf := frame_inside (R := R)
  refine Env.wf_of ⟨⟨fun t ht ↦ hk _ (hf.mapped (G.ok 0 (by omega)) t ht), hf.noWrap (G.noWrap
    (by omega))⟩, ⟨fun t ht ↦ hk _ (ha.mapped (G.ok i hi) t ht), ha.noWrap (G.noWrap hi)⟩, trivial⟩
    (List.pairwise_pair.mpr ?_)
  exact hf.apart ha (G.apart (Ne.symm h0) (by omega) hi)

/-- **The environment of the frame and two chunks** of two other regions is well formed. -/
theorem Geo.wf2 (G : Geo R) {m : MachineData} (hk : Kept R.d0 m.dmem) {a b : BitVec 64}
    {n n' i j : Nat} (hi : i < 8) (hj : j < 8) (h0 : i ≠ 0) (h0' : j ≠ 0) (hij : i ≠ j)
    (ha : Inside a n (R.big i)) (hb : Inside b n' (R.big j)) :
    (envOf R m [(a, n), (b, n')]).WF := by
  have hf := frame_inside (R := R)
  refine Env.wf_of ⟨⟨fun t ht ↦ hk _ (hf.mapped (G.ok 0 (by omega)) t ht), hf.noWrap (G.noWrap
    (by omega))⟩, ⟨fun t ht ↦ hk _ (ha.mapped (G.ok i hi) t ht), ha.noWrap (G.noWrap hi)⟩,
    ⟨fun t ht ↦ hk _ (hb.mapped (G.ok j hj) t ht), hb.noWrap (G.noWrap hj)⟩, trivial⟩ ?_
  show List.Pairwise _ [(base R.m0 176, 176), (a, n), (b, n')]
  simp only [List.pairwise_cons, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
    forall_eq, List.Pairwise.nil, and_true]
  exact ⟨⟨hf.apart ha (G.apart (Ne.symm h0) (by omega) hi),
    hf.apart hb (G.apart (Ne.symm h0') (by omega) hj)⟩, ha.apart hb (G.apart hij hi hj),
    fun _ h ↦ h.elim⟩

/-- The frame's environment is well formed. -/
theorem Geo.wf0 (G : Geo R) {m : MachineData} (hk : Kept R.d0 m.dmem) : (envOf R m []).WF := by
  have hf := frame_inside (R := R)
  exact Env.wf_of ⟨⟨fun t ht ↦ hk _ (hf.mapped (G.ok 0 (by omega)) t ht), hf.noWrap (G.noWrap
    (by omega))⟩, trivial⟩ (List.pairwise_singleton _ _)

theorem Geo.aligned (G : Geo R) : (base R.m0 176).toNat % 16 = 0 :=
  Ring.frame_aligned G.st (le_refl _) rfl

/-- A word of an input region (`1 ≤ i ≤ 6`) reads the same in any state of the frame. -/
theorem Geo.wordOf_keep (G : Geo R) {m : MachineData} (hfr : Frm R m) {i : Nat} (hi : i < 7)
    (h0 : i ≠ 0) {a : BitVec 64} (ha : Inside a 8 (R.big i)) : wordOf m.dmem a = wordOf R.d0 a :=
  WriteOpenings.wordOf_keep hfr.same fun t ht hq ↦ by
    have hp : InRange a 8 (a + BitVec.ofNat 64 t) :=
      NativeRustcVm.inRange_add ht (by
        have := ha.noWrap (G.noWrap (by omega))
        unfold NativeRustcVm.NoWrap at this
        omega)
    rcases hq with hq | hq
    · exact G.not_in (j := 0) h0 (by omega) (by omega) ha hp hq
    · exact G.not_in (j := 7) (by omega) (by omega) (by omega) ha hp hq

end Geo

end

public section
variable [Host] {R : Run}

/-- **A block from a state of the frame**: the frame kept (writes in the frame below the slots
or in chunks of the phase), the block's result, its exit. -/
theorem run_block (G : Geo R) {b : List Directive} {j : Nat} (hp : Placed code R.k)
    (hin : b.IsInfixAt code j) (hne : b ≠ []) {S S' : SState} {x : Exit}
    (hx : exec b S = some (S', x)) {cs : List (BitVec 64 × Nat)} {st : MachineState}
    (hfr : Frm R st.data) (hpc : st.pc = pcOf R j) (hwf : (envOf R st.data cs).WF)
    (hm : Match (envOf R st.data cs) S st.data) (hsp : S'.sp = S.sp)
    (hW : ∀ w ∈ S'.mem, Ring.WriteOk (envOf R st.data cs) 176 slots (Outs R) w)
    {Q : MachineState → Prop}
    (cont : ∀ st', Frm R st'.data → Match (envOf R st.data cs) S' st'.data →
      PcOk (envOf R st.data cs) x (Host.addrOf (R.k + j + b.length)) st' →
      Eventually (step1 Host.exe) Q st') :
    Eventually (step1 Host.exe) Q st :=
  exec_at (infix_of hin hne hp) hx hwf hpc hm fun st' hm' hpc' ↦ cont st'
    (Fr.ofBlockW hfr hm hm' hwf rfl hsp (fun _ h ↦ absurd h (by simp)) rfl (le_refl _)
      G.st.2.1 (by decide) hW) hm' hpc'

end

end NativeRustcVmArm.Wire.WriteOpenings
