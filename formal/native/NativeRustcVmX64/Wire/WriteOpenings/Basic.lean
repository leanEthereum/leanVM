module

public import NativeRustcVmX64.Wire.WriteOpenings.Exec
public import NativeRustcVmX64.Wire.Common
public import NativeRustcVmX64.Transcript.Frame
public import NativeRustcVmX64.Spec.Wire
public import NativeRustcVm.Arrays.ReadLemmas
public import NativeRustcVm.Wire.WordsFacts

/-!
# `write_openings`' run, places and memory (x86-64)

A run (`Run`): the entry state and the placement; the arguments as the entry names them (the
queries `qa`, `nq`, the positions `pa`, `np`, the leaves `lv`, their width `lw`, and above the
return address the height `h`, the siblings `sb`, their counts `cnt`, the phase `out`). What the
function reads, as words of the entry's memory: query `j` (`qw`), position `i` (`pw`), the first
position of a word (`pos`), leaf `i`'s word `t` (`lfw`), level `l`'s count (`cw`) and its digest
for a word (`digest`). What it writes: the phase's head (`Head`) and opening `j` at `ob j`
(`Opening`). Where things are (`Geo`): the eight regions of the precondition (`bigs`), each a
chunk's home (`Inside`). A state of the body (`Fr`): the frame (`Transcript.Frame`, 160 bytes, RSP
at offset `8`) and the entry's memory changed only in the frame and the phase (`Chg`); a block
keeps it (`blk`).
-/

namespace NativeRustcVmX64.Wire.WriteOpenings

open NativeRustcX64 NativeRustcX64.Sym NativeRustcVm.Wire NativeVm.Wire
open NativeRustcVmX64.Vm.WriteOpenings
open NativeRustcVmX64.Transcript (Frame Slots frameEnv frame_wf MidOk)
open NativeRustcVm (WordAt WordsAt InAny Region wordOf)
open LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.Compile

@[expose] public section

/-- A run of `write_openings`: the entry state, the placement. -/
structure Run where
  m0 : MachineData
  k : Nat

/-- The key `find` looks up at level `l` for query word `q`. -/
def skey (q : UInt64) (l : Nat) : UInt64 := UInt64.ofBitVec (q.toBitVec >>> l)

/-- Opening `j`'s offset in the phase. -/
abbrev ob (j : Nat) : Nat := 24 + 1544 * j

/-- The frame's slots: the six pushes. -/
def slots : Slots := [(152, .rbp), (144, .r15), (136, .r14), (128, .r13), (120, .r12), (112, .rbx)]

namespace Run

variable (R : Run)

/-- The entry's memory. -/
abbrev d0 : Mem 64 := R.m0.dmem
/-- The queries' address. -/
abbrev qa : BitVec 64 := reg R.m0 .rdi
/-- The queries' count. -/
abbrev nq : Nat := (reg R.m0 .rsi).toNat
/-- The positions' address. -/
abbrev pa : BitVec 64 := reg R.m0 .rdx
/-- The positions' count. -/
abbrev np : Nat := (reg R.m0 .rcx).toNat
/-- The leaves' address. -/
abbrev lv : BitVec 64 := reg R.m0 .r8
/-- The leaves' width. -/
abbrev lw : Nat := (reg R.m0 .r9).toNat
/-- The height. -/
abbrev h : Nat := (stackArg R.m0 0).toNat
/-- The siblings' address. -/
abbrev sb : BitVec 64 := stackArg R.m0 1
/-- The sibling counts' address. -/
abbrev cnt : BitVec 64 := stackArg R.m0 2
/-- The phase's address. -/
abbrev out : BitVec 64 := stackArg R.m0 3
/-- The frame's base: 160 bytes below the entry's RSP. -/
abbrev fb : BitVec 64 := stackBelow R.m0 160
/-- The argument words' address, above the return address. -/
abbrev ab : BitVec 64 := NativeRustcVm.Transcript.off (rspOf R.m0) 8

/-- Query `j`'s word. -/
def qw (j : Nat) : UInt64 := wordOf R.d0 (R.qa + BitVec.ofNat 64 (8 * j))
/-- Position `i`'s word. -/
def pw (i : Nat) : UInt64 := wordOf R.d0 (R.pa + BitVec.ofNat 64 (8 * i))
/-- The first position holding `q`. -/
def pos (q : UInt64) : Option Nat := ((List.range R.np).map R.pw).findIdx? (· == q)
/-- Word `t` of leaf `i`. -/
def lfw (i t : Nat) : UInt64 := wordOf R.d0 (R.lv + BitVec.ofNat 64 (512 * i + 8 * t))
/-- Level `l`'s sibling count. -/
@[irreducible] def cw (l : Nat) : UInt64 := wordOf R.d0 (R.cnt + BitVec.ofNat 64 (8 * l))
/-- Level `l`'s node `n`'s address. -/
def na (l n : Nat) : BitVec 64 := R.sb + BitVec.ofNat 64 (10240 * l + 40 * n)
/-- Level `l`'s keys. -/
@[irreducible] def keys (l : Nat) : List UInt64 := (List.range (R.cw l).toNat).map fun n ↦ wordOf R.d0 (R.na l n)
/-- The index of level `l`'s node of query word `q`'s key. -/
@[irreducible] def fidx (l : Nat) (q : UInt64) : Option Nat := (R.keys l).findIdx? (· == skey q l)
/-- Level `l`'s digest for query word `q`: the found node's four words, else zeros. -/
def digest (l : Nat) (q : UInt64) : List UInt64 :=
  match R.fidx l q with
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

/-- Opening `j` begun: the first `j` openings, the head, the query's word. -/
def Begun (j : Nat) (d : Mem 64) : Prop := R.Done d j ∧ WordAt d (R.oa (ob j)) (R.qw j)

/-- What makes `write_openings` return `None`: a query at no position, or a level of more than
`256` siblings. -/
def Bad : Prop := (∃ j < R.nq, R.pos (R.qw j) = none) ∨ (∃ l < R.h, 256 < (R.cw l).toNat)

/-! ## Places -/

/-- The precondition's regions: the stack with the return address, the argument words, the
queries, the positions, the leaves, the siblings, the counts, the phase. -/
def bigs : List Region :=
  stackR R.m0 writeOpeningsStack :: ⟨R.ab, 32⟩ :: writeOpeningsRegions R.m0

/-- Region `i` of `bigs`. -/
def big (i : Nat) : Region := R.bigs.getD i ⟨0, 0⟩

/-- What a run may change of the entry's memory: the frame and the phase. -/
def Chg (d : Mem 64) : Prop :=
  NativeRustcVm.SameOutside R.d0 d fun q ↦
    NativeRustcVm.InRange R.fb 160 q ∨ NativeRustcVm.InRange R.out phaseBytes q

/-- The frame or the phase's `n` bytes from `o`: what a block writing the phase changes. -/
abbrev FO (o n : Nat) (q : BitVec 64) : Prop :=
  NativeRustcVm.InRange R.fb 160 q ∨ NativeRustcVm.InRange (R.oa o) n q

/-- Frame word at offset `o`. -/
abbrev FW (d : Mem 64) (o : Nat) (v : BitVec 64) : Prop :=
  WordAt d (R.fb + BitVec.ofNat 64 o) (UInt64.ofBitVec v)

end Run

/-- No write into the frame overlaps the words at the offsets `os`. -/
def missAll (os : List Nat) (S : SState) : Bool :=
  S.mem.all fun w ↦ w.r != 0 || os.all fun o ↦ decide (w.off + w.n ≤ o) || decide (o + 8 ≤ w.off)


/-- The `n` bytes from `a` are inside region `A`. -/
def Inside (a : BitVec 64) (n : Nat) (A : Region) : Prop :=
  A.addr.toNat ≤ a.toNat ∧ a.toNat + n ≤ A.addr.toNat + A.size

/-- **The places**: the stack, the regions mapped, not wrapping, apart; the counts' bounds. -/
structure Geo (R : Run) : Prop where
  st : StackOk R.m0 160
  ok : ∀ i < 8, (R.big i).Ok R.d0
  dj : NativeRustcVm.Disjoint R.bigs
  nq0 : 0 < R.nq
  nq256 : R.nq ≤ 256
  np0 : 0 < R.np
  np256 : R.np ≤ 256
  lw64 : R.lw ≤ 64
  h32 : R.h ≤ 32

/-- **A state of the body**: the frame, RSP at offset `o`, and the entry's memory changed only in
the frame and the phase. -/
structure Fr (R : Run) (o : Nat) (m : MachineData) : Prop where
  fr : Frame R.m0 160 slots o m
  chg : R.Chg m.dmem

/-- The environment of the frame, the argument words and the chunks `cs`. -/
abbrev envOf (R : Run) (m : MachineData) (cs : List (BitVec 64 × Nat)) (ret : BitVec 64 := 0) :
    Env :=
  frameEnv R.m0 m 160 ((R.ab, 32) :: cs) (fun _ ↦ 0) ret

/-- The pc of directive `j`. -/
abbrev pcOf [Host] (R : Run) (j : Nat) : Int64 := Host.addrOf (R.k + j)

end

public section

theorem slots_le : ∀ p ∈ slots, p.1 + 8 ≤ 160 := by decide

theorem natOfBytes_eq_leNat (bs : List UInt8) : Nat.ofBytes bs = NativeRustcVm.leNat bs := by
  induction bs with
  | nil => rfl
  | cons b bs ih =>
    show Nat.ofBytes bs * 256 + b.toNat = b.toNat + 256 * NativeRustcVm.leNat bs
    rw [ih]; omega

/-- **An environment's load of eight bytes** is the word `wordOf` reads there. -/
theorem load_eq_wordOf (env : Env) (r o : Nat) :
    env.load r o 8 = (wordOf env.mem0 (env.base r + BitVec.ofNat 64 o)).toBitVec := by
  unfold Env.load wordOf NativeRustcVm.bytesFrom
  rw [ofBytes_natCast, BitVec.ofInt_natCast, natOfBytes_eq_leNat]
  show BitVec.ofNat 64 _ = BitVec.ofNat 64 _
  congr 2
  apply List.map_congr_left
  intro i _
  rw [addr_add]

/-- Mapped bytes hold the word `wordOf` reads. -/
theorem wordAt_wordOf {d : Mem 64} {a : BitVec 64} (h : NativeRustcVm.Mapped d a 8) :
    WordAt d a (wordOf d a) := by
  obtain ⟨w, hw⟩ := NativeRustcVm.Wire.exists_wordAt h
  rw [NativeRustcVm.wordOf_of_wordAt hw]
  exact hw

/-- A word read in memory changed only where `W` holds, `W` missing its bytes. -/
theorem wordOf_keep {d d' : Mem 64} {W : BitVec 64 → Prop}
    (hs : NativeRustcVm.SameOutside d d' W) {a : BitVec 64}
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

theorem inside_self : Inside A.addr A.size A := ⟨le_refl _, le_refl _⟩

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

theorem Inside.inRange (h : Inside a n A) (hA : NativeRustcVm.NoWrap A.addr A.size)
    {p : BitVec 64} (hp : NativeRustcVm.InRange a n p) : NativeRustcVm.InRange A.addr A.size p :=
  NativeRustcVm.InRange.mono hp (h.noWrap hA) hA h.1 h.2

theorem Inside.take (h : Inside a n A) {m : Nat} (hm : m ≤ n) : Inside a m A :=
  ⟨h.1, by have := h.2; omega⟩

/-- The `m` bytes `o` into an inside chunk are inside. -/
theorem Inside.sub (h : Inside a n A) (hA : NativeRustcVm.NoWrap A.addr A.size) {o m : Nat}
    (hom : o + m ≤ n) (hm : 0 < m) : Inside (a + BitVec.ofNat 64 o) m A := by
  have := h.noWrap hA
  unfold NativeRustcVm.NoWrap at this
  unfold Inside at *
  rw [NativeRustcVm.toNat_add_ofNat (by omega)]
  omega

end Inside

section Geo

variable {R : Run}

theorem bigs_length : R.bigs.length = 8 := rfl

theorem Geo.noWrap (G : Geo R) {i : Nat} (hi : i < 8) :
    NativeRustcVm.NoWrap (R.big i).addr (R.big i).size := (G.ok i hi).2

theorem Geo.apart (G : Geo R) {i j : Nat} (hij : i ≠ j) (hi : i < 8) (hj : j < 8) :
    NativeRustcVm.Apart (R.big i).addr (R.big i).size (R.big j).addr (R.big j).size := by
  have hd := G.dj
  unfold NativeRustcVm.Disjoint at hd
  rw [List.pairwise_iff_getElem] at hd
  unfold Run.big
  simp only [List.getD_eq_getElem?_getD,
    List.getElem?_eq_getElem (show i < R.bigs.length by rw [bigs_length]; omega),
    List.getElem?_eq_getElem (show j < R.bigs.length by rw [bigs_length]; omega), Option.getD_some]
  rcases Nat.lt_or_gt_of_ne hij with h | h
  · exact hd i j (by rw [bigs_length]; omega) (by rw [bigs_length]; omega) h
  · exact (hd j i (by rw [bigs_length]; omega) (by rw [bigs_length]; omega) h).symm

/-- A chunk of region `i` misses region `j`. -/
theorem Geo.not_in (G : Geo R) {i j : Nat} (hij : i ≠ j) (hi : i < 8) (hj : j < 8) {a : BitVec 64}
    {n : Nat} (ha : Inside a n (R.big i)) {p : BitVec 64} (hp : NativeRustcVm.InRange a n p) :
    ¬NativeRustcVm.InRange (R.big j).addr (R.big j).size p :=
  (G.apart hij hi hj).not_inRange (G.noWrap hi) (G.noWrap hj) (ha.inRange (G.noWrap hi) hp)

theorem big0 : R.big 0 = ⟨R.fb, 168⟩ := rfl
theorem big1 : R.big 1 = ⟨R.ab, 32⟩ := rfl
theorem big2 : R.big 2 = ⟨R.qa, 8 * R.nq⟩ := rfl
theorem big3 : R.big 3 = ⟨R.pa, 8 * R.np⟩ := rfl
theorem big4 : R.big 4 = ⟨R.lv, 512 * R.np⟩ := rfl
theorem big5 : R.big 5 = ⟨R.sb, nodesBytes * R.h⟩ := rfl
theorem big6 : R.big 6 = ⟨R.cnt, 8 * R.h⟩ := rfl
theorem big7 : R.big 7 = ⟨R.out, phaseBytes⟩ := rfl

theorem Geo.outNw (G : Geo R) : NativeRustcVm.NoWrap R.out phaseBytes := G.noWrap (i := 7) (by omega)
theorem Geo.fbNw (G : Geo R) : NativeRustcVm.NoWrap R.fb 168 := G.noWrap (i := 0) (by omega)

/-- **A word of an input region** (`1 ≤ i ≤ 6`) reads the same in any state the run reaches. -/
theorem Geo.rd (G : Geo R) {d : Mem 64} (hc : R.Chg d) {i : Nat} (hi : i < 7) (h0 : i ≠ 0)
    {a : BitVec 64} (ha : Inside a 8 (R.big i)) : wordOf d a = wordOf R.d0 a :=
  wordOf_keep hc fun t ht hq ↦ by
    have hp : NativeRustcVm.InRange a 8 (a + BitVec.ofNat 64 t) :=
      NativeRustcVm.inRange_add ht (by
        have := ha.noWrap (G.noWrap (by omega))
        unfold NativeRustcVm.NoWrap at this
        omega)
    rcases hq with hq | hq
    · refine G.not_in (j := 0) h0 (by omega) (by omega) ha hp ?_
      show NativeRustcVm.InRange R.fb 168 _
      exact NativeRustcVm.InRange.mono hq ((G.fbNw).mono (by omega)) G.fbNw (le_refl _)
        (by omega)
    · exact G.not_in (j := 7) (by omega) (by omega) (by omega) ha hp hq

/-- **The environment of the frame, the arguments and the chunks `cs`**, each inside a region of
the precondition past the arguments, pairwise apart, is well formed. -/
theorem Geo.wf (G : Geo R) {m : MachineData} (hk : Kept R.d0 m.dmem) {cs : List (BitVec 64 × Nat)}
    (hcs : ∀ x ∈ cs, ∃ i, 2 ≤ i ∧ i < 8 ∧ Inside x.1 x.2 (R.big i))
    (hp : cs.Pairwise fun x y ↦ NativeRustcVm.Apart x.1 x.2 y.1 y.2) {ret : BitVec 64} :
    (envOf R m cs ret).WF := by
  have h0 : Inside R.fb 168 (R.big 0) := inside_self
  have h1 : Inside R.ab 32 (R.big 1) := inside_self
  refine frame_wf ⟨fun t ht ↦ hk _ (h0.mapped (G.ok 0 (by omega)) t ht), G.fbNw⟩
    (fun x hx ↦ ?_) ?_
  · rcases List.mem_cons.mp hx with rfl | hx
    · exact ⟨fun t ht ↦ hk _ (h1.mapped (G.ok 1 (by omega)) t ht), G.noWrap (i := 1) (by omega)⟩
    · obtain ⟨i, hi2, hi8, hin⟩ := hcs x hx
      exact ⟨fun t ht ↦ hk _ (hin.mapped (G.ok i hi8) t ht), hin.noWrap (G.noWrap hi8)⟩
  · refine List.Pairwise.cons (fun y hy ↦ ?_) (List.Pairwise.cons (fun y hy ↦ ?_) hp)
    · rcases List.mem_cons.mp hy with rfl | hy
      · exact h0.apart h1 (G.apart (by omega) (by omega) (by omega))
      · obtain ⟨i, hi2, hi8, hin⟩ := hcs y hy
        exact h0.apart hin (G.apart (by omega) (by omega) hi8)
    · obtain ⟨i, hi2, hi8, hin⟩ := hcs y hy
      exact h1.apart hin (G.apart (by omega) (by omega) hi8)

theorem Geo.wf0 (G : Geo R) {m : MachineData} (hk : Kept R.d0 m.dmem) {ret : BitVec 64} :
    (envOf R m [] ret).WF :=
  G.wf hk (by simp) List.Pairwise.nil

theorem Geo.wf1 (G : Geo R) {m : MachineData} (hk : Kept R.d0 m.dmem) {a : BitVec 64} {n i : Nat}
    (hi2 : 2 ≤ i) (hi8 : i < 8) (ha : Inside a n (R.big i)) {ret : BitVec 64} :
    (envOf R m [(a, n)] ret).WF :=
  G.wf hk (fun x hx ↦ by rw [List.mem_singleton.mp hx]; exact ⟨i, hi2, hi8, ha⟩)
    (List.pairwise_singleton _ _)

theorem Geo.wf2 (G : Geo R) {m : MachineData} (hk : Kept R.d0 m.dmem) {a b : BitVec 64}
    {n n' i j : Nat} (hi2 : 2 ≤ i) (hi8 : i < 8) (hj2 : 2 ≤ j) (hj8 : j < 8) (hij : i ≠ j)
    (ha : Inside a n (R.big i)) (hb : Inside b n' (R.big j)) {ret : BitVec 64} :
    (envOf R m [(a, n), (b, n')] ret).WF :=
  G.wf hk (fun x hx ↦ by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl
      · exact ⟨i, hi2, hi8, ha⟩
      · exact ⟨j, hj2, hj8, hb⟩)
    (List.pairwise_pair.mpr (ha.apart hb (G.apart hij hi8 hj8)))

/-- The argument words are 168 bytes above the frame's base. -/
theorem fb_add (o : Nat) :
    R.fb + BitVec.ofInt 64 ((168 + o : Nat) : Int) = R.ab + BitVec.ofInt 64 (o : Int) := by
  show rspOf R.m0 - BitVec.ofNat 64 160 + _ = rspOf R.m0 + BitVec.ofNat 64 8 + _
  rw [BitVec.ofInt_natCast, BitVec.ofInt_natCast]
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_ofNat, Nat.reducePow]
  omega

end Geo

/-! ## Blocks -/

section Blocks

variable {R : Run}

theorem Run.Chg.trans {d d' : Mem 64} (h : R.Chg d) {W : BitVec 64 → Prop}
    (hs : NativeRustcVm.SameOutside d d' W)
    (hW : ∀ q, W q → NativeRustcVm.InRange R.fb 160 q ∨ NativeRustcVm.InRange R.out phaseBytes q) :
    R.Chg d' :=
  fun q hq ↦ (hs q fun h ↦ hq (hW q h)).trans (h q hq)

theorem Run.Chg.of_eq {d d' : Mem 64} (h : R.Chg d) (he : d' = d) : R.Chg d' := he ▸ h

theorem midOk_br {o : Nat} {S : SState} (h : MidOk 160 o slots S = true) :
    NativeRustcVmX64.Transcript.belowRet 160 S = true := by
  simp only [MidOk, Bool.and_eq_true] at h; exact h.1.1.1.2

theorem midOk_in {o : Nat} {S : SState} (h : MidOk 160 o slots S = true) :
    NativeRustcVmX64.Transcript.writesIn S = true := by
  simp only [MidOk, Bool.and_eq_true] at h; exact h.1.1.2

theorem missAll_spec {os : List Nat} {S : SState} (h : missAll os S = true) {o : Nat}
    (ho : o ∈ os) : ∀ w ∈ S.mem, w.r = 0 → w.off + w.n ≤ o ∨ o + 8 ≤ w.off := by
  intro w hw hr
  unfold missAll at h
  rw [List.all_eq_true] at h
  have := h w hw
  simp only [hr, bne_self_eq_false, Bool.false_or, List.all_eq_true, Bool.or_eq_true,
    decide_eq_true_eq] at this
  exact this o ho

theorem allOf_append {α : Type} {P : α → Prop} :
    ∀ {l₁ l₂ : List α}, AllOf P l₁ → AllOf P l₂ → AllOf P (l₁ ++ l₂)
  | [], _, _, h => h
  | _ :: _, _, ⟨h, h₁⟩, h₂ => ⟨h, allOf_append h₁ h₂⟩

section
variable [Labels]

omit [Labels] in
/-- The bytes a block wrote: in the frame below its return address, or in the bytes `P` of a
region. -/
theorem written_in {m : MachineData} {cs : List (BitVec 64 × Nat)} {ret : BitVec 64}
    {S : SState} (hwf : (envOf R m cs ret).WF)
    (hbr : NativeRustcVmX64.Transcript.belowRet 160 S = true) {P : BitVec 64 → Prop}
    (hW : ∀ w ∈ S.mem, w.r = 0 ∨ ∀ b sz, (envOf R m cs ret).regions[w.r]? = some (b, sz) →
      ∀ jj, w.off ≤ jj → jj < w.off + w.n → P (b + BitVec.ofNat 64 jj))
    {q : BitVec 64} (hq : Written (envOf R m cs ret) S q) :
    NativeRustcVm.InRange R.fb 160 q ∨ P q := by
  obtain ⟨w, hw, b, sz, hb, jj, h1, h2, rfl⟩ := NativeRustcVmX64.Transcript.written_off hwf hq
  have hnw := hwf.noWrap _ b sz hb
  rcases hW w hw with hr | hr
  · have hbr' := NativeRustcVmX64.Transcript.belowRet_spec hbr w hw hr
    rw [hr] at hb
    cases hb
    exact .inl (NativeRustcVm.inRange_add (by omega) (by omega))
  · exact .inr (hr b sz hb jj h1 h2)

/-- The argument words' aliases hold. -/
theorem argAl_ok {m : MachineData} {cs : List (BitVec 64 × Nat)} {ret : BitVec 64} :
    AllOf (fun p : Sym × Nat × Int ↦ p.1.eval (envOf R m cs ret) =
      (envOf R m cs ret).base p.2.1 + BitVec.ofInt 64 p.2.2) argAl :=
  ⟨fb_add 0, fb_add 8, fb_add 16, fb_add 24, trivial⟩

/-- **A body state matches `fS`**: the frame, the argument words, the chunks `cs` (their sizes
`csz`) at the aliases `al`. -/
theorem match_fS {m : MachineData} (hf : Frame R.m0 160 slots 8 m) {cs : List (BitVec 64 × Nat)}
    {csz : List Nat} {ret : BitVec 64} (hreg : RegionsOk csz cs)
    {al : List (Sym × Nat × Int)}
    (hal : AllOf (fun p : Sym × Nat × Int ↦ p.1.eval (envOf R m cs ret) =
      (envOf R m cs ret).base p.2.1 + BitVec.ofInt 64 p.2.2) al) :
    Match (envOf R m cs ret) (fS csz al) m :=
  match_ofMachine ⟨rfl, rfl, hreg⟩ ⟨hf.rsp_eval, trivial⟩ trivial trivial
    (allOf_append hal argAl_ok)

/-- **A frame word** no write of a block covers is kept. -/
theorem fw_keep {m d' : MachineData} {cs : List (BitVec 64 × Nat)} {ret : BitVec 64} {S : SState}
    (hwf : (envOf R m cs ret).WF) (hm : Match (envOf R m cs ret) S d') {o' : Nat}
    (hok : MidOk 160 o' slots S = true) {o : Nat} (ho : o + 8 ≤ 168)
    (hmiss : ∀ w ∈ S.mem, w.r = 0 → w.off + w.n ≤ o ∨ o + 8 ≤ w.off) {v : BitVec 64}
    (h : R.FW m.dmem o v) : R.FW d'.dmem o v := by
  simp only [MidOk, Bool.and_eq_true] at hok
  refine NativeRustcVm.BytesAt.of_sameOutside (R := fun q ↦ Written (envOf R m cs ret) S q) h
    (fun q hq ↦ hm.get?_mem0 hwf hq) fun i hi ↦ ?_
  have hi' : i < 8 := by rw [NativeRustcVm.length_wordBytes] at hi; exact hi
  have := NativeRustcVmX64.Transcript.not_written0 hwf hm hok.1.1.2 (j := o + i) (by omega)
    fun w hw hr ↦ by have := hmiss w hw hr; omega
  rwa [NativeRustcVm.Transcript.off, ← NativeRustcVm.addr_add_add] at this

omit [Labels] in
/-- An environment's register is the machine's. -/
theorem envRegs (m : MachineData) (rs : List (BitVec 64 × Nat)) (vs : Nat → BitVec 64)
    (ret : BitVec 64) (r : Reg64) : (Env.ofMachine m rs vs ret).regs r = reg m r := rfl

/-- A register a block keeps. -/
theorem kreg {m m' : MachineData} {rs : List (BitVec 64 × Nat)} {vs : Nat → BitVec 64}
    {ret : BitVec 64} {S' : SState} (hm' : Match (Env.ofMachine m rs vs ret) S' m') {r : Reg64}
    (h : S'.reg r = some (.reg r)) {v : BitVec 64} (hv : reg m r = v) : reg m' r = v :=
  (hm'.regs r _ h).trans hv

/-- A register a block set from another, kept register. -/
theorem kregV {m m' : MachineData} {rs : List (BitVec 64 × Nat)} {vs : Nat → BitVec 64}
    {ret : BitVec 64} {S' : SState} (hm' : Match (Env.ofMachine m rs vs ret) S' m') {r x : Reg64}
    (h : S'.reg r = some (.reg x)) {v : BitVec 64} (hv : reg m x = v) : reg m' r = v :=
  (hm'.regs r _ h).trans hv

omit [Labels] in
/-- A frame word, its value rewritten. -/
theorem fw_eq {d : Mem 64} {o : Nat} {v v' : BitVec 64} (h : R.FW d o v) (e : v = v') :
    R.FW d o v' := e ▸ h

/-- The frame words at the offsets `os` a block keeps. -/
theorem fw_keepAll {m d' : MachineData} {cs : List (BitVec 64 × Nat)} {ret : BitVec 64}
    {S : SState} (hwf : (envOf R m cs ret).WF) (hm : Match (envOf R m cs ret) S d') {o' : Nat}
    (hok : MidOk 160 o' slots S = true) {os : List Nat} (hmiss : missAll os S = true) {o : Nat}
    (ho : o ∈ os) (ho8 : o + 8 ≤ 168) {v : BitVec 64} (h : R.FW m.dmem o v) : R.FW d'.dmem o v :=
  fw_keep hwf hm hok ho8 (missAll_spec hmiss ho) h

omit [Labels] in
/-- A frame word, loaded. -/
theorem fw_load {m : MachineData} {cs : List (BitVec 64 × Nat)} {ret : BitVec 64} {o : Nat}
    {v : BitVec 64} (h : R.FW m.dmem o v) : (envOf R m cs ret).load 0 o 8 = v := by
  rw [load_eq_wordOf, show (envOf R m cs ret).base 0 = R.fb from rfl, Env.ofMachine_mem0,
    NativeRustcVm.wordOf_of_wordAt h]

/-- **A frame word stored** by a block. -/
theorem fw_write {m d' : MachineData} {cs : List (BitVec 64 × Nat)} {ret : BitVec 64} {S : SState}
    (hm : Match (envOf R m cs ret) S d') {o : Nat} (ho : o + 8 ≤ 168) {v : Sym}
    (hw : ∀ i < 8, findWrite 0 (o + i) S.mem = some (v, i)) :
    R.FW d'.dmem o (v.eval (envOf R m cs ret)) :=
  NativeRustcVmX64.Transcript.wordAt_write hm (r := 0) rfl ho hw

end

variable [Host]

/-- **A block from a state of the body** writing the frame below the slots and region `ro`, inside
the phase: the state kept, the memory changed only there, the block's result, its exit. -/
theorem blkW (G : Geo R) (hp : Placed code R.k) {b : List Directive} {j : Nat}
    (hin : b.IsInfixAt code j) (hne : b ≠ []) {S S' : SState} {x : Exit}
    (hx : exec b S = some (S', x)) {cs : List (BitVec 64 × Nat)} {ret : BitVec 64}
    {st : MachineState} (hF : Fr R 8 st.data) (hpc : st.pc = pcOf R j)
    (hwf : (envOf R st.data cs ret).WF) (hm : Match (envOf R st.data cs ret) S st.data)
    (hret : ∀ l, x = .call l → ret = (Host.addrOf (R.k + j + b.length)).toBitVec)
    {o : Nat} (hok : MidOk 160 o slots S' = true) {ro : Nat} {rb : BitVec 64} {rsz : Nat}
    (hro : (envOf R st.data cs ret).regions[ro]? = some (rb, rsz)) {lo n : Nat} {a : BitVec 64}
    (ha : rb + BitVec.ofNat 64 lo = a) (hrin : Inside a n (R.big 7))
    (hW : ∀ w ∈ S'.mem, w.r = 0 ∨ (w.r = ro ∧ lo ≤ w.off ∧ w.off + w.n ≤ lo + n))
    {Q : MachineState → Prop}
    (cont : ∀ st', Fr R o st'.data → Match (envOf R st.data cs ret) S' st'.data →
      PcOk (envOf R st.data cs ret) x (Host.addrOf (R.k + j + b.length)) st' →
      NativeRustcVm.SameOutside st.data.dmem st'.data.dmem
        (fun q ↦ NativeRustcVm.InRange R.fb 160 q ∨ NativeRustcVm.InRange a n q) →
      Eventually (step1 Host.exe) Q st') :
    Eventually (step1 Host.exe) Q st :=
  exec_at (infix_of hin hne hp) hx hwf hret hpc hm fun st' hm' hpc' ↦
    have hs : NativeRustcVm.SameOutside st.data.dmem st'.data.dmem
        (fun q ↦ NativeRustcVm.InRange R.fb 160 q ∨ NativeRustcVm.InRange a n q) :=
      fun _ hq ↦ hm'.get?_mem0 hwf fun hW' ↦ hq (written_in hwf (midOk_br hok) (fun w hw ↦
        (hW w hw).imp_right fun ⟨hr, h1, h2⟩ b sz hb jj hj1 hj2 ↦ by
          rw [hr, hro] at hb
          cases hb
          have hnw := hrin.noWrap G.outNw
          unfold NativeRustcVm.NoWrap at hnw
          rw [show jj = lo + (jj - lo) by omega, ← NativeRustcVm.addr_add_add, ha]
          exact NativeRustcVm.inRange_add (by omega) (by omega)) hW')
    cont st' ⟨Frame.of_block hF.fr hwf hm' hok slots_le,
      hF.chg.trans hs fun _ h ↦ h.imp_right (hrin.inRange G.outNw)⟩ hm' hpc' hs

/-- **A block from a state of the body** writing only the frame below the slots. -/
theorem blk (hp : Placed code R.k) {b : List Directive} {j : Nat}
    (hin : b.IsInfixAt code j) (hne : b ≠ []) {S S' : SState} {x : Exit}
    (hx : exec b S = some (S', x)) {cs : List (BitVec 64 × Nat)} {ret : BitVec 64}
    {st : MachineState} (hF : Fr R 8 st.data) (hpc : st.pc = pcOf R j)
    (hwf : (envOf R st.data cs ret).WF) (hm : Match (envOf R st.data cs ret) S st.data)
    (hret : ∀ l, x = .call l → ret = (Host.addrOf (R.k + j + b.length)).toBitVec)
    {o : Nat} (hok : MidOk 160 o slots S' = true) (hW : ∀ w ∈ S'.mem, w.r = 0)
    {Q : MachineState → Prop}
    (cont : ∀ st', Fr R o st'.data → Match (envOf R st.data cs ret) S' st'.data →
      PcOk (envOf R st.data cs ret) x (Host.addrOf (R.k + j + b.length)) st' →
      NativeRustcVm.SameOutside st.data.dmem st'.data.dmem (NativeRustcVm.InRange R.fb 160) →
      Eventually (step1 Host.exe) Q st') :
    Eventually (step1 Host.exe) Q st :=
  exec_at (infix_of hin hne hp) hx hwf hret hpc hm fun st' hm' hpc' ↦
    have hs : NativeRustcVm.SameOutside st.data.dmem st'.data.dmem
        (NativeRustcVm.InRange R.fb 160) :=
      fun _ hq ↦ hm'.get?_mem0 hwf fun hW' ↦ hq ((written_in (P := fun _ ↦ False) hwf (midOk_br hok)
        (fun w hw ↦ .inl (hW w hw)) hW').elim id False.elim)
    cont st' ⟨Frame.of_block hF.fr hwf hm' hok slots_le,
      hF.chg.trans hs fun _ h ↦ .inl h⟩ hm' hpc' hs

end Blocks

end

end NativeRustcVmX64.Wire.WriteOpenings
