module

public import NativeRustcVmX64.Wire.ClimbLevel.Exec
public import NativeRustcVmX64.Wire.Frame
public import NativeRustcVmX64.Wire.Common
public import NativeRustcVmX64.Spec.Wire
public import NativeRustcVm.Wire.ClimbFacts
public import NativeRustcVm.Wire.ReaderFacts
public import NativeRustcVm.Wire.WordsFacts
public import NativeRustcX64.Got

/-!
# `climb_level`'s places and memory (x86-64)

The nodes at RSI (`nd j`), the siblings at RCX (`sb i`), the parents at R8 (`pa p`), 40 bytes
each; the frame (208 bytes below the entry's RSP, `fb`). `Geo`: where everything is, as numbers.
The locals (`Loc`), the next node's index and address (`Nx`); the memory with the siblings `ss`
and the parents `ps` written (`MemS`), what a step may change (`Mov`) and what survives it
(`MemS.keep`); a block's writes as numbers (`written_num`).
-/

namespace NativeRustcVmX64.Wire.ClimbLevel

open NativeRustcX64 NativeRustcX64.Sym NativeRustcVm.Wire NativeVm.Wire
open NativeRustcVmX64.Vm.ClimbLevel
open NativeRustcVmX64.Transcript (Frame frameEnv frame_wf frame_mapped frame_noWrap
  Frame.of_block after after_eq MidOk)
open NativeRustcVm.Transcript (Mapped.keeps off off_zero off_add off_off toNat_off)
open NativeRustcVm (WordAt WordsAt)
open LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.Compile

@[expose] public section

/-- The reader's address. -/
abbrev rdr (m0 : MachineData) : BitVec 64 := reg m0 .rdi
/-- The nodes' address. -/
abbrev nodes (m0 : MachineData) : BitVec 64 := reg m0 .rsi
/-- The nodes' count. -/
abbrev cnt (m0 : MachineData) : Nat := (reg m0 .rdx).toNat
/-- The siblings' address. -/
abbrev sibs (m0 : MachineData) : BitVec 64 := reg m0 .rcx
/-- The parents' address. -/
abbrev nxt (m0 : MachineData) : BitVec 64 := reg m0 .r8
/-- Node `j`'s address. -/
abbrev nd (m0 : MachineData) (j : Nat) : BitVec 64 := off (nodes m0) (40 * j)
/-- The frame's base. -/
abbrev fb (m0 : MachineData) : BitVec 64 := stackBelow m0 208
/-- The entry's RSP, as a number. -/
abbrev sp (m0 : MachineData) : Nat := (rspOf m0).toNat
/-- The outputs. -/
abbrev W (m0 : MachineData) (q : BitVec 64) : Prop :=
  NativeRustcVm.InRange (sibs m0) nodesBytes q ∨ NativeRustcVm.InRange (nxt m0) nodesBytes q

/-- The places of `climb_level`, as numbers. -/
structure Geo [Labels] (m0 : MachineData) (bp : BitVec 64) (L : Nat) : Prop where
  g : RGeo m0 climbLevelStack (rdr m0) bp L (W m0)
  rc : RcAt m0 climbLevelStack
  n256 : cnt m0 ≤ 256
  nm : NativeRustcVm.Mapped m0.dmem (nodes m0) (40 * cnt m0)
  sm : NativeRustcVm.Mapped m0.dmem (sibs m0) 10240
  xm : NativeRustcVm.Mapped m0.dmem (nxt m0) 10240
  nN : (nodes m0).toNat + 40 * cnt m0 ≤ 2 ^ 64
  sN : (sibs m0).toNat + 10240 ≤ 2 ^ 64
  xN : (nxt m0).toNat + 10240 ≤ 2 ^ 64
  nS : (nodes m0).toNat + 40 * cnt m0 ≤ sp m0 - 1056 ∨ sp m0 + 8 ≤ (nodes m0).toNat
  sS : (sibs m0).toNat + 10240 ≤ sp m0 - 1056 ∨ sp m0 + 8 ≤ (sibs m0).toNat
  xS : (nxt m0).toNat + 10240 ≤ sp m0 - 1056 ∨ sp m0 + 8 ≤ (nxt m0).toNat
  rS : (rdr m0).toNat + 24 ≤ sp m0 - 1056 ∨ sp m0 + 8 ≤ (rdr m0).toNat
  nR : (nodes m0).toNat + 40 * cnt m0 ≤ (rdr m0).toNat ∨ (rdr m0).toNat + 24 ≤ (nodes m0).toNat
  sR : (sibs m0).toNat + 10240 ≤ (rdr m0).toNat ∨ (rdr m0).toNat + 24 ≤ (sibs m0).toNat
  xR : (nxt m0).toNat + 10240 ≤ (rdr m0).toNat ∨ (rdr m0).toNat + 24 ≤ (nxt m0).toNat
  nB : (nodes m0).toNat + 40 * cnt m0 ≤ bp.toNat ∨ bp.toNat + L ≤ (nodes m0).toNat
  nX : (nodes m0).toNat + 40 * cnt m0 ≤ (sibs m0).toNat ∨ (sibs m0).toNat + 10240 ≤ (nodes m0).toNat
  nY : (nodes m0).toNat + 40 * cnt m0 ≤ (nxt m0).toNat ∨ (nxt m0).toNat + 10240 ≤ (nodes m0).toNat
  sX : (sibs m0).toNat + 10240 ≤ (nxt m0).toNat ∨ (nxt m0).toNat + 10240 ≤ (sibs m0).toNat
  cR : rcAddr.toNat + 192 ≤ (rdr m0).toNat ∨ (rdr m0).toNat + 24 ≤ rcAddr.toNat
  cS : rcAddr.toNat + 192 ≤ (sibs m0).toNat ∨ (sibs m0).toNat + 10240 ≤ rcAddr.toNat
  cX : rcAddr.toNat + 192 ≤ (nxt m0).toNat ∨ (nxt m0).toNat + 10240 ≤ rcAddr.toNat
  got : GotAt m0 climbLevelStack
    [(rcAddr, 192), (rdr m0, 24), (sibs m0, nodesBytes), (nxt m0, nodesBytes)]
    ["memcpy", "memset"]

/-- What a run may change of the entry's memory: the stack, the reader's cursor, the outputs. -/
def Chg (m0 : MachineData) (d : Mem 64) : Prop :=
  NativeRustcVm.SameOutside m0.dmem d fun q ↦
    (sp m0 - 1056 ≤ q.toNat ∧ q.toNat < sp m0) ∨
    ((rdr m0).toNat + 16 ≤ q.toNat ∧ q.toNat < (rdr m0).toNat + 24) ∨
    ((sibs m0).toNat ≤ q.toNat ∧ q.toNat < (sibs m0).toNat + 10240) ∨
    ((nxt m0).toNat ≤ q.toNat ∧ q.toNat < (nxt m0).toNat + 10240)

/-- The locals: the reader at `40`, the nodes' end at `48`, their address less 40 at `56`, `40 n`
at `64`. -/
structure Loc (m0 : MachineData) (d : Mem 64) : Prop where
  rd : WordAt d (off (fb m0) 40) (UInt64.ofBitVec (rdr m0))
  en : WordAt d (off (fb m0) 48) (UInt64.ofBitVec (nd m0 (cnt m0)))
  bm : WordAt d (off (fb m0) 56)
    (UInt64.ofBitVec (nodes m0 + BitVec.ofNat 64 18446744073709551576))
  n40 : WordAt d (off (fb m0) 64) (UInt64.ofBitVec (BitVec.ofNat 64 (40 * cnt m0)))

/-- The next node's index `j` at `72` and address at `80`. -/
structure Nx (m0 : MachineData) (j : Nat) (d : Mem 64) : Prop where
  ix : WordAt d (off (fb m0) 72) (UInt64.ofBitVec (BitVec.ofNat 64 j))
  ad : WordAt d (off (fb m0) 80) (UInt64.ofBitVec (nd m0 j))

/-- **The memory** with the siblings `ss` and the parents `ps` written, the reader at `ci`. -/
structure MemS (m0 : MachineData) (bp : BitVec 64) (B : List UInt8) (ns ss ps : List (Nat × Digest))
    (ci : Nat) (d : Mem 64) : Prop where
  rd : ReaderAt d (rdr m0) bp B ci
  sb : NodesAt d (sibs m0) ss
  nx : NodesAt d (nxt m0) ps
  nd : NodesAt d (nodes m0) ns
  loc : Loc m0 d
  chg : Chg m0 d
  ls : ss.length ≤ 256
  lp : ps.length ≤ 256

/-- The bytes a step may change, the siblings `ls` and the parents `lp` written: the stack below
the locals and above them, the siblings from `ls`, the parents from `lp`. -/
def Mov (m0 : MachineData) (ls lp : Nat) (q : BitVec 64) : Prop :=
  (sp m0 - 1056 ≤ q.toNat ∧ q.toNat < sp m0 - 168) ∨
  (sp m0 - 136 ≤ q.toNat ∧ q.toNat < sp m0 - 48) ∨
  ((sibs m0).toNat + 40 * ls ≤ q.toNat ∧ q.toNat < (sibs m0).toNat + 10240) ∨
  ((nxt m0).toNat + 40 * lp ≤ q.toNat ∧ q.toNat < (nxt m0).toNat + 10240)

/-- No node before `j` is node `i`'s sibling. -/
def Miss (ns : List (Nat × Digest)) (i j : Nat) : Prop :=
  ∀ j' (h : j' < j) (hj : j' < ns.length) (hi : i < ns.length), ns[j'].1 ≠ ns[i].1 ^^^ 1

/-- What `climb_level` reaches. -/
abbrev Post [Labels] (m0 : MachineData) (st : MachineState) : Prop :=
  st.pc = retOf m0 ∧ rspOf st.data = rspOf m0 + 8#64 ∧ ClimbLevelPost m0 st.data

end

public section

theorem slots_le : ∀ p ∈ slots, p.1 + 8 ≤ 208 := by decide

theorem stack_eq : climbLevelStack = 1056 := by decide

theorem hps_eq : hashPairStack = 848 := by decide

theorem rds_eq : readerDigestStack = 48 := by decide

theorem keeps_of {S : SState} {xs : List Reg64} (h : Keeps xs S = true) :
    ∀ x ∈ xs, S.reg x = some (.reg x) := by
  intro x hx
  simp only [Keeps, List.all_eq_true, beq_iff_eq] at h
  exact h x hx

/-- The registers a block keeps (`Keeps`), from its registers' values. -/
theorem regs_kept [Labels] {S : SState} {xs : List Reg64} (hK : Keeps xs S = true)
    {s s' : MachineData} {rs : List (BitVec 64 × Nat)} {vars : Nat → BitVec 64} {ret : BitVec 64}
    (hr : ∀ r v, S.reg r = some v → reg s' r = v.eval (Env.ofMachine s rs vars ret)) :
    ∀ x ∈ xs, reg s' x = reg s x :=
  fun x hx ↦ hr x _ (keeps_of hK x hx)

/-- A list of registers within another. -/
theorem mem_of_all {xs ys : List Reg64} (h : (xs.all fun x ↦ ys.any (· == x)) = true) {x : Reg64}
    (hx : x ∈ xs) : x ∈ ys := by
  obtain ⟨y, hy, he⟩ := List.any_eq_true.mp (List.all_eq_true.mp h x hx)
  rwa [Reg64.eq_of_beq he] at hy

variable {m0 : MachineData} {bp : BitVec 64} {L : Nat}

theorem sp_eq (m0 : MachineData) : sp m0 = (rspOf m0).toNat := rfl

/-! ## A block's writes -/

/-- **A block's writes** in the frame environment with regions `rest`: within offsets `lo` to `hi`
of the frame, or in a region of `rest`. -/
theorem written_num [Labels] {rest : List (BitVec 64 × Nat)} {vars : Nat → BitVec 64}
    {ret : BitVec 64} {S : SState} {d d' : MachineData}
    (hm : Match (frameEnv m0 d 208 rest vars ret) S d') (hin : NativeRustcVmX64.Transcript.writesIn S = true)
    {lo hi : Nat} (hfr : FrW lo hi S = true) {q : BitVec 64}
    (h : Written (frameEnv m0 d 208 rest vars ret) S q) :
    ((fb m0).toNat + lo ≤ q.toNat ∧ q.toNat < (fb m0).toNat + hi) ∨
      ∃ x ∈ rest, x.1.toNat ≤ q.toNat ∧ q.toNat < x.1.toNat + x.2 := by
  obtain ⟨w, hw, b, sz, hb, h1, h2⟩ := h
  unfold NativeRustcVmX64.Transcript.writesIn at hin
  rw [List.all_eq_true] at hin
  have hw' := hin w hw
  obtain ⟨sz', hS'⟩ : ∃ sz', S.regions[w.r]? = some sz' := by
    revert hw'
    cases S.regions[w.r]? with
    | none => simp
    | some x => exact fun _ ↦ ⟨x, rfl⟩
  rw [hS'] at hw'
  simp only [decide_eq_true_eq] at hw'
  obtain ⟨b', hb'⟩ := hm.regions _ _ hS'
  rw [hb] at hb'
  cases hb'
  unfold FrW at hfr
  rw [List.all_eq_true] at hfr
  have hf := hfr w hw
  match hr : w.r, hb with
  | 0, hb =>
    cases hb
    left
    simp only [hr, bne_self_eq_false, Bool.false_or, Bool.and_eq_true, decide_eq_true_eq] at hf
    dsimp only [fb]
    omega
  | r + 1, hb =>
    right
    refine ⟨(b, sz), List.mem_of_getElem? hb, by dsimp only; omega, by dsimp only; omega⟩

/-- Memory after a block: changed only where it wrote (`written_num`). -/
theorem same_num [Labels] {rest : List (BitVec 64 × Nat)} {vars : Nat → BitVec 64}
    {ret : BitVec 64} {S : SState} {d d' : MachineData}
    (hwf : (frameEnv m0 d 208 rest vars ret).WF)
    (hm : Match (frameEnv m0 d 208 rest vars ret) S d')
    (hin : NativeRustcVmX64.Transcript.writesIn S = true) {lo hi : Nat} (hfr : FrW lo hi S = true) :
    NativeRustcVm.SameOutside d.dmem d'.dmem fun q ↦
      ((fb m0).toNat + lo ≤ q.toNat ∧ q.toNat < (fb m0).toNat + hi) ∨
        ∃ x ∈ rest, x.1.toNat ≤ q.toNat ∧ q.toNat < x.1.toNat + x.2 :=
  fun _ hq ↦ hm.get?_mem0 hwf fun hW ↦ hq (written_num hm hin hfr hW)

/-! ## Memory -/

theorem nodesAt_keep {d d' : Mem 64} {a : BitVec 64} {l : List (Nat × Digest)}
    (h : NodesAt d a l) (hnw : a.toNat + 40 * l.length ≤ 2 ^ 64) {R : BitVec 64 → Prop}
    (hs : NativeRustcVm.SameOutside d d' R)
    (hR : ∀ q, R q → ¬(a.toNat ≤ q.toNat ∧ q.toNat < a.toNat + 40 * l.length)) :
    NodesAt d' a l :=
  NodesAt.of_sameOutside h hs fun i hi hq ↦ hR _ hq (by
    rw [NativeRustcVm.toNat_add_ofNat (by omega)]; omega)

theorem wordAt_keep {d d' : Mem 64} {a : BitVec 64} {w : UInt64} (h : WordAt d a w)
    (hnw : a.toNat + 8 ≤ 2 ^ 64) {R : BitVec 64 → Prop} (hs : NativeRustcVm.SameOutside d d' R)
    (hR : ∀ q, R q → ¬(a.toNat ≤ q.toNat ∧ q.toNat < a.toNat + 8)) : WordAt d' a w :=
  NativeRustcVm.BytesAt.of_sameOutside h hs fun i hi hq ↦ hR _ hq (by
    simp only [NativeRustcVm.length_wordBytes] at hi
    rw [NativeRustcVm.toNat_add_ofNat (by omega)]; omega)

theorem wordsAt_keep {d d' : Mem 64} {a : BitVec 64} {ws : List UInt64} (h : WordsAt d a ws)
    (hnw : a.toNat + 8 * ws.length ≤ 2 ^ 64) {R : BitVec 64 → Prop}
    (hs : NativeRustcVm.SameOutside d d' R)
    (hR : ∀ q, R q → ¬(a.toNat ≤ q.toNat ∧ q.toNat < a.toNat + 8 * ws.length)) :
    WordsAt d' a ws :=
  NativeRustcVm.BytesAt.of_sameOutside h hs fun i hi hq ↦ hR _ hq (by
    rw [NativeRustcVm.length_wordsBytes] at hi
    rw [NativeRustcVm.toNat_add_ofNat (by omega)]; omega)

theorem chg_trans {d d' : Mem 64} (h : Chg m0 d) {R : BitVec 64 → Prop}
    (hs : NativeRustcVm.SameOutside d d' R)
    (hR : ∀ q, R q → (sp m0 - 1056 ≤ q.toNat ∧ q.toNat < sp m0) ∨
      ((rdr m0).toNat + 16 ≤ q.toNat ∧ q.toNat < (rdr m0).toNat + 24) ∨
      ((sibs m0).toNat ≤ q.toNat ∧ q.toNat < (sibs m0).toNat + 10240) ∨
      ((nxt m0).toNat ≤ q.toNat ∧ q.toNat < (nxt m0).toNat + 10240)) : Chg m0 d' :=
  fun q hq ↦ (hs q fun h ↦ hq (hR q h)).trans (h q hq)

/-- **A node more** at the siblings' end. -/
theorem nodesAt_snoc' {d d' : Mem 64} {a : BitVec 64} {l : List (Nat × Digest)}
    {x : Nat × Digest} (h : NodesAt d a l) (hnw : a.toNat + 40 * (l.length + 1) ≤ 2 ^ 64)
    (hx : NodeAt d' (off a (40 * l.length)) x) {R : BitVec 64 → Prop}
    (hs : NativeRustcVm.SameOutside d d' R)
    (hR : ∀ q, R q → ¬(a.toNat ≤ q.toNat ∧ q.toNat < a.toNat + 40 * l.length)) :
    NodesAt d' a (l ++ [x]) := by
  intro j hj
  simp only [List.length_append, List.length_singleton] at hj
  rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hj) with hj | rfl
  · rw [List.getElem_append_left hj]
    refine (h j hj).of_sameOutside hs fun i hi hq ↦ hR _ hq ?_
    rw [NativeRustcVm.toNat_add_ofNat (by rw [toNat_off (by omega)]; omega), toNat_off (by omega)]
    omega
  · rw [List.getElem_append_right (le_refl _)]
    simpa using hx

variable [Labels]

/-! ## Numbers -/

theorem Geo.s0 (g : Geo m0 bp L) : 1056 ≤ sp m0 ∧ sp m0 + 8 ≤ 2 ^ 64 := by
  have h := g.g.st
  rw [stack_eq] at h
  exact ⟨h.1, h.2.1⟩

theorem Geo.fb_toNat (g : Geo m0 bp L) : (fb m0).toNat = sp m0 - 208 :=
  NativeRustcVmX64.stackBelow_toNat (by have := g.s0; rw [← sp_eq]; omega)

/-- An offset of the frame, as a number. -/
theorem Geo.fo (g : Geo m0 bp L) {o : Nat} (ho : o < 216) :
    (off (fb m0) o).toNat = sp m0 - 208 + o := by
  have := g.s0
  have := sp_eq m0
  rw [toNat_off (by rw [g.fb_toNat]; omega), g.fb_toNat]

theorem Geo.nd_toNat (g : Geo m0 bp L) {o : Nat} (h : o < 40 * cnt m0) :
    (off (nodes m0) o).toNat = (nodes m0).toNat + o :=
  toNat_off (by have := g.nN; omega)

theorem Geo.sb_toNat (g : Geo m0 bp L) {o : Nat} (h : o < 10240) :
    (off (sibs m0) o).toNat = (sibs m0).toNat + o :=
  toNat_off (by have := g.sN; omega)

theorem Geo.pa_toNat (g : Geo m0 bp L) {o : Nat} (h : o < 10240) :
    (off (nxt m0) o).toNat = (nxt m0).toNat + o :=
  toNat_off (by have := g.xN; omega)

theorem Geo.rNw (g : Geo m0 bp L) : (rdr m0).toNat + 24 ≤ 2 ^ 64 := g.g.rNw

/-- The rounds' constants, kept by a change of the run's memory. -/
theorem Geo.rc_keep (g : Geo m0 bp L) {d : Mem 64} (h : Chg m0 d) :
    ∀ i < 192, d.get? (rcAddr + BitVec.ofNat 64 i) = m0.dmem.get? (rcAddr + BitVec.ofNat 64 i) := by
  have hrc := g.rc
  rw [stack_eq] at hrc
  obtain ⟨-, hnw, hap⟩ := hrc
  have hs0 := g.s0
  have := sp_eq m0
  have hsb : (stackBelow m0 1056).toNat = sp m0 - 1056 := NativeRustcVmX64.stackBelow_toNat hs0.1
  unfold NativeRustcVm.Apart at hap
  unfold NativeRustcVm.NoWrap at hnw
  rw [hsb] at hap
  have hcR := g.cR
  have hcS := g.cS
  have hcX := g.cX
  intro i hi
  refine h _ fun hq ↦ ?_
  dsimp only at hq
  rw [NativeRustcVm.toNat_add_ofNat (by omega)] at hq
  omega

/-- The loader slots survive every write allowed by `climb_level`. -/
theorem Geo.got_keep (g : Geo m0 bp L) {d : Mem 64} (h : Chg m0 d) :
    ∀ l ∈ ["memcpy", "memset"], ∀ i < 8,
      d.get? (gotAddr l + BitVec.ofNat 64 i) =
        m0.dmem.get? (gotAddr l + BitVec.ofNat 64 i) := by
  intro l hl i hi
  obtain ⟨_, hn, hs, ha⟩ := g.got.1 l hl
  have hr := ha (rdr m0, 24) (by simp)
  have hsb := ha (sibs m0, nodesBytes) (by simp)
  have hx := ha (nxt m0, nodesBytes) (by simp)
  change Apart (gotAddr l) 8 (stackBelow m0 1056) 1064 at hs
  have ht : (stackBelow m0 1056).toNat = sp m0 - 1056 := stackBelow_toNat g.s0.1
  unfold Apart at hs hr hsb hx
  change (gotAddr l).toNat + 8 ≤ 2 ^ 64 at hn
  rw [ht] at hs
  change (gotAddr l).toNat + 8 ≤ (rdr m0).toNat ∨
    (rdr m0).toNat + 24 ≤ (gotAddr l).toNat at hr
  change (gotAddr l).toNat + 8 ≤ (sibs m0).toNat ∨
    (sibs m0).toNat + 10240 ≤ (gotAddr l).toNat at hsb
  change (gotAddr l).toNat + 8 ≤ (nxt m0).toNat ∨
    (nxt m0).toNat + 10240 ≤ (gotAddr l).toNat at hx
  refine h _ fun hq => ?_
  dsimp only at hq
  rw [NativeRustcVm.toNat_add_ofNat (by omega)] at hq
  omega

/-! ## The memory -/

theorem Loc.keep (g : Geo m0 bp L) {d d' : Mem 64} (h : Loc m0 d) {R : BitVec 64 → Prop}
    (hs : NativeRustcVm.SameOutside d d' R)
    (hR : ∀ q, R q → ¬(sp m0 - 168 ≤ q.toNat ∧ q.toNat < sp m0 - 136)) : Loc m0 d' := by
  have := g.s0
  have := sp_eq m0
  have e : ∀ o, o < 216 → (off (fb m0) o).toNat = sp m0 - 208 + o := fun o ho ↦ g.fo ho
  refine ⟨wordAt_keep h.rd (by rw [e 40 (by omega)]; omega) hs fun q hq ↦ ?_,
    wordAt_keep h.en (by rw [e 48 (by omega)]; omega) hs fun q hq ↦ ?_,
    wordAt_keep h.bm (by rw [e 56 (by omega)]; omega) hs fun q hq ↦ ?_,
    wordAt_keep h.n40 (by rw [e 64 (by omega)]; omega) hs fun q hq ↦ ?_⟩ <;>
  · have := hR q hq; rw [e _ (by omega)]; omega

theorem Nx.keep (g : Geo m0 bp L) {j : Nat} {d d' : Mem 64} (h : Nx m0 j d) {R : BitVec 64 → Prop}
    (hs : NativeRustcVm.SameOutside d d' R)
    (hR : ∀ q, R q → ¬(sp m0 - 136 ≤ q.toNat ∧ q.toNat < sp m0 - 120)) : Nx m0 j d' := by
  have := g.s0
  have := sp_eq m0
  have e : ∀ o, o < 216 → (off (fb m0) o).toNat = sp m0 - 208 + o := fun o ho ↦ g.fo ho
  refine ⟨wordAt_keep h.ix (by rw [e 72 (by omega)]; omega) hs fun q hq ↦ ?_,
    wordAt_keep h.ad (by rw [e 80 (by omega)]; omega) hs fun q hq ↦ ?_⟩ <;>
  · have := hR q hq; rw [e _ (by omega)]; omega

/-- The reader survives a change of the stack and the outputs. -/
theorem Geo.reader {B : List UInt8} {c : Nat} (g : Geo m0 bp B.length) {d d' : Mem 64}
    (hR : ReaderAt d (rdr m0) bp B c) {R : BitVec 64 → Prop}
    (hs : NativeRustcVm.SameOutside d d' R)
    (hR' : ∀ q, R q → (sp m0 - 1056 ≤ q.toNat ∧ q.toNat < sp m0) ∨
      ((sibs m0).toNat ≤ q.toNat ∧ q.toNat < (sibs m0).toNat + 10240) ∨
      ((nxt m0).toNat ≤ q.toNat ∧ q.toNat < (nxt m0).toNat + 10240)) :
    ReaderAt d' (rdr m0) bp B c := by
  have hs0 := g.s0
  have := sp_eq m0
  have hsb : (stackBelow m0 climbLevelStack).toNat = sp m0 - 1056 := by
    rw [stack_eq]; exact NativeRustcVmX64.stackBelow_toNat hs0.1
  have hsN := g.sN
  have hxN := g.xN
  refine g.g.reader_frame rfl hR fun q hq ↦ hs q fun h ↦ hq ?_
  rcases hR' q h with h1 | h1 | h1
  · left
    rw [NativeRustcVm.inRange_iff (by unfold NativeRustcVm.NoWrap; rw [hsb, stack_eq]; omega), hsb,
      stack_eq]
    omega
  · right; left
    rw [NativeRustcVm.inRange_iff (by unfold NativeRustcVm.NoWrap nodesBytes; omega)]
    unfold nodesBytes; omega
  · right; right
    rw [NativeRustcVm.inRange_iff (by unfold NativeRustcVm.NoWrap nodesBytes; omega)]
    unfold nodesBytes; omega

variable {B : List UInt8} {ns : List (Nat × Digest)}

/-- **What survives a step's change** of `Mov`. -/
theorem MemS.keep (g : Geo m0 bp B.length) {ss ps : List (Nat × Digest)} {ci : Nat}
    {d d' : Mem 64} (h : MemS m0 bp B ns ss ps ci d) (hl : ns.length = cnt m0)
    {R : BitVec 64 → Prop} (hs : NativeRustcVm.SameOutside d d' R)
    (hR : ∀ q, R q → Mov m0 ss.length ps.length q) : MemS m0 bp B ns ss ps ci d' := by
  have := g.s0
  have := sp_eq m0
  have hls := h.ls
  have hlp := h.lp
  have hsS := g.sS
  have hxS := g.xS
  have hnS := g.nS
  have hsX := g.sX
  have hnX := g.nX
  have hnY := g.nY
  have hsN := g.sN
  have hxN := g.xN
  refine ⟨g.reader h.rd hs fun q hq ↦ ?_, nodesAt_keep h.sb (by omega) hs fun q hq ↦ ?_,
    nodesAt_keep h.nx (by omega) hs fun q hq ↦ ?_,
    nodesAt_keep h.nd (by rw [hl]; exact g.nN) hs fun q hq ↦ ?_,
    h.loc.keep g hs fun q hq ↦ ?_, chg_trans h.chg hs fun q hq ↦ ?_, hls, hlp⟩ <;>
  · have := hR q hq; unfold Mov at this; omega


end

end NativeRustcVmX64.Wire.ClimbLevel
