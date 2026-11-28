module

public import NativeRustcVmX64.Wire.RdRows.Exec
public import NativeRustcVmX64.Wire.Frame
public import NativeRustcVmX64.Wire.Common
public import NativeRustcVmX64.Spec.Wire
public import NativeRustcVm.Wire.RowsFacts
public import NativeRustcVm.Wire.WordsFacts
public import NativeRustcVm.Wire.ReaderFacts
import NativeVm.Wire.Read

/-!
# `rd_rows`' places and states (x86-64)

The leaves at `lv` (`512` bytes each, `leaf i`), the frame (80 bytes below the entry's RSP, `sb`),
its locals (`Loc`: `lw` at `8`, the reader at `16`), what a run changes (`Chg`: the stack, the
reader's cursor, the leaves), the memory after `i` rows (`Kp`: the rows read, the reader past
them, their padded leaves, the locals); what it keeps of a change of the stack or of the leaves
past the first `i` (`Kp.keep`); the result at the return (`Res`, `fin`); a block of the body in
the frame (`fr_step`) or with one more region (`rg_step`).
-/

namespace NativeRustcVmX64.Wire.RdRows

open NativeRustcX64 NativeRustcX64.Sym NativeRustcVm.Wire NativeVm.Wire
open NativeRustcVmX64.Vm.RdRows
open NativeRustcVmX64.Transcript (Frame frameEnv frame_wf frame_mapped frame_noWrap
  Frame.of_block Frame.epilogue Frame.load_ret after after_eq inRange_mono MidOk EpiOk)
open NativeRustcVm.Transcript (Mapped.keeps off off_zero off_add)
open NativeRustcVm (WordAt WordsAt)
open LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.Compile

@[expose] public section

/-- The reader's address. -/
abbrev rdr (m0 : MachineData) : BitVec 64 := reg m0 .rdi
/-- The rows' count. -/
abbrev nr (m0 : MachineData) : Nat := (reg m0 .rsi).toNat
/-- The leaves' width. -/
abbrev lw (m0 : MachineData) : Nat := (reg m0 .rdx).toNat
/-- The rows' width. -/
abbrev rw (m0 : MachineData) : Nat := (reg m0 .rcx).toNat
/-- The leaves' address. -/
abbrev lv (m0 : MachineData) : BitVec 64 := reg m0 .r8
/-- The zeros before a row. -/
abbrev zc (m0 : MachineData) : Nat := lw m0 - rw m0
/-- The frame's base. -/
abbrev sb (m0 : MachineData) : BitVec 64 := stackBelow m0 80
/-- The leaves' bytes. -/
abbrev W (m0 : MachineData) : BitVec 64 → Prop := NativeRustcVm.InRange (lv m0) (512 * nr m0)
/-- The stack's bytes `rd_rows` may change. -/
abbrev Stk (m0 : MachineData) : BitVec 64 → Prop := NativeRustcVm.InRange (stackBelow m0 128) 128

/-- Whether every row's first word is zero, as `rd_rows` returns it. -/
def flag (rows : List (List K)) : Nat := if ∀ x ∈ rows, x.getD 0 0 = 0 then 1 else 0

/-- What a run may change of the entry's memory: the stack, the reader's cursor, the leaves. -/
def Chg (m0 : MachineData) (d : Mem 64) : Prop :=
  NativeRustcVm.SameOutside m0.dmem d fun q ↦
    Stk m0 q ∨ NativeRustcVm.InRange (rdr m0 + BitVec.ofNat 64 16) 8 q ∨ W m0 q

/-- The places of `rd_rows`. -/
structure Geo (m0 : MachineData) (bp : BitVec 64) (L : Nat) : Prop where
  g : RGeo m0 128 (rdr m0) bp L (W m0)
  lvMap : NativeRustcVm.Mapped m0.dmem (lv m0) (512 * nr m0)
  lvNw : (lv m0).toNat + 512 * nr m0 ≤ 2 ^ 64
  aS : NativeRustcVm.Apart (lv m0) (512 * nr m0) (stackBelow m0 128) (128 + 8)
  aR : NativeRustcVm.Apart (lv m0) (512 * nr m0) (rdr m0) 24
  aB : NativeRustcVm.Apart (lv m0) (512 * nr m0) bp L
  n0 : 0 < nr m0
  n256 : nr m0 ≤ 256
  lw64 : lw m0 ≤ 64
  rwlw : rw m0 ≤ lw m0

/-- The locals: `lw` at offset `8`, the reader at `16`. -/
structure Loc (m0 : MachineData) (d : Mem 64) : Prop where
  lw : WordAt d (off (sb m0) 8) (UInt64.ofBitVec (reg m0 .rdx))
  rd : WordAt d (off (sb m0) 16) (UInt64.ofBitVec (rdr m0))

/-- **The memory after `i` rows**: the rows read, the reader past them, their padded leaves, the
locals, the changes. -/
structure Kp (m0 : MachineData) (bp : BitVec 64) (B : List UInt8) (c i : Nat)
    (rows : List (List K)) (ci : Nat) (d : Mem 64) : Prop where
  hrows : rdRows B (rw m0) i c = some (rows, ci)
  hrd : ReaderAt d (rdr m0) bp B ci
  hlvs : LeavesAt d (lv m0) (rows.map fun x ↦ paddedLeaf x (lw m0))
  hloc : Loc m0 d
  hchg : Chg m0 d

/-- The result `v` at the return, in the model's terms. -/
def Res (m0 : MachineData) (bp : BitVec 64) (B : List UInt8) (c v : Nat) (d : Mem 64) : Prop :=
  match rdRows B (rw m0) (nr m0) c with
  | some (rows, c') => v = flag rows ∧
      LeavesAt d (lv m0) (rows.map fun x ↦ paddedLeaf x (lw m0)) ∧ ReaderAt d (rdr m0) bp B c'
  | none => v = 2

/-- What `rd_rows` reaches. -/
abbrev Post (m0 : MachineData) (st : MachineState) : Prop :=
  st.pc = retOf m0 ∧ rspOf st.data = rspOf m0 + 8#64 ∧ RdRowsPost m0 st.data

end

public section

theorem slots_le : ∀ p ∈ slots, p.1 + 8 ≤ 80 := by decide

theorem stack_eq : rdRowsStack = 128 := by decide

theorem flag_le (rows : List (List K)) : flag rows ≤ 1 := by
  unfold flag; split <;> omega

theorem lane_eq_zero {x : K} : x.lane = 0 ↔ x = 0 := by
  constructor
  · intro h
    have hx : x = K.ofLane x.lane := rfl
    rw [hx, h]
    rfl
  · intro h
    rw [h]
    exact lane_zero

/-- The flag after one more row. -/
theorem flag_snoc (rows : List (List K)) (x : List K) :
    flag (rows ++ [x]) = if x.getD 0 0 = 0 then flag rows else 0 := by
  have e : (∀ y ∈ rows ++ [x], y.getD 0 0 = 0) ↔ (∀ y ∈ rows, y.getD 0 0 = 0) ∧ x.getD 0 0 = 0 :=
    ⟨fun h ↦ ⟨fun y hy ↦ h y (List.mem_append_left _ hy), h x (List.mem_append_right _
      (List.mem_singleton_self x))⟩, fun ⟨h1, h2⟩ y hy ↦ by
      rcases List.mem_append.mp hy with hy | hy
      · exact h1 y hy
      · rw [List.mem_singleton.mp hy]; exact h2⟩
  unfold flag
  by_cases h : ∀ y ∈ rows, y.getD 0 0 = 0 <;> by_cases hx : x.getD 0 0 = 0
  · simp only [eq_true (e.mpr ⟨h, hx⟩), eq_true hx, eq_true h, ite_true]
  · simp only [eq_false fun h' ↦ hx (e.mp h').2, eq_false hx, ite_false]
  · simp only [eq_false fun h' ↦ h (e.mp h').1, eq_true hx, eq_false h, ite_true, ite_false]
  · simp only [eq_false fun h' ↦ hx (e.mp h').2, eq_false hx, ite_false]

/-- **A padded leaf more.** -/
theorem leaves_snoc {d : Mem 64} {a : BitVec 64} {L : List (List K)} {x : List K}
    (h : LeavesAt d a L) (hx : WordsAt d (off a (512 * L.length)) (x.map K.lane)) :
    LeavesAt d a (L ++ [x]) := by
  intro j hj
  simp only [List.length_append, List.length_singleton] at hj
  rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hj) with hj | rfl
  · rw [List.getElem_append_left hj]; exact h j hj
  · rw [List.getElem_append_right (le_refl _)]; simpa using hx

variable {m0 : MachineData} {bp : BitVec 64} {L : Nat}

theorem geo_of (hst : StackOk m0 rdRowsStack) (hn0 : 0 < nr m0) (hn : nr m0 ≤ 256)
    (hlw : lw m0 ≤ 64) (hrw : rw m0 ≤ lw m0)
    (hout : NativeRustcVm.Region.Ok m0.dmem ⟨lv m0, 512 * nr m0⟩) {B : List UInt8} {c : Nat}
    (hR : ReaderAt m0.dmem (rdr m0) bp B c)
    (hd : NativeRustcVm.Disjoint [stackR m0 rdRowsStack, ⟨rdr m0, 24⟩, ⟨bp, B.length⟩,
      ⟨lv m0, 512 * nr m0⟩]) : Geo m0 bp B.length := by
  rw [stack_eq] at hst
  simp only [NativeRustcVm.Disjoint, List.pairwise_cons, List.mem_cons, List.not_mem_nil,
    or_false, forall_eq_or_imp, forall_eq, stackR, stack_eq] at hd
  obtain ⟨⟨h1, h2, h3⟩, ⟨h4, h5⟩, h6, -⟩ := hd
  have hS := NativeRustcVmX64.noWrap_stackBelow hst
  have hoS : NativeRustcVm.Apart (lv m0) (512 * nr m0) (stackBelow m0 128) (128 + 8) := by
    unfold NativeRustcVm.Apart at h3 ⊢; omega
  have haR : NativeRustcVm.Apart (lv m0) (512 * nr m0) (rdr m0) 24 := by
    unfold NativeRustcVm.Apart at h5 ⊢; omega
  have haB : NativeRustcVm.Apart (lv m0) (512 * nr m0) bp B.length := by
    unfold NativeRustcVm.Apart at h6 ⊢; omega
  refine ⟨⟨hst, hR.ok.2, hR.noWrap, by unfold NativeRustcVm.Apart at h1 ⊢; omega,
    by unfold NativeRustcVm.Apart at h2 ⊢; omega, h4, fun q hq ↦ ?_, fun q hq ↦ ?_,
    fun q hq ↦ ?_⟩, hout.1, hout.2, hoS, haR, haB, hn0, hn, hlw, hrw⟩
  · exact hoS.not_inRange hout.2 hS hq
  · exact haR.not_inRange hout.2 hR.ok.2 hq
  · exact haB.not_inRange hout.2 hR.noWrap hq

/-! ## Numbers -/

theorem Geo.s0 (g : Geo m0 bp L) : 128 ≤ (rspOf m0).toNat ∧ (rspOf m0).toNat + 8 ≤ 2 ^ 64 ∧
    (stackBelow m0 128).toNat = (rspOf m0).toNat - 128 :=
  ⟨g.g.st.1, g.g.st.2.1, NativeRustcVmX64.stackBelow_toNat g.g.st.1⟩

theorem Geo.sb_toNat (g : Geo m0 bp L) : (sb m0).toNat = (rspOf m0).toNat - 80 :=
  NativeRustcVmX64.stackBelow_toNat (by have := g.g.st.1; omega)

/-- An address of the leaves, as a number. -/
theorem Geo.lv_off (g : Geo m0 bp L) {o : Nat} (ho : o < 512 * nr m0) :
    (off (lv m0) o).toNat = (lv m0).toNat + o :=
  NativeRustcVm.Transcript.toNat_off (by have := g.lvNw; omega)

/-- The leaves' bytes as numbers. -/
theorem Geo.W_iff (g : Geo m0 bp L) {q : BitVec 64} :
    W m0 q ↔ (lv m0).toNat ≤ q.toNat ∧ q.toNat < (lv m0).toNat + 512 * nr m0 :=
  NativeRustcVm.inRange_iff g.lvNw

theorem Geo.Stk_iff (g : Geo m0 bp L) {q : BitVec 64} :
    Stk m0 q ↔ (rspOf m0).toNat - 128 ≤ q.toNat ∧ q.toNat < (rspOf m0).toNat := by
  have := g.s0
  show NativeRustcVm.InRange _ _ q ↔ _
  rw [NativeRustcVm.inRange_iff (by unfold NativeRustcVm.NoWrap; omega)]
  omega

theorem Geo.Stk8_iff (g : Geo m0 bp L) {q : BitVec 64} :
    NativeRustcVm.InRange (stackBelow m0 128) (128 + 8) q ↔
      (rspOf m0).toNat - 128 ≤ q.toNat ∧ q.toNat < (rspOf m0).toNat + 8 := by
  have := g.s0
  rw [NativeRustcVm.inRange_iff (by unfold NativeRustcVm.NoWrap; omega)]
  omega

/-- The leaves are apart from the stack, as numbers. -/
theorem Geo.lvS (g : Geo m0 bp L) : (lv m0).toNat + 512 * nr m0 ≤ (rspOf m0).toNat - 128 ∨
    (rspOf m0).toNat + 8 ≤ (lv m0).toNat := by
  have ha := g.aS
  have := g.s0
  unfold NativeRustcVm.Apart at ha
  omega

/-- The reader is apart from the stack and the leaves, as numbers. -/
theorem Geo.rS (g : Geo m0 bp L) : (rdr m0).toNat + 24 ≤ (rspOf m0).toNat - 128 ∨
    (rspOf m0).toNat + 8 ≤ (rdr m0).toNat := by
  have ha := g.g.sr
  have := g.s0
  unfold NativeRustcVm.Apart at ha
  omega

theorem Geo.rW (g : Geo m0 bp L) : (lv m0).toNat + 512 * nr m0 ≤ (rdr m0).toNat ∨
    (rdr m0).toNat + 24 ≤ (lv m0).toNat := by
  have ha := g.aR
  unfold NativeRustcVm.Apart at ha
  omega

theorem Geo.rNw (g : Geo m0 bp L) : (rdr m0).toNat + 24 ≤ 2 ^ 64 := g.g.rNw

/-- The reader's cursor, as numbers. -/
theorem Geo.cur_iff (g : Geo m0 bp L) {q : BitVec 64} :
    NativeRustcVm.InRange (rdr m0 + BitVec.ofNat 64 16) 8 q ↔
      (rdr m0).toNat + 16 ≤ q.toNat ∧ q.toNat < (rdr m0).toNat + 24 := by
  have := g.rNw
  have ht : (rdr m0 + BitVec.ofNat 64 16).toNat = (rdr m0).toNat + 16 :=
    NativeRustcVm.toNat_add_ofNat (by omega)
  rw [NativeRustcVm.inRange_iff (by unfold NativeRustcVm.NoWrap; rw [ht]; omega), ht]

/-- An address of the frame, as a number. -/
theorem Geo.off_sb (g : Geo m0 bp L) {o : Nat} (ho : o < 88) :
    (off (sb m0) o).toNat = (rspOf m0).toNat - 80 + o := by
  have := g.s0
  rw [NativeRustcVm.Transcript.toNat_off (by rw [g.sb_toNat]; omega), g.sb_toNat]

/-- A byte of the leaves is no byte of the stack. -/
theorem Geo.W_not_Stk8 (g : Geo m0 bp L) {q : BitVec 64} (h : W m0 q) :
    ¬NativeRustcVm.InRange (stackBelow m0 128) (128 + 8) q := g.g.wS q h

theorem Geo.W_not_Stk (g : Geo m0 bp L) {q : BitVec 64} (h : W m0 q) : ¬Stk m0 q :=
  fun h' ↦ g.g.wS q h (inRange_mono h' (by omega))

/-! ## The memory -/

/-- The reader survives a change of the stack and the leaves. -/
theorem Geo.reader {B : List UInt8} {c : Nat} (g : Geo m0 bp B.length) {d d' : Mem 64}
    (hR : ReaderAt d (rdr m0) bp B c) {R : BitVec 64 → Prop}
    (hs : NativeRustcVm.SameOutside d d' R) (hR' : ∀ q, R q → Stk m0 q ∨ W m0 q) :
    ReaderAt d' (rdr m0) bp B c :=
  g.g.reader_frame rfl hR fun q hq ↦ hs q fun h ↦ hq ((hR' q h).imp_left fun h ↦
    inRange_mono h (by omega))

theorem chg_trans {d d' : Mem 64} (h : Chg m0 d) {R : BitVec 64 → Prop}
    (hs : NativeRustcVm.SameOutside d d' R)
    (hR : ∀ q, R q → Stk m0 q ∨ NativeRustcVm.InRange (rdr m0 + BitVec.ofNat 64 16) 8 q ∨
      W m0 q) : Chg m0 d' :=
  fun q hq ↦ (hs q fun h ↦ hq (hR q h)).trans (h q hq)

theorem Loc.keep (g : Geo m0 bp L) {d d' : Mem 64} (h : Loc m0 d) {R : BitVec 64 → Prop}
    (hs : NativeRustcVm.SameOutside d d' R)
    (hR : ∀ q, R q → ¬((rspOf m0).toNat - 72 ≤ q.toNat ∧ q.toNat < (rspOf m0).toNat - 56)) :
    Loc m0 d' := by
  have := g.s0
  refine ⟨h.lw.of_sameOutside hs fun j hj hq ↦ hR _ hq ?_,
    h.rd.of_sameOutside hs fun j hj hq ↦ hR _ hq ?_⟩
  · simp only [NativeRustcVm.length_wordBytes] at hj
    rw [off_add, g.off_sb (by omega)]; omega
  · simp only [NativeRustcVm.length_wordBytes] at hj
    rw [off_add, g.off_sb (by omega)]; omega

/-- A word of leaf `j`, as a number. -/
theorem Geo.leafByte (g : Geo m0 bp L) {j t : Nat} (hj : j < nr m0) (ht : t < 512) :
    (off (off (lv m0) (512 * j)) t).toNat = (lv m0).toNat + 512 * j + t := by
  have := g.lvNw
  rw [NativeRustcVm.Transcript.off_off, NativeRustcVm.Transcript.toNat_off (by omega)]
  omega

theorem rows_len {B : List UInt8} {w i c ci : Nat} {rows : List (List K)}
    (h : rdRows B w i c = some (rows, ci)) : rows.length = i ∧ ∀ x ∈ rows, x.length = w :=
  rdRows_length w i h

/-- The leaves so far survive a change apart from them. -/
theorem Geo.leaves_keep (g : Geo m0 bp L) {d d' : Mem 64} {rows : List (List K)} {i : Nat}
    (hi : i ≤ nr m0) (hl : rows.length = i) (hw : ∀ x ∈ rows, x.length ≤ lw m0)
    (h : LeavesAt d (lv m0) (rows.map fun x ↦ paddedLeaf x (lw m0))) {R : BitVec 64 → Prop}
    (hs : NativeRustcVm.SameOutside d d' R)
    (hR : ∀ q, R q → ¬((lv m0).toNat ≤ q.toNat ∧ q.toNat < (lv m0).toNat + 512 * i)) :
    LeavesAt d' (lv m0) (rows.map fun x ↦ paddedLeaf x (lw m0)) := by
  have := g.lw64
  intro j hj
  have hj' : j < i := by simpa [hl] using hj
  refine (h j hj).of_sameOutside hs fun t ht hq ↦ hR _ hq ?_
  have hlen : (rows[j]'(by simpa using hj)).length ≤ lw m0 := hw _ (List.getElem_mem _)
  simp only [List.getElem_map, List.length_flatMap, NativeRustcVm.length_wordBytes,
    List.map_const', List.sum_replicate, smul_eq_mul, List.length_map] at ht
  have h1 : (paddedLeaf rows[j] (lw m0)).length = lw m0 := by
    simp [paddedLeaf]; omega
  rw [h1] at ht
  rw [show off (lv m0) (512 * j) + BitVec.ofNat 64 t = off (off (lv m0) (512 * j)) t from rfl,
    g.leafByte (by omega) (by omega)]
  omega

/-- The bytes a step after `i` rows may change: the stack below the locals (the callee's) or
above them, the leaves from leaf `i`. -/
@[expose] def Mov (m0 : MachineData) (i : Nat) (q : BitVec 64) : Prop :=
  ((rspOf m0).toNat - 128 ≤ q.toNat ∧ q.toNat < (rspOf m0).toNat - 72) ∨
  ((rspOf m0).toNat - 56 ≤ q.toNat ∧ q.toNat < (rspOf m0).toNat) ∨
  ((lv m0).toNat + 512 * i ≤ q.toNat ∧ q.toNat < (lv m0).toNat + 512 * nr m0)

/-- **What survives a change** of the stack below the locals or above them, or of the leaves past
the first `i`. -/
theorem Kp.keep {B : List UInt8} {c i : Nat} {rows : List (List K)} {ci : Nat}
    (g : Geo m0 bp B.length) {d d' : Mem 64} (h : Kp m0 bp B c i rows ci d)
    (hi : i ≤ nr m0) {R : BitVec 64 → Prop} (hs : NativeRustcVm.SameOutside d d' R)
    (hR : ∀ q, R q → Mov m0 i q) : Kp m0 bp B c i rows ci d' := by
  have hlen := rows_len h.hrows
  have hS := g.lvS
  have := g.s0
  have hSt : ∀ q, Mov m0 i q → Stk m0 q ∨ W m0 q := fun q hq ↦ by
    rw [g.Stk_iff, g.W_iff]; unfold Mov at hq; omega
  refine ⟨h.hrows, g.reader h.hrd hs fun q hq ↦ hSt q (hR q hq),
    g.leaves_keep hi hlen.1 (fun x hx ↦ by rw [hlen.2 x hx]; exact g.rwlw) h.hlvs hs
      fun q hq ↦ ?_,
    h.hloc.keep g hs fun q hq ↦ ?_, chg_trans h.hchg hs fun q hq ↦ ?_⟩
  · have := hR q hq; unfold Mov at this; omega
  · have := hR q hq; unfold Mov at this; omega
  · rcases hSt q (hR q hq) with h1 | h1
    · exact .inl h1
    · exact .inr (.inr h1)

/-- **One row more**: after the read of row `i` (the cursor moved too) and its leaf written. -/
theorem Kp.succ {B : List UInt8} {c i : Nat} {rows : List (List K)} {ci : Nat}
    (g : Geo m0 bp B.length) {d d' : Mem 64} (h : Kp m0 bp B c i rows ci d)
    (hi : i < nr m0) {x : List K} {c' : Nat} (hw : rdWords B (rw m0) ci = some (x, c'))
    {R : BitVec 64 → Prop} (hs : NativeRustcVm.SameOutside d d' R)
    (hR : ∀ q, R q → Mov m0 i q ∨
      ((rdr m0).toNat + 16 ≤ q.toNat ∧ q.toNat < (rdr m0).toNat + 24))
    (hR' : ReaderAt d' (rdr m0) bp B c')
    (hleaf : WordsAt d' (off (lv m0) (512 * i)) ((paddedLeaf x (lw m0)).map K.lane)) :
    Kp m0 bp B c (i + 1) (rows ++ [x]) c' d' := by
  have hlen := rows_len h.hrows
  have hS := g.lvS
  have hrW := g.rW
  have hrS := g.rS
  have := g.s0
  refine ⟨by rw [rdRows_succ h.hrows, hw]; rfl, hR', ?_, h.hloc.keep g hs fun q hq ↦ ?_,
    chg_trans h.hchg hs fun q hq ↦ ?_⟩
  · rw [List.map_append, List.map_singleton]
    refine leaves_snoc (g.leaves_keep (le_of_lt hi) hlen.1
      (fun x hx ↦ by rw [hlen.2 x hx]; exact g.rwlw) h.hlvs hs fun q hq ↦ ?_) ?_
    · have := hR q hq; unfold Mov at this; omega
    · rw [List.length_map, hlen.1]; exact hleaf
  · have := hR q hq; unfold Mov at this; omega
  · rcases hR q hq with h1 | h1
    · rw [g.Stk_iff, g.W_iff]; unfold Mov at h1; omega
    · exact .inr (.inl ((g.cur_iff).mpr h1))

/-- Words of the leaves at `o` survive a change apart from them. -/
theorem Geo.words_keep (g : Geo m0 bp L) {d d' : Mem 64} {o : Nat} {ws : List UInt64}
    (hle : o + 8 * ws.length ≤ 512 * nr m0) (h : WordsAt d (off (lv m0) o) ws)
    {R : BitVec 64 → Prop} (hs : NativeRustcVm.SameOutside d d' R)
    (hR : ∀ q, R q → ¬((lv m0).toNat + o ≤ q.toNat ∧ q.toNat < (lv m0).toNat + o + 8 * ws.length)) :
    WordsAt d' (off (lv m0) o) ws := by
  have := g.lvNw
  refine NativeRustcVm.BytesAt.of_sameOutside h hs fun t ht hq ↦ hR _ hq ?_
  rw [NativeRustcVm.length_wordsBytes] at ht
  rw [off_add, NativeRustcVm.Transcript.toNat_off (by omega)]
  omega

/-- A zero word more. -/
theorem zeros_snoc {d : Mem 64} {a : BitVec 64} {t : Nat}
    (h : WordsAt d a (List.replicate t 0)) (hw : WordAt d (off a (8 * t)) 0) :
    WordsAt d a (List.replicate (t + 1) 0) := by
  rw [List.replicate_succ', NativeRustcVm.wordsAt_append_iff, List.length_replicate,
    NativeRustcVm.wordsAt_singleton_iff]
  exact ⟨h, hw⟩

/-- The postcondition, from the result. -/
theorem post_of {B : List UInt8} {c : Nat} (hR : ReaderAt m0.dmem (rdr m0) bp B c)
    {m : MachineData} (hres : Res m0 bp B c (boolRet m) m.dmem) (hchg : Chg m0 m.dmem)
    (hsv : Saved m0 m) : RdRowsPost m0 m := by
  refine ⟨fun bp' B' c' hR' ↦ ?_, fun q hq ↦ hchg q ?_, hsv⟩
  · obtain ⟨h1, h2, h3⟩ := hR.unique hR'
    rw [h1, h2, h3]
    unfold Res at hres
    revert hres
    cases rdRows B (rw m0) (nr m0) c with
    | none => exact id
    | some p =>
      obtain ⟨rows, c'⟩ := p
      rintro ⟨h1, h2, h3⟩
      refine ⟨?_, h2, h3⟩
      rw [h1]; rfl
  · rintro (h | h | h)
    · exact hq ⟨frameR m0 rdRowsStack, by simp, by
        rw [show frameR m0 rdRowsStack = ⟨stackBelow m0 128, 128⟩ by rw [stack_eq]; rfl]
        exact h⟩
    · exact hq ⟨curRegion (rdr m0), by simp, h⟩
    · exact hq ⟨_, List.mem_cons_self, h⟩

/-! ## Blocks -/

theorem fr_wf (g : Geo m0 bp L) {m : MachineData} {o : Nat} (hf : Frame m0 80 slots o m)
    {vars : Nat → BitVec 64} {ret : BitVec 64} : (frameEnv m0 m 80 [] vars ret).WF :=
  frame_wf ⟨Mapped.keeps (frame_mapped g.g.st (by decide)) hf.kept,
    frame_noWrap g.g.st (by decide)⟩ (by simp) (List.pairwise_singleton _ _)

theorem fr_match [Labels] {m : MachineData} (hf : Frame m0 80 slots 8 m)
    {vars : Nat → BitVec 64} {ret : BitVec 64} : Match (frameEnv m0 m 80 [] vars ret) frS m :=
  match_ofMachine ⟨rfl, trivial⟩ ⟨hf.rsp_eval, trivial⟩ trivial trivial trivial

/-- The registers `xs` a block keeps. -/
theorem keeps_of {S : SState} {xs : List Reg64} (h : Keeps xs S = true) :
    ∀ x ∈ xs, S.reg x = some (.reg x) := by
  intro x hx
  simp only [Keeps, List.all_eq_true, beq_iff_eq] at h
  exact h x hx

variable [Host] {k : Nat}

/-- **A block from `frS`** (at `j`) without writes: memory and the frame kept. -/
theorem fr_step (hp : Placed code k) (g : Geo m0 bp L) {bj : List Directive}
    {j : Nat} (hb : bj.IsInfixAt code j) (hne : bj ≠ []) {x : Exit}
    (hrun : exec bj frS = some (after bj frS, x)) (hx : ∀ l, x = .call l → False)
    (hok : FrOk (after bj frS) = true)
    {st : MachineState} (hpc : st.pc = Host.addrOf (k + j)) (hf : Frame m0 80 slots 8 st.data)
    {R : MachineState → Prop}
    (cont : ∀ st', Frame m0 80 slots 8 st'.data → st'.data.dmem = st.data.dmem →
      (∀ r v, (after bj frS).reg r = some v → reg st'.data r = v.eval (frameEnv m0 st.data 80 [])) →
      PcOk (frameEnv m0 st.data 80 []) x (Host.addrOf (k + j + bj.length)) st' →
      Eventually (step1 Host.exe) R st') :
    Eventually (step1 Host.exe) R st := by
  simp only [FrOk, Bool.and_eq_true, List.isEmpty_iff] at hok
  have hwf := fr_wf g hf (vars := fun _ ↦ 0) (ret := 0)
  have hm := fr_match hf (vars := fun _ ↦ 0) (ret := 0)
  exact exec_at (Wire.infix_of hb hne hp) hrun hwf (fun l h ↦ (hx l h).elim) hpc hm
    fun st' hm' hpc' ↦ cont st' (Frame.of_block hf hwf hm' hok.1 slots_le) (hm'.dmem_eq hwf hok.2)
      (fun r v h ↦ hm'.regs r v h) hpc'

/-- **A block with the frame and `sz` bytes of the leaves at `a`** (at `j`), its writes there: the
frame kept, memory changed only there. -/
theorem rg_step (hp : Placed code k) (g : Geo m0 bp L) {bj : List Directive} {j : Nat}
    (hb : bj.IsInfixAt code j) (hne : bj ≠ []) {y : Sym} {sz : Nat} {x : Exit}
    (hrun : exec bj (rgS y sz) = some (after bj (rgS y sz), x)) (hx : ∀ l, x = .call l → False)
    (hok : MidOk 80 8 slots (after bj (rgS y sz)) = true)
    (hw : ∀ w ∈ (after bj (rgS y sz)).mem, w.r = 1 ∧ 0 ≤ w.off ∧ w.off + w.n ≤ sz)
    {a : BitVec 64} {o : Nat} (hsz : 0 < sz) (hin : o + sz ≤ 512 * nr m0) (ha : a = off (lv m0) o)
    {st : MachineState} (hpc : st.pc = Host.addrOf (k + j)) (hf : Frame m0 80 slots 8 st.data)
    (hy : y.eval (frameEnv m0 st.data 80 [(a, sz)]) = a)
    {R : MachineState → Prop}
    (cont : ∀ st', Frame m0 80 slots 8 st'.data →
      NativeRustcVm.SameOutside st.data.dmem st'.data.dmem (NativeRustcVm.InRange a sz) →
      Match (frameEnv m0 st.data 80 [(a, sz)]) (after bj (rgS y sz)) st'.data →
      ((after bj (rgS y sz)).mem = [] → st'.data.dmem = st.data.dmem) →
      PcOk (frameEnv m0 st.data 80 [(a, sz)]) x (Host.addrOf (k + j + bj.length)) st' →
      Eventually (step1 Host.exe) R st') :
    Eventually (step1 Host.exe) R st := by
  have hlv := g.lvNw
  have hS := g.lvS
  have := g.s0
  have hsb := g.sb_toNat
  have hat : a.toNat = (lv m0).toNat + o := by
    rw [ha, NativeRustcVm.Transcript.toNat_off (by omega)]
  have hwf : (frameEnv m0 st.data 80 [(a, sz)]).WF := by
    refine frame_wf ⟨Mapped.keeps (frame_mapped g.g.st (by decide)) hf.kept,
      frame_noWrap g.g.st (by decide)⟩ (fun z hz ↦ ?_) (List.pairwise_pair.mpr ?_)
    · rw [List.mem_singleton] at hz
      subst hz
      refine ⟨fun t ht ↦ ?_, ?_⟩
      · rw [ha, off_add]
        exact hf.kept _ (g.lvMap _ (by dsimp only at ht; omega))
      · show _ + sz ≤ 2 ^ 64
        rw [hat]; omega
    · unfold NativeRustcVm.Apart
      dsimp only
      rw [hat, hsb]
      omega
  have hm : Match (frameEnv m0 st.data 80 [(a, sz)]) (rgS y sz) st.data :=
    match_ofMachine ⟨rfl, rfl, trivial⟩ ⟨hf.rsp_eval, trivial⟩ trivial trivial
      ⟨by
        show Sym.eval _ y = _ + BitVec.ofInt 64 0
        rw [hy, NativeRustcVmX64.Transcript.ofInt_zero64, BitVec.add_zero]
        rfl, trivial⟩
  exact exec_at (Wire.infix_of hb hne hp) hrun hwf (fun l h ↦ (hx l h).elim) hpc hm
    fun st' hm' hpc' ↦ cont st' (Frame.of_block hf hwf hm' hok slots_le)
      (NativeRustcVmX64.Transcript.sameOutside_region hwf hm' (r := 1) rfl hw) hm'
      (fun h ↦ hm'.dmem_eq hwf h) hpc'

/-- **The return** (`b2`, at `NativeRustcVmX64.Vm.RdRows.label_21`) with the result in BL. -/
theorem fin (hp : Placed code k) (g : Geo m0 bp L) {B : List UInt8} {c : Nat}
    (hR : ReaderAt m0.dmem (rdr m0) bp B c) {st : MachineState}
    (hpc : st.pc = Host.addrOf (k + NativeRustcVmX64.Vm.RdRows.b2Offset)) (hf : Frame m0 80 slots 8 st.data)
    (hres : Res m0 bp B c ((reg st.data .rbx).toNat % 256) st.data.dmem)
    (hchg : Chg m0 st.data.dmem) : Eventually (step1 Host.exe) (Post m0) st := by
  obtain ⟨hepi, hmem, hrax⟩ := ok_b2
  have hwf := fr_wf g hf (vars := fun _ ↦ 0) (ret := 0)
  have hm := fr_match hf (vars := fun _ ↦ 0) (ret := 0)
  refine exec_at (Wire.infix_of b2_in_code (by simp [b2]) hp) exit_b2 hwf nofun hpc hm
    fun st' hm' hpc' ↦ ?_
  obtain ⟨hsv, hrsp⟩ := Frame.epilogue hf hwf hm' hepi
  have hd : st'.data.dmem = st.data.dmem := hm'.dmem_eq hwf hmem
  have ha : reg st'.data .rax = UnOp.apply .trunc .W32 (reg st.data .rbx) := hm'.regs .rax _ hrax
  simp only [PcOk] at hpc'
  refine .done _ ⟨by rw [hpc']; exact hf.load_ret g.g.st (by decide), hrsp, post_of hR ?_
    (by rw [hd]; exact hchg) hsv⟩
  have hb : boolRet st'.data = (reg st.data .rbx).toNat % 256 := by
    unfold boolRet
    rw [ha]
    simp only [UnOp.apply, ext, low, BitVec.toNat_setWidth, Width.bits]
    omega
  rw [hb, hd]
  exact hres

end

end NativeRustcVmX64.Wire.RdRows
