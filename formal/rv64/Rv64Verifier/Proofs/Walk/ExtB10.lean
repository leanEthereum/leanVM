import Rv64Verifier.Proofs.Walk.ExtS10
import Rv64Verifier.Proofs.Walk.Loop10

/-!
# `walk`: `ExtendBlocksSpec` from the proved `extend_trusted`

`extendBlocks_pre` gives `Layout.ExtendPre` (the coordinates being nonempty, their buffers are
allocated); `extendBlocks_post` reads `Layout.ExtendPost` and `NewSep` as `ExtendBlocksPost`: the
old blocks moved with the buffer (`blocksAt_moved`), the new ones appended. `r10c` is `r10` with
every callee's contract discharged.
-/

namespace Rv64Verifier.Proofs.Walk
open RiscvZkvm.Rv64 LeanVM.Parameters LeanVM.Protocol.Compile Rv64Verifier.Runtime
  Rv64Verifier.Model Rv64Verifier.Transcript Rv64Verifier.Model.LayoutMirror

theorem blocksAt_add (u : MachineState) (p : Word) (n m : Nat) :
    blocksAt u p (n + m) = blocksAt u p n ++
      (List.range m).map fun i ↦ blockOf u (p + BitVec.ofNat 64 (48 * (n + i))) := by
  simp only [blocksAt, List.range_add, List.map_append, List.map_map]
  rfl

theorem ExtRO.kept {s : MachineState} {a : Word} {n : Nat} (h : ExtRO s a n) {x : Word}
    (hx : Within x a n) : (x.toNat < heapNext s ∨ heapEnd ≤ x.toNat) ∧ ¬ Within x nextAddr 8 ∧
      ¬ Within x (stackLo s Layout.extendStack) Layout.extendStack ∧ ¬ Layout.ExtSelf s x := by
  have hn : n ≠ 0 := by simp only [Within] at hx; omega
  obtain ⟨h1, h2⟩ := h.free.resolve_left hn
  have h3 := h.stack
  refine ⟨?_, fun hw ↦ ?_, fun hw ↦ ?_, h.self x hx⟩
  · simp only [Within] at hx; omega
  · simp only [Within, Apart] at hx hw h2; omega
  · simp only [Within, Apart, extendBlocksStack, Layout.extendStack] at hx hw h3; omega

theorem extendBlocks_pre {s : MachineState} (h : ExtendBlocksPre s) : Layout.ExtendPre s where
  heap := h.heap
  stack := h.stack
  self := h.self
  vec := BlocksSound.vecOk h.ok
  selfFree := h.selfFree
  selfStack := h.selfStack
  selfBuf := Layout.Extend.apart_of fun x hx hb ↦ h.header x hx (Or.inl hb)
  iter := h.env.valid
  bounds := h.whole.1
  whole := h.whole.2
  src := by
    have := h.src.valid
    rwa [show (24 * itLen s + 7) / 8 = 3 * itLen s by omega] at this
  elems := h.srcOk
  elemsPtr := fun i hi ↦ Or.inl (by
    have hv := Layout.vecBuf_bounds (h.srcOk i hi).vec (by decide)
    have hl := (h.srcOk i hi).vec.len
    have hne := h.srcNe i hi
    show (vecPtr s (itBegin s + BitVec.ofNat 64 (24 * i))).toNat ≤ heapNext s
    rcases hv.2 with h0 | h0 <;> omega)
  height := h.height.valid
  rows := h.rows.valid
  owner := h.table.valid
  kept := fun x hx ↦ by
    rcases hx with hx | hx | ⟨i, hi, hx⟩ | hx | hx | hx
    · exact h.env.kept hx
    · exact h.src.kept hx
    · have dd := (h.srcOk i hi).deep_below hx
      have hh := h.heap.hi
      have ha := h.stack.above
      simp only [heapEnd, heapStart] at dd hh ha
      refine ⟨Or.inl dd.2, fun hw ↦ ?_, fun hw ↦ ?_, h.srcDeep i hi x hx⟩
      · simp only [Within, nextAddr] at hw; addr_omega [hw, dd, hh]
      · simp only [Within] at hw; addr_omega [hw, dd, hh, ha]
    · exact h.height.kept hx
    · exact h.rows.kept hx
    · exact h.table.kept hx

theorem extendBlocks_post {s t : MachineState} (h : ExtendBlocksPre s) (hp : Layout.ExtendPost s t)
    (hs : Layout.Extend.NewSep s t) : ExtendBlocksPost s t := by
  have hok : BlocksSound s (vecPtr s (s.getReg .x10)) (vecCap s (s.getReg .x10)).toNat
      (vecLen s (s.getReg .x10)).toNat := h.ok
  have hle := hp.vec.len
  have hlen := hp.len
  have hK : Layout.itLen s = itLen s := rfl
  rw [hK] at hlen
  have hhi := h.heap.hi
  have hab := h.stack.above
  have hbd := BlocksSound.bounds hok
  simp only [heapEnd, heapStart] at hhi hab hbd
  have hmono := hp.mono
  -- the old blocks' coordinates: below `NEXT`, missing what the call writes
  have hdb : ∀ x, blocksDeep s (vecPtr s (s.getReg .x10)) (vecLen s (s.getReg .x10)).toNat x →
      0x20000000 ≤ x.toNat ∧ x.toNat < heapNext s := fun x hx ↦ by
    have := hok.deep_below hx; simp only [heapStart] at this; exact this
  have hsep : ∀ x, blocksDeep s (vecPtr s (s.getReg .x10)) (vecLen s (s.getReg .x10)).toNat x →
      ¬ Within x (vecPtr t (s.getReg .x10)) (48 * (vecCap t (s.getReg .x10)).toNat) :=
    fun x hx hw ↦ by
      rcases hp.buf with ⟨e1, e2⟩ | hnb
      · rw [e1, e2] at hw; exact hok.sep x hx hw
      · have := hdb x hx
        simp only [NewBuf, Within] at hnb hw
        rcases hnb.2 with h0 | h0 <;> omega
  have mv := blocksAt_moved hp.frame (p' := vecPtr t (s.getReg .x10))
    (c' := (vecCap t (s.getReg .x10)).toNat) hok hp.old hp.vec.raw (by omega)
    (fun x hx hw ↦ by
      have hd := hdb x hx
      rcases hw with (hw | hw) | hw | hw | hw
      · exact h.header x hw (Or.inr hx)
      · exact hok.sep x hx hw
      · simp only [Within, stackLo, Layout.extendStack] at hw; addr_omega [hw, hd, hhi, hab]
      · simp only [Within, nextAddr] at hw; addr_omega [hw, hd, hhi]
      · simp only [Fresh] at hw; omega)
    hsep h.heap hmono
  -- the new blocks
  have hnew (i : Nat) (hi : i < itLen s) :=
    hp.new i hi
  have hblk (i : Nat) (hi : i < itLen s) :
      blockOf t (vecPtr t (s.getReg .x10) +
        BitVec.ofNat 64 (48 * ((vecLen s (s.getReg .x10)).toNat + i))) =
        ⟨(s.getMem (itHeight s)).toNat, s.getMem (itRows s),
          Layout.formVecOf s (itBegin s + BitVec.ofNat 64 (24 * i)), (s.getMem (itTable s + 72)).toNat⟩ := by
    have nb := hnew i hi
    simp only [blockOf, nb.logRows, nb.rows, nb.owner, nb.value]
    rfl
  have hfoot : ∀ x, blocksDeep t (vecPtr t (s.getReg .x10)) (vecLen t (s.getReg .x10)).toNat x →
      blocksDeep s (vecPtr s (s.getReg .x10)) (vecLen s (s.getReg .x10)).toNat x ∨
        (∃ i < itLen s, Layout.formVecDeep t (vecPtr t (s.getReg .x10) +
          BitVec.ofNat 64 (48 * ((vecLen s (s.getReg .x10)).toNat + i))) x) := by
    rintro x ⟨j, hj, hx⟩
    by_cases hjn : j < (vecLen s (s.getReg .x10)).toNat
    · exact Or.inl (by rw [← mv.2.2]; exact ⟨j, hjn, hx⟩)
    · refine Or.inr ⟨j - (vecLen s (s.getReg .x10)).toNat, by omega, ?_⟩
      rwa [show (vecLen s (s.getReg .x10)).toNat + (j - (vecLen s (s.getReg .x10)).toNat) = j by omega]
  refine {
    heap := hp.heap
    mono := hmono
    value := ?_
    ok := ⟨hp.vec.raw, hle, fun j hj ↦ ?_, fun x hx hw ↦ ?_⟩
    foot := fun x hx ↦ ?_
    frame := hp.frame }
  · simp only [blocksOf]
    rw [hlen, blocksAt_add, mv.1, List.map_map]
    congr 1
    exact List.map_congr_left fun i hm ↦ hblk i (List.mem_range.mp hm)
  · by_cases hjn : j < (vecLen s (s.getReg .x10)).toNat
    · exact mv.2.1.elems j hjn
    · have := (hnew (j - (vecLen s (s.getReg .x10)).toNat) (by omega)).ok
      rwa [show (vecLen s (s.getReg .x10)).toNat + (j - (vecLen s (s.getReg .x10)).toNat) = j by
        omega] at this
  · rcases hfoot x hx with hx | ⟨i, hi, hx⟩
    · exact hsep x hx hw
    · exact hs i hi x hx hw
  · rcases hx with hx | hx
    · rcases hp.buf with ⟨e1, e2⟩ | hnb
      · rw [e1, e2] at hx; exact Or.inl (Or.inl hx)
      · right
        simp only [NewBuf, Within] at hnb hx
        simp only [Fresh]
        rcases hnb.2 with h0 | h0 <;> omega
    · rcases hfoot x hx with hx | ⟨i, hi, hx⟩
      · exact Or.inl (Or.inr hx)
      · exact Or.inr ((hnew i hi).fresh x hx)

/-- `ExtendBlocksSpec`, proved. -/
theorem extendBlocks_proved : ExtendBlocksSpec := fun s hpc hp ↦
  (Layout.Extend.extend_trusted_sep s hpc (extendBlocks_pre hp)).imp fun _ ⟨hr, ht⟩ ↦
    ⟨hr, ht.imp_left fun ⟨a, b, c, d⟩ ↦ ⟨a, b, extendBlocks_post hp c d⟩⟩

/-- R10, from `AtR10` to `AtR11`, every callee's contract proved. -/
theorem r10c {OI : MachineState → Word → List (List Opening) → Prop} {s u : MachineState}
    {A : List E} {k : Nat} {R Q B : Word} (hpre : WalkPre s) (h : AtR10 OI s u A k R Q B) :
    ∃ t, Reaches Image.code u t ∧ (Dead Image.code t ∨
      (t.pc = 0x80003038 ∧ AtR11 OI s t A k R Q B (heapNext u))) :=
  r10 extendBlocks_proved Runtime.reserveFresh_800060bc Runtime.alloc_spec Layout.col_proved
    Layout.clone_proved hpre h

end Rv64Verifier.Proofs.Walk
