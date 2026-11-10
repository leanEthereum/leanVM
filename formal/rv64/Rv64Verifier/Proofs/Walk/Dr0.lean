import Rv64Verifier.Proofs.Walk.AtDeref

/-!
# `walk`: `tables()`, the tools DEREF and JUMP need (R8)

Frame slots named by their distance `M` below the caller's `sp` (`s.getReg .x2 - M`), so that their
placement and disjointness are decided on numerals (`inSlot_off`, `apart_off`, `l4_off`, `fs_apart`);
the heap below a bound kept (`Keep`); an empty `Form` (`SF.empty`); forms in frame slots with fixed
buffer bounds (`SFh`); `self.add_scaled(other, ONE)` on a form in a frame slot (`ascM8`); a finished
table's `Flushes` as an `FB` (`M8.fb`).
-/

namespace Rv64Verifier.Proofs.Walk
open RiscvZkvm.Rv64 LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol.Compile
  Rv64Verifier.Runtime Rv64Verifier.Model Rv64Verifier.Transcript Rv64Verifier.Blocks.F4
open Rv64Verifier.Layout (FlushesOk flushesOf flushesDeep FormOk formOf formBuf)

/-! ## Frame slots by offset -/

theorem inSlot_off {s : MachineState} (hpre : WalkPre s) {M n : Nat}
    (h : M ≤ 2080 ∧ n + 104 ≤ M ∧ M % 8 = 0) : InSlot s (s.getReg .x2 - BitVec.ofNat 64 M) n := by
  obtain ⟨hb1, -, hb3, -⟩ := bounds hpre
  obtain ⟨h1, h2, h3⟩ := h
  simp only [InSlot]
  addr_omega [hb1, hb3, h1, h2, h3]

theorem apart_off {s : MachineState} (hpre : WalkPre s) {M M' n n' : Nat} (hM : M ≤ 2656)
    (hM' : M' ≤ 2656) (h : M' + n ≤ M ∨ M + n' ≤ M') :
    ∀ x, Within x (s.getReg .x2 - BitVec.ofNat 64 M) n →
      ¬ Within x (s.getReg .x2 - BitVec.ofNat 64 M') n' := by
  obtain ⟨hb1, -, -, -⟩ := bounds hpre
  intro x hx hw
  simp only [Within] at hx hw
  rcases h with h | h <;> addr_omega [hx, hw, hb1, hM, hM', h]

/-- A slot at or above `sp + 1240` misses the KECCAK, XOR, MUL and SET tables. -/
theorem l4_off {s : MachineState} (hpre : WalkPre s) {t : LayoutMirror.TableRust} {M n : Nat}
    (h : M ≤ 1416) : ∀ e ∈ L4 s t, ∀ a, Within a (s.getReg .x2 - BitVec.ofNat 64 M) n →
      ¬ Within a e.1 72 := by
  obtain ⟨hb1, -, -, -⟩ := bounds hpre
  intro e he a ha hw
  simp only [L4, L3, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil,
    or_false] at he
  rcases he with rfl | rfl | rfl | rfl <;> simp only [Within] at ha hw <;> addr_omega [ha, hw, hb1, h]

/-- A form's slot named by its offset. -/
def offW (s : MachineState) (e : Nat × LayoutMirror.FormRust) : Word × LayoutMirror.FormRust :=
  (s.getReg .x2 - BitVec.ofNat 64 e.1, e.2)

theorem fs_apart {s : MachineState} (hpre : WalkPre s) {Fs : List (Nat × LayoutMirror.FormRust)}
    {M n : Nat} (hM : M ≤ 2656) (h : ∀ e ∈ Fs, e.1 ≤ 2656 ∧ (M + 24 ≤ e.1 ∨ e.1 + n ≤ M)) :
    ∀ e ∈ Fs.map (offW s), ∀ x, Within x e.1 24 → ¬ Within x (s.getReg .x2 - BitVec.ofNat 64 M) n := by
  intro e he x hx
  obtain ⟨e', he', rfl⟩ := List.mem_map.mp he
  obtain ⟨h1, h2⟩ := h e' he'
  exact apart_off hpre h1 hM h2 x hx

theorem fs_slot {s : MachineState} (hpre : WalkPre s) {Fs : List (Nat × LayoutMirror.FormRust)}
    (h : ∀ e ∈ Fs, e.1 ≤ 2080 ∧ 128 ≤ e.1 ∧ e.1 % 8 = 0) : ∀ e ∈ Fs.map (offW s), InSlot s e.1 24 := by
  intro e he
  obtain ⟨e', he', rfl⟩ := List.mem_map.mp he
  exact inSlot_off hpre (h e' he')

theorem SFs.sub {s u : MachineState} {lo : Nat} {Fs Fs' : List (Word × LayoutMirror.FormRust)}
    (h : SFs s u lo Fs) (hs : ∀ e ∈ Fs', e ∈ Fs) : SFs s u lo Fs' :=
  ⟨fun e he ↦ h.sf e (hs e he), fun e he ↦ h.loc e (hs e he)⟩

/-! ## The heap below a bound kept -/

/-- No doubleword of the heap below `H` changed from `u` to `v`. -/
def Keep (u v : MachineState) (H : Nat) : Prop :=
  Rv64Verifier.Layout.DFrame u v fun x ↦ ¬ (heapStart ≤ x.toNat ∧ x.toNat < H)

theorem Keep.of {u v : MachineState} {H : Nat} {w : Word → Prop} (fr : Rv64Verifier.Layout.DFrame u v w)
    (hw : ∀ x, w x → heapStart ≤ x.toNat → H ≤ x.toNat) : Keep u v H :=
  fr.mono fun x hx hh ↦ by have := hw x hx hh.1; omega

theorem Keep.refl (u : MachineState) (H : Nat) : Keep u u H := fun _ _ _ ↦ rfl

theorem Keep.trans {u v t : MachineState} {H : Nat} (h₁ : Keep u v H) (h₂ : Keep v t H) : Keep u t H :=
  (Rv64Verifier.Layout.DFrame.union h₁ h₂).mono fun _ h ↦ h.elim id id

theorem Keep.mono {u v : MachineState} {H H' : Nat} (h : Keep u v H) (hH : H' ≤ H) : Keep u v H' :=
  Rv64Verifier.Layout.DFrame.mono h fun x hx hh ↦ hx ⟨hh.1, by omega⟩

theorem Keep.of_same {u v : MachineState} (H : Nat) (hm : ∀ a, v.getMem a = u.getMem a) : Keep u v H :=
  fun a _ _ ↦ hm a

/-- A form whose header was copied from `o` at `u` to `o'` at `v`, its buffer in the heap below
`hi` kept. -/
theorem SF.keep {u v : MachineState} {o o' : Word} {f : LayoutMirror.FormRust} {lo hi : Nat}
    (h : SF u o f lo hi) (k : Keep u v hi) (hlo : heapStart ≤ lo)
    (m0 : v.getMem o' = u.getMem o) (m8 : v.getMem (o' + 8) = u.getMem (o + 8))
    (m16 : v.getMem (o' + 16) = u.getMem (o + 16)) (hheap : HeapOk u)
    (mono : heapNext u ≤ heapNext v) : SF v o' f lo hi :=
  h.move k m0 m8 m16 (fun x h1 h2 hw ↦ hw ⟨by omega, h2⟩) hheap mono

/-- A callee writing a frame slot, its stack, `NEXT` and fresh heap keeps the heap below `heapNext`. -/
theorem Keep.cw {s u t : MachineState} (hpre : WalkPre s) (h : Inv s u) {o : Word} {n : Nat}
    (fr : Rv64Verifier.Layout.DFrame u t (CW u t o n)) (hn : n ≤ 8736)
    (ho : (s.getReg .x2 - 2080).toNat ≤ o.toNat) : Keep u t (heapNext u) := by
  obtain ⟨hb1, -, -, -⟩ := bounds hpre
  have hu := h.heap.hi
  simp only [heapEnd, heapNext] at hu
  refine Keep.of fr fun x hx hs ↦ ?_
  simp only [heapStart] at hs
  rcases hx with hx | hx | hx | hx
  · simp only [Within] at hx; addr_omega [hx, hb1, ho, hu]
  · rw [stackLo_callee h] at hx; simp only [Within] at hx; addr_omega [hx, hb1, hn, hu]
  · simp only [Within, nextAddr] at hx; simp only [heapNext]; addr_omega [hx, hu]
  · simp only [Fresh] at hx; omega

/-- A block writing only frame slots keeps the heap. -/
theorem Keep.slot {s u v : MachineState} (hpre : WalkPre s) {H : Nat} (hH : H ≤ heapEnd) {o : Word}
    {n : Nat} (fr : Rv64Verifier.Layout.DFrame u v fun x ↦ Within x o n)
    (ho : (s.getReg .x2 - 2080).toNat ≤ o.toNat ∧ o.toNat + n ≤ (s.getReg .x2 - 104).toNat) :
    Keep u v H := by
  obtain ⟨hb1, -, -, -⟩ := bounds hpre
  refine Keep.of (H := H) fr fun x hx _ ↦ ?_
  simp only [heapEnd] at hH
  simp only [Within] at hx
  addr_omega [hx, hb1, ho.1, ho.2, hH]

/-- The empty `Form` {0, 8, 0}. -/
theorem SF.empty {u : MachineState} {o : Word} (lo hi : Nat) (h0 : u.getMem o = 0)
    (h8 : u.getMem (o + 8) = 8) (h16 : u.getMem (o + 16) = 0) : SF u o {} lo hi := by
  have e0 : (0 : Word).toNat = 0 := rfl
  have e8 : (8 : Word).toNat = 8 := rfl
  refine ⟨⟨⟨?_, ?_⟩, fun i hi ↦ ?_⟩, ?_, fun x hx ↦ ?_⟩
  · simp only [RawVecOk, Buf, vecCap, vecPtr]; rw [h0, h8, e0, e8]; exact ⟨rfl, Or.inl rfl⟩
  · simp only [vecLen, vecCap, h0, h16]; exact le_refl _
  · simp only [vecLen, h16, e0] at hi; omega
  · simp only [formOf, vecLen, h16, e0]; rfl
  · simp only [formBuf, vecCap, h0, e0, Within] at hx; omega

/-- A one-term form's length. -/
theorem len_term {u : MachineState} {q : Word} {m : LayoutMirror.Monomial} {c : E}
    (h : formOf u q = LayoutMirror.FormRust.term m c) : (vecLen u q).toNat = 1 := by
  have := congrArg (fun f ↦ f.terms.length) h
  simpa [formOf, Rv64Verifier.Layout.termsOf_length, LayoutMirror.FormRust.term] using this

/-- Forms in frame slots, their buffers in `[lo, hi)`. -/
structure SFh (s u : MachineState) (lo hi : Nat) (Fs : List (Word × LayoutMirror.FormRust)) : Prop where
  sf : ∀ e ∈ Fs, SF u e.1 e.2 lo hi
  slot : ∀ e ∈ Fs, InSlot s e.1 24

theorem SFs.toH {s u : MachineState} {lo : Nat} {Fs : List (Word × LayoutMirror.FormRust)}
    (h : SFs s u lo Fs) (hs : ∀ e ∈ Fs, InSlot s e.1 24) : SFh s u lo (heapNext u) Fs :=
  ⟨h.sf, hs⟩

/-- A callee writing a frame slot `o`, a heap range apart from the forms' buffers, its stack, `NEXT`
and fresh heap keeps the forms. -/
theorem SFh.frame' {s u t : MachineState} {o : Word} {n lo hi lo' hi' : Nat}
    {Fs : List (Word × LayoutMirror.FormRust)} (hpre : WalkPre s) (h : Inv s u) (hf : SFh s u lo hi Fs)
    (fr : Rv64Verifier.Layout.DFrame u t fun a ↦ CW u t o n a ∨ (lo' ≤ a.toNat ∧ a.toNat < hi'))
    (hn : n ≤ 8736) (ho : InSlot s o 24) (hoo : ∀ e ∈ Fs, ∀ x, Within x e.1 24 → ¬ Within x o 24)
    (hA : hi ≤ lo' ∨ hi' ≤ lo) (hhi : hi ≤ heapNext u) (hhi' : hi' ≤ heapNext t) (hv : HeapOk t)
    (mono : heapNext u ≤ heapNext t) : SFh s t lo hi Fs := by
  obtain ⟨hb1, -, -, -⟩ := bounds hpre
  obtain ⟨o1, o2, -⟩ := ho
  have hu := h.heap.hi
  have ht := hv.hi
  simp only [heapEnd, heapNext] at hu ht mono hhi
  refine ⟨fun e he ↦ ?_, hf.slot⟩
  obtain ⟨e1, e2, -⟩ := hf.slot e he
  refine (hf.sf e he).frame fr (fun x hx hw ↦ ?_) (fun x hx1 hx2 hw ↦ ?_) (by addr_omega [hb1, e2]) h.heap
    (by simp only [heapNext]; omega)
  · simp only [Within] at hx
    rcases hw with (hw | hw | hw | hw) | hw
    · exact hoo e he x (by simp only [Within]; exact hx) hw
    · rw [stackLo_callee h] at hw; simp only [Within] at hw; addr_omega [hx, hw, hb1, hn, e1, e2]
    · simp only [Within] at hw; addr_omega [hx, hw, hb1, e1, e2]
    · simp only [Fresh, heapNext] at hw; addr_omega [hx, hw, hb1, e1, e2, ht]
    · simp only [heapNext] at hhi'; addr_omega [hx, hw, hb1, e1, e2, hu, ht, mono, hhi']
  · rcases hw with (hw | hw | hw | hw) | hw
    · simp only [Within] at hw; addr_omega [hw, hb1, o1, o2, hx2, hhi, hu]
    · rw [stackLo_callee h] at hw; simp only [Within] at hw; addr_omega [hw, hb1, hn, hx2, hhi, hu]
    · simp only [Within] at hw; addr_omega [hw, hx2, hhi, hu]
    · simp only [Fresh, heapNext] at hw; omega
    · omega

/-- A block writing a frame slot apart from the forms' headers keeps them. -/
theorem SFh.slot' {s u v : MachineState} {o : Word} {n lo hi : Nat}
    {Fs : List (Word × LayoutMirror.FormRust)} (hpre : WalkPre s) (hf : SFh s u lo hi Fs)
    (fr : Rv64Verifier.Layout.DFrame u v fun a ↦ Within a o n) (ho : InSlot s o n)
    (hoo : ∀ e ∈ Fs, ∀ x, Within x e.1 24 → ¬ Within x o n) (hheap : HeapOk u)
    (hhi : hi ≤ heapNext u) (mono : heapNext u ≤ heapNext v) : SFh s v lo hi Fs := by
  obtain ⟨hb1, -, -, -⟩ := bounds hpre
  obtain ⟨o1, o2, -⟩ := ho
  have hu := hheap.hi
  simp only [heapEnd] at hu
  refine ⟨fun e he ↦ ?_, hf.slot⟩
  obtain ⟨e1, e2, -⟩ := hf.slot e he
  exact (hf.sf e he).frame fr (fun x hx hw ↦ hoo e he x hx hw)
    (fun x _ hx2 hw ↦ by simp only [Within] at hw; addr_omega [hw, hb1, o1, o2, hx2, hhi, hu])
    (by addr_omega [hb1, e2]) hheap mono

/-- A finished table's `Flushes`, as the `Flushes` `colSlot` and `prodSlot` keep. -/
theorem M8.fb {OI : MachineState → Word → List (List Opening) → Prop} {s u : MachineState}
    {A : List E} {k : Nat} {R Q : Word} {B : Nat} {Bb : Word} {W : Nat}
    {L : List (Word × LayoutMirror.TableRust)} (h : M8 OI s u A k R Q B Bb W L) {e : Word × LayoutMirror.TableRust}
    (he : e ∈ L) : FB u (e.1 + 24) e.2.flushes B := by
  obtain ⟨-, T, hd⟩ := h.tabs e he
  exact ⟨T.ok, T.flushes, fun x hx ↦ (hd x (Or.inr hx)).1⟩

set_option maxRecDepth 8192 in
/-- `self.add_scaled(other, ONE)`: `self` the form at the frame slot `o`, `other` the one-term
form at the slot `q`, allocated before `self`'s buffer. -/
theorem ascM8 (hA : Rv64Verifier.Layout.AddScaledSpec)
    {OI : MachineState → Word → List (List Opening) → Prop} {s u : MachineState}
    {A : List E} {k : Nat} {R Q : Word} {B : Nat} {Bb : Word} {W : Nat}
    {L : List (Word × LayoutMirror.TableRust)} {o q : Word} {f g : LayoutMirror.FormRust}
    {lo hi lo' hi' : Nat} (hpre : WalkPre s) (h : M8 OI s u A k R Q B Bb W L)
    (hpc : u.pc = 0x800119cc) (x10 : u.getReg .x10 = o) (ho : InSlot s o 24)
    (hL : ∀ e ∈ L, ∀ a, Within a o 24 → ¬ Within a e.1 72) (hf : SF u o f lo hi)
    (hg : SF u q g lo' hi') (hlen : (vecLen u q).toNat = 1) (hhi : hi' ≤ lo)
    (hhiN : hi ≤ heapNext u) (hloN : lo ≤ heapNext u) (hWl : W ≤ lo)
    (x11 : u.getReg .x11 = vecPtr u q) (x12 : u.getReg .x12 = vecLen u q)
    (x13 : u.getReg .x13 = 0xa00000b0) :
    ∃ t, Reaches Image.code u t ∧ ((t.pc = returnAddress u ∧ Preserves u t ∧
      M8 OI s t A k R Q B Bb W L ∧ SF t o (f.add g) lo (heapNext t) ∧ heapNext u ≤ heapNext t ∧
      Rv64Verifier.Layout.DFrame u t (fun a ↦ CW u t o Rv64Verifier.Layout.addScaledStack a ∨
        (lo ≤ a.toNat ∧ a.toNat < hi))) ∨ Dead Image.code t) := by
  obtain ⟨hb1, -, hb3, -⟩ := bounds hpre
  have hn : Rv64Verifier.Layout.addScaledStack ≤ 8736 := by decide
  have I := h.m.inv
  have hu := I.heap.hi
  have hu' := I.heap.lo
  simp only [heapEnd, heapStart, heapNext] at hu hu' hhiN hloN
  have hS := slotOk hpre h ho hL
  have sO := slotW (n := 3) hpre I (o := o) (by simpa [InSlot] using ho) hn
  obtain ⟨o1, o2, o3⟩ := ho
  have qraw := hg.ok.vec.raw
  have qlen := hg.ok.vec.len
  simp only [RawVecOk, Buf] at qraw
  rw [hlen] at qlen
  have qbuf : heapStart ≤ (vecPtr u q).toNat ∧ (vecPtr u q).toNat + 48 ≤ heapNext u := by
    rcases qraw.2 with h0 | h0
    · rw [Nat.mul_eq_zero] at h0; omega
    · constructor
      · exact h0.1
      · have := h0.2; nlinarith
  simp only [heapStart, heapNext] at qbuf
  have q47 : (vecPtr u q).toNat + 48 ≤ hi' := by
    have hx : formBuf u q (vecPtr u q + 47) := by
      simp only [formBuf, Within]; addr_omega [qbuf, qlen, hu]
    have := (hg.buf _ hx).2
    addr_omega [this, qbuf, hu]
  have fbuf (x : Word) (hx : formBuf u o x) : lo ≤ x.toNat ∧ x.toNat < hi := hf.buf x hx
  have hab := hpre.stack.above
  rw [stackLo_eq] at hab
  simp only [heapEnd] at hab
  have pre : Rv64Verifier.Layout.AddScaledPre u := {
    heap := I.heap
    stack := stk_sub hpre I hn (by decide)
    self := by rw [x10]; exact sO.1
    ok := by rw [x10]; exact hf.ok
    other := by
      rw [x11, x12, hlen]
      exact Rv64Verifier.Layout.validMemRange_of qraw.1 (Or.inl ⟨by omega, by omega⟩)
    otherTags := by rw [x11, x12]; exact hg.ok.tags
    weight := by rw [x13]; exact Rv64Verifier.Layout.validMemRange_of (by decide) (Or.inr ⟨by decide, by decide⟩)
    rodata := I.rodata hpre
    selfFree := by rw [x10]; exact sO.2.1
    otherFree := by rw [x11, x12, hlen]; exact ⟨Or.inl (by simp only [heapNext]; omega), by addr_omega [qbuf, hu]⟩
    weightFree := by rw [x13]; exact ⟨Or.inr (by decide), by addr_omega []⟩
    selfStack := by rw [x10]; exact sO.2.2
    otherStack := by rw [x11, x12, hlen, stackLo_callee I]; addr_omega [qbuf, hb1, hab, hu]
    weightStack := by rw [x13, stackLo_callee I]; addr_omega [hb1]
    selfOther := by rw [x10, x11, x12, hlen]; addr_omega [qbuf, hb1, o1, hu]
    selfWeight := by rw [x10, x13]; addr_omega [hb1, o1, o2]
    selfRodata := by rw [x10]; addr_omega [hb1, o1, o2]
    buf := fun x hx hw ↦ by
      rw [x10] at hx
      have := fbuf x hx
      rw [x10, x11, x12, hlen, x13] at hw
      rcases hw with hw | hw | hw
      · simp only [Within] at hw; addr_omega [hw, this, hb1, o1, hhiN, hu]
      · simp only [Within] at hw; omega
      · simp only [Within] at hw; addr_omega [hw, this, hb1, hhiN, hu] }
  obtain ⟨t, hr, ⟨hpct, hp, post⟩ | hdd⟩ := hA u hpc pre
  swap
  · exact ⟨t, hr, Or.inr hdd⟩
  have fr := post.frame
  rw [x10] at fr
  have fr' : Rv64Verifier.Layout.DFrame u t (fun a ↦ CW u t o Rv64Verifier.Layout.addScaledStack a ∨
      (lo ≤ a.toNat ∧ a.toNat < hi)) := fr.mono fun a ha ↦ by
    rcases ha with ha | ha | ha | ha | ha
    · exact Or.inl (Or.inl ha)
    · exact Or.inr (fbuf a ha)
    · exact Or.inl (Or.inr (Or.inl ha))
    · exact Or.inl (Or.inr (Or.inr (Or.inl ha)))
    · exact Or.inl (Or.inr (Or.inr (Or.inr ha)))
  have hb := h.bb
  have hW := h.bb.2.2.2
  have hBu := h.m.bufQ.2.2.2
  have hBW : B ≤ W := by omega
  simp only [heapNext] at hW hBu
  have ht := post.heap.hi
  have mo := post.mono
  simp only [heapEnd, heapNext] at ht mo
  have M := h.step hpre fr' (fun a ha ↦ ?_) (fun a ha ↦ ?_) post.heap post.mono (hp.reg .x2)
  · refine ⟨t, hr, Or.inl ⟨hpct, hp, M, ⟨?_, ?_, fun x hx ↦ ?_⟩, post.mono, fr'⟩⟩
    · rw [← x10]; exact post.ok
    · rw [← x10, post.value, x10, hf.val, x11, x12, x13, Rv64Verifier.Layout.eAt_one (I.rodata hpre),
        ← hg.val]
      rfl
    · rw [← x10] at hx
      rcases post.buf x hx with hx | hx
      · rw [x10] at hx; have := fbuf x hx; simp only [heapNext]; omega
      · simp only [Fresh, heapNext] at hx ⊢; omega
  · rcases ha with (ha | ha | ha | ha) | ha
    · exact (hS a ha).1.mono post.mono
    · exact Or.inr (Or.inr (Or.inr (Or.inl (stackLo_w6 hpre I hn ha))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ha))))
    · simp only [Fresh, heapNext] at ha
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨by omega, by simp only [heapNext]; omega⟩))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨by omega, by simp only [heapNext]; omega⟩))))
  · rcases ha with (ha | ha | ha | ha) | ha
    · exact (hS a ha).2
    · simp only [M8W]
      rw [stackLo_callee I] at ha
      refine ⟨?_, ?_, ?_, ?_, fun e he hw ↦ ?_⟩ <;> simp only [Within] at ha ⊢
      all_goals first
        | addr_omega [ha, hb1, hn, hu, hW]
        | (obtain ⟨e1, e2, -⟩ := (h.tabs e he).1; simp only [Within] at hw; addr_omega [ha, hb1, hn, e1, hw])
    · simp only [M8W]
      refine ⟨?_, ?_, ?_, ?_, fun e he hw ↦ ?_⟩ <;> simp only [Within] at ha ⊢
      all_goals first
        | addr_omega [ha, hb1, hu, hW]
        | (obtain ⟨e1, e2, -⟩ := (h.tabs e he).1; simp only [Within] at hw; addr_omega [ha, hb1, e1, hw])
    · simp only [M8W]
      simp only [Fresh, heapNext] at ha
      refine ⟨by omega, ?_, ?_, ?_, fun e he hw ↦ ?_⟩
      all_goals first
        | addr_omega [ha, hb1, ht, hW]
        | (obtain ⟨e1, e2, -⟩ := (h.tabs e he).1; simp only [Within] at hw; addr_omega [ha, hb1, e1, hw, ht])
    · simp only [M8W]
      refine ⟨by omega, ?_, ?_, ?_, fun e he hw ↦ ?_⟩
      all_goals first
        | (simp only [Within]; addr_omega [ha, hb1, hhiN, hu])
        | (obtain ⟨e1, e2, -⟩ := (h.tabs e he).1; simp only [Within] at hw; addr_omega [ha, hb1, e1, hw, hhiN, hu])

end Rv64Verifier.Proofs.Walk
