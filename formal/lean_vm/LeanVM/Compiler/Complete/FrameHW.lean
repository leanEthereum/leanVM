/-
  LeanVM.Compiler.Complete.FrameHW

  From the words of a frame's cells to `PathWords`' instruction facts: each straight-line
  instruction holds (`HW`) and each jump reads its words (`JW`) on every memory holding the words.
-/

module

public import LeanVM.Compiler.Complete.PathRun

/-!
# Straight-line instructions on frame words

`PathWords` asks, of each straight-line instruction on the path, that it holds on every memory the
frame words describe (`HW`), and of each jump that its cells read their words there (`JW`). Here
both follow from facts about words: `Rds Ag fp size w` says every memory `Ag` admits reads `w n` at
cell `n` of the frame `fp` below `size`; then a `SET` holds when its cell's word is the immediate's,
an `XOR`/`MUL` when its words add or multiply, a `DEREF` when the memory reads the word at the
address its pointer word gives (a load, a callee frame cell, a jump table slot), a copy into the
next frame when the memory holds the product there, a `KECCAK` when its words are related; the
calls' segments when the callee frames hold their cells. The frame side's per-instruction relation
`OpW` gives them for the walk's instance (`FrameOp.lean`, `opOK_instOf`).
-/

namespace LeanVM.Compiler.Complete

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Memory

@[expose] public section

/-- Every memory `Ag` admits reads the word `w n` at cell `n` of frame `fp`, below `size`. -/
def Rds (Ag : (κ : ℕ) → MemoryImage κ → Prop) (fp size : ℕ) (w : ℕ → E) : Prop :=
  ∀ (κ : ℕ) (L : MemoryImage κ), Ag κ L → ∀ n, n < size → L.read (addressOfIndex (fp + n)) = some (w n)

section Bridge

variable {κ₀ : ℕ} {Γ : Site κ₀} {Ag : (κ : ℕ) → MemoryImage κ → Prop} {fp size : ℕ} {w : ℕ → E}

theorem Rds.read (h : Rds Ag fp size w) {κ : ℕ} {L : MemoryImage κ} (hA : Ag κ L) {n : ℕ}
    (hn : n < size) : L.read (addressOfIndex fp * addressOfIndex n) = some (w n) := by
  rw [idx_mul]
  exact h κ L hA n hn

/-- **A `SET`**: its cell's word is the immediate's. -/
theorem set_hw (h : Rds Ag fp size w) {pc o : ℕ} {k : KVal} (ho : o < size)
    (hk : w o = OffsetInstruction.immediateWord (resolveK Γ.l Γ.pc0 Γ.frame k).1
      (resolveK Γ.l Γ.pc0 Γ.frame k).2) : HW Γ fp Ag pc (.set o k) := by
  intro κ L hA
  simp only [Site.R, resolveOp]
  rcases e : resolveK Γ.l Γ.pc0 Γ.frame k with ⟨c0, c1⟩
  rw [e] at hk
  simp only [Holds]
  rw [h.read hA ho, hk]

/-- **An `XOR`**: its words add. -/
theorem xor_hw (h : Rds Ag fp size w) {pc a b c : ℕ} (ha : a < size) (hb : b < size)
    (hc : c < size) (hw : w c = w a + w b) : HW Γ fp Ag pc (.xor a b c) := by
  intro κ L hA
  exact ⟨w a, w b, h.read hA ha, h.read hA hb, by rw [h.read hA hc, hw]⟩

/-- **A `MUL`**: its words multiply. -/
theorem mul_hw (h : Rds Ag fp size w) {pc a b c : ℕ} (ha : a < size) (hb : b < size)
    (hc : c < size) (hw : w c = w a * w b) : HW Γ fp Ag pc (.mul a b c) := by
  intro κ L hA
  exact ⟨w a, w b, h.read hA ha, h.read hA hb, by rw [h.read hA hc, hw]⟩

/-- **A `DEREF`**: the memory holds, at the address its pointer word gives, what the mode
stores. -/
theorem deref_hw (h : Rds Ag fp size w) {pc p off d : ℕ} {mode : DerefMode} (hp : p < size)
    (hd : d < size) (hK : IsInK (w p))
    (hr : ∀ (κ : ℕ) (L : MemoryImage κ), Ag κ L → L.read ((w p).limb 0 * addressOfIndex off) =
      some (derefSource mode ⟨addressOfIndex pc, addressOfIndex fp⟩ (w d))) :
    HW Γ fp Ag pc (.deref p off d mode) := by
  intro κ L hA
  exact ⟨w p, w d, h.read hA hp, hK, h.read hA hd, hr κ L hA⟩

/-- **A `DEREF` into a frame `kfp`** (a callee's): the memory holds what the mode stores at its
cell `off`. -/
theorem derefAt_hw (h : Rds Ag fp size w) {pc p off d kfp : ℕ} {mode : DerefMode} (hp : p < size)
    (hd : d < size) (hpw : w p = ofK (addressOfIndex kfp))
    (hr : ∀ (κ : ℕ) (L : MemoryImage κ), Ag κ L → L.read (addressOfIndex (kfp + off)) =
      some (derefSource mode ⟨addressOfIndex pc, addressOfIndex fp⟩ (w d))) :
    HW Γ fp Ag pc (.deref p off d mode) := by
  refine deref_hw h hp hd (by rw [hpw]; exact (isInK_iff _).mpr ⟨_, rfl⟩) fun κ L hA => ?_
  rw [hpw, limb_ofK, idx_mul]
  exact hr κ L hA

/-- **A jump table read**: the selector word is `g^j` and the slot `first + j` is the word of the
destination cell. -/
theorem slot_hw (h : Rds Ag fp size w) {pc x first e j : ℕ} (hx : x < size) (he : e < size)
    (hj : w x = ofK (addressOfIndex j))
    (hr : ∀ (κ : ℕ) (L : MemoryImage κ), Ag κ L →
      L.read (addressOfIndex (Γ.l.tablesBase + (first + j))) = some (w e)) :
    HW Γ fp Ag pc (.slot x first e) := by
  intro κ L hA
  refine deref_hw (Γ := Γ) (mode := .cell) h hx he
    (by rw [hj]; exact (isInK_iff _).mpr ⟨_, rfl⟩) (fun κ L hA => ?_) κ L hA
  rw [hj, limb_ofK, idx_mul, show j + (Γ.l.tablesBase + first) = Γ.l.tablesBase + (first + j) by
    omega]
  exact hr κ L hA

/-- **A copy into the next frame**: the memory holds the product there. -/
theorem mulNextFrame_hw (h : Rds Ag fp size w) {pc a b c : ℕ} (ha : a < size) (hb : b < size)
    (hr : ∀ (κ : ℕ) (L : MemoryImage κ), Ag κ L →
      L.read (addressOfIndex (fp + (Γ.frame + c))) = some (w a * w b)) :
    HW Γ fp Ag pc (.mulNextFrame a b c) := by
  intro κ L hA
  refine ⟨w a, w b, h.read hA ha, h.read hA hb, ?_⟩
  rw [idx_mul]
  exact hr κ L hA

/-- **A `KECCAK`**: its input words and some output words, those it writes the cells' words, are
related. -/
theorem keccak_hw (h : Rds Ag fp size w) {pc m0 m1 m2 m3 tail b8 cap out : ℕ} {inOdd outOdd : Bool}
    {oc : KeccakOutputCells} {output : Fin 13 → E}
    (hin : ∀ c : Fin 13, keccakInOff m0 m1 m2 m3 tail b8 cap c.val < size)
    (hout : ∀ c : Fin 13, c.val < oc.cellCount → out + c.val < size ∧ output c = w (out + c.val))
    (hw : KeccakCellsRelation (fun c : Fin 13 => w (keccakInOff m0 m1 m2 m3 tail b8 cap c)) inOdd
      output outOdd oc) :
    HW Γ fp Ag pc (.keccak m0 m1 m2 m3 tail b8 cap out inOdd outOdd oc) := by
  intro κ L hA
  exact ⟨_, output, fun c => h.read hA (hin c), fun c hc => by
    rw [(hout c hc).2]; exact h.read hA (hout c hc).1, hw⟩

/-- **A `JUMP`** on words read from its cells. -/
theorem jw_of {hdr : E × E} {FS : FrameSpec} (h : Rds Ag fp size (fwd hdr FS)) {oc od of : ℕ}
    {fall : Prop} {taken : E → E → Prop} (hc : oc < size) (hd : od < size) (hf : of < size)
    (hcK : IsInK (fwd hdr FS oc)) (hdK : IsInK (fwd hdr FS od)) (hfK : IsInK (fwd hdr FS of))
    (h0 : fwd hdr FS oc = 0 → fall)
    (h1 : fwd hdr FS oc ≠ 0 → taken (fwd hdr FS od) (fwd hdr FS of)) :
    JW fp hdr FS Ag oc od of fall taken := by
  refine ⟨fun κ L hA n hn => ?_, hcK, hdK, hfK, h0, h1⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with rfl | rfl | rfl
  · exact h κ L hA _ hc
  · exact h κ L hA _ hd
  · exact h κ L hA _ hf

/-! ## Segments -/

theorem segW_nil {ops : List LOp} {pos : ℕ} (h : ops = []) : SegW Γ fp Ag ops pos := by
  subst h
  intro i hi
  exact absurd hi (Nat.not_lt_zero _)

theorem segW_cons {o : LOp} {os : List LOp} {pos : ℕ} :
    SegW Γ fp Ag (o :: os) pos ↔ HW Γ fp Ag (Γ.pc0 + pos) o ∧ SegW Γ fp Ag os (pos + 1) := by
  constructor
  · intro h
    refine ⟨by simpa using h 0 (Nat.zero_lt_succ _), fun i hi => ?_⟩
    have := h (i + 1) (Nat.succ_lt_succ hi)
    rw [show Γ.pc0 + (pos + 1) + i = Γ.pc0 + pos + (i + 1) by omega]
    exact this
  · rintro ⟨h0, h1⟩ i hi
    cases i with
    | zero => simpa using h0
    | succ i =>
        have := h1 i (Nat.lt_of_succ_lt_succ hi)
        rw [show Γ.pc0 + (pos + 1) + i = Γ.pc0 + pos + (i + 1) by omega] at this
        exact this

theorem segW_append {a b : List LOp} {pos : ℕ} :
    SegW Γ fp Ag (a ++ b) pos ↔ SegW Γ fp Ag a pos ∧ SegW Γ fp Ag b (pos + a.length) := by
  induction a generalizing pos with
  | nil =>
      simp only [List.nil_append, List.length_nil, Nat.add_zero, iff_and_self]
      exact fun _ => segW_nil rfl
  | cons o os ih =>
      rw [List.cons_append, segW_cons, segW_cons, ih, List.length_cons, and_assoc,
        show pos + 1 + os.length = pos + (os.length + 1) by omega]

/-- A run made of a list, one instruction an element. -/
theorem segW_zipIdx {l : List ℕ} {f : ℕ × ℕ → LOp} {pos : ℕ}
    (h : ∀ k (hk : k < l.length), HW Γ fp Ag (Γ.pc0 + pos + k) (f (l[k], k))) :
    SegW Γ fp Ag (l.zipIdx.map f) pos := by
  intro i hi
  simp only [List.length_map, List.length_zipIdx] at hi
  simpa using h i hi

/-! ## The calls' instructions -/

/-- **A call's instructions before its jump**: the entry; the arguments and (a registered loop
helper's) self pointer copied into the callee frame `kfp`; its header `kh` there: this frame's
header for a tail call, else the return pc and this frame. -/
theorem callPre_segW (hr : Rds Ag fp size w) {c : CallSite} {pos kfp : ℕ} {kh : E × E}
    (hs : 2 ≤ size) (hen : c.entry < size) (hnfp : c.nfp < size)
    (hent : w c.entry = OffsetInstruction.immediateWord
      (resolveK Γ.l Γ.pc0 Γ.frame (.entry c.callee)).1
      (resolveK Γ.l Γ.pc0 Γ.frame (.entry c.callee)).2)
    (hkw : w c.nfp = ofK (addressOfIndex kfp))
    (hargs : ∀ k (hk : k < c.args.length), c.args[k] < size ∧
      ∀ (κ : ℕ) (L : MemoryImage κ), Ag κ L →
        L.read (addressOfIndex (kfp + (argBase + k))) = some (w c.args[k]))
    (hloop : c.loop.isSome → ∀ (κ : ℕ) (L : MemoryImage κ), Ag κ L →
      L.read (addressOfIndex (kfp + (argBase + c.args.length))) = some (w c.nfp))
    (hhdr : ∀ (κ : ℕ) (L : MemoryImage κ), Ag κ L →
      L.read (addressOfIndex (kfp + 0)) = some kh.1 ∧ L.read (addressOfIndex (kfp + 1)) = some kh.2)
    (hkh : kh = if c.tail then (w 0, w 1) else
      (Γ.tgt (pos + (callPre c).length + 1), ofK (addressOfIndex fp))) :
    SegW Γ fp Ag (callPre c) pos := by
  have hlen : (callPre c).length = c.args.length + (if c.loop.isSome then 1 else 0) + 3 := by
    simp only [callPre]
    split <;> split <;> simp
  rw [hlen] at hkh
  unfold callPre
  refine segW_append.mpr ⟨segW_cons.mpr ⟨set_hw hr hen hent, segW_nil rfl⟩,
    segW_append.mpr ⟨segW_append.mpr ⟨segW_zipIdx fun k hk => ?_, ?_⟩, ?_⟩⟩
  · exact derefAt_hw hr hnfp (hargs k hk).1 hkw (hargs k hk).2
  · split
    · next hl => exact segW_cons.mpr ⟨derefAt_hw hr hnfp hnfp hkw (hloop hl), segW_nil rfl⟩
    · exact segW_nil rfl
  · cases ht : c.tail
    · simp only [ht, Bool.false_eq_true, ↓reduceIte] at hkh ⊢
      subst hkh
      refine segW_cons.mpr ⟨derefAt_hw hr hnfp (by omega) hkw fun κ L hA => (hhdr κ L hA).2,
        segW_cons.mpr ⟨derefAt_hw hr hnfp (by omega) hkw fun κ L hA => ?_, segW_nil rfl⟩⟩
      rw [(hhdr κ L hA).1, derefSource_pc, Site.tgt]
      show some (ofK (addressOfIndex _)) = some (ofK (addressOfIndex _))
      congr 3
      by_cases hl : c.loop.isSome = true <;> simp [hl] <;> omega
    · simp only [ht, ↓reduceIte] at hkh ⊢
      subst hkh
      exact segW_cons.mpr ⟨derefAt_hw hr hnfp (by omega) hkw fun κ L hA => (hhdr κ L hA).2,
        segW_cons.mpr ⟨derefAt_hw hr hnfp (by omega) hkw fun κ L hA => (hhdr κ L hA).1,
          segW_nil rfl⟩⟩

/-- **A call's instructions after its jump**: the returned words read back from the callee frame
`kfp`. -/
theorem callRets_segW (hr : Rds Ag fp size w) {nfp nargs pos kfp : ℕ} {rets : List Cell}
    (hnfp : nfp < size) (hkw : w nfp = ofK (addressOfIndex kfp))
    (hrets : ∀ k (hk : k < rets.length), rets[k] < size ∧
      ∀ (κ : ℕ) (L : MemoryImage κ), Ag κ L →
        L.read (addressOfIndex (kfp + (argBase + nargs + k))) = some (w rets[k])) :
    SegW Γ fp Ag (callRets nfp nargs rets) pos :=
  segW_zipIdx fun k hk => derefAt_hw hr hnfp (hrets k hk).1 hkw (hrets k hk).2

/-- **A loop helper's closing call before its jump**: the entry; the arguments, the next frame's
self pointer and this frame's header copied into the next frame. -/
theorem loopPre_segW (hr : Rds Ag fp size w) {callee : String} {nfp entry one pos : ℕ}
    {args : List Cell} (hs : 2 ≤ size) (hen : entry < size) (hnfp : nfp < size) (hone : one < size)
    (h1 : w one = 1)
    (hent : w entry = OffsetInstruction.immediateWord
      (resolveK Γ.l Γ.pc0 Γ.frame (.entry callee)).1 (resolveK Γ.l Γ.pc0 Γ.frame (.entry callee)).2)
    (hargs : ∀ k (hk : k < args.length), args[k] < size ∧
      ∀ (κ : ℕ) (L : MemoryImage κ), Ag κ L →
        L.read (addressOfIndex (fp + (Γ.frame + (argBase + k)))) = some (w args[k]))
    (hself : ∀ (κ : ℕ) (L : MemoryImage κ), Ag κ L →
      L.read (addressOfIndex (fp + (Γ.frame + (argBase + args.length)))) = some (w nfp))
    (hhdr : ∀ (κ : ℕ) (L : MemoryImage κ), Ag κ L →
      L.read (addressOfIndex (fp + (Γ.frame + 1))) = some (w 1) ∧
        L.read (addressOfIndex (fp + (Γ.frame + 0))) = some (w 0)) :
    SegW Γ fp Ag (loopPre callee nfp entry one args) pos := by
  have hm : ∀ a c, a < size → (∀ (κ : ℕ) (L : MemoryImage κ), Ag κ L →
      L.read (addressOfIndex (fp + (Γ.frame + c))) = some (w a)) → ∀ pc,
      HW Γ fp Ag pc (.mulNextFrame a one c) := fun a c ha h pc =>
    mulNextFrame_hw hr ha hone fun κ L hA => by rw [h1, mul_one]; exact h κ L hA
  unfold loopPre
  refine segW_append.mpr ⟨segW_append.mpr ⟨segW_cons.mpr ⟨set_hw hr hen hent, segW_nil rfl⟩,
    segW_zipIdx fun k hk => hm _ _ (hargs k hk).1 (hargs k hk).2 _⟩, ?_⟩
  exact segW_cons.mpr ⟨hm _ _ hnfp hself _, segW_cons.mpr ⟨hm _ _ (by omega)
    (fun κ L hA => (hhdr κ L hA).1) _, segW_cons.mpr ⟨hm _ _ (by omega)
    (fun κ L hA => (hhdr κ L hA).2) _, segW_nil rfl⟩⟩⟩

/-- **A fused `match` of calls before its jump**: the arguments and the header (the join and this
frame) written into the callee frame `kfp`, the entry read from the table at the selector. -/
theorem dispatchPre_segW (hr : Rds Ag fp size w) {nfp joinCell x entry first pos kfp j : ℕ}
    {args : List Cell} (hs : 1 ≤ size) (hnfp : nfp < size) (hjc : joinCell < size) (hx : x < size)
    (hen : entry < size) (hkw : w nfp = ofK (addressOfIndex kfp))
    (hargs : ∀ k (hk : k < args.length), args[k] < size ∧
      ∀ (κ : ℕ) (L : MemoryImage κ), Ag κ L →
        L.read (addressOfIndex (kfp + (argBase + k))) = some (w args[k]))
    (hjw : w joinCell = OffsetInstruction.immediateWord
      (resolveK Γ.l Γ.pc0 Γ.frame (.local (pos + args.length + 5))).1
      (resolveK Γ.l Γ.pc0 Γ.frame (.local (pos + args.length + 5))).2)
    (hhdr : ∀ (κ : ℕ) (L : MemoryImage κ), Ag κ L →
      L.read (addressOfIndex (kfp + 0)) = some (w joinCell) ∧
        L.read (addressOfIndex (kfp + 1)) = some (ofK (addressOfIndex fp)))
    (hj : w x = ofK (addressOfIndex j))
    (hslot : ∀ (κ : ℕ) (L : MemoryImage κ), Ag κ L →
      L.read (addressOfIndex (Γ.l.tablesBase + (first + j))) = some (w entry)) :
    SegW Γ fp Ag (dispatchPre pos nfp joinCell x entry first args) pos := by
  unfold dispatchPre
  refine segW_append.mpr ⟨segW_append.mpr ⟨segW_zipIdx fun k hk =>
    derefAt_hw hr hnfp (hargs k hk).1 hkw (hargs k hk).2, segW_cons.mpr
    ⟨derefAt_hw hr hnfp (by omega) hkw fun κ L hA => (hhdr κ L hA).2, segW_nil rfl⟩⟩, ?_⟩
  exact segW_cons.mpr ⟨set_hw hr hjc hjw, segW_cons.mpr ⟨derefAt_hw hr hnfp hjc hkw
    fun κ L hA => (hhdr κ L hA).1, segW_cons.mpr ⟨slot_hw hr hx hen hj hslot, segW_nil rfl⟩⟩⟩

/-! ## A `KECCAK`'s cells -/

theorem keccakIn_mem {m0 m1 m2 m3 tail b8 cap out : ℕ} {inOdd outOdd : Bool}
    {oc : KeccakOutputCells} (c : Fin 13) :
    keccakInOff m0 m1 m2 m3 tail b8 cap c.val ∈
      opCells (.keccak m0 m1 m2 m3 tail b8 cap out inOdd outOdd oc) := by
  simp only [opCells, List.mem_append, List.mem_cons, List.mem_map, List.mem_range,
    List.not_mem_nil, or_false, keccakInOff]
  have := c.isLt
  split_ifs <;> first
    | (left; left; left; simp_all; done)
    | (left; left; right; exact ⟨_, by omega, rfl⟩)
    | (left; right; exact ⟨_, by omega, rfl⟩)

theorem keccakOut_mem {m0 m1 m2 m3 tail b8 cap out : ℕ} {inOdd outOdd : Bool}
    {oc : KeccakOutputCells} (c : Fin 13) (hc : c.val < oc.cellCount) :
    out + c.val ∈ opCells (.keccak m0 m1 m2 m3 tail b8 cap out inOdd outOdd oc) := by
  simp only [opCells, List.mem_append, List.mem_map, List.mem_range]
  exact Or.inr ⟨_, hc, rfl⟩

end Bridge

end
end LeanVM.Compiler.Complete
