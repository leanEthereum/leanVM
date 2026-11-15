/-
  LeanVM.Guest.Backend.Complete.FrameHW

  From the words of a frame's cells to `PathWords`' instruction facts: each straight-line
  instruction holds (`HW`) and each jump reads its words (`JW`) on every memory holding the words.
-/

module

public import LeanVM.Guest.Backend.Complete.Frame
public import LeanVM.Guest.Backend.Complete.PathRun

/-!
# Straight-line instructions on frame words

`PathWords` asks, of each straight-line instruction on the path, that it holds on every memory the
frame words describe (`HW`), and of each jump that its cells read their words there (`JW`). Here
both follow from facts about words: `Rds Ag fp size w` says every memory `Ag` admits reads `w n` at
cell `n` of the frame `fp` below `size`; then a `SET` holds when its cell's word is the immediate's,
an `XOR`/`MUL` when its words add or multiply, a `DEREF` when the memory reads the word at the
address its pointer word gives (a load, a callee frame cell, a jump table slot), a copy into the
next frame when the memory holds the product there, a `KECCAK` when its words are related. The
frame side's per-instruction relation `OpW` gives `HW` at once (`opW_hw`, `opW_jw`).
-/

namespace LeanVM.Guest.Backend.Complete

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

/-- **A `KECCAK`**: its words are related. -/
theorem keccak_hw (h : Rds Ag fp size w) {pc m0 m1 m2 m3 tail b8 cap out : ℕ} {inOdd outOdd : Bool}
    {oc : KeccakOutputCells}
    (hin : ∀ c : Fin 13, keccakInOff m0 m1 m2 m3 tail b8 cap c.val < size)
    (hout : ∀ c : Fin 13, c.val < oc.cellCount → out + c.val < size)
    (hw : KeccakCellsRelation (fun c : Fin 13 => w (keccakInOff m0 m1 m2 m3 tail b8 cap c)) inOdd
      (fun c : Fin 13 => w (out + c.val)) outOdd oc) :
    HW Γ fp Ag pc (.keccak m0 m1 m2 m3 tail b8 cap out inOdd outOdd oc) := by
  intro κ L hA
  exact ⟨_, _, fun c => h.read hA (hin c), fun c hc => h.read hA (hout c hc), hw⟩

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

end Bridge

/-! ## The frame side's relation -/

section OpW

variable {κ₀ : ℕ} {Γ : Site κ₀} {Ag : (κ : ℕ) → MemoryImage κ → Prop} {I : Inst} {Ψ : ℕ → E}

/-- The memories `Ag` admits hold the frame words `Ψ` and are readers of the instance. -/
def AgRd (Ag : (κ : ℕ) → MemoryImage κ → Prop) (I : Inst) (Ψ : ℕ → E) : Prop :=
  ∀ (κ : ℕ) (L : MemoryImage κ), Ag κ L → FrameRd I Ψ L.read ∧ I.Rd L.read

/-- The instance's immediate words are the layout's. -/
def KwOf (Γ : Site κ₀) (I : Inst) : Prop :=
  ∀ k, I.kw k = OffsetInstruction.immediateWord (resolveK Γ.l Γ.pc0 Γ.frame k).1
    (resolveK Γ.l Γ.pc0 Γ.frame k).2

theorem AgRd.rds (h : AgRd Ag I Ψ) : Rds Ag I.fp I.size (fw I Ψ) := by
  intro κ L hA n hn
  obtain ⟨⟨h0, h1, h2⟩, -⟩ := h κ L hA
  rcases n with _ | _ | n
  · simpa [fw] using h0
  · simpa [fw] using h1
  · simpa [fw] using h2 (n + 2) (by omega) hn

theorem fw_eq_fwd (I : Inst) (FS : FrameSpec) : fw I FS.Ψ = fwd I.hdr FS := rfl

/-- **The frame side's relation of a straight-line instruction gives `HW`**, its own cells in the
frame. -/
theorem opW_hw (h : AgRd Ag I Ψ) (hkw : KwOf Γ I) {pc : ℕ} {o : LOp}
    (hj : ∀ oc od of, o ≠ .jump oc od of) (hc : ∀ n ∈ opCells o, n < I.size) (hw : OpW I Ψ o) :
    HW Γ I.fp Ag pc o := by
  have hr := h.rds
  cases o with
  | set o k => exact set_hw hr (hc o (by simp [opCells])) (hw.trans (hkw k))
  | xor a b c =>
      exact xor_hw hr (hc a (by simp [opCells])) (hc b (by simp [opCells]))
        (hc c (by simp [opCells])) hw
  | mul a b c =>
      exact mul_hw hr (hc a (by simp [opCells])) (hc b (by simp [opCells]))
        (hc c (by simp [opCells])) hw
  | deref p off d mode =>
      cases mode with
      | cell =>
          exact deref_hw hr (hc p (by simp [opCells])) (hc d (by simp [opCells])) hw.1
            fun κ L hA => hw.2 L.read (h κ L hA).1 (h κ L hA).2
      | fp =>
          exact deref_hw hr (hc p (by simp [opCells])) (hc d (by simp [opCells])) hw.1
            fun κ L hA => hw.2 L.read (h κ L hA).1 (h κ L hA).2
      | pc => exact hw.elim
  | jump oc od of => exact absurd rfl (hj oc od of)
  | keccak m0 m1 m2 m3 tail b8 cap out inOdd outOdd oc =>
      refine keccak_hw hr (fun c => hc _ ?_) (fun c hc' => hc _ ?_) hw
      · simp only [opCells, List.mem_append, List.mem_cons, List.mem_map, List.mem_range,
          List.not_mem_nil, or_false, keccakInOff]
        have := c.isLt
        split_ifs <;> first
          | (left; left; left; simp_all; done)
          | (left; left; right; exact ⟨_, by omega, rfl⟩)
          | (left; right; exact ⟨_, by omega, rfl⟩)
      · simp only [opCells, List.mem_append, List.mem_map, List.mem_range]
        exact Or.inr ⟨_, hc', rfl⟩
  | slot => exact hw.elim
  | mulNextFrame => exact hw.elim

/-- **The frame side's relation of a straight-line `JUMP` gives `JW`**: it falls through. -/
theorem opW_jw {FS : FrameSpec} (h : AgRd Ag I FS.Ψ) {oc od of : ℕ} {fall : Prop}
    {taken : E → E → Prop} (hc : ∀ n ∈ opCells (.jump oc od of), n < I.size)
    (hw : OpW I FS.Ψ (.jump oc od of)) (hf : fall) : JW I.fp I.hdr FS Ag oc od of fall taken := by
  have hr : Rds Ag I.fp I.size (fwd I.hdr FS) := h.rds
  obtain ⟨h0, hd, hf'⟩ := hw
  exact jw_of hr (hc oc (by simp [opCells])) (hc od (by simp [opCells]))
    (hc of (by simp [opCells])) (by rw [← fw_eq_fwd, h0]; exact (isInK_iff _).mpr ⟨0, by simp⟩)
    hd hf' (fun _ => hf) (fun h' => absurd h0 h')

end OpW

end
end LeanVM.Guest.Backend.Complete
