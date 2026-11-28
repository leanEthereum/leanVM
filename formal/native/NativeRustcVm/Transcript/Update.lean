module

public import NativeRustcVm.Transcript.Frame

/-!
# The transcript's state after a change of one of its parts

A memory that agrees with another on an area but at offsets `W` (`Agree`, from `SameOutside` by
`agree_of_sameOutside`) keeps the bytes there (`bytesAt_agree`), the decoded proof
(`DecodedAt.agree`, `PhaseAt.agree`) and the parts of a sponge or a `TState` that `W` avoids. The
representations after a change: the sponge's lanes (`SpongeAt.with_state`), its queue
(`with_pending`), its ground challenge (`with_ground`); the `TState`'s sponge
(`TStateAt.with_sponge`), cursor (`with_cursor`), a root pushed (`with_root`); nothing
(`SpongeAt.frame`, `TStateAt.frame`).
-/

namespace NativeRustcVm.Transcript

open NativeVm NativeVm.Model LeanVM.Parameters LeanVM.Protocol.Compile LeanVM.Semantics

@[expose] public section

/-- `d'` agrees with `d` on the `N` bytes from `b` but at the offsets `W`. -/
def Agree (d d' : Mem 64) (b : BitVec 64) (N : Nat) (W : Nat → Prop) : Prop :=
  ∀ j < N, ¬ W j → d'.get? (off b j) = d.get? (off b j)

end

public section

variable {d d' : Mem 64}

theorem agree_of_sameOutside {b : BitVec 64} {N : Nat} {W : Nat → Prop} {R : BitVec 64 → Prop}
    (hN : NoWrap b N) (hR : ∀ q, R q → ¬ InRange b N q)
    (hs : SameOutside d d' (fun q ↦ Touch b N W q ∨ R q)) : Agree d d' b N W := by
  intro j hj hW
  refine hs _ ?_
  have hN' := hN
  unfold NoWrap at hN'
  rintro (⟨i, hi, hWi, hq⟩ | hq)
  · have e : j = i := off_inj hN hi hj hq
    exact hW (e ▸ hWi)
  · exact hR _ hq (inRange_off_self hj (by omega))

/-- An area apart from the one changed agrees everywhere. -/
theorem agree_of_apart {b a : BitVec 64} {N n : Nat} {W : Nat → Prop} {R : BitVec 64 → Prop}
    (hN : NoWrap b N) (hn : NoWrap a n) (hA : Apart b N a n) (hR : ∀ q, R q → ¬ InRange a n q)
    (hs : SameOutside d d' (fun q ↦ Touch b N W q ∨ R q)) : Agree d d' a n (fun _ ↦ False) := by
  intro j hj _
  refine hs _ ?_
  have hn' := hn
  unfold NoWrap at hn'
  have hin : InRange a n (off a j) := inRange_off_self hj (by omega)
  rintro (⟨i, hi, -, hq⟩ | hq)
  · have hN' := hN
    unfold NoWrap at hN'
    exact not_inRange_of_apart hA hN hn (hq ▸ inRange_off_self hi (by omega)) hin
  · exact hR _ hq hin

theorem Agree.mono {b : BitVec 64} {N : Nat} {W W' : Nat → Prop} (h : Agree d d' b N W)
    (hW : ∀ j, W j → W' j) : Agree d d' b N W' :=
  fun j hj hw ↦ h j hj fun h' ↦ hw (hW j h')

theorem bytesAt_agree {b : BitVec 64} {N : Nat} {W : Nat → Prop} (h : Agree d d' b N W)
    {o : Nat} {bs : List UInt8} (hle : o + bs.length ≤ N) (hW : ∀ i < bs.length, ¬ W (o + i))
    (hb : BytesAt d (off b o) bs) : BytesAt d' (off b o) bs :=
  bytesAt_congr hb fun i hi ↦ by rw [off_add]; exact h _ (by omega) (hW i hi)

section agree
variable {b : BitVec 64} {N : Nat} {W : Nat → Prop} (h : Agree d d' b N W)
include h

theorem wordAt_agree {o : Nat} {w : UInt64} (hle : o + 8 ≤ N) (hW : ∀ i < 8, ¬ W (o + i))
    (hb : WordAt d (off b o) w) : WordAt d' (off b o) w :=
  bytesAt_agree h hle hW hb

theorem ewAt_agree {o : Nat} {x : EW} (hle : o + 16 ≤ N) (hW : ∀ i < 16, ¬ W (o + i))
    (hb : EWAt d (off b o) x) : EWAt d' (off b o) x :=
  bytesAt_agree h hle hW hb

theorem wordsAt_agree {o : Nat} {ws : List UInt64} (hle : o + 8 * ws.length ≤ N)
    (hW : ∀ i < 8 * ws.length, ¬ W (o + i)) (hb : WordsAt d (off b o) ws) :
    WordsAt d' (off b o) ws :=
  bytesAt_agree h (by rw [length_flatMap_wordBytes]; omega)
    (fun i hi ↦ hW i (by rw [length_flatMap_wordBytes] at hi; omega)) hb

theorem optEWAt_agree {o : Nat} {g : Option EW} (hle : o + 24 ≤ N)
    (hW : ∀ i < 24, ¬ W (o + i)) (hb : OptEWAt d (off b o) g) : OptEWAt d' (off b o) g := by
  cases g with
  | none => exact wordAt_agree h (by omega) (fun i hi ↦ hW i (by omega)) hb
  | some c =>
    refine ⟨wordAt_agree h (by omega) (fun i hi ↦ hW i (by omega)) hb.1, ?_⟩
    have := hb.2
    rw [off_off] at this ⊢
    exact ewAt_agree h (by omega) (fun i hi ↦ by
      have := hW (8 + i) (by omega); rwa [← Nat.add_assoc] at this) this

end agree

/-! ## The decoded proof -/

theorem phaseWords_eq : phaseWords = 49411 := rfl
theorem openingWords_eq : openingWords = 193 := rfl

theorem phaseBase_add_le {L k : Nat} (hk : k < wireMaxPhases) :
    phaseBase L k + phaseWords ≤ decodedWords L := by
  simp only [decodedWords, phaseBase, phaseWords_eq, wireMaxPhases] at hk ⊢
  have : k * 49411 + 49411 ≤ 8 * 49411 := by
    rw [← Nat.succ_mul]; exact Nat.mul_le_mul_right _ hk
  omega

theorem streamEnd_lt (L : Nat) : streamEnd L < decodedWords L := by
  simp only [decodedWords, phaseBase, phaseWords_eq, wireMaxPhases]
  omega

theorem openingAt_agree {o h width : Nat} {op : OpeningW} {a : BitVec 64} {n : Nat}
    (hA : Agree d d' a n (fun _ ↦ False)) (hh : h ≤ wireMaxHeight)
    (hw : width ≤ wireMaxLeafWords) (hle : o + 8 * openingWords ≤ n)
    (ho : OpeningAt d (off a o) h width op) : OpeningAt d' (off a o) h width op := by
  obtain ⟨hl, hp, hi, h0, hleaf, hpath⟩ := ho
  simp only [openingWords_eq, wireMaxHeight, wireMaxLeafWords] at hle hh hw
  refine ⟨hl, hp, hi, wordAt_agree hA (by omega) (fun _ _ ↦ id) h0, ?_, ?_⟩
  · rw [off_off] at hleaf ⊢
    exact wordsAt_agree hA (by simp [hl]; omega) (fun _ _ ↦ id) hleaf
  · rw [off_off] at hpath ⊢
    refine wordsAt_agree hA ?_ (fun _ _ ↦ id) hpath
    have : (op.path.toList.flatMap (·.toList)).length = 4 * op.path.size := by
      rw [← Array.length_toList]
      generalize op.path.toList = l
      induction l with
      | nil => rfl
      | cons x l ih => simp only [List.flatMap_cons, List.length_append, ih, Vector.length_toList,
          List.length_cons]; omega
    rw [this, hp]
    simp only [wireMaxLeafWords]
    omega

theorem phaseAt_agree {o : Nat} {ph : Array OpeningW} {a : BitVec 64} {n : Nat}
    (hA : Agree d d' a n (fun _ ↦ False)) (hle : o + 8 * phaseWords ≤ n)
    (hp : PhaseAt d (off a o) ph) : PhaseAt d' (off a o) ph := by
  obtain ⟨h, width, hh, hw, hq, h0, h1, h2, hs⟩ := hp
  simp only [phaseWords_eq] at hle
  refine ⟨h, width, hh, hw, hq, wordAt_agree hA (by omega) (fun _ _ ↦ id) h0, ?_, ?_,
    fun j hj ↦ ?_⟩
  · rw [off_off] at h1 ⊢; exact wordAt_agree hA (by omega) (fun _ _ ↦ id) h1
  · rw [off_off] at h2 ⊢; exact wordAt_agree hA (by omega) (fun _ _ ↦ id) h2
  · have := hs j hj
    rw [off_off] at this ⊢
    refine openingAt_agree hA hh hw ?_ this
    have hj' : j < 256 := by simp only [wireMaxQueries] at hq; omega
    simp only [openingWords_eq]
    have : j * 193 + 193 ≤ 256 * 193 := by rw [← Nat.succ_mul]; exact Nat.mul_le_mul_right _ hj'
    omega

theorem DecodedAt.agree {a : DecArea} {stream : Array EW} {openings : Array (Array OpeningW)}
    (h : DecodedAt d a stream openings) (hA : Agree d d' a.words (8 * a.len) (fun _ ↦ False)) :
    DecodedAt d' a stream openings := by
  have hlen := h.len
  have hse := streamEnd_lt a.l
  have hsl := h.stream_le
  refine ⟨h.l_lt, hlen, hsl, wordAt_agree hA (by omega) (fun _ _ ↦ id) h.stream_count,
    fun i hi ↦ ewAt_agree hA ?_ (fun _ _ ↦ id) (h.stream i hi), h.phases_le,
    wordAt_agree hA (by omega) (fun _ _ ↦ id) h.phase_count,
    fun k hk ↦ phaseAt_agree hA ?_ (h.phases k hk)⟩
  · simp only [streamEnd, maxStream] at hse hsl
    omega
  · have := phaseBase_add_le (L := a.l) (Nat.lt_of_lt_of_le hk h.phases_le)
    omega

/-! ## The sponge -/

section sponge
variable {p : BitVec 64} {sp : SpongeW}

theorem pendingAt_agree {N : Nat} {W : Nat → Prop} (hA : Agree d d' p N W) {o : Nat}
    {x : EW × UInt64} (hle : o + 24 ≤ N) (hW : ∀ i < 24, ¬ W (o + i))
    (h : PendingAt d (off p o) x) : PendingAt d' (off p o) x := by
  refine ⟨ewAt_agree hA (by omega) (fun i hi ↦ hW i (by omega)) h.1, ?_⟩
  have := h.2
  rw [off_off] at this ⊢
  exact wordAt_agree hA (by omega) (fun i hi ↦ by
    have := hW (16 + i) (by omega); rwa [← Nat.add_assoc] at this) this

/-- The sponge kept where the memory agrees with the old one on its 328 bytes. -/
theorem SpongeAt.agree {N : Nat} {W : Nat → Prop} (h : SpongeAt d p sp) (hA : Agree d d' p N W)
    (hN : spongeBytes ≤ N) (hW : ∀ j < spongeBytes, ¬ W j) : SpongeAt d' p sp := by
  unfold spongeBytes at hN hW
  have hle := h.pending_le
  unfold rateScalars at hle
  refine ⟨?_, h.pending_le, ?_, fun i hi ↦ ?_, ?_⟩
  · have := h.state
    rw [← off_zero p] at this ⊢
    exact wordsAt_agree hA (by simp; omega) (fun i hi ↦ hW _ (by simp at hi; omega)) this
  · exact wordAt_agree hA (by omega) (fun i hi ↦ hW _ (by omega)) h.n_pending
  · exact pendingAt_agree hA (by omega) (fun j hj ↦ hW _ (by omega)) (h.pending i hi)
  · exact optEWAt_agree hA (by omega) (fun i hi ↦ hW _ (by omega)) h.ground

theorem SpongeAt.frame {R : BitVec 64 → Prop} (h : SpongeAt d p sp) (hN : NoWrap p spongeBytes)
    (hR : ∀ q, R q → ¬ InRange p spongeBytes q) (hs : SameOutside d d' R) : SpongeAt d' p sp :=
  h.agree (agree_of_sameOutside (W := fun _ ↦ False) hN hR
    (SameOutside.mono hs fun _ hq ↦ Or.inr hq)) le_rfl (fun _ _ ↦ id)

/-- **The lanes changed.** -/
theorem SpongeAt.with_state (h : SpongeAt d p sp) (hA : Agree d d' p spongeBytes (· < 200))
    {st : KeccakState} (hst : WordsAt d' p st.toList) : SpongeAt d' p { sp with state := st } := by
  unfold spongeBytes at hA
  have hle := h.pending_le
  unfold rateScalars at hle
  refine ⟨hst, h.pending_le, ?_, fun i hi ↦ ?_, ?_⟩
  · exact wordAt_agree hA (by omega) (fun i hi ↦ by omega) h.n_pending
  · have hi' : i < sp.pending.size := hi
    exact pendingAt_agree hA (by omega) (fun j hj ↦ by omega) (h.pending i hi)
  · exact optEWAt_agree hA (by omega) (fun i hi ↦ by omega) h.ground

/-- **The queue changed**: its slots and count. -/
theorem SpongeAt.with_pending (h : SpongeAt d p sp)
    (hA : Agree d d' p spongeBytes (fun j ↦ 200 ≤ j ∧ j < 304)) {pend : Array (EW × UInt64)}
    (hle : pend.size ≤ rateScalars) (hn : WordAt d' (off p 296) pend.size.toUInt64)
    (hp : ∀ i (h : i < pend.size), PendingAt d' (off p (200 + 24 * i)) pend[i]) :
    SpongeAt d' p { sp with pending := pend } := by
  unfold spongeBytes at hA
  refine ⟨?_, hle, hn, hp, ?_⟩
  · have := h.state
    rw [← off_zero p] at this ⊢
    exact wordsAt_agree hA (by simp) (fun i hi ↦ by simp at hi; omega) this
  · exact optEWAt_agree hA (by omega) (fun i hi ↦ by omega) h.ground

/-- **A scalar pushed** on a queue of `n < rateScalars`: its slot and the count written. -/
theorem SpongeAt.push (h : SpongeAt d p sp) (hlt : sp.pending.size < rateScalars)
    (hA : Agree d d' p spongeBytes (fun j ↦ (200 + 24 * sp.pending.size ≤ j ∧
      j < 224 + 24 * sp.pending.size) ∨ (296 ≤ j ∧ j < 304)))
    {x : EW × UInt64} (hn : WordAt d' (off p 296) (sp.pending.size + 1).toUInt64)
    (hx : PendingAt d' (off p (200 + 24 * sp.pending.size)) x) :
    SpongeAt d' p { sp with pending := sp.pending.push x } := by
  unfold rateScalars at hlt
  unfold spongeBytes at hA
  have hle : (sp.pending.push x).size ≤ rateScalars := by
    rw [Array.size_push]; unfold rateScalars; omega
  refine h.with_pending (hA.mono fun j hj ↦ by omega) hle
    (by rw [Array.size_push]; exact hn) fun i hi ↦ ?_
  simp only [Array.size_push] at hi
  by_cases hlt' : i < sp.pending.size
  · rw [Array.getElem_push_lt hlt']
    exact pendingAt_agree hA (by omega) (fun j hj ↦ by omega) (h.pending i hlt')
  · have : i = sp.pending.size := by omega
    subst this
    rw [Array.getElem_push_eq]
    exact hx

/-- **The ground challenge changed.** -/
theorem SpongeAt.with_ground (h : SpongeAt d p sp)
    (hA : Agree d d' p spongeBytes (fun j ↦ 304 ≤ j)) {g : Option EW}
    (hg : OptEWAt d' (off p 304) g) : SpongeAt d' p { sp with ground := g } := by
  unfold spongeBytes at hA
  have hle := h.pending_le
  unfold rateScalars at hle
  refine ⟨?_, h.pending_le, ?_, fun i hi ↦ ?_, hg⟩
  · have := h.state
    rw [← off_zero p] at this ⊢
    exact wordsAt_agree hA (by simp) (fun i hi ↦ by simp at hi; omega) this
  · exact wordAt_agree hA (by omega) (fun i hi ↦ by omega) h.n_pending
  · have hi' : i < sp.pending.size := hi
    exact pendingAt_agree hA (by omega) (fun j hj ↦ by omega) (h.pending i hi)

end sponge

/-! ## The `TState` -/

section tstate
variable {t : BitVec 64} {a : DecArea} {s : TState}

theorem rootAt_agree {N : Nat} {W : Nat → Prop} (hA : Agree d d' t N W) {o : Nat} {r : RootW}
    (hle : o + 48 ≤ N) (hW : ∀ i < 48, ¬ W (o + i)) (h : RootAt d (off t o) r) :
    RootAt d' (off t o) r := by
  obtain ⟨hh, hw, hd, h1, h2⟩ := h
  refine ⟨hh, hw, wordsAt_agree hA (by simp; omega) (fun i hi ↦ hW i (by simp at hi; omega)) hd,
    ?_, ?_⟩
  · rw [off_off] at h1 ⊢
    exact wordAt_agree hA (by omega) (fun i hi ↦ by
      have := hW (32 + i) (by omega); rwa [← Nat.add_assoc] at this) h1
  · rw [off_off] at h2 ⊢
    exact wordAt_agree hA (by omega) (fun i hi ↦ by
      have := hW (40 + i) (by omega); rwa [← Nat.add_assoc] at this) h2

/-- The `TState` with its parts at offsets `W` given anew and the rest kept. -/
theorem TStateAt.agree {W : Nat → Prop} (h : TStateAt d t a s)
    (hk : Keeps d d') (hA : Agree d d' t tstateBytes W)
    (hD : Agree d d' a.words (8 * a.len) (fun _ ↦ False)) {s' : TState}
    (hsp : SpongeAt d' t s'.sponge) (hst : s'.stream = s.stream) (hop : s'.openings = s.openings)
    (hcl : s'.cursor ≤ s'.stream.size) (hc : WordAt d' (off t 352) s'.cursor.toUInt64)
    (hpl : s'.phase ≤ s'.openings.size) (hph : WordAt d' (off t 360) s'.phase.toUInt64)
    (hrl : s'.roots.size ≤ maxRoots) (hnr : WordAt d' (off t 752) s'.roots.size.toUInt64)
    (hr : ∀ i (hi : i < s'.roots.size), RootAt d' (off t (368 + 48 * i)) s'.roots[i])
    (hW : ∀ j, W j → 328 ≤ j → j < 352 → False) : TStateAt d' t a s' := by
  have hf := h.footprint
  unfold tstateBytes at hA
  refine ⟨⟨Region.Ok.keeps hf.1 hk, Region.Ok.keeps hf.2.1 hk, hf.2.2⟩, hsp, ?_, hst ▸ hop ▸ h.decoded.agree hD,
    hcl, hc, hpl, hph, hrl, hnr, hr⟩
  obtain ⟨h0, h1, h2⟩ := h.dec
  refine ⟨wordAt_agree hA (by omega) (fun i hi hw ↦ hW _ hw (by omega) (by omega)) h0, ?_, ?_⟩
  · rw [off_off] at h1 ⊢
    exact wordAt_agree hA (by omega) (fun i hi hw ↦ hW _ hw (by omega) (by omega)) h1
  · rw [off_off] at h2 ⊢
    exact wordAt_agree hA (by omega) (fun i hi hw ↦ hW _ hw (by omega) (by omega)) h2

/-- The `TState`'s footprint: the memory agrees outside it. -/
theorem TStateAt.agrees {W : Nat → Prop} {R : BitVec 64 → Prop} (h : TStateAt d t a s)
    (hR : ∀ q, R q → ¬ InRange t tstateBytes q ∧ ¬ InRange a.words (8 * a.len) q)
    (hs : SameOutside d d' (fun q ↦ Touch t tstateBytes W q ∨ R q)) :
    Agree d d' t tstateBytes W ∧ Agree d d' a.words (8 * a.len) (fun _ ↦ False) :=
  ⟨agree_of_sameOutside h.footprint.1.2 (fun q hq ↦ (hR q hq).1) hs,
    agree_of_apart h.footprint.1.2 h.footprint.2.1.2 h.footprint.2.2 (fun q hq ↦ (hR q hq).2) hs⟩

/-- **The sponge changed.** -/
theorem TStateAt.with_sponge {R : BitVec 64 → Prop} (h : TStateAt d t a s) (hk : Keeps d d')
    (hR : ∀ q, R q → ¬ InRange t tstateBytes q ∧ ¬ InRange a.words (8 * a.len) q)
    (hs : SameOutside d d' (fun q ↦ Touch t tstateBytes (· < spongeBytes) q ∨ R q))
    {sp : SpongeW} (hsp : SpongeAt d' t sp) : TStateAt d' t a { s with sponge := sp } := by
  obtain ⟨hA, hD⟩ := h.agrees hR hs
  unfold tstateBytes spongeBytes at hA
  exact h.agree hk hA hD hsp rfl rfl h.cursor_le
    (wordAt_agree hA (by omega) (fun i hi ↦ by omega) h.cursor) h.phase_le
    (wordAt_agree hA (by omega) (fun i hi ↦ by omega) h.phase) h.roots_le
    (wordAt_agree hA (by omega) (fun i hi ↦ by omega) h.n_roots)
    (fun i hi ↦ by
      have hi' : i < s.roots.size := hi
      exact rootAt_agree hA (by have := h.roots_le; unfold maxRoots at this; omega)
        (fun j hj ↦ by omega) (h.roots i hi))
    (fun j (hj : j < 328) h1 _ ↦ by omega)

/-- **The cursor changed.** -/
theorem TStateAt.with_cursor {R : BitVec 64 → Prop} (h : TStateAt d t a s) (hk : Keeps d d')
    (hR : ∀ q, R q → ¬ InRange t tstateBytes q ∧ ¬ InRange a.words (8 * a.len) q)
    (hs : SameOutside d d' (fun q ↦ Touch t tstateBytes (fun j ↦ 352 ≤ j ∧ j < 360) q ∨ R q))
    {c : Nat} (hcl : c ≤ s.stream.size) (hc : WordAt d' (off t 352) c.toUInt64) :
    TStateAt d' t a { s with cursor := c } := by
  obtain ⟨hA, hD⟩ := h.agrees hR hs
  unfold tstateBytes at hA
  exact h.agree hk hA hD (h.sponge.agree hA (by unfold spongeBytes; omega)
      (fun j hj ⟨h1, _⟩ ↦ by unfold spongeBytes at hj; omega)) rfl rfl hcl hc h.phase_le
    (wordAt_agree hA (by omega) (fun i hi ↦ by omega) h.phase) h.roots_le
    (wordAt_agree hA (by omega) (fun i hi ↦ by omega) h.n_roots)
    (fun i hi ↦ by
      have hi' : i < s.roots.size := hi
      exact rootAt_agree hA (by have := h.roots_le; unfold maxRoots at this; omega)
        (fun j hj ↦ by omega) (h.roots i hi))
    (fun j hj h1 h2 ↦ by omega)

/-- **A root pushed.** -/
theorem TStateAt.with_root {R : BitVec 64 → Prop} (h : TStateAt d t a s) (hk : Keeps d d')
    (hR : ∀ q, R q → ¬ InRange t tstateBytes q ∧ ¬ InRange a.words (8 * a.len) q)
    (hs : SameOutside d d' (fun q ↦ Touch t tstateBytes (fun j ↦
      (368 + 48 * s.roots.size ≤ j ∧ j < 416 + 48 * s.roots.size) ∨ 752 ≤ j) q ∨ R q))
    (hlt : s.roots.size < maxRoots) {r : RootW}
    (hr : RootAt d' (off t (368 + 48 * s.roots.size)) r)
    (hn : WordAt d' (off t 752) (s.roots.size + 1).toUInt64) :
    TStateAt d' t a { s with roots := s.roots.push r } := by
  obtain ⟨hA, hD⟩ := h.agrees hR hs
  unfold tstateBytes at hA
  unfold maxRoots at hlt
  refine h.agree hk hA hD (h.sponge.agree hA (by unfold spongeBytes; omega)
      (fun j hj hw ↦ by unfold spongeBytes at hj; omega)) rfl rfl h.cursor_le
    (wordAt_agree hA (by omega) (fun i hi hw ↦ by omega) h.cursor) h.phase_le
    (wordAt_agree hA (by omega) (fun i hi hw ↦ by omega) h.phase)
    (by simp only [Array.size_push]; unfold maxRoots; omega)
    (by simpa only [Array.size_push] using hn) (fun i hi ↦ ?_) (fun j hj h1 h2 ↦ by omega)
  simp only [Array.size_push] at hi
  by_cases hlt' : i < s.roots.size
  · rw [Array.getElem_push_lt hlt']
    exact rootAt_agree hA (by omega) (fun j hj hw ↦ by
      have : 48 * i + 48 ≤ 48 * s.roots.size := by omega
      omega) (h.roots i hlt')
  · have hi' : i = s.roots.size := by omega
    subst hi'
    rw [Array.getElem_push_eq]
    exact hr

/-- **Nothing changed** of the `TState`. -/
theorem TStateAt.frame {R : BitVec 64 → Prop} (h : TStateAt d t a s) (hk : Keeps d d')
    (hR : ∀ q, R q → ¬ InRange t tstateBytes q ∧ ¬ InRange a.words (8 * a.len) q)
    (hs : SameOutside d d' R) : TStateAt d' t a s := by
  obtain ⟨hA, hD⟩ := h.agrees (W := fun _ ↦ False) hR (SameOutside.mono hs fun _ hq ↦ Or.inr hq)
  unfold tstateBytes at hA
  exact h.agree hk hA hD (h.sponge.agree hA (by unfold spongeBytes; omega) (fun _ _ ↦ id)) rfl
    rfl h.cursor_le (wordAt_agree hA (by omega) (fun _ _ ↦ id) h.cursor) h.phase_le
    (wordAt_agree hA (by omega) (fun _ _ ↦ id) h.phase) h.roots_le
    (wordAt_agree hA (by omega) (fun _ _ ↦ id) h.n_roots)
    (fun i hi ↦ rootAt_agree hA (by have := h.roots_le; unfold maxRoots at this; omega)
      (fun _ _ ↦ id) (h.roots i hi)) (fun _ h _ _ ↦ h)

end tstate

end

end NativeRustcVm.Transcript
