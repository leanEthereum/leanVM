module

public import NativeRustcVmArm.Layout.Common

/-!
# Forms: the model's `addTerm` by cases, forms in memory kept and changed

- `addTerm` finds the first term with the monomial (`addTerm_found`) or appends (`addTerm_none`);
  it never shrinks a form (`le_size_addTerm`, `le_size_addScaled`).
- Memory: bytes that a change misses (`same_of_outside`), a term over them (`TermWAt.of_same`); a
  form with one coefficient changed (`FormBufAt.modify`) or one term appended (`FormBufAt.push`).
- Columns: two terms' column words equal, word by word, are equal columns (`cols_eq_of_words`).
- Where a block wrote (`Match.sameOutside_of`).
-/

namespace NativeRustcVmArm.Layout.Forms

open NativeRustcArm NativeRustcArm.Sym NativeVm.Model NativeRustcVm.Layout
open NativeRustcVm (addr_add_add not_inRange_sub toNat_add_ofNat EWAt WordAt)
open NativeRustcVm.Transcript (off)

public section

/-! ## The model -/

theorem addTerm_found {f : FormW} {cs : Array Nat} {c : EW} {i : Nat} (hi : i < f.size)
    (heq : f[i].cols = cs) (hne : ∀ j (hj : j < i), f[j].cols ≠ cs) :
    FormW.addTerm f cs c = f.modify i fun t ↦ { t with coeff := t.coeff + c } := by
  unfold FormW.addTerm
  rw [(Array.findIdx?_eq_some_iff_getElem (i := i)).mpr
    ⟨hi, by simpa using heq, fun j hj ↦ by simpa using hne j hj⟩]

theorem addTerm_none {f : FormW} {cs : Array Nat} {c : EW}
    (hne : ∀ j (hj : j < f.size), f[j].cols ≠ cs) :
    FormW.addTerm f cs c = f.push ⟨cs, 0 + c⟩ := by
  unfold FormW.addTerm
  rw [Array.findIdx?_eq_none_iff.mpr fun x hx ↦ ?_]
  obtain ⟨j, hj, rfl⟩ := Array.getElem_of_mem hx
  simpa using hne j hj

theorem size_addTerm (f : FormW) (cs : Array Nat) (c : EW) :
    (FormW.addTerm f cs c).size = f.size ∨ (FormW.addTerm f cs c).size = f.size + 1 := by
  unfold FormW.addTerm
  split <;> simp

theorem le_size_addTerm (f : FormW) (cs : Array Nat) (c : EW) :
    f.size ≤ (FormW.addTerm f cs c).size := by
  rcases size_addTerm f cs c with h | h <;> omega

theorem le_size_foldl_addTerm (ts : List TermW) (w : EW) (f : FormW) :
    f.size ≤ (ts.foldl (fun acc t ↦ FormW.addTerm acc t.cols (w * t.coeff)) f).size := by
  induction ts generalizing f with
  | nil => exact Nat.le_refl _
  | cons t ts ih => exact Nat.le_trans (le_size_addTerm _ _ _) (ih _)

theorem zero_add (x : EW) : (0 : EW) + x = x := by
  show (⟨0 ^^^ x.c0, 0 ^^^ x.c1⟩ : EW) = x
  rw [UInt64.zero_xor, UInt64.zero_xor]

/-! ## Memory -/

/-- Bytes of a range that a change inside a sub-range of it misses. -/
theorem same_of_outside {d d' : Mem 64} {a : BitVec 64} {N o k o' k' : Nat}
    (hs : SameOutside d d' (InRange (a + BitVec.ofNat 64 o) k)) (hN : NoWrap a N)
    (hk : o + k ≤ N) (hk' : o' + k' ≤ N) (hd : o' + k' ≤ o ∨ o + k ≤ o') :
    Same d d' (a + BitVec.ofNat 64 o') k' :=
  Same.of_sameOutside hs fun j hj ↦ by
    rw [addr_add_add]; exact not_inRange_sub hN hk (by omega) (by omega)

/-- Bytes of a range that a change inside two sub-ranges of it misses. -/
theorem same_of_outside2 {d d' : Mem 64} {a : BitVec 64} {N o k o₂ k₂ o' k' : Nat}
    (hs : SameOutside d d' fun p ↦ InRange (a + BitVec.ofNat 64 o) k p ∨
      InRange (a + BitVec.ofNat 64 o₂) k₂ p) (hN : NoWrap a N)
    (hk : o + k ≤ N) (hk₂ : o₂ + k₂ ≤ N) (hk' : o' + k' ≤ N) (hd : o' + k' ≤ o ∨ o + k ≤ o')
    (hd₂ : o' + k' ≤ o₂ ∨ o₂ + k₂ ≤ o') : Same d d' (a + BitVec.ofNat 64 o') k' :=
  Same.of_sameOutside hs fun j hj ↦ by
    rw [addr_add_add]
    rintro (h | h)
    · exact not_inRange_sub hN hk (by omega) (by omega) h
    · exact not_inRange_sub hN hk₂ (by omega) (by omega) h

/-- A term over bytes that stayed the same. -/
theorem TermWAt.of_same {d d' : Mem 64} {a : BitVec 64} {t : TermW} (h : TermWAt d a t)
    (hs : Same d d' a termBytes) : TermWAt d' a t where
  degree_le := h.degree_le
  degree := WordAt.of_same h.degree hs (by decide)
  cols_lt := h.cols_lt
  cols i hi := WordAt.of_same (h.cols i hi) (hs.sub (o := 8 + 8 * i) (k := 8)
    (by have := h.degree_le; unfold termBytes; omega)) (Nat.le_refl _)
  coeff := EWAt.of_same h.coeff (hs.sub (o := 24) (k := 16) (by decide)) (Nat.le_refl _)

/-- Term `i` of a form's terms. -/
theorem term_addr (b : BitVec 64) (i : Nat) :
    off (off b 8) (termBytes * i) = b + BitVec.ofNat 64 (8 + 40 * i) := by
  simp only [off, termBytes]; rw [addr_add_add]

/-- A form over bytes that stayed the same. -/
theorem FormBufAt.of_same {d d' : Mem 64} {b : BitVec 64} {f : FormW} (h : FormBufAt d b f)
    (hs : Same d d' b formBufBytes) : FormBufAt d' b f := by
  have hle := h.len_le
  unfold formCap at hle
  refine ⟨h.len_le, WordAt.of_same h.len hs (by decide), fun i hi ↦ ?_⟩
  have ht := h.terms i hi
  rw [term_addr] at ht ⊢
  exact TermWAt.of_same ht (hs.sub (o := 8 + 40 * i) (k := termBytes)
    (by unfold termBytes formBufBytes formCap termBytes; omega))

/-- **A coefficient changed**: term `i` of a form, its other bytes and the form's other bytes
the same, its coefficient now `(g f[i]).coeff`. -/
theorem FormBufAt.modify {d d' : Mem 64} {b : BitVec 64} {f : FormW} {i : Nat} (hi : i < f.size)
    (h : FormBufAt d b f) (hN : NoWrap b formBufBytes) (g : TermW → TermW)
    (hg : (g f[i]).cols = f[i].cols)
    (hs : SameOutside d d' (InRange (b + BitVec.ofNat 64 (8 + 40 * i + 24)) 16))
    (hc : EWAt d' (b + BitVec.ofNat 64 (8 + 40 * i + 24)) (g f[i]).coeff) :
    FormBufAt d' b (f.modify i g) := by
  have hle := h.len_le
  unfold formCap at hle
  have hN' : NoWrap b 5928 := hN
  refine ⟨by rw [Array.size_modify]; exact h.len_le, ?_, fun j hj ↦ ?_⟩
  · rw [Array.size_modify]
    exact WordAt.of_same h.len (by
      have := same_of_outside (o' := 0) (k' := 8) hs hN' (by omega) (by omega) (by omega)
      rwa [NativeRustcVm.addr_add_zero] at this) (Nat.le_refl _)
  · rw [Array.size_modify] at hj
    rw [Array.getElem_modify, term_addr]
    have ht := h.terms j hj
    rw [term_addr] at ht
    by_cases hij : i = j
    · subst hij
      simp only [↓reduceIte]
      have hu := ht
      obtain ⟨hdl, hdeg, hcl, hcols, -⟩ := hu
      rw [← hg] at hdl hdeg hcl
      refine ⟨hdl, WordAt.of_same hdeg (same_of_outside (o' := 8 + 40 * i) (k' := 8) hs hN'
          (by omega) (by omega) (by omega)) (Nat.le_refl _), hcl, fun c hc' ↦ ?_, ?_⟩
      · have hc2 : c < f[i].cols.size := by rw [← hg]; exact hc'
        have hcw := hcols c hc2
        have e : (g f[i]).cols[c] = f[i].cols[c] := by simp [hg]
        rw [e]
        have hd2 : c < 2 := by have := h.terms i hi |>.degree_le; omega
        refine WordAt.of_same (n := 8) (by simp only [off] at hcw ⊢; rw [addr_add_add] at hcw ⊢; exact hcw) ?_
          (Nat.le_refl _)
        simp only [off]; rw [addr_add_add]
        exact same_of_outside hs hN' (by omega) (by omega) (by omega)
      · simp only [off]; rw [addr_add_add]; exact hc
    · simp only [hij, ↓reduceIte]
      exact TermWAt.of_same ht (same_of_outside hs hN' (by omega) (by unfold termBytes; omega)
        (by unfold termBytes; omega))

/-- **A term appended**: the count now `n + 1`, the terms before the same, the new one at `n`. -/
theorem FormBufAt.push {d d' : Mem 64} {b : BitVec 64} {f : FormW} {x : TermW}
    (h : FormBufAt d b f) (hn : f.size < formCap) (hN : NoWrap b formBufBytes)
    (hlen : WordAt d' b (f.size + 1).toUInt64)
    (hs : SameOutside d d' fun p ↦ InRange (b + BitVec.ofNat 64 0) 8 p ∨
      InRange (b + BitVec.ofNat 64 (8 + 40 * f.size)) 40 p)
    (hnew : TermWAt d' (b + BitVec.ofNat 64 (8 + 40 * f.size)) x) :
    FormBufAt d' b (f.push x) := by
  have hN' : NoWrap b 5928 := hN
  have hn' : f.size < 148 := hn
  refine ⟨by rw [Array.size_push]; exact hn, by rw [Array.size_push]; exact hlen, fun j hj ↦ ?_⟩
  rw [Array.size_push] at hj
  rw [term_addr]
  rcases Nat.lt_or_ge j f.size with hlt | hge
  · rw [Array.getElem_push_lt hlt]
    have ht := h.terms j hlt
    rw [term_addr] at ht
    exact TermWAt.of_same ht (same_of_outside2 hs hN' (by omega) (by omega)
      (by unfold termBytes; omega) (by unfold termBytes; omega) (by unfold termBytes; omega))
  · obtain rfl : j = f.size := by omega
    rw [Array.getElem_push_eq]
    exact hnew

/-! ## Columns -/

theorem toUInt64_inj {a b : Nat} (ha : a < 2 ^ 64) (hb : b < 2 ^ 64)
    (h : a.toUInt64 = b.toUInt64) : a = b := by
  have := congrArg UInt64.toNat h
  simp only [Nat.toUInt64, UInt64.toNat_ofNat'] at this
  rwa [Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] at this

/-- Columns equal word by word are equal. -/
theorem cols_eq_of_words {u t : TermW} (hs : u.cols.size = t.cols.size)
    (hu : ∀ j (h : j < u.cols.size), u.cols[j] < 2 ^ 64)
    (ht : ∀ j (h : j < t.cols.size), t.cols[j] < 2 ^ 64)
    (h : ∀ j (h : j < u.cols.size), u.cols[j].toUInt64 = (t.cols[j]'(hs ▸ h)).toUInt64) :
    u.cols = t.cols :=
  Array.ext hs fun j h1 h2 ↦ toUInt64_inj (hu j h1) (ht j h2) (h j h1)

/-! ## Where a block wrote -/

/-- Memory after a block is `env.mem0`'s outside `R`, when every write of the block is in `R`. -/
theorem Match.sameOutside_of [Labels] {env : Env} {S : SState} {m : MachineData}
    (hm : Match env S m) (hwf : env.WF) (R : BitVec 64 → Prop)
    (hR : ∀ p, Written env S p → R p) : SameOutside env.mem0 m.dmem R :=
  fun _ hp ↦ hm.get?_mem0 hwf fun hw ↦ hp (hR _ hw)

/-- A write at offsets `o' ≤ o < o' + n'` of a region is in its sub-range `o, k` when inside it. -/
theorem inRange_of_written {b p : BitVec 64} {sz o k off n : Nat} (hnw : b.toNat + sz ≤ 2 ^ 64)
    (hk : o + k ≤ sz) (h1 : b.toNat + off ≤ p.toNat) (h2 : p.toNat < b.toNat + off + n)
    (ho : o ≤ off) (hn : off + n ≤ o + k) : InRange (b + BitVec.ofNat 64 o) k p := by
  have hk0 : 0 < k := by omega
  have e := toNat_add_ofNat (a := b) (i := o) (by omega)
  rw [Sym.inRange_iff (by rw [e]; omega), e]
  omega

end

end NativeRustcVmArm.Layout.Forms
