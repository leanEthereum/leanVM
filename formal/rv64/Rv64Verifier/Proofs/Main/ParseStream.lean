import Rv64Verifier.Proofs.Main.ParseCall

/-!
# The stream

`0x80000aac` reads the stream's length `n` and allocates its buffer (`try_allocate_in`, 24-byte
elements); `0x80000b10` copies the scalars, three words at a time, aborting when fewer than three
are left (`stream_body`, `stream_loop`); `0x80000b4c` (or `0x80000e0c` for an empty stream) aborts
unless a word is left (`stream_stage`, to `AtB58`).
-/

namespace Rv64Verifier.Proofs.Main
open RiscvZkvm.Rv64 LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.Compile Rv64Verifier.Runtime
  Rv64Verifier.Proofs.Bytecode Rv64Verifier.Proofs.End Rv64Verifier.Blocks.F3

theorem PG.word {s u₀ t : MachineState} {words : List Word} (h0 : ParseA s words u₀)
    (hg : PG u₀ t) {a : Word} {j : Nat} (hj : j < words.length)
    (ha : a = inputBase + BitVec.ofNat 64 (8 * j)) : t.getMem a = words[j] := by
  subst ha; exact (hg.minv h0).input j hj

theorem getD_drop {words : List Word} {j i : Nat} (h : j + i < words.length) :
    (words.drop j).getD i 0 = words[j + i] := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_drop, List.getElem?_eq_getElem h]
  rfl

theorem ofNat_toNat' (w : Word) : BitVec.ofNat 64 w.toNat = w := by simp

theorem input_mapped {words : List Word} (hf : words.length ≤ inputWords) :
    Mapped inputBase (8 * words.length) := by
  have hib : inputBase.toNat = 0x10000000 := rfl
  simp only [Mapped, hib]
  simp only [inputWords] at hf
  omega

/-- A step that writes only heap from `NEXT` at `u₀` on, below `NEXT`. -/
theorem PG.heapWrite {u₀ t t' : MachineState} (hg : PG u₀ t) {lo : Word} {m : Nat}
    (hfr : MemFrame t t' lo m) (hlo : lo.toNat % 8 = 0) (hm : m % 8 = 0) (h1 : heapNext u₀ ≤ lo.toNat)
    (h2 : lo.toNat + m ≤ heapNext t) (hsp : t'.getReg .x2 = msp) : PG u₀ t' := by
  have hhi := hg.heap.hi
  simp only [heapNext, heapEnd] at hhi h2
  have hn : heapNext t' = heapNext t := by
    simp only [heapNext]; rw [hfr _ (by addr_omega [h2, hhi])]
  exact hg.step (BFrame.of_memFrame hfr hlo hm)
    (fun a ha ↦ Wf.heap (by simp only [Within] at ha; omega)
      (by simp only [Within, heapEnd] at ha ⊢; omega))
    hsp ⟨by rw [hn]; exact hg.heap.lo, by rw [hn]; exact hg.heap.hi⟩ (le_of_eq hn.symm) (Or.inl hn)

/-- A step that writes only `main`'s scratch slots. -/
theorem PG.slotWrite {u₀ t t' : MachineState} (hg : PG u₀ t) {c m : Nat}
    (hfr : MemFrame t t' (msp + BitVec.ofNat 64 c) m)
    (hc : c % 8 = 0) (hm : m % 8 = 0) (h1 : 24 ≤ c) (h2 : c + m ≤ 104) (hsp : t'.getReg .x2 = msp) :
    PG u₀ t' := by
  have hn : heapNext t' = heapNext t := by
    simp only [heapNext]; rw [hfr _ (by addr_omega [h1, h2])]
  exact hg.step (BFrame.of_memFrame hfr (by addr_omega [hc, h1, h2]) hm)
    (fun a ha ↦ Wf.slot (by addr_omega [ha, h1, h2]))
    hsp ⟨by rw [hn]; exact hg.heap.lo, by rw [hn]; exact hg.heap.hi⟩ (le_of_eq hn.symm) (Or.inl hn)

theorem eListAt_snoc {t t' : MachineState} {S : Word} {c : Nat}
    (hf : MemFrame t t' (S + BitVec.ofNat 64 (24 * c)) 24) (hS : S.toNat + 24 * (c + 1) ≤ 2 ^ 64) :
    eListAt t' S (c + 1) = eListAt t S c ++ [eAt t' (S + BitVec.ofNat 64 (24 * c))] := by
  unfold eListAt
  rw [List.range_succ, List.map_append]
  congr 1
  apply List.map_congr_left
  intro i hi
  simp only [List.mem_range] at hi
  exact hf.eAt (by addr_omega [hi, hS]) (by addr_omega [hi, hS])

/-! ## The copy loop -/

/-- At `0x80000b10`, `c` of the stream's `nw` scalars copied to `S`; `k0` words were read before
the stream's length, `X` is `a0` (the words left after the stream, less one). -/
structure SLoop (u₀ : MachineState) (words : List Word) (k0 : Nat) (nw S X : Word)
    (t : MachineState) (c : Nat) : Prop where
  pg : PG u₀ t
  pc : t.pc = 0x80000b10
  lt : c < nw.toNat
  room : k0 + 1 + 3 * c ≤ words.length
  x7 : t.getReg .x7 = S
  x10 : t.getReg .x10 = X
  x11 : t.getReg .x11 = inputBase + BitVec.ofNat 64 (8 * (k0 + 1 + 3 * c))
  x12 : t.getReg .x12 = BitVec.ofNat 64 (words.length - (k0 + 1 + 3 * c))
  x13 : t.getReg .x13 = S + BitVec.ofNat 64 (24 * c + 16)
  x14 : t.getReg .x14 = 2
  x15 : t.getReg .x15 = 1
  x16 : t.getReg .x16 = BitVec.ofNat 64 (nw.toNat - c)
  x18 : t.getReg .x18 = nw
  read : (rep readScalar c).run (words.drop (k0 + 1)) =
    some (eListAt t S c, words.drop (k0 + 1 + 3 * c))
  buf : S.toNat % 8 = 0 ∧ heapNext u₀ ≤ S.toNat ∧ S.toNat + 24 * nw.toNat ≤ heapNext t

/-- At `0x80000b4c`, the stream copied. -/
structure SEnd (u₀ : MachineState) (words : List Word) (k0 : Nat) (nw S X : Word)
    (t : MachineState) : Prop where
  pg : PG u₀ t
  pc : t.pc = 0x80000b4c
  room : k0 + 1 + 3 * nw.toNat ≤ words.length
  x7 : t.getReg .x7 = S
  x10 : t.getReg .x10 = X
  x17 : t.getReg .x17 = inputBase + BitVec.ofNat 64 (8 * (k0 + 1 + 3 * nw.toNat))
  x18 : t.getReg .x18 = nw
  read : (rep readScalar nw.toNat).run (words.drop (k0 + 1)) =
    some (eListAt t S nw.toNat, words.drop (k0 + 1 + 3 * nw.toNat))
  buf : S.toNat % 8 = 0 ∧ heapNext u₀ ≤ S.toNat ∧ S.toNat + 24 * nw.toNat ≤ heapNext t

section
variable {s u₀ : MachineState} {words : List Word}

/-- One scalar. -/
theorem stream_body (h0 : ParseA s words u₀) {t : MachineState} {k0 c : Nat} {nw S X : Word}
    (h : SLoop u₀ words k0 nw S X t c) :
    ∃ v, Reaches Image.code t v ∧ (Dead Image.code v ∨ SLoop u₀ words k0 nw S X v (c + 1) ∨
      SEnd u₀ words k0 nw S X v) := by
  have hg := h.pg
  have hsp := hg.sp
  have hfit := h0.inv.fits
  simp only [inputWords] at hfit
  have hib : inputBase.toNat = 0x10000000 := rfl
  have hhi := hg.heap.hi
  simp only [heapNext, heapEnd] at hhi
  obtain ⟨hS8, hS0, hSn⟩ := h.buf
  simp only [heapNext] at hS0 hSn
  have hlt := h.lt
  have hroom := h.room
  set j := k0 + 1 + 3 * c with hj
  -- the three checks
  obtain ⟨t₁, r₁, h₁⟩ := Sym.BlockSpec.reaches b80000b10_spec h.pc trivial
  by_cases c2 : t.getReg .x12 = t.getReg .x14
  · obtain ⟨w, hw, hd⟩ := abort (u := t₁) (by rw [b80000b10_pc_taken h₁ c2]; decide)
    exact ⟨w, r₁.trans hw, Or.inl hd⟩
  have k₁ := b80000b10_keeps h₁
  obtain ⟨t₂, r₂, h₂⟩ := Sym.BlockSpec.reaches b80000b14_spec (b80000b10_pc_not_taken h₁ c2) trivial
  have k₂ := b80000b14_keeps h₂
  by_cases c1 : t₁.getReg .x12 = t₁.getReg .x15
  · obtain ⟨w, hw, hd⟩ := abort (u := t₂) (by rw [b80000b14_pc_taken h₂ c1]; decide)
    exact ⟨w, r₁.trans (r₂.trans hw), Or.inl hd⟩
  obtain ⟨t₃, r₃, h₃⟩ := Sym.BlockSpec.reaches b80000b18_spec (b80000b14_pc_not_taken h₂ c1) trivial
  have k₃ := b80000b18_keeps h₃
  by_cases c0 : t₂.getReg .x12 = 0
  · obtain ⟨w, hw, hd⟩ := abort (u := t₃) (by rw [b80000b18_pc_taken h₃ c0]; decide)
    exact ⟨w, r₁.trans (r₂.trans (r₃.trans hw)), Or.inl hd⟩
  have pc₃ := b80000b18_pc_not_taken h₃ c0
  have R : ∀ r ∈ ([.x2, .x7, .x10, .x11, .x12, .x13, .x14, .x15, .x16, .x18] : List Reg),
      t₃.getReg r = t.getReg r := by
    intro r hr
    rw [k₃ r (mem_of_mem hr _), k₂ r (mem_of_mem hr _), k₁ r (mem_of_mem hr _)]
  have m₃ : ∀ a, t₃.getMem a = t.getMem a := fun a ↦ by
    rw [b80000b18_mem_same h₃, b80000b14_mem_same h₂, b80000b10_mem_same h₁]
  rw [k₂ .x12 (by decide), k₁ .x12 (by decide)] at c0
  rw [k₁ .x12 (by decide), k₁ .x15 (by decide)] at c1
  rw [h.x12] at c0 c1 c2
  rw [h.x14] at c2
  rw [h.x15] at c1
  have h3 : j + 3 ≤ words.length := by
    by_contra hc
    rcases (by omega : words.length - j = 0 ∨ words.length - j = 1 ∨ words.length - j = 2)
      with e | e | e <;> rw [e] at c0 c1 c2
    · exact c0 rfl
    · exact c1 rfl
    · exact c2 rfl
  -- the copy
  have e11 : t₃.getReg .x11 = inputBase + BitVec.ofNat 64 (8 * j) := by
    rw [R .x11 (by decide), h.x11]
  have e13 : t₃.getReg .x13 = S + BitVec.ofNat 64 (24 * c + 16) := by
    rw [R .x13 (by decide), h.x13]
  have hin := input_mapped (words := words) (by simp only [inputWords]; exact hfit)
  have hlo0 := h0.inv.heap.lo
  simp only [heapStart, heapNext] at hlo0
  have hSm : Mapped S (24 * nw.toNat) := by simp only [Mapped]; omega
  obtain ⟨t₄, r₄, h₄⟩ := Sym.BlockSpec.reaches b80000b1c_spec pc₃ (by
    rv_eval [e11, e13]
    and_intros <;> first
      | valid_in hSm [hS8, hlt, hSn, hhi]
      | valid_in hin [hib, h3, hfit])
  have k₄ := b80000b1c_keeps h₄
  have hfr₄ := b80000b1c_frame h₄ (by rw [e13]; constructor <;> addr_omega [hlt, hSn, hhi])
  have hlo : t₃.getReg .x13 - 16 = S + BitVec.ofNat 64 (24 * c) := by
    rw [e13]; addr_omega [hlt, hSn, hhi]
  rw [hlo] at hfr₄
  have hfr : MemFrame t t₄ (S + BitVec.ofNat 64 (24 * c)) 24 := fun a ha ↦ by
    rw [hfr₄ a ha, m₃]
  have hsp₄ : t₄.getReg .x2 = msp := by rw [k₄ .x2 (by decide), R .x2 (by decide), hsp]
  have hg₄ : PG u₀ t₄ := hg.heapWrite hfr (by addr_omega [hS8, hlt, hSn, hhi]) (by decide)
    (by addr_omega [hS0, hlt, hSn, hhi]) (by simp only [heapNext]; addr_omega [hlt, hSn, hhi]) hsp₄
  have hg₃ : PG u₀ t₃ := hg.same m₃ (by rw [R .x2 (by decide), hsp])
  have w0 : t₄.getMem (S + BitVec.ofNat 64 (24 * c)) = words[j] := by
    have e := b80000b1c_m_x13_n16 h₄
    rw [hlo, e11] at e
    rw [e, hg₃.word h0 (j := j) (by omega) rfl]
  have w8 : t₄.getMem (S + BitVec.ofNat 64 (24 * c) + 8) = words[j + 1] := by
    have e := b80000b1c_m_x13_n8 h₄
    rw [show t₃.getReg .x13 - 8 = S + BitVec.ofNat 64 (24 * c) + 8 by
      rw [e13]; addr_omega [hlt, hSn, hhi], e11] at e
    rw [e, hg₃.word h0 (j := j + 1) (by omega) (by addr_omega [hib, h3, hfit])]
  have w16 : t₄.getMem (S + BitVec.ofNat 64 (24 * c) + 16) = words[j + 2] := by
    have e := b80000b1c_m_x13_0 h₄
    rw [show t₃.getReg .x13 = S + BitVec.ofNat 64 (24 * c) + 16 by
      rw [e13]; addr_omega [hlt, hSn, hhi], e11] at e
    rw [e, hg₃.word h0 (j := j + 2) (by omega) (by addr_omega [hib, h3, hfit])]
  have hE : eAt t₄ (S + BitVec.ofNat 64 (24 * c)) = scalarOfWords (words.drop j) := by
    unfold eAt scalarOfWords
    rw [w0, w8, w16, getD_drop (by omega), getD_drop (by omega), getD_drop (by omega)]
    rfl
  have hval : eListAt t₄ S (c + 1) = eListAt t S c ++ [scalarOfWords (words.drop j)] := by
    rw [eListAt_snoc hfr (by omega), hE]
  have hread : (rep readScalar (c + 1)).run (words.drop (k0 + 1)) =
      some (eListAt t₄ S (c + 1), words.drop (k0 + 1 + 3 * (c + 1))) := by
    rw [rep_step h.read (readScalar_run (by simp only [List.length_drop]; omega)), hval,
      List.drop_drop]
    congr 3
  have hnx : heapNext t₄ = heapNext t := by
    simp only [heapNext]; rw [hfr _ (by addr_omega [hlt, hSn, hhi])]
  have hbuf : S.toNat % 8 = 0 ∧ heapNext u₀ ≤ S.toNat ∧ S.toNat + 24 * nw.toNat ≤ heapNext t₄ := by
    rw [hnx]; exact ⟨hS8, hS0, hSn⟩
  have x16 := b80000b1c_x16 h₄
  rw [R .x16 (by decide), h.x16] at x16
  have r : Reaches Image.code t t₄ := r₁.trans (r₂.trans (r₃.trans r₄))
  by_cases hc : c + 1 = nw.toNat
  · have pc₄ := b80000b1c_pc_not_taken h₄ (by
      rw [R .x16 (by decide), h.x16, show nw.toNat - c = 1 by omega]; rfl)
    refine ⟨t₄, r, Or.inr (Or.inr ⟨hg₄, pc₄, by omega, ?_, ?_, ?_, ?_, ?_, hbuf⟩)⟩
    · rw [k₄ .x7 (by decide), R .x7 (by decide), h.x7]
    · rw [k₄ .x10 (by decide), R .x10 (by decide), h.x10]
    · rw [b80000b1c_x17 h₄, e11]; addr_omega [hib, h3, hfit, hc]
    · rw [k₄ .x18 (by decide), R .x18 (by decide), h.x18]
    · rw [← hc]; exact hread
  · have pc₄ := b80000b1c_pc_taken h₄ (by
      rw [R .x16 (by decide), h.x16]; addr_omega [hlt, hc, hSn, hhi])
    refine ⟨t₄, r, Or.inr (Or.inl ⟨hg₄, pc₄, by omega, by omega, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
      ?_, hread, hbuf⟩)⟩
    · rw [k₄ .x7 (by decide), R .x7 (by decide), h.x7]
    · rw [k₄ .x10 (by decide), R .x10 (by decide), h.x10]
    · rw [b80000b1c_x11 h₄, e11]; addr_omega [hib, h3, hfit]
    · rw [b80000b1c_x12 h₄, R .x12 (by decide), h.x12]; addr_omega [h3, hfit]
    · rw [b80000b1c_x13 h₄, e13]; addr_omega [hlt, hc, hSn, hhi]
    · rw [k₄ .x14 (by decide), R .x14 (by decide), h.x14]
    · rw [k₄ .x15 (by decide), R .x15 (by decide), h.x15]
    · rw [x16]; addr_omega [hlt, hc, hSn, hhi]
    · rw [k₄ .x18 (by decide), R .x18 (by decide), h.x18]

/-- The copy loop. -/
theorem stream_loop (h0 : ParseA s words u₀) {t : MachineState} {k0 : Nat} {nw S X : Word}
    (h : SLoop u₀ words k0 nw S X t 0) :
    ∃ v, Reaches Image.code t v ∧ (Dead Image.code v ∨ SEnd u₀ words k0 nw S X v) := by
  refine Reaches.loop (fun t ↦ ∃ c, SLoop u₀ words k0 nw S X t c)
    (fun t ↦ (t.getReg .x16).toNat) _ ?_ t ⟨0, h⟩
  rintro t ⟨c, hc⟩
  obtain ⟨v, hv, hd | hl | he⟩ := stream_body h0 hc
  · exact Or.inl ⟨v, hv, Or.inl hd⟩
  · refine Or.inr ⟨v, hv, ⟨c + 1, hl⟩, ?_⟩
    have b := hc.buf.2.2
    have hhi := hc.pg.heap.hi
    simp only [heapNext, heapEnd] at b hhi
    rw [hl.x16, hc.x16, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
    have := hl.lt
    omega
  · exact Or.inl ⟨v, hv, Or.inr he⟩

end

end Rv64Verifier.Proofs.Main
