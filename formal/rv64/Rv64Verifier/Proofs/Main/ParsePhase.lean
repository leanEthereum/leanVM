import Rv64Verifier.Proofs.Main.ParsePaths

/-!
# A phase, to its paths' end

At `0x80000be8` (`PhS`, phase `i` of `np`): `0x80000bf0` reads the phase's path count and allocates
its buffer (`try_allocate_in`, 56-byte elements), `0x80000c28` saves the counter, then the paths'
loop (`path_loop`), to `0x80000bb0` (`phase_head`, to `AtBB0`).
-/

namespace Rv64Verifier.Proofs.Main
open RiscvZkvm.Rv64 LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.Compile Rv64Verifier.Runtime
  Rv64Verifier.Proofs.Bytecode Rv64Verifier.Proofs.End Rv64Verifier.Blocks.F3

/-- At `0x80000be8`, phase `i` of `np`: the stream (`n` scalars at `S`) and the openings' buffer
`O` in place, `rep (readList readOpening) i` read from word `k1` to `k`, each phase held at
`O + 24 i'` with its buffers past `O`'s. -/
structure PhS (u₀ : MachineState) (words : List Word) (k1 : Nat) (S O : Word) (stream : List E)
    (np B1 : Nat) (t : MachineState) (i k : Nat) (phs : List (List Opening)) : Prop where
  pg : PG u₀ t
  pc : t.pc = 0x80000be8
  lt : i < np
  x8 : t.getReg .x8 = BitVec.ofNat 64 i
  s32 : t.getMem (msp + 32) = BitVec.ofNat 64 stream.length
  s40 : t.getMem (msp + 40) = S
  s56 : t.getMem (msp + 56) = BitVec.ofNat 64 np
  s64 : t.getMem (msp + 64) = O
  room : k ≤ words.length
  ptr : t.getMem (msp + 88) = inputBase + BitVec.ofNat 64 (8 * k)
  rest : (t.getMem (msp + 96)).toNat = words.length - k
  oread : (rep (readList readOpening) i).run (words.drop k1) = some (phs, words.drop k)
  sval : eListAt t S stream.length = stream
  sbuf : InR S (24 * stream.length) 8 (heapNext u₀) B1
  b1 : heapNext u₀ ≤ B1
  obuf : O.toNat % 8 = 0 ∧ B1 ≤ O.toNat ∧ O.toNat + 24 * np ≤ heapNext t
  phases : ∀ i' (h : i' < phs.length), PhaseIn t (O + BitVec.ofNat 64 (24 * i')) phs[i']
    (O.toNat + 24 * np) (heapNext t)

/-- At `0x80000d88`, the openings read: `np` phases from word `k1` to `k`. -/
structure AtD88 (u₀ : MachineState) (words : List Word) (k1 : Nat) (S O : Word) (stream : List E)
    (np B1 : Nat) (t : MachineState) (k : Nat) (phs : List (List Opening)) : Prop where
  pg : PG u₀ t
  pc : t.pc = 0x80000d88
  x8 : t.getReg .x8 = BitVec.ofNat 64 (words.length - k)
  x9 : t.getReg .x9 = BitVec.ofNat 64 np
  x18 : t.getReg .x18 = BitVec.ofNat 64 stream.length
  s40 : t.getMem (msp + 40) = S
  s64 : t.getMem (msp + 64) = O
  room : k ≤ words.length
  oread : (rep (readList readOpening) np).run (words.drop k1) = some (phs, words.drop k)
  sval : eListAt t S stream.length = stream
  sbuf : InR S (24 * stream.length) 8 (heapNext u₀) B1
  b1 : heapNext u₀ ≤ B1
  b1hi : B1 ≤ heapNext t
  obuf : InR O (24 * np) 8 B1 (heapNext t)
  phases : ∀ i' (h : i' < phs.length), PhaseIn t (O + BitVec.ofNat 64 (24 * i')) phs[i']
    (O.toNat + 24 * np) (heapNext t)

/-- At `0x80000bb0`, phase `i`'s `npi` paths read (`ops`) into the buffer at `P`, from word `k`
to `kj`; `t₀` where the phase started. -/
structure AtBB0 (u₀ : MachineState) (words : List Word) (O : Word) (i k : Nat) (t₀ : MachineState)
    (P : Word) (npi kj : Nat) (ops : List Opening) (b : MachineState) : Prop where
  pg : PG u₀ b
  pc : b.pc = 0x80000bb0
  x18 : b.getReg .x18 = BitVec.ofNat 64 npi
  x23 : b.getReg .x23 = P
  slots : ∀ c : Nat, c % 8 = 0 → 24 ≤ c → c + 8 ≤ 72 →
    b.getMem (msp + BitVec.ofNat 64 c) = t₀.getMem (msp + BitVec.ofNat 64 c)
  s80 : b.getMem (msp + 80) = BitVec.ofNat 64 i
  room : kj ≤ words.length
  ptr : b.getMem (msp + 88) = inputBase + BitVec.ofNat 64 (8 * kj)
  rest : (b.getMem (msp + 96)).toNat = words.length - kj
  read : (readList readOpening).run (words.drop k) = some (ops, words.drop kj)
  len : ops.length = npi
  paths : ∀ j (h : j < ops.length),
    PathIn b (P + BitVec.ofNat 64 (56 * j)) ops[j] (P.toNat + 56 * npi) (heapNext b)
  pbuf : P.toNat % 8 = 0 ∧ (npi = 0 ∨ heapNext t₀ ≤ P.toNat ∧ P.toNat + 56 * npi ≤ heapNext b)
  frame : BFrame t₀ b (Wph (heapNext t₀) (O + BitVec.ofNat 64 (24 * i)))
  mono : heapNext t₀ ≤ heapNext b

theorem toNat_56 : (56 : Word).toNat = 56 := rfl

theorem Wph.of_wc {B B' : Nat} {q a : Word} (hB : B ≤ B') (h : Wc B' a) : Wph B q a := by
  rcases h with h | h | h | h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr (Or.inl h))
  · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨le_trans hB h.1, h.2⟩))))

section
variable {s u₀ t : MachineState} {words : List Word}

/-- **A phase, to its paths' end.** -/
theorem phase_head (h0 : ParseA s words u₀) {k1 : Nat} {S O : Word} {stream : List E} {np B1 i k : Nat}
    {phs : List (List Opening)} (h : PhS u₀ words k1 S O stream np B1 t i k phs) :
    ∃ v, Reaches Image.code t v ∧ (Dead Image.code v ∨
      ∃ P npi kj ops, AtBB0 u₀ words O i k t P npi kj ops v) := by
  have hg := h.pg
  have hsp := hg.sp
  have hfit := h0.inv.fits
  simp only [inputWords] at hfit
  have hib : inputBase.toNat = 0x10000000 := rfl
  have hhi := hg.heap.hi
  simp only [heapNext, heapEnd] at hhi
  have hin := input_mapped (words := words) (by simp only [inputWords]; exact hfit)
  have hrest := h.rest
  -- `0x80000be8`: a word left
  obtain ⟨t₁, r₁, h₁⟩ := Sym.BlockSpec.reaches b80000be8_spec h.pc (by rv_eval [hsp, msp]; decide)
  by_cases z : t.getMem (t.getReg .x2 + 96) = 0
  · obtain ⟨w, hw, hd⟩ := abort (u := t₁) (by rw [b80000be8_pc_taken h₁ z]; decide)
    exact ⟨w, r₁.trans hw, Or.inl hd⟩
  have hk : k < words.length := by
    rw [hsp] at z
    by_contra hc
    exact z (BitVec.eq_of_toNat_eq (by rw [hrest]; simp; omega))
  have k₁ := b80000be8_keeps h₁
  have m₁ := b80000be8_mem_same h₁
  have hsp₁ : t₁.getReg .x2 = msp := by rw [k₁ .x2 (by decide), hsp]
  have x10₁ : t₁.getReg .x10 = BitVec.ofNat 64 (words.length - k) := by
    rw [b80000be8_x10 h₁, hsp]
    apply BitVec.eq_of_toNat_eq
    rw [hrest, BitVec.toNat_ofNat]
    omega
  have g88 : t₁.getMem (msp + 88) = inputBase + BitVec.ofNat 64 (8 * k) := by rw [m₁, h.ptr]
  have hg₁ : PG u₀ t₁ := hg.same m₁ hsp₁
  -- `0x80000bf0`: the path count, `try_allocate_in`
  obtain ⟨t₂, r₂, h₂⟩ := Sym.BlockSpec.reaches b80000bf0_spec (b80000be8_pc_not_taken h₁ z) (by
    rv_eval [hsp₁, g88]
    and_intros <;> first
      | decide
      | valid_in hin [hib, hk, hfit])
  have k₂ := b80000bf0_keeps h₂
  have hsp₂ : t₂.getReg .x2 = msp := by rw [k₂ .x2 (by decide), hsp₁]
  have hfr₂ := b80000bf0_frame h₂ (by rw [hsp₁]; decide)
  rw [hsp₁] at hfr₂
  have hg₂ : PG u₀ t₂ := hg₁.slotWrite (c := 88) hfr₂ (by decide) (by decide) (by decide)
    (by decide) hsp₂
  have hn₂ : heapNext t₂ = heapNext t := by
    simp only [heapNext]; rw [hfr₂ _ (by addr_omega []), m₁]
  set npw := words[k] with hnpw
  set npi := npw.toNat with hnpi
  have x18₂ : t₂.getReg .x18 = npw := by
    rw [b80000bf0_x18 h₂, hsp₁, g88]; exact hg₁.word h0 hk rfl
  have p88 : t₂.getMem (msp + 88) = inputBase + BitVec.ofNat 64 (8 * (k + 1)) := by
    have e := b80000bf0_m_x2_88 h₂
    rw [hsp₁, g88] at e
    rw [e]; addr_omega [hib, hk, hfit]
  have p96 : t₂.getMem (msp + 96) = BitVec.ofNat 64 (words.length - (k + 1)) := by
    have e := b80000bf0_m_x2_96 h₂
    rw [hsp₁, x10₁] at e
    rw [e]; addr_omega [hk, hfit]
  obtain ⟨w, rw', hd | ⟨pcw, regw, hgw, hfw, hmw, -, bufw⟩⟩ := alloc_call hg₂ (b80000bf0_pc h₂)
    (by rw [b80000bf0_x10 h₂, hsp₁]) (by rw [b80000bf0_x12 h₂]; decide)
    (by rw [b80000bf0_x13 h₂]; decide) (by rw [returnAddress, b80000bf0_x1 h₂]; decide)
    b80000c20_spec (fun v hv ↦ by rv_eval [hv]; decide)
    (fun _ _ h hc ↦ b80000c20_pc_taken h hc) (fun _ _ h hc ↦ b80000c20_pc_not_taken h hc)
    (fun _ _ h ↦ b80000c20_mem_same h) (fun _ _ h r hr ↦ b80000c20_keeps h r (mem_of_calleeSaved hr _))
  · exact ⟨w, r₁.trans (r₂.trans rw'), Or.inl hd⟩
  have hspw : w.getReg .x2 = msp := by rw [regw .x2 (by decide), hsp₂]
  rw [b80000bf0_x11 h₂, hsp₁, g88, hg₁.word h0 hk rfl, b80000bf0_x13 h₂, b80000bf0_x12 h₂,
    ← hnpw, ← hnpi] at bufw
  set P := w.getMem (msp + 336) with hP
  have hww := hgw.heap.hi
  simp only [heapNext, heapEnd] at hww
  have hPb : 56 * npi = 0 ∨ heapNext t ≤ P.toNat ∧ P.toNat + 56 * npi ≤ heapNext w := by
    rcases bufw.2 with h' | h'
    · left; rw [toNat_56] at h'; omega
    · right; rw [toNat_56, hn₂] at h'; exact ⟨h'.1, by omega⟩
  have hP8 : P.toNat % 8 = 0 := bufw.1
  -- `0x80000c28`: the counter saved
  obtain ⟨t₄, r₄, h₄⟩ := Sym.BlockSpec.reaches b80000c28_spec pcw (by rv_eval [hspw, msp]; decide)
  have k₄ := b80000c28_keeps h₄
  have hsp₄ : t₄.getReg .x2 = msp := by rw [k₄ .x2 (by decide), hspw]
  have hfr₄ := b80000c28_frame h₄ (by rw [hspw]; decide)
  rw [hspw] at hfr₄
  have hg₄ : PG u₀ t₄ := hgw.slotWrite (c := 72) hfr₄ (by decide) (by decide) (by decide)
    (by decide) hsp₄
  have hn₄ : heapNext t₄ = heapNext w := by
    simp only [heapNext]; rw [hfr₄ _ (by addr_omega [])]
  have x23₄ : t₄.getReg .x23 = P := by rw [b80000c28_x23 h₄, hspw]
  have x18₄ : t₄.getReg .x18 = npw := by rw [k₄ .x18 (by decide), regw .x18 (by decide), x18₂]
  have s80 : t₄.getMem (msp + 80) = BitVec.ofNat 64 i := by
    have e := b80000c28_m_x2_80 h₄
    rw [hspw, regw .x8 (by decide), k₂ .x8 (by decide), k₁ .x8 (by decide), h.x8] at e
    exact e
  -- the frame so far
  have hfr : BFrame t t₄ (Wph (heapNext t) (O + BitVec.ofNat 64 (24 * i))) := by
    have b1 : BFrame t t₂ (Wph (heapNext t) (O + BitVec.ofNat 64 (24 * i))) :=
      (BFrame.of_same m₁ _).trans (BFrame.of_memFrame hfr₂ (by decide) (by decide))
        fun a ha ↦ Or.inl (by addr_omega [ha])
    have b2 := b1.trans hfw fun a ha ↦ Wph.of_wc (le_of_eq hn₂.symm) ha
    exact b2.trans (BFrame.of_memFrame hfr₄ (by decide) (by decide))
      fun a ha ↦ Or.inl (by addr_omega [ha])
  have slots₄ : ∀ c : Nat, c % 8 = 0 → 24 ≤ c → c + 8 ≤ 72 →
      t₄.getMem (msp + BitVec.ofNat 64 c) = t.getMem (msp + BitVec.ofNat 64 c) := by
    intro c h8 h1 h2
    rw [hfr₄ _ (by addr_omega [h1, h2]), Wc.keep hfw (by addr_omega [h8, h1, h2])
      (by addr_omega [h1, h2]) (by addr_omega [h1, h2]), hfr₂ _ (by addr_omega [h1, h2]), m₁]
  have k88 : t₄.getMem (msp + 88) = t₂.getMem (msp + 88) := by
    rw [hfr₄ _ (by addr_omega []), Wc.keep hfw (by decide) (by decide) (by decide)]
  have k96 : t₄.getMem (msp + 96) = t₂.getMem (msp + 96) := by
    rw [hfr₄ _ (by addr_omega []), Wc.keep hfw (by decide) (by decide) (by decide)]
  have hread0 : (readList readOpening).run (words.drop k) =
      (rep readOpening npi).run (words.drop (k + 1)) := by
    rw [drop_cons hk, readList_run]
  have r : Reaches Image.code t t₄ := r₁.trans (r₂.trans (rw'.trans r₄))
  have hmono₄ : heapNext t ≤ heapNext t₄ := by rw [hn₄, ← hn₂]; exact hmw
  by_cases hz : w.getReg .x18 = 0
  · -- no paths
    have hz' : npi = 0 := by
      rw [regw .x18 (by decide), x18₂] at hz; rw [hnpi, hz]; rfl
    refine ⟨t₄, r, Or.inr ⟨P, npi, k + 1, [], ⟨hg₄, b80000c28_pc_taken h₄ hz, ?_, x23₄, slots₄, s80,
      by omega, by rw [k88, p88], by rw [k96, p96, BitVec.toNat_ofNat]; omega, ?_, ?_,
      fun j hj ↦ absurd hj (by simp), ⟨hP8, Or.inl hz'⟩, hfr, hmono₄⟩⟩⟩
    · rw [x18₄, ofNat_toNat']
    · rw [hread0, hz']; rfl
    · rw [hz']; rfl
  -- the paths
  have hpos : 0 < npi := by
    rcases Nat.eq_zero_or_pos npi with h' | h'
    · exfalso
      apply hz
      rw [regw .x18 (by decide), x18₂]
      exact BitVec.eq_of_toNat_eq (by rw [← hnpi, h']; rfl)
    · exact h'
  have hPb' : heapNext t ≤ P.toNat ∧ P.toNat + 56 * npi ≤ heapNext w := hPb.resolve_left (by omega)
  obtain ⟨t₅, r₅, h₅⟩ := Sym.BlockSpec.reaches b80000c3c_spec (b80000c28_pc_not_taken h₄ hz) trivial
  have k₅ := b80000c3c_keeps h₅
  have m₅ := b80000c3c_mem_same h₅
  have hsp₅ : t₅.getReg .x2 = msp := by rw [k₅ .x2 (by decide), hsp₄]
  have hn₅ : heapNext t₅ = heapNext w := by simp only [heapNext, m₅]; exact hn₄
  have hI : PaI u₀ words P npi (k + 1) t t₅ (O + BitVec.ofNat 64 (24 * i)) 0x80000c7c t₅ 0 (k + 1) [] :=
    { pas := { pg := hg₄.same m₅ hsp₅
               pc := b80000c3c_pc h₅
               x18 := by rw [k₅ .x18 (by decide), x18₄, ofNat_toNat']
               x23 := by rw [k₅ .x23 (by decide), x23₄]
               x24 := by rw [b80000c3c_x24 h₅]; rfl
               room := by omega
               ptr := by rw [m₅, k88, p88]
               rest := by rw [m₅, k96, p96, BitVec.toNat_ofNat]; omega
               buf := ⟨hP8, by have := hg.mono; simp only [heapNext] at this hPb' ⊢; omega,
                 by rw [hn₅]; exact hPb'.2⟩ }
      read := by rw [rep_zero]
      paths := fun j hj ↦ absurd hj (by simp)
      frame := hfr.trans (BFrame.of_same m₅ _) fun _ h ↦ h
      slots := fun _ _ _ _ ↦ rfl
      low := hPb'.1 }
  obtain ⟨v, rv, hd | ⟨kj, ops, hv⟩⟩ := path_loop h0 hI hpos
  · exact ⟨v, r.trans (r₅.trans rv), Or.inl hd⟩
  have hlen := rep_length hv.read
  have hhv := hv.pas.pg.heap.hi
  refine ⟨v, r.trans (r₅.trans rv), Or.inr ⟨P, npi, kj, ops, ⟨hv.pas.pg, hv.pas.pc, hv.pas.x18,
    hv.pas.x23, ?_, ?_, hv.pas.room, hv.pas.ptr, hv.pas.rest, ?_, hlen, hv.paths, ⟨hP8, Or.inr
    ⟨hPb'.1, hv.pas.buf.2.2⟩⟩, hv.frame, ?_⟩⟩⟩
  · intro c h8 h1 h2
    rw [hv.slots c h8 h1 (by omega), m₅, slots₄ c h8 h1 h2]
  · have e := hv.slots 80 (by decide) (by decide) (by decide)
    rw [m₅] at e
    exact e.trans s80
  · rw [hread0]; exact hv.read
  · exact le_trans hPb'.1 (by have := hv.pas.buf.2.2; omega)

end

end Rv64Verifier.Proofs.Main
