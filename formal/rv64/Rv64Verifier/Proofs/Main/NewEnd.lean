import Rv64Verifier.Proofs.Main.NewGroup

/-!
# `Bytecode::new`'s blocks: the end of one

`BE`: at `0x80000510`, block `i` done, `newRust`'s fold after it in the `Vec`s. `block_next`: on to
the next block (`NewL`) or, the table done, out of the loop (`AfterNew`). `block_empty`: a block of
zero words leaves `group` (`0x8000064c`) straight for `0x80000510`.
-/

namespace Rv64Verifier.Proofs.Main
open RiscvZkvm.Rv64 LeanVM.Parameters Rv64Verifier.Runtime Rv64Verifier.Proofs.Bytecode
  Rv64Verifier.Blocks.F3

/-- At `0x80000510`, block `i` of length `L` done: `newRust`'s fold after it is `st`. -/
structure BE (s : MachineState) (words : List Word) (u₀ : MachineState) (i L : Nat)
    (st : Model.NewState) (t : MachineState) : Prop where
  a : NewA s words u₀
  ng : NG u₀ t
  pc : t.pc = 0x80000510
  lt : 2 ^ 14 * i < (words.getD 0 0).toNat
  hL : L = min ((words.getD 0 0).toNat - 2 ^ 14 * i) (2 ^ 14)
  fold : foldNew (tbl words) (i + 1) = some st
  x8 : t.getReg .x8 = u₀.getReg .x8
  x15 : t.getReg .x15 = inputBase + BitVec.ofNat 64 (8 * (1 + 2 ^ 14 * i + L))
  x16 : t.getReg .x16 = u₀.getReg .x9
  x22 : t.getReg .x22 = 32768
  x25 : t.getReg .x25 = u₀.getReg .x8 + 0x20000
  x26 : t.getReg .x26 = BitVec.ofNat 64 ((words.getD 0 0).toNat - 2 ^ 14 * i - L)
  x27 : t.getReg .x27 = 1
  m8 : t.getMem (msp + 8) = u₀.getReg .x8 + 0x20000
  m16 : t.getMem (msp + 16) = 0x77fff801
  m40 : t.getMem (msp + 40) = u₀.getReg .x9
  m56 : t.getMem (msp + 56) = BitVec.ofNat 64 i + 1
  vecs : VecsAt t st
  bufs : VecBufs t (heapNext u₀) (heapNext t)
  groupOf : halvesAt t (u₀.getReg .x9) 0x4000 = st.groupOf
  slots : st.slots.length = 2 ^ 15

theorem VecIn.mono {t : MachineState} {a : Word} {size al H H' H'' : Nat}
    (h : VecIn t a size al H H') (hH : H' ≤ H'') : VecIn t a size al H H'' :=
  ⟨h.len, h.al, h.buf.imp_right fun h ↦ ⟨h.1, le_trans h.2 hH⟩, h.dang⟩

theorem VecBufs.mono {t : MachineState} {H H' H'' : Nat} (h : VecBufs t H H') (hH : H' ≤ H'') :
    VecBufs t H H'' :=
  ⟨h.b.mono hH, h.w.mono hH, h.p.mono hH, h.y.mono hH, h.bw, h.bp, h.bY, h.wp, h.wy, h.py⟩

/-- A `Vec`'s live elements are a buffer of the heap. -/
theorem VecIn.buf' {t : MachineState} {a : Word} {size al H : Nat}
    (h : VecIn t a size al H (heapNext t)) (hH : heapStart ≤ H) :
    Buf t (vecPtr t a) (size * (vecLen t a).toNat) al := by
  have hl := Nat.mul_le_mul_right size h.len
  refine ⟨h.al, ?_⟩
  rcases h.buf with h0 | ⟨h1, h2⟩
  · left; rw [Nat.mul_comm]; omega
  · right; rw [Nat.mul_comm]; omega

/-- A `Vec`'s pointer lies below `NEXT`. -/
theorem VecIn.ptr_le {t : MachineState} {a : Word} {size al H : Nat}
    (h : VecIn t a size al H (heapNext t)) (hn : heapStart ≤ heapNext t) :
    (vecPtr t a).toNat ≤ heapNext t := by
  rcases h.buf with h0 | ⟨_, h2⟩
  · exact le_of_lt (lt_of_lt_of_le (h.dang h0) hn)
  · omega

section
variable {s u₀ t : MachineState} {words : List Word} {i L : Nat} {st : Model.NewState}

/-- `0x80000510`: on to block `i + 1`, or out of the loop. -/
theorem block_next (h : BE s words u₀ i L st t) :
    ∃ v, Reaches Image.code t v ∧ (NewL s words u₀ (i + 1) st v ∨ AfterNew s words v) := by
  have hsp := h.ng.sp
  obtain ⟨v, rv, hv⟩ := Sym.BlockSpec.reaches b80000510_spec h.pc (by rv_eval [hsp, msp]; decide)
  have kv := b80000510_keeps hv
  have hm := b80000510_mem_same hv
  have hspv : v.getReg .x2 = msp := (kv .x2 (by decide)).trans hsp
  have ng := h.ng.same hm hspv
  have hn : heapNext v = heapNext t := by simp only [heapNext, hm]
  have hlo := h.a.inv.heap.lo
  have hhi := h.ng.heap.hi
  have hmo := h.ng.mono
  simp only [heapNext, heapStart, heapEnd] at hlo hhi hmo
  obtain ⟨vecs, bufs⟩ := VecsAt.frame h.vecs h.bufs (BFrame.of_same hm (fun _ ↦ False))
    (fun _ h ↦ h.elim) (by simp only [heapNext, heapEnd]; omega)
  rw [← hn] at bufs
  have hfit := h.a.inv.fits
  simp only [inputWords] at hfit
  have hlen := h.a.len
  have hlt := h.lt
  have hL := h.hL
  have x26n : (t.getReg .x26).toNat = (words.getD 0 0).toNat - 2 ^ 14 * i - L := by
    rw [h.x26, BitVec.toNat_ofNat]; omega
  by_cases hz : t.getReg .x26 = 0
  · have he : (words.getD 0 0).toNat - 2 ^ 14 * i - L = 0 := by
      rw [← x26n, hz]; rfl
    refine ⟨v, rv, Or.inr ⟨ng.minv h.a, b80000510_pc_taken hv hz, hlen, ?_, ?_, ?_, ?_, ?_⟩⟩
    · have e := ng.keepMsp (c := 0) (by decide) (by decide)
      rw [show (msp + BitVec.ofNat 64 0 : Word) = msp from by decide, h.a.n] at e
      exact e
    · exact (ng.keepMsp (c := 88) (by decide) (by decide)).trans h.a.ptr
    · exact (congrArg BitVec.toNat (ng.keepMsp (c := 96) (by decide) (by decide))).trans h.a.rest
    · rw [ng.iv']; exact h.a.iv
    · have hnb : ((tbl words).length + 2 ^ 14 - 1) / 2 ^ 14 = i + 1 := by
        rw [tbl_length hlen]; omega
      have hS : heapStart ≤ heapNext v := by rw [hn]; simp only [heapStart, heapNext]; omega
      refine ⟨_, by rw [newRust_eq, hnb, h.fold]; rfl, vecs.blocks, vecs.words, vecs.positions,
        vecs.bytes, bufs.b.buf' hlo, bufs.w.buf' hlo, bufs.p.buf' hlo, bufs.y.buf' hlo,
        bufs.b.ptr_le hS, bufs.w.ptr_le hS, bufs.p.ptr_le hS, bufs.y.ptr_le hS⟩
  · have hL' : L = 2 ^ 14 := by
      have : (t.getReg .x26).toNat ≠ 0 := fun e ↦ hz (BitVec.eq_of_toNat_eq e)
      omega
    subst hL'
    refine ⟨v, rv, Or.inl ⟨h.a, ng, b80000510_pc_not_taken hv hz, ?_, h.fold, ?_, ?_, ?_, ?_, ?_,
      ?_, ?_, ?_, ?_, ?_, ?_, vecs, bufs, by rw [halvesAt_same hm]; exact h.groupOf, h.slots⟩⟩
    · have : (t.getReg .x26).toNat ≠ 0 := fun e ↦ hz (BitVec.eq_of_toNat_eq e)
      omega
    · rw [kv .x8 (by decide)]; exact h.x8
    · rw [b80000510_x13 hv, hsp, h.m56, BitVec.ofNat_add]; rfl
    · rw [kv .x15 (by decide), h.x15, show 1 + 2 ^ 14 * i + 2 ^ 14 = 1 + 2 ^ 14 * (i + 1) by omega]
    · rw [kv .x16 (by decide)]; exact h.x16
    · rw [kv .x22 (by decide)]; exact h.x22
    · rw [kv .x25 (by decide)]; exact h.x25
    · rw [kv .x26 (by decide), x26n]; omega
    · rw [kv .x27 (by decide)]; exact h.x27
    · rw [hm]; exact h.m8
    · rw [hm]; exact h.m16
    · rw [hm]; exact h.m40

variable {Hb : Nat} {g : GrpSt}

/-- `group`'s fold over a whole block leaves `2^15` slots. -/
theorem GS.gslots (h : GS s words u₀ i L Hb st L g t) (hf : gfold words i st L = some g) :
    g.1.length = 2 ^ 15 := by
  have hbl := h.blk_len
  have hgl : st.groupOf.length = 0x4000 := by
    rw [← gfold_len words i st L g hf, ← h.mem.groupOf]; simp [halvesAt]
  obtain ⟨g₀, hg₀, hinv⟩ := groupFold_spec (blk words i) (by rw [hbl]; exact h.L_le) st.slots
    h.k.slotsLen st.groupOf (by rw [hbl, hgl]; exact h.L_le) L (by omega)
  have : gfold words i st L = some g₀ := hg₀
  rw [hf] at this
  cases this
  exact hinv.slots_len

theorem GS.groupRust (h : GS s words u₀ i L Hb st L g t) (hf : gfold words i st L = some g) :
    Model.groupRust (((tbl words).drop (i * 2 ^ 14)).take (2 ^ 14)) st.slots st.groupOf = some g := by
  have e := hf
  rw [← h.blk_len] at e
  exact e

/-- `0x8000064c`: a block of zero words, its `distinct` empty, done. -/
theorem block_empty (h : GS s words u₀ i L Hb st L g t) (hpc : t.pc = 0x8000064c)
    (hf : gfold words i st L = some g) (he : g.2.2 = []) :
    ∃ v, Reaches Image.code t v ∧ BE s words u₀ i L { st with slots := g.1, groupOf := g.2.1 } v := by
  obtain ⟨v, rv, hv⟩ := Sym.BlockSpec.reaches b8000064c_spec hpc trivial
  have kv := b8000064c_keeps hv
  have gs := h.same (fun a ↦ b8000064c_mem_same hv a) fun r _ _ _ _ _ ↦ by
    rcases r with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ |
      _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _
    all_goals first | exact kv _ (by decide) | rfl
  have hfold : foldNew (tbl words) (i + 1) = some { st with slots := g.1, groupOf := g.2.1 } := by
    rw [foldNew_succ, h.k.fold, Option.bind_some, Model.blockNewRust, h.groupRust hf]
    simp only [Option.map_some, he, List.isEmpty_nil, ↓reduceIte]
  have hx18 : t.getReg .x18 = 0 := by rw [h.x18, he]; rfl
  refine ⟨v, rv, ⟨gs.k.a, gs.k.ng, b8000064c_pc_taken hv hx18, gs.k.lt, gs.k.hL, hfold, gs.x8,
    gs.x15, gs.x16, gs.x22, gs.x25, gs.x26, gs.x27, gs.k.bm.m8, gs.k.bm.m16, gs.k.bm.m40,
    gs.k.bm.m56, ⟨gs.vecs.blocks, gs.vecs.words, gs.vecs.positions, gs.vecs.bytes⟩, gs.bufs.mono gs.k.hb, gs.mem.groupOf, h.gslots hf⟩⟩

end

end Rv64Verifier.Proofs.Main
