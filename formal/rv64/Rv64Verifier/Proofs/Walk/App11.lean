import Rv64Verifier.Proofs.Walk.TmpA11

/-!
# `walk`: `kappas.extend(vec![h; w])` (R11)

From `0x800031a4` (`Tmp11 .. i T`): `reserve(w)` on `kappas` (`kapReserve`, to `App11` at
`0x800031b4`), `memcpy` of `T` past its length and the new length (`kapCopy`), to the loop's
latch at `0x800030b8`.
-/

namespace Rv64Verifier.Proofs.Walk
open RiscvZkvm.Rv64 LeanVM.Parameters LeanVM.Protocol.Compile Rv64Verifier.Runtime
  Rv64Verifier.Model Rv64Verifier.Transcript Rv64Verifier.Layout Rv64Verifier.Model.LayoutMirror
  Rv64Verifier.Blocks.F4
open Rv64Verifier.Sym (reduceReg reducePc reduceMem reduceWrites reduceObl)

/-- At `0x800031b4`: `kappas` has room for `w` more, its buffer apart from `T`. -/
structure App11 (OI : MachineState → Word → List (List Opening) → Prop) (s u : MachineState)
    (A : List E) (k : Nat) (R Q B : Word) (lo lo2 i : Nat) (T : Word) : Prop where
  keep : Keep11 OI s u A k R Q B lo lo2
  kv : KapVec s u lo2 (kapPre A k i)
  lt : i < 6
  x8 : u.getReg .x8 = BitVec.ofNat 64 (80 * i)
  x9 : u.getReg .x9 = 6
  x19 : u.getReg .x19 = 0xa0000460
  x20 : u.getReg .x20 = 480
  x22 : u.getReg .x22 = 6
  x27 : u.getReg .x27 = B
  x18 : u.getReg .x18 = BitVec.ofNat 64 ((hts A).getD 5 0)
  x23 : u.getReg .x23 = BitVec.ofNat 64 (k - 4)
  x26 : u.getReg .x26 = BitVec.ofNat 64 ((hts A).getD 5 0 + 6)
  x24 : u.getReg .x24 = BitVec.ofNat 64 (tableWidthsRust.getD i 0)
  x25 : u.getReg .x25 = T
  tal : T.toNat % 8 = 0
  tlo : heapStart ≤ T.toNat
  thi : T.toNat + 8 * tableWidthsRust.getD i 0 ≤ heapNext u
  tvals : ∀ j < tableWidthsRust.getD i 0,
    u.getMem (T + BitVec.ofNat 64 (8 * j)) = BitVec.ofNat 64 ((hts A).getD i 0)
  room : (kapPre A k i).length + tableWidthsRust.getD i 0 ≤ (vecCap u (s.getReg .x2 - 1344)).toNat
  apart : (vecPtr u (s.getReg .x2 - 1344)).toNat + 8 * (vecCap u (s.getReg .x2 - 1344)).toNat ≤
      T.toNat ∨ T.toNat + 8 * tableWidthsRust.getD i 0 ≤ (vecPtr u (s.getReg .x2 - 1344)).toNat

set_option maxRecDepth 8192 in
/-- `reserve(w)` on `kappas`. -/
theorem kapReserve (hRF : ReserveFreshSpec 0x8000d628 8 8)
    {OI : MachineState → Word → List (List Opening) → Prop} {s c : MachineState} {A : List E}
    {k : Nat} {R Q B : Word} {lo lo2 i : Nat} {T : Word}
    (hpre : WalkPre s) (hc : c.pc = 0x800031a4) (h : Tmp11 OI s c A k R Q B lo lo2 i T) :
    ∃ t, Reaches Image.code c t ∧ (Dead Image.code t ∨
      (t.pc = 0x800031b4 ∧ App11 OI s t A k R Q B lo lo2 i T)) := by
  obtain ⟨hb1, hb2, hb3, -⟩ := bounds hpre
  have hi := h.lt
  have hk := kapPre_ne A k (le_of_lt hi)
  have hw := width_pos hi
  set w := tableWidthsRust.getD i 0 with hwdef
  have H := h.keep.at11.base
  have spc : c.getReg .x2 = s.getReg .x2 - 2656 := H.inv.sp
  obtain ⟨c₁, hr₁, h₁⟩ := Sym.BlockSpec.reaches b800031a4_spec hc (by rv_eval [])
  have m₁ (a : Word) : c₁.getMem a = c.getMem a := b800031a4_mem_same h₁ a
  have k₁ := b800031a4_keeps h₁
  have K₁ := h.keep.same hpre m₁ (k₁ .x2 (by decide))
  have kv₁ := h.kv.same hpre hk H.inv.heap.hi m₁
  have hn₁ : heapNext c₁ = heapNext c := by simp only [heapNext, m₁]
  have hP₁ : vecPtr c₁ (s.getReg .x2 - 1344) = vecPtr c (s.getReg .x2 - 1344) := by
    simp only [vecPtr, m₁]
  have hC₁ : vecCap c₁ (s.getReg .x2 - 1344) = vecCap c (s.getReg .x2 - 1344) := by
    simp only [vecCap, m₁]
  have e1312 : c.getReg .x2 + 1312 = s.getReg .x2 - 1344 := by
    rw [spc]; apply BitVec.eq_of_toNat_eq; addr_omega [hb1]
  have x10₁ : c₁.getReg .x10 = s.getReg .x2 - 1344 := by rw [b800031a4_x10 h₁, e1312]
  have x11₁ : c₁.getReg .x11 = BitVec.ofNat 64 w := by rw [b800031a4_x11 h₁]; exact h.x24
  have I₁ := K₁.at11.base.inv
  have hab := hpre.stack.above
  have hx := hpre.stack.next
  rw [stackLo_eq] at hab hx
  rw [stack_eq] at hx
  simp only [heapEnd] at hab
  have pre : ReservePre 8 8 c₁ := {
    heap := I₁.heap
    self := by
      rw [x10₁]; exact validMemRange_of (by addr_omega [hb1, hb3]) (Or.inr ⟨by addr_omega [hb1],
        by addr_omega [hb1, hb2]⟩)
    vec := by rw [x10₁]; exact kv₁.ok
    stack := stk10 hpre I₁ (by decide) (by decide)
    selfFree := by
      rw [x10₁]; exact ⟨Or.inr (by addr_omega [hab, hb1]), by simp only [Apart]; addr_omega [hx, hb1]⟩
    selfStack := by rw [x10₁, stackLo_callee I₁]; simp only [Apart]; addr_omega [hb1] }
  obtain ⟨t, hr, ⟨hpct, hp, post, hsame⟩ | hd⟩ := hRF c₁ (b800031a4_pc h₁) pre
  swap
  · exact ⟨t, hr₁.trans hr, Or.inl hd⟩
  have pcap := post.cap
  have pvec := post.vec
  have plen := post.len
  have pbytes := post.bytes
  have pframe := post.frame
  have phv := post.heap
  have pmono := post.mono
  rw [x10₁, x11₁] at pcap
  rw [x10₁] at pvec plen pbytes pframe hsame
  have fr := pframe.dframe
  have hhc := I₁.heap.hi
  have hht := phv.hi
  have hl2 := K₁.lo2le
  simp only [heapEnd] at hhc hht
  have hwN : (BitVec.ofNat 64 w).toNat = w := by rw [BitVec.toNat_ofNat]; omega
  rw [hwN] at pcap
  have hW : ∀ a, (Within a (s.getReg .x2 - 1344) 16 ∨ Within a (stackLo c₁ reserveStack) reserveStack ∨
      Within a nextAddr 8 ∨ Fresh c₁ t a) → W11 s lo2 t a := fun a ha ↦ by
    rcases ha with ha | ha | ha | ha
    · simp only [Within] at ha
      refine Or.inl ⟨by addr_omega [ha, hb1], by addr_omega [ha, hb1], ?_⟩
      simp only [hdrs, Within]; addr_omega [ha, hb1]
    · rw [stackLo_callee I₁] at ha
      exact Or.inr (Or.inl (by simp only [Within, reserveStack] at ha ⊢; addr_omega [ha, hb1]))
    · exact Or.inr (Or.inr (Or.inl ha))
    · simp only [Fresh] at ha; exact Or.inr (Or.inr (Or.inr ⟨by omega, ha.2⟩))
  have K' := K₁.keep hpre fr hW phv pmono (hp .x2 (by decide))
  obtain ⟨b1, b2, b3, b4⟩ := kv₁.bounds hk
  have hraw := pvec.raw
  simp only [RawVecOk, Buf] at hraw
  have hL := kv₁.len
  have tlo := h.tlo
  have thi := h.thi
  rw [← hP₁, ← hC₁] at tlo
  rw [← hn₁] at thi
  simp only [heapStart] at b2
  have hfr : lo2 ≤ (vecPtr t (s.getReg .x2 - 1344)).toNat := by
    rcases hsame with ⟨e1, -⟩ | hnb
    · rw [e1]; exact kv₁.fresh
    · simp only [NewBuf] at hnb; rcases hnb.2 with h0 | h0 <;> omega
  have hap : (vecPtr t (s.getReg .x2 - 1344)).toNat + 8 * (vecCap t (s.getReg .x2 - 1344)).toNat ≤
      T.toNat ∨ T.toNat + 8 * w ≤ (vecPtr t (s.getReg .x2 - 1344)).toNat := by
    rcases hsame with ⟨e1, e2⟩ | hnb
    · left; rw [e1, e2]; exact tlo
    · right; simp only [NewBuf] at hnb; rcases hnb.2 with h0 | h0 <;> omega
  have hT : ∀ j < w, t.getMem (T + BitVec.ofNat 64 (8 * j)) = c₁.getMem (T + BitVec.ofNat 64 (8 * j)) :=
    fun j hj ↦ fr.getMem_of (fun x hx hw' ↦ by
      simp only [Within] at hx
      rcases hw' with h2 | h2 | h2 | h2
      · simp only [Within] at h2; addr_omega [hx, h2, hb1, b2, tlo, thi, hhc, hj]
      · rw [stackLo_callee I₁] at h2
        simp only [Within, reserveStack] at h2
        addr_omega [hx, h2, hb1, b2, tlo, thi, hhc, hj]
      · simp only [Within, nextAddr] at h2; addr_omega [hx, h2, b2, tlo, thi, hhc, hj]
      · simp only [Fresh] at h2; addr_omega [hx, h2, b2, tlo, thi, hhc, hj])
      (by addr_omega [b2, tlo, thi, hhc, hj])
  refine ⟨t, hr₁.trans hr, Or.inr ⟨by rw [hpct, returnAddress_eq, b800031a4_x1 h₁]; decide, {
    keep := K'
    kv := ⟨pvec, hfr, by rw [plen]; exact hL, fun j hj ↦ by
      rw [getMem_eq_of_bytesAt pbytes hraw.1 b1 (by omega) (by omega)]
      exact kv₁.vals j hj⟩
    lt := hi
    x8 := by rw [hp .x8 (by decide), k₁ .x8 (by decide)]; exact h.x8
    x9 := by rw [hp .x9 (by decide), k₁ .x9 (by decide)]; exact h.x9
    x19 := by rw [hp .x19 (by decide), k₁ .x19 (by decide)]; exact h.x19
    x20 := by rw [hp .x20 (by decide), k₁ .x20 (by decide)]; exact h.x20
    x22 := by rw [hp .x22 (by decide), k₁ .x22 (by decide)]; exact h.x22
    x27 := by rw [hp .x27 (by decide), k₁ .x27 (by decide)]; exact h.x27
    x18 := by rw [hp .x18 (by decide), k₁ .x18 (by decide)]; exact h.x18
    x23 := by rw [hp .x23 (by decide), k₁ .x23 (by decide)]; exact h.x23
    x26 := by rw [hp .x26 (by decide), k₁ .x26 (by decide)]; exact h.x26
    x24 := by rw [hp .x24 (by decide), k₁ .x24 (by decide)]; exact h.x24
    x25 := by rw [hp .x25 (by decide), k₁ .x25 (by decide)]; exact h.x25
    tal := h.tal
    tlo := by simp only [heapStart]; omega
    thi := by omega
    tvals := fun j hj ↦ by rw [hT j hj, m₁]; exact h.tvals j hj
    room := by rw [hL] at pcap; exact pcap
    apart := hap }⟩⟩

/-- At the loop's latch's targets, `n` tables done. -/
structure Lat11 (OI : MachineState → Word → List (List Opening) → Prop) (s u : MachineState)
    (A : List E) (k : Nat) (R Q B : Word) (lo lo2 n : Nat) : Prop where
  keep : Keep11 OI s u A k R Q B lo lo2
  kv : KapVec s u lo2 (kapPre A k n)
  le : n ≤ 6
  x8 : u.getReg .x8 = BitVec.ofNat 64 (80 * n)
  x9 : u.getReg .x9 = 6
  x19 : u.getReg .x19 = 0xa0000460
  x20 : u.getReg .x20 = 480
  x22 : u.getReg .x22 = 6
  x27 : u.getReg .x27 = B
  x18 : u.getReg .x18 = BitVec.ofNat 64 ((hts A).getD 5 0)
  x23 : u.getReg .x23 = BitVec.ofNat 64 (k - 4)
  x26 : u.getReg .x26 = BitVec.ofNat 64 ((hts A).getD 5 0 + 6)
  x24 : u.getReg .x24 = BitVec.ofNat 64 (kapLen n)

theorem Lat11.kap11 {OI : MachineState → Word → List (List Opening) → Prop} {s u : MachineState}
    {A : List E} {k : Nat} {R Q B : Word} {lo lo2 n : Nat} (h : Lat11 OI s u A k R Q B lo lo2 n)
    (hn : n < 6) : Kap11 OI s u A k R Q B lo lo2 n :=
  ⟨h.keep, h.kv, hn, h.x8, h.x9, h.x19, h.x20, h.x22, h.x27, h.x18, h.x23, h.x26⟩

theorem ofNat_mul8 (n : Nat) : BitVec.ofNat 64 n * 8 = BitVec.ofNat 64 (8 * n) := by
  apply BitVec.eq_of_toNat_eq
  have h8 : (8 : Word).toNat = 8 := rfl
  simp only [BitVec.toNat_mul, BitVec.toNat_ofNat, h8]
  omega

theorem ofNat_add80 {i : Nat} (hi : i < 6) :
    BitVec.ofNat 64 (80 * i) + 80 = BitVec.ofNat 64 (80 * (i + 1)) := by
  interval_cases i <;> decide

theorem kapPre_getD_lt (A : List E) (k : Nat) {i j : Nat} (hi : i < 6) (hj : j < kapLen i) :
    (kapPre A k (i + 1)).getD j 0 = (kapPre A k i).getD j 0 := by
  have hl : i < tablesRust.length := hi
  obtain ⟨t, ht⟩ : ∃ t, tablesRust[i]? = some t := ⟨_, List.getElem?_eq_getElem hl⟩
  rw [kapPre_succ A k ht]
  simp only [List.getD_eq_getElem?_getD]
  rw [List.getElem?_append_left (by rw [kapPre_length A k i (by omega)]; exact hj)]

theorem kapPre_getD_ge (A : List E) (k : Nat) {i j : Nat} (hi : i < 6) (hj1 : kapLen i ≤ j)
    (hj2 : j < kapLen i + tableWidthsRust.getD i 0) :
    (kapPre A k (i + 1)).getD j 0 = (hts A).getD i 0 := by
  have hl : i < tablesRust.length := hi
  obtain ⟨t, ht⟩ : ∃ t, tablesRust[i]? = some t := ⟨_, List.getElem?_eq_getElem hl⟩
  have hL := kapPre_length A k i (by omega)
  rw [kapPre_succ A k ht, List.getD_eq_getElem?_getD, List.getElem?_append_right (by omega), hL,
    List.getElem?_replicate]
  simp only [show j - kapLen i < tableWidthsRust.getD i 0 by omega, ite_true, Option.getD_some]

set_option maxRecDepth 8192 in
/-- `memcpy(kappas.ptr + 8 len, T, 8 w)`, the new length, the latch. -/
theorem kapCopy (hMC : MemcpySpec 0x800126e4)
    {OI : MachineState → Word → List (List Opening) → Prop} {s c : MachineState} {A : List E}
    {k : Nat} {R Q B : Word} {lo lo2 i : Nat} {T : Word}
    (hpre : WalkPre s) (hc : c.pc = 0x800031b4) (h : App11 OI s c A k R Q B lo lo2 i T) :
    ∃ t, Reaches Image.code c t ∧ (Dead Image.code t ∨
      (t.pc = (if i + 1 = 6 then 0x800031dc else 0x800030c8) ∧
        Lat11 OI s t A k R Q B lo lo2 (i + 1))) := by
  obtain ⟨hb1, hb2, hb3, -⟩ := bounds hpre
  have hi := h.lt
  have hk := kapPre_ne A k (le_of_lt hi)
  have hw := width_pos hi
  set w := tableWidthsRust.getD i 0 with hwdef
  have hLk : (kapPre A k i).length = kapLen i := kapPre_length A k i (by omega)
  have hL165 : kapLen i ≤ 165 := kapLen_le (by omega)
  set L := (kapPre A k i).length with hLdef
  have I := h.keep.at11.base.inv
  have spc : c.getReg .x2 = s.getReg .x2 - 2656 := I.sp
  obtain ⟨P, hP⟩ : ∃ P, vecPtr c (s.getReg .x2 - 1344) = P := ⟨_, rfl⟩
  obtain ⟨C, hC⟩ : ∃ C, vecCap c (s.getReg .x2 - 1344) = C := ⟨_, rfl⟩
  obtain ⟨b1, b2, b3, b4⟩ := h.kv.bounds hk
  have room := h.room
  have hap := h.apart
  have hfr := h.kv.fresh
  rw [hP] at b1 b2 b3 hap hfr
  rw [hC] at b3 b4 room hap
  have hPm : c.getMem (s.getReg .x2 - 1344 + 8) = P := hP
  have hhc := I.heap.hi
  simp only [heapEnd, heapStart] at hhc b2
  have tlo := h.tlo
  have thi := h.thi
  simp only [heapStart] at tlo
  have hlenW : vecLen c (s.getReg .x2 - 1344) = BitVec.ofNat 64 L := by
    apply BitVec.eq_of_toNat_eq; rw [h.kv.len, BitVec.toNat_ofNat]; omega
  have hwN : (BitVec.ofNat 64 w).toNat = w := by rw [BitVec.toNat_ofNat]; omega
  -- 0x800031b4
  obtain ⟨c₁, hr₁, h₁⟩ := Sym.BlockSpec.reaches b800031b4_spec hc (by
    rv_eval [spc]; simp only [Sym.validAccess_eight]; addr_omega [hb1, hb2, hb3])
  have k₁ := b800031b4_keeps h₁
  have m₁ := b800031b4_mem_same h₁
  have e1328 : c.getReg .x2 + 1328 = s.getReg .x2 - 1344 + 16 := by
    rw [spc]; apply BitVec.eq_of_toNat_eq; addr_omega [hb1]
  have x21₁ : c₁.getReg .x21 = BitVec.ofNat 64 L := by rw [b800031b4_x21 h₁, e1328]; exact hlenW
  have pc₁ := b800031b4_pc_not_taken h₁ (by
    rw [h.x24]; intro he
    have := congrArg BitVec.toNat he
    have h0 : (0 : Word).toNat = 0 := rfl
    rw [hwN, h0] at this; omega)
  have sp₁ : c₁.getReg .x2 = s.getReg .x2 - 2656 := by rw [k₁ .x2 (by decide)]; exact spc
  -- 0x800031bc
  obtain ⟨c₂, hr₂, h₂⟩ := Sym.BlockSpec.reaches b800031bc_spec pc₁ (by
    rv_eval [sp₁]; simp only [Sym.validAccess_eight]; addr_omega [hb1, hb2, hb3])
  have k₂ := b800031bc_keeps h₂
  have m₂ (a : Word) : c₂.getMem a = c.getMem a := by rw [b800031bc_mem_same h₂, m₁]
  have sp₂ : c₂.getReg .x2 = c.getReg .x2 := by rw [k₂ .x2 (by decide), k₁ .x2 (by decide)]
  have I₂ : Inv s c₂ := I.same m₂ sp₂
  have e1320 : c₁.getReg .x2 + 1320 = s.getReg .x2 - 1344 + 8 := by
    rw [sp₁]; apply BitVec.eq_of_toNat_eq; addr_omega [hb1]
  have x10₂ : c₂.getReg .x10 = P + BitVec.ofNat 64 (8 * L) := by
    rw [b800031bc_x10 h₂, e1320, m₁, hPm, x21₁, ofNat_mul8]
  have x11₂ : c₂.getReg .x11 = T := by rw [b800031bc_x11 h₂, k₁ .x25 (by decide)]; exact h.x25
  have x12₂ : c₂.getReg .x12 = BitVec.ofNat 64 (8 * w) := by
    rw [b800031bc_x12 h₂, k₁ .x24 (by decide), h.x24, ofNat_mul8]
  have x12N : (c₂.getReg .x12).toNat = 8 * w := by rw [x12₂, BitVec.toNat_ofNat]; omega
  have hD : (P + BitVec.ofNat 64 (8 * L)).toNat = P.toNat + 8 * L := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  have hmc : MemcpyPre c₂ := {
    dst := by rw [x10₂, x12N]; simp only [Mapped]; omega
    src := by rw [x11₂, x12N]; simp only [Mapped]; omega
    apart := by rw [x10₂, x11₂, x12N]; simp only [Apart]; rw [hD]; omega
    stack := calleeStack hpre I₂ (by decide) (by decide)
    dstStack := by
      rw [x10₂, x12N, stackLo_callee I₂]; simp only [Apart, memcpyStack]; rw [hD]
      addr_omega [hb1, b2, b3, b4, hhc, room]
    srcStack := by
      rw [x11₂, x12N, stackLo_callee I₂]; simp only [Apart, memcpyStack]
      addr_omega [hb1, tlo, thi, hhc] }
  obtain ⟨t₃, hr₃, ⟨hpc₃, hp₃, post⟩ | hd⟩ := hMC.call (Reaches.refl c₂) (b800031bc_pc h₂) hmc
  swap
  · exact ⟨t₃, hr₁.trans (hr₂.trans hr₃), Or.inl hd⟩
  have by₃ := post.bytes
  have fr₃ := post.frame
  rw [x10₂, x11₂, x12N] at by₃
  rw [x10₂, x12N, stackLo_callee I₂] at fr₃
  have pc₃ : t₃.pc = 0x800031d8 := by rw [hpc₃, returnAddress_eq, b800031bc_x1 h₂]; decide
  obtain ⟨t₄, hr₄, h₄⟩ := Sym.BlockSpec.reaches b800031d8_spec pc₃ (by rv_eval [])
  have k₄ := b800031d8_keeps h₄
  have rg (r : Reg) (hr : r ∈ ([.x2, .x8, .x9, .x18, .x19, .x20, .x22, .x23, .x24, .x26, .x27] :
      List Reg)) : t₄.getReg r = c.getReg r := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      rw [k₄ _ (by decide), hp₃ _ (by decide), k₂ _ (by decide), k₁ _ (by decide)]
  have sp₄ : t₄.getReg .x2 = s.getReg .x2 - 2656 := by rw [rg .x2 (by decide)]; exact spc
  have x21₄ : t₄.getReg .x21 = BitVec.ofNat 64 L := by
    rw [k₄ .x21 (by decide), hp₃ .x21 (by decide), k₂ .x21 (by decide)]; exact x21₁
  -- the latch
  obtain ⟨t₅, hr₅, h₅⟩ := Sym.BlockSpec.reaches b800030b8_spec (b800031d8_pc h₄) (by
    rv_eval [sp₄]; simp only [Sym.validAccess_eight]; addr_omega [hb1, hb2, hb3])
  have fr₅ := (b800030b8_frame h₅ (by rw [sp₄]; addr_omega [hb1])).dframe
  have e5 : t₄.getReg .x2 + 1328 = s.getReg .x2 - 1328 := by
    rw [sp₄]; apply BitVec.eq_of_toNat_eq; addr_omega [hb1]
  rw [e5] at fr₅
  have frC : Layout.DFrame c t₅ fun a ↦ Within a (P + BitVec.ofNat 64 (8 * L)) (8 * w) ∨
      Within a (s.getReg .x2 - 2656 - BitVec.ofNat 64 memcpyStack) memcpyStack ∨
      Within a (s.getReg .x2 - 1328) 8 := fun a ha hw8 ↦ by
    rw [fr₅ a (fun x hx h' ↦ ha x hx (Or.inr (Or.inr h'))) hw8, b800031d8_mem_same h₄,
      fr₃.dframe a (fun x hx h' ↦ ha x hx (h'.imp_right Or.inl)) hw8, m₂]
  have hn₅ : heapNext t₅ = heapNext c := by
    simp only [heapNext]
    exact congrArg BitVec.toNat (frC nextAddr (fun y hy hw' ↦ by
      simp only [Within, nextAddr, memcpyStack] at hy hw'
      rcases hw' with hw' | hw' | hw' <;> addr_omega [hy, hw', hb1, hD, b2, b3, hhc, room]) (by decide))
  have hv₅ : HeapOk t₅ := ⟨hn₅ ▸ I.heap.lo, hn₅ ▸ I.heap.hi⟩
  have k₅ := b800030b8_keeps h₅
  have sp₅ : t₅.getReg .x2 = c.getReg .x2 := by rw [k₅ .x2 (by decide), rg .x2 (by decide)]
  have K₅ := h.keep.keep hpre frC (fun a ha ↦ by
      rcases ha with ha | ha | ha
      · simp only [Within] at ha
        exact Or.inr (Or.inr (Or.inr ⟨by omega, by rw [hn₅]; omega⟩))
      · simp only [Within, memcpyStack] at ha
        exact Or.inr (Or.inl (by simp only [Within]; addr_omega [ha, hb1]))
      · simp only [Within] at ha
        refine Or.inl ⟨by addr_omega [ha, hb1], by addr_omega [ha, hb1], ?_⟩
        simp only [hdrs, Within]; addr_omega [ha, hb1]) hv₅ hn₅.ge sp₅
  have g (o : Nat) (ho : o + 8 ≤ 16) : t₅.getMem (s.getReg .x2 - 1344 + BitVec.ofNat 64 o) =
      c.getMem (s.getReg .x2 - 1344 + BitVec.ofNat 64 o) :=
    frC.getMem_of (fun x hx hw' ↦ by
      simp only [Within, memcpyStack] at hx hw'
      rcases hw' with h2 | h2 | h2 <;> addr_omega [hx, h2, hb1, hD, b2, b3, hhc, ho, room])
      (by addr_omega [ho, hb1])
  have hC₅ : vecCap t₅ (s.getReg .x2 - 1344) = C := by
    rw [← hC]; simpa [vecCap] using g 0 (by decide)
  have hP₅ : vecPtr t₅ (s.getReg .x2 - 1344) = P := by rw [← hP]; exact g 8 (by decide)
  have e1328' : t₄.getReg .x2 + 1328 = s.getReg .x2 - 1344 + 16 := by
    rw [sp₄]; apply BitVec.eq_of_toNat_eq; addr_omega [hb1]
  have hsum : BitVec.ofNat 64 L + BitVec.ofNat 64 w = BitVec.ofNat 64 (kapLen (i + 1)) := by
    rw [kapLen_succ hi, ← hLk]; apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  have x24₅ : t₅.getReg .x24 = BitVec.ofNat 64 (kapLen (i + 1)) := by
    rw [b800030b8_x24 h₅, x21₄, rg .x24 (by decide), h.x24, hsum]
  have hlen₅ : vecLen t₅ (s.getReg .x2 - 1344) = BitVec.ofNat 64 (kapLen (i + 1)) := by
    simp only [vecLen]; rw [← e1328', b800030b8_m_x2_1328 h₅, x21₄, rg .x24 (by decide), h.x24, hsum]
  have hlenL : (kapPre A k (i + 1)).length = kapLen (i + 1) := kapPre_length A k (i + 1) (by omega)
  have hkl : kapLen (i + 1) = L + w := by rw [kapLen_succ hi, ← hLk]
  have hP8 : (P + BitVec.ofNat 64 (8 * L)).toNat % 8 = 0 := by rw [hD]; omega
  have kv₅ : KapVec s t₅ lo2 (kapPre A k (i + 1)) := {
    ok := ⟨by
      simp only [RawVecOk, Buf, hC₅, hP₅, hn₅]
      exact ⟨b1, Or.inr ⟨by simp only [heapStart]; omega, by omega⟩⟩, by
      rw [hlen₅, hC₅, BitVec.toNat_ofNat]; omega⟩
    fresh := by rw [hP₅]; exact hfr
    len := by rw [hlen₅, hlenL, BitVec.toNat_ofNat]; omega
    vals := fun j hj ↦ by
      rw [hlenL, hkl] at hj
      rw [hP₅, fr₅ _ (fun x hx h' ↦ by simp only [Within] at hx h'; addr_omega [hx, h', hb1, b2, b3, hhc, hj, room])
        (by addr_omega [b2, b3, hhc, hj, room]), b800031d8_mem_same h₄]
      by_cases hjL : j < L
      · rw [fr₃.dframe _ (fun x hx h' ↦ by
            simp only [Within, memcpyStack] at hx h'
            rcases h' with h2 | h2 <;> addr_omega [hx, h2, hb1, hD, b2, b3, hhc, hjL, room])
          (by addr_omega [b2, b3, hhc, hj, room]), m₂, kapPre_getD_lt A k hi (by omega), ← hP]
        exact h.kv.vals j hjL
      · have e : P + BitVec.ofNat 64 (8 * j) =
            P + BitVec.ofNat 64 (8 * L) + BitVec.ofNat 64 (8 * (j - L)) := by
          apply BitVec.eq_of_toNat_eq; addr_omega [b2, b3, hhc, hj, hjL, room]
        rw [e, getMem_eq_of_bytesAt by₃ hP8 h.tal (by omega) (by omega), m₂,
          kapPre_getD_ge A k hi (by omega) (by omega)]
        exact h.tvals (j - L) (by omega) }
  have x8₄ : t₄.getReg .x8 = BitVec.ofNat 64 (80 * i) := by rw [rg .x8 (by decide)]; exact h.x8
  have x20₄ : t₄.getReg .x20 = 480 := by rw [rg .x20 (by decide)]; exact h.x20
  have hpc₅ : t₅.pc = (if i + 1 = 6 then 0x800031dc else 0x800030c8) := by
    split_ifs with h6
    · have e : i = 5 := by omega
      subst e
      exact b800030b8_pc_taken h₅ (by rw [x8₄, x20₄]; decide)
    · have hi5 : i < 5 := by omega
      exact b800030b8_pc_not_taken h₅ (by rw [x8₄, x20₄]; interval_cases i <;> decide)
  refine ⟨t₅, hr₁.trans (hr₂.trans (hr₃.trans (hr₄.trans hr₅))), Or.inr ⟨hpc₅, {
    keep := K₅
    kv := kv₅
    le := by omega
    x8 := by rw [b800030b8_x8 h₅, x8₄, ofNat_add80 hi]
    x9 := by rw [k₅ .x9 (by decide), rg .x9 (by decide)]; exact h.x9
    x19 := by rw [k₅ .x19 (by decide), rg .x19 (by decide)]; exact h.x19
    x20 := by rw [k₅ .x20 (by decide), rg .x20 (by decide)]; exact h.x20
    x22 := by rw [k₅ .x22 (by decide), rg .x22 (by decide)]; exact h.x22
    x27 := by rw [k₅ .x27 (by decide), rg .x27 (by decide)]; exact h.x27
    x18 := by rw [k₅ .x18 (by decide), rg .x18 (by decide)]; exact h.x18
    x23 := by rw [k₅ .x23 (by decide), rg .x23 (by decide)]; exact h.x23
    x26 := by rw [k₅ .x26 (by decide), rg .x26 (by decide)]; exact h.x26
    x24 := x24₅ }⟩⟩

end Rv64Verifier.Proofs.Walk
