import Rv64Verifier.Proofs.Bus.VbbTail42

/-!
# `verify_bus_balance`'s side loop: `known`

`dot` of the framework selectors and the shifted fingerprints into `S - 320` (`dotCallC`), from
`0x80007788` to `0x8000779c` (`Dotted`, `sideDot`).
-/

namespace Rv64Verifier.Proofs.Bus.VerifyBusBalance
open RiscvZkvm.Rv64 LeanVM.Parameters LeanVM.Protocol.Verifier Rv64Verifier.Runtime
  Rv64Verifier.Model Rv64Verifier.Bus Rv64Verifier.Transcript Rv64Verifier.Blocks.F26
  Rv64Verifier.MultilinearContracts Rv64Verifier.Contracts
open Rv64Verifier.Sym (reduceReg reducePc reduceMem reduceWrites reduceObl)

theorem Apart.symm' {a b : Word} {n m : Nat} (h : Apart a n b m) : Apart b m a n := by
  rcases h with h | h | h | h
  · exact Or.inr (Or.inl h)
  · exact Or.inl h
  · exact Or.inr (Or.inr (Or.inr h))
  · exact Or.inr (Or.inr (Or.inl h))

theorem LowBuf.valid {p : Word} {n B : Nat} (h : LowBuf p (24 * n) B) (hB : B ≤ heapEnd) :
    ValidMemRange p (3 * n) := by
  obtain ⟨p8, hb⟩ := h
  rcases hb with h0 | ⟨b1, b2⟩
  · intro i hi; omega
  · exact heapRange p8 b1 (by omega)

theorem LowBuf.apart {p : Word} {n B : Nat} (h : LowBuf p (24 * n) B) (hB : B ≤ heapEnd)
    {a : Word} {m : Nat} (ha : heapEnd ≤ a.toNat) : Apart p (24 * n) a m := by
  obtain ⟨-, hb⟩ := h
  simp only [heapEnd] at hB ha
  rcases hb with h0 | ⟨-, b2⟩
  · exact Or.inl h0
  · exact Or.inr (Or.inr (Or.inl (by omega)))

/-- `dot(S - 320, a1, a2, a3, a4)`, both slices in the heap. -/
theorem dotCallC (hD : DotSpec) {s z h u₀ u : MachineState} (hpre : BusBalancePre s)
    (hsz : heapNext s ≤ heapNext z) (C : Cur s z h u) (hr : Reaches Image.code u₀ u)
    (hpc : u.pc = 0x80007f3c) (h10 : u.getReg .x10 = s.getReg .x2 - 320)
    (hl : LowBuf (u.getReg .x11) (24 * (u.getReg .x12).toNat) (heapNext u))
    (hr' : LowBuf (u.getReg .x13) (24 * (u.getReg .x14).toNat) (heapNext u)) :
    ∃ v, Reaches Image.code u₀ v ∧ ((v.pc = returnAddress u ∧ Preserves u v ∧ Cur s z h v ∧
      DFrame u v (fun x ↦ Within x (s.getReg .x2 - 320) 24 ∨
        Within x (s.getReg .x2 - BitVec.ofNat 64 2464) 1120) ∧ heapNext v = heapNext u ∧
      u.getReg .x12 = u.getReg .x14 ∧
      eAt v (s.getReg .x2 - 320) = dotRust (eListAt u (u.getReg .x11) (u.getReg .x12).toNat)
        (eListAt u (u.getReg .x13) (u.getReg .x12).toNat)) ∨ Dead Image.code v) := by
  obtain ⟨hb1, hb2, hb3, -⟩ := bounds hpre
  have hval : ValidMemRange (s.getReg .x2 - 4544) 568 := hpre.stack.valid
  have hrs := hpre.stack.rodata
  rw [stackLo_eq] at hrs
  have hrb : rodataBase.toNat = 2684354560 := rfl
  have h := C.inv
  have hE := h.heap.hi
  have hsl : stackLo u dotStack = s.getReg .x2 - BitVec.ofNat 64 2464 := by
    simp only [stackLo, dotStack, mulStack, h.sp]; apply BitVec.eq_of_toNat_eq; addr_omega [hb1]
  have rs : RtStack u dotStack :=
    hpre.stack.sub 1344 h.sp (by decide) (by decide) (by decide) (by decide) (by decide)
  have hfa : heapEnd ≤ (s.getReg .x2 - 320).toNat := by simp only [heapEnd]; addr_omega [hb1]
  have hfs : heapEnd ≤ (s.getReg .x2 - BitVec.ofNat 64 2464).toNat := by
    simp only [heapEnd]; addr_omega [hb1]
  have pre : DotPre u := {
    ret := by rw [h10]; valid_sub hval [hb1]
    left := hl.valid hE
    right := hr'.valid hE
    stack := rs.toStackOk
    retLeft := by rw [h10]; exact Apart.symm' (hl.apart hE hfa)
    retRight := by rw [h10]; exact Apart.symm' (hr'.apart hE hfa)
    retStack := by rw [h10, hsl]; addr_omega [hb1]
    leftStack := by rw [hsl]; exact hl.apart hE hfs
    rightStack := by rw [hsl]; exact hr'.apart hE hfs
    rodata := h.rodata hpre
    retRodata := by rw [h10]; simp only [rodataSize] at hrs ⊢; addr_omega [hrs, hrb, hb1]
    stackRodata := by rw [hsl]; simp only [rodataSize] at hrs ⊢; addr_omega [hrs, hrb, hb1] }
  obtain ⟨v, hrv, ⟨hpcv, hp, post⟩ | hd⟩ := hD.call hr hpc pre
  swap
  · exact ⟨v, hrv, Or.inr hd⟩
  have fr : DFrame u v fun x ↦ Within x (s.getReg .x2 - 320) 24 ∨
      Within x (s.getReg .x2 - BitVec.ofNat 64 2464) 1120 :=
    (DFrame.of_two fun x h1 h2 ↦ post.frame x h1 h2).mono fun x hx ↦ by
      rw [h10, hsl] at hx; exact hx
  have hx := hpre.stack.next
  rw [stackLo_eq] at hx
  have hn : heapNext v = heapNext u := by
    simp only [heapNext]
    exact congrArg BitVec.toNat (fr nextAddr fun i hi hw ↦ by
      rcases hw with hw | hw <;> addr_omega [hx, hw, hi, hb1])
  have st : StepS s u v fun x ↦ Within x (s.getReg .x2 - 320) 24 :=
    ⟨fr.mono fun x hx ↦ by
      rcases hx with hx | hx
      · exact Or.inl hx
      · exact Or.inr (Or.inl (by addr_omega [hx, hb1])), ⟨hn ▸ h.heap.lo, hn ▸ h.heap.hi⟩,
      hn.ge, hp.reg .x2⟩
  refine ⟨v, hrv, Or.inl ⟨hpcv, hp, C.next hpre hsz st fun x hx ↦ Or.inl ?_, fr, hn, post.len, ?_⟩⟩
  · simp only [SlotW]
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (by addr_omega [hx, hb1]))))))
  · have := post.value
    rw [h10] at this
    exact this

/-- What `known`'s computation writes from `u` (`0x800076c4`) to `t`: `S - [320, 104)`, the stack
below the frame, `NEXT`, the heap from `u`'s `NEXT` on. -/
def DotW (s u t : MachineState) (a : Word) : Prop :=
  Within a (s.getReg .x2 - 320) 216 ∨ Within a (s.getReg .x2 - 4544) 3200 ∨
    Within a nextAddr 8 ∨ (heapNext u ≤ a.toNat ∧ a.toNat < heapNext t)

/-- At `0x8000779c`, past `Front` at `u`: `known` at `S - 320`. -/
structure Dotted (s z h u t : MachineState) (i : Nat)
    (sd : List BusBlock × BusLayoutRust × List E × List E × E) (point : List E) : Prop where
  cur : Cur s z h t
  fr : DFrame u t (DotW s u t)
  regs : ∀ r ∈ ([.x2, .x8, .x20, .x21, .x24, .x25, .x26, .x27] : List Reg),
    t.getReg r = u.getReg r
  x9 : t.getReg .x9 = sideWord s h i 72
  x18 : t.getReg .x18 = sideWord s h i 80
  known : eAt t (s.getReg .x2 - 320) =
    dotRust (sd.2.1.framework.map (·.eqAbove point)) (sd.2.2.1.map (sd.2.2.2.2 + ·))

set_option maxRecDepth 8192 in
theorem sideDot (hD : DotSpec) {s z h u w : MachineState} {i : Nat}
    {sd : List BusBlock × BusLayoutRust × List E × List E × E} {point : List E} {q : Word}
    (hpre : BusBalancePre s) (hsz : heapNext s ≤ heapNext z) (Ih : Inv s h)
    (F : Front s z h u i sd point) (S : Shifted s z h u w i sd q) (hpc : w.pc = 0x80007788) :
    ∃ t, Reaches Image.code w t ∧ (Dead Image.code t ∨
      (t.pc = 0x8000779c ∧ Dotted s z h u t i sd point)) := by
  obtain ⟨hb1, -, -, -⟩ := bounds hpre
  have hval : ValidMemRange (s.getReg .x2 - 4544) 568 := hpre.stack.valid
  have hnx := hpre.stack.next
  rw [stackLo_eq] at hnx
  have Cw := S.cur
  have spw : w.getReg .x2 = s.getReg .x2 - 1344 := Cw.inv.sp
  have hhu := F.cur.step.mono
  have huw := S.mono
  -- `0x80007788`
  obtain ⟨w₁, hr₁, h₁⟩ := Sym.BlockSpec.reaches b80007788_spec hpc (by
    rv_eval [spw]; valid_access hval [hb1])
  have m₁ := b80007788_mem_same h₁
  have k₁ := b80007788_keeps h₁
  have hn₁ : heapNext w₁ = heapNext w := by simp only [heapNext, m₁]
  have C₁ : Cur s z h w₁ := Cw.next hpre hsz (A := fun _ ↦ False)
    (StepS.same m₁ Cw.inv.heap (k₁ .x2 (by decide))) fun _ h ↦ h.elim
  have hwE := Cw.inv.heap.hi
  have m1288 : w.getMem (s.getReg .x2 - 1288) = u.getMem (s.getReg .x2 - 1288) :=
    S.fr _ fun k hk hw ↦ by
      rcases hw with hw | hw | hw | ⟨-, a2⟩
      · addr_omega [hw, hk, hb1]
      · addr_omega [hw, hk, hb1]
      · addr_omega [hw, hk, hb1, hnx]
      · simp only [heapNext, heapEnd] at a2 hwE; addr_omega [a2, hk, hb1, hwE]
  have hfb := F.fwBuf
  have hlo := Ih.heap.lo
  have hnf : (BitVec.ofNat 64 sd.2.1.framework.length).toNat = sd.2.1.framework.length := by
    rw [BitVec.toNat_ofNat]; apply Nat.mod_eq_of_lt
    rcases hfb.2 with h0 | ⟨-, b2⟩
    · omega
    · have := F.cur.inv.heap.hi; simp only [heapNext, heapEnd] at b2 this; omega
  have x12₁ : w₁.getReg .x12 = BitVec.ofNat 64 sd.2.1.framework.length := by
    rw [b80007788_x12 h₁, spw]; rv_eval []; rw [m1288]; exact F.m1288
  have x11₁ : w₁.getReg .x11 = u.getReg .x24 := by
    rw [b80007788_x11 h₁, S.regs .x24 (by decide)]
  have x13₁ : w₁.getReg .x13 = q := by rw [k₁ .x13 (by decide), S.x13]
  have x14₁ : w₁.getReg .x14 = sideWord s h i 16 := by rw [k₁ .x14 (by decide), S.x14]
  have hl : LowBuf (w₁.getReg .x11) (24 * (w₁.getReg .x12).toNat) (heapNext w₁) := by
    rw [x11₁, x12₁, hnf, hn₁]
    refine ⟨hfb.1, ?_⟩
    rcases hfb.2 with h0 | ⟨b1, b2⟩
    · exact Or.inl h0
    · exact Or.inr ⟨by omega, by omega⟩
  have hr' : LowBuf (w₁.getReg .x13) (24 * (w₁.getReg .x14).toNat) (heapNext w₁) := by
    rw [x13₁, x14₁, hn₁]
    have hb := S.buf
    refine ⟨hb.1, ?_⟩
    rcases hb.2 with h0 | ⟨b1, b2⟩
    · exact Or.inl h0
    · exact Or.inr ⟨by omega, b2⟩
  -- `dot`
  obtain ⟨t, hrt, ⟨hpct, hpt, Ct, frt, hnt, hlen, hv⟩ | hd⟩ := dotCallC hD hpre hsz C₁
    (Reaches.refl _) (b80007788_pc h₁) (by rw [b80007788_x10 h₁, spw]; rv_eval []) hl hr'
  swap
  · exact ⟨t, hr₁.trans hrt, Or.inl hd⟩
  refine ⟨t, hr₁.trans hrt, Or.inr ⟨by rw [hpct, returnAddress_eq, b80007788_x1 h₁]; decide,
    Ct, ?_, fun r hr ↦ ?_, ?_, ?_, ?_⟩⟩
  · refine ((S.fr.mono fun a ha ↦ ?_).trans (DFrame.of_same m₁ _) fun _ h ↦ h).trans
      (frt.mono fun a ha ↦ ?_) fun _ h ↦ h
    · rcases ha with ha | ha | ha | ⟨a1, a2⟩
      · exact Or.inl (by addr_omega [ha, hb1])
      · exact Or.inr (Or.inl ha)
      · exact Or.inr (Or.inr (Or.inl ha))
      · exact Or.inr (Or.inr (Or.inr ⟨a1, by rw [hnt, hn₁]; exact a2⟩))
    · rcases ha with ha | ha
      · exact Or.inl (by addr_omega [ha, hb1])
      · exact Or.inr (Or.inl (by addr_omega [ha, hb1]))
  · rw [hpt.reg r (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide),
      k₁ r (mem_of_mem hr _), S.regs r hr]
  · rw [hpt.reg .x9, k₁ .x9 (by decide), S.x9]
  · rw [hpt.reg .x18, k₁ .x18 (by decide), S.x18]
  · rw [hv, x11₁, x12₁, x13₁, hnf]
    have hlen' : sd.2.1.framework.length = (sideWord s h i 16).toNat := by
      rw [← hnf, ← x12₁, hlen, x14₁]
    have e1 : eListAt w₁ (u.getReg .x24) sd.2.1.framework.length =
        sd.2.1.framework.map (·.eqAbove point) := by
      rw [eListAt_congr fun j _ ↦ eAt_congr (m₁ _) (m₁ _) (m₁ _), ← F.fw]
      refine S.fr.eListAt fun k hk hw ↦ ?_
      rcases hfb.2 with h0 | ⟨b1, b2⟩
      · omega
      have hh := F.cur.inv.heap.hi
      simp only [heapNext, heapEnd, heapStart] at b1 b2 hh hlo
      rcases hw with hw | hw | hw | ⟨a1, -⟩
      · addr_omega [hw, hk, hb1, b1, b2, hh]
      · addr_omega [hw, hk, hb1, b1, b2, hh]
      · simp only [nextAddr] at hw; addr_omega [hw, hk, b1, b2, hh, hlo]
      · simp only [heapNext] at a1; addr_omega [a1, hk, b1, b2, hh]
    have e2 : eListAt w₁ q sd.2.1.framework.length = sd.2.2.1.map (sd.2.2.2.2 + ·) := by
      rw [eListAt_congr fun j _ ↦ eAt_congr (m₁ _) (m₁ _) (m₁ _), hlen', S.vals]
    rw [e1, e2]

end Rv64Verifier.Proofs.Bus.VerifyBusBalance
