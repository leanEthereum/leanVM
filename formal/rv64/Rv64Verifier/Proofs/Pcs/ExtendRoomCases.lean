import Rv64Verifier.Proofs.Pcs.ExtendRoom

/-!
# `Vec<StackClaim>::extend_desugared`: room, with or without `grow_amortized`

`room_nogrow`: the `Vec` not full. `room_grow`: full, `grow_amortized(self, len, 1, 8, 88)` at
`0x80009d58` moves it to a new buffer holding the old one's bytes.
-/

namespace Rv64Verifier.Proofs.Pcs.Extend
open RiscvZkvm.Rv64 Rv64Verifier.Runtime Rv64Verifier.Transcript Rv64Verifier.Pcs
  Rv64Verifier.PcsContracts Rv64Verifier.Model.Pcs Rv64Verifier.Blocks.F37 LeanVM.Parameters
open Rv64Verifier.Sym (reduceReg reducePc reduceMem reduceWrites reduceObl)

theorem room_nogrow {s u w : MachineState} {k : Nat} (hp : Push s u k) (hB : Base s u w k)
    (h0 : w.getMem (s.getReg .x10) = u.getMem (s.getReg .x10))
    (h8 : w.getMem (s.getReg .x10 + 8) = u.getMem (s.getReg .x10 + 8)) (hpc : w.pc = 0x80009bf8)
    (hne : vecLen u (s.getReg .x10) ≠ vecCap u (s.getReg .x10)) : Room s u w k := by
  have hI := hp.inv
  have hP : vecPtr w (s.getReg .x10) = vecPtr u (s.getReg .x10) := h8
  have hC : vecCap w (s.getReg .x10) = vecCap u (s.getReg .x10) := h0
  have hl := hI.vec.len
  have hne' : (vecLen u (s.getReg .x10)).toNat ≠ (vecCap u (s.getReg .x10)).toNat :=
    fun h ↦ hne (BitVec.eq_of_toNat_eq h)
  have hraw := hI.vec.raw
  simp only [RawVecOk, Buf] at hraw
  have hm := hB.mono
  have hpb := hB.pt.buf
  simp only [NewBuf] at hpb
  refine ⟨hB, hpc, by rw [hC]; omega, ?_, ?_, Or.inl ⟨hP, hC⟩⟩
  · simp only [RawVecOk, Buf, hP, hC]; omega
  · simp only [Apart, hP, hC]; omega

theorem room_grow (hG : GrowSpec) {s u w : MachineState} {k : Nat} (hpre : ExtendPre s)
    (hp : Push s u k) (hB : Base s u w k)
    (h0 : w.getMem (s.getReg .x10) = u.getMem (s.getReg .x10))
    (h8 : w.getMem (s.getReg .x10 + 8) = u.getMem (s.getReg .x10 + 8)) (hpc : w.pc = 0x80009d58)
    (hfull : vecLen u (s.getReg .x10) = vecCap u (s.getReg .x10)) :
    ∃ v, Reaches Image.code w v ∧ (Dead Image.code v ∨ Room s u v k) := by
  have hI := hp.inv
  have hb := sbounds hpre
  have hst := hpre.stack
  have hA := hpre.self
  have hAb := Region.bounds hA.region
  have hAs := hA.stack
  rw [hK] at hAs
  have hAf := hA.free
  simp only [Outside] at hAf
  have hu' : heapNext s ≤ heapNext u := hI.p.mono
  have hP : vecPtr w (s.getReg .x10) = vecPtr u (s.getReg .x10) := h8
  have hC : vecCap w (s.getReg .x10) = vecCap u (s.getReg .x10) := h0
  have hraw := hI.vec.raw
  simp only [RawVecOk, Buf] at hraw
  have hwm := hB.mono
  have hwh := hB.heap.hi
  obtain ⟨t₆, hr₆, h₆⟩ := Sym.BlockSpec.reaches b80009d58_spec hpc (by rv_eval [])
  have k₆ := b80009d58_keeps h₆
  have m₆ := b80009d58_mem_same h₆
  have hn₆ : heapNext t₆ = heapNext w := by simp only [heapNext, m₆]
  have x9w : w.getReg .x9 = s.getReg .x10 := (hB.keep .x9 (by decide)).trans hI.x9
  have x10₆ : t₆.getReg .x10 = s.getReg .x10 := (b80009d58_x10 h₆).trans x9w
  have hsp₆ : t₆.getReg .x2 = s.getReg .x2 - BitVec.ofNat 64 240 := (k₆ .x2 (by decide)).trans hB.sp
  have hsl : stackLo t₆ growStack = s.getReg .x2 - 384 := by
    simp only [stackLo, hsp₆]; addr_omega [hb]
  have hP₆ : vecPtr t₆ (s.getReg .x10) = vecPtr u (s.getReg .x10) := by
    simp only [vecPtr, m₆]; exact h8
  have hC₆ : vecCap t₆ (s.getReg .x10) = vecCap u (s.getReg .x10) := by
    simp only [vecCap, m₆]; exact h0
  have hpreG : GrowPre t₆ := {
    heap := ⟨by rw [hn₆]; exact hB.heap.lo, by rw [hn₆]; exact hwh⟩
    self := by rw [x10₆]; exact Region.vrange hA.region (Nat.le_refl _) (by omega) hAb.2.2
    align := by rw [b80009d58_x13 h₆]; decide
    size := by rw [b80009d58_x14 h₆]; decide
    raw := by
      rw [x10₆, b80009d58_x13 h₆, b80009d58_x14 h₆]
      have h88 : (88 : Word).toNat = 88 := rfl
      have h8' : (8 : Word).toNat = 8 := rfl
      simp only [RawVecOk, Buf, hP₆, hC₆, hn₆, h88, h8']
      exact ⟨hraw.1, by omega⟩
    stack := hst.sub 240 hsp₆ (by decide) (by decide) (by decide) (by decide) (by decide)
    selfFree := by
      rw [x10₆]; simp only [Outside, hn₆]
      exact ⟨by omega, by addr_omega [hAf.2]⟩
    selfStack := by rw [x10₆, hsl]; addr_omega [hAs, hAb, hb] }
  obtain ⟨t₇, hr₇, ⟨hpc₇, hpres₇, hpost₇⟩ | hdead⟩ := hG.call hr₆ (b80009d58_pc h₆) hpreG
  swap
  · exact ⟨t₇, hr₇, Or.inl hdead⟩
  have kp (r : Reg) (hr : r ∈ calleeSaved) : t₇.getReg r = t₆.getReg r := hpres₇ r hr
  have x23₇ : t₇.getReg .x23 = 0xffffffffffffffff := by
    rw [kp .x23 (by decide), k₆ .x23 (by decide), hB.keep .x23 (by decide), hI.x23]
  obtain ⟨t₈, hr₈, h₈⟩ := Sym.BlockSpec.reaches b80009d74_spec
    (by rw [hpc₇, returnAddress_eq, b80009d58_x1 h₆]; decide) (by rv_eval [])
  by_cases hok : t₇.getReg .x10 = 0xffffffffffffffff
  swap
  · refine ⟨t₈, hr₇.trans hr₈, Or.inl (dead_of_fetch ?_)⟩
    rw [b80009d74_pc_not_taken h₈ (by rw [x23₇]; exact hok)]
    exact htrap
  have m₈ := b80009d74_mem_same h₈
  have k₈ := b80009d74_keeps h₈
  have h88 : (88 : Word).toNat = 88 := rfl
  have h8' : (8 : Word).toNat = 8 := rfl
  obtain ⟨hcap, hraw₇, hby⟩ := hpost₇.ok hok
  have hfr := hpost₇.fresh hok
  have h1' : (1 : Word).toNat = 1 := rfl
  rw [x10₆, b80009d58_x11 h₆, b80009d58_x12 h₆, hB.x18, h1'] at hcap
  rw [x10₆, b80009d58_x13 h₆, b80009d58_x14 h₆, h88, h8'] at hraw₇ hfr
  rw [x10₆, b80009d58_x14 h₆, h88, hP₆, hC₆] at hby
  have hgf := DFrame.of_byteFrame hpost₇.frame
  rw [x10₆, hsl] at hgf
  have hW8 : DFrame w t₈ fun a ↦ Within a (s.getReg .x10) 16 ∨ Within a (s.getReg .x2 - 384) growStack ∨
      Within a nextAddr 8 ∨ Fresh t₆ t₇ a :=
    ((DFrame.of_same m₆ _).trans hgf fun _ h ↦ h).trans (DFrame.of_same m₈ _) fun _ h ↦ h
  have hn₈ : heapNext t₈ = heapNext t₇ := by simp only [heapNext, m₈]
  have hm7 := hpost₇.mono
  have hh7 := hpost₇.heap.hi
  rw [hn₆] at hm7
  have hlo7 := hpost₇.heap.lo
  have hstk (a : Word) (h1 : (s.getReg .x2).toNat - 240 ≤ a.toNat) (h2 : a.toNat + 8 ≤ (s.getReg .x2).toNat) :
      t₈.getMem a = w.getMem a :=
    hW8.word (fun x hx hw ↦ by
      rcases hw with hw | hw | hw | hw
      · addr_omega [hx, hw, hAs, hAb, h1, h2, hb]
      · addr_omega [hx, hw, h1, h2, hb]
      · addr_omega [hx, hw, h1, h2, hb]
      · simp only [Fresh] at hw; addr_omega [hx, hw.2, hh7, h1, h2, hb]) (by omega)
  have hP₈ : vecPtr t₈ (s.getReg .x10) = vecPtr t₇ (s.getReg .x10) := m₈ _
  have hC₈ : vecCap t₈ (s.getReg .x10) = vecCap t₇ (s.getReg .x10) := m₈ _
  have hL₈ : vecLen t₈ (s.getReg .x10) = vecLen w (s.getReg .x10) :=
    hW8.word (fun x hx hw ↦ by
      rcases hw with hw | hw | hw | hw
      · addr_omega [hx, hw, hAb]
      · addr_omega [hx, hw, hAs, hAb, hb]
      · addr_omega [hx, hw, hAf.2, hAb]
      · simp only [Fresh] at hw; addr_omega [hx, hw.1, hw.2, hh7, hAf.1, hu', hwm, hAb, hn₆]) (by addr_omega [hAb])
  have hpb := hB.pt.buf
  have hpv := hB.pt.vec
  simp only [NewBuf] at hpb
  have hS0 : t₈.getMem (s.getReg .x2 - 184) = w.getMem (s.getReg .x2 - 184) := hstk _ (by addr_omega [hb]) (by addr_omega [hb])
  have hS8 : t₈.getMem (s.getReg .x2 - 184 + 8) = w.getMem (s.getReg .x2 - 184 + 8) := hstk _ (by addr_omega [hb]) (by addr_omega [hb])
  refine ⟨t₈, hr₇.trans hr₈, Or.inr ⟨⟨?_, fun r hr ↦ ?_, ?_, ?_, ⟨by rw [hn₈]; exact hlo7, by rw [hn₈]; exact hh7⟩,
    by rw [hn₈]; omega, ?_, ?_, ?_, by rw [hL₈]; exact hB.len⟩,
    b80009d74_pc_taken h₈ (by rw [x23₇]; exact hok), by rw [hC₈]; omega, ?_, ?_, Or.inr ⟨?_, ?_⟩⟩⟩
  · rw [k₈ .x2 (by decide), kp .x2 (by decide), hsp₆]; rfl
  · rw [k₈ r ((by decide : [Reg.x8, .x9, .x19, .x20, .x21, .x22, .x23, .x24] ⊆ _) hr),
      kp r ((by decide : [Reg.x8, .x9, .x19, .x20, .x21, .x22, .x23, .x24] ⊆ calleeSaved) hr),
      keeps_sub k₆ (by decide) r hr]
    exact hB.keep r hr
  · rw [k₈ .x25 (by decide), kp .x25 (by decide), k₆ .x25 (by decide), hB.x25]
  · rw [k₈ .x18 (by decide), kp .x18 (by decide), k₆ .x18 (by decide), hB.x18]
  · refine ((hB.fr.mono fun a h ↦ h.mono (by rw [← hn₈] at hm7; exact hm7)).trans hW8
      fun a h ↦ ?_)
    rcases h with h | h | h | h
    · exact Or.inl (by addr_omega [h])
    · exact Or.inr (Or.inr (Or.inl (by rw [hK]; addr_omega [h, hb])))
    · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
    · simp only [Fresh] at h
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨by omega, by rw [← hn₈] at h; exact h.2⟩))))
  · refine NewVecE.frame hB.pt hW8 (by rw [hn₈]; omega) (fun x hx hw ↦ ?_) (by addr_omega [hb])
      fun x hx hw ↦ ?_
    · rcases hw with hw | hw | hw | hw
      · addr_omega [hx, hw, hAs, hAb, hb]
      · addr_omega [hx, hw, hb]
      · addr_omega [hx, hw, hb]
      · simp only [Fresh] at hw; addr_omega [hx, hw.2, hh7, hb]
    · rcases hpb with ⟨-, h0 | ⟨h1, h2⟩⟩
      · simp only [Within] at hx; omega
      · rcases hw with hw | hw | hw | hw
        · addr_omega [hx, hw, hAf.1, hu', h1, h2, hwh, hAb]
        · addr_omega [hx, hw, h2, hwh, hb]
        · addr_omega [hx, hw, h2, hwh]
        · simp only [Fresh] at hw; rw [hn₆] at hw; addr_omega [hx, hw.1, h2]
  · rw [← hB.val]
    exact hW8.eAt' (fun x hx hw ↦ by
      rcases hw with hw | hw | hw | hw
      · addr_omega [hx, hw, hAs, hAb, hb]
      · addr_omega [hx, hw, hb]
      · addr_omega [hx, hw, hb]
      · simp only [Fresh] at hw; addr_omega [hx, hw.2, hh7, hb]) (by addr_omega [hb])
  · simp only [RawVecOk, Buf, hP₈, hC₈, hn₈]; exact hraw₇
  · rw [show vecPtr t₈ (s.getReg .x2 - 184) = vecPtr w (s.getReg .x2 - 184) from hS8,
      show vecCap t₈ (s.getReg .x2 - 184) = vecCap w (s.getReg .x2 - 184) from hS0]
    simp only [Apart, hP₈, hC₈]
    rcases hfr with ⟨-, hf0 | ⟨hf1, hf2⟩⟩
    · omega
    · rw [hn₆] at hf1; omega
  · simp only [NewBuf, hP₈, hC₈, hn₈] at hfr ⊢
    omega
  · intro i hi j hj
    rw [hfull] at hi
    have hsafe := (hI.safe i (by rw [hfull]; exact hi)).1
    have hsb : (vecPtr u (s.getReg .x10) + BitVec.ofNat 64 (88 * i)).toNat + 88 ≤ 0xc0000000 := by
      rcases hsafe.bound with h | h
      · omega
      · exact h
    rw [m₈, hP₈, add_ofNat_add, add_ofNat_add,
      getMem_eq_of_bytesAt hby hfr.1 hraw.1 (by omega) (by omega), m₆]
    refine hB.fr.word (fun x hx ↦ hsafe.miss hwh x ?_) ?_
    · rw [← add_ofNat_add] at hx; addr_omega [hx, hsb, hj]
    · rw [← add_ofNat_add]; addr_omega [hsb, hj]

end Rv64Verifier.Proofs.Pcs.Extend
