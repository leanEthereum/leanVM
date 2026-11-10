import Rv64Verifier.Proofs.Bus.VbbTail40

/-!
# `verify_bus_balance`'s side loop: the shifted fingerprints' loop

The loop at `0x8000774c` stores each of the `n` framework fingerprints from `fp`, its limbs XORed
with `beta`'s, 24 bytes apart from `q`: `beta + f` (`eOf3_xor`, `ShI`, `shIter`, `shLoop`).
-/

namespace Rv64Verifier.Proofs.Bus.VerifyBusBalance
open RiscvZkvm.Rv64 LeanVM.Parameters LeanVM.Protocol.Verifier Rv64Verifier.Runtime
  Rv64Verifier.Model Rv64Verifier.Bus Rv64Verifier.Transcript Rv64Verifier.Blocks.F26
open Rv64Verifier.Sym (reduceReg reducePc reduceMem reduceWrites reduceObl)

theorem limbs_eOf3' (a b c : Word) : Model.limbs (eOf3 a b c) = (a, b, c) := rfl

theorem eOf3_xor (a b c x y w : Word) :
    eOf3 (a ^^^ x) (b ^^^ y) (c ^^^ w) = eOf3 a b c + eOf3 x y w :=
  eq_of_limbs (by rw [limbs_add, limbs_eOf3', limbs_eOf3', limbs_eOf3'])

theorem eAt_eq_eOf3 (t : MachineState) (a : Word) :
    eAt t a = eOf3 (t.getMem a) (t.getMem (a + 8)) (t.getMem (a + 16)) := rfl

/-- In the loop at `0x8000774c` from `v`: `k` of the `n` fingerprints `fps` from `fp`, each plus
`beta`, stored from `q`. -/
structure ShI (s z h v t : MachineState) (fp q : Word) (n : Nat) (fps : List E) (beta : E)
    (k : Nat) : Prop where
  cur : Cur s z h t
  fr : DFrame v t (Within · q (24 * n))
  next : heapNext t = heapNext v
  regs : ∀ r ∈ ([.x2, .x8, .x9, .x11, .x13, .x14, .x18, .x20, .x21, .x24, .x25, .x26, .x27] :
    List Reg), t.getReg r = v.getReg r
  x22 : t.getReg .x22 = fp + BitVec.ofNat 64 (24 * k + 16)
  x10 : t.getReg .x10 = q + BitVec.ofNat 64 (24 * k + 16)
  vals : eListAt t q k = (fps.take k).map (beta + ·)

set_option maxRecDepth 8192 in
/-- One iteration. -/
theorem shIter {s z h v t : MachineState} {fp q : Word} {n : Nat} {fps : List E} {beta : E}
    {k : Nat} (hpre : BusBalancePre s) (hsz : heapNext s ≤ heapNext z) (Ih : Inv s h)
    (hzh : heapNext z ≤ heapNext h)
    (hfp : fp.toNat % 8 = 0 ∧ heapStart ≤ fp.toNat ∧ fp.toNat + 24 * n ≤ heapNext z)
    (hq : q.toNat % 8 = 0 ∧ heapNext h ≤ q.toNat ∧ q.toNat + 24 * n ≤ heapNext v)
    (hfps : eListAt h fp n = fps)
    (hbeta : eOf3 (v.getReg .x26) (v.getReg .x9) (v.getReg .x18) = beta)
    (hx11 : v.getReg .x11 = fp + BitVec.ofNat 64 (24 * n + 16))
    (S : ShI s z h v t fp q n fps beta k) (hk : k < n) (hpc : t.pc = 0x8000774c) :
    ∃ t', Reaches Image.code t t' ∧ ShI s z h v t' fp q n fps beta (k + 1) ∧
      ((k + 1 < n ∧ t'.pc = 0x8000774c) ∨ (k + 1 = n ∧ t'.pc = 0x8000777c)) := by
  obtain ⟨hb1, -, -, -⟩ := bounds hpre
  have hnx := hpre.stack.next
  rw [stackLo_eq] at hnx
  have It := S.cur.inv
  have htE := It.heap.hi
  have hhl := Ih.heap.lo
  have hnt := S.next
  have hht := S.cur.step.mono
  obtain ⟨F8, Fl, Fh⟩ := hfp
  obtain ⟨Q8, Qh, Qv⟩ := hq
  simp only [heapNext, heapEnd, heapStart] at htE hhl hnt Fl Fh Qh Qv hzh hht
  have hvF : ValidMemRange fp (3 * n) :=
    heapRange F8 (by simp only [heapStart]; omega) (by simp only [heapEnd]; omega)
  have hvQ : ValidMemRange q (3 * n) :=
    heapRange Q8 (by simp only [heapStart]; omega) (by simp only [heapEnd]; omega)
  have x10 := S.x10
  have x22 := S.x22
  obtain ⟨t', hr, hh⟩ := Sym.BlockSpec.reaches b8000774c_spec hpc (by
    rv_eval [x10, x22]
    and_intros <;> first
      | valid_access hvF [Fl, Fh, hk, htE, hzh]
      | valid_access hvQ [Qh, Qv, hk, htE, hnt])
  have kt := b8000774c_keeps hh
  have hqk : (q + BitVec.ofNat 64 (24 * k)).toNat = q.toNat + 24 * k := by
    addr_omega [Qv, hk, htE, hnt]
  have fr' : DFrame t t' (Within · (q + BitVec.ofNat 64 (24 * k)) 24) := by
    have := DFrame.of_memFrame (b8000774c_frame hh (by rw [x10]; addr_omega [Qv, hk, htE, hnt]))
    rw [x10] at this
    exact this.mono fun a ha ↦ by addr_omega [ha, Qv, hk, htE, hnt]
  have nx : ∀ i < 8, ¬ Within (nextAddr + BitVec.ofNat 64 i) (q + BitVec.ofNat 64 (24 * k)) 24 :=
    fun i hi hw ↦ by simp only [nextAddr] at hw; addr_omega [hw, hi, hqk, Qh, Qv, hk, htE, hnt, hhl]
  have st : StepS s t t' (Within · (q + BitVec.ofNat 64 (24 * k)) 24) :=
    StepS.ofDFrame It.heap fr' (fun _ h ↦ h) nx (kt .x2 (by decide))
  have hn' : heapNext t' = heapNext t := by
    simp only [heapNext]; exact congrArg BitVec.toNat (fr' nextAddr nx)
  have C' : Cur s z h t' := S.cur.next hpre hsz st fun a ha ↦ Or.inr ⟨by
      simp only [heapNext]; addr_omega [ha, hqk, Qh, hzh],
    by rw [hn']; simp only [heapNext]; addr_omega [ha, hqk, Qv, hk, hnt]⟩
  have r (x : Reg) (hx : x ∈ ([.x2, .x8, .x9, .x11, .x13, .x14, .x18, .x20, .x21, .x24, .x25, .x26,
      .x27] : List Reg)) : t'.getReg x = v.getReg x := by
    have hx' : x ∈ ([.x1, .x2, .x3, .x4, .x5, .x6, .x7, .x8, .x9, .x11, .x13, .x14, .x17, .x18,
        .x19, .x20, .x21, .x23, .x24, .x25, .x26, .x27, .x28, .x29, .x30, .x31] : List Reg) := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx ⊢
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        simp
    rw [kt x hx', S.regs x hx]
  -- the new element
  have e0 := b8000774c_m_x10_n16 hh
  have e8 := b8000774c_m_x10_n8 hh
  have e16 := b8000774c_m_x10_0 hh
  have a0 : t.getReg .x10 - 16 = q + BitVec.ofNat 64 (24 * k) := by
    rw [x10]; apply BitVec.eq_of_toNat_eq; addr_omega [Qv, hk, htE, hnt]
  have a8 : t.getReg .x10 - 8 = q + BitVec.ofNat 64 (24 * k) + 8 := by
    rw [x10]; apply BitVec.eq_of_toNat_eq; addr_omega [Qv, hk, htE, hnt]
  have a16 : t.getReg .x10 = q + BitVec.ofNat 64 (24 * k) + 16 := by
    rw [x10]; apply BitVec.eq_of_toNat_eq; addr_omega [Qv, hk, htE, hnt]
  have f0 : t.getReg .x22 - 16 = fp + BitVec.ofNat 64 (24 * k) := by
    rw [x22]; apply BitVec.eq_of_toNat_eq; addr_omega [Fh, hk, htE, hzh, hht]
  have f8 : t.getReg .x22 - 8 = fp + BitVec.ofNat 64 (24 * k) + 8 := by
    rw [x22]; apply BitVec.eq_of_toNat_eq; addr_omega [Fh, hk, htE, hzh, hht]
  have f16 : t.getReg .x22 = fp + BitVec.ofNat 64 (24 * k) + 16 := by
    rw [x22]; apply BitVec.eq_of_toNat_eq; addr_omega [Fh, hk, htE, hzh, hht]
  rw [a0, f0] at e0
  rw [a8, f8] at e8
  rw [a16, f16] at e16
  have rdF (j : Nat) (hj : j + 8 ≤ 24) :
      t.getMem (fp + BitVec.ofNat 64 (24 * k) + BitVec.ofNat 64 j) =
        h.getMem (fp + BitVec.ofNat 64 (24 * k) + BitVec.ofNat 64 j) :=
    S.cur.low hpre Ih (by simp only [heapNext]; omega)
      (by simp only [heapStart]; addr_omega [Fl, Fh, hk, hj])
      (by simp only [heapNext]; addr_omega [Fl, Fh, hk, hj])
  have hfk : fps[k]'(by rw [← hfps, eListAt_length]; exact hk) =
      eAt t (fp + BitVec.ofNat 64 (24 * k)) := by
    subst hfps
    rw [eListAt_getElem]
    exact (eAt_congr (by simpa using rdF 0 (by omega)) (rdF 8 (by omega)) (rdF 16 (by omega))).symm
  have hnew : eAt t' (q + BitVec.ofNat 64 (24 * k)) = beta + fps[k]'(by
      rw [← hfps, eListAt_length]; exact hk) := by
    rw [hfk, eAt_eq_eOf3 t', e0, e8, e16, S.regs .x26 (by decide), S.regs .x9 (by decide),
      S.regs .x18 (by decide), eOf3_xor, hbeta, add_comm]
    rfl
  have hold : eListAt t' q k = eListAt t q k :=
    fr'.eListAt fun i hi hw ↦ by addr_omega [hw, hi, hqk, Qv, hk, htE, hnt]
  have hlen : k < fps.length := by rw [← hfps, eListAt_length]; exact hk
  refine ⟨t', hr, ⟨C', S.fr.trans fr' fun a ha ↦ by addr_omega [ha, hqk, Qv, hk, htE, hnt],
    hn'.trans S.next, r, ?_, ?_, ?_⟩, ?_⟩
  · rw [b8000774c_x22 hh, x22]; apply BitVec.eq_of_toNat_eq; addr_omega [Fh, hk, htE, hzh, hht]
  · rw [b8000774c_x10 hh, x10]; apply BitVec.eq_of_toNat_eq; addr_omega [Qv, hk, htE, hnt]
  · rw [eListAt_succ, hold, S.vals, hnew, List.take_add_one, List.getElem?_eq_getElem hlen]
    simp only [Option.toList_some, List.map_append, List.map_cons, List.map_nil]
  · have x11t : t.getReg .x11 = fp + BitVec.ofNat 64 (24 * n + 16) := by
      rw [S.regs .x11 (by decide), hx11]
    rcases Nat.lt_or_ge (k + 1) n with hlt | hge
    · refine Or.inl ⟨hlt, b8000774c_pc_taken hh ?_⟩
      rw [x22, x11t]; intro he
      have := congrArg BitVec.toNat he
      addr_omega [this, Fh, hk, hlt, htE, hzh, hht]
    · refine Or.inr ⟨by omega, b8000774c_pc_not_taken hh ?_⟩
      rw [x22, x11t]; apply BitVec.eq_of_toNat_eq
      addr_omega [Fh, hk, hge, htE, hzh, hht]

/-- The loop, from `k` of `n` to the last. -/
theorem shLoop {s z h v : MachineState} {fp q : Word} {n : Nat} {fps : List E} {beta : E}
    (hpre : BusBalancePre s) (hsz : heapNext s ≤ heapNext z) (Ih : Inv s h)
    (hzh : heapNext z ≤ heapNext h)
    (hfp : fp.toNat % 8 = 0 ∧ heapStart ≤ fp.toNat ∧ fp.toNat + 24 * n ≤ heapNext z)
    (hq : q.toNat % 8 = 0 ∧ heapNext h ≤ q.toNat ∧ q.toNat + 24 * n ≤ heapNext v)
    (hfps : eListAt h fp n = fps)
    (hbeta : eOf3 (v.getReg .x26) (v.getReg .x9) (v.getReg .x18) = beta)
    (hx11 : v.getReg .x11 = fp + BitVec.ofNat 64 (24 * n + 16)) :
    ∀ d k t, k + d + 1 = n → ShI s z h v t fp q n fps beta k → t.pc = 0x8000774c →
      ∃ t', Reaches Image.code t t' ∧ ShI s z h v t' fp q n fps beta n ∧ t'.pc = 0x8000777c := by
  intro d
  induction d with
  | zero =>
    intro k t hk S hpc
    obtain ⟨t', hr, S', ⟨hlt, -⟩ | ⟨he, hpc'⟩⟩ :=
      shIter hpre hsz Ih hzh hfp hq hfps hbeta hx11 S (by omega) hpc
    · omega
    · rw [he] at S'; exact ⟨t', hr, S', hpc'⟩
  | succ d ih =>
    intro k t hk S hpc
    obtain ⟨t', hr, S', ⟨-, hpc'⟩ | ⟨he, -⟩⟩ :=
      shIter hpre hsz Ih hzh hfp hq hfps hbeta hx11 S (by omega) hpc
    · obtain ⟨t'', hr', S'', hpc''⟩ := ih (k + 1) t' (by omega) S' hpc'
      exact ⟨t'', hr.trans hr', S'', hpc''⟩
    · omega

end Rv64Verifier.Proofs.Bus.VerifyBusBalance
