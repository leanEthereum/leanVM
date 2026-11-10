import Rv64Verifier.Proofs.Bytecode.EvalAdds

/-!
# `Bytecode::evaluate`: a block's words

`adds`: from `AInv`, the eight buckets (`EvalAdds.lean`), then the next word (`WInv`) or the
block's end (`Mid`). `words_loop`: from `WInv`, every word of the block (`word_start`,
`sum_loop`, `adds`).
-/

namespace Rv64Verifier.Proofs.Bytecode.Eval
open RiscvZkvm.Rv64 LeanVM.Parameters Rv64Verifier.Runtime Rv64Verifier.Contracts
  Rv64Verifier.Model Rv64Verifier.Blocks.F84
open Rv64Verifier.Sym (reduceReg reducePc reduceMem reduceWrites reduceObl)

variable {e : Env}

/-- `Blk` over a step that writes only buckets and keeps the registers it names. -/
theorem Blk.of_bk (he : EnvOk e) {t t' : MachineState} {i : Nat} (hb : Blk e t i)
    (hm : ∀ a, ¬ Within a e.bk 49152 → t'.getMem a = t.getMem a)
    (hr : ∀ r ∈ [Reg.x2, .x9, .x11, .x18, .x20, .x21, .x23], t'.getReg r = t.getReg r) :
    Blk e t' i := by
  have hsp := he.sp
  have hbk := he.bkIn
  have hh := he.heapL.hi
  simp only [heapNext, heapEnd] at hbk hh
  exact {
    sp := (hr .x2 (by decide)).trans hb.sp
    mem := hb.mem.frame fun a ha ↦ hm a fun hw ↦ ha (Or.inr (Or.inr (Or.inr hw)))
    x9 := (hr .x9 (by decide)).trans hb.x9
    x18 := by rw [hr .x18 (by decide)]; exact hb.x18
    x20 := (hr .x20 (by decide)).trans hb.x20
    x21 := (hr .x21 (by decide)).trans hb.x21
    x23 := (hr .x23 (by decide)).trans hb.x23
    lt := hb.lt
    ptr := by rw [hm _ (by addr_omega [hsp, hbk, hh])]; exact hb.ptr
    we := by rw [hm _ (by addr_omega [hsp, hbk, hh])]; exact hb.we
    total := by
      rw [hm _ (by addr_omega [hsp, hbk, hh]), hm _ (by addr_omega [hsp, hbk, hh]),
        hm _ (by addr_omega [hsp, hbk, hh])]
      exact hb.total
    bs := by rw [hr .x11 (by decide)]; exact hb.bs
    wsle := hb.wsle
    wele := hb.wele }

set_option maxHeartbeats 2000000 in
/-- The eight buckets of word `j`, then the next word or the block's end. -/
theorem adds (he : EnvOk e) {t : MachineState} {i j : Nat} (ha : AInv e t i j)
    (hpc : t.pc = 0x80011150) :
    ∃ u, Reaches Image.code t u ∧ (Dead Image.code u ∨ (u.pc = 0x800110d0 ∧ WInv e u i (j + 1)) ∨
      (u.pc = 0x8001136c ∧ Mid e u i)) := by
  generalize hw : (e.wd j).1 = w
  generalize hsum : memberSumRust e.lowW ((e.bc.positions.drop (e.ps i j)).take
    ((e.wd j).2 - e.ps i j)) = sum
  have hacc := ha.acc
  rw [hsum] at hacc
  have h17 : t.getReg .x17 = w := ha.x17.trans hw
  obtain ⟨u₀, hr₀, h₀⟩ := Sym.BlockSpec.reaches b80011150_spec hpc trivial
  have k₀ := b80011150_keeps h₀
  have i₀ : (u₀.getReg .x5).toNat = 256 * 0 + ((toLeBytes w).getD 0 0).toNat := by
    rw [b80011150_x5 h₀, h17, idx0]
  have pc₀ := b80011150_pc_not_taken h₀ (by
    rw [ha.x21, h17, idx0]; have := byteIdx w 0 (by decide); simp only [Sym.wordToNatLit]; omega)
  have K₀ : ∀ r ∈ bkKeep, u₀.getReg r = t.getReg r := fun r hr ↦ k₀ r (mem_of_mem hr _)
  have x17₀ : u₀.getReg .x17 = w := (k₀ .x17 (by decide)).trans h17
  have s (u : MachineState) (hK : ∀ r ∈ bkKeep, u.getReg r = t.getReg r) :
      (u.getReg .x16, u.getReg .x15, u.getReg .x14) = limbs sum := by
    rw [hK .x16 (by decide), hK .x15 (by decide), hK .x14 (by decide)]; exact hacc
  have g20 (u : MachineState) (hK : ∀ r ∈ bkKeep, u.getReg r = t.getReg r) :
      u.getReg .x20 = e.bk := (hK .x20 (by decide)).trans ha.x20
  have g21 (u : MachineState) (hK : ∀ r ∈ bkKeep, u.getReg r = t.getReg r) :
      u.getReg .x21 = 2048 := (hK .x21 (by decide)).trans ha.x21
  have tr {u v : MachineState} (hK : ∀ r ∈ bkKeep, u.getReg r = t.getReg r)
      (hv : ∀ r ∈ bkKeep, v.getReg r = u.getReg r) : ∀ r ∈ bkKeep, v.getReg r = t.getReg r :=
    fun r hr ↦ (hv r hr).trans (hK r hr)
  obtain ⟨u₁, hr₁, pc₁, i₁, L₁, F₁, K₁, x17₁⟩ :=
    bucket0 he pc₀ i₀ (g20 _ K₀) (g21 _ K₀) x17₀ (s _ K₀)
  obtain ⟨u₂, hr₂, pc₂, i₂, L₂, F₂, K₂, x17₂⟩ :=
    bucket1 he pc₁ i₁ (g20 _ (tr K₀ K₁)) (g21 _ (tr K₀ K₁)) x17₁ (s _ (tr K₀ K₁))
  have T₂ := tr (tr K₀ K₁) K₂
  obtain ⟨u₃, hr₃, pc₃, i₃, L₃, F₃, K₃, x17₃⟩ :=
    bucket2 he pc₂ i₂ (g20 _ T₂) (g21 _ T₂) x17₂ (s _ T₂)
  have T₃ := tr T₂ K₃
  obtain ⟨u₄, hr₄, pc₄, i₄, L₄, F₄, K₄, x17₄⟩ :=
    bucket3 he pc₃ i₃ (g20 _ T₃) (g21 _ T₃) x17₃ (s _ T₃)
  have T₄ := tr T₃ K₄
  obtain ⟨u₅, hr₅, pc₅, i₅, L₅, F₅, K₅, x17₅⟩ :=
    bucket4 he pc₄ i₄ (g20 _ T₄) (g21 _ T₄) x17₄ (s _ T₄)
  have T₅ := tr T₄ K₅
  obtain ⟨u₆, hr₆, pc₆, i₆, L₆, F₆, K₆, x17₆⟩ :=
    bucket5 he pc₅ i₅ (g20 _ T₅) (g21 _ T₅) x17₅ (s _ T₅)
  have T₆ := tr T₅ K₆
  obtain ⟨u₇, hr₇, pc₇, i₇, L₇, F₇, K₇⟩ :=
    bucket6 he pc₆ i₆ (g20 _ T₆) (g21 _ T₆) x17₆ (s _ T₆)
  have T₇ := tr T₆ K₇
  obtain ⟨u₈, hr₈, pc₈, L₈, F₈, x13₈, x6₈, K₈⟩ := bucket7 (w := w) he pc₇ i₇ (g20 _ T₇) (s _ T₇)
  have hr := hr₀.trans (hr₁.trans (hr₂.trans (hr₃.trans (hr₄.trans (hr₅.trans (hr₆.trans
    (hr₇.trans hr₈)))))))
  have hbuck : eListAt u₈ e.bk 2048 = addToBuckets w sum (eListAt t e.bk 2048) := by
    rw [L₈, L₇, L₆, L₅, L₄, L₃, L₂, L₁, addToBuckets_unfold,
      buckets_congr he fun a _ ↦ b80011150_mem_same h₀ a]
  have hfr : ∀ a, ¬ Within a e.bk 49152 → u₈.getMem a = t.getMem a := fun a ha' ↦ by
    rw [F₈ a ha', F₇ a ha', F₆ a ha', F₅ a ha', F₄ a ha', F₃ a ha', F₂ a ha', F₁ a ha',
      b80011150_mem_same h₀]
  have K : ∀ r ∈ [Reg.x2, .x9, .x11, .x12, .x18, .x19, .x20, .x21, .x23],
      u₈.getReg r = t.getReg r := fun r hr ↦ by
    rw [K₈ r hr, T₇ r (mem_of_mem hr _)]
  have hblk : Blk e u₈ i := ha.toBlk.of_bk he hfr fun r hr ↦ K r (mem_of_mem hr _)
  have hj : j < e.bc.words.length := Nat.lt_of_lt_of_le ha.jhi ha.wele
  have hwf : e.wf i (j + 1 - (e.st i).wordsStart) =
      (addToBuckets w sum (e.wf i (j - (e.st i).wordsStart)).1, (e.wd j).2) := by
    rw [wf_succ e ha.jlo hj, wordStepRust, ← hw, ← hsum]
    rfl
  have hb₈ : eListAt u₈ e.bk 2048 = (e.wf i (j + 1 - (e.st i).wordsStart)).1 := by
    rw [hbuck, ha.buckets, hwf]
  have e16 : ∀ n : Nat, BitVec.ofNat 64 (16 * n) + 16 = BitVec.ofNat 64 (16 * (n + 1)) :=
    fun n ↦ by
      rw [show (16 : Word) = BitVec.ofNat 64 16 from rfl, ← BitVec.ofNat_add,
        show 16 * n + 16 = 16 * (n + 1) by omega]
  have x13₈' : u₈.getReg .x13 = e.wordsPtr + BitVec.ofNat 64 (16 * (j + 1)) := by
    rw [x13₈, T₇ .x13 (by decide), ha.x13, BitVec.add_assoc, e16]
  have hwm := he.pre.bc.words
  have hlen := bc_words_length e
  simp only [Env.wordsLen, Env.bcp] at hwm hlen
  by_cases hc : u₇.getReg .x13 + 16 ≠ u₇.getReg .x12
  · rw [ite_eq_left_of_eq_true _ _ (eq_true hc)] at pc₈
    refine ⟨u₈, hr, Or.inr (Or.inl ⟨pc₈, ?_⟩)⟩
    have hjhi : j + 1 < (e.bc.blocks[i]'ha.lt).wordsEnd := by
      refine Nat.lt_of_le_of_ne ha.jhi fun h ↦ hc ?_
      rw [T₇ .x13 (by decide), T₇ .x12 (by decide), ha.x13, ha.x12, ← h, BitVec.add_assoc, e16]
    exact { hblk with
      jlo := Nat.le_succ_of_le ha.jlo
      jhi := hjhi
      x13 := x13₈'
      x12 := (K .x12 (by decide)).trans ha.x12
      x6 := by rw [x6₈, T₇ .x19 (by decide), ha.x19, hwf]
      buckets := hb₈ }
  · rw [ite_eq_right_of_eq_false _ _ (eq_false hc)] at pc₈
    refine ⟨u₈, hr, Or.inr (Or.inr ⟨pc₈, ?_⟩)⟩
    have hend : j + 1 = (e.bc.blocks[i]'ha.lt).wordsEnd := by
      have h := not_not.mp hc
      rw [T₇ .x13 (by decide), T₇ .x12 (by decide), ha.x13, ha.x12, BitVec.add_assoc, e16] at h
      have h' := congrArg BitVec.toNat h
      simp only [BitVec.toNat_add, BitVec.toNat_ofNat] at h'
      have := ha.wele
      have := ha.jhi
      simp only [Mapped] at hwm
      omega
    exact { hblk with
      x19 := by rw [← hend, K .x19 (by decide), ha.x19, hwf]
      buckets := by rw [← hend]; exact hb₈ }

/-- One word, through its sum and its buckets. -/
theorem word_body (he : EnvOk e) {t : MachineState} {i j : Nat} (hw : WInv e t i j)
    (hpc : t.pc = 0x800110d0) :
    ∃ u, Reaches Image.code t u ∧ (Dead Image.code u ∨ (u.pc = 0x800110d0 ∧ WInv e u i (j + 1)) ∨
      (u.pc = 0x8001136c ∧ Mid e u i)) := by
  obtain ⟨u, hr, hd | ⟨hu, ha⟩ | ⟨hu, hs⟩⟩ := word_start he hw hpc
  · exact ⟨u, hr, Or.inl hd⟩
  · obtain ⟨v, hr', hv⟩ := adds he ha hu
    exact ⟨v, hr.trans hr', hv⟩
  · obtain ⟨v, hr', hd | ⟨hv, ha⟩⟩ := sum_loop he hs hu
    · exact ⟨v, hr.trans hr', Or.inl hd⟩
    · obtain ⟨x, hr'', hx⟩ := adds he ha hv
      exact ⟨x, hr.trans (hr'.trans hr''), hx⟩

/-- Every word of block `i`, from word `j` on. -/
theorem words_loop (he : EnvOk e) {t : MachineState} {i j : Nat} (hw : WInv e t i j)
    (hpc : t.pc = 0x800110d0) :
    ∃ u, Reaches Image.code t u ∧ (Dead Image.code u ∨ (u.pc = 0x8001136c ∧ Mid e u i)) := by
  have hwm := he.pre.bc.words
  simp only [Mapped] at hwm
  refine Reaches.loop (fun t ↦ ∃ j, t.pc = 0x800110d0 ∧ WInv e t i j)
    (fun t ↦ (t.getReg .x12).toNat - (t.getReg .x13).toNat) _ (fun t ⟨j, hpc, hw⟩ ↦ ?_) t
    ⟨j, hpc, hw⟩
  obtain ⟨u, hr, hd | ⟨hu, hw'⟩ | ⟨hu, hm⟩⟩ := word_body he hw hpc
  · exact Or.inl ⟨u, hr, Or.inl hd⟩
  · refine Or.inr ⟨u, hr, ⟨j + 1, hu, hw'⟩, ?_⟩
    rw [hw'.x13, hw'.x12, hw.x13, hw.x12]
    have h1 := hw'.jhi
    have h2 := hw.wele
    have h3 := bc_words_length e
    simp only [Env.wordsPtr, Env.wordsLen, Env.bcp] at h3 ⊢
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
    omega
  · exact Or.inl ⟨u, hr, Or.inr ⟨hu, hm⟩⟩

end Rv64Verifier.Proofs.Bytecode.Eval
