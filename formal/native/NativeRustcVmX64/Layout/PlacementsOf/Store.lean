module

public import NativeRustcVmX64.Layout.PlacementsOf.Loop2

/-!
# `placements_of` on x86-64: a placement stored (`b21`)

At `.L15` with RSI the placement's tag, RCX its variable count and RDX its index (`Ready3`),
`b21` stores them at the placements' column `c` and moves on to column `c + 1` (`store`).
-/

namespace NativeRustcVmX64.Layout.PlacementsOf

open NativeRustcX64 NativeRustcX64.Sym NativeRustcVmX64.Vm.PlacementsOf NativeRustcVmX64.Transcript
open NativeRustcVm.Transcript NativeRustcVmX64.Layout.BuildFrame
open NativeVm.Model NativeRustcVm.Layout LeanVM.Protocol.Verifier NativeVm.Math.Layout
open NativeRustcVm (WordAt WordsAt wordOf)

public section

theorem plF_slot {κ : Nat → Nat} {c s : Nat} (h : slotF c = some s) :
    plF κ c = some ⟨κ c, sumF κ (keyF κ 4) + s * 2 ^ κ c⟩ := by
  unfold plF; rw [h]

theorem plF_block {κ : Nat → Nat} {c : Nat} (h : slotF c = none) (ho : outF c = false) :
    plF κ c = some ⟨κ c, sumF κ (keyF κ c)⟩ := by
  unfold plF; rw [h]; simp [ho]

theorem plF_out {κ : Nat → Nat} {c : Nat} (h : slotF c = none) (ho : outF c = true) :
    plF κ c = none := by
  unfold plF; rw [h]; simp [ho]

section
variable [Labels] {m0 : MachineData}

/-- **At `.L15`**: the third loop at column `c`, the placement's words in RSI, RCX, RDX. -/
structure Ready3 (m0 : MachineData) (c : Nat) (d : MachineData) : Prop where
  i3 : I3 m0 c d
  lt : c < 158
  rsi : (reg d .rsi).toNat = if (plF (κ m0) c).isSome then 1 else 0
  rcx : ∀ p, plF (κ m0) c = some p → (reg d .rcx).toNat = p.variableCount
  rdx : ∀ p, plF (κ m0) c = some p → (reg d .rdx).toNat = p.index

theorem I3.of {c : Nat} {d d' : MachineData} (h : I3 m0 c d) (hb : B m0 8 d')
    (hd : d'.dmem = d.dmem) (he : ∀ r ∈ Reg64.rax :: cs, reg d' r = reg d r) : I3 m0 c d' :=
  ⟨hb, h.le, by rw [he .rax (by simp)]; exact h.rax, (he .rbx (by simp [cs])).trans h.rbx,
    by rw [he .r15 (by simp [cs])]; exact h.r15, (he .rbp (by simp [cs])).trans h.rbp,
    (he .r12 (by simp [cs])).trans h.r12, (he .r14 (by simp [cs])).trans h.r14,
    by rw [hd]; exact h.tot, by rw [hd]; exact h.offs, by rw [hd]; exact h.pl⟩

end

variable [Host] {k : Nat} {m0 : MachineData}

/-- **`b21`**: column `c`'s placement stored. -/
theorem store (hp : Placed code k) (hF : Facts m0) {c : Nat} {st : MachineState}
    (hpc : st.pc = Host.addrOf (k + NativeRustcVmX64.Vm.PlacementsOf.b21Offset)) (hR : Ready3 m0 c st.data) :
    Eventually (step1 Host.exe) (fun s ↦ (c + 1 < 158 ∧ s.pc = Host.addrOf (k + NativeRustcVmX64.Vm.PlacementsOf.b22Offset) ∧
      I3 m0 (c + 1) s.data) ∨ (c + 1 = 158 ∧ s.pc = Host.addrOf (k + NativeRustcVmX64.Vm.PlacementsOf.b32Offset) ∧ I3 m0 158 s.data))
      st := by
  have hI := hR.i3
  have hc := hR.lt
  have hpb := hF.pr
  have hpn : (pp m0).toNat + 3792 ≤ 2 ^ 64 := hpb.2
  set a := off (pp m0) (24 * c) with ha
  have han : a.toNat = (pp m0).toNat + 24 * c := toNat_off (by omega)
  have hma : NativeRustcVm.Mapped st.data.dmem a 24 :=
    Mapped.keeps (mapped_off (N := 3792) hpb.1 (by omega)) hI.b.fr.kept
  have hna : NativeRustcVm.NoWrap a 24 := by unfold NativeRustcVm.NoWrap; omega
  let env := Env.ofMachine st.data [(a, 24)] (fun _ ↦ 0) 0
  have hwf : env.WF := Env.wf_of ⟨⟨hma, hna⟩, trivial⟩ (List.pairwise_singleton _ _)
  have hm : Match env plS st.data :=
    match_ofMachine ⟨rfl, trivial⟩ ⟨by
      show reg st.data .rbx = a + BitVec.ofInt 64 (16 : Nat)
      rw [hI.rbx, BitVec.ofInt_natCast, ha, off_add], trivial⟩ trivial trivial trivial
  refine exec_at (b21_in_code.trans hp.1 (List.cons_ne_nil _ _)) exit_b21 hwf nofun hpc hm
    fun st1 hm1 hpc1 ↦ ?_
  obtain ⟨hok, hw0, hws, hwc, hwd, hax, hbx, hK⟩ := ok_b21
  have hok' := hok
  simp only [AOk, Bool.and_eq_true] at hok'
  have hin : ∀ q, Written env (after b21 plS) q → NativeRustcVm.InRange a 24 q := fun q h ↦ by
    obtain ⟨w, hw, b, sz, hb', hq⟩ := written_in hwf hm1 hok'.2 h
    rw [hw0 w hw] at hb'
    simp only [List.getElem?_cons_zero, Option.some.injEq, Prod.mk.injEq] at hb'
    obtain ⟨rfl, rfl⟩ := hb'
    exact hq
  have hinR : ∀ q, NativeRustcVm.InRange a 24 q → R m0 q := fun q h ↦ by
    rw [inRange_iff' hna, han] at h
    show NativeRustcVm.InRange (pp m0) 3792 q
    have hpb2 : NativeRustcVm.NoWrap (pp m0) 3792 := hpb.2
    rw [inRange_iff' hpb2]
    omega
  have hb1 : B m0 8 st1.data := hI.b.of_written hF.stack (by decide) hwf hm1 hok (L := 5072)
    (by decide) slots_ge slots_le fun q h ↦ Or.inl ⟨hinR q (hin q h), hF.R_frame (hinR q (hin q h))⟩
  have hsame : NativeRustcVm.SameOutside st.data.dmem st1.data.dmem (NativeRustcVm.InRange a 24) :=
    fun q hq ↦ hm1.get?_mem0 hwf fun h ↦ hq (hin q h)
  -- the words kept: the frame's, the other columns'
  have kf : ∀ {o : Nat} {v : UInt64}, o + 8 ≤ 5120 →
      WordAt st.data.dmem (off (fb m0) o) v → WordAt st1.data.dmem (off (fb m0) o) v :=
    fun ho h ↦ word_keep h hsame fun i hi h' ↦ hF.R_frame (hinR _ h')
      (fb_in hF.stack (by decide) (by omega))
  have kp : ∀ {c' : Nat} {P : Option Placement}, c' < c →
      PlacementWAt st.data.dmem (off (pp m0) (24 * c')) P →
      PlacementWAt st1.data.dmem (off (pp m0) (24 * c')) P := by
    intro c' P hc' h
    have kw : ∀ {o : Nat} {v : UInt64}, o + 8 ≤ 24 →
        WordAt st.data.dmem (off (off (pp m0) (24 * c')) o) v →
        WordAt st1.data.dmem (off (off (pp m0) (24 * c')) o) v := fun ho hw ↦
      bytesAt_congr hw fun i hi ↦ by
        have hi8 : i < 8 := by simpa [NativeRustcVm.length_wordBytes] using hi
        rw [off_add, off_off]
        refine hsame _ fun h' ↦ ?_
        rw [inRange_iff' hna, han, toNat_off (by omega)] at h'
        omega
    cases P with
    | none =>
      have h0 : WordAt st.data.dmem (off (pp m0) (24 * c')) 0 := h
      have := kw (o := 0) (by omega) (by rw [off_zero]; exact h0)
      rw [off_zero] at this
      exact this
    | some p =>
      obtain ⟨h1, h2, h3, h4, h5⟩ := h
      have := kw (o := 0) (by omega) (by rw [off_zero]; exact h1)
      rw [off_zero] at this
      exact ⟨this, h2, h3, kw (by omega) h4, kw (by omega) h5⟩
  -- the new words
  have w0 := wordAt_write hm1 (r := 0) (o := 0) rfl (by decide) (fun t ht ↦ by simpa using hws t ht)
  have w8 := wordAt_write hm1 (r := 0) (o := 8) rfl (by decide) hwc
  have w16 := wordAt_write hm1 (r := 0) (o := 16) rfl (by decide) hwd
  rw [off_zero] at w0
  have hnew : PlacementWAt st1.data.dmem a (plF (κ m0) c) := by
    cases hP : plF (κ m0) c with
    | none =>
      have : (reg st.data .rsi).toNat = 0 := by rw [hR.rsi, hP]; rfl
      show WordAt _ _ 0
      rw [show (0 : UInt64) = (0 : Nat).toUInt64 from rfl, ← u64_of this]
      exact w0
    | some p =>
      have h1 : (reg st.data .rsi).toNat = 1 := by rw [hR.rsi, hP]; rfl
      have h2 := hR.rcx p hP
      have h3 := hR.rdx p hP
      refine ⟨?_, by rw [← h2]; exact (reg st.data .rcx).isLt,
        by rw [← h3]; exact (reg st.data .rdx).isLt, ?_, ?_⟩
      · rw [show (1 : UInt64) = (1 : Nat).toUInt64 from rfl, ← u64_of h1]; exact w0
      · rw [← u64_of h2]; exact w8
      · rw [← u64_of h3]; exact w16
  have hK' := fun r (hr : r ∈ [Reg64.rbp, .r12, .r13, .r14, .r15]) ↦ kreg hm1 hK hr
  have hc1 : ((Sym.bin .add .W64 (.reg .rax) (.lit 1)).eval env).toNat = c + 1 := by
    show (BinOp.apply .add .W64 (reg st.data .rax) (BitVec.ofNat 64 1)).toNat = _
    simp only [BinOp.apply, low_W64, ext_W64, BitVec.toNat_add, hI.rax, BitVec.toNat_ofNat]
    omega
  have hI1 : I3 m0 (c + 1) st1.data :=
    ⟨hb1, by omega, by show (st1.data.regs.get64 .rax).toNat = _; rw [hm1.regs .rax _ hax]; exact hc1,
      by
        show st1.data.regs.get64 .rbx = _
        rw [hm1.regs .rbx _ hbx]
        show a + BitVec.ofInt 64 (40 : Nat) = _
        rw [BitVec.ofInt_natCast, ha, off_add, show 24 * c + 40 = 24 * (c + 1) + 16 by omega],
      by rw [hK' .r15 (by simp)]; exact hI.r15, (hK' .rbp (by simp)).trans hI.rbp,
      (hK' .r12 (by simp)).trans hI.r12, (hK' .r14 (by simp)).trans hI.r14, kf (by omega) hI.tot,
      fun c' hc' ↦ kf (by have := lt_of_mem_blockList hc'; omega) (hI.offs c' hc'),
      fun c' hc' ↦ by
        rcases Nat.lt_or_ge c' c with h | h
        · exact kp h (hI.pl c' h)
        · obtain rfl : c' = c := by omega
          exact hnew⟩
  simp only [PcOk] at hpc1
  obtain ⟨hy, hno⟩ := pc_of (P := c + 1 = 158) hpc1 (by rw [eq_eval, hc1]; rfl)
  by_cases hl : c + 1 = 158
  · exact .done _ (.inr ⟨hl, (hy hl).trans (hp.label NativeRustcVmX64.Vm.PlacementsOf.label_24_at), hl ▸ hI1⟩)
  · exact .done _ (.inl ⟨by omega, hno hl, hI1⟩)

end

end NativeRustcVmX64.Layout.PlacementsOf
