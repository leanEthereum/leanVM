module

public import NativeRustcVmX64.Tables.TableSumcheck.State

/-!
# `table_sumcheck`: blocks over parts of the frame (x86-64)

The reverse loop's blocks address the challenges through registers: their environment's regions
are parts of the frame (`LE m0 d L`, `L` the offsets and sizes), not the frame itself. Such a block
keeps the body where it keeps RSP and writes within its regions below the slots (`Bd.loc`); bytes
of the frame no region holds are kept (`bytes_keep`), words of regions loaded (`ld_loc`) and
elements written (`ew_written`).
-/

namespace NativeRustcVmX64.Tables.TableSumcheck

open NativeRustcX64 NativeRustcX64.Sym NativeRustcVmX64.Transcript NativeRustcVm.Transcript
open NativeVm.Model NativeRustcVm.Tables
open NativeRustcVmX64.Tables.Body NativeRustcVmX64.Sumcheck NativeRustcVmX64.Vm.TableSumcheck

@[expose] public section

/-- Parts of the frame: offsets, sizes. -/
def locs (m0 : MachineData) (L : List (Nat × Nat)) : List (BitVec 64 × Nat) :=
  L.map fun p ↦ (off (fb m0) p.1, p.2)

/-- A block's environment over parts of the frame. -/
abbrev LE (m0 d : MachineData) (L : List (Nat × Nat)) : Env := Env.ofMachine d (locs m0 L)

/-- Each write of a block is within its region. -/
def InLocs (L : List (Nat × Nat)) (Sy : SState) : Prop :=
  ∀ w ∈ Sy.mem, ∃ p, L[w.r]? = some p ∧ w.off + w.n ≤ p.2

end

public section

theorem off_inj {b : BitVec 64} {i j : Nat} (hi : i < 2 ^ 64) (hj : j < 2 ^ 64)
    (h : off b i = off b j) : i = j := by
  have h1 : NativeRustcVm.InRange (off b i) 1 (off b j) := by
    rw [← h]; unfold NativeRustcVm.InRange; simp
  have := (inRange_off_iff hj (by omega)).mp h1
  omega

theorem locs_get {m0 : MachineData} {L : List (Nat × Nat)} {r : Nat} {b : BitVec 64} {n : Nat}
    (h : (locs m0 L)[r]? = some (b, n)) : ∃ p, L[r]? = some p ∧ b = off (fb m0) p.1 ∧ n = p.2 := by
  unfold locs at h
  rw [List.getElem?_map, Option.map_eq_some_iff] at h
  obtain ⟨p, hp, he⟩ := h
  simp only [Prod.mk.injEq] at he
  exact ⟨p, hp, he.1.symm, he.2.symm⟩

theorem locs_get' {m0 : MachineData} {L : List (Nat × Nat)} {r : Nat} {p : Nat × Nat}
    (h : L[r]? = some p) : (locs m0 L)[r]? = some (off (fb m0) p.1, p.2) := by
  unfold locs
  rw [List.getElem?_map, h]
  rfl

variable [Labels] {a : DecArea} {s : TState} {heights : Array Nat} {bus : BusResultW}
  {m0 : MachineData}

/-- **The environment is well formed**: its regions in the frame, apart. -/
theorem loc_wf (h : TableSumcheckPre a s heights bus m0) {d : MachineData}
    (hk : Kept m0.dmem d.dmem) {L : List (Nat × Nat)} (hL : ∀ p ∈ L, p.1 + p.2 ≤ 736)
    (hd : L.Pairwise fun x y ↦ x.1 + x.2 ≤ y.1 ∨ y.1 + y.2 ≤ x.1) : (LE m0 d L).WF := by
  have hS := Pre.stack h
  have hnw : (fb m0).toNat + (736 + 8) ≤ 2 ^ 64 :=
    frame_noWrap (F := 736) hS (by unfold N tableSumcheckStack; omega)
  have hmp : NativeRustcVm.Mapped d.dmem (fb m0) (736 + 8) :=
    Mapped.keeps (frame_mapped hS (by unfold N tableSumcheckStack; omega)) hk
  refine ⟨fun r b n hb ↦ ?_, fun r b n hb ↦ ?_, fun r r' b b' n n' hne hb hb' ↦ ?_⟩
  · obtain ⟨p, hp, rfl, rfl⟩ := locs_get hb
    have := hL p (List.mem_of_getElem? hp)
    rw [toNat_off (by omega)]; omega
  · obtain ⟨p, hp, rfl, rfl⟩ := locs_get hb
    have := hL p (List.mem_of_getElem? hp)
    exact mapped_off hmp (by omega)
  · obtain ⟨p, hp, rfl, rfl⟩ := locs_get hb
    obtain ⟨p', hp', rfl, rfl⟩ := locs_get hb'
    have h1 := hL p (List.mem_of_getElem? hp)
    have h2 := hL p' (List.mem_of_getElem? hp')
    rw [toNat_off (by omega), toNat_off (by omega)]
    have hpw := List.pairwise_iff_getElem.mp hd
    obtain ⟨hr, e⟩ := List.getElem?_eq_some_iff.mp hp
    obtain ⟨hr', e'⟩ := List.getElem?_eq_some_iff.mp hp'
    rcases Nat.lt_or_gt_of_ne hne with hl | hl
    · have := hpw r r' hr hr' hl
      rw [e, e'] at this
      omega
    · have := hpw r' r hr' hr hl
      rw [e, e'] at this
      omega

omit [Labels] in
/-- A byte a block over parts of the frame wrote: in a part, below its end. -/
theorem written_loc {d : MachineData} {L : List (Nat × Nat)} {Sy : SState} (hwf : (LE m0 d L).WF)
    (hin : InLocs L Sy) {q : BitVec 64} (hq : Written (LE m0 d L) Sy q) :
    ∃ p ∈ L, ∃ j < p.2, q = off (fb m0) (p.1 + j) := by
  obtain ⟨w, hw, b, sz, hb, j, hj1, hj2, rfl⟩ := written_off hwf hq
  obtain ⟨p, hp, hle⟩ := hin w hw
  rw [Env.ofMachine_regions, locs_get' hp, Option.some.injEq, Prod.mk.injEq] at hb
  obtain ⟨rfl, rfl⟩ := hb
  exact ⟨p, List.mem_of_getElem? hp, j, by omega, off_off _ _ _⟩

/-- **Bytes of the frame no part holds** are kept. -/
theorem bytes_keep {d d' : MachineData} {L : List (Nat × Nat)} {Sy : SState}
    (hwf : (LE m0 d L).WF) (hm : Match (LE m0 d L) Sy d') (hin : InLocs L Sy)
    (hL : ∀ p ∈ L, p.1 + p.2 ≤ 744) {lo : Nat} {bs : List UInt8} (hlo : lo + bs.length ≤ 744)
    (hmiss : ∀ p ∈ L, lo + bs.length ≤ p.1 ∨ p.1 + p.2 ≤ lo)
    (hx : NativeRustcVm.BytesAt d.dmem (off (fb m0) lo) bs) :
    NativeRustcVm.BytesAt d'.dmem (off (fb m0) lo) bs :=
  bytesAt_congr hx fun i hi ↦ by
    rw [off_add]
    refine hm.get?_mem0 hwf fun hw ↦ ?_
    obtain ⟨p, hp, j, hj, he⟩ := written_loc hwf hin hw
    have := hL p hp
    have := off_inj (by omega) (by omega) he
    have := hmiss p hp
    omega

/-- **A block over parts of the frame below the slots** keeps the body. -/
theorem Bd.loc (h : TableSumcheckPre a s heights bus m0) {d d' : MachineData} {o : Nat}
    (hb : Bd m0 736 N slots (outs m0) o d) {L : List (Nat × Nat)} {Sy : SState}
    (hwf : (LE m0 d L).WF) (hm : Match (LE m0 d L) Sy d') (hin : InLocs L Sy)
    (hL : ∀ p ∈ L, p.1 + p.2 ≤ 688) (hsp : Sy.reg .rsp = some (.reg .rsp)) :
    Bd m0 736 N slots (outs m0) o d' ∧
      NativeRustcVm.SameOutside d.dmem d'.dmem (NativeRustcVm.InRange (fb m0) 736) := by
  have hS := Pre.stack h
  have hnw : (fb m0).toNat + (736 + 8) ≤ 2 ^ 64 :=
    frame_noWrap (F := 736) hS (by unfold N tableSumcheckStack; omega)
  have hw : ∀ q, Written (LE m0 d L) Sy q → ∃ j < 688, q = off (fb m0) j := fun q hq ↦ by
    obtain ⟨p, hp, j, hj, rfl⟩ := written_loc hwf hin hq
    exact ⟨p.1 + j, by have := hL p hp; omega, rfl⟩
  have hnot : ∀ j, 688 ≤ j → j < 744 → d'.dmem.get? (off (fb m0) j) = d.dmem.get? (off (fb m0) j) :=
    fun j h1 h2 ↦ hm.get?_mem0 hwf fun hq ↦ by
      obtain ⟨j', hj', he⟩ := hw _ hq
      have := off_inj (by omega) (by omega) he
      omega
  have hso : NativeRustcVm.SameOutside d.dmem d'.dmem (NativeRustcVm.InRange (fb m0) 736) :=
    fun q hq ↦ hm.get?_mem0 hwf fun hw' ↦ hq (by
      obtain ⟨j, hj, rfl⟩ := hw q hw'
      exact inRange_off_self (by omega) (by omega))
  have hcs : ∀ r, calleeSaved r = true → slots.any (·.2 == r) = true := by
    intro r; cases r <;> decide
  refine ⟨⟨⟨?_, fun p hp ↦ ?_, fun j hj ↦ ?_, kept_trans hb.fr.kept (hm.kept hwf),
    fun r hr hsl ↦ by rw [hcs r hr] at hsl; cases hsl⟩, fun q hq ↦ ?_⟩, hso⟩
  · show d'.regs.get64 .rsp = _
    rw [hm.regs .rsp _ hsp]
    exact hb.fr.sp
  · refine bytesAt_congr (hb.fr.slot p hp) fun i hi ↦ ?_
    have hi' : i < 8 := by simpa [LeanVM.Protocol.KeccakHash.wordBytes] using hi
    have := slots_le p hp
    rw [off_add]
    exact hnot _ (by omega) (by omega)
  · rw [hnot _ (by omega) (by omega)]
    exact hb.fr.ret j hj
  · refine (hso q fun hq' ↦ hq (.inr (fr_stack h hq'))).trans (hb.same q hq)

/-- **A word of a part loaded.** -/
theorem ld_loc {d : MachineData} {L : List (Nat × Nat)} {r : Nat} {p : Nat × Nat}
    (hp : L[r]? = some p) {o : Nat} {w : UInt64}
    (hx : NativeRustcVm.WordAt d.dmem (off (fb m0) (p.1 + o)) w) :
    (Sym.load r o 8).eval (LE m0 d L) = w.toBitVec := by
  show (LE m0 d L).load r o 8 = _
  refine load_of_wordAt ?_
  rw [Env.base_ofMachine _ _ _ _ (locs_get' hp), off_add]
  exact hx

/-- **An element of a part written**: its two words. -/
theorem ew_written {d d' : MachineData} {L : List (Nat × Nat)} {Sy : SState}
    (hm : Match (LE m0 d L) Sy d') {r : Nat} {p : Nat × Nat} (hp : L[r]? = some p) {o : Nat}
    (hle : o + 16 ≤ p.2) {v0 v1 : Sym} (h0 : WordW r o v0 Sy) (h1 : WordW r (o + 8) v1 Sy)
    {x : EW} (e0 : v0.eval (LE m0 d L) = x.c0.toBitVec) (e1 : v1.eval (LE m0 d L) = x.c1.toBitVec) :
    NativeRustcVm.EWAt d'.dmem (off (fb m0) (p.1 + o)) x := by
  rw [NativeRustcVm.ewAt_iff]
  have w0 := wordAt_written hm (locs_get' hp) (by omega) h0 e0
  have w1 := wordAt_written hm (locs_get' hp) (by omega) h1 e1
  rw [off_off] at w0 w1
  rw [← Nat.add_assoc] at w1
  rw [off_add]
  exact ⟨w0, w1⟩

/-- **An element of a part loaded**: its two words. -/
theorem ew_ld {d : MachineData} {L : List (Nat × Nat)} {r : Nat} {p : Nat × Nat}
    (hp : L[r]? = some p) {o : Nat} {x : EW}
    (hx : NativeRustcVm.EWAt d.dmem (off (fb m0) (p.1 + o)) x) :
    (Sym.load r o 8).eval (LE m0 d L) = x.c0.toBitVec ∧
      (Sym.load r (o + 8) 8).eval (LE m0 d L) = x.c1.toBitVec := by
  rw [NativeRustcVm.ewAt_iff, off_add, Nat.add_assoc] at hx
  exact ⟨ld_loc hp hx.1, ld_loc hp hx.2⟩

end

end NativeRustcVmX64.Tables.TableSumcheck
