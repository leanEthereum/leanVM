module

public import NativeRustcArm.Code.Xmss.WotsLeaf.Names

public import NativeRustcArm.WotsLeaf.Codeword.Checks

/-!
# The digits' loop

`b9` (`.LWotsLeaf_3`, directive 102), 14 turns: turn `j` stores digits `4 j .. 4 j + 3` at the
frame's bytes `380 + 4 j ..` (`Run.AtDigits`, `digits_turn`, `digits_loop`).
-/

namespace NativeRustcArm.WotsLeafProof

open NativeRustc NativeRustc.Xmss NativeRustcArm.Sym NativeRustcArm.Xmss.WotsLeaf Codeword
open LeanVM.Protocol.KeccakHash

@[expose] public section

/-- The first `n` digits of the digest. -/
def Run.digitsPre (r : Run) (n : Nat) : List UInt8 :=
  (List.range n).map fun d ↦ UInt8.ofNat (r.dNum >>> (2 * d) &&& 3)

/-- The slots through the digits' loop: `e`, `hi`, the digest, `out`. -/
def Run.loopSlots (r : Run) : List Slot := r.checkSlots ++ [(0, 8, wordBytes r.m0.regs.X0)]

/-- **At turn `j` of the digits' loop** (`b9`): the first `4 j` digits at 380; X8, X9 the
digest's words, X10 `X8 << 1`, X11 the frame's byte `381 + 4 j`, X12 `6 + 8 j`; X19 `out`, X20
`P`'s address, X22 the chain values'. -/
def Run.AtDigits (r : Run) (j : Nat) (m : MachineData) : Prop :=
  Keep r r.loopSlots m ∧ BytesAt m.dmem (r.off 380) (r.digitsPre (4 * j)) ∧
    Run.RegIs m .X8 r.hiW ∧ Run.RegIs m .X9 r.lo ∧ Run.RegIs m .X10 (r.hiW <<< 1) ∧
    Run.RegIs m .X11 (r.off (381 + 4 * j)) ∧ Run.RegIs m .X12 (BitVec.ofNat 64 (6 + 8 * j)) ∧
    Run.RegIs m .X19 r.out ∧ Run.RegIs m .X20 r.m0.regs.X1.toBitVec ∧
    Run.RegIs m .X22 r.m0.regs.X7.toBitVec

end

public section

theorem noWriteIn_mono {S : SState} {o n o' n' : Nat} (h : Run.noWriteIn S o n = true)
    (h1 : o ≤ o') (h2 : o' + n' ≤ o + n) : Run.noWriteIn S o' n' = true := by
  simp only [Run.noWriteIn, List.all_eq_true, Bool.or_eq_true, bne_iff_ne, ne_eq,
    decide_eq_true_eq] at h ⊢
  intro w hw
  have := h w hw
  omega

theorem digitsPre_succ4 (r : Run) (n : Nat) :
    r.digitsPre (n + 4) = r.digitsPre n ++
      [UInt8.ofNat (r.dNum >>> (2 * n) &&& 3), UInt8.ofNat (r.dNum >>> (2 * (n + 1)) &&& 3),
        UInt8.ofNat (r.dNum >>> (2 * (n + 2)) &&& 3), UInt8.ofNat (r.dNum >>> (2 * (n + 3)) &&& 3)] := by
  simp [Run.digitsPre, List.range_succ]

theorem length_digitsPre (r : Run) (n : Nat) : (r.digitsPre n).length = n := by
  simp [Run.digitsPre]


/-- What a turn of the loop does, from `ok9`. -/
theorem ok9_spec {j : Nat} (h : ok9 j = true) : ∃ S, exec b9 (s9 j) =
      some (S, .cond (.lit (j != 13)) NativeRustcArm.Xmss.WotsLeaf.label_3) ∧ coversDigits S.mem j = true ∧
    blockOK S = true ∧ Run.noWriteIn S 0 (380 + 4 * j) = true ∧ Run.noWriteIn S 1776 32 = true ∧
    S.reg .X11 = some (.ptr 0 (381 + 4 * (j + 1))) ∧ S.reg .X12 = some (.lit (6 + 8 * (j + 1))) ∧
    S.reg .X8 = some (.reg .X8) ∧ S.reg .X9 = some (.reg .X9) ∧ S.reg .X10 = some (.reg .X10) ∧
    S.reg .X19 = some (.reg .X19) ∧ S.reg .X20 = some (.reg .X20) ∧
    S.reg .X22 = some (.reg .X22) := by
  unfold ok9 at h
  split at h
  · rename_i S x hx
    simp only [Bool.and_eq_true, beq_iff_eq, List.all_cons, List.all_nil, Bool.and_true,
      and_assoc] at h
    obtain ⟨hc, -, -, -, -, hb, n1, n2, h11, h12, h8, h9, h10, h19, h20, h22, hxx⟩ := h
    subst hxx
    exact ⟨S, hx, hc, hb, n1, n2, h11, h12, h8, h9, h10, h19, h20, h22⟩
  · cases h

/-- The four digits a turn stores. -/
theorem digits_of_covers [Labels] {r : Run} {m m' : MachineData} {S : SState}
    (hm : Match (r.env m) S m') {j : Nat} (hj : j < 14) (hc : coversDigits S.mem j = true)
    (h8 : Run.RegIs m .X8 r.hiW) (h9 : Run.RegIs m .X9 r.lo) (h10 : Run.RegIs m .X10 (r.hiW <<< 1)) :
    BytesAt m'.dmem (r.off (380 + 4 * j))
      [UInt8.ofNat (r.dNum >>> (2 * (4 * j)) &&& 3), UInt8.ofNat (r.dNum >>> (2 * (4 * j + 1)) &&& 3),
        UInt8.ofNat (r.dNum >>> (2 * (4 * j + 2)) &&& 3),
        UInt8.ofNat (r.dNum >>> (2 * (4 * j + 3)) &&& 3)] := by
  have one : ∀ t < 4, BytesAt m'.dmem (r.off (380 + 4 * j + t))
      [UInt8.ofNat (r.dNum >>> (2 * (4 * j + t)) &&& 3)] := by
    intro t ht
    have hw : covers S.mem 0 (380 + 4 * j + t) 1 (digitSym (4 * j + t)) = true := by
      simp only [coversDigits, List.all_eq_true, List.mem_range] at hc
      have := hc t ht 0 (by decide)
      simpa [covers] using this
    have := bytesAt_write_val hm (b := r.base) (sz := 2752) rfl (by omega) hw
    rw [show (List.range 1).map (byteOf ((digitSym (4 * j + t)).eval (r.env m))) =
      [byteOf ((digitSym (4 * j + t)).eval (r.env m)) 0] from rfl,
      byteOf_digitSym (r.env m) h8 h9 h10 (by omega)] at this
    exact this
  have e : ∀ t, r.off (380 + 4 * j) + BitVec.ofNat 64 t = r.off (380 + 4 * j + t) :=
    fun t ↦ r.off_add _ _
  refine BytesAt.append (bs := [_]) (BytesAt.zero ?_) (BytesAt.append (bs := [_]) ?_
    (BytesAt.append (bs := [_]) ?_ ?_))
  · rw [e]; simpa using one 0 (by decide)
  · rw [e]; exact one 1 (by decide)
  · rw [List.length_singleton, addr_add_add, e]; exact one 2 (by decide)
  · rw [List.length_singleton, addr_add_add, List.length_singleton, addr_add_add, e]
    exact one 3 (by decide)

variable [NativeRustcArm.Host]

/-- **The digits' loop**: from turn `j < 14` at `b9`, the machine reaches `b10` (directive 146)
with the 56 digits of the 14 turns stored. -/
theorem digits_loop (r : Run) (hp : Placed Xmss.WotsLeaf.code r.k) (hpre : r.Pre) :
    ∀ n j, j + n = 14 → 0 < n → ∀ m, r.AtDigits j m →
      Eventually (step1 NativeRustcArm.Host.exe) (fun st ↦ st.pc = r.pc NativeRustcArm.Xmss.WotsLeaf.b10Offset ∧ r.AtDigits 14 st.data)
        ⟨m, r.pc NativeRustcArm.Xmss.WotsLeaf.b9Offset⟩ := by
  intro n
  induction n with
  | zero => intro j _ h; omega
  | succ n ih =>
    intro j hjn _ m hA
    obtain ⟨hK, hD, h8, h9, h10, h11, h12, h19, h20, h22⟩ := hA
    obtain ⟨S, hx, hc, hb, n1, n2, s11, s12, s8, s9, s10, s19, s20, s22⟩ :=
      ok9_spec (ok9_all j (by omega))
    have hL : slotsKept S r.loopSlots = true := by
      simp only [slotsKept, Run.loopSlots, Run.checkSlots, Run.prologueSlots, List.cons_append,
        List.nil_append, List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true]
      refine ⟨?_, ?_, ?_, ?_⟩
      · exact noWriteIn_mono n1 (o' := 24) (n' := 4) (by omega) (by omega)
      · exact noWriteIn_mono n1 (o' := 28) (n' := 4) (by omega) (by omega)
      · exact n2
      · exact noWriteIn_mono n1 (o' := 0) (n' := 8) (by omega) (by omega)
    refine frameStep r hp hpre b9_in_code (List.cons_ne_nil _ _) hx hb hL hK
      ⟨known_ptr h11, known_lit h12, trivial⟩ fun st hm hK' hkb hpc ↦ ?_
    have hD' : BytesAt st.data.dmem (r.off 380) (r.digitsPre (4 * (j + 1))) := by
      rw [show 4 * (j + 1) = 4 * j + 4 by ring, digitsPre_succ4]
      refine BytesAt.append (hkb 380 _ (by rw [length_digitsPre]; omega)
        (by rw [length_digitsPre]; exact noWriteIn_mono n1 (by omega) (by omega)) hD) ?_
      rw [length_digitsPre, r.off_add]
      exact digits_of_covers hm (by omega) hc h8 h9 h10
    have hA' : r.AtDigits (j + 1) st.data :=
      ⟨hK', hD', regIs_reg hm s8 h8, regIs_reg hm s9 h9, regIs_reg hm s10 h10,
        regIs_ptr hm (o := 381 + 4 * (j + 1)) (by rw [s11]; push_cast; ring_nf),
        regIs_lit hm s12, regIs_reg hm s19 h19, regIs_reg hm s20 h20, regIs_reg hm s22 h22⟩
    by_cases hj : j = 13
    · subst hj
      have : st.pc = r.pc NativeRustcArm.Xmss.WotsLeaf.b10Offset := by
        simpa [PcOk, SBool.eval, NativeRustcArm.Xmss.WotsLeaf.b9_next] using hpc
      exact .done _ ⟨this, hA'⟩
    · have : st.pc = r.pc NativeRustcArm.Xmss.WotsLeaf.b9Offset := by
        have h1 := hpc
        simp only [PcOk, SBool.eval, bne_iff_ne, ne_eq, hj, not_false_eq_true,
          ite_true] at h1
        rw [h1]
        exact Run.label_of_block r hp b9_in_code rfl
      exact pc_at this (ih (j + 1) (by omega) (by omega) st.data hA')

end

end NativeRustcArm.WotsLeafProof
