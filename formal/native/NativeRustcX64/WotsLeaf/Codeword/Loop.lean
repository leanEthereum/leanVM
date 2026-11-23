module

public import NativeRustcX64.Code.Xmss.WotsLeaf.Names

public import NativeRustcX64.WotsLeaf.Codeword.Checks

/-!
# The digits' loop

`b9` (`.LWotsLeaf_3`, directive 124), 29 turns: turn `j` stores digits `2 j`, `2 j + 1` at the
frame's bytes `614 + 2 j`, `615 + 2 j` (`Run.AtDigits`, `digits_loop`).
-/

namespace NativeRustcX64.WotsLeafProof

open NativeRustc NativeRustc.Xmss NativeRustcX64.Sym NativeRustcX64.Xmss.WotsLeaf Codeword
open LeanVM.Protocol.KeccakHash

@[expose] public section

/-- `layer << 23` as the 32-bit shift stores it at `8`: the address's `hi`. -/
def Run.layerW (r : Run) : BitVec 64 := BinOp.apply .shl .W32 (reg r.m0 .rdx) (BitVec.ofNat 64 23)

/-- The first `n` digits of the digest. -/
def Run.digitsPre (r : Run) (n : Nat) : List UInt8 :=
  (List.range n).map fun d ↦ UInt8.ofNat (r.dNum >>> (2 * d) &&& 3)

/-- The slots through the digits' loop: `hi`, `e`, `out`, `P`'s address, the digest. -/
def Run.loopSlots (r : Run) : List Slot :=
  [(8, 8, regBytes r.layerW), (52, 4, u32Bytes r.e), (96, 8, regBytes r.out),
    (104, 8, regBytes (reg r.m0 .rsi)), (112, 32, r.digest32)]

/-- **At turn `j` of the digits' loop** (`b9`): the first `2 j` digits at 614; RSI, RDX the
digest's words, RAX `4 j`, RDI the frame's byte `615 + 2 j`. -/
def Run.AtDigits (r : Run) (j : Nat) (m : MachineData) : Prop :=
  Keep r r.loopSlots m ∧ BytesAt m.dmem (r.off 614) (r.digitsPre (2 * j)) ∧
    Run.RegIs m .rsi r.lo ∧ Run.RegIs m .rdx r.hiW ∧ Run.RegIs m .rax (BitVec.ofNat 64 (4 * j)) ∧
    Run.RegIs m .rdi (r.off (615 + 2 * j))

end

public section

theorem noWriteIn_mono {S : SState} {o n o' n' : Nat} (h : Run.noWriteIn S o n = true)
    (h1 : o ≤ o') (h2 : o' + n' ≤ o + n) : Run.noWriteIn S o' n' = true := by
  simp only [Run.noWriteIn, List.all_eq_true, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq,
    bne_iff_ne, ne_eq, decide_eq_true_eq] at h ⊢
  intro w hw
  have := h w hw
  omega

theorem digitsPre_succ2 (r : Run) (n : Nat) :
    r.digitsPre (n + 2) = r.digitsPre n ++
      [UInt8.ofNat (r.dNum >>> (2 * n) &&& 3), UInt8.ofNat (r.dNum >>> (2 * (n + 1)) &&& 3)] := by
  simp [Run.digitsPre, List.range_succ]

theorem length_digitsPre (r : Run) (n : Nat) : (r.digitsPre n).length = n := by
  simp [Run.digitsPre]


/-- What a turn of the loop does, from `ok9`. -/
theorem ok9_spec {j : Nat} (h : ok9 j = true) : ∃ S, exec b9 (s9 j) =
      some (S, .cond (.lit (j != 28)) NativeRustcX64.Xmss.WotsLeaf.label_3) ∧ coversDigits S.mem j = true ∧
    blockOK S 0 = true ∧ Run.noWriteIn S 0 (614 + 2 * j) = true ∧
    S.reg .rax = some (.lit (4 * (j + 1))) ∧ S.reg .rdi = some (.ptr 0 (615 + 2 * (j + 1))) ∧
    S.reg .rsi = some (.reg .rsi) ∧ S.reg .rdx = some (.reg .rdx) := by
  unfold ok9 at h
  split at h
  · rename_i S x hx
    simp only [Bool.and_eq_true, beq_iff_eq, and_assoc] at h
    obtain ⟨hc, -, hb, n1, hax, hdi, hsi, hdx, hxx⟩ := h
    subst hxx
    exact ⟨S, hx, hc, hb, n1, hax, hdi, hsi, hdx⟩
  · cases h

/-- The two digits a turn stores. -/
theorem digits_of_covers [Labels] {r : Run} {m m' : MachineData} {ret : BitVec 64} {S : SState}
    (hm : Match (r.envR m [] ret) S m') {j : Nat} (hj : j < 29) (hc : coversDigits S.mem j = true)
    (hs : Run.RegIs m .rsi r.lo) (hd : Run.RegIs m .rdx r.hiW) :
    BytesAt m'.dmem (r.off (614 + 2 * j))
      [UInt8.ofNat (r.dNum >>> (2 * (2 * j)) &&& 3),
        UInt8.ofNat (r.dNum >>> (2 * (2 * j + 1)) &&& 3)] := by
  have one : ∀ t < 2, BytesAt m'.dmem (r.off (614 + 2 * j + t))
      [UInt8.ofNat (r.dNum >>> (2 * (2 * j + t)) &&& 3)] := by
    intro t ht
    have hw : covers S.mem 0 (614 + 2 * j + t) 1 (digitSym (2 * j + t)) = true := by
      simp only [coversDigits, List.all_eq_true, List.mem_range, beq_iff_eq] at hc
      have := hc t ht
      simpa [covers] using this
    have := frame_covers hm (by omega) hw
    rw [show (List.range 1).map (byteOf ((digitSym (2 * j + t)).eval (r.envR m [] ret))) =
      [byteOf ((digitSym (2 * j + t)).eval (r.envR m [] ret)) 0] from rfl,
      byteOf_digitSym (r.envR m [] ret) hs hd (by omega)] at this
    exact this
  refine BytesAt.append (bs := [_]) (one 0 (by decide)) ?_
  rw [List.length_singleton, r.off_add]
  exact one 1 (by decide)

variable [Host]

/-- **The digits' loop**: from turn `j < 29` at `b9`, the machine reaches `b10` (directive 147)
with the 58 digits of the 29 turns stored. -/
theorem digits_loop (r : Run) (hp : Placed Xmss.WotsLeaf.code r.k) (hpre : r.Pre) :
    ∀ n j, j + n = 29 → 0 < n → ∀ m, r.AtDigits j m →
      Eventually (step1 Host.exe) (fun st ↦ st.pc = r.pc NativeRustcX64.Xmss.WotsLeaf.b10Offset ∧ r.AtDigits 29 st.data)
        ⟨m, r.pc NativeRustcX64.Xmss.WotsLeaf.b9Offset⟩ := by
  intro n
  induction n with
  | zero => intro j _ h; omega
  | succ n ih =>
    intro j hjn _ m hA
    obtain ⟨hK, hD, hs, hd, hax, hdi⟩ := hA
    obtain ⟨S, hx, hc, hb, n1, sax, sdi, ssi, sdx⟩ := ok9_spec (ok9_all j (by omega))
    have hL : slotsKept S r.loopSlots = true := by
      simp only [slotsKept, Run.loopSlots, List.all_cons, List.all_nil, Bool.and_true,
        Bool.and_eq_true]
      refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> exact noWriteIn_mono n1 (by omega) (by omega)
    refine frameStep r hp hpre b9_in_code (List.cons_ne_nil _ _) hx hb hL hK trivial
      extraOK_nil ⟨known_lit hax, known_ptr hdi, trivial⟩ trivial trivial
      fun st hm hK' hkb hpc ↦ ?_
    have hD' : BytesAt st.data.dmem (r.off 614) (r.digitsPre (2 * (j + 1))) := by
      rw [show 2 * (j + 1) = 2 * j + 2 by ring, digitsPre_succ2]
      refine BytesAt.append (hkb 614 _ (by rw [length_digitsPre]; omega)
        (by rw [length_digitsPre]; exact noWriteIn_mono n1 (by omega) (by omega)) hD) ?_
      rw [length_digitsPre, r.off_add]
      exact digits_of_covers hm (by omega) hc hs hd
    have hA' : r.AtDigits (j + 1) st.data :=
      ⟨hK', hD', regIs_reg hm ssi hs, regIs_reg hm sdx hd, regIs_lit hm sax,
        regIs_ptr hm (o := 615 + 2 * (j + 1)) (by rw [sdi]; push_cast; ring_nf)⟩
    by_cases hj : j = 28
    · subst hj
      have : st.pc = r.pc NativeRustcX64.Xmss.WotsLeaf.b10Offset := by
        simpa [PcOk, SBool.eval, NativeRustcX64.Xmss.WotsLeaf.b9_next] using hpc
      exact .done _ ⟨this, hA'⟩
    · have : st.pc = r.pc NativeRustcX64.Xmss.WotsLeaf.b9Offset := by
        have h1 := hpc
        simp only [PcOk, SBool.eval, bne_iff_ne, ne_eq, hj, not_false_eq_true,
          ite_true] at h1
        rw [h1]
        exact Run.label_of_block r hp b9_in_code rfl
      exact pc_at this (ih (j + 1) (by omega) (by omega) st.data hA')

end

end NativeRustcX64.WotsLeafProof
