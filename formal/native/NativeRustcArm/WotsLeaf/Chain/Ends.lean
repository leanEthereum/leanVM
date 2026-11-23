module

public import NativeRustcArm.Code.Xmss.WotsLeaf.Names

public import NativeRustcArm.WotsLeaf.Chain.Steps

/-!
# A chain's end stored

`b41` goes back to `b13` (`seg_b41`); `b13` stores chain `i`'s end at `440 + 16 i` after the ends
so far, reloads the chain values' address and goes on with chain `i + 1` at `b14` or, after chain
57, to `b44` (`seg_b13`, from `ok13`).
-/

namespace NativeRustcArm.WotsLeafProof.Chain

open NativeRustc NativeRustc.Xmss NativeRustcArm.Sym NativeRustcArm.Xmss.WotsLeaf

public section

/-- What `b13` does, from `ok13`. -/
theorem ok13_spec {i : Nat} (h : ok13 i = true) : ∃ S, exec b13 (s13 i) =
      some (S, .cond (.lit (i + 1 == 58)) NativeRustcArm.Xmss.WotsLeaf.label_27) ∧
    covers S.mem 0 (440 + 16 * i) 8 (.load 0 1384 8) = true ∧
    covers S.mem 0 (448 + 16 * i) 8 (.load 0 1392 8) = true ∧ blockOK S = true ∧
    Run.noWriteIn S 0 (440 + 16 * i) = true ∧ S.reg .X19 = some (.lit 136) ∧
    S.reg .X20 = some (.reg .X20) ∧ S.reg .X21 = some (.ptr 0 1976) ∧
    S.reg .X23 = some (.ptr 0 1632) ∧ S.reg .X28 = some (.lit (i + 1)) ∧
    S.reg .X22 = some (.load 0 8 8) ∧ S.reg .X9 = some (.ptr 0 380) := by
  unfold ok13 at h
  split at h
  · rename_i S x hx
    simp only [Bool.and_eq_true, beq_iff_eq, and_assoc] at h
    obtain ⟨c1, c2, hb, hn, s19, s20, s21, s23, s28, s22, s9, rfl⟩ := h
    exact ⟨S, hx, c1, c2, hb, hn, s19, s20, s21, s23, s28, s22, s9⟩
  · cases h

/-- The chain values' address, loaded from the frame's byte 8. -/
theorem load_values [Labels] {r : Run} {x E : List UInt8} {m : MachineData} (hK : r.CK x E m) :
    (r.env m).load 0 8 8 = r.m0.regs.X7.toBitVec := by
  rw [Env.load_of_bytesAt (length_wordBytes _) (CK.slot8 hK)]
  exact ofInt_ofBytes_wordBytes _

variable [NativeRustcArm.Host] {r : Run}

/-- **`b13`**: chain `i`'s end stored after the ends so far; on to chain `i + 1` at `b14`, or
`b44` after chain 57. -/
theorem seg_b13 (hp : Placed Xmss.WotsLeaf.code r.k) (hpre : r.Pre) {x E : List UInt8}
    {i : Nat} (hi : i < 58) (hE : E.length = 16 * i) {e : List UInt8} (he : e.length = 16)
    {R : MachineState → Prop} {m : MachineData} (hK : r.CK x E m)
    (h19 : Run.RegIs m .X19 (BitVec.ofNat 64 136)) (h20 : Run.RegIs m .X20 r.m0.regs.X1.toBitVec)
    (h21 : Run.RegIs m .X21 (r.off 1976)) (h23 : Run.RegIs m .X23 (r.off 1632))
    (h28 : Run.RegIs m .X28 (BitVec.ofNat 64 i)) (hcell : BytesAt m.dmem (r.off 1384) e)
    (cont : ∀ m', r.AtChain x (i + 1) (E ++ e) m' →
      Eventually (step1 NativeRustcArm.Host.exe) R ⟨m', if i + 1 = 58 then r.pc NativeRustcArm.Xmss.WotsLeaf.b44Offset else r.pc NativeRustcArm.Xmss.WotsLeaf.b14Offset⟩) :
    Eventually (step1 NativeRustcArm.Host.exe) R ⟨m, r.pc NativeRustcArm.Xmss.WotsLeaf.b13Offset⟩ := by
  obtain ⟨S, hx, c1, c2, hok, hnw, s19, s20, s21, s23, s28, s22, s9⟩ := ok13_spec (ok13_all i hi)
  have hwf := r.frame_wf hpre hK.1.1 (fun _ ↦ 0)
  have hk : KnownOK r m ([(XReg.X28, Sym.lit i)] ++ keptK) :=
    allOf_append ⟨known_lit h28, trivial⟩ ⟨known_lit h19, known_ptr h21, known_ptr h23, trivial⟩
  have hm := match_frameS hpre hK.1.1 hk
  refine blk r hp b13_in_code (List.cons_ne_nil _ _) hx hwf hm fun st hm1 hpc ↦ ?_
  have hK1 : Keep r (r.cSlots x) st.data :=
    hK.1.of_block hpre hm1 hwf hok (cSlots_kept r x (noWriteIn_mono hnw (by omega) (by omega)))
  have hE1 := r.bytesAt_kept hpre hm1 hwf (by omega) hK.2.1
    (noWriteIn_mono hnw (by omega) (by omega))
  have he1 : BytesAt st.data.dmem (r.off (440 + 16 * i)) e :=
    frame_copy16 hm1 (o := 440 + 16 * i) (o' := 1384) (by omega) c1
      (by rw [show 440 + 16 * i + 8 = 448 + 16 * i by omega]; exact c2) he hcell
  have hEe : BytesAt st.data.dmem (r.off 440) (E ++ e) := BytesAt.cat hE1 he1 (by rw [hE])
  have hlen : (E ++ e).length = 16 * (i + 1) := by rw [List.length_append, hE, he]; ring
  have hA : r.AtChain x (i + 1) (E ++ e) st.data := by
    refine ⟨by omega, hlen, ⟨hK1.1, SlotsAt.append hK1.2
      ⟨⟨rfl, by show 440 + (E ++ e).length ≤ 2656; omega, hEe⟩, trivial⟩⟩,
      regIs_lit hm1 s28, regIs_ptr hm1 s9, regIs_lit hm1 s19, regIs_ptr hm1 s21,
      regIs_ptr hm1 s23, regIs_reg hm1 s20 h20, ?_⟩
    unfold Run.RegIs
    rw [hm1.regs .X22 _ s22]
    exact load_values hK
  refine pc_at ?_ (cont _ hA)
  rw [pc_cond hpc (b := (i + 1 == 58)) rfl]
  by_cases h58 : i + 1 = 58
  · simp only [h58, beq_self_eq_true, ite_true]
    exact Run.label_of_block r hp b44_in_code rfl
  · have : (i + 1 == 58) = false := beq_false_of_ne h58
    simp only [this, h58, Bool.false_eq_true, ite_false]
    rfl

/-- **`b41`**: back to `b13`. -/
theorem seg_b41 (hp : Placed Xmss.WotsLeaf.code r.k) (hpre : r.Pre) {x E : List UInt8}
    {pos i : Nat} {e : List UInt8} (he : e.length = 16) {R : MachineState → Prop}
    {m : MachineData} (hK : r.CK x E m) (hR : r.SRegs m pos i)
    (hcell : BytesAt m.dmem (r.off 1384) e)
    (cont : ∀ m', r.CK x E m' → r.SRegs m' pos i → BytesAt m'.dmem (r.off 1384) e →
      Eventually (step1 NativeRustcArm.Host.exe) R ⟨m', r.pc NativeRustcArm.Xmss.WotsLeaf.b13Offset⟩) :
    Eventually (step1 NativeRustcArm.Host.exe) R ⟨m, r.pc NativeRustcArm.Xmss.WotsLeaf.b41Offset⟩ := by
  have hwf := r.frame_wf hpre hK.1.1 (fun _ ↦ 0)
  have hm := match_frameS hpre hK.1.1 (knownK hR (k := []) trivial)
  refine blk r hp b41_in_code (List.cons_ne_nil _ _) run_b41 hwf hm fun st hm1 hpc ↦ ?_
  exact pc_at (hpc.trans (Run.label_of_block r hp b13_in_code rfl))
    (cont _ (CK.of_block hpre hK hm1 hwf (by decide +kernel) (by decide +kernel))
      (SRegs.of_block hm1 rfl rfl rfl rfl rfl rfl hR)
      (r.bytesAt_kept hpre hm1 hwf (by omega) hcell (by rw [he]; decide +kernel)))

end

end NativeRustcArm.WotsLeafProof.Chain
