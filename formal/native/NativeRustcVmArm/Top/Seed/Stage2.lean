module

public import NativeRustcVmArm.Code.Vm.KeccakF.Names
public import NativeRustcVmArm.Code.Vm.Memcpy.Names
public import NativeRustcVmArm.Top.Seed.Basic

/-!
# `seed`: the public input, the permutation, the copy out

From `S1` after `memset`, `b2` copies the public input to the frame's bytes 40 to 71, so that
the frame's bytes 8 to 207 hold the state `Model.seed` permutes (`seed_state`); `keccak_f`
permutes it in place, `b3` and `memcpy` copy it to the output: `stage2`, to `S2`.
-/

namespace NativeRustcVmArm.Top.Seed

open NativeRustcArm NativeRustcArm.Sym NativeRustcVmArm.Vm.Seed NativeVm.Model
open NativeRustcVm (WordsAt Region)

public section

variable [Host] {k : Nat}

theorem stage2 (hp : Placed code k)
    (hkf : Spec (Labels.label NativeRustcVmArm.Vm.KeccakF.entryLabel) KeccakFPre KeccakFPost)
    (hmemcpy : Spec (Labels.label NativeRustcVmArm.Vm.Memcpy.entryLabel) MemcpyPre MemcpyPost) {m0 : MachineData}
    (hpre : SeedPre m0) {st4 : MachineState} (hpc4 : st4.pc = Host.addrOf (k + NativeRustcVmArm.Vm.Seed.b2Offset))
    (hS1 : S1 m0 st4.data) :
    Eventually (step1 Host.exe) (fun st ↦ st.pc = Host.addrOf (k + NativeRustcVmArm.Vm.Seed.b4Offset) ∧ S2 m0 st.data) st4 := by
  have g := geo_of hpre
  obtain ⟨⟨-, -, hmap⟩, ⟨hrcW, -, -⟩, -, -, ⟨hpubM, -⟩, ⟨houtM, -⟩, -, -, -⟩ := hpre
  obtain ⟨hs928, hs16, hF, hF8, hF72, hsb0, hpubA, hpubN, houtA, houtN, hrcA, hrcN, -, -, -⟩ := g
  have hrcL : LeanVM.Parameters.keccakRC.length = 24 := rfl
  have hS : seedStack = 928 := rfl
  have hKF : keccakFStack = 400 := rfl
  have hsl := m0.regs.SP.toBitVec.isLt
  set F := frameOf m0 with hFdef
  have hFm : Mapped m0.dmem F 240 :=
    Mapped.within hmap (by rw [hsb0]; omega) (by rw [hsb0, hF]; omega) (by rw [hsb0, hF]; omega)
  obtain ⟨hB4, hX19_4, hX20_4, hiv4, hz4⟩ := hS1
  have hsp4 : st4.data.regs.SP.toBitVec = F := hB4.sp
  have hpubF : F.toNat + 240 ≤ m0.regs.X3.toBitVec.toNat ∨
      m0.regs.X3.toBitVec.toNat + 32 ≤ F.toNat := by omega
  have hwf4 : (Env.ofMachine st4.data [(F, 240), (m0.regs.X3.toBitVec, 32)]).WF :=
    Env.wf_of ⟨⟨Mapped.kept hFm hB4.kept, show F.toNat + 240 ≤ 2 ^ 64 by omega⟩,
      ⟨Mapped.kept hpubM hB4.kept, hpubN⟩, trivial⟩ (List.pairwise_pair.mpr hpubF)
  have hm4 : Match (Env.ofMachine st4.data [(F, 240), (m0.regs.X3.toBitVec, 32)]) pubS
      st4.data :=
    match_ofMachine ⟨rfl, fun _ ↦ show F.toNat % 16 = 0 by omega, rfl, fun h ↦ absurd h (by decide),
      trivial⟩
      (show st4.data.regs.SP.toBitVec = F + BitVec.ofInt 64 0 by rw [hsp4]; simp)
      ⟨show (st4.data.regs.getXReg .X19).toBitVec = m0.regs.X3.toBitVec + BitVec.ofInt 64 0 by
        show st4.data.regs.X19.toBitVec = _
        rw [hX19_4]; simp, trivial⟩
      trivial trivial trivial
  refine exec_at (hb2 hp) run_b2 hwf4 hpc4 hm4 fun st5 hm5 hpc5 ↦ ?_
  have hb2m := b2_mem1
  rw [after_eq run_b2] at hb2m
  have hw5 : ∀ q, Written (Env.ofMachine st4.data [(F, 240), (m0.regs.X3.toBitVec, 32)])
      (after b2 pubS) q → F.toNat + 40 ≤ q.toNat ∧ q.toNat < F.toNat + 72 := by
    intro q hq
    rw [after_eq run_b2] at hq
    exact written_sub (r := 0) rfl hb2m hq
  have hk2 := b2_keeps
  rw [after_eq run_b2] at hk2
  have hB5 : Body m0 240 slots (InStack m0 928) st5.data :=
    hB4.block slotsIn (by show 240 ≤ m0.regs.SP.toBitVec.toNat; omega) hm4 hm5 hwf4 rfl hk2
      fun q hq ↦ by
        have := hw5 q (by rw [after_eq run_b2]; exact hq)
        unfold InStack; omega
  have hsame5 : SameOutside st4.data.dmem st5.data.dmem
      (fun q ↦ F.toNat + 40 ≤ q.toNat ∧ q.toNat < F.toNat + 72) := fun q hq ↦
    hm5.get?_mem0 hwf4 fun hw ↦ hq (hw5 q (by rw [after_eq run_b2]; exact hw))
  -- The state in the frame.
  have hP5 : ∀ P : Vector UInt64 4, WordsAt m0.dmem m0.regs.X3.toBitVec P.toList →
      WordsAt st5.data.dmem (F + BitVec.ofNat 64 40) P.toList := by
    intro P hP
    have hP4 : WordsAt st4.data.dmem m0.regs.X3.toBitVec P.toList :=
      wordsAt_keep hP hB4.same (by rw [Vector.length_toList]; omega) fun q hq ↦ by
        unfold InStack at hq; rw [Vector.length_toList]; omega
    refine NativeRustcVm.wordsAt_iff.mpr fun q hq ↦ ?_
    have hq4 : q < 4 := by simpa using hq
    have hw := b2_words q hq4
    rw [after_eq run_b2] at hw
    have h := hm5.bytesAt_write (r := 0) (o := 40 + 8 * q) (n := 8) (b := F) (sz := 240) rfl
      (by omega) hw
    have hl : (Sym.load 1 (8 * q) 8).eval
        (Env.ofMachine st4.data [(F, 240), (m0.regs.X3.toBitVec, 32)]) = P.toList[q].toBitVec :=
      load_wordAt (hP4.getElem hq)
    rw [hl, ← wordBytes_byteOf, ← addr_add] at h
    exact h
  have hst5 : ∀ w : List UInt64, w.length = m0.regs.X2.toBitVec.toNat →
      WordsAt m0.dmem m0.regs.X1.toBitVec w → ∀ P : Vector UInt64 4,
      WordsAt m0.dmem m0.regs.X3.toBitVec P.toList →
      WordsAt st5.data.dmem (F + BitVec.ofNat 64 8)
        (Vector.ofFn (n := 25) fun i ↦ if h : i.val < 4 then (fiatShamirIv w.toArray)[i.val]
          else if h' : i.val < 8 then P[i.val - 4] else 0).toList := by
    intro w hw hbc P hP
    rw [seed_state, NativeRustcVm.wordsAt_append_iff, NativeRustcVm.wordsAt_append_iff]
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · exact wordsAt_keep (hiv4 w hw hbc) hsame5 (by simp; omega) fun q hq ↦ by simp; omega
    · simp only [Vector.length_toList, addr_add]
      exact hP5 P hP
    · simp only [List.length_append, Vector.length_toList, addr_add]
      have hz : BytesAt st4.data.dmem (F + BitVec.ofNat 64 72) (List.replicate (8 * 17) 0) := hz4
      refine wordsAt_zeros 17 (bytesAt_keep hz hsame5 ?_ fun q hq ↦ ?_)
      · rw [List.length_replicate, hF72]; omega
      · rw [List.length_replicate, hF72]; omega
  -- `keccak_f`, in place.
  have hsp5 : st5.data.regs.SP.toBitVec = F := hB5.sp
  have hX0_5 : st5.data.regs.X0.toBitVec = F + BitVec.ofNat 64 8 := hm5.regs .X0 _ rfl
  have hsb5 : (stackBelow st5.data keccakFStack).toNat = m0.regs.SP.toBitVec.toNat - 640 := by
    show (st5.data.regs.SP.toBitVec - BitVec.ofNat 64 400).toNat = _
    rw [hsp5, toNat_subAddr (by rw [hF]; omega), hF]; omega
  have hsb5' : (st5.data.regs.SP.toBitVec - BitVec.ofNat 64 keccakFStack).toNat =
      m0.regs.SP.toBitVec.toNat - 640 := hsb5
  have hx0_5 : st5.data.regs.X0.toBitVec.toNat = m0.regs.SP.toBitVec.toNat - 232 := by
    rw [hX0_5, hF8]
  have hpre5 : KeccakFPre st5.data := by
    refine ⟨⟨?_, ?_, ?_⟩, ⟨?_, hrcN, ?_⟩, ?_, ?_, ?_, ?_⟩
    · show st5.data.regs.SP.toBitVec.toNat % 16 = 0
      rw [hsp5, hF]; omega
    · show 400 ≤ st5.data.regs.SP.toBitVec.toNat
      rw [hsp5, hF]; omega
    · exact Mapped.kept (Mapped.within hmap (by omega) (by omega) (by omega)) hB5.kept
    · exact wordsAt_keep hrcW hB5.same (by rw [hrcL]; omega) fun q hq ↦ by
        unfold InStack at hq; rw [hrcL]; omega
    · show _ ∨ _
      omega
    · show Mapped st5.data.dmem st5.data.regs.X0.toBitVec 200
      rw [hX0_5]
      exact Mapped.kept (Mapped.within hFm (by omega) (by rw [hF8]; omega) (by rw [hF8]; omega))
        hB5.kept
    · show st5.data.regs.X0.toBitVec.toNat + 200 ≤ 2 ^ 64
      omega
    · show _ ∨ _
      omega
    · show _ ∨ _
      omega
  refine call_then hpc5 hkf hpre5 fun st6 hpc6 hpost6 ↦ ?_
  obtain ⟨hkf6, hsame6, hsaved6⟩ := hpost6
  have hB6 : Body m0 240 slots (InStack m0 928) st6.data := by
    refine hB5.call slotsIn (by show 240 ≤ m0.regs.SP.toBitVec.toNat; omega) hsame6 hsaved6
      fun q hq ↦ ?_
    rcases hq with hq | hq
    · rw [inRange_nat (by omega)] at hq
      unfold InStack; omega
    · change InRange (st5.data.regs.SP.toBitVec - BitVec.ofNat 64 400) 400 q at hq
      rw [inRange_below (by rw [hsp5, hF]; omega), hsp5, hF] at hq
      unfold InStack; omega
  -- `b3`: `memcpy`'s arguments.
  rw [show k + NativeRustcVmArm.Vm.Seed.b2Offset + b2.length = k + NativeRustcVmArm.Vm.Seed.b3Offset from by rw [Nat.add_assoc, NativeRustcVmArm.Vm.Seed.b2_next]] at hpc6
  refine exec_at (hb3 hp) run_b3 (Env.wf_nil st6.data) hpc6 (match_nil st6.data)
    fun st7 hm7 hpc7 ↦ ?_
  have hk3 := b3_keeps
  rw [after_eq run_b3] at hk3
  have hd7 : st7.data.dmem = st6.data.dmem := hm7.dmem_eq (Env.wf_nil _) hk3.2
  have hB7 : Body m0 240 slots (InStack m0 928) st7.data :=
    hB6.block slotsIn (by show 240 ≤ m0.regs.SP.toBitVec.toNat; omega) (match_nil _) hm7
      (Env.wf_nil _) rfl hk3.1 fun p ⟨w, hw, _⟩ ↦ by rw [hk3.2] at hw; cases hw
  have hX0_7 : st7.data.regs.X0 = m0.regs.X0 := by
    have h7 : st7.data.regs.X0 = st6.data.regs.X20 := UInt64.toBitVec_inj.mp (hm7.regs .X0 _ rfl)
    have h6 : st6.data.regs.X20 = st5.data.regs.X20 := hsaved6.1 .X20 rfl
    have h5 : st5.data.regs.X20 = st4.data.regs.X20 :=
      UInt64.toBitVec_inj.mp (hm5.regs .X20 _ rfl)
    exact h7.trans (h6.trans (h5.trans hX20_4))
  have hX1_7 : st7.data.regs.X1.toBitVec = F + BitVec.ofNat 64 8 := by
    have h := hm7.regs .X1 _ rfl
    refine h.trans ?_
    sym_simp
    show st6.data.regs.SP.toBitVec + _ = _
    rw [hB6.sp]
    rfl
  have hX2_7 : st7.data.regs.X2.toNat = 200 := by
    show (st7.data.regs.getXReg .X2).toBitVec.toNat = 200
    rw [hm7.regs .X2 _ rfl]; rfl
  have hpre7 : MemcpyPre st7.data := by
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · rw [hX0_7, hX2_7]; exact Mapped.kept houtM hB7.kept
    · rw [hX1_7, hX2_7]
      exact Mapped.kept (Mapped.within hFm (by omega) (by rw [hF8]; omega) (by rw [hF8]; omega))
        hB7.kept
    · show st7.data.regs.X0.toBitVec.toNat + st7.data.regs.X2.toNat ≤ 2 ^ 64
      rw [hX0_7, hX2_7]; omega
    · show st7.data.regs.X1.toBitVec.toNat + st7.data.regs.X2.toNat ≤ 2 ^ 64
      rw [hX1_7, hX2_7, hF8]; omega
    · show _ ∨ _
      rw [hX0_7, hX1_7, hX2_7, hF8]; omega
  refine call_then hpc7 hmemcpy hpre7 fun st8 hpc8 hpost8 ↦ ?_
  obtain ⟨-, hcp8, hsame8, hsaved8⟩ := hpost8
  rw [hX0_7, hX1_7, hX2_7, hd7] at hcp8
  rw [hX0_7, hX2_7] at hsame8
  have hB8 : Body m0 240 slots (fun q ↦ InStack m0 928 q ∨ InRange m0.regs.X0.toBitVec 200 q)
      st8.data := by
    refine (hB7.mono fun _ h ↦ Or.inl h).call slotsIn
      (by show 240 ≤ m0.regs.SP.toBitVec.toNat; omega) hsame8 hsaved8 fun q hq ↦ ⟨Or.inr hq, ?_⟩
    rw [inRange_nat (by omega)] at hq
    omega
  rw [show k + NativeRustcVmArm.Vm.Seed.b3Offset + b3.length = k + NativeRustcVmArm.Vm.Seed.b4Offset from by rw [Nat.add_assoc, NativeRustcVmArm.Vm.Seed.b3_next]] at hpc8
  refine Eventually.done _ ⟨hpc8, hB8, fun w hw hbc P hP ↦ ?_⟩
  have h5 := hst5 w hw hbc P hP
  rw [← hX0_5] at h5
  have h6 := hkf6 _ h5
  rw [hX0_5] at h6
  have e := bytesOf_of_bytesAt h6
  rw [NativeRustcVm.length_wordsBytes, Vector.length_toList] at e
  have e' : NativeRustcArm.bytesOf st6.data.dmem (F + BitVec.ofNat 64 8) 200 = _ := e
  rw [e'] at hcp8
  exact hcp8

end

end NativeRustcVmArm.Top.Seed
