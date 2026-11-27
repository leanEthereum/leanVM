module

public import NativeRustcX64.Code.Sphincs.SphincsVerify.Names

public import NativeRustcX64.SphincsVerify.Chains.Ends

/-!
# Region 5b on x86-64: a layer's chains

`b108` reads chain `i`'s digit `d` and value (`seg_b108`); a digit above 2 goes straight to
`b107`, otherwise `b109` and the `3 - d` steps to `b141`; `b107` stores the chain's end and goes
on with chain `i + 1` (`chains_loop`, by induction on the chains left). From `AtChains l x` at
`b108`, the machine reaches `b142` with the 64 ends `chainEnds l x` at `20520`: **`chainsSpec`**.
`b108`'s symbolic state: region 0 the frame's first 12780 bytes, region 1 the chain's value.
-/

namespace NativeRustcX64.SphincsVerifyProof.Chains

open NativeRustc NativeRustc.Sphincs NativeRustcX64.Sym NativeRustcX64.Sphincs.SphincsVerify
open LeanVM.Protocol.KeccakHash

public section

theorem drop_take_one {x : List UInt8} {i : Nat} (hi : i < x.length) :
    (x.drop i).take 1 = [x.getD i 0] := by
  rw [List.drop_eq_getElem_cons hi, List.take_succ_cons, List.take_zero, List.getD_eq_getElem?_getD,
    List.getElem?_eq_getElem hi, Option.getD_some]

theorem load_one [Labels] {env : Env} {r off : Nat} {b : UInt8}
    (h : BytesAt env.mem0 (env.base r + BitVec.ofNat 64 off) [b]) :
    env.load r off 1 = BitVec.ofNat 64 b.toNat := by
  rw [Env.load_of_bytesAt (n := 1) rfl h]
  show BitVec.ofInt 64 (0 * 256 + (b.toNat : Int)) = _
  simp

theorem length_ends (r : Run) {l : Nat} (hl : l < 3) (x : List UInt8) {i : Nat} (hi : i ≤ 64) :
    ((List.range i).map (chainEnd r l x)).flatten.length = 16 * i := by
  rw [length_flatten_uniform _ (fun e he ↦ by
    obtain ⟨j, hj, rfl⟩ := List.mem_map.mp he
    exact length_chain _ _ _ _ _ (SigMemBytes.length_wots_getD r.sigB r.hsig hl (by simp at hj; omega)))]
  simp

theorem ends_succ (r : Run) (l : Nat) (x : List UInt8) (i : Nat) :
    ((List.range (i + 1)).map (chainEnd r l x)).flatten =
      ((List.range i).map (chainEnd r l x)).flatten ++ chainEnd r l x i := by
  rw [List.range_succ, List.map_append, List.flatten_append]
  simp

theorem digit_cond (d : Nat) : (!decide (d < 2) && !decide (d = 2)) = decide (2 < d) := by
  by_cases h1 : d < 2
  · simp [h1, show ¬2 < d by omega]
  · by_cases h2 : d = 2
    · subst h2
      decide
    · simp [h1, h2, show 2 < d by omega]

theorem ult_ofNat {a b : Nat} (ha : a < 2 ^ 64) (hb : b < 2 ^ 64) :
    (BitVec.ofNat 64 a).ult (BitVec.ofNat 64 b) = decide (a < b) := by
  rw [BitVec.ult, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb]

variable [ElfHost] {r : Run}

/-- **`b108`**: chain `i`'s digit and value; then, through `b109`, its steps and `b141`, or
straight on, `b107`. -/
theorem seg_b108 (hp : PlacedIn Sphincs.SphincsVerify.code r.sec r.k) (hc : Callees) (hpre : r.Pre)
    {l : Nat} {x E : List UInt8} (hl : l < 3) (hx : x.length = 64) {i : Nat} (hi : i < 64)
    (hEl : E.length = 16 * i) {R : MachineState → Prop} {m : MachineData} (hF : r.Frame m)
    (hK : KeepRest r l x E m) (h0 : Run.RegIs m .rax (BitVec.ofNat 64 i))
    (h12 : Run.RegIs m .r12 (r.off 4072))
    (hf : Funcs m)
    (cont : ∀ m', r.Frame m' → KeepRest r l x E m' → r.WordAt m' 80 i.toUInt64 →
      r.WordAt m' 176 (16 * i).toUInt64 → Run.RegIs m' .r12 (r.off 4072) →
      BytesAt m'.dmem (r.off 1592) (chainEnd r l x i) → Funcs m' →
      Eventually (elfStep1 ElfHost.exe) R ⟨m', r.pc NativeRustcX64.Sphincs.SphincsVerify.b107Offset⟩) :
    Eventually (elfStep1 ElfHost.exe) R ⟨m, r.pc NativeRustcX64.Sphincs.SphincsVerify.b108Offset⟩ := by
  have hv := SigMemBytes.length_wots_getD r.sigB r.hsig hl hi
  have hval : BytesAt m.dmem (r.off (17436 + 1028 * l + 16 * i)) ((r.layerSig l).wots.getD i []) := by
    have := BytesAt.slice hK.1.2 (4656 + 1028 * l + 16 * i) 16
    rwa [Run.off_add, show r.sig = sigOfBytes r.sigB from rfl, SigMemBytes.sigMem_wots r.sigB r.hsig hl hi,
      show 12780 + (4656 + 1028 * l + 16 * i) = 17436 + 1028 * l + 16 * i by omega] at this
  have hdig : BytesAt m.dmem (r.off 0 + BitVec.ofNat 64 (3048 + i)) [x.getD i 0] := by
    have := BytesAt.slice hK.2.2.2.1 i 1
    rwa [drop_take_one (by omega), Run.off_add, ← Nat.zero_add (3048 + i), ← Run.off_add] at this
  have hti : (m.regs.get64 .rax).toNat = i := by
    rw [show m.regs.get64 .rax = BitVec.ofNat 64 i from h0]
    show (BitVec.ofNat 64 i).toNat = i
    rw [BitVec.toNat_ofNat]
    omega
  obtain ⟨m0, w0⟩ := r.frame_mapped hpre hF.2.2.2 (a := 0) (n := 12780) (by decide)
  obtain ⟨m1, w1⟩ := r.frame_mapped hpre hF.2.2.2 (a := 17436 + 1028 * l + 16 * i) (n := 16)
    (by omega)
  have hwf : (Env.ofMachine m [(r.off 0, 12780), (r.off (17436 + 1028 * l + 16 * i), 16)]).WF :=
    Env.wf_of ⟨⟨m0, w0⟩, ⟨m1, w1⟩, trivial⟩
      (List.pairwise_pair.mpr (apart_regions hpre (by decide) (by omega) (by omega)))
  have hm : Match (Env.ofMachine m [(r.off 0, 12780), (r.off (17436 + 1028 * l + 16 * i), 16)])
      s117 m := by
    refine match_ofMachine ⟨rfl, rfl, trivial⟩ ⟨?_, trivial⟩ trivial ⟨?_, trivial⟩ ⟨?_, trivial⟩
    · show m.regs.get64 .rsp = r.off 0 + BitVec.ofInt 64 0
      rw [off_add_ofInt 0 (b := 0) (by simp), off_zero']
      exact hF.1
    · show (m.regs.get64 .rax).toNat < 64
      rw [hti]
      exact hi
    · show BinOp.apply .add .W64
        ((Env.ofMachine m [(r.off 0, 12780), (r.off (17436 + 1028 * l + 16 * i), 16)]).load 0 184 8)
        (BinOp.apply .shl .W64 (m.regs.get64 .rax) (BitVec.ofNat 64 4)) =
          r.off (17436 + 1028 * l + 16 * i) + BitVec.ofInt 64 0
      rw [load0_word hK.2.1.2.2.2.2.2.2.2.2.2, show m.regs.get64 .rax = BitVec.ofNat 64 i from h0,
        shl4 (by omega), off_add_ofInt (17436 + 1028 * l + 16 * i) (b := 17436 + 1028 * l + 16 * i)
          (by simp)]
      simp only [BinOp.apply, low_W64, ext_W64]
      exact r.off_add _ _
  refine blk r hp b108_in_code (List.cons_ne_nil _ _) run_b108 hwf (fun _ h ↦ nomatch h) hm
    fun st hm1 hpc ↦ ?_
  have hD : (Sym.un (.zext .W8) .W32 (.loadx 0 3048 (.reg .rax) 1)).eval
      (Env.ofMachine m [(r.off 0, 12780), (r.off (17436 + 1028 * l + 16 * i), 16)]) =
        BitVec.ofNat 64 (x.getD i 0).toNat := by
    show UnOp.apply (.zext .W8) .W32 (Env.load _ 0 (3048 + (m.regs.get64 .rax).toNat) 1) = _
    rw [hti, load_one hdig, zext8 (x.getD i 0).toNat_lt]
  have hsi : Run.RegIs st.data .rbp (BitVec.ofNat 64 (x.getD i 0).toNat) := by
    unfold Run.RegIs reg
    rw [hm1.regs .rbp _ rfl]
    exact hD
  have h12' : Run.RegIs st.data .r12 (r.off 4072) := by
    unfold Run.RegIs reg
    rw [reg_same hm1 rfl]
    exact h12
  have hf' : Funcs st.data := ⟨regIs_reg hm1 rfl hf.1, regIs_reg hm1 rfl hf.2⟩
  have hsp : rspOf st.data = r.base := by
    rw [rspOf, hm1.regs .rsp _ rfl]
    show r.off 0 + BitVec.ofInt 64 0 = r.base
    rw [off_add_ofInt 0 (b := 0) (by simp), off_zero']
  have hout := written_three hm1 hwf hpre (n0 := 12780) (by rw [← off_zero']; rfl) (a := 80)
    (n := 8) (a' := 176) (n' := 8) (a'' := 1592) (n'' := 16) (by decide) (by decide) (by decide)
    (by decide +kernel)
  have hF1 : r.Frame st.data :=
    Run.Frame.of_change hF.2.1 hF.2.2.1 hF.2.2.2 hsp hout
      (fun _ hp ↦ hp.elim (r.inRange_off hpre (by decide))
        (fun hp ↦ hp.elim (r.inRange_off hpre (by decide)) (r.inRange_off hpre (by decide))))
      (hm1.kept hwf)
  have hK1 := KeepRest.of_change hx (by omega) hK hout
    (fun o ho hk hp ↦ hp.elim (r.not_inRange_off hpre (by decide) ho (by omega))
      (fun hp ↦ hp.elim (r.not_inRange_off hpre (by decide) ho (by omega))
        (r.not_inRange_off hpre (by decide) ho (by omega))))
    (reg_same hm1 rfl)
  have h80 : r.WordAt st.data 80 i.toUInt64 := by
    have := bytesAt_write_val hm1 (r := 0) (b := r.off 0) (sz := 12780) rfl (o := 80) (n := 8)
      (v := .reg .rax) (by decide) (by decide +kernel)
    rw [Run.off_add, bytes_word_of (x := Sym.eval (Env.ofMachine m [(r.off 0, 12780),
      (r.off (17436 + 1028 * l + 16 * i), 16)]) (.reg .rax)) (w := i.toUInt64) h0] at this
    exact this
  have h168 : r.WordAt st.data 176 (16 * i).toUInt64 := by
    have := bytesAt_write_val hm1 (r := 0) (b := r.off 0) (sz := 12780) rfl (o := 176) (n := 8)
      (v := .bin .shl .W64 (.reg .rax) (.lit 4)) (by decide) (by decide +kernel)
    rw [Run.off_add, bytes_word_of (x := Sym.eval (Env.ofMachine m [(r.off 0, 12780),
      (r.off (17436 + 1028 * l + 16 * i), 16)]) (.bin .shl .W64 (.reg .rax) (.lit 4)))
      (w := (16 * i).toUInt64) (by
      show BinOp.apply .shl .W64 (m.regs.get64 .rax) (BitVec.ofNat 64 4) = _
      rw [show m.regs.get64 .rax = BitVec.ofNat 64 i from h0, shl4 (by omega)]
      rfl)] at this
    exact this
  have hcell : BytesAt st.data.dmem (r.off 1592) ((r.layerSig l).wots.getD i []) := by
    have := copy16 hm1 (k := 0) (b := r.off 0) rfl (o := 1592) (by decide) (k' := 1) (o' := 0)
      (by decide +kernel) (by decide +kernel) hv (bytesAt_add_zero hval)
    rwa [Run.off_add] at this
  have hcond : (SBool.and
      (.not (.cmp .ult .W64 (.un (.zext .W8) .W32 (.loadx 0 3048 (.reg .rax) 1)) (.lit 2)))
      (.not (.cmp .eq .W64 (.un (.zext .W8) .W32 (.loadx 0 3048 (.reg .rax) 1)) (.lit 2)))).eval
        (Env.ofMachine m [(r.off 0, 12780), (r.off (17436 + 1028 * l + 16 * i), 16)]) =
      decide (2 < (x.getD i 0).toNat) := by
    show (!(CmpOp.apply .ult .W64 (Sym.eval _ (.un (.zext .W8) .W32 (.loadx 0 3048 (.reg .rax) 1)))
      (BitVec.ofNat 64 2)) && !(CmpOp.apply .eq .W64 (Sym.eval _ (.un (.zext .W8) .W32
        (.loadx 0 3048 (.reg .rax) 1))) (BitVec.ofNat 64 2))) = _
    have hlt := (x.getD i 0).toNat_lt
    rw [hD]
    simp only [CmpOp.apply, low_W64]
    rw [ult_ofNat (by omega) (by decide), beq_ofNat (by omega) (by decide)]
    exact digit_cond _
  have hpc' : st.pc = if decide (2 < (x.getD i 0).toNat) = true then Labels.label NativeRustcX64.Sphincs.SphincsVerify.label_52
      else r.pc (NativeRustcX64.Sphincs.SphincsVerify.b108Offset + b108.length) := by
    rw [← hcond]
    exact pc_cond hpc
  by_cases hd : (x.getD i 0).toNat ≤ 2
  · have hp' : st.pc = r.pc NativeRustcX64.Sphincs.SphincsVerify.b109Offset := by
      rw [hpc']
      split
      next h =>
        simp only [decide_eq_true_eq] at h
        omega
      next => rfl
    refine pc_at hp' (seg_b109 hp hpre hx (by omega) hi hv hF1 hK1 h80 h168 hsi h12' hcell hf'
      fun m1 k1 g1 c1 ↦ ?_)
    have hk : 3 - (x.getD i 0).toNat = 2 - (x.getD i 0).toNat + 1 := by omega
    exact steps hp hc hpre hx (by omega) (2 - (x.getD i 0).toNat) _ (by omega) hv k1 g1 c1
      fun m2 k2 g2 c2 ↦ seg_b141 hp hpre hx (by omega) (length_chain _ _ _ _ _ hv) k2 g2.2.1 c2 g2.2.2
        fun m3 k3 g3 c3 f3 ↦ cont m3 k3.1 k3.2.1 k3.2.2.1 k3.2.2.2.1 g3 (by
          unfold chainEnd
          rw [hk]
          exact c3) f3
  · have hp' : st.pc = r.pc NativeRustcX64.Sphincs.SphincsVerify.b107Offset := by
      rw [hpc']
      split
      next => exact labelAt r hp b107_in_code rfl
      next h =>
        simp only [decide_eq_true_eq] at h
        omega
    refine pc_at hp' (cont _ hF1 hK1 h80 h168 h12' ?_ hf')
    unfold chainEnd
    rw [show 3 - (x.getD i 0).toNat = 0 by omega]
    exact hcell

/-- **The chains from chain `i`**: the ends of chains `i .. 63` after those before. -/
theorem chains_loop (hp : PlacedIn Sphincs.SphincsVerify.code r.sec r.k) (hc : Callees) (hpre : r.Pre)
    {l : Nat} {x : List UInt8} (hl : l < 3) (hx : x.length = 64) :
    ∀ (n i : Nat) {m : MachineData}, i + n = 64 → 0 < n → r.Frame m →
      KeepRest r l x ((List.range i).map (chainEnd r l x)).flatten m →
      Run.RegIs m .rax (BitVec.ofNat 64 i) → Run.RegIs m .r12 (r.off 4072) → Funcs m →
      Eventually (elfStep1 ElfHost.exe)
        (fun st ↦ st.pc = r.pc NativeRustcX64.Sphincs.SphincsVerify.b142Offset ∧ r.AtWotsPk l (r.chainEnds l x) st.data) ⟨m, r.pc NativeRustcX64.Sphincs.SphincsVerify.b108Offset⟩
  | 0, _, _, _, hn, _, _, _, _, _ => absurd hn (by decide)
  | n + 1, i, m, hin, _, hF, hK, h0, h12, hf => by
    have hi : i < 64 := by omega
    have hEl := length_ends r hl x (i := i) (by omega)
    refine seg_b108 hp hc hpre hl hx hi hEl hF hK h0 h12 hf fun m1 f1 k1 a1 b1 g1 c1 hf1 ↦ ?_
    refine seg_b107 hp hpre hx hi hEl
      (length_chain _ _ _ _ _ (SigMemBytes.length_wots_getD r.sigB r.hsig hl hi)) f1 k1 a1 b1 g1 c1 hf1
      fun m2 f2 k2 g0 g12 hf2 ↦ ?_
    have k2' : KeepRest r l x ((List.range (i + 1)).map (chainEnd r l x)).flatten m2 := by
      rw [ends_succ]
      exact k2
    by_cases h : i + 1 = 64
    · simp only [h, ↓reduceIte]
      rw [h] at k2'
      refine .done _ ⟨rfl, hl, ?_, f2, k2'.1, k2'.2.1, g12, k2'.2.2.1, ?_, hf2⟩
      · rw [chainEnds_eq]
        exact length_ends r hl x (le_refl _)
      · rw [chainEnds_eq]
        exact k2'.2.2.2.2
    · simp only [h, ↓reduceIte]
      exact chains_loop hp hc hpre hl hx n (i + 1) (by omega) (by omega) f2 k2' g0 g12 hf2

/-- **Region 5b on x86-64, a layer's chains**: from `AtChains l x` at `b108` to
`AtWotsPk l (chainEnds l x)` at `b142`. -/
theorem chainsSpec : ChainsSpec := by
  intro l x r hp hc hpre m ⟨hl, hx, hF, hI, hLS, h0, h12, h13, hxa, hf⟩
  exact chains_loop hp hc hpre hl hx 64 0 rfl (by decide) hF
    ⟨hI, hLS, h13, hxa, fun _ h ↦ absurd h (by simp)⟩ h0 h12 hf

end

end NativeRustcX64.SphincsVerifyProof.Chains
