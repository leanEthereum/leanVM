module

public import NativeRustcVmArm.Code.Vm.Keccak256WordsOfHashWords.Names
public import NativeRustcVmArm.Wire.PhaseM.Hash

/-!
# `phase_m`: the leaves hashed, run

`hash_entry`: the hashing's set-up (`b26`), from `Rows` to leaf 0. `hash_step`: leaf `i` hashed
(`b27`, `keccak256_words::<hash_words's closure>`) and its node stored (`b28`). `hash_run`: the
loop, to the climb's set-up (`Climb0`).
-/

namespace NativeRustcVmArm.Wire.PhaseM

open NativeRustcArm NativeRustcArm.Sym NativeRustcVm.Wire NativeVm.Wire
open NativeRustcVmArm.Ring (Fr base)
open NativeRustcVm (WordAt WordsAt InAny Region)
open NativeRustcVmArm.Vm.PhaseM
open LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.Compile LeanVM.Protocol.KeccakHash

public section

variable {m0 : MachineData} {bp : BitVec 64} {B : List UInt8} {c : Nat}

theorem ofNat_toNat_bv {x : BitVec 64} {n : Nat} (h : x.toNat = n) :
    x = BitVec.ofNat 64 n := by
  apply BitVec.eq_of_toNat_eq
  rw [h, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by have := x.isLt; omega)]

theorem wa_add (o n : Nat) :
    BinOp.apply .add .W64 (wa m0 o) (BitVec.ofNat 64 n) = wa m0 (o + n) := by
  rw [add_lit, wa, NativeRustcVm.addr_add_add]

theorem nodes0_get {qs : List Nat} {lw : Nat} {rows : List (List K)} {i : Nat}
    (hl : rows.length = (sortD qs).length) (hi : i < (sortD qs).length) :
    (nodes0 qs lw rows)[i]'(by simp [hl]; omega) = ((sortD qs)[i],
      NativeVm.Model.hashWords
        (((leavesOf lw rows)[i]'(by simp [hl]; omega)).map K.lane).toArray) := by
  simp only [nodes0, List.getElem_zip, List.getElem_map, leaf_hash]

variable [Host] {k : Nat}

/-- **The hashing's set-up.** -/
theorem hash_entry (hp : Placed code k) (G : Geo m0 bp B) {count : Nat} {qs : List Nat}
    {height lw : Nat} {rows : List (List K)} {c6 : Nat} {st : MachineState}
    (h : Rows m0 bp B c k count qs height lw rows c6 st) :
    Eventually (step1 Host.exe) (HashSt m0 bp B c k count qs height lw rows c6 0) st := by
  obtain ⟨hpc, hb, hmod, hql, hc0, hcnt, hqlt, h32, h64, hps0, hps256, hrl, hrw, x21, x24, x26,
    f56, f48, f40, hqW, hpW, hlv, hrd⟩ := h
  have hst := G.st
  refine blkW hp b26_in_code (by simp [b26]) run_b26 (by decide) rfl hst hb.fr hpc
    fun s1 hfr1 _ hm1 hpc1 ↦ .done _ ?_
  have hm := frEnv_match hst hb.fr
  have hwf := frEnv_wf hst hb.fr
  have hs1 := Match.sameOutside_in hm1 hwf (r0 := 0) (o := 32) (n := 8) rfl (by omega) (by decide)
  have r1 : ∀ r ∈ [XReg.X19, .X20, .X21, .X22, .X26], s1.data.regs.getXReg r =
      st.data.regs.getXReg r := regs_of hm hm1 (by decide)
  have hb1 : Base m0 s1.data := hb.of_regs hfr1 fun r hr ↦ r1 r (by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
    rcases hr with rfl | rfl | rfl <;> simp)
  have e56 : (frEnv m0 st.data).load 0 56 8 = lw.toUInt64.toBitVec := load_fw f56
  have e40 : (frEnv m0 st.data).load 0 40 8 = wa m0 352512 := load_fw f40
  have hlwN : lw.toUInt64.toBitVec.toNat = lw := by
    rw [UInt64.toNat_toBitVec, toNat_toUInt64_of_lt (by omega)]
  have hqb : 0 + ((qs.map Nat.toUInt64).flatMap NativeRustcVm.wordBytes).length ≤ workBytes := by
    rw [NativeRustcVm.length_wordsBytes, List.length_map, hql, workBytes_eq]; omega
  have hpb : 2048 + (((sortD qs).map Nat.toUInt64).flatMap NativeRustcVm.wordBytes).length ≤
      workBytes := by
    rw [NativeRustcVm.length_wordsBytes, List.length_map, workBytes_eq]; omega
  refine ⟨by simp only [PcOk] at hpc1; exact hpc1, hb1, ⟨hmod, hql, hc0, hcnt, hqlt, h32, h64,
    hps0, hps256, hrl, hrw, FW.frame hst hs1 (by omega) (by omega) (.inr (by omega)) f56,
    FW.frame hst hs1 (by omega) (by omega) (.inr (by omega)) f48,
    FW.frame hst hs1 (by omega) (by omega) (.inr (by omega)) f40, ?_,
    keep_frame G hs1 (by omega) hqb hqW, keep_frame G hs1 (by omega) hpb hpW, ?_⟩,
    reader_fr G hs1 (by omega) hrd, by rw [r1 .X21 (by simp)]; exact x21,
    by rw [r1 .X26 (by simp)]; exact x26, ?_, ?_, ?_, ?_, ?_, ?_, hps0,
    fun j hj ↦ absurd hj (by simp)⟩
  · have := hm1.bytesAt_write (r := 0) (o := 32) (n := 8) (b := base m0 192) (sz := 192) rfl
      (by omega) (v := .reg .X24) (by decide)
    have hw := wordAt_reg this
    simp only [Sym.eval, Env.ofMachine_regs] at hw
    rwa [ofBitVec_eq x24] at hw
  · refine leaves_keep hlv (Match.sameOutside_in hm1 hwf (r0 := 0) (o := 32) (n := 8) rfl
      (by omega) (by decide)) (fun x hx ↦ ?_) fun i hi hq ↦ ?_
    · simp only [leavesOf, List.mem_map] at hx
      obtain ⟨r, hr, rfl⟩ := hx
      rw [length_paddedLeaf (hrw r hr)]; exact h64
    · rw [List.length_map, hrl] at hi
      exact G.not_chg (L := []) (o := 352512) (n := 131072) (by rw [workBytes_eq]) (by simp) i
        (by omega) (frame_chg hst (by omega) hq)
  · show (s1.data.regs.getXReg .X5).toBitVec.toNat = _
    rw [hm1.regs .X5 _ rfl]; show ((frEnv m0 st.data).load 0 56 8).toNat = _
    rw [e56, hlwN]
  · show (s1.data.regs.getXReg .X28).toBitVec.toNat = _
    rw [hm1.regs .X28 _ rfl]; simp only [Sym.eval]
    rw [e56, lsl3 (by rw [hlwN]; omega), hlwN]
  · rw [hm1.regs .X23 _ rfl]; simp only [Sym.eval, Env.ofMachine_regs]; rw [hb.x19, add_lit]
  · rw [hm1.regs .X25 _ rfl]; simp only [Sym.eval, Env.ofMachine_regs]; rw [hb.x19, add_lit]
  · show (s1.data.regs.getXReg .X27).toBitVec.toNat = _
    rw [hm1.regs .X27 _ rfl]; simp only [Sym.eval, Env.ofMachine_regs]
    exact x26
  · rw [hm1.regs .X29 _ rfl]; simp only [Sym.eval]; rw [e40]

/-- A frame word kept by a callee writing the frame's bytes 64 to 96. -/
theorem fw_hash (G : Geo m0 bp B) {m m' : MachineData} (hfr : Frm m0 m)
    (hs : SameOutside m.dmem m'.dmem fun q ↦ InRange (stackBelow m keccak256WordsStack)
      keccak256WordsStack q ∨ InRange (base m0 192 + BitVec.ofNat 64 64) 32 q ∨
        outs (rdr m0) (W m0) q) {o : Nat} {v : UInt64} (ho : o + 8 ≤ 64) (h : FW m0 m.dmem o v) :
    FW m0 m'.dmem o v :=
  FW.call G hfr (by unfold keccak256WordsStack keccakFStack; omega) hs (by omega) (.inl ho)
    (by omega) h

/-- **Leaf `i` hashed and its node stored.** -/
theorem hash_step (hp : Placed code k) (G : Geo m0 bp B)
    (hkw : Spec (Labels.label NativeRustcVmArm.Vm.Keccak256WordsOfHashWords.entryLabel) Keccak256WordsHashPre Keccak256WordsHashPost)
    {count : Nat} {qs : List Nat} {height lw : Nat} {rows : List (List K)} {c6 i : Nat}
    {st : MachineState} (h : HashSt m0 bp B c k count qs height lw rows c6 i st) :
    Eventually (step1 Host.exe) (fun st' ↦
      HashSt m0 bp B c k count qs height lw rows c6 (i + 1) st' ∨
      Climb0 m0 bp B c k count qs height lw rows c6 st') st := by
  obtain ⟨hpc, hb, hM, hrd, x21, x26, x5, x28, x23, x25, x27, x29, hi, hnd⟩ := h
  have hst := G.st
  have hW : workBytes = 483584 := workBytes_eq
  have hl := hM.rlen
  have hps := hM.ps256
  have hlw := hM.lw64
  set n := (sortD qs).length with hn
  -- `b27`: position `i`, the call
  have hon : 2048 + 8 * i + 8 ≤ workBytes := by omega
  have hwf := G.al_wf (o := 2048 + 8 * i) (n := 8) hon (by omega) hb.fr
  have hmA := G.al_match (o := 2048 + 8 * i) (n := 8) (a := .reg .X23) (k := 0) hb.fr (by
    simp only [Sym.eval, Env.ofMachine_regs]; rw [x23]; simp)
  refine exec_at (infix_of b27_in_code (by simp [b27]) hp) run_b27 hwf hpc hmA
    fun s1 hm1 hpc1 ↦ ?_
  have hd1 : s1.data.dmem = st.data.dmem := hm1.dmem_eq hwf rfl
  have hfr1 : Frm m0 s1.data := Fr.ofBlock hb.fr hmA hm1 hwf rfl rfl rfl
    fun x hx ↦ absurd hx (by simp)
  have r1 : ∀ r ∈ [XReg.X19, .X20, .X21, .X22, .X25, .X26, .X27, .X28, .X29],
      s1.data.regs.getXReg r = st.data.regs.getXReg r := regs_of hmA hm1 (by decide)
  have hb1 : Base m0 s1.data := hb.of_regs hfr1 fun r hr ↦ r1 r (by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
    rcases hr with rfl | rfl | rfl <;> simp)
  have hpi : i < n := hi
  have hpos : (sortD qs)[i] < 2 ^ 32 := sortD_lt hM.qlt _ (List.getElem_mem _)
  have x24 : (s1.data.regs.getXReg .X24).toBitVec = ((sortD qs)[i]).toUInt64.toBitVec := by
    rw [hm1.regs .X24 _ rfl]
    show (alEnv m0 st.data (wa m0 (2048 + 8 * i)) 8).load 1 0 8 = _
    apply load_word
    rw [Env.ofMachine_mem0, Env.base_ofMachine _ _ _ rfl, NativeRustcVm.addr_add_zero]
    have := NativeRustcVm.WordsAt.getElem hM.psW (i := i) (by simp; omega)
    simpa [wa, NativeRustcVm.addr_add_add] using this
  have hx0 : s1.data.regs.X0.toBitVec = base m0 192 + BitVec.ofNat 64 64 := by
    show (s1.data.regs.getXReg .X0).toBitVec = _
    rw [hm1.regs .X0 _ rfl]; simp [Sym.eval]
  have hx1 : s1.data.regs.X1.toNat = lw := by
    show (s1.data.regs.getXReg .X1).toBitVec.toNat = _
    rw [hm1.regs .X1 _ rfl]; exact x5
  have hx4 : s1.data.regs.X4.toNat = lw := by
    show (s1.data.regs.getXReg .X4).toBitVec.toNat = _
    rw [hm1.regs .X4 _ rfl]; exact x5
  have hx2 : s1.data.regs.X2.toNat = 8 * lw := by
    show (s1.data.regs.getXReg .X2).toBitVec.toNat = _
    rw [hm1.regs .X2 _ rfl]; exact x28
  have hx3 : s1.data.regs.X3.toBitVec = wa m0 (352512 + 512 * i) := by
    show (s1.data.regs.getXReg .X3).toBitVec = _
    rw [hm1.regs .X3 _ rfl]; exact x29
  have hNs : 192 + keccak256WordsStack ≤ 1184 := by unfold keccak256WordsStack keccakFStack; omega
  have hlo : 352512 + 512 * i + 8 * lw ≤ workBytes := by omega
  have hb0 := G.base_toNat (F := 192) (by omega)
  have hSP := m0.regs.SP.toNat_lt
  have hsp := G.sp
  have hpre : Keccak256WordsHashPre s1.data := by
    refine ⟨hfr1.stackOk hst (by decide) hNs, G.rcAt hfr1 hNs, by rw [hx1, hx4], by rw [hx2, hx4],
      ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [hx3, hx4]; exact (G.wa_ok hlo hfr1.kept).1
    · rw [hx3, hx4]; exact (G.wa_ok hlo hfr1.kept).2
    · rw [hx0]; intro j hj
      rw [NativeRustcVm.addr_add_add]
      exact Ring.frame_mapped hst (by omega) |> fun hmp ↦ hfr1.kept _ (hmp _ (by omega))
    · rw [hx0]; unfold NoWrap
      rw [NativeRustcVm.toNat_add_ofNat (by omega), hb0]; omega
    · intro _; rw [hx3, hx4]
      exact hfr1.apart hsp (G.wa_apart hlo (by omega) G.sW.symm) hNs
    · rw [hx0, Ring.stackBelow_eq hfr1.sp (by omega)]
      unfold NativeRustcArm.Apart
      rw [NativeRustcVm.toNat_add_ofNat (by omega), hb0, Ring.base_toNat (by omega)]
      unfold keccak256WordsStack keccakFStack; omega
    · rw [hx0]
      have hcs := G.cS
      unfold NativeRustcVm.Apart at hcs
      rw [G.base_toNat le_rfl] at hcs
      unfold NativeRustcArm.Apart
      rw [NativeRustcVm.toNat_add_ofNat (by omega), hb0]; omega
  simp only [PcOk] at hpc1
  have hQ : ∀ m', Keccak256WordsHashPost s1.data m' → SameOutside s1.data.dmem m'.dmem (fun q ↦
      InRange (stackBelow s1.data keccak256WordsStack) keccak256WordsStack q ∨
      InRange (base m0 192 + BitVec.ofNat 64 64) 32 q ∨ outs (rdr m0) (W m0) q) ∧
      Saved s1.data m' := by
    rintro m' ⟨-, hs, hsv⟩
    refine ⟨NativeRustcVm.SameOutside.mono hs fun q hq ↦ ?_, hsv⟩
    rcases hq with hq | hq
    · rw [hx0] at hq; exact .inr (.inl hq)
    · exact .inl hq
  refine Fr.leafIn (lo := 64) (n := 32) hfr1 hst.2.1 hNs (by omega) (by simp) (by decide)
    (fun q hq ↦ G.rgeo.not_frame (by omega) hq) hkw hpc1 hpre hQ fun m2 hfr2 hq2 hcs ↦ ?_
  have hs2 := (hQ m2 hq2).1
  obtain ⟨hpost, hsK, -⟩ := hq2
  have hli : i < (leavesOf lw rows).length := by simp; omega
  have hleaf := hM.lvW i hli
  have hll : ((leavesOf lw rows)[i]).length = lw := by
    simp only [leavesOf, List.getElem_map]
    exact length_paddedLeaf (hM.rw _ (List.getElem_mem _))
  have hdig := hpost (((leavesOf lw rows)[i]).map K.lane) (by rw [List.length_map, hll, hx4])
    (by rw [hx3, hd1]; simpa [wa, NativeRustcVm.addr_add_add] using hleaf)
  rw [hx0] at hdig
  have hb2 : Base m0 m2 := hb1.call hfr2 hcs
  -- what the call changed: the stack and the digest in the frame
  have hsC : SameOutside s1.data.dmem m2.dmem (Chg m0 []) :=
    NativeRustcVm.SameOutside.mono hsK fun q hq ↦ by
      rcases hq with hq | hq
      · rw [hx0] at hq; exact frame_chg hst (by omega) hq
      · exact .inl (stack_sub hst hfr1 hNs hq)
  have hM2 : Mid m0 B c count qs height lw rows c6 m2.dmem :=
    (hM.keep G (L := []) (by rw [← hd1]; exact hsC) (by simp)
      (fw_hash G hfr1 hs2 (by omega) (by rw [hd1]; exact hM.f56))
      (fw_hash G hfr1 hs2 (by omega) (by rw [hd1]; exact hM.f48))
      (fw_hash G hfr1 hs2 (by omega) (by rw [hd1]; exact hM.f40))
      (fw_hash G hfr1 hs2 (by omega) (by rw [hd1]; exact hM.f32)))
  have hrd2 : ReaderAt m2.dmem (rdr m0) bp B c6 :=
    G.rgeo.reader_frame rfl (by rw [hd1]; exact hrd) (NativeRustcVm.SameOutside.mono hsK
      fun q hq ↦ by
        rcases hq with hq | hq
        · rw [hx0] at hq; exact .inl (frame_sub hst (by omega) hq)
        · exact .inl (stack_sub hst hfr1 hNs hq))
  have hnd2 : NodesAt m2.dmem (wa m0 4096) ((nodes0 qs lw rows).take i) :=
    nodes_keep (by rw [hd1]; exact hnd) hsC fun j hj ↦ by
      rw [List.length_take] at hj
      have : j < 40 * i := by omega
      exact G.not_chg (L := []) (o := 4096) (n := 40 * i) (by omega) (by simp) j this
  -- `b28`: the node
  have hon3 : 4096 + 40 * i + 40 ≤ workBytes := by omega
  have hwf3 := G.al_wf (o := 4096 + 40 * i) (n := 40) hon3 (by omega) hb2.fr
  have x25' : (m2.regs.getXReg .X25).toBitVec = wa m0 (4104 + 40 * i) := by
    rw [hcs .X25 rfl, r1 .X25 (by simp)]; exact x25
  have hmB := G.al_match (o := 4096 + 40 * i) (n := 40) (a := .reg .X25) (k := 8) hb2.fr (by
    simp only [Sym.eval, Env.ofMachine_regs]
    rw [x25', show BitVec.ofInt 64 8 = BitVec.ofNat 64 8 from rfl, wa, wa,
      NativeRustcVm.addr_add_add]
    congr 2
    omega)
  refine exec_at (infix_of b28_in_code (by simp [b28]) hp) run_b28 hwf3 rfl hmB
    fun s3 hm3 hpc3 ↦ .done _ ?_
  have hfr3 : Frm m0 s3.data := Fr.ofBlockW hb2.fr hmB hm3 hwf3 rfl rfl
    (fun x hx ↦ absurd hx (by simp)) rfl (by omega) hst.2.1 (by decide) fun w hw ↦ by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
      right
      refine ⟨by rcases hw with rfl | rfl | rfl | rfl | rfl <;> decide, fun b sz hb ↦ ?_⟩
      have hb' : wa m0 (4096 + 40 * i) = b ∧ 40 = sz := by
        rcases hw with rfl | rfl | rfl | rfl | rfl <;>
          simpa only [Env.ofMachine_regions, List.getElem?_cons_succ, List.getElem?_cons_zero,
            Option.some.injEq, Prod.mk.injEq] using hb
      obtain ⟨rfl, rfl⟩ := hb'
      refine ⟨by rcases hw with rfl | rfl | rfl | rfl | rfl <;> decide, fun j hj ↦ .inr (.inr ?_)⟩
      exact NativeRustcVm.InRange.of_sub (o := 4096 + 40 * i) (m := 40) (by
        rw [← wa]; exact NativeRustcVm.inRange_add hj (by
          have := G.wa_toNat (o := 4096 + 40 * i) (by omega); have := G.wNw; omega)) G.wOk.2 hon3
  have hs3 := Match.sameOutside_in hm3 hwf3 (r0 := 1) (o := 0) (n := 40) rfl (by omega)
    (by decide)
  rw [NativeRustcVm.addr_add_zero] at hs3
  have hs3c : SameOutside m2.dmem s3.data.dmem (Chg m0 [(4096 + 40 * i, 40)]) :=
    NativeRustcVm.SameOutside.mono hs3 fun q hq ↦
      .inr (.inr (.inr ⟨_, List.mem_singleton_self _, hq⟩))
  have r3 : ∀ r ∈ [XReg.X19, .X20, .X21, .X22, .X23, .X26, .X28], s3.data.regs.getXReg r =
      m2.regs.getXReg r := regs_of hmB hm3 (by decide)
  have hb3 : Base m0 s3.data := hb2.of_regs hfr3 fun r hr ↦ r3 r (by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
    rcases hr with rfl | rfl | rfl <;> simp)
  have fw3 : ∀ {f : Nat} {v : UInt64}, f + 8 ≤ 192 → FW m0 m2.dmem f v → FW m0 s3.data.dmem f v :=
    fun hf h ↦ FW.wa G hon3 hs3 hf h
  have hM3 : Mid m0 B c count qs height lw rows c6 s3.data.dmem :=
    hM2.keep G hs3c (by simp; omega) (fw3 (by omega) hM2.f56) (fw3 (by omega) hM2.f48)
      (fw3 (by omega) hM2.f40) (fw3 (by omega) hM2.f32)
  have hrd3 : ReaderAt s3.data.dmem (rdr m0) bp B c6 :=
    G.rgeo.reader_frame rfl hrd2 (NativeRustcVm.SameOutside.mono hs3 fun q hq ↦
      .inr (.inr (NativeRustcVm.InRange.of_sub hq G.wOk.2 hon3)))
  -- the node
  have hdl : (NativeVm.Model.hashWords (((leavesOf lw rows)[i]).map K.lane).toArray).toList.length
      = 4 := by simp
  have hload : ∀ j (hj : j < 4), (alEnv m0 m2 (wa m0 (4096 + 40 * i)) 40).load 0 (64 + 8 * j) 8 =
      ((NativeVm.Model.hashWords (((leavesOf lw rows)[i]).map K.lane).toArray).toList[j]'(by
        rw [hdl]; exact hj)).toBitVec := by
    intro j hj
    apply load_word
    rw [Env.ofMachine_mem0, Env.base_ofMachine _ _ _ rfl]
    have := NativeRustcVm.WordsAt.getElem hdig (i := j) (by rw [hdl]; exact hj)
    rwa [NativeRustcVm.addr_add_add] at this
  have hw : ∀ (o : Nat) (v : Sym), o + 8 ≤ 40 → (∀ t < 8, findWrite 1 (o + t) (after b28
      (alS (.reg .X25) 40 8)).mem = some (v, t)) →
      WordAt s3.data.dmem (wa m0 (4096 + 40 * i) + BitVec.ofNat 64 o)
        (UInt64.ofBitVec (v.eval (alEnv m0 m2 (wa m0 (4096 + 40 * i)) 40))) := fun o v ho hf ↦ by
    rw [after_eq run_b28] at hf
    exact wordAt_reg (hm3.bytesAt_write (r := 1) (o := o) (n := 8) rfl ho hf)
  have hnode : NodeAt s3.data.dmem (wa m0 (4096 + 40 * i)) ((nodes0 qs lw rows)[i]'(by
      simp [hl]; omega)) := by
    rw [nodes0_get hl hi]
    refine ⟨by omega, ?_, ?_⟩
    · have := hw 0 (.reg .X24) (by omega) (by decide)
      rw [NativeRustcVm.addr_add_zero] at this
      simp only [Sym.eval, Env.ofMachine_regs] at this
      rw [hcs .X24 rfl, x24] at this
      exact this
    · refine NativeRustcVm.wordsAt_iff.mpr fun j hj ↦ ?_
      rw [NativeRustcVm.addr_add_add]
      have hj4 : j < 4 := by rw [hdl] at hj; exact hj
      match j, hj4 with
      | 0, h0 =>
        have := hw 8 (.load 0 64 8) (by omega) (by decide)
        simp only [Sym.eval] at this; rw [hload 0 h0] at this; exact this
      | 1, h0 =>
        have := hw 16 (.load 0 72 8) (by omega) (by decide)
        simp only [Sym.eval] at this; rw [hload 1 h0] at this; exact this
      | 2, h0 =>
        have := hw 24 (.load 0 80 8) (by omega) (by decide)
        simp only [Sym.eval] at this; rw [hload 2 h0] at this; exact this
      | 3, h0 =>
        have := hw 32 (.load 0 88 8) (by omega) (by decide)
        simp only [Sym.eval] at this; rw [hload 3 h0] at this; exact this
  have hlt : i < (nodes0 qs lw rows).length := by simp [hl]; omega
  have hnd3 : NodesAt s3.data.dmem (wa m0 4096) ((nodes0 qs lw rows).take (i + 1)) := by
    rw [List.take_add_one, List.getElem?_eq_getElem hlt, Option.toList_some]
    have hti : ((nodes0 qs lw rows).take i).length = i := by rw [List.length_take]; omega
    refine nodes_snoc hnd2 ?_ ?_ ?_
    · rw [hti, wa, NativeRustcVm.addr_add_add]; exact hnode
    · rw [hti, wa, NativeRustcVm.addr_add_add]; exact hs3
    · rw [hti]; unfold NoWrap; rw [G.wa_toNat (by omega)]; have := G.wNw; omega
  -- the registers
  have e27 : (m2.regs.getXReg .X27).toBitVec.toNat = n - i := by
    rw [hcs .X27 rfl, r1 .X27 (by simp)]; exact x27
  have hcond : (SBool.cmp .eq .W64 (.reg .X27) (.lit 1)).not.eval
      (alEnv m0 m2 (wa m0 (4096 + 40 * i)) 40) = !decide (i + 1 = n) := by
    simp only [SBool.eval, Sym.eval, Env.ofMachine_regs]
    rw [eq_lit _ 1 (by decide), e27]
    by_cases hh : i + 1 = n
    · rw [decide_eq_true (by omega), decide_eq_true hh]
    · rw [decide_eq_false (by omega), decide_eq_false hh]
  simp only [PcOk, hcond] at hpc3
  have ex5 : (s3.data.regs.getXReg .X5).toNat = lw := by
    show (s3.data.regs.getXReg .X5).toBitVec.toNat = _
    rw [hm3.regs .X5 _ rfl]
    show ((alEnv m0 m2 (wa m0 (4096 + 40 * i)) 40).load 0 56 8).toNat = _
    rw [load_word (by rw [Env.ofMachine_mem0, Env.base_ofMachine _ _ _ rfl]; exact hM2.f56),
      UInt64.toNat_toBitVec, toNat_toUInt64_of_lt (by omega)]
  have ex21 : (s3.data.regs.getXReg .X21).toNat = count := by
    rw [r3 .X21 (by simp), hcs .X21 rfl, r1 .X21 (by simp)]; exact x21
  have ex26 : (s3.data.regs.getXReg .X26).toNat = n := by
    rw [r3 .X26 (by simp), hcs .X26 rfl, r1 .X26 (by simp)]; exact x26
  by_cases hlast : i + 1 = n
  · simp only [hlast, decide_true, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hpc3
    refine .inr ⟨hpc3.trans (congrArg _ rfl), hb3, hM3, hrd3, ex21, ex26, ex5, ?_⟩
    rw [List.take_of_length_le (by simp [hl]; omega)] at hnd3
    exact hnd3
  · simp only [hlast, decide_false, Bool.not_false, ↓reduceIte] at hpc3
    refine .inl ⟨hpc3.trans (hp.label (j := NativeRustcVmArm.Vm.PhaseM.b27Offset) NativeRustcVmArm.Vm.PhaseM.label_20_at), hb3, hM3, hrd3, ex21, ex26, ex5, ?_, ?_, ?_,
      ?_, ?_, by omega, hnd3⟩
    · rw [r3 .X28 (by simp), hcs .X28 rfl, r1 .X28 (by simp)]; exact x28
    · rw [r3 .X23 (by simp), hcs .X23 rfl, hm1.regs .X23 _ rfl]
      simp only [Sym.eval, Env.ofMachine_regs]
      rw [x23, wa_add, show 2048 + 8 * i + 8 = 2048 + 8 * (i + 1) by omega]
    · rw [hm3.regs .X25 _ rfl]
      simp only [Sym.eval, Env.ofMachine_regs]
      rw [x25', wa_add, show 4104 + 40 * i + 40 = 4104 + 40 * (i + 1) by omega]
    · show (s3.data.regs.getXReg .X27).toBitVec.toNat = _
      rw [hm3.regs .X27 _ rfl]
      simp only [Sym.eval, Env.ofMachine_regs]
      rw [sub_lit (by rw [e27]; omega), e27]; omega
    · rw [hm3.regs .X29 _ rfl]
      simp only [Sym.eval, Env.ofMachine_regs]
      rw [hcs .X29 rfl, r1 .X29 (by simp), x29, wa_add,
        show 352512 + 512 * i + 512 = 352512 + 512 * (i + 1) by omega]

/-- **The leaves hashed.** -/
theorem hash_run (hp : Placed code k) (G : Geo m0 bp B)
    (hkw : Spec (Labels.label NativeRustcVmArm.Vm.Keccak256WordsOfHashWords.entryLabel) Keccak256WordsHashPre Keccak256WordsHashPost)
    {count : Nat} {qs : List Nat} {height lw : Nat} {rows : List (List K)} {c6 : Nat}
    {st : MachineState} (h : Rows m0 bp B c k count qs height lw rows c6 st) :
    Eventually (step1 Host.exe) (Climb0 m0 bp B c k count qs height lw rows c6) st :=
  Eventually.bind (hash_entry hp G h) fun _ h0 ↦
    Sym.loop (tr := step1 Host.exe)
      (fun n st ↦ ∃ i, n = (sortD qs).length - i ∧
        HashSt m0 bp B c k count qs height lw rows c6 i st)
      (fun _ _ ⟨i, hn, hi⟩ ↦ Eventually.mono (hash_step hp G hkw hi) fun _ h' ↦ by
        rcases h' with h' | h'
        · exact .inr ⟨_, by have := hi.ilt; omega, i + 1, rfl, h'⟩
        · exact .inl h')
      ⟨0, rfl, h0⟩

end

end NativeRustcVmArm.Wire.PhaseM
