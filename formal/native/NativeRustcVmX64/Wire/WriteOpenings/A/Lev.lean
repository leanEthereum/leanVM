module

public import NativeRustcVmX64.Wire.WriteOpenings.A.Defs
public import NativeRustcVmX64.Transcript.Arith
public import NativeRustcVmX64.Code.Vm.Find.Names

/-!
# `write_openings`' levels (`h > 0`, x86-64)

From the leaf copied (`LeafA`, `b14`): the frame words saved, the levels' loop at level `0`
(`leaf_step`). A level: its sibling count read (`b18`, more than `256` a rejection), `find` called for
the query's key (`b19`, `call_step`), its outcome checked (`b20`, `ret_step`), the found node's digest
loaded (`b16`) or zeros (`b21`): `DigA`. Then the digest stored (`dig_step`, `b17`): the next
level, or the opening written (`NextA`).
-/

namespace NativeRustcVmX64.Wire.WriteOpenings

open NativeRustcX64 hiding InRange SameOutside
open NativeRustcX64.Sym NativeRustcVm.Wire NativeVm.Wire
open NativeRustcVmX64.Vm.WriteOpenings
open NativeRustcVmX64.Transcript (Frame low8_replaceLow)
open NativeRustcVm (WordAt WordsAt wordOf InRange SameOutside)

public section

variable {R : Run} {j : Nat}

/-- Level `l`'s `n` node bytes from byte `o`. -/
theorem Geo.lvl_in (G : Geo R) {l o n : Nat} (hl : l < R.h) (hon : o + n ≤ 10240) (ho : o < 10240) :
    Inside (R.sb + BitVec.ofNat 64 (10240 * l + o)) n (R.big 5) := by
  have hnw := G.noWrap (i := 5) (by omega)
  rw [big5] at hnw ⊢
  unfold NativeRustcVm.NoWrap at hnw
  simp only [show nodesBytes = 10240 from rfl] at hnw ⊢
  have hh : 10240 * l + o + n ≤ 10240 * R.h := by
    have : 10240 * (l + 1) ≤ 10240 * R.h := Nat.mul_le_mul_left _ hl
    omega
  unfold Inside
  dsimp only
  rw [NativeRustcVm.toNat_add_ofNat (by omega)]
  omega

theorem findOut_of {m : MachineData} {ks : List UInt64} {k : UInt64}
    (h : match ks.findIdx? (· == k) with
      | some i => reg m .rax = 1 ∧ (reg m .rdx).toNat = i
      | none => reg m .rax = 0) : FindOut (ks.findIdx? (· == k)) m := h

theorem fidx_eq (l : Nat) (q : UInt64) : R.fidx l q = (R.keys l).findIdx? (· == skey q l) := by
  unfold Run.fidx; rfl

theorem cw_eq (l : Nat) : wordOf R.d0 (R.cnt + BitVec.ofNat 64 (8 * l)) = R.cw l := by
  unfold Run.cw; rfl

theorem keys_get (l n : Nat) (hn : n < (R.keys l).length) :
    (R.keys l)[n]'hn = wordOf R.d0 (R.sb + BitVec.ofNat 64 (10240 * l + 40 * n)) := by
  have e : R.keys l = (List.range (R.cw l).toNat).map fun n ↦ wordOf R.d0 (R.na l n) := by
    unfold Run.keys; rfl
  simp only [e, List.getElem_map, List.getElem_range]
  rfl

theorem keys_length (l : Nat) : (R.keys l).length = (R.cw l).toNat := by
  unfold Run.keys; rw [List.length_map, List.length_range]

/-- A word of an input region in a state of the run: the entry's. -/
theorem Geo.word_at (G : Geo R) {d : Mem 64} (hc : R.Chg d) (hk : Kept R.d0 d) {i : Nat}
    (hi : i < 7) (h0 : i ≠ 0) {a : BitVec 64} (ha : Inside a 8 (R.big i)) :
    WordAt d a (wordOf R.d0 a) := by
  rw [← G.rd hc hi h0 ha]
  exact wordAt_wordOf fun t ht ↦ hk _ (ha.mapped (G.ok i (by omega)) t ht)

/-- `b20`'s test: AL `1` and the index below the count. -/
theorem found_cond (x a : BitVec 64) (c : Bool) (ha : a = BitVec.ofNat 64 1 ∨ a = BitVec.ofNat 64 0) :
    CmpOp.apply .eq .W8
      (BinOp.apply .merge .W8 (BinOp.apply .merge .W8 x (if c then BitVec.ofNat 64 1 else
        BitVec.ofNat 64 0))
        (BinOp.apply .and .W8 (BinOp.apply .merge .W8 x (if c then BitVec.ofNat 64 1 else
          BitVec.ofNat 64 0)) a)) (BitVec.ofNat 64 1) =
      (c && a == BitVec.ofNat 64 1) := by
  rcases ha with rfl | rfl <;> cases c <;>
    simp only [CmpOp.apply, BinOp.apply, low8_replaceLow, low_ext, low_one, low_zero, Bool.false_eq_true,
      ↓reduceIte] <;> decide

/-- `b20`'s test, as the executor states it. -/
theorem found_eval [Labels] (env : Env) (c : SBool)
    (ha : env.regs .rax = BitVec.ofNat 64 1 ∨ env.regs .rax = BitVec.ofNat 64 0) :
    SBool.eval env (.cmp .eq .W8 (.bin .merge .W8 (.bin .merge .W8 (.reg .rcx)
      (.ite c (.lit 1) (.lit 0))) (.bin .and .W8 (.bin .merge .W8 (.reg .rcx)
        (.ite c (.lit 1) (.lit 0))) (.reg .rax))) (.lit 1)) =
      (c.eval env && env.regs .rax == BitVec.ofNat 64 1) :=
  found_cond (env.regs .rcx) (env.regs .rax) (c.eval env) ha

/-- `b18`'s test: more than `256`. -/
theorem gt256_cond (c : BitVec 64) :
    (!decide (c.toNat < (BitVec.ofNat 64 256).toNat) && !(c == BitVec.ofNat 64 256)) =
      decide (256 < c.toNat) := by
  rw [toNat_ofNat (by decide +kernel)]
  by_cases h1 : c.toNat < 256
  · rw [decide_eq_true h1, decide_eq_false (by omega)]
    rfl
  · by_cases h2 : c = BitVec.ofNat 64 256
    · subst h2
      decide
    · have h3 : 256 < c.toNat := by
        have : c.toNat ≠ 256 := fun h ↦ h2 (BitVec.eq_of_toNat_eq (by rw [h]; rfl))
        omega
      rw [decide_eq_false h1, decide_eq_true h3, beq_eq_false_iff_ne.mpr h2]
      rfl

/-- Four words from four. -/
theorem words4 {d : Mem 64} {a : BitVec 64} {w0 w1 w2 w3 : UInt64} (h0 : WordAt d a w0)
    (h1 : WordAt d (a + BitVec.ofNat 64 8) w1) (h2 : WordAt d (a + BitVec.ofNat 64 16) w2)
    (h3 : WordAt d (a + BitVec.ofNat 64 24) w3) : WordsAt d a [w0, w1, w2, w3] := by
  rw [NativeRustcVm.wordsAt_iff]
  intro i hi
  simp only [List.length_cons, List.length_nil] at hi
  rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3) with rfl | rfl | rfl | rfl
  · simpa using h0
  · exact h1
  · exact h2
  · exact h3

variable [Host]

/-- **The leaf copied** (`b14`): the frame words saved, the levels' loop at level `0`. -/
theorem leaf_step (hp : Placed code R.k) (G : Geo R) {i : Nat} {st : MachineState}
    (H : LeafA R j i st) : Eventually (step1 Host.exe) (LevA R j 0) st := by
  have K := H.k
  have hwf := G.wf0 K.F.fr.kept (ret := 0)
  refine blk hp b14_in_code (by simp [b14]) run_b14 K.F H.pc hwf (frMatch K.F.fr) nofun (o := 8)
    (by decide +kernel) (by decide +kernel) fun s1 F1 hm1 hpc1 hs1 ↦ ?_
  have hW : ∀ p, InRange R.out phaseBytes p → ¬InRange R.fb 160 p := G.frame_out
  have hk1 := fwK_of hwf hm1 (o' := 8) (by decide +kernel) (os := (wB R j).map Prod.fst)
    (by kdecA) (by kdecA)
  have hfw : FWs R s1.data.dmem (wC R j) := by
    refine FWs.append (K.w.keep hk1) (FWs.cons ?_ (FWs.cons ?_ (FWs.cons ?_ (FWs.nil _))))
    · exact fw_write hm1 (o := 24) (by omega) (v := .reg .r11) (by decide +kernel) |>.congr
        (by rw [show (Sym.reg .r11).eval _ = reg st.data .r11 from rfl,
          K.rg.get (v := R.lv) (by simp)])
    · exact fw_write hm1 (o := 48) (by omega) (v := .reg .r13) (by decide +kernel) |>.congr
        (by rw [show (Sym.reg .r13).eval _ = reg st.data .r13 from rfl,
          K.rg.get (v := BitVec.ofNat 64 (R.lw % 4)) (by simp)])
    · exact fw_write hm1 (o := 72) (by omega) (v := .reg .rdx) (by decide +kernel) |>.congr
        (by rw [show (Sym.reg .rdx).eval _ = reg st.data .rdx from rfl,
          K.rg.get (v := R.pa) (by simp)])
  refine .done _ ⟨(pc_jump hpc1).trans (hp.label NativeRustcVmX64.Vm.WriteOpenings.label_15_at), F1, K.lt, K.h0,
    G.begun_keepW hs1 hW K.lt K.mem, ⟨i, K.pos, G.leaf_keepW hs1 hW K.lt (le_refl _) H.leaf⟩,
    path_zero, hfw, by keep_regs hm1 K.rg, ?_, hm1.regs .r13 _ rfl, ?_⟩
  · refine (hm1.regs .rbp _ rfl).trans ?_
    show reg st.data .rbx = _
    rw [K.rg.get (v := R.sb) (by simp), Nat.mul_zero, NativeRustcVm.addr_add_zero]
  · refine (hm1.regs .r14 _ rfl).trans ?_
    show (envOf R st.data [] 0).load 0 16 8 = _
    rw [fw_load (K.w.get (v := R.oa (ob j + 544)) (by simp)), Nat.mul_zero, Nat.add_zero]



/-- **A level's count** (`b18`): a rejection, or at most `256`. -/
theorem cnt_step (hp : Placed code R.k) (G : Geo R) {l : Nat} {st : MachineState}
    (H : LevA R j l st) :
    Eventually (step1 Host.exe) (fun st' ↦ Post R st' ∨ CntA R j l st') st := by
  have S := H.s
  have hl := S.llt
  have hh := G.h32
  have hj := S.lt
  -- `b18`: the count.
  have hin2 : Inside (R.cnt + BitVec.ofNat 64 (8 * l)) 8 (R.big 6) :=
    inside_off (A := R.big 6) (G.noWrap (by omega)) (by show 8 * l + 8 ≤ 8 * R.h; omega)
      (by omega)
  have hwf := G.wf1 S.F.fr.kept (i := 6) (by omega) (by omega) hin2 (ret := 0)
  have hc0 := G.arg_load S.F.chg (m := st.data) (cs := [(R.cnt + BitVec.ofNat 64 (8 * l), 8)])
    (ret := 0) (i := 2) (by omega)
  have hm : Match (envOf R st.data [(R.cnt + BitVec.ofNat 64 (8 * l), 8)] 0) kS st.data :=
    match_fS S.F.fr (csz := [8]) (cs := [(R.cnt + BitVec.ofNat 64 (8 * l), 8)]) ⟨rfl, trivial⟩
      ⟨al0 (by
        show BinOp.apply .add .W64 ((envOf R st.data _ 0).load 1 (8 * 2) 8)
          (BinOp.apply .mul .W64 (reg st.data .r13) (BitVec.ofNat 64 8)) = _
        rw [hc0, add_eval, mul_eval, S.r13, ofNat_mul, Nat.mul_comm]
        rfl), trivial⟩
  refine blk hp b18_in_code (by simp [b18]) run_b18 S.F H.pc hwf hm nofun (o := 8) (by decide +kernel)
    (by decide +kernel) fun s1 F1 hm1 hpc1 _ ↦ ?_
  have hd1 : s1.data.dmem = st.data.dmem := hm1.dmem_eq hwf rfl
  have hcw : (envOf R st.data [(R.cnt + BitVec.ofNat 64 (8 * l), 8)] 0).load 2 0 8 =
      (R.cw l).toBitVec := by
    rw [load_eq_wordOf]
    show (wordOf st.data.dmem (R.cnt + BitVec.ofNat 64 (8 * l) + BitVec.ofNat 64 0)).toBitVec = _
    rw [NativeRustcVm.addr_add_zero, G.rd S.F.chg (i := 6) (by omega) (by omega) hin2, cw_eq]
  have hrbx1 : reg s1.data .rbx = (R.cw l).toBitVec := (hm1.regs .rbx _ rfl).trans hcw
  have hpc1' := pc_cond hpc1 (b := decide (256 < (R.cw l).toNat)) (by
    simp only [SBool.eval, Sym.eval, ult_eval, eq_eval]
    rw [hcw]
    exact gt256_cond _)
  have hk1 : Regs s1.data (lA R j) := S.rg.keep hm1 (by kdecA)
  by_cases hbad : 256 < (R.cw l).toNat
  · rw [decide_eq_true hbad, hp.label NativeRustcVmX64.Vm.WriteOpenings.label_45_at] at hpc1'
    simp only [↓reduceIte] at hpc1'
    exact Eventually.mono (fail_spec hp G hpc1' F1 (.inr ⟨l, hl, hbad⟩)) fun _ h ↦ .inl h
  rw [decide_eq_false hbad] at hpc1'
  simp only [Bool.false_eq_true, ↓reduceIte] at hpc1'
  exact .done _ (.inr ⟨hpc1'.trans (congrArg Host.addrOf rfl), ⟨F1, S.lt, S.llt, hd1 ▸ S.mem,
    hd1 ▸ S.leaf, hd1 ▸ S.path, S.w.keep (FwK.of_eq hd1 _), hk1, kreg hm1 rfl S.rbp,
    kreg hm1 rfl S.r13, kreg hm1 rfl S.r14⟩, hrbx1, by omega⟩)



/-- **A level's call** (`b19`, `find`): back from `find`. -/
theorem call_step (hp : Placed code R.k) (G : Geo R)
    (hfind : Spec (Labels.label NativeRustcVmX64.Vm.Find.entryLabel) FindPre FindPost) {l : Nat} {st : MachineState}
    (H : CntA R j l st) : Eventually (step1 Host.exe) (RetA R j l) st := by
  have S := H.s
  have hl := S.llt
  have hh := G.h32
  have hj := S.lt
  have F1 := S.F
  have hk1 := S.rg
  have hrbx1 := H.rbx
  have hc := H.cw256
  -- `b19`: the call.
  have hwf2 := G.wf0 F1.fr.kept (ret := (Host.addrOf (R.k + NativeRustcVmX64.Vm.WriteOpenings.b19Offset + b19.length)).toBitVec)
  refine blk hp b19_in_code (by simp [b19]) run_b19 F1 H.pc
    hwf2 (frMatch F1.fr) (fun _ _ ↦ rfl) (o := 0) (by decide +kernel) (by decide +kernel)
    fun s2 F2 hm2 hpc2 hs2 ↦ ?_
  have hs2' : SameOutside st.data.dmem s2.data.dmem (InRange R.fb 160) := hs2
  have hk2 : FwK R st.data.dmem s2.data.dmem ((wC R j).map Prod.fst) :=
    fwK_of hwf2 hm2 (o' := 0) (by decide +kernel) (by kdecA) (by kdecA)
  have hrdi : reg s2.data .rdi = R.sb + BitVec.ofNat 64 (10240 * l) :=
    (hm2.regs .rdi _ rfl).trans S.rbp
  have hrsi : reg s2.data .rsi = (R.cw l).toBitVec := (hm2.regs .rsi _ rfl).trans hrbx1
  have hrdx : reg s2.data .rdx = (R.qw j).toBitVec >>> l := by
    refine (hm2.regs .rdx _ rfl).trans ?_
    show BinOp.apply .shr .W64 (reg st.data .r15) (UnOp.apply .trunc .W32 (reg st.data .r13)) = _
    rw [hk1.get (v := (R.qw j).toBitVec) (by simp), S.r13, shr_trunc (by omega)]
  have hsp2 : rspOf s2.data = R.fb := by
    have := F2.fr.sp
    rwa [NativeRustcVm.Transcript.off, NativeRustcVm.addr_add_zero] at this
  have hlv : Inside (R.sb + BitVec.ofNat 64 (10240 * l)) (40 * (R.cw l).toNat) (R.big 5) := by
    have := G.lvl_in hl (o := 0) (n := 40 * (R.cw l).toNat) (by omega) (by omega)
    rwa [Nat.add_zero] at this
  have hP : FindPre s2.data := by
    refine ⟨NativeRustcVmX64.Transcript.stackOk_callee G.st F2.fr.kept hsp2 (by
      show 160 + 0 ≤ 160; omega), ?_, ?_⟩
    · rw [hrdi, hrsi]
      exact fun t ht ↦ F2.fr.kept _ (hlv.mapped (G.ok 5 (by omega)) t ht)
    · rw [hrdi, hrsi]
      exact hlv.noWrap (G.noWrap (by omega))
  refine call_then hpc2 hfind hP fun s3 hpc3 hrsp3 hpost ↦ ?_
  obtain ⟨hres, hd3, hsv⟩ := hpost
  have F3 : Fr R 8 s3.data := ⟨NativeRustcVmX64.Transcript.Frame.call F2.fr hsv hrsp3
    (R := fun _ ↦ False) (fun _ _ ↦ by rw [hd3]) (fun _ h ↦ h.elim)
    (G.fbNw) slots_le, F2.chg.of_eq hd3⟩
  have hkl : (R.keys l).length = (R.cw l).toNat := keys_length l
  have hks : ∀ n (hn : n < (R.keys l).length), WordAt s2.data.dmem
      (NativeRustcVm.Transcript.off (reg s2.data .rdi) (40 * n)) ((R.keys l)[n]'hn) := by
    intro n hn
    have hn' : n < (R.cw l).toNat := lt_of_lt_of_eq hn hkl
    have e := keys_get l n hn
    rw [e, hrdi, NativeRustcVm.Transcript.off, NativeRustcVm.addr_add_add]
    exact G.word_at F2.chg F2.fr.kept (i := 5) (by omega) (by omega)
      (G.lvl_in hl (o := 40 * n) (n := 8) (by omega) (by omega))
  have hres' := hres (R.keys l) (by rw [hkl, hrsi]; rfl) hks
  rw [hrdx, show UInt64.ofBitVec ((R.qw j).toBitVec >>> l) = skey (R.qw j) l from rfl] at hres'
  have hfo : FindOut (R.fidx l (R.qw j)) s3.data := by
    rw [fidx_eq]
    exact findOut_of hres'
  have hkeep3 : ∀ x, calleeSaved x = true → reg s3.data x = reg s2.data x := fun x hx ↦ hsv.1 x hx
  have hrbx3 : reg s3.data .rbx = (R.cw l).toBitVec :=
    (hkeep3 .rbx rfl).trans ((kreg hm2 rfl hrbx1))
  have hS3 : ∀ x ∈ [Reg64.rbp, .r12, .r13, .r14, .r15], reg s3.data x = reg st.data x := by
    intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl <;>
      exact (hkeep3 _ rfl).trans (kreg hm2 rfl rfl)
  have hW : ∀ p, InRange R.out phaseBytes p → ¬InRange R.fb 160 p := G.frame_out
  have hs3 : SameOutside st.data.dmem s3.data.dmem (InRange R.fb 160) := fun q hq ↦ by
    rw [hd3]; exact hs2' q hq
  refine .done _ ⟨hpc3.trans (congrArg Host.addrOf rfl), ⟨F3, S.lt, S.llt,
    G.begun_keepW hs3 hW hj S.mem,
    (S.leaf.imp fun _ h ↦ ⟨h.1, G.leaf_keepW hs3 hW hj (le_refl _) h.2⟩),
    G.path_keepW hs3 hW hj (by omega) S.path, S.w.keep (hk2.trans (FwK.of_eq hd3 _)),
    Regs.cons ((hS3 .r12 (by simp)).trans (S.rg.get (by simp)))
      (Regs.cons ((hS3 .r15 (by simp)).trans (S.rg.get (by simp))) (Regs.nil _)),
    (hS3 .rbp (by simp)).trans S.rbp, (hS3 .r13 (by simp)).trans S.r13,
    (hS3 .r14 (by simp)).trans S.r14⟩, hrbx3, H.cw256, hfo⟩



/-- **A level's digest** (`b20`, then `b16` or `b21`): the found node's digest, or zeros. -/
theorem ret_step (hp : Placed code R.k) (G : Geo R) {l : Nat} {st : MachineState}
    (H : RetA R j l st) : Eventually (step1 Host.exe) (DigA R j l) st := by
  have S := H.s
  have hl := S.llt
  have hh := G.h32
  have hj := S.lt
  have hres' := H.res
  have hrbx3 := H.rbx
  -- `b20`: the test.
  have hwf4 := G.wf0 S.F.fr.kept (ret := 0)
  refine blk hp b20_in_code (by simp [b20]) run_b20 S.F H.pc
    hwf4 (frMatch S.F.fr) nofun (o := 8) (by decide +kernel) (by decide +kernel) fun s4 F4 hm4 hpc4 _ ↦ ?_
  have hd4 : s4.data.dmem = st.data.dmem := hm4.dmem_eq hwf4 rfl
  have hS4 : ∀ x ∈ [Reg64.rbp, .r12, .r13, .r14, .r15], reg s4.data x = reg st.data x := by
    intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl <;> exact kreg hm4 rfl rfl
  have S4 : ∀ s : MachineState, Fr R 8 s.data → s.data.dmem = st.data.dmem →
      (∀ x ∈ [Reg64.rbp, .r12, .r13, .r14, .r15], reg s.data x = reg st.data x) →
      LevS R j l s.data := fun s F hd hS ↦
    ⟨F, S.lt, S.llt, hd ▸ S.mem, hd ▸ S.leaf, hd ▸ S.path, S.w.keep (FwK.of_eq hd _),
      Regs.cons ((hS .r12 (by simp)).trans (S.rg.get (by simp)))
        (Regs.cons ((hS .r15 (by simp)).trans (S.rg.get (by simp))) (Regs.nil _)),
      (hS .rbp (by simp)).trans S.rbp, (hS .r13 (by simp)).trans S.r13,
      (hS .r14 (by simp)).trans S.r14⟩
  cases hf : R.fidx l (R.qw j) with
  | none =>
    rw [hf] at hres'
    unfold FindOut at hres'
    have hpc4' := pc_cond hpc4 (b := false) (by
      rw [found_eval _ _ (.inr hres'), envRegs, hres']
      cases SBool.eval _ _ <;> rfl)
    simp only [Bool.false_eq_true, ↓reduceIte] at hpc4'
    -- `b21`: zeros.
    have hwf5 := G.wf0 F4.fr.kept (ret := 0)
    refine blk hp b21_in_code (by simp [b21]) run_b21 F4 (hpc4'.trans (congrArg Host.addrOf rfl))
      hwf5 (frMatch F4.fr) nofun (o := 8) (by decide +kernel) (by decide +kernel) fun s5 F5 hm5 hpc5 _ ↦ ?_
    have hd5 : s5.data.dmem = st.data.dmem := (hm5.dmem_eq hwf5 rfl).trans hd4
    refine .done _ ⟨(pc_jump hpc5).trans (hp.label NativeRustcVmX64.Vm.WriteOpenings.label_14_at),
      S4 s5 F5 hd5 fun x hx ↦ by
        rw [← hS4 x hx]
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
        rcases hx with rfl | rfl | rfl | rfl | rfl <;> exact kreg hm5 rfl rfl, ?_⟩
    simp only [NativeRustcX64.reg]
    rw [hm5.regs .rsi _ rfl, hm5.regs .rdx _ rfl, hm5.regs .rcx _ rfl, hm5.regs .rax _ rfl]
    unfold Run.digest
    rw [hf]
    rfl
  | some n =>
    rw [hf] at hres'
    unfold FindOut at hres'
    obtain ⟨hax, hdx⟩ := hres'
    have hn : n < (R.cw l).toNat := by
      have hf' := hf
      unfold Run.fidx at hf'
      have := (List.findIdx?_eq_some_iff_getElem.mp hf').1
      rw [keys_length] at this
      exact this
    have hc := H.cw256
    have hrdx3 : reg st.data .rdx = BitVec.ofNat 64 n := by
      rw [← hdx]; exact (ofNat_toNat' _).symm
    have hpc4' := pc_cond hpc4 (b := true) (by
      rw [found_eval _ _ (.inl hax), envRegs, hax]
      simp only [SBool.eval, Sym.eval, ult_eval, envRegs]
      rw [hrdx3, hrbx3, toNat_ofNat (by omega),
        decide_eq_true (show n < (R.cw l).toBitVec.toNat from hn)]
      rfl)
    simp only [↓reduceIte] at hpc4'
    rw [hp.label NativeRustcVmX64.Vm.WriteOpenings.label_13_at] at hpc4'
    -- `b16`: the node's digest.
    have hrbp4 : reg s4.data .rbp = R.sb + BitVec.ofNat 64 (10240 * l) :=
      (hS4 .rbp (by simp)).trans S.rbp
    have hrdx4 : reg s4.data .rdx = BitVec.ofNat 64 n := kreg hm4 rfl hrdx3
    have hin5 : Inside (R.na l n) 40 (R.big 5) := by
      rw [Run.na]; exact G.lvl_in hl (o := 40 * n) (n := 40) (by omega) (by omega)
    have hwf5 := G.wf1 F4.fr.kept (i := 5) (by omega) (by omega) hin5 (ret := 0)
    have hm5 : Match (envOf R s4.data [(R.na l n, 40)] 0) nS s4.data :=
      match_fS F4.fr (csz := [40]) (cs := [(R.na l n, 40)]) ⟨rfl, trivial⟩
        ⟨al0 (by
          show BinOp.apply .add .W64 (reg s4.data .rbp) (BinOp.apply .mul .W64
            (BinOp.apply .add .W64 (reg s4.data .rdx) (BinOp.apply .mul .W64 (reg s4.data .rdx)
              (BitVec.ofNat 64 4))) (BitVec.ofNat 64 8)) = R.na l n
          rw [hrbp4, hrdx4, add_eval, add_eval, mul_eval, mul_eval, ofNat_mul, ofNat_add,
            ofNat_mul]
          show _ = R.sb + BitVec.ofNat 64 (10240 * l + 40 * n)
          exact addr_add (by omega)), trivial⟩
    refine blk hp b16_in_code (by simp [b16]) run_b16 F4 hpc4' hwf5 hm5 nofun (o := 8)
      (by decide +kernel) (by decide +kernel) fun s5 F5 hm6 hpc5 _ ↦ ?_
    have hd5 : s5.data.dmem = st.data.dmem := (hm6.dmem_eq hwf5 rfl).trans hd4
    have hload : ∀ u, u < 4 → (envOf R s4.data [(R.na l n, 40)] 0).load 2 (8 + 8 * u) 8 =
        (wordOf R.d0 (R.na l n + BitVec.ofNat 64 (8 + 8 * u))).toBitVec := by
      intro u hu
      rw [G.in_load F4.chg (cs := [(R.na l n, 40)]) (r := 2) rfl (by omega) (i := 5) (by omega)
        (by omega) (by
          unfold Run.na
          rw [NativeRustcVm.addr_add_add, show 10240 * l + 40 * n + (8 + 8 * u) =
            10240 * l + (40 * n + 8 + 8 * u) by omega]
          exact G.lvl_in hl (by omega) (by omega))]
    refine .done _ ⟨(pc_fall hpc5).trans (congrArg Host.addrOf rfl),
      S4 s5 F5 hd5 fun x hx ↦ by
        rw [← hS4 x hx]
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
        rcases hx with rfl | rfl | rfl | rfl | rfl <;> exact kreg hm6 rfl rfl, ?_⟩
    simp only [NativeRustcX64.reg]
    rw [hm6.regs .rsi _ rfl, hm6.regs .rdx _ rfl, hm6.regs .rcx _ rfl, hm6.regs .rax _ rfl]
    unfold Run.digest
    rw [hf]
    simp only [Sym.eval]
    rw [hload 0 (by omega), hload 1 (by omega), hload 2 (by omega), hload 3 (by omega)]
    rfl

/-- **A level's digest stored** (`b17`): the next level, or the opening written. -/
theorem dig_step (hp : Placed code R.k) (G : Geo R) {l : Nat} {st : MachineState}
    (H : DigA R j l st) :
    Eventually (step1 Host.exe) (fun st' ↦ LevA R j (l + 1) st' ∨ NextA R j st') st := by
  have S := H.s
  have hl := S.llt
  have hh := G.h32
  have hj := S.lt
  have hnq := G.nq256
  have hob := ob_le (j := j) (by omega)
  have hob' : 24 + 1544 * j + 1544 ≤ phaseBytes := hob
  have hin2 : Inside (R.oa (ob j + 520 + 32 * l)) 32 (R.big 7) := G.o_in (by omega) (by omega)
  have hwf := G.wf1 S.F.fr.kept (i := 7) (by omega) (by omega) hin2 (ret := 0)
  have hm : Match (envOf R st.data [(R.oa (ob j + 520 + 32 * l), 32)] 0) dS st.data :=
    match_fS S.F.fr (csz := [32]) (cs := [(R.oa (ob j + 520 + 32 * l), 32)]) ⟨rfl, trivial⟩
      ⟨alN (o := 24) (by
        show reg st.data .r14 = R.oa (ob j + 520 + 32 * l) + BitVec.ofNat 64 24
        rw [S.r14, oa_add]
        congr 1
        omega), trivial⟩
  refine blkW G hp b17_in_code (by simp [b17]) run_b17 S.F H.pc hwf hm nofun (o := 8)
    (by decide +kernel) (ro := 2) rfl (lo := 0) (a := R.oa (ob j + 520 + 32 * l)) (n := 32)
    (NativeRustcVm.addr_add_zero _) hin2 (by decide +kernel) fun s1 F1 hm1 hpc1 hs1 ↦ ?_
  have hdg : WordsAt s1.data.dmem (R.oa (ob j + 520 + 32 * l)) (R.digest l (R.qw j)) := by
    rw [← H.dg]
    refine words4 ?_ ?_ ?_ ?_
    · have := stored_reg hm1 (r := 2) (o := 0) (sz := 32) rfl (by omega) (x := .rsi) (by decide +kernel)
        (w := UInt64.ofBitVec (reg st.data .rsi)) rfl
      rwa [NativeRustcVm.addr_add_zero] at this
    · exact stored_reg hm1 (r := 2) (o := 8) (sz := 32) rfl (by omega) (x := .rdx) (by decide +kernel)
        (w := UInt64.ofBitVec (reg st.data .rdx)) rfl
    · exact stored_reg hm1 (r := 2) (o := 16) (sz := 32) rfl (by omega) (x := .rcx) (by decide +kernel)
        (w := UInt64.ofBitVec (reg st.data .rcx)) rfl
    · exact stored_reg hm1 (r := 2) (o := 24) (sz := 32) rfl (by omega) (x := .rax) (by decide +kernel)
        (w := UInt64.ofBitVec (reg st.data .rax)) rfl
  obtain ⟨i, hpos, hleaf⟩ := S.leaf
  have hlw := G.lw64
  have hpath : R.PathPart s1.data.dmem j (l + 1) :=
    path_succ (G.path_keep hs1 (by omega) hj S.path (by omega)) hdg
  have hmem := G.begun_keep hs1 (by omega) hj S.mem (by omega)
  have hleaf1 := G.leaf_keep hs1 (by omega) hj hleaf (by omega)
  have hw1 : FWs R s1.data.dmem (wC R j) := S.w.keep
    (fwK_of hwf hm1 (o' := 8) (by decide +kernel) (os := (wC R j).map Prod.fst) (by kdecA) (by kdecA))
  have hrg1 : Regs s1.data (lA R j) := S.rg.keep hm1 (by kdecA)
  have hpc1' := pc_cond hpc1 (b := decide (R.h = l + 1)) (by
    simp only [SBool.eval, Sym.eval, eq_eval, add_eval, envRegs]
    rw [show (envOf R st.data [(R.oa (ob j + 520 + 32 * l), 32)] 0).load 1 0 8 = stackArg R.m0 0
      from G.arg_load S.F.chg (i := 0) (by omega), S.r13, ofNat_add, ← ofNat_toNat' (stackArg R.m0 0),
      beq_ofNat (by omega) (by omega), beq_decide])
  by_cases hlast : R.h = l + 1
  · rw [decide_eq_true hlast, hp.label NativeRustcVmX64.Vm.WriteOpenings.label_18_at] at hpc1'
    simp only [↓reduceIte] at hpc1'
    refine .done _ (.inr ⟨hpc1', F1, hj, by omega, ⟨hmem.1.1, fun j' hj' ↦ ?_⟩, hw1,
      hrg1.get (by simp)⟩)
    rcases Nat.lt_succ_iff_lt_or_eq.mp hj' with h | rfl
    · exact hmem.1.2 j' h
    · exact ⟨i, hpos, hmem.2, hleaf1, hlast ▸ hpath⟩
  rw [decide_eq_false hlast] at hpc1'
  simp only [Bool.false_eq_true, ↓reduceIte] at hpc1'
  refine .done _ (.inl ⟨hpc1'.trans (congrArg Host.addrOf rfl), ⟨F1, hj, by omega, hmem,
    ⟨i, hpos, hleaf1⟩, hpath, hw1, hrg1, ?_, ?_, ?_⟩⟩)
  · refine (hm1.regs .rbp _ rfl).trans ?_
    simp only [Sym.eval, add_eval, envRegs]
    rw [S.rbp]
    exact lit_add (by omega)
  · refine (hm1.regs .r13 _ rfl).trans ?_
    simp only [Sym.eval, add_eval, envRegs]
    rw [S.r13, ofNat_add]
  · refine (hm1.regs .r14 _ rfl).trans ?_
    simp only [Sym.eval, add_eval, envRegs]
    rw [S.r14]
    exact lit_add (by omega)

end

end NativeRustcVmX64.Wire.WriteOpenings
