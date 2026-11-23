module

public import NativeRustcVmArm.Code.Vm.EWMul.Names
public import NativeRustcVmArm.Code.Vm.Memcpy.Names
public import NativeRustcVmArm.KeccakGkr.KeccakOpen.FoldCopy
public import NativeRustcVmArm.KeccakGkr.KeccakOpen.FoldInner

/-!
# `keccak_open`'s fold: a row

Row `i` of round `t`: rows `2 i`, `2 i + 1` copied into the two buffers (`copyRow`), the counter
zeroed (`zeroBlock`), the inner loop. An entry folded is the model's (`F_succ_fun`). The rows of
an unrolled round (`rowD`); the head of a looped round's row (`rowHead`).
-/

namespace NativeRustcVmArm.KeccakGkr.KeccakOpen

open NativeRustcArm NativeRustcArm.Sym NativeVm.Model NativeRustcVmArm.Arrays
open NativeRustcVmArm.Vm.KeccakOpen

public section

theorem half_le (t : Nat) : half t ≤ 32 := Nat.div_le_self _ _

/-- **An entry folded**, as the inner loop's step needs it. -/
theorem F_succ_fun {sl : Array EW} {rows : Array (Array EW)} (hsz : rows.size = 64)
    (hrow : ∀ r < 64, (rows.getD r #[]).size = 64) {t i j : Nat} (ht : t < sl.size)
    (hi : i < half t) (hj : j < 64) :
    F sl rows t i (j + 1) = fun n ↦ if n = 64 * i + j then
      foldE (sl.getD t 0) (fun z ↦ F sl rows t i 0 (64 * (2 * i) + z))
        (fun z ↦ F sl rows t i 0 (64 * (2 * i + 1) + z)) j else F sl rows t i j n := by
  funext n
  rw [F_step hj n, W_succ hsz hrow ht hi hj]
  have h0 := F_pair hsz hrow ht hi (b := 0) (by decide) hj
  simp only [Nat.add_zero] at h0
  unfold foldE
  dsimp only
  rw [h0, F_pair hsz hrow ht hi (b := 1) (by decide) hj]

end

@[expose] public section

/-- A value with no variable, register, flag or memory in it. -/
def varFree : Sym → Bool
  | .lit _ | .ptr _ _ => true
  | .bin _ _ a b => varFree a && varFree b
  | .un _ _ a => varFree a
  | _ => false

/-- `(r, v)` is one of `ks`, as a check. -/
def inK (r : XReg) (v : Sym) (ks : List (XReg × Sym)) : Bool :=
  ks.any fun p ↦ p.1 == r && decide (p.2 = v)

end

public section

theorem memK {ks : List (XReg × Sym)} {r : XReg} {v : Sym} (h : inK r v ks = true) :
    (r, v) ∈ ks := by
  obtain ⟨p, hp, he⟩ := List.any_eq_true.mp h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at he
  rw [← XReg.eq_of_beq he.1, ← he.2]
  exact hp

theorem eval_varFree [Labels] : ∀ (v : Sym), varFree v = true → ∀ {e e' : Env},
    e.regions = e'.regions → v.eval e = v.eval e'
  | .lit _, _, _, _, _ => rfl
  | .ptr r o, _, e, e', hr => by simp only [Sym.eval, Env.base, hr]
  | .bin op w a b, h, e, e', hr => by
    simp only [varFree, Bool.and_eq_true] at h
    simp only [Sym.eval]
    rw [eval_varFree a h.1 hr, eval_varFree b h.2 hr]
  | .un op w a, h, e, e', hr => by
    simp only [varFree] at h
    simp only [Sym.eval]
    rw [eval_varFree a h hr]
  | .var _, h, _, _, _ => nomatch h
  | .reg _, h, _, _, _ => nomatch h
  | .sp, h, _, _, _ => nomatch h
  | .label _, h, _, _, _ => nomatch h
  | .load _ _ _, h, _, _, _ => nomatch h
  | .loadx _ _ _ _, h, _, _, _ => nomatch h
  | .ite _ _ _, h, _, _, _ => nomatch h

/-- **Known registers without variables** are known whatever the variables. -/
theorem KAt.revar [Labels] {m0 st : MachineData} {vars vars' : Nat → BitVec 64}
    {ks : List (XReg × Sym)} (hk : KAt m0 vars ks st)
    (h : ks.all (fun p ↦ varFree p.2) = true) : KAt m0 vars' ks st :=
  KAt.of_reg hk.1 fun p hp ↦ (hk.reg hp).trans
    (eval_varFree p.2 (List.all_eq_true.mp h p hp) rfl)

/-- A row's address in the rows. -/
theorem evP2 [Labels] {m0 : MachineData} {vars : Nat → BitVec 64} (o : Nat) :
    (Sym.ptr 2 (o : Int)).eval (Env.ofMachine m0 (envR m0) vars) =
      rwA m0 + BitVec.ofNat 64 o := by
  show rwA m0 + BitVec.ofInt 64 (o : Int) = _
  rw [BitVec.ofInt_natCast]

/-- A label at the head of a block is the block's address. -/
theorem lblAt [NativeRustcArm.Host] {k : Nat} (hp : Placed code k) {l : Label}
    {rest : List Directive} {K : Nat} (h : (Kraken.Directive.label l :: rest).IsInfixAt code K) :
    Labels.label l = Host.addrOf (k + K) :=
  hp.label h.cons.1

variable [NativeRustcArm.Host] {k : Nat} {c : Cx} {m0 : MachineData}

/-- **A block that writes nothing**, from `pS ks`. -/
theorem zeroBlock (hp : Placed code k) (ok : Ok c.a m0) {ks ks' : List (XReg × Sym)}
    (hw : wfK ks = true) {t : Nat} (ht : t < c.sl.size) {vars : Nat → BitVec 64}
    (hv0 : vars 0 = (c.sl.getD t 0).c0.toBitVec) (hv1 : vars 1 = (c.sl.getD t 0).c1.toBitVec)
    {bZ : List Directive} {kZ : Nat} (hin : bZ.IsInfixAt code kZ) (hne : bZ ≠ [])
    {SZ : SState} {x : Exit} (hx : exec bZ (pS ks) = some (SZ, x)) (hmem : SZ.mem = [])
    (hok : regsOk t SZ ks' = true) {s : MachineState} (hpc : s.pc = Host.addrOf (k + kZ))
    (hmid : Mid c m0 s.data) (hk : KAt m0 vars ks s.data) :
    Eventually (step1 Host.exe) (fun s' ↦
      PcOk (Env.ofMachine s.data (envR m0) vars) x (Host.addrOf (k + kZ + bZ.length)) s' ∧
      Mid c m0 s'.data ∧ KAt m0 vars ks' s'.data ∧ s'.data.dmem = s.data.dmem) s := by
  have hsp : SZ.sp = .ptr 0 0 := by
    simp only [regsOk, Bool.and_eq_true, beq_iff_eq] at hok; exact hok.2
  have hwf := wf_fold (vars := vars) ok hmid.body
  have hm := match_pS ok hk hw hmid.sw
  refine exec_at (hin.trans hp.1 hne) hx hwf hpc hm fun s1 hm1 hpc1 ↦ ?_
  have hb1 : Body m0 s1.data :=
    hmid.body.of_block hm hm1 hwf rfl all_slots (by simp [keepsAll, hmem, hsp, pS, init])
  have hd1 : s1.data.dmem = s.data.dmem := hm1.dmem_eq hwf hmem
  exact .done _ ⟨hpc1, hmid.of_dmem hb1 hd1, KAt.after hm1 ht hv0 hv1 hmid hok, hd1⟩

/-- **A row's head**: the two copies and the counter zeroed, the inner loop's start. -/
theorem rowHead (hp : Placed code k)
    (hmemcpy : Spec (Labels.label NativeRustcVmArm.Vm.Memcpy.entryLabel) MemcpyPre MemcpyPost) (ok : Ok c.a m0)
    {rows : Array (Array EW)} {t i : Nat} (ht : t < 6) (hi : i < half t)
    {vars : Nat → BitVec 64} (hv0 : vars 0 = (c.sl.getD t 0).c0.toBitVec)
    (hv1 : vars 1 = (c.sl.getD t 0).c1.toBitVec) {ks : List (XReg × Sym)}
    {ksA ksA' : List (XReg × Sym)} (hsA : subK ksA ks = true) (hwA : wfK ksA = true)
    {bA : List Directive} {kA : Nat} (hinA : bA.IsInfixAt code kA) (hneA : bA ≠ [])
    {SA : SState} (hxA : exec bA (pS ksA) = some (SA, .call NativeRustcVmArm.Vm.Memcpy.entryLabel)) {vA : Sym}
    (hokA : CopyOk t ksA' 80 vA SA = true)
    (hvA : vA.eval (Env.ofMachine m0 (envR m0) vars) = rwA m0 + BitVec.ofNat 64 (1024 * (2 * i)))
    {ksB ksB' : List (XReg × Sym)} (hsB : subK ksB ksA' = true) (hwB : wfK ksB = true)
    {bB : List Directive} {kB : Nat} (hkB : kA + bA.length = kB) (hinB : bB.IsInfixAt code kB)
    (hneB : bB ≠ []) {SB : SState} (hxB : exec bB (pS ksB) = some (SB, .call NativeRustcVmArm.Vm.Memcpy.entryLabel))
    {vB : Sym} (hokB : CopyOk t ksB' 1104 vB SB = true)
    (hvB : vB.eval (Env.ofMachine m0 (envR m0) vars) =
      rwA m0 + BitVec.ofNat 64 (1024 * (2 * i + 1)))
    {ksZ ksZ' : List (XReg × Sym)} (hsZ : subK ksZ ksB' = true) (hwZ : wfK ksZ = true)
    {bZ : List Directive} {kZ : Nat} (hkZ : kB + bB.length = kZ) (hinZ : bZ.IsInfixAt code kZ)
    (hneZ : bZ ≠ []) {SZ : SState} (hxZ : exec bZ (pS ksZ) = some (SZ, .fall))
    (hZm : SZ.mem = []) (hokZ : regsOk t SZ ksZ' = true)
    {kI : List (XReg × Sym)} (hsI : subK kI ksZ' = true) {CT : XReg}
    (hct0 : inK CT (.lit 0) ksZ' = true) {kL : Nat} (hkL : kZ + bZ.length = kL)
    {s : MachineState} (hpc : s.pc = Host.addrOf (k + kA)) (hmid : Mid c m0 s.data)
    (hk : KAt m0 vars ks s.data) (hrw : ElemsAt s.data.dmem (rwA m0) (F c.sl rows t i 0) 4096) :
    Eventually (step1 Host.exe) (fun s' ↦ s'.pc = Host.addrOf (k + kL) ∧
      Inner c m0 vars kI CT (fun z ↦ F c.sl rows t i 0 (64 * (2 * i) + z))
        (fun z ↦ F c.sl rows t i 0 (64 * (2 * i + 1) + z)) (F c.sl rows t i 0) 0 s'.data) s := by
  have hsl : t < c.sl.size := by rw [hmid.sl_size]; exact ht
  have hh := half_le t
  refine (copyRow hp hmemcpy ok hwA hsl hv0 hv1 hinA hneA hxA ⟨by decide, by decide⟩ hokA
    (by omega) hvA hpc hmid (hk.sub hsA) hrw).bind
    fun s1 ⟨hpc1, hmid1, hk1, hrw1, hbA1, _⟩ ↦ ?_
  refine (copyRow hp hmemcpy ok hwB hsl hv0 hv1 hinB hneB hxB ⟨by decide, by decide⟩ hokB
    (by omega) hvB (by rw [hpc1, Nat.add_assoc, hkB]) hmid1 (hk1.sub hsB) hrw1).bind
    fun s2 ⟨hpc2, hmid2, hk2, hrw2, hbB2, hkeep2⟩ ↦ ?_
  have hbA2 := hkeep2 80 _ (Or.inl (by decide)) (by decide) hbA1
  refine (zeroBlock hp ok hwZ hsl hv0 hv1 hinZ hneZ hxZ hZm hokZ
    (by rw [hpc2, Nat.add_assoc, hkZ]) hmid2 (hk2.sub hsZ)).bind
    fun s3 ⟨hpc3, hmid3, hk3, hd3⟩ ↦ ?_
  refine .done _ ⟨by rw [hpc3, Nat.add_assoc, hkL], hmid3, hk3.sub hsI, ?_, ?_, ?_, ?_⟩
  · rw [hk3.reg (memK hct0)]; rfl
  · rw [hd3]; exact hbA2
  · rw [hd3]; exact hbB2
  · rw [hd3]; exact hrw2

/-- **A row of an unrolled round**. -/
theorem rowD (hp : Placed code k)
    (hmul : Spec (Labels.label NativeRustcVmArm.Vm.EWMul.entryLabel) EWMulPre EWMulPost)
    (hmemcpy : Spec (Labels.label NativeRustcVmArm.Vm.Memcpy.entryLabel) MemcpyPre MemcpyPost) (ok : Ok c.a m0)
    {rows : Array (Array EW)} (hsz : rows.size = 64)
    (hrow : ∀ r < 64, (rows.getD r #[]).size = 64) {t i : Nat} (ht : t < 6) (hi : i < half t)
    {vars : Nat → BitVec 64} (hv0 : vars 0 = (c.sl.getD t 0).c0.toBitVec)
    (hv1 : vars 1 = (c.sl.getD t 0).c1.toBitVec) {ks : List (XReg × Sym)}
    {ksA ksA' : List (XReg × Sym)} (hsA : subK ksA ks = true) (hwA : wfK ksA = true)
    {bA : List Directive} {kA : Nat} (hinA : bA.IsInfixAt code kA) (hneA : bA ≠ [])
    {SA : SState} (hxA : exec bA (pS ksA) = some (SA, .call NativeRustcVmArm.Vm.Memcpy.entryLabel)) {vA : Sym}
    (hokA : CopyOk t ksA' 80 vA SA = true)
    (hvA : vA.eval (Env.ofMachine m0 (envR m0) vars) = rwA m0 + BitVec.ofNat 64 (1024 * (2 * i)))
    {ksB ksB' : List (XReg × Sym)} (hsB : subK ksB ksA' = true) (hwB : wfK ksB = true)
    {bB : List Directive} {kB : Nat} (hkB : kA + bA.length = kB) (hinB : bB.IsInfixAt code kB)
    (hneB : bB ≠ []) {SB : SState} (hxB : exec bB (pS ksB) = some (SB, .call NativeRustcVmArm.Vm.Memcpy.entryLabel))
    {vB : Sym} (hokB : CopyOk t ksB' 1104 vB SB = true)
    (hvB : vB.eval (Env.ofMachine m0 (envR m0) vars) =
      rwA m0 + BitVec.ofNat 64 (1024 * (2 * i + 1)))
    {ksZ ksZ' : List (XReg × Sym)} (hsZ : subK ksZ ksB' = true) (hwZ : wfK ksZ = true)
    {bZ : List Directive} {kZ : Nat} (hkZ : kB + bB.length = kZ) (hinZ : bZ.IsInfixAt code kZ)
    (hneZ : bZ ≠ []) {SZ : SState} (hxZ : exec bZ (pS ksZ) = some (SZ, .fall))
    (hZm : SZ.mem = []) (hokZ : regsOk t SZ ksZ' = true)
    {kI : List (XReg × Sym)} (hsI : subK kI ksZ' = true) (hwI : wfK kI = true)
    {A B CT D : XReg} (hct0 : inK CT (.lit 0) ksZ' = true) (hA : inK A A0 kI = true)
    (hB : inK B B0 kI = true) (h22 : inK .X22 V0 kI = true) (h23 : inK .X23 V1 kI = true)
    (hD : inK D P kI = true)
    {bL : List Directive} {kL : Nat} (hkL : kZ + bZ.length = kL) (hinL : bL.IsInfixAt code kL)
    (hneL : bL ≠ []) {SL : SState} (hxL : exec bL (loS A B CT) = some (SL, .call NativeRustcVmArm.Vm.EWMul.entryLabel))
    (hshL : LSh .X22 .X23 .X19 .X20 (loS A B CT) SL = true)
    (hLx : SL.reg .X21 = some (.bin .add .W64 (.reg D) (.reg CT)))
    (hLct : SL.reg CT = some (.bin .add .W64 (.reg CT) (.lit 16)))
    (hLk : keepK kI SL = true) (hcc : calleeSaved CT = true)
    {bS : List Directive} {kS kE : Nat} (hkS : kL + bL.length = kS)
    (hinS : bS.IsInfixAt code kS) (hneS : bS ≠ []) {SS : SState} {lbl : Label}
    (hxS : exec bS (dstS (1024 * i)) = some (SS, .cond (notEnd CT) lbl))
    (hlbl : Labels.label lbl = Host.addrOf (k + kL)) (hkE : kS + bS.length = kE)
    (hmem : SS.mem = stW .X19 .X20 (1024 * i)) (hsp : SS.sp = .sp)
    (hSk : keepK kI SS = true) (hSct : SS.reg CT = some (.reg CT))
    {s : MachineState} (hpc : s.pc = Host.addrOf (k + kA)) (hmid : Mid c m0 s.data)
    (hk : KAt m0 vars ks s.data) (hrw : ElemsAt s.data.dmem (rwA m0) (F c.sl rows t i 0) 4096) :
    Eventually (step1 Host.exe) (fun s' ↦ s'.pc = Host.addrOf (k + kE) ∧ Mid c m0 s'.data ∧
      KAt m0 vars kI s'.data ∧ ElemsAt s'.data.dmem (rwA m0) (F c.sl rows t (i + 1) 0) 4096) s := by
  have hsl : t < c.sl.size := by rw [hmid.sl_size]; exact ht
  have hh := half_le t
  refine (rowHead hp hmemcpy ok ht hi hv0 hv1 hsA hwA hinA hneA hxA hokA hvA hsB hwB hkB hinB
    hneB hxB hokB hvB hsZ hwZ hkZ hinZ hneZ hxZ hZm hokZ hsI hct0 hkL hpc hmid hk hrw).bind
    fun s3 ⟨hpc3, hI⟩ ↦ ?_
  refine (innerD_run hp hmul ok hwI (memK hA) (memK hB) (memK h22) (memK h23) (memK hD) hv0 hv1
    hinL hneL hxL hshL hLx hLct hLk hcc
    hkS hinS hneS hxS hlbl hkE hmem hsp hSk hSct (by omega)
    (G := F c.sl rows t i) (fun j hj ↦ F_succ_fun hsz hrow hsl hi hj) hpc3 hI).mono
    fun s' ⟨hpc', hI'⟩ ↦ ⟨hpc', hI'.mid, hI'.kat, ?_⟩
  have := hI'.rows
  rwa [F_row] at this

end

end NativeRustcVmArm.KeccakGkr.KeccakOpen
