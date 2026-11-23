module

public import NativeRustcVmX64.Layout.BuildLayout.Stores
public import NativeRustcVmX64.Code.Vm.ColumnKappas.Names

/-!
# `build_layout` on x86-64: the last row and height, `column_kappas` (`b15`)

`b15` stores the sixth table's row count and height (its `bit_length`, at least `9`) and calls
`column_kappas` on the frame's `kappas` (offset `48`), the log-sizes and the heights just stored:
the heights in memory are the model's (`heightsF`), the `kappas` the model's `columnKappas`.
-/

namespace NativeRustcVmX64.Layout.BuildLayout

open NativeRustcX64 NativeRustcX64.Sym NativeRustcVmX64.Vm.BuildLayout NativeRustcVmX64.Transcript
open NativeRustcVm.Transcript NativeRustcVmX64.Layout.BuildFrame
open NativeVm.Model NativeRustcVm.Layout LeanVM.Protocol.Verifier NativeVm.Math.Layout
open NativeRustcVm (WordAt WordsAt wordOf)

public section

variable {m0 : MachineData} {bc : Array UInt64}

theorem kappasBytes_eq : kappasBytes = 1264 := rfl
theorem placementsBytes_eq : placementsBytes = 3792 := rfl

/-- **The geometry** in numbers: the frame below the entry's RSP, the layout off the stack. -/
theorem Facts.num [Labels] (hF : Facts bc m0) :
    (fb m0).toNat + 1360 = (rspOf m0).toNat ∧ 7824 ≤ (rspOf m0).toNat ∧
      (rspOf m0).toNat + 8 ≤ 2 ^ 64 ∧ (ll m0).toNat + 3912 ≤ 2 ^ 64 ∧
      ((ll m0).toNat + 3912 ≤ (rspOf m0).toNat - 7824 ∨ (rspOf m0).toNat + 8 ≤ (ll m0).toNat) := by
  have h1 := hF.fb_toNat
  have h2 := hF.rsp
  have h3 : (ll m0).toNat + 3912 ≤ (stackBelow m0 7824).toNat ∨
      (stackBelow m0 7824).toNat + (7824 + 8) ≤ (ll m0).toNat := hF.lo
  rw [hF.sb_toNat] at h3
  refine ⟨by omega, h2.1, h2.2, hF.lnw, by omega⟩

theorem mapped_off {d : Mem 64} {a : BitVec 64} {n o l : Nat} (h : NativeRustcVm.Mapped d a n)
    (hl : o + l ≤ n) : NativeRustcVm.Mapped d (off a o) l := fun i hi ↦ by
  rw [show off a o + BitVec.ofNat 64 i = off a (o + i) from off_off a o i]
  exact h _ (by omega)

/-- Words kept where memory changed elsewhere. -/
theorem Ws.same {d d' : Mem 64} {b : BitVec 64} {ws : List (Nat × UInt64)} (h : Ws d b ws)
    {Rc : BitVec 64 → Prop} (hs : NativeRustcVm.SameOutside d d' Rc)
    (hR : ∀ p ∈ ws, ∀ i < 8, ¬ Rc (off b (p.1 + i))) : Ws d' b ws := fun p hp ↦
  NativeRustcVm.BytesAt.of_sameOutside (h p hp) hs fun i hi ↦ by
    rw [show b + BitVec.ofNat 64 p.1 + BitVec.ofNat 64 i = off b (p.1 + i) from off_off b p.1 i]
    exact hR p hp i (by simpa [NativeRustcVm.length_wordBytes] using hi)

theorem ite9_eval [Labels] (env : Env) (x : Sym) :
    ((Sym.ite (SBool.cmp .ult .W64 x (.lit 10)).not x (.lit 9)).eval env).toNat =
      max (x.eval env).toNat 9 := by
  show (if (!(SBool.cmp .ult .W64 x (.lit 10)).eval env) = true then x.eval env
    else (Sym.lit 9).eval env).toNat = _
  have h10 : ((Sym.lit 10).eval env).toNat = 10 := lit_eval env (by decide)
  have h9 : ((Sym.lit 9).eval env).toNat = 9 := lit_eval env (by decide)
  rw [ult_eval, h10]
  by_cases h : (x.eval env).toNat < 10
  · rw [decide_eq_true h]
    simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
    rw [h9]; omega
  · rw [decide_eq_false h]
    simp only [Bool.not_false, ↓reduceIte]
    omega

theorem rows_le [Labels] (hc : Chk m0) : ∀ t < 6, (rowsOf m0).getD t 0 ≤ 2 ^ 30 := fun t ht ↦ by
  rw [rows_getD m0 ht]; exact hc.2.2.2.1 t ht

theorem rng1a {A q : Nat} (h : A - 1312 ≤ q) : A - 1368 ≤ q :=
  Nat.le_trans (Nat.sub_le_sub_left (by decide) A) h
theorem rng1b {A q : Nat} (h : q < A - 1312 + 1264) (hA : 7824 ≤ A) : q < A - 48 := by
  have : A - 1312 + 1264 = A - 48 := by omega
  rwa [this] at h
theorem rng1 {A q : Nat} (h : A - 1312 ≤ q ∧ q < A - 1312 + 1264) (hA : 7824 ≤ A) :
    A - 1368 ≤ q ∧ q < A - 48 := ⟨rng1a h.1, rng1b h.2 hA⟩
theorem rng2 {A q : Nat} (h : A - 1368 ≤ q ∧ q < A - 1368 + 8) (hA : 7824 ≤ A) :
    A - 1368 ≤ q ∧ q < A - 48 := by omega
theorem rng3a {A q : Nat} (h : A - 1368 ≤ q) : A - 7824 ≤ q :=
  Nat.le_trans (Nat.sub_le_sub_left (by decide) A) h
theorem rng3b {A q : Nat} (h : q < A - 48) (hA : 7824 ≤ A) : q < A - 7824 + 7824 := by
  have : A - 7824 + 7824 = A := by omega
  rw [this]; omega
theorem rng3 {A q : Nat} (h : A - 1368 ≤ q ∧ q < A - 48) (hA : 7824 ≤ A) :
    A - 7824 ≤ q ∧ q < A - 7824 + 7824 := ⟨rng3a h.1, rng3b h.2 hA⟩
theorem rng4 {A x j : Nat} (h : A - 1368 ≤ x ∧ x < A - 48) (hx : x = A - 1360 + j) (hj : 1312 ≤ j)
    (hA : 7824 ≤ A) : False := by omega
theorem rng5 {A L x j : Nat} (h : A - 1368 ≤ x ∧ x < A - 48) (hx : x = L + j) (hj : j < 3912)
    (hLA : L + 3912 ≤ A - 7824 ∨ A + 8 ≤ L) (hA : 7824 ≤ A) : False := by omega

/-- **After `column_kappas`**: the layout's first `120` bytes stored, the `kappas` in the frame. -/
structure SK [Labels] (m0 d : MachineData) : Prop where
  b : B m0 8 d
  r13 : reg d .r13 = ll m0
  r12 : reg d .r12 = off (fb m0) 48
  ws : Ws d.dmem (ll m0) (wsK0 m0)
  kap : WordsAt d.dmem (off (fb m0) 48)
    (natWords (columnKappas (lmN m0) (bitLength (nN m0) - 5) (heightsF (rowsOf m0))))
  pow2 : Pow2 (nN m0)
  chk : Chk m0

variable [Host] {k : Nat}

/-- **`b15` and `column_kappas`.** -/
theorem kappas (hp : Placed code k)
    (hck : Spec (Labels.label NativeRustcVmX64.Vm.ColumnKappas.entryLabel) ColumnKappasPre ColumnKappasPost) (hF : Facts bc m0)
    {st : MachineState} (hpc : st.pc = Host.addrOf (k + NativeRustcVmX64.Vm.BuildLayout.b15Offset)) (hs : Ht m0 st.data 12 5)
    (h15 : reg st.data .r15 = (rowW m0 5).toBitVec) :
    Eventually (step1 Host.exe) (fun s ↦ s.pc = Host.addrOf (k + NativeRustcVmX64.Vm.BuildLayout.b16Offset) ∧ SK m0 s.data) st := by
  obtain ⟨hA, hA1, hA2, hL, hLA⟩ := hF.num
  have hb := hs.1.b
  have hwf := wfL (ret := (Host.addrOf (k + NativeRustcVmX64.Vm.BuildLayout.b15Offset + b15.length)).toBitVec) hF hb
  obtain ⟨hok, h0, hmiss, w1, w2, hdi, hsi, hdx, hcx, h12, h13, hK⟩ := ok_b15
  refine exec_at (b15_in_code.trans hp.1 (List.cons_ne_nil _ _)) exit_b15 hwf (fun _ _ ↦ rfl) hpc
    (matchL hb hs.1.r13) fun st1 hm1 hpc1 ↦ ?_
  have hb1 : B m0 0 st1.data := hb.of_block hF.stack (by decide) hwf hm1 hok slots_le restL
  have hin := writesIn_of hok
  have hc := hs.1.chk
  have hr := rows_le hc
  have hrs := rowsOf_size m0
  have hws1 : Ws st1.data.dmem (ll m0) (wsK0 m0) := by
    have := Ws.take2 (n := 12) (Ws.keep hwf hm1 hin (r := 1) rfl
      (fun p hp ↦ wsK_le p (List.mem_of_mem_take hp)) (misses_of hmiss rfl) hs.1.ws) rfl rfl
      (w_write hm1 (r := 1) rfl (by decide) w1 (by
        show (reg st.data .r15).toNat = _; rw [h15, row_toNat (by decide)]; rfl))
      (w_write hm1 (r := 1) rfl (by decide) w2 (by
        rw [ite9_eval]
        show max (reg st.data .rax).toNat 9 = _
        rw [hs.2, ← rows_getD m0 (by decide)]
        exact (toNat_toUInt64 (by
          have := bitLength_le (k := 64) (n := (rowsOf m0).getD 5 0 - 1) (by
            have := hr 5 (by decide); omega)
          omega)).symm))
    rwa [List.take_of_length_le (by simp)] at this
  -- the registers at the call
  have hdi1 : reg st1.data .rdi = off (fb m0) 48 := (hm1.regs .rdi _ hdi).trans (eval_ptr0 48)
  have h121 : reg st1.data .r12 = off (fb m0) 48 := (hm1.regs .r12 _ h12).trans (eval_ptr0 48)
  have hcx1 : reg st1.data .rcx = off (ll m0) 24 := (hm1.regs .rcx _ hcx).trans rfl
  have hsi1 : reg st1.data .rsi = reg m0 .rsi := (hm1.regs .rsi _ hsi).trans hs.1.rbx
  have hdx1 : reg st1.data .rdx = (bitLength (nN m0) - 5).toUInt64.toBitVec :=
    (hm1.regs .rdx _ hdx).trans (load_fr (hs.1.fr.get (by simp)))
  have hlb : bitLength (nN m0) - 5 < 2 ^ 64 := by have := hc.2.2.2.2; omega
  have h131 : reg st1.data .r13 = ll m0 := r13_of hm1 h13
  clear hok h0 hmiss w1 w2 hdi hsi hdx hcx h12 h13 hK hm1 hwf
  have hsp1 := hb1.rsp0
  have hcs : (stackBelow st1.data columnKappasStack).toNat = (rspOf m0).toNat - 1368 := by
    show (stackBelow st1.data 8).toNat = _
    rw [stackBelow_callee hsp1 (by omega), stackBelow_toNat (by omega)]
  have hk48 : (off (fb m0) 48).toNat = (rspOf m0).toNat - 1312 := by
    rw [hF.off_toNat (by decide)]; omega
  have hl24 : (off (ll m0) 24).toNat = (ll m0).toNat + 24 := toNat_off (by omega)
  have hheights : natsOf st1.data (reg st1.data .rcx) nTables = heightsF (rowsOf m0) := by
    rw [hcx1]
    exact natsOf_of_words (heights_words hrs hws1) (heights_lt hrs hr) (heightsF_size hrs)
  have hfm : NativeRustcVm.Mapped st1.data.dmem (fb m0) 1368 :=
    Mapped.keeps (frame_mapped hF.stack (by decide)) hb1.fr.kept
  have hlm : NativeRustcVm.Mapped st1.data.dmem (ll m0) 3912 :=
    Mapped.keeps hF.lr.1 hb1.fr.kept
  have hpre : ColumnKappasPre st1.data := by
    refine ⟨hb1.stackOk hF.stack (by decide), ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [hdi1]
      exact ⟨mapped_off hfm (by decide),
        (show (off (fb m0) 48).toNat + 1264 ≤ 2 ^ 64 by rw [hk48]; omega)⟩
    · rw [hdi1]
      exact (show (off (fb m0) 48).toNat + 1264 ≤ (stackBelow st1.data columnKappasStack).toNat ∨
        (stackBelow st1.data columnKappasStack).toNat + (8 + 8) ≤ (off (fb m0) 48).toNat by
        rw [hk48, hcs]; omega)
    · rw [hcx1]
      exact ⟨mapped_off hlm (by decide), (show (off (ll m0) 24).toNat + 48 ≤ 2 ^ 64 by rw [hl24]; omega)⟩
    · rw [hcx1]
      exact (show (off (ll m0) 24).toNat + 48 ≤ (stackBelow st1.data columnKappasStack).toNat ∨
        (stackBelow st1.data columnKappasStack).toNat + (8 + 8) ≤ (off (ll m0) 24).toNat by
        rw [hl24, hcs]; omega)
    · rw [hdi1, hcx1]
      exact (show (off (fb m0) 48).toNat + 1264 ≤ (off (ll m0) 24).toNat ∨
        (off (ll m0) 24).toNat + 48 ≤ (off (fb m0) 48).toNat by rw [hk48, hl24]; omega)
    · rw [hheights]
      have := heights_le hrs hr (t := opKeccak) (by decide)
      have hq : qkeccakSlotBits < 64 := by decide
      omega
  refine call_then hpc1 hck hpre fun st2 hpc2 hrsp2 hpost ↦ ?_
  obtain ⟨hwk, hch, hsv⟩ := hpost
  -- the changed bytes: the `kappas` and the callee's stack
  have hRc : ∀ q, (NativeRustcVm.InRange (reg st1.data .rdi) kappasBytes q ∨
      NativeRustcVm.InRange (stackBelow st1.data columnKappasStack) columnKappasStack q) →
      (rspOf m0).toNat - 1368 ≤ q.toNat ∧ q.toNat < (rspOf m0).toNat - 48 := by
    intro q hq
    rcases hq with h | h
    · rw [hdi1, inRange_iff' (by unfold NativeRustcVm.NoWrap; rw [hk48, kappasBytes_eq]; omega), hk48,
        kappasBytes_eq] at h
      exact rng1 h hA1
    · rw [inRange_iff' (by unfold NativeRustcVm.NoWrap; rw [hcs, show columnKappasStack = 8 from rfl]; omega), hcs,
        show columnKappasStack = 8 from rfl] at h
      exact rng2 h hA1
  have hsb : (stackBelow m0 7824).toNat = (rspOf m0).toNat - 7824 := hF.sb_toNat
  have hb2 : B m0 8 st2.data := hb1.call hsv hrsp2 hch
    (fun q hq ↦ .inr ((inRange_iff' (by unfold NativeRustcVm.NoWrap; rw [hsb]; omega)).mpr
      (by rw [hsb]; exact rng3 (hRc q hq) hA1)))
    (fun p hp i hi hq ↦ rng4 (hRc _ hq) (hF.off_toNat (by have := slots_le p hp; omega))
      (by have := slots_ge p hp; omega) hA1)
    (fun j hj hq ↦ rng4 (hRc _ hq) (hF.off_toNat (by omega)) (by omega) hA1)
  refine .done _ ⟨hpc2.trans rfl, hb2, (hsv.1 .r13 rfl).trans h131, (hsv.1 .r12 rfl).trans h121, ?_,
    ?_, hs.1.pow2, hc⟩
  · refine hws1.same hch fun p hp i hi hq ↦ ?_
    have h1 := wsK_le p hp
    exact rng5 (hRc _ hq) (toNat_off (by omega)) (by omega) hLA hA1
  · have e : columnKappas (reg st1.data .rsi).toNat (reg st1.data .rdx).toNat
        (natsOf st1.data (reg st1.data .rcx) nTables) =
        columnKappas (lmN m0) (bitLength (nN m0) - 5) (heightsF (rowsOf m0)) := by
      rw [hheights, hsi1, hdx1]
      show NativeVm.Model.columnKappas (lmN m0) (bitLength (nN m0) - 5).toUInt64.toNat _ = _
      rw [toNat_toUInt64 hlb]
    rw [← e, ← hdi1]
    exact hwk

end

end NativeRustcVmX64.Layout.BuildLayout
