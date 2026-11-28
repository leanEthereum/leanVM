module

public import NativeRustcVmX64.Bus.BytecodeShare.Frame
public import NativeRustcVm.Arrays.ReadLemmas

/-!
# `bytecode_share`: the point's copy and the result (x86-64)

From `b12` on, the check passed: `bytecode_low` goes to the point's first slots, two elements a
turn (`b18`, the head `NativeRustcVmX64.Vm.BytecodeShare.label_13`), then the odd one (`b20`), the slot point after them
and the result to the output (`b21`), then the epilogue. `Cp j`: the first `j` elements copied,
nothing else changed since `b12` but the point.

- `copied`, `copied_words`: words a block copied from one region to another.
- `finish`: `b21` and the epilogue; `odd`: `b20`; `pair`: a turn of `b18`.
-/

namespace NativeRustcVmX64.Bus.BytecodeShare

open NativeRustcX64 NativeRustcX64.Sym NativeRustcVmX64.Vm.BytecodeShare NativeRustcVmX64.Transcript
open NativeRustcVmX64.Sumcheck NativeVm.Model NativeRustcVm.Transcript
open NativeRustcVm.Bus (busPointCap)

public section

/-! ## Arithmetic on small lengths -/

theorem ofNat_toNat64 (x : BitVec 64) : BitVec.ofNat 64 x.toNat = x := by simp

theorem shl4 (x : BitVec 64) (h : x.toNat < 64) :
    BinOp.apply .shl .W64 x (BitVec.ofNat 64 4) = BitVec.ofNat 64 (16 * x.toNat) := by
  have key : ∀ y : Fin 64, BinOp.apply .shl .W64 (BitVec.ofNat 64 y.val) (BitVec.ofNat 64 4) =
      BitVec.ofNat 64 (16 * y.val) := by decide +kernel
  have e := key ⟨x.toNat, h⟩
  simp only [ofNat_toNat64] at e
  exact e

theorem and1_eq (x : BitVec 64) (h : x.toNat < 64) :
    CmpOp.apply .eq .W8 (BinOp.apply .and .W8 x (BitVec.ofNat 64 1)) (BitVec.ofNat 64 0) =
      decide (x.toNat % 2 = 0) := by
  have key : ∀ y : Fin 64, CmpOp.apply .eq .W8 (BinOp.apply .and .W8 (BitVec.ofNat 64 y.val)
      (BitVec.ofNat 64 1)) (BitVec.ofNat 64 0) = decide (y.val % 2 = 0) := by decide +kernel
  have e := key ⟨x.toNat, h⟩
  simp only [ofNat_toNat64] at e
  exact e

theorem andSelf_eq (x : BitVec 64) (h : x.toNat < 64) :
    CmpOp.apply .eq .W64 (BinOp.apply .and .W64 x x) (BitVec.ofNat 64 0) = decide (x.toNat = 0) := by
  have key : ∀ y : Fin 64, CmpOp.apply .eq .W64 (BinOp.apply .and .W64 (BitVec.ofNat 64 y.val)
      (BitVec.ofNat 64 y.val)) (BitVec.ofNat 64 0) = decide (y.val = 0) := by decide +kernel
  have e := key ⟨x.toNat, h⟩
  simp only [ofNat_toNat64] at e
  exact e

theorem eq1_eq (x : BitVec 64) (h : x.toNat < 64) :
    CmpOp.apply .eq .W64 x (BitVec.ofNat 64 1) = decide (x.toNat = 1) := by
  have key : ∀ y : Fin 64, CmpOp.apply .eq .W64 (BitVec.ofNat 64 y.val) (BitVec.ofNat 64 1) =
      decide (y.val = 1) := by decide +kernel
  have e := key ⟨x.toNat, h⟩
  simp only [ofNat_toNat64] at e
  exact e

theorem and62 (x : BitVec 64) (h : x.toNat < 64) :
    (BinOp.apply .and .W32 (UnOp.apply .trunc .W32 x) (BitVec.ofNat 64 62)).toNat =
      x.toNat - x.toNat % 2 := by
  have key : ∀ y : Fin 64, (BinOp.apply .and .W32 (UnOp.apply .trunc .W32 (BitVec.ofNat 64 y.val))
      (BitVec.ofNat 64 62)).toNat = y.val - y.val % 2 := by decide +kernel
  have e := key ⟨x.toNat, h⟩
  simp only [ofNat_toNat64] at e
  exact e

theorem add64 (x y : BitVec 64) : BinOp.apply .add .W64 x y = x + y := by
  simp only [BinOp.apply, low_W64, ext_W64]

theorem eq64 (x y : BitVec 64) : CmpOp.apply .eq .W64 x y = decide (x = y) := by
  simp only [CmpOp.apply, low_W64]
  by_cases h : x = y <;> simp [h]

theorem size4 (x : BitVec 64) : ((x.toNat + 4).toUInt64).toBitVec = x + BitVec.ofNat 64 4 := by
  apply BitVec.eq_of_toNat_eq
  simp [BitVec.toNat_add]

/-! ## Copies -/

/-- **A word a block copied**: region `rd`'s eight bytes at `od` are region `rr`'s at `os`. -/
theorem copied [Labels] {st st' : MachineData} {rs : List (BitVec 64 × Nat)}
    {vars : Nat → BitVec 64} {ret : BitVec 64} {S : SState}
    (hm : Match (Env.ofMachine st rs vars ret) S st') {rd rr od os : Nat} {bd bs : BitVec 64}
    {szd szs : Nat} (hbd : rs[rd]? = some (bd, szd)) (hbs : rs[rr]? = some (bs, szs))
    (hd : od + 8 ≤ szd) (hmap : NativeRustcVm.Mapped st.dmem (off bs os) 8)
    (hw : ∀ t < 8, findWrite rd (od + t) S.mem = some (.load rr os 8, t)) :
    ∀ i < 8, st'.dmem.get? (off bd (od + i)) = st.dmem.get? (off bs (os + i)) := by
  have h2 := NativeRustcVm.wordAt_of_mapped hmap
  have h1 := wordAt_write hm hbd hd hw
  simp only [Sym.eval] at h1
  rw [load_ofMachine hbs h2, UInt64.ofBitVec_toBitVec] at h1
  intro i hi
  have hi' : i < (NativeRustcVm.wordBytes (NativeRustcVm.wordOf st.dmem (off bs os))).length := by
    rw [NativeRustcVm.length_wordBytes]; exact hi
  rw [← off_add, ← off_add, h1 i hi', h2 i hi']

/-- **Words a block copied** (`CopyW`). -/
theorem copied_words [Labels] {st st' : MachineData} {rs : List (BitVec 64 × Nat)}
    {vars : Nat → BitVec 64} {ret : BitVec 64} {S : SState}
    (hm : Match (Env.ofMachine st rs vars ret) S st') {rd rr od os nw : Nat} {bd bs : BitVec 64}
    {szd szs : Nat} (hbd : rs[rd]? = some (bd, szd)) (hbs : rs[rr]? = some (bs, szs))
    (hd : od + 8 * nw ≤ szd) (hmap : NativeRustcVm.Mapped st.dmem (off bs os) (8 * nw))
    (hw : CopyW S rd od rr os nw) :
    ∀ i < 8 * nw, st'.dmem.get? (off bd (od + i)) = st.dmem.get? (off bs (os + i)) := by
  intro i hi
  have hw8 : i / 8 < nw := by omega
  have e := copied hm (od := od + 8 * (i / 8)) (os := os + 8 * (i / 8)) hbd hbs (by omega)
    (fun t ht ↦ by
      have := hmap (8 * (i / 8) + t) (by omega)
      rw [off_add, ← Nat.add_assoc] at this
      rw [off_add]; exact this) (hw _ hw8) (i % 8) (Nat.mod_lt _ (by omega))
  rwa [show od + 8 * (i / 8) + i % 8 = od + i by omega,
    show os + 8 * (i / 8) + i % 8 = os + i by omega] at e

/-- Bytes moved from `a` to `b` carry the elements there. -/
theorem ewsAt_transfer {d d' : Mem 64} {a b : BitVec 64} {xs : List EW}
    (htr : ∀ i < 16 * xs.length, d'.get? (b + BitVec.ofNat 64 i) = d.get? (a + BitVec.ofNat 64 i))
    (h : NativeRustcVm.EWsAt d a xs) : NativeRustcVm.EWsAt d' b xs := fun i hi ↦ by
  have := hi
  rw [NativeRustcVm.length_ewsBytes] at this
  rw [htr i this]
  exact h i hi

/-- A sub-range of a range that does not wrap. -/
theorem sub_ok {d : Mem 64} {x : BitVec 64} {N o l : Nat} (hm : NativeRustcVm.Mapped d x N)
    (hnw : NativeRustcVm.NoWrap x N) (hol : o + l ≤ N) (hl : 0 < l) :
    NativeRustcVm.Mapped d (off x o) l ∧ NativeRustcVm.NoWrap (off x o) l ∧
      (off x o).toNat = x.toNat + o := by
  unfold NativeRustcVm.NoWrap at hnw
  have e : (off x o).toNat = x.toNat + o := toNat_off (by omega)
  refine ⟨mapped_off hm hol, ?_, e⟩
  unfold NativeRustcVm.NoWrap; rw [e]; omega

/-- A sub-range of a range apart from another is apart from it. -/
theorem apart_sub {x y : BitVec 64} {N M o l : Nat} (hA : NativeRustcVm.Apart x N y M)
    (hnw : NativeRustcVm.NoWrap x N) (hol : o + l ≤ N) (hl : 0 < l) :
    NativeRustcVm.Apart (off x o) l y M := by
  unfold NativeRustcVm.Apart at hA ⊢
  unfold NativeRustcVm.NoWrap at hnw
  rw [toNat_off (by omega)]
  omega

/-- Two sub-ranges of ranges apart are apart. -/
theorem apart_sub2 {x y : BitVec 64} {N M o l o' l' : Nat} (hA : NativeRustcVm.Apart x N y M)
    (hnx : NativeRustcVm.NoWrap x N) (hny : NativeRustcVm.NoWrap y M) (hol : o + l ≤ N)
    (hl : 0 < l) (hol' : o' + l' ≤ M) (hl' : 0 < l') :
    NativeRustcVm.Apart (off x o) l (off y o') l' :=
  Apart.symm' (apart_sub (Apart.symm' (apart_sub hA hnx hol hl)) hny hol' hl')

/-- Bytes of a range at `a` and from `a`, joined. -/
theorem inRange_join {x q : BitVec 64} {N a b : Nat} (hnw : NativeRustcVm.NoWrap x N)
    (hab : a + b ≤ N) (hq : NativeRustcVm.InRange x a q ∨ NativeRustcVm.InRange (off x a) b q) :
    NativeRustcVm.InRange x (a + b) q := by
  unfold NativeRustcVm.NoWrap at hnw
  rw [inRange_iff' (by unfold NativeRustcVm.NoWrap; omega)]
  rcases hq with hq | hq
  · rw [inRange_iff' (by unfold NativeRustcVm.NoWrap; omega)] at hq; omega
  · rcases Nat.eq_zero_or_pos b with rfl | hb
    · unfold NativeRustcVm.InRange at hq; omega
    rw [inRange_iff' (by unfold NativeRustcVm.NoWrap; rw [toNat_off (by omega)]; omega),
      toNat_off (by omega)] at hq
    omega

/-- A byte before `a` is not in the range from `a`. -/
theorem not_inRange_off {x : BitVec 64} {N a b i : Nat} (hnw : NativeRustcVm.NoWrap x N)
    (hab : a + b ≤ N) (hi : i < a) : ¬ NativeRustcVm.InRange (off x a) b (x + BitVec.ofNat 64 i) := by
  unfold NativeRustcVm.NoWrap at hnw
  rcases Nat.eq_zero_or_pos b with rfl | hb
  · unfold NativeRustcVm.InRange; omega
  rw [inRange_iff' (by unfold NativeRustcVm.NoWrap; rw [toNat_off (by omega)]; omega),
    toNat_off (by omega), show x + BitVec.ofNat 64 i = off x i from rfl, toNat_off (by omega)]
  omega

/-! ## The copy's invariant -/

/-- **`j` elements copied**, since the state `m` at `b12`. -/
structure Cp (m0 m : MachineData) (v0 : BitVec 64) (j : Nat) (st : MachineData) : Prop where
  fr : BF m0 (OP m0) 8 st
  r15 : reg st .r15 = v0
  rax : reg st .rax = reg m0 .r8 + BitVec.ofNat 64 4
  rcx : reg st .rcx = off (pAt m0) (16 * nB m0)
  le : j ≤ nB m0
  cpy : ∀ i < 16 * j, st.dmem.get? (pAt m0 + BitVec.ofNat 64 i) =
    m0.dmem.get? (bAt m0 + BitVec.ofNat 64 i)
  same : NativeRustcVm.SameOutside m.dmem st.dmem (NativeRustcVm.InRange (pAt m0) (16 * j))
  kept : Kept m.dmem st.dmem

section
variable [Labels] {a : DecArea} {s0 : TState} {m0 m : MachineData} {v0 : BitVec 64}

theorem nB_le (h : BytecodeSharePre a s0 m0) : nB m0 ≤ 63 := (pre_parts h).2.2.2.2.2.1

/-- `bytecode_low` readable and apart from the stack. -/
theorem bOk (h : BytecodeSharePre a s0 m0) :
    NativeRustcVm.Mapped m0.dmem (bAt m0) (16 * nB m0) ∧ NativeRustcVm.NoWrap (bAt m0) (16 * nB m0) ∧
      NativeRustcVm.Apart (bAt m0) (16 * nB m0) (stackBelow m0 bytecodeShareStack)
        (bytecodeShareStack + 8) :=
  ⟨(pre_parts h).2.2.2.2.2.2.1.1.1, (pre_parts h).2.2.2.2.2.2.1.1.2,
    (pre_parts h).2.2.2.2.2.2.1.2⟩

/-- **`bytecode_low` kept** while the outputs are the `TState` and the point. -/
theorem b_kept (h : BytecodeSharePre a s0 m0) {O : BitVec 64 → Prop} (hO : ∀ q, O q → OP m0 q)
    {o : Nat} {st : MachineData} (hf : BF m0 O o st) :
    ∀ i < 16 * nB m0, st.dmem.get? (bAt m0 + BitVec.ofNat 64 i) =
      m0.dmem.get? (bAt m0 + BitVec.ofNat 64 i) := fun i hi ↦ by
  have c := ctx_of h
  obtain ⟨-, hbnw, hbs⟩ := bOk h
  have hin : NativeRustcVm.InRange (bAt m0) (16 * nB m0) (off (bAt m0) i) :=
    inRange_off_self hi (by unfold NativeRustcVm.NoWrap at hbnw; omega)
  refine hf.same _ fun hq ↦ ?_
  rcases hq with hq | hq
  · rcases hO _ hq with hq | hq
    · exact not_inRange_of_apart (pre_parts h).2.2.2.2.2.2.2.2.2.2.2.2 hbnw c.fp.1.2 hin hq
    · exact not_inRange_of_apart (Apart.symm' (pre_parts h).2.2.2.2.2.2.2.2.2.2.1) hbnw
        (pOk h).2.1 hin hq
  · exact not_inRange_of_apart hbs hbnw c.noWrap_stack hin (inRange_mono hq (by omega))

/-- A byte of the point's first `n` is not one of the frame's. -/
theorem pt_not_frame (h : BytecodeSharePre a s0 m0) {n : Nat} (hn : n ≤ ptBytes) {jj : Nat}
    (hjj : jj < 440) : ¬ NativeRustcVm.InRange (pAt m0) n (off (fa m0) jj) := fun hq ↦ by
  have hfnw := (ctx_of h).noWrap_frame
  unfold NativeRustcVm.NoWrap at hfnw
  exact not_frame h (.inr (.inr (inRange_mono hq hn))) (inRange_off_self hjj (by omega))

/-- A byte of a part of the point is one of the point's. -/
theorem pt_sub (h : BytecodeSharePre a s0 m0) {o l : Nat} (hol : o + l ≤ ptBytes) {q : BitVec 64}
    (hq : NativeRustcVm.InRange (off (pAt m0) o) l q) : NativeRustcVm.InRange (pAt m0) ptBytes q :=
  inRange_of_off (pOk h).2.1 hol hq

/-- `Cp` through a block that writes nothing and keeps the registers. -/
theorem Cp.ofRun (h : BytecodeSharePre a s0 m0) {j : Nat} {st st' : MachineData} {ret : BitVec 64}
    {S : SState} (hc : Cp m0 m v0 j st) (hm : Match (envB m0 st ret) S st')
    (hmid : MidOk 432 8 slots S = true) (hmem : S.mem = [])
    (hk : KeepsB S (.rax :: .rcx :: six) = true) : Cp m0 m v0 j st' := by
  have hwf := wf_envB h hc.fr.frame.kept ret
  have hd : st'.dmem = st.dmem := hm.dmem_eq hwf hmem
  refine ⟨(BF.block h hc.fr hm hmid (KeepsB.mono hk (by simp [six]))).1,
    (hm.regs .r15 _ (KeepsB.reg hk (by simp [six]))).trans hc.r15,
    (hm.regs .rax _ (KeepsB.reg hk (by simp [six]))).trans hc.rax,
    (hm.regs .rcx _ (KeepsB.reg hk (by simp [six]))).trans hc.rcx, hc.le,
    fun i hi ↦ by rw [hd]; exact hc.cpy i hi, fun q hq ↦ by rw [hd]; exact hc.same q hq,
    by rw [hd]; exact hc.kept⟩

end

variable [Host] {a : DecArea} {s0 s3 : TState} {m0 m : MachineData} {k : Nat} {v0 : BitVec 64}

/-- **`b21` and the epilogue**: the slot point after the copied elements, the result. -/
theorem finish (hp : Placed code k) (h : BytecodeSharePre a s0 m0) {st : MachineData}
    {sh v : EW} {sp : Array EW} (hcp : Cp m0 m v.c0.toBitVec (nB m0) st)
    (w120 : NativeRustcVm.WordAt m.dmem (off (fa m0) 120) sh.c0)
    (w112 : NativeRustcVm.WordAt m.dmem (off (fa m0) 112) sh.c1)
    (w24 : NativeRustcVm.WordAt m.dmem (off (fa m0) 24) v.c1)
    (hsp : NativeRustcVm.EWsAt m.dmem (off (fa m0) 32) sp.toList) (hsz : sp.size = 4)
    (hts : TStateAt m.dmem (tAt m0) a s3)
    (hr : res s0 m0 = some ((sh, slice m0 (bAt m0) (reg m0 .r8) ++ sp, v), s3)) :
    Eventually (step1 Host.exe) (Goal a s0 m0) ⟨st, Host.addrOf (k + NativeRustcVmX64.Vm.BytecodeShare.b21Offset)⟩ := by
  have c := ctx_of h
  have hlen := nB_le h
  have ho := oOk h
  have hpo := pOk h
  have hpnw : (pAt m0).toNat + 1072 ≤ 2 ^ 64 := hpo.2.1
  have hfnw := c.noWrap_frame
  unfold NativeRustcVm.NoWrap at hfnw
  -- the frame's words at `st`
  have kf : ∀ {bs : List UInt8} {jj : Nat}, jj + bs.length ≤ 440 →
      NativeRustcVm.BytesAt m.dmem (off (fa m0) jj) bs →
      NativeRustcVm.BytesAt st.dmem (off (fa m0) jj) bs := fun hjj hb ↦
    NativeRustcVm.BytesAt.of_sameOutside hb hcp.same fun i hi ↦ by
      rw [off_add]; exact pt_not_frame h (by unfold ptBytes sharePointSlots busPointCap; omega)
        (by omega)
  have w120' := kf (bs := NativeRustcVm.wordBytes sh.c0) (by simp [NativeRustcVm.length_wordBytes]) w120
  have w112' := kf (bs := NativeRustcVm.wordBytes sh.c1) (by simp [NativeRustcVm.length_wordBytes]) w112
  have w24' := kf (bs := NativeRustcVm.wordBytes v.c1) (by simp [NativeRustcVm.length_wordBytes]) w24
  obtain ⟨hmT, hnT, hT⟩ := sub_ok (d := st.dmem) (o := 16 * nB m0) (l := 64)
    (Mapped.keeps hpo.1 hcp.fr.frame.kept) hpo.2.1 (by unfold ptBytes sharePointSlots busPointCap; omega)
    (by omega)
  let env := frameEnv m0 st 432 [(oAt m0, 48), (off (pAt m0) (16 * nB m0), 64)] (fun _ ↦ 0) 0
  have hwf : env.WF :=
    frame_wf ⟨c.mapped_frame hcp.fr.frame.kept, c.noWrap_frame⟩
      (rest2_ok (x := (oAt m0, 48)) (y := (off (pAt m0) (16 * nB m0), 64))
        ⟨Mapped.keeps ho.1 hcp.fr.frame.kept, ho.2.1⟩ ⟨hmT, hnT⟩ (fun _ h ↦ h))
      (pairwise3 (Apart.symm' (apart_frame ho.2.2.2.2.1 c.spN N_ge))
        (Apart.symm' (apart_sub (apart_frame hpo.2.2.2.2.1 c.spN N_ge) hpo.2.1
          (by unfold ptBytes sharePointSlots busPointCap; omega) (by omega)))
        (Apart.symm' (apart_sub (Apart.symm' (pre_parts h).2.2.2.2.2.2.2.2.2.1) hpo.2.1
          (by unfold ptBytes sharePointSlots busPointCap; omega) (by omega))))
  have hm : Match env endS st :=
    match_ofMachine ⟨rfl, rfl, rfl, trivial⟩
      ⟨hcp.fr.frame.rsp_eval, known_ptr rfl hcp.fr.rbx, known_ptr rfl hcp.rcx, trivial⟩
      trivial trivial trivial
  refine exec_then (infix_of b21_in_code (by simp [b21]) hp) exit_b21 hwf nofun hm
    fun st' hm' hpc ↦ ?_
  obtain ⟨hmid, hk, hrbx, hW0, hW8, hW16, hW24, hW32, hW40, hcp8, hws⟩ := ok_b21
  have hs : NativeRustcVm.SameOutside st.dmem st'.data.dmem (fun q ↦
      NativeRustcVm.InRange (oAt m0) 48 q ∨
        NativeRustcVm.InRange (off (pAt m0) (16 * nB m0)) 64 q) := fun q hq ↦
    hm'.get?_mem0 hwf fun ⟨w, hw, b, sz, hb, h1, h2⟩ ↦ hq (by
      rcases hws w hw with ⟨hr, hle⟩ | ⟨hr, hle⟩
      · rw [hr] at hb; cases hb
        left; rw [inRange_iff' ho.2.1]; omega
      · rw [hr] at hb; cases hb
        right; rw [inRange_iff' hnT]; omega)
  have hf' : BF m0 (OA m0) 8 st'.data :=
    ⟨Frame.of_block hcp.fr.frame hwf hm' hmid slots_le,
      NativeRustcVm.SameOutside.mono (hcp.fr.same.trans hs) fun q hq ↦ by
        rcases hq with (hq | hq) | hq | hq
        · exact .inl (.inr hq)
        · exact .inr hq
        · exact .inl (.inl hq)
        · exact .inl (.inr (.inr (pt_sub h (by unfold ptBytes sharePointSlots busPointCap; omega)
            hq))),
      (hm'.regs .rbx _ hrbx).trans (eval_ptr rfl),
      (hm'.regs .rbp _ (KeepsB.reg hk (by simp))).trans hcp.fr.rbp,
      (hm'.regs .r12 _ (KeepsB.reg hk (by simp))).trans hcp.fr.r12,
      (hm'.regs .r13 _ (KeepsB.reg hk (by simp))).trans hcp.fr.r13,
      (hm'.regs .r14 _ (KeepsB.reg hk (by simp))).trans hcp.fr.r14⟩
  -- the output's words
  have o0 := wordAt_written hm' (r := 1) (o := 0) rfl (by omega) hW0 (w := 1) rfl
  have o8 := wordAt_written hm' (r := 1) (o := 8) rfl (by omega) hW8 (w := sh.c0)
    (load_ofMachine (o := 120) rfl w120')
  have o16 := wordAt_written hm' (r := 1) (o := 16) rfl (by omega) hW16 (w := sh.c1)
    (load_ofMachine (o := 112) rfl w112')
  have o24 := wordAt_written hm' (r := 1) (o := 24) rfl (by omega) hW24
    (w := ((slice m0 (bAt m0) (reg m0 .r8) ++ sp).size.toUInt64)) (by
      show reg st .rax = _
      rw [hcp.rax, Array.size_append, hsz,
        show (slice m0 (bAt m0) (reg m0 .r8)).size = (reg m0 .r8).toNat by simp [slice], size4])
  have o32 := wordAt_written hm' (r := 1) (o := 32) rfl (by omega) hW32 (w := v.c0) hcp.r15
  have o40 := wordAt_written hm' (r := 1) (o := 40) rfl (by omega) hW40 (w := v.c1)
    (load_ofMachine (o := 24) rfl w24')
  -- the slot point's copy
  have hcpy := copied_words hm' (rd := 2) (rr := 0) (od := 0) (os := 32) (nw := 8) rfl rfl
    (by omega) (mapped_off (c.mapped_frame hcp.fr.frame.kept) (by omega)) hcp8
  have hk' : Kept m.dmem st'.data.dmem := kept_trans hcp.kept (hm'.kept hwf)
  have hblL : (slice m0 (bAt m0) (reg m0 .r8)).toList.length = nB m0 := by simp [slice]
  simp only [PcOk] at hpc
  rw [hp.label NativeRustcVmX64.Vm.BytecodeShare.label_15_at] at hpc
  obtain ⟨d', pc⟩ := st'
  simp only at hpc
  subst hpc
  refine exit16 hp h hf' ?_ fun x s' hx ↦ ?_
  · rw [hr]
    simp only [Option.map_some, OptShareAt]
    rw [off_zero] at o0
    refine ⟨o0, ewAt_iff.mpr ⟨o8, by rw [off_off]; exact o16⟩, o24,
      ewAt_iff.mpr ⟨o32, by rw [off_off]; exact o40⟩⟩
  · rw [hr] at hx
    simp only [Option.some.injEq, Prod.mk.injEq] at hx
    obtain ⟨rfl, rfl⟩ := hx
    refine ⟨?_, ?_⟩
    · show NativeRustcVm.EWsAt _ (pAt m0) (slice m0 (bAt m0) (reg m0 .r8) ++ sp).toList
      rw [Array.toList_append]
      refine NativeRustcVm.ewsAt_append_iff.mpr ⟨?_, ?_⟩
      · refine ewsAt_transfer (a := bAt m0) (fun i hi ↦ ?_)
          (NativeRustcVm.ewsAt_of_mapped (d := m0.dmem) (bOk h).1)
        have hi' : i < 16 * nB m0 := hblL ▸ hi
        rw [hs _ fun hq ↦ ?_, hcp.cpy i hi']
        rcases hq with hq | hq
        · exact not_inRange_of_apart (Apart.symm' (pre_parts h).2.2.2.2.2.2.2.2.2.1) hpo.2.1 ho.2.1
            (inRange_off_self (N := ptBytes) (by unfold ptBytes sharePointSlots busPointCap; omega)
              (by unfold ptBytes sharePointSlots busPointCap; omega)) hq
        · exact not_inRange_off hpo.2.1 (by unfold ptBytes sharePointSlots busPointCap; omega)
            hi' hq
      · rw [hblL]
        refine ewsAt_transfer (a := off (fa m0) 32) (fun i hi ↦ ?_) hsp
        rw [Array.length_toList, hsz] at hi
        have e := hcpy i (by omega)
        rw [Nat.zero_add] at e
        rw [show off (pAt m0) (16 * nB m0) + BitVec.ofNat 64 i = off (off (pAt m0) (16 * nB m0)) i
          from rfl, e, off_add]
        exact hcp.same _ (pt_not_frame h (by unfold ptBytes sharePointSlots busPointCap; omega)
          (by omega))
    · refine tstate_keep h (hcp.same.trans hs) hk' (fun q hq ↦ ?_) hts
      rcases hq with hq | hq | hq
      · exact .inl (inRange_mono hq (by unfold ptBytes sharePointSlots busPointCap; omega))
      · exact .inr (.inl hq)
      · exact .inl (pt_sub h (by unfold ptBytes sharePointSlots busPointCap; omega) hq)

/-- The pair loop's head `NativeRustcVmX64.Vm.BytecodeShare.label_13`, `j` elements copied. -/
structure PH (m0 m : MachineData) (v0 : BitVec 64) (j : Nat) (st : MachineData) : Prop where
  cp : Cp m0 m v0 j st
  even : j % 2 = 0
  lt : j + 2 ≤ nB m0 - nB m0 % 2
  rsi : (reg st .rsi).toNat = nB m0 - nB m0 % 2
  rdx : reg st .rdx = BitVec.ofNat 64 j
  rdi : reg st .rdi = BitVec.ofNat 64 (16 * j + 24)

/-- What `b21` needs: every element copied. -/
abbrev Fin' (a : DecArea) (s0 : TState) (m0 m : MachineData) (v0 : BitVec 64) (k : Nat) : Prop :=
  ∀ st, Cp m0 m v0 (nB m0) st →
    Eventually (step1 Host.exe) (Goal a s0 m0) ⟨st, Host.addrOf (k + NativeRustcVmX64.Vm.BytecodeShare.b21Offset)⟩

/-- **The odd element** (`NativeRustcVmX64.Vm.BytecodeShare.label_10`, `b20`). -/
theorem odd (hp : Placed code k) (h : BytecodeSharePre a s0 m0) (F : Fin' a s0 m0 m v0 k)
    {j : Nat} {st : MachineData} (hc : Cp m0 m v0 j st) (hdx : reg st .rdx = BitVec.ofNat 64 j)
    (hj : j + 1 = nB m0) :
    Eventually (step1 Host.exe) (Goal a s0 m0) ⟨st, Host.addrOf (k + NativeRustcVmX64.Vm.BytecodeShare.b20Offset)⟩ := by
  have c := ctx_of h
  have hlen := nB_le h
  obtain ⟨hbm, hbnw, hbs⟩ := bOk h
  have hpo := pOk h
  have hfnw := c.noWrap_frame
  unfold NativeRustcVm.NoWrap at hfnw
  obtain ⟨hmB, hnB, hB⟩ := sub_ok (d := st.dmem) (o := 16 * j) (l := 16)
    (Mapped.keeps hbm hc.fr.frame.kept) hbnw (by omega) (by omega)
  obtain ⟨hmP, hnP, hP⟩ := sub_ok (d := st.dmem) (o := 16 * j) (l := 16)
    (Mapped.keeps hpo.1 hc.fr.frame.kept) hpo.2.1
    (by unfold ptBytes sharePointSlots busPointCap; omega) (by omega)
  let env := frameEnv m0 st 432 [(off (bAt m0) (16 * j), 16), (off (pAt m0) (16 * j), 16)]
    (fun _ ↦ 0) 0
  have hwf : env.WF :=
    frame_wf ⟨c.mapped_frame hc.fr.frame.kept, c.noWrap_frame⟩
      (rest2_ok (x := (off (bAt m0) (16 * j), 16)) (y := (off (pAt m0) (16 * j), 16))
        ⟨hmB, hnB⟩ ⟨hmP, hnP⟩ (fun _ h ↦ h))
      (pairwise3 (Apart.symm' (apart_sub (apart_frame hbs c.spN N_ge) hbnw (by omega) (by omega)))
        (Apart.symm' (apart_sub (apart_frame hpo.2.2.2.2.1 c.spN N_ge) hpo.2.1
          (by unfold ptBytes sharePointSlots busPointCap; omega) (by omega)))
        (apart_sub2 (Apart.symm' (pre_parts h).2.2.2.2.2.2.2.2.2.2.1) hbnw hpo.2.1 (by omega)
          (by omega) (by unfold ptBytes sharePointSlots busPointCap; omega) (by omega)))
  have hshl : BinOp.apply .shl .W64 (reg st .rdx) (BitVec.ofNat 64 4) =
      BitVec.ofNat 64 (16 * j) := by
    rw [hdx, shl4 _ (by rw [BitVec.toNat_ofNat]; omega), BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (by omega)]
  have hm : Match env oneS st :=
    match_ofMachine ⟨rfl, rfl, rfl, trivial⟩ ⟨hc.fr.frame.rsp_eval, trivial⟩ trivial trivial
      ⟨by
        show BinOp.apply .add .W64 (reg st .r13)
          (BinOp.apply .shl .W64 (reg st .rdx) (BitVec.ofNat 64 4)) = _
        rw [hshl, add64, hc.fr.r13, ofInt_zero64, BitVec.add_zero]
        rfl,
       by
        show BinOp.apply .add .W64 (reg st .r12)
          (BinOp.apply .shl .W64 (reg st .rdx) (BitVec.ofNat 64 4)) = _
        rw [hshl, add64, hc.fr.r12, ofInt_zero64, BitVec.add_zero]
        rfl, trivial⟩
  refine exec_then (infix_of b20_in_code (by simp [b20]) hp) exit_b20 hwf nofun hm
    fun st' hm' hpc ↦ ?_
  obtain ⟨hmid, hk, hcp2, hws⟩ := ok_b20
  have hs : NativeRustcVm.SameOutside st.dmem st'.data.dmem
      (NativeRustcVm.InRange (off (pAt m0) (16 * j)) 16) := fun q hq ↦
    hm'.get?_mem0 hwf fun ⟨w, hw, b, sz, hb, h1, h2⟩ ↦ hq (by
      obtain ⟨hr, hle⟩ := hws w hw
      rw [hr] at hb; cases hb
      rw [inRange_iff' hnP]; omega)
  have hcpy := copied_words hm' (rd := 2) (rr := 1) (od := 0) (os := 0) (nw := 2) rfl rfl
    (by omega) (by rw [off_zero]; exact hmB) hcp2
  have hbk := b_kept h (fun _ h ↦ h) hc.fr
  have hc2 : Cp m0 m v0 (j + 1) st'.data := by
    refine ⟨⟨Frame.of_block hc.fr.frame hwf hm' hmid slots_le,
        NativeRustcVm.SameOutside.mono (hc.fr.same.trans hs) fun q hq ↦ by
          rcases hq with hq | hq
          · exact hq
          · exact .inl (.inr (pt_sub h (by unfold ptBytes sharePointSlots busPointCap; omega) hq)),
        (hm'.regs .rbx _ (KeepsB.reg hk (by simp [six]))).trans hc.fr.rbx,
        (hm'.regs .rbp _ (KeepsB.reg hk (by simp [six]))).trans hc.fr.rbp,
        (hm'.regs .r12 _ (KeepsB.reg hk (by simp [six]))).trans hc.fr.r12,
        (hm'.regs .r13 _ (KeepsB.reg hk (by simp [six]))).trans hc.fr.r13,
        (hm'.regs .r14 _ (KeepsB.reg hk (by simp [six]))).trans hc.fr.r14⟩,
      (hm'.regs .r15 _ (KeepsB.reg hk (by simp [six]))).trans hc.r15,
      (hm'.regs .rax _ (KeepsB.reg hk (by simp [six]))).trans hc.rax,
      (hm'.regs .rcx _ (KeepsB.reg hk (by simp [six]))).trans hc.rcx, by omega, fun i hi ↦ ?_,
      fun q hq ↦ ?_, kept_trans hc.kept (hm'.kept hwf)⟩
    · rcases Nat.lt_or_ge i (16 * j) with hi' | hi'
      · rw [hs _ (not_inRange_off hpo.2.1 (by unfold ptBytes sharePointSlots busPointCap; omega)
          hi'), hc.cpy i hi']
      · have e := hcpy (i - 16 * j) (by omega)
        simp only [Nat.zero_add, off_off] at e
        rw [show 16 * j + (i - 16 * j) = i by omega] at e
        rw [show pAt m0 + BitVec.ofNat 64 i = off (pAt m0) i from rfl, e]
        exact hbk i (by omega)
    · have h1 : ¬ NativeRustcVm.InRange (off (pAt m0) (16 * j)) 16 q := fun h' ↦
        hq (by
          rw [show 16 * (j + 1) = 16 * j + 16 by omega]
          exact inRange_join hpo.2.1 (by unfold ptBytes sharePointSlots busPointCap; omega) (.inr h'))
      have h2 : ¬ NativeRustcVm.InRange (pAt m0) (16 * j) q := fun h' ↦
        hq (inRange_mono h' (by omega))
      rw [hs q h1]
      exact hc.same q h2
  simp only [PcOk] at hpc
  rw [NativeRustcVmX64.Vm.BytecodeShare.b20_length] at hpc
  obtain ⟨d', pc⟩ := st'
  simp only at hpc
  subst hpc
  exact F _ (hj ▸ hc2)

end

end NativeRustcVmX64.Bus.BytecodeShare
