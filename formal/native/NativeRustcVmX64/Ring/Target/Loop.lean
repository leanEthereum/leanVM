module

public import NativeRustcVmX64.Ring.Target.Wrap
public import NativeRustcVmX64.Ring.Target.LoopExec
public import NativeRustcVmX64.Code.Vm.RingPsi.Names

/-!
# `ring_target`: the images loop (x86-64)

In the loop's layout (`rsL`: `s` region `1`), turn `i` from `H i` (`vL`: `g` in RBX's variable
`8`, `f` in R12's `10`) with the images so far at the frame's offset `256` (`LI i`): `b1` and
`ring_psi` on `s_i` (`A i`, `vA i`: `Ψ(s_i)` in RAX, RDX), `b2` its store (`turn`). `loop`: the
64 turns.
-/

namespace NativeRustcVmX64.Ring.Target

open NativeRustcX64 NativeRustcX64.Sym NativeRustcVmX64.Ring NativeVm.Model NativeRustcVm.Ring
open NativeRustcVmX64.Vm.RingTarget
open NativeRustcVmX64.Transcript (after wordAt_write)

@[expose] public section

/-- The loop's layout. -/
abbrev rsL (m0 : MachineData) : List (BitVec 64 × Nat) := [(sA m0, 1024)]

/-- Image `i`. -/
def img (m0 : MachineData) (i : Nat) : EW := (imgs m0).getD i 0

/-- The loop's values. -/
def vL (m0 : MachineData) : Nat → BitVec 64 := upd (pv0 m0) [(8, gA m0), (10, fA m0)]

/-- After `ring_psi` in turn `i`. -/
def vA (m0 : MachineData) (i : Nat) : Nat → BitVec 64 :=
  upd (pv0 m0) [(6, c0 (img m0 i)), (7, c1 (img m0 i)), (8, gA m0), (10, fA m0)]

/-- The first `i` images at the frame's offset `256`. -/
def LI (m0 : MachineData) (i : Nat) (d : MachineData) : Prop :=
  NativeRustcVm.EWsAt d.dmem (stackBelow m0 2352 + BitVec.ofNat 64 256) ((imgs m0).toList.take i)

end

public section

variable {m0 : MachineData}

theorem img_eq {i : Nat} (hi : i < 64) : img m0 i = ringPsi (sE m0 i) (gl m0) := by
  unfold img imgs sl arr
  rw [Array.getD_eq_getD_getElem?, Array.getElem?_map, List.getElem?_toArray,
    List.getElem?_eq_getElem (by rw [NativeRustcVm.length_ewsOf]; exact hi),
    NativeRustcVm.getElem_ewsOf]
  rfl

/-- Bytes apart from the stack, in a state at a call of a block of the loop: the entry's. -/
theorem keep_at [Labels] (hpre : RingTargetPre m0) {T S' : SState} {vals : Nat → BitVec 64}
    {m mc : MachineData} {ret : BitVec 64} (hB : Bnd m0 2352 NT (rsL m0) noWr T vals m)
    (hwr : S'.mem.all (writeOk 2352 ((2352 + 8) :: (rsL m0).map Prod.snd) noWr) = true)
    (hm : Match (envS m0 m 2352 (rsL m0) vals ret) S' mc) {a : BitVec 64} {n : Nat}
    (hap : Apart a n (stackBelow m0 NT) (NT + 8)) (hw : NoWrap a n) {i : Nat} (hi : i < n) :
    mc.dmem.get? (a + BitVec.ofNat 64 i) = m0.dmem.get? (a + BitVec.ofNat 64 i) := by
  have hns : ¬InRange (stackBelow m0 NT) NT (a + BitVec.ofNat 64 i) := fun h ↦
    NativeRustcVm.Apart.not_inRange_add hap hw (noWrap_stackBelow hpre.1) hi
      (inRange_le h (Nat.le_add_right _ _))
  have hno : ¬(InRange (stackBelow m0 NT) NT (a + BitVec.ofNat 64 i) ∨
      outsOf (rsL m0) noWr (a + BitVec.ofNat 64 i)) :=
    fun h ↦ h.elim hns fun ⟨_, _, hw', _⟩ ↦ by cases hw'
  rw [hm.get?_mem0 ((layL hpre).wf hB.kept) fun hW ↦ hno ((layL hpre).written hwr hW)]
  exact hB.same _ hno

theorem turn_res [Labels] (hpre : RingTargetPre m0) {T S' : SState} {vals : Nat → BitVec 64}
    {m mc m' : MachineData} {ret : BitVec 64} (hB : Bnd m0 2352 NT (rsL m0) noWr T vals m)
    (hwr : S'.mem.all (writeOk 2352 ((2352 + 8) :: (rsL m0).map Prod.snd) noWr) = true)
    (hm : Match (envS m0 m 2352 (rsL m0) vals ret) S' mc) {i : Nat} (hi : i < 64)
    (h0 : S'.reg .rdi = some (.load 1 (16 * i) 8)) (h1 : S'.reg .rsi = some (.load 1 (16 * i + 8) 8))
    (h2 : reg mc .rdx = gA m0) (hq : RingPsiPost mc m') :
    reg m' .rax = c0 (img m0 i) ∧ reg m' .rdx = c1 (img m0 i) := by
  have hs := hpre.2.1
  have hg := hpre.2.2.2.1
  have hword : ∀ o, o + 8 ≤ 1024 → (Sym.load 1 o 8).eval (envS m0 m 2352 (rsL m0) vals ret) =
      (NativeRustcVm.wordOf m0.dmem (sA m0 + BitVec.ofNat 64 o)).toBitVec := by
    intro o ho
    simp only [Sym.eval]
    rw [load_eq_wordOf, show (envS m0 m 2352 (rsL m0) vals ret).base 1 = sA m0 from rfl,
      Env.ofMachine_mem0]
    refine congrArg UInt64.toBitVec (NativeRustcVm.wordOf_congr fun j hj ↦ ?_)
    rw [NativeRustcVm.addr_add]
    refine hB.same _ fun h ↦ h.elim (fun h1 ↦ ?_) fun ⟨_, _, hw', _⟩ ↦ by cases hw'
    exact NativeRustcVm.Apart.not_inRange_add hs.2 hs.1.2 (noWrap_stackBelow hpre.1)
      (show o + j < 16 * 64 by omega) (inRange_le h1 (Nat.le_add_right _ _))
  have harg : ewArg (reg mc .rdi) (reg mc .rsi) = sE m0 i := by
    rw [regv hm h0 (hword _ (by omega)), regv hm h1 (hword _ (by omega)), ← NativeRustcVm.addr_add]
    rfl
  have hgl : arr mc (reg mc .rdx) ringWidth = gl m0 := by
    rw [h2]
    unfold gl arr
    exact congrArg List.toArray (NativeRustcVm.ewsOf_congr fun j hj ↦
      keep_at hpre hB hwr hm hg.2 hg.1.2 hj)
  have he := hq.1
  rw [harg, hgl, ← img_eq hi] at he
  rw [← he]
  exact ⟨rfl, rfl⟩

theorem take_succ_imgs {i : Nat} (hi : i < 64) :
    (imgs m0).toList.take (i + 1) = (imgs m0).toList.take i ++ [img m0 i] := by
  have hs : i < (imgs m0).toList.length := by rw [Array.length_toList, imgs_size]; exact hi
  rw [List.take_add_one, List.getElem?_eq_getElem hs, Option.toList_some]
  congr 2
  simp only [img, Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem
    (show i < (imgs m0).size by rw [imgs_size]; exact hi), Option.getD_some, Array.getElem_toList]

theorem LI_succ {i : Nat} (hi : i < 64) {d : MachineData} (h : LI m0 i d)
    (h0 : NativeRustcVm.WordAt d.dmem (NativeRustcVm.Transcript.off (stackBelow m0 2352)
      (256 + 16 * i)) (UInt64.ofBitVec (c0 (img m0 i))))
    (h1 : NativeRustcVm.WordAt d.dmem (NativeRustcVm.Transcript.off (stackBelow m0 2352)
      (264 + 16 * i)) (UInt64.ofBitVec (c1 (img m0 i)))) : LI m0 (i + 1) d := by
  unfold LI
  rw [take_succ_imgs hi, NativeRustcVm.ewsAt_append_iff, NativeRustcVm.ewsAt_singleton_iff]
  have hl : ((imgs m0).toList.take i).length = i := by
    rw [List.length_take, Array.length_toList, imgs_size]; omega
  rw [hl]
  refine ⟨h, NativeRustcVm.ewAt_iff.mpr ⟨?_, ?_⟩⟩
  · rw [NativeRustcVm.addr_add_add]
    exact h0
  · rw [NativeRustcVm.addr_add_add, NativeRustcVm.addr_add_add,
      show 256 + (16 * i + 8) = 264 + 16 * i by omega]
    exact h1

variable [Host] {k : Nat}

/-- **Turn `i`** of the images loop. -/
theorem turn (hp : Placed code k) (hpre : RingTargetPre m0)
    (hpsi : Spec (Labels.label NativeRustcVmX64.Vm.RingPsi.entryLabel) RingPsiPre RingPsiPost) {i : Nat} (hi : i < 64)
    {st : MachineState} (h : At m0 k NativeRustcVmX64.Vm.RingTarget.b1Offset (rsL m0) (H i) (vL m0) (LI m0 i) st) :
    Eventually (step1 Host.exe) (fun st' ↦
      (i < 63 ∧ At m0 k NativeRustcVmX64.Vm.RingTarget.b1Offset (rsL m0) (H (i + 1)) (vL m0) (LI m0 (i + 1)) st') ∨
      (i = 63 ∧ At m0 k NativeRustcVmX64.Vm.RingTarget.b3Offset (rsL m0) (H 64) (vL m0) (LI m0 64) st')) st := by
  have g := geoT hpre
  obtain ⟨e1, r_di, r_si, r_dx, r_sp, hL, hLW, hwr, hmiss⟩ := loop_b1 i hi
  refine Eventually.bind (cstep hp (layL hpre) b1_in_code (by simp [b1]) rfl (T' := A i)
    (vals' := vA m0 i) e1 hwr r_sp hpsi (S := ringPsiStack) (by decide) (I := LI m0 i)
    (fun m mc hB _ hm hk hs ↦ ?_) (fun _ _ hq ↦ ⟨changes0 hq.2.1, hq.2.2⟩) hL hLW
    (fun m hB ret ↦ by
      simp only [List.cons_append, List.nil_append, List.forall_mem_cons, Sym.eval, pushL]
      and_intros <;> first | rfl | exact fun _ h ↦ nomatch h)
    rfl rfl (fun m hB _ mc m' hm hq ↦ turn_res hpre hB hwr hm hi r_di r_si (regv hm r_dx rfl) hq)
    (fun m mc m' hB hI hm hsp hq ↦ bytes_callee g
      (bytes_block g ((layL hpre).wf hB.kept) hmiss (by decide) hm hI (by decide) ?_) ?_ hsp
      (by decide) (changes0 hq.2.1)) rfl rfl rfl (fun _ _ ↦ noKeys rfl) rfl h) fun st2 h2 ↦ ?_
  · have hg := hpre.2.2.2.1
    rw [show RingPsiPre mc = (StackOk mc ringPsiStack ∧ ArrOk mc (reg mc .rdx) ringWidth ringPsiStack)
      from rfl, regv hm r_dx rfl]
    have hsp : rspOf mc = stackBelow m0 2352 := by
      show mc.regs.get64 .rsp = _
      rw [hm.regs .rsp _ r_sp]
      show stackBelow m0 2352 + BitVec.ofInt 64 0 = _
      simp
    exact ⟨hs, ⟨fun j hj ↦ hk _ (hg.1.1 j hj), hg.1.2⟩,
      NativeRustcVmX64.Transcript.apart_callee hg.2 hsp hpre.1.1 (by decide)⟩
  · rw [NativeRustcVm.length_ewsBytes, List.length_take]
    rw [Array.length_toList, imgs_size]
    omega
  · rw [NativeRustcVm.length_ewsBytes, List.length_take]
    rw [Array.length_toList, imgs_size]
    omega
  -- `b2`: the image stored.
  obtain ⟨d, pc⟩ := st2
  obtain ⟨hpc, hB, hI⟩ := h2
  simp only at hpc hB hI
  subst hpc
  obtain ⟨e2, hL2, hLW2, hwr2, hmiss2⟩ := loop_b2 i hi
  refine jumpStep (layL hpre) hB (b2_in_code.trans hp.1 (by simp [b2])) e2 (fun _ h ↦ by cases h)
    hwr2 hL2 hLW2 (vals' := vL m0) (fun ret ↦ by
      simp only [List.cons_append, List.nil_append, List.forall_mem_cons, Sym.eval, pushL]
      and_intros <;> first | rfl | exact fun _ h ↦ nomatch h)
    rfl rfl rfl (fun _ _ ↦ noKeys rfl) (fun _ _ _ _ h ↦ by cases h) fun st hpc hB' hm ↦ .done _ ?_
  have hwf := (layL hpre).wf hB.kept (vals := vA m0 i) (ret := 0)
  have hpre' : LI m0 i st.data :=
    bytes_block g hwf hmiss2 (by omega) hm hI (by decide) (by
      rw [NativeRustcVm.length_ewsBytes, List.length_take, Array.length_toList, imgs_size]; omega)
  have hw0 := wordAt_write hm (r := 0) (o := 256 + 16 * i) rfl (by omega)
    fun t ht ↦ (loop_b2w i hi t ht).1
  have hw1 := wordAt_write hm (r := 0) (o := 264 + 16 * i) rfl (by omega)
    fun t ht ↦ (loop_b2w i hi t ht).2
  have hnew : LI m0 (i + 1) st.data := LI_succ hi hpre' hw0 hw1
  have hc : (SBool.lit (decide (i < 63))).eval (envS m0 d 2352 [(sA m0, 1024)] (vA m0 i) 0) =
      decide (i < 63) := rfl
  simp only [PcOk, hc] at hpc
  by_cases h63 : i < 63
  · refine .inl ⟨h63, ?_, hB', hnew⟩
    rw [hpc, ite_eq_left (decide_eq_true h63)]
    exact hp.label NativeRustcVmX64.Vm.RingTarget.label_1_at
  · have : i = 63 := by omega
    subst this
    exact .inr ⟨rfl, hpc.trans rfl, hB', hnew⟩

/-- **The images loop**, from turn `i`. -/
theorem loop (hp : Placed code k) (hpre : RingTargetPre m0)
    (hpsi : Spec (Labels.label NativeRustcVmX64.Vm.RingPsi.entryLabel) RingPsiPre RingPsiPost) :
    ∀ n i, i + n = 63 → ∀ {st : MachineState}, At m0 k NativeRustcVmX64.Vm.RingTarget.b1Offset (rsL m0) (H i) (vL m0) (LI m0 i) st →
      Eventually (step1 Host.exe) (At m0 k NativeRustcVmX64.Vm.RingTarget.b3Offset (rsL m0) (H 64) (vL m0) (LI m0 64)) st := by
  intro n
  induction n with
  | zero =>
    intro i hi st h
    refine Eventually.mono (turn hp hpre hpsi (by omega) h) fun st' hs ↦ ?_
    rcases hs with ⟨hlt, -⟩ | ⟨-, hl⟩
    · omega
    · exact hl
  | succ n ih =>
    intro i hi st h
    refine Eventually.bind (turn hp hpre hpsi (by omega) h) fun st' hs ↦ ?_
    rcases hs with ⟨-, h'⟩ | ⟨h63, -⟩
    · exact ih (i + 1) (by omega) h'
    · omega

end

end NativeRustcVmX64.Ring.Target
