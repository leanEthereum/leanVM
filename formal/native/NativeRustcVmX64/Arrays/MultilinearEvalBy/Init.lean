module

public import NativeRustcVmX64.Arrays.MultilinearEvalBy.Loops

/-!
# `multilinear_eval_by`: the prologue and the set-up, for both instances (x86-64)

`entry_zinv`: the prologue (pushes, `point` stored at `56`, RAX zeroed) makes the zeroing loop's
head. `init_body`, `init_outer`: the set-up (the flags zeroed, the arguments stored) keeps the
body and, with entries and levels, makes the outer loop's head with nothing streamed.
`zero_end`: a block zeroing the value reaches the epilogue with `0`.
-/

namespace NativeRustcVmX64.Arrays.MleFrame

open NativeRustcX64 NativeRustcX64.Sym NativeVm.Model NativeRustcVmX64.Field
open NativeRustcVm (wordOf ewOf ewsOf)
open NativeRustcVm.Mle (setP stream cont)

@[expose] public section

/-- The prologue: RSP at `8`, the pushed registers in their slots, writes in the frame, `point`
at `56`, the arguments' registers kept. -/
abbrev EntryOk (S : SState) : Prop :=
  S.reg .rsp = some (.ptr 0 8) ∧
    (∀ p ∈ mleSlots, p.1 + 8 ≤ 1216 ∧ ∀ i < 8, findWrite 0 (p.1 + i) S.mem = some (.reg p.2, i)) ∧
    (∀ w ∈ S.mem, w.r = 0 ∧ w.off + w.n ≤ 1216) ∧
    (∀ i < 8, findWrite 0 (56 + i) S.mem = some (.reg .rcx, i)) ∧
    (∀ r ∈ [Reg64.rdi, .rsi, .rdx, .rcx, .r8], S.reg r = some (.reg r))

/-- The set-up's writes: between `16` and `56`, or among the flags; RSP kept. -/
abbrev InitOk (S : SState) : Prop :=
  (∀ w ∈ S.mem, w.r = 0 ∧ ((16 ≤ w.off ∧ w.off + w.n ≤ 56) ∨ (80 ≤ w.off ∧ w.off + w.n ≤ 144))) ∧
    S.reg .rsp = some (.ptr 0 8)

/-- The set-up's words: the flags zeroed, the arguments and `i = 0` stored. -/
abbrev MleArgsOk (S : SState) : Prop :=
  (∀ k < 64, findWrite 0 (80 + k) S.mem = some (.lit 0, k % 8)) ∧
    (∀ i < 8, findWrite 0 (16 + i) S.mem = some (.lit 0, i)) ∧
    (∀ i < 8, findWrite 0 (24 + i) S.mem = some (.reg .rsi, i)) ∧
    (∀ i < 8, findWrite 0 (32 + i) S.mem = some (.reg .rdi, i)) ∧
    (∀ i < 8, findWrite 0 (40 + i) S.mem = some (.reg .rdx, i)) ∧
    (∀ i < 8, findWrite 0 (48 + i) S.mem = some (.bin .shl .W64 (.reg .r8) (.lit 4), i))

/-- A block zeroing the value, RSP kept, no writes. -/
abbrev ZeroValOk (R : Regs) (S : SState) : Prop :=
  S.mem = [] ∧ keepsRegs regsS S [.rsp] = true ∧ S.reg R.vlo = some (.lit 0) ∧
    S.reg R.vhi = some (.lit 0)

/-- The facts the zeroing loop keeps, at its exit. -/
structure AfterZero (m0 s : MachineData) : Prop where
  body : Body m0 1216 mleStack mleSlots 0 0 s
  w56 : ValsAt s.dmem (fbOf m0) [(56, reg m0 .rcx)]
  regs : ∀ r ∈ [Reg64.rdi, .rsi, .rdx, .rcx, .r8], reg s r = reg m0 r

end

public section

/-- **The prologue** makes the zeroing loop's head. -/
theorem entry_zinv [Labels] {m0 st : MachineData} {S : SState} (hS : StackOk m0 mleStack)
    (hm : Match (frameEnv m0 m0 1216) S st) (hc : EntryOk S) (hax : S.reg .rax = some (.lit 0)) :
    ZInv m0 0 st := by
  obtain ⟨hsp, hw, hmem, h56, hregs⟩ := hc
  refine ⟨Body.of_entry hS (by decide) hm hsp hw (by rw [freeRegs_mleSlots]; nofun) hmem,
    val_of_write hm (r := 0) rfl (by omega) h56, fun r hr ↦ hm.regs r _ (hregs r hr), ?_,
    by omega⟩
  show st.regs.get64 .rax = _
  rw [hm.regs .rax _ hax]
  rfl

/-- The body after the prologue. -/
theorem entry_body [Labels] {m0 st : MachineData} {S : SState} (hS : StackOk m0 mleStack)
    (hm : Match (frameEnv m0 m0 1216) S st) (hc : EntryOk S) :
    Body m0 1216 mleStack mleSlots 0 0 st :=
  Body.of_entry hS (by decide) hm hc.1 hc.2.1 (by rw [freeRegs_mleSlots]; nofun) hc.2.2.1

/-- **The set-up keeps the body.** -/
theorem init_body [Labels] {m0 s st : MachineData} {S : SState} (hS : StackOk m0 mleStack)
    (hb : Body m0 1216 mleStack mleSlots 0 0 s) (hm : Match (frameEnv m0 s 1216) S st)
    (hc : InitOk S) : Body m0 1216 mleStack mleSlots 0 0 st := by
  have hwf := hb.wf (vars := fun _ ↦ 0) (ret := 0) hS (by decide)
  refine body_of_local hb hS hm hwf rfl
    (Match.reg_eq hb.mid_match hm (show (midS 1216).reg .rsp = some (.ptr 0 8) from rfl) hc.2)
    fun p hp ↦ ?_
  obtain ⟨w, hw', b, sz, hb', hlo, hhi⟩ := written_bounds hp
  obtain ⟨hr, hw⟩ := hc.1 w hw'
  rw [hr] at hb'
  simp only [Env.ofMachine_regions, List.getElem?_cons_zero, Option.some.injEq,
    Prod.mk.injEq] at hb'
  obtain ⟨rfl, rfl⟩ := hb'
  have := fb_toNat hS
  have : (stackBelow m0 1216).toNat = (rspOf m0).toNat - 1216 := (fb_toNat hS).1
  exact frame_addr hS (lo := 16) (hi := 1168) (by omega) (by omega) (by omega)

/-- `16 |point|` as `shl $4`. -/
theorem shl4_eq (x : BitVec 64) : x <<< 4 = BitVec.ofNat 64 (16 * x.toNat) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.shiftLeft_eq]
  omega

/-- **The set-up** makes the outer loop's head with nothing streamed. -/
theorem init_outer [Labels] {es : List EW} {m0 s st : MachineData} {S : SState}
    (hS : StackOk m0 mleStack) (hZ : AfterZero m0 s) (hm : Match (frameEnv m0 s 1216) S st)
    (hc : InitOk S) (ha : MleArgsOk S) (hn : 0 < nn m0) (hpos : 0 < mm m0) (hlt : mm m0 < 64) :
    Outer es m0 0 st := by
  obtain ⟨hfl, h16, h24, h32, h40, h48⟩ := ha
  have hwf := hZ.body.wf (vars := fun _ ↦ 0) (ret := 0) hS (by decide)
  have bd := init_body hS hZ.body hm hc
  have hvals : ∀ {o : Nat} {v : Sym}, o + 8 ≤ 1224 →
      (∀ i < 8, findWrite 0 (o + i) S.mem = some (v, i)) →
      ValsAt st.dmem (fbOf m0) [(o, v.eval (frameEnv m0 s 1216))] := fun ho hv ↦
    val_of_write hm (r := 0) rfl ho hv
  have hreg : ∀ r ∈ [Reg64.rdi, .rsi, .rdx, .rcx, .r8],
      (Sym.reg r).eval (frameEnv m0 s 1216) = reg m0 r := fun r hr ↦ hZ.regs r hr
  have h56 : ValsAt st.dmem (fbOf m0) [(56, reg m0 .rcx)] :=
    vals_congr hZ.w56 fun p hp j hj ↦ by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
      subst hp
      dsimp only
      refine hm.get?_mem0 hwf fun h ↦ ?_
      obtain ⟨w, hw', b, sz, hb', hlo, hhi⟩ := written_bounds h
      obtain ⟨hr, hw⟩ := hc.1 w hw'
      rw [hr] at hb'
      simp only [Env.ofMachine_regions, List.getElem?_cons_zero, Option.some.injEq,
        Prod.mk.injEq] at hb'
      obtain ⟨rfl, rfl⟩ := hb'
      have := fb_toNat hS
      have : (stackBelow m0 1216).toNat = (rspOf m0).toNat - 1216 := (fb_toNat hS).1
      have e := fb_add_toNat hS (o := 56 + j) (by omega)
      omega
  have h48v : (Sym.bin .shl .W64 (.reg .r8) (.lit 4)).eval (frameEnv m0 s 1216) =
      BitVec.ofNat 64 (16 * mm m0) := by
    rw [eval_shl_lit _ (by decide), hreg .r8 (by simp)]
    exact shl4_eq _
  have hargs : ValsAt st.dmem (fbOf m0) (argVals m0) := by
    have a24 := hvals (by omega) h24
    have a32 := hvals (by omega) h32
    have a40 := hvals (by omega) h40
    have a48 := hvals (by omega) h48
    rw [hreg .rsi (by simp)] at a24
    rw [hreg .rdi (by simp)] at a32
    rw [hreg .rdx (by simp)] at a40
    rw [h48v] at a48
    rw [vals_cons] at a24 a32 a40 a48 h56
    unfold argVals
    simp only [vals_cons]
    exact ⟨a24.1, a32.1, a40.1, a48.1, h56.1, vals_nil _ _⟩
  have hflags : ∀ k < 64, st.dmem.get? (fbOf m0 + BitVec.ofNat 64 (80 + k)) = some 0 := by
    intro k hk
    have := hm.mem 0 (fbOf m0) 1224 rfl (80 + k) (by omega)
    rw [this]
    unfold memByte
    rw [hfl k hk]
    simp [Sym.eval, byteOf]
  refine ⟨⟨bd, hargs, fun k hk ↦ .inl (hflags k hk)⟩, hn, hpos, hlt, ?_, ?_⟩
  · have := hvals (by omega) h16
    exact this
  · rw [pendOf_zero hflags, List.drop_zero]

/-- **A block that writes nothing** keeps the outer loop's head. -/
theorem Outer.of_keeps [Labels] {es : List EW} {m0 st st' : MachineData} {i : Nat} {env : Env}
    {S₀ S₁ : SState} {rs : List Reg64} (hO : Outer es m0 i st) (hS : StackOk m0 mleStack)
    (hm₀ : Match env S₀ st) (hm : Match env S₁ st') (hwf : env.WF) (hd : env.mem0 = st.dmem)
    (hk : keepsAll S₀ S₁ rs = true) : Outer es m0 i st' ∧ ∀ r ∈ rs, reg st' r = reg st r := by
  obtain ⟨bd, hdm, hr⟩ := body_of_keeps hO.fr.body hS hm₀ hm hwf hd hk
  refine ⟨⟨⟨bd, ?_, ?_⟩, hO.hi, hO.pos, hO.lt, ?_, ?_⟩, hr⟩
  · rw [hdm]; exact hO.fr.args
  · rw [hdm]; exact hO.fr.flags
  · rw [hdm]; exact hO.wi
  · rw [hdm]; exact hO.val

/-- `i << 4`. -/
theorem ofNat_shl4 (i : Nat) : BitVec.ofNat 64 i <<< 4 = BitVec.ofNat 64 (16 * i) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.shiftLeft_eq]
  omega

variable [Host]

/-- **A block zeroing the value** reaches the epilogue with `0`. -/
theorem zero_end (R : Regs) {es : List EW} {m0 : MachineData} (hS : StackOk m0 mleStack)
    {ds : List Directive} {kz : Nat} {S : SState} (hk : ds.IsInfixAt Host.prog kz)
    (hx : exec ds regsS = some (S, .fall)) (hc : ZeroValOk R S) {s : MachineState}
    (hpc : s.pc = Host.addrOf kz) (hb : Body m0 1216 mleStack mleSlots 0 0 s.data)
    (h0 : stream (pts m0) es (fun _ ↦ none) = 0) :
    Eventually (step1 Host.exe)
      (fun s' ↦ s'.pc = Host.addrOf (kz + ds.length) ∧ AtEnd es R m0 s'.data) s := by
  obtain ⟨hmem, hk', hlo, hhi⟩ := hc
  refine exec_at hk hx (Env.wf_nil _) (by intro l h; cases h) hpc (match_nil _)
    fun s2 hm2 hpc2 ↦ .done _ ⟨hpc2, ?_, ?_⟩
  · exact (body_of_keeps hb hS (match_nil _) hm2 (Env.wf_nil _) rfl
      (rs := []) (by simp only [keepsAll, hmem, List.isEmpty_nil, Bool.and_true]; exact hk')).1
  · rw [h0]
    show ewArg (s2.data.regs.get64 R.vlo) (s2.data.regs.get64 R.vhi) = 0
    rw [hm2.regs R.vlo _ hlo, hm2.regs R.vhi _ hhi]
    rfl

end

end NativeRustcVmX64.Arrays.MleFrame
