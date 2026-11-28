module

public import NativeRustcVmArm.KeccakGkr.VerifyLayer.Tail
public import NativeRustcVmArm.KeccakGkr.VerifyLayer.Arith

/-!
# `verify_layer`: the layer's weights loop, its state

The loop (`b52` to `b61`) writes the layer's weights `layerWeights eq β` (`lwF`), from the local
equality kernel `eq` at the scratch's `eq` (`eqA`), into the scratch's `layer_weights`. `WMem`:
what memory holds with `j` weights written; `WHead`: the machine at the loop's head. A scratch
range as an environment's second region (`wf_s`, `Body.sBlock`).
-/

namespace NativeRustcVmArm.KeccakGkr.VerifyLayer

open NativeRustcArm NativeRustcArm.Sym NativeRustcVmArm.Ring NativeVm.Model
open NativeRustcVmArm.Vm.VerifyLayer
open NativeRustcVm (Region)
open NativeRustcVm.Layout (Same)
open NativeRustcVm.Transcript (tstateBytes TStateAt DecArea)
open NativeRustcVm.KeccakGkr (ClaimAt WeightsAt claimBytes)
open LeanVM.Protocol.Verifier (keccakAlong)

@[expose] public section

/-- The local equality kernel's address. -/
abbrev eqA (m0 : MachineData) : BitVec 64 := sA m0 + BitVec.ofNat 64 107520

/-- The layer's weight `i`. -/
def lwF (eq : Array EW) (beta : EW) (i : Nat) : EW :=
  eq.getD i 0 + beta * (eq.getD (keccakAlong i 4) 0 + beta * eq.getD (keccakAlong i 3) 0)

/-- **Memory in the loop**, `j` weights written. -/
structure WMem (m0 : MachineData) (a : DecArea) (s' : TState) (t0 t1 t2 beta : EW)
    (mu point eq : Array EW) (j : Nat) (d : DataMem) : Prop where
  fw : Bus.FrameWords d (base m0 2032) (tailWords m0 t0 t1 t2)
  f144 : NativeRustcVm.WordAt d (base m0 2032 + BitVec.ofNat 64 144) (UInt64.ofBitVec (eqA m0))
  mu : NativeRustcVm.BufEWAt d (base m0 2032 + BitVec.ofNat 64 968) 16 mu.toList
  pt : NativeRustcVm.EWsAt d (base m0 2032 + BitVec.ofNat 64 1232) point.toList
  ts : TStateAt d (tA m0) a s'
  kern : NativeRustcVm.EWsAt d (eqA m0) eq.toList
  lw : ∀ i < j, NativeRustcVm.EWAt d (sA m0 + BitVec.ofNat 64 (51200 + 16 * i)) (lwF eq beta i)

/-- **The loop's head**, `j` weights written. -/
structure WHead [Host] (k : Nat) (m0 : MachineData) (a : DecArea) (s' : TState)
    (t0 t1 t2 beta : EW) (mu point eq : Array EW) (j : Nat) (st : MachineState) : Prop where
  lt : j < 1600
  pc : st.pc = Host.addrOf (k + NativeRustcVmArm.Vm.VerifyLayer.b57Offset)
  body : Body m0 st.data
  x19 : st.data.regs.X19.toNat = j
  x26 : st.data.regs.X26.toNat = 25600 - 16 * j
  x29 : st.data.regs.X29.toBitVec = sA m0 + BitVec.ofNat 64 (51200 + 16 * j)
  x20 : st.data.regs.X20.toBitVec = sA m0 + BitVec.ofNat 64 (51208 + 16 * j)
  x23 : st.data.regs.X23 = beta.c0
  x25 : st.data.regs.X25 = beta.c1
  x24 : st.data.regs.X24.toNat = point.size
  mem : WMem m0 a s' t0 t1 t2 beta mu point eq j st.data.dmem
  f96 : NativeRustcVm.WordAt st.data.dmem (base m0 2032 + BitVec.ofNat 64 96)
    (UInt64.ofBitVec (sA m0 + BitVec.ofNat 64 (107528 + 16 * j)))

end

public section

variable {a : DecArea} {s : TState} {c : KeccakClaimW} {m0 : MachineData}

/-- **A scratch range** `n` bytes from offset `o` as an environment's second region. -/
theorem wf_s [Labels] (hpre : VerifyLayerPre a s c m0) {m : MachineData} (hb : Body m0 m)
    {o n : Nat} (hn : 0 < n) (hon : o + n ≤ 205824) :
    (Env.ofMachine m [(base m0 2032, 2032), (sA m0 + BitVec.ofNat 64 o, n)]).WF := by
  have g := geo_of hpre
  have hS := hpre.1
  obtain ⟨-, -, -, -, -, -, -, -, -, hA⟩ := hpre
  have hsok := hA.1 ⟨sA m0, NativeRustcVm.KeccakGkr.scratchBytes⟩ (by simp)
  have := g.hN; have := Geo.sp_lt m0; have hbN := g.bN; have := g.hs; have := g.hss
  have e : (sA m0 + BitVec.ofNat 64 o).toNat = (sA m0).toNat + o :=
    NativeRustcVm.toNat_add_ofNat (by omega)
  refine Env.wf_of ⟨⟨fun i hi ↦ hb.kept _ ((frame_mapped hS (by decide)) i hi),
    base_noWrap (by omega)⟩, ⟨fun i hi ↦ ?_, by unfold NoWrap; rw [e]; omega⟩, trivial⟩ ?_
  · rw [NativeRustcVm.addr_add_add]
    exact hb.kept _ (hsok.1 _ (show o + i < NativeRustcVm.KeccakGkr.scratchBytes by
      unfold NativeRustcVm.KeccakGkr.scratchBytes; omega))
  · refine List.Pairwise.cons ?_ (List.pairwise_singleton _ _)
    simp only [List.mem_singleton, forall_eq]
    unfold Apart
    rw [hbN, e]
    omega

/-- **A block writing only into the frame's locals and a range of the scratch's
`layerRegion`** (region 1) keeps the body. -/
theorem Body.sBlock [Labels] (hpre : VerifyLayerPre a s c m0) {m m' : MachineData}
    (hb : Body m0 m) {o n : Nat} (hn : 0 < n) (h1 : 25600 ≤ o) (h2 : o + n ≤ 140288) {S S' : SState}
    (hm : Match (Env.ofMachine m [(base m0 2032, 2032), (sA m0 + BitVec.ofNat 64 o, n)]) S m)
    (hm' : Match (Env.ofMachine m [(base m0 2032, 2032), (sA m0 + BitVec.ofNat 64 o, n)]) S' m')
    (hsp : S'.sp = S.sp)
    (hw : S'.mem.all (fun w ↦ (w.r == 0 && decide (w.off + w.n ≤ 1936)) ||
      (w.r == 1 && decide (w.off + w.n ≤ n))) = true) :
    Body m0 m' := by
  have g := geo_of hpre
  have := g.hN
  have hwf := wf_s hpre hb (o := o) hn (by omega)
  refine Fr.ofBlockW hb hm hm' hwf rfl hsp (fun r hr ↦ by cases hr) rfl
    (by decide) (by rw [stack_eq]; omega) (fun p hp ↦ by have := slots_bound p hp; omega)
    fun w hwm ↦ ?_
  have h := List.all_eq_true.mp hw w hwm
  simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h
  rcases h with h | h
  · exact .inl ⟨h.1, by omega, fun p hp ↦ by have := slots_bound p hp; omega⟩
  refine .inr ⟨by omega, fun b sz hb' ↦ ?_⟩
  rw [h.1] at hb'
  simp only [Env.ofMachine_regions, List.getElem?_cons_succ, List.getElem?_cons_zero,
    Option.some.injEq, Prod.mk.injEq] at hb'
  obtain ⟨rfl, rfl⟩ := hb'
  exact ⟨h.2, fun i hi ↦ in_layer g h1 h2 (NativeRustcVm.inRange_add hi (by omega))⟩

/-- **A scratch range as region 1**: the frame and `n` bytes at offset `o` match `init` with
region 1 reached by an alias `x` of value its base. -/
theorem match_sAlias [Labels] (hpre : VerifyLayerPre a s c m0) {m : MachineData} (hb : Body m0 m)
    {o n : Nat} {x : Sym} {off : Int}
    (hx : x.eval (Env.ofMachine m [(base m0 2032, 2032), (sA m0 + BitVec.ofNat 64 o, n)]) =
      sA m0 + BitVec.ofNat 64 o + BitVec.ofInt 64 off) :
    Match (Env.ofMachine m [(base m0 2032, 2032), (sA m0 + BitVec.ofNat 64 o, n)])
      (init [(2032, true), (n, false)] (.ptr 0 0) [] [] [] [(x, (1, off))]) m :=
  match_ofMachine (sregions := [(2032, true), (n, false)])
    (regions := [(base m0 2032, 2032), (sA m0 + BitVec.ofNat 64 o, n)])
    ⟨rfl, fun _ ↦ Bus.base_aligned hpre.1 (by decide) (by decide), rfl, nofun, trivial⟩
    (by simp only [Sym.eval, Env.base_ofMachine_eq, List.getElem?_cons_zero, Option.map_some,
          Option.getD_some]; rw [hb.sp]; simp)
    trivial trivial trivial ⟨hx, trivial⟩

/-- **A scratch range as region 1**, reached by registers. -/
theorem match_sRegs [Labels] (hpre : VerifyLayerPre a s c m0) {m : MachineData} (hb : Body m0 m)
    {o n : Nat} {known : List (XReg × Sym)}
    (hk : AllOf (fun p ↦ (m.regs.getXReg p.1).toBitVec =
      p.2.eval (Env.ofMachine m [(base m0 2032, 2032), (sA m0 + BitVec.ofNat 64 o, n)])) known) :
    Match (Env.ofMachine m [(base m0 2032, 2032), (sA m0 + BitVec.ofNat 64 o, n)])
      (init [(2032, true), (n, false)] (.ptr 0 0) known) m :=
  match_ofMachine (sregions := [(2032, true), (n, false)])
    (regions := [(base m0 2032, 2032), (sA m0 + BitVec.ofNat 64 o, n)])
    ⟨rfl, fun _ ↦ Bus.base_aligned hpre.1 (by decide) (by decide), rfl, nofun, trivial⟩
    (by simp only [Sym.eval, Env.base_ofMachine_eq, List.getElem?_cons_zero, Option.map_some,
          Option.getD_some]; rw [hb.sp]; simp)
    hk trivial trivial trivial

/-- **`WMem` kept by a change outside it**: the frame's words `16` to `144`, its bytes from `968`,
the `TState`, the kernel and the weights written untouched. -/
theorem WMem.keep [Labels] (hpre : VerifyLayerPre a s c m0) {s' : TState} {t0 t1 t2 beta : EW}
    {mu point eq : Array EW} {j : Nat} {d d' : DataMem} {R : BitVec 64 → Prop}
    (hps : point.size ≤ 30) (heq : eq.size = 2048) (hj : j ≤ 1600)
    (h : WMem m0 a s' t0 t1 t2 beta mu point eq j d) (hk : Kept d d') (hs : SameOutside d d' R)
    (hfr : ∀ o < 2032, (16 ≤ o ∧ o < 96 ∨ 104 ≤ o ∧ o < 152 ∨ 968 ≤ o ∧ o < 1712) →
      ¬R (base m0 2032 + BitVec.ofNat 64 o))
    (hsc : ∀ o < 205824, (51200 ≤ o ∧ o < 51200 + 16 * j ∨ 107520 ≤ o ∧ o < 140288) →
      ¬R (sA m0 + BitVec.ofNat 64 o))
    (ht : ∀ q, R q → ¬InRange (tA m0) tstateBytes q ∧ ¬InRange a.words (8 * a.len) q) :
    WMem m0 a s' t0 t1 t2 beta mu point eq j d' := by
  have g := geo_of hpre
  have := g.hs
  have hsame : ∀ {o n : Nat}, (∀ i < n, 16 ≤ o + i ∧ o + i < 96 ∨ 104 ≤ o + i ∧ o + i < 152 ∨
      968 ≤ o + i ∧ o + i < 1712) → o + n ≤ 2032 → Same d d' (base m0 2032 + BitVec.ofNat 64 o) n :=
    fun hi hon ↦ NativeRustcVm.Layout.Same.of_sameOutside hs fun i hin ↦ by
      rw [NativeRustcVm.addr_add_add]; exact hfr _ (by omega) (hi i hin)
  have hssame : ∀ {o n : Nat}, (∀ i < n, 51200 ≤ o + i ∧ o + i < 51200 + 16 * j ∨
      107520 ≤ o + i ∧ o + i < 140288) → o + n ≤ 205824 → Same d d' (sA m0 + BitVec.ofNat 64 o) n :=
    fun hi hon ↦ NativeRustcVm.Layout.Same.of_sameOutside hs fun i hin ↦ by
      rw [NativeRustcVm.addr_add_add]; exact hsc _ (by omega) (hi i hin)
  refine ⟨fun p hp ↦ ?_, ?_, ?_, ?_, ?_, ?_, fun i hi ↦ ?_⟩
  · have hp' := hp
    simp only [tailWords, List.mem_cons, List.not_mem_nil, or_false] at hp'
    refine NativeRustcVm.Layout.WordAt.of_same (h.fw p hp) (hsame (n := 8) (fun i hi ↦ ?_)
      (by rcases hp' with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp))
      (Nat.le_refl _)
    rcases hp' with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp <;> omega
  · exact NativeRustcVm.Layout.WordAt.of_same h.f144 (hsame (n := 8) (fun i hi ↦ by omega)
      (by omega)) (Nat.le_refl _)
  · exact NativeRustcVm.Layout.BufEWAt.of_same h.mu (hsame (n := 264) (fun i hi ↦ by omega)
      (by omega)) (by omega)
  · exact ewsAt_same h.pt (hsame (n := 480) (fun i hi ↦ by omega) (by omega))
      (by rw [Array.length_toList]; omega)
  · exact NativeRustcVm.Transcript.TStateAt.frame h.ts hk ht hs
  · exact ewsAt_same h.kern (hssame (n := 32768) (fun i hi ↦ by omega) (by omega))
      (by rw [Array.length_toList, heq])
  · have := h.lw i hi
    exact NativeRustcVm.Layout.EWAt.of_same this
      (hssame (n := 16) (fun i' hi' ↦ by omega) (by omega)) (Nat.le_refl _)

/-- `WMem` kept by a callee writing only its stack below the frame. -/
theorem WMem.call [Labels] (hpre : VerifyLayerPre a s c m0) {s' : TState} {t0 t1 t2 beta : EW}
    {mu point eq : Array EW} {j : Nat} {m m' : MachineData} (hb : Body m0 m)
    (hps : point.size ≤ 30) (heq : eq.size = 2048) (hj : j ≤ 1600)
    (h : WMem m0 a s' t0 t1 t2 beta mu point eq j m.dmem) (hk : Kept m.dmem m'.dmem) {n : Nat}
    (hn : n ≤ 1616)
    (hs : SameOutside m.dmem m'.dmem fun q ↦ InRange (stackBelow m n) n q ∨ False) :
    WMem m0 a s' t0 t1 t2 beta mu point eq j m'.dmem := by
  have g := geo_of hpre
  have := g.hN; have := Geo.sp_lt m0; have hbN := g.bN; have := g.hs; have := g.hss
  have hst := g.stk hb.sp hn
  refine h.keep hpre hps heq hj hk hs (fun o ho _ hq ↦ ?_) (fun o ho _ hq ↦ ?_) fun q hq ↦ ?_
  · rcases hq with hq | hq
    · exact notIn (by rw [hst]; omega) (by rw [hbN]; omega) (by rw [hst, hbN]; omega) hq
    · exact hq
  · rcases hq with hq | hq
    · exact notIn (by rw [hst]; omega) (by omega) (by rw [hst]; omega) hq
    · exact hq
  · rcases hq with hq | hq
    · obtain ⟨hdw, hds, -, -⟩ := dec_geo hpre
      have := g.ht; have := g.hts
      rw [Sym.inRange_iff (by rw [hst]; omega), hst] at hq
      refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
      · have h' : InRange (tA m0) 760 q := h
        rw [Sym.inRange_iff (by omega)] at h'; omega
      · have h' : InRange a.words (8 * a.len) q := h
        rw [Sym.inRange_iff hdw] at h'; omega
    · exact hq.elim

end

end NativeRustcVmArm.KeccakGkr.VerifyLayer
