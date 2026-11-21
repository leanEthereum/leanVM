module

public import NativeVm.Code.Phase7.Claims
public import NativeVm.Code.Phase7.RingWeight

/-!
# Phase 7: the basis evaluation

`basisEvalC` computes `BasisW.eval ⟨scales, cl⟩ x` (`dot scales (cl.map (·.weight.eval x))`) for
the stack claims `cl = stackClaims …` and the scales at `basisR`, the point `x` at the scratch's
`xO`: each claim's weight by `Ring.weightRing` (the ring-switched claim) or `Ring.weightEq` (a
column claim on the stack, the out-of-domain claim), then `accC` adds `scale · weight` to the sum
at `tmpO + 18`. The kernels keep only `rdi`, so the loop's state is in scratch words: the claims
left (`cI`), the next claim (`cJ`), the next scale (`cK`).
-/

@[expose] public section

namespace NativeVm.Code.P7

open Native NativeVm.Model NativeVm.Field LeanVM.Parameters NativeVm.Equiv
open LeanVM.Protocol.Verifier (qkeccak Placement)
open NativeVm.Transcript (wd Env Fits Disj wdisp ctxWork ctxEnd wd_inj wd_zero wd_toNat wp_load
  wp_store wp_storei wp_reg eval_cw eval_wd eval_idx64 setMem_wd_ne setMem_wd_eq toUInt64_add
  wp_ite_true wp_ite_false)

/-! ## Words -/

/-- The words the basis evaluation writes. -/
def WBe (k : Nat) : Prop :=
  (tmpO + 16 ≤ k ∧ k < tmpO + 32) ∨ (ringO ≤ k ∧ k < ringO + 128) ∨ (sc 5 ≤ k ∧ k < sc 8)

theorem fits_wd {W : UInt64} {N k m : Nat} (h : Fits W N) (hk : k < N) (hkm : k + m ≤ N) :
    Fits (wd W k) m := by
  have := wd_toNat h hk
  unfold Fits at *
  omega

theorem disj_wd {W : UInt64} {N a n b m : Nat} (h : Fits W N) (ha : a < N) (hb : b < N)
    (hd : a + n ≤ b ∨ b + m ≤ a) : Disj (wd W a) n (wd W b) m := by
  have := wd_toNat h ha
  have := wd_toNat h hb
  unfold Disj
  omega

/-- A kernel writing only `n` words from area word `o`, all in `Wk`. -/
theorem Wr.buf {env : Env} {Wk : Nat → Prop} {s0 t t' : QState} (h : Wr env Wk s0 t) {o n : Nat}
    (hW : ∀ j < n, Wk (o + j)) (h1 : mineLo ≤ o) (h2 : o + n ≤ dataEnd)
    (hdi : t'.reg .rdi = t.reg .rdi) (hd : ∀ a, (t'.mem a).isSome = (t.mem a).isSome)
    (hm : ∀ a, (∀ j < n, a ≠ wd env.work (o + j)) → t'.mem a = t.mem a) : Wr env Wk s0 t' := by
  refine ⟨⟨hdi.trans h.fr.rdi, fun a ↦ (hd a).trans (h.fr.dom a), fun a ha ↦ ?_⟩,
    fun k k1 k2 hk ↦ ?_⟩
  · rw [hm a fun j hj e ↦ ha (by rw [e]; exact inMine_wd (by omega) (by omega))]
    exact h.fr.mem a ha
  · rw [hm _ fun j hj e ↦ ?_]
    · exact h.only k k1 k2 hk
    · rw [dataEnd_val] at k2 h2
      have := (wd_inj (by omega) (by omega)).mp e
      exact hk (this ▸ hW j hj)

theorem WrS.regs {env : Env} {Wk : Nat → Prop} {s0 t t' : QState} (h : WrS env Wk s0 t)
    (hm : t'.mem = t.mem) (hdi : t'.reg .rdi = t.reg .rdi) : WrS env Wk s0 t' :=
  ⟨h.w.regs hm hdi, by rw [hm]; exact h.sm⟩

/-- The context's words are kept. -/
theorem Wr.ctx {env : Env} {inp : Input} {Wk : Nat → Prop} {s0 t : QState} (h : Wr env Wk s0 t)
    (hi : Inputs env inp s0.mem) {k : Nat} (hk : k < ctxEnd) :
    t.mem (wd env.ctx k) = s0.mem (wd env.ctx k) :=
  h.fr.mem _ fun ⟨j, _, j2, e⟩ ↦ hi.ctx_ne_work hk
    (by have := workWords_ge inp.bytecode.size; rw [dataEnd_val] at j2; omega) e

/-- An array in area words outside `Wk` is kept. -/
theorem Wr.ewarr {env : Env} {Wk : Nat → Prop} {s0 t : QState} (h : Wr env Wk s0 t) {o : Nat}
    {xs : Array EW} (hx : EWArr s0.mem (wd env.work o) xs) (h1 : mineLo ≤ o)
    (h2 : o + 2 * xs.size ≤ dataEnd) (hW : ∀ j < 2 * xs.size, ¬ Wk (o + j)) :
    EWArr t.mem (wd env.work o) xs :=
  hx.congr (h.only.same h1 h2 hW) le_rfl

/-! ## The model -/

theorem add_mul_comm (acc a b : EW) : acc + a * b = b * a + acc :=
  EW.toE_injective (by rw [EW.toE_add, EW.toE_add, EW.toE_mul, EW.toE_mul]; ring)

theorem dot_extract_succ {xs ws : Array EW} {k : Nat} (hk : k < xs.size) (hws : ws.size = k)
    (w : EW) : dot (xs.extract 0 (k + 1)) (ws.push w) = dot (xs.extract 0 k) ws + xs[k] * w := by
  rw [Array.extract_succ_right (by omega) hk, dot_push (by rw [Array.size_extract]; omega)]

/-- The weights after `i` column claims. -/
def wsAt (layout : LayoutW) (x : Array EW) (ringW : EW) (claims : Array ColumnClaimW) (i : Nat) :
    List EW :=
  ringW :: ((claims.toList.take i).filterMap (·.onStack layout)).map (·.weight.eval x)

theorem wsAt_succ (layout : LayoutW) (x : Array EW) (ringW : EW) (claims : Array ColumnClaimW)
    {i : Nat} (hi : i < claims.size) :
    wsAt layout x ringW claims (i + 1) = wsAt layout x ringW claims i ++
      (((layout.placements[claims[i].column]?).getD none).map fun pl ↦
        StackWeight.eval (.eq (stackPoint pl claims[i].point layout.stackLog)) x).toList := by
  simp only [wsAt, List.take_add_one, List.filterMap_append, List.map_append, List.cons_append]
  rw [List.getElem?_eq_getElem (by simpa using hi), Array.getElem_toList]
  simp only [Option.toList_some, List.filterMap_cons, List.filterMap_nil, ColumnClaimW.onStack]
  cases (layout.placements[claims[i].column]?).getD none <;> simp

/-! ## One weight added -/

/-- The sum after the weights `ws`, and the next scale's address. -/
structure EInv (W : UInt64) (scales ws : Array EW) (mem : UInt64 → Option UInt64) : Prop where
  acc : EWAt mem (wd W (tmpO + 18)) (dot (scales.extract 0 ws.size) ws)
  ptr : mem (wd W cK) = some (wd W (basisR.off + 1 + 2 * ws.size))

/-- `sum += scale · A`, the scale at `cK`'s address, which moves to the next. -/
def accC : List Stmt := [ldW, ldw .r13 cK,
  I (.load .r11 (at_ .r13 (wdisp 0))), I (.load .r12 (at_ .r13 (wdisp 1))), emul,
  ldw .r11 (tmpO + 18), ldw .r12 (tmpO + 18 + 1), eadd,
  stw (tmpO + 18) .r9, stw (tmpO + 18 + 1) .r10,
  I (.addi .r13 16), stw cK .r13]

variable {s : QState} {P E : QState → Prop} {rest : List Stmt}

theorem accC_spec {env : Env} {s0 : QState} {w : EW} {scales ws : Array EW}
    (hrdi : s.reg .rdi = env.ctx) (hwp : s.mem (wd env.ctx ctxWork) = some env.work)
    (h9 : s.reg .r9 = w.c0) (h10 : s.reg .r10 = w.c1) (hE : EInv env.work scales ws s.mem)
    (hsc : EWArr s.mem (wd env.work (basisR.off + 1)) scales) (hk : ws.size < scales.size)
    (hw : WrS env WBe s0 s) :
    WP (blk accC) s (fun s' ↦ EInv env.work scales (ws.push w) s'.mem ∧ WrS env WBe s0 s' ∧
      s'.reg .rdi = s.reg .rdi ∧ ∀ j, j ≠ tmpO + 18 → j ≠ tmpO + 18 + 1 → j ≠ cK → j < 2 ^ 61 →
        s'.mem (wd env.work j) = s.mem (wd env.work j)) E := by
  obtain ⟨c0, c1⟩ := hsc ws.size hk
  rw [wd_wd] at c0 c1
  rw [wd_wd] at c1
  obtain ⟨a0, a1⟩ := ewat_wd hE.acc
  unfold accC ldW
  refine wp_load (eval_cw hrdi ctxWork) hwp ?_
  have hW : (s.setReg .rbp env.work).reg .rbp = env.work := by rsimp
  refine ldw_wp hW hE.ptr ?_
  refine wp_load (eval_wd (b := env.work) (j := basisR.off + 1 + 2 * ws.size) (by rsimp) 0)
    (by rsimp; rw [Nat.add_zero]; exact c0) ?_
  refine wp_load (eval_wd (b := env.work) (j := basisR.off + 1 + 2 * ws.size) (by rsimp) 1)
    (by rsimp; rw [show basisR.off + 1 + 2 * ws.size + 1 = basisR.off + 1 + (2 * ws.size + 1) by
      omega]; exact c1) ?_
  refine emul_r (a := w) (b := scales[ws.size]) (by rsimp; exact h9) (by rsimp; exact h10)
    (by rsimp) (by rsimp) fun s1 m1 e9 e10 f1 ↦ ?_
  rsimp at m1
  have hW1 : s1.reg .rbp = env.work := by rw [f1 .rbp (by decide)]; rsimp
  have h13 : s1.reg .r13 = wd env.work (basisR.off + 1 + 2 * ws.size) := by
    rw [f1 .r13 (by decide)]; rsimp
  have hdi1 : s1.reg .rdi = s.reg .rdi := by rw [f1 .rdi (by decide)]; rsimp
  refine ldw_wp hW1 (by rw [m1]; exact a0) (ldw_wp (by rsimp; exact hW1) (by rsimp; rw [m1]; exact a1) ?_)
  refine eadd_r (a := w * scales[ws.size]) (b := dot (scales.extract 0 ws.size) ws) (by rsimp; exact e9)
    (by rsimp; exact e10) (by rsimp) (by rsimp) fun s2 m2 g9 g10 f2 ↦ ?_
  rsimp at m2
  have hW2 : s2.reg .rbp = env.work := by rw [f2 .rbp (by decide)]; rsimp; exact hW1
  have g13 : s2.reg .r13 = wd env.work (basisR.off + 1 + 2 * ws.size) := by
    rw [f2 .r13 (by decide)]; rsimp; exact h13
  have hdi2 : s2.reg .rdi = s.reg .rdi := by rw [f2 .rdi (by decide)]; rsimp; exact hdi1
  have hm2 : s2.mem = s.mem := by rw [m2, m1]
  have hw2 : WrS env WBe s0 s2 := hw.regs hm2 hdi2
  refine stw_wp hW2 (hw2.sm _ (by oomega)) ?_
  refine stw_wp (by rsimp; exact hW2) (by wsome hw2.sm) ?_
  refine wp_reg rfl ?_
  refine stw_wp (by rsimp; exact hW2) (by wsome hw2.sm) ?_
  refine WP.blk_nil ⟨⟨?_, ?_⟩, ?_, ?_, ?_⟩
  · rw [Array.size_push, dot_extract_succ hk rfl, add_mul_comm]
    refine ⟨?_, ?_⟩ <;> (try rw [wd_wd]) <;> cwsimp
    · exact g9.symm ▸ rfl
    · exact g10.symm ▸ rfl
  · cwsimp
    rw [g13, Array.size_push, show (16 : Int64).toUInt64 = (8 * 2 : Nat).toUInt64 from rfl,
      NativeVm.Transcript.wd_add]
    congr 2
  · refine WrS.st (k := cK) ?_ ⟨.inr (.inr ⟨by oomega, by oomega⟩), by oomega, by oomega⟩ _
    refine WrS.reg (r := .r13) ?_ (by decide) _
    refine WrS.st (k := tmpO + 18 + 1) ?_ ⟨.inl ⟨by oomega, by oomega⟩, by oomega, by oomega⟩ _
    exact WrS.st (k := tmpO + 18) hw2 ⟨.inl ⟨by oomega, by oomega⟩, by oomega, by oomega⟩ _
  · rsimp; exact hdi2
  · intro j j1 j2 j3 j4
    cwsimp
    rw [hm2]

/-- A register set by `leaw`, `rbp` at the area. -/
macro "evw" : tactic => `(tactic|
  simp only [NativeVm.Transcript.eval_at, QState.setReg_reg, QState.setReg_mem, QState.setMem_reg,
    reduceCtorEq, ite_false, ite_true, ↓reduceIte])

/-! ## The ring-switched claim's weight -/

/-- `q_keccak`'s placement word. -/
abbrev qkW : Nat := layoutR.off + 16 + 3 * qkeccak

/-- `rsi`, `rdx`: `q_keccak`'s placement (`⟨0, 0⟩` for none). -/
def plC : Stmt := .ite (.cmp .eq .rax (.imm 1)) (blk [ldw .rdx (qkW + 1), ldw .rsi (qkW + 2)]) .skip

/-- The ring-switched claim's weight, in `A`. -/
def ringWC : List Stmt := [ldW, I (.movi .rsi 0), I (.movi .rdx 0), ldw .rax qkW, plC,
  leaw .r13 (keccakR.off + 1), ldw .r15 keccakR.off, leaw .r14 xO, leaw .r11 (ringR.off + 2),
  I (.movi .r12 (Int64.ofNat ringCoeffCount)), leaw .rbx ringO, ldw .rbp (layoutR.off + 2),
  Ring.weightRing]

theorem ring_imm : (Int64.ofNat ringCoeffCount).toUInt64 = ringCoeffCount.toUInt64 ∧
    ringCoeffCount = 64 ∧ pointCap = 36 ∧ qkeccak = 4 ∧ Ring.bufWords = 80 := by decide +kernel

theorem plC_spec {env : Env} {layout : LayoutW} {bc : Array UInt64} {rate : Nat}
    (hlay : LayoutAt s.mem (layoutR.at env.work) bc layout rate) (hW : s.reg .rbp = env.work)
    (hax : s.mem (wd env.work qkW) = some (s.reg .rax)) (hsi : s.reg .rsi = 0)
    (hdx : s.reg .rdx = 0) :
    WP plC s (fun u ↦ u.mem = s.mem ∧ u.reg .rdi = s.reg .rdi ∧ u.reg .rbp = env.work ∧
      u.reg .rsi = (layout.placement qkeccak).index.toUInt64 ∧
      u.reg .rdx = (layout.placement qkeccak).variableCount.toUInt64 ∧
      (layout.placement qkeccak).index < 2 ^ 64 ∧
      (layout.placement qkeccak).variableCount < 2 ^ 64) E := by
  obtain ⟨-, -, -, hq4, -⟩ := ring_imm
  have hP := hlay.placements qkeccak (by rw [hq4, columnCount_val]; omega)
  rw [Region.at, wd_wd, ← Nat.add_assoc] at hP
  have hg : layout.placement qkeccak = (layout.placements.getD qkeccak none).getD default := by
    rw [LayoutW.placement, placement_some (by rw [hlay.placementsSize, hq4, columnCount_val]; omega)]
  unfold plC
  rcases hpe : layout.placements.getD qkeccak none with _ | pl
  · rw [hpe] at hP hg
    have h0 : s.reg .rax = 0 := Option.some_inj.mp (hax.symm.trans hP)
    refine wp_ite_false ?_ (WP.skip ⟨rfl, rfl, hW, by rw [hg, hsi]; rfl, by rw [hg, hdx]; rfl,
      by rw [hg]; decide, by rw [hg]; decide⟩)
    rw [NativeVm.Transcript.cond_eq, NativeVm.Transcript.rhs_imm, h0]
    simp [int64One_toUInt64]
  · rw [hpe] at hP hg
    rw [Option.getD_some] at hg
    obtain ⟨h1, ⟨v1, v2⟩, ⟨i1, i2⟩⟩ := hP
    rw [wd_wd] at v2 i2
    have h0 : s.reg .rax = 1 := Option.some_inj.mp (hax.symm.trans h1)
    refine wp_ite_true ?_ ?_
    · rw [NativeVm.Transcript.cond_eq, NativeVm.Transcript.rhs_imm, h0]
      simp [int64One_toUInt64]
    · refine ldw_wp hW v2 (ldw_wp (by rsimp; exact hW) (by rsimp; exact i2) (WP.blk_nil ?_))
      rw [hg]
      refine ⟨rfl, by rsimp, by rsimp; exact hW, by rsimp, by rsimp, i1, v1⟩

/-- `weightRing` on the ring switch's point, coefficients and the basis point, the buffer at
`ringO`. -/
theorem ringK_spec {env : Env} {inp : Input} {pl : Placement} {point coeffs x : Array EW}
    (hfw : Fits env.work (workWords inp.bytecode.size))
    (hsm : ∀ j < dataEnd, (s.mem (wd env.work j)).isSome)
    (h13 : s.reg .r13 = wd env.work (keccakR.off + 1))
    (hp : EWArr s.mem (wd env.work (keccakR.off + 1)) point)
    (h15 : s.reg .r15 = point.size.toUInt64) (hpc : point.size ≤ pointCap)
    (h14 : s.reg .r14 = wd env.work xO) (hx : EWArr s.mem (wd env.work xO) x)
    (hbp : s.reg .rbp = x.size.toUInt64) (hxs : x.size ≤ 30)
    (h11 : s.reg .r11 = wd env.work (ringR.off + 2))
    (hc : EWArr s.mem (wd env.work (ringR.off + 2)) coeffs)
    (h12 : s.reg .r12 = coeffs.size.toUInt64) (hcs : coeffs.size = ringCoeffCount)
    (hsi : s.reg .rsi = pl.index.toUInt64) (hdx : s.reg .rdx = pl.variableCount.toUInt64)
    (hidx : pl.index < 2 ^ 64) (hvc : pl.variableCount < 2 ^ 64)
    (hbx : s.reg .rbx = wd env.work ringO) :
    WP Ring.weightRing s (fun s' ↦ s'.reg .r9 = (StackWeight.eval (.ring pl point coeffs) x).c0 ∧
      s'.reg .r10 = (StackWeight.eval (.ring pl point coeffs) x).c1 ∧ s'.reg .rdi = s.reg .rdi ∧
      (∀ a, (∀ k < 80, a ≠ wd env.work (ringO + k)) → s'.mem a = s.mem a) ∧
      ∀ a, (s'.mem a).isSome = (s.mem a).isSome) E := by
  obtain ⟨-, h64, h36, -, hb80⟩ := ring_imm
  have hww := workWords_ge inp.bytecode.size
  have hpc' := hpc
  rw [h36] at hpc'
  have hcs' := hcs
  rw [h64] at hcs'
  refine WP.mono (Ring.weightRing_spec (pl := pl) (buf := wd env.work ringO)
    (by rw [h13]; exact hp) h15 hpc (by rw [h14]; exact hx) hbp (by omega)
    (by rw [h11]; exact hc) h12 (by omega) hsi hdx hidx hvc hbx
    (fits_wd hfw (by aomega) (by rw [hb80]; aomega))
    (fun j hj ↦ by rw [wd_wd]; exact hsm _ (by rw [hb80] at hj; aomega))
    (by rw [h13]; exact fits_wd hfw (by aomega) (by aomega))
    (by rw [h14]; exact fits_wd hfw (by aomega) (by aomega))
    (by rw [h11]; exact fits_wd hfw (by aomega) (by aomega))
    (by rw [h13]; exact disj_wd hfw (by aomega) (by aomega) (by rw [hb80]; aomega))
    (by rw [h14]; exact disj_wd hfw (by aomega) (by aomega) (by rw [hb80]; aomega))
    (by rw [h11]; exact disj_wd hfw (by aomega) (by aomega) (by rw [hb80]; aomega))) ?_
    fun _ h ↦ h
  rintro s' ⟨h9, h10, hdi, -, hfr, hd⟩
  exact ⟨h9, h10, hdi, fun a ha ↦ hfr a fun k hk ↦ by
    rw [wd_wd]; exact ha k (by rw [hb80] at hk; exact hk), hd⟩

theorem ringWC_spec {env : Env} {inp : Input} {s0 : QState} {bc : Array UInt64}
    {layout : LayoutW} {rate : Nat} {claims : Array ColumnClaimW} {ood : StackClaimW}
    {target : EW} {coeffs point slices x : Array EW}
    (hrdi : s.reg .rdi = env.ctx) (hwp : s.mem (wd env.ctx ctxWork) = some env.work)
    (hfw : Fits env.work (workWords inp.bytecode.size))
    (hR : Regs s.mem env.work bc layout rate claims ood target coeffs point slices)
    (hx : EWArr s.mem (wd env.work xO) x) (hxs : x.size ≤ 30) (hxl : x.size = layout.stackLog)
    (hw : WrS env WBe s0 s) :
    WP (blk ringWC) s (fun s' ↦
      s'.reg .r9 = (StackWeight.eval (.ring (layout.placement qkeccak) point coeffs) x).c0 ∧
      s'.reg .r10 = (StackWeight.eval (.ring (layout.placement qkeccak) point coeffs) x).c1 ∧
      s'.reg .rdi = s.reg .rdi ∧ WrS env WBe s0 s' ∧
      ∀ j, (j < ringO ∨ ringO + 80 ≤ j) → j < 2 ^ 61 →
        s'.mem (wd env.work j) = s.mem (wd env.work j)) E := by
  obtain ⟨hcc, h64, h36, hq4, hb80⟩ := ring_imm
  have hww := workWords_ge inp.bytecode.size
  obtain ⟨hpc, hpn, hpa⟩ := hR.kec.1
  rw [Region.at, wd_wd] at hpa
  obtain ⟨-, hcs, hca⟩ := hR.ring
  rw [Region.at, wd_wd] at hca
  have hsl := hR.lay.stackLog
  rw [Region.at, wd_wd] at hsl
  have hq := hR.lay.placements qkeccak (by rw [hq4, columnCount_val]; omega)
  rw [Region.at, wd_wd, ← Nat.add_assoc] at hq
  have hqw : ∃ v, s.mem (wd env.work qkW) = some v := by
    cases hpe : layout.placements.getD qkeccak none with
    | none => rw [hpe] at hq; exact ⟨_, hq⟩
    | some pl => rw [hpe] at hq; exact ⟨_, hq.1⟩
  obtain ⟨v, hv⟩ := hqw
  unfold ringWC ldW
  refine wp_load (eval_cw hrdi ctxWork) hwp ?_
  have hW : (s.setReg .rbp env.work).reg .rbp = env.work := by rsimp
  refine wp_reg rfl (wp_reg rfl ?_)
  refine ldw_wp (by rsimp; exact hW) (by rsimp; exact hv) ?_
  refine WP.then (plC_spec (env := env) (layout := layout) (by rsimp; exact hR.lay) (by rsimp)
    (by rsimp; exact hv) (by rsimp) (by rsimp)) fun u ⟨um, udi, uW, usi, udx, ui, uv⟩ ↦ ?_
  rsimp at um udi
  refine wp_reg rfl ?_
  refine ldw_wp (by rsimp; exact uW) (by rsimp; rw [um]; exact hpn.2) ?_
  refine wp_reg rfl (wp_reg rfl (wp_reg rfl (wp_reg rfl ?_)))
  refine ldw_wp (by rsimp; exact uW) (by rsimp; rw [um]; exact hsl.2) ?_
  refine WP.mono (ringK_spec (pl := layout.placement qkeccak) (point := point) (coeffs := coeffs)
    (x := x) hfw (fun j hj ↦ by rsimp; rw [um]; exact hw.sm j hj)
    (by evw; rw [uW]; rfl) (by rsimp; rw [um]; exact hpa) (by rsimp) hpc
    (by evw; rw [uW]; rfl) (by rsimp; rw [um]; exact hx)
    (by rsimp; rw [hxl]) hxs (by evw; rw [uW]; rfl)
    (by rsimp; rw [um]; exact hca) (by rsimp; rw [hcc, hcs]) hcs (by rsimp; exact usi)
    (by rsimp; exact udx) ui uv (by evw; rw [uW]; rfl)) ?_ fun _ h ↦ h
  rintro s' ⟨h9, h10, hdi, hfr, hd⟩
  refine ⟨h9, h10, by rw [hdi]; rsimp; rw [udi], ?_, ?_⟩
  · refine ⟨Wr.buf (o := ringO) (n := 80) (hw.w.regs (s' := u) um udi)
      (fun j hj ↦ .inr (.inl ⟨by omega, by omega⟩)) (by oomega)
      (by oomega) (by rw [hdi]; rsimp) (fun a ↦ by rw [hd a]; rsimp)
      (fun a ha ↦ by rw [hfr a ha]; rsimp), ?_⟩
    intro j hj
    rw [hd]; rsimp; rw [um]; exact hw.sm j hj
  · intro j hj hj'
    rw [hfr _ fun k hk e ↦ ?_]
    · rsimp; rw [um]
    · rw [wd_inj hj' (by oomega)] at e
      omega

/-! ## The column claims' weights -/

/-- Word `d` of the placement triple, `rbx` thrice the column. -/
def lidx (d : Nat) : Addr := { base := .rbp, idx := some (.rbx, .W64), disp := wdisp (layoutR.off + d) }

/-- A column claim on the stack (at `r13`): its weight, added. -/
def colEPush : List Stmt := [I (.load .rdx (lidx 17)), I (.load .rsi (lidx 18)),
  I (.load .r15 (at_ .r13 (wdisp 1))), I (.lea .r13 (at_ .r13 (wdisp 2))), leaw .r14 xO,
  ldw .rcx (layoutR.off + 2), I (.mov .rbp .rcx), Ring.weightEq, blk accC]

/-- The column (in `rax`) below `columnCount` and placed: its weight, added. -/
def colETest : Stmt := .ite (.cmp .ltu .rax (.imm (Int64.ofNat columnCount))) (blk [
  I (.mov .rbx .rax), I (.add .rbx .rbx), I (.add .rbx .rax), I (.load .rcx (lidx 16)),
  .ite (.cmp .eq .rcx (.imm 1)) (blk colEPush) .skip]) .skip

theorem wsAt_length_le (layout : LayoutW) (x : Array EW) (ringW : EW) (claims : Array ColumnClaimW)
    {i j : Nat} (h : i ≤ j) : (wsAt layout x ringW claims i).length ≤ (wsAt layout x ringW claims j).length := by
  simp only [wsAt, List.length_cons, List.length_map]
  exact Nat.succ_le_succ (((List.take_sublist_take_left h).filterMap _).length_le)

theorem lidx_eval {t : QState} {W : UInt64} {c d : Nat} (hW : t.reg .rbp = W)
    (hbx : t.reg .rbx = c.toUInt64 + c.toUInt64 + c.toUInt64) :
    (lidx d).eval t = wd W (layoutR.off + d + 3 * c) := by
  rw [lidx, eval_idx64 (j := 0) (i := c + c + c) (by rw [hW, wd_zero])
    (by rw [hbx, toUInt64_add, toUInt64_add])]
  congr 1; omega

theorem colETest_spec {env : Env} {s0 t : QState} {bc : Array UInt64} {layout : LayoutW}
    {rate : Nat} {claims : Array ColumnClaimW} {ood : StackClaimW} {target ringW : EW}
    {coeffs point slices x scales ws : Array EW} {i : Nat}
    (hR : Regs t.mem env.work bc layout rate claims ood target coeffs point slices)
    (hrdi : t.reg .rdi = env.ctx) (hwp : t.mem (wd env.ctx ctxWork) = some env.work)
    (hx : EWArr t.mem (wd env.work xO) x) (hxs : x.size ≤ 30) (hxl : x.size = layout.stackLog)
    (hsc : EWArr t.mem (wd env.work (basisR.off + 1)) scales)
    (hsz : (wsAt layout x ringW claims claims.size).length < scales.size)
    (hi : i < claims.size) (hW : t.reg .rbp = env.work)
    (h13 : t.reg .r13 = wd env.work (claimsR.off + 1 + claimWords * i))
    (hrax : t.reg .rax = claims[i].column.toUInt64)
    (hv : ws.toList = wsAt layout x ringW claims i) (hE : EInv env.work scales ws t.mem)
    (hw : WrS env WBe s0 t) :
    WP colETest t (fun t' ↦ ∃ ws' : Array EW, ws'.toList = wsAt layout x ringW claims (i + 1) ∧
      EInv env.work scales ws' t'.mem ∧ WrS env WBe s0 t' ∧ t'.reg .rdi = t.reg .rdi ∧
      ∀ j, j ≠ tmpO + 18 → j ≠ tmpO + 18 + 1 → j ≠ cK → j < 2 ^ 61 →
        t'.mem (wd env.work j) = t.mem (wd env.work j)) E := by
  obtain ⟨cw76, vw73, cap160, cc158⟩ := claim_sizes
  have hcap := hR.cl.1
  rw [cap160] at hcap
  have hcl := hR.cl.2.2 i hi
  rw [Region.at, wd_wd, ← Nat.add_assoc] at hcl
  obtain ⟨hc64, ⟨hpc, hpn, hpa⟩, -⟩ := hcl
  rw [wd_wd] at hpn
  rw [wd_wd, wd_wd, Nat.add_assoc] at hpa
  have hpl := hR.lay.placementsSize
  have hsl := hR.lay.stackLog
  rw [Region.at, wd_wd] at hsl
  have skip : ∀ u : QState, u.mem = t.mem → u.reg .rdi = t.reg .rdi →
      wsAt layout x ringW claims (i + 1) = wsAt layout x ringW claims i →
      ∃ ws' : Array EW, ws'.toList = wsAt layout x ringW claims (i + 1) ∧
        EInv env.work scales ws' u.mem ∧ WrS env WBe s0 u ∧ u.reg .rdi = t.reg .rdi ∧
        ∀ j, j ≠ tmpO + 18 → j ≠ tmpO + 18 + 1 → j ≠ cK → j < 2 ^ 61 →
          u.mem (wd env.work j) = t.mem (wd env.work j) := fun u hm hdi he ↦
    ⟨ws, by rw [he, hv], by rw [hm]; exact hE, hw.regs hm hdi, hdi, fun j _ _ _ _ ↦ by rw [hm]⟩
  unfold colETest
  by_cases hlt : claims[i].column < columnCount
  · rw [cc158] at hlt
    refine wp_ite_true (by
      rw [NativeVm.Transcript.cond_ltu, NativeVm.Transcript.rhs_imm, cc_imm, hrax,
        decide_eq_true_eq, NativeVm.Transcript.toUInt64_lt (by omega) (by omega)]
      exact hlt) ?_
    have hP := hR.lay.placements _ (by rw [cc158]; exact hlt)
    rw [Region.at, wd_wd, ← Nat.add_assoc] at hP
    have hg := placement_some (layout := layout) (c := claims[i].column)
      (by rw [hpl, cc158]; exact hlt)
    refine wp_reg rfl (wp_reg rfl (wp_reg rfl ?_))
    have hbx : ∀ u : QState, u.reg .rbp = env.work → u.reg .rbx = claims[i].column.toUInt64 +
        claims[i].column.toUInt64 + claims[i].column.toUInt64 → ∀ d,
        (lidx d).eval u = wd env.work (layoutR.off + d + 3 * claims[i].column) :=
      fun u h1 h2 d ↦ lidx_eval h1 h2
    rcases hpe : layout.placements.getD claims[i].column none with _ | pl
    · rw [hpe] at hP
      refine wp_load (hbx _ (by rsimp; exact hW) (by rsimp; rw [hrax]) 16) (by rsimp; exact hP) ?_
      refine wp_ite_false (by
        rw [NativeVm.Transcript.cond_eq, NativeVm.Transcript.rhs_imm]; simp [int64One_toUInt64])
        (WP.skip (skip _ (by rsimp) (by rsimp) ?_))
      rw [wsAt_succ _ _ _ _ hi, hg, hpe]
      simp
    · rw [hpe] at hP
      obtain ⟨hf, ⟨hv1, hv2⟩, ⟨hi1, hi2⟩⟩ := hP
      rw [wd_wd] at hv2 hi2
      refine wp_load (hbx _ (by rsimp; exact hW) (by rsimp; rw [hrax]) 16) (by rsimp; exact hf) ?_
      refine wp_ite_true (by
        rw [NativeVm.Transcript.cond_eq, NativeVm.Transcript.rhs_imm]; simp [int64One_toUInt64]) ?_
      unfold colEPush
      refine wp_load (hbx _ (by rsimp; exact hW) (by rsimp; rw [hrax]) 17)
        (by rsimp; rw [show layoutR.off + 17 + 3 * claims[i].column =
          layoutR.off + 16 + 3 * claims[i].column + 1 by omega]; exact hv2) ?_
      refine wp_load (hbx _ (by rsimp; exact hW) (by rsimp; rw [hrax]) 18)
        (by rsimp; rw [show layoutR.off + 18 + 3 * claims[i].column =
          layoutR.off + 16 + 3 * claims[i].column + 2 by omega]; exact hi2) ?_
      refine wp_load (eval_wd (by rsimp; exact h13) 1) (by rsimp; exact hpn.2) ?_
      refine wp_reg rfl ?_
      refine wp_reg rfl ?_
      refine ldw_wp (by rsimp; exact hW) (by rsimp; exact hsl.2) ?_
      refine wp_reg rfl ?_
      refine WP.then (Ring.weightEq_spec (pt := claims[i].point) (x := x) (pl := pl)
        (sl := layout.stackLog)
        (by evw; rw [h13, NativeVm.Transcript.wdisp_toUInt64, NativeVm.Transcript.wd_add]
            exact hpa)
        (by evw; rw [hW, NativeVm.Transcript.wdisp_toUInt64]; exact hx)
        (by rsimp) (by rsimp; rw [hxl]) (by rsimp) (by rsimp)
        (by rsimp) (by rw [pointCap_val] at hpc; omega) (by omega) hi1 hv1 hsl.1)
        fun u ⟨u9, u10, um, udi, _⟩ ↦ ?_
      rsimp at um udi
      have hk : ws.size < scales.size := by
        have := wsAt_length_le layout x ringW claims (i := i + 1) (j := claims.size) (by omega)
        rw [wsAt_succ _ _ _ _ hi, hg, hpe, List.length_append, ← hv] at this
        simp at this
        omega
      refine WP.mono (accC_spec (s0 := s0) (by rw [udi]; exact hrdi) (by rw [um]; exact hwp) u9 u10
        (by rw [um]; exact hE) (by rw [um]; exact hsc) hk (hw.regs um udi)) ?_ fun _ h ↦ h
      rintro t' ⟨hE', hw', hdi', hfr'⟩
      refine ⟨ws.push _, ?_, hE', hw', by rw [hdi', udi], fun j j1 j2 j3 j4 ↦ by
        rw [hfr' j j1 j2 j3 j4, um]⟩
      rw [Array.toList_push, hv, wsAt_succ _ _ _ _ hi, hg, hpe]
      rfl
  · refine wp_ite_false (by
      rw [NativeVm.Transcript.cond_ltu, NativeVm.Transcript.rhs_imm, cc_imm, hrax,
        decide_eq_false_iff_not, NativeVm.Transcript.toUInt64_lt hc64.1 (by omega)]
      omega) (WP.skip (skip _ rfl rfl ?_))
    rw [wsAt_succ _ _ _ _ hi, Array.getElem?_eq_none (by omega)]
    simp

/-- One column claim, at `cJ`'s address; `cI` claims left (also in `r15`). -/
def colEBody : Stmt := blk [ldW, ldw .r13 cJ, I (.load .rax (at_ .r13 (wdisp 0))), colETest,
  ldW, ldw .r13 cJ, I (.addi .r13 (Int64.ofNat (8 * claimWords))), stw cJ .r13,
  ldw .r15 cI, I (.subi .r15 1), stw cI .r15]

/-- The facts of the start state the loop reads. -/
structure Start (env : Env) (inp : Input) (s0 : QState) (bc : Array UInt64) (layout : LayoutW)
    (rate : Nat) (claims : Array ColumnClaimW) (ood : StackClaimW) (target : EW)
    (coeffs point slices x scales : Array EW) : Prop where
  regs : Regs s0.mem env.work bc layout rate claims ood target coeffs point slices
  inp : Inputs env inp s0.mem
  wp : s0.mem (wd env.ctx ctxWork) = some env.work
  px : EWArr s0.mem (wd env.work xO) x
  pxs : x.size ≤ 30
  pxl : x.size = layout.stackLog
  psc : EWArr s0.mem (wd env.work (basisR.off + 1)) scales
  pscs : scales.size ≤ stackClaimCap

/-- The start state's facts in a later state. -/
theorem Start.at {env : Env} {inp : Input} {s0 t : QState} {bc : Array UInt64} {layout : LayoutW}
    {rate : Nat} {claims : Array ColumnClaimW} {ood : StackClaimW} {target : EW}
    {coeffs point slices x scales : Array EW}
    (h : Start env inp s0 bc layout rate claims ood target coeffs point slices x scales)
    (hw : Wr env WBe s0 t) :
    Regs t.mem env.work bc layout rate claims ood target coeffs point slices ∧
      t.mem (wd env.ctx ctxWork) = some env.work ∧ EWArr t.mem (wd env.work xO) x ∧
      EWArr t.mem (wd env.work (basisR.off + 1)) scales := by
  have hxs := h.pxs
  have hss := h.pscs
  rw [stackClaimCap_val] at hss
  refine ⟨h.regs.congr fun _ _ _ ho ↦ hw.low ho, by
      rw [hw.ctx h.inp (by decide)]
      exact h.wp,
    hw.ewarr h.px (by oomega) (by oomega) fun j hj ↦ ?_,
    hw.ewarr h.psc (by oomega) (by oomega) fun j hj ↦ ?_⟩
  · simp only [WBe]; oomega
  · simp only [WBe]; oomega

theorem colELoop_spec {env : Env} {inp : Input} {s0 s : QState} {bc : Array UInt64}
    {layout : LayoutW} {rate : Nat} {claims : Array ColumnClaimW} {ood : StackClaimW}
    {target ringW : EW} {coeffs point slices x scales ws : Array EW} {F : QState → Prop}
    (hS : Start env inp s0 bc layout rate claims ood target coeffs point slices x scales)
    (hsz : (wsAt layout x ringW claims claims.size).length < scales.size)
    (hrdi : s.reg .rdi = env.ctx) (h15 : s.reg .r15 = claims.size.toUInt64)
    (hcI : s.mem (wd env.work cI) = some claims.size.toUInt64)
    (hcJ : s.mem (wd env.work cJ) = some (wd env.work (claimsR.off + 1)))
    (hv : ws.toList = wsAt layout x ringW claims 0) (hE : EInv env.work scales ws s.mem)
    (hw : WrS env WBe s0 s) :
    WP (.loop (.cmp .ne .r15 (.imm 0)) colEBody) s (fun s' ↦ s'.reg .rdi = env.ctx ∧
      ∃ ws' : Array EW, ws'.toList = wsAt layout x ringW claims claims.size ∧
        EInv env.work scales ws' s'.mem ∧ WrS env WBe s0 s') F := by
  obtain ⟨cw76, vw73, cap160, cc158⟩ := claim_sizes
  have hcap := hS.regs.cl.1
  rw [cap160] at hcap
  have hne : ∀ t : QState, ∀ i ≤ claims.size, t.reg .r15 = (claims.size - i).toUInt64 →
      ((Cond.cmp .ne .r15 (.imm 0)).eval t = true ↔ i < claims.size) := fun t i hi h ↦ by
    rw [NativeVm.Transcript.cond_ne, NativeVm.Transcript.rhs_imm, h, int64Zero_toUInt64,
      bne_iff_ne, ne_eq, show (0 : UInt64) = (0 : Nat).toUInt64 from rfl,
      NativeVm.Transcript.toUInt64_inj (by omega) (by omega)]
    omega
  refine WP.loop (fun t ↦ ∃ i ≤ claims.size, t.reg .rdi = env.ctx ∧
      t.reg .r15 = (claims.size - i).toUInt64 ∧
      t.mem (wd env.work cI) = some (claims.size - i).toUInt64 ∧
      t.mem (wd env.work cJ) = some (wd env.work (claimsR.off + 1 + claimWords * i)) ∧
      ∃ ws : Array EW, ws.toList = wsAt layout x ringW claims i ∧
        EInv env.work scales ws t.mem ∧ WrS env WBe s0 t)
    (fun t ↦ (t.reg .r15).toNat)
    ⟨0, by omega, hrdi, by rw [h15, Nat.sub_zero], by rw [hcI, Nat.sub_zero],
      by rw [hcJ, Nat.mul_zero, Nat.add_zero], ws, hv, hE, hw⟩ ?_ ?_
  · rintro t ⟨i, hi, trdi, t15, tI, tJ, ws, hv, hE, hw⟩ hc
    have hin : i < claims.size := (hne t i hi t15).mp hc
    obtain ⟨hR, hwp, hx, hsc⟩ := hS.at hw.w
    have hcl := hR.cl.2.2 i hin
    rw [Region.at, wd_wd, ← Nat.add_assoc] at hcl
    unfold colEBody ldW
    refine wp_load (eval_cw trdi ctxWork) hwp ?_
    have hW : (t.setReg .rbp env.work).reg .rbp = env.work := by rsimp
    refine ldw_wp hW (by rsimp; exact tJ) ?_
    refine wp_load (eval_wd (b := env.work) (j := claimsR.off + 1 + claimWords * i) (by rsimp) 0)
      (by rsimp; rw [Nat.add_zero]; exact hcl.1.2) ?_
    refine WP.then (colETest_spec (s0 := s0) (ws := ws) (by rsimp; exact hR) (by rsimp; exact trdi)
      (by rsimp; exact hwp) (by rsimp; exact hx) hS.pxs hS.pxl (by rsimp; exact hsc) hsz hin
      (by rsimp) (by rsimp) (by rsimp) hv (by rsimp; exact hE)
      (((hw.reg (r := .rbp) (by decide) _).reg (r := .r13) (by decide) _).reg (r := .rax)
        (by decide) _))
      fun u ⟨ws', hv', hE', hw', udi, hfr⟩ ↦ ?_
    rsimp at udi
    obtain ⟨-, uwp, -, -⟩ := hS.at hw'.w
    refine wp_load (eval_cw (by rw [udi, trdi]) ctxWork) uwp ?_
    have uW : (u.setReg .rbp env.work).reg .rbp = env.work := by rsimp
    refine ldw_wp uW (by rsimp; rw [hfr _ (by oomega) (by oomega) (by oomega) (by oomega)]; exact tJ) ?_
    refine wp_reg rfl ?_
    refine stw_wp (env := env) (by rsimp) (by rsimp; exact hw'.sm _ (by oomega)) ?_
    refine ldw_wp (env := env) (by rsimp) (by
        cwsimp; rw [hfr _ (by oomega) (by oomega) (by oomega) (by oomega)]; exact tI) ?_
    refine wp_reg rfl ?_
    refine stw_wp (env := env) (by rsimp) (by wsome hw'.sm) ?_
    refine WP.blk_nil ⟨⟨i + 1, by omega, by rsimp; rw [udi, trdi], ?_, ?_, ?_, ws', hv', ?_, ?_⟩, ?_⟩
    · rsimp
      rw [show claims.size - i = claims.size - (i + 1) + 1 by omega,
        ← NativeVm.Transcript.toUInt64_succ, UInt64.add_sub_cancel]
    · cwsimp
      rw [show claims.size - i = claims.size - (i + 1) + 1 by omega,
        ← NativeVm.Transcript.toUInt64_succ, UInt64.add_sub_cancel]
    · cwsimp
      rw [claimStep_imm, NativeVm.Transcript.wd_add, cw76]
      congr 2
    · refine ⟨?_, ?_⟩
      · refine ⟨?_, ?_⟩ <;> (try rw [wd_wd]) <;> cwsimp
        · exact hE'.acc.1
        · have := hE'.acc.2
          rw [wd_wd] at this
          exact this
      · cwsimp; exact hE'.ptr
    · refine WrS.st (k := cI) ?_ ⟨.inr (.inr ⟨by oomega, by oomega⟩), by oomega, by oomega⟩ _
      refine WrS.reg (r := .r15) ?_ (by decide) _
      refine WrS.reg (r := .r15) ?_ (by decide) _
      refine WrS.st (k := cJ) ?_ ⟨.inr (.inr ⟨by oomega, by oomega⟩), by oomega, by oomega⟩ _
      exact (((hw'.reg (r := .rbp) (by decide) _).reg (r := .r13) (by decide) _).reg (r := .r13)
        (by decide) _)
    · rsimp
      rw [show claims.size - i = claims.size - (i + 1) + 1 by omega,
        ← NativeVm.Transcript.toUInt64_succ, UInt64.add_sub_cancel,
        t15, NativeVm.Transcript.toNat_toUInt64 (by omega),
        NativeVm.Transcript.toNat_toUInt64 (by omega)]
      omega
  · rintro t ⟨i, hi, trdi, t15, -, -, ws, hv, hE, hw⟩ hc
    have : ¬ i < claims.size := fun h ↦ by
      rw [(hne t i hi t15).mpr h] at hc; exact absurd hc (by decide)
    obtain rfl : i = claims.size := by omega
    exact ⟨trdi, ws, hv, hE, hw⟩

/-! ## The out-of-domain claim's weight -/

/-- The out-of-domain claim's weight, in `A`. -/
def oodWC : List Stmt := [ldW, leaw .r13 (oodR.off + 1), ldw .r15 oodR.off, I (.movi .rsi 0),
  I (.movi .rdx 0), I (.movi .rcx 0), leaw .r14 xO, ldw .rbp (layoutR.off + 2), Ring.weightEq]

theorem oodWC_spec {env : Env} {bc : Array UInt64} {layout : LayoutW} {rate : Nat}
    {claims : Array ColumnClaimW} {ood : StackClaimW} {target : EW}
    {coeffs point slices x : Array EW}
    (hrdi : s.reg .rdi = env.ctx) (hwp : s.mem (wd env.ctx ctxWork) = some env.work)
    (hR : Regs s.mem env.work bc layout rate claims ood target coeffs point slices)
    (hx : EWArr s.mem (wd env.work xO) x) (hxs : x.size ≤ 30) (hxl : x.size = layout.stackLog) :
    WP (blk oodWC) s (fun s' ↦ s'.reg .r9 = (ood.weight.eval x).c0 ∧
      s'.reg .r10 = (ood.weight.eval x).c1 ∧ s'.mem = s.mem ∧ s'.reg .rdi = s.reg .rdi) E := by
  obtain ⟨z, hz, ⟨hzc, hzn, hza⟩, -⟩ := hR.ood
  rw [Region.at] at hzn
  rw [Region.at, wd_wd] at hza
  have hsl := hR.lay.stackLog
  rw [Region.at, wd_wd] at hsl
  rw [stackCap_val] at hzc
  unfold oodWC ldW
  refine wp_load (eval_cw hrdi ctxWork) hwp ?_
  refine wp_reg rfl ?_
  refine ldw_wp (env := env) (by rsimp) (by rsimp; exact hzn.2) ?_
  refine wp_reg rfl (wp_reg rfl (wp_reg rfl (wp_reg rfl ?_)))
  refine ldw_wp (env := env) (by rsimp) (by rsimp; exact hsl.2) ?_
  refine WP.mono (Ring.weightEq_spec (pt := z) (x := x) (pl := ⟨0, 0⟩) (sl := 0)
    (by evw; exact hza) (by evw; exact hx) (by rsimp) (by rsimp; rw [hxl]) (by rsimp; rfl)
    (by rsimp; rfl) (by rsimp; rfl) (by omega) (by omega) (by decide) (by decide) (by decide)) ?_
    fun _ h ↦ h
  rintro s' ⟨h9, h10, hm, hdi, -⟩
  rw [Ring.stackPoint_zero] at h9 h10
  exact ⟨by rw [h9, hz], by rw [h10, hz], by rw [hm]; rsimp, by rw [hdi]; rsimp⟩

/-! ## The basis evaluation -/

theorem dot_nil_right (xs : Array EW) : dot xs #[] = 0 := by
  rw [dot, ← Array.foldl_toList, Array.toList_zipWith]
  simp

/-- The sum `0`, the first scale's address. -/
def eInitC : List Stmt :=
  [ldW, stwi (tmpO + 18) 0, stwi (tmpO + 18 + 1) 0, leaw .rax (basisR.off + 1), stw cK .rax]

theorem eInitC_spec {env : Env} {scales : Array EW}
    (hrdi : s.reg .rdi = env.ctx) (hwp : s.mem (wd env.ctx ctxWork) = some env.work)
    (h0 : ∀ k < dataEnd, (s.mem (wd env.work k)).isSome) :
    WP (blk eInitC) s (fun s' ↦ EInv env.work scales #[] s'.mem ∧ WrS env WBe s s' ∧
      s'.reg .rdi = s.reg .rdi) E := by
  unfold eInitC ldW
  refine wp_load (eval_cw hrdi ctxWork) hwp ?_
  refine stwi_wp (env := env) (by rsimp) (h0 _ (by oomega)) ?_
  refine stwi_wp (env := env) (by rsimp) (by wsome h0) ?_
  refine wp_reg rfl ?_
  refine stw_wp (env := env) (by rsimp) (by wsome h0) ?_
  refine WP.blk_nil ⟨⟨⟨?_, ?_⟩, ?_⟩, ?_, by rsimp⟩
  · cwsimp; rw [dot_nil_right]; rfl
  · rw [wd_wd]; cwsimp; rw [dot_nil_right]; rfl
  · cwsimp; evw; rfl
  · refine WrS.st (k := cK) ?_ ⟨.inr (.inr ⟨by oomega, by oomega⟩), by oomega, by oomega⟩ _
    refine WrS.reg (r := .rax) ?_ (by decide) _
    refine WrS.st (k := tmpO + 18 + 1) ?_ ⟨.inl ⟨by oomega, by oomega⟩, by oomega, by oomega⟩ _
    refine WrS.st (k := tmpO + 18) ?_ ⟨.inl ⟨by oomega, by oomega⟩, by oomega, by oomega⟩ _
    exact WrS.reg ⟨Wr.refl s, h0⟩ (by decide) _

/-- The loop's counters: `cI` and `r15` the column claims' count, `cJ` the first's address. -/
def loopInitC : List Stmt :=
  [ldW, ldw .r15 claimsR.off, stw cI .r15, leaw .rax (claimsR.off + 1), stw cJ .rax]

theorem loopInitC_spec {env : Env} {s0 : QState} {scales ws : Array EW} {n : Nat}
    (hrdi : s.reg .rdi = env.ctx) (hwp : s.mem (wd env.ctx ctxWork) = some env.work)
    (hn : NatAt s.mem (wd env.work claimsR.off) n) (hE : EInv env.work scales ws s.mem)
    (hw : WrS env WBe s0 s) :
    WP (blk loopInitC) s (fun s' ↦ s'.reg .rdi = env.ctx ∧ s'.reg .r15 = n.toUInt64 ∧
      s'.mem (wd env.work cI) = some n.toUInt64 ∧
      s'.mem (wd env.work cJ) = some (wd env.work (claimsR.off + 1)) ∧
      EInv env.work scales ws s'.mem ∧ WrS env WBe s0 s') E := by
  obtain ⟨a0, a1⟩ := ewat_wd hE.acc
  unfold loopInitC ldW
  refine wp_load (eval_cw hrdi ctxWork) hwp ?_
  refine ldw_wp (env := env) (by rsimp) (by rsimp; exact hn.2) ?_
  refine stw_wp (env := env) (by rsimp) (by rsimp; exact hw.sm _ (by oomega)) ?_
  refine wp_reg rfl ?_
  refine stw_wp (env := env) (by rsimp) (by wsome hw.sm) ?_
  refine WP.blk_nil ⟨by rsimp; exact hrdi, by rsimp, by cwsimp, by cwsimp; evw; rfl,
    ⟨⟨by cwsimp; exact a0, by rw [wd_wd]; cwsimp; exact a1⟩, by cwsimp; exact hE.ptr⟩, ?_⟩
  refine WrS.st (k := cJ) ?_ ⟨.inr (.inr ⟨by oomega, by oomega⟩), by oomega, by oomega⟩ _
  refine WrS.reg (r := .rax) ?_ (by decide) _
  refine WrS.st (k := cI) ?_ ⟨.inr (.inr ⟨by oomega, by oomega⟩), by oomega, by oomega⟩ _
  exact (hw.reg (r := .rbp) (by decide) _).reg (r := .r15) (by decide) _

/-- **The basis evaluation**: `BasisW.eval ⟨scales, cl⟩ x` at `tmpO + 18`. -/
def basisEvalC : Stmt := blk [blk eInitC, blk ringWC, blk accC, blk loopInitC,
  .loop (.cmp .ne .r15 (.imm 0)) colEBody, blk oodWC, blk accC]

theorem stackClaims_weights (layout : LayoutW) (target : EW) (point coeffs : Array EW)
    (claims : Array ColumnClaimW) (ood : StackClaimW) (x : Array EW) :
    ((stackClaims layout target point coeffs claims ood).map (·.weight.eval x)).toList =
      wsAt layout x (StackWeight.eval (.ring (layout.placement qkeccak) point coeffs) x) claims
        claims.size ++ [ood.weight.eval x] := by
  simp [stackClaims, wsAt, List.take_of_length_le]

/-- **The basis evaluation**: `BasisW.eval` of the scales at `basisR` and the stack claims
`stackClaims`, at the point at `xO`; it writes only the words `WBe`. -/
theorem basisEvalC_spec {env : Env} {inp : Input} {s : QState} {F : QState → Prop}
    {bc : Array UInt64} {layout : LayoutW} {rate : Nat} {claims : Array ColumnClaimW}
    {ood : StackClaimW} {target : EW} {coeffs point slices scales x : Array EW}
    (hrdi : s.reg .rdi = env.ctx) (hwp : s.mem (wd env.ctx ctxWork) = some env.work)
    (hi : Inputs env inp s.mem)
    (hlay : LayoutAt s.mem (layoutR.at env.work) bc layout rate)
    (hcl : ClaimsAt s.mem (claimsR.at env.work) claims)
    (hood : EqClaimAt s.mem (oodR.at env.work) ood)
    (hring : RingAt s.mem (ringR.at env.work) target coeffs)
    (hk : KeccakOutAt s.mem (keccakR.at env.work) point slices)
    (hsc : EVec s.mem (basisR.at env.work) stackClaimCap scales)
    (hss : scales.size = (stackClaims layout target point coeffs claims ood).size)
    (hx : EWArr s.mem (wd env.work xO) x) (hxs : x.size ≤ 30) (hxl : x.size = layout.stackLog) :
    WP basisEvalC s (fun s' ↦ EWAt s'.mem (wd env.work (tmpO + 18))
        (BasisW.eval ⟨scales, stackClaims layout target point coeffs claims ood⟩ x) ∧
      FrM env s s' ∧ Only env WBe s.mem s'.mem) F := by
  have hcw := stackClaims_weights layout target point coeffs claims ood x
  set ringW := StackWeight.eval (.ring (layout.placement qkeccak) point coeffs) x with hringW
  have hlen : (stackClaims layout target point coeffs claims ood).size =
      (wsAt layout x ringW claims claims.size).length + 1 := by
    rw [← Array.size_map (f := (·.weight.eval x)), ← Array.length_toList, hcw]
    simp
  have hww := workWords_ge inp.bytecode.size
  have h0 : ∀ k < dataEnd, (s.mem (wd env.work k)).isSome := fun k hk ↦
    hi.workSome k (by rw [dataEnd_val] at hk; omega)
  have hscs := hsc.2.2
  rw [Region.at, wd_wd] at hscs
  have hS : Start env inp s bc layout rate claims ood target coeffs point slices x scales :=
    ⟨⟨hlay, hcl, hood, hring, hk⟩, hi, hwp, hx, hxs, hxl, hscs, hsc.1⟩
  unfold basisEvalC
  refine WP.then (eInitC_spec (scales := scales) hrdi hwp h0) fun s1 ⟨hE1, hw1, d1⟩ ↦ ?_
  obtain ⟨hR1, hwp1, hx1, -⟩ := hS.at hw1.w
  refine WP.then (ringWC_spec (inp := inp) (by rw [d1, hrdi]) hwp1 hi.fitWork hR1 hx1 hxs hxl hw1)
    fun s2 ⟨r9, r10, d2, hw2, fr2⟩ ↦ ?_
  obtain ⟨-, hwp2, -, hsc2⟩ := hS.at hw2.w
  refine WP.then (accC_spec (ws := #[]) (by rw [d2, d1, hrdi]) hwp2 r9 r10
    ⟨⟨by rw [fr2 _ (by oomega) (by oomega)]; exact hE1.acc.1, by
      rw [wd_wd, fr2 _ (by oomega) (by oomega)]; have := hE1.acc.2; rwa [wd_wd] at this⟩,
      by rw [fr2 _ (by oomega) (by oomega)]; exact hE1.ptr⟩ hsc2 (by rw [hss, hlen]; simp) hw2)
    fun s3 ⟨hE3, hw3, d3, _⟩ ↦ ?_
  obtain ⟨hR3, hwp3, -, -⟩ := hS.at hw3.w
  refine WP.then (loopInitC_spec (n := claims.size) (by rw [d3, d2, d1, hrdi]) hwp3 (by
      have := hR3.cl.2.1; rwa [Region.at] at this) hE3 hw3)
    fun s4 ⟨d4, h15, hcI, hcJ, hE4, hw4⟩ ↦ ?_
  refine WP.then (colELoop_spec (ringW := ringW) hS (by rw [hss, hlen]; omega) d4 h15 hcI hcJ
    (by simp [wsAt, hringW]) hE4 hw4) fun s5 ⟨d5, ws, hv, hE5, hw5⟩ ↦ ?_
  obtain ⟨hR5, hwp5, hx5, -⟩ := hS.at hw5.w
  refine WP.then (oodWC_spec d5 hwp5 hR5 hx5 hxs hxl) fun s6 ⟨r9', r10', m6, d6⟩ ↦ ?_
  obtain ⟨-, -, -, hsc6⟩ := hS.at hw5.w
  have hws : ws.size = (wsAt layout x ringW claims claims.size).length := by
    rw [← Array.length_toList, hv]
  refine WP.mono (accC_spec (ws := ws) (by rw [d6, d5]) (by rw [m6]; exact hwp5) r9' r10'
    (by rw [m6]; exact hE5) (by rw [m6]; exact hsc6) (by rw [hss, hlen, hws]; omega)
    (hw5.regs m6 d6)) ?_ fun _ h ↦ h
  rintro s7 ⟨hE7, hw7, -, -⟩
  have hpush : ws.push (ood.weight.eval x) =
      (stackClaims layout target point coeffs claims ood).map (·.weight.eval x) := by
    apply Array.ext'
    rw [Array.toList_push, hv, hcw]
  have ha := hE7.acc
  rw [hpush, Array.size_map, ← hss, Array.extract_eq_self_of_le le_rfl] at ha
  exact ⟨ha, hw7.w.fr, hw7.w.only⟩

end NativeVm.Code.P7
