module

public import NativeVm.Transcript.Sim
public import NativeVm.Transcript.QueryOpen

/-!
# A Merkle climb

`climbStep_spec`: one level, the node in the scratch lanes and the sibling at `r9`, hashed into the
parent (`parentAt`); `climbLoop_spec`: the whole path (`climbK`); `checkRoot_spec`: the top against
the query's root. They write only the scratch area and the climb's input (`ClimbW`).
-/

@[expose] public section

namespace NativeVm.Transcript

open Native LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.Compile
open LeanVM.Protocol.KeccakHash

variable {s : QState} {E : QState → Prop}

/-- The context's words a climb writes: the scratch area and the climb's input. -/
def ClimbW (ctx : UInt64) (a : UInt64) : Prop :=
  CtxIn ctx scratchW (scratchW + Keccak.scratchWords) a ∨ CtxIn ctx climbW qRootW a

/-! ## Digests as words -/

theorem getD_toList {n : Nat} (v : Vector UInt64 n) {k : Nat} (hk : k < n) : v.toList.getD k 0 = v[k] := by
  simp [List.getD_eq_getElem?_getD, hk]

theorem vec_ext_getD {n : Nat} {a b : Vector UInt64 n} (h : ∀ k < n, a.toList.getD k 0 = b.toList.getD k 0) :
    a = b := Vector.ext fun k hk ↦ by rw [← getD_toList a hk, ← getD_toList b hk, h k hk]

theorem digestBytes_length (a : Digest) : (digestBytes a).length = 32 := by
  obtain ⟨⟨l⟩, hl⟩ := a
  match l, hl with
  | [_, _, _, _], _ => rfl

theorem wordsBytes_digests (a b : Digest) :
    Keccak.wordsBytes (a.toList ++ b.toList) = digestBytes a ++ digestBytes b := by
  simp only [Keccak.wordsBytes, digestBytes, List.flatMap_append]

theorem holds_digests (a b : Digest) : Keccak.HoldsBytes (a.toList ++ b.toList) 64 := by
  refine ⟨by simp, fun x hx ↦ ?_⟩
  rw [wordsBytes_digests, List.drop_eq_nil_of_le (by simp [digestBytes_length])] at hx
  cases hx

theorem take_digests (a b : Digest) :
    (Keccak.wordsBytes (a.toList ++ b.toList)).take 64 = digestBytes a ++ digestBytes b := by
  rw [wordsBytes_digests, List.take_of_length_le (by simp [digestBytes_length])]

/-! ## Registers -/

theorem and_one_eq_zero {q : Nat} (hq : q < 2 ^ 64) :
    (q.toUInt64 &&& (1 : Int64).toUInt64 == 0) = decide (q % 2 = 0) := by
  have h : (q.toUInt64 &&& (1 : Int64).toUInt64).toNat = q % 2 := by
    rw [UInt64.toNat_and, toNat_toUInt64 hq, show ((1 : Int64).toUInt64).toNat = 1 from rfl,
      Nat.and_one_is_mod]
  rw [Bool.eq_iff_iff, beq_iff_eq, decide_eq_true_eq, ← UInt64.toNat_inj, h]
  rfl

theorem toUInt64_shr1 {q : Nat} (hq : q < 2 ^ 64) : q.toUInt64 >>> (1 : Nat).toUInt64 = (q / 2).toUInt64 := by
  apply UInt64.toNat_inj.mp
  simp only [UInt64.toNat_shiftRight, toNat_toUInt64 hq, toNat_toUInt64 (show q / 2 < 2 ^ 64 by omega),
    toNat_toUInt64 (show 1 < 2 ^ 64 by omega), Nat.shiftRight_eq_div_pow]

theorem sub1_toUInt64 {c : Nat} (hc : 0 < c) (hc' : c < 2 ^ 64) : c.toUInt64 - 1 = (c - 1).toUInt64 := by
  apply UInt64.toNat_inj.mp
  rw [UInt64.toNat_sub_of_le _ _ (by rw [UInt64.le_iff_toNat_le, toNat_toUInt64 hc']; simp; omega),
    toNat_toUInt64 hc', toNat_toUInt64 (by omega)]
  simp

/-! ## Copies from `r9` -/

/-- Copy piece `t` from `r9`'s words to the context's. -/
def copyInP (dst t : Nat) : List Stmt :=
  [I (.load .rax (at_ .r9 (wdisp t))), I (.store (cw (dst + t)) .rax)]

/-- **A copy of words at `r9` into the context's.** -/
theorem copyIn_spec {ctx O : UInt64} {b dst n : Nat} {f : Nat → UInt64} (hrdi : s.reg .rdi = ctx)
    (hr9 : s.reg .r9 = wd O b) (hdst : dst + n ≤ 2 ^ 61)
    (hv : ∀ t < n, s.mem (wd O (b + t)) = some (f t))
    (hne : ∀ t < n, ¬ CtxIn ctx dst (dst + n) (wd O (b + t)))
    (hd : ∀ t < n, (s.mem (wd ctx (dst + t))).isSome) :
    WP (blk ((List.range n).flatMap (copyInP dst))) s (fun s' ↦
      (∀ t < n, s'.mem (wd ctx (dst + t)) = some (f t)) ∧
      Keep (CtxIn ctx dst (dst + n)) s.mem s'.mem ∧ RegsFrame [.rax] s s') E := by
  refine Keccak.Proof.wp_range_flatMap (s := s) _ (fun j s' ↦ (∀ t < j, s'.mem (wd ctx (dst + t)) =
    some (f t)) ∧ Keep (CtxIn ctx dst (dst + j)) s.mem s'.mem ∧ RegsFrame [.rax] s s') n ?_
    ⟨fun t ht ↦ absurd ht (by omega), Keep.refl _ _, rf_refl _ _⟩
  intro j hj s' ⟨hw, hk, hr⟩
  have hrdi' : s'.reg .rdi = ctx := (hr _ (by simp)).trans hrdi
  have hr9' : s'.reg .r9 = wd O b := (hr _ (by simp)).trans hr9
  have hsj : s'.mem (wd O (b + j)) = some (f j) := by
    rw [hk _ (fun h ↦ hne j hj (h.mono le_rfl (by omega)))]
    exact hv j hj
  refine wp_load (eval_wd hr9' _) hsj (wp_store (eval_cw (by reg_simp; exact hrdi') _) ?_
    (wp_done ⟨?_, ?_, ?_⟩))
  · rw [QState.setReg_mem, hk.ctx (by omega) (by omega) (by omega)]
    exact hd j hj
  · intro t ht
    simp only [QState.setMem_mem, QState.setReg_mem, QState.setReg_reg, ↓reduceIte]
    split
    · rename_i e
      rw [wd_inj (by omega) (by omega)] at e
      rw [show t = j by omega]
    · rename_i e
      rw [wd_inj (by omega) (by omega)] at e
      exact hw t (by omega)
  · refine Keep.update (hk.mono fun a ha ↦ ha.mono le_rfl (by omega)) (CtxIn.word (by omega)
      (by omega)) _
  · exact rf_setMem (rf_setReg hr (by simp) _) _ _

/-! ## One level -/

/-- The climb's input: the node left when the position is even. -/
def climbInput (node sib : Digest) (q : Nat) : List UInt64 :=
  if q % 2 = 0 then node.toList ++ sib.toList else sib.toList ++ node.toList

theorem climbInput_length (node sib : Digest) (q : Nat) : (climbInput node sib q).length = 8 := by
  unfold climbInput; split <;> simp

theorem climbInput_holds (node sib : Digest) (q : Nat) : Keccak.HoldsBytes (climbInput node sib q) 64 := by
  unfold climbInput; split <;> exact holds_digests _ _

theorem climbInput_hash (node sib : Digest) (q : Nat) :
    keccak256 ((Keccak.wordsBytes (climbInput node sib q)).take 64) = parentAt node q sib := by
  unfold climbInput parentAt; split <;> rw [take_digests]

theorem climbInput_lo {node sib : Digest} {q t : Nat} (hq : q % 2 = 0) (ht : t < 4) :
    (climbInput node sib q).getD t 0 = node.toList.getD t 0 := by
  rw [climbInput, ite_eq_left_of_eq_true _ _ (eq_true hq), List.getD_append _ _ _ _ (by simpa using ht)]

theorem climbInput_hi {node sib : Digest} {q t : Nat} (hq : q % 2 = 0) :
    (climbInput node sib q).getD (4 + t) 0 = sib.toList.getD t 0 := by
  rw [climbInput, ite_eq_left_of_eq_true _ _ (eq_true hq), List.getD_append_right _ _ _ _ (by simp)]
  simp

theorem climbInput_lo' {node sib : Digest} {q t : Nat} (hq : ¬ q % 2 = 0) (ht : t < 4) :
    (climbInput node sib q).getD t 0 = sib.toList.getD t 0 := by
  rw [climbInput, ite_eq_right_of_eq_false _ _ (eq_false hq), List.getD_append _ _ _ _ (by simpa using ht)]

theorem climbInput_hi' {node sib : Digest} {q t : Nat} (hq : ¬ q % 2 = 0) :
    (climbInput node sib q).getD (4 + t) 0 = node.toList.getD t 0 := by
  rw [climbInput, ite_eq_right_of_eq_false _ _ (eq_false hq), List.getD_append_right _ _ _ _ (by simp)]
  simp

theorem not_climbW {ctx a : UInt64} (h : ∀ k < ctxEnd, a ≠ wd ctx k) : ¬ ClimbW ctx a := by
  rintro (⟨k, -, hk, rfl⟩ | ⟨k, -, hk, rfl⟩)
  · exact h k (by lay_omega) rfl
  · exact h k (by lay_omega) rfl

/-- The climb's input in place, the siblings' order by the position's low bit. -/
theorem climbIn_spec {ctx O : UInt64} {b q : Nat} {node sib : Digest}
    (hrdi : s.reg .rdi = ctx) (hdom : Dom ctx s.mem)
    (hnode : ∀ k < 4, s.mem (wd ctx (scratchW + k)) = some (node.toList.getD k 0))
    (hr9 : s.reg .r9 = wd O b)
    (hsib : ∀ l < 4, s.mem (wd O (b + l)) = some (sib.toList.getD l 0))
    (hO : ∀ l < 4, ∀ k < ctxEnd, wd O (b + l) ≠ wd ctx k)
    (hr14 : s.reg .r14 = q.toUInt64) (hq : q < 2 ^ 64) :
    WP (.ite (.test true .r14 (.imm 1))
      (blk [copyCtx scratchW climbW 4, blk ((List.range 4).flatMap (copyInP (climbW + 4)))])
      (blk [blk ((List.range 4).flatMap (copyInP climbW)), copyCtx scratchW (climbW + 4) 4])) s
      (fun s₁ ↦ (∀ t < 8, s₁.mem (wd ctx (climbW + t)) = some ((climbInput node sib q).getD t 0)) ∧
        Keep (CtxIn ctx climbW (climbW + 8)) s.mem s₁.mem ∧ RegsFrame [.rax] s s₁) E := by
  have hc : (Cond.test true .r14 (.imm 1)).eval s = decide (q % 2 = 0) := by
    show (((s.reg .r14 &&& (1 : Int64).toUInt64) == 0) == true) = decide (q % 2 = 0)
    rw [hr14, and_one_eq_zero hq]
    cases decide (q % 2 = 0) <;> rfl
  have hne : ∀ lo hi, hi ≤ ctxEnd → ∀ t < 4, ¬ CtxIn ctx lo hi (wd O (b + t)) :=
    fun lo hi hhi t ht ⟨k, _, hk, e⟩ ↦ hO t ht k (by omega) e
  by_cases hq2 : q % 2 = 0
  · refine wp_ite_true (by rw [hc, decide_eq_true hq2]) ?_
    refine wp_then (copyCtx_spec (f := fun t ↦ node.toList.getD t 0) hrdi (by lay_omega)
      (by lay_omega) (by lay_omega) hnode (fun t ht ↦ hdom _ (by lay_omega))) ?_
    rintro s₁ ⟨h1, k1, r1⟩
    refine WP.mono (copyIn_spec (f := fun t ↦ sib.toList.getD t 0) ((r1 _ (by simp)).trans hrdi)
      ((r1 _ (by simp)).trans hr9) (by lay_omega)
      (fun t ht ↦ by rw [k1 _ (hne _ _ (by lay_omega) t ht)]; exact hsib t ht)
      (hne _ _ (by lay_omega)) (fun t ht ↦ by
        rw [k1.ctx (by omega) (by lay_omega) (by lay_omega)]; exact hdom _ (by lay_omega)))
      (fun s₂ ⟨h2, k2, r2⟩ ↦ ⟨fun t ht ↦ ?_, ?_, rf_trans r1 r2⟩) (fun _ h ↦ h)
    · by_cases ht4 : t < 4
      · rw [k2.ctx (by omega) (by lay_omega) (by lay_omega), h1 t ht4, climbInput_lo hq2 ht4]
      · obtain ⟨u, rfl⟩ : ∃ u, t = 4 + u := ⟨t - 4, by omega⟩
        rw [← Nat.add_assoc, h2 u (by omega), climbInput_hi hq2]
    · exact k1.trans k2 (fun a h ↦ h.mono le_rfl (by omega)) (fun a h ↦ h.mono (by omega) (by omega))
  · refine wp_ite_false (by rw [hc, decide_eq_false hq2]) ?_
    refine wp_then (copyIn_spec (f := fun t ↦ sib.toList.getD t 0) (dst := climbW) hrdi hr9
      (by lay_omega) hsib (hne _ _ (by lay_omega)) (fun t ht ↦ hdom _ (by lay_omega))) ?_
    rintro s₁ ⟨h1, k1, r1⟩
    refine WP.mono (copyCtx_spec (f := fun t ↦ node.toList.getD t 0) ((r1 _ (by simp)).trans hrdi)
      (by lay_omega) (by lay_omega) (by lay_omega)
      (fun t ht ↦ by rw [k1.ctx (by lay_omega) (by lay_omega) (by lay_omega)]; exact hnode t ht)
      (fun t ht ↦ by
        rw [k1.ctx (by omega) (by lay_omega) (by lay_omega)]; exact hdom _ (by lay_omega)))
      (fun s₂ ⟨h2, k2, r2⟩ ↦ ⟨fun t ht ↦ ?_, ?_, rf_trans r1 r2⟩) (fun _ h ↦ h)
    · by_cases ht4 : t < 4
      · rw [k2.ctx (by omega) (by lay_omega) (by lay_omega), h1 t ht4, climbInput_lo' hq2 ht4]
      · obtain ⟨u, rfl⟩ : ∃ u, t = 4 + u := ⟨t - 4, by omega⟩
        rw [← Nat.add_assoc, h2 u (by omega), climbInput_hi' hq2]
    · exact k1.trans k2 (fun a h ↦ h.mono le_rfl (by omega)) (fun a h ↦ h.mono (by omega) (by omega))

/-- **One level of a climb**: the node at the scratch lanes and the sibling at `r9` hashed into
the parent; the position halved, `r9` at the next sibling, `r15` counted down. -/
theorem climbStep_spec {ctx O : UInt64} {b q c : Nat} {node sib : Digest}
    (hrdi : s.reg .rdi = ctx) (hdom : Dom ctx s.mem)
    (hnode : ∀ k < 4, s.mem (wd ctx (scratchW + k)) = some (node.toList.getD k 0))
    (hr9 : s.reg .r9 = wd O b)
    (hsib : ∀ l < 4, s.mem (wd O (b + l)) = some (sib.toList.getD l 0))
    (hO : ∀ l < 4, ∀ k < ctxEnd, wd O (b + l) ≠ wd ctx k)
    (hr14 : s.reg .r14 = q.toUInt64) (hq : q < 2 ^ 64)
    (hr15 : s.reg .r15 = c.toUInt64) (hc : 0 < c) (hc' : c < 2 ^ 64) :
    WP climbStep s (fun s' ↦
      (∀ k < 4, s'.mem (wd ctx (scratchW + k)) = some ((parentAt node q sib).toList.getD k 0)) ∧
      s'.reg .r9 = wd O (b + 4) ∧ s'.reg .r14 = (q / 2).toUInt64 ∧
      s'.reg .r15 = (c - 1).toUInt64 ∧ Keep (ClimbW ctx) s.mem s'.mem ∧
      RegsFrame [.rax, .rbx, .rcx, .rdx, .rsi, .r8, .r9, .r14, .r15] s s') E := by
  unfold climbStep
  refine wp_then (climbIn_spec hrdi hdom hnode hr9 hsib hO hr14 hq) ?_
  rintro s₁ ⟨h1, k1, r1⟩
  refine wp_reg rfl (wp_reg rfl ?_)
  have hrdi₁ : s₁.reg .rdi = ctx := (r1 _ (by simp)).trans hrdi
  refine wp_then (hashAt_spec (ctx := ctx) (ws := climbInput node sib q) (len := 64)
    (by reg_simp; exact hrdi₁) (climbInput_holds _ _ _) (by reg_simp; rfl) (by norm_num)
    (fun i hi ↦ ?_) (fun k hk ↦ ?_) (fun i hi k hk ↦ ?_)) ?_
  · rw [climbInput_length] at hi
    reg_simp
    rw [eval_cw hrdi₁, wd_add, h1 i hi, List.getD_eq_getElem _ _ (by rw [climbInput_length]; exact hi)]
  · reg_simp
    rw [k1.ctx (by lay_omega) (by lay_omega) (by lay_omega)]
    exact hdom _ (by lay_omega)
  · rw [climbInput_length] at hi
    reg_simp
    rw [eval_cw hrdi₁, wd_add, Ne, wd_inj (by lay_omega) (by lay_omega)]
    lay_omega
  rintro s₂ ⟨h2, -, k2, r2⟩
  refine wp_reg rfl (wp_reg rfl (wp_reg rfl (wp_done ⟨fun k hk ↦ ?_, ?_, ?_, ?_, ?_, ?_⟩)))
  · reg_simp
    rw [h2 k hk, climbInput_hash, getD_toList _ hk]
  · reg_simp
    rw [r2 _ (by simp)]
    reg_simp
    rw [r1 _ (by simp), hr9, ← wd_add]
    rfl
  · reg_simp
    rw [r2 _ (by simp)]
    reg_simp
    rw [r1 _ (by simp), hr14, ← toUInt64_shr1 hq]
  · reg_simp
    rw [r2 _ (by simp)]
    reg_simp
    rw [r1 _ (by simp), hr15, ← sub1_toUInt64 hc hc']
  · refine (k1.trans k2 (V := ClimbW ctx) (fun a h ↦ .inr (h.mono le_rfl (by lay_omega)))
      (fun a h ↦ .inl h)).mono fun a h ↦ h
  · have r12 : RegsFrame [.rsi, .rbx] s₁ ((s₁.setReg Reg64.rsi ((cw climbW).eval s₁)).setReg Reg64.rbx
        (Int64.toUInt64 64)) := by rf_tac
    rf_tac
    exact rf_trans r1 (rf_trans (l'' := [.rax, .rbx, .rcx, .rdx, .rsi, .r8]) r12 r2)

/-! ## The path -/

/-- **A climb**: from the node at the scratch lanes, position `q` in `r14`, the path's digests at
`r9` and their count in `r15`, the path's top at the scratch lanes. -/
theorem climbLoop_spec {ctx O : UInt64} {b q : Nat} {node : Digest} {path : List Digest}
    (hrdi : s.reg .rdi = ctx) (hdom : Dom ctx s.mem)
    (hnode : ∀ k < 4, s.mem (wd ctx (scratchW + k)) = some (node.toList.getD k 0))
    (hr9 : s.reg .r9 = wd O b)
    (hpath : ∀ d < path.length, ∀ l < 4,
      s.mem (wd O (b + 4 * d + l)) = some ((path.getD d default).toList.getD l 0))
    (hO : ∀ i < 4 * path.length, ∀ k < ctxEnd, wd O (b + i) ≠ wd ctx k)
    (hr14 : s.reg .r14 = q.toUInt64) (hq : q < 2 ^ 64)
    (hr15 : s.reg .r15 = path.length.toUInt64) (hlen : path.length < 2 ^ 64) :
    WP (.loop (.cmp .ne .r15 (.imm 0)) climbStep) s (fun s' ↦
      (∀ k < 4, s'.mem (wd ctx (scratchW + k)) = some ((climbK node q path).toList.getD k 0)) ∧
      Keep (ClimbW ctx) s.mem s'.mem ∧
      RegsFrame [.rax, .rbx, .rcx, .rdx, .rsi, .r8, .r9, .r14, .r15] s s') E := by
  set n := path.length
  refine WP.loop (fun s' ↦ ∃ d ≤ n, ∃ (nd : Digest) (q' : Nat), q' < 2 ^ 64 ∧
      climbK nd q' (path.drop d) = climbK node q path ∧
      (∀ k < 4, s'.mem (wd ctx (scratchW + k)) = some (nd.toList.getD k 0)) ∧
      s'.reg .r9 = wd O (b + 4 * d) ∧ s'.reg .r14 = q'.toUInt64 ∧ s'.reg .r15 = (n - d).toUInt64 ∧
      Keep (ClimbW ctx) s.mem s'.mem ∧
      RegsFrame [.rax, .rbx, .rcx, .rdx, .rsi, .r8, .r9, .r14, .r15] s s' ∧
      ∀ a, (s'.mem a).isSome = (s.mem a).isSome)
    (fun s' ↦ (s'.reg .r15).toNat) ⟨0, by omega, node, q, hq, rfl, hnode, by rw [hr9]; rfl, hr14,
      by rw [hr15]; rfl, Keep.refl _ _, rf_refl _ _, fun _ ↦ rfl⟩ ?_ ?_
  · rintro s' ⟨d, hd, nd, q', hq', hcl, h1, h9, h14, h15, hk, hr, hs⟩ hc
    have hdn : d < n := by
      rw [cond_ne, rhs_imm, h15, bne_iff_ne, ne_eq] at hc
      by_contra h
      exact hc (by rw [show n - d = 0 by omega]; rfl)
    have hpd : path.drop d = path[d] :: path.drop (d + 1) := List.drop_eq_getElem_cons hdn
    refine WP.mono (WP.frame (climbStep_spec (O := O) (b := b + 4 * d) (sib := path[d])
      ((hr _ (by simp)).trans hrdi) (hdom.of_isSome hs) h1 h9 (fun l hl ↦ ?_)
      (fun l hl k hk ↦ by rw [Nat.add_assoc]; exact hO _ (by omega) k hk) h14 hq' h15 (by omega)
      (by omega))) ?_ (fun _ h ↦ h.1)
    · rw [hk _ (not_climbW fun k hk ↦ by rw [Nat.add_assoc]; exact hO _ (by omega) k hk),
        hpath d hdn l hl, List.getD_eq_getElem _ _ hdn]
    rintro s'' ⟨⟨g1, g9, g14, g15, gk, gr⟩, gs, -⟩
    refine ⟨⟨d + 1, by omega, parentAt nd q' path[d], q' / 2, by omega, ?_, g1, ?_, g14, ?_,
      hk.trans gk (fun _ h ↦ h) (fun _ h ↦ h), rf_trans hr gr, fun a ↦ (gs a).trans (hs a)⟩, ?_⟩
    · rw [← hcl, hpd, climbK_cons]
    · rw [g9]; congr 1
    · rw [g15]; congr 1
    · rw [g15, h15, toNat_toUInt64 (by omega), toNat_toUInt64 (by omega)]
      omega
  · rintro s' ⟨d, hd, nd, q', hq', hcl, h1, h9, h14, h15, hk, hr, hs⟩ hc
    have hdn : d = n := by
      rw [cond_ne, rhs_imm, h15, bne_eq_false_iff_eq] at hc
      have := congrArg UInt64.toNat hc
      rw [toNat_toUInt64 (by omega), show (Int64.toUInt64 0).toNat = 0 from rfl] at this
      omega
    rw [hdn, List.drop_length, climbK_nil] at hcl
    exact ⟨fun k hk ↦ by rw [h1 k hk, hcl], hk, hr⟩

/-- **The climb's top against the root.** -/
theorem checkRoot_spec {ctx : UInt64} {top root : Digest} (hrdi : s.reg .rdi = ctx)
    (htop : ∀ k < 4, s.mem (wd ctx (scratchW + k)) = some (top.toList.getD k 0))
    (hroot : ∀ k < 4, s.mem (wd ctx (qRootW + k)) = some (root.toList.getD k 0)) :
    WP checkRoot s (fun s' ↦ top = root ∧ s'.mem = s.mem ∧ RegsFrame [.rax, .rcx] s s')
      (fun s' ↦ top ≠ root ∧ s'.mem = s.mem ∧ RegsFrame [.rax, .rcx] s s') := by
  unfold checkRoot
  refine WP.mono (Keccak.Proof.wp_range_flatMap (s := s) _ (fun j s' ↦
    (∀ k < j, top.toList.getD k 0 = root.toList.getD k 0) ∧ s'.mem = s.mem ∧
      RegsFrame [.rax, .rcx] s s') 4 ?_ ⟨fun k hk ↦ absurd hk (by omega), rfl, rf_refl _ _⟩)
    (fun s' ⟨h, hm, hr⟩ ↦ ⟨vec_ext_getD h, hm, hr⟩) (fun _ h ↦ h)
  intro j hj s' ⟨hw, hm, hr⟩
  have hrdi' : s'.reg .rdi = ctx := (hr _ (by simp)).trans hrdi
  refine wp_load (eval_cw hrdi' _) (by rw [hm]; exact htop j hj) ?_
  refine wp_load (eval_cw (by reg_simp; exact hrdi') _) (by rw [QState.setReg_mem, hm]; exact hroot j hj) ?_
  by_cases he : top.toList.getD j 0 = root.toList.getD j 0
  · refine wp_failIf (by rw [cond_ne, rhs_reg]; reg_simp; rw [he]; exact bne_self_eq_false _)
      (wp_done ⟨fun k hk ↦ ?_, by rw [QState.setReg_mem, QState.setReg_mem, hm], by rf_tac; exact hr⟩)
    by_cases hkj : k < j
    · exact hw k hkj
    · rw [show k = j by omega]; exact he
  · refine wp_failIf_fail (by rw [cond_ne, rhs_reg]; reg_simp; exact bne_iff_ne.mpr he)
      ⟨fun e ↦ he (by rw [e]), by rw [QState.setReg_mem, QState.setReg_mem, hm], by rf_tac; exact hr⟩

end NativeVm.Transcript
