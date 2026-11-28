module

public import NativeRustcVmX64.Whir.BasisWEval.Exec
public import NativeRustcVmX64.Whir.MathFrame
public import NativeRustcVmX64.Spec.Whir
public import NativeRustcVmX64.Spec.Layout
public import NativeRustcVm.Whir.BasisEval
public import NativeRustcVm.Tables.Same

/-!
# `BasisW::eval`: its frame, its inputs, the weights (x86-64)

`m0` is the entry's state. `Fb m0 o st`: the frame (`Fr`, 160 bytes, the slots of `Exec`), RSP at
offset `o`, no byte outside the stack changed (until the result's stores, `b26`, `b27`), so every
input reads as at the entry (`same_of`). `FW m0 d o v`: the frame's word at offset `o` is `v`.

`In m0 ba b v`: the precondition with the basis's data `v` (`Vals`) named. `ws v x j`: the weights
the code has met after `j` column claims (the ring-switched claim's, then those with a
placement).
-/

namespace NativeRustcVmX64.Whir.BasisWEval

open NativeRustcX64 NativeRustcX64.Sym NativeVm.Model LeanVM.Parameters
open NativeRustcVmX64.Transcript NativeRustcVm.Whir NativeRustcVm.Layout NativeRustcVm.Ring
open NativeRustcVm.KeccakGkr (KeccakOutAt outBytes)
open NativeRustcVm.Transcript (off off_add off_zero toNat_off)
open LeanVM.Protocol.Verifier (qkeccak Placement)

@[expose] public section

/-- The frame's base: 160 bytes below the entry's RSP. -/
abbrev fb (m0 : MachineData) : BitVec 64 := stackBelow m0 160

/-- **The frame** before the result's stores, RSP at offset `o`. -/
abbrev Fb (m0 : MachineData) (o : Nat) (d : MachineData) : Prop :=
  Fr m0 160 basisWEvalStack slots (fun _ ↦ False) o d

/-- The frame's word at offset `o` holds `v`. -/
abbrev FW (m0 d : MachineData) (o : Nat) (v : BitVec 64) : Prop :=
  NativeRustcVm.WordAt d.dmem (off (fb m0) o) (UInt64.ofBitVec v)

/-- A block's environment: the frame, then `rest`. -/
abbrev envB (m0 d : MachineData) (rest : List (BitVec 64 × Nat)) (ret : BitVec 64 := 0) : Env :=
  frameEnv m0 d 160 rest (fun _ ↦ 0) ret

/-- The data a basis refers to. -/
structure Vals where
  L : LayoutW
  target : EW
  coeffs : Array EW
  kp : Array EW
  slices : Array EW
  cs : Array ColumnClaimW
  z : Array EW
  value : EW

/-- **The precondition**, the basis's data `v` named. -/
structure In (m0 : MachineData) (ba : BasisAddrs) (b : BasisW) (v : Vals) : Prop where
  pre : BasisWEvalPre ba b m0
  log : v.L.stackLog ≤ 30
  layout : LayoutWAt m0.dmem ba.layout v.L
  ring : RingWAt m0.dmem ba.ring v.target v.coeffs
  keccak : KeccakOutAt m0.dmem ba.keccak v.kp v.slices
  claims : ClaimsWAt m0.dmem ba.claims v.cs
  ood : EqClaimAt m0.dmem ba.ood v.z v.value
  eq : b.claims = stackClaims v.L v.target v.kp v.coeffs v.cs v.z v.value

/-- The point. -/
def xpt (m0 : MachineData) : Array EW := slice m0 (reg m0 .rdx) (reg m0 .rcx)

/-- The ring-switched claim's weight at `x`. -/
def ringW (v : Vals) (x : Array EW) : EW :=
  StackWeight.eval (.ring (v.L.placement qkeccak) v.kp v.coeffs) x

/-- The weights met after `j` column claims. -/
def ws (v : Vals) (x : Array EW) (j : Nat) : Array EW :=
  (ringW v x :: colWs v.L x v.cs j).toArray

/-- Column claim `i`'s address. -/
def cA (ba : BasisAddrs) (i : Nat) : BitVec 64 := off ba.claims (8 + 608 * i)

/-- The placement entry of column `c`. -/
def pA (ba : BasisAddrs) (c : Nat) : BitVec 64 := off ba.layout (120 + 24 * c)

/-- Scale `j`'s address. -/
def sA (ba : BasisAddrs) (j : Nat) : BitVec 64 := off ba.scales (16 * j)

end

public section

variable {m0 : MachineData} {ba : BasisAddrs} {b : BasisW} {v : Vals}

theorem in_of_pre (h : BasisWEvalPre ba b m0) : ∃ v, In m0 ba b v := by
  obtain ⟨L, target, coeffs, kp, slices, cs, z, value, hlog, hL, hR, hK, hC, hO, heq⟩ :=
    h.2.1.data.holds
  exact ⟨⟨L, target, coeffs, kp, slices, cs, z, value⟩, h, hlog, hL, hR, hK, hC, hO, heq⟩

theorem stack_le : 144 + ewMulStack ≤ basisWEvalStack ∧
    160 + ringClaimWeightStack ≤ basisWEvalStack ∧ 160 + columnWeightStack ≤ basisWEvalStack ∧
    144 + eqEvalStack ≤ basisWEvalStack ∧ 144 + layoutWPlacementStack ≤ basisWEvalStack ∧
    160 ≤ basisWEvalStack := by
  unfold basisWEvalStack layoutWPlacementStack; omega

theorem slots_le : ∀ p ∈ slots, p.1 + 8 ≤ 160 := by decide
theorem slots_cs : ∀ p ∈ slots, calleeSaved p.2 = true := by decide
/-- The slots against a call at `16` changing nothing in the frame. -/
theorem slots_c16 : ∀ p ∈ slots, 16 ≤ p.1 ∧ 24 + 0 ≤ p.1 ∧ p.1 + 8 ≤ 160 := by decide
/-- The slots against a call at `0` writing the `Option<EW>` at `80`. -/
theorem slots_c0 : ∀ p ∈ slots, 0 ≤ p.1 ∧ 80 + 24 ≤ p.1 ∧ p.1 + 8 ≤ 160 := by decide

theorem In.stackOk (h : In m0 ba b v) : StackOk m0 basisWEvalStack := h.pre.1

theorem In.hN (h : In m0 ba b v) : basisWEvalStack ≤ (rspOf m0).toNat := h.pre.1.1

/-! ## Inputs -/

/-- The `BasisW`. -/
theorem In.basis (h : In m0 ba b v) : WhirIn m0 (reg m0 .rsi) basisBytes basisWEvalStack :=
  h.pre.2.2.1.1

theorem In.area (h : In m0 ba b v) {r : NativeRustcVm.Region} (hr : r ∈ ba.regions) :
    WhirIn m0 r.addr r.size basisWEvalStack :=
  (h.pre.2.2.1.2.2 r hr).1

theorem In.scales (h : In m0 ba b v) : WhirIn m0 ba.scales (16 * ba.count) basisWEvalStack :=
  h.area (r := ⟨ba.scales, 16 * ba.count⟩) (by simp [BasisAddrs.regions])

theorem In.layoutIn (h : In m0 ba b v) : WhirIn m0 ba.layout layoutBytes basisWEvalStack :=
  h.area (r := ⟨ba.layout, layoutBytes⟩) (by unfold BasisAddrs.regions; exact .tail _ (.head _))

theorem In.ringIn (h : In m0 ba b v) : WhirIn m0 ba.ring ringWBytes basisWEvalStack :=
  h.area (r := ⟨ba.ring, ringWBytes⟩) (by
    unfold BasisAddrs.regions; exact .tail _ (.tail _ (.head _)))

theorem In.keccakIn (h : In m0 ba b v) : WhirIn m0 ba.keccak outBytes basisWEvalStack :=
  h.area (r := ⟨ba.keccak, outBytes⟩) (by
    unfold BasisAddrs.regions; exact .tail _ (.tail _ (.tail _ (.head _))))

theorem In.claimsIn (h : In m0 ba b v) : WhirIn m0 ba.claims claimsBytes basisWEvalStack :=
  h.area (r := ⟨ba.claims, claimsBytes⟩) (by
    unfold BasisAddrs.regions; exact .tail _ (.tail _ (.tail _ (.tail _ (.head _)))))

theorem In.oodIn (h : In m0 ba b v) : WhirIn m0 ba.ood eqClaimBytes basisWEvalStack :=
  h.area (r := ⟨ba.ood, eqClaimBytes⟩) (by
    unfold BasisAddrs.regions; exact .tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.head _))))))

theorem In.point (h : In m0 ba b v) : SliceOk m0 (reg m0 .rdx) (reg m0 .rcx) basisWEvalStack :=
  h.pre.2.2.2.2.1

theorem In.out (h : In m0 ba b v) : WhirIn m0 (reg m0 .rdi) 24 basisWEvalStack :=
  h.pre.2.2.2.2.2.1

/-- The areas the blocks read together are apart. -/
theorem In.aparts (h : In m0 ba b v) :
    NativeRustcVm.Apart (reg m0 .rsi) basisBytes ba.keccak outBytes ∧
      NativeRustcVm.Apart (reg m0 .rsi) basisBytes ba.claims claimsBytes ∧
      NativeRustcVm.Apart (reg m0 .rsi) basisBytes ba.ood eqClaimBytes ∧
      NativeRustcVm.Apart ba.layout layoutBytes ba.claims claimsBytes := by
  have hp := h.pre.2.2.2.2.2.2
  simp only [BasisApart, BasisAddrs.regions, List.pairwise_cons, List.mem_cons,
    List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hp
  exact ⟨hp.1.2.2.2.1, hp.1.2.2.2.2.1, hp.1.2.2.2.2.2, hp.2.2.1.2.2.1⟩

/-! ## Sub-areas -/

/-- An area inside an input. -/
theorem WhirIn.sub' {m : MachineData} {a : BitVec 64} {N o n S : Nat} (h : WhirIn m a N S)
    (hle : o + n ≤ N) : WhirIn m (off a o) n S :=
  WhirIn.sub h hle

theorem WhirIn.mono' {m : MachineData} {a : BitVec 64} {N n S : Nat} (h : WhirIn m a N S)
    (hle : n ≤ N) : WhirIn m a n S := by
  have := WhirIn.sub (o := 0) (n := n) h (by omega)
  rwa [NativeRustcVm.addr_add_zero] at this

/-- Areas inside apart areas are apart. -/
theorem apart_sub {a b : BitVec 64} {n m o n' o' m' : Nat} (h : NativeRustcVm.Apart a n b m)
    (ha : NativeRustcVm.NoWrap a n) (hb : NativeRustcVm.NoWrap b m) (h1 : o + n' ≤ n)
    (h2 : o' + m' ≤ m) : NativeRustcVm.Apart (off a o) n' (off b o') m' := by
  unfold NativeRustcVm.NoWrap at ha hb
  unfold NativeRustcVm.Apart at h ⊢
  have e1 := NativeRustcVm.toNat_add_ofNat_le (a := a) (i := o) (by omega)
  have e2 := NativeRustcVm.toNat_add_ofNat_le (a := b) (i := o') (by omega)
  simp only [off]
  omega

/-! ## The frame -/

section
variable {o : Nat} {st : MachineData}

theorem In.frame_noWrap (h : In m0 ba b v) : NativeRustcVm.NoWrap (fb m0) 168 :=
  NativeRustcVmX64.Transcript.frame_noWrap h.stackOk stack_le.2.2.2.2.2

/-- The frame is mapped in a state that kept the entry's bytes. -/
theorem In.frame_mapped (h : In m0 ba b v) (hk : Kept m0.dmem st.dmem) :
    NativeRustcVm.Mapped st.dmem (fb m0) 168 :=
  NativeRustcVm.Transcript.Mapped.keeps (NativeRustcVmX64.Transcript.frame_mapped h.stackOk
    stack_le.2.2.2.2.2) hk

/-- An input is apart from the frame. -/
theorem In.frame_apart (h : In m0 ba b v) {a : BitVec 64} {n : Nat}
    (ha : WhirIn m0 a n basisWEvalStack) : NativeRustcVm.Apart a n (fb m0) 168 :=
  apart_frame ha.2 h.hN stack_le.2.2.2.2.2

/-- An input is mapped in a state that kept the entry's bytes. -/
theorem mapped_of (hk : Kept m0.dmem st.dmem) {a : BitVec 64} {n : Nat}
    (h : WhirIn m0 a n basisWEvalStack) :
    NativeRustcVm.Mapped st.dmem a n ∧ NativeRustcVm.NoWrap a n :=
  ⟨NativeRustcVm.Transcript.Mapped.keeps h.1.1 hk, h.1.2⟩

/-- **An input reads as at the entry** in a state of the frame. -/
theorem In.same_of (h : In m0 ba b v) (hf : Fb m0 o st) {a : BitVec 64} {n : Nat}
    (ha : WhirIn m0 a n basisWEvalStack) : Same m0.dmem st.dmem a n := by
  have hS := h.stackOk
  refine Same.of_sameOutside hf.same fun j hj hq ↦ ?_
  rcases hq with hq | hq
  · exact NativeRustcVm.Apart.not_inRange_add ha.2 ha.1.2 (noWrap_stackBelow hS) hj
      (inRange_mono hq (by omega))
  · exact hq

/-- A block's environment with the frame and `rest`, inputs pairwise apart: well formed. -/
theorem In.wf (h : In m0 ba b v) (hk : Kept m0.dmem st.dmem) {rest : List (BitVec 64 × Nat)}
    (hin : ∀ x ∈ rest, WhirIn m0 x.1 x.2 basisWEvalStack)
    (hap : rest.Pairwise fun x y ↦ NativeRustcVm.Apart x.1 x.2 y.1 y.2) {ret : BitVec 64} :
    (envB m0 st rest ret).WF :=
  frame_wf ⟨h.frame_mapped hk, h.frame_noWrap⟩ (fun x hx ↦ mapped_of hk (hin x hx))
    (List.Pairwise.cons (fun x hx ↦ Apart.symm' (h.frame_apart (hin x hx))) hap)

/-- The frame alone. -/
theorem In.wf0 (h : In m0 ba b v) (hf : Fb m0 o st) {ret : BitVec 64} : (envB m0 st [] ret).WF :=
  h.wf hf.frame.kept (by simp) List.Pairwise.nil

/-- The frame and one input. -/
theorem In.wf1 (h : In m0 ba b v) (hk : Kept m0.dmem st.dmem) {a : BitVec 64} {n : Nat}
    (ha : WhirIn m0 a n basisWEvalStack) {ret : BitVec 64} : (envB m0 st [(a, n)] ret).WF :=
  h.wf hk (by simpa using ha) (List.pairwise_singleton _ _)

/-- The frame and two inputs, apart. -/
theorem In.wf2 (h : In m0 ba b v) (hk : Kept m0.dmem st.dmem) {a a' : BitVec 64} {n n' : Nat}
    (ha : WhirIn m0 a n basisWEvalStack) (ha' : WhirIn m0 a' n' basisWEvalStack)
    (hap : NativeRustcVm.Apart a n a' n') {ret : BitVec 64} :
    (envB m0 st [(a, n), (a', n')] ret).WF :=
  h.wf hk (by simp [ha, ha']) (List.pairwise_pair.mpr hap)

/-- The body's state: RSP at offset `o`. -/
theorem match_body [Labels] (hf : Fb m0 o st) {rest : List (BitVec 64 × Nat)} {ret : BitVec 64}
    {sizes : List Nat} (hsz : RegionsOk sizes ((fb m0, 168) :: rest)) :
    Match (envB m0 st rest ret) (init sizes [(.rsp, .ptr 0 (o : Int))]) st :=
  match_ofMachine hsz ⟨hf.frame.rsp_eval, trivial⟩ trivial trivial trivial

end

/-! ## The inputs through the frame -/

section
variable {o : Nat} {st : MachineData}

theorem In.layoutAt (h : In m0 ba b v) (hf : Fb m0 o st) : LayoutWAt st.dmem ba.layout v.L :=
  NativeRustcVm.Tables.LayoutWAt.of_same h.layout (h.same_of hf h.layoutIn)

theorem In.claimsAt (h : In m0 ba b v) (hf : Fb m0 o st) : ClaimsWAt st.dmem ba.claims v.cs :=
  NativeRustcVm.Tables.ClaimsWAt.of_same h.claims (h.same_of hf h.claimsIn)

/-- The `BasisW`'s words. -/
abbrev basisWords (ba : BasisAddrs) : List UInt64 :=
  [UInt64.ofBitVec ba.scales, ba.count.toUInt64, UInt64.ofBitVec ba.layout,
    UInt64.ofBitVec ba.ring, UInt64.ofBitVec ba.keccak, UInt64.ofBitVec ba.claims,
    UInt64.ofBitVec ba.ood]

theorem In.wordsAt (h : In m0 ba b v) (hf : Fb m0 o st) :
    NativeRustcVm.WordsAt st.dmem (reg m0 .rsi) (basisWords ba) :=
  NativeRustcVm.Tables.WordsAt.of_same h.pre.2.1.words (h.same_of hf h.basis)
    (by simp [basisBytes])

/-- Word `i` of the `BasisW` in a state of the frame. -/
theorem In.word (h : In m0 ba b v) (hf : Fb m0 o st) (i : Nat) (hi : i < 7) :
    NativeRustcVm.WordAt st.dmem (off (reg m0 .rsi) (8 * i))
      ((basisWords ba)[i]'(by simpa using hi)) :=
  (h.wordsAt hf).getElem (by simpa using hi)

/-- Word `i` of the `BasisW` at the entry. -/
theorem In.word0 (h : In m0 ba b v) (i : Nat) (hi : i < 7) :
    NativeRustcVm.WordAt m0.dmem (off (reg m0 .rsi) (8 * i))
      ((basisWords ba)[i]'(by simpa using hi)) :=
  h.pre.2.1.words.getElem (by simpa using hi)

theorem count_lt (h : In m0 ba b v) : ba.count < 2 ^ 64 := h.pre.2.1.count_lt

theorem In.scalesAt (h : In m0 ba b v) (hf : Fb m0 o st) :
    NativeRustcVm.EWsAt st.dmem ba.scales b.scales.toList :=
  NativeRustcVm.Tables.EWsAt.of_same h.pre.2.1.scales (h.same_of hf h.scales)
    (by rw [Array.length_toList, h.pre.2.1.scales_size])

/-- The elements of an input read as at the entry. -/
theorem In.ewsOf_eq (h : In m0 ba b v) (hf : Fb m0 o st) {a : BitVec 64} {n N : Nat}
    (ha : WhirIn m0 a N basisWEvalStack) (hn : 16 * n ≤ N) :
    NativeRustcVm.ewsOf st.dmem a n = NativeRustcVm.ewsOf m0.dmem a n :=
  NativeRustcVm.ewsOf_congr fun i hi ↦ h.same_of hf ha i (by omega)

/-- The point, as at the entry. -/
theorem In.xpt_eq (h : In m0 ba b v) (hf : Fb m0 o st) {a n : BitVec 64}
    (ha : a = reg m0 .rdx) (hn : n = reg m0 .rcx) : slice st a n = xpt m0 := by
  subst ha hn
  unfold slice xpt slice
  rw [h.ewsOf_eq hf h.point le_rfl]

end

/-! ## Numbers -/

theorem toNat_toUInt64' {n : Nat} (h : n < 2 ^ 64) : n.toUInt64.toNat = n := by
  simp only [Nat.toUInt64_eq, UInt64.toNat_ofNat']; exact Nat.mod_eq_of_lt h

theorem toNat_bv_toUInt64 {n : Nat} (h : n < 2 ^ 64) : n.toUInt64.toBitVec.toNat = n := by
  rw [UInt64.toNat_toBitVec]; exact toNat_toUInt64' h

theorem placement_lt {d : Mem 64} {a : BitVec 64} {L : LayoutW} (h : LayoutWAt d a L) (c : Nat) :
    (L.placement c).variableCount < 2 ^ 64 ∧ (L.placement c).index < 2 ^ 64 := by
  unfold LayoutW.placement
  cases hc : L.placements[c]? with
  | none => exact ⟨by decide, by decide⟩
  | some o =>
    cases o with
    | none => exact ⟨by decide, by decide⟩
    | some p =>
      obtain ⟨hc', he⟩ := Array.getElem?_eq_some_iff.mp hc
      have := h.placements c hc'
      rw [he] at this
      exact ⟨this.2.1, this.2.2.1⟩

theorem placementArg_eq {m : MachineData} {p : Placement} (hp : p.variableCount < 2 ^ 64 ∧
    p.index < 2 ^ 64) (h1 : reg m .rsi = p.variableCount.toUInt64.toBitVec)
    (h2 : reg m .rdx = p.index.toUInt64.toBitVec) : placementArg m = p := by
  unfold placementArg
  rw [h1, h2, toNat_bv_toUInt64 hp.1, toNat_bv_toUInt64 hp.2]

/-! ## The weights -/

theorem dot_push_c (sc W : Array EW) (w : EW) :
    (dot sc (W.push w)).c0 = (dot sc W).c0 ^^^ (EW.mul (sAt sc W.size) w).c0 ∧
      (dot sc (W.push w)).c1 = (dot sc W).c1 ^^^ (EW.mul (sAt sc W.size) w).c1 := by
  rw [dot_push]
  exact ⟨rfl, rfl⟩

theorem dot_single (sc : Array EW) (w : EW) : dot sc #[w] = EW.mul (sAt sc 0) w := by
  rw [show #[w] = (#[] : Array EW).push w from rfl, dot_push, dot_empty]
  exact ew_zero_add _

theorem ws_size (v : Vals) (x : Array EW) (i : Nat) :
    (ws v x i).size = 1 + (colWs v.L x v.cs i).length := by
  simp [ws, Nat.add_comm]

theorem ws_succ (v : Vals) (x : Array EW) {i : Nat} (hi : i < v.cs.size) :
    ws v x (i + 1) = match (v.L.placements[v.cs[i].column]?).getD none with
      | none => ws v x i
      | some pl => (ws v x i).push (eqEval (stackPoint pl v.cs[i].point v.L.stackLog) x) := by
  unfold ws
  rw [colWs_succ _ _ _ hi]
  cases (v.L.placements[v.cs[i].column]?).getD none <;> simp

theorem ws_zero (v : Vals) (x : Array EW) : ws v x 0 = #[ringW v x] := by
  simp [ws, colWs_zero]

theorem sAt_ge {sc : Array EW} {j : Nat} (hj : sc.size ≤ j) : sAt sc j = 0 := by
  rw [sAt, Array.getElem?_eq_none hj]; rfl

theorem sAt_lt {sc : Array EW} {j : Nat} (hj : j < sc.size) : sAt sc j = sc[j] := by
  rw [sAt, Array.getElem?_eq_getElem hj, Option.getD_some]

/-- **The value**: the scales against the weights met, then the out-of-domain claim's. -/
theorem In.eval_eq (h : In m0 ba b v) :
    b.eval (xpt m0) = dot b.scales ((ws v (xpt m0) v.cs.size).push (eqEval v.z (xpt m0))) := by
  obtain ⟨sc, cl⟩ := b
  have he : cl = stackClaims v.L v.target v.kp v.coeffs v.cs v.z v.value := h.eq
  subst he
  rw [basis_eval]
  simp [ws, ringW]

/-! ## Scales -/

theorem scale_beq {s : BitVec 64} {c j : Nat} (hnw : NativeRustcVm.NoWrap s (16 * c))
    (hpos : 0 < s.toNat ∨ s.toNat + 16 * c < 2 ^ 64) :
    ((off s (16 * min j c)) == (off s (16 * c))) = decide (c ≤ j) := by
  rw [bv_beq_toNat]
  unfold NativeRustcVm.NoWrap at hnw
  have e1 := NativeRustcVm.toNat_add_ofNat_le (a := s) (i := 16 * min j c) (by omega)
  have e2 := NativeRustcVm.toNat_add_ofNat_le (a := s) (i := 16 * c) (by omega)
  simp only [off]
  by_cases hc : c ≤ j
  · simp only [hc, decide_true, decide_eq_true_eq]
    rw [Nat.min_eq_right hc]
  · simp only [hc, decide_false, decide_eq_false_iff_not]
    omega

/-- The scales do not reach `2 ^ 64` or do not start at `0`. -/
theorem In.scalesPos (h : In m0 ba b v) :
    0 < ba.scales.toNat ∨ ba.scales.toNat + 16 * ba.count < 2 ^ 64 := by
  have hs : NativeRustcVm.Apart ba.scales (16 * ba.count) (stackBelow m0 basisWEvalStack)
    (basisWEvalStack + 8) := h.scales.2
  have := (stackBelow m0 basisWEvalStack).isLt
  unfold NativeRustcVm.Apart at hs
  omega

/-- The scales' pointer against their end: equal once `j` scales are taken. -/
theorem In.scale_beq (h : In m0 ba b v) (j : Nat) :
    ((off ba.scales (16 * min j ba.count)) == (off ba.scales (16 * ba.count))) =
      decide (ba.count ≤ j) :=
  BasisWEval.scale_beq h.scales.1.2 h.scalesPos

section
variable {o : Nat} {st : MachineData}

/-- Scale `j` in a state of the frame. -/
theorem In.scaleAt (h : In m0 ba b v) (hf : Fb m0 o st) {j : Nat} (hj : j < ba.count) :
    NativeRustcVm.WordAt st.dmem (off (sA ba j) 0) (sAt b.scales j).c0 ∧
      NativeRustcVm.WordAt st.dmem (off (sA ba j) 8) (sAt b.scales j).c1 := by
  have hsz := h.pre.2.1.scales_size
  have hj' : j < b.scales.toList.length := by simp; omega
  have he := NativeRustcVm.ewAt_iff.mp ((h.scalesAt hf).getElem hj')
  rw [sAt_lt (by omega)]
  exact ⟨by simpa [sA, off] using he.1, by simpa [sA, off] using he.2⟩

/-- Scale `j`'s 16 bytes: an input area. -/
theorem In.scaleIn (h : In m0 ba b v) {j : Nat} (hj : j < ba.count) :
    WhirIn m0 (sA ba j) 16 basisWEvalStack :=
  WhirIn.sub h.scales (by omega)

end

end

end NativeRustcVmX64.Whir.BasisWEval
