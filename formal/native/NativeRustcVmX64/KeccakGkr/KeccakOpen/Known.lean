module

public import NativeRustcVmX64.KeccakGkr.KeccakOpen.Defs
public import NativeRustcX64.Hasher.Bytes
public import NativeRustcX64.Got

/-!
# `keccak_open`: the registers and saved words known around the fold (x86-64)

`KAt m0 vars ks st`: each register of `ks` holds its value, a stable symbolic value evaluated with
the fold's regions and `vars` (`envK`); `Words m0 vars ws st`: each saved word of `ws` at its frame
offset. From them `pS ks` describes the machine (`match_pS`); the known loads of round `t` are
their values (`kl_ok`, `subst_eval`); after a block the registers and words its checks give
(`KAt.after`, `Words.after`). A block around the fold (`blk_run`) and one calling `memcpy`
(`copy_run`).
-/

namespace NativeRustcVmX64.KeccakGkr.KeccakOpen

open NativeRustcX64 NativeRustcX64.Sym NativeVm.Model NativeRustcVmX64.Transcript
open LeanVM.Parameters LeanVM.Protocol.Verifier
open NativeRustcVm (Region InAny)
open NativeRustcVm.Transcript (off off_zero off_off off_add toNat_off inRange_iff' Mapped.keeps
  bytesAt_congr inRange_off_self DecArea tstateBytes TStateAt Touch)

@[expose] public section

/-- **The known registers.** -/
def KAt [Labels] (m0 : MachineData) (vars : Nat → BitVec 64) (ks : List (Reg64 × Sym))
    (st : MachineData) : Prop :=
  AllOf (fun p ↦ reg st p.1 = p.2.eval (envK m0 vars)) ks

/-- **The saved words.** -/
def Words [Labels] (m0 : MachineData) (vars : Nat → BitVec 64) (ws : List (Nat × Sym))
    (st : MachineData) : Prop :=
  AllOf (fun p ↦ NativeRustcVm.WordAt st.dmem (off (fbA m0) p.1)
    (UInt64.ofBitVec (p.2.eval (envK m0 vars)))) ws

/-- Round `t`'s challenge in variables `0`, `1`. -/
def VarsOk (cx : Cx) (t : Nat) (vars : Nat → BitVec 64) : Prop :=
  t < 6 ∧ vars 0 = (cx.sl.getD t 0).c0.toBitVec ∧ vars 1 = (cx.sl.getD t 0).c1.toBitVec

/-- Saved words with stable values. -/
def wfW (ws : List (Nat × Sym)) : Bool := ws.all fun p ↦ stable p.2

end

public section

theorem allOf_imp {α : Type} {P Q : α → Prop} :
    ∀ {l : List α}, AllOf P l → (∀ x ∈ l, P x → Q x) → AllOf Q l
  | [], _, _ => trivial
  | x :: _, h, hq =>
    ⟨hq x List.mem_cons_self h.1, allOf_imp h.2 fun y hy ↦ hq y (List.mem_cons_of_mem _ hy)⟩

theorem allOf_of {α : Type} {P : α → Prop} : ∀ {l : List α}, (∀ x ∈ l, P x) → AllOf P l
  | [], _ => trivial
  | x :: _, h => ⟨h x List.mem_cons_self, allOf_of fun y hy ↦ h y (List.mem_cons_of_mem _ hy)⟩

theorem lookup_mem {kl : List (Sym × Sym)} {e v : Sym} (h : kl.lookup e = some v) : (e, v) ∈ kl := by
  induction kl with
  | nil => cases h
  | cons p kl ih =>
    obtain ⟨k, w⟩ := p
    simp only [List.lookup_cons] at h
    split at h
    · rename_i he
      rw [beq_iff_eq] at he
      subst he
      cases h
      exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ (ih h)

variable [Labels]

theorem eval_stable : ∀ (v : Sym), stable v = true → ∀ {e e' : Env}, e.regions = e'.regions →
    e.vars = e'.vars → v.eval e = v.eval e'
  | .lit _, _, _, _, _, _ => rfl
  | .var i, _, e, e', _, hv => by simp only [Sym.eval, hv]
  | .ptr r o, _, e, e', hr, _ => by simp only [Sym.eval, Env.base, hr]
  | .bin op w a b, h, e, e', hr, hv => by
    simp only [stable, Bool.and_eq_true] at h
    simp only [Sym.eval]
    rw [eval_stable a h.1 hr hv, eval_stable b h.2 hr hv]
  | .un op w a, h, e, e', hr, hv => by
    simp only [stable] at h
    simp only [Sym.eval]
    rw [eval_stable a h hr hv]
  | .reg _, h, _, _, _, _ => nomatch h
  | .label _, _, _, _, _, _ => rfl
  | .gotSlot _, h, _, _, _, _ => nomatch h
  | .load _ _ _, h, _, _, _, _ => nomatch h
  | .loadx _ _ _ _, h, _, _, _, _ => nomatch h
  | .retAddr, h, _, _, _, _ => nomatch h
  | .tern _ _ _ _ _, h, _, _, _, _ => nomatch h
  | .ite _ _ _, h, _, _, _, _ => nomatch h

/-- **The known loads replaced by their values** keep a value. -/
theorem subst_eval {env : Env} {kl : List (Sym × Sym)}
    (hkl : ∀ p ∈ kl, p.1.eval env = p.2.eval env) (e : Sym) : (subst kl e).eval env = e.eval env := by
    unfold subst
    cases hl : kl.lookup e with
    | some v => exact (hkl _ (lookup_mem hl)).symm
    | none =>
      dsimp only
      cases e with
      | bin op w a b =>
        show BinOp.apply op w ((subst kl a).eval env) ((subst kl b).eval env) = _
        rw [subst_eval hkl a, subst_eval hkl b]; rfl
      | un op w a =>
        show UnOp.apply op w ((subst kl a).eval env) = _
        rw [subst_eval hkl a]; rfl
      | _ => rfl

variable {a : DecArea} {s : TState} {c : KeccakClaimW} {cx : Cx} {m0 st st' : MachineData}
  {vars : Nat → BitVec 64} {ks ks' : List (Reg64 × Sym)} {ws ws' : List (Nat × Sym)}

theorem eval_K (st : MachineData) (vars : Nat → BitVec 64) (ret : BitVec 64) {v : Sym}
    (h : stable v = true) : v.eval (envK m0 vars) = v.eval (E m0 st vars ret) :=
  eval_stable v h rfl rfl

theorem KAt.get (hk : KAt m0 vars ks st) {r : Reg64} {v : Sym} (h : (r, v) ∈ ks) :
    reg st r = v.eval (envK m0 vars) :=
  mem_of_allOf (P := fun p : Reg64 × Sym ↦ reg st p.1 = p.2.eval (envK m0 vars)) hk h

theorem Words.word (hw : Words m0 vars ws st) {p : Nat × Sym} (h : p ∈ ws) :
    NativeRustcVm.WordAt st.dmem (off (fbA m0) p.1) (UInt64.ofBitVec (p.2.eval (envK m0 vars))) :=
  mem_of_allOf hw h

/-- **A callee keeps the known registers.** -/
theorem KAt.call (hk : KAt m0 vars ks st) (hw : wfK ks = true) (hs : Saved st st') :
    KAt m0 vars ks st' :=
  allOf_imp hk fun p hp h ↦ by
    have := List.all_eq_true.mp hw p hp
    simp only [Bool.and_eq_true] at this
    rw [show NativeRustcX64.reg st' p.1 = NativeRustcX64.reg st p.1 from hs.1 p.1 this.1]
    exact h

/-- **Saved words kept** where memory changed off them. -/
theorem Words.keep (h : PreOk a s c m0) (hw : Words m0 vars ws st)
    (hws : ws.all (fun p ↦ decide (16 ≤ p.1) && decide (p.1 + 8 ≤ 64)) = true)
    {R : BitVec 64 → Prop} (hs : NativeRustcVm.SameOutside st.dmem st'.dmem R)
    (hR : ∀ q, R q → q.toNat < (rspOf m0).toNat - 2208 + 16 ∨
      (rspOf m0).toNat - 2208 + 64 ≤ q.toNat) : Words m0 vars ws st' :=
  allOf_imp hw fun p hp hwd ↦ by
    have := List.all_eq_true.mp hws p hp
    simp only [Bool.and_eq_true, decide_eq_true_eq] at this
    refine bytesAt_congr hwd fun i hi ↦ hs _ fun hq ↦ ?_
    rw [NativeRustcVm.length_wordBytes] at hi
    have h1 := hR _ hq
    rw [off_add, fb_off h (by omega)] at h1
    omega

/-- The fold and its callees cannot overwrite the loader slot. -/
theorem got_byte (h : PreOk a s c m0)
    (hs : NativeRustcVm.SameOutside m0.dmem st.dmem (Out m0)) {i : Nat} (hi : i < 8) :
    st.dmem.get? (gotAddr "memcpy" + BitVec.ofNat 64 i) =
      some (byteOf (Labels.label "memcpy").toBitVec i) := by
  have hg := h.got.1 "memcpy" (by simp)
  have hn := nums h
  rw [hs _ ?_]
  · exact h.got.byte (by simp) hi
  rintro ⟨r, hr, hq⟩
  simp only [wsOf, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl
  · change NativeRustcVm.InRange (stackBelow m0 keccakOpenStack) keccakOpenStack _ at hq
    exact hg.2.2.1.not_inRange hg.2.1 (noWrap_stackBelow h.st) hi
      (inRange_mono hq (show keccakOpenStack ≤ keccakOpenStack + 8 by omega))
  · exact (hg.2.2.2 (oA m0, 24) (by simp)).not_inRange hg.2.1 hn.o hi hq
  · exact (hg.2.2.2 (tA m0, tstateBytes) (by simp)).not_inRange hg.2.1 hn.t hi hq
  · change NativeRustcVm.InRange (slA m0) 96 _ at hq
    exact (hg.2.2.2 (slA m0, 96) (by simp)).not_inRange hg.2.1 hn.s hi hq
  · exact (hg.2.2.2 (rwA m0, 65536) (by simp [NativeRustcVm.KeccakGkr.rowsBytes])).not_inRange
      hg.2.1 hn.w hi hq

/-- The fold's regions are data memory, do not wrap and are apart. -/
theorem wf_fold (h : PreOk a s c m0) (hk : Kept m0.dmem st.dmem) {ret : BitVec 64} :
    (E m0 st vars ret).WF := by
  have hn := nums h
  have := hn.r1; have := hn.r2; have := hn.s; have := hn.w; have := hn.ss; have := hn.sw
  have := hn.sw'; have := hn.sarg; have := hn.warg
  have hfb : (stackBelow m0 2208).toNat = _ := fbA_toNat h
  have ha := argA_toNat h
  have hA := h.areas
  have ms : ewsRegion (slA m0) qkeccakSlotBits ∈ wsOf m0 ++ rsOf a c m0 :=
    List.mem_append_left _ (.tail _ (.tail _ (.head _)))
  have mw : (⟨rwA m0, NativeRustcVm.KeccakGkr.rowsBytes⟩ : Region) ∈ wsOf m0 ++ rsOf a c m0 :=
    List.mem_append_left _ (.tail _ (.tail _ (.tail _ (.head _))))
  have mg : argsRegion m0 6 ∈ wsOf m0 ++ rsOf a c m0 :=
    List.mem_append_right _ (.tail _ (.tail _ (.tail _ (.tail _ (.head _)))))
  have e6 : 16 * qkeccakSlotBits = 96 := by rw [NativeVm.Math.Keccak.qkeccakSlotBits_eq]
  refine frame_wf ⟨Mapped.keeps (frame_mapped h.st (by rw [stack_eq]; decide)) hk,
    frame_noWrap h.st (by rw [stack_eq]; decide)⟩ (fun x hx ↦ ?_) ?_
  · simp only [RF, List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · have := (Areas.ok hA ms).1
      dsimp only [ewsRegion] at this
      rw [e6] at this
      exact ⟨Mapped.keeps this hk, by show _ + 96 ≤ _; omega⟩
    · exact ⟨Mapped.keeps (Areas.ok hA mw).1 hk, by show _ + 65536 ≤ _; omega⟩
    · exact ⟨Mapped.keeps (Areas.ok hA mg).1 hk, by show _ + 48 ≤ _; rw [ha]; omega⟩
    · exact ⟨Mapped.keeps (h.got.mapped (by simp)) hk, (h.got.1 "memcpy" (by simp)).2.1⟩
  · have hg := h.got.1 "memcpy" (by simp)
    have hgf : NativeRustcVm.Apart (gotAddr "memcpy") 8 (fbA m0) 2216 :=
      apart_frame hg.2.2.1 h.st.1 (by rw [stack_eq]; decide)
    have hgs : NativeRustcVm.Apart (gotAddr "memcpy") 8 (slA m0) 96 :=
      (apart_iff.mp (hg.2.2.2 (slA m0, 96) (by simp)))
    have hgw : NativeRustcVm.Apart (gotAddr "memcpy") 8 (rwA m0) 65536 :=
      (apart_iff.mp (hg.2.2.2 (rwA m0, 65536) (by simp [NativeRustcVm.KeccakGkr.rowsBytes])))
    have hga : NativeRustcVm.Apart (gotAddr "memcpy") 8 (argA m0) 48 :=
      (apart_iff.mp (hg.2.2.2 (argA m0, 48) (by simp)))
    simp only [RF]
    refine List.pairwise_cons.mpr ⟨fun y hy ↦ ?_, List.pairwise_cons.mpr ⟨fun y hy ↦ ?_,
      List.pairwise_cons.mpr ⟨fun y hy ↦ ?_, List.pairwise_pair.mpr (Apart.symm' hga)⟩⟩⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
      rcases hy with rfl | rfl | rfl | rfl
      · unfold NativeRustcVm.Apart; dsimp only; omega
      · unfold NativeRustcVm.Apart; dsimp only; omega
      · unfold NativeRustcVm.Apart; dsimp only; omega
      · exact Apart.symm' hgf
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
      rcases hy with rfl | rfl | rfl
      · unfold NativeRustcVm.Apart; dsimp only; omega
      · unfold NativeRustcVm.Apart; dsimp only; omega
      · exact Apart.symm' hgs
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
      rcases hy with rfl | rfl
      · unfold NativeRustcVm.Apart; dsimp only; omega
      · exact Apart.symm' hgw

/-- The stack arguments are kept where memory changed only in `Out`. -/
theorem arg_keep (h : PreOk a s c m0) (hs : NativeRustcVm.SameOutside m0.dmem st.dmem (Out m0)) :
    ∀ i < 48, st.dmem.get? (argA m0 + BitVec.ofNat 64 i) = m0.dmem.get? (argA m0 + BitVec.ofNat 64 i) := by
  intro i hi
  have hn := nums h
  have := hn.r1; have := hn.r2; have := hn.oarg; have := hn.targ; have := hn.sarg
  have := hn.warg; have := hn.o; have := hn.t; have := hn.s; have := hn.w
  have e := argA_toNat h
  have e2 : (argA m0 + BitVec.ofNat 64 i).toNat = (rspOf m0).toNat + 8 + i := by
    rw [show argA m0 + BitVec.ofNat 64 i = off (argA m0) i from rfl, toNat_off (by omega), e]
  refine hs _ fun ⟨r, hr, hq⟩ ↦ ?_
  simp only [wsOf, List.mem_cons, List.not_mem_nil, or_false] at hr
  have eq6 : qkeccakSlotBits = 6 := NativeVm.Math.Keccak.qkeccakSlotBits_eq
  rcases hr with rfl | rfl | rfl | rfl | rfl <;> unfold NativeRustcVm.Region.Holds at hq <;>
    dsimp only [ewsRegion] at hq
  · have hsb : (stackBelow m0 3200).toNat = (rspOf m0).toNat - 3200 := stackBelow_toNat (by omega)
    rw [stack_eq, inRange_iff' (by unfold NativeRustcVm.NoWrap; rw [hsb]; omega), hsb, e2] at hq
    omega
  · rw [inRange_iff' (by unfold NativeRustcVm.NoWrap; omega), e2] at hq; omega
  · rw [inRange_iff' (by unfold NativeRustcVm.NoWrap; show _ + 760 ≤ _; omega), e2] at hq
    show False; have : tstateBytes = 760 := rfl; omega
  · rw [eq6, inRange_iff' (by unfold NativeRustcVm.NoWrap; omega), e2] at hq; omega
  · rw [inRange_iff' (by unfold NativeRustcVm.NoWrap; show _ + 65536 ≤ _; omega), e2] at hq
    show False; have : NativeRustcVm.KeccakGkr.rowsBytes = 65536 := rfl; omega

/-- **A stack argument word**, in memory changed only in `Out`. -/
theorem arg_word (h : PreOk a s c m0) (hs : NativeRustcVm.SameOutside m0.dmem st.dmem (Out m0))
    {i : Nat} (hi : i < 6) :
    NativeRustcVm.WordAt st.dmem (off (argA m0) (8 * i)) (UInt64.ofBitVec (stackArg m0 i)) := by
  have hm : NativeRustcVm.Mapped m0.dmem (off (argA m0) (8 * i)) 8 :=
    mapped_off h.args.1 (by omega)
  have hw := NativeRustcVm.wordAt_of_mapped hm
  have e : off (argA m0) (8 * i) = rspOf m0 + BitVec.ofNat 64 (8 + 8 * i) := by
    show rspOf m0 + 8#64 + BitVec.ofNat 64 (8 * i) = _
    rw [BitVec.add_assoc, show (8#64 : BitVec 64) = BitVec.ofNat 64 8 from rfl, ← BitVec.ofNat_add]
  rw [show UInt64.ofBitVec (stackArg m0 i) = NativeRustcVm.wordOf m0.dmem (off (argA m0) (8 * i)) by
    rw [e]; rfl]
  exact bytesAt_congr hw fun j hj ↦ by
    rw [NativeRustcVm.length_wordBytes] at hj
    rw [off_add]
    exact arg_keep h hs _ (by omega)

/-- **A stack argument word** loaded in the fold's environment. -/
theorem load_arg (h : PreOk a s c m0) (hs : NativeRustcVm.SameOutside m0.dmem st.dmem (Out m0))
    {ret : BitVec 64} {i : Nat} (hi : i < 6) :
    (E m0 st vars ret).load 3 (8 * i) 8 = stackArg m0 i := by
  have := load_of_wordAt (env := E m0 st vars ret) (r := 3) (o := 8 * i) (arg_word h hs hi)
  rw [this]

/-- A stack argument word's alias. -/
theorem arg_alias {ret : BitVec 64} (i : Nat) :
    (Sym.ptr 0 ((2216 + 8 * i : Nat) : Int)).eval (E m0 st vars ret) =
      (E m0 st vars ret).base 3 + BitVec.ofInt 64 ((8 * i : Nat) : Int) := by
  rw [eval_ptr0, show 2216 + 8 * i = 2208 + (8 + 8 * i) by omega, frame_add]
  show _ = rspOf m0 + 8#64 + _
  rw [BitVec.add_assoc, show BitVec.ofInt 64 ((8 * i : Nat) : Int) = BitVec.ofNat 64 (8 * i) from
    BitVec.ofInt_natCast .., show (8#64 : BitVec 64) = BitVec.ofNat 64 8 from rfl,
    ← BitVec.ofNat_add]

omit [Labels] in
theorem ofInt0 : BitVec.ofInt 64 0 = 0#64 := rfl

/-- **The known loads of round `t`** are their values. -/
theorem kl_ok (h : PreOk a s c m0) {o : Nat} (hm : Mid cx m0 o st) {t : Nat} (hv : VarsOk cx t vars)
    (hw : Words m0 vars ws st) (hws : wfW ws = true) {ret : BitVec 64} :
    ∀ p ∈ klOf t ws, p.1.eval (E m0 st vars ret) = p.2.eval (E m0 st vars ret) := by
  intro p hp
  simp only [klOf, List.mem_append, List.mem_cons, List.not_mem_nil, or_false, List.mem_map] at hp
  rcases hp with (rfl | rfl | rfl | rfl) | ⟨q, hq, rfl⟩
  · show (E m0 st vars ret).load 3 (8 * 5) 8 = (E m0 st vars ret).base 2 + BitVec.ofInt 64 0
    rw [load_arg h hm.same (by decide), ofInt0, BitVec.add_zero]; rfl
  · show (E m0 st vars ret).load 3 (8 * 4) 8 = (E m0 st vars ret).base 1 + BitVec.ofInt 64 0
    rw [load_arg h hm.same (by decide), ofInt0, BitVec.add_zero]; rfl
  · have he := NativeRustcVm.ewAt_iff.mp (ewsAt_getD hm.slot (i := t) (by rw [hm.sl_size]; exact hv.1))
    show (E m0 st vars ret).load 1 (16 * t) 8 = vars 0
    rw [hv.2.1]
    exact load_of_wordAt (by exact he.1)
  · have he := NativeRustcVm.ewAt_iff.mp (ewsAt_getD hm.slot (i := t) (by rw [hm.sl_size]; exact hv.1))
    show (E m0 st vars ret).load 1 (16 * t + 8) 8 = vars 1
    rw [hv.2.2]
    refine load_of_wordAt ?_
    have := he.2
    rwa [off_add] at this
  · have hst := List.all_eq_true.mp hws q hq
    show (E m0 st vars ret).load 0 q.1 8 = _
    rw [← eval_K st vars ret hst]
    exact load_of_wordAt (hw.word hq)

/-- **The fold's symbolic state describes the machine.** -/
theorem match_pS (h : PreOk a s c m0) (hm : Mid cx m0 8 st) (hk : KAt m0 vars ks st)
    (hwk : wfK ks = true) {ret : BitVec 64} : Match (E m0 st vars ret) (pS ks) st := by
  apply Match.withKnownBytes
  · refine match_ofMachine ⟨rfl, rfl, rfl, rfl, rfl, trivial⟩ ⟨hm.fr.rsp_eval, ?_⟩ trivial trivial
      ⟨arg_alias 0, arg_alias 1, arg_alias 2, arg_alias 3, arg_alias 4, arg_alias 5, ?_,
        by simp [Sym.eval, RF, Env.base, gotAddr], trivial⟩
    · exact allOf_imp hk fun p hp hr ↦ by
        have := List.all_eq_true.mp hwk p hp
        simp only [Bool.and_eq_true] at this
        exact hr.trans (eval_K st vars ret this.2)
    · show (E m0 st vars ret).load 3 32 8 = (E m0 st vars ret).base 1 + BitVec.ofInt 64 0
      rw [show (32 : Nat) = 8 * 4 from rfl, load_arg h hm.same (by decide), ofInt0, BitVec.add_zero]
      rfl
  · intro i hi
    simpa only [RF, Nat.zero_add, Sym.eval, Env.base_ofMachine_eq, Env.ofMachine_mem0,
      List.getElem?_cons_succ, List.getElem?_cons_zero, Option.map_some, Option.getD_some] using
      got_byte h hm.same hi

/-- **The known registers after a block.** -/
theorem KAt.after {env : Env} {S : SState} (hm' : Match env S st') {kl : List (Sym × Sym)}
    (hkl : ∀ p ∈ kl, p.1.eval env = p.2.eval env) (henv : env.regions = (envK m0 vars).regions)
    (hvars : env.vars = vars) (h : regsOk kl S ks' = true) : KAt m0 vars ks' st' :=
  allOf_of fun p hp ↦ by
    have h1 := List.all_eq_true.mp h p hp
    simp only [Bool.and_eq_true, beq_iff_eq] at h1
    obtain ⟨⟨-, hs⟩, he⟩ := h1
    cases hr : S.reg p.1 with
    | none => rw [hr] at he; cases he
    | some e =>
      rw [hr, Option.map_some, Option.some.injEq] at he
      show st'.regs.get64 p.1 = _
      rw [hm'.regs p.1 e hr, ← subst_eval hkl e, he]
      exact eval_stable p.2 hs henv hvars

/-- **The saved words after a block** writing only the frame below `64`. -/
theorem Words.after (h : PreOk a s c m0) {ret : BitVec 64} {S : SState}
    (hwf : (E m0 st vars ret).WF) (hm' : Match (E m0 st vars ret) S st')
    {kl : List (Sym × Sym)} (hkl : ∀ p ∈ kl, p.1.eval (E m0 st vars ret) = p.2.eval (E m0 st vars ret))
    (hlow : low64 S = true) (hw : Words m0 vars ws st) (hok : wordsOk kl S ws ws' = true) :
    Words m0 vars ws' st' :=
  allOf_of fun p hp ↦ by
    have hn := nums h
    have := hn.r1; have := hn.r2
    have hfb : (stackBelow m0 2208).toNat = _ := fbA_toNat h
    have hfb2 := fbA_toNat h
    have h1 := List.all_eq_true.mp hok p hp
    simp only [wordOk, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at h1
    obtain ⟨⟨⟨hs, ho1⟩, ho2⟩, hwr | ⟨hun, hmem⟩⟩ := h1
    · cases hf : findWrite 0 p.1 S.mem with
      | none => rw [hf] at hwr; cases hwr
      | some et =>
        obtain ⟨e, t0⟩ := et
        rw [hf] at hwr
        simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.mem_range] at hwr
        obtain ⟨hse, hall⟩ := hwr
        have := wordAt_write hm' (r := 0) (o := p.1) rfl (by omega) (v := e) fun i hi ↦ hall i hi
        rw [← subst_eval hkl e, hse, ← eval_K st vars ret hs] at this
        exact this
    · have hp' : p ∈ ws := by simpa using hmem
      refine bytesAt_congr (hw.word hp') fun i hi ↦ ?_
      rw [NativeRustcVm.length_wordBytes] at hi
      rw [off_add]
      refine hm'.get?_mem0 hwf fun ⟨w, hw', b, sz, hb, h2, h3⟩ ↦ ?_
      have hlw := List.all_eq_true.mp hlow w hw'
      simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hlw
      rw [hlw.1] at hb
      cases hb
      have hu := List.all_eq_true.mp hun w hw'
      simp only [bne_iff_ne, ne_eq, Bool.or_eq_true, decide_eq_true_eq, hlw.1,
        not_true_eq_false, false_or] at hu
      rw [toNat_off (by rw [hfb]; omega)] at h2 h3
      change (stackBelow m0 2208).toNat + w.off ≤ _ at h2
      change _ < (stackBelow m0 2208).toNat + w.off + w.n at h3
      omega

/-- A frame byte below `64` is `Safe` and off the saved words' range end. -/
theorem touch64_safe (h : PreOk a s c m0) {q : BitVec 64}
    (hq : Touch (fbA m0) 2216 (fun j ↦ 0 ≤ j ∧ j < 64) q) : Safe m0 q := by
  obtain ⟨j, hj, hj', rfl⟩ := hq
  have := (nums h).r1
  unfold Safe SafeN
  rw [fb_off h (by omega)]
  omega

end

end NativeRustcVmX64.KeccakGkr.KeccakOpen
