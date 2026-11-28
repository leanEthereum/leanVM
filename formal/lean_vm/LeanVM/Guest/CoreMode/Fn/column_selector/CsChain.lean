/-
  LeanVM.Guest.CoreMode.Fn.column_selector.CsChain

  `column_selector`'s arguments at the honest instances of b2c's aligned tree (`CsQ`), carried down its one
  chain of callers from `main`'s exponent tables and `verify_sub`'s stack placement.
-/

module

public import LeanVM.Guest.EndExecInstA
public import LeanVM.Guest.CoreMode.Fam.MonoChain
public import LeanVM.Guest.CoreMode.Fam.ProgOkG
public import LeanVM.Guest.CoreMode.Fam.CarryDefs
public import LeanVM.Guest.CoreMode.Gen.TermCallers
public import LeanVM.Guest.CoreMode.Fn.column_selector.Found
public import LeanVM.Guest.B1.VerifySub.Sizes
public import LeanVM.Guest.B1.VerifySub.Flat
public import LeanVM.Guest.B1.VsC.StkSelA
public import LeanVM.Guest.B1.Bits.Tables
public import LeanVM.Protocol.Relation.Placement
public import LeanVM.Guest.EndSound
public import LeanVM.Guest.CoreMode.Fn.check_stack_terminal.Carry
import LeanVM.Guest.ValRef
import LeanVM.Guest.Data.Consts
import LeanVM.Guest.Data.ValNames.«verify_sub»

/-!
# `column_selector`'s arguments, carried down

`column_selector__L{n}_L{κ}`'s only caller is `stack_selectors__L{n}`, whose only caller is
`check_stack_terminal`, whose only caller is `verify_sub`, whose only caller is the loop `main_loop4`,
called by `main` and itself (`Own.column_selector.stCallers`, the whole program's check
`Res.termCallers_all`). `CsQ r J` states what each of them receives:

* `main_loop4` and `verify_sub`: the exponent tables (`B1.ExpTables`) at their `g_squares`, `main`'s
  return of `exponent_tables`;
* `check_stack_terminal` and `stack_selectors__L{n}`: the tables, and the blocks' offsets and kappas
  (`BlocksAt`), placed by `certify_stack` in `verify_sub` (`B1.VerifySub.sizesOk`,
  `placement_aligned`): block `b`'s offset `g^idx`, `idx < 2^32`, a multiple of `2^κ`, its kappa `g^κ`;
  `check_stack_terminal` also its kappa source `kappa_base[g^7]`, the Keccak table's log height `g^e`, `e < 25`
  (`vs_kappa`);
* `column_selector__L{n}_L{κ}`, `κ < 4n`: its offset `g^idx`, `idx < 2^32` a multiple of `2^κ`, and the
  nibble shares at `sel_g` (`SharesAt`): its block's, the dispatch taking the block's kappa
  (`B1.VsC.walk_stsBody`).

`csQ_allA`: `CsQ` at every honest instance (`insts_allA`).
-/

namespace LeanVM.Guest.B1.VerifySub

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

public section

/-- The Keccak table's height word, `kb[2 + TABLE_KECCAK]` (`PhOpen.heights_at` at `5`). -/
theorem vsHeight5 {bytecode : List K} {rd : Reader} {σ : Val} (S : SizesOk bytecode rd σ) :
    σ (.n (115 + 5)) = gen ^ (vsLayout bytecode σ).tableLogHeights.getD 5 0 := by
  have hlen : (vsLayout bytecode σ).tableLogHeights.length = 6 := by
    obtain ⟨-, -, -, hth, -⟩ := Stack.buildLayout_some S.build
    rw [hth, List.length_zipWith]; simp [vsRows, vsAnnounced, tableLogFloors, nTables]
  have := congrArg (fun l ↦ l.getD 5 0) S.heights
  simp only [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range (show 5 < nTables by decide),
    Option.map_some, Option.getD_some] at this
  rw [this, List.getElem?_eq_getElem (by rw [hlen]; decide), List.getD_eq_getElem _ _ (by rw [hlen]; decide)]
  rfl

/-- Table `t`'s height word, `kb[2 + t]` (`PhOpen.heights_at`). -/
theorem vsHeight {bytecode : List K} {rd : Reader} {σ : Val} (S : SizesOk bytecode rd σ) {t : ℕ} (ht : t < 6) :
    σ (.n (115 + t)) = gen ^ (vsLayout bytecode σ).tableLogHeights.getD t 0 := by
  have hlen : (vsLayout bytecode σ).tableLogHeights.length = 6 := by
    obtain ⟨-, -, -, hth, -⟩ := Stack.buildLayout_some S.build
    rw [hth, List.length_zipWith]; simp [vsRows, vsAnnounced, tableLogFloors, nTables]
  have := congrArg (fun l ↦ l.getD t 0) S.heights
  simp only [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range (show t < nTables from ht),
    Option.map_some, Option.getD_some] at this
  rw [this, List.getElem?_eq_getElem (by rw [hlen]; exact ht), List.getD_eq_getElem _ _ (by rw [hlen]; exact ht)]
  rfl

end

end LeanVM.Guest.B1.VerifySub

namespace LeanVM.Guest.EndExec

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Memory
open LeanVM.Guest.B1.Stack (cselName cselBody stsName stsBody stsBodyA stsBlock cs_found sts_found)
open LeanVM.Protocol.Verifier (gen placement_aligned bytecodeSlotBits)

@[expose] public section

/-- **The blocks placed**: block `b`'s offset `g^idx`, `idx < 2^32` a multiple of `2^κ`, its kappa `g^κ`,
`κ < 31`. -/
def BlocksAt (rd : Reader) (offs kaps : E) : Prop :=
  ∀ b < 52, ∃ idx κ, κ < 31 ∧ idx < 2 ^ 32 ∧ 2 ^ κ ∣ idx ∧ LoadHolds rd offs b (gen ^ idx) ∧
    LoadHolds rd kaps b (gen ^ κ)

/-- **The nibble shares** at `sg`: `sg[16 j + u] = g^(u·16^j)`. -/
def SharesAt (rd : Reader) (sg : E) : Prop :=
  ∀ j < 9, ∀ u < 16, LoadHolds rd sg (16 * j + u) (gen ^ (u * 16 ^ j))

/-- **What `verify_sub` certifies of `check_stack_terminal`'s sizes**: `gmv = g^s`, `s ≤ 30`; `g_log_mem = g^l`,
`l ≤ 30`; `g_n = g^n`, `n ≤ 24`, each table's height source `kappa_base[g^(2 + t)]` and each sent target's block's
kappa `kaps[g^b]` a power `g^e`, `e ≤ n` (`Res.expFacts`, `Res.dimFacts`). -/
def CstQ (rd : Reader) (σ : Val) : Prop :=
  (∃ s ≤ 30, σ (.n 4) = gen ^ s) ∧ (∃ l ≤ 30, σ (.n 8) = gen ^ l) ∧
    ∃ n ≤ 24, σ (.n 6) = gen ^ n ∧ (∀ t < 6, ∃ e ≤ n, LoadHolds rd (σ (.n 1)) (2 + t) (gen ^ e)) ∧
      ∀ b ∈ CoreMode.Own.check_stack_terminal.sentBlocks, ∃ e ≤ n, LoadHolds rd (σ (.n 3)) b (gen ^ e)

/-- **What `column_selector`'s chain of callers receives**, at an instance. -/
def CsQ (r : Ref) (J : Inst) : Prop :=
  ∀ f σ bufs kids, J.t = .node f σ bufs kids →
    (f = name% «main_loop4» → B1.ExpTables r.img.read (σ (.n 14))) ∧
    (f = name% «verify_sub» → B1.ExpTables r.img.read (σ (.n 4))) ∧
    (f = name% «check_stack_terminal» →
      B1.ExpTables r.img.read (σ (.n 0)) ∧ BlocksAt r.img.read (σ (.n 2)) (σ (.n 3)) ∧
        (∃ e < 25, LoadHolds r.img.read (σ (.n 1)) 7 (gen ^ e)) ∧ CstQ r.img.read σ) ∧
    (∀ n, 4 ≤ n → n ≤ 8 → f = stsName n →
      B1.ExpTables r.img.read (σ (.n 4)) ∧ BlocksAt r.img.read (σ (.n 0)) (σ (.n 1))) ∧
    (∀ n κ, 4 ≤ n → n ≤ 8 → κ < 4 * n → κ < 31 → f = cselName n κ →
      ∃ idx < 2 ^ 32, 2 ^ κ ∣ idx ∧ σ (.n 0) = gen ^ idx ∧ SharesAt r.img.read (σ (.n 2)))

end

/-! ## The program's facts -/

public section

/-- `main` returns the exponent tables at its value `51` before anything, and hands them to `main_loop4`. -/
theorem main_facts : Res.scanCall (fun g args rets ↦ g == "exponent_tables" && args.isEmpty && rets == [.n 51])
      (fn% «main»).body = true ∧
    Res.sitesB (fun g args _ ↦ g != name% «main_loop4» || args[14]? == some (.n 51)) (fn% «main»).body = true := by
  decide +kernel

/-- `main_loop4` hands its tables on to itself and to `verify_sub`. -/
theorem ml4_facts : (fn% «main_loop4»).params = (List.range 16).map V.n ∧
    Res.sitesB (fun g args _ ↦ (g != name% «main_loop4» || args[14]? == some (.n 14)) &&
      (g != name% «verify_sub» || args[4]? == some (.n 14))) (fn% «main_loop4»).body = true := by
  decide +kernel

/-- `verify_sub` hands its tables, kappa sources, offsets, kappas, `gmv`, `g_n` and `g_log_mem` to
`check_stack_terminal`. -/
theorem vs_facts : (fn% «verify_sub»).params = (List.range 6).map V.n ∧ (fn% «verify_sub»).loop = false ∧
    Res.sitesB (fun g args _ ↦ g != name% «check_stack_terminal» ||
      (args[0]? == some (.n (val% «verify_sub» "g_squares")) && args[2]? == some (.n (val% «verify_sub» "offs")) &&
        args[3]? == some (.n (val% «verify_sub» "kaps")) &&
        args[1]? == some (.n (val% «verify_sub» "kappa_base")) && args[4]? == some (.n (val% «verify_sub» "gmv")) &&
        args[6]? == some (.n 408) && args[8]? == some (.n (val% «verify_sub» "g_log_mem"))))
      (fn% «verify_sub»).body = true := by
  decide +kernel

/-- `check_stack_terminal` hands its tables, offsets and kappas to `stack_selectors`. -/
theorem cst_facts : (fn% «check_stack_terminal»).params = (List.range 23).map V.n ∧
    (fn% «check_stack_terminal»).loop = false ∧
    Res.sitesB (fun g args _ ↦ ((List.range 5).all fun i ↦ g != stsName (i + 4)) ||
      args == [.n 2, .n 3, .n 17, .n 18, .n 0]) (fn% «check_stack_terminal»).body = true := by
  decide +kernel

theorem find_main : coreProgram.find? "main" = some fn% «main» := coreProgram_find?_at (j := idx% «main») rfl
theorem find_ml4 : coreProgram.find? name% «main_loop4» = some fn% «main_loop4» :=
  coreProgram_find?_at (j := idx% «main_loop4») rfl
theorem find_vs : coreProgram.find? name% «verify_sub» = some fn% «verify_sub» :=
  coreProgram_find?_at (j := idx% «verify_sub») rfl
theorem find_cst : coreProgram.find? name% «check_stack_terminal» = some fn% «check_stack_terminal» :=
  coreProgram_find?_at (j := idx% «check_stack_terminal») rfl

/-- The callers' pairs of the chain. -/
theorem chain_callers : (name% «main_loop4», "main") ∈ Res.termCallers ∧
    (name% «verify_sub», name% «main_loop4») ∈ Res.termCallers ∧
    (name% «check_stack_terminal», name% «verify_sub») ∈ Res.termCallers := by
  refine ⟨CoreMode.FnReg.stCallers_of_column_selector _ ?_, CoreMode.FnReg.stCallers_of_column_selector _ ?_,
    CoreMode.FnReg.stCallers_of_column_selector _ ?_⟩ <;> decide +kernel

theorem sts_callers_b : (List.range 5).all (fun i ↦ decide ((stsName (i + 4), name% «check_stack_terminal») ∈
    CoreMode.Own.column_selector.stCallers)) = true := by
  decide +kernel

theorem cs_callers_b : (List.range 5).all (fun i ↦ (List.range 31).all fun κ ↦ !decide (κ < 4 * (i + 4)) ||
    decide ((cselName (i + 4) κ, stsName (i + 4)) ∈ CoreMode.Own.column_selector.stCallers)) = true := by
  decide +kernel

/-- `stack_selectors__L{n}`'s caller is `check_stack_terminal`. -/
theorem sts_callers {n : ℕ} (h4 : 4 ≤ n) (h8 : n ≤ 8) : (stsName n, name% «check_stack_terminal») ∈ Res.termCallers := by
  refine CoreMode.FnReg.stCallers_of_column_selector _ ?_
  have := List.all_eq_true.mp sts_callers_b (n - 4) (List.mem_range.mpr (by omega))
  rw [show n - 4 + 4 = n by omega] at this
  exact of_decide_eq_true this

/-- `column_selector__L{n}_L{κ}`'s caller is `stack_selectors__L{n}`, `κ < 4n`. -/
theorem cs_callers {n κ : ℕ} (h4 : 4 ≤ n) (h8 : n ≤ 8) (hκn : κ < 4 * n) (hκ : κ < 31) :
    (cselName n κ, stsName n) ∈ Res.termCallers := by
  refine CoreMode.FnReg.stCallers_of_column_selector _ ?_
  have := List.all_eq_true.mp (List.all_eq_true.mp cs_callers_b (n - 4) (List.mem_range.mpr (by omega))) κ
    (List.mem_range.mpr hκ)
  rw [show n - 4 + 4 = n by omega] at this
  simp only [Bool.or_eq_true, Bool.not_eq_true', decide_eq_false_iff_not, decide_eq_true_eq] at this
  exact this.resolve_left (by omega)

theorem cs_inj_b : (List.range 5).all (fun i ↦ (List.range 31).all fun a ↦ (List.range 31).all fun b ↦
    cselName (i + 4) a != cselName (i + 4) b || a == b) = true := by
  decide +kernel

/-- `column_selector`'s specializations at `n` nibbles are named apart. -/
theorem cs_inj {n a b : ℕ} (h4 : 4 ≤ n) (h8 : n ≤ 8) (ha : a < 31) (hb : b < 31) (h : cselName n a = cselName n b) :
    a = b := by
  have := List.all_eq_true.mp (List.all_eq_true.mp (List.all_eq_true.mp cs_inj_b (n - 4)
    (List.mem_range.mpr (by omega))) a (List.mem_range.mpr ha)) b (List.mem_range.mpr hb)
  rw [show n - 4 + 4 = n by omega, h] at this
  simpa using this

theorem names_b : (List.range 5).all (fun i ↦ (List.range 5).all fun i' ↦ (List.range 31).all fun κ ↦
      "selector_tables__L" ++ B1.Whir.natStr (i + 4) != cselName (i' + 4) κ) ∧
    (List.range 5).all (fun i ↦ "main" != stsName (i + 4) && (List.range 31).all fun κ ↦ "main" != cselName (i + 4) κ) ∧
    "main" ≠ name% «main_loop4» ∧ "main" ≠ name% «verify_sub» ∧ "main" ≠ name% «check_stack_terminal» := by
  decide +kernel

theorem sel_ne_cs {n n' κ : ℕ} (h4 : 4 ≤ n) (h8 : n ≤ 8) (h4' : 4 ≤ n') (h8' : n' ≤ 8) (hκ : κ < 31) :
    "selector_tables__L" ++ B1.Whir.natStr n ≠ cselName n' κ := by
  have := List.all_eq_true.mp (List.all_eq_true.mp (List.all_eq_true.mp names_b.1 (n - 4)
    (List.mem_range.mpr (by omega))) (n' - 4) (List.mem_range.mpr (by omega))) κ (List.mem_range.mpr hκ)
  rw [show n - 4 + 4 = n by omega, show n' - 4 + 4 = n' by omega] at this
  simpa using this

/-- A function of the template `cselBody` or `stsBody` is no loop: it returns a value. -/
theorem loop_of_ret {fn : Fn} {pre : List Stmt} {v : V} (h : fn.body = pre ++ [.ret [v]]) : fn.loop = false := by
  unfold Core.Fn.loop
  rw [h, List.reverse_append]
  simp

theorem cs_not_loop {n κ : ℕ} {fn : Fn} (h : fn.body = cselBody n κ) : fn.loop = false :=
  loop_of_ret (h.trans rfl)

theorem sts_not_loop {n : ℕ} {fn : Fn} (h : fn.body = stsBody n) : fn.loop = false :=
  loop_of_ret (h.trans rfl)

/-- A parameter's word is its argument's. -/
theorem param_of {fn : Fn} {σ σI : Val} {args : List V} {k : ℕ} {v a : V}
    (hpar : fn.params.map σ = args.map σI) (hp : fn.params[k]? = some v) (ha : args[k]? = some a) : σ v = σI a := by
  have := congrArg (·[k]?) hpar
  simp only [List.getElem?_map, hp, ha, Option.map_some, Option.some.injEq] at this
  exact this

/-- **A top-level call is on every returning path.** -/
theorem scanCall_sound {σ : Val} {p : String → List V → List V → Bool} :
    ∀ {ss : List Stmt} {es : List Ev} {vs : List V}, Res.scanCall p ss = true → walk σ ss = .ret es vs →
      ∃ f args rets, p f args rets = true ∧ Ev.call f args rets ∈ es
  | [], _, _, h, _ => by simp [Res.scanCall] at h
  | s :: ss, es, vs, h, hw => by
    simp only [Res.scanCall, Bool.or_eq_true, Bool.and_eq_true] at h
    rcases h with h | ⟨hn, h⟩
    · cases s with
      | call f args rets =>
        rw [walk] at hw
        simp only [walk1, Out.seq] at hw
        cases h2 : walk σ ss with
        | fall _ => rw [h2] at hw; simp [Out.pre] at hw
        | ret es2 vs2 =>
          rw [h2] at hw
          simp only [Out.pre, Out.ret.injEq] at hw
          exact ⟨f, args, rets, h, by rw [← hw.1]; exact List.mem_cons_self⟩
        | stuck => rw [h2] at hw; simp [Out.pre] at hw
      | _ => simp at h
    · obtain ⟨es1, es2, -, h2, rfl⟩ := Res.walk_cons_noRet hn hw
      obtain ⟨f, args, rets, hp, he⟩ := scanCall_sound h h2
      exact ⟨f, args, rets, hp, List.mem_append_right _ he⟩

/-- `stack_selectors`' block `b`'s statements are its body's. -/
theorem sts_blk_mem {n b : ℕ} (hb : b < 52) {s : Stmt} (hs : s ∈ stsBlock n b) : s ∈ stsBodyA n := by
  unfold stsBodyA
  exact List.mem_append_left _ (List.mem_append_right _
    (List.mem_flatten.mpr ⟨_, List.mem_map.mpr ⟨b, List.mem_range.mpr hb, rfl⟩, hs⟩))

/-- **A slice of `verify_sub`'s statements holds** when its statements before the `ret` do. -/
theorem vs_slice {C : CallRel} {rd : Reader} {σ : Val} {kret : List E → Prop}
    (h : Stmt.HoldsList C rd σ B1.VerifySub.vsPre True kret) {a m : ℕ} {T : List Stmt}
    (hT : (B1.VerifySub.vsPre.drop a).take m = T) : Stmt.HoldsList C rd σ T True kret := by
  refine B1.VerifySub.holdsList_of_forall _ fun s hs ↦ ?_
  subst hT
  have hs' : s ∈ B1.VerifySub.vsPre := List.mem_of_mem_drop (List.mem_of_mem_take hs)
  exact ⟨B1.VerifySub.noRet_of_mem B1.VerifySub.vsPre_noRet s hs',
    B1.VerifySub.holds_of_noRetList _ B1.VerifySub.vsPre_noRet h s hs'⟩

theorem sizeBits_eq : B1.sizeBits = 34 := by decide

/-- **The nibble shares from the exponent tables**: at `q·g^34`. -/
theorem shares_of {rd : Reader} {q : E} (h : B1.ExpTables rd q) : SharesAt rd (q * gen ^ 34) := by
  intro j hj u hu
  rw [B1.loadHolds_mul_gen_pow]
  have := h.2 j hj u hu
  rw [sizeBits_eq] at this
  rw [show 34 + (16 * j + u) = 34 + 16 * j + u by omega]
  exact this

end

/-! ## Down the chain -/

section

variable {al : String → Bool} {D : Ref → RefD} {r : Ref}

public section

/-- **The blocks `verify_sub` places**, at an honest instance with the exponent tables at its `g_squares`. -/
theorem vs_blocks (hR : RefH (layB al) (D r) r) (hr : r.Ok) {I : Inst} (hI : I ∈ instsR al D r) {σ : Val}
    {bufs : List ℕ} {kids : List Tree} (ht : I.t = .node name% «verify_sub» σ bufs kids)
    (hexp : B1.ExpTables r.img.read (σ (.n (val% «verify_sub» "g_squares")))) :
    BlocksAt r.img.read (σ (.n (val% «verify_sub» "offs"))) (σ (.n (val% «verify_sub» "kaps"))) := by
  have hκ28 : r.κ ≤ 28 := hr.log
  have hκ23 : 23 ≤ r.κ := by rw [hR.κ]; exact twentyThree_le_logMem _
  obtain ⟨args, rets, hv⟩ := inst_validA hR hI ht
  obtain ⟨-, hb⟩ := Res.holds_of_valid Res.fs_pos hv find_vs
  rw [B1.VerifySub.vs_body_eq, Core.holdsList_append] at hb
  have hpre := ((Core.holdsList_noRet _ B1.VerifySub.vsPre_noRet _ _).mp hb).1
  have hbl : (List.replicate (2 ^ (B1.Main.bytecodeLog + bytecodeSlotBits)) (0 : K)).length =
      2 ^ (B1.Main.bytecodeLog + bytecodeSlotBits) := List.length_replicate
  have S := B1.VerifySub.sizesOk (by omega) (by omega) r.img (fun _ _ _ h ↦ Res.KidRel.rel h) hbl hexp
    (vs_slice hpre B1.VerifySub.vsReadsT_eq) (vs_slice hpre B1.VerifySub.vsHeightsT_eq)
    (vs_slice hpre B1.VerifySub.vsStackT_eq)
  intro b hb
  obtain ⟨p, hp, ho, hk⟩ := S.placed.2 b (by rw [B1.Stack.nStkBlocks, B1.Stack.stackBlocks_length]; exact hb)
  obtain ⟨hal, hle⟩ := placement_aligned S.build hp
  have h30 := Nat.pow_le_pow_right (n := 2) (by norm_num) S.st2
  have h1 := Nat.one_le_two_pow (n := p.variableCount)
  have hv30 : 2 ^ p.variableCount ≤ 2 ^ 30 := by omega
  have hv : p.variableCount ≤ 30 := (Nat.pow_le_pow_iff_right (by norm_num)).mp hv30
  have h32 : (2 : ℕ) ^ 30 ≤ 2 ^ 32 := Nat.pow_le_pow_right (by norm_num) (by norm_num)
  exact ⟨p.index, p.variableCount, by omega, by omega, hal, ho, hk⟩

/-- **The Keccak table's kappa source `verify_sub` certifies**: the word at `kappa_base·g^7` is `g^e`, `e ≤ 24` (a
table's log height, `SizesOk.heights24`), at an honest instance with the exponent tables at its `g_squares`. -/
theorem vs_kappa (hR : RefH (layB al) (D r) r) (hr : r.Ok) {I : Inst} (hI : I ∈ instsR al D r) {σ : Val}
    {bufs : List ℕ} {kids : List Tree} (ht : I.t = .node name% «verify_sub» σ bufs kids)
    (hexp : B1.ExpTables r.img.read (σ (.n (val% «verify_sub» "g_squares")))) :
    ∃ e < 25, LoadHolds r.img.read (σ (.n (val% «verify_sub» "kappa_base"))) 7 (gen ^ e) := by
  have hκ28 : r.κ ≤ 28 := hr.log
  have hκ23 : 23 ≤ r.κ := by rw [hR.κ]; exact twentyThree_le_logMem _
  obtain ⟨args, rets, hv⟩ := inst_validA hR hI ht
  obtain ⟨-, hb⟩ := Res.holds_of_valid Res.fs_pos hv find_vs
  rw [B1.VerifySub.vs_body_eq, Core.holdsList_append] at hb
  have hpre := ((Core.holdsList_noRet _ B1.VerifySub.vsPre_noRet _ _).mp hb).1
  have hbl : (List.replicate (2 ^ (B1.Main.bytecodeLog + bytecodeSlotBits)) (0 : K)).length =
      2 ^ (B1.Main.bytecodeLog + bytecodeSlotBits) := List.length_replicate
  have S := B1.VerifySub.sizesOk (by omega) (by omega) r.img (fun _ _ _ h ↦ Res.KidRel.rel h) hbl hexp
    (vs_slice hpre B1.VerifySub.vsReadsT_eq) (vs_slice hpre B1.VerifySub.vsHeightsT_eq)
    (vs_slice hpre B1.VerifySub.vsStackT_eq)
  have F := B1.VerifySub.readsFacts (vs_slice hpre B1.VerifySub.vsReadsT_eq)
  have h7 := F.kb.2.2 7 (by simp)
  simp only [List.getElem_map, List.getElem_range] at h7
  rw [show 113 + 7 = 115 + 5 from rfl, B1.VerifySub.vsHeight5 S] at h7
  exact ⟨_, by have := S.heights24 5 (by decide); omega, h7⟩

/-- **The sizes `verify_sub` certifies**, at an honest instance with the exponent tables at its `g_squares`: `gmv`,
`g_log_mem`, `g_n` (its link shape's), each table's height source and each sent target's block's kappa (`CstQ`). -/
theorem vs_cst (hR : RefH (layB al) (D r) r) (hr : r.Ok) {I : Inst} (hI : I ∈ instsR al D r) {σ : Val}
    {bufs : List ℕ} {kids : List Tree} (ht : I.t = .node name% «verify_sub» σ bufs kids)
    (hexp : B1.ExpTables r.img.read (σ (.n (val% «verify_sub» "g_squares")))) :
    (∃ s ≤ 30, σ (.n (val% «verify_sub» "gmv")) = gen ^ s) ∧
      (∃ l ≤ 30, σ (.n (val% «verify_sub» "g_log_mem")) = gen ^ l) ∧
      ∃ n ≤ 24, σ (.n 408) = gen ^ n ∧
        (∀ t < 6, ∃ e ≤ n, LoadHolds r.img.read (σ (.n (val% «verify_sub» "kappa_base"))) (2 + t) (gen ^ e)) ∧
        ∀ b ∈ CoreMode.Own.check_stack_terminal.sentBlocks, ∃ e ≤ n,
          LoadHolds r.img.read (σ (.n (val% «verify_sub» "kaps"))) b (gen ^ e) := by
  have hκ28 : r.κ ≤ 28 := hr.log
  have hκ23 : 23 ≤ r.κ := by rw [hR.κ]; exact twentyThree_le_logMem _
  obtain ⟨args, rets, hv⟩ := inst_validA hR hI ht
  obtain ⟨-, hb⟩ := Res.holds_of_valid Res.fs_pos hv find_vs
  rw [B1.VerifySub.vs_body_eq, Core.holdsList_append] at hb
  have hpre := ((Core.holdsList_noRet _ B1.VerifySub.vsPre_noRet _ _).mp hb).1
  have hbl : (List.replicate (2 ^ (B1.Main.bytecodeLog + bytecodeSlotBits)) (0 : K)).length =
      2 ^ (B1.Main.bytecodeLog + bytecodeSlotBits) := List.length_replicate
  have S := B1.VerifySub.sizesOk (by omega) (by omega) r.img (fun _ _ _ h ↦ Res.KidRel.rel h) hbl hexp
    (vs_slice hpre B1.VerifySub.vsReadsT_eq) (vs_slice hpre B1.VerifySub.vsHeightsT_eq)
    (vs_slice hpre B1.VerifySub.vsStackT_eq)
  have F := B1.VerifySub.readsFacts (vs_slice hpre B1.VerifySub.vsReadsT_eq)
  obtain ⟨hlmL, hlm, -⟩ := B1.Stack.buildLayout_some S.build
  obtain ⟨n, hn, gn, hle⟩ := B1.VerifySub.vs_gn (by omega) (by omega) r.img S
    (vs_slice hpre B1.VerifySub.vsShapeAT_eq)
  refine ⟨⟨_, S.st2, S.placed.1⟩, ⟨_, by rw [hlmL]; exact hlm, S.logMem⟩, n, hn, gn, fun t ht ↦ ?_, fun b hb ↦ ?_⟩
  · have h := F.kb.2.2 (2 + t) (by simp; omega)
    simp only [List.getElem_map, List.getElem_range] at h
    rw [show 113 + (2 + t) = 115 + t by omega, B1.VerifySub.vsHeight S ht] at h
    exact ⟨_, hle t ht, h⟩
  · obtain ⟨t, ht, h⟩ := B1.VerifySub.sent_kappas S hb
    exact ⟨_, hle t ht, h⟩

/-- **`CsQ` passes down a call.** -/
theorem csQ_stepA (hR : RefH (layB al) (D r) r) (hr : r.Ok) :
    Res.KidStep coreProgram r.img.read B2C.H (instsR al D r) (CsQ r) := by
  intro I hI fI σI bufsI kidsI hIt fnI hfI es vs hw hh i c J hci hJS hk _ _ hname hval hph hQI
    f σ bufs kids hJt
  have hct : c.taken = true := by
    cases h : c.taken
    · obtain ⟨g', σ', h'⟩ := hph h
      rw [hJt] at h'; cases h'
    · rfl
  have hJv := hval hct
  rw [hJt] at hJv
  obtain ⟨fn, hfn, hpar, -⟩ := hJv
  have hcf : c.f = f := by rw [← hname, hJt]; rfl
  have hc : c ∈ calls es := List.mem_of_getElem? hci
  have hnI := find_name' hfI
  have hQ := hQI fI σI bufsI kidsI hIt
  -- the caller of a listed callee
  have hcaller : ∀ g, (f, g) ∈ Res.termCallers → fI = g ∨ (fI = f ∧ fnI.loop = true) := by
    intro g hg
    have hcal := List.all_eq_true.mp (Res.calls_sites (Res.termCallers_all fnI (List.mem_of_find?_eq_some hfI))
      hw c hc) _ hg
    rw [hcf] at hcal
    simp only [bne_self_eq_false, Bool.false_or, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq] at hcal
    rcases hcal with h | ⟨h, hl⟩
    · exact Or.inl (by rw [← hnI, h])
    · exact Or.inr ⟨by rw [← hnI, h], hl⟩
  have hsite : ∀ {p : String → List V → List V → Bool}, Res.sitesB p fnI.body = true →
      p c.f c.args c.rets = true :=
    fun hs ↦ Res.calls_sites hs hw c hc
  obtain ⟨hcm, hcv, hcc⟩ := chain_callers
  refine ⟨fun hf ↦ ?_, fun hf ↦ ?_, fun hf ↦ ?_, fun n h4 h8 hf ↦ ?_, fun n κ h4 h8 hκn hκ hf ↦ ?_⟩
  · -- `main_loop4`: from `main`'s `exponent_tables`, or its own
    subst hf
    obtain rfl : fn = fn% «main_loop4» := Option.some.inj (hfn.symm.trans find_ml4)
    obtain ⟨hps, hs⟩ := ml4_facts
    have h14 : (fn% «main_loop4»).params[14]? = some (.n 14) := by rw [hps]; rfl
    rcases hcaller _ hcm with h | ⟨h, -⟩
    · subst h
      obtain rfl : fnI = fn% «main» := Option.some.inj (hfI.symm.trans find_main)
      obtain ⟨hscan, hsm⟩ := main_facts
      have hs1 := hsite hsm
      rw [hcf] at hs1
      simp only [bne_self_eq_false, Bool.false_or, beq_iff_eq] at hs1
      rw [param_of hpar h14 hs1]
      obtain ⟨g, args, rets, hp, he⟩ := scanCall_sound hscan hw
      simp only [Bool.and_eq_true, beq_iff_eq, List.isEmpty_iff] at hp
      obtain ⟨⟨rfl, rfl⟩, rfl⟩ := hp
      obtain ⟨args', rets', hv⟩ := inst_validA hR hI hIt
      obtain ⟨fn', hf', -, es', vs', hw', -, -, hk'⟩ := hv
      obtain rfl : fn% «main» = fn' := Option.some.inj (hfI.symm.trans hf')
      rw [hw] at hw'
      obtain ⟨rfl, -⟩ := Out.ret.inj hw'
      exact (End.expTablesSound _ _ (Tree.KidsValid.rel σI kidsI (calls es) hk' _ (mem_calls_of_call he) rfl)).1
    · subst h
      obtain rfl : fnI = fn% «main_loop4» := Option.some.inj (hfI.symm.trans find_ml4)
      have hs1 := hsite hs
      rw [hcf] at hs1
      simp only [bne_self_eq_false, Bool.false_or, Bool.and_eq_true, beq_iff_eq] at hs1
      rw [param_of hpar h14 hs1.1]
      exact hQ.1 rfl
  · -- `verify_sub`: from `main_loop4`
    subst hf
    obtain rfl : fn = fn% «verify_sub» := Option.some.inj (hfn.symm.trans find_vs)
    obtain ⟨hps, hlp, -⟩ := vs_facts
    have h4 : (fn% «verify_sub»).params[4]? = some (.n 4) := by rw [hps]; rfl
    rcases hcaller _ hcv with h | ⟨h, hl⟩
    · subst h
      obtain rfl : fnI = fn% «main_loop4» := Option.some.inj (hfI.symm.trans find_ml4)
      have hs1 := hsite ml4_facts.2
      rw [hcf] at hs1
      simp only [bne_self_eq_false, Bool.false_or, Bool.and_eq_true, beq_iff_eq] at hs1
      rw [param_of hpar h4 hs1.2]
      exact hQ.1 rfl
    · rw [h] at hfI
      obtain rfl : fnI = fn% «verify_sub» := Option.some.inj (hfI.symm.trans find_vs)
      rw [hlp] at hl; cases hl
  · -- `check_stack_terminal`: from `verify_sub`, its stack placed
    subst hf
    obtain rfl : fn = fn% «check_stack_terminal» := Option.some.inj (hfn.symm.trans find_cst)
    obtain ⟨hps, hlp, -⟩ := cst_facts
    rcases hcaller _ hcc with h | ⟨h, hl⟩
    · subst h
      obtain rfl : fnI = fn% «verify_sub» := Option.some.inj (hfI.symm.trans find_vs)
      have hs1 := hsite vs_facts.2.2
      rw [hcf] at hs1
      simp only [bne_self_eq_false, Bool.false_or, Bool.and_eq_true, beq_iff_eq] at hs1
      obtain ⟨⟨⟨⟨⟨⟨h0, h2⟩, h3⟩, h1⟩, h4⟩, h6⟩, h8⟩ := hs1
      have hexp : B1.ExpTables r.img.read (σI (.n (val% «verify_sub» "g_squares"))) := hQ.2.1 rfl
      have e0 := param_of hpar (k := 0) (by rw [hps]; rfl) h0
      have e1 := param_of hpar (k := 1) (by rw [hps]; rfl) h1
      have e2 := param_of hpar (k := 2) (by rw [hps]; rfl) h2
      have e3 := param_of hpar (k := 3) (by rw [hps]; rfl) h3
      have e4 := param_of hpar (k := 4) (by rw [hps]; rfl) h4
      have e6 := param_of hpar (k := 6) (by rw [hps]; rfl) h6
      have e8 := param_of hpar (k := 8) (by rw [hps]; rfl) h8
      refine ⟨by rw [e0]; exact hexp, by rw [e2, e3]; exact vs_blocks hR hr hI hIt hexp,
        by rw [e1]; exact vs_kappa hR hr hI hIt hexp, ?_⟩
      unfold CstQ
      rw [e4, e8, e6, e1, e3]
      exact vs_cst hR hr hI hIt hexp
    · rw [h] at hfI
      obtain rfl : fnI = fn% «check_stack_terminal» := Option.some.inj (hfI.symm.trans find_cst)
      rw [hlp] at hl; cases hl
  · -- `stack_selectors__L{n}`: from `check_stack_terminal`
    subst hf
    obtain ⟨fs, hfs, hps, hbody⟩ := sts_found n h4 h8
    obtain rfl : fn = fs := Option.some.inj (hfn.symm.trans hfs)
    rcases hcaller _ (sts_callers h4 h8) with h | ⟨h, hl⟩
    · subst h
      obtain rfl : fnI = fn% «check_stack_terminal» := Option.some.inj (hfI.symm.trans find_cst)
      have hs1 := hsite cst_facts.2.2
      rw [hcf] at hs1
      simp only [Bool.or_eq_true, beq_iff_eq] at hs1
      rcases hs1 with hs1 | hs1
      · have := List.all_eq_true.mp hs1 (n - 4) (List.mem_range.mpr (by omega))
        rw [show n - 4 + 4 = n by omega] at this
        simp at this
      rw [hs1, hps] at hpar
      simp only [List.map_cons, List.map_nil, List.cons.injEq] at hpar
      obtain ⟨e0, e1, -, -, e4, -⟩ := hpar
      rw [e0, e1, e4]
      exact ⟨(hQ.2.2.1 rfl).1, (hQ.2.2.1 rfl).2.1⟩
    · rw [h] at hfI
      obtain rfl : fnI = fn := Option.some.inj (hfI.symm.trans hfs)
      rw [sts_not_loop hbody] at hl; cases hl
  · -- `column_selector__L{n}_L{κ}`: from `stack_selectors__L{n}`, its block's dispatch at its kappa
    subst hf
    obtain ⟨fc, hfc, hpc, hbc⟩ := cs_found n κ h4 h8 hκn hκ
    obtain rfl : fn = fc := Option.some.inj (hfn.symm.trans hfc)
    rcases hcaller _ (cs_callers h4 h8 hκn hκ) with h | ⟨h, hl⟩
    swap
    · rw [h] at hfI
      obtain rfl : fnI = fn := Option.some.inj (hfI.symm.trans hfc)
      rw [cs_not_loop hbc] at hl; cases hl
    subst h
    obtain ⟨fs, hfs, -, hbody⟩ := sts_found n h4 h8
    obtain rfl : fnI = fs := Option.some.inj (hfI.symm.trans hfs)
    obtain ⟨hexp, hB⟩ := hQ.2.2.2.1 n h4 h8 rfl
    -- the body's statements
    obtain ⟨args', rets', hv⟩ := inst_validA hR hI hIt
    obtain ⟨-, hb⟩ := Res.holds_of_valid Res.fs_pos hv hfI
    rw [hbody, stsBody, B1.Whir.holdsList_flat_ret _ (B1.Stack.stsBodyA_flat n)] at hb
    obtain ⟨hA, -⟩ := hb
    choose! idx kap hkap hidx hal hoff hkb using hB
    have hsel : ∀ b < 52, σI (.n (10 + 5 * b)) = ofK (addressOfIndex (kap b)) := by
      intro b hb
      have hl : LoadHolds r.img.read (σI (.n 1)) b (σI (.n (10 + 5 * b))) :=
        hA (.atom (.load (.n (10 + 5 * b)) (.n 1) b)) (sts_blk_mem hb (by simp [stsBlock]))
      rw [B1.loadHolds_unique hl (hkb b hb), Value.gen_pow_eq_ofK]
    have hwalk := B1.VsC.walk_stsBody σI n kap hkap hsel
    rw [hbody] at hw
    rw [hw] at hwalk
    obtain ⟨rfl, -⟩ := Out.ret.inj hwalk
    rw [B1.VsC.calls_stsEvs] at hci
    cases i with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hci
      subst hci
      exact absurd hcf (sel_ne_cs h4 h8 h4 h8 hκ)
    | succ i =>
      rw [List.getElem?_cons_succ] at hci
      obtain ⟨b, hb, rfl⟩ := List.mem_map.mp (List.mem_of_getElem? hci)
      have hb' := List.mem_range.mp hb
      have hkb' : kap b = κ := cs_inj h4 h8 (hkap b hb') hκ hcf
      simp only [B1.VsC.cselCall, hpc, List.map_cons, List.map_nil, List.cons.injEq] at hpar
      obtain ⟨e0, -, e2, -⟩ := hpar
      have hl0 : LoadHolds r.img.read (σI (.n 0)) b (σI (.n (7 + 5 * b))) :=
        hA (.atom (.load (.n (7 + 5 * b)) (.n 0) b)) (sts_blk_mem hb' (by simp [stsBlock]))
      have hc8 : σI (.n (8 + 5 * b)) = B1.Stack.csW 34 :=
        hA (.atom (.const (.n (8 + 5 * b)) (B1.Stack.csW 34))) (sts_blk_mem hb' (by simp [stsBlock, B1.Whir.osCst]))
      have hm9 : σI (.n (9 + 5 * b)) = σI (.n 4) * σI (.n (8 + 5 * b)) :=
        hA (.atom (.mul (.n (9 + 5 * b)) (.n 4) (.n (8 + 5 * b)))) (sts_blk_mem hb' (by simp [stsBlock, B1.Whir.osMul]))
      refine ⟨idx b, hidx b hb', hkb' ▸ hal b hb', ?_, ?_⟩
      · rw [e0]; exact B1.loadHolds_unique hl0 (hoff b hb')
      · rw [e2, hm9, hc8, B1.Stack.csW_eq (by norm_num)]
        exact shares_of hexp

/-- **`CsQ` at every honest instance.** -/
theorem csQ_allA (hR : RefH (layB al) (D r) r) (hr : r.Ok) : ∀ J ∈ instsR al D r, CsQ r J := by
  refine insts_allA hR (csQ_stepA hR hr) fun J hm ↦ ?_
  intro f σ bufs kids hJt
  have hn := hm _ _ _ _ hJt
  subst hn
  obtain ⟨-, hb2, h1, h2, h3⟩ := names_b
  refine ⟨fun h ↦ absurd h h1, fun h ↦ absurd h h2, fun h ↦ absurd h h3, fun n h4 h8 h ↦ ?_,
    fun n κ h4 h8 _ hκ h ↦ ?_⟩
  · have := List.all_eq_true.mp hb2 (n - 4) (List.mem_range.mpr (by omega))
    rw [show n - 4 + 4 = n by omega] at this
    simp only [Bool.and_eq_true, bne_iff_ne, ne_eq] at this
    exact absurd h this.1
  · have := List.all_eq_true.mp hb2 (n - 4) (List.mem_range.mpr (by omega))
    rw [show n - 4 + 4 = n by omega] at this
    simp only [Bool.and_eq_true, bne_iff_ne, ne_eq] at this
    have := List.all_eq_true.mp this.2 κ (List.mem_range.mpr hκ)
    simp only [bne_iff_ne, ne_eq] at this
    exact absurd h this

end

end

end LeanVM.Guest.EndExec
