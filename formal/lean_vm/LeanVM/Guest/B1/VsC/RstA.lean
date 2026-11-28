/-
  LeanVM.Guest.B1.VsC.RstA

  `ring_switch_target` completes placed: `RingSwitchTargetCompleteA`.
-/

module

public import LeanVM.Guest.B1.VsC.RstLoopA
public import LeanVM.Guest.B1.VsC.Vsc8CalleesA
public import LeanVM.Guest.B1.VsC.FwdCalls
public import LeanVM.Guest.Complete.ComposeRd
public import LeanVM.Guest.B1.VsC.CalleesB
import LeanVM.Guest.ValRef
import LeanVM.Guest.Data.ValNames.«ring_switch_target»

/-!
# `ring_switch_target`, placed

`ring_switch_target(slices, map_challenges)` (`rstT`), placed at frame `fp` and cursor `c`: its
`HeapBuf` `rs_chain` of `72` words at `c`, its own words the honest chain `rsChain s G` there
(`G` the challenges `g_0 .. g_7`); its loop (`rl_placed`) at the aligned base past it. On each
memory the valuation is the forward evaluation (`fwdVal`), the `HeapBuf` pointer `g^c` its oracle
(`callAtA_nodeRd`): every atom holds, the stores of the zero row by the chain's row `0`; the
returned word is `ringTarget` by the guest stream's soundness (`ring_switch_target_holds`) on the
node's own valid tree. `rst_complete`: `RingSwitchTargetCompleteA`, the pointers in `K` (else no
memory holds the slices).
-/

namespace LeanVM.Guest.B1.VsC

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Memory LeanVM.Guest.B1
open LeanVM.Guest.Complete LeanVM.Guest.B1.Fwd LeanVM.Guest.Value LeanVM.Guest.B1.VerifySub
open LeanVM.Protocol.Verifier
open LeanVM.Prover.Exec (allocBase)

@[expose] public section

/-! ## The template's facts -/

/-- `ring_switch_target`'s body before its return. -/
def rstPre : List Stmt :=
  [.atom (.hint (.alloc (.n (val% «ring_switch_target» "rs_chain")) 72))] ++
  ((List.range 8).map fun p ↦
    [Stmt.atom (.const (.n ((val% «ring_switch_target» "s1.u0.s0#0") + p)) (word 0 0)), .atom (.load (.n ((val% «ring_switch_target» "s1.u0.s0#0") + p)) (.n (val% «ring_switch_target» "rs_chain")) p)]).flatten ++
  [.atom (.const (.n (val% «ring_switch_target» "s2#0")) (word 1 0)), .call name% «ring_switch_target_loop0» [.n (val% «ring_switch_target» "s2#0"), .n (val% «ring_switch_target» "map_challenges"), .n (val% «ring_switch_target» "slices"),
      .n (val% «ring_switch_target» "rs_chain")] [],
    .atom (.const (.n (val% «ring_switch_target» "sums~0")) (word 27 0)), .atom (.mul (.n (val% «ring_switch_target» "sums")) (.n (val% «ring_switch_target» "rs_chain")) (.n (val% «ring_switch_target» "sums~0"))),
    .atom (.load (.n (val% «ring_switch_target» "total@1~0")) (.n (val% «ring_switch_target» "map_challenges")) 0), .atom (.load (.n (val% «ring_switch_target» "total@1~1")) (.n (val% «ring_switch_target» "sums")) 0),
    .atom (.mul (.n (val% «ring_switch_target» "total@1")) (.n (val% «ring_switch_target» "total@1~0")) (.n (val% «ring_switch_target» "total@1~1")))] ++
  ((List.range 7).map fun p ↦ tbBlock (p + 1)).flatten ++
  [.atom (.const (.n (val% «ring_switch_target» "s6#1")) (word 9223372036854775808 0)), .atom (.mul (.n (val% «ring_switch_target» "s6#0")) (.n (val% «ring_switch_target» "total@8")) (.n (val% «ring_switch_target» "s6#1")))]

abbrev rstChain : ℕ := val% «ring_switch_target» "rs_chain"
abbrev rstSums : ℕ := val% «ring_switch_target» "sums"
abbrev rstRet : ℕ := val% «ring_switch_target» "s6#0"

theorem rstT_split : rstT = rstPre ++ [.ret [.n rstRet]] := by
  simp only [rstT, rstPre, List.append_assoc, List.cons_append, List.nil_append]

/-- The zero row's stores. -/
def rstStores : List Atom :=
  (List.range 8).map fun p => .load (.n ((val% «ring_switch_target» "s1.u0.s0#0") + p)) (.n rstChain) p

/-- The body's `HeapBuf`. -/
abbrev rstAlloc : Atom := .hint (.alloc (.n rstChain) 72)

/-- An atom of the body: its `HeapBuf`, or a load through the challenges, the sums or the chain. -/
def rstAtomOk (a : Atom) : Bool := decide (a = rstAlloc) || loadOkB [(1, 16), (rstSums, 8), (rstChain, 8)] a

/-- The loop's call. -/
def rstCall : Call := ⟨rlName, [.n (val% «ring_switch_target» "s2#0"), .n 1, .n 0, .n rstChain], [], true⟩

/-- What the kernel checks of `ring_switch_target`. -/
def rstChecks : Bool :=
  (chk 2 rstT).isSome && decide (storesOf 2 rstT = rstStores) && rstPre.all atomOrCall &&
    (atomsOf rstPre).all rstAtomOk &&
    decide (rstPre.filterMap Stmt.allocSz = [(.n rstChain, .inl 72)]) && decide (rstPre.filterMap Stmt.addrS = [])

set_option maxRecDepth 100000 in
theorem rstChecks_ok : rstChecks = true := by decide +kernel

theorem rst_params : (fn% «ring_switch_target»).params = [.n 0, .n 1] := rfl

set_option maxRecDepth 100000 in
theorem rst_callsOfB : callsOfB rstPre = [rstCall] := rfl

/-- The valuation on a memory: the forward evaluation, the `HeapBuf` at `g^c`. -/
noncomputable def rstVal (c isl im : ℕ) (rd : Reader) : Val :=
  fwdVal rd (fun _ => ptrAt c) [ptrAt isl, ptrAt im] (fn% «ring_switch_target»).body

/-- The events of a body of atoms and calls. -/
theorem mem_slEvs_aoc {σ : Val} : ∀ {ss : List Stmt}, ss.all atomOrCall = true → ∀ {e : Ev},
    e ∈ ss.flatMap (slEvs σ) → (∃ a, e = .atom a ∧ Stmt.atom a ∈ ss) ∨
      ∃ f args rets, e = .call f args rets ∧ Stmt.call f args rets ∈ ss
  | [], _, _, h => by simp at h
  | s :: ss, hs, e, h => by
    simp only [List.all_cons, Bool.and_eq_true] at hs
    rw [List.flatMap_cons, List.mem_append] at h
    rcases h with h | h
    · cases s with
      | atom a => simp only [slEvs, List.mem_singleton] at h; exact Or.inl ⟨a, h, List.mem_cons_self⟩
      | call f args rets =>
        simp only [slEvs, List.mem_singleton] at h; exact Or.inr ⟨f, args, rets, h, List.mem_cons_self⟩
      | _ => simp [atomOrCall] at hs
    · rcases mem_slEvs_aoc hs.2 h with ⟨a, he, ha⟩ | ⟨f, args, rets, he, hc⟩
      · exact Or.inl ⟨a, he, List.mem_cons_of_mem _ ha⟩
      · exact Or.inr ⟨f, args, rets, he, List.mem_cons_of_mem _ hc⟩


/-! ## The node -/

variable {fs : String → ℕ} {al : String → Bool} {cert : String → V → ℕ}

theorem ptrAt_addr (a t : ℕ) : (ptrAt a).limb 0 * addressOfIndex t = addressOfIndex (a + t) := by
  simp [ptrAt, addressOfIndex, pow_add]

/-- **`ring_switch_target` completes placed** on pointers `g^isl`, `g^im`: its chain at its cursor,
its loop past it. -/
theorem rst_placed {k im isl : ℕ} {s ch : List E} (hs : s.length = 64) (hch : ch.length = 16)
    {R : ℕ → Prop} (hR : (∀ i < 64, R (isl + i)) ∧ ∀ i < 16, R (im + i)) (fp c : ℕ)
    (hfc : fp + fs "ring_switch_target" ≤ c) :
    ∃ e, ((∀ f, fs f < 2 ^ 16) → e ≤ c + 2 ^ 20) ∧
      CallAtA fs al cert k "ring_switch_target" [ptrAt isl, ptrAt im] [ringTarget s (ch.take 8) (ch.drop 8)]
      R (fun _ => False) (fun _ => True) (fun rd => ReadsAt rd (ptrAt isl) s ∧ ReadsAt rd (ptrAt im) ch)
      PostQuiet (fs "ring_switch_target") fp c e := by
  have hck := rstChecks_ok
  simp only [rstChecks, Bool.and_eq_true, decide_eq_true_eq] at hck
  obtain ⟨⟨⟨⟨⟨hc, hst⟩, haoc⟩, hok⟩, hasz⟩, hadr⟩ := hck
  obtain ⟨c', hc⟩ := Option.isSome_iff_exists.mp hc
  have hlp : coreProgram.loop "ring_switch_target" = false := by
    rw [Program.loop_of_find? find_rst, Fn.loop, rst_body, rstT_split]; simp
  have hchk : chk [ptrAt isl, ptrAt im].length (fn% «ring_switch_target»).body = some c' := by rw [rst_body]; exact hc
  have hst' : storesOf [ptrAt isl, ptrAt im].length (fn% «ring_switch_target»).body = rstStores := by
    rw [rst_body]; exact hst
  set σ : Reader → Val := rstVal c isl im with hσ
  set σ0 := σ fun _ => none with hσ0
  set es := rstPre.flatMap (slEvs σ0) with hes
  have hes' : ∀ τ : Val, rstPre.flatMap (slEvs τ) = es := fun τ =>
    List.flatMap_congr fun st hs' => slEvs_atomOrCall τ σ0 st (List.all_eq_true.mp haoc st hs')
  have hwalk : ∀ τ : Val, walk τ (fn% «ring_switch_target»).body = .ret es [.n rstRet] := fun τ => by
    rw [rst_body, rstT_split, walk_straight τ _ _ (straight_of_atomOrCall _ haoc), hes']
  have hmemB : ∀ a, Stmt.atom a ∈ rstPre → Stmt.atom a ∈ (fn% «ring_switch_target»).body := fun a ha => by
    rw [rst_body, rstT_split]; exact List.mem_append_left _ ha
  -- the values every memory's valuation takes
  have hp : ∀ rd, ∀ i < 2, σ rd (.n i) = [ptrAt isl, ptrAt im].getD i 0 := fun rd i hi =>
    fwd_param hchk (by simpa using hi)
  have hG : ∀ rd a, Stmt.atom a ∈ rstPre →
      Good rd (storesOf [ptrAt isl, ptrAt im].length (fn% «ring_switch_target»).body) (fun _ => ptrAt c) (σ rd) a :=
    fun rd a ha => fwd_good hchk a (hmemB a ha)
  have vch : ∀ rd, σ rd (.n rstChain) = ptrAt c := fun rd => hG rd rstAlloc (by simp [rstPre])
  have v20 : ∀ rd, σ rd (.n (val% «ring_switch_target» "s2#0")) = word 1 0 := fun rd =>
    hG rd (.const (.n (val% «ring_switch_target» "s2#0")) (word 1 0)) (by simp [rstPre])
  have vz : ∀ rd, ∀ p < 8, σ rd (.n ((val% «ring_switch_target» "s1.u0.s0#0") + p)) = word 0 0 := fun rd p hp' =>
    hG rd (.const (.n ((val% «ring_switch_target» "s1.u0.s0#0") + p)) (word 0 0)) (by
      simp only [rstPre, List.mem_append, List.mem_flatten, List.mem_map, List.mem_range]
      exact Or.inl (Or.inl (Or.inl (Or.inr ⟨_, ⟨p, hp', rfl⟩, List.mem_cons_self⟩))))
  have vs0 : ∀ rd, σ rd (.n (val% «ring_switch_target» "sums~0")) = word 27 0 := fun rd =>
    hG rd (.const (.n (val% «ring_switch_target» "sums~0")) (word 27 0)) (by simp [rstPre])
  have vsums : ∀ rd, σ rd (.n rstSums) = ptrAt (c + 64) := fun rd => by
    have h := hG rd (.mul (.n rstSums) (.n rstChain) (.n (val% «ring_switch_target» "sums~0"))) (by simp [rstPre])
    simp [Good] at h
    rw [h, vch, vs0, word_27, ptrAt_mul_gen]
  have hsp := straight_parts σ0 rstPre (straight_of_atomOrCall _ haoc)
  have hal : ∀ τ : Val, allocs τ es = [72] := fun τ => by
    rw [← hes' τ, (straight_parts τ rstPre (straight_of_atomOrCall _ haoc)).2.1, hasz]; rfl
  have hdst : allocDsts es = [.n rstChain] := by rw [hes, hsp.1, hasz]; rfl
  have haddr : addrs es = [] := by rw [hes, hsp.2.2.1, hadr]
  have hcl : calls es = [rstCall] := by rw [hes, calls_atomOrCall σ0 _ haoc, rst_callsOfB]
  -- the own words and the loop
  set G := ch.drop 8 with hGdef
  set Wo : Words := [(c, rsChain s G)] with hWo
  have hWr : ∀ rd, HoldsWords rd Wo → ReadsAt rd (ptrAt c) (rsChain s G) := fun rd h => h _ List.mem_cons_self
  have hown : ∀ i, c ≤ i → i < c + 72 → ownData cert fp c "ring_switch_target" [72] es i := by
    intro i h1 h2
    unfold ownData; left
    exact ⟨(72, c), by simp [bases], h1, h2⟩
  set fl := allocBase (al rlName) (c + 72) with hfl
  set Rl : ℕ → Prop := fun i => (im ≤ i ∧ i < im + 16) ∨ (isl ≤ i ∧ i < isl + 64) ∨ (c ≤ i ∧ i < c + 72) with hRl
  have hloop := rl_placed (fs := fs) (al := al) (cert := cert) (k := k) (im := im) (isl := isl) (ic := c) hs hch
    (R := Rl) ⟨fun i hi => Or.inl ⟨by omega, by omega⟩, fun i hi => Or.inr (Or.inl ⟨by omega, by omega⟩),
      fun i hi => Or.inr (Or.inr ⟨by omega, by omega⟩)⟩ fl (fl + lpB fs rlName 8 0)
  have hla : ∀ rd, rstCall.args.map (σ rd) = rlArgs 0 im isl c := by
    intro rd
    simp only [rstCall, List.map_cons, List.map_nil, v20 rd, vch rd, hp rd 0 (by decide), hp rd 1 (by decide),
      rlArgs, word_one, pow_zero, List.getD_cons_zero, List.getD_cons_succ]
  -- the atoms
  have hok' : ∀ a, Stmt.atom a ∈ rstPre → a = rstAlloc ∨ loadOkB [(1, 16), (rstSums, 8), (rstChain, 8)] a = true :=
    fun a ha => by simpa [rstAtomOk] using List.all_eq_true.mp hok a (mem_atomsOf' ha)
  have hev : ∀ rd, (ReadsAt rd (ptrAt isl) s ∧ ReadsAt rd (ptrAt im) ch) → HoldsWords rd Wo →
      ∀ ev ∈ es, ev.Holds rd (σ rd) := by
    intro rd hP hW ev hev'
    rw [← hes' (σ rd)] at hev'
    rcases mem_slEvs_aoc haoc hev' with ⟨a, rfl, ha⟩ | ⟨f, a1, r1, rfl, -⟩
    · show a.Holds rd (σ rd)
      rcases hok' a ha with rfl | hk
      · trivial
      cases a with
      | load d q off =>
        have hk' : (q = .n 1 ∧ off < 16) ∨ (q = .n rstSums ∧ off < 8) ∨ (q = .n rstChain ∧ off < 8) := by
          simpa [loadOkB, or_assoc] using hk
        by_cases hS : Atom.load d q off ∈ rstStores
        · simp only [rstStores, List.mem_map, List.mem_range, Atom.load.injEq] at hS
          obtain ⟨p, hp8, rfl, rfl, rfl⟩ := hS
          show LoadHolds rd (σ rd (.n rstChain)) p (σ rd (.n ((val% «ring_switch_target» "s1.u0.s0#0") + p)))
          rw [vch, vz rd p hp8, word_zero]
          have := rsChain_load (hWr rd hW) (j := 0) (by omega) hp8
          simpa [rstH] using this
        · refine fwd_holds_load hchk (hmemB _ ha) (by rw [hst']; exact hS) ?_
          show ∃ v, LoadHolds rd (σ rd q) off v
          rcases hk' with ⟨hq, ho⟩ | ⟨hq, ho⟩ | ⟨hq, ho⟩ <;> rw [hq]
          · rw [hp rd 1 (by decide)]; exact ⟨_, hP.2 off (by omega)⟩
          · rw [vsums]; exact ⟨_, readsAt_off (hWr rd hW) (m := 64) (o := off) (by simp [rsChain]; omega)⟩
          · rw [vch]; exact ⟨_, hW _ List.mem_cons_self off (by simp [rsChain]; omega)⟩
      | _ => exact fwd_holds_noSide hchk (hmemB _ ha) (by revert hk; simp [loadOkB])
    · trivial
  have hub : (∀ f, fs f < 2 ^ 16) → fl + lpB fs rlName 8 0 ≤ c + 2 ^ 20 := by
    intro hfs
    have := allocBase_le (al rlName) (c + 72)
    have := hfs rlName
    have := hfs (tailKey rlName)
    unfold lpB
    omega
  refine ⟨fl + lpB fs rlName 8 0, hub, callAtA_nodeRd hlp hfc ⟨σ0, fn% «ring_switch_target», es, [.n rstRet], Wo,
    [PostQuiet], fun rd => HoldsWords rd Wo, fun _ => False, find_rst, ?_, fun _ h => h.elim, ?_,
    fun _ _ => trivial, fun rd hl hP hO => ?_⟩⟩
  · rw [hal]
    exact ⟨fun q hq => by rw [List.mem_singleton] at hq; subst hq; right; simp [rsChain], List.pairwise_singleton _ _⟩
  · rw [hcl, hal]
    simp only [KidsAtF, rstCall, ↓reduceIte, List.headD_cons, List.sum_cons, List.sum_nil, Nat.add_zero]
    have h0 := hla (fun _ => none)
    simp only [rstCall] at h0
    rw [h0]
    refine ⟨lpB fs rlName 8 0, fl + lpB fs rlName 8 0, Rl, fun _ => False, fun _ => True, fun i hi => ?_,
      hloop.mono (fun _ h => h) (fun _ h => h) (fun _ h => h) (fun rd h => ⟨h.1.2, h.1.1, hWr rd h.2⟩)
        (fun _ _ _ h => h), rfl, fun rd h => h.1, fun _ h => h.elim⟩
    rcases hi with h | h | h
    · exact Or.inl (Or.inl (by have := hR.2 (i - im) (by omega); rwa [Nat.add_sub_cancel' h.1] at this))
    · exact Or.inl (Or.inl (by have := hR.1 (i - isl) (by omega); rwa [Nat.add_sub_cancel' h.1] at this))
    · exact Or.inl (Or.inr (hown i h.1 h.2))
  -- on a memory
  simp only [hal]
  have hevr := hev rd hP hO
  obtain ⟨tl, hn, hv, hb, hq⟩ := rl_loop (kd := k) hs hch 7 0 rfl rd hl ⟨hP.2, hP.1, hWr rd hO⟩
  have hkv : Tree.KidsValid coreProgram rd (σ rd) (calls es) [tl] := by
    rw [hcl]
    refine kidsValid_cons_taken rfl hn ?_ kidsValid_nil
    rw [hla rd]; exact hv
  have hpar : (fn% «ring_switch_target»).params.map (σ rd) = [ptrAt isl, ptrAt im] := by
    rw [rst_params]; exact fwd_params hchk
  have hrel := Tree.Valid.rel (P := coreProgram) (rd := rd) (.node "ring_switch_target" (σ rd) [72] [tl])
    ⟨_, find_rst, hpar, es, [.n rstRet], hwalk _, rfl, hevr, hkv⟩
  obtain ⟨s', ch', hs', hch', hrs, hrc, hret⟩ := ring_switch_target_holds rd _ _ hrel
  obtain rfl := readsAt_eq hrs hP.1 (by rw [hs', hs]; rfl)
  obtain rfl := readsAt_eq hrc hP.2 (by rw [hch', hch]; rfl)
  refine ⟨σ rd, hpar, hwalk _, by rw [hret]; rfl, trivial, ⟨by rw [hdst]; simp [vch, bases, ptrAt],
    by rw [haddr]; simp⟩, fun c' hc' => ?_, fun A hA => ?_, fun A hA => ?_, hevr, fun ts hv' hp' => ?_⟩
  · rw [hcl, List.mem_singleton] at hc'
    subst hc'
    exact ⟨(hla _).trans (hla rd).symm, by simp [rstCall]⟩
  · rw [loadAddrs, List.mem_filterMap] at hA
    obtain ⟨ev, hev', hA⟩ := hA
    rw [← hes' (σ rd)] at hev'
    rcases mem_slEvs_aoc haoc hev' with ⟨a, rfl, ha⟩ | ⟨f, a1, r1, rfl, -⟩
    · rcases hok' a ha with rfl | hk
      · simp [Ev.loadAddr?] at hA
      cases a with
      | load d q off =>
        simp only [Ev.loadAddr?, Option.some.injEq] at hA
        subst hA
        have hk' : (q = .n 1 ∧ off < 16) ∨ (q = .n rstSums ∧ off < 8) ∨ (q = .n rstChain ∧ off < 8) := by
          simpa [loadOkB, or_assoc] using hk
        rcases hk' with ⟨hq, ho⟩ | ⟨hq, ho⟩ | ⟨hq, ho⟩ <;> rw [hq]
        · refine ⟨im + off, by rw [hp rd 1 (by decide)]; exact ptrAt_addr im off, Or.inr (Or.inl ?_)⟩
          exact hR.2 off (by omega)
        · exact ⟨c + 64 + off, by rw [vsums]; exact ptrAt_addr _ off, Or.inl (hown _ (by omega) (by omega))⟩
        · exact ⟨c + off, by rw [vch]; exact ptrAt_addr _ off, Or.inl (hown _ (by omega) (by omega))⟩
      | _ => simp [Ev.loadAddr?] at hA
    · simp [Ev.loadAddr?] at hA
  · rw [heapHintAddrs, List.mem_flatMap] at hA
    obtain ⟨ev, hev', hA⟩ := hA
    rw [← hes' (σ rd)] at hev'
    rcases mem_slEvs_aoc haoc hev' with ⟨a, rfl, ha⟩ | ⟨f, a1, r1, rfl, -⟩
    · rcases hok' a ha with rfl | hk
      · simp [Ev.hintAddrs, hintDest?] at hA
      cases a with
      | hint hh => simp [loadOkB] at hk
      | _ => simp [Ev.hintAddrs] at hA
    · simp [Ev.hintAddrs] at hA
  · refine postQuiet_node find_rst (hwalk _) (fun a ha => ?_) (fun ev hev' => ?_) hv' (by rw [hcl] at hp' ⊢; exact hp') _
    · rw [← hes' (σ rd)] at ha
      rcases mem_slEvs_aoc haoc ha with ⟨b, hb, hb'⟩ | ⟨f, a1, r1, hb, -⟩
      · cases hb
        rcases hok' a hb' with rfl | hk
        · rfl
        · exact (quiet_of_loadOk hk).1
      · cases hb
    · rw [← hes' (σ rd)] at hev'
      rcases mem_slEvs_aoc haoc hev' with ⟨a, rfl, ha⟩ | ⟨f, a1, r1, rfl, -⟩
      · rcases hok' a ha with rfl | hk
        · trivial
        · exact exact_of_trivExact (quiet_of_loadOk hk).2
      · trivial

/-- **`ring_switch_target` completes placed** (`RingSwitchTargetCompleteA`): on pointers in `K`, from
`rst_placed`; otherwise no memory holds the slices there. Its end within `2^20` of its cursor when
every frame is below `2^16`. -/
theorem rst_completeAE (k : ℕ) :
    RingSwitchTargetCompleteAE fs al cert k (fun c e => FsSmall fs → e ≤ c + 2 ^ 20) := by
  intro sl mc s ch fp hs hch hpb
  have hs64 : s.length = 64 := hs
  have hch16 : ch.length = 16 := hch
  by_cases hK : IsInK sl ∧ IsInK mc
  · obtain ⟨isl, -, hisl⟩ := hpb (sl, kBits) List.mem_cons_self 0 (by simp [kBits])
    obtain ⟨im, -, him⟩ := hpb (mc, 2 * ringMapWidth) (List.mem_cons_of_mem _ List.mem_cons_self) 0
      (by simp [ringMapWidth])
    have esl : sl = ptrAt isl := by
      rw [eq_ofK_limb hK.1, ptrAt]; congr 1; simpa [addressOfIndex] using hisl
    have emc : mc = ptrAt im := by
      rw [eq_ofK_limb hK.2, ptrAt]; congr 1; simpa [addressOfIndex] using him
    subst esl emc
    obtain ⟨e, hb, h⟩ := rst_placed (fs := fs) (al := al) (cert := cert) (k := k) hs64 hch16
      (R := ptrRegion [(ptrAt isl, kBits), (ptrAt im, 2 * ringMapWidth)])
      ⟨fun i hi => ⟨_, List.mem_cons_self, i, by simp only [kBits]; omega, ptrAt_addr isl i⟩,
        fun i hi => ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, i, by simp only [ringMapWidth]; omega,
          ptrAt_addr im i⟩⟩ fp (fp + fs "ring_switch_target") le_rfl
    exact ⟨e, hb, h⟩
  · refine ⟨fp + fs "ring_switch_target", fun _ => Nat.le_add_right _ _, [], ⟨by simp, List.Pairwise.nil⟩, le_rfl,
      fun _ _ => trivial, fun rd _ _ hP => absurd ⟨(hP.1 0 (by omega)).1, (hP.2 0 (by omega)).1⟩ hK⟩

/-- **`ring_switch_target` completes placed** (`RingSwitchTargetCompleteA`). -/
theorem rst_completeA (k : ℕ) : RingSwitchTargetCompleteA fs al cert k :=
  (rst_completeAE k).toA

/-- **`ring_switch_target` completes placed, its end within `2^20` of its cursor**, every frame below
`2^16`. -/
theorem rst_completeAB (k : ℕ) (hfs : FsSmall fs) : RingSwitchTargetCompleteAB fs al cert k 20 :=
  (rst_completeAE k).mono fun _ _ h _ => h hfs

end
end LeanVM.Guest.B1.VsC
