/-
  LeanVM.Guest.B1.VsC.CalleesA

  `verify_sub`'s callees left to prove, placed, and its completeness from them and its body's
  windows.
-/

module

public import LeanVM.Guest.B1.VsC.LinkCalleesA
public import LeanVM.Guest.B1.VsC.OpenStackedA
public import LeanVM.Guest.Complete.SegA
public import LeanVM.Guest.Complete.MainA

/-!
# `verify_sub`'s placed completeness: the callees and the windows

`VsCalleesCompleteA fs al cert k`: one field per callee `verify_sub` enters with its own placed
completeness statement, each its owner's: the link's (`VsLinkCalleesA`, this part),
the stack's, terminal's, ring's and Keccak's (`Vsc8CalleesA.lean`), the opening's per size
(`OpenStackedCompleteA`). The callees proved layout-free (`hint_stream`, `g_power_of_word`,
`assert_small_g_power`, `table_size`, `table_point`, `chunk_d`, `squeeze_point_from`,
`opening_message`, `state_ends`, `index_side`, `one_plus_suffixes`, `packed_message`) are placed in
the windows, by `callAtA_of_callCompletes0` or their own placed restatement.

`VsWindowsA al k bytecode seed`: on a child the guest accepts, at every placement `VsCompleteHypA`
quantifies, `verify_sub`'s body is a window (`SegA`) before its `ret []`: the honest valuation
`σ0` fixed before the memory, on each memory `σ rd` (its range checks' touched words read), its own
words `Wo`, its callees by `KidsAtF` from the end of its `HeapBuf`s. `vsComplete_of_windowsA` closes
it into `VsCompleteHypA` by `callAtA_segRd`. What is left is `VsWindowsFromCallees al k`: the
windows from the callees, proved window by window with `segA_append`.
-/

namespace LeanVM.Guest.B1.VsC

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Memory LeanVM.Guest.B1
open LeanVM.Guest.Complete LeanVM.Node LeanVM.Protocol LeanVM.Protocol.KeccakHash

@[expose] public section

/-- **`verify_sub`'s callees whose placed completeness is left**, each its placed statement. -/
structure VsCalleesCompleteA (fs : String → ℕ) (al : String → Bool) (cert : String → V → ℕ) (k : ℕ) :
    Prop where
  link : VsLinkCalleesA fs al cert k
  certify_stack : CertifyStackCompleteA fs al cert k
  check_stack_terminal : CheckStackTerminalCompleteA fs al cert k
  ring_switch_target : RingSwitchTargetCompleteA fs al cert k
  verify_keccak : VerifyKeccakCompleteA fs al cert k
  open_stacked : ∀ m, m ≤ 14 → OpenStackedCompleteA fs al cert k m

/-- `verify_sub`'s `Pre`, as `VsCompleteHypA` states it. -/
def vsPreA (seed : Digest) (c : Child) (qt qo : ℕ) (rd : Reader) : Prop :=
  VerifySub.VerifySubPre rd (vsArgs seed c (ptrAt qt) (ptrAt qo)) ∧ ReadsAt rd (ptrAt qo) c.freshClaim.cells

/-- `verify_sub`'s `Post`, as `VsCompleteHypA` states it. -/
def vsPostA (bytecode : List K) (seed : Digest) (c : Child) (rd : Reader) (t : Tree) : Prop :=
  SameStreams (t.pops coreProgram rd) (Prover.childHints bytecode seed c) ∧ t.Every (ExactAt coreProgram rd)

/-- **`verify_sub`'s body as one placed window**: on a child the guest accepts, at every placement
`VsCompleteHypA` quantifies, the statements before its `ret []` are a `SegA` window on an honest
valuation, its callees ending at `e`, its parameters the arguments, its tree's `Post` from its
callees', ending within `2^40` of its cursor below `2^60`. -/
def VsWindowsA (al : String → Bool) (k : ℕ) (bytecode : List K) (seed : Digest) : Prop :=
  ∀ (c : Child) (qt qo fp cur : ℕ), VsChildOk bytecode seed c → qt + expTabLen ≤ fp →
    qo + c.freshClaim.cells.length ≤ fp → fp + B2C.fs "verify_sub" ≤ cur →
    (∃ rd, vsPreA seed c qt qo rd) → cur < 2 ^ 60 →
    ∃ (fn : Fn) (ss : List Stmt) (σ0 : Val) (σ : Reader → Val) (es : List Ev) (Wo : Words)
      (Qs : List (Reader → Tree → Prop)) (Oend : Reader → Prop) (Dend : ℕ → Prop) (e : ℕ),
      (cur < 2 ^ 60 → e ≤ cur + 2 ^ 40) ∧ coreProgram.loop "verify_sub" = false ∧ coreProgram.find? "verify_sub" = some fn ∧
      fn.body = ss ++ [.ret []] ∧
      WordsInA Wo (fp + 2) (fp + B2C.fs "verify_sub") cur (cur + (allocs σ0 es).sum) ∧
      SegA (fs := B2C.fs) (al := al) (cert := B2C.cert) k "verify_sub" fp σ0 σ
        (ownData B2C.cert fp cur "verify_sub" (allocs σ0 es) es) (vsRegion qt qo c.freshClaim.cells.length)
        (vsPreA seed c qt qo) ss es cur (cur + (allocs σ0 es).sum) (cur + (allocs σ0 es).sum) e
        (fun rd => HoldsWords rd Wo) Oend (fun _ => False) Dend Qs ∧
      (∀ rd, LowDef k rd → vsPreA seed c qt qo rd → Oend rd →
        fn.params.map (σ rd) = vsArgs seed c (ptrAt qt) (ptrAt qo)) ∧
      ∀ rd, LowDef k rd → vsPreA seed c qt qo rd → Oend rd → ∀ ts,
        Tree.KidsValid coreProgram rd (σ rd) (calls es) ts → KidsPost rd Qs (calls es) ts →
        vsPostA bytecode seed c rd (.node "verify_sub" (σ rd) (allocs σ0 es) ts)

/-- Indices `2^64 - 1` apart share their address. -/
theorem addressOfIndex_wrapV (c : ℕ) : addressOfIndex (c + (2 ^ 64 - 1)) = addressOfIndex c := by
  show g ^ (c + (2 ^ 64 - 1)) = g ^ c
  rw [pow_add, g_pow_card_sub_one, mul_one]

/-- **Every call is placed at every position**, by own words no memory holds (`Agg/Wrap.lean`'s). -/
theorem callAtA_wrapV {fs : String → ℕ} {al : String → Bool} {cert : String → V → ℕ} {k : ℕ} {f : String}
    {args rets : List E} {R D : ℕ → Prop} {Pre : Reader → Prop} {Post : Reader → Tree → Prop} {B fp c : ℕ} :
    ∃ e, CallAtA fs al cert k f args rets R D (fun _ => True) Pre Post B fp c e := by
  refine ⟨c + (2 ^ 64 - 1) + 1, [(c, [0]), (c + (2 ^ 64 - 1), [1])], ⟨?_, ?_⟩, by omega,
    fun _ _ => trivial, fun rd _ hW _ => ?_⟩
  · intro q hq
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hq
    rcases hq with rfl | rfl <;> right <;> simp
  · exact List.pairwise_pair.mpr (Or.inl (by simp only [List.length_singleton]; omega))
  · exfalso
    have h0 := hW (c, [0]) (by simp) 0 (by simp)
    have h1 := hW (c + (2 ^ 64 - 1), [1]) (by simp) 0 (by simp)
    simp only [LoadHolds, Main.addr_ofK, Nat.add_zero, List.getElem_singleton] at h0 h1
    rw [addressOfIndex_wrapV, h0.2] at h1
    exact zero_ne_one (Option.some.inj h1.2)

/-- **`verify_sub` completes placed from its window.** -/
theorem vsComplete_of_windowsA {al : String → Bool} {k : ℕ} {bytecode : List K} {seed : Digest}
    (h : VsWindowsA al k bytecode seed) : VsCompleteHypA al k bytecode seed := by
  intro c qt qo fp cur hc ht ho hfc
  by_cases hP : ∃ rd, vsPreA seed c qt qo rd
  swap
  · exact ⟨cur, fun _ => by omega, [], ⟨by simp, by simp⟩, le_rfl, fun _ _ => trivial,
      fun rd _ _ hp => absurd ⟨rd, hp⟩ hP⟩
  by_cases hcur : cur < 2 ^ 60
  swap
  · obtain ⟨e, he⟩ := callAtA_wrapV (fs := B2C.fs) (al := al) (cert := B2C.cert) (k := k) (f := "verify_sub")
      (args := vsArgs seed c (ptrAt qt) (ptrAt qo)) (rets := []) (R := vsRegion qt qo c.freshClaim.cells.length)
      (D := fun _ => False) (B := B2C.fs "verify_sub") (fp := fp) (c := cur)
      (Pre := fun rd => VerifySub.VerifySubPre rd (vsArgs seed c (ptrAt qt) (ptrAt qo)) ∧
        ReadsAt rd (ptrAt qo) c.freshClaim.cells)
      (Post := fun rd t => SameStreams (t.pops coreProgram rd) (Prover.childHints bytecode seed c) ∧
        t.Every (ExactAt coreProgram rd))
    exact ⟨e, fun h => absurd h hcur, he⟩
  obtain ⟨fn, ss, σ0, σ, es, Wo, Qs, Oend, Dend, e, he, hlp, hf, hb, hWo, hseg, hpar, hpost⟩ :=
    h c qt qo fp cur hc ht ho hfc hP hcur
  exact ⟨e, he, callAtA_segRd hlp hfc hf hb σ0 σ es Wo Qs Oend Dend hWo (fun _ h => h.elim) hseg
    (fun _ _ => trivial) (fun rd hl hp ho => ⟨hpar rd hl hp ho, rfl⟩) hpost⟩

/-- **What is left of `verify_sub`'s completeness**: its window from its callees' placed
completeness, at every seed, on a memory floor `k ≥ 14` (the stream's range check reads `8193`). -/
def VsWindowsFromCallees (al : String → Bool) (k : ℕ) : Prop :=
  14 ≤ k → VsCalleesCompleteA B2C.fs al B2C.cert k → ∀ seed, VsWindowsA al k guestBytecode seed

/-- **`verify_sub` completes placed from its callees**, given the windows' statement. -/
theorem vsComplete_of_calleesA {al : String → Bool} {k : ℕ} (hw : VsWindowsFromCallees al k)
    (hk : 14 ≤ k) (h : VsCalleesCompleteA B2C.fs al B2C.cert k) :
    ∀ seed, VsCompleteHypA al k guestBytecode seed :=
  fun seed => vsComplete_of_windowsA (hw hk h seed)

end
end LeanVM.Guest.B1.VsC
