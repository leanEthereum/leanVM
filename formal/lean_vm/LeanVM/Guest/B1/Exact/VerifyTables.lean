/-
  LeanVM.Guest.B1.Exact.VerifyTables

  `verify_tables` on an honest child by a tree exact at every node, given its own computed hints exact at its honest
  valuation (`VtOwnExact`): its callees are exact on every valid tree.
-/

module

public import LeanVM.Guest.B1.VerifySub.CompleteBP
public import LeanVM.Guest.B1.Exact.Padding
public import LeanVM.Guest.B1.Exact.SharedTables
public import LeanVM.Guest.B1.Exact.GPower
public import LeanVM.Guest.B1.Exact.VtOwn

/-!
# `verify_tables`, every node exact

Every callee of `verify_tables` is in `ExactOk`: its 31 `padding_weight`s (`pw_exactOk`), `shared_selector_tables`
(`sst_exactOk`), the others exact for free (`vt_callees_ok`). So a valid `verify_tables` node is exact at every node
once its own events are (`everyKids_of_callees_ok`). `VtOwnExact`: its own computed hints (96 digit runs, three bit runs,
the limbs and the inverses) exact at its honest valuation (`vtQn`) on a memory holding its caller's buffers, proved as
`vtOwnExact` (`Tables.vt_own_exact`). `CompleteAtDTBR.monoVM`: `monoV` given the memory's low words and input
buffers. `ChildSegs.vt_kidBWPE`: `vt_kidBWP` by a tree also exact, given it.
-/

namespace LeanVM.Guest.B1.VerifySub

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Node LeanVM.Guest.Memory

@[expose] public section

variable {fs : String → ℕ} {cert : String → V → ℕ}

/-- **The callees of a valid node whose function's callees are in `ExactOk` are exact.** -/
theorem everyKids_of_callees_ok {rd : Reader} {f : String} {fn : Fn} (hf : coreProgram.find? f = some fn)
    (hc : ∀ g ∈ Stmt.blockCallees fn.body, ExactOk g) {σ : Val} {bufs : List ℕ} {ks : List Tree}
    {args rets : List E} (hv : (Memory.Tree.node f σ bufs ks).Valid coreProgram rd args rets) :
    Tree.EveryKids (ExactAt coreProgram rd) ks := by
  obtain ⟨fn', hf', -, es, vs, hw, -, -, hkv⟩ := hv
  rw [hf] at hf'
  cases hf'
  exact everyKids_of_everyIn (coreProgram_exactOkIn rd) ks σ (calls es) hkv fun c hc' =>
    hc c.f (walk_callees (σ := σ) fn.body (by rw [hw]; exact hc'))

/-- `verify_tables`' callees: its `padding_weight`s, `shared_selector_tables`, or exact for free. -/
noncomputable def vtCalleeOk (g : String) : Bool :=
  exactCallee idx% «verify_tables» g || g == "shared_selector_tables" ||
    (List.range 31).any fun τ => g == Tables.lName "padding_weight" τ

theorem vt_callees_check : (Stmt.blockCallees (fn% «verify_tables»).body).all vtCalleeOk = true := by
  decide +kernel

/-- **Every callee of `verify_tables` is in `ExactOk`.** -/
theorem vt_callees_ok : ∀ g ∈ Stmt.blockCallees (fn% «verify_tables»).body, ExactOk g := by
  intro g hg
  have h := List.all_eq_true.mp vt_callees_check g hg
  simp only [vtCalleeOk, Bool.or_eq_true, beq_iff_eq, List.any_eq_true, List.mem_range] at h
  rcases h with (h | rfl) | ⟨τ, hτ, rfl⟩
  · exact .free (exactFreeG_of_callee h)
  · exact sst_exactOk
  · exact Tables.pw_exactOk hτ

/-- **`verify_tables`' own computed hints are exact at its honest valuation**, on every valid node of it on a memory
holding its caller's buffers. -/
def VtOwnExact : Prop :=
  ∀ (H : Tables.VtHonest) (B : Tables.VtBases) (rd : Reader) (σ : Val) (bufs : List ℕ) (ks : List Tree)
    (args rets : List E), H.Ok → Tables.VtShape H → Tables.vtQn H B rd σ → LowDef 14 rd → Main.MemL rd (H.linL B) →
    (Memory.Tree.node "verify_tables" σ bufs ks).Valid coreProgram rd args rets → ExactAt coreProgram rd "verify_tables" σ

theorem vtOwnExact : VtOwnExact := fun _ B _ _ _ _ _ _ _ hs hq hlow hlin hv => Tables.vt_own_exact hs B hq hlow hlin hv

/-- `CompleteAtDTBR.monoV` given also the memory's low words and its input buffers. -/
theorem CompleteAtDTBR.monoVM {k : ℕ} {f : String} {Lin : Main.Layout} {args : List E}
    {Out : List E → Main.Layout → Prop}
    {T T' : Reader → Tree → Prop} {B B' : ℕ} (h : CompleteAtDTBR fs cert k f Lin args Out T B) (hB : B ≤ B')
    (hT : ∀ rd t rets, LowDef k rd → Main.MemL rd Lin → t.Valid coreProgram rd args rets → T rd t → T' rd t) :
    CompleteAtDTBR fs cert k f Lin args Out T' B' := fun fp =>
  let ⟨n, Lown, rets, Lout, hn, ho, hw, hd, hr⟩ := h fp
  ⟨n, Lown, rets, Lout, hn.trans hB, ho, hw, hd, fun rd hl hm =>
    let ⟨t, ht, hT'⟩ := hr rd hl hm
    ⟨t, ht, hT rd t rets hl (Main.memL_append.mp hm).2 ht.2.1 hT'⟩⟩

namespace ChildSegs

variable {bytecode : List K} {seed : Digest} {c : Child} (S : ChildSegs bytecode seed c)

/-- **`verify_tables` on the honest child, within `vtMax` by a tree within its weights popping its group order and
its round count, exact at every node**, given its own computed hints exact. -/
theorem vt_kidBWPE (hbl : bytecode.length = 2 ^ 23) {κ : ℕ} (hκ : 14 ≤ κ) (W : VsWordsOs fs) (hV : VtOwnExact)
    (B : Tables.VtBases) :
    CompleteAtDTBR fs cert κ "verify_tables" (S.H.linL B) (S.H.args B) (Returns (S.H.retsH B))
      (fun rd t ↦ ((∀ op, Budget.WeighsLe coreProgram (W.ωv op) (vtWB W.toVsWords op) t) ∧
        vsPvt S.logMem S.rowsN S.H.n rd t) ∧ t.Every (ExactAt coreProgram rd)) (vtMax fs W.Kf W.Ksh W.K10) :=
  CompleteAtDTBR.monoVM (Tables.verify_tables_completeAtTBWR' hκ (S.H_run hbl).1 (S.H_shape hbl) B W.Kf W.Ksh W.K10
    W.hKf W.hsh W.h10 W.ωv W.Kvw W.Wss W.Kw10 W.hKvw W.hssw W.h10w) (S.vt_bound_le hbl W)
    fun rd t _ hlow hlin hv ⟨hw, σ, ks, e, hq⟩ ↦ by
      subst e
      exact ⟨⟨hw, vt_honest_vsPvt rfl rfl rfl hq hv⟩, Tree.every_node.mpr
        ⟨hV _ _ _ _ _ _ _ _ (S.H_run hbl).1 (S.H_shape hbl) hq (hlow.mono hκ) hlin hv,
          everyKids_of_callees_ok find_vt vt_callees_ok hv⟩⟩

end ChildSegs

end
end LeanVM.Guest.B1.VerifySub
