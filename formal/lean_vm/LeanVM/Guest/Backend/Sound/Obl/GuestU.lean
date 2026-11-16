/-
  LeanVM.Guest.Backend.Sound.Obl.GuestU

  The guest's precondition `World.U`, and a guest function's obligations over the core program.
-/

module

public import LeanVM.Guest.Backend.Sound.Obl.CheckXSound
public import LeanVM.Guest.Backend.Sound.Obl.GuestTab
public import LeanVM.Guest.ExpTables
public import LeanVM.Guest.CoreData
public import LeanVM.Guest.B1.Tables.Basic

/-!
# The guest's precondition

`guestU`: the table's bounds (`guestTab`), relation `0` the exponent table with its window
section, relation `1` the window table, a walk tag the path windows `walk_path` dispatches on and
a `memRel` tag a word read through the argument and bounded (`guestRel`, B1's `ExpTables`,
`ExpWinTab`, `WinTabs`, `WinsAt`), and the `ext` functions' relations (`guestX`).

`OblFn g`: `g`'s obligations under `guestU`, on a memory of `2^κ` words, `minLogMem ≤ κ ≤
maxLogMem`, for every call relation within the core program's whose calls meet their callees'
preconditions and the table's postconditions (`CallsOk`), at every valuation meeting `g`'s own
precondition. `oblFn_of_chkX`: from the analysis with facts and `ext` sites, the facts and the
sites' `ext` preconditions shown under the same hypotheses.
-/

namespace LeanVM.Guest.Backend.Obl

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core

@[expose] public section

/-- **The guest's relations**: tag `0` the exponent table and its window section, tag `1` the
window table, a tag `t` with `2 ≤ t < 2^32` the path windows of walk tag `t` (`WinsAt` of its
depth and cap depth), and `memRel c n` the word at the argument times `g^c`, read, `g^e` with
`e < n`. -/
def guestRel (t : Nat) (rd : Reader) (v : E) : Prop :=
  (t = 0 → B1.ExpTables rd v ∧ B1.ExpWinTab rd v) ∧ (t = 1 → B1.WinTabs rd v) ∧
    (2 ≤ t → t < 2 ^ 32 → B1.WinsAt rd (walkD t) (walkCd t) v) ∧
    (2 ^ 32 ≤ t → ∃ e < (t - 2 ^ 32) % 2 ^ 16,
      LoadHolds rd v ((t - 2 ^ 32) / 2 ^ 16) (ofK (addressOfIndex e)))

theorem memRel_decode {c n : Nat} (hn : n < 2 ^ 16) :
    2 ^ 32 ≤ memRel c n ∧ (memRel c n - 2 ^ 32) % 2 ^ 16 = n ∧ (memRel c n - 2 ^ 32) / 2 ^ 16 = c := by
  unfold memRel
  refine ⟨by omega, by omega, by omega⟩

/-- A word read through `v` at `g^c`, bounded, is relation `memRel c n` of `v`. -/
theorem guestRel_memRel {rd : Reader} {v : E} {c n : Nat} (hn : n < 2 ^ 16)
    (h : ∃ e < n, LoadHolds rd v c (ofK (addressOfIndex e))) : guestRel (memRel c n) rd v := by
  obtain ⟨h0, h1, h2⟩ := memRel_decode (c := c) hn
  refine ⟨fun h' => by omega, fun h' => by omega, fun _ h' => by omega, fun _ => ?_⟩
  rw [h1, h2]
  exact h

/-- The path windows of walk tag `winsTag d cd`, `d, cd < 64`, are its relation. -/
theorem guestRel_winsTag {rd : Reader} {v : E} {d cd : Nat} (hd : d < 64) (hc : cd < 64)
    (h : B1.WinsAt rd d cd v) : guestRel (winsTag d cd) rd v := by
  have hl := walkTag_lt (kind := 0) (odd := 1) (by omega) (by omega) hc hd
  obtain ⟨-, -, hD, hC⟩ := walkTag_decode (kind := 0) (odd := 1) (d := d) (by omega) (by omega) hc
  unfold winsTag at *
  have h2 : 2 ≤ walkTag 0 1 d cd := by unfold walkTag; omega
  refine ⟨fun h' => by omega, fun h' => by omega, fun _ _ => ?_, fun h' => by omega⟩
  rw [hD, hC]
  exact h

/-- **The guest's precondition** (`World.U`). -/
def guestU (rd : Reader) : String → List E → Prop := UOf guestTab guestRel guestX rd

/-- **What a call relation of the guest gives at a call**: the core program's relation, the
callee's precondition, the table's postconditions. -/
def CallsOk (rd : Reader) (C : CallRel) : Prop :=
  ∀ f a r, C f a r → coreProgram.Rel rd f a r ∧ guestU rd f a ∧
    SigPost (guestTab.sig f) (a ++ r) ∧ XPost guestRel rd (guestTab.sig f) (a ++ r)

/-- **A guest function's obligations, over the core program.** -/
def OblFn (g : Fn) : Prop :=
  ∀ (κ : ℕ) (L : MemoryImage κ), minLogMem ≤ κ → κ ≤ maxLogMem → ∀ (C : CallRel) (σ : Val),
    CallsOk L.read C → guestU L.read g.name (g.params.map σ) →
    OblList C (guestU L.read) L.read σ g.body True

/-- A function's own `ext` precondition, from its precondition `guestU`. -/
theorem own_spec {rd : Reader} {f : String} {a : List E} {s : XSpec} (h : guestU rd f a)
    (he : (guestTab.sig f).ext = true) (hs : xSpecOf f = some s) : s.Holds rd a :=
  h.2 he s hs

theorem getD_range_map {σ : Val} {n k : ℕ} (h : k < n) :
    (((List.range n).map V.n).map σ).getD k 0 = σ (.n k) := by
  rw [List.getD_eq_getElem _ _ (by simpa using h)]
  simp

theorem nameKey_inj {s t : String} (h : nameKey s = nameKey t) : s = t := by
  unfold nameKey at h
  have h1 : s.toByteArray.data.toList = t.toByteArray.data.toList :=
    (List.map_injective_iff.mpr fun _ _ hab => UInt8.toNat_inj.mp hab) h
  have h2 : s.toByteArray = t.toByteArray := by
    have := Array.toList_inj.mp h1
    cases hs : s.toByteArray
    cases ht : t.toByteArray
    rw [hs, ht] at this
    simp only at this
    rw [this]
  exact String.toByteArray_inj.mp h2

/-- A statement of a body holds, the statements before a later one holding and returning nowhere. -/
theorem holds_at {C : CallRel} {rd : Reader} {σ : Val} {kret : List E → Prop} {body : List Stmt}
    {k n : ℕ} {s : Stmt} {ss : List Stmt} (hk : k < n) (hnr : Stmt.noRetList (body.take n) = true)
    (hd : body.drop k = s :: ss) (h : Stmt.HoldsList C rd σ (body.take n) True kret) :
    Stmt.HoldsList C rd σ [s] True kret := by
  have e : body.take n = body.take k ++ ([s] ++ ss.take (n - k - 1)) := by
    rw [← List.take_append_drop k (body.take n), List.take_take, Nat.min_eq_left hk.le,
      List.drop_take, hd]
    obtain ⟨m, hm⟩ : ∃ m, n - k = m + 1 := ⟨n - k - 1, by omega⟩
    rw [hm, List.take_succ_cons, show m + 1 - 1 = m by omega]
    rfl
  rw [e] at h hnr
  rw [B1.Tables.tb_noRetList_append, Bool.and_eq_true, B1.Tables.tb_noRetList_append,
    Bool.and_eq_true] at hnr
  rw [holdsList_append, holdsList_noRet _ hnr.1, holdsList_append, holdsList_noRet _ hnr.2.1] at h
  exact h.2.1

/-- An atom of a body's statements returning nowhere holds where they do. -/
theorem atom_of_mem {C : CallRel} {rd : Reader} {σ : Val} {kret : List E → Prop} {pre : List Stmt}
    {a : Atom} (hnr : Stmt.noRetList pre = true) (h : Stmt.HoldsList C rd σ pre True kret)
    (ha : Stmt.atom a ∈ pre) : a.Holds rd σ := by
  obtain ⟨A, B, rfl⟩ := List.append_of_mem ha
  rw [B1.Tables.tb_noRetList_append, Bool.and_eq_true] at hnr
  rw [holdsList_append, holdsList_noRet _ hnr.1] at h
  exact h.2.1

/-- **The powers the table lists are right.** -/
theorem guestTab_pows : PowsOk guestTab := by
  unfold PowsOk
  decide +kernel

theorem maxLogMem_le : maxLogMem ≤ 32 := by decide

/-- **A function the analysis with facts and `ext` sites accepts has its obligations**, its facts
and its sites' `ext` preconditions shown wherever the statements before them hold. -/
theorem oblFn_of_chkX {g : Fn} {facts : List (Nat × Hyp)} {xs : List Nat}
    (h : chkFnX guestTab facts xs g = true)
    (hf : ∀ {κ : ℕ} (L : MemoryImage κ), minLogMem ≤ κ → κ ≤ maxLogMem → ∀ (C : CallRel)
      (σ : Val), CallsOk L.read C → guestU L.read g.name (g.params.map σ) → ∀ p ∈ facts,
      Stmt.HoldsList C L.read σ (g.body.take p.1) True (fun _ => True) →
        p.2.Holds guestRel L.read σ)
    (hx : ∀ {κ : ℕ} (L : MemoryImage κ), minLogMem ≤ κ → κ ≤ maxLogMem → ∀ (C : CallRel)
      (σ : Val), CallsOk L.read C → guestU L.read g.name (g.params.map σ) → ∀ i ∈ xs, ∀ s ss,
      g.body.drop i = s :: ss → Stmt.HoldsList C L.read σ (g.body.take i) True (fun _ => True) →
        XSite guestX guestTab L.read σ s) :
    OblFn g := by
  intro κ L h1 h2 C σ hC hpre
  exact fnX_obl_of_chk guestTab_pows (h2.trans maxLogMem_le)
    (fun f a r hc => (hC f a r hc).2.2) h (hf L h1 h2 C σ hC hpre) (hx L h1 h2 C σ hC hpre) hpre.1

end
end LeanVM.Guest.Backend.Obl
