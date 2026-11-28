/-
  LeanVM.Guest.B1.VsC.VsRun

  A run of `verify_sub`'s atoms: its plain atoms hold on every memory from their equations, its
  loads and stores through buffers both memories read alike.
-/

module

public import LeanVM.Guest.B1.VsC.VsW0
public import LeanVM.Guest.Complete.MainA

/-!
# Runs of atoms

`holds_run`: on `rdOver σ0 rd`, every atom of a run holds once its non-plain atoms (`plainOk`
false: loads, stores, range checks, assertions, divisions) do, the plain ones from their equations
on `σ0` (`holds_plain`). `holds_loadAt`: a load into a new value through a pointer `ptrAt b` holds
when both the evaluation's memory `rd0` and `rd` read the same words from `b`. `holds_storeAt`: a
store of the word `xs[off]` holds on a memory reading `xs` from `b`. `vsA_run_good`: each atom of a
run of `vsA` (no branch `assertNe`) satisfies its equations on the forward valuation.
-/

namespace LeanVM.Guest.B1.VsC

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Memory LeanVM.Guest.B1
open LeanVM.Guest.Complete LeanVM.Guest.B1.Fwd LeanVM.Protocol.Verifier

@[expose] public section

/-- **A run's atoms hold** once its non-plain ones do. -/
theorem holds_run {rd0 rd : Reader} {S : List Atom} {w : ℕ → E} {σ0 : Val} {as : List Atom}
    (hg : ∀ a ∈ as, Good rd0 S w σ0 a)
    (hx : ∀ a ∈ as.filter (fun a => !plainOk a), a.Holds rd (rdOver σ0 rd)) :
    ∀ a ∈ as, a.Holds rd (rdOver σ0 rd) := by
  intro a ha
  by_cases hp : plainOk a = true
  · exact holds_plain hp (hg a ha)
  · exact hx a (List.mem_filter.mpr ⟨ha, by simpa using hp⟩)

theorem readsAt_word {rd : Reader} {b : ℕ} {xs : List E} (h : ReadsAt rd (ptrAt b) xs) {off : ℕ}
    (hoff : off < xs.length) : rd ((ptrAt b).limb 0 * addressOfIndex off) = some xs[off] := (h off hoff).2

/-- **A load through a buffer both memories read alike holds.** -/
theorem holds_loadAt {rd0 rd : Reader} {S : List Atom} {w : ℕ → E} {σ0 : Val} {d p : V} {off b : ℕ}
    {xs : List E} (hd : vsRcs.lookup d = none) (hp : vsRcs.lookup p = none) (hS : Atom.load d p off ∉ S)
    (hg : Good rd0 S w σ0 (.load d p off)) (hpb : σ0 p = ptrAt b) (hoff : off < xs.length)
    (h0 : ReadsAt rd0 (ptrAt b) xs) (h1 : ReadsAt rd (ptrAt b) xs) :
    (Atom.load d p off).Holds rd (rdOver σ0 rd) := by
  refine holds_load hd hp hS hg (by rw [hpb]; exact Value.ofK_isInK _) ?_ ?_
  · rw [hpb, readsAt_word h1 hoff, readsAt_word h0 hoff]
  · rw [hpb, readsAt_word h0 hoff]; rfl

/-- The word a load through a buffer `rd0` reads. -/
theorem good_loadAt {rd0 : Reader} {S : List Atom} {w : ℕ → E} {σ0 : Val} {d p : V} {off b : ℕ}
    {xs : List E} (hS : Atom.load d p off ∉ S) (hg : Good rd0 S w σ0 (.load d p off)) (hpb : σ0 p = ptrAt b)
    (hoff : off < xs.length) (h0 : ReadsAt rd0 (ptrAt b) xs) : σ0 d = xs[off] := by
  have hg' : σ0 d = rdAt rd0 (σ0 p) off := (hg : Atom.load d p off ∈ S ∨ _).resolve_left hS
  rw [hg', rdAt, hpb, readsAt_word h0 hoff]; rfl

/-- **A store of a buffer's word holds** on a memory reading the buffer. -/
theorem holds_storeAt {rd : Reader} {σ0 : Val} {d p : V} {off b : ℕ} {xs : List E}
    (hd : vsRcs.lookup d = none) (hp : vsRcs.lookup p = none) (hpb : σ0 p = ptrAt b) (hoff : off < xs.length)
    (hv : σ0 d = xs[off]) (h1 : ReadsAt rd (ptrAt b) xs) :
    (Atom.load d p off).Holds rd (rdOver σ0 rd) := by
  refine holds_store hd hp ?_
  rw [hpb, hv]; exact h1 off hoff

/-- **Each atom of a run of `vsA` satisfies its equations** on the forward valuation. -/
theorem vsA_run_good {rd0 : Reader} {w : ℕ → E} {args : List E} (ha : args.length = 6) {i n : ℕ}
    {as : List Atom} (h : (vsA.drop i).take n = as.map Stmt.atom) (hne : as.all neB = true) :
    ∀ a ∈ as, Good rd0 (storesOf 6 vsAf) w (vsVal rd0 w args) a := by
  intro a ha'
  have hm : Stmt.atom a ∈ vsA :=
    List.mem_of_mem_drop (List.mem_of_mem_take (by rw [h]; exact List.mem_map_of_mem ha'))
  exact vsA_good ha hm (List.all_eq_true.mp hne a ha')

end
end LeanVM.Guest.B1.VsC
