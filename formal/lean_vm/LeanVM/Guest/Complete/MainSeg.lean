module

public import LeanVM.Guest.B1.VsC.VsW0
public import LeanVM.Guest.B1.Fwd.Eval

/-!
# Windows for `main`'s body

Two kinds `WinSeg` lacks, and the valuation per memory with touches.

* `segA_callIfT`, `segA_callIfN`: a `callIf` whose selector every memory's valuation reads as `σ0`
  does is a window: taken, from its callee's `CallAtA` at the aligned base of the callees' cursor;
  skipped, a phantom of its tail's frame.
* `over T σ0 rd`: `σ0` with each temporary of `T` (a pair `(t, x)`: `t` reads the word at `σ0 x`)
  read from `rd`, every other value `σ0`'s. `main`'s temporaries are its range checks' and its
  touches' (`assert_gpow`). `holdsT_plain`, `holdsT_rc`, `holdsT_touch`, `holdsT_load`,
  `holdsT_store`: an atom holds on every memory's `over`, from its equations on `σ0`.
-/

namespace LeanVM.Guest.Complete

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Memory LeanVM.Guest.B1
open LeanVM.Guest.B1.Fwd LeanVM.Guest.B1.VsC
open LeanVM.Prover.Exec (allocBase)

@[expose] public section

variable {fs : String → ℕ} {al : String → Bool} {cert : String → V → ℕ}

/-! ## `callIf` windows -/

theorem walk_callIf (σ : Val) (c : V) (g : String) (args : List V) :
    walk σ [.callIf c g args] = .fall [.inK c, if σ c = 0 then .skip g args else .call g args []] := by
  simp [walk, walk1, Out.seq, Out.pre]

/-- **A taken `callIf` is a window**: its selector nonzero in `K` as `σ0` reads it, its callee at the
aligned base of the callees' cursor `kc`. -/
theorem segA_callIfT {k : ℕ} {f : String} {fp : ℕ} {σ0 : Val} {σ : Reader → Val} {Own R : ℕ → Prop}
    {Pre : Reader → Prop} {c : V} {g : String} {args : List V} {a kc : ℕ}
    {O : Reader → Prop} {D : ℕ → Prop} {Q : Reader → Tree → Prop} {Bc ec : ℕ} {Rc Dc : ℕ → Prop}
    {Oc : Reader → Prop}
    (hsel : ∀ rd, LowDef k rd → Pre rd → O rd → Oc rd → σ rd c = σ0 c) (h0 : σ0 c ≠ 0) (hK : IsInK (σ0 c))
    (hag : ∀ rd, LowDef k rd → Pre rd → O rd → Oc rd → args.map σ0 = args.map (σ rd))
    (hR : ∀ i, Rc i → (R i ∨ Own i) ∨ D i)
    (hc : CallAtA fs al cert k g (args.map σ0) [] Rc Dc Oc (fun rd => Pre rd ∧ O rd) Q Bc
      (allocBase (al g) kc) (allocBase (al g) kc + Bc) ec) :
    SegA (fs := fs) (al := al) (cert := cert) k f fp σ0 σ Own R Pre [.callIf c g args]
      [.inK c, .call g args []] a a kc ec O (fun rd => O rd ∧ Oc rd) D (fun i => D i ∨ Dc i) [Q] := by
  have hcs : calls [Ev.inK c, Ev.call g args []] = [⟨g, args, [], true⟩] := rfl
  refine ⟨rfl, by rw [hcs]; rfl, fun _ h => h.1, fun _ h => Or.inl h, ?_, fun rd hl hp ho => ?_⟩
  · rw [hcs, KidsAtF]
    simp only [↓reduceIte, List.headD_cons, List.tail_cons]
    refine ⟨Bc, ec, Rc, Dc, Oc, hR, by simpa using hc, ?_⟩
    rw [KidsAtF]
    exact ⟨rfl, fun _ h => h, fun _ h => h⟩
  have hs := hsel rd hl hp ho.1 ho.2
  refine ⟨by rw [walk_callIf, hs]; simp [h0], rfl, rfl,
    by simp [addrs, Ev.addr?], ?_, by simp [loadAddrs, Ev.loadAddr?],
    by simp [heapHintAddrs, Ev.hintAddrs], fun e he => ?_⟩
  · rw [hcs]
    intro cl hcl
    rw [List.mem_singleton] at hcl
    subst hcl
    exact ⟨hag rd hl hp ho.1 ho.2, rfl⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl
    · show IsInK (σ rd c); rw [hs]; exact hK
    · trivial

/-- **A skipped `callIf` is a window**: its selector zero as `σ0` reads it, a phantom of the callee
at its arguments, the callees' cursor past its tail's frame. -/
theorem segA_callIfN {k : ℕ} {f : String} {fp : ℕ} {σ0 : Val} {σ : Reader → Val} {Own R : ℕ → Prop}
    {Pre : Reader → Prop} {c : V} {g : String} {args : List V} {a kc : ℕ}
    {O : Reader → Prop} {D : ℕ → Prop} {Q : Reader → Tree → Prop}
    (hsel : ∀ rd, LowDef k rd → Pre rd → O rd → σ rd c = σ0 c) (h0 : σ0 c = 0)
    (hag : ∀ rd, LowDef k rd → Pre rd → O rd → args.map σ0 = args.map (σ rd))
    (hph : ∃ σ', Phantom coreProgram (.phantom g σ') (args.map σ0)) :
    SegA (fs := fs) (al := al) (cert := cert) k f fp σ0 σ Own R Pre [.callIf c g args]
      [.inK c, .skip g args] a a kc (allocBase (al g) kc + fs (tailKey g)) O O D D [Q] := by
  have hcs : calls [Ev.inK c, Ev.skip g args] = [⟨g, args, [], false⟩] := rfl
  refine ⟨rfl, by rw [hcs]; rfl, fun _ h => h, fun _ h => h, ?_, fun rd hl hp ho => ?_⟩
  · rw [hcs, KidsAtF]
    simp only [Bool.false_eq_true, ↓reduceIte, List.tail_cons]
    refine ⟨hph, ?_⟩
    rw [KidsAtF]
    exact ⟨rfl, fun _ h => h, fun _ h => h⟩
  have hs := hsel rd hl hp ho
  refine ⟨by rw [walk_callIf, hs]; simp [h0], rfl, rfl,
    by simp [addrs, Ev.addr?], ?_, by simp [loadAddrs, Ev.loadAddr?],
    by simp [heapHintAddrs, Ev.hintAddrs], fun e he => ?_⟩
  · rw [hcs]
    intro cl hcl
    rw [List.mem_singleton] at hcl
    subst hcl
    exact ⟨hag rd hl hp ho, rfl⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl
    · show IsInK (σ rd c); rw [hs, h0]; exact (isInK_iff _).mpr ⟨0, by simp⟩
    · trivial

/-! ## The valuation per memory, temporaries read from it -/

/-- **`σ0` on a memory**: each temporary `t` of `T` (paired with the value `x` whose word it reads)
read from `rd`, every other value `σ0`'s. -/
noncomputable def over (T : List (V × V)) (σ0 : Val) (rd : Reader) : Val := fun v =>
  match T.lookup v with
  | some x => rdAt rd (σ0 x) 0
  | none => σ0 v

theorem over_eq {T : List (V × V)} {σ0 : Val} {rd : Reader} {v : V} (h : T.lookup v = none) :
    over T σ0 rd v = σ0 v := by
  simp only [over, h]

theorem over_tmp {T : List (V × V)} {σ0 : Val} {rd : Reader} {t x : V} (h : T.lookup t = some x) :
    over T σ0 rd t = rdAt rd (σ0 x) 0 := by
  simp only [over, h]

/-- `plainB`, naming no temporary of `T`. -/
def plainOkT (T : List (V × V)) (a : Atom) : Bool :=
  plainB a && (atomUses a ++ atomTmps a).all fun v => (T.lookup v).isNone

/-- **A plain atom holds on every memory's valuation** from its equations on `σ0`. -/
theorem holdsT_plain {T : List (V × V)} {rd0 rd : Reader} {S : List Atom} {w : ℕ → E} {σ0 : Val} {a : Atom}
    (hp : plainOkT T a = true) (hg : Good rd0 S w σ0 a) : a.Holds rd (over T σ0 rd) := by
  simp only [plainOkT, Bool.and_eq_true, List.all_eq_true, Option.isNone_iff_eq_none] at hp
  rw [atom_holds_congr a (fun v hv => over_eq (hp.2 v hv))]
  refine holds_of_good (good_plain hp.1 hg) ?_
  have hb := hp.1
  cases a with
  | mul d x y =>
    simp only [plainB, Bool.and_eq_true, decide_eq_true_eq] at hb
    simp only [Side]; rw [ite_pos' hb]; trivial
  | _ => trivial

/-- **A range check holds on every memory's valuation**: its temporaries read there, its operands
`σ0`'s in `K` with their words defined, the divisor nonzero when it divides. -/
theorem holdsT_rc {T : List (V × V)} {rd0 rd : Reader} {S : List Atom} {w : ℕ → E} {σ0 : Val}
    {x y t1 t2 k : V} (h1 : T.lookup t1 = some x) (h2 : T.lookup t2 = some y) (hx : T.lookup x = none)
    (hy : T.lookup y = none) (hk : T.lookup k = none) (hg : Good rd0 S w σ0 (.rangeCheck x y t1 t2 k))
    (hKx : IsInK (σ0 x)) (hKy : IsInK (σ0 y)) (hdx : (rd ((σ0 x).limb 0 * addressOfIndex 0)).isSome)
    (hdy : (rd ((σ0 y).limb 0 * addressOfIndex 0)).isSome) (hx0 : k.idx < y.idx → σ0 x ≠ 0) :
    (Atom.rangeCheck x y t1 t2 k).Holds rd (over T σ0 rd) := by
  have ex := over_eq (σ0 := σ0) (rd := rd) hx
  have ey := over_eq (σ0 := σ0) (rd := rd) hy
  have ek := over_eq (σ0 := σ0) (rd := rd) hk
  refine holds_of_good (S := S) (w := w) ?_ ?_
  · refine ⟨by rw [over_tmp h1, ex], by rw [over_tmp h2, ey], ?_⟩
    have h3 := hg.2.2
    rw [ex, ey, ek]; exact h3
  · refine ⟨by rw [ex]; exact hKx, by rw [ex]; exact hdx, by rw [ey]; exact hKy, by rw [ey]; exact hdy, ?_⟩
    rw [ex]
    split_ifs with hh
    exact hx0 hh

/-- **A touch holds on every memory's valuation**: its temporary read there, its pointer `σ0`'s in
`K` with its word defined. -/
theorem holdsT_touch {T : List (V × V)} {rd : Reader} {σ0 : Val} {t p : V} (ht : T.lookup t = some p)
    (hp : T.lookup p = none) (hK : IsInK (σ0 p)) (hd : (rd ((σ0 p).limb 0 * addressOfIndex 0)).isSome) :
    (Atom.touch t p).Holds rd (over T σ0 rd) := by
  show LoadHolds rd (over T σ0 rd p) 0 (over T σ0 rd t)
  rw [over_eq hp, over_tmp ht]
  exact load_of_rdAt rfl hK hd

/-- **A load holds on every memory's valuation** that reads its word as the evaluation's memory
`rd0` does. -/
theorem holdsT_load {T : List (V × V)} {rd0 rd : Reader} {S : List Atom} {w : ℕ → E} {σ0 : Val} {d p : V}
    {off : ℕ} (hd : T.lookup d = none) (hp : T.lookup p = none) (hS : Atom.load d p off ∉ S)
    (hg : Good rd0 S w σ0 (.load d p off)) (hK : IsInK (σ0 p))
    (hrd : rd ((σ0 p).limb 0 * addressOfIndex off) = rd0 ((σ0 p).limb 0 * addressOfIndex off))
    (hdef : (rd0 ((σ0 p).limb 0 * addressOfIndex off)).isSome) :
    (Atom.load d p off).Holds rd (over T σ0 rd) := by
  show LoadHolds rd (over T σ0 rd p) off (over T σ0 rd d)
  rw [over_eq hd, over_eq hp]
  have hg' : σ0 d = rdAt rd0 (σ0 p) off := (hg : Atom.load d p off ∈ S ∨ _).resolve_left hS
  refine load_of_rdAt ?_ hK (by rw [hrd]; exact hdef)
  rw [hg', rdAt, rdAt, hrd]

/-- **A store holds on every memory's valuation** that holds the stored word. -/
theorem holdsT_store {T : List (V × V)} {rd : Reader} {σ0 : Val} {d p : V} {off : ℕ} (hd : T.lookup d = none)
    (hp : T.lookup p = none) (h : LoadHolds rd (σ0 p) off (σ0 d)) :
    (Atom.load d p off).Holds rd (over T σ0 rd) := by
  show LoadHolds rd (over T σ0 rd p) off (over T σ0 rd d)
  rw [over_eq hd, over_eq hp]; exact h

end
end LeanVM.Guest.Complete
