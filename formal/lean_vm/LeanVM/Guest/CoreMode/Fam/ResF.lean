/-
  LeanVM.Guest.CoreMode.Fam.ResF

  The `sub` families read off a function's own code, sound at the honest frames: a run over a product
  scaled by a factor and a read the exponent tables' side section guards.
-/

module

public import LeanVM.Guest.CoreMode.Fam.ResS
public import LeanVM.Guest.CoreMode.Fam.FamDefs
public import LeanVM.Guest.B1.Placement.Common
public import LeanVM.Guest.EndExecYPtr
public import LeanVM.Guest.CoreMode.Fam.ResA
public import LeanVM.Guest.EndExecW
public import LeanVM.Guest.B1.Tables.Basic

/-!
# The families' shared checks, sound

`topAtoms_on_path`, `topSels_sound`: a top-level atom or selector before any statement that may
return is on every returning path; so are a witness's (`TopAt.wit`, `witOk`). `powOf_sound`:
`powOf w = some e` makes `w = g^e` (`Data.powTree`, checked once). `rcBound_sound`: on a memory of at
most `2^32` words, a range check against `g^(N - 1)` makes its value `g^e`, `e < N`
(`B1.Tables.tb_rc_sound'`).
-/

namespace LeanVM.Guest.EndExec

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Mode LeanVM.Guest.Core LeanVM.Guest.Memory
open LeanVM.Guest.B2C (idxOf entryOf FrameHolds fsN fn_of_idx cellJ namedOf)
open LeanVM.Guest.Bridge (FnAl)
open LeanVM.Guest.Res (Wit witOk topAtoms topSels selOf powOf constOf rcBound cellLt holdsBase mulBy inFr eqCells shiftHi shiftB frEx subFamB sideShape sideB sideRead sideIn tabVals numOf frExT mulConst)
open LeanVM.Protocol.Verifier (gen)
open LeanVM.Prover.Exec

public section

/-! ## The atoms on every path -/

theorem topAtoms_on_path {σ : Core.Val} : ∀ {ss : List Stmt} {es : List Ev} {vs : List V},
    walk σ ss = .ret es vs → ∀ {a : Atom}, a ∈ topAtoms ss → Ev.atom a ∈ es
  | [], _, _, _, _, h => by simp [topAtoms] at h
  | s :: ss, es, vs, hw, a, ha => by
    have hrest : Memory.Stmt.noRet s = true → a ∈ topAtoms ss → Ev.atom a ∈ es := fun hn h ↦ by
      obtain ⟨es1, es2, -, h2, rfl⟩ := Res.walk_cons_noRet hn hw
      exact List.mem_append_right _ (topAtoms_on_path h2 h)
    cases s with
    | atom b =>
      simp only [topAtoms, List.mem_cons] at ha
      obtain ⟨es1, es2, h1, h2, rfl⟩ := Res.walk_cons_noRet (s := .atom b) rfl hw
      simp only [walk1, Out.fall.injEq] at h1
      subst h1
      rcases ha with rfl | ha
      · exact List.mem_cons_self
      · exact List.mem_append_right _ (topAtoms_on_path h2 ha)
    | _ =>
      simp only [topAtoms] at ha
      split_ifs at ha with hn
      · exact hrest (by rw [← Memory.noRetR_eq]; exact hn) ha
      · simp at ha

/-- **A top-level selector on a returning path** picks an arm: `g^e`, `e` below the arms. -/
theorem topSels_sound {σ : Core.Val} : ∀ {ss : List Stmt} {es : List Ev} {vs : List V},
    walk σ ss = .ret es vs → ∀ {x : V} {n : ℕ}, (x, n) ∈ topSels ss → ∃ e < n, σ x = ofK (addressOfIndex e)
  | [], _, _, _, _, _, h => by simp [topSels] at h
  | s :: ss, es, vs, hw, x, n, h => by
    simp only [topSels, List.mem_append] at h
    rcases h with h | h
    · split at h
      · rename_i p hs
        simp only [List.mem_singleton] at h
        subst h
        exact Res.selOf_walk hs (Res.walk1_ne_stuck hw)
      · simp at h
    · split_ifs at h with hn
      · obtain ⟨es1, es2, -, h2, rfl⟩ := Res.walk_cons_noRet (by rw [← Memory.noRetR_eq]; exact hn) hw
        exact topSels_sound h2 h
      · simp at h

/-! ## Constants -/

theorem powOf_sound {w : E} {e : ℕ} (h : powOf w = some e) : w = ofK (addressOfIndex e) := by
  unfold powOf at h
  split_ifs at h with h1
  have hk := Exec.PowTree.find_ok (Exec.PowTree.ok_of_okW Checked.powTree_ok) h
  rw [show K.ofBits (w.limb 0).toBitVec.toNat = w.limb 0 by
    simp [K.ofBits, BF64.ofBitVec, BitVec.ofNat_toNat]] at hk
  rw [eq_ofK_limb h1, hk]

theorem constOf_sound {as : List Atom} {k : V} {w : E} (h : constOf as k = some w) : Atom.const k w ∈ as := by
  unfold constOf at h
  obtain ⟨a, ha, hf⟩ := List.exists_of_findSome?_eq_some h
  cases a with
  | const d w' =>
    simp only at hf
    split_ifs at hf with hd
    obtain rfl := Option.some.inj hf
    rw [← hd]; exact ha
  | _ => simp at hf

/-- **A range check's bound**: its value `g^e`, `e < N`. -/
theorem rcBound_sound {μ : ℕ} (hμ : μ ≤ 32) (Lm : MemoryImage μ) {σ : Core.Val} {as : List Atom}
    (hh : ∀ a ∈ as, a.Holds Lm.read σ) {v : V} {N : ℕ} (h : rcBound as v = some N) :
    ∃ e < N, σ v = gen ^ e := by
  unfold rcBound at h
  obtain ⟨a, ha, hf⟩ := List.exists_of_findSome?_eq_some h
  cases a with
  | rangeCheck x y t1 t2 k =>
    simp only at hf
    split_ifs at hf with hx
    subst hx
    cases hc : (constOf as k).bind powOf with
    | none => rw [hc] at hf; simp at hf
    | some e =>
      rw [hc] at hf
      simp only at hf
      split_ifs at hf with he
      obtain rfl := Option.some.inj hf
      obtain ⟨w, hw, hpw⟩ := Option.bind_eq_some_iff.mp hc
      have hk : σ k = w := hh _ (constOf_sound hw)
      obtain ⟨h1, h2, h3⟩ := hh _ ha
      exact B1.Tables.tb_rc_sound' hμ Lm (by omega) he
        (by rw [hk, powOf_sound hpw, Nat.add_sub_cancel]) h1 h2 h3
  | _ => simp at hf

/-! ## Cells -/

section

variable {A : String → FnAl} {r : Ref} {K : Mode.Cert} {i : ℕ} {e : Bridge.Ent} {j : ℕ} {w : Wit}

end

/-! ## Products -/

section

variable {M : ℕ → E} {fp : ℕ}

end

section

variable {A : String → FnAl} {r : Ref} {K : Mode.Cert} {i : ℕ} {e : Bridge.Ent} {j : ℕ} {w : Wit}

end

/-! ## A read guarded by the side section -/

section

variable {A : String → FnAl} {r : Ref} {K : Mode.Cert} {i : ℕ} {e : Bridge.Ent} {j : ℕ} {w : Wit}

end

/-! ## A run inside the run up to a factor times a constant -/

section

variable {A : String → FnAl} {r : Ref} {K : Mode.Cert} {i : ℕ} {e : Bridge.Ent} {j : ℕ} {w : Wit}

end

end

end LeanVM.Guest.EndExec
