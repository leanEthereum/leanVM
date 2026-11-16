/-
  LeanVM.Guest.EndExecRLce

  `log2_ceil_in_the_exponent`'s residuals at its honest frames: its divisor `g_N` and, on the branch
  `g_log ≠ g^fl`, the order residual `0 < e(g_log)`.
-/

module

public import LeanVM.Guest.EndExecRCld
public import LeanVM.Guest.EndExecYWitCells
public import LeanVM.Guest.Memory.Uniform
public import LeanVM.Guest.Res.ResGiven

/-!
# `log2_ceil_in_the_exponent`'s residuals

Its certificates' residuals are `nz 2` at offset `12` and `0 < e([7])` at the branch's offset
(`lce0_res`, `lce16_res`). Cell `7` holds `g_log = [11]·g^fl`, `[11]` an address (`lce_val`). At the
branch's offset the frame's alignment reaches a call of `assert_small_g_power` on `[26]` past atoms
(`callIn`), which the body's walk makes only when `g_log + g^fl ≠ 0` (`thenFree`), so `g_log ≠ g^fl`
and the exponent is past `fl`.
-/

namespace LeanVM.Guest.Res

open LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Memory

@[expose] public section

/-- The branch's call of `assert_small_g_power` on `[26]`. -/
abbrev lceCall : Ev := .call "assert_small_g_power" [.n 26, .n 1] []

/-- A block reaching `lceCall`'s statement past atoms. -/
def callIn : List Stmt → Bool
  | .atom _ :: ss => callIn ss
  | .call f a r :: ss => (f == "assert_small_g_power" && a == [.n 26, .n 1] && r == []) || callIn ss
  | _ => false

/-- Atoms, then a return. -/
def atomsRet : List Stmt → Bool
  | .atom _ :: ss => atomsRet ss
  | [.ret _] => true
  | _ => false

/-- Atoms and calls but `lceCall`'s, then `ite c [] _`, then atoms and a return. -/
def thenFree (c : V) : List Stmt → Bool
  | .ite c' z _ :: rest => c' == c && z.isEmpty && atomsRet rest
  | .atom _ :: ss => thenFree c ss
  | .call f a r :: ss => !(f == "assert_small_g_power" && a == [.n 26, .n 1] && r == []) && thenFree c ss
  | _ => false

/-- `log2_ceil_in_the_exponent__L{fl}`'s atoms the order residual reads: `g_log = [11]·g^fl`, `[11]`
range checked, `[19] = g_log + g^fl`. -/
def lceAtoms (fl : ℕ) : List Atom :=
  [.mul (.n 4) (.n 11) (.n 10), .const (.n 10) (word (2 ^ fl) 0), .rangeCheck (.n 11) (.n 12) (.n 13) (.n 14) (.n 9),
    .const (.n 18) (word (2 ^ fl) 0), .add (.n 19) (.n 4) (.n 18)]

end

public section

theorem callIn_atoms (p : List Stmt) : ∀ as : List Atom, callIn (as.map Stmt.atom ++ p) = callIn p
  | [] => rfl
  | _ :: as => by simp only [List.map_cons, List.cons_append, callIn]; exact callIn_atoms p as

theorem callIn_sound {σ : Val} {ss : List Stmt} :
    ∀ {es vs}, walk σ ss = .ret es vs → callIn ss = true → lceCall ∈ es := by
  induction ss with
  | nil => intro es vs _ hc; simp [callIn] at hc
  | cons s ss ih =>
    intro es vs h hc
    cases s
    case atom a =>
      rw [Bridge.walk_atom_cons] at h
      obtain ⟨es', h', rfl⟩ := Bridge.pre_eq_ret h
      exact List.mem_append_right _ (ih h' hc)
    case call f a r =>
      rw [Bridge.walk_call_cons] at h
      obtain ⟨es', h', rfl⟩ := Bridge.pre_eq_ret h
      simp only [callIn, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq] at hc
      rcases hc with ⟨⟨rfl, rfl⟩, rfl⟩ | hc
      · exact List.mem_append_left _ (List.mem_singleton_self _)
      · exact List.mem_append_right _ (ih h' hc)
    all_goals simp [callIn] at hc

theorem atomsRet_calls {σ : Val} {ss : List Stmt} :
    ∀ {es vs}, walk σ ss = .ret es vs → atomsRet ss = true → lceCall ∉ es := by
  induction ss with
  | nil => intro es vs _ hc; simp [atomsRet] at hc
  | cons s ss ih =>
    intro es vs h hc
    cases s
    case atom a =>
      rw [Bridge.walk_atom_cons] at h
      obtain ⟨es', h', rfl⟩ := Bridge.pre_eq_ret h
      simp only [List.singleton_append, List.mem_cons, reduceCtorEq, false_or]
      exact ih h' hc
    case ret r =>
      rw [Bridge.walk_ret_cons] at h
      obtain ⟨rfl, -⟩ := Out.ret.inj h
      simp
    all_goals simp [atomsRet] at hc

theorem thenFree_calls {σ : Val} {c : V} (h0 : σ c = 0) {ss : List Stmt} :
    ∀ {es vs}, walk σ ss = .ret es vs → thenFree c ss = true → lceCall ∉ es := by
  induction ss with
  | nil => intro es vs _ hc; simp [thenFree] at hc
  | cons s ss ih =>
    intro es vs h hc
    cases s
    case ite c' z n =>
      simp only [thenFree, Bool.and_eq_true, beq_iff_eq, List.isEmpty_iff] at hc
      obtain ⟨⟨rfl, rfl⟩, hr⟩ := hc
      rw [Bridge.walk_ite_cons] at h
      simp only [h0, ↓reduceIte, List.nil_append] at h
      obtain ⟨es', h', rfl⟩ := Bridge.pre_eq_ret h
      simp only [List.singleton_append, List.mem_cons, reduceCtorEq, false_or]
      exact atomsRet_calls h' hr
    case atom a =>
      rw [Bridge.walk_atom_cons] at h
      obtain ⟨es', h', rfl⟩ := Bridge.pre_eq_ret h
      simp only [List.singleton_append, List.mem_cons, reduceCtorEq, false_or]
      exact ih h' hc
    case call f a r =>
      rw [Bridge.walk_call_cons] at h
      obtain ⟨es', h', rfl⟩ := Bridge.pre_eq_ret h
      simp only [thenFree, Bool.and_eq_true, Bool.not_eq_true', Bool.and_eq_false_iff, beq_eq_false_iff_ne]
        at hc
      obtain ⟨hne, hc⟩ := hc
      simp only [List.singleton_append, List.mem_cons, not_or]
      refine ⟨fun he ↦ ?_, ih h' hc⟩
      simp only [Ev.call.injEq] at he
      obtain ⟨rfl, rfl, rfl⟩ := he
      simp at hne
    all_goals simp [thenFree] at hc

end

end LeanVM.Guest.Res

namespace LeanVM.Guest.EndExec

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Mode LeanVM.Guest.Core LeanVM.Guest.Memory
open LeanVM.Guest.B2C (fn_of_idx cellJ fsN entryOf)
open LeanVM.Guest.Bridge (FnAl)
open LeanVM.Guest.Res (lceAtoms topAtoms)
open LeanVM.Protocol.Verifier (gen)
open LeanVM.Prover.Exec

public section

variable {A : String → FnAl} {r : Ref} {K : Mode.Cert} {i : ℕ} {e : Bridge.Ent} {j : ℕ}

/-- **`g_log` at an honest frame**: cell `7` holds `g^(b + fl)`, and `b = 0` when `[19] = 0`. -/
theorem lce_val (t : TopAt A r K i e j) (hr : r.Ok) {fl : ℕ} (hfl : fl < 64)
    (hat : (lceAtoms fl).all (topAtoms (coreOf j).body).contains = true) (hc : cellJ j (.n 4) = 7)
    (hc7 : 7 < fsN j) :
    ∃ b < maxCells, refMem r.img (e.I.fp + 7) = ofK (Parameters.g ^ (b + fl)) ∧ (e.σ (.n 19) ≠ 0 → b ≠ 0) := by
  obtain ⟨vs, hw, hF, hev⟩ := t.events hr
  have hA : ∀ a ∈ lceAtoms fl, a.Holds r.img.read e.σ := fun a ha ↦
    hev _ (topAtoms_on_path hw (List.contains_iff_mem.mp (List.all_eq_true.mp hat a ha)))
  simp only [lceAtoms, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hA
  obtain ⟨m4, c10, ⟨⟨hK, hrd⟩, -, -⟩, c18, a19⟩ := hA
  simp only [Atom.Holds] at m4 c10 c18 a19
  have hκ : r.κ ≤ 28 := logMemorySize_le_28 (e := r.exec) hr.size
  rw [show addressOfIndex 0 = 1 by simp [addressOfIndex], mul_one] at hrd
  obtain ⟨b, hb, he⟩ := read_pow hrd hκ
  have e11 : e.σ (.n 11) = gen ^ b := by rw [Core.eq_ofK_limb hK, he, ofK_gpow]
  have hgfl : word (2 ^ fl) 0 = gen ^ fl := B1.Tables.tb_word_two_pow hfl
  have hfb := t.fb
  have hm := t.cell hr hF (x := .n 4) (namedOf_atom (topAtoms_on_path hw (List.contains_iff_mem.mp
    (List.all_eq_true.mp hat (.mul (.n 4) (.n 11) (.n 10)) (by simp [lceAtoms])))) (by simp [atomUses])) (by rw [hc]; omega) (by rw [hc]; omega)
  rw [hc] at hm
  refine ⟨b, hb, ?_, fun h19 hb0 ↦ h19 ?_⟩
  · rw [hm, m4, e11, c10, hgfl, ← pow_add, ofK_gpow]
  · rw [a19, m4, e11, c10, c18, hgfl, hb0, pow_zero, one_mul]
    exact CharTwo.add_self_eq_zero _


/-- **`log2_ceil_in_the_exponent__L{fl}`'s residuals at its honest frames**, from its checks: its
certificate's residuals are `nz 2` at `12` and `0 < e([7])` at `o`; at `o` its alignment reaches the
branch's call past atoms; the body takes that call only off the branch `[19] = 0`. -/
theorem lce_resCert {name : String} {Kc : Mode.Cert} {jf fl o : ℕ} (hfl : fl < 64)
    (hres : ∀ i < Kc.code.length, ∀ x ∈ (Kc.F.res.get i).getD [],
      (i = 12 ∧ x = .nz 2) ∨ (i = o ∧ x = .lt (.num 0) (.ex (.fr 7) 0)))
    (hidx : B2C.idxOf name = some jf ∧ (fnOf jf).entryPc = Kc.F.entry ∧
      Bridge.entOf Bridge.alignA name = Kc.F.entry)
    (hat : (lceAtoms fl).all (topAtoms (coreOf jf).body).contains = true)
    (hc : cellJ jf (.n 4) = 7 ∧ 7 < fsN jf)
    (hal : (Bridge.alOf Bridge.alignA name o).map Res.callIn = some true)
    (hthen : Res.thenFree (.n 19) (coreOf jf).body = true)
    (hnzB : Res.nzB [(name, .n 0)] jf 2 = true) (hnz : NzVal name (.n 0)) :
    ResCert Bridge.alignA Kc := by
  intro r hr i hi e j t x hx hin
  obtain ⟨hj0, hent0, hentA⟩ := hidx
  obtain ⟨ia, rfl, hia, hna, hfa, hca, -, -, h1a, hlta⟩ := fn_of_idx t.idx
  obtain ⟨ib, hib, hib', hnb, hfb, hcb, -, -, h1b, hltb⟩ := fn_of_idx hj0
  have hjj : ia + 1 = jf := by
    refine fnOf_entry_inj hlta hltb ?_
    have := t.entry
    simp only [entryOf, t.idx] at this
    rw [this, hent0]
  obtain rfl : ia = ib := by omega
  have hname : e.I.t.name = name := by rw [← hna, hnb]
  rcases hres i hi x hx with ⟨-, rfl⟩ | ⟨rfl, rfl⟩
  · rw [hjj] at t
    exact nzPar_top t hr (nzs := [(name, .n 0)]) (by simpa using hnz) hnzB
  · obtain ⟨off, hoff, p, hal', as, -, hpos⟩ := t.at'
    rw [hname, hentA] at hoff
    obtain rfl : off = i := by omega
    rw [hname] at hal'
    have hci : Res.callIn p = true := by rw [hal'] at hal; exact Option.some.inj hal
    obtain ⟨vs', hrest⟩ := t.rest
    rw [hpos] at hrest
    have hmem := Res.callIn_sound hrest (by rw [Res.callIn_atoms]; exact hci)
    rw [hjj] at t
    obtain ⟨vs, hw, -⟩ := t.events hr
    have h19 : e.σ (.n 19) ≠ 0 := fun h0 ↦ Res.thenFree_calls h0 hw hthen (List.mem_append_right _ hmem)
    obtain ⟨b, hb, hm, hb0⟩ := lce_val t hr hfl hat hc.1 hc.2
    have := hb0 h19
    exact ⟨0, b + fl, rfl, ⟨_, b + fl, rfl, hm, by unfold maxCells at hb; omega, rfl⟩, by omega⟩

/-- **`log2_ceil_in_the_exponent__L0_L34`'s residuals at its honest frames.** -/
theorem resLce0_alignA : ResCert Bridge.alignA Fn.«log2_ceil_in_the_exponent__L0_L34».modeCert :=
  lce_resCert (jf := fn_idx% «log2_ceil_in_the_exponent__L0_L34») (fl := 0) (o := 30) (by norm_num)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) nzVal_lce0

/-- **`log2_ceil_in_the_exponent__L16_L34`'s residuals at its honest frames.** -/
theorem resLce16_alignA : ResCert Bridge.alignA Fn.«log2_ceil_in_the_exponent__L16_L34».modeCert :=
  lce_resCert (jf := fn_idx% «log2_ceil_in_the_exponent__L16_L34») (fl := 16) (o := 31) (by norm_num)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) nzVal_lce16

end

end LeanVM.Guest.EndExec
