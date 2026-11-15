/-
  LeanVM.Guest.EndExecRRt

  The roots' tree's reads (`Res.rootsB`), sound at the honest frames.
-/

module

public import LeanVM.Guest.EndExecRRtQ
public import LeanVM.Guest.EndExecRBlk

/-!
# The roots' tree's reads

`rt_rres`: on a frame whose `[N]` is `g^a` and `[G]` is `g^b`, `a + b = 2^k`, a point `e = S·c + d`
of the run, below `2^(k+1)`, is `2m + p`, `p < 2`, `m < 2^k`: offset `2m + p` from `[R]`, `m < a`, or
`2(m - a) + p` past `[R]·[N]^2`, `m - a < b`. `roots_top`: at an honest frame of arm `k`, from its
arguments (`rtQ_all`), which its parameters' cells hold.
-/

namespace LeanVM.Guest.EndExec

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Mode LeanVM.Guest.Core LeanVM.Guest.Memory
open LeanVM.Guest.B2C (cellJ fsN)
open LeanVM.Guest.Bridge (FnAl)
open LeanVM.Guest.Res (rootsB rtRes rtSubs inFr)
open LeanVM.Protocol.Verifier (gen)
open LeanVM.Prover.Exec

public section

section

variable {M : ℕ → E} {fp : ℕ}

/-- **A read of the roots' tree's leaves**: `[N] = g^a`, `[G] = g^b`, `a + b = 2^k`. -/
theorem rt_rres {R N G lo hi S d a b k : ℕ} (hN : M (fp + N) = ofK (Parameters.g ^ a))
    (hG : M (fp + G) = ofK (Parameters.g ^ b)) (hab : a + b = 2 ^ k) (hk : k ≤ 10) (hdS : d < S)
    (hSh : S * hi ≤ 2 ^ (k + 1)) : RRes M fp (rtRes R N G lo hi S d) := by
  have h2k : 2 ^ k ≤ 2 ^ 10 := Nat.pow_le_pow_right (by norm_num) hk
  refine ⟨lo, hi, rfl, rfl, fun vq hvq c _ hc ↦ ?_⟩
  have he : S * c + d < 2 * 2 ^ k := by
    have h1 : S * c + d < S * (c + 1) := by rw [Nat.mul_succ]; omega
    have h2 : S * (c + 1) ≤ S * hi := Nat.mul_le_mul_left _ hc
    rw [pow_succ] at hSh
    omega
  obtain ⟨m, p, hp2, hsplit⟩ : ∃ m p, p < 2 ∧ S * c + d = 2 * m + p :=
    ⟨_, _, Nat.mod_lt _ (by norm_num), (Nat.div_add_mod _ _).symm⟩
  obtain ⟨wq, ⟨u, w, hu, hw, rfl⟩, rfl⟩ := hvq
  change w = 1 at hw
  change M (fp + R) = u at hu
  subst hw hu
  by_cases hma : m < a
  · refine ⟨⟨⟨0, 0, [(.fr R, 1)]⟩, .num 0, .ex (.fr N) 0, 2, p⟩, ?_,
      fun vb ylo yhi hvb hlo hhi ↦ ⟨m, ?_, ?_, ?_⟩⟩
    · interval_cases p <;> simp [rtSubs]
    · change ylo = 0 at hlo; omega
    · rw [ridx_ex_fr hN (by omega) yhi hhi]; exact hma
    · obtain ⟨wb, ⟨u', w', hu', hw', rfl⟩, rfl⟩ := hvb
      change w' = 1 at hw'
      change M (fp + R) = u' at hu'
      subst hw' hu'
      rw [hsplit]
  · refine ⟨⟨⟨0, 0, [(.fr R, 1), (.fr N, 2)]⟩, .num 0, .ex (.fr G) 0, 2, p⟩, ?_,
      fun vb ylo yhi hvb hlo hhi ↦ ⟨m - a, ?_, ?_, ?_⟩⟩
    · interval_cases p <;> simp [rtSubs]
    · change ylo = 0 at hlo; omega
    · rw [ridx_ex_fr hG (by omega) yhi hhi]; omega
    · obtain ⟨wb, ⟨u', w', hu', ⟨u2, w2, hu2, hw2, rfl⟩, rfl⟩, rfl⟩ := hvb
      change w2 = 1 at hw2
      change M (fp + R) = u' at hu'
      change M (fp + N) = u2 at hu2
      subst hw2 hu'
      rw [← hu2, hN, hsplit, show 2 * m + p = a * 2 + (2 * (m - a) + p) by omega]
      simp only [ofK_gpow]
      ring

end

variable {A : String → FnAl} {r : Ref} {K : Mode.Cert} {i : ℕ} {e : Bridge.Ent} {j : ℕ}

/-- **A read of the roots' tree's leaves at an honest frame.** -/
theorem roots_top (t : TopAt A r K i e j) (hr : r.Ok) {x : Mode.Res} (hx : rootsB j x = true) :
    RRes (refMem r.img) e.I.fp x := by
  match x, hx with
  | .sub a bs, hx =>
    simp only [rootsB] at hx
    split at hx
    · rename_i lo hi _ _
      simp only [inFr, Bool.and_eq_true, decide_eq_true_eq, List.any_eq_true, List.mem_range,
        beq_iff_eq] at hx
      obtain ⟨⟨⟨⟨⟨h21, hl1⟩, h22, hl2⟩, hdS⟩, k, hk, hname, hSh⟩, hxe⟩ := hx
      obtain ⟨f, bufs, kids, hJ, hf, hfn⟩ := t.found
      rw [hfn] at hname
      subst hname
      have hQ := rtQ_all hr e.I t.inst _ e.σ bufs kids hJ k hk rfl _ hf
      obtain ⟨hf', hok⟩ := B1.Da.rt_find hk
      have hcj := Option.some.inj (hf.symm.trans hf')
      simp only [B1.Da.rtOk, Bool.and_eq_true, decide_eq_true_eq] at hok
      have hps : (coreOf j).params = [.n 0, .n 1, .n 2] := by rw [hcj]; exact hok.1
      rw [hps] at hQ
      simp only [List.map_cons, List.map_nil, RtH] at hQ
      obtain ⟨a0, b0, hab, h1, h2⟩ := hQ
      obtain ⟨vs, -, hF, -⟩ := t.events hr
      have c1 := t.cell hr hF (x := .n 1) (List.mem_append_left _ (List.mem_append_left _ (by rw [hps]; simp)))
        h21 hl1
      have c2 := t.cell hr hF (x := .n 2) (List.mem_append_left _ (List.mem_append_left _ (by rw [hps]; simp)))
        h22 hl2
      rw [h1, Value.gen_pow_eq_ofK] at c1
      rw [h2, Value.gen_pow_eq_ofK] at c2
      rw [hxe]
      exact rt_rres c1 c2 hab (by omega) hdS hSh
    · cases hx
  | .lt _ _, hx => simp [rootsB] at hx
  | .nz _, hx => simp [rootsB] at hx
  | .name _, hx => simp [rootsB] at hx

end

end LeanVM.Guest.EndExec
