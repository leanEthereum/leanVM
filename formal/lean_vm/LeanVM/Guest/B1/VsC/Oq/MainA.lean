/-
  LeanVM.Guest.B1.VsC.Oq.MainA

  `opening_queries__L…` completes placed (`OqA`): its node by `callAtA_node` on its honest
  valuation, its loop by `oqL_complete`.
-/

module

public import LeanVM.Guest.B1.VsC.Oq.LoopA
public import LeanVM.Guest.Exact.Free

/-!
# `opening_queries`, placed

`opening_queries__L…` of shape `s` on `[cap, flags, λ⁻¹, coefs, hs, positions, qptrs, g^N, g^odd]`
allocates its chain (`N + 1` words at its cursor `c`, its own words: the chain `o.chainW`, only
its first word at the final level, where nothing else is written), at level 0 runs its odd first
query when `odd = 1`, runs its loop from `g^0` when `N ≠ 0` (`oqL_complete`), and returns the
chain's end (`0` at the final level).

* `oqMain_vals`: the function's values at `oqMainF`, memory-free.
* `OqA fs al cert kd name s`: the placed completeness of `name`, on every call's honest data
  (`OqCall`) with its static facts, its region, at every frame and cursor past its block; it pops
  its queries' entries (`oqQE`) in order, every node exact.
* `oqA_complete'`: one specialization, from its functions and `ExactFreeG name`.
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Memory
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

/-- **The function's values at `oqMainF`**, memory-free: its parameters, its chain's size and
pointer, its tail, at level 0 the branch's word, the loop's moved positions and windows, and the
odd query's values. -/
theorem oqMain_vals {s : Oq} (hs : s.RowShape) {odd cd : ℕ}
    {cap flags lamInv coefs hsp positions qptrs nG ch bp : E}
    {rounds : List FoldRound} {hsv : List E} {w : QW} (rest : List E) {σ : Val}
    (hσ : ∀ i, σ (.n i) = oqMainF s [cap, flags, lamInv, coefs, hsp, positions, qptrs, nG, gen ^ odd]
      ch (oqQD s cd 17 true 0 bp cap flags rounds hsv w) rest i) :
    oqMainParams.map σ = [cap, flags, lamInv, coefs, hsp, positions, qptrs, nG, gen ^ odd] ∧
      σ (.n 10) = nG * gen ∧ σ (.n 11) = ch ∧
      (∀ o, σ (.n (oqMK s + o)) = (oqMainTl nG rest).getD o 0) ∧
      (s.base = 1 → σ (.n 13) = gen ^ odd + 1 ∧ σ (.n (oqMK s - 2)) = positions * gen ^ odd ∧
        σ (.n (oqMK s - 1)) = qptrs * gen ^ odd ∧ σ (.n 16) = bp ∧
        (oqQD s cd 17 true 0 bp cap flags rounds hsv w).Hv σ) := by
  set tl := oqMainTl nG rest with htl
  set args : List E := [cap, flags, lamInv, coefs, hsp, positions, qptrs, nG, gen ^ odd] with hargs
  set D := oqQD s cd 17 true 0 bp cap flags rounds hsv w with hD
  have eP : ∀ i < 9, σ (.n i) = args.getD i 0 := fun i hi => by
    rw [hσ]; simp only [oqMainF, hi, ↓reduceIte]
  have e10 : σ (.n 10) = nG * word 2 0 := by rw [hσ]; simp [oqMainF, hargs]
  have e11 : σ (.n 11) = ch := by rw [hσ]; simp [oqMainF]
  have hpar : oqMainParams.map σ = args := by
    simp only [oqMainParams, List.map_cons, List.map_nil, eP 0 (by omega), eP 1 (by omega),
      eP 2 (by omega), eP 3 (by omega), eP 4 (by omega), eP 5 (by omega), eP 6 (by omega),
      eP 7 (by omega), eP 8 (by omega)]
    rfl
  have hb01 : s.base = 0 ∨ s.base = 1 := by rcases hs with ⟨h, -⟩ | ⟨h, -⟩ <;> omega
  by_cases hb : s.base = 1
  · have hk : oqMK s = oqEnd s 17 true + 3 := by simp [oqMK, hb]
    set e := oqEnd s 17 true with he
    have i1 := D.b_le_ch
    have i2 := D.ch_lt_e
    have hDb : D.b = 17 := rfl
    have hDe : D.e = e := rfl
    have eT : ∀ o, σ (.n (oqMK s + o)) = tl.getD o 0 := fun o => by
      rw [hσ]
      simp only [oqMainF, hb, ← he, show ¬ oqMK s + o < 9 by omega, show oqMK s + o ≠ 9 by omega,
        show oqMK s + o ≠ 10 by omega, show oqMK s + o ≠ 11 by omega, show oqMK s + o ≠ 12 by omega,
        show oqMK s + o ≠ 13 by omega, show oqMK s + o ≠ 14 by omega, show oqMK s + o ≠ 15 by omega,
        show oqMK s + o ≠ 16 by omega, show ¬ oqMK s + o < e by omega, show oqMK s + o ≠ e by omega,
        show oqMK s + o ≠ e + 1 by omega, show oqMK s + o ≠ e + 2 by omega, ↓reduceIte,
        Nat.add_sub_cancel_left]
      rfl
    have e13 : σ (.n 13) = gen ^ odd + word 1 0 := by rw [hσ]; simp [oqMainF, hb, hargs]
    have e16 : σ (.n 16) = bp := by rw [hσ]; simp [oqMainF, hb, hD, oqQD]
    have eQ : D.Hv σ := fun i h1 h2 => by
      rw [hσ]
      simp only [oqMainF, hb, ← he, show ¬ i < 9 by omega, show i ≠ 9 by omega, show i ≠ 10 by omega,
        show i ≠ 11 by omega, show i ≠ 12 by omega, show i ≠ 13 by omega, show i ≠ 14 by omega,
        show i ≠ 15 by omega, show i ≠ 16 by omega, show i < e by omega, ↓reduceIte]
    have eE1 : σ (.n (oqMK s - 2)) = positions * gen ^ odd := by
      rw [hσ, hk, show e + 3 - 2 = e + 1 by omega]
      simp only [oqMainF, hb, ← he, show ¬ e + 1 < 9 by omega, show e + 1 ≠ 9 by omega,
        show e + 1 ≠ 10 by omega, show e + 1 ≠ 11 by omega, show e + 1 ≠ 12 by omega,
        show e + 1 ≠ 13 by omega, show e + 1 ≠ 14 by omega, show e + 1 ≠ 15 by omega,
        show e + 1 ≠ 16 by omega, show ¬ e + 1 < e by omega, show e + 1 ≠ e by omega, ↓reduceIte]
      rfl
    have eE2 : σ (.n (oqMK s - 1)) = qptrs * gen ^ odd := by
      rw [hσ, hk, show e + 3 - 1 = e + 2 by omega]
      simp only [oqMainF, hb, ← he, show ¬ e + 2 < 9 by omega, show e + 2 ≠ 9 by omega,
        show e + 2 ≠ 10 by omega, show e + 2 ≠ 11 by omega, show e + 2 ≠ 12 by omega,
        show e + 2 ≠ 13 by omega, show e + 2 ≠ 14 by omega, show e + 2 ≠ 15 by omega,
        show e + 2 ≠ 16 by omega, show ¬ e + 2 < e by omega, show e + 2 ≠ e by omega,
        show e + 2 ≠ e + 1 by omega, ↓reduceIte]
      rfl
    exact ⟨hpar, by rw [e10, word_gen], e11, eT, fun _ => ⟨by rw [e13, word_one], eE1, eE2, e16, eQ⟩⟩
  · have hk : oqMK s = 13 := by simp [oqMK, hb]
    have eT : ∀ o, σ (.n (oqMK s + o)) = tl.getD o 0 := fun o => by
      rw [hσ]
      simp only [oqMainF, hb, hk, show ¬ 13 + o < 9 by omega, show 13 + o ≠ 9 by omega,
        show 13 + o ≠ 10 by omega, show 13 + o ≠ 11 by omega, show 13 + o ≠ 12 by omega,
        ↓reduceIte, Nat.add_sub_cancel_left]
      rfl
    exact ⟨hpar, by rw [e10, word_gen], e11, eT, fun h => absurd h hb⟩

/-- The tail after the loop's call walks to its return, calling and popping nothing. -/
theorem oqMainEnd_walk (σ : Val) (s : Oq) (k : ℕ) :
    ∃ es vs, walk σ (oqMainEnd s k ++ [.ret [.n (oqMainRet s k)]]) = .ret es vs ∧ calls es = [] := by
  unfold oqMainEnd oqMainRet
  split
  · exact ⟨[.atom (.const (.n (k + 3)) (word 0 0))], [.n (k + 3)], by simp [walk, walk1, Out.seq, Out.pre], rfl⟩
  · exact ⟨[.atom (.mul (.n (k + 3)) (.n 11) (.n oqMN)), .atom (.load (.n (k + 4)) (.n (k + 3)) 0),
      .atom (.copy (.n (k + 5)) (.n (k + 4)))], [.n (k + 5)], by simp [walk, walk1, Out.seq, Out.pre], rfl⟩

theorem flatMap_range_pairs {α : Type} (f : ℕ → List α) {odd : ℕ} (hodd : odd ≤ 1) : ∀ N : ℕ,
    (List.range (odd + 2 * N)).flatMap f =
      (if odd = 1 then f 0 else []) ++ (List.range N).flatMap fun j => f (odd + 2 * j) ++ f (odd + 2 * j + 1)
  | 0 => by
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hodd with rfl | rfl
    · rfl
    · simp
  | N + 1 => by
    rw [show odd + 2 * (N + 1) = odd + 2 * N + 1 + 1 by ring, List.range_succ, List.range_succ,
      List.flatMap_append, List.flatMap_append, flatMap_range_pairs f hodd N, List.range_succ, List.flatMap_append]
    simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, List.append_assoc]

theorem oqMainPre_noHeap : Stmt.atomsAll noHeapA oqMainPre = true := by unfold oqMainPre; nh
theorem oqEvenT_noHeap : Stmt.atomsAll noHeapA oqEvenT = true := by unfold oqEvenT; nh
theorem oqMainPost_noHeap (s : Oq) : Stmt.atomsAll noHeapA (oqMainPost s) = true := by unfold oqMainPost; nh
theorem oqMainEnd_noHeap (s : Oq) (k : ℕ) : Stmt.atomsAll noHeapA (oqMainEnd s k) = true := by
  unfold oqMainEnd; split <;> nh

theorem oqOddT_noHeap (s : Oq) : Stmt.atomsAll noHeapA (oqOddT s) = true := by
  unfold oqOddT
  exact atomsAll_app (atomsAll_app (by nh) (oqQueryT_noHeap s _ _ _ _ _ _ _ _ _)) (by nh)

theorem oqStartFlat_noHeap (s : Oq) (even : Bool) : Stmt.atomsAll noHeapA (oqStartFlat s even) = true := by
  unfold oqStartFlat
  split
  · refine atomsAll_app (atomsAll_app oqMainPre_noHeap ?_) (oqMainPost_noHeap s)
    split
    · exact oqEvenT_noHeap
    · exact oqOddT_noHeap s
  · rename_i hb
    simp only [oqMainA, hb, ↓reduceIte]
    nh

/-- Every `match` of the odd first query's branch names an arm. -/
theorem oqOddT_matchOk {σ : Val} {s : Oq} (h : WinSel σ s (oqCh s 17 true)) :
    ∀ st ∈ oqOddT s, MatchOk σ st := by
  intro st hst
  cases st with
  | match_ y arms =>
    unfold oqOddT at hst
    rcases List.mem_append.mp hst with hst | hst
    · rcases List.mem_append.mp hst with hst | hst
      · simp at hst
      · exact oqQuery_matchOk h _ hst
    · simp at hst
  | _ => trivial

end
end LeanVM.Guest.B1

namespace LeanVM.Guest.B1.VsC

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Memory LeanVM.Guest.B1
open LeanVM.Guest.Complete LeanVM.Guest.Value
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Prover.Exec (allocBase)

@[expose] public section

namespace OqCall

variable (o : OqCall)

/-- The chain buffer's words the call writes: all at a non-final level, its first at the final one. -/
def chainW : List E := if o.s.final = 1 then [o.chain 0] else o.chainL

/-- The call's entries: its queries' in order. -/
def pops : List Pop := (List.range o.Q).flatMap fun k => oqQE o.s (o.ws k)

/-- The call's arguments. -/
def margs : List E :=
  [ptrAt o.icap, ptrAt o.iflg, o.mu, ptrAt o.icf, ptrAt o.ihs, ptrAt o.ipos, ptrAt o.iptr, gen ^ o.N, gen ^ o.odd]

/-- The call's return. -/
def mret : E := if o.s.final = 1 then 0 else o.chain o.N

end OqCall

variable (fs : String → ℕ) (al : String → Bool) (cert : String → V → ℕ)

/-- **`opening_queries__L…` of shape `s` completes placed**: on every call's honest data with its
facts and region, at every frame `fp` and cursor `c` past its block, it returns the chain's end
(`0` at the final level), pops its queries' entries in order, every node exact. -/
def OqA (kd : ℕ) (name : String) (s : Oq) : Prop :=
  ∀ (o : OqCall) (R : ℕ → Prop), o.s = s → o.Static → o.Reg R →
    ∀ fp c, fp + fs name ≤ c → ∃ e, CallAtA fs al cert kd name o.margs [o.mret] R (fun _ => False)
      (fun _ => True) o.Mem (fun rd t => t.pops coreProgram rd = o.pops ∧ t.Every (ExactAt coreProgram rd))
      (fs name) fp c e

/-- **`OqA` with its end bounded**, `loop` its loop helper: within `(N + 2)·(fs loop + fs (tailKey loop) + 32)`
of its cursor. -/
def OqAE (kd : ℕ) (name loop : String) (s : Oq) : Prop :=
  ∀ (o : OqCall) (R : ℕ → Prop), o.s = s → o.Static → o.Reg R →
    ∀ fp c, fp + fs name ≤ c → ∃ e, e ≤ c + (o.N + 2) * (fs loop + fs (tailKey loop) + 32) ∧
      CallAtA fs al cert kd name o.margs [o.mret] R (fun _ => False)
      (fun _ => True) o.Mem (fun rd t => t.pops coreProgram rd = o.pops ∧ t.Every (ExactAt coreProgram rd))
      (fs name) fp c e

variable {fs al cert}

/-- The bounded form gives `OqA`. -/
theorem OqAE.toA {kd : ℕ} {name loop : String} {s : Oq} (h : OqAE fs al cert kd name loop s) :
    OqA fs al cert kd name s := by
  intro o R h1 h2 h3 fp c hfc
  obtain ⟨e, -, he⟩ := h o R h1 h2 h3 fp c hfc
  exact ⟨e, he⟩

/-- `opening_queries`' end, from its pieces. -/
theorem oq_end_le {c N L T x : ℕ} (hx : x ≤ c + N + 16 + N * L + T) :
    x ≤ c + (N + 2) * (L + T + 32) := by
  have hX : (N + 2) * (L + T + 32) = N * L + N * T + 32 * N + 2 * L + 2 * T + 64 := by ring
  omega

theorem chainW_load0 {o : OqCall} {rd : Reader} {c : ℕ} (h : ReadsAt rd (ptrAt c) o.chainW) :
    LoadHolds rd (ptrAt c) 0 (o.chain 0) := by
  unfold OqCall.chainW at h
  split at h
  · exact h 0 (by simp)
  · exact chain_load h (Nat.zero_le _)

theorem chainW_length (o : OqCall) : o.chainW.length = if o.s.final = 1 then 1 else o.N + 1 := by
  unfold OqCall.chainW OqCall.chainL; split <;> simp

/-- **`opening_queries__L…` completes placed.** -/
theorem oqA_complete' {kd : ℕ} {name loop : String} {s : Oq} {fm fl : Fn}
    (hfm : coreProgram.find? name = some fm) (hpm : fm.params = oqMainParams) (hbm : fm.body = oqMainT s loop)
    (hfl : coreProgram.find? loop = some fl) (hpl : fl.params = oqLoopParams) (hbl : fl.body = oqLoopT s loop)
    (hlp : coreProgram.loop loop = true) (hside : s.base = 0 ∨ s.base = 1 ∧ s.final = 0)
    (hex : ExactFreeG name) : OqAE fs al cert kd name loop s := by
  intro o R hos hst hR fp c hfc
  subst hos
  obtain ⟨hs, hfin, hcd, hrl, hnh, hodd, hN, hW⟩ := hst
  have hst : o.Static := ⟨hs, hfin, hcd, hrl, hnh, hodd, hN, hW⟩
  set ch0 : E := ptrAt c with hch0
  set D := o.qd 0 17 true 0 with hD
  set args := o.margs with hargs
  set rest := oqMainRest o.s ch0 (gen ^ o.N) (o.chain o.N) with hrest
  obtain ⟨σ, hσ⟩ : ∃ σ : Val, ∀ v : V, σ v = oqMainF o.s args ch0 D rest v.idx := ⟨_, fun _ ↦ rfl⟩
  obtain ⟨hpar, e10, e11, eT, eb1⟩ := oqMain_vals (σ := σ) hs rest (fun _ ↦ hσ _)
  set k := oqMK o.s with hk
  have hb01 : o.s.base = 0 ∨ o.s.base = 1 := by rcases hs with ⟨h, -⟩ | ⟨h, -⟩ <;> omega
  have hQ : o.Q = o.odd + 2 * o.N ∨ (o.s.base = 0 ∧ o.Q = o.N) := by
    rcases hb01 with hb | hb
    · right; exact ⟨hb, by simp [OqCall.Q, oqCount, hb]⟩
    · left; simp [OqCall.Q, oqCount, hb]
  have t : ∀ o', σ (.n (k + o')) = (oqMainTl (gen ^ o.N) rest).getD o' 0 := eT
  have t1 : σ (.n (k + 1)) = 1 + gen ^ o.N := by rw [t 1]; simp [oqMainTl, word_one]
  have t2 : σ (.n (k + 2)) = 1 := by rw [t 2]; simp [oqMainTl, word_one]
  have t3 : σ (.n (k + 3)) = rest.getD 0 0 := by rw [t 3]; rfl
  have t4 : σ (.n (k + 4)) = rest.getD 1 0 := by rw [t 4]; rfl
  have t5 : σ (.n (k + 5)) = rest.getD 2 0 := by rw [t 5]; rfl
  have eP : ∀ i < 9, σ (.n i) = args.getD i 0 := by
    intro i hi
    have := congrArg (·.getD i 0) hpar
    simp only [oqMainParams] at this
    interval_cases i <;> simpa [hargs, OqCall.margs] using this
  have hret : σ (.n (oqMainRet o.s k)) = o.mret := by
    unfold oqMainRet OqCall.mret
    split
    · rename_i hf
      rw [t3]; simp [hrest, oqMainRest, hf, word_zero]
    · rename_i hf
      rw [t5]; simp [hrest, oqMainRest, hf]
  -- the odd query is taken exactly at `odd = 1`
  have hodd1 : o.odd ≤ 1 := by omega
  have h13 : o.s.base = 1 → (σ (.n 13) = 0 ↔ o.odd ≠ 1) := fun hb ↦ by
    rw [(eb1 hb).1, gen_pow_add_one hodd1]; omega
  set even : Bool := decide (σ (.n 13) = 0) with heven
  have hodd_even : o.s.base = 1 → even = false → o.odd = 1 := fun hb he ↦ by
    by_contra hne
    have := (h13 hb).mpr hne
    simp [heven, this] at he
  -- the body's flat parts
  set ca : Stmt := .callIf (.n (k + 1)) loop (oqCallArgs o.s) with hca
  set en : List Stmt := oqMainEnd o.s k with hen
  have hpA : AllAtoms en := oqMainEnd_atoms o.s k
  set flb := oqStartFlat o.s even ++ ca :: en with hflb
  have hok := oqStart_ok o.s even
  have hflF : flb.all Stmt.flatM = true := by
    rw [hflb, List.all_append, hok.flatM, List.all_cons, hen, oqMainEnd_flatM]; rfl
  have hmoF : ∀ x ∈ flb, MatchOk σ x := by
    intro x hx
    rcases List.mem_append.mp hx with hx | hx
    · unfold oqStartFlat at hx
      split at hx
      · rename_i hb
        rcases List.mem_append.mp hx with hx | hx
        · rcases List.mem_append.mp hx with hx | hx
          · obtain ⟨a, rfl⟩ := oqMainPre_atoms _ hx; trivial
          · split at hx
            · obtain ⟨a, rfl⟩ := oqEvenT_atoms _ hx; trivial
            · rename_i he
              exact oqOddT_matchOk (D.winSel (eb1 hb).2.2.2.2) x hx
        · obtain ⟨a, rfl⟩ := oqMainPost_atoms o.s _ hx; trivial
      · rename_i hb
        cases x with
        | match_ y arms => simp [oqMainA, hb] at hx
        | _ => trivial
    · rcases List.mem_cons.mp hx with rfl | hx
      · trivial
      · obtain ⟨a, rfl⟩ := hpA _ hx
        trivial
  -- the walk
  have hwalk : ∃ es, walk σ fm.body = .ret es [.n (oqMainRet o.s k)] ∧
      allocDsts es = allocDsts (flb.flatMap (fmEvs σ)) ∧ allocs σ es = allocs σ (flb.flatMap (fmEvs σ)) ∧
      addrs es = addrs (flb.flatMap (fmEvs σ)) ∧ calls es = calls (flb.flatMap (fmEvs σ)) ∧
      loadAddrs σ es = loadAddrs σ (flb.flatMap (fmEvs σ)) ∧
      heapHintAddrs σ es = heapHintAddrs σ (flb.flatMap (fmEvs σ)) ∧
      ∀ e ∈ es, e ∈ flb.flatMap (fmEvs σ) ∨ (o.s.base = 1 ∧ e = .inK (.n 13)) := by
    by_cases hb : o.s.base = 1
    · have hsf : oqStartFlat o.s even = oqMainPre ++ (if σ (.n 13) = 0 then oqEvenT else oqOddT o.s) ++
          oqMainPost o.s := by
        unfold oqStartFlat
        rw [ite_eq_left hb]
        by_cases h0 : σ (.n 13) = 0
        · rw [show even = true by rw [heven]; exact decide_eq_true h0, ite_eq_left rfl, ite_eq_left h0]
        · rw [show even = false by rw [heven]; exact decide_eq_false h0, ite_eq_right (by decide), ite_eq_right h0]
      have hbody : fm.body = oqMainPre ++ .ite (.n 13) oqEvenT (oqOddT o.s) ::
          ((oqMainPost o.s ++ ca :: en) ++ [.ret [.n (oqMainRet o.s k)]]) := by
        rw [hbm, oqMainT_eq, oqMainA_one hb]
        simp only [List.append_assoc, List.cons_append, ← hk, hca, hen]
      have hfl' : flb = oqMainPre ++ (if σ (.n 13) = 0 then oqEvenT else oqOddT o.s) ++
          (oqMainPost o.s ++ ca :: en) := by rw [hflb, hsf, List.append_assoc]
      have hal : ∀ l : List Stmt, (∀ x ∈ l, x ∈ flb) → l.all Stmt.flatM = true ∧ ∀ x ∈ l, MatchOk σ x :=
        fun l hl ↦ ⟨List.all_eq_true.mpr fun x hx ↦ List.all_eq_true.mp hflF x (hl x hx),
          fun x hx ↦ hmoF x (hl x hx)⟩
      obtain ⟨b1, b2⟩ := hal _ fun x hx ↦ by
        rw [hfl']; exact List.mem_append_left _ (List.mem_append_right _ hx)
      obtain ⟨p1, p2⟩ := hal _ fun x hx ↦ by rw [hfl']; exact List.mem_append_right _ hx
      obtain ⟨q1, q2⟩ := hal _ fun x hx ↦ by
        rw [hfl']; exact List.mem_append_left _ (List.mem_append_left _ hx)
      have hw := walk_ite_flatM σ (.n 13) oqEvenT (oqOddT o.s) (oqMainPost o.s ++ ca :: en)
        [.n (oqMainRet o.s k)] b1 b2 p1 p2 oqMainPre q1 q2
      obtain ⟨i1, i2, i3, i4, i5⟩ := ite_parts σ (.n 13) oqMainPre
        (if σ (.n 13) = 0 then oqEvenT else oqOddT o.s) (oqMainPost o.s ++ ca :: en)
      refine ⟨_, by rw [hbody]; exact hw, ?_, ?_, ?_, ?_, ?_, ?_, fun e he ↦ ?_⟩
      · rw [i1, hfl']
      · rw [i2, hfl']
      · rw [i3, hfl']
      · rw [i4, hfl']
      · rw [i5, hfl']
      · rw [hfl']
        simp only [heapHintAddrs, List.flatMap_append, List.flatMap_cons, Ev.hintAddrs, List.nil_append,
          List.append_assoc]
      · rw [hfl', List.flatMap_append, List.flatMap_append]
        rcases List.mem_append.mp he with he | he
        · exact Or.inl (List.mem_append_left _ (List.mem_append_left _ he))
        · rcases List.mem_cons.mp he with rfl | he
          · exact Or.inr ⟨hb, rfl⟩
          · rcases List.mem_append.mp he with he | he
            · exact Or.inl (List.mem_append_left _ (List.mem_append_right _ he))
            · exact Or.inl (List.mem_append_right _ he)
    · have hbody : fm.body = flb ++ [.ret [.n (oqMainRet o.s k)]] := by
        rw [hbm, oqMainT_eq, hflb, oqStartFlat, ite_eq_right hb]
        simp only [List.append_assoc, List.cons_append, ← hk, hca, hen]
      exact ⟨_, by rw [hbody]; exact walk_flatM σ _ flb hflF hmoF, rfl, rfl, rfl, rfl, rfl, rfl,
        fun e he => Or.inl he⟩
  obtain ⟨es, hw, i1, i2, i3, i4, i5, i6, hesub⟩ := hwalk
  obtain ⟨j1, j2, j3, j4⟩ := flatM_parts σ flb hflF
  have hal : flb.filterMap Stmt.allocSz = [(.n 11, .inr (.n 10))] := by
    rw [hflb, List.filterMap_append, oqStart_allocSz, List.filterMap_cons, hen, oqMainEnd_allocSz]
    rfl
  have hlogN : logG (σ (.n 10)) = o.N + 1 := by
    rw [e10, ← pow_succ, gen_pow_eq_ofK, logG_spec hN]
  have hallocs : allocs σ es = [o.N + 1] := by
    rw [i2, j2, hal]; simp [hlogN]
  have hsum : (allocs σ es).sum = o.N + 1 := by rw [hallocs]; simp
  have hcalls : calls es = [⟨loop, oqCallArgs o.s, [], decide (σ (.n (k + 1)) ≠ 0)⟩] := by
    rw [i4, j4, hflb, List.filterMap_append, oqStart_callS, List.filterMap_cons, callS_atoms hpA]
    rfl
  have hnode : NodeAt cert (fp, c) name σ (allocs σ es) es := by
    refine ⟨?_, fun q hq => ?_⟩
    · rw [i1, j1, hal, hallocs]; simp [bases, e11, hch0]
    · have hb : ∀ p run, oqAlloc ≠ .frameAddr p run := fun p run h ↦ by cases h
      rw [i3, j3, hflb, List.filterMap_append, hok.addrS' hb, List.filterMap_cons, hen,
        oqMainEnd_addrS] at hq
      simp [hca, Stmt.addrS] at hq
  have hown : ∀ i, c ≤ i → i < c + (o.N + 1) → ownData cert fp c name (allocs σ es) es i := by
    intro i h1 h2
    rw [hallocs]
    exact ownData_buf (s := o.N + 1) (b := c) (by simp [bases]) h1 h2
  -- the own words: the chain buffer
  let Wo : Words := [(c, o.chainW)]
  have hWo : ∀ rd, HoldsWords rd Wo → ReadsAt rd (ptrAt c) o.chainW := fun rd h => h _ List.mem_cons_self
  have hWoIn : WordsInA Wo (fp + 2) (fp + fs name) c (c + (allocs σ es).sum) := by
    rw [hsum]
    refine ⟨fun q hq => Or.inr ?_, List.pairwise_singleton _ _⟩
    simp only [Wo, List.mem_cons, List.not_mem_nil, or_false] at hq
    subst hq
    refine ⟨le_rfl, ?_⟩
    rw [chainW_length]; split <;> omega
  have hchL : ∀ rd, HoldsWords rd Wo → o.s.final ≠ 1 → ReadsAt rd (ptrAt c) o.chainL := fun rd h hf => by
    have := hWo rd h; unfold OqCall.chainW at this; simpa [hf] using this
  -- the events
  have hev : ∀ rd, o.Mem rd → HoldsWords rd Wo → ∀ ev ∈ es, ev.Holds rd σ := by
    intro rd hm hWr
    have hc0 := chainW_load0 (hWo rd hWr)
    have hA := (oqMain_at (rd := rd) (σ := σ) hs hfin hodd
      (fun ho => by
        have hb : o.s.base = 1 := by omega
        have hf0 : o.s.final ≠ 1 := by rcases hside with h | h <;> omega
        have h0Q : 0 < o.Q := by simp [OqCall.Q, oqCount, hb, ho]
        obtain ⟨hx, hbp, -, -⟩ := hm.2.2 0 h0Q
        refine ⟨hx, hbp, o.qdOk hst hm h0Q 17 true 0, ?_⟩
        rw [oqResV_eq hf0]
        simpa [OqCall.chain, oqChain, ho, OqCall.ds, hch0] using hc0)
      (fun ho => by simpa [OqCall.chain, oqChain, ho, hch0] using hc0) rest (fun _ ↦ hσ _)).2.2.2.2.2.2
    have hst' : BlockOkC anyCall rd σ (oqStartFlat o.s even) := by
      unfold OqStartOk at hA
      unfold oqStartFlat
      split
      · rename_i hb
        simp only [hb, ↓reduceIte] at hA
        obtain ⟨hpp, -, hz, hn⟩ := hA
        obtain ⟨hpre, hpost⟩ := blockOkC_append.mp hpp
        refine blockOkC_append.mpr ⟨blockOkC_append.mpr ⟨hpre, ?_⟩, hpost⟩
        by_cases h0 : σ (.n 13) = 0
        · simp only [heven, h0, decide_true, ↓reduceIte]; exact hz h0
        · simp only [heven, h0, decide_false, Bool.false_eq_true, ↓reduceIte]; exact hn h0
      · rename_i hb
        simp only [hb, ↓reduceIte] at hA
        exact hA
    have hpostH : ∀ a, Stmt.atom a ∈ en → a.Holds rd σ := by
      intro a ha
      rw [hen, oqMainEnd] at ha
      split at ha
      · rename_i hf
        simp only [List.mem_singleton, Stmt.atom.injEq] at ha
        subst ha
        show σ (.n (k + 3)) = word 0 0
        rw [t3]; simp [hrest, oqMainRest, hf]
      · rename_i hf
        simp only [List.mem_cons, List.not_mem_nil, or_false, Stmt.atom.injEq] at ha
        have u3 : σ (.n (k + 3)) = ch0 * gen ^ o.N := by rw [t3]; simp [hrest, oqMainRest, hf]
        have u4 : σ (.n (k + 4)) = o.chain o.N := by rw [t4]; simp [hrest, oqMainRest, hf]
        have u5 : σ (.n (k + 5)) = o.chain o.N := by rw [t5]; simp [hrest, oqMainRest, hf]
        rcases ha with rfl | rfl | rfl
        · show σ (.n (k + 3)) = σ (.n 11) * σ (.n oqMN)
          rw [u3, e11, eP 7 (by omega)]; rfl
        · show LoadHolds rd (σ (.n (k + 3))) 0 (σ (.n (k + 4)))
          rw [u3, u4, loadHolds_mul_gen_pow, Nat.add_zero]
          exact chain_load (hchL rd hWr hf) le_rfl
        · show σ (.n (k + 5)) = σ (.n (k + 4))
          rw [u5, u4]
    have hFev : ∀ e ∈ flb.flatMap (fmEvs σ), e.Holds rd σ := by
      intro e he
      obtain ⟨x, hx, he⟩ := List.mem_flatMap.mp he
      rcases List.mem_append.mp hx with hx | hx
      · exact hok.evs_holds hst' e (List.mem_flatMap.mpr ⟨x, hx, he⟩)
      · rcases List.mem_cons.mp hx with rfl | hx
        · change e ∈ slEvs σ ca at he
          simp only [hca, slEvs, List.mem_cons, List.not_mem_nil, or_false] at he
          rcases he with rfl | he
          · show IsInK (σ (.n (k + 1)))
            rw [t1, gen_pow_eq_ofK, ← ofK_one, ← ofK_add]; exact ofK_isInK _
          · rw [he]; split <;> trivial
        · obtain ⟨a, rfl⟩ := hpA _ hx
          simp only [fmEvs, slEvs, List.mem_singleton] at he
          subst he
          exact hpostH a hx
    intro ev hev'
    rcases hesub ev hev' with h | ⟨hb, rfl⟩
    · exact hFev ev h
    · show IsInK (σ (.n 13))
      rw [(eb1 hb).1, gen_pow_eq_ofK, ← ofK_one, ← ofK_add]; exact ofK_isInK _
  -- the loads
  have hloads : ∀ A ∈ loadAddrs σ es, ∃ i, A = addressOfIndex i ∧
      (ownData cert fp c name (allocs σ es) es i ∨ R i ∨ False) := by
    intro A hAl
    rw [i5, loadAddrs_flatM σ flb hflF] at hAl
    obtain ⟨⟨p, off⟩, hq, rfl⟩ := List.mem_map.mp hAl
    rw [hflb, List.filterMap_append] at hq
    have hb : ∀ d p off, oqAlloc ≠ .load d p off := fun d p off h ↦ by cases h
    rcases List.mem_append.mp hq with hq | hq
    · rcases hok.load' hb hq with ⟨hb1, he, hl⟩ | ⟨hb1, he, rfl, rfl⟩ | ⟨hb1, he, rfl, rfl⟩ | ⟨rfl, rfl⟩
      · have ho := hodd_even hb1 he
        have h0Q : 0 < o.Q := by simp [OqCall.Q, oqCount, hb1, ho]
        obtain ⟨-, -, -, e16, hvD⟩ := eb1 hb1
        obtain ⟨i, hi, hr⟩ := oqQLoad_in (R := R) (d := D) hvD (coefs := .n oqMCoefs) (hs := .n oqMHs)
          (bp := .n 16) (by rw [eP 3 (by omega), eP 4 (by omega), e16]; exact hR.1 0 h0Q) hl
        exact ⟨i, hi, Or.inr (Or.inl hr)⟩
      · have h0Q : 0 < o.Q := by simp [OqCall.Q, oqCount, hb1, hodd_even hb1 he]
        rw [eP 5 (by omega)]
        exact ⟨o.ipos, by simp [hargs, OqCall.margs, ptrAt], Or.inr (Or.inl (by simpa using (hR.2 0 h0Q).1))⟩
      · have h0Q : 0 < o.Q := by simp [OqCall.Q, oqCount, hb1, hodd_even hb1 he]
        rw [eP 6 (by omega)]
        exact ⟨o.iptr, by simp [hargs, OqCall.margs, ptrAt], Or.inr (Or.inl (by simpa using (hR.2 0 h0Q).2))⟩
      · rw [e11, hch0]
        exact ⟨c, by simp [ptrAt], Or.inl (hown _ le_rfl (by omega))⟩
    · rw [List.filterMap_cons] at hq
      simp only [hca, stmtLoad?] at hq
      rw [hen, oqMainEnd] at hq
      split at hq
      · simp [stmtLoad?] at hq
      · rename_i hf
        simp only [stmtLoad?, List.filterMap_cons, List.filterMap_nil, List.mem_singleton,
          Prod.mk.injEq] at hq
        obtain ⟨rfl, rfl⟩ := hq
        have u3 : σ (.n (k + 3)) = ch0 * gen ^ o.N := by rw [t3]; simp [hrest, oqMainRest, hf]
        rw [u3, hch0]
        exact ⟨c + o.N + 0, addr_gpow c o.N 0, Or.inl (hown _ (by omega) (by omega))⟩
  have hhints : ∀ A ∈ heapHintAddrs σ es, ∃ i, A = addressOfIndex i ∧
      (ownData cert fp c name (allocs σ es) es i ∨ R i ∨ False) := by
    intro A hA
    rw [i6, heapHintAddrs_flatM σ flb hflF (by
      rw [hflb, Stmt.atomsAll_append, oqStartFlat_noHeap]
      simp only [Stmt.atomsAll, hca, Bool.true_and]
      exact oqMainEnd_noHeap o.s k)] at hA
    exact absurd hA List.not_mem_nil
  -- the loop
  have hargsL : (oqCallArgs o.s).map σ = o.args c 0 := by
    rcases hb01 with hb | hb
    · have ho : o.odd = 0 := by omega
      have f1 : (if o.s.base = 1 then k - 2 else oqMPos) = oqMPos := by simp [hb]
      have f2 : (if o.s.base = 1 then k - 1 else oqMQp) = oqMQp := by simp [hb]
      simp only [oqCallArgs, f1, f2, List.map_cons, List.map_nil, ← hk, t2,
        eP 7 (by omega), eP 5 (by omega), eP 6 (by omega), eP 0 (by omega), eP 1 (by omega),
        eP 3 (by omega), eP 4 (by omega), e11, eP 2 (by omega)]
      simp [hargs, OqCall.margs, OqCall.args, ho, hch0]
    · obtain ⟨-, eE1, eE2, -, -⟩ := eb1 hb
      simp only [oqCallArgs, hb, ↓reduceIte, List.map_cons, List.map_nil, ← hk, t2, eE1, eE2,
        eP 7 (by omega), eP 0 (by omega), eP 1 (by omega), eP 3 (by omega),
        eP 4 (by omega), e11, eP 2 (by omega)]
      simp [hargs, OqCall.margs, OqCall.args, hch0, ptrAt_mul_gen]
  set Rc : ℕ → Prop := fun i => R i ∨ (c ≤ i ∧ i < c + (o.N + 1)) with hRc
  have hRcR : ∀ i, Rc i → (R i ∨ ownData cert fp c name (allocs σ es) es i) ∨ False := by
    rintro i (hi | ⟨h1, h2⟩)
    · exact Or.inl (Or.inl hi)
    · exact Or.inl (Or.inr (hown i h1 h2))
  have hLreg : o.Reg Rc := ⟨fun k hk => (hR.1 k hk).mono fun i h => Or.inl h,
    fun k hk => ⟨Or.inl (hR.2 k hk).1, Or.inl (hR.2 k hk).2⟩⟩
  have hLc : o.s.final ≠ 1 → ∀ i ≤ o.N, Rc (c + i) := fun _ i hi => Or.inr ⟨by omega, by omega⟩
  have hfin' : ∀ rd, o.Mem rd ∧ HoldsWords rd Wo → o.Mem rd ∧ (o.s.final ≠ 1 → ReadsAt rd (ptrAt c) o.chainL) :=
    fun rd h => ⟨h.1, hchL rd h.2⟩
  have hkids : ∃ e, e ≤ c + (o.N + 2) * (fs loop + fs (tailKey loop) + 32) ∧
      KidsAtF fs al cert kd σ (fun i => R i ∨ ownData cert fp c name (allocs σ es) es i) o.Mem
      (fun rd => HoldsWords rd Wo) (fun _ => False) [fun rd t => t.pops coreProgram rd = o.popsFrom 0]
      (calls es) (c + (allocs σ es).sum) e (fun rd => HoldsWords rd Wo) (fun _ => False) := by
    rw [hcalls, hsum]
    have hNlt : o.N + 1 < ordG := hN
    by_cases hN0 : o.N = 0
    · have hd : decide (σ (.n (k + 1)) ≠ 0) = false := by
        rw [t1]; simp [hN0, ← CharTwo.add_self_eq_zero (1 : E)]
      refine ⟨allocBase (al loop) (c + (o.N + 1)) + fs (tailKey loop),
        oq_end_le (by have := allocBase_le (al loop) (c + (o.N + 1)); omega), ?_⟩
      rw [KidsAtF]
      simp only [hd, Bool.false_eq_true, ↓reduceIte]
      refine ⟨⟨fun v => (o.args c 0).getD v.idx 0, fl, hfl, ?_⟩, ?_⟩
      · rw [hpl, hargsL]
        exact params_range_map (o.args c 0)
      · rw [KidsAtF]; exact ⟨rfl, fun _ h => h, fun _ h => h⟩
    · have hd : decide (σ (.n (k + 1)) ≠ 0) = true := by
        rw [t1]; simpa using (one_add_gen_pow hNlt).mpr hN0
      have hL := oqL_complete (fs := fs) (al := al) (cert := cert) (kd := kd) hfl hpl hbl hlp hst hLreg hLc
        (o.N - 1) 0 (by omega)
      set fL := allocBase (al loop) (c + (o.N + 1)) with hfL
      refine ⟨fL + lpB fs loop o.N 0, oq_end_le (by
        have := allocBase_le (al loop) (c + (o.N + 1)); rw [hfL]; unfold lpB; rw [Nat.sub_zero]; omega), ?_⟩
      rw [KidsAtF]
      simp only [hd, ↓reduceIte]
      refine ⟨lpB fs loop o.N 0, fL + lpB fs loop o.N 0, Rc, fun _ => False, fun _ => True, hRcR, ?_, ?_⟩
      · rw [hargsL]
        exact (hL fL (fL + lpB fs loop o.N 0) le_rfl).mono (fun _ h => h) (fun _ h => h) (fun _ h => h)
          (fun rd h => hfin' rd h) (fun _ _ _ h => h)
      · rw [KidsAtF]; exact ⟨rfl, fun _ h => h.1, fun _ h => h.elim⟩
  obtain ⟨e, hbe, hk⟩ := hkids
  have hlo : coreProgram.loop name = false := fn_loop_main hfm hbm
  refine ⟨e, hbe, callAtA_node hlo hfc ⟨σ, fm, es, [.n (oqMainRet o.s k)], Wo,
    [fun rd t => t.pops coreProgram rd = o.popsFrom 0], fun rd => HoldsWords rd Wo, fun _ => False,
    hfm, by rw [hpm]; exact hpar, hw, by simp [hret], hnode, hWoIn, hloads, hhints, fun _ h => h.elim, hk,
    fun _ _ => trivial, fun rd _ hp hO => hev rd hp hO, ?_⟩⟩
  -- the post
  intro rd ts hl hp hO hv hq
  have hvalid : (Memory.Tree.node name σ (allocs σ es) ts).Valid coreProgram rd o.margs [o.mret] :=
    ⟨fm, hfm, by rw [hpm]; exact hpar, es, _, hw, by simp [hret], hev rd hp hO, hv⟩
  refine ⟨?_, every_exact_of_free hex hvalid rfl rd⟩
  -- the pops
  have hkn : Tree.popsKids coreProgram rd ts = [if o.N = 0 then [] else o.popsFrom 0] := by
    rw [hcalls] at hv hq
    refine tail_pops hv hq (fun ht t h => ?_) (fun hf => ?_)
    · have hN0 : o.N ≠ 0 := by
        intro h0
        simp only [decide_eq_true_eq, t1, h0, pow_zero] at ht
        exact ht (CharTwo.add_self_eq_zero 1)
      rw [ite_eq_right hN0]; exact h
    · have hN0 : o.N = 0 := by
        by_contra h0
        simp only [decide_eq_false_iff_not, not_not, t1] at hf
        exact ((one_add_gen_pow hN).mpr h0) hf
      rw [ite_eq_left hN0]
  have hsel : o.s.base = 1 → σ (.n 13) ≠ 0 → WinSel σ o.s (oqCh o.s 17 true) := fun hb _ ↦
    D.winSel (eb1 hb).2.2.2.2
  rw [oqMain_pops hfm hbm σ _ hsel hkn]
  unfold startPops OqCall.pops
  have hpf : (if o.N = 0 then [] else o.popsFrom 0) = (List.range o.N).flatMap o.iterPops := by
    split
    · rename_i h0; simp [h0]
    · simp [OqCall.popsFrom, List.range_eq_range']
  rw [hpf]
  have hit : ∀ j, o.iterPops j = if o.s.base = 1 then oqQE o.s (o.ws (o.odd + 2 * j)) ++
      oqQE o.s (o.ws (o.odd + 2 * j + 1)) else oqQE o.s (o.ws j) := fun j => rfl
  rcases hb01 with hb | hb
  · have hQ0 : o.Q = o.N := by simp [OqCall.Q, oqCount, hb]
    have hns : ¬ (o.s.base = 1 ∧ σ (.n 13) ≠ 0) := fun h => by omega
    rw [hQ0, ite_eq_right hns, List.nil_append]
    congr 1; funext j; rw [hit, ite_eq_right (by omega)]
  · have hQ1 : o.Q = o.odd + 2 * o.N := by simp [OqCall.Q, oqCount, hb]
    rw [hQ1, flatMap_range_pairs _ hodd1]
    have hodd' : (o.s.base = 1 ∧ σ (.n 13) ≠ 0) ↔ o.odd = 1 :=
      ⟨fun ⟨_, h⟩ => by by_contra hne; exact h ((h13 hb).mpr hne), fun h => ⟨hb, fun h0 => (h13 hb).mp h0 h⟩⟩
    have hrest : (List.range o.N).flatMap o.iterPops = (List.range o.N).flatMap fun j =>
        oqQE o.s (o.ws (o.odd + 2 * j)) ++ oqQE o.s (o.ws (o.odd + 2 * j + 1)) := by
      congr 1; funext j; rw [hit, ite_eq_left hb]
    rw [hrest]
    by_cases ho : o.odd = 1
    · rw [ite_eq_left (hodd'.mpr ho), ite_eq_left ho,
        show queryPops σ o.s 17 true = queryPops σ D.s D.b D.emit from rfl, D.queryPops_vals (eb1 hb).2.2.2.2]
      rfl
    · rw [ite_eq_right (fun h => ho (hodd'.mp h)), ite_eq_right ho]

end
end LeanVM.Guest.B1.VsC
