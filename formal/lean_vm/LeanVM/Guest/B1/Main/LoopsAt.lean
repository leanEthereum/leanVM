/-
  LeanVM.Guest.B1.Main.LoopsAt

  `main`'s loops placed, uniformly, by bounded trees (`CompleteAtB`): the hint-filling loops
  (`__loop0`, `__loop1`, `__loop2`), the raw signatures' writers (`__loop3`, `__loop4`) and a
  child's DA roots (`__loop100`), from the words of the caller's layout and their callees'
  `CompleteRelB`.
-/

module

public import LeanVM.Guest.B1.Main.CalleesAt
public import LeanVM.Guest.B1.Main.LoopsC
public import LeanVM.Guest.B1.Main.MainC

/-!
# `main`'s loops, placed

`__loop0` to `__loop2` place nothing, load nothing and check no range, so they hold on every
memory and their trees serve every memory (`quietLoop_completeAt`), within the bound of their
valid trees, their frames (`leafLoop_total`).
`__loop3`, `__loop4` and `__loop100` are straight-line iterations (`loopStep_straight`) with one
callee each, so `m` iterations are within `m` times the frame and the callee's bound, plus a
frame; their valuations take the range checks' words from the memory (`loop3Val`, …), which
`LowDef 16` defines. `CellL L i v`: the layout `L` holds `v` at word `i`.
-/

namespace LeanVM.Guest.B1.Main

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Memory
open LeanVM.Protocol LeanVM.Protocol.Blake2sHash LeanVM.Protocol.Verifier LeanVM.Node
open LeanVM.Guest.B1 (DisjL disj_nil disj_append bufL_disj Within LowDef CompleteAtB CompleteRelB Returns Kid CallsMatch
  OutsOk relAtIn_dmono Meaning_verify_lean_xmss Meaning_verify_sig_lean_sphincs kidsBound)

@[expose] public section

variable {fs : String → ℕ} {cert : String → V → ℕ} {rd : Reader}

/-! ## Layout words -/

/-- The layout `L` holds `v` at word `i`. -/
def CellL (L : Layout) (i : ℕ) (v : E) : Prop :=
  ∃ b xs, (b, xs) ∈ L ∧ b ≤ i ∧ ∃ h : i - b < xs.length, xs[i - b] = v

theorem CellL.region {L : Layout} {i : ℕ} {v : E} (h : CellL L i v) : RegionL L i := by
  obtain ⟨b, xs, hq, hb, hk, -⟩ := h
  exact ⟨(b, xs), hq, hb, by simp only; omega⟩

theorem CellL.load {L : Layout} {b k : ℕ} {v : E} (hL : MemL rd L) (h : CellL L (b + k) v) :
    LoadHolds rd (ofK (gpow b)) k v := by
  obtain ⟨b', xs, hq, hb, hk, rfl⟩ := h
  have := (hL _ hq (b + k - b') hk).2
  refine ⟨(isInK_iff _).mpr ⟨_, rfl⟩, ?_⟩
  rw [addr_ofK] at this ⊢
  rwa [show b' + (b + k - b') = b + k by omega] at this

theorem ofK_gpow_mul_gen (a b : ℕ) : ofK (gpow a) * gen ^ b = ofK (gpow (a + b)) := by
  rw [gen_pow_eq_ofK, ← ofK_mul]; congr 1; exact (pow_add _ _ _).symm

theorem cellL_loadHolds {L : Layout} {b k : ℕ} {v : E} (hL : MemL rd L) (h : CellL L (b + k) v) :
    LoadHolds rd (ofK (gpow b) * gen ^ k) 0 v := by
  rw [loadHolds_mul_gen_pow, Nat.add_zero]; exact h.load hL

theorem gen_pow_succ_add_ne {j m : ℕ} (hm : m < 2 ^ 34) (hj : j + 1 < 2 ^ 34) :
    decide (gen ^ j * gen + gen ^ m ≠ 0) = decide (j + 1 ≠ m) := by
  rw [decide_eq_decide, ne_eq, ne_eq, gen_pow_add_eq_zero_iff]
  exact ⟨fun h1 h2 => h1 (by rw [h2]), fun h1 h2 => h1 (gen_pow_inj' hj hm h2.symm)⟩

/-! ## The hint-filling loops -/

/-- **A quiet loop holding on every memory is complete** at every frame pointer, within the bound
`B` of its valid trees. -/
theorem quietLoop_completeAt {f : String} (hS : coreProgram.QuietIn [f]) (κ : ℕ) (Lin : Layout)
    {args : List E} (h : ∀ rd, coreProgram.Rel rd f args []) {B : ℕ}
    (hB : ∀ (rd : Reader) (t : Tree), t.name = f → t.Valid coreProgram rd args [] →
      t.BufsOk coreProgram → t.total fs ≤ B) :
    CompleteAtB fs cert κ f Lin args (Returns []) B := by
  obtain ⟨n, hn⟩ := relAtIn_uniform_quiet (fs := fs) (cert := cert) coreProgram_wf coreProgram_fresh hS
    (List.mem_singleton_self f) (h fun _ => none)
  intro fp
  have hnB : n ≤ B := by
    obtain ⟨t, hname, hv, hbo, -, ht, -⟩ := hn fp (RegionL Lin) (fun _ => none) fun A hA => by simp at hA
    rw [← ht]; exact hB _ t hname hv hbo
  refine ⟨n, [], [], [], ⟨rfl, rfl⟩, fun q hq => by simp at hq, disj_nil, hnB, fun rd _ _ => ?_⟩
  refine relAtIn_dmono (hn fp (RegionL Lin) rd fun A hA => by simp at hA) fun i hi => ?_
  obtain ⟨q, hq, _⟩ := hi; simp at hq

set_option maxRecDepth 100000 in
theorem loop0_quiet : coreProgram.QuietIn ["__loop0"] := by
  intro g hg fn hfn
  rw [List.mem_singleton] at hg; subst hg
  rw [find_loop0] at hfn; cases hfn; decide +kernel

set_option maxRecDepth 100000 in
theorem loop1_quiet : coreProgram.QuietIn ["__loop1"] := by
  intro g hg fn hfn
  rw [List.mem_singleton] at hg; subst hg
  rw [find_loop1] at hfn; cases hfn; decide +kernel

set_option maxRecDepth 100000 in
theorem loop2_quiet : coreProgram.QuietIn ["__loop2"] := by
  intro g hg fn hfn
  rw [List.mem_singleton] at hg; subst hg
  rw [find_loop2] at hfn; cases hfn; decide +kernel

theorem core30_split : Fn.body Data.core30 = (Fn.body Data.core30).take 9 ++
    [.callIf (.n 8) "__loop0" [.n 10, .n 1, .n 2], .ret []] := stmtsEqb_sound (by decide +kernel)

theorem core31_split : Fn.body Data.core31 = (Fn.body Data.core31).take 10 ++
    [.callIf (.n 10) "__loop1" [.n 12, .n 1, .n 2, .n 3], .ret []] := stmtsEqb_sound (by decide +kernel)

theorem core32_split : Fn.body Data.core32 = (Fn.body Data.core32).take 10 ++
    [.callIf (.n 10) "__loop2" [.n 12, .n 1, .n 2, .n 3], .ret []] := stmtsEqb_sound (by decide +kernel)

/-- `__loop0`'s valid trees over `m` iterations. -/
theorem loop0_total {rd : Reader} {m : ℕ} {rest : List E} {t : Tree} {rets : List E} (hm : 0 < m)
    (hn : t.name = "__loop0") (hv : t.Valid coreProgram rd (1 :: gen ^ m :: rest) rets)
    (hbo : t.BufsOk coreProgram) : t.total fs ≤ m * fs "__loop0" + fs "__loop0" :=
  leafLoop_total find_loop0 core30_split rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (mem_of_getElem? 4 rfl) (mem_of_getElem? 5 rfl) (mem_of_getElem? 6 rfl) (mem_of_getElem? 7 rfl)
    (mem_of_getElem? 8 rfl) hm hn hv hbo

/-- `__loop1`'s valid trees over `m` iterations. -/
theorem loop1_total {rd : Reader} {m : ℕ} {rest : List E} {t : Tree} {rets : List E} (hm : 0 < m)
    (hn : t.name = "__loop1") (hv : t.Valid coreProgram rd (1 :: gen ^ m :: rest) rets)
    (hbo : t.BufsOk coreProgram) : t.total fs ≤ m * fs "__loop1" + fs "__loop1" :=
  leafLoop_total find_loop1 core31_split rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (mem_of_getElem? 5 rfl) (mem_of_getElem? 6 rfl) (mem_of_getElem? 7 rfl) (mem_of_getElem? 8 rfl)
    (mem_of_getElem? 9 rfl) hm hn hv hbo

/-- `__loop2`'s valid trees over `m` iterations. -/
theorem loop2_total {rd : Reader} {m : ℕ} {rest : List E} {t : Tree} {rets : List E} (hm : 0 < m)
    (hn : t.name = "__loop2") (hv : t.Valid coreProgram rd (1 :: gen ^ m :: rest) rets)
    (hbo : t.BufsOk coreProgram) : t.total fs ≤ m * fs "__loop2" + fs "__loop2" :=
  leafLoop_total find_loop2 core32_split rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (mem_of_getElem? 5 rfl) (mem_of_getElem? 6 rfl) (mem_of_getElem? 7 rfl) (mem_of_getElem? 8 rfl)
    (mem_of_getElem? 9 rfl) hm hn hv hbo

/-! ## `__loop3` -/

/-- `__loop3`'s statements before its return. -/
noncomputable def loop3Pre : List Stmt := (Fn.body Data.core33).dropLast

theorem core33_split : Fn.body Data.core33 = loop3Pre ++ [.ret []] := stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem loop3_parts : loop3Pre.all Stmt.straight = true ∧ loop3Pre.filterMap Stmt.allocSz = [] ∧
    loop3Pre.filterMap Stmt.addrS = [] ∧
    loop3Pre.filterMap Stmt.callS = [(none, "verify_lean_xmss", [.n 14], [])] ++
      [(some (.n 17), "__loop3", [.n 19, .n 1, .n 2, .n 3, .n 4], [])] ∧
    loop3Pre.filterMap LeanVM.Guest.B1.Stmt.loadS = [(.n 11, 0)] := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel

theorem loop3_isLoop : coreProgram.loop "__loop3" = true := by
  rw [Program.loop_of_find? find_loop3]; decide +kernel

/-- `__loop3`'s valuation at `x`, slot `s`, the range check's words from `rd`. -/
noncomputable def loop3Val (rd : Reader) (x N : E) (M : ℕ) (cover table : E) (s : ℕ) : Val :=
  setl (Val.ofArgs [x, N, gen ^ M, cover, table]) 5 [gen ^ s, ginvW, gen ^ M * ginvW,
    gen ^ (M - 1 - s), cellAt rd (gen ^ s) 0, cellAt rd (gen ^ (M - 1 - s)) 0, cover * gen ^ s,
    gen ^ s * gen ^ s, gen ^ s * gen ^ s * (gen ^ s * gen ^ s),
    table * (gen ^ s * gen ^ s * (gen ^ s * gen ^ s)), gen, x * gen, x * gen + N, gen, x * gen]

theorem loop3_holds {C : CallRel} (hl : LowDef 16 rd) {x N cover table : E} {M : ℕ}
    (hM : M ≤ 2 ^ 16) {s : ℕ} (hs : s < M) (hmark : LoadHolds rd cover s x)
    (hv : C "verify_lean_xmss" [table * gen ^ (4 * s)] []) (hK : IsInK (x * gen + N))
    (hnext : x * gen + N ≠ 0 → C "__loop3" [x * gen, N, gen ^ M, cover, table] []) :
    Stmt.HoldsList C rd (loop3Val rd x N M cover table s) (Fn.body Data.core33) False
      (fun rs => rs = []) := by
  simp only [show Fn.body Data.core33 = Data.core33.body from rfl, Data.core33.body,
    Stmt.HoldsList, Stmt.Holds, Atom.Holds, List.map_cons, List.map_nil, word_gen, loop3Val]
  b1_look
  simp only [true_and, and_true]
  exact ⟨⟨loadHolds_cellAt_gen hl (by omega), gen_pow_mul_ginv s hs,
      loadHolds_cellAt_gen hl (by omega)⟩,
    by rw [loadHolds_mul_gen_pow, Nat.add_zero]; exact hmark, by rw [gen_pow_four]; exact hv, hK,
    hnext⟩

/-- **`__loop3`, placed**: iteration `c < m` marks slot `sl c` of the leanXMSS region `g^M` of the
coverage table at `cb` with `g^c`, and verifies the claim at `tb·g^(4·sl c)`; the marks are words
of `Lin`, and the claims' signatures verify on every memory holding it; each verification within
`Bx`. -/
theorem loop3_completeAt {κ Bx : ℕ}
    (H : CompleteRelB fs cert κ "verify_lean_xmss" Meaning_verify_lean_xmss Bx)
    (hκ : 16 ≤ κ) {M m cb tb : ℕ} (hM : M ≤ 2 ^ 16) (hm : m < 2 ^ 16) (hm0 : 0 < m) (sl : ℕ → ℕ)
    (hs : ∀ c < m, sl c < M) (Lin : Layout) (hmark : ∀ c < m, CellL Lin (cb + sl c) (gen ^ c))
    (hv : ∀ c < m, ∀ rd, LowDef κ rd → MemL rd Lin →
      Meaning_verify_lean_xmss rd [ofK (gpow tb) * gen ^ (4 * sl c)] []) :
    CompleteAtB fs cert κ "__loop3" Lin [1, gen ^ m, gen ^ M, ofK (gpow cb), ofK (gpow tb)]
      (Returns []) (m * (fs "__loop3" + Bx) + fs "__loop3") := by
  have h := completeAt_loop (fs := fs) (cert := cert) (f := "__loop3") κ Lin
    (fun j => [gen ^ j, gen ^ m, gen ^ M, ofK (gpow cb), ofK (gpow tb)]) m (fun _ => Bx)
    (fun j hj fp mt => ?_) 0 hm0
  · rw [loopSum_const, Nat.sub_zero] at h; simpa using h
  obtain ⟨p1, p2, p3, p4, p5⟩ := loop3_parts
  refine Exists.elim (loopStep_straight (fs := fs) (cert := cert) find_loop3 loop3_isLoop
    core33_split p1 p2 p3 κ Lin _ _ _ _ p4
    [⟨"verify_lean_xmss", true, [ofK (gpow tb) * gen ^ (4 * sl j)], Lin, Returns []⟩] (fun _ => Bx)
    (fun k hk _ => by
      rw [List.mem_singleton] at hk; subst hk
      exact H _ _ Lin fun rd hl hL => hv j hj rd hl hL)
    (fun k hk q hq => by rw [List.mem_singleton] at hk; subst hk; exact hq)
    [gen ^ (j + 1), gen ^ m, gen ^ M, ofK (gpow cb), ofK (gpow tb)] (decide (j + 1 ≠ m)) fp mt
    (fun rd hl hL outs ho => ?_)) fun n ⟨L, hW, hD, hNb, hS⟩ =>
      ⟨n, L, hW, hD, by simpa [kidsBound] using hNb, fun rd hl hL ht hn =>
        hS rd hl hL (fun h => ht (by simp at h; omega)) fun h => hn (by simpa using h)⟩
  match outs, ho with
  | [o], ⟨ho1, _⟩ =>
    obtain ⟨hr1, -⟩ := ho1 rfl
    have hl16 : LowDef 16 rd := hl.mono hκ
    have hsj := hs j hj
    refine ⟨loop3Val rd (gen ^ j) (gen ^ m) M (ofK (gpow cb)) (ofK (gpow tb)) (sl j), ?_,
      loop3_holds (C := fun _ _ _ => True) hl16 hM hsj ((hmark j hj).load hL) trivial
        (isInK_add (isInK_mul (gen_pow_isInK j) (by simpa using gen_pow_isInK 1)) (gen_pow_isInK _))
        (fun _ => trivial), ?_, ?_, ?_, ?_⟩
    · simp only [show Fn.params Data.core33 = [.n 0, .n 1, .n 2, .n 3, .n 4] from rfl,
        List.map_cons, List.map_nil, loop3Val]; b1_look
    · simp only [List.map_cons, List.map_nil, mkCall, CallsMatch, true_and, forall_const, and_true]
      simp only [loop3Val]; b1_look
      exact ⟨by rw [gen_pow_four], hr1.symm⟩
    · simp only [loop3Val]; b1_look
      exact gen_pow_succ_add_ne (by omega) (by omega)
    · simp only [List.map_cons, List.map_nil, loop3Val]; b1_look
      rw [gen_pow_mul_gen]
    · intro q hq
      rw [p5, List.mem_singleton] at hq; subst hq
      simp only [loop3Val]; b1_look
      refine ⟨cb + sl j, ?_, (hmark j hj).region⟩
      rw [ofK_gpow_mul_gen, addr_ofK, Nat.add_zero]

/-! ## `__loop4` -/

/-- `__loop4`'s statements before its return. -/
noncomputable def loop4Pre : List Stmt := (Fn.body Data.core34).dropLast

theorem core34_split : Fn.body Data.core34 = loop4Pre ++ [.ret []] := stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem loop4_parts : loop4Pre.all Stmt.straight = true ∧ loop4Pre.filterMap Stmt.allocSz = [] ∧
    loop4Pre.filterMap Stmt.addrS = [] ∧
    loop4Pre.filterMap Stmt.callS = [(none, "verify_sig_lean_sphincs", [.n 18], [])] ++
      [(some (.n 21), "__loop4", [.n 23, .n 1, .n 2, .n 3, .n 4, .n 5, .n 6], [])] ∧
    loop4Pre.filterMap LeanVM.Guest.B1.Stmt.loadS = [(.n 15, 0)] := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel

theorem loop4_isLoop : coreProgram.loop "__loop4" = true := by
  rw [Program.loop_of_find? find_loop4]; decide +kernel

/-- `__loop4`'s valuation at `x`, offset `s`, the range check's words from `rd`. -/
noncomputable def loop4Val (rd : Reader) (x N : E) (M : ℕ) (cover : E) (Lx : ℕ) (w table : E)
    (s : ℕ) : Val :=
  setl (Val.ofArgs [x, N, gen ^ M, cover, gen ^ Lx, w, table]) 7 [gen ^ s, ginvW,
    gen ^ M * ginvW, gen ^ (M - 1 - s), cellAt rd (gen ^ s) 0, cellAt rd (gen ^ (M - 1 - s)) 0, w * x,
    gen ^ Lx * gen ^ s, cover * (gen ^ Lx * gen ^ s), gen ^ s * gen ^ s,
    gen ^ s * gen ^ s * (gen ^ s * gen ^ s), table * (gen ^ s * gen ^ s * (gen ^ s * gen ^ s)), gen,
    x * gen, x * gen + N, gen, x * gen]

theorem loop4_holds {C : CallRel} (hl : LowDef 16 rd) {x N cover w table : E} {M Lx : ℕ}
    (hM : M ≤ 2 ^ 16) {s : ℕ} (hs : s < M) (hmark : LoadHolds rd cover (Lx + s) (w * x))
    (hv : C "verify_sig_lean_sphincs" [table * gen ^ (4 * s)] []) (hK : IsInK (x * gen + N))
    (hnext : x * gen + N ≠ 0 → C "__loop4" [x * gen, N, gen ^ M, cover, gen ^ Lx, w, table] []) :
    Stmt.HoldsList C rd (loop4Val rd x N M cover Lx w table s) (Fn.body Data.core34) False
      (fun rs => rs = []) := by
  simp only [show Fn.body Data.core34 = Data.core34.body from rfl, Data.core34.body,
    Stmt.HoldsList, Stmt.Holds, Atom.Holds, List.map_cons, List.map_nil, word_gen, loop4Val]
  b1_look
  simp only [true_and, and_true]
  exact ⟨⟨loadHolds_cellAt_gen hl (by omega), gen_pow_mul_ginv s hs,
      loadHolds_cellAt_gen hl (by omega)⟩,
    by rw [← pow_add, loadHolds_mul_gen_pow, Nat.add_zero]; exact hmark,
    by rw [gen_pow_four]; exact hv, hK, hnext⟩

/-- **`__loop4`, placed**: iteration `c < m` marks slot `Lx + sl c` of the coverage table at `cb`
with `w·g^c`, `sl c` in the leanSPHINCS region `g^M`, and verifies the claim at
`tb·g^(4·sl c)`, each verification within `Bs`. -/
theorem loop4_completeAt {κ Bs : ℕ}
    (H : CompleteRelB fs cert κ "verify_sig_lean_sphincs" Meaning_verify_sig_lean_sphincs Bs)
    (hκ : 16 ≤ κ) {M Lx m cb tb : ℕ} {w : E} (hM : M ≤ 2 ^ 16) (hm : m < 2 ^ 16) (hm0 : 0 < m)
    (sl : ℕ → ℕ) (hs : ∀ c < m, sl c < M) (Lin : Layout)
    (hmark : ∀ c < m, CellL Lin (cb + (Lx + sl c)) (w * gen ^ c))
    (hv : ∀ c < m, ∀ rd, LowDef κ rd → MemL rd Lin →
      Meaning_verify_sig_lean_sphincs rd [ofK (gpow tb) * gen ^ (4 * sl c)] []) :
    CompleteAtB fs cert κ "__loop4" Lin
      [1, gen ^ m, gen ^ M, ofK (gpow cb), gen ^ Lx, w, ofK (gpow tb)] (Returns [])
      (m * (fs "__loop4" + Bs) + fs "__loop4") := by
  have h := completeAt_loop (fs := fs) (cert := cert) (f := "__loop4") κ Lin
    (fun j => [gen ^ j, gen ^ m, gen ^ M, ofK (gpow cb), gen ^ Lx, w, ofK (gpow tb)]) m (fun _ => Bs)
    (fun j hj fp mt => ?_) 0 hm0
  · rw [loopSum_const, Nat.sub_zero] at h; simpa using h
  obtain ⟨p1, p2, p3, p4, p5⟩ := loop4_parts
  refine Exists.elim (loopStep_straight (fs := fs) (cert := cert) find_loop4 loop4_isLoop
    core34_split p1 p2 p3 κ Lin _ _ _ _ p4
    [⟨"verify_sig_lean_sphincs", true, [ofK (gpow tb) * gen ^ (4 * sl j)], Lin, Returns []⟩]
    (fun _ => Bs) (fun k hk _ => by
      rw [List.mem_singleton] at hk; subst hk
      exact H _ _ Lin fun rd hl hL => hv j hj rd hl hL)
    (fun k hk q hq => by rw [List.mem_singleton] at hk; subst hk; exact hq)
    [gen ^ (j + 1), gen ^ m, gen ^ M, ofK (gpow cb), gen ^ Lx, w, ofK (gpow tb)] (decide (j + 1 ≠ m))
    fp mt (fun rd hl hL outs ho => ?_)) fun n ⟨L, hW, hD, hNb, hS⟩ =>
      ⟨n, L, hW, hD, by simpa [kidsBound] using hNb, fun rd hl hL ht hn =>
        hS rd hl hL (fun h => ht (by simp at h; omega)) fun h => hn (by simpa using h)⟩
  match outs, ho with
  | [o], ⟨ho1, _⟩ =>
    obtain ⟨hr1, -⟩ := ho1 rfl
    have hl16 : LowDef 16 rd := hl.mono hκ
    have hsj := hs j hj
    have e15 : ofK (gpow cb) * (gen ^ Lx * gen ^ sl j) = ofK (gpow (cb + (Lx + sl j))) := by
      rw [← pow_add, ofK_gpow_mul_gen]
    refine ⟨loop4Val rd (gen ^ j) (gen ^ m) M (ofK (gpow cb)) Lx w (ofK (gpow tb)) (sl j), ?_,
      loop4_holds (C := fun _ _ _ => True) hl16 hM hsj ((hmark j hj).load hL) trivial
        (isInK_add (isInK_mul (gen_pow_isInK j) (by simpa using gen_pow_isInK 1)) (gen_pow_isInK _))
        (fun _ => trivial), ?_, ?_, ?_, ?_⟩
    · simp only [show Fn.params Data.core34 = [.n 0, .n 1, .n 2, .n 3, .n 4, .n 5, .n 6] from rfl,
        List.map_cons, List.map_nil, loop4Val]; b1_look
    · simp only [List.map_cons, List.map_nil, mkCall, CallsMatch, true_and, forall_const, and_true]
      simp only [loop4Val]; b1_look
      exact ⟨by rw [gen_pow_four], hr1.symm⟩
    · simp only [loop4Val]; b1_look
      exact gen_pow_succ_add_ne (by omega) (by omega)
    · simp only [List.map_cons, List.map_nil, loop4Val]; b1_look
      rw [gen_pow_mul_gen]
    · intro q hq
      rw [p5, List.mem_singleton] at hq; subst hq
      simp only [loop4Val]; b1_look
      refine ⟨cb + (Lx + sl j), ?_, (hmark j hj).region⟩
      rw [e15, addr_ofK, Nat.add_zero]

/-! ## `__loop100` -/

/-- `__loop100`'s statements before its return. -/
noncomputable def loop100Pre : List Stmt := (Fn.body Data.core573).dropLast

theorem core573_split : Fn.body Data.core573 = loop100Pre ++ [.ret []] :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem loop100_parts : loop100Pre.all Stmt.straight = true ∧
    loop100Pre.filterMap Stmt.allocSz = [] ∧ loop100Pre.filterMap Stmt.addrS = [] ∧
    loop100Pre.filterMap Stmt.callS =
      [(none, "cover_da_root", [.n 3, .n 4, .n 5, .n 12], [.n 13, .n 14, .n 15, .n 16])] ++
      [(some (.n 19), "__loop100", [.n 21, .n 1, .n 2, .n 3, .n 4, .n 5, .n 6, .n 7], [])] ∧
    loop100Pre.filterMap LeanVM.Guest.B1.Stmt.loadS =
      [(.n 10, 0), (.n 10, 1), (.n 10, 2), (.n 10, 3)] := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel

theorem loop100_isLoop : coreProgram.loop "__loop100" = true := by
  rw [Program.loop_of_find? find_loop100]; decide +kernel

/-- `__loop100`'s valuation at `x`, the root's cells `r0..r3`. -/
noncomputable def loop100Val (x N cda roots dcov dslots base nsub r0 r1 r2 r3 : E) : Val :=
  setl (Val.ofArgs [x, N, cda, roots, dcov, dslots, base, nsub]) 8 [x * x, x * x * (x * x),
    cda * (x * x * (x * x)), base * nsub, base * nsub * x, r0, r1, r2, r3, gen, x * gen, x * gen + N,
    gen, x * gen]

theorem loop100_holds {C : CallRel} {x N cda roots dcov dslots base nsub r0 r1 r2 r3 : E}
    (hcov : C "cover_da_root" [roots, dcov, dslots, base * nsub * x] [r0, r1, r2, r3])
    (hcda : ReadsAt rd (cda * (x * x * (x * x))) [r0, r1, r2, r3]) (hK : IsInK (x * gen + N))
    (hnext : x * gen + N ≠ 0 → C "__loop100" [x * gen, N, cda, roots, dcov, dslots, base, nsub] []) :
    Stmt.HoldsList C rd (loop100Val x N cda roots dcov dslots base nsub r0 r1 r2 r3)
      (Fn.body Data.core573) False (fun rs => rs = []) := by
  simp only [show Fn.body Data.core573 = Data.core573.body from rfl, Data.core573.body,
    Stmt.HoldsList, Stmt.Holds, Atom.Holds, List.map_cons, List.map_nil, word_gen, loop100Val]
  b1_look
  simp only [true_and, and_true]
  exact ⟨hcov, readsAt_getD' hcda (k := 0) (by simp), readsAt_getD' hcda (k := 1) (by simp),
    readsAt_getD' hcda (k := 2) (by simp), readsAt_getD' hcda (k := 3) (by simp), hK, hnext⟩

/-- **`__loop100`, placed**: iteration `c < m` marks its DA slot by `cover_da_root` with
`base·nsub·g^c` in DA slot `sl c`, which returns the root's cells `rt c`, stored at `cdab + 4c`
(words of `Lin`), each `cover_da_root` within `Bc`. -/
theorem loop100_completeAt {κ Bc : ℕ} (H : ∀ i, CompleteRelB fs cert κ "cover_da_root" (CoverPreAt i) Bc)
    {m cdab : ℕ} {roots dcov dslots base nsub : E} (hm : m < 2 ^ 16) (hm0 : 0 < m) (Lin : Layout)
    (rt : ℕ → List E) (hlen : ∀ c < m, (rt c).length = 4) (sl : ℕ → ℕ)
    (hcov : ∀ c < m, ∀ rd, LowDef κ rd → MemL rd Lin →
      CoverPreAt (sl c) rd [roots, dcov, dslots, base * nsub * gen ^ c] (rt c))
    (hcda : ∀ c < m, ∀ k < 4, CellL Lin (cdab + 4 * c + k) ((rt c).getD k 0)) :
    CompleteAtB fs cert κ "__loop100" Lin
      [1, gen ^ m, ofK (gpow cdab), roots, dcov, dslots, base, nsub] (Returns [])
      (m * (fs "__loop100" + Bc) + fs "__loop100") := by
  have h := completeAt_loop (fs := fs) (cert := cert) (f := "__loop100") κ Lin
    (fun j => [gen ^ j, gen ^ m, ofK (gpow cdab), roots, dcov, dslots, base, nsub]) m (fun _ => Bc)
    (fun j hj fp mt => ?_) 0 hm0
  · rw [loopSum_const, Nat.sub_zero] at h; simpa using h
  obtain ⟨p1, p2, p3, p4, p5⟩ := loop100_parts
  refine Exists.elim (loopStep_straight (fs := fs) (cert := cert) find_loop100 loop100_isLoop
    core573_split p1 p2 p3 κ Lin _ _ _ _ p4
    [⟨"cover_da_root", true, [roots, dcov, dslots, base * nsub * gen ^ j], Lin, Returns (rt j)⟩]
    (fun _ => Bc) (fun k hk _ => by
      rw [List.mem_singleton] at hk; subst hk
      exact H (sl j) _ _ Lin fun rd hl hL => hcov j hj rd hl hL)
    (fun k hk q hq => by rw [List.mem_singleton] at hk; subst hk; exact hq)
    [gen ^ (j + 1), gen ^ m, ofK (gpow cdab), roots, dcov, dslots, base, nsub] (decide (j + 1 ≠ m))
    fp mt (fun rd hl hL outs ho => ?_)) fun n ⟨L, hW, hD, hNb, hS⟩ =>
      ⟨n, L, hW, hD, by simpa [kidsBound] using hNb, fun rd hl hL ht hn =>
        hS rd hl hL (fun h => ht (by simp at h; omega)) fun h => hn (by simpa using h)⟩
  have hcj := hcda j hj
  obtain ⟨r0, r1, r2, r3, hr⟩ : ∃ a b c d, rt j = [a, b, c, d] := by
    have := hlen j hj
    match rt j, this with
    | [a, b, c, d], _ => exact ⟨a, b, c, d, rfl⟩
  rw [hr] at hcj ho ⊢
  match outs, ho with
  | [o], ⟨ho1, _⟩ =>
    obtain ⟨hr1, -⟩ := ho1 rfl
    have e10 : ∀ k, ofK (gpow cdab) * (gen ^ j * gen ^ j * (gen ^ j * gen ^ j)) * gen ^ k =
        ofK (gpow (cdab + 4 * j + k)) := fun k => by
      rw [gen_pow_four, ofK_gpow_mul_gen, ofK_gpow_mul_gen]
    have hrd : ReadsAt rd (ofK (gpow cdab) * (gen ^ j * gen ^ j * (gen ^ j * gen ^ j)))
        [r0, r1, r2, r3] := by
      rw [gen_pow_four, ofK_gpow_mul_gen]
      intro k hk
      simp only [List.length_cons, List.length_nil] at hk
      have := (hcj k hk).load hL
      interval_cases k <;> simpa using this
    refine ⟨loop100Val (gen ^ j) (gen ^ m) (ofK (gpow cdab)) roots dcov dslots base nsub r0 r1 r2 r3,
      ?_, loop100_holds (C := fun _ _ _ => True) trivial hrd
        (isInK_add (isInK_mul (gen_pow_isInK j) (by simpa using gen_pow_isInK 1)) (gen_pow_isInK _))
        (fun _ => trivial), ?_, ?_, ?_, ?_⟩
    · simp only [show Fn.params Data.core573 = [.n 0, .n 1, .n 2, .n 3, .n 4, .n 5, .n 6, .n 7]
        from rfl, List.map_cons, List.map_nil, loop100Val]; b1_look
    · simp only [List.map_cons, List.map_nil, mkCall, CallsMatch, true_and, forall_const, and_true]
      simp only [loop100Val]; b1_look
      exact ⟨trivial, hr1.symm⟩
    · simp only [loop100Val]; b1_look
      exact gen_pow_succ_add_ne (by omega) (by omega)
    · simp only [List.map_cons, List.map_nil, loop100Val]; b1_look
      rw [gen_pow_mul_gen]
    · intro q hq
      rw [p5] at hq
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
      have hreg : ∀ k < 4, RegionL Lin (cdab + 4 * j + k) := fun k hk => by
        have := (hcj k hk).region; exact this
      rcases hq with rfl | rfl | rfl | rfl <;> simp only [loop100Val] <;> b1_look
      · exact ⟨_, by rw [← mul_one (ofK _ * _), ← pow_zero gen, e10, addr_ofK], hreg 0 (by omega)⟩
      · exact ⟨_, by rw [← mul_one (ofK _ * _), ← pow_zero gen, e10, addr_ofK], hreg 1 (by omega)⟩
      · exact ⟨_, by rw [← mul_one (ofK _ * _), ← pow_zero gen, e10, addr_ofK], hreg 2 (by omega)⟩
      · exact ⟨_, by rw [← mul_one (ofK _ * _), ← pow_zero gen, e10, addr_ofK], hreg 3 (by omega)⟩

end
end LeanVM.Guest.B1.Main
