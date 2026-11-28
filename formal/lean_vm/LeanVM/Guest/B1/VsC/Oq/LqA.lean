/-
  LeanVM.Guest.B1.VsC.Oq.LqA

  `level_queries__L…` completes placed (`LqA`), from its honest cap and flags.
-/

module

public import LeanVM.Guest.B1.VsC.Oq.LqChecks
public import LeanVM.Guest.B1.VsC.Oq.Table
public import LeanVM.Guest.B1.Whir.HelperAll
public import LeanVM.Guest.B1.VsC.LrA

/-!
# `level_queries`, placed

`level_queries__L{q}_…` on `[λ, λ⁻¹, coefs, hs, positions, win_ptrs]` allocates its cap (`4·2^cd`
words at its cursor `c`) and flags (`2^cd` after them), hints both (`merkle_caps`,
`merkle_cap_active`, heap hints into its own words), checks the cap to its root
(`verify_merkle_cap__L{cd}`, `vmcA`), runs its queries (`opening_queries`, `oqA_all`) on the cap's
leaves `cap·g^(2^(cd+1))` and their parents' flags `flags·g^(2^(cd-1))`, and returns the root's
halves, the queries' chain and `λ^q`.

* `CapOk cd capW flW root`: what `verify_merkle_cap` asks of the cap's cells and flags.
* `LqCall`: a call's honest data (the cap, the flags, the root, the queries'); `LqCall.Static`, its
  static facts (each query's climb at its cap leaf, its parent flagged), `.Reg`, `.Mem`, `.pops`.
* `LqA`, `lqA_complete'`: one specialization, by `callAtA_node` on the forward evaluation of its
  straight body (it loads nothing); `lqA_all`: every `lqTable` entry.
-/

namespace LeanVM.Guest.B1.VsC

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Memory LeanVM.Guest.B1
open LeanVM.Guest.Complete LeanVM.Guest.Value LeanVM.Guest.B1.Whir LeanVM.Guest.B1.Fwd
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Prover.Exec (allocBase)

@[expose] public section

/-- **The cap's cells `capW` and flags `flW` check to `root`**: the flags in `K`, the root and
every flagged node hashing its children, an unflagged node's children unflagged, cells `2, 3` the
root's halves. -/
def CapOk (cd : ℕ) (capW flW : List E) (root : Digest) : Prop :=
  (∀ k, 2 ≤ k → k < 2 ^ cd → IsInK (flW.getD k 0)) ∧
    (∀ k, 1 ≤ k → k < 2 ^ cd → (k = 1 ∨ flW.getD k 0 ≠ 0) →
      HashesPair (capW.getD (4 * k) 0) (capW.getD (4 * k + 1) 0) (capW.getD (4 * k + 2) 0)
        (capW.getD (4 * k + 3) 0) (capW.getD (2 * k) 0) (capW.getD (2 * k + 1) 0)) ∧
    (∀ k, 2 ≤ k → 2 * k < 2 ^ cd → flW.getD k 0 = 0 → flW.getD (2 * k) 0 = 0 ∧ flW.getD (2 * k + 1) 0 = 0) ∧
    (capW.getD 2 0, capW.getD 3 0) = digestHalves root

/-- **A `level_queries` call's honest data.** -/
structure LqCall where
  lam : E
  root : Digest
  capW : List E
  flW : List E
  rounds : List FoldRound
  hsv : List E
  ws : ℕ → QW
  wp : ℕ → ℕ
  icf : ℕ
  ihs : ℕ
  ipos : ℕ
  iptr : ℕ

namespace LqCall

variable (l : LqCall)

/-- The call's arguments. -/
def args : List E := [l.lam, l.lam⁻¹, ptrAt l.icf, ptrAt l.ihs, ptrAt l.ipos, ptrAt l.iptr]

/-- Its `opening_queries` call at its cursor `c`, `λ⁻¹`'s place taken by `li`. -/
def oqG (s : Oq) (q base cd c : ℕ) (li : E) : OqCall :=
  ⟨s, cd, lqIters q base, lqOdd q base, l.rounds, l.hsv, l.ws, l.wp, li, c + 2 ^ (cd + 1),
    c + 4 * 2 ^ cd + 2 ^ (cd - 1), l.icf, l.ihs, l.ipos, l.iptr⟩

/-- Its `opening_queries` call at its cursor `c`. -/
def oq (s : Oq) (q base cd c : ℕ) : OqCall :=
  ⟨s, cd, lqIters q base, lqOdd q base, l.rounds, l.hsv, l.ws, l.wp, l.lam⁻¹, c + 2 ^ (cd + 1),
    c + 4 * 2 ^ cd + 2 ^ (cd - 1), l.icf, l.ihs, l.ipos, l.iptr⟩

/-- **Its static facts**: the cap and flags checking to the root, the rounds, the final
coefficients, and each query's position, row, siblings, final fold, its climb at its cap leaf
and its parent flagged. -/
def Static (q cd : ℕ) (s : Oq) : Prop :=
  l.capW.length = 4 * 2 ^ cd ∧ l.flW.length = 2 ^ cd ∧ CapOk cd l.capW l.flW l.root ∧
    l.rounds.length = s.folds ∧ (s.final = 1 → l.hsv.length = s.nHs) ∧
    ∀ k < q, (l.ws k).1 < 2 ^ (s.pd + cd) ∧ (l.ws k).2.1.length = rowLen s.base s.folds ∧
      (l.ws k).2.2.length = s.pd ∧
      (s.final = 1 → foldRow (lanesOf s.base (l.ws k).2.1) (K.ofBits (l.ws k).1) l.rounds =
        novelSum l.hsv (wsChain (s.vs.map K.ofBits) (eOfNat (l.ws k).1)) s.nHs s.hsBits) ∧
      l.capW.getD (2 ^ (cd + 1) + 2 * ((l.ws k).1 / 2 ^ s.pd)) 0 =
        (digestHalves (climbD (merkleLeafDigest (l.ws k).2.1) (l.ws k).1 (l.ws k).2.2)).1 ∧
      l.capW.getD (2 ^ (cd + 1) + 2 * ((l.ws k).1 / 2 ^ s.pd) + 1) 0 =
        (digestHalves (climbD (merkleLeafDigest (l.ws k).2.1) (l.ws k).1 (l.ws k).2.2)).2 ∧
      l.flW.getD (2 ^ (cd - 1) + (l.ws k).1 / 2 ^ (s.pd + 1)) 0 = 1

/-- **The region it reads**: the rounds, the final coefficients, the windows, positions and
pointers. -/
def Reg (q : ℕ) (s : Oq) (R : ℕ → Prop) : Prop :=
  (∀ off < 2 * s.folds, R (l.icf + off)) ∧ (s.final = 1 → ∀ off < s.nHs, R (l.ihs + off)) ∧
    (∀ k < q, ∀ off < oqNpw s + 2, R (l.wp k + off)) ∧ ∀ k < q, R (l.ipos + k) ∧ R (l.iptr + k)

/-- **What the memory holds**: the rounds, the final coefficients, the positions, pointers and
windows. -/
def Mem (q cd : ℕ) (s : Oq) (rd : Reader) : Prop :=
  RoundsAt rd (ptrAt l.icf) l.rounds ∧ (s.final = 1 → WordsAt rd (ptrAt l.ihs) l.hsv) ∧
    ∀ k < q, LoadHolds rd (ptrAt l.ipos) k (eOfNat (l.ws k).1) ∧ LoadHolds rd (ptrAt l.iptr) k (ptrAt (l.wp k)) ∧
      ∀ i < qwN (s.pd + cd) cd, LoadHolds rd (ptrAt (l.wp k)) i (gen ^ qwVal (s.pd + cd) cd (l.ws k).1 i)

/-- Its entries: the cap's, the flags', its queries' in order. -/
def pops (q : ℕ) (s : Oq) : List Pop :=
  [("merkle_caps", l.capW), ("merkle_cap_active", l.flW)] ++ (List.range q).flatMap fun k => oqQE s (l.ws k)

end LqCall

variable (fs : String → ℕ) (al : String → Bool) (cert : String → V → ℕ)

/-- **`level_queries__L…` completes placed**, its queries of shape `s`. -/
def LqA (kd : ℕ) (name : String) (q base cd : ℕ) (s : Oq) : Prop :=
  ∀ (l : LqCall) (R : ℕ → Prop), l.lam ≠ 0 → l.Static q cd s → l.Reg q s R →
    ∀ fp c, fp + fs name ≤ c → ∃ e, CallAtA fs al cert kd name l.args
      [(digestHalves l.root).1, (digestHalves l.root).2, (l.oq s q base cd 0).mret, l.lam ^ q] R
      (fun _ => False) (fun _ => True) (l.Mem q cd s)
      (fun rd t => t.pops coreProgram rd = l.pops q s ∧ t.Every (ExactAt coreProgram rd)) (fs name) fp c e

/-- **`level_queries__L…` completes placed at any second argument `li`**, `opening_queries`
chaining with `li` for `λ⁻¹`. -/
def LqAG (kd : ℕ) (name : String) (q base cd : ℕ) (s : Oq) : Prop :=
  ∀ (l : LqCall) (li : E) (R : ℕ → Prop), l.Static q cd s → l.Reg q s R →
    ∀ fp c, fp + fs name ≤ c → ∃ e, CallAtA fs al cert kd name
      [l.lam, li, ptrAt l.icf, ptrAt l.ihs, ptrAt l.ipos, ptrAt l.iptr]
      [(digestHalves l.root).1, (digestHalves l.root).2, (l.oqG s q base cd 0 li).mret, l.lam ^ q] R
      (fun _ => False) (fun _ => True) (l.Mem q cd s)
      (fun rd t => t.pops coreProgram rd = l.pops q s ∧ t.Every (ExactAt coreProgram rd)) (fs name) fp c e

/-- **`LqAG` with its end bounded**: every frame at most `F`, within `(q + 2)·(3F + 2048)` of its
cursor. -/
def LqAGE (kd : ℕ) (name : String) (q base cd : ℕ) (s : Oq) : Prop :=
  ∀ (l : LqCall) (li : E) (R : ℕ → Prop), l.Static q cd s → l.Reg q s R →
    ∀ fp c, fp + fs name ≤ c → ∃ e, (∀ F, (∀ f, fs f ≤ F) → e ≤ c + (q + 2) * (3 * F + 2048)) ∧
      CallAtA fs al cert kd name
      [l.lam, li, ptrAt l.icf, ptrAt l.ihs, ptrAt l.ipos, ptrAt l.iptr]
      [(digestHalves l.root).1, (digestHalves l.root).2, (l.oqG s q base cd 0 li).mret, l.lam ^ q] R
      (fun _ => False) (fun _ => True) (l.Mem q cd s)
      (fun rd t => t.pops coreProgram rd = l.pops q s ∧ t.Every (ExactAt coreProgram rd)) (fs name) fp c e

variable {fs al cert} in
/-- The bounded form gives `LqAG`. -/
theorem LqAGE.toG {kd : ℕ} {name : String} {q base cd : ℕ} {s : Oq} (h : LqAGE fs al cert kd name q base cd s) :
    LqAG fs al cert kd name q base cd s := by
  intro l li R h1 h2 fp c hfc
  obtain ⟨e, -, he⟩ := h l li R h1 h2 fp c hfc
  exact ⟨e, he⟩

variable {fs al cert} in
/-- `LqAG` gives `LqA`. -/
theorem lqAG_of_lqA {kd : ℕ} {name : String} {q base cd : ℕ} {s : Oq}
    (h : LqAG fs al cert kd name q base cd s) : LqA fs al cert kd name q base cd s :=
  fun l R _ hs hr fp c hc => h l l.lam⁻¹ R hs hr fp c hc

/-- `LqAG` at every entry of `lqTable`. -/
def LqAllG (kd : ℕ) : Prop :=
  ∀ (name : String) (q base folds leaf d cd mu nhs hbits fin : ℕ),
    (name, q, base, folds, leaf, d, cd, mu, nhs, hbits, fin) ∈ lqTable →
      LqAG fs al cert kd name q base cd (oqShapeK (oqKey base folds leaf (d - cd) mu nhs hbits fin)).oq

/-- `LqAGE` at every entry of `lqTable`. -/
def LqAllGE (kd : ℕ) : Prop :=
  ∀ (name : String) (q base folds leaf d cd mu nhs hbits fin : ℕ),
    (name, q, base, folds, leaf, d, cd, mu, nhs, hbits, fin) ∈ lqTable →
      LqAGE fs al cert kd name q base cd (oqShapeK (oqKey base folds leaf (d - cd) mu nhs hbits fin)).oq

variable {fs al cert}

/-! ## Pieces -/

theorem lq_count (q base : ℕ) : oqCount (lqOdd q base) base (lqIters q base) = q := by
  unfold oqCount lqOdd lqIters
  split <;> omega

theorem osPowSteps_noWit' (x : ℕ) : ∀ (ds : List Bool) (acc k : ℕ), noWit (osPowSteps x ds acc k).1 = true
  | [], _, _ => rfl
  | d :: ds, acc, k => by
    unfold osPowSteps
    split
    · show noWit ([osMul k acc acc, osMul (k + 1) k x] ++ _) = true
      rw [noWit_append, osPowSteps_noWit' x ds]; rfl
    · show noWit ([osMul k acc acc] ++ _) = true
      rw [noWit_append, osPowSteps_noWit' x ds]; rfl

/-- The cap's and the flags' entries: `4·2^cd` cells at the cap's pointer `.n 7`, `2^cd` at the flags' `.n 9`. -/
def capPops (rd : Reader) (σ : Val) (cd : ℕ) : List Pop :=
  [("merkle_caps", Dest.words rd σ (.heap (.n 7) 0 (4 * 2 ^ cd))),
    ("merkle_cap_active", Dest.words rd σ (.heap (.n 9) 0 (2 ^ cd)))]

/-- **`level_queries` pops the cap and its flags, then its callees' entries.** -/
theorem lq_node_pops {rd : Reader} {P : Core.Program} {name : String} {fn : Fn} (hf : P.find? name = some fn)
    {q base folds leaf d cd mu nhs hbits fin : ℕ} (hb : fn.body = lqBody q base folds leaf d cd mu nhs hbits fin)
    (τ : Val) (bufs : List ℕ) {kids : List Tree} {kc ko : List Pop} (hk : Tree.popsKids P rd kids = [kc, ko]) :
    (Memory.Tree.node name τ bufs kids).pops P rd = capPops rd τ cd ++ kc ++ ko := by
  let iters := if base = 1 then q / 2 else q
  let odd := if base = 1 then q % 2 else 0
  let pw := osPowSteps 0 (osPowDigits q) 0 22
  let k := 22 + osPowLen q
  have hx : SplicePops rd τ (osHeap (4 * 2 ^ cd) 6 ++
      [.atom (.hint (.witness "merkle_caps" (.heap (.n 7) 0 (4 * 2 ^ cd))))] ++
      osHeap (2 ^ cd) 8 ++
      [.atom (.hint (.witness "merkle_cap_active" (.heap (.n 9) 0 (2 ^ cd))))] ++
      [.call ("verify_merkle_cap__L" ++ natStr cd) [.n 7, .n 9] [.n 10, .n 11]] ++
      [osCst 12 (gw (2 ^ (cd + 1))), osMul 13 7 12, osCst 14 (gw (2 ^ (cd - 1))), osMul 15 9 14,
        osCst 16 (gw iters), osCst 17 (gw odd)] ++
      [.call (oqName base folds leaf (d - cd) mu nhs hbits fin)
        [.n 13, .n 15, .n 1, .n 2, .n 3, .n 4, .n 5, .n 16, .n 17] [.n 18]] ++
      ([osCp 19 10, osCp 20 11, osCp 21 18] ++ pw.1 ++ [osCp k pw.2]))
      (Tree.popsKids P rd kids) (capPops rd τ cd ++ kc ++ ko) := by
    rw [hk]
    have h : SplicePops rd τ (((((((osHeap (4 * 2 ^ cd) 6 ++
        [.atom (.hint (.witness "merkle_caps" (.heap (.n 7) 0 (4 * 2 ^ cd))))]) ++
        osHeap (2 ^ cd) 8) ++ [.atom (.hint (.witness "merkle_cap_active" (.heap (.n 9) 0 (2 ^ cd))))]) ++
        [.call ("verify_merkle_cap__L" ++ natStr cd) [.n 7, .n 9] [.n 10, .n 11]]) ++
        [osCst 12 (gw (2 ^ (cd + 1))), osMul 13 7 12, osCst 14 (gw (2 ^ (cd - 1))), osMul 15 9 14,
          osCst 16 (gw iters), osCst 17 (gw odd)]) ++
        [.call (oqName base folds leaf (d - cd) mu nhs hbits fin)
          [.n 13, .n 15, .n 1, .n 2, .n 3, .n 4, .n 5, .n 16, .n 17] [.n 18]]) ++
        ([osCp 19 10, osCp 20 11, osCp 21 18] ++ pw.1 ++ [osCp k pw.2]))
        ([] ++ [] ++ [] ++ [] ++ [kc] ++ [] ++ [ko] ++ [])
        ([] ++ [("merkle_caps", Dest.words rd τ (.heap (.n 7) 0 (4 * 2 ^ cd)))] ++ [] ++
          [("merkle_cap_active", Dest.words rd τ (.heap (.n 9) 0 (2 ^ cd)))] ++ kc ++ [] ++ ko ++ []) :=
      (((((((SplicePops.of_fallPops (fallPops_noWit τ rfl)).append (SplicePops.of_fallPops (FallPops.atom _))).append
        (SplicePops.of_fallPops (fallPops_noWit τ rfl))).append (SplicePops.of_fallPops (FallPops.atom _))).append
        (SplicePops.call _ _ _ kc)).append (SplicePops.of_fallPops (fallPops_noWit τ rfl))).append
        (SplicePops.call _ _ _ ko)).append (SplicePops.of_fallPops (fallPops_noWit τ (by
          rw [noWit_append, noWit_append, osPowSteps_noWit']; rfl)))
    have h' := SplicePops.congr_pops (SplicePops.congr_ks h (ks' := [kc, ko]) (by simp))
      (q := capPops rd τ cd ++ kc ++ ko) (by simp [capPops])
    simpa only [List.append_assoc] using h'
  obtain ⟨es, -, he⟩ := oqPops_of_splice (bufs := bufs) hf (ys := [.ret [.n 19, .n 20, .n 21, .n k]])
    (by rw [hb, lqBody]; simp [List.append_assoc]; exact ⟨rfl, rfl, rfl⟩) hx (es := [])
    (vs := [.n 19, .n 20, .n 21, .n k])
    (by simp [walk, walk1, Out.seq]) rfl
  rw [he]; simp [evPops]

/-- The memory's words through a pointer are the run there. -/
theorem dest_words_eq {rd : Reader} {σ : Val} {p : V} {a : ℕ} {W : List E} (hp : σ p = ptrAt a)
    (h : ReadsAt rd (ptrAt a) W) : Dest.words rd σ (.heap p 0 W.length) = W := by
  refine List.ext_getElem (by simp [Dest.words]) fun k h1 h2 => ?_
  have hl := (h k h2).2
  simp only [Dest.words, List.getElem_map, List.getElem_range, Nat.zero_add, hp]
  rw [hl]; rfl

theorem cap_bounds {q pd cd : ℕ} (hcd : 1 ≤ cd) (hq : q < 2 ^ (pd + cd)) :
    q / 2 ^ pd < 2 ^ cd ∧ q / 2 ^ (pd + 1) < 2 ^ (cd - 1) ∧
      4 * (q / 2 ^ (pd + 1)) + (if q.testBit pd then 2 else 0) = 2 * (q / 2 ^ pd) := by
  have h1 : q / 2 ^ pd < 2 ^ cd := by
    rw [Nat.div_lt_iff_lt_mul (by positivity), ← pow_add, Nat.add_comm]; exact hq
  have e2 : q / 2 ^ (pd + 1) = q / 2 ^ pd / 2 := by rw [pow_succ, Nat.div_div_eq_div_mul]
  have hc : 2 ^ cd = 2 * 2 ^ (cd - 1) := by rw [← pow_succ']; congr 1; omega
  refine ⟨h1, by rw [e2]; omega, ?_⟩
  rw [e2, Nat.testBit_eq_decide_div_mod_eq]
  by_cases hb : q / 2 ^ pd % 2 = 1 <;> simp [hb] <;> omega

end
end LeanVM.Guest.B1.VsC
