/-
  LeanVM.Guest.B1.Tables.Kids.Families

  The leaf callees of `verify_tables` that load through their parameters: their relations load
  from any region holding the runs they read.
-/

module

public import LeanVM.Guest.B1.Tables.Kids.Direct
public import LeanVM.Guest.B1.Eq.Meaning

/-!
# Leaf callees, loading from a region

Each family's specializations pass `dloadCheck` with its per-parameter bounds (the kernel):

* `padding_weight__L{n}` (`n < 29`), `[rows, zeta]`: `zeta`'s `n` words;
* `plus_one_run__L{n}` (`n ≤ 33`), `[out, src]`: `n` words each;
* `index_mle__L{n}` (`n < 34`), `[zeta]`: `n` words;
* `block_selector__L{n}` (`n < 34`), `[sel_bits, zeta1_hi, idxc_hi]`: `n` words each;
* `eq_prefix_run__L{n}` (`n ≤ 40`), `[chain, seed, a, b1]`: the chain's `n + 1`, `a`'s and
  `b1`'s `n`;
* `sel_partial_nibble__L{w}` (`w < 4`), `[eq_out, g_out, z, z1, gs]`: `2^(w+1) - 2`, `2^w` (none
  at `w = 0`), and `w` each;
* `sumcheck_round4`, `[rec, cur, claim]`: the record's `12` words and the cursor's `3`.
-/

namespace LeanVM.Guest.B1.Tables

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Memory

@[expose] public section

theorem pw_dload : ∀ n < 29, dloadCheck (lName "padding_weight" n) [0, n] = true := by
  decide +kernel

theorem por_dload : ∀ n < 34, dloadCheck (plusOneRunNames.getD n "") [n, n] = true := by
  decide +kernel

theorem im_dload : ∀ n < 34, dloadCheck (lName "index_mle" n) [n] = true := by decide +kernel

theorem bs_dload : ∀ n < 34, dloadCheck (lName "block_selector" n) [n, n, n] = true := by
  decide +kernel

theorem epr_dload : ∀ n < 41, dloadCheck (eqPrefixRunNames.getD n "") [n + 1, 0, n, n] = true := by
  decide +kernel

/-- `sel_partial_nibble__L{w}`'s runs: the eq levels, the `g` table, the `w` coordinates,
complements and shares. -/
def spnB (w : ℕ) : List ℕ := [2 ^ (w + 1) - 2, if w = 0 then 0 else 2 ^ w, w, w, w]

theorem spn_dload : ∀ w < 4, dloadCheck (lName "sel_partial_nibble" w) (spnB w) = true := by
  decide +kernel

theorem sr4_dload : dloadCheck "sumcheck_round4" [12, 3, 0] = true := by decide +kernel

section
variable {rd : Reader} {R : ℕ → Prop}

theorem padding_weight_relIn {n : ℕ} (hn : n < 29) {rows zeta : E} {rets : List E}
    (hz : PtrIn R zeta n) (h : coreProgram.Rel rd (lName "padding_weight" n) [rows, zeta] rets) :
    coreProgram.RelIn rd R (lName "padding_weight" n) [rows, zeta] rets :=
  relIn_of_dload (pw_dload n hn) (fun p hp ↦ by
    simp only [List.length_cons, List.length_nil] at hp
    interval_cases p
    · exact fun h ↦ absurd h (by simp)
    · exact fun _ ↦ hz) h

theorem plus_one_run_relIn {n : ℕ} (hn : n ≤ 33) {out src : E} {rets : List E}
    (ho : PtrIn R out n) (hs : PtrIn R src n)
    (h : coreProgram.Rel rd (plusOneRunNames.getD n "") [out, src] rets) :
    coreProgram.RelIn rd R (plusOneRunNames.getD n "") [out, src] rets :=
  relIn_of_dload (por_dload n (by omega)) (fun p hp ↦ by
    simp only [List.length_cons, List.length_nil] at hp
    interval_cases p
    · exact fun _ ↦ ho
    · exact fun _ ↦ hs) h

theorem index_mle_relIn {n : ℕ} (hn : n < 34) {zeta : E} {rets : List E} (hz : PtrIn R zeta n)
    (h : coreProgram.Rel rd (lName "index_mle" n) [zeta] rets) :
    coreProgram.RelIn rd R (lName "index_mle" n) [zeta] rets :=
  relIn_of_dload (im_dload n hn) (fun p hp ↦ by
    simp only [List.length_cons, List.length_nil] at hp
    interval_cases p
    exact fun _ ↦ hz) h

theorem block_selector_relIn {n : ℕ} (hn : n < 34) {sb z1 ic : E} {rets : List E}
    (hsb : PtrIn R sb n) (hz1 : PtrIn R z1 n) (hic : PtrIn R ic n)
    (h : coreProgram.Rel rd (lName "block_selector" n) [sb, z1, ic] rets) :
    coreProgram.RelIn rd R (lName "block_selector" n) [sb, z1, ic] rets :=
  relIn_of_dload (bs_dload n hn) (fun p hp ↦ by
    simp only [List.length_cons, List.length_nil] at hp
    interval_cases p
    · exact fun _ ↦ hsb
    · exact fun _ ↦ hz1
    · exact fun _ ↦ hic) h

theorem eq_prefix_run_relIn {n : ℕ} (hn : n ≤ 40) {chain seed a b1 : E} {rets : List E}
    (hc : PtrIn R chain (n + 1)) (ha : PtrIn R a n) (hb : PtrIn R b1 n)
    (h : coreProgram.Rel rd (eqPrefixRunNames.getD n "") [chain, seed, a, b1] rets) :
    coreProgram.RelIn rd R (eqPrefixRunNames.getD n "") [chain, seed, a, b1] rets :=
  relIn_of_dload (epr_dload n (by omega)) (fun p hp ↦ by
    simp only [List.length_cons, List.length_nil] at hp
    interval_cases p
    · exact fun _ ↦ hc
    · exact fun h ↦ absurd h (by simp)
    · exact fun _ ↦ ha
    · exact fun _ ↦ hb) h

theorem sel_partial_nibble_relIn {w : ℕ} (hw : w < 4) {eqo go z z1 gs : E} {rets : List E}
    (he : PtrIn R eqo (2 ^ (w + 1) - 2)) (hg : 0 < w → PtrIn R go (2 ^ w)) (hz : PtrIn R z w)
    (hz1 : PtrIn R z1 w) (hgs : PtrIn R gs w)
    (h : coreProgram.Rel rd (lName "sel_partial_nibble" w) [eqo, go, z, z1, gs] rets) :
    coreProgram.RelIn rd R (lName "sel_partial_nibble" w) [eqo, go, z, z1, gs] rets :=
  relIn_of_dload (spn_dload w hw) (fun p hp ↦ by
    simp only [spnB, List.length_cons, List.length_nil] at hp
    interval_cases p
    · exact fun _ ↦ he
    · by_cases h0 : w = 0
      · simp only [spnB, h0, ↓reduceIte]; exact fun h ↦ absurd h (by simp)
      · simp only [spnB, h0, ↓reduceIte]; exact fun _ ↦ hg (by omega)
    · exact fun _ ↦ hz
    · exact fun _ ↦ hz1
    · exact fun _ ↦ hgs) h

theorem sumcheck_round4_relIn {rc cur claim : E} {rets : List E} (hr : PtrIn R rc 12)
    (hc : PtrIn R cur 3) (h : coreProgram.Rel rd "sumcheck_round4" [rc, cur, claim] rets) :
    coreProgram.RelIn rd R "sumcheck_round4" [rc, cur, claim] rets :=
  relIn_of_dload sr4_dload (fun p hp ↦ by
    simp only [List.length_cons, List.length_nil] at hp
    interval_cases p
    · exact fun _ ↦ hr
    · exact fun _ ↦ hc
    · exact fun h ↦ absurd h (by simp)) h

end

end
end LeanVM.Guest.B1.Tables
