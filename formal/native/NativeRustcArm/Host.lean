module

public import Kraken.AArch64.OmniSemantics
public import Kraken.Data.List.Infix

/-!
# A program laid out in memory, for AArch64

Kraken's x86-64 reasons about a program through `Host` (`Kraken/X64/WP/Host.lean`): a program and a
layout in which two directives at one address are at one offset. Kraken has no such module for
AArch64; this is its transcription to Kraken's AArch64 `Executable`, with the one-directive step
`Host.eventually_of_interp` (Kraken's x86-64 `WP/Basic.lean`).
-/

namespace NativeRustcArm

private theorem takeWhile_eq_take_of {α : Type _} {p : α → Bool} {l : List α} {n : Nat}
    (hprior : ∀ k, k < n → ∀ c, l[k]? = some c → p c = true)
    (hhead : ∀ c, l[n]? = some c → p c = false) :
    l.takeWhile p = l.take n := by
  rw [List.takeWhile_eq_take_findIdx_not]
  by_cases hn : n < l.length
  · rw [(List.findIdx_eq hn).mpr ⟨by simp [hhead _ (List.getElem?_eq_getElem hn)],
      fun k hk => by simp [hprior k hk _ (List.getElem?_eq_getElem (by omega))]⟩]
  · rw [(List.take_of_length_le (Nat.le_of_not_lt hn) : l.take n = l), List.take_of_length_le]
    refine Nat.le_of_eq (List.findIdx_eq_length.mpr fun x hx => ?_).symm
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hx
    simp [hprior i (by omega) _ (List.getElem?_eq_getElem hi)]

private theorem exists_least_le {P : Nat → Prop} {n : Nat} (h : P n) :
    ∃ j, j ≤ n ∧ P j ∧ ∀ k, k < j → ¬P k := by
  induction n using Nat.strongRecOn with
  | ind n ih => grind

/-- A program and its layout, in which two directives at the same address are at the same offset. -/
public class Host where
  /-- The program. -/
  prog : Program
  /-- Its layout. -/
  layout : Layout
  /-- Two directives at the same address have the same offset in the executable. -/
  addr_determines_offset : ∀ j k, (layout.apply prog).addrOf j = (layout.apply prog).addrOf k →
    (layout.apply prog).sizeBefore j = (layout.apply prog).sizeBefore k

public instance [Host] : Layout := Host.layout

/-- The laid out program. -/
@[expose] public def Host.exe [Host] : Executable := Host.layout.apply Host.prog

/-- The address of the program's `k`th directive. -/
@[expose] public def Host.addrOf [Host] (k : Nat) : Int64 := Host.exe.addrOf k

public instance [Host] : Labels := Executable.labels Host.exe

public theorem Host.sizeBefore_eq_of_addrOf_eq [Host] {j k : Nat}
    (h : Host.addrOf j = Host.addrOf k) : Host.exe.sizeBefore j = Host.exe.sizeBefore k :=
  Host.addr_determines_offset j k h

public theorem Layout.apply_getElem? [layout : Layout] (p : Program) (i : Nat) :
    (layout p).program[i]? = (p[i]?).map (fun d => {directive := d, size := layout.size d i}) := by
  simp [Kraken.Layout.apply, List.getElem?_mapIdx]

public theorem Host.exe_getElem? [Host] (i : Nat) :
    Host.exe.program[i]? =
      Host.prog[i]?.map (fun d => {directive := d, size := Host.layout.size d i}) :=
  Layout.apply_getElem? _ _

public theorem Host.addrOf_succ [Host] {k : Nat} {d : Directive} (hd : Host.prog[k]? = some d) :
    Host.addrOf (k + 1) = Host.addrOf k + .ofNat (Host.layout.size d k) :=
  Kraken.Executable.addrOf_succ _ (c := {directive := d, size := Host.layout.size d k})
    (by rw [Host.exe_getElem?, hd]; rfl)

section
variable [Host]

public theorem Host.directivesAtAddress_addrOf {k : Nat} {c : Kraken.Sized Directive}
    (hc : Host.exe.program[k]? = some c) (hz : 0 < c.size) :
    ∃ pre : List (Kraken.Sized Directive),
      Host.exe.directivesAtAddress (Host.addrOf k) = pre ++ [c] ∧ ∀ c ∈ pre, c.size = 0 := by
  obtain ⟨j, hjk, hj, hmin⟩ :=
    exists_least_le (P := fun i => Host.exe.addrOf i = Host.exe.addrOf k) rfl
  have hsize := Host.sizeBefore_eq_of_addrOf_eq hj
  have hpre : ∀ c ∈ (Host.exe.program.drop j).take (k - j), c.size = 0 := by
    have := Host.exe.sizeBefore_add j (k - j)
    rw [Nat.add_sub_cancel' hjk] at this
    have hsum : (((Host.exe.program.drop j).take (k - j)).map (·.size)).sum = 0 := by omega
    exact fun c hc => List.sum_eq_zero_iff_forall_eq_nat.mp hsum _ (List.mem_map_of_mem hc)
  have haddr : ∀ m, j ≤ m → m ≤ k → Host.exe.addrOf m = Host.exe.addrOf k := fun m hjm hmk => by
    grind [Kraken.Executable.addrOf, Host.exe.sizeBefore_mono hjm, Host.exe.sizeBefore_mono hmk]
  have hnext : Host.exe.addrOf (k + 1) ≠ Host.exe.addrOf k := fun h => by
    grind [Host.sizeBefore_eq_of_addrOf_eq h]
  refine ⟨(Host.exe.program.drop j).take (k - j), ?_, hpre⟩
  show ((Host.exe.withAddresses.dropWhile
    (·.addr ≠ Host.exe.addrOf k)).takeWhile (·.addr = Host.exe.addrOf k)).map (·.toSized) = _
  rw [Kraken.Executable.withAddresses_dropWhile_addrOf _ j k hj hmin,
    takeWhile_eq_take_of (n := k - j + 1)]
  · rw [List.map_take, List.map_drop, Kraken.Executable.withAddresses_map_snd, List.take_add_one,
      List.getElem?_drop, Nat.add_sub_cancel' hjk, hc]
    rfl
  · intro m hm c hc
    have := haddr (j + m) (by omega) (by omega)
    grind [Kraken.Executable.getElem?_withAddresses_eq]
  · intro c hc
    grind [Kraken.Executable.getElem?_withAddresses_eq]

/-- One directive of the program, run from its address: the machine inevitably reaches what the
directive's semantics leads to. -/
public theorem Host.eventually_of_interp {k : Nat} {d : Directive} {p : Program}
    (hdp : (d :: p).IsInfixAt Host.prog k) {post : @Post MachineState} {s : MachineData}
    (h : (d.interp s ⟨Host.addrOf k, Host.addrOf (k + 1)⟩
      (fun s' => .done ⟨s', Host.addrOf (k + 1)⟩) (fun a s' => .done ⟨s', a⟩)).All post) :
    Eventually (step1 Host.exe) post ⟨s, Host.addrOf k⟩ := by
  have hd : Host.exe.program[k]? =
      some {directive := d, size := Host.layout.size d k : Kraken.Sized Directive} := by
    rw [Host.exe_getElem?, hdp.cons.1]
    rfl
  rw [Host.addrOf_succ hdp.cons.1] at h
  match hsize : Host.layout.size d k with
  | 0 =>
    apply Eventually.done
    simpa [hsize, inert_of_size_zero hsize, Effects.All] using h
  | _ + 1 =>
    refine Eventually.step _ post ?_ fun _ hb => Eventually.done _ hb
    obtain ⟨pre, hat, hpre⟩ := Host.directivesAtAddress_addrOf hd <| by grind only
    have hmem : ∀ c ∈ pre, c ∈ Host.exe.program := fun c hc =>
      Kraken.Executable.mem_of_mem_directivesAtAddress (hat ▸ List.mem_append_left _ hc)
    unfold step1 Executable.step
    change (Directives.interp (Host.exe.directivesAtAddress (Host.addrOf k)) s (Host.addrOf k)
      _).All post
    rw [hat]
    clear hat
    induction pre with
    | nil => simpa [Directives.interp] using h
    | cons c pre ih =>
      obtain ⟨m, hm⟩ := List.mem_iff_getElem?.mp (hmem c List.mem_cons_self)
      obtain ⟨d', _, rfl⟩ := Option.map_eq_some_iff.mp (Host.exe_getElem? m ▸ hm)
      have hz0 : Host.layout.size d' m = 0 := hpre _ List.mem_cons_self
      simp only [hz0, List.cons_append, Directives.interp, Int64.reduceOfNat, Int64.add_zero,
        inert_of_size_zero hz0]
      exact ih (fun c' hc' => hpre c' (List.mem_cons_of_mem _ hc'))
        (fun c' hc' => hmem c' (List.mem_cons_of_mem _ hc'))

end

end NativeRustcArm
