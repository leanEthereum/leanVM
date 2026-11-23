module

public import NativeRustcVmX64.KeccakGkr.KeccakOpen.FoldInner

namespace NativeRustcVmX64.KeccakGkr.KeccakOpen

open NativeRustcX64 NativeRustcX64.Sym NativeVm.Model NativeRustcVmX64.Transcript

public section

variable [Host]

theorem inner_loop {head tail : Int64} {I : Nat → MachineData → Prop} {limit : Nat}
    (hstep : ∀ j < limit, ∀ st : MachineState, st.pc = head → I j st.data →
      Eventually (step1 Host.exe) (fun st' ↦ st'.pc = (if j + 1 < limit then head else tail) ∧
        I (j + 1) st'.data) st)
    {j : Nat} (hj : j < limit) {st : MachineState} (hpc : st.pc = head) (hh : I j st.data) :
    Eventually (step1 Host.exe) (fun st' ↦ st'.pc = tail ∧ I limit st'.data) st := by
  refine (hstep j hj st hpc hh).bind fun st' ⟨hpc', hh'⟩ ↦ ?_
  by_cases hn : j + 1 < limit
  · rw [ite_eq_left hn] at hpc'
    exact inner_loop hstep hn hpc' hh'
  · have he : j + 1 = limit := by omega
    rw [ite_eq_right hn] at hpc'
    rw [he] at hh'
    exact .done _ ⟨hpc', hh'⟩
termination_by limit - j

end

end NativeRustcVmX64.KeccakGkr.KeccakOpen
