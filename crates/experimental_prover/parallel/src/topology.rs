//! Which cores exist, and how to ask the OS for one.

use std::sync::OnceLock;

/// Worker counts for the pool: performance cores first, then the efficiency
/// cores that join the same work queue at a lower scheduling class.
#[derive(Clone, Copy, Debug)]
pub(crate) struct Topology {
    /// Workers scheduled on performance cores, including the dispatcher.
    pub(crate) perf: usize,
    /// Extra workers scheduled on efficiency cores; `0` on a homogeneous host.
    pub efficiency: usize,
}

impl Topology {
    /// Total workers, dispatcher included.
    #[must_use]
    pub const fn total(self) -> usize {
        self.perf + self.efficiency
    }
}

static TOPOLOGY: OnceLock<Topology> = OnceLock::new();

/// The pool's shape, resolved once.
#[must_use]
pub(crate) fn topology() -> Topology {
    *TOPOLOGY.get_or_init(default_topology)
}

/// Fixes the worker count before the pool starts: performance workers first, efficiency workers only beyond the
/// performance cores; `1` is sequential and `0` keeps the default. Panics if it is already another.
pub fn set_num_threads(n: usize) {
    if n == 0 {
        return;
    }
    let set = TOPOLOGY
        .get_or_init(|| {
            let efficiency = n.saturating_sub(perf_cores()).min(efficiency_cores());
            Topology {
                perf: n - efficiency,
                efficiency,
            }
        })
        .total();
    assert_eq!(set, n, "the thread pool already runs with {set} threads");
}

/// Worker count including the dispatcher.
#[must_use]
#[inline]
pub fn num_threads() -> usize {
    topology().total()
}

/// The pool's shape when nothing is pinned. Leave one performance core free on heterogeneous hosts for setup work and the operating system.
fn default_topology() -> Topology {
    let efficiency = efficiency_cores();
    let perf = perf_cores();
    // Never reserve below two performance workers.
    let reserve = usize::from(efficiency > 0 && perf > 2);
    Topology {
        perf: perf - reserve,
        efficiency,
    }
}

/// Performance-core count: `hw.perflevel0.logicalcpu` on Apple silicon (where
/// `available_parallelism` counts the efficiency cores too, and those are handled
/// separately), else the platform's parallelism, capped on Linux at the physical cores
/// the process may run on.
///
/// The prover is DRAM-bound once every core runs: a second SMT thread per core adds
/// cache and bandwidth contention, not throughput.
fn perf_cores() -> usize {
    #[cfg(all(target_arch = "aarch64", target_os = "macos"))]
    if let Some(n) = sysctl_usize(c"hw.perflevel0.logicalcpu") {
        return n;
    }
    // Already capped by the affinity mask and any cgroup quota.
    let logical = std::thread::available_parallelism().map_or(1, |n| n.get());
    #[cfg(target_os = "linux")]
    if let Some(cores) = allowed_cores() {
        return logical.min(cores);
    }
    logical
}

/// The distinct physical cores behind the CPUs this process may run on: a core whose
/// threads include at least one allowed CPU counts once.
#[cfg(target_os = "linux")]
fn allowed_cores() -> Option<usize> {
    let status = std::fs::read_to_string("/proc/self/status").ok()?;
    let allowed = status
        .lines()
        .find_map(|line| line.strip_prefix("Cpus_allowed_list:"))?;
    let mut cores = std::collections::HashSet::new();
    // An allowed CPU that is offline has no topology; it adds no core.
    for cpu in cpu_list(allowed.trim())? {
        let path = format!("/sys/devices/system/cpu/cpu{cpu}/topology/thread_siblings_list");
        if let Ok(siblings) = std::fs::read_to_string(path) {
            cores.insert(siblings.trim().to_owned());
        }
    }
    (!cores.is_empty()).then_some(cores.len())
}

/// The CPUs of a kernel CPU list such as `0-3,8,10-11`.
#[cfg(any(target_os = "linux", test))]
fn cpu_list(list: &str) -> Option<Vec<usize>> {
    let mut cpus = Vec::new();
    for part in list.split(',') {
        let (lo, hi) = part.split_once('-').unwrap_or((part, part));
        cpus.extend(lo.parse::<usize>().ok()?..=hi.parse::<usize>().ok()?);
    }
    Some(cpus)
}

/// Efficiency-core count on Apple silicon, else `0`.
fn efficiency_cores() -> usize {
    #[cfg(all(target_arch = "aarch64", target_os = "macos"))]
    if let Some(n) = sysctl_usize(c"hw.perflevel1.logicalcpu") {
        return n;
    }
    0
}

/// Read an integer `sysctl` by name through the syscall, never a spawned
/// `sysctl` process. Any failure reads as "unknown".
#[cfg(all(target_arch = "aarch64", target_os = "macos"))]
fn sysctl_usize(name: &core::ffi::CStr) -> Option<usize> {
    let mut value: i32 = 0;
    let mut len = core::mem::size_of::<i32>();
    // SAFETY: a read-only sysctl; `value`/`len` are correctly sized and the
    // new-value pointer is null, so nothing is written into the kernel.
    let rc = unsafe {
        libc::sysctlbyname(
            name.as_ptr(),
            (&raw mut value).cast(),
            &raw mut len,
            core::ptr::null_mut(),
            0,
        )
    };
    (rc == 0 && len == core::mem::size_of::<i32>() && value > 0).then_some(value as usize)
}

/// Scheduling class for a worker, which on Apple silicon is also a choice of
/// core cluster: the scheduler keeps `USER_INTERACTIVE` work off the efficiency
/// cores and places `UTILITY` work on them.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum Qos {
    /// Latency-critical: performance cores.
    Interactive,
    /// Background-ish: efficiency cores.
    Utility,
}

/// Tag the calling thread with `qos`. Best-effort, since QoS is a scheduling hint
/// and a failure must not affect correctness, only placement. No-op off macOS.
pub(crate) fn set_qos(qos: Qos) {
    #[cfg(target_os = "macos")]
    {
        const QOS_CLASS_USER_INTERACTIVE: u32 = 0x21;
        const QOS_CLASS_UTILITY: u32 = 0x11;
        unsafe extern "C" {
            fn pthread_set_qos_class_self_np(qos_class: u32, relative_priority: i32) -> i32;
        }
        let class = match qos {
            Qos::Interactive => QOS_CLASS_USER_INTERACTIVE,
            Qos::Utility => QOS_CLASS_UTILITY,
        };
        // SAFETY: a libSystem call that only adjusts this thread's scheduling class.
        unsafe {
            let _ = pthread_set_qos_class_self_np(class, 0);
        }
    }
    #[cfg(not(target_os = "macos"))]
    {
        let _ = qos;
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    #[should_panic(expected = "already runs")]
    fn a_fixed_shape_refuses_another() {
        set_num_threads(num_threads());
        set_num_threads(num_threads() + 1);
    }

    #[test]
    fn cpu_lists_parse_ranges_and_singles() {
        assert_eq!(cpu_list("0-3,8,10-11"), Some(vec![0, 1, 2, 3, 8, 10, 11]));
        assert_eq!(cpu_list("5"), Some(vec![5]));
        assert_eq!(cpu_list("0-x"), None);
    }
}
