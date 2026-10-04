//! Which cores exist, and how to ask the OS for one.

#[cfg(all(target_arch = "aarch64", target_os = "macos"))]
use core::ffi::CStr;
use std::sync::OnceLock;

/// Worker counts for the pool: performance cores first, then the efficiency
/// cores that join the same work queue at a lower scheduling class.
#[derive(Clone, Copy, Debug)]
pub struct Topology {
    /// Workers scheduled on performance cores, including the dispatcher.
    pub perf: usize,
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

/// The pool's shape, resolved once.
///
/// `LEANVM_NUM_THREADS` sets the **performance**-worker count; the efficiency
/// workers are added on top either way, because that count has always meant
/// "how wide is the fast cluster" here and not "how many threads exist".
/// `1` is the exception and means strictly sequential (no workers at all), so a
/// single-threaded debugging run really is one thread.
#[must_use]
pub fn topology() -> Topology {
    static TOPOLOGY: OnceLock<Topology> = OnceLock::new();
    *TOPOLOGY.get_or_init(|| {
        let requested = std::env::var("LEANVM_NUM_THREADS")
            .ok()
            .and_then(|v| v.parse::<usize>().ok())
            .filter(|&n| n > 0);
        match requested {
            Some(1) => Topology { perf: 1, efficiency: 0 },
            Some(perf) => Topology {
                perf,
                efficiency: efficiency_cores(),
            },
            None => default_topology(),
        }
    })
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
/// separately), else the platform's parallelism.
fn perf_cores() -> usize {
    #[cfg(all(target_arch = "aarch64", target_os = "macos"))]
    if let Some(n) = sysctl_usize(c"hw.perflevel0.logicalcpu") {
        return n;
    }
    std::thread::available_parallelism().map_or(1, |n| n.get())
}

/// Efficiency-core count on Apple silicon, else `0`.
#[cfg_attr(
    not(all(target_arch = "aarch64", target_os = "macos")),
    expect(
        clippy::missing_const_for_fn,
        reason = "Apple silicon discovers its efficiency cores at runtime."
    )
)]
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
fn sysctl_usize(name: &CStr) -> Option<usize> {
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
#[cfg_attr(
    not(target_os = "macos"),
    expect(
        clippy::missing_const_for_fn,
        reason = "macOS thread scheduling is a runtime system call."
    )
)]
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
