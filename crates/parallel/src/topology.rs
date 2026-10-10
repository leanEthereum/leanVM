//! Which cores exist, and how to ask the OS for one.

#[cfg(all(target_arch = "aarch64", target_os = "macos"))]
use core::ffi::CStr;
use std::num::NonZeroUsize;
use std::sync::OnceLock;

static TOPOLOGY: OnceLock<Topology> = OnceLock::new();

/// Worker counts for the pool: performance cores first, then the efficiency
/// cores that join the same work queue at a lower scheduling class.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
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

pub(crate) fn configure_threads(threads: NonZeroUsize) -> Result<(), Topology> {
    let requested = Topology {
        perf: threads.get(),
        efficiency: 0,
    };
    let actual = *TOPOLOGY.get_or_init(|| requested);
    if actual == requested { Ok(()) } else { Err(actual) }
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

/// Performance-core count: on Apple silicon every logical CPU outside the
/// efficiency cores (`available_parallelism` counts those too, and they are handled
/// separately), else the platform's parallelism.
fn perf_cores() -> usize {
    #[cfg(all(target_arch = "aarch64", target_os = "macos"))]
    if let Some(n) = sysctl_usize(c"hw.logicalcpu") {
        return n.saturating_sub(efficiency_cores()).max(1);
    }
    std::thread::available_parallelism().map_or(1, |n| n.get())
}

/// Efficiency-core count on Apple silicon, else `0`.
///
/// Only the performance levels macOS names `Efficiency` count: on chips whose
/// second level is a performance cluster (the M5 Pro and Max name theirs
/// `Super` and `Performance`) `hw.perflevel1` is not an efficiency cluster.
#[cfg_attr(
    not(all(target_arch = "aarch64", target_os = "macos")),
    expect(
        clippy::missing_const_for_fn,
        reason = "Apple silicon discovers its efficiency cores at runtime."
    )
)]
fn efficiency_cores() -> usize {
    #[cfg(all(target_arch = "aarch64", target_os = "macos"))]
    {
        let levels = sysctl_usize(c"hw.nperflevels").unwrap_or(0);
        let mut total = 0;
        for level in 0..levels {
            let name = std::ffi::CString::new(format!("hw.perflevel{level}.name")).ok();
            let count = std::ffi::CString::new(format!("hw.perflevel{level}.logicalcpu")).ok();
            if let (Some(name), Some(count)) = (name, count)
                && sysctl_string(&name).as_deref() == Some(b"Efficiency".as_slice())
            {
                total += sysctl_usize(&count).unwrap_or(0);
            }
        }
        total
    }
    #[cfg(not(all(target_arch = "aarch64", target_os = "macos")))]
    0
}

/// Read a string `sysctl` by name, without its terminating nul. Any failure
/// reads as "unknown".
#[cfg(all(target_arch = "aarch64", target_os = "macos"))]
fn sysctl_string(name: &CStr) -> Option<Vec<u8>> {
    let mut value = [0_u8; 64];
    let mut len = value.len();
    // SAFETY: a read-only sysctl into a local buffer whose size `len` states;
    // the new-value pointer is null, so nothing is written into the kernel.
    let rc = unsafe {
        libc::sysctlbyname(
            name.as_ptr(),
            value.as_mut_ptr().cast(),
            &raw mut len,
            core::ptr::null_mut(),
            0,
        )
    };
    let bytes = value.get(..len)?;
    (rc == 0).then(|| bytes.strip_suffix(&[0]).unwrap_or(bytes).to_vec())
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
