//! The memory this process may use, read from the platform once.

/// Bytes of memory this process may use, or `None` where the platform does not say.
///
/// - On Linux, the least of the physical memory and every cgroup v2 limit above this process.
/// - It is a capacity, not what is free now: pages the allocator keeps from an earlier proof are reusable.
pub(crate) fn total_bytes() -> Option<usize> {
    #[cfg(target_os = "linux")]
    {
        let meminfo = std::fs::read_to_string("/proc/meminfo").ok()?;
        let line = meminfo.lines().find_map(|line| line.strip_prefix("MemTotal:"))?;
        let physical = line.trim().strip_suffix("kB")?.trim().parse::<usize>().ok()? << 10;
        Some(cgroup_limit().map_or(physical, |limit| limit.min(physical)))
    }
    #[cfg(not(target_os = "linux"))]
    None
}

/// The least cgroup v2 memory limit above this process, `None` when none is set.
#[cfg(target_os = "linux")]
fn cgroup_limit() -> Option<usize> {
    let membership = std::fs::read_to_string("/proc/self/cgroup").ok()?;
    let mut dir = membership.lines().find_map(|line| line.strip_prefix("0::"))?.trim();
    let mut least: Option<usize> = None;
    // A limit anywhere up the tree caps this process, so walk to the root.
    loop {
        // `max` reads as no limit at this level, like a file that is not there.
        let limit = std::fs::read_to_string(format!("/sys/fs/cgroup{dir}/memory.max")).ok();
        if let Some(limit) = limit.and_then(|s| s.trim().parse::<usize>().ok()) {
            least = Some(least.map_or(limit, |l| l.min(limit)));
        }
        let Some(i) = dir.rfind('/') else { break };
        dir = &dir[..i];
    }
    least
}
