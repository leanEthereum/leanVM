//! The allocation-free verifier links alloc, which requires a global allocator; allocation and panic trap.

use core::alloc::{GlobalAlloc, Layout};

struct NoAlloc;

// SAFETY: no call returns a pointer or touches an allocation.
unsafe impl GlobalAlloc for NoAlloc {
    unsafe fn alloc(&self, _: Layout) -> *mut u8 {
        abort()
    }

    unsafe fn dealloc(&self, _: *mut u8, _: Layout) {
        abort()
    }
}

#[global_allocator]
static ALLOCATOR: NoAlloc = NoAlloc;

#[panic_handler]
fn panic(_: &core::panic::PanicInfo) -> ! {
    abort()
}

fn abort() -> ! {
    // SAFETY: aborting does not access memory or return.
    unsafe {
        #[cfg(target_arch = "x86_64")]
        core::arch::asm!("ud2", options(noreturn, nomem, nostack));
        #[cfg(target_arch = "aarch64")]
        core::arch::asm!("udf #0", options(noreturn, nomem, nostack));
    }
}
