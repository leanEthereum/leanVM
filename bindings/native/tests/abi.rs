use lean_pq_native::*;
use std::ptr;

const OK: i32 = 0;
const ERROR: i32 = 1;

unsafe fn take(buffer: LpqBuffer) -> Vec<u8> {
    let bytes = std::slice::from_raw_parts(buffer.data, buffer.len).to_vec();
    lpq_buffer_free(buffer.data, buffer.len);
    bytes
}

#[test]
fn native_abi_signs_verifies_and_aggregates() {
    std::thread::Builder::new()
        .name("native-abi-test".to_owned())
        .stack_size(32 * 1024 * 1024)
        .spawn(|| unsafe {
            assert_eq!(lpq_setup(0), OK);
            let message = [42u8; 32];
            let other = [43u8; 32];

            // leanXMSS
            let mut xmss_key = ptr::null_mut();
            assert_eq!(
                lpq_xmss_secret_key_from_bytes([7; 32].as_ptr(), 32, &mut xmss_key),
                OK
            );
            let mut buffer = LpqBuffer::default();
            assert_eq!(lpq_xmss_secret_key_to_bytes(xmss_key, &mut buffer), OK);
            assert_eq!(take(buffer), [7; 32]);
            let mut buffer = LpqBuffer::default();
            assert_eq!(lpq_xmss_secret_key_public_key(xmss_key, &mut buffer), OK);
            let xmss_pk = take(buffer);
            assert_eq!(xmss_pk.len(), 32);
            assert_eq!(lpq_xmss_secret_key_prepare(xmss_key, 5), OK);
            let mut buffer = LpqBuffer::default();
            assert_eq!(
                lpq_xmss_secret_key_sign(xmss_key, message.as_ptr(), 32, 5, &mut buffer),
                OK
            );
            let xmss_sig = take(buffer);
            assert_eq!(xmss_sig.len(), lean_pq::xmss::SIGNATURE_LEN);
            assert_eq!(
                lpq_xmss_verify(
                    xmss_pk.as_ptr(),
                    32,
                    message.as_ptr(),
                    32,
                    xmss_sig.as_ptr(),
                    xmss_sig.len()
                ),
                OK
            );
            assert_eq!(
                lpq_xmss_verify(
                    xmss_pk.as_ptr(),
                    32,
                    other.as_ptr(),
                    32,
                    xmss_sig.as_ptr(),
                    xmss_sig.len()
                ),
                ERROR
            );
            let mut error = LpqBuffer::default();
            assert_eq!(lpq_last_error(&mut error), OK);
            assert!(!take(error).is_empty());

            // The key loads from its seed and its tree cache, and signs the same.
            let mut buffer = LpqBuffer::default();
            assert_eq!(
                lpq_xmss_secret_key_cache_to_bytes(xmss_key, &mut buffer),
                OK
            );
            let cache = take(buffer);
            let mut loaded = ptr::null_mut();
            assert_eq!(
                lpq_xmss_secret_key_from_cache_bytes(
                    [7; 32].as_ptr(),
                    32,
                    xmss_pk.as_ptr(),
                    xmss_pk.len(),
                    cache.as_ptr(),
                    cache.len(),
                    &mut loaded
                ),
                OK
            );
            let mut buffer = LpqBuffer::default();
            assert_eq!(
                lpq_xmss_secret_key_sign(loaded, message.as_ptr(), 32, 5, &mut buffer),
                OK
            );
            assert_eq!(take(buffer), xmss_sig);
            lpq_xmss_secret_key_destroy(loaded);
            let mut rejected = ptr::null_mut();
            assert_eq!(
                lpq_xmss_secret_key_from_cache_bytes(
                    [7; 32].as_ptr(),
                    32,
                    xmss_pk.as_ptr(),
                    xmss_pk.len(),
                    cache.as_ptr(),
                    cache.len() - 1,
                    &mut rejected
                ),
                ERROR
            );
            assert!(rejected.is_null());
            lpq_xmss_secret_key_destroy(xmss_key);

            // leanSPHINCS
            let mut sphincs_key = ptr::null_mut();
            assert_eq!(
                lpq_sphincs_secret_key_from_seed([9; 32].as_ptr(), 32, &mut sphincs_key),
                OK
            );
            let mut buffer = LpqBuffer::default();
            assert_eq!(
                lpq_sphincs_secret_key_to_bytes(sphincs_key, &mut buffer),
                OK
            );
            let sphincs_sk = take(buffer);
            assert_eq!(sphincs_sk, [9; 32]);
            let mut restored = ptr::null_mut();
            assert_eq!(
                lpq_sphincs_secret_key_from_bytes(
                    sphincs_sk.as_ptr(),
                    sphincs_sk.len(),
                    &mut restored
                ),
                OK
            );
            lpq_sphincs_secret_key_destroy(restored);
            let mut buffer = LpqBuffer::default();
            assert_eq!(
                lpq_sphincs_secret_key_public_key(sphincs_key, &mut buffer),
                OK
            );
            let sphincs_pk = take(buffer);
            let mut buffer = LpqBuffer::default();
            assert_eq!(
                lpq_sphincs_secret_key_sign(sphincs_key, message.as_ptr(), 32, &mut buffer),
                OK
            );
            let sphincs_sig = take(buffer);
            assert_eq!(sphincs_sig.len(), lean_pq::sphincs::SIGNATURE_LEN);
            assert_eq!(
                lpq_sphincs_verify(
                    sphincs_pk.as_ptr(),
                    32,
                    message.as_ptr(),
                    32,
                    sphincs_sig.as_ptr(),
                    sphincs_sig.len()
                ),
                OK
            );
            assert_eq!(
                lpq_sphincs_verify(
                    sphincs_pk.as_ptr(),
                    32,
                    other.as_ptr(),
                    32,
                    sphincs_sig.as_ptr(),
                    sphincs_sig.len()
                ),
                ERROR
            );
            lpq_sphincs_secret_key_destroy(sphincs_key);

            // Aggregate one record of each scheme.
            let xmss_record = [&xmss_pk[..], &message, &xmss_sig].concat();
            let sphincs_record = [&sphincs_pk[..], &message, &sphincs_sig].concat();
            let mut aggregate = ptr::null_mut();
            assert_eq!(
                lpq_aggregate_create(
                    ptr::null(),
                    0,
                    xmss_record.as_ptr(),
                    1,
                    sphincs_record.as_ptr(),
                    1,
                    &mut aggregate
                ),
                OK
            );
            let mut buffer = LpqBuffer::default();
            assert_eq!(lpq_aggregate_to_bytes(aggregate, &mut buffer), OK);
            let aggregate_bytes = take(buffer);
            lpq_aggregate_destroy(aggregate);

            // Decoding takes the claims the proof must prove, as 64-byte records.
            let xmss_claim = [&xmss_pk[..], &message].concat();
            let sphincs_claim = [&sphincs_pk[..], &message].concat();
            let mut decoded = ptr::null_mut();
            assert_eq!(
                lpq_aggregate_from_bytes(
                    aggregate_bytes.as_ptr(),
                    aggregate_bytes.len(),
                    xmss_claim.as_ptr(),
                    1,
                    sphincs_claim.as_ptr(),
                    1,
                    &mut decoded
                ),
                OK
            );
            let mut buffer = LpqBuffer::default();
            assert_eq!(lpq_aggregate_xmss_claims(decoded, &mut buffer), OK);
            assert_eq!(take(buffer), xmss_claim);
            let mut buffer = LpqBuffer::default();
            assert_eq!(lpq_aggregate_sphincs_claims(decoded, &mut buffer), OK);
            assert_eq!(take(buffer), sphincs_claim);

            // Re-aggregating it can keep only the leanXMSS claim.
            let mut only = ptr::null_mut();
            assert_eq!(
                lpq_aggregate_create_only(
                    &decoded,
                    1,
                    ptr::null(),
                    0,
                    ptr::null(),
                    0,
                    xmss_claim.as_ptr(),
                    1,
                    ptr::null(),
                    0,
                    &mut only
                ),
                OK
            );
            let mut buffer = LpqBuffer::default();
            assert_eq!(lpq_aggregate_xmss_claims(only, &mut buffer), OK);
            assert_eq!(take(buffer), xmss_claim);
            let mut buffer = LpqBuffer::default();
            assert_eq!(lpq_aggregate_sphincs_claims(only, &mut buffer), OK);
            assert!(take(buffer).is_empty());
            lpq_aggregate_destroy(only);

            // A claim the inputs do not cover fails, and leaves no handle.
            let uncovered = [&xmss_pk[..], &other].concat();
            let mut rejected = ptr::null_mut();
            assert_eq!(
                lpq_aggregate_create_only(
                    &decoded,
                    1,
                    ptr::null(),
                    0,
                    ptr::null(),
                    0,
                    uncovered.as_ptr(),
                    1,
                    ptr::null(),
                    0,
                    &mut rejected
                ),
                ERROR
            );
            assert!(rejected.is_null());
            lpq_aggregate_destroy(decoded);

            // The same proof against one claim short fails, and leaves no handle.
            let mut rejected = ptr::null_mut();
            assert_eq!(
                lpq_aggregate_from_bytes(
                    aggregate_bytes.as_ptr(),
                    aggregate_bytes.len(),
                    xmss_claim.as_ptr(),
                    1,
                    ptr::null(),
                    0,
                    &mut rejected
                ),
                ERROR
            );
            assert!(rejected.is_null());
        })
        .expect("test thread starts")
        .join()
        .expect("test thread completes");
}

#[test]
fn native_abi_reveals_and_verifies_vrf_proofs() {
    unsafe {
        let seed = [9u8; 32];
        let mut key = ptr::null_mut();
        assert_eq!(lpq_vrf_key_new(seed.as_ptr(), 32, 5, 5, &mut key), ERROR);
        assert_eq!(lpq_vrf_key_new(seed.as_ptr(), 32, 100, 200, &mut key), OK);

        let mut buffer = LpqBuffer::default();
        assert_eq!(lpq_vrf_key_root(key, &mut buffer), OK);
        let root = take(buffer);
        let mut buffer = LpqBuffer::default();
        assert_eq!(lpq_vrf_key_proof(key, 99, &mut buffer), ERROR);
        assert_eq!(lpq_vrf_key_proof(key, 150, &mut buffer), OK);
        let proof = take(buffer);
        assert_eq!(proof.len(), lean_pq::vrf::PROOF_LEN);
        let mut buffer = LpqBuffer::default();
        assert_eq!(lpq_vrf_key_cache_to_bytes(key, &mut buffer), OK);
        let cache = take(buffer);
        lpq_vrf_key_destroy(key);

        let mut key = ptr::null_mut();
        assert_eq!(
            lpq_vrf_key_from_cache_bytes(
                seed.as_ptr(),
                32,
                [0; 32].as_ptr(),
                32,
                cache.as_ptr(),
                cache.len(),
                &mut key
            ),
            ERROR
        );
        assert_eq!(
            lpq_vrf_key_from_cache_bytes(
                seed.as_ptr(),
                32,
                root.as_ptr(),
                32,
                cache.as_ptr(),
                cache.len(),
                &mut key
            ),
            OK
        );
        let mut buffer = LpqBuffer::default();
        assert_eq!(lpq_vrf_key_root(key, &mut buffer), OK);
        assert_eq!(take(buffer), root);
        lpq_vrf_key_destroy(key);

        assert_eq!(
            lpq_vrf_verify(root.as_ptr(), 32, 150, proof.as_ptr(), proof.len()),
            OK
        );
        assert_eq!(
            lpq_vrf_verify(root.as_ptr(), 32, 151, proof.as_ptr(), proof.len()),
            ERROR
        );
        assert_eq!(
            lpq_vrf_verify(root.as_ptr(), 32, 150, proof.as_ptr(), 32),
            ERROR
        );
    }
}

#[cfg(target_os = "linux")]
#[test]
fn lpq_sphincs_verify_respects_guard_pages_on_all_three_inputs() {
    use std::ffi::c_void;

    const PROT_NONE: i32 = 0;
    const PROT_READ: i32 = 1;
    const PROT_WRITE: i32 = 2;
    const MAP_PRIVATE: i32 = 0x02;
    const MAP_ANONYMOUS: i32 = 0x20;
    const SC_PAGESIZE: i32 = 30;

    extern "C" {
        fn mmap(
            addr: *mut c_void,
            length: usize,
            prot: i32,
            flags: i32,
            fd: i32,
            offset: isize,
        ) -> *mut c_void;
        fn mprotect(addr: *mut c_void, len: usize, prot: i32) -> i32;
        fn munmap(addr: *mut c_void, length: usize) -> i32;
        fn sysconf(name: i32) -> isize;
    }

    struct GuardedBuf {
        base: *mut u8,
        total: usize,
        ptr: *const u8,
    }

    impl GuardedBuf {
        unsafe fn new(data: &[u8], flush_right: bool) -> Self {
            let page = usize::try_from(sysconf(SC_PAGESIZE)).expect("positive page size");
            let data_pages = data.len().div_ceil(page).max(1);
            let total = (data_pages + 2) * page;
            let raw = mmap(
                ptr::null_mut(),
                total,
                PROT_NONE,
                MAP_PRIVATE | MAP_ANONYMOUS,
                -1,
                0,
            );
            assert_ne!(raw, usize::MAX as *mut c_void, "mmap failed");
            let base = raw.cast::<u8>();
            let usable = base.add(page);
            let usable_len = data_pages * page;
            assert_eq!(
                mprotect(usable.cast(), usable_len, PROT_READ | PROT_WRITE),
                0,
                "mprotect RW failed"
            );
            let offset = if flush_right {
                usable_len - data.len()
            } else {
                0
            };
            let dst = usable.add(offset);
            ptr::copy_nonoverlapping(data.as_ptr(), dst, data.len());
            assert_eq!(
                mprotect(usable.cast(), usable_len, PROT_READ),
                0,
                "mprotect RO failed"
            );
            Self {
                base,
                total,
                ptr: dst,
            }
        }
    }

    impl Drop for GuardedBuf {
        fn drop(&mut self) {
            unsafe {
                let _ = munmap(self.base.cast(), self.total);
            }
        }
    }

    unsafe {
        let message = [0x42u8; 32];
        let mut bad_message = message;
        bad_message[31] ^= 1;

        let mut key = ptr::null_mut();
        assert_eq!(
            lpq_sphincs_secret_key_from_seed([0x19; 32].as_ptr(), 32, &mut key),
            OK
        );
        let mut buf = LpqBuffer::default();
        assert_eq!(lpq_sphincs_secret_key_public_key(key, &mut buf), OK);
        let pk = take(buf);
        let mut buf = LpqBuffer::default();
        assert_eq!(
            lpq_sphincs_secret_key_sign(key, message.as_ptr(), message.len(), &mut buf),
            OK
        );
        let sig = take(buf);
        lpq_sphincs_secret_key_destroy(key);

        // Test both flush-left (immediately after a PROT_NONE page) and flush-right
        // (ending immediately before a PROT_NONE page; also unaligned for 7740-byte sig).
        for flush_right in [false, true] {
            let g_pk = GuardedBuf::new(&pk, flush_right);
            let g_msg = GuardedBuf::new(&message, flush_right);
            let g_bad = GuardedBuf::new(&bad_message, flush_right);
            let g_sig = GuardedBuf::new(&sig, flush_right);

            assert_eq!(
                lpq_sphincs_verify(
                    g_pk.ptr,
                    pk.len(),
                    g_msg.ptr,
                    message.len(),
                    g_sig.ptr,
                    sig.len()
                ),
                OK
            );
            assert_eq!(
                lpq_sphincs_verify(
                    g_pk.ptr,
                    pk.len(),
                    g_bad.ptr,
                    bad_message.len(),
                    g_sig.ptr,
                    sig.len()
                ),
                ERROR
            );
        }
    }
}
