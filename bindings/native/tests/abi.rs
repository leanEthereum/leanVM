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
            assert_eq!(lpq_setup(), OK);
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
            assert_eq!(xmss_sig.len(), 2404);
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
            assert_eq!(sphincs_sig.len(), 7740);
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
