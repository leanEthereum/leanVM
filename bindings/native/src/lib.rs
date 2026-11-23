//! The internal C ABI of the Java, Go, Zig and Nim bindings over the `lean_pq` facade: opaque
//! handles and owned buffers, not a public API.
#![allow(clippy::missing_safety_doc)] // Safety contract is documented in include/lean_pq_native.h.

use lean_pq::{sphincs, vrf, xmss, Aggregate, Message, Sidecar, MESSAGE_LEN, PUBLIC_KEY_LEN};
use std::cell::RefCell;
use std::ffi::c_int;
use std::panic::{catch_unwind, AssertUnwindSafe};
use std::path::PathBuf;
use std::ptr;

pub const LPQ_OK: c_int = 0;
pub const LPQ_ERROR: c_int = 1;
pub const LPQ_PANIC: c_int = 2;

const XMSS_RECORD_LEN: usize = PUBLIC_KEY_LEN + MESSAGE_LEN + xmss::SIGNATURE_LEN;
const SPHINCS_RECORD_LEN: usize = PUBLIC_KEY_LEN + MESSAGE_LEN + sphincs::SIGNATURE_LEN;
const CLAIM_RECORD_LEN: usize = PUBLIC_KEY_LEN + MESSAGE_LEN;

thread_local! {
    static LAST_ERROR: RefCell<String> = const { RefCell::new(String::new()) };
}

#[repr(C)]
#[derive(Default)]
pub struct LpqBuffer {
    pub data: *mut u8,
    pub len: usize,
}

/// Opaque ownership handle. Bindings only ever pass its address back to this library.
pub struct XmssSecretKeyHandle(xmss::SecretKey);
/// Opaque ownership handle. Bindings only ever pass its address back to this library.
pub struct SphincsSecretKeyHandle(sphincs::SecretKey);
/// Opaque ownership handle. Bindings only ever pass its address back to this library.
pub struct AggregateHandle(Aggregate);
/// Opaque ownership handle. Bindings only ever pass its address back to this library.
pub struct VrfKeyHandle(vrf::Key);
/// Opaque ownership handle. Bindings only ever pass its address back to this library.
pub struct SidecarHandle(Sidecar);

fn set_error(message: impl Into<String>) {
    LAST_ERROR.with(|error| *error.borrow_mut() = message.into());
}

fn ffi(operation: impl FnOnce() -> Result<(), String>) -> c_int {
    match catch_unwind(AssertUnwindSafe(operation)) {
        Ok(Ok(())) => {
            set_error("");
            LPQ_OK
        }
        Ok(Err(error)) => {
            set_error(error);
            LPQ_ERROR
        }
        Err(_) => {
            set_error("native lean-pq operation panicked");
            LPQ_PANIC
        }
    }
}

unsafe fn bytes<'a>(data: *const u8, len: usize, name: &str) -> Result<&'a [u8], String> {
    if len == 0 {
        return Ok(&[]);
    }
    if data.is_null() {
        return Err(format!(
            "{name} must not be null when its length is non-zero"
        ));
    }
    Ok(std::slice::from_raw_parts(data, len))
}

unsafe fn bytes32(data: *const u8, len: usize, name: &str) -> Result<[u8; 32], String> {
    bytes(data, len, name)?
        .try_into()
        .map_err(|_| format!("{name} must be exactly 32 bytes, got {len}"))
}

unsafe fn records<'a>(
    data: *const u8,
    count: usize,
    record_len: usize,
    name: &str,
) -> Result<std::slice::ChunksExact<'a, u8>, String> {
    let len = count
        .checked_mul(record_len)
        .ok_or_else(|| format!("{name} length overflow"))?;
    Ok(bytes(data, len, name)?.chunks_exact(record_len))
}

fn split_record(record: &[u8]) -> (&[u8], Message, &[u8]) {
    let (public_key, rest) = record.split_at(PUBLIC_KEY_LEN);
    let (message, signature) = rest.split_at(MESSAGE_LEN);
    let message = message.try_into().expect("record has message length");
    (public_key, message, signature)
}

unsafe fn handle<'a, T>(handle: *mut T, name: &str) -> Result<&'a T, String> {
    handle
        .as_ref()
        .ok_or_else(|| format!("{name} handle must not be null"))
}

unsafe fn put_handle<T>(out: *mut *mut T, value: T, name: &str) -> Result<(), String> {
    let out = out
        .as_mut()
        .ok_or_else(|| format!("{name} output pointer must not be null"))?;
    *out = Box::into_raw(Box::new(value));
    Ok(())
}

unsafe fn put_buffer(out: *mut LpqBuffer, value: Vec<u8>) -> Result<(), String> {
    let out = out
        .as_mut()
        .ok_or_else(|| "buffer output pointer must not be null".to_owned())?;
    let len = value.len();
    let data = Box::into_raw(value.into_boxed_slice()) as *mut u8;
    *out = LpqBuffer { data, len };
    Ok(())
}

unsafe fn destroy<T>(handle: *mut T) {
    if !handle.is_null() {
        drop(Box::from_raw(handle));
    }
}

fn claims<const N: usize>(claims: impl IntoIterator<Item = ([u8; N], Message)>) -> Vec<u8> {
    claims
        .into_iter()
        .flat_map(|(public_key, message)| public_key.into_iter().chain(message))
        .collect()
}

unsafe fn path_arg(data: *const u8, len: usize) -> Result<PathBuf, String> {
    let path = bytes(data, len, "path")?;
    #[cfg(unix)]
    {
        use std::os::unix::ffi::OsStrExt;
        Ok(PathBuf::from(std::ffi::OsStr::from_bytes(path)))
    }
    #[cfg(not(unix))]
    {
        std::str::from_utf8(path)
            .map(PathBuf::from)
            .map_err(|_| "path must be UTF-8".to_owned())
    }
}

#[no_mangle]
pub unsafe extern "C" fn lpq_sidecar_connect(
    path: *const u8,
    len: usize,
    out: *mut *mut SidecarHandle,
) -> c_int {
    ffi(|| {
        let sidecar = Sidecar::connect(path_arg(path, len)?).map_err(|e| e.to_string())?;
        put_handle(out, SidecarHandle(sidecar), "sidecar")
    })
}

#[no_mangle]
pub unsafe extern "C" fn lpq_sidecar_start(
    binary: *const u8,
    binary_len: usize,
    path: *const u8,
    len: usize,
    threads: usize,
    out: *mut *mut SidecarHandle,
) -> c_int {
    ffi(|| {
        let sidecar = Sidecar::start(path_arg(binary, binary_len)?, path_arg(path, len)?, threads)
            .map_err(|e| e.to_string())?;
        put_handle(out, SidecarHandle(sidecar), "sidecar")
    })
}

#[no_mangle]
pub unsafe extern "C" fn lpq_sidecar_prover(
    sidecar: *mut SidecarHandle,
    out: *mut LpqBuffer,
) -> c_int {
    ffi(|| {
        let prover = handle(sidecar, "sidecar")?.0.prover().as_bytes().to_vec();
        put_buffer(out, prover)
    })
}

#[no_mangle]
pub unsafe extern "C" fn lpq_sidecar_close(sidecar: *mut SidecarHandle) -> c_int {
    ffi(|| {
        handle(sidecar, "sidecar")?.0.close();
        Ok(())
    })
}

#[no_mangle]
pub unsafe extern "C" fn lpq_sidecar_destroy(sidecar: *mut SidecarHandle) {
    destroy(sidecar)
}

#[no_mangle]
pub unsafe extern "C" fn lpq_last_error(out: *mut LpqBuffer) -> c_int {
    ffi(|| {
        let bytes = LAST_ERROR.with(|error| error.borrow().as_bytes().to_vec());
        put_buffer(out, bytes)
    })
}

#[no_mangle]
pub unsafe extern "C" fn lpq_buffer_free(data: *mut u8, len: usize) {
    if !data.is_null() && len != 0 {
        drop(Box::from_raw(ptr::slice_from_raw_parts_mut(data, len)));
    }
}

#[no_mangle]
pub unsafe extern "C" fn lpq_xmss_secret_key_generate(out: *mut *mut XmssSecretKeyHandle) -> c_int {
    ffi(|| {
        put_handle(
            out,
            XmssSecretKeyHandle(xmss::SecretKey::generate()),
            "secret-key",
        )
    })
}

#[no_mangle]
pub unsafe extern "C" fn lpq_xmss_secret_key_from_bytes(
    data: *const u8,
    len: usize,
    out: *mut *mut XmssSecretKeyHandle,
) -> c_int {
    ffi(|| {
        let key = xmss::SecretKey::from_bytes(bytes(data, len, "secret key")?)
            .map_err(|e| e.to_string())?;
        put_handle(out, XmssSecretKeyHandle(key), "secret-key")
    })
}

#[no_mangle]
pub unsafe extern "C" fn lpq_xmss_secret_key_to_bytes(
    key: *mut XmssSecretKeyHandle,
    out: *mut LpqBuffer,
) -> c_int {
    ffi(|| put_buffer(out, handle(key, "secret-key")?.0.to_bytes().to_vec()))
}

#[no_mangle]
pub unsafe extern "C" fn lpq_xmss_secret_key_from_cache_bytes(
    seed: *const u8,
    seed_len: usize,
    public_key: *const u8,
    public_key_len: usize,
    cache: *const u8,
    cache_len: usize,
    out: *mut *mut XmssSecretKeyHandle,
) -> c_int {
    ffi(|| {
        let seed = bytes32(seed, seed_len, "seed")?;
        let public_key =
            xmss::PublicKey::from_bytes(bytes(public_key, public_key_len, "public key")?)
                .map_err(|e| e.to_string())?;
        let key =
            xmss::SecretKey::from_cache_bytes(seed, &public_key, bytes(cache, cache_len, "cache")?)
                .map_err(|e| e.to_string())?;
        put_handle(out, XmssSecretKeyHandle(key), "secret-key")
    })
}

#[no_mangle]
pub unsafe extern "C" fn lpq_xmss_secret_key_cache_to_bytes(
    key: *mut XmssSecretKeyHandle,
    out: *mut LpqBuffer,
) -> c_int {
    ffi(|| put_buffer(out, handle(key, "secret-key")?.0.cache_to_bytes()))
}

#[no_mangle]
pub unsafe extern "C" fn lpq_xmss_secret_key_public_key(
    key: *mut XmssSecretKeyHandle,
    out: *mut LpqBuffer,
) -> c_int {
    ffi(|| {
        let public_key = handle(key, "secret-key")?.0.public_key().to_bytes();
        put_buffer(out, public_key.to_vec())
    })
}

#[no_mangle]
pub unsafe extern "C" fn lpq_xmss_secret_key_prepare(
    key: *mut XmssSecretKeyHandle,
    leaf_index: u32,
) -> c_int {
    ffi(|| {
        handle(key, "secret-key")?.0.prepare(leaf_index);
        Ok(())
    })
}

#[no_mangle]
pub unsafe extern "C" fn lpq_xmss_secret_key_sign(
    key: *mut XmssSecretKeyHandle,
    message: *const u8,
    message_len: usize,
    leaf_index: u32,
    out: *mut LpqBuffer,
) -> c_int {
    ffi(|| {
        let key = handle(key, "secret-key")?;
        let message = bytes32(message, message_len, "message")?;
        let signature = key.0.sign(&message, leaf_index);
        put_buffer(out, signature.to_bytes().to_vec())
    })
}

#[no_mangle]
pub unsafe extern "C" fn lpq_xmss_secret_key_destroy(key: *mut XmssSecretKeyHandle) {
    destroy(key)
}

#[no_mangle]
pub unsafe extern "C" fn lpq_xmss_verify(
    public_key: *const u8,
    public_key_len: usize,
    message: *const u8,
    message_len: usize,
    signature: *const u8,
    signature_len: usize,
) -> c_int {
    ffi(|| {
        let public_key =
            xmss::PublicKey::from_bytes(bytes(public_key, public_key_len, "public key")?)
                .map_err(|e| e.to_string())?;
        let message = bytes32(message, message_len, "message")?;
        let signature = xmss::Signature::from_bytes(bytes(signature, signature_len, "signature")?)
            .map_err(|e| e.to_string())?;
        public_key
            .verify(&message, &signature)
            .map_err(|e| e.to_string())
    })
}

#[no_mangle]
pub unsafe extern "C" fn lpq_sphincs_secret_key_generate(
    out: *mut *mut SphincsSecretKeyHandle,
) -> c_int {
    ffi(|| {
        put_handle(
            out,
            SphincsSecretKeyHandle(sphincs::SecretKey::generate()),
            "secret-key",
        )
    })
}

#[no_mangle]
pub unsafe extern "C" fn lpq_sphincs_secret_key_from_seed(
    seed: *const u8,
    seed_len: usize,
    out: *mut *mut SphincsSecretKeyHandle,
) -> c_int {
    ffi(|| {
        let seed = bytes32(seed, seed_len, "seed")?;
        put_handle(
            out,
            SphincsSecretKeyHandle(sphincs::SecretKey::from_seed(seed)),
            "secret-key",
        )
    })
}

#[no_mangle]
pub unsafe extern "C" fn lpq_sphincs_secret_key_from_bytes(
    data: *const u8,
    len: usize,
    out: *mut *mut SphincsSecretKeyHandle,
) -> c_int {
    ffi(|| {
        let key = sphincs::SecretKey::from_bytes(bytes(data, len, "secret key")?)
            .map_err(|e| e.to_string())?;
        put_handle(out, SphincsSecretKeyHandle(key), "secret-key")
    })
}

#[no_mangle]
pub unsafe extern "C" fn lpq_sphincs_secret_key_to_bytes(
    key: *mut SphincsSecretKeyHandle,
    out: *mut LpqBuffer,
) -> c_int {
    ffi(|| put_buffer(out, handle(key, "secret-key")?.0.to_bytes().to_vec()))
}

#[no_mangle]
pub unsafe extern "C" fn lpq_sphincs_secret_key_public_key(
    key: *mut SphincsSecretKeyHandle,
    out: *mut LpqBuffer,
) -> c_int {
    ffi(|| {
        let public_key = handle(key, "secret-key")?.0.public_key().to_bytes();
        put_buffer(out, public_key.to_vec())
    })
}

#[no_mangle]
pub unsafe extern "C" fn lpq_sphincs_secret_key_sign(
    key: *mut SphincsSecretKeyHandle,
    message: *const u8,
    message_len: usize,
    out: *mut LpqBuffer,
) -> c_int {
    ffi(|| {
        let key = handle(key, "secret-key")?;
        let message = bytes32(message, message_len, "message")?;
        let signature = key.0.sign(&message);
        put_buffer(out, signature.to_bytes().to_vec())
    })
}

#[no_mangle]
pub unsafe extern "C" fn lpq_sphincs_secret_key_destroy(key: *mut SphincsSecretKeyHandle) {
    destroy(key)
}

#[no_mangle]
pub unsafe extern "C" fn lpq_sphincs_verify(
    public_key: *const u8,
    public_key_len: usize,
    message: *const u8,
    message_len: usize,
    signature: *const u8,
    signature_len: usize,
) -> c_int {
    ffi(|| {
        let public_key =
            sphincs::PublicKey::from_bytes(bytes(public_key, public_key_len, "public key")?)
                .map_err(|e| e.to_string())?;
        let message = bytes32(message, message_len, "message")?;
        let signature =
            sphincs::Signature::from_bytes(bytes(signature, signature_len, "signature")?)
                .map_err(|e| e.to_string())?;
        public_key
            .verify(&message, &signature)
            .map_err(|e| e.to_string())
    })
}

#[no_mangle]
pub unsafe extern "C" fn lpq_sidecar_aggregate(
    sidecar: *mut SidecarHandle,
    children: *const *mut AggregateHandle,
    child_count: usize,
    xmss_records: *const u8,
    xmss_count: usize,
    sphincs_records: *const u8,
    sphincs_count: usize,
    out: *mut *mut AggregateHandle,
) -> c_int {
    ffi(|| {
        let sidecar = &handle(sidecar, "sidecar")?.0;
        let children = if child_count == 0 {
            Vec::new()
        } else {
            if children.is_null() {
                return Err("children must not be null when the count is non-zero".to_owned());
            }
            std::slice::from_raw_parts(children, child_count)
                .iter()
                .map(|&child| handle(child, "aggregate").map(|child| &child.0))
                .collect::<Result<Vec<_>, _>>()?
        };
        let xmss = records(
            xmss_records,
            xmss_count,
            XMSS_RECORD_LEN,
            "leanXMSS records",
        )?
        .map(|record| {
            let (public_key, message, signature) = split_record(record);
            Ok((
                xmss::PublicKey::from_bytes(public_key)?,
                message,
                xmss::Signature::from_bytes(signature)?,
            ))
        })
        .collect::<Result<Vec<_>, lean_pq::Error>>()
        .map_err(|e| e.to_string())?;
        let sphincs = records(
            sphincs_records,
            sphincs_count,
            SPHINCS_RECORD_LEN,
            "leanSPHINCS records",
        )?
        .map(|record| {
            let (public_key, message, signature) = split_record(record);
            Ok((
                sphincs::PublicKey::from_bytes(public_key)?,
                message,
                sphincs::Signature::from_bytes(signature)?,
            ))
        })
        .collect::<Result<Vec<_>, lean_pq::Error>>()
        .map_err(|e| e.to_string())?;
        let aggregate = sidecar
            .aggregate(&children, &xmss, &sphincs)
            .map_err(|e| e.to_string())?;
        put_handle(out, AggregateHandle(aggregate), "aggregate")
    })
}

#[no_mangle]
pub unsafe extern "C" fn lpq_sidecar_verify(
    sidecar: *mut SidecarHandle,
    data: *const u8,
    len: usize,
    xmss_claims: *const u8,
    xmss_count: usize,
    sphincs_claims: *const u8,
    sphincs_count: usize,
    out: *mut *mut AggregateHandle,
) -> c_int {
    ffi(|| {
        let sidecar = &handle(sidecar, "sidecar")?.0;
        let xmss = records(xmss_claims, xmss_count, CLAIM_RECORD_LEN, "leanXMSS claims")?
            .map(|record| {
                let (public_key, message, _) = split_record(record);
                Ok((xmss::PublicKey::from_bytes(public_key)?, message))
            })
            .collect::<Result<Vec<_>, lean_pq::Error>>()
            .map_err(|e| e.to_string())?;
        let sphincs = records(
            sphincs_claims,
            sphincs_count,
            CLAIM_RECORD_LEN,
            "leanSPHINCS claims",
        )?
        .map(|record| {
            let (public_key, message, _) = split_record(record);
            Ok((sphincs::PublicKey::from_bytes(public_key)?, message))
        })
        .collect::<Result<Vec<_>, lean_pq::Error>>()
        .map_err(|e| e.to_string())?;
        let aggregate = sidecar
            .verify(bytes(data, len, "aggregate")?, &xmss, &sphincs)
            .map_err(|e| e.to_string())?;
        put_handle(out, AggregateHandle(aggregate), "aggregate")
    })
}

#[no_mangle]
pub unsafe extern "C" fn lpq_aggregate_to_bytes(
    aggregate: *mut AggregateHandle,
    out: *mut LpqBuffer,
) -> c_int {
    ffi(|| put_buffer(out, handle(aggregate, "aggregate")?.0.to_bytes()))
}

#[no_mangle]
pub unsafe extern "C" fn lpq_aggregate_xmss_claims(
    aggregate: *mut AggregateHandle,
    out: *mut LpqBuffer,
) -> c_int {
    ffi(|| {
        let aggregate = handle(aggregate, "aggregate")?;
        let claims = claims(
            aggregate
                .0
                .xmss_claims()
                .into_iter()
                .map(|(public_key, message)| (public_key.to_bytes(), message)),
        );
        put_buffer(out, claims)
    })
}

#[no_mangle]
pub unsafe extern "C" fn lpq_aggregate_sphincs_claims(
    aggregate: *mut AggregateHandle,
    out: *mut LpqBuffer,
) -> c_int {
    ffi(|| {
        let aggregate = handle(aggregate, "aggregate")?;
        let claims = claims(
            aggregate
                .0
                .sphincs_claims()
                .into_iter()
                .map(|(public_key, message)| (public_key.to_bytes(), message)),
        );
        put_buffer(out, claims)
    })
}

#[no_mangle]
pub unsafe extern "C" fn lpq_aggregate_destroy(aggregate: *mut AggregateHandle) {
    destroy(aggregate)
}

#[no_mangle]
pub unsafe extern "C" fn lpq_vrf_key_new(
    seed: *const u8,
    seed_len: usize,
    start: u32,
    end: u32,
    out: *mut *mut VrfKeyHandle,
) -> c_int {
    ffi(|| {
        let seed = bytes32(seed, seed_len, "seed")?;
        let key = vrf::Key::new(seed, start..end).map_err(|e| e.to_string())?;
        put_handle(out, VrfKeyHandle(key), "VRF key")
    })
}

#[no_mangle]
pub unsafe extern "C" fn lpq_vrf_key_from_cache_bytes(
    seed: *const u8,
    seed_len: usize,
    root: *const u8,
    root_len: usize,
    cache: *const u8,
    cache_len: usize,
    out: *mut *mut VrfKeyHandle,
) -> c_int {
    ffi(|| {
        let seed = bytes32(seed, seed_len, "seed")?;
        let root = bytes32(root, root_len, "root")?;
        let key = vrf::Key::from_cache_bytes(seed, &root, bytes(cache, cache_len, "cache")?)
            .map_err(|e| e.to_string())?;
        put_handle(out, VrfKeyHandle(key), "VRF key")
    })
}

#[no_mangle]
pub unsafe extern "C" fn lpq_vrf_key_cache_to_bytes(
    key: *mut VrfKeyHandle,
    out: *mut LpqBuffer,
) -> c_int {
    ffi(|| put_buffer(out, handle(key, "VRF key")?.0.cache_to_bytes()))
}

#[no_mangle]
pub unsafe extern "C" fn lpq_vrf_key_root(key: *mut VrfKeyHandle, out: *mut LpqBuffer) -> c_int {
    ffi(|| put_buffer(out, handle(key, "VRF key")?.0.root().to_vec()))
}

#[no_mangle]
pub unsafe extern "C" fn lpq_vrf_key_proof(
    key: *mut VrfKeyHandle,
    slot: u32,
    out: *mut LpqBuffer,
) -> c_int {
    ffi(|| {
        let proof = handle(key, "VRF key")?
            .0
            .proof(slot)
            .map_err(|e| e.to_string())?;
        put_buffer(out, proof.as_flattened().to_vec())
    })
}

#[no_mangle]
pub unsafe extern "C" fn lpq_vrf_key_destroy(key: *mut VrfKeyHandle) {
    destroy(key)
}

#[no_mangle]
pub unsafe extern "C" fn lpq_vrf_verify(
    root: *const u8,
    root_len: usize,
    slot: u64,
    proof: *const u8,
    proof_len: usize,
) -> c_int {
    ffi(|| {
        let root = bytes32(root, root_len, "root")?;
        let proof = bytes(proof, proof_len, "proof")?;
        if proof.len() != vrf::PROOF_LEN {
            return Err(format!(
                "proof must be exactly {} bytes, got {proof_len}",
                vrf::PROOF_LEN
            ));
        }
        let (nodes, _) = proof.as_chunks::<32>();
        let proof: vrf::Proof = nodes.try_into().expect("proof has 32 nodes");
        vrf::verify(&root, slot, &proof).map_err(|e| e.to_string())
    })
}
