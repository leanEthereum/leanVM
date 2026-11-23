// jemalloc configured for proving.
#[cfg(unix)]
#[global_allocator]
static ALLOCATOR: allocator::Jemalloc = allocator::Jemalloc;

use std::panic::{catch_unwind, AssertUnwindSafe};
use std::sync::Arc;
use std::thread;

use lean_pq::{sphincs, vrf, xmss, Message};
use napi::bindgen_prelude::{AsyncTask, Buffer, Error, Object, Result, Status, Task};
use napi::Env;
use napi_derive::napi;

/// Runs `task` on a thread of its own and returns its promise.
///
/// Proving holds a thread for seconds, and building a VRF key over a range for up to minutes, while
/// `AsyncTask`'s threads are libuv's pool, which Node's file, DNS and crypto work share.
fn on_own_thread<T: Task + 'static>(env: &Env, mut task: T) -> Result<Object<'_>> {
    let (deferred, promise) = env.create_deferred()?;
    thread::spawn(
        move || match catch_unwind(AssertUnwindSafe(|| task.compute())) {
            Ok(Ok(output)) => deferred.resolve(move |env| task.resolve(env, output)),
            Ok(Err(error)) => deferred.reject(error),
            Err(panic) => {
                let reason = panic
                    .downcast_ref::<String>()
                    .map(String::as_str)
                    .or_else(|| panic.downcast_ref::<&str>().copied())
                    .unwrap_or("");
                deferred.reject(Error::new(
                    Status::GenericFailure,
                    format!("lean-pq panicked: {reason}"),
                ))
            }
        },
    );
    Ok(promise)
}

fn api_error(error: lean_pq::Error) -> Error {
    Error::new(Status::GenericFailure, error.to_string())
}

fn invalid_arg(reason: String) -> Error {
    Error::new(Status::InvalidArg, reason)
}

fn bytes32(bytes: &[u8], what: &str) -> Result<[u8; 32]> {
    bytes
        .try_into()
        .map_err(|_| invalid_arg(format!("{what} must be 32 bytes, got {}", bytes.len())))
}

fn to_message(bytes: &[u8]) -> Result<Message> {
    bytes32(bytes, "message")
}

/// JavaScript numbers are doubles; reject anything that is not exactly a `u32` rather than
/// let it wrap or truncate into a different leaf index.
fn uint32(value: f64, what: &str) -> Result<u32> {
    if value.fract() == 0.0 && (0.0..=f64::from(u32::MAX)).contains(&value) {
        Ok(value as u32)
    } else {
        Err(invalid_arg(format!(
            "{what} must be an integer in [0, {}], got {value}",
            u32::MAX
        )))
    }
}

/// Slots are `u64` in Rust; a JavaScript number is exact only up to `2^53 - 1`.
fn uint53(value: f64, what: &str) -> Result<u64> {
    const MAX: f64 = 9_007_199_254_740_991.0;
    if value.fract() == 0.0 && (0.0..=MAX).contains(&value) {
        Ok(value as u64)
    } else {
        Err(invalid_arg(format!(
            "{what} must be an integer in [0, {MAX}], got {value}"
        )))
    }
}

/// A `(public key, message)` pair an aggregate proves.
#[napi(object)]
pub struct Claim {
    pub public_key: Buffer,
    pub message: Buffer,
}

struct RawClaim {
    public_key: Vec<u8>,
    message: Vec<u8>,
}

impl From<Claim> for RawClaim {
    fn from(claim: Claim) -> Self {
        Self {
            public_key: claim.public_key.to_vec(),
            message: claim.message.to_vec(),
        }
    }
}

/// A raw signature to aggregate.
#[napi(object)]
pub struct SignedMessage {
    pub public_key: Buffer,
    pub message: Buffer,
    pub signature: Buffer,
}

struct RawSignedMessage {
    public_key: Vec<u8>,
    message: Vec<u8>,
    signature: Vec<u8>,
}

impl From<SignedMessage> for RawSignedMessage {
    fn from(entry: SignedMessage) -> Self {
        Self {
            public_key: entry.public_key.to_vec(),
            message: entry.message.to_vec(),
            signature: entry.signature.to_vec(),
        }
    }
}

#[napi]
pub struct XmssSecretKey {
    inner: Arc<xmss::SecretKey>,
}

#[napi]
impl XmssSecretKey {
    /// SECRET KEY MATERIAL: the seed.
    #[napi]
    pub fn to_bytes(&self) -> Buffer {
        self.inner.to_bytes().to_vec().into()
    }

    /// The trees the key holds, without any secret.
    #[napi]
    pub fn cache_to_bytes(&self) -> Buffer {
        self.inner.cache_to_bytes().into()
    }

    #[napi(getter)]
    pub fn public_key(&self) -> Buffer {
        self.inner.public_key().to_bytes().to_vec().into()
    }

    #[napi(ts_return_type = "Promise<void>")]
    pub fn prepare(&self, leaf_index: f64) -> AsyncTask<XmssPrepareTask> {
        AsyncTask::new(XmssPrepareTask {
            key: self.inner.clone(),
            leaf_index,
        })
    }

    #[napi(ts_return_type = "Promise<Buffer>")]
    pub fn sign(&self, message: Buffer, leaf_index: f64) -> AsyncTask<XmssSignTask> {
        AsyncTask::new(XmssSignTask {
            key: self.inner.clone(),
            message: message.to_vec(),
            leaf_index,
        })
    }
}

#[napi]
pub struct SphincsSecretKey {
    inner: Arc<sphincs::SecretKey>,
}

#[napi]
impl SphincsSecretKey {
    /// SECRET KEY MATERIAL: the seed.
    #[napi]
    pub fn to_bytes(&self) -> Buffer {
        self.inner.to_bytes().to_vec().into()
    }

    #[napi(getter)]
    pub fn public_key(&self) -> Buffer {
        self.inner.public_key().to_bytes().to_vec().into()
    }

    #[napi(ts_return_type = "Promise<Buffer>")]
    pub fn sign(&self, message: Buffer) -> AsyncTask<SphincsSignTask> {
        AsyncTask::new(SphincsSignTask {
            key: self.inner.clone(),
            message: message.to_vec(),
        })
    }
}

#[napi]
pub struct VrfKey {
    inner: Arc<vrf::Key>,
}

#[napi]
impl VrfKey {
    #[napi]
    pub fn root(&self) -> Buffer {
        self.inner.root().to_vec().into()
    }

    /// Encodes the key's cache: its range and cached layer, no secret.
    #[napi]
    pub fn cache_to_bytes(&self) -> Buffer {
        self.inner.cache_to_bytes().into()
    }

    #[napi]
    pub fn proof(&self, slot: f64) -> Result<Buffer> {
        let proof = self.inner.proof(uint32(slot, "slot")?).map_err(api_error)?;
        Ok(proof.as_flattened().to_vec().into())
    }
}

#[napi]
pub struct Aggregate {
    inner: Arc<lean_pq::Aggregate>,
}

#[napi]
impl Aggregate {
    #[napi]
    pub fn to_bytes(&self) -> Buffer {
        self.inner.to_bytes().into()
    }

    #[napi(getter)]
    pub fn xmss_claims(&self) -> Vec<Claim> {
        self.inner
            .xmss_claims()
            .into_iter()
            .map(|(key, message)| Claim {
                public_key: key.to_bytes().to_vec().into(),
                message: message.to_vec().into(),
            })
            .collect()
    }

    #[napi(getter)]
    pub fn sphincs_claims(&self) -> Vec<Claim> {
        self.inner
            .sphincs_claims()
            .into_iter()
            .map(|(key, message)| Claim {
                public_key: key.to_bytes().to_vec().into(),
                message: message.to_vec().into(),
            })
            .collect()
    }
}

pub enum XmssKeySource {
    Random,
    Seed(Vec<u8>),
    Bytes(Vec<u8>),
    Cache {
        seed: Vec<u8>,
        public_key: Vec<u8>,
        cache: Vec<u8>,
    },
}

pub struct XmssKeyTask {
    source: XmssKeySource,
}

impl Task for XmssKeyTask {
    type Output = xmss::SecretKey;
    type JsValue = XmssSecretKey;

    fn compute(&mut self) -> Result<Self::Output> {
        match &self.source {
            XmssKeySource::Random => Ok(xmss::SecretKey::generate()),
            XmssKeySource::Seed(seed) => Ok(xmss::SecretKey::from_seed(bytes32(seed, "seed")?)),
            XmssKeySource::Bytes(bytes) => xmss::SecretKey::from_bytes(bytes).map_err(api_error),
            XmssKeySource::Cache {
                seed,
                public_key,
                cache,
            } => {
                let public_key = xmss::PublicKey::from_bytes(public_key).map_err(api_error)?;
                xmss::SecretKey::from_cache_bytes(bytes32(seed, "seed")?, &public_key, cache)
                    .map_err(api_error)
            }
        }
    }

    fn resolve(&mut self, _: Env, output: Self::Output) -> Result<Self::JsValue> {
        Ok(XmssSecretKey {
            inner: Arc::new(output),
        })
    }
}

pub struct XmssPrepareTask {
    key: Arc<xmss::SecretKey>,
    leaf_index: f64,
}

impl Task for XmssPrepareTask {
    type Output = ();
    type JsValue = ();

    fn compute(&mut self) -> Result<Self::Output> {
        self.key.prepare(uint32(self.leaf_index, "leaf index")?);
        Ok(())
    }

    fn resolve(&mut self, _: Env, output: Self::Output) -> Result<Self::JsValue> {
        Ok(output)
    }
}

pub struct XmssSignTask {
    key: Arc<xmss::SecretKey>,
    message: Vec<u8>,
    leaf_index: f64,
}

impl Task for XmssSignTask {
    type Output = Vec<u8>;
    type JsValue = Buffer;

    fn compute(&mut self) -> Result<Self::Output> {
        let message = to_message(&self.message)?;
        let leaf_index = uint32(self.leaf_index, "leaf index")?;
        let signature = self.key.sign(&message, leaf_index);
        Ok(signature.to_bytes().to_vec())
    }

    fn resolve(&mut self, _: Env, output: Self::Output) -> Result<Self::JsValue> {
        Ok(output.into())
    }
}

pub enum SphincsKeySource {
    Random,
    Seed(Vec<u8>),
    Bytes(Vec<u8>),
}

pub struct SphincsKeyTask {
    source: SphincsKeySource,
}

impl Task for SphincsKeyTask {
    type Output = sphincs::SecretKey;
    type JsValue = SphincsSecretKey;

    fn compute(&mut self) -> Result<Self::Output> {
        match &self.source {
            SphincsKeySource::Random => Ok(sphincs::SecretKey::generate()),
            SphincsKeySource::Seed(seed) => {
                Ok(sphincs::SecretKey::from_seed(bytes32(seed, "seed")?))
            }
            SphincsKeySource::Bytes(bytes) => {
                sphincs::SecretKey::from_bytes(bytes).map_err(api_error)
            }
        }
    }

    fn resolve(&mut self, _: Env, output: Self::Output) -> Result<Self::JsValue> {
        Ok(SphincsSecretKey {
            inner: Arc::new(output),
        })
    }
}

pub struct SphincsSignTask {
    key: Arc<sphincs::SecretKey>,
    message: Vec<u8>,
}

impl Task for SphincsSignTask {
    type Output = Vec<u8>;
    type JsValue = Buffer;

    fn compute(&mut self) -> Result<Self::Output> {
        let signature = self.key.sign(&to_message(&self.message)?);
        Ok(signature.to_bytes().to_vec())
    }

    fn resolve(&mut self, _: Env, output: Self::Output) -> Result<Self::JsValue> {
        Ok(output.into())
    }
}

pub enum VrfKeySource {
    Range { start: f64, end: f64 },
    Cache { cache: Vec<u8>, root: Vec<u8> },
}

pub struct VrfKeyTask {
    seed: Vec<u8>,
    source: VrfKeySource,
}

impl Task for VrfKeyTask {
    type Output = vrf::Key;
    type JsValue = VrfKey;

    fn compute(&mut self) -> Result<Self::Output> {
        let seed = bytes32(&self.seed, "seed")?;
        match &self.source {
            VrfKeySource::Range { start, end } => {
                let slots = uint32(*start, "start")?..uint32(*end, "end")?;
                vrf::Key::new(seed, slots).map_err(api_error)
            }
            VrfKeySource::Cache { cache, root } => {
                let root = bytes32(root, "root")?;
                vrf::Key::from_cache_bytes(seed, &root, cache).map_err(api_error)
            }
        }
    }

    fn resolve(&mut self, _: Env, output: Self::Output) -> Result<Self::JsValue> {
        Ok(VrfKey {
            inner: Arc::new(output),
        })
    }
}

pub struct SetupTask {
    threads: f64,
}

impl Task for SetupTask {
    type Output = ();
    type JsValue = ();

    fn compute(&mut self) -> Result<Self::Output> {
        lean_pq::setup(uint32(self.threads, "threads")? as usize).map_err(api_error)
    }

    fn resolve(&mut self, _: Env, output: Self::Output) -> Result<Self::JsValue> {
        Ok(output)
    }
}

pub struct AggregateFromBytesTask {
    data: Vec<u8>,
    xmss: Vec<RawClaim>,
    sphincs: Vec<RawClaim>,
}

impl Task for AggregateFromBytesTask {
    type Output = lean_pq::Aggregate;
    type JsValue = Aggregate;

    fn compute(&mut self) -> Result<Self::Output> {
        let (xmss, sphincs) = claim_lists(&self.xmss, &self.sphincs)?;
        lean_pq::Aggregate::from_bytes(&self.data, &xmss, &sphincs).map_err(api_error)
    }

    fn resolve(&mut self, _: Env, output: Self::Output) -> Result<Self::JsValue> {
        Ok(Aggregate {
            inner: Arc::new(output),
        })
    }
}

/// Claim lists, as `Aggregate::from_bytes` and `aggregate_only` take them.
type Claims = (
    Vec<(xmss::PublicKey, Message)>,
    Vec<(sphincs::PublicKey, Message)>,
);

fn claim_lists(xmss: &[RawClaim], sphincs: &[RawClaim]) -> Result<Claims> {
    let xmss = xmss
        .iter()
        .map(|claim| {
            Ok((
                xmss::PublicKey::from_bytes(&claim.public_key).map_err(api_error)?,
                to_message(&claim.message)?,
            ))
        })
        .collect::<Result<Vec<_>>>()?;
    let sphincs = sphincs
        .iter()
        .map(|claim| {
            Ok((
                sphincs::PublicKey::from_bytes(&claim.public_key).map_err(api_error)?,
                to_message(&claim.message)?,
            ))
        })
        .collect::<Result<Vec<_>>>()?;
    Ok((xmss, sphincs))
}

pub struct AggregateTask {
    children: Vec<Arc<lean_pq::Aggregate>>,
    xmss: Vec<RawSignedMessage>,
    sphincs: Vec<RawSignedMessage>,
    /// The claims to prove, all covered ones if `None`.
    only: Option<(Vec<RawClaim>, Vec<RawClaim>)>,
}

impl Task for AggregateTask {
    type Output = lean_pq::Aggregate;
    type JsValue = Aggregate;

    fn compute(&mut self) -> Result<Self::Output> {
        let xmss = self
            .xmss
            .iter()
            .map(|entry| {
                Ok((
                    xmss::PublicKey::from_bytes(&entry.public_key).map_err(api_error)?,
                    to_message(&entry.message)?,
                    xmss::Signature::from_bytes(&entry.signature).map_err(api_error)?,
                ))
            })
            .collect::<Result<Vec<_>>>()?;
        let sphincs = self
            .sphincs
            .iter()
            .map(|entry| {
                Ok((
                    sphincs::PublicKey::from_bytes(&entry.public_key).map_err(api_error)?,
                    to_message(&entry.message)?,
                    sphincs::Signature::from_bytes(&entry.signature).map_err(api_error)?,
                ))
            })
            .collect::<Result<Vec<_>>>()?;
        let children = self.children.iter().map(Arc::as_ref).collect::<Vec<_>>();
        match &self.only {
            None => lean_pq::aggregate(&children, &xmss, &sphincs),
            Some((xmss_claims, sphincs_claims)) => {
                let (xmss_claims, sphincs_claims) = claim_lists(xmss_claims, sphincs_claims)?;
                lean_pq::aggregate_only(&children, &xmss, &sphincs, &xmss_claims, &sphincs_claims)
            }
        }
        .map_err(api_error)
    }

    fn resolve(&mut self, _: Env, output: Self::Output) -> Result<Self::JsValue> {
        Ok(Aggregate {
            inner: Arc::new(output),
        })
    }
}

#[napi(ts_return_type = "Promise<void>")]
pub fn setup(env: &Env, threads: Option<f64>) -> Result<Object<'_>> {
    on_own_thread(
        env,
        SetupTask {
            threads: threads.unwrap_or(0.0),
        },
    )
}

#[napi(ts_return_type = "Promise<XmssSecretKey>")]
pub fn generate_xmss_secret_key() -> AsyncTask<XmssKeyTask> {
    AsyncTask::new(XmssKeyTask {
        source: XmssKeySource::Random,
    })
}

#[napi(ts_return_type = "Promise<XmssSecretKey>")]
pub fn xmss_secret_key_from_seed(seed: Buffer) -> AsyncTask<XmssKeyTask> {
    AsyncTask::new(XmssKeyTask {
        source: XmssKeySource::Seed(seed.to_vec()),
    })
}

#[napi(ts_return_type = "Promise<XmssSecretKey>")]
pub fn xmss_secret_key_from_bytes(data: Buffer) -> AsyncTask<XmssKeyTask> {
    AsyncTask::new(XmssKeyTask {
        source: XmssKeySource::Bytes(data.to_vec()),
    })
}

#[napi(ts_return_type = "Promise<XmssSecretKey>")]
pub fn xmss_secret_key_from_cache_bytes(
    seed: Buffer,
    public_key: Buffer,
    cache: Buffer,
) -> AsyncTask<XmssKeyTask> {
    AsyncTask::new(XmssKeyTask {
        source: XmssKeySource::Cache {
            seed: seed.to_vec(),
            public_key: public_key.to_vec(),
            cache: cache.to_vec(),
        },
    })
}

#[napi]
pub fn xmss_verify(public_key: Buffer, message: Buffer, signature: Buffer) -> Result<()> {
    let public_key = xmss::PublicKey::from_bytes(&public_key).map_err(api_error)?;
    let signature = xmss::Signature::from_bytes(&signature).map_err(api_error)?;
    public_key
        .verify(&to_message(&message)?, &signature)
        .map_err(api_error)
}

#[napi(ts_return_type = "Promise<SphincsSecretKey>")]
pub fn generate_sphincs_secret_key() -> AsyncTask<SphincsKeyTask> {
    AsyncTask::new(SphincsKeyTask {
        source: SphincsKeySource::Random,
    })
}

#[napi(ts_return_type = "Promise<SphincsSecretKey>")]
pub fn sphincs_secret_key_from_seed(seed: Buffer) -> AsyncTask<SphincsKeyTask> {
    AsyncTask::new(SphincsKeyTask {
        source: SphincsKeySource::Seed(seed.to_vec()),
    })
}

#[napi(ts_return_type = "Promise<SphincsSecretKey>")]
pub fn sphincs_secret_key_from_bytes(data: Buffer) -> AsyncTask<SphincsKeyTask> {
    AsyncTask::new(SphincsKeyTask {
        source: SphincsKeySource::Bytes(data.to_vec()),
    })
}

#[napi]
pub fn sphincs_verify(public_key: Buffer, message: Buffer, signature: Buffer) -> Result<()> {
    let public_key = sphincs::PublicKey::from_bytes(&public_key).map_err(api_error)?;
    let signature = sphincs::Signature::from_bytes(&signature).map_err(api_error)?;
    public_key
        .verify(&to_message(&message)?, &signature)
        .map_err(api_error)
}

#[napi(ts_return_type = "Promise<VrfKey>")]
pub fn vrf_key_from_seed(env: &Env, seed: Buffer, start: f64, end: f64) -> Result<Object<'_>> {
    on_own_thread(
        env,
        VrfKeyTask {
            seed: seed.to_vec(),
            source: VrfKeySource::Range { start, end },
        },
    )
}

#[napi(ts_return_type = "Promise<VrfKey>")]
pub fn vrf_key_from_cache_bytes(
    seed: Buffer,
    root: Buffer,
    cache: Buffer,
) -> AsyncTask<VrfKeyTask> {
    AsyncTask::new(VrfKeyTask {
        seed: seed.to_vec(),
        source: VrfKeySource::Cache {
            cache: cache.to_vec(),
            root: root.to_vec(),
        },
    })
}

#[napi]
pub fn vrf_verify(root: Buffer, slot: f64, proof: Buffer) -> Result<()> {
    let root = bytes32(&root, "root")?;
    let slot = uint53(slot, "slot")?;
    let proof: &[u8; vrf::PROOF_LEN] = proof.as_ref().try_into().map_err(|_| {
        invalid_arg(format!(
            "proof must be {} bytes, got {}",
            vrf::PROOF_LEN,
            proof.len()
        ))
    })?;
    let (nodes, _) = proof.as_chunks::<32>();
    let proof: vrf::Proof = nodes.try_into().expect("a proof is 32 nodes");
    vrf::verify(&root, slot, &proof).map_err(api_error)
}

#[napi(ts_return_type = "Promise<Aggregate>")]
pub fn aggregate_from_bytes(
    env: &Env,
    data: Buffer,
    xmss: Vec<Claim>,
    sphincs: Vec<Claim>,
) -> Result<Object<'_>> {
    on_own_thread(
        env,
        AggregateFromBytesTask {
            data: data.to_vec(),
            xmss: xmss.into_iter().map(RawClaim::from).collect(),
            sphincs: sphincs.into_iter().map(RawClaim::from).collect(),
        },
    )
}

#[napi(ts_return_type = "Promise<Aggregate>")]
pub fn aggregate<'env>(
    env: &'env Env,
    children: Vec<&Aggregate>,
    xmss: Vec<SignedMessage>,
    sphincs: Vec<SignedMessage>,
    only_xmss: Option<Vec<Claim>>,
    only_sphincs: Option<Vec<Claim>>,
) -> Result<Object<'env>> {
    let raw = |claims: Option<Vec<Claim>>| {
        claims
            .unwrap_or_default()
            .into_iter()
            .map(RawClaim::from)
            .collect()
    };
    let only = (only_xmss.is_some() || only_sphincs.is_some())
        .then(|| (raw(only_xmss), raw(only_sphincs)));
    on_own_thread(
        env,
        AggregateTask {
            children: children.iter().map(|child| child.inner.clone()).collect(),
            xmss: xmss.into_iter().map(RawSignedMessage::from).collect(),
            sphincs: sphincs.into_iter().map(RawSignedMessage::from).collect(),
            only,
        },
    )
}
