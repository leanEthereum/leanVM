use std::sync::Arc;

use lean_pq::{sphincs, xmss, Message};
use napi::bindgen_prelude::{AsyncTask, Buffer, Error, Result, Status, Task};
use napi::Env;
use napi_derive::napi;

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

pub struct SetupTask;

impl Task for SetupTask {
    type Output = ();
    type JsValue = ();

    fn compute(&mut self) -> Result<Self::Output> {
        lean_pq::setup();
        Ok(())
    }

    fn resolve(&mut self, _: Env, output: Self::Output) -> Result<Self::JsValue> {
        Ok(output)
    }
}

pub enum XmssKeySource {
    Random,
    Seed(Vec<u8>),
    Bytes(Vec<u8>),
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

pub struct AggregateFromBytesTask {
    data: Vec<u8>,
    xmss: Vec<RawClaim>,
    sphincs: Vec<RawClaim>,
}

impl Task for AggregateFromBytesTask {
    type Output = lean_pq::Aggregate;
    type JsValue = Aggregate;

    fn compute(&mut self) -> Result<Self::Output> {
        let xmss = self
            .xmss
            .iter()
            .map(|claim| {
                Ok((
                    xmss::PublicKey::from_bytes(&claim.public_key).map_err(api_error)?,
                    to_message(&claim.message)?,
                ))
            })
            .collect::<Result<Vec<_>>>()?;
        let sphincs = self
            .sphincs
            .iter()
            .map(|claim| {
                Ok((
                    sphincs::PublicKey::from_bytes(&claim.public_key).map_err(api_error)?,
                    to_message(&claim.message)?,
                ))
            })
            .collect::<Result<Vec<_>>>()?;
        lean_pq::Aggregate::from_bytes(&self.data, &xmss, &sphincs).map_err(api_error)
    }

    fn resolve(&mut self, _: Env, output: Self::Output) -> Result<Self::JsValue> {
        Ok(Aggregate {
            inner: Arc::new(output),
        })
    }
}

pub struct AggregateTask {
    children: Vec<Arc<lean_pq::Aggregate>>,
    xmss: Vec<RawSignedMessage>,
    sphincs: Vec<RawSignedMessage>,
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
        lean_pq::aggregate(&children, &xmss, &sphincs).map_err(api_error)
    }

    fn resolve(&mut self, _: Env, output: Self::Output) -> Result<Self::JsValue> {
        Ok(Aggregate {
            inner: Arc::new(output),
        })
    }
}

#[napi(ts_return_type = "Promise<void>")]
pub fn setup() -> AsyncTask<SetupTask> {
    AsyncTask::new(SetupTask)
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

#[napi(ts_return_type = "Promise<Aggregate>")]
pub fn aggregate_from_bytes(
    data: Buffer,
    xmss: Vec<Claim>,
    sphincs: Vec<Claim>,
) -> AsyncTask<AggregateFromBytesTask> {
    AsyncTask::new(AggregateFromBytesTask {
        data: data.to_vec(),
        xmss: xmss.into_iter().map(RawClaim::from).collect(),
        sphincs: sphincs.into_iter().map(RawClaim::from).collect(),
    })
}

#[napi(ts_return_type = "Promise<Aggregate>")]
pub fn aggregate(
    children: Vec<&Aggregate>,
    xmss: Vec<SignedMessage>,
    sphincs: Vec<SignedMessage>,
) -> AsyncTask<AggregateTask> {
    AsyncTask::new(AggregateTask {
        children: children.iter().map(|child| child.inner.clone()).collect(),
        xmss: xmss.into_iter().map(RawSignedMessage::from).collect(),
        sphincs: sphincs.into_iter().map(RawSignedMessage::from).collect(),
    })
}
