# Releasing the bindings

## How a release happens

1. Commits touching `bindings/` have conventional-commit titles (`feat:`, `fix:`, `chore:`, ...).
2. On `main`, release-please keeps a release pull request open. It bumps the version in `bindings/Cargo.toml` and in every file `release-please-config.json` lists (in READMEs, inside `x-release-please` blocks), and writes `bindings/CHANGELOG.md`.
3. Merging it tags `bindings-vX.Y.Z`, and `bindings-release.yml` runs on the tag and publishes every package below.

- Dispatching `bindings-release.yml` from a branch is a dry run at version 0.0.0: everything builds and is checked, nothing is published.
- PyPI, npm and NuGet skip versions already published, so a failed run can be re-dispatched on the same tag: `gh workflow run bindings-release.yml --ref bindings-vX.Y.Z`. Maven Central accepts a version only once.

## PyPI

`py-lean-pq`, by trusted publishing (`publish` job). One-time: on pypi.org, give the project a trusted publisher with repository `leanEthereum/leanVM`, workflow `bindings-release.yml`, environment `pypi`.

## npm

`@kevaundray/lean-pq` and one package per platform, by trusted publishing with provenance (`node-publish` job: platform packages first, then the root).

`npm/` holds the platform packages' manifests. After changing `napi.targets` in `package.json`, rerun `napi create-npm-dirs` and commit the result.

To check the packaging locally after `npm run build` in `bindings/node` (CI does the same on Linux x64):

```sh
pack=$(mktemp -d)
cp lean_pq_node.linux-x64-gnu.node npm/linux-x64-gnu/
npm pack --ignore-scripts --pack-destination "$pack"
npm pack --ignore-scripts --pack-destination "$pack" ./npm/linux-x64-gnu
sh scripts/install-check.sh "$pack/kevaundray-lean-pq-0.0.0-dev.tgz" "$pack/kevaundray-lean-pq-linux-x64-gnu-0.0.0-dev.tgz"
```

### First publish of a package

npm attaches a trusted publisher only to a package that exists, so the first release of any package (a new platform included; `node-package` warns about each one not yet on npm) publishes with a token:

1. From the account owning the `@kevaundray` scope, create a granular access token on npmjs.com (Access Tokens, Generate New Token, Granular Access Token): read and write on packages, a short expiry, nothing else. If publishing requires 2FA, let the token bypass it.
2. `gh secret set NPM_TOKEN -R leanEthereum/leanVM`
3. Cut the release. `node-publish` tries trusted publishing, then falls back to the token.
4. Give each new package a trusted publisher (repository `leanEthereum/leanVM`, workflow `bindings-release.yml`, environment `npm`, `npm publish` allowed), in its Settings, Trusted publishing on npmjs.com, or with npm 11.15 or newer: `npm trust github <package> --repo leanEthereum/leanVM --file bindings-release.yml --env npm --allow-publish --yes`
5. `gh secret delete NPM_TOKEN -R leanEthereum/leanVM`, revoke the token, and set each package's Settings, Publishing access to "Require two-factor authentication and disallow tokens".

Packages up to 0.11.1 were published from `ethereum/lean-pq-bindings`: point their trusted publishers at `leanEthereum/leanVM` (step 4) before the next release.

## Maven Central

`io.github.crate-crypto:lean-pq`, through the Central Portal (`java-native` builds each platform's library, `java-publish` bundles all four, runs a consumer against the jar, signs, uploads and releases).

Locally (from the repository root):

- `gradle -p bindings/java jar` bundles only the host library. `-PleanPqNativeDir=DIR` bundles `DIR/<platform>/` instead; `bindings/java/scripts/build-native.sh <platform> DIR` builds one (Linux: [Zig 0.15.2](https://ziglang.org/download/) and `cargo install cargo-zigbuild`; macOS: a Mac; Windows: Git Bash, the `x86_64-pc-windows-gnu` Rust target, and MinGW-w64 `gcc` and `objdump` on `PATH`).
- Local builds are `0.0.0-SNAPSHOT`; `-Pversion=X.Y.Z` overrides it.
- `bindings/java/scripts/consumer-smoke.sh [GRADLE_ARGS...]` publishes the jar to a throwaway repository and signs, verifies and aggregates through it from a fresh modular project (`GRADLE` names Gradle if it is not on `PATH`).

### One-time setup

The `io.github.crate-crypto` namespace must be verified on [central.sonatype.com](https://central.sonatype.com/publishing/namespaces).

1. Portal user token: at <https://central.sonatype.com/usertoken>, Generate User Token, and copy the username and password it shows once.
2. Signing key, and its public half on a keyserver (Central checks signatures against it):

   ```sh
   gpg --quick-generate-key "lean-pq release signing <maintainer@example.org>" rsa4096 sign 2y
   gpg --list-secret-keys --keyid-format long   # the 40-hex-digit fingerprint
   gpg --armor --export FINGERPRINT > lean-pq-signing.asc
   ```

   Upload `lean-pq-signing.asc` at <https://keys.openpgp.org/upload> and confirm the verification e-mail, so the key keeps its identity.
3. Repository secrets (Settings, Secrets and variables, Actions):

   | Secret | Value |
   | --- | --- |
   | `MAVEN_CENTRAL_USERNAME` | the token's username |
   | `MAVEN_CENTRAL_PASSWORD` | the token's password |
   | `SIGNING_KEY` | `gpg --armor --export-secret-keys FINGERPRINT`, including the `BEGIN`/`END` lines |
   | `SIGNING_PASSWORD` | the key's passphrase |

Before the key expires: `gpg --quick-set-expire FINGERPRINT 2y`, upload the public key again, and update `SIGNING_KEY`.

## NuGet

`Ethereum.LeanPq`, by trusted publishing (`dotnet-publish` job). It bundles the four libraries `java-native` builds, as `runtimes/<rid>/native` (one universal library under `runtimes/osx`), and `dotnet-consumer` runs a consumer against the package on every platform before anything is published.

Locally (from the repository root):

- `dotnet pack bindings/dotnet/src/Ethereum.LeanPq` bundles only the host library. `-p:LeanPqNativeDir=DIR` bundles `DIR/<platform>/` instead, as `bindings/java/scripts/build-native.sh` stages it.
- Local builds are `0.0.0-dev`; `-p:Version=X.Y.Z` overrides it.
- `bindings/dotnet/scripts/consumer-smoke.sh [DOTNET_PACK_ARGS...]` packs into a throwaway feed and signs, verifies and aggregates through the package from a fresh console project; `--feed DIR` runs it against the package already in `DIR`.

### One-time setup

Until it is done, `dotnet-publish` builds and checks the package, warns, and publishes nothing.

1. On nuget.org, from the account (or organization) that will own `Ethereum.LeanPq`, add a trusted publishing policy (Account, Trusted Publishing): repository owner `leanEthereum`, repository `leanVM`, workflow `bindings-release.yml`, environment `nuget`.
2. `gh secret set NUGET_USER -R leanEthereum/leanVM` with that account's nuget.org user name (not its e-mail).

## Go

`leanvm.org/go`. `go-publish` attaches the module's proxy files (`go-module-vX.Y.Z.{info,mod,zip}`) to the GitHub release, then dispatches `pages.yml`, which serves every release's files from `leanvm.org/goproxy`. Nothing to set up.

## GitHub release assets

The Zig package (`lean-pq-zig-X.Y.Z.tar.gz`) and the Nim package's native archives (`lean-pq-native-*.a`) are attached to the `bindings-vX.Y.Z` release. Nothing to set up.
